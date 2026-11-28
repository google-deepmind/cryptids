/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Longitudinal

/-!
# Non-Halting Proof for `1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC`

Kernel-verified non-halting proof for the `(6, 2)` Turing machine
`1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC` via longitudinal counter compression
and symbolic step reflection (`BusyBeaver.Calculi.Longitudinal`).

- Machine page: <https://bbchallenge.org/1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC>
- Upstream proof (`Others_v2.v`, `Module TM23`):
  <https://raw.githubusercontent.com/ccz181078/busycoq/BB6/verify/Others_v2.v>
-/

open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.SixState BusyBeaver.Longitudinal

namespace BusyBeaver.M_1RB0LA_1RC0RB_1LD1RB_0LA0LE_HHH1LF_1LA1LC

@[expose] public section

/-- Machine `1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LA_1RC0RB_1LD1RB_0LA0LE_HHH1LF_1LA1LC"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

private def tm40 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => none
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 2, Stmt.write 1 Dir.left)

private abbrev X : List (Fin 2) := [1, 1, 0, 1]

private abbrev Y : List (Fin 2) := [1, 1, 1, 0, 1]

private abbrev Dr : List (Fin 2) := [1, 1, 0, 0]

private abbrev Pr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0]

/-- Right-to-left boundary bounce signal `((B, [1, 1, 0, 0]), (A, []))`
(`h := [((B, <[0; 0; 1; 1]), (A, []))]` in `Others_v2.v`). -/
private abbrev h : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  [((B, [1, 1, 0, 0]), (A, []))]

/-- Initial right-to-left boundary bounce signal `((B, []), (A, []))`. -/
private abbrev hf : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  [((B, []), (A, []))]

private def end0 : ListBlank (Fin 2) := [0, 0] +> (Y +> default)

private def end1 : ListBlank (Fin 2) := [0] +> (Y +> (Y +> default))

/-- Canonical root configuration `0inf <{{A}} r` (`Others_v2.v` line 209). -/
private def root (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} r

-- ============================================================================
-- 1b. Reflective Symbolic Stepper (`SymState`, `runSym`, `runSym_plus`)
-- ============================================================================

private theorem step_B_X_one (l r : ListBlank (Fin 2)) :
    (l {{B}}> (X +> r)) [tm40]⊢* ((Dr +> l) {{B}}> r) := by
  bb_steps

private theorem shift_B_X (n : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{B}}> ((X ^ n) +> r)) [tm40]⊢* (((Dr ^ n) +> l) {{B}}> r) := by
  induction n generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ n ih =>
    rw [ListBlank.append_pow_succ]
    refine ReachesStar.trans (step_B_X_one l ((X ^ n) +> r)) ?_
    have h_ih := ih (Dr +> l) r
    rwa [ListBlank.append_pow_comm Dr n l, ← ListBlank.append_pow_succ] at h_ih

private theorem step_A_Dr_one (l r : ListBlank (Fin 2)) :
    ((Dr +> l) <{{A}} r) [tm40]⊢* (l <{{A}} (X +> r)) := by
  bb_steps

private theorem shift_A_Dr (n : ℕ) (l r : ListBlank (Fin 2)) :
    (((Dr ^ n) +> l) <{{A}} r) [tm40]⊢* (l <{{A}} ((X ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ n ih =>
    rw [ListBlank.append_pow_succ]
    refine ReachesStar.trans (step_A_Dr_one ((Dr ^ n) +> l) r) ?_
    have h_ih := ih l (X +> r)
    rwa [ListBlank.append_pow_comm X n r, ← ListBlank.append_pow_succ] at h_ih

private inductive LAtom where
  | bit (b : Fin 2)
  | repDr (id : ℕ)
  deriving DecidableEq, Repr

private inductive RAtom where
  | bit (b : Fin 2)
  | repX (id : ℕ)
  deriving DecidableEq, Repr

private inductive CallKind where
  | callH
  | callHf
  deriving DecidableEq, Repr

private structure SymState where
  dir : Bool
  q : Fin 6
  left : List LAtom
  right : List RAtom
  leftIsDefault : Bool
  deriving DecidableEq, Repr

private def evalLeft (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2)) : List LAtom → ListBlank (Fin 2)
  | [] => lBase
  | .bit b :: rest => b >> evalLeft vars lBase rest
  | .repDr id :: rest => (Dr ^ vars id) +> evalLeft vars lBase rest

private def evalRight (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2)) : List RAtom → ListBlank (Fin 2)
  | [] => rBase
  | .bit b :: rest => b >> evalRight vars rBase rest
  | .repX id :: rest => (X ^ vars id) +> evalRight vars rBase rest

private def evalState (vars : ℕ → ℕ) (lBase rBase : ListBlank (Fin 2)) (st : SymState) :
    Cfg (Fin 2) (Fin 6) :=
  let l := evalLeft vars (if st.leftIsDefault then default else lBase) st.left
  let r := evalRight vars rBase st.right
  if st.dir then l {{st.q}}> r else l <{{st.q}} r

private def evalCall : CallKind → DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)
  | .callH => ((B, [1, 1, 0, 0]), (A, []))
  | .callHf => ((B, []), (A, []))

private def evalCalls (cs : List CallKind) : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)) :=
  cs.map evalCall

private def popBit (expected : Fin 2) : List LAtom → Option (List LAtom)
  | .bit b :: rest => if b == expected then some rest else none
  | _ => none

private theorem popBit_some {expected : Fin 2} {ls rest : List LAtom}
    (h : popBit expected ls = some rest) :
    ls = .bit expected :: rest := by
  rcases ls with _ | ⟨b | id, rest'⟩
  · contradiction
  · dsimp only [popBit] at h
    split at h
    · cases h; rename_i hbe; rw [beq_iff_eq.mp hbe]
    · contradiction
  · contradiction

private def popDr (ls : List LAtom) : Option (List LAtom) :=
  match popBit 1 ls with
  | none => none
  | some ls1 =>
    match popBit 1 ls1 with
    | none => none
    | some ls2 =>
      match popBit 0 ls2 with
      | none => none
      | some ls3 => popBit 0 ls3

private theorem popDr_some {ls rest : List LAtom} (h : popDr ls = some rest) :
    ls = .bit 1 :: .bit 1 :: .bit 0 :: .bit 0 :: rest := by
  dsimp [popDr] at h
  rcases h1 : popBit 1 ls with _ | ls1; · rw [h1] at h; contradiction
  rw [h1] at h; dsimp at h
  rcases h2 : popBit 1 ls1 with _ | ls2; · rw [h2] at h; contradiction
  rw [h2] at h; dsimp at h
  rcases h3 : popBit 0 ls2 with _ | ls3; · rw [h3] at h; contradiction
  rw [h3] at h; dsimp at h
  rw [popBit_some h1, popBit_some h2, popBit_some h3, popBit_some h]

private def popBitR (expected : Fin 2) : List RAtom → Option (List RAtom)
  | .bit b :: rest => if b == expected then some rest else none
  | _ => none

private theorem popBitR_some {expected : Fin 2} {rs rest : List RAtom}
    (h : popBitR expected rs = some rest) :
    rs = .bit expected :: rest := by
  rcases rs with _ | ⟨b | id, rest'⟩
  · contradiction
  · dsimp only [popBitR] at h
    split at h
    · cases h; rename_i hbe; rw [beq_iff_eq.mp hbe]
    · contradiction
  · contradiction

private def popX (rs : List RAtom) : Option (List RAtom) :=
  match popBitR 1 rs with
  | none => none
  | some rs1 =>
    match popBitR 1 rs1 with
    | none => none
    | some rs2 =>
      match popBitR 0 rs2 with
      | none => none
      | some rs3 => popBitR 1 rs3

private theorem popX_some {rs rest : List RAtom} (h : popX rs = some rest) :
    rs = .bit 1 :: .bit 1 :: .bit 0 :: .bit 1 :: rest := by
  dsimp [popX] at h
  rcases h1 : popBitR 1 rs with _ | rs1; · rw [h1] at h; contradiction
  rw [h1] at h; dsimp at h
  rcases h2 : popBitR 1 rs1 with _ | rs2; · rw [h2] at h; contradiction
  rw [h2] at h; dsimp at h
  rcases h3 : popBitR 0 rs2 with _ | rs3; · rw [h3] at h; contradiction
  rw [h3] at h; dsimp at h
  rw [popBitR_some h1, popBitR_some h2, popBitR_some h3, popBitR_some h]

private def pushRepDr : ℕ → ℕ → List LAtom → List LAtom
  | 0, id, ls => .repDr id :: ls
  | fuel + 1, id, ls =>
    match popDr ls with
    | some rest => .bit 1 :: .bit 1 :: .bit 0 :: .bit 0 :: pushRepDr fuel id rest
    | none => .repDr id :: ls

private def insertRepDr (id : ℕ) (ls : List LAtom) : List LAtom :=
  pushRepDr 16 id ls

private theorem evalLeft_pushRepDr (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (fuel id : ℕ) (ls : List LAtom) :
    evalLeft vars lBase (pushRepDr fuel id ls) = evalLeft vars lBase (.repDr id :: ls) := by
  induction fuel generalizing ls with
  | zero => rfl
  | succ fuel ih =>
    dsimp [pushRepDr]
    rcases h : popDr ls with _ | rest
    · rfl
    · rw [popDr_some h]
      simp only [evalLeft, ih rest]
      exact (ListBlank.append_pow_comm Dr (vars id) (evalLeft vars lBase rest)).symm

private theorem evalLeft_insertRepDr (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2)) (id : ℕ)
    (ls : List LAtom) :
    evalLeft vars lBase (insertRepDr id ls) = evalLeft vars lBase (.repDr id :: ls) :=
  evalLeft_pushRepDr vars lBase 16 id ls

private def pushRepX : ℕ → ℕ → List RAtom → List RAtom
  | 0, id, rs => .repX id :: rs
  | fuel + 1, id, rs =>
    match popX rs with
    | some rest => .bit 1 :: .bit 1 :: .bit 0 :: .bit 1 :: pushRepX fuel id rest
    | none => .repX id :: rs

private def insertRepX (id : ℕ) (rs : List RAtom) : List RAtom :=
  pushRepX 16 id rs

private theorem evalRight_pushRepX (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2))
    (fuel id : ℕ) (rs : List RAtom) :
    evalRight vars rBase (pushRepX fuel id rs) = evalRight vars rBase (.repX id :: rs) := by
  induction fuel generalizing rs with
  | zero => rfl
  | succ fuel ih =>
    dsimp [pushRepX]
    rcases h : popX rs with _ | rest
    · rfl
    · rw [popX_some h]
      simp only [evalRight, ih rest]
      exact (ListBlank.append_pow_comm X (vars id) (evalRight vars rBase rest)).symm

private theorem evalRight_insertRepX (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2)) (id : ℕ)
    (rs : List RAtom) :
    evalRight vars rBase (insertRepX id rs) = evalRight vars rBase (.repX id :: rs) :=
  evalRight_pushRepX vars rBase 16 id rs

private def consLeftBit (leftIsDefault : Bool) (b : Fin 2) : List LAtom → List LAtom
  | [] => if b == 0 && leftIsDefault then [] else [.bit b]
  | a :: rest => .bit b :: a :: rest

private def consLeftNorm (leftIsDefault : Bool) (a : LAtom) (ls : List LAtom) : List LAtom :=
  match a with
  | .bit b => consLeftBit leftIsDefault b ls
  | .repDr id => insertRepDr id ls

private theorem evalLeft_consLeftNorm (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (leftIsDefault : Bool) (a : LAtom) (ls : List LAtom) :
    evalLeft vars (if leftIsDefault then default else lBase) (consLeftNorm leftIsDefault a ls) =
      evalLeft vars (if leftIsDefault then default else lBase) (a :: ls) := by
  rcases a with b | id
  · by_cases hb : b = 0
    · subst hb
      rcases leftIsDefault with _ | _ <;> rcases ls with _ | ⟨hd, tl⟩ <;>
        simp [consLeftNorm, consLeftBit, evalLeft, ListBlank.cons_zero_default]
    · have hbeq : (b == 0) = false := beq_false_of_ne hb
      rcases ls with _ | ⟨hd, tl⟩ <;> simp [consLeftNorm, consLeftBit, hbeq]
  · exact evalLeft_insertRepDr vars (if leftIsDefault then default else lBase) id ls

private def normLeft (leftIsDefault : Bool) : List LAtom → List LAtom
  | [] => []
  | a :: ls => consLeftNorm leftIsDefault a (normLeft leftIsDefault ls)

private theorem evalLeft_normLeft (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (leftIsDefault : Bool) (ls : List LAtom) :
    evalLeft vars (if leftIsDefault then default else lBase) (normLeft leftIsDefault ls) =
      evalLeft vars (if leftIsDefault then default else lBase) ls := by
  induction ls with
  | nil => rfl
  | cons a ls ih =>
    rw [normLeft, evalLeft_consLeftNorm]
    cases a <;> simp [evalLeft, ih]

private def normRight : List RAtom → List RAtom
  | [] => []
  | .bit b :: rs => .bit b :: normRight rs
  | .repX id :: rs => insertRepX id (normRight rs)

private theorem evalRight_normRight (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2)) (rs : List RAtom) :
  evalRight vars rBase (normRight rs) = evalRight vars rBase rs := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    rcases a with b | id
    · simp [normRight, evalRight, ih]
    · simp [normRight, evalRight_insertRepX, evalRight, ih]

private def normState (st : SymState) : SymState :=
  { st with left := normLeft st.leftIsDefault st.left, right := normRight st.right }

private theorem evalState_normState (vars : ℕ → ℕ) (lBase rBase : ListBlank (Fin 2))
    (st : SymState) :
    evalState vars lBase rBase (normState st) = evalState vars lBase rBase st := by
  dsimp only [evalState, normState]
  rw [evalLeft_normLeft, evalRight_normRight]

private def mkState (steppedPlus : Bool) (dir : Bool) (q : Fin 6) (left : List LAtom)
    (right : List RAtom) (leftIsDefault : Bool) : Option (Bool × SymState) :=
  match left, right with
  | [], [] => some (steppedPlus, ⟨dir, q, [], [], leftIsDefault⟩)
  | [], r :: rs => some (steppedPlus, ⟨dir, q, [], r :: rs, leftIsDefault⟩)
  | l :: ls, [] => some (steppedPlus, ⟨dir, q, l :: ls, [], leftIsDefault⟩)
  | l :: ls, r :: rs => some (steppedPlus, ⟨dir, q, l :: ls, r :: rs, leftIsDefault⟩)

@[simp] private theorem mkState_eq (steppedPlus dir : Bool) (q : Fin 6) (left : List LAtom)
    (right : List RAtom) (leftIsDefault : Bool) :
    mkState steppedPlus dir q left right leftIsDefault = some
      (steppedPlus, ⟨dir, q, left, right, leftIsDefault⟩) := by
  cases left <;> cases right <;> rfl

private def stepSymOne : SymState → Option (Bool × SymState)
  | ⟨true, q, left, .bit b :: r_rest, leftIsDefault⟩ =>
    match tm40 q b with
    | some (some q', Stmt.write w Dir.right) =>
      mkState true true q' (consLeftNorm leftIsDefault (.bit w) left) r_rest leftIsDefault
    | some (some q', Stmt.write w Dir.left) =>
      mkState true false q' left (.bit w :: r_rest) leftIsDefault
    | _ => none
  | ⟨true, q, left, .repX id :: r_rest, leftIsDefault⟩ =>
    if q == B then
      mkState false true B (insertRepDr id left) r_rest leftIsDefault
    else none
  | ⟨true, _, _, [], _⟩ => none
  | ⟨false, q, .bit b :: l_rest, right, leftIsDefault⟩ =>
    match tm40 q b with
    | some (some q', Stmt.write w Dir.left) =>
      mkState true false q' l_rest (.bit w :: right) leftIsDefault
    | some (some q', Stmt.write w Dir.right) =>
      mkState true true q' (consLeftNorm leftIsDefault (.bit w) l_rest) right leftIsDefault
    | _ => none
  | ⟨false, q, .repDr id :: l_rest, right, leftIsDefault⟩ =>
    if q == A then
      mkState false false A l_rest (insertRepX id right) leftIsDefault
    else none
  | ⟨false, q, [], right, true⟩ =>
    match tm40 q 0 with
    | some (some q', Stmt.write w Dir.left) =>
      mkState true false q' [] (.bit w :: right) true
    | some (some q', Stmt.write w Dir.right) =>
      mkState true true q' (consLeftNorm true (.bit w) []) right true
    | _ => none
  | ⟨false, _, [], _, false⟩ => none

private def ReachesMode (moved : Bool) (c₁ c₂ : Cfg (Fin 2) (Fin 6)) : Prop :=
  if moved then c₁ [tm40]⊢* c₂ else c₁ [tm40]⊢⁺ c₂

private theorem ReachesMode.of_plus {moved : Bool} {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [tm40]⊢⁺ c₂) : ReachesMode moved c₁ c₂ := by
  cases moved
  · exact h
  · exact ReachesPlus.to_star h

private theorem ReachesMode.trans_plus_mode {moved : Bool} {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [tm40]⊢⁺ c₂) (h₂ : ReachesMode true c₂ c₃) :
    ReachesMode moved c₁ c₃ :=
  ReachesMode.of_plus (ReachesPlus.trans_star h₁ h₂)

private theorem ReachesMode.trans_star_mode {moved : Bool} {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [tm40]⊢* c₂) (h₂ : ReachesMode moved c₂ c₃) :
    ReachesMode moved c₁ c₃ := by
  cases moved
  · exact ReachesStar.trans_plus h₁ h₂
  · exact ReachesStar.trans h₁ h₂

private theorem stepSymOne_sound (vars : ℕ → ℕ) (lBase rBase : ListBlank (Fin 2))
    (st st' : SymState) (steppedPlus : Bool)
    (hstep : stepSymOne st = some (steppedPlus, st')) :
    if steppedPlus then
      (evalState vars lBase rBase st) [tm40]⊢⁺ (evalState vars lBase rBase st')
    else
      (evalState vars lBase rBase st) [tm40]⊢* (evalState vars lBase rBase st') := by
  rcases st with ⟨dir, q, left, right, leftIsDefault⟩
  dsimp [stepSymOne] at hstep
  rcases dir with _ | _
  · -- dir = false (headLeft)
    rcases left with _ | ⟨a, l_rest⟩
    · -- left = []
      rcases leftIsDefault with _ | _
      · simp at hstep
      · rcases hm : tm40 q 0 with _ | ⟨_ | q', w, _ | _⟩ <;>
          dsimp only [stepSymOne] at hstep <;> rw [hm] at hstep <;> dsimp only at hstep <;>
          try contradiction
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact ReachesPlus.single (step_headLeft_default_left hm (evalRight vars rBase right))
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          dsimp only [evalState]
          rw [evalLeft_consLeftNorm]
          exact ReachesPlus.single (step_headLeft_default_right hm (evalRight vars rBase right))
    · rcases a with b | id
      · rcases hm : tm40 q b with _ | ⟨_ | q', w, _ | _⟩ <;>
          dsimp only [stepSymOne] at hstep <;> rw [hm] at hstep <;> dsimp only at hstep <;>
          try contradiction
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact ReachesPlus.single (step_headLeft_left hm
            (evalLeft vars (if leftIsDefault then default else lBase) l_rest)
            (evalRight vars rBase right))
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          dsimp only [evalState]
          rw [evalLeft_consLeftNorm]
          exact ReachesPlus.single (step_headLeft_right hm
            (evalLeft vars (if leftIsDefault then default else lBase) l_rest)
            (evalRight vars rBase right))
      · by_cases hq : q = A
        · subst hq
          simp only [beq_self_eq_true, ↓reduceIte, mkState_eq, Option.some.injEq,
            Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          dsimp only [evalState]
          rw [evalRight_insertRepX]
          exact shift_A_Dr (vars id)
            (evalLeft vars (if leftIsDefault then default else lBase) l_rest)
            (evalRight vars rBase right)
        · have hqb : (q == A) = false := beq_false_of_ne hq
          simp [hqb] at hstep
  · -- dir = true (headRight)
    rcases right with _ | ⟨a, r_rest⟩
    · simp at hstep
    · rcases a with b | id
      · rcases hm : tm40 q b with _ | ⟨_ | q', w, _ | _⟩ <;>
          dsimp only [stepSymOne] at hstep <;> rw [hm] at hstep <;> dsimp only at hstep <;>
          try contradiction
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          exact ReachesPlus.single (step_headRight_left hm
            (evalLeft vars (if leftIsDefault then default else lBase) left)
            (evalRight vars rBase r_rest))
        · rw [mkState_eq, Option.some.injEq, Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          dsimp only [evalState]
          rw [evalLeft_consLeftNorm]
          exact ReachesPlus.single (step_headRight_right hm
            (evalLeft vars (if leftIsDefault then default else lBase) left)
            (evalRight vars rBase r_rest))
      · by_cases hq : q = B
        · subst hq
          simp only [beq_self_eq_true, ↓reduceIte, mkState_eq, Option.some.injEq,
            Prod.mk.injEq] at hstep
          rcases hstep with ⟨rfl, rfl⟩
          dsimp only [evalState]
          rw [evalLeft_insertRepDr]
          exact shift_B_X (vars id)
            (evalLeft vars (if leftIsDefault then default else lBase) left)
            (evalRight vars rBase r_rest)
        · have hqb : (q == B) = false := beq_false_of_ne hq
          simp [hqb] at hstep

private def runSym (fuel : ℕ) (moved : Bool) (st : SymState) (calls : List CallKind)
    (target : SymState) : Bool :=
  if moved && calls.isEmpty &&
     (st.dir == target.dir && st.q == target.q && st.leftIsDefault == target.leftIsDefault &&
      st.right.isEmpty == target.right.isEmpty && st.left.isEmpty == target.left.isEmpty) &&
     st == target then
    true
  else
    match fuel with
    | 0 => false
    | fuel' + 1 =>
      match stepSymOne st with
      | some (steppedPlus, st') =>
        runSym fuel' (moved || steppedPlus) st' calls target
      | none =>
        match calls with
        | [] => false
        | c :: calls' =>
          if st.dir && st.q == B && st.right.isEmpty then
            match c with
            | .callHf =>
              runSym fuel' true { st with dir := false, q := A } calls' target
            | .callH =>
              match popDr st.left with
              | some l_rest =>
                runSym fuel' true { st with dir := false, q := A, left := l_rest } calls' target
              | none => false
          else
            false

private theorem sideRLs_nil_inv {r r' : ListBlank (Fin 2)}
    (H : SideRLs tm40 [] r r') : r = r' := by
  cases H
  rfl

private theorem sideRLs_cons_inv {g : DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6)}
    {gs : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r r' : ListBlank (Fin 2)}
    (H : SideRLs tm40 (g :: gs) r r') :
    ∃ r1, SideRL tm40 g.1 g.2 r r1 ∧ SideRLs tm40 gs r1 r' := by
  cases H with
  | cons h1 hs => exact ⟨_, h1, hs⟩

private theorem runSym_sound (fuel : ℕ) (moved : Bool) (st target : SymState)
    (calls : List CallKind)
    (h_run : runSym fuel moved st calls target = true)
    (vars : ℕ → ℕ) (lBase rBase rTarget : ListBlank (Fin 2))
    (h_calls : SideRLs tm40 (evalCalls calls) rBase rTarget) :
    ReachesMode moved (evalState vars lBase rBase st) (evalState vars lBase rTarget target) := by
  induction fuel generalizing moved st calls rBase with
  | zero =>
    dsimp [runSym] at h_run
    by_cases h_done : (moved && calls.isEmpty &&
      (st.dir == target.dir && st.q == target.q && st.leftIsDefault == target.leftIsDefault &&
       st.right.isEmpty == target.right.isEmpty && st.left.isEmpty == target.left.isEmpty) &&
      st == target) = true
    · rcases Bool.and_eq_true_iff.mp h_done with ⟨h_pre, h_eq⟩
      rcases Bool.and_eq_true_iff.mp h_pre with ⟨h_mc, _⟩
      rcases Bool.and_eq_true_iff.mp h_mc with ⟨h_moved, h_empty⟩
      subst h_moved
      have h_calls_nil : calls = [] := List.isEmpty_iff.mp h_empty
      subst h_calls_nil
      have hr : rBase = rTarget := sideRLs_nil_inv h_calls
      subst hr
      have h_st : st = target := of_decide_eq_true h_eq
      subst h_st
      exact ReachesStar.refl _ _
    · rw [ite_eq_right h_done] at h_run
      contradiction
  | succ fuel' ih =>
    dsimp [runSym] at h_run
    by_cases h_done : (moved && calls.isEmpty &&
      (st.dir == target.dir && st.q == target.q && st.leftIsDefault == target.leftIsDefault &&
       st.right.isEmpty == target.right.isEmpty && st.left.isEmpty == target.left.isEmpty) &&
      st == target) = true
    · rcases Bool.and_eq_true_iff.mp h_done with ⟨h_pre, h_eq⟩
      rcases Bool.and_eq_true_iff.mp h_pre with ⟨h_mc, _⟩
      rcases Bool.and_eq_true_iff.mp h_mc with ⟨h_moved, h_empty⟩
      subst h_moved
      have h_calls_nil : calls = [] := List.isEmpty_iff.mp h_empty
      subst h_calls_nil
      have hr : rBase = rTarget := sideRLs_nil_inv h_calls
      subst hr
      have h_st : st = target := of_decide_eq_true h_eq
      subst h_st
      exact ReachesStar.refl _ _
    · rw [ite_eq_right h_done] at h_run
      rcases h_step : stepSymOne st with _ | ⟨steppedPlus, st'⟩
      · -- stepSymOne st = none
        rw [h_step] at h_run
        rcases calls with _ | ⟨c, calls'⟩
        · contradiction
        · dsimp at h_run
          by_cases h_cond : (st.dir && st.q == B && st.right.isEmpty) = true
          · rw [ite_eq_left h_cond] at h_run
            rcases Bool.and_eq_true_iff.mp h_cond with ⟨h_dq, h_rempty⟩
            rcases Bool.and_eq_true_iff.mp h_dq with ⟨h_dir, h_qB⟩
            have h_q : st.q = B := of_decide_eq_true h_qB
            have h_r : st.right = [] := List.isEmpty_iff.mp h_rempty
            obtain ⟨rMid, h_head, h_tail⟩ := sideRLs_cons_inv h_calls
            rcases c with _ | _
            · -- .callH
              rcases h_pop : popDr st.left with _ | l_rest
              · rw [h_pop] at h_run
                contradiction
              · rw [h_pop] at h_run
                have h_left := popDr_some h_pop
                have h_ih := ih true { st with dir := false, q := A, left := l_rest }
                  calls' h_run rMid h_tail
                have h_call_step :=
                  h_head (evalLeft vars (if st.leftIsDefault then default else lBase) l_rest)
                dsimp [evalCall, toDHCfg] at h_call_step
                have h_st_eq : evalState vars lBase rBase st =
                    ((1 >> 1 >> 0 >> 0 >> evalLeft vars
                      (if st.leftIsDefault then default else lBase) l_rest) {{B}}> rBase) := by
                  simp [evalState, h_dir, h_q, h_r, h_left, evalRight, evalLeft]
                have h_st'_eq :
                  evalState vars lBase rMid { st with dir := false, q := A, left := l_rest } =
                    (evalLeft vars
                      (if st.leftIsDefault then default else lBase) l_rest <{{A}} rMid) := by
                  simp [evalState, h_r, evalRight]
                rw [← h_st_eq, ← h_st'_eq] at h_call_step
                exact ReachesMode.trans_plus_mode h_call_step h_ih
            · -- .callHf
              have h_ih := ih true { st with dir := false, q := A }
                calls' h_run rMid h_tail
              have h_call_step :=
                h_head (evalLeft vars (if st.leftIsDefault then default else lBase) st.left)
              dsimp [evalCall, toDHCfg] at h_call_step
              have h_st_eq : evalState vars lBase rBase st =
                  (evalLeft vars
                    (if st.leftIsDefault then default else lBase) st.left {{B}}> rBase) := by
                simp [evalState, h_dir, h_q, h_r, evalRight]
              have h_st'_eq : evalState vars lBase rMid { st with dir := false, q := A } =
                  (evalLeft vars (if st.leftIsDefault then default else lBase) st.left <{{A}} rMid)
                    := by
                simp [evalState, h_r, evalRight]
              rw [← h_st_eq, ← h_st'_eq] at h_call_step
              exact ReachesMode.trans_plus_mode h_call_step h_ih
          · rw [ite_eq_right h_cond] at h_run
            contradiction
      · -- stepSymOne st = some (steppedPlus, st')
        rw [h_step] at h_run
        have h_one := stepSymOne_sound vars lBase rBase st st' steppedPlus h_step
        have h_ih := ih (moved || steppedPlus) st' calls h_run rBase h_calls
        rcases steppedPlus with _ | _
        · rw [Bool.or_false] at h_ih
          exact ReachesMode.trans_star_mode h_one h_ih
        · rw [Bool.or_true] at h_ih
          exact ReachesMode.trans_plus_mode h_one h_ih

private theorem runSym_plus (fuel : ℕ) (st target : SymState) (calls : List CallKind)
    (h_run : runSym fuel false (normState st) calls (normState target) = true)
    (vars : ℕ → ℕ) (lBase rBase rTarget : ListBlank (Fin 2))
    (h_calls : SideRLs tm40 (evalCalls calls) rBase rTarget) :
    (evalState vars lBase rBase st) [tm40]⊢⁺ (evalState vars lBase rTarget target) := by
  rw [← evalState_normState vars lBase rBase st, ← evalState_normState vars lBase rTarget target]
  exact runSym_sound fuel false (normState st)
    (normState target) calls h_run vars lBase rBase rTarget h_calls

-- Builder helpers for `SymState`

private def lBits (bs : List (Fin 2)) : List LAtom := bs.map LAtom.bit

private def lDr (k : ℕ) (id : ℕ) : List LAtom := lBits (Dr ^ k) ++ [LAtom.repDr id]

private def rBits (bs : List (Fin 2)) : List RAtom := bs.map RAtom.bit

private def rX (k : ℕ) (id : ℕ) : List RAtom := rBits (X ^ k) ++ [RAtom.repX id]

@[simp] private theorem evalLeft_nil (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2)) :
    evalLeft vars lBase [] = lBase := rfl

@[simp] private theorem evalRight_nil (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2)) :
    evalRight vars rBase [] = rBase := rfl

@[simp] private theorem evalLeft_lBits_append (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (bs : List (Fin 2)) (rest : List LAtom) :
    evalLeft vars lBase (lBits bs ++ rest) = bs +> evalLeft vars lBase rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change b >> evalLeft vars lBase (lBits bs ++ rest) = b >> (bs +> evalLeft vars lBase rest)
    rw [ih]

@[simp] private theorem evalLeft_lBits (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (bs : List (Fin 2)) :
    evalLeft vars lBase (lBits bs) = bs +> lBase := by
  simpa [evalLeft] using evalLeft_lBits_append vars lBase bs []

@[simp] private theorem evalLeft_lDr_append (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2))
    (k id : ℕ) (rest : List LAtom) :
    evalLeft vars lBase (lDr k id ++ rest) =
      (Dr ^ (k + vars id)) +> evalLeft vars lBase rest := by
  simp only [lDr, List.append_assoc, evalLeft_lBits_append, List.singleton_append,
    evalLeft, ListBlank.append_pow_add]

@[simp] private theorem evalLeft_lDr (vars : ℕ → ℕ) (lBase : ListBlank (Fin 2)) (k id : ℕ) :
    evalLeft vars lBase (lDr k id) = (Dr ^ (k + vars id)) +> lBase := by
  simpa [evalLeft] using evalLeft_lDr_append vars lBase k id []

@[simp] private theorem evalRight_rBits_append (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2))
    (bs : List (Fin 2)) (rest : List RAtom) :
    evalRight vars rBase (rBits bs ++ rest) = bs +> evalRight vars rBase rest := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change b >> evalRight vars rBase (rBits bs ++ rest) = b >> (bs +> evalRight vars rBase rest)
    rw [ih]

@[simp] private theorem evalRight_rBits (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2))
    (bs : List (Fin 2)) :
    evalRight vars rBase (rBits bs) = bs +> rBase := by
  simpa [evalRight] using evalRight_rBits_append vars rBase bs []

@[simp] private theorem evalRight_rX_append (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2))
    (k id : ℕ) (rest : List RAtom) :
    evalRight vars rBase (rX k id ++ rest) =
      (X ^ (k + vars id)) +> evalRight vars rBase rest := by
  simp only [rX, List.append_assoc, evalRight_rBits_append, List.singleton_append,
    evalRight, ListBlank.append_pow_add]

@[simp] private theorem evalRight_rX (vars : ℕ → ℕ) (rBase : ListBlank (Fin 2)) (k id : ℕ) :
    evalRight vars rBase (rX k id) = (X ^ (k + vars id)) +> rBase := by
  simpa [evalRight] using evalRight_rX_append vars rBase k id []

private def symRoot (rs : List RAtom) : SymState :=
  { dir := false, q := A, left := [], right := rs, leftIsDefault := true }

private def pending (n : ℕ) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (Pr +> ((Dr ^ n) +> l)) {{B}}> r

private def symPending (k id : ℕ) (ls : List LAtom) (leftIsDefault : Bool) (rs : List RAtom) :
    SymState :=
  { dir := true, q := B, left := lBits Pr ++ (lDr k id ++ ls), right := rs, leftIsDefault :=
    leftIsDefault }

private def symPendingConst (k : ℕ) (ls : List LAtom) (leftIsDefault : Bool) (rs : List RAtom) :
    SymState :=
  { dir := true, q := B, left := lBits Pr ++ (lBits (Dr ^ k) ++ ls), right := rs, leftIsDefault :=
    leftIsDefault }

-- ============================================================================
-- 2. Elementary 2D Longitudinal Tiles (`Others_v2.v` lines 21–55)
-- ============================================================================

private theorem step_X : SegRLs tm40 h h X X :=
  BoundedConfig.segRLs_c_spec tm40 (T := 15) (by decide)

private theorem steps_X (n : ℕ) : SegRLs tm40 h h (X ^ n) (X ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm40 h
  | succ n ih =>
    rw [pow_succ_list X]
    exact step_X.concat ih

private theorem step_FX : SegRLs tm40 hf hf X X :=
  BoundedConfig.segRLs_c_spec tm40 (T := 15) (by decide)

private theorem steps_FX (n : ℕ) : SegRLs tm40 hf hf (X ^ n) (X ^ n) := by
  induction n with
  | zero => exact SegRLs.empty tm40 hf
  | succ n ih =>
    rw [pow_succ_list X]
    exact step_FX.concat ih

private theorem digit_even_0 : SegRLs tm40 h [] (X ++ [0, 0]) (X ++ [0] ++ Y) :=
  BoundedConfig.segRLs_c_spec tm40 (T := 25) (by decide)

private theorem digit_odd_0 : SegRLs tm40 h h (X ++ [0] ++ Y) (X ++ X ++ [0, 0]) :=
  BoundedConfig.segRLs_c_spec tm40 (T := 30) (by decide)

private theorem F_even_0 : SegRLs tm40 hf [] (X ++ [0, 0]) ([0] ++ Y) :=
  BoundedConfig.segRLs_c_spec tm40 (T := 25) (by decide)

private theorem F_odd_0 : SegRLs tm40 hf h ([0] ++ Y) [0, 0] :=
  BoundedConfig.segRLs_c_spec tm40 (T := 25) (by decide)

private theorem digit_even (n : ℕ) :
    SegRLs tm40 h [] (X ^ (1 + n) ++ [0, 0]) (X ^ (1 + n) ++ [0] ++ Y) := by
  have h1 : X ^ (1 + n) ++ [0, 0] = X ^ n ++ (X ++ [0, 0]) := by
    rw [Nat.add_comm 1 n, pow_succ_list', List.append_assoc]
  have h2 : X ^ (1 + n) ++ [0] ++ Y = X ^ n ++ (X ++ [0] ++ Y) := by
    rw [Nat.add_comm 1 n, pow_succ_list']
    simp only [List.append_assoc]
  rw [h1, h2]
  exact (steps_X n).concat digit_even_0

private theorem digit_odd (n : ℕ) :
    SegRLs tm40 h h (X ^ (1 + n) ++ [0] ++ Y) (X ^ (2 + n) ++ [0, 0]) := by
  have h1 : X ^ (1 + n) ++ [0] ++ Y = X ^ n ++ (X ++ [0] ++ Y) := by
    rw [Nat.add_comm 1 n, pow_succ_list']
    simp only [List.append_assoc]
  have h2 : X ^ (2 + n) ++ [0, 0] = X ^ n ++ (X ++ X ++ [0, 0]) := by
    have h2n : 2 + n = n + 1 + 1 := by omega
    rw [h2n, pow_succ_list', pow_succ_list']
    simp only [List.append_assoc]
  rw [h1, h2]
  exact (steps_X n).concat digit_odd_0

private theorem F_even (n : ℕ) :
    SegRLs tm40 hf [] (X ^ (1 + n) ++ [0, 0]) (X ^ n ++ [0] ++ Y) := by
  have h1 : X ^ (1 + n) ++ [0, 0] = X ^ n ++ (X ++ [0, 0]) := by
    rw [Nat.add_comm 1 n, pow_succ_list', List.append_assoc]
  have h2 : X ^ n ++ [0] ++ Y = X ^ n ++ ([0] ++ Y) := by
    rw [List.append_assoc]
  rw [h1, h2]
  exact (steps_FX n).concat F_even_0

private theorem F_odd (n : ℕ) :
    SegRLs tm40 hf h (X ^ n ++ [0] ++ Y) (X ^ n ++ [0, 0]) := by
  have h1 : X ^ n ++ [0] ++ Y = X ^ n ++ ([0] ++ Y) := by
    rw [List.append_assoc]
  rw [h1]
  exact (steps_FX n).concat F_odd_0

-- ============================================================================
-- 3. Recursive Stream Grammar (`Num`, `CutNum`) (`Others_v2.v` lines 59–208)
-- ============================================================================

/-- Complete `E`/`O` stream grammar (`false = E`, `true = O`). -/
private inductive Num : Bool → ℕ → ListBlank (Fin 2) → Prop where
  | O0 : Num true 0 (X +> ([0, 0] +> end0))
  | O1 : Num true 1 (X +> ([0] +> (Y +> end0)))
  | O2 : Num true 2 ((X ^ 2) +> ([0, 0] +> end1))
  | O3 : Num true 3 ((X ^ 2) +> ([0] +> (Y +> end1)))
  | E_even (n : ℕ) (r : ListBlank (Fin 2)) :
      Num true n r → Num false (n * 2) ((X ^ (1 + n)) +> ([0, 0] +> r))
  | E_odd (n : ℕ) (r : ListBlank (Fin 2)) :
      Num true n r → Num false (1 + n * 2) ((X ^ (1 + n)) +> ([0] +> (Y +> r)))
  | O_even (n : ℕ) (r : ListBlank (Fin 2)) :
      Num false n r → Num true (4 + n * 2) ((X ^ (3 + n)) +> ([0, 0] +> r))
  | O_odd (n : ℕ) (r : ListBlank (Fin 2)) :
      Num false n r → Num true (5 + n * 2) ((X ^ (3 + n)) +> ([0] +> (Y +> r)))

private def CutNum (b : Bool) (n d : ℕ) (r : ListBlank (Fin 2)) : Prop :=
  Num b n ((X ^ d) +> r)

private theorem side_O0_O1 :
    SideRLs tm40 h (X +> ([0, 0] +> end0)) (X +> ([0] +> (Y +> end0))) :=
  SideRLs.cons (fun l => by dsimp only [end0, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem side_O1_O2 :
    SideRLs tm40 h (X +> ([0] +> (Y +> end0))) ((X ^ 2) +> ([0, 0] +> end1)) :=
  SideRLs.cons (fun l => by dsimp only [end0, end1, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem side_O2_O3 :
    SideRLs tm40 h ((X ^ 2) +> ([0, 0] +> end1)) ((X ^ 2) +> ([0] +> (Y +> end1))) :=
  SideRLs.cons (fun l => by dsimp only [end1, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem side_O3_O4 :
    SideRLs tm40 h ((X ^ 2) +> ([0] +> (Y +> end1)))
      ((X ^ 3) +> ([0, 0] +> (X +> ([0, 0] +> (X +> ([0, 0] +> end0)))))) :=
  SideRLs.cons (fun l => by dsimp only [end0, end1, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem side_end0_end1 :
    SideRLs tm40 h end0 end1 :=
  SideRLs.cons (fun l => by dsimp only [end0, end1, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem side_end1_O4 :
    SideRLs tm40 h end1 (X +> ([0, 0] +> (X +> ([0, 0] +> end0)))) :=
  SideRLs.cons (fun l => by dsimp only [end0, end1, toDHCfg]; bb_steps) (SideRLs.nil _)

private theorem Num_inc {b : Bool} {n : ℕ} {r : ListBlank (Fin 2)} (H : Num b n r) :
    ∃ r', Num b (1 + n) r' ∧ SideRLs tm40 h r r' := by
  induction H with
  | O0 => exact ⟨_, Num.O1, side_O0_O1⟩
  | O1 => exact ⟨_, Num.O2, side_O1_O2⟩
  | O2 => exact ⟨_, Num.O3, side_O2_O3⟩
  | O3 =>
    refine ⟨_, ?_, side_O3_O4⟩
    exact Num.O_even 0 _ (Num.E_even 0 _ Num.O0)
  | E_even n r hn =>
    refine ⟨(X ^ (1 + n)) +> ([0] +> (Y +> r)), Num.E_odd n r hn, ?_⟩
    have h_seg := (digit_even n).sideRLs_concat (SideRLs.nil r)
    simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg
  | E_odd n r hn ih =>
    obtain ⟨r', hn', hr'⟩ := ih
    refine ⟨(X ^ (2 + n)) +> ([0, 0] +> r'), ?_, ?_⟩
    · have h_idx : 1 + (1 + n * 2) = (1 + n) * 2 := by omega
      have h_exp : 2 + n = 1 + (1 + n) := by omega
      rw [h_idx, h_exp]
      exact Num.E_even (1 + n) r' hn'
    · have h_seg := (digit_odd n).sideRLs_concat hr'
      simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg
  | O_even n r hn =>
    refine ⟨(X ^ (3 + n)) +> ([0] +> (Y +> r)), ?_, ?_⟩
    · have h_idx : 1 + (4 + n * 2) = 5 + n * 2 := by omega
      rw [h_idx]
      exact Num.O_odd n r hn
    · have h_seg := (digit_even (2 + n)).sideRLs_concat (SideRLs.nil r)
      have h_exp : 1 + (2 + n) = 3 + n := by omega
      rw [h_exp] at h_seg
      simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg
  | O_odd n r hn ih =>
    obtain ⟨r', hn', hr'⟩ := ih
    refine ⟨(X ^ (4 + n)) +> ([0, 0] +> r'), ?_, ?_⟩
    · have h_idx : 1 + (5 + n * 2) = 4 + (1 + n) * 2 := by omega
      have h_exp : 4 + n = 3 + (1 + n) := by omega
      rw [h_idx, h_exp]
      exact Num.O_even (1 + n) r' hn'
    · have h_seg := (digit_odd (2 + n)).sideRLs_concat hr'
      have h_exp1 : 1 + (2 + n) = 3 + n := by omega
      have h_exp2 : 2 + (2 + n) = 4 + n := by omega
      rw [h_exp1, h_exp2] at h_seg
      simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg

private theorem Num_ex (b : Bool) (n : ℕ) : ∃ r, Num b n r := by
  induction n with
  | zero =>
    cases b
    · exact ⟨_, Num.E_even 0 _ Num.O0⟩
    · exact ⟨_, Num.O0⟩
  | succ n ih =>
    obtain ⟨r, hr⟩ := ih
    obtain ⟨r', hn', _⟩ := Num_inc hr
    rw [Nat.add_comm 1 n] at hn'
    exact ⟨r', hn'⟩

private theorem Num_unique_aux {b : Bool} {n : ℕ} {r : ListBlank (Fin 2)} (H : Num b n r) :
    ∀ {m : ℕ} {r' : ListBlank (Fin 2)}, Num b m r' → n = m → r = r' := by
  induction H with
  | O0 =>
    intro m r' H' hm
    cases H' <;> first | rfl | omega
  | O1 =>
    intro m r' H' hm
    cases H' <;> first | rfl | omega
  | O2 =>
    intro m r' H' hm
    cases H' <;> first | rfl | omega
  | O3 =>
    intro m r' H' hm
    cases H' <;> first | rfl | omega
  | E_even n r hn ih =>
    intro m r' H' hm
    cases H' with
    | E_even n' r' hn' =>
      have hn_eq : n = n' := by omega
      subst hn_eq
      rw [ih hn' rfl]
    | _ => omega
  | E_odd n r hn ih =>
    intro m r' H' hm
    cases H' with
    | E_odd n' r' hn' =>
      have hn_eq : n = n' := by omega
      subst hn_eq
      rw [ih hn' rfl]
    | _ => omega
  | O_even n r hn ih =>
    intro m r' H' hm
    cases H' with
    | O_even n' r' hn' =>
      have hn_eq : n = n' := by omega
      subst hn_eq
      rw [ih hn' rfl]
    | _ => omega
  | O_odd n r hn ih =>
    intro m r' H' hm
    cases H' with
    | O_odd n' r' hn' =>
      have hn_eq : n = n' := by omega
      subst hn_eq
      rw [ih hn' rfl]
    | _ => omega

private theorem Num_unique {b : Bool} {n : ℕ} {r r' : ListBlank (Fin 2)}
    (H : Num b n r) (H' : Num b n r') : r = r' :=
  Num_unique_aux H H' rfl

private theorem Num_add (m : ℕ) (b : Bool) (n : ℕ) (r : ListBlank (Fin 2)) (H : Num b n r) :
    ∃ r', Num b (n + m) r' ∧ SideRLs tm40 (h ^ m) r r' := by
  induction m generalizing n r with
  | zero => exact ⟨r, H, SideRLs.nil r⟩
  | succ m ih =>
    obtain ⟨r1, hn1, hr1⟩ := Num_inc H
    obtain ⟨r2, hn2, hr2⟩ := ih (1 + n) r1 hn1
    refine ⟨r2, ?_, ?_⟩
    · have h_idx : 1 + n + m = n + (m + 1) := by omega
      rwa [h_idx] at hn2
    · rw [pow_succ_list h]
      exact hr1.trans hr2

private inductive NumView (b : Bool) : ℕ → ListBlank (Fin 2) → Prop where
  | NV_even (k : ℕ) (r : ListBlank (Fin 2)) :
      Num b (1 + k * 2) ((X ^ (1 + k)) +> ([0] +> (Y +> r))) →
      NumView b (k * 2) ((X ^ (1 + k)) +> ([0, 0] +> r))
  | NV_odd (k : ℕ) (r r' : ListBlank (Fin 2)) :
      SideRLs tm40 h r r' →
      Num b (2 + k * 2) ((X ^ (2 + k)) +> ([0, 0] +> r')) →
      NumView b (1 + k * 2) ((X ^ (1 + k)) +> ([0] +> (Y +> r)))

private theorem Num_view {b : Bool} {n : ℕ} {r : ListBlank (Fin 2)} (H : Num b n r) :
    NumView b n r := by
  cases H with
  | O0 => exact NumView.NV_even 0 end0 Num.O1
  | O1 => exact NumView.NV_odd 0 end0 end1 side_end0_end1 Num.O2
  | O2 => exact NumView.NV_even 1 end1 Num.O3
  | O3 =>
    refine NumView.NV_odd 1 end1 (X +> ([0, 0] +> (X +> ([0, 0] +> end0)))) side_end1_O4 ?_
    exact Num.O_even 0 _ (Num.E_even 0 _ Num.O0)
  | E_even n r hn => exact NumView.NV_even n r (Num.E_odd n r hn)
  | E_odd n r hn =>
    obtain ⟨r', hn', hr'⟩ := Num_inc hn
    have h_num := Num.E_even (1 + n) r' hn'
    have h_idx : (1 + n) * 2 = 2 + n * 2 := by omega
    have h_exp : 1 + (1 + n) = 2 + n := by omega
    rw [h_idx, h_exp] at h_num
    exact NumView.NV_odd n r r' hr' h_num
  | O_even n r hn =>
    have h_num := Num.O_odd n r hn
    have h_idx1 : 5 + n * 2 = 1 + (2 + n) * 2 := by omega
    have h_idx2 : (2 + n) * 2 = 4 + n * 2 := by omega
    have h_exp : 1 + (2 + n) = 3 + n := by omega
    rw [h_idx1, ← h_exp] at h_num
    have h_nv := NumView.NV_even (2 + n) r h_num
    rwa [h_idx2, h_exp] at h_nv
  | O_odd n r hn =>
    obtain ⟨r', hn', hr'⟩ := Num_inc hn
    have h_num := Num.O_even (1 + n) r' hn'
    have h_idx1 : 4 + (1 + n) * 2 = 2 + (2 + n) * 2 := by omega
    have h_idx2 : 1 + (2 + n) * 2 = 5 + n * 2 := by omega
    have h_exp1 : 3 + (1 + n) = 2 + (2 + n) := by omega
    have h_exp2 : 1 + (2 + n) = 3 + n := by omega
    rw [h_idx1, h_exp1] at h_num
    have h_nv := NumView.NV_odd (2 + n) r r' hr' h_num
    rwa [h_idx2, h_exp2] at h_nv

private theorem prefix_cancel (w : List (Fin 2)) {r r' : ListBlank (Fin 2)}
    (H : w +> r = w +> r') : r = r' := by
  induction w with
  | nil => exact H
  | cons a w ih =>
    apply ih
    have h_tail := congrArg ListBlank.tail H
    simpa only [ListBlank.append_cons, ListBlank.tail_cons] using h_tail

private theorem cut_prefix (a d : ℕ) (r t : ListBlank (Fin 2)) (hd : d ≤ a)
    (H : (X ^ d) +> r = (X ^ a) +> t) : r = (X ^ (a - d)) +> t := by
  apply prefix_cancel (X ^ d)
  rw [← ListBlank.append_pow_add]
  have h_add : d + (a - d) = a := by omega
  rw [h_add]
  exact H

private theorem CutNum_F (b : Bool) (n d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b n d r) (hd : d * 2 ≤ 1 + n) :
    ∃ r', CutNum b (1 + n) (1 + d) r' ∧ SideRLs tm40 hf r r' := by
  have h_nv := Num_view H
  generalize hs : (X ^ d) +> r = s at h_nv
  cases h_nv with
  | NV_even k r0 hnum =>
    have hr : r = (X ^ (1 + (k - d))) +> ([0, 0] +> r0) := by
      rw [cut_prefix (1 + k) d r ([0, 0] +> r0) (by omega) hs]
      have h_sub : 1 + k - d = 1 + (k - d) := by omega
      rw [h_sub]
    subst hr
    refine ⟨(X ^ (k - d)) +> ([0] +> (Y +> r0)), ?_, ?_⟩
    · unfold CutNum
      rw [← ListBlank.append_pow_add]
      have h_exp : 1 + d + (k - d) = 1 + k := by omega
      rw [h_exp]
      exact hnum
    · have h_seg := (F_even (k - d)).sideRLs_concat (SideRLs.nil r0)
      simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg
  | NV_odd k r0 r' hside hnum =>
    have hr : r = (X ^ (1 + k - d)) +> ([0] +> (Y +> r0)) :=
      cut_prefix (1 + k) d r ([0] +> (Y +> r0)) (by omega) hs
    subst hr
    refine ⟨(X ^ (1 + k - d)) +> ([0, 0] +> r'), ?_, ?_⟩
    · unfold CutNum
      rw [← ListBlank.append_pow_add]
      have h_exp : 1 + d + (1 + k - d) = 2 + k := by omega
      have h_idx : 1 + (1 + k * 2) = 2 + k * 2 := by omega
      rw [h_exp, h_idx]
      exact hnum
    · have h_seg := (F_odd (1 + k - d)).sideRLs_concat hside
      simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg

private theorem CutNum_Fs (m : ℕ) (b : Bool) (n d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b n d r) (hd : d * 2 + m ≤ 2 + n) :
    ∃ r', CutNum b (n + m) (d + m) r' ∧ SideRLs tm40 (hf ^ m) r r' := by
  induction m generalizing n d r with
  | zero => exact ⟨r, H, SideRLs.nil r⟩
  | succ m ih =>
    obtain ⟨r1, hn1, hr1⟩ := CutNum_F b n d r H (by omega)
    obtain ⟨r2, hn2, hr2⟩ := ih (1 + n) (1 + d) r1 hn1 (by omega)
    refine ⟨r2, ?_, ?_⟩
    · have h_n : 1 + n + m = n + (m + 1) := by omega
      have h_d : 1 + d + m = d + (m + 1) := by omega
      rwa [h_n, h_d] at hn2
    · rw [pow_succ_list hf]
      exact hr1.trans hr2

-- ============================================================================
-- 4. Main Loop Step (`Q_step`, `InLoop`, `loop_progress`) (`Others_v2.v` lines 211–480)
-- ============================================================================

set_option maxRecDepth 100000 in
private theorem normal_cycle (n : ℕ) (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r r3) :
    (root ((X ^ (3 + n)) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root ((X ^ (2 + n)) +> ([0, 0] +> r3))) := by
  have h_run := runSym_plus 300
    (symRoot (rX 3 0 ++ rBits [0, 0]))
    (symRoot (rX 2 0 ++ rBits [0, 0]))
    (List.replicate 3 .callH) (by decide) (fun _ => n) default r r3 H
  simpa [evalState, symRoot, root] using h_run

private theorem normal_end (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r r3) :
    (root ((X ^ 2) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root (X +> ([0] +> (X +> r3)))) := by
  have h_run := runSym_plus 300
    (symRoot (rBits (X ^ 2 ++ [0, 0])))
    (symRoot (rBits (X ++ [0] ++ X)))
    (List.replicate 3 .callH) (by decide) (fun _ => 0) default r r3 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem normal_odd (n : ℕ) (r r2 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r r2) :
    (root ((X ^ (2 + n)) +> ([0] +> (Y +> r)))) [tm40]⊢⁺
      (root ((X ^ (2 + n)) +> ([0, 0] +> r2))) := by
  have h_run := runSym_plus 300
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y)))
    (symRoot (rX 2 0 ++ rBits [0, 0]))
    (List.replicate 2 .callH) (by decide) (fun _ => n) default r r2 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem marker_cycle (p a : ℕ) (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r r3) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (4 + a)) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> r3))))) := by
  have h_run := runSym_plus 400
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 4 1 ++ rBits [0, 0]))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits [0, 0]))))
    (List.replicate 3 .callH) (by decide) (fun i => if i = 0 then p else a) default r r3 H
  simpa [evalState, symRoot, root] using h_run

private theorem Num_normal (n : ℕ) (b : Bool) (j : ℕ) (r : ListBlank (Fin 2)) (H : Num b j r) :
    ∃ r', Num b (j + 3 + n * 3) r' ∧
      ((root ((X ^ (2 + n)) +> ([0, 0] +> r))) [tm40]⊢⁺ (root (X +> ([0] +> (X +> r'))))) := by
  induction n generalizing j r with
  | zero =>
    obtain ⟨r', hn', hr'⟩ := Num_add 3 b j r H
    exact ⟨r', hn', normal_end r r' hr'⟩
  | succ n ih =>
    obtain ⟨r1, hn1, hr1⟩ := Num_add 3 b j r H
    obtain ⟨r2, hn2, hr2⟩ := ih (j + 3) r1 hn1
    refine ⟨r2, ?_, ?_⟩
    · have h_idx : j + 3 + 3 + n * 3 = j + 3 + (n + 1) * 3 := by omega
      rwa [h_idx] at hn2
    · have h_exp : 2 + (n + 1) = 3 + n := by omega
      rw [h_exp]
      exact ReachesPlus.trans (normal_cycle n r r1 hr1) hr2

private theorem Num_normal_odd (n : ℕ) (b : Bool) (j : ℕ) (r : ListBlank (Fin 2)) (H : Num b j r) :
    ∃ r', Num b (j + 5 + n * 3) r' ∧
      ((root ((X ^ (2 + n)) +> ([0] +> (Y +> r)))) [tm40]⊢⁺ (root (X +> ([0] +> (X +> r'))))) := by
  obtain ⟨r1, hn1, hr1⟩ := Num_add 2 b j r H
  obtain ⟨r2, hn2, hr2⟩ := Num_normal n b (j + 2) r1 hn1
  refine ⟨r2, ?_, ReachesPlus.trans (normal_odd n r r1 hr1) hr2⟩
  have h_idx : j + 2 + 3 + n * 3 = j + 5 + n * 3 := by omega
  rwa [h_idx] at hn2

private theorem Num_markers (m p a : ℕ) (b : Bool) (j : ℕ) (r : ListBlank (Fin 2)) (H : Num b j r) :
    ∃ r', Num b (j + m * 3) r' ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + a + m * 3)) +> ([0, 0] +> r))))) [tm40]⊢*
        (root ((X ^ (1 + p + m)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> r')))))) := by
  induction m generalizing p j r with
  | zero =>
    exact ⟨r, H, ReachesStar.refl _ _⟩
  | succ m ih =>
    obtain ⟨r1, hn1, hr1⟩ := Num_add 3 b j r H
    obtain ⟨r2, hn2, hr2⟩ := ih (1 + p) (j + 3) r1 hn1
    refine ⟨r2, ?_, ?_⟩
    · have h_idx : j + 3 + m * 3 = j + (m + 1) * 3 := by omega
      rwa [h_idx] at hn2
    · have h_step := marker_cycle p (a + m * 3) r r1 hr1
      have h_exp1 : 1 + a + (m + 1) * 3 = 4 + (a + m * 3) := by omega
      have h_exp2 : 1 + (1 + p) + m = 1 + p + (m + 1) := by omega
      have h_exp3 : 1 + (1 + p) = 2 + p := by omega
      have h_exp4 : 1 + a + m * 3 = 1 + (a + m * 3) := by omega
      rw [h_exp1]
      rw [h_exp2, h_exp3, h_exp4] at hr2
      exact ReachesPlus.to_star (ReachesPlus.trans_star h_step hr2)

private theorem pending_cycle (n : ℕ) (l r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r r3) :
    (pending (1 + n) l r) [tm40]⊢⁺ (pending n l (X +> r3)) := by
  have h_run := runSym_plus 300
    (symPending 1 0 [] false [])
    (symPending 0 0 [] false (rBits X))
    (List.replicate 3 .callHf) (by decide) (fun _ => n) l r r3 H
  simpa [evalState, symPending, pending] using h_run

private theorem pending_end (l r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r r3) :
    (pending 0 l r) [tm40]⊢⁺ (l <{{F}} ([1, 0] +> (Y +> (X +> r3)))) := by
  have h_run := runSym_plus 300
    (symPendingConst 0 [] false [])
    { dir := false, q := F, left := [], right := rBits ([1, 0] ++ Y ++ X), leftIsDefault := false }
    (List.replicate 3 .callHf) (by decide) (fun _ => 0) l r r3 H
  simpa [evalState, symPendingConst, pending, ListBlank.append_assoc] using h_run

private theorem CutNum_prepend (b : Bool) (j d k : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b j (d + k) r) : CutNum b j d ((X ^ k) +> r) := by
  unfold CutNum at H ⊢
  rwa [← ListBlank.append_pow_add]

private theorem Num_pending (q : ℕ) (l : ListBlank (Fin 2)) (b : Bool) (j d : ℕ)
    (r : ListBlank (Fin 2))
    (H : CutNum b j d r) (hd : d * 2 + q + 2 ≤ j) :
    ∃ r', CutNum b (j + (1 + q) * 3) (d + (1 + q) * 2) r' ∧
      ((pending q l r) [tm40]⊢⁺ (l <{{F}} ([1, 0] +> (Y +> r')))) := by
  induction q generalizing j d r with
  | zero =>
    obtain ⟨r3, hn3, hr3⟩ := CutNum_Fs 3 b j d r H (by omega)
    refine ⟨X +> r3, ?_, pending_end l r r3 hr3⟩
    have hc := CutNum_prepend b (j + 3) (d + 2) 1 r3 (by
      have h_d : d + 2 + 1 = d + 3 := by omega
      rwa [h_d])
    simpa using hc
  | succ q ih =>
    obtain ⟨r3, hn3, hr3⟩ := CutNum_Fs 3 b j d r H (by omega)
    have hc : CutNum b (j + 3) (d + 2) (X +> r3) := by
      have hc0 := CutNum_prepend b (j + 3) (d + 2) 1 r3 (by
        have h_d : d + 2 + 1 = d + 3 := by omega
        rwa [h_d])
      simpa using hc0
    obtain ⟨r4, hn4, hr4⟩ := ih (j + 3) (d + 2) (X +> r3) hc (by omega)
    refine ⟨r4, ?_, ?_⟩
    · have h_j : j + 3 + (1 + q) * 3 = j + (1 + (q + 1)) * 3 := by omega
      have h_d : d + 2 + (1 + q) * 2 = d + (1 + (q + 1)) * 2 := by omega
      rwa [h_j, h_d] at hn4
    · have h_exp : q + 1 = 1 + q := by omega
      rw [h_exp]
      exact ReachesPlus.trans (pending_cycle q l r r3 hr3) hr4

set_option maxRecDepth 100000 in
private theorem a3_prepare (q : ℕ) (r r2 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r r2) :
    (root ((X ^ (1 + q)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending q ([1, 1] +> default) r2) := by
  have h_run := runSym_plus 300
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ^ 3 ++ [0, 0])))
    (symPending 0 0 (lBits [1, 1]) true [])
    (List.replicate 2 .callH) (by decide) (fun _ => q) default r r2 H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem a3_finish (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r r3) :
    (([1, 1] +> default) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ 3) +> r3)) := by
  have h_run := runSym_plus 300
    { dir := false, q := F, left := lBits [1, 1], right := rBits ([1, 0] ++ Y), leftIsDefault :=
      true }
    (symRoot (rBits (X ^ 3)))
    (List.replicate 3 .callHf) (by decide) (fun _ => 0) default r r3 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem Num_a3 (q : ℕ) (b : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (H : Num b j r) (hj : q + 2 ≤ j) :
    ∃ r', CutNum b (j + 8 + q * 3) (2 + q * 2) r' ∧
      ((root ((X ^ (1 + q)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺ (root r')) := by
  obtain ⟨r1, hn1, hr1⟩ := Num_add 2 b j r H
  have hc1 : CutNum b (j + 2) 0 r1 := hn1
  obtain ⟨r2, hn2, hr2⟩ := Num_pending q ([1, 1] +> default) b (j + 2) 0 r1 hc1 (by omega)
  obtain ⟨r3, hn3, hr3⟩ := CutNum_Fs 3 b (j + 2 + (1 + q) * 3) (0 + (1 + q) * 2) r2 hn2 (by omega)
  refine ⟨(X ^ 3) +> r3, ?_, ?_⟩
  · have hc3 := CutNum_prepend b (j + 8 + q * 3) (2 + q * 2) 3 r3 (by
      have h_j : j + 2 + (1 + q) * 3 + 3 = j + 8 + q * 3 := by omega
      have h_d : 0 + (1 + q) * 2 + 3 = 2 + q * 2 + 3 := by omega
      rwa [h_j, h_d] at hn3)
    exact hc3
  · exact ReachesPlus.trans (a3_prepare q r r1 hr1) (ReachesPlus.trans hr2 (a3_finish r2 r3 hr3))

private theorem Num_E_even_inv (k : ℕ) (s : ListBlank (Fin 2)) (H : Num false (k * 2) s) :
    ∃ r, Num true k r ∧ s = (X ^ (1 + k)) +> ([0, 0] +> r) := by
  obtain ⟨r, hr⟩ := Num_ex true k
  exact ⟨r, hr, Num_unique H (Num.E_even k r hr)⟩

private theorem Num_E_odd_inv (k : ℕ) (s : ListBlank (Fin 2)) (H : Num false (1 + k * 2) s) :
    ∃ r, Num true k r ∧ s = (X ^ (1 + k)) +> ([0] +> (Y +> r)) := by
  obtain ⟨r, hr⟩ := Num_ex true k
  exact ⟨r, hr, Num_unique H (Num.E_odd k r hr)⟩

private theorem Num_O_even_inv (k : ℕ) (s : ListBlank (Fin 2)) (H : Num true (4 + k * 2) s) :
    ∃ r, Num false k r ∧ s = (X ^ (3 + k)) +> ([0, 0] +> r) := by
  obtain ⟨r, hr⟩ := Num_ex false k
  exact ⟨r, hr, Num_unique H (Num.O_even k r hr)⟩

private theorem Q_normal (n : ℕ) (s : ListBlank (Fin 2))
    (H : CutNum false (16 + n * 9) (4 + n * 2) s) :
    ∃ r, Num true (20 + n * 12) r ∧
      ((root s) [tm40]⊢⁺ (root (X +> ([0] +> (X +> r))))) := by
  unfold CutNum at H
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · have hv : Num false ((8 + k * 9) * 2) ((X ^ (4 + 2 * k * 2)) +> s) := by
      have h_idx : 16 + 2 * k * 9 = (8 + k * 9) * 2 := by omega
      rwa [h_idx] at H
    obtain ⟨r, hn, he⟩ := Num_E_even_inv (8 + k * 9) _ hv
    have hs : s = (X ^ (5 + k * 5)) +> ([0, 0] +> r) := by
      rw [cut_prefix (1 + (8 + k * 9)) (4 + 2 * k * 2) s ([0, 0] +> r) (by omega) he]
      have h_sub : 1 + (8 + k * 9) - (4 + 2 * k * 2) = 5 + k * 5 := by omega
      rw [h_sub]
    obtain ⟨r', hn', hr'⟩ := Num_normal (3 + k * 5) true (8 + k * 9) r hn
    refine ⟨r', ?_, ?_⟩
    · have h_idx : 8 + k * 9 + 3 + (3 + k * 5) * 3 = 20 + 2 * k * 12 := by omega
      rwa [h_idx] at hn'
    · rw [hs]
      have h_exp : 5 + k * 5 = 2 + (3 + k * 5) := by omega
      rw [h_exp]
      exact hr'
  · have hv : Num false (1 + (12 + k * 9) * 2) ((X ^ (4 + (2 * k + 1) * 2)) +> s) := by
      have h_idx : 16 + (2 * k + 1) * 9 = 1 + (12 + k * 9) * 2 := by omega
      rwa [h_idx] at H
    obtain ⟨r, hn, he⟩ := Num_E_odd_inv (12 + k * 9) _ hv
    have hs : s = (X ^ (7 + k * 5)) +> ([0] +> (Y +> r)) := by
      rw [cut_prefix (1 + (12 + k * 9)) (4 + (2 * k + 1) * 2) s ([0] +> (Y +> r)) (by omega) he]
      have h_sub : 1 + (12 + k * 9) - (4 + (2 * k + 1) * 2) = 7 + k * 5 := by omega
      rw [h_sub]
    obtain ⟨r', hn', hr'⟩ := Num_normal_odd (5 + k * 5) true (12 + k * 9) r hn
    refine ⟨r', ?_, ?_⟩
    · have h_idx : 12 + k * 9 + 5 + (5 + k * 5) * 3 = 20 + (2 * k + 1) * 12 := by omega
      rwa [h_idx] at hn'
    · rw [hs]
      have h_exp : 7 + k * 5 = 2 + (5 + k * 5) := by omega
      rw [h_exp]
      exact hr'

private theorem Q_finish (n : ℕ) (s : ListBlank (Fin 2)) (H : Num true (20 + n * 12) s) :
    ∃ r, Num false (17 + n * 12) r ∧
      ((root (X +> ([0] +> (X +> s)))) [tm40]⊢*
        (root ((X ^ (4 + n * 2)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))) := by
  have hv : Num true (4 + (8 + n * 6) * 2) s := by
    have h_idx : 20 + n * 12 = 4 + (8 + n * 6) * 2 := by omega
    rwa [h_idx] at H
  obtain ⟨r, hn, rfl⟩ := Num_O_even_inv (8 + n * 6) s hv
  obtain ⟨r', hn', hr'⟩ := Num_markers (3 + n * 2) 0 2 false (8 + n * 6) r hn
  refine ⟨r', ?_, ?_⟩
  · have h_idx : 8 + n * 6 + (3 + n * 2) * 3 = 17 + n * 12 := by omega
    rwa [h_idx] at hn'
  · have h_lhs : X +> ([0] +> (X +> ((X ^ (3 + (8 + n * 6))) +> ([0, 0] +> r)))) =
        (X ^ (1 + 0)) +> ([0] +> ((X ^ (1 + 2 + (3 + n * 2) * 3)) +> ([0, 0] +> r))) := by
      have h_exp : 1 + 2 + (3 + n * 2) * 3 = (3 + (8 + n * 6)) + 1 := by omega
      rw [h_exp, ListBlank.append_pow_succ]
      rfl
    have h_rhs : 1 + 0 + (3 + n * 2) = 4 + n * 2 := by omega
    rw [h_lhs, ← h_rhs]
    exact hr'

private theorem Q_step (n : ℕ) (r : ListBlank (Fin 2)) (hnum : Num false (5 + n * 6) r) :
    ∃ r', Num false (17 + n * 12) r' ∧
      ((root ((X ^ (2 + n)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (4 + n * 2)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r')))))) := by
  have h_exp_in : 2 + n = 1 + (1 + n) := by omega
  rw [h_exp_in]
  obtain ⟨r1, hn1, hr1⟩ := Num_a3 (1 + n) false (5 + n * 6) r hnum (by omega)
  have hc1 : CutNum false (16 + n * 9) (4 + n * 2) r1 := by
    have h_j : 5 + n * 6 + 8 + (1 + n) * 3 = 16 + n * 9 := by omega
    have h_d : 2 + (1 + n) * 2 = 4 + n * 2 := by omega
    rwa [h_j, h_d] at hn1
  obtain ⟨r2, hn2, hr2⟩ := Q_normal n r1 hc1
  obtain ⟨r3, hn3, hr3⟩ := Q_finish n r2 hn2
  exact ⟨r3, hn3, ReachesPlus.trans_star (ReachesPlus.trans hr1 hr2) hr3⟩

private inductive InLoop : Cfg (Fin 2) (Fin 6) → Prop where
  | in_loop (n : ℕ) (r : ListBlank (Fin 2)) :
      Num false (5 + n * 6) r →
      InLoop (root ((X ^ (2 + n)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))

private theorem loop_progress (c : Cfg (Fin 2) (Fin 6)) (h : InLoop c) :
    ∃ c', (c [tm40]⊢⁺ c') ∧ InLoop c' := by
  rcases h with ⟨n, r, hnum⟩
  obtain ⟨r', hnum', hstep⟩ := Q_step n r hnum
  refine ⟨root ((X ^ (2 + (2 + n * 2))) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r')))), ?_, ?_⟩
  · have h_exp : 2 + (2 + n * 2) = 4 + n * 2 := by omega
    rw [h_exp]
    exact hstep
  · refine InLoop.in_loop (2 + n * 2) r' ?_
    have h_idx : 5 + (2 + n * 2) * 6 = 17 + n * 12 := by omega
    rw [h_idx]
    exact hnum'

-- ============================================================================
-- 5. Initial Stem (`seed`, `init_to_seed`) (`Others_v2.v` lines 482–5128)
-- ============================================================================

private def seed : ListBlank (Fin 2) :=
  (X ^ 8) +>
    ([0] +> (Y +> ((X ^ 4) +> ([0] +> (Y +> (X +> ([0] +> (Y +> (X +> ([0, 0] +> end0))))))))))

private theorem seed_num : Num false 15 seed := by
  unfold seed
  exact Num.E_odd 7 _ (Num.O_odd 1 _ (Num.E_odd 0 _ Num.O0))

private def seed_word : List (Fin 2) :=
  X ^ 10 ++ ([0, 0] ++ (X ^ 8 ++ ([0] ++ (Y ++ (X ^ 4 ++ ([0] ++ (Y ++
    (X ++ ([0] ++ (Y ++ (X ++ ([0, 0] ++ ([0, 0] ++ Y)))))))))))))

private def seed_natCfg : NatCfg := ⟨0, 0, 0, encodeList seed_word 0⟩

private abbrev init_seed_steps : ℕ := 14665

private theorem eq_mp_rev {P Q : Prop} (h : P) (heq : Q = P) : Q := heq ▸ h

private theorem append_X_pow (m n : ℕ) (r : ListBlank (Fin 2)) :
    (X ^ m) +> ((X ^ n) +> r) = (X ^ (m + n)) +> r := by
  rw [← ListBlank.append_pow_add]

private theorem append_X_left (n : ℕ) (r : ListBlank (Fin 2)) :
    X +> ((X ^ n) +> r) = (X ^ (1 + n)) +> r := by
  have h := append_X_pow 1 n r
  rwa [pow_one_list X] at h

private theorem append_X_right (n : ℕ) (r : ListBlank (Fin 2)) :
    (X ^ n) +> (X +> r) = (X ^ (n + 1)) +> r := by
  have h := append_X_pow n 1 r
  rwa [pow_one_list X] at h

private theorem append_Dr_pow (m n : ℕ) (l : ListBlank (Fin 2)) :
    (Dr ^ m) +> ((Dr ^ n) +> l) = (Dr ^ (m + n)) +> l := by
  rw [← ListBlank.append_pow_add]

private theorem append_Dr_left (n : ℕ) (l : ListBlank (Fin 2)) :
    Dr +> ((Dr ^ n) +> l) = (Dr ^ (1 + n)) +> l := by
  have h := append_Dr_pow 1 n l
  rwa [pow_one_list Dr] at h

private theorem append_Dr_right (n : ℕ) (l : ListBlank (Fin 2)) :
    (Dr ^ n) +> (Dr +> l) = (Dr ^ (n + 1)) +> l := by
  have h := append_Dr_pow n 1 l
  rwa [pow_one_list Dr] at h

private theorem zero3_eq (r : ListBlank (Fin 2)) : [0, 0, 0] +> r = [0] +> ([0, 0] +> r) :=
    Eq.symm rfl

private theorem zero4_eq (r : ListBlank (Fin 2)) : [0, 0, 0, 0] +> r = [0, 0] +> ([0, 0] +> r) :=
    Eq.symm rfl

private theorem zero2_zero1_eq (r : ListBlank (Fin 2)) :
    [0, 0] +> ([0] +> r) = [0] +> ([0, 0] +> r) := Eq.symm rfl

private theorem append_X_X (r : ListBlank (Fin 2)) : X +> (X +> r) = (X ^ 2) +> r := Eq.symm rfl

private theorem append_Dr_Dr (l : ListBlank (Fin 2)) : Dr +> (Dr +> l) = (Dr ^ 2) +> l :=
    Eq.symm rfl

private theorem pow_one_X_eq : X ^ 1 = X := Eq.symm rfl

private theorem pow_one_Dr_eq : Dr ^ 1 = Dr := Eq.symm rfl

private theorem pow_zero_list_eq {α : Type*} (l : List α) : l ^ (0 : ℕ) = [] := Eq.symm rfl

private theorem append_nil_eq (r : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> r = r := Eq.symm rfl

private def sep : Bool → List (Fin 2)
  | true => [0] ++ Y
  | false => [0, 0]

private theorem sep_true_append (r : ListBlank (Fin 2)) : sep true +> r = [0] +> (Y +> r) :=
    Eq.symm rfl

private theorem sep_false_append (r : ListBlank (Fin 2)) : sep false +> r = [0, 0] +> r :=
    Eq.symm rfl

private theorem zero_Y_append (r : ListBlank (Fin 2)) : ([0] ++ Y) +> r = [0] +> (Y +> r) :=
    Eq.symm rfl

private theorem zero_cons_Y_append (r : ListBlank (Fin 2)) : (0 :: Y) +> r = [0] +> (Y +> r) :=
    Eq.symm rfl

private theorem congr_reachesPlus_left {a a' b : Cfg (Fin 2) (Fin 6)} (ha : a = a') :
    (a [tm40]⊢⁺ b) = (a' [tm40]⊢⁺ b) := by subst ha; rfl

private theorem congr_reachesStar {a a' b b' : Cfg (Fin 2) (Fin 6)} (ha : a = a') (hb : b = b') :
    (a [tm40]⊢* b) = (a' [tm40]⊢* b') := by subst ha hb; rfl

private theorem congr_reachesPlus {a a' b b' : Cfg (Fin 2) (Fin 6)} (ha : a = a') (hb : b = b') :
    (a [tm40]⊢⁺ b) = (a' [tm40]⊢⁺ b') := by subst ha hb; rfl

private theorem congr_sideRLs {gs gs' : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    {r r' s s' : ListBlank (Fin 2)} (hgs : gs = gs') (hr : r = r') (hs : s = s') :
    SideRLs tm40 gs r s = SideRLs tm40 gs' r' s' := by subst hgs hr hs; rfl

private theorem congr_num {b b' : Bool} {n n' : ℕ} {r r' : ListBlank (Fin 2)}
    (hb : b = b') (hn : n = n') (hr : r = r') :
    Num b n r = Num b' n' r' := by subst hb hn hr; rfl

private theorem congr_cutnum {b b' : Bool} {n n' d d' : ℕ} {r r' : ListBlank (Fin 2)}
    (hb : b = b') (hn : n = n') (hd : d = d') (hr : r = r') :
    CutNum b n d r = CutNum b' n' d' r' := by subst hb hn hd hr; rfl

private theorem CutNum_cast {b : Bool} {j d j' d' : ℕ} {r : ListBlank (Fin 2)}
    (hj : j = j') (hd : d = d') (h : CutNum b j d r) : CutNum b j' d' r := by
  subst hj hd; exact h

private theorem CutNum_O_odd {n d1 d2 : ℕ} {r : ListBlank (Fin 2)}
    (ht : Num false n r) (hd : 3 + n = d1 + d2) :
    CutNum true (5 + n * 2) d1 ((X ^ d2) +> ([0] +> (Y +> r))) := by
  unfold CutNum
  rw [append_X_pow, ← hd]
  exact Num.O_odd n r ht

private theorem CutNum_O_even {n d1 d2 : ℕ} {r : ListBlank (Fin 2)}
    (ht : Num false n r) (hd : 3 + n = d1 + d2) :
    CutNum true (4 + n * 2) d1 ((X ^ d2) +> ([0, 0] +> r)) := by
  unfold CutNum
  rw [append_X_pow, ← hd]
  exact Num.O_even n r ht

private theorem CutNum_E_odd {n d1 d2 : ℕ} {r : ListBlank (Fin 2)}
    (ht : Num true n r) (hd : 1 + n = d1 + d2) :
    CutNum false (1 + n * 2) d1 ((X ^ d2) +> ([0] +> (Y +> r))) := by
  unfold CutNum
  rw [append_X_pow, ← hd]
  exact Num.E_odd n r ht

private theorem CutNum_E_even {n d1 d2 : ℕ} {r : ListBlank (Fin 2)}
    (ht : Num true n r) (hd : 1 + n = d1 + d2) :
    CutNum false (n * 2) d1 ((X ^ d2) +> ([0, 0] +> r)) := by
  unfold CutNum
  rw [append_X_pow, ← hd]
  exact Num.E_even n r ht

private theorem Num_of_CutNum {b : Bool} {n1 n2 d1 d2 : ℕ} {r : ListBlank (Fin 2)}
    (hn : n1 = n2) (hd : d1 = d2) (h : CutNum b n1 d1 r) :
    Num b n2 ((X ^ d2) +> r) := by
  subst hn; subst hd; exact h

private theorem congr_root {r r' : ListBlank (Fin 2)} (hr : r = r') :
    root r = root r' := by subst hr; rfl

private theorem congr_pending {n n' : ℕ} {l l' r r' : ListBlank (Fin 2)}
    (hn : n = n') (hl : l = l') (hr : r = r') :
    pending n l r = pending n' l' r' := by subst hn hl hr; rfl

private theorem congr_headLeft {q : Fin 6} {l l' r r' : ListBlank (Fin 2)}
    (hl : l = l') (hr : r = r') :
    (l <{{q}} r) = (l' <{{q}} r') := by subst hl hr; rfl

private theorem congr_headRight {q : Fin 6} {l l' r r' : ListBlank (Fin 2)}
    (hl : l = l') (hr : r = r') :
    (l {{q}}> r) = (l' {{q}}> r') := by subst hl hr; rfl

private theorem congr_append {w w' : List (Fin 2)} {r r' : ListBlank (Fin 2)}
    (hw : w = w') (hr : r = r') :
    w +> r = w' +> r' := by subst hw hr; rfl

private theorem congr_pow {α : Type*} {x : List α} {m n : ℕ} (hmn : m = n) :
    x ^ m = x ^ n :=
  congrArg (HPow.hPow x) hmn

private theorem congr_pow_one_left {α : Type*} {x : List α} {n : ℕ} (hn : 1 = n) :
    x = x ^ n := by subst hn; exact (List.append_nil x).symm

private theorem congr_pow_one_right {α : Type*} {x : List α} {n : ℕ} (hn : n = 1) :
    x ^ n = x := by subst hn; exact List.append_nil x

private abbrev T2r : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1]

private def birth (a b : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (T2r +> ((Dr ^ b) +> ([1, 1] +> ((Dr ^ a) +> ([1] +> default))))) {{B}}> r

private theorem congr_birth {a a' b b' : ℕ} {r r' : ListBlank (Fin 2)}
    (ha : a = a') (hb : b = b') (hr : r = r') :
    birth a b r = birth a' b' r' := by subst ha hb hr; rfl

private abbrev T1r : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1]

private def klj (a b : ℕ) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (T1r +> ((Dr ^ (1 + b)) +> ([1, 0, 0] +> ((Dr ^ a) +> l)))) {{B}}> r

private theorem congr_klj {a a' b b' : ℕ} {l l' r r' : ListBlank (Fin 2)}
    (ha : a = a') (hb : b = b') (hl : l = l') (hr : r = r') :
    klj a b l r = klj a' b' l' r' := by subst ha hb hl hr; rfl

private theorem congr_cutnum_zero_left {b b' : Bool} {n n' : ℕ} {r r' : ListBlank (Fin 2)}
    (hb : b = b') (hn : n = n') (hr : r = r') :
    CutNum b n 0 r = Num b' n' r' := by subst hb hn hr; rfl

private theorem congr_cutnum_zero_right {b b' : Bool} {n n' : ℕ} {r r' : ListBlank (Fin 2)}
    (hb : b = b') (hn : n = n') (hr : r = r') :
    Num b n r = CutNum b' n' 0 r' := by subst hb hn hr; rfl

private theorem congr_and {P P' Q Q' : Prop} (hP : P = P') (hQ : Q = Q') : (P ∧ Q) = (P' ∧ Q') := by
  subst hP hQ; rfl

local macro "eq_omega" : tactic =>
  `(tactic| (
    try simp only
      [zero3_eq, zero4_eq, zero2_zero1_eq, Bool.not_true, Bool.not_false, pow_one_X_eq,
      pow_one_Dr_eq,
      pow_zero_list_eq, append_nil_eq,
      sep_true_append, sep_false_append, zero_Y_append, zero_cons_Y_append,
      cond, List.length_nil, List.length_cons, Nat.pow_succ, Nat.pow_zero,
      List.singleton_append, List.cons_append, List.nil_append, List.append_assoc,
      append_X_pow, append_X_left, append_X_right, append_X_X,
      append_Dr_pow, append_Dr_left, append_Dr_right, append_Dr_Dr]
    repeat' (first
      | with_reducible rfl
      | omega
      | with_reducible apply congr_and
      | with_reducible apply congr_append
      | with_reducible apply congr_pow
      | with_reducible apply congr_pow_one_left
      | with_reducible apply congr_pow_one_right
      | with_reducible apply congr_reachesStar
      | with_reducible apply congr_reachesPlus
      | with_reducible apply congr_sideRLs
      | with_reducible apply congr_num
      | with_reducible apply congr_cutnum
      | with_reducible apply congr_cutnum_zero_left
      | with_reducible apply congr_cutnum_zero_right
      | with_reducible apply congr_root
      | with_reducible apply congr_pending
      | with_reducible apply congr_birth
      | with_reducible apply congr_klj
      | with_reducible apply congr_headLeft
      | with_reducible apply congr_headRight)
    all_goals (try omega)))

private theorem star_trans_eq {a b b' c c' : Cfg (Fin 2) (Fin 6)}
    (h1 : a [tm40]⊢* b) (h2 : b' [tm40]⊢* c)
    (heq : (b [tm40]⊢* c') = (b' [tm40]⊢* c)) :
    a [tm40]⊢* c' :=
  ReachesStar.trans h1 (Eq.mpr heq h2)

private theorem star_plus_eq {a b b' c c' : Cfg (Fin 2) (Fin 6)}
    (h1 : a [tm40]⊢* b) (h2 : b' [tm40]⊢⁺ c)
    (heq : (b [tm40]⊢⁺ c') = (b' [tm40]⊢⁺ c)) :
    a [tm40]⊢* c' :=
  ReachesStar.trans h1 (ReachesPlus.to_star (Eq.mpr heq h2))

private theorem plus_star_trans_eq {a a' b b' c c' : Cfg (Fin 2) (Fin 6)}
    (h1 : a' [tm40]⊢⁺ b) (h2 : b' [tm40]⊢* c)
    (heq : ((a [tm40]⊢⁺ b) ∧ (b [tm40]⊢* c')) = ((a' [tm40]⊢⁺ b) ∧ (b' [tm40]⊢* c))) :
    a [tm40]⊢⁺ c' := by
  have h : (a [tm40]⊢⁺ b) ∧ (b [tm40]⊢* c') := Eq.mpr heq ⟨h1, h2⟩
  exact ReachesPlus.trans_star h.1 h.2

private theorem plus_star_left_eq {a a' b c : Cfg (Fin 2) (Fin 6)}
    (h1 : a' [tm40]⊢⁺ b) (heq : a = a') (h2 : b [tm40]⊢* c) :
    a [tm40]⊢⁺ c :=
  ReachesPlus.trans_star (Eq.mpr (congr_reachesPlus_left heq) h1) h2

private theorem sideRLs_pow_split {ls : List (DH0 (Fin 2) (Fin 6) × DH0 (Fin 2) (Fin 6))}
    (m1 m2 : ℕ) {m : ℕ}
    {r r' : ListBlank (Fin 2)}
    (H : SideRLs tm40 (ls ^ m) r r') (hm : m = m1 + m2) :
    ∃ r1, SideRLs tm40 (ls ^ m1) r r1 ∧ SideRLs tm40 (ls ^ m2) r1 r' := by
  rw [hm, pow_add_list] at H
  exact SideRLs.split H

-- Batch 1 (`Others_v2.v` lines 491–1000)

private theorem F_to_h (r r' : ListBlank (Fin 2)) (H : SideRLs tm40 hf r r') :
    SideRLs tm40 h r (X +> r') := by
  refine SideRLs.single (fun l => ?_)
  have h_run := runSym_plus 100
    { dir := true, q := B, left := lBits [1, 1, 0, 0], right := [], leftIsDefault := false }
    { dir := false, q := A, left := [], right := rBits X, leftIsDefault := false }
    [.callHf] (by decide) (fun _ => 0) l r r' H
  simpa [evalState, toDHCfg] using h_run

private theorem CutNum_h (b : Bool) (n d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b n d r) (hd : d * 2 ≤ 1 + n) :
    ∃ r', CutNum b (1 + n) d r' ∧ SideRLs tm40 h r r' := by
  obtain ⟨s, hn, hr⟩ := CutNum_F b n d r H hd
  refine ⟨X +> s, ?_, F_to_h r s hr⟩
  exact CutNum_prepend b (1 + n) d 1 s (CutNum_cast (by omega) (by omega) hn)

private theorem a2_prepare (q : ℕ) (r r1 : ListBlank (Fin 2))
    (H : SideRLs tm40 h r r1) :
    (root ((X ^ (2 + q)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending q ([1, 1, 0, 1, 1, 1] +> default) r1) := by
  have h_run := runSym_plus 300
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ^ 2 ++ [0, 0])))
    (symPending 0 0 (lBits [1, 1, 0, 1, 1, 1]) true [])
    [.callH] (by decide) (fun _ => q) default r r1 H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem CutNum_hs (m : ℕ) (b : Bool) (n d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b n d r) (hd : d * 2 ≤ 1 + n) :
    ∃ r', CutNum b (n + m) d r' ∧ SideRLs tm40 (h ^ m) r r' := by
  induction m generalizing n r with
  | zero => exact ⟨r, H, SideRLs.nil r⟩
  | succ m ih =>
    obtain ⟨r1, hn, hr⟩ := CutNum_h b n d r H hd
    obtain ⟨r2, hn', hr'⟩ := ih (1 + n) r1 hn (by omega)
    refine ⟨r2, eq_mp_rev hn' (by eq_omega), ?_⟩
    rw [pow_succ_list h]
    exact hr.trans hr'

private theorem F_marker (n : ℕ) (r r2 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 2) r r2) :
    SideRLs tm40 hf ((X ^ n) +> ([0] +> (X +> r))) ((X ^ n) +> ([0] +> (X +> r2))) := by
  refine SideRLs.single (fun l => ?_)
  have h_run := runSym_plus 300
    { dir := true, q := B, left := [], right := rX 0 0 ++ rBits ([0] ++ X), leftIsDefault := false }
    { dir := false, q := A, left := [], right := rX 0 0 ++ rBits ([0] ++ X), leftIsDefault :=
      false }
    (List.replicate 2 .callHf) (by decide) (fun _ => n) l r r2 H
  simpa [evalState, toDHCfg, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem marker_F_cycle (p : ℕ) (r r6 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r r6) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> r)))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (X +> r6)))) := by
  have h_run := runSym_plus 500
    (symRoot (rX 1 0 ++ rBits ([0] ++ X)))
    (symRoot (rX 2 0 ++ rBits ([0] ++ X)))
    (List.replicate 6 .callHf) (by decide) (fun _ => p) default r r6 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem a2_cleanup (r r12 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 12) r r12) :
    (root (X +> ([0, 0, 0] +> (X +> r)))) [tm40]⊢⁺
      (root ((X ^ 2) +> ([0] +> (X +> ([0] +> (X +> r12)))))) := by
  have h_run := runSym_plus 600
    (symRoot (rBits (X ++ [0, 0, 0] ++ X)))
    (symRoot (rBits (X ^ 2 ++ [0] ++ X ++ [0] ++ X)))
    (List.replicate 12 .callHf) (by decide) (fun _ => 0) default r r12 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem F_markers (m n : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 2)) r r') :
    SideRLs tm40 (hf ^ m) ((X ^ n) +> ([0] +> (X +> r))) ((X ^ n) +> ([0] +> (X +> r'))) := by
  induction m generalizing r with
  | zero =>
    cases H
    exact SideRLs.nil _
  | succ m ih =>
    obtain ⟨r2, h2, hs⟩ := sideRLs_pow_split 2 (m * 2) H (by omega)
    rw [pow_succ_list hf]
    exact (F_marker n r r2 h2).trans (ih r2 hs)

private theorem Num_O_odd_inv (k : ℕ) (s : ListBlank (Fin 2)) (H : Num true (5 + k * 2) s) :
    ∃ r, Num false k r ∧ s = (X ^ (3 + k)) +> ([0] +> (Y +> r)) := by
  obtain ⟨r, hr⟩ := Num_ex false k
  exact ⟨r, hr, Num_unique H (Num.O_odd k r hr)⟩

private theorem normal_calls (n : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (3 + n * 3)) r r') :
    (root ((X ^ (2 + n)) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root (X +> ([0] +> (X +> r')))) := by
  induction n generalizing r with
  | zero => exact normal_end r r' H
  | succ n ih =>
    obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (3 + n * 3) H (by omega)
    exact ReachesPlus.trans (eq_mp_rev (normal_cycle n r r3 h3) (by eq_omega)) (ih r3 hs)

private def markers : List ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | n :: ns, r => (X ^ n) +> ([0] +> (X +> markers ns r))

private theorem F_columns (ns : List ℕ) (m : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 2 ^ ns.length)) r r') :
    SideRLs tm40 (hf ^ m) (markers ns r) (markers ns r') := by
  induction ns generalizing m with
  | nil =>
    dsimp only [markers]
    simpa using H
  | cons n ns ih =>
    dsimp only [markers]
    apply F_markers
    apply ih
    have h_exp : m * 2 * 2 ^ ns.length = m * 2 ^ (ns.length + 1) := by ring
    rwa [h_exp]

private theorem h_columns (ns : List ℕ) (m a : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 2 ^ (1 + ns.length))) r r') :
    SideRLs tm40 (h ^ m) (markers (a :: ns) r) (markers ((a + m) :: ns) r') := by
  induction m generalizing a r with
  | zero =>
    simp only [Nat.zero_mul, pow_zero_list] at H
    cases H
    simpa [markers] using SideRLs.nil (markers (a :: ns) r')
  | succ m ih =>
    obtain ⟨r1, h1, hs⟩ :=
      sideRLs_pow_split (2 ^ (1 + ns.length)) (m * 2 ^ (1 + ns.length)) H (by ring)
    have hr : SideRLs tm40 h (markers (a :: ns) r) (markers ((1 + a) :: ns) r1) := by
      have hf1 : SideRLs tm40 (hf ^ 1) (markers (a :: ns) r) (markers (a :: ns) r1) := by
        apply F_columns (a :: ns) 1 r r1
        simpa [Nat.add_comm] using h1
      have h_eq1 : X +> markers (a :: ns) r1 = markers ((1 + a) :: ns) r1 := by
        dsimp only [markers]
        exact append_X_left a ([0] +> (X +> markers ns r1))
      rw [← h_eq1]
      exact F_to_h (markers (a :: ns) r) (markers (a :: ns) r1) hf1
    rw [pow_succ_list h]
    have h_ih := ih (1 + a) r1 hs
    have h_eq2 : markers ((1 + a + m) :: ns) r' = markers ((a + (m + 1)) :: ns) r' := by
      congr 2
      omega
    rw [h_eq2] at h_ih
    exact hr.trans h_ih

private theorem digit_odd_all_0 : SegRLs tm40 h h ([0] ++ Y) (X ++ [0, 0]) :=
  BoundedConfig.segRLs_c_spec tm40 (T := 25) (by decide)

private theorem digit_odd_all (n : ℕ) :
    SegRLs tm40 h h (X ^ n ++ [0] ++ Y) (X ^ (1 + n) ++ [0, 0]) := by
  have h1 : X ^ n ++ [0] ++ Y = X ^ n ++ ([0] ++ Y) := by rw [List.append_assoc]
  have h2 : X ^ (1 + n) ++ [0, 0] = X ^ n ++ (X ++ [0, 0]) := by
    rw [Nat.add_comm 1 n, pow_succ_list', List.append_assoc]
  rw [h1, h2]
  exact (steps_X n).concat digit_odd_all_0

private theorem digit_odd_all_side (n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    SideRLs tm40 h ((X ^ n) +> ([0] +> (Y +> r))) ((X ^ (1 + n)) +> ([0, 0] +> s)) := by
  have h_seg := (digit_odd_all n).sideRLs_concat H
  rwa [List.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc]
    at h_seg

private theorem F_pair (n : ℕ) (e : Bool) :
    SegRLs tm40 (hf ^ 2) h (X ^ (1 + n) ++ sep e) (X ^ n ++ sep e) := by
  cases e
  · dsimp only [sep]
    exact (F_even n).trans (F_odd n)
  · change SegRLs tm40 (hf ++ hf) (h ++ []) (X ^ (1 + n) ++ ([0] ++ Y)) (X ^ n ++ ([0] ++ Y))
    simpa only [List.append_assoc] using (F_odd (1 + n)).trans (F_even n)

private theorem F_pairs (m n : ℕ) (e : Bool) :
    SegRLs tm40 (hf ^ (m * 2)) (h ^ m) (X ^ (n + m) ++ sep e) (X ^ n ++ sep e) := by
  induction m with
  | zero => exact SegRLs.nil _
  | succ m ih =>
    have h_pow : hf ^ ((m + 1) * 2) = hf ^ 2 ++ hf ^ (m * 2) := by
      rw [← pow_add_list]
      congr 1
      omega
    rw [h_pow, pow_succ_list h]
    have hp : SegRLs tm40 (hf ^ 2) h (X ^ (n + (m + 1)) ++ sep e) (X ^ (n + m) ++ sep e) := by
      have h_exp : n + (m + 1) = 1 + (n + m) := by omega
      rw [h_exp]
      exact F_pair (n + m) e
    exact hp.trans ih

private theorem F_pairs_odd_side (m n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (hf ^ (m * 2)) ((X ^ (n + m)) +> ([0] +> (Y +> r)))
      ((X ^ n) +> ([0] +> (Y +> s))) := by
  have h_seg := (F_pairs m n true).sideRLs_concat H
  simp only [sep, ListBlank.append_assoc] at h_seg
  exact h_seg

private theorem h_pair_odd (n : ℕ) :
    SegRLs tm40 (h ^ 2) h (X ^ n ++ [0] ++ Y) (X ^ (1 + n) ++ [0] ++ Y) :=
  (digit_odd_all n).trans (digit_even n)

private theorem h_pairs_odd (m n : ℕ) :
    SegRLs tm40 (h ^ (m * 2)) (h ^ m) (X ^ n ++ [0] ++ Y) (X ^ (n + m) ++ [0] ++ Y) := by
  induction m generalizing n with
  | zero => exact SegRLs.nil _
  | succ m ih =>
    have h_pow : h ^ ((m + 1) * 2) = h ^ 2 ++ h ^ (m * 2) := by
      rw [← pow_add_list]
      congr 1
      omega
    rw [h_pow, pow_succ_list h]
    have h_ih := ih (1 + n)
    have h_exp : 1 + n + m = n + (m + 1) := by omega
    rw [h_exp] at h_ih
    exact (h_pair_odd n).trans h_ih

private theorem h_pairs_odd_side (m n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (h ^ (m * 2)) ((X ^ n) +> ([0] +> (Y +> r)))
      ((X ^ (n + m)) +> ([0] +> (Y +> s))) := by
  have h_seg := (h_pairs_odd m n).sideRLs_concat H
  rwa [List.append_assoc, List.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc,
       ListBlank.append_assoc, ListBlank.append_assoc] at h_seg

private theorem marker_calls (m p : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 6)) r r') :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> r)))) [tm40]⊢*
      (root ((X ^ (1 + p + m)) +> ([0] +> (X +> r')))) := by
  induction m generalizing p r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ m ih =>
    obtain ⟨r6, h6, hs⟩ := sideRLs_pow_split 6 (m * 6) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (marker_F_cycle p r r6 h6)
      (eq_mp_rev (ih (1 + p) r6 hs) (by eq_omega)))

set_option maxRecDepth 100000 in
private theorem pending_digit_pair (n a : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (pending (2 + n) l ((X ^ (2 + a)) +> ([0, 0] +> r))) [tm40]⊢⁺
      (pending n l ((X ^ (1 + a)) +> ([0, 0] +> s))) := by
  have h_run := runSym_plus 400
    (symPending 2 0 [] false (rX 2 1 ++ rBits [0, 0]))
    (symPending 0 0 [] false (rX 1 1 ++ rBits [0, 0]))
    (List.replicate 3 .callH) (by decide) (fun i => if i = 0 then n else a) l r s H
  simpa [evalState, symPending, pending, ListBlank.append_assoc] using h_run

private theorem pending_digit_pairs (k n a : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (k * 3)) r s) :
    (pending (n + k * 2) l ((X ^ (2 + a + k)) +> ([0, 0] +> r))) [tm40]⊢*
      (pending n l ((X ^ (2 + a)) +> ([0, 0] +> s))) := by
  induction k generalizing r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ k ih =>
    obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (k * 3) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (pending_digit_pair (n + k * 2) (1 + a + k) l r r3 h3) (by eq_omega))
      (eq_mp_rev (ih r3 hs) (by eq_omega)))

private theorem pending_digit_end (a : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (pending 0 l ((X ^ (2 + a)) +> ([0, 0] +> r))) [tm40]⊢⁺
      (l <{{F}} ([1, 0] +> (Y +> ((X ^ (1 + a)) +> ([0] +> (Y +> s)))))) := by
  have h_run := runSym_plus 400
    (symPendingConst 0 [] false (rX 2 0 ++ rBits [0, 0]))
    { dir := false, q := F, left := [], right :=
      rBits ([1, 0] ++ Y) ++ (rX 1 0 ++ rBits ([0] ++ Y)), leftIsDefault := false }
    [.callH] (by decide) (fun _ => a) l r s H
  simpa [evalState, symPendingConst, pending, ListBlank.append_assoc] using h_run

private theorem a1_prepare (q : ℕ) (r : ListBlank (Fin 2)) :
    (root ((X ^ (1 + q)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending q ([1] +> default) r) := by
  have h_run := runSym_plus 300
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ++ [0, 0])))
    (symPending 0 0 (lBits [1]) true [])
    [] (by decide) (fun _ => q) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem a1_digit_finish (a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (([1] +> default) <{{F}} ([1, 0] +> (Y +> ((X ^ (1 + a)) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (3 + a)) +> ([0, 0] +> s))))) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits [1], right :=
      rBits ([1, 0] ++ Y) ++ (rX 1 0 ++ rBits ([0] ++ Y)), leftIsDefault := true }
    (symRoot (rBits (X ++ [0]) ++ (rX 3 0 ++ rBits [0, 0])))
    [.callH] (by decide) (fun _ => a) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private def symBirth (ka ida kb idb : ℕ) (r : List RAtom) : SymState :=
  { dir := true, q := B,
    left := lBits T2r ++ (lDr kb idb ++ (lBits [1, 1] ++ (lDr ka ida ++ lBits [1]))),
    right := r, leftIsDefault := true }

private def symBirthConstA (ka kb idb : ℕ) (r : List RAtom) : SymState :=
  { dir := true, q := B,
    left := lBits T2r ++ (lDr kb idb ++ lBits ([1, 1] ++ Dr ^ ka ++ [1])),
    right := r, leftIsDefault := true }

set_option maxRecDepth 100000 in
private theorem birth_prepare (p : ℕ) (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r r3) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (birth (1 + p) 1 r3) := by
  have h_run := runSym_plus 350
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ Y)))
    { dir := true, q := B, left := lBits (T2r ++ Dr ++ [1, 1]) ++ (lDr 1 0 ++ lBits [1]), right :=
      [], leftIsDefault := true }
    (List.replicate 3 .callHf) (by decide) (fun _ => p) default r r3 H
  simpa [evalState, symRoot, root, birth, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem birth_cycle (a b : ℕ) (r r6 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r r6) :
    (birth (2 + a) (1 + b) r) [tm40]⊢⁺ (birth (1 + a) (4 + b) r6) := by
  have h_run := runSym_plus 600
    (symBirth 2 0 1 1 [])
    (symBirth 1 0 4 1 [])
    (List.replicate 6 .callHf) (by decide) (fun i => if i = 0 then a else b) default r r6 H
  simpa [evalState, symBirth, birth, ListBlank.append_assoc] using h_run

private theorem birth_cycles (k a b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (k * 6)) r s) :
    (birth (1 + a + k) (1 + b) r) [tm40]⊢* (birth (1 + a) (1 + b + k * 3) s) := by
  induction k generalizing b r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ k ih =>
    obtain ⟨r6, h6, hs⟩ := sideRLs_pow_split 6 (k * 6) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (birth_cycle (a + k) b r r6 h6) (by eq_omega))
      (eq_mp_rev (ih (3 + b) r6 hs) (by eq_omega)))

set_option maxRecDepth 100000 in
private theorem birth_end (b : ℕ) (r r2 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 2) r r2) :
    (birth 1 (1 + b) r) [tm40]⊢⁺
      ((T2r +> ((Dr ^ (3 + b)) +> ([1, 1, 1] +> default))) {{B}}> r2) := by
  have h_run := runSym_plus 250
    (symBirthConstA 1 1 0 [])
    { dir := true, q := B, left := lBits T2r ++ (lDr 3 0 ++ lBits [1, 1, 1]), right :=
      [], leftIsDefault := true }
    (List.replicate 2 .callHf) (by decide) (fun _ => b) default r r2 H
  simpa [evalState, symBirthConstA, birth, ListBlank.append_assoc] using h_run

private theorem marker_hcalls (m p a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (m * 3)) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + a + m * 3)) +> ([0, 0] +> r))))) [tm40]⊢*
      (root ((X ^ (1 + p + m)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> s))))) := by
  induction m generalizing p r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ m ih =>
    obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (m * 3) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (marker_cycle p (a + m * 3) r r3 h3) (by eq_omega))
      (eq_mp_rev (ih (1 + p) r3 hs) (by eq_omega)))

private abbrev Lr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0]

private abbrev Jr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0]

private abbrev Kr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0]

private theorem odd_zero_return (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (X +> ([0, 0] +> s))))) := by
  have h_run := runSym_plus 200
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y ++ [0, 0])))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ X ++ [0, 0])))
    [.callH] (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem zero4_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ((X ^ (3 + p)) +> ([0, 0, 0, 0] +> r))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (X +> ([0] +> (Y +> s)))))) := by
  have h_run := runSym_plus 350
    (symRoot (rX 3 0 ++ rBits [0, 0, 0, 0]))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ X ++ [0] ++ Y)))
    [.callH] (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private abbrev Wr : List (Fin 2) := [1, 1, 0, 1, 1, 1, 1, 0, 0, 1]

private def outer_left (p a b : ℕ) : ListBlank (Fin 2) :=
  (Dr ^ (2 + b)) +> ([1, 1, 0, 0, 1, 1] +>
    ((Dr ^ (1 + a)) +> ([1, 1, 0, 1, 1] +>
      ((Dr ^ p) +> ([1, 1, 0, 1, 1, 1] +> default)))))

private def symOuterLeft (kp idp ka ida kb idb : ℕ) : List LAtom :=
  lDr kb idb ++ (lBits [1, 1, 0, 0, 1, 1] ++
    (lDr ka ida ++ (lBits [1, 1, 0, 1, 1] ++
      (lDr kp idp ++ lBits [1, 1, 0, 1, 1, 1]))))

private theorem F_pairs_side (m n : ℕ) (e : Bool) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (hf ^ (m * 2)) ((X ^ (n + m)) +> (sep e +> r)) ((X ^ n) +> (sep e +> s)) := by
  have h_seg := (F_pairs m n e).sideRLs_concat H
  rwa [ListBlank.append_assoc, ListBlank.append_assoc] at h_seg

private theorem marked11011_finish (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (([1, 1, 0, 1, 1] +> l) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (l <{{A}} ([0, 0, 0, 0] +> ((X ^ 2) +> s))) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits [1, 1, 0, 1, 1], right :=
      rBits ([1, 0] ++ Y), leftIsDefault := false }
    { dir := false, q := A, left := [], right := rBits ([0, 0, 0, 0] ++ X ^ 2), leftIsDefault :=
      false }
    (List.replicate 3 .callHf) (by decide) (fun _ => 0) l r s H
  simpa [evalState, ListBlank.append_assoc] using h_run

local macro "cond_omega" : tactic => `(tactic| ((try dsimp only [cond, sep]); (try omega)))

private theorem Num_digit_split (b e : Bool) (k : ℕ) (r : ListBlank (Fin 2))
    (H : Num b (cond b 4 0 + cond e 1 0 + k * 2) r) :
    ∃ s, Num (!b) k s ∧ r = (X ^ (cond b 3 1 + k)) +> (sep e +> s) := by
  cases b <;> cases e
  · exact Num_E_even_inv k r (eq_mp_rev H (by eq_omega))
  · obtain ⟨s, hs, hr⟩ := Num_E_odd_inv k r (eq_mp_rev H (by eq_omega))
    exact ⟨s, hs, eq_mp_rev hr (by dsimp only [sep]; eq_omega)⟩
  · exact Num_O_even_inv k r (eq_mp_rev H (by eq_omega))
  · obtain ⟨s, hs, hr⟩ := Num_O_odd_inv k r (eq_mp_rev H (by eq_omega))
    exact ⟨s, hs, eq_mp_rev hr (by dsimp only [sep]; eq_omega)⟩

private theorem CutNum_digit_tail (b e : Bool) (j k d a : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hj : j = cond b 4 0 + cond e 1 0 + k * 2)
    (ha : d + a = cond b 3 1 + k) :
    ∃ s, Num (!b) k s ∧ r = (X ^ a) +> (sep e +> s) := by
  rw [hj] at hn
  obtain ⟨s, hs, et⟩ := Num_digit_split b e k _ hn
  refine ⟨s, hs, ?_⟩
  rw [cut_prefix (cond b 3 1 + k) d r (sep e +> s) (by dsimp only [cond] at ha ⊢; omega) et]
  have h_sub : cond b 3 1 + k - d = a := by dsimp only [cond] at ha ⊢; omega
  rw [h_sub]

private theorem leading_zero4 (p : ℕ) (r : ListBlank (Fin 2)) :
    (root ([0] +> ((X ^ (2 + p)) +> ([0, 0, 0, 0] +> r)))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0, 0] +> (Y +> r)))) := by
  have h_run := runSym_plus 300
    (symRoot (rBits [0] ++ rX 2 0 ++ rBits [0, 0, 0, 0]))
    (symRoot (rX 2 0 ++ rBits ([0, 0, 0] ++ Y)))
    [] (by decide) (fun _ => p) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private def symKlj (ka ida kb idb : ℕ) (l : List LAtom) (leftDef : Bool) (r : List RAtom) :
    SymState :=
  { dir := true, q := B,
    left := lBits T1r ++ (lDr kb idb ++ (lBits [1, 0, 0] ++ (lDr ka ida ++ l))),
    right := r, leftIsDefault := leftDef }

private def symKljConstA (ka kb idb : ℕ) (l : List LAtom) (leftDef : Bool) (r : List RAtom) :
    SymState :=
  { dir := true, q := B,
    left := lBits T1r ++ (lDr kb idb ++ lBits ([1, 0, 0] ++ Dr ^ ka) ++ l),
    right := r, leftIsDefault := leftDef }

set_option maxRecDepth 100000 in
private theorem klj_cycle (a b : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (klj (1 + a) b l r) [tm40]⊢⁺ (klj a (1 + b) l s) := by
  have h_run := runSym_plus 600
    (symKlj 1 0 1 1 [] false [])
    (symKlj 0 0 2 1 [] false [])
    (List.replicate 6 .callHf) (by decide) (fun i => if i = 0 then a else b) l r s H
  have h_step : (klj (1 + a) b l r) [tm40]⊢⁺
      ((T1r +> ((Dr ^ (2 + b)) +> ([1, 0, 0] +> ((Dr ^ a) +> l)))) {{B}}> s) := by
    simpa [evalState, symKlj, klj, ListBlank.append_assoc] using h_run
  have h_eq : (2 + b : ℕ) = 1 + (1 + b) := by omega
  simpa [klj, h_eq] using h_step

private theorem klj_cycles (m a b : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 6)) r s) :
    (klj (a + m) b l r) [tm40]⊢* (klj a (b + m) l s) := by
  induction m generalizing b r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ m ih =>
    obtain ⟨r6, h6, hs⟩ := sideRLs_pow_split 6 (m * 6) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (klj_cycle (a + m) b l r r6 h6) (by eq_omega))
      (eq_mp_rev (ih (1 + b) r6 hs) (by eq_omega)))

private abbrev CEr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1]

private abbrev EBr : List (Fin 2) := [1, 1, 1, 1, 0, 1, 1, 1]

private abbrev ZYr : List (Fin 2) := [1, 1, 0, 0, 1, 1, 1]

private theorem zeroY00_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (X +> ([0, 0] +> s))))) :=
  odd_zero_return p r s H

private theorem CutNum_takeX (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 ≤ j) :
    ∃ s, r = X +> s ∧ CutNum chi j (d + 1) s := by
  obtain ⟨s, hr⟩ : ∃ s, r = X +> s := by
    have h_nv := Num_view HN
    generalize hs : (X ^ d) +> r = z at h_nv
    cases h_nv with
    | NV_even k r0 _ =>
      refine ⟨(X ^ (k - d)) +> ([0, 0] +> r0), ?_⟩
      rw [cut_prefix (1 + k) d r ([0, 0] +> r0) (by omega) hs, append_X_left]
      congr 2; omega
    | NV_odd k r0 _ _ _ =>
      refine ⟨(X ^ (k - d)) +> ([0] +> (Y +> r0)), ?_⟩
      rw [cut_prefix (1 + k) d r ([0] +> (Y +> r0)) (by omega) hs, append_X_left]
      congr 2; omega
  refine ⟨s, hr, ?_⟩
  unfold CutNum at HN ⊢
  exact eq_mp_rev HN (by rw [hr]; eq_omega)

private theorem two_marker_cycle (p : ℕ) (r r12 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 12) r r12) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> (X +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> (X +> r12)))))) :=
  marker_F_cycle p ([0] +> (X +> r)) ([0] +> (X +> r12)) (F_markers 6 0 r r12 H)

private theorem two_markers (m p : ℕ) (r r' : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (m * 12)) r r') :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> (X +> r)))))) [tm40]⊢*
      (root ((X ^ (1 + p + m)) +> ([0] +> (X +> ([0] +> (X +> r')))))) := by
  induction m generalizing p r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ m ih =>
    obtain ⟨r12, h12, hs⟩ := sideRLs_pow_split 12 (m * 12) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (two_marker_cycle p r r12 h12)
      (eq_mp_rev (ih (1 + p) r12 hs) (by eq_omega)))

private theorem c1_prepare (p : ℕ) (r r1 : ListBlank (Fin 2))
    (H : SideRLs tm40 h r r1) :
    (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> (X +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root ([0] +> ((X ^ (2 + p)) +> ([0, 0] +> (Y +> (Y +> r1)))))) := by
  have h_run := runSym_plus 400
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ++ [0] ++ X ++ [0] ++ Y)))
    (symRoot (rBits [0] ++ (rX 2 0 ++ rBits ([0, 0] ++ Y ++ Y))))
    [.callH] (by decide) (fun _ => p) default r r1 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem c1_finish (p : ℕ) (r r4 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r r4) :
    (root ([0] +> ((X ^ (2 + p)) +> ([0, 0] +> (Y +> (Y +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (X +> ([0] +> (X +> ([0] +> (X +> r4)))))))) := by
  have h_run := runSym_plus 400
    (symRoot (rBits [0] ++ (rX 2 0 ++ rBits ([0, 0] ++ Y ++ Y))))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ X ++ [0] ++ X ++ [0] ++ X)))
    (List.replicate 4 .callHf) (by decide) (fun _ => p) default r r4 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_c1 (p : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b j d r) (hj : d * 2 + 1 ≤ j) :
    ∃ r', CutNum b (j + 5) (d + 3) r' ∧
      ((root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> (X +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0, 0] +> (X +> ([0] +> (X +> ([0] +> r')))))))) := by
  obtain ⟨r1, hn, hr⟩ := CutNum_h b j d r H (by omega)
  obtain ⟨r4, hn', hr'⟩ := CutNum_Fs 4 b (1 + j) d r1 hn (by omega)
  refine ⟨X +> r4, ?_, ReachesPlus.trans (c1_prepare p r r1 hr) (c1_finish p r1 r4 hr')⟩
  exact CutNum_prepend b (j + 5) (d + 3) 1 r4 (CutNum_cast (by omega) (by omega) hn')

set_option maxRecDepth 100000 in
private theorem two_odd6 (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 6) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 6) +> ([0] +> (Y +> r))))))))
      [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0, 0] +> (Y +> s)))))) := by
  have h_run := runSym_plus 850
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0] ++ X ^ 6 ++ [0] ++ Y)))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0, 0] ++ Y)))))
    (List.replicate 6 .callH) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem Num_a2_cleanup (a : ℕ) (e b : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (hn : Num b j r) :
    ∃ s, Num b (j + 6) s ∧
      ((root (X +> ([0, 0, 0] +> ((X ^ (7 + a)) +> (sep e +> r))))) [tm40]⊢⁺
        (root ((X ^ 2) +> ([0] +> (X +> ([0] +> ((X ^ (1 + a)) +> (sep e +> s)))))))) := by
  obtain ⟨s, hs, hh⟩ := Num_add 6 b j r hn
  have hf : SideRLs tm40 (hf ^ 12) ((X ^ (6 + a)) +> (sep e +> r)) ((X ^ a) +> (sep e +> s)) :=
    eq_mp_rev (F_pairs_side 6 a e r s hh) (by eq_omega)
  exact ⟨s, hs, eq_mp_rev (a2_cleanup _ _ hf) (by eq_omega)⟩

private theorem critical_E_prepare (a : ℕ) (r : ListBlank (Fin 2)) :
    (root ([0] +> ((X ^ 2) +> ([0] +> (Y +> ((X ^ (1 + a)) +> ([0] +> (X +> ([0, 0] +> r)))))))))
      [tm40]⊢⁺
      (pending a (CEr +> default) r) := by
  have h_run := runSym_plus 300
    (symRoot (rBits ([0] ++ X ^ 2 ++ [0] ++ Y) ++ rX 1 0 ++ rBits ([0] ++ X ++ [0, 0])))
    (symPending 0 0 (lBits CEr) true [])
    [] (by decide) (fun _ => a) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem C2_odd_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 8) r s) :
    (root ((X ^ (3 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (klj p 2 ([1, 1, 0, 1, 1, 1] +> default) s) := by
  have h_run := runSym_plus 600
    (symRoot (rX 3 0 ++ (rBits ([0] ++ X ++ [0] ++ X ^ 2 ++ [0] ++ Y))))
    { dir := true, q := B, left :=
      lBits (T1r ++ Dr ^ 3 ++ [1, 0, 0]) ++ (lDr 0 0 ++ lBits [1, 1, 0, 1, 1, 1]), right :=
      [], leftIsDefault := true }
    (List.replicate 8 .callHf) (by decide)
    (fun _ => p) default r s H
  simpa [evalState, symRoot, root, klj, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem klj_zero_left (b : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (klj 0 b ([1, 1] +> l) r) [tm40]⊢⁺
      ((T1r +> ((Dr ^ (2 + b)) +> ([1] +> l))) {{B}}> s) := by
  have h_run := runSym_plus 600
    (symKljConstA 0 1 0 (lBits [1, 1]) false [])
    { dir := true, q := B, left := lBits T1r ++ (lDr 2 0 ++ lBits [1]), right :=
      [], leftIsDefault := false }
    (List.replicate 6 .callHf) (by decide)
    (fun _ => b) l r s H
  simpa [evalState, symKljConstA, klj, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem C2_odd_finish (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    ((T1r +> ((Dr ^ (1 + b)) +> ([1, 0, 1, 1, 1] +> default))) {{B}}> r) [tm40]⊢⁺
      (root (X +> ([0, 0, 0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 3) +> s)))))) := by
  have h_run := runSym_plus 500
    { dir := true, q := B, left := lBits T1r ++ (lDr 1 0 ++ lBits [1, 0, 1, 1, 1]), right :=
      [], leftIsDefault := true }
    (symRoot (rBits (X ++ [0, 0, 0]) ++ (rX 1 0 ++ rBits ([0] ++ X ^ 3))))
    (List.replicate 6 .callHf) (by decide)
    (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem C2_odd_calls (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (20 + p * 6)) r s) :
    (root ((X ^ (3 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root (X +> ([0, 0, 0] +> ((X ^ (4 + p)) +> ([0] +> ((X ^ 3) +> s)))))) := by
  obtain ⟨r8, H8, Hs⟩ := sideRLs_pow_split 8 (p * 6 + 12) H (by omega)
  obtain ⟨rm, Hm, He⟩ := sideRLs_pow_split (p * 6) 12 Hs (by omega)
  obtain ⟨r6, H6, Hf⟩ := sideRLs_pow_split 6 6 He (by omega)
  refine ReachesPlus.trans (C2_odd_prepare p r r8 H8) ?_
  have h_l1 :
    ([1, 1, 0, 1, 1, 1] +> default : ListBlank (Fin 2)) = [1, 1] +> ([0, 1, 1, 1] +> default) := by
    rw [← ListBlank.append_assoc]; rfl
  have h_l2 :
    ([1] +> ([0, 1, 1, 1] +> default) : ListBlank (Fin 2)) = [1, 0, 1, 1, 1] +> default := by
    rw [← ListBlank.append_assoc]; rfl
  rw [h_l1]
  refine stepStar_stepPlus_trans
    (eq_mp_rev (klj_cycles p 0 2 ([1, 1] +> ([0, 1, 1, 1] +> default)) r8 rm Hm) (by eq_omega)) ?_
  have h_zl := klj_zero_left (2 + p) ([0, 1, 1, 1] +> default) rm r6 H6
  rw [h_l2] at h_zl
  exact ReachesPlus.trans (eq_mp_rev h_zl (by eq_omega))
    (eq_mp_rev (C2_odd_finish (3 + p) r6 s Hf) (by eq_omega))

private theorem CutNum_C2_odd (p : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 18 + p * 6 ≤ j) :
    ∃ s, CutNum chi (j + 20 + p * 6) (d + 17 + p * 6) s ∧
      ((root ((X ^ (3 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
        (root (X +> ([0, 0, 0] +> ((X ^ (4 + p)) +> ([0] +> s)))))) := by
  obtain ⟨t, HT, HF⟩ := CutNum_Fs (20 + p * 6) chi j d r HN (by omega)
  refine ⟨(X ^ 3) +> t, ?_, C2_odd_calls p r t HF⟩
  exact CutNum_prepend chi (j + 20 + p * 6) (d + 17 + p * 6) 3 t
    (CutNum_cast (by omega) (by omega) HT)

private theorem C2_post_calls (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 24) r s) :
    (root (X +> ([0, 0, 0] +> ((X ^ (1 + b)) +> ([0] +> (X +> r)))))) [tm40]⊢⁺
      (root ((X ^ 2) +> ([0] +> (X +> ([0] +> ((X ^ (1 + b)) +> ([0] +> (X +> s)))))))) := by
  exact eq_mp_rev (a2_cleanup _ _ (F_markers 12 b r s H)) (by eq_omega)

private theorem CutNum_C2_post (b : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 24 ≤ j) :
    ∃ s, CutNum chi (j + 24) (d + 24) s ∧
      ((root (X +> ([0, 0, 0] +> ((X ^ (1 + b)) +> ([0] +> r))))) [tm40]⊢⁺
        (root ((X ^ 2) +> ([0] +> (X +> ([0] +> ((X ^ (1 + b)) +> ([0] +> s)))))))) := by
  obtain ⟨t, E, HT⟩ := CutNum_takeX chi j d r HN (by omega)
  obtain ⟨u, HU, HF⟩ := CutNum_Fs 24 chi j (d + 1) t HT (by omega)
  refine ⟨X +> u, ?_, ?_⟩
  · exact CutNum_prepend chi (j + 24) (d + 24) 1 u (CutNum_cast (by omega) (by omega) HU)
  · rw [E]
    exact C2_post_calls b t u HF

set_option maxHeartbeats 2000000 in
-- Symbolic execution via runSym_plus requires additional heartbeats.
set_option maxRecDepth 100000 in
private theorem C_even6_calls (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 9) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (10 + p)) +> s)) := by
  have h_run := runSym_plus 1200
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 6 ++ [0, 0])))
    (symRoot (rX 10 0))
    (List.replicate 9 .callHf) (by decide)
    (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem odd_five_general (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 5) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))))
      [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ b) +> ([0] +> (Y +> (Y +> s))))))) := by
  have h_run := runSym_plus 700
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0] ++ X ^ 5 ++ [0] ++ Y)))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 0 1 ++ rBits ([0] ++ Y ++ Y)))))
    (List.replicate 5 .callH) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem odd_five (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 5) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (Y +> (Y +> s))))) :=
  odd_five_general p 0 r s H

set_option maxRecDepth 100000 in
private theorem marked_K_root (q : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    ((Kr +> ((Dr ^ q) +> ([1, 1] +> default))) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ (1 + q)) +> ([0] +> (Y +> ((X ^ 3) +> s))))) := by
  have h_run := runSym_plus 350
    { dir := false, q := F, left := lBits Kr ++ (lDr 0 0 ++ lBits [1, 1]), right :=
      rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rX 1 0 ++ rBits ([0] ++ Y ++ X ^ 3)))
    (List.replicate 6 .callHf) (by decide) (fun _ => q) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem nested_even4_prepare (p a b c : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (3 + a)) +> ([0] +> (Y +>
      ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + c)) +> ([0] +> ((X ^ 4) +> ([0, 0] +> r))))))))))))
        [tm40]⊢⁺
      (pending c ([1] +> outer_left p a b) s) := by
  have h_run := runSym_plus 600
    (symRoot
      (rX 1 0 ++
      (rBits [0] ++
      (rX 3 1 ++
      (rBits ([0] ++ Y) ++
      (rX 1 2 ++ (rBits [0] ++ (rX 1 3 ++ rBits ([0] ++ X ^ 4 ++ [0, 0])))))))))
    (symPending 0 3 (lBits [1] ++ symOuterLeft 0 0 1 1 2 2) true [])
    (List.replicate 3 .callH) (by decide)
    (fun i => if i = 0 then p else if i = 1 then a else if i = 2 then b else c) default r s H
  simpa [evalState, symRoot, symPending, symOuterLeft, root, pending, outer_left,
    ListBlank.append_assoc] using h_run

private theorem CutNum_zero4_odd (q : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 ≤ 1 + j) :
    ∃ s, CutNum b (j + 6 + q * 6) d s ∧
      ((root ((X ^ (3 + q * 2)) +> ([0, 0, 0, 0] +> r))) [tm40]⊢⁺
        (root ((X ^ (2 + q)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, h1⟩ := CutNum_hs 1 b j d r hn hd
  obtain ⟨r2, hn2, h2⟩ := CutNum_hs (1 + q * 3) b (j + 1) d r1 hn1 (by omega)
  have hh : SideRLs tm40 (h ^ (2 + q * 6))
      (X +> ([0] +> (Y +> r1))) ((X ^ (2 + q * 3)) +> ([0] +> (Y +> r2))) :=
    eq_mp_rev (h_pairs_odd_side (1 + q * 3) 1 r1 r2 h2) (by eq_omega)
  obtain ⟨r3, hn3, h3⟩ := CutNum_hs 1 b (j + 1 + (1 + q * 3)) d r2 hn2 (by omega)
  have hh3 : SideRLs tm40 (h ^ (3 + q * 6))
      (X +> ([0] +> (Y +> r1))) ((X ^ (3 + q * 3)) +> ([0, 0] +> r3)) := by
    have h_split : 3 + q * 6 = (2 + q * 6) + 1 := by omega
    rw [h_split, pow_add_list]
    refine hh.trans ?_
    exact eq_mp_rev (digit_odd_all_side (2 + q * 3) r2 r3 h3) (by eq_omega)
  obtain ⟨s, hs, h4⟩ := CutNum_hs (3 + q * 3) b (j + 1 + (1 + q * 3) + 1) d r3 hn3 (by omega)
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (zero4_prepare (q * 2) r r1 h1) (by eq_omega)) ?_
  refine ReachesPlus.trans_star
    (eq_mp_rev (normal_calls (q * 2) _ _ (eq_mp_rev hh3 (by eq_omega))) (by eq_omega)) ?_
  exact eq_mp_rev (marker_hcalls (1 + q) 0 0 _ _ (eq_mp_rev h4 (by eq_omega))) (by eq_omega)

set_option maxRecDepth 100000 in
private theorem two_even4 (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 8) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 4) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (9 + p)) +> s)) := by
  have h_run := runSym_plus 800
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 4 ++ [0, 0])))
    (symRoot (rX 9 0))
    (List.replicate 8 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem zero_X_even2 (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ([0] +> (X +> ([0, 0] +> ((X ^ b) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0, 0] +> s))))))) := by
  have h_run := runSym_plus 500
    (symRoot (rBits ([0] ++ X ++ [0, 0]) ++ (rX 0 0 ++ rBits ([0] ++ X ^ 2 ++ [0, 0]))))
    (symRoot (rBits (X ++ [0]) ++ (rX 2 0 ++ rBits ([0] ++ X ++ [0, 0]))))
    [.callH] (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem Num_marker_phase (m p a : ℕ) (e chi : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (hn : Num chi j r) :
    ∃ s, Num chi (j + m * 3) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + a + m * 3)) +> (sep e +> r))))) [tm40]⊢*
        (root ((X ^ (1 + p + m)) +> ([0] +> ((X ^ (1 + a)) +> (sep e +> s)))))) := by
  obtain ⟨s, hs, hh⟩ := Num_add (m * 3) chi j r hn
  have hf : SideRLs tm40 (hf ^ (m * 6))
      ((X ^ (a + m * 3)) +> (sep e +> r)) ((X ^ a) +> (sep e +> s)) :=
    eq_mp_rev (F_pairs_side (m * 3) a e r s hh) (by eq_omega)
  exact ⟨s, hs, eq_mp_rev (marker_calls m p _ _ hf) (by eq_omega)⟩

private theorem root_X_front (a b : ℕ) (r : ListBlank (Fin 2)) :
    root ((X ^ a) +> ((X ^ b) +> r)) = root ((X ^ (a + b)) +> r) := by
  rw [append_X_pow]

private theorem CutNum_root (p d : ℕ) (chi : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum chi j d r) :
    ∃ s, Num chi j s ∧ root ((X ^ (p + d)) +> r) = root ((X ^ p) +> s) :=
  ⟨(X ^ d) +> r, H, (root_X_front p d r).symm⟩

private theorem Num_even4_B21 (u v : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (10 + v * 6) r) :
    ∃ s, Num true (36 + u * 6 + v * 12) s ∧
      ((root ((X ^ (2 + u * 2)) +> ([0] +> (X +> ([0] +> ((X ^ 4) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (7 + u + v * 2)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨s, hs, h8⟩ := CutNum_Fs 8 true (10 + v * 6) 0 r hn (by omega)
  obtain ⟨t, ht, es⟩ := CutNum_root (1 + u * 2) 8 true (10 + v * 6 + 8) s hs
  obtain ⟨t1, hn1, et⟩ :=
    CutNum_digit_tail true false _ (7 + v * 3) 0 (10 + v * 3) t ht (by cond_omega) (by cond_omega)
  obtain ⟨t2, hn2, hn0⟩ := Num_normal (9 + u * 2 + v * 3) false (7 + v * 3) t1 hn1
  obtain ⟨t3, hn3, e2⟩ :=
    CutNum_digit_tail false true _ (18 + u * 3 + v * 6) 0 (19 + u * 3 + v * 6) t2 hn2
    (by cond_omega) (by cond_omega)
  obtain ⟨z, hz, hm⟩ := Num_marker_phase (6 + u + v * 2) 0 1 true true (18 + u * 3 + v * 6) t3 hn3
  refine ⟨z, eq_mp_rev hz (by eq_omega), ?_⟩
  refine ReachesPlus.trans (two_even4 (u * 2) r s h8) ?_
  have h_mid : root ((X ^ (9 + u * 2)) +> s) =
      root ((X ^ (2 + (9 + u * 2 + v * 3))) +> ([0, 0] +> t1)) := by
    have h_step1 : root ((X ^ (9 + u * 2)) +> s) = root ((X ^ (1 + u * 2)) +> t) := by
      rw [← es]
      eq_omega
    rw [h_step1, et]
    dsimp only [sep]
    eq_omega
  rw [h_mid]
  refine ReachesPlus.trans_star hn0 ?_
  rw [e2]
  exact eq_mp_rev hm (by dsimp only [sep]; eq_omega)

private theorem nested_even_prepare_front (p a : ℕ) (r : ListBlank (Fin 2)) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1] +> default))) r) := by
  have h_run := runSym_plus 300
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ++ [0, 0])))
    (symPending 0 1 (lBits [1, 1, 0, 1, 1] ++ lDr 1 0 ++ lBits [1]) true [])
    [] (by decide) (fun i => if i = 0 then p else a) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem D1s_zero4_cleanup (p : ℕ) (r : ListBlank (Fin 2)) :
    (((Dr ^ (1 + p)) +> ([1] +> default)) <{{A}} ([0, 0, 0, 0] +> r)) [tm40]⊢⁺
      (root ([0] +> ((X ^ (1 + p)) +> ([0, 0, 0, 0] +> r)))) := by
  have h_run := runSym_plus 300
    { dir := false, q := A, left := lDr 1 0 ++ lBits [1], right :=
      rBits [0, 0, 0, 0], leftIsDefault := true }
    (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0, 0, 0, 0]))
    [] (by decide) (fun _ => p) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_nested_even_front (p a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + a + 2 ≤ j) :
    ∃ s, CutNum b (j + 6 + a * 3) (d + 3 + a * 2) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ([0] +> ((X ^ (1 + p)) +> ([0, 0, 0, 0] +> s))))) := by
  obtain ⟨s, hs, hp⟩ :=
    Num_pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1] +> default))) b j d r hn hd
  obtain ⟨t, ht, h3⟩ := CutNum_Fs 3 b _ _ s hs (by omega)
  refine ⟨(X ^ 2) +> t,
    CutNum_prepend b (j + 6 + a * 3) (d + 3 + a * 2) 2 t (CutNum_cast (by omega) (by omega) ht), ?_⟩
  refine ReachesPlus.trans (nested_even_prepare_front p a r) ?_
  refine ReachesPlus.trans hp ?_
  exact ReachesPlus.trans (marked11011_finish ((Dr ^ (1 + p)) +> ([1] +> default)) s t h3)
    (D1s_zero4_cleanup p ((X ^ 2) +> t))

private theorem birth_positive_finish (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 hf r s) :
    ((T2r +> ((Dr ^ b) +> ([1, 1, 1] +> default))) {{B}}> r) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ b) +> ([0] +> ((X ^ 3) +> s)))))) := by
  have h_run := runSym_plus 100
    { dir := true, q := B, left := lBits T2r ++ (lDr 0 0 ++ lBits [1, 1, 1]), right :=
      [], leftIsDefault := true }
    (symRoot (rBits (X ++ [0]) ++ (rX 0 0 ++ rBits ([0] ++ X ^ 3))))
    [.callHf] (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem birth_full (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (6 + p * 6)) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (3 + p * 3)) +> ([0] +> ((X ^ 3) +> s)))))) := by
  obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (p * 6 + 3) H (by omega)
  obtain ⟨rm, hm, hlast⟩ := sideRLs_pow_split (p * 6) 3 hs (by omega)
  obtain ⟨rt, h2, h1⟩ := sideRLs_pow_split 2 1 hlast (by omega)
  refine ReachesPlus.trans (birth_prepare p r r3 h3) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev (birth_cycles p 0 0 r3 rm hm) (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (birth_end (p * 3) rm rt h2) (by eq_omega)) ?_
  exact birth_positive_finish (3 + p * 3) rt s h1

private theorem CutNum_birth (p : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + 4 + p * 6 ≤ j) :
    ∃ s, CutNum b (j + 6 + p * 6) (d + 3 + p * 6) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (3 + p * 3)) +> ([0] +> s)))))) := by
  obtain ⟨s, hs, hf⟩ := CutNum_Fs (6 + p * 6) b j d r hn (by omega)
  refine ⟨(X ^ 3) +> s, ?_, birth_full p r s hf⟩
  exact CutNum_prepend b (j + 6 + p * 6) (d + 3 + p * 6) 3 s (CutNum_cast (by omega) (by omega) hs)

set_option maxRecDepth 100000 in
private theorem two_even3 (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 5) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> ((X ^ 4) +> s)))))) := by
  have h_run := runSym_plus 600
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0, 0])))
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y ++ [0, 0] ++ X ^ 4)))
    (List.replicate 5 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem marked_even5_half (p a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 5) +> ([0, 0] +> r)))))))
      [tm40]⊢⁺
      (root ([0] +>
        ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))))) := by
  have h_run := runSym_plus 600
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ^ 5 ++ [0, 0])))
    (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ^ 3 ++ [0, 0])))
    (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem leading_marked_even3_prepare (p a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ([0] +>
      ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))) [tm40]⊢⁺
      (pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1, 1] +> default))) s) := by
  have h_run := runSym_plus 600
    (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ^ 3 ++ [0, 0])))
    (symPending 0 1 (lBits [1, 1, 0, 1, 1] ++ lDr 1 0 ++ lBits [1, 1]) true [])
    (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem D11_zero4_cleanup (p : ℕ) (r : ListBlank (Fin 2)) :
    (((Dr ^ p) +> ([1, 1] +> default)) <{{A}} ([0, 0, 0, 0] +> r)) [tm40]⊢⁺
      (root ((X ^ (1 + p)) +> ([0, 0, 0, 0] +> r))) := by
  have h_run := runSym_plus 300
    { dir := false, q := A, left := lDr 0 0 ++ lBits [1, 1], right :=
      rBits [0, 0, 0, 0], leftIsDefault := true }
    (symRoot (rX 1 0 ++ rBits [0, 0, 0, 0]))
    [] (by decide) (fun _ => p) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_marked_even3 (p a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + a ≤ j) :
    ∃ s, CutNum b (j + 8 + a * 3) (d + 3 + a * 2) s ∧
      ((root ([0] +>
        ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))))
        [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0, 0, 0, 0] +> s)))) := by
  obtain ⟨s, hs, h2⟩ := CutNum_hs 2 b j d r hn (by omega)
  obtain ⟨t, ht, hp⟩ :=
    Num_pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1, 1] +> default))) b (j + 2) d s hs
    (by omega)
  obtain ⟨u, hu, h3⟩ := CutNum_Fs 3 b (j + 2 + (1 + a) * 3) (d + (1 + a) * 2) t ht (by omega)
  refine ⟨(X ^ 2) +> u, ?_, ?_⟩
  · exact CutNum_prepend b (j + 8 + a * 3) (d + 3 + a * 2) 2 u
      (CutNum_cast (by omega) (by omega) hu)
  · refine ReachesPlus.trans (leading_marked_even3_prepare p a r s h2) ?_
    refine ReachesPlus.trans hp ?_
    refine ReachesPlus.trans (marked11011_finish ((Dr ^ (1 + p)) +> ([1, 1] +> default)) t u h3) ?_
    exact eq_mp_rev (D11_zero4_cleanup (1 + p) ((X ^ 2) +> u)) (by eq_omega)

private theorem CutNum_marked_even5 (p a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + a ≤ j) :
    ∃ s, CutNum b (j + 10 + a * 3) (d + 3 + a * 2) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 5) +> ([0, 0] +> r)))))))
        [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0, 0, 0, 0] +> s)))) := by
  obtain ⟨t, ht, h2⟩ := CutNum_hs 2 b j d r hn (by omega)
  obtain ⟨s, hs, hc⟩ := CutNum_marked_even3 p a b (j + 2) d t ht (by omega)
  exact ⟨s, eq_mp_rev hs (by eq_omega), ReachesPlus.trans (marked_even5_half p a r t h2) hc⟩

private theorem Num_two_markers (m p b a : ℕ) (e chi : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (hn : Num chi j r) :
    ∃ s, Num chi (j + m * 6) s ∧
      ((root ((X ^ (1 + p)) +>
        ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + a + m * 6)) +> (sep e +> r))))))) [tm40]⊢*
        (root ((X ^ (1 + p + m)) +>
          ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + a)) +> (sep e +> s)))))))) := by
  obtain ⟨s, hs, hh⟩ := Num_add (m * 6) chi j r hn
  have hf : SideRLs tm40 (hf ^ (m * 12))
      ((X ^ (a + m * 6)) +> (sep e +> r)) ((X ^ a) +> (sep e +> s)) :=
    eq_mp_rev (F_pairs_side (m * 6) a e r s hh) (by eq_omega)
  refine ⟨s, hs, ?_⟩
  exact eq_mp_rev (marker_calls m p _ _ (F_markers (m * 6) b _ _ (eq_mp_rev hf (by eq_omega))))
    (by eq_omega)

set_option maxHeartbeats 2000000 in
-- Symbolic execution via runSym_plus requires additional heartbeats.
set_option maxRecDepth 100000 in
private theorem two_even6_second (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 12) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 6) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (12 + p)) +> s)) := by
  have h_run := runSym_plus 1600
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ X ^ 6 ++ [0, 0])))
    (symRoot (rX 12 0))
    (List.replicate 12 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem odd1_prepare (q : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (root ((X ^ (2 + q)) +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + q)) +> ([0, 0] +> (X +> ([0] +> ((X ^ 2) +> s)))))) := by
  have h_run := runSym_plus 400
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ++ [0] ++ Y)))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ X ++ [0] ++ X ^ 2)))
    (List.replicate 3 .callHf) (by decide) (fun _ => q) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_odd1 (q : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + 5 + q * 6 ≤ j) :
    ∃ s, CutNum b (j + 9 + q * 6) (d + 7 + q * 6) s ∧
      ((root ((X ^ (2 + q)) +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (5 + q * 3)) +> ([0] +> s)))))) := by
  obtain ⟨r3, hn3, h3⟩ := CutNum_Fs 3 b j d r hn (by omega)
  have hc : CutNum b (j + 3) (d + 2) (X +> r3) :=
    CutNum_prepend b (j + 3) (d + 2) 1 r3 (CutNum_cast (by omega) (by omega) hn3)
  obtain ⟨r6, hn6, hf⟩ := CutNum_Fs ((3 + q * 3) * 2) b (j + 3) (d + 2) (X +> r3) hc (by omega)
  have hh := h_columns [] (3 + q * 3) 1 (X +> r3) r6 hf
  dsimp only [markers] at hh
  refine ⟨X +> r6,
    CutNum_prepend b (j + 9 + q * 6) (d + 7 + q * 6) 1 r6 (CutNum_cast (by omega) (by omega) hn6),
    ?_⟩
  refine ReachesPlus.trans (odd1_prepare q r r3 h3) ?_
  have h_nc := normal_calls q _ _ (eq_mp_rev hh (by eq_omega))
  exact eq_mp_rev h_nc (by eq_omega)

set_option maxRecDepth 100000 in
private theorem leading_marker_half (p a : ℕ) (e : Bool) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ([0] +> ((X ^ (1 + p)) +> ([0] +> ((X ^ (3 + a)) +> (sep e +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + a)) +> (sep e +> s))))) := by
  cases e
  · have h_run := runSym_plus 500
      (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 3 1 ++ rBits [0, 0]))
      (symRoot (rX 2 0 ++ rBits [0] ++ rX 1 1 ++ rBits [0, 0]))
      (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
    simpa [evalState, symRoot, root, sep, ListBlank.append_assoc] using h_run
  · have h_run := runSym_plus 500
      (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 3 1 ++ rBits ([0] ++ Y)))
      (symRoot (rX 2 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0] ++ Y)))
      (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
    simpa [evalState, symRoot, root, sep, ListBlank.append_assoc] using h_run

private theorem h_odd_batch (m n : ℕ) :
    SegRLs tm40 (h ^ (m * 2 + 1)) (h ^ (m + 1))
      (X ^ n ++ [0] ++ Y) (X ^ (1 + n + m) ++ [0, 0]) := by
  rw [pow_add_list h (m * 2) 1, pow_add_list h m 1, pow_one_list h]
  have h2 := digit_odd_all (n + m)
  have h_exp : 1 + (n + m) = 1 + n + m := by omega
  rw [h_exp] at h2
  exact (h_pairs_odd m n).trans h2

private theorem h_odd_batch_side (m n : ℕ) {r s : ListBlank (Fin 2)}
    (H : SideRLs tm40 (h ^ (m + 1)) r s) :
    SideRLs tm40 (h ^ (m * 2 + 1)) ((X ^ n) +> ([0] +> (Y +> r)))
      ((X ^ (1 + n + m)) +> ([0, 0] +> s)) := by
  have h_seg := (h_odd_batch m n).sideRLs_concat H
  rwa [List.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc]
    at h_seg

private theorem a1_even_finish (a : ℕ) (r : ListBlank (Fin 2)) :
    (([1] +> default) <{{F}} ([1, 0] +> (Y +> ((X ^ a) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (1 + a)) +> ([0] +> (Y +> r)))))) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits [1], right :=
      rBits ([1, 0] ++ Y) ++ (rX 0 0 ++ rBits [0, 0]), leftIsDefault := true }
    (symRoot (rBits (X ++ [0]) ++ (rX 1 0 ++ rBits ([0] ++ Y))))
    [] (by decide) (fun _ => a) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem pending_marker_short (q b : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (pending q l ((X ^ (1 + b)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending b (Jr +> ((Dr ^ q) +> l)) s) := by
  have h_run := runSym_plus 200
    (symPending 0 0 [] false (rX 1 1 ++ rBits ([0] ++ X ^ 2 ++ [0, 0])))
    (symPending 0 1 (lBits Jr ++ lDr 0 0) false [])
    [.callH] (by decide) (fun i => if i = 0 then q else b) l r s H
  simpa [evalState, symPending, pending, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem birth_marker_five (a b c : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (birth (2 + a) (1 + b) ((X ^ (1 + c)) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + a)) +> ([0, 0] +> ((X ^ (2 + b)) +> ([0] +>
        ((X ^ (4 + c)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s)))))))))) := by
  have h_run := runSym_plus 700
    (symBirth 2 0 1 1 (rX 1 2 ++ rBits ([0] ++ X ^ 5 ++ [0] ++ Y)))
    (symRoot
      (rX 2 0 ++
      (rBits [0, 0] ++ (rX 2 1 ++ (rBits [0] ++ (rX 4 2 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ Y)))))))
    (List.replicate 3 .callH) (by decide)
    (fun i => if i = 0 then a else if i = 1 then b else c) default r s H
  simpa [evalState, symBirth, symRoot, birth, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem marker_T_cycle (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (4 + b)) +> ([0] +> (Y +> (Y +> r))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> ((X ^ (1 + b)) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> (X +> s))))))))) := by
  have h_run := runSym_plus 600
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 4 1 ++ rBits ([0] ++ Y ++ Y)))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0] ++ Y ++ X ^ 3 ++ [0] ++ X)))))
    (List.replicate 6 .callHf) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem one_odd1 (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (root (X +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> s)))))) := by
  have h_run := runSym_plus 400
    (symRoot (rBits (X ++ [0] ++ X ++ [0] ++ Y)))
    (symRoot (rBits (X ++ [0] ++ X ^ 2 ++ [0] ++ X ^ 2)))
    (List.replicate 3 .callHf) (by decide) (fun _ => 0) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_one_odd1 (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + 1 ≤ j) :
    ∃ s, CutNum b (j + 3) (d + 1) s ∧
      ((root (X +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ 2) +> ([0] +> s)))))) := by
  obtain ⟨s, hs, h3⟩ := CutNum_Fs 3 b j d r hn (by omega)
  exact ⟨(X ^ 2) +> s, CutNum_prepend b (j + 3) (d + 1) 2 s (CutNum_cast (by omega) (by omega) hs),
    one_odd1 r s h3⟩

private theorem CutNum_a1_even (q : ℕ) (b : Bool) (j d k a : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + q + 2 ≤ j)
    (hj : j + (1 + q) * 3 = cond b 4 0 + k * 2)
    (ha : d + (1 + q) * 2 + a = cond b 3 1 + k) :
    ∃ s, Num (!b) k s ∧
      ((root ((X ^ (1 + q)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (1 + a)) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨s, hs, hp⟩ := Num_pending q ([1] +> default) b j d r hn hd
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail b false _ k _ a s hs (by dsimp only [cond] at hj ⊢; omega) ha
  refine ⟨t, ht, ?_⟩
  refine ReachesPlus.trans (a1_prepare q r) ?_
  refine ReachesPlus.trans hp ?_
  rw [es]
  exact a1_even_finish a t

private theorem CutNum_zero4_leading_even (u : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 ≤ j + 1) :
    ∃ s, CutNum b (j + 2 + u * 6) d s ∧
      ((root ([0] +> ((X ^ (2 + u * 2)) +> ([0, 0, 0, 0] +> r)))) [tm40]⊢⁺
        (root ((X ^ (1 + u)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, h1⟩ := CutNum_hs (2 + u * 3) b j d r hn (by omega)
  have hh :
    SideRLs tm40 (h ^ (3 + u * 6)) ([0] +> (Y +> r)) ((X ^ (2 + u * 3)) +> ([0, 0] +> r1)) :=
    eq_mp_rev (h_odd_batch_side (1 + u * 3) 0 (r := r) (s := r1) (eq_mp_rev h1 (by eq_omega)))
      (by eq_omega)
  obtain ⟨s, hs, h2⟩ := CutNum_hs (u * 3) b _ d r1 hn1 (by omega)
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (leading_zero4 (u * 2) r) ?_
  refine ReachesPlus.trans_star
    (eq_mp_rev (normal_calls (u * 2) _ _ (eq_mp_rev hh (by eq_omega))) (by eq_omega)) ?_
  exact eq_mp_rev (marker_hcalls u 0 2 _ _ h2) (by eq_omega)

set_option maxRecDepth 100000 in
private theorem birth_last_three (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (birth 2 (1 + b) r) [tm40]⊢⁺
      ((T1r +> ((Dr ^ (3 + b)) +> (EBr +> default))) {{B}}> s) := by
  have h_run := runSym_plus 400
    (symBirthConstA 2 1 0 [])
    { dir := true, q := B, left := lBits T1r ++ (lDr 3 0 ++ lBits EBr), right :=
      [], leftIsDefault := true }
    (List.replicate 3 .callHf) (by decide) (fun _ => b) default r s H
  simpa [evalState, symBirthConstA, birth, ListBlank.append_assoc] using h_run

private theorem birth_E_evenzero (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    ((T1r +> ((Dr ^ b) +> (EBr +> default))) {{B}}> ([0, 0] +> r)) [tm40]⊢⁺
      (root ([0, 0, 0] +> (Y +> ((X ^ b) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s))))))) := by
  have h_run := runSym_plus 400
    { dir := true, q := B, left := lBits T1r ++ (lDr 0 0 ++ lBits EBr), right :=
      rBits [0, 0], leftIsDefault := true }
    (symRoot (rBits ([0, 0, 0] ++ Y) ++ rX 0 0 ++ rBits ([0] ++ X ^ 2 ++ [0, 0])))
    [.callH] (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem birth_E_underflow (p : ℕ) (r t s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (6 + p * 6)) r ([0, 0] +> t))
    (H1 : SideRLs tm40 h t s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root ([0, 0, 0] +> (Y +> ((X ^ (3 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s))))))) := by
  obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (p * 6 + 3) H (by omega)
  obtain ⟨rm, hm, hlast⟩ := sideRLs_pow_split (p * 6) 3 hs (by omega)
  refine ReachesPlus.trans (eq_mp_rev (birth_prepare (1 + p) r r3 h3) (by eq_omega)) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev (birth_cycles p 1 0 r3 rm hm) (by eq_omega)) ?_
  exact ReachesPlus.trans (birth_last_three (p * 3) rm ([0, 0] +> t) hlast)
    (birth_E_evenzero (3 + p * 3) t s H1)

private theorem birth_E_prelude (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ([0, 0, 0] +> (Y +> ((X ^ b) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ([0] +> (Y +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0, 0] +> s))))))) := by
  have h_run := runSym_plus 400
    (symRoot (rBits ([0, 0, 0] ++ Y) ++ rX 0 0 ++ rBits ([0] ++ X ^ 2 ++ [0, 0])))
    (symRoot (rBits ([0] ++ Y) ++ rX 2 0 ++ rBits ([0] ++ X ++ [0, 0])))
    [.callH] (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem C1_zero4_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ([0] +> ((X ^ (1 + p)) +> ([0, 0, 0, 0] +> ((X ^ 2) +> s))))) := by
  have h_run := runSym_plus 400
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ++ [0] ++ X ++ [0, 0])))
    (symRoot (rBits [0] ++ (rX 1 0 ++ rBits ([0, 0, 0, 0] ++ X ^ 2))))
    (List.replicate 3 .callHf) (by decide)
    (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_C1_even (u : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 1 ≤ j) :
    ∃ s, CutNum chi (j + 5 + u * 6) (d + 1) s ∧
      ((root ((X ^ (2 + u * 2)) +> ([0] +> (X +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (1 + u)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨t, HT, HF⟩ := CutNum_Fs 3 chi j d r HN (by omega)
  have HN1 : CutNum chi (j + 3) (d + 1) ((X ^ 2) +> t) :=
    CutNum_prepend chi (j + 3) (d + 1) 2 t (CutNum_cast (by omega) (by omega) HT)
  obtain ⟨s, HS, HZ⟩ :=
    CutNum_zero4_leading_even u chi (j + 3) (d + 1) ((X ^ 2) +> t) HN1 (by omega)
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  exact ReachesPlus.trans (eq_mp_rev (C1_zero4_prepare (1 + u * 2) r t HF) (by eq_omega)) HZ

set_option maxRecDepth 100000 in
private theorem three_even3 (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (root ((X ^ (1 + p)) +>
      ([0] +> ((X ^ (3 + b)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> ((X ^ (1 + b)) +> ([0, 0] +> (X +> ([0, 0] +> ((X ^ 5) +> s)))))))) := by
  have h_run := runSym_plus 800
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 3 1 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0, 0])))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0, 0] ++ X ++ [0, 0] ++ X ^ 5)))))
    (List.replicate 6 .callHf) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem a2_digit_finish (a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (([1, 1, 0, 1, 1, 1] +> default) <{{F}}
      ([1, 0] +> (Y +> ((X ^ (1 + a)) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root (X +> ([0, 0, 0] +> ((X ^ (2 + a)) +> ([0, 0] +> s))))) := by
  have h_run := runSym_plus 250
    { dir := false, q := F, left := lBits [1, 1, 0, 1, 1, 1], right :=
      rBits ([1, 0] ++ Y) ++ (rX 1 0 ++ rBits ([0] ++ Y)), leftIsDefault := true }
    (symRoot (rBits (X ++ [0, 0, 0]) ++ (rX 2 0 ++ rBits [0, 0])))
    (List.replicate 2 .callH) (by decide) (fun _ => a) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem a2_double_odd (k a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (1 + k * 3 + 3)) r s) :
    (root ((X ^ (2 + k * 2)) +>
      ([0] +> ((X ^ 2) +> ([0, 0] +> ((X ^ (1 + a + k)) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root (X +> ([0, 0, 0] +> ((X ^ (2 + a)) +> ([0, 0] +> s))))) := by
  obtain ⟨r1, h1, hs⟩ := sideRLs_pow_split (1 + k * 3) 3 H (by omega)
  obtain ⟨r0, h0, hk⟩ := sideRLs_pow_split 1 (k * 3) h1 (by omega)
  obtain ⟨r2, h2, h3⟩ := sideRLs_pow_split 1 2 hs (by omega)
  have hd :
    SideRLs tm40 h ((X ^ (1 + a + k)) +> ([0] +> (Y +> r))) ((X ^ (2 + a + k)) +> ([0, 0] +> r0)) :=
    eq_mp_rev (digit_odd_all_side (1 + a + k) r r0 h0) (by eq_omega)
  have h_pairs := pending_digit_pairs k 0 a ([1, 1, 0, 1, 1, 1] +> default) r0 r1 hk
  rw [Nat.zero_add] at h_pairs
  refine ReachesPlus.trans (a2_prepare (k * 2) _ _ hd) ?_
  refine stepStar_stepPlus_trans h_pairs ?_
  exact ReachesPlus.trans (pending_digit_end a ([1, 1, 0, 1, 1, 1] +> default) r1 r2 h2)
    (a2_digit_finish a r2 s h3)

private theorem pending_marker_one (q b : ℕ) (l r : ListBlank (Fin 2)) :
    (pending q l ((X ^ (1 + b)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending b (Kr +> ((Dr ^ q) +> l)) r) := by
  have h_run := runSym_plus 100
    (symPending 0 0 [] false (rX 1 1 ++ rBits ([0] ++ X ++ [0, 0])))
    (symPending 0 1 (lBits Kr ++ lDr 0 0) false [])
    [] (by decide) (fun i => if i = 0 then q else b) l r r (SideRLs.nil r)
  simpa [evalState, symPending, pending, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem normal_odd5_prepare (p u b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 5) r s) :
    (root ((X ^ (3 + p)) +> ([0, 0] +> ((X ^ (1 + u)) +> ([0] +>
      ((X ^ (5 + b)) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r)))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> ((X ^ (4 + u)) +> ([0] +>
        ((X ^ (4 + b)) +> ([0] +> (Y +> (Y +> s))))))))) := by
  have h_run := runSym_plus 1300
    (symRoot
      (rX 3 0 ++
      (rBits [0, 0] ++ (rX 1 1 ++ (rBits [0] ++ (rX 5 2 ++ rBits ([0] ++ X ^ 5 ++ [0] ++ Y)))))))
    (symRoot
      (rX 2 0 ++ (rBits [0, 0] ++ (rX 4 1 ++ (rBits [0] ++ (rX 4 2 ++ rBits ([0] ++ Y ++ Y)))))))
    (List.replicate 5 .callH) (by decide)
    (fun i => if i = 0 then p else if i = 1 then u else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem final_marked_first_half (p a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + a)) +> ([0] +> ((X ^ 6) +> ([0, 0] +> r)))))))
      [tm40]⊢⁺
      (root ([0] +>
        ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + a)) +> ([0] +> ((X ^ 4) +> ([0, 0] +> s)))))))) := by
  have h_run := runSym_plus 600
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0] ++ X ^ 6 ++ [0, 0])))
    (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0] ++ X ^ 4 ++ [0, 0])))
    (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem birth_last_five (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 5) r s) :
    (birth 2 (1 + b) r) [tm40]⊢⁺
      ((T1r +> ((Dr ^ (4 + b)) +> ([1, 1] +> (Dr +> ([1] +> default))))) {{B}}> s) := by
  have h_run := runSym_plus 500
    (symBirthConstA 2 1 0 [])
    { dir := true, q := B, left := lBits T1r ++ (lDr 4 0 ++ lBits ([1, 1] ++ Dr ++ [1])), right :=
      [], leftIsDefault := true }
    (List.replicate 5 .callHf) (by decide) (fun _ => b) default r s H
  simpa [evalState, symBirthConstA, birth, ListBlank.append_assoc] using h_run

private theorem birth_evenzero (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    ((T1r +> ((Dr ^ b) +> ([1, 1] +> (Dr +> ([1] +> default))))) {{B}}> ([0, 0] +> r)) [tm40]⊢⁺
      (root ([0] +> (X +> ([0, 0] +> ((X ^ b) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))))) := by
  have h_run := runSym_plus 400
    { dir := true, q := B, left := lBits T1r ++ (lDr 0 0 ++ lBits ([1, 1] ++ Dr ++ [1])), right :=
      rBits [0, 0], leftIsDefault := true }
    (symRoot (rBits ([0] ++ X ++ [0, 0]) ++ (rX 0 0 ++ rBits ([0] ++ X ^ 2 ++ [0, 0]))))
    [.callH] (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem birth_underflow (p : ℕ) (r t s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (8 + p * 6)) r ([0, 0] +> t))
    (H1 : SideRLs tm40 h t s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root ([0] +> (X +> ([0, 0] +> ((X ^ (4 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s))))))))
        := by
  obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (p * 6 + 5) H (by omega)
  obtain ⟨rm, hm, h5⟩ := sideRLs_pow_split (p * 6) 5 hs (by omega)
  refine ReachesPlus.trans (eq_mp_rev (birth_prepare (1 + p) r r3 h3) (by eq_omega)) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev (birth_cycles p 1 0 r3 rm hm) (by eq_omega)) ?_
  exact ReachesPlus.trans (eq_mp_rev (birth_last_five (p * 3) rm ([0, 0] +> t) h5) (by eq_omega))
    (birth_evenzero (4 + p * 3) t s H1)

private theorem Num_birth_evenzero (p : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (6 + p * 6) r) :
    ∃ s, Num false (6 + p * 6) s ∧
      ((root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ([0] +>
          (X +> ([0, 0] +> ((X ^ (4 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s))))))))) := by
  obtain ⟨s, hs, hf⟩ := CutNum_Fs (8 + p * 6) true (6 + p * 6) 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ :=
    Num_O_even_inv (5 + p * 6) ((X ^ (8 + p * 6)) +> s)
    (eq_mp_rev hs (by dsimp only [CutNum]; eq_omega))
  have es : s = [0, 0] +> t :=
    prefix_cancel (X ^ (8 + p * 6)) (et.trans (by eq_omega))
  obtain ⟨u, hu, h1⟩ := Num_inc ht
  refine ⟨u, eq_mp_rev hu (by eq_omega), ?_⟩
  rw [es] at hf
  exact birth_underflow p r t u hf h1

private theorem C_short_prepare (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))))
      [tm40]⊢⁺
      (pending b ([1] +> ((Dr ^ (1 + p)) +> ([1] +> default))) s) := by
  have h_run := runSym_plus 300
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0] ++ X ^ 2 ++ [0, 0])))
    (symPending 0 1 (lBits [1] ++ lDr 1 0 ++ lBits [1]) true [])
    [.callH] (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem C_short_finish (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r s) :
    (([1] +> ((Dr ^ (1 + p)) +> ([1] +> default))) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ (4 + p)) +> s)) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits [1] ++ lDr 1 0 ++ lBits [1], right :=
      rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rX 4 0))
    (List.replicate 3 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_C_short (p b : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum chi j d r) (hd : d * 2 + b + 1 ≤ j) :
    ∃ s, CutNum chi (j + 7 + b * 3) (d + 5 + b * 2) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))))
        [tm40]⊢⁺
        (root ((X ^ (4 + p)) +> s))) := by
  obtain ⟨r1, hn1, h1⟩ := CutNum_hs 1 chi j d r hn (by omega)
  obtain ⟨r2, hn2, hp⟩ :=
    Num_pending b ([1] +> ((Dr ^ (1 + p)) +> ([1] +> default))) chi (j + 1) d r1 hn1 (by omega)
  obtain ⟨s, hs, h3⟩ := CutNum_Fs 3 chi _ _ r2 hn2 (by omega)
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  exact ReachesPlus.trans (C_short_prepare p b r r1 h1)
    (ReachesPlus.trans hp (C_short_finish p r2 s h3))

set_option maxRecDepth 100000 in
private theorem C2_three_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 5) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> ((X ^ 4) +> s)))))) := by
  have h_run := runSym_plus 500
    (symRoot (rX 2 0 ++ (rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0, 0]))))
    (symRoot (rX 2 0 ++ (rBits ([0] ++ Y ++ [0, 0] ++ X ^ 4))))
    (List.replicate 5 .callHf) (by decide)
    (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_C2_three (p : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 3 ≤ j) :
    ∃ s, CutNum chi (j + 5) (d + 1) s ∧
      ((root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> s)))))) := by
  obtain ⟨t, HT, HF⟩ := CutNum_Fs 5 chi j d r HN (by omega)
  refine ⟨(X ^ 4) +> t, ?_, C2_three_prepare p r t HF⟩
  exact CutNum_prepend chi (j + 5) (d + 1) 4 t (CutNum_cast (by omega) (by omega) HT)

set_option maxRecDepth 100000 in
private theorem pending_marker_prepare (q b : ℕ) (l r r2 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r r2) :
    (pending q l ((X ^ (1 + b)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending b (Lr +> ((Dr ^ q) +> l)) r2) := by
  have h_run := runSym_plus 300
    (symPending 0 0 [] false (rX 1 1 ++ rBits ([0] ++ X ^ 3 ++ [0, 0])))
    (symPending 0 1 (lBits Lr ++ lDr 0 0) false [])
    (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then q else b) l r r2 H
  simpa [evalState, symPending, pending, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem marked_F_finish (l r r9 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 9) r r9) :
    ((Lr +> l) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (l <{{A}} ([0, 0] +> ((X ^ 4) +> r9))) := by
  have h_run := runSym_plus 500
    { dir := false, q := F, left := lBits Lr, right := rBits ([1, 0] ++ Y), leftIsDefault := false }
    { dir := false, q := A, left := [], right := rBits ([0, 0] ++ X ^ 4), leftIsDefault := false }
    (List.replicate 9 .callHf) (by decide) (fun _ => 0) l r r9 H
  simpa [evalState, ListBlank.append_assoc] using h_run

private theorem marked_root_cleanup (q : ℕ) (r : ListBlank (Fin 2)) :
    (((Dr ^ q) +> ([1] +> default)) <{{A}} r) [tm40]⊢⁺
      (root ([0] +> ((X ^ q) +> r))) := by
  have h_run := runSym_plus 50
    { dir := false, q := A, left := lDr 0 0 ++ lBits [1], right := [], leftIsDefault := true }
    (symRoot (rBits [0] ++ rX 0 0))
    [] (by decide) (fun _ => q) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_marked_a1 (q a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + a + 6 ≤ j) :
    ∃ s, CutNum b (j + 14 + a * 3) (d + 7 + a * 2) s ∧
      ((root ((X ^ (1 + q)) +>
        ([0] +> (X +> ([0, 0] +> ((X ^ (1 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))))
        [tm40]⊢⁺
        (root ([0] +> ((X ^ q) +> ([0, 0] +> s))))) := by
  obtain ⟨r2, hn2, h2⟩ := CutNum_hs 2 b j d r hn (by omega)
  obtain ⟨rm, hm, hp⟩ :=
    Num_pending a (Lr +> ((Dr ^ q) +> ([1] +> default))) b (j + 2) d r2 hn2 (by omega)
  obtain ⟨r9, hs, h9⟩ := CutNum_Fs 9 b (j + 2 + (1 + a) * 3) (d + (1 + a) * 2) rm hm (by omega)
  refine ⟨(X ^ 4) +> r9, ?_, ?_⟩
  · exact CutNum_prepend b (j + 14 + a * 3) (d + 7 + a * 2) 4 r9
      (CutNum_cast (by omega) (by omega) hs)
  · refine ReachesPlus.trans (a1_prepare q _) ?_
    refine ReachesPlus.trans (pending_marker_prepare q a ([1] +> default) r r2 h2) ?_
    refine ReachesPlus.trans hp ?_
    refine ReachesPlus.trans (marked_F_finish ((Dr ^ q) +> ([1] +> default)) rm r9 h9) ?_
    exact marked_root_cleanup q ([0, 0] +> ((X ^ 4) +> r9))

private theorem Y_h (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 2) r s) :
    SideRLs tm40 h (Y +> r) (X +> ([0] +> (X +> s))) := by
  refine SideRLs.cons (fun l => ?_) (SideRLs.nil _)
  have h_run := runSym_plus 100
    { dir := true, q := B, left := lBits Dr, right := rBits Y, leftIsDefault := false }
    { dir := false, q := A, left := [], right := rBits (X ++ [0] ++ X), leftIsDefault := false }
    (List.replicate 2 .callHf) (by decide) (fun _ => 0) l r s H
  simpa [evalState, toDHCfg, ListBlank.append_assoc] using h_run

private theorem Y_hs (m : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (2 + m * 2)) r s) :
    SideRLs tm40 (h ^ (1 + m)) (Y +> r) ((X ^ (1 + m)) +> ([0] +> (X +> s))) := by
  obtain ⟨r2, h2, hs⟩ := sideRLs_pow_split 2 (m * 2) H (by omega)
  have hm : SideRLs tm40 (h ^ m) (X +> ([0] +> (X +> r2))) ((X ^ (1 + m)) +> ([0] +> (X +> s))) :=
    by
    simpa [markers] using h_columns [] m 1 r2 s hs
  rw [pow_add_list h 1 m, pow_one_list h]
  exact (Y_h r r2 h2).trans hm

set_option maxRecDepth 100000 in
private theorem marked_J_finish (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    ((Jr +> (Dr +> l)) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (l <{{A}} (X +> (Y +> ([0] +> ((X ^ 3) +> s))))) := by
  have h_run := runSym_plus 350
    { dir := false, q := F, left := lBits (Jr ++ Dr), right :=
      rBits ([1, 0] ++ Y), leftIsDefault := false }
    { dir := false, q := A, left := [], right := rBits (X ++ Y ++ [0] ++ X ^ 3), leftIsDefault :=
      false }
    (List.replicate 6 .callHf) (by decide) (fun _ => 0) l r s H
  simpa [evalState, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem J_root_cleanup (q : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r s) :
    (((Dr ^ q) +> ([1, 1, 0, 1, 1, 1] +> default)) <{{A}} (X +> (Y +> ([0] +> ((X ^ 3) +> r)))))
      [tm40]⊢⁺
      (root ((X ^ (3 + q)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> s)))))) := by
  have h_run := runSym_plus 350
    { dir := false, q := A, left := lDr 0 0 ++ lBits [1, 1, 0, 1, 1, 1], right :=
      rBits (X ++ Y ++ [0] ++ X ^ 3), leftIsDefault := true }
    (symRoot (rX 3 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3)))
    (List.replicate 4 .callHf) (by decide) (fun _ => q) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem marked_J_root (q : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 10) r s) :
    ((Jr +> ((Dr ^ (1 + q)) +> ([1, 1, 0, 1, 1, 1] +> default))) <{{F}} ([1, 0] +> (Y +> r)))
      [tm40]⊢⁺
      (root ((X ^ (3 + q)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> s)))))) := by
  obtain ⟨r6, h6, h4⟩ := sideRLs_pow_split 6 4 H (by omega)
  refine ReachesPlus.trans ?_ (J_root_cleanup q r6 s h4)
  exact eq_mp_rev (marked_J_finish ((Dr ^ q) +> ([1, 1, 0, 1, 1, 1] +> default)) r r6 h6)
    (by eq_omega)

set_option maxRecDepth 100000 in
private theorem two_even2 (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 7) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (6 + p)) +> s)) := by
  have h_run := runSym_plus 500
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 2 ++ [0, 0])))
    (symRoot (rX 6 0))
    (List.replicate 7 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem W_root_cleanup (q : ℕ) (r : ListBlank (Fin 2)) :
    (((Dr ^ q) +> (Wr +> default)) <{{A}} ([0, 0] +> r)) [tm40]⊢⁺
      (root ([0] +> (X +> ([0] +> ((X ^ q) +> ([0] +> (Y +> r))))))) := by
  have h_run := runSym_plus 100
    { dir := false, q := A, left := lDr 0 0 ++ lBits Wr, right := rBits [0, 0], leftIsDefault :=
      true }
    (symRoot (rBits ([0] ++ X ++ [0]) ++ (rX 0 0 ++ rBits ([0] ++ Y))))
    [] (by decide) (fun _ => q) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem normal_T_spill (p u b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (root ((X ^ (3 + p)) +> ([0, 0] +> ((X ^ (1 + u)) +> ([0] +>
      ((X ^ (4 + b)) +> ([0] +> (Y +> (Y +> r))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> ((X ^ (4 + u)) +> ([0] +>
        ((X ^ (1 + b)) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> (X +> s))))))))))) := by
  have h_run := runSym_plus 850
    (symRoot
      (rX 3 0 ++ (rBits [0, 0] ++ (rX 1 1 ++ (rBits [0] ++ (rX 4 2 ++ rBits ([0] ++ Y ++ Y)))))))
    (symRoot
      (rX 2 0 ++
      (rBits [0, 0] ++
      (rX 4 1 ++ (rBits [0] ++ (rX 1 2 ++ rBits ([0] ++ Y ++ X ^ 3 ++ [0] ++ X)))))))
    (List.replicate 6 .callHf) (by decide)
    (fun i => if i = 0 then p else if i = 1 then u else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem leading_marked_even4_prepare (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (root ([0] +>
      ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ 4) +> ([0, 0] +> r)))))))) [tm40]⊢⁺
      (pending b ([1] +> ((Dr ^ (1 + p)) +> ([1, 1] +> default))) s) := by
  have h_run := runSym_plus 600
    (symRoot (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0] ++ X ^ 4 ++ [0, 0])))
    (symPending 0 1 (lBits [1] ++ lDr 1 0 ++ lBits [1, 1]) true [])
    (List.replicate 3 .callH) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem CutNum_normalY (q : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 4 + q * 6 ≤ j) :
    ∃ s, CutNum chi (j + 6 + q * 6) (d + 5 + q * 6) s ∧
      ((root ((X ^ (2 + q)) +> ([0, 0] +> (Y +> r)))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (4 + q * 3)) +> ([0] +> s)))))) := by
  obtain ⟨t, HT, HF⟩ := CutNum_Fs (6 + q * 6) chi j d r HN (by omega)
  have HH : SideRLs tm40 (h ^ (3 + q * 3)) (Y +> r)
      ((X ^ (3 + q * 3)) +> ([0] +> (X +> t))) :=
    eq_mp_rev (Y_hs (2 + q * 3) r t (eq_mp_rev HF (by eq_omega))) (by eq_omega)
  refine ⟨X +> t, ?_, ?_⟩
  · exact CutNum_prepend chi (j + 6 + q * 6) (d + 5 + q * 6) 1 t
      (CutNum_cast (by omega) (by omega) HT)
  · exact eq_mp_rev (normal_calls q (Y +> r) _ (eq_mp_rev HH (by eq_omega))) (by eq_omega)

set_option maxHeartbeats 2000000 in
-- Symbolic execution via runSym_plus requires additional heartbeats.
set_option maxRecDepth 100000 in
private theorem marker_odd10_spill (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 12) r s) :
    (root ((X ^ (1 + p)) +>
      ([0] +> (X +> ([0] +> ((X ^ (2 + b)) +> ([0] +> ((X ^ 10) +> ([0] +> (Y +> r))))))))))
      [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> (X +> ([0] +> ((X ^ (1 + b)) +> ([0, 0] +> (X +> ([0] +> ((X ^ 11) +> s))))))))))
        := by
  have h_run := runSym_plus 2800
    (symRoot (rX 1 0 ++ (rBits ([0] ++ X ++ [0]) ++ (rX 2 1 ++ rBits ([0] ++ X ^ 10 ++ [0] ++ Y)))))
    (symRoot
      (rX 2 0 ++ (rBits ([0] ++ X ++ [0]) ++ (rX 1 1 ++ rBits ([0, 0] ++ X ++ [0] ++ X ^ 11)))))
    (List.replicate 12 .callHf) (by decide)
    (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_odd10_spill (p b : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + 10 ≤ j) :
    ∃ s, CutNum chi (j + 12) (d + 1) s ∧
      ((root ((X ^ (1 + p)) +>
        ([0] +> (X +> ([0] +> ((X ^ (2 + b)) +> ([0] +> ((X ^ 10) +> ([0] +> (Y +> r))))))))))
        [tm40]⊢⁺
        (root ((X ^ (2 + p)) +>
          ([0] +> (X +> ([0] +> ((X ^ (1 + b)) +> ([0, 0] +> (X +> ([0] +> s)))))))))) := by
  obtain ⟨t, HT, HF⟩ := CutNum_Fs 12 chi j d r HN (by omega)
  refine ⟨(X ^ 11) +> t, ?_, marker_odd10_spill p b r t HF⟩
  exact CutNum_prepend chi (j + 12) (d + 1) 11 t (CutNum_cast (by omega) (by omega) HT)

private theorem a2_finish (r r3 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 3) r r3) :
    (([1, 1, 0, 1, 1, 1] +> default) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root (X +> ([0, 0, 0] +> ((X ^ 2) +> r3)))) := by
  have h_run := runSym_plus 300
    { dir := false, q := F, left := lBits [1, 1, 0, 1, 1, 1], right :=
      rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rBits (X ++ [0, 0, 0] ++ X ^ 2)))
    (List.replicate 3 .callHf) (by decide) (fun _ => 0) default r r3 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_a2 (q : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b j d r) (hj : d * 2 + q + 1 ≤ j) :
    ∃ r', CutNum b (j + 7 + q * 3) (d + 3 + q * 2) r' ∧
      ((root ((X ^ (2 + q)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root (X +> ([0, 0, 0] +> r')))) := by
  obtain ⟨r1, hn, hr⟩ := CutNum_h b j d r H (by omega)
  obtain ⟨r2, hn', hr'⟩ :=
    Num_pending q ([1, 1, 0, 1, 1, 1] +> default) b (1 + j) d r1 hn (by omega)
  obtain ⟨r3, hn'', hr''⟩ := CutNum_Fs 3 b (1 + j + (1 + q) * 3) (d + (1 + q) * 2) r2 hn' (by omega)
  refine ⟨(X ^ 2) +> r3, ?_, ?_⟩
  · have h_eq : CutNum b (j + 7 + q * 3) (d + 3 + q * 2 + 2) r3 =
                CutNum b (1 + j + (1 + q) * 3 + 3) (d + (1 + q) * 2 + 3) r3 := by
      apply congr_cutnum
      · rfl
      · omega
      · omega
      · rfl
    exact CutNum_prepend b (j + 7 + q * 3) (d + 3 + q * 2) 2 r3 (eq_mp_rev hn'' h_eq)
  · exact ReachesPlus.trans (a2_prepare q r r1 hr) (ReachesPlus.trans hr' (a2_finish r2 r3 hr''))

set_option maxRecDepth 100000 in
private theorem two_odd3 (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (Y +> (Y +> (Y +> s)))))) := by
  have h_run := runSym_plus 450
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0] ++ Y)))
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y ++ Y ++ Y)))
    (List.replicate 3 .callH) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem normal_cycles (m p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (m * 3)) r s) :
    (root ((X ^ (2 + p + m)) +> ([0, 0] +> r))) [tm40]⊢*
      (root ((X ^ (2 + p)) +> ([0, 0] +> s))) := by
  induction m generalizing r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ m ih =>
    obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (m * 3) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (normal_cycle (p + m) r r3 h3) (by eq_omega))
      (ih r3 hs))

set_option maxHeartbeats 2000000 in
-- Symbolic execution via runSym_plus requires additional heartbeats.
set_option maxRecDepth 100000 in
private theorem marker_odd3_transpose (p b c : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 10) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (3 + b)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +>
      ((X ^ (1 + c)) +> ([0] +> (X +> r))))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> (Y +> (X +> ([0] +>
        ((X ^ (5 + c)) +> ([0] +> (X +> s))))))))))) := by
  have h_run := runSym_plus 950
    (symRoot
      (rX 1 0 ++
      (rBits [0] ++
      (rX 3 1 ++ (rBits ([0] ++ X ^ 3 ++ [0] ++ Y) ++ (rX 1 2 ++ rBits ([0] ++ X)))))))
    (symRoot
      (rX 2 0 ++
      (rBits [0] ++ (rX 1 1 ++ (rBits ([0] ++ Y ++ X ++ [0]) ++ (rX 5 2 ++ rBits ([0] ++ X)))))))
    (List.replicate 10 .callHf) (by decide)
    (fun i => if i = 0 then p else if i = 1 then b else c) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem D1_F_finish (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 hf r s) :
    (([1] +> ((Dr ^ (1 + p)) +> ([1, 1] +> default))) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ (4 + p)) +> s)) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits [1] ++ lDr 1 0 ++ lBits [1, 1], right :=
      rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rX 4 0))
    [.callHf] (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem zero_X_zero4 (r : ListBlank (Fin 2)) :
    (root ([0] +> (X +> ([0, 0, 0, 0] +> r)))) [tm40]⊢⁺
      (root (X +> ([0] +> (X +> ([0] +> (Y +> r)))))) := by
  have h_run := runSym_plus 300
    (symRoot (rBits ([0] ++ X ++ [0, 0, 0, 0])))
    (symRoot (rBits (X ++ [0] ++ X ++ [0] ++ Y)))
    [] (by decide) (fun _ => 0) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem zeroY_even_prepare (b : ℕ) (r : ListBlank (Fin 2)) :
    (root ([0] +> (Y +> ((X ^ (1 + b)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (pending b (ZYr +> default) r) := by
  have h_run := runSym_plus 300
    (symRoot (rBits ([0] ++ Y) ++ rX 1 0 ++ rBits ([0] ++ X ++ [0, 0])))
    (symPending 0 0 (lBits ZYr) true [])
    [] (by decide) (fun _ => b) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem zeroY_even_finish (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r s) :
    ((ZYr +> default) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ 4) +> s)) := by
  have h_run := runSym_plus 400
    { dir := false, q := F, left := lBits ZYr, right := rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rBits (X ^ 4)))
    (List.replicate 4 .callHf) (by decide) (fun _ => 0) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_zeroY_even (b : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum chi j d r) (hd : d * 2 + b + 3 ≤ j) :
    ∃ s, CutNum chi (j + 7 + b * 3) (d + 2 + b * 2) s ∧
      ((root ([0] +> (Y +> ((X ^ (1 + b)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺ root s) :=
        by
  obtain ⟨r1, hn1, hp⟩ := Num_pending b (ZYr +> default) chi j d r hn (by omega)
  obtain ⟨r2, hn2, h4⟩ := CutNum_Fs 4 chi _ _ r1 hn1 (by omega)
  refine ⟨(X ^ 4) +> r2,
    CutNum_prepend chi (j + 7 + b * 3) (d + 2 + b * 2) 4 r2
    (CutNum_cast (by omega) (by omega) hn2), ?_⟩
  exact ReachesPlus.trans (zeroY_even_prepare b r)
    (ReachesPlus.trans hp (zeroY_even_finish r1 r2 h4))

private theorem normal_two (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ((X ^ 2) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root ([0] +> (Y +> (X +> s)))) := by
  have h_run := runSym_plus 300
    (symRoot (rBits (X ^ 2 ++ [0, 0])))
    (symRoot (rBits ([0] ++ Y ++ X)))
    (List.replicate 2 .callH) (by decide)
    (fun _ => 0) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem normal_truncated (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (p * 3 + 2)) r s) :
    (root ((X ^ (2 + p)) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root ([0] +> (Y +> (X +> s)))) := by
  obtain ⟨t, H1, H2⟩ := sideRLs_pow_split (p * 3) 2 H (by omega)
  exact ReachesStar.trans_plus
    (eq_mp_rev (normal_cycles p 0 r t H1) (by eq_omega))
    (normal_two t s H2)

private theorem CutNum_even2 (q : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 + q + 11 ≤ j) :
    ∃ s, CutNum chi (j + 19 + q * 3) (d + 15 + q * 2) s ∧
      ((root ((X ^ (2 + q)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ 2) +> ([0] +> (X +> ([0] +> s)))))) := by
  obtain ⟨r1, HN1, HA⟩ := CutNum_a2 q chi j d r HN (by omega)
  obtain ⟨t, E, HT⟩ := CutNum_takeX chi _ _ r1 HN1 (by omega)
  obtain ⟨u, HU, HF⟩ := CutNum_Fs 12 chi _ _ t HT (by omega)
  refine ⟨X +> u, ?_, ?_⟩
  · exact CutNum_prepend chi (j + 19 + q * 3) (d + 15 + q * 2) 1 u
      (CutNum_cast (by omega) (by omega) HU)
  · rw [E] at HA
    exact ReachesPlus.trans HA (a2_cleanup t u HF)

private theorem CutNum_zero4_leading_odd (u : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum b j d r) (Hd : d * 2 ≤ j + 1) :
    ∃ s, CutNum b (j + 6 + u * 6) d s ∧
      ((root ([0] +> ((X ^ (3 + u * 2)) +> ([0, 0, 0, 0] +> r)))) [tm40]⊢⁺
        (root ((X ^ (2 + u)) +> ([0] +> (X +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, HN1, H1⟩ := CutNum_hs (3 + u * 3) b j d r HN (by omega)
  have HH : SideRLs tm40 (h ^ (6 + u * 6)) ([0] +> (Y +> r))
      ((X ^ (3 + u * 3)) +> ([0] +> (Y +> r1))) :=
    eq_mp_rev (h_pairs_odd_side (3 + u * 3) 0 _ _ H1) (by eq_omega)
  obtain ⟨s, HS, H2⟩ := CutNum_hs (3 + u * 3) b (j + (3 + u * 3)) d r1 HN1 (by omega)
  have HF : SideRLs tm40 (hf ^ (6 + u * 6))
      ((X ^ (3 + u * 3)) +> ([0] +> (Y +> r1))) ([0] +> (Y +> s)) :=
    eq_mp_rev (F_pairs_odd_side (3 + u * 3) 0 _ _ H2) (by eq_omega)
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (leading_zero4 (1 + u * 2) r) (by eq_omega)) ?_
  exact plus_star_trans_eq
    (normal_calls (1 + u * 2) _ _ (eq_mp_rev HH (by eq_omega)))
    (marker_calls (1 + u) 0 _ _ (eq_mp_rev HF (by eq_omega))) (by eq_omega)

private theorem F_pairs_even_side (m n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (hf ^ (m * 2)) ((X ^ (n + m)) +> ([0, 0] +> r)) ((X ^ n) +> ([0, 0] +> s)) := by
  have h_seg := (F_pairs m n false).sideRLs_concat H
  dsimp only [sep] at h_seg
  rwa [ListBlank.append_assoc, ListBlank.append_assoc] at h_seg

set_option maxRecDepth 100000 in
private theorem odd2_pair (p b : ℕ) (r r6 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r r6) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ (3 + b)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))
      [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> ((X ^ (1 + b)) +> ([0, 0] +> ((X ^ 2) +> ([0] +> ((X ^ 3) +> r6)))))))) := by
  have h_run := runSym_plus 700
    (symRoot (rX 1 0 ++ (rBits [0] ++ (rX 3 1 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ Y)))))
    (symRoot (rX 2 0 ++ (rBits [0] ++ (rX 1 1 ++ rBits ([0, 0] ++ X ^ 2 ++ [0] ++ X ^ 3)))))
    (List.replicate 6 .callHf) (by decide) (fun i => if i = 0 then p else b) default r r6 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_odd2_pair (p a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + 4 ≤ j) :
    ∃ s, CutNum b (j + 6) (d + 3) s ∧
      ((root ((X ^ (1 + p)) +>
        ([0] +> ((X ^ (3 + a)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> ((X ^ 2) +> ([0] +> s))))))))
          := by
  obtain ⟨r6, hn6, hr6⟩ := CutNum_Fs 6 b j d r hn (by omega)
  refine ⟨(X ^ 3) +> r6, ?_, odd2_pair p a r r6 hr6⟩
  exact CutNum_prepend b (j + 6) (d + 3) 3 r6 (CutNum_cast (by omega) (by omega) hn6)

private theorem pending_marker_cycle (n b a : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (pending (1 + n) l ((X ^ (1 + b)) +> ([0] +> ((X ^ (4 + a)) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (pending n l ((X ^ (2 + b)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> s))))) := by
  have hf : SideRLs tm40 (hf ^ 6) ((X ^ (3 + a)) +> ([0, 0] +> r)) ((X ^ a) +> ([0, 0] +> s)) :=
    eq_mp_rev (F_pairs_even_side 3 a r s H) (by eq_omega)
  exact eq_mp_rev (pending_cycle n l _ _ (F_markers 3 (1 + b) _ _ hf)) (by eq_omega)

private theorem pending_marker_cycles (k n b a : ℕ) (l r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (k * 3)) r s) :
    (pending (n + k) l ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + a + k * 3)) +> ([0, 0] +> r)))))
      [tm40]⊢*
      (pending n l ((X ^ (1 + b + k)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> s))))) := by
  induction k generalizing b r with
  | zero =>
    cases H
    exact ReachesStar.refl _ _
  | succ k ih =>
    obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (k * 3) H (by omega)
    exact ReachesPlus.to_star (ReachesPlus.trans_star
      (eq_mp_rev (pending_marker_cycle (n + k) b (a + k * 3) l r r3 h3) (by eq_omega))
      (eq_mp_rev (ih (1 + b) r3 hs) (by eq_omega)))

set_option maxRecDepth 100000 in
private theorem triple_Y_return (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 8) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> (Y +> (Y +> (Y +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> ((X ^ 2) +> ([0] +> (X +> ([0] +> (X +> s)))))))) := by
  have h_run := runSym_plus 400
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y ++ Y ++ Y)))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ X ^ 2 ++ [0] ++ X ++ [0] ++ X)))
    (List.replicate 8 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem h_pair_even (n : ℕ) :
    SegRLs tm40 (h ^ 2) h (X ^ (1 + n) ++ [0, 0]) (X ^ (2 + n) ++ [0, 0]) := by
  change SegRLs tm40 (h ++ h) ([] ++ h) (X ^ (1 + n) ++ [0, 0]) (X ^ (2 + n) ++ [0, 0])
  exact (digit_even n).trans (digit_odd n)

private theorem h_pairs_even (m n : ℕ) :
    SegRLs tm40 (h ^ (m * 2)) (h ^ m) (X ^ (1 + n) ++ [0, 0]) (X ^ (1 + n + m) ++ [0, 0]) := by
  induction m generalizing n with
  | zero =>
    exact SegRLs.nil _
  | succ m ih =>
    have h_mul : (m + 1) * 2 = 2 + m * 2 := by omega
    rw [h_mul, pow_add_list h 2 (m * 2), Nat.add_comm m 1, pow_add_list h 1 m, pow_one_list h]
    have h1 := h_pair_even n
    have h2 := ih (1 + n)
    have h_exp2 : 1 + (1 + n) = 2 + n := by omega
    have h_exp : 1 + (1 + n) + m = 1 + n + (1 + m) := by omega
    rw [h_exp, h_exp2] at h2
    exact h1.trans h2

private theorem h_pairs_even_side (m n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (h ^ (m * 2)) ((X ^ (1 + n)) +> ([0, 0] +> r))
      ((X ^ (1 + n + m)) +> ([0, 0] +> s)) := by
  have h_seg := (h_pairs_even m n).sideRLs_concat H
  rwa [ListBlank.append_assoc, ListBlank.append_assoc] at h_seg

set_option maxRecDepth 100000 in
private theorem outer_F_finish (p a b d : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (([1] +> outer_left p a b) <{{F}} ([1, 0] +> (Y +> ((X ^ d) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> ((X ^ a) +> ([0] +> (Y +> ((X ^ (5 + b + d)) +> ([0, 0] +> s)))))))) := by
  have h_run := runSym_plus 350
    { dir := false, q := F, left := lBits [1] ++ symOuterLeft 0 0 1 1 2 2, right :=
      rBits ([1, 0] ++ Y) ++ (rX 0 3 ++ rBits [0, 0]), leftIsDefault := true }
    (symRoot
      (rX 2 0 ++
      (rBits [0] ++ (rX 0 1 ++ (rBits ([0] ++ Y) ++ (rX 5 2 ++ (rX 0 3 ++ rBits [0, 0])))))))
    [.callH] (by decide)
    (fun i => if i = 0 then p else if i = 1 then a else if i = 2 then b else d) default r s H
  have h_sim :
    (([1] +> outer_left p a b) <{{F}} ([1, 0] +> (Y +> ((X ^ d) +> ([0, 0] +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +>
        ([0] +> ((X ^ a) +> ([0] +> (Y +> ((X ^ (5 + b)) +> ((X ^ d) +> ([0, 0] +> s))))))))) := by
    simpa [evalState, symRoot, symOuterLeft, root, outer_left, ListBlank.append_assoc] using h_run
  exact eq_mp_rev h_sim (by eq_omega)

set_option maxRecDepth 100000 in
private theorem d3_ten (p b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 10) r s) :
    (root ((X ^ (1 + p)) +>
      ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (6 + b)) +> s)))) := by
  have h_run := runSym_plus 1000
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ++ [0] ++ X ^ 2 ++ [0, 0])))
    (symRoot (rX 2 0 ++ rBits [0] ++ rX 6 1))
    (List.replicate 10 .callHf) (by decide) (fun i => if i = 0 then p else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem critical_E_front3 (r : ListBlank (Fin 2)) :
    (root ((X ^ 3) +> ([0, 0] +> r))) [tm40]⊢⁺
      (root ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))) := by
  have h_run := runSym_plus 300
    (symRoot (rBits (X ^ 3 ++ [0, 0])))
    (symRoot (rBits ([0] ++ X ^ 2 ++ [0] ++ Y)))
    [] (by decide) (fun _ => 0) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem C3_prepare (p a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 2) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))
      [tm40]⊢⁺
      (pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1, 1, 0, 1, 1, 1] +> default))) s) := by
  have h_run := runSym_plus 400
    (symRoot (rX 2 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ^ 3 ++ [0, 0])))
    (symPending 0 1 (lBits [1, 1, 0, 1, 1] ++ lDr 1 0 ++ lBits [1, 1, 0, 1, 1, 1]) true [])
    (List.replicate 2 .callH) (by decide) (fun i => if i = 0 then p else a) default r s H
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem C3_cleanup (p : ℕ) (r : ListBlank (Fin 2)) :
    (((Dr ^ (1 + p)) +> ([1, 1, 0, 1, 1, 1] +> default)) <{{A}} ([0, 0, 0, 0] +> r)) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> r))))) := by
  have h_run := runSym_plus 300
    { dir := false, q := A, left := lDr 1 0 ++ lBits [1, 1, 0, 1, 1, 1], right :=
      rBits [0, 0, 0, 0], leftIsDefault := true }
    (symRoot (rX 2 0 ++ rBits ([0] ++ Y ++ [0, 0])))
    [] (by decide) (fun _ => p) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_C3 (p a : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum chi j d r) (hd : d * 2 + a + 2 ≤ j) :
    ∃ s, CutNum chi (j + 8 + a * 3) (d + 3 + a * 2) s ∧
      ((root ((X ^ (2 + p)) +> ([0] +> ((X ^ (2 + a)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))
        [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0] +> (Y +> ([0, 0] +> s)))))) := by
  obtain ⟨r2, hn2, h2⟩ := CutNum_hs 2 chi j d r hn (by omega)
  obtain ⟨r3, hn3, hp⟩ :=
    Num_pending a ([1, 1, 0, 1, 1] +> ((Dr ^ (1 + p)) +> ([1, 1, 0, 1, 1, 1] +> default))) chi
    (j + 2) d r2 hn2 (by omega)
  obtain ⟨r6, hn6, h3⟩ := CutNum_Fs 3 chi _ _ r3 hn3 (by omega)
  refine ⟨(X ^ 2) +> r6,
    CutNum_prepend chi (j + 8 + a * 3) (d + 3 + a * 2) 2 r6
    (CutNum_cast (by omega) (by omega) hn6), ?_⟩
  refine ReachesPlus.trans (C3_prepare p a r r2 h2) ?_
  refine ReachesPlus.trans hp ?_
  exact ReachesPlus.trans
    (marked11011_finish ((Dr ^ (1 + p)) +> ([1, 1, 0, 1, 1, 1] +> default)) r3 r6 h3)
    (C3_cleanup p ((X ^ 2) +> r6))

private theorem CutNum_zeroY00_odd (u : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 ≤ j + 1) :
    ∃ s, CutNum chi (j + 7 + u * 6) d s ∧
      ((root ((X ^ (3 + u * 2)) +> ([0] +> (Y +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (2 + u)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, H1⟩ := CutNum_hs 1 chi j d r HN (by omega)
  obtain ⟨r2, HN2, H2⟩ := CutNum_hs (3 + u * 3) chi (j + 1) d r1 HN1 (by omega)
  have HH : SideRLs tm40 (h ^ (6 + u * 6)) (X +> ([0, 0] +> r1))
      ((X ^ (4 + u * 3)) +> ([0, 0] +> r2)) :=
    eq_mp_rev (h_pairs_even_side (3 + u * 3) 0 r1 r2 H2) (by eq_omega)
  obtain ⟨s, HS, HM⟩ := CutNum_hs ((1 + u) * 3) chi (j + 1 + (3 + u * 3)) d r2 HN2 (by omega)
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (zeroY00_prepare (1 + u * 2) r r1 H1) (by eq_omega)) ?_
  exact plus_star_trans_eq
    (normal_calls (1 + u * 2) _ _ (eq_mp_rev HH (by eq_omega)))
    (marker_hcalls (1 + u) 0 1 r2 s HM) (by eq_omega)

private theorem a1_double_digit (k a : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ (k * 3 + 2)) r s) :
    (root ((X ^ (1 + k * 2)) +> ([0] +> (X +> ([0, 0] +> ((X ^ (2 + a + k)) +> ([0, 0] +> r)))))))
      [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (3 + a)) +> ([0, 0] +> s))))) := by
  obtain ⟨r0, hk, h2⟩ := sideRLs_pow_split (k * 3) 2 H (by omega)
  obtain ⟨r1, h1, hs⟩ := sideRLs_pow_split 1 1 h2 (by omega)
  have h_pairs := pending_digit_pairs k 0 a ([1] +> default) r r0 hk
  rw [Nat.zero_add] at h_pairs
  exact ReachesPlus.trans (a1_prepare (k * 2) _)
    (stepStar_stepPlus_trans h_pairs
      (ReachesPlus.trans (pending_digit_end a ([1] +> default) r0 r1 h1)
        (a1_digit_finish a r1 s hs)))

private theorem birth_zero (b : ℕ) (r : ListBlank (Fin 2)) :
    ((T2r +> ((Dr ^ b) +> ([1, 1, 1] +> default))) {{B}}> ([0, 0] +> r)) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ b) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) := by
  have h_run := runSym_plus 100
    { dir := true, q := B, left := lBits T2r ++ (lDr 0 0 ++ lBits [1, 1, 1]), right :=
      rBits [0, 0], leftIsDefault := true }
    (symRoot (rBits (X ++ [0]) ++ (rX 0 0 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ Y))))
    [] (by decide) (fun _ => b) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem birth_short (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (5 + p * 6)) r ([0, 0] +> s)) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root (X +> ([0] +> ((X ^ (3 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s)))))))) := by
  obtain ⟨r3, h3, hs⟩ := sideRLs_pow_split 3 (p * 6 + 2) H (by omega)
  obtain ⟨rm, hm, h2⟩ := sideRLs_pow_split (p * 6) 2 hs (by omega)
  refine ReachesPlus.trans (birth_prepare p r r3 h3) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev (birth_cycles p 0 0 r3 rm hm) (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (birth_end (p * 3) rm ([0, 0] +> s) h2) (by eq_omega)) ?_
  exact birth_zero (3 + p * 3) s

private theorem Num_birth_short (p : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (3 + p * 6) r) :
    ∃ s, Num true (4 + p * 6) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (3 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))))) := by
  obtain ⟨s, hs, hf⟩ := CutNum_Fs (5 + p * 6) false (3 + p * 6) 0 r hn (by omega)
  have hs' : Num false ((4 + p * 6) * 2) ((X ^ (5 + p * 6)) +> s) :=
    Num_of_CutNum (by omega) (by omega) hs
  obtain ⟨t, ht, et⟩ := Num_E_even_inv (4 + p * 6) _ hs'
  have es : s = [0, 0] +> t :=
    prefix_cancel (X ^ (5 + p * 6)) (et.trans (by eq_omega))
  subst es
  exact ⟨t, ht, birth_short p r t hf⟩

private theorem leading_zero_even (q : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 h r s) :
    (root ([0] +> ((X ^ (2 + q)) +> ([0, 0] +> r)))) [tm40]⊢⁺
      (root ((X ^ (2 + q)) +> ([0, 0] +> s))) := by
  have h_run := runSym_plus 150
    (symRoot (rBits [0] ++ (rX 2 0 ++ rBits [0, 0])))
    (symRoot (rX 2 0 ++ rBits [0, 0]))
    [.callH] (by decide) (fun _ => q) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem YY_h (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r s) :
    SideRLs tm40 h (Y +> (Y +> r)) (markers [1, 0] s) := by
  refine SideRLs.cons (fun l => ?_) (SideRLs.nil _)
  have h_run := runSym_plus 150
    { dir := true, q := B, left := lBits Dr, right := rBits (Y ++ Y), leftIsDefault := false }
    { dir := false, q := A, left := [], right :=
      rBits (X ++ [0] ++ X ++ [0] ++ X), leftIsDefault := false }
    (List.replicate 4 .callHf) (by decide) (fun _ => 0) l r s H
  simpa [evalState, toDHCfg, markers, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem two_even5 (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 7) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 5) +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0, 0, 0] +> ((X ^ 6) +> s)))) := by
  have h_run := runSym_plus 950
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ++ [0] ++ X ^ 5 ++ [0, 0])))
    (symRoot (rX 2 0 ++ rBits ([0, 0, 0, 0] ++ X ^ 6)))
    (List.replicate 7 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem Num_odd_split (b : Bool) (k : ℕ) (r : ListBlank (Fin 2))
    (H : Num b (cond b 5 1 + k * 2) r) :
    ∃ s, Num (!b) k s ∧ r = (X ^ (cond b 3 1 + k)) +> ([0] +> (Y +> s)) := by
  cases b
  · exact Num_E_odd_inv k r H
  · exact Num_O_odd_inv k r H

private theorem CutNum_a1_odd (q : ℕ) (b : Bool) (j d k : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + q + 2 ≤ j)
    (hj : j + (1 + q) * 3 = cond b 5 1 + k * 2)
    (ha : d + (1 + q) * 2 < cond b 3 1 + k) :
    ∃ s, Num (!b) (1 + k) s ∧
      ((root ((X ^ (1 + q)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root (X +> ([0] +> ((X ^ (2 + (cond b 3 1 + k - (d + (1 + q) * 2)))) +> ([0, 0] +> s))))))
          := by
  obtain ⟨s, hs, hp⟩ := Num_pending q ([1] +> default) b j d r hn hd
  rw [hj] at hs
  obtain ⟨t, ht, et⟩ := Num_odd_split b k _ hs
  have es : s = (X ^ (1 + (cond b 3 1 + k - (d + (1 + q) * 2) - 1))) +> ([0] +> (Y +> t)) := by
    rw [cut_prefix (cond b 3 1 + k) (d + (1 + q) * 2) s ([0] +> (Y +> t))
      (by dsimp only [cond] at ha ⊢; omega) et]
    have h_exp :
      cond b 3 1 + k - (d + (1 + q) * 2) = 1 + (cond b 3 1 + k - (d + (1 + q) * 2) - 1) :=
      by dsimp only [cond] at ha ⊢; omega
    rw [← h_exp]
  obtain ⟨u, hu, h1⟩ := Num_inc ht
  refine ⟨u, hu, ?_⟩
  refine ReachesPlus.trans (a1_prepare q r) ?_
  refine ReachesPlus.trans hp ?_
  rw [es]
  exact eq_mp_rev (a1_digit_finish (cond b 3 1 + k - (d + (1 + q) * 2) - 1) t u h1)
    (by dsimp only [cond] at ha ⊢; eq_omega)

private theorem YY_hs (m : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (4 + m * 4)) r s) :
    SideRLs tm40 (h ^ (1 + m)) (Y +> (Y +> r)) (markers [1 + m, 0] s) := by
  obtain ⟨t, h4, hm⟩ := sideRLs_pow_split 4 (m * 4) H (by omega)
  have h_pow : h ^ (1 + m) = h ++ h ^ m := by
    rw [Nat.add_comm 1 m, pow_succ_list]
  rw [h_pow]
  exact (YY_h r t h4).trans
    (eq_mp_rev (h_columns [0] m 1 t s hm) (by dsimp only [markers]))

private theorem CutNum_a3 (q : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + q + 2 ≤ j) :
    ∃ s, CutNum b (j + 8 + q * 3) (d + 2 + q * 2) s ∧
      ((root ((X ^ (1 + q)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺ root s) := by
  obtain ⟨r1, hn1, h2⟩ := CutNum_hs 2 b j d r hn (by cond_omega)
  obtain ⟨r2, hn2, hp⟩ := Num_pending q ([1, 1] +> default) b (j + 2) d r1 hn1 (by omega)
  obtain ⟨r3, hn3, h3⟩ := CutNum_Fs 3 b _ _ r2 hn2 (by omega)
  refine ⟨(X ^ 3) +> r3,
    CutNum_prepend b (j + 8 + q * 3) (d + 2 + q * 2) 3 r3 (CutNum_cast (by omega) (by omega) hn3),
    ?_⟩
  exact ReachesPlus.trans (a3_prepare q r r1 h2) (ReachesPlus.trans hp (a3_finish r2 r3 h3))

set_option maxRecDepth 100000 in
private theorem klj_zero (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (klj 0 b ([1, 1] +> default) r) [tm40]⊢⁺
      ((T1r +> ((Dr ^ (2 + b)) +> ([1] +> default))) {{B}}> s) := by
  have h_run := runSym_plus 600
    (symKljConstA 0 1 0 (lBits [1, 1]) true [])
    { dir := true, q := B, left := lBits T1r ++ (lDr 2 0 ++ lBits [1]), right :=
      [], leftIsDefault := true }
    (List.replicate 6 .callHf) (by decide) (fun _ => b) default r s H
  simpa [evalState, symKljConstA, klj, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem a2_odd_prepare (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (klj (1 + p) 2 ([1, 1] +> default) s) := by
  have h_run := runSym_plus 500
    (symRoot (rX 2 0 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ X ^ 2 ++ [0] ++ Y)))
    { dir := true, q := B, left :=
      lBits (T1r ++ Dr ^ 3 ++ [1, 0, 0]) ++ (lDr 1 0 ++ lBits [1, 1]), right :=
      [], leftIsDefault := true }
    (List.replicate 4 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, klj, ListBlank.append_assoc] using h_run

private theorem klj_finish (b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 2) r s) :
    ((T1r +> ((Dr ^ b) +> ([1] +> default))) {{B}}> r) [tm40]⊢⁺
      (root ([0] +> ((X ^ b) +> ([0] +> ((X ^ 3) +> s))))) := by
  have h_run := runSym_plus 400
    { dir := true, q := B, left := lBits T1r ++ (lDr 0 0 ++ lBits [1]), right :=
      [], leftIsDefault := true }
    (symRoot (rBits [0] ++ rX 0 0 ++ rBits ([0] ++ X ^ 3)))
    (List.replicate 2 .callHf) (by decide) (fun _ => b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem a2_odd_calls (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ (18 + p * 6)) r s) :
    (root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))) [tm40]⊢⁺
      (root ([0] +> ((X ^ (5 + p)) +> ([0] +> ((X ^ 3) +> s))))) := by
  obtain ⟨r4, h4, hs⟩ := sideRLs_pow_split 4 ((1 + p) * 6 + 8) H (by omega)
  obtain ⟨rm, hm, he⟩ := sideRLs_pow_split ((1 + p) * 6) 8 hs (by omega)
  obtain ⟨r6, h6, h2⟩ := sideRLs_pow_split 6 2 he (by omega)
  refine ReachesPlus.trans (a2_odd_prepare p r r4 h4) ?_
  refine stepStar_stepPlus_trans
    (eq_mp_rev (klj_cycles (1 + p) 0 2 ([1, 1] +> default) r4 rm hm) (by eq_omega)) ?_
  refine ReachesPlus.trans (klj_zero (2 + (1 + p)) rm r6 h6) ?_
  exact eq_mp_rev (klj_finish (5 + p) r6 s h2) (by eq_omega)

set_option maxRecDepth 100000 in
private theorem d7_prepare (p b : ℕ) (r r4 : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 4) r r4) :
    (root ((X ^ (1 + p)) +>
      ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0] +> ((X ^ 7) +> ([0, 0] +> r))))))))) [tm40]⊢⁺
      (root ([0] +>
        ((X ^ (1 + p)) +>
        ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r4)))))))))) := by
  have h_run := runSym_plus 700
    (symRoot (rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ++ [0] ++ X ^ 7 ++ [0, 0])))
    (symRoot
      (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0, 0])))
    (List.replicate 4 .callH) (by decide) (fun i => if i = 0 then p else b) default r r4 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

set_option maxRecDepth 100000 in
private theorem d7_finish (p b : ℕ) (r r5 : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 5) r r5) :
    (root ([0] +>
      ((X ^ (1 + p)) +>
      ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0, 0, 0] +> (Y +> ((X ^ 4) +> r5)))))))
        := by
  have h_run := runSym_plus 500
    (symRoot
      (rBits [0] ++ rX 1 0 ++ rBits [0] ++ rX 2 1 ++ rBits ([0] ++ X ++ [0] ++ X ^ 3 ++ [0, 0])))
    (symRoot (rX 2 0 ++ rBits [0] ++ rX 1 1 ++ rBits ([0, 0, 0] ++ Y ++ X ^ 4)))
    (List.replicate 5 .callHf) (by decide) (fun i => if i = 0 then p else b) default r r5 H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_d7 (p a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (H : CutNum b j d r) (hd : d * 2 ≤ j + 1) :
    ∃ r', CutNum b (j + 9) (d + 1) r' ∧
      ((root ((X ^ (1 + p)) +>
        ([0] +> ((X ^ (2 + a)) +> ([0] +> (X +> ([0] +> ((X ^ 7) +> ([0, 0] +> r))))))))) [tm40]⊢⁺
        (root ((X ^ (2 + p)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0, 0] +> (Y +> r'))))))) := by
  obtain ⟨r4, hn, hr⟩ := CutNum_hs 4 b j d r H (by omega)
  obtain ⟨r5, hn', hr'⟩ := CutNum_Fs 5 b (j + 4) d r4 hn (by omega)
  refine ⟨(X ^ 4) +> r5, ?_, ReachesPlus.trans (d7_prepare p a r r4 hr) (d7_finish p a r4 r5 hr')⟩
  exact CutNum_prepend b (j + 9) (d + 1) 4 r5 (CutNum_cast (by omega) (by omega) hn')

set_option maxRecDepth 100000 in
private theorem odd_three (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ 3) r s) :
    (root ((X ^ (1 + p)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> (Y +> s)))) := by
  have h_run := runSym_plus 350
    (symRoot (rX 1 0 ++ rBits ([0] ++ X ^ 3 ++ [0] ++ Y)))
    (symRoot (rX 2 0 ++ rBits ([0, 0] ++ Y)))
    (List.replicate 3 .callH) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem h_even_batch (m n : ℕ) :
    SegRLs tm40 (h ^ (1 + m * 2)) (h ^ m)
      (X ^ (1 + n) ++ [0, 0]) (X ^ (1 + n + m) ++ [0] ++ Y) := by
  rw [pow_add_list h 1 (m * 2), pow_one_list h]
  have h1 := digit_even n
  have h2 := h_pairs_odd m (1 + n)
  have h_all := h1.trans h2
  simpa only [List.nil_append] using h_all

private theorem h_even_batch_side (m n : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (h ^ m) r s) :
    SideRLs tm40 (h ^ (1 + m * 2))
      ((X ^ (1 + n)) +> ([0, 0] +> r)) ((X ^ (1 + n + m)) +> ([0] +> (Y +> s))) := by
  have h_seg := (h_even_batch m n).sideRLs_concat H
  simpa only [List.append_assoc, ListBlank.append_assoc] using h_seg

set_option maxRecDepth 100000 in
private theorem normal_odd2_spill (p u b : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    (root ((X ^ (3 + p)) +> ([0, 0] +> ((X ^ (1 + u)) +> ([0] +>
      ((X ^ (3 + b)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0, 0] +> ((X ^ (4 + u)) +> ([0] +>
        ((X ^ (1 + b)) +> ([0, 0] +> ((X ^ 2) +> ([0] +> ((X ^ 3) +> s)))))))))) := by
  have h_run := runSym_plus 950
    (symRoot
      (rX 3 0 ++
      (rBits [0, 0] ++ (rX 1 1 ++ (rBits [0] ++ (rX 3 2 ++ rBits ([0] ++ X ^ 2 ++ [0] ++ Y)))))))
    (symRoot
      (rX 2 0 ++
      (rBits [0, 0] ++
      (rX 4 1 ++ (rBits [0] ++ (rX 1 2 ++ rBits ([0, 0] ++ X ^ 2 ++ [0] ++ X ^ 3)))))))
    (List.replicate 6 .callHf) (by decide)
    (fun i => if i = 0 then p else if i = 1 then u else b) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem nested_even_prepare (b : ℕ) (r : ListBlank (Fin 2)) :
    (root (X +> ([0] +> ((X ^ (2 + b)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
      (pending b (Wr +> default) r) := by
  have h_run := runSym_plus 100
    (symRoot (rBits (X ++ [0]) ++ (rX 2 0 ++ rBits ([0] ++ X ++ [0, 0]))))
    (symPending 0 0 (lBits Wr) true [])
    [] (by decide) (fun _ => b) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, symPending, root, pending, ListBlank.append_assoc] using h_run

private theorem marker_second_half (p : ℕ) (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 4) r s) :
    (root ([0] +> ((X ^ (1 + p)) +> ([0] +> (X +> r))))) [tm40]⊢⁺
      (root ((X ^ (2 + p)) +> ([0] +> (X +> s)))) := by
  have h_run := runSym_plus 200
    (symRoot (rBits [0] ++ (rX 1 0 ++ rBits ([0] ++ X))))
    (symRoot (rX 2 0 ++ rBits ([0] ++ X)))
    (List.replicate 4 .callHf) (by decide) (fun _ => p) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_zero4_even (q : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 ≤ 1 + j) :
    ∃ s, CutNum b (j + 7 + q * 6) d s ∧
      ((root ((X ^ (4 + q * 2)) +> ([0, 0, 0, 0] +> r))) [tm40]⊢⁺
        (root ((X ^ (2 + q)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, hn1, h1⟩ := CutNum_hs 1 b j d r hn hd
  obtain ⟨r2, hn2, h2⟩ := CutNum_hs (3 + q * 3) b (j + 1) d r1 hn1 (by omega)
  have hh : SideRLs tm40 (h ^ (6 + q * 6))
      (X +> ([0] +> (Y +> r1))) ((X ^ (4 + q * 3)) +> ([0] +> (Y +> r2))) :=
    eq_mp_rev (h_pairs_odd_side (3 + q * 3) 1 r1 r2 h2) (by eq_omega)
  obtain ⟨s, hs, h3⟩ := CutNum_hs (3 + q * 3) b (j + 1 + (3 + q * 3)) d r2 hn2 (by omega)
  have hf : SideRLs tm40 (hf ^ (6 + q * 6))
      ((X ^ (4 + q * 3)) +> ([0] +> (Y +> r2))) (X +> ([0] +> (Y +> s))) :=
    eq_mp_rev (F_pairs_odd_side (3 + q * 3) 1 r2 s h3) (by eq_omega)
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (zero4_prepare (1 + q * 2) r r1 h1) (by eq_omega)) ?_
  refine ReachesPlus.trans_star
    (eq_mp_rev (normal_calls (1 + q * 2) _ _ (eq_mp_rev hh (by eq_omega))) (by eq_omega)) ?_
  exact eq_mp_rev (marker_calls (1 + q) 0 _ _ (eq_mp_rev hf (by eq_omega))) (by eq_omega)

private theorem D1_zero4_cleanup (r : ListBlank (Fin 2)) :
    ((Dr +> ([1] +> default)) <{{A}} ([0, 0, 0, 0] +> r)) [tm40]⊢⁺
      (root ([0] +> (X +> ([0, 0, 0, 0] +> r)))) := by
  have h_run := runSym_plus 300
    { dir := false, q := A, left := lBits (Dr ++ [1]), right :=
      rBits [0, 0, 0, 0], leftIsDefault := true }
    (symRoot (rBits ([0] ++ X ++ [0, 0, 0, 0])))
    [] (by decide) (fun _ => 0) default r r (SideRLs.nil r)
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_nested_even (a : ℕ) (b : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (hn : CutNum b j d r) (hd : d * 2 + a + 2 ≤ j) :
    ∃ s, CutNum b (j + 6 + a * 3) (d + 3 + a * 2) s ∧
      ((root (X +> ([0] +> ((X ^ (2 + a)) +> ([0] +> (X +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ([0] +> (X +> ([0, 0, 0, 0] +> s))))) := by
  obtain ⟨s, hs, hp⟩ := Num_pending a (Wr +> default) b j d r hn hd
  obtain ⟨t, ht, h3⟩ := CutNum_Fs 3 b (j + (1 + a) * 3) (d + (1 + a) * 2) s hs (by omega)
  refine ⟨(X ^ 2) +> t, ?_, ?_⟩
  · exact CutNum_prepend b (j + 6 + a * 3) (d + 3 + a * 2) 2 t
      (CutNum_cast (by omega) (by omega) ht)
  · refine ReachesPlus.trans (nested_even_prepare a r) ?_
    refine ReachesPlus.trans hp ?_
    have h_wr :
      (Wr +> default : ListBlank (Fin 2)) = [1, 1, 0, 1, 1] +> (Dr +> ([1] +> default)) := by
      dsimp only [Wr, Dr]
      rw [← ListBlank.append_assoc, ← ListBlank.append_assoc]
      rfl
    rw [h_wr]
    exact ReachesPlus.trans (marked11011_finish (Dr +> ([1] +> default)) s t h3)
      (D1_zero4_cleanup ((X ^ 2) +> t))

set_option maxRecDepth 100000 in
private theorem critical_E_finish (r s : ListBlank (Fin 2))
    (H : SideRLs tm40 (hf ^ 6) r s) :
    ((CEr +> default) <{{F}} ([1, 0] +> (Y +> r))) [tm40]⊢⁺
      (root ((X ^ 3) +> ([0] +> ((X ^ 3) +> s)))) := by
  have h_run := runSym_plus 600
    { dir := false, q := F, left := lBits CEr, right := rBits ([1, 0] ++ Y), leftIsDefault := true }
    (symRoot (rBits (X ^ 3 ++ [0] ++ X ^ 3)))
    (List.replicate 6 .callHf) (by decide) (fun _ => 0) default r s H
  simpa [evalState, symRoot, root, ListBlank.append_assoc] using h_run

private theorem CutNum_zeroY00_even (u : ℕ) (chi : Bool) (j d : ℕ) (r : ListBlank (Fin 2))
    (HN : CutNum chi j d r) (Hd : d * 2 ≤ j + 1) :
    ∃ s, CutNum chi (j + 2 + u * 6) d s ∧
      ((root ((X ^ (2 + u * 2)) +> ([0] +> (Y +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (1 + u)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, HN1, H1⟩ := CutNum_hs 1 chi j d r HN (by omega)
  obtain ⟨r2, HN2, H2⟩ := CutNum_hs (1 + u * 3) chi (j + 1) d r1 HN1 (by omega)
  have HH : SideRLs tm40 (h ^ (3 + u * 6)) (X +> ([0, 0] +> r1))
      ((X ^ (2 + u * 3)) +> ([0] +> (Y +> r2))) :=
    eq_mp_rev (h_even_batch_side (1 + u * 3) 0 r1 r2 H2) (by eq_omega)
  obtain ⟨s, HS, H3⟩ := CutNum_hs (u * 3) chi (j + 1 + (1 + u * 3)) d r2 HN2 (by omega)
  have HF : SideRLs tm40 (hf ^ (u * 6))
      ((X ^ (2 + u * 3)) +> ([0] +> (Y +> r2))) ((X ^ 2) +> ([0] +> (Y +> s))) :=
    eq_mp_rev (F_pairs_odd_side (u * 3) 2 r2 s H3) (by eq_omega)
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (zeroY00_prepare (u * 2) r r1 (eq_mp_rev H1 (by eq_omega))) ?_
  refine plus_star_trans_eq
    (normal_calls (u * 2) _ _ (eq_mp_rev HH (by eq_omega)))
    (marker_calls u 0 _ _ HF) (by eq_omega)

set_option maxRecDepth 100000 in
private theorem init_to_seed : (init []) [tm40]⊢* root ((X ^ 10) +> ([0, 0] +> seed)) := by
  have h_run := stepsNat_sound (K := 6) tm40 init_seed_steps ⟨0, 0, 0, 0⟩ seed_natCfg
    (by decide) (by decide)
  rw [toCfg_zero] at h_run
  have h_cfg : NatCfg.toCfg (K := 6) seed_natCfg = root ((X ^ 10) +> ([0, 0] +> seed)) := by
    have h_hl := toCfg_headLeft (K := 6) (0 : Fin 6) 0 (encodeList seed_word 0)
    try dsimp [seed_natCfg] at h_hl ⊢
    rw [h_hl, decodeHalf_zero, ← decodeHalf_encodeList, decodeHalf_zero]
    unfold root seed_word seed end0
    simp only [append_assoc]
    rfl
  rw [h_cfg] at h_run
  exact ⟨init_seed_steps, h_run⟩

set_option maxRecDepth 100000 in
private theorem init_first_marker :
    ∃ r, Num true 42 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 8) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨s, hn, hr⟩ := Num_normal 8 false 15 seed seed_num
  obtain ⟨t, hn', rfl⟩ := Num_E_even_inv 21 s hn
  obtain ⟨r, hn'', hr'⟩ := Num_markers 7 0 1 true 21 t hn'
  refine ⟨r, hn'', ?_⟩
  refine star_trans_eq (star_plus_eq init_to_seed hr rfl) hr' ?_
  eq_omega

private theorem init_two_markers :
    ∃ r, Num false 49 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 4) +> ([0] +> (X +> ([0] +> (X +> ([0] +> (Y +> r))))))))) :=
        by
  obtain ⟨r, hn, hr⟩ := init_first_marker
  obtain ⟨s, hs, hrs⟩ := CutNum_a2 6 true 42 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 31 _ hs
  have es : s = (X ^ 19) +> ([0] +> (Y +> t)) :=
    cut_prefix 34 15 s ([0] +> (Y +> t)) (by omega) et
  have hc : CutNum true 67 16 ((X ^ 18) +> ([0] +> (Y +> t))) :=
    CutNum_O_odd ht (by omega)
  obtain ⟨u, hu, h36⟩ := CutNum_Fs 36 true 67 16 _ hc (by omega)
  obtain ⟨v, h12, h24⟩ := sideRLs_pow_split 12 24 h36 (by omega)
  obtain ⟨w, hw, ew⟩ := Num_O_odd_inv 49 _ hu
  have hu_eq : u = [0] +> (Y +> w) := prefix_cancel (X ^ 52) ew
  subst hu_eq
  refine ⟨w, hw, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev (a2_cleanup _ v h12) (by eq_omega))) ?_
  exact eq_mp_rev (two_markers 2 1 v ([0] +> (Y +> w)) h24) (by eq_omega)

private theorem init_nested_normal :
    ∃ r, CutNum false 54 3 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 4) +> ([0, 0] +> (X +> ([0] +> (X +> ([0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_markers
  obtain ⟨s, hs, hrs⟩ := CutNum_c1 2 false 49 0 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hrs)⟩

private theorem init_three_markers :
    ∃ r, Num true 45 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 11) +> ([0] +> (X +> ([0] +> ((X ^ 7) +> ([0, 0] +> r))))))))))
          := by
  obtain ⟨r, hn, hr⟩ := init_nested_normal
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 27 _ hn
  have er : r = (X ^ 25) +> ([0, 0] +> t) :=
    cut_prefix 28 3 r ([0, 0] +> t) (by omega) et
  have hc : CutNum false 54 4 ((X ^ 24) +> ([0, 0] +> t)) :=
    CutNum_E_even ht (by omega)
  obtain ⟨s, hs, h36⟩ := CutNum_Fs 36 false 54 4 _ hc (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_even_inv 45 _ hs
  have es : s = (X ^ 6) +> ([0, 0] +> u) :=
    cut_prefix 46 40 s ([0, 0] +> u) (by omega) eu
  refine ⟨u, hu, ?_⟩
  rw [er] at hr
  have h_cols := h_columns [0] 9 1 ((X ^ 24) +> ([0, 0] +> t)) s h36
  have h_norm :=
    normal_calls 2 (markers [1, 0] ((X ^ 24) +> ([0, 0] +> t))) (markers [10, 0] s) h_cols
  rw [es] at h_norm
  exact star_plus_eq hr (eq_mp_rev h_norm (by dsimp only [markers])) (by rfl)

-- sep moved above eq_omega

private theorem init_mixed_columns :
    ∃ r, CutNum true 54 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 2) +> ([0] +> ((X ^ 10) +> ([0, 0, 0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_three_markers
  obtain ⟨s, hs, hrs⟩ := CutNum_d7 0 9 true 45 0 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hrs)⟩

private theorem init_double_digit :
    ∃ r, CutNum true 59 1 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 5) +> ([0] +> (X +> ([0, 0] +> ((X ^ 5) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_mixed_columns
  obtain ⟨s, hs, h5⟩ := CutNum_hs 5 true 54 1 r hn (by omega)
  have h9 : SideRLs tm40 (h ^ 9) ([0] +> (Y +> r)) ((X ^ 5) +> ([0, 0] +> s)) :=
    h_odd_batch_side 4 0 h5
  have h18 : SideRLs tm40 (hf ^ 18)
      ((X ^ 9) +> ([0, 0, 0] +> (Y +> r))) ([0, 0] +> ((X ^ 5) +> ([0, 0] +> s))) :=
    F_pairs_even_side 9 0 _ _ h9
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (marker_calls 3 1 _ _ h18) (by eq_omega)

private theorem init_recovered_digit :
    ∃ r, CutNum true 67 1 r ∧
      ((init []) [tm40]⊢* (root (X +> ([0] +> ((X ^ 4) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_double_digit
  obtain ⟨s, hs, h8⟩ := CutNum_hs 8 true 59 1 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (a1_double_digit 2 1 r s h8))⟩

private theorem init_a1_source :
    ∃ r, CutNum true 70 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 2) +> ([0] +> (X +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_recovered_digit
  obtain ⟨s, hs, h3⟩ := CutNum_hs 3 true 67 1 r hn (by omega)
  have hf6 : SideRLs tm40 (hf ^ 6) ((X ^ 3) +> ([0, 0] +> r)) ([0, 0] +> s) :=
    F_pairs_even_side 3 0 _ _ h3
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (marker_calls 1 0 _ _ hf6) (by eq_omega)

private theorem init_odd_digit :
    ∃ r, Num false 36 r ∧
      ((init []) [tm40]⊢* (root (X +> ([0] +> ((X ^ 35) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_a1_source
  obtain ⟨s, hs, hrs⟩ := Num_pending 1 ([1] +> default) true 70 1 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 36 _ hs
  have es : s = (X ^ 34) +> ([0, 0] +> t) :=
    cut_prefix 39 5 s ([0, 0] +> t) (by omega) et
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star (a1_prepare 1 r)) ?_)
  refine ReachesStar.trans (ReachesPlus.to_star hrs) ?_
  rw [es]
  exact ReachesPlus.to_star (a1_even_finish 34 t)

private theorem init_E69 :
    ∃ r, Num false 69 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 12) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_odd_digit
  obtain ⟨s, hs, h33⟩ := Num_add 33 false 36 r hn
  have hf66 : SideRLs tm40 (hf ^ 66) ((X ^ 34) +> ([0] +> (Y +> r))) (X +> ([0] +> (Y +> s))) :=
    F_pairs_odd_side 33 1 _ _ h33
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (eq_mp_rev (marker_calls 11 0 _ _ hf66) (by eq_omega)) (by eq_omega)

-- ============================================================================
-- 5b. Batch 2 (`Others_v2.v` lines 1001–1802: `birth` through `init_nested_a3`)
-- ============================================================================

-- T2r, birth, congr_birth moved above eq_omega

private theorem init_O70 :
    ∃ r, Num true 70 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 36) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_E69
  obtain ⟨s, hs, hrs⟩ := Num_birth_short 11 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hrs)⟩

private theorem init_even_marked :
    ∃ r, CutNum true 76 3 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 2) +> ([0] +> ((X ^ 34) +> ([0, 0] +> ((X ^ 2) +> ([0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_O70
  obtain ⟨s, hs, hrs⟩ := CutNum_odd2_pair 0 33 true 70 0 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hrs)⟩

private theorem init_marked_a1 :
    ∃ r, Num false 69 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 13) +>
          ([0] +> (X +> ([0, 0] +> ((X ^ 35) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_even_marked
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 36 _ hn
  have er : r = (X ^ 36) +> ([0, 0] +> t) :=
    cut_prefix 39 3 r ([0, 0] +> t) (by omega) et
  have hc : CutNum true 76 4 ((X ^ 35) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨s, hs, h66⟩ := CutNum_Fs 66 true 76 4 _ hc (by omega)
  obtain ⟨u, hu, eu⟩ := Num_O_even_inv 69 _ hs
  have es : s = (X ^ 2) +> ([0, 0] +> u) :=
    cut_prefix 72 70 s ([0, 0] +> u) (by omega) eu
  refine ⟨u, hu, ?_⟩
  rw [er] at hr
  have hh33 := h_columns [] 33 2 _ _ h66
  try dsimp only [markers] at hh33
  have hm := marker_hcalls 11 1 0 _ _ hh33
  rw [es] at hm
  exact star_trans_eq hr hm (by eq_omega)

private theorem init_leading_zero :
    ∃ r, Num true 92 r ∧
      ((init []) [tm40]⊢*
        (root ([0] +> ((X ^ 12) +> ([0, 0] +> ((X ^ 18) +> ([0] +> (Y +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_marked_a1
  obtain ⟨s, hs, hrs⟩ := CutNum_marked_a1 12 34 false 69 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 92 _ hs
  have es : s = (X ^ 18) +> ([0] +> (Y +> t)) :=
    cut_prefix 93 75 s ([0] +> (Y +> t)) (by omega) et
  refine ⟨t, ht, ?_⟩
  rw [es] at hrs
  exact ReachesStar.trans hr (ReachesPlus.to_star hrs)

private theorem init_double_even :
    ∃ r, Num true 93 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 12) +> ([0, 0] +> ((X ^ 19) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_leading_zero
  have hc : CutNum false 185 75 ((X ^ 18) +> ([0] +> (Y +> r))) :=
    CutNum_E_odd hn (by omega)
  obtain ⟨s, hs, h1⟩ := CutNum_hs 1 false 185 75 _ hc (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 93 _ hs
  have es : s = (X ^ 19) +> ([0, 0] +> t) :=
    cut_prefix 94 75 s ([0, 0] +> t) (by omega) et
  refine ⟨t, ht, ?_⟩
  have hl := leading_zero_even 10 _ _ h1
  rw [es] at hl
  exact ReachesStar.trans hr (ReachesPlus.to_star hl)

private theorem init_odd_marked :
    ∃ r, Num true 142 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 12) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_double_even
  have hc : CutNum false 186 75 ((X ^ 19) +> ([0, 0] +> r)) :=
    CutNum_E_even hn (by omega)
  obtain ⟨s, hs, h33⟩ := CutNum_hs 33 false 186 75 _ hc (by omega)
  obtain ⟨t, ht, h66⟩ := CutNum_Fs 66 false 219 75 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_odd_inv 142 _ ht
  have et : t = (X ^ 2) +> ([0] +> (Y +> u)) :=
    cut_prefix 143 141 t ([0] +> (Y +> u)) (by omega) eu
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 10 _ _ h33)) ?_
  have hm := marker_calls 11 0 _ _ h66
  rw [et] at hm
  exact eq_mp_rev hm (by eq_omega)

private theorem init_Y_source :
    ∃ r, Num true 145 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 13) +> ([0, 0] +> (Y +> r))))) := by
  obtain ⟨r, hn, hr⟩ := init_odd_marked
  obtain ⟨s, hs, h3⟩ := Num_add 3 true 142 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (odd_three 11 r s h3))⟩

private theorem init_large_marked :
    ∃ r, Num false 142 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 7) +> ([0] +> ((X ^ 37) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_Y_source
  obtain ⟨s, hs, h72⟩ := CutNum_Fs 72 true 145 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 106 _ hs
  have es : s = (X ^ 37) +> ([0] +> (Y +> t)) :=
    cut_prefix 109 72 s ([0] +> (Y +> t)) (by omega) et
  obtain ⟨u, hu, h36⟩ := Num_add 36 false 106 t ht
  have hf : SideRLs tm40 (hf ^ 72) s (X +> ([0] +> (Y +> u))) := by
    rw [es]
    exact F_pairs_odd_side 36 1 t u h36
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 11 _ _ (Y_hs 35 r s h72))) ?_
  exact eq_mp_rev (marker_calls 6 0 _ _ (F_markers 36 36 s _ hf)) (by eq_omega)

private theorem init_nested_a2 :
    ∃ r, Num true 107 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 19) +>
          ([0] +> ((X ^ 2) +> ([0, 0] +> ((X ^ 35) +> ([0] +> ((X ^ 39) +> ([0, 0] +> r))))))))))
          := by
  obtain ⟨r, hn, hr⟩ := init_large_marked
  obtain ⟨s, hs, hrs⟩ := CutNum_odd2_pair 6 34 false 142 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 74 _ hs
  have es : s = (X ^ 72) +> ([0, 0] +> t) :=
    cut_prefix 75 3 s ([0, 0] +> t) (by omega) et
  have hc : CutNum false 148 4 ((X ^ 71) +> ([0, 0] +> t)) :=
    CutNum_E_even ht (by omega)
  obtain ⟨u, hu, h66⟩ := CutNum_Fs 66 false 148 4 _ hc (by omega)
  obtain ⟨v, hv, ev⟩ := Num_E_even_inv 107 _ hu
  have eu : u = (X ^ 38) +> ([0, 0] +> v) :=
    cut_prefix 108 70 u ([0, 0] +> v) (by omega) ev
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  have hh33 := h_columns [] 33 2 _ _ h66
  try dsimp only [markers] at hh33
  have hm := marker_hcalls 11 7 1 _ _ hh33
  rw [eu] at hm
  exact eq_mp_rev hm (by eq_omega)

private theorem init_nested_pending :
    ∃ r, Num true 144 r ∧
      ((init []) [tm40]⊢*
        (pending 5 ([1, 1, 0, 1, 1, 1] +> default)
          ((X ^ 48) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_a2
  have hc : CutNum false 214 70 ((X ^ 38) +> ([0, 0] +> r)) :=
    CutNum_E_even hn (by omega)
  obtain ⟨s, hs, h2⟩ := CutNum_Fs 2 false 214 70 _ hc (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 108 _ hs
  have es : s = (X ^ 37) +> ([0, 0] +> t) :=
    cut_prefix 109 72 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h36⟩ := Num_add 36 true 108 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  have hh1 := h_columns [] 1 35 _ _ h2
  try dsimp only [markers] at hh1
  have ha2 := a2_prepare 17 _ _ hh1
  rw [es] at ha2
  exact ReachesStar.trans (ReachesPlus.to_star ha2)
    (eq_mp_rev (pending_marker_cycles 12 5 35 1 ([1, 1, 0, 1, 1, 1] +> default) t u h36)
      (by eq_omega))

private theorem init_after_J :
    ∃ r, Num false 147 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 7) +> ([0] +> (X +> ([0] +> ((X ^ 47) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_pending
  obtain ⟨s, hs, h1⟩ := Num_add 1 true 144 r hn
  obtain ⟨t, ht, hp⟩ :=
    Num_pending 47 (Jr +> ((Dr ^ 5) +> ([1, 1, 0, 1, 1, 1] +> default))) true 145 0 s hs (by omega)
  obtain ⟨u, hu, h10⟩ := CutNum_Fs 10 true 289 96 t ht (by omega)
  obtain ⟨v, hv, ev⟩ := Num_O_odd_inv 147 _ hu
  have eu : u = (X ^ 44) +> ([0] +> (Y +> v)) :=
    cut_prefix 150 106 u ([0] +> (Y +> v)) (by omega) ev
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (pending_marker_short 5 47 ([1, 1, 0, 1, 1, 1] +> default) r s h1)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  have hj := marked_J_root 4 t u h10
  rw [eu] at hj
  exact ReachesPlus.to_star (eq_mp_rev hj (by eq_omega))

private theorem init_two_marker_odd5 :
    ∃ r, Num false 189 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 14) +> ([0] +> (X +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_after_J
  obtain ⟨s, hs, h42⟩ := Num_add 42 false 147 r hn
  have hf : SideRLs tm40 (hf ^ 84) ((X ^ 46) +> ([0] +> (Y +> r))) ((X ^ 4) +> ([0] +> (Y +> s))) :=
    F_pairs_odd_side 42 4 r s h42
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (two_markers 7 6 _ _ hf) (by eq_omega)

private theorem init_three_column :
    ∃ r, Num true 193 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 2) +>
          ([0] +> ((X ^ 43) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_marker_odd5
  obtain ⟨r5, hn5, h5⟩ := Num_add 5 false 189 r hn
  obtain ⟨s, hs, h168⟩ := CutNum_Fs 168 false 194 0 r5 hn5 (by omega)
  obtain ⟨r4, h4, h164⟩ := sideRLs_pow_split 4 164 h168 (by omega)
  have h42 : SideRLs tm40 (h ^ 42) (Y +> (Y +> r5)) (markers [42, 0] s) := by
    have h_eq : (42 : ℕ) = 1 + 41 := rfl
    rw [h_eq, pow_add_list h 1 41, pow_one_list h]
    exact (YY_h r5 r4 h4).trans (h_columns [0] 41 1 r4 s h164)
  obtain ⟨t, ht, h24⟩ := CutNum_Fs 24 false 362 168 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_even_inv 193 _ ht
  have et : t = (X ^ 2) +> ([0, 0] +> u) :=
    cut_prefix 194 192 t ([0, 0] +> u) (by omega) eu
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (odd_five 13 r r5 h5)) ?_
  have hn13 := normal_calls 13 _ _ h42
  try dsimp only [markers] at hn13
  refine ReachesStar.trans (ReachesPlus.to_star hn13) ?_
  have hfc := F_columns [42, 0] 6 s t h24
  try dsimp only [markers] at hfc
  have hm := marker_calls 1 0 _ _ hfc
  rw [et] at hm
  exact eq_mp_rev hm (by eq_omega)

private theorem init_three_short :
    ∃ r, CutNum true 218 1 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 16) +> ([0] +> ((X ^ 2) +> ([0, 0] +> ((X ^ 20) +> ([0] +> (Y +> r))))))))) :=
          by
  obtain ⟨r, hn, hr⟩ := init_three_column
  obtain ⟨s, hs, h6⟩ := CutNum_Fs 6 true 193 0 r hn (by omega)
  have hc : CutNum true 199 1 ((X ^ 5) +> s) :=
    CutNum_prepend true 199 1 5 s hs
  obtain ⟨t, ht, h19⟩ := CutNum_hs 19 true 199 1 _ hc (by omega)
  have h39 :
    SideRLs tm40 (h ^ 39) (X +> ([0, 0] +> ((X ^ 5) +> s))) ((X ^ 20) +> ([0] +> (Y +> t))) :=
    h_even_batch_side 19 0 ((X ^ 5) +> s) t h19
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (three_even3 1 40 r s h6)) ?_
  exact eq_mp_rev (marker_hcalls 13 2 1 _ _ h39) (by eq_omega)

private theorem init_three_return :
    ∃ r, CutNum true 243 1 r ∧
      ((init []) [tm40]⊢* (root (X +> ([0, 0, 0] +> ((X ^ 14) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_three_short
  obtain ⟨s, hs, h25⟩ := CutNum_hs 25 true 218 1 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (a2_double_odd 7 12 r s h25))⟩

private theorem init_O262 :
    ∃ r, Num true 262 r ∧ ((init []) [tm40]⊢* (root r)) := by
  obtain ⟨r, hn, hr⟩ := init_three_return
  obtain ⟨s, hs, h12⟩ := CutNum_hs 12 true 243 1 r hn (by omega)
  obtain ⟨r6, h6, h6'⟩ := sideRLs_pow_split 6 6 h12 (by omega)
  have hf1 : SideRLs tm40 (hf ^ 12) ((X ^ 13) +> ([0, 0] +> r)) ((X ^ 7) +> ([0, 0] +> r6)) :=
    F_pairs_even_side 6 7 r r6 h6
  have hf' : SideRLs tm40 (hf ^ 12) ((X ^ 7) +> ([0, 0] +> r6)) (X +> ([0, 0] +> s)) :=
    F_pairs_even_side 6 1 r6 s h6'
  obtain ⟨t, ht, h7⟩ := CutNum_Fs 7 true 255 1 s hs (by omega)
  refine ⟨(X ^ 8) +> t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev (a2_cleanup _ _ hf1) (by eq_omega))) ?_
  refine ReachesStar.trans (eq_mp_rev (two_markers 1 1 _ _ hf') (by eq_omega)) ?_
  exact ReachesPlus.to_star (two_even2 2 s t h7)

private theorem init_O522 :
    ∃ r, Num true 522 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 88) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_O262
  obtain ⟨s, hs, es⟩ := Num_O_even_inv 129 _ hn
  obtain ⟨t, ht, h393⟩ := Num_add 393 false 129 s hs
  obtain ⟨u, hu, eu⟩ := Num_E_even_inv 261 _ ht
  obtain ⟨v, hv, h261⟩ := Num_add 261 true 261 u hu
  refine ⟨v, hv, ?_⟩
  rw [es] at hr
  refine ReachesStar.trans hr ?_
  have hn130 := normal_calls 130 s t h393
  rw [eu] at hn130
  exact ReachesStar.trans (ReachesPlus.to_star hn130)
    (eq_mp_rev (marker_hcalls 87 0 1 u v h261) (by eq_omega))

private theorem init_two_odd3 :
    ∃ r, Num false 607 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 37) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_O522
  obtain ⟨s, hs, hrs⟩ := CutNum_a2 86 true 522 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 391 _ hs
  have es : s = (X ^ 219) +> ([0] +> (Y +> t)) :=
    cut_prefix 394 175 s ([0] +> (Y +> t)) (by omega) et
  obtain ⟨u, hu, h216⟩ := Num_add 216 false 391 t ht
  have hf :
    SideRLs tm40 (hf ^ 432) ((X ^ 218) +> ([0] +> (Y +> t))) ((X ^ 2) +> ([0] +> (Y +> u))) :=
    F_pairs_odd_side 216 2 t u h216
  obtain ⟨v, h12, h420⟩ := sideRLs_pow_split 12 420 hf (by omega)
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev (a2_cleanup _ _ h12) (by eq_omega))) ?_
  exact eq_mp_rev (two_markers 35 1 v _ h420) (by eq_omega)

private theorem init_triple_Y :
    ∃ r, Num false 610 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 37) +> ([0] +> (Y +> (Y +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_odd3
  obtain ⟨s, hs, h3⟩ := Num_add 3 false 607 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (two_odd3 35 r s h3))⟩

private theorem init_three_column_again :
    ∃ r, Num true 609 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 8) +>
          ([0] +> ((X ^ 111) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_triple_Y
  obtain ⟨r8, hn8, h8⟩ := CutNum_Fs 8 false 610 0 r hn (by omega)
  obtain ⟨s, hs, h432⟩ := CutNum_Fs 432 false 618 8 r8 hn8 (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 525 _ hs
  have es : s = (X ^ 86) +> ([0, 0] +> t) :=
    cut_prefix 526 440 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h84⟩ := Num_add 84 true 525 t ht
  have hf : SideRLs tm40 (hf ^ 168) s ((X ^ 2) +> ([0, 0] +> u)) := by
    rw [es]
    exact F_pairs_even_side 84 2 t u h84
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (triple_Y_return 35 r r8 h8)) ?_
  have hh108 := h_columns [0] 108 2 r8 s h432
  try dsimp only [markers] at hh108
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 35 _ _ hh108)) ?_
  have hfc := F_columns [110, 0] 42 s _ hf
  try dsimp only [markers] at hfc
  exact eq_mp_rev (marker_calls 7 0 _ _ hfc) (by eq_omega)

private theorem init_large_a1 :
    ∃ r, CutNum true 737 1 r ∧
      ((init []) [tm40]⊢* (root (X +> ([0] +> ((X ^ 34) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_three_column_again
  obtain ⟨s, hs, h6⟩ := CutNum_Fs 6 true 609 0 r hn (by omega)
  have hc : CutNum true 615 1 ((X ^ 5) +> s) :=
    CutNum_prepend true 615 1 5 s hs
  obtain ⟨t, ht, h54⟩ := CutNum_hs 54 true 615 1 _ hc (by omega)
  have h108 :
    SideRLs tm40 (h ^ 108) (X +> ([0, 0] +> ((X ^ 5) +> s))) ((X ^ 55) +> ([0, 0] +> t)) :=
    h_pairs_even_side 54 0 ((X ^ 5) +> s) t h54
  obtain ⟨u, hu, h68⟩ := CutNum_hs 68 true 669 1 t ht (by omega)
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (three_even3 7 108 r s h6)) ?_
  refine ReachesStar.trans (eq_mp_rev (marker_hcalls 36 8 0 _ _ h108) (by eq_omega)) ?_
  exact ReachesPlus.to_star (a1_double_digit 22 31 t u h68)

private theorem init_E779 :
    ∃ r, Num false 779 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 127) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_large_a1
  obtain ⟨s, hs, h33⟩ := CutNum_hs 33 true 737 1 r hn (by omega)
  obtain ⟨t, ht, hp⟩ := Num_pending 11 ([1] +> default) true 770 1 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_O_even_inv 401 _ ht
  have et : t = (X ^ 379) +> ([0, 0] +> u) :=
    cut_prefix 404 25 t ([0, 0] +> u) (by omega) eu
  obtain ⟨v, hv, h378⟩ := Num_add 378 false 401 u hu
  have hf : SideRLs tm40 (hf ^ 756) ((X ^ 379) +> ([0] +> (Y +> u))) (X +> ([0] +> (Y +> v))) :=
    F_pairs_odd_side 378 1 u v h378
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (eq_mp_rev (marker_hcalls 11 0 0 r s h33) (by eq_omega)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star (a1_prepare 11 s)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  rw [et]
  refine ReachesStar.trans (ReachesPlus.to_star (a1_even_finish 379 u)) ?_
  exact eq_mp_rev (marker_calls 126 0 _ _ hf) (by eq_omega)

private theorem init_O770 :
    ∃ r, Num true 770 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 381) +> ([0] +> ((X ^ 12) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_E779
  obtain ⟨s, hs, hrs⟩ := CutNum_birth 126 false 779 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 770 _ hs
  have es : s = (X ^ 12) +> ([0] +> (Y +> t)) :=
    cut_prefix 771 759 s ([0] +> (Y +> t)) (by omega) et
  refine ⟨t, ht, ?_⟩
  rw [es] at hrs
  exact ReachesStar.trans hr (ReachesPlus.to_star hrs)

private theorem init_two_odd6 :
    ∃ r, Num true 776 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 2) +> ([0] +> ((X ^ 381) +> ([0] +> ((X ^ 6) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_O770
  obtain ⟨s, hs, h6⟩ := Num_add 6 true 770 r hn
  have hf : SideRLs tm40 (hf ^ 12) ((X ^ 11) +> ([0] +> (Y +> r))) ((X ^ 5) +> ([0] +> (Y +> s))) :=
    F_pairs_odd_side 6 5 r s h6
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (marker_calls 1 0 _ _ (F_markers 6 380 _ _ hf)) (by eq_omega)

private theorem init_second_Y :
    ∃ r, Num true 782 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 3) +> ([0] +> ((X ^ 381) +> ([0, 0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_odd6
  obtain ⟨s, hs, h6⟩ := Num_add 6 true 776 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (two_odd6 1 380 r s h6))⟩

private theorem init_nested_a3 :
    ∃ r, Num false 767 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 129) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> ((X ^ 378) +> ([0] +> ((X ^ 15) +> ([0, 0] +> r))))))))))
          := by
  obtain ⟨r, hn, hr⟩ := init_second_Y
  obtain ⟨s, hs, h756⟩ := CutNum_Fs 756 true 782 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 767 _ hs
  have es : s = (X ^ 14) +> ([0, 0] +> t) :=
    cut_prefix 770 756 s ([0, 0] +> t) (by omega) et
  refine ⟨t, ht, ?_⟩
  have hm := marker_hcalls 126 2 2 _ _ (Y_hs 377 r s h756)
  rw [es] at hm
  exact star_trans_eq hr hm (by eq_omega)

-- ============================================================================
-- 5c. Batch 3 (`Others_v2.v` lines 1803–2680: `init_nested_a3_pending` through
-- `init_final_marked_even`)
-- ============================================================================

private theorem init_nested_a3_pending :
    ∃ r, Num false 781 r ∧
      ((init []) [tm40]⊢*
        (pending 124 ([1, 1] +> default) ((X ^ 384) +> ([0] +> (X +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_a3
  obtain ⟨s, hs, h2⟩ := Num_add 2 false 767 r hn
  have hf : SideRLs tm40 (hf ^ 4) ((X ^ 14) +> ([0, 0] +> r)) ((X ^ 12) +> ([0, 0] +> s)) :=
    F_pairs_even_side 2 12 r s h2
  obtain ⟨t, ht, h12⟩ := Num_add 12 false 769 s hs
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  have hh2 := h_columns [] 2 378 _ _ hf
  try dsimp only [markers] at hh2
  refine ReachesStar.trans
    (ReachesPlus.to_star (eq_mp_rev (a3_prepare 128 _ _ hh2) (by eq_omega))) ?_
  exact eq_mp_rev (pending_marker_cycles 4 124 379 0 ([1, 1] +> default) s t h12) (by eq_omega)

private theorem init_double_odd :
    ∃ r, Num true 969 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 125) +> ([0] +> (Y +> ((X ^ 199) +> ([0] +> (Y +> r))))))))
        := by
  obtain ⟨r, hn, hr⟩ := init_nested_a3_pending
  obtain ⟨s, hs, hp⟩ :=
    Num_pending 383 (Kr +> ((Dr ^ 124) +> ([1, 1] +> default))) false 781 0 r hn (by omega)
  obtain ⟨t, ht, h6⟩ := CutNum_Fs 6 false 1933 768 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_odd_inv 969 _ ht
  have et : t = (X ^ 196) +> ([0] +> (Y +> u)) :=
    cut_prefix 970 774 t ([0] +> (Y +> u)) (by omega) eu
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (pending_marker_one 124 383 ([1, 1] +> default) r)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  have hk := marked_K_root 124 s t h6
  rw [et] at hk
  exact ReachesPlus.to_star (eq_mp_rev hk (by eq_omega))

private theorem init_O1543 :
    ∃ r, Num true 1543 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 130) +> ([0, 0] +> (Y +> r))))) := by
  obtain ⟨r, hn, hr⟩ := init_double_odd
  obtain ⟨s, hs, h187⟩ := Num_add 187 true 969 r hn
  have h374 :
    SideRLs tm40 (h ^ 374) ((X ^ 199) +> ([0] +> (Y +> r))) ((X ^ 386) +> ([0] +> (Y +> s))) :=
    h_pairs_odd_side 187 199 r s h187
  obtain ⟨r2, h2, h372⟩ := sideRLs_pow_split 2 372 h374 (by omega)
  obtain ⟨t, ht, h384⟩ := Num_add 384 true 1156 s hs
  have hf :
    SideRLs tm40 (hf ^ 768) ((X ^ 386) +> ([0] +> (Y +> s))) ((X ^ 2) +> ([0] +> (Y +> t))) :=
    F_pairs_odd_side 384 2 s t h384
  obtain ⟨u, hu, h3⟩ := Num_add 3 true 1540 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_odd 123 _ _ h2)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 123 _ _ h372)) ?_
  refine ReachesStar.trans (eq_mp_rev (marker_calls 128 0 _ _ hf) (by eq_omega)) ?_
  exact ReachesPlus.to_star (odd_three 128 t u h3)

private theorem init_E1540 :
    ∃ r, Num false 1540 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 65) +> ([0] +> ((X ^ 388) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_O1543
  obtain ⟨s, hs, h774⟩ := CutNum_Fs 774 true 1543 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 1156 _ hs
  have es : s = (X ^ 385) +> ([0] +> (Y +> t)) :=
    cut_prefix 1159 774 s ([0] +> (Y +> t)) (by omega) et
  obtain ⟨u, hu, h384⟩ := Num_add 384 false 1156 t ht
  have hf : SideRLs tm40 (hf ^ 768) s (X +> ([0] +> (Y +> u))) := by
    rw [es]
    exact F_pairs_odd_side 384 1 t u h384
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 128 _ _ (Y_hs 386 r s h774))) ?_
  exact eq_mp_rev (marker_calls 64 0 _ _ (F_markers 384 387 s _ hf)) (by eq_omega)

private theorem init_large_nested_a2 :
    ∃ r, Num true 1157 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 194) +>
          ([0] +> ((X ^ 2) +> ([0, 0] +> ((X ^ 386) +> ([0] +> ((X ^ 387) +> ([0, 0] +> r))))))))))
          := by
  obtain ⟨r, hn, hr⟩ := init_E1540
  obtain ⟨s, hs, hrs⟩ := CutNum_odd2_pair 64 385 false 1540 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 773 _ hs
  have es : s = (X ^ 771) +> ([0, 0] +> t) :=
    cut_prefix 774 3 s ([0, 0] +> t) (by omega) et
  have hc : CutNum false 1546 4 ((X ^ 770) +> ([0, 0] +> t)) :=
    CutNum_E_even ht (by omega)
  obtain ⟨u, hu, h768⟩ := CutNum_Fs 768 false 1546 4 _ hc (by omega)
  obtain ⟨v, hv, ev⟩ := Num_E_even_inv 1157 _ hu
  have eu : u = (X ^ 386) +> ([0, 0] +> v) :=
    cut_prefix 1158 772 u ([0, 0] +> v) (by omega) ev
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  have hh384 := h_columns [] 384 2 _ _ h768
  try dsimp only [markers] at hh384
  have hm := marker_hcalls 128 65 1 _ _ hh384
  rw [eu] at hm
  exact eq_mp_rev hm (by eq_omega)

private theorem init_large_pending_J :
    ∃ r, Num true 1542 r ∧
      ((init []) [tm40]⊢*
        (pending 64 ([1, 1, 0, 1, 1, 1] +> default)
          ((X ^ 515) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_large_nested_a2
  have hc : CutNum false 2314 772 ((X ^ 386) +> ([0, 0] +> r)) :=
    CutNum_E_even hn (by omega)
  obtain ⟨s, hs, h2⟩ := CutNum_Fs 2 false 2314 772 _ hc (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 1158 _ hs
  have es : s = (X ^ 385) +> ([0, 0] +> t) :=
    cut_prefix 1159 774 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h384⟩ := Num_add 384 true 1158 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  have hh1 := h_columns [] 1 386 _ _ h2
  try dsimp only [markers] at hh1
  have ha2 := a2_prepare 192 _ _ hh1
  rw [es] at ha2
  exact ReachesStar.trans (ReachesPlus.to_star ha2)
    (eq_mp_rev (pending_marker_cycles 128 64 386 1 ([1, 1, 0, 1, 1, 1] +> default) t u h384)
      (by eq_omega))

private theorem init_large_after_J :
    ∃ r, Num false 1547 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 66) +> ([0] +> (X +> ([0] +> ((X ^ 513) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_large_pending_J
  obtain ⟨s, hs, h1⟩ := Num_add 1 true 1542 r hn
  obtain ⟨t, ht, hp⟩ :=
    Num_pending 514 (Jr +> ((Dr ^ 64) +> ([1, 1, 0, 1, 1, 1] +> default))) true 1543 0 s hs
    (by omega)
  obtain ⟨u, hu, h10⟩ := CutNum_Fs 10 true 3088 1030 t ht (by omega)
  obtain ⟨v, hv, ev⟩ := Num_O_even_inv 1547 _ hu
  have eu : u = (X ^ 510) +> ([0, 0] +> v) :=
    cut_prefix 1550 1040 u ([0, 0] +> v) (by omega) ev
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (pending_marker_short 64 514 ([1, 1, 0, 1, 1, 1] +> default) r s h1)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  have hj := marked_J_root 63 t u h10
  rw [eu] at hj
  exact ReachesPlus.to_star (eq_mp_rev hj (by eq_omega))

private theorem init_two_even3 :
    ∃ r, Num false 2057 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 151) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_large_after_J
  obtain ⟨s, hs, h510⟩ := Num_add 510 false 1547 r hn
  have hf : SideRLs tm40 (hf ^ 1020) ((X ^ 512) +> ([0, 0] +> r)) ((X ^ 2) +> ([0, 0] +> s)) :=
    F_pairs_even_side 510 2 r s h510
  refine ⟨s, hs, ?_⟩
  exact star_trans_eq hr (two_markers 85 65 _ _ hf) (by eq_omega)

private theorem init_E2513 :
    ∃ r, CutNum false 2513 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 76) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_even3
  obtain ⟨s, hs, h5⟩ := CutNum_Fs 5 false 2057 0 r hn (by omega)
  have hc : CutNum false 2062 1 ((X ^ 4) +> s) :=
    CutNum_prepend false 2062 1 4 s hs
  obtain ⟨t, ht, h1⟩ := CutNum_hs 1 false 2062 1 _ hc (by omega)
  obtain ⟨u, hu, h225⟩ := CutNum_hs 225 false 2063 1 t ht (by omega)
  have h450 : SideRLs tm40 (h ^ 450) (X +> ([0, 0] +> t)) ((X ^ 226) +> ([0, 0] +> u)) :=
    h_pairs_even_side 225 0 t u h225
  obtain ⟨v, hv, hlast⟩ := CutNum_hs 225 false 2288 1 u hu (by omega)
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (two_even3 149 r s h5)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star (odd_zero_return 149 ((X ^ 4) +> s) t h1)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 149 _ _ h450)) ?_
  exact eq_mp_rev (marker_hcalls 75 0 1 u v hlast) (by eq_omega)

private theorem init_two_even2_large :
    ∃ r, Num true 2589 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 204) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_E2513
  obtain ⟨s, hs, hrs⟩ := CutNum_a2 74 false 2513 1 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 1371 _ hs
  have es : s = (X ^ 1220) +> ([0, 0] +> t) :=
    cut_prefix 1372 152 s ([0, 0] +> t) (by omega) et
  have hc : CutNum false 2742 153 ((X ^ 1219) +> ([0, 0] +> t)) :=
    CutNum_E_even ht (by omega)
  obtain ⟨u, hu, h12⟩ := CutNum_Fs 12 false 2742 153 _ hc (by omega)
  obtain ⟨v, hv, ev⟩ := Num_E_even_inv 1377 _ hu
  have eu : u = (X ^ 1213) +> ([0, 0] +> v) :=
    cut_prefix 1378 165 u ([0, 0] +> v) (by omega) ev
  obtain ⟨w, hw, h1212⟩ := Num_add 1212 true 1377 v hv
  have hf : SideRLs tm40 (hf ^ 2424) u (X +> ([0, 0] +> w)) := by
    rw [eu]
    exact F_pairs_even_side 1212 1 v w h1212
  refine ⟨w, hw, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev (a2_cleanup _ u h12) (by eq_omega))) ?_
  exact eq_mp_rev (two_markers 202 1 u _ hf) (by eq_omega)

private theorem init_O5796 :
    ∃ r, Num true 5796 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 967) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_two_even2_large
  obtain ⟨s, hs, h7⟩ := CutNum_Fs 7 true 2589 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 1296 _ hs
  have es : s = (X ^ 1292) +> ([0, 0] +> t) :=
    cut_prefix 1299 7 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h4500⟩ := Num_add 4500 false 1296 t ht
  obtain ⟨v, hv, ev⟩ := Num_E_even_inv 2898 _ hu
  obtain ⟨w, hw, h2898⟩ := Num_add 2898 true 2898 v hv
  refine ⟨w, hw, ?_⟩
  refine ReachesStar.trans hr ?_
  have hte := two_even2 203 r s h7
  rw [es] at hte
  refine ReachesStar.trans (ReachesPlus.to_star hte) ?_
  have hn1499 := normal_calls 1499 t u h4500
  rw [ev] at hn1499
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev hn1499 (by eq_omega))) ?_
  exact eq_mp_rev (marker_hcalls 966 0 1 v w h2898) (by eq_omega)

private theorem init_two_even5 :
    ∃ r, Num false 6759 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 403) +> ([0] +> (X +> ([0] +> ((X ^ 5) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_O5796
  obtain ⟨s, hs, hrs⟩ := CutNum_a2 965 true 5796 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 4347 _ hs
  have es : s = (X ^ 2417) +> ([0, 0] +> t) :=
    cut_prefix 4350 1933 s ([0, 0] +> t) (by omega) et
  have hc : CutNum true 8698 1934 ((X ^ 2416) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨u, hu, h12⟩ := CutNum_Fs 12 true 8698 1934 _ hc (by omega)
  obtain ⟨v, hv, ev⟩ := Num_O_even_inv 4353 _ hu
  have eu : u = (X ^ 2410) +> ([0, 0] +> v) :=
    cut_prefix 4356 1946 u ([0, 0] +> v) (by omega) ev
  obtain ⟨w, hw, h2406⟩ := Num_add 2406 false 4353 v hv
  have hf : SideRLs tm40 (hf ^ 4812) u ((X ^ 4) +> ([0, 0] +> w)) := by
    rw [eu]
    exact F_pairs_even_side 2406 4 v w h2406
  refine ⟨w, hw, ?_⟩
  refine ReachesStar.trans hr (ReachesStar.trans (ReachesPlus.to_star hrs) ?_)
  rw [es]
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev (a2_cleanup _ u h12) (by eq_omega))) ?_
  exact eq_mp_rev (two_markers 401 1 u _ hf) (by eq_omega)

private theorem init_zero4 :
    ∃ r, CutNum false 6766 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 404) +> ([0, 0, 0, 0] +> r)))) := by
  obtain ⟨r, hn, hr⟩ := init_two_even5
  obtain ⟨s, hs, h7⟩ := CutNum_Fs 7 false 6759 0 r hn (by omega)
  refine ⟨(X ^ 6) +> s, CutNum_prepend false 6766 1 6 s hs, ?_⟩
  exact ReachesStar.trans hr (ReachesPlus.to_star (two_even5 402 r s h7))

private theorem init_birth_E7973 :
    ∃ r, CutNum false 7973 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 202) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_zero4
  obtain ⟨s, hs, h1⟩ := CutNum_hs 1 false 6766 1 r hn (by omega)
  obtain ⟨t, ht, h603⟩ := CutNum_hs 603 false 6767 1 s hs (by omega)
  have h1206 : SideRLs tm40 (h ^ 1206) (X +> ([0] +> (Y +> s))) ((X ^ 604) +> ([0] +> (Y +> t))) :=
    h_pairs_odd_side 603 1 s t h603
  obtain ⟨u, hu, hlast⟩ := CutNum_hs 603 false 7370 1 t ht (by omega)
  have hf : SideRLs tm40 (hf ^ 1206) ((X ^ 604) +> ([0] +> (Y +> t))) (X +> ([0] +> (Y +> u))) :=
    F_pairs_odd_side 603 1 t u hlast
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (zero4_prepare 401 r s h1)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_calls 401 _ _ h1206)) ?_
  exact eq_mp_rev (marker_calls 201 0 _ _ hf) (by eq_omega)

private theorem init_O4592 :
    ∃ r, Num true 4592 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 606) +> ([0] +> ((X ^ 3383) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_birth_E7973
  obtain ⟨s, hs, hrs⟩ := CutNum_birth 201 false 7973 1 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 4592 _ hs
  have es : s = (X ^ 3383) +> ([0] +> (Y +> t)) :=
    cut_prefix 4593 1210 s ([0] +> (Y +> t)) (by omega) et
  refine ⟨t, ht, ?_⟩
  rw [es] at hrs
  exact ReachesStar.trans hr (ReachesPlus.to_star hrs)

private theorem init_long_YY :
    ∃ r, Num true 7975 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 565) +> ([0] +> ((X ^ 605) +> ([0] +> (Y +> (Y +> r))))))))
        := by
  obtain ⟨r, hn, hr⟩ := init_O4592
  obtain ⟨s, hs, h3378⟩ := Num_add 3378 true 4592 r hn
  have hf :
    SideRLs tm40 (hf ^ 6756) ((X ^ 3382) +> ([0] +> (Y +> r))) ((X ^ 4) +> ([0] +> (Y +> s))) :=
    F_pairs_odd_side 3378 4 r s h3378
  obtain ⟨t, ht, h5⟩ := Num_add 5 true 7970 s hs
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (eq_mp_rev (marker_calls 563 0 _ _ (F_markers 3378 605 _ _ hf)) (by eq_omega)) ?_
  exact ReachesPlus.to_star (odd_five_general 563 605 s t h5)

private theorem init_nested_birth :
    ∃ r, Num false 4588 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 766) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +>
          ((X ^ 603) +> ([0] +> ((X ^ 3386) +> ([0] +> (Y +> r)))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_long_YY
  obtain ⟨s, hs, h1206⟩ := CutNum_Fs 1206 true 7975 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 4588 _ hs
  have es : s = (X ^ 3385) +> ([0] +> (Y +> t)) :=
    cut_prefix 4591 1206 s ([0] +> (Y +> t)) (by omega) et
  have hf : SideRLs tm40 (hf ^ 1206)
      ((X ^ 604) +> ([0] +> (Y +> (Y +> r))))
      (X +> ([0] +> (Y +> ((X ^ 603) +> ([0] +> (X +> s)))))) :=
    eq_mp_rev (F_pairs_odd_side 603 1 _ _ (Y_hs 602 r s h1206)) (by eq_omega)
  refine ⟨t, ht, ?_⟩
  have hm := marker_calls 201 564 _ _ hf
  rw [es] at hm
  exact star_trans_eq hr hm (by eq_omega)

private theorem init_nested_birth_short :
    ∃ r, Num false 7969 r ∧
      ((init []) [tm40]⊢*
        (birth 203 1690 ((X ^ 603) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_birth
  obtain ⟨s, hs, h3⟩ := Num_add 3 false 4588 r hn
  have hf6 :
    SideRLs tm40 (hf ^ 6) ((X ^ 3385) +> ([0] +> (Y +> r))) ((X ^ 3382) +> ([0] +> (Y +> s))) :=
    F_pairs_odd_side 3 3382 r s h3
  obtain ⟨t, ht, h3378⟩ := Num_add 3378 false 4591 s hs
  have hf6756 :
    SideRLs tm40 (hf ^ 6756) ((X ^ 3382) +> ([0] +> (Y +> s))) ((X ^ 4) +> ([0] +> (Y +> t))) :=
    F_pairs_odd_side 3378 4 s t h3378
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  have hbp := birth_prepare 765 _ _ (F_markers 3 603 _ _ hf6)
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev hbp (by eq_omega))) ?_
  exact eq_mp_rev (birth_cycles 563 202 0 _ _ (F_markers 3378 603 _ _ hf6756)) (by eq_omega)

private theorem init_nested_return :
    ∃ r, Num false 7972 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 203) +> ([0, 0] +> ((X ^ 1691) +> ([0] +>
          ((X ^ 606) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_birth_short
  obtain ⟨s, hs, h3⟩ := Num_add 3 false 7969 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star (birth_marker_five 201 1689 602 r s h3))⟩

private theorem init_nested_spill :
    ∃ r, CutNum false 7978 3 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 202) +> ([0, 0] +> ((X ^ 1694) +> ([0] +>
          ((X ^ 604) +> ([0, 0] +> ((X ^ 2) +> ([0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_return
  obtain ⟨s, hs, h6⟩ := CutNum_Fs 6 false 7972 0 r hn (by omega)
  refine ⟨(X ^ 3) +> s, CutNum_prepend false 7978 3 3 s hs, ?_⟩
  exact ReachesStar.trans hr (ReachesPlus.to_star (normal_odd2_spill 200 1690 603 r s h6))

private theorem init_even_exhaustion :
    ∃ r, CutNum false 9184 1209 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 2298) +> ([0] +> (X +> ([0, 0] +>
          ((X ^ 605) +> ([0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_spill
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 3989 _ hn
  have er : r = (X ^ 3987) +> ([0, 0] +> t) :=
    cut_prefix 3990 3 r ([0, 0] +> t) (by omega) et
  have hc : CutNum false 7978 4 ((X ^ 3986) +> ([0, 0] +> t)) :=
    CutNum_E_even ht (by omega)
  obtain ⟨s, hs, h1206⟩ := CutNum_Fs 1206 false 7978 4 _ hc (by omega)
  have hh603 := h_columns [] 603 2 _ _ h1206
  try dsimp only [markers] at hh603
  have hf : SideRLs tm40 (hf ^ 1206)
      ((X ^ 603) +> ([0, 0] +> ((X ^ 2) +> ([0] +> ((X ^ 3987) +> ([0, 0] +> t))))))
      ([0, 0] +> ((X ^ 605) +> ([0] +> (X +> s)))) :=
    eq_mp_rev (F_pairs_even_side 603 0 _ _ hh603) (by eq_omega)
  refine ⟨X +> s, ?_, ?_⟩
  · exact CutNum_prepend false 9184 1209 1 s (CutNum_cast (by omega) (by omega) hs)
  · rw [er] at hr
    have hh_top := h_columns [] 603 1694 _ _ hf
    try dsimp only [markers] at hh_top
    exact star_trans_eq hr (ReachesPlus.to_star (normal_calls 200 _ _ hh_top)) (by eq_omega)

private theorem init_mixed_return :
    ∃ r, CutNum true 13180 3469 r ∧
      ((init []) [tm40]⊢* (root ([0] +> (X +> ([0] +> ((X ^ 1169) +> ([0] +> (Y +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_even_exhaustion
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 4592 _ hn
  have er : r = (X ^ 3384) +> ([0, 0] +> t) :=
    cut_prefix 4593 1209 r ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h3381⟩ := Num_add 3381 true 4592 t ht
  obtain ⟨v, hv, h2⟩ := Num_add 2 true 7973 u hu
  obtain ⟨s, hs, hp⟩ :=
    Num_pending 1731 (Lr +> ((Dr ^ 1169) +> (Wr +> default))) true 7975 0 v hv (by omega)
  obtain ⟨w, hw, h9⟩ := CutNum_Fs 9 true 13171 3464 s hs (by omega)
  refine ⟨(X ^ 4) +> w, CutNum_prepend true 13180 3469 4 w hw, ?_⟩
  rw [er] at hr
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star
    (nested_even_prepare 2296 ((X ^ 605) +> ([0] +> ((X ^ 3384) +> ([0, 0] +> t)))))) ?_
  refine ReachesStar.trans
    (eq_mp_rev (pending_marker_cycles 1127 1169 604 2 (Wr +> default) t u h3381) (by eq_omega)) ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (pending_marker_prepare 1169 1731 (Wr +> default) u v h2)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (marked_F_finish ((Dr ^ 1169) +> (Wr +> default)) s w h9)) ?_
  exact ReachesPlus.to_star (W_root_cleanup 1169 ((X ^ 4) +> w))

private theorem init_post_mixed_odd3 :
    ∃ r, Num false 7171 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 390) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +>
          ((X ^ 3705) +> ([0, 0] +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_mixed_return
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 6588 _ hn
  have er : r = (X ^ 3122) +> ([0, 0] +> t) :=
    cut_prefix 6591 3469 r ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h1⟩ := Num_add 1 false 6588 t ht
  have hf4 : SideRLs tm40 (hf ^ 4)
      ((X ^ 1168) +> ([0] +> (Y +> ((X ^ 3122) +> ([0, 0] +> t)))))
      ((X ^ 1166) +> ([0] +> (Y +> ((X ^ 3123) +> ([0, 0] +> u))))) :=
    F_pairs_odd_side 2 1166 _ _ (h_pairs_even_side 1 3121 t u h1)
  obtain ⟨v, hv, h582⟩ := Num_add 582 false 6589 u hu
  have hf : SideRLs tm40 (hf ^ 2328)
      ((X ^ 1166) +> ([0] +> (Y +> ((X ^ 3123) +> ([0, 0] +> u)))))
      ((X ^ 2) +> ([0] +> (Y +> ((X ^ 3705) +> ([0, 0] +> v))))) :=
    F_pairs_odd_side 1164 2 _ _ (h_pairs_even_side 582 3122 u v h582)
  refine ⟨v, hv, ?_⟩
  rw [er] at hr
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (eq_mp_rev (marker_second_half 0 _ _ hf4) (by eq_omega))) ?_
  exact eq_mp_rev (marker_calls 388 1 _ _ hf) (by eq_omega)

private theorem init_post_mixed_Y :
    ∃ r, CutNum true 14355 3474 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 390) +> ([0, 0] +> ((X ^ 3) +> ([0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_post_mixed_odd3
  obtain ⟨s, hs, h1⟩ := Num_add 1 false 7171 r hn
  have h3 : SideRLs tm40 (h ^ 3) ((X ^ 3705) +> ([0, 0] +> r)) ((X ^ 3706) +> ([0] +> (Y +> s))) :=
    h_even_batch_side 1 3704 r s h1
  obtain ⟨t, ht, hlast⟩ := Num_add 3 false 7172 s hs
  have hf :
    SideRLs tm40 (hf ^ 6) ((X ^ 3706) +> ([0] +> (Y +> s))) ((X ^ 3703) +> ([0] +> (Y +> t))) :=
    F_pairs_odd_side 3 3703 s t hlast
  refine ⟨(X ^ 3704) +> ([0] +> (Y +> t)), ?_, ?_⟩
  · exact CutNum_O_odd ht (by omega)
  · refine ReachesStar.trans hr ?_
    refine ReachesStar.trans (ReachesPlus.to_star (odd_three 389 _ _ h3)) ?_
    exact ReachesPlus.to_star (eq_mp_rev (normal_cycle 388 _ _ (Y_hs 2 _ _ hf)) (by eq_omega))

private theorem init_post_mixed_markers :
    ∃ r, Num false 10874 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 423) +> ([0] +> ((X ^ 1171) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))))) :=
        by
  obtain ⟨r, hn, hr⟩ := init_post_mixed_Y
  obtain ⟨t, ht, et⟩ := Num_O_odd_inv 7175 _ hn
  have er : r = (X ^ 3704) +> ([0] +> (Y +> t)) :=
    cut_prefix 7178 3474 r ([0] +> (Y +> t)) (by omega) et
  have hc : CutNum true 14355 3475 ((X ^ 3703) +> ([0] +> (Y +> t))) :=
    CutNum_O_odd ht (by omega)
  obtain ⟨s, hs, h2334⟩ := CutNum_Fs 2334 true 14355 3475 _ hc (by omega)
  obtain ⟨u, hu, eu⟩ := Num_O_odd_inv 8342 _ hs
  have es : s = (X ^ 2536) +> ([0] +> (Y +> u)) :=
    cut_prefix 8345 5809 s ([0] +> (Y +> u)) (by omega) eu
  obtain ⟨v, hv, h2532⟩ := Num_add 2532 false 8342 u hu
  have hf :
    SideRLs tm40 (hf ^ 5064) ((X ^ 2536) +> ([0] +> (Y +> u))) ((X ^ 4) +> ([0] +> (Y +> v))) :=
    F_pairs_odd_side 2532 4 u v h2532
  refine ⟨v, hv, ?_⟩
  rw [er] at hr
  refine ReachesStar.trans hr ?_
  have hh1167 := h_columns [] 1167 3 _ s h2334
  try dsimp only [markers] at hh1167
  have hn388 := normal_calls 388 _ _ hh1167
  rw [es] at hn388
  refine ReachesStar.trans (ReachesPlus.to_star (eq_mp_rev hn388 (by eq_omega))) ?_
  exact eq_mp_rev (marker_calls 422 0 _ _ (F_markers 2532 1170 _ _ hf)) (by eq_omega)

private theorem init_post_mixed_T :
    ∃ r, CutNum false 10885 5 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 425) +> ([0] +> ((X ^ 1167) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> r))))))))) :=
          by
  obtain ⟨r, hn, hr⟩ := init_post_mixed_markers
  obtain ⟨s, hs, h5⟩ := Num_add 5 false 10874 r hn
  obtain ⟨t, ht, h6⟩ := CutNum_Fs 6 false 10879 0 s hs (by omega)
  refine ⟨X +> t, CutNum_prepend false 10885 5 1 t (CutNum_cast (by omega) (by omega) ht), ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (odd_five_general 422 1170 r s h5)) ?_
  exact ReachesPlus.to_star (marker_T_cycle 423 1166 s t h6)

private theorem init_post_T_odd3 :
    ∃ r, CutNum false 13213 2333 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 813) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> ((X ^ 1167) +> ([0] +> r))))))))) :=
          by
  obtain ⟨r, hn, hr⟩ := init_post_mixed_T
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 5442 _ hn
  have er : r = (X ^ 5438) +> ([0] +> (Y +> t)) :=
    cut_prefix 5443 5 r ([0] +> (Y +> t)) (by omega) et
  have hc : CutNum false 10885 6 ((X ^ 5437) +> ([0] +> (Y +> t))) :=
    CutNum_E_odd ht (by omega)
  obtain ⟨s, hs, h2328⟩ := CutNum_Fs 2328 false 10885 6 _ hc (by omega)
  have hh1164 := h_columns [] 1164 3 _ s h2328
  try dsimp only [markers] at hh1164
  have hf : SideRLs tm40 (hf ^ 2328)
      ((X ^ 1166) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> ((X ^ 5438) +> ([0] +> (Y +> t))))))))
      ((X ^ 2) +> ([0] +> (Y +> ((X ^ 1167) +> ([0] +> (X +> s)))))) :=
    eq_mp_rev (F_pairs_odd_side 1164 2 _ _ hh1164) (by eq_omega)
  refine ⟨X +> s, CutNum_prepend false 13213 2333 1 s (CutNum_cast (by omega) (by omega) hs), ?_⟩
  rw [er] at hr
  exact star_trans_eq hr (marker_calls 388 424 _ _ hf) (by eq_omega)

private theorem init_post_T_two_markers :
    ∃ r, CutNum false 13231 2351 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 813) +> ([0, 0] +> ((X ^ 3) +> ([0] +> ((X ^ 1171) +> ([0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_post_T_odd3
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 6606 _ hn
  have er : r = (X ^ 4274) +> ([0] +> (Y +> t)) :=
    cut_prefix 6607 2333 r ([0] +> (Y +> t)) (by omega) et
  have hc : CutNum false 13213 2334 ((X ^ 4273) +> ([0] +> (Y +> t))) :=
    CutNum_E_odd ht (by omega)
  obtain ⟨s, hs, h18⟩ := CutNum_Fs 18 false 13213 2334 _ hc (by omega)
  obtain ⟨u, h6, h12⟩ := sideRLs_pow_split 6 12 h18 (by omega)
  refine ⟨X +> s, CutNum_prepend false 13231 2351 1 s (CutNum_cast (by omega) (by omega) hs), ?_⟩
  rw [er] at hr
  refine ReachesStar.trans hr ?_
  have hh3 := h_columns [] 3 1167 _ u h6
  try dsimp only [markers] at hh3
  refine ReachesStar.trans
    (ReachesPlus.to_star (eq_mp_rev (odd_three 812 _ _ hh3) (by eq_omega))) ?_
  exact ReachesPlus.to_star
    (eq_mp_rev (normal_cycle 811 _ _ (Y_hs 2 _ _ (F_markers 6 1170 u s h12))) (by eq_omega))

private theorem init_normal_spill5 :
    ∃ r, Num true 10875 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 103) +> ([0, 0] +> ((X ^ 2133) +> ([0] +>
          ((X ^ 1171) +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_post_T_two_markers
  obtain ⟨t, ht, et⟩ := Num_E_odd_inv 6615 _ hn
  have er : r = (X ^ 4265) +> ([0] +> (Y +> t)) :=
    cut_prefix 6616 2351 r ([0] +> (Y +> t)) (by omega) et
  have hc : CutNum false 13231 2352 ((X ^ 4264) +> ([0] +> (Y +> t))) :=
    CutNum_E_odd ht (by omega)
  obtain ⟨s, hs, h8520⟩ := CutNum_Fs 8520 false 13231 2352 _ hc (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_odd_inv 10875 _ hs
  have es : s = (X ^ 4) +> ([0] +> (Y +> u)) :=
    cut_prefix 10876 10872 s ([0] +> (Y +> u)) (by omega) eu
  refine ⟨u, hu, ?_⟩
  rw [er] at hr
  have hh2130 := h_columns [1170] 2130 3 _ s h8520
  try dsimp only [markers] at hh2130
  have hnc := normal_cycles 710 101 _ _ hh2130
  rw [es] at hnc
  exact star_trans_eq hr hnc (by eq_omega)

private theorem init_normal_transpose :
    ∃ r, CutNum true 10886 5 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 101) +> ([0, 0] +> ((X ^ 2139) +> ([0] +>
          ((X ^ 1167) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_normal_spill5
  obtain ⟨s, hs, h5⟩ := Num_add 5 true 10875 r hn
  obtain ⟨t, ht, h6⟩ := CutNum_Fs 6 true 10880 0 s hs (by omega)
  refine ⟨X +> t, CutNum_prepend true 10886 5 1 t (CutNum_cast (by omega) (by omega) ht), ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (normal_odd5_prepare 100 2132 1166 r s h5)) ?_
  exact ReachesPlus.to_star (normal_T_spill 99 2135 1166 s t h6)

private theorem init_normal_transpose_end :
    ∃ r, CutNum true 11486 605 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 2440) +> ([0] +>
          ((X ^ 867) +> ([0] +> (Y +> ((X ^ 303) +> ([0] +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_normal_transpose
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 5441 _ hn
  have er : r = (X ^ 5439) +> ([0, 0] +> t) :=
    cut_prefix 5444 5 r ([0, 0] +> t) (by omega) et
  have hc : CutNum true 10886 6 ((X ^ 5438) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨s, hs, h600⟩ := CutNum_Fs 600 true 10886 6 _ hc (by omega)
  have hh300 := h_columns [] 300 3 _ s h600
  try dsimp only [markers] at hh300
  have hf : SideRLs tm40 (hf ^ 600)
      ((X ^ 1166) +> ([0] +> (Y +> ((X ^ 3) +> ([0] +> ((X ^ 5439) +> ([0, 0] +> t)))))))
      ((X ^ 866) +> ([0] +> (Y +> ((X ^ 303) +> ([0] +> (X +> s)))))) :=
    eq_mp_rev (F_pairs_odd_side 300 866 _ _ hh300) (by eq_omega)
  refine ⟨X +> s, CutNum_prepend true 11486 605 1 s (CutNum_cast (by omega) (by omega) hs), ?_⟩
  rw [er] at hr
  have hh_top := h_columns [] 300 2139 _ _ hf
  try dsimp only [markers] at hh_top
  exact star_trans_eq hr (ReachesPlus.to_star (normal_calls 99 _ _ hh_top)) (by eq_omega)

private theorem init_second_transpose_odd3 :
    ∃ r, CutNum true 13214 2333 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 145) +> ([0] +> ((X ^ 2440) +> ([0] +>
          ((X ^ 3) +> ([0] +> (Y +> ((X ^ 1167) +> ([0] +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_normal_transpose_end
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 5741 _ hn
  have er : r = (X ^ 5139) +> ([0, 0] +> t) :=
    cut_prefix 5744 605 r ([0, 0] +> t) (by omega) et
  have hc : CutNum true 11486 606 ((X ^ 5138) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨s, hs, h1728⟩ := CutNum_Fs 1728 true 11486 606 _ hc (by omega)
  have hh864 := h_columns [] 864 303 _ s h1728
  try dsimp only [markers] at hh864
  have hf : SideRLs tm40 (hf ^ 1728)
      ((X ^ 866) +> ([0] +> (Y +> ((X ^ 303) +> ([0] +> ((X ^ 5139) +> ([0, 0] +> t)))))))
      ((X ^ 2) +> ([0] +> (Y +> ((X ^ 1167) +> ([0] +> (X +> s)))))) :=
    eq_mp_rev (F_pairs_odd_side 864 2 _ _ hh864) (by eq_omega)
  refine ⟨X +> s, CutNum_prepend true 13214 2333 1 s (CutNum_cast (by omega) (by omega) hs), ?_⟩
  rw [er] at hr
  exact star_trans_eq hr (marker_calls 144 0 _ _ (F_markers 864 2439 _ _ hf)) (by eq_omega)

private theorem init_second_transpose :
    ∃ r, CutNum true 13224 2343 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 146) +> ([0] +> ((X ^ 2438) +> ([0] +> (Y +>
          (X +> ([0] +> ((X ^ 1171) +> ([0] +> r))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_transpose_odd3
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 6605 _ hn
  have er : r = (X ^ 4275) +> ([0, 0] +> t) :=
    cut_prefix 6608 2333 r ([0, 0] +> t) (by omega) et
  have hc : CutNum true 13214 2334 ((X ^ 4274) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨s, hs, h10⟩ := CutNum_Fs 10 true 13214 2334 _ hc (by omega)
  refine ⟨X +> s, CutNum_prepend true 13224 2343 1 s (CutNum_cast (by omega) (by omega) hs), ?_⟩
  rw [er] at hr
  exact star_trans_eq hr (ReachesPlus.to_star (marker_odd3_transpose 144 2437 1166 _ s h10))
    (by eq_omega)

private theorem init_nested_even4 :
    ∃ r, Num false 10876 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 857) +> ([0] +> ((X ^ 305) +> ([0] +> (Y +>
          ((X ^ 2134) +> ([0] +> ((X ^ 1171) +> ([0] +> ((X ^ 4) +> ([0, 0] +> r))))))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_transpose
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 6610 _ hn
  have er : r = (X ^ 4270) +> ([0, 0] +> t) :=
    cut_prefix 6613 2343 r ([0, 0] +> t) (by omega) et
  have hc : CutNum true 13224 2344 ((X ^ 4269) +> ([0, 0] +> t)) :=
    CutNum_O_even ht (by omega)
  obtain ⟨s, hs, h8532⟩ := CutNum_Fs 8532 true 13224 2344 _ hc (by omega)
  obtain ⟨u, hu, eu⟩ := Num_O_even_inv 10876 _ hs
  have es : s = (X ^ 3) +> ([0, 0] +> u) :=
    cut_prefix 10879 10876 s ([0, 0] +> u) (by omega) eu
  have hh2133 := h_columns [1170] 2133 1 _ s h8532
  try dsimp only [markers] at hh2133
  have hf : SideRLs tm40 (hf ^ 4266)
      ((X ^ 2437) +>
        ([0] +> (Y +> (X +> ([0] +> ((X ^ 1171) +> ([0] +> ((X ^ 4270) +> ([0, 0] +> t)))))))))
      ((X ^ 304) +> ([0] +> (Y +> ((X ^ 2134) +> ([0] +> ((X ^ 1171) +> ([0] +> (X +> s)))))))) :=
    eq_mp_rev (F_pairs_odd_side 2133 304 _ _ hh2133) (by eq_omega)
  refine ⟨u, hu, ?_⟩
  rw [er] at hr
  have hm := marker_calls 711 145 _ _ hf
  rw [es] at hm
  exact star_trans_eq hr hm (by eq_omega)

private theorem init_outer_return :
    ∃ r, Num true 7197 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 858) +>
          ([0] +> ((X ^ 302) +> ([0] +> (Y +> ((X ^ 6993) +> ([0, 0] +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_nested_even4
  obtain ⟨s, hs, h3⟩ := Num_add 3 false 10876 r hn
  obtain ⟨t, ht, hp⟩ :=
    Num_pending 1170 ([1] +> outer_left 856 302 2133) false 10879 0 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_E_even_inv 7196 _ ht
  have et : t = (X ^ 4855) +> ([0, 0] +> u) :=
    cut_prefix 7197 2342 t ([0, 0] +> u) (by omega) eu
  obtain ⟨v, hv, h1⟩ := Num_add 1 true 7196 u hu
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (nested_even4_prepare 856 302 2133 1170 r s h3)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  rw [et]
  exact ReachesPlus.to_star (outer_F_finish 856 302 2133 4855 u v h1)

private theorem init_final_birth :
    ∃ r, CutNum false 14694 205 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 958) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_outer_return
  obtain ⟨s, hs, h150⟩ := Num_add 150 true 7197 r hn
  have hf : SideRLs tm40 (hf ^ 600)
      ((X ^ 301) +> ([0] +> (Y +> ((X ^ 6993) +> ([0, 0] +> r)))))
      (X +> ([0] +> (Y +> ((X ^ 7143) +> ([0, 0] +> s))))) :=
    F_pairs_odd_side 300 1 _ _ (h_pairs_even_side 150 6992 r s h150)
  refine ⟨(X ^ 7143) +> ([0, 0] +> s), ?_, ?_⟩
  · exact CutNum_E_even hs (by omega)
  · exact star_trans_eq hr (marker_calls 100 857 _ _ hf) (by eq_omega)

private theorem init_final_marked_even :
    ∃ r, Num true 10221 r ∧
      ((init []) [tm40]⊢*
        (root (X +> ([0] +> ((X ^ 2874) +> ([0] +> ((X ^ 4272) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_final_birth
  obtain ⟨s, hs, hb⟩ := CutNum_birth 957 false 14694 205 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 10221 _ hs
  have es : s = (X ^ 4272) +> ([0, 0] +> t) :=
    cut_prefix 10222 5950 s ([0, 0] +> t) (by omega) et
  refine ⟨t, ht, ?_⟩
  rw [es] at hb
  exact ReachesStar.trans hr (ReachesPlus.to_star hb)

-- ============================================================================
-- 5d. Batch 4 (`Others_v2.v` lines 2681–3339: `final_marked_first_half` through `init_B21`)
-- ============================================================================

private theorem init_final_leading_zero :
    ∃ r, Num true 14489 r ∧
      ((init []) [tm40]⊢*
        (root ([0] +>
          ((X ^ 712) +> ([0] +> ((X ^ 2874) +> ([0] +> ((X ^ 4) +> ([0, 0] +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_final_marked_even
  obtain ⟨s, hs, h4266⟩ := Num_add 4266 true 10221 r hn
  have hf : SideRLs tm40 (hf ^ 8532) ((X ^ 4271) +> ([0, 0] +> r)) ((X ^ 5) +> ([0, 0] +> s)) :=
    F_pairs_even_side 4266 5 r s h4266
  obtain ⟨t, ht, h2⟩ := Num_add 2 true 14487 s hs
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  have h_mc := marker_calls 711 0 _ _ (F_markers 4266 2873 _ _ hf)
  refine ReachesStar.trans (eq_mp_rev h_mc (by eq_omega)) ?_
  exact ReachesPlus.to_star (eq_mp_rev (final_marked_first_half 711 2873 s t h2) (by eq_omega))

private theorem init_simple_num :
    ∃ r, Num false 11555 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 6524) +> ([0] +> (Y +> r))))) := by
  obtain ⟨r, hn, hr⟩ := init_final_leading_zero
  obtain ⟨s, hs, h3⟩ := Num_add 3 true 14489 r hn
  obtain ⟨t, ht, hp⟩ :=
    Num_pending 2873 ([1] +> ((Dr ^ 712) +> ([1, 1] +> default))) true 14492 0 s hs (by omega)
  obtain ⟨u, hu, h1⟩ := CutNum_Fs 1 true 23114 5748 t ht (by omega)
  obtain ⟨v, hv, ev⟩ := Num_O_odd_inv 11555 _ hu
  have eu : u = (X ^ 5809) +> ([0] +> (Y +> v)) :=
    cut_prefix 11558 5749 u ([0] +> (Y +> v)) (by omega) ev
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (leading_marked_even4_prepare 711 2873 r s h3)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  have h_fin := D1_F_finish 711 t u h1
  rw [eu] at h_fin
  exact ReachesPlus.to_star (eq_mp_rev h_fin (by eq_omega))

set_option maxRecDepth 100000 in
private theorem init_high_a1 :
    ∃ r, Num true 31127 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 5189) +> ([0] +> (X +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_simple_num
  obtain ⟨s, hs, hd⟩ := Num_normal_odd 6522 false 11555 r hn
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 15563 _ hs
  obtain ⟨u, hu, hm⟩ := Num_markers 5188 0 0 true 15563 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star hd) ?_
  rw [et]
  exact hm

private theorem init_high_odd2 :
    ∃ r, Num false 36314 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 4324) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_high_a1
  obtain ⟨s, hs, hp⟩ := Num_pending 5188 ([1] +> default) true 31127 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_O_even_inv 23345 _ hs
  have es : s = (X ^ 12970) +> ([0, 0] +> t) :=
    cut_prefix 23348 10378 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h12969⟩ := Num_add 12969 false 23345 t ht
  have hf : SideRLs tm40 (hf ^ 25938) ((X ^ 12970) +> ([0] +> (Y +> t))) (X +> ([0] +> (Y +> u))) :=
    F_pairs_odd_side 12969 1 t u h12969
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (a1_prepare 5188 r)) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hp) ?_
  rw [es]
  refine ReachesStar.trans (ReachesPlus.to_star (a1_even_finish 12970 t)) ?_
  exact eq_mp_rev (marker_calls 4323 0 _ _ hf) (by eq_omega)

private theorem init_high_T :
    ∃ r, Num true 36313 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 865) +> ([0] +> ((X ^ 12972) +> ([0] +> ((X ^ 5) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_high_odd2
  obtain ⟨s, hs, hb⟩ := CutNum_birth 4323 false 36314 0 r hn (by omega)
  obtain ⟨t, ht, et⟩ := Num_E_even_inv 31129 _ hs
  have es : s = (X ^ 5189) +> ([0, 0] +> t) :=
    cut_prefix 31130 25941 s ([0, 0] +> t) (by omega) et
  obtain ⟨u, hu, h5184⟩ := Num_add 5184 true 31129 t ht
  have hf : SideRLs tm40 (hf ^ 10368) ((X ^ 5188) +> ([0, 0] +> t)) ((X ^ 4) +> ([0, 0] +> u)) :=
    F_pairs_even_side 5184 4 t u h5184
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  rw [es] at hb
  refine ReachesStar.trans (ReachesPlus.to_star hb) ?_
  exact eq_mp_rev (marker_calls 864 0 _ _ (F_markers 5184 12971 _ _ hf)) (by eq_omega)

private theorem init_high_zero4 :
    ∃ r, CutNum true 75233 25943 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 866) +> ([0, 0, 0, 0] +> r)))) := by
  obtain ⟨r, hn, hr⟩ := init_high_T
  obtain ⟨s, hs, h2⟩ := Num_add 2 true 36313 r hn
  obtain ⟨t, ht, hc⟩ := CutNum_marked_even3 864 12970 true 36315 0 s hs (by omega)
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (marked_even5_half 864 12970 r s h2)) ?_
  exact ReachesPlus.to_star hc

private theorem init_next_T :
    ∃ r, Num false 51880 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 1946) +> ([0] +> ((X ^ 1299) +> ([0] +> ((X ^ 5) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_high_zero4
  obtain ⟨s, hs, hn0⟩ := CutNum_zero4_even 431 true 75233 25943 r hn (by omega)
  obtain ⟨t, ht, hb⟩ := CutNum_birth 432 true 77826 25943 s hs (by omega)
  obtain ⟨u, hu, eu⟩ := Num_O_even_inv 40210 _ ht
  have et : t = (X ^ 11675) +> ([0, 0] +> u) :=
    cut_prefix 40213 28538 t ([0, 0] +> u) (by omega) eu
  obtain ⟨v, hv, h11670⟩ := Num_add 11670 false 40210 u hu
  have hf : SideRLs tm40 (hf ^ 23340) ((X ^ 11674) +> ([0, 0] +> u)) ((X ^ 4) +> ([0, 0] +> v)) :=
    F_pairs_even_side 11670 4 u v h11670
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star hn0) ?_
  rw [et] at hb
  refine ReachesStar.trans (ReachesPlus.to_star hb) ?_
  exact eq_mp_rev (marker_calls 1945 0 _ _ (F_markers 11670 1298 _ _ hf)) (by eq_omega)

private theorem init_next_zero4 :
    ∃ r, CutNum false 55781 2597 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 1947) +> ([0, 0, 0, 0] +> r)))) := by
  obtain ⟨r, hn, hr⟩ := init_next_T
  obtain ⟨s, hs, ht⟩ := CutNum_marked_even5 1945 1297 false 51880 0 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star ht)⟩

private theorem init_next_a1 :
    ∃ r, CutNum false 61619 2597 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 974) +> ([0] +> (X +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_next_zero4
  obtain ⟨s, hs, hn1⟩ := CutNum_zero4_odd 972 false 55781 2597 r hn (by omega)
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hn1)⟩

private theorem init_second_E2 :
    ∃ r, Num true 59997 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 9243) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_next_a1
  obtain ⟨s, hs, ha⟩ :=
    CutNum_a1_odd 973 false 61619 2597 32270 r hn (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨t, ht, hm⟩ := Num_markers 9242 0 1 true 32271 s hs
  refine ⟨t, ht, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  exact hm

private theorem init_second_odd5 :
    ∃ r, Num false 69235 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 4230) +> ([0] +> (X +> ([0] +> ((X ^ 5) +> ([0] +> (Y +> r))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_E2
  obtain ⟨s, hs, ha⟩ := CutNum_a2 9241 true 59997 0 r hn (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail true true _ 43861 _ 25379 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hc⟩ := Num_a2_cleanup 25372 true false 43861 t ht
  obtain ⟨v, hv, hm⟩ := Num_two_markers 4228 1 0 4 true false 43867 u hu
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  rw [es] at ha
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hc) ?_
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem init_second_D3 :
    ∃ r, Num true 69240 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 771) +>
          ([0] +> ((X ^ 12691) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_odd5
  obtain ⟨r5, hn5, h5⟩ := Num_add 5 false 69235 r hn
  obtain ⟨s, hs, h50760⟩ := CutNum_Fs 50760 false 69240 0 r5 hn5 (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail false false _ 60000 _ 9241 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, h9240⟩ := Num_add 9240 true 60000 t ht
  have hf : SideRLs tm40 (hf ^ 18480) s (X +> ([0, 0] +> u)) := by
    rw [es]
    exact eq_mp_rev (F_pairs_even_side 9240 1 t u h9240) (by (try dsimp only [sep]); eq_omega)
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star (odd_five 4229 r r5 h5)) ?_
  refine ReachesStar.trans
    (ReachesPlus.to_star (normal_calls 4229 _ _ (YY_hs 12689 r5 s h50760))) ?_
  have h_mc := marker_calls 770 0 _ _ (F_columns [12690, 0] 4620 s (X +> ([0, 0] +> u)) hf)
  exact eq_mp_rev h_mc (by (try dsimp only [markers]); eq_omega)

private theorem init_third_a1 :
    ∃ r, Num false 81933 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 16542) +> ([0] +> (X +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_D3
  obtain ⟨s, hs, h10⟩ := CutNum_Fs 10 true 69240 0 r hn (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail true false _ 34623 _ 34616 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hm⟩ := Num_markers 15770 771 0 false 34623 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  have hd3 := d3_ten 770 12689 r s h10
  rw [es] at hd3
  refine ReachesStar.trans (ReachesPlus.to_star hd3) ?_
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem init_image_E3 :
    ∃ r, Num false 109375 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 14597) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_third_a1
  obtain ⟨s, hs, ha⟩ :=
    CutNum_a1_odd 16541 false 81933 0 65779 r hn (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨t, ht, hm⟩ := Num_markers 10899 0 0 true 65780 s hs
  obtain ⟨u, hu, ha2⟩ :=
    CutNum_a1_odd 10899 true 98477 0 65586 t ht (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨v, hv, hm2⟩ := Num_markers 14596 0 2 false 65587 u hu
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  refine ReachesStar.trans hm ?_
  refine ReachesStar.trans (ReachesPlus.to_star ha2) ?_
  exact hm2

private theorem init_image_U :
    ∃ r, Num false 218758 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 36461) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_image_E3
  obtain ⟨s, hs, ha⟩ := Num_a3 14596 false 109375 r hn (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail false true _ 76585 _ 47392 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hd⟩ := Num_normal_odd 47390 true 76585 t ht
  obtain ⟨v, hv, ev⟩ :=
    CutNum_digit_tail true false _ 109378 0 109381 u hu (by cond_omega) (by cond_omega)
  obtain ⟨w, hw, hm⟩ := Num_markers 36460 0 1 false 109378 v hv
  refine ⟨w, hw, ?_⟩
  refine ReachesStar.trans hr ?_
  rw [es] at ha
  refine ReachesStar.trans
    (ReachesPlus.to_star (eq_mp_rev ha (by dsimp only [sep]))) ?_
  rw [ev] at hd
  refine ReachesStar.trans
    (ReachesPlus.to_star (eq_mp_rev hd (by (try dsimp only [sep]); eq_omega))) ?_
  exact hm

private theorem init_second_zero4 :
    ∃ r, CutNum true 255224 1 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 15193) +> ([0, 0, 0, 0] +> r)))) := by
  obtain ⟨r, hn, hr⟩ := init_image_U
  obtain ⟨s, hs, ha⟩ := CutNum_a2 36459 false 218758 0 r hn (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail false false _ 164071 _ 91151 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hc⟩ := Num_a2_cleanup 91144 false true 164071 t ht
  obtain ⟨v, hv, hm⟩ := Num_two_markers 15190 1 0 4 false true 164077 u hu
  obtain ⟨w, hw, h7⟩ := CutNum_Fs 7 true 255217 0 v hv (by omega)
  refine ⟨(X ^ 6) +> w, CutNum_prepend true 255224 1 6 w hw, ?_⟩
  refine ReachesStar.trans hr ?_
  rw [es] at ha
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hc) ?_
  refine ReachesStar.trans (eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)) ?_
  exact ReachesPlus.to_star (two_even5 15191 v w h7)

-- T1r moved above eq_omega

private theorem init_B21_a2 :
    ∃ r, Num false 308395 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 48868) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, hn, hr⟩ := init_second_zero4
  obtain ⟨s, hs, hz⟩ := CutNum_zero4_odd 7595 true 255224 1 r hn (by omega)
  obtain ⟨t, ht, ha⟩ :=
    CutNum_a1_odd 7596 true 300800 1 161793 s hs (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hm⟩ := Num_markers 48867 0 1 false 161794 t ht
  refine ⟨u, hu, ?_⟩
  refine ReachesStar.trans hr ?_
  refine ReachesStar.trans (ReachesPlus.to_star hz) ?_
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  exact hm

private theorem init_B21_even4 :
    ∃ r, Num true 357262 r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ 21628) +> ([0] +> (X +> ([0] +> ((X ^ 4) +> ([0, 0] +> r)))))))) := by
  obtain ⟨r, hn, hr⟩ := init_B21_a2
  obtain ⟨s, hs, ha⟩ := CutNum_a2 48866 false 308395 0 r hn (by omega)
  obtain ⟨t, ht, es⟩ :=
    CutNum_digit_tail false false _ 227500 _ 129766 s hs (by cond_omega) (by cond_omega)
  obtain ⟨u, hu, hc⟩ := Num_a2_cleanup 129759 false true 227500 t ht
  obtain ⟨v, hv, hm⟩ := Num_two_markers 21626 1 0 3 false true 227506 u hu
  refine ⟨v, hv, ?_⟩
  refine ReachesStar.trans hr ?_
  rw [es] at ha
  refine ReachesStar.trans (ReachesPlus.to_star ha) ?_
  refine ReachesStar.trans (ReachesPlus.to_star hc) ?_
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem init_B21 :
    ∃ r, Num true 779418 r ∧
      ((init []) [tm40]⊢* (root ((X ^ 129904) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))) := by
  obtain ⟨r, hn, hr⟩ := init_B21_even4
  obtain ⟨s, hs, hb⟩ := Num_even4_B21 10813 59542 r hn
  exact ⟨s, hs, ReachesStar.trans hr (ReachesPlus.to_star hb)⟩

-- ============================================================================
-- 5e. Batch 5 (`Others_v2.v` lines 3340–4136: `D1_zero4_cleanup` through `zeroY00_prepare`)
-- ============================================================================

private theorem Num_B21_return (n : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (42 + n * 48) r) :
    ∃ s, Num true (151 + n * 150) s ∧
      ((root ((X ^ (8 + n * 8)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (26 + n * 25)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_birth_evenzero (6 + n * 8) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, h1⟩ := Num_inc hn1
  obtain ⟨r3, hn3, he⟩ :=
    CutNum_nested_even (22 + n * 24) false (43 + n * 48) 0 r2 (eq_mp_rev hn2 (by eq_omega))
    (by omega)
  obtain ⟨r4, hn4, ho⟩ := CutNum_one_odd1 false _ _ r3 hn3 (by omega)
  obtain ⟨r5, hn5, e4⟩ :=
    CutNum_digit_tail false false _ (59 + n * 60) _ (12 + n * 12) r4 hn4 (by cond_omega)
    (by cond_omega)
  obtain ⟨r6, hn6, hm⟩ := Num_two_markers (1 + n * 2) 0 1 5 false true (59 + n * 60) r5 hn5
  obtain ⟨r7, hn7, h12⟩ := CutNum_Fs 12 true _ 0 r6 hn6 (by omega)
  obtain ⟨r8, hn8, e7⟩ := CutNum_root (n * 2) 12 true _ r7 hn7
  obtain ⟨r9, hn9, e8⟩ :=
    CutNum_digit_tail true true _ (36 + n * 36) 0 (39 + n * 36) r8 hn8 (by cond_omega)
    (by cond_omega)
  obtain ⟨r10, hn10, hn0⟩ := Num_normal_odd (37 + n * 38) false (36 + n * 36) r9 hn9
  obtain ⟨r11, hn11, e10⟩ :=
    CutNum_digit_tail false false _ (76 + n * 75) 0 (77 + n * 75) r10 hn10 (by cond_omega)
    (by cond_omega)
  obtain ⟨r12, hn12, hm2⟩ := Num_markers (25 + n * 25) 0 2 true (76 + n * 75) r11 hn11
  refine ⟨r12, eq_mp_rev hn12 (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev hb (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (zero_X_even2 (22 + n * 24) r1 r2 h1) (by eq_omega)) ?_
  refine ReachesPlus.trans he ?_
  refine ReachesPlus.trans (zero_X_zero4 r3) ?_
  refine ReachesPlus.trans ho ?_
  rw [e4]
  refine stepStar_stepPlus_trans (eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (two_even6_second (n * 2) r6 r7 h12) (by eq_omega)) ?_
  have h_mid : root ((X ^ (12 + n * 2)) +> r7) =
      root ((X ^ (2 + (37 + n * 38))) +> ([0] +> (Y +> r9))) := by
    have h_step1 : root ((X ^ (12 + n * 2)) +> r7) = root ((X ^ (n * 2)) +> r8) := by
      rw [← e7]
      eq_omega
    rw [h_step1, e8]
    try dsimp only [sep]
    eq_omega
  rw [h_mid]
  refine ReachesPlus.trans_star hn0 ?_
  rw [e10]
  exact eq_mp_rev hm2 (by (try dsimp only [sep]); eq_omega)

private theorem Num_Oa3_odd_return (n : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (13 + n * 12) r) :
    ∃ s, Num true (35 + n * 24) s ∧
      ((root ((X ^ (3 + n * 2)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (7 + n * 4)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, ha⟩ := Num_a3 (2 + n * 2) true (13 + n * 12) r hn (by omega)
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail true true _ (11 + n * 9) _ (8 + n * 5) r1 hn1 (by cond_omega) (by cond_omega)
  obtain ⟨r3, hn3, hn0⟩ := Num_normal_odd (6 + n * 5) false (11 + n * 9) r2 hn2
  obtain ⟨r4, hn4, e3⟩ :=
    CutNum_digit_tail false false _ (17 + n * 12) 0 (18 + n * 12) r3 hn3 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm⟩ := Num_markers (6 + n * 4) 0 0 true (17 + n * 12) r4 hn4
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev ha (by eq_omega)) ?_
  rw [e1]
  refine ReachesPlus.trans_star (eq_mp_rev hn0 (by (try dsimp only [sep]); eq_omega)) ?_
  rw [e3]
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_B21_odd_return (n : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (90 + n * 96) r) :
    ∃ s, Num true (611 + n * 600) s ∧
      ((root ((X ^ (16 + n * 16)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (103 + n * 100)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨t, ht, hb⟩ := Num_B21_return (1 + n * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨s, hs, ha⟩ := Num_Oa3_odd_return (24 + n * 25) t (eq_mp_rev ht (by eq_omega))
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  exact ReachesPlus.trans (eq_mp_rev hb (by eq_omega)) (eq_mp_rev ha (by eq_omega))

private theorem Num_one_mod6_even (v : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (35 + v * 144) r) :
    ∃ s, Num true (101 + v * 360) s ∧
      ((root ((X ^ (7 + v * 24)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (18 + v * 60)) +> ([0] +> (X +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, hn1, ha1⟩ :=
    CutNum_a1_even (6 + v * 24) true (35 + v * 144) 0 (26 + v * 108) (15 + v * 60) r hn
    (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨r2, hn2, hm1⟩ := Num_marker_phase (5 + v * 20) 0 0 true false (26 + v * 108) r1 hn1
  obtain ⟨r3, hn3, ho⟩ := CutNum_odd1 (4 + v * 20) false _ 0 r2 hn2 (by omega)
  obtain ⟨r4, hn4, e3⟩ :=
    CutNum_digit_tail false false _ (37 + v * 144) _ (7 + v * 24) r3 hn3 (by cond_omega)
    (by cond_omega)
  obtain ⟨r5, hn5, hm2⟩ :=
    Num_two_markers (1 + v * 4) 0 (16 + v * 60) 0 false true (37 + v * 144) r4 hn4
  obtain ⟨r6, hn6, he⟩ :=
    CutNum_nested_even_front (1 + v * 4) (15 + v * 60) true _ 0 r5 hn5 (by omega)
  obtain ⟨r7, hn7, hz⟩ := CutNum_zero4_leading_even (v * 2) true _ _ r6 hn6 (by omega)
  obtain ⟨r8, hn8, ha3⟩ := CutNum_a3 (v * 2) true _ _ r7 hn7 (by omega)
  obtain ⟨r9, hn9, e8⟩ :=
    CutNum_digit_tail true false _ (50 + v * 183) _ (18 + v * 59) r8 hn8 (by cond_omega)
    (by cond_omega)
  obtain ⟨r10, hn10, hn0⟩ := Num_normal (16 + v * 59) false (50 + v * 183) r9 hn9
  obtain ⟨r11, hn11, e10⟩ :=
    CutNum_digit_tail false true _ (50 + v * 180) 0 (51 + v * 180) r10 hn10 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm3⟩ := Num_marker_phase (17 + v * 60) 0 0 true true (50 + v * 180) r11 hn11
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev ha1 (by eq_omega)) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev hm1 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev ho (by eq_omega)) ?_
  rw [e3]
  refine stepStar_stepPlus_trans (eq_mp_rev hm2 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev he (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev hz (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev ha3 (by eq_omega)) ?_
  rw [e8]
  refine ReachesPlus.trans_star (eq_mp_rev hn0 (by (try dsimp only [sep]); eq_omega)) ?_
  rw [e10]
  exact eq_mp_rev hm3 (by (try dsimp only [sep]); eq_omega)

private theorem Num_critical_odd (v : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (29 + v * 72) r) :
    ∃ s, Num true (47 + v * 108) s ∧
      ((root ((X ^ (6 + v * 12)) +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (2 + v * 3)) +>
          ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))))) := by
  obtain ⟨r1, hn1, ho⟩ := CutNum_odd1 (4 + v * 12) true (29 + v * 72) 0 r hn (by omega)
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail true false _ (29 + v * 72) _ 1 r1 hn1 (by cond_omega) (by cond_omega)
  obtain ⟨r3, hn3, he⟩ := CutNum_nested_even (15 + v * 36) false (29 + v * 72) 0 r2 hn2 (by omega)
  obtain ⟨r4, hn4, ho1⟩ := CutNum_one_odd1 false _ _ r3 hn3 (by omega)
  obtain ⟨r5, hn5, e4⟩ :=
    CutNum_digit_tail false true _ (41 + v * 90) _ (8 + v * 18) r4 hn4 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm⟩ := Num_two_markers (1 + v * 3) 0 1 1 true true (41 + v * 90) r5 hn5
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev ho (by eq_omega)) ?_
  rw [e1]
  refine ReachesPlus.trans (eq_mp_rev he (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (zero_X_zero4 r3) ?_
  refine ReachesPlus.trans_star ho1 ?_
  rw [e4]
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_B21_to_A2 (w : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (90 + w * 576) r) :
    ∃ s, Num true (47 + (21 + w * 125) * 108) s ∧
      ((root ((X ^ (16 + w * 96)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (65 + w * 375)) +>
          ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_B21_odd_return (w * 6) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, ho⟩ := Num_one_mod6_even (4 + w * 25) r1 (eq_mp_rev hn1 (by eq_omega))
  obtain ⟨s, hs, hc⟩ := Num_critical_odd (21 + w * 125) r2 (eq_mp_rev hn2 (by eq_omega))
  refine ⟨s, hs, ?_⟩
  exact ReachesPlus.trans (eq_mp_rev hb (by eq_omega))
    (ReachesPlus.trans (eq_mp_rev ho (by eq_omega)) (eq_mp_rev hc (by eq_omega)))

-- klj, congr_klj moved above eq_omega

private theorem Num_A2_return (p : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (47 + p * 36) r) :
    ∃ s, Num false (47 + p * 36) s ∧
      ((root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))
        [tm40]⊢⁺
        (root ((X ^ (11 + p * 6)) +> ([0] +> (X +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, hn1, hf⟩ := CutNum_Fs (18 + p * 6) true (47 + p * 36) 0 r hn (by omega)
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail true true _ (30 + p * 21) _ (15 + p * 15) r1 hn1 (by cond_omega)
    (by cond_omega)
  obtain ⟨r3, hn3, h2⟩ := Num_add 2 false (30 + p * 21) r2 hn2
  obtain ⟨s, hs, hm⟩ := Num_marker_phase (5 + p * 5) (5 + p) 0 true false (30 + p * 21 + 2) r3 hn3
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (a2_odd_calls p r r1 hf) ?_
  rw [e1]
  refine ReachesPlus.trans_star
    (eq_mp_rev (leading_marker_half (4 + p) (15 + p * 15) true r2 r3 h2) (by eq_omega)) ?_
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_critical_E (t : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (11 + t * 6) r) :
    ∃ s, CutNum true (40 + t * 15) (17 + t * 6) s ∧
      ((root ((X ^ (5 + t)) +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ 3) +> ([0] +> s)))) := by
  obtain ⟨r1, hn1, h3⟩ := CutNum_Fs 3 false (11 + t * 6) 0 r hn (by omega)
  have hc : CutNum false (14 + t * 6) 2 (X +> r1) :=
    CutNum_prepend false (14 + t * 6) 2 1 r1 (CutNum_cast (by omega) (by omega) hn1)
  obtain ⟨r2, hn2, hf⟩ := CutNum_Fs (12 + t * 6) false (14 + t * 6) 2 (X +> r1) hc (by omega)
  have hh := h_columns [] (6 + t * 3) 1 (X +> r1) r2 (eq_mp_rev hf (by eq_omega))
  try dsimp only [markers] at hh
  obtain ⟨r3, hn3, e2⟩ :=
    CutNum_digit_tail false false _ (13 + t * 6) _ 0 r2 hn2 (by cond_omega) (by cond_omega)
  obtain ⟨r4, hn4, hp⟩ :=
    Num_pending (6 + t * 3) (CEr +> default) true (13 + t * 6) 0 r3 hn3 (by omega)
  obtain ⟨r5, hn5, h6⟩ := CutNum_Fs 6 true _ _ r4 hn4 (by omega)
  refine ⟨(X ^ 3) +> r5,
    CutNum_prepend true (40 + t * 15) (17 + t * 6) 3 r5 (CutNum_cast (by omega) (by omega) hn5), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (odd1_prepare (3 + t) r r1 h3) (by eq_omega)) ?_
  refine stepStar_stepPlus_trans
    (eq_mp_rev (normal_cycles (2 + t) 1 _ _ (eq_mp_rev hh (by eq_omega))) (by eq_omega)) ?_
  rw [e2]
  refine ReachesPlus.trans (critical_E_front3 _) ?_
  refine ReachesPlus.trans
    (eq_mp_rev (critical_E_prepare (6 + t * 3) r3) (by (try dsimp only [sep]); eq_omega)) ?_
  exact ReachesPlus.trans hp (critical_E_finish r4 r5 h6)

private theorem Num_critical_E_return (p : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (47 + p * 36) r) :
    ∃ s, Num false (75 + p * 54) s ∧
      ((root ((X ^ (11 + p * 6)) +> ([0] +> (X +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (7 + p * 3)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, hc⟩ := Num_critical_E (6 + p * 6) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail true false _ (63 + p * 45) _ (13 + p * 9) r1 hn1 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm⟩ := Num_marker_phase (4 + p * 3) 2 0 false false (63 + p * 45) r2 hn2
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans_star (eq_mp_rev hc (by eq_omega)) ?_
  rw [e1]
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_E_resurge (s : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (75 + s * 108) r) :
    ∃ t, Num true (81 + s * 114) t ∧
      ((root ((X ^ (7 + s * 6)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (12 + s * 17)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> t))))))) := by
  obtain ⟨r1, hn1, ha⟩ :=
    CutNum_a1_even (6 + s * 6) false (75 + s * 108) 0 (48 + s * 63) (35 + s * 51) r hn
    (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨t, ht, hm⟩ := Num_marker_phase (11 + s * 17) 0 2 true true (48 + s * 63) r1 hn1
  refine ⟨t, eq_mp_rev ht (by eq_omega), ?_⟩
  exact ReachesPlus.trans_star (eq_mp_rev ha (by eq_omega))
    (eq_mp_rev hm (by (try dsimp only [sep]); eq_omega))

private theorem Num_Y_return (s : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (81 + s * 114) r) :
    ∃ t, Num false (82 + s * 114) t ∧
      ((root ((X ^ (12 + s * 17)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (2 + s)) +>
          ([0] +> ((X ^ (37 + s * 51)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> t)))))))) := by
  obtain ⟨r1, hn1, h3⟩ := Num_add 3 true (81 + s * 114) r hn
  obtain ⟨r2, hn2, hf⟩ := CutNum_Fs (72 + s * 102) true _ 0 r1 hn1 (by omega)
  obtain ⟨r3, hn3, e2⟩ :=
    CutNum_digit_tail true false _ (76 + s * 108) _ (7 + s * 6) r2 hn2 (by cond_omega)
    (by cond_omega)
  obtain ⟨t, ht, hm⟩ := Num_two_markers (1 + s) 0 (36 + s * 51) 1 false false (76 + s * 108) r3 hn3
  have hh := Y_hs (35 + s * 51) r1 r2 (eq_mp_rev hf (by eq_omega))
  refine ⟨t, eq_mp_rev ht (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (odd_three (11 + s * 17) r r1 h3) (by eq_omega)) ?_
  refine ReachesPlus.trans_star
    (eq_mp_rev (normal_calls (11 + s * 17) _ _ (eq_mp_rev hh (by eq_omega))) (by eq_omega)) ?_
  rw [e2]
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_A2_to_C (s : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (47 + s * 72) r) :
    ∃ t, Num false (82 + s * 114) t ∧
      ((root ((X ^ (2 + s * 2)) +> ([0] +> ((X ^ 2) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))
        [tm40]⊢⁺
        (root ((X ^ (2 + s)) +>
          ([0] +> ((X ^ (37 + s * 51)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> t)))))))) := by
  obtain ⟨r1, hn1, ha⟩ := Num_A2_return (s * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, hc⟩ := Num_critical_E_return (s * 2) r1 hn1
  obtain ⟨r3, hn3, he⟩ := Num_E_resurge s r2 (eq_mp_rev hn2 (by eq_omega))
  obtain ⟨t, ht, hy⟩ := Num_Y_return s r3 hn3
  exact ⟨t, ht,
    ReachesPlus.trans ha (ReachesPlus.trans hc (ReachesPlus.trans (eq_mp_rev he (by eq_omega)) hy))⟩

private theorem Num_B21_to_C (u : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (90 + (1 + u * 2) * 576) r) :
    ∃ t, Num false (82 + (219 + u * 375) * 114) t ∧
      ((root ((X ^ (16 + (1 + u * 2) * 96)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (2 + (219 + u * 375))) +> ([0] +> ((X ^ (37 + (219 + u * 375) * 51)) +>
          ([0] +> ((X ^ 2) +> ([0, 0] +> t)))))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_B21_to_A2 (1 + u * 2) r hn
  obtain ⟨t, ht, hc⟩ := Num_A2_to_C (219 + u * 375) r1 (eq_mp_rev hn1 (by eq_omega))
  exact ⟨t, ht, ReachesPlus.trans hb (eq_mp_rev hc (by eq_omega))⟩

private theorem Num_C_short (t : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (82 + t * 114) r) :
    ∃ s, CutNum false (197 + t * 267) (72 + t * 101) s ∧
      ((root ((X ^ (2 + t)) +>
        ([0] +> ((X ^ (37 + t * 51)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))) [tm40]⊢⁺ root s) :=
        by
  obtain ⟨r1, hn1, hc⟩ :=
    CutNum_C_short (1 + t) (36 + t * 51) false (82 + t * 114) 0 r hn (by omega)
  refine ⟨(X ^ (5 + t)) +> r1, ?_, eq_mp_rev hc (by eq_omega)⟩
  exact CutNum_prepend false (197 + t * 267) (72 + t * 101) (5 + t) r1
    (CutNum_cast (by omega) (by omega) hn1)

private theorem Num_C_even (n : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (196 + n * 228) r) :
    ∃ s, Num false (406 + n * 462) s ∧
      ((root ((X ^ (3 + n * 2)) +>
        ([0] +> ((X ^ (88 + n * 102)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (69 + n * 77)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, hn1, hc⟩ := Num_C_short (1 + n * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail false false _ (232 + n * 267) _ (60 + n * 65) r1 hn1 (by cond_omega)
    (by cond_omega)
  obtain ⟨r3, hn3, hn0⟩ := Num_normal (58 + n * 65) true (232 + n * 267) r2 hn2
  obtain ⟨r4, hn4, e3⟩ :=
    CutNum_digit_tail true true _ (202 + n * 231) 0 (205 + n * 231) r3 hn3 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm⟩ := Num_marker_phase (68 + n * 77) 0 1 true false (202 + n * 231) r4 hn4
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev hc (by eq_omega)) ?_
  rw [e1]
  refine ReachesPlus.trans_star (eq_mp_rev hn0 (by (try dsimp only [sep]); eq_omega)) ?_
  rw [e3]
  exact eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)

private theorem Num_B21_to_Ebirth (v : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (90 + (1 + v * 4) * 576) r) :
    ∃ s, Num false (406 + (109 + v * 375) * 462) s ∧
      ((root ((X ^ (16 + (1 + v * 4) * 96)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (69 + (109 + v * 375) * 77)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_B21_to_C (v * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨s, hs, hc⟩ := Num_C_even (109 + v * 375) r1 (eq_mp_rev hn1 (by eq_omega))
  exact ⟨s, hs, ReachesPlus.trans (eq_mp_rev hb (by eq_omega)) (eq_mp_rev hc (by eq_omega))⟩

private theorem Num_birth_Edeficit (p : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (4 + p * 6) r) :
    ∃ s, Num true (6 + p * 6) s ∧
      ((root ((X ^ (2 + p)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ([0, 0, 0] +> (Y +> ((X ^ (3 + p * 3)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))))) :=
          by
  obtain ⟨r1, hn1, hf⟩ := CutNum_Fs (6 + p * 6) false (4 + p * 6) 0 r hn (by omega)
  obtain ⟨r2, hn2, e1⟩ :=
    CutNum_digit_tail false false _ (5 + p * 6) _ 0 r1 hn1 (by cond_omega) (by cond_omega)
  obtain ⟨s, hs, h1⟩ := Num_inc hn2
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  have er1 : r1 = [0, 0] +> r2 := by simpa [sep] using e1
  rw [er1] at hf
  exact birth_E_underflow p r r2 s hf h1

private theorem Num_Ebirth_even_return (t : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (16 + t * 12) r) :
    ∃ s, Num true (95 + t * 48) s ∧
      ((root ((X ^ (4 + t * 2)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (17 + t * 8)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_birth_Edeficit (2 + t * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, h1⟩ := Num_inc hn1
  obtain ⟨r3, hn3, hz⟩ := CutNum_zeroY_even (10 + t * 6) true _ 0 r2 hn2 (by omega)
  obtain ⟨r4, hn4, e3⟩ :=
    CutNum_digit_tail true false _ (26 + t * 15) _ (7 + t * 3) r3 hn3 (by cond_omega)
    (by cond_omega)
  obtain ⟨r5, hn5, hn0⟩ := Num_normal (5 + t * 3) false (26 + t * 15) r4 hn4
  obtain ⟨r6, hn6, e5⟩ :=
    CutNum_digit_tail false false _ (22 + t * 12) 0 (23 + t * 12) r5 hn5 (by cond_omega)
    (by cond_omega)
  obtain ⟨r7, hn7, hm⟩ := Num_markers (7 + t * 4) 0 2 true (22 + t * 12) r6 hn6
  obtain ⟨r8, hn8, ha⟩ := Num_a3 (7 + t * 4) true _ r7 hn7 (by omega)
  obtain ⟨r9, hn9, e8⟩ :=
    CutNum_digit_tail true false _ (34 + t * 18) _ (21 + t * 10) r8 hn8 (by cond_omega)
    (by cond_omega)
  obtain ⟨r10, hn10, hn10r⟩ := Num_normal (19 + t * 10) false (34 + t * 18) r9 hn9
  obtain ⟨r11, hn11, e10⟩ :=
    CutNum_digit_tail false false _ (47 + t * 24) 0 (48 + t * 24) r10 hn10 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm2⟩ := Num_markers (16 + t * 8) 0 0 true (47 + t * 24) r11 hn11
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev hb (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (birth_E_prelude (9 + t * 6) r1 r2 h1) (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev hz (by eq_omega)) ?_
  rw [e3]
  refine ReachesPlus.trans (eq_mp_rev hn0 (by (try dsimp only [sep]); eq_omega)) ?_
  rw [e5]
  refine stepStar_stepPlus_trans (eq_mp_rev hm (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans ha ?_
  rw [e8]
  refine ReachesPlus.trans_star (eq_mp_rev hn10r (by (try dsimp only [sep]); eq_omega)) ?_
  rw [e10]
  exact eq_mp_rev hm2 (by (try dsimp only [sep]); eq_omega)

private theorem Num_Ebirth_to_C3 (v : ℕ) (r : ListBlank (Fin 2))
    (hn : Num false (40 + v * 36) r) :
    ∃ s, Num true (223 + v * 168) s ∧
      ((root ((X ^ (8 + v * 6)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (6 + v * 4)) +>
          ([0] +> ((X ^ (82 + v * 60)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))))) := by
  obtain ⟨r1, hn1, he⟩ := Num_Ebirth_even_return (2 + v * 3) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨r2, hn2, ha⟩ :=
    CutNum_a1_even (32 + v * 24) true _ 0 (143 + v * 108) (80 + v * 60) r1 hn1 (by cond_omega)
    (by cond_omega) (by cond_omega)
  obtain ⟨r3, hn3, hm1⟩ := Num_marker_phase (26 + v * 20) 0 2 true false (143 + v * 108) r2 hn2
  obtain ⟨r4, hn4, h3⟩ := Num_add 3 false _ r3 hn3
  obtain ⟨r5, hn5, hf⟩ := CutNum_Fs (162 + v * 120) false _ 0 r4 hn4 (by omega)
  obtain ⟨r6, hn6, e5⟩ :=
    CutNum_digit_tail false false _ (193 + v * 144) _ (32 + v * 24) r5 hn5 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, hs, hm2⟩ :=
    Num_two_markers (5 + v * 4) 0 (81 + v * 60) 2 false true (193 + v * 144) r6 hn6
  have hh := Y_hs (80 + v * 60) r4 r5 (eq_mp_rev hf (by eq_omega))
  refine ⟨s, eq_mp_rev hs (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev he (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev ha (by eq_omega)) ?_
  refine stepStar_stepPlus_trans (eq_mp_rev hm1 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (odd_three (26 + v * 20) r3 r4 h3) (by eq_omega)) ?_
  refine ReachesPlus.trans_star
    (eq_mp_rev (normal_calls (26 + v * 20) _ _ (eq_mp_rev hh (by eq_omega))) (by eq_omega)) ?_
  rw [e5]
  exact eq_mp_rev hm2 (by (try dsimp only [sep]); eq_omega)

private theorem Num_B21_to_C3 (w : ℕ) (r : ListBlank (Fin 2))
    (hn : Num true (90 + (1 + w * 8) * 576) r) :
    ∃ s, Num true (223 + (29 + 46 * 30 + w * 125 * 77) * 168) s ∧
      ((root ((X ^ (16 + (1 + w * 8) * 96)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (6 + (29 + 46 * 30 + w * 125 * 77) * 4)) +> ([0] +>
          ((X ^ (82 + (29 + 46 * 30 + w * 125 * 77) * 60)) +>
            ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))))) := by
  obtain ⟨r1, hn1, hb⟩ := Num_B21_to_Ebirth (w * 2) r (eq_mp_rev hn (by eq_omega))
  obtain ⟨s, hs, he⟩ :=
    Num_Ebirth_to_C3 (29 + 46 * 30 + w * 125 * 77) r1 (eq_mp_rev hn1 (by eq_omega))
  exact ⟨s, hs, ReachesPlus.trans (eq_mp_rev hb (by eq_omega)) (eq_mp_rev he (by eq_omega))⟩

private theorem Num_tight_odd3_boundary (n : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (5 + n * 6) r) :
    ∃ s, Num true (9 + n * 6) s ∧
      ((root ((X ^ (2 + n)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ([0] +> (Y +> ((X ^ (6 + n * 3)) +> ([0] +> (X +> ([0, 0] +> s)))))))) := by
  obtain ⟨r1, HN1, H3⟩ := Num_add 3 false (5 + n * 6) r HN
  obtain ⟨r2, HN2, HF⟩ := CutNum_Fs (10 + n * 6) false (5 + n * 6 + 3) 0 r1 HN1 (by omega)
  obtain ⟨s, HS, E2⟩ := CutNum_digit_tail false false (5 + n * 6 + 3 + (10 + n * 6)) (9 + n * 6)
    (0 + (10 + n * 6)) 0 r2 HN2 (by cond_omega) (by cond_omega)
  have HH : SideRLs tm40 (h ^ (5 + n * 3)) (Y +> r1)
      ((X ^ (5 + n * 3)) +> ([0] +> (X +> r2))) :=
    eq_mp_rev (Y_hs (4 + n * 3) r1 r2 (eq_mp_rev HF (by eq_omega))) (by eq_omega)
  refine ⟨s, HS, ?_⟩
  refine ReachesPlus.trans (eq_mp_rev (odd_three (1 + n) r r1 H3) (by eq_omega)) ?_
  have h_nt := normal_truncated (1 + n) (Y +> r1) _ (eq_mp_rev HH (by eq_omega))
  rw [E2] at h_nt
  exact eq_mp_rev h_nt (by (try dsimp only [sep]); eq_omega)

private theorem Num_tight_odd3_odd (t : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (11 + t * 12) r) :
    ∃ s, Num true (36 + t * 24) s ∧
      ((root ((X ^ (3 + t * 2)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (7 + t * 4)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, HB⟩ := Num_tight_odd3_boundary (1 + t * 2) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨r2, HN2, HZ⟩ :=
    CutNum_zeroY_even (8 + t * 6) true (9 + (1 + t * 2) * 6) 0 r1 HN1 (by omega)
  obtain ⟨r3, HN3, E2⟩ := CutNum_digit_tail true false
    _ (21 + t * 15) _ (6 + t * 3) r2 HN2 (by cond_omega) (by cond_omega)
  obtain ⟨r4, HN4, HN0⟩ := Num_normal (4 + t * 3) false (21 + t * 15) r3 HN3
  obtain ⟨r5, HN5, E4⟩ := CutNum_digit_tail false false
    _ (18 + t * 12) 0 (19 + t * 12) r4 HN4 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_markers (6 + t * 4) 0 1 true (18 + t * 12) r5 HN5
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev HB (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev HZ (by eq_omega)) ?_
  rw [E2]
  try dsimp only [sep]
  refine plus_star_left_eq HN0 (by eq_omega) ?_
  rw [E4]
  try dsimp only [sep]
  exact eq_mp_rev HM (by eq_omega)

private theorem Num_C3_two (v : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (55 + v * 168) r) :
    ∃ s, Num false (83 + v * 240) s ∧
      ((root ((X ^ (2 + v * 4)) +>
        ([0] +> ((X ^ (22 + v * 60)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (4 + v * 9)) +>
          ([0] +> ((X ^ (4 + v * 6)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))))) := by
  obtain ⟨r1, HN1, HC⟩ := CutNum_C3 (v * 4) (20 + v * 60) true (55 + v * 168) 0 r HN (by omega)
  obtain ⟨r2, HN2, HZ⟩ := CutNum_zeroY00_even (v * 2) true _ _ r1 HN1 (by omega)
  obtain ⟨r3, HN3, H3⟩ := CutNum_hs 3 true _ _ r2 HN2 (by omega)
  obtain ⟨r4, HN4, HY⟩ := CutNum_normalY (v * 2) true _ _ r3 HN3 (by omega)
  obtain ⟨r5, HN5, E4⟩ :=
    CutNum_digit_tail true false _ (65 + v * 186) _ (20 + v * 54) r4 HN4 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, HS, HM⟩ :=
    Num_two_markers (3 + v * 9) 0 (3 + v * 6) 1 false false (65 + v * 186) r5 HN5
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev HC (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev HZ (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev (odd_three (v * 2) r2 r3 H3) (by eq_omega)) ?_
  refine plus_star_left_eq HY (by eq_omega) ?_
  rw [E4]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_C3_odd_source (w : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (223 + w * 336) r) :
    ∃ s, Num false (689 + w * 169 * 6) s ∧
      ((root ((X ^ (6 + w * 8)) +>
        ([0] +> ((X ^ (82 + w * 120)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (116 + w * 169)) +> ([0] +> ((X ^ 3) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, HN1, HC⟩ := Num_C3_two (1 + w * 2) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨r2, HN2, HS0⟩ :=
    CutNum_C_short (12 + w * 18) (9 + w * 12) false (83 + (1 + w * 2) * 240) 0 r1 HN1 (by omega)
  have HN3 : CutNum false (357 + w * 516) (7 + w * 6) ((X ^ (16 + w * 18)) +> r2) :=
    CutNum_prepend false (357 + w * 516) (7 + w * 6) (16 + w * 18) r2
      (CutNum_cast (by omega) (by omega) HN2)
  obtain ⟨r3, HN4, E3⟩ := CutNum_digit_tail false true (357 + w * 516) (178 + w * 258)
    (7 + w * 6) (172 + w * 252) ((X ^ (16 + w * 18)) +> r2) HN3 (by cond_omega) (by cond_omega)
  obtain ⟨r4, HN5, HN0⟩ := Num_normal_odd (170 + w * 252) true (178 + w * 258) r3 HN4
  obtain ⟨r5, HN6, E4⟩ := CutNum_digit_tail true true
    _ (344 + w * 507) 0 (347 + w * 507) r4 HN5 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_marker_phase (115 + w * 169) 0 2 true false (344 + w * 507) r5 HN6
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev HC (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev HS0 (by eq_omega)) ?_
  have h_eq : 4 + (12 + w * 18) = 16 + w * 18 := by omega
  rw [h_eq, E3]
  try dsimp only [sep]
  refine plus_star_left_eq HN0 (by eq_omega) ?_
  rw [E4]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_C3_to_even2 (z : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (559 + z * 672) r) :
    ∃ s, Num true (36 + (141 + z * 169) * 24) s ∧
      ((root ((X ^ (14 + z * 16)) +>
        ([0] +> ((X ^ (202 + z * 240)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (571 + z * 676)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))) := by
  obtain ⟨t, HT, HC⟩ := Num_C3_odd_source (1 + z * 2) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨s, HS, HE⟩ := Num_tight_odd3_odd (141 + z * 169) t (eq_mp_rev HT (by eq_omega))
  refine ⟨s, HS, ?_⟩
  exact ReachesPlus.trans (eq_mp_rev HC (by eq_omega)) (eq_mp_rev HE (by eq_omega))

private theorem Num_B21_to_even2 (t : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (90 + (9 + t * 32) * 576) r) :
    ∃ s, Num true (36 + (141 + (58 + 90 * 30 + t * 125 * 77) * 169) * 24) s ∧
      ((root ((X ^ (16 + (9 + t * 32) * 96)) +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (571 + (58 + 90 * 30 + t * 125 * 77) * 676)) +>
          ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, HB⟩ := Num_B21_to_C3 (1 + t * 4) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨s, HS, HC⟩ :=
    Num_C3_to_even2 (58 + 90 * 30 + t * 125 * 77) r1 (eq_mp_rev HN1 (by eq_omega))
  refine ⟨s, HS, ?_⟩
  exact ReachesPlus.trans (eq_mp_rev HB (by eq_omega)) (eq_mp_rev HC (by eq_omega))

private theorem Num_even2_first (t : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (60 + t * 144) r) :
    ∃ s, Num false (69 + t * 168) s ∧
      ((root ((X ^ (11 + t * 24)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (5 + t * 10)) +> ([0] +> (X +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))))) := by
  obtain ⟨r1, HN1, HE⟩ := CutNum_even2 (9 + t * 24) true (60 + t * 144) 0 r HN (by omega)
  obtain ⟨r2, HN2, E⟩ := CutNum_digit_tail true false
    (60 + t * 144 + 19 + (9 + t * 24) * 3) (51 + t * 108)
    (0 + 15 + (9 + t * 24) * 2) (21 + t * 60) r1 HN1 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_two_markers (3 + t * 10) 1 0 2 false false (51 + t * 108) r2 HN2
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine plus_star_left_eq HE (by eq_omega) ?_
  rw [E]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_even2_second (t : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (60 + t * 144) r) :
    ∃ s, CutNum false (109 + t * 213) (18 + t * 10) s ∧
      ((root ((X ^ (11 + t * 24)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ 2) +> ([0] +> (X +> ([0] +> s)))))) := by
  obtain ⟨r1, HN1, H1⟩ := Num_even2_first t r HN
  obtain ⟨r2, HN2, H2⟩ := CutNum_C2_three (3 + t * 10) false (69 + t * 168) 0 r1 HN1 (by omega)
  obtain ⟨r3, HN3, H3⟩ :=
    CutNum_zeroY00_odd (1 + t * 5) false (69 + t * 168 + 5) (0 + 1) r2 HN2 (by omega)
  obtain ⟨s, HS, H4⟩ := CutNum_even2 (1 + t * 5) false
    (69 + t * 168 + 5 + 7 + (1 + t * 5) * 6) (0 + 1) r3 HN3 (by omega)
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans H1 ?_
  refine ReachesPlus.trans (eq_mp_rev H2 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H3 (by eq_omega)) (eq_mp_rev H4 (by eq_omega))

private theorem Num_even2_to_C2 (s : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (348 + s * 144 * 12) r) :
    ∃ t, Num true (495 + s * 203 * 12) t ∧
      ((root ((X ^ (59 + s * 288)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (40 + s * 193)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> t)))))))))
          := by
  obtain ⟨r1, HN1, HE⟩ := Num_even2_second (2 + s * 12) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨r2, HN2, E⟩ := CutNum_digit_tail false true
    (109 + (2 + s * 12) * 213) (267 + s * 213 * 6)
    (18 + (2 + s * 12) * 10) (230 + s * 193 * 6) r1 HN1 (by cond_omega) (by cond_omega)
  obtain ⟨t, HT, HM⟩ := Num_two_markers (38 + s * 193) 1 0 1 true true (267 + s * 213 * 6) r2 HN2
  refine ⟨t, eq_mp_rev HT (by eq_omega), ?_⟩
  refine plus_star_left_eq HE (by eq_omega) ?_
  rw [E]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_three_markers (m p b c a : ℕ) (e chi : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (HN : Num chi j r) :
    ∃ s, Num chi (j + m * 12) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + c)) +> ([0] +>
        ((X ^ (1 + a + m * 12)) +> (sep e +> r))))))))) [tm40]⊢*
        (root ((X ^ (1 + p + m)) +> ([0] +> ((X ^ (1 + b)) +> ([0] +> ((X ^ (1 + c)) +> ([0] +>
          ((X ^ (1 + a)) +> (sep e +> s)))))))))) := by
  obtain ⟨s, HS, HH⟩ := Num_add (m * 12) chi j r HN
  have HF : SideRLs tm40 (hf ^ (m * 24))
      ((X ^ (a + m * 12)) +> (sep e +> r)) ((X ^ a) +> (sep e +> s)) :=
    eq_mp_rev (F_pairs_side (m * 12) a e r s HH) (by eq_omega)
  have HM1 := F_markers (m * 12) c _ _ (eq_mp_rev HF (by eq_omega))
  have HM2 := F_markers (m * 6) b _ _ (eq_mp_rev HM1 (by eq_omega))
  refine ⟨s, HS, ?_⟩
  exact eq_mp_rev (marker_calls m p _ _ (eq_mp_rev HM2 (by eq_omega))) (by eq_omega)

private theorem Num_C2_to_post (v : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (495 + v * 812 * 12) r) :
    ∃ s, Num false (486 + v * 812 * 12) s ∧
      ((root ((X ^ (40 + v * 772)) +> ([0] +> (X +> ([0] +> ((X ^ 2) +> ([0] +> (Y +> r))))))))
        [tm40]⊢⁺
        (root ((X ^ (11 + v * 213)) +> ([0] +> (X +> ([0] +> ((X ^ (41 + v * 772)) +> ([0] +>
          ((X ^ 10) +> ([0] +> (Y +> s))))))))))) := by
  obtain ⟨r1, HN1, HC⟩ := CutNum_C2_odd (37 + v * 772) true (495 + v * 812 * 12) 0 r HN (by omega)
  obtain ⟨r2, HN2, HP⟩ := CutNum_C2_post (40 + v * 772) true
    (495 + v * 812 * 12 + 20 + (37 + v * 772) * 6) (0 + 17 + (37 + v * 772) * 6) r1 HN1 (by omega)
  obtain ⟨r3, HN3, E⟩ := CutNum_digit_tail true true
    (495 + v * 812 * 12 + 20 + (37 + v * 772) * 6 + 24) (378 + v * 599 * 12)
    (0 + 17 + (37 + v * 772) * 6 + 24) (118 + v * 213 * 12) r2 HN2 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_three_markers (9 + v * 213) 1 0 (40 + v * 772) 9 true false
    (378 + v * 599 * 12) r3 HN3
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev HC (by eq_omega)) ?_
  refine plus_star_left_eq HP (by eq_omega) ?_
  rw [E]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_even2_to_post (v : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (348 + v * 576 * 12) r) :
    ∃ s, Num false (486 + v * 812 * 12) s ∧
      ((root ((X ^ (59 + v * 288 * 4)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (11 + v * 213)) +> ([0] +> (X +> ([0] +> ((X ^ (41 + v * 772)) +> ([0] +>
          ((X ^ 10) +> ([0] +> (Y +> s))))))))))) := by
  obtain ⟨r1, HN1, HE⟩ := Num_even2_to_C2 (v * 4) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨s, HS, HC⟩ := Num_C2_to_post v r1 (eq_mp_rev HN1 (by eq_omega))
  refine ⟨s, HS, ?_⟩
  exact ReachesPlus.trans (eq_mp_rev HE (by eq_omega)) HC

private theorem Num_B21_to_C2post (w : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (90 + (9 + (42 + w * 288) * 32) * 576) r) :
    ∃ s, Num false (486 + (35 + 796 * 300 + w * 169 * 125 * 77) * 812 * 12) s ∧
      ((root ((X ^ (16 + (9 + (42 + w * 288) * 32) * 96)) +>
        ([0] +> ((X ^ 2) +> ([0] +> (Y +> r)))))) [tm40]⊢⁺
        (root ((X ^ (11 + (35 + 796 * 300 + w * 169 * 125 * 77) * 213)) +> ([0] +> (X +> ([0] +>
          ((X ^ (41 + (35 + 796 * 300 + w * 169 * 125 * 77) * 772)) +>
            ([0] +> ((X ^ 10) +> ([0] +> (Y +> s))))))))))) := by
  obtain ⟨r1, HN1, HB⟩ := Num_B21_to_even2 (42 + w * 288) r HN
  obtain ⟨s, HS, HC⟩ := Num_even2_to_post (35 + 796 * 300 + w * 169 * 125 * 77) r1
    (eq_mp_rev HN1 (by eq_omega))
  refine ⟨s, HS, ?_⟩
  exact ReachesPlus.trans HB (eq_mp_rev HC (by eq_omega))

private theorem init_C2_post :
    ∃ r, Num false (486 + (35 + 796 * 300) * 812 * 12) r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ (11 + (35 + 796 * 300) * 213)) +> ([0] +> (X +> ([0] +>
          ((X ^ (41 + (35 + 796 * 300) * 772)) +> ([0] +> ((X ^ 10) +> ([0] +> (Y +> r)))))))))))
            := by
  obtain ⟨r, HN, HR⟩ := init_B21
  obtain ⟨s, HS, HC⟩ := Num_B21_to_C2post 0 r (eq_mp_rev HN (by eq_omega))
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  exact ReachesStar.trans HR (ReachesPlus.to_star (eq_mp_rev HC (by eq_omega)))

private theorem Num_mixed_pair_batch (m p b c a : ℕ) (e f chi : Bool) (j : ℕ)
    (r : ListBlank (Fin 2))
    (HN : Num chi j r) :
    ∃ s, Num chi (j + m * 6) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ (1 + b + m * 6)) +> (sep e +>
        ((X ^ (1 + c)) +> ([0] +> ((X ^ (1 + a + m * 6)) +> (sep f +> r))))))))))) [tm40]⊢*
        (root ((X ^ (1 + p + m)) +> ([0] +> (X +> ([0] +> ((X ^ (1 + b)) +> (sep e +>
          ((X ^ (1 + c + m * 6)) +> ([0] +> ((X ^ (1 + a)) +> (sep f +> s)))))))))))) := by
  obtain ⟨s, HS, HH⟩ := Num_add (m * 6) chi j r HN
  have HF : SideRLs tm40 (hf ^ (m * 12))
      ((X ^ (a + m * 6)) +> (sep f +> r)) ((X ^ a) +> (sep f +> s)) :=
    eq_mp_rev (F_pairs_side (m * 6) a f r s HH) (by eq_omega)
  have HM : SideRLs tm40 (h ^ (m * 6))
      ((X ^ (1 + c)) +> ([0] +> ((X ^ (1 + a + m * 6)) +> (sep f +> r))))
      ((X ^ (1 + c + m * 6)) +> ([0] +> ((X ^ (1 + a)) +> (sep f +> s)))) := by
    have h_col := h_columns [] (m * 6) (1 + c)
      ((X ^ (a + m * 6)) +> (sep f +> r)) ((X ^ a) +> (sep f +> s))
      (eq_mp_rev HF (by (try dsimp only [List.length]); eq_omega))
    try dsimp only [markers] at h_col
    exact eq_mp_rev h_col (by eq_omega)
  have HG : SideRLs tm40 (hf ^ (m * 12))
      ((X ^ (b + m * 6)) +>
        (sep e +> ((X ^ (1 + c)) +> ([0] +> ((X ^ (1 + a + m * 6)) +> (sep f +> r))))))
      ((X ^ b) +> (sep e +> ((X ^ (1 + c + m * 6)) +> ([0] +> ((X ^ (1 + a)) +> (sep f +> s)))))) :=
    eq_mp_rev (F_pairs_side (m * 6) b e _ _ HM) (by eq_omega)
  refine ⟨s, HS, ?_⟩
  have h_fm := F_markers (m * 6) 0 _ _ (eq_mp_rev HG (by eq_omega))
  exact eq_mp_rev (marker_calls m p _ _ h_fm) (by eq_omega)

private theorem Num_C2_spill (v : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (486 + v * 812 * 12) r) :
    ∃ s, Num true (249 + v * 406 * 12) s ∧
      ((root ((X ^ (11 + v * 213)) +>
        ([0] +> (X +>
        ([0] +> ((X ^ (41 + v * 772)) +> ([0] +> ((X ^ 10) +> ([0] +> (Y +> r)))))))))) [tm40]⊢⁺
        (root ((X ^ (12 + v * 213)) +>
          ([0] +> (X +> ([0] +> ((X ^ (40 + v * 772)) +> ([0, 0] +> (X +> ([0] +>
          ((X ^ (249 + v * 406 * 12)) +> ([0, 0] +> s)))))))))))) := by
  obtain ⟨t, HT, HC⟩ :=
    CutNum_odd10_spill (10 + v * 213) (39 + v * 772) false (486 + v * 812 * 12) 0 r HN (by omega)
  obtain ⟨s, HS, E⟩ := CutNum_digit_tail false false
    (486 + v * 812 * 12 + 12) (249 + v * 406 * 12)
    (0 + 1) (249 + v * 406 * 12) t HT (by cond_omega) (by cond_omega)
  refine ⟨s, HS, ?_⟩
  rw [E] at HC
  exact eq_mp_rev HC (by (try dsimp only [sep]); eq_omega)

private theorem Num_C2_to_mixed (w : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (486 + (2 + w * 3) * 812 * 12) r) :
    ∃ s, Num true (249 + (2 + w * 3) * 406 * 12 + (263 + w * 386) * 6) s ∧
      ((root ((X ^ (11 + (2 + w * 3) * 213)) +>
        ([0] +> (X +> ([0] +> ((X ^ (41 + (2 + w * 3) * 772)) +> ([0] +>
        ((X ^ 10) +> ([0] +> (Y +> r)))))))))) [tm40]⊢⁺
        (root ((X ^ (701 + w * 205 * 5)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
          ((X ^ (1 + (263 + w * 386) * 6)) +>
            ([0] +> ((X ^ (15 + (28 + w * 41) * 300)) +> ([0, 0] +> s)))))))))))) := by
  obtain ⟨t, HT, HS⟩ := Num_C2_spill (2 + w * 3) r HN
  obtain ⟨s, HN1, HB⟩ := Num_mixed_pair_batch (263 + w * 386) (11 + (2 + w * 3) * 213) 5 0
    (14 + (28 + w * 41) * 300) false false true (249 + (2 + w * 3) * 406 * 12) t HT
  refine ⟨s, HN1, ?_⟩
  exact plus_star_trans_eq HS (eq_mp_rev HB (by dsimp only [sep])) (by eq_omega)

private theorem Num_C2_mixed_source (u : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (486 + (35 + u * 300) * 812 * 12) r) :
    ∃ s, Num true (249 + (2 + (11 + u * 100) * 3) * 406 * 12 + (263 + (11 + u * 100) * 386) * 6) s ∧
      ((root ((X ^ (11 + (35 + u * 300) * 213)) +>
        ([0] +> (X +> ([0] +> ((X ^ (41 + (35 + u * 300) * 772)) +> ([0] +>
        ((X ^ 10) +> ([0] +> (Y +> r)))))))))) [tm40]⊢⁺
        (root ((X ^ (701 + (11 + u * 100) * 205 * 5)) +>
          ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
          ((X ^ (1 + (263 + (11 + u * 100) * 386) * 6)) +>
            ([0] +> ((X ^ (15 + (28 + (11 + u * 100) * 41) * 300)) +> ([0, 0] +> s)))))))))))) := by
  obtain ⟨s, HS, HC⟩ := Num_C2_to_mixed (11 + u * 100) r (eq_mp_rev HN (by eq_omega))
  exact ⟨s, HS, eq_mp_rev HC (by eq_omega)⟩

private theorem init_C2_mixed :
    ∃ r, Num true
      (249 + (2 + (11 + 796 * 100) * 3) * 406 * 12 + (263 + (11 + 796 * 100) * 386) * 6) r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ (701 + (11 + 796 * 100) * 205 * 5)) +>
          ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
          ((X ^ (1 + (263 + (11 + 796 * 100) * 386) * 6)) +>
            ([0] +> ((X ^ (15 + (28 + (11 + 796 * 100) * 41) * 300)) +> ([0, 0] +> r)))))))))))) :=
            by
  obtain ⟨r, HN, HR⟩ := init_C2_post
  obtain ⟨s, HS, HC⟩ := Num_C2_mixed_source 796 r HN
  exact ⟨s, HS, ReachesStar.trans HR (ReachesPlus.to_star HC)⟩

private theorem Num_C_even6_marked (p b a : ℕ) (chi : Bool) (j : ℕ) (r : ListBlank (Fin 2))
    (HN : Num chi j r) :
    ∃ s, Num chi (j + 9) s ∧
      ((root ((X ^ (1 + p)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
        ((X ^ b) +> ([0] +> ((X ^ (10 + a)) +> ([0, 0] +> r))))))))))) [tm40]⊢⁺
        (root ((X ^ (10 + p + b)) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> s)))))) := by
  obtain ⟨s, HS, HH⟩ := Num_add 9 chi j r HN
  have HF : SideRLs tm40 (hf ^ 18)
      ((X ^ (a + 9)) +> ([0, 0] +> r)) ((X ^ a) +> ([0, 0] +> s)) :=
    F_pairs_even_side 9 a _ _ HH
  have HM : SideRLs tm40 (hf ^ 9)
      ((X ^ b) +> ([0] +> ((X ^ (10 + a)) +> ([0, 0] +> r))))
      ((X ^ b) +> ([0] +> ((X ^ (1 + a)) +> ([0, 0] +> s)))) :=
    eq_mp_rev (F_markers 9 b _ _ HF) (by eq_omega)
  refine ⟨s, HS, ?_⟩
  exact eq_mp_rev (C_even6_calls p _ _ HM) (by eq_omega)

private theorem Num_C2_collapse_first (w : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((571 + 11 * 1000) + w * (932 + 16 * 1000)) r) :
    ∃ s, Num true ((983 + 19 * 1000) + w * (232 + 29 * 1000)) s ∧
      ((root ((X ^ (701 + w * 1025)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
        ((X ^ (1579 + w * 2316)) +>
          ([0] +> ((X ^ ((415 + 8 * 1000) + w * (300 + 12 * 1000))) +> ([0, 0] +> r)))))))))))
          [tm40]⊢⁺
        (root ((X ^ ((90 + 5 * 1000) + w * (441 + 7 * 1000))) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨t, HT, HE⟩ := Num_C_even6_marked (700 + w * 1025) (1579 + w * 2316)
    ((405 + 8 * 1000) + w * (300 + 12 * 1000)) true
    ((571 + 11 * 1000) + w * (932 + 16 * 1000)) r HN
  obtain ⟨s, HS, HM⟩ := Num_markers (2801 + w * 4100) (2288 + w * 3341) 2 true
    ((571 + 11 * 1000) + w * (932 + 16 * 1000) + 9) t HT
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  exact plus_star_trans_eq (eq_mp_rev HE (by eq_omega)) (eq_mp_rev HM (by eq_omega)) (by eq_omega)

private theorem Num_C2_collapse_odd (z : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((571 + 11 * 1000) + (1 + z * 2) * (932 + 16 * 1000)) r) :
    ∃ s, Num true ((437 + 98 * 1000) + z * (928 + 116 * 1000)) s ∧
      ((root ((X ^ (701 + (1 + z * 2) * 1025)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
        ((X ^ (1579 + (1 + z * 2) * 2316)) +>
          ([0] +> ((X ^ ((415 + 8 * 1000) + (1 + z * 2) * (300 + 12 * 1000))) +>
          ([0, 0] +> r))))))))))) [tm40]⊢⁺
        (root ((X ^ ((407 + 16 * 1000) + z * (488 + 19 * 1000))) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, HC⟩ := Num_C2_collapse_first (1 + z * 2) r HN
  obtain ⟨r2, HN2, HA⟩ :=
    CutNum_a3 ((530 + 12 * 1000) + z * (882 + 14 * 1000)) true _ 0 r1 HN1 (by omega)
  obtain ⟨r3, HN3, E2⟩ := CutNum_digit_tail true true _
    ((404 + 43 * 1000) + z * (555 + 51 * 1000)) _
    ((345 + 18 * 1000) + z * (791 + 21 * 1000)) r2 HN2 (by cond_omega) (by cond_omega)
  obtain ⟨r4, HN4, HN0⟩ := Num_normal_odd ((343 + 18 * 1000) + z * (791 + 21 * 1000)) false
    ((404 + 43 * 1000) + z * (555 + 51 * 1000)) r3 HN3
  obtain ⟨r5, HN5, E4⟩ := CutNum_digit_tail false false _
    ((219 + 49 * 1000) + z * (464 + 58 * 1000)) 0
    ((220 + 49 * 1000) + z * (464 + 58 * 1000)) r4 HN4 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_markers ((406 + 16 * 1000) + z * (488 + 19 * 1000)) 0 2 true
    ((219 + 49 * 1000) + z * (464 + 58 * 1000)) r5 HN5
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans HC ?_
  refine ReachesPlus.trans (eq_mp_rev HA (by eq_omega)) ?_
  rw [E2]
  try dsimp only [sep]
  refine plus_star_left_eq HN0 (by eq_omega) ?_
  rw [E4]
  try dsimp only [sep]
  exact eq_mp_rev HM (by eq_omega)

private theorem Num_C2_collapse_source (u : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true
      (249 + (2 + (11 + u * 100) * 3) * 406 * 12 + (263 + (11 + u * 100) * 386) * 6) r) :
    ∃ s, Num true ((437 + 98 * 1000) + (5 + u * 50) * (928 + 116 * 1000)) s ∧
      ((root ((X ^ (701 + (11 + u * 100) * 205 * 5)) +> ([0] +> (X +> ([0] +> ((X ^ 6) +> ([0, 0] +>
        ((X ^ (1 + (263 + (11 + u * 100) * 386) * 6)) +>
          ([0] +> ((X ^ (15 + (28 + (11 + u * 100) * 41) * 300)) +> ([0, 0] +> r))))))))))) [tm40]⊢⁺
        (root ((X ^ ((407 + 16 * 1000) + (5 + u * 50) * (488 + 19 * 1000))) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨s, HS, HC⟩ := Num_C2_collapse_odd (5 + u * 50) r (eq_mp_rev HN (by eq_omega))
  exact ⟨s, HS, eq_mp_rev HC (by eq_omega)⟩

private theorem init_C2_collapse :
    ∃ r, Num true ((437 + 98 * 1000) + (5 + 796 * 50) * (928 + 116 * 1000)) r ∧
      ((init []) [tm40]⊢*
        (root ((X ^ ((407 + 16 * 1000) + (5 + 796 * 50) * (488 + 19 * 1000))) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> r)))))) := by
  obtain ⟨r, HN, HR⟩ := init_C2_mixed
  obtain ⟨s, HS, HC⟩ := Num_C2_collapse_source 796 r HN
  exact ⟨s, HS, ReachesStar.trans HR (ReachesPlus.to_star HC)⟩

private theorem Num_C_odd (n : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false (82 + n * 228) r) :
    ∃ s, Num false (177 + n * 462) s ∧
      ((root ((X ^ (2 + n * 2)) +>
        ([0] +> ((X ^ (37 + n * 102)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))))) [tm40]⊢⁺
        (root ((X ^ (31 + n * 77)) +> ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, HC⟩ := Num_C_short (n * 2) r (eq_mp_rev HN (by eq_omega))
  obtain ⟨r2, HN2, E1⟩ :=
    CutNum_digit_tail false true _ (98 + n * 267) _ (27 + n * 65) r1 HN1 (by cond_omega)
    (by cond_omega)
  obtain ⟨r3, HN3, HN0⟩ := Num_normal_odd (25 + n * 65) true (98 + n * 267) r2 HN2
  obtain ⟨r4, HN4, E3⟩ :=
    CutNum_digit_tail true false _ (87 + n * 231) 0 (90 + n * 231) r3 HN3 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_markers (30 + n * 77) 0 0 false (87 + n * 231) r4 HN4
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev HC (by eq_omega)) ?_
  rw [E1]
  try dsimp only [sep]
  refine plus_star_left_eq HN0 (by eq_omega) ?_
  rw [E3]
  try dsimp only [sep]
  exact eq_mp_rev HM (by eq_omega)

private theorem Num_C2_to_scalar_C (u : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((437 + 98 * 1000) + (5 + u * 50) * (928 + 116 * 1000)) r) :
    ∃ s, Num false (177 + ((577 + 35 * 1000) + u * (500 + 304 * 1000)) * 462) s ∧
      ((root ((X ^ ((407 + 16 * 1000) + (5 + u * 50) * (488 + 19 * 1000))) +>
        ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (31 + ((577 + 35 * 1000) + u * (500 + 304 * 1000)) * 77)) +>
          ([0] +> (X +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, H1⟩ := Num_Oa3_odd_return ((922 + 56 * 1000) + u * (200 + 487 * 1000)) r
    (eq_mp_rev HN (by eq_omega))
  obtain ⟨r2, HN2, H2⟩ := Num_one_mod6_even ((487 + 9 * 1000) + u * (200 + 81 * 1000)) r1
    (eq_mp_rev HN1 (by eq_omega))
  obtain ⟨r3, HN3, H3⟩ := Num_critical_odd ((436 + 47 * 1000) + u * (0 + 406 * 1000)) r2
    (eq_mp_rev HN2 (by eq_omega))
  obtain ⟨r4, HN4, H4⟩ := Num_A2_to_C ((154 + 71 * 1000) + u * (0 + 609 * 1000)) r3
    (eq_mp_rev HN3 (by eq_omega))
  obtain ⟨s, HS, H5⟩ := Num_C_odd ((577 + 35 * 1000) + u * (500 + 304 * 1000)) r4
    (eq_mp_rev HN4 (by eq_omega))
  refine ⟨s, HS, ?_⟩
  refine ReachesPlus.trans (eq_mp_rev H1 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H2 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H3 (by eq_omega)) ?_
  exact ReachesPlus.trans (eq_mp_rev H4 (by eq_omega)) (eq_mp_rev H5 (by eq_omega))

private theorem Num_scalar_a1 (a : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false ((511 + 26 * 1000) + a * (264 + 33 * 1000)) r) :
    ∃ s, Num true ((932 + 30 * 1000) + a * (808 + 38 * 1000)) s ∧
      ((root ((X ^ (4420 + a * (544 + 5 * 1000))) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (3683 + a * 4620)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> s)))))) := by
  obtain ⟨t, HT, HA⟩ := CutNum_a1_odd (4419 + a * (544 + 5 * 1000)) false
    ((511 + 26 * 1000) + a * (264 + 33 * 1000)) 0
    ((885 + 19 * 1000) + a * (948 + 24 * 1000)) r HN (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_markers (3682 + a * 4620) 0 1 true _ t HT
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  exact plus_star_trans_eq (eq_mp_rev HA (by eq_omega)) (eq_mp_rev HM (by eq_omega)) (by eq_omega)

private theorem Num_scalar_even2 (a : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((932 + 30 * 1000) + a * (808 + 38 * 1000)) r) :
    ∃ s, Num false ((615 + 34 * 1000) + a * (428 + 43 * 1000)) s ∧
      ((root ((X ^ (3683 + a * 4620)) +> ([0] +> ((X ^ 2) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (2272 + a * 2849)) +> ([0] +> (X +> ([0] +> (X +> ([0, 0] +> s)))))))) := by
  obtain ⟨t, HT, HE⟩ := CutNum_even2 (3681 + a * 4620) true
    ((932 + 30 * 1000) + a * (808 + 38 * 1000)) 0 r HN (by omega)
  obtain ⟨u, HU, E⟩ := CutNum_digit_tail true false
    ((932 + 30 * 1000) + a * (808 + 38 * 1000) + 19 + (3681 + a * 4620) * 3)
    ((995 + 20 * 1000) + a * (334 + 26 * 1000))
    (0 + 15 + (3681 + a * 4620) * 2)
    ((621 + 13 * 1000) + a * (94 + 17 * 1000)) t HT (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_two_markers (2270 + a * 2849) 1 0 0 false false
    ((995 + 20 * 1000) + a * (334 + 26 * 1000)) u HU
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine plus_star_left_eq HE (by eq_omega) ?_
  rw [E]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_scalar_C1_return (c : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false ((615 + 34 * 1000) + (2 + c * 4) * (428 + 43 * 1000)) r) :
    ∃ s, Num false ((764 + 290 * 1000) + c * (800 + 415 * 1000)) s ∧
      ((root ((X ^ (2272 + (2 + c * 4) * 2849)) +> ([0] +> (X +> ([0] +> (X +> ([0, 0] +> r)))))))
        [tm40]⊢⁺
        (root ((X ^ ((462 + 48 * 1000) + c * (300 + 69 * 1000))) +>
          ([0] +> ((X ^ 2) +> ([0] +> (Y +> s))))))) := by
  obtain ⟨r1, HN1, H1⟩ := CutNum_C1_even (1135 + (1 + c * 2) * 2849) false
    ((615 + 34 * 1000) + (2 + c * 4) * (428 + 43 * 1000)) 0 r HN (by omega)
  obtain ⟨r2, HN2, HA⟩ := CutNum_a3 (3984 + c * (698 + 5 * 1000)) false _ _ r1 HN1 (by omega)
  obtain ⟨r3, HN3, E2⟩ := CutNum_digit_tail false false _
    ((670 + 78 * 1000) + c * (497 + 112 * 1000)) _
    ((700 + 70 * 1000) + c * (101 + 101 * 1000)) r2 HN2 (by cond_omega) (by cond_omega)
  obtain ⟨r4, HN4, HN0⟩ := Num_normal ((698 + 70 * 1000) + c * (101 + 101 * 1000)) true
    ((670 + 78 * 1000) + c * (497 + 112 * 1000)) r3 HN3
  obtain ⟨r5, HN5, E4⟩ := CutNum_digit_tail true true _
    ((381 + 145 * 1000) + c * (900 + 207 * 1000)) 0
    ((384 + 145 * 1000) + c * (900 + 207 * 1000)) r4 HN4 (by cond_omega) (by cond_omega)
  obtain ⟨s, HS, HM⟩ := Num_marker_phase ((461 + 48 * 1000) + c * (300 + 69 * 1000)) 0 1 true false
    ((381 + 145 * 1000) + c * (900 + 207 * 1000)) r5 HN5
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev H1 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev HA (by eq_omega)) ?_
  rw [E2]
  try dsimp only [sep]
  refine plus_star_left_eq HN0 (by eq_omega) ?_
  rw [E4]
  exact eq_mp_rev HM (by (try dsimp only [sep]); eq_omega)

private theorem Num_scalar_to_terminal (c : ℕ) (r : ListBlank (Fin 2))
    (HN : Num false ((511 + 26 * 1000) + (2 + c * 4) * (264 + 33 * 1000)) r) :
    ∃ s, Num true (143 + (4038 + c * (775 + 5 * 1000)) * 288) s ∧
      ((root ((X ^ (4420 + (2 + c * 4) * (544 + 5 * 1000))) +> ([0] +> (X +> ([0, 0] +> r)))))
        [tm40]⊢⁺
        (root ((X ^ (25 + (4038 + c * (775 + 5 * 1000)) * 48)) +> ([0] +> (X +> ([0, 0] +> s))))))
          := by
  obtain ⟨r1, HN1, H1⟩ := Num_scalar_a1 (2 + c * 4) r HN
  obtain ⟨r2, HN2, H2⟩ := Num_scalar_even2 (2 + c * 4) r1 HN1
  obtain ⟨r3, HN3, H3⟩ := Num_scalar_C1_return c r2 HN2
  obtain ⟨s, HS, H4⟩ := Num_Ebirth_even_return ((229 + 24 * 1000) + c * (650 + 34 * 1000)) r3
    (eq_mp_rev HN3 (by eq_omega))
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans H1 ?_
  refine ReachesPlus.trans H2 ?_
  exact ReachesPlus.trans H3 (eq_mp_rev H4 (by eq_omega))

private theorem Num_terminal_Q (v : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true (143 + v * 288) r) :
    ∃ s, Num false (521 + v * 1014) s ∧
      ((root ((X ^ (25 + v * 48)) +> ([0] +> (X +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (88 + v * 169)) +> ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, H1⟩ := CutNum_a1_even (24 + v * 48) true (143 + v * 288) 0
    (107 + v * 216) (60 + v * 120) r HN (by cond_omega) (by cond_omega) (by cond_omega)
  obtain ⟨r2, HN2, H2⟩ := Num_marker_phase (20 + v * 40) 0 0 true false (107 + v * 216) r1 HN1
  obtain ⟨r3, HN3, H3⟩ := CutNum_odd1 (19 + v * 40) false _ 0 r2 HN2 (by omega)
  obtain ⟨r4, HN4, E3⟩ :=
    CutNum_digit_tail false false _ (145 + v * 288) _ (25 + v * 48) r3 HN3 (by cond_omega)
    (by cond_omega)
  obtain ⟨r5, HN5, H5⟩ :=
    Num_two_markers (4 + v * 8) 0 (61 + v * 120) 0 false true (145 + v * 288) r4 HN4
  obtain ⟨r6, HN6, H6⟩ :=
    CutNum_nested_even_front (4 + v * 8) (60 + v * 120) true _ 0 r5 HN5 (by omega)
  obtain ⟨r7, HN7, H7⟩ := CutNum_zero4_leading_odd (1 + v * 4) true _ _ r6 HN6 (by omega)
  obtain ⟨r8, HN8, H8⟩ := CutNum_odd1 (1 + v * 4) true _ _ r7 HN7 (by omega)
  obtain ⟨r9, HN9, E8⟩ :=
    CutNum_digit_tail true false _ (189 + v * 372) _ (56 + v * 108) r8 HN8 (by cond_omega)
    (by cond_omega)
  obtain ⟨r10, HN10, H10⟩ :=
    Num_two_markers (9 + v * 18) 0 (7 + v * 12) 1 false false (189 + v * 372) r9 HN9
  obtain ⟨r11, HN11, H11⟩ := CutNum_C_short (9 + v * 18) (7 + v * 12) false _ 0 r10 HN10 (by omega)
  have HN12 : CutNum false (271 + v * 516) (6 + v * 6) ((X ^ (13 + v * 18)) +> r11) :=
    CutNum_prepend false (271 + v * 516) (6 + v * 6) (13 + v * 18) r11
      (CutNum_cast (by omega) (by omega) HN11)
  obtain ⟨r12, HN13, E11⟩ :=
    CutNum_digit_tail false true _ (135 + v * 258) _ (130 + v * 252)
    ((X ^ (13 + v * 18)) +> r11) HN12 (by cond_omega) (by cond_omega)
  obtain ⟨r13, HN14, H12⟩ := Num_normal_odd (128 + v * 252) true (135 + v * 258) r12 HN13
  obtain ⟨r14, HN15, E13⟩ :=
    CutNum_digit_tail true false _ (260 + v * 507) 0 (263 + v * 507) r13 HN14 (by cond_omega)
    (by cond_omega)
  obtain ⟨s, HS, H14⟩ := Num_markers (87 + v * 169) 0 2 false (260 + v * 507) r14 HN15
  refine ⟨s, eq_mp_rev HS (by eq_omega), ?_⟩
  refine ReachesPlus.trans (eq_mp_rev H1 (by eq_omega)) ?_
  refine ReachesStar.trans_plus (eq_mp_rev H2 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H3 (by eq_omega)) ?_
  rw [E3]
  refine ReachesStar.trans_plus (eq_mp_rev H5 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H6 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H7 (by eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H8 (by eq_omega)) ?_
  rw [E8]
  refine ReachesStar.trans_plus (eq_mp_rev H10 (by (try dsimp only [sep]); eq_omega)) ?_
  refine ReachesPlus.trans (eq_mp_rev H11 (by eq_omega)) ?_
  have h_eq : 4 + (9 + v * 18) = 13 + v * 18 := by omega
  rw [h_eq, E11]
  try dsimp only [sep]
  refine plus_star_left_eq H12 (by eq_omega) ?_
  rw [E13]
  try dsimp only [sep]
  exact eq_mp_rev H14 (by eq_omega)

private theorem Num_C2_to_Q (d : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((437 + 98 * 1000) + (5 + (4 + d * 24) * 50) * (928 + 116 * 1000)) r) :
    ∃ s, Num false (521 + (4038 + (4352 + d * (375 + 25 * 1000)) * (775 + 5 * 1000)) * 1014) s ∧
      ((root ((X ^ ((407 + 16 * 1000) + (5 + (4 + d * 24) * 50) * (488 + 19 * 1000))) +>
        ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺
        (root ((X ^ (88 + (4038 + (4352 + d * (375 + 25 * 1000)) * (775 + 5 * 1000)) * 169)) +>
          ([0] +> ((X ^ 3) +> ([0, 0] +> s)))))) := by
  obtain ⟨r1, HN1, H1⟩ := Num_C2_to_scalar_C (4 + d * 24) r HN
  obtain ⟨r2, HN2, H2⟩ := Num_scalar_to_terminal (4352 + d * (375 + 25 * 1000)) r1
    (eq_mp_rev HN1 (by eq_omega))
  obtain ⟨s, HS, H3⟩ :=
    Num_terminal_Q (4038 + (4352 + d * (375 + 25 * 1000)) * (775 + 5 * 1000)) r2 HN2
  refine ⟨s, HS, ?_⟩
  refine ReachesPlus.trans H1 ?_
  exact ReachesPlus.trans (eq_mp_rev H2 (by eq_omega)) H3

private theorem Num_C2_to_loop (d : ℕ) (r : ListBlank (Fin 2))
    (HN : Num true ((437 + 98 * 1000) + (5 + (4 + d * 24) * 50) * (928 + 116 * 1000)) r) :
    ∃ c, ((root ((X ^ ((407 + 16 * 1000) + (5 + (4 + d * 24) * 50) * (488 + 19 * 1000))) +>
      ([0] +> ((X ^ 3) +> ([0, 0] +> r))))) [tm40]⊢⁺ c) ∧ InLoop c := by
  obtain ⟨s, HS, HC⟩ := Num_C2_to_Q d r HN
  refine ⟨_, HC, ?_⟩
  have h_in :=
    InLoop.in_loop (86 + (4038 + (4352 + d * (375 + 25 * 1000)) * (775 + 5 * 1000)) * 169) s
    (eq_mp_rev HS (by eq_omega))
  exact eq_mp_rev h_in (congrArg InLoop (by eq_omega))

private theorem init_loop : ∃ c, ((init []) [tm40]⊢* c) ∧ InLoop c := by
  obtain ⟨r, HN, HR⟩ := init_C2_collapse
  have h796 : (796 : ℕ) = 4 + 33 * 24 := by decide
  rw [h796] at HN HR
  obtain ⟨c, HC, HL⟩ := Num_C2_to_loop 33 r HN
  exact ⟨c, ReachesStar.trans HR (ReachesPlus.to_star HC), HL⟩

private theorem tm40_eq_target : tm40 = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LA_1RC0RB_1LD1RB_0LA0LE_---1LF_1LA1LC` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← tm40_eq_target]
  obtain ⟨c₀, hinit, hloop⟩ := init_loop
  exact IsNotHalt.of_reachesPlus_invariant hinit hloop loop_progress

end

end BusyBeaver.M_1RB0LA_1RC0RB_1LD1RB_0LA0LE_HHH1LF_1LA1LC
