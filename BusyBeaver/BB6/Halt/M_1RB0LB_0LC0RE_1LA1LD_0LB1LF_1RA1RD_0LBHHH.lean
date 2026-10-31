/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

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
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
-- ============================================================================
-- Section 5: Specific Turing Machine: Suspect 117 (Holdout #737)
-- ============================================================================
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

-- ============================================================================
-- Section 6: Four Sound Concrete Steppers (`wstep`, `cstep`, `rcstep`, `bstep`)
-- ============================================================================

abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev wmultiStep := Counter.wmultiStep target_tm
abbrev cmultiStep := Counter.cmultiStep target_tm
abbrev rcmultiStep := Counter.rcmultiStep target_tm
abbrev bmultiStep := Counter.bmultiStep target_tm

-- ============================================================================
-- Section 6.3: Token & RLE Encoding (`Tok`, `Mode`, `Rle`, `evalRle`, `evalRStack`, `evalWK`)
-- ============================================================================

inductive Tok
  | U | M | W | Z | T | P | PTTTM_TAIL
  deriving DecidableEq, Repr

inductive Mode
  | R0 | R1 | R1_ODD
  deriving DecidableEq, Repr

def isZpWord : List Tok → Bool
  | [] => true
  | .Z :: ts => isZpWord ts
  | .P :: ts => isZpWord ts
  | _ :: _ => false

def revWord : List Tok → List Tok
  | [] => []
  | t :: ts => revWord ts ++ [t]

@[simp] lemma revWord_nil : revWord [] = [] := rfl
@[simp] lemma revWord_cons (t : Tok) (ts : List Tok) : revWord (t :: ts) = revWord ts ++ [t] := rfl

@[simp] lemma revWord_append (w₁ w₂ : List Tok) :
    revWord (w₁ ++ w₂) = revWord w₂ ++ revWord w₁ := by
  induction w₁ with
  | nil => simp
  | cons t ts ih => simp [ih, List.append_assoc]

@[simp] lemma revWord_revWord (w : List Tok) : revWord (revWord w) = w := by
  induction w with
  | nil => rfl
  | cons t ts ih => simp [ih]

@[simp] lemma isZpWord_append (w₁ w₂ : List Tok) :
    isZpWord (w₁ ++ w₂) = (isZpWord w₁ && isZpWord w₂) := by
  induction w₁ with
  | nil => simp [isZpWord]
  | cons t ts ih =>
    cases t <;> simp [isZpWord, ih]

@[simp] lemma isZpWord_revWord (w : List Tok) :
    isZpWord (revWord w) = isZpWord w := by
  induction w with
  | nil => rfl
  | cons t ts ih =>
    simp [isZpWord_append, ih]
    cases t <;> simp [isZpWord, Bool.and_comm]

def tokL : Tok → List (Fin 2)
  | .U => [0, 1]
  | .M => [0, 1, 1]
  | .W => [0, 0, 1, 1]
  | .Z => [0, 0, 0, 0, 1, 1]
  | .T => [0, 1, 1, 1]
  | .P => [0, 1, 0, 0, 1, 1]
  | .PTTTM_TAIL => []

def tokR : Tok → List (Fin 2)
  | .Z => [1, 0, 1, 1, 0, 1]
  | .P => [0, 0, 1, 1, 0, 1]
  | .PTTTM_TAIL => [1, 0, 1, 0, 0, 1, 1, 0, 1]
  | _ => []

def wordL : List Tok → List (Fin 2) := encWords tokL
def wordR : List Tok → List (Fin 2) := encWords tokR

@[simp] lemma wordL_nil : wordL [] = [] := encWords_nil tokL
@[simp] lemma wordL_cons (t : Tok) (ts : List Tok) : wordL (t :: ts) = tokL t ++ wordL ts := encWords_cons tokL t ts
@[simp] theorem wordL_append (w₁ w₂ : List Tok) : wordL (w₁ ++ w₂) = wordL w₁ ++ wordL w₂ := encWords_append tokL w₁ w₂
@[simp] lemma wordR_nil : wordR [] = [] := encWords_nil tokR
@[simp] lemma wordR_cons (t : Tok) (ts : List Tok) : wordR (t :: ts) = tokR t ++ wordR ts := encWords_cons tokR t ts
@[simp] theorem wordR_append (w₁ w₂ : List Tok) : wordR (w₁ ++ w₂) = wordR w₁ ++ wordR w₂ := encWords_append tokR w₁ w₂

abbrev Rle := List (List Tok × Nat)

def evalRle : Rle → ListBlank (Fin 2)
  | [] => default
  | (w, c) :: rest => ((wordL w) ^ c) +> evalRle rest

def evalRStack : Rle → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r_end => r_end
  | (w, c) :: rest, r_end => ((wordR w) ^ c) +> evalRStack rest r_end

@[simp] lemma evalRle_nil : evalRle [] = default := rfl
@[simp] lemma evalRle_cons (w : List Tok) (c : Nat) (rest : Rle) :
    evalRle ((w, c) :: rest) = ((wordL w) ^ c) +> evalRle rest := rfl

@[simp] lemma evalRStack_nil (r_end : ListBlank (Fin 2)) : evalRStack [] r_end = r_end := rfl
@[simp] lemma evalRStack_cons (w : List Tok) (c : Nat) (rest : Rle) (r_end : ListBlank (Fin 2)) :
    evalRStack ((w, c) :: rest) r_end = ((wordR w) ^ c) +> evalRStack rest r_end := rfl

def pushRle (w : List Tok) (c : Nat) (rle : Rle) : Rle :=
  if c == 0 || w.isEmpty then rle
  else match rle with
    | (w', c') :: rest =>
      if w == w' then (w, c + c') :: rest
      else (w, c) :: rle
    | [] => [(w, c)]

@[simp] theorem evalRle_pushRle (w : List Tok) (c : Nat) (rle : Rle) :
    evalRle (pushRle w c rle) = ((wordL w) ^ c) +> evalRle rle := by
  unfold pushRle
  by_cases hc : c = 0
  · subst hc; simp
  · by_cases hw : w = []
    · subst hw; simp
    · have hcond : (c == 0 || w.isEmpty) = false := by
        cases w with
        | nil => contradiction
        | cons _ _ => simp [hc]
      rw [hcond]
      cases rle with
      | nil => rfl
      | cons hd rest =>
        rcases hd with ⟨w', c'⟩
        by_cases hww : w = w'
        · subst hww; simp [list_pow_add]
        · have hbeq : (w == w') = false := beq_false_of_ne hww
          simp [hbeq]

@[simp] theorem evalRStack_pushRle (w : List Tok) (c : Nat) (rs : Rle) (r_end : ListBlank (Fin 2)) :
    evalRStack (pushRle w c rs) r_end = ((wordR w) ^ c) +> evalRStack rs r_end := by
  unfold pushRle
  by_cases hc : c = 0
  · subst hc; simp
  · by_cases hw : w = []
    · subst hw; simp
    · have hcond : (c == 0 || w.isEmpty) = false := by
        cases w with
        | nil => contradiction
        | cons _ _ => simp [hc]
      rw [hcond]
      cases rs with
      | nil => rfl
      | cons hd rest =>
        rcases hd with ⟨w', c'⟩
        by_cases hww : w = w'
        · subst hww; simp [list_pow_add]
        · have hbeq : (w == w') = false := beq_false_of_ne hww
          simp [hbeq]

@[simp] def pushToksLtr : List Tok → Rle → Rle
  | [], rle => rle
  | t :: ts, rle => pushToksLtr ts (pushRle [t] 1 rle)

def popLastTok : Rle → Option (Tok × Rle)
  | [] => none
  | ([], _) :: rest => popLastTok rest
  | (t :: ts, c) :: rest =>
    if c == 0 then popLastTok rest
    else
      let rest' := if c == 1 then rest else (t :: ts, c - 1) :: rest
      some (t, pushRle ts 1 rest')

theorem popLastTok_sound : ∀ (rle : Rle) (t : Tok) (rle' : Rle),
    popLastTok rle = some (t, rle') →
    evalRle rle = tokL t +> evalRle rle'
  | [], _, _, h => by nomatch h
  | ([], c) :: rest, t, rle', h => by
    simp only [popLastTok] at h
    have ih := popLastTok_sound rest t rle' h
    simpa using! ih
  | (t₀ :: ts, 0) :: rest, t, rle', h => by
    simp only [popLastTok, beq_self_eq_true, ↓reduceIte] at h
    have ih := popLastTok_sound rest t rle' h
    simpa using! ih
  | (t₀ :: ts, c + 1) :: rest, t, rle', h => by
    simp only [popLastTok, Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    cases c with
    | zero =>
      simp [pow_succ_list]
    | succ c' =>
      simp [pow_succ_list]

-- ============================================================================
-- Section 6.4: Named Configurations & 59 Verified Micro-Step Lemmas
-- ============================================================================

def evalWK (k1 : Nat) : ListBlank (Fin 2) :=
  [1, 0, 1, 1] +> ((([0, 0, 1, 1] : List (Fin 2)) ^ k1) +> default)

def cfgR (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, [1, 1] +> l, default⟩⟩

def carryCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨1, l, [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩

def r0Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1OddShortCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨1, [1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1OddCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  r1OddShortCfg (tokL .Z +> l) r

def wSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨1, l, [1] +> r⟩⟩

def dSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨1, [0, 1, 1] +> l, r⟩⟩

def tSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def t3Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨1, l, [0, 1, 0, 0, 1] +> r⟩⟩

def pmuCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨1, l, [1, 0, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩

theorem init_to_carry0 :
    (init []) [target_tm]⊢^{307} (carryCfg (tokL .M +> (tokL .U +> default)) (evalWK 1)) :=
  bmultiStep_sound 307 ⟨A, 0, [], []⟩
    ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl

theorem carry_Z (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .Z +> l) r) [target_tm]⊢^{48} (carryCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 48 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_P (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .P +> l) r) [target_tm]⊢^{16} (carryCfg l (tokR .P +> r)) :=
  wmultiStep_sound 16 ⟨B, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .P +> l))))) r) [target_tm]⊢^{68} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 68 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (((tokL .T) ^ 2) +> (tokL .P +> l))) r) [target_tm]⊢^{104} (carryCfg l (((tokR .Z) ^ 3) +> r)) :=
  wmultiStep_sound 104 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTT (l r : ListBlank (Fin 2)) :
    (carryCfg (((tokL .T) ^ 3) +> (tokL .P +> l)) r) [target_tm]⊢^{72} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 72 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (((tokL .T) ^ 3) +> (tokL .P +> l))) r) [target_tm]⊢^{85} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .PTTTM_TAIL +> r))) :=
  wmultiStep_sound 85 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem turn_UM (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .U +> default)) r) [target_tm]⊢^{57} (r1Cfg (tokL .M +> (tokL .U +> default)) r) :=
  cmultiStep_sound 57 ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_UMT (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .M +> (tokL .U +> default))) r) [target_tm]⊢^{89} (r1Cfg (tokL .Z +> (tokL .U +> default)) r) :=
  cmultiStep_sound 89 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_ZT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{57} (r1Cfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 57 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_WM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .W +> l)) r) [target_tm]⊢^{51} (r1Cfg (tokL .T +> l) r) :=
  wmultiStep_sound 51 ⟨B, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .P +> l)) r) [target_tm]⊢^{105} (r0Cfg (tokL .P +> (tokL .T +> l)) r) :=
  wmultiStep_sound 105 ⟨B, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .Z +> l)) r) [target_tm]⊢^{51} (r1Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 51 ⟨B, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{127} (r1OddCfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 127 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_PTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{89} (r1Cfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 89 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{93} (r1Cfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 93 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .Z +> l))) r) [target_tm]⊢^{101} (r1OddCfg (tokL .T +> (tokL .T +> l)) r) :=
  wmultiStep_sound 101 ⟨B, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{111} (r0Cfg (tokL .P +> (tokL .M +> (tokL .T +> l))) r) :=
  wmultiStep_sound 111 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{115} (r0Cfg (tokL .P +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 115 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{115} (r0Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 115 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_MUTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .U +> (tokL .M +> l)))) r) [target_tm]⊢^{127} (r1OddCfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 127 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .P +> l)))) r) [target_tm]⊢^{147} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .U +> (tokL .M +> l)))) r) :=
  wmultiStep_sound 147 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{147} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 147 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{99} (r1Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 99 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZPMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .P +> (tokL .Z +> l)))) r) [target_tm]⊢^{147} (r0Cfg (tokL .P +> (tokL .M +> (tokL .W +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 147 ⟨B, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .Z +> l))))) r) [target_tm]⊢^{143} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 143 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .T +> (tokL .P +> l))))) r) [target_tm]⊢^{185} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .Z +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 185 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem carry_MU_to_pmuCfg (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> l)) r) [target_tm]⊢^{15} (pmuCfg l (tokR .P +> r)) :=
  wmultiStep_sound 15 ⟨B, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmu_step (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .P +> l) r) [target_tm]⊢^{52} (pmuCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 52 ⟨D, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmuCfg_Z_turn (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{36} (r0Cfg (tokL .M +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 36 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem pmuCfg_TM_halt (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .M +> (tokL .T +> l)) r) [target_tm]⊢^{21} (⟨some F, ⟨1, [] +> l, [1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩) :=
  wmultiStep_sound 21 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 1, [], [1, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem r0_Z (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r0Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r0_P (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .P +> r)) [target_tm]⊢^{44} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 44 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem r0_PTTTM_TAIL (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .PTTTM_TAIL +> r)) [target_tm]⊢^{15} (r1Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 15 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1_Z (l r : ListBlank (Fin 2)) :
    (r1Cfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r0Cfg (tokL .M +> (tokL .Z +> l)) r) :=
  wmultiStep_sound 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1_P (l r : ListBlank (Fin 2)) :
    (r1Cfg l (tokR .P +> r)) [target_tm]⊢^{62} (r1OddCfg (tokL .P +> l) r) :=
  wmultiStep_sound 62 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem r1OddShort_Z (l r : ListBlank (Fin 2)) :
    (r1OddShortCfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r1OddShortCfg (tokL .Z +> l) r) :=
  wmultiStep_sound 12 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1Odd_P (l r : ListBlank (Fin 2)) :
    (r1OddCfg l (tokR .P +> r)) [target_tm]⊢^{10} (r1Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 10 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_start (l : ListBlank (Fin 2)) :
    (cfgR l) [target_tm]⊢^{2} (wSweepCfg l default) :=
  rcmultiStep_sound 2 ⟨B, 0, [1, 1], []⟩
    ⟨D, 1, [], [1]⟩ l rfl

theorem wSweep_step (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .W +> l) r) [target_tm]⊢^{4} (wSweepCfg l ([0, 0, 1, 1] +> r)) :=
  wmultiStep_sound 4 ⟨D, 1, [0, 0, 1, 1], [1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 1]⟩ l r rfl

theorem dSweep_step (l r : ListBlank (Fin 2)) :
    (dSweepCfg l ([0, 0, 1, 1] +> r)) [target_tm]⊢^{6} (dSweepCfg (tokL .W +> l) r) :=
  wmultiStep_sound 6 ⟨E, 1, [0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem dSweep_end (l : ListBlank (Fin 2)) :
    (dSweepCfg l default) [target_tm]⊢^{5} (cfgR (tokL .W +> l)) :=
  rcmultiStep_sound 5 ⟨E, 1, [0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1], []⟩ l rfl

theorem tSweep_step (l r : ListBlank (Fin 2)) :
    (tSweepCfg l ([0, 0, 1, 1] +> r)) [target_tm]⊢^{22} (tSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 22 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem tSweep_end (l : ListBlank (Fin 2)) :
    (tSweepCfg l default) [target_tm]⊢^{2} (cfgR (tokL .Z +> l)) :=
  rcmultiStep_sound 2 ⟨E, 0, [0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩ l rfl

theorem r0_to_dSweep (l r : ListBlank (Fin 2)) :
    (r0Cfg l ([1, 0, 1, 1] +> r)) [target_tm]⊢^{6} (dSweepCfg (tokL .Z +> (tokL .Z +> l)) r) :=
  wmultiStep_sound 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1_to_dSweep (l r : ListBlank (Fin 2)) :
    (r1Cfg l ([1, 0, 1, 1] +> r)) [target_tm]⊢^{6} (dSweepCfg (tokL .Z +> (tokL .M +> (tokL .Z +> l))) r) :=
  wmultiStep_sound 6 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1Odd_to_tSweep (l r : ListBlank (Fin 2)) :
    (r1OddCfg l ([1, 0, 1, 1] +> r)) [target_tm]⊢^{10} (tSweepCfg (tokL .Z +> (tokL .Z +> l)) r) :=
  wmultiStep_sound 10 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_Z_to_dSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .Z +> l) r) [target_tm]⊢^{9} (dSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 9 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem wSweep_ZT_to_dSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .Z +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{47} (dSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 47 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_PT_to_carry (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .P +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{34} (carryCfg l ([1, 0, 1, 1] +> r)) :=
  wmultiStep_sound 34 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl

theorem wSweep_ZMT_to_tSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .M +> (tokL .Z +> l))) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{69} (tSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 69 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem cfgR_Z_to_TW (l : ListBlank (Fin 2)) :
    (cfgR (tokL .Z +> l)) [target_tm]⊢^{16} (cfgR (tokL .W +> (tokL .T +> l))) :=
  rcmultiStep_sound 16 ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl

theorem cfgR_TW_to_t3Cfg (l : ListBlank (Fin 2)) :
    (cfgR (tokL .W +> (tokL .T +> l))) [target_tm]⊢^{24} (t3Cfg l (evalWK 0)) :=
  rcmultiStep_sound 24 ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl

theorem t3_step (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 3) +> l) r) [target_tm]⊢^{56} (t3Cfg l (((tokR .Z) ^ 2) +> r)) :=
  wmultiStep_sound 56 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem t3Cfg_Z_zero_to_carry (l : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (evalWK 0)) [target_tm]⊢^{104} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 104 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_Z_succ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{35} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 35 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem t3Cfg_TZ_to_r1OddShort (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{47} (r1OddShortCfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 47 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem r1OddShortCfg_evalWK0_to_carry (l : ListBlank (Fin 2)) :
    (r1OddShortCfg l (evalWK 0)) [target_tm]⊢^{156} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 156 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_TTZ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 2) +> (tokL .Z +> l)) r) [target_tm]⊢^{71} (r0Cfg (tokL .W +> (tokL .T +> l)) r) :=
  wmultiStep_sound 71 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl


theorem r1Odd_Z (l r : ListBlank (Fin 2)) :
    (r1OddCfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r1OddCfg (tokL .Z +> l) r) :=
  r1OddShort_Z (tokL .Z +> l) r

-- ============================================================================
-- Section 6.5: Loop & Suffix Transition Lemmas
-- ============================================================================

theorem wSweep_loop : ∀ (n : Nat) (l r : ListBlank (Fin 2)),
    (wSweepCfg (((tokL .W) ^ n) +> l) r) [target_tm]⊢*
      (wSweepCfg l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r))
  | 0, l, r => stepStar_refl _ _
  | n + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨4, wSweep_step (((tokL .W) ^ n) +> l) r⟩ ?_
    have ih := wSweep_loop n l ([0, 0, 1, 1] +> r)
    rwa [pow_succ_right, listblank_append_assoc]

theorem dSweep_loop : ∀ (n : Nat) (l r : ListBlank (Fin 2)),
    (dSweepCfg l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)) [target_tm]⊢*
      (dSweepCfg (((tokL .W) ^ n) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | n + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨6, dSweep_step l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)⟩ ?_
    have ih := dSweep_loop n (tokL .W +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem tSweep_loop : ∀ (n : Nat) (l r : ListBlank (Fin 2)),
    (tSweepCfg l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)) [target_tm]⊢*
      (tSweepCfg (((tokL .T) ^ n) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | n + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨22, tSweep_step l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)⟩ ?_
    have ih := tSweep_loop n (tokL .T +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem t3_loop : ∀ (q : Nat) (l r : ListBlank (Fin 2)),
    (t3Cfg (((tokL .T) ^ (3 * q)) +> l) r) [target_tm]⊢*
      (t3Cfg l (((tokR .Z) ^ (2 * q)) +> r))
  | 0, l, r => stepStar_refl _ _
  | q + 1, l, r => by
    have h3 : 3 * (q + 1) = 3 + 3 * q := by omega
    have h2 : 2 * (q + 1) = 2 * q + 2 := by omega
    rw [h3, list_pow_add, listblank_append_assoc]
    refine stepStar_trans ⟨56, t3_step (((tokL .T) ^ (3 * q)) +> l) r⟩ ?_
    have ih := t3_loop q l (((tokR .Z) ^ 2) +> r)
    rwa [h2, list_pow_add, listblank_append_assoc]

theorem pmu_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (pmuCfg (((tokL .P) ^ m) +> l) r) [target_tm]⊢*
      (pmuCfg l (((tokR .Z) ^ m) +> r))
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨52, pmu_step (((tokL .P) ^ m) +> l) r⟩ ?_
    have ih := pmu_loop m l (tokR .Z +> r)
    rwa [pow_succ_right, listblank_append_assoc]

theorem r0_Z_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r0Cfg l (((tokR .Z) ^ m) +> r)) [target_tm]⊢*
      (r0Cfg (((tokL .Z) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨12, r0_Z l (((tokR .Z) ^ m) +> r)⟩ ?_
    have ih := r0_Z_loop m (tokL .Z +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem r0_P_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r0Cfg l (((tokR .P) ^ m) +> r)) [target_tm]⊢*
      (r0Cfg (((tokL .P) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨44, r0_P l (((tokR .P) ^ m) +> r)⟩ ?_
    have ih := r0_P_loop m (tokL .P +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem r1OddShort_Z_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r1OddShortCfg l (((tokR .Z) ^ m) +> r)) [target_tm]⊢*
      (r1OddShortCfg (((tokL .Z) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨12, r1OddShort_Z l (((tokR .Z) ^ m) +> r)⟩ ?_
    have ih := r1OddShort_Z_loop m (tokL .Z +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem cfgR_ZW_to_TW (n : Nat) (l : ListBlank (Fin 2)) :
    (cfgR (((tokL .W) ^ n) +> (tokL .Z +> l))) [target_tm]⊢*
      (cfgR (((tokL .W) ^ (n + 1)) +> (tokL .T +> l))) := by
  refine stepStar_trans ⟨2, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop n (tokL .Z +> l) default) ?_
  refine stepStar_trans ⟨9, wSweep_Z_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop n (tokL .T +> l) default) ?_
  rw [pow_succ_list, listblank_append_assoc]
  exact ⟨5, dSweep_end _⟩

theorem r0_end (k1 : Nat) (l : ListBlank (Fin 2)) :
    (r0Cfg l (evalWK k1)) [target_tm]⊢* (carryCfg l (evalWK (k1 + 2))) := by
  unfold evalWK
  refine stepStar_trans ⟨6, r0_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop k1 (tokL .Z +> (tokL .Z +> l)) default) ?_
  refine stepStar_trans ⟨5, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (k1 + 1) (tokL .Z +> l)) ?_
  refine stepStar_trans ⟨2, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (k1 + 2) (tokL .T +> (tokL .Z +> l)) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (k1 + 1), listblank_append_assoc]
  refine stepStar_trans ⟨47, wSweep_ZT_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop (k1 + 1) (tokL .Z +> (tokL .P +> l)) default) ?_
  refine stepStar_trans ⟨5, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (k1 + 2) (tokL .P +> l)) ?_
  refine stepStar_trans ⟨2, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (k1 + 3) (tokL .T +> (tokL .P +> l)) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (k1 + 2), listblank_append_assoc]
  exact ⟨34, wSweep_PT_to_carry l _⟩

theorem r1_end (kf1 : Nat) (l : ListBlank (Fin 2)) :
    (r1Cfg l (evalWK kf1)) [target_tm]⊢*
      (t3Cfg (((tokL .T) ^ (kf1 + 1)) +> (tokL .Z +> (tokL .P +> l))) (evalWK 0)) := by
  unfold evalWK
  refine stepStar_trans ⟨6, r1_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop kf1 (tokL .Z +> (tokL .M +> (tokL .Z +> l))) default) ?_
  refine stepStar_trans ⟨5, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (kf1 + 1) (tokL .M +> (tokL .Z +> l))) ?_
  refine stepStar_trans ⟨2, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (kf1 + 2) (tokL .T +> (tokL .M +> (tokL .Z +> l))) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (kf1 + 1), listblank_append_assoc]
  refine stepStar_trans ⟨69, wSweep_ZMT_to_tSweep l _⟩ ?_
  refine stepStar_trans (tSweep_loop (kf1 + 1) (tokL .Z +> (tokL .P +> l)) default) ?_
  refine stepStar_trans ⟨2, tSweep_end _⟩ ?_
  refine stepStar_trans ⟨16, cfgR_Z_to_TW _⟩ ?_
  exact ⟨24, cfgR_TW_to_t3Cfg _⟩

theorem r1Odd_end (kf1 : Nat) (l : ListBlank (Fin 2)) :
    (r1OddCfg l (evalWK kf1)) [target_tm]⊢*
      (t3Cfg (((tokL .T) ^ kf1) +> (tokL .Z +> (tokL .Z +> l))) (evalWK 0)) := by
  unfold evalWK
  refine stepStar_trans ⟨10, r1Odd_to_tSweep l _⟩ ?_
  refine stepStar_trans (tSweep_loop kf1 (tokL .Z +> (tokL .Z +> l)) default) ?_
  refine stepStar_trans ⟨2, tSweep_end _⟩ ?_
  refine stepStar_trans ⟨16, cfgR_Z_to_TW _⟩ ?_
  exact ⟨24, cfgR_TW_to_t3Cfg _⟩

def stepZtToCarry (rle2 : Rle) (n : Nat) : Rle × Nat :=
  let q := n / 3
  let rem := n % 3
  if rem == 0 then
    if q == 0 then
      (rle2, 1)
    else
      (pushRle [.Z] (2 * q - 1) (pushRle [.P] 1 rle2), 2)
  else if rem == 1 then
    (pushRle [.Z] (2 * q) (pushToksLtr [.T, .M] rle2), 1)
  else
    (pushRle [.Z] (2 * q) (pushToksLtr [.T, .W] rle2), 2)

theorem stepZtToCarry_sound (rle2 : Rle) (n : Nat) :
    (t3Cfg (((tokL .T) ^ n) +> (tokL .Z +> evalRle rle2)) (evalWK 0)) [target_tm]⊢*
      (carryCfg (evalRle (stepZtToCarry rle2 n).1) (evalWK (stepZtToCarry rle2 n).2)) := by
  dsimp -failIfUnchanged only [stepZtToCarry]
  generalize hq : n / 3 = q
  generalize hrem : n % 3 = rem
  have hdiv : n = 3 * q + rem := by omega
  have hlt : rem < 3 := by omega
  rw [hdiv, list_pow_add, listblank_append_assoc]
  refine stepStar_trans (t3_loop q (((tokL .T) ^ rem) +> (tokL .Z +> evalRle rle2)) (evalWK 0)) ?_
  rcases (by omega : rem = 0 ∨ rem = 1 ∨ rem = 2) with rfl | rfl | rfl
  · simp only [beq_self_eq_true, ↓reduceIte, pow_zero_list, listblank_append_nil]
    cases q with
    | zero =>
      simp only [beq_self_eq_true, ↓reduceIte, Nat.mul_zero, pow_zero_list, listblank_append_nil]
      exact ⟨104, t3Cfg_Z_zero_to_carry (evalRle rle2)⟩
    | succ q' =>
      have hq_ne : (q' + 1 == 0) = false := rfl
      have h2q : 2 * (q' + 1) = 1 + (2 * (q' + 1) - 1) := by omega
      have h2q_sub : 1 + (2 * (q' + 1) - 1) - 1 = 2 * (q' + 1) - 1 := by omega
      rw [hq_ne, h2q, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil, listblank_append_assoc]
      simp only [Bool.false_eq_true, ↓reduceIte, evalRle_pushRle, pow_succ_list, pow_zero_list,
        List.append_nil, wordL_cons, wordL_nil, h2q_sub]
      refine stepStar_trans ⟨35, t3Cfg_Z_succ_to_r0 (evalRle rle2) _⟩ ?_
      refine stepStar_trans (r0_Z_loop (2 * (q' + 1) - 1) (tokL .P +> evalRle rle2) (evalWK 0)) ?_
      exact r0_end 0 _
  · have hr0 : (1 == 0) = false := rfl
    rw [hr0]
    simp only [Bool.false_eq_true, beq_self_eq_true, ↓reduceIte, pow_succ_list, pow_zero_list,
      List.append_nil, pushToksLtr, evalRle_pushRle, wordL_cons, wordL_nil]
    refine stepStar_trans ⟨47, t3Cfg_TZ_to_r1OddShort (evalRle rle2) _⟩ ?_
    refine stepStar_trans (r1OddShort_Z_loop (2 * q) (tokL .M +> (tokL .T +> evalRle rle2)) (evalWK 0)) ?_
    exact ⟨156, r1OddShortCfg_evalWK0_to_carry _⟩
  · have hr0 : (2 == 0) = false := rfl
    have hr1 : (2 == 1) = false := rfl
    rw [hr0, hr1]
    simp only [Bool.false_eq_true, ↓reduceIte, pushToksLtr, evalRle_pushRle, pow_succ_list,
      pow_zero_list, List.append_nil, wordL_cons, wordL_nil]
    refine stepStar_trans ⟨71, t3Cfg_TTZ_to_r0 (evalRle rle2) _⟩ ?_
    refine stepStar_trans (r0_Z_loop (2 * q) (tokL .W +> (tokL .T +> evalRle rle2)) (evalWK 0)) ?_
    exact r0_end 0 _


-- ============================================================================
-- Section 6.6: RLE Combinators & Sweep Soundness Lemmas
-- ============================================================================

def popTok (t_exp : Tok) (rle : Rle) : Option Rle :=
  match popLastTok rle with
  | some (t, rle') => if t == t_exp then some rle' else none
  | none => none

theorem popTok_sound (t_exp : Tok) (rle rle' : Rle) (h : popTok t_exp rle = some rle') :
    evalRle rle = tokL t_exp +> evalRle rle' := by
  unfold popTok at h
  cases hp : popLastTok rle with
  | none => rw [hp] at h; nomatch h
  | some p =>
    rcases p with ⟨t, r⟩
    rw [hp] at h
    simp only [beq_iff_eq] at h
    split at h
    · rename_i heq
      injection h with hr
      rw [← heq, ← hr]
      exact popLastTok_sound rle t r hp
    · nomatch h

def popToks : List Tok → Rle → Option Rle
  | [], rle => some rle
  | t :: ts, rle =>
    match popTok t rle with
    | some rle' => popToks ts rle'
    | none => none

theorem popToks_sound : ∀ (ts : List Tok) (rle rle' : Rle),
    popToks ts rle = some rle' →
    evalRle rle = wordL ts +> evalRle rle'
  | [], rle, rle', h => by
    injection h with hr
    subst hr
    rfl
  | t :: ts, rle, rle', h => by
    unfold popToks at h
    cases h1 : popTok t rle with
    | none => rw [h1] at h; nomatch h
    | some r1 =>
      rw [h1] at h
      have ih := popToks_sound ts r1 rle' h
      have hp := popTok_sound t rle r1 h1
      rw [hp, ih, wordL_cons, listblank_append_assoc]

def matchHeadAnyCount (w_exp : List Tok) (rle : Rle) : Option (Nat × Rle) :=
  match rle with
  | (w, c) :: rest => if w == w_exp && c > 0 then some (c, rest) else none
  | [] => none

theorem matchHeadAnyCount_sound (w_exp : List Tok) (rle rest : Rle) (c : Nat)
    (h : matchHeadAnyCount w_exp rle = some (c, rest)) :
    c > 0 ∧ evalRle rle = ((wordL w_exp) ^ c) +> evalRle rest := by
  cases rle with
  | nil => nomatch h
  | cons hd tl =>
    rcases hd with ⟨w, c0⟩
    unfold matchHeadAnyCount at h
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    split at h
    · rename_i hwc
      rcases hwc with ⟨rfl, hc0⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨hc0, rfl⟩
    · nomatch h

def popPrefixCount (pref : List Tok) (w_exp : List Tok) (rle : Rle) : Option (Nat × Rle) :=
  match popToks pref rle with
  | some r1 => matchHeadAnyCount w_exp r1
  | none => none

theorem popPrefixCount_sound (pref w_exp : List Tok) (rle r3 : Rle) (b : Nat)
    (h : popPrefixCount pref w_exp rle = some (b, r3)) :
    b > 0 ∧ evalRle rle = wordL pref +> (((wordL w_exp) ^ b) +> evalRle r3) := by
  unfold popPrefixCount at h
  cases h1 : popToks pref rle with
  | none => rw [h1] at h; nomatch h
  | some r1 =>
    rw [h1] at h
    rcases matchHeadAnyCount_sound w_exp r1 r3 b h with ⟨hb, hr1⟩
    rw [popToks_sound pref rle r1 h1, hr1]
    exact ⟨hb, rfl⟩

theorem carry_word : ∀ (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (carryCfg (wordL w +> l) r) [target_tm]⊢*
      (carryCfg l (wordR (revWord w) +> r))
  | [], l, r, _ => stepStar_refl _ _
  | .Z :: ts, l, r, h => by
    simp only [isZpWord] at h
    rw [wordL_cons, listblank_append_assoc]
    refine stepStar_trans ⟨_, carry_Z (wordL ts +> l) r⟩ ?_
    have ih := carry_word ts l (tokR .Z +> r) h
    simpa [revWord, wordR_append, listblank_append_assoc] using! ih
  | .P :: ts, l, r, h => by
    simp only [isZpWord] at h
    rw [wordL_cons, listblank_append_assoc]
    refine stepStar_trans ⟨_, carry_P (wordL ts +> l) r⟩ ?_
    have ih := carry_word ts l (tokR .P +> r) h
    simpa [revWord, wordR_append, listblank_append_assoc] using! ih
  | .U :: _, _, _, h => by nomatch h
  | .M :: _, _, _, h => by nomatch h
  | .W :: _, _, _, h => by nomatch h
  | .T :: _, _, _, h => by nomatch h
  | .PTTTM_TAIL :: _, _, _, h => by nomatch h

theorem carry_pow : ∀ (c : Nat) (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (carryCfg (((wordL w) ^ c) +> l) r) [target_tm]⊢*
      (carryCfg l (((wordR (revWord w)) ^ c) +> r))
  | 0, _, l, r, _ => stepStar_refl _ _
  | c + 1, w, l, r, hw => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans (carry_word w (((wordL w) ^ c) +> l) r hw) ?_
    have ih := carry_pow c w l (wordR (revWord w) +> r) hw
    rwa [pow_succ_right, listblank_append_assoc]

def popCarrySpecial (rle rs : Rle) : Option (Rle × Rle) :=
  match popToks [.M, .T, .U, .M, .P] rle with
  | some r' => some (r', pushRle [.Z] 2 (pushRle [.P] 1 rs))
  | none => match popToks [.M, .T, .T, .T, .P] rle with
  | some r' => some (r', pushRle [.Z] 2 (pushRle [.PTTTM_TAIL] 1 rs))
  | none => match popToks [.W, .T, .T, .P] rle with
  | some r' => some (r', pushRle [.Z] 3 rs)
  | none => match popToks [.T, .T, .T, .P] rle with
  | some r' => some (r', pushRle [.Z] 2 (pushRle [.P] 1 rs))
  | none => none

theorem popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : ListBlank (Fin 2))
    (h : popCarrySpecial rle rs = some (rle', rs')) :
    (carryCfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
      (carryCfg (evalRle rle') (evalRStack rs' r_end)) := by
  unfold popCarrySpecial at h
  cases h1 : popToks [.M, .T, .U, .M, .P] rle with
  | some r1 =>
    rw [h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨hr1, hrs⟩
    rw [← hr1, ← hrs, popToks_sound _ _ _ h1]
    simp only [wordL_cons, List.append_nil, listblank_append_assoc,
      evalRStack_pushRle, pow_succ_list, pow_zero_list, wordR_cons]
    exact ⟨_, carry_PMUTM (evalRle r1) (evalRStack rs r_end)⟩
  | none =>
    rw [h1] at h
    cases h2 : popToks [.M, .T, .T, .T, .P] rle with
    | some r1 =>
      rw [h2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨hr1, hrs⟩
      rw [← hr1, ← hrs, popToks_sound _ _ _ h2]
      simp only [wordL_cons, List.append_nil, listblank_append_assoc,
        evalRStack_pushRle, pow_succ_list, pow_zero_list, wordR_cons]
      exact ⟨_, carry_PTTTM (evalRle r1) (evalRStack rs r_end)⟩
    | none =>
      rw [h2] at h
      cases h3 : popToks [.W, .T, .T, .P] rle with
      | some r1 =>
        rw [h3] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨hr1, hrs⟩
        rw [← hr1, ← hrs, popToks_sound _ _ _ h3]
        simp only [wordL_cons, List.append_nil, listblank_append_assoc,
          evalRStack_pushRle, pow_succ_list, pow_zero_list, wordR_cons]
        exact ⟨_, carry_PTTW (evalRle r1) (evalRStack rs r_end)⟩
      | none =>
        rw [h3] at h
        cases h4 : popToks [.T, .T, .T, .P] rle with
        | some r1 =>
          rw [h4] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨hr1, hrs⟩
          rw [← hr1, ← hrs, popToks_sound _ _ _ h4]
          simp only [wordL_cons, List.append_nil, listblank_append_assoc,
            evalRStack_pushRle, pow_succ_list, pow_zero_list, wordR_cons]
          exact ⟨_, carry_PTTT (evalRle r1) (evalRStack rs r_end)⟩
        | none =>
          rw [h4] at h
          nomatch h

def popCarryLoop : Nat → Rle → Rle → Rle × Rle
  | 0, rle, rs => (rle, rs)
  | fuel + 1, rle, rs =>
    match rle with
    | (w, c) :: rest =>
      if isZpWord w then
        popCarryLoop fuel rest (pushRle (revWord w) c rs)
      else match popCarrySpecial rle rs with
        | some (rle', rs') => popCarryLoop fuel rle' rs'
        | none => (rle, rs)
    | [] => ([], rs)

theorem popCarryLoop_sound : ∀ (fuel : Nat) (rle rs : Rle) (r_end : ListBlank (Fin 2)),
    (carryCfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
      (carryCfg (evalRle (popCarryLoop fuel rle rs).1) (evalRStack (popCarryLoop fuel rle rs).2 r_end))
  | 0, rle, rs, r_end => stepStar_refl _ _
  | fuel + 1, [], rs, r_end => stepStar_refl _ _
  | fuel + 1, (w, c) :: rest, rs, r_end => by
    simp only [popCarryLoop]
    split
    · rename_i hw
      simp only [evalRle_cons]
      refine stepStar_trans (carry_pow c w (evalRle rest) (evalRStack rs r_end) hw) ?_
      rw [← evalRStack_pushRle (revWord w) c rs r_end]
      exact popCarryLoop_sound fuel rest (pushRle (revWord w) c rs) r_end
    · cases hp : popCarrySpecial ((w, c) :: rest) rs with
      | none => exact stepStar_refl _ _
      | some p =>
        rcases p with ⟨rle', rs'⟩
        refine stepStar_trans (popCarrySpecial_sound ((w, c) :: rest) rs rle' rs' r_end hp) ?_
        exact popCarryLoop_sound fuel rle' rs' r_end

theorem r0_word : ∀ (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (r0Cfg l (wordR w +> r)) [target_tm]⊢*
      (r0Cfg (wordL (revWord w) +> l) r)
  | [], l, r, _ => stepStar_refl _ _
  | .Z :: ts, l, r, h => by
    simp only [isZpWord] at h
    rw [wordR_cons, listblank_append_assoc]
    refine stepStar_trans ⟨_, r0_Z l (wordR ts +> r)⟩ ?_
    have ih := r0_word ts (tokL .Z +> l) r h
    simpa [revWord, wordL_append, listblank_append_assoc] using! ih
  | .P :: ts, l, r, h => by
    simp only [isZpWord] at h
    rw [wordR_cons, listblank_append_assoc]
    refine stepStar_trans ⟨_, r0_P l (wordR ts +> r)⟩ ?_
    have ih := r0_word ts (tokL .P +> l) r h
    simpa [revWord, wordL_append, listblank_append_assoc] using! ih
  | .U :: _, _, _, h => by nomatch h
  | .M :: _, _, _, h => by nomatch h
  | .W :: _, _, _, h => by nomatch h
  | .T :: _, _, _, h => by nomatch h
  | .PTTTM_TAIL :: _, _, _, h => by nomatch h

theorem r0_pow : ∀ (c : Nat) (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (r0Cfg l (((wordR w) ^ c) +> r)) [target_tm]⊢*
      (r0Cfg (((wordL (revWord w)) ^ c) +> l) r)
  | 0, _, l, r, _ => stepStar_refl _ _
  | c + 1, w, l, r, hw => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans (r0_word w l (((wordR w) ^ c) +> r) hw) ?_
    have ih := r0_pow c w (wordL (revWord w) +> l) r hw
    rwa [pow_succ_right, listblank_append_assoc]

def allZpStack : Rle → Bool
  | [] => true
  | (it, _) :: rest => isZpWord it && allZpStack rest

def copyRStack : Rle → Rle → Option Rle
  | rle, [] => some rle
  | rle, (item, count) :: rest =>
    if isZpWord item then copyRStack (pushRle (revWord item) count rle) rest
    else none

theorem copyRStack_sound : ∀ (rs : Rle) (rle rle' : Rle) (r_end : ListBlank (Fin 2)),
    copyRStack rle rs = some rle' →
    allZpStack rs = true ∧
      (r0Cfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
        (r0Cfg (evalRle rle') r_end)
  | [], rle, rle', r_end, h => by
    injection h with hr
    subst hr
    exact ⟨rfl, stepStar_refl _ _⟩
  | (w, c) :: rest, rle, rle', r_end, h => by
    unfold copyRStack at h
    split at h
    · rename_i hw
      rcases copyRStack_sound rest (pushRle (revWord w) c rle) rle' r_end h with ⟨hrest, hstep⟩
      simp only [allZpStack, hw, hrest, Bool.and_self]
      refine ⟨trivial, ?_⟩
      simp only [evalRStack_cons]
      refine stepStar_trans (r0_pow c w (evalRle rle) (evalRStack rest r_end) hw) ?_
      simpa [evalRle_pushRle] using! hstep
    · nomatch h

def HasRoundtrip (R : Nat → ListBlank (Fin 2)) : Prop :=
  ∀ (l : ListBlank (Fin 2)) (k1 : Nat),
    (r0Cfg l (R k1)) [target_tm]⊢* (carryCfg l (R (k1 + 2)))

theorem hasRoundtrip_evalWK : HasRoundtrip evalWK :=
  fun l k1 => r0_end k1 l

theorem hasRoundtrip_Z {R : Nat → ListBlank (Fin 2)} (hR : HasRoundtrip R) :
    HasRoundtrip (fun k1 => tokR .Z +> R k1) := by
  intro l k1
  refine stepStar_trans ⟨_, r0_Z l (R k1)⟩ ?_
  refine stepStar_trans (hR (tokL .Z +> l) k1) ?_
  exact ⟨_, carry_Z l (R (k1 + 2))⟩

theorem hasRoundtrip_P {R : Nat → ListBlank (Fin 2)} (hR : HasRoundtrip R) :
    HasRoundtrip (fun k1 => tokR .P +> R k1) := by
  intro l k1
  refine stepStar_trans ⟨_, r0_P l (R k1)⟩ ?_
  refine stepStar_trans (hR (tokL .P +> l) k1) ?_
  exact ⟨_, carry_P l (R (k1 + 2))⟩

theorem hasRoundtrip_word : ∀ (w : List Tok) {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true → HasRoundtrip R →
    HasRoundtrip (fun k1 => wordR w +> R k1)
  | [], _, _, hR => hR
  | .Z :: ts, _, hw, hR => by
    simp only [isZpWord] at hw
    intro l k1
    dsimp -failIfUnchanged only
    rw [wordR_cons, listblank_append_assoc]
    exact hasRoundtrip_Z (hasRoundtrip_word ts hw hR) l k1
  | .P :: ts, _, hw, hR => by
    simp only [isZpWord] at hw
    intro l k1
    dsimp -failIfUnchanged only
    rw [wordR_cons, listblank_append_assoc]
    exact hasRoundtrip_P (hasRoundtrip_word ts hw hR) l k1
  | .U :: _, _, hw, _ => by nomatch hw
  | .M :: _, _, hw, _ => by nomatch hw
  | .W :: _, _, hw, _ => by nomatch hw
  | .T :: _, _, hw, _ => by nomatch hw
  | .PTTTM_TAIL :: _, _, hw, _ => by nomatch hw

theorem hasRoundtrip_pow : ∀ (c : Nat) (w : List Tok) {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true → HasRoundtrip R →
    HasRoundtrip (fun k1 => ((wordR w) ^ c) +> R k1)
  | 0, _, _, _, hR => hR
  | c + 1, w, _, hw, hR => by
    intro l k1
    simp only [pow_succ_list, listblank_append_assoc]
    exact hasRoundtrip_word w hw (hasRoundtrip_pow c w hw hR) l k1

theorem hasRoundtrip_stack : ∀ (rs : Rle) {R : Nat → ListBlank (Fin 2)},
    allZpStack rs = true → HasRoundtrip R →
    HasRoundtrip (fun k1 => evalRStack rs (R k1))
  | [], _, _, hR => hR
  | (w, c) :: rest, _, hrs, hR => by
    simp only [allZpStack, Bool.and_eq_true] at hrs
    rcases hrs with ⟨hw, hrest⟩
    intro l k1
    simp only [evalRStack_cons]
    exact hasRoundtrip_pow c w hw (hasRoundtrip_stack rest hrest hR) l k1

def r1PhaseCfg (phase : Bool) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  if phase then r1OddCfg l r else r1Cfg l r

@[simp] lemma r1PhaseCfg_false (l r : ListBlank (Fin 2)) : r1PhaseCfg false l r = r1Cfg l r := rfl
@[simp] lemma r1PhaseCfg_true (l r : ListBlank (Fin 2)) : r1PhaseCfg true l r = r1OddCfg l r := rfl

def stepR1StarWord : List Tok → Bool → List Tok × Nat × Bool
  | [], phase => ([], 0, phase)
  | t :: ts, false =>
    let (out, res, p2) := stepR1StarWord ts (t != .Z)
    (out ++ [.P], res + (if t == .Z then 1 else 0), p2)
  | t :: ts, true =>
    let (out, res, p2) := stepR1StarWord ts (t != .P)
    (out ++ [.Z], res, p2)

theorem stepR1StarWord_phase_inv : ∀ (w : List Tok) (phase : Bool),
    isZpWord w = true →
    (stepR1StarWord w (!phase)).2.2 = !(stepR1StarWord w phase).2.2
  | [], phase, _ => rfl
  | .Z :: ts, false, hw => by
    simp only [isZpWord] at hw
    simpa [stepR1StarWord] using! stepR1StarWord_phase_inv ts false hw
  | .Z :: ts, true, hw => by
    simp only [isZpWord] at hw
    simpa [stepR1StarWord] using! (stepR1StarWord_phase_inv ts false hw).symm
  | .P :: ts, false, hw => by
    simp only [isZpWord] at hw
    simpa [stepR1StarWord] using! stepR1StarWord_phase_inv ts true hw
  | .P :: ts, true, hw => by
    simp only [isZpWord] at hw
    simpa [stepR1StarWord] using! (stepR1StarWord_phase_inv ts true hw).symm
  | .U :: _, _, hw => by nomatch hw
  | .M :: _, _, hw => by nomatch hw
  | .W :: _, _, hw => by nomatch hw
  | .T :: _, _, hw => by nomatch hw
  | .PTTTM_TAIL :: _, _, hw => by nomatch hw

theorem stepR1StarWord_sound : ∀ (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true → HasRoundtrip R →
    ∀ (k1 : Nat),
      (r1PhaseCfg phase l (wordR w +> R k1)) [target_tm]⊢*
        (r1PhaseCfg (stepR1StarWord w phase).2.2
          (wordL (stepR1StarWord w phase).1 +> l)
          (R (k1 + 2 * (stepR1StarWord w phase).2.1)))
  | [], phase, l, R, _, _, k1 => by
    simp [stepR1StarWord]
    exact stepStar_refl _ _
  | .Z :: ts, false, l, R, hw, hR, k1 => by
    simp only [isZpWord] at hw
    have hR' : HasRoundtrip (fun k => wordR ts +> R k) := hasRoundtrip_word ts hw hR
    simp only [stepR1StarWord, bne_self_eq_false, beq_self_eq_true, ↓reduceIte,
      wordR_cons, listblank_append_assoc, r1PhaseCfg_false]
    refine stepStar_trans ⟨_, r1_Z l (wordR ts +> R k1)⟩ ?_
    refine stepStar_trans (hR' (tokL .M +> (tokL .Z +> l)) k1) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans ⟨_, turn_ZM l (wordR ts +> R (k1 + 2))⟩ ?_
    have ih := stepR1StarWord_sound ts false (tokL .P +> l) hw hR (k1 + 2)
    have hadd : k1 + 2 + 2 * (stepR1StarWord ts false).2.1 =
        k1 + 2 * ((stepR1StarWord ts false).2.1 + 1) := by omega
    rw [hadd] at ih
    simpa [wordL_append, listblank_append_assoc] using! ih
  | .P :: ts, false, l, R, hw, hR, k1 => by
    simp only [isZpWord] at hw
    have hne : (Tok.P != Tok.Z) = true := rfl
    have heq : (Tok.P == Tok.Z) = false := rfl
    simp only [stepR1StarWord, hne, heq, Bool.false_eq_true, ↓reduceIte, Nat.add_zero,
      wordR_cons, listblank_append_assoc, r1PhaseCfg_false]
    refine stepStar_trans ⟨_, r1_P l (wordR ts +> R k1)⟩ ?_
    have ih := stepR1StarWord_sound ts true (tokL .P +> l) hw hR k1
    simpa [wordL_append, listblank_append_assoc] using! ih
  | .Z :: ts, true, l, R, hw, hR, k1 => by
    simp only [isZpWord] at hw
    have hne : (Tok.Z != Tok.P) = true := rfl
    simp only [stepR1StarWord, hne, wordR_cons, listblank_append_assoc, r1PhaseCfg_true]
    refine stepStar_trans ⟨_, r1Odd_Z l (wordR ts +> R k1)⟩ ?_
    have ih := stepR1StarWord_sound ts true (tokL .Z +> l) hw hR k1
    simpa [wordL_append, listblank_append_assoc] using! ih
  | .P :: ts, true, l, R, hw, hR, k1 => by
    simp only [isZpWord] at hw
    have hne : (Tok.P != Tok.P) = false := rfl
    simp only [stepR1StarWord, hne, wordR_cons, listblank_append_assoc, r1PhaseCfg_true]
    refine stepStar_trans ⟨_, r1Odd_P l (wordR ts +> R k1)⟩ ?_
    have ih := stepR1StarWord_sound ts false (tokL .Z +> l) hw hR k1
    simpa [wordL_append, listblank_append_assoc] using! ih
  | .U :: _, _, _, _, hw, _, _ => by nomatch hw
  | .M :: _, _, _, _, hw, _, _ => by nomatch hw
  | .W :: _, _, _, _, hw, _, _ => by nomatch hw
  | .T :: _, _, _, _, hw, _, _ => by nomatch hw
  | .PTTTM_TAIL :: _, _, _, _, hw, _, _ => by nomatch hw

theorem stepR1Star_same_pow : ∀ (c : Nat) (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true →
    (stepR1StarWord w phase).2.2 = phase →
    HasRoundtrip R →
    ∀ (k1 : Nat),
      (r1PhaseCfg phase l (((wordR w) ^ c) +> R k1)) [target_tm]⊢*
        (r1PhaseCfg phase (((wordL (stepR1StarWord w phase).1) ^ c) +> l)
          (R (k1 + 2 * (c * (stepR1StarWord w phase).2.1))))
  | 0, w, phase, l, R, _, _, _, k1 => by
    simp
    exact stepStar_refl _ _
  | c + 1, w, phase, l, R, hw, hsame, hR, k1 => by
    have hR' : HasRoundtrip (fun k => ((wordR w) ^ c) +> R k) := hasRoundtrip_pow c w hw hR
    rw [pow_succ_list, listblank_append_assoc]
    have h1 := stepR1StarWord_sound w phase l hw hR' k1
    rw [hsame] at h1
    refine stepStar_trans h1 ?_
    dsimp -failIfUnchanged only
    have ih := stepR1Star_same_pow c w phase (wordL (stepR1StarWord w phase).1 +> l) hw hsame hR
      (k1 + 2 * (stepR1StarWord w phase).2.1)
    have hadd : k1 + 2 * (stepR1StarWord w phase).2.1 + 2 * (c * (stepR1StarWord w phase).2.1) =
        k1 + 2 * ((c + 1) * (stepR1StarWord w phase).2.1) := by
      have : (c + 1) * (stepR1StarWord w phase).2.1 =
          c * (stepR1StarWord w phase).2.1 + (stepR1StarWord w phase).2.1 := Nat.succ_mul c _
      omega
    rw [hadd] at ih
    rwa [pow_succ_right, listblank_append_assoc]

theorem stepR1Star_alt_pow : ∀ (q : Nat) (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true →
    (stepR1StarWord w (stepR1StarWord w phase).2.2).2.2 = phase →
    HasRoundtrip R →
    ∀ (k1 : Nat),
      let s1 := stepR1StarWord w phase
      let s2 := stepR1StarWord w s1.2.2
      (r1PhaseCfg phase l (((wordR w) ^ (2 * q)) +> R k1)) [target_tm]⊢*
        (r1PhaseCfg phase (((wordL (s2.1 ++ s1.1)) ^ q) +> l)
          (R (k1 + 2 * (q * (s1.2.1 + s2.2.1)))))
  | 0, w, phase, l, R, _, _, _, k1 => by
    simp
    exact stepStar_refl _ _
  | q + 1, w, phase, l, R, hw, halt, hR, k1 => by
    dsimp -failIfUnchanged only
    have h2q : 2 * (q + 1) = 1 + (1 + 2 * q) := by omega
    rw [h2q, list_pow_add, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil,
      listblank_append_assoc, listblank_append_assoc]
    have hR2 : HasRoundtrip (fun k => ((wordR w) ^ (2 * q)) +> R k) :=
      hasRoundtrip_pow (2 * q) w hw hR
    have hR1 : HasRoundtrip (fun k => wordR w +> (((wordR w) ^ (2 * q)) +> R k)) :=
      hasRoundtrip_word w hw hR2
    refine stepStar_trans (stepR1StarWord_sound w phase l hw hR1 k1) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans
      (stepR1StarWord_sound w (stepR1StarWord w phase).2.2
        (wordL (stepR1StarWord w phase).1 +> l) hw hR2
        (k1 + 2 * (stepR1StarWord w phase).2.1)) ?_
    dsimp -failIfUnchanged only
    rw [halt]
    have ih := stepR1Star_alt_pow q w phase
      (wordL ((stepR1StarWord w (stepR1StarWord w phase).2.2).1 ++
        (stepR1StarWord w phase).1) +> l)
      hw halt hR
      (k1 + 2 * (stepR1StarWord w phase).2.1 +
        2 * (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1)
    dsimp -failIfUnchanged only at ih
    have hadd :
        k1 + 2 * (stepR1StarWord w phase).2.1 +
          2 * (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1 +
          2 * (q * ((stepR1StarWord w phase).2.1 +
            (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1)) =
        k1 + 2 * ((q + 1) * ((stepR1StarWord w phase).2.1 +
          (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1)) := by
      have : (q + 1) * ((stepR1StarWord w phase).2.1 +
          (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1) =
        q * ((stepR1StarWord w phase).2.1 +
          (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1) +
        ((stepR1StarWord w phase).2.1 +
          (stepR1StarWord w (stepR1StarWord w phase).2.2).2.1) := Nat.succ_mul q _
      omega
    rw [hadd] at ih
    have hw_app :
        wordL (stepR1StarWord w (stepR1StarWord w phase).2.2).1 +>
          (wordL (stepR1StarWord w phase).1 +> l) =
        wordL ((stepR1StarWord w (stepR1StarWord w phase).2.2).1 ++
          (stepR1StarWord w phase).1) +> l := by
      rw [wordL_append, listblank_append_assoc]
    rw [hw_app, pow_succ_right, listblank_append_assoc]
    exact ih

theorem evalRle_pushRle_one (w : List Tok) (rle : Rle) :
    evalRle (pushRle w 1 rle) = wordL w +> evalRle rle := by
  rw [evalRle_pushRle, pow_succ_list, pow_zero_list, List.append_nil]

def sweepStarLoop : Rle → Bool → Nat → Rle → Rle × Bool × Nat
  | rle, phase, totalRes, [] => (rle, phase, totalRes)
  | rle, phase, totalRes, (item, count) :: rest =>
    let (out1, res1, nextPhase) := stepR1StarWord item phase
    if nextPhase == phase then
      sweepStarLoop (pushRle out1 count rle) phase (totalRes + count * res1) rest
    else
      let (out2, res2, _) := stepR1StarWord item nextPhase
      let q := count / 2
      let rem := count % 2
      let rle1 := pushRle (out2 ++ out1) q rle
      let resAfterQ := totalRes + q * (res1 + res2)
      if rem == 1 then
        sweepStarLoop (pushRle out1 1 rle1) nextPhase (resAfterQ + res1) rest
      else
        sweepStarLoop rle1 phase resAfterQ rest

theorem sweepStarLoop_sound : ∀ (rs : Rle) (rle : Rle) (phase : Bool) (totalRes : Nat)
    {R : Nat → ListBlank (Fin 2)},
    allZpStack rs = true → HasRoundtrip R →
    ∀ (k1 : Nat),
      let res := sweepStarLoop rle phase totalRes rs
      (r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)))) [target_tm]⊢*
        (r1PhaseCfg res.2.1 (evalRle res.1) (R (k1 + 2 * res.2.2)))
  | [], rle, phase, totalRes, R, _, _, k1 => stepStar_refl _ _
  | (item, count) :: rest, rle, phase, totalRes, R, hrs, hR, k1 => by
    simp only [allZpStack, Bool.and_eq_true] at hrs
    rcases hrs with ⟨hitem, hrest⟩
    have hR_rest : HasRoundtrip (fun k => evalRStack rest (R k)) :=
      hasRoundtrip_stack rest hrest hR
    dsimp -failIfUnchanged only [sweepStarLoop]
    by_cases hsame : (stepR1StarWord item phase).2.2 = phase
    · have hbeq : ((stepR1StarWord item phase).2.2 == phase) = true := beq_iff_eq.mpr hsame
      rw [hbeq]
      simp only [↓reduceIte, evalRStack_cons]
      refine stepStar_trans
        (stepR1Star_same_pow count item phase (evalRle rle) hitem hsame hR_rest (k1 + 2 * totalRes)) ?_
      dsimp -failIfUnchanged only
      have hadd : k1 + 2 * totalRes + 2 * (count * (stepR1StarWord item phase).2.1) =
          k1 + 2 * (totalRes + count * (stepR1StarWord item phase).2.1) := by omega
      rw [hadd, ← evalRle_pushRle]
      exact sweepStarLoop_sound rest (pushRle (stepR1StarWord item phase).1 count rle)
        phase (totalRes + count * (stepR1StarWord item phase).2.1) hrest hR k1
    · have hbeq : ((stepR1StarWord item phase).2.2 == phase) = false := beq_false_of_ne hsame
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnot : (stepR1StarWord item phase).2.2 = !phase := by
        cases phase <;> cases h : (stepR1StarWord item false).2.2 <;>
          cases h2 : (stepR1StarWord item true).2.2 <;> simp_all
      have halt : (stepR1StarWord item (stepR1StarWord item phase).2.2).2.2 = phase := by
        rw [hnot, stepR1StarWord_phase_inv item phase hitem]
        cases phase <;> cases h : (stepR1StarWord item false).2.2 <;>
          cases h2 : (stepR1StarWord item true).2.2 <;> simp_all
      generalize hq : count / 2 = q
      generalize hrem : count % 2 = rem
      have hdiv : count = 2 * q + rem := by omega
      simp only [evalRStack_cons]
      rw [hdiv, list_pow_add, listblank_append_assoc]
      have hR_rem : HasRoundtrip (fun k => ((wordR item) ^ rem) +> evalRStack rest (R k)) :=
        hasRoundtrip_pow rem item hitem hR_rest
      refine stepStar_trans
        (stepR1Star_alt_pow q item phase (evalRle rle) hitem halt hR_rem (k1 + 2 * totalRes)) ?_
      dsimp -failIfUnchanged only
      rw [← evalRle_pushRle]
      have hadd1 : k1 + 2 * totalRes +
          2 * (q * ((stepR1StarWord item phase).2.1 +
            (stepR1StarWord item (stepR1StarWord item phase).2.2).2.1)) =
          k1 + 2 * (totalRes + q * ((stepR1StarWord item phase).2.1 +
            (stepR1StarWord item (stepR1StarWord item phase).2.2).2.1)) := by omega
      rw [hadd1]
      rcases (by omega : rem = 0 ∨ rem = 1) with rfl | rfl
      · have h01 : (0 == 1) = false := rfl
        rw [h01]
        simp only [Bool.false_eq_true, ↓reduceIte, pow_zero_list, listblank_append_nil]
        exact sweepStarLoop_sound rest _ phase _ hrest hR k1
      · simp only [beq_self_eq_true, ↓reduceIte, pow_succ_list, pow_zero_list, List.append_nil]
        refine stepStar_trans
          (stepR1StarWord_sound item phase _ hitem hR_rest _) ?_
        dsimp -failIfUnchanged only
        rw [← evalRle_pushRle_one]
        have hadd2 : k1 + 2 * (totalRes + q * ((stepR1StarWord item phase).2.1 +
              (stepR1StarWord item (stepR1StarWord item phase).2.2).2.1)) +
            2 * (stepR1StarWord item phase).2.1 =
            k1 + 2 * (totalRes + q * ((stepR1StarWord item phase).2.1 +
              (stepR1StarWord item (stepR1StarWord item phase).2.2).2.1) +
              (stepR1StarWord item phase).2.1) := by omega
        rw [hadd2]
        exact sweepStarLoop_sound rest _ _ _ hrest hR k1

-- ============================================================================
-- Section 6.7: Turnaround, Special Loops, and Macro-Step Soundness
-- ============================================================================

def modeCfg : Mode → ListBlank (Fin 2) → ListBlank (Fin 2) → Cfg (Fin 2) (Fin 6)
  | .R0, l, r => r0Cfg l r
  | .R1, l, r => r1Cfg l r
  | .R1_ODD, l, r => r1OddCfg l r

@[simp] lemma modeCfg_R0 (l r : ListBlank (Fin 2)) : modeCfg .R0 l r = r0Cfg l r := rfl
@[simp] lemma modeCfg_R1 (l r : ListBlank (Fin 2)) : modeCfg .R1 l r = r1Cfg l r := rfl
@[simp] lemma modeCfg_R1_ODD (l r : ListBlank (Fin 2)) : modeCfg .R1_ODD l r = r1OddCfg l r := rfl

def stepOneTok (rle : Rle) (mode : Mode) (t : Tok) : Option (Rle × Mode) :=
  match mode, t with
  | .R0, .PTTTM_TAIL => some (pushRle [.Z] 1 rle, .R1)
  | .R0, .Z => some (pushRle [.Z] 1 rle, .R0)
  | .R0, .P => some (pushRle [.P] 1 rle, .R0)
  | .R1, .Z => some (pushToksLtr [.Z, .M] rle, .R0)
  | .R1, .P => some (pushRle [.P] 1 rle, .R1_ODD)
  | .R1_ODD, .Z => some (pushRle [.Z] 1 rle, .R1_ODD)
  | .R1_ODD, .P => some (pushRle [.Z] 1 rle, .R1)
  | _, _ => none

theorem stepOneTok_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : ListBlank (Fin 2))
    (h : stepOneTok rle mode t = some (rle', mode')) :
    (modeCfg mode (evalRle rle) (tokR t +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r) := by
  cases mode with
  | R0 =>
    cases t with
    | Z =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r0_Z (evalRle rle) r⟩
    | P =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r0_P (evalRle rle) r⟩
    | PTTTM_TAIL =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r0_PTTTM_TAIL (evalRle rle) r⟩
    | U => nomatch h
    | M => nomatch h
    | W => nomatch h
    | T => nomatch h
  | R1 =>
    cases t with
    | Z =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, pushToksLtr, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r1_Z (evalRle rle) r⟩
    | P =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r1_P (evalRle rle) r⟩
    | U => nomatch h
    | M => nomatch h
    | W => nomatch h
    | T => nomatch h
    | PTTTM_TAIL => nomatch h
  | R1_ODD =>
    cases t with
    | Z =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r1Odd_Z (evalRle rle) r⟩
    | P =>
      simp only [stepOneTok, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg, evalRle_pushRle_one, wordL_cons, wordL_nil, List.append_nil]
      exact ⟨_, r1Odd_P (evalRle rle) r⟩
    | U => nomatch h
    | M => nomatch h
    | W => nomatch h
    | T => nomatch h
    | PTTTM_TAIL => nomatch h

def stepOneWord : Rle → Mode → List Tok → Option (Rle × Mode)
  | rle, mode, [] => some (rle, mode)
  | rle, mode, t :: ts =>
    match stepOneTok rle mode t with
    | some (rle1, mode1) => stepOneWord rle1 mode1 ts
    | none => none

theorem stepOneWord_sound : ∀ (w : List Tok) (rle rle' : Rle) (mode mode' : Mode) (r : ListBlank (Fin 2)),
    stepOneWord rle mode w = some (rle', mode') →
    (modeCfg mode (evalRle rle) (wordR w +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r)
  | [], rle, rle', mode, mode', r, h => by
    simp only [stepOneWord, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact stepStar_refl _ _
  | t :: ts, rle, rle', mode, mode', r, h => by
    unfold stepOneWord at h
    cases ht : stepOneTok rle mode t with
    | none => rw [ht] at h; nomatch h
    | some p =>
      rcases p with ⟨rle1, mode1⟩
      rw [ht] at h
      rw [wordR_cons, listblank_append_assoc]
      refine stepStar_trans (stepOneTok_sound rle rle1 mode mode1 t (wordR ts +> r) ht) ?_
      exact stepOneWord_sound ts rle1 rle' mode1 mode' r h

theorem r1_PP_pow : ∀ (q : Nat) (l r : ListBlank (Fin 2)),
    (r1Cfg l (((wordR [.P]) ^ (2 * q)) +> r)) [target_tm]⊢*
      (r1Cfg (((wordL [.Z, .P]) ^ q) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | q + 1, l, r => by
    have h2 : 2 * (q + 1) = 1 + (1 + 2 * q) := by omega
    rw [h2, list_pow_add, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil,
      wordR_cons, wordR_nil, List.append_nil, listblank_append_assoc, listblank_append_assoc]
    refine stepStar_trans ⟨_, r1_P l _⟩ ?_
    refine stepStar_trans ⟨_, r1Odd_P (tokL .P +> l) _⟩ ?_
    have ih := r1_PP_pow q (wordL [.Z, .P] +> l) r
    have hw : tokL .Z +> (tokL .P +> l) = wordL [.Z, .P] +> l := by
      simp [wordL_cons, wordL_nil, listblank_append_assoc]
    rw [hw, pow_succ_right, listblank_append_assoc]
    exact ih

theorem r1Odd_PP_pow : ∀ (q : Nat) (l r : ListBlank (Fin 2)),
    (r1OddCfg l (((wordR [.P]) ^ (2 * q)) +> r)) [target_tm]⊢*
      (r1OddCfg (((wordL [.P, .Z]) ^ q) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | q + 1, l, r => by
    have h2 : 2 * (q + 1) = 1 + (1 + 2 * q) := by omega
    rw [h2, list_pow_add, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil,
      wordR_cons, wordR_nil, List.append_nil, listblank_append_assoc, listblank_append_assoc]
    refine stepStar_trans ⟨_, r1Odd_P l _⟩ ?_
    refine stepStar_trans ⟨_, r1_P (tokL .Z +> l) _⟩ ?_
    have ih := r1Odd_PP_pow q (wordL [.P, .Z] +> l) r
    have hw : tokL .P +> (tokL .Z +> l) = wordL [.P, .Z] +> l := by
      simp [wordL_cons, wordL_nil, listblank_append_assoc]
    rw [hw, pow_succ_right, listblank_append_assoc]
    exact ih

def stepOneBounceFuel : Nat → List Tok → Nat → Rle → Mode → Option (Rle × Mode)
  | _, _, 0, rle, mode => some (rle, mode)
  | 0, _, _ + 1, _, _ => none
  | fuel + 1, item, count + 1, rle, mode =>
    if mode == .R0 && isZpWord item then
      some (pushRle (revWord item) (count + 1) rle, .R0)
    else if item == [.P] && mode == .R1 && count >= 1 then
      let q := (count + 1) / 2
      let rem := (count + 1) % 2
      stepOneBounceFuel fuel [.P] rem (pushRle [.Z, .P] q rle) .R1
    else if item == [.P] && mode == .R1_ODD && count >= 1 then
      let q := (count + 1) / 2
      let rem := (count + 1) % 2
      stepOneBounceFuel fuel [.P] rem (pushRle [.P, .Z] q rle) .R1_ODD
    else
      match stepOneWord rle mode item with
      | some (rle1, mode1) => stepOneBounceFuel fuel item count rle1 mode1
      | none => none

theorem stepOneBounceFuel_sound : ∀ (fuel : Nat) (item : List Tok) (count : Nat)
    (rle rle' : Rle) (mode mode' : Mode) (r : ListBlank (Fin 2)),
    stepOneBounceFuel fuel item count rle mode = some (rle', mode') →
    (modeCfg mode (evalRle rle) (((wordR item) ^ count) +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r)
  | _, _, 0, rle, rle', mode, mode', r, h => by
    simp only [stepOneBounceFuel, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact stepStar_refl _ _
  | 0, _, _ + 1, _, _, _, _, _, h => by nomatch h
  | fuel + 1, item, count + 1, rle, rle', mode, mode', r, h => by
    unfold stepOneBounceFuel at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, beq_iff_eq] at hcond
      rcases hcond with ⟨rfl, hitem⟩
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [modeCfg_R0, evalRle_pushRle]
      exact r0_pow (count + 1) item (evalRle rle) r hitem
    · split at h
      · rename_i hcond2
        simp only [Bool.and_eq_true, beq_iff_eq, ge_iff_le, decide_eq_true_eq] at hcond2
        rcases hcond2 with ⟨⟨rfl, rfl⟩, _⟩
        generalize hq : (count + 1) / 2 = q at h
        generalize hrem : (count + 1) % 2 = rem at h
        have hdiv : count + 1 = 2 * q + rem := by omega
        rw [hdiv, list_pow_add, listblank_append_assoc]
        simp only [modeCfg_R1]
        refine stepStar_trans (r1_PP_pow q (evalRle rle) (((wordR [.P]) ^ rem) +> r)) ?_
        rw [← evalRle_pushRle]
        exact stepOneBounceFuel_sound fuel [.P] rem (pushRle [.Z, .P] q rle) rle' .R1 mode' r h
      · split at h
        · rename_i hcond3
          simp only [Bool.and_eq_true, beq_iff_eq, ge_iff_le, decide_eq_true_eq] at hcond3
          rcases hcond3 with ⟨⟨rfl, rfl⟩, _⟩
          generalize hq : (count + 1) / 2 = q at h
          generalize hrem : (count + 1) % 2 = rem at h
          have hdiv : count + 1 = 2 * q + rem := by omega
          rw [hdiv, list_pow_add, listblank_append_assoc]
          simp only [modeCfg_R1_ODD]
          refine stepStar_trans (r1Odd_PP_pow q (evalRle rle) (((wordR [.P]) ^ rem) +> r)) ?_
          rw [← evalRle_pushRle]
          exact stepOneBounceFuel_sound fuel [.P] rem (pushRle [.P, .Z] q rle) rle' .R1_ODD mode' r h
        · cases hw : stepOneWord rle mode item with
          | none => rw [hw] at h; nomatch h
          | some p =>
            rcases p with ⟨rle1, mode1⟩
            rw [hw] at h
            rw [pow_succ_list, listblank_append_assoc]
            refine stepStar_trans (stepOneWord_sound item rle rle1 mode mode1 (((wordR item) ^ count) +> r) hw) ?_
            exact stepOneBounceFuel_sound fuel item count rle1 rle' mode1 mode' r h

def simpleOneBounceCarry : Rle → Mode → Rle → Nat → Option (Rle × Nat)
  | rle, mode, [], k1 =>
    if mode == .R0 then
      some (rle, k1 + 2)
    else none
  | rle, mode, (item, count) :: rest, k1 =>
    match stepOneBounceFuel 3 item count rle mode with
    | some (rle', mode') => simpleOneBounceCarry rle' mode' rest k1
    | none => none

theorem simpleOneBounceCarry_sound : ∀ (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : Nat),
    simpleOneBounceCarry rle mode rs k1 = some (rle', kOut) →
    (modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1))) [target_tm]⊢*
      (carryCfg (evalRle rle') (evalWK kOut))
  | [], rle, rle', mode, k1, kOut, h => by
    unfold simpleOneBounceCarry at h
    split at h
    · rename_i hm
      rw [beq_iff_eq] at hm; subst hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact r0_end k1 (evalRle rle)
    · nomatch h
  | (item, count) :: rest, rle, rle', mode, k1, kOut, h => by
    unfold simpleOneBounceCarry at h
    cases hb : stepOneBounceFuel 3 item count rle mode with
    | none => rw [hb] at h; nomatch h
    | some p =>
      rcases p with ⟨rle1, mode1⟩
      rw [hb] at h
      simp only [evalRStack_cons]
      refine stepStar_trans (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ hb) ?_
      exact simpleOneBounceCarry_sound rest rle1 rle' mode1 k1 kOut h

def hasSpecial : Rle → Bool
  | [] => false
  | (it, _) :: rest => (it == [.PTTTM_TAIL]) || hasSpecial rest

def runRightSweepStarCarry (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : Nat) : Option (Rle × Nat) :=
  if mode == .R0 then
    match copyRStack rle rStack with
    | some rle' => some (rle', k1 + 2)
    | none => none
  else if hasSpecial rStack then
    simpleOneBounceCarry rle mode rStack k1
  else if allZpStack rStack then
    let initPhase := mode != .R1
    let (rle1, finalPhase, totalRes) := sweepStarLoop rle initPhase 0 rStack
    let kFinal1 := k1 + 2 * totalRes
    if !finalPhase then
      some (stepZtToCarry (pushRle [.P] 1 rle1) (kFinal1 + 1))
    else
      some (stepZtToCarry (pushRle [.Z] 1 rle1) kFinal1)
  else none

theorem runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : Nat)
    (h : runRightSweepStarCarry rle mode rStack k1 = some (rOut, kOut)) :
    (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1))) [target_tm]⊢*
      (carryCfg (evalRle rOut) (evalWK kOut)) := by
  unfold runRightSweepStarCarry at h
  split at h
  · rename_i hm
    rw [beq_iff_eq] at hm; subst hm
    cases hc : copyRStack rle rStack with
    | none => rw [hc] at h; nomatch h
    | some rle' =>
      rw [hc] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨h1, h2⟩
      rw [← h1, ← h2]
      simp only [modeCfg_R0]
      refine stepStar_trans (copyRStack_sound rStack rle rle' (evalWK k1) hc).2 ?_
      exact r0_end k1 (evalRle rle')
  · rename_i hm
    split at h
    · exact simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h
    · split at h
      · rename_i hall
        have hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
            r1PhaseCfg (mode != .R1) (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0))) := by
          cases mode with
          | R0 => exfalso; exact hm rfl
          | R1 => rfl
          | R1_ODD => rfl
        rw [hphase]
        refine stepStar_trans
          (sweepStarLoop_sound rStack rle (mode != .R1) 0 hall hasRoundtrip_evalWK k1) ?_
        dsimp -failIfUnchanged only at h ⊢
        generalize hsw : sweepStarLoop rle (mode != .R1) 0 rStack = sw at h ⊢
        rcases sw with ⟨rle1, finalPhase, totalRes⟩
        dsimp -failIfUnchanged only at h ⊢
        cases finalPhase with
        | false =>
          change some (stepZtToCarry (pushRle [.P] 1 rle1) (k1 + 2 * totalRes + 1)) = some (rOut, kOut) at h
          simp only [Option.some.injEq] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp -failIfUnchanged only at h1 h2
          rw [← h1, ← h2]
          simp only [r1PhaseCfg_false]
          refine stepStar_trans (r1_end (k1 + 2 * totalRes) (evalRle rle1)) ?_
          have hzt := stepZtToCarry_sound (pushRle [.P] 1 rle1) (k1 + 2 * totalRes + 1)
          rw [evalRle_pushRle_one] at hzt
          exact hzt
        | true =>
          change some (stepZtToCarry (pushRle [.Z] 1 rle1) (k1 + 2 * totalRes)) = some (rOut, kOut) at h
          simp only [Option.some.injEq] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp -failIfUnchanged only at h1 h2
          rw [← h1, ← h2]
          simp only [r1PhaseCfg_true]
          refine stepStar_trans (r1Odd_end (k1 + 2 * totalRes) (evalRle rle1)) ?_
          have hzt := stepZtToCarry_sound (pushRle [.Z] 1 rle1) (k1 + 2 * totalRes)
          rw [evalRle_pushRle_one] at hzt
          exact hzt
      · nomatch h

inductive StepCarryRes
  | halt
  | next (rle : Rle) (k1 : Nat)
  | err
  deriving DecidableEq, Repr

def StepCarryValid (cfg : Cfg (Fin 2) (Fin 6)) : StepCarryRes → Prop
  | .halt => ∃ cfg', (cfg [target_tm]⊢* cfg') ∧ (step target_tm cfg').isNone
  | .next rOut kOut => cfg [target_tm]⊢* carryCfg (evalRle rOut) (evalWK kOut)
  | .err => False

theorem stepCarryValid_of_stepStar {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)} {res : StepCarryRes}
    (hstep : cfg₁ [target_tm]⊢* cfg₂) (hval : StepCarryValid cfg₂ res) :
    StepCarryValid cfg₁ res := by
  cases res with
  | halt =>
    rcases hval with ⟨cfg', h2, hnone⟩
    exact ⟨cfg', stepStar_trans hstep h2, hnone⟩
  | next rOut kOut =>
    exact stepStar_trans hstep hval
  | err => exact hval

def finishTurn (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : Nat) : StepCarryRes :=
  match runRightSweepStarCarry rle mode rStack k1 with
  | some (rOut, kOut) => .next rOut kOut
  | none => .err

theorem finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : Nat)
    (hne : finishTurn rle mode rStack k1 ≠ .err) :
    StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
      (finishTurn rle mode rStack k1) := by
  unfold finishTurn at hne ⊢
  cases hr : runRightSweepStarCarry rle mode rStack k1 with
  | none => rw [hr] at hne; exfalso; exact hne rfl
  | some p =>
    rcases p with ⟨rOut, kOut⟩
    exact runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut hr

def stepTurnaround (r2 : Rle) (rStack : Rle) (k1 : Nat) : StepCarryRes :=
  if r2 == [([.M], 1), ([.U], 1)] then
    finishTurn [([.M], 1), ([.U], 1)] .R1 rStack k1
  else if r2 == [([.T], 1), ([.M], 1), ([.U], 1)] then
    finishTurn [([.Z], 1), ([.U], 1)] .R1 rStack k1
  else match popToks [.T, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .M] r') .R1 rStack k1
  | none => match popToks [.M, .W] r2 with
  | some r' => finishTurn (pushToksLtr [.T] r') .R1 rStack k1
  | none => match popToks [.T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .P] r') .R0 rStack k1
  | none => match popToks [.M, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.P] r') .R1 rStack k1
  | none => match popToks [.W, .T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.M, .U, .Z] r') .R1_ODD rStack k1
  | none => match popToks [.M, .T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .Z] r') .R1 rStack k1
  | none => match popToks [.T, .T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.M, .U, .Z] r') .R1 rStack k1
  | none => match popToks [.U, .M, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .T] r') .R1_ODD rStack k1
  | none => match popToks [.M, .T, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .M, .P] r') .R0 rStack k1
  | none => match popToks [.T, .T, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .W, .P] r') .R0 rStack k1
  | none => match popToks [.W, .T, .U, .M] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .Z] r') .R1_ODD rStack k1
  | none => match popToks [.M, .T, .T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.M, .U, .Z, .P] r') .R0 rStack k1
  | none => match popToks [.W, .T, .T, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.P, .Z, .Z] r') .R0 rStack k1
  | none => match popToks [.M, .T, .T, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .W, .Z] r') .R1 rStack k1
  | none => match popToks [.U, .M, .P, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .W, .M, .P] r') .R0 rStack k1
  | none => match popToks [.M, .T, .U, .M, .Z] r2 with
  | some r' => finishTurn (pushToksLtr [.P, .Z, .P] r') .R0 rStack k1
  | none => match popToks [.W, .T, .T, .T, .P] r2 with
  | some r' => finishTurn (pushToksLtr [.T, .Z, .Z, .Z] r') .R0 rStack k1
  | none => .err

theorem turnBranch_sound (pat out : List Tok) (mode : Mode) (r2 r' rStack : Rle) (k1 : Nat)
    (hp : popToks pat r2 = some r')
    (hturn : (carryCfg (wordL pat +> evalRle r') (evalRStack rStack (evalWK k1))) [target_tm]⊢*
      (modeCfg mode (evalRle (pushToksLtr out r')) (evalRStack rStack (evalWK k1))))
    (hne : finishTurn (pushToksLtr out r') mode rStack k1 ≠ .err) :
    StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
      (finishTurn (pushToksLtr out r') mode rStack k1) := by
  rw [popToks_sound pat r2 r' hp]
  exact stepCarryValid_of_stepStar hturn (finishTurn_sound (pushToksLtr out r') mode rStack k1 hne)

theorem stepTurnaround_sound (r2 rStack : Rle) (k1 : Nat)
    (hne : stepTurnaround r2 rStack k1 ≠ .err) :
    StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
      (stepTurnaround r2 rStack k1) := by
  unfold stepTurnaround at hne ⊢
  split
  · rename_i h1
    rw [if_pos h1] at hne
    rw [beq_iff_eq] at h1; subst h1
    refine stepCarryValid_of_stepStar ?_ (finishTurn_sound [([.M], 1), ([.U], 1)] .R1 rStack k1 hne)
    simp only [evalRle_cons, evalRle_nil, pow_succ_list, pow_zero_list, List.append_nil,
      wordL_cons, wordL_nil, modeCfg_R1]
    exact ⟨_, turn_UM (evalRStack rStack (evalWK k1))⟩
  · rename_i h1
    rw [if_neg h1] at hne
    split
    · rename_i h2
      rw [if_pos h2] at hne
      rw [beq_iff_eq] at h2; subst h2
      refine stepCarryValid_of_stepStar ?_ (finishTurn_sound [([.Z], 1), ([.U], 1)] .R1 rStack k1 hne)
      simp only [evalRle_cons, evalRle_nil, pow_succ_list, pow_zero_list, List.append_nil,
        wordL_cons, wordL_nil, modeCfg_R1]
      exact ⟨_, turn_UMT (evalRStack rStack (evalWK k1))⟩
    · rename_i h2
      rw [if_neg h2] at hne
      cases hp0 : popToks [.T, .Z] r2 with
      | some r' =>
        rw [hp0] at hne; dsimp -failIfUnchanged only at hne ⊢
        refine turnBranch_sound [.T, .Z] [.T, .M] .R1 r2 r' rStack k1 hp0 ?_ hne
        simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
        exact ⟨_, turn_ZT (evalRle r') (evalRStack rStack (evalWK k1))⟩
      | none =>
        rw [hp0] at hne; dsimp -failIfUnchanged only at hne ⊢
        cases hp1 : popToks [.M, .W] r2 with
        | some r' =>
          rw [hp1] at hne; dsimp -failIfUnchanged only at hne ⊢
          refine turnBranch_sound [.M, .W] [.T] .R1 r2 r' rStack k1 hp1 ?_ hne
          simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
          exact ⟨_, turn_WM (evalRle r') (evalRStack rStack (evalWK k1))⟩
        | none =>
          rw [hp1] at hne; dsimp -failIfUnchanged only at hne ⊢
          cases hp2 : popToks [.T, .P] r2 with
          | some r' =>
            rw [hp2] at hne; dsimp -failIfUnchanged only at hne ⊢
            refine turnBranch_sound [.T, .P] [.T, .P] .R0 r2 r' rStack k1 hp2 ?_ hne
            simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
            exact ⟨_, turn_PT (evalRle r') (evalRStack rStack (evalWK k1))⟩
          | none =>
            rw [hp2] at hne; dsimp -failIfUnchanged only at hne ⊢
            cases hp3 : popToks [.M, .Z] r2 with
            | some r' =>
              rw [hp3] at hne; dsimp -failIfUnchanged only at hne ⊢
              refine turnBranch_sound [.M, .Z] [.P] .R1 r2 r' rStack k1 hp3 ?_ hne
              simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
              exact ⟨_, turn_ZM (evalRle r') (evalRStack rStack (evalWK k1))⟩
            | none =>
              rw [hp3] at hne; dsimp -failIfUnchanged only at hne ⊢
              cases hp4 : popToks [.W, .T, .P] r2 with
              | some r' =>
                rw [hp4] at hne; dsimp -failIfUnchanged only at hne ⊢
                refine turnBranch_sound [.W, .T, .P] [.M, .U, .Z] .R1_ODD r2 r' rStack k1 hp4 ?_ hne
                simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                exact ⟨_, turn_PTW (evalRle r') (evalRStack rStack (evalWK k1))⟩
              | none =>
                rw [hp4] at hne; dsimp -failIfUnchanged only at hne ⊢
                cases hp5 : popToks [.M, .T, .P] r2 with
                | some r' =>
                  rw [hp5] at hne; dsimp -failIfUnchanged only at hne ⊢
                  refine turnBranch_sound [.M, .T, .P] [.T, .Z] .R1 r2 r' rStack k1 hp5 ?_ hne
                  simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                  exact ⟨_, turn_PTM (evalRle r') (evalRStack rStack (evalWK k1))⟩
                | none =>
                  rw [hp5] at hne; dsimp -failIfUnchanged only at hne ⊢
                  cases hp6 : popToks [.T, .T, .P] r2 with
                  | some r' =>
                    rw [hp6] at hne; dsimp -failIfUnchanged only at hne ⊢
                    refine turnBranch_sound [.T, .T, .P] [.M, .U, .Z] .R1 r2 r' rStack k1 hp6 ?_ hne
                    simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                    exact ⟨_, turn_PTT (evalRle r') (evalRStack rStack (evalWK k1))⟩
                  | none =>
                    rw [hp6] at hne; dsimp -failIfUnchanged only at hne ⊢
                    cases hp7 : popToks [.U, .M, .Z] r2 with
                    | some r' =>
                      rw [hp7] at hne; dsimp -failIfUnchanged only at hne ⊢
                      refine turnBranch_sound [.U, .M, .Z] [.T, .T] .R1_ODD r2 r' rStack k1 hp7 ?_ hne
                      simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                      exact ⟨_, turn_ZMU (evalRle r') (evalRStack rStack (evalWK k1))⟩
                    | none =>
                      rw [hp7] at hne; dsimp -failIfUnchanged only at hne ⊢
                      cases hp8 : popToks [.M, .T, .Z] r2 with
                      | some r' =>
                        rw [hp8] at hne; dsimp -failIfUnchanged only at hne ⊢
                        refine turnBranch_sound [.M, .T, .Z] [.T, .M, .P] .R0 r2 r' rStack k1 hp8 ?_ hne
                        simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                        exact ⟨_, turn_ZTM (evalRle r') (evalRStack rStack (evalWK k1))⟩
                      | none =>
                        rw [hp8] at hne; dsimp -failIfUnchanged only at hne ⊢
                        cases hp9 : popToks [.T, .T, .Z] r2 with
                        | some r' =>
                          rw [hp9] at hne; dsimp -failIfUnchanged only at hne ⊢
                          refine turnBranch_sound [.T, .T, .Z] [.T, .W, .P] .R0 r2 r' rStack k1 hp9 ?_ hne
                          simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                          exact ⟨_, turn_ZTT (evalRle r') (evalRStack rStack (evalWK k1))⟩
                        | none =>
                          rw [hp9] at hne; dsimp -failIfUnchanged only at hne ⊢
                          cases hp10 : popToks [.W, .T, .U, .M] r2 with
                          | some r' =>
                            rw [hp10] at hne; dsimp -failIfUnchanged only at hne ⊢
                            refine turnBranch_sound [.W, .T, .U, .M] [.T, .Z] .R1_ODD r2 r' rStack k1 hp10 ?_ hne
                            simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                            exact ⟨_, turn_MUTW (evalRle r') (evalRStack rStack (evalWK k1))⟩
                          | none =>
                            rw [hp10] at hne; dsimp -failIfUnchanged only at hne ⊢
                            cases hp11 : popToks [.M, .T, .T, .P] r2 with
                            | some r' =>
                              rw [hp11] at hne; dsimp -failIfUnchanged only at hne ⊢
                              refine turnBranch_sound [.M, .T, .T, .P] [.M, .U, .Z, .P] .R0 r2 r' rStack k1 hp11 ?_ hne
                              simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                              exact ⟨_, turn_PTTM (evalRle r') (evalRStack rStack (evalWK k1))⟩
                            | none =>
                              rw [hp11] at hne; dsimp -failIfUnchanged only at hne ⊢
                              cases hp12 : popToks [.W, .T, .T, .Z] r2 with
                              | some r' =>
                                rw [hp12] at hne; dsimp -failIfUnchanged only at hne ⊢
                                refine turnBranch_sound [.W, .T, .T, .Z] [.P, .Z, .Z] .R0 r2 r' rStack k1 hp12 ?_ hne
                                simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                                exact ⟨_, turn_ZTTW (evalRle r') (evalRStack rStack (evalWK k1))⟩
                              | none =>
                                rw [hp12] at hne; dsimp -failIfUnchanged only at hne ⊢
                                cases hp13 : popToks [.M, .T, .T, .Z] r2 with
                                | some r' =>
                                  rw [hp13] at hne; dsimp -failIfUnchanged only at hne ⊢
                                  refine turnBranch_sound [.M, .T, .T, .Z] [.T, .W, .Z] .R1 r2 r' rStack k1 hp13 ?_ hne
                                  simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                                  exact ⟨_, turn_ZTTM (evalRle r') (evalRStack rStack (evalWK k1))⟩
                                | none =>
                                  rw [hp13] at hne; dsimp -failIfUnchanged only at hne ⊢
                                  cases hp14 : popToks [.U, .M, .P, .Z] r2 with
                                  | some r' =>
                                    rw [hp14] at hne; dsimp -failIfUnchanged only at hne ⊢
                                    refine turnBranch_sound [.U, .M, .P, .Z] [.T, .W, .M, .P] .R0 r2 r' rStack k1 hp14 ?_ hne
                                    simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                                    exact ⟨_, turn_ZPMU (evalRle r') (evalRStack rStack (evalWK k1))⟩
                                  | none =>
                                    rw [hp14] at hne; dsimp -failIfUnchanged only at hne ⊢
                                    cases hp15 : popToks [.M, .T, .U, .M, .Z] r2 with
                                    | some r' =>
                                      rw [hp15] at hne; dsimp -failIfUnchanged only at hne ⊢
                                      refine turnBranch_sound [.M, .T, .U, .M, .Z] [.P, .Z, .P] .R0 r2 r' rStack k1 hp15 ?_ hne
                                      simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                                      exact ⟨_, turn_ZMUTM (evalRle r') (evalRStack rStack (evalWK k1))⟩
                                    | none =>
                                      rw [hp15] at hne; dsimp -failIfUnchanged only at hne ⊢
                                      cases hp16 : popToks [.W, .T, .T, .T, .P] r2 with
                                      | some r' =>
                                        rw [hp16] at hne; dsimp -failIfUnchanged only at hne ⊢
                                        refine turnBranch_sound [.W, .T, .T, .T, .P] [.T, .Z, .Z, .Z] .R0 r2 r' rStack k1 hp16 ?_ hne
                                        simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc, pushToksLtr, evalRle_pushRle_one, modeCfg]
                                        exact ⟨_, turn_PTTTW (evalRle r') (evalRStack rStack (evalWK k1))⟩
                                      | none =>
                                        rw [hp16] at hne; dsimp -failIfUnchanged only at hne ⊢
                                        exfalso; exact hne rfl

theorem wordL_Z_pow (n : Nat) : (wordL [.Z]) ^ n = (tokL .Z) ^ n := rfl
theorem wordL_P_pow (n : Nat) : (wordL [.P]) ^ n = (tokL .P) ^ n := rfl

theorem special_ZTM_loop : ∀ (n : Nat) (l : ListBlank (Fin 2)) {R : Nat → ListBlank (Fin 2)},
    HasRoundtrip R → ∀ (k1 : Nat),
    (carryCfg (tokL .M +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l))) (R k1)) [target_tm]⊢*
      (r0Cfg (((tokL .P) ^ (n + 1)) +> (tokL .M +> (tokL .T +> l))) (R (k1 + 2 * n)))
  | 0, l, R, _, k1 => by
    simp only [Nat.zero_add, pow_succ_list, pow_zero_list, List.append_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨_, turn_ZTM l (R k1)⟩
  | n + 1, l, R, hR, k1 => by
    rw [pow_succ_list (tokL .Z) (n + 1), listblank_append_assoc]
    refine stepStar_trans ⟨_, turn_ZTM (((tokL .Z) ^ (n + 1)) +> l) (R k1)⟩ ?_
    refine stepStar_trans (hR (tokL .P +> (tokL .M +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l)))) k1) ?_
    refine stepStar_trans ⟨_, carry_P (tokL .M +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l))) (R (k1 + 2))⟩ ?_
    refine stepStar_trans (special_ZTM_loop n l (hasRoundtrip_P hR) (k1 + 2)) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans ⟨_, r0_P (((tokL .P) ^ (n + 1)) +> (tokL .M +> (tokL .T +> l))) (R (k1 + 2 + 2 * n))⟩ ?_
    have hadd : k1 + 2 + 2 * n = k1 + 2 * (n + 1) := by omega
    rw [hadd, ← listblank_append_assoc, ← pow_succ_list (tokL .P) (n + 1)]
    exact stepStar_refl _ _

theorem special_PT_loop : ∀ (n : Nat) (l : ListBlank (Fin 2)) {R : Nat → ListBlank (Fin 2)},
    HasRoundtrip R → ∀ (k1 : Nat),
    (carryCfg (tokL .T +> (((tokL .P) ^ (n + 1)) +> l)) (R k1)) [target_tm]⊢*
      (r0Cfg (((tokL .P) ^ (n + 1)) +> (tokL .T +> l)) (R (k1 + 2 * n)))
  | 0, l, R, _, k1 => by
    simp only [Nat.zero_add, pow_succ_list, pow_zero_list, List.append_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨_, turn_PT l (R k1)⟩
  | n + 1, l, R, hR, k1 => by
    rw [pow_succ_list (tokL .P) (n + 1), listblank_append_assoc]
    refine stepStar_trans ⟨_, turn_PT (((tokL .P) ^ (n + 1)) +> l) (R k1)⟩ ?_
    refine stepStar_trans (hR (tokL .P +> (tokL .T +> (((tokL .P) ^ (n + 1)) +> l))) k1) ?_
    refine stepStar_trans ⟨_, carry_P (tokL .T +> (((tokL .P) ^ (n + 1)) +> l)) (R (k1 + 2))⟩ ?_
    refine stepStar_trans (special_PT_loop n l (hasRoundtrip_P hR) (k1 + 2)) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans ⟨_, r0_P (((tokL .P) ^ (n + 1)) +> (tokL .T +> l)) (R (k1 + 2 + 2 * n))⟩ ?_
    have hadd : k1 + 2 + 2 * n = k1 + 2 * (n + 1) := by omega
    rw [hadd, ← listblank_append_assoc, ← pow_succ_list (tokL .P) (n + 1)]
    exact stepStar_refl _ _

theorem special_ZTW_loop : ∀ (n : Nat) (l : ListBlank (Fin 2)) {R : Nat → ListBlank (Fin 2)},
    HasRoundtrip R → ∀ (k1 : Nat),
    (carryCfg (tokL .W +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l))) (R k1)) [target_tm]⊢*
      (r0Cfg (((tokL .Z) ^ (n + 1)) +> (tokL .W +> (tokL .T +> l))) (R (k1 + 2 * n)))
  | 0, l, R, _, k1 => by
    simp only [Nat.zero_add, pow_succ_list, pow_zero_list, List.append_nil, Nat.mul_zero, Nat.add_zero]
    exact ⟨_, turn_ZTW l (R k1)⟩
  | n + 1, l, R, hR, k1 => by
    rw [pow_succ_list (tokL .Z) (n + 1), listblank_append_assoc]
    refine stepStar_trans ⟨_, turn_ZTW (((tokL .Z) ^ (n + 1)) +> l) (R k1)⟩ ?_
    refine stepStar_trans (hR (tokL .Z +> (tokL .W +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l)))) k1) ?_
    refine stepStar_trans ⟨_, carry_Z (tokL .W +> (tokL .T +> (((tokL .Z) ^ (n + 1)) +> l))) (R (k1 + 2))⟩ ?_
    refine stepStar_trans (special_ZTW_loop n l (hasRoundtrip_Z hR) (k1 + 2)) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans ⟨_, r0_Z (((tokL .Z) ^ (n + 1)) +> (tokL .W +> (tokL .T +> l))) (R (k1 + 2 + 2 * n))⟩ ?_
    have hadd : k1 + 2 + 2 * n = k1 + 2 * (n + 1) := by omega
    rw [hadd, ← listblank_append_assoc, ← pow_succ_list (tokL .Z) (n + 1)]
    exact stepStar_refl _ _

def stepSpecialLoops (r2 rStack : Rle) (k1 : Nat) : Option StepCarryRes :=
  match popPrefixCount [.M, .T] [.Z] r2 with
  | some (b, r3) =>
    match copyRStack (pushRle [.P] b (pushToksLtr [.T, .M] r3)) rStack with
    | some r4 => some (.next r4 (k1 + 2 * b))
    | none => some .err
  | none => match popPrefixCount [.T] [.P] r2 with
  | some (b, r3) =>
    match copyRStack (pushRle [.P] b (pushRle [.T] 1 r3)) rStack with
    | some r4 => some (.next r4 (k1 + 2 * b))
    | none => some .err
  | none => match popPrefixCount [.W, .T] [.Z] r2 with
  | some (b, r3) =>
    match copyRStack (pushRle [.Z] b (pushToksLtr [.T, .W] r3)) rStack with
    | some r4 => some (.next r4 (k1 + 2 * b))
    | none => some .err
  | none => match popPrefixCount [.U, .M] [.P] r2 with
  | some (mVal, r3) =>
    match popTok .Z r3 with
    | some r4 =>
      let r5 := pushRle [.P] 1 (pushRle [.Z] (mVal - 1) (pushToksLtr [.T, .W, .M] r4))
      some (finishTurn r5 .R0 rStack k1)
    | none =>
      match popToks [.M, .T] r3 with
      | some _ => some .halt
      | none => some .err
  | none => none

theorem stepSpecialLoops_sound (r2 rStack : Rle) (k1 : Nat) (res : StepCarryRes)
    (h : stepSpecialLoops r2 rStack k1 = some res) (hne : res ≠ .err) :
    StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res := by
  unfold stepSpecialLoops at h
  revert h
  cases hp1 : popPrefixCount [.M, .T] [.Z] r2 with
  | some p1 =>
    rcases p1 with ⟨b, r3⟩
    dsimp -failIfUnchanged only
    rcases popPrefixCount_sound [.M, .T] [.Z] r2 r3 b hp1 with ⟨hb, hr2⟩
    cases hc1 : copyRStack (pushRle [.P] b (pushToksLtr [.T, .M] r3)) rStack with
    | none =>
      intro h; injection h with h'; subst h'; exfalso; exact hne rfl
    | some r4 =>
      intro h; injection h with h'; subst h'
      rcases copyRStack_sound rStack (pushRle [.P] b (pushToksLtr [.T, .M] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc1 with ⟨hrs, hcopy⟩
      have hb1 : b = (b - 1) + 1 := by omega
      have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
      rw [hr2, wordL_Z_pow, hb1]
      simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
      refine stepStar_trans (special_ZTM_loop (b - 1) (evalRle r3) hR k1) ?_
      rw [← hb1]
      simp only [pushToksLtr, evalRle_pushRle, wordL_cons, wordL_nil,
        List.append_nil, pow_succ_list, pow_zero_list] at hcopy
      refine stepStar_trans hcopy ?_
      have hadd : k1 + 2 * (b - 1) + 2 = k1 + 2 * b := by omega
      rw [← hadd]
      exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
  | none =>
    dsimp -failIfUnchanged only
    cases hp2 : popPrefixCount [.T] [.P] r2 with
    | some p2 =>
      rcases p2 with ⟨b, r3⟩
      dsimp -failIfUnchanged only
      rcases popPrefixCount_sound [.T] [.P] r2 r3 b hp2 with ⟨hb, hr2⟩
      cases hc2 : copyRStack (pushRle [.P] b (pushRle [.T] 1 r3)) rStack with
      | none =>
        intro h; injection h with h'; subst h'; exfalso; exact hne rfl
      | some r4 =>
        intro h; injection h with h'; subst h'
        rcases copyRStack_sound rStack (pushRle [.P] b (pushRle [.T] 1 r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc2 with ⟨hrs, hcopy⟩
        have hb1 : b = (b - 1) + 1 := by omega
        have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
        rw [hr2, wordL_P_pow, hb1]
        simp only [wordL_cons, wordL_nil, List.append_nil]
        refine stepStar_trans (special_PT_loop (b - 1) (evalRle r3) hR k1) ?_
        rw [← hb1]
        simp only [evalRle_pushRle, wordL_cons, wordL_nil,
          List.append_nil, pow_succ_list, pow_zero_list] at hcopy
        refine stepStar_trans hcopy ?_
        have hadd : k1 + 2 * (b - 1) + 2 = k1 + 2 * b := by omega
        rw [← hadd]
        exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
    | none =>
      dsimp -failIfUnchanged only
      cases hp3 : popPrefixCount [.W, .T] [.Z] r2 with
      | some p3 =>
        rcases p3 with ⟨b, r3⟩
        dsimp -failIfUnchanged only
        rcases popPrefixCount_sound [.W, .T] [.Z] r2 r3 b hp3 with ⟨hb, hr2⟩
        cases hc3 : copyRStack (pushRle [.Z] b (pushToksLtr [.T, .W] r3)) rStack with
        | none =>
          intro h; injection h with h'; subst h'; exfalso; exact hne rfl
        | some r4 =>
          intro h; injection h with h'; subst h'
          rcases copyRStack_sound rStack (pushRle [.Z] b (pushToksLtr [.T, .W] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc3 with ⟨hrs, hcopy⟩
          have hb1 : b = (b - 1) + 1 := by omega
          have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
          rw [hr2, wordL_Z_pow, hb1]
          simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
          refine stepStar_trans (special_ZTW_loop (b - 1) (evalRle r3) hR k1) ?_
          rw [← hb1]
          simp only [pushToksLtr, evalRle_pushRle, wordL_cons, wordL_nil,
            List.append_nil, pow_succ_list, pow_zero_list] at hcopy
          refine stepStar_trans hcopy ?_
          have hadd : k1 + 2 * (b - 1) + 2 = k1 + 2 * b := by omega
          rw [← hadd]
          exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
      | none =>
        dsimp -failIfUnchanged only
        cases hp4 : popPrefixCount [.U, .M] [.P] r2 with
        | none => intro h; nomatch h
        | some p4 =>
          rcases p4 with ⟨mVal, r3⟩
          dsimp -failIfUnchanged only
          rcases popPrefixCount_sound [.U, .M] [.P] r2 r3 mVal hp4 with ⟨hm, hr2⟩
          rw [hr2, wordL_P_pow]
          simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
          cases hz : popTok .Z r3 with
          | some r4 =>
            intro h; injection h with h'; subst h'
            refine stepCarryValid_of_stepStar
              ⟨_, carry_MU_to_pmuCfg (((tokL .P) ^ mVal) +> evalRle r3) (evalRStack rStack (evalWK k1))⟩ ?_
            refine stepCarryValid_of_stepStar
              (pmu_loop mVal (evalRle r3) (tokR .P +> evalRStack rStack (evalWK k1))) ?_
            rw [popTok_sound .Z r3 r4 hz]
            have hm1 : mVal = 1 + (mVal - 1) := by omega
            rw [hm1, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil, listblank_append_assoc]
            refine stepCarryValid_of_stepStar
              ⟨_, pmuCfg_Z_turn (evalRle r4) (((tokR .Z) ^ (mVal - 1)) +> (tokR .P +> evalRStack rStack (evalWK k1)))⟩ ?_
            refine stepCarryValid_of_stepStar
              (r0_Z_loop (mVal - 1) (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4))) (tokR .P +> evalRStack rStack (evalWK k1))) ?_
            refine stepCarryValid_of_stepStar
              ⟨_, r0_P (((tokL .Z) ^ (mVal - 1)) +> (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4)))) (evalRStack rStack (evalWK k1))⟩ ?_
            have hr5 : tokL .P +> (((tokL .Z) ^ (mVal - 1)) +> (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4)))) =
                evalRle (pushRle [.P] 1 (pushRle [.Z] (mVal - 1) (pushToksLtr [.T, .W, .M] r4))) := by
              simp [pushToksLtr, evalRle_pushRle, wordL_cons, wordL_nil, pow_succ_list, pow_zero_list]
            rw [← hm1, hr5]
            exact finishTurn_sound _ .R0 rStack k1 hne
          | none =>
            dsimp -failIfUnchanged only
            cases hmt : popToks [.M, .T] r3 with
            | none =>
              intro h; injection h with h'; subst h'; exfalso; exact hne rfl
            | some r4 =>
              intro h; injection h with h'; subst h'
              refine stepCarryValid_of_stepStar
                ⟨_, carry_MU_to_pmuCfg (((tokL .P) ^ mVal) +> evalRle r3) (evalRStack rStack (evalWK k1))⟩ ?_
              refine stepCarryValid_of_stepStar
                (pmu_loop mVal (evalRle r3) (tokR .P +> evalRStack rStack (evalWK k1))) ?_
              rw [popToks_sound [.M, .T] r3 r4 hmt]
              simp only [wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
              exact ⟨_, ⟨_, pmuCfg_TM_halt (evalRle r4) (((tokR .Z) ^ mVal) +> (tokR .P +> evalRStack rStack (evalWK k1)))⟩, rfl⟩

def stepCarry (rle : Rle) (k1 : Nat) : StepCarryRes :=
  let (r2, rStack) := popCarryLoop 80 rle []
  if !hasSpecial rStack then
    match stepSpecialLoops r2 rStack k1 with
    | some res => res
    | none => stepTurnaround r2 rStack k1
  else
    stepTurnaround r2 rStack k1

theorem stepCarry_sound (rle : Rle) (k1 : Nat) (hne : stepCarry rle k1 ≠ .err) :
    StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarry rle k1) := by
  have hp := popCarryLoop_sound 80 rle [] (evalWK k1)
  simp only [evalRStack_nil] at hp
  refine stepCarryValid_of_stepStar hp ?_
  unfold stepCarry at hne ⊢
  dsimp -failIfUnchanged only at hne ⊢
  generalize hpop : popCarryLoop 80 rle [] = p at hne ⊢
  rcases p with ⟨r2, rStack⟩
  dsimp -failIfUnchanged only at hne ⊢
  split
  · rename_i hns
    rw [if_pos hns] at hne
    cases hsl : stepSpecialLoops r2 rStack k1 with
    | some res =>
      rw [hsl] at hne
      exact stepSpecialLoops_sound r2 rStack k1 res hsl hne
    | none =>
      rw [hsl] at hne
      exact stepTurnaround_sound r2 rStack k1 hne
  · rename_i hns
    rw [if_neg hns] at hne
    exact stepTurnaround_sound r2 rStack k1 hne

def runCarry : Nat → Rle → Nat → Bool
  | 0, _, _ => false
  | n + 1, rle, k1 =>
    match stepCarry rle k1 with
    | .halt => true
    | .next rle' k1' => runCarry n rle' k1'
    | .err => false

theorem runCarry_sound : ∀ (n : Nat) (rle : Rle) (k1 : Nat),
    runCarry n rle k1 = true →
    ∃ cfg', ((carryCfg (evalRle rle) (evalWK k1)) [target_tm]⊢* cfg') ∧
      (step target_tm cfg').isNone
  | 0, _, _, h => by nomatch h
  | n + 1, rle, k1, h => by
    unfold runCarry at h
    cases hs : stepCarry rle k1 with
    | halt =>
      have hv := stepCarry_sound rle k1 (by rw [hs]; nofun)
      rwa [hs] at hv
    | next rle' k1' =>
      rw [hs] at h
      have hv := stepCarry_sound rle k1 (by rw [hs]; nofun)
      rw [hs] at hv
      rcases runCarry_sound n rle' k1' h with ⟨cfg', h2, hnone⟩
      exact ⟨cfg', stepStar_trans hv h2, hnone⟩
    | err =>
      rw [hs] at h; nomatch h

def initRle : Rle := pushToksLtr [.U, .M] []

theorem init_to_initRle :
    (init []) [target_tm]⊢* (carryCfg (evalRle initRle) (evalWK 1)) := by
  have h : evalRle initRle = tokL .M +> (tokL .U +> default) := rfl
  rw [h]
  exact ⟨307, init_to_carry0⟩


end Solution

open Solution

-- ============================================================================
-- Section 7: Final Halting Theorem (`holdout_0791_halt`)
-- ============================================================================

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
theorem runCarry_2605 : runCarry 2605 initRle 1 = true := rfl

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
theorem is_halt : IsHalt target_tm := by
  rcases runCarry_sound 2605 initRle 1 runCarry_2605 with ⟨cfg', hstep, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_initRle hstep, hnone⟩

end BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1LF_1RA1RD_0LBHHH
