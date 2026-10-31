/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LDHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LD---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

set_option linter.unusedTactic false
set_option linter.unusedSimpArgs false

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


-- ============================================================================
-- Section 6: Proof of Halting (IsHalt target_tm)
-- ============================================================================

namespace Solution

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

-- ============================================================================
-- Section 6: Four Sound Concrete Steppers (`wstep`, `cstep`, `rcstep`, `bstep`)
-- ============================================================================

abbrev CCfg := Counter.CCfg (Fin 2) (Fin 6)
abbrev wmultiStep := Counter.wmultiStep target_tm
abbrev cmultiStep := Counter.cmultiStep target_tm
abbrev rcmultiStep := Counter.rcmultiStep target_tm
abbrev bmultiStep := Counter.bmultiStep target_tm

-- ============================================================================

-- Section 6.3: Fast Recursor RLE Combinators & Soundness

inductive Tok
  | U | M | W | Z | T | P | PTTTM_TAIL
  deriving DecidableEq, Repr

inductive Mode
  | R0 | R1 | R1_ODD
  deriving DecidableEq, Repr

abbrev Rle := List (List Tok × Nat)

def tokEq (a b : Tok) : Bool :=
  Tok.casesOn a
    (Tok.casesOn b true false false false false false false)
    (Tok.casesOn b false true false false false false false)
    (Tok.casesOn b false false true false false false false)
    (Tok.casesOn b false false false true false false false)
    (Tok.casesOn b false false false false true false false)
    (Tok.casesOn b false false false false false true false)
    (Tok.casesOn b false false false false false false true)

def modeEq (a b : Mode) : Bool :=
  Mode.casesOn a
    (Mode.casesOn b true false false)
    (Mode.casesOn b false true false)
    (Mode.casesOn b false false true)

def wordEq (l1 l2 : List Tok) : Bool :=
  List.rec
    (fun l2 => List.casesOn l2 true (fun _ _ => false))
    (fun a _ ih l2 =>
      List.casesOn l2 false (fun b bs =>
        Bool.casesOn (tokEq a b) false (ih bs)))
    l1 l2

def isZpTok (t : Tok) : Bool :=
  Tok.casesOn t false false false true false true false

def isZpWord (l : List Tok) : Bool :=
  List.rec true (fun t _ ih => Bool.casesOn (isZpTok t) false ih) l

def strictNat {α : Type} (n : Nat) (k : Nat → α) : α :=
  Nat.casesOn (Nat.add n 1) (k 0) (fun m => k m)

def strictTok {α : Type} (t : Tok) (k : Tok → α) : α :=
  Tok.casesOn t (k .U) (k .M) (k .W) (k .Z) (k .T) (k .P) (k .PTTTM_TAIL)

def strictWord {α : Type} (w : List Tok) (k : List Tok → α) : α :=
  List.rec
    (fun k => k [])
    (fun t _ ih k => strictTok t (fun t' => ih (fun ts' => k (t' :: ts'))))
    w k

theorem tokEq_iff (a b : Tok) : tokEq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem modeEq_iff (a b : Mode) : modeEq a b = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem wordEq_iff : ∀ (w1 w2 : List Tok), wordEq w1 w2 = true ↔ w1 = w2
  | [], [] => by decide
  | [], _ :: _ => by simp [wordEq]
  | _ :: _, [] => by simp [wordEq]
  | a :: as, b :: bs => by
    change Bool.casesOn (tokEq a b) false (wordEq as bs) = true ↔ a :: as = b :: bs
    cases h : tokEq a b
    · simp only [Bool.false_eq_true, false_iff, List.cons.injEq, not_and]
      intro hab _
      exact Bool.false_ne_true (h.symm.trans ((tokEq_iff a b).mpr hab))
    · simp [(tokEq_iff a b).mp h, wordEq_iff as bs]

@[simp] theorem strictNat_eq {α : Type} (n : Nat) (k : Nat → α) :
    strictNat n k = k n := rfl

@[simp] theorem strictTok_eq {α : Type} (t : Tok) (k : Tok → α) :
    strictTok t k = k t := by
  cases t <;> rfl

@[simp] theorem strictWord_eq : ∀ {α : Type} (w : List Tok) (k : List Tok → α),
    strictWord w k = k w
  | _, [], _ => rfl
  | _, t :: ts, k => by
    change strictTok t (fun t' => strictWord ts (fun ts' => k (t' :: ts'))) = k (t :: ts)
    rw [strictTok_eq, strictWord_eq ts]

@[simp] lemma isZpWord_nil : isZpWord [] = true := rfl

@[simp] lemma isZpWord_cons (t : Tok) (ts : List Tok) :
    isZpWord (t :: ts) = (isZpTok t && isZpWord ts) := by
  change Bool.casesOn (isZpTok t) false (isZpWord ts) = (isZpTok t && isZpWord ts)
  cases isZpTok t <;> rfl

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
  | nil => simp
  | cons t ts ih => simp [ih, Bool.and_assoc]

@[simp] lemma isZpWord_revWord (w : List Tok) :
    isZpWord (revWord w) = isZpWord w := by
  induction w with
  | nil => rfl
  | cons t ts ih =>
    simp [isZpWord_append, ih, Bool.and_comm]

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

def evalRle : Rle → ListBlank (Fin 2)
  | [] => default
  | (w, c) :: rest => ((wordL w) ^ c) +> evalRle rest

def evalRStack : Rle → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r_end => r_end
  | (w, c) :: rest, r_end => ((wordR (revWord w)) ^ c) +> evalRStack rest r_end

@[simp] lemma evalRle_nil : evalRle [] = default := rfl
@[simp] lemma evalRle_cons (w : List Tok) (c : Nat) (rest : Rle) :
    evalRle ((w, c) :: rest) = ((wordL w) ^ c) +> evalRle rest := rfl

@[simp] lemma evalRStack_nil (r_end : ListBlank (Fin 2)) : evalRStack [] r_end = r_end := rfl
@[simp] lemma evalRStack_cons (w : List Tok) (c : Nat) (rest : Rle) (r_end : ListBlank (Fin 2)) :
    evalRStack ((w, c) :: rest) r_end = ((wordR (revWord w)) ^ c) +> evalRStack rest r_end := rfl

def pushRlePosK {α : Type} (w : List Tok) (c : Nat) (rle : Rle) (k : Rle → α) : α :=
  List.casesOn rle (k [(w, c)]) (fun p rest =>
    Prod.casesOn p (fun w' c' =>
      Bool.casesOn (wordEq w w')
        (k ((w, c) :: (w', c') :: rest))
        (strictNat (Nat.add c c') fun s => k ((w, s) :: rest))))

def pushRleK {α : Type} (w : List Tok) (c : Nat) (rle : Rle) (k : Rle → α) : α :=
  Bool.casesOn (Nat.beq c 0)
    (pushRlePosK w c rle k)
    (k rle)

def pushRlePos (w : List Tok) (c : Nat) (rle : Rle) : Rle :=
  pushRlePosK w c rle (fun r => r)

def pushRle (w : List Tok) (c : Nat) (rle : Rle) : Rle :=
  pushRleK w c rle (fun r => r)

@[simp] theorem pushRlePosK_eq {α : Type} (w : List Tok) (c : Nat) (rle : Rle) (k : Rle → α) :
    pushRlePosK w c rle k = k (pushRlePos w c rle) := by
  cases rle with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨w', c'⟩
    unfold pushRlePos; unfold pushRlePosK; dsimp -failIfUnchanged only
    cases wordEq w w' <;> rfl

@[simp] theorem pushRleK_eq {α : Type} (w : List Tok) (c : Nat) (rle : Rle) (k : Rle → α) :
    pushRleK w c rle k = k (pushRle w c rle) := by
  unfold pushRle; unfold pushRleK
  cases Nat.beq c 0
  · exact pushRlePosK_eq w c rle k
  · rfl

@[simp] theorem evalRle_pushRlePos (w : List Tok) (c : Nat) (rle : Rle) :
    evalRle (pushRlePos w c rle) = ((wordL w) ^ c) +> evalRle rle := by
  cases rle with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨w', c'⟩
    unfold pushRlePos; unfold pushRlePosK; dsimp -failIfUnchanged only
    cases hw : wordEq w w'
    · rfl
    · rw [(wordEq_iff w w').mp hw]
      change ((wordL w') ^ (c + c')) +> evalRle rest = ((wordL w') ^ c) +> (((wordL w') ^ c') +> evalRle rest)
      rw [list_pow_add, listblank_append_assoc]

@[simp] theorem evalRle_pushRle (w : List Tok) (c : Nat) (rle : Rle) :
    evalRle (pushRle w c rle) = ((wordL w) ^ c) +> evalRle rle := by
  unfold pushRle; unfold pushRleK
  cases hc : Nat.beq c 0
  · exact evalRle_pushRlePos w c rle
  · rw [Nat.beq_eq.mp hc]; simp

@[simp] theorem evalRStack_pushRlePos (w : List Tok) (c : Nat) (rs : Rle) (r_end : ListBlank (Fin 2)) :
    evalRStack (pushRlePos w c rs) r_end = ((wordR (revWord w)) ^ c) +> evalRStack rs r_end := by
  cases rs with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨w', c'⟩
    unfold pushRlePos; unfold pushRlePosK; dsimp -failIfUnchanged only
    cases hw : wordEq w w'
    · rfl
    · rw [(wordEq_iff w w').mp hw]
      change ((wordR (revWord w')) ^ (c + c')) +> evalRStack rest r_end =
        ((wordR (revWord w')) ^ c) +> (((wordR (revWord w')) ^ c') +> evalRStack rest r_end)
      rw [list_pow_add, listblank_append_assoc]

@[simp] theorem evalRStack_pushRle (w : List Tok) (c : Nat) (rs : Rle) (r_end : ListBlank (Fin 2)) :
    evalRStack (pushRle w c rs) r_end = ((wordR (revWord w)) ^ c) +> evalRStack rs r_end := by
  unfold pushRle; unfold pushRleK
  cases hc : Nat.beq c 0
  · exact evalRStack_pushRlePos w c rs r_end
  · rw [Nat.beq_eq.mp hc]; simp

def pushToksLtr (ts : List Tok) (rle : Rle) : Rle :=
  List.rec
    (fun rle => rle)
    (fun t _ ih rle => pushRlePosK [t] 1 rle (fun rle' => ih rle'))
    ts rle

@[simp] lemma pushToksLtr_nil (rle : Rle) : pushToksLtr [] rle = rle := rfl
@[simp] lemma pushToksLtr_cons (t : Tok) (ts : List Tok) (rle : Rle) :
    pushToksLtr (t :: ts) rle = pushToksLtr ts (pushRlePos [t] 1 rle) := by
  change pushRlePosK [t] 1 rle (fun rle' => pushToksLtr ts rle') = pushToksLtr ts (pushRlePos [t] 1 rle)
  rw [pushRlePosK_eq]

@[simp] theorem evalRle_pushToksLtr : ∀ (ts : List Tok) (rle : Rle),
    evalRle (pushToksLtr ts rle) = wordL (revWord ts) +> evalRle rle
  | [], rle => rfl
  | t :: ts, rle => by
    simp [pushToksLtr_cons, evalRle_pushToksLtr ts, wordL_append, pow_succ_list, pow_zero_list, listblank_append_assoc]

def popLastTok (rle : Rle) : Option (Tok × Rle) :=
  List.casesOn rle none (fun p rest =>
    Prod.casesOn p (fun w c =>
      List.casesOn w none (fun t ts =>
        List.casesOn ts
          (Bool.casesOn (Nat.beq c 1)
            (Bool.casesOn (Nat.beq c 0)
              (strictNat (Nat.sub c 1) fun cm1 => some (t, ([t], cm1) :: rest))
              none)
            (some (t, rest)))
          (fun t2 ts2 =>
            Bool.casesOn (Nat.beq c 1)
              (Bool.casesOn (Nat.beq c 0)
                (strictNat (Nat.sub c 1) fun cm1 =>
                  pushRlePosK (t2 :: ts2) 1 ((t :: t2 :: ts2, cm1) :: rest) fun rOut => some (t, rOut))
                none)
              (pushRlePosK (t2 :: ts2) 1 rest fun rOut => some (t, rOut))))))

theorem popLastTok_sound (rle : Rle) (t : Tok) (rle' : Rle)
    (h : popLastTok rle = some (t, rle')) :
    evalRle rle = tokL t +> evalRle rle' := by
  cases rle with
  | nil => nomatch h
  | cons p rest =>
    rcases p with ⟨w, c⟩
    cases w with
    | nil => nomatch h
    | cons t0 ts =>
      cases c with
      | zero => cases ts <;> nomatch h
      | succ c' =>
        cases ts with
        | nil =>
          cases c' with
          | zero =>
            change some (t0, rest) = some (t, rle') at h
            injection h with h'; injection h' with ht hr; subst ht hr
            simp [pow_succ_list, pow_zero_list]
          | succ c'' =>
            change some (t0, ([t0], c'' + 1) :: rest) = some (t, rle') at h
            injection h with h'; injection h' with ht hr; subst ht hr
            simp [pow_succ_list]
        | cons t2 ts2 =>
          cases c' with
          | zero =>
            change pushRlePosK (t2 :: ts2) 1 rest (fun rOut => some (t0, rOut)) = some (t, rle') at h
            rw [pushRlePosK_eq] at h
            injection h with h'; injection h' with ht hr; subst ht hr
            simp [pow_succ_list, pow_zero_list]
          | succ c'' =>
            change pushRlePosK (t2 :: ts2) 1 ((t0 :: t2 :: ts2, c'' + 1) :: rest) (fun rOut => some (t0, rOut)) = some (t, rle') at h
            rw [pushRlePosK_eq] at h
            injection h with h'; injection h' with ht hr; subst ht hr
            simp [pow_succ_list]

def popTok (t_exp : Tok) (rle : Rle) : Option Rle :=
  Option.casesOn (popLastTok rle) none (fun p =>
    Prod.casesOn p (fun t rle' =>
      Bool.casesOn (tokEq t t_exp) none (some rle')))

theorem popTok_sound (t_exp : Tok) (rle rle' : Rle) (h : popTok t_exp rle = some rle') :
    evalRle rle = tokL t_exp +> evalRle rle' := by
  unfold popTok at h
  cases hp : popLastTok rle with
  | none => rw [hp] at h; nomatch h
  | some p =>
    rcases p with ⟨t, r⟩
    rw [hp] at h; dsimp -failIfUnchanged only at h
    cases ht : tokEq t t_exp
    · rw [ht] at h; nomatch h
    · rw [ht] at h; injection h with hr; subst hr
      rw [← (tokEq_iff t t_exp).mp ht]
      exact popLastTok_sound rle t r hp

def popToks (ts : List Tok) (rle : Rle) : Option Rle :=
  List.rec
    (fun rle => some rle)
    (fun t _ ih rle =>
      Option.casesOn (popTok t rle) none (fun rle' => ih rle'))
    ts rle

theorem popToks_sound : ∀ (ts : List Tok) (rle rle' : Rle),
    popToks ts rle = some rle' →
    evalRle rle = wordL ts +> evalRle rle'
  | [], rle, rle', h => by
    injection h with hr; subst hr; rfl
  | t :: ts, rle, rle', h => by
    change Option.casesOn (popTok t rle) none (fun r1 => popToks ts r1) = some rle' at h
    cases h1 : popTok t rle with
    | none => rw [h1] at h; nomatch h
    | some r1 =>
      rw [h1] at h; dsimp -failIfUnchanged only at h
      rw [popTok_sound t rle r1 h1, popToks_sound ts r1 rle' h, wordL_cons, listblank_append_assoc]

def popTokCount (fuel : Nat) (t_exp : Tok) (acc : Nat) (rle : Rle) : Nat × Rle :=
  Nat.rec
    (fun acc rle => (acc, rle))
    (fun _ ih acc rle =>
      List.casesOn rle (acc, []) (fun p rest =>
        Prod.casesOn p (fun w c =>
          List.casesOn w (acc, ([], c) :: rest) (fun t ts =>
            Bool.casesOn (tokEq t t_exp)
              (acc, (t :: ts, c) :: rest)
              (Bool.casesOn (Nat.beq c 0)
                (List.casesOn ts
                  (strictNat (Nat.add acc c) fun acc' => ih acc' rest)
                  (fun t2 ts2 =>
                    strictNat (Nat.add acc 1) fun acc' =>
                    Bool.casesOn (Nat.beq c 1)
                      (strictNat (Nat.sub c 1) fun cm1 =>
                        pushRlePosK (t2 :: ts2) 1 ((t :: t2 :: ts2, cm1) :: rest) fun rOut =>
                        ih acc' rOut)
                      (pushRlePosK (t2 :: ts2) 1 rest fun rOut =>
                        ih acc' rOut)))
                (acc, (t :: ts, c) :: rest))))))
    fuel acc rle

theorem popTokCount_succ_cons (fuel : Nat) (t_exp : Tok) (acc : Nat) (t : Tok) (ts : List Tok) (c : Nat) (rest : Rle) :
    popTokCount (fuel + 1) t_exp acc ((t :: ts, c) :: rest) =
      if tokEq t t_exp then
        if c == 0 then (acc, (t :: ts, c) :: rest)
        else match ts with
          | [] => popTokCount fuel t_exp (acc + c) rest
          | t2 :: ts2 =>
            if c == 1 then popTokCount fuel t_exp (acc + 1) (pushRlePos (t2 :: ts2) 1 rest)
            else popTokCount fuel t_exp (acc + 1) (pushRlePos (t2 :: ts2) 1 ((t :: t2 :: ts2, c - 1) :: rest))
      else (acc, (t :: ts, c) :: rest) := by
  unfold popTokCount; dsimp -failIfUnchanged only
  cases tokEq t t_exp
  · rfl
  · cases c with
    | zero => rfl
    | succ c' =>
      cases ts with
      | nil => rfl
      | cons t2 ts2 =>
        cases c' <;> simp only [strictNat_eq, pushRlePosK_eq] <;> rfl

theorem popTokCount_sound : ∀ (fuel : Nat) (t_exp : Tok) (acc : Nat) (rle : Rle),
    acc ≤ (popTokCount fuel t_exp acc rle).1 ∧
    ((tokL t_exp) ^ acc) +> evalRle rle =
      ((tokL t_exp) ^ (popTokCount fuel t_exp acc rle).1) +> evalRle (popTokCount fuel t_exp acc rle).2
  | 0, _, acc, _ => ⟨Nat.le_refl acc, rfl⟩
  | fuel + 1, t_exp, acc, [] => ⟨Nat.le_refl acc, rfl⟩
  | fuel + 1, t_exp, acc, ([], c) :: rest => ⟨Nat.le_refl acc, rfl⟩
  | fuel + 1, t_exp, acc, (t :: ts, c) :: rest => by
    rw [popTokCount_succ_cons]
    cases ht : tokEq t t_exp
    · simp
    · simp only [↓reduceIte]
      rw [(tokEq_iff t t_exp).mp ht]
      cases c with
      | zero => simp
      | succ c' =>
        have hc0 : (c' + 1 == 0) = false := rfl
        rw [hc0]; simp only [Bool.false_eq_true, ↓reduceIte]
        cases ts with
        | nil =>
          rcases popTokCount_sound fuel t_exp (acc + (c' + 1)) rest with ⟨hle, heq⟩
          refine ⟨Nat.le_trans (Nat.le_add_right acc (c' + 1)) hle, ?_⟩
          rw [← heq]
          change ((tokL t_exp) ^ acc) +> (((wordL [t_exp]) ^ (c' + 1)) +> evalRle rest) =
            ((tokL t_exp) ^ (acc + (c' + 1))) +> evalRle rest
          have hw : wordL [t_exp] = tokL t_exp := List.append_nil _
          rw [hw, ← listblank_append_assoc, ← list_pow_add]
        | cons t2 ts2 =>
          cases c' with
          | zero =>
            simp only [beq_self_eq_true, ↓reduceIte]
            rcases popTokCount_sound fuel t_exp (acc + 1) (pushRlePos (t2 :: ts2) 1 rest) with ⟨hle, heq⟩
            refine ⟨Nat.le_trans (Nat.le_add_right acc 1) hle, ?_⟩
            rw [← heq, pow_succ_right (tokL t_exp) acc]
            simp [pow_succ_list, pow_zero_list, listblank_append_assoc]
          | succ c'' =>
            have hc1 : (c'' + 1 + 1 == 1) = false := rfl
            rw [hc1]; simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_sub_cancel]
            rcases popTokCount_sound fuel t_exp (acc + 1)
              (pushRlePos (t2 :: ts2) 1 ((t_exp :: t2 :: ts2, c'' + 1) :: rest)) with ⟨hle, heq⟩
            refine ⟨Nat.le_trans (Nat.le_add_right acc 1) hle, ?_⟩
            rw [← heq, pow_succ_right (tokL t_exp) acc]
            simp [pow_succ_list, pow_zero_list, listblank_append_assoc]


-- ============================================================================
-- Section 6.4: Named Configurations & 65 Verified Micro-Step Lemmas
-- ============================================================================

def evalWK (k1 : Nat) : ListBlank (Fin 2) :=
  [1, 0, 1, 1] +> ((([0, 0, 1, 1] : List (Fin 2)) ^ k1) +> default)

def cfgR (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, [1, 1] +> l, default⟩⟩

def carryCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨1, l, [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩

def r0Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1OddShortCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨1, [1, 1, 0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def r1OddCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  r1OddShortCfg (tokL .Z +> l) r

def wSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨1, l, [1] +> r⟩⟩

def dSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨1, [0, 1, 1] +> l, r⟩⟩

def tSweepCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, [0, 0, 0, 0, 1, 1] +> l, r⟩⟩

def t3Cfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨1, l, [0, 1, 0, 0, 1] +> r⟩⟩

def pmuCfg (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨1, l, [1, 0, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩

def initRle : Rle :=
  pushToksLtr [.U, .M, .Z, .Z, .P, .T, .M, .Z, .Z] []

theorem init_to_carry0 :
    (init []) [target_tm]⊢^{2049} (carryCfg (evalRle initRle) (evalWK 1)) :=
  bmultiStep_sound 2049 ⟨A, 0, [], []⟩
    ⟨D, 1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl

theorem carry_Z (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .Z +> l) r) [target_tm]⊢^{62} (carryCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 62 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_P (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .P +> l) r) [target_tm]⊢^{22} (carryCfg l (tokR .P +> r)) :=
  wmultiStep_sound 22 ⟨D, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .P +> l))))) r) [target_tm]⊢^{90} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 90 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (((tokL .T) ^ 2) +> (tokL .P +> l))) r) [target_tm]⊢^{134} (carryCfg l (((tokR .Z) ^ 3) +> r)) :=
  wmultiStep_sound 134 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTT (l r : ListBlank (Fin 2)) :
    (carryCfg (((tokL .T) ^ 3) +> (tokL .P +> l)) r) [target_tm]⊢^{94} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 94 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (((tokL .T) ^ 3) +> (tokL .P +> l))) r) [target_tm]⊢^{111} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .PTTTM_TAIL +> r))) :=
  wmultiStep_sound 111 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem turn_UM (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .U +> default)) r) [target_tm]⊢^{67} (r1Cfg (tokL .M +> (tokL .U +> default)) r) :=
  cmultiStep_sound 67 ⟨D, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_UMT (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .M +> (tokL .U +> default))) r) [target_tm]⊢^{105} (r1Cfg (tokL .Z +> (tokL .U +> default)) r) :=
  cmultiStep_sound 105 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_ZT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{67} (r1Cfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 67 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_WM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .W +> l)) r) [target_tm]⊢^{59} (r1Cfg (tokL .T +> l) r) :=
  wmultiStep_sound 59 ⟨D, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .P +> l)) r) [target_tm]⊢^{125} (r0Cfg (tokL .P +> (tokL .T +> l)) r) :=
  wmultiStep_sound 125 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .Z +> l)) r) [target_tm]⊢^{59} (r1Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 59 ⟨D, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{151} (r1OddCfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 151 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_PTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{105} (r1Cfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 105 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{109} (r1Cfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 109 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .Z +> l))) r) [target_tm]⊢^{121} (r1OddCfg (tokL .T +> (tokL .T +> l)) r) :=
  wmultiStep_sound 121 ⟨D, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{133} (r0Cfg (tokL .P +> (tokL .M +> (tokL .T +> l))) r) :=
  wmultiStep_sound 133 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{137} (r0Cfg (tokL .P +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 137 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{137} (r0Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 137 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_MUTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .U +> (tokL .M +> l)))) r) [target_tm]⊢^{151} (r1OddCfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 151 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .P +> l)))) r) [target_tm]⊢^{175} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .U +> (tokL .M +> l)))) r) :=
  wmultiStep_sound 175 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{175} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 175 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{117} (r1Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 117 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZPMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .P +> (tokL .Z +> l)))) r) [target_tm]⊢^{177} (r0Cfg (tokL .P +> (tokL .M +> (tokL .W +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 177 ⟨D, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .Z +> l))))) r) [target_tm]⊢^{171} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 171 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .T +> (tokL .P +> l))))) r) [target_tm]⊢^{221} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .Z +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 221 ⟨D, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem carry_MU_to_pmuCfg (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> l)) r) [target_tm]⊢^{19} (pmuCfg l (tokR .P +> r)) :=
  wmultiStep_sound 19 ⟨D, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmu_step (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .P +> l) r) [target_tm]⊢^{66} (pmuCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 66 ⟨A, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmuCfg_Z_turn (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{40} (r0Cfg (tokL .M +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 40 ⟨A, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem pmuCfg_M_to_carry (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .M +> l) r) [target_tm]⊢^{7} (carryCfg (tokL .U +> l) r) :=
  wmultiStep_sound 7 ⟨A, 1, [0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmuCfg_T_to_carry (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .T +> l) r) [target_tm]⊢^{7} (carryCfg (tokL .M +> l) r) :=
  wmultiStep_sound 7 ⟨A, 1, [0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{30} (carryCfg (tokL .Z +> l) (tokR .P +> r)) :=
  wmultiStep_sound 30 ⟨D, 1, [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem turn_PTMT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .M +> (tokL .T +> (tokL .P +> l)))) r) [target_tm]⊢^{175} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .U +> (tokL .M +> l)))) r) :=
  wmultiStep_sound 175 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{175} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 175 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .T +> (tokL .Z +> l))))) r) [target_tm]⊢^{155} (r1Cfg (tokL .Z +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 155 ⟨D, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTU_halt (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{34} (⟨some F, ⟨1, [1, 0, 1, 1, 0, 1, 1, 1] +> l, [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩) :=
  wmultiStep_sound 34 ⟨D, 1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 1, [1, 0, 1, 1, 0, 1, 1, 1], [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem r0_Z (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r0Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r0_P (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .P +> r)) [target_tm]⊢^{52} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 52 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
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
    (r1Cfg l (tokR .P +> r)) [target_tm]⊢^{74} (r1OddCfg (tokL .P +> l) r) :=
  wmultiStep_sound 74 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem r1OddShort_Z (l r : ListBlank (Fin 2)) :
    (r1OddShortCfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r1OddShortCfg (tokL .Z +> l) r) :=
  wmultiStep_sound 12 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r1Odd_P (l r : ListBlank (Fin 2)) :
    (r1OddCfg l (tokR .P +> r)) [target_tm]⊢^{10} (r1Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 10 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_start (l : ListBlank (Fin 2)) :
    (cfgR l) [target_tm]⊢^{2} (wSweepCfg l default) :=
  rcmultiStep_sound 2 ⟨D, 0, [1, 1], []⟩
    ⟨A, 1, [], [1]⟩ l rfl

theorem wSweep_step (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .W +> l) r) [target_tm]⊢^{6} (wSweepCfg l ([0, 0, 1, 1] +> r)) :=
  wmultiStep_sound 6 ⟨A, 1, [0, 0, 1, 1], [1]⟩
    ⟨A, 1, [], [1, 0, 0, 1, 1]⟩ l r rfl

theorem dSweep_step (l r : ListBlank (Fin 2)) :
    (dSweepCfg l ([0, 0, 1, 1] +> r)) [target_tm]⊢^{6} (dSweepCfg (tokL .W +> l) r) :=
  wmultiStep_sound 6 ⟨E, 1, [0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem dSweep_end (l : ListBlank (Fin 2)) :
    (dSweepCfg l default) [target_tm]⊢^{5} (cfgR (tokL .W +> l)) :=
  rcmultiStep_sound 5 ⟨E, 1, [0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 1, 1], []⟩ l rfl

theorem tSweep_step (l r : ListBlank (Fin 2)) :
    (tSweepCfg l ([0, 0, 1, 1] +> r)) [target_tm]⊢^{26} (tSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 26 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem tSweep_end (l : ListBlank (Fin 2)) :
    (tSweepCfg l default) [target_tm]⊢^{2} (cfgR (tokL .Z +> l)) :=
  rcmultiStep_sound 2 ⟨E, 0, [0, 0, 0, 0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩ l rfl

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
  wmultiStep_sound 10 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_Z_to_dSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .Z +> l) r) [target_tm]⊢^{13} (dSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 13 ⟨A, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem wSweep_ZT_to_dSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .Z +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{57} (dSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 57 ⟨A, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_PT_to_carry (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .P +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{46} (carryCfg l ([1, 0, 1, 1] +> r)) :=
  wmultiStep_sound 46 ⟨A, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl

theorem wSweep_ZMT_to_tSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .M +> (tokL .Z +> l))) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{83} (tSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 83 ⟨A, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem cfgR_Z_to_TW (l : ListBlank (Fin 2)) :
    (cfgR (tokL .Z +> l)) [target_tm]⊢^{20} (cfgR (tokL .W +> (tokL .T +> l))) :=
  rcmultiStep_sound 20 ⟨D, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨D, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl

theorem cfgR_TW_to_t3Cfg (l : ListBlank (Fin 2)) :
    (cfgR (tokL .W +> (tokL .T +> l))) [target_tm]⊢^{32} (t3Cfg l (evalWK 0)) :=
  rcmultiStep_sound 32 ⟨D, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl

theorem t3_step (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 3) +> l) r) [target_tm]⊢^{72} (t3Cfg l (((tokR .Z) ^ 2) +> r)) :=
  wmultiStep_sound 72 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem t3Cfg_Z_zero_to_carry (l : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (evalWK 0)) [target_tm]⊢^{130} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 130 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_Z_succ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{39} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 39 ⟨D, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem t3Cfg_TZ_to_r1OddShort (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{57} (r1OddShortCfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 57 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem r1OddShortCfg_evalWK0_to_carry (l : ListBlank (Fin 2)) :
    (r1OddShortCfg l (evalWK 0)) [target_tm]⊢^{194} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 194 ⟨D, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨D, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_TTZ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 2) +> (tokL .Z +> l)) r) [target_tm]⊢^{85} (r0Cfg (tokL .W +> (tokL .T +> l)) r) :=
  wmultiStep_sound 85 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
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
    refine stepStar_trans ⟨_, wSweep_step (((tokL .W) ^ n) +> l) r⟩ ?_
    have ih := wSweep_loop n l ([0, 0, 1, 1] +> r)
    rwa [pow_succ_right, listblank_append_assoc]

theorem dSweep_loop : ∀ (n : Nat) (l r : ListBlank (Fin 2)),
    (dSweepCfg l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)) [target_tm]⊢*
      (dSweepCfg (((tokL .W) ^ n) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | n + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, dSweep_step l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)⟩ ?_
    have ih := dSweep_loop n (tokL .W +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem tSweep_loop : ∀ (n : Nat) (l r : ListBlank (Fin 2)),
    (tSweepCfg l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)) [target_tm]⊢*
      (tSweepCfg (((tokL .T) ^ n) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | n + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, tSweep_step l ((([0, 0, 1, 1] : List (Fin 2)) ^ n) +> r)⟩ ?_
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
    refine stepStar_trans ⟨_, t3_step (((tokL .T) ^ (3 * q)) +> l) r⟩ ?_
    have ih := t3_loop q l (((tokR .Z) ^ 2) +> r)
    rwa [h2, list_pow_add, listblank_append_assoc]

theorem pmu_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (pmuCfg (((tokL .P) ^ m) +> l) r) [target_tm]⊢*
      (pmuCfg l (((tokR .Z) ^ m) +> r))
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, pmu_step (((tokL .P) ^ m) +> l) r⟩ ?_
    have ih := pmu_loop m l (tokR .Z +> r)
    rwa [pow_succ_right, listblank_append_assoc]

theorem r0_Z_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r0Cfg l (((tokR .Z) ^ m) +> r)) [target_tm]⊢*
      (r0Cfg (((tokL .Z) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, r0_Z l (((tokR .Z) ^ m) +> r)⟩ ?_
    have ih := r0_Z_loop m (tokL .Z +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem r0_P_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r0Cfg l (((tokR .P) ^ m) +> r)) [target_tm]⊢*
      (r0Cfg (((tokL .P) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, r0_P l (((tokR .P) ^ m) +> r)⟩ ?_
    have ih := r0_P_loop m (tokL .P +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem r1OddShort_Z_loop : ∀ (m : Nat) (l r : ListBlank (Fin 2)),
    (r1OddShortCfg l (((tokR .Z) ^ m) +> r)) [target_tm]⊢*
      (r1OddShortCfg (((tokL .Z) ^ m) +> l) r)
  | 0, l, r => stepStar_refl _ _
  | m + 1, l, r => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans ⟨_, r1OddShort_Z l (((tokR .Z) ^ m) +> r)⟩ ?_
    have ih := r1OddShort_Z_loop m (tokL .Z +> l) r
    rwa [pow_succ_right, listblank_append_assoc]

theorem cfgR_ZW_to_TW (n : Nat) (l : ListBlank (Fin 2)) :
    (cfgR (((tokL .W) ^ n) +> (tokL .Z +> l))) [target_tm]⊢*
      (cfgR (((tokL .W) ^ (n + 1)) +> (tokL .T +> l))) := by
  refine stepStar_trans ⟨_, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop n (tokL .Z +> l) default) ?_
  refine stepStar_trans ⟨_, wSweep_Z_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop n (tokL .T +> l) default) ?_
  rw [pow_succ_list, listblank_append_assoc]
  exact ⟨_, dSweep_end _⟩

theorem r0_end (k1 : Nat) (l : ListBlank (Fin 2)) :
    (r0Cfg l (evalWK k1)) [target_tm]⊢* (carryCfg l (evalWK (k1 + 2))) := by
  unfold evalWK
  refine stepStar_trans ⟨_, r0_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop k1 (tokL .Z +> (tokL .Z +> l)) default) ?_
  refine stepStar_trans ⟨_, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (k1 + 1) (tokL .Z +> l)) ?_
  refine stepStar_trans ⟨_, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (k1 + 2) (tokL .T +> (tokL .Z +> l)) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (k1 + 1), listblank_append_assoc]
  refine stepStar_trans ⟨_, wSweep_ZT_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop (k1 + 1) (tokL .Z +> (tokL .P +> l)) default) ?_
  refine stepStar_trans ⟨_, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (k1 + 2) (tokL .P +> l)) ?_
  refine stepStar_trans ⟨_, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (k1 + 3) (tokL .T +> (tokL .P +> l)) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (k1 + 2), listblank_append_assoc]
  exact ⟨_, wSweep_PT_to_carry l _⟩

theorem r1_end (kf1 : Nat) (l : ListBlank (Fin 2)) :
    (r1Cfg l (evalWK kf1)) [target_tm]⊢*
      (t3Cfg (((tokL .T) ^ (kf1 + 1)) +> (tokL .Z +> (tokL .P +> l))) (evalWK 0)) := by
  unfold evalWK
  refine stepStar_trans ⟨_, r1_to_dSweep l _⟩ ?_
  refine stepStar_trans (dSweep_loop kf1 (tokL .Z +> (tokL .M +> (tokL .Z +> l))) default) ?_
  refine stepStar_trans ⟨_, dSweep_end _⟩ ?_
  rw [← listblank_append_assoc, ← pow_succ_list]
  refine stepStar_trans (cfgR_ZW_to_TW (kf1 + 1) (tokL .M +> (tokL .Z +> l))) ?_
  refine stepStar_trans ⟨_, wSweep_start _⟩ ?_
  refine stepStar_trans (wSweep_loop (kf1 + 2) (tokL .T +> (tokL .M +> (tokL .Z +> l))) default) ?_
  rw [pow_succ_list [0, 0, 1, 1] (kf1 + 1), listblank_append_assoc]
  refine stepStar_trans ⟨_, wSweep_ZMT_to_tSweep l _⟩ ?_
  refine stepStar_trans (tSweep_loop (kf1 + 1) (tokL .Z +> (tokL .P +> l)) default) ?_
  refine stepStar_trans ⟨_, tSweep_end _⟩ ?_
  refine stepStar_trans ⟨_, cfgR_Z_to_TW _⟩ ?_
  exact ⟨_, cfgR_TW_to_t3Cfg _⟩

theorem r1Odd_end (kf1 : Nat) (l : ListBlank (Fin 2)) :
    (r1OddCfg l (evalWK kf1)) [target_tm]⊢*
      (t3Cfg (((tokL .T) ^ kf1) +> (tokL .Z +> (tokL .Z +> l))) (evalWK 0)) := by
  unfold evalWK
  refine stepStar_trans ⟨_, r1Odd_to_tSweep l _⟩ ?_
  refine stepStar_trans (tSweep_loop kf1 (tokL .Z +> (tokL .Z +> l)) default) ?_
  refine stepStar_trans ⟨_, tSweep_end _⟩ ?_
  refine stepStar_trans ⟨_, cfgR_Z_to_TW _⟩ ?_
  exact ⟨_, cfgR_TW_to_t3Cfg _⟩

def stepZtToCarry (rle2 : Rle) (n : Nat) : Rle × Nat :=
  strictNat (Nat.div n 3) fun q =>
  strictNat (Nat.mod n 3) fun rem =>
  Bool.casesOn (Nat.beq rem 0)
    (Bool.casesOn (Nat.beq rem 1)
      (strictNat (Nat.mul 2 q) fun zc =>
        pushRleK [.Z] zc (pushToksLtr [.T, .W] rle2) fun rle4 =>
        (rle4, 2))
      (strictNat (Nat.mul 2 q) fun zc =>
        pushRleK [.Z] zc (pushToksLtr [.T, .M] rle2) fun rle4 =>
        (rle4, 1)))
    (Bool.casesOn (Nat.beq q 0)
      (strictNat (Nat.sub (Nat.mul 2 q) 1) fun zc =>
        pushRlePosK [.P] 1 rle2 fun rle3 =>
        pushRleK [.Z] zc rle3 fun rle4 =>
        (rle4, 2))
      (rle2, 1))

@[simp] lemma nat_mod_eq (a b : Nat) : Nat.mod a b = a % b := rfl
@[simp] lemma nat_div_eq (a b : Nat) : Nat.div a b = a / b := rfl
@[simp] lemma nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[simp] lemma nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[simp] lemma nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl

theorem stepZtToCarry_eq (rle2 : Rle) (n : Nat) :
    stepZtToCarry rle2 n =
      let q := n / 3
      let rem := n % 3
      if Nat.beq rem 0 then
        if Nat.beq q 0 then (rle2, 1)
        else (pushRle [.Z] (2 * q - 1) (pushRlePos [.P] 1 rle2), 2)
      else if Nat.beq rem 1 then
        (pushRle [.Z] (2 * q) (pushToksLtr [.T, .M] rle2), 1)
      else
        (pushRle [.Z] (2 * q) (pushToksLtr [.T, .W] rle2), 2) := by
  unfold stepZtToCarry; dsimp -failIfUnchanged only
  simp only [strictNat_eq, pushRlePosK_eq, pushRleK_eq, nat_mod_eq, nat_div_eq, nat_mul_eq, nat_sub_eq]
  cases Nat.beq (n % 3) 0
  · cases Nat.beq (n % 3) 1 <;> rfl
  · cases Nat.beq (n / 3) 0 <;> rfl

theorem stepZtToCarry_sound (rle2 : Rle) (n : Nat) :
    (t3Cfg (((tokL .T) ^ n) +> (tokL .Z +> evalRle rle2)) (evalWK 0)) [target_tm]⊢*
      (carryCfg (evalRle (stepZtToCarry rle2 n).1) (evalWK (stepZtToCarry rle2 n).2)) := by
  rw [stepZtToCarry_eq]
  dsimp -failIfUnchanged only
  generalize hq : n / 3 = q
  generalize hrem : n % 3 = rem
  have hdiv : n = 3 * q + rem := by omega
  have hlt : rem < 3 := by omega
  rw [hdiv, list_pow_add, listblank_append_assoc]
  refine stepStar_trans (t3_loop q (((tokL .T) ^ rem) +> (tokL .Z +> evalRle rle2)) (evalWK 0)) ?_
  rcases (by omega : rem = 0 ∨ rem = 1 ∨ rem = 2) with rfl | rfl | rfl
  · have hr0 : Nat.beq 0 0 = true := rfl
    rw [hr0]
    simp only [↓reduceIte, pow_zero_list, listblank_append_nil]
    cases q with
    | zero =>
      rw [hr0]
      simp only [↓reduceIte, Nat.mul_zero, pow_zero_list, listblank_append_nil]
      exact ⟨_, t3Cfg_Z_zero_to_carry (evalRle rle2)⟩
    | succ q' =>
      have hq_ne : Nat.beq (q' + 1) 0 = false := rfl
      have h2q : 2 * (q' + 1) = 1 + (2 * (q' + 1) - 1) := by omega
      have h2q_sub : 1 + (2 * (q' + 1) - 1) - 1 = 2 * (q' + 1) - 1 := by omega
      rw [hq_ne, h2q, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil, listblank_append_assoc]
      simp only [Bool.false_eq_true, ↓reduceIte, evalRle_pushRle, evalRle_pushRlePos, pow_succ_list, pow_zero_list,
        List.append_nil, wordL_cons, wordL_nil, h2q_sub]
      refine stepStar_trans ⟨_, t3Cfg_Z_succ_to_r0 (evalRle rle2) _⟩ ?_
      refine stepStar_trans (r0_Z_loop (2 * (q' + 1) - 1) (tokL .P +> evalRle rle2) (evalWK 0)) ?_
      exact r0_end 0 _
  · have hr0 : Nat.beq 1 0 = false := rfl
    have hr1 : Nat.beq 1 1 = true := rfl
    rw [hr0, hr1]
    simp only [Bool.false_eq_true, ↓reduceIte, pow_succ_list, pow_zero_list,
      List.append_nil, evalRle_pushRle, evalRle_pushToksLtr, revWord_cons, revWord_nil,
      wordL_cons, wordL_nil]
    refine stepStar_trans ⟨_, t3Cfg_TZ_to_r1OddShort (evalRle rle2) _⟩ ?_
    refine stepStar_trans (r1OddShort_Z_loop (2 * q) (tokL .M +> (tokL .T +> evalRle rle2)) (evalWK 0)) ?_
    exact ⟨_, r1OddShortCfg_evalWK0_to_carry _⟩
  · have hr0 : Nat.beq 2 0 = false := rfl
    have hr1 : Nat.beq 2 1 = false := rfl
    rw [hr0, hr1]
    simp only [Bool.false_eq_true, ↓reduceIte, evalRle_pushRle, evalRle_pushToksLtr, revWord_cons,
      revWord_nil, pow_succ_list, pow_zero_list, List.append_nil, wordL_cons, wordL_nil, listblank_append_assoc]
    refine stepStar_trans ⟨_, t3Cfg_TTZ_to_r0 (evalRle rle2) _⟩ ?_
    refine stepStar_trans (r0_Z_loop (2 * q) (tokL .W +> (tokL .T +> evalRle rle2)) (evalWK 0)) ?_
    exact r0_end 0 _

-- ============================================================================
-- Section 6.6: RLE Combinators & Sweep Soundness Lemmas
-- ============================================================================

theorem carry_word : ∀ (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (carryCfg (wordL w +> l) r) [target_tm]⊢*
      (carryCfg l (wordR (revWord w) +> r))
  | [], l, r, _ => stepStar_refl _ _
  | t :: ts, l, r, h => by
    simp only [isZpWord_cons, Bool.and_eq_true] at h
    rcases h with ⟨ht, hts⟩
    cases t <;> try contradiction
    · rw [wordL_cons, listblank_append_assoc]
      refine stepStar_trans ⟨_, carry_Z (wordL ts +> l) r⟩ ?_
      have ih := carry_word ts l (tokR .Z +> r) hts
      simpa [revWord_cons, wordR_append, listblank_append_assoc] using ih
    · rw [wordL_cons, listblank_append_assoc]
      refine stepStar_trans ⟨_, carry_P (wordL ts +> l) r⟩ ?_
      have ih := carry_word ts l (tokR .P +> r) hts
      simpa [revWord_cons, wordR_append, listblank_append_assoc] using ih

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
  Option.casesOn (popLastTok rle) none (fun p1 =>
    Prod.casesOn p1 (fun t1 r1 =>
      Tok.casesOn t1
        (Option.casesOn (popLastTok r1) none (fun p2 =>
          Prod.casesOn p2 (fun t2 r2 =>
            Tok.casesOn t2
              none
              (Prod.casesOn (popTokCount 8 .P 0 r2) (fun mVal r3 =>
                Bool.casesOn (Nat.beq mVal 0)
                  (Option.casesOn (popLastTok r3) none (fun p3 =>
                    Prod.casesOn p3 (fun t3 r4 =>
                      Tok.casesOn t3
                        none
                        (pushRlePosK [.U] 1 r4 fun r5 =>
                          pushRlePosK [.P] 1 rs fun rs1 =>
                          pushRlePosK [.Z] mVal rs1 fun rs2 => some (r5, rs2))
                        none none
                        (pushRlePosK [.M] 1 r4 fun r5 =>
                          pushRlePosK [.P] 1 rs fun rs1 =>
                          pushRlePosK [.Z] mVal rs1 fun rs2 => some (r5, rs2))
                        none none)))
                  none))
              none none
              (Option.casesOn (popTok .P r2) none (fun r3 =>
                pushRlePosK [.Z] 1 r3 fun r4 =>
                pushRlePosK [.P] 1 rs fun rs1 => some (r4, rs1)))
              none none)))
        (Option.casesOn (popToks [.T, .U, .M, .P] r1)
          (Option.casesOn (popToks [.T, .T, .T, .P] r1) none (fun r5 =>
            pushRlePosK [.PTTTM_TAIL] 1 rs fun rs1 =>
            pushRlePosK [.Z] 2 rs1 fun rs2 => some (r5, rs2)))
          (fun r5 =>
            pushRlePosK [.P] 1 rs fun rs1 =>
            pushRlePosK [.Z] 2 rs1 fun rs2 => some (r5, rs2)))
        (Option.casesOn (popToks [.T, .T, .P] r1) none (fun r4 =>
          pushRlePosK [.Z] 3 rs fun rs1 => some (r4, rs1)))
        none
        (Option.casesOn (popToks [.T, .T, .P] r1) none (fun r4 =>
          pushRlePosK [.P] 1 rs fun rs1 =>
          pushRlePosK [.Z] 2 rs1 fun rs2 => some (r4, rs2)))
        none
        none))

theorem popCarrySpecial_sound (rle rs rle' rs' : Rle) (r_end : ListBlank (Fin 2))
    (h : popCarrySpecial rle rs = some (rle', rs')) :
    (carryCfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
      (carryCfg (evalRle rle') (evalRStack rs' r_end)) := by
  unfold popCarrySpecial at h
  cases hp1 : popLastTok rle with
  | none => rw [hp1] at h; nomatch h
  | some p1 =>
    rcases p1 with ⟨t1, r1⟩
    rw [hp1] at h; dsimp -failIfUnchanged only at h
    rw [popLastTok_sound rle t1 r1 hp1]
    cases t1 with
    | Z | P | PTTTM_TAIL => nomatch h
    | U =>
      dsimp -failIfUnchanged only at h
      cases hp2 : popLastTok r1 with
      | none => rw [hp2] at h; nomatch h
      | some p2 =>
        rcases p2 with ⟨t2, r2⟩
        rw [hp2] at h; dsimp -failIfUnchanged only at h
        rw [popLastTok_sound r1 t2 r2 hp2]
        cases t2 with
        | U | W | Z | P | PTTTM_TAIL => nomatch h
        | M =>
          dsimp -failIfUnchanged only at h
          have hpcs := (popTokCount_sound 8 .P 0 r2).2
          rcases hpc : popTokCount 8 .P 0 r2 with ⟨mVal, r3⟩
          rw [hpc] at h hpcs; dsimp -failIfUnchanged only at h hpcs
          simp only [pow_zero_list, listblank_append_nil] at hpcs
          rw [hpcs]
          cases hm : Nat.beq mVal 0
          · rw [hm] at h; dsimp -failIfUnchanged only at h
            cases hp3 : popLastTok r3 with
            | none => rw [hp3] at h; nomatch h
            | some p3 =>
              rcases p3 with ⟨t3, r4⟩
              rw [hp3] at h; dsimp -failIfUnchanged only at h
              rw [popLastTok_sound r3 t3 r4 hp3]
              cases t3 with
              | U | W | Z | P | PTTTM_TAIL => nomatch h
              | M =>
                simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                refine stepStar_trans ⟨_, carry_MU_to_pmuCfg _ _⟩ ?_
                refine stepStar_trans (pmu_loop mVal (tokL .M +> evalRle r4) _) ?_
                refine stepStar_trans ⟨_, pmuCfg_M_to_carry (evalRle r4) _⟩ ?_
                simp only [evalRle_pushRlePos, evalRStack_pushRlePos, pow_succ_list, pow_zero_list,
                  List.append_nil, wordL_cons, wordL_nil, revWord_cons, revWord_nil]
                exact stepStar_refl _ _
              | T =>
                simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                refine stepStar_trans ⟨_, carry_MU_to_pmuCfg _ _⟩ ?_
                refine stepStar_trans (pmu_loop mVal (tokL .T +> evalRle r4) _) ?_
                refine stepStar_trans ⟨_, pmuCfg_T_to_carry (evalRle r4) _⟩ ?_
                simp only [evalRle_pushRlePos, evalRStack_pushRlePos, pow_succ_list, pow_zero_list,
                  List.append_nil, wordL_cons, wordL_nil, revWord_cons, revWord_nil]
                exact stepStar_refl _ _
          · rw [hm] at h; nomatch h
        | T =>
          dsimp -failIfUnchanged only at h
          cases hp3 : popTok .P r2 with
          | none => rw [hp3] at h; nomatch h
          | some r3 =>
            rw [hp3] at h
            simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [popTok_sound .P r2 r3 hp3]
            simp only [evalRle_pushRlePos, evalRStack_pushRlePos, pow_succ_list, pow_zero_list,
              List.append_nil, wordL_cons, wordL_nil, revWord_cons, revWord_nil]
            exact ⟨_, carry_PTU (evalRle r3) (evalRStack rs r_end)⟩
    | M =>
      dsimp -failIfUnchanged only at h
      cases hp2 : popToks [.T, .U, .M, .P] r1 with
      | some r5 =>
        rw [hp2] at h
        simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [popToks_sound _ r1 r5 hp2]
        simp only [evalRStack_pushRlePos, pow_succ_list, pow_zero_list, List.append_nil,
          wordL_cons, wordL_nil, revWord_cons, revWord_nil, listblank_append_assoc]
        exact ⟨_, carry_PMUTM (evalRle r5) (evalRStack rs r_end)⟩
      | none =>
        rw [hp2] at h; dsimp -failIfUnchanged only at h
        cases hp3 : popToks [.T, .T, .T, .P] r1 with
        | none => rw [hp3] at h; nomatch h
        | some r5 =>
          rw [hp3] at h
          simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rw [popToks_sound _ r1 r5 hp3]
          simp only [evalRStack_pushRlePos, pow_succ_list, pow_zero_list, List.append_nil,
            wordL_cons, wordL_nil, revWord_cons, revWord_nil, listblank_append_assoc]
          exact ⟨_, carry_PTTTM (evalRle r5) (evalRStack rs r_end)⟩
    | W =>
      dsimp -failIfUnchanged only at h
      cases hp2 : popToks [.T, .T, .P] r1 with
      | none => rw [hp2] at h; nomatch h
      | some r4 =>
        rw [hp2] at h
        simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [popToks_sound _ r1 r4 hp2]
        simp only [evalRStack_pushRlePos, pow_succ_list, pow_zero_list, List.append_nil,
          wordL_cons, wordL_nil, revWord_cons, revWord_nil, listblank_append_assoc]
        exact ⟨_, carry_PTTW (evalRle r4) (evalRStack rs r_end)⟩
    | T =>
      dsimp -failIfUnchanged only at h
      cases hp2 : popToks [.T, .T, .P] r1 with
      | none => rw [hp2] at h; nomatch h
      | some r4 =>
        rw [hp2] at h
        simp only [pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [popToks_sound _ r1 r4 hp2]
        simp only [evalRStack_pushRlePos, pow_succ_list, pow_zero_list, List.append_nil,
          wordL_cons, wordL_nil, revWord_cons, revWord_nil, listblank_append_assoc]
        exact ⟨_, carry_PTTT (evalRle r4) (evalRStack rs r_end)⟩

def popCarryLoop (fuel : Nat) (rle rs : Rle) : Rle × Rle :=
  Nat.rec
    (fun rle rs => (rle, rs))
    (fun _ ih rle rs =>
      List.casesOn rle ([], rs) (fun p rest =>
        Prod.casesOn p (fun w c =>
          Bool.casesOn (isZpWord w)
            (Option.casesOn (popCarrySpecial ((w, c) :: rest) rs)
              ((w, c) :: rest, rs)
              (fun p' => Prod.casesOn p' (fun rle' rs' => ih rle' rs')))
            (pushRlePosK w c rs fun rs' => ih rest rs'))))
    fuel rle rs

theorem popCarryLoop_sound : ∀ (fuel : Nat) (rle rs : Rle) (r_end : ListBlank (Fin 2)),
    (carryCfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
      (carryCfg (evalRle (popCarryLoop fuel rle rs).1) (evalRStack (popCarryLoop fuel rle rs).2 r_end))
  | 0, rle, rs, r_end => stepStar_refl _ _
  | fuel + 1, [], rs, r_end => stepStar_refl _ _
  | fuel + 1, (w, c) :: rest, rs, r_end => by
    unfold popCarryLoop; dsimp -failIfUnchanged only
    cases hw : isZpWord w
    · dsimp -failIfUnchanged only
      cases hp : popCarrySpecial ((w, c) :: rest) rs with
      | none => exact stepStar_refl _ _
      | some p' =>
        rcases p' with ⟨rle', rs'⟩
        dsimp -failIfUnchanged only
        refine stepStar_trans (popCarrySpecial_sound ((w, c) :: rest) rs rle' rs' r_end hp) ?_
        exact popCarryLoop_sound fuel rle' rs' r_end
    · dsimp -failIfUnchanged only
      rw [pushRlePosK_eq]
      simp only [evalRle_cons]
      refine stepStar_trans (carry_pow c w (evalRle rest) (evalRStack rs r_end) hw) ?_
      rw [← evalRStack_pushRlePos w c rs r_end]
      exact popCarryLoop_sound fuel rest (pushRlePos w c rs) r_end

theorem r0_word : ∀ (w : List Tok) (l r : ListBlank (Fin 2)),
    isZpWord w = true →
    (r0Cfg l (wordR w +> r)) [target_tm]⊢*
      (r0Cfg (wordL (revWord w) +> l) r)
  | [], l, r, _ => stepStar_refl _ _
  | t :: ts, l, r, h => by
    simp only [isZpWord_cons, Bool.and_eq_true] at h
    rcases h with ⟨ht, hts⟩
    cases t <;> try contradiction
    · rw [wordR_cons, listblank_append_assoc]
      refine stepStar_trans ⟨_, r0_Z l (wordR ts +> r)⟩ ?_
      have ih := r0_word ts (tokL .Z +> l) r hts
      simpa [revWord_cons, wordL_append, listblank_append_assoc] using ih
    · rw [wordR_cons, listblank_append_assoc]
      refine stepStar_trans ⟨_, r0_P l (wordR ts +> r)⟩ ?_
      have ih := r0_word ts (tokL .P +> l) r hts
      simpa [revWord_cons, wordL_append, listblank_append_assoc] using ih

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

def allZpStack (rs : Rle) : Bool :=
  List.rec true (fun p _ ih => Prod.casesOn p (fun it _ => Bool.casesOn (isZpWord it) false ih)) rs

@[simp] lemma allZpStack_nil : allZpStack [] = true := rfl
@[simp] lemma allZpStack_cons (w : List Tok) (c : Nat) (rest : Rle) :
    allZpStack ((w, c) :: rest) = (isZpWord w && allZpStack rest) := by
  change Bool.casesOn (isZpWord w) false (allZpStack rest) = (isZpWord w && allZpStack rest)
  cases isZpWord w <;> rfl

def copyRStack (rle rs : Rle) : Option Rle :=
  List.rec
    (fun rle => some rle)
    (fun p _ ih rle =>
      Prod.casesOn p (fun item count =>
        Bool.casesOn (isZpWord item)
          none
          (pushRlePosK item count rle fun rle' => ih rle')))
    rs rle

theorem copyRStack_sound : ∀ (rs : Rle) (rle rle' : Rle) (r_end : ListBlank (Fin 2)),
    copyRStack rle rs = some rle' →
    allZpStack rs = true ∧
      (r0Cfg (evalRle rle) (evalRStack rs r_end)) [target_tm]⊢*
        (r0Cfg (evalRle rle') r_end)
  | [], rle, rle', r_end, h => by
    injection h with hr; subst hr
    exact ⟨rfl, stepStar_refl _ _⟩
  | (w, c) :: rest, rle, rle', r_end, h => by
    unfold copyRStack at h; dsimp -failIfUnchanged only at h
    cases hw : isZpWord w
    · rw [hw] at h; nomatch h
    · rw [hw] at h; dsimp -failIfUnchanged only at h
      rw [pushRlePosK_eq] at h
      rcases copyRStack_sound rest (pushRlePos w c rle) rle' r_end h with ⟨hrest, hstep⟩
      simp only [allZpStack_cons, hw, hrest, Bool.and_self]
      refine ⟨trivial, ?_⟩
      simp only [evalRStack_cons]
      have hrev : isZpWord (revWord w) = true := by rw [isZpWord_revWord]; exact hw
      refine stepStar_trans (r0_pow c (revWord w) (evalRle rle) (evalRStack rest r_end) hrev) ?_
      simpa [revWord_revWord, evalRle_pushRlePos] using hstep

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
  | t :: ts, _, hw, hR => by
    simp only [isZpWord_cons, Bool.and_eq_true] at hw
    rcases hw with ⟨ht, hts⟩
    cases t <;> try contradiction
    · intro l k1; dsimp -failIfUnchanged only; rw [wordR_cons, listblank_append_assoc]
      exact hasRoundtrip_Z (hasRoundtrip_word ts hts hR) l k1
    · intro l k1; dsimp -failIfUnchanged only; rw [wordR_cons, listblank_append_assoc]
      exact hasRoundtrip_P (hasRoundtrip_word ts hts hR) l k1

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
    simp only [allZpStack_cons, Bool.and_eq_true] at hrs
    rcases hrs with ⟨hw, hrest⟩
    intro l k1
    simp only [evalRStack_cons]
    have hrev : isZpWord (revWord w) = true := by rw [isZpWord_revWord]; exact hw
    exact hasRoundtrip_pow c (revWord w) hrev (hasRoundtrip_stack rest hrest hR) l k1

def r1PhaseCfg (phase : Bool) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  if phase then r1OddCfg l r else r1Cfg l r

@[simp] lemma r1PhaseCfg_false (l r : ListBlank (Fin 2)) : r1PhaseCfg false l r = r1Cfg l r := rfl
@[simp] lemma r1PhaseCfg_true (l r : ListBlank (Fin 2)) : r1PhaseCfg true l r = r1OddCfg l r := rfl

def stepR1StarWordL (w : List Tok) (phase : Bool) : List Tok × Nat × Bool :=
  List.rec
    ([], 0, phase)
    (fun t _ ih =>
      Prod.casesOn ih (fun out rest =>
        Prod.casesOn rest (fun res p1 =>
          Bool.casesOn p1
            (Bool.casesOn (tokEq t .Z)
              (.P :: out, res, true)
              (.P :: out, Nat.add res 1, false))
            (Bool.casesOn (tokEq t .P)
              (.Z :: out, res, true)
              (.Z :: out, res, false)))))
    w

theorem stepR1StarWordL_cons (t : Tok) (ts : List Tok) (phase : Bool) :
    stepR1StarWordL (t :: ts) phase =
      let (out, res, p1) := stepR1StarWordL ts phase
      if p1 then
        if tokEq t .P then (.Z :: out, res, false) else (.Z :: out, res, true)
      else
        if tokEq t .Z then (.P :: out, res + 1, false) else (.P :: out, res, true) := by
  have hstep : stepR1StarWordL (t :: ts) phase =
      Prod.casesOn (stepR1StarWordL ts phase) (fun out rest =>
        Prod.casesOn rest (fun res p1 =>
          Bool.casesOn p1
            (Bool.casesOn (tokEq t .Z)
              (.P :: out, res, true)
              (.P :: out, Nat.add res 1, false))
            (Bool.casesOn (tokEq t .P)
              (.Z :: out, res, true)
              (.Z :: out, res, false)))) := rfl
  rw [hstep]
  rcases stepR1StarWordL ts phase with ⟨out, res, p1⟩
  cases p1
  · cases tokEq t .Z <;> rfl
  · cases tokEq t .P <;> rfl

theorem stepR1StarWordL_phase_inv : ∀ (w : List Tok) (phase : Bool),
    isZpWord w = true →
    (stepR1StarWordL w (!phase)).2.2 = !(stepR1StarWordL w phase).2.2
  | [], phase, _ => rfl
  | t :: ts, phase, hw => by
    simp only [isZpWord_cons, Bool.and_eq_true] at hw
    rcases hw with ⟨ht, hts⟩
    have ih := stepR1StarWordL_phase_inv ts phase hts
    rw [stepR1StarWordL_cons, stepR1StarWordL_cons]
    rcases h1 : stepR1StarWordL ts (!phase) with ⟨o1, r1, p1⟩
    rcases h2 : stepR1StarWordL ts phase with ⟨o2, r2, p2⟩
    rw [h1, h2] at ih; dsimp -failIfUnchanged only at ih ⊢; subst ih
    cases t <;> try contradiction
    · cases p2 <;> rfl
    · cases p2 <;> rfl

theorem stepR1StarWordL_sound : ∀ (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true → HasRoundtrip R →
    ∀ (k1 : Nat),
      (r1PhaseCfg phase l (wordR (revWord w) +> R k1)) [target_tm]⊢*
        (r1PhaseCfg (stepR1StarWordL w phase).2.2
          (wordL (stepR1StarWordL w phase).1 +> l)
          (R (k1 + 2 * (stepR1StarWordL w phase).2.1)))
  | [], phase, l, R, _, _, k1 => stepStar_refl _ _
  | t :: ts, phase, l, R, hw, hR, k1 => by
    simp only [isZpWord_cons, Bool.and_eq_true] at hw
    rcases hw with ⟨ht, hts⟩
    have hRt : HasRoundtrip (fun k => tokR t +> R k) := by
      cases t <;> try contradiction
      · exact hasRoundtrip_Z hR
      · exact hasRoundtrip_P hR
    have ih := stepR1StarWordL_sound ts phase l hts hRt k1
    simp only [revWord_cons, wordR_append, wordR_cons, wordR_nil, List.append_nil, listblank_append_assoc]
    rw [stepR1StarWordL_cons]
    rcases hs : stepR1StarWordL ts phase with ⟨out, res, p1⟩
    rw [hs] at ih
    dsimp -failIfUnchanged only at ih ⊢
    refine stepStar_trans ih ?_
    cases t <;> try contradiction
    · cases p1
      · simp only [tokEq, Bool.false_eq_true, ↓reduceIte, r1PhaseCfg, wordL_cons]
        refine stepStar_trans ⟨_, r1_Z (wordL out +> l) (R (k1 + 2 * res))⟩ ?_
        refine stepStar_trans (hR (tokL .M +> (tokL .Z +> (wordL out +> l))) (k1 + 2 * res)) ?_
        refine stepStar_trans ⟨_, turn_ZM (wordL out +> l) (R (k1 + 2 * res + 2))⟩ ?_
        have hadd : k1 + 2 * res + 2 = k1 + 2 * (res + 1) := by omega
        rw [hadd, listblank_append_assoc]
        exact stepStar_refl _ _
      · simp only [tokEq, Bool.false_eq_true, ↓reduceIte, r1PhaseCfg, wordL_cons, listblank_append_assoc]
        exact ⟨_, r1Odd_Z (wordL out +> l) (R (k1 + 2 * res))⟩
    · cases p1
      · simp only [tokEq, Bool.false_eq_true, ↓reduceIte, r1PhaseCfg, wordL_cons, listblank_append_assoc]
        exact ⟨_, r1_P (wordL out +> l) (R (k1 + 2 * res))⟩
      · simp only [tokEq, ↓reduceIte, r1PhaseCfg, wordL_cons, listblank_append_assoc]
        exact ⟨_, r1Odd_P (wordL out +> l) (R (k1 + 2 * res))⟩

def appendWord (w1 w2 : List Tok) : List Tok :=
  List.rec w2 (fun t _ ih => t :: ih) w1

@[simp] theorem appendWord_eq (w1 w2 : List Tok) : appendWord w1 w2 = w1 ++ w2 := by
  induction w1 with
  | nil => rfl
  | cons t ts ih =>
    change t :: appendWord ts w2 = t :: (ts ++ w2)
    rw [ih]

theorem stepR1Star_same_pow : ∀ (c : Nat) (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true →
    (stepR1StarWordL w phase).2.2 = phase →
    HasRoundtrip R →
    ∀ (k1 : Nat),
      (r1PhaseCfg phase l (((wordR (revWord w)) ^ c) +> R k1)) [target_tm]⊢*
        (r1PhaseCfg phase (((wordL (stepR1StarWordL w phase).1) ^ c) +> l)
          (R (k1 + 2 * (c * (stepR1StarWordL w phase).2.1))))
  | 0, w, phase, l, R, _, _, _, k1 => by
    simp
    exact stepStar_refl _ _
  | c + 1, w, phase, l, R, hw, hsame, hR, k1 => by
    have hrev : isZpWord (revWord w) = true := by rw [isZpWord_revWord]; exact hw
    have hR' : HasRoundtrip (fun k => ((wordR (revWord w)) ^ c) +> R k) := hasRoundtrip_pow c (revWord w) hrev hR
    rw [pow_succ_list, listblank_append_assoc]
    have h1 := stepR1StarWordL_sound w phase l hw hR' k1
    rw [hsame] at h1
    refine stepStar_trans h1 ?_
    dsimp -failIfUnchanged only
    have ih := stepR1Star_same_pow c w phase (wordL (stepR1StarWordL w phase).1 +> l) hw hsame hR
      (k1 + 2 * (stepR1StarWordL w phase).2.1)
    have hadd : k1 + 2 * (stepR1StarWordL w phase).2.1 + 2 * (c * (stepR1StarWordL w phase).2.1) =
        k1 + 2 * ((c + 1) * (stepR1StarWordL w phase).2.1) := by
      have : (c + 1) * (stepR1StarWordL w phase).2.1 =
          c * (stepR1StarWordL w phase).2.1 + (stepR1StarWordL w phase).2.1 := Nat.succ_mul c _
      omega
    rw [hadd] at ih
    rwa [pow_succ_right, listblank_append_assoc]

theorem stepR1Star_alt_pow : ∀ (q : Nat) (w : List Tok) (phase : Bool) (l : ListBlank (Fin 2))
    {R : Nat → ListBlank (Fin 2)},
    isZpWord w = true →
    (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.2 = phase →
    HasRoundtrip R →
    ∀ (k1 : Nat),
      let s1 := stepR1StarWordL w phase
      let s2 := stepR1StarWordL w s1.2.2
      (r1PhaseCfg phase l (((wordR (revWord w)) ^ (2 * q)) +> R k1)) [target_tm]⊢*
        (r1PhaseCfg phase (((wordL (s2.1 ++ s1.1)) ^ q) +> l)
          (R (k1 + 2 * (q * (s1.2.1 + s2.2.1)))))
  | 0, w, phase, l, R, _, _, _, k1 => by
    simp
    exact stepStar_refl _ _
  | q + 1, w, phase, l, R, hw, halt, hR, k1 => by
    dsimp -failIfUnchanged only
    have hrev : isZpWord (revWord w) = true := by rw [isZpWord_revWord]; exact hw
    have h2q : 2 * (q + 1) = 1 + (1 + 2 * q) := by omega
    rw [h2q, list_pow_add, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil,
      listblank_append_assoc, listblank_append_assoc]
    have hR2 : HasRoundtrip (fun k => ((wordR (revWord w)) ^ (2 * q)) +> R k) :=
      hasRoundtrip_pow (2 * q) (revWord w) hrev hR
    have hR1 : HasRoundtrip (fun k => wordR (revWord w) +> (((wordR (revWord w)) ^ (2 * q)) +> R k)) :=
      hasRoundtrip_word (revWord w) hrev hR2
    refine stepStar_trans (stepR1StarWordL_sound w phase l hw hR1 k1) ?_
    dsimp -failIfUnchanged only
    refine stepStar_trans
      (stepR1StarWordL_sound w (stepR1StarWordL w phase).2.2
        (wordL (stepR1StarWordL w phase).1 +> l) hw hR2
        (k1 + 2 * (stepR1StarWordL w phase).2.1)) ?_
    dsimp -failIfUnchanged only
    rw [halt]
    have ih := stepR1Star_alt_pow q w phase
      (wordL ((stepR1StarWordL w (stepR1StarWordL w phase).2.2).1 ++
        (stepR1StarWordL w phase).1) +> l)
      hw halt hR
      (k1 + 2 * (stepR1StarWordL w phase).2.1 +
        2 * (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1)
    dsimp -failIfUnchanged only at ih
    have hadd :
        k1 + 2 * (stepR1StarWordL w phase).2.1 +
          2 * (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1 +
          2 * (q * ((stepR1StarWordL w phase).2.1 +
            (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1)) =
        k1 + 2 * ((q + 1) * ((stepR1StarWordL w phase).2.1 +
          (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1)) := by
      have : (q + 1) * ((stepR1StarWordL w phase).2.1 +
          (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1) =
        q * ((stepR1StarWordL w phase).2.1 +
          (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1) +
        ((stepR1StarWordL w phase).2.1 +
          (stepR1StarWordL w (stepR1StarWordL w phase).2.2).2.1) := Nat.succ_mul q _
      omega
    rw [hadd] at ih
    have hw_app :
        wordL (stepR1StarWordL w (stepR1StarWordL w phase).2.2).1 +>
          (wordL (stepR1StarWordL w phase).1 +> l) =
        wordL ((stepR1StarWordL w (stepR1StarWordL w phase).2.2).1 ++
          (stepR1StarWordL w phase).1) +> l := by
      rw [wordL_append, listblank_append_assoc]
    rw [hw_app, pow_succ_right, listblank_append_assoc]
    exact ih

def sweepStarLoop (rle : Rle) (phase : Bool) (totalRes : Nat) (rs : Rle) : Rle × Bool × Nat :=
  List.rec
    (fun rle phase totalRes => (rle, phase, totalRes))
    (fun p _ ih rle phase totalRes =>
      Prod.casesOn p (fun item count =>
        Prod.casesOn (stepR1StarWordL item phase) (fun out1 rest1 =>
          Prod.casesOn rest1 (fun res1 nextPhase =>
            Bool.casesOn (Bool.casesOn nextPhase (Bool.casesOn phase true false) phase)
              (Prod.casesOn (stepR1StarWordL item nextPhase) (fun out2 rest2 =>
                Prod.casesOn rest2 (fun res2 _ =>
                  strictNat (Nat.div count 2) fun q =>
                  strictNat (Nat.mod count 2) fun rem =>
                  strictWord (appendWord out2 out1) fun w21 =>
                  pushRleK w21 q rle fun rle1 =>
                  strictNat (Nat.add totalRes (Nat.mul q (Nat.add res1 res2))) fun resAfterQ =>
                  Bool.casesOn (Nat.beq rem 1)
                    (ih rle1 phase resAfterQ)
                    (strictNat (Nat.add resAfterQ res1) fun resFinal =>
                      pushRlePosK out1 1 rle1 fun rle2 =>
                      ih rle2 nextPhase resFinal))))
              (strictNat (Nat.add totalRes (Nat.mul count res1)) fun tr' =>
                pushRlePosK out1 count rle fun rle' =>
                ih rle' phase tr')))))
    rs rle phase totalRes

theorem sweepStarLoop_cons (rle : Rle) (phase : Bool) (totalRes : Nat) (item : List Tok) (count : Nat) (rest : Rle) :
    sweepStarLoop rle phase totalRes ((item, count) :: rest) =
      let (out1, res1, nextPhase) := stepR1StarWordL item phase
      if nextPhase == phase then
        sweepStarLoop (pushRlePos out1 count rle) phase (totalRes + count * res1) rest
      else
        let (out2, res2, _) := stepR1StarWordL item nextPhase
        let q := count / 2
        let rem := count % 2
        let rle1 := pushRle (out2 ++ out1) q rle
        let resAfterQ := totalRes + q * (res1 + res2)
        if Nat.beq rem 1 then
          sweepStarLoop (pushRlePos out1 1 rle1) nextPhase (resAfterQ + res1) rest
        else
          sweepStarLoop rle1 phase resAfterQ rest := by
  have hstep : sweepStarLoop rle phase totalRes ((item, count) :: rest) =
      Prod.casesOn (stepR1StarWordL item phase) (fun out1 rest1 =>
        Prod.casesOn rest1 (fun res1 nextPhase =>
          Bool.casesOn (Bool.casesOn nextPhase (Bool.casesOn phase true false) phase)
            (Prod.casesOn (stepR1StarWordL item nextPhase) (fun out2 rest2 =>
              Prod.casesOn rest2 (fun res2 _ =>
                strictNat (Nat.div count 2) fun q =>
                strictNat (Nat.mod count 2) fun rem =>
                strictWord (appendWord out2 out1) fun w21 =>
                pushRleK w21 q rle fun rle1 =>
                strictNat (Nat.add totalRes (Nat.mul q (Nat.add res1 res2))) fun resAfterQ =>
                Bool.casesOn (Nat.beq rem 1)
                  (sweepStarLoop rle1 phase resAfterQ rest)
                  (strictNat (Nat.add resAfterQ res1) fun resFinal =>
                    pushRlePosK out1 1 rle1 fun rle2 =>
                    sweepStarLoop rle2 nextPhase resFinal rest))))
            (strictNat (Nat.add totalRes (Nat.mul count res1)) fun tr' =>
              pushRlePosK out1 count rle fun rle' =>
              sweepStarLoop rle' phase tr' rest))) := rfl
  rw [hstep]
  rcases stepR1StarWordL item phase with ⟨out1, res1, nextPhase⟩
  dsimp -failIfUnchanged only
  cases nextPhase <;> cases phase
  · simp only [strictNat_eq, pushRlePosK_eq]; rfl
  · rcases stepR1StarWordL item false with ⟨out2, res2, p2⟩
    dsimp -failIfUnchanged only
    simp only [strictNat_eq, strictWord_eq, appendWord_eq, pushRleK_eq, pushRlePosK_eq, nat_mod_eq]
    cases Nat.beq (count % 2) 1 <;> rfl
  · rcases stepR1StarWordL item true with ⟨out2, res2, p2⟩
    dsimp -failIfUnchanged only
    simp only [strictNat_eq, strictWord_eq, appendWord_eq, pushRleK_eq, pushRlePosK_eq, nat_mod_eq]
    cases Nat.beq (count % 2) 1 <;> rfl
  · simp only [strictNat_eq, pushRlePosK_eq]; rfl

theorem evalRle_pushRlePos_one (w : List Tok) (rle : Rle) :
    evalRle (pushRlePos w 1 rle) = wordL w +> evalRle rle := by
  rw [evalRle_pushRlePos, pow_succ_list, pow_zero_list, List.append_nil]

theorem sweepStarLoop_sound : ∀ (rs : Rle) (rle : Rle) (phase : Bool) (totalRes : Nat)
    {R : Nat → ListBlank (Fin 2)},
    allZpStack rs = true → HasRoundtrip R →
    ∀ (k1 : Nat),
      let res := sweepStarLoop rle phase totalRes rs
      (r1PhaseCfg phase (evalRle rle) (evalRStack rs (R (k1 + 2 * totalRes)))) [target_tm]⊢*
        (r1PhaseCfg res.2.1 (evalRle res.1) (R (k1 + 2 * res.2.2)))
  | [], rle, phase, totalRes, R, _, _, k1 => stepStar_refl _ _
  | (item, count) :: rest, rle, phase, totalRes, R, hrs, hR, k1 => by
    simp only [allZpStack_cons, Bool.and_eq_true] at hrs
    rcases hrs with ⟨hitem, hrest⟩
    have hrev : isZpWord (revWord item) = true := by rw [isZpWord_revWord]; exact hitem
    have hR_rest : HasRoundtrip (fun k => evalRStack rest (R k)) :=
      hasRoundtrip_stack rest hrest hR
    dsimp -failIfUnchanged only
    rw [sweepStarLoop_cons]
    dsimp -failIfUnchanged only
    by_cases hsame : (stepR1StarWordL item phase).2.2 = phase
    · have hbeq : ((stepR1StarWordL item phase).2.2 == phase) = true := beq_iff_eq.mpr hsame
      rw [hbeq]
      simp only [↓reduceIte, evalRStack_cons]
      refine stepStar_trans
        (stepR1Star_same_pow count item phase (evalRle rle) hitem hsame hR_rest (k1 + 2 * totalRes)) ?_
      dsimp -failIfUnchanged only
      have hadd : k1 + 2 * totalRes + 2 * (count * (stepR1StarWordL item phase).2.1) =
          k1 + 2 * (totalRes + count * (stepR1StarWordL item phase).2.1) := by omega
      rw [hadd, ← evalRle_pushRlePos]
      exact sweepStarLoop_sound rest (pushRlePos (stepR1StarWordL item phase).1 count rle)
        phase (totalRes + count * (stepR1StarWordL item phase).2.1) hrest hR k1
    · have hbeq : ((stepR1StarWordL item phase).2.2 == phase) = false := beq_false_of_ne hsame
      rw [hbeq]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hnot : (stepR1StarWordL item phase).2.2 = !phase := by
        cases phase <;> cases h : (stepR1StarWordL item false).2.2 <;>
          cases h2 : (stepR1StarWordL item true).2.2 <;> simp_all
      have halt : (stepR1StarWordL item (stepR1StarWordL item phase).2.2).2.2 = phase := by
        rw [hnot, stepR1StarWordL_phase_inv item phase hitem]
        cases phase <;> cases h : (stepR1StarWordL item false).2.2 <;>
          cases h2 : (stepR1StarWordL item true).2.2 <;> simp_all
      generalize hq : count / 2 = q
      generalize hrem : count % 2 = rem
      have hdiv : count = 2 * q + rem := by omega
      simp only [evalRStack_cons]
      rw [hdiv, list_pow_add, listblank_append_assoc]
      have hR_rem : HasRoundtrip (fun k => ((wordR (revWord item)) ^ rem) +> evalRStack rest (R k)) :=
        hasRoundtrip_pow rem (revWord item) hrev hR_rest
      refine stepStar_trans
        (stepR1Star_alt_pow q item phase (evalRle rle) hitem halt hR_rem (k1 + 2 * totalRes)) ?_
      dsimp -failIfUnchanged only
      rw [← evalRle_pushRle]
      have hadd1 : k1 + 2 * totalRes +
          2 * (q * ((stepR1StarWordL item phase).2.1 +
            (stepR1StarWordL item (stepR1StarWordL item phase).2.2).2.1)) =
          k1 + 2 * (totalRes + q * ((stepR1StarWordL item phase).2.1 +
            (stepR1StarWordL item (stepR1StarWordL item phase).2.2).2.1)) := by omega
      rw [hadd1]
      rcases (by omega : rem = 0 ∨ rem = 1) with rfl | rfl
      · have h01 : Nat.beq 0 1 = false := rfl
        rw [h01]
        simp only [Bool.false_eq_true, ↓reduceIte, pow_zero_list, listblank_append_nil]
        exact sweepStarLoop_sound rest _ phase _ hrest hR k1
      · have h11 : Nat.beq 1 1 = true := rfl
        rw [h11]
        simp only [↓reduceIte, pow_succ_list, pow_zero_list, List.append_nil]
        refine stepStar_trans
          (stepR1StarWordL_sound item phase _ hitem hR_rest _) ?_
        dsimp -failIfUnchanged only
        rw [← evalRle_pushRlePos_one]
        have hadd2 : k1 + 2 * (totalRes + q * ((stepR1StarWordL item phase).2.1 +
              (stepR1StarWordL item (stepR1StarWordL item phase).2.2).2.1)) +
            2 * (stepR1StarWordL item phase).2.1 =
            k1 + 2 * (totalRes + q * ((stepR1StarWordL item phase).2.1 +
              (stepR1StarWordL item (stepR1StarWordL item phase).2.2).2.1) +
              (stepR1StarWordL item phase).2.1) := by omega
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

def stepOneTokPure (mode : Mode) (t : Tok) : Option (List Tok × Mode) :=
  Mode.casesOn mode
    (Tok.casesOn t none none none (some ([.Z], .R0)) none (some ([.P], .R0)) (some ([.Z], .R1)))
    (Tok.casesOn t none none none (some ([.M, .Z], .R0)) none (some ([.P], .R1_ODD)) none)
    (Tok.casesOn t none none none (some ([.Z], .R1_ODD)) none (some ([.Z], .R1)) none)

theorem stepOneTokPure_sound (mode mode' : Mode) (t : Tok) (toks : List Tok) (l r : ListBlank (Fin 2))
    (h : stepOneTokPure mode t = some (toks, mode')) :
    (modeCfg mode l (tokR t +> r)) [target_tm]⊢*
      (modeCfg mode' (wordL toks +> l) r) := by
  cases mode <;> cases t <;> try contradiction
  all_goals
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp only [modeCfg, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, r0_Z l r⟩
  · exact ⟨_, r0_P l r⟩
  · exact ⟨_, r0_PTTTM_TAIL l r⟩
  · exact ⟨_, r1_Z l r⟩
  · exact ⟨_, r1_P l r⟩
  · exact ⟨_, r1Odd_Z l r⟩
  · exact ⟨_, r1Odd_P l r⟩

def stepOneWordPureL (mode : Mode) (w : List Tok) : Option (List Tok × Mode) :=
  List.rec
    (some ([], mode))
    (fun t _ ih =>
      Option.casesOn ih none (fun p1 =>
        Prod.casesOn p1 (fun outRest mode1 =>
          Option.casesOn (stepOneTokPure mode1 t) none (fun p2 =>
            Prod.casesOn p2 (fun toks mode2 =>
              some (appendWord toks outRest, mode2))))))
    w

theorem stepOneWordPureL_cons (mode : Mode) (t : Tok) (ts : List Tok) :
    stepOneWordPureL mode (t :: ts) =
      Option.casesOn (stepOneWordPureL mode ts) none (fun p1 =>
        Prod.casesOn p1 (fun outRest mode1 =>
          Option.casesOn (stepOneTokPure mode1 t) none (fun p2 =>
            Prod.casesOn p2 (fun toks mode2 =>
              some (appendWord toks outRest, mode2))))) := rfl

theorem stepOneWordPureL_sound : ∀ (w : List Tok) (mode mode' : Mode) (out : List Tok) (l r : ListBlank (Fin 2)),
    stepOneWordPureL mode w = some (out, mode') →
    (modeCfg mode l (wordR (revWord w) +> r)) [target_tm]⊢*
      (modeCfg mode' (wordL out +> l) r)
  | [], mode, mode', out, l, r, h => by
    change some ([], mode) = some (out, mode') at h
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    exact stepStar_refl _ _
  | t :: ts, mode, mode', out, l, r, h => by
    rw [stepOneWordPureL_cons] at h
    rcases h1 : stepOneWordPureL mode ts with _ | ⟨outRest, mode1⟩
    · rw [h1] at h; contradiction
    · rw [h1] at h; dsimp -failIfUnchanged only at h
      rcases h2 : stepOneTokPure mode1 t with _ | ⟨toks, mode2⟩
      · rw [h2] at h; contradiction
      · rw [h2] at h; dsimp -failIfUnchanged only at h
        injection h with hp; injection hp with hout hm; subst hout; subst hm
        simp only [revWord_cons, wordR_append, wordR_cons, wordR_nil, List.append_nil, listblank_append_assoc]
        refine stepStar_trans (stepOneWordPureL_sound ts mode mode1 outRest l (tokR t +> r) h1) ?_
        refine stepStar_trans (stepOneTokPure_sound mode1 _ t toks (wordL outRest +> l) r h2) ?_
        rw [appendWord_eq, wordL_append, listblank_append_assoc]
        exact stepStar_refl _ _

theorem stepOneWordPureL_same_pow : ∀ (c : Nat) (w out : List Tok) (mode : Mode) (l r : ListBlank (Fin 2)),
    stepOneWordPureL mode w = some (out, mode) →
    (modeCfg mode l (((wordR (revWord w)) ^ c) +> r)) [target_tm]⊢*
      (modeCfg mode (((wordL out) ^ c) +> l) r)
  | 0, _, _, _, _, _, _ => stepStar_refl _ _
  | c + 1, w, out, mode, l, r, h => by
    rw [pow_succ_list, listblank_append_assoc]
    refine stepStar_trans (stepOneWordPureL_sound w mode mode out l (((wordR (revWord w)) ^ c) +> r) h) ?_
    have ih := stepOneWordPureL_same_pow c w out mode (wordL out +> l) r h
    rwa [pow_succ_right, listblank_append_assoc]

theorem stepOneWordPureL_alt_pow : ∀ (q : Nat) (w out1 out2 : List Tok) (mode mode1 : Mode) (l r : ListBlank (Fin 2)),
    stepOneWordPureL mode w = some (out1, mode1) →
    stepOneWordPureL mode1 w = some (out2, mode) →
    (modeCfg mode l (((wordR (revWord w)) ^ (2 * q)) +> r)) [target_tm]⊢*
      (modeCfg mode (((wordL (out2 ++ out1)) ^ q) +> l) r)
  | 0, _, _, _, _, _, _, _, _, _ => stepStar_refl _ _
  | q + 1, w, out1, out2, mode, mode1, l, r, h1, h2 => by
    have h2q : 2 * (q + 1) = 1 + (1 + 2 * q) := by omega
    rw [h2q, list_pow_add, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil,
      listblank_append_assoc, listblank_append_assoc]
    refine stepStar_trans (stepOneWordPureL_sound w mode mode1 out1 l _ h1) ?_
    refine stepStar_trans (stepOneWordPureL_sound w mode1 mode out2 (wordL out1 +> l) _ h2) ?_
    have ih := stepOneWordPureL_alt_pow q w out1 out2 mode mode1 (wordL (out2 ++ out1) +> l) r h1 h2
    have hw : wordL out2 +> (wordL out1 +> l) = wordL (out2 ++ out1) +> l := by
      rw [wordL_append, listblank_append_assoc]
    rw [hw, pow_succ_right, listblank_append_assoc]
    exact ih

def stepOneTokL (rle : Rle) (mode : Mode) (t : Tok) : Option (Rle × Mode) :=
  Mode.casesOn mode
    (Tok.casesOn t none none none
      (pushRlePosK [.Z] 1 rle fun r => some (r, .R0))
      none
      (pushRlePosK [.P] 1 rle fun r => some (r, .R0))
      (pushRlePosK [.Z] 1 rle fun r => some (r, .R1)))
    (Tok.casesOn t none none none
      (some (pushToksLtr [.Z, .M] rle, .R0))
      none
      (pushRlePosK [.P] 1 rle fun r => some (r, .R1_ODD))
      none)
    (Tok.casesOn t none none none
      (pushRlePosK [.Z] 1 rle fun r => some (r, .R1_ODD))
      none
      (pushRlePosK [.Z] 1 rle fun r => some (r, .R1))
      none)

theorem stepOneTokL_sound (rle rle' : Rle) (mode mode' : Mode) (t : Tok) (r : ListBlank (Fin 2))
    (h : stepOneTokL rle mode t = some (rle', mode')) :
    (modeCfg mode (evalRle rle) (tokR t +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r) := by
  cases mode <;> cases t <;> try contradiction
  all_goals
    simp only [stepOneTokL, pushRlePosK_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [modeCfg, evalRle_pushToksLtr, evalRle_pushRlePos_one, revWord_cons, revWord_nil,
      List.nil_append, List.cons_append, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, r0_Z (evalRle rle) r⟩
  · exact ⟨_, r0_P (evalRle rle) r⟩
  · exact ⟨_, r0_PTTTM_TAIL (evalRle rle) r⟩
  · exact ⟨_, r1_Z (evalRle rle) r⟩
  · exact ⟨_, r1_P (evalRle rle) r⟩
  · exact ⟨_, r1Odd_Z (evalRle rle) r⟩
  · exact ⟨_, r1Odd_P (evalRle rle) r⟩

def stepOneWordL (rle : Rle) (mode : Mode) (w : List Tok) : Option (Rle × Mode) :=
  List.rec
    (some (rle, mode))
    (fun t _ ih =>
      Option.casesOn ih none (fun p =>
        Prod.casesOn p (fun rle1 mode1 => stepOneTokL rle1 mode1 t)))
    w

theorem stepOneWordL_cons (rle : Rle) (mode : Mode) (t : Tok) (ts : List Tok) :
    stepOneWordL rle mode (t :: ts) =
      Option.casesOn (stepOneWordL rle mode ts) none (fun p =>
        Prod.casesOn p (fun rle1 mode1 => stepOneTokL rle1 mode1 t)) := rfl

theorem stepOneWordL_sound : ∀ (w : List Tok) (rle rle' : Rle) (mode mode' : Mode) (r : ListBlank (Fin 2)),
    stepOneWordL rle mode w = some (rle', mode') →
    (modeCfg mode (evalRle rle) (wordR (revWord w) +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r)
  | [], rle, rle', mode, mode', r, h => by
    change some (rle, mode) = some (rle', mode') at h
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    exact stepStar_refl _ _
  | t :: ts, rle, rle', mode, mode', r, h => by
    rw [stepOneWordL_cons] at h
    rcases h1 : stepOneWordL rle mode ts with _ | ⟨rle1, mode1⟩
    · rw [h1] at h; contradiction
    · rw [h1] at h; dsimp -failIfUnchanged only at h
      simp only [revWord_cons, wordR_append, wordR_cons, wordR_nil, List.append_nil, listblank_append_assoc]
      refine stepStar_trans (stepOneWordL_sound ts rle rle1 mode mode1 (tokR t +> r) h1) ?_
      exact stepOneTokL_sound rle1 rle' mode1 mode' t r h

def stepOneBounceFuel (fuel : Nat) (item : List Tok) (count : Nat) (rle : Rle) (mode : Mode) : Option (Rle × Mode) :=
  Nat.rec
    (fun count rle mode =>
      Nat.casesOn count (some (rle, mode)) (fun _ => none))
    (fun _ ih count rle mode =>
      Nat.casesOn count
        (some (rle, mode))
        (fun countPred =>
          Bool.casesOn (modeEq mode .R0)
            (Option.casesOn (stepOneWordPureL mode item) none (fun p1 =>
              Prod.casesOn p1 (fun out1 mode1 =>
                strictWord out1 fun out1w =>
                Bool.casesOn (modeEq mode1 mode)
                  (Bool.casesOn (Nat.ble 1 countPred)
                    (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
                      Prod.casesOn p (fun rle' mode' => ih countPred rle' mode')))
                    (Option.casesOn (stepOneWordPureL mode1 item) none (fun p2 =>
                      Prod.casesOn p2 (fun out2 mode2 =>
                        Bool.casesOn (modeEq mode2 mode)
                          (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
                            Prod.casesOn p (fun rle' mode' => ih countPred rle' mode')))
                          (strictNat (Nat.div (Nat.add countPred 1) 2) fun q =>
                            strictNat (Nat.mod (Nat.add countPred 1) 2) fun rem =>
                            strictWord (appendWord out2 out1w) fun w21 =>
                            pushRleK w21 q rle fun rle' =>
                            ih rem rle' mode)))))
                  (pushRlePosK out1w (Nat.add countPred 1) rle fun rle' =>
                    some (rle', mode)))))
            (Bool.casesOn (isZpWord item)
              (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
                Prod.casesOn p (fun rle' mode' => ih countPred rle' mode')))
              (pushRlePosK item (Nat.add countPred 1) rle fun rle' =>
                some (rle', .R0)))))
    fuel count rle mode

theorem stepOneBounceFuel_succ (fuel : Nat) (item : List Tok) (count : Nat) (rle : Rle) (mode : Mode) :
    stepOneBounceFuel (fuel + 1) item (count + 1) rle mode =
      Bool.casesOn (modeEq mode .R0)
        (Option.casesOn (stepOneWordPureL mode item) none (fun p1 =>
          Prod.casesOn p1 (fun out1 mode1 =>
            strictWord out1 fun out1w =>
            Bool.casesOn (modeEq mode1 mode)
              (Bool.casesOn (Nat.ble 1 count)
                (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
                  Prod.casesOn p (fun rle' mode' => stepOneBounceFuel fuel item count rle' mode')))
                (Option.casesOn (stepOneWordPureL mode1 item) none (fun p2 =>
                  Prod.casesOn p2 (fun out2 mode2 =>
                    Bool.casesOn (modeEq mode2 mode)
                      (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
                        Prod.casesOn p (fun rle' mode' => stepOneBounceFuel fuel item count rle' mode')))
                      (strictNat (Nat.div (Nat.add count 1) 2) fun q =>
                        strictNat (Nat.mod (Nat.add count 1) 2) fun rem =>
                        strictWord (appendWord out2 out1w) fun w21 =>
                        pushRleK w21 q rle fun rle' =>
                        stepOneBounceFuel fuel item rem rle' mode)))))
              (pushRlePosK out1w (Nat.add count 1) rle fun rle' =>
                some (rle', mode)))))
        (Bool.casesOn (isZpWord item)
          (Option.casesOn (stepOneWordL rle mode item) none (fun p =>
            Prod.casesOn p (fun rle' mode' => stepOneBounceFuel fuel item count rle' mode')))
          (pushRlePosK item (Nat.add count 1) rle fun rle' =>
            some (rle', .R0))) := rfl

theorem stepOneBounceFuel_sound : ∀ (fuel : Nat) (item : List Tok) (count : Nat)
    (rle rle' : Rle) (mode mode' : Mode) (r : ListBlank (Fin 2)),
    stepOneBounceFuel fuel item count rle mode = some (rle', mode') →
    (modeCfg mode (evalRle rle) (((wordR (revWord item)) ^ count) +> r)) [target_tm]⊢*
      (modeCfg mode' (evalRle rle') r)
  | 0, item, 0, rle, rle', mode, mode', r, h => by
    change some (rle, mode) = some (rle', mode') at h
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    exact stepStar_refl _ _
  | 0, _, _ + 1, _, _, _, _, _, h => by contradiction
  | fuel + 1, item, 0, rle, rle', mode, mode', r, h => by
    change some (rle, mode) = some (rle', mode') at h
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    exact stepStar_refl _ _
  | fuel + 1, item, count + 1, rle, rle', mode, mode', r, h => by
    rw [stepOneBounceFuel_succ] at h
    cases hm0 : modeEq mode .R0
    · rw [hm0] at h; dsimp -failIfUnchanged only at h
      rcases hp1 : stepOneWordPureL mode item with _ | ⟨out1, mode1⟩
      · rw [hp1] at h; contradiction
      · rw [hp1] at h; simp only [strictWord_eq] at h
        cases hm1 : modeEq mode1 mode
        · rw [hm1] at h; dsimp -failIfUnchanged only at h
          cases hble : Nat.ble 1 count
          · rw [hble] at h; dsimp -failIfUnchanged only at h
            rcases hw : stepOneWordL rle mode item with _ | ⟨rle1, mode1'⟩
            · rw [hw] at h; contradiction
            · rw [hw] at h; dsimp -failIfUnchanged only at h
              rw [pow_succ_list, listblank_append_assoc]
              refine stepStar_trans (stepOneWordL_sound item rle rle1 mode mode1' _ hw) ?_
              exact stepOneBounceFuel_sound fuel item count rle1 rle' mode1' mode' r h
          · rw [hble] at h; dsimp -failIfUnchanged only at h
            rcases hp2 : stepOneWordPureL mode1 item with _ | ⟨out2, mode2⟩
            · rw [hp2] at h; contradiction
            · rw [hp2] at h; dsimp -failIfUnchanged only at h
              cases hm2 : modeEq mode2 mode
              · rw [hm2] at h; dsimp -failIfUnchanged only at h
                rcases hw : stepOneWordL rle mode item with _ | ⟨rle1, mode1'⟩
                · rw [hw] at h; contradiction
                · rw [hw] at h; dsimp -failIfUnchanged only at h
                  rw [pow_succ_list, listblank_append_assoc]
                  refine stepStar_trans (stepOneWordL_sound item rle rle1 mode mode1' _ hw) ?_
                  exact stepOneBounceFuel_sound fuel item count rle1 rle' mode1' mode' r h
              · rw [hm2] at h
                simp only [strictNat_eq, appendWord_eq, pushRleK_eq,
                  nat_add_eq, nat_div_eq, nat_mod_eq] at h
                have hm2_eq : mode2 = mode := (modeEq_iff mode2 mode).mp hm2
                subst mode2
                generalize hq : (count + 1) / 2 = q at h
                generalize hrem : (count + 1) % 2 = rem at h
                have hdiv : count + 1 = 2 * q + rem := by omega
                rw [hdiv, list_pow_add, listblank_append_assoc]
                refine stepStar_trans (stepOneWordPureL_alt_pow q item out1 out2 mode mode1 (evalRle rle) _ hp1 hp2) ?_
                rw [← evalRle_pushRle]
                exact stepOneBounceFuel_sound fuel item rem (pushRle (out2 ++ out1) q rle) rle' mode mode' r h
        · rw [hm1] at h; simp only [pushRlePosK_eq, nat_add_eq, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          have hm1_eq : mode1 = mode := (modeEq_iff mode1 mode).mp hm1
          subst mode1
          rw [evalRle_pushRlePos]
          exact stepOneWordPureL_same_pow (count + 1) item out1 mode (evalRle rle) r hp1
    · rw [hm0] at h; dsimp -failIfUnchanged only at h
      cases hzp : isZpWord item
      · rw [hzp] at h; dsimp -failIfUnchanged only at h
        rcases hw : stepOneWordL rle mode item with _ | ⟨rle1, mode1'⟩
        · rw [hw] at h; contradiction
        · rw [hw] at h; dsimp -failIfUnchanged only at h
          rw [pow_succ_list, listblank_append_assoc]
          refine stepStar_trans (stepOneWordL_sound item rle rle1 mode mode1' _ hw) ?_
          exact stepOneBounceFuel_sound fuel item count rle1 rle' mode1' mode' r h
      · rw [hzp] at h; simp only [pushRlePosK_eq, nat_add_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hm0_eq : mode = .R0 := (modeEq_iff mode .R0).mp hm0
        subst mode
        have hrev : isZpWord (revWord item) = true := by rw [isZpWord_revWord]; exact hzp
        simp only [modeCfg_R0, evalRle_pushRlePos]
        have hr0 := r0_pow (count + 1) (revWord item) (evalRle rle) r hrev
        rwa [revWord_revWord] at hr0

def simpleOneBounceCarry (rle : Rle) (mode : Mode) (rs : Rle) (k1 : Nat) : Option (Rle × Nat) :=
  List.rec
    (fun rle mode =>
      Bool.casesOn (modeEq mode .R0) none
        (strictNat (Nat.add k1 2) fun kOut => some (rle, kOut)))
    (fun p _ ih rle mode =>
      Prod.casesOn p (fun item count =>
        Option.casesOn (stepOneBounceFuel 3 item count rle mode) none (fun p' =>
          Prod.casesOn p' (fun rle' mode' => ih rle' mode'))))
    rs rle mode

theorem simpleOneBounceCarry_cons (rle : Rle) (mode : Mode) (item : List Tok) (count : Nat) (rest : Rle) (k1 : Nat) :
    simpleOneBounceCarry rle mode ((item, count) :: rest) k1 =
      Option.casesOn (stepOneBounceFuel 3 item count rle mode) none (fun p' =>
        Prod.casesOn p' (fun rle' mode' => simpleOneBounceCarry rle' mode' rest k1)) := rfl

theorem simpleOneBounceCarry_sound : ∀ (rs : Rle) (rle rle' : Rle) (mode : Mode) (k1 kOut : Nat),
    simpleOneBounceCarry rle mode rs k1 = some (rle', kOut) →
    (modeCfg mode (evalRle rle) (evalRStack rs (evalWK k1))) [target_tm]⊢*
      (carryCfg (evalRle rle') (evalWK kOut))
  | [], rle, rle', mode, k1, kOut, h => by
    unfold simpleOneBounceCarry at h; dsimp -failIfUnchanged only at h
    cases hm : modeEq mode .R0
    · rw [hm] at h; contradiction
    · rw [hm] at h; dsimp -failIfUnchanged only [strictNat_eq] at h
      injection h with hp; injection hp with h1 h2; subst h1; subst h2
      rw [(modeEq_iff mode .R0).mp hm]
      exact r0_end k1 (evalRle rle)
  | (item, count) :: rest, rle, rle', mode, k1, kOut, h => by
    rw [simpleOneBounceCarry_cons] at h
    rcases hb : stepOneBounceFuel 3 item count rle mode with _ | ⟨rle1, mode1⟩
    · rw [hb] at h; contradiction
    · rw [hb] at h; dsimp -failIfUnchanged only at h
      simp only [evalRStack_cons]
      refine stepStar_trans (stepOneBounceFuel_sound 3 item count rle rle1 mode mode1 _ hb) ?_
      exact simpleOneBounceCarry_sound rest rle1 rle' mode1 k1 kOut h

def hasSpecialWord (w : List Tok) : Bool :=
  List.casesOn w false (fun t _ =>
    Tok.casesOn t false false false false false false true)

def hasSpecial (rs : Rle) : Bool :=
  List.rec false (fun p _ ih => Prod.casesOn p (fun it _ => Bool.casesOn (hasSpecialWord it) ih true)) rs

def runRightSweepStarCarry (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : Nat) : Option (Rle × Nat) :=
  Bool.casesOn (hasSpecial rStack)
    (Bool.casesOn (modeEq mode .R0)
      (Bool.casesOn (allZpStack rStack)
        none
        (Prod.casesOn (sweepStarLoop rle (Bool.casesOn (modeEq mode .R1) true false) 0 rStack) (fun rle1 rest =>
            Prod.casesOn rest (fun finalPhase totalRes =>
              strictNat (Nat.add k1 (Nat.mul 2 totalRes)) fun kFinal1 =>
              Bool.casesOn finalPhase
                (strictNat (Nat.add kFinal1 1) fun kf =>
                  pushRlePosK [.P] 1 rle1 fun rle2 =>
                  some (stepZtToCarry rle2 kf))
                (pushRlePosK [.Z] 1 rle1 fun rle2 =>
                  some (stepZtToCarry rle2 kFinal1))))))
      (Option.casesOn (copyRStack rle rStack) none (fun rle' =>
        strictNat (Nat.add k1 2) fun kOut => some (rle', kOut))))
    (simpleOneBounceCarry rle mode rStack k1)

theorem runRightSweepStarCarry_sound (rle rStack rOut : Rle) (mode : Mode) (k1 kOut : Nat)
    (h : runRightSweepStarCarry rle mode rStack k1 = some (rOut, kOut)) :
    (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1))) [target_tm]⊢*
      (carryCfg (evalRle rOut) (evalWK kOut)) := by
  unfold runRightSweepStarCarry at h
  cases hs : hasSpecial rStack
  · rw [hs] at h; dsimp -failIfUnchanged only at h
    cases hm : modeEq mode .R0
    · rw [hm] at h; dsimp -failIfUnchanged only at h
      cases hall : allZpStack rStack
      · rw [hall] at h; contradiction
      · rw [hall] at h; dsimp -failIfUnchanged only at h
        have hphase : modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)) =
            r1PhaseCfg (Bool.casesOn (modeEq mode .R1) true false) (evalRle rle) (evalRStack rStack (evalWK (k1 + 2 * 0))) := by
          cases mode with
          | R0 => contradiction
          | R1 => rfl
          | R1_ODD => rfl
        rw [hphase]
        have hsw_sound := sweepStarLoop_sound rStack rle (Bool.casesOn (modeEq mode .R1) true false) 0 hall hasRoundtrip_evalWK k1
        dsimp -failIfUnchanged only at hsw_sound
        rcases hsw : sweepStarLoop rle (Bool.casesOn (modeEq mode .R1) true false) 0 rStack with ⟨rle1, finalPhase, totalRes⟩
        rw [hsw] at h hsw_sound
        dsimp -failIfUnchanged only at h hsw_sound
        refine stepStar_trans hsw_sound ?_
        cases finalPhase
        · simp only [strictNat_eq, pushRlePosK_eq, nat_add_eq, nat_mul_eq, Option.some.injEq] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp -failIfUnchanged only at h1 h2
          rw [← h1, ← h2]
          simp only [r1PhaseCfg_false]
          refine stepStar_trans (r1_end (k1 + 2 * totalRes) (evalRle rle1)) ?_
          have hzt := stepZtToCarry_sound (pushRlePos [.P] 1 rle1) (k1 + 2 * totalRes + 1)
          rw [evalRle_pushRlePos_one] at hzt
          exact hzt
        · simp only [strictNat_eq, pushRlePosK_eq, nat_add_eq, nat_mul_eq, Option.some.injEq] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp -failIfUnchanged only at h1 h2
          rw [← h1, ← h2]
          simp only [r1PhaseCfg_true]
          refine stepStar_trans (r1Odd_end (k1 + 2 * totalRes) (evalRle rle1)) ?_
          have hzt := stepZtToCarry_sound (pushRlePos [.Z] 1 rle1) (k1 + 2 * totalRes)
          rw [evalRle_pushRlePos_one] at hzt
          exact hzt
    · rw [hm] at h; dsimp -failIfUnchanged only at h
      rcases hc : copyRStack rle rStack with _ | rle'
      · rw [hc] at h; contradiction
      · rw [hc] at h; simp only [strictNat_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [(modeEq_iff mode .R0).mp hm, modeCfg_R0]
        refine stepStar_trans (copyRStack_sound rStack rle rle' (evalWK k1) hc).2 ?_
        exact r0_end k1 (evalRle rle')
  · rw [hs] at h; dsimp -failIfUnchanged only at h
    exact simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h

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
  Option.casesOn (runRightSweepStarCarry rle mode rStack k1) .err (fun p =>
    Prod.casesOn p (fun rOut kOut => .next rOut kOut))

theorem finishTurn_sound (rle : Rle) (mode : Mode) (rStack : Rle) (k1 : Nat)
    (hne : finishTurn rle mode rStack k1 ≠ .err) :
    StepCarryValid (modeCfg mode (evalRle rle) (evalRStack rStack (evalWK k1)))
      (finishTurn rle mode rStack k1) := by
  unfold finishTurn at hne ⊢
  rcases hr : runRightSweepStarCarry rle mode rStack k1 with _ | ⟨rOut, kOut⟩
  · try rw [hr] at hne
    dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
  · try rw [hr]
    dsimp -failIfUnchanged only
    exact runRightSweepStarCarry_sound rle rStack rOut mode k1 kOut hr

def matchRule2 (t1 t2 : Tok) : Option (List Tok × Mode) :=
  Tok.casesOn t1
    none
    (Tok.casesOn t2 none none (some ([.T], .R1)) (some ([.P], .R1)) none none none)
    none none
    (Tok.casesOn t2 none none none (some ([.T, .M], .R1)) none (some ([.T, .P], .R0)) none)
    none none

theorem matchRule2_sound (t1 t2 : Tok) (out : List Tok) (mode : Mode) (r4 : Rle) (r : ListBlank (Fin 2))
    (h : matchRule2 t1 t2 = some (out, mode)) :
    (carryCfg (tokL t1 +> (tokL t2 +> evalRle r4)) r) [target_tm]⊢*
      (modeCfg mode (evalRle (pushToksLtr out r4)) r) := by
  cases t1 <;> try contradiction
  all_goals (cases t2 <;> try contradiction)
  all_goals
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp only [modeCfg, evalRle_pushToksLtr, revWord_cons, revWord_nil, List.nil_append,
      List.cons_append, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, turn_WM (evalRle r4) r⟩
  · exact ⟨_, turn_ZM (evalRle r4) r⟩
  · exact ⟨_, turn_ZT (evalRle r4) r⟩
  · exact ⟨_, turn_PT (evalRle r4) r⟩

def matchRule3 (t1 t2 t3 : Tok) : Option (List Tok × Mode) :=
  Tok.casesOn t1
    (Tok.casesOn t2 none
      (Tok.casesOn t3 none none none (some ([.T, .T], .R1_ODD)) none none none)
      none none none none none)
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3 none none none (some ([.T, .M, .P], .R0)) none (some ([.T, .Z], .R1)) none)
      none none)
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3 none none none (some ([.T, .W, .Z], .R0)) none (some ([.M, .U, .Z], .R1_ODD)) none)
      none none)
    none
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3 none none none (some ([.T, .W, .P], .R0)) none (some ([.M, .U, .Z], .R1)) none)
      none none)
    none none

theorem matchRule3_sound (t1 t2 t3 : Tok) (out : List Tok) (mode : Mode) (r5 : Rle) (r : ListBlank (Fin 2))
    (h : matchRule3 t1 t2 t3 = some (out, mode)) :
    (carryCfg (tokL t1 +> (tokL t2 +> (tokL t3 +> evalRle r5))) r) [target_tm]⊢*
      (modeCfg mode (evalRle (pushToksLtr out r5)) r) := by
  cases t1 <;> try contradiction
  all_goals (cases t2 <;> try contradiction)
  all_goals (cases t3 <;> try contradiction)
  all_goals
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp only [modeCfg, evalRle_pushToksLtr, revWord_cons, revWord_nil, List.nil_append,
      List.cons_append, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, turn_ZMU (evalRle r5) r⟩
  · exact ⟨_, turn_ZTM (evalRle r5) r⟩
  · exact ⟨_, turn_PTM (evalRle r5) r⟩
  · exact ⟨_, turn_ZTW (evalRle r5) r⟩
  · exact ⟨_, turn_PTW (evalRle r5) r⟩
  · exact ⟨_, turn_ZTT (evalRle r5) r⟩
  · exact ⟨_, turn_PTT (evalRle r5) r⟩

def matchRule4 (t1 t2 t3 t4 : Tok) : Option (List Tok × Mode) :=
  Tok.casesOn t1
    (Tok.casesOn t2 none
      (Tok.casesOn t3 none none none none none
        (Tok.casesOn t4 none none none (some ([.T, .W, .M, .P], .R0)) none none none)
        none)
      none none none none none)
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3 none none none none
        (Tok.casesOn t4 none none none (some ([.T, .W, .Z], .R1)) none (some ([.M, .U, .Z, .P], .R0)) none)
        none none)
      none none)
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3
        (Tok.casesOn t4 none (some ([.T, .Z], .R1_ODD)) none none none none none)
        none none none
        (Tok.casesOn t4 none none none (some ([.P, .Z, .Z], .R0)) none none none)
        none none)
      none none)
    none
    (Tok.casesOn t2 none
      (Tok.casesOn t3 none none none none
        (Tok.casesOn t4 none none none none none (some ([.M, .U, .Z, .P], .R0)) none)
        none none)
      none none
      (Tok.casesOn t3 none none none none
        (Tok.casesOn t4 none none none (some ([.P, .Z, .P], .R0)) none none none)
        none none)
      none none)
    none none

theorem matchRule4_sound (t1 t2 t3 t4 : Tok) (out : List Tok) (mode : Mode) (r6 : Rle) (r : ListBlank (Fin 2))
    (h : matchRule4 t1 t2 t3 t4 = some (out, mode)) :
    (carryCfg (tokL t1 +> (tokL t2 +> (tokL t3 +> (tokL t4 +> evalRle r6)))) r) [target_tm]⊢*
      (modeCfg mode (evalRle (pushToksLtr out r6)) r) := by
  cases t1 <;> try contradiction
  all_goals (cases t2 <;> try contradiction)
  all_goals (cases t3 <;> try contradiction)
  all_goals (cases t4 <;> try contradiction)
  all_goals
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp only [modeCfg, evalRle_pushToksLtr, revWord_cons, revWord_nil, List.nil_append,
      List.cons_append, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, turn_ZPMU (evalRle r6) r⟩
  · exact ⟨_, turn_ZTTM (evalRle r6) r⟩
  · exact ⟨_, turn_PTTM (evalRle r6) r⟩
  · exact ⟨_, turn_MUTW (evalRle r6) r⟩
  · exact ⟨_, turn_ZTTW (evalRle r6) r⟩
  · exact ⟨_, turn_PTMT (evalRle r6) r⟩
  · exact ⟨_, turn_ZTTT (evalRle r6) r⟩

def matchRule5 (t1 t2 t3 t4 t5 : Tok) : Option (List Tok × Mode) :=
  Tok.casesOn t1
    none
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3
        (Tok.casesOn t4 none
          (Tok.casesOn t5 none none none (some ([.P, .Z, .P], .R0)) none none none)
          none none none none none)
        none none none
        (Tok.casesOn t4 none none none none
          (Tok.casesOn t5 none none none (some ([.P, .Z, .Z], .R1)) none none none)
          none none)
        none none)
      none none)
    (Tok.casesOn t2 none none none none
      (Tok.casesOn t3 none none none none
        (Tok.casesOn t4 none none none none
          (Tok.casesOn t5 none none none none none (some ([.T, .Z, .Z, .Z], .R0)) none)
          none none)
        none none)
      none none)
    none none none none

theorem matchRule5_sound (t1 t2 t3 t4 t5 : Tok) (out : List Tok) (mode : Mode) (r7 : Rle) (r : ListBlank (Fin 2))
    (h : matchRule5 t1 t2 t3 t4 t5 = some (out, mode)) :
    (carryCfg (tokL t1 +> (tokL t2 +> (tokL t3 +> (tokL t4 +> (tokL t5 +> evalRle r7))))) r) [target_tm]⊢*
      (modeCfg mode (evalRle (pushToksLtr out r7)) r) := by
  cases t1 <;> try contradiction
  all_goals (cases t2 <;> try contradiction)
  all_goals (cases t3 <;> try contradiction)
  all_goals (cases t4 <;> try contradiction)
  all_goals (cases t5 <;> try contradiction)
  all_goals
    injection h with hp; injection hp with h1 h2; subst h1; subst h2
    simp only [modeCfg, evalRle_pushToksLtr, revWord_cons, revWord_nil, List.nil_append,
      List.cons_append, wordL_cons, wordL_nil, List.append_nil, listblank_append_assoc]
  · exact ⟨_, turn_ZMUTM (evalRle r7) r⟩
  · exact ⟨_, turn_ZTTTM (evalRle r7) r⟩
  · exact ⟨_, turn_PTTTW (evalRle r7) r⟩

def isEmptyRle (r : Rle) : Bool :=
  List.casesOn r true (fun _ _ => false)

@[simp] theorem isEmptyRle_iff (r : Rle) : isEmptyRle r = true ↔ r = [] := by
  cases r <;> simp [isEmptyRle]

def stepTurnFrom3 (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : Nat) : StepCarryRes :=
  Option.casesOn (matchRule3 t1 t2 t3)
    (Option.casesOn (popLastTok r5) .err (fun p4 =>
      Prod.casesOn p4 (fun t4 r6 =>
        Option.casesOn (matchRule4 t1 t2 t3 t4)
          (Option.casesOn (popLastTok r6) .err (fun p5 =>
            Prod.casesOn p5 (fun t5 r7 =>
              Option.casesOn (matchRule5 t1 t2 t3 t4 t5) .err (fun pm =>
                Prod.casesOn pm (fun out mode => finishTurn (pushToksLtr out r7) mode rStack k1)))))
          (fun pm => Prod.casesOn pm (fun out mode => finishTurn (pushToksLtr out r6) mode rStack k1)))))
    (fun pm => Prod.casesOn pm (fun out mode => finishTurn (pushToksLtr out r5) mode rStack k1))

theorem stepTurnFrom3_sound (t1 t2 t3 : Tok) (r5 rStack : Rle) (k1 : Nat)
    (hne : stepTurnFrom3 t1 t2 t3 r5 rStack k1 ≠ .err) :
    StepCarryValid (carryCfg (tokL t1 +> (tokL t2 +> (tokL t3 +> evalRle r5))) (evalRStack rStack (evalWK k1)))
      (stepTurnFrom3 t1 t2 t3 r5 rStack k1) := by
  unfold stepTurnFrom3 at hne ⊢
  rcases hm3 : matchRule3 t1 t2 t3 with _ | ⟨out, mode⟩
  · try rw [hm3] at hne; try rw [hm3]
    dsimp -failIfUnchanged only at hne ⊢
    rcases hp4 : popLastTok r5 with _ | ⟨t4, r6⟩
    · try rw [hp4] at hne
      dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
    · try rw [hp4] at hne; try rw [hp4]
      dsimp -failIfUnchanged only at hne ⊢
      rw [popLastTok_sound r5 t4 r6 hp4]
      rcases hm4 : matchRule4 t1 t2 t3 t4 with _ | ⟨out, mode⟩
      · try rw [hm4] at hne; try rw [hm4]
        dsimp -failIfUnchanged only at hne ⊢
        rcases hp5 : popLastTok r6 with _ | ⟨t5, r7⟩
        · try rw [hp5] at hne
          dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
        · try rw [hp5] at hne; try rw [hp5]
          dsimp -failIfUnchanged only at hne ⊢
          rw [popLastTok_sound r6 t5 r7 hp5]
          rcases hm5 : matchRule5 t1 t2 t3 t4 t5 with _ | ⟨out, mode⟩
          · try rw [hm5] at hne
            dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
          · try rw [hm5] at hne; try rw [hm5]
            dsimp -failIfUnchanged only at hne ⊢
            exact stepCarryValid_of_stepStar (matchRule5_sound t1 t2 t3 t4 t5 out mode r7 _ hm5)
              (finishTurn_sound (pushToksLtr out r7) mode rStack k1 hne)
      · try rw [hm4] at hne; try rw [hm4]
        dsimp -failIfUnchanged only at hne ⊢
        exact stepCarryValid_of_stepStar (matchRule4_sound t1 t2 t3 t4 out mode r6 _ hm4)
          (finishTurn_sound (pushToksLtr out r6) mode rStack k1 hne)
  · try rw [hm3] at hne; try rw [hm3]
    dsimp -failIfUnchanged only at hne ⊢
    exact stepCarryValid_of_stepStar (matchRule3_sound t1 t2 t3 out mode r5 _ hm3)
      (finishTurn_sound (pushToksLtr out r5) mode rStack k1 hne)

def stepTurnFrom2 (t1 t2 : Tok) (r4 rStack : Rle) (k1 : Nat) : StepCarryRes :=
  Option.casesOn (matchRule2 t1 t2)
    (Option.casesOn (popLastTok r4) .err (fun p3 =>
      Prod.casesOn p3 (fun t3 r5 =>
        Bool.casesOn (tokEq t1 .T)
          (Bool.casesOn (tokEq t1 .U)
            (stepTurnFrom3 t1 t2 t3 r5 rStack k1)
            (Bool.casesOn (tokEq t2 .T)
              (stepTurnFrom3 t1 t2 t3 r5 rStack k1)
              (Bool.casesOn (tokEq t3 .Z)
                (stepTurnFrom3 t1 t2 t3 r5 rStack k1)
                .halt)))
          (Bool.casesOn (tokEq t2 .M)
            (stepTurnFrom3 t1 t2 t3 r5 rStack k1)
            (Bool.casesOn (tokEq t3 .U)
              (stepTurnFrom3 t1 t2 t3 r5 rStack k1)
              (Bool.casesOn (isEmptyRle r5)
                .err
                (finishTurn [([.Z], 1), ([.U], 1)] .R1 rStack k1)))))))
    (fun pm => Prod.casesOn pm (fun out mode => finishTurn (pushToksLtr out r4) mode rStack k1))

theorem stepTurnFrom2_sound (t1 t2 : Tok) (r4 rStack : Rle) (k1 : Nat)
    (hne : stepTurnFrom2 t1 t2 r4 rStack k1 ≠ .err) :
    StepCarryValid (carryCfg (tokL t1 +> (tokL t2 +> evalRle r4)) (evalRStack rStack (evalWK k1)))
      (stepTurnFrom2 t1 t2 r4 rStack k1) := by
  unfold stepTurnFrom2 at hne ⊢
  rcases hm2 : matchRule2 t1 t2 with _ | ⟨out, mode⟩
  · try rw [hm2] at hne; try rw [hm2]
    dsimp -failIfUnchanged only at hne ⊢
    rcases hp3 : popLastTok r4 with _ | ⟨t3, r5⟩
    · try rw [hp3] at hne
      dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
    · try rw [hp3] at hne; try rw [hp3]
      dsimp -failIfUnchanged only at hne ⊢
      rw [popLastTok_sound r4 t3 r5 hp3]
      cases ht1 : tokEq t1 .T
      · try rw [ht1] at hne; try rw [ht1]
        dsimp -failIfUnchanged only at hne ⊢
        cases hu1 : tokEq t1 .U
        · try rw [hu1] at hne; try rw [hu1]
          dsimp -failIfUnchanged only at hne ⊢
          exact stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne
        · try rw [hu1] at hne; try rw [hu1]
          dsimp -failIfUnchanged only at hne ⊢
          cases ht2 : tokEq t2 .T
          · try rw [ht2] at hne; try rw [ht2]
            dsimp -failIfUnchanged only at hne ⊢
            exact stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne
          · try rw [ht2] at hne; try rw [ht2]
            dsimp -failIfUnchanged only at hne ⊢
            cases hz3 : tokEq t3 .Z
            · try rw [hz3] at hne; try rw [hz3]
              dsimp -failIfUnchanged only at hne ⊢
              exact stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne
            · try rw [hz3] at hne; try rw [hz3]
              dsimp -failIfUnchanged only at hne ⊢
              rw [(tokEq_iff t1 .U).mp hu1, (tokEq_iff t2 .T).mp ht2, (tokEq_iff t3 .Z).mp hz3]
              exact ⟨_, ⟨_, turn_ZTU_halt (evalRle r5) (evalRStack rStack (evalWK k1))⟩, rfl⟩
      · try rw [ht1] at hne; try rw [ht1]
        dsimp -failIfUnchanged only at hne ⊢
        cases hm2' : tokEq t2 .M
        · try rw [hm2'] at hne; try rw [hm2']
          dsimp -failIfUnchanged only at hne ⊢
          exact stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne
        · try rw [hm2'] at hne; try rw [hm2']
          dsimp -failIfUnchanged only at hne ⊢
          cases hu3 : tokEq t3 .U
          · try rw [hu3] at hne; try rw [hu3]
            dsimp -failIfUnchanged only at hne ⊢
            exact stepTurnFrom3_sound t1 t2 t3 r5 rStack k1 hne
          · try rw [hu3] at hne; try rw [hu3]
            dsimp -failIfUnchanged only at hne ⊢
            cases he : isEmptyRle r5
            · try rw [he] at hne
              dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
            · try rw [he] at hne; try rw [he]
              dsimp -failIfUnchanged only at hne ⊢
              rw [(tokEq_iff t1 .T).mp ht1, (tokEq_iff t2 .M).mp hm2', (tokEq_iff t3 .U).mp hu3, (isEmptyRle_iff r5).mp he]
              refine stepCarryValid_of_stepStar ?_ (finishTurn_sound [([.Z], 1), ([.U], 1)] .R1 rStack k1 hne)
              simp only [evalRle_cons, evalRle_nil, pow_succ_list, pow_zero_list, List.append_nil,
                wordL_cons, wordL_nil, modeCfg_R1]
              exact ⟨_, turn_UMT (evalRStack rStack (evalWK k1))⟩
  · try rw [hm2] at hne; try rw [hm2]
    dsimp -failIfUnchanged only at hne ⊢
    exact stepCarryValid_of_stepStar (matchRule2_sound t1 t2 out mode r4 _ hm2)
      (finishTurn_sound (pushToksLtr out r4) mode rStack k1 hne)

def stepTurnaround (r2 rStack : Rle) (k1 : Nat) : StepCarryRes :=
  Option.casesOn (popLastTok r2) .err (fun p1 =>
    Prod.casesOn p1 (fun t1 r3 =>
      Option.casesOn (popLastTok r3) .err (fun p2 =>
        Prod.casesOn p2 (fun t2 r4 =>
          Bool.casesOn (tokEq t1 .M)
            (stepTurnFrom2 t1 t2 r4 rStack k1)
            (Bool.casesOn (tokEq t2 .U)
              (stepTurnFrom2 t1 t2 r4 rStack k1)
              (Bool.casesOn (isEmptyRle r4)
                .err
                (finishTurn [([.M], 1), ([.U], 1)] .R1 rStack k1)))))))

theorem stepTurnaround_sound (r2 rStack : Rle) (k1 : Nat)
    (hne : stepTurnaround r2 rStack k1 ≠ .err) :
    StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1)))
      (stepTurnaround r2 rStack k1) := by
  unfold stepTurnaround at hne ⊢
  rcases hp1 : popLastTok r2 with _ | ⟨t1, r3⟩
  · try rw [hp1] at hne
    dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
  · try rw [hp1] at hne; try rw [hp1]
    dsimp -failIfUnchanged only at hne ⊢
    rw [popLastTok_sound r2 t1 r3 hp1]
    rcases hp2 : popLastTok r3 with _ | ⟨t2, r4⟩
    · try rw [hp2] at hne
      dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
    · try rw [hp2] at hne; try rw [hp2]
      dsimp -failIfUnchanged only at hne ⊢
      rw [popLastTok_sound r3 t2 r4 hp2]
      cases hm1 : tokEq t1 .M
      · try rw [hm1] at hne; try rw [hm1]
        dsimp -failIfUnchanged only at hne ⊢
        exact stepTurnFrom2_sound t1 t2 r4 rStack k1 hne
      · try rw [hm1] at hne; try rw [hm1]
        dsimp -failIfUnchanged only at hne ⊢
        cases hu2 : tokEq t2 .U
        · try rw [hu2] at hne; try rw [hu2]
          dsimp -failIfUnchanged only at hne ⊢
          exact stepTurnFrom2_sound t1 t2 r4 rStack k1 hne
        · try rw [hu2] at hne; try rw [hu2]
          dsimp -failIfUnchanged only at hne ⊢
          cases he : isEmptyRle r4
          · try rw [he] at hne
            dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl
          · try rw [he] at hne; try rw [he]
            dsimp -failIfUnchanged only at hne ⊢
            rw [(tokEq_iff t1 .M).mp hm1, (tokEq_iff t2 .U).mp hu2, (isEmptyRle_iff r4).mp he]
            refine stepCarryValid_of_stepStar ?_ (finishTurn_sound [([.M], 1), ([.U], 1)] .R1 rStack k1 hne)
            simp only [evalRle_cons, evalRle_nil, pow_succ_list, pow_zero_list, List.append_nil,
              wordL_cons, wordL_nil, modeCfg_R1]
            exact ⟨_, turn_UM (evalRStack rStack (evalWK k1))⟩

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
  Option.casesOn (popLastTok r2) none (fun p1 =>
    Prod.casesOn p1 (fun t1 r2a =>
      Tok.casesOn t1
        (Option.casesOn (popTok .M r2a) none (fun rest =>
          Prod.casesOn (popTokCount 8 .P 0 rest) (fun mVal r3 =>
            Bool.casesOn (Nat.beq mVal 0)
              (Option.casesOn (popTok .Z r3) (some .err) (fun r4 =>
                strictNat (Nat.sub mVal 1) fun mm1 =>
                pushRleK [.Z] mm1 (pushToksLtr [.T, .W, .M] r4) fun r4a =>
                pushRlePosK [.P] 1 r4a fun r5 =>
                some (finishTurn r5 .R0 rStack k1)))
              none)))
        (Option.casesOn (popTok .T r2a) none (fun rest =>
          Prod.casesOn (popTokCount 8 .Z 0 rest) (fun b r3 =>
            Bool.casesOn (Nat.beq b 0)
              (pushRlePosK [.P] b (pushToksLtr [.T, .M] r3) fun r3' =>
                Option.casesOn (copyRStack r3' rStack) (some .err) (fun r4 =>
                  strictNat (Nat.add k1 (Nat.mul 2 b)) fun kOut => some (.next r4 kOut)))
              none)))
        (Option.casesOn (popTok .T r2a) none (fun rest =>
          Prod.casesOn (popTokCount 8 .Z 0 rest) (fun b r3 =>
            Bool.casesOn (Nat.beq b 0)
              (pushRlePosK [.Z] b (pushToksLtr [.T, .W] r3) fun r3' =>
                Option.casesOn (copyRStack r3' rStack) (some .err) (fun r4 =>
                  strictNat (Nat.add k1 (Nat.mul 2 b)) fun kOut => some (.next r4 kOut)))
              none)))
        none
        (Prod.casesOn (popTokCount 8 .P 0 r2a) (fun b r3 =>
          Bool.casesOn (Nat.beq b 0)
            (pushRlePosK [.T] 1 r3 fun r3a =>
              pushRlePosK [.P] b r3a fun r3' =>
              Option.casesOn (copyRStack r3' rStack) (some .err) (fun r4 =>
                strictNat (Nat.add k1 (Nat.mul 2 b)) fun kOut => some (.next r4 kOut)))
            none))
        none none))

theorem stepSpecialLoops_sound (r2 rStack : Rle) (k1 : Nat) (res : StepCarryRes)
    (h : stepSpecialLoops r2 rStack k1 = some res) (hne : res ≠ .err) :
    StepCarryValid (carryCfg (evalRle r2) (evalRStack rStack (evalWK k1))) res := by
  unfold stepSpecialLoops at h
  rcases hp1 : popLastTok r2 with _ | ⟨t1, r2a⟩
  · rw [hp1] at h; contradiction
  · rw [hp1] at h; dsimp -failIfUnchanged only at h
    rw [popLastTok_sound r2 t1 r2a hp1]
    cases t1 <;> try contradiction
    · -- .U
      dsimp -failIfUnchanged only at h
      rcases hpm : popTok .M r2a with _ | rest
      · rw [hpm] at h; contradiction
      · rw [hpm] at h; dsimp -failIfUnchanged only at h
        rw [popTok_sound .M r2a rest hpm]
        have hcnt := (popTokCount_sound 8 .P 0 rest).2
        rcases hpc : popTokCount 8 .P 0 rest with ⟨mVal, r3⟩
        rw [hpc] at h hcnt; dsimp -failIfUnchanged only at h hcnt
        simp only [pow_zero_list, listblank_append_nil] at hcnt
        cases hm0 : Nat.beq mVal 0
        · rw [hm0] at h; dsimp -failIfUnchanged only at h
          have hm_pos : mVal ≥ 1 := by
            have hne0 : mVal ≠ 0 := by
              intro h0; subst h0; revert hm0; decide
            omega
          rcases hpz : popTok .Z r3 with _ | r4
          · rw [hpz] at h; injection h with h'; subst h'; exfalso; exact hne rfl
          · rw [hpz] at h; simp only [strictNat_eq, pushRleK_eq, pushRlePosK_eq] at h
            injection h with h'; subst h'
            rw [hcnt, popTok_sound .Z r3 r4 hpz]
            refine stepCarryValid_of_stepStar
              ⟨_, carry_MU_to_pmuCfg (((tokL .P) ^ mVal) +> (tokL .Z +> evalRle r4)) (evalRStack rStack (evalWK k1))⟩ ?_
            refine stepCarryValid_of_stepStar
              (pmu_loop mVal (tokL .Z +> evalRle r4) (tokR .P +> evalRStack rStack (evalWK k1))) ?_
            have hm1 : mVal = 1 + (mVal - 1) := by omega
            rw [hm1, list_pow_add, pow_succ_list, pow_zero_list, List.append_nil, listblank_append_assoc]
            refine stepCarryValid_of_stepStar
              ⟨_, pmuCfg_Z_turn (evalRle r4) (((tokR .Z) ^ (mVal - 1)) +> (tokR .P +> evalRStack rStack (evalWK k1)))⟩ ?_
            refine stepCarryValid_of_stepStar
              (r0_Z_loop (mVal - 1) (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4))) (tokR .P +> evalRStack rStack (evalWK k1))) ?_
            refine stepCarryValid_of_stepStar
              ⟨_, r0_P (((tokL .Z) ^ (mVal - 1)) +> (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4)))) (evalRStack rStack (evalWK k1))⟩ ?_
            have hr5 : tokL .P +> (((tokL .Z) ^ (mVal - 1)) +> (tokL .M +> (tokL .W +> (tokL .T +> evalRle r4)))) =
                evalRle (pushRlePos [.P] 1 (pushRle [.Z] (Nat.sub mVal 1) (pushToksLtr [.T, .W, .M] r4))) := by
              simp [pow_succ_list, pow_zero_list]
            rw [← hm1, hr5]
            exact finishTurn_sound _ .R0 rStack k1 hne
        · rw [hm0] at h; contradiction
    · -- .M
      dsimp -failIfUnchanged only at h
      rcases hpt : popTok .T r2a with _ | rest
      · rw [hpt] at h; contradiction
      · rw [hpt] at h; dsimp -failIfUnchanged only at h
        rw [popTok_sound .T r2a rest hpt]
        have hcnt := (popTokCount_sound 8 .Z 0 rest).2
        rcases hpc : popTokCount 8 .Z 0 rest with ⟨b, r3⟩
        rw [hpc] at h hcnt; dsimp -failIfUnchanged only at h hcnt
        simp only [pow_zero_list, listblank_append_nil] at hcnt
        cases hb0 : Nat.beq b 0
        · rw [hb0] at h; simp only [pushRlePosK_eq] at h
          have hb_pos : b ≥ 1 := by
            have hne0 : b ≠ 0 := by
              intro h0; subst h0; revert hb0; decide
            omega
          rcases hc : copyRStack (pushRlePos [.P] b (pushToksLtr [.T, .M] r3)) rStack with _ | r4
          · rw [hc] at h; injection h with h'; subst h'; exfalso; exact hne rfl
          · rw [hc] at h; simp only [strictNat_eq] at h
            injection h with h'; subst h'
            rcases copyRStack_sound rStack (pushRlePos [.P] b (pushToksLtr [.T, .M] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
            have hb1 : b = (b - 1) + 1 := by omega
            have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
            rw [hcnt, hb1]
            refine stepStar_trans (special_ZTM_loop (b - 1) (evalRle r3) hR k1) ?_
            rw [← hb1]
            simp only [evalRle_pushRlePos, evalRle_pushToksLtr, revWord_cons, revWord_nil,
              List.nil_append, List.cons_append, wordL_cons, wordL_nil, List.append_nil,
              listblank_append_assoc] at hcopy
            refine stepStar_trans hcopy ?_
            have hadd : k1 + 2 * (b - 1) + 2 = Nat.add k1 (Nat.mul 2 b) := by
              change k1 + 2 * (b - 1) + 2 = k1 + 2 * b
              omega
            rw [← hadd]
            exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
        · rw [hb0] at h; contradiction
    · -- .W
      dsimp -failIfUnchanged only at h
      rcases hpt : popTok .T r2a with _ | rest
      · rw [hpt] at h; contradiction
      · rw [hpt] at h; dsimp -failIfUnchanged only at h
        rw [popTok_sound .T r2a rest hpt]
        have hcnt := (popTokCount_sound 8 .Z 0 rest).2
        rcases hpc : popTokCount 8 .Z 0 rest with ⟨b, r3⟩
        rw [hpc] at h hcnt; dsimp -failIfUnchanged only at h hcnt
        simp only [pow_zero_list, listblank_append_nil] at hcnt
        cases hb0 : Nat.beq b 0
        · rw [hb0] at h; simp only [pushRlePosK_eq] at h
          have hb_pos : b ≥ 1 := by
            have hne0 : b ≠ 0 := by
              intro h0; subst h0; revert hb0; decide
            omega
          rcases hc : copyRStack (pushRlePos [.Z] b (pushToksLtr [.T, .W] r3)) rStack with _ | r4
          · rw [hc] at h; injection h with h'; subst h'; exfalso; exact hne rfl
          · rw [hc] at h; simp only [strictNat_eq] at h
            injection h with h'; subst h'
            rcases copyRStack_sound rStack (pushRlePos [.Z] b (pushToksLtr [.T, .W] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
            have hb1 : b = (b - 1) + 1 := by omega
            have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
            rw [hcnt, hb1]
            refine stepStar_trans (special_ZTW_loop (b - 1) (evalRle r3) hR k1) ?_
            rw [← hb1]
            simp only [evalRle_pushRlePos, evalRle_pushToksLtr, revWord_cons, revWord_nil,
              List.nil_append, List.cons_append, wordL_cons, wordL_nil, List.append_nil,
              listblank_append_assoc] at hcopy
            refine stepStar_trans hcopy ?_
            have hadd : k1 + 2 * (b - 1) + 2 = Nat.add k1 (Nat.mul 2 b) := by
              change k1 + 2 * (b - 1) + 2 = k1 + 2 * b
              omega
            rw [← hadd]
            exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
        · rw [hb0] at h; contradiction
    · -- .T
      dsimp -failIfUnchanged only at h
      have hcnt := (popTokCount_sound 8 .P 0 r2a).2
      rcases hpc : popTokCount 8 .P 0 r2a with ⟨b, r3⟩
      rw [hpc] at h hcnt; dsimp -failIfUnchanged only at h hcnt
      simp only [pow_zero_list, listblank_append_nil] at hcnt
      cases hb0 : Nat.beq b 0
      · rw [hb0] at h; simp only [pushRlePosK_eq] at h
        have hb_pos : b ≥ 1 := by
          have hne0 : b ≠ 0 := by
            intro h0; subst h0; revert hb0; decide
          omega
        rcases hc : copyRStack (pushRlePos [.P] b (pushRlePos [.T] 1 r3)) rStack with _ | r4
        · rw [hc] at h; injection h with h'; subst h'; exfalso; exact hne rfl
        · rw [hc] at h; simp only [strictNat_eq] at h
          injection h with h'; subst h'
          rcases copyRStack_sound rStack (pushRlePos [.P] b (pushRlePos [.T] 1 r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
          have hb1 : b = (b - 1) + 1 := by omega
          have hR := hasRoundtrip_stack rStack hrs hasRoundtrip_evalWK
          rw [hcnt, hb1]
          refine stepStar_trans (special_PT_loop (b - 1) (evalRle r3) hR k1) ?_
          rw [← hb1]
          simp only [evalRle_pushRlePos, pow_succ_list, pow_zero_list, wordL_cons, wordL_nil,
            List.append_nil] at hcopy
          refine stepStar_trans hcopy ?_
          have hadd : k1 + 2 * (b - 1) + 2 = Nat.add k1 (Nat.mul 2 b) := by
            change k1 + 2 * (b - 1) + 2 = k1 + 2 * b
            omega
          rw [← hadd]
          exact r0_end (k1 + 2 * (b - 1)) (evalRle r4)
      · rw [hb0] at h; contradiction

def stepCarry (rle : Rle) (k1 : Nat) : StepCarryRes :=
  Prod.casesOn (popCarryLoop 80 rle []) (fun r2 rStack =>
    Bool.casesOn (hasSpecial rStack)
      (Option.casesOn (stepSpecialLoops r2 rStack k1)
        (stepTurnaround r2 rStack k1)
        (fun res => res))
      (stepTurnaround r2 rStack k1))

theorem stepCarry_sound (rle : Rle) (k1 : Nat) (hne : stepCarry rle k1 ≠ .err) :
    StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (stepCarry rle k1) := by
  have hp := popCarryLoop_sound 80 rle [] (evalWK k1)
  simp only [evalRStack_nil] at hp
  unfold stepCarry at hne ⊢
  rcases hpop : popCarryLoop 80 rle [] with ⟨r2, rStack⟩
  try rw [hpop] at hp; try rw [hpop] at hne; try rw [hpop]
  dsimp -failIfUnchanged only at hp hne ⊢
  refine stepCarryValid_of_stepStar hp ?_
  cases hns : hasSpecial rStack
  · try rw [hns] at hne; try rw [hns]
    dsimp -failIfUnchanged only at hne ⊢
    rcases hsl : stepSpecialLoops r2 rStack k1 with _ | res
    · try rw [hsl] at hne; try rw [hsl]
      dsimp -failIfUnchanged only at hne ⊢
      exact stepTurnaround_sound r2 rStack k1 hne
    · try rw [hsl] at hne; try rw [hsl]
      dsimp -failIfUnchanged only at hne ⊢
      exact stepSpecialLoops_sound r2 rStack k1 res hsl hne
  · try rw [hns] at hne; try rw [hns]
    dsimp -failIfUnchanged only at hne ⊢
    exact stepTurnaround_sound r2 rStack k1 hne

def runCarryChunk (n : Nat) (rle : Rle) (k1 : Nat) : StepCarryRes :=
  Nat.rec
    (fun rle k1 => .next rle k1)
    (fun _ ih rle k1 =>
      StepCarryRes.casesOn (stepCarry rle k1)
        .halt
        (fun rle' k1' => ih rle' k1')
        .err)
    n rle k1

theorem runCarryChunk_succ (n : Nat) (rle : Rle) (k1 : Nat) :
    runCarryChunk (n + 1) rle k1 =
      StepCarryRes.casesOn (stepCarry rle k1)
        .halt
        (fun rle' k1' => runCarryChunk n rle' k1')
        .err := rfl

theorem runCarryChunk_sound : ∀ (n : Nat) (rle : Rle) (k1 : Nat),
    runCarryChunk n rle k1 ≠ .err →
    StepCarryValid (carryCfg (evalRle rle) (evalWK k1)) (runCarryChunk n rle k1)
  | 0, rle, k1, _ => stepStar_refl _ _
  | n + 1, rle, k1, hne => by
    rw [runCarryChunk_succ] at hne ⊢
    cases hs : stepCarry rle k1 with
    | halt =>
      try rw [hs]
      dsimp -failIfUnchanged only
      have hv := stepCarry_sound rle k1 (by rw [hs]; nofun)
      rwa [hs] at hv
    | next rle' k1' =>
      try rw [hs] at hne; try rw [hs]
      dsimp -failIfUnchanged only at hne ⊢
      have hv := stepCarry_sound rle k1 (by rw [hs]; nofun)
      rw [hs] at hv
      exact stepCarryValid_of_stepStar hv (runCarryChunk_sound n rle' k1' hne)
    | err =>
      try rw [hs] at hne
      dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl

def runCarryChunks (chunks chunkSize : Nat) (rle : Rle) (k1 : Nat) : Bool :=
  Nat.rec
    (fun _ _ => false)
    (fun _ ih rle k1 =>
      StepCarryRes.casesOn (runCarryChunk chunkSize rle k1)
        true
        (fun rle' k1' => ih rle' k1')
        false)
    chunks rle k1

theorem runCarryChunks_succ (chunks chunkSize : Nat) (rle : Rle) (k1 : Nat) :
    runCarryChunks (chunks + 1) chunkSize rle k1 =
      StepCarryRes.casesOn (runCarryChunk chunkSize rle k1)
        true
        (fun rle' k1' => runCarryChunks chunks chunkSize rle' k1')
        false := rfl

theorem runCarryChunks_sound : ∀ (chunks chunkSize : Nat) (rle : Rle) (k1 : Nat),
    runCarryChunks chunks chunkSize rle k1 = true →
    ∃ cfg', ((carryCfg (evalRle rle) (evalWK k1)) [target_tm]⊢* cfg') ∧
      (step target_tm cfg').isNone
  | 0, _, _, _, h => by nomatch h
  | chunks + 1, chunkSize, rle, k1, h => by
    rw [runCarryChunks_succ] at h
    cases hc : runCarryChunk chunkSize rle k1 with
    | halt =>
      have hv := runCarryChunk_sound chunkSize rle k1 (by rw [hc]; nofun)
      rwa [hc] at hv
    | next rle' k1' =>
      rw [hc] at h; dsimp -failIfUnchanged only at h
      have hv := runCarryChunk_sound chunkSize rle k1 (by rw [hc]; nofun)
      rw [hc] at hv
      rcases runCarryChunks_sound chunks chunkSize rle' k1' h with ⟨cfg', h2, hnone⟩
      exact ⟨cfg', stepStar_trans hv h2, hnone⟩
    | err =>
      rw [hc] at h; nomatch h

theorem init_to_initRle :
    (init []) [target_tm]⊢* (carryCfg (evalRle initRle) (evalWK 1)) := by
  exact ⟨2049, init_to_carry0⟩

end Solution

open Solution

-- ============================================================================
-- Section 7: Final Halting Theorem (`proved_is_halt`)
-- ============================================================================
macro "fast_rfl" : tactic => `(tactic| exact rfl)
set_option maxHeartbeats 400000000 in
theorem runCarryChunks_28_500 : runCarryChunks 28 500 initRle 1 = true := by fast_rfl

/--
Halting theorem for Suspect 154 (Holdout #305):
The machine halts when started on the blank tape.
-/

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := by
  rcases runCarryChunks_sound 28 500 initRle 1 runCarryChunks_28_500 with ⟨cfg', hstep, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_initRle hstep, hnone⟩

end BusyBeaver.M_1RB1LA_0LB1LC_1RD0LD_0LA0RE_1RC1RF_0LDHHH
