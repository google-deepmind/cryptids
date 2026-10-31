/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_---1LC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 1 Dir.left)

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

def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

set_option maxRecDepth 200000
set_option maxHeartbeats 20000000

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

def evalRleG (l_end : ListBlank (Fin 2)) : Rle → ListBlank (Fin 2)
  | [] => l_end
  | (w, c) :: rest => ((wordL w) ^ c) +> evalRleG l_end rest

variable {l_end : ListBlank (Fin 2)}
local notation "evalRle" => evalRleG l_end

def evalRStack : Rle → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r_end => r_end
  | (w, c) :: rest, r_end => ((wordR (revWord w)) ^ c) +> evalRStack rest r_end

@[simp] lemma evalRle_nil : evalRle [] = l_end := rfl
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
    (init []) [target_tm]⊢^{349} (carryCfg (tokL .M +> (tokL .U +> default)) (evalWK 1)) :=
  bmultiStep_sound 349 ⟨A, 0, [], []⟩
    ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl

theorem carry_Z (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .Z +> l) r) [target_tm]⊢^{54} (carryCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 54 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_P (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .P +> l) r) [target_tm]⊢^{18} (carryCfg l (tokR .P +> r)) :=
  wmultiStep_sound 18 ⟨B, 1, [0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .P +> l))))) r) [target_tm]⊢^{78} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 78 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (((tokL .T) ^ 2) +> (tokL .P +> l))) r) [target_tm]⊢^{120} (carryCfg l (((tokR .Z) ^ 3) +> r)) :=
  wmultiStep_sound 120 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTT (l r : ListBlank (Fin 2)) :
    (carryCfg (((tokL .T) ^ 3) +> (tokL .P +> l)) r) [target_tm]⊢^{84} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .P +> r))) :=
  wmultiStep_sound 84 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (((tokL .T) ^ 3) +> (tokL .P +> l))) r) [target_tm]⊢^{99} (carryCfg l (((tokR .Z) ^ 2) +> (tokR .PTTTM_TAIL +> r))) :=
  wmultiStep_sound 99 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem turn_UM (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .U +> default)) r) [target_tm]⊢^{61} (r1Cfg (tokL .M +> (tokL .U +> default)) r) :=
  cmultiStep_sound 61 ⟨B, 1, [0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_UMT (r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .M +> (tokL .U +> default))) r) [target_tm]⊢^{97} (r1Cfg (tokL .Z +> (tokL .U +> default)) r) :=
  cmultiStep_sound 97 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], []⟩ r rfl

theorem turn_ZT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{61} (r1Cfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 61 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_WM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .W +> l)) r) [target_tm]⊢^{55} (r1Cfg (tokL .T +> l) r) :=
  wmultiStep_sound 55 ⟨B, 1, [0, 1, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .P +> l)) r) [target_tm]⊢^{115} (r0Cfg (tokL .P +> (tokL .T +> l)) r) :=
  wmultiStep_sound 115 ⟨B, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .Z +> l)) r) [target_tm]⊢^{55} (r1Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 55 ⟨B, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{141} (r1OddCfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 141 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_PTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{97} (r1Cfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 97 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{103} (r1Cfg (tokL .Z +> (tokL .U +> (tokL .M +> l))) r) :=
  wmultiStep_sound 103 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .Z +> l))) r) [target_tm]⊢^{111} (r1OddCfg (tokL .T +> (tokL .T +> l)) r) :=
  wmultiStep_sound 111 ⟨B, 1, [0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{121} (r0Cfg (tokL .P +> (tokL .M +> (tokL .T +> l))) r) :=
  wmultiStep_sound 121 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{127} (r0Cfg (tokL .P +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 127 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{127} (r0Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 127 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_MUTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .U +> (tokL .M +> l)))) r) [target_tm]⊢^{141} (r1OddCfg (tokL .Z +> (tokL .T +> l)) r) :=
  wmultiStep_sound 141 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_PTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .P +> l)))) r) [target_tm]⊢^{163} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .U +> (tokL .M +> l)))) r) :=
  wmultiStep_sound 163 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{163} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 163 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{109} (r1Cfg (tokL .Z +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 109 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZPMU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> (tokL .P +> (tokL .Z +> l)))) r) [target_tm]⊢^{163} (r0Cfg (tokL .P +> (tokL .M +> (tokL .W +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 163 ⟨B, 1, [0, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem turn_ZMUTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .U +> (tokL .M +> (tokL .Z +> l))))) r) [target_tm]⊢^{157} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 157 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_PTTTW (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .W +> (tokL .T +> (tokL .T +> (tokL .T +> (tokL .P +> l))))) r) [target_tm]⊢^{205} (r0Cfg (tokL .Z +> (tokL .Z +> (tokL .Z +> (tokL .T +> l)))) r) :=
  wmultiStep_sound 205 ⟨B, 1, [0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem carry_MU_to_pmuCfg (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .M +> l)) r) [target_tm]⊢^{17} (pmuCfg l (tokR .P +> r)) :=
  wmultiStep_sound 17 ⟨B, 1, [0, 1, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmu_step (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .P +> l) r) [target_tm]⊢^{60} (pmuCfg l (tokR .Z +> r)) :=
  wmultiStep_sound 60 ⟨D, 1, [0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨D, 1, [], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmuCfg_Z_turn (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{38} (r0Cfg (tokL .M +> (tokL .W +> (tokL .T +> l))) r) :=
  wmultiStep_sound 38 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem pmuCfg_M_to_carry (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .M +> l) r) [target_tm]⊢^{7} (carryCfg (tokL .U +> l) r) :=
  wmultiStep_sound 7 ⟨D, 1, [0, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem pmuCfg_T_to_carry (l r : ListBlank (Fin 2)) :
    (pmuCfg (tokL .T +> l) r) [target_tm]⊢^{7} (carryCfg (tokL .M +> l) r) :=
  wmultiStep_sound 7 ⟨D, 1, [0, 1, 1, 1], [1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem carry_PTU (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .T +> (tokL .P +> l))) r) [target_tm]⊢^{30} (carryCfg (tokL .Z +> l) (tokR .P +> r)) :=
  wmultiStep_sound 30 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem turn_PTMT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .M +> (tokL .T +> (tokL .P +> l)))) r) [target_tm]⊢^{163} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .U +> (tokL .M +> l)))) r) :=
  wmultiStep_sound 163 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTT (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .T +> (tokL .T +> (tokL .T +> (tokL .Z +> l)))) r) [target_tm]⊢^{163} (r0Cfg (tokL .P +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 163 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTTTM (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .M +> (tokL .T +> (tokL .T +> (tokL .T +> (tokL .Z +> l))))) r) [target_tm]⊢^{145} (r1Cfg (tokL .Z +> (tokL .Z +> (tokL .P +> l))) r) :=
  wmultiStep_sound 145 ⟨B, 1, [0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem turn_ZTU_halt (l r : ListBlank (Fin 2)) :
    (carryCfg (tokL .U +> (tokL .T +> (tokL .Z +> l))) r) [target_tm]⊢^{33} (⟨some F, ⟨0, [1, 1, 0, 1, 1, 0, 1, 1, 1] +> l, [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1] +> r⟩⟩) :=
  wmultiStep_sound 33 ⟨B, 1, [0, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1]⟩
    ⟨F, 0, [1, 1, 0, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1]⟩ l r rfl

theorem r0_Z (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .Z +> r)) [target_tm]⊢^{12} (r0Cfg (tokL .Z +> l) r) :=
  wmultiStep_sound 12 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], []⟩ l r rfl

theorem r0_P (l r : ListBlank (Fin 2)) :
    (r0Cfg l (tokR .P +> r)) [target_tm]⊢^{48} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 48 ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
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
    (r1Cfg l (tokR .P +> r)) [target_tm]⊢^{68} (r1OddCfg (tokL .P +> l) r) :=
  wmultiStep_sound 68 ⟨E, 0, [0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [0, 0, 1, 1, 0, 1]⟩
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
    (wSweepCfg (tokL .W +> l) r) [target_tm]⊢^{6} (wSweepCfg l ([0, 0, 1, 1] +> r)) :=
  wmultiStep_sound 6 ⟨D, 1, [0, 0, 1, 1], [1]⟩
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
    (tSweepCfg l ([0, 0, 1, 1] +> r)) [target_tm]⊢^{24} (tSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 24 ⟨E, 0, [0, 0, 0, 0, 1, 1], [0, 0, 1, 1]⟩
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
    (wSweepCfg (tokL .Z +> l) r) [target_tm]⊢^{11} (dSweepCfg (tokL .T +> l) r) :=
  wmultiStep_sound 11 ⟨D, 1, [0, 0, 0, 0, 1, 1], [1]⟩
    ⟨E, 1, [0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem wSweep_ZT_to_dSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .Z +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{53} (dSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 53 ⟨D, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 1, [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem wSweep_PT_to_carry (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .P +> l)) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{40} (carryCfg l ([1, 0, 1, 1] +> r)) :=
  wmultiStep_sound 40 ⟨D, 1, [0, 1, 1, 1, 0, 1, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1]⟩ l r rfl

theorem wSweep_ZMT_to_tSweep (l r : ListBlank (Fin 2)) :
    (wSweepCfg (tokL .T +> (tokL .M +> (tokL .Z +> l))) ([0, 0, 1, 1] +> r)) [target_tm]⊢^{77} (tSweepCfg (tokL .Z +> (tokL .P +> l)) r) :=
  wmultiStep_sound 77 ⟨D, 1, [0, 1, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 0, 1, 1]⟩
    ⟨E, 0, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem cfgR_Z_to_TW (l : ListBlank (Fin 2)) :
    (cfgR (tokL .Z +> l)) [target_tm]⊢^{18} (cfgR (tokL .W +> (tokL .T +> l))) :=
  rcmultiStep_sound 18 ⟨B, 0, [1, 1, 0, 0, 0, 0, 1, 1], []⟩
    ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩ l rfl

theorem cfgR_TW_to_t3Cfg (l : ListBlank (Fin 2)) :
    (cfgR (tokL .W +> (tokL .T +> l))) [target_tm]⊢^{30} (t3Cfg l (evalWK 0)) :=
  rcmultiStep_sound 30 ⟨B, 0, [1, 1, 0, 0, 1, 1, 0, 1, 1, 1], []⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩ l rfl

theorem t3_step (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 3) +> l) r) [target_tm]⊢^{66} (t3Cfg l (((tokR .Z) ^ 2) +> r)) :=
  wmultiStep_sound 66 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩ l r rfl

theorem t3Cfg_Z_zero_to_carry (l : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (evalWK 0)) [target_tm]⊢^{120} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 120 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_Z_succ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .Z +> l) (tokR .Z +> r)) [target_tm]⊢^{37} (r0Cfg (tokL .P +> l) r) :=
  wmultiStep_sound 37 ⟨B, 1, [0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1]⟩
    ⟨E, 0, [0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1], []⟩ l r rfl

theorem t3Cfg_TZ_to_r1OddShort (l r : ListBlank (Fin 2)) :
    (t3Cfg (tokL .T +> (tokL .Z +> l)) r) [target_tm]⊢^{51} (r1OddShortCfg (tokL .M +> (tokL .T +> l)) r) :=
  wmultiStep_sound 51 ⟨B, 1, [0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
    ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], []⟩ l r rfl

theorem r1OddShortCfg_evalWK0_to_carry (l : ListBlank (Fin 2)) :
    (r1OddShortCfg l (evalWK 0)) [target_tm]⊢^{180} (carryCfg l (evalWK 1)) :=
  rcmultiStep_sound 180 ⟨B, 1, [1, 1, 0, 0, 0, 0, 1, 1], [1, 0, 1, 1]⟩
    ⟨B, 1, [], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ l rfl

theorem t3Cfg_TTZ_to_r0 (l r : ListBlank (Fin 2)) :
    (t3Cfg (((tokL .T) ^ 2) +> (tokL .Z +> l)) r) [target_tm]⊢^{79} (r0Cfg (tokL .W +> (tokL .T +> l)) r) :=
  wmultiStep_sound 79 ⟨B, 1, [0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1], [0, 1, 0, 0, 1]⟩
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
          have hpcs := (popTokCount_sound (l_end := l_end) 8 .P 0 r2).2
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
        have hsw_sound := sweepStarLoop_sound (l_end := l_end) rStack rle (Bool.casesOn (modeEq mode .R1) true false) 0 hall hasRoundtrip_evalWK k1
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
          have hzt := stepZtToCarry_sound (l_end := l_end) (pushRlePos [.P] 1 rle1) (k1 + 2 * totalRes + 1)
          rw [evalRle_pushRlePos_one] at hzt
          exact hzt
        · simp only [strictNat_eq, pushRlePosK_eq, nat_add_eq, nat_mul_eq, Option.some.injEq] at h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          dsimp -failIfUnchanged only at h1 h2
          rw [← h1, ← h2]
          simp only [r1PhaseCfg_true]
          refine stepStar_trans (r1Odd_end (k1 + 2 * totalRes) (evalRle rle1)) ?_
          have hzt := stepZtToCarry_sound (l_end := l_end) (pushRlePos [.Z] 1 rle1) (k1 + 2 * totalRes)
          rw [evalRle_pushRlePos_one] at hzt
          exact hzt
    · rw [hm] at h; dsimp -failIfUnchanged only at h
      rcases hc : copyRStack rle rStack with _ | rle'
      · rw [hc] at h; contradiction
      · rw [hc] at h; simp only [strictNat_eq, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rw [(modeEq_iff mode .R0).mp hm, modeCfg_R0]
        refine stepStar_trans (copyRStack_sound (l_end := l_end) rStack rle rle' (evalWK k1) hc).2 ?_
        exact r0_end k1 (evalRle rle')
  · rw [hs] at h; dsimp -failIfUnchanged only at h
    exact simpleOneBounceCarry_sound rStack rle rOut mode k1 kOut h

inductive StepCarryRes
  | halt
  | next (rle : Rle) (k1 : Nat)
  | err
  deriving DecidableEq, Repr

def StepCarryValidG (l_end_p : ListBlank (Fin 2)) (cfg : Cfg (Fin 2) (Fin 6)) : StepCarryRes → Prop
  | .halt => ∃ cfg', (cfg [target_tm]⊢* cfg') ∧ (step target_tm cfg').isNone
  | .next rOut kOut => cfg [target_tm]⊢* carryCfg (evalRleG l_end_p rOut) (evalWK kOut)
  | .err => False

local notation "StepCarryValid" => StepCarryValidG l_end

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
              .err)))))
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
            exfalso; exact hne rfl
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
              .err)))))

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
        have hcnt := (popTokCount_sound (l_end := l_end) 8 .P 0 rest).2
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
        have hcnt := (popTokCount_sound (l_end := l_end) 8 .Z 0 rest).2
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
            rcases copyRStack_sound (l_end := l_end) rStack (pushRlePos [.P] b (pushToksLtr [.T, .M] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
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
        have hcnt := (popTokCount_sound (l_end := l_end) 8 .Z 0 rest).2
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
            rcases copyRStack_sound (l_end := l_end) rStack (pushRlePos [.Z] b (pushToksLtr [.T, .W] r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
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
      have hcnt := (popTokCount_sound (l_end := l_end) 8 .P 0 r2a).2
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
          rcases copyRStack_sound (l_end := l_end) rStack (pushRlePos [.P] b (pushRlePos [.T] 1 r3)) r4 (evalWK (k1 + 2 * (b - 1))) hc with ⟨hrs, hcopy⟩
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
  have hp := popCarryLoop_sound (l_end := l_end) 80 rle [] (evalWK k1)
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
      have hv := stepCarry_sound (l_end := l_end) rle k1 (by rw [hs]; nofun)
      rwa [hs] at hv
    | next rle' k1' =>
      try rw [hs] at hne; try rw [hs]
      dsimp -failIfUnchanged only at hne ⊢
      have hv := stepCarry_sound (l_end := l_end) rle k1 (by rw [hs]; nofun)
      rw [hs] at hv
      exact stepCarryValid_of_stepStar hv (runCarryChunk_sound n rle' k1' hne)
    | err =>
      try rw [hs] at hne
      dsimp -failIfUnchanged only at hne; exfalso; exact hne rfl

def takeRle : Nat → Rle → Rle
  | 0, _ => []
  | n + 1, [] => []
  | n + 1, h :: t => h :: takeRle n t

def dropRle : Nat → Rle → Rle
  | 0, rle => rle
  | n + 1, [] => []
  | n + 1, _ :: t => dropRle n t

def truncRes (k : Nat) : StepCarryRes → StepCarryRes
  | .halt => .halt
  | .next rle k1 => .next (takeRle k rle) k1
  | .err => .err

theorem evalRleG_take_drop : ∀ (k : Nat) (rle : Rle) (l_end : ListBlank (Fin 2)),
    evalRleG l_end rle = evalRleG (evalRleG l_end (dropRle k rle)) (takeRle k rle)
  | 0, _, _ => rfl
  | k + 1, [], _ => rfl
  | k + 1, (w, c) :: t, l_end => by
    dsimp -failIfUnchanged only [evalRleG, takeRle, dropRle]
    rw [evalRleG_take_drop k t l_end]

theorem runCarryChunk_trunc_sound (n k : Nat) (rle rle' : Rle) (k1 k1' : Nat)
    (l_end : ListBlank (Fin 2))
    (h : truncRes k (runCarryChunk n rle k1) = .next rle' k1') :
    ∃ l_end', (carryCfg (evalRleG l_end rle) (evalWK k1)) [target_tm]⊢*
      (carryCfg (evalRleG l_end' rle') (evalWK k1')) := by
  have hne : runCarryChunk n rle k1 ≠ .err := by
    intro herr; rw [herr] at h; nomatch h
  have hv := runCarryChunk_sound (l_end := l_end) n rle k1 hne
  cases hrc : runCarryChunk n rle k1 with
  | halt => rw [hrc] at h; nomatch h
  | err => rw [hrc] at h; nomatch h
  | next rOut kOut =>
    rw [hrc] at hv h
    injection h with hr hk
    subst hr hk
    refine ⟨evalRleG l_end (dropRle k rOut), ?_⟩
    rw [← evalRleG_take_drop k rOut l_end]
    exact hv

theorem runCarryChunk_halt_sound (n : Nat) (rle : Rle) (k1 : Nat)
    (l_end : ListBlank (Fin 2))
    (h : runCarryChunk n rle k1 = .halt) :
    ∃ cfg', ((carryCfg (evalRleG l_end rle) (evalWK k1)) [target_tm]⊢* cfg') ∧
      (step target_tm cfg').isNone := by
  have hv := runCarryChunk_sound (l_end := l_end) n rle k1 (by rw [h]; nofun)
  rwa [h] at hv

end Solution

open Solution

set_option maxRecDepth 4000000
set_option maxHeartbeats 400000000

def ckptRle_0 : Rle := [([.Z], 6), ([.M], 1), ([.T], 1), ([.Z], 4), ([.P], 5), ([.Z], 1), ([.U], 1)]
def ckptK1_0 : Nat := 1

def ckptRle_1 : Rle := [([.Z], 2687347732367451952937656788591856444298439349414275365834221195969332993467316451686557022780597629902603946681348780194999994611346943798769796745674299962812486660507874859665600438768473774501368376613149872201460600715884481448680580106675590365243410717940439954917244208832180861485655214667225003440655147745204689584411699852289877905539360922842), ([.M], 1), ([.T], 1), ([.P], 941867465382926951635754360578740586877574476111732845465925424262170004441271075597581242438436299778336548201952880610015363096931916306576162569800076651699955076605002853350391407744227072142563055808139591990534360737097935961383843986538913584849580375304723029062723705897007911818208917624898047469089718404717234501847838735608029891069495162327), ([.Z], 1), ([.P, .Z], 353200299518597606863407885217027720079090428541899817049722034098313751665476653349092965914413612416876205575732330228755761161349468614966060963675028744387483153726876070006396777904085152053461145928052346996450385276411725985518941494952092594318592640739271135898521389711377966931828344109336767800908644401768962938192939525853011209151060685873), ([.Z], 1), ([.P], 367242734855466799340672460431096306188074178865174044810296404518202237328262956469150592818184697814864000657594044078723110538879354312569063062105590831634443611322151151386015365523957954626540934795618118167660319246991973154088708103563594000445792381672064665328166671304371800432375805156847169509584353600648356810075057101903356119782904158058), ([.T], 2), ([.Z], 275432051141600099505504345323322229641055634148880533607722303388651677996197217351862944613638523361148000493195533059042332904159515734426797296579193123725832708491613363539511524142968465969905701096713588625745239435243979865566531077672695500334344286254048498996125003478278850324281853867635377132188265200486267607556292826427517089837178118546), ([.P], 1), ([.Z, .P], 81278857211214805477219683697222636965280731973837840382143323314634195084976011777244428026717860405225153853002225632205265601572424304940014191703476142473390559634081476811789900666084886726825392048230201163507629333812807912094852069432272445516048289718421019259807706631347574982683355503578991095889306501002543798607176093438080346971843435373), ([.M], 1), ([.T], 1), ([.Z], 121918285816822208215829525545833955447921097960756760573214984971951292627464017665866642040076790607837730779503338448307898402358636457410021287555214213710085839451122215217684850999127330090238088072345301745261444000719211868142278104148408668274072434577631528889711559947021362474025033255368486643833959751503815697910764140157120520457765153062), ([.P], 1), ([.Z, .P], 22008161966885231837344445799023199150115130831992359720752540456110184163597944729704176203396585855205346331946099264935609237487394095470034794513721278923796706050273534515526920887528288011889245863037394571146835454403684537492597084694988367109330817626847167863739169673006993888922339696784275328681292949179806554226433716472238561717098359079), ([.M], 1), ([.T], 1), ([.Z], 58688431911693951566251855464061864400307015551979625922006774549627157769594519279211136542390895613880923551856264706494957966633050921253426118703256743796791216134062758708071789033408768031704655634766385523058227878409825433313592225853302312291548847004925780969971119128018650370459572524758067543150114531146150811270489910592636164578928957548), ([.P, .P], 1), ([.Z, .Z, .P, .P], 11004080983442615918672222899511599575057565415996179860376270228055092081798972364852088101698292927602673165973049632467804618743697047735017397256860639461898353025136767257763460443764144005944622931518697285573417727201842268746298542347494183554665408813423583931869584836503496944461169848392137664340646474589903277113216858236119280858549179540), ([.P], 1), ([.Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 8253060737581961939004167174633699681293174061997134895282202671041319061349229273639066076273719695702004874479787224350853464057772785801263047942645479596423764768852575443322595332823108004458467198639022964180063295401381701559723906760620637665999056610067687948902188627377622708345877386294103248255484855942427457834912643677089460643911884653), ([.P], 1), ([.Z], 2), ([.P], 1), ([.Z, .P], 14082624353910807314753431243591884514679911164294768116373842458823345000126961075750237472646204311081463690141234224770523621996359659290582965719730991688324424846902624840561870348850834766748492099013233458449465534564407927907745979806607472883114112628019019529516778575185457212433524156635786706458376292367958965016038085130077262703333041219)]
def ckptK1_1 : Nat := 1

def ckptRle_2 : Rle := [([.Z], 2651654449756534159029073754781221361344930473044449173563425219656532110883130163701611961384683582010596511253143066623574608037001330218241721508338366590715494765636247715705479158257920204850999641774339261762858187593500449654273369533559915597627807131443425946071308571358188843983960444720904334351028478260191211320624184166885284601602777592796596892446772125415052620951442416736923660728834176821801252461747630206791754417025652720143526743192421207564796855380496692775132848959187533993530965069454126595468095333201123373656629615088555629893748892178277332765055669202549140285054262436081614200928744366598445921905038538670862421890405505577468033639103080388207263301187408182619833467785815860374924343045160), ([.W], 1), ([.T], 1), ([.P], 1988740837317400619271805316085916021008697854783336880172568914742399083162347622776208971038512686507947383439857299967680956027750997663681291131253774943036621074227185786779109368693440153638249731330754446322143640695125337240705027150169936698220855348582569459553481428518641632987970333540678250763271358695143408490468138125163963451202083194597447669335079094061289465713581812552692745546625632616350939346310722655093815812769239540107645057394315905673597641535372519581349636719390650495148223802090594946601071499900842530242472211316416722420311669133707999573791751901911855213790696827061210650696558274948834441428778904003146816417804129183101025229327310291155447475890556136964875100839361895281193257283871), ([.Z], 1), ([.T], 1), ([.P], 1491555627988050464453853987064437015756523391087502660129426686056799312371760717082156728278884514880960537579892974975760717020813248247760968348440331207277465805670389340084332026520080115228687298498065834741607730521344002930528770362627452523665641511436927094665111071388981224740977750155508688072453519021357556367851103593872972588401562395948085752001309320545967099285186359414519559159969224462263204509733041991320361859576929655080733793045736929255198231151529389686012227539542987871361167851567946209950803624925631897681854158487312541815233751850280999680343813926433891410343022620295907988022418706211625831071584178002360112313353096887325768921995482718366585606917917102723656325629521421460894942962902), ([.Z], 1), ([.T], 1), ([.P], 1118666720991037848340390490298327761817392543315626995097070014542599484278820537811617546209163386160720403184919731231820537765609936185820726261330248405458099354252792005063249019890060086421515473873549376056205797891008002197896577771970589392749231133577695320998833303541735918555733312616631516054340139266018167275888327695404729441301171796961064314000981990409475324463889769560889669369976918346697403382299781493490271394682697241310550344784302696941398673363647042264509170654657240903520875888675959657463102718694223923261390618865484406361425313887710749760257860444825418557757266965221930991016814029658719373303688133501770084235014822665494326691496612038774939205188437827042742244222141066095671207222176), ([.Z], 1), ([.T], 1), ([.P], 652698274994419875564057473662049323908733801058294154807173677618482700795992211338838541347657572282840671679797436320364867989848663144662507915103588126420513504124296235383679900810694628660693524208304334533517067141833408104174838953918217028755010371703947882935721339673361990310627541870459599961493446231770250520454973329926649744935105783546995945217036239191070446849235672212306260968117351569310057300416439709807489874728856674714635906727532572113450000396831120807863115452249004529247362043088847875634953140041074017546105068089546530609821546515866227409864969899912883056110744420330153661224054918797407635695283753626424206253982641957947134287723930043827653995416280618898599135655427538458920964712641), ([.Z], 1), ([.P, .Z], 156647585998660770135373793678891837738096112253990597153721682628435848191038130721321249923437817347881761203151384716887568317563679154719001899624861150340923240989831096492083176194566710878566445809993040288044096114040017945001961348940372086901202489208947491904573121521606877674550610048910303990758427095624860124909193599182395938784425388051279026852088697405856907243816561330953502632348164376634413752099945530353797569934925601931512617614607817307228000095239468993887147708539761087019366890341323490152388753609857764211065216341491167346357171163807894578367592775979091933466578660879236878693773180511377832566868100870341809500955834069907312229053743210518636958899907348535663792557302609230141031531034), ([.Z, .P, .P, .Z], 58742844749497788800765172629584439151786042095246473932645630985663443071639299020495468721289181505455660451181769268832838119086379683019625712359322931377846215371186661184531191072962516579462417178747390108016536042765006729375735505852639532587950933453355309464214920570602579127956478768341363996534410160859322546840947599693398477044159520519229635069533261527196340216431210499107563487130561641237905157037479573882674088725597100724317231605477931490210500035714800872707680390702410407632262583877996308807145782603696661579149456128059187754883939186427960466887847290992159475049966997829713829510164942691766687212575537826378178562858437776215242085895153703944488859587465255700873922208988478461302886824138), ([.P], 1), ([.P, .Z, .Z, .P], 44057133562123341600573879472188329363839531571434855449484223239247582303729474265371601540966886129091745338386326951624628589314784762264719284269492198533384661528389995888398393304721887434596812884060542581012402032073755047031801629389479649440963200090016482098161190427951934345967359076256022997400807620644491910130710699770048857783119640389422226302149946145397255162323407874330672615347921230928428867778109680412005566544197825543237923704108448617657875026786100654530760293026807805724196937908497231605359336952772496184362092096044390816162954389820970350165885468244119606287475248372285372132623707018825015409431653369783633922143828332161431564421365277958366644690598941775655441656741358845977165118103), ([.Z], 2), ([.P], 83501787437237380289896341959923728938685032761744762133498979063555887037754418734007548046958899703152224919324265883043068625957624549418691784265283047761830134665721111340827279729166032141383851134049764819608343201583831767840057239817605833777998844935951816251027526984385435132248604747416650085326440436239560479489614142163450001213493903265150428912017045943442451119927036584922754956886854318546661211492807156015534016013371330000721696551108070484730629563403259363280321855014707935036835351631628327049868779423124767136426347835463195590200545323667904093274692674469901780869763557384295380395766953736040191660475155303741544437276208932796937080582010003350694904196983553906928183645448423805552388761748), ([.T], 2), ([.P], 1), ([.Z, .P], 8588755279258701972675052315877869262264746226922318390874180703680034095311883069783633513401486826609943134559067347970144201527069953654494012095857684912645385279902742880770805914999934734542338973787975810016858157877194124692120173238382314331451309764840758242962831346965359042174142202591426865919291016298926220747503168908240571553387944335844044116664610439896937829478209477306340509851219301336228010324974450333026355932803908228645660216685401535572293326521478105937404533658655673318074493310681770782272217312092833191175281491647642974992056090434412992451111246516904183175175680188098953412136029527135562570791730259813415999262695775944827814002721028916071475860261165544712613174960409305713959986920), ([.P, .Z, .Z, .P], 3220783229722013239753144618454200973349279835095869396577817763880012785741956151168862567525557559978728675459650255488804075572651232620435254535946631842242019479963528580289052218124975525453377115170490928756321809203947796759545064964393367874294241161815284341111061755112009640815303325971785074719734131112097332780313688340590214332520479125941516543749228914961351686054328553989877691194207238001085503871865418874884883474801465585742122581257025575839609997445554289726526700121995877494277934991505664043352081492034812446690730559367866115622021033912904872169166717443839068690690880070537107529551011072675835964046898847430030999723510915979310430251020385843526803447597937079267229940610153489642734995096), ([.Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 2415587422291509929814858463840650730011959876321902047433363322910009589306467113376646925644168169984046506594737691616603056679488424465326440901959973881681514609972646435216789163593731644090032836377868196567241356902960847569658798723295025905720680871361463255833296316334007230611477494478838806039800598334072999585235266255442660749390359344456137407811921686221013764540746415492408268395655428500814127903899064156163662606101099189306591935942769181879707498084165717294895025091496908120708451243629248032514061119026109335018047919525899586716515775434678654126875038082879301518018160052902830647163258304506876973035174135572523249792633186984482822688265289382645102585698452809450422455457615117232051246321), ([.Z], 2), ([.P], 7246762266874529789444575391521952190035879628965706142300089968730028767919401340129940776932504509952139519784213074849809170038465273395979322705879921645044543829917939305650367490781194932270098509133604589701724070708882542708976396169885077717162042614084389767499888949002021691834432483436516418119401795002218998755705798766327982248171078033368412223435765058663041293622239246477224805186966285502442383711697192468490987818303297567919775807828307545639122494252497151884685075274490724362125353730887744097542183357078328005054143758577698760149547326304035962380625114248637904554054480158708491941489774913520630919105522406717569749377899560953448468064795868147935307757095358428351267366372845351696153738963), ([.T], 3)]
def ckptK1_2 : Nat := 2

def ckptRle_3 : Rle := [([.Z], 6281431724708649825120674837375989358145940169906927812023632568887425192929852459284147968167086532053115673650560767062501895623868880670389058483328635094056805731084580571438325160659112049898746142508642234740575505996610008063643417833972938234970727799647588319072675372585019447265351842380974898495554236703297269347711172332550871062672105261235921520966767882384327674204271593002378098662905332614214006577685510787225031472576054675117564785662299387567985780847611240648618243696465713312254561891424102176933289750008157423845461247527101512530760138942187458220028745652606863163912395253357111585674362541572240628450656937443149488844669306744949755114681777272663781777667957770595077711566807728858641747789535285720523396163329447740793097617117856118559589984673640900329762187428931194504031435477040708154817880780580309338628819507763502187444618708518105685105095932823836391298587232872879130330541884305111237687605210655499869535518342720065391721895114873860952649563022745169533685549379149428844529315163390203272521024134923539733783453389735874360731009316048647991163538), ([.M], 1), ([.T], 1), ([.Z], 7687693930392208428132198942827418324413728111954742452807781172553899180532920886529718154236084944605711740321418387149094816971010850613911760823004578005454091825801875796575034043832187864229054741241591605033347118365838919346421424803486320822811987334380356420882080521307728843569897500897007249707955048504734112455020751314655971905074699908116502979336302490317878553878800196903578784785190031926691443651729927995665143318046453306819158117081836036607355623036156041486416434949289294937750191330664552755426556622959558402391665664121109354187859234446559316272325582088199590427522187264816464938846296075332490125160296719610707560921984397592771131031911567628056615061428979908179698693773593055762900243573522984862694034976322705026626789276843208475600421642846324176011121462075080128389046978595685605454362467091421040803564858382982730957841545800917207717280811516812647879873027934764529166495064778816917732880729463466284621615614642411647467572149276375086809910415983791096005838116175149771814887184323602408561660755236818633532021122025287314033835126529270960740096565), ([.U], 1), ([.M], 1), ([.Z, .P], 1116232551322770397234384805548284864676602369196704972671271279708123857188324328274977691791538767087203119406311679444581898219915946291669987610190538131841807822808165137998608815001695185051873175385041223366718308325643029987008323035502481429968978056741749443091590246950861596795331357166728528438608514116472935166589014524466056978026482860821085689479209966948612299334598688306923204045504137174761602019424673089467388642605404612680369197938166810974262357775167854124982282066352503732584726217036178546022470991420040125440338648178418707421170923839969520977739008568279166145470459059299486718596446563432491120183364006198129541608180906575272055510962588002584542023066754342587521403786932722169594599774264320214613057945184607207886987274001806145005273432877910062786424933063768149691633775745464402876843396189744678299847466407060039118971780663573235670044496087698038969899657816291201182030184387095531614230634583302997394798990957014349408917772977582384160783716393774582070840232802795387568058824231647408540226245175859742024381324493619528098732576078337928030021466), ([.Z], 1), ([.T], 1), ([.Z, .P], 1766652672574307763315189798011997006978545672786323447131646659999588335511521004173666616046993087139938783214220215736328658144213122688546922698436178620203476611867538285717028951435375264034022352580555628520786861061546564767899711265804888878585517193650884214739189948539536719543380205669649190201874629072802357004043767218529932486376529604722602927771903466920592158369951385531918840248942124797747689349974049908907040101662015377376815095967521702753496000863390661432423881039630981869071595531963028737262487742189794275456535975866997300399276289077490222624383084714795680264850361165006687633470914464817192676751747263655885793737563242522017118626004249857936688624969113122979865606378164673741492991565806799108897205170936407177098058704814397033344884683189461503217745615214386898454258841227917699168542528969538212001489355486558484990218799011770717223935808231106703985052727659245497255405464904960812535599638965496859338306864533890018391421783001058273392932689600147078931349060762885776862523869889703494670396538037947245550126596265863214663955596370138682247514744), ([.Z], 1), ([.T], 1), ([.Z, .P], 837174413492077797925788604161213648507451776897528729503453459781092892891243246206233268843654075315402339554733759583436423664936959718752490707642903598881355867106123853498956611251271388788904881538780917525038731244232272490256242276626861072476733542556312082318692685213146197596498517875046396328956385587354701374941760893349542733519862145615814267109407475211459224500949016230192403034128102881071201514568504817100541481954053459510276898453625108230696768331375890593736711549764377799438544662777133909516853243565030094080253986133814030565878192879977140733304256426209374609102844294474615038947334922574368340137523004648597156206135679931454041633221941001938406517300065756940641052840199541627195949830698240160959793458888455405915240455501354608753955074658432547089818699797826112268725331809098302157632547142308508724885599805295029339228835497679926752533372065773529227424743362218400886522638290321648710672975937477248046099243217760762056688329733186788120587787295330936553130174602096540676044118173735556405169683881894806518285993370214646074049432058753446022516099), ([.Z], 1), ([.T], 1), ([.Z, .P], 1245296940069465724414610548689805302154834518135073985136387021424375678175724328731771987404935437031660980087666467380361680201593727581644329927618819103336016852320359232079697959236266190823496011288936614818495112725795505329256160386482455845309141144552514222449055369254554968924791545339131514539322623561190118295225869328857444816110794941603523722325243619377045596445161661642411199513265553035593412252920650915437055454406654521021536886449767348493161442892921637258183358430274511976664835185880986690406319199802982264944377804374048370466743811908965996840790081433986444731040480888030989870434160697329372905954565469414788269856626823898037886929417637240383379694483847813449203566099796818170453975373163632239427692770096577416298920177558264980521508173554418413796105315949266341999728931066033724459478413874183906728267329710376356142102892802798891044393390947838124725794305751299871318702424456853452457126051706997406468572624286419133559323890478115347329374333601804768122781134720618604255615625783431640152689904774318524695950415138194286035148530187395750958492697), ([.P], 2), ([.Z], 1), ([.P, .Z], 425027009926747189716169599035693083088398594424899201132522525735016391775554263458549198028316684390896572389326370250052338168352610318751264513111012596355149901761570571776393356481414705077444016781227235051173509708610230648899323001979791006026649336990127672561797824800520377241299247536562016597777857298195463774970432453546690926248545397004951858686314564338125452438943346701482296925018883001159225384319394753297197983145904064059063656137994285717122974691313913686050945863726530267407261136486852600216248569809938355456128946806397892441138159462142240679985237877921682493852213257194804558234800806845448541915973217744672402381576575965199744213789600816368729462629264153523710072980408998056884097606354491158641125909897215821464660538946841570598161807134281139291754109128127103151814399226157599556951908549172012121864996824226707202993101098822116658978481202623484069307946630049341988542262516624837037726280091334602854173461941324694582626382787617907815067645857629552403896857874910551420145475380511897867239993355423517155437504326416666468363557814444057211431249), ([.Z], 1), ([.P, .P, .Z, .Z], 159385128722530196143563599638384906158149472909337200424695947150631146915832848796955949260618756646586214645997388843769626813132228869531724192416629723633181213160588964416147508680530514404041506292960213144190066140728836493337246125742421627259993501371297877210674184300195141465487217826210756224166696486823298915613912170080009097343204523876856947007367961626797044664603755013055861346882081125434709519119773032486449243679714024022148871051747857143921115509242717632269104698897448850277722926182569725081093213678726883296048355052399209665426809798303340254994464204220630935194579971448051709338050302567043203218489956654252150893091215986949904080171100306138273548485974057571391277367653374271331536602382934184490422216211455933049247702105065588974310677675355427234407790923047663681930399709809099833856965705939504545699373809085015201122412912058293747116930450983806525990479986268503245703348443734313889147355034250476070315048227996760468484893545356715430650367196611082151461321703091456782554553267691961700214997508283818933289064122406249925636334180416521454286719), ([.Z, .P], 1), ([.Z, .Z, .Z, .P], 76070175072116684523064445281956432484571339343092754748150338412801229209829314198547157601658952035870693353771481039071867342631291051367413819107936913552200124463008369380434038233889563692837991639821919909727077021711490144547322014558883049374087807472664895941458133416002226608527990326146042743352286959620210846088458081174549796459256704577590815617152890776425862226288155801685752006466447809866565906852618947323078048119863511465116506638334204545962350583956751597219345424473782405814367760223499186970521761073937830664023078547735986431226431949190230576247357915650755673615594986372933770365887644406997892445188388403165799289884443993771545129172570600656903284504669436568164018743652746811317324287500945860779519694100922149864413676004690394737739187072328726634603718395090930393648599861499797647977188177834763533174701136154211800535697071664185652033080442514998569222729084355422003631143575418649810729419448164999942650363926998453859958699192102068728264947980200743754106539903748195282582854968671163538738976083499095399978871512966619282690068586107885239545933), ([.P], 1), ([.M], 1), ([.T], 1), ([.P], 1), ([.Z, .P], 86937342939561925169216508893664494268081530677820291140743243900344261954090644798339608687610230898137935261453121187510705534435761201562758650409070758345371570814866707863353186553016644220386276159796479896830945167670274450911225159495866342141814637111617023933095009618288258981174846087024048849545470810994526681243952092770914053096293376660103789276746160887343842544329320916212288007390226068418932464974421654083517769279844013102990293300953376623956972095950573253964966199398608463787848868826856213680596298370214663616026375483126841635687350799074549229996980475029435055560679984426210023275300165036569019937358158175046627759867935992881765861911509257893603753719622213220758878564174567784362656328572509555176593936115339599845044201148217593985987642368375687582404249594389634735598399841714054454831072203239729752199658441319099200612225224759069316609234791445712650540261810691910861292735514764171212262193655045714220171844487998232982809941933830935689445654834515135718978902747140794608666119964195615472844544095427537599975853157676136323074364098409011702338208), ([.Z], 1), ([.T], 1)]
def ckptK1_3 : Nat := 1

def ckptRle_4 : Rle := [([.Z], 2049598894107271937864956752670616944521196122779473635635460247097856877970796597594312010353352271817951497324826820249844603957331621028094852369683011139066043525129330977644885903234477617781536763132302080134017251658044469899127338442049081411520551400227310249206047466705711823463907339914061838499417837702704290523846283379000522242414174534616946458033982759425245824499476212090705108234571249520348697209893445651782920804513011879753206185268126397516097728466714872855653059008083824582956454200838168508219321487070465201073714254168034861758072709337485686805526323629055509458538354109012980777271705700872571344715123072622015138228037443294221159582809151726646565318247534610481667286048285330877367923438951838091424616140970366683002540282098637680231556739745961518814304438617207986215943149046427589534312856941653178565822575484481387894698775466414869892348822202206770030844887954141118416239615204599219358600929889248337944209889964894039972412246592516966878404724913978048843552120244069765787188186748048417382795420917336698876080294030084684498000101229619583556772575447352995200993073465196034021548627555505625557745628905774740875331609750672075054321020123670466154947384952573939759757414303988021499564521681347871820769713836204219151116181605253996074817372517698860924658661178296161517617269176885864011548564917840266993887762785111648242609940497090440917781149327283195026977249653559938820154875895187291535581802131995694), ([.W], 1), ([.T], 1), ([.P], 858737776264618683306692870719751057753681059367204337988379729956011902060246813805756672063348303467392124783026867864149872568325516055174890010669273980115807719591219429117496075956707009919124911791926960822122921120071806963323292462810333647982433490797317463859466095016991947772105712416850765266106086763906780241423780375862671451718115379995281970812346210261644357661874680478155250899644818893287459485741454315794913426316401307745339298860257548524746159712114256488495607336900287288032507190221420283196817863185430235414393518960413331504977478584761364771944871671935453494902363826650425569046746197491536970438949757295801716075647590857644223533143772102688803272649259809545398912912911742093811687267223750842877617281412651544427425367391615007341441100614698706142709892507993453532770016472295810122007758134356990163028309718035652521570137571309140202137793632997176300321613424232141882257565174138527875667900855344039473577995380883929050156242311734430067452443913169333511673384827469968222854083967955845276895035920819423706060203031490418520443324529486207775902397568057879743338516828679597905409185212703439819815714810116447933499476061152332135700892836351787844349049112583803298965147353561868608346986364107619477982329922134735563026722775223572027420875221459043752929038033846096536437747688083905334256068554185792747569512606316221274107258644027746299807751991761284161710242877924539030676060166009715100220251350254470), ([.Z, .P], 88327314130075064568688409559745823083235766106341017621661915081189795640482529420020686269372968356646047120539906408883986892742053079960845829668839609383340222586525426994942453526975578163109990927169630255989786172350243001941824367603348603792478873339152653425545084058890600342273730420018935855942340352858983110546445981517303349319577581942371859854984181626911991073792824277753111521106324229023852975676263872481762523849686991653806327882769347848259604998960323524530976754652600978197629310994203229128815551641929967071194761950213942669083397797289740376542901086256218073761385993598329487101951037456272374102291975036139605082066609345357691563409073701990848336615352437553241031042470922043934916404628728658124554920373872730283963752074566115040833941777511866917535874657965040934799201694293283326835083693819576131054340428140809973647214150191797277934173059393995276604508809349591736460778132197105724354412659406815488710879524890918416587499209206969949795108516783131446914976725111196731493562922418315514194917980427140724051906597524728762102741951604295656949960892714524773600533159521330070270659050449496667181044951897691787445660394861382733957806120310469606847330765865762625036415156366363628287118597451069432021039649133858515054177199737281694249004308492930214586986769195598500890739762202915977237767051287681539750007010935382759622460889099996762265940204866874942347339267443666871726680474218142124594082996026173), ([.P], 132490971195112596853032614339618734624853649159511526432492872621784693460723794130031029404059452534969070680809859613325980339113079619941268744503259414075010333879788140492413680290463367244664986390754445383984679258525364502912736551405022905688718310008728980138317626088335900513410595630028403783913510529288474665819668972275955023979366372913557789782476272440367986610689236416629667281659486343535779463514395808722643785774530487480709491824154021772389407498440485286796465131978901467296443966491304843693223327462894950606792142925320914003625096695934610564814351629384327110642078990397494230652926556184408561153437962554209407623099914018036537345113610552986272504923028656329861546563706383065902374606943092987186832380560809095425945628111849172561250912666267800376303811986947561402198802541439924990252625540729364196581510642211214960470821225287695916901259589090992914906763214024387604691167198295658586531618989110223233066319287336377624881248813810454924692662775174697170372465087666795097240344383627473271292376970640711086077859896287093143154112927406443485424941339071787160400799739281995105405988575674245000771567427846537681168490592292074100936709180465704410270996148798643937554622734549545442430677896176604148031559473700787772581265799605922541373506462739395321880480153793397751336109643304373965856650576931522309625010516403074139433691333649995143398910307300312413521008901165500307590020711327213186891124494039263), ([.Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 24842057099083611909943615188678512742160059217408411206092413616584630023885711399380818013261147350306700752651848677498621313583702428738987889594361140139064437602460276342327565054461881358374684948266458509497127360973505844296138103388441794816634683126636683775934554891562981346264486680630325709483783224241588999841187932301741566996131194921292085584214301082568997489504231828118062615311153689412958649408949214135495709832724466402633029717028879082323013905957590991274337212246044025118083243717119658192479373899292803238773526798497671375679705630487739480902690930509561333245389810699530168247423729284576605216269617978914263929331233878381850752208801978684926094673067873061849039980694946824856695238801829935097531071355151705392364805270971719855234546124925212570556964747552667762912275476519985935672367288886755786859033245414602805088278979741442984418986172954561171545018102629572675879593849680435984974678560458166856199934866375570804665234152589460298379874270345255719444837203937524080732564571930151238367320681995133328639598730553829964341396173888708153517176501075960092575149951115374082263622857938920937644668892721225815219091986054763893925632971337319576925811777899745738291491762728039770455752105533113277755917401318897707358987337426110476507532461763636622852590028836262078375520558119570118598121983174660433054689471825576401143817125059374089387295682618808577535189168968531307673128883373852472542085842632359), ([.P], 1), ([.Z], 2), ([.P], 1), ([.Z, .P], 76548945239829812813090045544653403545026649448696688838019428145360308882281961471906314414312299512385265220774297831029516680275598250356234171104266057102866279331503887401250108214247189567181513510869284659142050976251664636194534257792863430508649213662331751595523070226841101603337916728978992357650123144672805512594941832077296508476055680853014290642008097836109865235867787927243942854018313629879635621718759382421730249377036758147681559519057699694933180535594570261480490715275899123806758727194800737355952876123594691041007496907951400823212380134944982692110370315280690757220745657009623042707610068313052406484067535326835472433835902388806438271218102701164860356938163064559485001200969375495196516890146084363943751268754013145411493555244425107206133118998639987265712424322778984867873130117504811953827854842342603282585829778556431205182392432170192328872261421235350075254075592881552207049071481923425776816556465581046346175584959347912881912606480612169205399471953432267934513833354674025279170484147056597637364836931383751509699807353939567618399908746541048174388372895499299757214058540907258231810797321719855315078124957869897556127365180791229051010002301652207211400401742020458787010867862812523592788490369573722164193240020970499753822210979723109142386798645129097050859721397799018842509412491988866009063276596861442503104123474362384767756217282748697656483576580085006095509624672214719085157889259052047853112105380980810), ([.Z], 3), ([.Z, .P], 22076818104519269253184463749132619057749716280116643327318243436480782670760168244834990879389177923465494198831829009164303253034427998632130915531967882672735086151636445730310042275950503307384877380372732771306184948392849396003681031509087543726903264410098791437717960614177793856111385451848020936793954237970250968967689023383916993991800764762747580877632847312729419728343892140185578367415548500169518397481950762560594425843437585841015996126898024202031802060441384735559327693011900301008257548801194086600375893258913502420780705091283253222597138299619996201834412211879104527957077103932940499963432500474005803263519674544743755215537623496608294855686678183340755216192480514473439230511052340595579581298347821110019557399872837975062631502418146849961413428031624829267230133746634387879471819691121992031264271259615913342754964096836859817869480360739069458666053369576523626767121953151857715057157936257716940595524714936538151288299720307567402573422956018405051359084593066989881785989351115250278068022508021994367682580531202420052435678426345083139119182053210874745597774297009141837124608865478120265021526105636775617897257256746966526564478568865890723270939731896460154120992376243466771260758762162402936922599752223795363070478224725059805843827220870988883314062777247524155367054412187975771982554502160375865412919160946024690162533116118360309640422073485990106576239159652873642098143766971580848806825926815844686650416013026517), ([.P], 33115227156778903879776695623698928586624574420174964990977365154721174006140252367252486319083766885198241298247743513746454879551641997948196373297951824009102629227454668595465063413925754961077316070559099156959277422589274094005521547263631315590354896615148187156576940921266690784167078177772031405190931356955376453451533535075875490987701147144121371316449270969094129592515838210278367551123322750254277596222926143840891638765156378761523994190347036303047703090662077103338991539517850451512386323201791129900563839888370253631171057636924879833895707449429994302751618317818656791935615655899410749945148750711008704895279511817115632823306435244912442283530017275011132824288720771710158845766578510893369371947521731665029336099809256962593947253627220274942120142047437243900845200619951581819207729536682988046896406889423870014132446145255289726804220541108604187999080054364785440150682929727786572585736904386575410893287072404807226932449580461351103860134434027607577038626889600484822678984026672875417102033762032991551523870796803630078653517639517624708678773079816312118396661445513712755686913298217180397532289158455163426845885885120449789846717853298836084906409597844690231181488564365200156891138143243604405383899628335693044605717337087589708765740831306483324971094165871286233050581618281963657973831753240563798119378741419037035243799674177540464460633110228985159864358739479310463147215650457371273210238890223767029975624019539779), ([.Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 2935248065974897072751051669065353888590175169733909639767860941088463053055628539734214692764806422814772073950750376510822862373618616849615230130844199991856203075565682577404234205159556610393321593213516525939041666351172339414737167401454737720905377053683738905104206819415280079218081031930547743187650944650768327926823700227771134439423414761853007702304120702580351223674184333223621037404749700210030041551558551670919123859188719430973081152379732382790794291880452564812150835382449613624793050190282764433081701188895450611419756278513313537521265267339355357090557542472075985971993216552015469657459597485571438802391822840767395852480007308285643620274112021339893320157360421360570469733614737291192100422652118783482582527700853846751889451755848167437862718179458017437323225797181181676902245109981496073183570970190843458730724152127284168927416745735026949402653037498678845610511706153205772653692572316386771250494332789449780968313502182474876337482732822368892159136980535711401294726251657232156378056317699712887740327618021052471141935072763987785382444321206960963554524633350656633511217414763337788762524804772255218476497623782206257778499957722859328697698680429012184960272936946873592158584735453320902420060683250478537202464425879350057467516766866692701378455621118283522671054685126409533094953062862070259004984035062734148511996269842706570823186096102902871992234241646643003814472024059008436162722033489869672479715279967443), ([.Z, .P], 11439157082026395734867093424844584586232545671983616706287992742457704355242105326132965039891147211187403882748146665957549661462403148036908450820145248170222801044349929079384421664873119861479295734465889829723110406623331185602615969700107527057142754894866581417875354546781486756263310426173838270879045080429744118935691332566689805772831885400319932189888288823355036343113568867049142404024651096587994416816759323157959632158789994811550473536272401460667246066222372996851167485229974782028635709518303990383602590917358762515839998074934573634061129908525355273146162509491895179060691269494532732951051681691350552145911663939906543066986067401826203655276610151677590338973380344689668923172348592351152869338870579371717131682535908785819291407811941424377469544744991495638323519692521105669573550353711382727699489001951995465291374784134608300296661828496705320481970075420899095571814011262398722302545792200597758444013266073218542456380453516504516087257855370995833773363475867690154523078022410750581813682927004675865228292723880947362657580587440810756885252163769352917108863068481835019164434854185388738164115294494896108797149459639716101161436495770964700789110494347819676437882305722093260155361224691885298926666502662453394765432057760645011471168681101369557544350070867946709574809114204282698175206333055816094812388828333703298263668977957891606888459093203783375873678301554618188424286851813251738049666488636633506996562813020590), ([.Z], 1), ([.P], 1), ([.T], 1), ([.Z, .Z, .P, .P], 4289683905759898400575160034316719219837204626993856264857997278421639133215789497299861889959180204195276456030554999734081123048401180513840669057554468063833550391631223404769158124327419948054735900424708686146166402483749194600980988637540322646428533085574968031703257955043057533598741409815189351579641905161154044600884249712508677164811957025119974571208108308758138628667588325143428401509244161220497906306284746184234862059546248054331427576102150547750217274833389873819187806961240543260738391069363996393850971594009535943439999278100465112772923715697008227429810941059460692147759226060449774856644380634256457054716873977464953650119775275684826370728728806879096377115017629258625846189630722131682326002076467264393924380950965794682234277929478034141551079279371810864371319884695414626090081382641768522887308375731998299484265544050478112611248185686264495180738778282837160839430254223399520863454672075224159416504974777456953421142670068689193532721695764123437665011303450383807946154258404031468180131097626753449460609771455355260996592720290304033831969561413507343915823650680688132186663070319520776811543235435586040798931047364893537935538685914111762795916435380432378664205864645784972558260459259456987097499938498420023037037021660241879301688255413013584079131276575480016090553417826606011815702374895931035554645810625138736848875866734209352583172159951418765952629363082981820659107569429969401768624933238737565123711054882721), ([.P], 1), ([.Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 2201436049481172804563288751799015416442631377300432229825895705816347289791721404800661019573604817111079055463062782383117146780213962637211422598133149993892152306674261933053175653869667457794991194910137394454281249763379254561052875551091053290679032790262804178828155114561460059413560773947910807390738208488076245945117775170828350829567561071389755776728090526935263417755638249917715778053562275157522531163668913753189342894391539573229810864284799287093095718910339423609113126536837210218594787642712073324811275891671587958564817208884985153140948950504516517817918156854056989478994912414011602243094698114178579101793867130575546889360005481214232715205584016004919990118020316020427852300211052968394075316989089087611936895775640385063917088816886125578397038634593513077992419347885886257676683832486122054887678227643132594048043114095463126695562559301270212051989778124009134207883779614904329490269429237290078437870749592087335726235126636856157253112049616776669119352735401783550971044688742924117283542238274784665805245713515789353356451304572990839036833240905220722665893475012992475133413061072503341571893603579191413857373217836654693333874968292144496523274010321759138720204702710155194118938551589990676815045512437858902901848319409512543100637575150019526033841715838712642003291013844807149821214797146552694253738026297050611383997202382029928117389572077177153994175681234982252860854018044256327122041525117402254359786459975582), ([.Z, .P], 3302154074221759206844933127698523124663947065950648344738843558724520934687582107200991529360407225666618583194594173574675720170320943955817133897199724990838228460011392899579763480804501186692486792365206091681421874645068881841579313326636579936018549185394206268242232671842190089120341160921866211086107312732114368917676662756242526244351341607084633665092135790402895126633457374876573667080343412736283796745503370629784014341587309359844716296427198930639643578365509135413669689805255815327892181464068109987216913837507381937847225813327477729711423425756774776726877235281085484218492368621017403364642047171267868652690800695863320334040008221821349072808376024007379985177030474030641778450316579452591112975483633631417905343663460577595875633225329188367595557951890269616988629021828829386515025748729183082331517341464698891072064671143194690043343838951905318077984667186013701311825669422356494235404143855935117656806124388131003589352689955284235879668074425165003679029103102675326456567033114386175925313357412176998707868570273684030034676956859486258555249861357831083998840212519488712700119591608755012357840405368787120786059826754982040000812452438216744784911015482638708080307054065232791178407827384986015222568268656788354352772479114268814650956362725029289050762573758068963004936520767210724731822195719829041380607039445575917075995803573044892176084358115765730991263521852473379291281027066384490683062287676103381539679689963375), ([.Z], 1)]
def ckptK1_4 : Nat := 2

def ckptRle_5 : Rle := [([.Z], 2155853078734684196573345768606268648753005982952936985256275611995741111325867267324209285000333117448904007189040752967264856645026528234710614216098801179603775913550329397926649832222895389525985311557592705392259696160196039405483657055360007072797585370968157190523174381909587900053146644684924294376886390902536447757412417005782121422803277396260460971410406211691685413536676520486363566787539113666140224352798088648202516618691756300843539681146491193464135692857500947767938293401723015686835649656695658974515123197717835356501034199572214519797503861674917938013168916193195126942189537611934667265107066889995505524715936859209450655596788502976202613688196763357949577793424550087705613600016155601404473077172015845872872515868906872252273054847316314172056177492460269982870891496692859666756049002049941172462848564686776815078403706356953974221501119751751686262294496238064114110221893536098839002613419436662768889958028597955141159497566989122428075458680154588467603760133429482404601974932895252810834026108123796429673809653573346370114467080619800594773445560843549814572960265493728733982851588030991118076319333561848457529242928496434047856812578251258767274163769469165484073840215351386975306746619245595006816635755591078086979298501435913105265189717474770994290168709003064144471204921271259075809826025237497327041091704662090189565659789221461450115589889356972612970564393174682720096898109061493750273081380407864654775371118850822309534207896168397815298261816785903068544139003166265815098167876903077487219174801183509164668683774230256443036256672546689452300009815898199366677999431071499090058706796146375405705852816904956339023872032620700055654429299900481874441509241732346323533440192278900048504734913681462014668653969118505185426956054148719939232580460873304015084587294531143893883174834291161281164486), ([.M], 1), ([.T], 1), ([.P], 842401149055239681938459628762680496714091680774281514130177539902390290187323013015105022396784570562092303121250540181477470724757912557432563520870427062173018991185792594856703542418110948015821005997352319834502409476021627055498333688517413413910828180155290254302044790328824908856213099923049199443713826954500333358658695851982813842254835504677370547053616728616675970363046555060447820798852926007109384695173279693326990615197135316833871813855635072085597744399883215816238776348157259162062836451296038236583822674880601726994513065789988335226197344550303315425208697396137802058838439900123786196060833412370140335189680046969867795942567519339058429280083975781078066754414014659363043713051259494887162241527409262147143032151704588775473395697868181144622262179612909308739219956255922347277218398945601375752989269496045366982950633914277144337475747604193540135592075150182713009883780991368600914528017187197760152903260747429066645556138844603131309333326789432887820691423432780762845556697166105715858901718916009585187840834098196845653648211798401259006408067955643729709541050528944100633491232560163131094022917456182380240664097810650036437072696571108940436748867407293182984223861642772967143046554172916381647269714567378678889345286770017426289671107977069418275011251372024032306444162631641512259179255844222962449642233411844835522475396575331738113161174598734809318184671543131791469323047078835233893646554571906203195383172255456109187381083065336439676886669189044892897263884924673542990881524460983310675329751574660474525175441088452244935811033624938311871515260659218071195754238090532315230423361487475041574664292815321817392255022464199025348966458016996502162631719845949863563145330936433314469076012512885847626164608598814311789150861704565690973916246090215215629691597045215902983145376590590223123711), ([.Z], 1), ([.P, .Z], 343296134421456853790262987566044450474731226394516593342146876894255108891932145030484856670188705376410482308585740601115677995176538979197370400699233634322270961165703579021387861206574975917914460870242705178974772397830019700063772201309042524435656453478445974516895765675176954641662751790338499212535876810386936422435500974032946961475365356854140392077857027983161547916029411096752255592746378330706146427309776173158441427557771167833182190825032582958579859609579590921107985217117845931590707542986634784526091803924351683640661678297923174334227603914238699674198008900511510933089774866530970525325762409647785848181441369647384059638718126542793167429715656168645814112751351990465144563305111689232907624219942830775475266582706117279684864699636648700321384611753936111305873338235657468292238101840701847625674551272323950480655529931072221725753478953769425260603049489564573359025994413906349111482280082809107595133117801878560256567616702198910791155560729989141784412867248541457199637975473025131551637672026512570946677764973659133956967275773755124819925186430641386463560872114700934318898480394487438216570418119645321531788497896947325827415444662166304182175258406591813895948526480122529064213131634310070096129118507036058642261141089148341228286021445362439619884688055208278292114662523107170994030782028741064011259172005728371904965447231062378150341664961984630588822842472883550187101357475770063799587783996878175765220807051321144257538693910780065762864087154985841116831992474085713958728871854421537407527983753131465730680696360972376947831112424596546559388253456242734814688107227804575073400898928458862312256211167285102245506809555472155527094214692758093761153214969026777611510079975680780476087173448886872143239888120656560803449520438564296090668365406349854799498877281462005464508282728323133985920), ([.Z], 1), ([.P, .Z], 1), ([.Z, .P], 1), ([.P, .Z, .Z, .P], 80246348010191139879936641246692508122881963151126958773049163426268738857215396150300955134773432760905081399727092122315773854519600055846597311775169800112017999029092161715813717983406264065867247234214599054767453362820002813546483965121316135840354414760244450866256879052983791616032298492594919308281316046559663384473230982967383202973920353705054806390191601166440450688494908730731865034890856154531705085767865636206262678286644857160750398157623419115470032086052837612748252157933802215087216102055540023194003698635206514486221000555442776407865278072427344699190447643422896063997617963308599358359167094599022615462611814267289437532216659234324685366056872039873078874360825683247680829816556179742804572125005250762020161035132699474706275808596744772464258973272459116228071181563999604443432975426999773085700866461508762515068958352282759828800264460091262604806770123636048865776472422808240173015740251117529310071932224272291844762771338494333662354081080844980207989664991350018723511529740829632611831933249938900355341193014566337827134391318886916664006598082886352678019777899631125354710183106467988240832876416189678630766901783865486510041995140257926146398864041409795234259692248888756584827913429177768727493861136270953126088798725240520506865079473989829216077467019205359797246194019378850691489097442952971050932749193592852310923352373631323630796205771237033170809654104288359757784231582787862172630328087060675619306596224446221063482642200697583362792307410235157611634891994805408065868578825399137186468290443511810508969782431294078699795634684453654758002808381477976029465946995258117726327802197749613195279234136799092407581107326439991830162161658540065431486517526147655910964599771649381627683662975514275299391456091358114355055445597841846555432386786589969475207499742403289499733321112675631794623), ([.Z], 1), ([.Z, .Z, .P, .Z], 10493382717938487470662614917100573197146707155197220896250441627741778443538017657605618393834041080000177942649377171896272053531260237804002508439088213918071168740726498606408483789657542710085140647284578673653095323901423191616322661119755917425869723465553238969293111152688159593717932909304159709323201333400102199182199159027087260252817163481631291565997040050563915469202011903272571904093610910853048233778219191034224658610289272144047722157575194470223962437313175266024781685976276519544637397838345060485407783570729419571706010988482604754165136341890858436291023848189251871031857406150130677669325455085896847640854852549874898458899177893239341632224598435234670656605671770853218634230023476145041692323899696427282302091002819214701951050408071911380683469790795322496475549045898435047285109420347856549066622765438083395185052763782906705428631035334825824170320259968376014662653172876325886994422562160633249783221040357482932049970335822966814851421633186916856227266588280576766283233779787245950781951654018685476577445800539670490741171323823895959506714489514459273573961400242521427447644006090024927496255871470828564612387891268898082614364561022275245093334333335277235298648899590201083319076475271782285784447414056317350064954212066910771352802873765635703059454183440260603861115279523998170699435296876444608063194195736995752394966252936386368652509836035191396622248815014538693703469499981920476771150435918981404840349960999201429546945487101523692890532592938734758371091412803773608050207543998822906310624916164053651585001205199158661658517217138901504503902181681904558807706866883497531079665285426883042900998474204571176899661941329427501827985947342005316420424083758696351195657112854314006806851635141443767323696214578425547330151221012944108174731821886256969372314393000194766799699526442348539036), ([.P, .P], 1), ([.Z, .P, .Z, .Z], 1), ([.P, .Z, .P, .P, .Z, .P, .Z, .Z], 7650043142668618031087081313239580778318390500261079354686251879636586665997751266781272878314424010859656253631451219424041914139305604359059028030036753773253022616455133829694391352504378226971808696142199796975364485645360284940380735263190705975693526353691238690287585700028315284289081517372103605597896555068466230056383971320500098922971475104639590958282273019324543268907104380088478071417796426551785629037868810301751315419494715971668167196544737979874273938030475554750721110965508524795269603196896402056332416923864908613718226737883429545610065804980394037081524304312625217626545612456673843758774841231894496521778043875162638945370945573182510760575412360219409490790868242238196530534077647957572745786711709944540660549430631379655390229749012311312842742951961839574130808228407861761909173483451035257097185012880580849472127639011133048342869841990111435115927925600176988954177910084589941451746973563572014227092873007876866169031654346534502595480785685199105313277150898107483137021818453996551510584873873694818819683119928326191133155800052020769819131732849505615037626462319455861140314567637342789242870059723641211924200983915361290663852652744600508124578839987507044999554661633449623759233563481964545455003975586815934517508403380199695784057764294118986768437250652159665484009256209601918639601583464933757725451879673210530915198505008269542051706723788356061283284287824788471363588182957089039358584653175260736396956555572113384714809038704206908289211680175568665541490507048982349418060682082592737527091363196657006006214431001254745923611251432029476712785970468008153903173762224734440477135567639174884933663392026139977054275563941713507504925864308650714707263989108667952950053549730779329617162874922643789454635907393341319111692432003824713749981965473116609543619547814717000485862558458837983188), ([.P], 2), ([.M], 1), ([.T], 1), ([.P, .Z], 8873914278274612784329011155775855432904751714446039039609960858211805947921510540228173592851951277019940734671123569757190968764340253995290241761819003621725925831723881328579013382186856142507957067691977083626400579795625929103579340443000912970185838600300132451597649687449484876665040231581626157303246357052609712487203908210300807864232221651042259108740011054926469665130209581977324748446735893385580967933880177666359333345292602706378976434795596596045388502303586172572296374070290209315511031179288142081089938972923811056733124591909392622255375879513716254532968788497228118562277819255169864335183189005339345358833049600831469720325009082693562871863802372684581523032734855919706634162704898037114706306813027929475112014507895774662454293704528082298465260516544658434066585989385763341292130855177010397158918019057990714632373872441894260782354428268425315805911860735959316761297195002191992447516403015096822161780995061423015916479334529419428319150655107965577352531163413485907675341274684456281057018019191453835806622349508274261277182048517191840242859648340711304310076660424105159691664853879373509519047842418068663204949064421829843778475220554324500595366178411821885600850012941596610829644280047040255616419453139657573483192482511055914243654131980188807035237509902877650043513660729610461378032990867857675177309963586631340496179859224897320832437436692038263281821096556993690505304983259552495900342530027458586991193507960046781321857089797335612962259878299820134237334648543122013758610129537900126911183649654019126942943366406186148040686681338752213393851863238360151997490444737177876691580030495015495937836879718846973308718498253537562797290673123623593219884112846719177915907667582605512173798365607096267542601108076782321649046725528686743369659278264571537935245604853980124625278013185219865855), ([.Z, .P, .P, .Z], 1404006901182901854271763832351591794615781178280852949880437919187530556605084275604353453072008254997528878363043913940077914457093692029805394964225623898948444265173874021875293304825382183386032817117074667104621271069399420345736185732493924366693727480506772226090626207619715851050403791049524280629190384966749189869264784318178450018482019009294988633388824205758682763208836494111488379629521221371877467031302766895957177044940661786217639098667358538788236138035508590500206745934203040507931147973075732154876675827898571967322873579798845789144919929609777152020452661591309079117149674413867115273496196434237954171227808551556526154818036526070755579196898851704542426597655517053940749048795895232960366884279401475113121050206057488566611213907936823511545083278891690590286063423170971976373793252171309032145383119284091477180702589592299602190712173448652149026654574847448262854480497912688989758359239425955487478848189822053435509842736901996707012460785548049118263834553654752645519450851351021106483199548475916183075828628837884021905192450808848641041881494624746337639678308257220397049752282610344912768929900739264244449522926505202560123971827473262239450791942331630291160306793678850061053804573300954633061843121126302905406131965843244292883958598125213879304136155770923850465892571122419912128138567258475172966377758644279497039345295637866600272650193830675289137308364201975374300872579066065362269810114935972250511910581362533830658473060172140030898822890510610535992694200735388741315971589440131476344397662565463125330653386925751326364487650211460709548948536844798679528735846244337467344153969924926384451513866979330192040069268930602692345184554732075624649974510302954739964428725486684100968638011372912462530328155528051764772134005120796037288701446090343263769758045718930509021388702420742367503), ([.P, .P, .P, .Z], 1923710953170077939851615351064353992723500714636411689973297402641896673865482176981211644247473473884948897138627424718868698829533903218428445696456502459198777921722581476341836713494688870054451083267416739255278946353960303068106066933631417997125961994605777443258492425173840977698986295793585528359526998927979452313436681260684352930605064109845858532388679939838743361214992099130008401038004738647715395943902299728927572959544064228674477064380990184728784550328336224214404394342155787985385488719157321125532051286947857178952048142167176444200846025207866443429410634095151465343704507806821583852197499442764300338334585048755274990303841879939330497752027038052175644539620053915949238762218441530957647980775483998440045955234403426931809146231261207350379389414812556322488906322848689276610755818520069866789211137862655040806437612573410745602670737152007344400562372928536480931005950213133007409459411704705820831819683325980195458837013546535578607220710117437973243364632625304569858802126655649998913182208720879005351654752227718826073750817385098299049190873503020401476600439401819037834622037594420153300713040167511504252332972652983631292956380234609448272470374572802915940011961174248668007312031716685462794314173801068684650065215098401674957411701367356923334077910442655268300425051651184010888623804316971455225113477700707255646722151571469895039513844928839059593374547006897259638616789656266823692818333824324719609786984122483712337223348501860823962024563851822014346306292468282013843507209136581071247296206054794047272950375476568479150769855290571370473745911869586377470323070532104236415188541510704426525174962915237422950700167914473893703799447689283222807482032014564951754036649856792966096536375729748637798147260000741605846258516952461491474920783258871062955959056101312037713090552523715082194), ([.P], 1), ([.Z], 1), ([.T], 1), ([.Z, .P], 1236671327037907247047467011398513281036536173694836086411405473126933576056381399487921771301947233211752862446260487319272734961843223497561143662007751580913500092535945234791180744389442845035004267814767903806965036941831623400925328743048768712438118425103714070666173701897469199949348333010162125373981642167986790772923580810439941169674684070615194770821294247039192160781066349440719686381574474844959897392508621254310582616849755575576449541387779404468504353782501858423545682077100149419176385605172563580699175827323622472183459519964613428414829587633628427918906836204025942006667183590099589619269821070348478788929376102771248208052469779960998177126303095890684342918327177517395939204283283841329916559069953998997172399793545060170448736862953633296672464623808071921600011207545585963535485883334330628650207160054563954804138465225764050744574045312004721400361525454059166312789539422728361906081050381596599106169796423844411366395222994201443390356170789781554227877263830552937766372795707203570729902848463422217726063769289247816761696954033277477960194132966227400949243139615455095750828452739270098550458382964828824162214053848346620116900530150820359603730955082516160247150546469159858004700591817869226082059111729258440132184781134686791044050379450443736429050085284564101050273247490046864142686731346624506930430092807597521487178526010230646811116043168539395452883637361576809767682221921885815231097500315637319749148775507310957931072152608339101118444362476171294936911188015324151756540348730659260087547561035224744675468098520651165168352049829653023875979514773305528373779116770638437695478348114024274194755333302652629039735822230733217381013930657396357519095592009363183270452132050795478204916241540552695727380381429048175186880475183725244519591932094988540471687964636557738529843926622388267121), ([.P], 1), ([.Z, .P], 457115249057143118677689733329369983874956869161497976272116247945384400165784547422634484538749404880622834282885221151086558403182906714626567563661433740537999607712884053091365631385482815032376868589254795580978524014990299317370506941342528266789766653955206244914374375566281509976474575894070253778476721226141397106665735396681086801490116419788889922321510645919101263771832941912939654268849198931203004023609322004854988744944651911891192592817331935557681735343260407852249209465171028202994874486050180124716112638749694654739697676412117445830940444236494490805469877448262362666834933500667886751217866557558959538269211356973124954823761749158135799293610816369234516005380372224383204634149464394333994914325830214006785042251026152622651838377967057538421005419926773323295746858029010013180042033811189376684465132186718609365535930754097335626636199756971928339499828332426839198001360972062335429430791963471099076712556167954271442903808027393135998216283935698271758582145374725051257345882750260232084928858095977984312324584204495610508859404168902990949230064648816305193859942898557134573523820263157237752783673822457934457998984626675013363423701008799546371213306720757223077592795226061947574439404194272981483352532717109771266284907251950717933870724587229170384137453276966974298474526696900716001958875758880083542326514222955883576113242109825704660820566521293739768784363154193981761065906036583623096585171983108616102334171367386135412946720113757911523641852464354077406493050415984242965236919185984867733199745801228361762022615694425435988928742210987032488783452236123981461398280338988284088926490735357211084263689398791782673789473754926415343091591221584960282834309441947865586040245495632180513068695005298432825651724720013413575693707436227063240262926342196841692386449062985445492291151467929195087), ([.M], 1), ([.T], 1), ([.P, .Z], 342836436792857339008267299997027487906217651871123482204087185959038300124338410566975863404062053660467125712163915863314918802387180035969925672746075305403499705784663039818524223539112111274282651441941096685733893011242724488027880206006896200092324990466404683685780781674711132482355931920552690333857540919606047829999301547510815101117587314841667441741132984439325947828874706434704740701636899198402253017706991503641241558708488933918394444612998951668261301507445305889186907098878271152246155864537635093537084479062270991054773257309088084373205333177370868104102408086196772000126200125500915063413399918169219653701908517729843716117821311868601849470208112276925887004035279168287403475612098295750496185744372660505088781688269614466988878783475293153815754064945079992471810143521757509885031525358392032513348849140038957024151948065573001719977149817728946254624871249320129398501020729046751572073093972603324307534417125965703582177856020544851998662212951773703818936609031043788443009412062695174063696643571983488234243438153371707881644553126677243211922548486612228895394957173917850930142865197367928314587755366843450843499238470006260022567775756599659778409980040567917308194596419546460680829553145704736112514399537832328449713680438963038450403043440421877788103089957725230723855895022675537001469156819160062656744885667216912682084931582369278495615424890970304826588272365645486320799429527437717322438878987331462076750628525539601559710040085318433642731389348265558054869787811988182223927689389488650799899809350921271321516961770819076991696556658240274366587589177092986096048710254241213066694868051517908313197767049093837005342105316194811507318693416188720212125732081460899189530184121724135384801521253973824619238793540010060181770280577170297430197194756647631269289836797239084119218363600946896316)]
def ckptK1_5 : Nat := 1

def ckptRle_6 : Rle := [([.Z], 57659174508582353593254875339936906634847184155740914943641512730402587422332796842168194860662738189971633086588402932270718390017810090525158069788166701448967831058380265969352573046183103723850426620770592172645360804102411465553616680479340933514725894542295533748902856999930963119492921765435453547301783443560320526207227422103386479746427852811710137610790817496802467927091470436904865781057073390373853290218826332318041392382414023589746955337913629996851891261981481999897351978363427812548791071413595447928731923977506942091373056029081890650761204173692457632025968638000946340899322587856811602428021726314321623854159665749165053755977188454761447673463116691025562636591057914586402549364815368875200314023746840214654769079623574933396056033207763049237841048001033101743891811924688547158401557553962506967109178363313558245743011014145114147153387282348474438483266972352603272343047702000974398458169562457476787166396917442373057885308405135078199767111998225012198090921497335442892973693191401445927521475891265752715734604596015100503010178229743649823486767598165593657574541588363379784182025367536428239052400709416026232978281237741080760239716833918466804493529391987056867317409097894752108231963031880782952182504279742054375585212633849998211537703658747269743976913573040055164963963053060794067966896078039152158489406184958487354558400201883061202358656601493658676905460018614621978679480071142786032644539731663434702810805178763462585714802426836775873928602299010206978273390954547605844856734416505353462336277853338288137265943000668576812806405448027400011993378884824823958249770870705711844674347595318096597733247970705583925760266471934746351645924182290222700557995073100332257221854367876116053336595334693676873599958981514465090886994154620094245263548506366331963776111128088460989229427515653715759259812426827609512217731782107363571810977438509899408684459564350628967164406911330572372539923323586348837554549802448939691534370225511953267907562153294839089736677332668450249546891218536249050860509605035179777135712771830270947922496258445711195428024648610279592449056434435268474281652430447191564522833865956796494885427887603181143571893907184841484866083675626013184), ([.W], 1), ([.T], 1), ([.P], 43244380881436765194941156504952679976135388116805686207731134547801940566749597631626146145497053642478724814941302199203038792513357567893868552341125026086725873293785199477014429784637327792887819965577944129484020603076808599165212510359505700136044420906721650311677142749948222339619691324076590160476337582670240394655420566577539859809820889608782603208093113122601850945318602827678649335792805042780389967664119749238531044286810517692310216503435222497638918446486111499923013983772570859411593303560196585946548942983130206568529792021811417988070903130269343224019476478500709755674491940892608701821016294735741217890619749311873790316982891341071085755097337518269171977443293435939801912023611526656400235517810130160991076809717681200047042024905822286928380786000774826307918858943516410368801168165471880225331883772485168684307258260608835610365040461761355828862450229264452454257285776500730798843627171843107590374797688081779793413981303851308649825333998668759148568191123001582169730269893551084445641106918449314536800953447011325377257633672307737367615075698624195243180906191272534838136519025652321179289300532062019674733710928305810570179787625438850103370147043990292650488056823421064081173972273910587214136878209806540781688909475387498658653277744060452307982685179780041373722972289795595550975172058529364118867054638718865515918800151412295901768992451120244007679095013960966484009610053357089524483404798747576027108103884072596939286101820127581905446451724257655233705043215910704383642550812379015096752208390003716102949457250501432609604804086020550008995034163618617968687328153029283883505760696488572448299935978029187944320199853951059763734443136717667025418496304825249192916390775907087040002446501020257655199969236135848818165245615965070683947661379774748972832083346066345741922070636740286819444859320120707134163298836580522678858233078882424556513344673262971725373305183497929279404942492689761628165912351836704768650777669133964950930671614971129317302507999501337687160168413902186788145382203776384832851784578872703210941872193834283396571018486457709694336792325826451355711239322835393673392125399467597371164070915702385857678920430388631113649562756719509889), ([.Z], 1), ([.T], 1), ([.P], 24841969764019127255271748819375911997535596583948520922015559584046441912018043374741768129770868892119524357153051246148968853570907489323029366577895813997086094583522689541217101016371846016545275353185817736910311429687689387244470244080265528231087357182339637684259750055985423484594372065663872966305778500396567477014015749861346376060149312436503815765107164146407944333960085666811809384387138444918323903932124369961407928945271375530198250875625305539089026931249358210861402712006109321204946837807901420898361891790573039973103812837539727042348616879209274039076721639831742394441330336432490506831981270984087228304305241868626849671503842693283325349093365507925960106445251357807328214484122996624315184824830529059191719901690593566885942181648103258978407348494439330182192879673520893210848282839720603348129782588668306837486518332170647761307477745494704709898764924144877535433420819238562123366010567124308280727191143022050555725133136630861338714999366899534909889941747211927740675623137628090570581338889921599055040320631663005750915554364485298691669073503193335744898122899345506486295343549189732477992221112013127554965374654177091633101491382141953122472843921490347410017323176679356967318856723782749668538854082893649992419914384494300577825020317830473895616869194339888527190891797721355509876083427060431271317753205247746948127695359001072385500395839041692715906996187414702412996094820321769765350787148256733570989732926632983412047955063457303394666091735855414357369496084995979640922056678936903204702241066676940544676880258538691328887479603750887289864407119254985357800091517895470925809805575507269137370231768733710436174035936059451937978173232230903775569307005129419471010945319715017643384390744686407364851115724518390310857720274358112358005290640558387563509191345294088466756969849328360073210783043814744471358190563447932755849440271278099779167074021189807581352122902179528789874184369168131934660353855056288702573934483012012732298999477395566964430198226174287895778861810259099388781919359932791138294433344256891608949855782815083130489435154434707037268513999291860026980851716233233098417989092680126093719469750357570675794593355680094594162276788446308641), ([.Z], 1), ([.P, .Z], 5962072743364590541265219716650218879408543180147645021283734300171146058884330409938024351145008534108685845716732299075752524857017797437527047978694995359300662700045445489892104243929243043970866084764596256858474743125045452938672858579263726775460965723761513044222340013436501636302649295759329511913386840095176194483363779966723130254435834984760915783625719395137906640150420560034834252252913226780397736943709848790737902946865130127247580210150073329381366463499845970606736650881466237089187241073896341015606854029737529593544915081009534490163668051010225769378413193559618174665919280743797721639675505036180934793033258048470443921160922246387998083782407721902230425546860325873758771476189519189835644357959326974206012776405742456052626123595544782154817763638665439243726291121645014370603587881532944803551147821280393640996764399720955462713794658918729130375703581794770608504020996617254909607842536109833987374525874325292133374031952791406721291599848055888378373586019330862657762149553030741736939521333581183773209676951599121380219733047476471686000577640766400578775549495842921556710882451805535794718133066883150613191689917002501991944357931714068749393482541157683378404157562403045672156525613707859920449324979894475998180779452278632138678004876279313734948048606641573246525814031453125322370260022494503505116260769259459267550646886160257372520095001370006251817679084979528579119062756877224743684188915581616057037535902391916018891509215229752814719862016605299445768679060399035113821293602944856769128537856002465730722451262049285918932995104900212949567457708621196485872021964294913022194353338121744592968855624496090504681768624654268465114761575735416906136633681231060673042626876731604234412253778724737767564267773884413674605852865845946965921269753734013015242205922870581232021672763838806417570587930515538673125965735227503861403865665106743947000097765085553819524509496523086909569804248600351664318484925213509288617744275922883055751759874574936071463247574281829094986926834462183853307660646383869873190664002621653986147965387875619951317464437064329688944443359830046406475404411895975943620317382243230262492672740085816962190702405363222702598946429227114074), ([.Z, .P, .P, .Z], 2235777278761721452974457393743832079778203692555366882981400362564179772081623903726759131679378200290757192143774612153407196821381674039072642992010623259737748512517042058709539091473466141489074781786723596321928028671892044852002321967223897540797862146410567391583377505038688113613493485909748566967520065035691072931261417487521173845413438119285343418859644773176714990056407710013062844594842460042649151353891193296526713605074423797717842578806277498518012423812442238977526244080549838908445215402711127880852570261151573597579343155378575433811375519128834663516904947584856815499719730278924145614878314388567850547387471768176416470435345842395499281418402895713336409580072622202659539303571069696188366634234747615327254791152153421019734796348329293308056661364499539716397359170616880388976345455574854301331680432980147615373786649895358298517672997094523423890888843173038978189007873731470591102940951041187745265447202871984550015261982296777520484349943020958141890094757249073496660806082386528151352320500092943914953628856849670517582399892803676882250216615287400217040831060941095583766580919427075923019299900081181479946883718875938246979134224392775781022555952934131266901559085901142127058697105140447470168496867460428499317792294604487052004251828604742650605518227490589967447180261794921995888847508435438814418597788472297225331492582310096514695035625513752344431629656867323217169648533828959278881570843343106021389075963396968507084315955711157305519948256226987292163254647649638167682985101104321288423201696000924649020919223268482219599873164337579856087796640732948682202008236610592383322882501795654222363320859186033939255663234245350674418035590900781339801237630461647752390985078774351587904595167021776662836600415206655127977194824692230112220476157650254880715827221076467962008127286439552406588970473943327002422237150710313948026449624415028980125036661907082682321691061196157591088676593225131874119431846955065983231654103471081145906909952965601026798717840355685910620097562923318944990372742393951202446499000983120244805487020453357481744049163899123633354166259936267402428276654460990978857619018341211348434752277532181360821513402011208513474604910960167778), ([.P], 1), ([.P, .Z, .Z, .P], 1676832959071291089730843045307874059833652769416525162236050271923134829061217927795069348759533650218067894107830959115055397616036255529304482244007967444803311384387781544032154318605099606116806086340042697241446021503919033639001741475417923155598396609807925543687533128779016085210120114432311425225640048776768304698446063115640880384060078589464007564144733579882536242542305782509797133446131845031986863515418394972395035203805817848288381934104708123888509317859331679233144683060412379181333911552033345910639427695863680198184507366533931575358531639346625997637678710688642611624789797709193109211158735791425887910540603826132312352826509381796624461063802171785002307185054466651994654477678302272141274975676060711495441093364115065764801097261246969981042496023374654787298019377962660291732259091681140725998760324735110711530339987421518723888254747820892567918166632379779233641755905298602943327205713280890808949085402153988412511446486722583140363262457265718606417571067936805122495604561789896113514240375069707936215221642637252888186799919602757661687662461465550162780623295705821687824935689570306942264474925060886109960162789156953685234350668294581835766916964700598450176169314425856595294022828855335602626372650595321374488344220953365289003188871453556987954138670617942475585385196346191496916635631326579110813948341354222918998619436732572386021276719135314258323722242650492412877236400371719459161178132507329516041806972547726380313236966783367979139961192170240469122440985737228625762238825828240966317401272000693486765689417451361664699904873253184892065847480549711511651506177457944287492161876346740666772490644389525454441747425684013005813526693175586004850928222846235814293238809080763690928446375266332497127450311404991345982896118519172584165357118237691160536870415807350971506095464829664304941727855457495251816677863032735461019837218311271735093777496430312011741268295897118193316507444918848905589573885216299487423740577603310859430182464724200770099038380266764432965073172192489208742779556795463401834874250737340183604115265340018111308036872924342725015624694952200551821207490845743234143214263755908511326064208149136020616135051508406385105953683220125833), ([.Z], 2), ([.P], 3678705659225434098228818120286891844954088041683851688565340692317698911901313017456012998913009489230694167801319831984847646376692757028994922441929364863417250489911386463802027912027584080514708752870874066639329972444105983638435075246721926174549699741483107114227196372658039071296782827051509661858314572793653441347842194468646464567742838061333785657958292342484192642430152961424317639416491032092332556946655853698568605460956271093028186989040125711733640161943451495870186848682356605263969012907501544770057817489759361157529680656906329439534653310017272717783302060770290495190029091248848764707743899887724946655731494520969764242971470588327865224747432563277580159872091630292869025752336276399655350203616260234728891821081398846364803443421687192928779083618267595045050885985536873885043988737127311793538689482980311348839798725969101924060374855910896169939017272250643593428779734106912441336563147435943857839374518013311326808644372238259487806388731815357703228535769853380267465668638358798498782930423752734996391543954108564876258471077339069790104354194021860307666102387461977370715529111052125541190979461891319611177862034019374362319864444249826838265293443867642360770991040559442371208902547654407669268935056405505720040631206488471075157497290156565696810487792386610060068771961484227660549812477074573892599991643964882044481292735515480640110036154649423687096973173538206819964227785495368639969017474953512911910462050476769405019068379143857749758837608940599306623590693550181853364632503414795863121312257824228396748604038617539244016345423173760468728224382176317924861890182807955316004470568716765309718908711212621128368703294474479204591096836230979148842399370181633856992123874360182357784402588790676716584810475971849828806122994404287958569622118384728124862173527371851906170360376957638329842163116874963625025368550244409844247947695157417922999120325420026518614896628350642385274338462205208506755074676649874403258754087764068975561911816142978226648926552829265026006093765051732548593964993710082882063031838177175370846946076767253823886742673585108875114289290189510535553093630586577943625271674823452074892766950737901336026948513591763842494336684913030162), ([.T], 2), ([.P], 1), ([.Z, .P], 1379514622209537786835806795107584441857783015631444383212002759619137091962992381546004874592378558461510312925494936994317867391259783885873095915723511823781468933716769923925760467010344030193015782326577774989748739666539743864413153217520722315456137403056165167835198639746764651736293560144316123196867964797620040505440822925742424212903564273000169621734359628431572240911307360534119114781184137034624708854995945136963227047858601659885570120890047141900115060728794310951320068255883726973988379840313079288771681558659760434073630246339873539825494991256477269168738272788858935696260909218318286765403962457896854995899310445363661591114301470622949459280287211229092559952034361359825884657126103649870756326356097588023334432905524567386801291283132697348292156356850348141894082244576327706891495776422741922577008556117616755814924522238413221522640570966586063727131477093991347535792400290092165501211180288478946689765444254991747553241639589347307927395774430759138710700913695017600299625739384549437043598908907275623646828982790711828596926654002151171289132822758197615374788395298241514018323416644547077946617298209244854191698262757265385869949166593685064349485041450365885289121640209790889203338455370402875975850646152064645015236702433176653184061483808712136303932922144978772525789485556585372706179678902965209724996866486830766680484775818305240041263557993533882661364940076827557486585419560763239988381553107567341966423268928788526882150642178946656159564103352724739983846510081318195011737188780548448670492096684085648780726514481577216506129533690160175773084143316119221823208818552983243501676463268786991144590766704732923138263735427929701721661313586617180815899763818112696372046452885068384169150970796503768719303928489443685802296122901607984463608294394273046823315072764444464813885141359114373690811168828111359384513206341653691592980385684031721124670122032509944480586235631490894477876923326953190033153003743702901222032782911525865835716931053616834993347457310974384752285161894399705722736872641281080773636939316440764067604778787720183957528502594415828167858483821066450832410111469966728859476878058794528084787606526713001010105692596911440935376256842386311), ([.P], 1), ([.Z, .P], 675896608994219585481855507818365167273435133282861899071405061725852787641170382964597523682795730711754757261086522680159273235708004779459262145047268735496341831625979084147217521893857368917854753074627012542504046033825558639285074589765921646122745043970334758417701506839504592166788758122712306909302786768325736373747997439138088292218698853529118517237954198581708042598382193052536880460952251501814016799799665609308250075230591225918479406636999329965943895817271770914623600249440266140016360874299246480930232798915839718511920721347732643270470804011302637564867035647818669842170150939365281462866153743276358537945158478713586407754028778531004079221986976038713380841535884831557468840349315208384237361705960949878715729505473175464799924181026858507174202225928184658421586074175553495076394268958055192228795745612510392875610618147727123802194693775890766907741312444347053748243990894448194322526996203364284503940844224326955362847543964744966641699319990899058012088716978517550010572523505444920879895350728194406127060486901596894150964340734601597479316595187395090337883749827743846379638978829397642801222656645669359351313166725743346691593780316959334517728725117076494878758451359063707336582969455799569305091447690229201712200728185812395926034662102052633525964109733608683343691813777173415100047208452581719920926690048893356257282787341118258976897001378259543937096777206635209333740707809894868757258461284237818107479433583204867960321260603123093830522983785061050371866131830752011961041987034963517915445779088926031774232106868272875041684598292897103734659029736408305046314174782938773236007530161728345299281610977977617478269491288779906424741621647889432855192649178536792943796276441054357500468268504160387398770229121562104571282680576614896963224618164172678374218860025100504173963008765677292491510224748761065212332519426898269405781979888198641141106081935454758304454129670356097337591936275669105006823489499512029506233822522931801364317789014812041824094293985514136444562875762867538817186838338153661720795457017422589982699859626400255018683972593959649966292397333545559955264420975325879402185558222136729542712836854753362910728320466727656411762182373673667), ([.M], 1), ([.T], 1), ([.P], 1), ([.Z, .P], 358739357662933754644999588512323164119902128440721388337597007988500031331073903194906132261488188134377977433034680065579127307736833134945559791745365132339759868661598358797102828363900653726907083670306318699807508716079249259024790323374620090469358008321789117458697472970568896635431411985524785488348186829889294005332619755168729867458974351221008699062815522741971138085098327348052455624935851274154514841447293243414170210663360018995698184030536026459142399729323962298866450942472529090474924005935562985648528370078980607043301963407172511598650439431055314311686668943825531930025530974373433611186818100146282708979324355309159785581697324436208015238228432383106039122489886188311944652495262529018829883061112241138785095173670250075301044281322664504044915041709576447998975609256692285092227563359001249703960671475702173985582773531082792339785734449048780887607295376146456903600309323120929803381389012994925513383238966916855302083685727265514303847510832170296020936968292745650214146781032967156902803830952262311608061250191436977296730649767011780987533021881253121193207546645937289134103583654012665658740317011264281292460530342205692710868094628304463744385055970697919088082778798279459565920872072002587676796536923819282049226798639070093962011450754481468701985581875125396050650300390265614429587550724642187372820959816229718753080794522610671054050667116890868058926927850985458781198356860677561234027703546437688367338018113386527201291721031086898289150093729482504616018750730236634297760904550447818587423293424138204811312778992910037337912551974723028095154077750681111321092439131798659390249817289861898059161464050572074875428310282167369866504363542073452756732173685047729335238563222746930626394959593217439140707717245520659780439411599591091384481602631532106743267444548232844436450847253658487776598151872322454326052385329341999288953309374825149702396509588927700055985547053262073520815756219545787518041263308265146410290764660712598012469909275400584420916298997716652119650995657932240474865816142807148859432247469907983068003724464389882949462404351852221159601465532254278169043162627149167242422100321959166520877868040281387846850948980955924289770010258116065), ([.Z], 1), ([.T], 1), ([.P], 1013844913491329378222783261727547750910152699924292848607107592588779181461755574446896285524193596067632135891629784020238909853562007169188893217570903103244512747438968626220826282840786053376782129611940518813756069050738337958927611884648882469184117565955502137626552260259256888250183137184068460363954180152488604560621996158707132438328048280293677775856931297872562063897573289578805320691428377252721025199699498413962375112845886838877719109955498994948915843725907656371935400374160399210024541311448869721395349198373759577767881082021598964905706206016953956347300553471728004763255226409047922194299230614914537806917737718070379611631043167796506118832980464058070071262303827247336203260523972812576356042558941424818073594258209763197199886271540287760761303338892276987632379111263330242614591403437082788343193618418765589313415927221590685703292040663836150361611968666520580622365986341672291483790494305046426755911266336490433044271315947117449962548979986348587018133075467776325015858785258167381319843026092291609190590730352395341226446511101902396218974892781092635506825624741615769569458468244096464201833984968504039026969750088615020037390670475439001776593087675614742318137677038595561004874454183699353957637171535343802568301092278718593889051993153078950288946164600413025015537720665760122650070812678872579881390035073340034385924181011677388465345502067389315905645165809952814000611061714842303135887691926356727161219150374807301940481890904684640745784475677591575557799197746128017941562980552445276873168668633389047661348160302409312562526897439345655601988544604612457569471262174408159854011295242592517948922416466966426217404236933169859637112432471834149282788973767805189415694414661581536250702402756240581098155343682343156856924020864922345444836927246259017561328290037650756260944513148515938737265337123141597818498779140347404108672969832297961711659122903182137456681194505534146006387904413503657510235234249268044259350733784397702046476683522218062736141440978271204666844313644301308225780257507230492581193185526133884974049789439600382528025958890939474949438596000318339932896631462988819103278337333205094314069255282130044366092480700091484617643273560510500), ([.M], 1), ([.T], 1), ([.P, .Z], 133800715405386209884298590957236470080396736417778027965825272670445694068321952402838555755864119524830828989959371103025999063362838037529218180299240582581683015625598118507079636332950489221181048029947792714887601680924224269797307424883830343791272655664230192279579826788457246552291380401625985599465221849027874124175237460424573085445508774411233829542636628869889006591541630844079366727694418846043852388679907091861564942864300665420548328287101706166931881162102981759772547363877014067775293678840928974571969055915549937650823538506173805549049216307291839497435467203247105056686011547730935812427219724445500740344961270811242481228952332196242089493148135604709347287722530677619205516750928474107281280053295548999658236358729359148694839957687706845070168030842225338772038789887644572962070328924600882002664796901465967344230496947646827335703779716011462852244038450647126793834053162903689719014553033437073324141489717969885963134752693936643955031231988838696465017143976810020226617110105576556677835484905471352375202802987098714922879838376951953832471194988528643232910273217324641337960244839615537231984737033264642306078455974304947773118648649901273607504360421128461661691299361580854528248072333789351624436915479579184857817126527531908641072292287256585160115941440297636826751888460101728407850168103974490293732104941904972072085215720307888654950797266514910136102905196914738514353804306701051611362975920634429734122159651329612507715587006952769994016687992197198990748113901779924951696706673155060654009486139832364499981591447418697156278832040479688160416151618978659852827919727824735528679035117818657429425686984999213285573623237164663860506343263391116604038013098815698709860285263973445712499677196804056296370122197704984521137004099681917978532209677832741156807628404303543951762943137882933239103530744747538967649431572406551455537095372829441700705600833691102698572683291586541297702450961177024565580001674432278806100977535623726414060824265064208591965716635477063699572199419269578988166681238661810113387604027857724792137432021473125716702849102139071527822736853669759503562093365637050442400208801637409399836627468605364480073266095559949488965447611250862), ([.Z], 1)]
def ckptK1_6 : Nat := 2

def ckptRle_7 : Rle := [([.Z], 1945563510843319212831356701884863521398873748211661979324002778135784218950069339966316099744925468539581122164710365510917147284474354314798858962659066439025116385848893699054696620538505955194150362775720900831669056634452319327065704388215019695515937527898730043914088129726533099169473489580961680777858973567889015306976182311533421012328015111808609273877558398108580227280583605002757015767666878160970846702917811649228100166795034632756665110288647098234394206697880015167462063286022467008914434027568305748076688723692417410972416805860166773101903708172057601543608156543302585943968154316731787020396729369069445827505135103025288235593862745788118225147108943766529382511685648920928265459895081087790714138660839068905350680860310364621205070576076894111107913884238990274207359330002119223160866657052517205703540832031700524488121181502942085774011985753733738626195993559593461083487729012842043232742834761589807338148704929711811539667572676751153308142032539722897803985971189284178358899761868888825718442031066741593105740973524469481736875304137630828323522628269422902882602873550116025539637288479942032167094294343167824835578732122303696606619503417162966193913577293374462118126342694304814637966764903053207484044455960277408257844066187597303790862491277016748646235114143510985206145573844063871057430693910288034743620446597434419353493086002536841035142547993142544327467016590302537438210234635102818443442147762312668609429863037442454002007736662297479671719445555626130365321373656298792019796202658379271289090368505641750627822011862773290074862385247776120625037564724813081959591223375857932319544904474059694657365293608775744113721862699676476670076702820752868856558308007686859804943476686559033846380195880177501917354049649318846706450862950612369157744291854092889363388034182038450311893255412289983486150974746425177979048875687218689099023051699043629143313296591219412803563698026524563500297518686791658619486279407523863447704686261583399165625073891522974155212468443283916996384102028212778622716877672441226087392110606246691153742976350840169344445107986981640650178519177583009324269179646589043351769334295895417396698859789415771979665699495641091060292800159194300374179648052649803271111408660761558475572552268132443031242768705897792642482223695756362629901037145202929904984017463439978679227691935725766295114272033343207006877123917167553158324072783896509658062123547068592485693165541881196610702608338232723621904046527118792869706099590396860351218449446069474412936573405285248612152519754662709466556016115874512899880145162417), ([.P], 988628497454093300360856464388224049785741612720872469517375252361863716965888385772419958651597977384530312196300802260511822701569697165789883921156185544253725906649851037206925803551879334069227297897983741938660845841537691634270545505711877130652480264622499743480006613839041521914476213760313881427369836330841106648556803223345787716549794599323911026387127920846256551876762667773993116157327515317587266752071256609152947213174623127596386248373190650928024214307180766327960657247659573455718886304020589133698659840749054198072606803786376064786086265977798829987706237453960000122657301720874350990685543752522981776913578461685917868586251182416827970887772897881838682064647874038476449755393772773920763004942579757546613095678541776838135537349211011531964288939868647436007746741589067360306535512355996703754349791401601925255646357806518787580884687410057209514750128237446213548190821633338938377541795999245427070104457849836317076666988327478722195284777176992366678398816632271811678568148911616694019947921493902520587084904917576733674499002643539280004824488930960615394625847814080955427305582915461625976941434824676301954202819467855510992674012824404986448238962254843729353366578537944307414429366208465859950423779137484602162889015083554943846641005525841982799011386479464232494466481548466938521275870442998325383693457614047085744013401073940688485574515915421481948089214672848738851627994971832567731040430257103827503257850141558897405181933724890401828429613624490876113698084461378464648822719626704377628291045161576696945065085338354536876923234644039387811069920671996278924412971830764432077000612279416659348186751752330932517240235463384949233005087931568060054518659841955980425258733367420931170333622722228127757884962089936277217600209609921755005424522144882991996960614040064365922458481213367567708450201020077050902909080885770400459533295057772051027817999165585750370514799466867148884485308692985036041661666474203713489151721372042408600986772089824426878989355991958837013560934603753544523683778446275574278771722315790158697445970206339531949284919022873488860706052521450771741648554009476608414243311547385144618881400393587194001795644089729156081588737393616747045072143395124724646741332331957731289578989550281093376220686333490394394488440304853129096180984808564176093810844070155855991162846788029020483016746912543661729356645548158803617371929255883678243011710461164997620405439113344743604736931835129315624043631728138188029570632175928773211763619941471807241817413370688051122952888605416300702179207475765723053226849031105), ([.Z], 1), ([.P, .Z], 68707772023836600025078827640880435892445363046238241124759670048314852916548227582639224925593681825951913588932102087603138257251948065576130928883441466396011839072190419574226503721752231711374870124184198281451332915628102121300655672211636248462334535765270252442625942274527982217994485898400192531631880517201312431173831884247969802694580319644132812644665260908234046076377328262285235871937819597361277226012674204497116022537232495354189005678445682303878130724051172949433559190957035993061544221901044804658594120206497975155625183274728838479341902654827717914203522294097606186130623285620611265761929681642523830055769931700179620210627495303100013420771861628853653579782477732403768708869065289307234494551993959983934500857968154374851118425813892693341147493890485149992816375863332866739450344488061546979066780869609400210817121391958834658130982136606292553148657560903597852770018491892281431643831382186940877458997070644995009189211543994660229788131232377847877263238221547847915885045098104635105633446281429518805280032001993749830660162345883038764814057145781046629742336913719911960198843600302352384497860335305688938902126449503471806440664983935481683661395060182189684789955265185318662006674099430059764894316696813601694718155488432389919843776445811411931977625315175120405020836555491910785262415706463204080720008637269681634719078066914796883167340874430836583264887506221147873858316252868672660844508666516868320689734758872819124684458714471147617419818707493574401724191198088078624242505611122311958722929779569036853324986625831589435461846423137872511966249313111710504399357115651582152069540621735520726901009774293269441352603236837564039359426960495077532746470568166824894419525871094890969366815478764889187806676902003293397362176729647071776438769878794956972761741516297909600788620315986935207537079607572922456572831876231147522284167224092266094597389903399781879031916565264898378072338055883129917953320449944659624728691060605263918215296901995520014756017018746174000942458775550439387746362980822240683466760624263408712563812601212786004197407499659161388002737240873026607527698734249339580912662578582751363474383038936561745298538971486968376326630398011974698113121934796312909812138926545324954488115103880539307999893258698174127802285426592109358035744117969711079878745919933611613285448811523252388781086658014617417484245636551577085377199716625120495653323506953551958174895382394615385657392946070763248003032320874468666147765942728640609311757370449778109469936064372142549085528937828159894359944921095687316440475994438), ([.Z], 1), ([.P, .P, .Z, .Z], 25765414508938725009404560365330163459667011142339340421784876268118069843705585343489709347097630684731967595849538282851176846469480524591049098331290549898504439652071407340334938895657086891765576296569074355544249843360538295487745877079363593173375450911976344665984728352947993331747932211900072199361955193950492161690186956592988676010467619866549804741749472840587767278641498098356963451976682349010478959754752826686418508451462185757820877129417130863954299021519189856037584696608888497398079083212891801746972795077436740683359443728023314429753213495560394217826320860286602319798983732107729224660723630615946436270913724387567357578985310738662505032789448110820120092418429149651413265825899483490212935456997734993975437821738057890569169409680209760002930310208931931247306140948749825027293879183023080117150042826103525079056420521984562996799118301227359707430746585338849194788756934459605536866436768320102829047123901491873128445954328997997586170549212141692953973714333080442968456891911789238164612542355536069551980012000747656186497560879706139536805271429667892486153376342644966985074566350113382144186697625739633352088297418563801927415249368975805631373023147568321131796233224444494498252502787286272411835368761305100635519308308162146219941416167179279474491609493190670151882813708309466544473405889923701530270003238976130613019654275093048831187752827911563718724332814832930452696868594825752247816690749943825620258650534577307171756672017926680356532432015310090400646571699283029484090939604170866984521098667338388819996869984686846038298192408676702191987343492416891439149758918369343307026077733150820272587878665359976040507226213814086514759785110185654074779926463062559335407322201660584113512555804536833445427503838251235024010816273617651916164538704548108864785653068611716100295732618495100702826404852839845921214811953586680320856562709034599785474021213774918204636968711974336891777126770956173719232495168729247359273259147726973969330736338248320005533506382029815250353422040831414770404886117808340256300035234098778267211429725454794751574027812372185520501026465327384977822887025343502342842248466968531761302893639601210654486952114307613141122486399254490511792420725548617341179552097454496857933043163955202240499959972011815297925857034972041009263404044238641654954529719975104354982043304321219645792907496755481531556592113706841407016449893734420185869996315107581984315585768397980769621522354776536218001137120327925749805412228523240228491909013918666791051226024139553455907073351685559960384979345410882743665178497915), ([.Z], 1), ([.P, .Z], 38648121763408087514106840547995245189500516713509010632677314402177104765558378015234564020646446027097951393774307424276765269704220786886573647496935824847756659478107111010502408343485630337648364444853611533316374765040807443231618815619045389760063176367964516998977092529421989997621898317850108299042932790925738242535280434889483014015701429799824707112624209260881650917962247147535445177965023523515718439632129240029627762677193278636731315694125696295931448532278784784056377044913332746097118624819337702620459192616155111025039165592034971644629820243340591326739481290429903479698475598161593836991085445923919654406370586581351036368477966107993757549184172166230180138627643724477119898738849225235319403185496602490963156732607086835853754114520314640004395465313397896870959211423124737540940818774534620175725064239155287618584630782976844495198677451841039561146119878008273792183135401689408305299655152480154243570685852237809692668931493496996379255823818212539430960571499620664452685337867683857246918813533304104327970018001121484279746341319559209305207907144501838729230064513967450477611849525170073216280046438609450028132446127845702891122874053463708447059534721352481697694349836666741747378754180929408617753053141957650953278962462243219329912124250768919211737414239786005227824220562464199816710108834885552295405004858464195919529481412639573246781629241867345578086499222249395679045302892238628371725036124915738430387975801865960757635008026890020534798648022965135600969857548924544226136409406256300476781648001007583229995304977030269057447288613015053287981015238625337158724638377554014960539116599726230408881817998039964060760839320721129772139677665278481112169889694593839003110983302490876170268833706805250168141255757376852536016224410426477874246808056822163297178479602917574150443598927742651054239607279259768881822217930380020481284844063551899678211031820662377306955453067961505337665690156434260578848742753093871038909888721590460953996104507372480008300259573044722875530133061247122155607329176712510384450052851148167400817144588182192127361041718558278280751539697991077466734330538015253514263372700452797641954340459401815981730428171461419711683729598881735767688631088322926011769328146181745286899564745932803360749939958017722946888785552458061513895106066357962482431794579962656532473064956481829468689361245133222297334888170560262110524674840601630278804994472661372976473378652596971154432283532164804327001705680491888624708118342784860342737863520878000186576839036209330183860610027528339940577469018116324115497767746871), ([.Z], 2), ([.P], 1), ([.Z, .P], 18445694477990223586278264806997730658625246613265664165595990964675436365380134961816496464399440149296749528846828543404819787813378102832228331759901189131883860205460212073194331254845414479332173939589223686355542501496749006996908980181817117840030152357437610385875430525405949771592269651701188051815945195669102343028202025742707802143857500586279973849207008965420787938118345229505553380392397590768865618915334410014140523095933155712985400672196355050330918617678510919663270862344999719728170252754683903523400978294074030261950510850743963739482414207048918587762025161341544842583363353668033422200290781009143471421222325413826630994046302006087929739383354897518949611617739050318625406216268948407766078793077923916141506622380655080748382645566513805456643290263212632597503259997400442917267208960573341447505144295960478181597210146420766690890277874742314336001557214503948855360132805351763054802108140956437252613281884022590989682899121896293726463006822328712001140272761182589852418002164121840958756706459076958883803872227807981133515299266153258986576501137148604848041621699848101364314746364285716762315476709336328422517758379199085470763189889153133577005687026100048082990485149318217652158041768170854113018502635934333409519504811525172862003513846957893260147402250806957040552468904812459003429824671195377231897843227903366234320888856032523595054868501800324025904920083346302483180712744022981722868767241437056978139715723617844907053072012833873437062991101869723809553795648350350653383286307531416136645786545935437450679577375400810231963478656211729978354575454798456371209486498378052594802760195323882695148140408155437392635855130344175573066664340246547803535629172419786796939332939825190899446488814611596671158326611475315983098652559521728076345067481665123391835183446847024026348081306422628912250721656010344239051513103135918866067766484877043028237083368952498260137829873345263911158624847389078912632354495794802086752446889849992728043595333064138185779669341680435917866654415595217392448952561612789047123888860775261714026364462541500788058679002039178270358689401313923336395930484052734631807518788852471601841844310169048536734977081833859407849052763102646616396846655790487414708088433404923886929337719649747058539744070872095042833284013673165722540846077125391184796992867709449708680326456502691337329013321540856096455287535949216007295867537559868996702383725588382556953203447830372596433589867624111156068995892962037752701601936329137890852162134964500089048036812736271224115291149502162244366519304100972873305752788278), ([.P, .Z, .Z, .P], 5270198422282921024650932801999351616750070460933046904455997418478696104394324274804713275542697185513357008241951012401377082232393743666350951931400339751966817201560060592341237501384404136952049697025492481815869286141928287713402565766233462240008614959267888681678694435830271363312077043343196586233127198762600669436629150212202229183959285881794278242630573990120225125176670065573015251540685025933961605404381260004040149455980901632281543049198958585808833890765288834189505960669999919922334357929909686720971708084021151503414431671641132496994975487728262453646292903240441383595246672476580977771511651716898134691777807261093323141156086287453694211252387113576842746176496871519607258918933985259361736798022263976040430463537330023070966470161861087273326654360917895027858074284971555119219202560163811842144326941702993766170631470405933340254365107069232667429016347001128244388609372957646587086316611701839215032366252577883139909399749113226778989430520665346286040077931766454243548000618320525988216201845450559681086820636516566038147228361758073996164714610613887099440463342813743246947070389795919074947279059810379549290788108342595848789482825472323879144482007457156595140138614090919329188011933763101175148143610266952402719858517578620817715289670559398074327829214516273440157848258517845429551378477484393494827955207972390352663111101723578170015676714800092578829977166670372138051632212577994777962504926124873422325633063890812830586592003666820982017997457677063945586798756671528758109510373580404610470224727410124985908450678685945780560993901774779993815592987085273248916996142393729312800788627235395055756611545187267826467387180098335878019046954356156515295894049262796227696952268521483114127568232746170477473807603278661709456757874149065164670019280475749540524338127670578293242308944692179689214491901717241211157575172324548247447933281393440865210595248272142360039379963812932546045321384968308260752101284512800596214984825671426493726741523732610910222762669051553119390472690170062112128272160460796870606825388792931918293246989297571653731051143439765220102482686089692381827408709729352751945005368243563314811955517191156724781422023381102687956872218029327604684813330225853547059453838115692539122667919899927731011355448820598583666652575335190206440241736321540338513426533631271345337236130429340382094003806154530313272939295985490287798819296445676856200681064453823587700915270808677884695311390749746044591141683703439357914743410379753683100617752847000025442296232210363206890083185572046355533291229743135106658786510937), ([.P], 1), ([.Z, .P], 7905297633424381536976399202999027425125105691399570356683996127718044156591486412207069913314045778270035512362926518602065623348590615499526427897100509627950225802340090888511856252076606205428074545538238722723803929212892431570103848649350193360012922438901833022518041653745407044968115565014794879349690798143901004154943725318303343775938928822691417363945860985180337687765005098359522877311027538900942408106571890006060224183971352448422314573798437878713250836147933251284258941004999879883501536894864530081457562126031727255121647507461698745492463231592393680469439354860662075392870008714871466657267477575347202037666710891639984711734129431180541316878580670365264119264745307279410888378400977889042605197033395964060645695305995034606449705242791630909989981541376842541787111427457332678828803840245717763216490412554490649255947205608900010381547660603849001143524520501692366582914059436469880629474917552758822548549378866824709864099623669840168484145780998019429060116897649681365322000927480788982324302768175839521630230954774849057220842542637110994247071915920830649160695014220614870420605584693878612420918589715569323936182162513893773184224238208485818716723011185734892710207921136378993782017900644651762722215415400428604079787776367931226572934505839097111491743821774410160236772387776768144327067716226590242241932811958585528994666652585367255023515072200138868244965750005558207077448318866992166943757389187310133488449595836219245879888005500231473026996186515595918380198135007293137164265560370606915705337091115187478862676018028918670841490852662169990723389480627909873375494213590593969201182940853092583634917317780901739701080770147503817028570431534234772943841073894194341545428402782224671191352349119255716210711404917992564185136811223597747005028920713624310786507191505867439863463417038269533821737852575861816736362758486822371171899922090161297815892872408213540059069945719398819067982077452462391128151926769200894322477238507139740590112285598916365334144003577329679085709035255093168192408240691195305910238083189397877439870483946357480596576715159647830153724029134538572741113064594029127917508052365344972217933275786735087172133035071654031935308327043991407027219995338780320589180757173538808684001879849891596517033173230897875499978863002785309660362604482310507770139800446907018005854195644010573141005709231795469909408943978235431698228944668515284301021596680735381551372906213016827042967086124619066886712525555159036872115115569630524650926629270500038163444348315544810335124778358069533299936844614702659988179766406), ([.M], 1), ([.T], 1), ([.P], 1), ([.Z, .P], 5928973225068286152732299402249270568843829268549677767512997095788533117443614809155302434985534333702526634272194888951549217511442961624644820922825382220962669351755068166383892189057454654071055909153679042042852946909669323677577886487012645020009691829176374766888531240309055283726086673761096159512268098607925753116207793988727507831954196617018563022959395738885253265823753823769642157983270654175706806079928917504545168137978514336316735930348828409034938127110949938463194205753749909912626152671148397561093171594523795441341235630596274059119347423694295260352079516145496556544652506536153599992950608181510401528250033168729988533800597073385405987658935502773948089448558980459558166283800733416781953897775046973045484271479496275954837278932093723182492486156032631906340333570592999509121602880184288322412367809415867986941960404206675007786160745452886750857643390376269274937185544577352410472106188164569116911412034150118532398074717752380126363109335748514571795087673237261023991500695610591736743227076131879641222673216081136792915631906977833245685303936940622986870521260665461152815454188520408959315688942286676992952136621885420329888168178656364364037542258389301169532655940852284245336513425483488822041661561550321453059840832275948419929700879379322833618807866330807620177579290832576108245300787169942681681449608968939146745999989439025441267636304150104151183724312504168655308086239150244125207818041890482600116337196877164434409916004125173604770247139886696938785148601255469852873199170277955186779002818336390609147007013521689003131118139496627493042542110470932405031620660192945476900887205639819437726187988335676304775810577610627862771427823650676079707880805420645756159071302086668503393514261839441787158033553688494423138852608417698310253771690535218233089880393629400579897597562778702150366303389431896362552272068865116778378924941567620973361919654306160155044302459289549114300986558089346793346113945076900670741857928880354805442584214199187274000608002682997259314281776441319876144306180518396479432678562392048408079902862959768110447432536369735872615293021850903929555834798445521845938131039274008729163449956840051315379099776303740523951481245282993555270414996504085240441885567880154106513001409887418697387774879923173406624984147252088982245271953361732880827604850335180263504390646733007929855754281923846602432056707983676573773671708501386463225766197510551536163529679659762620282225314593464300165034394166369277654086336677222893488194971952875028622583261236658607751343583768552149974952633461026994991134824802), ([.M], 1), ([.T], 2), ([.P], 8893459837602429229098449103373905853265743902824516651269495643682799676165422213732953652478301500553789951408292333427323826267164442436967231384238073331444004027632602249575838283586181981106583863730518563064279420364503985516366829730518967530014537743764562150332796860463582925589130010641644239268402147911888629674311690983091261747931294925527844534439093608327879898735630735654463236974905981263560209119893376256817752206967771504475103895523242613552407190666424907694791308630624864868939229006722596341639757391785693162011853445894411088679021135541442890528119274218244834816978759804230399989425912272265602292375049753094982800700895610078108981488403254160922134172838470689337249425701100125172930846662570459568226407219244413932255918398140584773738729234048947859510500355889499263682404320276432483618551714123801980412940606310012511679241118179330126286465085564403912405778316866028615708159282246853675367118051225177798597112076628570189544664003622771857692631509855891535987251043415887605114840614197819461834009824121705189373447860466749868527955905410934480305781890998191729223181282780613438973533413430015489428204932828130494832252267984546546056313387583951754298983911278426368004770138225233233062492342325482179589761248413922629894551319068984250428211799496211430266368936248864162367951180754914022522174413453408720118999984158538161901454456225156226775586468756252982962129358725366187811727062835723900174505795315746651614874006187760407155370709830045408177722901883204779309798755416932780168504227504585913720510520282533504696677209244941239563813165706398607547430990289418215351330808459729156589281982503514457163715866415941794157141735476014119561821208130968634238606953130002755090271392759162680737050330532741634708278912626547465380657535802827349634820590444100869846396344168053225549455084147844543828408103297675167568387412351431460042879481459240232566453688934323671451479837134020190019170917615351006112786893320532208163876321298780911000912004024495888971422664661979814216459270777594719149017843588072612119854294439652165671148804554603808922939532776355894333752197668282768907196558911013093745174935260076973068649664455610785927221867924490332905622494756127860662828351820231159769502114831128046081662319884760109937476220878133473367907930042599321241407275502770395256585970099511894783631422885769903648085061975514860660507562752079694838649296265827304245294519489643930423337971890196450247551591249553916481129505015834340232292457929312542933874891854987911627015375652828224962428950191540492486702237204), ([.Z], 1), ([.T], 1), ([.P], 4366979736716783742934789402864648294053794674952660182135893139656051301725839055597095995424036564020249530112070554114700989740444705271803917245899176108679427324384369766001534137188077444308524576834417798710536770658337862854252262145895556340090950266366338166769389267507721519008617665495486013975595680040570711422460892782631946656714280887998783734773361141254629940395470401326545038040239881508307619916456116279862232467215778137102429477582801961390609719780699544855643547417024918472573241801217811145989816562893405351219477868988372000999672484695223400552625944362310159466099015268330237685667275298041943187837450905431158023267288284185139625034568566159045516687462222178839725639811553475982111260120211300872937027692226387135062572761181162296113502239461427109179989972710491643028464682596865834222779699488941204235063431642022462309040290646822358599272822029883650802173614261171183608258805966118499764203626740238255354669502335193836393416129914804004460473814496032597544253251194747633392134005069050143084039750703882229047485504418100701562049157017983309542781229114771284509166530580534011298529740689408713799532428045363472573096925288010114781088071211051358865289026176439685517054668161833218329158119079853561345222177689980883641304607244243759830443707774455377601238749419707906439606820823307147416945894232171077998913983234312336711834149414044824894836258643874893167899010884790726420560507380244708518197924944657780293651052519899593408012980130910478851498031290201099146145252625931681765082146983505152085343425404576230459157592444499091437311404329577084905360549414847530225415094146034545506080492793390120359584444161102971435485423902888739714960120969826523791790381430306918840938526136332555328433607012417576664366108754237755530125540758402051364233215983015483586732897658220574777834839412852933123149686656654831097280788107827199033538702521318711714642570122171701090212899564299650041110910106161978058781997218572368565226883493791859524269584397679809796298823187917604150434331498072899185844893144833470721587315981845073459980071719535647062739483990479484461404452329731235076340633894686615302889987536060302786294488197357228322267303955251445530961780919375085995373623203000834659318603523799533341568303922377444187817018466844595535548265210919356910205221732981927103394004592561393978394057382862000356276153512305510733262460839190395682629625928380298295431417199659614287411161430095640288927093586303658782240183746039980299690910941172511105684192399718817690507379698178297618212760241756313566709348715), ([.Z], 3275234802537587807201092052148486220540346006214495136601919854742038476294379291697821996568027423015187147584052915586025742305333528953852937934424382081509570493288277324501150602891058083231393432625813349032902577993753397140689196609421667255068212699774753625077041950630791139256463249121614510481696760030428033566845669586973959992535710665999087801080020855940972455296602800994908778530179911131230714937342087209896674350411833602826822108187101471042957289835524658641732660562768688854429931350913358359492362422170054013414608401741279000749754363521417550414469458271732619599574261451247678264250456473531457390878088179073368517450466213138854718775926424619284137515596666634129794229858665106986583445090158475654702770769169790351296929570885871722085126679596070331884992479532868732271348511947649375667084774616705903176297573731516846731780217985116768949454616522412738101630210695878387706194104474588874823152720055178691516002126751395377295062097436103003345355360872024448158189938396060725044100503801787607313029813027911671785614128313575526171536867763487482157085921836078463381874897935400508473897305517056535349649321034022604429822693966007586085816053408288519148966769632329764137791001121374913746868589309890171008916633267485662730978455433182819872832780830841533200929062064780929829705115617480360562709420674128308499185487425734252533875612060533618671127193982906169875924258163593044815420380535183531388648443708493335220238289389924695056009735098182859138623523467650824359608939469448761323811610237628864064007569053432172844368194333374318577983553247182813679020412061135647669061320609525909129560369595042590269688333120827228576614067927166554786220090727369892843842786072730189130703894602249416496325205259313182498274581565678316647594155568801538523174911987261612690049673243665431083376129559639699842362264992491123322960591080870399275154026890989033785981927591628775817659674673224737530833182579621483544086497913929276423920162620343894643202188298259857347224117390938203112825748623554674389383669858625103041190486986383805094985053789651735297054612992859613346053339247298426307255475421014961477167490652045227089720866148017921241700477966438584148221335689531314496530217402250625994488952642849650006176227941783083140862763850133446651661198908189517682653916299736445327545503444421045483795543037146500267207115134229133049946845629392796761972219446285223721573562899744710715558371072571730216695320189727744086680137809529985224768183205879383329263144299789113267880534773633723213659570181317235175032011539), ([.P], 1), ([.Z, .P], 1151557570742519089444523712332890547947756626082863653158114296553024227699113802351309621967344780697546466722074347977895939979964313277960753146139689444951787848170040960590172287750779520760706660481735561793836397307520063141511430075996834653709976520728541722990104188919982837591614921242873582737852965446672880416636437727343249827117095153073549833027979532495639991828126325207151194845469802219681268461731957956375540844005025245626949222029814999386847836609559567957724967027971865089565589976912068055120000740472932260144706107716218157754796683480429383671731755650686733323317527292421281153201079453078629265721918204695039538629191711686721055540866937230823041971083315419081605714732135808948793437438358271901616388861103461657064683018712138142095272343037641892726442647103316402366669278805229264245567043051955140537321011545243460725195273993837618057787996071709641751080061694175139086430327859510878380567455839322546796582277568116902882540936401137444404499908947943027223092515683584035221998227789657226645733808693698331491300195465980849916958886020108775343277594566936256204109715752463033965810159691551451635810635787867199275546137850199897380573484738456228429474453641190045243261467753545853233855568832129036673549379310230544389804441028747213995357570923851597549268976383470107668178282371439184737342457928942731045168002442295642357128346377411172593426796461657422026849004079616957219117394873274108306340710771076104208752226060460355979257526120811788640897072561101242668101906968383951680648011822467141602519732403661949031675157244603419117774234975110935377606346651108065644041506099381160967940497042122861256601227825426687091185438852060924978202892564199975943582416708597573738382509216519727612177070443569324683421537857836421752683805546859230430941113425030084399032180233909672192128236849015237374078195408300772289504885577873197999310454286555731355098848289285526249198489143107746236633639052675638262904086385913393778840178740146911863207209310346053466134087654283628255955060792561570087959244773110494184151702423947025396690765848208604814732582795893718144454847960740420802028392644286602502995606954498713507596380072175430561574548494058152074127545073860404750873820331086267583903991299773250609839217995596319132645073595877754745191341160515067010425117447047934669522736491036263554664754890732713689893821484665317381059105612434687723178673135495089944269736208786666765046158743775848698368299925430889289303472507917887437264216252905948047360988245761058014877076020721435551804476200949527899158664593), ([.M], 1), ([.T], 1), ([.P], 1)]
def ckptK1_7 : Nat := 2

theorem ckpt_step_0 : truncRes 30 (runCarryChunk 3746 ckptRle_0 ckptK1_0) = .next ckptRle_1 ckptK1_1 := Eq.refl _
theorem ckpt_step_1 : truncRes 30 (runCarryChunk 3999 ckptRle_1 ckptK1_1) = .next ckptRle_2 ckptK1_2 := Eq.refl _
theorem ckpt_step_2 : truncRes 30 (runCarryChunk 4000 ckptRle_2 ckptK1_2) = .next ckptRle_3 ckptK1_3 := Eq.refl _
theorem ckpt_step_3 : truncRes 30 (runCarryChunk 4000 ckptRle_3 ckptK1_3) = .next ckptRle_4 ckptK1_4 := Eq.refl _
theorem ckpt_step_4 : truncRes 30 (runCarryChunk 4000 ckptRle_4 ckptK1_4) = .next ckptRle_5 ckptK1_5 := Eq.refl _
theorem ckpt_step_5 : truncRes 30 (runCarryChunk 4000 ckptRle_5 ckptK1_5) = .next ckptRle_6 ckptK1_6 := Eq.refl _
theorem ckpt_step_6 : truncRes 30 (runCarryChunk 4000 ckptRle_6 ckptK1_6) = .next ckptRle_7 ckptK1_7 := Eq.refl _
theorem ckpt_step_7 : runCarryChunk 3298 ckptRle_7 ckptK1_7 = .halt := Eq.refl _

theorem init_to_ckpt0 :
    (init []) [target_tm]⊢* (carryCfg (evalRleG default ckptRle_0) (evalWK ckptK1_0)) := by
  have h1 : evalRleG default ckptRle_0 =
      [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1] +> default := rfl
  rw [h1]
  exact stepStar_trans ⟨1500, bmultiStep_sound 1500 ⟨A, 0, [], []⟩ ⟨A, 0, [1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩ (stepStar_trans ⟨1500, bmultiStep_sound 1500 _ ⟨A, 0, [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1], [1, 0, 0, 1, 1]⟩ rfl⟩ (stepStar_trans ⟨1500, bmultiStep_sound 1500 _ ⟨A, 1, [1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩
    (stepStar_trans ⟨1500, bmultiStep_sound 1500 _ ⟨A, 0, [1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩ (stepStar_trans ⟨1500, bmultiStep_sound 1500 _ ⟨A, 0, [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [1, 1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩
      ⟨928, bmultiStep_sound 928 _ ⟨B, 1, [0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 1], [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 0, 1, 1]⟩ rfl⟩))))

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 400000000
-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_halt : IsHalt target_tm := by
  rcases runCarryChunk_trunc_sound 3746 30 ckptRle_0 ckptRle_1 ckptK1_0 ckptK1_1 default ckpt_step_0 with ⟨l1, h0⟩
  rcases runCarryChunk_trunc_sound 3999 30 ckptRle_1 ckptRle_2 ckptK1_1 ckptK1_2 l1 ckpt_step_1 with ⟨l2, h1⟩
  rcases runCarryChunk_trunc_sound 4000 30 ckptRle_2 ckptRle_3 ckptK1_2 ckptK1_3 l2 ckpt_step_2 with ⟨l3, h2⟩
  rcases runCarryChunk_trunc_sound 4000 30 ckptRle_3 ckptRle_4 ckptK1_3 ckptK1_4 l3 ckpt_step_3 with ⟨l4, h3⟩
  rcases runCarryChunk_trunc_sound 4000 30 ckptRle_4 ckptRle_5 ckptK1_4 ckptK1_5 l4 ckpt_step_4 with ⟨l5, h4⟩
  rcases runCarryChunk_trunc_sound 4000 30 ckptRle_5 ckptRle_6 ckptK1_5 ckptK1_6 l5 ckpt_step_5 with ⟨l6, h5⟩
  rcases runCarryChunk_trunc_sound 4000 30 ckptRle_6 ckptRle_7 ckptK1_6 ckptK1_7 l6 ckpt_step_6 with ⟨l7, h6⟩
  rcases runCarryChunk_halt_sound 3298 ckptRle_7 ckptK1_7 l7 ckpt_step_7 with ⟨cfg', h7, hnone⟩
  exact ⟨cfg', stepStar_trans init_to_ckpt0 (stepStar_trans h0 (stepStar_trans h1 (stepStar_trans h2
    (stepStar_trans h3 (stepStar_trans h4 (stepStar_trans h5 (stepStar_trans h6 h7))))))), hnone⟩

end BusyBeaver.M_1RB0LB_0LC0RE_1LA1LD_0LB1RF_1RA1RD_HHH1LC
