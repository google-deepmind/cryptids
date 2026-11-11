/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.WordRLE

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target


@[simp]
theorem zero_pow_append_default (n : ℕ) :
    ([0] : List (Fin 2)) ^ n +> (default : ListBlank (Fin 2)) = default :=
  WordRLE.lb_blank_pow [0] (by decide) n

/-! ## Reflective Trigram-Halfspace Symbolic Certificate Verifier  -/

abbrev b0 : Fin 2 := 0
abbrev b1 : Fin 2 := 1

@[inline]
def forceNat {α : Type*} (n : ℕ) (k : ℕ → α) : α :=
  Nat.casesOn (Nat.add n 1) (k 0) k

theorem forceNat_eq {α : Type*} (n : ℕ) (k : ℕ → α) : forceNat n k = k n :=
  rfl

def qOf : ℕ → Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 4
  | _ => 5

def stepCode : ℕ → Fin 2 → Option (Fin 2 × Bool × ℕ)
  | 0, 0 => some (1, true, 1)
  | 0, 1 => some (1, true, 0)
  | 1, 0 => some (0, false, 2)
  | 1, 1 => some (0, true, 0)
  | 2, 0 => some (1, true, 2)
  | 2, 1 => some (1, false, 3)
  | 3, 0 => some (0, false, 1)
  | 3, 1 => some (1, false, 4)
  | 4, 0 => some (1, false, 5)
  | 4, 1 => some (0, true, 2)
  | 5, 1 => some (0, false, 3)
  | _, _ => none

theorem stepCode_agrees : WordRLE.StepCodeAgrees target_tm qOf stepCode := by
  intro q a b dir' q' h
  rcases a with ⟨_ | _ | n, ha⟩
  · match q with
    | 0 | 1 | 2 | 3 | 4 =>
      simp only [stepCode] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    | 5 => simp [stepCode] at h
    | _ + 6 => simp [stepCode] at h
  · match q with
    | 0 | 1 | 2 | 3 | 4 | 5 =>
      simp only [stepCode] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    | _ + 6 => simp [stepCode] at h
  · omega

def StepRel (prog : Bool) (c₁ c₂ : Cfg (Fin 2) (Fin 6)) : Prop :=
  if prog then ReachesPlus target_tm c₁ c₂ else ReachesStar target_tm c₁ c₂

theorem StepRel.refl (c : Cfg (Fin 2) (Fin 6)) : StepRel false c c :=
  ⟨0, rfl⟩

theorem StepRel.trans {p₁ p₂ : Bool} {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepRel p₁ c₁ c₂) (h₂ : StepRel p₂ c₂ c₃) :
    StepRel (p₁ || p₂) c₁ c₃ := by
  cases p₁ <;> cases p₂
  · exact ReachesStar.trans h₁ h₂
  · exact ReachesStar.trans_plus h₁ h₂
  · exact ReachesPlus.trans_star h₁ h₂
  · exact ReachesPlus.trans h₁ h₂

theorem StepRel.chain {gProg dp : Bool} {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : StepRel dp c₁ c₂) (h₂ : StepRel (!(gProg || dp)) c₂ c₃) :
    StepRel (!gProg) c₁ c₃ := by
  have htr := StepRel.trans h₁ h₂
  cases gProg <;> cases dp
  · exact htr
  · exact htr
  · exact htr
  · exact ReachesPlus.to_star htr

theorem StepRel.of_reachesIn {dt : ℕ} {prog : Bool} {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : ReachesIn target_tm dt c₁ c₂) (hp : prog = true → dt > 0) :
    StepRel prog c₁ c₂ := by
  cases prog
  · exact ⟨dt, h⟩
  · exact ⟨dt, hp rfl, h⟩

/-! ### GMP Bit-Packed Concrete Zipper (`simZipNat`) -/

def bitOfBool (b : Bool) : Fin 2 :=
  if b then b1 else b0

def unpackBits : ℕ → ℕ → List (Fin 2)
  | 0, _ => []
  | k + 1, bits =>
    forceNat (bits / 2) fun rest ↦
      bitOfBool (Nat.beq (bits % 2) 1) :: unpackBits k rest

theorem unpackBits_push (b : Bool) (k bits : ℕ) :
    unpackBits (k + 1) ((if b then 1 else 0) + 2 * bits) =
      bitOfBool b :: unpackBits k bits := by
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, unpackBits, forceNat_eq]
    have hm : (0 + 2 * bits) % 2 = 0 := by omega
    have hd : (0 + 2 * bits) / 2 = bits := by omega
    rw [hm, hd]
    rfl
  · simp only [↓reduceIte, unpackBits, forceNat_eq]
    have hm : (1 + 2 * bits) % 2 = 1 := by omega
    have hd : (1 + 2 * bits) / 2 = bits := by omega
    rw [hm, hd]
    rfl

theorem unpackBits_zero_append (k : ℕ) :
    ListBlank.append (unpackBits k 0) (default : ListBlank (Fin 2)) = default := by
  induction k with
  | zero => rfl
  | succ n ih =>
    change ListBlank.cons 0 (ListBlank.append (unpackBits n 0) default) = default
    rw [ih, ListBlank.cons_zero_default]

def stepCodeBool : ℕ → Bool → Option (Bool × Bool × ℕ)
  | 0, false => some (true, true, 1)
  | 0, true => some (true, true, 0)
  | 1, false => some (false, false, 2)
  | 1, true => some (false, true, 0)
  | 2, false => some (true, true, 2)
  | 2, true => some (true, false, 3)
  | 3, false => some (false, false, 1)
  | 3, true => some (true, false, 4)
  | 4, false => some (true, false, 5)
  | 4, true => some (false, true, 2)
  | 5, true => some (false, false, 3)
  | _, _ => none

theorem stepCodeBool_agrees (q : ℕ) (a w dir' : Bool) (q' : ℕ)
    (h : stepCodeBool q a = some (w, dir', q')) :
    stepCode q (bitOfBool a) = some (bitOfBool w, dir', q') := by
  cases a
  · match q with
    | 0 | 1 | 2 | 3 | 4 =>
      simp only [stepCodeBool, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    | 5 => simp [stepCodeBool] at h
    | _ + 6 => simp [stepCodeBool] at h
  · match q with
    | 0 | 1 | 2 | 3 | 4 | 5 =>
      simp only [stepCodeBool, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      rfl
    | _ + 6 => simp [stepCodeBool] at h

noncomputable def simZipNat : ℕ → ℕ → Bool → ℕ → ℕ → ℕ → ℕ →
    Option (ℕ × Bool × ℕ × ℕ × ℕ × ℕ)
  | 0, q, dir, kL, lB, kR, rB =>
    forceNat q fun q' ↦ forceNat kL fun kL' ↦ forceNat lB fun lB' ↦
    forceNat kR fun kR' ↦ forceNat rB fun rB' ↦
      some (q', dir, kL', lB', kR', rB')
  | steps + 1, q, true, kL, lB, kR + 1, rB =>
    let a := Nat.beq (rB % 2) 1
    forceNat (rB / 2) fun rB' ↦
    match stepCodeBool q a with
    | none => none
    | some (w, true, q') =>
      forceNat (kL + 1) fun kL' ↦
      forceNat ((if w then 1 else 0) + 2 * lB) fun lB' ↦
        simZipNat steps q' true kL' lB' kR rB'
    | some (w, false, q') =>
      forceNat (kR + 1) fun kR1 ↦
      forceNat ((if w then 1 else 0) + 2 * rB') fun rB1 ↦
        simZipNat steps q' false kL lB kR1 rB1
  | _ + 1, _, true, _, _, 0, _ => none
  | steps + 1, q, false, kL + 1, lB, kR, rB =>
    let a := Nat.beq (lB % 2) 1
    forceNat (lB / 2) fun lB' ↦
    match stepCodeBool q a with
    | none => none
    | some (w, true, q') =>
      forceNat (kL + 1) fun kL1 ↦
      forceNat ((if w then 1 else 0) + 2 * lB') fun lB1 ↦
        simZipNat steps q' true kL1 lB1 kR rB
    | some (w, false, q') =>
      forceNat (kR + 1) fun kR' ↦
      forceNat ((if w then 1 else 0) + 2 * rB) fun rB' ↦
        simZipNat steps q' false kL lB' kR' rB'
  | _ + 1, _, false, 0, _, _, _ => none

theorem simZipNat_sound :
    ∀ (steps q : ℕ) (dir : Bool) (kL lB kR rB : ℕ)
      (q' : ℕ) (dir' : Bool) (kL' lB' kR' rB' : ℕ) (l r : ListBlank (Fin 2)),
      simZipNat steps q dir kL lB kR rB = some (q', dir', kL', lB', kR', rB') →
      ReachesIn target_tm steps
        (WordRLE.dirCfg qOf q dir
          (ListBlank.append (unpackBits kL lB) l)
          (ListBlank.append (unpackBits kR rB) r))
        (WordRLE.dirCfg qOf q' dir'
          (ListBlank.append (unpackBits kL' lB') l)
          (ListBlank.append (unpackBits kR' rB') r))
  | 0, q, dir, kL, lB, kR, rB, q', dir', kL', lB', kR', rB', l, r, h => by
    simp only [simZipNat, forceNat_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    exact ReachesIn.zero target_tm _
  | steps + 1, q, true, kL, lB, 0, rB, _, _, _, _, _, _, _, _, h => by
    simp [simZipNat] at h
  | steps + 1, q, true, kL, lB, kR + 1, rB, q', dir', kL', lB', kR', rB', l, r, h => by
    simp only [simZipNat, forceNat_eq] at h
    rcases hsc : stepCodeBool q (Nat.beq (rB % 2) 1) with _ | ⟨w, dNext, qNext⟩
    · simp [hsc] at h
    · rw [hsc] at h
      have hscFin := stepCode_agrees q _ _ dNext qNext (stepCodeBool_agrees _ _ _ _ _ hsc)
      cases dNext
      · simp only at h
        have ih := simZipNat_sound steps qNext false kL lB (kR + 1)
          ((if w then 1 else 0) + 2 * (rB / 2)) q' dir' kL' lB' kR' rB' l r h
        rw [unpackBits_push] at ih
        have hst := step_headRight_left hscFin
          (ListBlank.append (unpackBits kL lB) l)
          (ListBlank.append (unpackBits kR (rB / 2)) r)
        exact ReachesIn.step_left hst ih
      · simp only at h
        have ih := simZipNat_sound steps qNext true (kL + 1)
          ((if w then 1 else 0) + 2 * lB) kR (rB / 2) q' dir' kL' lB' kR' rB' l r h
        rw [unpackBits_push] at ih
        have hst := step_headRight_right hscFin
          (ListBlank.append (unpackBits kL lB) l)
          (ListBlank.append (unpackBits kR (rB / 2)) r)
        exact ReachesIn.step_left hst ih
  | steps + 1, q, false, 0, lB, kR, rB, _, _, _, _, _, _, _, _, h => by
    simp [simZipNat] at h
  | steps + 1, q, false, kL + 1, lB, kR, rB, q', dir', kL', lB', kR', rB', l, r, h => by
    simp only [simZipNat, forceNat_eq] at h
    rcases hsc : stepCodeBool q (Nat.beq (lB % 2) 1) with _ | ⟨w, dNext, qNext⟩
    · simp [hsc] at h
    · rw [hsc] at h
      have hscFin := stepCode_agrees q _ _ dNext qNext (stepCodeBool_agrees _ _ _ _ _ hsc)
      cases dNext
      · simp only at h
        have ih := simZipNat_sound steps qNext false kL (lB / 2) (kR + 1)
          ((if w then 1 else 0) + 2 * rB) q' dir' kL' lB' kR' rB' l r h
        rw [unpackBits_push] at ih
        have hst := step_headLeft_left hscFin
          (ListBlank.append (unpackBits kL (lB / 2)) l)
          (ListBlank.append (unpackBits kR rB) r)
        exact ReachesIn.step_left hst ih
      · simp only at h
        have ih := simZipNat_sound steps qNext true (kL + 1)
          ((if w then 1 else 0) + 2 * (lB / 2)) kR rB q' dir' kL' lB' kR' rB' l r h
        rw [unpackBits_push] at ih
        have hst := step_headLeft_right hscFin
          (ListBlank.append (unpackBits kL (lB / 2)) l)
          (ListBlank.append (unpackBits kR rB) r)
        exact ReachesIn.step_left hst ih

structure ZipNatEntry where
  steps : ℕ
  qIn : ℕ
  dirIn : Bool
  kL : ℕ
  lB : ℕ
  kR : ℕ
  rB : ℕ
  qOut : ℕ
  dirOut : Bool
  kLOut : ℕ
  lOut : ℕ
  kROut : ℕ
  rOut : ℕ

noncomputable def unpackZip (p0 : ℕ) : ZipNatEntry :=
  forceNat (p0 % 65536) fun steps ↦
  forceNat (p0 / 65536) fun p1 ↦
  forceNat (p1 % 8) fun qIn ↦
  let dirIn := Nat.beq ((p1 / 8) % 2) 1
  forceNat (p1 / 16) fun p2 ↦
  forceNat (p2 % 8) fun qOut ↦
  let dirOut := Nat.beq ((p2 / 8) % 2) 1
  forceNat (p2 / 16) fun p3 ↦
  forceNat (p3 % 256) fun kL ↦
  forceNat (p3 / 256) fun p4 ↦
  forceNat (p4 % 256) fun kR ↦
  forceNat (p4 / 256) fun p5 ↦
  forceNat (p5 % 256) fun kLOut ↦
  forceNat (p5 / 256) fun p6 ↦
  forceNat (p6 % 256) fun kROut ↦
  forceNat (p6 / 256) fun p7 ↦
  forceNat (Nat.pow 2 kL) fun mL ↦
  forceNat (p7 % mL) fun lB ↦
  forceNat (p7 / mL) fun p8 ↦
  forceNat (Nat.pow 2 kR) fun mR ↦
  forceNat (p8 % mR) fun rB ↦
  forceNat (p8 / mR) fun p9 ↦
  forceNat (Nat.pow 2 kLOut) fun mLO ↦
  forceNat (p9 % mLO) fun lOut ↦
  forceNat (p9 / mLO) fun rOut ↦
    ⟨steps, qIn, dirIn, kL, lB, kR, rB, qOut, dirOut, kLOut, lOut, kROut, rOut⟩

noncomputable def checkZipPacked (_ : ℕ) (p : ℕ) : Bool :=
  let e := unpackZip p
  Nat.ble 1 e.steps &&
    (simZipNat e.steps e.qIn e.dirIn e.kL e.lB e.kR e.rB ==
      some (e.qOut, e.dirOut, e.kLOut, e.lOut, e.kROut, e.rOut))

/-! ### Trigram Shift Laws -/

def symWord : ℕ → List (Fin 2)
  | 0 => [0]
  | 1 => [1]
  | 2 => [0, 1, 0]
  | 3 => [1, 1, 0]
  | _ => [0, 1, 1]

theorem exit_waL :
    WordRLE.WordExit target_tm qOf [0, 1, 0] 1 false [0, 1, 0] 1 false 3 :=
  WordRLE.runWordExit_sound stepCode_agrees (fuel := 16) (by decide +kernel)

theorem exit_wbR :
    WordRLE.WordExit target_tm qOf [1, 1, 0] 1 true [0, 1, 1] 1 true 3 :=
  WordRLE.runWordExit_sound stepCode_agrees (fuel := 16) (by decide +kernel)

theorem exit_wcL :
    WordRLE.WordExit target_tm qOf [0, 1, 1] 5 false [1, 1, 0] 5 false 3 :=
  WordRLE.runWordExit_sound stepCode_agrees (fuel := 16) (by decide +kernel)

theorem waR0_one_check :
    simZipNat 9 0 true 0 0 4 2 = some (0, true, 3, 2, 1, 0) := by
  decide +kernel

theorem wa_pow_zero_head (n : ℕ) (r : ListBlank (Fin 2)) :
    ∃ r', ListBlank.append (([0, 1, 0] : List (Fin 2)) ^ n) (ListBlank.cons 0 r) =
      ListBlank.cons 0 r' := by
  cases n with
  | zero => exact ⟨r, rfl⟩
  | succ k => exact ⟨ListBlank.append [1, 0] (ListBlank.append (([0, 1, 0] : List (Fin 2)) ^ k)
      (ListBlank.cons 0 r)), rfl⟩

theorem sweep_waR0_sound (n : ℕ) :
    ∀ (l r : ListBlank (Fin 2)),
      ReachesIn target_tm (9 * n)
        (WordRLE.dirCfg qOf 0 true l
          (ListBlank.append (([0, 1, 0] : List (Fin 2)) ^ n) (ListBlank.cons 0 r)))
        (WordRLE.dirCfg qOf 0 true
          (ListBlank.append (([0, 1, 0] : List (Fin 2)) ^ n) l)
          (ListBlank.cons 0 r)) := by
  induction n with
  | zero =>
    intro l r
    exact ReachesIn.zero target_tm _
  | succ k ih =>
    intro l r
    rw [ListBlank.append_pow_succ]
    obtain ⟨rMid, hMid⟩ := wa_pow_zero_head k r
    have h1 := simZipNat_sound 9 0 true 0 0 4 2 0 true 3 2 1 0 l rMid waR0_one_check
    change ReachesIn target_tm 9
      (WordRLE.dirCfg qOf 0 true l (ListBlank.append [0, 1, 0] (ListBlank.cons 0 rMid)))
      (WordRLE.dirCfg qOf 0 true (ListBlank.append [0, 1, 0] l) (ListBlank.cons 0 rMid)) at h1
    rw [← hMid] at h1
    have h2 := ih (ListBlank.append [0, 1, 0] l) r
    rw [ListBlank.append_pow_comm, ← ListBlank.append_pow_succ] at h2
    have htr := h1.trans h2
    have hdt : 9 + 9 * k = 9 * (k + 1) := by omega
    rwa [hdt] at htr

/-! ### Pure-`ℕ` 3-Variable Affine Forms (`Aff3`), Halfspaces, and Farkas Witnesses -/

inductive Var3 where
  | va
  | vb
  | vc
  deriving DecidableEq, Inhabited

structure Aff3 where
  c0 : ℕ
  ca : ℕ
  cb : ℕ
  cc : ℕ
  deriving DecidableEq, Inhabited

@[inline]
def Aff3.strict {α : Type*} (e : Aff3) (f : Aff3 → α) : α :=
  forceNat e.c0 fun c0 ↦
  forceNat e.ca fun ca ↦
  forceNat e.cb fun cb ↦
  forceNat e.cc fun cc ↦
    f ⟨c0, ca, cb, cc⟩

theorem Aff3.strict_eq {α : Type*} (e : Aff3) (f : Aff3 → α) : e.strict f = f e :=
  rfl

def Aff3.one : Aff3 := ⟨1, 0, 0, 0⟩
def Aff3.const (k : ℕ) : Aff3 := forceNat k fun k' ↦ ⟨k', 0, 0, 0⟩

def Aff3.eval (e : Aff3) (u v w : ℕ) : ℕ :=
  e.c0 + e.ca * u + e.cb * v + e.cc * w

def Aff3.isZero (e : Aff3) : Bool :=
  Nat.beq e.c0 0 && Nat.beq e.ca 0 && Nat.beq e.cb 0 && Nat.beq e.cc 0

def Aff3.add (p q : Aff3) : Aff3 :=
  forceNat (p.c0 + q.c0) fun n0 ↦
  forceNat (p.ca + q.ca) fun na ↦
  forceNat (p.cb + q.cb) fun nb ↦
  forceNat (p.cc + q.cc) fun nc ↦
    ⟨n0, na, nb, nc⟩

def Aff3.sub1 (e : Aff3) : Aff3 :=
  forceNat (e.c0 - 1) fun n0 ↦ ⟨n0, e.ca, e.cb, e.cc⟩

def Aff3.addConst (e : Aff3) (d : ℕ) : Aff3 :=
  forceNat (e.c0 + d) fun n0 ↦ ⟨n0, e.ca, e.cb, e.cc⟩

def Aff3.scale (e : Aff3) (k : ℕ) : Aff3 :=
  forceNat (k * e.c0) fun n0 ↦
  forceNat (k * e.ca) fun na ↦
  forceNat (k * e.cb) fun nb ↦
  forceNat (k * e.cc) fun nc ↦
    ⟨n0, na, nb, nc⟩

def Aff3.leCoeff (p q : Aff3) : Bool :=
  Nat.ble p.c0 q.c0 && Nat.ble p.ca q.ca && Nat.ble p.cb q.cb && Nat.ble p.cc q.cc

def Aff3.substZero (e : Aff3) : Var3 → Aff3
  | .va => ⟨e.c0, 0, e.cb, e.cc⟩
  | .vb => ⟨e.c0, e.ca, 0, e.cc⟩
  | .vc => ⟨e.c0, e.ca, e.cb, 0⟩

def Aff3.substSucc (e : Aff3) : Var3 → Aff3
  | .va => forceNat (e.c0 + e.ca) fun n0 ↦ ⟨n0, e.ca, e.cb, e.cc⟩
  | .vb => forceNat (e.c0 + e.cb) fun n0 ↦ ⟨n0, e.ca, e.cb, e.cc⟩
  | .vc => forceNat (e.c0 + e.cc) fun n0 ↦ ⟨n0, e.ca, e.cb, e.cc⟩

theorem Aff3.const_eval (k u v w : ℕ) : (Aff3.const k).eval u v w = k := by
  simp [Aff3.const, forceNat_eq, Aff3.eval]

theorem Aff3.one_eval (u v w : ℕ) : Aff3.one.eval u v w = 1 := by
  simp [Aff3.one, Aff3.eval]

theorem Aff3.isZero_sound {e : Aff3} (h : e.isZero = true) (u v w : ℕ) :
    e.eval u v w = 0 := by
  unfold Aff3.isZero at h
  simp only [Bool.and_eq_true] at h
  have h0 := Nat.eq_of_beq_eq_true h.1.1.1
  have ha := Nat.eq_of_beq_eq_true h.1.1.2
  have hb := Nat.eq_of_beq_eq_true h.1.2
  have hc := Nat.eq_of_beq_eq_true h.2
  simp [Aff3.eval, h0, ha, hb, hc]

theorem Aff3.add_eval (p q : Aff3) (u v w : ℕ) :
    (p.add q).eval u v w = p.eval u v w + q.eval u v w := by
  simp only [Aff3.add, forceNat_eq, Aff3.eval, Nat.add_mul]
  omega

theorem Aff3.sub1_eval {e : Aff3} (h : Nat.ble 1 e.c0 = true) (u v w : ℕ) :
    e.eval u v w = (e.sub1.eval u v w) + 1 := by
  have hc : 1 ≤ e.c0 := Nat.le_of_ble_eq_true h
  simp only [Aff3.sub1, forceNat_eq, Aff3.eval]
  omega

theorem Aff3.ge1_eval {e : Aff3} (h : Nat.ble 1 e.c0 = true) (u v w : ℕ) :
    1 ≤ e.eval u v w := by
  have hc : 1 ≤ e.c0 := Nat.le_of_ble_eq_true h
  unfold Aff3.eval
  omega

theorem Aff3.addConst_eval (e : Aff3) (d u v w : ℕ) :
    (e.addConst d).eval u v w = e.eval u v w + d := by
  simp only [Aff3.addConst, forceNat_eq, Aff3.eval]
  omega

theorem Aff3.scale_eval (e : Aff3) (k u v w : ℕ) :
    (e.scale k).eval u v w = k * e.eval u v w := by
  simp only [Aff3.scale, forceNat_eq, Aff3.eval, Nat.mul_add, Nat.mul_assoc]

theorem Aff3.leCoeff_sound {p q : Aff3} (h : p.leCoeff q = true) (u v w : ℕ) :
    p.eval u v w ≤ q.eval u v w := by
  unfold Aff3.leCoeff at h
  simp only [Bool.and_eq_true, Nat.ble_eq] at h
  obtain ⟨⟨⟨h0, ha⟩, hb⟩, hc⟩ := h
  have mu := Nat.mul_le_mul_right u ha
  have mv := Nat.mul_le_mul_right v hb
  have mw := Nat.mul_le_mul_right w hc
  unfold Aff3.eval
  omega

theorem Aff3.substZero_va (e : Aff3) (v w : ℕ) :
    (e.substZero .va).eval 0 v w = e.eval 0 v w := by
  simp [Aff3.substZero, Aff3.eval]

theorem Aff3.substSucc_va (e : Aff3) (u v w : ℕ) :
    (e.substSucc .va).eval u v w = e.eval (u + 1) v w := by
  simp only [Aff3.substSucc, forceNat_eq, Aff3.eval, Nat.mul_succ]
  omega

theorem Aff3.substZero_vb (e : Aff3) (u w : ℕ) :
    (e.substZero .vb).eval u 0 w = e.eval u 0 w := by
  simp [Aff3.substZero, Aff3.eval]

theorem Aff3.substSucc_vb (e : Aff3) (u v w : ℕ) :
    (e.substSucc .vb).eval u v w = e.eval u (v + 1) w := by
  simp only [Aff3.substSucc, forceNat_eq, Aff3.eval, Nat.mul_succ]
  omega

theorem Aff3.substZero_vc (e : Aff3) (u v : ℕ) :
    (e.substZero .vc).eval u v 0 = e.eval u v 0 := by
  simp [Aff3.substZero, Aff3.eval]

theorem Aff3.substSucc_vc (e : Aff3) (u v w : ℕ) :
    (e.substSucc .vc).eval u v w = e.eval u v (w + 1) := by
  simp only [Aff3.substSucc, forceNat_eq, Aff3.eval, Nat.mul_succ]
  omega

structure AffIneq where
  lhs : Aff3
  rhs : Aff3
  deriving DecidableEq, Inhabited

def AffIneq.holds (h : AffIneq) (u v w : ℕ) : Prop :=
  h.rhs.eval u v w ≤ h.lhs.eval u v w

def HubInv (m a b c : ℕ) : Prop :=
  m < 7 ∧
    match m with
    | 0 => 6 ≤ b + c ∧ 1 ≤ a ∧ 7 * a + 8 ≤ 3 * b + 6 * c
    | 1 | 2 => 6 ≤ b + c ∧ 1 ≤ a ∧ 7 * a ≤ 3 * b + 6 * c
    | 3 => 6 ≤ b + c ∧ 1 ≤ a ∧ 7 * a + 6 ≤ 3 * b + 6 * c
    | _ => 6 ≤ b + c ∧ 7 * a + 18 ≤ 6 * b ∧ 7 * a + 24 ≤ 6 * b + 12 * c

def modeIneqs (m : ℕ) (a b c : Aff3) : AffIneq × AffIneq × AffIneq :=
  let bc := b.add c
  match m with
  | 0 =>
    (⟨bc, Aff3.const 6⟩, ⟨a, Aff3.const 1⟩,
      ⟨(b.scale 3).add (c.scale 6), (a.scale 7).addConst 8⟩)
  | 1 | 2 =>
    (⟨bc, Aff3.const 6⟩, ⟨a, Aff3.const 1⟩,
      ⟨(b.scale 3).add (c.scale 6), a.scale 7⟩)
  | 3 =>
    (⟨bc, Aff3.const 6⟩, ⟨a, Aff3.const 1⟩,
      ⟨(b.scale 3).add (c.scale 6), (a.scale 7).addConst 6⟩)
  | _ =>
    (⟨bc, Aff3.const 6⟩, ⟨b.scale 6, (a.scale 7).addConst 18⟩,
      ⟨(b.scale 6).add (c.scale 12), (a.scale 7).addConst 24⟩)

theorem modeIneqs_iff {m : ℕ} (hm : m < 7) (a b c : Aff3) (u v w : ℕ) :
    (let (h0, h1, h2) := modeIneqs m a b c
     h0.holds u v w ∧ h1.holds u v w ∧ h2.holds u v w) ↔
      HubInv m (a.eval u v w) (b.eval u v w) (c.eval u v w) := by
  match m with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 =>
    simp [modeIneqs, HubInv, AffIneq.holds, hm, Aff3.const_eval, Aff3.add_eval,
      Aff3.addConst_eval, Aff3.scale_eval]
  | _ + 7 => omega

def selIneq (hs : AffIneq × AffIneq × AffIneq) : ℕ → AffIneq
  | 0 => hs.1
  | 1 => hs.2.1
  | _ => hs.2.2

theorem selIneq_holds {hs : AffIneq × AffIneq × AffIneq} {u v w : ℕ}
    (hh : hs.1.holds u v w ∧ hs.2.1.holds u v w ∧ hs.2.2.holds u v w) (idx : ℕ) :
    (selIneq hs idx).holds u v w := by
  match idx with
  | 0 => exact hh.1
  | 1 => exact hh.2.1
  | _ + 2 => exact hh.2.2

def isDeadIneq (h : AffIneq) : Bool :=
  (h.lhs.addConst 1).leCoeff h.rhs

theorem isDeadIneq_sound {h : AffIneq} {u v w : ℕ}
    (hd : isDeadIneq h = true) (hh : h.holds u v w) : False := by
  have hle := Aff3.leCoeff_sound hd u v w
  rw [Aff3.addConst_eval] at hle
  unfold AffIneq.holds at hh
  omega

structure FWit where
  k : ℕ
  i1 : ℕ
  l1 : ℕ
  i2 : ℕ
  l2 : ℕ
  deriving DecidableEq, Inhabited

def checkFarkas (hs : AffIneq × AffIneq × AffIneq) (goal : AffIneq) (wit : FWit) : Bool :=
  Nat.ble 1 wit.k &&
    let h1 := selIneq hs wit.i1
    let h2 := selIneq hs wit.i2
    let p := ((goal.lhs.scale wit.k).addConst (wit.k - 1)).add
      ((h1.rhs.scale wit.l1).add (h2.rhs.scale wit.l2))
    let q := (goal.rhs.scale wit.k).add
      ((h1.lhs.scale wit.l1).add (h2.lhs.scale wit.l2))
    q.leCoeff p

theorem checkFarkas_sound {hs : AffIneq × AffIneq × AffIneq} {goal : AffIneq} {wit : FWit}
    {u v w : ℕ} (hc : checkFarkas hs goal wit = true)
    (hh : hs.1.holds u v w ∧ hs.2.1.holds u v w ∧ hs.2.2.holds u v w) :
    goal.holds u v w := by
  unfold checkFarkas at hc
  simp only [Bool.and_eq_true] at hc
  have hk : 1 ≤ wit.k := Nat.le_of_ble_eq_true hc.1
  have hqp := Aff3.leCoeff_sound hc.2 u v w
  simp only [Aff3.add_eval, Aff3.addConst_eval, Aff3.scale_eval] at hqp
  have hh1 : (selIneq hs wit.i1).rhs.eval u v w ≤ (selIneq hs wit.i1).lhs.eval u v w :=
    selIneq_holds hh wit.i1
  have hh2 : (selIneq hs wit.i2).rhs.eval u v w ≤ (selIneq hs wit.i2).lhs.eval u v w :=
    selIneq_holds hh wit.i2
  have hm1 := Nat.mul_le_mul_left wit.l1 hh1
  have hm2 := Nat.mul_le_mul_left wit.l2 hh2
  unfold AffIneq.holds
  rcases Nat.lt_or_ge (goal.lhs.eval u v w) (goal.rhs.eval u v w) with hgt | hle
  · have hmul := Nat.mul_le_mul_left wit.k hgt
    rw [Nat.mul_succ] at hmul
    omega
  · exact hle

/-! ### Symbolic RLE Half-Tape Stacks (`SymRun`, `SymCfg`, `canonRight`) -/

structure SymRun where
  sym : ℕ
  cnt : Aff3
  deriving DecidableEq, Inhabited

def evalStk (side : Bool) (u v w : ℕ) : List SymRun → ListBlank (Fin 2)
  | [] => default
  | ⟨sym, cnt⟩ :: rest =>
    let wd := if side then symWord sym else (symWord sym).reverse
    ListBlank.append (wd ^ cnt.eval u v w) (evalStk side u v w rest)

def pushSym (sym : ℕ) (cnt : Aff3) (stk : List SymRun) : List SymRun :=
  cnt.strict fun cnt' ↦
    if cnt'.isZero then stk
    else
      match stk with
      | [] => if Nat.beq sym 0 then [] else [⟨sym, cnt'⟩]
      | ⟨ts, tc⟩ :: rest =>
        if Nat.beq ts sym then ⟨ts, tc.add cnt'⟩ :: rest
        else ⟨sym, cnt'⟩ :: ⟨ts, tc⟩ :: rest

theorem evalStk_pushSym (side : Bool) (u v w : ℕ) (sym : ℕ) (cnt : Aff3) (stk : List SymRun) :
    evalStk side u v w (pushSym sym cnt stk) =
      ListBlank.append
        ((if side then symWord sym else (symWord sym).reverse) ^ cnt.eval u v w)
        (evalStk side u v w stk) := by
  unfold pushSym
  rw [Aff3.strict_eq]
  cases h0 : cnt.isZero
  · simp only [Bool.false_eq_true, ↓reduceIte]
    cases stk with
    | nil =>
      cases hs : Nat.beq sym 0
      · rfl
      · have hsym : sym = 0 := Nat.eq_of_beq_eq_true hs
        subst hsym
        cases side <;> simp [evalStk, symWord]
    | cons top rest =>
      rcases top with ⟨ts, tc⟩
      simp only
      cases hs : Nat.beq ts sym
      · rfl
      · have heq : ts = sym := Nat.eq_of_beq_eq_true hs
        subst heq
        simp only [↓reduceIte, evalStk, Aff3.add_eval]
        rw [Nat.add_comm (tc.eval u v w), list_pow_add, ListBlank.append_assoc]
  · simp only [↓reduceIte, Aff3.isZero_sound h0 u v w, list_pow_zero, ListBlank.append_nil]

def pushBits : List (Fin 2) → List SymRun → List SymRun
  | [], stk => stk
  | b :: bs, stk => pushSym b.val Aff3.one (pushBits bs stk)

theorem symWord_bit_eq (side : Bool) (b : Fin 2) :
    (if side then symWord b.val else (symWord b.val).reverse) = [b] := by
  rcases b with ⟨_ | _ | n, hb⟩
  · cases side <;> rfl
  · cases side <;> rfl
  · omega

theorem evalStk_pushBits (side : Bool) (u v w : ℕ) (ws : List (Fin 2)) (stk : List SymRun) :
    evalStk side u v w (pushBits ws stk) =
      ListBlank.append ws (evalStk side u v w stk) := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
    simp only [pushBits, evalStk_pushSym, symWord_bit_eq, Aff3.one_eval, list_pow_one, ih]
    rfl

def popBit (b : Fin 2) : List SymRun → Option (List SymRun)
  | [] => if b == 0 then some [] else none
  | ⟨sym, cnt⟩ :: rest =>
    if Nat.beq sym b.val && Nat.ble 1 cnt.c0 then
      cnt.sub1.strict fun k ↦
        if k.isZero then some rest else some (⟨sym, k⟩ :: rest)
    else none

theorem popBit_sound (side : Bool) (u v w : ℕ) (b : Fin 2) (stk stk' : List SymRun)
    (h : popBit b stk = some stk') :
    evalStk side u v w stk = ListBlank.cons b (evalStk side u v w stk') := by
  cases stk with
  | nil =>
    rcases b with ⟨_ | _ | n, hb⟩
    · change popBit 0 [] = some stk' at h
      simp only [popBit, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at h
      subst h
      exact ListBlank.cons_zero_default.symm
    · change popBit 1 [] = some stk' at h
      simp [popBit] at h
    · omega
  | cons top rest =>
    rcases top with ⟨sym, cnt⟩
    simp only [popBit, Aff3.strict_eq] at h
    cases hc : Nat.beq sym b.val && Nat.ble 1 cnt.c0
    · simp [hc] at h
    · rw [hc] at h
      simp only [↓reduceIte] at h
      simp only [Bool.and_eq_true] at hc
      have hsym : sym = b.val := Nat.eq_of_beq_eq_true hc.1
      subst hsym
      have hcnt := Aff3.sub1_eval hc.2 u v w
      cases hz : cnt.sub1.isZero
      · rw [hz] at h
        simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [evalStk, symWord_bit_eq, hcnt]
        rw [ListBlank.append_pow_succ]
        rfl
      · rw [hz] at h
        simp only [↓reduceIte, Option.some.injEq] at h
        subst h
        simp only [evalStk, symWord_bit_eq, hcnt, Aff3.isZero_sound hz u v w, Nat.zero_add,
          list_pow_one]
        rfl

def popBits : List (Fin 2) → List SymRun → Option (List SymRun)
  | [], stk => some stk
  | b :: bs, stk =>
    match popBit b stk with
    | none => none
    | some stk' => popBits bs stk'

theorem popBits_sound (side : Bool) (u v w : ℕ) :
    ∀ (ws : List (Fin 2)) (stk stk' : List SymRun),
      popBits ws stk = some stk' →
      evalStk side u v w stk = ListBlank.append ws (evalStk side u v w stk')
  | [], stk, stk', h => by
    simp only [popBits, Option.some.injEq] at h
    subst h
    rfl
  | b :: bs, stk, stk', h => by
    simp only [popBits] at h
    rcases hp : popBit b stk with _ | mid
    · simp [hp] at h
    · rw [hp] at h
      simp only at h
      rw [popBit_sound side u v w b stk mid hp, popBits_sound side u v w bs mid stk' h]
      rfl

def substStk (sv : Var3) (isSucc : Bool) : List SymRun → List SymRun
  | [] => []
  | ⟨sym, cnt⟩ :: rest =>
    let nc := if isSucc then cnt.substSucc sv else cnt.substZero sv
    pushSym sym nc (substStk sv isSucc rest)

theorem substStk_zero_va (side : Bool) (v w : ℕ) (stk : List SymRun) :
    evalStk side 0 v w (substStk .va false stk) = evalStk side 0 v w stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substZero_va, ih, evalStk]

theorem substStk_succ_va (side : Bool) (u v w : ℕ) (stk : List SymRun) :
    evalStk side u v w (substStk .va true stk) = evalStk side (u + 1) v w stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substSucc_va, ih, evalStk]

theorem substStk_zero_vb (side : Bool) (u w : ℕ) (stk : List SymRun) :
    evalStk side u 0 w (substStk .vb false stk) = evalStk side u 0 w stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substZero_vb, ih, evalStk]

theorem substStk_succ_vb (side : Bool) (u v w : ℕ) (stk : List SymRun) :
    evalStk side u v w (substStk .vb true stk) = evalStk side u (v + 1) w stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substSucc_vb, ih, evalStk]

theorem substStk_zero_vc (side : Bool) (u v : ℕ) (stk : List SymRun) :
    evalStk side u v 0 (substStk .vc false stk) = evalStk side u v 0 stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substZero_vc, ih, evalStk]

theorem substStk_succ_vc (side : Bool) (u v w : ℕ) (stk : List SymRun) :
    evalStk side u v w (substStk .vc true stk) = evalStk side u v (w + 1) stk := by
  induction stk with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, cnt⟩
    simp [substStk, evalStk_pushSym, Aff3.substSucc_vc, ih, evalStk]

def nearBit (sym : ℕ) (side : Bool) : Fin 2 :=
  match sym with
  | 0 => 0
  | 1 => 1
  | 2 => 0
  | 3 => if side then 1 else 0
  | _ => if side then 0 else 1

theorem symWord_nearBit (side : Bool) (sym : ℕ) :
    ∃ rest, (if side then symWord sym else (symWord sym).reverse) = nearBit sym side :: rest := by
  match sym with
  | 0 | 1 | 2 | 3 => cases side <;> exact ⟨_, rfl⟩
  | _ + 4 => cases side <;> exact ⟨_, rfl⟩

def peekBit (side : Bool) : List SymRun → Option (Fin 2)
  | [] => some 0
  | ⟨sym, cnt⟩ :: rest =>
    let b := nearBit sym side
    if Nat.ble 1 cnt.c0 then some b
    else
      match peekBit side rest with
      | some b' => if b == b' then some b else none
      | none => none

theorem peekBit_sound (side : Bool) (u v w : ℕ) :
    ∀ (stk : List SymRun) (b : Fin 2),
      peekBit side stk = some b →
      ∃ tail, evalStk side u v w stk = ListBlank.cons b tail
  | [], b, h => by
    simp only [peekBit, Option.some.injEq] at h
    subst h
    exact ⟨default, ListBlank.cons_zero_default.symm⟩
  | ⟨sym, cnt⟩ :: rest, b, h => by
    simp only [peekBit] at h
    obtain ⟨wRest, hw⟩ := symWord_nearBit side sym
    cases hc : Nat.ble 1 cnt.c0
    · rw [hc] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases hp : peekBit side rest with _ | b'
      · simp [hp] at h
      · rw [hp] at h
        simp only at h
        cases hbb : nearBit sym side == b'
        · simp [hbb] at h
        · rw [hbb] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          have hbEq : nearBit sym side = b' := eq_of_beq hbb
          rcases hcnt : cnt.eval u v w with _ | k
          · simp only [evalStk, hcnt, list_pow_zero, ListBlank.append_nil]
            rw [hbEq]
            exact peekBit_sound side u v w rest b' hp
          · simp only [evalStk, hcnt, ListBlank.append_pow_succ]
            rw [hw]
            exact ⟨_, rfl⟩
    · rw [hc] at h
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      have hge := Aff3.ge1_eval hc u v w
      obtain ⟨k, hk⟩ : ∃ k, cnt.eval u v w = k + 1 := ⟨cnt.eval u v w - 1, by omega⟩
      simp only [evalStk, hk, ListBlank.append_pow_succ]
      rw [hw]
      exact ⟨_, rfl⟩

/-! ### Canonical Right-Stack Normalization (`canonRight`) -/

inductive CTok where
  | bit (b : Fin 2)
  | slope (sym ca cb cc : ℕ)
  deriving DecidableEq, Inhabited

def evalCTok (u v w : ℕ) : CTok → List (Fin 2)
  | .bit b => [b]
  | .slope sym ca cb cc => symWord sym ^ (ca * u + cb * v + cc * w)

def evalCanon (u v w : ℕ) : List CTok → ListBlank (Fin 2)
  | [] => default
  | t :: ts => ListBlank.append (evalCTok u v w t) (evalCanon u v w ts)

def consBit (b : Fin 2) : List CTok → List CTok
  | [] => if b == 0 then [] else [.bit b]
  | t :: ts => .bit b :: t :: ts

theorem evalCanon_consBit (u v w : ℕ) (b : Fin 2) (ts : List CTok) :
    evalCanon u v w (consBit b ts) = ListBlank.cons b (evalCanon u v w ts) := by
  cases ts with
  | nil =>
    rcases b with ⟨_ | _ | n, hb⟩
    · exact ListBlank.cons_zero_default.symm
    · rfl
    · omega
  | cons t rest => rfl

def consBits : List (Fin 2) → List CTok → List CTok
  | [], ts => ts
  | b :: bs, ts => consBit b (consBits bs ts)

theorem evalCanon_consBits (u v w : ℕ) (ws : List (Fin 2)) (ts : List CTok) :
    evalCanon u v w (consBits ws ts) = ListBlank.append ws (evalCanon u v w ts) := by
  induction ws with
  | nil => rfl
  | cons b bs ih =>
    simp only [consBits, evalCanon_consBit, ih]
    rfl

def consSlopeAux (sym ca cb cc : ℕ) : List CTok → List CTok
  | [] =>
    if Nat.beq sym 0 then [] else [.slope sym ca cb cc]
  | .slope sym' ca' cb' cc' :: tail =>
    if Nat.beq sym sym' && Nat.ble 2 sym then
      forceNat (ca + ca') fun na ↦
      forceNat (cb + cb') fun nb ↦
      forceNat (cc + cc') fun nc ↦
        .slope sym na nb nc :: tail
    else
      .slope sym ca cb cc :: .slope sym' ca' cb' cc' :: tail
  | .bit b0 :: .bit b1 :: .bit b2 :: tail =>
    if Nat.ble 2 sym && ([b0, b1, b2] == symWord sym) then
      .bit b0 :: .bit b1 :: .bit b2 :: consSlopeAux sym ca cb cc tail
    else
      .slope sym ca cb cc :: .bit b0 :: .bit b1 :: .bit b2 :: tail
  | t :: tail =>
    .slope sym ca cb cc :: t :: tail

theorem evalCanon_consSlopeAux (u v w sym ca cb cc : ℕ) :
    ∀ (ts : List CTok),
      evalCanon u v w (consSlopeAux sym ca cb cc ts) =
        ListBlank.append (symWord sym ^ (ca * u + cb * v + cc * w)) (evalCanon u v w ts)
  | [] => by
    unfold consSlopeAux
    cases hs : Nat.beq sym 0
    · rfl
    · have h0 : sym = 0 := Nat.eq_of_beq_eq_true hs
      subst h0
      simp [evalCanon, symWord]
  | .slope sym' ca' cb' cc' :: tail => by
    unfold consSlopeAux
    cases hm : Nat.beq sym sym' && Nat.ble 2 sym
    · rfl
    · simp only [↓reduceIte, forceNat_eq, evalCanon, evalCTok]
      simp only [Bool.and_eq_true] at hm
      have heq : sym = sym' := Nat.eq_of_beq_eq_true hm.1
      subst heq
      have hlin : (ca + ca') * u + (cb + cb') * v + (cc + cc') * w =
          (ca * u + cb * v + cc * w) + (ca' * u + cb' * v + cc' * w) := by
        simp only [Nat.add_mul]
        omega
      rw [hlin, list_pow_add, ListBlank.append_assoc]
  | .bit b0 :: [.bit b1] => rfl
  | .bit b0 :: [.slope _ _ _ _] => rfl
  | .bit b0 :: .slope _ _ _ _ :: _ :: _ => rfl
  | [.bit b0] => rfl
  | .bit b0 :: .bit b1 :: .slope _ _ _ _ :: _ => rfl
  | .bit b0 :: .bit b1 :: .bit b2 :: tail => by
    unfold consSlopeAux
    cases hm : Nat.ble 2 sym && ([b0, b1, b2] == symWord sym)
    · rfl
    · simp only [↓reduceIte]
      simp only [Bool.and_eq_true] at hm
      have hw : [b0, b1, b2] = symWord sym := eq_of_beq hm.2
      change ListBlank.append [b0, b1, b2] (evalCanon u v w (consSlopeAux sym ca cb cc tail)) =
        ListBlank.append (symWord sym ^ (ca * u + cb * v + cc * w))
          (ListBlank.append [b0, b1, b2] (evalCanon u v w tail))
      rw [evalCanon_consSlopeAux u v w sym ca cb cc tail, hw]
      exact (ListBlank.append_pow_comm (symWord sym) (ca * u + cb * v + cc * w)
        (evalCanon u v w tail)).symm

def consSlope (sym ca cb cc : ℕ) (ts : List CTok) : List CTok :=
  if Nat.beq ca 0 && Nat.beq cb 0 && Nat.beq cc 0 then ts
  else consSlopeAux sym ca cb cc ts

theorem evalCanon_consSlope (u v w sym ca cb cc : ℕ) (ts : List CTok) :
    evalCanon u v w (consSlope sym ca cb cc ts) =
      ListBlank.append (symWord sym ^ (ca * u + cb * v + cc * w)) (evalCanon u v w ts) := by
  unfold consSlope
  cases hz : Nat.beq ca 0 && Nat.beq cb 0 && Nat.beq cc 0
  · exact evalCanon_consSlopeAux u v w sym ca cb cc ts
  · simp only [↓reduceIte]
    simp only [Bool.and_eq_true] at hz
    have ha := Nat.eq_of_beq_eq_true hz.1.1
    have hb := Nat.eq_of_beq_eq_true hz.1.2
    have hc := Nat.eq_of_beq_eq_true hz.2
    simp [ha, hb, hc, list_pow_zero]

def canonRight : List SymRun → List CTok
  | [] => []
  | ⟨sym, ⟨c0, ca, cb, cc⟩⟩ :: rest =>
    consBits (symWord sym ^ c0) (consSlope sym ca cb cc (canonRight rest))

theorem evalCanon_canonRight (u v w : ℕ) (r : List SymRun) :
    evalCanon u v w (canonRight r) = evalStk true u v w r := by
  induction r with
  | nil => rfl
  | cons top rest ih =>
    rcases top with ⟨sym, ⟨c0, ca, cb, cc⟩⟩
    rw [canonRight, evalCanon_consBits, evalCanon_consSlope, ih]
    simp only [evalStk, ↓reduceIte, Aff3.eval]
    rw [← ListBlank.append_assoc, ← list_pow_add]
    have hassoc : c0 + (ca * u + cb * v + cc * w) = c0 + ca * u + cb * v + cc * w := by omega
    rw [hassoc]

/-! ### Hub Configurations (`mkSymCfg`, `evalHub`, `checkHubEq`) and Symbolic Ops -/

structure SymCfg where
  q : ℕ
  dir : Bool
  prog : Bool
  left : List SymRun
  right : List SymRun
  deriving DecidableEq, Inhabited

def evalSymCfg (u v w : ℕ) (c : SymCfg) : Cfg (Fin 2) (Fin 6) :=
  WordRLE.dirCfg qOf c.q c.dir (evalStk false u v w c.left) (evalStk true u v w c.right)

def modePref : ℕ → List (Fin 2)
  | 0 => [1, 1, 1]
  | 1 | 4 => [1, 1, 1, 0, 0, 1, 1]
  | 2 | 5 => [1, 1, 1, 0, 1, 0, 1, 1, 1]
  | _ => [1, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 1]

def modeHasZ (m : ℕ) : Bool :=
  Nat.ble 4 m

def sepBits : List (Fin 2) := [1, 1, 1, 0, 0]
def sfxBits : List (Fin 2) := [1, 1]

def mkSymCfg (m : ℕ) (a b c : Aff3) : SymCfg :=
  let r0 := pushBits sfxBits []
  let r1 := pushSym 3 c r0
  let r2 := pushBits sepBits r1
  let r3 := pushSym 3 b r2
  let r4 := if modeHasZ m then pushBits [0, 0] r3 else r3
  let r5 := pushSym 2 a r4
  let r6 := pushBits ((1 : Fin 2) :: modePref m) r5
  ⟨5, true, false, [], r6⟩

def evalHub (m a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  evalSymCfg 0 0 0 (mkSymCfg m (Aff3.const a) (Aff3.const b) (Aff3.const c))

theorem evalSymCfg_mkSymCfg (m : ℕ) (a b c : Aff3) (u v w : ℕ) :
    evalSymCfg u v w (mkSymCfg m a b c) =
      evalHub m (a.eval u v w) (b.eval u v w) (c.eval u v w) := by
  unfold evalHub mkSymCfg evalSymCfg
  cases modeHasZ m <;>
    simp only [↓reduceIte, Bool.false_eq_true, evalStk_pushBits, evalStk_pushSym,
      Aff3.const_eval, evalStk]

def checkHubEq (g : SymCfg) (dm : ℕ) (da db dc : Aff3) : Bool :=
  Nat.beq g.q 5 && g.prog &&
    let target := mkSymCfg dm da db dc
    if g.dir then
      g.left.isEmpty && (canonRight g.right == canonRight target.right)
    else
      match popBit 1 g.left with
      | some [] =>
        canonRight (pushSym 1 Aff3.one g.right) == canonRight target.right
      | _ => false

theorem checkHubEq_sound {g : SymCfg} {dm : ℕ} {da db dc : Aff3}
    (hc : checkHubEq g dm da db dc = true) (u v w : ℕ) :
    g.prog = true ∧
      evalSymCfg u v w g = evalHub dm (da.eval u v w) (db.eval u v w) (dc.eval u v w) := by
  unfold checkHubEq at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨hq, hprog⟩, hbody⟩ := hc
  have hq5 : g.q = 5 := Nat.eq_of_beq_eq_true hq
  refine ⟨hprog, ?_⟩
  rw [← evalSymCfg_mkSymCfg]
  cases hd : g.dir
  · rw [hd] at hbody
    simp only [Bool.false_eq_true, ↓reduceIte] at hbody
    rcases hp : popBit 1 g.left with _ | lRem
    · simp [hp] at hbody
    · rw [hp] at hbody
      cases lRem with
      | cons _ _ => simp at hbody
      | nil =>
        have hcan : canonRight (pushSym 1 Aff3.one g.right) =
            canonRight (mkSymCfg dm da db dc).right := eq_of_beq hbody
        have hrEq : evalStk true u v w (pushSym 1 Aff3.one g.right) =
            evalStk true u v w (mkSymCfg dm da db dc).right := by
          rw [← evalCanon_canonRight, hcan, evalCanon_canonRight]
        rw [evalStk_pushSym] at hrEq
        simp only [↓reduceIte, symWord, Aff3.one_eval, list_pow_one] at hrEq
        have hlEq := popBit_sound false u v w 1 g.left [] hp
        simp only [evalSymCfg, hd, hq5, hlEq, evalStk, WordRLE.dirCfg, Bool.false_eq_true,
          ↓reduceIte]
        rw [Cfg.headLeft_cons]
        change Cfg.headRight (qOf 5) default
          (ListBlank.append [1] (evalStk true u v w g.right)) = _
        rw [hrEq]
        rfl
  · rw [hd] at hbody
    simp only [↓reduceIte, Bool.and_eq_true, List.isEmpty_iff] at hbody
    have hcan : canonRight g.right = canonRight (mkSymCfg dm da db dc).right :=
      eq_of_beq hbody.2
    have hrEq : evalStk true u v w g.right =
        evalStk true u v w (mkSymCfg dm da db dc).right := by
      rw [← evalCanon_canonRight, hcan, evalCanon_canonRight]
    simp only [evalSymCfg, hd, hq5, hbody.1, evalStk, hrEq]
    rfl

inductive SymOp where
  | zip (id : ℕ)
  | shiftWaL
  | shiftWbR
  | shiftWcL
  | shiftWaR0
  | splitWaLast
  | bounce
  | unroll
  | fold (side : Bool) (sym k : ℕ)
  deriving DecidableEq, Inhabited

def initKL : ℕ := 19
def initKR : ℕ := 18
def initQOut : ℕ := 5
def initDirOut : Bool := false
def initKLOut : ℕ := 2
def initLBOut : ℕ := 0x1
def initKROut : ℕ := 35
def initRBOut : ℕ := 0x36db6d9d7

noncomputable def zipCache : WordRLE.NatTrie ℕ :=
  .node (some 0x2bf8000704038d0012) (.node none (.node none (.node none (.node none (.node none
      (.leaf) (.node (some 0x3b00030300980003) (.leaf) (.leaf))) (.node (some 0xed2b06020008920015)
      (.leaf) (.node (some 0x4df50602000895000f) (.leaf) (.leaf)))) (.node (some
      0x1a203020104930011) (.node none (.leaf) (.node (some 0xb02000002130004) (.leaf) (.leaf)))
      (.node (some 0x700020200890002) (.leaf) (.node (some 0x4504000004250008) (.leaf) (.leaf)))))
      (.node (some 0x200010100980001) (.node none (.node none (.leaf) (.node (some
      0x3703000003120005) (.leaf) (.leaf))) (.node (some 0x1da5607020009910016) (.leaf) (.node (some
      0x15eb00070007820011) (.leaf) (.leaf)))) (.node (some 0x5600040202930005) (.node none (.leaf)
      (.node (some 0x2303000003230005) (.leaf) (.leaf))) (.node (some 0x500020200990002) (.leaf)
      (.node (some 0x201010002830002) (.leaf) (.leaf)))))) (.node (some 0x1870500050029000b) (.node
      none (.node none (.node none (.leaf) (.node (some 0x1000001210001) (.leaf) (.leaf))) (.node
      (some 0x5d0004000495000b) (.leaf) (.node (some 0x1be03020005910008) (.leaf) (.leaf)))) (.node
      (some 0x100010001810001) (.node none (.leaf) (.node (some 0x2b8b00070007820015) (.leaf)
      (.leaf))) (.node (some 0x38b05000005120005) (.leaf) (.node (some 0x1947304050702110013)
      (.leaf) (.leaf))))) (.node (some 0x3b03000003520003) (.node none (.node none (.leaf) (.node
      (some 0xeab0600000612000a) (.leaf) (.leaf))) (.node (some 0xc704000004220006) (.leaf) (.node
      (some 0x6a3a0404080018000d) (.leaf) (.leaf)))) (.node (some 0xc00020002a10003) (.node none
      (.leaf) (.node (some 0x1d20b0306020792001e) (.leaf) (.leaf))) (.node (some 0xc00020200aa0002)
      (.leaf) (.node (some 0x4704000004250006) (.leaf) (.leaf))))))) (.node (some
      0x2a00030300980003) (.node none (.node none (.node none (.node none (.leaf) (.node (some
      0x1703000003150005) (.leaf) (.leaf))) (.node (some 0x75700060600990006) (.leaf) (.node (some
      0x57576000a080293000b) (.leaf) (.leaf)))) (.node (some 0x102000002150002) (.node none (.leaf)
      (.node (some 0xf100040004a50007) (.leaf) (.leaf))) (.node (some 0x2000002230002) (.leaf)
      (.node (some 0x57573000a080291000f) (.leaf) (.leaf))))) (.node (some 0x1000100290001) (.node
      none (.node none (.leaf) (.node (some 0x2e00030300880003) (.leaf) (.leaf))) (.node (some
      0x7700040400990004) (.leaf) (.node (some 0x3a7695ab0d02000f920020) (.leaf) (.leaf)))) (.node
      (some 0x1503000003150007) (.node none (.leaf) (.node (some 0x769590902000b950018) (.leaf)
      (.leaf))) (.node (some 0x5300040202910009) (.leaf) (.node (some 0xd02000002530002) (.leaf)
      (.leaf)))))) (.node (some 0x2502010003820003) (.node none (.node none (.node none (.leaf)
      (.node (some 0x577600080602930009) (.leaf) (.leaf))) (.node (some 0x1a503020005950012) (.leaf)
      (.node (some 0x15f600070502830008) (.leaf) (.leaf)))) (.node (some 0x402000200380003) (.node
      none (.leaf) (.node (some 0x1f00030300890003) (.leaf) (.leaf))) (.node (some
      0x194760405070213000f) (.leaf) (.node (some 0x602000002310002) (.leaf) (.leaf))))) (.node
      (some 0x101000001350001) (.node none (.node none (.leaf) (.node (some 0x15f30007050281000c)
      (.leaf) (.leaf))) (.node (some 0x1d278030606039d001b) (.leaf) (.node (some
      0x17d00050500890005) (.leaf) (.leaf)))) (.node (some 0xdb020202029a0008) (.node none (.leaf)
      (.node (some 0x2bd7d78000d0a038d0018) (.leaf) (.leaf))) (.node (some 0x1700030003830007)
      (.leaf) (.leaf))))))

def fuelMode0 : ℕ := 211
noncomputable def streamMode0 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.leaf
    0x6c0201c01c0c0181c0140ac06cac06c01012806c00c19002020010456090000) (.leaf
    0xf20010400a01201b00d03006070020200c02402c10028040240c0181c0080ac)) (.node (.leaf
    0x3006072290020201102b01b0100700502b01b00f0700e0100d03006072290020) (.leaf
    0xf1201b100d0300607229002020010400a071201b00d0300607229002020120))) (.node (.node (.leaf
    0x20a0060762b01b00f0700e0100d0300607229002020010400a0) (.leaf
    0xf0020200c070000000001000000000100000000010000000000060010000000)) (.node (.leaf
    0x10004a006070160601502b01b01401009030060700202b01b0130300607) (.leaf
    0xf00607000000600100000060010000004001000000000002001000000000000)))) (.node (.node (.node
    (.leaf 0xc0201c01c0c0181c0140ac06cac0ac01012806c00c19002020010400a0100d03) (.leaf
    0x3c0181c058180540ac06c050040240c0181c0080ac06)) (.node (.leaf
    0x6001000000600100000040010000000000000010000000020000000010004a) (.leaf
    0xf006070160601502b01b0140100d03006070000))) (.node (.node (.leaf
    0x6001000000000100000040010010000000020000010000000000000010011a) (.leaf 0x0)) (.node (.leaf
    0x0) (.leaf 0x0))))) (.node (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))
    (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))))) (.node (.node (.node (.node
    (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0)
    (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0) (.leaf 0x0))
    (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0))))) (.node (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))
    (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))))

def fuelMode1 : ℕ := 6307
noncomputable def streamMode1 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x1c0c0181c0140ac06cac06c01012806c00c190020200104560901802b01b0170) (.leaf
    0xf700b0400a01201b01a0701902402c10028040240c0181c0080ac06c0201c0)) (.node (.leaf
    0x1303006072290020201d0700903006070020201c02b01b0040400a01201b01b0) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b0))) (.node (.node (.leaf
    0x1000000000100000040010000000000030010000000000000000000010a) (.leaf
    0x3c8a407c180780900e01009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x1a070220100d0300607229002020010400a01201b02103006072290020202007) (.leaf
    0xf00d030060722900202001040250400a01201b024060230700b0400a01201b0)))) (.node (.node (.node
    (.leaf 0x1b00f0700e010260700502b01b00f0700e0100d0300607229002020010400a01) (.leaf
    0xf0060700502b0)) (.node (.leaf
    0x1000000000100000000010000000000060010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000))) (.node (.node (.leaf
    0x210300607229002020200722901f06029030060700202b01b00807007030060) (.leaf
    0xf300607229002020010400a01202b100d0300607229002020010400a01201b)) (.node (.leaf
    0x10000000000070010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b01303006072290020200c0700000000010000000001000000000))))) (.node (.node (.node
    (.node (.leaf 0xec0340c0181c0080ac06c04c0c0181c8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c8a40080800410028048)) (.node (.leaf
    0x1000000000100000000010000000000070010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006072290020200c070000))) (.node (.node (.leaf
    0x801c8a407c180780900e01009030060700202b01b01303006072290020200c0) (.leaf
    0x3d00280480ec40340c0181c8a4008080041002804806c0840c0181c8a400808)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac32c01012806c00c29002020010) (.leaf
    0x3dc0080ac06c04c0c0181c008080301c02c100a81d8ac06c03c1c0380402)))) (.node (.node (.node
    (.leaf 0xb01401009030060700202b01b01303006070020200c0700b0400a01009030060) (.leaf
    0xf006070160601502b01)) (.node (.leaf
    0x1000000000100000000010000000000040000000000090000000000014a) (.leaf
    0xf0060762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x10000000001000000000100000000000b0010000000000000000000040a) (.leaf
    0x3c0981c0080ac06c0401c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x80010000000020000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf2b01b01303006072290020200c0700000000010000008001000000000100)))))) (.node (.node (.node
    (.node (.node (.leaf 0x40c0181c0080ac06c04c0c0181c8a4008080300900b0400a0100903006070020)
    (.leaf 0x3c8004100280480ac0340c0181c0080ac06c04c0c0181c8a4008080741c02)) (.node (.leaf
    0x10000000000000000000020a0060762b01b00f0700e0100d0300607a290020) (.leaf
    0xf3006072290020200c0700000000010000000001000000000100000000000f))) (.node (.node (.leaf
    0x1b01303006072290020200c0700b0400a071201b1009030060700202b01b0130) (.leaf
    0xf2b01b0130300607a290020200c0700b0400a01201b1009030060700202b0)) (.node (.leaf
    0x2804806c0840c0181e8a4008080801e8a407c180780900e0100903006070020) (.leaf
    0xfb14b00404a01b0030a400808004100280480ac40340c0181e8a40080800410)))) (.node (.node (.node
    (.leaf 0xb0402a0762b01b00f0700e01009030060700202b01b00807007030060700502) (.leaf
    0xf70020200c0700b0400a01009030060700202b01b01303006070020200c070)) (.node (.leaf
    0x110000000000004a0060700202b01b02d030060700202b01b013030060) (.leaf
    0xf700e0100d03006070000000001000000000100000000010000000000040000))) (.node (.node (.leaf
    0x100000000010000000000130010000000000000000000030a0060762b01b00f0) (.leaf
    0x3c0981c0b00900b0402b02b01b0100762b01b00f070000000001000000000)) (.node (.leaf
    0x100010000000010000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf2b01b0130300607a290020200c0700000000010000006001000000000100))))) (.node (.node (.node
    (.node (.leaf 0x40c0181c0080ac06c04c0c0181e8a4008080300900b0400a0100903006070020) (.leaf
    0x3c80041002804806c0340c0181c0080ac06c04c0c0181e8a4008080741c02)) (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607a290020) (.leaf
    0xf7a290020200c07000000000100000000010000000001000000000017001))) (.node (.node (.leaf
    0x300607a290020200c0700b0400a071201b1009030060700202b01b013030060) (.leaf
    0xf0130300607a290020200c0700b0400a01201b1009030060700202b01b013)) (.node (.leaf
    0x806c0840c0181e8a4008080801e8a407c180780900e01009030060700202b01b) (.leaf
    0xf2b01b00807007030060700502b1bb00404a01b0030a4008080041002804)))) (.node (.node (.node
    (.leaf 0x30060700202b01b01303006070020200c0700b0400a01201b100903006070020) (.leaf
    0xf700b0400a01201b009030060700202b01b02e0700502b01b00f0700e010090)) (.node (.leaf
    0xb0210300607002020200701f06029030060700202b01b01303006070020200c0) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201))) (.node (.node (.leaf
    0x1000000000100000000010000000000070000000000150000000000010a) (.leaf
    0x3dc0140ac72c01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf400a01201b00d030060700202012030060700202b01b013030060700202))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf
    0x3006070020201102b01b0100700502b01b00f0700e0100d0300607002020010) (.leaf
    0xf400a01201b100d0300607002020010400a071201b00d030060700202012)) (.node (.leaf
    0x140000000000020a0060762b01b00f0700e0100d0300607002020010) (.leaf
    0xf700e0100d030060700000000010000000001000000000100000000000800))) (.node (.node (.leaf
    0x1000000000100000000001b0010000000000000000000020a0060762b01b00f0) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f070000000001000000000)) (.node (.leaf
    0x1000000600100000000010000000000180010000000000000000010005a0060) (.leaf
    0x3c0140ac06cac0ac01012806c00c19002020010400a0100d030060700000060)))) (.node (.node (.node
    (.leaf 0x181c008080801c07c180780900e01009030060700202b01b008070070300607) (.leaf
    0x3c02c1002804806c0681c088040340c0181c8a4008080041002804806c0840c)) (.node (.leaf
    0x29002020010400a0100d030060722900202001040250400a01201b0240602307) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006072))) (.node (.node (.leaf
    0x1000000000100000040010000000000040010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x1201b0210300607002020200701f06029030060700202b01b00807007030060) (.leaf
    0xf100d0300607229002020010400a01202b100d0300607229002020010400a))))) (.node (.node (.node
    (.node (.leaf 0x40010000000000050010000000000000000000030a0060762b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006070020200c07000000000100000000010000)) (.node (.leaf
    0x100280480ec0340c0181c0080ac06c04c0c0181c008080300900b0400a010090) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c8a400808004))) (.node (.node (.leaf
    0x1000000000100000040010000000000050010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x801c8a407c180780900e01009030060700202b01b01303006072290020200c0) (.leaf
    0x3d00280480ec40340c0181c8a4008080041002804806c0840c0181c8a400808)))) (.node (.node (.node
    (.leaf 0x40a0060762b01b00f0700e0100d0300607229002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000000900100)) (.node (.leaf
    0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf 0x3c0181c0)))
    (.node (.node (.leaf 0x1000000800100000000010000000000060010000000020000000000005a) (.leaf
    0x3c0300900b0400a01009030060700202b01b01303006072290020200c070000)) (.node (.leaf
    0xb01b01303006072290020201d07009030060700202b01b013030060722900202) (.leaf
    0xf2b01b00f0700e0100d0300607229002020010400a01202b00d030060700202)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1000000000100000000000d0010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b01303006072290020200c070000000001)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006072290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b01303006072290020200c0700))) (.node (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0xf700202b01b00807007030060700502b12b00404a01b0030a4008080041002)) (.node (.leaf
    0x202b01b01303006070020200c0700b0402a0762b01b00f0700e01009030060) (.leaf
    0xf02d030060700202b01b01303006070020200c0700b0400a010090300607)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000400000000000f0000000000004a0060700202b01b) (.leaf
    0xf0060762b01b00f0700e0100d0300607000000000100000000)) (.node (.leaf
    0x1000000000100000000010000000000110010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x1000000000100000000000e0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)) (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e))))) (.node (.node (.node
    (.node (.leaf 0x10000000000150010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000)) (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009))) (.node (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b1ab00404a01b0030a4008080041002804806c40340c018)) (.node (.leaf
    0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807) (.leaf
    0xf7002020010400a01201b00d030060700202012030060700202b01b013030)))) (.node (.node (.node
    (.leaf 0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006)) (.node (.leaf
    0x80000000000120000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000))) (.node (.node (.leaf
    0x1000000000100000000010000000000190010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)) (.node (.leaf
    0x6001000000600100000000010000000000160010000000000000000010005a) (.leaf
    0xf003064008080741c0240c0181c0080ac06c03c0900e0100d03006070000))))))) (.node (.node (.node
    (.node (.node (.node (.leaf
    0x701f06029030060700202b01b00807007030060700502b01b2b04b00404a01b) (.leaf
    0xf0010400a01202b100d0300607002020010400a01201b021030060700202020)) (.node (.leaf
    0x30010000000000000000000030a0060762b01b00f0700e0100d030060700202) (.leaf
    0xf700202b01b0130300607000000c001000000000100000040010000000000))) (.node (.node (.leaf
    0x10a0060700502b01b00f0700e01201b00d030060700202b01b013030060) (.leaf
    0xf7000000000100000000010000000001001000000006000001000000000000)) (.node (.leaf
    0xc0181c0140ac06cac0ec01012806c00c1900202001040270701a0762b01b00f0) (.leaf
    0xf01303006070020200c02402c10028040240c0181c0080ac06c0201c01c0)))) (.node (.node (.node
    (.leaf 0x62b01b00f0700e0100d0300607002020010400a01203b00d030060700202b01b) (.leaf 0xf00607))
    (.node (.leaf 0x8001000000000100000040010000000000030010000000010000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x4008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3c8004100280480ec40340c0181c8a4008080041002804806c0840c0181c8a)) (.node (.leaf
    0x10000000000000000000040a0060762b01b00f0700e0100d03006072290020) (.leaf
    0xfb01b0100762b01b00f07000000000100000000010000000001000000000007))))) (.node (.node (.node
    (.node (.leaf 0x3c0181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02) (.leaf
    0x0)) (.node (.leaf 0x1000000000100000000010000000000040010000000030000000000005a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x2b01b01303006072290020201d07009030060700202b01b01303006072290020) (.leaf
    0xf62b01b00f0700e0100d0300607229002020010400a01202b00d03006070020)) (.node (.leaf
    0x10000000001000000000100000000000b0010000000000000000000020a00607) (.leaf
    0xf00a071201b1009030060700202b01b01303006072290020200c07000000000)))) (.node (.node (.node
    (.leaf 0x700b0400a01201b1009030060700202b01b01303006072290020200c0700b04) (.leaf
    0x3dc8a407c180780900e01009030060700202b01b01303006072290020200c)) (.node (.leaf
    0xa01202b100d0300607a29002020010400a01201b0210300607a29002020200) (.leaf
    0x3dc0080ac06c0201c01c0c0181c0140ac42c01012806c00c290020200104))) (.node (.node (.leaf
    0x202b01b01303006070020200c0700b0402a0762b01b00f0700e01009030060) (.leaf
    0xf02d030060700202b01b01303006070020200c0700b0400a010090300607)) (.node (.leaf
    0x1000000000100000000000400000000000d0000000000004a0060700202b01b) (.leaf
    0xf0060762b01b00f0700e0100d0300607000000000100000000)))))) (.node (.node (.node (.node
    (.node (.leaf 0x10000000001000000000100000000000f0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x1000000000100000000000c0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b01303006072290020200c07000000000100000060))) (.node (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e)) (.node (.leaf
    0x10000000000130010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000)))) (.node (.node (.node
    (.leaf 0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)) (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b18b00404a01b0030a4008080041002804806c40340c018))) (.node (.node (.leaf
    0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807) (.leaf
    0xf7002020010400a01201b00d030060700202012030060700202b01b013030)) (.node (.leaf
    0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006))))) (.node (.node (.node
    (.node (.leaf 0x80000000000100000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x1000000000100000000010000000000170010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000))) (.node (.node (.leaf
    0x6001000000600100000000010000000000140010000000000000000010005a) (.leaf
    0x3dc0140ac06cac12c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0x3c0840c0181c008080801c07c180780900e01009030060700202b01b0130)))) (.node (.node (.node
    (.leaf 0x100d0300607229002020010400a01203b100d0300607002020010400a01201b) (.leaf
    0xf0060762b01b00f0700e)) (.node (.leaf
    0xc001000000000100000040010000000000050010000000000000000000040a) (.leaf
    0x3c0981c0080ac06c0401c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x20010000000050000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf700202b01b01303006070020200c0700000000010000000001000000000100)) (.node (.leaf
    0x80741c0240c0181c0080ac06c04c0c0181c008080300900b0400a01009030060) (.leaf
    0x3cc0181c8a400808004100280480ac0340c0181c0080ac06c04c0c0181c0080))))))))) (.node (.node
    (.node (.node (.node (.node (.node (.leaf
    0x10000000000090010000000000000000000020a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b01303006070020200c0700000000010000000001000000000)) (.node (.leaf
    0x9030060700202b01b01303006070020200c0700b0400a071201b1009030060) (.leaf
    0xf00e01009030060700202b01b01303006072290020200c0700b0400a01201b1))) (.node (.node (.leaf
    0xc0181e8a4008080041002804806c0840c0181c8a4008080801c8a407c1807809) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a400808004100280480ac40340)) (.node (.leaf
    0x10000000001000000000100000000000d0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000a0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b01303006072290020200c07000000000100000180)) (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181c8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e))) (.node (.node (.leaf
    0x10000000000110010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b01303006072290020200c070000000001000000000100000000)) (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009))))) (.node (.node (.node
    (.node (.leaf 0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b16b00404a01b0030a4008080041002804806c40340c018)) (.node (.leaf
    0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807) (.leaf
    0xf7002020010400a01201b00d030060700202012030060700202b01b013030))) (.node (.node (.leaf
    0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006)) (.node (.leaf
    0x800000000000e0000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)))) (.node (.node (.node
    (.leaf 0x1000000000100000000010000000000150010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)) (.node (.leaf
    0x6001000000600100000000010000000000120010000000000000000010005a) (.leaf
    0x3cac06cac16c01012806c00c19002020010400a01201b100d03006070000))) (.node (.node (.leaf
    0x2b01b0100762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3c0181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b0)) (.node (.leaf
    0x1000000000100000000010000000000000010000000070000000000005a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x700202b01b01303006070020201d07009030060700202b01b01303006070020)
    (.leaf 0xf0060762b01b00f0700e0100d0300607002020010400a01202b00d03006)) (.node (.leaf
    0x1000000000100000000010000000000070010000000010000000000020a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3c0181c8a4008080801c07c180780900e01009030060700202b01b013030060)) (.node (.leaf
    0x607a29002020010400a01202b100d0300607229002020010400a01201b02103) (.leaf
    0xf0060762b01b00f0700e0100d030)))) (.node (.node (.node (.leaf
    0x10000000001000000000100000000000b0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x100000000010000000000080010000000020000000000005a0060700502b01b) (.leaf
    0xf00a01009030060700202b01b01303006070020200c070000000001000000c0))) (.node (.node (.leaf
    0x181c8a4008080741c0240c0181c0080ac06c04c0c0181c8a4008080300900b04) (.leaf
    0x3c40340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0)) (.node (.leaf
    0x100000000000f0010000000000000000000010a0060700502b01b00f0700e0) (.leaf
    0xf700202b01b01303006072290020200c07000000000100000000010000000))))) (.node (.node (.node
    (.node (.leaf 0x30060700202b01b01303006072290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)) (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0x3dd8ac06c03c1c038040340c0181e8a4008080041002804806c40340c018))) (.node (.node (.leaf
    0x1000000000100000000010000000000130010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)) (.node (.leaf
    0x6001000000600100000000010000000000100010000000000000000010005a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x400a01009030060700202b01b00807007030060700502b01b2b06b00404a01b) (.leaf
    0x3cc0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b)) (.node (.leaf
    0x1b00f0700e0100d0300607002020010400a01202b00d030060700202b01b0130) (.leaf 0xf0060762b0)))
    (.node (.node (.leaf 0x1000000000100000000010000000000050010000000030000000000020a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf
    0xd0300607229002020010400a01202b100d0300607002020010400a01201b0210) (.leaf
    0xf0060762b01b00f0700e0100)) (.node (.leaf
    0x1000000000100000000010000000000090010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x100000000010000000000060010000000040000000000005a0060700502b01b) (.leaf
    0xf00a01009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0x4c0c0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b04) (.leaf
    0x3c03c1c038040340c0181c8a4008080041002804806c0340c0181c0080ac06c)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000d0010000000000000000000010a0060700502b01b) (.leaf
    0xf201b1009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006070020200c0700b0400a071) (.leaf
    0x3e8a407c180780900e01009030060700202b01b01303006072290020200c070))) (.node (.node (.leaf
    0xa01201b100d0300607a29002020010400a01201b0210300607a290020202007) (.leaf
    0xf0060762b01b00f0700e0100d0300607a2900202001040)) (.node (.leaf
    0x1000000000100000000010000000000110010000000000000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000))))) (.node (.node (.node (.node (.leaf
    0x60010000006001000000000100000000000e0010000000000000000010005a) (.leaf
    0x3dc0140ac06cac1ec01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303))) (.node (.node (.leaf
    0x2804806c0840c0181c008080801c07c180780900e01009030060700202b01b) (.leaf
    0x3c03c1c038040340c0181c00808004100280480ac40340c0181c008080041)) (.node (.leaf
    0x100000000010000000000070010000000010000000000030a0060762b01b) (.leaf
    0x3c4806c0981c0b00900b0402b02b01b0100762b01b00f07000000000100000)))) (.node (.node (.node
    (.leaf 0x10000000000040010000000060000000000005a0060700502b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006070020200c07000000000100000000010000000)) (.node (.leaf
    0xc008080741c0240c0181c0080ac06c04c0c0181c008080300900b0400a010090) (.leaf
    0x3c40340c0181c008080041002804806c0340c0181c0080ac06c04c0c0181))) (.node (.node (.leaf
    0x100000000000b0010000000010000000000010a0060700502b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006070020200c07000000000100000000010000000)) (.node (.leaf
    0x201b1009030060700202b01b01303006070020200c0700b0400a071201b10090) (.leaf
    0x3d80780900e01009030060700202b01b01303006070020200c0700b0400a01)))))) (.node (.node (.node
    (.node (.node (.leaf 0x201b100d0300607a29002020010400a01201b0210300607a29002020200701f0)
    (.leaf 0xf0060762b01b00f0700e0100d0300607a29002020010400a01)) (.node (.leaf
    0x10000000001000000000100000000000f0010000000000000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000))) (.node (.node (.leaf
    0x60010000006001000000000100000000000c0010000000010000000010005a) (.leaf
    0x3cac06cac22c01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf402b02b01b0100762b01b00f0700e01009030060700202b01b013030060)))) (.node (.node (.node
    (.leaf 0x20000000000001680181c0140ac06c03c1c03804806c0981c0b00900b0) (.leaf
    0x3c0181c008080301c0000000004000000000400000000040000000000080040)) (.node (.leaf
    0xc0080ac06c04c0c0181c008080300900b0400a01009030060700202b01b01303) (.leaf
    0x3d002804806c0340c0181c0080ac06c04c0c0181c008080741c0240c0181))) (.node (.node (.leaf
    0x30000000000010a0060700502b01b00f0700e0100d0300607002020010) (.leaf
    0xf006070020200c0700000000010000000001000000000100000000000900100)) (.node (.leaf
    0xb01b01303006070020200c0700b0400a071201b1009030060700202b01b01303) (.leaf
    0xf700202b01b01303006070020200c0700b0400a01201b1009030060700202))))) (.node (.node (.node
    (.node (.leaf 0xc008080041002804806c0840c0181c008080801c07c180780900e01009030060) (.leaf
    0x3dd8ac06c03c1c038040340c0181e8a4008080041002804806c40340c0181)) (.node (.leaf
    0x10000000001000000000100000000000d0010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000))) (.node (.node (.leaf
    0x60010000006001000000000100000000000a0010000000030000000010005a) (.leaf
    0x3cac06cac26c01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0x2b01b0100762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3c900b0400a01009030060700202b01b01303006070020200c0700b0402b0)))) (.node (.node (.node
    (.leaf 0x2b01b01303006070020201d07009030060700202b01b01303006070020200c0) (.leaf
    0xf700502b01b00f0700e0100d0300607002020010400a01201b00d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000070010000000050000000000010a0060) (.leaf
    0xf400a071201b1009030060700202b01b01303006070020200c0700000000))) (.node (.node (.leaf
    0x200c0700b0400a01201b1009030060700202b01b01303006070020200c0700b0) (.leaf
    0x3dc008080801c07c180780900e01009030060700202b01b01303006070020)) (.node (.leaf
    0x300607002020010400a01201b100d0300607002020010400a01201b021030060) (.leaf
    0xf0060762b01b00f0700e0100d0))))))) (.node (.node (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000b0010000000010000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)) (.node (.leaf
    0x6001000000600100000000010000000000080010000000050000000010005a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x400a01009030060700202b01b00807007030060700502b01b2b0ab00404a01b) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c0700b)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060)))) (.node (.node (.node
    (.leaf 0x100d0300607002020010400a01201b100d0300607002020010400a01201b0210) (.leaf
    0xf0060762b01b00f0700e0)) (.node (.leaf
    0x1000000000100000000010000000000090010000000030000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000))) (.node (.node (.leaf
    0x6001000000600100000000010000000000060010000000070000000010005a) (.leaf
    0x3dc0140ac06cac2ec01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303))))) (.node (.node (.node
    (.node (.leaf 0x700502b01b00f0700e01201b0260762b01b00f0700e01009030060700202b01b) (.leaf
    0xf0060)) (.node (.leaf 0x6001000000600100000000010000000000040010000000090000000010005a)
    (.leaf 0x3cac06cac32c01012806c00c19002020010400a071201b100d03006070000))) (.node (.node
    (.leaf 0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf700e01201b0260762b01b00f0700e01009030060700202b01b013030060)) (.node (.leaf
    0x100000000000200100000000b0000000010015a0060700502b01b00f0) (.leaf
    0x3e806c00c19002020010400a01201b100d03006070000006001000000600100)))) (.node (.node (.node
    (.leaf 0xb00f0700e01009030060700202b01b00807007030060700502b01b2b0db00404) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01)) (.node (.leaf
    0x60010000006001000000000100000000000000100000000d0000000010025a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x10000000001000000000100100000000d0000010000000000000010032a0060) (.leaf 0x60)) (.node
    (.leaf 0x0) (.leaf 0x0)))))) (.node (.node (.node (.node (.node (.leaf 0x0) (.leaf 0x0))
    (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf
    0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))) (.node
    (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0)
    (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node
    (.leaf 0x0) (.leaf 0x0)))))))))

def fuelMode2 : ℕ := 7352
noncomputable def streamMode2 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x6c0201c01c0c0181c0140ac06cac06c01012806c00c190020200104560902f0) (.leaf
    0xf30060700202b01b01303006070020200c02402c10028040240c0181c0080ac)) (.node (.leaf
    0x7229002020120300607229002020310700b0400a01201b01a0700502b01b0300) (.leaf
    0xf700502b01b00f0700e0100d0300607229002020010400a01201b00d030060))) (.node (.node (.leaf
    0x10400a071201b00d03006072290020201203006072290020201102b01b0100) (.leaf
    0x3c0140ac2ac01012806c00c29002020010400a01201b100d030060722900202)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b008070070300607) (.leaf
    0xf400a01201b00d030060700202012030060700202b01b0130300607002020)))) (.node (.node (.node
    (.leaf 0x3006070020201102b01b0100700502b01b00f0700e0100d0300607002020010) (.leaf
    0xf400a01201b100d0300607002020010400a071201b00d030060700202012)) (.node (.leaf
    0x20000000000020a0060762b01b00f0700e0100d0300607002020010) (.leaf
    0xf700e0100d030060700000000010000000001000000000100000000000800))) (.node (.node (.leaf
    0x100000000010000000000090010000000000000000000020a0060762b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000)) (.node (.leaf
    0x80900e01009030060700202b01b01303006072290020200c0700b0400a01201b) (.leaf
    0x3cc0181c8a4008080041002804806c0840c0181c8a4008080801c8a407c1807))))) (.node (.node (.node
    (.node (.leaf 0x100d030060722900202001040330700b0400a01201b01a0762b01b0320100d0) (.leaf
    0x3c01012806c00c29002020010400a01201b100d0300607229002020010400a)) (.node (.leaf
    0x100762b01b00f0700e01009030060700202b01b00807007030060700502b0ab) (.leaf
    0xf700202012030060700202b01b01303006070020200c0700b0402b02b01b))) (.node (.node (.leaf
    0x30060700202b01b01303006070020201d07009030060700202b01b013030060) (.leaf
    0xf20010400a01201b0210300607002020200701f06029030060700202b01b013)) (.node (.leaf
    0x30000000000010a0060700502b01b00f0700e0100d03006070020) (.leaf
    0xf00f0700e0100d0300607000000000100000000010000000001000000000009)))) (.node (.node (.node
    (.leaf 0xc01c0c0181c0140ac2ec01012806c00c29002020010402b02b01b0100762b01b) (.leaf
    0x3cac06c04c0c0181c008080301c02c10028040240c0181c0080ac06c0201)) (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a071201b00903006070020) (.leaf
    0xf01f06029030060700202b01b01303006070020200c0700b0400a01201b0090))) (.node (.node (.leaf
    0x2b01b00f0700e0100d0300607002020010400a01201b02103006070020202007) (.leaf 0xf006070050))
    (.node (.leaf 0x1000000000100000000010000000000080000000000040000000000010a) (.leaf
    0x3cc0181c0140ac32c01012806c00c29002020010400a0100d03006070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070)
    (.leaf 0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)) (.node (.leaf
    0xa01201b009030060700202b01b02e0700502b01b00f0700e0100903006070020) (.leaf
    0xf7002020200701f06029030060700202b01b01303006070020200c0700b0400))) (.node (.node (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b021030060) (.leaf 0x0)) (.node
    (.leaf 0x1000000000100000000010000000000090000000000050000000000010a) (.leaf
    0x3dc0140ac36c01012806c00c29002020010400a071201b100d03006070000)))) (.node (.node (.node
    (.leaf 0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf70020200c0700b0402a0762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x7002020010400a01201b00d030060700202012030060700202b01b013030060) (.leaf
    0xf70020201203006070020201102b01b0100700502b01b00f0700e0100d03006))) (.node (.node (.leaf
    0x607002020010400a01201b100d0300607002020010400a071201b00d030060) (.leaf
    0xf0060762b01b00f0700e0100d03)) (.node (.leaf
    0x10000000001000000000100000000000a0000000000040000000000020a) (.leaf
    0x3dc0140ac3ac01012806c00c29002020010400a01201b100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202)) (.node (.leaf
    0x400000000000b0000000000004a0060700202b01b02d030060700202b01b0130) (.leaf
    0xf00f0700e0100d030060700000000010000000001000000000100000000000))) (.node (.node (.leaf
    0x1000000000100000000000d0010000000000000000000030a0060762b01b) (.leaf
    0x3cac06c0101002804806c0a00900b040340762b01b00f07000000000100000)) (.node (.leaf
    0x4a0060700202b01b02d030060700202b01b0080700703006070020) (.leaf
    0xf200c0700000000010000010001000000000100000000000600100000000000)))) (.node (.node (.node
    (.leaf 0x181c8a4008080300900b0400a01009030060700202b01b01303006072290020) (.leaf
    0x3c806c40340c0181c8a4008080041002804806c0340c0181c0080ac06c04c0c)) (.node (.leaf
    0x20010402b02b01b0100762b01b00f0700e0100d0300607229002020010400a01) (.leaf
    0x3cc0181c0140ac36c01012806c00c29002020010400a0100d03006072290020))) (.node (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)) (.node (.leaf
    0xa01201b009030060700202b01b02e0700502b01b00f0700e0100903006070020) (.leaf
    0xf7002020200701f06029030060700202b01b01303006070020200c0700b0400))))))) (.node (.node
    (.node (.node (.node (.node (.node (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b021030060) (.leaf 0x0)) (.node
    (.leaf 0x1000000000100000000010000000000090000000000060000000000010a) (.leaf
    0x3dc0140ac3ac01012806c00c29002020010400a071201b100d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf70020200c0700b0402a0762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x7002020010400a01201b00d030060700202012030060700202b01b013030060) (.leaf
    0xf70020201203006070020201102b01b0100700502b01b00f0700e0100d03006)))) (.node (.node (.node
    (.leaf 0x607002020010400a01201b100d0300607002020010400a071201b00d030060) (.leaf
    0xf0060762b01b00f0700e0100d03)) (.node (.leaf
    0x10000000001000000000100000000000a0000000000050000000000020a) (.leaf
    0x3dc0140ac3ec01012806c00c29002020010400a01201b100d03006070000))) (.node (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202)) (.node (.leaf
    0x400000000000c0000000000004a0060700202b01b02d030060700202b01b0130) (.leaf
    0xf00f0700e0100d030060700000000010000000001000000000100000000000))))) (.node (.node (.node
    (.node (.leaf 0x1000000000100000000000e0010000000000000000000030a0060762b01b) (.leaf
    0xf201b1009030060700202b01b01303006072290020200c07000000000100000)) (.node (.leaf
    0x180780900e01009030060700202b01b01303006072290020200c0700b0400a01) (.leaf
    0xf4a01b0030a4008080041002804806c0840c0181c8a4008080801c8a407c))) (.node (.node (.leaf
    0x700b0400a01201b1009030060700202b01b00807007030060700502b0db0040) (.leaf
    0xf0020200c0700b0400a01201b1009030060700202b01b01303006070020200c)) (.node (.leaf
    0x700202b01b0100700502b01b00f0700e01009030060700202b01b0130300607) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b009030060700202b02b02e)))) (.node (.node (.node
    (.leaf 0x300607002020010400a01201b0210300607002020200701f0602903006070020) (.leaf
    0xf0060700502b01b00f0700e0100d0)) (.node (.leaf
    0x1000000000100000000010000000000090000000000070000000000010a) (.leaf
    0x3dc0140ac3ac01012806c00c29002020010400a01201b100d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf700b0402b02b01b0100762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x700202b01b013030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf30060700202b01b013030060700202b01b01303006070020201d0700903006)))))) (.node (.node (.node
    (.node (.node (.leaf 0x700e0100d0300607002020010400a01201b0210300607002020200701f060290)
    (.leaf 0xf0060700502b01b00f0)) (.node (.leaf
    0x10000000001000000000100000000000b0000000000060000000000010a) (.leaf
    0x3dc0140ac3ec01012806c00c29002020010400a01201b100d03006070000))) (.node (.node (.leaf
    0x402b02b01b0100762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf200c0700b0400a01009030060700202b01b01303006070020200c0700b0)) (.node (.leaf
    0x3006070020200c0700b0400a071201b009030060700202b01b01303006070020) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b009030060700202b01b0130)))) (.node (.node (.node
    (.leaf 0x300607002020010400a01201b0210300607002020200701f0602903006070020) (.leaf
    0xf0060700502b01b00f0700e0100d0)) (.node (.leaf
    0x10000000001000000000100000000000a0000000000070000000000010a) (.leaf
    0x3c00c29002020010402b02b01b0100762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x700b0400a01009030060700202b01b00807007030060700502b10b00404a01b) (.leaf
    0xf200c0700b0400a071201b1009030060700202b01b01303006070020200c)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b01303006070020) (.leaf
    0xf30060700202b01b02e0700502b01b00f0700e01009030060700202b01b0130))))) (.node (.node (.node
    (.node (.leaf 0x701f06029030060700202b01b01303006070020200c0700b0400a01201b0090) (.leaf
    0xf2b01b00f0700e0100d0300607002020010400a01201b021030060700202020)) (.node (.leaf
    0x1000000000100000000000b0000000000080000000000010a006070050) (.leaf
    0x3c0140ac46c01012806c00c29002020010400a0100d03006070000000001000))) (.node (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b008070070300607) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b013030)) (.node (.leaf
    0x1303006070020200c0700b0402a0762b01b00f0700e01009030060700202b01b) (.leaf
    0xf300607002020010400a01201b00d030060700202012030060700202b01b0)))) (.node (.node (.node
    (.leaf 0x3006070020201203006070020201102b01b0100700502b01b00f0700e0100d0) (.leaf
    0xf300607002020010400a01201b100d0300607002020010400a071201b00d)) (.node (.leaf
    0x100000000000c0000000000070000000000020a0060762b01b00f0700e0100d0) (.leaf
    0x3e9002020010400a071201b100d030060700000000010000000001000000000))) (.node (.node (.leaf
    0xa01201b1009030060700202b01b00807007030060700502b12b00404a01b0030) (.leaf
    0xf62b01b00f0700e01009030060700202b01b01303006070020200c0700b0400)) (.node (.leaf
    0xc0700b0400a01009030060700202b01b01303006070020200c0700b0402a07) (.leaf
    0xf0060700202b01b02d030060700202b01b013030060700202))))))) (.node (.node (.node (.node
    (.node (.node (.leaf 0x10000000001000000000100000000000600000000000e0000000000004a) (.leaf
    0x3dc0140ac4ec01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202))) (.node (.node (.leaf
    0x100000000000014a006070160601502b01b01401009030060700202b01b0130) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004000000000)) (.node (.leaf
    0x10000000000120010000000000000000000040a0060762b01b00f0700e0) (.leaf
    0xf0060700202b01b0350762b01b00f07000000000100000000010000)))) (.node (.node (.node (.leaf
    0x60010000006001000000000100000000000a0010000000000000000010006a) (.leaf
    0x3dc0140ac06cac0ac01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0x3c0840c0181c8a4008080801c07c180780900e01009030060700202b01b0130))) (.node (.node (.leaf
    0x700b0400a01201b01a0762b01b0320100d0300607229002020010400a01201b) (.leaf
    0xf1201b100d0300607229002020010400a0100d03006072290020200104033)) (.node (.leaf
    0x20010402b02b01b0100762b01b00f0700e0100d0300607229002020010400a0) (.leaf
    0x3c40240c0181c0080ac06c0201c01c0c0181c0140ac26c01012806c00c29002))))) (.node (.node (.node
    (.node (.leaf 0x700b0400a071201b009030060700202b01b01303006070020200c0700b0400a0) (.leaf
    0xf0020200c0700b0400a01201b009030060700202b01b01303006070020200c0)) (.node (.leaf
    0x400a01201b0210300607002020200701f06029030060700202b01b0130300607) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010))) (.node (.node (.leaf
    0x1000000000100000000010000000000080000000000020000000000010a) (.leaf
    0x3cc0181c0140ac2ac01012806c00c29002020010400a0100d03006070000)) (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)))) (.node (.node (.node
    (.leaf 0xa01201b009030060700202b01b02e0700502b01b00f0700e0100903006070020) (.leaf
    0xf7002020200701f06029030060700202b01b01303006070020200c0700b0400)) (.node (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b021030060) (.leaf 0x0))) (.node
    (.node (.leaf 0x1000000000100000000010000000000090000000000030000000000010a) (.leaf
    0x3dc0140ac2ec01012806c00c29002020010400a071201b100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf70020200c0700b0402a0762b01b00f0700e01009030060700202b01b0130)))))) (.node (.node (.node
    (.node (.node (.leaf 0x7002020010400a01201b00d030060700202012030060700202b01b013030060)
    (.leaf 0xf70020201203006070020201102b01b0100700502b01b00f0700e0100d03006)) (.node (.leaf
    0x607002020010400a01201b100d0300607002020010400a071201b00d030060) (.leaf
    0xf0060762b01b00f0700e0100d03))) (.node (.node (.leaf
    0x10000000001000000000100000000000a0000000000020000000000020a) (.leaf
    0x3dc0140ac32c01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202)))) (.node (.node (.node
    (.leaf 0x40000000000090000000000004a0060700202b01b02d030060700202b01b0130) (.leaf
    0xf00f0700e0100d030060700000000010000000001000000000100000000000)) (.node (.leaf
    0x1000000000100000000000b0010000000000000000000030a0060762b01b) (.leaf
    0x3cac06c0101002804806c0a00900b040340762b01b00f07000000000100000))) (.node (.node (.leaf
    0x4a0060700202b01b02d030060700202b01b0080700703006070020) (.leaf
    0xf200c070000000001000000c001000000400100000000000400100000000100)) (.node (.leaf
    0xc0c0181c8a4008080300900b0400a01009030060700202b01b01303006070020) (.leaf
    0x3c4806c40340c0181c8a4008080041002804806c0340c0181c0080ac06c04))))) (.node (.node (.node
    (.node (.leaf 0x20010402b02b01b0100762b01b00f0700e0100d0300607229002020010400a0) (.leaf
    0xf20010400a071201b100d0300607229002020010400a0100d0300607229002)) (.node (.leaf
    0x6c40240c0181c0080ac06c0201c01c0c0181c0140ac32c01012806c00c290020) (.leaf
    0x3c03c1c038040240c0181c0080ac06c04c0c0181c008080301c02c100280480))) (.node (.node (.leaf
    0x60700202012030060700202b01b01303006070020200c0700b0402a0762b01b) (.leaf
    0xf0100700502b01b00f0700e0100d0300607002020010400a01201b00d030)) (.node (.leaf
    0x607002020010400a071201b00d03006070020201203006070020201102b01b) (.leaf
    0xf0060762b01b00f0700e0100d0300607002020010400a01201b100d03)))) (.node (.node (.node (.leaf
    0x10000000001000000000100000000000a0000000000030000000000020a) (.leaf
    0x3dc0140ac36c01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202))) (.node (.node (.leaf
    0x400000000000a0000000000004a0060700202b01b02d030060700202b01b0130) (.leaf
    0xf00f0700e0100d030060700000000010000000001000000000100000000000)) (.node (.leaf
    0x1000000000100000000000c0010000000000000000000030a0060762b01b) (.leaf
    0xf201b1009030060700202b01b01303006072290020200c07000000000100000))))))))) (.node (.node
    (.node (.node (.node (.node (.node (.leaf
    0x180780900e01009030060700202b01b01303006072290020200c0700b0400a01) (.leaf
    0x3c0340c0181c8a4008080041002804806c0840c0181c8a4008080801c8a407c)) (.node (.leaf
    0xac06c0201c01c0c0181c0140ac32c01012806c00c29002020010400a01201b1) (.leaf
    0x3dc0080ac06c04c0c0181c008080301c02c1002804806c40240c0181c008))) (.node (.node (.leaf
    0x1303006070020200c0700b0402b02b01b0100762b01b00f0700e01009030060) (.leaf
    0xf201d07009030060700202b01b013030060700202012030060700202b01b)) (.node (.leaf
    0x20200701f06029030060700202b01b013030060700202b01b01303006070020) (.leaf
    0xf700502b01b00f0700e0100d0300607002020010400a01201b0210300607002)))) (.node (.node (.node
    (.leaf 0x10000000001000000000100000000000b0000000000040000000000010a0060) (.leaf
    0x3c0140ac36c01012806c00c29002020010400a01201b100d030060700000000)) (.node (.leaf
    0x2b02b01b0100762b01b00f0700e01009030060700202b01b008070070300607) (.leaf
    0xf200c0700b0400a01009030060700202b01b01303006070020200c0700b04))) (.node (.node (.leaf
    0x3006070020200c0700b0400a071201b009030060700202b01b01303006070020) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b009030060700202b01b0130)) (.node (.leaf
    0x300607002020010400a01201b0210300607002020200701f0602903006070020) (.leaf
    0xf0060700502b01b00f0700e0100d0))))) (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000a0000000000050000000000010a) (.leaf
    0x3c00c29002020010402b02b01b0100762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x700b0400a01009030060700202b01b00807007030060700502b0eb00404a01b) (.leaf
    0xf200c0700b0400a071201b1009030060700202b01b01303006070020200c))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b01303006070020) (.leaf
    0xf30060700202b01b02e0700502b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x701f06029030060700202b01b01303006070020200c0700b0400a01201b0090) (.leaf
    0xf2b01b00f0700e0100d0300607002020010400a01201b021030060700202020)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000b0000000000060000000000010a006070050) (.leaf
    0x3c0140ac3ec01012806c00c29002020010400a0100d03006070000000001000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b008070070300607) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b013030))) (.node (.node (.leaf
    0x1303006070020200c0700b0402a0762b01b00f0700e01009030060700202b01b) (.leaf
    0xf300607002020010400a01201b00d030060700202012030060700202b01b0)) (.node (.leaf
    0x3006070020201203006070020201102b01b0100700502b01b00f0700e0100d0) (.leaf
    0xf300607002020010400a01201b100d0300607002020010400a071201b00d)))))) (.node (.node (.node
    (.node (.node (.leaf 0x100000000000c0000000000050000000000020a0060762b01b00f0700e0100d0)
    (.leaf 0x3e9002020010400a071201b100d030060700000000010000000001000000000)) (.node (.leaf
    0xa01201b1009030060700202b01b00807007030060700502b10b00404a01b0030) (.leaf
    0xf62b01b00f0700e01009030060700202b01b01303006070020200c0700b0400))) (.node (.node (.leaf
    0xc0700b0400a01009030060700202b01b01303006070020200c0700b0402a07) (.leaf
    0xf0060700202b01b02d030060700202b01b013030060700202)) (.node (.leaf
    0x10000000001000000000100000000000600000000000c0000000000004a) (.leaf
    0x3dc0140ac46c01012806c00c29002020010400a01201b100d03006070000)))) (.node (.node (.node
    (.leaf 0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202)) (.node (.leaf
    0xe0000000000014a006070160601502b01b01401009030060700202b01b0130) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004000000000))) (.node (.node (.leaf
    0x10000000000100010000000000000000000040a0060762b01b00f0700e0) (.leaf
    0xf0060700202b01b0350762b01b00f07000000000100000000010000)) (.node (.leaf
    0x6001000000600100000000010000000000080010000000000000000010006a) (.leaf
    0x3cac06cac0ec01012806c00c19002020010400a01201b100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0xb040340762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3cc0181c0080ac06c0201c01c0c0181c0080ac06c0101002804806c0a009)) (.node (.leaf
    0x40010000000000020010000000030000000000004a0060700202b01b02d0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000100))) (.node (.node (.leaf
    0x80041002804806c0340c0181c0080ac06c04c0c0181c008080300900b0400a0) (.leaf
    0x3cac06c03c1c038040340c0181c8a4008080041002804806c40340c0181c008)) (.node (.leaf
    0xd0300607229002020010400a0100d0300607229002020010402b02b01b010076) (.leaf
    0x3c00c29002020010400a01201b100d0300607229002020010400a071201b100)))) (.node (.node (.node
    (.leaf 0x1b00f0700e01009030060700202b01b00807007030060700502b0bb00404a01b) (.leaf
    0xf400a01009030060700202b01b01303006070020200c0700b0402a0762b0)) (.node (.leaf
    0x4a0060700202b01b02d030060700202b01b01303006070020200c0700b0) (.leaf
    0xf70000000001000000000100000000010000000000040000000000080000000))) (.node (.node (.leaf
    0xa0010000000000000000000030a0060762b01b00f0700e0100d030060) (.leaf
    0xf2b01b01303006070020200c070000000001000000000100000000010000)) (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01201b100903006070020) (.leaf
    0x3c80041002804806c0840c0181c8a4008080801c8a407c180780900e010090))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf
    0x10400a01201b100d0300607229002020010400a01201b100d03006072290020) (.leaf
    0x3cc0181c0080ac06c0201c01c0c0181c0140ac2ec01012806c00c29002020)) (.node (.leaf
    0x2b01b01303006070020200c0700b0402b02b01b0100762b01b00f0700e010090) (.leaf
    0xf30060700202b01b01303006070020200c0700b0400a0100903006070020))) (.node (.node (.leaf
    0x1201b009030060700202b01b01303006070020200c0700b0400a071201b0090) (.leaf
    0xf002020200701f06029030060700202b01b01303006070020200c0700b0400a)) (.node (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b0210300607) (.leaf 0x0)))) (.node
    (.node (.node (.leaf 0x10000000001000000000100000000000a0000000000030000000000010a) (.leaf
    0x3c00c29002020010402b02b01b0100762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x700b0400a01009030060700202b01b00807007030060700502b0cb00404a01b) (.leaf
    0xf200c0700b0400a071201b1009030060700202b01b01303006070020200c))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b01303006070020) (.leaf
    0xf30060700202b01b02e0700502b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x701f06029030060700202b01b01303006070020200c0700b0400a01201b0090) (.leaf
    0xf2b01b00f0700e0100d0300607002020010400a01201b021030060700202020))))) (.node (.node (.node
    (.node (.leaf 0x1000000000100000000000b0000000000040000000000010a006070050) (.leaf
    0x3c0140ac36c01012806c00c29002020010400a0100d03006070000000001000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b008070070300607) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b013030))) (.node (.node (.leaf
    0x1303006070020200c0700b0402a0762b01b00f0700e01009030060700202b01b) (.leaf
    0xf300607002020010400a01201b00d030060700202012030060700202b01b0)) (.node (.leaf
    0x3006070020201203006070020201102b01b0100700502b01b00f0700e0100d0) (.leaf
    0xf300607002020010400a01201b100d0300607002020010400a071201b00d)))) (.node (.node (.node
    (.leaf 0x100000000000c0000000000030000000000020a0060762b01b00f0700e0100d0) (.leaf
    0x3e9002020010400a071201b100d030060700000000010000000001000000000)) (.node (.leaf
    0xa01201b1009030060700202b01b00807007030060700502b0eb00404a01b0030) (.leaf
    0xf62b01b00f0700e01009030060700202b01b01303006070020200c0700b0400))) (.node (.node (.leaf
    0xc0700b0400a01009030060700202b01b01303006070020200c0700b0402a07) (.leaf
    0xf0060700202b01b02d030060700202b01b013030060700202)) (.node (.leaf
    0x10000000001000000000100000000000600000000000a0000000000004a) (.leaf
    0x3dc0140ac3ec01012806c00c29002020010400a01201b100d03006070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060)
    (.leaf 0xf3006070020200c0700b0400a01009030060700202b01b013030060700202)) (.node (.leaf
    0xc0000000000014a006070160601502b01b01401009030060700202b01b0130) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004000000000))) (.node (.node (.leaf
    0x100000000000e0010000000000000000000040a0060762b01b00f0700e0) (.leaf
    0xf0060700202b01b0350762b01b00f07000000000100000000010000)) (.node (.leaf
    0x6001000000600100000000010000000000060010000000000000000010006a) (.leaf
    0x3c01012806c00c1900202001040340762b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x80300900b0400a01009030060700202b01b00807007030060700502b01b2b04b) (.leaf
    0x3cc0181c008080041002804806c0340c0181c0080ac06c04c0c0181c0080)) (.node (.leaf
    0x2b02b01b0100762b01b00f0700e0100d0300607002020010400a01201b100d0) (.leaf
    0xf400a071201b100d0300607229002020010400a0100d03006070020200104))) (.node (.node (.leaf
    0xf0700e0100d0300607229002020010400a01201b100d0300607229002020010) (.leaf 0xf0060762b01b0))
    (.node (.leaf 0x1000000000100000000010000000000080010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000))))) (.node (.node (.node
    (.node (.leaf 0xc008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3c008080041002804806c40340c0181c8a4008080041002804806c0840c0181)) (.node (.leaf
    0x762b01b00f0700e0100d0300607229002020010400a01201b100d0300607229) (.leaf
    0x3c0201c01c0c0181c0140ac2ac01012806c00c29002020010402b02b01b010))) (.node (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01009030060700202b01b) (.leaf
    0xf1009030060700202b01b01303006070020200c0700b0400a071201b10090)) (.node (.leaf
    0xb00f0700e01009030060700202b01b01303006070020200c0700b0400a01201b) (.leaf
    0xf3006070020200c0700b0400a01201b009030060700202b01b02e0700502b01)))) (.node (.node (.node
    (.leaf 0x20010400a01201b0210300607002020200701f06029030060700202b01b0130) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002)) (.node (.leaf
    0x10000000001000000000100000000000b0000000000020000000000010a) (.leaf
    0x3cc0181c0140ac2ec01012806c00c29002020010400a0100d03006070000))) (.node (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)) (.node (.leaf
    0xb01b01303006070020200c0700b0402a0762b01b00f0700e0100903006070020) (.leaf
    0xf100d0300607002020010400a01201b00d030060700202012030060700202))))))) (.node (.node (.node
    (.node (.node (.node (.leaf
    0x1b00d03006070020201203006070020201102b01b0100700502b01b00f0700e0) (.leaf
    0xf100d0300607002020010400a01201b100d0300607002020010400a07120)) (.node (.leaf
    0x100000000000c0000000000010000000000020a0060762b01b00f0700e0) (.leaf
    0x3c00c29002020010400a071201b100d0300607000000000100000000010000))) (.node (.node (.leaf
    0x400a01201b1009030060700202b01b00807007030060700502b0cb00404a01b) (.leaf
    0xf762b01b00f0700e01009030060700202b01b01303006070020200c0700b)) (.node (.leaf
    0x200c0700b0400a01009030060700202b01b01303006070020200c0700b0402a0) (.leaf
    0xf0060700202b01b02d030060700202b01b01303006070020)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000060000000000080000000000004a) (.leaf
    0x3dc0140ac36c01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202))) (.node (.node (.leaf
    0xa0000000000014a006070160601502b01b01401009030060700202b01b0130) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004000000000)) (.node (.leaf
    0x100000000000c0010000000000000000000040a0060762b01b00f0700e0) (.leaf
    0xf0060700202b01b0350762b01b00f07000000000100000000010000))))) (.node (.node (.node (.node
    (.leaf 0x6001000000600100000000010000000000040010000000020000000010006a) (.leaf
    0x3dc0140ac06cac16c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0x3c0840c0181c008080801c07c180780900e01009030060700202b01b0130))) (.node (.node (.leaf
    0x201b100d0300607002020010400a01201b100d0300607002020010400a01201b) (.leaf
    0xf402b02b01b0100762b01b00f0700e0100d0300607229002020010400a01)) (.node (.leaf
    0x181c0140ac26c01012806c00c29002020010400a0100d0300607229002020010) (.leaf
    0x3c0181c008080301c02c100281c4806c40240c0181c0080ac06c0201c01c0c0)))) (.node (.node (.node
    (.leaf 0x2b01b01303006070020200c0700b0400a01201b1009030060700202b01b01303) (.leaf
    0xf01303006070020200c0700b0402a0762b01b00f0700e0100903006070020)) (.node (.leaf
    0x100d0300607002020010400a01201b00d030060700202012030060700202b01b) (.leaf
    0xf00d03006070020201203006070020201102b01b0100700502b01b00f0700e0))) (.node (.node (.leaf
    0x700502b0db0040400a01201b0360400a01201b102607002020010400a071201b) (.leaf
    0xf700b0402a0762b01b00f0700e01009030060700202b01b00807007030060)) (.node (.leaf
    0x400a01201b00d030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf3006070020201102b01b0100700502b01b00f0700e0100d030060700202001)))))) (.node (.node (.node
    (.node (.node (.leaf 0x10400a01201b100d0300607002020010400a071201b00d0300607002020120)
    (.leaf 0xf0060762b01b00f0700e0100d030060700202)) (.node (.leaf
    0x1000000000100000000010000000000080000000000050000000000020a) (.leaf
    0x3dc0140ac2ac01012806c00c29002020010400a071201b100d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf70020200c0700b0402a0762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x2b01b01303006070020200c0700b0400a01009030060700202b01b013030060) (.leaf
    0xf0060700202b01b02d0300607002)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000060000000000060000000000004a) (.leaf
    0x3dc0140ac2ec01012806c00c29002020010400a01201b100d03006070000)) (.node (.leaf
    0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf3006070020200c0700b0400a01009030060700202b01b013030060700202))) (.node (.node (.leaf
    0x80000000000014a006070160601502b01b01401009030060700202b01b0130) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004000000000)) (.node (.leaf
    0x100000000000a0010000000000000000000040a0060762b01b00f0700e0) (.leaf
    0xf0060700202b01b0350762b01b00f07000000000100000000010000))))) (.node (.node (.node (.node
    (.leaf 0x6001000000600100000000010000000000020010000000040000000010006a) (.leaf
    0x3cac06cac1ac01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0x2b01b0350762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf 0xf006070020)))
    (.node (.node (.leaf 0x6001000000600100000000010000000000000010000000060000000010006a)
    (.leaf 0xf0060700202b01b0350762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x6001000000000100000000010010000000060000010000000000000010013a) (.leaf 0x0)))) (.node
    (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf
    0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))))))))

def fuelMode3 : ℕ := 20396
noncomputable def streamMode3 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x1c0c0181c0140ac06cac06c01012806c00c190020200104560903702b02b0170) (.leaf
    0xf2b01b01303006070020200c02402c10028040240c0181c0080ac06c0201c0)) (.node (.leaf
    0x700202b01b010070020200c0700b0400a01201b009030060703803006070020) (.leaf
    0xf00202b01b01303006072290020201d0700903006072290020201c02b03b02e))) (.node (.node (.leaf
    0x290020201d07009030060700202b01b01303006072290020201d070090300607) (.leaf
    0xf700e01201b00d030060700202b01b013030060700202b01b01303006072)) (.node (.leaf
    0x100000000000a0010000000000000000000010a0060700502b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000100)))) (.node (.node (.node
    (.leaf 0x80900e01009030060700202b01b01303006072290020200c0700b0400a01201b) (.leaf
    0x3cc0181c8a4008080041002804806c0840c0181c8a4008080801c8a407c1807)) (.node (.leaf
    0x700202b01b01007016060150200c0700b0400a01201b00903006070220100d0) (.leaf
    0xf300607229002020010400a0100d0300607229002020010401802b02b02e))) (.node (.node (.leaf
    0x81c0140ac2ac01012806c00c29002020390701a0700502b01b00f0700e0100d0) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080480c0181c0080ac06c0201c01c0c01)) (.node (.leaf
    0x202001040250400a01201b024060230700b0400a01201b01a0702201201b00d0) (.leaf
    0xf10260700502b01b00f0700e0100d0300607002020010400a0100d030060700))))) (.node (.node (.node
    (.node (.leaf 0x10000000000040000000000060000000000012a0060700502b01b00f0700e0) (.leaf
    0x3cac2ec01012806c00c29002020120300607000000000100000000010000000)) (.node (.leaf
    0x70020200c0700b0400a01201b009030060700202b01b0080700703006070050) (.leaf
    0xf400a01201b0210300607002020200701f06029030060700202b01b01303006))) (.node (.node (.leaf
    0x1201b024060230700b0400a01201b01a0702201201b100d0300607002020010) (.leaf
    0xf700e0100d0300607002020010400a0100d030060700202001040250400a)) (.node (.leaf
    0x40000000000022a0060700502b01b00f0700e010260762b01b00f0) (.leaf
    0xf00a01201b00d03006070000000001000000000100000000010000000000060)))) (.node (.node (.node
    (.leaf 0xc0181c0080ac06c0201c01c0c0181c0140ac32c01012806c00c290020200104) (.leaf
    0x3c0101002804806c0e81c0681c0080ac06c0401c0140ac06c03c1c03804024)) (.node (.leaf
    0x300607002020200701f06029030060700202b01b00807007030060700202b02b) (.leaf
    0xf300607002020010400a01202b100d0300607002020010400a01201b0210))) (.node (.node (.leaf
    0x10000000000050000000000080000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700502b01b00f0700e0100d030060700000000010000000001000000000)) (.node (.leaf
    0x80ac06c0201c01c0c0181c0140ac36c01012806c00c290020201102b01b0100) (.leaf
    0x3cc0181c008080741c0240c0181c0080ac06c04c0c0181c008080480c0181c0)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1b0040400a01201b01b0700b0400a01201b01a07038030060700202b01b0130)
    (.leaf 0xf100d030060700202b01b01303006070020201d0700903006070020201c02b)) (.node (.leaf
    0x10000000000070000000000080000000000010a0060700502b01b00f0700e0) (.leaf
    0x3cac3ac01012806c00c29002020120300607000000000100000000010000000))) (.node (.node (.leaf
    0x70020200c0700b0400a071201b009030060700202b01b0080700703006070050) (.leaf
    0xf01303006070020200c0700b0400a01201b009030060700202b01b013030060)) (.node (.leaf
    0x7002020010400a01201b0210300607002020200701f06029030060700202b01b) (.leaf
    0xf001040250400a01201b024060230700b0400a01201b01a070220100d030060)))) (.node (.node (.node
    (.leaf 0x260700502b01b00f0700e0100d0300607002020010400a0100d030060700202) (.leaf
    0xf0060700502b01b00f0700e01)) (.node (.leaf
    0x1000000000100000000010000000000080000000000060000000000012a) (.leaf
    0x3dc0140ac3ec01012806c00c29002020010400a071201b00d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf400a01201b03a0701a0700502b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x7002020200701f06029030060700202b01b00807007030060700202b01b0040) (.leaf
    0xf00607002020010400a01202b100d0300607002020010400a01201b02103006))))) (.node (.node (.node
    (.node (.leaf 0x70000000000090000000000030a0060762b01b00f0700e0100d03) (.leaf
    0x3e9002020010400a01201b100d0300607000000000100000000010000000001)) (.node (.leaf
    0xf0700e01009030060700202b01b00807007030060700502b10b00404a01b0030) (.leaf
    0xf012030060700202b01b01303006070020200c0700b040270701a0762b01b00))) (.node (.node (.leaf
    0x100d0300607002020010400a01203b00d030060700202b01b013030060700202) (.leaf
    0xf0060762b01b00f0700e0)) (.node (.leaf
    0x10000000001000000000100000000000500000000000c0000000000030a) (.leaf
    0x3d2806c00c2900202001040270701a0762b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x200c0700b0400a01009030060700202b01b00807007030060700502b11b0040) (.leaf
    0xf3006070020200c0700b0400a01201b009030060700202b01b0130300607002)) (.node (.leaf
    0x20010400a01201b0210300607002020200701f06029030060700202b01b0130) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01203b100d0300607002))) (.node (.node (.leaf
    0x10000000001000000000100000000000700000000000a0000000000040a0060) (.leaf
    0x3c0181c0140ac4ac01012806c00c29002020010400a0100d030060700000000)) (.node (.leaf
    0x1303006070020200c0700b0400a01201b1009030060700202b01b0080700703) (.leaf
    0xf2b01b0100700202b01b0100700502b01b00f0700e01009030060700202b01b))))))) (.node (.node
    (.node (.node (.node (.node (.leaf
    0x20000000000120000000000005a0060700502b01b00f0700e01201b026070020) (.leaf
    0xf400a01201b100d030060700000000010000000001000000000100000000000)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac4ec01012806c00c29002020010) (.leaf
    0x3ec06c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c0380402))) (.node (.node (.leaf
    0x6070020201d07009030060700202b01b013030060700202012030060700202) (.leaf
    0xf700e0100d0300607002020010400a01202b00d030060700202b01b01303)) (.node (.leaf
    0x1000000000100000000000700000000000e0000000000020a0060762b01b00f0) (.leaf
    0xf402b02b01b0100762b01b00f0700e0100d03006070000000001000000000)))) (.node (.node (.node
    (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac52c01012806c00c29002020010) (.leaf
    0x3c0281c4806c0240c0181c0080ac06c04c0c0181c008080301c02c100280402)) (.node (.leaf
    0x200c0700b0400a01201b009030060700202b01b01303006070020200c0700b04) (.leaf
    0xf201b0210300607002020200701f06029030060700202b01b01303006070020))) (.node (.node (.leaf
    0xf0700e0100d0300607002020010400a01202b100d0300607002020010400a01) (.leaf 0xf0060762b01b0))
    (.node (.leaf 0x10000000001000000000100000000000900000000000c0000000000030a) (.leaf
    0x3cc0181c0140ac56c01012806c00c29002020010400a0100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)) (.node (.leaf
    0xf0700e01201b0260700202b01b0100700502b01b00f0700e0100903006070020) (.leaf
    0xf0060700502b01b00))) (.node (.node (.leaf
    0x1000000000100000000010000000000040000000000130000000000005a) (.leaf
    0x3dc0140ac5ac01012806c00c29002020010400a071201b100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf700b0402b02b01b0100762b01b00f0700e01009030060700202b01b0130)))) (.node (.node (.node
    (.leaf 0x700202b01b013030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf20010400a01201b00d030060700202b01b01303006070020201d0700903006)) (.node (.leaf
    0x100000000000010a0060700502b01b00f0700e0100d03006070020) (.leaf
    0xf00a01201b100d0300607000000000100000000010000000001000000000009))) (.node (.node (.leaf
    0xc0181c0080ac06c0201c01c0c0181c0140ac5ec01012806c00c290020200104) (.leaf
    0x3c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c03804024)) (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01009030060700202b01b) (.leaf
    0xf201b009030060700202b01b01303006070020200c0700b0400a071201b0090)))))) (.node (.node (.node
    (.node (.node (.leaf 0x2020200701f06029030060700202b01b01303006070020200c0700b0400a01)
    (.leaf 0xf7002020010400a01201b100d0300607002020010400a01201b0210300607)) (.node (.leaf
    0xb00000000000e0000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000))) (.node (.node (.leaf
    0x6c0201c01c0c0181c0140ac62c01012806c00c29002020010402b02b01b0100) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080301c02c10028040240c0181c0080ac)) (.node (.leaf
    0x201b1009030060700202b01b01303006070020200c0700b0400a071201b10090) (.leaf
    0xf00f0700e01009030060700202b01b01303006070020200c0700b0400a01)))) (.node (.node (.node
    (.leaf 0x140000000000005a0060700502b01b00f0700e01201b0260700502b01b) (.leaf
    0xf400a0100d03006070000000001000000000100000000010000000000060000)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac66c01012806c00c29002020010) (.leaf
    0x3c40240c0181c0080ac06c04c0c0181c008080301c02c100281c4806c402))) (.node (.node (.leaf
    0xb00f0700e01009030060700202b01b01303006070020200c0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01)) (.node (.leaf
    0x1000000000100000000010000000000040000000000160000000000015a) (.leaf
    0x3dc0140ac6ac01012806c00c29002020010400a071201b100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xfb01b00f0700e01201b0260762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x100000000010000000000020000000000180000000000025a0060700502) (.leaf
    0x3c01012806c00c29002020010400a01201b100d030060700000000010000))) (.node (.node (.leaf
    0x260762b01b00f0700e01009030060700202b01b00807007030060700502b1bb) (.leaf
    0xf0060700502b01b00f0700e01201b)) (.node (.leaf
    0x10000000001000000000100000000000000000000001a0000000000035a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x10000000001000000000100000000001a0010000000000000000000042a0060) (.leaf
    0x3cac06c0101002804806c0a00900b040270701a0762b01b00f0700000000)) (.node (.leaf
    0x607229002020200722901f06029030060700202b01b0080700703006070020) (.leaf
    0xf700b0400a01201b01a070220100d0300607229002020010400a01201b02103))) (.node (.node (.leaf
    0x229002020010400a0100d030060722900202001040250400a01201b024060230) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d0300607)) (.node (.leaf
    0x10000000001000000000100000000000a0010000000000000000000012a) (.leaf
    0x3c0300900b0400a01009030060700202b01b01303006072290020200c070000)))))))) (.node (.node
    (.node (.node (.node (.node (.node (.leaf
    0xb0400a01201b01a0702201201b00d030060700202b01b013030060722900202) (.leaf
    0xf20010400a0100d030060722900202001040250400a01201b02406023070)) (.node (.leaf
    0x60700502b01b00f0700e010260700502b01b00f0700e0100d03006072290020) (.leaf 0xf0))) (.node
    (.node (.leaf 0x10000000001000000000100000000000a0010000000000000000000012a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006072290020200c070000)) (.node (.leaf
    0x801c8a407c180780900e01009030060700202b01b01303006072290020200c0) (.leaf
    0x3dc08804806c40340c0181e8a4008080041002804806c0840c0181c8a400808)))) (.node (.node (.node
    (.leaf 0x12806c00c2900202001040250400a01201b024060230700b0400a01201b01a0) (.leaf
    0x3c80301c02c10028040240c0181c0080ac06c0201c01c0c0181c0140ac3ac01)) (.node (.leaf
    0x700e010260700502b01b00f0700e01009030060700202b01b01303006070020) (.leaf
    0xf0060700502b01b00f))) (.node (.node (.leaf
    0x10000000001000000000100000000000200000000000c0000000000005a) (.leaf
    0x3cc0181c0140ac3ec01012806c00c29002020010400a0100d03006070000)) (.node (.leaf
    0x2b01b00f0700e010260762b01b00f0700e01009030060700202b01b008070070) (.leaf 0xf006070050)))))
    (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000000000000000e0000000000015a) (.leaf
    0xf0060700502b01b00f0700e010260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100000000000e0010000000000000000000022a) (.leaf
    0x3d002804806c0e81c0681c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x29002020200701f06029030060700202b01b00807007030060700202b02b0040) (.leaf
    0xf20010400a01202b100d0300607229002020010400a01201b02103006072)) (.node (.leaf
    0x10000000000000000000030a0060762b01b00f0700e0100d0300607a290020) (.leaf
    0xf3006072290020200c0700000000010000000001000000000100000000000f)))) (.node (.node (.node
    (.leaf 0x80ac06c04c0c0181c8a4008080300900b0400a01009030060700202b01b0130) (.leaf
    0x3c0681c0e00c0181c0080ac06c04c0c0181e8a4008080741c0240c0181c0)) (.node (.leaf
    0x1d070090300607a290020201c02b01b0040400a01201b01b0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b0130300607a29002020))) (.node (.node (.leaf
    0x1000000000100000000010000000000130010000000000000000000010a) (.leaf
    0xf00b0400a071201b1009030060700202b01b01303006072290020200c070000)) (.node (.leaf
    0x200c0700b0400a01201b1009030060700202b01b0130300607a290020200c07) (.leaf
    0x3c80801e8a407c180780900e01009030060700202b01b0130300607a29002)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1201b01a070220100d0300607a29002020010400a01201b0210300607a290020)
    (.leaf 0x3ec5ac01012806c00c2900202001040250400a01201b024060230700b0400a0)) (.node (.leaf
    0x6070020200c0700b0400a01009030060700202b01b00807007030060700502) (.leaf
    0xf400a01201b0210300607002020200701f06029030060700202b01b01303))) (.node (.node (.leaf
    0xb00f0700e0100d03006070020200104a01b03c0703b0100d0300607002020010) (.leaf 0xf0060762b01))
    (.node (.leaf 0x1000000000100000000010000000000050000000000100000000000020a) (.leaf
    0x3cc0181c0140ac5ec01012806c00c29002020010400a0100d03006070000)))) (.node (.node (.node
    (.leaf 0x1b00f0700e010260700502b01b00f0700e01009030060700202b01b008070070) (.leaf
    0xf0060700502b0)) (.node (.leaf
    0x1000000000100000000010000000000000000000000160000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x1000000000100000000010000000000160010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x210300607a290020202007a2901f06029030060700202b01b00807007030060) (.leaf
    0xf300607a29002020010400a01202b100d0300607a29002020010400a01201b))))) (.node (.node (.node
    (.node (.leaf 0x10000000000170010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b0130300607a290020200c0700000000010000000001000000000)) (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181e8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a40080800410028048))) (.node (.node (.leaf
    0x1000000000100000000010000000000170010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b0130300607a290020200c070000)) (.node (.leaf
    0x801e8a407c180780900e01009030060700202b01b0130300607a290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808)))) (.node (.node (.node
    (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac72c01012806c00c29002020010) (.leaf
    0x3dc0080ac06c04c0c0181c008080301c02c100a81d8ac06c03c1c0380402)) (.node (.leaf
    0xb01401009030060700202b01b01303006070020200c0700b0400a01009030060) (.leaf
    0xf006070160601502b01))) (.node (.node (.leaf
    0x1000000000100000000010000000000040000000000190000000000014a) (.leaf
    0xf0060762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100000000001b0010000000000000000000040a) (.leaf
    0x3c0981c0080ac06c0401c0b00900b0402b02b01b0100762b01b00f070000))))))) (.node (.node (.node
    (.node (.node (.node (.leaf 0x180010000000020000000000005a0060700502b01b00f0700e01201b)
    (.leaf 0xf2b01b0130300607a290020200c0700000000010000006001000000000100)) (.node (.leaf
    0x40c0181c0080ac06c04c0c0181e8a4008080300900b0400a0100903006070020) (.leaf
    0x3c8004100280480ac0340c0181c0080ac06c04c0c0181e8a4008080741c02))) (.node (.node (.leaf
    0x10000000000000000000020a0060762b01b00f0700e0100d0300607a290020) (.leaf
    0xf300607a290020200c0700000000010000000001000000000100000000001f)) (.node (.leaf
    0x1b0130300607a290020200c0700b0400a071201b1009030060700202b01b0130) (.leaf
    0xf2b01b0130300607a290020200c0700b0400a01201b1009030060700202b0)))) (.node (.node (.node
    (.leaf 0x2804806c0840c0181e8a4008080801e8a407c180780900e0100903006070020) (.leaf
    0xfb24b00404a01b0030a400808004100280480ac40340c0181e8a40080800410)) (.node (.leaf
    0xb0402a0762b01b00f0700e01009030060700202b01b00807007030060700502) (.leaf
    0xf70020200c0700b0400a01009030060700202b01b01303006070020200c070))) (.node (.node (.leaf
    0x210000000000004a0060700202b01b02d030060700202b01b013030060) (.leaf
    0xf700e0100d03006070000000001000000000100000000010000000000040000)) (.node (.leaf
    0x100000000010000000000230010000000000000000000030a0060762b01b00f0) (.leaf
    0x3c0981c0b00900b0402b02b01b0100762b01b00f070000000001000000000))))) (.node (.node (.node
    (.node (.leaf 0x200010000000010000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf2b01b0130300607a290020200c0700000000010000006001000000000100)) (.node (.leaf
    0x40c0181c0080ac06c04c0c0181e8a4008080300900b0400a0100903006070020) (.leaf
    0x3c80041002804806c0340c0181c0080ac06c04c0c0181e8a4008080741c02))) (.node (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607a290020) (.leaf
    0xf7a290020200c07000000000100000000010000000001000000000027001)) (.node (.leaf
    0x300607a290020200c0700b0400a071201b1009030060700202b01b013030060) (.leaf
    0xf0130300607a290020200c0700b0400a01201b1009030060700202b01b013)))) (.node (.node (.node
    (.leaf 0x806c0840c0181e8a4008080801e8a407c180780900e01009030060700202b01b) (.leaf
    0xf2b01b00807007030060700502b2bb00404a01b0030a4008080041002804)) (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01201b100903006070020) (.leaf
    0xf700b0400a01201b009030060700202b01b02e0700502b01b00f0700e010090))) (.node (.node (.leaf
    0xb0210300607002020200701f06029030060700202b01b01303006070020200c0) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201)) (.node (.leaf
    0x1000000000100000000010000000000070000000000250000000000010a) (.leaf
    0x3dc0140acb2c01012806c00c29002020010400a01201b100d03006070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0xc0700b0402a0762b01b00f0700e01009030060700202b01b00807007030060)
    (.leaf 0xf400a01201b00d030060700202012030060700202b01b013030060700202)) (.node (.leaf
    0x3006070020201102b01b0100700502b01b00f0700e0100d0300607002020010) (.leaf
    0xf400a01201b100d0300607002020010400a071201b00d030060700202012))) (.node (.node (.leaf
    0x240000000000020a0060762b01b00f0700e0100d0300607002020010) (.leaf
    0xf700e0100d030060700000000010000000001000000000100000000000800)) (.node (.leaf
    0x1000000000100000000002b0010000000000000000000020a0060762b01b00f0) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f070000000001000000000)))) (.node (.node (.node
    (.leaf 0x1000000600100000000010000000000280010000000000000000010005a0060) (.leaf
    0x3c0140ac06cac0ac01012806c00c19002020010400a0100d030060700000060)) (.node (.leaf
    0x6070020200c0700b0400a01201b1009030060700202b01b008070070300607) (.leaf
    0x3cc0181c8a4008080801c07c180780900e01009030060700202b01b01303))) (.node (.node (.leaf
    0xb0400a01201b00903006070220100d0300607229002020010400a01201b0210) (.leaf
    0xf00607229002020010401802b02b02e0700202b01b01007016060150200c070)) (.node (.leaf
    0x20390701a0700502b01b00f0700e0100d0300607229002020010400a0100d03) (.leaf
    0x3c0201c01c0c0181c0140ac26c01012806c00c29002020120300607229002))))) (.node (.node (.node
    (.node (.leaf 0x700202b01b01303006070020200c0700b0400a01201b009030060700202b01b) (.leaf
    0xf00d0300607002020010400a01201b0210300607002020200701f0602903006)) (.node (.leaf
    0x700202001040250400a01201b024060230700b0400a01201b01a0702201201b1) (.leaf
    0xf700e010260762b01b00f0700e0100d0300607002020010400a0100d030060))) (.node (.node (.leaf
    0x10000000000060000000000020000000000022a0060700502b01b00f0) (.leaf
    0x3d2806c00c29002020010400a01201b00d03006070000000001000000000100)) (.node (.leaf
    0x502b01b00f0700e01009030060700202b01b00807007030060700502b0ab0040) (.leaf
    0xf7007030060700202b02b0040400a01201b03a0701a0700202b01b0100700)))) (.node (.node (.node
    (.leaf 0x20010400a01201b0210300607002020200701f06029030060700202b01b0080) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01202b100d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000050000000000060000000000030a0060) (.leaf
    0x3c00c290020201102b01b0100700502b01b00f0700e0100d030060700000000))) (.node (.node (.leaf
    0x30060700202012030060700202b01b00807007030060700502b0bb00404a01b) (.leaf
    0xf7038030060700202b01b01303006070020201d07009030060700202b01b013)) (.node (.leaf
    0xd0700903006070020201c02b01b0040400a01201b01b0700b0400a01201b01a0) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b01303006070020201))))))))) (.node (.node
    (.node (.node (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000070000000000060000000000010a) (.leaf
    0x3ec06c0201c01c0c0181c0140ac32c01012806c00c290020201203006070000)) (.node (.leaf
    0x60700202b01b01303006070020200c0700b0400a071201b009030060700202) (.leaf
    0xf6029030060700202b01b01303006070020200c0700b0400a01201b00903))) (.node (.node (.leaf
    0xb01a070220100d0300607002020010400a01201b0210300607002020200701f0) (.leaf
    0xf00a0100d030060700202001040250400a01201b024060230700b0400a01201)) (.node (.leaf
    0x700502b01b00f0700e010260700502b01b00f0700e0100d03006070020200104) (.leaf 0xf0060))))
    (.node (.node (.node (.leaf 0x1000000000100000000010000000000080000000000040000000000012a)
    (.leaf 0x3dc0140ac36c01012806c00c29002020010400a071201b00d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf400a01201b03a0701a0700502b01b00f0700e01009030060700202b01b0130))) (.node (.node (.leaf
    0x7002020200701f06029030060700202b01b00807007030060700202b01b0040) (.leaf
    0xf00607002020010400a01202b100d0300607002020010400a01201b02103006)) (.node (.leaf
    0x70000000000070000000000030a0060762b01b00f0700e0100d03) (.leaf
    0x3e9002020010400a01201b100d0300607000000000100000000010000000001))))) (.node (.node (.node
    (.node (.leaf 0xf0700e01009030060700202b01b00807007030060700502b0eb00404a01b0030) (.leaf
    0xf012030060700202b01b01303006070020200c0700b040270701a0762b01b00)) (.node (.leaf
    0x100d0300607002020010400a01203b00d030060700202b01b013030060700202) (.leaf
    0xf0060762b01b00f0700e0))) (.node (.node (.leaf
    0x10000000001000000000100000000000500000000000a0000000000030a) (.leaf
    0x3d2806c00c2900202001040270701a0762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x200c0700b0400a01009030060700202b01b00807007030060700502b0fb0040) (.leaf
    0xf3006070020200c0700b0400a01201b009030060700202b01b0130300607002)))) (.node (.node (.node
    (.leaf 0x20010400a01201b0210300607002020200701f06029030060700202b01b0130) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01203b100d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000070000000000080000000000040a0060) (.leaf
    0x3c0181c0140ac42c01012806c00c29002020010400a0100d030060700000000))) (.node (.node (.leaf
    0x1303006070020200c0700b0400a01201b1009030060700202b01b0080700703) (.leaf
    0xf2b01b0100700202b01b0100700502b01b00f0700e01009030060700202b01b)) (.node (.leaf
    0x20000000000100000000000005a0060700502b01b00f0700e01201b026070020) (.leaf
    0xf400a01201b100d030060700000000010000000001000000000100000000000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac46c01012806c00c29002020010)
    (.leaf 0x3ec06c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c0380402)) (.node (.leaf
    0x6070020201d07009030060700202b01b013030060700202012030060700202) (.leaf
    0xf700e0100d0300607002020010400a01202b00d030060700202b01b01303))) (.node (.node (.leaf
    0x1000000000100000000000700000000000c0000000000020a0060762b01b00f0) (.leaf
    0xf402b02b01b0100762b01b00f0700e0100d03006070000000001000000000)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac4ac01012806c00c29002020010) (.leaf
    0x3c0281c4806c0240c0181c0080ac06c04c0c0181c008080301c02c100280402)))) (.node (.node (.node
    (.leaf 0x200c0700b0400a01201b009030060700202b01b01303006070020200c0700b04) (.leaf
    0xf201b0210300607002020200701f06029030060700202b01b01303006070020)) (.node (.leaf
    0xf0700e0100d0300607002020010400a01202b100d0300607002020010400a01) (.leaf 0xf0060762b01b0)))
    (.node (.node (.leaf 0x10000000001000000000100000000000900000000000a0000000000030a) (.leaf
    0x3cc0181c0140ac4ec01012806c00c29002020010400a0100d03006070000)) (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b))))) (.node (.node (.node
    (.node (.leaf 0xf0700e01201b0260700202b01b0100700502b01b00f0700e0100903006070020) (.leaf
    0xf0060700502b01b00)) (.node (.leaf
    0x1000000000100000000010000000000040000000000110000000000005a) (.leaf
    0x3dc0140ac52c01012806c00c29002020010400a071201b100d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf700b0402b02b01b0100762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x700202b01b013030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf20010400a01201b00d030060700202b01b01303006070020201d0700903006)))) (.node (.node (.node
    (.leaf 0xe0000000000010a0060700502b01b00f0700e0100d03006070020) (.leaf
    0xf00a01201b100d0300607000000000100000000010000000001000000000009)) (.node (.leaf
    0xc0181c0080ac06c0201c01c0c0181c0140ac56c01012806c00c290020200104) (.leaf
    0x3c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c03804024))) (.node (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01009030060700202b01b) (.leaf
    0xf201b009030060700202b01b01303006070020200c0700b0400a071201b0090)) (.node (.leaf
    0x2020200701f06029030060700202b01b01303006070020200c0700b0400a01) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a01201b0210300607))))))) (.node (.node (.node
    (.node (.node (.node (.leaf 0xb00000000000c0000000000020a0060762b01b00f0700e0100d030060)
    (.leaf 0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x6c0201c01c0c0181c0140ac5ac01012806c00c29002020010402b02b01b0100) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080301c02c10028040240c0181c0080ac))) (.node (.node (.leaf
    0x201b1009030060700202b01b01303006070020200c0700b0400a071201b10090) (.leaf
    0xf00f0700e01009030060700202b01b01303006070020200c0700b0400a01)) (.node (.leaf
    0x120000000000005a0060700502b01b00f0700e01201b0260700502b01b) (.leaf
    0xf400a0100d03006070000000001000000000100000000010000000000060000)))) (.node (.node (.node
    (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac5ec01012806c00c29002020010) (.leaf
    0x3c40240c0181c0080ac06c04c0c0181c008080301c02c100281c4806c402)) (.node (.leaf
    0xb00f0700e01009030060700202b01b01303006070020200c0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01))) (.node (.node (.leaf
    0x1000000000100000000010000000000040000000000140000000000015a) (.leaf
    0x3dc0140ac62c01012806c00c29002020010400a071201b100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xfb01b00f0700e01201b0260762b01b00f0700e01009030060700202b01b0130))))) (.node (.node (.node
    (.node (.leaf 0x100000000010000000000020000000000160000000000025a0060700502) (.leaf
    0x3c01012806c00c29002020010400a01201b100d030060700000000010000)) (.node (.leaf
    0x260762b01b00f0700e01009030060700202b01b00807007030060700502b19b) (.leaf
    0xf0060700502b01b00f0700e01201b))) (.node (.node (.leaf
    0x1000000000100000000010000000000000000000000180000000000035a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010000000000180010000000000000000000042a0060) (.leaf
    0x3cac06c0101002804806c0a00900b040270701a0762b01b00f0700000000)))) (.node (.node (.node
    (.leaf 0x10300607229002020200701f06029030060700202b01b0080700703006070020) (.leaf
    0xf700b0400a01201b01a070220100d0300607229002020010400a01201b02)) (.node (.leaf
    0x229002020010400a0100d030060722900202001040250400a01201b024060230) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d0300607))) (.node (.node (.leaf
    0x1000000000100000000010000000000080010000000000000000000012a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0xb0400a01201b01a0702201201b00d030060700202b01b01303006072290020) (.leaf
    0xf002020010400a0100d030060722900202001040250400a01201b0240602307)))))) (.node (.node (.node
    (.node (.node (.leaf 0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d0300607229)
    (.leaf 0x0)) (.node (.leaf 0x1000000000100000000010000000000080010000000000000000000012a)
    (.leaf 0xf700b0400a01201b1009030060700202b01b01303006072290020200c070000))) (.node (.node
    (.leaf 0x801c8a407c180780900e01009030060700202b01b01303006072290020200c0) (.leaf
    0x3dc08804806c40340c0181c8a4008080041002804806c0840c0181c8a400808)) (.node (.leaf
    0xd0300607a2900202001040250400a01201b024060230700b0400a01201b01a0) (.leaf
    0x3cac06c0201c01c0c0181c0140ac36c01012806c00c29002020010400a010)))) (.node (.node (.node
    (.leaf 0xf0060700502b01b00f0700e010260762b01b00f0700e0100903006070020) (.leaf 0x0)) (.node
    (.leaf 0x10000000001000000000100000000000000000000000c0000000000015a) (.leaf
    0xf0060700502b01b00f0700e010260762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x10000000001000000000100000000000c0010000000000000000000022a) (.leaf
    0x3d002804806c0e81c0681c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x29002020200701f06029030060700202b01b00807007030060700202b02b0040) (.leaf
    0xf20010400a01202b100d0300607229002020010400a01201b02103006072))))) (.node (.node (.node
    (.node (.leaf 0x10000000000000000000030a0060762b01b00f0700e0100d03006072290020) (.leaf
    0xf3006072290020200c0700000000010000000001000000000100000000000d)) (.node (.leaf
    0x80ac06c04c0c0181c8a4008080300900b0400a01009030060700202b01b0130) (.leaf
    0x3c0681c0e00c0181c0080ac06c04c0c0181c8a4008080741c0240c0181c0))) (.node (.node (.leaf
    0x1d070090300607a290020201c02b01b0040400a01201b01b0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b0130300607a29002020)) (.node (.leaf
    0x1000000000100000000010000000000110010000000000000000000010a) (.leaf
    0xf00b0400a071201b1009030060700202b01b01303006072290020200c070000)))) (.node (.node (.node
    (.leaf 0x200c0700b0400a01201b1009030060700202b01b01303006072290020200c07) (.leaf
    0x3c80801e8a407c180780900e01009030060700202b01b0130300607a29002)) (.node (.leaf
    0x1201b01a070220100d0300607a29002020010400a01201b0210300607a290020) (.leaf
    0x3ec52c01012806c00c2900202001040250400a01201b024060230700b0400a0))) (.node (.node (.leaf
    0x6070020200c0700b0400a01009030060700202b01b00807007030060700502) (.leaf
    0xf400a01201b0210300607002020200701f06029030060700202b01b01303)) (.node (.leaf
    0xb00f0700e0100d03006070020200104a01b03c0703b0100d0300607002020010) (.leaf
    0xf0060762b01)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000500000000000e0000000000020a) (.leaf
    0x3cc0181c0140ac56c01012806c00c29002020010400a0100d03006070000)) (.node (.leaf
    0x1b00f0700e010260700502b01b00f0700e01009030060700202b01b008070070) (.leaf
    0xf0060700502b0))) (.node (.node (.leaf
    0x1000000000100000000010000000000000000000000140000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010000000000140010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)))) (.node (.node (.node
    (.leaf 0x210300607a290020202007a2901f06029030060700202b01b00807007030060) (.leaf
    0xf300607a29002020010400a01202b100d0300607a29002020010400a01201b)) (.node (.leaf
    0x10000000000150010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b0130300607a290020200c0700000000010000000001000000000))) (.node (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181e8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a40080800410028048)) (.node (.leaf
    0x1000000000100000000010000000000150010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b0130300607a290020200c070000))))) (.node (.node (.node
    (.node (.leaf 0x801e8a407c180780900e01009030060700202b01b0130300607a290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808)) (.node (.leaf
    0x40a0060762b01b00f0700e0100d0300607a29002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000001900100))) (.node (.node (.leaf
    0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf 0x3c0181c0))
    (.node (.leaf 0x1000000600100000000010000000000160010000000020000000000005a) (.leaf
    0x3c0300900b0400a01009030060700202b01b0130300607a290020200c070000)))) (.node (.node (.node
    (.leaf 0xb01b0130300607a290020201d07009030060700202b01b0130300607a2900202) (.leaf
    0xf2b01b00f0700e0100d0300607a29002020010400a01202b00d030060700202)) (.node (.leaf
    0x1000000000100000000001d0010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b0130300607a290020200c070000000001))) (.node (.node (.leaf
    0xb0400a01201b1009030060700202b01b0130300607a290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b0130300607a290020200c0700)) (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0xf700202b01b00807007030060700502b22b00404a01b0030a4008080041002)))))) (.node (.node (.node
    (.node (.node (.leaf 0x202b01b01303006070020200c0700b0402a0762b01b00f0700e01009030060)
    (.leaf 0xf02d030060700202b01b01303006070020200c0700b0400a010090300607)) (.node (.leaf
    0x1000000000100000000000400000000001f0000000000004a0060700202b01b) (.leaf
    0xf0060762b01b00f0700e0100d0300607000000000100000000))) (.node (.node (.leaf
    0x1000000000100000000010000000000210010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x1000000000100000000001e0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)))) (.node (.node (.node
    (.leaf 0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e)) (.node (.leaf
    0x10000000000250010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000))) (.node (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)) (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b2ab00404a01b0030a4008080041002804806c40340c018))))) (.node (.node (.node
    (.node (.leaf 0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807) (.leaf
    0xf7002020010400a01201b00d030060700202012030060700202b01b013030)) (.node (.leaf
    0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006))) (.node (.node (.leaf
    0x80000000000220000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x1000000000100000000010000000000290010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)))) (.node (.node (.node (.leaf
    0x6001000000600100000000010000000000260010000000000000000010005a) (.leaf
    0x3cac06cac0ec01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0x270701a0762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3dc0080ac06c0201c01c0c0181c0080ac06c0101002804806c0a00900b04))) (.node (.node (.leaf
    0x100d0300607002020010400a01201b0210300607002020200701f06029030060) (.leaf
    0xf722900202001040250400a01201b024060230700b0400a01201b01a070220)) (.node (.leaf
    0xe010260700502b01b00f0700e0100d0300607229002020010400a0100d030060) (.leaf
    0xf0060700502b01b00f0700))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000060010000000000000000000012a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x30700b0400a01201b01a0702201201b00d030060700202b01b01303006070020) (.leaf
    0xf7229002020010400a0100d030060700202001040250400a01201b0240602))) (.node (.node (.leaf
    0x12a0060700502b01b00f0700e010260700502b01b00f0700e0100d030060) (.leaf
    0xf70000000001000000000100000000010000000000060010000000000000000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3dc8a4008080801c8a407c180780900e01009030060700202b01b013030060)))) (.node (.node (.node
    (.leaf 0xa01201b01a0702201201b100d0300607229002020010400a01201b021030060) (.leaf
    0xf400a0100d030060722900202001040250400a01201b024060230700b040)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac2ec01012806c00c29002020010) (.leaf
    0x3c0181c0140ac06c03c1c038040981d8ac06c03c1c0380402))) (.node (.node (.leaf
    0x10000000001000000000100000000000000000000000a0000000000015a) (.leaf
    0xf0060700502b01b00f0700e010260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100000000000a0010000000000000000000022a) (.leaf
    0x3d002804806c0e81c0681c0b00900b0402b02b01b0100762b01b00f070000))))) (.node (.node (.node
    (.node (.leaf 0x29002020200701f06029030060700202b01b00807007030060700202b02b0040) (.leaf
    0xf20010400a01202b100d0300607229002020010400a01201b02103006072)) (.node (.leaf
    0x10000000000000000000030a0060762b01b00f0700e0100d03006072290020) (.leaf
    0xf3006072290020200c0700000000010000000001000000000100000000000b))) (.node (.node (.leaf
    0x80ac06c04c0c0181c8a4008080300900b0400a01009030060700202b01b0130) (.leaf
    0x3c0681c0e00c0181c0080ac06c04c0c0181c8a4008080741c0240c0181c0)) (.node (.leaf
    0x1d0700903006072290020201c02b01b0040400a01201b01b0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b0130300607a29002020)))) (.node (.node (.node
    (.leaf 0x10000000001000000000100000000000f0010000000000000000000010a) (.leaf
    0xf00b0400a071201b1009030060700202b01b01303006072290020200c070000)) (.node (.leaf
    0x200c0700b0400a01201b1009030060700202b01b01303006072290020200c07) (.leaf
    0x3c80801e8a407c180780900e01009030060700202b01b0130300607229002))) (.node (.node (.leaf
    0x1201b01a070220100d0300607a29002020010400a01201b0210300607a290020) (.leaf
    0x3ec4ac01012806c00c2900202001040250400a01201b024060230700b0400a0)) (.node (.leaf
    0x6070020200c0700b0400a01009030060700202b01b00807007030060700502) (.leaf
    0xf400a01201b0210300607002020200701f06029030060700202b01b01303)))))) (.node (.node (.node
    (.node (.node (.leaf 0xb00f0700e0100d03006070020200104a01b03c0703b0100d0300607002020010)
    (.leaf 0xf0060762b01)) (.node (.leaf
    0x10000000001000000000100000000000500000000000c0000000000020a) (.leaf
    0x3cc0181c0140ac4ec01012806c00c29002020010400a0100d03006070000))) (.node (.node (.leaf
    0x1b00f0700e010260700502b01b00f0700e01009030060700202b01b008070070) (.leaf 0xf0060700502b0))
    (.node (.leaf 0x1000000000100000000010000000000000000000000120000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x1000000000100000000010000000000120010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x210300607a290020202007a2901f06029030060700202b01b00807007030060) (.leaf
    0xf300607a29002020010400a01202b100d0300607a29002020010400a01201b))) (.node (.node (.leaf
    0x10000000000130010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b0130300607a290020200c0700000000010000000001000000000)) (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181e8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a40080800410028048))))) (.node (.node (.node (.node
    (.leaf 0x1000000000100000000010000000000130010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b0130300607a290020200c070000)) (.node (.leaf
    0x801e8a407c180780900e01009030060700202b01b0130300607a290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808))) (.node (.node (.leaf
    0x40a0060762b01b00f0700e0100d0300607a29002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000001700100)) (.node (.leaf
    0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf 0x3c0181c0))))
    (.node (.node (.node (.leaf 0x1000000600100000000010000000000140010000000020000000000005a)
    (.leaf 0x3c0300900b0400a01009030060700202b01b0130300607a290020200c070000)) (.node (.leaf
    0xb01b0130300607a290020201d07009030060700202b01b0130300607a2900202) (.leaf
    0xf2b01b00f0700e0100d0300607a29002020010400a01202b00d030060700202))) (.node (.node (.leaf
    0x1000000000100000000001b0010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b0130300607a290020200c070000000001)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b0130300607a290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b0130300607a290020200c0700))))))) (.node (.node (.node
    (.node (.node (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0xf700202b01b00807007030060700502b20b00404a01b0030a4008080041002)) (.node (.leaf
    0x202b01b01303006070020200c0700b0402a0762b01b00f0700e01009030060) (.leaf
    0xf02d030060700202b01b01303006070020200c0700b0400a010090300607))) (.node (.node (.leaf
    0x1000000000100000000000400000000001d0000000000004a0060700202b01b) (.leaf
    0xf0060762b01b00f0700e0100d0300607000000000100000000)) (.node (.leaf
    0x10000000001000000000100000000001f0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)))) (.node (.node (.node
    (.leaf 0x1000000000100000000001c0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)) (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e))) (.node (.node (.leaf
    0x10000000000230010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000)) (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009))))) (.node (.node (.node
    (.node (.leaf 0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b28b00404a01b0030a4008080041002804806c40340c018)) (.node (.leaf
    0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807) (.leaf
    0xf7002020010400a01201b00d030060700202012030060700202b01b013030))) (.node (.node (.leaf
    0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006)) (.node (.leaf
    0x80000000000200000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)))) (.node (.node (.node
    (.leaf 0x1000000000100000000010000000000270010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)) (.node (.leaf
    0x6001000000600100000000010000000000240010000000000000000010005a) (.leaf
    0x3d2806c00c1900202001040270701a0762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x900b0400a01009030060700202b01b00807007030060700502b01b2b04b0040) (.leaf
    0x3d002804806c0681c08804806c0340c0181c0080ac06c04c0c0181c00808030)) (.node (.leaf
    0x7002020010400a0100d030060700202001040250400a01201b024060230700b0) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d030060)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1000000000100000040010000000000040010000000010000000000012a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0xc008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3c4806c0681c08804806c40340c0181c8a4008080041002804806c0840c0181))) (.node (.node (.leaf
    0x10400a0100d030060722900202001040250400a01201b024060230700b0400a0) (.leaf
    0xf700502b01b00f0700e010260762b01b00f0700e0100d03006072290020200)) (.node (.leaf
    0x1000000000100000000010000000000080010000000000000000000022a0060) (.leaf
    0x3c4806c0e81c0681c0b00900b0402b02b01b0100762b01b00f0700000000)))) (.node (.node (.node
    (.leaf 0x20200701f06029030060700202b01b00807007030060700202b02b0040400a0) (.leaf
    0xf002020010400a01202b100d0300607002020010400a01201b0210300607002)) (.node (.leaf
    0x90010000000000000000000030a0060762b01b00f0700e0100d0300607229) (.leaf
    0xfb01b01303006070020200c0700000000010000000001000000000100000000))) (.node (.node (.leaf
    0x240c0181c0080ac06c04c0c0181c008080300900b0400a01009030060700202) (.leaf
    0x3c02c1002804806c0681c0e00c0181c0080ac06c04c0c0181c8a4008080741c)) (.node (.leaf
    0x6072290020201d0700903006072290020201c02b01b0040400a01201b01b07) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b01303))))) (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000d0010000000000000000000010a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x20200c0700b0400a01201b1009030060700202b01b01303006072290020200c0) (.leaf
    0x3c80801c8a407c180780900e01009030060700202b01b013030060722900))) (.node (.node (.leaf
    0x1201b01a070220100d0300607a29002020010400a01201b0210300607a290020) (.leaf
    0xf400a0100d0300607a2900202001040250400a01201b024060230700b0400a0)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac46c01012806c00c29002020010) (.leaf
    0x3c0181c0140ac06c03c1c038040981c0140ac06c03c1c0380402)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000000000000000100000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010000000000100010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000))) (.node (.node (.leaf
    0x210300607a29002020200722901f06029030060700202b01b00807007030060) (.leaf
    0xf300607a29002020010400a01202b100d0300607a29002020010400a01201b)) (.node (.leaf
    0x10000000000110010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b01303006072290020200c0700000000010000000001000000000))))))))))) (.node (.node
    (.node (.node (.node (.node (.node (.node (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181e8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a40080800410028048)) (.node (.leaf
    0x1000000000100000000010000000000110010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b0130300607a290020200c070000))) (.node (.node (.leaf
    0x801e8a407c180780900e01009030060700202b01b0130300607a290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808)) (.node (.leaf
    0x40a0060762b01b00f0700e0100d0300607a29002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000001500100)))) (.node (.node (.node
    (.leaf 0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf
    0x3c0181c0)) (.node (.leaf 0x1000000600100000000010000000000120010000000020000000000005a)
    (.leaf 0x3c0300900b0400a01009030060700202b01b0130300607a290020200c070000))) (.node (.node
    (.leaf 0xb01b0130300607a290020201d07009030060700202b01b0130300607a2900202) (.leaf
    0xf2b01b00f0700e0100d0300607a29002020010400a01202b00d030060700202)) (.node (.leaf
    0x100000000010000000000190010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b0130300607a290020200c070000000001))))) (.node (.node (.node
    (.node (.leaf 0xb0400a01201b1009030060700202b01b0130300607a290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b0130300607a290020200c0700)) (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a4008080041002))) (.node (.node (.leaf
    0x10000000001000000000100000000001d0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x1000000000100000000001a0010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)))) (.node (.node (.node
    (.leaf 0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e)) (.node (.leaf
    0x10000000000210010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000))) (.node (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)) (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0xf007030060700502b26b00404a01b0030a4008080041002804806c40340c018)))))) (.node (.node (.node
    (.node (.node (.leaf 0x6070020200c0700b0402a0762b01b00f0700e01009030060700202b01b00807)
    (.leaf 0xf7002020010400a01201b00d030060700202012030060700202b01b013030)) (.node (.leaf
    0x70020201203006070020201102b01b0100700502b01b00f0700e0100d030060) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a071201b00d03006))) (.node (.node (.leaf
    0x800000000001e0000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x1000000000100000000010000000000250010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)))) (.node (.node (.node (.leaf
    0x6001000000600100000000010000000000220010000000000000000010005a) (.leaf
    0x3dc0140ac06cac16c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0x3c0840c0181c008080801c07c180780900e01009030060700202b01b0130))) (.node (.node (.leaf
    0x60230700b0400a01201b01a0702201201b100d0300607002020010400a01201b) (.leaf
    0xf300607229002020010400a0100d030060700202001040250400a01201b0240)) (.node (.leaf
    0x22a0060700502b01b00f0700e010260762b01b00f0700e0100d0) (.leaf
    0xfb01b00f0700000000010000000001000000000100000000000600100000000))))) (.node (.node (.node
    (.node (.leaf 0x181c0080ac0ac0101002804806c0e81c0681c0b00900b0402b02b01b0100762) (.leaf
    0x3c4806c0840c0181c008080801c07c180a40c0181c0080ac06c0201c01c0c)) (.node (.leaf
    0xf0700e0100d0300607002020010400a01202b100d0300607002020010400a0) (.leaf 0xf0060762b01b)))
    (.node (.node (.leaf 0x1000000000100000000010000000000070010000000010000000000030a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x700202b01b01303006070020201d07009030060700202b01b01303006070020) (.leaf
    0xf70020201c02b01b0040400a01201b01b0700b0400a01201b01a0703803006)))) (.node (.node (.node
    (.leaf 0x1b00f0700e0100d030060700202b01b01303006072290020201d07009030060) (.leaf
    0xf0060700502b)) (.node (.leaf
    0x10000000001000000000100000000000b0010000000000000000000010a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3dc8a4008080801c8a407c180780900e01009030060700202b01b013030060)) (.node (.leaf
    0xb0400a01201b01a070220100d0300607a29002020010400a01201b021030060) (.leaf
    0xf20010400a0100d0300607a2900202001040250400a01201b02406023070))))))) (.node (.node (.node
    (.node (.node (.node (.leaf
    0x8040240c0181c0080ac06c0201c01c0c0181c0140ac3ec01012806c00c290020) (.leaf
    0x3c0181c0140ac06c03c1c038040981c0140ac06c03c1c03)) (.node (.leaf
    0x10000000001000000000100000000000000000000000e0000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x10000000001000000000100000000000e0010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x210300607229002020200722901f06029030060700202b01b00807007030060) (.leaf
    0xf300607a29002020010400a01202b100d0300607a29002020010400a01201b)))) (.node (.node (.node
    (.leaf 0x100000000000f0010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0xf700202b01b01303006072290020200c0700000000010000000001000000000)) (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181c8a4008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a40080800410028048))) (.node (.node (.leaf
    0x10000000001000000000100000000000f0010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006072290020200c070000)) (.node (.leaf
    0x801e8a407c180780900e01009030060700202b01b0130300607a290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808))))) (.node (.node (.node
    (.node (.leaf 0x40a0060762b01b00f0700e0100d0300607a29002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000001300100)) (.node (.leaf
    0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf 0x3c0181c0)))
    (.node (.node (.leaf 0x1000000600100000000010000000000100010000000020000000000005a) (.leaf
    0x3c0300900b0400a01009030060700202b01b0130300607a290020200c070000)) (.node (.leaf
    0xb01b0130300607a290020201d07009030060700202b01b0130300607a2900202) (.leaf
    0xf2b01b00f0700e0100d0300607a29002020010400a01202b00d030060700202)))) (.node (.node (.node
    (.leaf 0x100000000010000000000170010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b0130300607a290020200c070000000001)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b0130300607a290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b0130300607a290020200c0700))) (.node (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a4008080041002)) (.node (.leaf
    0x10000000001000000000100000000001b0010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x100000000010000000000180010000000010000000000005a0060700502b01b)
    (.leaf 0xf1009030060700202b01b0130300607a290020200c07000000000100000060)) (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e))) (.node (.node (.leaf
    0x100000000001f0010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000)) (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)))) (.node (.node (.node
    (.leaf 0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0x3dd8ac06c03c1c038040340c0181e8a4008080041002804806c40340c018)) (.node (.leaf
    0x1000000000100000000010000000000230010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000))) (.node (.node (.leaf
    0x6001000000600100000000010000000000200010000000000000000010005a) (.leaf
    0x3cac06cac1ac01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0x2b01b0100762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3dc01c0c0181c0080ac0ac0101002804806c0e81c0681c0b00900b0402b0))))) (.node (.node (.node
    (.node (.leaf 0x20010400a01201b0210300607002020200701f06029030060700202b01b0080) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01202b100d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000050010000000030000000000030a0060) (.leaf
    0x3c900b0400a01009030060700202b01b01303006070020200c0700000000))) (.node (.node (.leaf
    0x2b01b01303006070020201d07009030060700202b01b01303006070020200c0) (.leaf
    0xf201c02b01b0040400a01201b01b0700b0400a01201b01a070380300607002)) (.node (.leaf
    0xb00f0700e0100d030060700202b01b01303006070020201d0700903006070020) (.leaf
    0xf0060700502b01)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000090010000000010000000000010a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060))) (.node (.node (.leaf
    0x230700b0400a01201b01a070220100d0300607229002020010400a01201b0210) (.leaf
    0x3e9002020010400a0100d0300607a2900202001040250400a01201b024060)) (.node (.leaf
    0xf0700e01009030060700202b01b00807007030060700502b0db00404a01b0030) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00)))))))) (.node (.node (.node (.node (.node
    (.node (.node (.leaf 0x10000000001000000000100000000000000000000000c0000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100000000000c0010000000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000))) (.node (.node (.leaf
    0x1201b0210300607002020200701f06029030060700202b01b00807007030060) (.leaf
    0xf100d0300607a29002020010400a01202b100d0300607229002020010400a)) (.node (.leaf
    0x100000000000d0010000000000000000000030a0060762b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006070020200c07000000000100000000010000)))) (.node (.node (.node
    (.leaf 0x100280480ec0340c0181c0080ac06c04c0c0181c008080300900b0400a010090) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c8a400808004)) (.node (.leaf
    0x10000000001000000000100000000000d0010000000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x801e8a407c180780900e01009030060700202b01b01303006072290020200c0) (.leaf
    0x3d00280480ec40340c0181e8a4008080041002804806c0840c0181e8a400808)) (.node (.leaf
    0x40a0060762b01b00f0700e0100d0300607a29002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100000000001100100))))) (.node (.node (.node
    (.node (.leaf 0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf
    0x3c0181c0)) (.node (.leaf 0x10000006001000000000100000000000e0010000000020000000000005a)
    (.leaf 0x3c0300900b0400a01009030060700202b01b0130300607a290020200c070000))) (.node (.node
    (.leaf 0xb01b0130300607a290020201d07009030060700202b01b0130300607a2900202) (.leaf
    0xf2b01b00f0700e0100d0300607a29002020010400a01202b00d030060700202)) (.node (.leaf
    0x100000000010000000000150010000000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b0130300607a290020200c070000000001)))) (.node (.node (.node
    (.leaf 0xb0400a01201b1009030060700202b01b0130300607a290020200c0700b0400a0) (.leaf
    0xfa407c180780900e01009030060700202b01b0130300607a290020200c0700)) (.node (.leaf
    0x80480ac40340c0181e8a4008080041002804806c0840c0181e8a4008080801e8) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a4008080041002))) (.node (.node (.leaf
    0x1000000000100000000010000000000190010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x100000000010000000000160010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)))))) (.node (.node (.node
    (.node (.node (.leaf 0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0)
    (.leaf 0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e)) (.node (.leaf
    0x100000000001d0010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000))) (.node (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009)) (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0x3dd8ac06c03c1c038040340c0181e8a4008080041002804806c40340c018)))) (.node (.node (.node
    (.leaf 0x1000000000100000000010000000000210010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)) (.node (.leaf
    0x60010000006001000000000100000000001e0010000000000000000010005a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x400a01009030060700202b01b00807007030060700502b01b2b07b00404a01b) (.leaf
    0x3cc0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b)) (.node (.leaf
    0x1b0040400a01201b01b0700b0400a01201b01a07038030060700202b01b0130) (.leaf
    0xf100d030060700202b01b01303006070020201d0700903006070020201c02b))))) (.node (.node (.node
    (.node (.leaf 0x10000000000070010000000030000000000010a0060700502b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006070020200c07000000000100000000010000000)) (.node (.leaf
    0x201b1009030060700202b01b01303006070020200c0700b0400a071201b10090) (.leaf
    0x3d80780900e01009030060700202b01b01303006070020200c0700b0400a01))) (.node (.node (.leaf
    0xb01a070220100d0300607002020010400a01201b0210300607002020200701f0) (.leaf
    0xf00a0100d030060700202001040250400a01201b024060230700b0400a01201)) (.node (.leaf
    0x502b01b00f0700e010260700502b01b00f0700e0100d0300607a290020200104) (.leaf 0xf0060700))))
    (.node (.node (.node (.leaf 0x10000000001000000000100000000000a0010000000000000000000012a)
    (.leaf 0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x1201b0210300607002020200701f06029030060700202b01b00807007030060) (.leaf
    0xf700e0100d0300607002020010400a01202b100d0300607002020010400a))) (.node (.node (.leaf
    0x1000000000100000000000b0010000000000000000000030a0060762b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000)) (.node (.leaf
    0x8004100280480ec0340c0181c0080ac06c04c0c0181c008080300900b0400a0) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c008))))))) (.node (.node (.node (.node (.node (.node
    (.leaf 0x10000000001000000000100000000000b0010000000010000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x4008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3c8004100280480ec40340c0181e8a4008080041002804806c0840c0181e8a))) (.node (.node (.leaf
    0x10000000000000000000040a0060762b01b00f0700e0100d0300607a290020) (.leaf
    0xfb01b0100762b01b00f0700000000010000000001000000000100000000000f)) (.node (.leaf
    0x3c0181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02) (.leaf 0x0)))) (.node
    (.node (.node (.leaf 0x10000000001000000000100000000000c0010000000030000000000005a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0x2b01b0130300607a290020201d07009030060700202b01b0130300607a290020) (.leaf
    0xf62b01b00f0700e0100d0300607a29002020010400a01202b00d03006070020))) (.node (.node (.leaf
    0x1000000000100000000010000000000130010000000000000000000020a00607) (.leaf
    0xf00a071201b1009030060700202b01b0130300607a290020200c07000000000)) (.node (.leaf
    0x700b0400a01201b1009030060700202b01b0130300607a290020200c0700b04) (.leaf
    0x3de8a407c180780900e01009030060700202b01b0130300607a290020200c))))) (.node (.node (.node
    (.node (.leaf 0xa01202b100d0300607a29002020010400a01201b0210300607a29002020200) (.leaf
    0xf0060762b01b00f0700e0100d0300607a290020200104)) (.node (.leaf
    0x1000000000100000000010000000000170010000000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x100000000010000000000140010000000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b0130300607a290020200c07000000000100000060)) (.node (.leaf
    0x8a4008080741c0240c0181c0080ac06c04c0c0181e8a4008080300900b0400a0) (.leaf
    0x3c0340c0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181e)))) (.node (.node (.node
    (.leaf 0x100000000001b0010000000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b0130300607a290020200c070000000001000000000100000000)) (.node (.leaf
    0x30060700202b01b0130300607a290020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b0130300607a290020200c0700b0400a01201b1009))) (.node (.node (.leaf
    0x1e8a4008080041002804806c0840c0181e8a4008080801e8a407c180780900e0) (.leaf
    0x3dd8ac06c03c1c038040340c0181e8a4008080041002804806c40340c018)) (.node (.leaf
    0x10000000001000000000100000000001f0010000000000000000000020a0060) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f0700000000)))))) (.node (.node (.node (.node
    (.node (.leaf 0x60010000006001000000000100000000001c0010000000000000000010005a) (.leaf
    0x3dc0140ac06cac22c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303))) (.node (.node (.leaf
    0x2804806c0840c0181c008080801c07c180780900e01009030060700202b01b) (.leaf
    0x3c4806c0901808c1c02c1002804806c0681c088040340c0181c008080041)) (.node (.leaf
    0xf0700e0100d0300607002020010400a0100d030060700202001040250400a0) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000080010000000010000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x1201b0210300607002020200701f06029030060700202b01b00807007030060) (.leaf
    0xf700e0100d0300607002020010400a01202b100d0300607002020010400a))) (.node (.node (.leaf
    0x100000000010000000000090010000000020000000000030a0060762b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000)) (.node (.leaf
    0x8004100280480ec0340c0181c0080ac06c04c0c0181c008080300900b0400a0) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c008))))) (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000090010000000030000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000)) (.node (.leaf
    0xc008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3e8a400808004100280480ec40340c0181c008080041002804806c0840c0181))) (.node (.node (.leaf
    0xd0010000000000000000000040a0060762b01b00f0700e0100d0300607) (.leaf
    0xf402b02b01b0100762b01b00f0700000000010000000001000000000100000)) (.node (.leaf
    0x1680181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0) (.leaf
    0x3dc000000000400000000040000000004000000000028004000000014000000)))) (.node (.node (.node
    (.leaf 0xc0181c008080300900b0400a01009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080741c0240c0181c0080ac06c04c0)) (.node (.leaf
    0x20a0060762b01b00f0700e0100d0300607a29002020010400a01202b00d0) (.leaf
    0xf70000000001000000000100000000010000000000110010000000000000000))) (.node (.node (.leaf
    0x20200c0700b0400a071201b1009030060700202b01b01303006070020200c0) (.leaf
    0xf00607a290020200c0700b0400a01201b1009030060700202b01b0130300607)) (.node (.leaf
    0x840c0181e8a4008080801e8a407c180780900e01009030060700202b01b01303) (.leaf
    0x3c0181e8a400808004100280480ac40340c0181e8a4008080041002804806c0))))))))) (.node (.node
    (.node (.node (.node (.node (.node (.node (.leaf
    0x150010000000000000000000030a0060762b01b00f0700e0100d03) (.leaf
    0x3c900b0402b02b01b0100762b01b00f07000000000100000000010000000001)) (.node (.leaf
    0x20010000000010000000000005a0060700502b01b00f0700e01201b0260702c0) (.leaf
    0xf300607a290020200c0700000000010000006001000000000100000000001))) (.node (.node (.leaf
    0x80ac06c04c0c0181e8a4008080300900b0400a01009030060700202b01b0130) (.leaf
    0x3c4806c0340c0181c0080ac06c04c0c0181e8a4008080741c0240c0181c0)) (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607a29002020010400a0) (.leaf
    0xf200c070000000001000000000100000000010000000000190010000000000)))) (.node (.node (.node
    (.leaf 0x290020200c0700b0400a071201b1009030060700202b01b0130300607a290020) (.leaf
    0xf7a290020200c0700b0400a01201b1009030060700202b01b0130300607a)) (.node (.leaf
    0x181e8a4008080801e8a407c180780900e01009030060700202b01b013030060) (.leaf
    0x3de8a4008080041002804806c40340c0181e8a4008080041002804806c0840c))) (.node (.node (.leaf
    0x1d0010000000000000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf700e01201b0260762b01b00f070000000001000000000100000000010000)) (.node (.leaf
    0x100000000001a0010000000000000000010005a0060700502b01b00f0) (.leaf
    0x3c00c19002020010400a071201b100d03006070000006001000000600100))))) (.node (.node (.node
    (.node (.leaf 0x1201b1009030060700202b01b00807007030060700502b01b2b09b00404a01b) (.leaf
    0xf2b01b00f0700e01009030060700202b01b01303006070020200c0700b0400a)) (.node (.leaf
    0xac06c0201c01c0c0181c0080ac06c0101002804806c0a00900b040270701a076) (.leaf
    0x3dc008080041002804806c0840c0181c008080801c07c180a40c0181c0080))) (.node (.node (.leaf
    0xf0060762b01b00f0700e0100d0300607002020010400a01202b100d030060) (.leaf 0x0)) (.node (.leaf
    0x1000000000100000000010000000000070010000000040000000000030a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000)))) (.node (.node (.node
    (.leaf 0x100d0300607002020010400a01203b00d030060700202b01b01303006070020) (.leaf
    0xf0060762b01b00f0700e)) (.node (.leaf
    0x1000000000100000000010000000000070010000000050000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0xc008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3dc00808004100280480ec40340c0181c008080041002804806c0840c0181)) (.node (.leaf
    0xb0010000000010000000000040a0060762b01b00f0700e0100d030060) (.leaf
    0xf402b02b01b0100762b01b00f070000000001000000000100000000010000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1680181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0) (.leaf
    0x3dc00000000040000000004000000000400000000002000400000001c000000)) (.node (.leaf
    0xc0181c008080300900b0400a01009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080741c0240c0181c0080ac06c04c0))) (.node (.node (.leaf
    0x20a0060762b01b00f0700e0100d0300607002020010400a01202b00d0) (.leaf
    0xf700000000010000000001000000000100000000000f0010000000010000)) (.node (.leaf
    0x20200c0700b0400a071201b1009030060700202b01b01303006070020200c0) (.leaf
    0xf3006070020200c0700b0400a01201b1009030060700202b01b0130300607)))) (.node (.node (.node
    (.leaf 0x6c0840c0181e8a4008080801c07c180780900e01009030060700202b01b0130) (.leaf
    0x3cc0181e8a400808004100280480ac40340c0181e8a40080800410028048)) (.node (.leaf
    0x10000000000130010000000000000000000030a0060762b01b00f0700e0100d0) (.leaf
    0x3c900b0402b02b01b0100762b01b00f0700000000010000000001000000000))) (.node (.node (.leaf
    0x10000000020000000000005a0060700502b01b00f0700e01201b0260702c0) (.leaf
    0xf01303006070020200c0700000000010000006001000000000100000000001)) (.node (.leaf
    0x81c0080ac06c04c0c0181e8a4008080300900b0400a01009030060700202b01b) (.leaf
    0x3d002804806c0340c0181c0080ac06c04c0c0181e8a4008080741c0240c01))))) (.node (.node (.node
    (.node (.leaf 0x10a0060700502b01b00f0700e0100d0300607a29002020010) (.leaf
    0x3e90020200c0700000000010000000001000000000100000000001700100000)) (.node (.leaf
    0x181e8a4008080301c02c100281c4806c40240c0181c0080ac06c04c0c0181e8) (.leaf
    0x3cc0181e8a4008080301c02c1002804806c40240c0181c0080ac06c04c0c))) (.node (.node (.leaf
    0x840c0181e8a4008080801e8a407c180780900e01009030060700202b01b0130) (.leaf
    0x3cc0181e8a4008080041002804806c40340c0181e8a4008080041002804806c)) (.node (.leaf
    0x100000000001b0010000000000000000000020a0060762b01b00f0700e0100d0) (.leaf
    0xf00f0700e01201b0260762b01b00f0700000000010000000001000000000)))) (.node (.node (.node
    (.leaf 0x100000000010000000000180010000000000000000010005a0060700502b01b) (.leaf
    0x3d2806c00c19002020010400a01201b100d0300607000000600100000060)) (.node (.leaf
    0x1b00f0700e01009030060700202b01b00807007030060700502b01b2b0ab0040) (.leaf
    0xf1009030060700202b01b01303006070020200c0700b040270701a0762b0))) (.node (.node (.leaf
    0x8004100280480ec0340c0181c0080ac06c04c0c0181c008080300900b0400a0) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c008)) (.node (.leaf
    0x1000000000100000000010000000000050010000000070000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006070020200c070000))))))) (.node (.node (.node
    (.node (.node (.node (.leaf
    0xc008080801c07c180780900e01009030060700202b01b01303006070020200c0) (.leaf
    0x3dc00808004100280480ec40340c0181c008080041002804806c0840c0181)) (.node (.leaf
    0x90010000000030000000000040a0060762b01b00f0700e0100d030060) (.leaf
    0xf402b02b01b0100762b01b00f070000000001000000000100000000010000))) (.node (.node (.leaf
    0x1680181c0140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0) (.leaf
    0x3dc000000000400000000040000000004000000000018004000000024000000)) (.node (.leaf
    0xc0181c008080300900b0400a01009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080741c0240c0181c0080ac06c04c0)))) (.node (.node (.node
    (.leaf 0x20a0060762b01b00f0700e0100d0300607002020010400a01202b00d0) (.leaf
    0xf700000000010000000001000000000100000000000d0010000000030000)) (.node (.leaf
    0x20200c0700b0400a071201b1009030060700202b01b01303006070020200c0) (.leaf
    0xf3006070020200c0700b0400a01201b1009030060700202b01b0130300607))) (.node (.node (.leaf
    0x4806c0840c0181c008080801c07c180780900e01009030060700202b01b0130) (.leaf
    0x3c038040340c0181e8a400808004100280480ac40340c0181c0080800410028)) (.node (.leaf
    0x10000000000110010000000000000000000030a0060762b01b00f07) (.leaf
    0x3c0981c0b00900b0402b02b01b0100762b01b00f0700000000010000000001))))) (.node (.node (.node
    (.node (.leaf 0xe0010000000040000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf700202b01b01303006070020200c0700000000010000000001000000000100)) (.node (.leaf
    0x80741c0240c0181c0080ac06c04c0c0181c008080300900b0400a01009030060) (.leaf
    0x3cc0181e8a4008080041002804806c0340c0181c0080ac06c04c0c0181c0080))) (.node (.node (.leaf
    0x150010000000000000000000010a0060700502b01b00f0700e0100d0) (.leaf
    0xf700202b01b01303006070020200c0700000000010000000001000000000100)) (.node (.leaf
    0x9030060700202b01b01303006070020200c0700b0400a071201b1009030060) (.leaf
    0xf00e01009030060700202b01b0130300607a290020200c0700b0400a01201b1)))) (.node (.node (.node
    (.leaf 0xc0181e8a4008080041002804806c0840c0181e8a4008080801e8a407c1807809) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181e8a4008080041002804806c40340)) (.node (.leaf
    0x1000000000100000000010000000000190010000000000000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000))) (.node (.node (.leaf
    0x6001000000600100000000010000000000160010000000000000000010005a) (.leaf
    0x3d2806c00c1900202001040270701a0762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x700b0400a01009030060700202b01b00807007030060700502b01b2b0bb0040) (.leaf
    0xf0020200c0700b0400a01201b1009030060700202b01b01303006070020200c)))))) (.node (.node (.node
    (.node (.node (.leaf 0x840c0181c008080801c07c180780900e01009030060700202b01b0130300607)
    (.leaf 0x3c40340c0181c00808004100280480ec40340c0181c008080041002804806c)) (.node (.leaf
    0x10000000000070010000000050000000000040a0060762b01b00f0700e0) (.leaf
    0x3dc0b00900b0402b02b01b0100762b01b00f07000000000100000000010000))) (.node (.node (.leaf
    0xb0000000000005a0060700502b01b00f0700e01201b0260700202b01b0100) (.leaf
    0xf70020200c0700000000010000000001000000000100000000000400100000)) (.node (.leaf
    0xac06c04c0c0181c008080300900b0400a01009030060700202b01b013030060) (.leaf
    0x3c0280480ac0340c0181c0080ac06c04c0c0181c008080741c0240c0181c008)))) (.node (.node (.node
    (.leaf 0x50000000000020a0060762b01b00f0700e0100d03006070020200104) (.leaf
    0xf3006070020200c0700000000010000000001000000000100000000000b001)) (.node (.leaf
    0x2b01b01303006070020200c0700b0400a071201b1009030060700202b01b0130) (.leaf
    0xf700202b01b01303006070020200c0700b0400a01201b100903006070020))) (.node (.node (.leaf
    0xc008080041002804806c0840c0181c008080801c07c180780900e01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181c00808004100280480ac40340c0181)) (.node (.leaf
    0x10000000001000000000100000000000f0010000000010000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000))))) (.node (.node (.node
    (.node (.leaf 0x1000000000100000000000c0010000000060000000000005a0060700502b01b) (.leaf
    0xf00a01009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0x4c0c0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b04) (.leaf
    0x3c03c1c038040340c0181c008080041002804806c0340c0181c0080ac06c))) (.node (.node (.leaf
    0x100000000010000000000130010000000010000000000010a0060700502b01b) (.leaf
    0xf201b1009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006070020200c0700b0400a071) (.leaf
    0x3c80801c07c180780900e01009030060700202b01b01303006070020200c070)))) (.node (.node (.node
    (.leaf 0x10400a01201b100d0300607a29002020010400a01201b0210300607a290020) (.leaf
    0xf0060762b01b00f0700e0100d0300607a2900202)) (.node (.leaf
    0x1000000000100000000010000000000170010000000000000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000))) (.node (.node (.leaf
    0x6001000000600100000000010000000000140010000000010000000010005a) (.leaf
    0x3dc0140ac06cac32c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0x3c900b0402b02b01b0100762b01b00f0700e01009030060700202b01b0130)))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf 0x5a0060700502b01b00f0700e01201b0260700202b01b0100702c0)
    (.leaf 0xf200c0700000000010000000001000000000100000000000200100000000d0)) (.node (.leaf
    0xc04c0c0181c008080300900b0400a01009030060700202b01b01303006070020) (.leaf
    0x3c80ac0340c0181c0080ac06c04c0c0181c008080741c0240c0181c0080ac06))) (.node (.node (.leaf
    0x70000000000020a0060762b01b00f0700e0100d0300607002020010400a01) (.leaf
    0xf70020200c0700000000010000000001000000000100000000000900100000)) (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b013030060) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)))) (.node (.node (.node
    (.leaf 0x80041002804806c0840c0181c008080801c07c180780900e0100903006070020) (.leaf
    0x3dd8ac06c03c1c038040340c0181c00808004100280480ac40340c0181c0080)) (.node (.leaf
    0x10000000001000000000100000000000d0010000000030000000000030a0060) (.leaf
    0x3dc03804806c0981c0b00900b0402b02b01b0100762b01b00f0700000000))) (.node (.node (.leaf
    0x100000000000a0010000000080000000000005a0060700502b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000100)) (.node (.leaf
    0xc0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b0400a0) (.leaf
    0x3dc038040340c0181c008080041002804806c0340c0181c0080ac06c04c0))))) (.node (.node (.node
    (.node (.leaf 0x10000000000110010000000030000000000010a0060700502b01b00f0) (.leaf
    0xf1009030060700202b01b01303006070020200c070000000001000000000100)) (.node (.leaf
    0xa01201b1009030060700202b01b01303006070020200c0700b0400a071201b) (.leaf
    0x3dc07c180780900e01009030060700202b01b01303006070020200c0700b04))) (.node (.node (.leaf
    0x20010400a01201b100d0300607002020010400a01201b0210300607002020200) (.leaf
    0xf0060762b01b00f0700e0100d0300607a290020)) (.node (.leaf
    0x1000000000100000000010000000000150010000000000000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)))) (.node (.node (.node (.leaf
    0x6001000000600100000000010000000000120010000000030000000010005a) (.leaf
    0x3cac06cac36c01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0x2b01b0100762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0x3c900b0400a01009030060700202b01b01303006070020200c0700b0402b0))) (.node (.node (.leaf
    0x2b01b01303006070020201d07009030060700202b01b01303006070020200c0) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01202b00d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000070010000000090000000000020a0060) (.leaf
    0xf400a071201b1009030060700202b01b01303006070020200c0700000000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x200c0700b0400a01201b1009030060700202b01b01303006070020200c0700b0)
    (.leaf 0x3dc008080801c07c180780900e01009030060700202b01b01303006070020)) (.node (.leaf
    0x300607002020010400a01202b100d0300607002020010400a01201b021030060) (.leaf
    0xf0060762b01b00f0700e0100d0))) (.node (.node (.leaf
    0x10000000001000000000100000000000b0010000000050000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x1000000000100000000000800100000000a0000000000005a0060700502b01b) (.leaf
    0xf00a01009030060700202b01b01303006070020200c07000000000100000000)))) (.node (.node (.node
    (.leaf 0x4c0c0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b04) (.leaf
    0x3c03c1c038040340c0181c008080041002804806c0340c0181c0080ac06c)) (.node (.leaf
    0x1000000000100000000000f0010000000050000000000010a0060700502b01b) (.leaf
    0xf201b1009030060700202b01b01303006070020200c07000000000100000000))) (.node (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006070020200c0700b0400a071) (.leaf
    0x3c80801c07c180780900e01009030060700202b01b01303006070020200c070)) (.node (.leaf
    0x7002020010400a01201b100d0300607002020010400a01201b02103006070020) (.leaf
    0xf0060762b01b00f0700e0100d030060))))) (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000130010000000010000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)) (.node (.leaf
    0x6001000000600100000000010000000000100010000000050000000010005a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x400a01009030060700202b01b00807007030060700502b01b2b0eb00404a01b) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c0700b)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060)))) (.node (.node (.node
    (.leaf 0x100d0300607002020010400a01202b100d0300607002020010400a01201b0210) (.leaf
    0xf0060762b01b00f0700e0)) (.node (.leaf
    0x1000000000100000000010000000000090010000000070000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x1000000000100000000000600100000000c0000000000005a0060700502b01b) (.leaf
    0xf00a01009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0x4c0c0181c008080741c0240c0181c0080ac06c04c0c0181c008080300900b04) (.leaf
    0x3c03c1c038040340c0181c008080041002804806c0340c0181c0080ac06c))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf
    0x1000000000100000000000d0010000000070000000000010a0060700502b01b) (.leaf
    0xf201b1009030060700202b01b01303006070020200c07000000000100000000)) (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006070020200c0700b0400a071) (.leaf
    0x3c80801c07c180780900e01009030060700202b01b01303006070020200c070))) (.node (.node (.leaf
    0x7002020010400a01201b100d0300607002020010400a01201b02103006070020) (.leaf
    0xf0060762b01b00f0700e0100d030060)) (.node (.leaf
    0x1000000000100000000010000000000110010000000030000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)))) (.node (.node (.node (.leaf
    0x60010000006001000000000100000000000e0010000000070000000010005a) (.leaf
    0x3dc0140ac06cac3ec01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303))) (.node (.node (.leaf
    0x981c0b00900b0402b02b01b0100762b01b00f0700e01009030060700202b01b) (.leaf
    0x3c0181c0140ac06c03c1c03804806c)) (.node (.leaf
    0x10000000001000000000100000000000400100000000e0000000000005a) (.leaf
    0x3c80300900b0400a01009030060700202b01b01303006070020200c070000))))) (.node (.node (.node
    (.node (.leaf 0x700202b01b01303006070020201d07009030060700202b01b01303006070020) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b00d03006)) (.node (.leaf
    0x10000000001000000000100000000000b0010000000090000000000010a) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c070000))) (.node (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060)) (.node (.leaf
    0x100d0300607002020010400a01201b100d0300607002020010400a01201b0210) (.leaf
    0xf0060762b01b00f0700e0)))) (.node (.node (.node (.leaf
    0x10000000001000000000100000000000f0010000000050000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)) (.node (.leaf
    0x60010000006001000000000100000000000c0010000000090000000010005a) (.leaf
    0x3cac06cac42c01012806c00c19002020010400a071201b100d03006070000))) (.node (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf402b02b01b0100762b01b00f0700e01009030060700202b01b013030060)) (.node (.leaf
    0xc008080300900b0400a01009030060700202b01b01303006070020200c0700b0) (.leaf
    0x3dc0080ac06c04c0c0181c008080741c0240c0181c0080ac06c04c0c0181)))))) (.node (.node (.node
    (.node (.node (.leaf 0xf0060700502b01b00f0700e0100d0300607002020010400a01201b00d030060)
    (.leaf 0x0)) (.node (.leaf 0x10000000001000000000100000000000900100000000b0000000000010a)
    (.leaf 0xf700b0400a071201b1009030060700202b01b01303006070020200c070000))) (.node (.node
    (.leaf 0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0x3cc0181c008080801c07c180780900e01009030060700202b01b013030060)) (.node (.leaf
    0x100d0300607002020010400a01201b100d0300607002020010400a01201b0210) (.leaf
    0xf0060762b01b00f0700e0)))) (.node (.node (.node (.leaf
    0x10000000001000000000100000000000d0010000000070000000000020a) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f070000)) (.node (.leaf
    0x60010000006001000000000100000000000a00100000000b0000000010005a) (.leaf
    0x3cac06cac46c01012806c00c19002020010400a01201b100d03006070000))) (.node (.node (.leaf
    0x2b01b0100762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0xf700b0400a01009030060700202b01b01303006070020200c0700b0402b0)) (.node (.leaf
    0x20200c0700b0400a071201b1009030060700202b01b01303006070020200c0) (.leaf
    0xf3006070020200c0700b0400a01201b1009030060700202b01b0130300607))))) (.node (.node (.node
    (.node (.leaf 0x4806c0840c0181c008080801c07c180780900e01009030060700202b01b0130) (.leaf
    0x3dc038040340c0181c008080041002804806c40340c0181c0080800410028)) (.node (.leaf
    0x1000000000100000000000b0010000000090000000000020a0060762b01b00f0) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f070000000001000000000))) (.node (.node (.leaf
    0x10000006001000000000100000000000800100000000d0000000010005a0060) (.leaf
    0x3d9002020010402b02b01b0100762b01b00f0700e0100d030060700000060)) (.node (.leaf
    0xa01009030060700202b01b00807007030060700502b01b2b12b00404a01b0030) (.leaf
    0xf00b0400a071201b1009030060700202b01b01303006070020200c0700b0400)))) (.node (.node (.node
    (.leaf 0x20200c0700b0400a01201b1009030060700202b01b01303006070020200c07) (.leaf
    0xf700e01201b0260762b01b00f0700e01009030060700202b01b0130300607)) (.node (.leaf
    0x100000000000600100000000f0000000010005a0060700502b01b00f0) (.leaf
    0x3c01012806c00c19002020010400a0100d03006070000006001000000600100))) (.node (.node (.leaf
    0xb0400a071201b1009030060700202b01b00807007030060700502b01b2b13b) (.leaf
    0xf200c0700b0400a01201b1009030060700202b01b01303006070020200c07)) (.node (.leaf
    0x700e01201b0260762b01b00f0700e01009030060700202b01b01303006070020) (.leaf
    0xf0060700502b01b00f0))))))) (.node (.node (.node (.node (.node (.node (.leaf
    0x6001000000600100000000010000000000040010000000110000000010015a) (.leaf
    0x3cac06cac52c01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf700e01201b0260762b01b00f0700e01009030060700202b01b013030060))) (.node (.node (.leaf
    0x10000000000020010000000130000000010025a0060700502b01b00f0) (.leaf
    0x3e806c00c19002020010400a01201b100d03006070000006001000000600100)) (.node (.leaf
    0xb00f0700e01009030060700202b01b00807007030060700502b01b2b15b00404) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01)))) (.node (.node (.node (.leaf
    0x6001000000600100000000010000000000000010000000150000000010035a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010010000000150000010000000000000010042a0060) (.leaf 0x60))) (.node
    (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))) (.node (.node (.node
    (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0)
    (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0) (.leaf 0x0))
    (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0)))))) (.node (.node (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf
    0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))
    (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))) (.node (.node (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf
    0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node
    (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf
    0x0)))))))))))

def fuelMode4 : ℕ := 1122
noncomputable def streamMode4 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.leaf
    0x181d86400808054080301c02c1002804806c0240c0f40900b0401802b01b0170) (.leaf
    0x3c0181c0080ac06c0401c0f80c0)) (.node (.leaf
    0x4001000000000100000040010010000000010000010000000000000000011a) (.leaf
    0x3c0640900b0400a01009030060700202b01b01303006076190020200c070000))) (.node (.node (.leaf
    0x903006076190020201c02b01b0040400a01201b01b0700b0400a01201b01a07) (.leaf
    0xf00502b01b00f0700e0100d030060700202b01b01303006076190020201d070)) (.node (.leaf
    0x1000000000100000040010010000000050000010000000000000000010a00607) (.leaf
    0x3c0780900e01009030060700202b01b01303006076190020200c07000000000)))) (.node (.node (.node
    (.leaf 0x100d0300607619002020010400a01201b0210300607619002020200761901f06) (.leaf
    0xf761900202001040250400a01201b024060230700b0400a01201b01a070220)) (.node (.leaf
    0x1c01c0c0181c0140ac06cac22c01012806c00c19002020010400a0100d030060) (.leaf
    0x3cac06c03c1c038040981c0140ac06c03c1c038040240c0181c0080ac06c020))) (.node (.node (.leaf
    0x100000000010000000000000010000000080000000000005a006070050) (.leaf
    0xf2b01b00f0700e010260700502b01b00f0700e0100d03006070000000001000)) (.node (.leaf
    0x100000000010010000000080000010000000000000000012a006070050) (.leaf
    0x3c0101002804806c0a00900b040270701a0762b01b00f070000000001000))))) (.node (.node (.node
    (.node (.leaf 0x619002020200761901f06029030060700202b01b00807007030060700202b01b) (.leaf
    0xf002020010400a01202b100d0300607619002020010400a01201b0210300607)) (.node (.leaf
    0x90000010000000000000000030a0060762b01b00f0700e0100d0300607619) (.leaf
    0xf01303006076190020200c0700000000010000000001000000000100100000))) (.node (.node (.leaf
    0x81c0080ac06c04c0c0181d864008080300900b0400a01009030060700202b01b) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181d86400808004100280480ec0340c01)) (.node (.leaf
    0x1000000000100000000010010000000090000010000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006076190020200c070000)))) (.node (.node (.node
    (.leaf 0x801d86407c180780900e01009030060700202b01b01303006076190020200c0) (.leaf
    0x3d00280480ec40340c0181d864008080041002804806c0840c0181d86400808)) (.node (.leaf
    0x10000000000000000040a0060762b01b00f0700e0100d0300607619002020010) (.leaf
    0xf762b01b00f0700000000010000000001000000000100100000000d00000))) (.node (.node (.leaf
    0x140ac06c03c1c03804806c0981c0080ac06c0401c0b00900b0402b02b01b0100) (.leaf 0x3c0181c0))
    (.node (.leaf 0x10000005001000000000100100000000a0000010000020000000000005a) (.leaf
    0x3c0300900b0400a01009030060700202b01b01303006076190020200c070000)))))) (.node (.node (.node
    (.node (.node (.leaf 0xb01b01303006076190020201d07009030060700202b01b013030060761900202)
    (.leaf 0xf2b01b00f0700e0100d0300607619002020010400a01202b00d030060700202)) (.node (.leaf
    0x100000000010010000000110000010000000000000000020a006076) (.leaf
    0xf71201b1009030060700202b01b01303006076190020200c070000000001))) (.node (.node (.leaf
    0xb0400a01201b1009030060700202b01b01303006076190020200c0700b0400a0) (.leaf
    0xf6407c180780900e01009030060700202b01b01303006076190020200c0700)) (.node (.leaf
    0x80480ac40340c0181d864008080041002804806c0840c0181d864008080801d8) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181d864008080041002)))) (.node (.node (.node (.leaf
    0x1000000000100000000010010000000150000010000000000000000030a) (.leaf
    0x3c03c1c03804806c0981c0b00900b0402b02b01b0100762b01b00f070000)) (.node (.leaf
    0x100000000010010000000120000010000010000000000005a0060700502b01b) (.leaf
    0xf1009030060700202b01b01303006076190020200c07000000000100000050))) (.node (.node (.leaf
    0x864008080741c0240c0181c0080ac06c04c0c0181d864008080300900b0400a0) (.leaf
    0x3c0340c0181d864008080041002804806c0340c0181c0080ac06c04c0c0181d)) (.node (.leaf
    0x10010000000190000010000000000000000010a0060700502b01b00f0700e01) (.leaf
    0xf700202b01b01303006076190020200c070000000001000000000100000000))))) (.node (.node (.node
    (.node (.leaf 0x30060700202b01b01303006076190020200c0700b0400a071201b1009030060) (.leaf
    0xf1009030060700202b01b01303006076190020200c0700b0400a01201b1009)) (.node (.leaf
    0x1d864008080041002804806c0840c0181d864008080801d86407c180780900e0) (.leaf
    0xf0060700502b01b2b1db00404a01b003064008080041002804806c40340c018))) (.node (.node (.leaf
    0x20200c0700b0402a0762b01b00f0700e01009030060700202b01b0080700703) (.leaf
    0xf20010400a01201b00d030060700202012030060700202b01b01303006070)) (.node (.leaf
    0x201203006070020201102b01b0100700502b01b00f0700e0100d03006070020) (.leaf
    0xf20010400a01201b100d0300607002020010400a071201b00d0300607002)))) (.node (.node (.node
    (.leaf 0x80010000000160000000000020a0060762b01b00f0700e0100d03006070020) (.leaf
    0xf00f0700e0100d0300607000000000100000000010000000001000000000)) (.node (.leaf
    0x1000000000100100000001d0000010000000000000000020a0060762b01b) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01b00f07000000000100000))) (.node (.node (.leaf
    0x50010000005001000000000100100000001a0000010000000000000010005a) (.leaf 0x0)) (.node (.leaf
    0x0) (.leaf 0x0))))))

def fuelMode5 : ℕ := 3527
noncomputable def streamMode5 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.node (.leaf
    0x81c0080ac06c0201c01c0c0181c0080ac06c0101002804806c0a00900b0402f0) (.leaf
    0x3c40340c0181d864008080041002804806c0340c0181d864008080480c01)) (.node (.leaf
    0x806c00c190020201203006076190020201102b01b0100700502b01b00f0700e0) (.leaf
    0x3dc4806c0240c0181c0080ac06c0201c01c0c0181c0140ac06cac1ac01012))) (.node (.node (.leaf
    0x700b0400a01201b009030060700202b01b01303006070020200c0700b0400a0) (.leaf
    0xf0210300607002020200701f06029030060700202b01b01303006070020200c)) (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607002020010400a01201b) (.leaf
    0xf00607000000000100000000010000000001000000000006001000000001000)))) (.node (.node (.node
    (.leaf 0xc01c0c0181c0140ac06cac1ec01012806c00c19002020010400a071201b00d03) (.leaf
    0x3c04c0c0181c008080301c02c1002804806c40240c0181c0080ac06c0201)) (.node (.leaf
    0x1b009030060700202b01b02e0700502b01b00f0700e01009030060700202b01b) (.leaf
    0xf20200701f06029030060700202b01b01303006070020200c0700b0400a0120))) (.node (.node (.leaf
    0x700502b01b00f0700e0100d0300607002020010400a01201b02103006070020) (.leaf 0xf006)) (.node
    (.leaf 0x1000000000100000000010000000000070010000000020000000000010a) (.leaf
    0x3cac06cac22c01012806c00c19002020010400a01201b100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0xb0402a0762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0xf1201b00d030060700202012030060700202b01b01303006070020200c07)) (.node (.leaf
    0x70020201102b01b0100700502b01b00f0700e0100d0300607002020010400a0) (.leaf
    0xf1201b100d0300607002020010400a071201b00d03006070020201203006))) (.node (.node (.leaf
    0x10000000000020a0060762b01b00f0700e0100d0300607002020010400a0) (.leaf
    0xf100d03006070000000001000000000100000000010000000000080010000)) (.node (.leaf
    0x10010000000080000010000000000000000020a0060762b01b00f0700e0) (.leaf
    0xf30060700202b01b01303006076190020200c07000000000100000000010000)))) (.node (.node (.node
    (.leaf 0x140ac06c0c00c0181c0080ac06c04c0c0181d864008080300900b0400a010090) (.leaf
    0x3c0340c0181d864008080480c0181d864008080c41c02c1002804806c0681c0)) (.node (.leaf
    0x1102b01b0100700502b01b00f0700e0100d0300607619002020010400a01201b) (.leaf
    0x3dc0080ac06c0201c01c0c0181c0140ac06cac22c01012806c00c19002020))) (.node (.node (.leaf
    0xb01303006070020201d07009030060700202b01b013030060700202012030060) (.leaf
    0xf0210300607002020200701f06029030060700202b01b013030060700202b01)) (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607002020010400a01201b) (.leaf
    0xf00607000000000100000000010000000001000000000007001000000003000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x1c0080ac06c0201c01c0c0181c0140ac06cac26c01012806c00c190020201203)
    (.leaf 0x3cc0181c0080ac06c04c0c0181c008080301c02c100281c4806c0240c018)) (.node (.leaf
    0x701f06029030060700202b01b01303006070020200c0700b0400a01201b0090) (.leaf
    0xf2b01b00f0700e0100d0300607002020010400a01201b021030060700202020))) (.node (.node (.leaf
    0x100000000010000000000060010000000040000000000010a006070050) (.leaf
    0x3ec2ac01012806c00c19002020010400a071201b00d03006070000000001000)) (.node (.leaf
    0xc0700b0400a01201b1009030060700202b01b00807007030060700502b01b2) (.leaf
    0xfb01b02e0700502b01b00f0700e01009030060700202b01b013030060700202)))) (.node (.node (.node
    (.leaf 0x30060700202b01b01303006070020200c0700b0400a01201b009030060700202) (.leaf
    0xf100d0300607002020010400a01201b0210300607002020200701f060290)) (.node (.leaf
    0x10000000000070010000000050000000000010a0060700502b01b00f0700e0) (.leaf
    0x3d9002020010400a01201b100d0300607000000000100000000010000000))) (.node (.node (.leaf
    0xe01009030060700202b01b00807007030060700502b01b2b0bb00404a01b0030) (.leaf
    0xf012030060700202b01b01303006070020200c0700b0402a0762b01b00f0700)) (.node (.leaf
    0x700502b01b00f0700e0100d0300607002020010400a01201b00d030060700202) (.leaf
    0xf20010400a071201b00d03006070020201203006070020201102b01b0100))))) (.node (.node (.node
    (.node (.leaf 0x60762b01b00f0700e0100d0300607002020010400a01201b100d03006070020) (.leaf
    0xf0)) (.node (.leaf 0x1000000000100000000010000000000080010000000040000000000020a) (.leaf
    0xf0060762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x10000000001000000000100100000000b0000010000000000000000020a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006076190020200c070000)) (.node (.leaf
    0x801d86407c180780900e01009030060700202b01b01303006076190020200c0) (.leaf
    0x3d8ac06c0c8040340c0181d864008080041002804806c0840c0181d86400808)))) (.node (.node (.node
    (.leaf 0x1c0140ac06cac26c01012806c00c1900202001040330700b0400a01201b01a07) (.leaf
    0x3cc0181c008080301c02c10028040240c0181c0080ac06c0201c01c0c018)) (.node (.leaf
    0x202b01b01303006070020200c0700b0400a01201b009030060700202b01b0130) (.leaf
    0xf300607002020010400a01201b0210300607002020200701f06029030060700))) (.node (.node (.leaf
    0x60010000000040000000000020a0060762b01b00f0700e01201b100d0) (.leaf
    0x3d9002020010400a0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x1b1009030060700202b01b00807007030060700502b01b2b0ab00404a01b0030) (.leaf
    0xf00f0700e01009030060700202b01b01303006070020200c0700b0400a0120))))))) (.node (.node (.node
    (.node (.node (.node (.node (.leaf
    0xc0700b0400a01201b009030060700202b02b02e0700202b01b0100700502b01b) (.leaf
    0xf0210300607002020200701f06029030060700202b01b01303006070020200)) (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607002020010400a01201b) (.leaf
    0xf00607000000000100000000010000000001000000000007001000000006000))) (.node (.node (.leaf
    0xc01c0c0181c0140ac06cac2ec01012806c00c19002020010400a01201b100d03) (.leaf
    0x3dc02c100ac0ac06c0401d8ac06c03c1c038040240c0181c0080ac06c0201)) (.node (.leaf
    0x700202b01b013030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf30060700202b01b013030060700202b01b01303006070020201d0700903006)))) (.node (.node (.node
    (.leaf 0x700e0100d0300607002020010400a01201b0210300607002020200701f060290) (.leaf
    0xf0060700502b01b00f0)) (.node (.leaf
    0x1000000000100000000010000000000090010000000050000000000010a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x400a01009030060700202b01b00807007030060700502b01b2b0cb00404a01b) (.leaf
    0xf00c0700b0400a071201b009030060700202b01b01303006070020200c0700b)) (.node (.leaf
    0x3006070020200c0700b0400a01201b009030060700202b01b013030060700202) (.leaf
    0xf0010400a01201b0210300607002020200701f06029030060700202b01b0130))))) (.node (.node (.node
    (.node (.leaf 0x10000000060000000000010a0060700502b01b00f0700e0100d030060700202) (.leaf
    0xf400a0100d03006070000000001000000000100000000010000000000080)) (.node (.leaf
    0x81c0080ac06c0201c01c0c0181c0140ac06cac36c01012806c00c19002020010) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080301c02c100281c4806c40240c01))) (.node (.node (.leaf
    0x700e01009030060700202b01b01303006070020200c0700b0400a01201b10090) (.leaf
    0xf70020200c0700b0400a01201b009030060700202b01b02e0700502b01b00f0)) (.node (.leaf
    0x400a01201b0210300607002020200701f06029030060700202b01b013030060) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202001)))) (.node (.node (.node (.leaf
    0x1000000000100000000010000000000090010000000070000000000010a) (.leaf
    0x3cac06cac3ac01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf200c0700b0402a0762b01b00f0700e01009030060700202b01b013030060))) (.node (.node (.leaf
    0x20010400a01201b00d030060700202012030060700202b01b01303006070020) (.leaf
    0xf201203006070020201102b01b0100700502b01b00f0700e0100d0300607002)) (.node (.leaf
    0x2020010400a01201b100d0300607002020010400a071201b00d03006070020) (.leaf
    0xf0060762b01b00f0700e0100d0300607)))))) (.node (.node (.node (.node (.node (.leaf
    0x10000000001000000000100000000000a0010000000060000000000020a) (.leaf
    0x3cac06cac3ec01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0xb0402a0762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0xf70020200c0700b0400a01009030060700202b01b01303006070020200c07))) (.node (.node (.leaf
    0xd0000000000004a0060700202b01b02d030060700202b01b013030060) (.leaf
    0xf700e0100d03006070000000001000000000100000000010000000000040010)) (.node (.leaf
    0x1000000000100100000000f0000010000000000000000030a0060762b01b00f0) (.leaf
    0x3c0101002804806c0a00900b040340762b01b00f070000000001000000000)))) (.node (.node (.node
    (.leaf 0x4a0060700202b01b02d030060700202b01b00807007030060700202b01b) (.leaf
    0xf70000000001000000500100000000010010000000080000010000000000000)) (.node (.leaf
    0x864008080300900b0400a01009030060700202b01b01303006076190020200c0) (.leaf
    0x3c0340c0181d864008080041002804806c0340c0181c0080ac06c04c0c0181d))) (.node (.node (.leaf
    0x402b02b01b0100762b01b00f0700e0100d0300607619002020010400a01201b1) (.leaf
    0x3cac06cac3ac01012806c00c19002020010400a0100d0300607619002020010)) (.node (.leaf
    0x20200c0700b0400a071201b1009030060700202b01b0080700703006070050) (.leaf
    0xf3006070020200c0700b0400a01201b1009030060700202b01b0130300607))))) (.node (.node (.node
    (.node (.leaf 0x9030060700202b01b02e0700502b01b00f0700e01009030060700202b01b0130) (.leaf
    0xf701f06029030060700202b01b01303006070020200c0700b0400a01201b00)) (.node (.leaf
    0x2b01b00f0700e0100d0300607002020010400a01201b0210300607002020200) (.leaf 0xf00607005)))
    (.node (.node (.leaf 0x1000000000100000000010000000000090010000000080000000000010a) (.leaf
    0x3cac06cac3ec01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf200c0700b0402a0762b01b00f0700e01009030060700202b01b013030060)))) (.node (.node (.node
    (.leaf 0x20010400a01201b00d030060700202012030060700202b01b01303006070020) (.leaf
    0xf201203006070020201102b01b0100700502b01b00f0700e0100d0300607002)) (.node (.leaf
    0x2020010400a01201b100d0300607002020010400a071201b00d03006070020) (.leaf
    0xf0060762b01b00f0700e0100d0300607))) (.node (.node (.leaf
    0x10000000001000000000100000000000a0010000000070000000000020a) (.leaf
    0x3cac06cac42c01012806c00c19002020010400a01201b100d03006070000)) (.node (.leaf
    0xb0402a0762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0xf70020200c0700b0400a01009030060700202b01b01303006070020200c07))))))) (.node (.node (.node
    (.node (.node (.node (.leaf 0xe0000000000004a0060700202b01b02d030060700202b01b013030060)
    (.leaf 0xf700e0100d03006070000000001000000000100000000010000000000040010)) (.node (.leaf
    0x100000000010010000000100000010000000000000000030a0060762b01b00f0) (.leaf
    0xf1009030060700202b01b01303006076190020200c070000000001000000000))) (.node (.node (.leaf
    0x80900e01009030060700202b01b01303006076190020200c0700b0400a01201b) (.leaf
    0x3cc0181d864008080041002804806c0840c0181d864008080801d86407c1807)) (.node (.leaf
    0x1c01c0c0181c0140ac06cac3ec01012806c00c19002020010400a01201b100d0) (.leaf
    0x3ec06c04c0c0181c008080301c02c1002804806c40240c0181c0080ac06c020)))) (.node (.node (.node
    (.leaf 0x6070020200c0700b0402b02b01b0100762b01b00f0700e01009030060700202) (.leaf
    0xf7009030060700202b01b013030060700202012030060700202b01b013030)) (.node (.leaf
    0x701f06029030060700202b01b013030060700202b01b01303006070020201d0) (.leaf
    0xf2b01b00f0700e0100d0300607002020010400a01201b021030060700202020))) (.node (.node (.leaf
    0x1000000000100000000000b0010000000080000000000010a006070050) (.leaf
    0x3ec42c01012806c00c19002020010400a01201b100d03006070000000001000)) (.node (.leaf
    0x100762b01b00f0700e01009030060700202b01b00807007030060700502b01b2) (.leaf
    0xf400a01009030060700202b01b01303006070020200c0700b0402b02b01b0))))) (.node (.node (.node
    (.node (.leaf 0x200c0700b0400a071201b009030060700202b01b01303006070020200c0700b0) (.leaf
    0xf006070020200c0700b0400a01201b009030060700202b01b01303006070020)) (.node (.leaf
    0x20010400a01201b0210300607002020200701f06029030060700202b01b01303) (.leaf
    0xf0060700502b01b00f0700e0100d03006070020))) (.node (.node (.leaf
    0x10000000001000000000100000000000a0010000000090000000000010a) (.leaf
    0x3c00c19002020010402b02b01b0100762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x400a01009030060700202b01b00807007030060700502b01b2b11b00404a01b) (.leaf
    0xf700b0400a071201b1009030060700202b01b01303006070020200c0700b)))) (.node (.node (.node
    (.leaf 0x70020200c0700b0400a01201b1009030060700202b01b01303006070020200c0) (.leaf
    0xf700202b01b02e0700502b01b00f0700e01009030060700202b01b013030060)) (.node (.leaf
    0x6029030060700202b01b01303006070020200c0700b0400a01201b009030060) (.leaf
    0xf00f0700e0100d0300607002020010400a01201b0210300607002020200701f))) (.node (.node (.leaf
    0x1000000000100000000000b00100000000a0000000000010a0060700502b01b) (.leaf
    0x3ec4ac01012806c00c19002020010400a0100d0300607000000000100000000)) (.node (.leaf
    0xc0700b0400a071201b1009030060700202b01b00807007030060700502b01b2) (.leaf
    0xf70020200c0700b0400a01201b1009030060700202b01b0130300607002020)))))) (.node (.node (.node
    (.node (.node (.leaf 0x20200c0700b0402a0762b01b00f0700e01009030060700202b01b013030060)
    (.leaf 0xf20010400a01201b00d030060700202012030060700202b01b0130300607)) (.node (.leaf
    0x201203006070020201102b01b0100700502b01b00f0700e0100d03006070020) (.leaf
    0xf20010400a01201b100d0300607002020010400a071201b00d0300607002))) (.node (.node (.leaf
    0xc0010000000090000000000020a0060762b01b00f0700e0100d03006070020) (.leaf
    0xf400a071201b100d0300607000000000100000000010000000001000000000)) (.node (.leaf
    0x81c0080ac06c0201c01c0c0181c0140ac06cac4ec01012806c00c19002020010) (.leaf
    0x3c0240c0181c0080ac06c04c0c0181c008080301c02c1002804806c40240c01)))) (.node (.node (.node
    (.leaf 0x9030060700202b01b01303006070020200c0700b0402a0762b01b00f0700e01) (.leaf
    0xf700202b01b02d030060700202b01b01303006070020200c0700b0400a010)) (.node (.leaf
    0x1000000000100000000010000000000060010000000100000000000004a0060) (.leaf
    0x3ec06cac52c01012806c00c19002020010400a01201b100d030060700000000))) (.node (.node (.leaf
    0xb0402a0762b01b00f0700e01009030060700202b01b00807007030060700502) (.leaf
    0xf70020200c0700b0400a01009030060700202b01b01303006070020200c070)) (.node (.leaf
    0x14a006070160601502b01b01401009030060700202b01b013030060) (.leaf
    0xf30060700000000010000000001000000000100000000000400100000001200))))) (.node (.node (.node
    (.node (.leaf 0x10010000000140000010000000000000000040a0060762b01b00f0700e0100d0) (.leaf
    0xf0060700202b01b0350762b01b00f0700000000010000000001000000000)) (.node (.leaf
    0x50010000005001000000000100100000000c0000010000000000000010006a) (.leaf 0x0))) (.node
    (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf
    0x0)) (.node (.leaf 0x0) (.leaf 0x0))))))))

def fuelMode6 : ℕ := 6592
noncomputable def streamMode6 : WordRLE.BTree ℕ :=
  .node (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x6c0201c01c0c0181c0080ac06c010100281c4806c0a00900b0403702b02b0170) (.leaf
    0x3cac06c0101002804806c06c1c02c1002804806c0681c0e00c0181c0080ac0)) (.node (.leaf
    0xd030060700202b01b01303006076190020201d0700903006076190020201c0) (.leaf
    0xf0060700502b01b00f0700e01))) (.node (.node (.leaf
    0x1000000000100000040010010000000050000010000000000000000010a) (.leaf
    0x3c0300900b0400a01009030060700202b01b01303006076190020200c070000)) (.node (.leaf
    0xc0700b0400a01201b0090300607038030060700202b01b013030060761900202) (.leaf
    0xf201d0700903006076190020201c02b03b02e0700202b01b010070020200)))) (.node (.node (.node
    (.leaf 0x2b01b01303006076190020201d07009030060700202b01b01303006076190020) (.leaf
    0x3cc0181c0140ac06cac2ac01012806c00c190020201d0700903006070020)) (.node (.leaf
    0x400a01201b0210300607002020200701f06029030060700202b01b008070070) (.leaf
    0xfb01b00f0700e0100d0300607002020010400a01202b100d030060700202001))) (.node (.node (.leaf
    0x100000000010000000000030010000000060000000000030a0060762) (.leaf
    0xf00d030060700202b01b013030060700202b01b013030060700000000010)) (.node (.leaf
    0x100000000c0000010000000000000000010a0060700502b01b00f0700e01201b) (.leaf
    0xf2b01b01303006076190020200c0700000000010000000001000000000100))))) (.node (.node (.node
    (.node (.leaf 0x60700202b01b01303006076190020200c0700b0400a01201b100903006070020) (.leaf
    0x3d002804806c0840c0181d864008080801d86407c180780900e010090300)) (.node (.leaf
    0x6060150200c0700b0400a01201b00903006070220100d0300607619002020010) (.leaf
    0x3cac26c01012806c00c19002020010401802b02b02e0700202b01b0100701))) (.node (.node (.leaf
    0x70020200c0700b0400a01009030060700202b01b00807007030060700502b01b) (.leaf
    0xf00a01201b0210300607002020200701f06029030060700202b01b013030060)) (.node (.leaf
    0x16060150200c0700b0400a01201b00903006070220100d03006070020200104) (.leaf
    0xf20010400a0100d0300607002020010401802b02b02e0700202b01b01007)))) (.node (.node (.node
    (.leaf 0x7002020120300607002020390701a0700502b01b00f0700e0100d03006070020) (.leaf
    0xf0100700502b01b00f0700e0100d0300607002020010400a01201b00d030060)) (.node (.leaf
    0x1c0c0181c0140ac32c01012806c00c29002020120300607a290020201102b01b) (.leaf
    0x3c04c0c0181c008080301c02c100281c4806c0240c0181c0080ac06c0201c0))) (.node (.node (.leaf
    0x700202b01b01303006070020200c0700b0400a01201b009030060700202b01b) (.leaf
    0xf00d0300607002020010400a01201b0210300607002020200701f0602903006)) (.node (.leaf
    0x30060700202001040250400a01201b024060230700b0400a01201b01a0702201) (.leaf
    0xf700e010260700502b01b00f0700e0100d0300607002020010400a0100d0)))))) (.node (.node (.node
    (.node (.node (.leaf 0x10000000000080000000000040000000000012a0060700502b01b00f0) (.leaf
    0x3e806c00c29002020010400a071201b00d03006070000000001000000000100)) (.node (.leaf
    0x700b0400a01201b1009030060700202b01b00807007030060700502b0db00404) (.leaf
    0xf01a0700502b01b00f0700e01009030060700202b01b01303006070020200c0))) (.node (.node (.leaf
    0x6029030060700202b01b00807007030060700202b01b0040400a01201b03a07) (.leaf
    0xf00a01202b100d0300607002020010400a01201b0210300607002020200701f)) (.node (.leaf
    0x70000000000030a0060762b01b00f0700e0100d03006070020200104) (.leaf
    0xf1201b100d0300607000000000100000000010000000001000000000007000)))) (.node (.node (.node
    (.leaf 0x81c0080ac06c0201c01c0c0181c0140ac3ac01012806c00c29002020010400a0) (.leaf
    0x3c04c0c0181c008080301c02c1009c1c0681d8ac06c03c1c038040240c01)) (.node (.leaf
    0x400a01203b00d030060700202b01b013030060700202012030060700202b01b) (.leaf
    0xf0060762b01b00f0700e0100d030060700202001))) (.node (.node (.leaf
    0x10000000001000000000100000000000500000000000a0000000000030a) (.leaf
    0x3d2806c00c2900202001040270701a0762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x200c0700b0400a01009030060700202b01b00807007030060700502b0fb0040) (.leaf
    0xf3006070020200c0700b0400a01201b009030060700202b01b0130300607002))))) (.node (.node (.node
    (.node (.leaf 0x20010400a01201b0210300607002020200701f06029030060700202b01b0130) (.leaf
    0xf762b01b00f0700e0100d0300607002020010400a01203b100d0300607002)) (.node (.leaf
    0x1000000000100000000010000000000070000000000080000000000040a0060) (.leaf
    0x3c0181c0140ac42c01012806c00c29002020010400a0100d030060700000000))) (.node (.node (.leaf
    0x1303006070020200c0700b0400a01201b1009030060700202b01b0080700703) (.leaf
    0xf2b01b0100700202b01b0100700502b01b00f0700e01009030060700202b01b)) (.node (.leaf
    0x20000000000100000000000005a0060700502b01b00f0700e01201b026070020) (.leaf
    0xf400a01201b100d030060700000000010000000001000000000100000000000)))) (.node (.node (.node
    (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac46c01012806c00c29002020010) (.leaf
    0x3ec06c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c0380402)) (.node (.leaf
    0x6070020201d07009030060700202b01b013030060700202012030060700202) (.leaf
    0xf700e0100d0300607002020010400a01202b00d030060700202b01b01303))) (.node (.node (.leaf
    0x1000000000100000000000700000000000c0000000000020a0060762b01b00f0) (.leaf
    0xf402b02b01b0100762b01b00f0700e0100d03006070000000001000000000)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac4ac01012806c00c29002020010) (.leaf
    0x3c0281c4806c0240c0181c0080ac06c04c0c0181c008080301c02c100280402))))))) (.node (.node
    (.node (.node (.node (.node (.node (.leaf
    0x200c0700b0400a01201b009030060700202b01b01303006070020200c0700b04) (.leaf
    0xf201b0210300607002020200701f06029030060700202b01b01303006070020)) (.node (.leaf
    0xf0700e0100d0300607002020010400a01202b100d0300607002020010400a01) (.leaf 0xf0060762b01b0)))
    (.node (.node (.leaf 0x10000000001000000000100000000000900000000000a0000000000030a) (.leaf
    0x3cc0181c0140ac4ec01012806c00c29002020010400a0100d03006070000)) (.node (.leaf
    0x1303006070020200c0700b0400a071201b1009030060700202b01b008070070) (.leaf
    0xf2b01b01303006070020200c0700b0400a01201b1009030060700202b01b)))) (.node (.node (.node
    (.leaf 0xf0700e01201b0260700202b01b0100700502b01b00f0700e0100903006070020) (.leaf
    0xf0060700502b01b00)) (.node (.leaf
    0x1000000000100000000010000000000040000000000110000000000005a) (.leaf
    0x3dc0140ac52c01012806c00c29002020010400a071201b100d03006070000))) (.node (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xf700b0402b02b01b0100762b01b00f0700e01009030060700202b01b0130)) (.node (.leaf
    0x700202b01b013030060700202012030060700202b01b01303006070020200c0) (.leaf
    0xf20010400a01201b00d030060700202b01b01303006070020201d0700903006))))) (.node (.node (.node
    (.node (.leaf 0xe0000000000010a0060700502b01b00f0700e0100d03006070020) (.leaf
    0xf00a01201b100d0300607000000000100000000010000000001000000000009)) (.node (.leaf
    0xc0181c0080ac06c0201c01c0c0181c0140ac56c01012806c00c290020200104) (.leaf
    0x3c04c0c0181c008080301c02c100ac0ac06c0401d8ac06c03c1c03804024))) (.node (.node (.leaf
    0x30060700202b01b01303006070020200c0700b0400a01009030060700202b01b) (.leaf
    0xf201b009030060700202b01b01303006070020200c0700b0400a071201b0090)) (.node (.leaf
    0x2020200701f06029030060700202b01b01303006070020200c0700b0400a01) (.leaf
    0xf7002020010400a01201b100d0300607002020010400a01201b0210300607)))) (.node (.node (.node
    (.leaf 0xb00000000000c0000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000)) (.node (.leaf
    0x6c0201c01c0c0181c0140ac5ac01012806c00c29002020010402b02b01b0100) (.leaf
    0x3cc0181c0080ac06c04c0c0181c008080301c02c10028040240c0181c0080ac))) (.node (.node (.leaf
    0x201b1009030060700202b01b01303006070020200c0700b0400a071201b10090) (.leaf
    0xf00f0700e01009030060700202b01b01303006070020200c0700b0400a01)) (.node (.leaf
    0x120000000000005a0060700502b01b00f0700e01201b0260700502b01b) (.leaf
    0xf400a0100d03006070000000001000000000100000000010000000000060000)))))) (.node (.node (.node
    (.node (.node (.leaf 0x40c0181c0080ac06c0201c01c0c0181c0140ac5ec01012806c00c29002020010)
    (.leaf 0x3c40240c0181c0080ac06c04c0c0181c008080301c02c100281c4806c402)) (.node (.leaf
    0xb00f0700e01009030060700202b01b01303006070020200c0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01))) (.node (.node (.leaf
    0x1000000000100000000010000000000040000000000140000000000015a) (.leaf
    0x3dc0140ac62c01012806c00c29002020010400a071201b100d03006070000)) (.node (.leaf
    0x3006070020200c0700b0400a01201b1009030060700202b01b00807007030060) (.leaf
    0xfb01b00f0700e01201b0260762b01b00f0700e01009030060700202b01b0130)))) (.node (.node (.node
    (.leaf 0x100000000010000000000020000000000160000000000025a0060700502) (.leaf
    0x3c01012806c00c29002020010400a01201b100d030060700000000010000)) (.node (.leaf
    0x260762b01b00f0700e01009030060700202b01b00807007030060700502b19b) (.leaf
    0xf0060700502b01b00f0700e01201b))) (.node (.node (.leaf
    0x1000000000100000000010000000000000000000000180000000000035a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010000000000180010000000000000000000042a0060) (.leaf
    0x3c0140ac06cac2ac01012806c00c19002020010400a0100d030060700000000))))) (.node (.node (.node
    (.node (.leaf 0xb03a0701a0700502b01b00f0700e01009030060700202b01b008070070300607) (.leaf
    0xf701f06029030060700202b01b00807007030060700202b01b0040400a01201)) (.node (.leaf
    0x1201b01a070220100d0300607002020010400a01201b0210300607002020200) (.leaf
    0xf0010400a0100d030060700202001040250400a01201b024060230700b0400a))) (.node (.node (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d030060700202) (.leaf 0x0)) (.node
    (.leaf 0x1000000000100000000010000000000060010000000050000000000012a) (.leaf
    0x3d2806c00c19002020390701a0700502b01b00f0700e0100d03006070000)))) (.node (.node (.node
    (.leaf 0x30060700202012030060700202b01b00807007030060700502b01b2b0bb0040) (.leaf
    0xf024060230700b0400a01201b01a0702201201b00d030060700202b01b013)) (.node (.leaf
    0xe0100d0300607002020010400a0100d030060700202001040250400a01201b) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f07))) (.node (.node (.leaf
    0x1000000000100000000010000000000040010000000080000000000012a) (.leaf
    0x3dc01c0c0181c0140ac06cac32c01012806c00c190020201203006070000)) (.node (.leaf
    0x202b01b01303006070020200c0700b0400a01201b009030060700202b01b0080) (.leaf
    0xf300607002020010400a01201b0210300607002020200701f06029030060700))))))) (.node (.node
    (.node (.node (.node (.node (.leaf
    0x2001040250400a01201b024060230700b0400a01201b01a0702201201b100d0) (.leaf
    0xf10260762b01b00f0700e0100d0300607002020010400a0100d0300607002)) (.node (.leaf
    0x10000000000060010000000060000000000022a0060700502b01b00f0700e0) (.leaf
    0x3c00c19002020010400a01201b00d0300607000000000100000000010000000))) (.node (.node (.leaf
    0x700e01009030060700202b01b00807007030060700502b01b2b0db00404a01b) (.leaf
    0xf700202b02b0040400a01201b03a0701a0700202b01b0100700502b01b00f)) (.node (.leaf
    0x1201b0210300607002020200701f06029030060700202b01b00807007030060) (.leaf
    0xf700e0100d0300607002020010400a01202b100d0300607002020010400a)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000500100000000a0000000000030a0060762b01b00f0) (.leaf
    0xf01102b01b0100700502b01b00f0700e0100d03006070000000001000000000)) (.node (.leaf
    0xc0181c0080ac06c0201c01c0c0181c0140ac06cac3ac01012806c00c1900202) (.leaf
    0x3ec06c04c0c0181c008080741c0240c0181c0080ac06c04c0c0181c00808048))) (.node (.node (.leaf
    0x201c02b01b0040400a01201b01b0700b0400a01201b01a07038030060700202) (.leaf
    0xf00f0700e0100d030060700202b01b01303006070020201d070090300607002)) (.node (.leaf
    0x1000000000100000000000700100000000a0000000000010a0060700502b01b) (.leaf
    0x3c0140ac06cac3ec01012806c00c19002020120300607000000000100000000))))) (.node (.node (.node
    (.node (.leaf 0x6070020200c0700b0400a071201b009030060700202b01b008070070300607) (.leaf
    0xfb01b01303006070020200c0700b0400a01201b009030060700202b01b01303)) (.node (.leaf
    0x607002020010400a01201b0210300607002020200701f06029030060700202) (.leaf
    0xf2001040250400a01201b024060230700b0400a01201b01a070220100d03))) (.node (.node (.leaf
    0x10260700502b01b00f0700e0100d0300607002020010400a0100d03006070020) (.leaf
    0xf0060700502b01b00f0700e0)) (.node (.leaf
    0x1000000000100000000010000000000080010000000080000000000012a) (.leaf
    0x3cac06cac42c01012806c00c19002020010400a071201b00d03006070000)))) (.node (.node (.node
    (.leaf 0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf1201b03a0701a0700502b01b00f0700e01009030060700202b01b013030060)) (.node (.leaf
    0x20200701f06029030060700202b01b00807007030060700202b01b0040400a0) (.leaf
    0xf002020010400a01202b100d0300607002020010400a01201b0210300607002))) (.node (.node (.leaf
    0x700100000000b0000000000030a0060762b01b00f0700e0100d0300607) (.leaf
    0xf20010400a01201b100d030060700000000010000000001000000000100000)) (.node (.leaf
    0x40c0181c0080ac06c0201c01c0c0181c0140ac06cac46c01012806c00c190020) (.leaf
    0x3cac06c04c0c0181c008080301c02c1009c1c0681d8ac06c03c1c0380402)))))) (.node (.node (.node
    (.node (.node (.leaf 0x20010400a01203b00d030060700202b01b01303006070020201203006070020)
    (.leaf 0xf0060762b01b00f0700e0100d0300607002)) (.node (.leaf
    0x10000000001000000000100000000000500100000000e0000000000030a) (.leaf
    0x3d2806c00c1900202001040270701a0762b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x700b0400a01009030060700202b01b00807007030060700502b01b2b12b0040) (.leaf
    0xf70020200c0700b0400a01201b009030060700202b01b01303006070020200c)) (.node (.leaf
    0x400a01201b0210300607002020200701f06029030060700202b01b013030060) (.leaf
    0xfb01b00f0700e0100d0300607002020010400a01203b100d030060700202001)))) (.node (.node (.node
    (.leaf 0x1000000000100000000000700100000000c0000000000040a0060762) (.leaf
    0x3cac06cac4ec01012806c00c19002020010400a0100d030060700000000010)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf700202b01b0100700502b01b00f0700e01009030060700202b01b013030060))) (.node (.node (.leaf
    0x140000000000005a0060700502b01b00f0700e01201b0260700202b01b0100) (.leaf
    0xf100d030060700000000010000000001000000000100000000000200100000)) (.node (.leaf
    0x6c0201c01c0c0181c0140ac06cac52c01012806c00c19002020010400a01201b) (.leaf
    0x3c80301c02c100ac0ac06c0401d8ac06c03c1c038040240c0181c0080ac0))))) (.node (.node (.node
    (.node (.leaf 0x30060700202b01b013030060700202012030060700202b01b01303006070020) (.leaf
    0xf7002020010400a01202b00d030060700202b01b01303006070020201d07009)) (.node (.leaf
    0x70010000000100000000000020a0060762b01b00f0700e0100d030060) (.leaf
    0xf762b01b00f0700e0100d03006070000000001000000000100000000010000))) (.node (.node (.leaf
    0x1c01c0c0181c0140ac06cac56c01012806c00c19002020010402b02b01b0100) (.leaf
    0x3dc0080ac06c04c0c0181c008080301c02c10028040240c0181c0080ac06c02)) (.node (.leaf
    0xb009030060700202b01b01303006070020200c0700b0400a071201b009030060) (.leaf
    0xf0200701f06029030060700202b01b01303006070020200c0700b0400a01201)))) (.node (.node (.node
    (.leaf 0x2020010400a01202b100d0300607002020010400a01201b021030060700202) (.leaf
    0xf0060762b01b00f0700e0100d0300607)) (.node (.leaf
    0x10000000001000000000100000000000900100000000e0000000000030a) (.leaf
    0x3dc0140ac06cac5ac01012806c00c19002020010400a0100d03006070000))) (.node (.node (.leaf
    0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303)) (.node (.leaf
    0xe01201b0260700202b01b0100700502b01b00f0700e01009030060700202b01b) (.leaf
    0xf0060700502b01b00f0700))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000040010000000150000000000005a) (.leaf
    0x3cac06cac5ec01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf402b02b01b0100762b01b00f0700e01009030060700202b01b013030060))) (.node (.node (.leaf
    0x2b01b013030060700202012030060700202b01b01303006070020200c0700b0) (.leaf
    0xf400a01201b00d030060700202b01b01303006070020201d070090300607002)) (.node (.leaf
    0x120000000000010a0060700502b01b00f0700e0100d0300607002020010) (.leaf
    0xf201b100d030060700000000010000000001000000000100000000000900100)))) (.node (.node (.node
    (.leaf 0xac06c0201c01c0c0181c0140ac06cac62c01012806c00c19002020010400a01) (.leaf
    0x3dc008080301c02c100ac0ac06c0401d8ac06c03c1c038040240c0181c008)) (.node (.leaf
    0x2b01b01303006070020200c0700b0400a01009030060700202b01b013030060) (.leaf
    0xf0060700202b01b01303006070020200c0700b0400a071201b0090300607002))) (.node (.node (.leaf
    0x701f06029030060700202b01b01303006070020200c0700b0400a01201b00903) (.leaf
    0xf400a01201b100d0300607002020010400a01201b0210300607002020200)) (.node (.leaf
    0x10000000100000000000020a0060762b01b00f0700e0100d0300607002020010) (.leaf
    0xf700e0100d030060700000000010000000001000000000100000000000b00))))) (.node (.node (.node
    (.node (.leaf 0x1c0140ac06cac66c01012806c00c19002020010402b02b01b0100762b01b00f0) (.leaf
    0x3cc0181c008080301c02c10028040240c0181c0080ac06c0201c01c0c018)) (.node (.leaf
    0x2b01b01303006070020200c0700b0400a071201b1009030060700202b01b0130) (.leaf
    0xf700202b01b01303006070020200c0700b0400a01201b100903006070020))) (.node (.node (.leaf
    0xf0060700502b01b00f0700e01201b0260700502b01b00f0700e01009030060) (.leaf 0x0)) (.node (.leaf
    0x1000000000100000000010000000000060010000000160000000000005a) (.leaf
    0x3dc0140ac06cac6ac01012806c00c19002020010400a0100d03006070000)))) (.node (.node (.node
    (.leaf 0x6070020200c0700b0400a071201b1009030060700202b01b00807007030060) (.leaf
    0xf01303006070020200c0700b0400a01201b1009030060700202b01b01303)) (.node (.leaf
    0x700502b01b00f0700e01201b0260762b01b00f0700e01009030060700202b01b) (.leaf 0xf0060))) (.node
    (.node (.leaf 0x1000000000100000000010000000000040010000000180000000000015a) (.leaf
    0x3cac06cac6ec01012806c00c19002020010400a071201b100d03006070000)) (.node (.leaf
    0x70020200c0700b0400a01201b1009030060700202b01b0080700703006070050) (.leaf
    0xf700e01201b0260762b01b00f0700e01009030060700202b01b013030060)))))) (.node (.node (.node
    (.node (.node (.leaf 0x100000000000200100000001a0000000000025a0060700502b01b00f0) (.leaf
    0x3e806c00c19002020010400a01201b100d03006070000000001000000000100)) (.node (.leaf
    0xb00f0700e01009030060700202b01b00807007030060700502b01b2b1cb00404) (.leaf
    0xf0060700502b01b00f0700e01201b0260762b01))) (.node (.node (.leaf
    0x10000000001000000000100000000000000100000001c0000000000035a) (.leaf
    0xf700502b01b00f0700e01201b0260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100100000001c0000010000000000000000042a0060) (.leaf
    0x3cac06c0101002804806c0a00900b040270701a0762b01b00f0700000000)))) (.node (.node (.node
    (.leaf 0x607619002020200761901f06029030060700202b01b0080700703006070020) (.leaf
    0xf700b0400a01201b01a070220100d0300607619002020010400a01201b02103)) (.node (.leaf
    0xc19002020010400a0100d030060761900202001040250400a01201b024060230) (.leaf
    0x3c40240c0181c0080ac06c0201c01c0c0181c0140ac06cac32c01012806c00))) (.node (.node (.leaf
    0xc0000000000005a0060700502b01b00f0700e010260700502b01b00f0700e0) (.leaf
    0xf100d0300607000000000100000000010000000001000000000000001000000)) (.node (.leaf
    0x12a0060700502b01b00f0700e010260700502b01b00f0700e0) (.leaf
    0xf0020200c0700000000010000000001000000000100100000000c000001000))))) (.node (.node (.node
    (.node (.leaf 0x4c0c0181d864008080300900b0400a01009030060700202b01b0130300607619) (.leaf
    0x3c0901808c1c02c1002804806c0681c08804806c0340c0181c0080ac06c0)) (.node (.leaf
    0xd0300607619002020010400a0100d030060761900202001040250400a01201b) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e010))) (.node (.node (.leaf
    0x10000000001000000000100100000000c0000010000000000000000012a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006076190020200c070000)) (.node (.leaf
    0x801d86407c180780900e01009030060700202b01b01303006076190020200c0) (.leaf
    0x3dc08804806c40340c0181d864008080041002804806c0840c0181d86400808)))) (.node (.node (.node
    (.leaf 0x12806c00c1900202001040250400a01201b024060230700b0400a01201b01a0) (.leaf
    0x3dc02c10028040240c0181c0080ac06c0201c01c0c0181c0140ac06cac3ec01)) (.node (.leaf
    0x10260700502b01b00f0700e01009030060700202b01b01303006070020200c0) (.leaf
    0xf0060700502b01b00f0700e))) (.node (.node (.leaf
    0x10000000001000000000100000000000200100000000e0000000000005a) (.leaf
    0x3dc0140ac06cac42c01012806c00c19002020010400a0100d03006070000)) (.node (.leaf
    0xf0700e010260762b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf0060700502b01b))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf
    0x1000000000100000000010000000000000010000000100000000000015a) (.leaf
    0xf0060700502b01b00f0700e010260762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x1000000000100000000010010000000100000010000000000000000022a) (.leaf
    0x3d002804806c0e81c0681c0b00900b0402b02b01b0100762b01b00f070000))) (.node (.node (.leaf
    0x19002020200701f06029030060700202b01b00807007030060700202b02b0040) (.leaf
    0xf20010400a01202b100d0300607619002020010400a01201b02103006076)) (.node (.leaf
    0x10000000000000000030a0060762b01b00f0700e0100d03006076190020) (.leaf
    0xf3006076190020200c07000000000100000000010000000001001000000011)))) (.node (.node (.node
    (.leaf 0x80ac06c04c0c0181d864008080300900b0400a01009030060700202b01b0130) (.leaf
    0x3c0681c0e00c0181c0080ac06c04c0c0181d864008080741c0240c0181c0)) (.node (.leaf
    0x1d0700903006076190020201c02b01b0040400a01201b01b0700b0400a01201b) (.leaf
    0xf0060700502b01b00f0700e0100d030060700202b01b0130300607619002020))) (.node (.node (.leaf
    0x1000000000100000000010010000000150000010000000000000000010a) (.leaf
    0xf00b0400a071201b1009030060700202b01b01303006076190020200c070000)) (.node (.leaf
    0x200c0700b0400a01201b1009030060700202b01b01303006076190020200c07) (.leaf
    0x3c80801d86407c180780900e01009030060700202b01b0130300607619002))))) (.node (.node (.node
    (.node (.leaf 0x1201b01a070220100d0300607619002020010400a01201b02103006076190020) (.leaf
    0x3ec5ec01012806c00c1900202001040250400a01201b024060230700b0400a0)) (.node (.leaf
    0x20200c0700b0400a01009030060700202b01b00807007030060700502b01b2) (.leaf
    0xf1201b0210300607002020200701f06029030060700202b01b0130300607))) (.node (.node (.leaf
    0x700e0100d03006070020200104a01b03c0703b0100d0300607002020010400a0) (.leaf
    0xf0060762b01b00f0)) (.node (.leaf
    0x1000000000100000000010000000000050010000000120000000000020a) (.leaf
    0x3dc0140ac06cac62c01012806c00c19002020010400a0100d03006070000)))) (.node (.node (.node
    (.leaf 0x700e010260700502b01b00f0700e01009030060700202b01b00807007030060) (.leaf
    0xf0060700502b01b00f)) (.node (.leaf
    0x1000000000100000000010000000000000010000000180000000000005a) (.leaf
    0xf0060700502b01b00f0700e010260700502b01b00f0700e0100d03006070000))) (.node (.node (.leaf
    0x1000000000100000000010010000000180000010000000000000000012a) (.leaf
    0x3dc0080ac06c0101002804806c0a00900b040270701a0762b01b00f070000)) (.node (.leaf
    0x210300607619002020200761901f06029030060700202b01b00807007030060) (.leaf
    0xf300607619002020010400a01202b100d0300607619002020010400a01201b)))))) (.node (.node (.node
    (.node (.node (.leaf 0x10010000000190000010000000000000000030a0060762b01b00f0700e0100d0)
    (.leaf 0xf700202b01b01303006076190020200c0700000000010000000001000000000)) (.node (.leaf
    0xec0340c0181c0080ac06c04c0c0181d864008080300900b0400a01009030060) (.leaf
    0x3c0181d8ac06c03c1c038040340c0181d8640080800410028048))) (.node (.node (.leaf
    0x1000000000100000000010010000000190000010000000000000000030a) (.leaf
    0xf700b0400a01201b1009030060700202b01b01303006076190020200c070000)) (.node (.leaf
    0x801d86407c180780900e01009030060700202b01b01303006076190020200c0) (.leaf
    0x3d00280480ec40340c0181d864008080041002804806c0840c0181d86400808)))) (.node (.node (.node
    (.leaf 0x81c0080ac06c0201c01c0c0181c0140ac06cac76c01012806c00c19002020010) (.leaf
    0x3cac06c04c0c0181c008080301c02c100a81d8ac06c03c1c038040240c01)) (.node (.leaf
    0x1009030060700202b01b01303006070020200c0700b0400a0100903006070020) (.leaf
    0xf006070160601502b01b0140))) (.node (.node (.leaf
    0x10000000001000000000100000000000400100000001b0000000000014a) (.leaf
    0xf0060762b01b00f0700e0100d03006070000)) (.node (.leaf
    0x10000000001000000000100100000001d0000010000000000000000040a) (.leaf
    0x3c0981c0080ac06c0401c0b00900b0402b02b01b0100762b01b00f070000))))) (.node (.node (.node
    (.node (.leaf 0x100000001a0000010000020000000000005a0060700502b01b00f0700e01201b) (.leaf
    0xf2b01b01303006076190020200c0700000000010000005001000000000100)) (.node (.leaf
    0x40c0181c0080ac06c04c0c0181d864008080300900b0400a0100903006070020) (.leaf
    0x3c8004100280480ac0340c0181c0080ac06c04c0c0181d864008080741c02))) (.node (.node (.leaf
    0x10000000000000000020a0060762b01b00f0700e0100d03006076190020) (.leaf
    0xf3006076190020200c07000000000100000000010000000001001000000021)) (.node (.leaf
    0x1b01303006076190020200c0700b0400a071201b1009030060700202b01b0130) (.leaf
    0xf2b01b01303006076190020200c0700b0400a01201b1009030060700202b0)))) (.node (.node (.node
    (.leaf 0x2804806c0840c0181d864008080801d86407c180780900e0100903006070020) (.leaf
    0xfb25b00404a01b00306400808004100280480ac40340c0181d8640080800410)) (.node (.leaf
    0x2a0762b01b00f0700e01009030060700202b01b00807007030060700502b01b2) (.leaf
    0xf200c0700b0400a01009030060700202b01b01303006070020200c0700b040))) (.node (.node (.leaf
    0x230000000000004a0060700202b01b02d030060700202b01b01303006070020) (.leaf
    0xf100d0300607000000000100000000010000000001000000000004001000000)) (.node (.leaf
    0x10010000000250000010000000000000000030a0060762b01b00f0700e0) (.leaf
    0x3dc0b00900b0402b02b01b0100762b01b00f07000000000100000000010000))))))) (.node (.node (.node
    (.node (.node (.node (.leaf 0x220000010000010000000000005a0060700502b01b00f0700e01201b0260)
    (.leaf 0xf01303006076190020200c07000000000100000050010000000001001000)) (.node (.leaf
    0x81c0080ac06c04c0c0181d864008080300900b0400a01009030060700202b01b) (.leaf
    0x3d002804806c0340c0181c0080ac06c04c0c0181d864008080741c0240c01))) (.node (.node (.leaf
    0x10a0060700502b01b00f0700e0100d0300607619002020010) (.leaf
    0x3d90020200c0700000000010000000001000000000100100000002900000100)) (.node (.leaf
    0x181d864008080301c02c100281c4806c40240c0181c0080ac06c04c0c0181d8) (.leaf
    0x3cc0181d864008080301c02c1002804806c40240c0181c0080ac06c04c0c)))) (.node (.node (.node
    (.leaf 0x840c0181d864008080801d86407c180780900e01009030060700202b01b0130) (.leaf
    0xf7007030060700502b01b2b2cb00404a01b003064008080041002804806c)) (.node (.leaf
    0x2b01b01303006070020200c0700b0400a01201b1009030060700202b01b0080) (.leaf
    0xf1201b009030060700202b01b02e0700502b01b00f0700e010090300607002))) (.node (.node (.leaf
    0x7002020200701f06029030060700202b01b01303006070020200c0700b0400a0) (.leaf
    0xf0060700502b01b00f0700e0100d0300607002020010400a01201b021030060)) (.node (.leaf
    0x1000000000100000000010000000000070010000000270000000000010a) (.leaf
    0x3cac06cacb6c01012806c00c19002020010400a01201b100d03006070000))))) (.node (.node (.node
    (.node (.leaf 0xb0402a0762b01b00f0700e01009030060700202b01b0080700703006070050) (.leaf
    0xf1201b00d030060700202012030060700202b01b01303006070020200c07)) (.node (.leaf
    0x70020201102b01b0100700502b01b00f0700e0100d0300607002020010400a0) (.leaf
    0xf1201b100d0300607002020010400a071201b00d03006070020201203006))) (.node (.node (.leaf
    0x260000000000020a0060762b01b00f0700e0100d0300607002020010400a0) (.leaf
    0xf100d03006070000000001000000000100000000010000000000080010000)) (.node (.leaf
    0x100100000002d0000010000000000000000020a0060762b01b00f0700e0) (.leaf
    0xf2b01b00f0700e01201b0260762b01b00f07000000000100000000010000)))) (.node (.node (.node
    (.leaf 0x5001000000000100100000002a0000010000000000000010005a006070050) (.leaf 0x5001000))
    (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0)
    (.leaf 0x0)))))) (.node (.node (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf
    0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))
    (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))))) (.node (.node (.node (.node
    (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf
    0x0)) (.node (.leaf 0x0) (.leaf 0x0)))) (.node (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node
    (.leaf 0x0) (.leaf 0x0))) (.node (.node (.leaf 0x0) (.leaf 0x0)) (.node (.leaf 0x0) (.leaf
    0x0)))))))))


/-! ### Bit-Packed Zipper Cache and Bytecode Stream Interpreter -/

noncomputable def zipLookup (id : ℕ) : Option ℕ :=
  zipCache.find? id


theorem zipCache_ok : WordRLE.NatTrie.checkAll checkZipPacked 0 1 zipCache = true := by
  decide +kernel

theorem zipLookup_sound {id p : ℕ} (h : zipLookup id = some p) :
    let e := unpackZip p
    1 ≤ e.steps ∧
      simZipNat e.steps e.qIn e.dirIn e.kL e.lB e.kR e.rB =
        some (e.qOut, e.dirOut, e.kLOut, e.lOut, e.kROut, e.rOut) := by
  unfold zipLookup at h
  have hchk : checkZipPacked id p = true := WordRLE.NatTrie.checkAll_sound zipCache_ok h
  unfold checkZipPacked at hchk
  simp only [Bool.and_eq_true] at hchk
  exact ⟨Nat.le_of_ble_eq_true hchk.1, eq_of_beq hchk.2⟩

noncomputable def stepOp (op : SymOp) (g : SymCfg) : Option SymCfg :=
  match op with
  | .zip id =>
    match zipLookup id with
    | none => none
    | some p =>
      let e := unpackZip p
      if Nat.beq g.q e.qIn && (g.dir == e.dirIn) then
        match popBits (unpackBits e.kL e.lB) g.left, popBits (unpackBits e.kR e.rB) g.right with
        | some lRem, some rRem =>
          some ⟨e.qOut, e.dirOut, true,
            pushBits (unpackBits e.kLOut e.lOut) lRem,
            pushBits (unpackBits e.kROut e.rOut) rRem⟩
        | _, _ => none
      else none
  | .shiftWaL =>
    if !g.dir && Nat.beq g.q 1 then
      match g.left with
      | ⟨2, cnt⟩ :: rest =>
        some ⟨1, false, g.prog || Nat.ble 1 cnt.c0, rest, pushSym 2 cnt g.right⟩
      | _ => none
    else none
  | .shiftWbR =>
    if g.dir && Nat.beq g.q 1 then
      match g.right with
      | ⟨3, cnt⟩ :: rest =>
        some ⟨1, true, g.prog || Nat.ble 1 cnt.c0, pushSym 4 cnt g.left, rest⟩
      | _ => none
    else none
  | .shiftWcL =>
    if !g.dir && Nat.beq g.q 5 then
      match g.left with
      | ⟨4, cnt⟩ :: rest =>
        some ⟨5, false, g.prog || Nat.ble 1 cnt.c0, rest, pushSym 3 cnt g.right⟩
      | _ => none
    else none
  | .shiftWaR0 =>
    if g.dir && Nat.beq g.q 0 then
      match g.right with
      | ⟨2, cnt⟩ :: rest =>
        if peekBit true rest == some 0 then
          some ⟨0, true, g.prog || Nat.ble 1 cnt.c0, pushSym 2 cnt g.left, rest⟩
        else none
      | _ => none
    else none
  | .splitWaLast =>
    if g.dir && Nat.beq g.q 0 then
      match g.right with
      | ⟨2, cnt⟩ :: rest =>
        if Nat.ble 1 cnt.c0 then
          let r' := pushSym 2 cnt.sub1 (pushBits [0, 1, 0] rest)
          some ⟨0, true, g.prog, g.left, r'⟩
        else none
      | _ => none
    else none
  | .bounce =>
    let ac := if g.dir then g.right else g.left
    match peekBit g.dir ac with
    | none => none
    | some b =>
      match stepCode g.q b with
      | some (w, nd, q') =>
        if (w == b) && (nd == !g.dir) then
          some ⟨q', nd, true, g.left, g.right⟩
        else none
      | none => none
  | .unroll =>
    let ac := if g.dir then g.right else g.left
    match ac with
    | ⟨sym, cnt⟩ :: rest =>
      if Nat.ble 2 sym && Nat.ble 1 cnt.c0 then
        let wd := if g.dir then symWord sym else (symWord sym).reverse
        let ac' := pushBits wd (pushSym sym cnt.sub1 rest)
        if g.dir then some ⟨g.q, true, g.prog, g.left, ac'⟩
        else some ⟨g.q, false, g.prog, ac', g.right⟩
      else none
    | [] => none
  | .fold side sym k =>
    let wd := if side then symWord sym else (symWord sym).reverse
    let ac := if side then g.right else g.left
    match popBits (wd ^ k) ac with
    | none => none
    | some rem =>
      let ac' := pushSym sym (Aff3.const k) rem
      if side then some ⟨g.q, g.dir, g.prog, g.left, ac'⟩
      else some ⟨g.q, g.dir, g.prog, ac', g.right⟩

theorem stepOp_sound (op : SymOp) (g g' : SymCfg) (u v w : ℕ)
    (h : stepOp op g = some g') :
    ∃ dp : Bool, g'.prog = (g.prog || dp) ∧
      StepRel dp (evalSymCfg u v w g) (evalSymCfg u v w g') := by
  cases op with
  | zip id =>
    simp only [stepOp] at h
    rcases hz : zipLookup id with _ | p
    · simp [hz] at h
    · rw [hz] at h
      simp only at h
      set e := unpackZip p
      cases hqd : Nat.beq g.q e.qIn && (g.dir == e.dirIn)
      · simp [hqd] at h
      · rw [hqd] at h
        simp only [↓reduceIte] at h
        rcases hpl : popBits (unpackBits e.kL e.lB) g.left with _ | lRem
        · simp [hpl] at h
        · rw [hpl] at h
          rcases hpr : popBits (unpackBits e.kR e.rB) g.right with _ | rRem
          · simp [hpr] at h
          · rw [hpr] at h
            simp only [Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hqd
            have hqEq : g.q = e.qIn := Nat.eq_of_beq_eq_true hqd.1
            have hdEq : g.dir = e.dirIn := eq_of_beq hqd.2
            obtain ⟨hpos, hsim⟩ := zipLookup_sound hz
            refine ⟨true, by simp, ?_⟩
            apply StepRel.of_reachesIn _ (fun _ ↦ hpos)
            simp only [evalSymCfg, hqEq, hdEq,
              popBits_sound false u v w (unpackBits e.kL e.lB) g.left lRem hpl,
              popBits_sound true u v w (unpackBits e.kR e.rB) g.right rRem hpr,
              evalStk_pushBits]
            exact simZipNat_sound e.steps e.qIn e.dirIn e.kL e.lB e.kR e.rB
              e.qOut e.dirOut e.kLOut e.lOut e.kROut e.rOut
              (evalStk false u v w lRem) (evalStk true u v w rRem) hsim
  | shiftWaL =>
    simp only [stepOp] at h
    cases hcond : !g.dir && Nat.beq g.q 1
    · simp [hcond] at h
    · rw [hcond] at h
      simp only [↓reduceIte] at h
      rcases hl : g.left with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hl] at h
      · rw [hl] at h
        match sym with
        | 2 =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          have hq1 : g.q = 1 := Nat.eq_of_beq_eq_true hcond.2
          refine ⟨Nat.ble 1 cnt.c0, rfl, ?_⟩
          have hex := WordRLE.sweepWord_sound exit_waL (cnt.eval u v w)
            (evalStk false u v w rest) (evalStk true u v w g.right)
          simp only [WordRLE.placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            WordRLE.reverse_pow] at hex
          apply StepRel.of_reachesIn
          · simp only [evalSymCfg, hl, hcond.1, hq1, evalStk, Bool.false_eq_true, ↓reduceIte,
              evalStk_pushSym, symWord]
            exact hex
          · intro hp
            have hge := Aff3.ge1_eval hp u v w
            omega
        | 0 | 1 | _ + 3 => simp at h
  | shiftWbR =>
    simp only [stepOp] at h
    cases hcond : g.dir && Nat.beq g.q 1
    · simp [hcond] at h
    · rw [hcond] at h
      simp only [↓reduceIte] at h
      rcases hr : g.right with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hr] at h
      · rw [hr] at h
        match sym with
        | 3 =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hcond
          have hq1 : g.q = 1 := Nat.eq_of_beq_eq_true hcond.2
          refine ⟨Nat.ble 1 cnt.c0, rfl, ?_⟩
          have hex := WordRLE.sweepWord_sound exit_wbR (cnt.eval u v w)
            (evalStk false u v w g.left) (evalStk true u v w rest)
          simp only [WordRLE.placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true,
            WordRLE.reverse_pow] at hex
          apply StepRel.of_reachesIn
          · simp only [evalSymCfg, hr, hcond.1, hq1, evalStk, Bool.false_eq_true, ↓reduceIte,
              evalStk_pushSym, symWord]
            exact hex
          · intro hp
            have hge := Aff3.ge1_eval hp u v w
            omega
        | 0 | 1 | 2 | _ + 4 => simp at h
  | shiftWcL =>
    simp only [stepOp] at h
    cases hcond : !g.dir && Nat.beq g.q 5
    · simp [hcond] at h
    · rw [hcond] at h
      simp only [↓reduceIte] at h
      rcases hl : g.left with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hl] at h
      · rw [hl] at h
        match sym with
        | 4 =>
          simp only [Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcond
          have hq5 : g.q = 5 := Nat.eq_of_beq_eq_true hcond.2
          refine ⟨Nat.ble 1 cnt.c0, rfl, ?_⟩
          have hex := WordRLE.sweepWord_sound exit_wcL (cnt.eval u v w)
            (evalStk false u v w rest) (evalStk true u v w g.right)
          simp only [WordRLE.placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            WordRLE.reverse_pow] at hex
          apply StepRel.of_reachesIn
          · simp only [evalSymCfg, hl, hcond.1, hq5, evalStk, Bool.false_eq_true, ↓reduceIte,
              evalStk_pushSym, symWord]
            exact hex
          · intro hp
            have hge := Aff3.ge1_eval hp u v w
            omega
        | 0 | 1 | 2 | 3 | _ + 5 => simp at h
  | shiftWaR0 =>
    simp only [stepOp] at h
    cases hcond : g.dir && Nat.beq g.q 0
    · simp [hcond] at h
    · rw [hcond] at h
      simp only [↓reduceIte] at h
      rcases hr : g.right with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hr] at h
      · rw [hr] at h
        match sym with
        | 2 =>
          simp only at h
          cases hpk : peekBit true rest == some 0
          · simp [hpk] at h
          · rw [hpk] at h
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hcond
            have hq0 : g.q = 0 := Nat.eq_of_beq_eq_true hcond.2
            obtain ⟨rTail, hrTail⟩ := peekBit_sound true u v w rest 0 (eq_of_beq hpk)
            refine ⟨Nat.ble 1 cnt.c0, rfl, ?_⟩
            apply StepRel.of_reachesIn (dt := 9 * cnt.eval u v w)
            · simp only [evalSymCfg, hr, hcond.1, hq0, evalStk, Bool.false_eq_true, ↓reduceIte,
                evalStk_pushSym, symWord, hrTail]
              exact sweep_waR0_sound (cnt.eval u v w) (evalStk false u v w g.left) rTail
            · intro hp
              have hge := Aff3.ge1_eval hp u v w
              omega
        | 0 | 1 | _ + 3 => simp at h
  | splitWaLast =>
    simp only [stepOp] at h
    cases hcond : g.dir && Nat.beq g.q 0
    · simp [hcond] at h
    · rw [hcond] at h
      simp only [↓reduceIte] at h
      rcases hr : g.right with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hr] at h
      · rw [hr] at h
        match sym with
        | 2 =>
          simp only at h
          cases hc : Nat.ble 1 cnt.c0
          · simp [hc] at h
          · rw [hc] at h
            simp only [↓reduceIte, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hcond
            have hq0 : g.q = 0 := Nat.eq_of_beq_eq_true hcond.2
            refine ⟨false, by simp, ?_⟩
            have heq : evalSymCfg u v w g =
                evalSymCfg u v w
                  ⟨0, true, g.prog, g.left, pushSym 2 cnt.sub1 (pushBits [0, 1, 0] rest)⟩ := by
              simp only [evalSymCfg, hr, hcond.1, hq0, evalStk, ↓reduceIte, evalStk_pushSym,
                evalStk_pushBits, Aff3.sub1_eval hc u v w, symWord]
              rw [list_pow_succ', ListBlank.append_assoc]
            rw [heq]
            exact StepRel.refl _
        | 0 | 1 | _ + 3 => simp at h
  | bounce =>
    simp only [stepOp] at h
    rcases hp : peekBit g.dir (if g.dir then g.right else g.left) with _ | b
    · simp [hp] at h
    · rw [hp] at h
      simp only at h
      rcases hsc : stepCode g.q b with _ | ⟨wb, nd, q'⟩
      · simp [hsc] at h
      · rw [hsc] at h
        simp only at h
        cases hchk : (wb == b) && (nd == !g.dir)
        · simp [hchk] at h
        · rw [hchk] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hchk
          have hwb : wb = b := eq_of_beq hchk.1
          have hnd : nd = !g.dir := eq_of_beq hchk.2
          rw [hwb] at hsc
          subst hnd
          refine ⟨true, by simp, ?_⟩
          cases hd : g.dir
          · rw [hd] at hp hsc
            simp only [Bool.false_eq_true, ↓reduceIte] at hp
            obtain ⟨lTail, hlTail⟩ := peekBit_sound false u v w g.left b hp
            have hst := step_headLeft_right (stepCode_agrees g.q b b true q' hsc)
              lTail (evalStk true u v w g.right)
            rw [← hlTail] at hst
            simp only [evalSymCfg, hd, WordRLE.dirCfg, Bool.false_eq_true, ↓reduceIte,
              Bool.not_false]
            exact ReachesPlus.single hst
          · rw [hd] at hp hsc
            simp only [↓reduceIte] at hp
            obtain ⟨rTail, hrTail⟩ := peekBit_sound true u v w g.right b hp
            have hst := step_headRight_left (stepCode_agrees g.q b b false q' hsc)
              (evalStk false u v w g.left) rTail
            rw [← hrTail] at hst
            simp only [evalSymCfg, hd, WordRLE.dirCfg, Bool.false_eq_true, ↓reduceIte,
              Bool.not_true]
            exact ReachesPlus.single hst
  | unroll =>
    simp only [stepOp] at h
    cases hd : g.dir
    · rw [hd] at h
      simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases hl : g.left with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hl] at h
      · rw [hl] at h
        simp only at h
        cases hc : Nat.ble 2 sym && Nat.ble 1 cnt.c0
        · simp [hc] at h
        · rw [hc] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hc
          refine ⟨false, by simp, ?_⟩
          have heq : evalSymCfg u v w g =
              evalSymCfg u v w
                ⟨g.q, false, g.prog,
                  pushBits (symWord sym).reverse (pushSym sym cnt.sub1 rest), g.right⟩ := by
            simp only [evalSymCfg, hd, hl, evalStk, Bool.false_eq_true, ↓reduceIte,
              evalStk_pushBits, evalStk_pushSym, Aff3.sub1_eval hc.2 u v w]
            rw [ListBlank.append_pow_succ]
          rw [heq]
          exact StepRel.refl _
    · rw [hd] at h
      simp only [↓reduceIte] at h
      rcases hr : g.right with _ | ⟨⟨sym, cnt⟩, rest⟩
      · simp [hr] at h
      · rw [hr] at h
        simp only at h
        cases hc : Nat.ble 2 sym && Nat.ble 1 cnt.c0
        · simp [hc] at h
        · rw [hc] at h
          simp only [↓reduceIte, Option.some.injEq] at h
          subst h
          simp only [Bool.and_eq_true] at hc
          refine ⟨false, by simp, ?_⟩
          have heq : evalSymCfg u v w g =
              evalSymCfg u v w
                ⟨g.q, true, g.prog, g.left,
                  pushBits (symWord sym) (pushSym sym cnt.sub1 rest)⟩ := by
            simp only [evalSymCfg, hd, hr, evalStk, ↓reduceIte,
              evalStk_pushBits, evalStk_pushSym, Aff3.sub1_eval hc.2 u v w]
            rw [ListBlank.append_pow_succ]
          rw [heq]
          exact StepRel.refl _
  | fold side sym k =>
    simp only [stepOp] at h
    cases side
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      rcases hp : popBits ((symWord sym).reverse ^ k) g.left with _ | rem
      · simp [hp] at h
      · rw [hp] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨false, by simp, ?_⟩
        have heq : evalSymCfg u v w g =
            evalSymCfg u v w
              ⟨g.q, g.dir, g.prog, pushSym sym (Aff3.const k) rem, g.right⟩ := by
          simp only [evalSymCfg, popBits_sound false u v w _ g.left rem hp,
            evalStk_pushSym, Bool.false_eq_true, ↓reduceIte, Aff3.const_eval]
        rw [heq]
        exact StepRel.refl _
    · simp only [↓reduceIte] at h
      rcases hp : popBits (symWord sym ^ k) g.right with _ | rem
      · simp [hp] at h
      · rw [hp] at h
        simp only [Option.some.injEq] at h
        subst h
        refine ⟨false, by simp, ?_⟩
        have heq : evalSymCfg u v w g =
            evalSymCfg u v w
              ⟨g.q, g.dir, g.prog, g.left, pushSym sym (Aff3.const k) rem⟩ := by
          simp only [evalSymCfg, popBits_sound true u v w _ g.right rem hp,
            evalStk_pushSym, ↓reduceIte, Aff3.const_eval]
        rw [heq]
        exact StepRel.refl _

def GoodCfg (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m a b c, HubInv m a b c ∧ cfg = evalHub m a b c

structure Frame where
  a : Aff3
  b : Aff3
  c : Aff3
  g : SymCfg

def FrameOk (m : ℕ) (fr : Frame) : Prop :=
  ∀ u v w : ℕ,
    HubInv m (fr.a.eval u v w) (fr.b.eval u v w) (fr.c.eval u v w) →
    ∃ cfg', StepRel (!fr.g.prog) (evalSymCfg u v w fr.g) cfg' ∧ GoodCfg cfg'

def TodoOk (m : ℕ) : List Frame → Prop
  | [] => True
  | fr :: rest => FrameOk m fr ∧ TodoOk m rest

theorem frameOk_of_stepOp {m : ℕ} {op : SymOp} {fr : Frame} {g' : SymCfg}
    (hs : stepOp op fr.g = some g')
    (hnext : FrameOk m ⟨fr.a, fr.b, fr.c, g'⟩) :
    FrameOk m fr := by
  intro u v w hinv
  obtain ⟨dp, hpEq, hstep⟩ := stepOp_sound op fr.g g' u v w hs
  obtain ⟨cfg', hs2, hg2⟩ := hnext u v w hinv
  dsimp only at hs2
  rw [hpEq] at hs2
  exact ⟨cfg', StepRel.chain hstep hs2, hg2⟩

theorem frameOk_of_split {m : ℕ} (sv : Var3) (fr : Frame)
    (h0 : FrameOk m ⟨fr.a.substZero sv, fr.b.substZero sv, fr.c.substZero sv,
      ⟨fr.g.q, fr.g.dir, fr.g.prog, substStk sv false fr.g.left, substStk sv false fr.g.right⟩⟩)
    (h1 : FrameOk m ⟨fr.a.substSucc sv, fr.b.substSucc sv, fr.c.substSucc sv,
      ⟨fr.g.q, fr.g.dir, fr.g.prog, substStk sv true fr.g.left, substStk sv true fr.g.right⟩⟩) :
    FrameOk m fr := by
  intro u v w hinv
  cases sv with
  | va =>
    cases u with
    | zero =>
      rw [← Aff3.substZero_va fr.a v w, ← Aff3.substZero_va fr.b v w,
        ← Aff3.substZero_va fr.c v w] at hinv
      obtain ⟨cfg', hs, hg⟩ := h0 0 v w hinv
      simp only [evalSymCfg, substStk_zero_va] at hs
      exact ⟨cfg', hs, hg⟩
    | succ u' =>
      rw [← Aff3.substSucc_va fr.a u' v w, ← Aff3.substSucc_va fr.b u' v w,
        ← Aff3.substSucc_va fr.c u' v w] at hinv
      obtain ⟨cfg', hs, hg⟩ := h1 u' v w hinv
      simp only [evalSymCfg, substStk_succ_va] at hs
      exact ⟨cfg', hs, hg⟩
  | vb =>
    cases v with
    | zero =>
      rw [← Aff3.substZero_vb fr.a u w, ← Aff3.substZero_vb fr.b u w,
        ← Aff3.substZero_vb fr.c u w] at hinv
      obtain ⟨cfg', hs, hg⟩ := h0 u 0 w hinv
      simp only [evalSymCfg, substStk_zero_vb] at hs
      exact ⟨cfg', hs, hg⟩
    | succ v' =>
      rw [← Aff3.substSucc_vb fr.a u v' w, ← Aff3.substSucc_vb fr.b u v' w,
        ← Aff3.substSucc_vb fr.c u v' w] at hinv
      obtain ⟨cfg', hs, hg⟩ := h1 u v' w hinv
      simp only [evalSymCfg, substStk_succ_vb] at hs
      exact ⟨cfg', hs, hg⟩
  | vc =>
    cases w with
    | zero =>
      rw [← Aff3.substZero_vc fr.a u v, ← Aff3.substZero_vc fr.b u v,
        ← Aff3.substZero_vc fr.c u v] at hinv
      obtain ⟨cfg', hs, hg⟩ := h0 u v 0 hinv
      simp only [evalSymCfg, substStk_zero_vc] at hs
      exact ⟨cfg', hs, hg⟩
    | succ w' =>
      rw [← Aff3.substSucc_vc fr.a u v w', ← Aff3.substSucc_vc fr.b u v w',
        ← Aff3.substSucc_vc fr.c u v w'] at hinv
      obtain ⟨cfg', hs, hg⟩ := h1 u v w' hinv
      simp only [evalSymCfg, substStk_succ_vc] at hs
      exact ⟨cfg', hs, hg⟩

noncomputable def decodeAff (p0 : ℕ) : Aff3 × ℕ :=
  forceNat (p0 % 4096) fun c0 ↦
  forceNat (p0 / 4096) fun p1 ↦
  forceNat (p1 % 4096) fun ca ↦
  forceNat (p1 / 4096) fun p2 ↦
  forceNat (p2 % 4096) fun cb ↦
  forceNat (p2 / 4096) fun p3 ↦
  forceNat (p3 % 4096) fun cc ↦
  forceNat (p3 / 4096) fun p4 ↦
    (⟨c0, ca, cb, cc⟩, p4)

noncomputable def decodeFWit (p0 : ℕ) : FWit × ℕ :=
  forceNat (p0 % 4096) fun k ↦
  forceNat (p0 / 4096) fun p1 ↦
  forceNat (p1 % 4) fun i1 ↦
  forceNat (p1 / 4) fun p2 ↦
  forceNat (p2 % 4096) fun l1 ↦
  forceNat (p2 / 4096) fun p3 ↦
  forceNat (p3 % 4) fun i2 ↦
  forceNat (p3 / 4) fun p4 ↦
  forceNat (p4 % 4096) fun l2 ↦
  forceNat (p4 / 4096) fun p5 ↦
    (⟨k, i1, l1, i2, l2⟩, p5)

def decodeVar : ℕ → Var3
  | 0 => .va
  | 1 => .vb
  | _ => .vc

def decodeUnitOp : ℕ → SymOp
  | 1 => .shiftWaL
  | 2 => .shiftWbR
  | 3 => .shiftWcL
  | 4 => .shiftWaR0
  | 5 => .splitWaLast
  | 6 => .bounce
  | _ => .unroll

noncomputable def decodeFoldOp (arg : ℕ) : SymOp :=
  forceNat (arg % 256) fun fk ↦
  forceNat ((arg / 256) % 8) fun fsym ↦
    .fold (Nat.beq (arg / 2048) 1) fsym fk

noncomputable def checkDoneLeaf (m : ℕ) (fr : Frame) (dm : ℕ) (da db dc : Aff3)
    (w0 w1 w2 : FWit) : Bool :=
  let hs := modeIneqs m fr.a fr.b fr.c
  let dhs := modeIneqs dm da db dc
  Nat.ble (dm + 1) 7 &&
    checkHubEq fr.g dm da db dc &&
    checkFarkas hs dhs.1 w0 &&
    checkFarkas hs dhs.2.1 w1 &&
    checkFarkas hs dhs.2.2 w2

theorem checkDoneLeaf_sound {m : ℕ} (hm : m < 7) {fr : Frame} {dm : ℕ} {da db dc : Aff3}
    {w0 w1 w2 : FWit} (hc : checkDoneLeaf m fr dm da db dc w0 w1 w2 = true) :
    FrameOk m fr := by
  intro u v w hinv
  simp only [checkDoneLeaf, Bool.and_eq_true] at hc
  rcases hc with ⟨⟨⟨⟨hdmLe, hhub⟩, hf0⟩, hf1⟩, hf2⟩
  have hdm : dm < 7 := by
    have := Nat.le_of_ble_eq_true hdmLe
    omega
  obtain ⟨hgProg, hgHub⟩ := checkHubEq_sound hhub u v w
  have hh := (modeIneqs_iff hm fr.a fr.b fr.c u v w).mpr hinv
  have hd0 := checkFarkas_sound hf0 hh
  have hd1 := checkFarkas_sound hf1 hh
  have hd2 := checkFarkas_sound hf2 hh
  have hdInv := (modeIneqs_iff hdm da db dc u v w).mp ⟨hd0, hd1, hd2⟩
  refine ⟨evalHub dm (da.eval u v w) (db.eval u v w) (dc.eval u v w), ?_,
    ⟨dm, da.eval u v w, db.eval u v w, dc.eval u v w, hdInv, rfl⟩⟩
  rw [← hgHub, hgProg]
  exact StepRel.refl _

noncomputable def checkStream (m : ℕ) : ℕ → ℕ → List ℕ → List Frame → Bool
  | _, _, _, [] => true
  | 0, _, _, _ :: _ => false
  | fuel + 1, cur, chunks, fr :: rest =>
    forceNat (cur % 16) fun tag ↦
    forceNat (cur / 16) fun cur1 ↦
    if Nat.beq tag 15 then
      match chunks with
      | [] => false
      | nextW :: chunks' => checkStream m fuel nextW chunks' (fr :: rest)
    else if Nat.beq tag 0 then
      forceNat (cur1 % 4096) fun id ↦
      forceNat (cur1 / 4096) fun cur2 ↦
      match stepOp (.zip id) fr.g with
      | none => false
      | some g' => checkStream m fuel cur2 chunks (⟨fr.a, fr.b, fr.c, g'⟩ :: rest)
    else if Nat.ble tag 7 then
      match stepOp (decodeUnitOp tag) fr.g with
      | none => false
      | some g' => checkStream m fuel cur1 chunks (⟨fr.a, fr.b, fr.c, g'⟩ :: rest)
    else if Nat.beq tag 8 then
      forceNat (cur1 % 4) fun idx ↦
      forceNat (cur1 / 4) fun cur2 ↦
      isDeadIneq (selIneq (modeIneqs m fr.a fr.b fr.c) idx) &&
        checkStream m fuel cur2 chunks rest
    else if Nat.beq tag 9 then
      forceNat (cur1 % 4) fun svCode ↦
      forceNat (cur1 / 4) fun cur2 ↦
      let sv := decodeVar svCode
      let g0 : SymCfg := ⟨fr.g.q, fr.g.dir, fr.g.prog,
        substStk sv false fr.g.left, substStk sv false fr.g.right⟩
      let g1 : SymCfg := ⟨fr.g.q, fr.g.dir, fr.g.prog,
        substStk sv true fr.g.left, substStk sv true fr.g.right⟩
      let fr0 : Frame := ⟨fr.a.substZero sv, fr.b.substZero sv, fr.c.substZero sv, g0⟩
      let fr1 : Frame := ⟨fr.a.substSucc sv, fr.b.substSucc sv, fr.c.substSucc sv, g1⟩
      checkStream m fuel cur2 chunks (fr0 :: fr1 :: rest)
    else if Nat.beq tag 10 then
      forceNat (cur1 % 16) fun dm ↦
      forceNat (cur1 / 16) fun c2 ↦
      let pA := decodeAff c2
      let pB := decodeAff pA.2
      let pC := decodeAff pB.2
      let pW0 := decodeFWit pC.2
      let pW1 := decodeFWit pW0.2
      let pW2 := decodeFWit pW1.2
      checkDoneLeaf m fr dm pA.1 pB.1 pC.1 pW0.1 pW1.1 pW2.1 &&
        checkStream m fuel pW2.2 chunks rest
    else if Nat.beq tag 11 then
      forceNat (cur1 % 4096) fun arg ↦
      forceNat (cur1 / 4096) fun cur2 ↦
      match stepOp (decodeFoldOp arg) fr.g with
      | none => false
      | some g' => checkStream m fuel cur2 chunks (⟨fr.a, fr.b, fr.c, g'⟩ :: rest)
    else
      false

theorem checkStream_sound {m : ℕ} (hm : m < 7) :
    ∀ (fuel cur : ℕ) (chunks : List ℕ) (todo : List Frame),
      checkStream m fuel cur chunks todo = true →
      TodoOk m todo
  | _, _, _, [], _ => trivial
  | 0, _, _, _ :: _, hc => by simp [checkStream] at hc
  | fuel + 1, cur, chunks, fr :: rest, hc => by
    simp only [checkStream, forceNat_eq] at hc
    cases h15 : Nat.beq (cur % 16) 15
    · rw [h15] at hc
      simp only [Bool.false_eq_true, ↓reduceIte] at hc
      cases h0 : Nat.beq (cur % 16) 0
      · rw [h0] at hc
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        cases h7 : Nat.ble (cur % 16) 7
        · rw [h7] at hc
          simp only [Bool.false_eq_true, ↓reduceIte] at hc
          cases h8 : Nat.beq (cur % 16) 8
          · rw [h8] at hc
            simp only [Bool.false_eq_true, ↓reduceIte] at hc
            cases h9 : Nat.beq (cur % 16) 9
            · rw [h9] at hc
              simp only [Bool.false_eq_true, ↓reduceIte] at hc
              cases h10 : Nat.beq (cur % 16) 10
              · rw [h10] at hc
                simp only [Bool.false_eq_true, ↓reduceIte] at hc
                cases h11 : Nat.beq (cur % 16) 11
                · rw [h11] at hc
                  simp at hc
                · rw [h11] at hc
                  simp only [↓reduceIte] at hc
                  rcases hs : stepOp (decodeFoldOp ((cur / 16) % 4096)) fr.g with _ | g'
                  · simp [hs] at hc
                  · rw [hs] at hc
                    have ih := checkStream_sound hm fuel ((cur / 16) / 4096) chunks _ hc
                    exact ⟨frameOk_of_stepOp hs ih.1, ih.2⟩
              · rw [h10] at hc
                simp only [↓reduceIte, Bool.and_eq_true] at hc
                exact ⟨checkDoneLeaf_sound hm hc.1,
                  checkStream_sound hm fuel _ chunks rest hc.2⟩
            · rw [h9] at hc
              simp only [↓reduceIte] at hc
              have ih := checkStream_sound hm fuel ((cur / 16) / 4) chunks _ hc
              exact ⟨frameOk_of_split _ fr ih.1 ih.2.1, ih.2.2⟩
          · rw [h8] at hc
            simp only [↓reduceIte, Bool.and_eq_true] at hc
            refine ⟨fun u v w hinv ↦ ?_,
                checkStream_sound hm fuel ((cur / 16) / 4) chunks rest hc.2⟩
            have hh := (modeIneqs_iff hm fr.a fr.b fr.c u v w).mpr hinv
            exact False.elim (isDeadIneq_sound hc.1 (selIneq_holds hh ((cur / 16) % 4)))
        · rw [h7] at hc
          simp only [↓reduceIte] at hc
          rcases hs : stepOp (decodeUnitOp (cur % 16)) fr.g with _ | g'
          · simp [hs] at hc
          · rw [hs] at hc
            have ih := checkStream_sound hm fuel (cur / 16) chunks _ hc
            exact ⟨frameOk_of_stepOp hs ih.1, ih.2⟩
      · rw [h0] at hc
        simp only [↓reduceIte] at hc
        rcases hs : stepOp (.zip ((cur / 16) % 4096)) fr.g with _ | g'
        · simp [hs] at hc
        · rw [hs] at hc
          have ih := checkStream_sound hm fuel ((cur / 16) / 4096) chunks _ hc
          exact ⟨frameOk_of_stepOp hs ih.1, ih.2⟩
    · rw [h15] at hc
      simp only [↓reduceIte] at hc
      rcases chunks with _ | ⟨nextW, chunks'⟩
      · simp at hc
      · exact checkStream_sound hm fuel nextW chunks' (fr :: rest) hc

def varA : Aff3 := ⟨0, 1, 0, 0⟩
def varB : Aff3 := ⟨0, 0, 1, 0⟩
def varC : Aff3 := ⟨0, 0, 0, 1⟩

def twoPow256 : ℕ :=
  0x10000000000000000000000000000000000000000000000000000000000000000

noncomputable def unpackSuperList : List ℕ → List ℕ
  | lo :: hi :: rest =>
    forceNat (lo + twoPow256 * hi) fun w ↦ w :: unpackSuperList rest
  | [w] => [w]
  | [] => []

noncomputable def checkModeStream (m fuel : ℕ) (tree : WordRLE.BTree ℕ) : Bool :=
  match unpackSuperList tree.toList with
  | [] => false
  | w0 :: ws =>
    checkStream m fuel w0 ws [⟨varA, varB, varC, mkSymCfg m varA varB varC⟩]

theorem modeStream_sound {m fuel : ℕ} (hm : m < 7) {tree : WordRLE.BTree ℕ}
    (hc : checkModeStream m fuel tree = true) {a b c : ℕ} (hinv : HubInv m a b c) :
    ∃ cfg', ReachesPlus target_tm (evalHub m a b c) cfg' ∧ GoodCfg cfg' := by
  unfold checkModeStream at hc
  rcases hlist : unpackSuperList tree.toList with _ | ⟨w0, ws⟩
  · simp [hlist] at hc
  · rw [hlist] at hc
    have htodo := checkStream_sound hm fuel w0 ws _ hc
    have hfr := htodo.1 a b c
    have hva : varA.eval a b c = a := by simp [varA, Aff3.eval]
    have hvb : varB.eval a b c = b := by simp [varB, Aff3.eval]
    have hvc : varC.eval a b c = c := by simp [varC, Aff3.eval]
    rw [hva, hvb, hvc] at hfr
    obtain ⟨cfg', hs, hg⟩ := hfr hinv
    rw [evalSymCfg_mkSymCfg, hva, hvb, hvc] at hs
    exact ⟨cfg', hs, hg⟩

/-! ### Blank-Tape Stem Entry (`init_reaches_entry`, `1,614` Steps) -/

theorem init_zip_ok :
    simZipNat 1614 0 true initKL 0 initKR 0 =
      some (initQOut, initDirOut, initKLOut, initLBOut, initKROut, initRBOut) := by
  decide +kernel

theorem init_hub_ok :
    checkHubEq ⟨initQOut, initDirOut, true,
      pushBits (unpackBits initKLOut initLBOut) [],
      pushBits (unpackBits initKROut initRBOut) []⟩
      0 (Aff3.const 1) (Aff3.const 0) (Aff3.const 7) = true := by
  decide +kernel

theorem init_reaches_entry :
    ReachesStar target_tm (init []) (evalHub 0 1 0 7) ∧ HubInv 0 1 0 7 := by
  refine ⟨?_, by simp [HubInv]⟩
  have hsim := simZipNat_sound 1614 0 true initKL 0 initKR 0
    initQOut initDirOut initKLOut initLBOut initKROut initRBOut
    default default init_zip_ok
  rw [unpackBits_zero_append, unpackBits_zero_append] at hsim
  have hinit : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
      WordRLE.dirCfg qOf 0 true default default := rfl
  rw [← hinit] at hsim
  have hhub := (checkHubEq_sound init_hub_ok 0 0 0).2
  simp only [evalSymCfg, evalStk_pushBits, evalStk, Aff3.const_eval] at hhub
  rw [← hhub]
  exact ⟨1614, hsim⟩

theorem closed_mode0 : checkModeStream 0 fuelMode0 streamMode0 = true := by
  decide +kernel

theorem closed_mode1 : checkModeStream 1 fuelMode1 streamMode1 = true := by
  decide +kernel

theorem closed_mode2 : checkModeStream 2 fuelMode2 streamMode2 = true := by
  decide +kernel

theorem closed_mode3 : checkModeStream 3 fuelMode3 streamMode3 = true := by
  decide +kernel

theorem closed_mode4 : checkModeStream 4 fuelMode4 streamMode4 = true := by
  decide +kernel

theorem closed_mode5 : checkModeStream 5 fuelMode5 streamMode5 = true := by
  decide +kernel

theorem closed_mode6 : checkModeStream 6 fuelMode6 streamMode6 = true := by
  decide +kernel

theorem goodCfg_closed :
    ∀ c, GoodCfg c → ∃ c', ReachesPlus target_tm c c' ∧ GoodCfg c' := by
  intro c ⟨m, a, b, c0, hinv, hEq⟩
  subst hEq
  have hm : m < 7 := hinv.1
  match m with
  | 0 => exact modeStream_sound hm closed_mode0 hinv
  | 1 => exact modeStream_sound hm closed_mode1 hinv
  | 2 => exact modeStream_sound hm closed_mode2 hinv
  | 3 => exact modeStream_sound hm closed_mode3 hinv
  | 4 => exact modeStream_sound hm closed_mode4 hinv
  | 5 => exact modeStream_sound hm closed_mode5 hinv
  | 6 => exact modeStream_sound hm closed_mode6 hinv
  | _ + 7 => omega



public section

theorem is_not_halt : IsNotHalt target := by
  obtain ⟨hreach, hinv0⟩ := init_reaches_entry
  exact IsNotHalt.of_reachesPlus_invariant hreach ⟨0, 1, 0, 7, hinv0, rfl⟩ goodCfg_closed

end

end BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD
