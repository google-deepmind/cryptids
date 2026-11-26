/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge


/-!
# Busy Beaver Machine `1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RC_1RC---_1LD1RE_1LE0LD_1RA0LF_0RC0RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS


abbrev stC : Fin 6 := 2
abbrev stD : Fin 6 := 3
abbrev stE : Fin 6 := 4

def ones : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => 1 :: ones n

def zeros : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => 0 :: zeros n

def oo : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => 1 :: 1 :: oo n

def enc : List ℕ → ListBlank (Fin 2)
  | [] => default
  | n :: L' => ones n +> ((0 : Fin 2) >> enc L')

def CC (s : List ℕ × List ℕ) : Cfg (Fin 2) (Fin 6) :=
  enc s.1 {{stC}}> enc s.2

theorem enc_nil : enc [] = (0 : Fin 2) >> enc [] :=
  (ListBlank.cons_zero_default).symm

theorem oo_shift (n : ℕ) (s : ListBlank (Fin 2)) :
    oo n +> ((1 : Fin 2) >> s) = (1 : Fin 2) >> (oo n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [oo, ListBlank.append_cons, ih]

theorem zeros_shift (n : ℕ) (s : ListBlank (Fin 2)) :
    zeros n +> ((0 : Fin 2) >> s) = (0 : Fin 2) >> (zeros n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [zeros, ListBlank.append_cons, ih]

theorem oo_ones (m p : ℕ) (s : ListBlank (Fin 2)) :
    oo m +> (ones p +> s) = ones (2 * m + p) +> s := by
  induction m with
  | zero =>
    have h0 : 2 * 0 + p = p := by omega
    rw [h0]
    rfl
  | succ m ih =>
    have h1 : 2 * (m + 1) + p = (2 * m + p) + 2 := by omega
    rw [h1]
    simp only [oo, ones, ListBlank.append_cons, ih]

theorem enc_rep0 (k : ℕ) (X : List ℕ) :
    enc (List.replicate k 0 ++ X) = zeros k +> enc X := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [List.replicate_succ, List.cons_append, enc, ones, zeros,
      ListBlank.append_nil, ListBlank.append_cons, ih]

def bump (d : ℕ) : List ℕ → List ℕ
  | [] => [d]
  | t :: L' => (d + t) :: L'

theorem rule1 (L : List ℕ) (r : ListBlank (Fin 2)) :
    (enc L {{stC}}> ((1 : Fin 2) >> (1 : Fin 2) >> r)) [target_tm]⊢⁺ (enc (1 :: L) {{stC}}> r) := by
  dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

theorem rule2 (L : List ℕ) (r : ListBlank (Fin 2)) :
    (enc L {{stC}}> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [target_tm]⊢⁺
      (enc (0 :: bump 2 L) {{stC}}> r) := by
  cases L with
  | nil =>
    dsimp only [bump, enc, ones, ListBlank.append_cons, ListBlank.append_nil]
    rw [ListBlank.cons_zero_default]
    bb_steps
  | cons t L' =>
    have h2 : 2 + t = t + 2 := by omega
    dsimp only [bump]
    rw [h2]
    dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps

theorem rule3 (L : List ℕ) (r : ListBlank (Fin 2)) :
    (enc L {{stC}}> ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> r)) [target_tm]⊢⁺
      (enc (bump 4 L) {{stC}}> r) := by
  cases L with
  | nil =>
    dsimp only [bump, enc, ones, ListBlank.append_cons, ListBlank.append_nil]
    rw [ListBlank.cons_zero_default]
    bb_steps
  | cons t L' =>
    have h4 : 4 + t = t + 4 := by omega
    dsimp only [bump]
    rw [h4]
    dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
    bb_steps

theorem Dsweep (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((ones k +> l) <{{stD}} r) [target_tm]⊢* (l <{{stD}} (zeros k +> r)) := by
  induction k generalizing r with
  | zero =>
    dsimp only [ones, zeros, ListBlank.append_nil]
    bb_refl
  | succ k ih =>
    dsimp only [ones, zeros, ListBlank.append_cons]
    bb_step
    refine ReachesStar.trans (ih ((0 : Fin 2) >> r)) ?_
    rw [zeros_shift]

def pushB (m k p : ℕ) (rest : List ℕ) : List ℕ :=
  match k with
  | 0 => (2 * m + 2 + p) :: rest
  | k' + 1 => (2 * m + 1) :: (List.replicate k' 0 ++ (1 + p) :: rest)

def pushA (m k p : ℕ) (rest : List ℕ) : List ℕ :=
  match k with
  | 0 => (2 * m + 1 + p) :: rest
  | k' + 1 => (2 * m) :: (List.replicate k' 0 ++ (1 + p) :: rest)

theorem ones_2m (m : ℕ) (s : ListBlank (Fin 2)) :
    ones (2 * m) +> s = oo m +> s := by
  have h : 2 * m = 2 * m + 0 := by omega
  rw [h, ← oo_ones m 0 s]
  rfl

theorem ones_2m1 (m : ℕ) (s : ListBlank (Fin 2)) :
    ones (2 * m + 1) +> s = oo m +> ((1 : Fin 2) >> s) := by
  rw [oo_shift]
  dsimp only [ones, ListBlank.append_cons]
  rw [ones_2m]

theorem pushB_ok (m k p : ℕ) (rest : List ℕ) :
    oo m +> ((1 : Fin 2) >> (zeros k +> ((1 : Fin 2) >> (ones p +> ((0 : Fin 2) >> enc rest))))) =
      enc (pushB m k p rest) := by
  cases k with
  | zero =>
    dsimp only [pushB, zeros, ListBlank.append_nil]
    have h : 2 * m + 2 + p = 2 * m + (p + 2) := by omega
    rw [h]
    dsimp only [enc]
    rw [← oo_ones m (p + 2) ((0 : Fin 2) >> enc rest)]
    rfl
  | succ k' =>
    dsimp only [pushB, zeros, ListBlank.append_cons, enc]
    rw [enc_rep0, ones_2m1]
    have h1 : 1 + p = p + 1 := by omega
    rw [h1]
    rfl

theorem pushA_ok (m k p : ℕ) (rest : List ℕ) :
    oo m +> (zeros k +> ((1 : Fin 2) >> (ones p +> ((0 : Fin 2) >> enc rest)))) =
      enc (pushA m k p rest) := by
  cases k with
  | zero =>
    dsimp only [pushA, zeros, ListBlank.append_nil]
    have h : 2 * m + 1 + p = 2 * m + (p + 1) := by omega
    rw [h]
    dsimp only [enc]
    rw [← oo_ones m (p + 1) ((0 : Fin 2) >> enc rest)]
    rfl
  | succ k' =>
    dsimp only [pushA, zeros, ListBlank.append_cons, enc]
    rw [enc_rep0, ones_2m]
    have h1 : 1 + p = p + 1 := by omega
    rw [h1]
    rfl

def turnE (m : ℕ) (L1 : List ℕ) (k p : ℕ) (rest : List ℕ) : List ℕ × List ℕ :=
  match L1 with
  | [] => ([0, 1], pushA m k p rest)
  | 0 :: [] => ([0, 1], pushA m k p rest)
  | 0 :: ns :: L4 => (0 :: (ns + 1) :: L4, pushA m k p rest)
  | 1 :: L' => turnE (m + 1) L' k p rest
  | (a + 2) :: L3 => (1 :: a :: L3, pushB m k p rest)

theorem turnE_ok (L1 : List ℕ) :
    ∀ m k p rest,
      (enc L1 <{{stE}}
        (oo m +> ((1 : Fin 2) >> (zeros k +> ((1 : Fin 2) >> (ones p +> ((0 : Fin 2) >> enc
          rest)))))))
        [target_tm]⊢* CC (turnE m L1 k p rest) := by
  induction L1 with
  | nil =>
    intro m k p rest
    dsimp only [turnE, CC]
    rw [← pushA_ok, oo_shift]
    dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
    rw [ListBlank.cons_zero_default]
    bb_steps
  | cons a L1 ih =>
    intro m k p rest
    rcases a with _ | _ | a
    · cases L1 with
      | nil =>
        dsimp only [turnE, CC]
        rw [← pushA_ok, oo_shift]
        dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
        rw [ListBlank.cons_zero_default]
        bb_steps
      | cons ns L4 =>
        dsimp only [turnE, CC]
        rw [← pushA_ok, oo_shift]
        dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
        bb_steps
    · dsimp only [turnE, enc, ones, ListBlank.append_cons, ListBlank.append_nil]
      rw [oo_shift]
      bb_step
      bb_step
      bb_step
      bb_step
      have hih := ih (m + 1) k p rest
      dsimp only [oo, ListBlank.append_cons] at hih
      rw [oo_shift] at hih
      exact hih
    · dsimp only [turnE, CC]
      rw [← pushB_ok]
      dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
      bb_steps

def top (L : List ℕ) : ℕ × List ℕ :=
  match L with
  | [] => (0, [])
  | x :: L' => (x, L')

theorem top_ok (L : List ℕ) :
    enc L = ones (top L).1 +> ((0 : Fin 2) >> enc (top L).2) := by
  cases L with
  | nil => exact enc_nil
  | cons x L' => rfl

def turn (L R1 : List ℕ) : List ℕ × List ℕ :=
  turnE 0 (top L).2 (top L).1 (top R1).1 (top R1).2

theorem turn_ok (L R1 : List ℕ) :
    (enc L {{stC}}> ((0 : Fin 2) >> enc R1)) [target_tm]⊢⁺ CC (turn L R1) := by
  unfold turn
  have hL := top_ok L
  have hR := top_ok R1
  rcases htopL : top L with ⟨k, L1⟩
  rcases htopR : top R1 with ⟨p, rest⟩
  rw [htopL] at hL
  rw [htopR] at hR
  dsimp only at hL hR ⊢
  rw [hL, hR]
  bb_step
  refine ReachesStar.trans (Dsweep k ((0 : Fin 2) >> enc L1)
    ((1 : Fin 2) >> (ones p +> ((0 : Fin 2) >> enc rest)))) ?_
  bb_step
  have hE := turnE_ok L1 0 k p rest
  dsimp only [oo, ListBlank.append_nil] at hE
  exact hE

def rep1 : ℕ → List ℕ → List ℕ
  | 0, L => L
  | q' + 1, L => 1 :: rep1 q' L

theorem rep1_shift (q : ℕ) (L : List ℕ) :
    rep1 q (1 :: L) = 1 :: rep1 q L := by
  induction q with
  | zero => rfl
  | succ q ih =>
    dsimp only [rep1]
    rw [ih]

theorem read_pairs (q : ℕ) (L : List ℕ) (r : ListBlank (Fin 2)) :
    (enc L {{stC}}> (oo q +> r)) [target_tm]⊢* (enc (rep1 q L) {{stC}}> r) := by
  induction q generalizing L with
  | zero =>
    dsimp only [oo, rep1, ListBlank.append_nil]
    bb_refl
  | succ q ih =>
    dsimp only [oo, ListBlank.append_cons]
    refine ReachesStar.trans (ReachesPlus.to_star (rule1 L (oo q +> r))) ?_
    dsimp only [rep1]
    rw [← rep1_shift]
    exact ih (1 :: L)

theorem turnE_rep (q : ℕ) (L : List ℕ) (m k p : ℕ) (rest : List ℕ) :
    turnE m (rep1 q L) k p rest = turnE (q + m) L k p rest := by
  induction q generalizing m with
  | zero =>
    have h0 : 0 + m = m := by omega
    rw [h0]
    rfl
  | succ q ih =>
    dsimp only [rep1, turnE]
    rw [ih (m + 1)]
    have h1 : q + (m + 1) = (q + 1) + m := by omega
    rw [h1]

theorem tloop (i : ℕ) :
    ∀ a L4 b R,
      (enc (0 :: a :: L4) {{stC}}> enc ((2 * i) :: b :: R)) [target_tm]⊢*
        (enc (0 :: (a + i) :: L4) {{stC}}> enc (0 :: (b + i) :: R)) := by
  induction i with
  | zero =>
    intro a L4 b R
    have h0 : 2 * 0 = 0 := rfl
    rw [h0, Nat.add_zero, Nat.add_zero]
  | succ i ih =>
    intro a L4 b R
    change (enc (0 :: a :: L4) {{stC}}> (ones (2 * (i + 1)) +> ((0 : Fin 2) >> enc (b :: R))))
      [target_tm]⊢* _
    rw [ones_2m (i + 1)]
    refine ReachesStar.trans (read_pairs (i + 1) (0 :: a :: L4) ((0 : Fin 2) >> enc (b :: R))) ?_
    refine ReachesStar.trans (ReachesPlus.to_star (turn_ok (rep1 (i + 1) (0 :: a :: L4)) (b ::
      R))) ?_
    unfold turn CC
    dsimp only [rep1, top]
    rw [turnE_rep i (0 :: a :: L4) 0 1 b R]
    have hi0 : i + 0 = i := by omega
    rw [hi0]
    dsimp only [turnE, pushA, List.replicate, List.nil_append]
    have h1b : 1 + b = b + 1 := by omega
    rw [h1b]
    have ha : a + (i + 1) = (a + 1) + i := by omega
    have hb : b + (i + 1) = (b + 1) + i := by omega
    rw [ha, hb]
    exact ih (a + 1) L4 (b + 1) R

def pushC (m k p : ℕ) (rest : List ℕ) : List ℕ :=
  match k with
  | 0 => []
  | 1 => (3 + p + m) :: rest
  | k' + 2 => (2 + m) :: (List.replicate k' 0 ++ (1 + p) :: rest)

def Aout (m ns : ℕ) (L4 : List ℕ) (k p : ℕ) (rest : List ℕ) : Option (List ℕ × List ℕ) :=
  match k with
  | 0 => none
  | _ + 1 =>
    match ns + m with
    | 0 => none
    | t + 1 => some (1 :: t :: L4, pushC m k p rest)

theorem uturn (a' : ℕ) (L4 : List ℕ) (b : ℕ) (R : List ℕ) :
    (enc (0 :: (a' + 2) :: L4) {{stC}}> enc (0 :: b :: R)) [target_tm]⊢⁺
      (enc (1 :: a' :: L4) {{stC}}> enc ((2 + b) :: R)) := by
  have h := turn_ok (0 :: (a' + 2) :: L4) (b :: R)
  unfold turn CC at h
  dsimp only [top, turnE, pushB] at h
  have h2 : 2 * 0 + 2 + b = 2 + b := by omega
  rw [h2] at h
  exact h

theorem Aout_ok (m ns : ℕ) (L4 : List ℕ) (k p : ℕ) (rest : List ℕ) (s' : List ℕ × List ℕ)
    (h : Aout m ns L4 k p rest = some s') :
    (CC (0 :: (ns + 1) :: L4, pushA m k p rest)) [target_tm]⊢⁺ (CC s') := by
  unfold Aout at h
  cases k with
  | zero => cases h
  | succ k =>
    rcases hnm : ns + m with _ | t
    · rw [hnm] at h; cases h
    · rw [hnm] at h
      injection h with hs'
      subst hs'
      unfold CC
      dsimp only
      have ht : (ns + 1) + m = t + 2 := by omega
      cases k with
      | zero =>
        dsimp only [pushA, pushC, List.replicate, List.nil_append]
        refine ReachesStar.trans_plus (tloop m (ns + 1) L4 (1 + p) rest) ?_
        rw [ht]
        have hp : 2 + ((1 + p) + m) = 3 + p + m := by omega
        rw [← hp]
        exact uturn t L4 ((1 + p) + m) rest
      | succ k' =>
        dsimp only [pushA, pushC, List.replicate, List.cons_append]
        refine ReachesStar.trans_plus
          (tloop m (ns + 1) L4 0 (List.replicate k' 0 ++ (1 + p) :: rest)) ?_
        rw [ht, Nat.zero_add]
        exact uturn t L4 m (List.replicate k' 0 ++ (1 + p) :: rest)

def mturnE (m : ℕ) (L1 : List ℕ) (k p : ℕ) (rest : List ℕ) : Option (List ℕ × List ℕ) :=
  match L1 with
  | [] => Aout m 0 [] k p rest
  | 0 :: [] => Aout m 0 [] k p rest
  | 0 :: ns :: L4 => Aout m ns L4 k p rest
  | 1 :: L' => mturnE (m + 1) L' k p rest
  | (a + 2) :: L3 => some (1 :: a :: L3, pushB m k p rest)

theorem mturnE_ok (L1 : List ℕ) :
    ∀ m k p rest s',
      mturnE m L1 k p rest = some s' →
      (CC (turnE m L1 k p rest)) [target_tm]⊢* (CC s') := by
  induction L1 with
  | nil =>
    intro m k p rest s' h
    exact ReachesPlus.to_star (Aout_ok m 0 [] k p rest s' h)
  | cons a L1 ih =>
    intro m k p rest s' h
    rcases a with _ | _ | a
    · cases L1 with
      | nil => exact ReachesPlus.to_star (Aout_ok m 0 [] k p rest s' h)
      | cons ns L4 => exact ReachesPlus.to_star (Aout_ok m ns L4 k p rest s' h)
    · dsimp only [mturnE] at h
      dsimp only [turnE]
      exact ih (m + 1) k p rest s' h
    · dsimp only [mturnE] at h
      injection h with hs'
      subst hs'
      dsimp only [turnE]
      exact ReachesStar.refl _ _

def mturn (L R1 : List ℕ) : Option (List ℕ × List ℕ) :=
  mturnE 0 (top L).2 (top L).1 (top R1).1 (top R1).2

theorem mturn_ok (L R1 : List ℕ) (s' : List ℕ × List ℕ) (h : mturn L R1 = some s') :
    (enc L {{stC}}> ((0 : Fin 2) >> enc R1)) [target_tm]⊢⁺ (CC s') :=
  ReachesPlus.trans_star (turn_ok L R1) (mturnE_ok (top L).2 0 (top L).1 (top R1).1 (top R1).2 s' h)

def mone (L R1 : List ℕ) : Option (List ℕ × List ℕ) :=
  match R1 with
  | [] => mturn (bump 4 L) []
  | (p2 + 1) :: R2 => some (0 :: bump 2 L, p2 :: R2)
  | 0 :: 0 :: 0 :: R4 => mturn (bump 4 L) R4
  | 0 :: 0 :: (p4 + 1) :: R4 => some (bump 4 L, (p4 + 1) :: R4)
  | _ => none

theorem mone_ok (L R1 : List ℕ) (s' : List ℕ × List ℕ) (h : mone L R1 = some s') :
    (enc L {{stC}}> ((1 : Fin 2) >> (0 : Fin 2) >> enc R1)) [target_tm]⊢⁺ (CC s') := by
  cases R1 with
  | nil =>
    dsimp only [mone] at h
    have he : enc [] = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> enc [] := by
      dsimp only [enc]
      simp only [ListBlank.cons_zero_default]
    rw [he]
    exact ReachesPlus.trans (rule3 L ((0 : Fin 2) >> enc [])) (mturn_ok (bump 4 L) [] s' h)
  | cons p2 R2 =>
    cases p2 with
    | succ p2 =>
      dsimp only [mone] at h
      injection h with hs'
      subst hs'
      dsimp only [enc, ones, ListBlank.append_cons]
      exact rule2 L (ones p2 +> ((0 : Fin 2) >> enc R2))
    | zero =>
      cases R2 with
      | nil => cases h
      | cons p3 R3 =>
        cases p3 with
        | succ _ => cases h
        | zero =>
          cases R3 with
          | nil => cases h
          | cons p4 R4 =>
            cases p4 with
            | zero =>
              dsimp only [mone] at h
              dsimp only [enc, ones, ListBlank.append_nil]
              exact ReachesPlus.trans (rule3 L ((0 : Fin 2) >> enc R4))
                (mturn_ok (bump 4 L) R4 s' h)
            | succ p4 =>
              dsimp only [mone] at h
              injection h with hs'
              subst hs'
              dsimp only [enc, ones, ListBlank.append_nil]
              exact rule3 L (enc ((p4 + 1) :: R4))

def mread : ℕ → List ℕ → List ℕ → Option (List ℕ × List ℕ)
  | 0, L, R1 => mturn L R1
  | 1, L, R1 => mone L R1
  | z' + 2, L, R1 => mread z' (1 :: L) R1

theorem mread_ok :
    ∀ (z : ℕ) (L R1 : List ℕ) (s' : List ℕ × List ℕ),
      mread z L R1 = some s' →
      (enc L {{stC}}> enc (z :: R1)) [target_tm]⊢⁺ (CC s')
  | 0, L, R1, s', h => mturn_ok L R1 s' h
  | 1, L, R1, s', h => mone_ok L R1 s' h
  | z + 2, L, R1, s', h => by
      dsimp only [enc, ones, ListBlank.append_cons]
      exact ReachesPlus.trans (rule1 L (enc (z :: R1))) (mread_ok z (1 :: L) R1 s' h)

def mstep (s : List ℕ × List ℕ) : Option (List ℕ × List ℕ) :=
  match s.2 with
  | [] => none
  | z :: R1 => mread z s.1 R1

theorem mstep_ok (s s' : List ℕ × List ℕ) (h : mstep s = some s') :
    (CC s) [target_tm]⊢⁺ (CC s') := by
  rcases s with ⟨L, _ | ⟨z, R1⟩⟩
  · cases h
  · exact mread_ok z L R1 s' h

-- Invariant definitions and closure
def zf : List ℕ → Prop
  | [] => True
  | w :: W' => 1 ≤ w ∧ zf W'

def nth0 : ℕ → List ℕ → ℕ
  | _, [] => 0
  | 0, x :: _ => x
  | n + 1, _ :: xs => nth0 n xs

theorem nth0_nil (n : ℕ) : nth0 n [] = 0 := by cases n <;> rfl
theorem nth0_zero_cons (x : ℕ) (xs : List ℕ) : nth0 0 (x :: xs) = x := rfl
theorem nth0_succ_cons (n x : ℕ) (xs : List ℕ) : nth0 (n + 1) (x :: xs) = nth0 n xs := rfl

def Zr (x y u : ℕ) : Prop :=
  x % 2 = 0 → 2 ≤ y ∧ (y % 2 = 0 → 2 ≤ u)

def Tr (a y u : ℕ) : Prop :=
  2 ≤ a ∧ Zr a y u ∧ (a = 3 → ¬ (y = 0 ∧ u = 0))

def S3e (x y q : ℕ) (W : List ℕ) : Prop :=
  match q with
  | 0 => 1 ≤ x ∧ (x = 1 → 2 ≤ y)
  | 1 => 1 ≤ x ∧ (x = 1 → W ≠ [1])
  | _ + 2 => 2 ≤ x

inductive TR : ℕ → List ℕ → Prop where
  | T1 : ∀ p W, zf W → TR p W
  | T2 : ∀ W, W ≠ [] → zf W → TR 0 (0 :: W)
  | T3 : ∀ W, W ≠ [] → zf W → TR 0 (0 :: 0 :: W)

inductive Hub (x y u : ℕ) : ℕ → List ℕ → Prop where
  | H0 : ∀ z W, 1 ≤ z → zf W →
      (z = 1 → x ≠ 0 ∧ W ≠ []) →
      (z = 2 → x % 2 = 0 → 2 ≤ y) →
      (W = [] → z = 5 → ¬ (x = 0 ∧ y = 0)) →
      (W = [] → z = 3 → ¬ (x = 1 ∧ y = 0 ∧ u = 0)) →
      Hub x y u z W
  | H1 : ∀ z q W, z = 2 * (q + 1) → W ≠ [] → zf W → Hub x y u z (0 :: W)
  | H2e : ∀ z q W, z = 2 * (q + 1) → W ≠ [] → zf W → 2 ≤ x → Hub x y u z (0 :: 0 :: W)
  | H2o : ∀ z q W, z = 2 * q + 1 → W ≠ [] → zf W → W ≠ [1] → Hub x y u z (0 :: 0 :: W)
  | H3e : ∀ z q W, z = 2 * (q + 1) → W ≠ [] → zf W → S3e x y q W → Hub x y u z (0 :: 0 :: 0 :: W)
  | H3o : ∀ z q W, z = 2 * q + 1 → W ≠ [] → zf W → (q = 0 → Zr x y u) → Hub x y u z (0 :: 0 :: 0
    :: W)
  | H4 : ∀ z q W, z = 2 * q + 1 → W ≠ [] → zf W → (q = 0 → Zr x y u) → Hub x y u z (0 :: 0 :: 0 ::
    0 :: W)
  | HP : ∀ z q W, z = 2 * (q + 1) + 1 → W ≠ [] → zf W → Hub x y u z (1 :: 0 :: 0 :: W)
  | HQ : ∀ z q W, z = 2 * (q + 1) + 1 → W ≠ [] → zf W → Hub x y u z (1 :: 0 :: W)

def Inv (s : List ℕ × List ℕ) : Prop :=
  match s with
  | (0 :: a :: L2, p :: W) => Tr a (nth0 0 L2) (nth0 1 L2) ∧ TR p W
  | (1 :: L1, z :: R1) => Hub (nth0 0 L1) (nth0 1 L1) (nth0 2 L1) z R1
  | (5 :: _, w :: W) => zf (w :: W) ∧ w :: W ≠ [1]
  | _ => False

def OK (o : Option (List ℕ × List ℕ)) : Prop :=
  ∃ s', o = some s' ∧ Inv s'

theorem mread_even (q : ℕ) (L R1 : List ℕ) :
    mread (2 * q) L R1 = mturn (rep1 q L) R1 := by
  induction q generalizing L with
  | zero => rfl
  | succ q ih =>
    have h : 2 * (q + 1) = 2 * q + 2 := by omega
    rw [h]
    dsimp only [mread]
    rw [ih (1 :: L), rep1_shift]
    rfl

theorem mread_odd (q : ℕ) (L R1 : List ℕ) :
    mread (2 * q + 1) L R1 = mone (rep1 q L) R1 := by
  induction q generalizing L with
  | zero => rfl
  | succ q ih =>
    have h : 2 * (q + 1) + 1 = (2 * q + 1) + 2 := by omega
    rw [h]
    dsimp only [mread]
    rw [ih (1 :: L), rep1_shift]
    rfl

theorem mturnE_rep (q : ℕ) (L : List ℕ) (m k p : ℕ) (rest : List ℕ) :
    mturnE m (rep1 q L) k p rest = mturnE (q + m) L k p rest := by
  induction q generalizing m with
  | zero =>
    have h0 : 0 + m = m := by omega
    rw [h0]
    rfl
  | succ q ih =>
    dsimp only [rep1, mturnE]
    rw [ih (m + 1)]
    have h1 : q + (m + 1) = (q + 1) + m := by omega
    rw [h1]

theorem Aout_S (m ns : ℕ) (L4 : List ℕ) (k p : ℕ) (rest : List ℕ) (t : ℕ)
    (he : ns + m = t + 1) :
    Aout m ns L4 (k + 1) p rest = some (1 :: t :: L4, pushC m (k + 1) p rest) := by
  unfold Aout
  rw [he]

theorem tg (P : Option (List ℕ × List ℕ) → Prop) (k p : ℕ) (rest L1 : List ℕ) :
    ∀ m,
      (∀ i a L3, P (some (1 :: a :: L3, pushB (i + m) k p rest))) →
      (∀ i L4, (∀ j, j < i → nth0 j L1 = 1) → nth0 i L1 = 0 →
        P (Aout (i + m) (nth0 (i + 1) L1) L4 k p rest)) →
      P (mturnE m L1 k p rest) := by
  induction L1 with
  | nil =>
    intro m _ hA
    have h0 := hA 0 [] (fun _ hlt => by omega) rfl
    simpa only [Nat.zero_add, nth0_nil, nth0_zero_cons, nth0_succ_cons, mturnE] using h0
  | cons a L1 ih =>
    intro m hB hA
    rcases a with _ | _ | a
    · cases L1 with
      | nil =>
        have h0 := hA 0 [] (fun _ hlt => by omega) rfl
        simpa only [Nat.zero_add, nth0_nil, nth0_zero_cons, nth0_succ_cons, mturnE] using h0
      | cons ns L4 =>
        have h0 := hA 0 L4 (fun _ hlt => by omega) rfl
        simpa only [Nat.zero_add, nth0_nil, nth0_zero_cons, nth0_succ_cons, mturnE] using h0
    · dsimp only [mturnE]
      refine ih (m + 1) ?_ ?_
      · intro i a' L3
        have him : i + (m + 1) = (i + 1) + m := by omega
        rw [him]
        exact hB (i + 1) a' L3
      · intro i L4 hj hz
        have him : i + (m + 1) = (i + 1) + m := by omega
        rw [him]
        refine hA (i + 1) L4 ?_ hz
        intro j hlt
        cases j with
        | zero => rfl
        | succ j => exact hj j (by omega)
    · have h0 := hB 0 a L1
      simpa only [Nat.zero_add, mturnE] using h0

theorem k5_gen (L1 : List ℕ) (m p : ℕ) (rest : List ℕ)
    (hm : 1 ≤ m) (hrest : zf rest) (hne : (1 + p) :: rest ≠ [1]) :
    OK (mturnE m L1 5 p rest) := by
  refine tg OK 5 p rest L1 m ?_ ?_
  · intro i a L3
    refine ⟨_, rfl, ?_⟩
    simp only [Inv, pushB, List.replicate, List.cons_append, List.nil_append, nth0_nil,
      nth0_zero_cons, nth0_succ_cons]
    exact Hub.H4 _ (i + m) _ rfl (by simp) ⟨by omega, hrest⟩ (fun hq => by omega)
  · intro i L4 _ _
    generalize nth0 (i + 1) L1 = ns
    have het : ns + (i + m) = (ns + (i + m) - 1) + 1 := by omega
    rw [Aout_S _ _ _ 4 _ _ _ het]
    refine ⟨_, rfl, ?_⟩
    simp only [Inv, pushC, List.replicate, List.cons_append, List.nil_append, nth0_nil,
      nth0_zero_cons, nth0_succ_cons]
    rcases nat_even_or_odd_two_mul (i + m) with ⟨e, he⟩ | ⟨e, he⟩
    · refine Hub.H3e _ e _ (by omega) (by simp) ⟨by omega, hrest⟩ ?_
      rcases e with _ | _ | e
      · omega
      · dsimp only [S3e]
        exact ⟨by omega, fun _ => hne⟩
      · dsimp only [S3e]
        omega
    · exact Hub.H3o _ (e + 1) _ (by omega) (by simp) ⟨by omega, hrest⟩ (fun hq => by omega)

theorem k1_gen (L1 : List ℕ) (m p : ℕ) (rest : List ℕ)
    (hm : 1 ≤ m) (hrest : zf rest)
    (hr : m = 1 → nth0 0 L1 = 0 → nth0 1 L1 = 0 → rest ≠ [] ∨ p ≠ 1) :
    OK (mturnE m L1 1 p rest) := by
  refine tg OK 1 p rest L1 m ?_ ?_
  · intro i a L3
    refine ⟨_, rfl, ?_⟩
    simp only [Inv, pushB, List.replicate, List.nil_append, nth0_nil, nth0_zero_cons,
      nth0_succ_cons]
    exact Hub.H0 _ _ (by omega) ⟨by omega, hrest⟩
      (fun h1 => by omega) (fun h2 => by omega) (fun hnil => by simp at hnil) (fun hnil => by simp
        at hnil)
  · intro i L4 _ hz
    generalize hns : nth0 (i + 1) L1 = ns
    have het : ns + (i + m) = (ns + (i + m) - 1) + 1 := by omega
    rw [Aout_S _ _ _ 0 _ _ _ het]
    refine ⟨_, rfl, ?_⟩
    simp only [Inv, pushC, nth0_nil, nth0_zero_cons, nth0_succ_cons]
    refine Hub.H0 _ _ (by omega) hrest (fun h1 => by omega) (fun h2 => by omega) ?_ (fun _ h3 =>
      by omega)
    intro hrest0 h5 ⟨hx0, _⟩
    have hi0 : i = 0 := by omega
    have hm1 : m = 1 := by omega
    have hns0 : ns = 0 := by omega
    have hp1 : p = 1 := by omega
    subst hi0 hm1 hp1 hns0 hrest0
    have h10 : nth0 1 L1 = 0 := by simpa only [Nat.zero_add] using hns
    rcases hr rfl hz h10 with hc | hc
    · exact hc rfl
    · exact hc rfl

theorem k5_zero (L1 : List ℕ) (p : ℕ) (rest : List ℕ)
    (hrest : zf rest) (hne : (1 + p) :: rest ≠ [1])
    (hz : Zr (nth0 0 L1) (nth0 1 L1) (nth0 2 L1)) :
    OK (mturnE 0 L1 5 p rest) := by
  cases L1 with
  | nil =>
    simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons, Zr] at hz
    have hy := (hz trivial).1
    omega
  | cons a L1 =>
    rcases a with _ | _ | a
    · simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons, Zr] at hz
      obtain ⟨hy, hu⟩ := hz trivial
      cases L1 with
      | nil =>
        simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy
        omega
      | cons ns L4 =>
        simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy hu
        dsimp only [mturnE]
        have het : ns + 0 = (ns - 1) + 1 := by omega
        rw [Aout_S 0 ns L4 4 p rest (ns - 1) het]
        refine ⟨_, rfl, ?_⟩
        simp only [Inv, pushC, List.replicate, List.cons_append, List.nil_append, nth0_nil,
          nth0_zero_cons, nth0_succ_cons]
        refine Hub.H3e _ 0 _ rfl (by simp) ⟨by omega, hrest⟩ ?_
        dsimp only [S3e]
        refine ⟨by omega, fun hx => ?_⟩
        have hns2 : ns = 2 := by omega
        subst hns2
        exact hu rfl
    · dsimp only [mturnE]
      exact k5_gen L1 1 p rest (by omega) hrest hne
    · refine ⟨_, rfl, ?_⟩
      simp only [mturnE, Inv, pushB, List.replicate, List.cons_append, List.nil_append, nth0_nil,
        nth0_zero_cons, nth0_succ_cons]
      refine Hub.H4 _ 0 _ rfl (by simp) ⟨by omega, hrest⟩ (fun _ => ?_)
      simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons, Zr] at hz ⊢
      intro hev
      exact hz (by omega)

theorem inv_t5 (L2 : List ℕ) (w : ℕ) (W : List ℕ)
    (hz : zf (w :: W)) (hne : w :: W ≠ [1]) :
    OK (mstep (5 :: L2, w :: W)) := by
  obtain ⟨hw, hW⟩ := hz
  unfold mstep
  dsimp only
  rcases nat_even_or_odd_two_mul w with ⟨q, rfl⟩ | ⟨q, rfl⟩
  · cases q with
    | zero => omega
    | succ q =>
      rw [mread_even]
      unfold mturn
      have hrep : rep1 (q + 1) (5 :: L2) = 1 :: rep1 q (5 :: L2) := rfl
      rw [hrep]
      dsimp only [top]
      rw [mturnE_rep]
      cases W with
      | nil =>
        refine ⟨_, rfl, ?_⟩
        simp only [mturnE, top, Inv, pushB, List.replicate, List.nil_append, nth0_nil,
          nth0_zero_cons, nth0_succ_cons]
        exact Hub.H0 _ _ (by omega) ⟨by omega, trivial⟩
          (fun _ => ⟨by omega, by simp⟩) (fun h2 => by omega)
          (fun hnil => by simp at hnil) (fun hnil => by simp at hnil)
      | cons p rest =>
        obtain ⟨hp, hrest⟩ := hW
        refine ⟨_, rfl, ?_⟩
        simp only [mturnE, top, Inv, pushB, List.replicate, List.nil_append, nth0_nil,
          nth0_zero_cons, nth0_succ_cons]
        exact Hub.H0 _ _ (by omega) ⟨by omega, hrest⟩
          (fun _ => ⟨by omega, by simp⟩) (fun h2 => by omega)
          (fun hnil => by simp at hnil) (fun hnil => by simp at hnil)
  · rw [mread_odd]
    cases W with
    | nil =>
      cases q with
      | zero => exact False.elim (hne rfl)
      | succ q =>
        unfold mone mturn
        have hrep : rep1 (q + 1) (5 :: L2) = 1 :: rep1 q (5 :: L2) := rfl
        rw [hrep]
        dsimp only [bump, top]
        have h41 : 4 + 1 = 5 := rfl
        rw [h41, mturnE_rep]
        refine ⟨_, rfl, ?_⟩
        simp only [mturnE, Inv, pushB, List.replicate, List.cons_append, List.nil_append,
          nth0_nil, nth0_zero_cons, nth0_succ_cons]
        exact Hub.H4 _ (q + 0) _ (by omega) (by simp) ⟨by omega, trivial⟩ (fun _ hev => by omega)
    | cons p rest =>
      obtain ⟨hp, hrest⟩ := hW
      cases p with
      | zero => omega
      | succ p =>
        refine ⟨_, rfl, ?_⟩
        cases q with
        | zero =>
          simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
          exact ⟨⟨by omega, fun hev => by omega, fun h3 => by omega⟩, TR.T1 p rest hrest⟩
        | succ q =>
          simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
          refine ⟨⟨by omega, fun hev => by omega, fun _ ⟨hy, _⟩ => ?_⟩, TR.T1 p rest hrest⟩
          cases q <;> simp only [rep1, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy <;> omega

theorem inv_t0 (a : ℕ) (L2 : List ℕ) (p : ℕ) (W : List ℕ)
    (ht : Tr a (nth0 0 L2) (nth0 1 L2)) (hr : TR p W) :
    OK (mstep (0 :: a :: L2, p :: W)) := by
  obtain ⟨ha, hz, h3⟩ := ht
  rcases a with _ | _ | a
  · omega
  · omega
  · unfold mstep
    dsimp only
    have hz' : Zr a (nth0 0 L2) (nth0 1 L2) := by
      intro hev
      exact hz (by omega)
    cases hr with
    | T1 p W hW =>
      rcases nat_even_or_odd_two_mul p with ⟨q, rfl⟩ | ⟨q, rfl⟩
      · cases q with
        | zero =>
          cases W with
          | nil =>
            refine ⟨_, rfl, ?_⟩
            simp only [mread, mturn, top, mturnE, Inv, pushB, nth0_nil, nth0_zero_cons,
              nth0_succ_cons]
            exact Hub.H0 _ _ (by omega) trivial
              (fun h1 => by omega) (fun _ hev => (hz' hev).1)
              (fun _ h5 => by omega) (fun _ h3' => by omega)
          | cons p2 rest =>
            obtain ⟨hp, hrest⟩ := hW
            refine ⟨_, rfl, ?_⟩
            simp only [mread, mturn, top, mturnE, Inv, pushB, nth0_nil, nth0_zero_cons,
              nth0_succ_cons]
            refine Hub.H0 _ _ (by omega) hrest
              (fun h1 => by omega) (fun h2 => by omega)
              (fun _ _ ⟨hx0, hy0⟩ => ?_) (fun _ _ ⟨hx1, hy0, hu0⟩ => ?_)
            · subst hx0
              have hy2 := (hz' rfl).1
              omega
            · subst hx1
              exact h3 rfl ⟨hy0, hu0⟩
        | succ q =>
          rw [mread_even]
          unfold mturn
          have hrep : rep1 (q + 1) (0 :: (a + 2) :: L2) = 1 :: rep1 q (0 :: (a + 2) :: L2) := rfl
          rw [hrep]
          dsimp only [top]
          rw [mturnE_rep]
          cases W with
          | nil =>
            dsimp only [top, mturnE]
            have het : (a + 2) + (q + 0) = ((a + 1) + (q + 0)) + 1 := by omega
            rw [Aout_S _ _ _ 0 _ _ _ het]
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushC, nth0_nil, nth0_zero_cons, nth0_succ_cons]
            refine Hub.H0 _ _ (by omega) trivial
              (fun h1 => by omega) (fun h2 => by omega)
              (fun _ h5 ⟨hx0, _⟩ => by omega) (fun _ h3' ⟨hx1, hy0, _⟩ => ?_)
            have ha0 : a = 0 := by omega
            subst ha0
            have hy2 := (hz' rfl).1
            omega
          | cons p2 rest =>
            obtain ⟨hp, hrest⟩ := hW
            dsimp only [top, mturnE]
            have het : (a + 2) + (q + 0) = ((a + 1) + (q + 0)) + 1 := by omega
            rw [Aout_S _ _ _ 0 _ _ _ het]
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushC, nth0_nil, nth0_zero_cons, nth0_succ_cons]
            exact Hub.H0 _ _ (by omega) hrest
              (fun h1 => by omega) (fun h2 => by omega)
              (fun _ _ ⟨hx0, _⟩ => by omega) (fun _ h3' => by omega)
      · rw [mread_odd]
        cases W with
        | nil =>
          unfold mone mturn
          cases q with
          | zero =>
            refine ⟨_, rfl, ?_⟩
            dsimp only [rep1, bump, top, mturnE, Inv, pushB,
              List.replicate, List.cons_append, List.nil_append, nth0_nil, nth0_zero_cons,
                nth0_succ_cons]
            exact Hub.H3o _ 0 _ rfl (by simp) ⟨by omega, trivial⟩ (fun _ => hz')
          | succ q =>
            have hrep : rep1 (q + 1) (0 :: (a + 2) :: L2) = 1 :: rep1 q (0 :: (a + 2) :: L2) := rfl
            rw [hrep]
            dsimp only [bump, top]
            have h41 : 4 + 1 = 5 := rfl
            rw [h41, mturnE_rep]
            dsimp only [mturnE]
            have het : (a + 2) + (q + 0) = ((a + 1) + (q + 0)) + 1 := by omega
            rw [Aout_S _ _ _ 4 _ _ _ het]
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushC, List.replicate, List.cons_append, List.nil_append, nth0_nil,
              nth0_zero_cons, nth0_succ_cons]
            rcases nat_even_or_odd_two_mul (q + 0) with ⟨e, he⟩ | ⟨e, he⟩
            · refine Hub.H3e _ e _ (by omega) (by simp) ⟨by omega, trivial⟩ ?_
              rcases e with _ | _ | e
              · dsimp only [S3e]
                refine ⟨by omega, fun hx => ?_⟩
                have ha0 : a = 0 := by omega
                subst ha0
                exact (hz' rfl).1
              · dsimp only [S3e]
                exact ⟨by omega, fun hx => by omega⟩
              · dsimp only [S3e]
                omega
            · exact Hub.H3o _ (e + 1) _ (by omega) (by simp) ⟨by omega, trivial⟩ (fun hq => by
                omega)
        | cons p2 rest =>
          obtain ⟨hp, hrest⟩ := hW
          cases p2 with
          | zero => omega
          | succ p2 =>
            refine ⟨_, rfl, ?_⟩
            cases q with
            | zero =>
              simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
              refine ⟨⟨by omega, fun _ => ⟨by omega, fun hev => (hz' (by omega)).1⟩,
                fun h3' => by omega⟩, TR.T1 p2 rest hrest⟩
            | succ q =>
              simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
              refine ⟨⟨by omega, fun hev => by omega, fun _ ⟨hy, hu⟩ => ?_⟩, TR.T1 p2 rest hrest⟩
              cases q <;> simp only [rep1, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy hu <;>
                omega
    | T2 W hn hW =>
      cases W with
      | nil => exact False.elim (hn rfl)
      | cons w W' =>
        refine ⟨_, rfl, ?_⟩
        simp only [mread, mturn, top, mturnE, Inv, pushB, nth0_nil, nth0_zero_cons, nth0_succ_cons]
        exact Hub.H0 _ _ (by omega) hW
          (fun h1 => by omega) (fun _ hev => (hz' hev).1)
          (fun hnil => by simp at hnil) (fun hnil => by simp at hnil)
    | T3 W hn hW =>
      refine ⟨_, rfl, ?_⟩
      simp only [mread, mturn, top, mturnE, Inv, pushB, nth0_nil, nth0_zero_cons, nth0_succ_cons]
      exact Hub.H1 _ 0 _ rfl hn hW

theorem inv_hub (L1 : List ℕ) (z : ℕ) (R1 : List ℕ)
    (h : Hub (nth0 0 L1) (nth0 1 L1) (nth0 2 L1) z R1) :
    OK (mstep (1 :: L1, z :: R1)) := by
  unfold mstep
  dsimp only
  cases h with
  | H0 _ hz hW h1z h2z h5 h3 =>
    rcases nat_even_or_odd_two_mul z with ⟨q, rfl⟩ | ⟨q, rfl⟩
    · cases q with
      | zero => omega
      | succ q =>
        rw [mread_even]
        unfold mturn
        have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
        rw [hrep]
        dsimp only [top]
        rw [mturnE_rep]
        dsimp only [mturnE]
        have hrest : zf (top R1).2 := by
          cases R1 with
          | nil => trivial
          | cons _ _ => exact hW.2
        refine k1_gen L1 (q + 0 + 1) (top R1).1 (top R1).2 (by omega) hrest ?_
        intro hq1 hx0 hy0
        have hq0 : q = 0 := by omega
        subst hq0
        have h2 := h2z rfl (by rw [hx0])
        omega
    · rw [mread_odd]
      cases R1 with
      | nil =>
        cases q with
        | zero => exact False.elim ((h1z rfl).2 rfl)
        | succ q =>
          unfold mone mturn
          have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
          rw [hrep]
          dsimp only [bump, top]
          have h41 : 4 + 1 = 5 := rfl
          rw [h41, mturnE_rep]
          dsimp only [mturnE]
          refine tg OK 5 0 [] L1 (q + 0 + 1) ?_ ?_
          · intro i a L3
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushB, List.replicate, List.cons_append, List.nil_append, nth0_nil,
              nth0_zero_cons, nth0_succ_cons]
            exact Hub.H4 _ (i + (q + 0 + 1)) _ rfl (by simp) ⟨by omega, trivial⟩ (fun hq0 => by
              omega)
          · intro i L4 hj hzz
            generalize hns : nth0 (i + 1) L1 = ns
            have het : ns + (i + (q + 0 + 1)) = (ns + (i + (q + 0 + 1)) - 1) + 1 := by omega
            rw [Aout_S _ _ _ 4 _ _ _ het]
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushC, List.replicate, List.cons_append, List.nil_append, nth0_nil,
              nth0_zero_cons, nth0_succ_cons]
            rcases nat_even_or_odd_two_mul (i + (q + 0 + 1)) with ⟨e, he⟩ | ⟨e, he⟩
            · refine Hub.H3e _ e _ (by omega) (by simp) ⟨by omega, trivial⟩ ?_
              rcases e with _ | _ | e
              · omega
              · dsimp only [S3e]
                refine ⟨by omega, fun hex hc => ?_⟩
                have hns0 : ns = 0 := by omega
                rcases i with _ | _ | i
                · have hq1 : q = 1 := by omega
                  subst hq1
                  exact h5 rfl rfl ⟨hzz, by simpa only [hns0] using hns⟩
                · cases q with
                  | zero =>
                    exact h3 rfl rfl ⟨hj 0 (by omega), hzz, by simpa only [hns0] using hns⟩
                  | succ _ => omega
                · omega
              · dsimp only [S3e]
                omega
            · exact Hub.H3o _ (e + 1) _ (by omega) (by simp) ⟨by omega, trivial⟩ (fun hq0 => by
                omega)
      | cons p rest =>
        obtain ⟨hp, hrest⟩ := hW
        cases p with
        | zero => omega
        | succ p =>
          refine ⟨_, rfl, ?_⟩
          cases q with
          | zero =>
            simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
            exact ⟨⟨by omega, fun hev => by omega, fun _ ⟨hx0, _⟩ => (h1z rfl).1 hx0⟩,
              TR.T1 p rest hrest⟩
          | succ q =>
            simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
            refine ⟨⟨by omega, fun hev => by omega, fun _ ⟨hy, _⟩ => ?_⟩, TR.T1 p rest hrest⟩
            cases q <;> simp only [rep1, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy <;> omega
  | H1 q W he hn hW =>
    subst he
    rw [mread_even]
    unfold mturn
    have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
    rw [hrep]
    dsimp only [top]
    rw [mturnE_rep]
    dsimp only [mturnE]
    cases W with
    | nil => exact False.elim (hn rfl)
    | cons w W' =>
      exact k1_gen L1 (q + 0 + 1) 0 (w :: W') (by omega) hW (fun _ _ _ => Or.inl (by simp))
  | H2e q W he hn hW hx =>
    subst he
    rw [mread_even]
    unfold mturn
    have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
    rw [hrep]
    dsimp only [top]
    rw [mturnE_rep]
    dsimp only [mturnE]
    cases L1 with
    | nil =>
      simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hx
      omega
    | cons a L2 =>
      rcases a with _ | _ | a <;> simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hx
      · omega
      · omega
      · refine ⟨_, rfl, ?_⟩
        simp only [mturnE, top, Inv, pushB, List.replicate, List.nil_append, nth0_nil,
          nth0_zero_cons, nth0_succ_cons]
        exact Hub.HQ _ (q + 0) _ (by omega) hn hW
  | H2o q W he hn hW hne =>
    subst he
    rw [mread_odd]
    cases W with
    | nil => exact False.elim (hn rfl)
    | cons w W' =>
      obtain ⟨hw, hW'⟩ := hW
      cases w with
      | zero => omega
      | succ w =>
        refine ⟨_, rfl, ?_⟩
        cases q <;>
          (dsimp only [mone, rep1, bump, Inv]
           exact ⟨⟨by omega, hW'⟩, hne⟩)
  | H3e q W he hn hW hs =>
    subst he
    rw [mread_even]
    unfold mturn
    have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
    rw [hrep]
    dsimp only [top]
    rw [mturnE_rep]
    dsimp only [mturnE]
    cases L1 with
    | nil =>
      rcases q with _ | _ | q <;> simp only [S3e, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hs
        <;> omega
    | cons a L2 =>
      rcases a with _ | _ | a
      · rcases q with _ | _ | q
          <;> simp only [S3e, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hs
          <;> omega
      · dsimp only [mturnE]
        rcases q with _ | _ | q
        · simp only [S3e, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hs
          have hy := hs.2 trivial
          cases L2 with
          | nil =>
            simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy
            omega
          | cons b L3 =>
            simp only [nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy
            rcases b with _ | _ | b
            · omega
            · omega
            · refine ⟨_, rfl, ?_⟩
              simp only [mturnE, top, Inv, pushB, List.replicate, List.nil_append, nth0_nil,
                nth0_zero_cons, nth0_succ_cons]
              exact Hub.HP _ 1 _ (by omega) hn hW
        · simp only [S3e, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hs
          have hne := hs.2 trivial
          refine tg OK 1 0 (0 :: 0 :: W) L2 3 ?_ ?_
          · intro i a' L3
            refine ⟨_, rfl, ?_⟩
            simp only [top, Inv, pushB, List.replicate, List.nil_append, nth0_nil, nth0_zero_cons,
              nth0_succ_cons]
            exact Hub.HP _ (i + 2) _ (by omega) hn hW
          · intro i L4 _ _
            generalize nth0 (i + 1) L2 = ns
            have het : ns + (i + 3) = (ns + (i + 3) - 1) + 1 := by omega
            rw [Aout_S _ _ _ 0 _ _ _ het]
            refine ⟨_, rfl, ?_⟩
            simp only [Inv, pushC, nth0_nil, nth0_zero_cons, nth0_succ_cons]
            rcases nat_even_or_odd_two_mul (i + 3) with ⟨e, he'⟩ | ⟨e, he'⟩
            · exact Hub.H2o _ (e + 1) _ (by omega) hn hW hne
            · exact Hub.H2e _ (e + 1) _ (by omega) hn hW (by omega)
        · simp only [S3e, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hs
          omega
      · refine ⟨_, rfl, ?_⟩
        simp only [mturnE, top, Inv, pushB, List.replicate, List.nil_append, nth0_nil,
          nth0_zero_cons, nth0_succ_cons]
        exact Hub.HP _ (q + 0) _ (by omega) hn hW
  | H3o q W he hn hW hq =>
    subst he
    rw [mread_odd]
    cases W with
    | nil => exact False.elim (hn rfl)
    | cons w W' =>
      obtain ⟨hw, hW'⟩ := hW
      have hne : (1 + w) :: W' ≠ [1] := by
        intro hc
        injection hc with h1 _
        omega
      simp only [mone]
      unfold mturn
      cases q with
      | zero =>
        dsimp only [rep1, bump, top]
        have h41 : 4 + 1 = 5 := rfl
        rw [h41]
        exact k5_zero L1 w W' hW' hne (hq rfl)
      | succ q =>
        have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
        rw [hrep]
        dsimp only [bump, top]
        have h41 : 4 + 1 = 5 := rfl
        rw [h41, mturnE_rep]
        dsimp only [mturnE]
        exact k5_gen L1 (q + 0 + 1) w W' (by omega) hW' hne
  | H4 q W he hn hW hq =>
    subst he
    rw [mread_odd]
    cases W with
    | nil => exact False.elim (hn rfl)
    | cons w W' =>
      have hne : (1 + 0) :: w :: W' ≠ [1] := by simp
      simp only [mone]
      unfold mturn
      cases q with
      | zero =>
        dsimp only [rep1, bump, top]
        have h41 : 4 + 1 = 5 := rfl
        rw [h41]
        exact k5_zero L1 0 (w :: W') hW hne (hq rfl)
      | succ q =>
        have hrep : rep1 (q + 1) (1 :: L1) = 1 :: rep1 q (1 :: L1) := rfl
        rw [hrep]
        dsimp only [bump, top]
        have h41 : 4 + 1 = 5 := rfl
        rw [h41, mturnE_rep]
        dsimp only [mturnE]
        exact k5_gen L1 (q + 0 + 1) 0 (w :: W') (by omega) hW hne
  | HP q W he hn hW =>
    subst he
    rw [mread_odd]
    refine ⟨_, rfl, ?_⟩
    simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
    refine ⟨⟨by omega, fun hev => by omega, fun _ ⟨hy, _⟩ => ?_⟩, TR.T3 W hn hW⟩
    cases q <;> simp only [rep1, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy <;> omega
  | HQ q W he hn hW =>
    subst he
    rw [mread_odd]
    refine ⟨_, rfl, ?_⟩
    simp only [mone, rep1, bump, Inv, nth0_nil, nth0_zero_cons, nth0_succ_cons, Tr, Zr]
    refine ⟨⟨by omega, fun hev => by omega, fun _ ⟨hy, _⟩ => ?_⟩, TR.T2 W hn hW⟩
    cases q <;> simp only [rep1, nth0_nil, nth0_zero_cons, nth0_succ_cons] at hy <;> omega

theorem inv_step (s : List ℕ × List ℕ) (h : Inv s) :
    ∃ s', mstep s = some s' ∧ Inv s' := by
  rcases s with ⟨L, R⟩
  cases L with
  | nil =>
    cases R <;> cases h
  | cons t L =>
    cases R with
    | nil =>
      rcases t with _ | _ | _ | _ | _ | _ | t
      · cases L <;> cases h
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
      · cases h
    | cons z R1 =>
      rcases t with _ | _ | _ | _ | _ | _ | t
      · cases L with
        | nil => cases h
        | cons a L2 => exact inv_t0 a L2 z R1 h.1 h.2
      · exact inv_hub L z R1 h
      · cases h
      · cases h
      · cases h
      · exact inv_t5 L z R1 h.1 h.2
      · cases h

def s0 : List ℕ × List ℕ := ([1, 1, 0, 1], [2])

theorem init_reaches_s0 : (init []) [target_tm]⊢* CC s0 := by
  unfold CC s0
  dsimp only [enc, ones, ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

theorem inv0 : Inv s0 := by
  simp only [Inv, s0, nth0_nil, nth0_zero_cons, nth0_succ_cons]
  exact Hub.H0 2 [] (by omega) trivial
    (fun h1 => by omega) (fun _ _ => by omega) (fun _ h5 => by omega) (fun _ h3 => by omega)

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  refine IsNotHalt.of_reachesPlus_invariant (P := fun c => ∃ s, c = CC s ∧ Inv s)
    init_reaches_s0 ⟨s0, rfl, inv0⟩ ?_
  rintro _ ⟨s, rfl, hs⟩
  obtain ⟨s', hstep, hinv⟩ := inv_step s hs
  exact ⟨CC s', mstep_ok s s' hstep, s', rfl, hinv⟩


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RC_1RCHHH_1LD1RE_1LE0LD_1RA0LF_0RC0RB
