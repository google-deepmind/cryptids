/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.Longitudinal


/-!
# Busy Beaver Machine `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open BusyBeaver.Longitudinal

namespace Solution

private abbrev Sym := Fin 2
private abbrev Side := ListBlank Sym

private abbrev S0 : Sym := 0
private abbrev S1 : Sym := 1

private abbrev A : Fin 6 := 0
private abbrev B : Fin 6 := 1
private abbrev C : Fin 6 := 2
private abbrev D : Fin 6 := 3
private abbrev E : Fin 6 := 4


private abbrev tm : Machine (Fin 2) (Fin 6) := target_tm
/-! ## Stepping Helpers -/

private theorem step_right_R {q q' : Fin 6} {s w : Sym}
    (h : tm q s = some (some q', .write w .right)) (l r : Side) :
    step tm (l {{q}}> (s >> r)) = some ((w >> l) {{q'}}> r) := by
  simp [BusyBeaver.step, ListBlank.head_cons, ListBlank.tail_cons, h, Tape.write, Tape.move]

private theorem step_right_L {q q' : Fin 6} {s w : Sym}
    (h : tm q s = some (some q', .write w .left)) (l r : Side) :
    step tm (l {{q}}> (s >> r)) = some (l <{{q'}} (w >> r)) := by
  simp [BusyBeaver.step, ListBlank.head_cons, ListBlank.tail_cons, h, Tape.write, Tape.move]

private theorem step_left_L {q q' : Fin 6} {s w : Sym}
    (h : tm q s = some (some q', .write w .left)) (l r : Side) :
    step tm ((s >> l) <{{q}} r) = some (l <{{q'}} (w >> r)) := by
  simp [BusyBeaver.step, ListBlank.head_cons, ListBlank.tail_cons, h, Tape.write, Tape.move]

private theorem step_left_R {q q' : Fin 6} {s w : Sym}
    (h : tm q s = some (some q', .write w .right)) (l r : Side) :
    step tm ((s >> l) <{{q}} r) = some ((w >> l) {{q'}}> r) := by
  simp [BusyBeaver.step, ListBlank.head_cons, ListBlank.tail_cons, h, Tape.write, Tape.move]

local macro "tm_step1" : tactic =>
  `(tactic| first
    | exact step_right_R rfl _ _
    | exact step_right_L rfl _ _
    | exact step_left_L rfl _ _
    | exact step_left_R rfl _ _)

local macro "tm_step_star" : tactic =>
  `(tactic| first
    | exact ReachesStar.refl tm _
    | refine ReachesStar.head (by tm_step1) ?_)

local macro "tm_steps_star" : tactic =>
  `(tactic| repeat tm_step_star)

local macro "tm_steps_plus" : tactic =>
  `(tactic| (refine ReachesPlus.head (by tm_step1) ?_; tm_steps_star))

/-! ## Tape Encoding and Counter Tick Law -/

private def sb (b : Bool) : Sym := if b then S1 else S0

private def X : List Bool → Side
  | [] => S1 >> default
  | b :: r => sb b >> S1 >> X r

private def tok (b : Bool) (L : Side) : Side := S0 >> S0 >> S0 >> S0 >> sb b >> L

private def TL : List Bool → Side → Side
  | [], L => L
  | d :: r, L => tok d (TL r L)

private def inc : List Bool → Option (List Bool)
  | [] => none
  | false :: r => some (true :: r)
  | true :: r =>
    match inc r with
    | some r' => some (false :: r')
    | none => none

private def ones : ℕ → Side → Side
  | 0, r => r
  | n + 1, r => S1 >> ones n r

private def zeros : ℕ → Side → Side
  | 0, r => r
  | n + 1, r => S0 >> zeros n r

private theorem ones_shift (n : ℕ) (r : Side) : ones n (S1 >> r) = S1 >> ones n r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [ones, ih]

private theorem zeros_shift (n : ℕ) (r : Side) : zeros n (S0 >> r) = S0 >> zeros n r := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros, ih]

private theorem ones_add (a b : ℕ) (r : Side) : ones a (ones b r) = ones (a + b) r := by
  induction a with
  | zero => simp [ones]
  | succ a ih => simp only [ones, Nat.succ_add, ih]

private theorem zeros_add (a b : ℕ) (r : Side) : zeros a (zeros b r) = zeros (a + b) r := by
  induction a with
  | zero => simp [zeros]
  | succ a ih => simp only [zeros, Nat.succ_add, ih]

private theorem B_clear (n : ℕ) (P r : Side) :
    ReachesStar tm (P {{B}}> ones n r) (zeros n P {{B}}> r) := by
  induction n generalizing P with
  | zero => exact ReachesStar.refl tm _
  | succ n ih =>
    simp only [ones, zeros]
    refine ReachesStar.head (by tm_step1) ?_
    rw [← zeros_shift]
    exact ih (S0 >> P)

private theorem C_pass (n : ℕ) (P r : Side) :
    ReachesStar tm (P {{C}}> ones n r) (ones n P {{C}}> r) := by
  induction n generalizing P with
  | zero => exact ReachesStar.refl tm _
  | succ n ih =>
    simp only [ones]
    refine ReachesStar.head (by tm_step1) ?_
    rw [← ones_shift]
    exact ih (S1 >> P)

private theorem carry (xs ys : List Bool) (h : inc xs = some ys) (P : Side) :
    ReachesPlus tm ((S1 >> S1 >> P) {{C}}> X xs) (P <{{A}} (S0 >> S1 >> X ys)) := by
  induction xs generalizing ys P with
  | nil => cases h
  | cons b r ih =>
    cases b
    · simp only [inc, Option.some.injEq] at h
      subst h
      simp only [X, sb]
      tm_steps_plus
    · simp only [inc] at h
      rcases he : inc r with _ | r' <;> rw [he] at h
      · cases h
      · injection h with h; subst h
        simp only [X, sb]
        have h1 : ReachesStar tm ((S1 >> S1 >> P) {{C}}> (S1 >> S1 >> X r))
            ((S1 >> S1 >> S1 >> S1 >> P) {{C}}> X r) := by tm_steps_star
        have h2 := ih r' he (S1 >> S1 >> P)
        have h3 : ReachesPlus tm ((S1 >> S1 >> P) <{{A}} (S0 >> S1 >> X r'))
            (P <{{A}} (S0 >> S1 >> S0 >> S1 >> X r')) := by tm_steps_plus
        exact ReachesStar.trans_plus h1 (ReachesPlus.trans h2 h3)

private theorem E_T1 (T r : Side) :
    ReachesPlus tm (tok true T <{{E}} r) (T <{{E}} ones 5 r) := by
  simp only [tok, sb, ones]
  tm_steps_plus

private theorem E_T0 (T r : Side) :
    ReachesPlus tm (tok false T <{{E}} r) ((S1 >> T) {{B}}> ones 4 r) := by
  simp only [tok, sb, ones]
  tm_steps_plus

private theorem sweepD (ds ds' : List Bool) (h : inc ds = some ds') (L : Side) (k : ℕ) (R : Side) :
    ReachesPlus tm (TL ds L <{{E}} ones k (S0 >> R)) (zeros k (TL ds' L) {{B}}> (S0 >> R)) := by
  induction ds generalizing ds' k with
  | nil => cases h
  | cons b r ih =>
    cases b
    · simp only [inc, Option.some.injEq] at h
      subst h
      simp only [TL]
      have h1 := E_T0 (TL r L) (ones k (S0 >> R))
      rw [ones_add] at h1
      have h2 := B_clear (4 + k) (S1 >> TL r L) (S0 >> R)
      have heq : zeros (4 + k) (S1 >> TL r L) = zeros k (tok true (TL r L)) := by
        have hk : 4 + k = k + 4 := by omega
        rw [hk, ← zeros_add]
        rfl
      rw [heq] at h2
      exact ReachesPlus.trans_star h1 h2
    · simp only [inc] at h
      rcases he : inc r with _ | r' <;> rw [he] at h
      · cases h
      · injection h with h; subst h
        simp only [TL]
        have h1 := E_T1 (TL r L) (ones k (S0 >> R))
        rw [ones_add] at h1
        have h2 := ih r' he (5 + k)
        have heq : zeros (5 + k) (TL r' L) = zeros k (tok false (TL r' L)) := by
          have hk : 5 + k = k + 5 := by omega
          rw [hk, ← zeros_add]
          rfl
        rw [heq] at h2
        exact ReachesPlus.trans h1 h2

private def anchor (ds xs : List Bool) (L : Side) : Cfg Sym (Fin 6) :=
  (S0 >> TL ds L) <{{A}} (S0 >> S1 >> X xs)

private theorem phase1 (xs x1 : List Bool) (h : inc xs = some x1) (L : Side) :
    ReachesPlus tm ((S0 >> L) <{{A}} (S0 >> S1 >> X xs)) (L <{{E}} (S1 >> S0 >> S1 >> X x1)) := by
  have h1 : ReachesStar tm ((S0 >> L) <{{A}} (S0 >> S1 >> X xs))
      ((S1 >> S1 >> S1 >> L) {{C}}> X xs) := by tm_steps_star
  have h2 := carry xs x1 h (S1 >> L)
  have h3 : ReachesPlus tm ((S1 >> L) <{{A}} (S0 >> S1 >> X x1))
      (L <{{E}} (S1 >> S0 >> S1 >> X x1)) := by tm_steps_plus
  exact ReachesStar.trans_plus h1 (ReachesPlus.trans h2 h3)

private theorem phase2 (xs x1 : List Bool) (h : inc xs = some x1) (P : Side) :
    ReachesPlus tm (P {{B}}> (S0 >> S1 >> X xs)) (P <{{A}} (S0 >> S1 >> X x1)) := by
  have h1 : ReachesStar tm (P {{B}}> (S0 >> S1 >> X xs))
      ((S1 >> S1 >> P) {{C}}> X xs) := by tm_steps_star
  exact ReachesStar.trans_plus h1 (carry xs x1 h P)

private theorem tick (ds ds' xs x1 x2 : List Bool) (L : Side)
    (hd : inc ds = some ds') (h1 : inc xs = some x1) (h2 : inc x1 = some x2) :
    ReachesPlus tm (anchor ds xs L) (anchor ds' x2 L) := by
  unfold anchor
  have p1 := phase1 xs x1 h1 (TL ds L)
  have sw := sweepD ds ds' hd L 1 (S1 >> X x1)
  simp only [ones, zeros] at sw
  exact ReachesPlus.trans p1 (ReachesPlus.trans sw (phase2 x1 x2 h2 (S0 >> TL ds' L)))

/-! ## Defect Propagation and Carry Sweeps -/

private def oL (n : ℕ) : List Bool := List.replicate n true
private def zL (n : ℕ) : List Bool := List.replicate n false
private def B0 : Side := default
private def U (R : Side) : Side := S0 >> S0 >> S0 >> S1 >> R
private def D3 (R : Side) : Side := S0 >> S0 >> S1 >> R
private def AC (L : Side) (xs : List Bool) : Cfg Sym (Fin 6) := (S0 >> L) <{{A}} (S0 >> S1 >> X xs)
private def EC (L : Side) (xs : List Bool) : Cfg Sym (Fin 6) := L <{{E}} (S1 >> S0 >> S1 >> X xs)
private def BC (P : Side) (xs : List Bool) : Cfg Sym (Fin 6) := P {{B}}> (S0 >> S1 >> X xs)

private def pr : ℕ → Side → Side
  | 0, r => r
  | k + 1, r => S0 >> S1 >> pr k r

private def alt : ℕ → Side → Side
  | 0, r => r
  | k + 1, r => S1 >> S0 >> alt k r

private theorem X_zL (k : ℕ) (xs : List Bool) : X (zL k ++ xs) = pr k (X xs) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hz : zL (k + 1) = false :: zL k := rfl
    rw [hz, List.cons_append, X, sb, pr, ih]; rfl

private theorem alt_S0 (p : ℕ) (r : Side) : alt p (S1 >> S0 >> r) = S1 >> S0 >> alt p r := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [alt, ih]

private theorem alt_S1 (p : ℕ) (r : Side) : alt p (S1 >> r) = S1 >> pr p r := by
  induction p with
  | zero => rfl
  | succ p ih => simp only [alt, pr, ih]

private theorem tok_false (R : Side) : tok false R = zeros 5 R := rfl
private theorem tok_true (R : Side) : tok true R = zeros 4 (S1 >> R) := rfl
private theorem U_zeros (R : Side) : U R = zeros 3 (S1 >> R) := rfl
private theorem D3_zeros (R : Side) : D3 R = zeros 2 (S1 >> R) := rfl

private theorem TL_zL (n : ℕ) (R : Side) : TL (zL n) R = zeros (5 * n) R := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hm : 5 * (n + 1) = 5 + 5 * n := by omega
    have hz : zL (n + 1) = false :: zL n := rfl
    rw [hm, ← zeros_add, hz, TL, ih, tok_false]

private theorem B0_S0 : B0 = S0 >> B0 :=
  ListBlank.cons_zero_default.symm

private theorem zeros_B0 (n : ℕ) : zeros n B0 = B0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [zeros, ih, ← B0_S0]

private theorem TL_zL_B0 (n : ℕ) : TL (zL n) B0 = B0 := by
  rw [TL_zL, zeros_B0]

private theorem TL_app (a b : List Bool) (R : Side) : TL (a ++ b) R = TL a (TL b R) := by
  induction a with
  | nil => rfl
  | cons d a ih => simp only [List.cons_append, TL, ih]

private theorem E_T1s (m : ℕ) (Q r : Side) :
    ReachesStar tm (TL (oL m) Q <{{E}} r) (Q <{{E}} ones (5 * m) r) := by
  induction m generalizing r with
  | zero => exact ReachesStar.refl tm _
  | succ m ih =>
    have ho : oL (m + 1) = true :: oL m := rfl
    rw [ho, TL]
    have h1 := (E_T1 (TL (oL m) Q) r).to_star
    have h2 := ih (ones 5 r)
    rw [ones_add] at h2
    have hm : 5 * m + 5 = 5 * (m + 1) := by omega
    rw [hm] at h2
    exact ReachesStar.trans h1 h2

private theorem U_pass (R r : Side) :
    ReachesPlus tm (U R <{{E}} r) (R <{{E}} ones 4 r) := by
  simp only [U, ones]
  tm_steps_plus

private theorem E_stop (Q : Side) (k : ℕ) (R : Side) :
    ReachesPlus tm (zeros 5 Q <{{E}} ones k (S0 >> R))
      (zeros (4 + k) (S1 >> Q) {{B}}> (S0 >> R)) := by
  have h1 := E_T0 Q (ones k (S0 >> R))
  rw [tok_false, ones_add] at h1
  exact ReachesPlus.trans_star h1 (B_clear (4 + k) (S1 >> Q) (S0 >> R))

private theorem ovf_C (W : ℕ) (P : Side) :
    ReachesPlus tm ((S1 >> S1 >> P) {{C}}> X (oL W)) (P <{{E}} (S1 >> S0 >> S1 >> X (zL W))) := by
  induction W generalizing P with
  | zero =>
    simp only [oL, zL, List.replicate_zero, X]
    refine ReachesPlus.head (step_right_R rfl _ _) ?_
    conv_lhs => rw [← ListBlank.cons_zero_default]
    tm_steps_star
  | succ W ih =>
    have ho : oL (W + 1) = true :: oL W := rfl
    have hz : zL (W + 1) = false :: zL W := rfl
    rw [ho, hz]
    change ReachesPlus tm ((S1 >> S1 >> P) {{C}}> (S1 >> S1 >> X (oL W)))
      (P <{{E}} (S1 >> S0 >> S1 >> S0 >> S1 >> X (zL W)))
    have h1 : ReachesStar tm ((S1 >> S1 >> P) {{C}}> (S1 >> S1 >> X (oL W)))
        ((S1 >> S1 >> S1 >> S1 >> P) {{C}}> X (oL W)) := by tm_steps_star
    have h2 := ih (S1 >> S1 >> P)
    have h3 : ReachesPlus tm ((S1 >> S1 >> P) <{{E}} (S1 >> S0 >> S1 >> X (zL W)))
        (P <{{E}} (S1 >> S0 >> S1 >> S0 >> S1 >> X (zL W))) := by tm_steps_plus
    exact ReachesStar.trans_plus h1 (ReachesPlus.trans h2 h3)

private theorem ovf1 (W : ℕ) (L : Side) :
    ReachesPlus tm (AC (S0 >> L) (oL W)) (EC L (true :: zL W)) := by
  simp only [AC, EC, X, sb]
  have h1 : ReachesStar tm ((S0 >> S0 >> L) <{{A}} (S0 >> S1 >> X (oL W)))
      ((S1 >> S1 >> S1 >> S0 >> L) {{C}}> X (oL W)) := by tm_steps_star
  have h2 := ovf_C W (S1 >> S0 >> L)
  have h3 : ReachesPlus tm ((S1 >> S0 >> L) <{{E}} (S1 >> S0 >> S1 >> X (zL W)))
      (L <{{E}} (S1 >> S0 >> S1 >> S1 >> S1 >> X (zL W))) := by tm_steps_plus
  exact ReachesStar.trans_plus h1 (ReachesPlus.trans h2 h3)

private theorem ovf2 (W : ℕ) (P : Side) :
    ReachesPlus tm (BC P (oL W)) (EC P (zL W)) := by
  simp only [BC, EC]
  have h1 : ReachesStar tm (P {{B}}> (S0 >> S1 >> X (oL W)))
      ((S1 >> S1 >> P) {{C}}> X (oL W)) := by tm_steps_star
  exact ReachesStar.trans_plus h1 (ovf_C W P)

private theorem E_step (ds ds' : List Bool) (L : Side) (x : List Bool) (h : inc ds = some ds') :
    ReachesPlus tm (EC (TL ds L) x) (BC (S0 >> TL ds' L) x) :=
  sweepD ds ds' h L 1 (S1 >> X x)

private theorem E5 (Q : Side) (x : List Bool) :
    ReachesPlus tm (EC (zeros 5 Q) x) (BC (S0 >> tok true Q) x) :=
  E_stop Q 1 (S1 >> X x)

private theorem ones_tail (n : ℕ) (R : Side) : ones n (S1 >> R) = ones (n + 1) R := by
  rw [← ones_add]; rfl

private theorem E_cross (m i : ℕ) (Q : Side) (x : List Bool) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (zeros 5 Q)))) x)
      (BC (S0 >> TL (zL (m + i + 1)) (U Q)) x) := by
  unfold EC BC
  have h1 := E_T1s m (U (TL (oL i) (zeros 5 Q))) (S1 >> S0 >> S1 >> X x)
  have h2 := U_pass (TL (oL i) (zeros 5 Q)) (ones (5 * m) (S1 >> S0 >> S1 >> X x))
  have h3 := E_T1s i (zeros 5 Q) (ones 4 (ones (5 * m) (S1 >> S0 >> S1 >> X x)))
  have hp := ReachesStar.trans_plus h1 (ReachesPlus.trans_star h2 h3)
  rw [ones_add, ones_add, ones_tail] at hp
  have hs := E_stop Q (5 * i + 4 + 5 * m + 1) (S1 >> X x)
  have hp2 := ReachesPlus.trans hp hs
  have heq : zeros (4 + (5 * i + 4 + 5 * m + 1)) (S1 >> Q) =
      S0 >> TL (zL (m + i + 1)) (U Q) := by
    rw [TL_zL, U_zeros]
    change zeros (4 + (5 * i + 4 + 5 * m + 1)) (S1 >> Q) =
      zeros 1 (zeros (5 * (m + i + 1)) (zeros 3 (S1 >> Q)))
    rw [zeros_add, zeros_add]
    congr 1
    omega
  rwa [heq] at hp2

private theorem E_absorb (m i : ℕ) (x : List Bool) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (U B0)))) x)
      (BC (S0 >> TL (zL (m + i + 2)) (D3 B0)) x) := by
  unfold EC BC
  have h1 := E_T1s m (U (TL (oL i) (U B0))) (S1 >> S0 >> S1 >> X x)
  have h2 := U_pass (TL (oL i) (U B0)) (ones (5 * m) (S1 >> S0 >> S1 >> X x))
  have h3 := E_T1s i (U B0) (ones 4 (ones (5 * m) (S1 >> S0 >> S1 >> X x)))
  have h4 := U_pass B0 (ones (5 * i) (ones 4 (ones (5 * m) (S1 >> S0 >> S1 >> X x))))
  have hp := ReachesStar.trans_plus h1 (ReachesPlus.trans h2 (ReachesStar.trans_plus h3 h4))
  rw [ones_add, ones_add, ones_add, ones_tail] at hp
  have hs := E_stop B0 (4 + 5 * i + 4 + 5 * m + 1) (S1 >> X x)
  rw [zeros_B0 5] at hs
  have hp2 := ReachesPlus.trans hp hs
  have heq : zeros (4 + (4 + 5 * i + 4 + 5 * m + 1)) (S1 >> B0) =
      S0 >> TL (zL (m + i + 2)) (D3 B0) := by
    rw [TL_zL, D3_zeros]
    change zeros (4 + (4 + 5 * i + 4 + 5 * m + 1)) (S1 >> B0) =
      zeros 1 (zeros (5 * (m + i + 2)) (zeros 2 (S1 >> B0)))
    rw [zeros_add, zeros_add]
    congr 1
    omega
  rwa [heq] at hp2

private theorem tick_cross (m i : ℕ) (R : Side) (xs x1 x2 : List Bool)
    (h1 : inc xs = some x1) (h2 : inc x1 = some x2) :
    ReachesPlus tm (AC (TL (oL m) (U (TL (oL i) (tok false R)))) xs)
      (AC (TL (zL (m + i + 1)) (U R)) x2) := by
  have p1 := phase1 xs x1 h1 (TL (oL m) (U (TL (oL i) (tok false R))))
  have ec := E_cross m i R x1
  have p2 := phase2 x1 x2 h2 (S0 >> TL (zL (m + i + 1)) (U R))
  exact ReachesPlus.trans p1 (ReachesPlus.trans ec p2)

private theorem tick_absorb (m i : ℕ) (xs x1 x2 : List Bool)
    (h1 : inc xs = some x1) (h2 : inc x1 = some x2) :
    ReachesPlus tm (AC (TL (oL m) (U (TL (oL i) (U B0)))) xs)
      (AC (TL (zL (m + i + 2)) (D3 B0)) x2) := by
  have p1 := phase1 xs x1 h1 (TL (oL m) (U (TL (oL i) (U B0))))
  have ea := E_absorb m i x1
  have p2 := phase2 x1 x2 h2 (S0 >> TL (zL (m + i + 2)) (D3 B0))
  exact ReachesPlus.trans p1 (ReachesPlus.trans ea p2)

private theorem tick_plain (ds ds' : List Bool) (R : Side) (xs x1 x2 : List Bool)
    (hd : inc ds = some ds') (h1 : inc xs = some x1) (h2 : inc x1 = some x2) :
    ReachesPlus tm (AC (TL ds R) xs) (AC (TL ds' R) x2) :=
  tick ds ds' xs x1 x2 R hd h1 h2

private theorem turn (P : Side) (x : List Bool) :
    ReachesPlus tm ((S1 >> S1 >> P) {{C}}> (S0 >> S1 >> X x))
      ((S1 >> P) <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  tm_steps_plus

private theorem reb0a (k : ℕ) (N r : Side) :
    ReachesStar tm ((S1 >> S0 >> N) <{{E}} ones k r) ((S1 >> S1 >> N) {{C}}> ones k r) := by
  tm_steps_star

private theorem reb0 (k : ℕ) (N : Side) (x : List Bool) :
    ReachesPlus tm ((S1 >> S0 >> N) <{{E}} ones k (S0 >> S1 >> X x))
      (ones (k + 1) N <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  have h1 := ReachesStar.trans (reb0a k N (S0 >> S1 >> X x))
    (C_pass k (S1 >> S1 >> N) (S0 >> S1 >> X x))
  rw [ones_shift, ones_shift] at h1
  have h2 := turn (ones k N) x
  have heq : S1 >> ones k N = ones (k + 1) N := rfl
  rw [heq] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem reb2a (k : ℕ) (Ln r : Side) :
    ReachesStar tm (D3 Ln <{{E}} ones k r) ((S1 >> Ln) {{C}}> ones (k + 2) r) := by
  simp only [D3, ones]
  tm_steps_star

private theorem reb2 (k : ℕ) (Ln : Side) (x : List Bool) :
    ReachesPlus tm (D3 Ln <{{E}} ones k (S0 >> S1 >> X x))
      (ones (k + 2) Ln <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  have h1 := ReachesStar.trans (reb2a k Ln (S0 >> S1 >> X x))
    (C_pass (k + 2) (S1 >> Ln) (S0 >> S1 >> X x))
  rw [ones_shift] at h1
  change ReachesStar tm (D3 Ln <{{E}} ones k (S0 >> S1 >> X x))
    ((S1 >> S1 >> ones (k + 1) Ln) {{C}}> (S0 >> S1 >> X x)) at h1
  have h2 := turn (ones (k + 1) Ln) x
  exact ReachesStar.trans_plus h1 h2

private theorem E_ones_even (p : ℕ) (P r : Side) :
    ReachesStar tm (ones (2 * p) P <{{E}} r) (P <{{E}} alt p r) := by
  induction p generalizing r with
  | zero => exact ReachesStar.refl tm _
  | succ p ih =>
    have hm : 2 * (p + 1) = 2 * p + 2 := by omega
    rw [hm]
    simp only [ones]
    have h1 : ReachesStar tm ((S1 >> S1 >> ones (2 * p) P) <{{E}} r)
        (ones (2 * p) P <{{E}} (S1 >> S0 >> r)) := by tm_steps_star
    have h2 := ih (S1 >> S0 >> r)
    rw [alt_S0] at h2
    exact ReachesStar.trans h1 h2

private theorem E_ones_odd (p : ℕ) (P r : Side) :
    ReachesPlus tm (ones (2 * p + 1) P <{{E}} r) (P <{{A}} (S0 >> alt p r)) := by
  rw [← ones_add (2 * p) 1 P]
  have h1 := E_ones_even p (ones 1 P) r
  simp only [ones] at h1
  have h2 : ReachesPlus tm ((S1 >> P) <{{E}} alt p r) (P <{{A}} (S0 >> alt p r)) := by tm_steps_plus
  exact ReachesStar.trans_plus h1 h2

private theorem after_even (p : ℕ) (P : Side) (x : List Bool) :
    ReachesStar tm (ones (2 * (p + 1)) P <{{E}} (S1 >> S1 >> S1 >> X x))
      (EC P (zL p ++ true :: x)) := by
  have h1 := E_ones_even (p + 1) P (S1 >> S1 >> S1 >> X x)
  rw [alt_S1] at h1
  simp only [pr] at h1
  have hx : S1 >> S1 >> X x = X (true :: x) := rfl
  rw [hx, ← X_zL] at h1
  exact h1

private theorem after_odd (p : ℕ) (L : Side) (x : List Bool) :
    ReachesPlus tm (ones (2 * p + 1) (S0 >> L) <{{E}} (S1 >> S1 >> S1 >> X x))
      (AC L (zL p ++ true :: x)) := by
  have h1 := E_ones_odd p (S0 >> L) (S1 >> S1 >> S1 >> X x)
  rw [alt_S1] at h1
  have hx : S1 >> S1 >> X x = X (true :: x) := rfl
  rw [hx, ← X_zL] at h1
  exact h1

private theorem R0 (m : ℕ) (N : Side) (x : List Bool) :
    ReachesPlus tm (EC (TL (oL m) (S1 >> S0 >> N)) x)
      (ones (5 * m + 2) N <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  unfold EC
  have h1 := E_T1s m (S1 >> S0 >> N) (S1 >> S0 >> S1 >> X x)
  rw [ones_tail] at h1
  exact ReachesStar.trans_plus h1 (reb0 (5 * m + 1) N x)

private theorem R2 (r : ℕ) (Ln : Side) (x : List Bool) :
    ReachesPlus tm (EC (TL (oL r) (D3 Ln)) x)
      (ones (5 * r + 3) Ln <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  unfold EC
  have h1 := E_T1s r (D3 Ln) (S1 >> S0 >> S1 >> X x)
  rw [ones_tail] at h1
  exact ReachesStar.trans_plus h1 (reb2 (5 * r + 1) Ln x)

private theorem R2U (m i : ℕ) (Ln : Side) (x : List Bool) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (D3 Ln)))) x)
      (ones (5 * (m + i + 1) + 2) Ln <{{E}} (S1 >> S1 >> S1 >> X x)) := by
  unfold EC
  have h1 := E_T1s m (U (TL (oL i) (D3 Ln))) (S1 >> S0 >> S1 >> X x)
  have h2 := U_pass (TL (oL i) (D3 Ln)) (ones (5 * m) (S1 >> S0 >> S1 >> X x))
  have h3 := E_T1s i (D3 Ln) (ones 4 (ones (5 * m) (S1 >> S0 >> S1 >> X x)))
  have hp := ReachesStar.trans_plus h1 (ReachesPlus.trans_star h2 h3)
  rw [ones_add, ones_add, ones_tail] at hp
  have hr := reb2 (5 * i + 4 + 5 * m + 1) Ln x
  have hp2 := ReachesPlus.trans hp hr
  have hm : 5 * i + 4 + 5 * m + 1 + 2 = 5 * (m + i + 1) + 2 := by omega
  rwa [hm] at hp2

/-! ## Binary Words and Multi-Tick Acceleration -/

private def pw (n : ℕ) : ℕ := 2 ^ n

private theorem pw_0 : pw 0 = 1 := rfl

private theorem pw_S (n : ℕ) : pw (n + 1) = 2 * pw n := by
  simp only [pw, Nat.pow_succ]; ring

private theorem pw_add (a b : ℕ) : pw (a + b) = pw a * pw b := by
  simp only [pw, Nat.pow_add]

private theorem pw_pos (n : ℕ) : 1 ≤ pw n :=
  Nat.one_le_two_pow

private theorem pw_le (a b : ℕ) (h : a ≤ b) : pw a ≤ pw b :=
  Nat.pow_le_pow_right (by omega) h

private theorem pw_lt (a b : ℕ) (h : a < b) : 2 * pw a ≤ pw b := by
  rw [← pw_S]; exact pw_le (a + 1) b h

private def bin : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, v => (v % 2 == 1) :: bin n (v / 2)

private theorem bin_even (n w : ℕ) : bin (n + 1) (2 * w) = false :: bin n w := by
  have h1 : (2 * w) % 2 = 0 := by omega
  have h2 : (2 * w) / 2 = w := by omega
  simp only [bin, h1, h2]; rfl

private theorem bin_odd (n w : ℕ) : bin (n + 1) (2 * w + 1) = true :: bin n w := by
  have h1 : (2 * w + 1) % 2 = 1 := by omega
  have h2 : (2 * w + 1) / 2 = w := by omega
  simp only [bin, h1, h2]; rfl

private theorem N_parity (v : ℕ) : (∃ w, v = 2 * w) ∨ (∃ w, v = 2 * w + 1) := by
  rcases Nat.mod_two_eq_zero_or_one v with h | h
  · exact Or.inl ⟨v / 2, by omega⟩
  · exact Or.inr ⟨v / 2, by omega⟩

private theorem bin_zero (n : ℕ) : bin n 0 = zL n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h0 : (0 : ℕ) = 2 * 0 := rfl
    rw [h0, bin_even, ih]; rfl

private theorem bin_ones (n : ℕ) : bin n (pw n - 1) = oL n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hp := pw_pos n
    have heq : pw (n + 1) - 1 = 2 * (pw n - 1) + 1 := by rw [pw_S]; omega
    rw [heq, bin_odd, ih]; rfl

private theorem bin_app (n t u m : ℕ) (h : t < pw n) :
    bin (n + m) (t + pw n * u) = bin n t ++ bin m u := by
  induction n generalizing t with
  | zero =>
    rw [pw_0] at h
    have ht : t = 0 := by omega
    subst ht
    simp [bin, pw_0]
  | succ n ih =>
    rw [pw_S] at h ⊢
    rw [Nat.succ_add]
    rcases N_parity t with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have heq : 2 * w + 2 * pw n * u = 2 * (w + pw n * u) := by ring
      rw [heq, bin_even, bin_even, List.cons_append, ih w (by omega)]
    · have heq : 2 * w + 1 + 2 * pw n * u = 2 * (w + pw n * u) + 1 := by ring
      rw [heq, bin_odd, bin_odd, List.cons_append, ih w (by omega)]

private theorem bin_split (t c C : ℕ) :
    bin (t + (c + 1)) (pw t * (2 * C + 1)) = zL t ++ true :: bin c C := by
  have heq : pw t * (2 * C + 1) = 0 + pw t * (2 * C + 1) := by omega
  rw [heq, bin_app t 0 (2 * C + 1) (c + 1) (by have := pw_pos t; omega), bin_zero, bin_odd]

private theorem bin_pow (u k : ℕ) : bin (u + (k + 1)) (pw u) = zL u ++ true :: zL k := by
  have heq : pw u = pw u * (2 * 0 + 1) := by omega
  rw [heq, bin_split, bin_zero]

private theorem inc_bin (n v : ℕ) (h : v + 1 < pw n) :
    inc (bin n v) = some (bin n (v + 1)) := by
  induction n generalizing v with
  | zero => rw [pw_0] at h; omega
  | succ n ih =>
    rw [pw_S] at h
    rcases N_parity v with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [bin_even, bin_odd]; rfl
    · have heq : 2 * w + 1 + 1 = 2 * (w + 1) := by omega
      rw [bin_odd, heq, bin_even, inc, ih w (by omega)]

private theorem inc_none (xs : List Bool) (h : inc xs = none) : xs = oL xs.length := by
  induction xs with
  | nil => rfl
  | cons b r ih =>
    cases b
    · cases h
    · simp only [inc] at h
      rcases he : inc r with _ | r' <;> rw [he] at h
      · simp only [List.length_cons, oL, List.replicate_succ]
        exact congrArg (true :: ·) (ih he)
      · cases h

private theorem inc_form (xs ys : List Bool) (h : inc xs = some ys) :
    ∃ i rest, xs = oL i ++ false :: rest ∧ ys = zL i ++ true :: rest := by
  induction xs generalizing ys with
  | nil => cases h
  | cons b r ih =>
    cases b
    · simp only [inc, Option.some.injEq] at h
      subst h
      exact ⟨0, r, rfl, rfl⟩
    · simp only [inc] at h
      rcases he : inc r with _ | r' <;> rw [he] at h
      · cases h
      · injection h with h; subst h
        obtain ⟨i, rest, rfl, rfl⟩ := ih r' he
        exact ⟨i + 1, rest, rfl, rfl⟩

private theorem inc_app (a a' b : List Bool) (h : inc a = some a') :
    inc (a ++ b) = some (a' ++ b) := by
  induction a generalizing a' with
  | nil => cases h
  | cons d a ih =>
    cases d
    · simp only [inc, Option.some.injEq] at h
      subst h; rfl
    · simp only [inc] at h
      rcases he : inc a with _ | a2 <;> rw [he] at h
      · cases h
      · injection h with h; subst h
        simp only [List.cons_append, inc, ih a2 he]

private theorem inc_oL_app (m : ℕ) (r : List Bool) :
    inc (oL m ++ r) = match inc r with | some r' => some (zL m ++ r') | none => none := by
  induction m with
  | zero => simp only [oL, zL, List.replicate_zero, List.nil_append]; cases inc r <;> rfl
  | succ m ih =>
    have ho : oL (m + 1) = true :: oL m := rfl
    have hz : zL (m + 1) = false :: zL m := rfl
    rw [ho, hz, List.cons_append, inc, ih]
    cases inc r <;> rfl

private theorem zL_add (a b : ℕ) : zL (a + b) = zL a ++ zL b :=
  List.replicate_add a b false

private theorem oL_true_form (a b : List Bool) (n : ℕ) (h : a ++ true :: b = oL n) :
    a = oL a.length ∧ b = oL b.length := by
  induction a generalizing n with
  | nil =>
    cases n with
    | zero => cases h
    | succ n =>
      have ho : oL (n + 1) = true :: oL n := rfl
      rw [List.nil_append, ho, List.cons.injEq] at h
      obtain ⟨_, rfl⟩ := h
      exact ⟨rfl, by simp [oL]⟩
  | cons d a ih =>
    cases n with
    | zero => cases h
    | succ n =>
      have ho : oL (n + 1) = true :: oL n := rfl
      rw [List.cons_append, ho, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨h3, h4⟩ := ih n h2
      refine ⟨?_, h4⟩
      simp only [List.length_cons, oL, List.replicate_succ]
      exact congrArg (true :: ·) h3

private theorem zL_true_form (u : ℕ) (a b : List Bool) (k : ℕ)
    (h : a ++ true :: b = zL u ++ true :: zL k) :
    a = zL u ∧ b = zL k := by
  induction u generalizing a with
  | zero =>
    cases a with
    | nil =>
      simp only [zL, List.replicate_zero, List.nil_append, List.cons.injEq] at h
      exact ⟨rfl, h.2⟩
    | cons d a =>
      have hz : zL 0 = [] := rfl
      rw [hz, List.nil_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      have hin : true ∈ List.replicate k false := by
        change true ∈ zL k
        rw [← h2]; simp
      simp at hin
  | succ u ih =>
    cases a with
    | nil =>
      have hz : zL (u + 1) = false :: zL u := rfl
      rw [hz, List.nil_append, List.cons_append, List.cons.injEq] at h
      cases h.1
    | cons d a =>
      have hz : zL (u + 1) = false :: zL u := rfl
      rw [hz, List.cons_append, List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h2⟩ := h
      obtain ⟨rfl, rfl⟩ := ih a h2
      exact ⟨rfl, rfl⟩

private theorem TL_bin_pad (n k v : ℕ) (h : v < pw n) :
    TL (bin (n + k) v) B0 = TL (bin n v) B0 := by
  have hv : v = v + pw n * 0 := by omega
  conv_lhs => rw [hv]
  rw [bin_app n v 0 k h, TL_app, bin_zero, TL_zL_B0]

private theorem skip_plain (K m W v x : ℕ) (R : Side)
    (h1 : v + K < pw m) (h2 : x + 2 * K < pw W) :
    ReachesStar tm (AC (TL (bin m v) R) (bin W x))
      (AC (TL (bin m (v + K)) R) (bin W (x + 2 * K))) := by
  induction K generalizing v x with
  | zero => simp only [Nat.add_zero, Nat.mul_zero]; exact ReachesStar.refl tm _
  | succ K ih =>
    have hx2 : inc (bin W (x + 1)) = some (bin W (x + 2)) := by
      have h_eq : x + 2 = (x + 1) + 1 := by omega
      rw [h_eq]; exact inc_bin W (x + 1) (by omega)
    have st := tick_plain (bin m v) (bin m (v + 1)) R
      (bin W x) (bin W (x + 1)) (bin W (x + 2))
      (inc_bin m v (by omega)) (inc_bin W x (by omega)) hx2
    have ih' := ih (v + 1) (x + 2) (by omega) (by omega)
    have hv : v + 1 + K = v + (K + 1) := by omega
    have hx : x + 2 + 2 * K = x + 2 * (K + 1) := by omega
    rw [hv, hx] at ih'
    exact ReachesStar.trans st.to_star ih'

private def MXC (T : Side) (low hi : List Bool) (W : ℕ) (x : ℕ) : Cfg Sym (Fin 6) :=
  AC (TL low (U (TL hi T))) (bin W x)

private theorem mix_tick (L V W x : ℕ) (T : Side) (low hi : List Bool)
    (hb : low ++ true :: hi = bin L V) (h1 : V + 1 < pw L) (h2 : x + 2 < pw W) :
    ∃ low' hi', low' ++ true :: hi' = bin L (V + 1) ∧
      ReachesPlus tm (MXC T low hi W x) (MXC T low' hi' W (x + 2)) := by
  unfold MXC
  have hi_bin := inc_bin L V h1
  rw [← hb] at hi_bin
  have hx1 := inc_bin W x (by omega)
  have hx2 : inc (bin W (x + 1)) = some (bin W (x + 2)) := by
    have : x + 2 = (x + 1) + 1 := by omega
    rw [this]; exact inc_bin W (x + 1) (by omega)
  rcases el : inc low with _ | low'
  · have hl := inc_none low el
    rw [hl, inc_oL_app] at hi_bin
    simp only [inc] at hi_bin
    rcases eh : inc hi with _ | h' <;> rw [eh] at hi_bin
    · cases hi_bin
    · injection hi_bin with hi_bin
      obtain ⟨i, rest, rfl, rfl⟩ := inc_form hi h' eh
      refine ⟨zL (low.length + i + 1), rest, ?_, ?_⟩
      · rw [← hi_bin]
        have hlen : low.length + i + 1 = low.length + (i + 1) := by omega
        rw [hlen, zL_add, List.append_assoc]; rfl
      · conv_lhs => rw [hl]
        rw [TL_app]
        simp only [TL]
        exact tick_cross low.length i (TL rest T) (bin W x) (bin W (x + 1)) (bin W (x + 2)) hx1 hx2
  · rw [inc_app low low' (true :: hi) el] at hi_bin
    injection hi_bin with hi_bin
    exact ⟨low', hi, hi_bin,
      tick_plain low low' (U (TL hi T)) (bin W x) (bin W (x + 1)) (bin W (x + 2)) el hx1 hx2⟩

private theorem skip_mix (K L V W x : ℕ) (T : Side) (low hi : List Bool)
    (hb : low ++ true :: hi = bin L V) (h1 : V + K < pw L) (h2 : x + 2 * K < pw W) :
    ∃ low' hi', low' ++ true :: hi' = bin L (V + K) ∧
      ReachesStar tm (MXC T low hi W x) (MXC T low' hi' W (x + 2 * K)) := by
  induction K generalizing V x low hi with
  | zero =>
    exact ⟨low, hi, by simpa using hb,
      by simp only [Nat.mul_zero, Nat.add_zero]; exact ReachesStar.refl tm _⟩
  | succ K ih =>
    obtain ⟨l1, h1', e1, s1⟩ := mix_tick L V W x T low hi hb (by omega) (by omega)
    obtain ⟨l2, h2', e2, s2⟩ := ih (V + 1) (x + 2) l1 h1' e1 (by omega) (by omega)
    have hv : V + 1 + K = V + (K + 1) := by omega
    have hx : x + 2 + 2 * K = x + 2 * (K + 1) := by omega
    rw [hv] at e2
    rw [hx] at s2
    exact ⟨l2, h2', e2, ReachesStar.trans s1.to_star s2⟩

private theorem mix_to_pow (K u k W x : ℕ) (low hi : List Bool)
    (hb : low ++ true :: hi = bin (u + (k + 1)) (pw u - K))
    (h1 : K ≤ pw u - 1) (h2 : x + 2 * K < pw W) :
    ReachesStar tm (MXC B0 low hi W x) (AC (TL (zL u) (U B0)) (bin W (x + 2 * K))) := by
  have hu := pw_pos u
  have hk := pw_pos k
  have hlt : pw u - K + K < pw (u + (k + 1)) := by
    have : pw u - K + K = pw u := by omega
    rw [this, pw_add, pw_S]
    nlinarith
  obtain ⟨l2, h2', e2, s2⟩ := skip_mix K (u + (k + 1)) (pw u - K) W x B0 low hi hb hlt h2
  have heq : pw u - K + K = pw u := by omega
  rw [heq, bin_pow] at e2
  obtain ⟨rfl, rfl⟩ := zL_true_form u l2 h2' k e2
  unfold MXC at s2
  rwa [TL_zL_B0] at s2

private theorem mix_to_ones (K L W x : ℕ) (T : Side) (low hi : List Bool)
    (hb : low ++ true :: hi = bin L (pw L - 1 - K))
    (h1 : K ≤ pw L - 1) (h2 : x + 2 * K < pw W) :
    ∃ m i, m + (i + 1) = L ∧
      ReachesStar tm (MXC T low hi W x) (AC (TL (oL m) (U (TL (oL i) T))) (bin W (x + 2 * K))) := by
  have hL := pw_pos L
  obtain ⟨l2, h2', e2, s2⟩ := skip_mix K L (pw L - 1 - K) W x T low hi hb (by omega) h2
  have heq : pw L - 1 - K + K = pw L - 1 := by omega
  rw [heq, bin_ones] at e2
  obtain ⟨e3, e4⟩ := oL_true_form l2 h2' L e2
  refine ⟨l2.length, h2'.length, ?_, ?_⟩
  · have hlen := congrArg List.length e2
    simp only [List.length_append, List.length_cons, oL, List.length_replicate] at hlen
    omega
  · rw [← e3, ← e4]; exact s2

/-! ## Macro Stage Transitions -/

private def Afun (m : ℕ) : ℕ := (5 * m + 1) / 2
private def Apr (r : ℕ) : ℕ := (5 * r + 2) / 2

private theorem Afun_even (k : ℕ) : Afun (2 * k) = 5 * k := by unfold Afun; omega
private theorem Afun_odd (k : ℕ) : Afun (2 * k + 1) = 5 * k + 3 := by unfold Afun; omega
private theorem Apr_even (k : ℕ) : Apr (2 * k) = 5 * k + 1 := by unfold Apr; omega
private theorem Apr_odd (k : ℕ) : Apr (2 * k + 1) = 5 * k + 3 := by unfold Apr; omega

private def x1v (t : ℕ) : ℕ := pw (t + 2) - 2
private def yv (t : ℕ) : ℕ := pw (Afun (t + 1)) * (2 * x1v t + 1)
private def zv (t r : ℕ) : ℕ := yv t + 2 * pw r - 1
private def y2v (t r : ℕ) : ℕ := pw (Apr r) * (2 * zv t r + 1)

private def D1 (m : ℕ) (Cs : Side) (W : ℕ) : Cfg Sym (Fin 6) :=
  AC (TL (bin m 1) (S1 >> Cs)) (bin W 1)

private theorem pw_ge2 (t : ℕ) : 2 ≤ pw (t + 1) := by
  rw [pw_S]; have := pw_pos t; omega

private theorem d1_skip (t : ℕ) (Cs : Side) (W : ℕ) (h : t + 2 ≤ W) :
    ReachesPlus tm (D1 (t + 1) Cs W) (EC (TL (oL (t + 1)) (S1 >> Cs)) (bin W (x1v t))) := by
  unfold D1 x1v
  have h2 := pw_ge2 t
  have h3 := pw_le (t + 2) W h
  have hs : pw (t + 2) = 2 * pw (t + 1) := pw_S (t + 1)
  have sp := skip_plain (pw (t + 1) - 2) (t + 1) W 1 1 (S1 >> Cs) (by omega) (by omega)
  have hv : 1 + (pw (t + 1) - 2) = pw (t + 1) - 1 := by omega
  rw [hv, bin_ones] at sp
  have hx : pw (t + 2) - 2 = (1 + 2 * (pw (t + 1) - 2)) + 1 := by omega
  rw [hx]
  exact ReachesStar.trans_plus sp (phase1 _ _ (inc_bin W _ (by omega)) _)

private theorem stage_even (t k : ℕ) (N : Side) (W : ℕ) (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W) :
    ReachesPlus tm (D1 (t + 1) (S0 >> N) W) (EC N (bin (Afun (t + 1) + (W + 1)) (yv t))) := by
  have h1 := ReachesPlus.trans (d1_skip t (S0 >> N) W hW) (R0 (t + 1) N (bin W (x1v t)))
  have hm : 5 * (t + 1) + 2 = 2 * (5 * k + 1) := by omega
  rw [hm] at h1
  have h2 := after_even (5 * k) N (bin W (x1v t))
  have h3 := ReachesPlus.trans_star h1 h2
  have hrhs : bin (Afun (t + 1) + (W + 1)) (yv t) = zL (5 * k) ++ true :: bin W (x1v t) := by
    unfold yv; rw [hk, Afun_even, bin_split]
  rwa [hrhs]

private theorem stage_odd (t k : ℕ) (L : Side) (W : ℕ) (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W) :
    ReachesPlus tm (D1 (t + 1) (S0 >> S0 >> L) W) (AC L (bin (Afun (t + 1) + (W + 1)) (yv t))) := by
  have h1 := ReachesPlus.trans (d1_skip t (S0 >> S0 >> L) W hW)
    (R0 (t + 1) (S0 >> L) (bin W (x1v t)))
  have hm : 5 * (t + 1) + 2 = 2 * (5 * k + 3) + 1 := by omega
  rw [hm] at h1
  have hrhs : bin (Afun (t + 1) + (W + 1)) (yv t) = zL (5 * k + 3) ++ true :: bin W (x1v t) := by
    unfold yv; rw [hk, Afun_odd, bin_split]
  rw [hrhs]
  exact ReachesPlus.trans h1 (after_odd (5 * k + 3) L (bin W (x1v t)))

private theorem Cs_form (r c1 C1 : ℕ) (T : Side) :
    TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) T =
      zeros (5 * r + 4) (S1 >> TL (bin c1 C1) T) := by
  rw [bin_split, TL_app]
  simp only [TL, TL_zL, tok_true, zeros_add]

private theorem tokS_form (r c1 C1 : ℕ) (T : Side) :
    TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) T = S0 >> TL (zL r) (U (TL (bin c1 C1) T)) := by
  rw [Cs_form, TL_zL, U_zeros]
  change zeros (5 * r + 4) _ = zeros 1 (zeros (5 * r) (zeros 3 _))
  rw [zeros_add, zeros_add]
  congr 1; omega

private theorem tokD3_form (r c1 C1 : ℕ) (T : Side) :
    TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) T =
      S0 >> S0 >> TL (zL r) (D3 (TL (bin c1 C1) T)) := by
  rw [Cs_form, TL_zL, D3_zeros]
  change zeros (5 * r + 4) _ = zeros 2 (zeros (5 * r) (zeros 2 _))
  rw [zeros_add, zeros_add]
  congr 1; omega

private theorem N_tz (D : ℕ) (h : D ≠ 0) : ∃ t C, D = pw t * (2 * C + 1) := by
  induction D using Nat.strongRecOn with
  | ind p ih =>
    rcases N_parity p with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · obtain ⟨t, C, hc⟩ := ih w (by omega) (by omega)
      exact ⟨t + 1, C, by rw [pw_S, hc]; ring⟩
    · exact ⟨0, w, by rw [pw_0]; ring⟩

private theorem tz_bound (u t C : ℕ) (h : pw t * (2 * C + 1) < pw u) :
    ∃ c, u = t + (c + 1) ∧ C < pw c := by
  have ht : t < u := by
    by_contra hge
    have hp := pw_le u t (by omega)
    have hpos := pw_pos t
    nlinarith
  refine ⟨u - (t + 1), by omega, ?_⟩
  have hu : u = t + (u - (t + 1) + 1) := by omega
  rw [hu, pw_add, pw_S] at h
  have hpos := pw_pos t
  nlinarith

private theorem cut_sweep (r c1 C1 : ℕ) (T : Side) (x x2 : List Bool)
    (hx : inc x = some x2) (hc : pw r * (2 * C1 + 1) + 1 < pw (r + (c1 + 1))) :
    ∃ low hi, low ++ true :: hi = bin (r + (c1 + 1)) (pw r * (2 * C1 + 1) + 1) ∧
      ReachesPlus tm (EC (TL (zL r) (U (TL (bin c1 C1) T))) x) (AC (TL low (U (TL hi T))) x2) := by
  cases r with
  | zero =>
    rw [pw_0, Nat.one_mul, Nat.zero_add, pw_S] at hc
    have hi_bin := inc_bin c1 C1 (by omega)
    obtain ⟨i, rest, e1, e2⟩ := inc_form (bin c1 C1) (bin c1 (C1 + 1)) hi_bin
    refine ⟨zL (i + 1), rest, ?_, ?_⟩
    · rw [pw_0, Nat.one_mul, Nat.zero_add]
      have hev : 2 * C1 + 1 + 1 = 2 * (C1 + 1) := by omega
      rw [hev, bin_even, e2]; rfl
    · rw [e1, TL_app]
      simp only [zL, List.replicate_zero, TL]
      have ec := E_cross 0 i (TL rest T) x
      rw [Nat.zero_add] at ec
      exact ReachesPlus.trans ec (phase2 x x2 hx _)
  | succ r' =>
    refine ⟨true :: zL r', bin c1 C1, ?_, ?_⟩
    · have hod : pw (r' + 1) * (2 * C1 + 1) + 1 = 2 * (pw r' * (2 * C1 + 1)) + 1 := by
        rw [pw_S]; ring
      rw [hod, Nat.succ_add, bin_odd, bin_split]; rfl
    · have hz : zL (r' + 1) = false :: zL r' := rfl
      rw [hz, TL, tok_false]
      exact ReachesPlus.trans (E5 _ x) (phase2 x x2 hx _)

private theorem stage_E (t k r c1 C1 : ℕ) (T : Side) (W : ℕ)
    (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W)
    (hy : yv t + 1 < pw (Afun (t + 1) + (W + 1)))
    (hc : pw r * (2 * C1 + 1) + 1 < pw (r + (c1 + 1))) :
    ∃ low hi, low ++ true :: hi = bin (r + (c1 + 1)) (pw r * (2 * C1 + 1) + 1) ∧
      ReachesPlus tm (D1 (t + 1) (TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) T) W)
        (MXC T low hi (Afun (t + 1) + (W + 1)) (yv t + 1)) := by
  have hi2 := inc_bin (Afun (t + 1) + (W + 1)) (yv t) hy
  obtain ⟨low, hi, e1, e2⟩ := cut_sweep r c1 C1 T _ _ hi2 hc
  refine ⟨low, hi, e1, ?_⟩
  rw [tokS_form]
  exact ReachesPlus.trans (stage_even t k _ W hk hW) e2

private theorem stage_Vover (t k c1 W : ℕ)
    (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W)
    (hy : yv t + 1 < pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm (D1 (t + 1) (TL (bin (c1 + 1) (pw (c1 + 1) - 1)) (U B0)) W)
      (AC (TL (zL (c1 + 2)) (D3 B0)) (bin (Afun (t + 1) + (W + 1)) (yv t + 1))) := by
  have hi2 := inc_bin (Afun (t + 1) + (W + 1)) (yv t) hy
  rw [bin_ones]
  have htl : TL (oL (c1 + 1)) (U B0) = S0 >> U (TL (oL c1) (U B0)) := rfl
  rw [htl]
  have h1 := stage_even t k (U (TL (oL c1) (U B0))) W hk hW
  have h2 := E_absorb 0 c1 (bin (Afun (t + 1) + (W + 1)) (yv t))
  rw [Nat.zero_add] at h2
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (phase2 _ _ hi2 _))

private theorem stage_Oc (t k r c1 C1 : ℕ) (T : Side) (W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t r < pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm (D1 (t + 1) (TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) T) W)
      (EC (TL (oL r) (D3 (TL (bin c1 C1) T))) (bin (Afun (t + 1) + (W + 1)) (zv t r))) := by
  rw [tokD3_form]
  have h1 := stage_odd t k (TL (zL r) (D3 (TL (bin c1 C1) T))) W hk hW
  have hr := pw_pos r
  unfold zv at hz ⊢
  have sp := skip_plain (pw r - 1) r (Afun (t + 1) + (W + 1)) 0 (yv t) (D3 (TL (bin c1 C1) T))
    (by omega) (by omega)
  rw [bin_zero r, Nat.zero_add, bin_ones] at sp
  have hz_eq : yv t + 2 * pw r - 1 = (yv t + 2 * (pw r - 1)) + 1 := by omega
  rw [hz_eq]
  exact ReachesPlus.trans h1 (ReachesStar.trans_plus sp (phase1 _ _ (inc_bin _ _ (by omega)) _))

private theorem stage_O0 (t k j r2 c2 C2 : ℕ) (T : Side) (W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j) < pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
        (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) T) W)
      (MXC T (zL r2) (bin c2 C2) (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)) (y2v t (2 * j))) := by
  have h1 := stage_Oc t k (2 * j) (r2 + (c2 + 1)) (pw r2 * (2 * C2 + 1)) T W hk hW hz
  conv at h1 => arg 3; rw [tokS_form]
  have h2 := R2 (2 * j) (S0 >> TL (zL r2) (U (TL (bin c2 C2) T)))
    (bin (Afun (t + 1) + (W + 1)) (zv t (2 * j)))
  have hm : 5 * (2 * j) + 3 = 2 * (5 * j + 1) + 1 := by omega
  rw [hm] at h2
  have hrhs : MXC T (zL r2) (bin c2 C2)
      (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)) (y2v t (2 * j)) =
      AC (TL (zL r2) (U (TL (bin c2 C2) T)))
        (zL (5 * j + 1) ++ true :: bin (Afun (t + 1) + (W + 1)) (zv t (2 * j))) := by
    unfold MXC y2v; rw [Apr_even, bin_split]
  rw [hrhs]
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (after_odd (5 * j + 1) _ _))

private theorem stage_O1 (t k j c1 C1 : ℕ) (T : Side) (W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j + 1) < pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) T) W)
      (EC (TL (bin c1 C1) T)
        (bin (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)) (y2v t (2 * j + 1)))) := by
  have h1 := stage_Oc t k (2 * j + 1) c1 C1 T W hk hW hz
  have h2 := R2 (2 * j + 1) (TL (bin c1 C1) T)
    (bin (Afun (t + 1) + (W + 1)) (zv t (2 * j + 1)))
  have hm : 5 * (2 * j + 1) + 3 = 2 * ((5 * j + 3) + 1) := by omega
  rw [hm] at h2
  have h3 := after_even (5 * j + 3) (TL (bin c1 C1) T)
    (bin (Afun (t + 1) + (W + 1)) (zv t (2 * j + 1)))
  have hrhs : bin (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)) (y2v t (2 * j + 1)) =
      zL (5 * j + 3) ++ true :: bin (Afun (t + 1) + (W + 1)) (zv t (2 * j + 1)) := by
    unfold y2v; rw [Apr_odd, bin_split]
  rw [hrhs]
  exact ReachesPlus.trans h1 (ReachesPlus.trans_star h2 h3)

private theorem ovf1_cut (u D : ℕ) (T : Side) (W : ℕ) (h0 : D ≠ 0) (h1 : D + 1 < pw u) :
    ∃ low hi, low ++ true :: hi = bin u (D + 1) ∧
      ReachesPlus tm (AC (TL (bin u D) T) (oL (W + 1))) (MXC T low hi (W + 2) 2) := by
  obtain ⟨t, C, rfl⟩ := N_tz D h0
  obtain ⟨c, rfl, hc⟩ := tz_bound u t C (by omega)
  have hx : inc (true :: zL (W + 1)) = some (bin (W + 2) 2) := by
    rw [← bin_zero (W + 1)]
    change inc (bin ((W + 1) + 1) (2 * 0 + 1)) = some (bin ((W + 1) + 1) (1 + 1))
    rw [bin_odd]
    exact inc_bin (W + 2) 1 (by rw [pw_S, pw_S]; have := pw_pos W; omega)
  obtain ⟨low, hi, e1, e2⟩ := cut_sweep t c C T _ _ hx h1
  refine ⟨low, hi, e1, ?_⟩
  rw [tokS_form]
  exact ReachesPlus.trans (ovf1 (W + 1) _) e2

private theorem of2 (t c C : ℕ) (R : Side) (W' : ℕ) (h : pw t * (2 * C + 1) < pw (t + (c + 1))) :
    ReachesPlus tm (EC (TL (bin (t + (c + 1)) (pw t * (2 * C + 1) - 1)) R) (oL (W' + 1)))
      (D1 (t + 1) (TL (bin c C) R) (W' + 1)) := by
  have hp : 1 ≤ pw t * (2 * C + 1) := by have := pw_pos t; nlinarith
  have h1 := E_step _ _ R (oL (W' + 1)) (inc_bin (t + (c + 1)) (pw t * (2 * C + 1) - 1) (by omega))
  have heq : pw t * (2 * C + 1) - 1 + 1 = pw t * (2 * C + 1) := by omega
  rw [heq] at h1
  have h2 := ovf2 (W' + 1) (S0 >> TL (bin (t + (c + 1)) (pw t * (2 * C + 1))) R)
  have hz : (S0 >> TL (bin (t + (c + 1)) (pw t * (2 * C + 1))) R) =
      zeros 5 (zeros (5 * t) (S1 >> TL (bin c C) R)) := by
    rw [Cs_form]
    change zeros 1 (zeros (5 * t + 4) _) = zeros 5 (zeros (5 * t) _)
    rw [zeros_add, zeros_add]
    congr 1; omega
  conv at h2 => arg 3; rw [hz]
  have h3 := E5 (zeros (5 * t) (S1 >> TL (bin c C) R)) (zL (W' + 1))
  have h4 : ReachesPlus tm
      (BC (S0 >> tok true (zeros (5 * t) (S1 >> TL (bin c C) R))) (zL (W' + 1)))
      (D1 (t + 1) (TL (bin c C) R) (W' + 1)) := by
    unfold D1
    have hb1 : bin (t + 1) 1 = true :: zL t := by
      change bin (t + 1) (2 * 0 + 1) = _; rw [bin_odd, bin_zero]
    have hb2 : bin (W' + 1) 1 = true :: zL W' := by
      change bin (W' + 1) (2 * 0 + 1) = _; rw [bin_odd, bin_zero]
    rw [hb1, hb2]
    simp only [TL, TL_zL]
    exact phase2 (zL (W' + 1)) (true :: zL W') rfl _
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 (ReachesPlus.trans h3 h4))

private theorem mx_pad (low hi : List Bool) (c d V W x : ℕ)
    (h1 : low ++ true :: hi = bin c V) (h2 : V < pw c) :
    low ++ true :: (hi ++ zL d) = bin (c + d) V ∧
      MXC B0 low (hi ++ zL d) W x = MXC B0 low hi W x := by
  refine ⟨?_, ?_⟩
  · have hv : bin (c + d) V = bin (c + d) (V + pw c * 0) := by simp
    rw [hv, bin_app c V 0 d h2, ← h1, bin_zero, List.append_assoc]; rfl
  · unfold MXC; rw [TL_app, TL_zL_B0]

private theorem mx_to_tail (low hi : List Bool) (c u V K Vl W x : ℕ)
    (h1 : low ++ true :: hi = bin c V) (h2 : V < pw c) (h3 : c ≤ u + 1)
    (h4 : V ≤ pw u) (h4b : 1 ≤ V) (h5 : V + K = pw u + Vl) (h6 : Vl < pw u)
    (h7 : x + 2 * K < pw W) :
    ReachesStar tm (MXC B0 low hi W x) (AC (TL (bin u Vl) (U B0)) (bin W (x + 2 * K))) := by
  obtain ⟨e1, e2⟩ := mx_pad low hi c (u + 1 - c) V W x h1 h2
  rw [← e2]
  have hcd : c + (u + 1 - c) = u + (0 + 1) := by omega
  rw [hcd] at e1
  have hu := pw_pos u
  have he1' : low ++ true :: (hi ++ zL (u + 1 - c)) = bin (u + (0 + 1)) (pw u - (pw u - V)) := by
    have hsub : pw u - (pw u - V) = V := by omega
    rwa [hsub]
  have s1 := mix_to_pow (pw u - V) u 0 W x low (hi ++ zL (u + 1 - c)) he1' (by omega) (by omega)
  rw [← bin_zero u] at s1
  have s2 := skip_plain Vl u W 0 (x + 2 * (pw u - V)) (U B0) (by omega) (by omega)
  rw [Nat.zero_add] at s2
  have hx : x + 2 * (pw u - V) + 2 * Vl = x + 2 * K := by omega
  rw [hx] at s2
  exact ReachesStar.trans s1 s2

private theorem dbl_blank (t c C : ℕ) (h1 : pw t * (2 * C + 1) + 1 < pw (t + (c + 1))) :
    ReachesPlus tm (AC (TL (bin (t + (c + 1)) (pw t * (2 * C + 1))) B0) (oL (t + (c + 1))))
      (D1 (t + 1) (TL (bin c C) (U B0)) (t + (c + 1) + 1)) := by
  set c0 := pw t * (2 * C + 1)
  have hp : 1 ≤ c0 := by have := pw_pos t; dsimp [c0]; nlinarith
  set W' := t + c
  have hw : t + (c + 1) = W' + 1 := by omega
  rw [hw] at h1 ⊢
  obtain ⟨low, hi, e1, e2⟩ := ovf1_cut (W' + 1) c0 B0 W' (by omega) h1
  have hs : pw (W' + 2) = 2 * pw (W' + 1) := pw_S (W' + 1)
  have hp2 := pw_pos (W' + 1)
  have mxt := mx_to_tail low hi (W' + 1) (W' + 1) (c0 + 1)
    (pw (W' + 1) - (c0 + 1) + (c0 - 1)) (c0 - 1) (W' + 2) 2
    e1 h1 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have hx : 2 + 2 * (pw (W' + 1) - (c0 + 1) + (c0 - 1)) = pw (W' + 2) - 2 := by omega
  rw [hx] at mxt
  have p1 := phase1 _ _ (inc_bin (W' + 2) (pw (W' + 2) - 2) (by omega))
    (TL (bin (W' + 1) (c0 - 1)) (U B0))
  have hx2 : pw (W' + 2) - 2 + 1 = pw (W' + 2) - 1 := by omega
  rw [hx2, bin_ones] at p1
  have hof : ReachesPlus tm (EC (TL (bin (W' + 1) (c0 - 1)) (U B0)) (oL (W' + 2)))
      (D1 (t + 1) (TL (bin c C) (U B0)) (W' + 2)) := by
    rw [← hw]
    exact of2 t c C (U B0) (W' + 1) (by rw [hw]; omega)
  exact ReachesPlus.trans e2 (ReachesStar.trans_plus mxt (ReachesPlus.trans p1 hof))

private theorem tailL (u D t c3 C3 : ℕ)
    (h0 : D ≠ 0) (h1 : D + 1 < pw u)
    (hZ : pw u + D = pw t * (2 * C3 + 1)) (hu : u + 1 = t + (c3 + 1)) :
    ReachesPlus tm (AC (TL (bin u D) (U B0)) (oL (u + 1)))
      (D1 (t + 1) (TL (bin c3 C3) (D3 B0)) (u + 2)) := by
  obtain ⟨low, hi, e1, e2⟩ := ovf1_cut u D (U B0) u h0 h1
  have hp := pw_pos u
  have hs : pw (u + 1) = 2 * pw u := pw_S u
  have hs2 : pw (u + 2) = 2 * pw (u + 1) := pw_S (u + 1)
  have he1' : low ++ true :: hi = bin u (pw u - 1 - (pw u - 1 - (D + 1))) := by
    have hsub : pw u - 1 - (pw u - 1 - (D + 1)) = D + 1 := by omega
    rwa [hsub]
  obtain ⟨m, i, hm, sm⟩ := mix_to_ones (pw u - 1 - (D + 1)) u (u + 2) 2 (U B0) low hi
    he1' (by omega) (by omega)
  set x0 := 2 + 2 * (pw u - 1 - (D + 1))
  have hx0_eq : x0 = 2 * pw u - 2 * (D + 1) := by dsimp [x0]; omega
  have hx2_inc : inc (bin (u + 2) (x0 + 1)) = some (bin (u + 2) (x0 + 2)) := by
    have h_eq : x0 + 2 = (x0 + 1) + 1 := by omega
    rw [h_eq]; exact inc_bin (u + 2) (x0 + 1) (by omega)
  have ta := tick_absorb m i (bin (u + 2) x0) (bin (u + 2) (x0 + 1)) (bin (u + 2) (x0 + 2))
    (inc_bin (u + 2) x0 (by omega)) hx2_inc
  have hmi : m + i + 2 = u + 1 := by omega
  rw [hmi, ← bin_zero (u + 1)] at ta
  have sp := skip_plain (pw u - 1 + D) (u + 1) (u + 2) 0 (x0 + 2) (D3 B0) (by omega) (by omega)
  rw [Nat.zero_add] at sp
  have p1 : ReachesPlus tm
      (AC (TL (bin (u + 1) (pw u - 1 + D)) (D3 B0)) (bin (u + 2) (x0 + 2 + 2 * (pw u - 1 + D))))
      (EC (TL (bin (t + (c3 + 1)) (pw t * (2 * C3 + 1) - 1)) (D3 B0)) (oL (u + 2))) := by
    have p1_raw := phase1 _ _ (inc_bin (u + 2) (x0 + 2 + 2 * (pw u - 1 + D)) (by omega))
      (TL (bin (u + 1) (pw u - 1 + D)) (D3 B0))
    have hx : x0 + 2 + 2 * (pw u - 1 + D) + 1 = pw (u + 2) - 1 := by omega
    have hv : pw u - 1 + D = pw t * (2 * C3 + 1) - 1 := by omega
    conv at p1_raw => arg 3; rw [hx, bin_ones, hv, hu]
    exact p1_raw
  have hof := of2 t c3 C3 (D3 B0) (u + 1) (by rw [← hu]; omega)
  exact ReachesPlus.trans e2 (ReachesStar.trans_plus sm
    (ReachesPlus.trans ta (ReachesStar.trans_plus sp (ReachesPlus.trans p1 hof))))

private theorem tailS (u Vl : ℕ) (h0 : Vl ≠ 0) (h1 : Vl + 1 < pw u) :
    ReachesPlus tm (AC (TL (bin u Vl) (U B0)) (oL (u + 2)))
      (EC (TL (oL (u + 1)) (D3 B0)) (bin (u + 3) (2 * pw u - 2 * Vl + 2 * pw (u + 1) - 1))) := by
  obtain ⟨low, hi, e1, e2⟩ := ovf1_cut u Vl (U B0) (u + 1) h0 h1
  have hp := pw_pos u
  have hs : pw (u + 1) = 2 * pw u := pw_S u
  have hs2 : pw (u + 2) = 2 * pw (u + 1) := pw_S (u + 1)
  have hs3 : pw (u + 3) = 2 * pw (u + 2) := pw_S (u + 2)
  have he1' : low ++ true :: hi = bin u (pw u - 1 - (pw u - 1 - (Vl + 1))) := by
    have hsub : pw u - 1 - (pw u - 1 - (Vl + 1)) = Vl + 1 := by omega
    rwa [hsub]
  obtain ⟨m, i, hm, sm⟩ := mix_to_ones (pw u - 1 - (Vl + 1)) u (u + 3) 2 (U B0) low hi
    he1' (by omega) (by omega)
  set x0 := 2 + 2 * (pw u - 1 - (Vl + 1))
  have hx0_eq : x0 = 2 * pw u - 2 * (Vl + 1) := by dsimp [x0]; omega
  have hx2_inc : inc (bin (u + 3) (x0 + 1)) = some (bin (u + 3) (x0 + 2)) := by
    have h_eq : x0 + 2 = (x0 + 1) + 1 := by omega
    rw [h_eq]; exact inc_bin (u + 3) (x0 + 1) (by omega)
  have ta := tick_absorb m i (bin (u + 3) x0) (bin (u + 3) (x0 + 1)) (bin (u + 3) (x0 + 2))
    (inc_bin (u + 3) x0 (by omega)) hx2_inc
  have hmi : m + i + 2 = u + 1 := by omega
  rw [hmi, ← bin_zero (u + 1)] at ta
  have sp := skip_plain (pw (u + 1) - 1) (u + 1) (u + 3) 0 (x0 + 2) (D3 B0) (by omega) (by omega)
  rw [Nat.zero_add, bin_ones] at sp
  have p1 := phase1 _ _ (inc_bin (u + 3) (x0 + 2 + 2 * (pw (u + 1) - 1)) (by omega))
    (TL (oL (u + 1)) (D3 B0))
  have hx : x0 + 2 + 2 * (pw (u + 1) - 1) + 1 = 2 * pw u - 2 * Vl + 2 * pw (u + 1) - 1 := by omega
  rw [hx] at p1
  exact ReachesPlus.trans e2
    (ReachesStar.trans_plus sm (ReachesPlus.trans ta (ReachesStar.trans_plus sp p1)))

private theorem b_level (low hi : List Bool) (L V Wf x : ℕ)
    (h1 : low ++ true :: hi = bin L V) (h2 : V < pw L) (h3 : x + 2 * (pw L - V) < pw Wf) :
    ReachesPlus tm (MXC (U B0) low hi Wf x)
      (AC (TL (zL (L + 1)) (D3 B0)) (bin Wf (x + 2 * (pw L - V)))) := by
  have h1' : low ++ true :: hi = bin L (pw L - 1 - (pw L - 1 - V)) := by
    have hsub : pw L - 1 - (pw L - 1 - V) = V := by omega
    rwa [hsub]
  obtain ⟨m, i, hm, sm⟩ := mix_to_ones (pw L - 1 - V) L Wf x (U B0) low hi
    h1' (by omega) (by omega)
  set x0 := x + 2 * (pw L - 1 - V)
  have hx2_inc : inc (bin Wf (x0 + 1)) = some (bin Wf (x0 + 2)) := by
    have h_eq : x0 + 2 = (x0 + 1) + 1 := by omega
    rw [h_eq]; exact inc_bin Wf (x0 + 1) (by omega)
  have ta := tick_absorb m i (bin Wf x0) (bin Wf (x0 + 1)) (bin Wf (x0 + 2))
    (inc_bin Wf x0 (by omega)) hx2_inc
  have hmi : m + i + 2 = L + 1 := by omega
  have hx : x0 + 2 = x + 2 * (pw L - V) := by omega
  rw [hmi, hx] at ta
  exact ReachesStar.trans_plus sm ta

private theorem d3_plain (N Wf x : ℕ) (h : x + 2 * pw N - 1 < pw Wf) :
    ReachesPlus tm (AC (TL (zL N) (D3 B0)) (bin Wf x))
      (EC (TL (oL N) (D3 B0)) (bin Wf (x + 2 * pw N - 1))) := by
  have hp := pw_pos N
  rw [← bin_zero N]
  have sp := skip_plain (pw N - 1) N Wf 0 x (D3 B0) (by omega) (by omega)
  rw [Nat.zero_add, bin_ones] at sp
  have p1 := phase1 _ _ (inc_bin Wf (x + 2 * (pw N - 1)) (by omega)) (TL (oL N) (D3 B0))
  have hx : x + 2 * (pw N - 1) + 1 = x + 2 * pw N - 1 := by omega
  rw [hx] at p1
  exact ReachesStar.trans_plus sp p1

private theorem d3_level (low hi : List Bool) (L V Wf x : ℕ)
    (h1 : low ++ true :: hi = bin L V) (h2 : V < pw L) (h3 : x + 2 * (pw L - 1 - V) + 1 < pw Wf) :
    ∃ m i, m + (i + 1) = L ∧
      ReachesPlus tm (MXC (D3 B0) low hi Wf x)
        (EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin Wf (x + 2 * (pw L - 1 - V) + 1))) := by
  have h1' : low ++ true :: hi = bin L (pw L - 1 - (pw L - 1 - V)) := by
    have hsub : pw L - 1 - (pw L - 1 - V) = V := by omega
    rwa [hsub]
  obtain ⟨m, i, hm, sm⟩ := mix_to_ones (pw L - 1 - V) L Wf x (D3 B0) low hi
    h1' (by omega) (by omega)
  exact ⟨m, i, hm, ReachesStar.trans_plus sm (phase1 _ _ (inc_bin Wf _ h3) _)⟩

private def F0 (a h H : ℕ) : Cfg Sym (Fin 6) := AC B0 (zL a ++ true :: bin h H)
private def F1 (a h H : ℕ) : Cfg Sym (Fin 6) :=
  AC (tok true B0) (true :: zL (a - 1) ++ true :: bin h H)

private theorem after_odd_B0 (p : ℕ) (x : List Bool) :
    ReachesPlus tm (ones (2 * p + 1) B0 <{{E}} (S1 >> S1 >> S1 >> X x))
      (AC B0 (zL p ++ true :: x)) := by
  have h := after_odd p B0 x
  rwa [← B0_S0] at h

private theorem after_even_B0 (p : ℕ) (x : List Bool) :
    ReachesPlus tm (ones (2 * (p + 2)) B0 <{{E}} (S1 >> S1 >> S1 >> X x))
      (AC (tok true B0) (true :: zL p ++ true :: x)) := by
  have h1 := after_even (p + 1) B0 x
  have h2 := E5 B0 (zL (p + 1) ++ true :: x)
  rw [zeros_B0] at h2
  have h3 : ReachesPlus tm (BC (S0 >> tok true B0) (zL (p + 1) ++ true :: x))
      (AC (tok true B0) (true :: zL p ++ true :: x)) :=
    phase2 _ _ rfl _
  exact ReachesStar.trans_plus h1 (ReachesPlus.trans h2 h3)

private theorem fin_plain_even (j h H : ℕ) :
    ReachesPlus tm (EC (TL (oL (2 * j)) (D3 B0)) (bin h H)) (F0 (Apr (2 * j)) h H) := by
  unfold F0
  rw [Apr_even]
  have h1 := R2 (2 * j) B0 (bin h H)
  have hm : 5 * (2 * j) + 3 = 2 * (5 * j + 1) + 1 := by omega
  rw [hm] at h1
  exact ReachesPlus.trans h1 (after_odd_B0 (5 * j + 1) (bin h H))

private theorem fin_plain_odd (j h H : ℕ) :
    ReachesPlus tm (EC (TL (oL (2 * j + 1)) (D3 B0)) (bin h H)) (F1 (Apr (2 * j + 1)) h H) := by
  unfold F1
  rw [Apr_odd]
  have h1 := R2 (2 * j + 1) B0 (bin h H)
  have hm : 5 * (2 * j + 1) + 3 = 2 * ((5 * j + 2) + 2) := by omega
  have hs : 5 * j + 3 - 1 = 5 * j + 2 := by omega
  rw [hm] at h1; rw [hs]
  exact ReachesPlus.trans h1 (after_even_B0 (5 * j + 2) (bin h H))

private theorem fin_U_odd (m i j h H : ℕ) (hj : m + i + 1 = 2 * j + 1) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H))
      (F0 (Afun (2 * j + 1)) h H) := by
  unfold F0
  rw [Afun_odd]
  have h1 := R2U m i B0 (bin h H)
  rw [hj] at h1
  have hm : 5 * (2 * j + 1) + 2 = 2 * (5 * j + 3) + 1 := by omega
  rw [hm] at h1
  exact ReachesPlus.trans h1 (after_odd_B0 (5 * j + 3) (bin h H))

private theorem fin_U_even (m i j h H : ℕ) (hj : m + i + 1 = 2 * (j + 1)) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H))
      (F1 (Afun (2 * (j + 1))) h H) := by
  unfold F1
  rw [Afun_even]
  have h1 := R2U m i B0 (bin h H)
  rw [hj] at h1
  have hm : 5 * (2 * (j + 1)) + 2 = 2 * ((5 * j + 4) + 2) := by omega
  have hs : 5 * (j + 1) - 1 = 5 * j + 4 := by omega
  rw [hm] at h1; rw [hs]
  exact ReachesPlus.trans h1 (after_even_B0 (5 * j + 4) (bin h H))

/-! ## Full Macro Round Map -/

private def FC (b : Bool) (a h H : ℕ) : Cfg Sym (Fin 6) := if b then F1 a h H else F0 a h H

private def isEven (n : ℕ) : Bool := n % 2 == 0
private def isOdd (n : ℕ) : Bool := n % 2 == 1

private theorem odd_2j (j : ℕ) : isOdd (2 * j) = false := by
  unfold isOdd
  have h : (2 * j) % 2 = 0 := by omega
  simp [h]

private theorem odd_2j1 (j : ℕ) : isOdd (2 * j + 1) = true := by
  unfold isOdd
  have h : (2 * j + 1) % 2 = 1 := by omega
  simp [h]

private theorem even_2j (j : ℕ) : isEven (2 * j) = true := by
  unfold isEven
  have h : (2 * j) % 2 = 0 := by omega
  simp [h]

private theorem even_2j1 (j : ℕ) : isEven (2 * j + 1) = false := by
  unfold isEven
  have h : (2 * j + 1) % 2 = 1 := by omega
  simp [h]

private theorem fin_plain (N h H : ℕ) :
    ReachesPlus tm (EC (TL (oL N) (D3 B0)) (bin h H)) (FC (isOdd N) (Apr N) h H) := by
  rcases N_parity N with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [odd_2j]; exact fin_plain_even j h H
  · rw [odd_2j1]; exact fin_plain_odd j h H

private theorem fin_U (m i L h H : ℕ) (hL : m + i + 1 = L) :
    ReachesPlus tm (EC (TL (oL m) (U (TL (oL i) (D3 B0)))) (bin h H))
      (FC (isEven L) (Afun L) h H) := by
  rcases N_parity L with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · rw [even_2j]
    cases j with
    | zero => omega
    | succ j => exact fin_U_even m i j h H hL
  · rw [even_2j1]; exact fin_U_odd m i j h H hL

private theorem d3_fin (N Wf x : ℕ) (h : x + 2 * pw N - 1 < pw Wf) :
    ReachesPlus tm (AC (TL (zL N) (D3 B0)) (bin Wf x))
      (FC (isOdd N) (Apr N) Wf (x + 2 * pw N - 1)) :=
  ReachesPlus.trans (d3_plain N Wf x h) (fin_plain N Wf _)

private theorem phase1_full (W x : ℕ) (L : Side) (h : x + 2 = pw W) :
    ReachesPlus tm (AC L (bin W x)) (EC L (oL W)) := by
  have hi : inc (bin W x) = some (oL W) := by
    rw [← bin_ones W]
    have hx : pw W - 1 = x + 1 := by omega
    rw [hx]
    exact inc_bin W x (by omega)
  exact phase1 _ _ hi L

private theorem F0_D1 (a' h G H : ℕ) (hG : G + H + 1 = pw h) :
    ReachesPlus tm (F0 (a' + 1) h H) (D1 (a' + 1) (TL (bin h G) B0) (a' + (h + 1) + 1)) := by
  unfold F0
  have hbs : zL (a' + 1) ++ true :: bin h H =
      bin ((a' + 1) + (h + 1)) (pw (a' + 1) * (2 * H + 1)) :=
    (bin_split (a' + 1) h H).symm
  have heqw : (a' + 1) + (h + 1) = a' + (h + 1) + 1 := by omega
  rw [hbs, heqw]
  set W := a' + (h + 1) + 1
  have pW : pw W = 4 * (pw a' * pw h) := by
    have : W = (a' + (h + 1)) + 1 := rfl
    rw [this, pw_S, pw_add, pw_S]; ring
  have hz : pw a' * G + pw a' * H + pw a' = pw a' * pw h := by
    have := congrArg (pw a' * ·) hG; linarith
  have ha := pw_pos a'
  have hh := pw_pos h
  have hpad : TL (bin (h + 1) G) B0 = TL (bin h G) B0 := TL_bin_pad h 1 G (by omega)
  have hof := of2 a' (h + 1) G B0 (a' + (h + 1)) (by
    have : a' + (h + 1 + 1) = W := by omega
    rw [this]; nlinarith)
  have heqw2 : a' + (h + 1 + 1) = W := by omega
  rw [heqw2, hpad] at hof
  rw [pw_S]
  set Z := pw a' * (2 * G + 1)
  have hZ : Z = 2 * (pw a' * G) + pw a' := by dsimp [Z]; ring
  have hH_lin : 2 * pw a' * (2 * H + 1) = 4 * (pw a' * H) + 2 * pw a' := by ring
  have hb0 : B0 = TL (bin W 0) B0 := by rw [bin_zero, TL_zL_B0]
  conv_lhs => rw [hb0]
  have sp := skip_plain (Z - 1) W W 0 (2 * pw a' * (2 * H + 1)) B0 (by omega) (by omega)
  rw [Nat.zero_add] at sp
  have pf := phase1_full W (2 * pw a' * (2 * H + 1) + 2 * (Z - 1))
    (TL (bin W (Z - 1)) B0) (by omega)
  exact ReachesStar.trans_plus sp (ReachesPlus.trans pf hof)

private theorem F1_D1 (a' h G H : ℕ) (hG : G + H + 1 = pw h) :
    ReachesPlus tm (F1 (a' + 1) h H)
      (D1 (a' + 1) (TL (bin (h + 1) G) (U B0)) (a' + (h + 1) + 2)) := by
  unfold F1
  have hsa : a' + 1 - 1 = a' := by omega
  rw [hsa]
  set W := a' + (h + 1) + 1
  have hdig : true :: zL a' ++ true :: bin h H = bin W (2 * (pw a' * (2 * H + 1)) + 1) := by
    change _ = bin ((a' + (h + 1)) + 1) _
    rw [bin_odd, bin_split]; rfl
  have htok : tok true B0 = TL (bin W 1) B0 := by
    have : bin W 1 = true :: bin (a' + (h + 1)) 0 := by
      change bin ((a' + (h + 1)) + 1) (2 * 0 + 1) = _; rw [bin_odd]
    rw [this, bin_zero]
    simp only [TL, TL_zL_B0]
  rw [hdig, htok]
  have pW : pw W = 4 * (pw a' * pw h) := by
    change pw ((a' + (h + 1)) + 1) = _
    rw [pw_S, pw_add, pw_S]; ring
  have hz : pw a' * G + pw a' * H + pw a' = pw a' * pw h := by
    have := congrArg (pw a' * ·) hG; linarith
  have ha := pw_pos a'
  have hh := pw_pos h
  set Z := pw a' * (2 * G + 1)
  have hZ : Z = 2 * (pw a' * G) + pw a' := by dsimp [Z]; ring
  have hH_lin : pw a' * (2 * H + 1) = 2 * (pw a' * H) + pw a' := by ring
  have sp := skip_plain (Z - 1) W W 1 (2 * (pw a' * (2 * H + 1)) + 1) B0 (by omega) (by omega)
  have hv : 1 + (Z - 1) = Z := by omega
  have hx : 2 * (pw a' * (2 * H + 1)) + 1 + 2 * (Z - 1) = pw W - 1 := by omega
  rw [hv, hx, bin_ones] at sp
  have hd := dbl_blank a' (h + 1) G (by
    have : a' + (h + 1 + 1) = W := by omega
    rw [this]; omega)
  have heqw : a' + (h + 1 + 1) = W := by omega
  rw [heqw] at hd
  exact ReachesStar.trans_plus sp hd

private theorem a_E1_tail (t k r c1 C1 W K u Vl : ℕ)
    (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W)
    (hc : pw r * (2 * C1 + 1) < pw (r + (c1 + 1)))
    (hx : yv t + 1 + 2 * K + 1 = pw (Afun (t + 1) + (W + 1)))
    (hc_u : r + (c1 + 1) + 1 ≤ u + 1)
    (hv : pw r * (2 * C1 + 1) + 1 ≤ pw u)
    (hK : pw r * (2 * C1 + 1) + 1 + K = pw u + Vl)
    (hVl : Vl < pw u) :
    ReachesPlus tm (D1 (t + 1) (TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) B0) W)
      (AC (TL (bin u Vl) (U B0)) (oL (Afun (t + 1) + (W + 1)))) := by
  rw [← TL_bin_pad (r + (c1 + 1)) 1 _ hc]
  have heq : r + (c1 + 1) + 1 = r + ((c1 + 1) + 1) := by omega
  rw [heq]
  have hc2 : pw r * (2 * C1 + 1) + 1 < pw (r + ((c1 + 1) + 1)) := by
    have : r + ((c1 + 1) + 1) = (r + (c1 + 1)) + 1 := by omega
    rw [this, pw_S]; have := pw_pos (r + (c1 + 1)); omega
  obtain ⟨low, hi, e1, e2⟩ := stage_E t k r (c1 + 1) C1 B0 W hk hW (by omega) hc2
  have mxt := mx_to_tail low hi (r + ((c1 + 1) + 1)) u (pw r * (2 * C1 + 1) + 1) K Vl
    (Afun (t + 1) + (W + 1)) (yv t + 1) e1 hc2 (by omega) hv (by omega) hK hVl (by omega)
  have hones : yv t + 1 + 2 * K = pw (Afun (t + 1) + (W + 1)) - 1 := by omega
  rw [hones, bin_ones] at mxt
  exact ReachesPlus.trans_star e2 mxt

private theorem a_O0_next (t k j r2 c2 C2 W K u t' c' C' W2 : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j) < pw (Afun (t + 1) + (W + 1)))
    (hW2 : Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1) = W2 + 1)
    (hx : y2v t (2 * j) + 2 * K + 2 = pw (W2 + 1))
    (hc : pw r2 * (2 * C2 + 1) < pw (r2 + (c2 + 1)))
    (hcu : r2 + (c2 + 1) ≤ u + 1)
    (hv1 : 1 ≤ pw r2 * (2 * C2 + 1))
    (hv : pw r2 * (2 * C2 + 1) ≤ pw u)
    (hK : pw r2 * (2 * C2 + 1) + K + 1 = pw u + pw t' * (2 * C' + 1))
    (hu : u = t' + (c' + 1))
    (hZ : pw t' * (2 * C' + 1) < pw u) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
        (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) B0) W)
      (D1 (t' + 1) (TL (bin c' C') (U B0)) (W2 + 1)) := by
  have s0 := stage_O0 t k j r2 c2 C2 B0 W hk hW hz
  rw [hW2] at s0
  have hp : 1 ≤ pw t' * (2 * C' + 1) := by have := pw_pos t'; nlinarith
  have mxt := mx_to_tail (zL r2) (bin c2 C2) (r2 + (c2 + 1)) u (pw r2 * (2 * C2 + 1)) K
    (pw t' * (2 * C' + 1) - 1) (W2 + 1) (y2v t (2 * j))
    (bin_split r2 c2 C2).symm hc hcu hv hv1 (by omega) (by omega) (by omega)
  have pf := phase1_full (W2 + 1) (y2v t (2 * j) + 2 * K)
    (TL (bin u (pw t' * (2 * C' + 1) - 1)) (U B0)) hx
  subst hu
  exact ReachesPlus.trans s0
    (ReachesStar.trans_plus mxt (ReachesPlus.trans pf (of2 t' c' C' (U B0) W2 hZ)))

private theorem a_O1_next (t k j c1 C1 W K t' c' C' : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j + 1) < pw (Afun (t + 1) + (W + 1)))
    (hx : y2v t (2 * j + 1) + 1 + 2 * K + 1 = pw (t' + (c' + 1)))
    (hW2 : Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1) = t' + (c' + 1))
    (hc : c1 ≤ t' + (c' + 1))
    (hc1 : C1 < pw c1)
    (hc2 : C1 + 1 < pw (t' + (c' + 1)))
    (hK : C1 + 1 + K = pw t' * (2 * C' + 1))
    (hZ : pw t' * (2 * C' + 1) + 1 < pw (t' + (c' + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) B0) W)
      (D1 (t' + 1) (TL (bin c' C') (U B0)) (t' + (c' + 1) + 1)) := by
  have s0 := stage_O1 t k j c1 C1 B0 W hk hW hz
  rw [hW2] at s0
  have hpad : TL (bin c1 C1) B0 = TL (bin (t' + (c' + 1)) C1) B0 := by
    have : t' + (c' + 1) = c1 + (t' + (c' + 1) - c1) := by omega
    rw [this]; exact (TL_bin_pad c1 _ C1 hc1).symm
  rw [hpad] at s0
  set W2 := t' + (c' + 1)
  have e1 := E_step _ _ B0 (bin W2 (y2v t (2 * j + 1))) (inc_bin W2 C1 hc2)
  have p2 := phase2 _ _ (inc_bin W2 (y2v t (2 * j + 1)) (by omega)) (S0 >> TL (bin W2 (C1 + 1)) B0)
  have sp := skip_plain K W2 W2 (C1 + 1) (y2v t (2 * j + 1) + 1) B0 (by omega) (by omega)
  have hx2 : y2v t (2 * j + 1) + 1 + 2 * K = pw W2 - 1 := by omega
  rw [hK, hx2, bin_ones] at sp
  exact ReachesPlus.trans s0 (ReachesPlus.trans e1 (ReachesPlus.trans p2
    (ReachesStar.trans_plus sp (dbl_blank t' c' C' hZ))))

private theorem b_E1 (t k c C W : ℕ)
    (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W) (h0 : C ≠ 0) (hc : C < pw c)
    (hx : yv t + 1 + 2 * (pw c - (C + 1)) < pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm (D1 (t + 1) (TL (bin c C) (U B0)) W)
      (AC (TL (zL (c + 1)) (D3 B0))
        (bin (Afun (t + 1) + (W + 1)) (yv t + 1 + 2 * (pw c - (C + 1))))) := by
  by_cases heq : C + 1 = pw c
  · cases c with
    | zero => rw [pw_0] at hc; omega
    | succ c1 =>
      have hc' : C = pw (c1 + 1) - 1 := by omega
      subst hc'
      have hp := pw_pos (c1 + 1)
      have hsub : yv t + 1 + 2 * (pw (c1 + 1) - (pw (c1 + 1) - 1 + 1)) = yv t + 1 := by omega
      rw [hsub] at hx ⊢
      exact stage_Vover t k c1 W hk hW hx
  · obtain ⟨r, C1, rfl⟩ := N_tz C h0
    obtain ⟨c1, rfl, hb⟩ := tz_bound c r C1 hc
    obtain ⟨low, hi, e1, e2⟩ := stage_E t k r c1 C1 (U B0) W hk hW (by omega) (by omega)
    exact ReachesPlus.trans e2 (b_level low hi (r + (c1 + 1)) (pw r * (2 * C1 + 1) + 1)
      (Afun (t + 1) + (W + 1)) (yv t + 1) e1 (by omega) hx)

private theorem b_O0 (t k j r2 c2 C2 W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j) < pw (Afun (t + 1) + (W + 1)))
    (hc : pw r2 * (2 * C2 + 1) < pw (r2 + (c2 + 1)))
    (hx : y2v t (2 * j) + 2 * (pw (r2 + (c2 + 1)) - pw r2 * (2 * C2 + 1)) <
        pw (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
        (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (U B0)) W)
      (AC (TL (zL (r2 + (c2 + 1) + 1)) (D3 B0))
        (bin (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1))
          (y2v t (2 * j) + 2 * (pw (r2 + (c2 + 1)) - pw r2 * (2 * C2 + 1))))) := by
  have s0 := stage_O0 t k j r2 c2 C2 (U B0) W hk hW hz
  exact ReachesPlus.trans s0 (b_level (zL r2) (bin c2 C2) (r2 + (c2 + 1)) (pw r2 * (2 * C2 + 1))
    _ (y2v t (2 * j)) (bin_split r2 c2 C2).symm hc hx)

private theorem b_O1 (t k j c1 C1 W K u Vl : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j + 1) < pw (Afun (t + 1) + (W + 1)))
    (hc : C1 < pw c1)
    (hx : y2v t (2 * j + 1) + 1 + 2 * K + 1 = pw (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)))
    (hcu : c1 + 2 ≤ u + 1)
    (hv : C1 + 1 + pw c1 ≤ pw u)
    (hK : C1 + 1 + pw c1 + K = pw u + Vl)
    (hVl : Vl < pw u) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) (U B0)) W)
      (AC (TL (bin u Vl) (U B0)) (oL (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)))) := by
  have s0 := stage_O1 t k j c1 C1 (U B0) W hk hW hz
  set W2 := Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)
  set y2 := y2v t (2 * j + 1)
  have hi := inc_bin W2 y2 (by omega)
  have hp1 := pw_pos c1
  rw [← bin_ones W2]
  have hones : pw W2 - 1 = (y2 + 1) + 2 * K := by omega
  rw [hones]
  by_cases heq : C1 + 1 = pw c1
  · have hc' : C1 = pw c1 - 1 := by omega
    subst hc'
    rw [bin_ones] at s0
    have ec := E_cross c1 0 B0 (bin W2 y2)
    rw [zeros_B0, Nat.add_zero] at ec
    simp only [oL, List.replicate_zero, TL] at ec
    have p2 := phase2 _ _ hi (S0 >> TL (zL (c1 + 1)) (U B0))
    have mxt := mx_to_tail (zL (c1 + 1)) [] ((c1 + 1) + 1) u (pw (c1 + 1)) K Vl W2 (y2 + 1)
      (by simpa [zL] using (bin_pow (c1 + 1) 0).symm)
      (by rw [pw_S ((c1 + 1))]; have := pw_pos (c1 + 1); omega)
      (by omega)
      (by rw [pw_S]; omega)
      (by rw [pw_S]; omega)
      (by rw [pw_S]; omega)
      hVl (by omega)
    exact ReachesPlus.trans s0 (ReachesPlus.trans ec (ReachesPlus.trans_star p2 mxt))
  · have es := E_step _ _ (U B0) (bin W2 y2) (inc_bin c1 C1 (by omega))
    have p2 := phase2 _ _ hi (S0 >> TL (bin c1 (C1 + 1)) (U B0))
    have mxt := mx_to_tail (bin c1 (C1 + 1)) [] (c1 + 1) u (C1 + 1 + pw c1) K Vl W2 (y2 + 1)
      (by
        have : C1 + 1 + pw c1 = (C1 + 1) + pw c1 * 1 := by omega
        rw [this, bin_app c1 (C1 + 1) 1 1 (by omega)]; rfl)
      (by rw [pw_S]; omega)
      (by omega) hv (by omega) hK hVl (by omega)
    exact ReachesPlus.trans s0 (ReachesPlus.trans es (ReachesPlus.trans_star p2 mxt))

private theorem d3_E1 (t k r c1 C1 W : ℕ)
    (hk : t + 1 = 2 * k) (hW : t + 2 ≤ W)
    (hc : pw r * (2 * C1 + 1) + 1 < pw (r + (c1 + 1)))
    (hx : yv t + 1 + 2 * (pw (r + (c1 + 1)) - 1 - (pw r * (2 * C1 + 1) + 1)) + 1 <
        pw (Afun (t + 1) + (W + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) (D3 B0)) W)
      (FC (isEven (r + (c1 + 1))) (Afun (r + (c1 + 1))) (Afun (t + 1) + (W + 1))
        (yv t + 1 + 2 * (pw (r + (c1 + 1)) - 1 - (pw r * (2 * C1 + 1) + 1)) + 1)) := by
  obtain ⟨low, hi, e1, e2⟩ := stage_E t k r c1 C1 (D3 B0) W hk hW (by omega) hc
  obtain ⟨m, i, hm, sm⟩ := d3_level low hi (r + (c1 + 1)) (pw r * (2 * C1 + 1) + 1)
    (Afun (t + 1) + (W + 1)) (yv t + 1) e1 hc hx
  exact ReachesPlus.trans e2 (ReachesPlus.trans sm (fin_U m i (r + (c1 + 1)) _ _ (by omega)))

private theorem d3_O0 (t k j r2 c2 C2 W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j) < pw (Afun (t + 1) + (W + 1)))
    (hc : pw r2 * (2 * C2 + 1) < pw (r2 + (c2 + 1)))
    (hx : y2v t (2 * j) + 2 * (pw (r2 + (c2 + 1)) - 1 - pw r2 * (2 * C2 + 1)) + 1 <
        pw (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
        (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (D3 B0)) W)
      (FC (isEven (r2 + (c2 + 1))) (Afun (r2 + (c2 + 1)))
        (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1))
        (y2v t (2 * j) + 2 * (pw (r2 + (c2 + 1)) - 1 - pw r2 * (2 * C2 + 1)) + 1)) := by
  have s0 := stage_O0 t k j r2 c2 C2 (D3 B0) W hk hW hz
  obtain ⟨m, i, hm, sm⟩ := d3_level (zL r2) (bin c2 C2) (r2 + (c2 + 1)) (pw r2 * (2 * C2 + 1))
    _ (y2v t (2 * j)) (bin_split r2 c2 C2).symm hc hx
  exact ReachesPlus.trans s0 (ReachesPlus.trans sm (fin_U m i (r2 + (c2 + 1)) _ _ (by omega)))

private theorem d3_O1 (t k j c1 C1 W : ℕ)
    (hk : t + 1 = 2 * k + 1) (hW : t + 2 ≤ W)
    (hz : zv t (2 * j + 1) < pw (Afun (t + 1) + (W + 1)))
    (hc : C1 + 1 < pw c1)
    (hx : y2v t (2 * j + 1) + 1 + 2 * (pw c1 - 1 - (C1 + 1)) + 1 <
        pw (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1))) :
    ReachesPlus tm
      (D1 (t + 1) (TL (bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) (D3 B0)) W)
      (FC (isOdd c1) (Apr c1) (Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1))
        (y2v t (2 * j + 1) + 1 + 2 * (pw c1 - 1 - (C1 + 1)) + 1)) := by
  have s0 := stage_O1 t k j c1 C1 (D3 B0) W hk hW hz
  set W2 := Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)
  set y2 := y2v t (2 * j + 1)
  have hp1 := pw_pos c1
  have es := E_step _ _ (D3 B0) (bin W2 y2) (inc_bin c1 C1 hc)
  have p2 := phase2 _ _ (inc_bin W2 y2 (by omega)) (S0 >> TL (bin c1 (C1 + 1)) (D3 B0))
  have sp := skip_plain (pw c1 - 1 - (C1 + 1)) c1 W2 (C1 + 1) (y2 + 1) (D3 B0) (by omega) (by omega)
  have hv : C1 + 1 + (pw c1 - 1 - (C1 + 1)) = pw c1 - 1 := by omega
  rw [hv, bin_ones] at sp
  have p1 := phase1 _ _ (inc_bin W2 (y2 + 1 + 2 * (pw c1 - 1 - (C1 + 1))) hx) (TL (oL c1) (D3 B0))
  exact ReachesPlus.trans s0 (ReachesPlus.trans es (ReachesPlus.trans p2
    (ReachesStar.trans_plus sp (ReachesPlus.trans p1 (fin_plain c1 W2 _)))))

private theorem tailS_fin (u Vl : ℕ) (h0 : Vl ≠ 0) (h1 : Vl + 1 < pw u) :
    ReachesPlus tm (AC (TL (bin u Vl) (U B0)) (oL (u + 2)))
      (FC (isOdd (u + 1)) (Apr (u + 1)) (u + 3) (2 * pw u - 2 * Vl + 2 * pw (u + 1) - 1)) :=
  ReachesPlus.trans (tailS u Vl h0 h1) (fin_plain (u + 1) (u + 3) _)

private theorem tailS_top (u Vl : ℕ) (h : Vl + 1 = pw u) (hu : 1 ≤ u) :
    ReachesPlus tm (AC (TL (bin u Vl) (U B0)) (oL (u + 2)))
      (FC (isOdd (u + 1)) (Apr (u + 1)) (u + 3) (2 * pw u - 2 * Vl + 2 * pw (u + 1) - 1)) := by
  have hv : Vl = pw u - 1 := by omega
  subst hv
  rw [bin_ones]
  cases u with
  | zero => omega
  | succ u0 =>
    have htl : TL (oL (u0 + 1)) (U B0) = S0 >> U (TL (oL u0) (U B0)) := rfl
    rw [htl]
    have h1 := ovf1 (u0 + 3) (U (TL (oL u0) (U B0)))
    have hx : inc (true :: zL (u0 + 3)) = some (bin (u0 + 4) 2) := by
      rw [← bin_zero (u0 + 3)]
      change inc (bin ((u0 + 3) + 1) (2 * 0 + 1)) = some (bin ((u0 + 3) + 1) (1 + 1))
      rw [bin_odd]
      exact inc_bin (u0 + 4) 1 (by rw [pw_S, pw_S]; have := pw_pos (u0 + 2); omega)
    have ea := E_absorb 0 u0 (true :: zL (u0 + 3))
    rw [Nat.zero_add] at ea
    have p2 := phase2 _ _ hx (S0 >> TL (zL (u0 + 2)) (D3 B0))
    have p1 : pw (u0 + 2) = 2 * pw (u0 + 1) := pw_S (u0 + 1)
    have p2' : pw (u0 + 3) = 2 * pw (u0 + 2) := pw_S (u0 + 2)
    have p3 : pw (u0 + 4) = 2 * pw (u0 + 3) := pw_S (u0 + 3)
    have p4 := pw_pos (u0 + 1)
    have heq : 2 * pw (u0 + 1) - 2 * (pw (u0 + 1) - 1) + 2 * pw (u0 + 2) - 1 =
        2 + 2 * pw (u0 + 2) - 1 := by omega
    rw [heq]
    exact ReachesPlus.trans h1 (ReachesPlus.trans ea (ReachesPlus.trans p2
      (d3_fin (u0 + 2) (u0 + 4) 2 (by omega))))

/-! ## Run-of-Ones Arithmetic and Popcount Bounds -/

private def ones_on (V p q : ℕ) : Prop :=
  p ≤ q ∧ ∃ a b, b < pw p ∧ V = a * pw q + (pw q - pw p) + b

private def LR (D : ℕ) : Prop :=
  ∃ p q, ones_on D p q ∧ 2 * p + 25 ≤ 5 * (q - p)

private theorem mod_uniq (M a b r s : ℕ) (hr : r < M) (hs : s < M)
    (h : a * M + r = b * M + s) : a = b ∧ r = s := by
  rcases lt_trichotomy a b with hab | rfl | hab
  · exfalso
    have h1 : (a + 1) * M ≤ b * M := Nat.mul_le_mul_right M hab
    nlinarith
  · exact ⟨rfl, by omega⟩
  · exfalso
    have h1 : (b + 1) * M ≤ a * M := Nat.mul_le_mul_right M hab
    nlinarith

private theorem pw_split (a b : ℕ) (h : a ≤ b) : pw b = pw a * pw (b - a) := by
  rw [← pw_add]; congr 1; omega

private theorem ones_sub_lo (V p p' q : ℕ) (h : ones_on V p q) (hp : p ≤ p' ∧ p' ≤ q) :
    ones_on V p' q := by
  obtain ⟨hpq, a, b, hb, hV⟩ := h
  have h1 := pw_le p p' hp.1
  have h2 := pw_le p' q hp.2
  exact ⟨hp.2, a, pw p' - pw p + b, by omega, by omega⟩

private theorem ones_sub_hi (V p q' q : ℕ) (h : ones_on V p q) (hp : p ≤ q' ∧ q' ≤ q) :
    ones_on V p q' := by
  obtain ⟨hpq, a, b, hb, hV⟩ := h
  have h1 := pw_le p q' hp.1
  have h2 := pw_split q' q hp.2
  have h3 := pw_pos (q - q')
  have h4 := pw_pos q'
  set Pd := pw (q - q')
  refine ⟨hp.1, a * Pd + (Pd - 1), b, hb, ?_⟩
  rw [hV, h2]
  have hle : pw p ≤ pw q' * Pd := by nlinarith
  zify [h1, h3, hle]
  ring

private theorem ones_sub (V p p' q' q : ℕ) (h : ones_on V p q)
    (h1 : p ≤ p') (h2 : q' ≤ q) (h3 : p' ≤ q') : ones_on V p' q' :=
  ones_sub_lo V p p' q' (ones_sub_hi V p q' q h ⟨h1.trans h3, h2⟩) ⟨h1, h3⟩

private theorem ones_high (V p q n : ℕ) (h : ones_on V p q) (hn : q ≤ n) :
    ones_on (V + pw n) p q := by
  obtain ⟨hpq, a, b, hb, hV⟩ := h
  have h2 := pw_split q n hn
  refine ⟨hpq, a + pw (n - q), b, hb, ?_⟩
  rw [hV, h2]; ring

private theorem ones_shift_val (V V1 r p q : ℕ) (hV : V = pw r * (2 * V1 + 1))
    (hon : ones_on V p q) (hr : r < p) :
    ones_on V1 (p - (r + 1)) (q - (r + 1)) := by
  obtain ⟨hpq, a, b, hb, hE⟩ := hon
  refine ⟨by omega, ?_⟩
  have hp := pw_split (r + 1) p hr
  have hq := pw_split (r + 1) q (by omega)
  rw [pw_S] at hp hq
  set P1 := pw (p - (r + 1))
  set Q1 := pw (q - (r + 1))
  set R := pw r
  have hR := pw_pos r
  have hPQ : P1 ≤ Q1 := pw_le _ _ (by omega)
  set Xv := a * Q1 + (Q1 - P1)
  have ha : a * pw q + (pw q - pw p) = 2 * R * Xv := by
    have hqp : pw p ≤ pw q := pw_le p q hpq
    rw [hp, hq] at hqp ⊢
    dsimp [Xv]
    zify [hPQ, hqp]
    ring
  have hE2 : R * (2 * V1 + 1) = 2 * R * Xv + b := by linarith
  have hV1 : Xv ≤ V1 := by
    by_contra hlt
    have h3 : V1 + 1 ≤ Xv := by omega
    have h4 : 2 * R * (V1 + 1) ≤ 2 * R * Xv := Nat.mul_le_mul_left (2 * R) h3
    nlinarith
  refine ⟨a, V1 - Xv, ?_, by dsimp [Xv]; omega⟩
  have hbb : b = R + 2 * R * (V1 - Xv) := by
    zify [hV1] at hE2 ⊢
    linarith
  rw [hp] at hb
  nlinarith

private theorem int_sub (A i j Y Yh Yl : ℕ) (hon : ones_on A i j) (hlt : i < j)
    (hY : Y = Yh * pw j + Yl) (hYl : Yl < pw i) (hYA : Y ≤ A) :
    ones_on (A - Y) (i + 1) j := by
  obtain ⟨hij, a, b, hb, hA⟩ := hon
  refine ⟨by omega, ?_⟩
  have h2 := pw_lt i j hlt
  have h1 := pw_pos i
  have hge : Yh ≤ a := by
    by_contra hlt'
    have h3 : (a + 1) * pw j ≤ Yh * pw j := Nat.mul_le_mul_right (pw j) (by omega)
    have h4 : a * pw j + pw j = (a + 1) * pw j := by ring
    omega
  refine ⟨a - Yh, pw i + b - Yl, ?_, ?_⟩
  · rw [pw_S]; omega
  · rw [pw_S]
    have hmul : (a - Yh) * pw j + Yh * pw j = a * pw j := by
      rw [← Nat.add_mul]; congr 1; omega
    omega

private theorem fresh (G Y K0 Q Wf f g Yh Yl : ℕ)
    (hG : G + Y + K0 = pw Wf + Q)
    (hY : Y = Yh * pw g + Yl) (hYl : Yl < pw f) (hK : K0 ≤ pw f) (hQ : Q < K0)
    (hfg : f < g) (hgW : g ≤ Wf) :
    ones_on G (f + 1) g := by
  refine ⟨by omega, ?_⟩
  have hW := pw_split g Wf hgW
  set M := pw (Wf - g)
  have h2 := pw_lt f g hfg
  have h1 := pw_pos f
  set Bv := Yl + K0 - Q
  have hB : G + Yh * pw g + Bv = pw g * M := by dsimp [Bv]; omega
  have hB0 : 0 < Bv := by dsimp [Bv]; omega
  have hB1 : Bv < 2 * pw f := by dsimp [Bv]; omega
  have hM : Yh + 1 ≤ M := by
    by_contra hlt
    have h3 : M * pw g ≤ Yh * pw g := Nat.mul_le_mul_right (pw g) (by omega)
    nlinarith
  refine ⟨M - Yh - 1, 2 * pw f - Bv, ?_, ?_⟩
  · rw [pw_S]; omega
  · rw [pw_S]
    have hcomm : pw g * M = M * pw g := Nat.mul_comm _ _
    have h4 : (M - Yh - 1) * pw g + Yh * pw g + pw g = M * pw g := by
      have : (M - Yh - 1 + Yh + 1) * pw g = M * pw g := by congr 1; omega
      linarith
    omega

private theorem ones_tz (V V1 r p q : ℕ) (hV : V = pw r * (2 * V1 + 1))
    (hon : ones_on V p q) (hlt : p < q) : r ≤ p := by
  obtain ⟨hpq, a, b, hb, hE⟩ := hon
  by_contra hgt
  have hr := pw_split (p + 1) r (by omega)
  have hq := pw_split (p + 1) q hlt
  rw [pw_S] at hr hq
  have h1 := pw_pos p
  set P := pw p
  set R := pw (r - (p + 1))
  set Q1 := pw (q - (p + 1))
  have hQ1 := pw_pos (q - (p + 1))
  have hle_q : P ≤ pw q := pw_le p q hpq
  have hE2 : 2 * P * (R * (2 * V1 + 1)) + P = 2 * P * (a * Q1 + Q1) + b := by
    rw [hq] at hE hle_q
    rw [hr] at hV
    zify [hle_q] at hE ⊢
    linarith
  rcases le_or_gt (a * Q1 + Q1) (R * (2 * V1 + 1)) with hge | hlt'
  · have h4 : 2 * P * (a * Q1 + Q1) ≤ 2 * P * (R * (2 * V1 + 1)) :=
      Nat.mul_le_mul_left (2 * P) hge
    omega
  · have h4 : 2 * P * (R * (2 * V1 + 1) + 1) ≤ 2 * P * (a * Q1 + Q1) :=
      Nat.mul_le_mul_left (2 * P) hlt'
    nlinarith

private def cell1 (V c : ℕ) : Prop := ∃ a b, b < pw c ∧ V = a * pw (c + 1) + pw c + b
private def cell0 (V c : ℕ) : Prop := ∃ a b, b < pw c ∧ V = a * pw (c + 1) + b

private theorem ones_cell (V p q c : ℕ) (h : ones_on V p q) (hc : p ≤ c ∧ c < q) : cell1 V c := by
  obtain ⟨_, a, b, hb, hV⟩ := ones_sub V p c (c + 1) q h hc.1 hc.2 (by omega)
  exact ⟨a, b, hb, by rw [hV, pw_S]; omega⟩

private theorem two_zero (Xv Yv c1 c2 : ℕ) (hc : c1 < c2)
    (hx1 : cell1 Xv c1) (hx2 : cell1 Xv c2) (hy1 : cell0 Yv c1) (hy2 : cell0 Yv c2) :
    Xv ≠ Yv ∧ ∀ x, Xv ≠ Yv + pw x := by
  obtain ⟨cx, dx, hdx, hX1⟩ := hx1
  obtain ⟨ax, bx, hbx, hX2⟩ := hx2
  obtain ⟨cy, dy, hdy, hY1⟩ := hy1
  obtain ⟨ay, by', hby, hY2⟩ := hy2
  have hS2 := pw_S c2
  have hS1 := pw_S c1
  have hP := pw_split (c1 + 1) c2 hc
  rw [hS1] at hP
  set R := pw (c2 - (c1 + 1))
  have hR := pw_pos (c2 - (c1 + 1))
  have h1 := pw_pos c1
  have h2 := pw_pos c2
  have hPP := pw_le c1 c2 (by omega)
  refine ⟨?_, ?_⟩
  · intro heq
    rw [heq, hY2] at hX2
    obtain ⟨_, e2⟩ := mod_uniq (pw (c2 + 1)) ay ax by' (pw c2 + bx) (by omega) (by omega) (by omega)
    omega
  · intro x heq
    rcases le_or_gt x c1 with hx | hx
    · have hxp := pw_le x c1 hx
      have hE : ax * pw (c2 + 1) + (pw c2 + bx) = ay * pw (c2 + 1) + (by' + pw x) := by omega
      obtain ⟨_, e2⟩ := mod_uniq (pw (c2 + 1)) ax ay (pw c2 + bx) (by' + pw x)
        (by omega) (by omega) hE
      have hMul : pw (c2 + 1) = 2 * R * pw (c1 + 1) := by rw [hS2, hS1, hP]; ring
      have hX4 : Xv = (ax * (2 * R) + R) * pw (c1 + 1) + bx := by
        rw [hX2, hMul, hS1, hP]; ring
      have hX5 : (ax * (2 * R) + R) * pw (c1 + 1) + bx = cx * pw (c1 + 1) + (pw c1 + dx) := by
        linarith
      obtain ⟨_, e3⟩ := mod_uniq (pw (c1 + 1)) (ax * (2 * R) + R) cx bx (pw c1 + dx)
        (by omega) (by omega) hX5
      omega
    · have hM : pw x = pw (x - (c1 + 1)) * pw (c1 + 1) := by
        rw [Nat.mul_comm]; exact pw_split (c1 + 1) x hx
      have hE : cx * pw (c1 + 1) + (pw c1 + dx) = (cy + pw (x - (c1 + 1))) * pw (c1 + 1) + dy := by
        rw [Nat.add_mul, ← hM]; omega
      obtain ⟨_, e3⟩ := mod_uniq (pw (c1 + 1)) cx (cy + pw (x - (c1 + 1))) (pw c1 + dx) dy
        (by omega) (by omega) hE
      omega

private theorem ones_not_pow (D p q : ℕ) (h : ones_on D p q) (hq : p + 2 ≤ q) :
    D ≠ 0 ∧ ∀ x, D ≠ pw x := by
  have hz0 : ∀ c, cell0 0 c := fun c => ⟨0, 0, pw_pos c, by simp⟩
  obtain ⟨h1, h2⟩ := two_zero D 0 p (p + 1) (by omega)
    (ones_cell D p q p h (by omega))
    (ones_cell D p q (p + 1) h (by omega))
    (hz0 p) (hz0 (p + 1))
  exact ⟨h1, fun x => by simpa using h2 x⟩

private theorem second_bit (Zh v p t C r C1 : ℕ)
    (h0 : v ≠ 0) (hv : v < pw p) (hx : ∀ x, v ≠ pw x)
    (hZ : Zh * pw p + v = pw t * (2 * C + 1))
    (hC : C = pw r * (2 * C1 + 1)) : t + r + 2 ≤ p := by
  have ht1 : t < p := by
    by_contra hge
    have h2 := pw_split p t (by omega)
    have hE : Zh * pw p + v = (pw (t - p) * (2 * C + 1)) * pw p + 0 := by
      rw [hZ, h2]; ring
    obtain ⟨_, e⟩ := mod_uniq (pw p) Zh _ v 0 hv (pw_pos p) hE
    exact h0 e
  by_contra hgt
  have h3 := pw_split p (t + (r + 1)) (by omega)
  have h4 : pw (t + (r + 1)) = pw t * (2 * pw r) := by rw [pw_add, pw_S]
  have hM : pw t * (2 * C) = (pw (t + (r + 1) - p) * (2 * C1 + 1)) * pw p := by
    rw [hC]
    have : pw t * (2 * (pw r * (2 * C1 + 1))) = pw (t + (r + 1)) * (2 * C1 + 1) := by
      rw [h4]; ring
    rw [this, h3]; ring
  have hE : Zh * pw p + v = (pw (t + (r + 1) - p) * (2 * C1 + 1)) * pw p + pw t := by
    linarith
  have h6 := pw_lt t p ht1
  have hpt := pw_pos t
  obtain ⟨_, e⟩ := mod_uniq (pw p) Zh _ v (pw t) hv (by omega) hE
  exact hx t e

private def pc (n : ℕ) : ℕ :=
  if n = 0 then 0 else n % 2 + pc (n / 2)
termination_by n

private theorem pc_0 : pc 0 = 0 := by unfold pc; rfl

private theorem pc_double (x : ℕ) : pc (2 * x) = pc x := by
  by_cases hx : x = 0
  · subst hx; rfl
  · conv_lhs => unfold pc
    have hne : 2 * x ≠ 0 := by omega
    have hm : (2 * x) % 2 = 0 := by omega
    have hd : (2 * x) / 2 = x := by omega
    simp [hne, hm, hd]

private theorem pc_double1 (x : ℕ) : pc (2 * x + 1) = pc x + 1 := by
  conv_lhs => unfold pc
  have hm : (2 * x + 1) % 2 = 1 := by omega
  have hd : (2 * x + 1) / 2 = x := by omega
  simp [hm, hd]; omega

private theorem pc_1 : pc 1 = 1 := by
  simpa [pc_0] using pc_double1 0

private theorem pc_3 : pc 3 = 2 := by
  simpa [pc_1] using pc_double1 1

private theorem pc_succ (x : ℕ) : pc (x + 1) ≤ pc x + 1 := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rcases N_parity x with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [pc_double1, pc_double]
    · have heq : 2 * w + 1 + 1 = 2 * (w + 1) := by omega
      rw [heq, pc_double, pc_double1]
      by_cases hw : w = 0
      · subst hw; simp [pc_0, pc_1]
      · have := ih w (by omega); omega

private theorem pc_add (x y : ℕ) : pc (x + y) ≤ pc x + pc y := by
  induction x using Nat.strongRecOn generalizing y with
  | ind x ih =>
    by_cases hx : x = 0
    · subst hx; simp [pc_0]
    · rcases N_parity x with ⟨u, rfl⟩ | ⟨u, rfl⟩ <;> rcases N_parity y with ⟨v, rfl⟩ | ⟨v, rfl⟩
      · have heq : 2 * u + 2 * v = 2 * (u + v) := by omega
        rw [heq, pc_double, pc_double, pc_double]
        exact ih u (by omega) v
      · have heq : 2 * u + (2 * v + 1) = 2 * (u + v) + 1 := by omega
        rw [heq, pc_double1, pc_double, pc_double1]
        have := ih u (by omega) v; omega
      · have heq : 2 * u + 1 + 2 * v = 2 * (u + v) + 1 := by omega
        rw [heq, pc_double1, pc_double1, pc_double]
        by_cases hu : u = 0
        · subst hu; simp [pc_0]
        · have := ih u (by omega) v; omega
      · have heq : 2 * u + 1 + (2 * v + 1) = 2 * (u + (v + 1)) := by omega
        rw [heq, pc_double, pc_double1, pc_double1]
        have hs := pc_succ v
        by_cases hu : u = 0
        · subst hu; simp [pc_0]; omega
        · have := ih u (by omega) (v + 1); omega

private theorem pc_pw (n : ℕ) : pc (pw n) = 1 := by
  induction n with
  | zero => exact pc_1
  | succ n ih => rw [pw_S, pc_double]; exact ih

private theorem pc_split (n x y : ℕ) (h : x < pw n) : pc (x + pw n * y) = pc x + pc y := by
  induction n generalizing x with
  | zero =>
    rw [pw_0] at h
    have hx : x = 0 := by omega
    subst hx; simp [pc_0, pw_0]
  | succ n ih =>
    rw [pw_S] at h ⊢
    rcases N_parity x with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · have heq : 2 * w + 2 * pw n * y = 2 * (w + pw n * y) := by ring
      rw [heq, pc_double, pc_double]
      exact ih w (by omega)
    · have heq : 2 * w + 1 + 2 * pw n * y = 2 * (w + pw n * y) + 1 := by ring
      rw [heq, pc_double1, pc_double1, ih w (by omega)]; omega

private theorem pc_ones_n (n : ℕ) : pc (pw n - 1) = n := by
  induction n with
  | zero => exact pc_0
  | succ n ih =>
    have hp := pw_pos n
    have heq : pw (n + 1) - 1 = 2 * (pw n - 1) + 1 := by rw [pw_S]; omega
    rw [heq, pc_double1, ih]

private theorem pc_on (V p q : ℕ) (h : ones_on V p q) : q - p ≤ pc V := by
  obtain ⟨hpq, a, b, hb, hV⟩ := h
  have hq := pw_split p q hpq
  set n := q - p
  have hn := pw_pos n
  have hp := pw_pos p
  have hV2 : V = b + pw p * ((pw n - 1) + pw n * a) := by
    rw [hV, hq]
    have hle : pw p ≤ pw p * pw n := by nlinarith
    zify [hn, hle]
    ring
  rw [hV2, pc_split p b _ hb, pc_split n (pw n - 1) a (by omega), pc_ones_n]
  omega

private theorem pc_three (a b c : ℕ) : pc (pw a + pw b + pw c) ≤ 3 := by
  have h1 := pc_add (pw a + pw b) (pw c)
  have h2 := pc_add (pw a) (pw b)
  rw [pc_pw] at h1
  rw [pc_pw, pc_pw] at h2
  omega

private theorem pc_two (a b : ℕ) : pc (pw a + pw b) ≤ 2 := by
  have h1 := pc_add (pw a) (pw b)
  rw [pc_pw, pc_pw] at h1
  omega

/-! ## Window Selection Inequalities -/

private def cand (x y zu zv o : ℕ) : Prop :=
  7 * x + 32 ≤ 5 * y + 2 * o ∧ 7 * x + 32 ≤ 5 * (zv + o) + 2 * o ∧
  7 * (zu + o) + 32 ≤ 5 * y + 2 * o ∧ 7 * (zu + o) + 32 ≤ 5 * (zv + o) + 2 * o

private theorem arith_O_odd (m r Lb Wp A Ap rp ap A2 A3 f1 : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : 5 * r + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * r + 2)
    (_h3 : m + r + Lb ≤ Wp + 1) (h4 : Wp ≤ m + r + Lb + 2)
    (h5 : 5 * Lb ≤ 2 * ap + 9) (_h6 : 2 * ap + 3 ≤ 5 * Lb) (h7 : 12 ≤ Lb)
    (h8 : 5 * rp + 1 ≤ 2 * A2 ∧ 2 * A2 ≤ 5 * rp + 2)
    (h9 : 5 * ap ≤ 2 * A3 ∧ 2 * A3 ≤ 5 * ap + 1)
    (h10 : rp + A2 + A3 + ap + 2 ≤ Wp + A + Ap + 2 + 1)
    (h11 : 26 ≤ m ∨ 90 ≤ Wp)
    (h12 : Lb ≤ f1) (h13 : Ap + r + 2 ≤ f1) (h14 : f1 ≤ Lb ∨ f1 ≤ Ap + r + 2)
    (h15 : Lb < Ap → rp ≤ Lb) (h16 : Ap ≤ Lb → r + 1 ≤ A → rp ≤ f1 + 1) :
    (Lb < Ap ∧ cand Lb Ap (A2 + rp + 1) (A2 + A3) (rp + 1)) ∨
    (Lb < Ap ∧ cand Lb Ap 0 (A2 - 1) (rp + 1)) ∨
    (r + 1 ≤ A ∧ cand (f1 + 1) (Ap + A + 1) (A2 + rp + 1) (A2 + A3) (rp + 1)) ∨
    (r + 1 ≤ A ∧ cand (f1 + 1) (Ap + A + 1) 0 (A2 - 1) (rp + 1)) := by
  unfold cand
  by_cases hz0 : Lb < Ap
  · have hrp := h15 hz0
    rcases le_or_gt (7 * (f1 + 1) + 32) (5 * (A2 - 1 + (rp + 1)) + 2 * (rp + 1)) with hd | hd
    · rcases le_or_gt (7 * Lb + 32) (5 * Ap + 2 * (rp + 1)) with ha | ha
      · rcases le_or_gt (7 * (rp + 1) + 32) (5 * Ap + 2 * (rp + 1)) with ha2 | ha2
        · rcases le_or_gt (7 * (A2 + 2 * rp + 2) + 32) (5 * Ap + 2 * (rp + 1)) with hb | hb
          · exact Or.inl ⟨hz0, by lia, by lia, by lia, by lia⟩
          · rcases le_or_gt (7 * Lb + 32) (5 * (A2 - 1 + (rp + 1)) + 2 * (rp + 1)) with hc | hc
            · exact Or.inr (Or.inl ⟨hz0, by lia, by lia, by lia, by lia⟩)
            · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
              exact Or.inr (Or.inr (Or.inr ⟨hrA, by lia, by lia, by lia, by lia⟩))
        · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
          exact Or.inr (Or.inr (Or.inr ⟨hrA, by lia, by lia, by lia, by lia⟩))
      · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
        exact Or.inr (Or.inr (Or.inr ⟨hrA, by lia, by lia, by lia, by lia⟩))
    · rcases le_or_gt (7 * Lb + 32) (5 * Ap + 2 * (rp + 1)) with ha | ha
      · rcases le_or_gt (7 * (rp + 1) + 32) (5 * Ap + 2 * (rp + 1)) with ha2 | ha2
        · rcases le_or_gt (7 * (A2 + 2 * rp + 2) + 32) (5 * Ap + 2 * (rp + 1)) with hb | hb
          · exact Or.inl ⟨hz0, by lia, by lia, by lia, by lia⟩
          · rcases le_or_gt (7 * Lb + 32) (5 * (A2 - 1 + (rp + 1)) + 2 * (rp + 1)) with hc | hc
            · exact Or.inr (Or.inl ⟨hz0, by lia, by lia, by lia, by lia⟩)
            · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
              exact Or.inr (Or.inr (Or.inl ⟨hrA, by lia, by lia, by lia, by lia⟩))
        · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
          exact Or.inr (Or.inr (Or.inl ⟨hrA, by lia, by lia, by lia, by lia⟩))
      · by_cases hrA : r + 1 ≤ A <;> [skip; lia]
        exact Or.inr (Or.inr (Or.inl ⟨hrA, by lia, by lia, by lia, by lia⟩))
  · have hge : Ap ≤ Lb := by lia
    have hrA : r + 1 ≤ A := by lia
    have hrp := h16 hge hrA
    rcases le_or_gt (7 * (f1 + 1) + 32) (5 * (A2 - 1 + (rp + 1)) + 2 * (rp + 1)) with hd | hd
    · exact Or.inr (Or.inr (Or.inr ⟨hrA, by lia, by lia, by lia, by lia⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨hrA, by lia, by lia, by lia, by lia⟩))

private theorem arith_O_even (m r Lb Wp A Ap ap A3 f1 : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : 5 * r + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * r + 2)
    (_h3 : m + r + Lb ≤ Wp + 1) (h4 : Wp ≤ m + r + Lb + 2)
    (h5 : 5 * Lb ≤ 2 * ap + 9) (_h6 : 2 * ap + 3 ≤ 5 * Lb) (h7 : 12 ≤ Lb)
    (h8 : 5 * ap ≤ 2 * A3 ∧ 2 * A3 ≤ 5 * ap + 1)
    (h9 : A3 + ap + 1 ≤ Wp + A + Ap + 2)
    (h10 : 26 ≤ m ∨ 90 ≤ Wp)
    (h11 : Lb ≤ f1) (h12 : Ap + r + 2 ≤ f1) (h13 : f1 ≤ Lb ∨ f1 ≤ Ap + r + 2) :
    cand Lb Ap 0 (A3 - 1) 0 ∨
    (r + 1 ≤ A ∧ cand (f1 + 1) (Ap + A + 1) 0 (A3 - 1) 0) := by
  unfold cand
  rcases le_or_gt (7 * Lb + 32) (5 * Ap) with ha | ha
  · exact Or.inl ⟨by omega, by omega, by omega, by omega⟩
  · exact Or.inr ⟨by omega, by omega, by omega, by omega, by omega⟩

private theorem arith_E_odd (m Lb Wp A ap A3 : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : m + Lb ≤ Wp + 2) (h3 : Wp ≤ m + Lb + 1)
    (h4 : 5 * Lb ≤ 2 * ap + 9) (h5 : 2 * ap + 3 ≤ 5 * Lb) (h6 : 12 ≤ Lb)
    (h7 : 5 * ap ≤ 2 * A3 ∧ 2 * A3 ≤ 5 * ap + 1)
    (h8 : A3 + ap + 2 ≤ Wp + A + 1) :
    cand Lb A 2 (1 + A3) 1 := by
  unfold cand
  omega

private theorem arith_E_even (m Lb Wp A ap A3 : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : m + Lb ≤ Wp + 2) (h3 : Wp ≤ m + Lb + 1)
    (h4 : 5 * Lb ≤ 2 * ap + 9) (h5 : 2 * ap + 3 ≤ 5 * Lb) (h6 : 12 ≤ Lb)
    (h7 : 5 * ap ≤ 2 * A3 ∧ 2 * A3 ≤ 5 * ap + 1)
    (h8 : A3 + ap + 1 ≤ Wp + A + 1) :
    cand Lb A 0 (A3 - 1) 0 := by
  unfold cand
  omega

/-! ## Shift Constants and Zone Decompositions -/

private theorem Afun_bd (m : ℕ) : 5 * m ≤ 2 * Afun m ∧ 2 * Afun m ≤ 5 * m + 1 := by
  unfold Afun; omega

private theorem Apr_bd (r : ℕ) : 5 * r + 1 ≤ 2 * Apr r ∧ 2 * Apr r ≤ 5 * r + 2 := by
  unfold Apr; omega

private def Ya (m : ℕ) : ℕ := pw (m + 2) - 3
private def y1e (t : ℕ) : ℕ := pw (Afun (t + 1) - 1) * Ya (t + 1)
private def y1o (t r : ℕ) : ℕ := pw (Apr r - 1) * (2 * zv t r + 1)

private theorem pw_add_r2 (m : ℕ) : pw (m + 2) = 4 * pw m := by
  rw [pw_add]; change pw m * 4 = 4 * pw m; ring

private theorem Ya_lo (t : ℕ) : pw (t + 2) ≤ Ya (t + 1) := by
  unfold Ya
  have h1 : pw ((t + 1) + 2) = 2 * pw (t + 2) := pw_S (t + 2)
  have h2 := pw_add_r2 t
  have h3 := pw_pos t
  omega

private theorem Ya_hi (m : ℕ) : Ya m < pw (m + 2) := by
  unfold Ya; rw [pw_add_r2]; have := pw_pos m; omega

private theorem yv_Ya (t : ℕ) : yv t = pw (Afun (t + 1)) * Ya (t + 1) := by
  unfold yv x1v Ya
  congr 1
  have hs : pw ((t + 1) + 2) = 2 * pw (t + 2) := pw_S (t + 2)
  have hg : 2 ≤ pw (t + 2) := pw_ge2 (t + 1)
  omega

private theorem Afun_pos (t : ℕ) : 1 ≤ Afun (t + 1) := by have := Afun_bd (t + 1); omega
private theorem Apr_pos (r : ℕ) : 1 ≤ Apr r := by have := Apr_bd r; omega

private theorem pw_pred2 (n : ℕ) (h : 1 ≤ n) : pw n = 2 * pw (n - 1) := by
  rw [← pw_S]; congr 1; omega

private theorem yv_y1e (t : ℕ) : yv t = 2 * y1e t := by
  rw [yv_Ya]; unfold y1e
  rw [pw_pred2 (Afun (t + 1)) (Afun_pos t)]; ring

private theorem y2v_y1o (t r : ℕ) : y2v t r = 2 * y1o t r := by
  unfold y2v y1o
  rw [pw_pred2 (Apr r) (Apr_pos r)]; ring

private theorem zv_form (t r : ℕ) : 2 * zv t r + 1 = 2 * yv t + (pw (r + 2) - 1) := by
  unfold zv; rw [pw_add_r2]; have := pw_pos r; omega

private theorem y1o_split (t r : ℕ) :
    y1o t r = pw (Apr r + Afun (t + 1)) * Ya (t + 1) + pw (Apr r - 1) * (pw (r + 2) - 1) := by
  unfold y1o
  rw [zv_form, yv_Ya, pw_add (Apr r), pw_pred2 (Apr r) (Apr_pos r)]
  ring

private theorem y2v_split (t r : ℕ) :
    y2v t r = pw (Apr r + (Afun (t + 1) + 1)) * Ya (t + 1) + pw (Apr r) * (pw (r + 2) - 1) := by
  unfold y2v
  rw [zv_form, yv_Ya, pw_add (Apr r), pw_add (Afun (t + 1))]
  change pw (Apr r) * (2 * (pw (Afun (t + 1)) * Ya (t + 1)) + (pw (r + 2) - 1)) =
    pw (Apr r) * (pw (Afun (t + 1)) * 2) * Ya (t + 1) + pw (Apr r) * (pw (r + 2) - 1)
  ring

private theorem Yc_lt (a r : ℕ) : pw a * (pw (r + 2) - 1) < pw (a + (r + 2)) := by
  rw [pw_add a]
  have ha := pw_pos a
  have hr := pw_pos (r + 2)
  have : pw (r + 2) - 1 < pw (r + 2) := by omega
  exact Nat.mul_lt_mul_of_pos_left this ha

private theorem y2v_lt (t r T : ℕ) (h1 : Afun (t + 1) + (t + 4) ≤ T) (h2 : r + 3 ≤ T) :
    y2v t r < pw (Apr r + (T + 1)) := by
  unfold y2v
  rw [zv_form, yv_Ya, pw_add (Apr r)]
  have h3 := Ya_hi (t + 1)
  have hy : 2 * (pw (Afun (t + 1)) * Ya (t + 1)) + 1 ≤ pw T := by
    have h4 := pw_le _ _ h1
    have heq : Afun (t + 1) + (t + 4) = (Afun (t + 1) + ((t + 1) + 2)) + 1 := by omega
    rw [heq, pw_S, pw_add] at h4
    have h5 : pw (Afun (t + 1)) * (Ya (t + 1) + 1) ≤ pw (Afun (t + 1)) * pw ((t + 1) + 2) :=
      Nat.mul_le_mul_left _ h3
    have hpos := pw_pos (Afun (t + 1))
    have hlin : pw (Afun (t + 1)) * (Ya (t + 1) + 1) =
        pw (Afun (t + 1)) * Ya (t + 1) + pw (Afun (t + 1)) := by ring
    omega
  have hr := pw_le (r + 2) T (by omega)
  have hT : pw (T + 1) = 2 * pw T := pw_S T
  have hp := pw_pos (Apr r)
  have hp2 := pw_pos (r + 2)
  exact Nat.mul_lt_mul_of_pos_left (by omega) hp

private theorem yv_lt (t T : ℕ) (h : Afun (t + 1) + (t + 3) ≤ T) : yv t < pw T := by
  rw [yv_Ya]
  have h4 := pw_le _ _ h
  rw [pw_add] at h4
  have h3 := Ya_hi (t + 1)
  have h5 := pw_pos (Afun (t + 1))
  have h6 : pw (Afun (t + 1)) * Ya (t + 1) < pw (Afun (t + 1)) * pw ((t + 1) + 2) :=
    Nat.mul_lt_mul_of_pos_left h3 h5
  exact lt_of_lt_of_le h6 h4

private def Zone (Y zu zv : ℕ) : Prop :=
  ∀ i j, zu ≤ i → j ≤ zv → ∃ Yh Yl, Y = Yh * pw j + Yl ∧ Yl < pw i

private theorem zone_y1o_G (t r : ℕ) : Zone (y1o t r) (Apr r + r + 1) (Apr r + Afun (t + 1)) := by
  intro i j hi hj
  refine ⟨pw (Apr r + Afun (t + 1) - j) * Ya (t + 1), pw (Apr r - 1) * (pw (r + 2) - 1), ?_, ?_⟩
  · rw [y1o_split, pw_split j (Apr r + Afun (t + 1)) hj]; ring
  · have h := Yc_lt (Apr r - 1) r
    have hp := Apr_pos r
    have hle := pw_le (Apr r - 1 + (r + 2)) i (by omega)
    omega

private theorem zone_y1o_Z (t r : ℕ) : Zone (y1o t r) 0 (Apr r - 1) := by
  intro i j _ hj
  refine ⟨pw (Apr r - 1 - j) * (2 * zv t r + 1), 0, ?_, pw_pos i⟩
  unfold y1o
  rw [pw_split j (Apr r - 1) hj]; ring

private theorem zone_y1e_Z (t : ℕ) : Zone (y1e t) 0 (Afun (t + 1) - 1) := by
  intro i j _ hj
  refine ⟨pw (Afun (t + 1) - 1 - j) * Ya (t + 1), 0, ?_, pw_pos i⟩
  unfold y1e
  rw [pw_split j (Afun (t + 1) - 1) hj]; ring

private theorem LR_even (A x y zu zv Y : ℕ)
    (h1 : ones_on A x y) (hc : cand x y zu zv 0) (hZ : Zone Y zu zv) (hY : Y ≤ A) :
    LR (A - Y) := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  set i := max x zu
  set j := min y zv
  have hi : 7 * i + 32 ≤ 5 * j := by omega
  obtain ⟨Yh, Yl, e, hl⟩ := hZ i j (by omega) (by omega)
  have h2 := ones_sub A x i j y h1 (by omega) (by omega) (by omega)
  have h3 := int_sub A i j Y Yh Yl h2 (by omega) e hl hY
  exact ⟨i + 1, j, h3, by omega⟩

private theorem LR_odd (G G1 r A x y zu zv Y : ℕ)
    (hG : G = pw r * (2 * G1 + 1)) (h1 : ones_on G x y)
    (hc : cand x y zu zv (r + 1)) (hZ : Zone Y zu zv) (hY : Y ≤ A)
    (hA : ∀ p q, ones_on G1 p q → q + (r + 1) ≤ y → ones_on A p q) :
    LR (A - Y) := by
  obtain ⟨c1, c2, c3, c4⟩ := hc
  set o := r + 1
  set i := max x (zu + o)
  set j := min y (zv + o)
  have hi : 7 * i + 32 ≤ 5 * j + 2 * o := by omega
  have h2 := ones_sub G x i j y h1 (by omega) (by omega) (by omega)
  have h3 := ones_shift_val G G1 r i j hG h2 (by omega)
  obtain ⟨Yh, Yl, e, hl⟩ := hZ (i - o) (j - o) (by omega) (by omega)
  have h4 := hA (i - o) (j - o) h3 (by omega)
  have h5 := int_sub A (i - o) (j - o) Y Yh Yl h4 (by omega) e hl hY
  exact ⟨(i - o) + 1, j - o, h5, by omega⟩

private theorem fresh0 (G Yh K0 Q Wf f g : ℕ)
    (hG : G + Yh * pw g + K0 = pw Wf + Q)
    (hK : K0 ≤ pw f + Q) (hQ : Q < K0) (hfg : f ≤ g) (hgW : g ≤ Wf) :
    ones_on G f g := by
  refine ⟨hfg, ?_⟩
  have hW := pw_split g Wf hgW
  set M := pw (Wf - g)
  have h2 := pw_le f g hfg
  have h1 := pw_pos f
  set Bv := K0 - Q
  have hB : G + Yh * pw g + Bv = pw g * M := by dsimp [Bv]; omega
  have hB0 : 0 < Bv := by dsimp [Bv]; omega
  have hB1 : Bv ≤ pw f := by dsimp [Bv]; omega
  have hM : Yh + 1 ≤ M := by
    by_contra hlt
    have h3 : M * pw g ≤ Yh * pw g := Nat.mul_le_mul_right (pw g) (by omega)
    nlinarith
  refine ⟨M - Yh - 1, pw f - Bv, by omega, ?_⟩
  have hcomm : pw g * M = M * pw g := Nat.mul_comm _ _
  have h4 : (M - Yh - 1) * pw g + Yh * pw g + pw g = M * pw g := by
    have : (M - Yh - 1 + Yh + 1) * pw g = M * pw g := by congr 1; omega
    linarith
  omega

/-! ## Run-of-Ones Invariant and Odd-Branch Closure -/

private def DCond (e : Bool) (a h r G1 G : ℕ) : Prop :=
  ∀ t, a = t + 1 →
    (isEven a = true → e = false → y1e t ≤ G → LR (G - y1e t)) ∧
    (isEven a = false → e = false → y1o t r ≤ G1 → LR (G1 - y1o t r)) ∧
    (isEven a = false → e = true → isOdd r = true →
      y1o t r ≤ G1 + pw (h - r) → LR (G1 + pw (h - r) - y1o t r))

private def Inv (e : Bool) (a h G : ℕ) : Prop :=
  26 ≤ a ∧ 2 ≤ h ∧ pw (h - 2) ≤ G ∧ G < pw h ∧
  ∃ r G1, G = pw r * (2 * G1 + 1) ∧ r + 3 ≤ h ∧ (e = true → r + 9 ≤ h) ∧
    r ≤ a ∧ DCond e a h r G1 G

private theorem pw_lt_inv (x y : ℕ) (h : pw x < pw y) : x < y := by
  by_contra hge
  have := pw_le y x (by omega)
  omega

private theorem y1o_lo (t r : ℕ) : pw (Apr r + Afun (t + 1) + (t + 2)) ≤ y1o t r := by
  rw [y1o_split, pw_add (Apr r + Afun (t + 1))]
  have h := Ya_lo t
  have h2 : pw (Apr r + Afun (t + 1)) * pw (t + 2) ≤ pw (Apr r + Afun (t + 1)) * Ya (t + 1) :=
    Nat.mul_le_mul_left _ h
  omega

private theorem y1e_lo (t : ℕ) : pw (Afun (t + 1) - 1 + (t + 2)) ≤ y1e t := by
  unfold y1e; rw [pw_add]
  exact Nat.mul_le_mul_left _ (Ya_lo t)

private theorem G1_bound (G G1 r Wf x : ℕ) (h1 : G = pw r * (2 * G1 + 1))
    (h2 : G < pw Wf) (h3 : pw x ≤ G1) : r + (x + 1) < Wf := by
  apply pw_lt_inv
  rw [pw_add, pw_S]
  have h4 := pw_pos r
  have h5 : pw r * (2 * pw x) ≤ pw r * (2 * G1 + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

private theorem r_lt (G G1 r Wf : ℕ) (h1 : G = pw r * (2 * G1 + 1)) (h2 : G < pw Wf) : r < Wf := by
  apply pw_lt_inv
  have h4 := pw_pos r
  have h5 : pw r * 1 ≤ pw r * (2 * G1 + 1) := Nat.mul_le_mul_left _ (by omega)
  omega

private theorem G1_bound2 (G G1 r Wf x : ℕ) (h1 : G = pw r * (2 * G1 + 1))
    (h2 : G < pw Wf) (h3 : pw x ≤ G1 + pw (Wf - r)) : x + r ≤ Wf := by
  have hr := r_lt G G1 r Wf h1 h2
  have h4 := pw_split r Wf (by omega)
  have h5 := pw_pos r
  have h6 : 2 * G1 + 1 < pw (Wf - r) := by nlinarith
  have h7 : pw x < pw (Wf - r + 1) := by rw [pw_S]; omega
  have := pw_lt_inv _ _ h7
  omega

private theorem O_nat1 (m q Lb Wp A Ap ta : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : 5 * q + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * q + 2)
    (h3 : m + q + Lb ≤ Wp + 1) (h4 : Wp ≤ m + q + Lb + 2)
    (h5 : 5 * Lb ≤ 2 * ta + 9) (h6 : 2 * ta + 3 ≤ 5 * Lb)
    (h7 : 12 ≤ Lb) (h8 : 1 ≤ m) :
    26 ≤ ta ∧ Lb ≤ Ap + A + Wp + 2 - 2 ∧ 9 ≤ Ap + A + Wp + 2 := by
  omega

private theorem O_r_bound (m q Lb Wp A Ap ta r T f1 f2 : ℕ)
    (h1 : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (h2 : 5 * q + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * q + 2)
    (h3 : m + q + Lb ≤ Wp + 1) (h4 : Wp ≤ m + q + Lb + 2)
    (h5 : 5 * Lb ≤ 2 * ta + 9) (h6 : 2 * ta + 3 ≤ 5 * Lb)
    (h7 : 12 ≤ Lb) (h8 : 1 ≤ m)
    (h9 : A + (m + 3) ≤ T) (h10 : q + 3 ≤ T) (h11 : T ≤ A + (m + 3) ∨ T ≤ q + 3)
    (h12 : Lb ≤ f1) (h13 : Ap + q + 2 ≤ f1) (h14 : f1 ≤ Lb ∨ f1 ≤ Ap + q + 2)
    (h15 : Ap + (T + 1) ≤ f2) (h16 : Lb ≤ f2) (h17 : f2 ≤ Ap + (T + 1) ∨ f2 ≤ Lb)
    (h18 : Lb < Ap → r ≤ Lb)
    (h19 : Ap ≤ Lb → (f1 + 1 < Ap + (A + 1) ∧ r ≤ f1 + 1) ∨ (Ap + (A + 1) ≤ f1 + 1 ∧ r ≤ f2 + 1)) :
    r ≤ ta ∧ r + 3 ≤ Ap + A + Wp + 2 := by
  omega

private theorem O_even_part (G m q Lb Wp A Ap t' f1 : ℕ)
    (bA : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (bAp : 5 * q + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * q + 2)
    (h1 : m + q + Lb ≤ Wp + 1) (h2 : Wp ≤ m + q + Lb + 2)
    (h3 : 5 * Lb ≤ 2 * (t' + 1) + 9) (h4 : 2 * (t' + 1) + 3 ≤ 5 * Lb)
    (h5 : 12 ≤ Lb) (h6 : 26 ≤ m ∨ 90 ≤ Wp)
    (h7 : Lb ≤ f1) (h8 : Ap + q + 2 ≤ f1) (h9 : f1 ≤ Lb ∨ f1 ≤ Ap + q + 2)
    (run0 : Lb ≤ Ap → ones_on G Lb Ap)
    (run1 : f1 < Ap + (A + 1) → ones_on G (f1 + 1) (Ap + (A + 1)))
    (hhigh : G < pw (Ap + A + Wp + 2)) (hle : y1e t' ≤ G) :
    LR (G - y1e t') := by
  have bA3 := Afun_bd (t' + 1)
  have hl := y1e_lo t'
  have hr2 := pw_lt_inv _ _ (lt_of_le_of_lt (le_trans hl hle) hhigh)
  rcases arith_O_even m q Lb Wp A Ap (t' + 1) (Afun (t' + 1)) f1
      bA bAp h1 h2 h3 h4 h5 bA3 (by omega) h6 h7 h8 h9 with c | ⟨_, c⟩
  · exact LR_even G Lb Ap 0 (Afun (t' + 1) - 1) (y1e t')
      (run0 (by unfold cand at c; omega)) c (zone_y1e_Z t') hle
  · have heq : Ap + (A + 1) = Ap + A + 1 := by omega
    rw [heq] at run1
    exact LR_even G (f1 + 1) (Ap + A + 1) 0 (Afun (t' + 1) - 1) (y1e t')
      (run1 (by unfold cand at c; omega)) c (zone_y1e_Z t') hle

private theorem O_odd_part (G G1 At r m q Lb Wp A Ap t' f1 : ℕ)
    (bA : 5 * m ≤ 2 * A ∧ 2 * A ≤ 5 * m + 1)
    (bAp : 5 * q + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * q + 2)
    (h1 : m + q + Lb ≤ Wp + 1) (h2 : Wp ≤ m + q + Lb + 2)
    (h3 : 5 * Lb ≤ 2 * (t' + 1) + 9) (h4 : 2 * (t' + 1) + 3 ≤ 5 * Lb)
    (h5 : 12 ≤ Lb) (h6 : 26 ≤ m ∨ 90 ≤ Wp)
    (h7 : Lb ≤ f1) (h8 : Ap + q + 2 ≤ f1) (h9 : f1 ≤ Lb ∨ f1 ≤ Ap + q + 2)
    (run0 : Lb ≤ Ap → ones_on G Lb Ap)
    (run1 : f1 < Ap + (A + 1) → ones_on G (f1 + 1) (Ap + (A + 1)))
    (r1 : Lb < Ap → r ≤ Lb) (r2 : Ap ≤ Lb → q + 1 ≤ A → r ≤ f1 + 1)
    (hGr : G = pw r * (2 * G1 + 1))
    (hR : r + Apr r + Afun (t' + 1) + (t' + 1) + 1 ≤ Ap + A + Wp + 2)
    (hA : ∀ p q0, ones_on G1 p q0 → q0 + (r + 1) ≤ Ap + A + Wp + 2 → ones_on At p q0)
    (hle : y1o t' r ≤ At) :
    LR (At - y1o t' r) := by
  have bA3 := Afun_bd (t' + 1)
  have bA2 := Apr_bd r
  have heq : Ap + (A + 1) = Ap + A + 1 := by omega
  rw [heq] at run1
  rcases arith_O_odd m q Lb Wp A Ap r (t' + 1) (Apr r) (Afun (t' + 1)) f1
      bA bAp h1 h2 h3 h4 h5 bA2 bA3 (by omega) h6 h7 h8 h9 r1 r2 with
      ⟨c0, c⟩ | ⟨c0, c⟩ | ⟨_, c⟩ | ⟨_, c⟩
  · exact LR_odd G G1 r At Lb Ap (Apr r + r + 1) (Apr r + Afun (t' + 1)) (y1o t' r)
      hGr (run0 (by omega)) c (zone_y1o_G t' r) hle (fun p q0 h10 h11 => hA p q0 h10 (by omega))
  · exact LR_odd G G1 r At Lb Ap 0 (Apr r - 1) (y1o t' r)
      hGr (run0 (by omega)) c (zone_y1o_Z t' r) hle (fun p q0 h10 h11 => hA p q0 h10 (by omega))
  · exact LR_odd G G1 r At (f1 + 1) (Ap + A + 1) (Apr r + r + 1) (Apr r + Afun (t' + 1)) (y1o t' r)
      hGr (run1 (by unfold cand at c; omega)) c (zone_y1o_G t' r) hle
      (fun p q0 h10 h11 => hA p q0 h10 (by omega))
  · exact LR_odd G G1 r At (f1 + 1) (Ap + A + 1) 0 (Apr r - 1) (y1o t' r)
      hGr (run1 (by unfold cand at c; omega)) c (zone_y1o_Z t' r) hle
      (fun p q0 h10 h11 => hA p q0 h10 (by omega))

private theorem close_O (t k q K0 Q Lb Wp G t' : ℕ) (e : Bool)
    (hk : t + 1 = 2 * k + 1)
    (hG : G + y2v t q + K0 = pw (Apr q + (Afun (t + 1) + (Wp + 1) + 1)) + Q)
    (hQ : Q < K0) (hK : K0 ≤ pw Lb)
    (hW1 : (t + 1) + q + Lb ≤ Wp + 1) (hW2 : Wp ≤ (t + 1) + q + Lb + 2)
    (ha1 : 5 * Lb ≤ 2 * (t' + 1) + 9) (ha2 : 2 * (t' + 1) + 3 ≤ 5 * Lb)
    (hLb : 12 ≤ Lb) (hm : 26 ≤ t + 1 ∨ 90 ≤ Wp)
    (h9 : e = true → ∀ r G1, G = pw r * (2 * G1 + 1) →
      r + 9 ≤ Apr q + (Afun (t + 1) + (Wp + 1) + 1)) :
    Inv e (t' + 1) (Apr q + (Afun (t + 1) + (Wp + 1) + 1)) G := by
  have bA := Afun_bd (t + 1)
  have bAp := Apr_bd q
  have hy0 : y2v t q = (2 * zv t q + 1) * pw (Apr q) := by unfold y2v; ring
  have hys := y2v_split t q
  have hy_lt : ∀ T, Afun (t + 1) + (t + 4) ≤ T → q + 3 ≤ T → y2v t q < pw (Apr q + (T + 1)) :=
    fun T h1 h2 => y2v_lt t q T h1 h2
  generalize hA_def : Afun (t + 1) = A at bA hys hy_lt hG h9 ⊢
  generalize hAp_def : Apr q = Ap at bAp hy0 hys hy_lt hG h9 ⊢
  have hWf_eq : Ap + (A + (Wp + 1) + 1) = Ap + A + Wp + 2 := by omega
  rw [hWf_eq] at hG h9 ⊢
  generalize hWf_def : Ap + A + Wp + 2 = Wf at hG h9 ⊢
  obtain ⟨h26, hlW0, _h9W⟩ :=
    O_nat1 (t + 1) q Lb Wp A Ap (t' + 1) bA bAp hW1 hW2 ha1 ha2 hLb (by omega)
  obtain ⟨T, hT1, hT2, hT3⟩ :
      ∃ T, A + (t + 4) ≤ T ∧ q + 3 ≤ T ∧ (T ≤ A + (t + 4) ∨ T ≤ q + 3) :=
    ⟨max (A + (t + 4)) (q + 3), le_max_left _ _, le_max_right _ _, by omega⟩
  have hY : y2v t q < pw (Ap + (T + 1)) := hy_lt T hT1 hT2
  have hTW : Ap + (T + 1) ≤ Wf - 1 := by omega
  have hLW : Lb ≤ Wf - 2 := by omega
  have hP1 := pw_le _ _ hTW
  have hP2 := pw_le _ _ hLW
  have hW0 : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by omega)
  have hW1' : pw (Wf - 1) = 2 * pw (Wf - 2) := by
    have : Wf - 2 = Wf - 1 - 1 := by omega
    rw [this]; exact pw_pred2 (Wf - 1) (by omega)
  have hlow : pw (Wf - 2) ≤ G := by omega
  have hhigh : G < pw Wf := by omega
  have hG0 : G ≠ 0 := by have := pw_pos (Wf - 2); omega
  obtain ⟨r, G1, hGr⟩ := N_tz G hG0
  have runI0 : Lb ≤ Ap → ones_on G Lb Ap := fun hl =>
    fresh0 G (2 * zv t q + 1) K0 Q Wf Lb Ap (by linarith) (by omega) hQ hl (by omega)
  obtain ⟨f1, hf1, hf2, hf3⟩ :
      ∃ f1, Lb ≤ f1 ∧ Ap + q + 2 ≤ f1 ∧ (f1 ≤ Lb ∨ f1 ≤ Ap + q + 2) :=
    ⟨max Lb (Ap + q + 2), le_max_left _ _, le_max_right _ _, by omega⟩
  have runI1 : f1 < Ap + (A + 1) → ones_on G (f1 + 1) (Ap + (A + 1)) := fun hl =>
    fresh G (y2v t q) K0 Q Wf f1 (Ap + (A + 1)) (Ya (t + 1)) (pw Ap * (pw (q + 2) - 1))
      hG (by linarith)
      (lt_of_lt_of_le (Yc_lt Ap q) (pw_le (Ap + (q + 2)) f1 (by omega)))
      (le_trans hK (pw_le Lb f1 hf1)) hQ hl (by omega)
  obtain ⟨f2, hg1, hg2, hg3⟩ :
      ∃ f2, Ap + (T + 1) ≤ f2 ∧ Lb ≤ f2 ∧ (f2 ≤ Ap + (T + 1) ∨ f2 ≤ Lb) :=
    ⟨max (Ap + (T + 1)) Lb, le_max_left _ _, le_max_right _ _, by omega⟩
  have runI2 : f2 < Wf → ones_on G (f2 + 1) Wf := fun hl =>
    fresh G (y2v t q) K0 Q Wf f2 Wf 0 (y2v t q)
      hG (by simp) (lt_of_lt_of_le hY (pw_le _ _ hg1))
      (le_trans hK (pw_le _ _ hg2)) hQ hl (le_refl Wf)
  have hr1 : Lb < Ap → r ≤ Lb := fun hl => ones_tz G G1 r Lb Ap hGr (runI0 (by omega)) hl
  have hr2 : Ap ≤ Lb →
      (f1 + 1 < Ap + (A + 1) ∧ r ≤ f1 + 1) ∨ (Ap + (A + 1) ≤ f1 + 1 ∧ r ≤ f2 + 1) := by
    intro hl
    rcases lt_or_ge (f1 + 1) (Ap + (A + 1)) with h1 | h1
    · exact Or.inl ⟨h1, ones_tz G G1 r (f1 + 1) (Ap + (A + 1)) hGr (runI1 (by omega)) h1⟩
    · refine Or.inr ⟨h1, ?_⟩
      have h2 : f2 + 2 ≤ Wf := by omega
      exact ones_tz G G1 r (f2 + 1) Wf hGr (runI2 (by omega)) (by omega)
  obtain ⟨hb1, hb2⟩ := O_r_bound (t + 1) q Lb Wp A Ap (t' + 1) r T f1 f2
    bA bAp hW1 hW2 ha1 ha2 hLb (by omega) hT1 hT2 hT3 hf1 hf2 hf3 hg1 hg2 hg3 hr1 hr2
  refine ⟨h26, by omega, hlow, hhigh, r, G1, hGr, by omega, fun he => h9 he r G1 hGr, hb1, ?_⟩
  intro t2 ht2
  have _ht2' : t2 = t' := by omega
  subst t2
  have hr3 : Ap ≤ Lb → q + 1 ≤ A → r ≤ f1 + 1 ∨ Ap + (A + 1) ≤ f1 + 1 := by
    intro h1 h2; rcases hr2 h1 with ⟨_, h4⟩ | ⟨h3, _⟩ <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ hle
    have hhigh' : G < pw (Ap + A + Wp + 2) := by rwa [hWf_def]
    exact O_even_part G (t + 1) q Lb Wp A Ap t' f1 bA bAp
      hW1 hW2 ha1 ha2 hLb hm hf1 hf2 hf3 runI0 runI1 hhigh' hle
  · intro _ _ hle
    have hl := y1o_lo t' r
    have hR := G1_bound G G1 r Wf (Apr r + Afun (t' + 1) + (t' + 2)) hGr hhigh (le_trans hl hle)
    have hR' : r + Apr r + Afun (t' + 1) + (t' + 1) + 1 ≤ Ap + A + Wp + 2 := by omega
    have hr3' : Ap ≤ Lb → q + 1 ≤ A → r ≤ f1 + 1 := by
      intro h1 h2
      rcases hr3 h1 h2 with h3 | h3
      · exact h3
      · have := Afun_bd (t' + 1); have := Apr_bd r; omega
    exact O_odd_part G G1 G1 r (t + 1) q Lb Wp A Ap t' f1 bA bAp
      hW1 hW2 ha1 ha2 hLb hm hf1 hf2 hf3 runI0 runI1 hr1 hr3'
      hGr hR' (fun _ _ h1 _ => h1) hle
  · intro _ _ _ hle
    have hl := y1o_lo t' r
    have hR := G1_bound2 G G1 r Wf (Apr r + Afun (t' + 1) + (t' + 2)) hGr hhigh (le_trans hl hle)
    have hR' : r + Apr r + Afun (t' + 1) + (t' + 1) + 1 ≤ Ap + A + Wp + 2 := by omega
    have hr3' : Ap ≤ Lb → q + 1 ≤ A → r ≤ f1 + 1 := by
      intro h1 h2
      rcases hr3 h1 h2 with h3 | h3
      · exact h3
      · have := Afun_bd (t' + 1); have := Apr_bd r; omega
    exact O_odd_part G G1 (G1 + pw (Wf - r)) r (t + 1) q Lb Wp A Ap t' f1 bA bAp
      hW1 hW2 ha1 ha2 hLb hm hf1 hf2 hf3 runI0 runI1 hr1 hr3'
      hGr hR' (fun p q0 h1 h2 => ones_high G1 p q0 (Wf - r) h1 (by omega)) hle

/-! ## Even-Branch Closure -/

private theorem close_E (t k K0 Q Lb Wp G G1 t' : ℕ) (e : Bool)
    (hk : t + 1 = 2 * k)
    (hG : G + yv t + K0 = pw (Afun (t + 1) + (Wp + 1)) + Q)
    (hQ : Q < K0) (hK : K0 ≤ pw Lb) (hG1 : G = 2 * G1 + 1)
    (hW1 : (t + 1) + Lb ≤ Wp + 2) (hW2 : Wp ≤ (t + 1) + Lb + 1)
    (ha1 : 5 * Lb ≤ 2 * (t' + 1) + 9) (ha2 : 2 * (t' + 1) + 3 ≤ 5 * Lb)
    (hLb : 12 ≤ Lb) :
    Inv e (t' + 1) (Afun (t + 1) + (Wp + 1)) G := by
  have bA := Afun_bd (t + 1)
  set A := Afun (t + 1)
  set Wf := A + Wp + 1
  have hWf_eq : Afun (t + 1) + (Wp + 1) = Wf := by dsimp [A, Wf]; omega
  rw [hWf_eq] at hG ⊢
  have hY := yv_lt t (A + (t + 3)) (by dsimp [A]; omega)
  have hTW : A + (t + 3) ≤ Wf - 1 := by dsimp [Wf]; omega
  have hLW : Lb ≤ Wf - 2 := by dsimp [Wf]; omega
  have hP1 := pw_le _ _ hTW
  have hP2 := pw_le _ _ hLW
  have hW0 : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have hW1' : pw (Wf - 1) = 2 * pw (Wf - 2) := by
    have : Wf - 2 = Wf - 1 - 1 := by omega
    rw [this]; exact pw_pred2 (Wf - 1) (by dsimp [Wf]; omega)
  have hlow : pw (Wf - 2) ≤ G := by omega
  have hhigh : G < pw Wf := by omega
  have run0 : Lb ≤ A → ones_on G Lb A := fun hl =>
    fresh0 G (Ya (t + 1)) K0 Q Wf Lb A
      (by have : yv t = Ya (t + 1) * pw A := by rw [yv_Ya]; dsimp [A]; ring
          linarith)
      (by omega) hQ hl (by dsimp [Wf]; omega)
  have hGr : G = pw 0 * (2 * G1 + 1) := by rw [pw_0, Nat.one_mul]; exact hG1
  refine ⟨by omega, by dsimp [Wf]; omega, hlow, hhigh, 0, G1, hGr,
    by dsimp [Wf]; omega, fun _ => by dsimp [Wf]; omega, by omega, ?_⟩
  intro t2 ht2
  have ht2' : t2 = t' := by omega
  subst t2
  have bA3 := Afun_bd (t' + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ hle
    have hl := y1e_lo t'
    have hR2 := pw_lt_inv _ _ (lt_of_le_of_lt (le_trans hl hle) hhigh)
    have c := arith_E_even (t + 1) Lb Wp A (t' + 1) (Afun (t' + 1)) bA hW1 hW2 ha1 ha2 hLb bA3
      (by dsimp [Wf] at hR2; omega)
    exact LR_even G Lb A 0 (Afun (t' + 1) - 1) (y1e t')
      (run0 (by unfold cand at c; omega)) c (zone_y1e_Z t') hle
  · intro _ _ hle
    have hl := y1o_lo t' 0
    have hR := G1_bound G G1 0 Wf _ hGr hhigh (le_trans hl hle)
    have hap0 : Apr 0 = 1 := rfl
    rw [hap0] at hR
    have c := arith_E_odd (t + 1) Lb Wp A (t' + 1) (Afun (t' + 1)) bA hW1 hW2 ha1 ha2 hLb bA3
      (by dsimp [Wf] at hR; omega)
    exact LR_odd G G1 0 G1 Lb A 2 (1 + Afun (t' + 1)) (y1o t' 0) hGr
      (run0 (by unfold cand at c; omega)) c (zone_y1o_G t' 0) hle (fun _ _ h1 _ => h1)
  · intro _ _ hodd
    cases hodd

private theorem close_TS (u Vl t' : ℕ) (e : Bool)
    (h0 : Vl ≠ 0) (h1 : Vl < pw u) (ht : t' + 1 = Apr (u + 1)) (hu : 10 ≤ u)
    (h7 : e = true → ∀ r G1, pw u + Vl = pw r * (2 * G1 + 1) → r + 7 ≤ u) :
    Inv e (t' + 1) (u + 3) (2 * (pw u + Vl)) := by
  have bA := Apr_bd (u + 1)
  rw [← ht] at bA
  have p1 : pw (u + 1) = 2 * pw u := pw_S u
  have p2 : pw (u + 2) = 2 * pw (u + 1) := pw_S (u + 1)
  have p3 : pw (u + 3) = 2 * pw (u + 2) := pw_S (u + 2)
  have hpu := pw_pos u
  obtain ⟨r, G1, hV⟩ := N_tz (pw u + Vl) (by omega)
  have hru : r < u := by
    by_contra hge
    have h2 := pw_split u r (by omega)
    have hE : 1 * pw u + Vl = (pw (r - u) * (2 * G1 + 1)) * pw u + 0 := by
      rw [Nat.one_mul, hV, h2]; ring
    obtain ⟨_, e'⟩ := mod_uniq (pw u) 1 _ Vl 0 h1 hpu hE
    exact h0 e'
  have hGr : 2 * (pw u + Vl) = pw (r + 1) * (2 * G1 + 1) := by rw [hV, pw_S]; ring
  have hhigh : 2 * (pw u + Vl) < pw (u + 3) := by omega
  refine ⟨by omega, by omega, by have h_eq : u + 3 - 2 = u + 1 := (by omega); rw [h_eq]; omega,
    hhigh, r + 1, G1, hGr, by omega, fun he => by have := h7 he r G1 hV; omega, by omega, ?_⟩
  intro t2 ht2
  have ht2' : t2 = t' := by omega
  subst t2
  have bA3 := Afun_bd (t' + 1)
  refine ⟨?_, ?_, ?_⟩
  · intro _ _ hle
    exfalso
    have hl := y1e_lo t'
    have := pw_lt_inv _ _ (lt_of_le_of_lt (le_trans hl hle) hhigh)
    omega
  · intro _ _ hle
    exfalso
    have hl := y1o_lo t' (r + 1)
    have := G1_bound _ G1 (r + 1) (u + 3) _ hGr hhigh (le_trans hl hle)
    omega
  · intro _ _ _ hle
    exfalso
    have hl := y1o_lo t' (r + 1)
    have := G1_bound2 _ G1 (r + 1) (u + 3) _ hGr hhigh (le_trans hl hle)
    omega

private theorem run_top (t q K0 Q Lb Wf G f : ℕ)
    (hG : G + y2v t q + K0 = pw Wf + Q) (hQ : Q < K0) (hK : K0 ≤ pw Lb)
    (h1 : Apr q + (Afun (t + 1) + (t + 4) + 1) ≤ f)
    (h2 : Apr q + (q + 4) ≤ f) (h3 : Lb ≤ f) (h4 : f < Wf) :
    ones_on G (f + 1) Wf := by
  set T := max (Afun (t + 1) + (t + 4)) (q + 3)
  have hT1 : Afun (t + 1) + (t + 4) ≤ T := le_max_left _ _
  have hT2 : q + 3 ≤ T := le_max_right _ _
  have hT3 : Apr q + (T + 1) ≤ f := by dsimp [T]; omega
  have hY := y2v_lt t q T hT1 hT2
  exact fresh G (y2v t q) K0 Q Wf f Wf 0 (y2v t q) hG (by simp)
    (lt_of_lt_of_le hY (pw_le _ _ hT3)) (le_trans hK (pw_le _ _ h3)) hQ h4 (le_refl Wf)

/-! ## Macro Closure on Simple Branches -/

private def Good (c : Cfg Sym (Fin 6)) : Prop :=
  ∃ e a h G, ReachesPlus tm c (FC e a h (pw h - 1 - G)) ∧ Inv e a h G

private theorem Apr_S (n : ℕ) : (Apr n - 1) + 1 = Apr n := by
  have := Apr_pos n; omega

private theorem Afun_S (n : ℕ) (h : 1 ≤ n) : (Afun n - 1) + 1 = Afun n := by
  have := Afun_bd n; omega

private theorem good_BE1 (t k c C W : ℕ)
    (hk : t + 1 = 2 * k) (h0 : C ≠ 0) (hC : C < pw c) (hc : 9 ≤ c)
    (hW1 : (t + 1) + c + 1 ≤ W) (hW2 : W ≤ (t + 1) + c + 2) :
    Good (D1 (t + 1) (TL (bin c C) (U B0)) W) := by
  set Wf := Afun (t + 1) + (W + 1)
  have bA := Afun_bd (t + 1)
  have hY := yv_lt t (Afun (t + 1) + (t + 3)) (by omega)
  have h1 := pw_le (Afun (t + 1) + (t + 3)) (Wf - 1) (by dsimp [Wf]; omega)
  have h2 := pw_le (c + 3) (Wf - 1) (by dsimp [Wf]; omega)
  have hW : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have hc3 : pw (c + 3) = 8 * pw c := by rw [pw_add]; change pw c * 8 = 8 * pw c; ring
  have hS : pw (c + 1) = 2 * pw c := pw_S c
  have hp := pw_pos c
  set x' := yv t + 1 + 2 * (pw c - (C + 1))
  set xf := x' + 2 * pw (c + 1) - 1
  have hx1 : x' < pw Wf := by dsimp [x']; omega
  have hx2 : xf < pw Wf := by dsimp [xf, x']; omega
  set G := pw Wf - 1 - xf
  have hGe : G + yv t + 6 * pw c = pw Wf + (2 * C + 1) := by dsimp [G, xf, x']; omega
  have hye := yv_y1e t
  rcases N_parity G with ⟨w, hw⟩ | ⟨w, hw⟩
  · exfalso; omega
  · refine ⟨isOdd (c + 1), Apr (c + 1), Wf, G, ?_, ?_⟩
    · have hsub : pw Wf - 1 - G = xf := by dsimp [G]; omega
      rw [hsub]
      exact ReachesPlus.trans (b_E1 t k c C W hk (by omega) h0 hC hx1) (d3_fin (c + 1) Wf x' hx2)
    · have bA2 := Apr_bd (c + 1)
      rw [← Apr_S (c + 1)]
      exact close_E t k (6 * pw c) (2 * C + 1) (c + 3) W G w (Apr (c + 1) - 1) (isOdd (c + 1))
        hk hGe (by omega) (by omega) hw (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem good_DE1 (t k r c1 C1 W : ℕ)
    (hk : t + 1 = 2 * k) (hC : pw r * (2 * C1 + 1) + 1 < pw (r + (c1 + 1)))
    (hc : 11 ≤ r + (c1 + 1)) (hW : W = (t + 1) + (r + (c1 + 1)) + 1) :
    Good (D1 (t + 1) (TL (bin (r + (c1 + 1)) (pw r * (2 * C1 + 1))) (D3 B0)) W) := by
  set c := r + (c1 + 1)
  set C := pw r * (2 * C1 + 1)
  set Wf := Afun (t + 1) + (W + 1)
  have bA := Afun_bd (t + 1)
  have hY := yv_lt t (Afun (t + 1) + (t + 3)) (by omega)
  have h1 := pw_le (Afun (t + 1) + (t + 3)) (Wf - 1) (by dsimp [Wf]; omega)
  have h2 := pw_le (c + 1) (Wf - 1) (by dsimp [Wf]; omega)
  have hW2 : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have hc1_pw : pw (c + 1) = 2 * pw c := pw_S c
  set xf := yv t + 1 + 2 * (pw c - 1 - (C + 1)) + 1
  have hx : xf < pw Wf := by dsimp [xf]; omega
  set G := pw Wf - 1 - xf
  have hGe : G + yv t + 2 * pw c = pw Wf + (2 * C + 1) := by dsimp [G, xf]; omega
  have hye := yv_y1e t
  rcases N_parity G with ⟨w, hw⟩ | ⟨w, hw⟩
  · exfalso; omega
  · refine ⟨isEven c, Afun c, Wf, G, ?_, ?_⟩
    · have hsub : pw Wf - 1 - G = xf := by dsimp [G]; omega
      rw [hsub]
      exact d3_E1 t k r c1 C1 W hk (by omega) hC hx
    · have bA2 := Afun_bd c
      rw [← Afun_S c (by omega)]
      exact close_E t k (2 * pw c) (2 * C + 1) (c + 1) W G w (Afun c - 1) (isEven c)
        hk hGe (by omega) (by omega) hw (by omega) (by omega) (by omega) (by omega) (by omega)

private theorem good_TS (u Vl : ℕ) (h0 : Vl ≠ 0) (h1 : Vl + 1 ≤ pw u) (hu : 10 ≤ u)
    (h7 : isOdd (u + 1) = true → ∀ r G1, pw u + Vl = pw r * (2 * G1 + 1) → r + 7 ≤ u) :
    Good (AC (TL (bin u Vl) (U B0)) (oL (u + 2))) := by
  have p1 : pw (u + 1) = 2 * pw u := pw_S u
  have p2 : pw (u + 2) = 2 * pw (u + 1) := pw_S (u + 1)
  have p3 : pw (u + 3) = 2 * pw (u + 2) := pw_S (u + 2)
  refine ⟨isOdd (u + 1), Apr (u + 1), u + 3, 2 * (pw u + Vl), ?_, ?_⟩
  · have hsub : pw (u + 3) - 1 - 2 * (pw u + Vl) =
        2 * pw u - 2 * Vl + 2 * pw (u + 1) - 1 := by omega
    rw [hsub]
    rcases lt_or_ge (Vl + 1) (pw u) with hl | hl
    · exact tailS_fin u Vl h0 hl
    · exact tailS_top u Vl (by omega) (by omega)
  · rw [← Apr_S (u + 1)]
    exact close_TS u Vl (Apr (u + 1) - 1) (isOdd (u + 1)) h0 (by omega) (Apr_S (u + 1)) hu h7

/-! ## Trailing-Ones Defect Absorption -/

private theorem h9_run (t q K0 Q Lb Wf G r G1 : ℕ)
    (hG : G + y2v t q + K0 = pw Wf + Q) (hQ : Q < K0) (hK : K0 ≤ pw Lb)
    (h1 : Apr q + (Afun (t + 1) + (t + 4) + 1) + 10 ≤ Wf)
    (h2 : Apr q + (q + 4) + 10 ≤ Wf) (h3 : Lb + 10 ≤ Wf)
    (hr : G = pw r * (2 * G1 + 1)) : r + 9 ≤ Wf := by
  have R := run_top t q K0 Q Lb Wf G (Wf - 10) hG hQ hK (by omega) (by omega) (by omega) (by omega)
  have E := ones_tz G G1 r (Wf - 10 + 1) Wf hr R (by omega)
  omega

private theorem h9_gen (t k q K0 Q Lb L W G r G1 : ℕ)
    (hk : t + 1 = 2 * k + 1)
    (hG : G + y2v t q + K0 = pw (Apr q + (Afun (t + 1) + (W + 1) + 1)) + Q)
    (hQ : Q < K0) (hK : K0 ≤ pw Lb)
    (h1 : (t + 1) + q + L + 2 ≤ W) (h2 : 10 ≤ L) (h3 : Lb ≤ L + 3)
    (h4 : t ≠ 0 ∨ 2 ≤ q) (hr : G = pw r * (2 * G1 + 1)) :
    r + 9 ≤ Apr q + (Afun (t + 1) + (W + 1) + 1) := by
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd q
  exact h9_run t q K0 Q Lb _ G r G1 hG hQ hK (by omega) (by omega) (by omega) hr

private theorem y2v00 : y2v 0 0 = 166 := by decide

private theorem h9_zero (K0 Q W G : ℕ)
    (h : G + y2v 0 0 + K0 = pw (Apr 0 + (Afun 1 + (W + 1) + 1)) + Q) :
    G + 166 + K0 = pw (W + 6) + Q := by
  rw [y2v00] at h
  have ha0 : Apr 0 = 1 := rfl
  have ha1 : Afun 1 = 3 := rfl
  rw [ha0, ha1] at h
  have heq : 1 + (3 + (W + 1) + 1) = W + 6 := by omega
  rwa [heq] at h

private theorem mult_split (r L G1 : ℕ) (h : L ≤ r) : ∃ Z, pw r * (2 * G1 + 1) = Z * pw L :=
  ⟨pw (r - L) * (2 * G1 + 1), by rw [pw_split L r h]; ring⟩

private theorem h9_core (P Z C1 B : ℕ) (hP : 512 ≤ P) (h1 : C1 < P) (h2 : C1 ≠ 83)
    (e : Z * (2 * P) + 166 = B * (2 * P) + 2 * C1) : False := by
  rcases lt_or_ge C1 83 with h | h
  · have e2 : Z * (2 * P) + (166 - 2 * C1) = B * (2 * P) + 0 := by omega
    obtain ⟨_, e3⟩ := mod_uniq (2 * P) Z B (166 - 2 * C1) 0 (by omega) (by omega) e2
    omega
  · have e2 : Z * (2 * P) + 0 = B * (2 * P) + (2 * C1 - 166) := by omega
    obtain ⟨_, e3⟩ := mod_uniq (2 * P) Z B 0 (2 * C1 - 166) (by omega) (by omega) e2
    omega

private theorem pw_9 (L : ℕ) : pw (L + 9) = 512 * pw L := by
  rw [pw_add]; change pw L * 512 = 512 * pw L; ring

private theorem pw_10 (L : ℕ) : pw (L + 10) = 1024 * pw L := by
  rw [pw_add]; change pw L * 1024 = 1024 * pw L; ring

private theorem h9_s1 (L C1 G r G1 : ℕ) (hL : 9 ≤ L) (h1 : C1 < pw L) (h2 : C1 ≠ 83)
    (hE : G + 166 + 6 * pw L = pw (L + 9) + 2 * C1 ∨ G + 166 + 2 * pw L = pw (L + 9) + 2 * C1)
    (hr : G = pw r * (2 * G1 + 1)) : r + 9 ≤ L + 9 := by
  rcases le_or_gt r L with h | h
  · omega
  · exfalso
    obtain ⟨Z, hZ⟩ := mult_split r (L + 1) G1 h
    rw [pw_S] at hZ
    rw [pw_9] at hE
    rw [hZ] at hr; subst hr
    have P := pw_le 9 L hL
    have hp9 : pw 9 = 512 := by decide
    rw [hp9] at P
    rcases hE with hE | hE
    · exact h9_core (pw L) Z C1 253 P h1 h2 (by omega)
    · exact h9_core (pw L) Z C1 255 P h1 h2 (by omega)

private theorem h9_s2 (L C1 G r G1 : ℕ) (hL : 9 ≤ L) (h1 : C1 < pw L)
    (hE : G + 166 + 6 * pw L = pw (L + 10) + 2 * C1)
    (hr : G = pw r * (2 * G1 + 1)) : r + 9 ≤ L + 10 := by
  rcases le_or_gt r (L + 1) with h | h
  · omega
  · exfalso
    obtain ⟨Z, hZ⟩ := mult_split r (L + 2) G1 h
    have hs2 : pw (L + 2) = 2 * (2 * pw L) := by rw [pw_S (L + 1), pw_S L]
    rw [hs2] at hZ
    rw [pw_10] at hE
    rw [hZ] at hr; subst hr
    have P := pw_le 9 L hL
    have hp9 : pw 9 = 512 := by decide
    rw [hp9] at P
    have e2 : Z * (2 * (2 * pw L)) + 0 =
        254 * (2 * (2 * pw L)) + (2 * pw L + 2 * C1 - 166) := by omega
    obtain ⟨_, e3⟩ := mod_uniq (2 * (2 * pw L)) Z 254 0 (2 * pw L + 2 * C1 - 166)
      (by omega) (by omega) e2
    omega

private theorem odd_ge10 (L : ℕ) (h1 : 9 ≤ L) (h2 : isOdd (L + 1) = true) : 10 ≤ L := by
  by_cases heq : L = 9
  · subst heq; revert h2; decide
  · omega

private theorem h9_BO0 (t k j L C1 W G : ℕ)
    (hk : t + 1 = 2 * k + 1) (hL : 9 ≤ L) (hC : C1 < pw L)
    (hW1 : (t + 1) + (2 * j + (L + 1)) + 1 ≤ W)
    (hW2 : W ≤ (t + 1) + (2 * j + (L + 1)) + 2)
    (h83 : t = 0 → j = 0 → W = (t + 1) + (2 * j + (L + 1)) + 1 → C1 ≠ 83)
    (hG : G + y2v t (2 * j) + 6 * pw L = pw (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)) + 2 * C1)
    (ho : isOdd (L + 1) = true) (r G1 : ℕ) (hr : G = pw r * (2 * G1 + 1)) :
    r + 9 ≤ Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1) := by
  have h10 := odd_ge10 L hL ho
  by_cases ht : t = 0
  · by_cases hj : j = 0
    · subst ht hj
      have hg0 := h9_zero (6 * pw L) (2 * C1) W G hG
      have ha0 : Apr 0 = 1 := rfl
      have ha1 : Afun 1 = 3 := rfl
      simp only [Nat.mul_zero, Nat.zero_add, ha0, ha1] at hW1 hW2 h83 ⊢
      rcases (show W = L + 3 ∨ W = L + 4 by omega) with rfl | rfl
      · have heq : L + 3 + 6 = L + 9 := by omega
        rw [heq] at hg0
        have := h9_s1 L C1 G r G1 hL hC (h83 trivial trivial (by omega)) (Or.inl hg0) hr
        omega
      · have heq : L + 4 + 6 = L + 10 := by omega
        rw [heq] at hg0
        have := h9_s2 L C1 G r G1 hL hC hg0 hr
        omega
    · have hp3 : pw (L + 3) = 8 * pw L := by rw [pw_add]; change pw L * 8 = 8 * pw L; ring
      exact h9_gen t k (2 * j) (6 * pw L) (2 * C1) (L + 3) L W G r G1 hk hG
        (by omega) (by omega) (by omega) h10 (by omega) (by omega) hr
  · have hp3 : pw (L + 3) = 8 * pw L := by rw [pw_add]; change pw L * 8 = 8 * pw L; ring
    exact h9_gen t k (2 * j) (6 * pw L) (2 * C1) (L + 3) L W G r G1 hk hG
      (by omega) (by omega) (by omega) h10 (by omega) (by omega) hr

private theorem h9_DO0 (t k j L C1 W G : ℕ)
    (hk : t + 1 = 2 * k + 1) (hL : 11 ≤ L) (hC1 : pw (L - 1) ≤ C1) (hC : C1 < pw L)
    (hW : W = (t + 1) + (2 * j + (L + 1)) + 1)
    (hG : G + y2v t (2 * j) + 2 * pw L = pw (Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)) + 2 * C1)
    (r G1 : ℕ) (hr : G = pw r * (2 * G1 + 1)) :
    r + 9 ≤ Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1) := by
  by_cases ht : t = 0
  · by_cases hj : j = 0
    · subst ht hj
      have hg0 := h9_zero (2 * pw L) (2 * C1) W G hG
      have ha0 : Apr 0 = 1 := rfl
      have ha1 : Afun 1 = 3 := rfl
      simp only [Nat.mul_zero, Nat.zero_add, ha0, ha1] at hW ⊢
      have hW' : W = L + 3 := by omega
      subst hW'
      have heq : L + 3 + 6 = L + 9 := by omega
      rw [heq] at hg0
      have P := pw_le 10 (L - 1) (by omega)
      have hp10 : pw 10 = 1024 := by decide
      rw [hp10] at P
      have := h9_s1 L C1 G r G1 (by omega) hC (by omega) (Or.inr hg0) hr
      omega
    · have pS := pw_S L
      have pLe := pw_le (L + 1) (L + 3) (by omega)
      exact h9_gen t k (2 * j) (2 * pw L) (2 * C1) (L + 3) L W G r G1 hk hG
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr
  · have pS := pw_S L
    have pLe := pw_le (L + 1) (L + 3) (by omega)
    exact h9_gen t k (2 * j) (2 * pw L) (2 * C1) (L + 3) L W G r G1 hk hG
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hr

private theorem zv_lt2 (t q W : ℕ) (h1 : t + 3 ≤ W) (h2 : q + 1 ≤ W) :
    zv t q < pw (Afun (t + 1) + (W + 1)) := by
  unfold zv
  have hY := yv_lt t (Afun (t + 1) + (t + 3)) (by omega)
  have p1 := pw_le (Afun (t + 1) + (t + 3)) (Afun (t + 1) + W) (by omega)
  have p2 := pw_le (q + 1) (Afun (t + 1) + W) (by omega)
  have p3 := pw_S q
  have p4 := pw_pos q
  have heq : Afun (t + 1) + (W + 1) = (Afun (t + 1) + W) + 1 := by omega
  rw [heq, pw_S]
  omega

private theorem y2v_lt2 (t q W : ℕ) (h1 : t + 4 ≤ W) (h2 : q + 3 ≤ Afun (t + 1) + W) :
    y2v t q < pw (Apr q + (Afun (t + 1) + (W + 1) + 1) - 1) := by
  have heq : Apr q + (Afun (t + 1) + (W + 1) + 1) - 1 = Apr q + (Afun (t + 1) + W + 1) := by omega
  rw [heq]
  exact y2v_lt t q (Afun (t + 1) + W) (by omega) h2

/-! ## Mixed Defect Carry Regimes -/

private theorem good_BO0 (t k j r2 c2 C2 W : ℕ)
    (hk : t + 1 = 2 * k + 1)
    (hC : pw r2 * (2 * C2 + 1) < pw (r2 + (c2 + 1)))
    (hL : 9 ≤ r2 + (c2 + 1))
    (hW1 : (t + 1) + (2 * j + (r2 + (c2 + 1) + 1)) + 1 ≤ W)
    (hW2 : W ≤ (t + 1) + (2 * j + (r2 + (c2 + 1) + 1)) + 2)
    (hbig : 26 ≤ t + 1 ∨ 90 ≤ W)
    (h83 : t = 0 → j = 0 → W = (t + 1) + (2 * j + (r2 + (c2 + 1) + 1)) + 1 →
      pw r2 * (2 * C2 + 1) ≠ 83) :
    Good (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
      (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (U B0)) W) := by
  set L := r2 + (c2 + 1)
  set C1 := pw r2 * (2 * C2 + 1)
  set Wf := Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd (2 * j)
  have hY : y2v t (2 * j) < pw (Wf - 1) := y2v_lt2 t (2 * j) W (by omega) (by omega)
  have hZ := zv_lt2 t (2 * j) W (by omega) (by omega)
  have hW : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have h2 := pw_le (L + 3) (Wf - 1) (by dsimp [Wf]; omega)
  have hc3 : pw (L + 3) = 8 * pw L := by rw [pw_add]; change pw L * 8 = 8 * pw L; ring
  have hS : pw (L + 1) = 2 * pw L := pw_S L
  have hp := pw_pos L
  set x' := y2v t (2 * j) + 2 * (pw L - C1)
  set xf := x' + 2 * pw (L + 1) - 1
  have hx1 : x' < pw Wf := by dsimp [x']; omega
  have hx2 : xf < pw Wf := by dsimp [xf, x']; omega
  set G := pw Wf - 1 - xf
  have hGe : G + y2v t (2 * j) + 6 * pw L = pw Wf + 2 * C1 := by dsimp [G, xf, x']; omega
  refine ⟨isOdd (L + 1), Apr (L + 1), Wf, G, ?_, ?_⟩
  · have hsub : pw Wf - 1 - G = xf := by dsimp [G]; omega
    rw [hsub]
    exact ReachesPlus.trans (b_O0 t k j r2 c2 C2 W hk (by omega) hZ hC hx1)
      (d3_fin (L + 1) Wf x' hx2)
  · have bA2 := Apr_bd (L + 1)
    rw [← Apr_S (L + 1)]
    exact close_O t k (2 * j) (6 * pw L) (2 * C1) (L + 3) W G (Apr (L + 1) - 1) (isOdd (L + 1))
      hk hGe (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbig
      (fun he r G1 hr => h9_BO0 t k j L C1 W G hk hL hC hW1 hW2 h83 hGe he r G1 hr)

private theorem good_DO0 (t k j r2 c2 C2 W : ℕ)
    (hk : t + 1 = 2 * k + 1)
    (hC1 : pw (r2 + (c2 + 1) - 1) ≤ pw r2 * (2 * C2 + 1))
    (hC : pw r2 * (2 * C2 + 1) < pw (r2 + (c2 + 1)))
    (hL : 11 ≤ r2 + (c2 + 1))
    (hW1 : W = (t + 1) + (2 * j + (r2 + (c2 + 1) + 1)) + 1)
    (hbig : 26 ≤ t + 1 ∨ 90 ≤ W) :
    Good (D1 (t + 1) (TL (bin (2 * j + (r2 + (c2 + 1) + 1))
      (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1))) (D3 B0)) W) := by
  set L := r2 + (c2 + 1)
  set C1 := pw r2 * (2 * C2 + 1)
  set Wf := Apr (2 * j) + (Afun (t + 1) + (W + 1) + 1)
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd (2 * j)
  have hY : y2v t (2 * j) < pw (Wf - 1) := y2v_lt2 t (2 * j) W (by omega) (by omega)
  have hZ := zv_lt2 t (2 * j) W (by omega) (by omega)
  have hW : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have h2 := pw_le (L + 1) (Wf - 1) (by dsimp [Wf]; omega)
  have hS : pw (L + 1) = 2 * pw L := pw_S L
  set xf := y2v t (2 * j) + 2 * (pw L - 1 - C1) + 1
  have hx : xf < pw Wf := by dsimp [xf]; omega
  set G := pw Wf - 1 - xf
  have hGe : G + y2v t (2 * j) + 2 * pw L = pw Wf + 2 * C1 := by dsimp [G, xf]; omega
  refine ⟨isEven L, Afun L, Wf, G, ?_, ?_⟩
  · have hsub : pw Wf - 1 - G = xf := by dsimp [G]; omega
    rw [hsub]
    exact d3_O0 t k j r2 c2 C2 W hk (by omega) hZ hC hx
  · have bA2 := Afun_bd L
    rw [← Afun_S L (by omega)]
    exact close_O t k (2 * j) (2 * pw L) (2 * C1) (L + 1) W G (Afun L - 1) (isEven L)
      hk hGe (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbig
      (fun _ r G1 hr => h9_DO0 t k j L C1 W G hk hL hC1 hC hW1 hGe r G1 hr)

private theorem odd_r0 (G r G1 a b : ℕ) (h1 : G + 2 * a = 2 * b + 1)
    (h2 : G = pw r * (2 * G1 + 1)) : r = 0 := by
  cases r with
  | zero => rfl
  | succ r =>
    exfalso
    have h2' : G = 2 * (pw r * (2 * G1 + 1)) := by rw [h2, pw_S]; ring
    omega

private theorem good_DO1 (t k j L C1 W : ℕ)
    (hk : t + 1 = 2 * k + 1) (_hC1 : pw (L - 1) ≤ C1) (hC : C1 + 1 < pw L)
    (hL : 11 ≤ L) (hW1 : W = (t + 1) + (2 * j + 1 + (L + 1)) + 1)
    (hbig : 26 ≤ t + 1 ∨ 90 ≤ W) :
    Good (D1 (t + 1)
      (TL (bin (2 * j + 1 + (L + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) (D3 B0)) W) := by
  set Wf := Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd (2 * j + 1)
  have hY : y2v t (2 * j + 1) < pw (Wf - 1) := y2v_lt2 t (2 * j + 1) W (by omega) (by omega)
  have hZ := zv_lt2 t (2 * j + 1) W (by omega) (by omega)
  have hW : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by dsimp [Wf]; omega)
  have h2 := pw_le (L + 1) (Wf - 1) (by dsimp [Wf]; omega)
  have hS : pw (L + 1) = 2 * pw L := pw_S L
  set xf := y2v t (2 * j + 1) + 1 + 2 * (pw L - 1 - (C1 + 1)) + 1
  have hx : xf < pw Wf := by dsimp [xf]; omega
  set G := pw Wf - 1 - xf
  have hGe : G + y2v t (2 * j + 1) + 2 * pw L = pw Wf + (2 * C1 + 1) := by dsimp [G, xf]; omega
  refine ⟨isOdd L, Apr L, Wf, G, ?_, ?_⟩
  · have hsub : pw Wf - 1 - G = xf := by dsimp [G]; omega
    rw [hsub]
    exact d3_O1 t k j L C1 W hk (by omega) hZ hC hx
  · have bA2 := Apr_bd L
    rw [← Apr_S L]
    exact close_O t k (2 * j + 1) (2 * pw L) (2 * C1 + 1) (L + 1) W G (Apr L - 1) (isOdd L)
      hk hGe (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hbig
      (fun _ r G1 hr => by
        have hy := y2v_y1o t (2 * j + 1)
        have e := odd_r0 G r G1 (y1o t (2 * j + 1) + pw L) (pw (Wf - 1) + C1) (by omega) hr
        omega)

/-! ## Overflow Closure Lemmas -/

private theorem good_back {c c' : Cfg Sym (Fin 6)}
    (h : ReachesPlus tm c c') (hg : Good c') : Good c := by
  obtain ⟨e, a, h', G, hs, hi⟩ := hg
  exact ⟨e, a, h', G, ReachesPlus.trans h hs, hi⟩

private theorem good_DE1' (t k c C W : ℕ)
    (hk : t + 1 = 2 * k) (h0 : C ≠ 0) (h1 : C + 1 < pw c) (h2 : 11 ≤ c)
    (h3 : W = (t + 1) + c + 1) :
    Good (D1 (t + 1) (TL (bin c C) (D3 B0)) W) := by
  obtain ⟨r, C1, rfl⟩ := N_tz C h0
  obtain ⟨c1, rfl, hc1⟩ := tz_bound c r C1 (by omega)
  exact good_DE1 t k r c1 C1 W hk h1 h2 h3

private theorem good_DO0' (t k j L C W : ℕ)
    (hk : t + 1 = 2 * k + 1) (h1 : pw (L - 1) ≤ C) (h2 : C < pw L) (h3 : 11 ≤ L)
    (h4 : W = (t + 1) + (2 * j + (L + 1)) + 1) (h5 : 26 ≤ t + 1 ∨ 90 ≤ W) :
    Good (D1 (t + 1) (TL (bin (2 * j + (L + 1)) (pw (2 * j) * (2 * C + 1))) (D3 B0)) W) := by
  have P := pw_pos (L - 1)
  obtain ⟨r, C2, rfl⟩ := N_tz C (by omega)
  obtain ⟨c2, rfl, hc2⟩ := tz_bound L r C2 h2
  exact good_DO0 t k j r c2 C2 W hk h1 h2 h3 h4 h5

private theorem good_BO0' (t k j L C W : ℕ)
    (hk : t + 1 = 2 * k + 1) (h0 : C ≠ 0) (h1 : C < pw L) (h2 : 9 ≤ L)
    (h3 : (t + 1) + (2 * j + (L + 1)) + 1 ≤ W)
    (h4 : W ≤ (t + 1) + (2 * j + (L + 1)) + 2)
    (h5 : 26 ≤ t + 1 ∨ 90 ≤ W)
    (h6 : t = 0 → j = 0 → W = (t + 1) + (2 * j + (L + 1)) + 1 → C ≠ 83) :
    Good (D1 (t + 1) (TL (bin (2 * j + (L + 1)) (pw (2 * j) * (2 * C + 1))) (U B0)) W) := by
  obtain ⟨r, C2, rfl⟩ := N_tz C h0
  obtain ⟨c2, rfl, hc2⟩ := tz_bound L r C2 h1
  exact good_BO0 t k j r c2 C2 W hk h1 h2 h3 h4 h5 h6

private theorem good_D3 (t c Ev u : ℕ)
    (h0 : Ev ≠ 0) (h1 : Ev < pw c) (hu : u = t + c + 11) (hb : 88 ≤ u) :
    Good (D1 (t + 1) (TL (bin (c + 11) (Ev + pw (c + 10))) (D3 B0)) (u + 2)) := by
  have p2 : pw (c + 10) = 1024 * pw c := pw_10 c
  have p3 : pw (c + 11) = 2048 * pw c := by rw [pw_add]; change pw c * 2048 = 2048 * pw c; ring
  rcases N_parity (t + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact good_DE1' t k (c + 11) (Ev + pw (c + 10)) (u + 2) hk
      (by omega) (by omega) (by omega) (by omega)
  · obtain ⟨q, E2, rfl⟩ := N_tz Ev h0
    obtain ⟨c2, rfl, hc2⟩ := tz_bound c q E2 h1
    have q2 : pw (c2 + 10) = 1024 * pw c2 := pw_10 c2
    have q3 : pw (c2 + 11) = 2048 * pw c2 := by
      rw [pw_add]; change pw c2 * 2048 = 2048 * pw c2; ring
    have hC : pw q * (2 * E2 + 1) + pw (q + (c2 + 1) + 10) =
        pw q * (2 * (E2 + pw (c2 + 10)) + 1) := by
      have heq : q + (c2 + 1) + 10 = q + ((c2 + 10) + 1) := by omega
      rw [heq, pw_add, pw_S]; ring
    have hlen : q + (c2 + 1) + 11 = q + ((c2 + 11) + 1) := by omega
    rw [hC]
    have pc_pos' := pw_pos c2
    rcases N_parity q with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [hlen]
      exact good_DO0' t k j (c2 + 11) (E2 + pw (c2 + 10)) (u + 2) hk
        (by have : c2 + 11 - 1 = c2 + 10 := (by omega); rw [this]; omega)
        (by omega) (by omega) (by omega) (by omega)
    · rw [hlen]
      exact good_DO1 t k j (c2 + 11) (E2 + pw (c2 + 10)) (u + 2) hk
        (by have : c2 + 11 - 1 = c2 + 10 := (by omega); rw [this]; omega)
        (by omega) (by omega) (by omega) (by omega)

private theorem good_tailL (u D n : ℕ)
    (hn : n = u + 1) (h0 : D ≠ 0) (hp : ∀ x, D ≠ pw x)
    (h1 : D < pw (u - 10)) (hb : 88 ≤ u) :
    Good (AC (TL (bin u D) (U B0)) (oL n)) := by
  subst hn
  obtain ⟨t, Ev, rfl⟩ := N_tz D h0
  have hE : Ev ≠ 0 := by intro e0; subst e0; exact hp t (by ring)
  obtain ⟨c, ec, hEc⟩ := tz_bound (u - 10) t Ev h1
  have hu : u = t + c + 11 := by omega
  have h2 : pw u + pw t * (2 * Ev + 1) = pw t * (2 * (Ev + pw (c + 10)) + 1) := by
    have heq : u = t + ((c + 10) + 1) := by omega
    rw [heq, pw_add, pw_S]; ring
  have h3 : pw t * (2 * Ev + 1) + 1 < pw u := by
    have := pw_lt (u - 10) u (by omega)
    have := pw_pos (u - 10)
    omega
  exact good_back (tailL u _ t (c + 11) (Ev + pw (c + 10)) h0 h3 h2 (by omega))
    (good_D3 t c Ev u hE hEc hu hb)

private theorem tz_sub (n Ev B r G1 : ℕ)
    (h0 : Ev ≠ 0) (h1 : Ev < pw B) (h2 : B ≤ n)
    (h3 : pw n = pw r * (2 * G1 + 1) + Ev) : r < B := by
  by_contra hge
  obtain ⟨Z, hZ⟩ := mult_split r B G1 (by omega)
  rw [hZ, pw_split B n h2] at h3
  have e2 : pw (n - B) * pw B + 0 = Z * pw B + Ev := by linarith
  obtain ⟨_, e3⟩ := mod_uniq (pw B) (pw (n - B)) Z 0 Ev (pw_pos B) h1 e2
  exact h0 e3.symm

private theorem good_TS2 (u Vl Ev B n : ℕ)
    (hn : n = u + 2) (h0 : Vl ≠ 0) (h1 : Vl + Ev = pw u) (h2 : Ev ≠ 0)
    (h3 : Ev < pw B) (h4 : B + 6 ≤ u) (h5 : 10 ≤ u) :
    Good (AC (TL (bin u Vl) (U B0)) (oL n)) := by
  subst hn
  refine good_TS u Vl h0 (by omega) h5 ?_
  intro _ r G1 hr
  have hE : pw (u + 1) = pw r * (2 * G1 + 1) + Ev := by rw [pw_S]; omega
  have := tz_sub (u + 1) Ev B r G1 h2 h3 (by omega) hE
  omega

/-! ## Odd-Stage Defect Splitting -/

private theorem y1o_bound (t q : ℕ) : y1o t q < pw (Apr q + (Afun (t + 1) + (t + 4) + q)) := by
  have h := y2v_lt t q (Afun (t + 1) + (t + 4) + q) (by omega) (by omega)
  have e := y2v_y1o t q
  have heq : Apr q + (Afun (t + 1) + (t + 4) + q + 1) =
      (Apr q + (Afun (t + 1) + (t + 4) + q)) + 1 := by omega
  rw [heq, pw_S] at h
  omega

private theorem good_BO1 (t k j c1 C1 W : ℕ)
    (hk : t + 1 = 2 * k + 1) (h1 : C1 < pw c1) (h2 : 9 ≤ c1)
    (h3 : (t + 1) + (2 * j + 1 + (c1 + 1)) + 1 ≤ W) (hbig : 26 ≤ t + 1 ∨ 90 ≤ W)
    (hD : y1o t (2 * j + 1) ≤ C1 + pw c1 →
      C1 + pw c1 - y1o t (2 * j + 1) ≠ 0 ∧ ∀ x, C1 + pw c1 - y1o t (2 * j + 1) ≠ pw x) :
    Good (D1 (t + 1)
      (TL (bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * C1 + 1))) (U B0)) W) := by
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd (2 * j + 1)
  have hZ := zv_lt2 t (2 * j + 1) W (by omega) (by omega)
  have hy := y2v_y1o t (2 * j + 1)
  have hB := y1o_bound t (2 * j + 1)
  set W2 := Apr (2 * j + 1) + (Afun (t + 1) + (W + 1) + 1)
  set Bv := Apr (2 * j + 1) + (Afun (t + 1) + (t + 4) + (2 * j + 1))
  have hW : pw W2 = 2 * pw (W2 - 1) := pw_pred2 W2 (by dsimp [W2]; omega)
  have hW' : pw (W2 - 1) = 2 * pw (W2 - 2) := by
    have : W2 - 2 = W2 - 1 - 1 := by omega
    rw [this]; exact pw_pred2 (W2 - 1) (by dsimp [W2]; omega)
  have hBu : Bv + 6 ≤ W2 - 2 := by dsimp [Bv, W2]; omega
  have p1 := pw_le Bv (W2 - 2) (by omega)
  have p2 := pw_le (c1 + 1) (W2 - 2) (by dsimp [W2]; omega)
  have p3 := pw_le (c1 + 1) (W2 - 1 - 10) (by dsimp [W2]; omega)
  have p4 := pw_S c1
  have hK : y2v t (2 * j + 1) + 1 + 2 * (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) + 1 =
      pw W2 := by omega
  rcases le_or_gt (y1o t (2 * j + 1)) (C1 + pw c1) with hle | hlt
  · obtain ⟨hD0, hDp⟩ := hD hle
    exact good_back
      (b_O1 t k j c1 C1 W (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) (W2 - 1)
        (C1 + pw c1 - y1o t (2 * j + 1)) hk (by omega) hZ h1 hK
        (by dsimp [W2]; omega) (by omega) (by omega) (by omega))
      (good_tailL (W2 - 1) (C1 + pw c1 - y1o t (2 * j + 1)) W2
        (by dsimp [W2]; omega) hD0 hDp (by omega) (by dsimp [W2]; omega))
  · exact good_back
      (b_O1 t k j c1 C1 W (pw (W2 - 1) - 1 - y1o t (2 * j + 1)) (W2 - 2)
        (pw (W2 - 2) + (C1 + pw c1) - y1o t (2 * j + 1)) hk (by omega) hZ h1 hK
        (by dsimp [W2]; omega) (by omega) (by omega) (by omega))
      (good_TS2 (W2 - 2) (pw (W2 - 2) + (C1 + pw c1) - y1o t (2 * j + 1))
        (y1o t (2 * j + 1) - (C1 + pw c1)) Bv W2
        (by dsimp [W2]; omega) (by omega) (by omega)
        (by omega) (by omega) hBu (by dsimp [W2]; omega))

private theorem good_B (t c C W : ℕ)
    (h0 : C ≠ 0) (h1 : C < pw c)
    (h2 : (t + 1) + c + 1 ≤ W) (h3 : W ≤ (t + 1) + c + 2)
    (hbig : 26 ≤ t + 1 ∨ 90 ≤ W)
    (hE : ∀ k, t + 1 = 2 * k → 9 ≤ c)
    (hO : ∀ k, t + 1 = 2 * k + 1 → ∀ q c1 C1, C = pw q * (2 * C1 + 1) → c = q + (c1 + 1) →
      9 ≤ c1 ∧ C1 ≠ 0 ∧ (∀ j, q = 2 * j + 1 → y1o t q ≤ C1 + pw c1 →
        C1 + pw c1 - y1o t q ≠ 0 ∧ ∀ x, C1 + pw c1 - y1o t q ≠ pw x))
    (h83 : t = 0 → W = (t + 1) + c + 1 → C ≠ 167) :
    Good (D1 (t + 1) (TL (bin c C) (U B0)) W) := by
  rcases N_parity (t + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
  · exact good_BE1 t k c C W hk h0 h1 (hE k hk) h2 h3
  · obtain ⟨q, C1, hC⟩ := N_tz C h0
    obtain ⟨c1, ec, hc1⟩ := tz_bound c q C1 (by rw [← hC]; exact h1)
    obtain ⟨h9, hn, hD⟩ := hO k hk q c1 C1 hC ec
    subst hC ec
    rcases N_parity q with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact good_BO0' t k j c1 C1 W hk hn hc1 h9 h2 h3 hbig (fun et ej hw e83 => by
        subst et ej e83
        exact h83 rfl hw (by decide))
    · exact good_BO1 t k j c1 C1 W hk hc1 h9 h2 hbig (hD j rfl)

/-! ## Carry Exclusion Bounds -/

private theorem cell0_of (Y c Q b : ℕ) (h1 : Y = Q * pw (c + 1) + b) (h2 : b < pw c) : cell0 Y c :=
  ⟨Q, b, h2, h1⟩

private theorem pw_factor (x y : ℕ) (h : x ≤ y) : ∃ z, pw y = z * pw x ∧ z = pw (y - x) :=
  ⟨pw (y - x), by rw [pw_split x y h]; ring, rfl⟩

private theorem Ya_form (m : ℕ) (_h : 1 ≤ m) : Ya m = 4 * (pw m - 1) + 1 := by
  unfold Ya; rw [pw_add_r2]; have := pw_pos m; omega

private theorem Yc_form (a r : ℕ) : pw a * (pw (r + 2) - 1) = pw (a + (r + 2)) - pw a := by
  rw [pw_add a (r + 2)]
  have p := pw_pos (r + 2)
  have ha := pw_pos a
  have hle : pw a ≤ pw a * pw (r + 2) := by nlinarith
  zify [p, hle]
  ring

private theorem cz_low (t r c : ℕ) (h : c + 2 ≤ Apr r) : cell0 (y1o t r) c := by
  rw [y1o_split]
  obtain ⟨z1, e1, _⟩ := pw_factor (c + 1) (Apr r + Afun (t + 1)) (by omega)
  obtain ⟨z2, e2, _⟩ := pw_factor (c + 1) (Apr r - 1) (by omega)
  refine cell0_of _ c (z1 * Ya (t + 1) + z2 * (pw (r + 2) - 1)) 0 ?_ (pw_pos c)
  rw [e1, e2]; ring

private theorem Yc_bound (r : ℕ) : pw (Apr r - 1) * (pw (r + 2) - 1) < pw (Apr r + r + 1) := by
  have h := Yc_lt (Apr r - 1) r
  have hp := Apr_pos r
  have heq : Apr r - 1 + (r + 2) = Apr r + r + 1 := by omega
  rwa [heq] at h

private theorem cz_gap (t r c : ℕ) (h1 : Apr r + r + 1 ≤ c) (h2 : c < Apr r + Afun (t + 1)) :
    cell0 (y1o t r) c := by
  rw [y1o_split]
  obtain ⟨z1, e1, _⟩ := pw_factor (c + 1) (Apr r + Afun (t + 1)) (by omega)
  refine cell0_of _ c (z1 * Ya (t + 1)) (pw (Apr r - 1) * (pw (r + 2) - 1)) ?_
    (lt_of_lt_of_le (Yc_bound r) (pw_le _ _ h1))
  rw [e1]; ring

private theorem y1o_form (t r : ℕ) :
    y1o t r = pw (Apr r + Afun (t + 1) + 2) * (pw (t + 1) - 1) +
      pw (Apr r + Afun (t + 1)) + pw (Apr r - 1) * (pw (r + 2) - 1) := by
  rw [y1o_split, Ya_form (t + 1) (by omega), pw_add_r2 (Apr r + Afun (t + 1))]
  ring

private theorem cz_a31 (t r : ℕ) (h : r + 1 ≤ Afun (t + 1)) :
    cell0 (y1o t r) (Apr r + Afun (t + 1) + 1) := by
  rw [y1o_form]
  set a3 := Apr r + Afun (t + 1)
  refine cell0_of _ (a3 + 1) (pw (t + 1) - 1) (pw a3 + pw (Apr r - 1) * (pw (r + 2) - 1)) ?_ ?_
  · ring
  · have B := Yc_bound r
    have P := pw_le (Apr r + r + 1) a3 (by dsimp [a3]; omega)
    rw [pw_S a3]; omega

private theorem Yc_exact (r : ℕ) :
    pw (Apr r - 1) * (pw (r + 2) - 1) = pw (Apr r + r + 1) - pw (Apr r - 1) := by
  rw [Yc_form]
  have hp := Apr_pos r
  have heq : Apr r - 1 + (r + 2) = Apr r + r + 1 := by omega
  rw [heq]

private theorem cz_Q2 (t r : ℕ) (h : r = Afun (t + 1)) :
    cell0 (y1o t r) (Apr r + Afun (t + 1)) := by
  rw [y1o_form, Yc_exact, ← h]
  set a3 := Apr r + r
  have p0 : pw (Apr r - 1) < pw a3 := by
    have := pw_lt (Apr r - 1) a3 (by have := Apr_pos r; dsimp [a3]; omega)
    have := pw_pos (Apr r - 1)
    omega
  have p00 := pw_pos (Apr r - 1)
  have p1 : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  have p2 : pw (a3 + 2) = 4 * pw a3 := pw_add_r2 a3
  refine cell0_of _ a3 (2 * (pw (t + 1) - 1) + 1) (pw a3 - pw (Apr r - 1)) ?_ (by omega)
  rw [p1, p2]
  have hp_t := pw_pos (t + 1)
  have hsub2 : pw (Apr r - 1) ≤ 2 * pw a3 := by omega
  zify [hp_t, le_of_lt p0, hsub2]
  ring

private theorem cz_M (t r c : ℕ) (h : Afun (t + 1) + 1 ≤ r)
    (hc : c = Apr r + Afun (t + 1) ∨ c = Apr r + Afun (t + 1) + 1) :
    cell0 (y1o t r) c := by
  rw [y1o_form, Yc_exact]
  set a3 := Apr r + Afun (t + 1)
  obtain ⟨z, e, _⟩ := pw_factor (a3 + 2) (Apr r + r + 1) (by dsimp [a3]; omega)
  have p0 : pw (Apr r - 1) < pw a3 := by
    have := pw_lt (Apr r - 1) a3 (by have := Apr_pos r; have := Afun_pos t; dsimp [a3]; omega)
    have := pw_pos (Apr r - 1)
    omega
  have p00 := pw_pos (Apr r - 1)
  have p1 : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  have p2 : pw (a3 + 2) = 4 * pw a3 := pw_add_r2 a3
  have hz : pw (a3 + 2) ≤ pw (Apr r + r + 1) := pw_le _ _ (by dsimp [a3]; omega)
  rw [p2] at e hz
  have hp_t := pw_pos (t + 1)
  rcases hc with rfl | rfl
  · refine cell0_of _ a3 (2 * (pw (t + 1) - 1 + z)) (pw a3 - pw (Apr r - 1)) ?_ (by omega)
    rw [p1, p2, e]
    have hsub_ok : pw (Apr r - 1) ≤ z * (4 * pw a3) := by omega
    zify [hp_t, le_of_lt p0, hsub_ok]
    ring
  · refine cell0_of _ (a3 + 1) (pw (t + 1) - 1 + z) (pw a3 - pw (Apr r - 1)) ?_ (by rw [p1]; omega)
    have h_s : (a3 + 1) + 1 = a3 + 2 := rfl
    rw [h_s, p2, e]
    have hsub_ok : pw (Apr r - 1) ≤ z * (4 * pw a3) := by omega
    zify [hp_t, le_of_lt p0, hsub_ok]
    ring

private theorem y1o_ltT (t r T : ℕ) (h1 : Afun (t + 1) + (t + 4) ≤ T) (h2 : r + 3 ≤ T) :
    y1o t r < pw (Apr r + T) := by
  have h := y2v_lt t r T h1 h2
  have e := y2v_y1o t r
  have heq : Apr r + (T + 1) = (Apr r + T) + 1 := by omega
  rw [heq, pw_S] at h
  omega

private theorem cz_top (t r T c : ℕ) (h1 : Afun (t + 1) + (t + 4) ≤ T) (h2 : r + 3 ≤ T)
    (h3 : Apr r + T ≤ c) : cell0 (y1o t r) c :=
  cell0_of _ c 0 (y1o t r) (by simp) (lt_of_lt_of_le (y1o_ltT t r T h1 h2) (pw_le _ _ h3))

private theorem y1o_lt4 (t r : ℕ) (h : r ≤ Afun (t + 1)) :
    y1o t r < pw (Apr r + Afun (t + 1) + (t + 3)) := by
  rw [y1o_form]
  set a3 := Apr r + Afun (t + 1)
  have B := Yc_bound r
  have P := pw_le (Apr r + r + 1) (a3 + 1) (by dsimp [a3]; omega)
  rw [pw_S a3] at P
  have heq : a3 + (t + 3) = (a3 + 2) + (t + 1) := by omega
  rw [heq, pw_add (a3 + 2) (t + 1), pw_add_r2]
  have Q := pw_pos (t + 1)
  have pa3 := pw_pos a3
  have hmul : 4 * pw a3 * (pw (t + 1) - 1) + 4 * pw a3 = 4 * pw a3 * pw (t + 1) := by
    zify [Q]; ring
  omega

private theorem cz_top2 (t r c : ℕ)
    (h1 : r ≤ Afun (t + 1)) (h2 : Apr r + Afun (t + 1) + (t + 3) ≤ c) :
    cell0 (y1o t r) c :=
  cell0_of _ c 0 (y1o t r) (by simp) (lt_of_lt_of_le (y1o_lt4 t r h1) (pw_le _ _ h2))

/-! ## Popcount Exclusion of Isolated Carries -/

private theorem two_cells (t j u0 v0 : ℕ)
    (h : 2 * (u0 + (t + 1) + (2 * j + 1) + 1) + 18 ≤ 5 * (v0 - u0)) :
    ∃ c1 c2, u0 ≤ c1 ∧ c1 < c2 ∧ c2 < v0 ∧
      cell0 (y1o t (2 * j + 1)) c1 ∧ cell0 (y1o t (2 * j + 1)) c2 := by
  have bA := Afun_bd (t + 1)
  have bP := Apr_bd (2 * j + 1)
  set Ap := Apr (2 * j + 1)
  set A := Afun (t + 1)
  set R := 2 * j + 1
  set m := t + 1
  set Y := y1o t (2 * j + 1)
  have zlow : ∀ c, c + 2 ≤ Ap → cell0 Y c := cz_low t (2 * j + 1)
  have zgap : ∀ c, Ap + R + 1 ≤ c → c < Ap + A → cell0 Y c := cz_gap t (2 * j + 1)
  have z31 : R + 1 ≤ A → cell0 Y (Ap + A + 1) := cz_a31 t (2 * j + 1)
  have zQ : R = A → cell0 Y (Ap + A) := cz_Q2 t (2 * j + 1)
  have zM : ∀ c, A + 1 ≤ R → (c = Ap + A ∨ c = Ap + A + 1) → cell0 Y c :=
    fun c h1 h2 => cz_M t (2 * j + 1) c h1 h2
  have ztop : ∀ T c, A + (m + 3) ≤ T → R + 3 ≤ T → Ap + T ≤ c → cell0 Y c := cz_top t (2 * j + 1)
  have z42 : ∀ c, R ≤ A → Ap + A + (m + 2) ≤ c → cell0 Y c := cz_top2 t (2 * j + 1)
  rcases le_or_gt (u0 + 3) Ap with l0 | l0
  · exact ⟨u0, u0 + 1, by omega, by omega, by omega, zlow _ (by omega), zlow _ (by omega)⟩
  rcases le_or_gt (R + 1) A with s1 | s1
  · by_cases u : u0 + 2 = Ap
    · by_cases e : R + 1 = A
      · exact ⟨u0, Ap + A + 1, by omega, by omega, by omega, zlow _ (by omega), z31 s1⟩
      · exact ⟨u0, Ap + R + 1, by omega, by omega, by omega,
          zlow _ (by omega), zgap _ (by omega) (by omega)⟩
    · rcases lt_or_ge u0 (Ap + R + 1) with u2 | u2
      · rcases lt_trichotomy (R + 2) A with e | e | e
        · exact ⟨Ap + R + 1, Ap + R + 2, by omega, by omega, by omega,
            zgap _ (by omega) (by omega), zgap _ (by omega) (by omega)⟩
        · exact ⟨Ap + R + 1, Ap + A + 1, by omega, by omega, by omega,
            zgap _ (by omega) (by omega), z31 s1⟩
        · exact ⟨Ap + A + 1, Ap + A + (m + 2), by omega, by omega, by omega,
            z31 s1, z42 _ (by omega) (by omega)⟩
      · rcases lt_or_ge (u0 + 1) (Ap + A) with u3 | u3
        · exact ⟨u0, u0 + 1, by omega, by omega, by omega,
            zgap _ (by omega) (by omega), zgap _ (by omega) (by omega)⟩
        · by_cases u4 : u0 + 1 = Ap + A
          · exact ⟨u0, Ap + A + 1, by omega, by omega, by omega,
              zgap _ (by omega) (by omega), z31 s1⟩
          · rcases le_or_gt u0 (Ap + A + 1) with u5 | u5
            · exact ⟨Ap + A + 1, Ap + A + (m + 2), by omega, by omega, by omega,
                z31 s1, z42 _ (by omega) (by omega)⟩
            · rcases lt_or_ge u0 (Ap + A + (m + 2)) with u6 | u6
              · exact ⟨Ap + A + (m + 2), Ap + A + (m + 2) + 1, by omega, by omega, by omega,
                  z42 _ (by omega) (by omega), z42 _ (by omega) (by omega)⟩
              · exact ⟨u0, u0 + 1, by omega, by omega, by omega,
                  z42 _ (by omega) (by omega), z42 _ (by omega) (by omega)⟩
  · by_cases e : R = A
    · by_cases u : u0 + 2 = Ap
      · exact ⟨u0, Ap + A, by omega, by omega, by omega, zlow _ (by omega), zQ e⟩
      · rcases le_or_gt u0 (Ap + A) with u2 | u2
        · exact ⟨Ap + A, Ap + A + (m + 2), by omega, by omega, by omega,
            zQ e, z42 _ (by omega) (by omega)⟩
        · rcases lt_or_ge u0 (Ap + A + (m + 2)) with u6 | u6
          · exact ⟨Ap + A + (m + 2), Ap + A + (m + 2) + 1, by omega, by omega, by omega,
              z42 _ (by omega) (by omega), z42 _ (by omega) (by omega)⟩
          · exact ⟨u0, u0 + 1, by omega, by omega, by omega,
              z42 _ (by omega) (by omega), z42 _ (by omega) (by omega)⟩
    · set T := max (A + (m + 3)) (R + 3)
      have zT : ∀ c, Ap + T ≤ c → cell0 Y c :=
        fun c hc => ztop T c (le_max_left _ _) (le_max_right _ _) hc
      have hAR : A + 1 ≤ R := by omega
      by_cases u : u0 + 2 = Ap
      · exact ⟨u0, Ap + A, by omega, by omega, by omega, zlow _ (by omega), zM _ hAR (Or.inl rfl)⟩
      · rcases le_or_gt u0 (Ap + A) with u2 | u2
        · exact ⟨Ap + A, Ap + A + 1, by omega, by omega, by omega,
            zM _ hAR (Or.inl rfl), zM _ hAR (Or.inr rfl)⟩
        · by_cases u3 : u0 = Ap + A + 1
          · exact ⟨Ap + A + 1, Ap + T, by omega, by dsimp [T]; omega, by dsimp [T]; omega,
              zM _ hAR (Or.inr rfl), zT _ (by omega)⟩
          · rcases lt_or_ge u0 (Ap + T) with u4 | u4
            · exact ⟨Ap + T, Ap + T + 1, by omega, by omega, by dsimp [T] at u4 ⊢; omega,
                zT _ (by omega), zT _ (by omega)⟩
            · exact ⟨u0, u0 + 1, by omega, by omega, by omega, zT _ u4, zT _ (by omega)⟩

private theorem N2_run (Z u t C q C1 c1 j p0 q0 : ℕ)
    (hZ : Z = pw t * (2 * C + 1)) (hC : C = pw q * (2 * C1 + 1))
    (hq : q = 2 * j + 1) (hu : u = t + ((q + (c1 + 1)) + 1))
    (hrun : ones_on Z p0 q0) (hq0 : q0 ≤ u) (hratio : 2 * p0 + 25 ≤ 5 * (q0 - p0)) :
    C1 + pw c1 ≠ y1o t q ∧ ∀ x, C1 + pw c1 ≠ y1o t q + pw x := by
  have ht := ones_tz Z C t p0 q0 hZ hrun (by omega)
  have ht2 : t < p0 := by
    by_cases e : t = p0
    · exfalso
      have r1 := ones_sub_lo Z p0 (p0 + 1) q0 hrun (by omega)
      have r2 := ones_shift_val Z C t (p0 + 1) q0 hZ r1 (by omega)
      have r3 := ones_tz C C1 q _ _ hC r2 (by omega)
      omega
    · omega
  have r2 := ones_shift_val Z C t p0 q0 hZ hrun ht2
  have r3 := ones_tz C C1 q _ _ hC r2 (by omega)
  have r4 := ones_sub_lo C (p0 - (t + 1)) ((p0 + 1) - (t + 1)) (q0 - (t + 1)) r2 (by omega)
  have r5 := ones_shift_val C C1 q _ _ hC r4 (by omega)
  set u0 := (p0 + 1) - (t + 1) - (q + 1)
  set v0 := q0 - (t + 1) - (q + 1)
  have r6 := ones_high C1 u0 v0 c1 r5 (by dsimp [v0]; omega)
  subst hq
  obtain ⟨c2, c3, h1, h2, h3, h4, h5⟩ := two_cells t j u0 v0 (by dsimp [u0, v0]; omega)
  exact two_zero _ _ c2 c3 h2
    (ones_cell _ u0 v0 c2 r6 (by omega))
    (ones_cell _ u0 v0 c3 r6 (by omega)) h4 h5

/-! ## Trailing-Zero Uniqueness and Remainder Splitting -/

private theorem tz_uniq (a x b y : ℕ)
    (h : pw a * (2 * x + 1) = pw b * (2 * y + 1)) : a = b ∧ x = y := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero => rw [pw_0] at h; exact ⟨rfl, by omega⟩
    | succ b =>
      exfalso
      have hb : pw 0 * (2 * x + 1) = 2 * (pw b * (2 * y + 1)) := by rw [h, pw_S]; ring
      rw [pw_0] at hb; omega
  | succ a ih =>
    cases b with
    | zero =>
      exfalso
      have ha : 2 * (pw a * (2 * x + 1)) = pw 0 * (2 * y + 1) := by rw [← h, pw_S]; ring
      rw [pw_0] at ha; omega
    | succ b =>
      have hab : 2 * (pw a * (2 * x + 1)) = 2 * (pw b * (2 * y + 1)) := by
        rw [pw_S, pw_S] at h; linarith
      obtain ⟨rfl, rfl⟩ := ih b (by omega)
      exact ⟨rfl, rfl⟩

private theorem good_Z (Z t c C W Zh v p : ℕ)
    (hZ : Z = pw t * (2 * C + 1)) (hC : C < pw c)
    (hZv : Z = Zh * pw p + v) (h0 : v ≠ 0) (h1 : v < pw p) (hnp : ∀ x, v ≠ pw x)
    (hp : p + 9 ≤ t + (c + 1)) (hpc : 3 ≤ pc Z)
    (hW1 : (t + 1) + c + 1 ≤ W) (hW2 : W ≤ (t + 1) + c + 2)
    (hbig : 26 ≤ t + 1 ∨ 90 ≤ W)
    (h83 : t = 0 → W = (t + 1) + c + 1 → C ≠ 167)
    (hD : ∀ k q c1 C1 j, t + 1 = 2 * k + 1 → C = pw q * (2 * C1 + 1) →
      c = q + (c1 + 1) → q = 2 * j + 1 →
      C1 + pw c1 ≠ y1o t q ∧ ∀ x, C1 + pw c1 ≠ y1o t q + pw x) :
    Good (D1 (t + 1) (TL (bin c C) (U B0)) W) := by
  have hC0 : C ≠ 0 := by
    intro e; subst e
    have : Z = pw t := by omega
    rw [this, pc_pw] at hpc; omega
  have hsb : ∀ q C1, C = pw q * (2 * C1 + 1) → t + q + 2 ≤ p :=
    fun q C1 hq => second_bit Zh v p t C q C1 h0 h1 hnp (by linarith) hq
  refine good_B t c C W hC0 hC hW1 hW2 hbig ?_ ?_ h83
  · intro k _
    obtain ⟨q, C1, hq⟩ := N_tz C hC0
    have := hsb q C1 hq; omega
  · intro k hk q c1 C1 hq hc
    have hs := hsb q C1 hq
    refine ⟨by omega, ?_, ?_⟩
    · intro e; subst e
      have e2 : Z = pw t + pw (t + (q + 1)) := by
        rw [hZ, hq, pw_add t (q + 1), pw_S]; ring
      rw [e2] at hpc
      have := pc_two t (t + (q + 1))
      omega
    · intro j hj hle
      obtain ⟨d1, d2⟩ := hD k q c1 C1 j hk hq hc hj
      exact ⟨by omega, fun x e => d2 x (by omega)⟩

private theorem G1_ne (r G1 h : ℕ)
    (h1 : pw (h - 2) ≤ pw r * (2 * G1 + 1)) (h2 : r + 3 ≤ h) : G1 ≠ 0 := by
  intro e; subst e
  have := pw_lt r (h - 2) (by omega)
  have := pw_pos r
  omega

private theorem step_e1 (a h G : ℕ) (hInv : Inv true a h G) :
    Good (FC true a h (pw h - 1 - G)) := by
  obtain ⟨ha, hh, hlo, hhi, r, G1, hG, hr, he, hra, hD⟩ := hInv
  cases a with
  | zero => omega
  | succ t =>
    have p0 := pw_pos (h - 2)
    have p1 := pw_S h
    refine good_back (F1_D1 t h G (pw h - 1 - G) (by omega)) ?_
    have he9 := he rfl
    refine good_B t (h + 1) G (t + (h + 1) + 2) (by omega) (by omega) (by omega) (by omega)
      (Or.inl (by omega)) (fun _ _ => by omega) ?_ (fun et => by omega)
    intro k hk q c1 C1 hq hc
    obtain ⟨hq_eq, hC1_eq⟩ := tz_uniq q C1 r G1 (by linarith)
    subst q C1
    have ec1 : c1 = h - r := by omega
    subst ec1
    refine ⟨by omega, G1_ne r G1 h (by linarith) hr, ?_⟩
    intro j hj hle
    obtain ⟨_, _, h3⟩ := hD t rfl
    have hev : isEven (t + 1) = false := by rw [hk]; exact even_2j1 k
    have hod : isOdd r = true := by rw [hj]; exact odd_2j1 j
    obtain ⟨p, q0, hrun, hrat⟩ := h3 hev rfl hod hle
    exact ones_not_pow _ p q0 hrun (by omega)

private theorem good_TS3 (u Vl n : ℕ)
    (hn : n = u + 2) (h0 : Vl ≠ 0) (h1 : Vl + 1 ≤ pw u) (h2 : 10 ≤ u)
    (h3 : ∀ r G1, isOdd (u + 1) = true → pw u + Vl = pw r * (2 * G1 + 1) → r + 7 ≤ u) :
    Good (AC (TL (bin u Vl) (U B0)) (oL n)) := by
  subst hn
  exact good_TS u Vl h0 h1 h2 (fun ho r G1 hr => h3 r G1 ho hr)

private theorem TS_small (u r2 G2 y1 Yq f G : ℕ)
    (hy : y1 = pw f * Yq) (h0 : G ≠ 0) (h1 : G < pw f) (h2 : f ≤ u + 1)
    (h3 : pw (u + 1) + G = pw r2 * (2 * G2 + 1) + y1) : r2 < f := by
  by_contra hge
  obtain ⟨Z, hZ⟩ := mult_split r2 f G2 (by omega)
  rw [hZ, hy, pw_split f (u + 1) h2] at h3
  have e : pw (u + 1 - f) * pw f + G = (Z + Yq) * pw f + 0 := by linarith
  obtain ⟨_, e3⟩ := mod_uniq (pw f) (pw (u + 1 - f)) (Z + Yq) G 0 h1 (pw_pos f) e
  exact h0 e3

private theorem step_e0_even (t k h G : ℕ) (hk : t + 1 = 2 * k) (hInv : Inv false (t + 1) h G) :
    Good (FC false (t + 1) h (pw h - 1 - G)) := by
  obtain ⟨ha, hh, hlo, hhi, r, G1, hG, hr, _, hra, hD⟩ := hInv
  refine good_back (F0_D1 t h G (pw h - 1 - G) (by omega)) ?_
  obtain ⟨hd1, _⟩ := hD t rfl
  have hev : isEven (t + 1) = true := by rw [hk]; exact even_2j k
  have hd := hd1 hev rfl
  obtain ⟨c1, ec, hc1⟩ := tz_bound h r G1 (by rw [← hG]; exact hhi)
  have bA := Afun_bd (t + 1)
  set W0 := t + (h + 1) + 1
  set W2 := Afun (t + 1) + (W0 + 1)
  have hY := yv_lt t (Afun (t + 1) + (t + 3)) (by omega)
  have hye := yv_y1e t
  have hW : pw W2 = 2 * pw (W2 - 1) := pw_pred2 W2 (by dsimp [W2]; omega)
  have hW' : pw (W2 - 1) = 2 * pw (W2 - 2) := by
    have : W2 - 2 = W2 - 1 - 1 := by omega
    rw [this]; exact pw_pred2 (W2 - 1) (by dsimp [W2]; omega)
  have hB : pw (Afun (t + 1) + (t + 3)) = 2 * pw (Afun (t + 1) + (t + 2)) :=
    pw_S (Afun (t + 1) + (t + 2))
  have p1 := pw_le (Afun (t + 1) + (t + 2)) (W2 - 2) (by dsimp [W2, W0]; omega)
  have p2 := pw_le h (W2 - 2) (by dsimp [W2, W0]; omega)
  have p0 := pw_pos (h - 2)
  have hK : yv t + 1 + 2 * (pw (W2 - 1) - 1 - y1e t) + 1 = pw W2 := by omega
  have hGr : pw r * (2 * G1 + 1) < pw (r + (c1 + 1)) := by rw [← ec, ← hG]; exact hhi
  have e1 : bin h G = bin (r + (c1 + 1)) (pw r * (2 * G1 + 1)) := by rw [← hG, ← ec]
  have Step : ∀ u Vl, r + (c1 + 1) + 1 ≤ u + 1 → G + 1 ≤ pw u →
      G + 1 + (pw (W2 - 1) - 1 - y1e t) = pw u + Vl → Vl < pw u →
      ReachesPlus tm (D1 (t + 1) (TL (bin h G) B0) W0) (AC (TL (bin u Vl) (U B0)) (oL W2)) := by
    intro u Vl h1' h2' h3' h4'
    rw [e1]
    exact a_E1_tail t k r c1 G1 W0 (pw (W2 - 1) - 1 - y1e t) u Vl
      hk (by dsimp [W0]; omega) hGr hK h1' (by rwa [← hG]) (by rwa [← hG]) h4'
  rcases le_or_gt (y1e t) G with hle | hlt
  · obtain ⟨p, q0, hrun, hrat⟩ := hd hle
    obtain ⟨d0, dp⟩ := ones_not_pow _ p q0 hrun (by omega)
    have p3 := pw_le h (W2 - 1 - 10) (by dsimp [W2, W0]; omega)
    exact good_back
      (Step (W2 - 1) (G - y1e t) (by dsimp [W2, W0]; omega) (by omega) (by omega) (by omega))
      (good_tailL (W2 - 1) (G - y1e t) W2
        (by dsimp [W2]; omega) d0 dp (by omega) (by dsimp [W2, W0]; omega))
  · refine good_back
      (Step (W2 - 2) (pw (W2 - 2) + G - y1e t)
        (by dsimp [W2, W0]; omega) (by omega) (by omega) (by omega)) ?_
    rcases lt_or_ge h (Afun (t + 1) - 1) with hs | hs
    · refine good_TS3 (W2 - 2) (pw (W2 - 2) + G - y1e t) W2
        (by dsimp [W2]; omega) (by omega) (by omega) (by dsimp [W2, W0]; omega) ?_
      intro r2 G2 _ hr2
      have p3 := pw_le h (Afun (t + 1) - 1) (by omega)
      have hs2 : pw ((W2 - 2) + 1) + G = pw r2 * (2 * G2 + 1) + y1e t := by
        rw [pw_S]; omega
      have hsm := TS_small (W2 - 2) r2 G2 (y1e t) (Ya (t + 1)) (Afun (t + 1) - 1) G
        rfl (by omega) (by omega) (by dsimp [W2, W0]; omega) hs2
      dsimp [W2, W0] at *; omega
    · exact good_TS2 (W2 - 2) (pw (W2 - 2) + G - y1e t) (y1e t - G)
        (Afun (t + 1) + (t + 2)) W2
        (by dsimp [W2]; omega) (by omega) (by omega) (by omega) (by omega)
        (by dsimp [W2, W0]; omega) (by dsimp [W2, W0]; omega)

/-! ## Diophantine Core Inequalities -/

private theorem pc_pos (x : ℕ) (h : x ≠ 0) : 1 ≤ pc x := by
  induction x using Nat.strongRecOn with
  | ind x ih =>
    rcases N_parity x with ⟨w, rfl⟩ | ⟨w, rfl⟩
    · rw [pc_double]; exact ih w (by omega) (by omega)
    · rw [pc_double1]; omega

private theorem pc_ge2 (W : ℕ) (h0 : W ≠ 0) (hp : ∀ x, W ≠ pw x) : 2 ≤ pc W := by
  obtain ⟨t, C, hC⟩ := N_tz W h0
  have e : pc W = pc C + 1 := by
    rw [hC]
    have hs := pc_split t 0 (2 * C + 1) (pw_pos t)
    rw [Nat.zero_add] at hs
    rw [hs, pc_0, Nat.zero_add, pc_double1]
  have hC0 : C ≠ 0 := by intro e0; subst e0; exact hp t (by rw [hC]; ring)
  have := pc_pos C hC0
  omega

private theorem pc_rhs (a b theta : ℕ) (h : theta = 0 ∨ ∃ x, theta = pw x) :
    pc (pw a + pw b + theta) ≤ 3 := by
  rcases h with rfl | ⟨x, rfl⟩
  · have := pc_two a b; simp only [Nat.add_zero]; omega
  · exact pc_three a b x

private theorem W_bounds (a3 Lam Sv W : ℕ) (h1 : Lam ≤ a3 + 1) (h2 : Sv ≠ 0) (h3 : Sv < pw a3)
    (h4 : W + pw Lam = 3 * pw a3 + Sv) :
    pw a3 < W ∧ W < 4 * pw a3 ∧ ∀ x, W ≠ pw x := by
  have p0 := pw_pos Lam
  have hL : (pw Lam = 2 * pw a3 ∧ W = pw a3 + Sv) ∨
      (pw Lam = pw a3 ∧ W = 2 * pw a3 + Sv) ∨
      (2 * pw Lam ≤ pw a3 ∧ 2 * pw a3 < W) := by
    rcases lt_trichotomy Lam a3 with e | rfl | e
    · have hlt := pw_lt Lam a3 e
      exact Or.inr (Or.inr ⟨hlt, by omega⟩)
    · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
    · have e2 : Lam = a3 + 1 := by omega
      subst e2; rw [pw_S] at *; exact Or.inl ⟨rfl, by omega⟩
  refine ⟨by omega, by omega, ?_⟩
  intro x e
  rcases lt_or_ge a3 x with hx | hx
  · by_cases hx2 : x = a3 + 1
    · subst hx2; rw [pw_S] at e; omega
    · have P := pw_le (a3 + 2) x (by omega)
      rw [pw_add_r2] at P; omega
  · have := pw_le x a3 hx; omega

private theorem top_le (Lp Lam f a1 a2 a3 a4 Xl theta : ℕ)
    (hE : pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta)
    (h1 : Xl < pw f) (h2 : f ≤ Lam) (h3 : a1 < a3) (h4 : a3 + 3 ≤ a4) :
    a4 ≤ Lp + 1 := by
  by_contra hgt
  have p1 := pw_lt (Lp + 1) a4 (by omega)
  have p2 := pw_le (a3 + 3) a4 h4
  have hp3 : pw (a3 + 3) = 8 * pw a3 := by rw [pw_add]; change pw a3 * 8 = 8 * pw a3; ring
  rw [hp3] at p2
  have p3 := pw_lt a1 a3 h3
  have p4 := pw_le f Lam h2
  omega

private theorem lam_le (Lam Lp f a a1 a2 a3 a4 Xl theta : ℕ)
    (hE : pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (h1 : Lam + 3 ≤ Lp + 1) (h2 : Xl < pw f) (h3 : Lam = f + a)
    (h4 : 26 ≤ a) (h5 : a1 < a3) :
    Lam ≤ a3 + 1 := by
  by_contra hgt
  have p3 := pw_lt a1 a3 h5
  have p2 := pw_le (a3 + 2) Lam (by omega)
  rw [pw_add_r2] at p2
  have p4 := pw_le (f + 4) Lam (by omega)
  have hp4 : pw (f + 4) = 16 * pw f := by rw [pw_add]; change pw f * 16 = 16 * pw f; ring
  rw [hp4] at p4
  have p5 := pw_pos a1
  set inner := Xl + 3 * pw a3 + pw a1
  have hin : inner < pw Lam := by dsimp [inner]; omega
  have s1 := pw_split Lam (Lp + 1) (by omega)
  have p6 := pw_pos (Lp + 1 - Lam)
  set w := pw (Lp + 1 - Lam) - 1
  have ew : pw (Lp + 1 - Lam) = w + 1 := by dsimp [w]; omega
  rw [ew, Nat.mul_add, Nat.mul_one] at s1
  have e2 : inner + pw Lam * w = pw a4 + pw a2 + theta := by dsimp [inner]; omega
  have PC := pc_split Lam inner w hin
  rw [e2, pc_ones_n] at PC
  have PR := pc_rhs a4 a2 theta hth
  have PP := pc_pos inner (by dsimp [inner]; omega)
  omega

/-! ## Low-Exponent Exclusion Cases -/

private theorem shape_C (Lp a2 a3 a4 W theta : ℕ)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (hE : pw (Lp + 1) + W = pw a4 + pw a2 + theta)
    (h1 : a3 + 2 ≤ a2) (h2 : a3 + 2 ≤ a4) (h3 : a3 + 2 ≤ Lp + 1)
    (h0 : W ≠ 0) (h4 : W < 4 * pw a3) (hnp : ∀ x, W ≠ pw x) : False := by
  have M := pw_add_r2 a3
  have s1 := pw_split _ _ h1
  have s2 := pw_split _ _ h2
  have s3 := pw_split _ _ h3
  rw [s1, s2, s3] at hE
  rw [← M] at h4
  have p9 := pw_pos (a3 + 2)
  rcases hth with rfl | ⟨x, rfl⟩
  · have e2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W =
        (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2))) * pw (a3 + 2) + 0 := by linarith
    obtain ⟨_, e3⟩ := mod_uniq (pw (a3 + 2)) _ _ W 0 h4 p9 e2
    exact h0 e3
  · rcases lt_or_ge x (a3 + 2) with hx | hx
    · have P := pw_lt x (a3 + 2) hx
      have P0 := pw_pos x
      have e2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W =
          (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2))) * pw (a3 + 2) + pw x := by linarith
      obtain ⟨_, e3⟩ := mod_uniq (pw (a3 + 2)) _ _ W (pw x) h4 (by omega) e2
      exact hnp x e3
    · have s4 := pw_split (a3 + 2) x hx
      have e2 : pw (Lp + 1 - (a3 + 2)) * pw (a3 + 2) + W =
          (pw (a4 - (a3 + 2)) + pw (a2 - (a3 + 2)) + pw (x - (a3 + 2))) * pw (a3 + 2) + 0 := by
        rw [s4] at hE; linarith
      obtain ⟨_, e3⟩ := mod_uniq (pw (a3 + 2)) _ _ W 0 h4 p9 e2
      exact h0 e3

private theorem a4_eq (Lp a2 a3 a4 W theta : ℕ)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (hE : pw (Lp + 1) + W = pw a4 + pw a2 + theta)
    (h1 : a4 ≤ Lp + 1) (h2 : a3 + 3 ≤ a4) (h3 : a2 ≤ a3 + 1)
    (_h0 : W ≠ 0) (h4 : W < 4 * pw a3) (hnp : ∀ x, W ≠ pw x) :
    a4 = Lp + 1 := by
  by_contra hne
  have eL : pw (Lp + 1) = 2 * pw Lp := pw_S Lp
  have p1 := pw_le (a3 + 3) Lp (by omega)
  have hp3 : pw (a3 + 3) = 8 * pw a3 := by rw [pw_add]; change pw a3 * 8 = 8 * pw a3; ring
  rw [hp3] at p1
  have p2 := pw_le a4 Lp (by omega)
  have p3 := pw_le a2 (a3 + 1) h3
  have eA : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  have p4 := pw_le (a3 + 3) a4 h2
  rw [hp3] at p4
  rcases hth with rfl | ⟨x, rfl⟩
  · omega
  · rcases lt_trichotomy x Lp with hx | rfl | hx
    · have := pw_lt x Lp hx; omega
    · by_cases ha4 : a4 = x
      · subst ha4; exact hnp a2 (by omega)
      · have := pw_lt a4 x (by omega); omega
    · by_cases hx2 : x = Lp + 1
      · subst hx2; omega
      · have p5 := pw_le (Lp + 2) x (by omega)
        rw [pw_add_r2] at p5; omega

private theorem low_case (Lam a1 a2 a3 f x Xl W : ℕ)
    (h1 : Lam < a3) (h2 : Xl ≠ 0) (h3 : Xl < pw f) (h4 : f + 4 ≤ Lam)
    (h5 : W + pw Lam = 3 * pw a3 + (Xl + pw a1))
    (h6 : W = pw a2 + pw x) (h7 : a2 ≤ a3 + 1) (_h8 : Xl + pw a1 < pw a3) : False := by
  have p1 := pw_lt Lam a3 h1
  have e2 : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  have hc : ∃ c, W = 2 * pw a3 + pw c := by
    rcases le_or_gt (a3 + 2) x with hx | hx
    · exfalso; have P := pw_le (a3 + 2) x hx; rw [pw_add_r2] at P; omega
    · by_cases ha2 : a2 = a3 + 1
      · subst ha2; exact ⟨x, by omega⟩
      · by_cases hx1 : x = a3 + 1
        · subst hx1; exact ⟨a2, by omega⟩
        · exfalso
          have := pw_le a2 a3 (by omega)
          have := pw_le x a3 (by omega)
          omega
  obtain ⟨c, ec⟩ := hc
  have ec3 : c = a3 := by
    rcases lt_trichotomy c a3 with hx | hx | hx
    · exfalso; have := pw_lt c a3 hx; omega
    · exact hx
    · exfalso; have := pw_lt a3 c hx; omega
  subst ec3
  have e3 : Xl + pw a1 = pw Lam := by omega
  have hx := pw_lt_inv a1 Lam (by omega)
  have p2 := pw_lt a1 Lam hx
  have p3 := pw_le (f + 4) Lam h4
  have hp4 : pw (f + 4) = 16 * pw f := by rw [pw_add]; change pw f * 16 = 16 * pw f; ring
  rw [hp4] at p3
  omega

private theorem eq_case (a2 a3 x Sv W : ℕ)
    (h1 : W = 2 * pw a3 + Sv) (h2 : W = pw a2 + pw x) (h3 : a2 ≤ a3 + 1)
    (h4 : Sv ≠ 0) (h5 : Sv < pw a3) :
    ∃ b, Sv = pw b ∧ (b = a2 ∨ a2 = a3 + 1) := by
  have e2 : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  by_cases ha2 : a2 = a3 + 1
  · subst ha2; exact ⟨x, by omega, Or.inr rfl⟩
  · rcases le_or_gt (a3 + 2) x with hx | hx
    · exfalso; have P := pw_le (a3 + 2) x hx; rw [pw_add_r2] at P; omega
    · by_cases hx1 : x = a3 + 1
      · subst hx1; exact ⟨a2, by omega, Or.inl rfl⟩
      · exfalso
        have := pw_le a2 a3 (by omega)
        have := pw_le x a3 (by omega)
        omega

private theorem eq1_case (a2 a3 x Sv W : ℕ)
    (h1 : W = pw a3 + Sv) (h2 : W = pw a2 + pw x) (h3 : a2 ≤ a3 + 1)
    (h4 : Sv ≠ 0) (h5 : Sv < pw a3) :
    ∃ b, Sv = pw b ∧ (b = a2 ∨ a2 = a3) := by
  have e2 : pw (a3 + 1) = 2 * pw a3 := pw_S a3
  have a1' : a2 ≤ a3 := by
    by_cases ha : a2 = a3 + 1
    · subst ha; omega
    · omega
  have a2' : x ≤ a3 := by
    by_contra hgt
    have := pw_le (a3 + 1) x (by omega); omega
  by_cases ha : a2 = a3
  · subst ha; exact ⟨x, by omega, Or.inr rfl⟩
  · by_cases hb : x = a3
    · subst hb; exact ⟨a2, by omega, Or.inl rfl⟩
    · exfalso
      have := pw_lt a2 a3 (by omega)
      have := pw_lt x a3 (by omega)
      omega

/-! ## Diophantine Core Classification -/

private theorem S_small (Lam f a a1 a3 Xl : ℕ)
    (h1 : Lam ≤ a3 + 1) (h2 : Lam = f + a) (h3 : 26 ≤ a) (h4 : a1 < a3) (h5 : Xl < pw f) :
    Xl + pw a1 < pw a3 := by
  have p1 := pw_lt a1 a3 h4
  have p2 := pw_le (f + 2) a3 (by omega)
  rw [pw_add_r2] at p2
  omega

private theorem core_even (Lp Lam f a a1 a2 a3 a4 Xl theta : ℕ)
    (hE : pw (Lp + 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (h1 : Lam + 3 ≤ Lp + 1) (h2 : Xl < pw f) (h3 : Lam = f + a)
    (h4 : 26 ≤ a) (h5 : a1 < a3) (h6 : a3 + 3 ≤ a4) (h7 : Xl ≠ 0) :
    a4 = Lp + 1 ∧ (Lam = a3 + 1 ∨ Lam = a3) ∧
      ∃ b, Xl + pw a1 = pw b ∧ (b = a2 ∨ a2 = a3 ∨ a2 = a3 + 1) := by
  have ht := top_le Lp Lam f a1 a2 a3 a4 Xl theta hE h2 (by omega) h5 h6
  have hl := lam_le Lam Lp f a a1 a2 a3 a4 Xl theta hE hth h1 h2 h3 h4 h5
  have hS := S_small Lam f a a1 a3 Xl hl h3 h4 h5 h2
  have pL := pw_le Lam (a3 + 1) hl
  rw [pw_S] at pL
  have p0 := pw_pos a1
  set Sv := Xl + pw a1
  set W := 3 * pw a3 + Sv - pw Lam
  have hW : W + pw Lam = 3 * pw a3 + Sv := by dsimp [W]; omega
  have sv0 : Sv ≠ 0 := by dsimp [Sv]; omega
  obtain ⟨w1, w2, wnp⟩ := W_bounds a3 Lam Sv W hl sv0 hS hW
  have e3 : pw (Lp + 1) + W = pw a4 + pw a2 + theta := by dsimp [Sv] at *; omega
  rcases le_or_gt (a3 + 2) a2 with sh | sh
  · exfalso; exact shape_C Lp a2 a3 a4 W theta hth e3 sh (by omega) (by omega) (by omega) w2 wnp
  have ea := a4_eq Lp a2 a3 a4 W theta hth e3 ht h6 (by omega) (by omega) w2 wnp
  refine ⟨ea, ?_⟩
  rw [ea] at e3
  have e4 : W = pw a2 + theta := by omega
  rcases hth with rfl | ⟨x, rfl⟩
  · exfalso; exact wnp a2 (by omega)
  rcases lt_trichotomy Lam a3 with hx | hx | hx
  · exfalso; exact low_case Lam a1 a2 a3 f x Xl W hx h7 h2 (by omega) hW e4 (by omega) hS
  · refine ⟨Or.inr hx, ?_⟩
    obtain ⟨b, eb, hb⟩ := eq_case a2 a3 x Sv W (by rw [hx] at hW; omega) e4 (by omega) sv0 hS
    exact ⟨b, eb, by omega⟩
  · have e5 : Lam = a3 + 1 := by omega
    subst e5
    refine ⟨Or.inl rfl, ?_⟩
    obtain ⟨b, eb, hb⟩ := eq1_case a2 a3 x Sv W (by rw [pw_S] at hW; omega) e4 (by omega) sv0 hS
    exact ⟨b, eb, by omega⟩

private theorem core_odd (Lp Lam f a a1 a2 a3 a4 Xl theta : ℕ)
    (hE : pw Lp + pw (Lp - 1) + Xl + 3 * pw a3 + pw a1 = pw a4 + pw a2 + pw Lam + theta)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (h1 : Lam + 3 ≤ Lp - 1) (h2 : Xl < pw f) (h3 : Lam = f + a)
    (h4 : 26 ≤ a) (h5 : a1 < a3) (h6 : a3 + 3 ≤ a4)
    (hcoll : a4 = a3 + 3 → a2 ≤ a3 → a3 < 28) : False := by
  have eL : pw Lp = 2 * pw (Lp - 1) := pw_pred2 Lp (by omega)
  have p1 := pw_lt a1 a3 h5
  have p2 := pw_le (a3 + 3) a4 h6
  have hp3 : pw (a3 + 3) = 8 * pw a3 := by rw [pw_add]; change pw a3 * 8 = 8 * pw a3; ring
  rw [hp3] at p2
  have p3 := pw_le f Lam (by omega)
  have p0 := pw_pos a1
  have ht : a4 ≤ Lp + 1 := by
    by_contra hgt
    have p4 := pw_le (Lp + 2) a4 (by omega)
    rw [pw_add_r2] at p4; omega
  have hl : Lam ≤ a3 + 1 := by
    by_contra hgt
    have p4 := pw_le (a3 + 2) Lam (by omega)
    rw [pw_add_r2] at p4
    have p5 := pw_le (f + 4) Lam (by omega)
    have hp4 : pw (f + 4) = 16 * pw f := by rw [pw_add]; change pw f * 16 = 16 * pw f; ring
    rw [hp4] at p5
    set inner := Xl + 3 * pw a3 + pw a1
    have hin : inner < pw Lam := by dsimp [inner]; omega
    have s1 := pw_split Lam (Lp - 1) (by omega)
    have p6 := pw_pos (Lp - 1 - Lam)
    set w := pw (Lp - 1 - Lam) - 1
    have ew : pw (Lp - 1 - Lam) = w + 1 := by dsimp [w]; omega
    rw [ew, Nat.mul_add, Nat.mul_one] at s1
    have hx0 : inner + pw Lam * w < pw Lp := by omega
    have e2 : (inner + pw Lam * w) + pw Lp * 1 = pw a4 + pw a2 + theta := by dsimp [inner]; omega
    have PC1 := pc_split Lam inner w hin
    have PC2 := pc_split Lp (inner + pw Lam * w) 1 hx0
    have hpc1 : pc 1 = 1 := pc_1
    rw [e2, PC1, pc_ones_n, hpc1] at PC2
    have PR := pc_rhs a4 a2 theta hth
    have PP := pc_pos inner (by dsimp [inner]; omega)
    omega
  have hS := S_small Lam f a a1 a3 Xl hl h3 h4 h5 h2
  have pL := pw_le Lam (a3 + 1) hl
  rw [pw_S] at pL
  set Sv := Xl + pw a1
  set W := 3 * pw a3 + Sv - pw Lam
  have hW : W + pw Lam = 3 * pw a3 + Sv := by dsimp [W]; omega
  have sv0 : Sv ≠ 0 := by dsimp [Sv]; omega
  obtain ⟨w1, w2, wnp⟩ := W_bounds a3 Lam Sv W hl sv0 hS hW
  have e3 : pw Lp + pw (Lp - 1) + W = pw a4 + pw a2 + theta := by dsimp [Sv] at *; omega
  rcases le_or_gt (a3 + 2) (Lp - 1) with hc | hc
  · have p4 := pw_le (a3 + 2) (Lp - 1) hc
    rw [pw_add_r2] at p4
    have e5 : W + pw (Lp - 1) * 3 = pw a4 + pw a2 + theta := by omega
    have PC := pc_split (Lp - 1) W 3 (by omega)
    have hpc3 : pc 3 = 2 := pc_3
    rw [e5, hpc3] at PC
    have PR := pc_rhs a4 a2 theta hth
    have PG := pc_ge2 W (by omega) wnp
    omega
  · have e6 : Lp = a3 + 2 := by omega
    subst e6
    have e7 : a4 = a3 + 3 := by omega
    subst e7
    have hsub : a3 + 2 - 1 = a3 + 1 := by omega
    rw [hsub] at e3
    rw [pw_add_r2, pw_S] at e3
    have ha2 : pw a2 < pw (a3 + 1) := by rw [pw_S]; omega
    have ha3 := pw_lt_inv a2 (a3 + 1) ha2
    have hcoll' := hcoll rfl (by omega)
    omega

/-! ## Exponent Size Exclusions -/

private theorem y1o_add (t r : ℕ) :
    y1o t r + 3 * pw (Apr r + Afun (t + 1)) + pw (Apr r - 1) =
      pw (Apr r + Afun (t + 1) + (t + 3)) + pw (Apr r + r + 1) := by
  rw [y1o_split, Yc_exact]
  unfold Ya
  have heq : (t + 1) + 2 = t + 3 := rfl
  rw [heq, pw_add (Apr r + Afun (t + 1)) (t + 3)]
  have ha := Apr_pos r
  have P := pw_lt (Apr r - 1) (Apr r + r + 1) (by omega)
  have p0 := pw_pos (Apr r - 1)
  have pt : 3 ≤ pw (t + 3) := by
    have : t + 3 = (t + 1) + 2 := rfl
    rw [this, pw_add_r2]; have := pw_pos (t + 1); omega
  have hsub : pw (Apr r - 1) ≤ pw (Apr r + r + 1) := by omega
  zify [pt, hsub]
  ring

private theorem split_Z (Z t C q C1 un p0 v f : ℕ)
    (hZ : Z = pw t * (2 * C + 1)) (hC : C = pw q * (2 * C1 + 1))
    (hE : Z + pw p0 = pw un + v)
    (h0 : v ≠ 0) (hv : v < pw f) (hnp : ∀ x, v ≠ pw x)
    (h1 : f ≤ p0) (h2 : p0 ≤ un) :
    t + q + 2 ≤ f ∧
      ∃ Xl, v = pw t + pw (t + (q + 1)) + pw ((t + (q + 1)) + 1) * Xl ∧
        C1 + pw (p0 - ((t + (q + 1)) + 1)) = pw (un - ((t + (q + 1)) + 1)) + Xl ∧
        Xl < pw (f - ((t + (q + 1)) + 1)) := by
  have s1 := pw_split f un (le_trans h1 h2)
  have s2 := pw_split f p0 h1
  have p1 := pw_le (p0 - f) (un - f) (by omega)
  have ht : t + q + 2 ≤ f := by
    apply second_bit (pw (un - f) - pw (p0 - f)) v f t C q C1 h0 hv hnp _ hC
    rw [Nat.sub_mul, ← hZ]
    have p2 : pw (p0 - f) * pw f ≤ pw (un - f) * pw f := Nat.mul_le_mul_right _ p1
    rw [s1, s2, Nat.mul_comm (pw f) (pw (un - f)), Nat.mul_comm (pw f) (pw (p0 - f))] at hE
    omega
  refine ⟨ht, ?_⟩
  set p2 := t + (q + 1)
  have hZ2 : Z = pw t + pw p2 + 2 * pw p2 * C1 := by
    rw [hZ, hC]; dsimp [p2]; rw [pw_add t (q + 1), pw_S]; ring
  have M : pw (p2 + 1) = 2 * pw p2 := pw_S p2
  have p3 := pw_lt t p2 (by dsimp [p2]; omega)
  have p4 := pw_pos t
  have M0 : 0 < pw (p2 + 1) := pw_pos (p2 + 1)
  set Xl := v / pw (p2 + 1)
  set rr := v % pw (p2 + 1)
  have dv : pw (p2 + 1) * Xl + rr = v := Nat.div_add_mod v (pw (p2 + 1))
  have mv : rr < pw (p2 + 1) := Nat.mod_lt v M0
  have s3 := pw_split (p2 + 1) un (by dsimp [p2]; omega)
  have s4 := pw_split (p2 + 1) p0 (by dsimp [p2]; omega)
  have e2 : (C1 + pw (p0 - (p2 + 1))) * pw (p2 + 1) + (pw t + pw p2) =
      (pw (un - (p2 + 1)) + Xl) * pw (p2 + 1) + rr := by
    rw [s3, s4, hZ2, ← dv] at hE
    have lhs_eq : (C1 + pw (p0 - (p2 + 1))) * pw (p2 + 1) + (pw t + pw p2) =
        pw t + pw p2 + 2 * pw p2 * C1 + pw (p2 + 1) * pw (p0 - (p2 + 1)) := by rw [M]; ring
    have rhs_eq : (pw (un - (p2 + 1)) + Xl) * pw (p2 + 1) + rr =
        pw (p2 + 1) * pw (un - (p2 + 1)) + (pw (p2 + 1) * Xl + rr) := by ring
    rw [lhs_eq, rhs_eq, hE]
  obtain ⟨e3, e4⟩ := mod_uniq (pw (p2 + 1)) (C1 + pw (p0 - (p2 + 1))) (pw (un - (p2 + 1)) + Xl)
    (pw t + pw p2) rr (by omega) mv e2
  refine ⟨Xl, by linarith, e3, ?_⟩
  by_contra hge
  have s5 := pw_split (p2 + 1) f (by dsimp [p2]; omega)
  have p5 : pw (p2 + 1) * pw (f - (p2 + 1)) ≤ pw (p2 + 1) * Xl :=
    Nat.mul_le_mul_left _ (by omega)
  omega

private theorem v_np (v U0 : ℕ) (h1 : 5 * pw U0 < 2 * v) (h2 : 2 * v < 7 * pw U0) (x : ℕ) :
    v ≠ pw x := by
  intro rfl
  rcases le_or_gt x (U0 + 1) with hx | hx
  · by_cases hx2 : x = U0 + 1
    · subst hx2; rw [pw_S] at *; omega
    · have := pw_le x U0 (by omega); omega
  · have P := pw_le (U0 + 2) x hx; rw [pw_add_r2] at P; omega

private theorem Xl_ne (v U0 t' p2 R j Xl : ℕ)
    (h1 : 5 * pw U0 < 2 * v) (h2 : 2 * v < 7 * pw U0)
    (hv : v = pw t' + pw p2 + pw (p2 + 1) * Xl)
    (hp : p2 = t' + (R + 1)) (hR : R = 2 * j + 1) : Xl ≠ 0 := by
  intro rfl
  rw [Nat.mul_zero, Nat.add_zero] at hv
  have p1 := pw_lt t' p2 (by omega)
  have p0 := pw_pos t'
  have ep : p2 = U0 + 1 := by
    rcases lt_trichotomy p2 (U0 + 1) with hx | hx | hx
    · exfalso; have := pw_le p2 U0 (by omega); omega
    · exact hx
    · exfalso; have P := pw_le (U0 + 2) p2 hx; rw [pw_add_r2] at P; omega
  rw [ep, pw_S] at hv
  have et : t' = U0 := by
    rcases lt_trichotomy t' U0 with hx | hx | hx
    · exfalso; have := pw_lt t' U0 hx; omega
    · exact hx
    · omega
  omega

private theorem block (v U0 t' p2 Xl a1 b : ℕ)
    (h1 : 5 * pw U0 < 2 * v) (h2 : 2 * v < 7 * pw U0)
    (hv : v = pw t' + pw p2 + pw (p2 + 1) * Xl)
    (ht : t' < p2) (h0 : Xl ≠ 0) (eb : Xl + pw a1 = pw b) :
    a1 < b ∧ b ≤ a1 + 2 ∧ p2 + b = U0 + 1 := by
  have hab : a1 < b := pw_lt_inv a1 b (by omega)
  have p1 := pw_lt t' p2 ht
  have p0 := pw_pos t'
  have M : pw (p2 + 1) = 2 * pw p2 := pw_S p2
  have eMb : pw (p2 + 1) * Xl + pw ((p2 + 1) + a1) = pw ((p2 + 1) + b) := by
    rw [pw_add (p2 + 1) a1, pw_add (p2 + 1) b, ← eb]; ring
  have p2' := pw_lt ((p2 + 1) + a1) ((p2 + 1) + b) (by omega)
  have p3 := pw_le (p2 + 1) ((p2 + 1) + a1) (by omega)
  have hs : (p2 + 1) + b = U0 + 2 := by
    rcases lt_trichotomy ((p2 + 1) + b) (U0 + 2) with hx | hx | hx
    · exfalso; have P := pw_le ((p2 + 1) + b) (U0 + 1) (by omega); rw [pw_S] at P; omega
    · exact hx
    · exfalso
      have P := pw_le (U0 + 3) ((p2 + 1) + b) hx
      have hp3 : pw (U0 + 3) = 8 * pw U0 := by rw [pw_add]; change pw U0 * 8 = 8 * pw U0; ring
      rw [hp3] at P; omega
  refine ⟨hab, ?_, by omega⟩
  by_contra hgt
  have p4 := pw_le (((p2 + 1) + a1) + 3) ((p2 + 1) + b) (by omega)
  have hp3 : pw (((p2 + 1) + a1) + 3) = 8 * pw ((p2 + 1) + a1) := by
    rw [pw_add]; change pw ((p2 + 1) + a1) * 8 = 8 * pw ((p2 + 1) + a1); ring
  rw [hp3, hs, pw_add_r2] at p4
  rw [hs, pw_add_r2] at eMb
  omega

private theorem sizes_even (m R r a h U0 Lam b A' Ap' A Ap : ℕ)
    (h1 : 5 * m ≤ 2 * A' ∧ 2 * A' ≤ 5 * m + 1)
    (h2 : 5 * R + 1 ≤ 2 * Ap' ∧ 2 * Ap' ≤ 5 * R + 2)
    (h3 : 5 * a ≤ 2 * A ∧ 2 * A ≤ 5 * a + 1)
    (h4 : 5 * r + 1 ≤ 2 * Ap ∧ 2 * Ap ≤ 5 * r + 2)
    (h5 : U0 = Ap + A)
    (h6 : Ap' + A' + (m + 2) + (m + R) = U0 + a + h + 1)
    (h7 : Lam + (m + R) + 1 = U0 + a + 2)
    (_h8 : Lam = Ap' + A' + 1 ∨ Lam = Ap' + A')
    (h9 : m + R + b = U0 + 1)
    (h10 : Ap' - 1 < b) (h11 : b ≤ Ap' - 1 + 2) (h12 : 1 ≤ Ap')
    (h13 : R + 1 = A' ∨ R = A') (h14 : r + 3 ≤ h) (h15 : 26 ≤ a) : False := by
  omega

/-! ## Exclusion of Degenerate Overflow Collisions -/

private theorem v_bounds (t r G1 v : ℕ)
    (h1 : v + pw (Apr r + r + 1) = G1 + 3 * pw (Apr r + Afun (t + 1)) + pw (Apr r - 1))
    (h2 : 2 * G1 < pw (Apr r + Afun (t + 1))) (h3 : r + 2 ≤ Afun (t + 1)) :
    5 * pw (Apr r + Afun (t + 1)) < 2 * v ∧ 2 * v < 7 * pw (Apr r + Afun (t + 1)) := by
  have p1 := pw_lt (Apr r + r + 1) (Apr r + Afun (t + 1)) (by omega)
  have p2 := pw_le (Apr r - 1) (Apr r + r + 1) (by omega)
  have p3 := pw_pos (Apr r - 1)
  omega

private theorem low_setup (t r G1 Z un : ℕ)
    (hZ : Z + y1o t r = pw un + G1)
    (h1 : 2 * G1 < pw (Apr r + Afun (t + 1)))
    (h2 : r ≤ t + 1) (h3 : 26 ≤ t + 1) :
    ∃ v, Z + pw (Apr r + Afun (t + 1) + (t + 3)) = pw un + v ∧
      v ≠ 0 ∧ v < pw (Apr r + Afun (t + 1) + 2) ∧
      5 * pw (Apr r + Afun (t + 1)) < 2 * v ∧ 2 * v < 7 * pw (Apr r + Afun (t + 1)) ∧
      (∀ x, v ≠ pw x) := by
  have bA := Afun_bd (t + 1)
  have p1 := pw_lt (Apr r + r + 1) (Apr r + Afun (t + 1)) (by omega)
  have Y := y1o_add t r
  set v := G1 + 3 * pw (Apr r + Afun (t + 1)) + pw (Apr r - 1) - pw (Apr r + r + 1)
  have hv : v + pw (Apr r + r + 1) = G1 + 3 * pw (Apr r + Afun (t + 1)) + pw (Apr r - 1) := by
    dsimp [v]; omega
  obtain ⟨b1, b2⟩ := v_bounds t r G1 v hv h1 (by omega)
  have p2 := pw_add_r2 (Apr r + Afun (t + 1))
  exact ⟨v, by omega, by omega, by omega, b1, b2, v_np v _ b1 b2⟩

private theorem short_B (t r G1 h t' C' q C1' c1' j Z theta u : ℕ)
    (hZ : Z = pw t' * (2 * C' + 1)) (hC : C' = pw q * (2 * C1' + 1))
    (hq : q = 2 * j + 1) (hu1 : u = t' + ((q + (c1' + 1)) + 1))
    (hu2 : u = Apr r + Afun (t + 1) + (t + 1) + h + 1)
    (hE : Z + y1o t r = pw u + G1)
    (h1 : 2 * G1 < pw (Apr r + Afun (t + 1)))
    (h2 : r + 3 ≤ h) (h3 : r ≤ t + 1) (h4 : 26 ≤ t + 1)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (hX : C1' + pw c1' = y1o t' q + theta) : False := by
  obtain ⟨v, hZv, v0, vf, b1, b2, vn⟩ := low_setup t r G1 Z u hE h1 h3 h4
  obtain ⟨ht, Xl, hv, hC1, hXl⟩ :=
    split_Z Z t' C' q C1' u _ v _ hZ hC hZv v0 vf vn (by omega) (by omega)
  have xn := Xl_ne v _ t' (t' + (q + 1)) q j Xl b1 b2 hv rfl hq
  have Y := y1o_add t' q
  have p1 : pw (c1' + 1) = 2 * pw c1' := pw_S c1'
  have hsub : u - ((t' + (q + 1)) + 1) = c1' := by omega
  rw [hsub] at hC1
  set Lam := Apr r + Afun (t + 1) + (t + 3) - ((t' + (q + 1)) + 1)
  have hE2 : pw (c1' + 1) + Xl + 3 * pw (Apr q + Afun (t' + 1)) + pw (Apr q - 1) =
      pw (Apr q + Afun (t' + 1) + (t' + 3)) + pw (Apr q + q + 1) + pw Lam + theta := by
    omega
  have pq := Apr_pos q
  have pa := Afun_pos t'
  obtain ⟨ea, hlam, b, eb, hb⟩ :=
    core_even c1' Lam (Apr r + Afun (t + 1) + 2 - ((t' + (q + 1)) + 1)) (t + 1)
      (Apr q - 1) (Apr q + q + 1) (Apr q + Afun (t' + 1)) (Apr q + Afun (t' + 1) + (t' + 3))
      Xl theta hE2 hth (by dsimp [Lam]; omega) hXl
      (by dsimp [Lam]; omega) h4 (by omega) (by omega) xn
  obtain ⟨bb, bc, bd⟩ := block v _ t' (t' + (q + 1)) Xl (Apr q - 1) b b1 b2 hv (by omega) xn eb
  rcases hb with hb | hb
  · omega
  · exact sizes_even (t' + 1) q r (t + 1) h (Apr r + Afun (t + 1)) Lam b
      (Afun (t' + 1)) (Apr q) (Afun (t + 1)) (Apr r)
      (Afun_bd _) (Apr_bd _) (Afun_bd _) (Apr_bd _) rfl
      (by omega) (by dsimp [Lam]; omega) hlam (by omega) bb bc pq (by omega) h2 h4

private theorem hcoll (t' j : ℕ)
    (h1 : Apr (2 * j + 1) + Afun (t' + 1) + (t' + 3) = Apr (2 * j + 1) + Afun (t' + 1) + 3)
    (h2 : Apr (2 * j + 1) + (2 * j + 1) + 1 ≤ Apr (2 * j + 1) + Afun (t' + 1)) :
    Apr (2 * j + 1) + Afun (t' + 1) < 28 := by
  have et : t' = 0 := by omega
  subst et
  have ha1 : Afun 1 = 3 := rfl
  rw [ha1] at h2 ⊢
  have ej : j = 0 := by omega
  subst ej
  decide

private theorem short_C (t r G1 h t' C' q C1' c1' j Z theta u : ℕ)
    (hZ : Z = pw t' * (2 * C' + 1)) (hC : C' = pw q * (2 * C1' + 1))
    (hq : q = 2 * j + 1) (hu1 : u = t' + ((q + (c1' + 1)) + 1))
    (hu2 : u = Apr r + Afun (t + 1) + (t + 1) + h + 3)
    (hE : Z + y1o t r = pw (u - 1) + G1)
    (h1 : 2 * G1 < pw (Apr r + Afun (t + 1)))
    (h2 : r + 3 ≤ h) (h3 : r ≤ t + 1) (h4 : 26 ≤ t + 1)
    (hth : theta = 0 ∨ ∃ x, theta = pw x)
    (hX : C1' + pw c1' = y1o t' q + theta) : False := by
  obtain ⟨v, hZv, v0, vf, b1, b2, vn⟩ := low_setup t r G1 Z (u - 1) hE h1 h3 h4
  obtain ⟨ht, Xl, hv, hC1, hXl⟩ :=
    split_Z Z t' C' q C1' (u - 1) _ v _ hZ hC hZv v0 vf vn (by omega) (by omega)
  have Y := y1o_add t' q
  have hsub : u - 1 - ((t' + (q + 1)) + 1) = c1' - 1 := by omega
  rw [hsub] at hC1
  set Lam := Apr r + Afun (t + 1) + (t + 3) - ((t' + (q + 1)) + 1)
  have hE2 : pw c1' + pw (c1' - 1) + Xl + 3 * pw (Apr q + Afun (t' + 1)) + pw (Apr q - 1) =
      pw (Apr q + Afun (t' + 1) + (t' + 3)) + pw (Apr q + q + 1) + pw Lam + theta := by
    omega
  have pq := Apr_pos q
  have pa := Afun_pos t'
  subst hq
  exact core_odd c1' Lam (Apr r + Afun (t + 1) + 2 - ((t' + ((2 * j + 1) + 1)) + 1)) (t + 1)
    (Apr (2 * j + 1) - 1) (Apr (2 * j + 1) + (2 * j + 1) + 1)
    (Apr (2 * j + 1) + Afun (t' + 1)) (Apr (2 * j + 1) + Afun (t' + 1) + (t' + 3))
    Xl theta hE2 hth (by dsimp [Lam]; omega) hXl (by dsimp [Lam]; omega) h4 (by omega) (by omega)
    (hcoll t' j)

/-! ## Secondary Carry Regime Closure -/

private theorem cell_lo (V c : ℕ) (h : cell1 V c) : pw c ≤ V := by
  obtain ⟨a, b, _, h2⟩ := h; omega

private theorem ones_lt (V p q n : ℕ)
    (h1 : ones_on V p q) (h2 : V < pw n) (h3 : p < q) : q ≤ n := by
  have P := cell_lo V (q - 1) (ones_cell V p q (q - 1) h1 (by omega))
  by_contra hgt
  have := pw_le n (q - 1) (by omega)
  omega

private theorem not_LR_335 (h : LR 335) : False := by
  obtain ⟨p, q, hrun, hr⟩ := h
  rcases le_or_gt p 4 with hc | hc
  · obtain ⟨a, b, h1, h2⟩ := ones_cell 335 p q 4 hrun (by omega)
    have hp4 : pw 4 = 16 := by decide
    have hp5 : pw 5 = 32 := by decide
    rw [hp4] at h1 h2; rw [hp5] at h2; omega
  · rcases le_or_gt p 7 with hd | hd
    · obtain ⟨a, b, h1, h2⟩ := ones_cell 335 p q 7 hrun (by omega)
      have hp7 : pw 7 = 128 := by decide
      have hp8 : pw 8 = 256 := by decide
      rw [hp7] at h1 h2; rw [hp8] at h2; omega
    · have P := cell_lo 335 (p + 1) (ones_cell 335 p q (p + 1) hrun (by omega))
      have P2 := pw_le 9 (p + 1) (by omega)
      have hp9 : pw 9 = 512 := by decide
      rw [hp9] at P2; omega

private theorem pc_top (Z P0 un v : ℕ)
    (h1 : Z + pw P0 = pw un + v) (h2 : v < pw P0) (h3 : P0 ≤ un) :
    pc Z = pc v + (un - P0) := by
  have s1 := pw_split P0 un h3
  have P := pw_pos (un - P0)
  set w := pw (un - P0) - 1
  have ew : pw (un - P0) = w + 1 := by dsimp [w]; omega
  rw [ew, Nat.mul_add, Nat.mul_one] at s1
  have e : Z = v + pw P0 * w := by omega
  rw [e, pc_split P0 v w h2, pc_ones_n]

private theorem Z_form (Z P0 un v f : ℕ)
    (h1 : Z + pw P0 = pw un + v) (h2 : f ≤ P0) (h3 : P0 ≤ un) :
    Z = (pw (un - f) - pw (P0 - f)) * pw f + v := by
  have s1 := pw_split f un (le_trans h2 h3)
  have s2 := pw_split f P0 h2
  have p1 := pw_le (P0 - f) (un - f) (by omega)
  have p2 : pw (P0 - f) * pw f ≤ pw (un - f) * pw f := Nat.mul_le_mul_right _ p1
  rw [Nat.sub_mul]
  rw [s1, s2, Nat.mul_comm (pw f) (pw (un - f)), Nat.mul_comm (pw f) (pw (P0 - f))] at h1
  omega

private theorem long_Z (Z Ev p0 un : ℕ)
    (h1 : Z + Ev = pw un) (h2 : Ev ≠ 0) (h3 : Ev < pw p0) (h4 : p0 + 2 ≤ un) :
    ones_on Z p0 un ∧
      ∃ v, Z + pw (p0 + 2) = pw un + v ∧ v ≠ 0 ∧ v < pw (p0 + 2) ∧ ∀ x, v ≠ pw x := by
  have p1 := pw_le p0 un (by omega)
  have p2 := pw_add_r2 p0
  have p3 := pw_pos p0
  refine ⟨⟨by omega, 0, pw p0 - Ev, by omega, by omega⟩,
    4 * pw p0 - Ev, by omega, by omega, by omega, ?_⟩
  intro x ex
  rcases lt_trichotomy x (p0 + 1) with hx | rfl | hx
  · have := pw_le x p0 (by omega); omega
  · rw [pw_S] at ex; omega
  · have Q := pw_le (p0 + 2) x hx; rw [pw_add_r2] at Q; omega

/-! ## Even-Round Inductive Step -/

private theorem level_run (Z t' c' C' u p0 q0 h Zh v W : ℕ)
    (hZ : Z = pw t' * (2 * C' + 1)) (hC : C' < pw c') (hu : u = t' + (c' + 1))
    (hrun : ones_on Z p0 q0) (hr : 2 * p0 + 25 ≤ 5 * (q0 - p0)) (hq0 : q0 ≤ u)
    (hZv : Z = Zh * pw h + v) (v0 : v ≠ 0) (vl : v < pw h) (vn : ∀ x, v ≠ pw x)
    (hh : h + 9 ≤ u)
    (w1 : (t' + 1) + c' + 1 ≤ W) (w2 : W ≤ (t' + 1) + c' + 2) (wb : 90 ≤ W)
    (h83 : t' = 0 → W = (t' + 1) + c' + 1 → C' ≠ 167) :
    Good (D1 (t' + 1) (TL (bin c' C') (U B0)) W) := by
  have PC := pc_on Z p0 q0 hrun
  exact good_Z Z t' c' C' W Zh v h hZ hC hZv v0 vl vn (by omega) (by omega) w1 w2 (Or.inr wb) h83
    (fun _ q c1 C1 j _ hC1 hc hq =>
      N2_run Z u t' C' q C1 c1 j p0 q0 hZ hC1 hq (by omega) hrun hq0 hr)

private theorem level_low (t r G1 h Z t' c' C' u un W : ℕ)
    (hZ : Z = pw t' * (2 * C' + 1)) (hC : C' < pw c') (hu : u = t' + (c' + 1)) (hun : un ≤ u)
    (hun2 : un = Apr r + Afun (t + 1) + (t + 3) + (h - 1) ∨ un = Apr r + Afun (t + 1) + (t + 3) + h)
    (hE : Z + y1o t r = pw un + G1) (hlt : G1 < y1o t r) (hGh : G1 < pw h)
    (hr : r + 3 ≤ h) (hra : r ≤ t + 1) (ha : 26 ≤ t + 1)
    (w1 : (t' + 1) + c' + 1 ≤ W) (w2 : W ≤ (t' + 1) + c' + 2) (wb : 90 ≤ W)
    (h83 : t' = 0 → W = (t' + 1) + c' + 1 → C' ≠ 167)
    (hshort : 2 * G1 < pw (Apr r + Afun (t + 1)) →
      ∀ q C1 c1 j theta, C' = pw q * (2 * C1 + 1) → c' = q + (c1 + 1) →
        q = 2 * j + 1 → (theta = 0 ∨ ∃ x, theta = pw x) → C1 + pw c1 = y1o t' q + theta → False) :
    Good (D1 (t' + 1) (TL (bin c' C') (U B0)) W) := by
  have bA := Afun_bd (t + 1)
  set U0 := Apr r + Afun (t + 1)
  set p0 := U0 + (t + 3)
  rcases lt_or_ge (2 * G1) (pw U0) with sh | lg
  · obtain ⟨v, hZv, v0, vf, _, _, vn⟩ := low_setup t r G1 Z un hE sh hra ha
    have hZf := Z_form Z p0 un v (U0 + 2) hZv (by dsimp [p0]; omega) (by dsimp [p0, U0] at *; omega)
    have p1 := pw_le (U0 + 2) p0 (by dsimp [p0]; omega)
    have PC := pc_top Z p0 un v hZv (lt_of_lt_of_le vf p1) (by dsimp [p0, U0] at *; omega)
    have PV := pc_pos v v0
    exact good_Z Z t' c' C' W _ v (U0 + 2) hZ hC hZf v0 vf vn
      (by dsimp [U0, p0] at *; omega) (by dsimp [U0, p0] at *; omega) w1 w2 (Or.inr wb) h83
      (fun _ q c1 C1 j _ hC1 hc hq =>
        ⟨fun e => hshort sh q C1 c1 j 0 hC1 hc hq (Or.inl rfl) (by omega),
         fun x e => hshort sh q C1 c1 j (pw x) hC1 hc hq (Or.inr ⟨x, rfl⟩) e⟩)
  · have hh : U0 ≤ h := by
      by_contra hgt
      have := pw_lt h U0 (by omega); omega
    have y4 := y1o_lt4 t r (by omega)
    have pa := Apr_pos r
    obtain ⟨hrun, v, hZv, v0, vf, vn⟩ :=
      long_Z Z (y1o t r - G1) p0 un (by omega) (by omega) (by dsimp [p0, U0] at *; omega)
        (by dsimp [p0, U0] at *; omega)
    have hZf := Z_form Z (p0 + 2) un v (p0 + 2) hZv (le_refl _) (by dsimp [p0, U0] at *; omega)
    exact level_run Z t' c' C' u p0 un (p0 + 2) _ v W hZ hC hu hrun
      (by dsimp [p0, U0] at *; omega) hun hZf v0 vf vn (by dsimp [p0, U0] at *; omega)
      w1 w2 wb h83

/-! ## Odd-Round Inductive Steps and Full Invariant Step -/

private theorem step_odd_even (t k h G j G1 : ℕ)
    (hk : t + 1 = 2 * k + 1) (ha : 26 ≤ t + 1)
    (hlo : pw (h - 2) ≤ G) (hhi : G < pw h)
    (hG : G = pw (2 * j) * (2 * G1 + 1))
    (hr : 2 * j + 3 ≤ h) (hra : 2 * j ≤ t + 1)
    (hd : y1o t (2 * j) ≤ G1 → LR (G1 - y1o t (2 * j))) :
    Good (F0 (t + 1) h (pw h - 1 - G)) := by
  refine good_back (F0_D1 t h G (pw h - 1 - G) (by omega)) ?_
  have g0 := G1_ne (2 * j) G1 h (by linarith) hr
  obtain ⟨L, eL, hL⟩ := tz_bound h (2 * j) G1 (by linarith)
  obtain ⟨r2, C2, hG1⟩ := N_tz G1 g0
  obtain ⟨c2, eL2, hc2⟩ := tz_bound L r2 C2 (by linarith)
  have bA := Afun_bd (t + 1)
  have pa := Apr_pos (2 * j)
  set W0 := t + (h + 1) + 1
  set W2 := Apr (2 * j) + (Afun (t + 1) + (W0 + 1) + 1) - 1
  have eW2 : Apr (2 * j) + (Afun (t + 1) + (W0 + 1) + 1) = W2 + 1 := by dsimp [W2]; omega
  have wv : W2 = Apr (2 * j) + Afun (t + 1) + (t + 1) + h + 2 := by dsimp [W2, W0]; omega
  have hZv := zv_lt2 t (2 * j) W0 (by dsimp [W0]; omega) (by dsimp [W0]; omega)
  have y4 := y1o_lt4 t (2 * j) (by omega)
  have hy2 := y2v_y1o t (2 * j)
  have p1 : pw W2 = 2 * pw (W2 - 1) := pw_pred2 W2 (by omega)
  have p2 := pw_le (Apr (2 * j) + Afun (t + 1) + (t + 3)) (W2 - 1) (by omega)
  have p3 := pw_le h (W2 - 1) (by omega)
  have p4 : pw (W2 + 1) = 2 * pw W2 := pw_S W2
  have hK : y2v t (2 * j) + 2 * (pw W2 - 1 - y1o t (2 * j)) + 2 = pw (W2 + 1) := by omega
  have e1 : bin h G =
      bin (2 * j + (r2 + (c2 + 1) + 1)) (pw (2 * j) * (2 * (pw r2 * (2 * C2 + 1)) + 1)) := by
    rw [← hG1, ← hG, ← eL2, ← eL]
  have p5 := pw_le L h (by omega)
  have hG2 : G1 < pw h := by omega
  have Step : ∀ u t' c' C', L ≤ u + 1 → G1 ≤ pw u →
      G1 + (pw W2 - 1 - y1o t (2 * j)) + 1 = pw u + pw t' * (2 * C' + 1) →
      u = t' + (c' + 1) → pw t' * (2 * C' + 1) < pw u →
      ReachesPlus tm (D1 (t + 1) (TL (bin h G) B0) W0)
        (D1 (t' + 1) (TL (bin c' C') (U B0)) (W2 + 1)) := by
    intro u t' c' C' h1' h2' h3' h4' h5'
    rw [e1]
    exact a_O0_next t k j r2 c2 C2 W0 (pw W2 - 1 - y1o t (2 * j)) u t' c' C' W2
      hk (by dsimp [W0]; omega) hZv eW2 hK (by rwa [← eL2, ← hG1])
      (by rwa [← eL2]) (by rw [← hG1]; omega) (by rwa [← hG1])
      (by rwa [← hG1]) h4' h5'
  rcases le_or_gt (y1o t (2 * j)) G1 with hle | hlt
  · obtain ⟨p0, q0, hrun, hrat⟩ := hd hle
    obtain ⟨d0, dp⟩ := ones_not_pow _ p0 q0 hrun (by omega)
    obtain ⟨t', C', hD⟩ := N_tz _ d0
    have hlt2 : pw t' * (2 * C' + 1) < pw W2 := by omega
    obtain ⟨c', eu, hC'⟩ := tz_bound W2 t' C' hlt2
    refine good_back (Step W2 t' c' C' (by omega) (by omega) (by omega) eu hlt2) ?_
    have hq0 := ones_lt _ p0 q0 h hrun (by omega) (by omega)
    exact level_run (G1 - y1o t (2 * j)) t' c' C' W2 p0 q0 h 0 (G1 - y1o t (2 * j)) (W2 + 1)
      hD hC' eu hrun hrat (by omega) (by simp) d0 (by omega) dp
      (by omega) (by omega) (by omega) (by omega)
      (fun et _ e => by
        subst et e
        have hd335 : pw 0 * (2 * 167 + 1) = 335 := by decide
        rw [hd335] at hD
        rw [hD] at hrun
        exact not_LR_335 ⟨p0, q0, hrun, hrat⟩)
  · set Zl := pw (W2 - 1) + G1 - y1o t (2 * j)
    have hZl_eq : Zl + y1o t (2 * j) = pw (W2 - 1) + G1 := by dsimp [Zl]; omega
    have z0 : Zl ≠ 0 := by dsimp [Zl]; omega
    obtain ⟨t', C', hD⟩ := N_tz Zl z0
    have hlt2 : pw t' * (2 * C' + 1) < pw (W2 - 1) := by omega
    obtain ⟨c', eu, hC'⟩ := tz_bound (W2 - 1) t' C' hlt2
    refine good_back (Step (W2 - 1) t' c' C' (by omega) (by omega) (by omega) eu hlt2) ?_
    have hun_eq : W2 - 1 = Apr (2 * j) + Afun (t + 1) + (t + 3) + (h - 1) := by omega
    have hw2_sub : W2 - 1 = Apr (2 * j) + Afun (t + 1) + (t + 1) + h + 1 := by omega
    exact level_low t (2 * j) G1 h Zl t' c' C' (W2 - 1) (W2 - 1) (W2 + 1)
      hD hC' eu (le_refl _) (Or.inl hun_eq) hZl_eq
      hlt hG2 hr hra ha (by omega) (by omega) (by omega) (by omega)
      (fun sh q C1 c1 j' theta hC1 hc hq hth hX =>
        short_B t (2 * j) G1 h t' C' q C1 c1 j' Zl theta (W2 - 1)
          hD hC1 hq (by rw [eu, hc]) hw2_sub hZl_eq sh hr hra ha hth hX)

private theorem step_odd_odd (t k h G j G1 : ℕ)
    (hk : t + 1 = 2 * k + 1) (ha : 26 ≤ t + 1)
    (_hlo : pw (h - 2) ≤ G) (hhi : G < pw h)
    (hG : G = pw (2 * j + 1) * (2 * G1 + 1))
    (hr : 2 * j + 1 + 3 ≤ h) (hra : 2 * j + 1 ≤ t + 1)
    (hd : y1o t (2 * j + 1) ≤ G1 → LR (G1 - y1o t (2 * j + 1))) :
    Good (F0 (t + 1) h (pw h - 1 - G)) := by
  refine good_back (F0_D1 t h G (pw h - 1 - G) (by omega)) ?_
  obtain ⟨c1, eh, hc1⟩ := tz_bound h (2 * j + 1) G1 (by linarith)
  have bA := Afun_bd (t + 1)
  have pa := Apr_pos (2 * j + 1)
  set W0 := t + (h + 1) + 1
  set Wf := Apr (2 * j + 1) + (Afun (t + 1) + (W0 + 1) + 1)
  have wv : Wf = Apr (2 * j + 1) + Afun (t + 1) + (t + 1) + h + 3 := by dsimp [Wf, W0]; omega
  have hZv := zv_lt2 t (2 * j + 1) W0 (by dsimp [W0]; omega) (by dsimp [W0]; omega)
  have y4 := y1o_lt4 t (2 * j + 1) (by omega)
  have hy2 := y2v_y1o t (2 * j + 1)
  have p1 : pw Wf = 2 * pw (Wf - 1) := pw_pred2 Wf (by omega)
  have p0 : pw (Wf - 1) = 2 * pw (Wf - 2) := by
    have : Wf - 2 = Wf - 1 - 1 := by omega
    rw [this]; exact pw_pred2 (Wf - 1) (by omega)
  have p2 := pw_le (Apr (2 * j + 1) + Afun (t + 1) + (t + 3)) (Wf - 2) (by omega)
  have p3 := pw_le h (Wf - 2) (by omega)
  have p9 := pw_le 9 (Wf - 2) (by omega)
  have hp9 : pw 9 = 512 := by decide
  rw [hp9] at p9
  have p5 := pw_le c1 h (by omega)
  have hG2 : G1 < pw h := by omega
  have hK : y2v t (2 * j + 1) + 1 + 2 * (pw (Wf - 1) - 1 - y1o t (2 * j + 1)) + 1 =
      pw Wf := by omega
  have e1 : bin h G = bin (2 * j + 1 + (c1 + 1)) (pw (2 * j + 1) * (2 * G1 + 1)) := by
    rw [← hG, ← eh]
  set Z := G1 + pw (Wf - 1) - y1o t (2 * j + 1)
  have z1 : Z + y1o t (2 * j + 1) = pw (Wf - 1) + G1 := by dsimp [Z]; omega
  have z0 : Z ≠ 0 := by omega
  obtain ⟨t', C', hD⟩ := N_tz Z z0
  have hlt2 : pw t' * (2 * C' + 1) < pw Wf := by omega
  obtain ⟨c', ew, hC'⟩ := tz_bound Wf t' C' hlt2
  have ew2 : t' + (c' + 1) = Wf := ew.symm
  have hstep : ReachesPlus tm (D1 (t + 1) (TL (bin h G) B0) W0)
      (D1 (t' + 1) (TL (bin c' C') (U B0)) (Wf + 1)) := by
    rw [e1, ← ew2]
    exact a_O1_next t k j c1 G1 W0 (pw (Wf - 1) - 1 - y1o t (2 * j + 1)) t' c' C'
      hk (by dsimp [W0]; omega) hZv (by rwa [ew2]) ew2.symm (by omega) hc1
      (by rw [ew2]; omega) (by rw [← hD]; dsimp [Z]; omega) (by rw [ew2]; omega)
  refine good_back hstep ?_
  have h83 : t' = 0 → Wf + 1 = (t' + 1) + c' + 1 → C' ≠ 167 := by
    intro et _ e; subst et e
    have hd335 : pw 0 * (2 * 167 + 1) = 335 := by decide
    rw [hd335] at hD; omega
  rcases le_or_gt (y1o t (2 * j + 1)) G1 with hle | hlt
  · obtain ⟨p0', q0, hrun, hrat⟩ := hd hle
    obtain ⟨d0, dp⟩ := ones_not_pow _ p0' q0 hrun (by omega)
    have hq0 := ones_lt _ p0' q0 h hrun (by omega) (by omega)
    have hr2 := ones_high _ p0' q0 (Wf - 1) hrun (by omega)
    have eZ : G1 - y1o t (2 * j + 1) + pw (Wf - 1) = Z := by dsimp [Z]; omega
    rw [eZ] at hr2
    have s1 := pw_split h (Wf - 1) (by omega)
    exact level_run Z t' c' C' Wf p0' q0 h (pw (Wf - 1 - h)) (G1 - y1o t (2 * j + 1)) (Wf + 1)
      hD hC' ew hr2 hrat (by omega) (by linarith) d0 (by omega) dp
      (by omega) (by omega) (by omega) (by omega) h83
  · exact level_low t (2 * j + 1) G1 h Z t' c' C' Wf (Wf - 1) (Wf + 1)
      hD hC' ew (by omega) (Or.inr (by omega)) z1 hlt hG2 hr hra ha
      (by omega) (by omega) (by omega) h83
      (fun sh q C1 c2 j' theta hC1 hc hq hth hX =>
        short_C t (2 * j + 1) G1 h t' C' q C1 c2 j' Z theta Wf
          hD hC1 hq (by omega) wv z1 sh hr hra ha hth hX)

private theorem inv_step (e : Bool) (a h G : ℕ) (hI : Inv e a h G) :
    Good (FC e a h (pw h - 1 - G)) := by
  cases e
  · cases a with
    | zero => obtain ⟨ha, _⟩ := hI; omega
    | succ t =>
      rcases N_parity (t + 1) with ⟨k, hk⟩ | ⟨k, hk⟩
      · exact step_e0_even t k h G hk hI
      · obtain ⟨ha, hh, hlo, hhi, r, G1, hG, hr, _, hra, hD⟩ := hI
        obtain ⟨_, hd, _⟩ := hD t rfl
        have hev : isEven (t + 1) = false := by rw [hk]; exact even_2j1 k
        have hd2 := hd hev rfl
        rcases N_parity r with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact step_odd_even t k h G j G1 hk ha hlo hhi hG hr hra hd2
        · exact step_odd_odd t k h G j G1 hk ha hlo hhi hG hr hra hd2
  · exact step_e1 a h G hI

/-! ## Initial Trajectory and Non-Halting Theorem -/

private def w_start0 : List Sym :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
   1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1]

private theorem start0_raw :
    ReachesStar tm (init []) (NatCfg.toCfg (K := 6) ⟨0, 0, 0, 1882276860963498⟩) := by
  rw [← toCfg_zero (K := 6)]
  exact ⟨2742, stepsNat_sound tm 2742 ⟨0, 0, 0, 0⟩ ⟨0, 0, 0, 1882276860963498⟩
    (by decide +kernel) (by decide)⟩

private theorem start0_toCfg :
    NatCfg.toCfg (K := 6) ⟨0, 0, 0, 1882276860963498⟩ = F0 11 12 458 := by
  have h1 : NatCfg.toCfg (K := 6) ⟨0, 0, 0, 1882276860963498⟩ =
      Cfg.headLeft A (decodeHalf 0) (decodeHalf 1882276860963498) :=
    toCfg_headLeft (K := 6) A 0 1882276860963498
  have h_enc : encodeList w_start0 0 = 1882276860963498 := by decide
  have h2 : decodeHalf 1882276860963498 = w_start0 +> (default : Side) := by
    rw [← h_enc, ← decodeHalf_encodeList, decodeHalf_zero]
  have h_bin : zL 11 ++ true :: bin 12 458 =
      [false, false, false, false, false, false, false, false, false, false, false, true,
       false, true, false, true, false, false, true, true, true, false, false, false] := by
    decide
  rw [h1, decodeHalf_zero, h2]
  unfold F0 AC B0
  rw [h_bin, ListBlank.cons_zero_default]
  rfl

private theorem start0 : ReachesStar tm (init []) (F0 11 12 458) := by
  rw [← start0_toCfg]
  exact start0_raw

private def Gs : ℕ := 2296833611741004516
private def G1s : ℕ := 287104201467625564
private def Cp : ℕ := 4501401409422219
private def C2p : ℕ := 1125350352355554
private def Kp : ℕ := 18010002073583612
private def xs : ℕ := 2198217948444

private theorem s1 : ReachesPlus tm (F0 11 12 458) (D1 1 (TL (bin 52 Cp) (U B0)) 55) := by
  have h1 := F0_D1 10 12 3637 458 (by decide)
  have h_eq : bin 12 3637 =
      bin (2 * 0 + (1 + (9 + 1) + 1)) (pw (2 * 0) * (2 * (pw 1 * (2 * 454 + 1)) + 1)) := by
    decide
  rw [h_eq] at h1
  have h2 := a_O0_next 10 5 0 1 9 454 24 Kp 53 0 52 Cp 54
    rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) rfl (by decide)
  exact ReachesPlus.trans h1 h2

private theorem s2 :
    ReachesPlus tm (D1 1 (TL (bin 52 Cp) (U B0)) 55) (AC (TL (zL 52) (D3 B0)) (bin 61 xs)) := by
  have h_cp : bin 52 Cp =
      bin (2 * 0 + (0 + (50 + 1) + 1)) (pw (2 * 0) * (2 * (pw 0 * (2 * C2p + 1)) + 1)) := by
    decide
  rw [h_cp]
  have h := b_O0 0 0 0 0 50 C2p 55 rfl (by decide) (by decide) (by decide) (by decide)
  have h_w : Apr (2 * 0) + (Afun (0 + 1) + (55 + 1) + 1) = 61 := by decide
  have h_x : y2v 0 (2 * 0) + 2 * (pw (0 + (50 + 1)) - pw 0 * (2 * C2p + 1)) = xs := by decide
  rwa [h_w, h_x] at h

private theorem s3 :
    ReachesPlus tm (AC (TL (zL 52) (D3 B0)) (bin 61 xs)) (FC false 131 61 (pw 61 - 1 - Gs)) := by
  have h := d3_fin 52 61 xs (by decide)
  have ho : isOdd 52 = false := by decide
  have ha : Apr 52 = 131 := by decide
  have hx : xs + 2 * pw 52 - 1 = pw 61 - 1 - Gs := by decide
  rwa [ho, ha, hx] at h

private theorem inv0 : Inv false 131 61 Gs := by
  refine ⟨by decide, by decide, by decide, by decide,
    ⟨2, G1s, by decide, by decide, by decide, by decide, ?_⟩⟩
  intro t ht
  have ht' : t = 130 := by omega
  subst ht'
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact absurd h (by decide)
  · intro _ _ hle
    exfalso
    have P := y1o_lo 130 2
    have P2 := pw_le 61 (Apr 2 + Afun (130 + 1) + (130 + 2)) (by decide)
    have h61 : G1s < pw 61 := by decide
    omega
  · intro _ he; cases he

private def PInv (c : Cfg Sym (Fin 6)) : Prop :=
  ∃ e a h G, c = FC e a h (pw h - 1 - G) ∧ Inv e a h G

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  have h_init : ReachesStar target_tm (init [])
      (Solution.FC false 131 61 (Solution.pw 61 - 1 - Solution.Gs)) := by
    have h12 := ReachesPlus.trans Solution.s1 Solution.s2
    have h13 := ReachesPlus.trans h12 Solution.s3
    exact ReachesStar.trans Solution.start0 h13.to_star
  have h0 : Solution.PInv (Solution.FC false 131 61 (Solution.pw 61 - 1 - Solution.Gs)) :=
    ⟨false, 131, 61, Solution.Gs, rfl, Solution.inv0⟩
  exact IsNotHalt.of_reachesPlus_invariant h_init h0 (fun c hc => by
    obtain ⟨e, a, h, G, rfl, hInv⟩ := hc
    obtain ⟨e', a', h', G', hPlus, hInv'⟩ := Solution.inv_step e a h G hInv
    exact ⟨Solution.FC e' a' h' (Solution.pw h' - 1 - G'), hPlus, e', a', h', G', rfl, hInv'⟩)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LCHHH
