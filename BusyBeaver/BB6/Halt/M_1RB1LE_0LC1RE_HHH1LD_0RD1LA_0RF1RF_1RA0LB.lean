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
import BusyBeaver.Calculi.Accelerated


/-!
# Busy Beaver Machine `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.Accelerated`
and defines `target_tm` for `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 3, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

-- Holdout #123 (797:#123 / 608:#87, 1RB1LE_0LC1RE_---1LD_0RD1LA_0RF1RF_1RA0LB)
-- derived_from:
-- suspects/partial/accelerated/m_1rb1le_0lc1re_hhh1ld_0rd1la_0rf1rf_1ra0lb/has_queried_acceleration.lean

def subGuard (a b : ℕ) : ℕ :=
  if b ≤ a then a - b else 0

private theorem subGuard_eq {a b : ℕ} (h : b ≤ a) : subGuard a b = a - b :=
  (ite_eq_left_of_eq_true _ _ (eq_true h))

private theorem ms_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)} {m n : ℕ}
    (h₁ : c₁ [target_tm]⊢^{m} c₂) (h₂ : c₂ [target_tm]⊢^{n} c₃) :
    c₁ [target_tm]⊢^{m + n} c₃ := by
  unfold multiStep at *
  rw [Nat.add_comm m n, Function.iterate_add_apply]
  rcases h : (Option.bind · (step target_tm))^[m] (some c₁) with _ | c'
  · rw [h] at h₁; nomatch h₁
  · rw [h] at h₁; cases h₁; exact h₂

private theorem zero_cons_def : (0 : Fin 2) >> (default : ListBlank (Fin 2)) = default :=
  ListBlank.cons_default_default

private theorem head_def_fin : (default : ListBlank (Fin 2)).head = 0 :=
  ListBlank.head_default_fin

private theorem tail_def_fin : (default : ListBlank (Fin 2)).tail = default :=
  ListBlank.tail_default

private theorem app_assoc {α : Type*} [Inhabited α] :
    ∀ (l₁ l₂ : List α) (s : ListBlank α), (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s)
  | [], _, _ => rfl
  | _ :: xs, l₂, s => by simp only [List.cons_append, ListBlank.append, app_assoc xs l₂ s]

private theorem pow_add_list {α : Type*} (u : List α) (m n : ℕ) :
    u ^ (m + n) = u ^ m ++ u ^ n :=
  list_pow_add u m n

private theorem pow_succ_right {α : Type*} (u : List α) (k : ℕ) :
    u ^ (k + 1) = u ^ k ++ u :=
  list_pow_succ' u k

private theorem pow_succ_left {α : Type*} (u : List α) (k : ℕ) :
    u ^ (k + 1) = u ++ u ^ k :=
  list_pow_succ u k

private def evalWin (l r : ListBlank (Fin 2)) (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  if dR then (ls +> l) {{q}}> (rs +> r) else (ls +> l) <{{q}} (rs +> r)

private def stepWin (bL bR : Bool) : Fin 6 × Bool × List (Fin 2) × List (Fin 2) →
    Option (Fin 6 × Bool × List (Fin 2) × List (Fin 2))
  | (q, true, ls, a :: rs) =>
      match target_tm q a with
      | some (some q', Stmt.write w Dir.right) => some (q', true, w :: ls, rs)
      | some (some q', Stmt.write w Dir.left) => some (q', false, ls, w :: rs)
      | _ => none
  | (q, true, ls, []) =>
      if bR then
        match target_tm q 0 with
        | some (some q', Stmt.write w Dir.right) => some (q', true, w :: ls, [])
        | some (some q', Stmt.write w Dir.left) => some (q', false, ls, [w])
        | _ => none
      else none
  | (q, false, a :: ls, rs) =>
      match target_tm q a with
      | some (some q', Stmt.write w Dir.right) => some (q', true, w :: ls, rs)
      | some (some q', Stmt.write w Dir.left) => some (q', false, ls, w :: rs)
      | _ => none
  | (q, false, [], rs) =>
      if bL then
        match target_tm q 0 with
        | some (some q', Stmt.write w Dir.right) => some (q', true, [w], rs)
        | some (some q', Stmt.write w Dir.left) => some (q', false, [], [w] ++ rs)
        | _ => none
      else none

private def multiStepWin (bL bR : Bool) : ℕ → Fin 6 × Bool × List (Fin 2) × List (Fin 2) →
    Option (Fin 6 × Bool × List (Fin 2) × List (Fin 2))
  | 0, st => some st
  | n + 1, st => (stepWin bL bR st).bind (multiStepWin bL bR n)

private def checkWin (bL bR : Bool) (n : ℕ) (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2))
    (q' : Fin 6) (dR' : Bool) (ls' rs' : List (Fin 2)) : Bool :=
  multiStepWin bL bR n (q, dR, ls, rs) == some (q', dR', ls', rs')

private theorem stepWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
    (hL : bL = true → l = default) (hR : bR = true → r = default)
    {q q' : Fin 6} {dR dR' : Bool} {ls rs ls' rs' : List (Fin 2)}
    (hs : stepWin bL bR (q, dR, ls, rs) = some (q', dR', ls', rs')) :
    step target_tm (evalWin l r q dR ls rs) = some (evalWin l r q' dR' ls' rs') := by
  have h_exec : ∀ (x : Fin 2) (ls₀ rs₀ : List (Fin 2)),
      evalWin l r q dR ls rs = ⟨some q, ⟨x, ls₀ +> l, rs₀ +> r⟩⟩ →
      (match target_tm q x with
       | some (some q₁, Stmt.write w Dir.right) => some (q₁, true, w :: ls₀, rs₀)
       | some (some q₁, Stmt.write w Dir.left) => some (q₁, false, ls₀, w :: rs₀)
       | _ => none) = some (q', dR', ls', rs') →
      step target_tm (evalWin l r q dR ls rs) = some (evalWin l r q' dR' ls' rs') := by
    intro x ls₀ rs₀ hev hm
    rw [hev]
    rcases htm : target_tm q x with _ | ⟨q_opt, stmt⟩
    · rw [htm] at hm; nomatch hm
    · rcases q_opt with _ | q₁
      · rw [htm] at hm; nomatch hm
      · rcases stmt with ⟨w, dir⟩
        cases dir <;>
        · rw [htm] at hm
          injection hm with ht
          injection ht with hq hd
          injection hd with hdR hls
          injection hls with hls' hrs'
          subst hq hdR hls' hrs'
          simp [evalWin, step, htm, Tape.write, Tape.move, ListBlank.append]
  unfold stepWin at hs
  cases dR with
  | true =>
      cases rs with
      | cons a rs₀ =>
          dsimp only at hs
          exact h_exec a ls rs₀ (by simp [evalWin, ListBlank.append]) hs
      | nil =>
          cases hbR : bR with
          | false => simp [hbR] at hs
          | true =>
              simp only [hbR, ↓reduceIte] at hs
              have hr0 := hR hbR; subst hr0
              exact h_exec 0 ls [] (by simp [evalWin, ListBlank.append, head_def_fin,
                tail_def_fin]) hs
  | false =>
      cases ls with
      | cons a ls₀ =>
          dsimp only at hs
          exact h_exec a ls₀ rs (by simp [evalWin, ListBlank.append]) hs
      | nil =>
          cases hbL : bL with
          | false => simp [hbL] at hs
          | true =>
              simp only [hbL, ↓reduceIte, List.singleton_append] at hs
              have hl0 := hL hbL; subst hl0
              exact h_exec 0 [] rs (by simp [evalWin, ListBlank.append, head_def_fin,
                tail_def_fin]) hs

private theorem checkWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
    (hL : bL = true → l = default) (hR : bR = true → r = default) :
    ∀ (n : ℕ) (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2))
      (q' : Fin 6) (dR' : Bool) (ls' rs' : List (Fin 2)),
      checkWin bL bR n q dR ls rs q' dR' ls' rs' = true →
      (evalWin l r q dR ls rs) [target_tm]⊢^{n} (evalWin l r q' dR' ls' rs')
  | 0, q, dR, ls, rs, q', dR', ls', rs', h => by
      unfold checkWin multiStepWin at h
      rcases eq_of_beq h with ⟨⟩; rfl
  | n + 1, q, dR, ls, rs, q', dR', ls', rs', h => by
      unfold checkWin multiStepWin at h
      rcases hsw : stepWin bL bR (q, dR, ls, rs) with _ | ⟨q₁, dR₁, ls₁, rs₁⟩
      · simp [hsw] at h
      · simp only [hsw, Option.bind_some] at h
        have h1 : (evalWin l r q dR ls rs) [target_tm]⊢^{1} (evalWin l r q₁ dR₁ ls₁ rs₁) :=
          stepWin_sound hL hR hsw
        have h2 := checkWin_sound hL hR n q₁ dR₁ ls₁ rs₁ q' dR' ls' rs' h
        rw [Nat.add_comm n 1]
        exact ms_trans h1 h2

private theorem chkWin_eq {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (bL bR : Bool) (n : ℕ)
    (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2))
    (q' : Fin 6) (dR' : Bool) (ls' rs' : List (Fin 2))
    (l r : ListBlank (Fin 2))
    (hL : bL = true → l = default) (hR : bR = true → r = default)
    (h₁ : c₁ = evalWin l r q dR ls rs)
    (h₂ : c₂ = evalWin l r q' dR' ls' rs')
    (hc : checkWin bL bR n q dR ls rs q' dR' ls' rs' = true) :
    c₁ [target_tm]⊢^{n} c₂ :=
  h₁ ▸ h₂ ▸ checkWin_sound hL hR n q dR ls rs q' dR' ls' rs' hc
private theorem walkWordRight (s : ℕ) (q : Fin 6) (dR : Bool) (pL u pR v : List (Fin 2))
    (hbody : checkWin false false s q dR pL (pR ++ v) q dR (pL ++ u) pR = true) :
    ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
      (evalWin l ((v ^ k) +> r) q dR pL pR) [target_tm]⊢^{s * k}
        (evalWin ((u ^ k) +> l) r q dR pL pR)
  | 0, _, _ => by simp [list_pow_succ, list_pow_zero, list_pow_one]
  | k + 1, l, r => by
      have hstart : evalWin l ((v ^ (k + 1)) +> r) q dR pL pR =
          evalWin l ((v ^ k) +> r) q dR pL (pR ++ v) := by
        simp only [evalWin, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, app_assoc]
      have hmid : evalWin l ((v ^ k) +> r) q dR (pL ++ u) pR =
          evalWin (u +> l) ((v ^ k) +> r) q dR pL pR := by
        simp only [evalWin, app_assoc]
      have hend : evalWin ((u ^ k) +> (u +> l)) r q dR pL pR =
          evalWin ((u ^ (k + 1)) +> l) r q dR pL pR := by
        rw [← app_assoc (u ^ k) u l, ← pow_succ_right u k]
      rw [hstart]
      have h1 := checkWin_sound (bL := false) (bR := false) (l := l) (r := (v ^ k) +> r)
        (fun hc => nomatch hc) (fun hc => nomatch hc) s q dR pL (pR ++ v) q dR (pL ++ u) pR hbody
      rw [hmid] at h1
      have h2 := walkWordRight s q dR pL u pR v hbody k (u +> l) r
      rw [hend] at h2
      rw [show s * (k + 1) = s + s * k by ring]
      exact ms_trans h1 h2

private theorem walkWordLeft (s : ℕ) (q : Fin 6) (dR : Bool) (pL u pR v : List (Fin 2))
    (hbody : checkWin false false s q dR (pL ++ u) pR q dR pL (pR ++ v) = true) :
    ∀ (k : ℕ) (l r : ListBlank (Fin 2)),
      (evalWin ((u ^ k) +> l) r q dR pL pR) [target_tm]⊢^{s * k}
        (evalWin l ((v ^ k) +> r) q dR pL pR)
  | 0, _, _ => by simp [list_pow_succ, list_pow_zero, list_pow_one]
  | k + 1, l, r => by
      have hstart : evalWin ((u ^ (k + 1)) +> l) r q dR pL pR =
          evalWin ((u ^ k) +> l) r q dR (pL ++ u) pR := by
        simp only [evalWin, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, app_assoc]
      have hmid : evalWin ((u ^ k) +> l) r q dR pL (pR ++ v) =
          evalWin ((u ^ k) +> l) (v +> r) q dR pL pR := by
        simp only [evalWin, app_assoc]
      have hend : evalWin l ((v ^ k) +> (v +> r)) q dR pL pR =
          evalWin l ((v ^ (k + 1)) +> r) q dR pL pR := by
        rw [← app_assoc (v ^ k) v r, ← pow_succ_right v k]
      rw [hstart]
      have h1 := checkWin_sound (bL := false) (bR := false) (l := (u ^ k) +> l) (r := r)
        (fun hc => nomatch hc) (fun hc => nomatch hc) s q dR (pL ++ u) pR q dR pL (pR ++ v) hbody
      rw [hmid] at h1
      have h2 := walkWordLeft s q dR pL u pR v hbody k l (v +> r)
      rw [hend] at h2
      rw [show s * (k + 1) = s + s * k by ring]
      exact ms_trans h1 h2

inductive Mode
  | Init0
  | B0
  | A0
  | E0
  | F0
  | F0z
  | Halt

inductive LTok
  | U (a : ℕ)
  | M8 (k : ℕ)
  | M06 (k : ℕ)

inductive WTok
  | B (b : Bool)
  | T010 (k : ℕ)
  | MW (k : ℕ)

abbrev BaseState := Mode × List LTok × List WTok

private def u8Pref : List (Fin 2) := [1, 1, 1, 1, 1, 1, 1, 1, 0]
private def u8 : List (Fin 2) := 1 :: u8Pref
private def u8Rot : List (Fin 2) := u8Pref ++ [1]
private def u06Tail : List (Fin 2) := [0, 1, 1, 1, 1, 1, 1, 1, 0]
private def u06 : List (Fin 2) := 1 :: u06Tail
private def t010 : List (Fin 2) := [0, 1, 0]
private def wPref5 : List (Fin 2) := [0, 1, 1, 0, 0]
private def wSuff5 : List (Fin 2) := [1, 0, 0, 1, 0]
private def w24 : List (Fin 2) := wPref5 ++ wSuff5
private def v10 : List (Fin 2) := wSuff5 ++ wPref5

private def eL : List LTok → ListBlank (Fin 2)
  | [] => default
  | .U a :: xs => (([1] : List (Fin 2)) ^ (a + 1)) +> ([0] +> eL xs)
  | .M8 k :: xs => (u8 ^ (k + 1)) +> eL xs
  | .M06 k :: xs => (u06 ^ (k + 1)) +> eL xs

private def eW : List WTok → ListBlank (Fin 2)
  | [] => default
  | .B false :: xs => [0] +> eW xs
  | .B true :: xs => [1] +> eW xs
  | .T010 k :: xs => (t010 ^ (k + 1)) +> eW xs
  | .MW k :: xs => (v10 ^ (k + 1)) +> eW xs

private def encodeBase : BaseState → Cfg (Fin 2) (Fin 6)
  | (.Init0, _, _) => init []
  | (.B0, l, w) => evalWin (eL l) (eW w) 1 true [] [0]
  | (.A0, l, w) => evalWin (eL l) (eW w) 0 true [] []
  | (.E0, l, w) => evalWin (eL l) (eW w) 4 true [] []
  | (.F0, l, w) => evalWin (eL l) (eW w) 5 true [] []
  | (.F0z, l, w) => evalWin (eL l) (eW w) 5 true [0] []
  | (.Halt, _, w) => evalWin default (eW w) 2 true [] [0, 0]

def peelM8 (k : ℕ) (xs : List LTok) : List LTok :=
  match k with
  | 0 => xs
  | k' + 1 => .M8 k' :: xs

def peelM06 (k : ℕ) (xs : List LTok) : List LTok :=
  match k with
  | 0 => xs
  | k' + 1 => .M06 k' :: xs

def peelT010 (k : ℕ) (xs : List WTok) : List WTok :=
  match k with
  | 0 => xs
  | k' + 1 => .T010 k' :: xs

def peelMW (k : ℕ) (xs : List WTok) : List WTok :=
  match k with
  | 0 => xs
  | k' + 1 => .MW k' :: xs

def mwTail (k : ℕ) (rest : List WTok) : List WTok :=
  .B false :: .B false :: .B true :: .B false :: .B false ::
    .B true :: .B true :: .B false :: .B false :: peelMW k rest

def unconsL : List LTok → Option (ℕ × List LTok)
  | [] => none
  | .U a :: rest => some (a, rest)
  | .M8 k :: rest => some (8, peelM8 k rest)
  | .M06 k :: rest => some (0, .U 6 :: peelM06 k rest)

def unconsW : List WTok → Option (Bool × List WTok)
  | [] => none
  | .B b :: rest => some (b, rest)
  | .T010 k :: rest => some (false, .B true :: .B false :: peelT010 k rest)
  | .MW k :: rest => some (true, mwTail k rest)

def bump1L (l : List LTok) : List LTok :=
  match unconsL l with
  | none => [.U 0]
  | some (a, rest) => .U (a + 1) :: rest

def bump2L (l : List LTok) : List LTok := bump1L (bump1L l)
def bump4L (l : List LTok) : List LTok := bump2L (bump2L l)

def pushM8 (k : ℕ) : List LTok → List LTok
  | .M8 m :: rest => .M8 (k + 1 + m) :: rest
  | .U a :: rest => if a == 8 then .M8 (k + 1) :: rest else .M8 k :: .U a :: rest
  | xs => .M8 k :: xs

def pushM06 (k : ℕ) : List LTok → List LTok
  | .M06 m :: rest => .M06 (k + 1 + m) :: rest
  | .U a :: .U b :: rest =>
      if a == 0 && b == 6 then .M06 (k + 1) :: rest else .M06 k :: .U a :: .U b :: rest
  | xs => .M06 k :: xs

def pushT010 (k : ℕ) : List WTok → List WTok
  | .T010 m :: rest => .T010 (k + 1 + m) :: rest
  | xs => .T010 k :: xs

def pushMW (k : ℕ) : List WTok → List WTok
  | .MW m :: rest => .MW (k + 1 + m) :: rest
  | xs => .MW k :: xs

def matchWPref5 : List WTok → Option (List WTok)
  | .B false :: .B true :: .B true :: .B false :: .B false :: wRest => some wRest
  | _ => none

def pushW24 (k : ℕ) (w : List WTok) : List WTok :=
  let pref : List WTok := [.B false, .B true, .B true, .B false, .B false]
  let suff : List WTok := [.B true, .B false, .B false, .B true, .B false]
  match matchWPref5 w with
  | some wRest => pref ++ pushMW k wRest
  | none =>
      match k with
      | 0 => pref ++ suff ++ w
      | k' + 1 => pref ++ (.MW k' :: suff) ++ w

def matchV10 : List WTok → Option (List WTok)
  | .B true :: .B false :: .B false :: .B true :: .B false ::
    .B false :: .B true :: .B true :: .B false :: .B false :: wRest => some wRest
  | _ => none

def stepB0 (l : List LTok) (w : List WTok) : BaseState × ℕ :=
  match l with
  | .M8 k :: lp => ((.B0, lp, pushW24 k w), 24 * (k + 1))
  | _ =>
      match unconsL l with
      | none => ((.Halt, [], w), 1)
      | some (a, lp) =>
          if a = 8 then
            ((.B0, lp, pushW24 0 w), 24)
          else if a ≥ 3 then
            let q1 := (subGuard a 3) / 3
            let r := a % 3
            ((.B0, .U r :: lp, pushT010 q1 w), 9 * (q1 + 1))
          else if a = 0 then
            ((.F0z, bump2L lp, w), 7)
          else if a = 1 then
            ((.A0, bump4L lp, w), 7)
          else
            ((.B0, lp, .B false :: .B true :: .B true :: .B false :: w), 6)
def stepRightNil (m : Mode) (l : List LTok) : BaseState × ℕ :=
  match m with
  | .A0 => ((.B0, bump1L l, []), 1)
  | .E0 => ((.B0, .U 1 :: l, []), 3)
  | .F0 => ((.B0, bump2L l, []), 2)
  | _ => ((.B0, .U 1 :: l, []), 2)

def stepRightZero (m : Mode) (l : List LTok) (w1 : List WTok) : BaseState × ℕ :=
  match m with
  | .A0 =>
      match unconsW w1 with
      | none => ((.B0, bump1L l, []), 1)
      | some (false, w2) => ((.B0, bump1L l, w2), 1)
      | some (true, w2) => ((.E0, bump2L l, w2), 2)
  | .E0 => ((.F0z, l, w1), 1)
  | .F0 => ((.A0, bump1L l, w1), 1)
  | _ => ((.A0, .U 0 :: l, w1), 1)

def stepRightOne (m : Mode) (l : List LTok) (w1 : List WTok) : BaseState × ℕ :=
  match m with
  | .A0 =>
      match l with
      | [] => ((.B0, [], .B false :: w1), 3)
      | _ :: _ => ((.F0z, l, w1), 5)
  | .E0 => ((.F0, bump1L l, w1), 1)
  | .F0 =>
      match l with
      | [] => ((.B0, [], .B false :: w1), 1)
      | _ :: _ => ((.F0z, l, w1), 3)
  | _ => ((.B0, l, .B false :: w1), 1)

def stepRight (m : Mode) (l : List LTok) (w : List WTok) : BaseState × ℕ :=
  match unconsW w with
  | none => stepRightNil m l
  | some (false, w1) => stepRightZero m l w1
  | some (true, w1) => stepRightOne m l w1

def stepMotifA0? (l : List LTok) (w : List WTok) : Option (BaseState × ℕ) :=
  match l with
  | [] => none
  | t :: lp =>
      match w with
      | .MW k :: wRest => some ((.A0, pushM8 k (t :: lp), wRest), 32 * (k + 1))
      | .B false :: .MW k :: wRest =>
          match t with
          | .U a =>
              if a == 4 then
                some ((.A0, .U 4 :: pushM06 k lp, .B false :: wRest), 14 * (k + 1))
              else none
          | _ => none
      | _ =>
          match matchV10 w with
          | some wRest => some ((.A0, pushM8 0 (t :: lp), wRest), 32)
          | none => none

def stepSys : BaseState → Option (BaseState × ℕ)
  | (.Halt, _, _) => none
  | (.Init0, _, _) => some ((.B0, [.U 0], []), 1)
  | (.B0, l, w) => some (stepB0 l w)
  | (.A0, l, w) =>
      match stepMotifA0? l w with
      | some res => some res
      | none => some (stepRight .A0 l w)
  | (.E0, l, w) => some (stepRight .E0 l w)
  | (.F0, l, w) => some (stepRight .F0 l w)
  | (.F0z, l, w) => some (stepRight .F0z l w)

private theorem evalWin_b0_flip (l r : ListBlank (Fin 2)) (rs : List (Fin 2)) :
    evalWin l r 1 false [0] rs = evalWin l r 1 true [] (0 :: rs) := by
  simp [evalWin, ListBlank.append]

private theorem evalWin_b0_def (r : ListBlank (Fin 2)) :
    evalWin default r 1 false [] [0] = evalWin default ([0] +> r) 1 true [] [0] := by
  simp [evalWin, ListBlank.append, head_def_fin, tail_def_fin]

private theorem eL_peelM8 (k : ℕ) (xs : List LTok) :
    eL (peelM8 k xs) = (u8 ^ k) +> eL xs := by
  cases k with
  | zero => simp [peelM8, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | succ _ => rfl

private theorem eL_peelM06 (k : ℕ) (xs : List LTok) :
    eL (peelM06 k xs) = (u06 ^ k) +> eL xs := by
  cases k with
  | zero => simp [peelM06, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | succ _ => rfl

private theorem eW_peelT010 (k : ℕ) (xs : List WTok) :
    eW (peelT010 k xs) = (t010 ^ k) +> eW xs := by
  cases k with
  | zero => simp [peelT010, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | succ _ => rfl

private theorem eW_peelMW (k : ℕ) (xs : List WTok) :
    eW (peelMW k xs) = (v10 ^ k) +> eW xs := by
  cases k with
  | zero => simp [peelMW, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | succ _ => rfl

private theorem eL_u8 (xs : List LTok) :
    eL (.U 8 :: xs) = u8 +> eL xs := by
  simp [eL, u8, u8Pref, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq,
    ListBlank.append]

private theorem eL_u06 (xs : List LTok) :
    eL (.U 0 :: .U 6 :: xs) = u06 +> eL xs := by
  simp [eL, u06, u06Tail, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq,
    ListBlank.append]

private theorem eW_v10 (xs : List WTok) :
    eW (.B true :: .B false :: .B false :: .B true :: .B false ::
        .B false :: .B true :: .B true :: .B false :: .B false :: xs) =
      v10 +> eW xs := by
  simp [eW, v10, wSuff5, wPref5, ListBlank.append]

private theorem unconsL_none {l : List LTok} (h : unconsL l = none) : l = [] := by
  cases l with
  | nil => rfl
  | cons t _ => cases t <;> simp [unconsL] at h

private theorem unconsL_some {l rest : List LTok} {a : ℕ}
    (h : unconsL l = some (a, rest)) : eL l = eL (.U a :: rest) := by
  cases l with
  | nil => simp [unconsL] at h
  | cons t xs =>
      cases t with
      | U m => simp [unconsL] at h; obtain ⟨rfl, rfl⟩ := h; rfl
      | M8 k =>
          simp [unconsL] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [eL_u8, eL_peelM8]
          dsimp only [eL]
          rw [pow_succ_left u8 k, app_assoc]
      | M06 k =>
          simp [unconsL] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [eL_u06, eL_peelM06]
          dsimp only [eL]
          rw [pow_succ_left u06 k, app_assoc]

private theorem unconsW_none {w : List WTok} (h : unconsW w = none) : w = [] := by
  cases w with
  | nil => rfl
  | cons t _ => cases t <;> simp [unconsW] at h

private theorem unconsW_some {w rest : List WTok} {b : Bool}
    (h : unconsW w = some (b, rest)) : eW w = eW (.B b :: rest) := by
  cases w with
  | nil => simp [unconsW] at h
  | cons t xs =>
      cases t with
      | B b0 => simp [unconsW] at h; obtain ⟨rfl, rfl⟩ := h; rfl
      | T010 k =>
          simp [unconsW] at h
          obtain ⟨rfl, rfl⟩ := h
          dsimp only [eW]
          rw [eW_peelT010, pow_succ_left t010 k, app_assoc]
          simp [t010, ListBlank.append]
      | MW k =>
          simp [unconsW] at h
          obtain ⟨rfl, rfl⟩ := h
          have hv : eW (.B true :: mwTail k xs) = v10 +> eW (peelMW k xs) := by
            dsimp only [mwTail]
            exact eW_v10 (peelMW k xs)
          rw [hv, eW_peelMW]
          dsimp only [eW]
          rw [pow_succ_left v10 k, app_assoc]
private theorem eL_bump1L (l : List LTok) :
    eL (bump1L l) = [1] +> eL l := by
  unfold bump1L
  rcases hl : unconsL l with _ | ⟨a, rest⟩
  · rw [unconsL_none hl]
    simp [eL, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, ListBlank.append,
      zero_cons_def]
  · rw [unconsL_some hl]
    dsimp only [eL]
    rw [pow_succ_left ([1] : List (Fin 2)) (a + 1), app_assoc]

private theorem eL_bump2L (l : List LTok) :
    eL (bump2L l) = [1, 1] +> eL l := by
  rw [bump2L, eL_bump1L, eL_bump1L]
  simp [ListBlank.append]

private theorem eL_bump4L (l : List LTok) :
    eL (bump4L l) = [1, 1, 1, 1] +> eL l := by
  rw [bump4L, eL_bump2L, eL_bump2L]
  simp [ListBlank.append]

private def tailAfter1L : LTok → List LTok → ListBlank (Fin 2)
  | .U a, xs => (([1] : List (Fin 2)) ^ a) +> ([0] +> eL xs)
  | .M8 k, xs => u8Pref +> ((u8 ^ k) +> eL xs)
  | .M06 k, xs => u06Tail +> ((u06 ^ k) +> eL xs)

private theorem eL_cons_one (t : LTok) (xs : List LTok) :
    eL (t :: xs) = [1] +> tailAfter1L t xs := by
  cases t with
  | U a =>
      dsimp only [eL, tailAfter1L]
      rw [pow_succ_left ([1] : List (Fin 2)) a, app_assoc]
  | M8 k =>
      dsimp only [eL, tailAfter1L]
      rw [pow_succ_left u8 k, app_assoc]
      rfl
  | M06 k =>
      dsimp only [eL, tailAfter1L]
      rw [pow_succ_left u06 k, app_assoc]
      rfl

private theorem eL_pushM8 (k : ℕ) (l : List LTok) :
    eL (pushM8 k l) = (u8 ^ (k + 1)) +> eL l := by
  cases l with
  | nil => rfl
  | cons t rest =>
      cases t with
      | M8 m =>
          dsimp only [pushM8, eL]
          rw [show k + 1 + m + 1 = (k + 1) + (m + 1) by omega, pow_add_list, app_assoc]
      | M06 _ => rfl
      | U a =>
          dsimp only [pushM8]
          cases ha : (a == 8) with
          | false => rfl
          | true =>
              have ha8 : a = 8 := eq_of_beq ha
              subst ha8
              rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))]
              rw [eL_u8]
              dsimp only [eL]
              rw [pow_succ_right u8 (k + 1), app_assoc]

private theorem eL_pushM06 (k : ℕ) (l : List LTok) :
    eL (pushM06 k l) = (u06 ^ (k + 1)) +> eL l := by
  cases l with
  | nil => rfl
  | cons t1 rest1 =>
      cases t1 with
      | M8 _ => rfl
      | M06 m =>
          dsimp only [pushM06, eL]
          rw [show k + 1 + m + 1 = (k + 1) + (m + 1) by omega, pow_add_list, app_assoc]
      | U a =>
          cases rest1 with
          | nil => rfl
          | cons t2 rest2 =>
              cases t2 with
              | M8 _ => rfl
              | M06 _ => rfl
              | U b =>
                  dsimp only [pushM06]
                  cases hab : (a == 0 && b == 6) with
                  | false => rfl
                  | true =>
                      simp only [Bool.and_eq_true, beq_iff_eq] at hab
                      obtain ⟨rfl, rfl⟩ := hab
                      rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl))]
                      rw [eL_u06]
                      dsimp only [eL]
                      rw [pow_succ_right u06 (k + 1), app_assoc]

private theorem eW_pushT010 (k : ℕ) (w : List WTok) :
    eW (pushT010 k w) = (t010 ^ (k + 1)) +> eW w := by
  cases w with
  | nil => rfl
  | cons t rest =>
      cases t with
      | B _ => rfl
      | MW _ => rfl
      | T010 m =>
          dsimp only [pushT010, eW]
          rw [show k + 1 + m + 1 = (k + 1) + (m + 1) by omega, pow_add_list, app_assoc]

private theorem eW_pushMW (k : ℕ) (w : List WTok) :
    eW (pushMW k w) = (v10 ^ (k + 1)) +> eW w := by
  cases w with
  | nil => rfl
  | cons t rest =>
      cases t with
      | B _ => rfl
      | T010 _ => rfl
      | MW m =>
          dsimp only [pushMW, eW]
          rw [show k + 1 + m + 1 = (k + 1) + (m + 1) by omega, pow_add_list, app_assoc]

private theorem w24_pow_eq :
    ∀ (k : ℕ) (s : ListBlank (Fin 2)),
      (w24 ^ (k + 1)) +> s = wPref5 +> ((v10 ^ k) +> (wSuff5 +> s))
  | 0, s => by
      have hw1 : w24 ^ 1 = wPref5 ++ wSuff5 := by
        simp [w24, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq]
      rw [hw1, app_assoc wPref5 wSuff5]
      simp [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | k' + 1, s => by
      rw [pow_succ_left w24 (k' + 1), app_assoc w24 (w24 ^ (k' + 1)), w24_pow_eq k' s]
      have hw : w24 = wPref5 ++ wSuff5 := rfl
      have hv : wSuff5 ++ wPref5 = v10 := rfl
      rw [hw, app_assoc wPref5 wSuff5, ← app_assoc wSuff5 wPref5, hv,
        ← app_assoc v10 (v10 ^ k'), ← pow_succ_left v10 k']

private theorem matchWPref5_eq {w wRest : List WTok} (h : matchWPref5 w = some wRest) :
    w = .B false :: .B true :: .B true :: .B false :: .B false :: wRest := by
  unfold matchWPref5 at h
  split at h
  · injection h with h'; subst h'; rfl
  · nomatch h

private theorem eW_pushW24 (k : ℕ) (w : List WTok) :
    eW (pushW24 k w) = (w24 ^ (k + 1)) +> eW w := by
  have hpref : ∀ xs : List WTok,
      eW (.B false :: .B true :: .B true :: .B false :: .B false :: xs) = wPref5 +> eW xs := by
    intro xs
    simp [eW, wPref5, ListBlank.append]
  have hsuff : ∀ xs : List WTok,
      eW (.B true :: .B false :: .B false :: .B true :: .B false :: xs) = wSuff5 +> eW xs := by
    intro xs
    simp [eW, wSuff5, ListBlank.append]
  rw [w24_pow_eq k (eW w)]
  unfold pushW24
  rcases hm : matchWPref5 w with _ | wRest
  · cases k with
    | zero =>
        dsimp only [List.cons_append, List.nil_append]
        rw [hpref, hsuff]
        simp [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
    | succ k' =>
        dsimp only [List.cons_append, List.nil_append]
        rw [hpref]
        have hmw : ∀ xs : List WTok, eW (.MW k' :: xs) = (v10 ^ (k' + 1)) +> eW xs :=
          fun _ => rfl
        rw [hmw, hsuff]
  · dsimp only [List.cons_append, List.nil_append]
    rw [hpref, eW_pushMW, matchWPref5_eq hm, hpref]
    have hv : wSuff5 ++ wPref5 = v10 := rfl
    rw [← app_assoc wSuff5 wPref5, hv, ← app_assoc (v10 ^ k) v10, ← pow_succ_right v10 k]

private theorem u8Rot_pow_eq :
    ∀ (n : ℕ) (s : ListBlank (Fin 2)),
      [1] +> ((u8Rot ^ n) +> s) = (u8 ^ n) +> ([1] +> s)
  | 0, s => by simp [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | n' + 1, s => by
      rw [pow_succ_left u8Rot n', app_assoc u8Rot (u8Rot ^ n')]
      have hstep : u8Rot +> ((u8Rot ^ n') +> s) = u8Pref +> ([1] +> ((u8Rot ^ n') +> s)) := by
        simp [u8Rot, ListBlank.append, app_assoc]
      have hu8 : ([1] : List (Fin 2)) ++ u8Pref = u8 := rfl
      rw [hstep, u8Rot_pow_eq n' s,
        ← app_assoc [1] u8Pref, hu8, ← app_assoc u8 (u8 ^ n'), ← pow_succ_left u8 n']

private theorem drain3_loop :
    ∀ (q m : ℕ) (sL sW : ListBlank (Fin 2)),
      ReachesIn target_tm (9 * q)
        (evalWin ((([1] : List (Fin 2)) ^ (3 * q + m + 1)) +> sL) sW 1 false [0] [])
        (evalWin ((([1] : List (Fin 2)) ^ (m + 1)) +> sL) ((t010 ^ q) +> sW) 1 false [0] [])
  | 0, m, sL, sW => by
      simp [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | q' + 1, m, sL, sW => by
      have hsplit : ((([1] : List (Fin 2)) ^ (3 * (q' + 1) + m + 1)) +> sL) =
          ([1, 1, 1, 1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ (3 * q' + m)) +> sL) := by
        rw [show 3 * (q' + 1) + m + 1 = 4 + (3 * q' + m) by omega,
          pow_add_list ([1] : List (Fin 2)) 4 (3 * q' + m), app_assoc]
        simp [list_pow_succ, list_pow_zero, list_pow_one, List.append_eq]
      have h9 : ReachesIn target_tm 9
          (evalWin ((([1] : List (Fin 2)) ^ (3 * (q' + 1) + m + 1)) +> sL) sW 1 false [0] [])
          (evalWin ((([1] : List (Fin 2)) ^ (3 * q' + m + 1)) +> sL) (t010 +> sW) 1 false [0] []) :=
        chkWin_eq false false 9 1 false [0, 1, 1, 1, 1] [] 1 false [0, 1] [0, 1, 0]
          ((([1] : List (Fin 2)) ^ (3 * q' + m)) +> sL) sW
          (fun hc => nomatch hc) (fun hc => nomatch hc)
          (by rw [hsplit]; simp [evalWin, ListBlank.append])
          (by
            rw [pow_succ_left ([1] : List (Fin 2)) (3 * q' + m), app_assoc]
            simp [evalWin, t010, ListBlank.append])
          rfl
      have ih := drain3_loop q' m sL (t010 +> sW)
      have hend : (t010 ^ q') +> (t010 +> sW) = (t010 ^ (q' + 1)) +> sW := by
        rw [← app_assoc (t010 ^ q') t010 sW, ← pow_succ_right t010 q']
      rw [hend] at ih
      rw [show 9 * (q' + 1) = 9 + 9 * q' by omega]
      exact ms_trans h9 ih

private theorem motifB0_body :
    checkWin false false 24 1 false ([0] ++ u8) [] 1 false [0] w24 = true := by
  decide +kernel

private theorem motifB0_sound (k : ℕ) (lp : List LTok) (w : List WTok) :
    ReachesIn target_tm (24 * (k + 1))
      (encodeBase (.B0, .M8 k :: lp, w))
      (encodeBase (.B0, lp, pushW24 k w)) := by
  have hw := walkWordLeft 24 1 false [0] u8 [] w24 motifB0_body (k + 1) (eL lp) (eW w)
  have hstart : encodeBase (.B0, .M8 k :: lp, w) =
      evalWin ((u8 ^ (k + 1)) +> eL lp) (eW w) 1 false [0] [] := by
    dsimp only [encodeBase, eL]
    rw [← evalWin_b0_flip]
  have hend : encodeBase (.B0, lp, pushW24 k w) =
      evalWin (eL lp) ((w24 ^ (k + 1)) +> eW w) 1 false [0] [] := by
    dsimp only [encodeBase]
    rw [eW_pushW24, ← evalWin_b0_flip]
  rw [hstart, hend]
  exact hw
private theorem stepB0_sound (l : List LTok) (w : List WTok) :
    ReachesIn target_tm (stepB0 l w).2
      (encodeBase (.B0, l, w))
      (encodeBase (stepB0 l w).1) := by
  have stepB0_tail : ∀ (l₀ : List LTok) (hl : unconsL l₀ = unconsL l) (heL : eL l = eL l₀),
      match unconsL l₀ with
      | none => ReachesIn target_tm 1 (encodeBase (.B0, l, w)) (encodeBase (.Halt, [], w))
      | some (a, lp) =>
          ReachesIn target_tm
            (if a = 8 then 24
             else if a ≥ 3 then 9 * (((subGuard a 3) / 3) + 1)
             else if a = 0 then 7
             else if a = 1 then 7
             else 6)
            (encodeBase (.B0, l, w))
            (encodeBase
              (if a = 8 then (.B0, lp, pushW24 0 w)
               else if a ≥ 3 then (.B0, .U (a % 3) :: lp, pushT010 ((subGuard a 3) / 3) w)
               else if a = 0 then (.F0z, bump2L lp, w)
               else if a = 1 then (.A0, bump4L lp, w)
               else (.B0, lp, .B false :: .B true :: .B true :: .B false :: w))) := by
    intro l₀ _ heL
    rcases hu : unconsL l₀ with _ | ⟨a, lp⟩
    · have hl0 := unconsL_none hu
      subst hl0
      exact chkWin_eq true false 1 1 true [] [0] 2 false [] [0]
        default (eW w) (fun _ => rfl) (fun hc => nomatch hc)
        (by rw [encodeBase, heL]; simp [eL])
        (by simp [encodeBase, evalWin, ListBlank.append, head_def_fin, tail_def_fin])
        rfl
    · have hal : eL l = eL (.U a :: lp) := heL.trans (unconsL_some hu)
      dsimp only
      split_ifs with h8 h3 h0 h1
      · subst h8
        have hm0 : encodeBase (.B0, l, w) = encodeBase (.B0, .M8 0 :: lp, w) := by
          dsimp only [encodeBase]
          rw [hal, eL_u8]
          dsimp only [eL]
          have hu1 : u8 ^ 1 = u8 := by simp [list_pow_succ, list_pow_zero, list_pow_one,
            List.append_eq]
          rw [hu1]
        rw [hm0]
        exact motifB0_sound 0 lp w
      · let q1 := (subGuard a 3) / 3
        let r := a % 3
        have hsg : subGuard a 3 = a - 3 := subGuard_eq h3
        have ha_eq : a = 3 * (q1 + 1) + r := by dsimp [q1, r]; rw [hsg]; omega
        have hd := drain3_loop (q1 + 1) r ([0] +> eL lp) (eW w)
        have hstart : encodeBase (.B0, l, w) =
            evalWin ((([1] : List (Fin 2)) ^ (3 * (q1 + 1) + r + 1)) +> ([0] +> eL lp))
              (eW w) 1 false [0] [] := by
          dsimp only [encodeBase]
          rw [hal]
          dsimp only [eL]
          rw [← ha_eq, ← evalWin_b0_flip]
        have hend : encodeBase (.B0, .U r :: lp, pushT010 q1 w) =
            evalWin ((([1] : List (Fin 2)) ^ (r + 1)) +> ([0] +> eL lp))
              ((t010 ^ (q1 + 1)) +> eW w) 1 false [0] [] := by
          dsimp only [encodeBase, eL]
          rw [eW_pushT010, ← evalWin_b0_flip]
        rw [hstart, hend]
        exact hd
      · subst h0
        exact chkWin_eq false false 7 1 true [1, 0] [0] 5 true [0, 1, 1] []
          (eL lp) (eW w) (fun hc => nomatch hc) (fun hc => nomatch hc)
          (by rw [encodeBase, hal]; simp [evalWin, eL, list_pow_succ, list_pow_zero, list_pow_one,
            List.append_eq, ListBlank.append])
          (by rw [encodeBase, eL_bump2L]; simp [evalWin, ListBlank.append])
          rfl
      · subst h1
        exact chkWin_eq false false 7 1 true [1, 1, 0] [0] 0 true [1, 1, 1, 1] []
          (eL lp) (eW w) (fun hc => nomatch hc) (fun hc => nomatch hc)
          (by rw [encodeBase, hal]; simp [evalWin, eL, list_pow_succ, list_pow_zero, list_pow_one,
            List.append_eq, ListBlank.append])
          (by rw [encodeBase, eL_bump4L]; simp [evalWin, ListBlank.append])
          rfl
      · have ha2 : a = 2 := by omega
        subst ha2
        exact chkWin_eq false false 6 1 true [1, 1, 1, 0] [0] 1 false [0] [0, 1, 1, 0]
          (eL lp) (eW w) (fun hc => nomatch hc) (fun hc => nomatch hc)
          (by rw [encodeBase, hal]; simp [evalWin, eL, list_pow_succ, list_pow_zero, list_pow_one,
            List.append_eq, ListBlank.append])
          (by rw [encodeBase, ← evalWin_b0_flip]; simp [evalWin, eW, ListBlank.append])
          rfl
  cases l with
  | nil =>
      have ht := stepB0_tail [] rfl rfl
      simpa [stepB0, unconsL] using ht
  | cons t lp =>
      cases t with
      | M8 k =>
          dsimp only [stepB0]
          exact motifB0_sound k lp w
      | M06 k =>
          have ht := stepB0_tail (.M06 k :: lp) rfl rfl
          dsimp only [stepB0, unconsL] at ht ⊢
          exact ht
      | U a =>
          have ht := stepB0_tail (.U a :: lp) rfl rfl
          dsimp only [stepB0, unconsL] at ht ⊢
          split_ifs at ht ⊢ <;> exact ht

private theorem motifA0_body :
    checkWin false false 32 0 true [1] v10 0 true ([1] ++ u8Rot) [] = true := by
  decide +kernel

private theorem motifA0_sound (k : ℕ) (t : LTok) (lp : List LTok) (wRest : List WTok) :
    ReachesIn target_tm (32 * (k + 1))
      (encodeBase (.A0, t :: lp, .MW k :: wRest))
      (encodeBase (.A0, pushM8 k (t :: lp), wRest)) := by
  have hw := walkWordRight 32 0 true [1] u8Rot [] v10 motifA0_body (k + 1)
    (tailAfter1L t lp) (eW wRest)
  have hstart : encodeBase (.A0, t :: lp, .MW k :: wRest) =
      evalWin (tailAfter1L t lp) ((v10 ^ (k + 1)) +> eW wRest) 0 true [1] [] := by
    dsimp only [encodeBase, eW]
    rw [eL_cons_one t lp]
    simp [evalWin, ListBlank.append]
  have hend : encodeBase (.A0, pushM8 k (t :: lp), wRest) =
      evalWin ((u8Rot ^ (k + 1)) +> tailAfter1L t lp) (eW wRest) 0 true [1] [] := by
    dsimp only [encodeBase]
    rw [eL_pushM8, eL_cons_one t lp, ← u8Rot_pow_eq (k + 1) (tailAfter1L t lp)]
    simp [evalWin, ListBlank.append]
  rw [hstart, hend]
  exact hw

private theorem motifM06_body :
    checkWin false false 14 0 true [1, 1, 1, 1, 1, 0] ([0] ++ v10)
      0 true ([1, 1, 1, 1, 1, 0] ++ u06) [0] = true := by
  decide +kernel

private theorem motifM06_sound (k : ℕ) (lp : List LTok) (wRest : List WTok) :
    ReachesIn target_tm (14 * (k + 1))
      (encodeBase (.A0, .U 4 :: lp, .B false :: .MW k :: wRest))
      (encodeBase (.A0, .U 4 :: pushM06 k lp, .B false :: wRest)) := by
  have hw := walkWordRight 14 0 true [1, 1, 1, 1, 1, 0] u06 [0] v10 motifM06_body (k + 1)
    (eL lp) (eW wRest)
  have hstart : encodeBase (.A0, .U 4 :: lp, .B false :: .MW k :: wRest) =
      evalWin (eL lp) ((v10 ^ (k + 1)) +> eW wRest) 0 true [1, 1, 1, 1, 1, 0] [0] := by
    simp [encodeBase, evalWin, eL, eW, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq,
      ListBlank.append]
  have hend : encodeBase (.A0, .U 4 :: pushM06 k lp, .B false :: wRest) =
      evalWin ((u06 ^ (k + 1)) +> eL lp) (eW wRest) 0 true [1, 1, 1, 1, 1, 0] [0] := by
    dsimp only [encodeBase]
    rw [show eL (.U 4 :: pushM06 k lp) = [1, 1, 1, 1, 1, 0] +> eL (pushM06 k lp) by
      simp [eL, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, ListBlank.append]]
    rw [eL_pushM06]
    simp [evalWin, eW, ListBlank.append]
  rw [hstart, hend]
  exact hw

private theorem matchV10_eq {w wRest : List WTok} (h : matchV10 w = some wRest) :
    w = .B true :: .B false :: .B false :: .B true :: .B false ::
        .B false :: .B true :: .B true :: .B false :: .B false :: wRest := by
  unfold matchV10 at h
  split at h
  · injection h with h'; subst h'; rfl
  · nomatch h
private theorem stepMotifA0_sound (l : List LTok) (w : List WTok) (s' : BaseState) (c : ℕ)
    (hm : stepMotifA0? l w = some (s', c)) :
    ReachesIn target_tm c (encodeBase (.A0, l, w)) (encodeBase s') := by
  unfold stepMotifA0? at hm
  cases l with
  | nil => nomatch hm
  | cons t lp =>
      cases w with
      | nil => simp [matchV10] at hm
      | cons wt wRest =>
          cases wt with
          | MW k =>
              simp only [Option.some.injEq, Prod.mk.injEq] at hm
              obtain ⟨rfl, rfl⟩ := hm
              exact motifA0_sound k t lp wRest
          | T010 _ => simp [matchV10] at hm
          | B b0 =>
              cases b0 with
              | true =>
                  dsimp only at hm
                  rcases hv : matchV10 (.B true :: wRest) with _ | wRest'
                  · rw [hv] at hm; nomatch hm
                  · rw [hv] at hm
                    simp only [Option.some.injEq, Prod.mk.injEq] at hm
                    obtain ⟨rfl, rfl⟩ := hm
                    have heq := matchV10_eq hv
                    have henc : encodeBase (.A0, t :: lp, .B true :: wRest) =
                        encodeBase (.A0, t :: lp, .MW 0 :: wRest') := by
                      rw [heq]
                      dsimp only [encodeBase]
                      rw [eW_v10]
                      dsimp only [eW]
                      have hv1 : v10 ^ 1 = v10 := by
                        simp [list_pow_succ, list_pow_zero, list_pow_one, List.append_eq]
                      rw [hv1]
                    rw [henc]
                    exact motifA0_sound 0 t lp wRest'
              | false =>
                  cases wRest with
                  | nil => simp [matchV10] at hm
                  | cons wt2 wRest2 =>
                      cases wt2 with
                      | B _ => simp [matchV10] at hm
                      | T010 _ => simp [matchV10] at hm
                      | MW k =>
                          cases t with
                          | M8 _ => simp at hm
                          | M06 _ => simp at hm
                          | U a =>
                              dsimp only at hm
                              cases ha : (a == 4) with
                              | false => rw [ha] at hm; nomatch hm
                              | true =>
                                  rw [ha] at hm
                                  have ha4 : a = 4 := eq_of_beq ha
                                  subst ha4
                                  simp only [ite_true, Option.some.injEq, Prod.mk.injEq] at hm
                                  obtain ⟨rfl, rfl⟩ := hm
                                  exact motifM06_sound k lp wRest2

private theorem stepRight_sound (m : Mode)
    (hm : m = .A0 ∨ m = .E0 ∨ m = .F0 ∨ m = .F0z)
    (l : List LTok) (w : List WTok) :
    ReachesIn target_tm (stepRight m l w).2
      (encodeBase (m, l, w))
      (encodeBase (stepRight m l w).1) := by
  unfold stepRight
  rcases hw : unconsW w with _ | ⟨b, w1⟩
  · have hw0 := unconsW_none hw
    subst hw0
    rcases hm with rfl | rfl | rfl | rfl
    · dsimp only [stepRightNil]
      exact chkWin_eq false true 1 0 true [] [] 1 true [1] []
        (eL l) default (fun hc => nomatch hc) (fun _ => rfl)
        (by simp [encodeBase, eW])
        (by rw [encodeBase, eL_bump1L]; simp [evalWin, eW, ListBlank.append, zero_cons_def])
        rfl
    · dsimp only [stepRightNil]
      exact chkWin_eq false true 3 4 true [] [] 1 true [1, 1, 0] []
        (eL l) default (fun hc => nomatch hc) (fun _ => rfl)
        (by simp [encodeBase, eW])
        (by simp [encodeBase, evalWin, eL, eW, list_pow_succ, list_pow_zero, list_pow_one,
          List.append_eq, ListBlank.append, zero_cons_def])
        rfl
    · dsimp only [stepRightNil]
      exact chkWin_eq false true 2 5 true [] [] 1 true [1, 1] []
        (eL l) default (fun hc => nomatch hc) (fun _ => rfl)
        (by simp [encodeBase, eW])
        (by rw [encodeBase, eL_bump2L]; simp [evalWin, eW, ListBlank.append, zero_cons_def])
        rfl
    · dsimp only [stepRightNil]
      exact chkWin_eq false true 2 5 true [0] [] 1 true [1, 1, 0] []
        (eL l) default (fun hc => nomatch hc) (fun _ => rfl)
        (by simp [encodeBase, eW])
        (by simp [encodeBase, evalWin, eL, eW, list_pow_succ, list_pow_zero, list_pow_one,
          List.append_eq, ListBlank.append, zero_cons_def])
        rfl
  · have hew := unconsW_some hw
    cases b with
    | false =>
        rcases hm with rfl | rfl | rfl | rfl
        · dsimp only [stepRightZero]
          rcases hw1 : unconsW w1 with _ | ⟨b2, w2⟩
          · have hw10 := unconsW_none hw1
            subst hw10
            dsimp only
            exact chkWin_eq false true 1 0 true [] [0] 1 true [1] []
              (eL l) default (fun hc => nomatch hc) (fun _ => rfl)
              (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
              (by rw [encodeBase, eL_bump1L]; simp [evalWin, eW, ListBlank.append, zero_cons_def])
              rfl
          · have hew1 := unconsW_some hw1
            cases b2 with
            | false =>
                dsimp only
                exact chkWin_eq false false 1 0 true [] [0, 0] 1 true [1] [0]
                  (eL l) (eW w2) (fun hc => nomatch hc) (fun hc => nomatch hc)
                  (by rw [encodeBase, hew]; dsimp only [eW]; rw [hew1]; simp [evalWin, eW,
                    ListBlank.append])
                  (by rw [encodeBase, eL_bump1L]; simp [evalWin, ListBlank.append])
                  rfl
            | true =>
                dsimp only
                exact chkWin_eq false false 2 0 true [] [0, 1] 4 true [1, 1] []
                  (eL l) (eW w2) (fun hc => nomatch hc) (fun hc => nomatch hc)
                  (by rw [encodeBase, hew]; dsimp only [eW]; rw [hew1]; simp [evalWin, eW,
                    ListBlank.append])
                  (by rw [encodeBase, eL_bump2L]; simp [evalWin, ListBlank.append])
                  rfl
        · dsimp only [stepRightZero]
          exact chkWin_eq false false 1 4 true [] [0] 5 true [0] []
            (eL l) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
            (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
            (by simp [encodeBase, evalWin])
            rfl
        · dsimp only [stepRightZero]
          exact chkWin_eq false false 1 5 true [] [0] 0 true [1] []
            (eL l) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
            (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
            (by rw [encodeBase, eL_bump1L]; simp [evalWin, ListBlank.append])
            rfl
        · dsimp only [stepRightZero]
          exact chkWin_eq false false 1 5 true [0] [0] 0 true [1, 0] []
            (eL l) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
            (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
            (by simp [encodeBase, evalWin, eL, list_pow_succ, list_pow_zero, list_pow_one,
              List.append_eq, ListBlank.append])
            rfl
    | true =>
        rcases hm with rfl | rfl | rfl | rfl
        · dsimp only [stepRightOne]
          cases l with
          | nil =>
              dsimp only
              exact chkWin_eq true false 3 0 true [] [1] 1 false [0] [0]
                default (eW w1) (fun _ => rfl) (fun hc => nomatch hc)
                (by rw [encodeBase, hew]; simp [evalWin, eL, eW, ListBlank.append])
                (by rw [encodeBase, ← evalWin_b0_flip]; simp [evalWin, eL, eW, ListBlank.append])
                rfl
          | cons t lp =>
              dsimp only
              exact chkWin_eq false false 5 0 true [1] [1] 5 true [0, 1] []
                (tailAfter1L t lp) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
                (by rw [encodeBase, eL_cons_one t lp, hew]; simp [evalWin, eW, ListBlank.append])
                (by rw [encodeBase, eL_cons_one t lp]; simp [evalWin, ListBlank.append])
                rfl
        · dsimp only [stepRightOne]
          exact chkWin_eq false false 1 4 true [] [1] 5 true [1] []
            (eL l) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
            (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
            (by rw [encodeBase, eL_bump1L]; simp [evalWin, ListBlank.append])
            rfl
        · dsimp only [stepRightOne]
          cases l with
          | nil =>
              dsimp only
              exact chkWin_eq true false 1 5 true [] [1] 1 false [] [0]
                default (eW w1) (fun _ => rfl) (fun hc => nomatch hc)
                (by rw [encodeBase, hew]; simp [evalWin, eL, eW, ListBlank.append])
                (by rw [encodeBase, eL, eW, ← evalWin_b0_def])
                rfl
          | cons t lp =>
              dsimp only
              exact chkWin_eq false false 3 5 true [1] [1] 5 true [0, 1] []
                (tailAfter1L t lp) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
                (by rw [encodeBase, eL_cons_one t lp, hew]; simp [evalWin, eW, ListBlank.append])
                (by rw [encodeBase, eL_cons_one t lp]; simp [evalWin, ListBlank.append])
                rfl
        · dsimp only [stepRightOne]
          exact chkWin_eq false false 1 5 true [0] [1] 1 false [0] [0]
            (eL l) (eW w1) (fun hc => nomatch hc) (fun hc => nomatch hc)
            (by rw [encodeBase, hew]; simp [evalWin, eW, ListBlank.append])
            (by rw [encodeBase, ← evalWin_b0_flip]; simp [evalWin, eW, ListBlank.append])
            rfl

private theorem stepSys_sound :
    ∀ (s s' : BaseState) (c : ℕ), stepSys s = some (s', c) →
      ReachesIn target_tm c (encodeBase s) (encodeBase s') := by
  rintro ⟨m, l, w⟩ s' c h
  cases m with
  | Halt => nomatch h
  | Init0 =>
      simp only [stepSys, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact chkWin_eq true true 1 0 true [] [] 1 true [1] []
        default default (fun _ => rfl) (fun _ => rfl)
        (by rfl)
        (by simp [encodeBase, evalWin, eL, eW, list_pow_succ, list_pow_zero, list_pow_one,
          List.append_eq, ListBlank.append, zero_cons_def])
        rfl
  | B0 =>
      simp only [stepSys, Option.some.injEq] at h
      have hs := stepB0_sound l w
      rw [h] at hs; exact hs
  | A0 =>
      dsimp only [stepSys] at h
      rcases hm : stepMotifA0? l w with _ | res
      · rw [hm] at h
        simp only [Option.some.injEq] at h
        have hs := stepRight_sound .A0 (Or.inl rfl) l w
        rw [h] at hs; exact hs
      · rw [hm] at h
        injection h with hres
        subst hres
        exact stepMotifA0_sound l w s' c hm
  | E0 =>
      simp only [stepSys, Option.some.injEq] at h
      have hs := stepRight_sound .E0 (Or.inr (Or.inl rfl)) l w
      rw [h] at hs; exact hs
  | F0 =>
      simp only [stepSys, Option.some.injEq] at h
      have hs := stepRight_sound .F0 (Or.inr (Or.inr (Or.inl rfl))) l w
      rw [h] at hs; exact hs
  | F0z =>
      simp only [stepSys, Option.some.injEq] at h
      have hs := stepRight_sound .F0z (Or.inr (Or.inr (Or.inr rfl))) l w
      rw [h] at hs; exact hs
/-! ### Multi-Layer Base-8/3 Self-Similar Odometer Accelerator (`stepOdom?`) -/

inductive Sep
  | S0
  | S1
  | S2
  | S3
  | S4
  | S5
  | S6
  | S7

def sepToks : Sep → List LTok
  | .S0 => [.U 0, .U 2, .U 0, .U 2]
  | .S1 => [.U 0, .U 6, .U 2]
  | .S2 => [.U 14, .U 2]
  | .S3 => [.U 10, .U 6]
  | .S4 => [.U 0, .U 12]
  | .S5 => [.U 10, .U 0, .U 2]
  | .S6 => [.U 0, .U 2, .U 6]
  | .S7 => [.U 20]

def qPol : Sep → Bool
  | .S0 | .S1 | .S2 | .S5 => true
  | .S3 | .S4 | .S6 | .S7 => false

def parse8 : List LTok → ℕ × List LTok
  | .M8 m :: rest =>
      let (c, rem) := parse8 rest
      (m + 1 + c, rem)
  | .U a :: rest =>
      if a == 8 then
        let (c, rem) := parse8 rest
        (1 + c, rem)
      else (0, .U a :: rest)
  | xs => (0, xs)

def parseSep : List LTok → Option (Sep × List LTok)
  | .U a :: rest1 =>
      if a == 20 then some (.S7, rest1)
      else if a == 14 then
        match rest1 with
        | .U b :: rest2 => if b == 2 then some (.S2, rest2) else none
        | _ => none
      else if a == 10 then
        match rest1 with
        | .U b :: rest2 =>
            if b == 6 then some (.S3, rest2)
            else if b == 0 then
              match rest2 with
              | .U c :: rest3 => if c == 2 then some (.S5, rest3) else none
              | _ => none
            else none
        | _ => none
      else if a == 0 then
        match rest1 with
        | .U b :: rest2 =>
            if b == 12 then some (.S4, rest2)
            else if b == 6 then
              match rest2 with
              | .U c :: rest3 => if c == 2 then some (.S1, rest3) else none
              | _ => none
            else if b == 2 then
              match rest2 with
              | .U c :: rest3 =>
                  if c == 6 then some (.S6, rest3)
                  else if c == 0 then
                    match rest3 with
                    | .U d :: rest4 => if d == 2 then some (.S0, rest4) else none
                    | _ => none
                  else none
              | _ => none
            else none
        | _ => none
      else none
  | _ => none

def parseLayersAux : ℕ → List LTok → List (ℕ × Sep) × List LTok
  | 0, cur => ([], cur)
  | fuel + 1, cur =>
      match parse8 cur with
      | (0, _) => ([], cur)
      | (km1 + 1, rem) =>
          match parseSep rem with
          | none => ([], cur)
          | some (j, afterSep) =>
              let (more, tail) := parseLayersAux fuel afterSep
              ((km1, j) :: more, tail)

def parseLayers (l : List LTok) : List (ℕ × Sep) × List LTok :=
  parseLayersAux l.length l

def encLayers : List (ℕ × Sep) → List LTok → List LTok
  | [], tail => tail
  | (km1, j) :: rest, tail => .M8 km1 :: (sepToks j ++ encLayers rest tail)

def pick6 (r0 r1 r2 r3 r4 r5 rc : ℕ) : ℕ :=
  if rc == 0 then r0
  else if rc == 1 then r1
  else if rc == 2 then r2
  else if rc == 3 then r3
  else if rc == 4 then r4
  else r5

def maxR (p0 : Bool) (j0 : Sep) (rc : ℕ) : ℕ :=
  match p0, j0 with
  | false, .S0 | false, .S6 => pick6 2 5 7 10 13 15 rc
  | false, .S1 | false, .S4 => pick6 1 3 6 9 11 14 rc
  | false, .S2 | false, .S7 => pick6 0 3 5 8 11 13 rc
  | false, .S3 | false, .S5 => pick6 1 4 7 9 12 15 rc
  | true, .S0 | true, .S6 => pick6 2 4 7 10 12 15 rc
  | true, .S1 | true, .S4 => pick6 0 3 6 8 11 14 rc
  | true, .S2 | true, .S7 => pick6 0 2 5 8 10 13 rc
  | true, .S3 | true, .S5 => pick6 1 4 6 9 12 14 rc

def maxCarries : Bool → List (ℕ × Sep) → ℕ
  | _, [] => 0
  | p0, (_, j0) :: rest =>
      let c := maxCarries (qPol j0) rest
      16 * (c / 6) + maxR p0 j0 (c % 6)

def step1Carry (isTop : Bool) (p : Bool) (km1 : ℕ) (j : Sep) : ℕ × Sep × Option Bool × ℕ :=
  match p, j with
  | false, .S0 => (km1, .S5, none, 56 * km1 + (if isTop then 144 else 175))
  | false, .S1 => (km1, .S2, none, 56 * km1 + (if isTop then 144 else 175))
  | false, .S2 => (km1 + 1, .S6, some true, 56 * km1 + (if isTop then 137 else 168))
  | false, .S3 => (km1 + 1, .S4, none, 56 * km1 + (if isTop then 184 else 215))
  | false, .S4 => (km1, .S7, none, 56 * km1 + (if isTop then 144 else 175))
  | false, .S5 => (km1 + 1, .S1, none, 56 * km1 + (if isTop then 184 else 215))
  | false, .S6 => (km1, .S3, none, 56 * km1 + (if isTop then 144 else 175))
  | false, .S7 => (km1 + 1, .S0, some false, 56 * km1 + (if isTop then 137 else 168))
  | true, .S0 => (km1, .S1, none, 112 * km1 + (if isTop then 240 else 271))
  | true, .S1 => (km1, .S6, some true, 112 * km1 + (if isTop then 193 else 224))
  | true, .S2 => (km1, .S3, some true, 112 * km1 + (if isTop then 249 else 280))
  | true, .S3 => (km1, .S7, none, 112 * km1 + (if isTop then 296 else 327))
  | true, .S4 => (km1, .S0, some false, 112 * km1 + (if isTop then 193 else 224))
  | true, .S5 => (km1, .S2, none, 112 * km1 + (if isTop then 296 else 327))
  | true, .S6 => (km1, .S4, none, 112 * km1 + (if isTop then 240 else 271))
  | true, .S7 => (km1, .S5, some false, 112 * km1 + (if isTop then 249 else 280))

def iterCarryAux (isTop : Bool) : ℕ → Bool → Bool → ℕ → Sep → Option (ℕ × Sep × ℕ × ℕ)
  | 0, _, _, km1, j => some (km1, j, 0, 0)
  | r + 1, p, qCur, km1, j =>
      let (km1_1, j_1, em, c1) := step1Carry isTop p km1 j
      match em with
      | none =>
          match iterCarryAux isTop r (!p) qCur km1_1 j_1 with
          | none => none
          | some (km1_2, j_2, nEm, c2) => some (km1_2, j_2, nEm, c1 + c2)
      | some b =>
          if b == qCur then
            match iterCarryAux isTop r (!p) (!qCur) km1_1 j_1 with
            | none => none
            | some (km1_2, j_2, nEm, c2) => some (km1_2, j_2, nEm + 1, c1 + c2)
          else none

def b16 (isTop : Bool) (p0 : Bool) (j0 : Sep) : ℕ :=
  match isTop, p0, j0 with
  | false, false, .S0 | false, false, .S1 | false, false, .S4 | false, false, .S6 => 6134
  | false, false, _ => 6806
  | false, true, .S0 | false, true, .S1 | false, true, .S4 | false, true, .S6 => 5686
  | false, true, _ => 6358
  | true, false, .S0 | true, false, .S1 | true, false, .S4 | true, false, .S6 => 5638
  | true, false, _ => 6310
  | true, true, .S0 | true, true, .S1 | true, true, .S4 | true, true, .S6 => 5190
  | true, true, _ => 5862

def qCyclesCost (isTop : Bool) (p0 : Bool) (j0 : Sep) (km1 : ℕ) : ℕ → ℕ
  | 0 => 0
  | q' + 1 =>
      let q := q' + 1
      q * (1344 * km1 + b16 isTop p0 j0) + 2688 * q * q'

def fastCarries (isTop : Bool) (p0 : Bool) (C : ℕ) :
    List (ℕ × Sep) → Option (List (ℕ × Sep) × ℕ)
  | [] => if C == 0 then some ([], 0) else none
  | (km1, j0) :: rest =>
      if C == 0 then some ((km1, j0) :: rest, 0)
      else
        let q := C / 16
        let r := C % 16
        let costQ := qCyclesCost isTop p0 j0 km1 q
        match iterCarryAux isTop r p0 (qPol j0) (km1 + 4 * q) j0 with
        | none => none
        | some (km1Out, jOut, rEmit, costR) =>
            match fastCarries false (qPol j0) (6 * q + rEmit) rest with
            | none => none
            | some (restOut, childCost) =>
                some ((km1Out, jOut) :: restOut, costQ + costR + childCost)

def topHead : Bool → List LTok
  | false => [.U 11]
  | true => [.U 5, .U 2]

def parityXor (p : Bool) (n : ℕ) : Bool :=
  if n % 2 == 1 then !p else p

def matchTopHead : List LTok → Option (Bool × List LTok)
  | .U a :: rest =>
      if a == 11 then some (false, rest)
      else if a == 5 then
        match rest with
        | .U b :: rest2 => if b == 2 then some (true, rest2) else none
        | _ => none
      else none
  | _ => none

def stepOdom? : BaseState → Option (BaseState × ℕ)
  | (.B0, l, []) =>
      match matchTopHead l with
      | none => none
      | some (p0, rest) =>
          let (layers, tail) := parseLayers rest
          let cap := maxCarries p0 layers
          if 1 ≤ cap then
            match fastCarries true p0 cap layers with
            | none => none
            | some (layers', c) =>
                some ((.B0, topHead (parityXor p0 cap) ++ encLayers layers' tail, []), c)
          else none
  | _ => none

def masterStep (bs : BaseState) : Option (BaseState × ℕ) :=
  match stepOdom? bs with
  | some res => some res
  | none => stepSys bs
private def uBits : List ℕ → List (Fin 2)
  | [] => []
  | a :: rest => (([1] : List (Fin 2)) ^ (a + 1)) ++ (0 :: uBits rest)

private def sepBits : Sep → List (Fin 2)
  | .S0 => uBits [0, 2, 0, 2]
  | .S1 => uBits [0, 6, 2]
  | .S2 => uBits [14, 2]
  | .S3 => uBits [10, 6]
  | .S4 => uBits [0, 12]
  | .S5 => uBits [10, 0, 2]
  | .S6 => uBits [0, 2, 6]
  | .S7 => uBits [20]

private def topBits : Bool → List (Fin 2)
  | false => uBits [11]
  | true => uBits [5, 2]

private def layerBits (km1 : ℕ) (j : Sep) (sNext : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  (u8 ^ (km1 + 1)) +> (sepBits j +> sNext)

private def layersBits : List (ℕ × Sep) → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], sTail => sTail
  | (km1, j) :: rest, sTail => layerBits km1 j (layersBits rest sTail)

private theorem uBits_cons2 (a b : ℕ) (rest : List ℕ) (s : ListBlank (Fin 2)) :
    uBits (a :: b :: rest) +> s = uBits [a] +> (uBits (b :: rest) +> s) := by
  simp only [uBits, app_assoc, ListBlank.append]

private theorem uBits_eight : uBits [8] = u8 := by decide

private theorem eL_u (a : ℕ) (xs : List LTok) :
    eL (.U a :: xs) = uBits [a] +> eL xs := by
  simp only [eL, uBits, app_assoc, ListBlank.append]

private theorem eL_sepToks (j : Sep) (xs : List LTok) :
    eL (sepToks j ++ xs) = sepBits j +> eL xs := by
  cases j <;>
    simp only [sepToks, sepBits, List.cons_append, List.nil_append, eL_u, uBits_cons2]

private theorem eL_topHead (p : Bool) (xs : List LTok) :
    eL (topHead p ++ xs) = topBits p +> eL xs := by
  cases p <;>
    simp only [topHead, topBits, List.cons_append, List.nil_append, eL_u, uBits_cons2]

private theorem eL_encLayers :
    ∀ (layers : List (ℕ × Sep)) (tail : List LTok),
      eL (encLayers layers tail) = layersBits layers (eL tail)
  | [], _ => rfl
  | (km1, j) :: rest, tail => by
      dsimp only [encLayers, eL, layersBits, layerBits]
      rw [eL_sepToks, eL_encLayers rest tail]

private theorem eL_parse8 :
    ∀ (l : List LTok), eL l = (u8 ^ (parse8 l).1) +> eL (parse8 l).2
  | [] => by simp [parse8, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | .M06 m :: rest => by simp [parse8, list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
  | .M8 m :: rest => by
      dsimp only [parse8, eL]
      rw [eL_parse8 rest, ← app_assoc (u8 ^ (m + 1)) (u8 ^ (parse8 rest).1), ← pow_add_list]
  | .U a :: rest => by
      dsimp only [parse8]
      cases ha : (a == 8) with
      | false => simp [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append]
      | true =>
          have ha8 : a = 8 := eq_of_beq ha
          subst ha8
          rw [(ite_eq_left_of_eq_true _ _ (eq_true rfl)), eL_u8, eL_parse8 rest]
          dsimp only
          rw [← app_assoc u8 (u8 ^ (parse8 rest).1), ← pow_succ_left u8 (parse8 rest).1,
              Nat.add_comm (parse8 rest).1 1]

private theorem parseSep_eq {l afterSep : List LTok} {j : Sep}
    (h : parseSep l = some (j, afterSep)) :
    l = sepToks j ++ afterSep := by
  unfold parseSep at h
  cases l with
  | nil => nomatch h
  | cons t1 r1 =>
      cases t1 with
      | M8 _ => nomatch h
      | M06 _ => nomatch h
      | U a =>
          dsimp only at h
          split_ifs at h with ha20 ha14 ha10 ha0
          · rw [eq_of_beq ha20]; injection h with hp; injection hp with hj hr; subst hj hr; rfl
          · cases r1 with
            | nil => nomatch h
            | cons t2 r2 =>
                cases t2 with
                | M8 _ => nomatch h
                | M06 _ => nomatch h
                | U b =>
                    dsimp only at h
                    split_ifs at h with hb2
                    rw [eq_of_beq ha14, eq_of_beq hb2]
                    injection h with hp; injection hp with hj hr; subst hj hr; rfl
          · cases r1 with
            | nil => nomatch h
            | cons t2 r2 =>
                cases t2 with
                | M8 _ => nomatch h
                | M06 _ => nomatch h
                | U b =>
                    dsimp only at h
                    split_ifs at h with hb6 hb0
                    · rw [eq_of_beq ha10, eq_of_beq hb6]
                      injection h with hp; injection hp with hj hr; subst hj hr; rfl
                    · cases r2 with
                      | nil => nomatch h
                      | cons t3 r3 =>
                          cases t3 with
                          | M8 _ => nomatch h
                          | M06 _ => nomatch h
                          | U c =>
                              dsimp only at h
                              split_ifs at h with hc2
                              rw [eq_of_beq ha10, eq_of_beq hb0, eq_of_beq hc2]
                              injection h with hp; injection hp with hj hr; subst hj hr; rfl
          · cases r1 with
            | nil => nomatch h
            | cons t2 r2 =>
                cases t2 with
                | M8 _ => nomatch h
                | M06 _ => nomatch h
                | U b =>
                    dsimp only at h
                    split_ifs at h with hb12 hb6 hb2
                    · rw [eq_of_beq ha0, eq_of_beq hb12]
                      injection h with hp; injection hp with hj hr; subst hj hr; rfl
                    · cases r2 with
                      | nil => nomatch h
                      | cons t3 r3 =>
                          cases t3 with
                          | M8 _ => nomatch h
                          | M06 _ => nomatch h
                          | U c =>
                              dsimp only at h
                              split_ifs at h with hc2
                              rw [eq_of_beq ha0, eq_of_beq hb6, eq_of_beq hc2]
                              injection h with hp; injection hp with hj hr; subst hj hr; rfl
                    · cases r2 with
                      | nil => nomatch h
                      | cons t3 r3 =>
                          cases t3 with
                          | M8 _ => nomatch h
                          | M06 _ => nomatch h
                          | U c =>
                              dsimp only at h
                              split_ifs at h with hc6 hc0
                              · rw [eq_of_beq ha0, eq_of_beq hb2, eq_of_beq hc6]
                                injection h with hp; injection hp with hj hr; subst hj hr; rfl
                              · cases r3 with
                                | nil => nomatch h
                                | cons t4 r4 =>
                                    cases t4 with
                                    | M8 _ => nomatch h
                                    | M06 _ => nomatch h
                                    | U d =>
                                        dsimp only at h
                                        split_ifs at h with hd2
                                        rw [eq_of_beq ha0, eq_of_beq hb2, eq_of_beq hc0,
                                          eq_of_beq hd2]
                                        injection h with hp; injection hp with hj hr; subst hj hr;
                                          rfl

private theorem eL_parseLayersAux :
    ∀ (fuel : ℕ) (cur : List LTok),
      eL cur = layersBits (parseLayersAux fuel cur).1 (eL (parseLayersAux fuel cur).2)
  | 0, _ => rfl
  | fuel + 1, cur => by
      unfold parseLayersAux
      rcases hp8 : parse8 cur with ⟨c, rem⟩
      cases c with
      | zero => rfl
      | succ km1 =>
          dsimp only
          rcases hps : parseSep rem with _ | ⟨j, afterSep⟩
          · rfl
          · dsimp only [layersBits, layerBits]
            have hcur := eL_parse8 cur
            rw [hp8] at hcur
            dsimp only at hcur
            rw [hcur, parseSep_eq hps, eL_sepToks, eL_parseLayersAux fuel afterSep]

private theorem eL_parseLayers (l : List LTok) :
    eL l = layersBits (parseLayers l).1 (eL (parseLayers l).2) :=
  eL_parseLayersAux l.length l
private def UnitStepB (c : ℕ) (sL sL' : ListBlank (Fin 2)) : Prop :=
  ∀ sW : ListBlank (Fin 2),
    (evalWin sL sW 1 false [0] []) [target_tm]⊢^{c} (evalWin sL' sW 5 true [0] [])

private theorem evalWin_b0_pfx (pfx : List (Fin 2)) (sL sW : ListBlank (Fin 2)) :
    evalWin (pfx +> sL) sW 1 false [0] [] = evalWin sL sW 1 true pfx [0] := by
  simp [evalWin, ListBlank.append]

private theorem evalWin_f0z_pfx (pfx : List (Fin 2)) (sL sW : ListBlank (Fin 2)) :
    evalWin (pfx +> sL) sW 5 true [0] [] = evalWin sL sW 5 true (0 :: pfx) [] := by
  simp [evalWin, ListBlank.append]

private theorem unit_S0 (s : ListBlank (Fin 2)) :
    UnitStepB 7 (sepBits .S0 +> s) (uBits [4] +> (uBits [0, 2] +> s)) := by
  intro sW
  rw [← uBits_cons2 4 0 [2] s]
  exact chkWin_eq false false 7 1 true (sepBits .S0) [0] 5 true (0 :: uBits [4, 0, 2]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem unit_S1 (s : ListBlank (Fin 2)) :
    UnitStepB 7 (sepBits .S1 +> s) (uBits [8] +> (uBits [2] +> s)) := by
  intro sW
  rw [← uBits_cons2 8 2 [] s]
  exact chkWin_eq false false 7 1 true (sepBits .S1) [0] 5 true (0 :: uBits [8, 2]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem unit_S3 (s : ListBlank (Fin 2)) :
    UnitStepB 47 (sepBits .S3 +> s) (uBits [2] +> (sepBits .S4 +> s)) := by
  intro sW
  have hout : uBits [2] +> (sepBits .S4 +> s) = uBits [2, 0, 12] +> s := by
    dsimp only [sepBits]; rw [← uBits_cons2 2 0 [12] s]
  rw [hout]
  exact chkWin_eq false false 47 1 true (sepBits .S3) [0] 5 true (0 :: uBits [2, 0, 12]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem unit_S4 (s : ListBlank (Fin 2)) :
    UnitStepB 7 (sepBits .S4 +> s) (uBits [14] +> s) := by
  intro sW
  exact chkWin_eq false false 7 1 true (sepBits .S4) [0] 5 true (0 :: uBits [14]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem unit_S5 (s : ListBlank (Fin 2)) :
    UnitStepB 47 (sepBits .S5 +> s) (uBits [2] +> (sepBits .S1 +> s)) := by
  intro sW
  have hout : uBits [2] +> (sepBits .S1 +> s) = uBits [2, 0, 6, 2] +> s := by
    dsimp only [sepBits]; rw [← uBits_cons2 2 0 [6, 2] s]
  rw [hout]
  exact chkWin_eq false false 47 1 true (sepBits .S5) [0] 5 true (0 :: uBits [2, 0, 6, 2]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem unit_S6 (s : ListBlank (Fin 2)) :
    UnitStepB 7 (sepBits .S6 +> s) (uBits [4] +> (uBits [6] +> s)) := by
  intro sW
  rw [← uBits_cons2 4 6 [] s]
  exact chkWin_eq false false 7 1 true (sepBits .S6) [0] 5 true (0 :: uBits [4, 6]) []
    s sW (fun hc => nomatch hc) (fun hc => nomatch hc)
    (evalWin_b0_pfx _ s sW) (evalWin_f0z_pfx _ s sW) (by decide +kernel)

private theorem m8_entry_body :
    checkWin false false 23 5 true [0, 1] wPref5 0 true [1, 1, 1, 1, 1, 1, 1] [] = true := by
  decide +kernel

private theorem m8_exit_body :
    checkWin false false 9 0 true [1] wSuff5 5 true [0, 1, 1, 1, 0, 1] [] = true := by
  decide +kernel

private theorem unitStep_m8 {c a : ℕ} {sX sY : ListBlank (Fin 2)}
    (hX : UnitStepB c sX (uBits [a] +> sY)) (km1 : ℕ) :
    UnitStepB (56 * (km1 + 1) + c)
      ((u8 ^ (km1 + 1)) +> sX)
      (uBits [2] +> ((u8 ^ km1) +> (uBits [a + 6] +> sY))) := by
  intro sW
  let sYa : ListBlank (Fin 2) := ((([1] : List (Fin 2)) ^ a) ++ [0]) +> sY
  let s6 : ListBlank (Fin 2) := [1, 1, 1, 1, 1, 1] +> sYa
  have hu_a : uBits [a] +> sY = [1] +> sYa := by
    dsimp only [uBits, sYa]
    rw [pow_succ_left ([1] : List (Fin 2)) a, List.append_assoc, app_assoc]
  have hu_a6 : [1] +> s6 = uBits [a + 6] +> sY := by
    dsimp only [s6, sYa, uBits]
    have h7 : ([1, 1, 1, 1, 1, 1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 7 := by decide
    have hsplit : [1] +> ([1, 1, 1, 1, 1, 1] +> (((([1] : List (Fin 2)) ^ a) ++ [0]) +> sY)) =
        ((([1] : List (Fin 2)) ^ 7 ++ ([1] : List (Fin 2)) ^ a) ++ [0]) +> sY := by
      rw [← h7]
      simp only [List.cons_append, List.nil_append, ListBlank.append, app_assoc]
    rw [hsplit, ← pow_add_list ([1] : List (Fin 2)) 7 a, show 7 + a = a + 6 + 1 by omega]
  have h1 := walkWordLeft 24 1 false [0] u8 [] w24 motifB0_body (km1 + 1) sX sW
  have h2 := hX ((w24 ^ (km1 + 1)) +> sW)
  have h3 : (evalWin (uBits [a] +> sY) ((w24 ^ (km1 + 1)) +> sW) 5 true [0] []) [target_tm]⊢^{23}
      (evalWin s6 ((v10 ^ km1) +> (wSuff5 +> sW)) 0 true [1] []) :=
    chkWin_eq false false 23 5 true [0, 1] wPref5 0 true [1, 1, 1, 1, 1, 1, 1] []
      sYa ((v10 ^ km1) +> (wSuff5 +> sW))
      (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by rw [hu_a, w24_pow_eq km1 sW]; simp [evalWin, ListBlank.append])
      (by simp [evalWin, s6, ListBlank.append])
      m8_entry_body
  have h4 := walkWordRight 32 0 true [1] u8Rot [] v10 motifA0_body km1 s6 (wSuff5 +> sW)
  have h5 : (evalWin ((u8Rot ^ km1) +> s6) (wSuff5 +> sW) 0 true [1] []) [target_tm]⊢^{9}
      (evalWin (uBits [2] +> ((u8 ^ km1) +> (uBits [a + 6] +> sY))) sW 5 true [0] []) :=
    chkWin_eq false false 9 0 true [1] wSuff5 5 true [0, 1, 1, 1, 0, 1] []
      ((u8Rot ^ km1) +> s6) sW
      (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin])
      (by
        have hlt : [0, 1, 1, 1, 0, 1] +> ((u8Rot ^ km1) +> s6) =
            [0] +> (uBits [2] +> ([1] +> ((u8Rot ^ km1) +> s6))) := by
          simp [uBits, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, ListBlank.append]
        rw [evalWin, (ite_eq_left_of_eq_true _ _ (eq_true rfl)), evalWin, (ite_eq_left_of_eq_true
          _ _ (eq_true rfl)), hlt, u8Rot_pow_eq km1 s6, hu_a6])
      m8_exit_body
  have h12 := ms_trans h1 h2
  have h123 := ms_trans h12 h3
  have h1234 := ms_trans h123 h4
  have h12345 := ms_trans h1234 h5
  rw [show 24 * (km1 + 1) + c + 23 + 32 * km1 + 9 = 56 * (km1 + 1) + c by omega] at h12345
  exact h12345
private def CarrySem : Bool → Bool → ℕ → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | false, false, c, sL, sL' =>
      UnitStepB c (sepBits .S7 +> sL) (uBits [2] +> (sepBits .S0 +> sL'))
  | false, true, c, sL, sL' =>
      UnitStepB c (sepBits .S2 +> sL) (uBits [2] +> (sepBits .S6 +> sL'))
  | true, false, c, sL, sL' =>
      (evalWin (topBits false +> sL) default 1 true [] [0]) [target_tm]⊢^{c}
        (evalWin (topBits true +> sL') default 1 true [] [0])
  | true, true, c, sL, sL' =>
      (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{c}
        (evalWin (topBits false +> sL') default 1 true [] [0])

private def w0110 : List (Fin 2) := [0, 1, 1, 0]
private def w_s7 : List (Fin 2) := w0110 ++ t010 ++ t010 ++ t010 ++ t010 ++ t010 ++ t010
private def w_s2 : List (Fin 2) := w0110 ++ w0110 ++ t010 ++ t010 ++ t010 ++ t010
private def w_s2_rem : List (Fin 2) := [0, 0] ++ t010 ++ t010 ++ t010 ++ t010
private def w_top0 : List (Fin 2) := w0110 ++ t010 ++ t010 ++ t010
private def w_top1 : List (Fin 2) := w0110 ++ w0110 ++ t010
private def w_top1_rem : List (Fin 2) := [0, 0] ++ t010

private theorem wrap_S7 {c1 : ℕ} {sL sR : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR)) :
    CarrySem false false (c1 + 112) sL (u8 +> sR) := by
  intro sW
  have ha : (evalWin (sepBits .S7 +> sL) sW 1 false [0] []) [target_tm]⊢^{60}
      (evalWin sL (w_s7 +> sW) 1 false [0] []) :=
    chkWin_eq false false 60 1 true (sepBits .S7) [0] 1 false [0] w_s7
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_s7 +> sW)
  have hc : (evalWin (uBits [2] +> sR) (w_s7 +> sW) 5 true [0] []) [target_tm]⊢^{52}
      (evalWin (uBits [2] +> (sepBits .S0 +> (u8 +> sR))) sW 5 true [0] []) :=
    chkWin_eq false false 52 5 true (0 :: uBits [2]) w_s7
      5 true (0 :: (uBits [2] ++ (sepBits .S0 ++ u8))) []
      sR sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append, app_assoc])
      (by decide +kernel)
  have habc := ms_trans (ms_trans ha hb) hc
  rw [show 60 + c1 + 52 = c1 + 112 by omega] at habc
  exact habc

private theorem wrap_Top0 {c1 : ℕ} {sL sR : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR)) :
    CarrySem true false (c1 + 81) sL (u8 +> sR) := by
  have ha : (evalWin (topBits false +> sL) default 1 true [] [0]) [target_tm]⊢^{33}
      (evalWin sL (w_top0 +> default) 1 false [0] []) :=
    chkWin_eq false false 33 1 true (topBits false) [0] 1 false [0] w_top0
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_top0 +> default)
  have hc : (evalWin (uBits [2] +> sR) (w_top0 +> default) 5 true [0] []) [target_tm]⊢^{48}
      (evalWin (topBits true +> (u8 +> sR)) default 1 true [] [0]) :=
    chkWin_eq false true 48 5 true (0 :: uBits [2]) w_top0
      1 true (topBits true ++ u8) []
      sR default (fun hc => nomatch hc) (fun _ => rfl)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, app_assoc, ListBlank.append, zero_cons_def])
      (by decide +kernel)
  have habc := ms_trans (ms_trans ha hb) hc
  rw [show 33 + c1 + 48 = c1 + 81 by omega] at habc
  exact habc

private theorem mkCarry0 (isTop : Bool) {c1 : ℕ} {sL sR : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR)) :
    CarrySem isTop false (c1 + if isTop then 81 else 112) sL (u8 +> sR) := by
  cases isTop
  · exact wrap_S7 h1
  · exact wrap_Top0 h1

private theorem wrap_S2 {c1 c2 : ℕ} {sL sR1 sR2 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitStepB c2 (u8 +> sR1) (uBits [2] +> sR2)) :
    CarrySem false true (c1 + c2 + 105) sL sR2 := by
  intro sW
  have ha : (evalWin (sepBits .S2 +> sL) sW 1 false [0] []) [target_tm]⊢^{48}
      (evalWin sL (w_s2 +> sW) 1 false [0] []) :=
    chkWin_eq false false 48 1 true (sepBits .S2) [0] 1 false [0] w_s2
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_s2 +> sW)
  have hc : (evalWin (uBits [2] +> sR1) (w_s2 +> sW) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_s2_rem +> sW) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_s2 1 false (0 :: u8) w_s2_rem
      sR1 sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  have hd := h2 (w_s2_rem +> sW)
  have he : (evalWin (uBits [2] +> sR2) (w_s2_rem +> sW) 5 true [0] []) [target_tm]⊢^{28}
      (evalWin (uBits [2] +> (sepBits .S6 +> sR2)) sW 5 true [0] []) :=
    chkWin_eq false false 28 5 true (0 :: uBits [2]) w_s2_rem
      5 true (0 :: (uBits [2] ++ sepBits .S6)) []
      sR2 sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append, app_assoc])
      (by decide +kernel)
  have hall := ms_trans (ms_trans (ms_trans (ms_trans ha hb) hc) hd) he
  rw [show 48 + c1 + 29 + c2 + 28 = c1 + c2 + 105 by omega] at hall
  exact hall

private theorem wrap_Top1 {c1 c2 : ℕ} {sL sR1 sR2 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitStepB c2 (u8 +> sR1) (uBits [2] +> sR2)) :
    CarrySem true true (c1 + c2 + 74) sL sR2 := by
  have ha : (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{21}
      (evalWin sL (w_top1 +> default) 1 false [0] []) :=
    chkWin_eq false false 21 1 true (topBits true) [0] 1 false [0] w_top1
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_top1 +> default)
  have hc : (evalWin (uBits [2] +> sR1) (w_top1 +> default) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_top1_rem +> default) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_top1 1 false (0 :: u8) w_top1_rem
      sR1 default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  have hd := h2 (w_top1_rem +> default)
  have he : (evalWin (uBits [2] +> sR2) (w_top1_rem +> default) 5 true [0] []) [target_tm]⊢^{24}
      (evalWin (topBits false +> sR2) default 1 true [] [0]) :=
    chkWin_eq false true 24 5 true (0 :: uBits [2]) w_top1_rem
      1 true (topBits false) []
      sR2 default (fun hc => nomatch hc) (fun _ => rfl)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append, zero_cons_def])
      (by decide +kernel)
  have hall := ms_trans (ms_trans (ms_trans (ms_trans ha hb) hc) hd) he
  rw [show 21 + c1 + 29 + c2 + 24 = c1 + c2 + 74 by omega] at hall
  exact hall

private theorem mkCarry1 (isTop : Bool) {c1 c2 : ℕ} {sL sR1 sR2 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitStepB c2 (u8 +> sR1) (uBits [2] +> sR2)) :
    CarrySem isTop true (c1 + c2 + if isTop then 74 else 105) sL sR2 := by
  cases isTop
  · exact wrap_S2 h1 h2
  · exact wrap_Top1 h1 h2
private theorem u8_cons_pow (k : ℕ) (s : ListBlank (Fin 2)) :
    u8 +> ((u8 ^ k) +> s) = (u8 ^ (k + 1)) +> s := by
  rw [pow_succ_left u8 k, app_assoc]

private theorem u8_snoc_pow (k : ℕ) (s : ListBlank (Fin 2)) :
    (u8 ^ k) +> (u8 +> s) = (u8 ^ (k + 1)) +> s := by
  rw [pow_succ_right u8 k, app_assoc]

private theorem sub_S0 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 63) (layerBits km1 .S0 s)
      (uBits [2] +> ((u8 ^ km1) +> (sepBits .S5 +> s))) := by
  have h := unitStep_m8 (unit_S0 s) km1
  have hs : uBits [10] +> (uBits [0, 2] +> s) = sepBits .S5 +> s := by
    dsimp only [sepBits]; rw [← uBits_cons2 10 0 [2] s]
  rw [show 56 * (km1 + 1) + 7 = 56 * km1 + 63 by omega, hs] at h
  exact h

private theorem sub_S1 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 63) (layerBits km1 .S1 s)
      (uBits [2] +> ((u8 ^ km1) +> (sepBits .S2 +> s))) := by
  have h := unitStep_m8 (unit_S1 s) km1
  have hs : uBits [14] +> (uBits [2] +> s) = sepBits .S2 +> s := by
    dsimp only [sepBits]; rw [← uBits_cons2 14 2 [] s]
  rw [show 56 * (km1 + 1) + 7 = 56 * km1 + 63 by omega, hs] at h
  exact h

private theorem sub_S2 (km1 : ℕ) {cChild : ℕ} {s s' : ListBlank (Fin 2)}
    (hc : CarrySem false true cChild s s') :
    UnitStepB (56 * km1 + 56 + cChild) (layerBits km1 .S2 s)
      (uBits [2] +> layerBits km1 .S6 s') := by
  have h := unitStep_m8 hc km1
  dsimp only [layerBits] at h ⊢
  rw [uBits_eight, u8_snoc_pow km1, show 56 * (km1 + 1) + cChild = 56 * km1 + 56 + cChild by
    omega] at h
  exact h

private theorem sub_S3 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 103) (layerBits km1 .S3 s)
      (uBits [2] +> layerBits km1 .S4 s) := by
  have h := unitStep_m8 (unit_S3 s) km1
  dsimp only [layerBits] at h ⊢
  rw [uBits_eight, u8_snoc_pow km1, show 56 * (km1 + 1) + 47 = 56 * km1 + 103 by omega] at h
  exact h

private theorem sub_S4 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 63) (layerBits km1 .S4 s)
      (uBits [2] +> ((u8 ^ km1) +> (sepBits .S7 +> s))) := by
  have h := unitStep_m8 (unit_S4 s) km1
  rw [show 56 * (km1 + 1) + 7 = 56 * km1 + 63 by omega] at h
  exact h

private theorem sub_S5 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 103) (layerBits km1 .S5 s)
      (uBits [2] +> layerBits km1 .S1 s) := by
  have h := unitStep_m8 (unit_S5 s) km1
  dsimp only [layerBits] at h ⊢
  rw [uBits_eight, u8_snoc_pow km1, show 56 * (km1 + 1) + 47 = 56 * km1 + 103 by omega] at h
  exact h

private theorem sub_S6 (km1 : ℕ) (s : ListBlank (Fin 2)) :
    UnitStepB (56 * km1 + 63) (layerBits km1 .S6 s)
      (uBits [2] +> ((u8 ^ km1) +> (sepBits .S3 +> s))) := by
  have h := unitStep_m8 (unit_S6 s) km1
  have hs : uBits [10] +> (uBits [6] +> s) = sepBits .S3 +> s := by
    dsimp only [sepBits]; rw [← uBits_cons2 10 6 [] s]
  rw [show 56 * (km1 + 1) + 7 = 56 * km1 + 63 by omega, hs] at h
  exact h

private theorem sub_S7 (km1 : ℕ) {cChild : ℕ} {s s' : ListBlank (Fin 2)}
    (hc : CarrySem false false cChild s s') :
    UnitStepB (56 * km1 + 56 + cChild) (layerBits km1 .S7 s)
      (uBits [2] +> layerBits km1 .S0 s') := by
  have h := unitStep_m8 hc km1
  dsimp only [layerBits] at h ⊢
  rw [uBits_eight, u8_snoc_pow km1, show 56 * (km1 + 1) + cChild = 56 * km1 + 56 + cChild by
    omega] at h
  exact h

private theorem step1Carry_none_sound {isTop p : Bool} {km1 km1' : ℕ} {j j' : Sep} {c1 : ℕ}
    (h : step1Carry isTop p km1 j = (km1', j', none, c1)) (s : ListBlank (Fin 2)) :
    CarrySem isTop p c1 (layerBits km1 j s) (layerBits km1' j' s) := by
  cases p with
  | false =>
      cases j with
      | S0 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S0 km1 s)
          rw [u8_cons_pow km1, show (56 * km1 + 63) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 144 else 175) by cases isTop <;> rfl] at hm
          exact hm
      | S1 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S1 km1 s)
          rw [u8_cons_pow km1, show (56 * km1 + 63) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 144 else 175) by cases isTop <;> rfl] at hm
          exact hm
      | S2 => simp [step1Carry] at h
      | S3 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S3 km1 s)
          dsimp only [layerBits] at hm ⊢
          rw [u8_cons_pow (km1 + 1), show (56 * km1 + 103) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 184 else 215) by cases isTop <;> rfl] at hm
          exact hm
      | S4 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S4 km1 s)
          rw [u8_cons_pow km1, show (56 * km1 + 63) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 144 else 175) by cases isTop <;> rfl] at hm
          exact hm
      | S5 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S5 km1 s)
          dsimp only [layerBits] at hm ⊢
          rw [u8_cons_pow (km1 + 1), show (56 * km1 + 103) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 184 else 215) by cases isTop <;> rfl] at hm
          exact hm
      | S6 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S6 km1 s)
          rw [u8_cons_pow km1, show (56 * km1 + 63) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 144 else 175) by cases isTop <;> rfl] at hm
          exact hm
      | S7 => simp [step1Carry] at h
  | true =>
      cases j with
      | S0 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have h1 := sub_S0 km1 s
          have h2 : UnitStepB (56 * km1 + 103) (u8 +> ((u8 ^ km1) +> (sepBits .S5 +> s)))
              (uBits [2] +> layerBits km1 .S1 s) := by
            rw [u8_cons_pow km1]; exact sub_S5 km1 s
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 63) + (56 * km1 + 103) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 240 else 271) by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S1 => simp [step1Carry] at h
      | S2 => simp [step1Carry] at h
      | S3 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have h1 := sub_S3 km1 s
          have h2 : UnitStepB (56 * (km1 + 1) + 63) (u8 +> layerBits km1 .S4 s)
              (uBits [2] +> layerBits km1 .S7 s) := by
            dsimp only [layerBits]; rw [u8_cons_pow (km1 + 1)]; exact sub_S4 (km1 + 1) s
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 103) + (56 * (km1 + 1) + 63) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 296 else 327) by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S4 => simp [step1Carry] at h
      | S5 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have h1 := sub_S5 km1 s
          have h2 : UnitStepB (56 * (km1 + 1) + 63) (u8 +> layerBits km1 .S1 s)
              (uBits [2] +> layerBits km1 .S2 s) := by
            dsimp only [layerBits]; rw [u8_cons_pow (km1 + 1)]; exact sub_S1 (km1 + 1) s
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 103) + (56 * (km1 + 1) + 63) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 296 else 327) by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S6 =>
          simp only [step1Carry, Prod.mk.injEq] at h; obtain ⟨rfl, rfl, _, rfl⟩ := h
          have h1 := sub_S6 km1 s
          have h2 : UnitStepB (56 * km1 + 103) (u8 +> ((u8 ^ km1) +> (sepBits .S3 +> s)))
              (uBits [2] +> layerBits km1 .S4 s) := by
            rw [u8_cons_pow km1]; exact sub_S3 km1 s
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 63) + (56 * km1 + 103) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 240 else 271) by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S7 => simp [step1Carry] at h
private theorem step1Carry_some_sound {isTop p b : Bool} {km1 km1' : ℕ} {j j' : Sep}
    {c1 cChild : ℕ} {s s' : ListBlank (Fin 2)}
    (h : step1Carry isTop p km1 j = (km1', j', some b, c1))
    (hc : CarrySem false b cChild s s') :
    CarrySem isTop p (c1 + cChild) (layerBits km1 j s) (layerBits km1' j' s') := by
  cases p with
  | false =>
      cases j with
      | S2 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S2 km1 hc)
          dsimp only [layerBits] at hm ⊢
          rw [u8_cons_pow (km1 + 1), show (56 * km1 + 56 + cChild) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 137 else 168) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S7 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have hm := mkCarry0 isTop (sub_S7 km1 hc)
          dsimp only [layerBits] at hm ⊢
          rw [u8_cons_pow (km1 + 1), show (56 * km1 + 56 + cChild) + (if isTop then 81 else 112) =
            56 * km1 + (if isTop then 137 else 168) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | _ => simp [step1Carry] at h
  | true =>
      cases j with
      | S1 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have h1 := sub_S1 km1 s
          have h2 : UnitStepB (56 * km1 + 56 + cChild) (u8 +> ((u8 ^ km1) +> (sepBits .S2 +> s)))
              (uBits [2] +> layerBits km1 .S6 s') := by
            rw [u8_cons_pow km1]; exact sub_S2 km1 hc
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 63) + (56 * km1 + 56 + cChild) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 193 else 224) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S2 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have h1 := sub_S2 km1 hc
          have h2 : UnitStepB (56 * (km1 + 1) + 63) (u8 +> layerBits km1 .S6 s')
              (uBits [2] +> layerBits km1 .S3 s') := by
            dsimp only [layerBits]; rw [u8_cons_pow (km1 + 1)]; exact sub_S6 (km1 + 1) s'
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 56 + cChild) + (56 * (km1 + 1) + 63) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 249 else 280) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S4 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have h1 := sub_S4 km1 s
          have h2 : UnitStepB (56 * km1 + 56 + cChild) (u8 +> ((u8 ^ km1) +> (sepBits .S7 +> s)))
              (uBits [2] +> layerBits km1 .S0 s') := by
            rw [u8_cons_pow km1]; exact sub_S7 km1 hc
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 63) + (56 * km1 + 56 + cChild) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 193 else 224) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | S7 =>
          simp only [step1Carry, Prod.mk.injEq, Option.some.injEq] at h
          obtain ⟨rfl, rfl, rfl, rfl⟩ := h
          have h1 := sub_S7 km1 hc
          have h2 : UnitStepB (56 * (km1 + 1) + 63) (u8 +> layerBits km1 .S0 s')
              (uBits [2] +> layerBits km1 .S5 s') := by
            dsimp only [layerBits]; rw [u8_cons_pow (km1 + 1)]; exact sub_S0 (km1 + 1) s'
          have hm := mkCarry1 isTop h1 h2
          rw [show (56 * km1 + 56 + cChild) + (56 * (km1 + 1) + 63) + (if isTop then 74 else 105) =
            112 * km1 + (if isTop then 249 else 280) + cChild by
              cases isTop
              · simp only [Bool.false_eq_true, ↓reduceIte]; omega
              · simp only [↓reduceIte]; omega] at hm
          exact hm
      | _ => simp [step1Carry] at h

private inductive CarryChain (isTop : Bool) :
    ℕ → Bool → ℕ → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | zero (p : Bool) (s : ListBlank (Fin 2)) :
      CarryChain isTop 0 p 0 s s
  | succ {n : ℕ} {p : Bool} {c1 c2 : ℕ} {s0 s1 s2 : ListBlank (Fin 2)} :
      CarrySem isTop p c1 s0 s1 →
      CarryChain isTop n (!p) c2 s1 s2 →
      CarryChain isTop (n + 1) p (c1 + c2) s0 s2

private theorem parityXor_zero (p : Bool) : parityXor p 0 = p := rfl

private theorem parityXor_succ (p : Bool) (n : ℕ) :
    parityXor p (n + 1) = parityXor (!p) n := by
  unfold parityXor
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have h1 : (n + 1) % 2 = 1 := by omega
    rw [h, h1]; cases p <;> rfl
  · have h1 : (n + 1) % 2 = 0 := by omega
    rw [h, h1]; cases p <;> rfl

private theorem parityXor_even (p : Bool) (k : ℕ) :
    parityXor p (2 * k) = p := by
  unfold parityXor
  have h : (2 * k) % 2 = 0 := by omega
  rw [h]; rfl

private theorem carryChain_append {isTop : Bool} :
    ∀ {m n : ℕ} {p : Bool} {c1 c2 : ℕ} {s0 s1 s2 : ListBlank (Fin 2)},
      CarryChain isTop m p c1 s0 s1 →
      CarryChain isTop n (parityXor p m) c2 s1 s2 →
      CarryChain isTop (m + n) p (c1 + c2) s0 s2
  | 0, _, _, _, _, _, _, _, .zero _ _, h2 => by
      simpa [parityXor_zero] using h2
  | m + 1, n, p, _, c2, s0, _, s2, .succ hsem htail, h2 => by
      rw [parityXor_succ] at h2
      have hrec := carryChain_append htail h2
      have hcomb := CarryChain.succ hsem hrec
      rw [show m + n + 1 = m + 1 + n by omega, ← Nat.add_assoc] at hcomb
      exact hcomb

private theorem carryChain_split {isTop : Bool} :
    ∀ (m : ℕ) {n : ℕ} {p : Bool} {c : ℕ} {s0 s2 : ListBlank (Fin 2)},
      CarryChain isTop (m + n) p c s0 s2 →
      ∃ c1 c2 s1, c = c1 + c2 ∧
        CarryChain isTop m p c1 s0 s1 ∧
        CarryChain isTop n (parityXor p m) c2 s1 s2
  | 0, _, p, c, s0, _, h => by
      rw [Nat.zero_add] at h
      exact ⟨0, c, s0, by omega, .zero p s0, by simpa [parityXor_zero] using h⟩
  | m + 1, n, p, _, s0, s2, h => by
      rw [show m + 1 + n = (m + n) + 1 by omega] at h
      cases h with
      | succ hsem htail =>
          obtain ⟨c1b, c2, s1, hceq, hm1, hn1⟩ := carryChain_split m htail
          refine ⟨_ + c1b, c2, s1, by omega, .succ hsem hm1, ?_⟩
          rw [parityXor_succ]
          exact hn1

private theorem iterCarryAux_sound (isTop : Bool) :
    ∀ (r : ℕ) (p qCur : Bool) (km1 : ℕ) (j : Sep)
      (km1' : ℕ) (j' : Sep) (nEm cR cChild : ℕ) (sNext sNext' : ListBlank (Fin 2)),
      iterCarryAux isTop r p qCur km1 j = some (km1', j', nEm, cR) →
      CarryChain false nEm qCur cChild sNext sNext' →
      CarryChain isTop r p (cR + cChild)
        (layerBits km1 j sNext) (layerBits km1' j' sNext')
  | 0, p, _, km1, j, _, _, _, _, _, sNext, _, h, hChild => by
      simp only [iterCarryAux, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      cases hChild with
      | zero _ _ => exact .zero p _
  | r + 1, p, qCur, km1, j, km1', j', nEm, cR, cChild, sNext, sNext', h, hChild => by
      unfold iterCarryAux at h
      rcases hs1 : step1Carry isTop p km1 j with ⟨km1_1, j_1, em, c1⟩
      rw [hs1] at h
      dsimp only at h
      cases em with
      | none =>
          dsimp only at h
          rcases hit : iterCarryAux isTop r (!p) qCur km1_1 j_1 with _ | ⟨km1_2, j_2, nEm2, c2⟩
          · rw [hit] at h; nomatch h
          · rw [hit] at h
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h
            have h1 := step1Carry_none_sound hs1 sNext
            have h2 := iterCarryAux_sound isTop r (!p) qCur km1_1 j_1 km1_2 j_2 nEm2 c2 cChild
              sNext sNext' hit hChild
            have hc := CarryChain.succ h1 h2
            rw [Nat.add_assoc]
            exact hc
      | some b =>
          dsimp only at h
          cases hbq : (b == qCur) with
          | false => rw [hbq] at h; nomatch h
          | true =>
              rw [hbq, (ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
              have hb_eq : b = qCur := eq_of_beq hbq
              subst hb_eq
              rcases hit : iterCarryAux isTop r (!p) (!b) km1_1 j_1 with _ | ⟨km1_2, j_2, nEm2, c2⟩
              · rw [hit] at h; nomatch h
              · rw [hit] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl, rfl⟩ := h
                cases hChild with
                | succ hSemChild hTailChild =>
                    rename_i cc1 cc2 sMid
                    have h1 := step1Carry_some_sound hs1 hSemChild
                    have h2 := iterCarryAux_sound isTop r (!p) (!b) km1_1 j_1 km1_2 j_2 nEm2 c2
                      cc2 sMid sNext' hit hTailChild
                    have hc := CarryChain.succ h1 h2
                    rw [show (c1 + c2) + (cc1 + cc2) = (c1 + cc1) + (c2 + cc2) by omega]
                    exact hc
private theorem cycle16_eq (isTop p0 : Bool) (j0 : Sep) (km1 : ℕ) :
    iterCarryAux isTop 16 p0 (qPol j0) km1 j0 =
      some (km1 + 4, j0, 6, 1344 * km1 + b16 isTop p0 j0) := by
  cases isTop
  · cases p0 <;> cases j0 <;>
      (simp only [iterCarryAux, step1Carry, qPol, b16, Bool.not_true, Bool.not_false,
         beq_self_eq_true, Bool.false_eq_true, ↓reduceIte];
       rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq];
       refine ⟨by omega, rfl, rfl, by omega⟩)
  · cases p0 <;> cases j0 <;>
      (simp only [iterCarryAux, step1Carry, qPol, b16, Bool.not_true, Bool.not_false,
         beq_self_eq_true, ↓reduceIte];
       rw [Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq];
       refine ⟨by omega, rfl, rfl, by omega⟩)

private theorem carryChain_congr_pol {isTop : Bool} {n : ℕ} {p p' : Bool} {c : ℕ}
    {s0 s1 : ListBlank (Fin 2)} (hp : p = p') (h : CarryChain isTop n p c s0 s1) :
    CarryChain isTop n p' c s0 s1 := hp ▸ h

private theorem qCycles_sound (isTop p0 : Bool) (j0 : Sep) :
    ∀ (q km1 cChild : ℕ) (sNext sNext' : ListBlank (Fin 2)),
      CarryChain false (6 * q) (qPol j0) cChild sNext sNext' →
      CarryChain isTop (16 * q) p0 (qCyclesCost isTop p0 j0 km1 q + cChild)
        (layerBits km1 j0 sNext) (layerBits (km1 + 4 * q) j0 sNext')
  | 0, km1, _, sNext, _, hChild => by
      cases hChild with
      | zero _ _ =>
          simp only [Nat.mul_zero, Nat.add_zero, qCyclesCost]
          exact .zero p0 _
  | q' + 1, km1, cChild, sNext, sNext', hChild => by
      rw [show 6 * (q' + 1) = 6 * q' + 6 by omega] at hChild
      obtain ⟨cc1, cc2, sMid, hceq, hcQ, hc16⟩ := carryChain_split (6 * q') hChild
      have hpar6 : parityXor (qPol j0) (6 * q') = qPol j0 := by
        rw [show 6 * q' = 2 * (3 * q') by omega]
        exact parityXor_even (qPol j0) (3 * q')
      rw [hpar6] at hc16
      have h1 := qCycles_sound isTop p0 j0 q' km1 cc1 sNext sMid hcQ
      have hpar16 : parityXor p0 (16 * q') = p0 := by
        rw [show 16 * q' = 2 * (8 * q') by omega]
        exact parityXor_even p0 (8 * q')
      have h2 := iterCarryAux_sound isTop 16 p0 (qPol j0) (km1 + 4 * q') j0
        (km1 + 4 * q' + 4) j0 6 (1344 * (km1 + 4 * q') + b16 isTop p0 j0) cc2 sMid sNext'
        (cycle16_eq isTop p0 j0 (km1 + 4 * q')) hc16
      have hcomb := carryChain_append h1 (carryChain_congr_pol hpar16.symm h2)
      have hcost : (qCyclesCost isTop p0 j0 km1 q' + cc1) +
          ((1344 * (km1 + 4 * q') + b16 isTop p0 j0) + cc2) =
          qCyclesCost isTop p0 j0 km1 (q' + 1) + cChild := by
        rw [hceq]
        cases q' with
        | zero =>
            dsimp only [qCyclesCost]
            ring
        | succ m =>
            dsimp only [qCyclesCost]
            ring
      rw [show 16 * q' + 16 = 16 * (q' + 1) by omega,
          show km1 + 4 * q' + 4 = km1 + 4 * (q' + 1) by omega, hcost] at hcomb
      exact hcomb

private theorem fastCarries_sound :
    ∀ (layers : List (ℕ × Sep)) (isTop p0 : Bool) (C : ℕ)
      (layersOut : List (ℕ × Sep)) (cost : ℕ) (sTail : ListBlank (Fin 2)),
      fastCarries isTop p0 C layers = some (layersOut, cost) →
      CarryChain isTop C p0 cost (layersBits layers sTail) (layersBits layersOut sTail)
  | [], isTop, p0, C, layersOut, cost, sTail, h => by
      unfold fastCarries at h
      cases hc : (C == 0) with
      | false => rw [hc] at h; nomatch h
      | true =>
          rw [hc, (ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
          have hc0 : C = 0 := eq_of_beq hc
          subst hc0
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .zero p0 sTail
  | (km1, j0) :: rest, isTop, p0, C, layersOut, cost, sTail, h => by
      unfold fastCarries at h
      cases hc : (C == 0) with
      | true =>
          rw [hc, (ite_eq_left_of_eq_true _ _ (eq_true rfl))] at h
          have hc0 : C = 0 := eq_of_beq hc
          subst hc0
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .zero p0 _
      | false =>
          rw [hc, (ite_eq_right_of_eq_false _ _ (eq_false (by simp)))] at h
          dsimp only at h
          rcases hit : iterCarryAux isTop (C % 16) p0 (qPol j0) (km1 + 4 * (C / 16)) j0 with
            _ | ⟨km1Out, jOut, rEmit, costR⟩
          · rw [hit] at h; nomatch h
          · rw [hit] at h
            dsimp only at h
            rcases hfc : fastCarries false (qPol j0) (6 * (C / 16) + rEmit) rest with
              _ | ⟨restOut, childCost⟩
            · rw [hfc] at h; nomatch h
            · rw [hfc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hChild := fastCarries_sound rest false (qPol j0)
                (6 * (C / 16) + rEmit) restOut childCost sTail hfc
              obtain ⟨ccQ, ccR, sMid, hcc, hchQ, hchR⟩ := carryChain_split (6 * (C / 16)) hChild
              have hpar6 : parityXor (qPol j0) (6 * (C / 16)) = qPol j0 := by
                rw [show 6 * (C / 16) = 2 * (3 * (C / 16)) by omega]
                exact parityXor_even (qPol j0) (3 * (C / 16))
              rw [hpar6] at hchR
              have hQ := qCycles_sound isTop p0 j0 (C / 16) km1 ccQ (layersBits rest sTail) sMid
                hchQ
              have hpar16 : parityXor p0 (16 * (C / 16)) = p0 := by
                rw [show 16 * (C / 16) = 2 * (8 * (C / 16)) by omega]
                exact parityXor_even p0 (8 * (C / 16))
              have hR := iterCarryAux_sound isTop (C % 16) p0 (qPol j0)
                (km1 + 4 * (C / 16)) j0 km1Out jOut rEmit costR ccR
                sMid (layersBits restOut sTail) hit hchR
              have hcomb := carryChain_append hQ (carryChain_congr_pol hpar16.symm hR)
              rw [Nat.div_add_mod C 16,
                  show (qCyclesCost isTop p0 j0 km1 (C / 16) + ccQ) + (costR + ccR) =
                    qCyclesCost isTop p0 j0 km1 (C / 16) + costR + childCost by omega] at hcomb
              exact hcomb

private theorem carryChain_top_reaches :
    ∀ {n : ℕ} {p : Bool} {c : ℕ} {s0 s1 : ListBlank (Fin 2)},
      CarryChain true n p c s0 s1 →
      (evalWin (topBits p +> s0) default 1 true [] [0]) [target_tm]⊢^{c}
        (evalWin (topBits (parityXor p n) +> s1) default 1 true [] [0])
  | 0, p, _, _, _, .zero _ _ => by
      rw [parityXor_zero]
      rfl
  | _ + 1, p, _, s0, _, .succ (c1 := c1) (s1 := s1) hsem htail => by
      rw [parityXor_succ]
      have h1 : (evalWin (topBits p +> s0) default 1 true [] [0]) [target_tm]⊢^{c1}
          (evalWin (topBits (!p) +> s1) default 1 true [] [0]) := by
        cases p <;> exact hsem
      exact ms_trans h1 (carryChain_top_reaches htail)

private theorem matchTopHead_eq {l rest : List LTok} {p0 : Bool}
    (h : matchTopHead l = some (p0, rest)) :
    l = topHead p0 ++ rest := by
  unfold matchTopHead at h
  cases l with
  | nil => nomatch h
  | cons t1 r1 =>
      cases t1 with
      | M8 _ => nomatch h
      | M06 _ => nomatch h
      | U a =>
          dsimp only at h
          split_ifs at h with ha11 ha5
          · rw [eq_of_beq ha11]
            injection h with hp; injection hp with hp0 hr; subst hp0 hr; rfl
          · cases r1 with
            | nil => nomatch h
            | cons t2 r2 =>
                cases t2 with
                | M8 _ => nomatch h
                | M06 _ => nomatch h
                | U b =>
                    dsimp only at h
                    split_ifs at h with hb2
                    rw [eq_of_beq ha5, eq_of_beq hb2]
                    injection h with hp; injection hp with hp0 hr; subst hp0 hr; rfl


private theorem stepOdom?_sound {bs bs' : BaseState} {c : ℕ}
    (h : stepOdom? bs = some (bs', c)) :
    ReachesIn target_tm c (encodeBase bs) (encodeBase bs') := by
  unfold stepOdom? at h
  rcases bs with ⟨m, l, w⟩
  cases m with
  | B0 =>
      cases w with
      | cons _ _ => nomatch h
      | nil =>
          dsimp only at h
          rcases hm : matchTopHead l with _ | ⟨p0, rest⟩
          · rw [hm] at h; nomatch h
          · rw [hm] at h
            dsimp only at h
            split_ifs at h with hcap
            rcases hfc : fastCarries true p0 (maxCarries p0 (parseLayers rest).1) (parseLayers
              rest).1 with
              _ | ⟨layers', cOut⟩
            · rw [hfc] at h; nomatch h
            · rw [hfc] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hch := fastCarries_sound (parseLayers rest).1 true p0
                (maxCarries p0 (parseLayers rest).1) layers' cOut (eL (parseLayers rest).2) hfc
              have htr := carryChain_top_reaches hch
              have hstart : encodeBase (.B0, l, []) =
                  evalWin (topBits p0 +> layersBits (parseLayers rest).1 (eL (parseLayers rest).2))
                    default 1 true [] [0] := by
                dsimp only [encodeBase, eW]
                rw [matchTopHead_eq hm, eL_topHead, eL_parseLayers]
              have hend : encodeBase (.B0,
                    topHead (parityXor p0 (maxCarries p0 (parseLayers rest).1)) ++
                      encLayers layers' (parseLayers rest).2, []) =
                  evalWin (topBits (parityXor p0 (maxCarries p0 (parseLayers rest).1)) +>
                      layersBits layers' (eL (parseLayers rest).2))
                    default 1 true [] [0] := by
                dsimp only [encodeBase, eW]
                rw [eL_topHead, eL_encLayers]
              rw [hstart, hend]
              exact htr
  | _ => nomatch h

private theorem masterStep_sound {bs bs' : BaseState} {c : ℕ}
    (h : masterStep bs = some (bs', c)) :
    ReachesIn target_tm c (encodeBase bs) (encodeBase bs') := by
  unfold masterStep at h
  rcases ho : stepOdom? bs with _ | res
  · rw [ho] at h
    exact stepSys_sound bs bs' c h
  · rw [ho] at h
    injection h with hres
    subst hres
    exact stepOdom?_sound ho

/-! ### Part 1: Concrete Phase `init [] ⊢* bs_4444` (Era 1 + Era-1 Wrap, 27,168,468 raw TM steps) -/

private def beqMode : Mode → Mode → Bool
  | .Init0, .Init0 => true
  | .B0, .B0 => true
  | .A0, .A0 => true
  | .E0, .E0 => true
  | .F0, .F0 => true
  | .F0z, .F0z => true
  | .Halt, .Halt => true
  | _, _ => false

private theorem beqMode_eq {a b : Mode} (h : beqMode a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | nomatch h

private def beqLTok : LTok → LTok → Bool
  | .U a, .U b => a == b
  | .M8 a, .M8 b => a == b
  | .M06 a, .M06 b => a == b
  | _, _ => false

private theorem beqLTok_eq {a b : LTok} (h : beqLTok a b = true) : a = b := by
  cases a <;> cases b <;> dsimp only [beqLTok] at h
  · exact congrArg LTok.U (eq_of_beq h)
  · nomatch h
  · nomatch h
  · nomatch h
  · exact congrArg LTok.M8 (eq_of_beq h)
  · nomatch h
  · nomatch h
  · nomatch h
  · exact congrArg LTok.M06 (eq_of_beq h)

private def beqWTok : WTok → WTok → Bool
  | .B a, .B b => a == b
  | .T010 a, .T010 b => a == b
  | .MW a, .MW b => a == b
  | _, _ => false

private theorem beqWTok_eq {a b : WTok} (h : beqWTok a b = true) : a = b := by
  cases a <;> cases b <;> dsimp only [beqWTok] at h
  · exact congrArg WTok.B (eq_of_beq h)
  · nomatch h
  · nomatch h
  · nomatch h
  · exact congrArg WTok.T010 (eq_of_beq h)
  · nomatch h
  · nomatch h
  · nomatch h
  · exact congrArg WTok.MW (eq_of_beq h)

private def beqList {α : Type*} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | x :: xs, y :: ys => f x y && beqList f xs ys
  | _, _ => false

private theorem beqList_eq {α : Type*} {f : α → α → Bool}
    (hf : ∀ {x y : α}, f x y = true → x = y) :
    ∀ {xs ys : List α}, beqList f xs ys = true → xs = ys
  | [], [], _ => rfl
  | _ :: _, [], h => by nomatch h
  | [], _ :: _, h => by nomatch h
  | x :: xs, y :: ys, h => by
      dsimp only [beqList] at h
      have hxy : f x y = true ∧ beqList f xs ys = true := Bool.and_eq_true_iff.mp h
      rw [hf hxy.1, beqList_eq hf hxy.2]

private def beqBS (a b : BaseState) : Bool :=
  beqMode a.1 b.1 && beqList beqLTok a.2.1 b.2.1 && beqList beqWTok a.2.2 b.2.2

private theorem beqBS_eq {a b : BaseState} (h : beqBS a b = true) : a = b := by
  rcases a with ⟨ma, la, wa⟩
  rcases b with ⟨mb, lb, wb⟩
  unfold beqBS at h
  dsimp only at h
  have h1 := Bool.and_eq_true_iff.mp h
  have h2 := Bool.and_eq_true_iff.mp h1.1
  rw [beqMode_eq h2.1, beqList_eq beqLTok_eq h2.2, beqList_eq beqWTok_eq h1.2]

private def runMaster : ℕ → BaseState → Option BaseState
  | 0, bs => some bs
  | n + 1, bs =>
      match masterStep bs with
      | some (bs', _) => runMaster n bs'
      | none => none

private def checkMaster (n : ℕ) (a b : BaseState) : Bool :=
  match runMaster n a with
  | some r => beqBS r b
  | none => false

private theorem rs_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : c₂ [target_tm]⊢* c₃) : c₁ [target_tm]⊢* c₃ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn⟩
  exact ⟨m + n, ms_trans hm hn⟩

private theorem runMaster_sound :
    ∀ (n : ℕ) (a b : BaseState), runMaster n a = some b →
      (encodeBase a) [target_tm]⊢* (encodeBase b)
  | 0, a, b, h => by
      injection h with hab; subst hab; exact ⟨0, rfl⟩
  | n + 1, a, b, h => by
      dsimp only [runMaster] at h
      rcases hm : masterStep a with _ | ⟨a', c⟩
      · rw [hm] at h; nomatch h
      · rw [hm] at h
        exact rs_trans ⟨c, masterStep_sound hm⟩ (runMaster_sound n a' b h)

private theorem checkMaster_sound (n : ℕ) (a b : BaseState) (h : checkMaster n a b = true) :
    (encodeBase a) [target_tm]⊢* (encodeBase b) := by
  unfold checkMaster at h
  rcases hr : runMaster n a with _ | r
  · rw [hr] at h; nomatch h
  · rw [hr] at h
    have hEq := beqBS_eq h
    subst hEq
    exact runMaster_sound n a r hr
private def cp0 : BaseState := (.Init0, [], [])
private def cp1 : BaseState := (.A0, [.U 10, .U 6, .M8 0, .U 10, .U 0, .U 2, .U 14, .U 6, .U 2, .U
  0, .U 6, .U 0, .U 2, .U 0, .U 2, .U 0, .U 1], [.MW 4, .B true, .B false, .B false, .B true, .B
  false, .B false, .B false, .T010 0])
private def cp2 : BaseState := (.B0, [.U 1, .U 6, .M8 29, .U 0, .U 2, .U 0, .U 2, .U 8, .M8 9, .U
  0, .U 2, .U 0, .U 2, .U 8, .M8 2, .U 0, .U 2, .U 0, .U 2, .U 8, .U 0, .U 2, .U 0, .U 2, .U 0, .U
  2, .U 8, .U 0, .U 2, .U 2, .U 0, .U 2, .U 0, .U 1], [])
private def cp3 : BaseState := (.F0z, [.U 2, .M8 33, .U 0, .U 2, .U 6, .M8 11, .U 10, .U 6, .M8 3,
  .U 0, .U 2, .U 6, .U 8, .U 0, .U 2, .U 6, .U 0, .U 2, .U 6, .U 0, .U 2, .U 6, .U 1], [.B false,
  .B false, .T010 3, .B false, .B true, .B true, .B false, .B false, .MW 90, .B true, .B false, .B
  false, .B true, .B false, .B false, .B false, .T010 0])
private def cp4 : BaseState := (.B0, [.U 2, .U 2, .M8 370, .U 20, .M8 137, .U 20, .M8 50, .U 20,
  .M8 17, .U 14, .U 2, .M8 5, .U 14, .U 2, .M8 1, .U 0, .U 12, .U 20, .U 1], [.T010 0])
private def cp5 : BaseState := (.B0, [.U 11, .U 8, .U 0, .U 2, .U 0, .U 2, .U 8, .U 0, .U 12, .M06
  368, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6, .M06 136, .U 0, .U 2, .U 0, .U 2, .U 0, .U
  6, .U 0, .U 6, .M06 49, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6, .M06 16, .U 0, .U 2, .U
  0, .U 10, .M06 5, .U 0, .U 2, .U 0, .U 6, .U 6, .M06 0, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U
  0, .U 2, .U 0, .U 2, .U 0, .U 9], [])

private theorem reach_0_1 : (encodeBase cp0) [target_tm]⊢* (encodeBase cp1) :=
  checkMaster_sound 1000 cp0 cp1 (by decide +kernel)

private theorem reach_1_2 : (encodeBase cp1) [target_tm]⊢* (encodeBase cp2) :=
  checkMaster_sound 1000 cp1 cp2 (by decide +kernel)

private theorem reach_2_3 : (encodeBase cp2) [target_tm]⊢* (encodeBase cp3) :=
  checkMaster_sound 1000 cp2 cp3 (by decide +kernel)

private theorem reach_3_4 : (encodeBase cp3) [target_tm]⊢* (encodeBase cp4) :=
  checkMaster_sound 1000 cp3 cp4 (by decide +kernel)

private theorem reach_4_5 : (encodeBase cp4) [target_tm]⊢* (encodeBase cp5) :=
  checkMaster_sound 444 cp4 cp5 (by decide +kernel)

private theorem init_reaches_cp5 : (init [] : Cfg (Fin 2) (Fin 6)) [target_tm]⊢* (encodeBase cp5) :=
  rs_trans reach_0_1 (rs_trans reach_1_2 (rs_trans reach_2_3 (rs_trans reach_3_4 reach_4_5)))

/-! ### Part 2: Inductive `TailHalts` Lifting Engine across Arbitrary Odometer Layers -/

private def HaltsFrom (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (c [target_tm]⊢* cfg') ∧ (step target_tm cfg').isNone

private theorem halts_of_ms {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {n : ℕ}
    (h : c₁ [target_tm]⊢^{n} c₂) (hh : HaltsFrom c₂) : HaltsFrom c₁ := by
  rcases hh with ⟨cfg', ⟨m, hm⟩, hnone⟩
  exact ⟨cfg', ⟨n + m, ms_trans h hm⟩, hnone⟩

private theorem halts_of_rs {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : c₁ [target_tm]⊢* c₂) (hh : HaltsFrom c₂) : HaltsFrom c₁ := by
  rcases h with ⟨n, hn⟩
  exact halts_of_ms hn hh

private def UnitHalt (sL : ListBlank (Fin 2)) : Prop :=
  ∀ sW : ListBlank (Fin 2), HaltsFrom (evalWin sL sW 1 false [0] [])

private def CarryHalt : Bool → Bool → ListBlank (Fin 2) → Prop
  | false, false, sL => UnitHalt (sepBits .S7 +> sL)
  | false, true,  sL => UnitHalt (sepBits .S2 +> sL)
  | true,  false, sL => HaltsFrom (evalWin (topBits false +> sL) default 1 true [] [0])
  | true,  true,  sL => HaltsFrom (evalWin (topBits true +> sL) default 1 true [] [0])

private theorem unitStep_m8_halt {sX : ListBlank (Fin 2)}
    (hX : UnitHalt sX) (km1 : ℕ) :
    UnitHalt ((u8 ^ (km1 + 1)) +> sX) := by
  intro sW
  have h1 := walkWordLeft 24 1 false [0] u8 [] w24 motifB0_body (km1 + 1) sX sW
  exact halts_of_ms h1 (hX ((w24 ^ (km1 + 1)) +> sW))

private theorem wrap_S7_halt {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt false false sL := by
  intro sW
  have ha : (evalWin (sepBits .S7 +> sL) sW 1 false [0] []) [target_tm]⊢^{60}
      (evalWin sL (w_s7 +> sW) 1 false [0] []) :=
    chkWin_eq false false 60 1 true (sepBits .S7) [0] 1 false [0] w_s7
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  exact halts_of_ms ha (h1 (w_s7 +> sW))

private theorem wrap_Top0_halt {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt true false sL := by
  have ha : (evalWin (topBits false +> sL) default 1 true [] [0]) [target_tm]⊢^{33}
      (evalWin sL (w_top0 +> default) 1 false [0] []) :=
    chkWin_eq false false 33 1 true (topBits false) [0] 1 false [0] w_top0
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  exact halts_of_ms ha (h1 (w_top0 +> default))

private theorem mkCarry0_halt (isTop : Bool) {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt isTop false sL := by
  cases isTop
  · exact wrap_S7_halt h1
  · exact wrap_Top0_halt h1

private theorem wrap_S2_halt_1 {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt false true sL := by
  intro sW
  have ha : (evalWin (sepBits .S2 +> sL) sW 1 false [0] []) [target_tm]⊢^{48}
      (evalWin sL (w_s2 +> sW) 1 false [0] []) :=
    chkWin_eq false false 48 1 true (sepBits .S2) [0] 1 false [0] w_s2
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  exact halts_of_ms ha (h1 (w_s2 +> sW))

private theorem wrap_Top1_halt_1 {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt true true sL := by
  have ha : (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{21}
      (evalWin sL (w_top1 +> default) 1 false [0] []) :=
    chkWin_eq false false 21 1 true (topBits true) [0] 1 false [0] w_top1
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  exact halts_of_ms ha (h1 (w_top1 +> default))

private theorem mkCarry1_halt_1 (isTop : Bool) {sL : ListBlank (Fin 2)} (h1 : UnitHalt sL) :
    CarryHalt isTop true sL := by
  cases isTop
  · exact wrap_S2_halt_1 h1
  · exact wrap_Top1_halt_1 h1

private theorem wrap_S2_halt_2 {c1 : ℕ} {sL sR1 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitHalt (u8 +> sR1)) :
    CarryHalt false true sL := by
  intro sW
  have ha : (evalWin (sepBits .S2 +> sL) sW 1 false [0] []) [target_tm]⊢^{48}
      (evalWin sL (w_s2 +> sW) 1 false [0] []) :=
    chkWin_eq false false 48 1 true (sepBits .S2) [0] 1 false [0] w_s2
      sL sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (evalWin_b0_pfx _ sL sW) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_s2 +> sW)
  have hc : (evalWin (uBits [2] +> sR1) (w_s2 +> sW) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_s2_rem +> sW) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_s2 1 false (0 :: u8) w_s2_rem
      sR1 sW (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  exact halts_of_ms (ms_trans (ms_trans ha hb) hc) (h2 (w_s2_rem +> sW))

private theorem wrap_Top1_halt_2 {c1 : ℕ} {sL sR1 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitHalt (u8 +> sR1)) :
    CarryHalt true true sL := by
  have ha : (evalWin (topBits true +> sL) default 1 true [] [0]) [target_tm]⊢^{21}
      (evalWin sL (w_top1 +> default) 1 false [0] []) :=
    chkWin_eq false false 21 1 true (topBits true) [0] 1 false [0] w_top1
      sL default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin]) (by simp [evalWin]) (by decide +kernel)
  have hb := h1 (w_top1 +> default)
  have hc : (evalWin (uBits [2] +> sR1) (w_top1 +> default) 5 true [0] []) [target_tm]⊢^{29}
      (evalWin (u8 +> sR1) (w_top1_rem +> default) 1 false [0] []) :=
    chkWin_eq false false 29 5 true (0 :: uBits [2]) w_top1 1 false (0 :: u8) w_top1_rem
      sR1 default (fun hc => nomatch hc) (fun hc => nomatch hc)
      (by simp [evalWin, ListBlank.append])
      (by simp [evalWin, ListBlank.append])
      (by decide +kernel)
  exact halts_of_ms (ms_trans (ms_trans ha hb) hc) (h2 (w_top1_rem +> default))

private theorem mkCarry1_halt_2 (isTop : Bool) {c1 : ℕ} {sL sR1 : ListBlank (Fin 2)}
    (h1 : UnitStepB c1 sL (uBits [2] +> sR1))
    (h2 : UnitHalt (u8 +> sR1)) :
    CarryHalt isTop true sL := by
  cases isTop
  · exact wrap_S2_halt_2 h1 h2
  · exact wrap_Top1_halt_2 h1 h2

private inductive TailHalts : Bool → ListBlank (Fin 2) → Prop
  | halt {q : Bool} {s : ListBlank (Fin 2)} : CarryHalt false q s → TailHalts q s
  | step {q : Bool} {c : ℕ} {s s' : ListBlank (Fin 2)} :
      CarrySem false q c s s' → TailHalts (!q) s' → TailHalts q s

private def LayerGoal (isTop p : Bool) (s : ListBlank (Fin 2)) : Prop :=
  match isTop with
  | true => CarryHalt true p s
  | false => TailHalts p s

private theorem layerGoal_halt {isTop p : Bool} {s : ListBlank (Fin 2)}
    (h : CarryHalt isTop p s) : LayerGoal isTop p s := by
  cases isTop with
  | true => exact h
  | false => exact TailHalts.halt h

private theorem layerGoal_step {isTop p : Bool} {c : ℕ} {s0 s1 : ListBlank (Fin 2)}
    (hc : CarrySem isTop p c s0 s1) (hg : LayerGoal isTop (!p) s1) :
    LayerGoal isTop p s0 := by
  cases isTop with
  | true =>
      cases p with
      | false => exact halts_of_ms hc hg
      | true => exact halts_of_ms hc hg
  | false => exact TailHalts.step hc hg

private theorem lift_layer_gen (isTop : Bool) :
    ∀ {q : Bool} {s : ListBlank (Fin 2)}, TailHalts q s →
      ∀ (km1 : ℕ) (p : Bool) (j : Sep), qPol j = q → LayerGoal isTop p (layerBits km1 j s) := by
  intro q s h
  induction h with
  | @halt q s hh =>
      intro km1 p j hj
      subst hj
      cases q_eq : qPol j with
      | true =>
          have hh' : CarryHalt false true s := by rw [q_eq] at hh; exact hh
          have e_fS2 : ∀ k, LayerGoal isTop false (layerBits k .S2 s) := fun k =>
            layerGoal_halt (mkCarry0_halt isTop (unitStep_m8_halt hh' k))
          have e_tS2 : ∀ k, LayerGoal isTop true (layerBits k .S2 s) := fun k =>
            layerGoal_halt (mkCarry1_halt_1 isTop (unitStep_m8_halt hh' k))
          have e_tS1 : ∀ k, LayerGoal isTop true (layerBits k .S1 s) := fun k => by
            refine layerGoal_halt (mkCarry1_halt_2 isTop (sub_S1 k s) ?_)
            rw [u8_cons_pow k]
            exact unitStep_m8_halt hh' k
          have e_tS5 : ∀ k, LayerGoal isTop true (layerBits k .S5 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S5) rfl s) (e_fS2 k)
          have e_fS5 : ∀ k, LayerGoal isTop false (layerBits k .S5 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S5) rfl s) (e_tS1 (k + 1))
          have e_fS1 : ∀ k, LayerGoal isTop false (layerBits k .S1 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S1) rfl s) (e_tS2 k)
          have e_fS0 : ∀ k, LayerGoal isTop false (layerBits k .S0 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S0) rfl s) (e_tS5 k)
          have e_tS0 : ∀ k, LayerGoal isTop true (layerBits k .S0 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S0) rfl s) (e_fS1 k)
          cases j <;> simp only [qPol] at q_eq <;> try cases q_eq
          · cases p with | false => exact e_fS0 km1 | true => exact e_tS0 km1
          · cases p with | false => exact e_fS1 km1 | true => exact e_tS1 km1
          · cases p with | false => exact e_fS2 km1 | true => exact e_tS2 km1
          · cases p with | false => exact e_fS5 km1 | true => exact e_tS5 km1
      | false =>
          have hh' : CarryHalt false false s := by rw [q_eq] at hh; exact hh
          have e_fS7 : ∀ k, LayerGoal isTop false (layerBits k .S7 s) := fun k =>
            layerGoal_halt (mkCarry0_halt isTop (unitStep_m8_halt hh' k))
          have e_tS7 : ∀ k, LayerGoal isTop true (layerBits k .S7 s) := fun k =>
            layerGoal_halt (mkCarry1_halt_1 isTop (unitStep_m8_halt hh' k))
          have e_tS4 : ∀ k, LayerGoal isTop true (layerBits k .S4 s) := fun k => by
            refine layerGoal_halt (mkCarry1_halt_2 isTop (sub_S4 k s) ?_)
            rw [u8_cons_pow k]
            exact unitStep_m8_halt hh' k
          have e_fS4 : ∀ k, LayerGoal isTop false (layerBits k .S4 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S4) rfl s) (e_tS7 k)
          have e_tS3 : ∀ k, LayerGoal isTop true (layerBits k .S3 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S3) rfl s) (e_fS7 k)
          have e_fS3 : ∀ k, LayerGoal isTop false (layerBits k .S3 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S3) rfl s) (e_tS4 (k + 1))
          have e_tS6 : ∀ k, LayerGoal isTop true (layerBits k .S6 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S6) rfl s) (e_fS4 k)
          have e_fS6 : ∀ k, LayerGoal isTop false (layerBits k .S6 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S6) rfl s) (e_tS3 k)
          cases j <;> simp only [qPol] at q_eq <;> try cases q_eq
          · cases p with | false => exact e_fS3 km1 | true => exact e_tS3 km1
          · cases p with | false => exact e_fS4 km1 | true => exact e_tS4 km1
          · cases p with | false => exact e_fS6 km1 | true => exact e_tS6 km1
          · cases p with | false => exact e_fS7 km1 | true => exact e_tS7 km1
  | @step q cChild s s' hc _ ih =>
      intro km1 p j hj
      cases q with
      | true =>
          have e_fS2 : ∀ k, LayerGoal isTop false (layerBits k .S2 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := false) (b := true) (km1
              := k) (j := .S2) rfl hc) (ih (k + 1) true .S6 rfl)
          have e_tS2 : ∀ k, LayerGoal isTop true (layerBits k .S2 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := true) (b := true) (km1 :=
              k) (j := .S2) rfl hc) (ih k false .S3 rfl)
          have e_tS1 : ∀ k, LayerGoal isTop true (layerBits k .S1 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := true) (b := true) (km1 :=
              k) (j := .S1) rfl hc) (ih k false .S6 rfl)
          have e_tS5 : ∀ k, LayerGoal isTop true (layerBits k .S5 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S5) rfl s) (e_fS2 k)
          have e_fS5 : ∀ k, LayerGoal isTop false (layerBits k .S5 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S5) rfl s) (e_tS1 (k + 1))
          have e_fS1 : ∀ k, LayerGoal isTop false (layerBits k .S1 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S1) rfl s) (e_tS2 k)
          have e_fS0 : ∀ k, LayerGoal isTop false (layerBits k .S0 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S0) rfl s) (e_tS5 k)
          have e_tS0 : ∀ k, LayerGoal isTop true (layerBits k .S0 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S0) rfl s) (e_fS1 k)
          cases j <;> simp only [qPol] at hj <;> try cases hj
          · cases p with | false => exact e_fS0 km1 | true => exact e_tS0 km1
          · cases p with | false => exact e_fS1 km1 | true => exact e_tS1 km1
          · cases p with | false => exact e_fS2 km1 | true => exact e_tS2 km1
          · cases p with | false => exact e_fS5 km1 | true => exact e_tS5 km1
      | false =>
          have e_fS7 : ∀ k, LayerGoal isTop false (layerBits k .S7 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := false) (b := false) (km1
              := k) (j := .S7) rfl hc) (ih (k + 1) true .S0 rfl)
          have e_tS7 : ∀ k, LayerGoal isTop true (layerBits k .S7 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := true) (b := false) (km1
              := k) (j := .S7) rfl hc) (ih k false .S5 rfl)
          have e_tS4 : ∀ k, LayerGoal isTop true (layerBits k .S4 s) := fun k =>
            layerGoal_step (step1Carry_some_sound (isTop := isTop) (p := true) (b := false) (km1
              := k) (j := .S4) rfl hc) (ih k false .S0 rfl)
          have e_fS4 : ∀ k, LayerGoal isTop false (layerBits k .S4 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S4) rfl s) (e_tS7 k)
          have e_tS3 : ∀ k, LayerGoal isTop true (layerBits k .S3 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S3) rfl s) (e_fS7 k)
          have e_fS3 : ∀ k, LayerGoal isTop false (layerBits k .S3 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S3) rfl s) (e_tS4 (k + 1))
          have e_tS6 : ∀ k, LayerGoal isTop true (layerBits k .S6 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := true) (km1 := k) (j :=
              .S6) rfl s) (e_fS4 k)
          have e_fS6 : ∀ k, LayerGoal isTop false (layerBits k .S6 s) := fun k =>
            layerGoal_step (step1Carry_none_sound (isTop := isTop) (p := false) (km1 := k) (j :=
              .S6) rfl s) (e_tS3 k)
          cases j <;> simp only [qPol] at hj <;> try cases hj
          · cases p with | false => exact e_fS3 km1 | true => exact e_tS3 km1
          · cases p with | false => exact e_fS4 km1 | true => exact e_tS4 km1
          · cases p with | false => exact e_fS6 km1 | true => exact e_tS6 km1
          · cases p with | false => exact e_fS7 km1 | true => exact e_tS7 km1

private theorem lift_layer {p : Bool} {km1 : ℕ} {j : Sep} {s : ListBlank (Fin 2)}
    (h : TailHalts (qPol j) s) : TailHalts p (layerBits km1 j s) :=
  lift_layer_gen false h km1 p j rfl

private theorem lift_top {p : Bool} {km1 : ℕ} {j : Sep} {s : ListBlank (Fin 2)}
    (h : TailHalts (qPol j) s) :
    HaltsFrom (evalWin (topBits p +> layerBits km1 j s) default 1 true [] [0]) := by
  have hg := lift_layer_gen true h km1 p j rfl
  cases p <;> exact hg

/-! ### Part 3: The 54 Local `CarrySem` Rules, 304-Step `halt_bottom`, and `eat_M06_2k` Induction -/

private theorem uBits_append_list : ∀ (a b : List ℕ), uBits (a ++ b) = uBits a ++ uBits b
  | [], _ => rfl
  | x :: xs, b => by
      dsimp only [List.cons_append, uBits]
      rw [uBits_append_list xs b, List.append_assoc, List.cons_append]

private theorem uBits_append (a b : List ℕ) (s : ListBlank (Fin 2)) :
    uBits (a ++ b) +> s = uBits a +> (uBits b +> s) := by
  rw [uBits_append_list, app_assoc]

private theorem u06_eq_uBits : u06 = uBits [0, 6] := by decide

private def sepList : Sep → List ℕ
  | .S0 => [0, 2, 0, 2]
  | .S1 => [0, 6, 2]
  | .S2 => [14, 2]
  | .S3 => [10, 6]
  | .S4 => [0, 12]
  | .S5 => [10, 0, 2]
  | .S6 => [0, 2, 6]
  | .S7 => [20]

private theorem uBits_sepList (j : Sep) : uBits (sepList j) = sepBits j := by
  cases j <;> rfl

private theorem mkRule0 (c : ℕ) (lhs rhs : List ℕ)
    (hc : checkWin false false c 1 true (sepBits .S7 ++ uBits lhs) [0]
            5 true (0 :: (uBits [2] ++ (sepBits .S0 ++ uBits rhs))) [] = true)
    (s : ListBlank (Fin 2)) :
    CarrySem false false c (uBits lhs +> s) (uBits rhs +> s) := by
  intro sW
  exact chkWin_eq false false c 1 true (sepBits .S7 ++ uBits lhs) [0]
    5 true (0 :: (uBits [2] ++ (sepBits .S0 ++ uBits rhs))) []
    s sW (fun h => nomatch h) (fun h => nomatch h)
    (by rw [← app_assoc (sepBits .S7) (uBits lhs) s]; exact evalWin_b0_pfx _ s sW)
    (by rw [← app_assoc (sepBits .S0) (uBits rhs) s, ← app_assoc (uBits [2]) _ s]; exact
      evalWin_f0z_pfx _ s sW)
    hc

private theorem mkRule1 (c : ℕ) (lhs rhs : List ℕ)
    (hc : checkWin false false c 1 true (sepBits .S2 ++ uBits lhs) [0]
            5 true (0 :: (uBits [2] ++ (sepBits .S6 ++ uBits rhs))) [] = true)
    (s : ListBlank (Fin 2)) :
    CarrySem false true c (uBits lhs +> s) (uBits rhs +> s) := by
  intro sW
  exact chkWin_eq false false c 1 true (sepBits .S2 ++ uBits lhs) [0]
    5 true (0 :: (uBits [2] ++ (sepBits .S6 ++ uBits rhs))) []
    s sW (fun h => nomatch h) (fun h => nomatch h)
    (by rw [← app_assoc (sepBits .S2) (uBits lhs) s]; exact evalWin_b0_pfx _ s sW)
    (by rw [← app_assoc (sepBits .S6) (uBits rhs) s, ← app_assoc (uBits [2]) _ s]; exact
      evalWin_f0z_pfx _ s sW)
    hc

private theorem th_rule {q : Bool} {c : ℕ} {lhs rhs rest : List ℕ} {s : ListBlank (Fin 2)}
    (hr : ∀ t : ListBlank (Fin 2), CarrySem false q c (uBits lhs +> t) (uBits rhs +> t))
    (ht : TailHalts (!q) (uBits (rhs ++ rest) +> s)) :
    TailHalts q (uBits (lhs ++ rest) +> s) := by
  rw [uBits_append lhs rest s]
  rw [uBits_append rhs rest s] at ht
  exact TailHalts.step (hr (uBits rest +> s)) ht

private theorem th_spawn1 {q : Bool} (j : Sep) {rest : List ℕ} {s : ListBlank (Fin 2)}
    (ht : TailHalts (qPol j) (uBits rest +> s)) :
    TailHalts q (uBits ([8] ++ sepList j ++ rest) +> s) := by
  rw [uBits_append ([8] ++ sepList j) rest s, uBits_append [8] (sepList j) _,
      uBits_eight, uBits_sepList j]
  have heq : u8 +> (sepBits j +> (uBits rest +> s)) = layerBits 0 j (uBits rest +> s) := by
    simp [layerBits, list_pow_succ, list_pow_zero, list_pow_one, List.append_eq]
  rw [heq]
  exact lift_layer ht

private theorem th_spawn2 {q : Bool} (j : Sep) {rest : List ℕ} {s : ListBlank (Fin 2)}
    (ht : TailHalts (qPol j) (uBits rest +> s)) :
    TailHalts q (uBits ([8, 8] ++ sepList j ++ rest) +> s) := by
  rw [uBits_append ([8, 8] ++ sepList j) rest s, uBits_append [8, 8] (sepList j) _,
      uBits_sepList j]
  have h88 : uBits [8, 8] = u8 ^ 2 := by decide
  rw [h88]
  exact lift_layer (km1 := 1) ht

private def rsHaltBottom : List (Fin 2) := [0, 0, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0,
  1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0,
  0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0]

private theorem halt_bottom_win :
    checkWin true false 304 1 true (sepBits .S2 ++ uBits [0, 6, 2, 0, 6, 2, 0, 9]) [0]
      2 false [] rsHaltBottom = true := by
  decide +kernel

private theorem halt_bottom :
    CarryHalt false true (uBits [0, 6, 2, 0, 6, 2, 0, 9] +> default) := by
  intro sW
  have hrun : (evalWin (sepBits .S2 +> (uBits [0, 6, 2, 0, 6, 2, 0, 9] +> default)) sW 1 false [0]
    [])
      [target_tm]⊢^{304} (evalWin default sW 2 false [] rsHaltBottom) :=
    chkWin_eq true false 304 1 true (sepBits .S2 ++ uBits [0, 6, 2, 0, 6, 2, 0, 9]) [0]
      2 false [] rsHaltBottom
      default sW (fun _ => rfl) (fun h => nomatch h)
      (by rw [← app_assoc (sepBits .S2) (uBits [0, 6, 2, 0, 6, 2, 0, 9]) default]; exact
        evalWin_b0_pfx _ default sW)
      rfl halt_bottom_win
  refine ⟨evalWin default sW 2 false [] rsHaltBottom, ⟨304, hrun⟩, ?_⟩
  simp [evalWin, step, target_tm, head_def_fin]
private theorem tr_00 (s : ListBlank (Fin 2)) :
    CarrySem false false 119 (uBits [0, 6] +> s) (uBits [14] +> s) :=
  mkRule0 119 [0, 6] [14] (by decide +kernel) s

private theorem tr_01 (s : ListBlank (Fin 2)) :
    CarrySem false true 287 (uBits [14, 6, 6] +> s) (uBits [10, 8, 0, 8] +> s) :=
  mkRule1 287 [14, 6, 6] [10, 8, 0, 8] (by decide +kernel) s

private theorem tr_02 (s : ListBlank (Fin 2)) :
    CarrySem false false 159 (uBits [10, 8] +> s) (uBits [8, 0, 14] +> s) :=
  mkRule0 159 [10, 8] [8, 0, 14] (by decide +kernel) s

private theorem tr_03 (s : ListBlank (Fin 2)) :
    CarrySem false true 327 (uBits [8, 0, 14, 0] +> s) (uBits [8, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule1 327 [8, 0, 14, 0] [8, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_04 (s : ListBlank (Fin 2)) :
    CarrySem false true 259 (uBits [0, 6, 8, 0, 6] +> s) (uBits [0, 2, 8, 14] +> s) :=
  mkRule1 259 [0, 6, 8, 0, 6] [0, 2, 8, 14] (by decide +kernel) s

private theorem tr_05 (s : ListBlank (Fin 2)) :
    CarrySem false false 119 (uBits [0, 2] +> s) (uBits [10] +> s) :=
  mkRule0 119 [0, 2] [10] (by decide +kernel) s

private theorem tr_06 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 8] +> s) (uBits [22] +> s) :=
  mkRule1 215 [10, 8] [22] (by decide +kernel) s

private theorem tr_07 (s : ListBlank (Fin 2)) :
    CarrySem false false 215 (uBits [22, 14] +> s) (uBits [8, 0, 2, 0, 2, 0, 20] +> s) :=
  mkRule0 215 [22, 14] [8, 0, 2, 0, 2, 0, 20] (by decide +kernel) s

private theorem tr_08 (s : ListBlank (Fin 2)) :
    CarrySem false true 243 (uBits [0, 20, 0] +> s) (uBits [0, 2, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule1 243 [0, 20, 0] [0, 2, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_09 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 0] +> s) (uBits [14] +> s) :=
  mkRule1 215 [10, 0] [14] (by decide +kernel) s

private theorem tr_10 (s : ListBlank (Fin 2)) :
    CarrySem false false 271 (uBits [14, 2, 0, 2, 0] +> s) (uBits [8, 0, 2, 6, 0, 6] +> s) :=
  mkRule0 271 [14, 2, 0, 2, 0] [8, 0, 2, 6, 0, 6] (by decide +kernel) s

private theorem tr_11 (s : ListBlank (Fin 2)) :
    CarrySem false true 259 (uBits [14, 0, 6] +> s) (uBits [10, 14] +> s) :=
  mkRule1 259 [14, 0, 6] [10, 14] (by decide +kernel) s

private theorem tr_12 (s : ListBlank (Fin 2)) :
    CarrySem false false 159 (uBits [10, 14] +> s) (uBits [8, 0, 20] +> s) :=
  mkRule0 159 [10, 14] [8, 0, 20] (by decide +kernel) s

private theorem tr_13 (s : ListBlank (Fin 2)) :
    CarrySem false true 355 (uBits [8, 0, 20, 0] +> s) (uBits [8, 0, 2, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule1 355 [8, 0, 20, 0] [8, 0, 2, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_14 (s : ListBlank (Fin 2)) :
    CarrySem false true 159 (uBits [0, 2, 0] +> s) (uBits [0, 6] +> s) :=
  mkRule1 159 [0, 2, 0] [0, 6] (by decide +kernel) s

private theorem tr_15 (s : ListBlank (Fin 2)) :
    CarrySem false true 259 (uBits [0, 6, 8, 0, 2] +> s) (uBits [0, 2, 8, 10] +> s) :=
  mkRule1 259 [0, 6, 8, 0, 2] [0, 2, 8, 10] (by decide +kernel) s

private theorem tr_16 (s : ListBlank (Fin 2)) :
    CarrySem false false 215 (uBits [22, 10] +> s) (uBits [8, 0, 2, 0, 2, 0, 16] +> s) :=
  mkRule0 215 [22, 10] [8, 0, 2, 0, 2, 0, 16] (by decide +kernel) s

private theorem tr_17 (s : ListBlank (Fin 2)) :
    CarrySem false true 231 (uBits [0, 16, 0] +> s) (uBits [0, 2, 0, 2, 0, 2, 0, 2] +> s) :=
  mkRule1 231 [0, 16, 0] [0, 2, 0, 2, 0, 2, 0, 2] (by decide +kernel) s

private theorem tr_18 (s : ListBlank (Fin 2)) :
    CarrySem false true 427 (uBits [14, 2, 2, 0, 6, 0, 6] +> s) (uBits [10, 6, 0, 2, 2, 14] +> s) :=
  mkRule1 427 [14, 2, 2, 0, 6, 0, 6] [10, 6, 0, 2, 2, 14] (by decide +kernel) s

private theorem tr_19 (s : ListBlank (Fin 2)) :
    CarrySem false false 159 (uBits [10, 6] +> s) (uBits [8, 0, 12] +> s) :=
  mkRule0 159 [10, 6] [8, 0, 12] (by decide +kernel) s

private theorem tr_20 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 2] +> s) (uBits [16] +> s) :=
  mkRule1 215 [10, 2] [16] (by decide +kernel) s

private theorem tr_21 (s : ListBlank (Fin 2)) :
    CarrySem false false 187 (uBits [16, 14] +> s) (uBits [8, 0, 2, 0, 20] +> s) :=
  mkRule0 187 [16, 14] [8, 0, 2, 0, 20] (by decide +kernel) s

private theorem tr_22 (s : ListBlank (Fin 2)) :
    CarrySem false true 271 (uBits [8, 0, 2, 0] +> s) (uBits [8, 0, 6] +> s) :=
  mkRule1 271 [8, 0, 2, 0] [8, 0, 6] (by decide +kernel) s

private theorem tr_23 (s : ListBlank (Fin 2)) :
    CarrySem false false 175 (uBits [8, 0, 6] +> s) (uBits [8, 14] +> s) :=
  mkRule0 175 [8, 0, 6] [8, 14] (by decide +kernel) s

private theorem tr_24 (s : ListBlank (Fin 2)) :
    CarrySem false true 483 (uBits [8, 14, 20, 0, 6] +> s) (uBits [8, 10, 8, 0, 2, 0, 2, 14] +> s)
      :=
  mkRule1 483 [8, 14, 20, 0, 6] [8, 10, 8, 0, 2, 0, 2, 14] (by decide +kernel) s

private theorem tr_25 (s : ListBlank (Fin 2)) :
    CarrySem false false 215 (uBits [8, 10, 8] +> s) (uBits [8, 8, 0, 14] +> s) :=
  mkRule0 215 [8, 10, 8] [8, 8, 0, 14] (by decide +kernel) s

private theorem tr_26 (s : ListBlank (Fin 2)) :
    CarrySem false true 439 (uBits [8, 8, 0, 14, 0] +> s) (uBits [8, 8, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule1 439 [8, 8, 0, 14, 0] [8, 8, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_27 (s : ListBlank (Fin 2)) :
    CarrySem false true 271 (uBits [0, 6, 2, 0, 2, 14] +> s) (uBits [0, 2, 6, 0, 20] +> s) :=
  mkRule1 271 [0, 6, 2, 0, 2, 14] [0, 2, 6, 0, 20] (by decide +kernel) s

private theorem tr_28 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 6] +> s) (uBits [20] +> s) :=
  mkRule1 215 [10, 6] [20] (by decide +kernel) s

private theorem tr_29 (s : ListBlank (Fin 2)) :
    CarrySem false false 231 (uBits [20, 0, 20] +> s) (uBits [8, 0, 2, 0, 2, 28] +> s) :=
  mkRule0 231 [20, 0, 20] [8, 0, 2, 0, 2, 28] (by decide +kernel) s

private theorem tr_30 (s : ListBlank (Fin 2)) :
    CarrySem false true 299 (uBits [28, 0] +> s) (uBits [10, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule1 299 [28, 0] [10, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_31 (s : ListBlank (Fin 2)) :
    CarrySem false false 159 (uBits [10, 0] +> s) (uBits [8, 0, 6] +> s) :=
  mkRule0 159 [10, 0] [8, 0, 6] (by decide +kernel) s

private theorem tr_32 (s : ListBlank (Fin 2)) :
    CarrySem false true 287 (uBits [14, 6, 2] +> s) (uBits [10, 8, 0, 4] +> s) :=
  mkRule1 287 [14, 6, 2] [10, 8, 0, 4] (by decide +kernel) s

private theorem tr_33 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [0, 6, 4, 0] +> s) (uBits [0, 2, 12] +> s) :=
  mkRule1 215 [0, 6, 4, 0] [0, 2, 12] (by decide +kernel) s

private theorem tr_34 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 12] +> s) (uBits [26] +> s) :=
  mkRule1 215 [10, 12] [26] (by decide +kernel) s

private theorem tr_35 (s : ListBlank (Fin 2)) :
    CarrySem false false 371 (uBits [26, 2, 0, 6, 0, 6] +> s) (uBits [8, 0, 2, 0, 2, 0, 2, 6, 0,
      2, 14] +> s) :=
  mkRule0 371 [26, 2, 0, 6, 0, 6] [8, 0, 2, 0, 2, 0, 2, 6, 0, 2, 14] (by decide +kernel) s

private theorem tr_36 (s : ListBlank (Fin 2)) :
    CarrySem false true 159 (uBits [0, 2, 6] +> s) (uBits [0, 12] +> s) :=
  mkRule1 159 [0, 2, 6] [0, 12] (by decide +kernel) s

private theorem tr_37 (s : ListBlank (Fin 2)) :
    CarrySem false false 119 (uBits [0, 12] +> s) (uBits [20] +> s) :=
  mkRule0 119 [0, 12] [20] (by decide +kernel) s

private theorem tr_38 (s : ListBlank (Fin 2)) :
    CarrySem false true 287 (uBits [20, 0, 2] +> s) (uBits [10, 0, 2, 10] +> s) :=
  mkRule1 287 [20, 0, 2] [10, 0, 2, 10] (by decide +kernel) s

private theorem tr_39 (s : ListBlank (Fin 2)) :
    CarrySem false true 215 (uBits [10, 14] +> s) (uBits [28] +> s) :=
  mkRule1 215 [10, 14] [28] (by decide +kernel) s

private theorem tr_40 (s : ListBlank (Fin 2)) :
    CarrySem false false 243 (uBits [28, 0] +> s) (uBits [8, 0, 2, 0, 2, 0, 2, 0, 6] +> s) :=
  mkRule0 243 [28, 0] [8, 0, 2, 0, 2, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_41 (s : ListBlank (Fin 2)) :
    CarrySem false true 383 (uBits [14, 2, 10, 0] +> s) (uBits [10, 6, 14] +> s) :=
  mkRule1 383 [14, 2, 10, 0] [10, 6, 14] (by decide +kernel) s

private theorem tr_42 (s : ListBlank (Fin 2)) :
    CarrySem false false 231 (uBits [14, 6, 0] +> s) (uBits [8, 0, 2, 8, 0, 2] +> s) :=
  mkRule0 231 [14, 6, 0] [8, 0, 2, 8, 0, 2] (by decide +kernel) s

private theorem tr_43 (s : ListBlank (Fin 2)) :
    CarrySem false true 271 (uBits [8, 0, 2, 8] +> s) (uBits [8, 0, 14] +> s) :=
  mkRule1 271 [8, 0, 2, 8] [8, 0, 14] (by decide +kernel) s

private theorem tr_44 (s : ListBlank (Fin 2)) :
    CarrySem false false 175 (uBits [8, 0, 14] +> s) (uBits [8, 22] +> s) :=
  mkRule0 175 [8, 0, 14] [8, 22] (by decide +kernel) s

private theorem tr_45 (s : ListBlank (Fin 2)) :
    CarrySem false true 383 (uBits [8, 22, 0] +> s) (uBits [8, 10, 0, 2, 0, 6] +> s) :=
  mkRule1 383 [8, 22, 0] [8, 10, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_46 (s : ListBlank (Fin 2)) :
    CarrySem false true 315 (uBits [0, 6, 2, 6, 0] +> s) (uBits [0, 2, 6, 10] +> s) :=
  mkRule1 315 [0, 6, 2, 6, 0] [0, 2, 6, 10] (by decide +kernel) s

private theorem tr_47 (s : ListBlank (Fin 2)) :
    CarrySem false false 271 (uBits [20, 10, 6] +> s) (uBits [8, 0, 2, 0, 2, 8, 0, 12] +> s) :=
  mkRule0 271 [20, 10, 6] [8, 0, 2, 0, 2, 8, 0, 12] (by decide +kernel) s

private theorem tr_48 (s : ListBlank (Fin 2)) :
    CarrySem false true 371 (uBits [14, 2, 6, 6] +> s) (uBits [10, 6, 16] +> s) :=
  mkRule1 371 [14, 2, 6, 6] [10, 6, 16] (by decide +kernel) s

private theorem tr_49 (s : ListBlank (Fin 2)) :
    CarrySem false false 187 (uBits [16, 0] +> s) (uBits [8, 0, 2, 0, 6] +> s) :=
  mkRule0 187 [16, 0] [8, 0, 2, 0, 6] (by decide +kernel) s

private theorem tr_50 (s : ListBlank (Fin 2)) :
    CarrySem false true 399 (uBits [8, 14, 6, 6] +> s) (uBits [8, 10, 8, 0, 8] +> s) :=
  mkRule1 399 [8, 14, 6, 6] [8, 10, 8, 0, 8] (by decide +kernel) s

private theorem tr_51 (s : ListBlank (Fin 2)) :
    CarrySem false true 427 (uBits [14, 2, 2, 0, 6, 0, 2] +> s) (uBits [10, 6, 0, 2, 2, 10] +> s) :=
  mkRule1 427 [14, 2, 2, 0, 6, 0, 2] [10, 6, 0, 2, 2, 10] (by decide +kernel) s

private theorem tr_52 (s : ListBlank (Fin 2)) :
    CarrySem false false 187 (uBits [16, 10] +> s) (uBits [8, 0, 2, 0, 16] +> s) :=
  mkRule0 187 [16, 10] [8, 0, 2, 0, 16] (by decide +kernel) s

private theorem tr_53 (s : ListBlank (Fin 2)) :
    CarrySem false true 439 (uBits [8, 14, 16, 0] +> s) (uBits [8, 10, 8, 0, 2, 0, 6] +> s) :=
  mkRule1 439 [8, 14, 16, 0] [8, 10, 8, 0, 2, 0, 6] (by decide +kernel) s

private theorem eat_M06_2 (s : ListBlank (Fin 2))
    (h : TailHalts false (uBits [0, 6, 6, 6] +> s)) :
    TailHalts false (uBits [0, 6, 6, 6, 0, 6, 0, 6] +> s) := by
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6, 0, 6, 0, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := [0, 6, 0, 6]) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8, 0, 6, 0, 6]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8, 0, 6, 0, 6])
    tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := [0, 6]) tr_04 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14, 0, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [14, 0, 6]) tr_06 ?_
  refine th_rule (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := [0, 6]) tr_07 ?_
  refine th_spawn1 .S0 (rest := [0, 20, 0, 6]) ?_
  refine th_rule (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_08 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 6]) tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 6]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 6, 6]) ?_
  exact h

private theorem eat_M06_2_pow (s : ListBlank (Fin 2))
    (h : TailHalts false (uBits [0, 6, 6, 6] +> s)) :
    TailHalts false (uBits [0, 6, 6, 6] +> ((u06 ^ 2) +> s)) := by
  have h2 : u06 ^ 2 = uBits [0, 6, 0, 6] := by decide
  have heq : uBits [0, 6, 6, 6] +> ((u06 ^ 2) +> s) =
      uBits [0, 6, 6, 6, 0, 6, 0, 6] +> s := by
    rw [h2, ← uBits_append [0, 6, 6, 6] [0, 6, 0, 6] s]
    rfl
  rw [heq]
  exact eat_M06_2 s h

private theorem eat_M06_2k : ∀ (k : ℕ) (s : ListBlank (Fin 2)),
    TailHalts false (uBits [0, 6, 6, 6] +> s) →
    TailHalts false (uBits [0, 6, 6, 6] +> ((u06 ^ (2 * k)) +> s))
  | 0, s, h => by
      simpa [list_pow_succ, list_pow_zero, list_pow_one, ListBlank.append] using h
  | k + 1, s, h => by
      have hpow : (u06 ^ (2 * (k + 1))) +> s = (u06 ^ 2) +> ((u06 ^ (2 * k)) +> s) := by
        rw [show 2 * (k + 1) = 2 + 2 * k by omega, pow_add_list, app_assoc]
      rw [hpow]
      exact eat_M06_2_pow ((u06 ^ (2 * k)) +> s) (eat_M06_2k k s h)

/-! ### Part 4: Compressed Symbolic Era-2 Halting Chain (223 ops covering 3,542 carries /
  ~1.27e758 steps!) -/

private inductive Chunk
  | m06 (k : ℕ)
  | u (xs : List ℕ)

private def eChunks : List Chunk → ListBlank (Fin 2)
  | [] => default
  | .m06 k :: cs => (u06 ^ k) +> eChunks cs
  | .u xs :: cs => uBits xs +> eChunks cs

private theorem th_peel_u {q : Bool} {hd xs : List ℕ} {cs : List Chunk}
    (h : TailHalts q (uBits (hd ++ xs) +> eChunks cs)) :
    TailHalts q (uBits hd +> eChunks (.u xs :: cs)) := by
  dsimp only [eChunks]
  rw [← uBits_append hd xs (eChunks cs)]
  exact h

private theorem th_peel_m06_1 {q : Bool} {hd : List ℕ} {cs : List Chunk}
    (h : TailHalts q (uBits (hd ++ [0, 6]) +> eChunks cs)) :
    TailHalts q (uBits hd +> eChunks (.m06 1 :: cs)) := by
  dsimp only [eChunks]
  have h1 : u06 ^ 1 = uBits [0, 6] := by
    simp [list_pow_succ, list_pow_zero, list_pow_one, List.append_eq, u06_eq_uBits]
  rw [h1, ← uBits_append hd [0, 6] (eChunks cs)]
  exact h

private theorem th_peel_m06_succ {q : Bool} {hd : List ℕ} {n : ℕ} {cs : List Chunk}
    (h : TailHalts q (uBits (hd ++ [0, 6]) +> eChunks (.m06 n :: cs))) :
    TailHalts q (uBits hd +> eChunks (.m06 (n + 1) :: cs)) := by
  dsimp only [eChunks] at h ⊢
  have hstep : (u06 ^ (n + 1)) +> eChunks cs = uBits [0, 6] +> ((u06 ^ n) +> eChunks cs) := by
    rw [pow_succ_left u06 n, app_assoc]
    exact congrArg (· +> ((u06 ^ n) +> eChunks cs)) u06_eq_uBits
  rw [hstep, ← uBits_append hd [0, 6] ((u06 ^ n) +> eChunks cs)]
  exact h

private theorem th_loop_even (m : ℕ) {cs : List Chunk}
    (h : TailHalts false (uBits [0, 6, 6, 6] +> eChunks cs)) :
    TailHalts false (uBits [0, 6, 6, 6] +> eChunks (.m06 (2 * m) :: cs)) :=
  eat_M06_2k m (eChunks cs) h

private theorem th_loop_odd (m : ℕ) {cs : List Chunk}
    (h : TailHalts false (uBits [0, 6, 6, 6] +> eChunks (.m06 1 :: cs))) :
    TailHalts false (uBits [0, 6, 6, 6] +> eChunks (.m06 (2 * m + 1) :: cs)) := by
  dsimp only [eChunks] at h ⊢
  rw [pow_add_list u06 (2 * m) 1, app_assoc]
  exact eat_M06_2k m ((u06 ^ 1) +> eChunks cs) h

private def era2Chunks : List Chunk :=
  [ .m06 369, .u [0, 2, 0, 2, 0, 6, 0, 6],
    .m06 137, .u [0, 2, 0, 2, 0, 6, 0, 6],
    .m06 50,  .u [0, 2, 0, 2, 0, 6, 0, 6],
    .m06 17,  .u [0, 2, 0, 10],
    .m06 6,   .u [0, 2, 0, 6, 6],
    .m06 1,   .u [0, 2, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9] ]

private theorem tail_era2_halts : TailHalts false (uBits [] +> eChunks era2Chunks) := by
  dsimp only [era2Chunks]
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := []) tr_00 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [14, 0, 6]) (rhs := [10, 14]) (rest := []) tr_11 ?_
  refine th_rule (lhs := [10, 14]) (rhs := [8, 0, 20]) (rest := []) tr_12 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [8, 0, 20, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_13 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_even 183 ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 2, 0, 6, 0, 6])
    tr_15 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 2, 0, 6, 0, 6]) tr_06 ?_
  refine th_rule (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 2, 0, 6, 0, 6])
    tr_16 ?_
  refine th_spawn1 .S0 (rest := [0, 16, 0, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [2, 0, 6, 0, 6])
    tr_17 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 2, 0, 6, 0, 6]) tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 2, 0, 6, 0,
    6]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 2, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [2, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 2, 2, 0, 6, 0, 6]) (rhs := [10, 6, 0, 2, 2, 14]) (rest := []) tr_18 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [0, 2, 2, 14]) tr_19 ?_
  refine th_spawn1 .S4 (rest := [0, 2, 2, 14]) ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [2, 14]) tr_05 ?_
  refine th_rule (lhs := [10, 2]) (rhs := [16]) (rest := [14]) tr_20 ?_
  refine th_rule (lhs := [16, 14]) (rhs := [8, 0, 2, 0, 20]) (rest := []) tr_21 ?_
  refine th_rule (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [20]) tr_22 ?_
  refine th_rule (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [20]) tr_23 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [8, 14, 20, 0, 6]) (rhs := [8, 10, 8, 0, 2, 0, 2, 14]) (rest := []) tr_24
    ?_
  refine th_rule (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 2, 0, 2, 14]) tr_25 ?_
  refine th_rule (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2,
    14]) tr_26 ?_
  refine th_spawn2 .S0 (rest := [0, 6, 2, 0, 2, 14]) ?_
  refine th_rule (lhs := [0, 6, 2, 0, 2, 14]) (rhs := [0, 2, 6, 0, 20]) (rest := []) tr_27 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [6, 0, 20]) tr_05 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [20]) (rest := [0, 20]) tr_28 ?_
  refine th_rule (lhs := [20, 0, 20]) (rhs := [8, 0, 2, 0, 2, 28]) (rest := []) tr_29 ?_
  refine th_spawn1 .S0 (rest := [28]) ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [28, 0]) (rhs := [10, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_30 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 0, 2, 0, 6, 6]) tr_31 ?_
  refine th_spawn1 .S1 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_odd 67 ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_m06_1 ?_
  refine th_rule (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := []) tr_04 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [14]) tr_06 ?_
  refine th_rule (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := []) tr_07 ?_
  refine th_spawn1 .S0 (rest := [0, 20]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2, 0, 6, 0,
    6]) tr_08 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 2, 0, 2, 0, 6,
    0, 6]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 6, 2, 0, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 2, 0, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 2]) (rhs := [10, 8, 0, 4]) (rest := [0, 2, 0, 6, 0, 6]) tr_32 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 4, 0, 2, 0, 6, 0, 6]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [4, 0, 2, 0, 6, 0,
    6]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 4, 0, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6, 4, 0]) (rhs := [0, 2, 12]) (rest := [2, 0, 6, 0, 6]) tr_33 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [12, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 12]) (rhs := [26]) (rest := [2, 0, 6, 0, 6]) tr_34 ?_
  refine th_rule (lhs := [26, 2, 0, 6, 0, 6]) (rhs := [8, 0, 2, 0, 2, 0, 2, 6, 0, 2, 14]) (rest :=
    []) tr_35 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 6, 0, 2, 14]) ?_
  refine th_rule (lhs := [0, 2, 6]) (rhs := [0, 12]) (rest := [0, 2, 14]) tr_36 ?_
  refine th_rule (lhs := [0, 12]) (rhs := [20]) (rest := [0, 2, 14]) tr_37 ?_
  refine th_rule (lhs := [20, 0, 2]) (rhs := [10, 0, 2, 10]) (rest := [14]) tr_38 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 10, 14]) tr_31 ?_
  refine th_spawn1 .S1 (rest := [10, 14]) ?_
  refine th_rule (lhs := [10, 14]) (rhs := [28]) (rest := []) tr_39 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [28, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_40 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_odd 24 ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_m06_1 ?_
  refine th_rule (lhs := [0, 6, 8, 0, 6]) (rhs := [0, 2, 8, 14]) (rest := []) tr_04 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 14]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [14]) tr_06 ?_
  refine th_rule (lhs := [22, 14]) (rhs := [8, 0, 2, 0, 2, 0, 20]) (rest := []) tr_07 ?_
  refine th_spawn1 .S0 (rest := [0, 20]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 20, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 2, 0, 6, 0,
    6]) tr_08 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 6, 2, 0, 2, 0, 6, 0, 6])
    tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [6, 2, 0, 2, 0, 6,
    0, 6]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 6, 2, 0, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 2, 0, 2, 0, 6, 0, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 2]) (rhs := [10, 8, 0, 4]) (rest := [0, 2, 0, 6, 0, 6]) tr_32 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 4, 0, 2, 0, 6, 0, 6]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [4, 0, 2, 0, 6, 0,
    6]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 4, 0, 2, 0, 6, 0, 6]) ?_
  refine th_rule (lhs := [0, 6, 4, 0]) (rhs := [0, 2, 12]) (rest := [2, 0, 6, 0, 6]) tr_33 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [12, 2, 0, 6, 0, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 12]) (rhs := [26]) (rest := [2, 0, 6, 0, 6]) tr_34 ?_
  refine th_rule (lhs := [26, 2, 0, 6, 0, 6]) (rhs := [8, 0, 2, 0, 2, 0, 2, 6, 0, 2, 14]) (rest :=
    []) tr_35 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 6, 0, 2, 14]) ?_
  refine th_rule (lhs := [0, 2, 6]) (rhs := [0, 12]) (rest := [0, 2, 14]) tr_36 ?_
  refine th_rule (lhs := [0, 12]) (rhs := [20]) (rest := [0, 2, 14]) tr_37 ?_
  refine th_rule (lhs := [20, 0, 2]) (rhs := [10, 0, 2, 10]) (rest := [14]) tr_38 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [8, 0, 6]) (rest := [2, 10, 14]) tr_31 ?_
  refine th_spawn1 .S1 (rest := [10, 14]) ?_
  refine th_rule (lhs := [10, 14]) (rhs := [28]) (rest := []) tr_39 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [28, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_40 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_loop_even 8 ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 10]) tr_15 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 10]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 10]) tr_06 ?_
  refine th_rule (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 10]) tr_16 ?_
  refine th_spawn1 .S0 (rest := [0, 16, 0, 10]) ?_
  refine th_rule (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [10]) tr_17 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 10]) tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 10]) tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 10]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 2, 10]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [2, 10]) tr_00 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [14, 2, 10, 0]) (rhs := [10, 6, 14]) (rest := [6]) tr_41 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [14, 6]) tr_19 ?_
  refine th_spawn1 .S4 (rest := [14, 6]) ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [14, 6, 0]) (rhs := [8, 0, 2, 8, 0, 2]) (rest := [6]) tr_42 ?_
  refine th_rule (lhs := [8, 0, 2, 8]) (rhs := [8, 0, 14]) (rest := [0, 2, 6]) tr_43 ?_
  refine th_rule (lhs := [8, 0, 14]) (rhs := [8, 22]) (rest := [0, 2, 6]) tr_44 ?_
  refine th_rule (lhs := [8, 22, 0]) (rhs := [8, 10, 0, 2, 0, 6]) (rest := [2, 6]) tr_45 ?_
  refine th_spawn1 .S5 (rest := [0, 6, 2, 6]) ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [0, 6, 2, 6, 0]) (rhs := [0, 2, 6, 10]) (rest := [6]) tr_46 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [6, 10, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [20]) (rest := [10, 6]) tr_28 ?_
  refine th_rule (lhs := [20, 10, 6]) (rhs := [8, 0, 2, 0, 2, 8, 0, 12]) (rest := []) tr_47 ?_
  refine th_spawn1 .S0 (rest := [8, 0, 12]) ?_
  refine th_spawn1 .S4 (rest := []) ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := []) tr_00 ?_
  refine th_peel_m06_succ ?_
  refine th_rule (lhs := [14, 0, 6]) (rhs := [10, 14]) (rest := []) tr_11 ?_
  refine th_rule (lhs := [10, 14]) (rhs := [8, 0, 20]) (rest := []) tr_12 ?_
  refine th_peel_m06_1 ?_
  refine th_rule (lhs := [8, 0, 20, 0]) (rhs := [8, 0, 2, 0, 2, 0, 2, 0, 6]) (rest := [6]) tr_13 ?_
  refine th_spawn1 .S0 (rest := [0, 2, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 2, 0]) (rhs := [0, 6]) (rest := [6, 6]) tr_14 ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 6, 6]) (rhs := [10, 8, 0, 8]) (rest := []) tr_01 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [8, 0, 14]) (rest := [0, 8]) tr_02 ?_
  refine th_rule (lhs := [8, 0, 14, 0]) (rhs := [8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_03 ?_
  refine th_spawn1 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 6, 6]) tr_15 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 6, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 6, 6]) tr_06 ?_
  refine th_rule (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 6, 6]) tr_16 ?_
  refine th_spawn1 .S0 (rest := [0, 16, 0, 6, 6]) ?_
  refine th_rule (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [6, 6]) tr_17 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 6, 6]) tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 6, 6]) tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 6, 6]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 2, 6, 6]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [2, 6, 6]) tr_00 ?_
  refine th_rule (lhs := [14, 2, 6, 6]) (rhs := [10, 6, 16]) (rest := []) tr_48 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [16]) tr_19 ?_
  refine th_spawn1 .S4 (rest := [16]) ?_
  refine th_peel_m06_1 ?_
  refine th_rule (lhs := [16, 0]) (rhs := [8, 0, 2, 0, 6]) (rest := [6]) tr_49 ?_
  refine th_rule (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [6, 6]) tr_22 ?_
  refine th_rule (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [6, 6]) tr_23 ?_
  refine th_rule (lhs := [8, 14, 6, 6]) (rhs := [8, 10, 8, 0, 8]) (rest := []) tr_50 ?_
  refine th_rule (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 8]) tr_25 ?_
  refine th_rule (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [8]) tr_26 ?_
  refine th_spawn2 .S0 (rest := [0, 6, 8]) ?_
  refine th_peel_u ?_
  refine th_rule (lhs := [0, 6, 8, 0, 2]) (rhs := [0, 2, 8, 10]) (rest := [0, 2, 0, 6, 0, 2, 0, 2,
    0, 9]) tr_15 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [8, 10, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9])
    tr_05 ?_
  refine th_rule (lhs := [10, 8]) (rhs := [22]) (rest := [10, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9]) tr_06
    ?_
  refine th_rule (lhs := [22, 10]) (rhs := [8, 0, 2, 0, 2, 0, 16]) (rest := [0, 2, 0, 6, 0, 2, 0,
    2, 0, 9]) tr_16 ?_
  refine th_spawn1 .S0 (rest := [0, 16, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9]) ?_
  refine th_rule (lhs := [0, 16, 0]) (rhs := [0, 2, 0, 2, 0, 2, 0, 2]) (rest := [2, 0, 6, 0, 2, 0,
    2, 0, 9]) tr_17 ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [0, 2, 0, 2, 0, 2, 2, 0, 6, 0, 2, 0, 2, 0,
    9]) tr_05 ?_
  refine th_rule (lhs := [10, 0]) (rhs := [14]) (rest := [2, 0, 2, 0, 2, 2, 0, 6, 0, 2, 0, 2, 0,
    9]) tr_09 ?_
  refine th_rule (lhs := [14, 2, 0, 2, 0]) (rhs := [8, 0, 2, 6, 0, 6]) (rest := [2, 2, 0, 6, 0, 2,
    0, 2, 0, 9]) tr_10 ?_
  refine th_spawn1 .S6 (rest := [0, 6, 2, 2, 0, 6, 0, 2, 0, 2, 0, 9]) ?_
  refine th_rule (lhs := [0, 6]) (rhs := [14]) (rest := [2, 2, 0, 6, 0, 2, 0, 2, 0, 9]) tr_00 ?_
  refine th_rule (lhs := [14, 2, 2, 0, 6, 0, 2]) (rhs := [10, 6, 0, 2, 2, 10]) (rest := [0, 2, 0,
    9]) tr_51 ?_
  refine th_rule (lhs := [10, 6]) (rhs := [8, 0, 12]) (rest := [0, 2, 2, 10, 0, 2, 0, 9]) tr_19 ?_
  refine th_spawn1 .S4 (rest := [0, 2, 2, 10, 0, 2, 0, 9]) ?_
  refine th_rule (lhs := [0, 2]) (rhs := [10]) (rest := [2, 10, 0, 2, 0, 9]) tr_05 ?_
  refine th_rule (lhs := [10, 2]) (rhs := [16]) (rest := [10, 0, 2, 0, 9]) tr_20 ?_
  refine th_rule (lhs := [16, 10]) (rhs := [8, 0, 2, 0, 16]) (rest := [0, 2, 0, 9]) tr_52 ?_
  refine th_rule (lhs := [8, 0, 2, 0]) (rhs := [8, 0, 6]) (rest := [16, 0, 2, 0, 9]) tr_22 ?_
  refine th_rule (lhs := [8, 0, 6]) (rhs := [8, 14]) (rest := [16, 0, 2, 0, 9]) tr_23 ?_
  refine th_rule (lhs := [8, 14, 16, 0]) (rhs := [8, 10, 8, 0, 2, 0, 6]) (rest := [2, 0, 9]) tr_53
    ?_
  refine th_rule (lhs := [8, 10, 8]) (rhs := [8, 8, 0, 14]) (rest := [0, 2, 0, 6, 2, 0, 9]) tr_25 ?_
  refine th_rule (lhs := [8, 8, 0, 14, 0]) (rhs := [8, 8, 0, 2, 0, 2, 0, 6]) (rest := [2, 0, 6, 2,
    0, 9]) tr_26 ?_
  refine th_spawn2 .S0 (rest := [0, 6, 2, 0, 6, 2, 0, 9]) ?_
  exact TailHalts.halt halt_bottom

private theorem eL_u_cons_eq (xs : List ℕ) (rest : List LTok) :
    eL (xs.map LTok.U ++ rest) = uBits xs +> eL rest := by
  induction xs with
  | nil => rfl
  | cons a tl ih =>
      rw [List.map_cons, List.cons_append, eL_u, ih, ← uBits_append [a] tl (eL rest)]
      rfl

private theorem eL_m06_match (k n : ℕ) (hkn : k + 1 = n) (xs : List LTok) (cs : List Chunk)
    (h : eL xs = eChunks cs) :
    eL (.M06 k :: xs) = eChunks (.m06 n :: cs) := by
  subst hkn
  exact congrArg ((u06 ^ (k + 1)) +> ·) h

private theorem eL_u_match (us : List ℕ) (xs : List LTok) (cs : List Chunk)
    (h : eL xs = eChunks cs) :
    eL (us.map LTok.U ++ xs) = eChunks (.u us :: cs) := by
  dsimp only [eChunks]
  rw [eL_u_cons_eq, h]

private theorem eL_era2_eq :
    eL [.M06 368, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
        .M06 136, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
        .M06 49,  .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
        .M06 16,  .U 0, .U 2, .U 0, .U 10,
        .M06 5,   .U 0, .U 2, .U 0, .U 6, .U 6,
        .M06 0,   .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 2, .U 0, .U 2, .U 0, .U 9] =
      eChunks era2Chunks := by
  dsimp only [era2Chunks]
  refine eL_m06_match 368 369 rfl _ _ ?_
  refine eL_u_match [0, 2, 0, 2, 0, 6, 0, 6] _ _ ?_
  refine eL_m06_match 136 137 rfl _ _ ?_
  refine eL_u_match [0, 2, 0, 2, 0, 6, 0, 6] _ _ ?_
  refine eL_m06_match 49 50 rfl _ _ ?_
  refine eL_u_match [0, 2, 0, 2, 0, 6, 0, 6] _ _ ?_
  refine eL_m06_match 16 17 rfl _ _ ?_
  refine eL_u_match [0, 2, 0, 10] _ _ ?_
  refine eL_m06_match 5 6 rfl _ _ ?_
  refine eL_u_match [0, 2, 0, 6, 6] _ _ ?_
  refine eL_m06_match 0 1 rfl _ _ ?_
  exact eL_u_match [0, 2, 0, 2, 0, 6, 0, 2, 0, 2, 0, 9] [] [] rfl

private theorem encode_cp5_eq :
    encodeBase cp5 =
      evalWin (topBits false +> layerBits 0 .S0 (layerBits 0 .S4 (eChunks era2Chunks)))
        default 1 true [] [0] := by
  dsimp only [cp5, encodeBase, eW]
  have h1 : eL [.U 11, .U 8, .U 0, .U 2, .U 0, .U 2, .U 8, .U 0, .U 12,
       .M06 368, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 136, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 49,  .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 16,  .U 0, .U 2, .U 0, .U 10,
       .M06 5,   .U 0, .U 2, .U 0, .U 6, .U 6,
       .M06 0,   .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 2, .U 0, .U 2, .U 0, .U 9] =
      topBits false +> layerBits 0 .S0 (layerBits 0 .S4 (eChunks era2Chunks)) := by
    have hp_l := eL_u_cons_eq [11, 8, 0, 2, 0, 2, 8, 0, 12]
      [.M06 368, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 136, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 49,  .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 16,  .U 0, .U 2, .U 0, .U 10,
       .M06 5,   .U 0, .U 2, .U 0, .U 6, .U 6,
       .M06 0,   .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 2, .U 0, .U 2, .U 0, .U 9]
    have hsplit : eL [.U 11, .U 8, .U 0, .U 2, .U 0, .U 2, .U 8, .U 0, .U 12,
       .M06 368, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 136, .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 49,  .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 6,
       .M06 16,  .U 0, .U 2, .U 0, .U 10,
       .M06 5,   .U 0, .U 2, .U 0, .U 6, .U 6,
       .M06 0,   .U 0, .U 2, .U 0, .U 2, .U 0, .U 6, .U 0, .U 2, .U 0, .U 2, .U 0, .U 9] =
      uBits [11, 8, 0, 2, 0, 2, 8, 0, 12] +> eChunks era2Chunks := by
      rw [← eL_era2_eq]
      exact hp_l
    rw [hsplit]
    have hp : uBits [11, 8, 0, 2, 0, 2, 8, 0, 12] =
        topBits false ++ ((u8 ^ 1) ++ (sepBits .S0 ++ ((u8 ^ 1) ++ sepBits .S4))) := by decide
    rw [hp, app_assoc, app_assoc, app_assoc, app_assoc]
    rfl
  rw [h1]

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

private theorem is_halt_proof : IsHalt target_tm := by
  have h1 : HaltsFrom (encodeBase cp5) := by
    rw [encode_cp5_eq]
    exact lift_top (p := false) (km1 := 0) (j := .S0) (lift_layer (km1 := 0) (j := .S4)
      tail_era2_halts)
  exact halts_of_rs init_reaches_cp5 h1



private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB` halts from the blank tape. -/
theorem is_halt : IsHalt target := by
  rw [← target_tm_eq_target]
  exact is_halt_proof

end

end BusyBeaver.M_1RB1LE_0LC1RE_HHH1LD_0RD1LA_0RF1RF_1RA0LB
