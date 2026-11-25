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
import BusyBeaver.Calculi.ProofKit


/-!
# Busy Beaver Machine `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`, `BusyBeaver.ProofKit`
and defines `target_tm` for `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Impl

/-!
## Section 1: Window Soundness & Macro Stepper (`step284`)
-/

def evalWin (l r : ListBlank (Fin 2)) (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2)) :
    Cfg (Fin 2) (Fin 6) :=
  if dR then (ls +> l) {{q}}> (rs +> r) else (ls +> l) <{{q}} (rs +> r)

def stepWin (bL bR : Bool) : Fin 6 × Bool × List (Fin 2) × List (Fin 2) →
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
        | some (some q', Stmt.write w Dir.left) => some (q', false, [], w :: rs)
        | _ => none
      else none

def multiStepWin (bL bR : Bool) : ℕ → Fin 6 × Bool × List (Fin 2) × List (Fin 2) →
    Option (Fin 6 × Bool × List (Fin 2) × List (Fin 2))
  | 0, st => some st
  | n + 1, st => (stepWin bL bR st).bind (multiStepWin bL bR n)

theorem stepWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
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
          exact h_exec a ls rs₀ (by simp [evalWin, ListBlank.append]) hs
      | nil =>
          cases hbR : bR with
          | false => simp [hbR] at hs
          | true =>
              simp only [hbR, ↓reduceIte] at hs
              have hr0 := hR hbR; subst hr0
              have hd0 : (default : ListBlank (Fin 2)).head = 0 := rfl
              have ht0 : (default : ListBlank (Fin 2)).tail = default := rfl
              exact h_exec 0 ls [] (by simp [evalWin, ListBlank.append, hd0, ht0]) hs
  | false =>
      cases ls with
      | cons a ls₀ =>
          exact h_exec a ls₀ rs (by simp [evalWin, ListBlank.append]) hs
      | nil =>
          cases hbL : bL with
          | false => simp [hbL] at hs
          | true =>
              simp only [hbL, ↓reduceIte] at hs
              have hl0 := hL hbL; subst hl0
              have hd0 : (default : ListBlank (Fin 2)).head = 0 := rfl
              have ht0 : (default : ListBlank (Fin 2)).tail = default := rfl
              exact h_exec 0 [] rs (by simp [evalWin, ListBlank.append, hd0, ht0]) hs

theorem multiStepWin_sound {bL bR : Bool} {l r : ListBlank (Fin 2)}
    (hL : bL = true → l = default) (hR : bR = true → r = default) :
    ∀ (n : ℕ) {q q' : Fin 6} {dR dR' : Bool} {ls rs ls' rs' : List (Fin 2)},
      multiStepWin bL bR n (q, dR, ls, rs) = some (q', dR', ls', rs') →
      (evalWin l r q dR ls rs) [target_tm]⊢^{n} (evalWin l r q' dR' ls' rs')
  | 0, _, _, _, _, _, _, _, _, h => by
      unfold multiStepWin at h
      injection h with ht
      injection ht with hq hd
      injection hd with hdR hls
      injection hls with hls' hrs'
      subst hq hdR hls' hrs'; rfl
  | n + 1, q, q', dR, dR', ls, rs, ls', rs', h => by
      unfold multiStepWin at h
      rcases hsw : stepWin bL bR (q, dR, ls, rs) with _ | ⟨q₁, dR₁, ls₁, rs₁⟩
      · rw [hsw] at h; nomatch h
      · rw [hsw, Option.bind_some] at h
        have h1 : (evalWin l r q dR ls rs) [target_tm]⊢^{1} (evalWin l r q₁ dR₁ ls₁ rs₁) :=
          stepWin_sound hL hR hsw
        have h2 := multiStepWin_sound hL hR n h
        rw [Nat.add_comm n 1]
        exact multiStep_trans h1 h2

theorem runWinPlus {bL bR : Bool} {l r : ListBlank (Fin 2)} {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (n : ℕ) (hn : 0 < n) (hL : bL = true → l = default) (hR : bR = true → r = default)
    (q : Fin 6) (dR : Bool) (ls rs : List (Fin 2))
    (q' : Fin 6) (dR' : Bool) (ls' rs' : List (Fin 2))
    (h₁ : c₁ = evalWin l r q dR ls rs) (h₂ : c₂ = evalWin l r q' dR' ls' rs')
    (hw : multiStepWin bL bR n (q, dR, ls, rs) = some (q', dR', ls', rs')) :
    c₁ [target_tm]⊢⁺ c₂ :=
  ⟨n, hn, h₁ ▸ h₂ ▸ multiStepWin_sound hL hR n hw⟩

inductive Ones where
  | o1 | o2 | o3

inductive RSym where
  | r0 | r1 | r2

inductive Mode where
  | br | br1 | dl

abbrev State := Mode × List (ℕ × Ones) × List RSym

def consZeros : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, s => s
  | n + 1, s => (0 : Fin 2) >> consZeros n s

def encOnes : Ones → ListBlank (Fin 2) → ListBlank (Fin 2)
  | .o1, s => (1 : Fin 2) >> s
  | .o2, s => (1 : Fin 2) >> (1 : Fin 2) >> s
  | .o3, s => (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> s

def encL : List (ℕ × Ones) → ListBlank (Fin 2)
  | [] => default
  | (a, o) :: L => consZeros (a + 1) (encOnes o (encL L))

def encR : List RSym → ListBlank (Fin 2)
  | [] => default
  | .r0 :: R => (0 : Fin 2) >> (1 : Fin 2) >> encR R
  | .r1 :: R => (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encR R
  | .r2 :: R => (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encR R

def evalCfg : State → Cfg (Fin 2) (Fin 6)
  | (.br, L, R) => (encL L) {{1}}> (encR R)
  | (.br1, L, R) => ((1 : Fin 2) >> encL L) {{1}}> (encR R)
  | (.dl, L, R) => (encL L) <{{3}} (encR R)

def addZ : List (ℕ × Ones) → List (ℕ × Ones)
  | [] => []
  | (a, o) :: L => (a + 1, o) :: L

theorem zero_cons_encL (L : List (ℕ × Ones)) :
    (0 : Fin 2) >> encL L = encL (addZ L) := by
  cases L with
  | nil => exact z00
  | cons p L' => rcases p with ⟨a, o⟩; rfl

theorem encL_eq_zero_tail (L : List (ℕ × Ones)) :
    encL L = (0 : Fin 2) >> (encL L).tail := by
  cases L with
  | nil => exact z00.symm
  | cons p L' =>
      rcases p with ⟨a, o⟩
      change (0 : Fin 2) >> consZeros a (encOnes o (encL L')) =
        (0 : Fin 2) >> ((0 : Fin 2) >> consZeros a (encOnes o (encL L'))).tail
      rw [Turing.ListBlank.tail_cons]

def step284 : State → Option State
  | (.br, L, []) => some (.dl, addZ L, [])
  | (.br, L, .r0 :: R) => some (.br1, addZ L, R)
  | (.br, L, .r1 :: R) => some (.br, (0, .o1) :: addZ L, R)
  | (.br, L, .r2 :: R) => some (.dl, addZ L, .r1 :: R)
  | (.br1, L, []) => some (.dl, (0, .o1) :: L, [])
  | (.br1, L, .r0 :: R) => some (.br1, (0, .o1) :: L, R)
  | (.br1, L, .r1 :: R) => some (.br, (0, .o1) :: (0, .o1) :: L, R)
  | (.br1, L, .r2 :: R) => some (.dl, (0, .o1) :: L, .r1 :: R)
  | (.dl, [], R) => some (.br1, [], .r0 :: R)
  | (.dl, [(0, .o1)], R) => some (.dl, [], .r1 :: R)
  | (.dl, (0, .o1) :: (0, .o1) :: L, R) => some (.dl, L, .r2 :: R)
  | (.dl, (0, .o1) :: (0, .o2) :: L, R) => some (.br, addZ L, .r2 :: R)
  | (.dl, (0, .o1) :: (0, .o3) :: L, R) => some (.br, (0, .o1) :: L, .r2 :: R)
  | (.dl, (0, .o1) :: (a + 1, o) :: L, R) => some (.dl, (a, o) :: L, .r1 :: R)
  | (.dl, (0, .o2) :: L, R) => some (.br, (1, .o1) :: L, R)
  | (.dl, (0, .o3) :: L, R) => some (.br, (1, .o2) :: L, R)
  | (.dl, [(1, .o1)], R) => some (.dl, [], .r0 :: .r0 :: R)
  | (.dl, (1, .o1) :: (0, .o1) :: L, R) => some (.br, addZ L, .r0 :: .r0 :: R)
  | (.dl, (1, .o1) :: (0, .o2) :: L, R) => some (.br, (0, .o1) :: L, .r0 :: .r0 :: R)
  | (.dl, (1, .o1) :: (0, .o3) :: L, R) => some (.br, (0, .o2) :: L, .r0 :: .r0 :: R)
  | (.dl, (1, .o1) :: (a + 1, o) :: L, R) => some (.dl, (a, o) :: L, .r0 :: .r0 :: R)
  | (.dl, (1, .o2) :: _, _) => none
  | (.dl, (1, .o3) :: _, _) => none
  | (.dl, (2, .o1) :: L, R) => some (.br1, (0, .o2) :: L, R)
  | (.dl, (2, .o2) :: L, R) => some (.br1, (0, .o3) :: L, R)
  | (.dl, (2, .o3) :: _, _) => none
  | (.dl, (a + 3, o) :: L, R) => some (.br1, (a, o) :: L, .r0 :: R)

theorem step284_sound {s₁ s₂ : State} (h : step284 s₁ = some s₂) :
    (evalCfg s₁) [target_tm]⊢⁺ (evalCfg s₂) := by
  rcases s₁ with ⟨m, L, R⟩
  cases m with
  | br =>
      cases R with
      | nil =>
          injection h with hs; subst hs
          exact runWinPlus (bL := false) (bR := true) (l := encL L) (r := default) 2 (by omega)
            (fun hc => nomatch hc) (fun _ => rfl) 1 true [] [] 3 false [0] [0] rfl
            (by change ((encL (addZ L)) <{{3}} (default : ListBlank (Fin 2))) =
                  (((0 : Fin 2) >> encL L) <{{3}} ((0 : Fin 2) >> (default : ListBlank (Fin 2))))
                rw [zero_cons_encL, z00]) rfl
      | cons r R' =>
          cases r with
          | r0 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L) (r := encR R') 2 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [] [0, 1] 1 true [1, 0] [] rfl
                (by change (((1 : Fin 2) >> encL (addZ L)) {{1}}> encR R') =
                      (((1 : Fin 2) >> (0 : Fin 2) >> encL L) {{1}}> encR R')
                    rw [zero_cons_encL]) rfl
          | r1 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L) (r := encR R') 3 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [] [0, 1, 1] 1 true [0, 1, 0]
                  [] rfl
                (by change (((0 : Fin 2) >> (1 : Fin 2) >> encL (addZ L)) {{1}}> encR R') =
                      (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encL L) {{1}}> encR R')
                    rw [zero_cons_encL]) rfl
          | r2 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L)
                (r := (1 : Fin 2) >> (1 : Fin 2) >> encR R') 2 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [] [0, 0] 3 false [0] [0] rfl
                (by change ((encL (addZ L)) <{{3}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                  encR R')) =
                      (((0 : Fin 2) >> encL L) <{{3}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2)
                        >> encR R'))
                    rw [zero_cons_encL]) rfl
  | br1 =>
      cases R with
      | nil =>
          injection h with hs; subst hs
          exact runWinPlus (bL := false) (bR := true) (l := encL L) (r := default) 2 (by omega)
            (fun hc => nomatch hc) (fun _ => rfl) 1 true [1] [] 3 false [0, 1] [0] rfl
            (by change (((0 : Fin 2) >> (1 : Fin 2) >> encL L) <{{3}} (default : ListBlank (Fin
              2))) =
                  (((0 : Fin 2) >> (1 : Fin 2) >> encL L) <{{3}} ((0 : Fin 2) >> (default :
                    ListBlank (Fin 2))))
                rw [z00]) rfl
      | cons r R' =>
          cases r with
          | r0 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L) (r := encR R') 2 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [1] [0, 1] 1 true [1, 0, 1]
                  [] rfl rfl rfl
          | r1 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L) (r := encR R') 3 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [1] [0, 1, 1] 1 true [0, 1,
                  0, 1] [] rfl rfl rfl
          | r2 =>
              injection h with hs; subst hs
              exact runWinPlus (bL := false) (bR := false) (l := encL L)
                (r := (1 : Fin 2) >> (1 : Fin 2) >> encR R') 2 (by omega)
                (fun hc => nomatch hc) (fun hc => nomatch hc) 1 true [1] [0, 0] 3 false [0, 1] [0]
                  rfl rfl rfl
  | dl =>
      cases L with
      | nil =>
          injection h with hs; subst hs
          exact runWinPlus (bL := true) (bR := false) (l := default) (r := encR R) 3 (by omega)
            (fun _ => rfl) (fun hc => nomatch hc) 3 false [] [] 1 true [1] [0, 1] rfl rfl rfl
      | cons p L' =>
          rcases p with ⟨a, o⟩
          rcases a with _ | _ | _ | a
          · cases o with
            | o1 =>
                cases L' with
                | nil =>
                    injection h with hs; subst hs
                    exact runWinPlus (bL := true) (bR := false) (l := default) (r := encR R) 3 (by
                      omega)
                      (fun _ => rfl) (fun hc => nomatch hc) 3 false [0, 1] [] 3 false [] [0, 1,
                        1] rfl rfl rfl
                | cons p2 L'' =>
                    rcases p2 with ⟨a2, o'⟩
                    cases a2 with
                    | zero =>
                        cases o' with
                        | o1 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := (encL L'').tail) (r := encR R) 6 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 1, 0, 1, 0] [] 3 false [0] [0, 0, 1, 1]
                              (by change (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
                                2) >> encL L'') <{{3}} encR R) =
                                    (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                                      (0 : Fin 2) >> (encL L'').tail) <{{3}} encR R)
                                  rw [← encL_eq_zero_tail L''])
                              (by change (encL L'' <{{3}} ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
                                2) >> (1 : Fin 2) >> encR R)) =
                                    (((0 : Fin 2) >> (encL L'').tail) <{{3}} ((0 : Fin 2) >> (0 :
                                      Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> encR R))
                                  rw [← encL_eq_zero_tail L''])
                              rfl
                        | o2 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := encL L'') (r := encR R) 5 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 1, 0, 1, 1] [] 1 true [0] [0, 0, 1, 1] rfl
                              (by change (encL (addZ L'') {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1
                                : Fin 2) >> (1 : Fin 2) >> encR R)) =
                                    (((0 : Fin 2) >> encL L'') {{1}}> ((0 : Fin 2) >> (0 : Fin 2)
                                      >> (1 : Fin 2) >> (1 : Fin 2) >> encR R))
                                  rw [zero_cons_encL]) rfl
                        | o3 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := encL L'') (r := encR R) 5 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 1, 0, 1, 1, 1] [] 1 true [0, 1] [0, 0, 1, 1] rfl rfl rfl
                    | succ a2' =>
                        injection h with hs; subst hs
                        exact runWinPlus (bL := false) (bR := false)
                          (l := encL ((a2', o') :: L'')) (r := encR R) 3 (by omega)
                          (fun hc => nomatch hc) (fun hc => nomatch hc)
                          3 false [0, 1, 0] [] 3 false [] [0, 1, 1] rfl rfl rfl
            | o2 =>
                injection h with hs; subst hs
                exact runWinPlus (bL := false) (bR := false)
                  (l := encL L') (r := encR R) 5 (by omega)
                  (fun hc => nomatch hc) (fun hc => nomatch hc)
                  3 false [0, 1, 1] [] 1 true [0, 0, 1] [] rfl rfl rfl
            | o3 =>
                injection h with hs; subst hs
                exact runWinPlus (bL := false) (bR := false)
                  (l := encL L') (r := encR R) 5 (by omega)
                  (fun hc => nomatch hc) (fun hc => nomatch hc)
                  3 false [0, 1, 1, 1] [] 1 true [0, 0, 1, 1] [] rfl rfl rfl
          · cases o with
            | o1 =>
                cases L' with
                | nil =>
                    injection h with hs; subst hs
                    exact runWinPlus (bL := true) (bR := false) (l := default) (r := encR R) 6 (by
                      omega)
                      (fun _ => rfl) (fun hc => nomatch hc)
                      3 false [0, 0, 1] [] 3 false [0] [0, 1, 0, 1] rfl
                      (by change ((default : ListBlank (Fin 2)) <{{3}} ((0 : Fin 2) >> (1 : Fin 2)
                        >> (0 : Fin 2) >> (1 : Fin 2) >> encR R)) =
                            (((0 : Fin 2) >> (default : ListBlank (Fin 2))) <{{3}} ((0 : Fin 2) >>
                              (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> encR R))
                          rw [z00]) rfl
                | cons p2 L'' =>
                    rcases p2 with ⟨a2, o'⟩
                    cases a2 with
                    | zero =>
                        cases o' with
                        | o1 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := encL L'') (r := encR R) 5 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 0, 1, 0, 1] [] 1 true [0] [0, 1, 0, 1] rfl
                              (by change (encL (addZ L'') {{1}}> ((0 : Fin 2) >> (1 : Fin 2) >> (0
                                : Fin 2) >> (1 : Fin 2) >> encR R)) =
                                    (((0 : Fin 2) >> encL L'') {{1}}> ((0 : Fin 2) >> (1 : Fin 2)
                                      >> (0 : Fin 2) >> (1 : Fin 2) >> encR R))
                                  rw [zero_cons_encL]) rfl
                        | o2 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := encL L'') (r := encR R) 5 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 0, 1, 0, 1, 1] [] 1 true [0, 1] [0, 1, 0, 1] rfl rfl rfl
                        | o3 =>
                            injection h with hs; subst hs
                            exact runWinPlus (bL := false) (bR := false)
                              (l := encL L'') (r := encR R) 5 (by omega)
                              (fun hc => nomatch hc) (fun hc => nomatch hc)
                              3 false [0, 0, 1, 0, 1, 1, 1] [] 1 true [0, 1, 1] [0, 1, 0,
                                1] rfl rfl rfl
                    | succ a2' =>
                        injection h with hs; subst hs
                        exact runWinPlus (bL := false) (bR := false)
                          (l := (encL ((a2', o') :: L'')).tail) (r := encR R) 6 (by omega)
                          (fun hc => nomatch hc) (fun hc => nomatch hc)
                          3 false [0, 0, 1, 0, 0] [] 3 false [0] [0, 1, 0, 1]
                          (by change (((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                            encL ((a2', o') :: L'')) <{{3}} encR R) =
                                (((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 :
                                  Fin 2) >> (encL ((a2', o') :: L'')).tail) <{{3}} encR R)
                              rw [← encL_eq_zero_tail ((a2', o') :: L'')])
                          (by change (encL ((a2',
                            o') :: L'') <{{3}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 :
                            Fin 2) >> encR R)) =
                                (((0 : Fin 2) >> (encL ((a2',
                                  o') :: L'')).tail) <{{3}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 :
                                  Fin 2) >> (1 : Fin 2) >> encR R))
                              rw [← encL_eq_zero_tail ((a2', o') :: L'')])
                          rfl
            | o2 => nomatch h
            | o3 => nomatch h
          · cases o with
            | o1 =>
                injection h with hs; subst hs
                exact runWinPlus (bL := false) (bR := false)
                  (l := encL L') (r := encR R) 5 (by omega)
                  (fun hc => nomatch hc) (fun hc => nomatch hc)
                  3 false [0, 0, 0, 1] [] 1 true [1, 0, 1, 1] [] rfl rfl rfl
            | o2 =>
                injection h with hs; subst hs
                exact runWinPlus (bL := false) (bR := false)
                  (l := encL L') (r := encR R) 5 (by omega)
                  (fun hc => nomatch hc) (fun hc => nomatch hc)
                  3 false [0, 0, 0, 1, 1] [] 1 true [1, 0, 1, 1, 1] [] rfl rfl rfl
            | o3 => nomatch h
          · injection h with hs; subst hs
            exact runWinPlus (bL := false) (bR := false)
              (l := encL ((a, o) :: L')) (r := encR R) 3 (by omega)
              (fun hc => nomatch hc) (fun hc => nomatch hc)
              3 false [0, 0, 0] [] 1 true [1] [0, 1] rfl rfl rfl

def steps284 : ℕ → State → Option State
  | 0, s => some s
  | n + 1, s => (step284 s).bind (steps284 n)

theorem steps284_add (m n : ℕ) (s : State) :
    steps284 (m + n) s = (steps284 m s).bind (steps284 n) := by
  induction m generalizing s with
  | zero => simp [steps284]
  | succ m ih =>
      rw [Nat.succ_add]
      change (step284 s).bind (steps284 (m + n)) = ((step284 s).bind (steps284 m)).bind (steps284 n)
      cases h : step284 s with
      | none => rfl
      | some s' => exact ih s'

def MStar (s₁ s₂ : State) : Prop := ∃ n, steps284 n s₁ = some s₂
def MPlus (s₁ s₂ : State) : Prop := ∃ n, 0 < n ∧ steps284 n s₁ = some s₂

theorem mstar_refl (s : State) : MStar s s := ⟨0, rfl⟩

theorem mstar_of_plus {s₁ s₂ : State} (h : MPlus s₁ s₂) : MStar s₁ s₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩

theorem mstar_trans {s₁ s₂ s₃ : State} (h₁ : MStar s₁ s₂) (h₂ : MStar s₂ s₃) : MStar s₁ s₃ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hn⟩
  exact ⟨m + n, by rw [steps284_add, hm, Option.bind_some, hn]⟩

theorem mplus_trans {s₁ s₂ s₃ : State} (h₁ : MPlus s₁ s₂) (h₂ : MPlus s₂ s₃) : MPlus s₁ s₃ := by
  rcases h₁ with ⟨m, hmpos, hm⟩
  rcases h₂ with ⟨n, _, hn⟩
  exact ⟨m + n, by omega, by rw [steps284_add, hm, Option.bind_some, hn]⟩

theorem mplus_star {s₁ s₂ s₃ : State} (h₁ : MPlus s₁ s₂) (h₂ : MStar s₂ s₃) : MPlus s₁ s₃ := by
  rcases h₁ with ⟨m, hmpos, hm⟩
  rcases h₂ with ⟨n, hn⟩
  exact ⟨m + n, by omega, by rw [steps284_add, hm, Option.bind_some, hn]⟩

theorem mstar_plus {s₁ s₂ s₃ : State} (h₁ : MStar s₁ s₂) (h₂ : MPlus s₂ s₃) : MPlus s₁ s₃ := by
  rcases h₁ with ⟨m, hm⟩
  rcases h₂ with ⟨n, hnpos, hn⟩
  exact ⟨m + n, by omega, by rw [steps284_add, hm, Option.bind_some, hn]⟩

theorem steps284_sound : ∀ (n : ℕ) {s₁ s₂ : State},
    0 < n → steps284 n s₁ = some s₂ → (evalCfg s₁) [target_tm]⊢⁺ (evalCfg s₂)
  | 0, _, _, hpos, _ => by omega
  | 1, s₁, s₂, _, h => by
      unfold steps284 at h
      rcases hs : step284 s₁ with _ | s'
      · rw [hs] at h; nomatch h
      · rw [hs] at h; simp [steps284] at h; subst h; exact step284_sound hs
  | n + 2, s₁, s₂, _, h => by
      unfold steps284 at h
      rcases hs : step284 s₁ with _ | s'
      · rw [hs] at h; nomatch h
      · rw [hs, Option.bind_some] at h
        exact stepPlus_trans (step284_sound hs) (steps284_sound (n + 1) (by omega) h)

theorem mplus_sound {s₁ s₂ : State} (h : MPlus s₁ s₂) :
    (evalCfg s₁) [target_tm]⊢⁺ (evalCfg s₂) := by
  rcases h with ⟨n, hpos, hn⟩
  exact steps284_sound n hpos hn

theorem init_to_br1 : (init ([] : List (Fin 2))) [target_tm]⊢⁺ evalCfg (.br1, [], []) := by
  exact runWinPlus (bL := true) (bR := true) (l := default) (r := default) 1 (by omega)
    (fun _ => rfl) (fun _ => rfl) 0 true [] [] 1 true [1] [] rfl rfl rfl

def cp100 : State := (.dl, [(1, .o1), (0, .o1), (0, .o1)], [.r1, .r2, .r0, .r0, .r1, .r0, .r0, .r2])
def cp200 : State := (.dl, [(1, .o1), (0, .o1), (0, .o1), (0, .o1), (0, .o1)], [.r1, .r1, .r2,
  .r0, .r0, .r1, .r2, .r1, .r0, .r0, .r2])
def cp300 : State := (.br, [(0, .o1), (1, .o1), (1, .o1), (1, .o1), (0, .o1), (0, .o1), (1, .o1),
  (1, .o1), (0, .o1), (0, .o1), (1, .o1), (0, .o1), (0, .o1), (2, .o1), (2, .o1), (0, .o1), (0,
  .o1)], [.r1])
def cp400 : State := (.dl, [(0, .o1), (1, .o1), (1, .o1), (0, .o1), (0, .o1), (1, .o1), (0, .o1),
  (0, .o1), (2, .o1), (2, .o1), (0, .o1), (0, .o1), (0, .o1), (0, .o1)], [.r2, .r1, .r1, .r0, .r0,
  .r2])
def cp500 : State := (.br1, [(0, .o1), (0, .o1), (2, .o1), (2, .o1)], [.r0, .r1, .r2, .r1, .r2,
  .r1, .r1, .r2, .r1, .r0, .r0, .r2, .r1])
def cp600 : State := (.br, [(0, .o1), (1, .o1), (0, .o1), (0, .o1), (2, .o1), (0, .o1), (0, .o1),
  (2, .o1), (0, .o1), (0, .o1), (0, .o1), (0, .o1)], [.r2, .r1, .r1, .r2, .r0, .r0, .r2, .r1, .r1])
def cp682 : State := (.br, [(0, .o1), (1, .o1), (1, .o1), (1, .o1), (1, .o1), (1, .o1), (0, .o1),
  (0, .o1), (0, .o1), (1, .o1), (0, .o1), (0, .o1), (1, .o1), (0, .o1), (0, .o1), (2, .o1), (2,
  .o1), (0, .o1), (0, .o1), (2, .o1), (0, .o1), (0, .o1)], [])

theorem br1_to_cp682 : MPlus (.br1, [], []) cp682 := by
  have h1 : MPlus (.br1, [], []) cp100 := ⟨100, by omega, rfl⟩
  have h2 : MPlus cp100 cp200 := ⟨100, by omega, rfl⟩
  have h3 : MPlus cp200 cp300 := ⟨100, by omega, rfl⟩
  have h4 : MPlus cp300 cp400 := ⟨100, by omega, rfl⟩
  have h5 : MPlus cp400 cp500 := ⟨100, by omega, rfl⟩
  have h6 : MPlus cp500 cp600 := ⟨100, by omega, rfl⟩
  have h7 : MPlus cp600 cp682 := ⟨82, by omega, rfl⟩
  exact mplus_trans h1 (mplus_trans h2 (mplus_trans h3 (mplus_trans h4 (mplus_trans h5
    (mplus_trans h6 h7)))))

/-!
## Section 2: Bijective Base-2 Algebra & Repetition Builders
-/

def rep1 : ℕ → List (ℕ × Ones) → List (ℕ × Ones)
  | 0, u => u
  | k + 1, u => (1, .o1) :: rep1 k u

def repBlk : ℕ → List (ℕ × Ones) → List (ℕ × Ones)
  | 0, u => u
  | k + 1, u => (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: repBlk k u

def repL0 : ℕ → List (ℕ × Ones) → List (ℕ × Ones)
  | 0, u => u
  | k + 1, u => (0, .o1) :: repL0 k u

def repL00 : ℕ → List (ℕ × Ones) → List (ℕ × Ones)
  | 0, u => u
  | k + 1, u => (0, .o1) :: (0, .o1) :: repL00 k u

def repL2 : ℕ → List (ℕ × Ones) → List (ℕ × Ones)
  | 0, u => u
  | k + 1, u => (2, .o1) :: repL2 k u

def repR0 : ℕ → List RSym → List RSym
  | 0, R => R
  | k + 1, R => .r0 :: repR0 k R

def repR00 : ℕ → List RSym → List RSym
  | 0, R => R
  | k + 1, R => .r0 :: .r0 :: repR00 k R

def repR1 : ℕ → List RSym → List RSym
  | 0, R => R
  | k + 1, R => .r1 :: repR1 k R

def repR2 : ℕ → List RSym → List RSym
  | 0, R => R
  | k + 1, R => .r2 :: repR2 k R

def repR1001 : ℕ → List RSym → List RSym
  | 0, R => R
  | k + 1, R => .r1 :: .r0 :: .r0 :: .r1 :: repR1001 k R

theorem repBlk_snoc (k : ℕ) (u : List (ℕ × Ones)) :
    repBlk k ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u) = repBlk (k + 1) u := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repBlk, ih]

theorem repL0_snoc (k : ℕ) (u : List (ℕ × Ones)) :
    repL0 k ((0, .o1) :: u) = (0, .o1) :: repL0 k u := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repL0, ih]

theorem repL0_add (m n : ℕ) (u : List (ℕ × Ones)) :
    repL0 (m + n) u = repL0 m (repL0 n u) := by
  induction m with
  | zero => simp [repL0]
  | succ m ih => rw [Nat.succ_add]; simp [repL0, ih]

theorem repL0_double (k : ℕ) (u : List (ℕ × Ones)) :
    repL0 (2 * k) u = repL00 k u := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      change (0, .o1) :: (0, .o1) :: repL0 (2 * k) u = (0, .o1) :: (0, .o1) :: repL00 k u
      rw [ih]

theorem repR0_double (k : ℕ) (R : List RSym) :
    repR0 (2 * k) R = repR00 k R := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      change .r0 :: .r0 :: repR0 (2 * k) R = .r0 :: .r0 :: repR00 k R
      rw [ih]

theorem repR1_snoc (k : ℕ) (R : List RSym) :
    repR1 k (.r1 :: R) = .r1 :: repR1 k R := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repR1, ih]

theorem repR2_snoc (k : ℕ) (R : List RSym) :
    repR2 k (.r2 :: R) = .r2 :: repR2 k R := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repR2, ih]

theorem repL2_snoc (k : ℕ) (u : List (ℕ × Ones)) :
    repL2 k ((2, .o1) :: u) = (2, .o1) :: repL2 k u := by
  induction k with
  | zero => rfl
  | succ k ih => simp [repL2, ih]

def encB : List Bool → List (ℕ × Ones)
  | [] => []
  | false :: u => (0, .o1) :: (0, .o1) :: encB u
  | true :: u => (2, .o1) :: encB u

def valB : List Bool → ℕ
  | [] => 0
  | false :: u => 1 + 2 * valB u
  | true :: u => 2 + 2 * valB u

def valW : List Bool → ℕ
  | [] => 0
  | false :: u => 2 * valW u
  | true :: u => 1 + 2 * valW u

def incB : List Bool → List Bool
  | [] => [false]
  | false :: u => true :: u
  | true :: u => false :: incB u

def addB : ℕ → List Bool → List Bool
  | 0, u => u
  | k + 1, u => addB k (incB u)

theorem valB_incB (u : List Bool) : valB (incB u) = valB u + 1 := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      cases b with
      | false => simp [incB, valB]; omega
      | true => simp [incB, valB, ih]; omega

theorem valB_addB (k : ℕ) (u : List Bool) : valB (addB k u) = valB u + k := by
  induction k generalizing u with
  | zero => simp [addB]
  | succ k ih => simp [addB, ih, valB_incB]; omega

theorem valB_eq_pow_add_valW (u : List Bool) :
    valB u + 1 = 2 ^ u.length + valW u := by
  induction u with
  | nil => rfl
  | cons b u ih =>
      cases b with
      | false =>
          simp only [valB, valW, List.length_cons, Nat.pow_succ]
          omega
      | true =>
          simp only [valB, valW, List.length_cons, Nat.pow_succ]
          omega

theorem need_le_valB (u : List Bool) :
    2 ^ u.length + 2 * valW u ≤ 2 * valB u + 1 := by
  have h := valB_eq_pow_add_valW u
  have hp : 1 ≤ 2 ^ u.length := Nat.one_le_two_pow
  omega

theorem encB_rep_true (k : ℕ) (u : List Bool) :
    encB (List.replicate k true ++ u) = repL2 k (encB u) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, encB, repL2, ih]

theorem encB_rep_false (k : ℕ) (u : List Bool) :
    encB (List.replicate k false ++ u) = repL00 k (encB u) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, encB, repL00, ih]

theorem valB_rep_true (k : ℕ) (u : List Bool) :
    valB (List.replicate k true ++ u) + 2 = 2 ^ k * (valB u + 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, valB, Nat.pow_succ]
      calc 2 + 2 * valB (List.replicate k true ++ u) + 2
          = 2 * (valB (List.replicate k true ++ u) + 2) := by omega
        _ = 2 * (2 ^ k * (valB u + 2)) := by rw [ih]
        _ = 2 ^ k * 2 * (valB u + 2) := by ring

theorem valB_rep_false (k : ℕ) (u : List Bool) :
    valB (List.replicate k false ++ u) + 1 = 2 ^ k * (valB u + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append, valB, Nat.pow_succ]
      calc 1 + 2 * valB (List.replicate k false ++ u) + 1
          = 2 * (valB (List.replicate k false ++ u) + 1) := by omega
        _ = 2 * (2 ^ k * (valB u + 1)) := by rw [ih]
        _ = 2 ^ k * 2 * (valB u + 1) := by ring

inductive BitDecomp where
  | allTrue (a : ℕ)
  | allFalse (a : ℕ)
  | trueThenFalse (a : ℕ) (t : List Bool)
  | falseThenTrue (a : ℕ) (t : List Bool)

def evalDecomp : BitDecomp → List Bool
  | .allTrue a => List.replicate a true
  | .allFalse a => List.replicate (a + 1) false
  | .trueThenFalse a t => List.replicate (a + 1) true ++ false :: t
  | .falseThenTrue a t => List.replicate (a + 1) false ++ true :: t

theorem decomp_complete (s : List Bool) : ∃ d : BitDecomp, s = evalDecomp d := by
  induction s with
  | nil => exact ⟨.allTrue 0, rfl⟩
  | cons b s' ih =>
      rcases ih with ⟨d, hd⟩
      subst hd
      cases b with
      | true =>
          cases d with
          | allTrue a => exact ⟨.allTrue (a + 1), rfl⟩
          | allFalse a =>
              exact ⟨.trueThenFalse 0 (List.replicate a false), by simp [evalDecomp,
                List.replicate_succ]⟩
          | trueThenFalse a t =>
              exact ⟨.trueThenFalse (a + 1) t, by simp [evalDecomp, List.replicate_succ]⟩
          | falseThenTrue a t =>
              exact ⟨.trueThenFalse 0 (List.replicate a false ++ true :: t),
                by simp [evalDecomp, List.replicate_succ]⟩
      | false =>
          cases d with
          | allTrue a =>
              cases a with
              | zero => exact ⟨.allFalse 0, rfl⟩
              | succ a' =>
                  exact ⟨.falseThenTrue 0 (List.replicate a' true),
                    by simp [evalDecomp, List.replicate_succ]⟩
          | allFalse a =>
              exact ⟨.allFalse (a + 1), by simp [evalDecomp, List.replicate_succ]⟩
          | trueThenFalse a t =>
              exact ⟨.falseThenTrue 0 (List.replicate a true ++ false :: t),
                by simp [evalDecomp, List.replicate_succ]⟩
          | falseThenTrue a t =>
              exact ⟨.falseThenTrue (a + 1) t, by simp [evalDecomp, List.replicate_succ]⟩

/-!
## Section 3: `Call1`, `Call0`, `Call1N`, `Call0N` & Defect Erasure
-/

def Call1 (u u' : List (ℕ × Ones)) : Prop :=
  ∀ R : List RSym, MPlus (.dl, (1, .o1) :: u, R) (.br1, (0, .o1) :: u', R)

def Call0 (u u' : List (ℕ × Ones)) : Prop :=
  ∀ R : List RSym,
    MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u', R)

def Call1N : ℕ → List (ℕ × Ones) → List (ℕ × Ones) → Prop
  | 0, u, u' => u = u'
  | k + 1, u, u' => ∃ v, Call1 u v ∧ Call1N k v u'

def Call0N : ℕ → List (ℕ × Ones) → List (ℕ × Ones) → Prop
  | 0, u, u' => u = u'
  | k + 1, u, u' => ∃ v, Call0 u v ∧ Call0N k v u'

theorem call1N_add {m n : ℕ} {u v w : List (ℕ × Ones)}
    (h1 : Call1N m u v) (h2 : Call1N n v w) : Call1N (m + n) u w := by
  induction m generalizing u with
  | zero => subst h1; simpa using h2
  | succ m ih =>
      rcases h1 with ⟨x, hstep, hrest⟩
      rw [Nat.succ_add]
      exact ⟨x, hstep, ih hrest⟩

theorem call1_nil : Call1 [] [(0, .o1), (0, .o1)] := fun _ => ⟨5, by omega, rfl⟩
theorem call1_erase_end : Call1 [(0, .o1)] [] := fun _ => ⟨3, by omega, rfl⟩
theorem call1_00 (u : List (ℕ × Ones)) :
    Call1 ((0, .o1) :: (0, .o1) :: u) ((2, .o1) :: u) := fun _ => ⟨3, by omega, rfl⟩
theorem call1_02 (u : List (ℕ × Ones)) :
    Call1 ((0, .o1) :: (2, .o1) :: u) ((4, .o1) :: u) := fun _ => ⟨3, by omega, rfl⟩
theorem call1_4 (u : List (ℕ × Ones)) :
    Call1 ((4, .o1) :: u) ((0, .o1) :: (0, .o1) :: (0, .o1) :: u) := fun _ => ⟨5, by omega, rfl⟩
theorem call1_M1 (u : List (ℕ × Ones)) :
    Call1 ((1, .o1) :: (0, .o1) :: (0, .o2) :: u) ((1, .o1) :: (0, .o1) :: (0, .o2) :: u) :=
  fun _ => ⟨8, by omega, rfl⟩

theorem call1_2 {u u' : List (ℕ × Ones)} (h : Call1 u u') :
    Call1 ((2, .o1) :: u) ((0, .o1) :: (0, .o1) :: u') := fun R => by
  have h1 : MPlus (.dl, (1, .o1) :: (2, .o1) :: u, R) (.dl, (1, .o1) :: u, .r0 :: .r0 :: R) :=
    ⟨1, by omega, rfl⟩
  have h2 := h (.r0 :: .r0 :: R)
  have h3 : MPlus (.br1, (0, .o1) :: u', .r0 :: .r0 :: R)
                  (.br1, (0, .o1) :: (0, .o1) :: (0, .o1) :: u', R) :=
    ⟨2, by omega, rfl⟩
  exact mplus_trans h1 (mplus_trans h2 h3)

theorem call1_100 {u u' : List (ℕ × Ones)} (h : Call0 u u') :
    Call1 ((1, .o1) :: (0, .o1) :: (0, .o1) :: u) ((1, .o1) :: (0, .o1) :: (0, .o1) :: u') :=
  fun R => by
    have h1 : MPlus (.dl, (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u, R)
                    (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r0 :: .r0 :: R) :=
      ⟨1, by omega, rfl⟩
    have h2 := h (.r0 :: .r0 :: R)
    have h3 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u', .r0 :: .r0 :: R)
                    (.br1, (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u', R) :=
      ⟨2, by omega, rfl⟩
    exact mplus_trans h1 (mplus_trans h2 h3)

theorem call0_M11 (u : List (ℕ × Ones)) :
    Call0 ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: u)
          ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: u) :=
  fun _ => ⟨22, by omega, rfl⟩

theorem call0_2 {u u' : List (ℕ × Ones)} (h : Call1 u u') :
    Call0 ((2, .o1) :: u) ((2, .o1) :: u') := fun R => by
  have h1 : MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: u, R)
                  (.dl, (1, .o1) :: u, .r1 :: .r2 :: R) := ⟨2, by omega, rfl⟩
  have h2 := h (.r1 :: .r2 :: R)
  have h3 : MPlus (.br1, (0, .o1) :: u', .r1 :: .r2 :: R)
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: u', R) :=
    ⟨6, by omega, rfl⟩
  exact mplus_trans h1 (mplus_trans h2 h3)

theorem call0_100 {u u₁ u₂ : List (ℕ × Ones)} (h1 : Call0 u u₁) (h2 : Call0 u₁ u₂) :
    Call0 ((1, .o1) :: (0, .o1) :: (0, .o1) :: u) ((1, .o1) :: (0, .o1) :: (0, .o1) :: u₂) :=
  fun R => by
    have s1 : MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
      u, R)
                    (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r1 :: .r2 :: R) :=
      ⟨2, by omega, rfl⟩
    have s2 := h1 (.r1 :: .r2 :: R)
    have s3 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₁, .r1 :: .r2 :: R)
                    (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₁, .r0 :: .r0 :: .r1 :: R) :=
      ⟨3, by omega, rfl⟩
    have s4 := h2 (.r0 :: .r0 :: .r1 :: R)
    have s5 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₂, .r0 :: .r0 :: .r1 :: R)
                    (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
                      u₂, R) :=
      ⟨3, by omega, rfl⟩
    exact mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 s5)))

theorem call0_1100 {u u₁ u₂ : List (ℕ × Ones)} (h1 : Call0 u u₁) (h2 : Call0 u₁ u₂) :
    Call0 ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u)
          ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u₂) := fun R => by
  have s1 : MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) ::
    (0, .o1) :: u, R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r1 :: .r1 :: .r2 :: R) :=
    ⟨3, by omega, rfl⟩
  have s2 := h1 (.r1 :: .r1 :: .r2 :: R)
  have s3 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₁, .r1 :: .r1 :: .r2 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₁, .r1 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨5, by omega, rfl⟩
  have s4 := h2 (.r1 :: .r0 :: .r0 :: .r1 :: R)
  have s5 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u₂, .r1 :: .r0 :: .r0 :: .r1 :: R)
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) ::
                    (0, .o1) :: u₂, R) :=
    ⟨4, by omega, rfl⟩
  exact mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 s5)))

theorem call0N_2 {m : ℕ} {u u' : List (ℕ × Ones)} (h : Call1N m u u') :
    Call0N m ((2, .o1) :: u) ((2, .o1) :: u') := by
  induction m generalizing u with
  | zero => subst h; rfl
  | succ m ih =>
      rcases h with ⟨v, hv, hrest⟩
      exact ⟨(2, .o1) :: v, call0_2 hv, ih hrest⟩

theorem call0N_100 {m : ℕ} {u u' : List (ℕ × Ones)} (h : Call0N (2 * m) u u') :
    Call0N m ((1, .o1) :: (0, .o1) :: (0, .o1) :: u)
             ((1, .o1) :: (0, .o1) :: (0, .o1) :: u') := by
  induction m generalizing u with
  | zero => subst h; rfl
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega] at h
      rcases h with ⟨v1, h1, v2, h2, hrest⟩
      exact ⟨(1, .o1) :: (0, .o1) :: (0, .o1) :: v2, call0_100 h1 h2, ih hrest⟩

theorem call0N_1100 {m : ℕ} {u u' : List (ℕ × Ones)} (h : Call0N (2 * m) u u') :
    Call0N m ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u)
             ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u') := by
  induction m generalizing u with
  | zero => subst h; rfl
  | succ m ih =>
      rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega] at h
      rcases h with ⟨v1, h1, v2, h2, hrest⟩
      exact ⟨(1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: v2, call0_1100 h1 h2, ih hrest⟩

theorem call0N_repBlk (k m : ℕ) {u u' : List (ℕ × Ones)} (h : Call0N (m * 2 ^ k) u u') :
    Call0N m (repBlk k u) (repBlk k u') := by
  induction k generalizing m u with
  | zero => simpa [repBlk] using h
  | succ k ih =>
      apply call0N_1100
      apply ih
      have heq : (2 * m) * 2 ^ k = m * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
      rw [heq]; exact h

theorem call0N_M11 (m : ℕ) (u : List (ℕ × Ones)) :
    Call0N m ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: u)
             ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: u) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ⟨_, call0_M11 u, ih⟩

theorem call1N_M1 (m : ℕ) (u : List (ℕ × Ones)) :
    Call1N m ((1, .o1) :: (0, .o1) :: (0, .o2) :: u)
             ((1, .o1) :: (0, .o1) :: (0, .o2) :: u) := by
  induction m with
  | zero => rfl
  | succ m ih => exact ⟨_, call1_M1 u, ih⟩

theorem call1N_100 {m : ℕ} {u u' : List (ℕ × Ones)} (h : Call0N m u u') :
    Call1N m ((1, .o1) :: (0, .o1) :: (0, .o1) :: u)
             ((1, .o1) :: (0, .o1) :: (0, .o1) :: u') := by
  induction m generalizing u with
  | zero => subst h; rfl
  | succ m ih =>
      rcases h with ⟨v, hv, hrest⟩
      exact ⟨(1, .o1) :: (0, .o1) :: (0, .o1) :: v, call1_100 hv, ih hrest⟩

theorem call1_encB (u : List Bool) : Call1 (encB u) (encB (incB u)) := by
  induction u with
  | nil => exact call1_nil
  | cons b u ih =>
      cases b with
      | false => exact call1_00 (encB u)
      | true => exact call1_2 ih

theorem call1N_encB (m : ℕ) (u : List Bool) : Call1N m (encB u) (encB (addB m u)) := by
  induction m generalizing u with
  | zero => rfl
  | succ m ih => exact ⟨encB (incB u), call1_encB u, ih (incB u)⟩

theorem call1N_00_even {q : ℕ} {x x' : List (ℕ × Ones)} (h : Call1N q x x') :
    Call1N (2 * q) ((0, .o1) :: (0, .o1) :: x) ((0, .o1) :: (0, .o1) :: x') := by
  induction q generalizing x with
  | zero => subst h; rfl
  | succ q ih =>
      rcases h with ⟨v, hv, hrest⟩
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega]
      exact ⟨(2, .o1) :: x, call1_00 x, (0, .o1) :: (0, .o1) :: v, call1_2 hv, ih hrest⟩

theorem call1N_00_odd {q : ℕ} {x x' : List (ℕ × Ones)} (h : Call1N q x x') :
    Call1N (2 * q + 1) ((0, .o1) :: (0, .o1) :: x) ((2, .o1) :: x') := by
  have h1 := call1N_00_even h
  have h2 : Call1N 1 ((0, .o1) :: (0, .o1) :: x') ((2, .o1) :: x') :=
    ⟨(2, .o1) :: x', call1_00 x', rfl⟩
  exact call1N_add h1 h2

theorem call1N_2_even {q : ℕ} {x x' : List (ℕ × Ones)} (h : Call1N q x x') :
    Call1N (2 * q) ((2, .o1) :: x) ((2, .o1) :: x') := by
  induction q generalizing x with
  | zero => subst h; rfl
  | succ q ih =>
      rcases h with ⟨v, hv, hrest⟩
      rw [show 2 * (q + 1) = (2 * q + 1) + 1 by omega]
      exact ⟨(0, .o1) :: (0, .o1) :: v, call1_2 hv, (2, .o1) :: v, call1_00 v, ih hrest⟩

/--
Fundamental defect-erasure theorem: sufficient `Call1` carries erase a leading `(0, .o1)` defect. -/
theorem call1N_erase_0 (u : List Bool) :
    ∀ m : ℕ, 2 ^ u.length + 2 * valW u ≤ m →
      ∃ v : List Bool, Call1N m ((0, .o1) :: encB u) (encB v) ∧ valB v + 1 + 2 * valW u = m := by
  induction u with
  | nil =>
      intro m hm
      rcases m with _ | m'
      · simp [valW] at hm
      · refine ⟨addB m' [], ?_, ?_⟩
        · exact ⟨[], call1_erase_end, call1N_encB m' []⟩
        · simp [valB_addB, valB, valW]
  | cons b r ih =>
      intro m hm
      cases b with
      | false =>
          have hq : 2 ^ r.length + 2 * valW r ≤ m / 2 := by
            simp only [List.length_cons, Nat.pow_succ, valW] at hm
            omega
          obtain ⟨v, hv_call, hv_val⟩ := ih (m / 2) hq
          have hmod : m % 2 = 0 ∨ m % 2 = 1 := by omega
          rcases hmod with h0 | h1
          · refine ⟨false :: v, ?_, ?_⟩
            · have hm_eq : m = 2 * (m / 2) := by omega
              rw [hm_eq]
              exact call1N_00_even hv_call
            · simp only [valB, valW]; omega
          · refine ⟨true :: v, ?_, ?_⟩
            · have hm_eq : m = 2 * (m / 2) + 1 := by omega
              rw [hm_eq]
              exact call1N_00_odd hv_call
            · simp only [valB, valW]; omega
      | true =>
          have hm2 : 2 ≤ m := by
            simp only [List.length_cons, Nat.pow_succ, valW] at hm
            have hp : 1 ≤ 2 ^ r.length := Nat.one_le_two_pow
            omega
          have hq : 2 ^ r.length + 2 * valW r ≤ (m - 2) / 2 := by
            simp only [List.length_cons, Nat.pow_succ, valW] at hm
            omega
          obtain ⟨v, hv_call, hv_val⟩ := ih ((m - 2) / 2) hq
          have hpre : Call1N 2 ((0, .o1) :: (2, .o1) :: encB r)
                               ((0, .o1) :: (0, .o1) :: (0, .o1) :: encB r) :=
            ⟨(4, .o1) :: encB r, call1_02 (encB r),
             (0, .o1) :: (0, .o1) :: (0, .o1) :: encB r, call1_4 (encB r), rfl⟩
          have hmod : (m - 2) % 2 = 0 ∨ (m - 2) % 2 = 1 := by omega
          rcases hmod with h0 | h1
          · refine ⟨false :: v, ?_, ?_⟩
            · have hm_eq : m = 2 + 2 * ((m - 2) / 2) := by omega
              rw [hm_eq]
              exact call1N_add hpre (call1N_00_even hv_call)
            · simp only [valB, valW]; omega
          · refine ⟨true :: v, ?_, ?_⟩
            · have hm_eq : m = 2 + (2 * ((m - 2) / 2) + 1) := by omega
              rw [hm_eq]
              exact call1N_add hpre (call1N_00_odd hv_call)
            · simp only [valB, valW]; omega

theorem call0N_erase_2_0 (u : List Bool) (C : ℕ) (hC : 2 ^ u.length + 2 * valW u ≤ C) :
    ∃ v : List Bool,
      Call0N C ((2, .o1) :: (0, .o1) :: encB u) (encB (true :: v)) ∧
      valB (true :: v) + 4 * valW u = 2 * C := by
  obtain ⟨v, hv, hval⟩ := call1N_erase_0 u C hC
  refine ⟨v, call0N_2 hv, ?_⟩
  simp only [valB]; omega

theorem call0N_erase_2_2_0 (u : List Bool) (q : ℕ) (hq : 2 ^ u.length + 2 * valW u ≤ q) :
    ∃ v : List Bool,
      Call0N (2 * q) ((2, .o1) :: (2, .o1) :: (0, .o1) :: encB u) (encB (true :: true :: v)) ∧
      valB (true :: true :: v) + 8 * valW u = 4 * q + 2 := by
  obtain ⟨v, hv, hval⟩ := call1N_erase_0 u q hq
  refine ⟨v, call0N_2 (call1N_2_even hv), ?_⟩
  simp only [valB]; omega

theorem call0N_erase_2_4 (u : List Bool) (q : ℕ) (hq : 1 + (2 ^ u.length + 2 * valW u) ≤ q) :
    ∃ v : List Bool,
      Call0N (2 * q) ((2, .o1) :: (4, .o1) :: encB u) (encB (true :: true :: v)) ∧
      valB (true :: true :: v) + 8 * valW u + 2 = 4 * q := by
  have hq1 : 2 ^ u.length + 2 * valW u ≤ q - 1 := by omega
  obtain ⟨v, hv, hval⟩ := call1N_erase_0 u (q - 1) hq1
  have h1 : Call1N 1 ((4, .o1) :: encB u) ((0, .o1) :: (0, .o1) :: (0, .o1) :: encB u) :=
    ⟨(0, .o1) :: (0, .o1) :: (0, .o1) :: encB u, call1_4 (encB u), rfl⟩
  have h2 := call1N_00_odd hv
  have htot := call1N_add h1 h2
  have heq : 1 + (2 * (q - 1) + 1) = 2 * q := by omega
  rw [heq] at htot
  refine ⟨v, call0N_2 htot, ?_⟩
  simp only [valB]; omega

/-!
## Section 4: `BR1` Prefix, `BR` Prefix (`IN`/`OUT`), `F_core`, and `BR` Body Exits
-/

theorem dl_0_1_sweep (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.dl, (0, .o1) :: rep1 a u, R) (.dl, (0, .o1) :: u, repR1 a R) := by
  induction a generalizing R with
  | zero => exact mstar_refl _
  | succ a ih =>
      have h1 : MPlus (.dl, (0, .o1) :: (1, .o1) :: rep1 a u, R)
                      (.dl, (0, .o1) :: rep1 a u, .r1 :: R) := ⟨1, by omega, rfl⟩
      have h2 := ih (.r1 :: R)
      rw [repR1_snoc] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem br_r1_sweep (a : ℕ) (b : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.br, (0, .o1) :: rep1 b ((0, .o1) :: u), repR1 a R)
          (.br, (0, .o1) :: rep1 (a + b) ((0, .o1) :: u), R) := by
  induction a generalizing b with
  | zero =>
      rw [Nat.zero_add]; exact mstar_refl _
  | succ a ih =>
      have h1 : MPlus (.br, (0, .o1) :: rep1 b ((0, .o1) :: u), .r1 :: repR1 a R)
                      (.br, (0, .o1) :: (1, .o1) :: rep1 b ((0, .o1) :: u), repR1 a R) :=
        ⟨1, by omega, rfl⟩
      have h2 := ih (b + 1)
      rw [show a + (b + 1) = a + 1 + b by omega] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem br1_loop_step (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR1 (a + 1) (.r0 :: .r0 :: .r2 :: R))
          (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR1 a (.r0 :: .r0 :: .r2 :: .r1 :: R)) :=
            by
  have h1 := br_r1_sweep (a + 1) 0 ((0, .o1) :: u) (.r0 :: .r0 :: .r2 :: R)
  rw [Nat.add_zero] at h1
  have hmid : MPlus (.br, (0, .o1) :: (1, .o1) :: rep1 a ((0, .o1) :: (0, .o1) :: u), .r0 :: .r0
    :: .r2 :: R)
                    (.dl, (0, .o1) :: rep1 a ((0, .o1) :: (0, .o1) :: u), .r0 :: .r0 :: .r2 :: .r1
                      :: R) :=
    ⟨5, by omega, rfl⟩
  have h2 := dl_0_1_sweep a ((0, .o1) :: (0, .o1) :: u) (.r0 :: .r0 :: .r2 :: .r1 :: R)
  exact mstar_plus h1 (mplus_star hmid h2)

theorem br1_call0_loop (a b : ℕ) (u u' : List (ℕ × Ones)) (h : Call0N (a + 1) u u') :
    MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR1 a (.r0 :: .r0 :: .r2 :: repR1 b []))
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u', .r0 :: .r0 :: .r2 :: repR1 (a + b) []) := by
  induction a generalizing b u with
  | zero =>
      rcases h with ⟨v, hv, hv'⟩
      subst hv'
      simpa [repR1] using hv (.r0 :: .r0 :: .r2 :: repR1 b [])
  | succ a ih =>
      rcases h with ⟨v, hv, hrest⟩
      have h1 := hv (repR1 (a + 1) (.r0 :: .r0 :: .r2 :: repR1 b []))
      have h2 := br1_loop_step a v (repR1 b [])
      have h3 := ih (b + 1) v hrest
      rw [show a + (b + 1) = a + 1 + b by omega] at h3
      exact mplus_trans h1 (mplus_trans h2 h3)

theorem br1_prefix_step (n : ℕ) {body body' : List (ℕ × Ones)}
    (hcall : Call0N (n + 1) ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body)
                             ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body')) :
    MPlus (.br1, (0, .o1) :: rep1 (n + 2) ((0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0,
      .o1) :: (0, .o1) :: body), [])
          (.br,  (0, .o1) :: rep1 (n + 3) ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0,
            .o1) :: (0, .o1) :: body'), []) := by
  have h1 : MPlus (.br1, (0, .o1) :: (1, .o1) :: (1, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: (1,
    .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body), [])
                  (.dl,  (0, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0,
                    .o1) :: (0, .o1) :: body), [.r0, .r0, .r2]) :=
    ⟨3, by omega, rfl⟩
  have h2 := dl_0_1_sweep n ((0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
    :: body) [.r0, .r0, .r2]
  have h3 := br1_call0_loop n 0 ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body)
                                ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body') hcall
  rw [Nat.add_zero] at h3
  have h4 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) ::
    (0, .o1) :: body',
                        .r0 :: .r0 :: .r2 :: repR1 n [])
                  (.br1, (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body',
                        .r1 :: .r1 :: .r1 :: .r1 :: repR1 n []) := ⟨15, by omega, rfl⟩
  have h5 : MPlus (.br1, (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: body',
                        .r1 :: .r1 :: .r1 :: .r1 :: repR1 n [])
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) ::
                    (0, .o1) :: body',
                        repR1 (n + 3) []) := by
    have hr : .r1 :: .r1 :: .r1 :: repR1 n [] = repR1 (n + 3) [] := by
      simp [repR1]
    rw [← hr]
    exact ⟨1, by omega, rfl⟩
  have h6 := br_r1_sweep (n + 3) 0 ((0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
    body') []
  rw [Nat.add_zero] at h6
  exact mplus_star (mplus_trans (mplus_star h1 h2) (mplus_trans h3 (mplus_trans h4 h5))) h6

theorem br1_run (n k : ℕ) {body body' : List (ℕ × Ones)}
    (hcall : Call0N ((n + 1) * 2 ^ (k + 1)) body body') :
    MPlus (.br1, (0, .o1) :: rep1 (n + 2) ((0, .o1) :: (0, .o1) :: repBlk (k + 1) body), [])
          (.br,  (0, .o1) :: rep1 (n + 3) ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0,
            .o1) :: (0, .o1) :: repBlk k body'), []) := by
  apply br1_prefix_step n
  have h := call0N_repBlk (k + 1) (n + 1) hcall
  exact h

theorem br_in_peel (k : ℕ) (body : List (ℕ × Ones)) (R : List RSym) :
    MStar (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: repBlk k body, .r2 :: .r2 :: R)
          (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: body, .r2 :: .r2 :: repR1001 k R) := by
  induction k generalizing R with
  | zero => exact mstar_refl _
  | succ k ih =>
      have h1 : MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1)
        :: (0, .o1) :: repBlk k body,
                            .r2 :: .r2 :: R)
                      (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: repBlk k body,
                            .r2 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R) := ⟨19, by omega, rfl⟩
      have h2 := ih (.r1 :: .r0 :: .r0 :: .r1 :: R)
      have hr : repR1001 k (.r1 :: .r0 :: .r0 :: .r1 :: R) = repR1001 (k + 1) R := by
        clear h1 h2 ih
        induction k with
        | zero => rfl
        | succ k ihk => simp [repR1001, ihk]
      rw [hr] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem br_in (n k : ℕ) (body : List (ℕ × Ones)) :
    MPlus (.br, (0, .o1) :: rep1 (n + 1) ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1)
      :: (0, .o1) :: repBlk k body), [])
          (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: body, .r2 :: .r2 :: repR1001 k (repR1 n [.r0,
            .r0])) := by
  have h1 : MPlus (.br, (0, .o1) :: (1, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1,
    .o1) :: (0, .o1) :: (0, .o1) :: repBlk k body), [])
                  (.dl, (0, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0,
                    .o1) :: (0, .o1) :: repBlk k body), [.r0, .r0]) :=
    ⟨2, by omega, rfl⟩
  have h2 := dl_0_1_sweep n ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
    :: repBlk k body) [.r0, .r0]
  have h3 : MPlus (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) ::
    (0, .o1) :: repBlk k body, repR1 n [.r0, .r0])
                  (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: repBlk k body, .r2 :: .r2 :: repR1 n
                    [.r0, .r0]) :=
    ⟨2, by omega, rfl⟩
  have h4 := br_in_peel k body (repR1 n [.r0, .r0])
  exact mplus_star (mplus_trans (mplus_star h1 h2) h3) h4

theorem br_out_1001 (k : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR1001 k R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repBlk k u, R) := by
  induction k generalizing u with
  | zero => exact mstar_refl _
  | succ k ih =>
      have h1 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r1 :: .r0 :: .r0 :: .r1 ::
        repR1001 k R)
                      (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0,
                        .o1) :: (0, .o1) :: u, repR1001 k R) :=
        ⟨4, by omega, rfl⟩
      have h2 := ih ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: u)
      rw [repBlk_snoc] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem br_out (n k : ℕ) (u : List (ℕ × Ones)) :
    MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR1001 k (repR1 n [.r0, .r0]))
          (.br1, (0, .o1) :: rep1 (n + 1) ((0, .o1) :: (0, .o1) :: repBlk k u), []) := by
  have h1 := br_out_1001 k u (repR1 n [.r0, .r0])
  have h2 := br_r1_sweep n 0 ((0, .o1) :: repBlk k u) [.r0, .r0]
  rw [Nat.add_zero] at h2
  have h3 : MPlus (.br, (0, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: repBlk k u), [.r0, .r0])
                  (.br1, (0, .o1) :: (1, .o1) :: rep1 n ((0, .o1) :: (0, .o1) :: repBlk k u), [])
                    := by
    cases n with
    | zero => exact ⟨2, by omega, rfl⟩
    | succ n' =>
        have hstep1 : MPlus (.br, (0, .o1) :: (1, .o1) :: rep1 n' ((0, .o1) :: (0, .o1) :: repBlk
          k u), [.r0, .r0])
                            (.br1, (0, .o1) :: (1, .o1) :: (1, .o1) :: rep1 n' ((0, .o1) :: (0,
                              .o1) :: repBlk k u), []) :=
          ⟨2, by omega, rfl⟩
        exact hstep1
  exact mstar_plus (mstar_trans h1 h2) h3

theorem br_wrap (n k : ℕ) {body out : List (ℕ × Ones)}
    (hmid : ∀ R : List RSym,
      MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: body, .r2 :: .r2 :: R)
            (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: out, R)) :
    MPlus (.br,  (0, .o1) :: rep1 (n + 1) ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0,
      .o1) :: (0, .o1) :: repBlk k body), [])
          (.br1, (0, .o1) :: rep1 (n + 1) ((0, .o1) :: (0, .o1) :: repBlk k out), []) :=
  mplus_trans (br_in n k body) (mplus_trans (hmid _) (br_out n k out))

/-!
### `F_core` Helpers & 4-Case Proof
-/

theorem br_out_2_step (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: u, R) :=
  ⟨5, by omega, rfl⟩

theorem br_out_2_sweep (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: u, repR2 a R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL2 a u, R) := by
  induction a generalizing u with
  | zero => exact mstar_refl _
  | succ a ih =>
      have h1 := br_out_2_step u (repR2 a R)
      have h2 := ih ((2, .o1) :: u)
      rw [repL2_snoc] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem dl_1_2_sweep (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.dl, (1, .o1) :: repL2 a u, R)
          (.dl, (1, .o1) :: u, repR00 a R) := by
  induction a generalizing R with
  | zero => exact mstar_refl _
  | succ a ih =>
      have h1 : MPlus (.dl, (1, .o1) :: (2, .o1) :: repL2 a u, R)
                      (.dl, (1, .o1) :: repL2 a u, .r0 :: .r0 :: R) := ⟨1, by omega, rfl⟩
      have h2 := ih (.r0 :: .r0 :: R)
      have hr : repR00 a (.r0 :: .r0 :: R) = repR00 (a + 1) R := by
        clear h1 h2 ih
        induction a with
        | zero => rfl
        | succ a iha => simp [repR00, iha]
      rw [hr] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem dl_00_sweep (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.dl, repL00 a u, R) (.dl, u, repR2 a R) := by
  induction a generalizing R with
  | zero => exact mstar_refl _
  | succ a ih =>
      have h1 : MPlus (.dl, (0, .o1) :: (0, .o1) :: repL00 a u, R)
                      (.dl, repL00 a u, .r2 :: R) := ⟨1, by omega, rfl⟩
      have h2 := ih (.r2 :: R)
      rw [repR2_snoc] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem br1_r0_sweep (k : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MStar (.br1, u, repR0 k R) (.br1, repL0 k u, R) := by
  induction k generalizing u with
  | zero => exact mstar_refl _
  | succ k ih =>
      have h1 : MPlus (.br1, u, .r0 :: repR0 k R) (.br1, (0, .o1) :: u, repR0 k R) :=
        ⟨1, by omega, rfl⟩
      have h2 := ih ((0, .o1) :: u)
      rw [repL0_snoc] at h2
      exact mstar_trans (mstar_of_plus h1) h2

theorem dl_0_2_to_1 (a : ℕ) (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (0, .o1) :: repL2 (a + 1) u, R)
          (.dl, (1, .o1) :: u, repR00 a (.r1 :: R)) := by
  have h1 : MPlus (.dl, (0, .o1) :: (2, .o1) :: repL2 a u, R)
                  (.dl, (1, .o1) :: repL2 a u, .r1 :: R) := ⟨1, by omega, rfl⟩
  exact mplus_star h1 (dl_1_2_sweep a u (.r1 :: R))

theorem f_core_allTrue (a : ℕ) (R : List RSym) :
    MPlus (.dl, (0, .o1) :: repL2 a [], .r1 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a +
            1) [], R) := by
  cases a with
  | zero => exact ⟨20, by omega, rfl⟩
  | succ a' =>
      have h1 := dl_0_2_to_1 a' [] (.r1 :: .r2 :: R)
      have h2 : MPlus (.dl, [(1, .o1)], repR00 a' (.r1 :: .r1 :: .r2 :: R))
                      (.br1, [], .r0 :: .r0 :: .r0 :: repR00 a' (.r1 :: .r1 :: .r2 :: R)) :=
        ⟨2, by omega, rfl⟩
      have h3 := br1_r0_sweep (2 * a' + 3) [] (.r1 :: .r1 :: .r2 :: R)
      have h3r : repR0 (2 * a' + 3) (.r1 :: .r1 :: .r2 :: R) =
          .r0 :: .r0 :: .r0 :: repR00 a' (.r1 :: .r1 :: .r2 :: R) := by
        change .r0 :: .r0 :: .r0 :: repR0 (2 * a') (.r1 :: .r1 :: .r2 :: R) = _
        rw [repR0_double]
      rw [h3r] at h3
      have h4 : MPlus (.br1, repL0 (2 * a' + 3) [], .r1 :: .r1 :: .r2 :: R)
                      (.dl, (0, .o1) :: (0, .o1) :: repL0 (2 * a' + 3) [],
                        .r0 :: .r0 :: .r1 :: R) :=
        ⟨4, by omega, rfl⟩
      have h4eq : (0, .o1) :: (0, .o1) :: repL0 (2 * a' + 3) [] = repL00 (a' + 2) [(0, .o1)] := by
        rw [← repL0_double]
        have hs : 2 * (a' + 2) = 2 * a' + 4 := by omega
        rw [hs]
        calc (0, .o1) :: (0, .o1) :: repL0 (2 * a' + 3) []
            = repL0 ((2 * a' + 3) + 2) [] := rfl
          _ = repL0 ((2 * a' + 4) + 1) [] := rfl
          _ = repL0 (2 * a' + 4) [(0, .o1)] := by rw [repL0_add]; rfl
      have h5 := dl_00_sweep (a' + 2) [(0, .o1)] (.r0 :: .r0 :: .r1 :: R)
      rw [← h4eq] at h5
      have h6 : MPlus (.dl, [(0, .o1)], repR2 (a' + 2) (.r0 :: .r0 :: .r1 :: R))
                      (.br, [(0, .o1), (0, .o1), (0, .o1)],
                        repR2 (a' + 2) (.r0 :: .r0 :: .r1 :: R)) :=
        ⟨4, by omega, rfl⟩
      have h7 := br_out_2_sweep (a' + 2) [] (.r0 :: .r0 :: .r1 :: R)
      have h8 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a' + 2) [], .r0 :: .r0 ::
        .r1 :: R)
                      (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0,
                        .o1) :: repL2 (a' + 2) [], R) :=
        ⟨3, by omega, rfl⟩
      exact mplus_trans h1 (mplus_trans (mplus_star h2 h3) (mplus_trans (mplus_star h4 h5)
        (mplus_trans (mplus_star h6 h7) h8)))

theorem f_core_allFalse (a : ℕ) (R : List RSym) :
    MPlus (.dl, (0, .o1) :: repL00 (a + 1) [], .r1 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1)
            :: repL00 (a + 1) [], R) := by
  have h1 := dl_00_sweep (a + 1) [(0, .o1)] (.r1 :: .r2 :: R)
  have h1l : (0, .o1) :: repL00 (a + 1) [] = repL00 (a + 1) [(0, .o1)] := by
    rw [← repL0_double, ← repL0_double]
    exact (repL0_snoc (2 * (a + 1)) []).symm
  rw [h1l]
  have h2 : MPlus (.dl, [(0, .o1)], repR2 (a + 1) (.r1 :: .r2 :: R))
                  (.br, [(0, .o1), (0, .o1), (0, .o1)], repR2 (a + 1) (.r1 :: .r2 :: R)) :=
    ⟨4, by omega, rfl⟩
  have h3 := br_out_2_sweep (a + 1) [] (.r1 :: .r2 :: R)
  have h4 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a + 1) [], .r1 :: .r2 :: R)
                  (.dl, (0, .o1) :: repL2 (a + 1) [], .r2 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨4, by omega, rfl⟩
  have h5 := dl_0_2_to_1 a [] (.r2 :: .r0 :: .r0 :: .r1 :: R)
  have h6 : MPlus (.dl, [(1, .o1)], repR00 a (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R))
                  (.br1, [], .r0 :: .r0 :: .r0 :: repR00 a (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R))
                    :=
    ⟨2, by omega, rfl⟩
  have h7 := br1_r0_sweep (2 * a + 3) [] (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R)
  have h7r : repR0 (2 * a + 3) (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R) =
      .r0 :: .r0 :: .r0 :: repR00 a (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R) := by
    change .r0 :: .r0 :: .r0 :: repR0 (2 * a) _ = _
    rw [repR0_double]
  rw [h7r] at h7
  have h8 : MPlus (.br1, repL0 (2 * a + 3) [], .r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R)
                  (.br, (0, .o1) :: (0, .o1) :: repL0 (2 * a + 3) [], .r2 :: .r0 :: .r0 :: .r1 ::
                    R) :=
    ⟨1, by omega, rfl⟩
  have h8l : (0, .o1) :: (0, .o1) :: repL0 (2 * a + 3) [] =
      (0, .o1) :: (0, .o1) :: (0, .o1) :: repL00 (a + 1) [] := by
    rw [← repL0_double, show 2 * (a + 1) = 2 * a + 2 by omega]
    rfl
  rw [h8l] at h8
  have h9 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL00 (a + 1) [], .r2 :: .r0 :: .r0
    :: .r1 :: R)
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
                    (2, .o1) :: repL00 (a + 1) [], R) :=
    ⟨8, by omega, rfl⟩
  exact mstar_plus h1 (mplus_trans (mplus_star h2 h3) (mplus_trans h4 (mplus_trans h5 (mplus_trans
    (mplus_star h6 h7) (mplus_trans h8 h9)))))

theorem f_core_trueThenFalse (a : ℕ) (t : List Bool) (R : List RSym) :
    MPlus (.dl, (0, .o1) :: repL2 (a + 1) ((0, .o1) :: (0, .o1) :: encB t), .r1 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a +
            1) (encB (incB t)), R) := by
  have h1 := dl_0_2_to_1 a ((0, .o1) :: (0, .o1) :: encB t) (.r1 :: .r2 :: R)
  have h2 : MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: encB t, repR00 a (.r1 :: .r1 :: .r2 ::
    R))
                  (.br, (1, .o1) :: encB t, .r0 :: .r0 :: repR00 a (.r1 :: .r1 :: .r2 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h3 : MPlus (.br, (1, .o1) :: encB t, .r0 :: .r0 :: repR00 a (.r1 :: .r1 :: .r2 :: R))
                  (.br1, (2, .o1) :: encB t, .r0 :: repR00 a (.r1 :: .r1 :: .r2 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h4 := br1_r0_sweep (2 * a + 1) ((2, .o1) :: encB t) (.r1 :: .r1 :: .r2 :: R)
  have h4r : repR0 (2 * a + 1) (.r1 :: .r1 :: .r2 :: R) = .r0 :: repR00 a (.r1 :: .r1 :: .r2 :: R)
    := by
    change .r0 :: repR0 (2 * a) _ = _
    rw [repR0_double]
  rw [h4r] at h4
  have h5 : MPlus (.br1, repL0 (2 * a + 1) ((2, .o1) :: encB t), .r1 :: .r1 :: .r2 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: repL0 (2 * a + 1) ((2, .o1) :: encB t), .r0 :: .r0
                    :: .r1 :: R) :=
    ⟨4, by omega, rfl⟩
  have h5l : (0, .o1) :: (0, .o1) :: repL0 (2 * a + 1) ((2, .o1) :: encB t) =
      repL00 (a + 1) ((0, .o1) :: (2, .o1) :: encB t) := by
    rw [← repL0_double, show 2 * (a + 1) = 2 * a + 2 by omega, repL0_snoc]
    rfl
  rw [h5l] at h5
  have h6 := dl_00_sweep (a + 1) ((0, .o1) :: (2, .o1) :: encB t) (.r0 :: .r0 :: .r1 :: R)
  have h7 : MPlus (.dl, (0, .o1) :: (2, .o1) :: encB t, repR2 (a + 1) (.r0 :: .r0 :: .r1 :: R))
                  (.dl, (1, .o1) :: encB t, .r1 :: repR2 (a + 1) (.r0 :: .r0 :: .r1 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h8 := call1_encB t (.r1 :: repR2 (a + 1) (.r0 :: .r0 :: .r1 :: R))
  have h9 : MPlus (.br1, (0, .o1) :: encB (incB t), .r1 :: repR2 (a + 1) (.r0 :: .r0 :: .r1 :: R))
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: encB (incB t), repR2 (a + 1) (.r0 ::
                    .r0 :: .r1 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h10 := br_out_2_sweep (a + 1) (encB (incB t)) (.r0 :: .r0 :: .r1 :: R)
  have h11 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a + 1) (encB (incB t)), .r0 ::
    .r0 :: .r1 :: R)
                   (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
                     repL2 (a + 1) (encB (incB t)), R) :=
    ⟨3, by omega, rfl⟩
  exact mplus_trans h1 (mplus_trans h2 (mplus_trans (mplus_star h3 h4) (mplus_trans (mplus_star h5
    h6) (mplus_trans h7 (mplus_trans h8 (mplus_trans (mplus_star h9 h10) h11))))))

theorem f_core_falseThenTrue (a : ℕ) (t : List Bool) (R : List RSym) :
    MPlus (.dl, (0, .o1) :: repL00 (a + 1) ((2, .o1) :: encB t), .r1 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1)
            :: repL00 a (encB (incB (incB t))), R) := by
  have h1l : (0, .o1) :: repL00 (a + 1) ((2, .o1) :: encB t) =
      repL00 (a + 1) ((0, .o1) :: (2, .o1) :: encB t) := by
    rw [← repL0_double, ← repL0_double]
    exact (repL0_snoc (2 * (a + 1)) ((2, .o1) :: encB t)).symm
  rw [h1l]
  have h1 := dl_00_sweep (a + 1) ((0, .o1) :: (2, .o1) :: encB t) (.r1 :: .r2 :: R)
  have h2 : MPlus (.dl, (0, .o1) :: (2, .o1) :: encB t, repR2 (a + 1) (.r1 :: .r2 :: R))
                  (.dl, (1, .o1) :: encB t, .r1 :: repR2 (a + 1) (.r1 :: .r2 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h3 := call1_encB t (.r1 :: repR2 (a + 1) (.r1 :: .r2 :: R))
  have h4 : MPlus (.br1, (0, .o1) :: encB (incB t), .r1 :: repR2 (a + 1) (.r1 :: .r2 :: R))
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: encB (incB t), repR2 (a + 1) (.r1 ::
                    .r2 :: R)) :=
    ⟨1, by omega, rfl⟩
  have h5 := br_out_2_sweep (a + 1) (encB (incB t)) (.r1 :: .r2 :: R)
  have h6 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: repL2 (a + 1) (encB (incB t)), .r1 ::
    .r2 :: R)
                  (.dl, (1, .o1) :: repL2 a (encB (incB t)), .r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R)
                    :=
    ⟨5, by omega, rfl⟩
  have h7 := dl_1_2_sweep a (encB (incB t)) (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R)
  have h8 := call1_encB (incB t) (repR00 a (.r1 :: .r2 :: .r0 :: .r0 :: .r1 :: R))
  have h9 := br1_r0_sweep (2 * a) ((0, .o1) :: encB (incB (incB t))) (.r1 :: .r2 :: .r0 :: .r0 ::
    .r1 :: R)
  rw [repR0_double] at h9
  have h9l : repL0 (2 * a) ((0, .o1) :: encB (incB (incB t))) =
      (0, .o1) :: repL00 a (encB (incB (incB t))) := by
    rw [repL0_snoc, repL0_double]
  rw [h9l] at h9
  have h10 : MPlus (.br1, (0, .o1) :: repL00 a (encB (incB (incB t))), .r1 :: .r2 :: .r0 :: .r0 ::
    .r1 :: R)
                   (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
                     (2, .o1) :: repL00 a (encB (incB (incB t))), R) :=
    ⟨9, by omega, rfl⟩
  exact mstar_plus h1 (mplus_trans h2 (mplus_trans h3 (mplus_trans (mplus_star h4 h5) (mplus_trans
    (mplus_star h6 h7) (mplus_trans (mplus_star h8 h9) h10)))))

theorem f_core_ex (s : List Bool) :
    ∃ t : List Bool,
      valB (true :: t) ≤ 2 + 2 * valB s ∧
      ∀ R : List RSym,
        MPlus (.dl, (0, .o1) :: encB s, .r1 :: .r2 :: R)
              (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: encB
                (true :: t), R) := by
  obtain ⟨d, hd⟩ := decomp_complete s
  subst hd
  cases d with
  | allTrue a =>
      refine ⟨List.replicate a true, ?_, ?_⟩
      · simp [evalDecomp, valB]
      · intro R
        have he : encB (List.replicate a true) = repL2 a [] := by
          rw [← List.append_nil (List.replicate a true), encB_rep_true]; rfl
        have h := f_core_allTrue a R
        simpa [evalDecomp, encB, he, repL2] using h
  | allFalse a =>
      refine ⟨List.replicate (a + 1) false, ?_, ?_⟩
      · simp [evalDecomp, valB]
      · intro R
        have he : encB (List.replicate (a + 1) false) = repL00 (a + 1) [] := by
          rw [← List.append_nil (List.replicate (a + 1) false), encB_rep_false]; rfl
        have h := f_core_allFalse a R
        simpa [evalDecomp, encB, he] using h
  | trueThenFalse a t₀ =>
      refine ⟨List.replicate a true ++ incB t₀, ?_, ?_⟩
      · have h1 := valB_rep_true (a + 1) (incB t₀)
        have h2 := valB_rep_true (a + 1) (false :: t₀)
        have hle : valB (List.replicate (a + 1) true ++ incB t₀) + 2 ≤
            valB (List.replicate (a + 1) true ++ false :: t₀) + 2 := by
          rw [h1, h2, valB_incB]
          simp only [valB]
          exact Nat.mul_le_mul_left _ (by omega)
        simp only [evalDecomp, List.replicate_succ, List.cons_append] at hle ⊢
        omega
      · intro R
        have h := f_core_trueThenFalse a t₀ R
        have he1 : encB (evalDecomp (.trueThenFalse a t₀)) =
            repL2 (a + 1) ((0, .o1) :: (0, .o1) :: encB t₀) := by
          simp [evalDecomp, encB_rep_true, encB]
        have he2 : encB (true :: (List.replicate a true ++ incB t₀)) =
            repL2 (a + 1) (encB (incB t₀)) := by
          have : true :: (List.replicate a true ++ incB t₀) =
              List.replicate (a + 1) true ++ incB t₀ := by simp [List.replicate_succ]
          rw [this, encB_rep_true]
        rw [he1, he2]; exact h
  | falseThenTrue a t₀ =>
      refine ⟨List.replicate a false ++ incB (incB t₀), ?_, ?_⟩
      · have h1 := valB_rep_false a (incB (incB t₀))
        have h2 := valB_rep_false (a + 1) (true :: t₀)
        have hval_out : valB (true :: (List.replicate a false ++ incB (incB t₀))) =
            2 ^ (a + 1) * (valB t₀ + 3) := by
          simp only [valB, Nat.pow_succ]
          calc 2 + 2 * valB (List.replicate a false ++ incB (incB t₀))
              = 2 * (valB (List.replicate a false ++ incB (incB t₀)) + 1) := by omega
            _ = 2 * (2 ^ a * (valB (incB (incB t₀)) + 1)) := by rw [h1]
            _ = 2 ^ a * 2 * (valB t₀ + 3) := by rw [valB_incB, valB_incB]; ring
        have hval_in : valB (evalDecomp (.falseThenTrue a t₀)) + 1 =
            2 ^ (a + 1) * (2 * valB t₀ + 3) := by
          simp only [evalDecomp]
          rw [h2]; simp only [valB]; ring
        have hle : 2 ^ (a + 1) * (valB t₀ + 3) ≤ 2 ^ (a + 1) * (2 * valB t₀ + 3) :=
          Nat.mul_le_mul_left _ (by omega)
        omega
      · intro R
        have h := f_core_falseThenTrue a t₀ R
        have he1 : encB (evalDecomp (.falseThenTrue a t₀)) =
            repL00 (a + 1) ((2, .o1) :: encB t₀) := by
          simp [evalDecomp, encB_rep_false, encB]
        have he2 : encB (true :: (List.replicate a false ++ incB (incB t₀))) =
            (2, .o1) :: repL00 a (encB (incB (incB t₀))) := by
          simp [encB, encB_rep_false]
        rw [he1, he2]; exact h

/-!
### Exact `BR` Body Exit Lemmas (all constant-step gadgets via `rfl`)
-/

theorem body_2_100100 (u₀ : List Bool) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
      :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u₀, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
            (2, .o1) :: encB (addB 4 u₀), R) := by
  let u1 := incB u₀
  let u2 := incB u1
  let u3 := incB u2
  let u4 := incB u3
  have hc1 : Call0 ((2, .o1) :: encB u₀) ((2, .o1) :: encB u1) := call0_2 (call1_encB u₀)
  have hc2 : Call0 ((2, .o1) :: encB u1) ((2, .o1) :: encB u2) := call0_2 (call1_encB u1)
  have hc3 : Call0 ((2, .o1) :: encB u2) ((2, .o1) :: encB u3) := call0_2 (call1_encB u2)
  have hc4 : Call0 ((2, .o1) :: encB u3) ((2, .o1) :: encB u4) := call0_2 (call1_encB u3)
  have s1 : MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (1, .o1) :: (0, .o1) ::
    (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u₀, .r2 :: .r2 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u₀, .r1 :: .r2 :: .r1
                    :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨22, by omega, rfl⟩
  have s2 := hc1 (.r1 :: .r2 :: .r1 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
  have s3 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u1, .r1 :: .r2 :: .r1
    :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u1, .r0 :: .r0 :: .r1
                    :: .r1 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨3, by omega, rfl⟩
  have s4 := hc2 (.r0 :: .r0 :: .r1 :: .r1 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
  have s5 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u2, .r0 :: .r0 :: .r1
    :: .r1 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u2, .r1 :: .r2 :: .r1
                    :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨10, by omega, rfl⟩
  have s6 := hc3 (.r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
  have s7 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u3, .r1 :: .r2 :: .r1
    :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
                  (.dl, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u3, .r0 :: .r0 :: .r1
                    :: .r1 :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R) :=
    ⟨3, by omega, rfl⟩
  have s8 := hc4 (.r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
  have s9 : MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u4, .r0 :: .r0 :: .r1
    :: .r1 :: .r0 :: .r0 :: .r1 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
                  (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) ::
                    (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0,
                    .o1) :: (0, .o1) :: (2, .o1) :: encB u4, R) :=
    ⟨11, by omega, rfl⟩
  exact mplus_trans s1 (mplus_trans s2 (mplus_trans s3 (mplus_trans s4 (mplus_trans s5
    (mplus_trans s6 (mplus_trans s7 (mplus_trans s8 s9)))))))

theorem body_m2_000 (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2)
      :: (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1) :: (0, .o1) ::
            u, R) :=
  ⟨43, by omega, rfl⟩

theorem body_m2_0 (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2)
      :: (0, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: u, R) :=
  ⟨43, by omega, rfl⟩

theorem body_m11_000_false (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2)
      :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (2, .o1) :: (0, .o1) ::
            u, R) :=
  ⟨56, by omega, rfl⟩

theorem body_m11_000_true (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2)
      :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (4, .o1) :: u, R) :=
  ⟨56, by omega, rfl⟩

theorem body_m11_0 (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2)
      :: (0, .o1) :: (2, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: (0, .o1) :: u, R) :=
  ⟨55, by omega, rfl⟩

theorem body_100_000 (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1)
      :: (0, .o1) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1) :: (0, .o1) ::
            u, R) :=
  ⟨46, by omega, rfl⟩

theorem body_100_0 (u : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1)
      :: (0, .o1) :: (0, .o1) :: (2, .o1) :: u, .r2 :: .r2 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (2, .o1) :: u, R) :=
  ⟨46, by omega, rfl⟩

theorem body_100_22_in (s : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1)
      :: (2, .o1) :: s, .r2 :: .r2 :: R)
          (.dl, (0, .o1) :: s, .r1 :: .r2 :: .r0 :: .r0 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1
            :: R) :=
  ⟨32, by omega, rfl⟩

theorem body_100_22_out (s : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: s, .r0 ::
      .r0 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
            s, R) :=
  ⟨12, by omega, rfl⟩

theorem body_plain_in (s : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: s, .r2 :: .r2 :: R)
          (.dl, (0, .o1) :: s, .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 :: R) :=
  ⟨19, by omega, rfl⟩

theorem body_plain_out (s : List (ℕ × Ones)) (R : List RSym) :
    MPlus (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: s, .r1 ::
      .r0 :: .r0 :: .r1 :: R)
          (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
            :: (1, .o1) :: (0, .o1) :: (0, .o1) :: s, R) :=
  ⟨4, by omega, rfl⟩

/-!
## Section 5: The 16-Constructor Closed Invariant `Inv284` (Zero `Nat.sub`)
-/

def mkBR1 (ones blocks : ℕ) (body : List (ℕ × Ones)) : State :=
  (.br1, (0, .o1) :: rep1 ones ((0, .o1) :: (0, .o1) :: repBlk blocks body), [])

def mkBR (ones blocks : ℕ) (body : List (ℕ × Ones)) : State :=
  (.br, (0, .o1) :: rep1 ones ((0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0,
    .o1) :: repBlk blocks body), [])

theorem br_wrap_add1 (n k : ℕ) {body out : List (ℕ × Ones)}
    (hmid : ∀ R : List RSym,
      MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: body, .r2 :: .r2 :: R)
            (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
              :: out, R)) :
    MPlus (mkBR (n + 1) k body) (mkBR1 (n + 1) (k + 1) out) := by
  unfold mkBR mkBR1
  rw [← repBlk_snoc k out]
  exact br_wrap n k hmid

theorem br_wrap_add2 (n k : ℕ) {body out : List (ℕ × Ones)}
    (hmid : ∀ R : List RSym,
      MPlus (.dl, (1, .o1) :: (0, .o1) :: (0, .o1) :: body, .r2 :: .r2 :: R)
            (.br, (0, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1)
              ::
                  (1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: out, R)) :
    MPlus (mkBR (n + 1) k body) (mkBR1 (n + 1) (k + 2) out) := by
  unfold mkBR mkBR1
  rw [← repBlk_snoc (k + 1) out, ← repBlk_snoc k _]
  exact br_wrap n k hmid

inductive Inv284 : State → Prop where
  | br1_100 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) ≤ 4 * (m + 4) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 5) (k + 1) ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true :: u)))
  | br_100 (m k : ℕ) (u : List Bool)
      (hlo : 16 ≤ valB (true :: u))
      (hhi : valB (true :: u) ≤ 16 * (m + 3) * 2 ^ k) :
      Inv284 (mkBR (m + 5) k ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true :: u)))
  | br1_2_100100 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) ≤ 4 * (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) ::
        (0, .o1) :: (0, .o1) :: encB (true :: u)))
  | br_2_100100 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) + 8 * 2 ^ k ≤ 16 * (m + 5) * 2 ^ k) :
      Inv284 (mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1)
        :: (0, .o1) :: encB (true :: u)))
  | br1_m2_0 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) + 1 ≤ 2 * (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        encB (true :: u)))
  | br_m2_0 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) + 1 ≤ 4 * (m + 3) * 2 ^ k) :
      Inv284 (mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: encB
        (true :: u)))
  | br1_m11_0 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) + 1 ≤ 2 * (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 6) (k + 1) ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        encB (true :: u)))
  | br_m11_0 (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) + 1 ≤ 4 * (m + 3) * 2 ^ k) :
      Inv284 (mkBR (m + 7) k ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: encB
        (true :: u)))
  | br1_2_0 (m k : ℕ) (u : List Bool)
      (hb : 2 * valB u + 3 ≤ (m + 3) * 2 ^ (k + 2)) :
      Inv284 (mkBR1 (m + 7) (k + 2) ((2, .o1) :: (0, .o1) :: encB u))
  | br1_m2_000 (m k : ℕ) (u : List Bool)
      (hlo : 1 ≤ valB u)
      (hb : valB u + 1 ≤ (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        (0, .o1) :: (0, .o1) :: encB u))
  | br_m2_000 (m k : ℕ) (u : List Bool)
      (hlo : 1 ≤ valB u)
      (hb : valB u + 1 ≤ 2 * (m + 3) * 2 ^ k) :
      Inv284 (mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1)
        :: (0, .o1) :: encB u))
  | br1_m11_000 (m k : ℕ) (u : List Bool)
      (hlo : 1 ≤ valB u)
      (hb : valB u + 1 ≤ (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 6) (k + 1) ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        (0, .o1) :: (0, .o1) :: encB u))
  | br_m11_000 (m k : ℕ) (u : List Bool)
      (hlo : 1 ≤ valB u)
      (hb : valB u + 1 ≤ 2 * (m + 3) * 2 ^ k) :
      Inv284 (mkBR (m + 7) k ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1)
        :: (0, .o1) :: encB u))
  | br1_2_2_0 (m k : ℕ) (u : List Bool)
      (hb : 2 * valB u + 2 ≤ (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 7) (k + 2) ((2, .o1) :: (2, .o1) :: (0, .o1) :: encB u))
  | br1_2_4 (m k : ℕ) (u : List Bool)
      (hb : 2 * valB u + 3 ≤ (m + 3) * 2 ^ (k + 1)) :
      Inv284 (mkBR1 (m + 7) (k + 2) ((2, .o1) :: (4, .o1) :: encB u))
  | br_plain (m k : ℕ) (u : List Bool)
      (hb : valB (true :: u) ≤ 4 * (m + 6) * 2 ^ (k + 1) + 2) :
      Inv284 (mkBR (m + 8) (k + 1) (encB (true :: u)))

theorem inv284_cp682 : Inv284 cp682 := by
  have heq : cp682 = mkBR (0 + 5) 0 ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true :: [true,
    false, true, false])) := rfl
  rw [heq]
  exact Inv284.br_100 0 0 [true, false, true, false] (by decide) (by decide)

theorem inv284_step {s : State} (hs : Inv284 s) : ∃ s', MPlus s s' ∧ Inv284 s' := by
  cases hs with
  | br1_100 m k u hb =>
      let C := (m + 4) * 2 ^ (k + 1)
      let u' := addB (2 * C) u
      refine ⟨mkBR ((m + 1) + 5) k ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true :: u')), ?_, ?_⟩
      · have hcall : Call0N ((m + 3 + 1) * 2 ^ (k + 1))
            ((1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u)
            ((1, .o1) :: (0, .o1) :: (0, .o1) :: (2, .o1) :: encB u') :=
          call0N_100 (call0N_2 (call1N_encB (2 * C) u))
        exact br1_run (m + 3) k hcall
      · apply Inv284.br_100 (m + 1) k u'
        · have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
          simp only [u', C, valB, valB_addB, Nat.pow_succ]
          nlinarith
        · have hval : valB (true :: u') = valB (true :: u) + 4 * C := by
            simp only [u', valB, valB_addB]; omega
          rw [hval]
          have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
          dsimp only [C] at hb ⊢
          nlinarith
  | br_100 m k u hlo hhi =>
      cases u with
      | nil => simp [valB] at hlo
      | cons b1 r1 =>
          cases b1 with
          | true =>
              obtain ⟨t, ht_le, ht_run⟩ := f_core_ex r1
              refine ⟨mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1,
                .o1) :: (0, .o1) :: (0, .o1) :: encB (true :: t)), ?_, ?_⟩
              · exact br_wrap_add1 (m + 4) k (fun R =>
                  mplus_trans (body_100_22_in (encB r1) R)
                    (mplus_trans (ht_run (.r0 :: .r0 :: .r1 :: .r2 :: .r1 :: .r0 :: .r0 :: .r1 ::
                      R))
                      (body_100_22_out (encB (true :: t)) R)))
              · apply Inv284.br1_2_100100 m k t
                have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
                simp only [valB] at hhi
                nlinarith
          | false =>
              cases r1 with
              | nil => simp [valB] at hlo
              | cons b2 r2 =>
                  cases b2 with
                  | true =>
                      refine ⟨mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0,
                        .o2) :: (0, .o1) :: encB (true :: r2)), ?_, ?_⟩
                      · exact br_wrap_add1 (m + 4) k (body_100_0 (encB r2))
                      · apply Inv284.br1_m2_0 m k r2
                        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
                        simp only [valB] at hhi ⊢
                        nlinarith
                  | false =>
                      refine ⟨mkBR1 (m + 5) (k + 1) ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0,
                        .o2) :: (0, .o1) :: (0, .o1) :: (0, .o1) :: encB r2), ?_, ?_⟩
                      · exact br_wrap_add1 (m + 4) k (body_100_000 (encB r2))
                      · apply Inv284.br1_m2_000 m k r2
                        · simp only [valB] at hlo; omega
                        · have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
                          simp only [valB] at hhi
                          nlinarith
  | br1_2_100100 m k u hb =>
      let C := (m + 4) * 2 ^ (k + 1)
      let u' := addB (2 * C) u
      refine ⟨mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1)
        :: (0, .o1) :: encB (true :: u')), ?_, ?_⟩
      · have hcall : Call0N ((m + 3 + 1) * 2 ^ (k + 1))
            ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
              (2, .o1) :: encB u)
            ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o1) ::
              (2, .o1) :: encB u') :=
          call0N_2 (call1N_100 (call0N_100 (call0N_2 (call1N_encB (2 * C) u))))
        exact br1_run (m + 3) k hcall
      · apply Inv284.br_2_100100 m k u'
        have hval : valB (true :: u') = valB (true :: u) + 4 * C := by
          simp only [u', valB, valB_addB]; omega
        rw [hval]
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        dsimp only [C]
        rw [hpow] at hb ⊢
        calc valB (true :: u) + 4 * ((m + 4) * (2 * 2 ^ k)) + 8 * 2 ^ k
            ≤ 4 * (m + 3) * (2 * 2 ^ k) + 4 * ((m + 4) * (2 * 2 ^ k)) + 8 * 2 ^ k := by omega
          _ = (16 * m + 64) * 2 ^ k := by ring
          _ ≤ 16 * (m + 5) * 2 ^ k := by
              rw [show 16 * (m + 5) * 2 ^ k = (16 * m + 80) * 2 ^ k by ring]
              exact Nat.mul_le_mul_right _ (by omega)
  | br_2_100100 m k u hb =>
      refine ⟨mkBR1 ((m + 1) + 5) ((k + 1) + 1) ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true ::
        addB 4 u)), ?_, ?_⟩
      · exact br_wrap_add2 (m + 5) k (body_2_100100 u)
      · apply Inv284.br1_100 (m + 1) (k + 1) (addB 4 u)
        have hval : valB (true :: addB 4 u) = valB (true :: u) + 8 := by
          simp only [valB, valB_addB]; omega
        rw [hval]
        have hp : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        have hpow : 2 ^ ((k + 1) + 1) = 4 * 2 ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; ring
        nlinarith
  | br1_m2_0 m k u hb =>
      refine ⟨mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: encB
        (true :: u)), ?_, ?_⟩
      · exact br1_run (m + 3) k (call0N_2 (call1N_M1 _ ((0, .o1) :: encB (true :: u))))
      · apply Inv284.br_m2_0 m k u
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br_m2_0 m k u hb =>
      refine ⟨mkBR1 (m + 6) (k + 1) ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        encB (true :: u)), ?_, ?_⟩
      · exact br_wrap_add1 (m + 5) k (body_m2_0 (encB (true :: u)))
      · apply Inv284.br1_m11_0 m k u
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br1_m11_0 m k u hb =>
      refine ⟨mkBR (m + 7) k ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: encB
        (true :: u)), ?_, ?_⟩
      · exact br1_run (m + 4) k (call0N_M11 _ ((0, .o1) :: encB (true :: u)))
      · apply Inv284.br_m11_0 m k u
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br_m11_0 m k u hb =>
      refine ⟨mkBR1 (m + 7) (k + 2) ((2, .o1) :: (0, .o1) :: encB u), ?_, ?_⟩
      · exact br_wrap_add2 (m + 6) k (body_m11_0 (encB u))
      · apply Inv284.br1_2_0 m k u
        have hpow : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [Nat.pow_succ, Nat.pow_succ]; ring
        simp only [valB] at hb
        nlinarith
  | br1_2_0 m k u hb =>
      let C := (m + 6) * 2 ^ (k + 2)
      have hneed : 2 ^ u.length + 2 * valW u ≤ C := by
        have h1 := need_le_valB u
        have hp : 1 ≤ 2 ^ (k + 2) := Nat.one_le_two_pow
        dsimp only [C]; nlinarith
      obtain ⟨v, hv_call, hv_val⟩ := call0N_erase_2_0 u C hneed
      refine ⟨mkBR (m + 8) (k + 1) (encB (true :: v)), ?_, ?_⟩
      · exact br1_run (m + 5) (k + 1) hv_call
      · apply Inv284.br_plain m k v
        have hpow : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
        dsimp only [C] at hv_val
        nlinarith
  | br1_m2_000 m k u hlo hb =>
      refine ⟨mkBR (m + 6) k ((2, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1)
        :: (0, .o1) :: encB u), ?_, ?_⟩
      · exact br1_run (m + 3) k (call0N_2 (call1N_M1 _ ((0, .o1) :: (0, .o1) :: (0, .o1) :: encB
          u)))
      · apply Inv284.br_m2_000 m k u hlo
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br_m2_000 m k u hlo hb =>
      refine ⟨mkBR1 (m + 6) (k + 1) ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) ::
        (0, .o1) :: (0, .o1) :: encB u), ?_, ?_⟩
      · exact br_wrap_add1 (m + 5) k (body_m2_000 (encB u))
      · apply Inv284.br1_m11_000 m k u hlo
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br1_m11_000 m k u hlo hb =>
      refine ⟨mkBR (m + 7) k ((1, .o1) :: (1, .o1) :: (0, .o1) :: (0, .o2) :: (0, .o1) :: (0, .o1)
        :: (0, .o1) :: encB u), ?_, ?_⟩
      · exact br1_run (m + 4) k (call0N_M11 _ ((0, .o1) :: (0, .o1) :: (0, .o1) :: encB u))
      · apply Inv284.br_m11_000 m k u hlo
        have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
        nlinarith
  | br_m11_000 m k u hlo hb =>
      cases u with
      | nil => simp [valB] at hlo
      | cons b r =>
          cases b with
          | false =>
              refine ⟨mkBR1 (m + 7) (k + 2) ((2, .o1) :: (2, .o1) :: (0, .o1) :: encB r), ?_, ?_⟩
              · exact br_wrap_add2 (m + 6) k (body_m11_000_false (encB r))
              · apply Inv284.br1_2_2_0 m k r
                have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
                simp only [valB] at hb
                nlinarith
          | true =>
              refine ⟨mkBR1 (m + 7) (k + 2) ((2, .o1) :: (4, .o1) :: encB r), ?_, ?_⟩
              · exact br_wrap_add2 (m + 6) k (body_m11_000_true (encB r))
              · apply Inv284.br1_2_4 m k r
                have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ]; ring
                simp only [valB] at hb
                nlinarith
  | br1_2_2_0 m k u hb =>
      let q := (m + 6) * 2 ^ (k + 1)
      have hneed : 2 ^ u.length + 2 * valW u ≤ q := by
        have h1 := need_le_valB u
        have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
        dsimp only [q]; nlinarith
      obtain ⟨v, hv_call, hv_val⟩ := call0N_erase_2_2_0 u q hneed
      have heq : 2 * q = (m + 5 + 1) * 2 ^ ((k + 1) + 1) := by
        dsimp only [q]; rw [Nat.pow_succ]; ring
      rw [heq] at hv_call
      refine ⟨mkBR (m + 8) (k + 1) (encB (true :: true :: v)), ?_, ?_⟩
      · exact br1_run (m + 5) (k + 1) hv_call
      · apply Inv284.br_plain m k (true :: v)
        dsimp only [q] at hv_val
        rw [show 4 * (m + 6) * 2 ^ (k + 1) = 4 * ((m + 6) * 2 ^ (k + 1)) by ring]
        omega
  | br1_2_4 m k u hb =>
      let q := (m + 6) * 2 ^ (k + 1)
      have hneed : 1 + (2 ^ u.length + 2 * valW u) ≤ q := by
        have h1 := need_le_valB u
        have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
        dsimp only [q]; nlinarith
      obtain ⟨v, hv_call, hv_val⟩ := call0N_erase_2_4 u q hneed
      have heq : 2 * q = (m + 5 + 1) * 2 ^ ((k + 1) + 1) := by
        dsimp only [q]; rw [Nat.pow_succ]; ring
      rw [heq] at hv_call
      refine ⟨mkBR (m + 8) (k + 1) (encB (true :: true :: v)), ?_, ?_⟩
      · exact br1_run (m + 5) (k + 1) hv_call
      · apply Inv284.br_plain m k (true :: v)
        dsimp only [q] at hv_val
        rw [show 4 * (m + 6) * 2 ^ (k + 1) = 4 * ((m + 6) * 2 ^ (k + 1)) by ring]
        omega
  | br_plain m k u hb =>
      obtain ⟨t, ht_le, ht_run⟩ := f_core_ex u
      refine ⟨mkBR1 ((m + 3) + 5) ((k + 1) + 1) ((1, .o1) :: (0, .o1) :: (0, .o1) :: encB (true ::
        t)), ?_, ?_⟩
      · exact br_wrap_add1 (m + 7) (k + 1) (fun R =>
          mplus_trans (body_plain_in (encB u) R)
            (mplus_trans (ht_run (.r1 :: .r0 :: .r0 :: .r1 :: R))
              (body_plain_out (encB (true :: t)) R)))
      · apply Inv284.br1_100 (m + 3) (k + 1) t
        have hpow : 2 ^ ((k + 1) + 1) = 2 * 2 ^ (k + 1) := by rw [Nat.pow_succ]; ring
        have hp : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow
        simp only [valB] at hb
        nlinarith

end Impl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  have hinit : ReachesStar target_tm (init []) (Impl.evalCfg Impl.cp682) :=
    stepPlus_stepStar (stepPlus_trans Impl.init_to_br1 (Impl.mplus_sound Impl.br1_to_cp682))
  refine IsNotHalt.of_reachesPlus_invariant (P := fun c => ∃ s, Impl.Inv284 s ∧ c = Impl.evalCfg s)
    hinit ⟨Impl.cp682, Impl.inv284_cp682, rfl⟩ ?_
  intro c ⟨s, hs, hc⟩
  subst hc
  obtain ⟨s', hstep, hs'⟩ := Impl.inv284_step hs
  exact ⟨Impl.evalCfg s', Impl.mplus_sound hstep, s', hs', rfl⟩

private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH
