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

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 1 => none


private def A : Fin 6 := 0
private def B : Fin 6 := 1
private def D : Fin 6 := 3


private theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
private theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
private theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
private theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
private theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
private theorem init_nil : (init ([] : List (Fin 2))) = (default {{A}}> default) := rfl

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  try simp only [zero_cons_default, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    default_head, default_tail, multiStep_zero, listblank_append_cons, listblank_append_nil]
  rfl))
local macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      default_head]
  apply step_stepStar_stepPlus (by rfl)
  try simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

/-! ## Constructive Step-Indexed Safety (`Safe k c`) -/

private def Safe (k : ℕ) (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∀ j ≤ k, ∀ c', multiStep target_tm c j = some c' → (step target_tm c').isSome

private theorem multiStep_zero_eq (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target_tm c 0 = some c := rfl

private theorem multiStep_succ_eq (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep target_tm c (n + 1) = (multiStep target_tm c n).bind (step target_tm) :=
  Function.iterate_succ_apply' (Option.bind · (step target_tm)) n (some c)

private theorem multiStep_add_eq (c c₁ : Cfg (Fin 2) (Fin 6)) (a b : ℕ)
    (h : multiStep target_tm c a = some c₁) :
    multiStep target_tm c (a + b) = multiStep target_tm c₁ b := by
  induction b with
  | zero => exact h
  | succ b ih =>
    rw [← Nat.add_assoc, multiStep_succ_eq, ih, multiStep_succ_eq]

private theorem multiStep_none_succ
    (c : Cfg (Fin 2) (Fin 6)) (hs : step target_tm c = none) (m : ℕ) :
    multiStep target_tm c (m + 1) = none := by
  induction m with
  | zero =>
    rw [multiStep_succ_eq, multiStep_zero_eq]
    exact hs
  | succ m ih =>
    rw [multiStep_succ_eq, ih]
    rfl

private theorem multiStep_prefix_isSome {c c' : Cfg (Fin 2) (Fin 6)} {n j : ℕ}
    (h : multiStep target_tm c n = some c') (hj : j < n)
    {cj : Cfg (Fin 2) (Fin 6)} (hcj : multiStep target_tm c j = some cj) :
    (step target_tm cj).isSome := by
  have hsplit : n = j + (n - j - 1 + 1) := by omega
  rw [hsplit, multiStep_add_eq c cj j (n - j - 1 + 1) hcj] at h
  cases hs : step target_tm cj with
  | none =>
    rw [multiStep_none_succ cj hs (n - j - 1)] at h
    cases h
  | some _ => rfl

private theorem Safe_of_stepPlus {k : ℕ} {c c' : Cfg (Fin 2) (Fin 6)}
    (h : c [target_tm]⊢⁺ c') (hsafe : ∀ k' < k, Safe k' c') :
    Safe k c := by
  rcases h with ⟨n, hn, hreach⟩
  intro j hj cⱼ hcj
  rcases Nat.lt_or_ge j n with hlt | hge
  · exact multiStep_prefix_isSome hreach hlt hcj
  · have hjeq : j = n + (j - n) := by omega
    rw [hjeq, multiStep_add_eq c c' n (j - n) hreach] at hcj
    exact hsafe (k - n) (by omega) (j - n) (by omega) cⱼ hcj

private theorem isNotHalt_of_forall_safe (c₀ : Cfg (Fin 2) (Fin 6))
    (hinit : (init []) [target_tm]⊢⁺ c₀)
    (hsafe : ∀ k, Safe k c₀) : IsNotHalt target_tm := by
  rcases hinit with ⟨n₀, hn₀, hreach⟩
  intro cfg ⟨m, hm⟩
  rcases Nat.lt_or_ge m n₀ with hlt | hge
  · exact multiStep_prefix_isSome hreach hlt hm
  · have hmeq : m = n₀ + (m - n₀) := by omega
    rw [hmeq, multiStep_add_eq (init []) c₀ n₀ (m - n₀) hreach] at hm
    exact hsafe (m - n₀) (m - n₀) (Nat.le_refl _) cfg hm

/-! ## Pillar 1: Prefix-Separator Bitstring Transducer (`encBits`) -/

/-- Separator bitstring encoding on the left half-tape:
    `false` pushes `0`, `true :: false` pushes `1 0`, `true :: true` pushes `1 1 0`.
    Under `encBits`, `[true, false, false]` encodes `[1, 0, 0]`,
    `[false, true, false, false]` encodes `[0, 1, 0, 0]`, and
    `[true, true]` encodes `[1, 1, 0]`, while collars `[0]`, `[0, 0]`, and `[1, 0]`
    are encoded directly by `false :: xs`, `false :: false :: xs`, and `true :: false :: xs`. -/
private def encBits : List Bool → ListBlank (Fin 2)
  | [] => default
  | false :: xs => (0 : Fin 2) >> encBits xs
  | [true] => (1 : Fin 2) >> default
  | true :: false :: xs => (1 : Fin 2) >> (0 : Fin 2) >> encBits xs
  | true :: true :: xs => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encBits xs

private def cfgTop (xs : List Bool) : Cfg (Fin 2) (Fin 6) :=
  (encBits (true :: false :: xs)) {{B}}> default

private def cfgB (xs : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (encBits xs) {{B}}> ((0 : Fin 2) >> r)

private def cfgD (xs : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (encBits (false :: false :: xs)) {{D}}> r

private def cfgA (xs : List Bool) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (encBits (false :: xs)) {{A}}> r

/-! ## Pillar 2: Finite `Prop`-Valued Block-DFA (`Q5` & `InL`) -/

/-- 5-state finite automaton recognizing valid separator-encoded token bitstrings
    `{[true, false, false], [false, true, false, false], [true, true]}^*`. -/
private inductive Q5 where
  | q0
  | qT
  | qTF
  | qFT
  | qFTF

private def InL : Q5 → List Bool → Prop
  | .q0, [] => True
  | .q0, true :: xs => InL .qT xs
  | .q0, false :: xs => InL .qFT xs
  | .qT, true :: xs => InL .q0 xs
  | .qT, false :: xs => InL .qTF xs
  | .qTF, false :: xs => InL .q0 xs
  | .qFT, true :: xs => InL .qFTF xs
  | .qFTF, false :: xs => InL .qTF xs
  | _, _ => False

private inductive TokDecomp : List Bool → Type where
  | emp : TokDecomp []
  | w100 (u : List Bool) : InL .q0 u → TokDecomp (true :: false :: false :: u)
  | w0100 (u : List Bool) : InL .q0 u → TokDecomp (false :: true :: false :: false :: u)
  | w110 (u : List Bool) : InL .q0 u → TokDecomp (true :: true :: u)

private def inl_decomp : ∀ (xs : List Bool), InL .q0 xs → TokDecomp xs
  | [], _ => .emp
  | [true], h => False.elim h
  | [false], h => False.elim h
  | true :: true :: u, h => .w110 u h
  | [true, false], h => False.elim h
  | true :: false :: true :: _, h => False.elim h
  | true :: false :: false :: u, h => .w100 u h
  | false :: false :: _, h => False.elim h
  | [false, true], h => False.elim h
  | false :: true :: true :: _, h => False.elim h
  | [false, true, false], h => False.elim h
  | false :: true :: false :: true :: _, h => False.elim h
  | false :: true :: false :: false :: u, h => .w0100 u h

/-! ## Phase-Exact Stream-Gap Potential (`potBits`) -/

private def is110Head : List Bool → Bool
  | true :: true :: _ => true
  | _ => false

private def tokLen : List Bool → ℕ
  | [] => 0
  | [true] => 0
  | [false] => 0
  | true :: true :: u => tokLen u + 1
  | [true, false] => 0
  | true :: false :: true :: _ => 0
  | true :: false :: false :: u => tokLen u + 1
  | false :: false :: _ => 0
  | [false, true] => 0
  | false :: true :: true :: _ => 0
  | [false, true, false] => 0
  | false :: true :: false :: true :: _ => 0
  | false :: true :: false :: false :: u => tokLen u + 1

private def step110_100 (cv Gv : ℕ) : Option (ℕ × ℕ) :=
  match Gv with
  | 0 => none
  | Gv' + 1 =>
    match cv % 3 with
    | 2 => some ((cv + 1) / 3, Gv' + 2)
    | 1 => some (cv / 3, Gv' + 1)
    | _ =>
      match Nat.ble (Gv' + 1) cv with
      | true => none
      | false => some (cv / 3, Gv' / 3)

private def potBits : List Bool → Option (ℕ × ℕ)
  | [] => some (0, 0)
  | true :: false :: false :: u =>
    match potBits u with
    | none => none
    | some (cu, Gu) => some (cu + 1, Gu + 1)
  | false :: true :: false :: false :: u =>
    match potBits u with
    | none => none
    | some (cu, _) => some (0, cu + 1)
  | [true, true] => some (0, 0)
  | true :: true :: false :: true :: false :: false :: v =>
    match potBits v with
    | none => none
    | some (cv, _) => some (0, cv + 1)
  | true :: true :: true :: true :: z => potBits (true :: true :: z)
  | true :: true :: true :: false :: false :: v =>
    match potBits v with
    | none => none
    | some (cv, Gv) => step110_100 cv Gv
  | _ => none
termination_by xs => xs.length

private theorem potBits_110_of_is110Head
    {u : List Bool} (hu : InL .q0 u) (hh : is110Head u = true) :
    potBits (true :: true :: u) = potBits u := by
  cases inl_decomp u hu with
  | emp => cases hh
  | w100 _ _ => cases hh
  | w0100 _ _ => cases hh
  | w110 z _ => exact potBits.eq_6 z

private theorem step110_100_le {cv Gv c G : ℕ} (hcv : cv ≤ Gv) (hs : step110_100 cv Gv = some (c,
    G)) :
    c ≤ G := by
  unfold step110_100 at hs
  cases Gv with
  | zero => cases hs
  | succ Gv' =>
    have hmod : cv % 3 = 0 ∨ cv % 3 = 1 ∨ cv % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rw [h0] at hs
      dsimp only at hs
      cases hble : Nat.ble (Gv' + 1) cv
      · rw [hble] at hs
        injection hs with hs'
        injection hs' with hc hG
        have hlt : ¬ (Gv' + 1 ≤ cv) := by
          intro hle
          have hb : Nat.ble (Gv' + 1) cv = true := Nat.ble_eq.mpr hle
          rw [hble] at hb
          cases hb
        omega
      · rw [hble] at hs
        cases hs
    · rw [h1] at hs
      injection hs with hs'
      injection hs' with hc hG
      omega
    · rw [h2] at hs
      injection hs with hs'
      injection hs' with hc hG
      omega

private theorem potBits_le : ∀ (n : ℕ) {xs : List Bool} {c G : ℕ},
    xs.length ≤ n → InL .q0 xs → potBits xs = some (c, G) → c ≤ G
  | 0, xs, c, G, hlen, _, hpot => by
    cases xs with
    | nil =>
      rw [potBits.eq_1] at hpot
      injection hpot with hp
      injection hp with hc hG
      omega
    | cons _ _ => simp at hlen
  | n + 1, xs, c, G, hlen, hIn, hpot => by
    cases inl_decomp xs hIn with
    | emp =>
      rw [potBits.eq_1] at hpot
      injection hpot with hp
      injection hp with hc hG
      omega
    | w100 u hu =>
      rw [potBits.eq_2] at hpot
      cases hpu : potBits u with
      | none => rw [hpu] at hpot; cases hpot
      | some p =>
        rw [hpu] at hpot
        rcases p with ⟨cu, Gu⟩
        injection hpot with hp
        injection hp with hc hG
        have ih := potBits_le n (by simp at hlen; omega) hu hpu
        omega
    | w0100 u _ =>
      rw [potBits.eq_3] at hpot
      cases hpu : potBits u with
      | none => rw [hpu] at hpot; cases hpot
      | some p =>
        rw [hpu] at hpot
        rcases p with ⟨cu, Gu⟩
        injection hpot with hp
        injection hp with hc hG
        omega
    | w110 u hu =>
      cases inl_decomp u hu with
      | emp =>
        rw [potBits.eq_4] at hpot
        injection hpot with hp
        injection hp with hc hG
        omega
      | w0100 v _ =>
        rw [potBits.eq_5] at hpot
        cases hpv : potBits v with
        | none => rw [hpv] at hpot; cases hpot
        | some p =>
          rw [hpv] at hpot
          rcases p with ⟨cv, Gv⟩
          injection hpot with hp
          injection hp with hc hG
          omega
      | w110 z _ =>
        rw [potBits.eq_6] at hpot
        exact potBits_le n (by simp only [List.length_cons] at hlen ⊢; omega) hu hpot
      | w100 v hv =>
        rw [potBits.eq_7] at hpot
        cases hpv : potBits v with
        | none => rw [hpv] at hpot; cases hpot
        | some p =>
          rw [hpv] at hpot
          dsimp only at hpot
          rcases p with ⟨cv, Gv⟩
          have ih := potBits_le n (by simp only [List.length_cons] at hlen; omega) hv hpv
          exact step110_100_le ih hpot

private theorem potBits_c_le_G {xs : List Bool} {c G : ℕ} (hIn : InL .q0 xs)
    (hpot : potBits xs = some (c, G)) : c ≤ G :=
  potBits_le xs.length (Nat.le_refl _) hIn hpot

private theorem step110_100_succ3 {cv Gv c G Gv3 : ℕ}
    (hs : step110_100 (cv + 3) Gv = some (c + 1, G))
    (hG : Gv ≤ Gv3) :
    ∃ G1, step110_100 cv Gv3 = some (c, G1) ∧ G ≤ G1 := by
  unfold step110_100 at hs ⊢
  cases Gv with
  | zero => cases hs
  | succ Gv' =>
    obtain ⟨Gv3', rfl⟩ : ∃ Gv3', Gv3 = Gv3' + 1 := by
      cases Gv3 with
      | zero => omega
      | succ m => exact ⟨m, rfl⟩
    have hdiv_le : Gv' / 3 ≤ Gv3' / 3 := Nat.div_le_div_right (by omega)
    have hmod_eq : (cv + 3) % 3 = cv % 3 := Nat.add_mod_right cv 3
    rw [hmod_eq] at hs
    have hmod : cv % 3 = 0 ∨ cv % 3 = 1 ∨ cv % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rw [h0] at hs ⊢
      dsimp only at hs ⊢
      cases hble : Nat.ble (Gv' + 1) (cv + 3)
      · rw [hble] at hs
        dsimp only at hs
        have hdiv : (cv + 3) / 3 = cv / 3 + 1 := Nat.add_div_right cv (by omega)
        rw [hdiv] at hs
        injection hs with hs'
        injection hs' with hc hG0
        have hlt : ¬ (Gv' + 1 ≤ cv + 3) := by
          intro hle
          have hb : Nat.ble (Gv' + 1) (cv + 3) = true := Nat.ble_eq.mpr hle
          rw [hble] at hb
          cases hb
        have hble2 : Nat.ble (Gv3' + 1) cv = false := by
          cases hb2 : Nat.ble (Gv3' + 1) cv
          · rfl
          · have hle2 : Gv3' + 1 ≤ cv := Nat.ble_eq.mp hb2
            omega
        rw [hble2]
        dsimp only
        have hc_eq : cv / 3 = c := Nat.succ.inj hc
        rw [hc_eq, ← hG0]
        exact ⟨Gv3' / 3, rfl, hdiv_le⟩
      · rw [hble] at hs; cases hs
    · rw [h1] at hs ⊢
      dsimp only at hs ⊢
      have hdiv : (cv + 3) / 3 = cv / 3 + 1 := Nat.add_div_right cv (by omega)
      rw [hdiv] at hs
      injection hs with hs'
      injection hs' with hc hG0
      have hc_eq : cv / 3 = c := Nat.succ.inj hc
      rw [hc_eq]
      exact ⟨Gv3' + 1, rfl, by omega⟩
    · rw [h2] at hs ⊢
      dsimp only at hs ⊢
      have hdiv : (cv + 3 + 1) / 3 = (cv + 1) / 3 + 1 := by
        have heq : cv + 3 + 1 = (cv + 1) + 3 := by omega
        rw [heq]
        exact Nat.add_div_right (cv + 1) (by omega)
      rw [hdiv] at hs
      injection hs with hs'
      injection hs' with hc hG0
      have hc_eq : (cv + 1) / 3 = c := Nat.succ.inj hc
      rw [hc_eq]
      exact ⟨Gv3' + 2, rfl, by omega⟩

private theorem step110_100_c0_preserve {Gv' c2 Gv3 : ℕ}
    (hc2 : Gv' ≤ c2 + 1) (hG : Gv' + 1 ≤ Gv3) (hlt : c2 < Gv3) :
    ∃ c_out G_out, step110_100 c2 Gv3 = some (c_out, G_out) ∧
      Gv' / 3 ≤ c_out ∧ Gv' / 3 ≤ G_out := by
  unfold step110_100
  cases Gv3 with
  | zero => omega
  | succ Gv3' =>
    have hmod : c2 % 3 = 0 ∨ c2 % 3 = 1 ∨ c2 % 3 = 2 := by omega
    rcases hmod with h0 | h1 | h2
    · rw [h0]; dsimp only
      have hble : Nat.ble (Gv3' + 1) c2 = false := by
        cases hb : Nat.ble (Gv3' + 1) c2
        · rfl
        · have hle : Gv3' + 1 ≤ c2 := Nat.ble_eq.mp hb
          omega
      rw [hble]
      exact ⟨c2 / 3, Gv3' / 3, rfl, by omega, by omega⟩
    · rw [h1]; dsimp only
      exact ⟨c2 / 3, Gv3' + 1, rfl, by omega, by omega⟩
    · rw [h2]; dsimp only
      exact ⟨(c2 + 1) / 3, Gv3' + 2, rfl, by omega, by omega⟩

/-! ## Symbolic TM Micro-Step Lemmas -/

private theorem encBits_nil : encBits [] = default := rfl
private theorem encBits_f (xs : List Bool) : encBits (false :: xs) = (0 : Fin 2) >> encBits xs :=
    rfl
private theorem encBits_tf (xs : List Bool) :
    encBits (true :: false :: xs) = (1 : Fin 2) >> (0 : Fin 2) >> encBits xs := rfl
private theorem encBits_tt (xs : List Bool) :
    encBits (true :: true :: xs) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encBits xs := rfl

private theorem init_to_top : (init []) [target_tm]⊢⁺ (cfgTop []) := by
  rw [init_nil]
  unfold cfgTop
  simp only [encBits_tf, encBits_nil, zero_cons_default]
  execute 1

private theorem top_enter (xs : List Bool) :
    (cfgTop xs) [target_tm]⊢⁺ (cfgB xs ([0, 1] +> default)) := by
  unfold cfgTop cfgB
  simp only [encBits_tf]
  execute 2

private theorem top_ret_A (xs : List Bool) :
    (cfgA xs ([0, 1] +> default)) [target_tm]⊢⁺ (cfgTop (true :: true :: xs)) := by
  unfold cfgA cfgTop
  simp only [encBits_f, encBits_tf, encBits_tt]
  execute 6

private theorem top_ret_D (xs : List Bool) :
    (cfgD xs ([0, 1] +> default)) [target_tm]⊢⁺ (cfgB xs ([1] +> default)) := by
  unfold cfgD cfgB
  simp only [encBits_f]
  execute 4

private theorem top_ret_DD (xs : List Bool) :
    (cfgD xs ([1] +> default)) [target_tm]⊢⁺ (cfgTop (false :: true :: false :: false :: xs)) := by
  unfold cfgD cfgTop
  simp only [encBits_f, encBits_tf]
  execute 4

private theorem top_ret_DA (xs : List Bool) :
    (cfgA xs ([1] +> default)) [target_tm]⊢⁺ (cfgTop (true :: false :: false :: xs)) := by
  unfold cfgA cfgTop
  simp only [encBits_f, encBits_tf]
  execute 4

private theorem box_emp (r : ListBlank (Fin 2)) :
    (cfgB [] r) [target_tm]⊢⁺ (cfgD [] r) := by
  unfold cfgB cfgD
  simp only [encBits_nil, encBits_f, zero_cons_default]
  execute 3

private theorem box_0100 (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgB (false :: true :: false :: false :: u) r) [target_tm]⊢⁺
      (cfgD (true :: false :: false :: u) r) := by
  unfold cfgB cfgD
  simp only [encBits_f, encBits_tf]
  execute 3

private theorem box_100 (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgB (true :: false :: false :: u) r) [target_tm]⊢⁺ (cfgB u ([1, 0, 0] +> r)) := by
  unfold cfgB
  simp only [encBits_tf, encBits_f]
  execute 9

private theorem ret_100_D (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD u ([1, 0, 0] +> r)) [target_tm]⊢⁺ (cfgA (false :: true :: false :: false :: u) r) := by
  unfold cfgD cfgA
  simp only [encBits_f, encBits_tf]
  execute 3

private theorem ret_100_A (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA u ([1, 0, 0] +> r)) [target_tm]⊢⁺ (cfgA (true :: false :: false :: u) r) := by
  unfold cfgA
  simp only [encBits_f, encBits_tf]
  execute 3

private theorem box_110_emp (r : ListBlank (Fin 2)) :
    (cfgB [true, true] r) [target_tm]⊢⁺ (cfgD [false, true, false, false] r) := by
  unfold cfgB cfgD
  simp only [encBits_tt, encBits_f, encBits_tf, encBits_nil, zero_cons_default]
  execute 11

private theorem box_110_0100 (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgB (true :: true :: false :: true :: false :: false :: v) r) [target_tm]⊢⁺
      (cfgB v ([1, 0, 0, 1, 0, 0, 1] +> r)) := by
  unfold cfgB
  simp only [encBits_tt, encBits_f, encBits_tf]
  execute 13

private theorem ret_110_0100_D (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD v ([1, 0, 0, 1, 0, 0, 1] +> r)) [target_tm]⊢⁺
      (cfgD (true :: false :: false :: false :: true :: false :: false :: v) r) := by
  unfold cfgD
  simp only [encBits_f, encBits_tf]
  execute 7

private theorem ret_110_0100_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 0, 1, 0, 0, 1] +> r)) [target_tm]⊢⁺
      (cfgD (true :: false :: false :: true :: false :: false :: v) r) := by
  unfold cfgA cfgD
  simp only [encBits_f, encBits_tf]
  execute 7

private theorem box_110_110 (z : List Bool) (r : ListBlank (Fin 2)) :
    (cfgB (true :: true :: true :: true :: z) r) [target_tm]⊢⁺
      (cfgB (true :: true :: z) ([0, 1, 1] +> r)) := by
  unfold cfgB
  simp only [encBits_tt]
  execute 15

private theorem ret_110_110_A (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA u ([0, 1, 1] +> r)) [target_tm]⊢⁺ (cfgA (true :: true :: u) r) := by
  unfold cfgA
  simp only [encBits_f, encBits_tt]
  execute 9

private theorem ret_110_110_D (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD u ([0, 1, 1] +> r)) [target_tm]⊢⁺ (cfgB u ([1, 0, 0, 1] +> r)) := by
  unfold cfgD cfgB
  simp only [encBits_f]
  execute 4

private theorem ret_1001_D (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD u ([1, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgD (false :: true :: false :: false :: u) r) := by
  unfold cfgD
  simp only [encBits_f, encBits_tf]
  execute 4

private theorem ret_1001_A (u : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA u ([1, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgD (true :: false :: false :: u) r) := by
  unfold cfgA cfgD
  simp only [encBits_f, encBits_tf]
  execute 4

private theorem box_110_100 (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgB (true :: true :: true :: false :: false :: v) r) [target_tm]⊢⁺
      (cfgB v ([1, 0, 1, 0, 0, 1] +> r)) := by
  unfold cfgB
  simp only [encBits_tt, encBits_tf, encBits_f]
  execute 6

private theorem ret_101001_D (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD v ([1, 0, 1, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgB v ([1, 0, 0, 0, 0, 0, 1] +> r)) := by
  unfold cfgD cfgB
  simp only [encBits_f]
  execute 12

private theorem ret_1000001_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 0, 0, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgB v ([1, 0, 0, 0, 1, 0, 1] +> r)) := by
  unfold cfgA cfgB
  simp only [encBits_f]
  execute 15

private theorem ret_1000101_D (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD v ([1, 0, 0, 0, 1, 0, 1] +> r)) [target_tm]⊢⁺
      (cfgD (true :: true :: false :: true :: false :: false :: v) r) := by
  unfold cfgD
  simp only [encBits_f, encBits_tt, encBits_tf]
  execute 9

private theorem ret_1000101_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 0, 0, 1, 0, 1] +> r)) [target_tm]⊢⁺
      (cfgD (true :: true :: true :: false :: false :: v) r) := by
  unfold cfgA cfgD
  simp only [encBits_f, encBits_tt, encBits_tf]
  execute 9

private theorem ret_101001_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 1, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgB v ([1, 0, 0, 0, 0, 1] +> r)) := by
  unfold cfgA cfgB
  simp only [encBits_f]
  execute 5

private theorem ret_100001_D (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD v ([1, 0, 0, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgB v ([1, 0, 0, 1, 0, 0, 1] +> r)) := by
  unfold cfgD cfgB
  simp only [encBits_f]
  execute 22

private theorem ret_100001_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 0, 0, 0, 1] +> r)) [target_tm]⊢⁺ (cfgB v ([1, 0, 0, 0, 1, 1] +> r)) := by
  unfold cfgA cfgB
  simp only [encBits_f]
  execute 15

private theorem ret_100011_D (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgD v ([1, 0, 0, 0, 1, 1] +> r)) [target_tm]⊢⁺
      (cfgA (true :: true :: false :: true :: false :: false :: v) r) := by
  unfold cfgD cfgA
  simp only [encBits_f, encBits_tt, encBits_tf]
  execute 12

private theorem ret_100011_A (v : List Bool) (r : ListBlank (Fin 2)) :
    (cfgA v ([1, 0, 0, 0, 1, 1] +> r)) [target_tm]⊢⁺
      (cfgA (true :: true :: true :: false :: false :: v) r) := by
  unfold cfgA
  simp only [encBits_f, encBits_tt, encBits_tf]
  execute 12

/-! ## Pillar 3: Step-Indexed CPS Safety Contracts (`BoxCPS` & `top_safe`) -/

private def BoxCPS (n : ℕ) : Prop :=
  ∀ (xs : List Bool) (c G : ℕ),
    tokLen xs = n →
    InL .q0 xs →
    potBits xs = some (c, G) →
    (c = 0 → ∀ (k : ℕ) (r : ListBlank (Fin 2)),
      (∀ (j : ℕ) (xs₁ : List Bool) (c₁ G₁ : ℕ),
        j < k → tokLen xs₁ = n → InL .q0 xs₁ → potBits xs₁ = some (c₁, G₁) →
        G ≤ c₁ → G ≤ G₁ → Safe j (cfgD xs₁ r)) →
      Safe k (cfgB xs r)) ∧
    (∀ c', c = c' + 1 → ∀ (k : ℕ) (r : ListBlank (Fin 2)),
      (∀ (j : ℕ) (xs₁ : List Bool) (G₁ : ℕ),
        j < k → tokLen xs₁ = n → InL .q0 xs₁ → potBits xs₁ = some (c', G₁) →
        G ≤ G₁ → (is110Head xs = true → is110Head xs₁ = true) → Safe j (cfgA xs₁ r)) →
      Safe k (cfgB xs r))

private theorem box_cps_holds : ∀ n : ℕ, BoxCPS n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs c G hlen hIn hpot
    cases inl_decomp xs hIn with
    | emp =>
      rw [potBits.eq_1] at hpot
      injection hpot with hp; injection hp with hc hG
      subst hc; subst hG
      refine ⟨fun _ k r hcont => ?_, fun _ hc => by omega⟩
      exact Safe_of_stepPlus (box_emp r) fun k' hk' =>
        hcont k' [] 0 0 hk' hlen trivial potBits.eq_1 (Nat.le_refl _) (Nat.le_refl _)
    | w0100 u hu =>
      rw [potBits.eq_3] at hpot
      cases hpu : potBits u with
      | none => rw [hpu] at hpot; cases hpot
      | some p =>
        rw [hpu] at hpot
        rcases p with ⟨cu, Gu⟩
        injection hpot with hp; injection hp with hc hG
        subst hc; subst hG
        have hu_le : cu ≤ Gu := potBits_c_le_G hu hpu
        refine ⟨fun _ k r hcont => ?_, fun _ hc => by omega⟩
        refine Safe_of_stepPlus (box_0100 u r) fun k' hk' => ?_
        have hp_out : potBits (true :: false :: false :: u) = some (cu + 1, Gu + 1) := by
          rw [potBits.eq_2, hpu]
        exact hcont k' (true :: false :: false :: u) (cu + 1) (Gu + 1) hk'
          (by simpa [tokLen] using hlen) hu hp_out (Nat.le_refl _) (by omega)
    | w100 u hu =>
      rw [potBits.eq_2] at hpot
      cases hpu : potBits u with
      | none => rw [hpu] at hpot; cases hpot
      | some p =>
        rw [hpu] at hpot
        rcases p with ⟨cu, Gu⟩
        injection hpot with hp; injection hp with hc hG
        subst hc; subst hG
        have hlen_u : tokLen u < n := by simp [tokLen] at hlen; omega
        have ih_u := ih (tokLen u) hlen_u u cu Gu rfl hu hpu
        refine ⟨fun hc => by omega, fun c' hc' k r hcont => ?_⟩
        refine Safe_of_stepPlus (box_100 u r) fun k₁ hk₁ => ?_
        cases cu with
        | zero =>
          have hc0 : c' = 0 := Nat.succ.inj hc'.symm
          rw [hc0] at hcont
          exact ih_u.1 rfl k₁ ([1, 0, 0] +> r) fun k₂ u₁ c₁ G₁ hk₂ _ hu₁ hpu₁ hGc _ =>
            Safe_of_stepPlus (ret_100_D u₁ r) fun k₃ hk₃ => by
              have hp_out : potBits (false :: true :: false :: false :: u₁) = some (0, c₁ + 1) := by
                rw [potBits.eq_3, hpu₁]
              exact hcont k₃ (false :: true :: false :: false :: u₁) (c₁ + 1)
                (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (by simp [tokLen] at hlen ⊢; omega) hu₁ hp_out (by omega)
                (fun hh => by cases hh)
        | succ c'' =>
          have hcs : c' = c'' + 1 := Nat.succ.inj hc'.symm
          rw [hcs] at hcont
          exact ih_u.2 c'' rfl k₁ ([1, 0, 0] +> r) fun k₂ u₁ G₁ hk₂ _ hu₁ hpu₁ hGG _ =>
            Safe_of_stepPlus (ret_100_A u₁ r) fun k₃ hk₃ => by
              have hp_out : potBits (true :: false :: false :: u₁) = some (c'' + 1, G₁ + 1) := by
                rw [potBits.eq_2, hpu₁]
              exact hcont k₃ (true :: false :: false :: u₁) (G₁ + 1)
                (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (by simp [tokLen] at hlen ⊢; omega) hu₁ hp_out (by omega)
                (fun hh => by cases hh)
    | w110 u hu =>
      cases inl_decomp u hu with
      | emp =>
        rw [potBits.eq_4] at hpot
        injection hpot with hp; injection hp with hc hG
        subst hc; subst hG
        refine ⟨fun _ k r hcont => ?_, fun _ hc => by omega⟩
        have hp0100 : potBits [false, true, false, false] = some (0, 1) := by
          rw [potBits.eq_3, potBits.eq_1]
        exact Safe_of_stepPlus (box_110_emp r) fun k' hk' =>
          hcont k' [false, true, false, false] 0 1 hk'
            (by simpa [tokLen] using hlen) trivial hp0100 (Nat.zero_le _) (Nat.zero_le _)
      | w0100 v hv =>
        rw [potBits.eq_5] at hpot
        cases hpv : potBits v with
        | none => rw [hpv] at hpot; cases hpot
        | some p =>
          rw [hpv] at hpot
          rcases p with ⟨cv, Gv⟩
          injection hpot with hp; injection hp with hc hG
          subst hc; subst hG
          have hlen_v : tokLen v < n := by simp [tokLen] at hlen; omega
          have ih_v := ih (tokLen v) hlen_v v cv Gv rfl hv hpv
          refine ⟨fun _ k r hcont => ?_, fun _ hc => by omega⟩
          refine Safe_of_stepPlus (box_110_0100 v r) fun k₁ hk₁ => ?_
          cases cv with
          | zero =>
            exact ih_v.1 rfl k₁ ([1, 0, 0, 1, 0, 0, 1] +> r)
              fun k₂ v₁ c₁ G₁ hk₂ hlv₁ hv₁ hpv₁ _ _ =>
                Safe_of_stepPlus (ret_110_0100_D v₁ r) fun k₃ hk₃ => by
                  have hp_out :
                      potBits (true :: false :: false :: false :: true :: false :: false :: v₁) =
                        some (1, c₁ + 2) := by
                    rw [potBits.eq_2, potBits.eq_3, hpv₁]
                  exact hcont k₃
                    (true :: false :: false :: false :: true :: false :: false :: v₁)
                    1 (c₁ + 2) (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                    (by simp [tokLen] at hlen ⊢; omega) hv₁ hp_out (by omega) (by omega)
          | succ cv' =>
            have hcv_le : cv' + 1 ≤ Gv := potBits_c_le_G hv hpv
            exact ih_v.2 cv' rfl k₁ ([1, 0, 0, 1, 0, 0, 1] +> r)
              fun k₂ v₁ G₁ hk₂ hlv₁ hv₁ hpv₁ hGG _ =>
                Safe_of_stepPlus (ret_110_0100_A v₁ r) fun k₃ hk₃ => by
                  have hp_out :
                      potBits (true :: false :: false :: true :: false :: false :: v₁) =
                        some (cv' + 2, G₁ + 2) := by
                    rw [potBits.eq_2, potBits.eq_2, hpv₁]
                  exact hcont k₃
                    (true :: false :: false :: true :: false :: false :: v₁)
                    (cv' + 2) (G₁ + 2) (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                    (by simp [tokLen] at hlen ⊢; omega) hv₁ hp_out (by omega) (by omega)
      | w110 z _ =>
        rw [potBits.eq_6] at hpot
        have hlen_eq : tokLen (true :: true :: z) + 1 = n := hlen
        have hlen_u : tokLen (true :: true :: z) < n := by omega
        have ih_u := ih (tokLen (true :: true :: z)) hlen_u (true :: true :: z) c G rfl hu hpot
        refine ⟨fun hc k r hcont => ?_, fun c' hc' k r hcont => ?_⟩
        · subst hc
          refine Safe_of_stepPlus (box_110_110 z r) fun k₁ hk₁ => ?_
          exact ih_u.1 rfl k₁ ([0, 1, 1] +> r) fun k₂ u₁ c₁ G₁ hk₂ hlu₁ hu₁ hpu₁ hGc₁ hGG₁ =>
            Safe_of_stepPlus (ret_110_110_D u₁ r) fun k₃ hk₃ => by
              have hlen_u1 : tokLen u₁ < n := by omega
              have ih_u1 := ih (tokLen u₁) hlen_u1 u₁ c₁ G₁ rfl hu₁ hpu₁
              cases c₁ with
              | zero =>
                have hG0 : G = 0 := by omega
                exact ih_u1.1 rfl k₃ ([1, 0, 0, 1] +> r)
                  fun k₄ u₂ c₂ G₂ hk₄ hlu₂ hu₂ hpu₂ _ _ =>
                    Safe_of_stepPlus (ret_1001_D u₂ r) fun k₅ hk₅ => by
                      have hp_out :
                          potBits (false :: true :: false :: false :: u₂) = some (0, c₂ + 1) := by
                        rw [potBits.eq_3, hpu₂]
                      exact hcont k₅ (false :: true :: false :: false :: u₂) 0 (c₂ + 1)
                        (Nat.lt_trans hk₅
                            (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))))
                        (by change tokLen u₂ + 1 = n; omega) hu₂ hp_out (by omega) (by omega)
              | succ c₁' =>
                exact ih_u1.2 c₁' rfl k₃ ([1, 0, 0, 1] +> r)
                  fun k₄ u₂ G₂ hk₄ hlu₂ hu₂ hpu₂ hGG₂ _ =>
                    Safe_of_stepPlus (ret_1001_A u₂ r) fun k₅ hk₅ => by
                      have hp_out :
                          potBits (true :: false :: false :: u₂) = some (c₁' + 1, G₂ + 1) := by
                        rw [potBits.eq_2, hpu₂]
                      exact hcont k₅ (true :: false :: false :: u₂) (c₁' + 1) (G₂ + 1)
                        (Nat.lt_trans hk₅
                            (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))))
                        (by change tokLen u₂ + 1 = n; omega) hu₂ hp_out (by omega) (by omega)
        · refine Safe_of_stepPlus (box_110_110 z r) fun k₁ hk₁ => ?_
          exact ih_u.2 c' hc' k₁ ([0, 1, 1] +> r) fun k₂ u₁ G₁ hk₂ hlu₁ hu₁ hpu₁ hGG₁ hh₁ =>
            Safe_of_stepPlus (ret_110_110_A u₁ r) fun k₃ hk₃ => by
              have hh_u1 : is110Head u₁ = true := hh₁ rfl
              have hp_out : potBits (true :: true :: u₁) = some (c', G₁) := by
                rw [potBits_110_of_is110Head hu₁ hh_u1, hpu₁]
              exact hcont k₃ (true :: true :: u₁) G₁
                (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (by change tokLen u₁ + 1 = n; omega) hu₁ hp_out hGG₁ (fun _ => rfl)
      | w100 v hv =>
        rw [potBits.eq_7] at hpot
        cases hpv : potBits v with
        | none => rw [hpv] at hpot; cases hpot
        | some p =>
          rw [hpv] at hpot
          dsimp only at hpot
          rcases p with ⟨cv, Gv⟩
          have hcv_le : cv ≤ Gv := potBits_c_le_G hv hpv
          have hlen_v : tokLen v < n := by simp [tokLen] at hlen; omega
          have ih_v := ih (tokLen v) hlen_v v cv Gv rfl hv hpv
          refine ⟨fun hc k r hcont => ?_, fun c' hc' k r hcont => ?_⟩
          · subst hc
            cases cv with
            | zero =>
              unfold step110_100 at hpot
              cases Gv with
              | zero => cases hpot
              | succ Gv' =>
                dsimp only at hpot
                cases hble : Nat.ble (Gv' + 1) 0
                · rw [hble] at hpot
                  injection hpot with hp; injection hp with _ hG
                  subst hG
                  refine Safe_of_stepPlus (box_110_100 v r) fun k₁ hk₁ => ?_
                  exact ih_v.1 rfl k₁ ([1, 0, 1, 0, 0, 1] +> r)
                    fun k₂ v₁ c₁ G₁ hk₂ hlv₁ hv₁ hpv₁ hGc₁ hGG₁ =>
                      Safe_of_stepPlus (ret_101001_D v₁ r) fun k₃ hk₃ => by
                        obtain ⟨c₁', rfl⟩ : ∃ c₁', c₁ = c₁' + 1 := by
                          cases c₁ with
                          | zero => omega
                          | succ m => exact ⟨m, rfl⟩
                        have ih_v1 := ih (tokLen v₁) (by omega) v₁ (c₁' + 1) G₁ rfl hv₁ hpv₁
                        exact ih_v1.2 c₁' rfl k₃ ([1, 0, 0, 0, 0, 0, 1] +> r)
                          fun k₄ v₂ G₂ hk₄ hlv₂ hv₂ hpv₂ hGG₂ _ =>
                            Safe_of_stepPlus (ret_1000001_A v₂ r) fun k₅ hk₅ => by
                              have hc1_le_G2 : c₁' + 1 ≤ G₂ := by
                                have hle1 := potBits_c_le_G hv₁ hpv₁
                                omega
                              have ih_v2 := ih (tokLen v₂) (by omega) v₂ c₁' G₂ rfl hv₂ hpv₂
                              cases c₁' with
                              | zero =>
                                have hGv0 : Gv' = 0 := by omega
                                exact ih_v2.1 rfl k₅ ([1, 0, 0, 0, 1, 0, 1] +> r)
                                  fun k₆ v₃ c₃ G₃ hk₆ hlv₃ hv₃ hpv₃ _ _ =>
                                    Safe_of_stepPlus (ret_1000101_D v₃ r) fun k₇ hk₇ => by
                                      have hp_out :
                                          potBits (true :: true :: false :: true :: false ::
                                              false :: v₃) =
                                            some (0, c₃ + 1) := by
                                        rw [potBits.eq_5, hpv₃]
                                      have hk₇lt : k₇ < k :=
                                        Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅
                                          (Nat.lt_trans hk₄
                                              (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
                                      exact hcont k₇
                                        (true :: true :: false :: true :: false :: false :: v₃)
                                        0 (c₃ + 1) hk₇lt
                                        (by simp [tokLen] at hlen hlv₁ hlv₂ ⊢; omega)
                                        hv₃ hp_out (by omega) (by omega)
                              | succ c₂ =>
                                exact ih_v2.2 c₂ rfl k₅ ([1, 0, 0, 0, 1, 0, 1] +> r)
                                  fun k₆ v₃ G₃ hk₆ hlv₃ hv₃ hpv₃ hGG₃ _ =>
                                    Safe_of_stepPlus (ret_1000101_A v₃ r) fun k₇ hk₇ => by
                                      obtain ⟨c_out, G_out, hs_out, hc_ge, hG_ge⟩ :=
                                        step110_100_c0_preserve (Gv' := Gv') (c2 := c₂) (Gv3 := G₃)
                                          (by omega) (by omega) (by omega)
                                      have hp_out :
                                          potBits (true :: true :: true :: false :: false :: v₃) =
                                            some (c_out, G_out) := by
                                        rw [potBits.eq_7, hpv₃]
                                        exact hs_out
                                      have hk₇lt : k₇ < k :=
                                        Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅
                                          (Nat.lt_trans hk₄
                                              (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
                                      exact hcont k₇
                                        (true :: true :: true :: false :: false :: v₃)
                                        c_out G_out hk₇lt
                                        (by simp [tokLen] at hlen hlv₁ hlv₂ ⊢; omega)
                                        hv₃ hp_out (by simpa using hc_ge) (by simpa using hG_ge)
                · rw [hble] at hpot; cases hpot
            | succ cv0 =>
              cases cv0 with
              | zero =>
                unfold step110_100 at hpot
                cases Gv with
                | zero => cases hpot
                | succ Gv' =>
                  dsimp only at hpot
                  injection hpot with hp; injection hp with _ hG
                  subst hG
                  refine Safe_of_stepPlus (box_110_100 v r) fun k₁ hk₁ => ?_
                  exact ih_v.2 0 rfl k₁ ([1, 0, 1, 0, 0, 1] +> r)
                    fun k₂ v₁ G₁ hk₂ hlv₁ hv₁ hpv₁ hGG₁ _ =>
                      Safe_of_stepPlus (ret_101001_A v₁ r) fun k₃ hk₃ => by
                        have ih_v1 := ih (tokLen v₁) (by omega) v₁ 0 G₁ rfl hv₁ hpv₁
                        exact ih_v1.1 rfl k₃ ([1, 0, 0, 0, 0, 1] +> r)
                          fun k₄ v₂ c₂ G₂ hk₄ hlv₂ hv₂ hpv₂ hGc₂ hGG₂ =>
                            Safe_of_stepPlus (ret_100001_D v₂ r) fun k₅ hk₅ => by
                              obtain ⟨c₂', rfl⟩ : ∃ c₂', c₂ = c₂' + 1 := by
                                cases c₂ with
                                | zero => omega
                                | succ m => exact ⟨m, rfl⟩
                              have ih_v2 := ih (tokLen v₂) (by omega) v₂ (c₂' + 1) G₂ rfl hv₂ hpv₂
                              exact ih_v2.2 c₂' rfl k₅ ([1, 0, 0, 1, 0, 0, 1] +> r)
                                fun k₆ v₃ G₃ hk₆ hlv₃ hv₃ hpv₃ hGG₃ _ =>
                                  Safe_of_stepPlus (ret_110_0100_A v₃ r) fun k₇ hk₇ => by
                                    have hp_out :
                                        potBits (true :: false :: false :: true :: false :: false ::
                                            v₃) =
                                          some (c₂' + 2, G₃ + 2) := by
                                      rw [potBits.eq_2, potBits.eq_2, hpv₃]
                                    have hk₇lt : k₇ < k :=
                                      Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅
                                        (Nat.lt_trans hk₄
                                            (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
                                    exact hcont k₇
                                      (true :: false :: false :: true :: false :: false :: v₃)
                                      (c₂' + 2) (G₃ + 2) hk₇lt
                                      (by simp [tokLen] at hlen hlv₁ hlv₂ ⊢; omega)
                                      hv₃ hp_out (by omega) (by omega)
              | succ cv1 =>
                exfalso
                unfold step110_100 at hpot
                cases Gv with
                | zero => cases hpot
                | succ Gv' =>
                  have hmod :
                      (cv1 + 1 + 1) % 3 = 0 ∨ (cv1 + 1 + 1) % 3 = 1 ∨ (cv1 + 1 + 1) % 3 = 2 := by
                      omega
                  rcases hmod with h0 | h1 | h2
                  · rw [h0] at hpot; dsimp only at hpot
                    cases hble : Nat.ble (Gv' + 1) (cv1 + 1 + 1) <;> rw [hble] at hpot
                    · injection hpot with hp; injection hp with hc0 _; omega
                    · cases hpot
                  · rw [h1] at hpot; dsimp only at hpot
                    injection hpot with hp; injection hp with hc0 _; omega
                  · rw [h2] at hpot; dsimp only at hpot
                    injection hpot with hp; injection hp with hc0 _; omega
          · subst hc'
            cases cv with
            | zero =>
              unfold step110_100 at hpot
              cases Gv with
              | zero => cases hpot
              | succ Gv' =>
                dsimp only at hpot
                cases hble : Nat.ble (Gv' + 1) 0 <;> rw [hble] at hpot
                · injection hpot with hp; injection hp with hc0 _; omega
                · cases hpot
            | succ cv0 =>
              cases cv0 with
              | zero =>
                unfold step110_100 at hpot
                cases Gv with
                | zero => cases hpot
                | succ Gv' =>
                  dsimp only at hpot
                  injection hpot with hp; injection hp with hc0 _; omega
              | succ cv1 =>
                cases cv1 with
                | zero =>
                  unfold step110_100 at hpot
                  cases Gv with
                  | zero => cases hpot
                  | succ Gv' =>
                    dsimp only at hpot
                    injection hpot with hp; injection hp with hc' hG
                    have hc'_zero : c' = 0 := by omega
                    subst hc'_zero; subst hG
                    refine Safe_of_stepPlus (box_110_100 v r) fun k₁ hk₁ => ?_
                    exact ih_v.2 1 rfl k₁ ([1, 0, 1, 0, 0, 1] +> r)
                      fun k₂ v₁ G₁ hk₂ hlv₁ hv₁ hpv₁ hGG₁ _ =>
                        Safe_of_stepPlus (ret_101001_A v₁ r) fun k₃ hk₃ => by
                          have ih_v1 := ih (tokLen v₁) (by omega) v₁ 1 G₁ rfl hv₁ hpv₁
                          exact ih_v1.2 0 rfl k₃ ([1, 0, 0, 0, 0, 1] +> r)
                            fun k₄ v₂ G₂ hk₄ hlv₂ hv₂ hpv₂ hGG₂ _ =>
                              Safe_of_stepPlus (ret_100001_A v₂ r) fun k₅ hk₅ => by
                                have ih_v2 := ih (tokLen v₂) (by omega) v₂ 0 G₂ rfl hv₂ hpv₂
                                exact ih_v2.1 rfl k₅ ([1, 0, 0, 0, 1, 1] +> r)
                                  fun k₆ v₃ c₃ G₃ hk₆ hlv₃ hv₃ hpv₃ hGc₃ _ =>
                                    Safe_of_stepPlus (ret_100011_D v₃ r) fun k₇ hk₇ => by
                                      have hp_out :
                                          potBits (true :: true :: false :: true :: false ::
                                              false :: v₃) =
                                            some (0, c₃ + 1) := by
                                        rw [potBits.eq_5, hpv₃]
                                      have hk₇lt : k₇ < k :=
                                        Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅
                                          (Nat.lt_trans hk₄
                                              (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
                                      exact hcont k₇
                                        (true :: true :: false :: true :: false :: false :: v₃)
                                        (c₃ + 1) hk₇lt
                                        (by simp [tokLen] at hlen hlv₁ hlv₂ ⊢; omega)
                                        hv₃ hp_out (by omega) (fun _ => rfl)
                | succ cv3 =>
                  refine Safe_of_stepPlus (box_110_100 v r) fun k₁ hk₁ => ?_
                  exact ih_v.2 (cv3 + 2) rfl k₁ ([1, 0, 1, 0, 0, 1] +> r)
                    fun k₂ v₁ G₁ hk₂ hlv₁ hv₁ hpv₁ hGG₁ _ =>
                      Safe_of_stepPlus (ret_101001_A v₁ r) fun k₃ hk₃ => by
                        have ih_v1 := ih (tokLen v₁) (by omega) v₁ (cv3 + 2) G₁ rfl hv₁ hpv₁
                        exact ih_v1.2 (cv3 + 1) rfl k₃ ([1, 0, 0, 0, 0, 1] +> r)
                          fun k₄ v₂ G₂ hk₄ hlv₂ hv₂ hpv₂ hGG₂ _ =>
                            Safe_of_stepPlus (ret_100001_A v₂ r) fun k₅ hk₅ => by
                              have ih_v2 := ih (tokLen v₂) (by omega) v₂ (cv3 + 1) G₂ rfl hv₂ hpv₂
                              exact ih_v2.2 cv3 rfl k₅ ([1, 0, 0, 0, 1, 1] +> r)
                                fun k₆ v₃ G₃ hk₆ hlv₃ hv₃ hpv₃ hGG₃ _ =>
                                  Safe_of_stepPlus (ret_100011_A v₃ r) fun k₇ hk₇ => by
                                    obtain ⟨G_out, hs_out, hG_ge⟩ :=
                                      step110_100_succ3 hpot (by omega : Gv ≤ G₃)
                                    have hp_out :
                                        potBits (true :: true :: true :: false :: false :: v₃) =
                                          some (c', G_out) := by
                                      rw [potBits.eq_7, hpv₃]
                                      exact hs_out
                                    have hk₇lt : k₇ < k :=
                                      Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅
                                        (Nat.lt_trans hk₄
                                            (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
                                    exact hcont k₇
                                      (true :: true :: true :: false :: false :: v₃)
                                      G_out hk₇lt
                                      (by simp [tokLen] at hlen hlv₁ hlv₂ ⊢; omega)
                                      hv₃ hp_out hG_ge (fun _ => rfl)

private theorem push110_potBits {xs₁ : List Bool} {c' G₁ : ℕ}
    (hIn : InL .q0 xs₁) (hpot : potBits xs₁ = some (c', G₁)) (hG : c' + 1 ≤ G₁) :
    ∃ c₂ G₂, potBits (true :: true :: xs₁) = some (c₂, G₂) := by
  cases inl_decomp xs₁ hIn with
  | emp => exact ⟨0, 0, potBits.eq_4⟩
  | w0100 v _ =>
    rw [potBits.eq_3] at hpot
    cases hpv : potBits v with
    | none => rw [hpv] at hpot; cases hpot
    | some p =>
      rcases p with ⟨cv, Gv⟩
      refine ⟨0, cv + 1, ?_⟩
      rw [potBits.eq_5, hpv]
  | w110 z _ =>
    refine ⟨c', G₁, ?_⟩
    rw [potBits.eq_6, hpot]
  | w100 v hv =>
    rw [potBits.eq_2] at hpot
    cases hpv : potBits v with
    | none => rw [hpv] at hpot; cases hpot
    | some p =>
      rw [hpv] at hpot
      rcases p with ⟨cv, Gv⟩
      injection hpot with hp; injection hp with hc hG₁
      have hlt : cv < Gv := by omega
      obtain ⟨c₂, G₂, hs, _, _⟩ :=
        step110_100_c0_preserve (Gv' := 0) (c2 := cv) (Gv3 := Gv)
          (Nat.zero_le _) (by omega) hlt
      refine ⟨c₂, G₂, ?_⟩
      rw [potBits.eq_7, hpv]
      exact hs

private theorem top_safe : ∀ (k : ℕ) (xs : List Bool) (c G : ℕ),
    InL .q0 xs → potBits xs = some (c, G) → Safe k (cfgTop xs) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro xs c G hIn hpot
    have hcG : c ≤ G := potBits_c_le_G hIn hpot
    have hbox := box_cps_holds (tokLen xs) xs c G rfl hIn hpot
    refine Safe_of_stepPlus (top_enter xs) fun k₁ hk₁ => ?_
    cases c with
    | zero =>
      exact hbox.1 rfl k₁ ([0, 1] +> default) fun k₂ xs₁ c₁ G₁ hk₂ _ hIn₁ hpot₁ _ _ =>
        Safe_of_stepPlus (top_ret_D xs₁) fun k₃ hk₃ => by
          have hbox₁ := box_cps_holds (tokLen xs₁) xs₁ c₁ G₁ rfl hIn₁ hpot₁
          cases c₁ with
          | zero =>
            exact hbox₁.1 rfl k₃ ([1] +> default) fun k₄ xs₂ c₂ G₂ hk₄ _ hIn₂ hpot₂ _ _ =>
              Safe_of_stepPlus (top_ret_DD xs₂) fun k₅ hk₅ => by
                have hp_out :
                    potBits (false :: true :: false :: false :: xs₂) = some (0, c₂ + 1) := by
                  rw [potBits.eq_3, hpot₂]
                have hk₅lt : k₅ < k :=
                  Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                exact ih k₅ hk₅lt (false :: true :: false :: false :: xs₂) 0 (c₂ + 1) hIn₂ hp_out
          | succ c₁' =>
            exact hbox₁.2 c₁' rfl k₃ ([1] +> default) fun k₄ xs₂ G₂ hk₄ _ hIn₂ hpot₂ _ _ =>
              Safe_of_stepPlus (top_ret_DA xs₂) fun k₅ hk₅ => by
                have hp_out :
                    potBits (true :: false :: false :: xs₂) = some (c₁' + 1, G₂ + 1) := by
                  rw [potBits.eq_2, hpot₂]
                have hk₅lt : k₅ < k :=
                  Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                exact ih k₅ hk₅lt (true :: false :: false :: xs₂) (c₁' + 1) (G₂ + 1) hIn₂ hp_out
    | succ c' =>
      exact hbox.2 c' rfl k₁ ([0, 1] +> default) fun k₂ xs₁ G₁ hk₂ _ hIn₁ hpot₁ hGG₁ _ =>
        Safe_of_stepPlus (top_ret_A xs₁) fun k₃ hk₃ => by
          obtain ⟨c₂, G₂, hp_out⟩ := push110_potBits hIn₁ hpot₁ (by omega)
          have hk₃lt : k₃ < k := Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)
          exact ih k₃ hk₃lt (true :: true :: xs₁) c₂ G₂ hIn₁ hp_out


private theorem is_does_not_halt : IsNotHalt target_tm :=
  isNotHalt_of_forall_safe (cfgTop []) init_to_top
    (fun k => top_safe k [] 0 0 trivial potBits.eq_1)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RC---` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RD_1LC0LE_0RA0LB_1RC1RF_1LB1RD_0RCHHH
