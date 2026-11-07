/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge

open Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
local infixr:67 " ::ᵇ " => Turing.ListBlank.cons

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

@[simp] theorem list_append_inj (xs l1 l2 : List Nat) : (xs ++ l1 = xs ++ l2) ↔ l1 = l2 :=
  List.append_right_inj xs

structure Sim where
  q : Fin 6
  dir : Dir
  l : zF
  r : zF

def Sim.toCfg (x : Sim) (l₀ r₀ : zB) : Cfg (Fin 2) (Fin 6) :=
  match x.dir with
  | .left => (x.l +> l₀) <{{x.q}} (x.r +> r₀)
  | .right => (x.l +> l₀) {{x.q}}> (x.r +> r₀)

def simStep (x : Sim) : Option Sim :=
  match x.dir with
  | .left =>
    match x.l with
    | [] => none
    | a :: l' =>
      match target_tm x.q a with
      | some (some q', Stmt.write w .left) => some ⟨q', .left, l', w :: x.r⟩
      | some (some q', Stmt.write w .right) => some ⟨q', .right, w :: l', x.r⟩
      | _ => none
  | .right =>
    match x.r with
    | [] => none
    | a :: r' =>
      match target_tm x.q a with
      | some (some q', Stmt.write w .left) => some ⟨q', .left, x.l, w :: r'⟩
      | some (some q', Stmt.write w .right) => some ⟨q', .right, w :: x.l, r'⟩
      | _ => none

theorem simStep_sound (x x' : Sim) (h : simStep x = some x') (l₀ r₀ : zB) :
    (x.toCfg l₀ r₀) [target_tm]⊢ (x'.toCfg l₀ r₀) := by
  rcases x with ⟨q, _ | _, l, r⟩
  · rcases l with _ | ⟨a, l'⟩
    · cases h
    · dsimp [simStep] at h
      rcases hM : target_tm q a with _ | ⟨_ | q', ⟨w, _ | _⟩⟩ <;> rw [hM] at h <;> cases h <;>
        simp [Sim.toCfg, step, hM, Tape.write, Tape.move]
  · rcases r with _ | ⟨a, r'⟩
    · cases h
    · dsimp [simStep] at h
      rcases hM : target_tm q a with _ | ⟨_ | q', ⟨w, _ | _⟩⟩ <;> rw [hM] at h <;> cases h <;>
        simp [Sim.toCfg, step, hM, Tape.write, Tape.move]

def simSteps : Nat → Sim → Option Sim
  | 0, x => some x
  | n + 1, x => (simStep x).bind (simSteps n)

theorem simSteps_sound : ∀ (n : Nat) (x x' : Sim),
    simSteps n x = some x' → ∀ (l₀ r₀ : zB), (x.toCfg l₀ r₀) [target_tm]⊢^{n} (x'.toCfg l₀ r₀)
  | 0, x, x', h, l₀, r₀ => by cases h; rfl
  | n + 1, x, x', h, l₀, r₀ => by
    dsimp [simSteps] at h
    rcases hs : simStep x with _ | y <;> rw [hs] at h
    · cases h
    · have h1 : (x.toCfg l₀ r₀) [target_tm]⊢^{1} (y.toCfg l₀ r₀) := simStep_sound x y hs l₀ r₀
      have h2 := simSteps_sound n y x' h l₀ r₀
      rw [Nat.add_comm n 1]
      exact multiStep_trans h1 h2

theorem simSteps_star {n : Nat} {x x' : Sim} (h : simSteps n x = some x') (l₀ r₀ : zB) :
    (x.toCfg l₀ r₀) [target_tm]⊢* (x'.toCfg l₀ r₀) :=
  ⟨n, simSteps_sound n x x' h l₀ r₀⟩

theorem simSteps_star_ex (n : Nat) (x x' : Sim) (h : simSteps n x = some x') (l₀ r₀ : zB) :
    (x.toCfg l₀ r₀) [target_tm]⊢* (x'.toCfg l₀ r₀) :=
  ⟨n, simSteps_sound n x x' h l₀ r₀⟩

theorem pow_comm_append (w : zF) (n : Nat) (s : zB) :
    (w ^ n) +> (w +> s) = (w ^ (n + 1)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_succ' w n]

theorem shiftL_gen {k : Nat} {q : Fin 6} {x x' d : zF}
    (h : simSteps k ⟨q, .left, x, d⟩ = some ⟨q, .left, [], d ++ x'⟩)
    (n : Nat) (l₀ r₀ : zB) :
    (((x ^ n) +> l₀) <{{q}} (d +> r₀)) [target_tm]⊢* (l₀ <{{q}} (d +> ((x' ^ n) +> r₀))) := by
  induction n generalizing r₀ with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [list_pow_succ, listblank_append_right_assoc]
    have h1 := simSteps_star h ((x ^ n) +> l₀) r₀
    dsimp only [Sim.toCfg] at h1
    rw [listblank_append_nil, listblank_append_right_assoc] at h1
    have h2 := ih (x' +> r₀)
    rw [pow_comm_append] at h2
    exact ReachesStar.trans h1 h2

theorem shiftR_gen {k : Nat} {q : Fin 6} {x x' d : zF}
    (h : simSteps k ⟨q, .right, d, x⟩ = some ⟨q, .right, d ++ x', []⟩)
    (n : Nat) (l₀ r₀ : zB) :
    ((d +> l₀) {{q}}> ((x ^ n) +> r₀)) [target_tm]⊢* ((d +> ((x' ^ n) +> l₀)) {{q}}> r₀) := by
  induction n generalizing l₀ with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    rw [list_pow_succ, listblank_append_right_assoc]
    have h1 := simSteps_star h l₀ ((x ^ n) +> r₀)
    dsimp only [Sim.toCfg] at h1
    rw [listblank_append_nil, listblank_append_right_assoc] at h1
    have h2 := ih (x' +> l₀)
    rw [pow_comm_append] at h2
    exact ReachesStar.trans h1 h2

theorem pow_add_1 (w : zF) (n : Nat) : w ^ (1 + n) = w ++ w ^ n := by
  rw [Nat.add_comm 1 n]; rfl
theorem pow_add_2 (w : zF) (n : Nat) : w ^ (2 + n) = w ++ (w ++ w ^ n) := by
  rw [Nat.add_comm 2 n]; rfl
theorem pow_add_3 (w : zF) (n : Nat) : w ^ (3 + n) = w ++ (w ++ (w ++ w ^ n)) := by
  rw [Nat.add_comm 3 n]; rfl
theorem pow_add_4 (w : zF) (n : Nat) : w ^ (4 + n) = w ++ (w ++ (w ++ (w ++ w ^ n))) := by
  rw [Nat.add_comm 4 n]; rfl
theorem pow_add_5 (w : zF) (n : Nat) : w ^ (5 + n) = w ++ (w ++ (w ++ (w ++ (w ++ w ^ n)))) := by
  rw [Nat.add_comm 5 n]; rfl

theorem pow_double3 (a b c : Fin 2) (n : Nat) :
    ([a, b, c, a, b, c] : zF) ^ n = ([a, b, c] : zF) ^ (n * 2) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (n + 1) * 2 = n * 2 + 1 + 1 := by omega
    rw [list_pow_succ, ih, h, list_pow_succ, list_pow_succ]
    rfl

theorem lpow_shift (a : Fin 2) (x : zF) (n : Nat) (s : zB) :
    (((a :: x) ^ n) +> (a ::ᵇ s)) = a ::ᵇ (((x ++ [a]) ^ n) +> s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [list_pow_succ, List.cons_append, listblank_append_cons, listblank_append_right_assoc, ih]
    rw [list_pow_succ]
    simp only [listblank_append_right_assoc, listblank_append_cons, listblank_append_nil]

theorem shift2 (a b : Fin 2) (n : Nat) (s : zB) :
    (([a, b] : zF) ^ n) +> (a ::ᵇ s) = a ::ᵇ ((([b, a] : zF) ^ n) +> s) :=
  lpow_shift a [b] n s

theorem shift3 (a b c : Fin 2) (n : Nat) (s : zB) :
    (([a, b, c] : zF) ^ n) +> (a ::ᵇ s) = a ::ᵇ ((([b, c, a] : zF) ^ n) +> s) :=
  lpow_shift a [b, c] n s

theorem shift6 (a b c d e f : Fin 2) (n : Nat) (s : zB) :
    (([a, b, c, d, e, f] : zF) ^ n) +> (a ::ᵇ s) = a ::ᵇ ((([b, c, d, e, f, a] : zF) ^ n) +> s) :=
  lpow_shift a [b, c, d, e, f] n s

theorem shift2_0 (n : Nat) :
    (([0, 1] : zF) ^ n) +> default = (0 : Fin 2) ::ᵇ ((([1, 0] : zF) ^ n) +> default) := by
  conv_lhs => rw [← ListBlank.cons_zero_default]
  exact shift2 0 1 n default

theorem shift3_0_1 (c : Fin 2) (n : Nat) :
    (([0, 1, c] : zF) ^ n) +> default = (0 : Fin 2) ::ᵇ ((([1, c, 0] : zF) ^ n) +> default) := by
  conv_lhs => rw [← ListBlank.cons_zero_default]
  exact shift3 0 1 c n default

theorem shift3_0_01 (n : Nat) :
    (([0, 0, 1] : zF) ^ n) +> default = (0 : Fin 2) ::ᵇ (0 : Fin 2) ::ᵇ ((([1, 0, 0] : zF) ^ n)
        +> default) := by
  conv_lhs => rw [← ListBlank.cons_zero_default]
  rw [shift3 0 0 1 n default]
  congr 1
  exact shift3_0_1 0 n

theorem shift6_0_1 (c d e f : Fin 2) (n : Nat) :
    (([0, 1, c, d, e, f] : zF) ^ n) +> default = (0 : Fin 2) ::ᵇ ((([1, c, d, e, f, 0] : zF) ^ n)
        +> default) := by
  conv_lhs => rw [← ListBlank.cons_zero_default]
  exact shift6 0 1 c d e f n default

theorem shift6_0_01 (d e f : Fin 2) (n : Nat) :
    (([0, 0, 1, d, e, f] : zF) ^ n) +> default =
    (0 : Fin 2) ::ᵇ (0 : Fin 2) ::ᵇ ((([1, d, e, f, 0, 0] : zF) ^ n) +> default) := by
  conv_lhs => rw [← ListBlank.cons_zero_default]
  rw [shift6 0 0 1 d e f n default]
  congr 1
  exact shift6_0_1 d e f 0 n

theorem pow_merge (w : zF) (m n : Nat) (s : zB) :
    (w ^ m) +> ((w ^ n) +> s) = (w ^ (m + n)) +> s := by
  rw [← listblank_append_right_assoc, ← list_pow_add]

theorem step_bridge {c₁ c₁' c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h : c₁' [target_tm]⊢* c₂) (heq : c₁ = c₁') (hrest : c₂ [target_tm]⊢* c₃) :
    c₁ [target_tm]⊢* c₃ := by
  rw [heq]; exact ReachesStar.trans h hrest

theorem step_end {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁' [target_tm]⊢* c₂') (heq₁ : c₁ = c₁') (heq₂ : c₂' = c₂) :
    c₁ [target_tm]⊢* c₂ := by
  rw [heq₁, ← heq₂]; exact h

-- 16 Shift Rules
theorem sr_0 (n : Nat) (l₀ r₀ : zB) :
    ((([] : zF) +> l₀) {{A}}> ((([0, 0, 1, 1, 0, 1] : zF) ^ n) +> r₀)) [target_tm]⊢*
    ((([] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF) ^ n) +> l₀)) {{A}}> r₀) :=
  shiftR_gen (k := 6) rfl n l₀ r₀

theorem sr_1 (n : Nat) (l₀ r₀ : zB) :
    ((([] : zF) +> l₀) {{A}}> ((([0, 1] : zF) ^ n) +> r₀)) [target_tm]⊢*
    ((([] : zF) +> ((([0, 1] : zF) ^ n) +> l₀)) {{A}}> r₀) :=
  shiftR_gen (k := 2) rfl n l₀ r₀

theorem sr_2 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 0] : zF) ^ n) +> l₀) <{{A}} (([] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{A}} (([] : zF) +> ((([1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 4) rfl n l₀ r₀

theorem sr_3 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 1, 0, 1, 1, 0] : zF) ^ n) +> l₀) <{{A}} (([] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{A}} (([] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_4 (n : Nat) (l₀ r₀ : zB) :
    ((((([0, 1, 1, 0, 1, 1] : zF) ^ n) +> l₀) <{{E}} (([] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{E}} (([] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_5 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 1, 0] : zF) ^ n) +> l₀) <{{C}} (([0, 1] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 17) rfl n l₀ r₀

theorem sr_6 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 1, 0, 1, 1, 0] : zF) ^ n) +> l₀) <{{C}} (([0, 1] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{C}} (([0, 1] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 34) rfl n l₀ r₀

theorem sr_7 (n : Nat) (l₀ r₀ : zB) :
    ((((([0, 1, 1, 0, 1, 1] : zF) ^ n) +> l₀) <{{A}} (([1, 0, 1, 1] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{A}} (([1, 0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 34) rfl n l₀ r₀

theorem sr_8 (n : Nat) (l₀ r₀ : zB) :
    ((([] : zF) +> l₀) {{B}}> ((([1, 0, 0, 1, 1, 0] : zF) ^ n) +> r₀)) [target_tm]⊢*
    ((([] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ n) +> l₀)) {{B}}> r₀) :=
  shiftR_gen (k := 6) rfl n l₀ r₀

theorem sr_9 (n : Nat) (l₀ r₀ : zB) :
    ((([] : zF) +> l₀) {{B}}> ((([1, 0] : zF) ^ n) +> r₀)) [target_tm]⊢*
    ((([] : zF) +> ((([1, 0] : zF) ^ n) +> l₀)) {{B}}> r₀) :=
  shiftR_gen (k := 2) rfl n l₀ r₀

theorem sr_10 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 1, 0, 1, 1, 0] : zF) ^ n) +> l₀) <{{B}} (([1] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_11 (n : Nat) (l₀ r₀ : zB) :
    ((((([0, 1, 1, 0, 1, 1] : zF) ^ n) +> l₀) <{{C}} (([0] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{C}} (([0] : zF) +> ((([1, 0, 0, 1, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_12 (n : Nat) (l₀ r₀ : zB) :
    ((((([0, 1] : zF) ^ n) +> l₀) <{{C}} (([0] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{C}} (([0] : zF) +> ((([1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 4) rfl n l₀ r₀

theorem sr_13 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 0, 1, 1, 0, 1] : zF) ^ n) +> l₀) <{{A}} (([] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{A}} (([] : zF) +> ((([1, 0, 0, 1, 1, 0] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_14 (n : Nat) (l₀ r₀ : zB) :
    ((((([1, 0, 1, 1, 0, 1] : zF) ^ n) +> l₀) <{{C}} (([0] : zF) +> r₀))) [target_tm]⊢*
    (l₀ <{{C}} (([0] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ n) +> r₀))) :=
  shiftL_gen (k := 14) rfl n l₀ r₀

theorem sr_15 (n : Nat) (l₀ r₀ : zB) :
    ((([] : zF) +> l₀) {{C}}> ((([1, 1, 0, 1, 0, 0] : zF) ^ n) +> r₀)) [target_tm]⊢*
    ((([] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ n) +> l₀)) {{C}}> r₀) :=
  shiftR_gen (k := 6) rfl n l₀ r₀


theorem pow_add_right_2 (w : zF) (n : Nat) : w ^ (n + 2) = w ++ (w ++ w ^ n) := rfl
theorem pow_add_right_3 (w : zF) (n : Nat) : w ^ (n + 3) = w ++ (w ++ (w ++ w ^ n)) := rfl
theorem pow_add_right_4 (w : zF) (n : Nat) : w ^ (n + 4) = w ++ (w ++ (w ++ (w ++ w ^ n))) := rfl
theorem pow_add_right_5 (w : zF) (n : Nat) : w ^ (n + 5)
    = w ++ (w ++ (w ++ (w ++ (w ++ w ^ n)))) := rfl

theorem simSteps_plus (n : Nat) (hn : n > 0) (x x' : Sim) (h : simSteps n x = some x')
    (l₀ r₀ : zB) :
    (x.toCfg l₀ r₀) [target_tm]⊢⁺ (x'.toCfg l₀ r₀) :=
  ⟨n, hn, simSteps_sound n x x' h l₀ r₀⟩

theorem step_end_plus {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁' [target_tm]⊢⁺ c₂') (heq₁ : c₁ = c₁') (heq₂ : c₂' = c₂) :
    c₁ [target_tm]⊢⁺ c₂ := by
  rw [heq₁, ← heq₂]; exact h

abbrev w10 : zF := [1, 0]
abbrev w110 : zF := [1, 1, 0]

def section_side : List Nat → Bool → zB
  | [], _ => default
  | a :: xs, true => (w10 ^ a) +> section_side xs false
  | a :: xs, false => (w110 ^ a) +> section_side xs true

def section_481 (xs : List Nat) : Cfg (Fin 2) (Fin 6) :=
  (section_side xs true) {{B}}> default

def S (l r : zB) (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ a) +> l) <{{B}}
    (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ b) +> ((([1, 0] : zF) ^ c) +> (([0] : zF)
        +> ((([1, 0, 0] : zF) ^ d) +> r)))))

def P (a : Nat) : Prop :=
  ∀ l : zB, (((([1, 0] : zF) ^ a) +> l) {{B}}> default) [target_tm]⊢*
    (l <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ a) +> default)))

def PP (a : Nat) : Prop :=
  ∀ l : zB, (((([1, 0] : zF) ^ a) +> l) {{B}}> default) [target_tm]⊢*
    (l <{{E}} (([0, 1, 1] : zF) +> ((([0, 1, 0] : zF) ^ a) +> default)))

def rootW (r : zB) (a : Nat) (w : zF) (c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : zF) ^ (1 + a)) +> (w +> ((([1, 0] : zF) ^ c) +> (([1, 0, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r)))))

def crossW (l r : zB) (a : Nat) (w : zF) (c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ a) +> l) <{{B}} (([1, 0, 1] : zF) +> (w +> ((([1, 0] : zF) ^ c)
      +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r)))))

def crossZ (l r : zB) (a b c e : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ a) +> l) <{{B}} (([1, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b)
      +> ((([1, 0] : zF) ^ c) +> (([0] : zF) +> ((([1, 0] : zF) ^ e) +> r)))))

def rootZ (r : zB) (a b c e : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : zF) ^ (1 + a)) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b) +> ((([1, 0] : zF)
      ^ c) +> (([0] : zF) +> ((([1, 0] : zF) ^ e) +> r)))))

def crossV (l r : zB) (a b c e : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ a) +> l) <{{B}} (([1, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b)
      +> ((([1, 0] : zF) ^ c) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ e)
          +> r)))))

def rootV (r : zB) (a b c e : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : zF) ^ (1 + a)) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b) +> ((([1, 0] : zF)
      ^ c) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ e) +> r)))))

def seed (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : zF) ^ (2 + a)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (1 + b))
      +> ((([1, 0] : zF) ^ (c * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default)))))

def final_scan (t m : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ t) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ m) +> default))

def scan_root (a d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} (([1] : zF) +> ((([0, 1] : zF) ^ a) +> ((([0, 1, 0] : zF) ^ d) +> default)))

def rootT (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} ((([1, 0] : zF) ^ (1 + a)) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b))
      +> ((([1, 0] : zF) ^ c) +> (([1, 0, 1] : zF) +> ((([0, 0, 1] : zF) ^ d) +> default)))))

def scan_left (r : zB) (a d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{A}} (([1] : zF) +> ((([0, 1] : zF) ^ a) +> ((([0, 1, 0] : zF) ^ d) +> r)))

def scanW (l r : zB) (w : zF) (c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  l <{{C}} (([0, 1, 0, 1, 0, 0, 1] : zF) +> (w +> ((([1, 0] : zF) ^ c) +> (([1, 0, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r)))))

macro "norm_cfg" : tactic =>
  `(tactic| (
    try dsimp only [Sim.toCfg,
      S, rootW, crossW, crossZ, rootZ, crossV, rootV, seed, final_scan, scan_root,
      rootT, scan_left, scanW, section_481, section_side, w10, w110]
    try simp only
        [Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
            Nat.mul_one,
      list_pow_zero, list_pow_succ,
      pow_add_1, pow_add_2, pow_add_3, pow_add_4, pow_add_5,
      pow_add_right_2, pow_add_right_3, pow_add_right_4, pow_add_right_5,
      pow_double3,
      List.nil_append, List.cons_append, List.append_assoc,
      listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
      shift2, shift3, shift6,
      shift2_0, shift3_0_1, shift3_0_01, shift6_0_1, shift6_0_01,
      pow_merge, ListBlank.cons_zero_default]
    try ac_rfl))


theorem edge1 (l : zB) (r : zB) (b : Nat) (c : Nat) :
    (((([1, 0] : zF) +> l) <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
        +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> r))))))
            [target_tm]⊢* ((l <{{C}} (([0, 1, 0, 1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (b))
                +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> r)))))) := by
  refine step_bridge (simSteps_star_ex 7 ⟨B, .left, [1, 0], [1]⟩ ⟨A, .right, [0, 1],
      [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
          +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1] : zF) +> l) (([0] : zF) +> ((([1, 0] : zF) ^ (c))
      +> (([0, 1, 0] : zF) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l))
      (([0, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l)) r)
          (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l))
      (([1, 0, 1, 0, 1] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> l) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
      +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .left, [1], [1, 0, 1, 0]⟩ ⟨C, .left, [],
      [0, 1, 0, 1, 0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem edge2 (l : zB) (r : zB) (b : Nat) (c : Nat) :
    (((([1, 0, 1, 0] : zF) +> l) <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
        +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0] : zF) +> r))))))
            [target_tm]⊢* ((l <{{B}} (([1, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF)
                ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> r)))))) := by
  refine step_bridge (simSteps_star_ex 7 ⟨B, .left, [1, 0, 1, 0], [1]⟩ ⟨A, .right, [0, 1, 1, 0],
      [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0] : zF) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0] : zF) +> l) (([0] : zF) +> ((([1, 0] : zF) ^ (c))
      +> (([0, 1, 0, 0] : zF) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))
      (([0, 0, 1, 0, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))) r) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))
      (([1, 0, 1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [1, 1, 0], [1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l) ((([1, 0] : zF) ^ (c))
          +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> l) (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (c)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0], [0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem Inc1 (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) (d : Nat) :
    (S (l) (r) (2+a) (b) (c) (2+d)) [target_tm]⊢* (S (l) (r) (a) (1+b) (2+c) (d)) := by
  refine step_bridge (simSteps_star_ex 7 ⟨B, .left, [1, 0, 1, 0], [1]⟩ ⟨A, .right, [0, 1, 1, 0],
      [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)) (([0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
      +> ((([1, 0] : zF) ^ (a)) +> l))) (([0, 0, 1, 0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF)
          ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0, 1, 0, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))))
              ((([1, 0, 0] : zF) ^ (d)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
      +> ((([1, 0] : zF) ^ (a)) +> l))) (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF)
          ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [1, 1, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left,
      [0], [0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF)
          ^ (a)) +> l)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r))))
              (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0], [0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0, 0] : zF)
              ^ (d)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem pass_011 (l : zB) (r : zB) (n : Nat) :
    ((((([1, 1, 0] : zF) ^ (n)) +> l) <{{C}} (([0, 1] : zF) +> r)))
        [target_tm]⊢* ((l <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> r)))) := by
  exact step_end (sr_5 (n) l r) (by norm_cfg) (by norm_cfg)

theorem P3 :
    P 3 := by
  intro l
  exact step_end (simSteps_star_ex 77 ⟨B, .right, [1, 0, 1, 0, 1, 0], [0, 0, 0, 0, 0, 0]⟩ ⟨C, .left,
      [], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]⟩ rfl l default) (by norm_cfg) (by norm_cfg)

theorem close (l : zB) (a : Nat) (b : Nat) :
    ((((([1, 1, 0, 1, 1, 0] : zF) ^ (a)) +> (([1] : zF) +> l)) <{{C}} (([0, 1] : zF)
        +> ((([0, 1, 0] : zF) ^ (b)) +> default)))) [target_tm]⊢* ((l <{{E}} (([0, 1, 1] : zF)
            +> ((([0, 1, 0] : zF) ^ (a*2+b)) +> default)))) := by
  refine step_bridge (sr_6 (a) (([1] : zF) +> l) ((([0, 1, 0] : zF) ^ (b)) +> default))
      (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [1], [0, 1]⟩ ⟨E, .left, [],
      [0, 1, 1]⟩ rfl l ((([0, 1, 0, 0, 1, 0] : zF) ^ (a)) +> ((([0, 1, 0] : zF) ^ (b)) +> default)))
          (by norm_cfg) (by norm_cfg)

theorem close_odd (l : zB) (a : Nat) (b : Nat) :
    (((([1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (a)) +> l)) <{{C}} (([0, 1] : zF)
        +> ((([0, 1, 0] : zF) ^ (b)) +> default)))) [target_tm]⊢* ((l <{{C}} (([0, 1, 0, 1, 0] : zF)
            +> ((([0, 1, 0] : zF) ^ (a*2+b)) +> default)))) := by
  refine step_bridge (simSteps_star_ex 4 ⟨C, .left, [1, 1, 0], [0, 1]⟩ ⟨A, .left, [0],
      [1, 0, 1, 1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (a)) +> l) ((([0, 1, 0] : zF) ^ (b))
          +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_7 (a) (([0] : zF) +> l) ((([0, 1, 0] : zF) ^ (b)) +> default))
      (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 13 ⟨A, .left, [0], [1, 0, 1, 1]⟩ ⟨C, .left, [],
      [0, 1, 0, 1, 0]⟩ rfl l ((([0, 1, 0, 0, 1, 0] : zF) ^ (a)) +> ((([0, 1, 0] : zF) ^ (b))
          +> default))) (by norm_cfg) (by norm_cfg)

theorem root_end0 (a : Nat) (b : Nat) (c : Nat) :
    (rootW default (a) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (c) (0)) [target_tm]⊢* (((([1, 0] : zF)
        +> ((([1, 0] : zF) ^ (c)) +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
            ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))))))
                {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1] : zF)
          +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1] : zF)
      +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1]⟩ ⟨B,
      .right, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg)
              ?_
  refine step_bridge (sr_8 (b) (([1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1] : zF) +> default))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1], [1, 0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))) default)
              (by norm_cfg) (by norm_cfg)

theorem root_end1 (a : Nat) (b : Nat) (c : Nat) :
    (rootW default (a) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (c) (1))
        [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([1, 1, 0, 1, 1, 0] : zF)
            +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                ^ (a)) +> default)))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> default))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
      ^ (a)) +> default)) (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([1, 0] : zF) ^ (c))
              +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0] : zF)
          +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1, 0, 1], [0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))) default)
              (by norm_cfg) (by norm_cfg)

theorem crossZ_step (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ (l) (r) (4+a) (b) (3+c) (2+e)) [target_tm]⊢* (crossZ (l) (r) (a) (2+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
              +> l))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
                  ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg)
                  ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] :
              zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem rootZ_step (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (rootZ (r) (a) (b) (3+c) (2+e)) [target_tm]⊢* (rootZ (r) (4+a) (b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1], [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
          +> default))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) ((([1, 0] : zF)
              ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right, [0, 1], [0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossV_step (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV (l) (r) (4+a) (b) (3+c) (1+e)) [target_tm]⊢* (crossV (l) (r) (a) (2+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
              +> l))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))))
                      ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
              ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                      +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
                  ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c)
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
              (([1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
                  (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
                  ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                      +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF)
                  ^ (c)) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (c)) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) (by norm_cfg)

theorem rootV_step (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (rootV (r) (a) (b) (3+c) (1+e)) [target_tm]⊢* (rootV (r) (4+a) (b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1], [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
          +> default))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (a)) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
              ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (a)) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))
                      (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg)
              ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))))
                  (by norm_cfg) (by norm_cfg)

theorem even_root (a : Nat) (d : Nat) :
    (S default default (1) (1+a) (a*2) (1+d)) [target_tm]⊢* (rootW default (0)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+a)) (1+a*2) (d)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
          +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
              +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (a) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
          +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (a)) +> default)) (([0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a*2)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (a)) +> default))) ((([1, 0, 0] : zF) ^ (d)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (a*2) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (a))
          +> default) ((([1, 0] : zF) ^ (a*2)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
              (by norm_cfg) ?_
  refine step_bridge (sr_3 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a*2)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))
              (by norm_cfg) (by norm_cfg)

theorem even_end (a : Nat) :
    (S default default (1) (1+a) (a*2) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF)
        ^ (a*2)) +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (a))
            +> (([1, 0] : zF) +> default))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
          +> ((([1, 0] : zF) ^ (a*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (a) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (a*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (a)) +> default)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a*2)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (a)) +> default))) default) (by norm_cfg) (by norm_cfg)

theorem odd_seed (a : Nat) (b : Nat) (c : Nat) (d : Nat) :
    (((([1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c))
        +> default))) <{{B}} (([1, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
            +> ((([1, 0] : zF) ^ (a*2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
                +> default))))))) [target_tm]⊢* (seed (c) (b+a) (a) (d)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨B, .left, [1, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨C, .left,
      [0], [0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF)
          ^ (c)) +> default)) ((([0, 1, 1, 0, 1, 0] : zF) ^ (a)) +> ((([1, 0] : zF) ^ (a*2))
              +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_11 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))
      (([1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (a)) +> ((([1, 0] : zF)
          ^ (a*2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_12 (c) (([0] : zF) +> default) (([1, 0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (a)) +> ((([1, 0] : zF)
          ^ (a*2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (c)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
              +> ((([1, 0] : zF) ^ (a*2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
                  +> default)))))))) (by norm_cfg) (by norm_cfg)

theorem seed_root (a : Nat) (b : Nat) (c : Nat) (d : Nat) :
    (seed (a) (b) (c) (1+d)) [target_tm]⊢* (rootW default (1+a) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b))
        (1+c*2) (d)) := by
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [0], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> (([0, 1, 0, 0] : zF)
              +> ((([1, 0, 0] : zF) ^ (d)) +> default))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> (([0, 1, 0, 0] : zF)
          +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> (([0, 1, 0, 0] : zF)
              +> ((([1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0] : zF) +> ((([1, 0] : zF) ^ (c*2)) +> (([0, 1, 0, 0] : zF)
          +> ((([1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0, 0, 1, 0, 0] : zF)
          +> ((([1, 0, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c*2)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
              +> default))))) ((([1, 0, 0] : zF) ^ (d)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c*2) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([1, 0] : zF) ^ (c*2))
              +> ((([1, 0, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c*2)) +> ((([1, 0, 0] : zF)
          ^ (d)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [1, 0, 1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c*2))
              +> ((([1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c*2))
          +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c*2))
              +> ((([1, 0, 0] : zF) ^ (d)) +> default))))))) (by norm_cfg) (by norm_cfg)

theorem seed_zero (a : Nat) (b : Nat) (c : Nat) :
    (seed (a) (b) (c) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c*2))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF)
            +> ((([1, 0] : zF) ^ (a)) +> default)))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [0], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> default)))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c*2)) +> default))) (by norm_cfg)
              ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0] : zF) +> ((([1, 0] : zF) ^ (c*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0] : zF) +> default))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c*2)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))) default) (by norm_cfg)
              (by norm_cfg)

theorem even_exit (l : zB) (a : Nat) :
    (S (l) default (1) (1+a) (a*2) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (a)) +> (([1] : zF) +> l)))))
            {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (a)) +> ((([1, 0] : zF)
          ^ (a*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (a) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l) (([0] : zF) +> ((([1, 0] : zF)
      ^ (a*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (a)) +> l)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a*2)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (a)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem lone_one (b : Nat) (l : zB) (r : zB) :
    (((([1] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> l)))
        <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢* ((l <{{C}} (([0] : zF)
            +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> r))))) := by
  refine step_bridge (simSteps_star_ex 4 ⟨C, .left, [1, 1], [0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l)) r) (by norm_cfg) ?_
  refine step_bridge (sr_13 (b) (([0] : zF) +> l) (([1, 0, 1, 1] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .left, [0], [1, 0]⟩ ⟨A, .right, [0, 1],
      [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 1] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1] : zF) +> l) (([0, 1, 1] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l) r) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> l) (([1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .left, [1], [1, 0, 1, 0]⟩ ⟨C, .left, [],
      [0, 1, 0, 1, 0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> r)) (by norm_cfg) (by norm_cfg)

theorem cross_to_Z (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) :
    (crossW (l) (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) (2+a) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (3+c)
        (0)) [target_tm]⊢* (crossZ (l) (r) (a) (1+b) (5+c) (2)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
              ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
      +> l)) (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 1, 0] : zF) +> r)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
          [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 1, 0, 1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
                  +> ((([1, 0] : zF) ^ (a)) +> l)))) r) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
      ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0] : zF)
          +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 1, 0] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 1, 0] : zF) +> r)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0], [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B,
      .left, [], [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 1, 0] : zF) +> r))))) (by norm_cfg) (by norm_cfg)

theorem odd_block (l : zB) (r : zB) (b : Nat) :
    (((([1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l)) <{{B}} (([1] : zF) +> r)))
        [target_tm]⊢* ((l <{{A}} (([1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
            +> r)))) := by
  refine step_bridge (simSteps_star_ex 6 ⟨B, .left, [1, 1, 0], [1]⟩ ⟨C, .left, [0],
      [0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l) r) (by norm_cfg) ?_
  refine step_bridge (sr_11 (b) (([0] : zF) +> l) (([1, 0] : zF) +> r)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> r)) (by norm_cfg) (by norm_cfg)

theorem even_block (l : zB) (r : zB) (b : Nat) :
    ((((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l) <{{B}} (([1] : zF) +> r)))
        [target_tm]⊢* ((l <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> r)))) := by
  exact step_end (sr_10 (b) l r) (by norm_cfg) (by norm_cfg)

theorem S_exit0 (l : zB) (a : Nat) (b : Nat) (c : Nat) :
    (S (l) default (2+a) (1+b) (c) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
        +> (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
            +> ((([1, 0] : zF) ^ (a)) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg)
              ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
      +> l)) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
      ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) default)
              (by norm_cfg) (by norm_cfg)

theorem S_exit1 (l : zB) (a : Nat) (b : Nat) (c : Nat) :
    (S (l) default (4+a) (1+b) (c) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
        ^ (c)) +> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
            +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))))
                {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
              +> l))))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 0, 1, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                  +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 1 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([0, 1] : zF) ^ (c)) +> default))
                  (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1] : zF)
          +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) default)
              (by norm_cfg) (by norm_cfg)

theorem S_root1 (b : Nat) (c : Nat) (d : Nat) :
    (S default default (1) (1+b) (c) (1+d)) [target_tm]⊢* (rootW default (0)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (1+c) (d)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d))
              +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))
          (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) ((([1, 0, 0] : zF) ^ (d)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))
              (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default) (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> default)))))
              (by norm_cfg) (by norm_cfg)

theorem into_S (l : zB) (r : zB) (a : Nat) (d : Nat) :
    (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0] : zF) ^ (d)) +> (([0, 1] : zF) +> r))))) [target_tm]⊢* (S (l) (([1] : zF)
            +> r) (a) (1) (0) (d)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0], [0, 1, 0, 1, 0, 0, 1]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 0, 1] : zF) ^ (d)) +> r))
          (by norm_cfg) (by norm_cfg)

theorem crossV_end (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV (l) (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (4+a) (b) (3+c) (0))
        [target_tm]⊢* (crossZ (l) (r) (a) (2+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
              +> l))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
                  ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_9 (c)
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg)
                  ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF)
                  ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg)
                      (by norm_cfg)

theorem cross_to_V (l : zB) (r : zB) (a : Nat) (b : Nat) (c : Nat) (n : Nat) :
    (crossW (l) (([0, 1, 1, 0, 1, 0, 0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (n))
        +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (n*2)) +> (([0] : zF) +> r)))))
            (2+a) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (3+c) (0)) [target_tm]⊢* (crossV (l)
                (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r)) (a) (1+b)
                    (5+c) (n)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
              ^ (c)) +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
      +> l)) (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
          [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
                  +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (n*2)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
                  +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                      +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))
                          (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
      ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
              +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                      +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))
                          (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0], [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B,
      .left, [], [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))
                      (by norm_cfg) (by norm_cfg)

theorem S_short1 (l : zB) (b : Nat) (c : Nat) :
    (S (l) default (3) (1+b) (c) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
        +> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
            +> (([1] : zF) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : zF) +> l) (([0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l))) (([0, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l)))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0] : zF) +> l))) (([1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0] : zF) +> l)) ((([0, 1] : zF) ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0] : zF) +> l) (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l)
      (([0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 1 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1]⟩ ⟨B, .right, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l) ((([0, 1] : zF) ^ (c)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l)) (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem lone_S (l : zB) (r : zB) (a : Nat) (b : Nat) (m : Nat) :
    (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)) <{{C}} (([0] : zF)
        +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (m))
            +> (([0, 1] : zF) +> r))))))) [target_tm]⊢* (S (l) (([1] : zF) +> r) (a) (1+b) (0)
                (m)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0], [0, 1, 0, 1, 0, 0, 1]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([1, 0, 1, 0, 0, 1] : zF)
          ^ (b)) +> ((([0, 0, 1] : zF) ^ (m)) +> r))) (by norm_cfg) (by norm_cfg)

theorem crossW_one (r : zB) (b : Nat) (c : Nat) (d : Nat) :
    (crossW default (r) (1) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (c) (2+d)) [target_tm]⊢* (rootW (r)
        (0) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (2+c) (d)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF)
              ^ (d)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) ((([0, 1, 0] : zF) ^ (d)) +> r))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r))) (by norm_cfg)
                  ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> ((([0, 1, 0] : zF) ^ (d)) +> r)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))
              (by norm_cfg) (by norm_cfg)

theorem root_to_Z (r : zB) (a : Nat) (b : Nat) (c : Nat) :
    (rootW (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) (a) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (3+c) (0))
        [target_tm]⊢* (rootZ (r) (2+a) (b) (5+c) (2)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF)
          +> r)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 1, 0, 1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (a)) +> default)))) r) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
          +> r)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 1, 0] : zF) +> r)))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem cross_to_Z_one (r : zB) (b : Nat) (c : Nat) :
    (crossW default (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) (1) (([1, 0, 1, 0, 0, 1] : zF) ^ (b))
        (3+c) (0)) [target_tm]⊢* (rootZ (r) (0) (1+b) (5+c) (2)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF)
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 1, 0] : zF)
          +> r)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1, 0, 1, 0, 1, 0] : zF) +> r))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) r)
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0] : zF) +> r)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 1, 0] : zF) +> r)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
              +> r))))) (by norm_cfg) (by norm_cfg)

theorem root_to_V (r : zB) (a : Nat) (b : Nat) (c : Nat) (n : Nat) :
    (rootW (([0, 1, 1, 0, 1, 0, 0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (n))
        +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (n*2)) +> (([0] : zF) +> r))))) (a)
            (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (3+c) (0))
                [target_tm]⊢* (rootV (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                    ^ (n*2)) +> r)) (2+a) (b) (5+c) (n)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r)))))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))) (by norm_cfg)
                  ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r)))))) (by norm_cfg)
                      ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (a)) +> default)))) ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                      +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))
                          (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
              +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))) (by norm_cfg)
                  ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r)))))))))
                      (by norm_cfg) (by norm_cfg)

theorem cross_to_V_one (r : zB) (b : Nat) (c : Nat) (n : Nat) :
    (crossW default (([0, 1, 1, 0, 1, 0, 0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (n))
        +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (n*2)) +> (([0] : zF) +> r))))) (1)
            (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (3+c) (0))
                [target_tm]⊢* (rootV (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                    ^ (n*2)) +> r)) (0) (1+b) (5+c) (n)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 7 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r)))))) (by norm_cfg)
                      ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 21 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
                  ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (n*2)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (n*2)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
                  +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n)) +> (([1, 0, 1, 0, 1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (n*2)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
              +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (n))
                  +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> r))))))))
                      (by norm_cfg) (by norm_cfg)

theorem rootV_end (r : zB) (a : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (rootV (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (a) (b) (3+c) (0))
        [target_tm]⊢* (rootZ (r) (4+a) (b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1], [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
          +> default))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([0, 0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
              +> default)))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossV_one (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (r) (1) (b) (3+c) (1+e)) [target_tm]⊢* (rootV (r) (2) (1+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
                  ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default)))
          (([1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> (([0, 1, 0, 1] : zF) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))
                      (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossV_three (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (r) (3) (b) (3+c) (1+e)) [target_tm]⊢* (rootV (r) (0) (2+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))
          (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> default))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> default))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] :
              zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) (by norm_cfg)

theorem crossVend_one (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (1) (b) (3+c) (0))
        [target_tm]⊢* (rootZ (r) (2) (1+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))
              ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))) (([1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossVend_three (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (3) (b) (3+c) (0))
        [target_tm]⊢* (rootZ (r) (0) (2+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 0, 1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] :
              zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_one' (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ default (r) (1) (b) (3+c) (2+e)) [target_tm]⊢* (rootZ (r) (2) (1+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) ((([1, 0] : zF) ^ (e)) +> r))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1]⟩ ⟨B,
      .right, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))) (([1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF)
                  ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_three' (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ default (r) (3) (b) (3+c) (2+e)) [target_tm]⊢* (rootZ (r) (0) (2+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem S_root1' (r : zB) (b : Nat) (c : Nat) (d : Nat) :
    (S default (r) (1) (1+b) (c) (1+d)) [target_tm]⊢* (rootW (([0] : zF) +> r) (0)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (1+c) (d)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) ((([1, 0, 0] : zF) ^ (d)) +> r))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0, 0] : zF) ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default) (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> r)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> ((([1, 0, 0] : zF) ^ (d)) +> r)))))
              (by norm_cfg) (by norm_cfg)

theorem S_short0 (l : zB) (b : Nat) (c : Nat) :
    (S (l) default (1) (1+b) (c) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> l)))))
            {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF)
          ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l) (([0] : zF) +> ((([1, 0] : zF)
      ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> l)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem crossV_step_block (l : zB) (r : zB) (a : Nat) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> l))) (r) (2) (b) (3+c) (1+e)) [target_tm]⊢* (crossV (l) (r) (a) (2+vB+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                      +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                      +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))))
              (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF)
                      ^ (a)) +> l)))))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
          +> l))))) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (a)) +> l)))) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
      +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
                  +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                      +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                          (by norm_cfg) ?_
  refine step_bridge (sr_9 (c)
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
              +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
                  ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))))
                      ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
          +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
                  +> ((([1, 0] : zF) ^ (a)) +> l))) ((([1, 0] : zF) ^ (c))
                      +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                          (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF)
      ^ (a)) +> l))) (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_4 (vB) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_step_block (l : zB) (r : zB) (a : Nat) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> l))) (r) (2) (b) (3+c) (2+e)) [target_tm]⊢* (crossZ (l) (r) (a) (2+vB+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))) (([0, 0, 1, 0, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
                  +> l)))))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
          +> l))))) (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
                  +> l)))) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                      +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
      +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
                  +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
          +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))))
                  ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
          +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] :
              zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))
                  ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF)
      ^ (a)) +> l))) (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  refine step_bridge (sr_4 (vB) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF)
                      ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossVend_block (l : zB) (r : zB) (a : Nat) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> l))) (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (2) (b) (3+c) (0))
            [target_tm]⊢* (crossZ (l) (r) (a) (2+vB+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)))) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg)
                      ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))) (([0, 0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
                  +> l)))))) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
          +> l))))) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (a)) +> l)))) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                      +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
      +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
                  +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c)
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
              +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
                  (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF) ^ (a)) +> l)))))
                  ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
          +> ((([1, 0] : zF) ^ (a)) +> l)))) (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB))
                  +> ((([1, 0] : zF) ^ (a)) +> l))) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> ((([1, 0] : zF)
      ^ (a)) +> l))) (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  refine step_bridge (sr_4 (vB) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossV_step_block_root (r : zB) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0] : zF) +> default)) (r) (2) (b) (3+c)
        (1+e)) [target_tm]⊢* (rootV (r) (0) (2+vB+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF)
                      ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
              ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
              ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF)
                      ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] :
              zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  refine step_bridge (sr_3 (vB) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_step_block_root (r : zB) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0] : zF) +> default)) (r) (2) (b) (3+c)
        (2+e)) [target_tm]⊢* (rootZ (r) (0) (2+vB+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([0, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (vB) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF)
                      ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossVend_block_root (r : zB) (vB : Nat) (b : Nat) (c : Nat) (e : Nat) :
    (crossV ((([1, 1, 0, 1, 1, 0] : zF) ^ (vB)) +> (([1, 0] : zF) +> default)) (([1, 0] : zF)
        +> ((([1, 0] : zF) ^ (e)) +> r)) (2) (b) (3+c) (0)) [target_tm]⊢* (rootZ (r) (0) (2+vB+b)
            (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
          +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([0, 0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([0, 1] : zF) ^ (c))
                  +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (vB) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (vB) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) (([0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB))
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] :
              zF) ^ (b)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default)) ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (vB)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (vB) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (vB)) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                      +> ((([1, 0] : zF) ^ (e)) +> r))))))) (by norm_cfg) (by norm_cfg)

theorem crossW_finish0 (l : zB) (a : Nat) (b : Nat) (c : Nat) :
    (crossW (l) default (2+a) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (c) (0))
        [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
                +> ((([1, 0] : zF) ^ (a)) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 12 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1]⟩ ⟨B, .right,
      [1, 1, 0, 1, 1, 0, 1, 1, 0], [1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_8 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
      ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1], [1, 0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) default)
              (by norm_cfg) (by norm_cfg)

theorem crossW_finish1 (l : zB) (a : Nat) (b : Nat) (c : Nat) :
    (crossW (l) default (2+a) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (c) (1))
        [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
                +> ((([1, 0] : zF) ^ (a)) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
              +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
      +> l)) (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF) ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([0] : zF)
          +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1, 0, 1], [0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) default)
              (by norm_cfg) (by norm_cfg)

theorem crossW_short0 (l : zB) (b : Nat) (c : Nat) :
    (crossW (l) default (1) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (c) (0))
        [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([1, 1, 0, 1, 1, 0] : zF)
            +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 12 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1]⟩ ⟨B, .right,
      [1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl l ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c))
          +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_8 (b) (([1, 1, 0, 1, 1, 0, 1] : zF) +> l) (([1] : zF) +> ((([0, 1] : zF)
      ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> l)) (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1], [1, 0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem crossW_short1 (l : zB) (b : Nat) (c : Nat) :
    (crossW (l) default (1) (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (c) (1))
        [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([1, 1, 0, 1, 1, 0] : zF)
            +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l)
          ((([1, 0] : zF) ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> l)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1, 0, 1], [0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem scan_root_step (a : Nat) (d : Nat) :
    (scan_root (a) (2+d)) [target_tm]⊢* (scan_root (4+a) (d)) := by
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [0], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d))
          +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 0] : zF) ^ (d))
          +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl default ((([0, 1] : zF) ^ (a)) +> ((([0, 1, 0] : zF) ^ (d))
          +> default))) (by norm_cfg) (by norm_cfg)

theorem bare_root (a : Nat) (b : Nat) (c : Nat) :
    ((default <{{A}} (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> default)))))))
            [target_tm]⊢* (section_481 [1+c, 2+b*2, 2+a]) := by
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [0], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> default)))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg)
              ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0] : zF) +> default))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))) default) (by norm_cfg)
              (by norm_cfg)

theorem unary_zero :
    (section_481 [0]) [target_tm]⊢⁺ (section_481 [3]) := by
  exact step_end_plus (simSteps_plus 13 (by decide) ⟨B, .right, [0, 0], [0, 0, 0]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1], []⟩ rfl default default) (by norm_cfg) (by norm_cfg)

theorem unary_one :
    (section_481 [1]) [target_tm]⊢⁺ (section_481 [5]) := by
  exact step_end_plus (simSteps_plus 39 (by decide) ⟨B, .right, [1, 0, 0, 0, 0, 0], [0, 0, 0]⟩ ⟨B,
      .right, [1, 0, 1, 0, 1, 0, 1, 0, 1], []⟩ rfl default default) (by norm_cfg) (by norm_cfg)

theorem unary_two :
    (section_481 [2]) [target_tm]⊢⁺ (section_481 [9]) := by
  exact step_end_plus (simSteps_plus 142 (by decide) ⟨B, .right, [1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
      [0, 0, 0, 0, 0, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
          []⟩ rfl default default) (by norm_cfg) (by norm_cfg)

theorem pred_S (a : Nat) (b : Nat) (n : Nat) :
    (((([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF)
        +> ((([1, 0] : zF) ^ (a)) +> default)))) <{{E}} (([0, 1, 1] : zF) +> ((([0, 1, 0] : zF)
            ^ (n)) +> default)))) [target_tm]⊢* (S default default (a) (2+b) (0) (n)) := by
  refine step_bridge (simSteps_star_ex 10 ⟨E, .left, [1, 1, 0, 1, 1, 0, 1], [0, 1, 1]⟩ ⟨B, .left,
      [1], [1, 0, 1, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (a)) +> default))) ((([0, 1, 0] : zF) ^ (n)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))
      (([0, 1, 1, 0, 1, 0, 1, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n))
              +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
      +> default)) (([0, 1, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 1]⟩ ⟨E,
      .left, [0], [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (a)) +> default)) ((([0, 1, 0] : zF) ^ (n)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> default)))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0], [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B,
      .left, [], [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([0, 1, 0] : zF) ^ (n)) +> default)))
              (by norm_cfg) (by norm_cfg)

theorem rootT_step (a : Nat) (b : Nat) (c : Nat) (d : Nat) :
    (rootT (a) (b) (c) (2+d)) [target_tm]⊢* (rootT (2+a) (b) (2+c) (d)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
              +> ((([0, 0, 1] : zF) ^ (d)) +> default))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
          +> ((([0, 0, 1] : zF) ^ (d)) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
              +> ((([0, 0, 1] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
      ^ (a)) +> default)) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1] : zF)
          +> ((([0, 0, 1] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([0, 0, 1, 0, 0, 1] : zF) +> ((([0, 0, 1] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
              +> default))))) ((([0, 0, 1] : zF) ^ (d)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 0, 1] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([0, 1] : zF) ^ (c))
                  +> ((([0, 0, 1] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> ((([0, 0, 1] : zF) ^ (d)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> ((([0, 0, 1] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default)
      (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> ((([0, 0, 1] : zF) ^ (d))
              +> default)))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> (([0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF)
              +> ((([0, 1] : zF) ^ (c)) +> ((([0, 0, 1] : zF) ^ (d)) +> default))))))) (by norm_cfg)
                  (by norm_cfg)

theorem rootT_end0 (a : Nat) (b : Nat) (c : Nat) :
    (rootT (a) (b) (c) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
            +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))))))
                {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1] : zF)
          +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1] : zF)
      +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1]⟩ ⟨B,
      .right, [1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 0, 1, 1, 0, 1] : zF) ^ (b)) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg)
              ?_
  refine step_bridge (sr_8 (b) (([1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1] : zF) +> default))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1], [1, 0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))) default)
              (by norm_cfg) (by norm_cfg)

theorem rootT_end1 (a : Nat) (b : Nat) (c : Nat) :
    (rootT (a) (b) (c) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b))
            +> (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))))))
                {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 1, 0, 1, 0] : zF)
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF)
              +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF)
          +> default))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF)
              +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
      ^ (a)) +> default)) (([0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
              +> default))))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 0, 1, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([0, 1] : zF) ^ (c))
              +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default)
      (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> (([0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF)
              +> ((([0, 1] : zF) ^ (c)) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 0, 1, 1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 6 ⟨A, .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
      [0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
          [0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1] : zF) ^ (a)) +> default)) (([0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 1 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([0, 1] : zF) ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))))
              default) (by norm_cfg) (by norm_cfg)

theorem pred_root (b : Nat) (n : Nat) :
    (((([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF)
        +> default))) <{{E}} (([0, 1, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> default))))
            [target_tm]⊢* (rootT (0) (b) (0) (n)) := by
  refine step_bridge (simSteps_star_ex 10 ⟨E, .left, [1, 1, 0, 1, 1, 0, 1], [0, 1, 1]⟩ ⟨B, .left,
      [1], [1, 0, 1, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)
          ((([0, 1, 0] : zF) ^ (n)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default) (([0, 1, 1, 0, 1, 0, 1, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 1] : zF) +> ((([0, 1, 0] : zF) ^ (n)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 24 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)
          ((([0, 1, 0] : zF) ^ (n)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default) (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left,
      [], [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([0, 1, 0] : zF) ^ (n)) +> default))) (by norm_cfg) (by norm_cfg)

theorem scan_left_step (r : zB) (a : Nat) (d : Nat) :
    (scan_left (r) (a) (2+d)) [target_tm]⊢* (scan_left (r) (4+a) (d)) := by
  refine step_bridge (simSteps_star_ex 4 ⟨A, .left, [0], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d))
          +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1] : zF) +> default) (([0, 0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 0] : zF) ^ (d)) +> r))
          (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1, 0] : zF) ^ (d)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl default ((([0, 1] : zF) ^ (a)) +> ((([0, 1, 0] : zF) ^ (d))
          +> r))) (by norm_cfg) (by norm_cfg)

theorem scan_left_entry (r : zB) (d : Nat) :
    (((([1, 0] : zF) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))
        [target_tm]⊢* (scan_left (r) (3) (d)) := by
  exact step_end (simSteps_star_ex 25 ⟨C, .left, [1, 0, 0, 0, 0], [0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl default ((([0, 1, 0] : zF) ^ (d)) +> r)) (by norm_cfg)
          (by norm_cfg)

theorem scanW_entry (l : zB) (r : zB) (a : Nat) (w : zF) (c : Nat) (d : Nat) :
    (scanW (([1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)) (r) (w) (c) (d))
        [target_tm]⊢* (crossW (l) (r) (a) (([1, 0, 1, 0, 0, 1] : zF) ++ w) (c) (d)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0], [0, 1, 0, 1, 0, 0, 1]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) (w +> (([1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg)
              (by norm_cfg)

theorem crossW_zero (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (crossW default (r) (0) (w) (c) (d)) [target_tm]⊢* (rootW (r) (2) (w) (c) (d)) := by
  exact step_end (simSteps_star_ex 21 ⟨B, .left, [0, 0, 0], [1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0]⟩ rfl default (w +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem crossV_two (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (r) (2) (b) (3+c) (1+e)) [target_tm]⊢* (rootV (r) (4) (1+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF)
      +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default))
          (([0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1],
      [0, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)))
                  ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))
              (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF)
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))
          (([1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg)
              ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1],
      [1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
              +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
                  +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))) ((([1, 0, 1, 0, 0, 1] : zF)
                      ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))
          (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) (by norm_cfg)

theorem crossV_zero (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (r) (0) (b) (c) (e)) [target_tm]⊢* (rootV (r) (2) (b) (c) (e)) := by
  exact step_end (simSteps_star_ex 21 ⟨B, .left, [0, 0, 0], [1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg)
              (by norm_cfg)

theorem crossZ_zero (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ default (r) (0) (b) (c) (e)) [target_tm]⊢* (rootZ (r) (2) (b) (c) (e)) := by
  exact step_end (simSteps_star_ex 21 ⟨B, .left, [0, 0, 0], [1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (c))
          +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_two (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossZ default (r) (2) (b) (3+c) (2+e)) [target_tm]⊢* (rootZ (r) (4) (1+b) (3+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF)
      +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1, 1] : zF)
          +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default))) ((([1, 0] : zF) ^ (e)) +> r))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 3 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1]⟩ ⟨B,
      .right, [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))
          (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 13 ⟨B, .right, [1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], [1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossVend_two (r : zB) (b : Nat) (c : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (2) (b) (3+c) (0))
        [target_tm]⊢* (rootZ (r) (4) (1+b) (4+c) (e)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default) (([0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1], [0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF)
              ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF)
      +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 0, 1, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .right, [0, 1, 0, 1], [0, 0, 1, 0, 0, 1, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))))
                      (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF)
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))
          (([1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 1, 0, 0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0] : zF)
          +> ((([1, 0] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
                  +> (([0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_empty (l : zB) (a : Nat) (b : Nat) (c : Nat) :
    (crossZ (l) (([1, 0, 1] : zF) +> default) (4+a) (b) (4+c) (0)) [target_tm]⊢* (crossW (l)
        default (a) (([1, 0, 1, 0, 0, 1] : zF) ^ (2+b)) (2+c) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF)
                  +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF)
          +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
              +> l))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([0, 1] : zF) ^ (c))
                  +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (c)) +> (([1] : zF) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
              [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
                  ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c)
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))) (([1, 1] : zF)
              +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)))
          (([1, 0, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 32 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([0, 1] : zF)
                  ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> default))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF)
                  ^ (c)) +> default)))) (by norm_cfg) (by norm_cfg)

theorem rootZ_empty (a : Nat) (b : Nat) (c : Nat) :
    (rootZ (([1, 0, 1] : zF) +> default) (a) (b) (4+c) (0)) [target_tm]⊢* (rootW default (4+a)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (2+c) (0)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF)
              +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0, 1] : zF) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (a)) +> default))) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF)
              +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([0, 0, 1, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
              +> default)))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1] : zF) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> (([1] : zF) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1] : zF) +> default)))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF)
          +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1], [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) (([1, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))) default)
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))))
          (([1, 0, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> default))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
              +> default))))) (by norm_cfg) (by norm_cfg)

theorem crossZ_empty_one (b : Nat) (c : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (1) (b) (4+c) (0))
        [target_tm]⊢* (rootW default (2) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (2+c) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default) (([0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> default) ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default))) default)
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF)
          +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))
              ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default))) (([1, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF) +> default)))) default)
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> default)) ((([0, 1] : zF) ^ (c)) +> default)) (by norm_cfg)
                  ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg)
                  (by norm_cfg)

theorem crossZ_empty_three (b : Nat) (c : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (3) (b) (4+c) (0))
        [target_tm]⊢* (rootW default (0) (([1, 0, 1, 0, 0, 1] : zF) ^ (2+b)) (2+c) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)))
              default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg)
                  ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> (([1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF)
                  +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([0, 1] : zF) ^ (c))
              +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 1] : zF) +> default)) (by norm_cfg)
          ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 28 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([0, 1] : zF) ^ (c)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> default))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> default)))) (by norm_cfg) (by norm_cfg)

theorem crossZ_empty_two (b : Nat) (c : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (2) (b) (4+c) (0))
        [target_tm]⊢* (rootW default (4) (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (2+c) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default)))))
              (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default)
      (([0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 4 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1],
      [0, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
          [0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default) ((([1, 0] : zF) ^ (c))
              +> (([0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF)
      +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)) (([0, 0, 1, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 18 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1] : zF) ^ (c))
          +> (([1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (b)) +> default)))
              default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (b)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF)
          +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 0, 1] : zF)
                  +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 5 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 0, 1]⟩ ⟨B, .right, [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF)
              +> default)) ((([0, 1] : zF) ^ (c)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_9 (c) (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)))
          (([1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 17 ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], [1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (c)) +> (([1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))))
              default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (c) (([1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
      +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default))) (([1, 0, 1, 0, 1, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([0, 1] : zF) ^ (c)) +> default))
                  (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> default)))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
                  +> default)))) (by norm_cfg) (by norm_cfg)

theorem scan_left_zero (r : zB) (d : Nat) :
    ((default <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))
        [target_tm]⊢* (scan_left (r) (1) (d)) := by
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1]⟩ rfl default ((([0, 1, 0] : zF) ^ (d)) +> r)) (by norm_cfg) (by norm_cfg)

theorem scanW_zero (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (scanW default (r) (w) (c) (d)) [target_tm]⊢* (rootW (r) (0) (([1, 0, 1, 0, 0, 1] : zF) ++ w)
        (c) (d)) := by
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 0, 1]⟩ rfl default (w +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem cleanup_one_entry (l : zB) (a : Nat) (r : zB) :
    (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l)) <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF)
        +> r))) [target_tm]⊢* (crossV (l) (r) (a) (0) (2) (0)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ ⟨B, .left,
      [], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) r) (by norm_cfg)
          (by norm_cfg)

theorem cleanup_one_zero (r : zB) :
    ((default <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> r))) [target_tm]⊢* (rootV (r) (0) (0)
        (2) (0)) := by
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl default r) (by norm_cfg) (by norm_cfg)

theorem crossV_low (l : zB) (r : zB) (a : Nat) (b : Nat) (e : Nat) :
    (crossV (l) (r) (4+a) (b) (2) (1+e)) [target_tm]⊢* (crossV (l) (r) (a) (2+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
              +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                  (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 27 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl
              ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
                  +> l))) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 48 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨E, .left,
          [0], [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l))
                  ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem rootV_low (r : zB) (a : Nat) (b : Nat) (e : Nat) :
    (rootV (r) (a) (b) (2) (1+e)) [target_tm]⊢* (rootV (r) (4+a) (b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1] : zF)
      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1]⟩ ⟨C, .right,
      [1, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨C, .right, [1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
                  ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .right, [0, 1], [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem crossV_low_one (r : zB) (b : Nat) (e : Nat) :
    (crossV default (r) (1) (b) (2) (1+e)) [target_tm]⊢* (rootV (r) (2) (1+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C,
      .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
          +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
              (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 22 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0, 1] : zF) +> default)) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
          ^ (e)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
                  (by norm_cfg) (by norm_cfg)

theorem crossV_low_three (r : zB) (b : Nat) (e : Nat) :
    (crossV default (r) (3) (b) (2) (1+e)) [target_tm]⊢* (rootV (r) (0) (2+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1, 0, 1],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
              +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 27 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl
              ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 44 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl
              ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> default) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                  +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem crossV_low_two (r : zB) (b : Nat) (e : Nat) :
    (crossV default (r) (2) (b) (2) (1+e)) [target_tm]⊢* (rootV (r) (4) (1+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C,
      .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
          +> (([0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))))
              (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 23 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] :
              zF) ^ (b)) +> default) ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
                  +> (([1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e))
                      +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([1, 0, 1, 0, 0, 1] : zF)
                  ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF)
          ^ (e)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 0, 1] : zF)
                  +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (e)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem crossVend_low (l : zB) (r : zB) (a : Nat) (b : Nat) (e : Nat) :
    (crossV (l) (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (4+a) (b) (2) (0))
        [target_tm]⊢* (crossZ (l) (r) (a) (2+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
              +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 27 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) ((([1, 0] : zF) ^ (e))
                  +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 48 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1, 0]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]⟩ rfl
              ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) ((([1, 0] : zF)
                  ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF)
          ^ (e)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF)
                  ^ (e)) +> r)))) (by norm_cfg) (by norm_cfg)

theorem rootVend_low (r : zB) (a : Nat) (b : Nat) (e : Nat) :
    (rootV (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (a) (b) (2) (0)) [target_tm]⊢* (rootZ (r)
        (4+a) (b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (([0, 1] : zF)
          +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r)))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0, 0, 1] : zF)
      +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 2 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0, 0, 1]⟩ ⟨C, .right,
      [1, 1, 0, 1, 0, 1, 0, 1], [1]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨C, .right, [1, 1, 0, 1], [1, 0, 0, 1, 1, 0]⟩ ⟨A, .left,
      [1], [1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))) ((([1, 0] : zF) ^ (e))
              +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .right, [0, 1], [0, 1, 0, 1, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default)))
              ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))))
              (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
              +> r))))) (by norm_cfg) (by norm_cfg)

theorem crossVend_low_one (r : zB) (b : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (1) (b) (2) (0))
        [target_tm]⊢* (rootZ (r) (2) (1+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C,
      .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
          +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 22 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg)
                  (by norm_cfg)

theorem crossVend_low_three (r : zB) (b : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (3) (b) (2) (0))
        [target_tm]⊢* (rootZ (r) (0) (2+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1, 0, 1],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b)) +> (([0, 0, 1, 1, 0] : zF)
              +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 27 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 0, 1, 1, 0]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 44 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
          +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) (by norm_cfg)

theorem crossVend_low_two (r : zB) (b : Nat) (e : Nat) :
    (crossV default (([1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)) (2) (b) (2) (0))
        [target_tm]⊢* (rootZ (r) (4) (1+b) (3) (e)) := by
  refine step_bridge (simSteps_star_ex 15 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ ⟨C,
      .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1], [1]⟩ rfl default ((([1, 0, 1, 0, 0, 1] : zF) ^ (b))
          +> (([0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_15 (b) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default)
      (([1, 0, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 23 ⟨C, .right, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 0, 1, 1, 0]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) ((([1, 0] : zF) ^ (e)) +> r)) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1, 0] : zF)
                  +> ((([1, 0] : zF) ^ (e)) +> r)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1, 0]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) ((([1, 0] : zF) ^ (e)) +> r))
                  (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e)) +> r)))
          (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0] : zF) +> ((([1, 0] : zF) ^ (e))
                  +> r)))) (by norm_cfg) (by norm_cfg)

theorem crossZ_empty_low (l : zB) (a : Nat) (b : Nat) :
    (crossZ (l) (([1, 0, 1] : zF) +> default) (4+a) (b) (3) (0)) [target_tm]⊢* (crossW (l)
        default (a) (([1, 0, 1, 0, 0, 1] : zF) ^ (2+b)) (1) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1, 0, 0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
      ^ (a)) +> l)) (([0, 1, 0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 35 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> (([0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))) default) (by norm_cfg)
                  ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1] : zF) +> default))) (by norm_cfg)
                  ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 0] : zF) ^ (a)) +> l)) (([0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 48 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1, 0, 1, 1]⟩ ⟨E, .left, [0],
          [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 1, 0, 1, 1, 0] :
              zF) ^ (b)) +> ((([1, 0] : zF) ^ (a)) +> l)) default) (by norm_cfg) ?_
  refine step_bridge (sr_4 (b) (([0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg)
          ?_
  exact step_end (simSteps_star_ex 1 ⟨E, .left, [0],
      [0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨B, .left, [],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a))
              +> l) ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default))) (by norm_cfg)
                  (by norm_cfg)

theorem rootZ_empty_low (a : Nat) (b : Nat) :
    (rootZ (([1, 0, 1] : zF) +> default) (a) (b) (3) (0)) [target_tm]⊢* (rootW default (4+a)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (b)) (1) (0)) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 0, 1, 0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 0, 1, 0, 1] : zF) +> default))))
          (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([0, 1, 0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .right, [0, 1], [0, 1, 0, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (a)) +> default))) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a)) +> default))
      (([1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 8 ⟨A, .left, [1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 14 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 0, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1] : zF) +> default)))) (by norm_cfg)
              ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .right, [0, 1], [0, 1, 0, 1, 1]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (a)) +> default))) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (a))
      +> default)) (([1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1], [1, 0, 1, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1] : zF) ^ (a)) +> default)
          ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF)
      +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default)))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨A,
      .left, [], [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a))
          +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default)))) (by norm_cfg)
              (by norm_cfg)

theorem crossZ_empty_low_one (b : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (1) (b) (3) (0)) [target_tm]⊢* (rootW default (2)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (1) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 0, 1, 0, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> default) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 16 ⟨A, .left, [1, 0, 0], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
          ^ (b)) +> (([1, 0, 1, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1] : zF) +> default)) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 12 ⟨A, .left, [1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1] : zF) +> default))) (by norm_cfg) (by norm_cfg)

theorem crossZ_empty_low_three (b : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (3) (b) (3) (0)) [target_tm]⊢* (rootW default (0)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (2+b)) (1) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 35 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) default) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1] : zF) +> default)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1, 0, 1, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 44 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1, 0, 1, 1]⟩ ⟨A, .left, [1],
          [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF)
              ^ (b)) +> default) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default))) (by norm_cfg)
                  (by norm_cfg)

theorem crossZ_empty_low_two (b : Nat) :
    (crossZ default (([1, 0, 1] : zF) +> default) (2) (b) (3) (0)) [target_tm]⊢* (rootW default (4)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+b)) (1) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> (([1, 0, 0, 1, 0, 1] : zF) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default)
      (([0, 1, 0, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 31 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1],
      [0, 1, 0, 0, 1, 0, 1]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (b))
              +> default) default) (by norm_cfg) ?_
  refine step_bridge (sr_14 (b) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 41 ⟨C, .left, [1, 0, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1],
              [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1, 0, 1, 1] : zF)
                  +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([0, 1, 0, 1, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 30 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1], [0, 1, 0, 1, 1]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
          +> (([0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)) default) (by norm_cfg) ?_
  refine step_bridge (sr_3 (b) (([1, 0, 1, 0, 1, 0, 1, 0, 1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 20 ⟨A, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default
              ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> default))) (by norm_cfg)
                  (by norm_cfg)

theorem P_S_1 (l : zB) (b : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)))) [target_tm]⊢* (S (l) default (2+b*2)
            (1) (0) (b*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0]⟩ ⟨B, .left,
      [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l)
          ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)) (by norm_cfg) (by norm_cfg)

theorem P_S_2 (l : zB) (b : Nat) :
    (S (l) default (2) (1+b) (b*2) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2))
        +> (([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))))
            {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> l) (([0] : zF)
      +> ((([1, 0] : zF) ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (b*2) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem P_S'_1 (l : zB) (b : Nat) :
    (((([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default))))
            [target_tm]⊢* (S (l) default (4+b*2) (1) (0) (1+b*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l)
              ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)) (by norm_cfg) (by norm_cfg)

theorem P_S'_2 (l : zB) (b : Nat) :
    (S (l) default (4) (1+b) (b*2) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
        ^ (b*2)) +> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
            +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l)))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0],
          [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF) ^ (b*2))
              +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> l) (([0] : zF)
      +> ((([1, 0] : zF) ^ (b*2)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (b*2) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> l))) (([0, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> l)))) default) (by norm_cfg)
              ?_
  refine step_bridge (sr_2 (b*2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0, 1, 0] : zF) +> l))) (([1, 0, 1, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0, 1, 0] : zF) +> l)) ((([0, 1] : zF) ^ (b*2)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0, 1, 0] : zF) +> l)
      (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (b*2)) +> default)))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0, 1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (b)) +> (([1] : zF) +> ((([0, 1] : zF) ^ (b*2)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> l)
      (([0, 1] : zF) +> ((([0, 1] : zF) ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 1 ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [0, 1]⟩ ⟨B, .right,
          [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0], [1]⟩ rfl ((([1, 1, 0, 1, 1, 0] : zF)
              ^ (b)) +> l) ((([0, 1] : zF) ^ (b*2)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_9 (b*2) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
      +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l)) (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF)
          +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem return_odd_1 (l : zB) (b : Nat) (d : Nat) :
    (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0] : zF) ^ (b*2+d)) +> default)))) [target_tm]⊢* (S (l) default (b*2) (1) (0)
            (b*2+d)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0], [0, 1, 0, 1, 0]⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l) ((([0, 1, 0] : zF) ^ (b*2+d))
          +> default)) (by norm_cfg) (by norm_cfg)

theorem return_even_1 (l : zB) (b : Nat) (d : Nat) :
    (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (b*2+d)) +> default))))
            [target_tm]⊢* (S (l) default (1+b*2) (1) (0) (1+b*2+d)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left,
      [1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l) ((([0, 1, 0] : zF)
          ^ (b*2+d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem return_last_1 (l : zB) (b : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default))))
            [target_tm]⊢* (S (l) default (2+b*2) (1) (0) (1+b*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B,
      .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l)
          ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)) (by norm_cfg) (by norm_cfg)

theorem pred_odd_1 (l : zB) (b : Nat) :
    (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)))) [target_tm]⊢* (S (l) default (1+b*2)
            (1) (0) (b*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0], [0, 1, 0, 1, 0]⟩ ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l) ((([0, 1, 0, 0, 1, 0] : zF) ^ (b))
          +> default)) (by norm_cfg) (by norm_cfg)

theorem pred_odd_2 (l : zB) (b : Nat) :
    (S (l) default (1) (1+b) (b*2) (0)) [target_tm]⊢* (((([1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2))
        +> (([1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF) ^ (b)) +> (([1] : zF) +> l)))))
            {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b)) +> ((([1, 0] : zF)
          ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l) (([0] : zF) +> ((([1, 0] : zF)
      ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (b*2) (([0, 1, 1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
      ^ (b)) +> l)) (([0] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1] : zF) +> ((([1, 0, 1, 1, 0, 1] : zF)
          ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem pred_even_1 (l : zB) (b : Nat) :
    (((([1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (b*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default))))
            [target_tm]⊢* (S (l) default (3+b*2) (1) (0) (1+b*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left, [1, 0, 1, 0, 1, 0],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (b*2)) +> l)
              ((([0, 1, 0, 0, 1, 0] : zF) ^ (b)) +> default)) (by norm_cfg) (by norm_cfg)

theorem pred_even_2 (l : zB) (b : Nat) :
    (S (l) default (3) (1+b) (b*2) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
        ^ (b*2)) +> (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 1, 0, 1, 1, 0] : zF)
            ^ (b)) +> (([1] : zF) +> l))))) {{B}}> default)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A,
      .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
          +> ((([1, 0] : zF) ^ (b*2)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0] : zF) +> l) (([0] : zF)
      +> ((([1, 0] : zF) ^ (b*2)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (b*2) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l))) (([0, 0, 1] : zF) +> default))
          (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l)))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (b*2) (([1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> (([0] : zF) +> l))) (([1, 0, 1, 0, 1] : zF)
          +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [1, 0, 1, 0, 1]⟩ ⟨B, .left, [1],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b))
              +> (([0] : zF) +> l)) ((([0, 1] : zF) ^ (b*2)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_10 (b) (([1, 0] : zF) +> l) (([0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1] : zF) ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 19 ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
          [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1], [0]⟩ rfl l ((([0, 1, 1, 0, 1, 0] : zF) ^ (b))
              +> (([1] : zF) +> ((([0, 1] : zF) ^ (b*2)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (b) (([0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF) +> l)
      (([0, 1] : zF) +> ((([0, 1] : zF) ^ (b*2)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 1 ⟨A, .right, [0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
      [0, 1]⟩ ⟨B, .right, [1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1],
          [1]⟩ rfl ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l) ((([0, 1] : zF) ^ (b*2)) +> default))
              (by norm_cfg) ?_
  refine step_bridge (sr_9 (b*2) (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
      +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l)) (([1] : zF) +> default)) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (b*2)) +> (([1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1] : zF)
          +> ((([1, 0, 1, 1, 0, 1] : zF) ^ (b)) +> l))) default) (by norm_cfg) (by norm_cfg)

theorem Word_U_1 (l : zB) (r : zB) :
    ((l {{B}}> (([1, 0] : zF) +> r))) [target_tm]⊢* (((([1, 0] : zF) +> l) {{B}}> r)) := by
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [], [1, 0]⟩ ⟨B, .right, [1, 0], []⟩ rfl l r)
      (by norm_cfg) (by norm_cfg)

theorem Word_U_2 (l : zB) (r : zB) :
    (((([1, 0] : zF) +> l) <{{A}} r)) [target_tm]⊢* ((l <{{A}} (([1, 0] : zF) +> r))) := by
  exact step_end (simSteps_star_ex 4 ⟨A, .left, [1, 0], []⟩ ⟨A, .left, [], [1, 0]⟩ rfl l r)
      (by norm_cfg) (by norm_cfg)

theorem Word_V_1 (l : zB) (r : zB) :
    ((l {{B}}> (([1, 0, 0, 1, 1, 0] : zF) +> r))) [target_tm]⊢* (((([1, 1, 0, 1, 1, 0] : zF) +> l)
        {{B}}> r)) := by
  exact step_end (simSteps_star_ex 6 ⟨B, .right, [], [1, 0, 0, 1, 1, 0]⟩ ⟨B, .right,
      [1, 1, 0, 1, 1, 0], []⟩ rfl l r) (by norm_cfg) (by norm_cfg)

theorem Word_V_2 (l : zB) (r : zB) :
    (((([1, 1, 0, 1, 1, 0] : zF) +> l) <{{A}} r))
        [target_tm]⊢* ((l <{{A}} (([1, 0, 1, 0, 0, 1] : zF) +> r))) := by
  exact step_end (simSteps_star_ex 14 ⟨A, .left, [1, 1, 0, 1, 1, 0], []⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 0, 1]⟩ rfl l r) (by norm_cfg) (by norm_cfg)

theorem rootW_step_1 (r : zB) (a : Nat) (w : zF) (c : Nat) (d : Nat) :
    (rootW (r) (a) (w) (c) (2+d)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> default)) {{B}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) := by
  refine step_bridge (simSteps_star_ex 2 ⟨A, .left, [0], [1, 0]⟩ ⟨A, .right, [0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1] : zF) +> default) (([0] : zF)
      +> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
          +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))) (by norm_cfg)
              (by norm_cfg)

theorem rootW_step_3 (l : zB) (r : zB) (c : Nat) (d : Nat) :
    ((l {{B}}> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
        +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))) [target_tm]⊢* ((l <{{A}} (([1, 0, 1, 0] : zF)
            +> ((([1, 0] : zF) ^ (c)) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d))
                +> r)))))) := by
  refine step_bridge (simSteps_star_ex 3 ⟨B, .right, [], [1, 0, 1, 0]⟩ ⟨A, .right, [0, 1, 0],
      [0]⟩ rfl l ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))
          (by norm_cfg) ?_
  refine step_bridge (sr_1 (c) (([0, 1, 0] : zF) +> l) (([0, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF)
      ^ (d)) +> r))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 11 ⟨A, .right, [0, 1, 0], [0, 0, 1, 0]⟩ ⟨C, .left, [0],
      [0, 1, 0, 1, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (c)) +> l) ((([0, 1, 0] : zF) ^ (d)) +> r))
          (by norm_cfg) ?_
  refine step_bridge (sr_12 (c) (([0] : zF) +> l) (([1, 0, 1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
      ^ (d)) +> r))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0, 1, 0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl l ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))
          (by norm_cfg) (by norm_cfg)

theorem rootW_step_4 (r : zB) (a : Nat) (w : zF) (c : Nat) (d : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> default))
        <{{A}} (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([1, 0, 1] : zF)
            +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) [target_tm]⊢* (rootW (r) (2+a) (w) (2+c)
                (d)) := by
  refine step_bridge (simSteps_star_ex 9 ⟨A, .left, [1, 0, 1, 0, 1, 0], []⟩ ⟨C, .left, [0],
      [0, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a)) +> default) (w +> (([1, 0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) ?_
  refine step_bridge (sr_12 (a) (([0] : zF) +> default) (([1, 0, 1, 0] : zF)
      +> (w +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d))
          +> r)))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1, 0, 1, 0]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (w +> (([1, 0, 1, 0, 1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))) (by norm_cfg)
              (by norm_cfg)

theorem crossW_step_1 (l : zB) (r : zB) (a : Nat) (w : zF) (c : Nat) (d : Nat) :
    (crossW (l) (r) (2+a) (w) (c) (2+d)) [target_tm]⊢* (((([0, 1, 1, 0, 1, 1, 0] : zF)
        +> ((([1, 0] : zF) ^ (a)) +> l)) {{F}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
            ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) := by
  exact step_end (simSteps_star_ex 10 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1]⟩ ⟨F, .right,
      [0, 1, 1, 0, 1, 1, 0], []⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) (w +> (([1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))
              (by norm_cfg) (by norm_cfg)

theorem crossW_step_2 (l : zB) (r : zB) :
    (((([0, 1, 1, 0, 1, 1, 0] : zF) +> l) {{F}}> (([1, 0] : zF) +> r)))
        [target_tm]⊢* (((([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> l) {{B}}> r)) := by
  exact step_end (simSteps_star_ex 2 ⟨F, .right, [0, 1, 1, 0, 1, 1, 0], [1, 0]⟩ ⟨B, .right,
      [1, 1, 0, 1, 1, 0, 1, 1, 0], []⟩ rfl l r) (by norm_cfg) (by norm_cfg)

theorem crossW_step_4 (l : zB) (r : zB) (a : Nat) (w : zF) (c : Nat) (d : Nat) :
    (((([1, 1, 0, 1, 1, 0, 1, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a)) +> l))
        <{{A}} (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([1, 0, 1] : zF)
            +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) [target_tm]⊢* (crossW (l) (r) (a)
                (([1, 0, 1, 0, 0, 1] : zF) ++ w) (2+c) (d)) := by
  exact step_end (simSteps_star_ex 19 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1, 0], []⟩ ⟨B, .left, [],
      [1, 0, 1, 1, 0, 1, 0, 0, 1]⟩ rfl ((([1, 0] : zF) ^ (a)) +> l)
          (w +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c)) +> ((([0, 1, 0] : zF) ^ (d))
              +> r))))) (by norm_cfg) (by norm_cfg)

theorem normal_odd_root_1 (a : Nat) (d : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> default))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d))
            +> default)))) [target_tm]⊢* (S default default (2+a*2) (1) (0) (2+a*2+d*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left, [1, 0, 1, 0],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a*2)) +> default)
              ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem normal_odd_root_2 (a : Nat) (d : Nat) :
    (S default default (0) (1+(a+1)) (2+a*2) (d*2)) [target_tm]⊢* (rootW default (2)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+a)) (1+a*2) (1+d*2)) := by
  exact step_end (simSteps_star_ex 21 ⟨B, .left, [0, 0, 0],
      [1, 0, 1, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (a)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> (([0] : zF)
                  +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default)))))) (by norm_cfg) (by norm_cfg)

theorem normal_even_root_1 (a : Nat) (d : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> default))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d))
            +> default)))) [target_tm]⊢* (S default default (2+a*2) (1) (0) (1+a*2+d*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B,
      .left, [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a*2)) +> default)
          ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem normal_even_root_2_d0 (a : Nat) :
    (S default default (2) (a+1) (a*2) (1)) [target_tm]⊢* (rootW default (2)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+a)) (1+a*2) (0)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
          +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (a) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1] : zF) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a*2) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (a)) +> default)) (([0, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0]⟩ ⟨A, .left, [1],
      [1, 0, 1, 0, 1]⟩ rfl ((([0, 1] : zF) ^ (a*2)) +> (([1, 0, 1, 1, 0, 1, 1] : zF)
          +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (a)) +> default))) default) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a*2) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (a)) +> default)) (([1, 0, 1, 0, 1] : zF) +> default)) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1], [1, 0, 1, 0, 1]⟩ ⟨C,
      .left, [1], [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (a))
          +> default) ((([0, 1] : zF) ^ (a*2)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_14 (a) (([1] : zF) +> default) (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1] : zF)
      +> ((([0, 1] : zF) ^ (a*2)) +> default))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 25 ⟨C, .left, [1, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (a)) +> (([1] : zF) +> ((([0, 1] : zF) ^ (a*2)) +> default)))) (by norm_cfg)
                  (by norm_cfg)

theorem normal_even_root_2_dS (a : Nat) (d : Nat) :
    (S default default (2) (a+1) (a*2) (1+(1+d)*2)) [target_tm]⊢* (rootW default (2)
        (([1, 0, 1, 0, 0, 1] : zF) ^ (1+a)) (1+a*2) ((1+d)*2)) := by
  refine step_bridge (simSteps_star_ex 13 ⟨B, .left, [1, 0, 1], [1, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 1, 0, 1, 1, 0, 1, 1], [0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF) ^ (a))
          +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0, 1, 0, 0, 1, 0, 0] : zF)
              +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_0 (a) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> default) (([0] : zF)
      +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0, 1, 0, 0, 1, 0, 0] : zF)
          +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a*2) (([0, 1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (a)) +> default)) (([0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0] : zF) +> ((([1, 0, 0, 1, 0, 0] : zF)
          ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 10 ⟨A, .right, [0, 1], [0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0]⟩ ⟨A,
      .left, [1], [1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0]⟩ rfl ((([0, 1] : zF) ^ (a*2))
          +> (([1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF) ^ (a)) +> default)))
              ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_2 (a*2) (([1, 1, 0, 1, 1, 0, 1, 1] : zF) +> ((([0, 1, 1, 0, 1, 1] : zF)
      ^ (a)) +> default)) (([1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 0, 0] : zF)
          +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default))) (by norm_cfg) ?_
  refine step_bridge (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 1],
      [1, 0, 1, 0, 1, 0, 1, 0]⟩ ⟨C, .left, [1],
          [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0]⟩ rfl ((([0, 1, 1, 0, 1, 1] : zF) ^ (a))
              +> default) ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0] : zF)
                  +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default)))) (by norm_cfg) ?_
  refine step_bridge (sr_14 (a) (([1] : zF) +> default)
      (([1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2))
          +> (([0, 1, 0, 0] : zF) +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default)))))
              (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 25 ⟨C, .left, [1, 0, 0, 0, 0],
      [0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ ⟨A, .left, [],
          [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0]⟩ rfl default ((([0, 1, 1, 0, 1, 0] : zF)
              ^ (a)) +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> (([0, 1, 0, 0] : zF)
                  +> ((([1, 0, 0, 1, 0, 0] : zF) ^ (d)) +> default)))))) (by norm_cfg) (by norm_cfg)

theorem even_left_even_1 (a : Nat) (d : Nat) :
    (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> default))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d))
            +> default)))) [target_tm]⊢* (S default default (1+a*2) (1) (0) (1+a*2+d*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left,
      [1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a*2)) +> default)
          ((([0, 1, 0, 0, 1, 0] : zF) ^ (a+d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem even_left_odd_1 (l : zB) (a : Nat) (m : Nat) :
    (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0] : zF) ^ (a*2+m)) +> default)))) [target_tm]⊢* (S (l) default (1+a*2) (1) (0)
            (a*2+m)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0], [0, 1, 0, 1, 0]⟩ ⟨B, .left, [1, 0],
      [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a*2)) +> l) ((([0, 1, 0] : zF) ^ (a*2+m))
          +> default)) (by norm_cfg) (by norm_cfg)

theorem left_overflow_odd_1 (l : zB) (a : Nat) (d : Nat) :
    (((([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a+d*2)) +> l)) <{{C}} (([0, 1, 0, 1, 0] : zF)
        +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (d)) +> default)))) [target_tm]⊢* (S (l) default (2+a+d*2)
            (1) (0) (d*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0]⟩ ⟨B, .left,
      [1, 0, 1, 0], [1, 0, 1, 1, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a+d*2)) +> l)
          ((([0, 1, 0, 0, 1, 0] : zF) ^ (d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem left_overflow_even_1 (l : zB) (a : Nat) (d : Nat) :
    (((([1, 0, 1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a+d*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (d)) +> default))))
            [target_tm]⊢* (S (l) default (4+a+d*2) (1) (0) (1+d*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left, [1, 0, 1, 0, 1, 0, 1, 0],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a+d*2)) +> l)
              ((([0, 1, 0, 0, 1, 0] : zF) ^ (d)) +> default)) (by norm_cfg) (by norm_cfg)

theorem border_even_1 (l : zB) (a : Nat) :
    (((([1, 0, 1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0, 0, 1, 0] : zF) ^ (a)) +> default))))
            [target_tm]⊢* (S (l) default (3+a*2) (1) (0) (1+a*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0, 1, 0, 1, 0],
      [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left, [1, 0, 1, 0, 1, 0],
          [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (a*2)) +> l)
              ((([0, 1, 0, 0, 1, 0] : zF) ^ (a)) +> default)) (by norm_cfg) (by norm_cfg)

theorem rootW_finish_word0_1 (a : Nat) (w : zF) (c : Nat) :
    (rootW default (a) (w) (c) (0)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> default)) {{B}}> (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> default))))) := by
  refine step_bridge (simSteps_star_ex 2 ⟨A, .left, [0], [1, 0]⟩ ⟨A, .right, [0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (w +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1] : zF) +> default) (([0] : zF) +> (w +> (([1, 0, 1] : zF)
      +> ((([0, 1] : zF) ^ (c)) +> default))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) (w +> (([1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> default)))) (by norm_cfg) (by norm_cfg)

theorem rootW_finish_word_end (l : zB) (n : Nat) :
    ((l {{B}}> ((([1, 0] : zF) ^ (n)) +> default))) [target_tm]⊢* ((((([1, 0] : zF) ^ (n)) +> l)
        {{B}}> default)) := by
  exact step_end (sr_9 (n) l default) (by norm_cfg) (by norm_cfg)

theorem crossW_finish_word0_1 (l : zB) (a : Nat) (w : zF) (c : Nat) :
    (crossW (l) default (2+a) (w) (c) (0)) [target_tm]⊢* (((([0, 1, 1, 0, 1, 1, 0] : zF)
        +> ((([1, 0] : zF) ^ (a)) +> l)) {{F}}> (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> default))))) := by
  exact step_end (simSteps_star_ex 10 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1]⟩ ⟨F, .right,
      [0, 1, 1, 0, 1, 1, 0], []⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) (w +> (([1, 0, 1] : zF)
          +> ((([0, 1] : zF) ^ (c)) +> default)))) (by norm_cfg) (by norm_cfg)

theorem crossW_finish_word1_1 (l : zB) (a : Nat) (w : zF) (c : Nat) :
    (crossW (l) default (2+a) (w) (c) (1)) [target_tm]⊢* (((([0, 1, 1, 0, 1, 1, 0] : zF)
        +> ((([1, 0] : zF) ^ (a)) +> l)) {{F}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
            ^ (c)) +> default))))) := by
  exact step_end (simSteps_star_ex 10 ⟨B, .left, [1, 0, 1, 0], [1, 0, 1]⟩ ⟨F, .right,
      [0, 1, 1, 0, 1, 1, 0], []⟩ rfl ((([1, 0] : zF) ^ (a)) +> l) (w +> (([1, 0, 1, 0, 1, 0] : zF)
          +> ((([1, 0] : zF) ^ (c)) +> default)))) (by norm_cfg) (by norm_cfg)

theorem rootW_finish_word1_1 (a : Nat) (w : zF) (c : Nat) :
    (rootW default (a) (w) (c) (1)) [target_tm]⊢* (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (a))
        +> default)) {{B}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
            +> default))))) := by
  refine step_bridge (simSteps_star_ex 2 ⟨A, .left, [0], [1, 0]⟩ ⟨A, .right, [0, 1],
      [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> default))))) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1] : zF) +> default) (([0] : zF)
      +> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> default))))) (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1], [0]⟩ ⟨B, .right, [1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
          ^ (c)) +> default)))) (by norm_cfg) (by norm_cfg)

theorem final_zero_1 (m : Nat) :
    (final_scan (0) (m)) [target_tm]⊢* (scan_root (1) (m)) := by
  exact step_end (simSteps_star_ex 3 ⟨C, .left, [0], [0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1]⟩ rfl default ((([0, 1, 0] : zF) ^ (m)) +> default)) (by norm_cfg) (by norm_cfg)

theorem final_one_1 (m : Nat) :
    (final_scan (1) (m)) [target_tm]⊢* (scan_root (3) (m)) := by
  exact step_end (simSteps_star_ex 25 ⟨C, .left, [1, 0, 0, 0, 0], [0, 1]⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 1]⟩ rfl default ((([0, 1, 0] : zF) ^ (m)) +> default)) (by norm_cfg)
          (by norm_cfg)

theorem final_even_2 (a : Nat) :
    (scan_root (1+a) (0)) [target_tm]⊢* (section_481 [3+a]) := by
  refine step_bridge (simSteps_star_ex 3 ⟨A, .left, [0], [1, 0, 1]⟩ ⟨B, .right, [1, 0, 1],
      [1]⟩ rfl default ((([0, 1] : zF) ^ (a)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_9 (a) (([1, 0, 1] : zF) +> default) (([1] : zF) +> default)) (by norm_cfg)
      ?_
  exact step_end (simSteps_star_ex 2 ⟨B, .right, [1, 0, 1], [1, 0]⟩ ⟨B, .right, [1, 0, 1, 0, 1],
      []⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) default) (by norm_cfg) (by norm_cfg)

theorem final_odd_2 (a : Nat) :
    (scan_root (1+a) (1)) [target_tm]⊢* (section_481 [4+a]) := by
  refine step_bridge (simSteps_star_ex 6 ⟨A, .left, [0], [1, 0, 1, 0, 1, 0]⟩ ⟨A, .right,
      [0, 1, 0, 1, 0, 1], [0]⟩ rfl default ((([1, 0] : zF) ^ (a)) +> default)) (by norm_cfg) ?_
  refine step_bridge (sr_1 (a) (([0, 1, 0, 1, 0, 1] : zF) +> default) (([0] : zF) +> default))
      (by norm_cfg) ?_
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [0, 1, 0, 1, 0, 1], [0]⟩ ⟨B, .right,
      [1, 0, 1, 0, 1, 0, 1], []⟩ rfl ((([0, 1] : zF) ^ (a)) +> default) default) (by norm_cfg)
          (by norm_cfg)

theorem crossW_one_word_1 (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (crossW default (r) (1) (w) (c) (2+d)) [target_tm]⊢* (((([0, 1, 1, 0, 1] : zF) +> default)
        {{F}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
            +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) := by
  exact step_end (simSteps_star_ex 10 ⟨B, .left, [1, 0], [1, 0, 1]⟩ ⟨F, .right, [0, 1, 1, 0, 1],
      []⟩ rfl default (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c))
          +> (([0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossW_one_word_2 (l : zB) (r : zB) :
    (((([0, 1, 1, 0, 1] : zF) +> l) {{F}}> (([1, 0] : zF) +> r)))
        [target_tm]⊢* (((([1, 1, 0, 1, 1, 0, 1] : zF) +> l) {{B}}> r)) := by
  exact step_end (simSteps_star_ex 2 ⟨F, .right, [0, 1, 1, 0, 1], [1, 0]⟩ ⟨B, .right,
      [1, 1, 0, 1, 1, 0, 1], []⟩ rfl l r) (by norm_cfg) (by norm_cfg)

theorem crossW_one_word_4 (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (((([1, 1, 0, 1, 1, 0, 1] : zF) +> default) <{{A}} (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
        ^ (c)) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))))
            [target_tm]⊢* (rootW (r) (0) (([1, 0, 1, 0, 0, 1] : zF) ++ w) (2+c) (d)) := by
  exact step_end (simSteps_star_ex 18 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1, 0], []⟩ ⟨A, .left, [],
      [1, 0, 1, 0, 1, 0, 0, 1]⟩ rfl default (w +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF)
          ^ (c)) +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem crossW_next_1 (l : zB) (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (crossW (l) (r) (1) (w) (c) (2+d)) [target_tm]⊢* (((([0, 1, 1, 0, 1] : zF) +> l)
        {{F}}> (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
            +> ((([0, 1, 0] : zF) ^ (d)) +> r))))))) := by
  exact step_end (simSteps_star_ex 10 ⟨B, .left, [1, 0], [1, 0, 1]⟩ ⟨F, .right, [0, 1, 1, 0, 1],
      []⟩ rfl l (w +> (([1, 0, 1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (c)) +> (([0, 1, 0] : zF)
          +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))) (by norm_cfg) (by norm_cfg)

theorem crossW_next_4 (l : zB) (r : zB) (w : zF) (c : Nat) (d : Nat) :
    (((([1, 1, 0, 1, 1, 0, 1] : zF) +> l) <{{A}} (w +> (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF)
        ^ (c)) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)))))))
            [target_tm]⊢* (scanW (l) (r) (w) (2+c) (d)) := by
  exact step_end (simSteps_star_ex 15 ⟨A, .left, [1, 1, 0, 1, 1, 0, 1], []⟩ ⟨C, .left, [],
      [0, 1, 0, 1, 0, 0, 1]⟩ rfl l (w +> (([1, 0, 1, 0, 1, 0, 1] : zF) +> ((([0, 1] : zF) ^ (c))
          +> ((([0, 1, 0] : zF) ^ (d)) +> r))))) (by norm_cfg) (by norm_cfg)

theorem scan_pair_1 (l : zB) (r : zB) (n : Nat) (d : Nat) :
    (((([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ (n*2)) +> l))
        <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d+n*2)) +> r))))
            [target_tm]⊢* (S (l) (([1, 0] : zF) +> ((([0, 1, 0] : zF) ^ (d)) +> r)) (1+n*2) (1) (0)
                (n*2)) := by
  exact step_end (simSteps_star_ex 4 ⟨C, .left, [1, 0, 1, 0], [0, 1, 0, 1, 0, 0, 1, 0]⟩ ⟨B, .left,
      [1, 0], [1, 0, 1, 1, 0, 1, 0, 0, 1, 0]⟩ rfl ((([1, 0] : zF) ^ (n*2)) +> l) ((([0, 1, 0] : zF)
          ^ (d+n*2)) +> r)) (by norm_cfg) (by norm_cfg)

theorem init_tm1 :
    ((default {{A}}> default)) [target_tm]⊢* (section_481 [1]) := by
  exact step_end (simSteps_star_ex 1 ⟨A, .right, [], [0]⟩ ⟨B, .right, [1], []⟩ rfl default default)
      (by norm_cfg) (by norm_cfg)

def special (r : zB) : zB :=
  ([1, 0, 0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r

def specialN (n : Nat) (r : zB) : zB :=
  ([1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n)) +> ((([0, 1] : zF) ^ (1 + n * 2))
      +> (([0] : zF) +> r)))

def negativeN (l : zB) (p n d e : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ (p + 2 + n * 2)) +> ((([1, 1, 0] : zF) ^ (p + 4 + n * 2 + e)) +> ((([1, 0] : zF)
      ^ (1 + d * 2)) +> l))) {{B}}> default

def loneN (l : zB) (p n e : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([1, 0] : zF) ^ (p + 2 + n * 2)) +> ((([1, 1, 0] : zF) ^ (p + 3 + n * 2 + e)) +> (([1] : zF)
      +> l))) {{B}}> default

def flow_tail (n : Nat) (r : zB) : zB :=
  ([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ n) +> ((([0, 1] : zF) ^ (2 + n * 2))
      +> (([0] : zF) +> r)))

def short_suffix (n d : Nat) : zB :=
  ([0, 1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n)) +> ((([0, 1] : zF) ^ (1 + n * 2))
      +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default))))

theorem fold2 (a b : Fin 2) (n : Nat) (s : zB) :
    a ::ᵇ (b ::ᵇ ((([a, b] : zF) ^ n) +> s)) = ((([a, b] : zF) ^ (1 + n)) +> s) := by
  rw [pow_add_1, List.cons_append, List.cons_append, List.nil_append, listblank_append_cons,
      listblank_append_cons]

theorem fold3 (a b c : Fin 2) (n : Nat) (s : zB) :
    a ::ᵇ (b ::ᵇ (c ::ᵇ ((([a, b, c] : zF) ^ n) +> s))) = ((([a, b, c] : zF) ^ (1 + n)) +> s) := by
  rw [pow_add_1, List.cons_append, List.cons_append, List.cons_append, List.nil_append,
    listblank_append_cons, listblank_append_cons, listblank_append_cons]

theorem fold6 (a b c d e f : Fin 2) (n : Nat) (s : zB) :
    a ::ᵇ (b ::ᵇ (c ::ᵇ (d ::ᵇ (e ::ᵇ (f ::ᵇ ((([a, b, c, d, e, f] : zF) ^ n) +> s)))))) =
    ((([a, b, c, d, e, f] : zF) ^ (1 + n)) +> s) := by
  rw [pow_add_1, List.cons_append, List.cons_append, List.cons_append, List.cons_append,
    List.cons_append, List.cons_append, List.nil_append,
    listblank_append_cons, listblank_append_cons, listblank_append_cons, listblank_append_cons,
        listblank_append_cons, listblank_append_cons]

theorem cfg_left_congr {q : Fin 6} {l₁ l₂ r₁ r₂ : zB} (hl : l₁ = l₂) (hr : r₁ = r₂) :
    (l₁ <{{q}} r₁) = (l₂ <{{q}} r₂) := by rw [hl, hr]

theorem cfg_right_congr {q : Fin 6} {l₁ l₂ r₁ r₂ : zB} (hl : l₁ = l₂) (hr : r₁ = r₂) :
    (l₁ {{q}}> r₁) = (l₂ {{q}}> r₂) := by rw [hl, hr]

theorem app2_congr {α : Type} {f : Nat → Nat → α} {a₁ a₂ b₁ b₂ : Nat}
    (ha : a₁ = a₂) (hb : b₁ = b₂) : f a₁ b₁ = f a₂ b₂ := by rw [ha, hb]

theorem app3_congr {α : Type} {f : zB → Nat → Nat → α} {l₁ l₂ : zB} {a₁ a₂ b₁ b₂ : Nat}
    (hl : l₁ = l₂) (ha : a₁ = a₂) (hb : b₁ = b₂) : f l₁ a₁ b₁ = f l₂ a₂ b₂ := by rw [hl, ha, hb]

theorem cons_congr {a : Fin 2} {s₁ s₂ : zB} (hs : s₁ = s₂) :
    (a ::ᵇ s₁) = (a ::ᵇ s₂) := by rw [hs]

theorem same_pow_congr {w : zF} {n₁ n₂ : Nat} {s₁ s₂ : zB} (hn : n₁ = n₂) (hs : s₁ = s₂) :
    ((w ^ n₁) +> s₁) = ((w ^ n₂) +> s₂) := by rw [hn, hs]

theorem same_word_congr {w : zF} {s₁ s₂ : zB} (hs : s₁ = s₂) :
    (w +> s₁) = (w +> s₂) := by rw [hs]

theorem pow_zero_left {w : zF} {n : Nat} {s₁ s₂ : zB} (hn : n = 0) (hs : s₁ = s₂) :
    ((w ^ n) +> s₁) = s₂ := by
  rw [hn, list_pow_zero, listblank_append_nil, hs]

theorem pow_zero_right {w : zF} {n : Nat} {s₁ s₂ : zB} (hn : 0 = n) (hs : s₁ = s₂) :
    s₁ = ((w ^ n) +> s₂) := by
  rw [← hn, list_pow_zero, listblank_append_nil, hs]

theorem pow2_succ_left {a b : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : s₁ = ((([a, b] : zF) ^ (n - 1)) +> s₂)) :
    (a ::ᵇ (b ::ᵇ s₁)) = ((([a, b] : zF) ^ n) +> s₂) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold2, hs]

theorem pow2_succ_right {a b : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : ((([a, b] : zF) ^ (n - 1)) +> s₁) = s₂) :
    ((([a, b] : zF) ^ n) +> s₁) = (a ::ᵇ (b ::ᵇ s₂)) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold2, hs]

theorem pow3_succ_left {a b c : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : s₁ = ((([a, b, c] : zF) ^ (n - 1)) +> s₂)) :
    (a ::ᵇ (b ::ᵇ (c ::ᵇ s₁))) = ((([a, b, c] : zF) ^ n) +> s₂) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold3, hs]

theorem pow3_succ_right {a b c : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : ((([a, b, c] : zF) ^ (n - 1)) +> s₁) = s₂) :
    ((([a, b, c] : zF) ^ n) +> s₁) = (a ::ᵇ (b ::ᵇ (c ::ᵇ s₂))) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold3, hs]

theorem pow6_succ_left {a b c d e f : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : s₁ = ((([a, b, c, d, e, f] : zF) ^ (n - 1)) +> s₂)) :
    (a ::ᵇ (b ::ᵇ (c ::ᵇ (d ::ᵇ (e ::ᵇ (f ::ᵇ s₁)))))) = ((([a, b, c, d, e, f] : zF) ^ n)
        +> s₂) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold6, hs]

theorem pow6_succ_right {a b c d e f : Fin 2} {n : Nat} {s₁ s₂ : zB}
    (hn : n ≥ 1) (hs : ((([a, b, c, d, e, f] : zF) ^ (n - 1)) +> s₁) = s₂) :
    ((([a, b, c, d, e, f] : zF) ^ n) +> s₁)
        = (a ::ᵇ (b ::ᵇ (c ::ᵇ (d ::ᵇ (e ::ᵇ (f ::ᵇ s₂)))))) := by
  have h1 : n = 1 + (n - 1) := by omega
  rw [h1, ← fold6, hs]

theorem pow_split_left {w : zF} {n₁ n₂ : Nat} {s₁ s₂ : zB}
    (h : n₁ > n₂) (hs : ((w ^ (n₁ - n₂)) +> s₁) = s₂) :
    ((w ^ n₁) +> s₁) = ((w ^ n₂) +> s₂) := by
  have hn : n₁ = n₂ + (n₁ - n₂) := by omega
  rw [hn, ← pow_merge, hs]

theorem pow_split_right {w : zF} {n₁ n₂ : Nat} {s₁ s₂ : zB}
    (h : n₂ > n₁) (hs : s₁ = ((w ^ (n₂ - n₁)) +> s₂)) :
    ((w ^ n₁) +> s₁) = ((w ^ n₂) +> s₂) := by
  have hn : n₂ = n₁ + (n₂ - n₁) := by omega
  rw [hn, ← pow_merge, hs]

macro "spine_step" : tactic =>
  `(tactic| first
    | rfl
    | apply cons_congr
    | apply same_pow_congr (by omega)
    | apply same_word_congr
    | apply pow_zero_left (by omega)
    | apply pow_zero_right (by omega)
    | apply pow2_succ_left (by omega)
    | apply pow2_succ_right (by omega)
    | apply pow3_succ_left (by omega)
    | apply pow3_succ_right (by omega)
    | apply pow6_succ_left (by omega)
    | apply pow6_succ_right (by omega)
    | apply pow_split_left (by omega)
    | apply pow_split_right (by omega))

macro "solve_spine" : tactic =>
  `(tactic| repeat' spine_step)

macro "solve_cfg_spine" : tactic =>
  `(tactic| (first
    | rfl
    | apply app2_congr (by omega) (by omega)
    | (apply app3_congr ?_ (by omega) (by omega); solve_spine; done)
    | ((first | apply cfg_left_congr | apply cfg_right_congr) <;> (solve_spine; done))))

macro "cfg_eq" : tactic =>
  `(tactic| first
    | rfl
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         S, rootW, crossW, crossZ, rootZ, crossV, rootV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only
           [Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
               Nat.mul_one, Nat.mul_zero, Nat.zero_mul,
         list_pow_zero, list_pow_succ, list_pow_one,
         pow_add_1, pow_add_2, pow_add_3, pow_add_4, pow_add_5,
         pow_add_right_2, pow_add_right_3, pow_add_right_4, pow_add_right_5,
         pow_double3,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         shift2, shift3, shift6,
         shift2_0, shift3_0_1, shift3_0_01, shift6_0_1, shift6_0_01,
         pow_merge, ListBlank.cons_zero_default]
       try ac_rfl
       done)
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         S, rootW, crossW, crossZ, rootZ, crossV, rootV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only [Nat.mul_zero, Nat.zero_mul,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         list_pow_zero,
         pow_double3, pow_merge, fold2, fold3, fold6, ListBlank.cons_zero_default]
       first | done | (solve_cfg_spine; done))
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         S, rootW, crossW, crossZ, rootZ, crossV, rootV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only
           [Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
               Nat.mul_one, Nat.mul_zero, Nat.zero_mul,
         list_pow_zero, list_pow_succ,
         pow_add_1, pow_add_2, pow_add_3, pow_add_4, pow_add_5,
         pow_add_right_2, pow_add_right_3, pow_add_right_4, pow_add_right_5,
         pow_double3,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         shift2, shift3, shift6,
         shift2_0, shift3_0_1, shift3_0_01, shift6_0_1, shift6_0_01,
         pow_merge, ListBlank.cons_zero_default]
       try simp only [fold2, fold3, fold6, pow_merge, ListBlank.cons_zero_default]
       first | done | (solve_cfg_spine; done)))

theorem step_eq {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ = c₂) : c₁ [target_tm]⊢* c₂ := by
  rw [h]

theorem evstep_progress {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [target_tm]⊢* c₂) (hne : c₁ ≠ c₂) :
    c₁ [target_tm]⊢⁺ c₂ := by
  rcases h with ⟨_ | n, hn⟩
  · cases hn; contradiction
  · exact ⟨n + 1, by omega, hn⟩

theorem evstep_progress_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢* c₂) (h₂ : c₂ [target_tm]⊢⁺ c₃) : c₁ [target_tm]⊢⁺ c₃ :=
  ReachesStar.trans_plus h₁ h₂

theorem progress_evstep_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢⁺ c₂) (h₂ : c₂ [target_tm]⊢* c₃) : c₁ [target_tm]⊢⁺ c₃ :=
  ReachesPlus.trans_star h₁ h₂

theorem progress_trans {c₁ c₂ c₃ : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [target_tm]⊢⁺ c₂) (h₂ : c₂ [target_tm]⊢⁺ c₃) : c₁ [target_tm]⊢⁺ c₃ :=
  ReachesPlus.trans h₁ h₂

theorem step_end_plus_eq {c₁ c₁' c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (h : c₁' [target_tm]⊢⁺ c₂') (heq₁ : c₁ = c₁') (heq₂ : c₂' = c₂) :
    c₁ [target_tm]⊢⁺ c₂ := by
  rw [heq₁, ← heq₂]; exact h

theorem S_ne_section (l r : zB) (a b c d : Nat) (xs : List Nat) :
    S l r (1 + a) b c d ≠ section_481 xs := by
  intro h
  rw [S, pow_add_1, List.cons_append, listblank_append_cons, section_481] at h
  have ht := congrArg (fun x => x.tape.head) h
  simp at ht

macro "ne_cfg" : tactic =>
  `(tactic| first
    | apply S_ne_section
    | (intro h; have hq := congrArg Cfg.q h; dsimp
        [final_scan, rootW, crossW, rootZ, crossZ, rootV, crossV, seed, section_481, S] at hq;
            revert hq; decide))

theorem Incs1 (l r : zB) (a b c d n : Nat) :
    (S l r (n * 2 + a) b c (n * 2 + d)) [target_tm]⊢* (S l r a (n + b) (n * 2 + c) d) := by
  induction n generalizing a b c d with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (Inc1 l r (n * 2 + a) b c (n * 2 + d)) (by cfg_eq) ?_
    exact step_end (ih a (1 + b) (2 + c) d) (by cfg_eq) (by cfg_eq)

theorem P_S (b : Nat) (HP : P (1 + b * 2)) : P ((1 + b * 2) + (3 + b * 2)) := by
  intro l
  refine step_bridge (HP ((([1, 0] : zF) ^ (3 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (P_S_1 l b) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 2 1 0 0 b) (by cfg_eq) ?_
  refine step_bridge (P_S_2 l b) (by cfg_eq) ?_
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> l)) (by cfg_eq) ?_
  exact step_end (close_odd l (1 + b) (1 + b * 2)) (by cfg_eq) (by cfg_eq)

theorem P_S' (b : Nat) (HP : P (2 + b * 2)) : P ((2 + b * 2) + (5 + b * 2)) := by
  intro l
  refine step_bridge (HP ((([1, 0] : zF) ^ (5 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (P_S'_1 l b) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 4 1 0 1 b) (by cfg_eq) ?_
  refine step_bridge (P_S'_2 l b) (by cfg_eq) ?_
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (5 + b * 2)) +> l)) (by cfg_eq) ?_
  exact step_end (close_odd l (2 + b) (2 + b * 2)) (by cfg_eq) (by cfg_eq)

theorem return_odd (l : zB) (b d : Nat) (HP : P (1 + b * 2 + d)) :
    ((((([1, 0] : zF) ^ ((1 + b * 2 + d) + (1 + b * 2))) +> l) {{B}}> default)) [target_tm]⊢*
    (l <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (1 + b)) +> ((([1, 0] : zF) ^ (b * 2))
        +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default)))))) := by
  refine step_bridge (HP ((([1, 0] : zF) ^ (1 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (return_odd_1 l b d) (by cfg_eq) ?_
  exact step_end (Incs1 l default 0 1 0 d b) (by cfg_eq) (by cfg_eq)

theorem return_even (l : zB) (b d : Nat) (HP : P (2 + b * 2 + d)) :
    ((((([1, 0] : zF) ^ ((2 + b * 2 + d) + (2 + b * 2))) +> l) {{B}}> default)) [target_tm]⊢*
    (l <{{C}} (([0, 1, 0, 1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + b)) +> ((([0, 1] : zF)
        ^ (1 + b * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default)))))) := by
  refine step_bridge (HP ((([1, 0] : zF) ^ (2 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (return_even_1 l b d) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 1 1 0 (1 + d) b) (by cfg_eq) ?_
  exact step_end (edge1 l (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default)) (1 + b) (b * 2))
      (by cfg_eq) (by cfg_eq)

theorem return_last (l : zB) (b : Nat) (HP : P (2 + b * 2)) :
    ((((([1, 0] : zF) ^ ((2 + b * 2) + (3 + b * 2))) +> l) {{B}}> default)) [target_tm]⊢*
    (l <{{B}} (([1] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (2 + b)) +> ((([1, 0] : zF)
        ^ (1 + b * 2)) +> default)))) := by
  refine step_bridge (HP ((([1, 0] : zF) ^ (3 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (return_last_1 l b) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 2 1 0 1 b) (by cfg_eq) ?_
  exact step_end (edge2 l default (1 + b) (b * 2)) (by cfg_eq) (by cfg_eq)

theorem pred_odd (b : Nat) (HP : P (1 + b * 2)) : PP ((1 + b * 2) + (2 + b * 2)) := by
  intro l
  refine step_bridge (HP ((([1, 0] : zF) ^ (2 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (pred_odd_1 l b) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 1 1 0 0 b) (by cfg_eq) ?_
  refine step_bridge (pred_odd_2 l b) (by cfg_eq) ?_
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> (([1] : zF) +> l))) (by cfg_eq) ?_
  exact step_end (close l (1 + b) (1 + b * 2)) (by cfg_eq) (by cfg_eq)

theorem pred_even (b : Nat) (HP : P (2 + b * 2)) : PP ((2 + b * 2) + (4 + b * 2)) := by
  intro l
  refine step_bridge (HP ((([1, 0] : zF) ^ (4 + b * 2)) +> l)) (by cfg_eq) ?_
  refine step_bridge (pred_even_1 l b) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 3 1 0 1 b) (by cfg_eq) ?_
  refine step_bridge (pred_even_2 l b) (by cfg_eq) ?_
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (4 + b * 2)) +> (([1] : zF) +> l))) (by cfg_eq) ?_
  exact step_end (close l (2 + b) (2 + b * 2)) (by cfg_eq) (by cfg_eq)

def Word (w x y : zF) : Prop :=
  w ++ [1, 0] = [1, 0] ++ x ∧
  (∀ l r : zB, (l {{B}}> (x +> r)) [target_tm]⊢* ((y.reverse +> l) {{B}}> r)) ∧
  (∀ l r : zB, ((y.reverse +> l) <{{A}} r) [target_tm]⊢* (l <{{A}} (w +> r)))

theorem Word_nil : Word [] [] [] :=
  ⟨rfl, fun _ _ => ReachesStar.refl target_tm _, fun _ _ => ReachesStar.refl target_tm _⟩

theorem Word_U : Word [1, 0] [1, 0] [0, 1] :=
  ⟨rfl, Word_U_1, Word_U_2⟩

theorem Word_V : Word [1, 0, 1, 0, 0, 1] [1, 0, 0, 1, 1, 0] [0, 1, 1, 0, 1, 1] :=
  ⟨rfl, Word_V_1, Word_V_2⟩

theorem Word_app (w1 x1 y1 w2 x2 y2 : zF) (h1 : Word w1 x1 y1) (h2 : Word w2 x2 y2) :
    Word (w1 ++ w2) (x1 ++ x2) (y1 ++ y2) := by
  rcases h1 with ⟨e1, r1, l1⟩
  rcases h2 with ⟨e2, r2, l2⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [List.append_assoc, e2, ← List.append_assoc, e1, List.append_assoc]
  · intro l r
    rw [List.reverse_append, listblank_append_right_assoc, listblank_append_right_assoc]
    exact ReachesStar.trans (r1 l (x2 +> r)) (r2 (y1.reverse +> l) r)
  · intro l r
    rw [List.reverse_append, listblank_append_right_assoc, listblank_append_right_assoc]
    exact ReachesStar.trans (l2 (y1.reverse +> l) r) (l1 l (w2 +> r))

theorem Word_pow (w x y : zF) (n : Nat) (h : Word w x y) : Word (w ^ n) (x ^ n) (y ^ n) := by
  induction n with
  | zero => exact Word_nil
  | succ n ih => exact Word_app w x y (w ^ n) (x ^ n) (y ^ n) h ih

theorem word_shift {w x : zF} (h : w ++ [1, 0] = [1, 0] ++ x) (s : zB) :
    w +> (([1, 0] : zF) +> s) = ([1, 0] : zF) +> (x +> s) := by
  rw [← listblank_append_right_assoc, h, listblank_append_right_assoc]

theorem rootW_step (r : zB) (a : Nat) (w x y : zF) (c d : Nat) (hw : Word w x y) :
    (rootW r a w c (2 + d)) [target_tm]⊢* (rootW r (2 + a) w (2 + c) d) := by
  rcases hw with ⟨e, hr, hl⟩
  refine ReachesStar.trans (rootW_step_1 r a w c d) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> (([0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r))))
  refine step_bridge (Word_U_1 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  refine step_bridge (rootW_step_3 _ r c d) (by cfg_eq) ?_
  refine ReachesStar.trans (hl _ _) ?_
  exact step_end (rootW_step_4 r a w c d) (by cfg_eq) (by cfg_eq)

theorem crossW_step (l r : zB) (a : Nat) (w x y : zF) (c d : Nat) (hw : Word w x y) :
    (crossW l r (2 + a) w c (2 + d)) [target_tm]⊢* (crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ++ w)
        (2 + c) d) := by
  rcases hw with ⟨e, hr, hl⟩
  refine ReachesStar.trans (crossW_step_1 l r a w c d) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> (([0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r))))
  refine step_bridge (crossW_step_2 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  refine step_bridge (rootW_step_3 _ r c d) (by cfg_eq) ?_
  refine ReachesStar.trans (hl _ _) ?_
  exact step_end (crossW_step_4 l r a w c d) (by cfg_eq) (by cfg_eq)

theorem rootsW (r : zB) (a : Nat) (w x y : zF) (c d n : Nat) (hw : Word w x y) :
    (rootW r a w c (n * 2 + d)) [target_tm]⊢* (rootW r (n * 2 + a) w (n * 2 + c) d) := by
  induction n generalizing a c d with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (rootW_step r a w x y c (n * 2 + d) hw) (by cfg_eq) ?_
    exact step_end (ih (2 + a) (2 + c) d) (by cfg_eq) (by cfg_eq)

theorem crossesZ (l r : zB) (a b c e n : Nat) :
    (crossZ l r (n * 4 + a) b (3 + c) (n * 2 + e)) [target_tm]⊢* (crossZ l r a (n * 2 + b) (3 + c)
        e) := by
  induction n generalizing a b c e with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (crossZ_step l r (n * 4 + a) b c (n * 2 + e)) (by cfg_eq) ?_
    exact step_end (ih a (2 + b) c e) (by cfg_eq) (by cfg_eq)

theorem crossesV (l r : zB) (a b c e n : Nat) :
    (crossV l r (n * 4 + a) b (3 + c) (n + e)) [target_tm]⊢* (crossV l r a (n * 2 + b) (3 + (n + c))
        e) := by
  induction n generalizing a b c e with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (crossV_step l r (n * 4 + a) b c (n + e)) (by cfg_eq) ?_
    exact step_end (ih a (2 + b) (1 + c) e) (by cfg_eq) (by cfg_eq)

theorem normal_odd_root (a d : Nat) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (3 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    (rootW default 2 (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + a)) (1 + a * 2) (1 + d * 2)) := by
  refine step_bridge (normal_odd_root_1 a d) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 2 1 0 (2 + d * 2) a) (by cfg_eq) ?_
  refine step_bridge (Inc1 default default 0 (a + 1) (a * 2) (d * 2)) (by cfg_eq) ?_
  exact step_end (normal_odd_root_2 a d) (by cfg_eq) (by cfg_eq)

theorem normal_odd (a d : Nat) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (3 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (3 + d * 2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 0] : zF)
        ^ (5 + d * 2)) +> default))) {{B}}> default)) := by
  refine ReachesStar.trans (normal_odd_root a d) ?_
  refine step_bridge (rootsW default 2 _ _ _ (1 + a * 2) 1 d (Word_pow _ _ _ (1 + a) Word_V))
      (by cfg_eq) ?_
  exact step_end (root_end1 (d * 2 + 2) a (d * 2 + (1 + a * 2))) (by cfg_eq) (by cfg_eq)

theorem normal_even_root (a d : Nat) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    (rootW default 2 (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + a)) (1 + a * 2) (d * 2)) := by
  refine step_bridge (normal_even_root_1 a d) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 2 1 0 (1 + d * 2) a) (by cfg_eq) ?_
  rcases d with _ | d
  · exact step_end (normal_even_root_2_d0 a) (by cfg_eq) (by cfg_eq)
  · exact step_end (normal_even_root_2_dS a d) (by cfg_eq) (by cfg_eq)

theorem normal_even (a d : Nat) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + d * 2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 0] : zF)
        ^ (5 + d * 2)) +> default))) {{B}}> default)) := by
  refine ReachesStar.trans (normal_even_root a d) ?_
  refine step_bridge (rootsW default 2 _ _ _ (1 + a * 2) 0 d (Word_pow _ _ _ (1 + a) Word_V))
      (by cfg_eq) ?_
  exact step_end (root_end0 (d * 2 + 2) a (d * 2 + (1 + a * 2))) (by cfg_eq) (by cfg_eq)

theorem even_left_even (a d : Nat) :
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + a * 2 + d * 2)) +> ((([1, 1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 0] : zF)
        ^ (3 + d * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (even_left_even_1 a d) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 1 1 0 (1 + d * 2) a) (by cfg_eq) ?_
  refine step_bridge (even_root a (d * 2)) (by cfg_eq) ?_
  refine step_bridge (rootsW default 0 _ _ _ (1 + a * 2) 0 d (Word_pow _ _ _ (1 + a) Word_V))
      (by cfg_eq) ?_
  exact step_end (root_end0 (d * 2) a (d * 2 + (1 + a * 2))) (by cfg_eq) (by cfg_eq)

theorem even_left_odd (a d : Nat) :
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (1 + a * 2 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + a * 2 + d * 2)) +> ((([1, 1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 0] : zF)
        ^ (1 + d * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (even_left_odd_1 default a (d * 2)) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 1 1 0 (d * 2) a) (by cfg_eq) ?_
  rcases d with _ | d
  · exact step_end (even_end a) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (even_root a (1 + d * 2)) (by cfg_eq) ?_
    refine step_bridge (rootsW default 0 _ _ _ (1 + a * 2) 1 d (Word_pow _ _ _ (1 + a) Word_V))
        (by cfg_eq) ?_
    exact step_end (root_end1 (d * 2) a (d * 2 + (1 + a * 2))) (by cfg_eq) (by cfg_eq)

theorem left_overflow_odd (l : zB) (a d : Nat) :
    ((((([1, 0] : zF) ^ (3 + d * 2 + a)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (1 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + d * 2)) +> ((([1, 1, 0] : zF) ^ (3 + d * 2)) +> ((([1, 0] : zF) ^ a)
        +> l))) {{B}}> default)) := by
  refine step_bridge (left_overflow_odd_1 l a d) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default (2 + a) 1 0 0 d) (by cfg_eq) ?_
  exact step_end (S_exit0 l a d (d * 2)) (by cfg_eq) (by cfg_eq)

theorem left_overflow_even (l : zB) (a d : Nat) :
    ((((([1, 0] : zF) ^ (5 + d * 2 + a)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + d * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + d * 2)) +> ((([1, 1, 0] : zF) ^ (5 + d * 2)) +> ((([1, 0] : zF) ^ a)
        +> l))) {{B}}> default)) := by
  refine step_bridge (left_overflow_even_1 l a d) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default (4 + a) 1 0 1 d) (by cfg_eq) ?_
  exact step_end (S_exit1 l a d (d * 2)) (by cfg_eq) (by cfg_eq)

theorem seed_odd (a b c d : Nat) :
    (seed a b c (1 + d * 2)) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + c * 2 + d * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> ((([1, 0] : zF)
        ^ (4 + a + d * 2)) +> default))) {{B}}> default)) := by
  refine ReachesStar.trans (seed_root a b c (d * 2)) ?_
  refine step_bridge (rootsW default (1 + a) _ _ _ (1 + c * 2) 0 d (Word_pow _ _ _ (1 + b) Word_V))
      (by cfg_eq) ?_
  exact step_end (root_end0 (d * 2 + (1 + a)) b (d * 2 + (1 + c * 2))) (by cfg_eq) (by cfg_eq)

theorem seed_even (a b c d : Nat) :
    (seed a b c (2 + d * 2)) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (3 + c * 2 + d * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> ((([1, 0] : zF)
        ^ (4 + a + d * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (seed_root a b c (1 + d * 2)) (by cfg_eq) ?_
  refine step_bridge (rootsW default (1 + a) _ _ _ (1 + c * 2) 1 d (Word_pow _ _ _ (1 + b) Word_V))
      (by cfg_eq) ?_
  exact step_end (root_end1 (d * 2 + (1 + a)) b (d * 2 + (1 + c * 2))) (by cfg_eq) (by cfg_eq)

theorem border (l : zB) (a : Nat) :
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (1 + a * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + a * 2)) +> (([1] : zF) +> l)))
        {{B}}> default)) := by
  refine step_bridge (even_left_odd_1 l a 0) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 1 1 0 0 a) (by cfg_eq) ?_
  exact step_end (even_exit l a) (by cfg_eq) (by cfg_eq)

theorem bridge4 (l r : zB) (a b c : Nat) :
    (S l (special r) (4 + a) (1 + b) (2 + c) 0) [target_tm]⊢* (crossZ l r a (2 + b) (5 + c) 2) := by
  refine step_bridge (crossW_step l (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) (2 + a) _ _ _ (1 + c)
      0 (Word_pow _ _ _ b Word_V)) (by cfg_eq) ?_
  exact step_end (cross_to_Z l r a (1 + b) c) (by cfg_eq) (by cfg_eq)

theorem bridge8 (l r : zB) (a b c d : Nat) :
    (S l (special ((([1, 0, 0] : zF) ^ d) +> r)) (8 + a) (1 + b) (2 + c) 0)
        [target_tm]⊢* (S l r a (5 + b) (3 + c) d) := by
  refine step_bridge (bridge4 l ((([1, 0, 0] : zF) ^ d) +> r) (4 + a) b c) (by cfg_eq) ?_
  exact step_end (crossZ_step l ((([1, 0, 0] : zF) ^ d) +> r) a (2 + b) (2 + c) 0) (by cfg_eq)
      (by cfg_eq)

theorem S_even_block (l r : zB) (b c d e : Nat) :
    (S ((([1, 1, 0] : zF) ^ (e * 2)) +> l) r 0 b c d) [target_tm]⊢* (S l r 0 (e + b) c d) := by
  exact step_end (even_block l ((([0, 1, 1, 0, 1, 0] : zF) ^ b) +> ((([1, 0] : zF) ^ c)
      +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> r)))) e) (by cfg_eq) (by cfg_eq)

theorem bridgeV (l r : zB) (a b c n : Nat) :
    (S l (specialN (1 + n) r) (4 + a) (1 + b) (2 + c) 0) [target_tm]⊢*
    (crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a (2 + b) (5 + c) n) := by
  refine step_bridge (crossW_step l (([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (1 + n))
      +> ((([0, 1] : zF) ^ (4 + n * 2)) +> (([0] : zF) +> r)))) (2 + a) _ _ _ (1 + c)
          0 (Word_pow _ _ _ b Word_V)) (by cfg_eq) ?_
  exact step_end (cross_to_V l r a (1 + b) c n) (by cfg_eq) (by cfg_eq)

theorem bridges (l r : zB) (a b c d n : Nat) :
    (S l (specialN n ((([1, 0, 0] : zF) ^ d) +> r)) (8 + n * 8 + a) (1 + b) (2 + c) 0) [target_tm]⊢*
    (S l r a (5 + n * 4 + b) (3 + n + c) d) := by
  rcases n with _ | n
  · exact step_end (bridge8 l r a b c d) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (bridgeV l ((([1, 0, 0] : zF) ^ d) +> r) (12 + n * 8 + a) b c n) (by cfg_eq)
        ?_
    refine step_bridge (crossesV l ((([1, 0] : zF) ^ (5 + n * 2)) +> ((([1, 0, 0] : zF) ^ d) +> r))
        (12 + n * 4 + a) (2 + b) (2 + c) 0 n) (by cfg_eq) ?_
    refine step_bridge (crossV_end l ((([1, 0, 0] : zF) ^ d) +> r) (8 + n * 4 + a) (2 + n * 2 + b)
        (2 + n + c) (4 + n * 2)) (by cfg_eq) ?_
    exact step_end (crossesZ l ((([1, 0, 0] : zF) ^ d) +> r) a (4 + n * 2 + b) (3 + n + c)
        0 (2 + n)) (by cfg_eq) (by cfg_eq)

theorem negativeN_first_odd (l : zB) (a n d : Nat) (HP : P (3 + a * 2)) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
        ^ (8 + a * 2 + n * 2 + d * 2)) +> l))) {{B}}> default)) [target_tm]⊢*
    (negativeN l (3 + a * 2) n d 0) := by
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
      ^ (8 + a * 2 + n * 2 + d * 2)) +> l))) (by cfg_eq) ?_
  refine step_bridge (pass_011 ((([1, 0] : zF) ^ (8 + a * 2 + n * 2 + d * 2)) +> l)
      ((([0, 1, 0] : zF) ^ (3 + a * 2)) +> default) (2 + n * 2)) (by cfg_eq) ?_
  exact step_end (left_overflow_odd l (1 + d * 2) (2 + a + n)) (by cfg_eq) (by cfg_eq)

theorem negativeN_first_even (l : zB) (a n d : Nat) (HP : P (2 + a * 2)) :
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
        ^ (8 + a * 2 + n * 2 + d * 2)) +> l))) {{B}}> default)) [target_tm]⊢*
    (negativeN l (2 + a * 2) n d 1) := by
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
      ^ (8 + a * 2 + n * 2 + d * 2)) +> l))) (by cfg_eq) ?_
  refine step_bridge (pass_011 ((([1, 0] : zF) ^ (8 + a * 2 + n * 2 + d * 2)) +> l)
      ((([0, 1, 0] : zF) ^ (2 + a * 2)) +> default) (2 + n * 2)) (by cfg_eq) ?_
  exact step_end (left_overflow_even l (1 + d * 2) (1 + a + n)) (by cfg_eq) (by cfg_eq)

theorem negativeN_entry (l : zB) (p n d e d0 : Nat) (HP : P p) (E : p = 2 + n * 2 + d0) :
    (negativeN l p n d e) [target_tm]⊢*
    (S l (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) (d * 2) 1 0 (p + 3 + n * 2 + e)) := by
  have HP' : P (2 + n * 2 + d0) := E ▸ HP
  refine step_bridge (return_even ((([1, 1, 0] : zF) ^ (p + 4 + n * 2 + e)) +> ((([1, 0] : zF)
      ^ (1 + d * 2)) +> l)) n d0 HP') (by cfg_eq) ?_
  refine step_bridge (pass_011 ((([1, 0] : zF) ^ (1 + d * 2)) +> l) (([0, 1] : zF)
      +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n)) +> ((([0, 1] : zF) ^ (1 + n * 2)) +> (([0] : zF)
          +> ((([1, 0, 0] : zF) ^ d0) +> default))))) (p + 4 + n * 2 + e)) (by cfg_eq) ?_
  exact step_end (into_S l ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n)) +> ((([0, 1] : zF) ^ (1 + n * 2))
      +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d0) +> default)))) (d * 2) (p + 3 + n * 2 + e))
          (by cfg_eq) (by cfg_eq)

theorem negativeN_cross (p n d e d0 b j a : Nat) (HP : P p) (E1 : p = 2 + n * 2 + d0)
    (E2 : p + 3 + n * 2 + e = d * 2 + j * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (j * 2 + 8 + n * 8 + a))
        +> default)) p n d e) [target_tm]⊢*
    (S default default a (5 + n * 4 + b + d + j) (1 + n + d * 2 + j * 2) d0) := by
  refine step_bridge (negativeN_entry ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF)
      ^ (j * 2 + 8 + n * 8 + a)) +> default)) p n d e d0 HP E1) (by cfg_eq) ?_
  refine step_bridge (Incs1 ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF)
      ^ (j * 2 + 8 + n * 8 + a)) +> default)) (specialN n ((([1, 0, 0] : zF) ^ d0) +> default))
          0 1 0 (j * 2) d) (by cfg_eq) ?_
  refine step_bridge (S_even_block ((([1, 0] : zF) ^ (j * 2 + 8 + n * 8 + a)) +> default)
      (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) (1 + d) (d * 2) (j * 2) b) (by cfg_eq) ?_
  refine step_bridge (Incs1 default (specialN n ((([1, 0, 0] : zF) ^ d0) +> default))
      (8 + n * 8 + a) (b + (1 + d)) (d * 2) 0 j) (by cfg_eq) ?_
  exact step_end (bridges default default a (b + d + j) (d * 2 + j * 2 - 2) d0 n) (by cfg_eq)
      (by cfg_eq)

theorem negativeN_bounded_odd (a n d b j r u t : Nat)
    (HP : P (3 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : d * 2 = b + n * 4 + 3 + u)
        (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2) n d 0)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (19 + a * 4 + n * 8 + b * 2))
        +> ((([1, 0] : zF) ^ (1 + u * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (3 + a * 2) n d 0 (1 + r * 2) b j (5 + r * 2 + u * 2) HP
      (by omega) (by omega)) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default (5 + u * 2) (8 + a + n * 5 + b) (7 + a * 2 + n * 3) 1 r)
      (by cfg_eq) ?_
  exact step_end (S_exit1 default (1 + u * 2) (7 + a * 2 + n * 4 + b) (7 + a * 4 + n)) (by cfg_eq)
      (by cfg_eq)

theorem negativeN_bounded_even (a n d b j r u t : Nat)
    (HP : P (2 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : d * 2 = b + n * 4 + 2 + u)
        (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (2 + a * 2) n d 1)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (17 + a * 4 + n * 8 + b * 2))
        +> ((([1, 0] : zF) ^ (1 + u * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (2 + a * 2) n d 1 (r * 2) b j (3 + r * 2 + u * 2) HP
      (by omega) (by omega)) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default (3 + u * 2) (8 + a + n * 5 + b) (7 + a * 2 + n * 3) 0 r)
      (by cfg_eq) ?_
  exact step_end (S_exit0 default (1 + u * 2) (7 + a * 2 + n * 4 + b) (7 + a * 4 + n)) (by cfg_eq)
      (by cfg_eq)

theorem S_root_exit0 (b c v w : Nat) :
    (S default default (1 + v * 2) (1 + b) c (1 + v * 2 + w * 2)) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + c + v * 2 + w * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2 + v * 2))
        +> ((([1, 0] : zF) ^ (3 + w * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (Incs1 default default 1 (1 + b) c (1 + w * 2) v) (by cfg_eq) ?_
  refine step_bridge (S_root1 (b + v) (c + v * 2) (w * 2)) (by cfg_eq) ?_
  refine step_bridge (rootsW default 0 _ _ _ (1 + (c + v * 2)) 0 w (Word_pow _ _ _ (1 + (b + v))
      Word_V)) (by cfg_eq) ?_
  exact step_end (root_end0 (w * 2) (b + v) (1 + (c + v * 2) + w * 2)) (by cfg_eq) (by cfg_eq)

theorem S_root_exit1 (b c v w : Nat) :
    (S default default (1 + v * 2) (1 + b) c (2 + v * 2 + w * 2)) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (3 + c + v * 2 + w * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2 + v * 2))
        +> ((([1, 0] : zF) ^ (3 + w * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (Incs1 default default 1 (1 + b) c (2 + w * 2) v) (by cfg_eq) ?_
  refine step_bridge (S_root1 (b + v) (c + v * 2) (1 + w * 2)) (by cfg_eq) ?_
  refine step_bridge (rootsW default 0 _ _ _ (1 + (c + v * 2)) 1 w (Word_pow _ _ _ (1 + (b + v))
      Word_V)) (by cfg_eq) ?_
  exact step_end (root_end1 (w * 2) (b + v) (1 + (c + v * 2) + w * 2)) (by cfg_eq) (by cfg_eq)

theorem negativeN_positive_odd (a n d b j u v t : Nat)
    (HP : P (3 + a * 2)) (E1 : a = n + u + v) (E2 : a + n + 3 = d + j)
        (E3 : b + n * 4 + 1 = d * 2 + u) (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2) n d 0)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> ((([1, 0] : zF) ^ (3 + u * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (3 + a * 2) n d 0 (1 + v * 2 + u * 2) b j (1 + v * 2) HP
      (by omega) (by omega)) (by cfg_eq) ?_
  exact step_end (S_root_exit0 (7 + a + n * 5 + b) (7 + a * 2 + n * 3) v u) (by cfg_eq) (by cfg_eq)

theorem negativeN_positive_even (a n d b j u v t : Nat)
    (HP : P (2 + a * 2)) (E1 : a = 1 + n + u + v) (E2 : a + n + 3 = d + j)
        (E3 : b + n * 4 = d * 2 + u) (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (2 + a * 2) n d 1)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> ((([1, 0] : zF) ^ (3 + u * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (2 + a * 2) n d 1 (2 + v * 2 + u * 2) b j (1 + v * 2) HP
      (by omega) (by omega)) (by cfg_eq) ?_
  exact step_end (S_root_exit1 (7 + a + n * 5 + b) (7 + a * 2 + n * 3) v u) (by cfg_eq) (by cfg_eq)

theorem border_even (l : zB) (a : Nat) :
    ((((([1, 0] : zF) ^ (4 + a * 2)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + a * 2)) +> default)))) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (4 + a * 2)) +> (([1] : zF) +> l)))
        {{B}}> default)) := by
  refine step_bridge (border_even_1 l a) (by cfg_eq) ?_
  refine step_bridge (Incs1 l default 3 1 0 1 a) (by cfg_eq) ?_
  exact step_end (S_short1 l a (a * 2)) (by cfg_eq) (by cfg_eq)

theorem loneN_first_odd (l : zB) (a n : Nat) (HP : P (3 + a * 2)) :
    ((((([1, 0] : zF) ^ (3 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
        ^ (6 + a * 2 + n * 2)) +> l))) {{B}}> default)) [target_tm]⊢*
    (loneN l (3 + a * 2) n 0) := by
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF) ^ (6 + a * 2 + n * 2))
      +> l))) (by cfg_eq) ?_
  refine step_bridge (pass_011 ((([1, 0] : zF) ^ (6 + a * 2 + n * 2)) +> l) ((([0, 1, 0] : zF)
      ^ (3 + a * 2)) +> default) (2 + n * 2)) (by cfg_eq) ?_
  exact step_end (border l (2 + a + n)) (by cfg_eq) (by cfg_eq)

theorem loneN_first_even (l : zB) (a n : Nat) (HP : P (2 + a * 2)) :
    ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF)
        ^ (6 + a * 2 + n * 2)) +> l))) {{B}}> default)) [target_tm]⊢*
    (loneN l (2 + a * 2) n 1) := by
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ (2 + n * 2)) +> ((([1, 0] : zF) ^ (6 + a * 2 + n * 2))
      +> l))) (by cfg_eq) ?_
  refine step_bridge (pass_011 ((([1, 0] : zF) ^ (6 + a * 2 + n * 2)) +> l) ((([0, 1, 0] : zF)
      ^ (2 + a * 2)) +> default) (2 + n * 2)) (by cfg_eq) ?_
  exact step_end (border_even l (1 + a + n)) (by cfg_eq) (by cfg_eq)

theorem loneN_entry (p n e d0 b t : Nat) (HP : P p) (E : p = 2 + n * 2 + d0) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (2 + t)) +> default)) p n e)
        [target_tm]⊢*
    (S default (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) t (1 + b)
        0 (p + 3 + n * 2 + e)) := by
  have HP' : P (2 + n * 2 + d0) := E ▸ HP
  refine step_bridge (return_even ((([1, 1, 0] : zF) ^ (p + 3 + n * 2 + e)) +> (([1] : zF)
      +> ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (2 + t)) +> default)))) n d0 HP')
          (by cfg_eq) ?_
  refine step_bridge (pass_011 (([1] : zF) +> ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF)
      ^ (2 + t)) +> default))) (([0, 1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n))
          +> ((([0, 1] : zF) ^ (1 + n * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d0)
              +> default))))) (p + 3 + n * 2 + e)) (by cfg_eq) ?_
  refine step_bridge (lone_one b ((([1, 0] : zF) ^ (1 + t)) +> default) ((([0, 1, 0] : zF)
      ^ (p + 3 + n * 2 + e)) +> (([0, 1] : zF) +> ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n))
          +> ((([0, 1] : zF) ^ (1 + n * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d0)
              +> default))))))) (by cfg_eq) ?_
  exact step_end (lone_S default ((([0, 0, 1, 1, 0, 1] : zF) ^ (1 + n)) +> ((([0, 1] : zF)
      ^ (1 + n * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d0) +> default))))
          t b (p + 3 + n * 2 + e)) (by cfg_eq) (by cfg_eq)

theorem loneN_cross (p n e d0 b h a : Nat) (HP : P p) (E1 : p = 2 + n * 2 + d0)
    (E2 : p + 3 + n * 2 + e = h * 2) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (10 + h * 2 + n * 8 + a)) +> default))
        p n e) [target_tm]⊢*
    (S default default a (5 + n * 4 + b + h) (1 + n + h * 2) d0) := by
  refine step_bridge (loneN_entry p n e d0 b (8 + h * 2 + n * 8 + a) HP E1) (by cfg_eq) ?_
  refine step_bridge (Incs1 default (specialN n ((([1, 0, 0] : zF) ^ d0) +> default))
      (8 + n * 8 + a) (1 + b) 0 0 h) (by cfg_eq) ?_
  exact step_end (bridges default default a (b + h) (h * 2 - 2) d0 n) (by cfg_eq) (by cfg_eq)

theorem loneN_odd (a n b v t : Nat)
    (HP : P (3 + a * 2)) (E1 : a = 3 + n * 5 + b + v) (E2 : t + b * 2 = 11 + a * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2) n 0)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (10 + a * 4)) +> ((([1, 0] : zF)
        ^ (9 + n * 8 + b * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (loneN_cross (3 + a * 2) n 0 (1 + v * 2 + (3 + n * 4 + b) * 2) b (a + n + 3)
      (1 + v * 2) HP (by omega) (by omega)) (by cfg_eq) ?_
  exact step_end (S_root_exit0 (7 + a + n * 5 + b) (7 + a * 2 + n * 3) v (3 + n * 4 + b))
      (by cfg_eq) (by cfg_eq)

theorem loneN_even (a n b v t : Nat)
    (HP : P (2 + a * 2)) (E1 : a = 3 + n * 5 + b + v) (E2 : t + b * 2 = 11 + a * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (2 + a * 2) n 1)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (10 + a * 4)) +> ((([1, 0] : zF)
        ^ (7 + n * 8 + b * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (loneN_cross (2 + a * 2) n 1 (2 + v * 2 + (2 + n * 4 + b) * 2) b (a + n + 3)
      (1 + v * 2) HP (by omega) (by omega)) (by cfg_eq) ?_
  exact step_end (S_root_exit1 (7 + a + n * 5 + b) (7 + a * 2 + n * 3) v (2 + n * 4 + b))
      (by cfg_eq) (by cfg_eq)

theorem rootZ_end (r : zB) (a b c d : Nat) :
    (rootZ ((([1, 0, 0] : zF) ^ d) +> r) a b (3 + c) 0) [target_tm]⊢*
    (rootW (([0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (1 + d)) :=
  step_eq (by cfg_eq)

structure Flow (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (R : Nat → Nat → Cfg (Fin 2) (Fin 6))
    (D : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (T : Nat → Nat → Cfg (Fin 2) (Fin 6))
        (n : Nat) : Prop where
  flow_cross : ∀ l a b, (C l (n * 2 + a) b) [target_tm]⊢* (D l a (n + b))
  flow_root : ∀ a b, (R a b) [target_tm]⊢* (T (n * 2 + a) b)
  flow_border : ∀ s v b, s + v + 1 = n → (C default (1 + s * 2) b) [target_tm]⊢* (T (v * 2)
      (1 + s + b))

theorem Flow_id (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (R : Nat → Nat → Cfg (Fin 2) (Fin 6)) :
    Flow C R C R 0 := by
  refine ⟨fun l a b => step_eq (by cfg_eq), fun a b => step_eq (by cfg_eq), fun s v b h => by omega⟩

theorem Flow_trans {C R D T F U} {n m : Nat} (h1 : Flow C R D T n) (h2 : Flow D T F U m) :
    Flow C R F U (n + m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b
    refine step_bridge (h1.flow_cross l (m * 2 + a) b) (by cfg_eq) ?_
    exact step_end (h2.flow_cross l a (n + b)) (by cfg_eq) (by cfg_eq)
  · intro a b
    refine ReachesStar.trans (h1.flow_root a b) ?_
    exact step_end (h2.flow_root (n * 2 + a) b) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    by_cases hle : n ≤ s
    · refine step_bridge (h1.flow_cross default (1 + (s - n) * 2) b) (by cfg_eq) ?_
      exact step_end (h2.flow_border (s - n) v (n + b) (by omega)) (by cfg_eq) (by cfg_eq)
    · refine ReachesStar.trans (h1.flow_border s (n - s - 1) b (by omega)) ?_
      exact step_end (h2.flow_root ((n - s - 1) * 2) (1 + s + b)) (by cfg_eq) (by cfg_eq)

theorem Flow_W (r : zB) (c d : Nat) :
    Flow (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
         (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d)
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b
    exact step_end (crossW_step l r a _ _ _ c d (Word_pow _ _ _ b Word_V)) (by cfg_eq) (by cfg_eq)
  · intro a b
    exact step_end (rootW_step r a _ _ _ c d (Word_pow _ _ _ b Word_V)) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    exact step_end (crossW_one r b c d) (by cfg_eq) (by cfg_eq)

theorem Flow_to_Z (r : zB) (c : Nat) :
    Flow (fun l a b => crossW l (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF)
                         ^ b) (3 + c) 0)
         (fun a b => rootW (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                       (3 + c) 0)
         (fun l a b => crossZ l r a b (5 + c) 2)
         (fun a b => rootZ r a b (5 + c) 2) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b; exact step_end (cross_to_Z l r a b c) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (root_to_Z r a b c) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv; exact step_end (cross_to_Z_one r b c) (by cfg_eq) (by cfg_eq)

theorem Flow_to_V (r : zB) (c n : Nat) :
    Flow (fun l a b => crossW l (([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (1 + n))
                         +> ((([0, 1] : zF) ^ (4 + n * 2)) +> (([0] : zF) +> r))))
                             a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + c) 0)
         (fun a b => rootW (([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (1 + n))
                       +> ((([0, 1] : zF) ^ (4 + n * 2)) +> (([0] : zF) +> r))))
                           a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + c) 0)
         (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (5 + c) n)
         (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (5 + c) n) 1 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b; exact step_end (cross_to_V l r a b c n) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (root_to_V r a b c n) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv; exact step_end (cross_to_V_one r b c n) (by cfg_eq) (by cfg_eq)

theorem Flow_V (r : zB) (c e : Nat) :
    Flow (fun l a b => crossV l r a b (3 + c) (1 + e))
         (fun a b => rootV r a b (3 + c) (1 + e))
         (fun l a b => crossV l r a b (4 + c) e)
         (fun a b => rootV r a b (4 + c) e) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b; exact step_end (crossV_step l r a b c e) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootV_step r a b c e) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    rcases s with _ | _ | s
    · exact step_end (crossV_one r b c e) (by cfg_eq) (by cfg_eq)
    · exact step_end (crossV_three r b c e) (by cfg_eq) (by cfg_eq)
    · omega

theorem Flow_Z (r : zB) (c e : Nat) :
    Flow (fun l a b => crossZ l r a b (3 + c) (2 + e))
         (fun a b => rootZ r a b (3 + c) (2 + e))
         (fun l a b => crossZ l r a b (3 + c) e)
         (fun a b => rootZ r a b (3 + c) e) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b; exact step_end (crossZ_step l r a b c e) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootZ_step r a b c e) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    rcases s with _ | _ | s
    · exact step_end (crossZ_one' r b c e) (by cfg_eq) (by cfg_eq)
    · exact step_end (crossZ_three' r b c e) (by cfg_eq) (by cfg_eq)
    · omega

theorem Flow_V_end (r : zB) (c e : Nat) :
    Flow (fun l a b => crossV l ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
         (fun a b => rootV ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
         (fun l a b => crossZ l r a b (4 + c) e)
         (fun a b => rootZ r a b (4 + c) e) 2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro l a b; exact step_end (crossV_end l r a b c e) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootV_end r a b c e) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    rcases s with _ | _ | s
    · exact step_end (crossVend_one r b c e) (by cfg_eq) (by cfg_eq)
    · exact step_end (crossVend_three r b c e) (by cfg_eq) (by cfg_eq)
    · omega

theorem Flow_eq {C1 R1 D1 T1 C2 R2 D2 T2} {n1 n2 : Nat}
    (h : Flow C1 R1 D1 T1 n1)
    (hC : ∀ l a b, C1 l a b = C2 l a b)
    (hR : ∀ a b, R1 a b = R2 a b)
    (hD : ∀ l a b, D1 l a b = D2 l a b)
    (hT : ∀ a b, T1 a b = T2 a b)
    (hn : n1 = n2) :
    Flow C2 R2 D2 T2 n2 := by
  have eC : C1 = C2 := by funext l a b; exact hC l a b
  have eR : R1 = R2 := by funext a b; exact hR a b
  have eD : D1 = D2 := by funext l a b; exact hD l a b
  have eT : T1 = T2 := by funext a b; exact hT a b
  subst eC; subst eR; subst eD; subst eT; subst hn; exact h

theorem Flow_Vs (r : zB) (c e n : Nat) :
    Flow (fun l a b => crossV l r a b (3 + c) (e + n))
         (fun a b => rootV r a b (3 + c) (e + n))
         (fun l a b => crossV l r a b (3 + c + n) e)
         (fun a b => rootV r a b (3 + c + n) e) (n * 2) := by
  induction n generalizing c e with
  | zero =>
    exact Flow_eq (Flow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by omega)
  | succ n ih =>
    have h1 : Flow (fun l a b => crossV l r a b (3 + c) (e + (n + 1)))
                   (fun a b => rootV r a b (3 + c) (e + (n + 1)))
                   (fun l a b => crossV l r a b (3 + (1 + c)) (e + n))
                   (fun a b => rootV r a b (3 + (1 + c)) (e + n)) 2 :=
      Flow_eq (Flow_V r c (e + n)) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    exact Flow_eq (Flow_trans h1 (ih (1 + c) e)) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem Flow_Zs (r : zB) (c e n : Nat) :
    Flow (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
         (fun a b => rootZ r a b (3 + c) (e + n * 2))
         (fun l a b => crossZ l r a b (3 + c) e)
         (fun a b => rootZ r a b (3 + c) e) (n * 2) := by
  induction n generalizing e with
  | zero =>
    exact Flow_eq (Flow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by omega)
  | succ n ih =>
    have h1 : Flow (fun l a b => crossZ l r a b (3 + c) (e + (n + 1) * 2))
                   (fun a b => rootZ r a b (3 + c) (e + (n + 1) * 2))
                   (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
                   (fun a b => rootZ r a b (3 + c) (e + n * 2)) 2 :=
      Flow_eq (Flow_Z r c (e + n * 2)) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    exact Flow_eq (Flow_trans h1 (ih e)) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by omega)

theorem Flow_tail (r : zB) (c n : Nat) :
    Flow (fun l a b => crossW l (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
         (fun a b => rootW (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
         (fun l a b => crossZ l r a b (5 + c + n) 0)
         (fun a b => rootZ r a b (5 + c + n) 0) (4 + n * 4) := by
  have hw := Flow_W (flow_tail n r) (1 + c) 0
  rcases n with _ | n
  · have h1 : Flow (fun l a b => crossW l (flow_tail 0 r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                   (2 + (1 + c)) 0)
                   (fun a b => rootW (flow_tail 0 r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + (1 + c))
                                 0)
                   (fun l a b => crossZ l r a b (3 + (2 + c)) (2 + 0))
                   (fun a b => rootZ r a b (3 + (2 + c)) (2 + 0)) 1 :=
      Flow_eq (Flow_to_Z r c) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    have h2 := Flow_Z r (2 + c) 0
    exact Flow_eq (Flow_trans hw (Flow_trans h1 h2)) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)
  · have h1 : Flow (fun l a b => crossW l (flow_tail (n + 1) r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                   (2 + (1 + c)) 0)
                   (fun a b => rootW (flow_tail (n + 1) r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                 (2 + (1 + c)) 0)
                   (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c))
                                   (0 + n))
                   (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c)) (0 + n))
                                 1 :=
      Flow_eq (Flow_to_V r c n) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    have h2 := Flow_Vs ((([1, 0] : zF) ^ (5 + n * 2)) +> r) (2 + c) 0 n
    have h3 : Flow (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c) + n)
                                   0)
                   (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c) + n) 0)
                   (fun l a b => crossZ l r a b (3 + (3 + c + n)) (0 + (2 + n) * 2))
                   (fun a b => rootZ r a b (3 + (3 + c + n)) (0 + (2 + n) * 2)) 2 :=
      Flow_eq (Flow_V_end r (2 + c + n) (4 + n * 2)) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    have h4 := Flow_Zs r (3 + c + n) 0 (2 + n)
    exact Flow_eq (Flow_trans hw (Flow_trans h1 (Flow_trans h2 (Flow_trans h3 h4))))
        (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem bridges_root (n s v b c d : Nat) (E : s + v = 3 + n * 4) :
    (S default (specialN n ((([1, 0, 0] : zF) ^ d) +> default)) (1 + s * 2) (1 + b) (2 + c) 0)
        [target_tm]⊢*
    (rootW default (v * 2) (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + s + b)) (2 + c + n) (1 + d)) := by
  refine step_bridge ((Flow_tail ((([1, 0, 0] : zF) ^ d) +> default) c n).flow_border s v b
      (by omega)) (by cfg_eq) ?_
  exact step_end (rootZ_end default (v * 2) (1 + s + b) (2 + c + n) d) (by cfg_eq) (by cfg_eq)

theorem root_tail_entry (n : Nat) (r : zB) (a b c : Nat) :
    (rootW (([0] : zF) +> specialN n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c 1) [target_tm]⊢*
    (rootW (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c 2) :=
  step_eq (by cfg_eq)

theorem S_tail_root (n s v b c j d : Nat) (E1 : 1 <= c + j) (E2 : s + v + 1 = j + 4 + n * 4) :
    (S default (specialN n ((([1, 0, 0] : zF) ^ d) +> default)) (1 + s * 2) (1 + b) (c * 2) (j * 2))
        [target_tm]⊢*
    (rootW default (v * 2) (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b + s)) ((c + j) * 2 + n)
        (1 + d)) := by
  by_cases hle : j ≤ s
  · refine step_bridge (Incs1 default (specialN n ((([1, 0, 0] : zF) ^ d) +> default)) (1 + (s - j)
        * 2) (1 + b) (c * 2) 0 j) (by cfg_eq) ?_
    exact step_end (bridges_root n (s - j) v (b + j) ((c + j) * 2 - 2) d (by omega)) (by cfg_eq)
        (by cfg_eq)
  · refine step_bridge (Incs1 default (specialN n ((([1, 0, 0] : zF) ^ d) +> default)) 1 (1 + b)
        (c * 2) (2 + (j - s - 1) * 2) s) (by cfg_eq) ?_
    refine step_bridge (S_root1' (specialN n ((([1, 0, 0] : zF) ^ d) +> default)) (b + s) ((c + s)
        * 2) (1 + (j - s - 1) * 2)) (by cfg_eq) ?_
    refine step_bridge (rootsW (([0] : zF) +> specialN n ((([1, 0, 0] : zF) ^ d) +> default))
        0 _ _ _ (1 + (c + s) * 2) 1 (j - s - 1) (Word_pow _ _ _ (1 + b + s) Word_V)) (by cfg_eq) ?_
    refine step_bridge (root_tail_entry n ((([1, 0, 0] : zF) ^ d) +> default) ((j - s - 1) * 2)
        (1 + b + s) ((c + j) * 2 - 1)) (by cfg_eq) ?_
    refine step_bridge ((Flow_tail ((([1, 0, 0] : zF) ^ d) +> default) ((c + j) * 2 - 2)
        n).flow_root ((j - s - 1) * 2) (1 + b + s)) (by cfg_eq) ?_
    exact step_end (rootZ_end default (v * 2) (1 + b + s) ((c + j) * 2 + n) d) (by cfg_eq)
        (by cfg_eq)

theorem negativeN_absorb (p n d e d0 b j t : Nat) (HP : P p) (E1 : p = 2 + n * 2 + d0)
    (E2 : p + 3 + n * 2 + e = d * 2 + j * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) p n d e)
        [target_tm]⊢*
    (S default (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) t (1 + b + d) (d * 2)
        (j * 2)) := by
  refine step_bridge (negativeN_entry ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
      +> default)) p n d e d0 HP E1) (by cfg_eq) ?_
  refine step_bridge (Incs1 ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default))
      (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) 0 1 0 (j * 2) d) (by cfg_eq) ?_
  exact step_end (S_even_block ((([1, 0] : zF) ^ t) +> default) (specialN n ((([1, 0, 0] : zF) ^ d0)
      +> default)) (1 + d) (d * 2) (j * 2) b) (by cfg_eq) (by cfg_eq)

theorem negativeN_root (p n d e d0 b j s v : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = d * 2 + j * 2) (E3 : 1 <= d + j)
        (E4 : s + v + 1 = j + 4 + n * 4) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (1 + s * 2)) +> default)) p n d e)
        [target_tm]⊢*
    (rootW default (v * 2) (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b + d + s)) ((d + j) * 2 + n)
        (1 + d0)) := by
  refine step_bridge (negativeN_absorb p n d e d0 b j (1 + s * 2) HP E1 E2) (by cfg_eq) ?_
  exact step_end (S_tail_root n s v (b + d) d j d0 E3 E4) (by cfg_eq) (by cfg_eq)

theorem negativeN_root_odd (a n d b j r s v : Nat)
    (HP : P (3 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : s + b = 6 + a * 2 + d)
        (E4 : s + v + 1 = j + 4 + n * 4) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (1 + s * 2)) +> default))
        (3 + a * 2) n d 0) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> ((([1, 0] : zF) ^ (5 + v * 2 + r * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_root (3 + a * 2) n d 0 (1 + r * 2) b j s v HP (by omega) (by omega)
      (by omega) E4) (by cfg_eq) ?_
  refine step_bridge (rootsW default (v * 2) _ _ _ ((d + j) * 2 + n) 0 (1 + r)
      (Word_pow _ _ _ (1 + b + d + s) Word_V)) (by cfg_eq) ?_
  exact step_end (root_end0 (2 + v * 2 + r * 2) (b + d + s) (2 + (d + j) * 2 + n + r * 2))
      (by cfg_eq) (by cfg_eq)

theorem negativeN_root_even (a n d b j r s v : Nat)
    (HP : P (2 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : s + b = 6 + a * 2 + d)
        (E4 : s + v + 1 = j + 4 + n * 4) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (1 + s * 2)) +> default))
        (2 + a * 2) n d 1) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> ((([1, 0] : zF) ^ (3 + v * 2 + r * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_root (2 + a * 2) n d 1 (r * 2) b j s v HP (by omega) (by omega)
      (by omega) E4) (by cfg_eq) ?_
  refine step_bridge (rootsW default (v * 2) _ _ _ ((d + j) * 2 + n)
      1 r (Word_pow _ _ _ (1 + b + d + s) Word_V)) (by cfg_eq) ?_
  exact step_end (root_end1 (v * 2 + r * 2) (b + d + s) ((d + j) * 2 + n + r * 2)) (by cfg_eq)
      (by cfg_eq)

theorem loneN_root (p n e d0 b h s v : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (E3 : 1 <= h)
        (E4 : s + v + 1 = h + 4 + n * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (3 + s * 2)) +> default)) p n e)
        [target_tm]⊢*
    (rootW default (v * 2) (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b + s)) (h * 2 + n) (1 + d0)) := by
  refine step_bridge (loneN_entry p n e d0 b (1 + s * 2) HP E1) (by cfg_eq) ?_
  exact step_end (S_tail_root n s v b 0 h d0 (by omega) E4) (by cfg_eq) (by cfg_eq)

theorem loneN_root_odd (a n b r s v : Nat)
    (HP : P (3 + a * 2)) (E1 : a = n + r) (E2 : s + b = 4 + a * 2)
        (E3 : s + v + 1 = a + n + 7 + n * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (3 + s * 2)) +> default)) (3 + a * 2)
        n 0) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (10 + a * 4)) +> ((([1, 0] : zF)
        ^ (5 + v * 2 + r * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (loneN_root (3 + a * 2) n 0 (1 + r * 2) b (a + n + 3) s v HP (by omega)
      (by omega) (by omega) (by omega)) (by cfg_eq) ?_
  refine step_bridge (rootsW default (v * 2) _ _ _ ((a + n + 3) * 2 + n) 0 (1 + r)
      (Word_pow _ _ _ (1 + b + s) Word_V)) (by cfg_eq) ?_
  exact step_end (root_end0 (2 + v * 2 + r * 2) (b + s) (2 + (a + n + 3) * 2 + n + r * 2))
      (by cfg_eq) (by cfg_eq)

theorem loneN_root_even (a n b r s v : Nat)
    (HP : P (2 + a * 2)) (E1 : a = n + r) (E2 : s + b = 4 + a * 2)
        (E3 : s + v + 1 = a + n + 7 + n * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (3 + s * 2)) +> default)) (2 + a * 2)
        n 1) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (10 + a * 4)) +> ((([1, 0] : zF)
        ^ (3 + v * 2 + r * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (loneN_root (2 + a * 2) n 1 (r * 2) b (a + n + 3) s v HP (by omega) (by omega)
      (by omega) (by omega)) (by cfg_eq) ?_
  refine step_bridge (rootsW default (v * 2) _ _ _ ((a + n + 3) * 2 + n)
      1 r (Word_pow _ _ _ (1 + b + s) Word_V)) (by cfg_eq) ?_
  exact step_end (root_end1 (v * 2 + r * 2) (b + s) ((a + n + 3) * 2 + n + r * 2)) (by cfg_eq)
      (by cfg_eq)

theorem negativeN_one_odd (a n d b j r t : Nat)
    (HP : P (3 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : b + n * 4 + 2 = d * 2)
        (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2) n d 0)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (9 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> (([1, 0] : zF) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (3 + a * 2) n d 0 (1 + r * 2) b j (3 + r * 2) HP (by omega)
      (by omega)) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 3 (8 + a + n * 5 + b) (7 + a * 2 + n * 3) 1 r)
      (by cfg_eq) ?_
  exact step_end (S_short1 default (7 + a + n * 5 + b + r) (7 + a * 2 + n * 3 + r * 2)) (by cfg_eq)
      (by cfg_eq)

theorem negativeN_one_even (a n d b j r t : Nat)
    (HP : P (2 + a * 2)) (E1 : a = n + r) (E2 : a + n + 3 = d + j) (E3 : b + n * 4 + 1 = d * 2)
        (E4 : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (2 + a * 2) n d 1)
        [target_tm]⊢*
    ((((([1, 0] : zF) ^ (8 + a * 4 + n)) +> ((([1, 1, 0] : zF) ^ (14 + a * 4 + d * 4))
        +> (([1, 0] : zF) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_cross (2 + a * 2) n d 1 (r * 2) b j (1 + r * 2) HP (by omega)
      (by omega)) (by cfg_eq) ?_
  refine step_bridge (Incs1 default default 1 (8 + a + n * 5 + b) (7 + a * 2 + n * 3) 0 r)
      (by cfg_eq) ?_
  exact step_end (S_short0 default (7 + a + n * 5 + b + r) (7 + a * 2 + n * 3 + r * 2)) (by cfg_eq)
      (by cfg_eq)

theorem crossW_block (l r : zB) (b_blk b c d : Nat) :
    (crossW ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> l) r 0 (([1, 0, 1, 0, 0, 1] : zF) ^ b) c d)
        [target_tm]⊢*
    (crossW l r 0 (([1, 0, 1, 0, 0, 1] : zF) ^ (b_blk + b)) c d) := by
  exact step_end (even_block l (([0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b) +> ((([1, 0] : zF)
      ^ c) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r))))) b_blk) (by cfg_eq) (by cfg_eq)

theorem crossV_block (l r : zB) (b_blk b c e : Nat) :
    (crossV ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> l) r 0 b c e) [target_tm]⊢*
    (crossV l r 0 (b_blk + b) c e) := by
  exact step_end (even_block l (([0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b) +> ((([1, 0] : zF)
      ^ c) +> (([0, 1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ e) +> r))))) b_blk)
          (by cfg_eq) (by cfg_eq)

theorem crossZ_block (l r : zB) (b_blk b c e : Nat) :
    (crossZ ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> l) r 0 b c e) [target_tm]⊢*
    (crossZ l r 0 (b_blk + b) c e) := by
  exact step_end (even_block l (([0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ b) +> ((([1, 0] : zF)
      ^ c) +> (([0] : zF) +> ((([1, 0] : zF) ^ e) +> r))))) b_blk) (by cfg_eq) (by cfg_eq)

theorem crossW_absorb (l r : zB) (a b_blk b c d : Nat) :
    (crossW ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a) +> l))
        r 0 (([1, 0, 1, 0, 0, 1] : zF) ^ b) c d) [target_tm]⊢*
    (crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ (b_blk + b)) c d) := by
  exact step_end (crossW_block ((([1, 0] : zF) ^ a) +> l) r b_blk b c d) (by cfg_eq) (by cfg_eq)

theorem crossV_absorb (l r : zB) (a b_blk b c e : Nat) :
    (crossV ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a) +> l)) r 0 b c e)
        [target_tm]⊢*
    (crossV l r a (b_blk + b) c e) := by
  exact step_end (crossV_block ((([1, 0] : zF) ^ a) +> l) r b_blk b c e) (by cfg_eq) (by cfg_eq)

theorem crossZ_absorb (l r : zB) (a b_blk b c e : Nat) :
    (crossZ ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a) +> l)) r 0 b c e)
        [target_tm]⊢*
    (crossZ l r a (b_blk + b) c e) := by
  exact step_end (crossZ_block ((([1, 0] : zF) ^ a) +> l) r b_blk b c e) (by cfg_eq) (by cfg_eq)

structure BlockFlow (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (R : Nat → Nat → Cfg (Fin 2) (Fin 6))
    (D : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (T : Nat → Nat → Cfg (Fin 2) (Fin 6))
        (n : Nat) : Prop where
  block_flow : Flow C R D T n
  block_cross : ∀ l a b_blk b s v, s + v + 1 = n →
    (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (2 + v * 2 + a)) +> l)) (s * 2) b)
        [target_tm]⊢*
    (D l a (n + b_blk + b))
  block_border : ∀ b_blk b s t v, s + t + v + 1 = n →
    (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (1 + t * 2)) +> default)) (s * 2) b)
        [target_tm]⊢*
    (T (v * 2) (1 + s + t + b_blk + b))

theorem BlockFlow_id (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (R : Nat → Nat → Cfg (Fin 2)
    (Fin 6)) :
    BlockFlow C R C R 0 := by
  refine ⟨Flow_id C R, fun l a b_blk b s v h => by omega, fun b_blk b s t v h => by omega⟩

theorem BlockFlow_eq {C1 R1 D1 T1 C2 R2 D2 T2} {n1 n2 : Nat}
    (h : BlockFlow C1 R1 D1 T1 n1)
    (hC : ∀ l a b, C1 l a b = C2 l a b)
    (hR : ∀ a b, R1 a b = R2 a b)
    (hD : ∀ l a b, D1 l a b = D2 l a b)
    (hT : ∀ a b, T1 a b = T2 a b)
    (hn : n1 = n2) :
    BlockFlow C2 R2 D2 T2 n2 := by
  have eC : C1 = C2 := by funext l a b; exact hC l a b
  have eR : R1 = R2 := by funext a b; exact hR a b
  have eD : D1 = D2 := by funext l a b; exact hD l a b
  have eT : T1 = T2 := by funext a b; exact hT a b
  subst eC; subst eR; subst eD; subst eT; subst hn; exact h

theorem BlockFlow_trans {C R D T F U} {n m : Nat} (h1 : BlockFlow C R D T n)
    (h2 : BlockFlow D T F U m) :
    BlockFlow C R F U (n + m) := by
  refine ⟨Flow_trans h1.block_flow h2.block_flow, ?_, ?_⟩
  · intro l a b_blk b s v E
    by_cases hle : n ≤ s
    · refine step_bridge (h1.block_flow.flow_cross ((([1, 1, 0] : zF) ^ (b_blk * 2))
          +> ((([1, 0] : zF) ^ (2 + v * 2 + a)) +> l)) ((s - n) * 2) b) (by cfg_eq) ?_
      exact step_end (h2.block_cross l a b_blk (n + b) (s - n) v (by omega)) (by cfg_eq) (by cfg_eq)
    · refine step_bridge (h1.block_cross l (m * 2 + a) b_blk b s (n - s - 1) (by omega)) (by cfg_eq)
          ?_
      exact step_end (h2.block_flow.flow_cross l a (n + b_blk + b)) (by cfg_eq) (by cfg_eq)
  · intro b_blk b s t v E
    by_cases hle : n ≤ s
    · refine step_bridge (h1.block_flow.flow_cross ((([1, 1, 0] : zF) ^ (b_blk * 2))
          +> ((([1, 0] : zF) ^ (1 + t * 2)) +> default)) ((s - n) * 2) b) (by cfg_eq) ?_
      exact step_end (h2.block_border b_blk (n + b) (s - n) t v (by omega)) (by cfg_eq) (by cfg_eq)
    · by_cases hle2 : n ≤ s + t
      · refine step_bridge (h1.block_cross default (1 + (s + t - n) * 2) b_blk b s (n - s - 1)
            (by omega)) (by cfg_eq) ?_
        exact step_end (h2.block_flow.flow_border (s + t - n) v (n + b_blk + b) (by omega))
            (by cfg_eq) (by cfg_eq)
      · refine ReachesStar.trans (h1.block_border b_blk b s t (n - s - t - 1) (by omega)) ?_
        exact step_end (h2.block_flow.flow_root ((n - s - t - 1) * 2) (1 + s + t + b_blk + b))
            (by cfg_eq) (by cfg_eq)

theorem BlockFlow_one {C R D T} (h : Flow C R D T 1)
    (hblock : ∀ l a b_blk b, (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a) +> l))
        0 b) [target_tm]⊢* (C l a (b_blk + b))) :
    BlockFlow C R D T 1 := by
  refine ⟨h, ?_, ?_⟩
  · intro l a b_blk b s v E
    have hs : s = 0 := by omega
    have hv : v = 0 := by omega
    subst hs; subst hv
    refine ReachesStar.trans (hblock l (2 + 0 * 2 + a) b_blk b) ?_
    have hfc := h.flow_cross l a (b_blk + b)
    have heq1 : C l (2 + 0 * 2 + a) (b_blk + b) = C l (1 * 2 + a) (b_blk + b) := rfl
    have heq2 : D l a (1 + (b_blk + b)) = D l a (1 + b_blk + b) := by congr 1; omega
    exact step_end hfc heq1 heq2
  · intro b_blk b s t v E
    have hs : s = 0 := by omega
    have ht : t = 0 := by omega
    have hv : v = 0 := by omega
    subst hs; subst ht; subst hv
    refine ReachesStar.trans (hblock default (1 + 0 * 2) b_blk b) ?_
    have hfb := h.flow_border 0 0 (b_blk + b) rfl
    have heq2 : T (0 * 2) (1 + 0 + (b_blk + b)) = T (0 * 2) (1 + 0 + 0 + b_blk + b) :=
        by congr 1; omega
    exact step_end hfb rfl heq2

theorem BlockFlow_two {C R D T} (h : Flow C R D T 2)
    (hblock : ∀ l a b_blk b, (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a) +> l))
        0 b) [target_tm]⊢* (C l a (b_blk + b)))
    (hc : ∀ l a b_blk b, (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (2 + a)) +> l))
        2 b) [target_tm]⊢* (D l a (2 + b_blk + b)))
    (hb : ∀ b_blk b, (C ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> (([1, 0] : zF) +> default)) 2 b)
        [target_tm]⊢* (T 0 (2 + b_blk + b))) :
    BlockFlow C R D T 2 := by
  refine ⟨h, ?_, ?_⟩
  · intro l a b_blk b s v E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv
      refine ReachesStar.trans (hblock l (2 + 1 * 2 + a) b_blk b) ?_
      have hfc := h.flow_cross l a (b_blk + b)
      exact step_end hfc (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      exact hc l a b_blk b
    · omega
  · intro b_blk b s t v E
    rcases s with _ | _ | s
    · refine ReachesStar.trans (hblock default (1 + t * 2) b_blk b) ?_
      have hfb := h.flow_border t v (b_blk + b) (by omega)
      exact step_end hfb rfl (by cfg_eq)
    · have ht : t = 0 := by omega
      have hv : v = 0 := by omega
      subst ht; subst hv
      have h1 := hb b_blk b
      exact step_end h1 (by cfg_eq) (by cfg_eq)
    · omega

theorem BlockFlow_W (r : zB) (c d : Nat) :
    BlockFlow (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
              (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
              (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d)
              (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d) 1 :=
  BlockFlow_one (Flow_W r c d) (fun l a b_blk b => crossW_absorb l r a b_blk b c (2 + d))

theorem BlockFlow_to_Z (r : zB) (c : Nat) :
    BlockFlow (fun l a b => crossW l (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r)
                              a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + c) 0)
              (fun a b => rootW (([0, 1, 1, 0, 1, 0, 1, 0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF)
                            ^ b) (3 + c) 0)
              (fun l a b => crossZ l r a b (5 + c) 2)
              (fun a b => rootZ r a b (5 + c) 2) 1 :=
  BlockFlow_one (Flow_to_Z r c) (fun l a b_blk b => crossW_absorb l (([0, 1, 1, 0, 1, 0, 1, 0] : zF)
      +> r) a b_blk b (3 + c) 0)

theorem BlockFlow_to_V (r : zB) (c n : Nat) :
    BlockFlow (fun l a b => crossW l (([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (1 + n))
                              +> ((([0, 1] : zF) ^ (4 + n * 2)) +> (([0] : zF) +> r))))
                                  a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + c) 0)
              (fun a b => rootW (([0, 1, 1] : zF) +> ((([0, 1, 0, 0, 1, 1] : zF) ^ (1 + n))
                            +> ((([0, 1] : zF) ^ (4 + n * 2)) +> (([0] : zF) +> r))))
                                a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + c) 0)
              (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (5 + c) n)
              (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (5 + c) n) 1 :=
  BlockFlow_one (Flow_to_V r c n) (fun l a b_blk b => crossW_absorb l _ a b_blk b (3 + c) 0)

theorem BlockFlow_V (r : zB) (c e : Nat) :
    BlockFlow (fun l a b => crossV l r a b (3 + c) (1 + e))
              (fun a b => rootV r a b (3 + c) (1 + e))
              (fun l a b => crossV l r a b (4 + c) e)
              (fun a b => rootV r a b (4 + c) e) 2 :=
  BlockFlow_two (Flow_V r c e)
    (fun l a b_blk b => crossV_absorb l r a b_blk b (3 + c) (1 + e))
    (fun l a b_blk b => step_end (crossV_step_block l r a b_blk b c e) (by cfg_eq) (by cfg_eq))
    (fun b_blk b => step_end (crossV_step_block_root r b_blk b c e) (by cfg_eq) (by cfg_eq))

theorem BlockFlow_Z (r : zB) (c e : Nat) :
    BlockFlow (fun l a b => crossZ l r a b (3 + c) (2 + e))
              (fun a b => rootZ r a b (3 + c) (2 + e))
              (fun l a b => crossZ l r a b (3 + c) e)
              (fun a b => rootZ r a b (3 + c) e) 2 :=
  BlockFlow_two (Flow_Z r c e)
    (fun l a b_blk b => crossZ_absorb l r a b_blk b (3 + c) (2 + e))
    (fun l a b_blk b => step_end (crossZ_step_block l r a b_blk b c e) (by cfg_eq) (by cfg_eq))
    (fun b_blk b => step_end (crossZ_step_block_root r b_blk b c e) (by cfg_eq) (by cfg_eq))

theorem BlockFlow_V_end (r : zB) (c e : Nat) :
    BlockFlow (fun l a b => crossV l ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
              (fun a b => rootV ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
              (fun l a b => crossZ l r a b (4 + c) e)
              (fun a b => rootZ r a b (4 + c) e) 2 :=
  BlockFlow_two (Flow_V_end r c e)
    (fun l a b_blk b => crossV_absorb l ((([1, 0] : zF) ^ (1 + e)) +> r) a b_blk b (3 + c) 0)
    (fun l a b_blk b => step_end (crossVend_block l r a b_blk b c e) (by cfg_eq) (by cfg_eq))
    (fun b_blk b => step_end (crossVend_block_root r b_blk b c e) (by cfg_eq) (by cfg_eq))

theorem BlockFlow_Vs (r : zB) (c e n : Nat) :
    BlockFlow (fun l a b => crossV l r a b (3 + c) (e + n))
              (fun a b => rootV r a b (3 + c) (e + n))
              (fun l a b => crossV l r a b (3 + c + n) e)
              (fun a b => rootV r a b (3 + c + n) e) (n * 2) := by
  induction n generalizing c e with
  | zero =>
    exact BlockFlow_eq (BlockFlow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)
  | succ n ih =>
    have h1 : BlockFlow (fun l a b => crossV l r a b (3 + c) (e + (n + 1)))
                        (fun a b => rootV r a b (3 + c) (e + (n + 1)))
                        (fun l a b => crossV l r a b (3 + (1 + c)) (e + n))
                        (fun a b => rootV r a b (3 + (1 + c)) (e + n)) 2 :=
      BlockFlow_eq (BlockFlow_V r c (e + n)) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    exact BlockFlow_eq (BlockFlow_trans h1 (ih (1 + c) e)) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem BlockFlow_Zs (r : zB) (c e n : Nat) :
    BlockFlow (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
              (fun a b => rootZ r a b (3 + c) (e + n * 2))
              (fun l a b => crossZ l r a b (3 + c) e)
              (fun a b => rootZ r a b (3 + c) e) (n * 2) := by
  induction n generalizing e with
  | zero =>
    exact BlockFlow_eq (BlockFlow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)
  | succ n ih =>
    have h1 : BlockFlow (fun l a b => crossZ l r a b (3 + c) (e + (n + 1) * 2))
                        (fun a b => rootZ r a b (3 + c) (e + (n + 1) * 2))
                        (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
                        (fun a b => rootZ r a b (3 + c) (e + n * 2)) 2 :=
      BlockFlow_eq (BlockFlow_Z r c (e + n * 2)) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    exact BlockFlow_eq (BlockFlow_trans h1 (ih e)) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem BlockFlow_tail (r : zB) (c n : Nat) :
    BlockFlow (fun l a b => crossW l (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
              (fun a b => rootW (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
              (fun l a b => crossZ l r a b (5 + c + n) 0)
              (fun a b => rootZ r a b (5 + c + n) 0) (4 + n * 4) := by
  have hw := BlockFlow_W (flow_tail n r) (1 + c) 0
  rcases n with _ | n
  · have h1 : BlockFlow (fun l a b => crossW l (flow_tail 0 r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                        (2 + (1 + c)) 0)
                        (fun a b => rootW (flow_tail 0 r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                      (2 + (1 + c)) 0)
                        (fun l a b => crossZ l r a b (3 + (2 + c)) (2 + 0))
                        (fun a b => rootZ r a b (3 + (2 + c)) (2 + 0)) 1 :=
      BlockFlow_eq (BlockFlow_to_Z r c) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    have h2 := BlockFlow_Z r (2 + c) 0
    exact BlockFlow_eq (BlockFlow_trans hw (BlockFlow_trans h1 h2)) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) (by omega)
  · have h1 : BlockFlow (fun l a b => crossW l (flow_tail (n + 1) r) a (([1, 0, 1, 0, 0, 1] : zF)
                                        ^ b) (2 + (1 + c)) 0)
                        (fun a b => rootW (flow_tail (n + 1) r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                      (2 + (1 + c)) 0)
                        (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r)
                                        a b (3 + (2 + c)) (0 + n))
                        (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c))
                                      (0 + n)) 1 :=
      BlockFlow_eq (BlockFlow_to_V r c n) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    have h2 := BlockFlow_Vs ((([1, 0] : zF) ^ (5 + n * 2)) +> r) (2 + c) 0 n
    have h3 : BlockFlow (fun l a b => crossV l ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c)
                                        + n) 0)
                        (fun a b => rootV ((([1, 0] : zF) ^ (5 + n * 2)) +> r) a b (3 + (2 + c) + n)
                                      0)
                        (fun l a b => crossZ l r a b (3 + (3 + c + n)) (0 + (2 + n) * 2))
                        (fun a b => rootZ r a b (3 + (3 + c + n)) (0 + (2 + n) * 2)) 2 :=
      BlockFlow_eq (BlockFlow_V_end r (2 + c + n) (4 + n * 2)) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) rfl
    have h4 := BlockFlow_Zs r (3 + c + n) 0 (2 + n)
    exact BlockFlow_eq (BlockFlow_trans hw (BlockFlow_trans h1 (BlockFlow_trans h2 (BlockFlow_trans
        h3 h4)))) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
            (by omega)

theorem crossW_finish (l : zB) (a b c e : Nat) (he : e ≤ 1) :
    (crossW l default (2 + a) (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> ((([1, 0] : zF) ^ a)
        +> l))) {{B}}> default)) := by
  rcases e with _ | _ | e
  · exact step_end (crossW_finish0 l a b c) (by cfg_eq) (by cfg_eq)
  · exact step_end (crossW_finish1 l a b c) (by cfg_eq) (by cfg_eq)
  · omega

theorem crossW_short (b c e : Nat) (he : e ≤ 1) :
    (crossW default default 1 (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> (([1, 0] : zF)
        +> default))) {{B}}> default)) := by
  rcases e with _ | _ | e
  · exact step_end (crossW_short0 default b c) (by cfg_eq) (by cfg_eq)
  · exact step_end (crossW_short1 default b c) (by cfg_eq) (by cfg_eq)
  · omega

theorem rootW_finish (a b c e : Nat) (he : e ≤ 1) :
    (rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b)) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> ((([1, 0] : zF)
        ^ (3 + a)) +> default))) {{B}}> default)) := by
  rcases e with _ | _ | e
  · exact step_end (root_end0 a b c) (by cfg_eq) (by cfg_eq)
  · exact step_end (root_end1 a b c) (by cfg_eq) (by cfg_eq)
  · omega

theorem crossZ_end (r : zB) (a b c d : Nat) (l : zB) :
    (crossZ l ((([1, 0, 0] : zF) ^ d) +> r) a b (3 + c) 0) [target_tm]⊢*
    (crossW l (([0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (1 + d)) :=
  step_eq (by cfg_eq)

theorem BlockFlow_Z_end (r : zB) (c d : Nat) :
    BlockFlow (fun l a b => crossZ l ((([1, 0, 0] : zF) ^ d) +> r) a b (3 + c) 0)
              (fun a b => rootZ ((([1, 0, 0] : zF) ^ d) +> r) a b (3 + c) 0)
              (fun l a b => crossW l (([0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (1 + d))
              (fun a b => rootW (([0] : zF) +> r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (1 + d))
                            0 := by
  refine ⟨⟨?_, ?_, ?_⟩, fun l a b_blk b s v h => by omega, fun b_blk b s t v h => by omega⟩
  · intro l a b; exact step_end (crossZ_end r a b c d l) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootZ_end r a b c d) (by cfg_eq) (by cfg_eq)
  · intro s v b h; omega

theorem BlockFlow_Ws (r : zB) (c e n : Nat) :
    BlockFlow (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (e + n * 2))
              (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (e + n * 2))
              (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (c + n * 2) e)
              (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (c + n * 2) e) n := by
  induction n generalizing c with
  | zero =>
    exact BlockFlow_eq (BlockFlow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) rfl
  | succ n ih =>
    have h1 : BlockFlow (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (e + (n + 1)
                                        * 2))
                        (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (e + (n + 1) * 2))
                        (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c)
                                        (e + n * 2))
                        (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) (e + n * 2))
                                      1 :=
      BlockFlow_eq (BlockFlow_W r c (e + n * 2)) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    exact BlockFlow_eq (BlockFlow_trans h1 (ih (2 + c))) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem BlockFlow_whole (c n d q e : Nat) (E : 1 + d = e + q * 2) :
    BlockFlow (fun l a b => crossW l (flow_tail n ((([1, 0, 0] : zF) ^ d) +> default))
                              a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
              (fun a b => rootW (flow_tail n ((([1, 0, 0] : zF) ^ d) +> default))
                            a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2)
              (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c + n + q * 2)
                              e)
              (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c + n + q * 2) e)
                            (4 + n * 4 + q) := by
  have h1 := BlockFlow_tail ((([1, 0, 0] : zF) ^ d) +> default) c n
  have h2 : BlockFlow (fun l a b => crossZ l ((([1, 0, 0] : zF) ^ d) +> default) a b (5 + c + n) 0)
                      (fun a b => rootZ ((([1, 0, 0] : zF) ^ d) +> default) a b (5 + c + n) 0)
                      (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c + n)
                                      (e + q * 2))
                      (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c + n)
                                    (e + q * 2)) 0 :=
    BlockFlow_eq (BlockFlow_Z_end default (2 + c + n) d) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) rfl
  have h3 := BlockFlow_Ws default (2 + c + n) e q
  exact BlockFlow_eq (BlockFlow_trans h1 (BlockFlow_trans h2 h3)) (by intros; cfg_eq)
      (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem S_tail_entry (l r : zB) (a b c n : Nat) :
    (S l (specialN n r) a (1 + b) (2 + c) 0) [target_tm]⊢*
    (crossW l (flow_tail n r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) 2) :=
  step_eq (by cfg_eq)

theorem negativeN_large_start (l : zB) (p n e h k d0 : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (Hh : 1 ≤ h) :
    (negativeN l p n (h + k) e) [target_tm]⊢*
    (crossW l (flow_tail n ((([1, 0, 0] : zF) ^ d0) +> default)) (k * 2) (([1, 0, 1, 0, 0, 1] : zF)
        ^ h) (h * 2 - 1) 2) := by
  refine step_bridge (negativeN_entry l p n (h + k) e d0 HP E1) (by cfg_eq) ?_
  refine step_bridge (Incs1 l (specialN n ((([1, 0, 0] : zF) ^ d0) +> default)) (k * 2) 1 0 0 h)
      (by cfg_eq) ?_
  exact step_end (S_tail_entry l ((([1, 0, 0] : zF) ^ d0) +> default) (k * 2) h (h * 2 - 2) n)
      (by cfg_eq) (by cfg_eq)

theorem negativeN_large_cross (l : zB) (p n e h k d0 q M b_blk v a : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (Hh : 1 ≤ h)
    (E3 : 1 + d0 = e + q * 2) (EM : M = 4 + n * 4 + q) (EK : k + v = M) :
    (negativeN ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (v * 2 + a)) +> l))
        p n (h + k) e) [target_tm]⊢*
    (crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ (M + b_blk + h)) (h * 2 + n + q * 2) e) := by
  refine step_bridge (negativeN_large_start ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF)
      ^ (v * 2 + a)) +> l)) p n e h k d0 HP E1 E2 Hh) (by cfg_eq) ?_
  rcases v with _ | v
  · refine step_bridge ((BlockFlow_whole (h * 2 - 2)
        n d0 q e E3).block_flow.flow_cross ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ a)
            +> l)) 0 h) (by cfg_eq) ?_
    exact step_end (crossW_absorb l default a b_blk (M + h) (h * 2 + n + q * 2) e) (by cfg_eq)
        (by cfg_eq)
  · exact step_end ((BlockFlow_whole (h * 2 - 2) n d0 q e E3).block_cross l a b_blk h k v
        (by omega)) (by cfg_eq) (by cfg_eq)

theorem negativeN_large_late (p n e h k d0 q M b_blk v u : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (Hh : 1 ≤ h) (He : e ≤ 1)
    (E3 : 1 + d0 = e + q * 2) (EM : M = 4 + n * 4 + q) (EK : k + v = M) :
    (negativeN ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (3 + v * 2 + u * 2))
        +> default)) p n (h + k) e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + h * 2 + n + q * 2 + e)) +> ((([1, 1, 0] : zF) ^ (3 + (M + b_blk + h)
        * 2)) +> ((([1, 0] : zF) ^ (1 + u * 2)) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_large_cross default p n e h k d0 q M b_blk v (3 + u * 2)
      HP E1 E2 Hh E3 EM EK) (by cfg_eq) ?_
  exact step_end (crossW_finish default (1 + u * 2) (M + b_blk + h) (h * 2 + n + q * 2) e He)
      (by cfg_eq) (by cfg_eq)

theorem negativeN_large_short (p n e h k d0 q M b_blk v : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (Hh : 1 ≤ h) (He : e ≤ 1)
    (E3 : 1 + d0 = e + q * 2) (EM : M = 4 + n * 4 + q) (EK : k + v = M) :
    (negativeN ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (1 + v * 2)) +> default))
        p n (h + k) e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + h * 2 + n + q * 2 + e)) +> ((([1, 1, 0] : zF) ^ (2 + (M + b_blk + h)
        * 2)) +> (([1, 0] : zF) +> default))) {{B}}> default)) := by
  refine step_bridge (negativeN_large_cross default p n e h k d0 q M b_blk v 1 HP E1 E2 Hh E3 EM EK)
      (by cfg_eq) ?_
  exact step_end (crossW_short (M + b_blk + h) (h * 2 + n + q * 2) e He) (by cfg_eq) (by cfg_eq)

theorem negativeN_large_root (p n e h k d0 q M b_blk s v : Nat)
    (HP : P p) (E1 : p = 2 + n * 2 + d0) (E2 : p + 3 + n * 2 + e = h * 2) (Hh : 1 ≤ h) (He : e ≤ 1)
    (E3 : 1 + d0 = e + q * 2) (EM : M = 4 + n * 4 + q) (EK : k + s + v + 1 = M) :
    (negativeN ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF) ^ (1 + s * 2)) +> default))
        p n (h + k) e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + h * 2 + n + q * 2 + e)) +> ((([1, 1, 0] : zF)
        ^ (2 + (k + s + b_blk + h) * 2)) +> ((([1, 0] : zF) ^ (3 + v * 2)) +> default)))
            {{B}}> default)) := by
  refine step_bridge (negativeN_large_start ((([1, 1, 0] : zF) ^ (b_blk * 2)) +> ((([1, 0] : zF)
      ^ (1 + s * 2)) +> default)) p n e h k d0 HP E1 E2 Hh) (by cfg_eq) ?_
  refine step_bridge ((BlockFlow_whole (h * 2 - 2) n d0 q e E3).block_border b_blk h k s v
      (by omega)) (by cfg_eq) ?_
  exact step_end (rootW_finish (v * 2) (k + s + b_blk + h) (h * 2 + n + q * 2) e He) (by cfg_eq)
      (by cfg_eq)

theorem rootW_finish_word0 (a : Nat) (w x y : zF) (c : Nat) (hw : Word w x y) :
    (rootW default a w c 0) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c)) +> (y.reverse +> ((([1, 0] : zF) ^ (3 + a)) +> default)))
        {{B}}> default)) := by
  rcases hw with ⟨e, hr, _⟩
  refine ReachesStar.trans (rootW_finish_word0_1 a w c) ?_
  have hws := word_shift e (([1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> default))
  refine step_bridge (Word_U_1 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  exact step_end (rootW_finish_word_end _ (1 + c)) (by cfg_eq) (by cfg_eq)

theorem crossW_finish_word0 (l : zB) (a : Nat) (w x y : zF) (c : Nat) (hw : Word w x y) :
    (crossW l default (2 + a) w c 0) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c)) +> (y.reverse +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF) ^ a)
        +> l)))) {{B}}> default)) := by
  rcases hw with ⟨e, hr, _⟩
  refine ReachesStar.trans (crossW_finish_word0_1 l a w c) ?_
  have hws := word_shift e (([1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> default))
  refine step_bridge (crossW_step_2 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  exact step_end (rootW_finish_word_end _ (1 + c)) (by cfg_eq) (by cfg_eq)

theorem crossW_finish_word1 (l : zB) (a : Nat) (w x y : zF) (c : Nat) (hw : Word w x y) :
    (crossW l default (2 + a) w c 1) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + c)) +> (y.reverse +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF) ^ a)
        +> l)))) {{B}}> default)) := by
  rcases hw with ⟨e, hr, _⟩
  refine ReachesStar.trans (crossW_finish_word1_1 l a w c) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> default))
  refine step_bridge (crossW_step_2 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  exact step_end (rootW_finish_word_end _ (2 + c)) (by cfg_eq) (by cfg_eq)

theorem rootW_finish_word1 (a : Nat) (w x y : zF) (c : Nat) (hw : Word w x y) :
    (rootW default a w c 1) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (2 + c)) +> (y.reverse +> ((([1, 0] : zF) ^ (3 + a)) +> default)))
        {{B}}> default)) := by
  rcases hw with ⟨e, hr, _⟩
  refine ReachesStar.trans (rootW_finish_word1_1 a w c) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> default))
  refine step_bridge (Word_U_1 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  exact step_end (rootW_finish_word_end _ (2 + c)) (by cfg_eq) (by cfg_eq)

theorem scan_roots (a d n : Nat) :
    (scan_root a (n * 2 + d)) [target_tm]⊢* (scan_root (n * 4 + a) d) := by
  induction n generalizing a d with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (scan_root_step a (n * 2 + d)) (by cfg_eq) ?_
    exact step_end (ih (4 + a) d) (by cfg_eq) (by cfg_eq)

theorem final_zero_even (d : Nat) :
    (final_scan 0 (d * 2)) [target_tm]⊢* (section_481 [3 + d * 4]) := by
  refine ReachesStar.trans (final_zero_1 (d * 2)) ?_
  refine step_bridge (scan_roots 1 0 d) (by cfg_eq) ?_
  exact step_end (final_even_2 (d * 4)) (by cfg_eq) (by cfg_eq)

theorem final_zero_odd (d : Nat) :
    (final_scan 0 (1 + d * 2)) [target_tm]⊢* (section_481 [4 + d * 4]) := by
  refine ReachesStar.trans (final_zero_1 (1 + d * 2)) ?_
  refine step_bridge (scan_roots 1 1 d) (by cfg_eq) ?_
  exact step_end (final_odd_2 (d * 4)) (by cfg_eq) (by cfg_eq)

theorem final_one_even (d : Nat) :
    (final_scan 1 (d * 2)) [target_tm]⊢* (section_481 [5 + d * 4]) := by
  refine ReachesStar.trans (final_one_1 (d * 2)) ?_
  refine step_bridge (scan_roots 3 0 d) (by cfg_eq) ?_
  exact step_end (final_even_2 (2 + d * 4)) (by cfg_eq) (by cfg_eq)

theorem final_one_odd (d : Nat) :
    (final_scan 1 (1 + d * 2)) [target_tm]⊢* (section_481 [6 + d * 4]) := by
  refine ReachesStar.trans (final_one_1 (1 + d * 2)) ?_
  refine step_bridge (scan_roots 3 1 d) (by cfg_eq) ?_
  exact step_end (final_odd_2 (2 + d * 4)) (by cfg_eq) (by cfg_eq)

inductive Last : Nat → Nat → List Nat → Prop where
  | Last0E (d : Nat) : Last 0 (d * 2) [3 + d * 4]
  | Last0O (d : Nat) : Last 0 (1 + d * 2) [4 + d * 4]
  | Last1E (d : Nat) : Last 1 (d * 2) [5 + d * 4]
  | Last1O (d : Nat) : Last 1 (1 + d * 2) [6 + d * 4]
  | LastEE (a d : Nat) : Last (2 + a * 2) (2 + a * 2 + d * 2)
      [2 + a * 2 + d * 2, 2 + a * 2, 3 + d * 2]
  | LastEO (a d : Nat) : Last (2 + a * 2) (1 + a * 2 + d * 2)
      [1 + a * 2 + d * 2, 2 + a * 2, 1 + d * 2]
  | LastOE (a d : Nat) : Last (3 + a * 2) (2 + a * 2 + d * 2)
      [2 + a * 2 + d * 2, 2 + a * 2, 5 + d * 2]
  | LastOO (a d : Nat) : Last (3 + a * 2) (3 + a * 2 + d * 2)
      [3 + a * 2 + d * 2, 2 + a * 2, 5 + d * 2]
  | LastBorder (a : Nat) : Last (4 + a * 2) (2 + a * 2) [2 + a * 2, 4 + a * 2, 1]
  | LastOverflowO (a d : Nat) : Last (3 + d * 2 + a) (1 + d * 2) [1 + d * 2, 3 + d * 2, a]
  | LastOverflowE (a d : Nat) : Last (5 + d * 2 + a) (2 + d * 2) [2 + d * 2, 5 + d * 2, a]

theorem Last_spec (t m : Nat) (xs : List Nat) (h : Last t m xs) :
    (final_scan t m) [target_tm]⊢* (section_481 xs) := by
  rcases h with d | d | d | d | ⟨a, d⟩ | ⟨a, d⟩ | ⟨a, d⟩ | ⟨a, d⟩ | a | ⟨a, d⟩ | ⟨a, d⟩
  · exact final_zero_even d
  · exact final_zero_odd d
  · exact final_one_even d
  · exact final_one_odd d
  · exact step_end (even_left_even a d) (by cfg_eq) (by cfg_eq)
  · exact step_end (even_left_odd a d) (by cfg_eq) (by cfg_eq)
  · exact step_end (normal_even a d) (by cfg_eq) (by cfg_eq)
  · exact step_end (normal_odd a d) (by cfg_eq) (by cfg_eq)
  · exact step_end (border_even default a) (by cfg_eq) (by cfg_eq)
  · exact step_end (left_overflow_odd default a d) (by cfg_eq) (by cfg_eq)
  · exact step_end (left_overflow_even default a d) (by cfg_eq) (by cfg_eq)

theorem parity (n : Nat) : ∃ k, n = k * 2 ∨ n = 1 + k * 2 := by
  refine ⟨n / 2, ?_⟩
  omega

theorem Last_eq {t1 t2 m1 m2 : Nat} {xs1 xs2 : List Nat} (h : Last t1 m1 xs1)
    (ht : t1 = t2 := by omega) (hm : m1 = m2 := by omega) (hxs : xs1 = xs2 := by rfl) :
    Last t2 m2 xs2 := by
  subst ht; subst hm; subst hxs; exact h

theorem Last_total (t m : Nat) (Hm : 0 < m) : ∃ xs, Last t m xs := by
  rcases t with _ | _ | t
  · rcases parity m with ⟨d, rfl | rfl⟩
    · exact ⟨_, Last.Last0E d⟩
    · exact ⟨_, Last.Last0O d⟩
  · rcases parity m with ⟨d, rfl | rfl⟩
    · exact ⟨_, Last.Last1E d⟩
    · exact ⟨_, Last.Last1O d⟩
  · rcases m with _ | m
    · omega
    · rcases parity t with ⟨a, rfl | rfl⟩ <;> rcases parity m with ⟨d, rfl | rfl⟩
      · by_cases hle : a ≤ d
        · exact ⟨_, Last_eq (Last.LastEO a (d - a))⟩
        · exact ⟨_, Last_eq (Last.LastOverflowO (a * 2 - d * 2 - 1) d)⟩
      · by_cases hle : a ≤ d
        · exact ⟨_, Last_eq (Last.LastEE a (d - a))⟩
        · by_cases heq : a = 1 + d
          · exact ⟨_, Last_eq (Last.LastBorder d)⟩
          · exact ⟨_, Last_eq (Last.LastOverflowE (a * 2 - d * 2 - 3) d)⟩
      · by_cases hlt : a < d
        · exact ⟨_, Last_eq (Last.LastOO a (d - a - 1))⟩
        · exact ⟨_, Last_eq (Last.LastOverflowO ((a - d) * 2) d)⟩
      · by_cases hle : a ≤ d
        · exact ⟨_, Last_eq (Last.LastOE a (d - a))⟩
        · exact ⟨_, Last_eq (Last.LastOverflowE ((a - d - 1) * 2) d)⟩

theorem Last_progress (t m : Nat) (xs : List Nat) (H : Last t m xs) :
    (final_scan t m) [target_tm]⊢⁺ (section_481 xs) :=
  evstep_progress (Last_spec t m xs H) (by ne_cfg)

def last_output (t m : Nat) : List Nat :=
  let e := 1 - m % 2
  let r := t % 2
  if t ≤ 1 then [m * 2 + 2 + t * 2 + e]
  else if t + r ≤ m + 1 + e then [m, t - r, m + 2 + r * 3 + e - t]
  else [m, m + 2 + e, t - (m + 2 + e)]

theorem Last_output (t m : Nat) (xs : List Nat) (H : Last t m xs) :
    xs = last_output t m := by
  cases H <;> dsimp only [last_output] <;> split_ifs <;>
    (try simp only [List.cons.injEq, and_true, true_and]) <;>
    ((repeat' constructor) <;> first | trivial | omega)

theorem last_output_spec (t m : Nat) (H : 0 < m) :
    (final_scan t m) [target_tm]⊢⁺ (section_481 (last_output t m)) := by
  rcases Last_total t m H with ⟨xs, HL⟩
  rw [← Last_output t m xs HL]
  exact Last_progress t m xs HL

theorem good_section_formula (p b t : Nat) (HP : P p) (H : 0 < p + b) :
    (section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 (last_output t (p + b))) := by
  refine evstep_progress_trans ?_ (last_output_spec t (p + b) H)
  refine step_bridge (HP ((([1, 1, 0] : zF) ^ b) +> ((([1, 0] : zF) ^ t) +> default))) (by cfg_eq)
      ?_
  exact step_end (pass_011 ((([1, 0] : zF) ^ t) +> default) ((([0, 1, 0] : zF) ^ p) +> default) b)
      (by cfg_eq) (by cfg_eq)

theorem S_short_section1 (b c : Nat) :
    (S default default 3 (1 + b) c 1) [target_tm]⊢* (section_481 [2 + c, 4 + b * 2, 1]) :=
  step_end (S_short1 default b c) (by cfg_eq) (by cfg_eq)

def S_odd_output (b c v d : Nat) : List Nat :=
  let edge := d + 2 + d % 2
  if 1 + v * 2 < edge then [1 + c + d, 2 + b * 2 + v * 2, edge - (1 + v * 2)]
  else [1 + c + d, 3 + b * 2 + d + d % 2, 1 + v * 2 - edge]

theorem S_odd_spec (b c v d : Nat) :
    (S default default (1 + v * 2) (1 + b) c d)
        [target_tm]⊢* (section_481 (S_odd_output b c v d)) := by
  rcases parity d with ⟨r, rfl | rfl⟩ <;> dsimp only [S_odd_output]
  · by_cases hlt : v < r
    · rw [ite_eq_left (by omega)]
      exact step_end (S_root_exit1 b c v (r - v - 1)) (by cfg_eq) (by cfg_eq)
    · by_cases heq : v = r
      · subst heq
        rw [ite_eq_left (by omega)]
        have he : v * 2 + 2 + v * 2 % 2 - (1 + v * 2) = 1 := by omega
        rw [he]
        refine step_bridge (Incs1 default default 1 (1 + b) c 0 v) (by cfg_eq) ?_
        exact step_end (S_short0 default (b + v) (c + v * 2)) (by cfg_eq) (by cfg_eq)
      · rw [ite_eq_right (by omega)]
        refine step_bridge (Incs1 default default (1 + (v - r) * 2) (1 + b) c 0 r) (by cfg_eq) ?_
        exact step_end (S_exit0 default ((v - r) * 2 - 1) (b + r) (c + r * 2)) (by cfg_eq)
            (by cfg_eq)
  · by_cases hle : v ≤ r
    · rw [ite_eq_left (by omega)]
      exact step_end (S_root_exit0 b c v (r - v)) (by cfg_eq) (by cfg_eq)
    · by_cases heq : v = 1 + r
      · subst v
        rw [ite_eq_left (by omega)]
        have he : 1 + r * 2 + 2 + (1 + r * 2) % 2 - (1 + (1 + r) * 2) = 1 := by omega
        rw [he]
        refine step_bridge (Incs1 default default 3 (1 + b) c 1 r) (by cfg_eq) ?_
        exact step_end (S_short_section1 (b + r) (c + r * 2)) (by cfg_eq) (by cfg_eq)
      · rw [ite_eq_right (by omega)]
        refine step_bridge (Incs1 default default (1 + (v - r) * 2) (1 + b) c 1 r) (by cfg_eq) ?_
        exact step_end (S_exit1 default ((v - r) * 2 - 3) (b + r) (c + r * 2)) (by cfg_eq)
            (by cfg_eq)

theorem S_odd_progress (b c v d : Nat) :
    (S default default (1 + v * 2) (1 + b) c d)
        [target_tm]⊢⁺ (section_481 (S_odd_output b c v d)) :=
  evstep_progress (S_odd_spec b c v d) (by ne_cfg)

theorem odd_last_S (g j t : Nat) (HP : P (2 + g * 2)) :
    (section_481 [(2 + g * 2) + (3 + g * 2), j * 2, t]) [target_tm]⊢*
    (S default default t (2 + j + g) (1 + g * 2) 0) := by
  refine step_bridge (return_last ((([1, 1, 0] : zF) ^ (j * 2)) +> ((([1, 0] : zF) ^ t) +> default))
      g HP) (by cfg_eq) ?_
  exact step_end (even_block ((([1, 0] : zF) ^ t) +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (2 + g))
      +> ((([1, 0] : zF) ^ (1 + g * 2)) +> default)) j) (by cfg_eq) (by cfg_eq)

theorem odd_gap_seed (g j t d : Nat) (HP : P (1 + g * 2 + d)) :
    (section_481 [(1 + g * 2 + d) + (1 + g * 2), 1 + j * 2, t]) [target_tm]⊢*
    (seed t (j + g) g d) := by
  refine step_bridge (return_odd ((([1, 1, 0] : zF) ^ (1 + j * 2)) +> ((([1, 0] : zF) ^ t)
      +> default)) g d HP) (by cfg_eq) ?_
  exact step_end (odd_seed g j t d) (by cfg_eq) (by cfg_eq)

theorem odd_gap_S (g j t d : Nat) (HP : P (1 + g * 2 + d)) :
    (section_481 [(1 + g * 2 + d) + (1 + g * 2), j * 2, t]) [target_tm]⊢*
    (S default default t (1 + j + g) (g * 2) d) := by
  refine step_bridge (return_odd ((([1, 1, 0] : zF) ^ (j * 2)) +> ((([1, 0] : zF) ^ t) +> default))
      g d HP) (by cfg_eq) ?_
  exact step_end (even_block ((([1, 0] : zF) ^ t) +> default) ((([0, 1, 1, 0, 1, 0] : zF) ^ (1 + g))
      +> ((([1, 0] : zF) ^ (g * 2)) +> (([0] : zF) +> ((([1, 0, 0] : zF) ^ d) +> default)))) j)
          (by cfg_eq) (by cfg_eq)

theorem seed_section (a b c d : Nat) :
    (seed a b c d) [target_tm]⊢* (section_481 [1 + c * 2 + d, 2 + b * 2, 2 + a + d + d % 2]) := by
  rcases parity d with ⟨r, rfl | rfl⟩
  · rcases r with _ | r
    · exact step_end (seed_zero a b c) (by cfg_eq) (by cfg_eq)
    · have hm : ((r + 1) * 2) % 2 = 0 := by omega
      rw [hm]
      exact step_end (seed_even a b c r) (by cfg_eq) (by cfg_eq)
  · have hm : (1 + r * 2) % 2 = 1 := by omega
    rw [hm]
    exact step_end (seed_odd a b c r) (by cfg_eq) (by cfg_eq)

theorem odd_last_even_formula (g j v : Nat) (H : P (2 + g * 2)) :
    (section_481 [(2 + g * 2) + (3 + g * 2), j * 2, 1 + v * 2]) [target_tm]⊢⁺
    (section_481 (S_odd_output (1 + j + g) (1 + g * 2) v 0)) := by
  refine evstep_progress_trans (odd_last_S g j (1 + v * 2) H) ?_
  exact step_end_plus_eq (S_odd_progress (1 + j + g) (1 + g * 2) v 0) (by cfg_eq) (by cfg_eq)

theorem unary_progress (p k : Nat) (HP : P p) (H : 0 < p) :
    (section_481 [p + k]) [target_tm]⊢⁺ (section_481 (last_output k p)) := by
  refine evstep_progress_trans ?_ (last_output_spec k p H)
  exact step_end (HP ((([1, 0] : zF) ^ k) +> default)) (by cfg_eq) (by cfg_eq)

theorem rootTs (a b c d n : Nat) :
    (rootT a b c (n * 2 + d)) [target_tm]⊢* (rootT (n * 2 + a) b (n * 2 + c) d) := by
  induction n generalizing a c d with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (rootT_step a b c (n * 2 + d)) (by cfg_eq) ?_
    exact step_end (ih (2 + a) (2 + c) d) (by cfg_eq) (by cfg_eq)

def pred_output (n b t : Nat) : List Nat :=
  let h := n + 4 + n % 2
  if t < h then [1 + n, b + t - 1, h - t] else [1 + n, b + h - 1, t - h]

theorem pred_root_formula (b n : Nat) :
    (rootT 0 b 0 n) [target_tm]⊢* (section_481 [1 + n, 2 + b * 2, 3 + n + n % 2]) := by
  rcases parity n with ⟨r, rfl | rfl⟩
  · have hm : (r * 2) % 2 = 0 := by omega
    rw [hm]
    refine step_bridge (rootTs 0 b 0 0 r) (by cfg_eq) ?_
    exact step_end (rootT_end0 (r * 2) b (r * 2)) (by cfg_eq) (by cfg_eq)
  · have hm : (1 + r * 2) % 2 = 1 := by omega
    rw [hm]
    refine step_bridge (rootTs 0 b 0 1 r) (by cfg_eq) ?_
    exact step_end (rootT_end1 (r * 2) b (r * 2)) (by cfg_eq) (by cfg_eq)

theorem pred_S_formula (b v n : Nat) :
    S_odd_output (1 + b) 0 v n = pred_output n (2 + b * 2) (3 + v * 2) := by
  dsimp only [S_odd_output, pred_output]
  split_ifs <;> (try simp only [List.cons.injEq, and_true, true_and]) <;>
    ((repeat' constructor) <;> first | trivial | omega)

theorem pred_terminal (n b v : Nat) :
    ((((([1, 1, 0] : zF) ^ (2 + b * 2)) +> ((([1, 0] : zF) ^ (1 + v * 2)) +> default)) <{{E}}
      (([0, 1, 1] : zF) +> ((([0, 1, 0] : zF) ^ n) +> default)))) [target_tm]⊢⁺
    (section_481 (pred_output n (2 + b * 2) (1 + v * 2))) := by
  refine evstep_progress ?_ (by ne_cfg)
  rcases v with _ | v
  · refine step_bridge (pred_root b n) (by cfg_eq) ?_
    dsimp only [pred_output]
    rw [ite_eq_left (by omega)]
    exact step_end (pred_root_formula b n) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (pred_S (1 + v * 2) b n) (by cfg_eq) ?_
    have heq : 1 + (v + 1) * 2 = 3 + v * 2 := by omega
    rw [heq, ← pred_S_formula b v n]
    exact step_end (S_odd_spec (1 + b) 0 v n) (by cfg_eq) (by cfg_eq)

theorem pred_section (n b v : Nat) (HP : PP n) :
    (section_481 [n, 2 + b * 2, 1 + v * 2]) [target_tm]⊢⁺ (section_481 (pred_output n (2 + b * 2)
        (1 + v * 2))) := by
  refine evstep_progress_trans ?_ (pred_terminal n b v)
  exact step_end (HP ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> ((([1, 0] : zF) ^ (1 + v * 2))
      +> default))) (by cfg_eq) (by cfg_eq)

theorem scan_lefts (r : zB) (a d n : Nat) :
    (scan_left r a (n * 2 + d)) [target_tm]⊢* (scan_left r (n * 4 + a) d) := by
  induction n generalizing a d with
  | zero => exact step_eq (by cfg_eq)
  | succ n ih =>
    refine step_bridge (scan_left_step r a (n * 2 + d)) (by cfg_eq) ?_
    exact step_end (ih (4 + a) d) (by cfg_eq) (by cfg_eq)

theorem short_normalize (a n d : Nat) :
    (scan_left (short_suffix n d) (1 + a) 0) [target_tm]⊢*
    (rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + n)) (1 + n * 2) d) :=
  step_eq (by cfg_eq)

theorem short_root (n j d : Nat) (HP : P (2 + n * 2 + d)) :
    (section_481 [(2 + n * 2 + d) + (2 + n * 2), j * 2, 1]) [target_tm]⊢*
    (rootW default (2 + j * 4) (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + n)) (1 + n * 2) d) := by
  refine step_bridge (return_even ((([1, 1, 0] : zF) ^ (j * 2)) +> ((([1, 0] : zF) ^ 1) +> default))
      n d HP) (by cfg_eq) ?_
  refine step_bridge (pass_011 (([1, 0] : zF) +> default) (short_suffix n d) (j * 2)) (by cfg_eq) ?_
  refine step_bridge (scan_left_entry (short_suffix n d) (j * 2)) (by cfg_eq) ?_
  refine step_bridge (scan_lefts (short_suffix n d) 3 0 j) (by cfg_eq) ?_
  exact step_end (short_normalize (2 + j * 4) n d) (by cfg_eq) (by cfg_eq)

theorem short_section (n j d : Nat) (HP : P (2 + n * 2 + d)) :
    (section_481 [(2 + n * 2 + d) + (2 + n * 2), j * 2, 1]) [target_tm]⊢⁺
    (section_481 [2 + n * 2 + d, 2 + n * 2, 5 + j * 4 + d - d % 2]) := by
  refine evstep_progress_trans (short_root n j d HP) ?_
  refine evstep_progress ?_ (by ne_cfg)
  rcases parity d with ⟨r, rfl | rfl⟩
  · have hm : (r * 2) % 2 = 0 := by omega
    rw [hm]
    refine step_bridge (rootsW default (2 + j * 4) _ _ _ (1 + n * 2) 0 r (Word_pow _ _ _ (1 + n)
        Word_V)) (by cfg_eq) ?_
    exact step_end (root_end0 (r * 2 + (2 + j * 4)) n (r * 2 + (1 + n * 2))) (by cfg_eq) (by cfg_eq)
  · have hm : (1 + r * 2) % 2 = 1 := by omega
    rw [hm]
    refine step_bridge (rootsW default (2 + j * 4) _ _ _ (1 + n * 2) 1 r (Word_pow _ _ _ (1 + n)
        Word_V)) (by cfg_eq) ?_
    exact step_end (root_end1 (r * 2 + (2 + j * 4)) n (r * 2 + (1 + n * 2))) (by cfg_eq) (by cfg_eq)

def next_p (p : Nat) : Nat := p * 2 + 2 + (1 - p % 2)

theorem P_next (p : Nat) (H : 3 ≤ p) (HP : P p) : P (next_p p) := by
  dsimp only [next_p]
  rcases parity p with ⟨a, rfl | rfl⟩
  · rcases a with _ | a
    · omega
    · have he1 : (a + 1) * 2 = 2 + a * 2 := by omega
      have he2 : (a + 1) * 2 * 2 + 2 + (1 - (a + 1) * 2 % 2) = (2 + a * 2) + (5 + a * 2) := by omega
      rw [he2]
      exact P_S' a (he1 ▸ HP)
  · have he2 : (1 + a * 2) * 2 + 2 + (1 - (1 + a * 2) % 2) = (1 + a * 2) + (3 + a * 2) := by omega
    rw [he2]
    exact P_S a HP

inductive Chain : Nat → Prop where
  | Chain0 : Chain 3
  | ChainS (p : Nat) : Chain p → Chain (next_p p)

theorem next_p_grows (p : Nat) : p < next_p p := by
  dsimp only [next_p]; omega

theorem Chain_spec (p : Nat) (H : Chain p) :
    3 ≤ p ∧ P p ∧ (p % 16 = 3 ∨ p % 32 = 8) := by
  induction H with
  | Chain0 => refine ⟨by omega, P3, Or.inl rfl⟩
  | ChainS p _ ih =>
    rcases ih with ⟨Hp, HP, Hm⟩
    have hg := next_p_grows p
    refine ⟨by omega, P_next p Hp HP, ?_⟩
    dsimp only [next_p]
    rcases Hm with h16 | h32
    · right; omega
    · left; omega

def Band (p n : Nat) : Prop := Chain p ∧ p ≤ n ∧ n < next_p p

theorem Band_total (n : Nat) (Hn : 3 ≤ n) : ∃ p, Band p n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases heq : n = 2
    · subst heq
      exact ⟨3, Chain.Chain0, by omega, by dsimp [next_p]; omega⟩
    · rcases ih (by omega) with ⟨p, HP, Hlo, Hhi⟩
      by_cases hlt : n + 1 < next_p p
      · exact ⟨p, HP, by omega, hlt⟩
      · have hg := next_p_grows (next_p p)
        exact ⟨next_p p, Chain.ChainS p HP, by omega, by omega⟩

def link (w : zF) (c d : Nat) (r : zB) : zB :=
  ([0, 1, 0, 0, 1] : zF) +> (w +> ((([1, 0] : zF) ^ c) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
      ^ d) +> r))))

def clean_input (c d : Nat) (r : zB) : zB :=
  ((([1, 0] : zF) ^ c) +> (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r)))

theorem lpow_comm_single (w : zF) (n : Nat) : w ^ n ++ w = w ++ w ^ n := by
  induction n with
  | zero => simp only [list_pow_zero, List.nil_append, List.append_nil]
  | succ n ih =>
    rw [list_pow_succ, List.append_assoc, ih, ← List.append_assoc]

theorem reverse_power (w : zF) (n : Nat) : (w ^ n).reverse = (w.reverse) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [list_pow_succ, List.reverse_append, ih,
      list_pow_succ, lpow_comm_single]

theorem rev_011011 : ([0, 1, 1, 0, 1, 1] : zF).reverse = [1, 1, 0, 1, 1, 0] := rfl
theorem rev_01 : ([0, 1] : zF).reverse = [1, 0] := rfl

macro "solve_cfg_spine2" : tactic =>
  `(tactic| (first
    | rfl
    | apply app2_congr (by omega) (by omega)
    | (apply app3_congr ?_ (by omega) (by omega); solve_spine; done)
    | ((first | apply cfg_left_congr | apply cfg_right_congr) <;> (solve_spine; done))
    | (solve_spine; done)))

macro "cfg_eq" : tactic =>
  `(tactic| first
    | rfl
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         link, clean_input,
         S, rootW, crossW, crossZ, rootZ, crossV, rootV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only
           [Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
               Nat.mul_one, Nat.mul_zero, Nat.zero_mul,
         list_pow_zero, list_pow_succ, list_pow_one,
         pow_add_1, pow_add_2, pow_add_3, pow_add_4, pow_add_5,
         pow_add_right_2, pow_add_right_3, pow_add_right_4, pow_add_right_5,
         pow_double3,
         List.reverse_append, List.reverse_nil, reverse_power, rev_011011, rev_01,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         shift2, shift3, shift6,
         shift2_0, shift3_0_1, shift3_0_01, shift6_0_1, shift6_0_01,
         pow_merge, ListBlank.cons_zero_default]
       try ac_rfl
       done)
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         link, clean_input,
         S, rootW, crossW, rootZ, crossZ, rootV, crossV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only [Nat.mul_zero, Nat.zero_mul,
         List.reverse_append, List.reverse_nil, reverse_power, rev_011011, rev_01,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         list_pow_zero,
         pow_double3, pow_merge, fold2, fold3, fold6, ListBlank.cons_zero_default]
       first | done | (solve_cfg_spine2; done))
    | (try dsimp only [Sim.toCfg, special, specialN, flow_tail, short_suffix, negativeN, loneN,
         link, clean_input,
         S, rootW, crossW, rootZ, crossZ, rootV, crossV, seed, final_scan, scan_root,
         rootT, scan_left, scanW, section_481, section_side, w10, w110]
       try simp only
           [Nat.add_assoc, Nat.add_zero, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul,
               Nat.mul_one, Nat.mul_zero, Nat.zero_mul,
         list_pow_zero, list_pow_succ,
         pow_add_1, pow_add_2, pow_add_3, pow_add_4, pow_add_5,
         pow_add_right_2, pow_add_right_3, pow_add_right_4, pow_add_right_5,
         pow_double3,
         List.reverse_append, List.reverse_nil, reverse_power, rev_011011, rev_01,
         List.nil_append, List.cons_append, List.append_assoc,
         listblank_append_nil, listblank_append_cons, listblank_append_right_assoc,
         shift2, shift3, shift6,
         shift2_0, shift3_0_1, shift3_0_01, shift6_0_1, shift6_0_01,
         pow_merge, ListBlank.cons_zero_default]
       try simp only [fold2, fold3, fold6, pow_merge, ListBlank.cons_zero_default]
       first | done | (solve_cfg_spine2; done)))

theorem crossW_one_word (r : zB) (w x y : zF) (c d : Nat) (hw : Word w x y) :
    (crossW default r 1 w c (2 + d)) [target_tm]⊢*
    (rootW r 0 (([1, 0, 1, 0, 0, 1] : zF) ++ w) (2 + c) d) := by
  rcases hw with ⟨e, hr, hl⟩
  refine ReachesStar.trans (crossW_one_word_1 r w c d) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> (([0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r))))
  refine step_bridge (crossW_one_word_2 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  refine step_bridge (rootW_step_3 _ r c d) (by cfg_eq) ?_
  refine ReachesStar.trans (hl _ _) ?_
  exact step_end (crossW_one_word_4 r w c d) (by cfg_eq) (by cfg_eq)

theorem crossW_join (l r : zB) (a : Nat) (w : zF) (c : Nat) (v : zF) (c' d : Nat) :
    (crossW l (link v c' d r) a w c 0) [target_tm]⊢*
    (crossW l r a (w ++ ([1, 0] : zF) ^ (1 + c) ++ [1, 0, 1, 0, 0, 1] ++ v) c' d) :=
  step_eq (by cfg_eq)

theorem rootW_join (r : zB) (a : Nat) (w : zF) (c : Nat) (v : zF) (c' d : Nat) :
    (rootW (link v c' d r) a w c 0) [target_tm]⊢*
    (rootW r a (w ++ ([1, 0] : zF) ^ (1 + c) ++ [1, 0, 1, 0, 0, 1] ++ v) c' d) :=
  step_eq (by cfg_eq)

theorem Flow_W_word (r : zB) (w x y : zF) (c d : Nat) (hw : Word w x y) :
    Flow (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c (2 + d))
         (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c (2 + d))
         (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (2 + c) d)
         (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (2 + c) d) 1 := by
  have HW : ∀ b, Word ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) ((([1, 0, 0, 1, 1, 0] : zF) ^ b) ++ x)
      ((([0, 1, 1, 0, 1, 1] : zF) ^ b) ++ y) :=
    fun b => Word_app _ _ _ _ _ _ (Word_pow _ _ _ b Word_V) hw
  refine ⟨?_, ?_, ?_⟩
  · intro l a b
    exact step_end (crossW_step l r a _ _ _ c d (HW b)) (by cfg_eq) (by cfg_eq)
  · intro a b
    exact step_end (rootW_step r a _ _ _ c d (HW b)) (by cfg_eq) (by cfg_eq)
  · intro s v b hsv
    have hs : s = 0 := by omega
    have hv : v = 0 := by omega
    subst hs; subst hv
    exact step_end (crossW_one_word r _ _ _ c d (HW b)) (by cfg_eq) (by cfg_eq)

theorem Flow_Ws_word (r : zB) (w x y : zF) (c d n : Nat) (hw : Word w x y) :
    Flow (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c (n * 2 + d))
         (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c (n * 2 + d))
         (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (n * 2 + c) d)
         (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (n * 2 + c) d) n := by
  induction n generalizing c with
  | zero =>
    exact Flow_eq (Flow_id _ _) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) rfl
  | succ n ih =>
    have h1 : Flow (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c ((n + 1)
                                   * 2 + d))
                   (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) c ((n + 1) * 2 + d))
                   (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (2 + c)
                                   (n * 2 + d))
                   (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ w) (2 + c) (n * 2 + d))
                                 1 :=
      Flow_eq (Flow_W_word r w x y c (n * 2 + d) hw) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    exact Flow_eq (Flow_trans h1 (ih (2 + c))) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem Flow_join (r : zB) (w : zF) (c : Nat) (v : zF) (c' d : Nat) :
    Flow (fun l a n => crossW l (link v c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) c 0)
         (fun a n => rootW (link v c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) c 0)
         (fun l a n => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w ++ ([1, 0] : zF) ^ (1 + c)
                         ++ [1, 0, 1, 0, 0, 1] ++ v) c' d)
         (fun a n => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w ++ ([1, 0] : zF) ^ (1 + c)
                       ++ [1, 0, 1, 0, 0, 1] ++ v) c' d) 0 := by
  refine ⟨?_, ?_, fun s v b h => by omega⟩
  · intro l a n; exact step_end (crossW_join l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) c v c' d)
        (by cfg_eq) (by cfg_eq)
  · intro a n; exact step_end (rootW_join r a ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) c v c' d)
        (by cfg_eq) (by cfg_eq)

inductive Route : Nat → Nat → zB → Nat → zF → Nat → Nat → zB → Prop where
  | Route_done (c n e : Nat) (r : zB) : Route c (n * 2 + e) r n [] (n * 2 + c) e r
  | Route_more (c n : Nat) (v x y : zF) (c' d : Nat) (r : zB) (m : Nat) (w : zF) (C_out e : Nat)
      (R : zB) :
      Word v x y → Route c' d r m w C_out e R →
      Route c (n * 2) (link v c' d r) (n + m)
        (([1, 0] : zF) ^ (1 + n * 2 + c) ++ [1, 0, 1, 0, 0, 1] ++ v ++ w) C_out e R

theorem Route_eq {c1 c2 d1 d2 : Nat} {r1 r2 : zB} {n1 n2 : Nat} {w1 w2 : zF} {C1 C2 e1 e2 : Nat} {R1
    R2 : zB}
    (h : Route c1 d1 r1 n1 w1 C1 e1 R1)
    (hc : c1 = c2 := by omega) (hd : d1 = d2 := by omega) (hr : r1 = r2 := by cfg_eq)
    (hn : n1 = n2 := by omega)
    (hw : w1 = w2 :=
        by simp only
            [list_pow_zero, list_pow_one, List.append_nil, List.nil_append, List.append_assoc])
    (hC : C1 = C2 := by omega) (he : e1 = e2 := by omega) (hR : R1 = R2 := by cfg_eq) :
    Route c2 d2 r2 n2 w2 C2 e2 R2 := by
  subst hc; subst hd; subst hr; subst hn; subst hw; subst hC; subst he; subst hR; exact h

theorem Word_link (v x y : zF) (c : Nat) (z X Y : zF) (hv : Word v x y) (hz : Word z X Y) :
    Word (v ++ ([1, 0] : zF) ^ c ++ [1, 0, 1, 0, 0, 1] ++ z)
         (x ++ ([1, 0] : zF) ^ c ++ [1, 0, 0, 1, 1, 0] ++ X)
         (y ++ ([0, 1] : zF) ^ c ++ [0, 1, 1, 0, 1, 1] ++ Y) := by
  exact Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ hv (Word_pow _ _ _ c
      Word_U)) Word_V) hz

theorem Route_flow (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) (v x y : zF) (HW : Word v x y) :
    Flow (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v) c d)
         (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v) c d)
         (fun l a b => crossW l R a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v ++ w) C_out e)
         (fun a b => rootW R a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v ++ w) C_out e) n := by
  induction H generalizing v x y with
  | Route_done c n e r =>
    exact Flow_eq (Flow_Ws_word r v x y c e n HW) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) rfl
  | Route_more c n z X Y c' d r m w C_out e R Hz HR ih =>
    have h1 : Flow (fun l a b => crossW l (link z c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v)
                                   c (n * 2))
                   (fun a b => rootW (link z c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v)
                                 c (n * 2))
                   (fun l a b => crossW l (link z c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v)
                                   (n * 2 + c) 0)
                   (fun a b => rootW (link z c' d r) a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v)
                                 (n * 2 + c) 0) n :=
      Flow_eq (Flow_Ws_word (link z c' d r) v x y c 0 n HW) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) (by intros; cfg_eq) rfl
    have h2 := Flow_join r v (n * 2 + c) z c' d
    have HV := Word_link v x y (1 + n * 2 + c) z X Y HW Hz
    have h3 : Flow (fun l a b => crossW l r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v ++ ([1, 0] : zF)
                                   ^ (1 + (n * 2 + c)) ++ [1, 0, 1, 0, 0, 1] ++ z) c' d)
                   (fun a b => rootW r a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ v ++ ([1, 0] : zF)
                                 ^ (1 + (n * 2 + c)) ++ [1, 0, 1, 0, 0, 1] ++ z) c' d)
                   (fun l a b => crossW l R a ((([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                   ++ (v ++ ([1, 0] : zF) ^ (1 + n * 2 + c)
                                       ++ [1, 0, 1, 0, 0, 1] ++ z) ++ w) C_out e)
                   (fun a b => rootW R a ((([1, 0, 1, 0, 0, 1] : zF) ^ b) ++ (v ++ ([1, 0] : zF)
                                 ^ (1 + n * 2 + c) ++ [1, 0, 1, 0, 0, 1] ++ z) ++ w) C_out e) m :=
      Flow_eq (ih _ _ _ HV) (by intros; cfg_eq) (by intros; cfg_eq) (by intros; cfg_eq)
          (by intros; cfg_eq) rfl
    exact Flow_eq (Flow_trans h1 (Flow_trans h2 h3)) (by intros; cfg_eq) (by intros; cfg_eq)
        (by intros; cfg_eq) (by intros; cfg_eq) (by omega)

theorem Route_word (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) : ∃ x y, Word w x y := by
  induction H with
  | Route_done => exact ⟨[], [], Word_nil⟩
  | Route_more c n v x y c' d r m w C_out e R HV HR ih =>
    rcases ih with ⟨X, Y, HW⟩
    exact ⟨_, _, Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1
        + n * 2 + c) Word_U) Word_V) HV) HW⟩

theorem Route_cut (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) (k : Nat) (Hk : k ≤ n) :
    ∃ c' d' r' u v, Route c d r k u c' d' r' ∧ Route c' d' r' (n - k) v C_out e R ∧ w = u ++ v := by
  induction H generalizing k with
  | Route_done c n e r =>
    refine ⟨k * 2 + c, (n - k) * 2 + e, r, [], [], ?_, ?_, rfl⟩
    · exact Route_eq (Route.Route_done c k ((n - k) * 2 + e) r)
    · exact Route_eq (Route.Route_done (k * 2 + c) (n - k) e r)
  | Route_more c n z X Y c0 d0 r0 m w C_out e R Hz HR ih =>
    by_cases hle : k ≤ n
    · refine ⟨k * 2 + c, (n - k) * 2, link z c0 d0 r0, [], ([1, 0] : zF) ^ (1 + n * 2 + c)
          ++ [1, 0, 1, 0, 0, 1] ++ z ++ w, ?_, ?_, rfl⟩
      · exact Route_eq (Route.Route_done c k ((n - k) * 2) (link z c0 d0 r0))
      · have heq : 1 + (n - k) * 2 + (k * 2 + c) = 1 + n * 2 + c := by omega
        exact Route_eq (Route.Route_more (k * 2 + c) (n - k) z X Y c0 d0 r0 m w C_out e R Hz HR)
          (hw := by rw [heq])
    · rcases ih (k - n) (by omega) with ⟨c', d', r', u, v, HU, HV, EW⟩
      refine ⟨c', d', r', ([1, 0] : zF) ^ (1 + n * 2 + c) ++ [1, 0, 1, 0, 0, 1] ++ z ++ u, v, ?_,
          ?_, ?_⟩
      · exact Route_eq (Route.Route_more c n z X Y c0 d0 r0 (k - n) u c' d' r' Hz HU)
      · exact Route_eq HV
      · rw [EW]; simp only [List.append_assoc]

theorem crossW_next (l r : zB) (w x y : zF) (c d : Nat) (hw : Word w x y) :
    (crossW l r 1 w c (2 + d)) [target_tm]⊢* (scanW l r w (2 + c) d) := by
  rcases hw with ⟨e, hr, hl⟩
  refine ReachesStar.trans (crossW_next_1 l r w c d) ?_
  have hws := word_shift e (([1, 0, 1, 0] : zF) +> ((([1, 0] : zF) ^ c) +> (([0, 1, 0] : zF)
      +> ((([0, 1, 0] : zF) ^ d) +> r))))
  refine step_bridge (crossW_one_word_2 _ _) (by rw [← hws]; rfl) ?_
  refine ReachesStar.trans (hr _ _) ?_
  refine step_bridge (rootW_step_3 _ r c d) (by cfg_eq) ?_
  refine ReachesStar.trans (hl _ _) ?_
  exact step_end (crossW_next_4 l r w c d) (by cfg_eq) (by cfg_eq)

theorem scan_pair (l r : zB) (n d : Nat) :
    ((((([1, 0] : zF) ^ (2 + n * 2)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF)
        ^ (2 + n * 2 + d)) +> r)))) [target_tm]⊢*
    (scanW l r (([1, 0, 1, 0, 0, 1] : zF) ^ n) (1 + n * 2) d) := by
  refine step_bridge (scan_pair_1 l r n d) (by cfg_eq) ?_
  refine step_bridge (Incs1 l (([1, 0] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r)) 1 1 0 0 n)
      (by cfg_eq) ?_
  exact step_end (edge1 l ((([0, 1, 0] : zF) ^ d) +> r) (1 + n) (n * 2)) (by cfg_eq) (by cfg_eq)

theorem scanW_join (l r : zB) (v : zF) (c : Nat) (w : zF) (c' d : Nat) :
    (scanW l (link w c' d r) v c 0) [target_tm]⊢*
    (scanW l r (v ++ ([1, 0] : zF) ^ (1 + c) ++ [1, 0, 1, 0, 0, 1] ++ w) c' d) :=
  step_eq (by cfg_eq)

theorem Route_scan_zero (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) (hn : n = 0) (l : zB) (v : zF) :
    (scanW l r v c d) [target_tm]⊢* (scanW l R (v ++ w) C_out e) := by
  induction H generalizing v with
  | Route_done c n e r =>
    subst hn; exact step_eq (by cfg_eq)
  | Route_more c n z X Y c' d r m w C_out e R Hz HR ih =>
    have hn0 : n = 0 := by omega
    have hm0 : m = 0 := by omega
    subst hn0
    refine ReachesStar.trans (scanW_join l r v c z c' d) ?_
    exact step_end (ih hm0 (v ++ ([1, 0] : zF) ^ (1 + c) ++ [1, 0, 1, 0, 0, 1] ++ z)) (by cfg_eq)
        (by cfg_eq)

theorem Route_next (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) (hn : n = 1) (l : zB) (v x y : zF) (HW : Word v x y) :
    (crossW l r 1 v c d) [target_tm]⊢* (scanW l R (v ++ w) C_out e) := by
  induction H generalizing v x y with
  | Route_done c n e r =>
    subst hn
    exact step_end (crossW_next l r v x y c e HW) (by cfg_eq) (by cfg_eq)
  | Route_more c n z X Y c' d r m w C_out e R Hz HR ih =>
    rcases n with _ | n
    · have hm1 : m = 1 := by omega
      refine step_bridge (crossW_join l r 1 v c z c' d) (by cfg_eq) ?_
      exact step_end (ih hm1 _ _ _ (Word_link v x y (1 + c) z X Y HW Hz)) (by cfg_eq) (by cfg_eq)
    · have hn0 : n = 0 := by omega
      have hm0 : m = 0 := by omega
      subst hn0; subst hm0
      refine step_bridge (crossW_next l (link z c' d r) v x y c 0 HW) (by cfg_eq) ?_
      refine ReachesStar.trans (scanW_join l r v (2 + c) z c' d) ?_
      exact step_end (Route_scan_zero _ _ _ _ _ _ _ _ HR rfl l (v ++ ([1, 0] : zF) ^ (3 + c)
          ++ [1, 0, 1, 0, 0, 1] ++ z)) (by cfg_eq) (by cfg_eq)

theorem Route_scan (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : Route c d r n w C_out e R) (a : Nat) (l : zB) (v x y : zF) (Ha : a ≤ n) (HW : Word v x y) :
    ∃ c' d' r' u z, Route c' d' r' (n - a) z C_out e R ∧ w = u ++ z ∧
      (∃ X Y, Word u X Y) ∧
      (scanW ((([1, 0] : zF) ^ (a * 2)) +> l) r v c d) [target_tm]⊢*
        (scanW l r' ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ v ++ u) c' d') := by
  rcases a with _ | a
  · refine ⟨c, d, r, [], w, Route_eq H, rfl, ⟨[], [], Word_nil⟩, step_eq (by cfg_eq)⟩
  · rcases Route_cut c d r n w C_out e R H a (by omega) with ⟨c1, d1, r1, u0, z0, H0, H1, E0⟩
    rcases Route_cut c1 d1 r1 (n - a) z0 C_out e R H1 1 (by omega) with ⟨c2, d2, r2, u1, z1, H2, H3,
        E1⟩
    rcases Route_word _ _ _ _ _ _ _ _ H0 with ⟨X, Y, HU⟩
    rcases Route_word _ _ _ _ _ _ _ _ H2 with ⟨X1, Y1, HU1⟩
    refine ⟨c2, d2, r2, u0 ++ u1, z1, Route_eq H3, by rw [E0, E1, List.append_assoc], ⟨X ++ X1,
        Y ++ Y1, Word_app _ _ _ _ _ _ HU HU1⟩, ?_⟩
    have HV : Word ([1, 0, 1, 0, 0, 1] ++ v) ([1, 0, 0, 1, 1, 0] ++ x) ([0, 1, 1, 0, 1, 1] ++ y) :=
      Word_app _ _ _ _ _ _ Word_V HW
    refine step_bridge (scanW_entry l r (1 + a * 2) v c d) (by cfg_eq) ?_
    refine step_bridge ((Route_flow _ _ _ _ _ _ _ _ H0 _ _ _ HV).flow_cross l 1 0) (by cfg_eq) ?_
    have HZ : Word ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ [1, 0, 1, 0, 0, 1] ++ v ++ u0)
                   ((([1, 0, 0, 1, 1, 0] : zF) ^ a) ++ [1, 0, 0, 1, 1, 0] ++ x ++ X)
                   ((([0, 1, 1, 0, 1, 1] : zF) ^ a) ++ [0, 1, 1, 0, 1, 1] ++ y ++ Y) :=
      Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_pow _ _ _ a Word_V)
          Word_V) HW) HU
    exact step_end (Route_next _ _ _ _ _ _ _ _ H2 rfl l _ _ _ HZ) (by cfg_eq) (by cfg_eq)

def Counter (r : zB) (n : Nat) (w : zF) (C_out e : Nat) : Prop :=
  ∃ d s, r = ((([0, 1, 0] : zF) ^ (2 + d)) +> s) ∧ Route 1 d s n w C_out e default

theorem Counter_eq {r1 r2 : zB} {n1 n2 : Nat} {w1 w2 : zF} {C1 C2 e1 e2 : Nat}
    (h : Counter r1 n1 w1 C1 e1)
    (hr : r1 = r2 := by cfg_eq) (hn : n1 = n2 := by omega)
    (hw : w1 = w2 :=
        by simp only
            [list_pow_zero, list_pow_one, List.append_nil, List.nil_append, List.append_assoc])
    (hC : C1 = C2 := by omega) (he : e1 = e2 := by omega) :
    Counter r2 n2 w2 C2 e2 := by
  subst hr; subst hn; subst hw; subst hC; subst he; exact h

theorem Counter_step (l r : zB) (n : Nat) (w : zF) (C_out e a b : Nat)
    (HR : Counter r n w C_out e) (Ha : a ≤ n) :
    ∃ r', Counter r' (n - a + b) ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
        ^ (1 + a)) ++ w) C_out e ∧
      ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l))
          <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
        (l <{{C}} (([0, 1] : zF) +> r')) := by
  rcases HR with ⟨d, s, rfl, HR⟩
  rcases Route_scan 1 d s n w C_out e default HR a ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l)
      [] [] [] Ha Word_nil with
    ⟨c', d', s', u, z, HZ, EW, ⟨X, Y, HU⟩, HS⟩
  refine ⟨((([0, 1, 0] : zF) ^ (2 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u)
      c' d' s'), ?_, ?_⟩
  · refine ⟨b * 2, link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) c' d' s', rfl, ?_⟩
    have HV : Word ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) ((([1, 0, 0, 1, 1, 0] : zF) ^ a) ++ X)
        ((([0, 1, 1, 0, 1, 1] : zF) ^ a) ++ Y) :=
      Word_app _ _ _ _ _ _ (Word_pow _ _ _ a Word_V) HU
    have heq : 1 + b * 2 + 1 = 2 + b * 2 := by omega
    exact Route_eq (Route.Route_more 1 b _ _ _ c' d' s' (n - a) z C_out e default HV HZ)
      (hw := by rw [heq, EW, pow_add_1]; simp only [List.append_assoc])
  · refine step_bridge (scan_pair ((([1, 0] : zF) ^ (a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2))
        +> l)) s 0 d) (by cfg_eq) ?_
    refine ReachesStar.trans HS ?_
    exact step_end (pass_011 l (link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) c' d' s') (2 + b * 2))
        (by cfg_eq) (by cfg_eq)

theorem Counter_root (r : zB) (n : Nat) (w : zF) (C_out e s : Nat)
    (HR : Counter r n w C_out e) (Hs : s ≤ n) :
    ((((([1, 0] : zF) ^ (3 + s * 2)) +> default) <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
      (rootW default (2 + (n - s) * 2) ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + s)) ++ w) C_out e) := by
  rcases HR with ⟨d, r0, rfl, HR⟩
  rcases Route_cut 1 d r0 n w C_out e default HR s Hs with ⟨c', d', r', u, z, HU, HZ, EW⟩
  rcases Route_word _ _ _ _ _ _ _ _ HU with ⟨X, Y, HW⟩
  refine step_bridge (scan_pair ((([1, 0] : zF) ^ (1 + s * 2)) +> default) r0 0 d) (by cfg_eq) ?_
  refine step_bridge (scanW_entry default r0 (s * 2) [] 1 d) (by cfg_eq) ?_
  refine step_bridge ((Route_flow _ _ _ _ _ _ _ _ HU _ _ _ Word_V).flow_cross default 0 0)
      (by cfg_eq) ?_
  have hcz := crossW_zero r' ((([1, 0, 1, 0, 0, 1] : zF) ^ s) ++ [1, 0, 1, 0, 0, 1] ++ u) c' d'
  refine ReachesStar.trans hcz ?_
  have HV : Word ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + s)) ++ u) ((([1, 0, 0, 1, 1, 0] : zF) ^ (1 + s))
      ++ X) ((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + s)) ++ Y) :=
    Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1 + s) Word_V) HW
  refine step_end ((Route_flow _ _ _ _ _ _ _ _ HZ _ _ _ HV).flow_root 2 0) ?_ ?_
  · rw [pow_add_1]; cfg_eq
  · rw [EW]; cfg_eq

theorem Counter_cross (r : zB) (n : Nat) (w : zF) (C_out e s : Nat)
    (HR : Counter r n w C_out e) :
    ((((([1, 0] : zF) ^ (5 + n * 2 + s * 2)) +> default) <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
      (crossW default default (2 + s * 2) ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + n)) ++ w)
          C_out e) := by
  rcases HR with ⟨d, r0, rfl, HR⟩
  refine step_bridge (scan_pair ((([1, 0] : zF) ^ (3 + n * 2 + s * 2)) +> default) r0 0 d)
      (by cfg_eq) ?_
  refine step_bridge (scanW_entry default r0 (2 + n * 2 + s * 2) [] 1 d) (by cfg_eq) ?_
  refine step_end ((Route_flow _ _ _ _ _ _ _ _ HR _ _ _ Word_V).flow_cross default (2 + s * 2) 0)
      (by cfg_eq) ?_
  rw [pow_add_1]; cfg_eq

theorem rootW_terminal (a : Nat) (w x y : zF) (c e : Nat) (He : e ≤ 1) (HW : Word w x y) :
    (rootW default a w c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> (y.reverse +> ((([1, 0] : zF) ^ (3 + a)) +> default)))
        {{B}}> default)) := by
  rcases e with _ | _ | e
  · exact step_end (rootW_finish_word0 a w x y c HW) (by cfg_eq) (by cfg_eq)
  · exact step_end (rootW_finish_word1 a w x y c HW) (by cfg_eq) (by cfg_eq)
  · omega

theorem crossW_terminal (l : zB) (a : Nat) (w x y : zF) (c e : Nat) (He : e ≤ 1) (HW : Word w x y) :
    (crossW l default (2 + a) w c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> (y.reverse +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF)
        ^ a) +> l)))) {{B}}> default)) := by
  rcases e with _ | _ | e
  · exact step_end (crossW_finish_word0 l a w x y c HW) (by cfg_eq) (by cfg_eq)
  · exact step_end (crossW_finish_word1 l a w x y c HW) (by cfg_eq) (by cfg_eq)
  · omega

theorem Counter_normal (r : zB) (n : Nat) (w : zF) (C_out e s : Nat) (x y : zF)
    (HR : Counter r n w C_out e) (Hs : s ≤ n) (He : e ≤ 1) (HW : Word w x y) :
    ((((([1, 0] : zF) ^ (3 + s * 2)) +> default) <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + s) ++ y).reverse)
        +> ((([1, 0] : zF) ^ (5 + (n - s) * 2)) +> default))) {{B}}> default)) := by
  refine evstep_progress ?_ (by ne_cfg)
  refine ReachesStar.trans (Counter_root r n w C_out e s HR Hs) ?_
  exact step_end (rootW_terminal (2 + (n - s) * 2)
      _ _ _ C_out e He (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1 + s) Word_V) HW)) (by cfg_eq)
          (by cfg_eq)

theorem Counter_overflow (r : zB) (n : Nat) (w : zF) (C_out e s : Nat) (x y : zF)
    (HR : Counter r n w C_out e) (He : e ≤ 1) (HW : Word w x y) :
    ((((([1, 0] : zF) ^ (5 + n * 2 + s * 2)) +> default) <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + n) ++ y).reverse)
        +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF) ^ (s * 2)) +> default))))
            {{B}}> default)) := by
  refine evstep_progress ?_ (by ne_cfg)
  refine ReachesStar.trans (Counter_cross r n w C_out e s HR) ?_
  exact step_end (crossW_terminal default (s * 2)
      _ _ _ C_out e He (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (1 + n) Word_V) HW)) (by cfg_eq)
          (by cfg_eq)

def column_side (l : zB) : List (Nat × Nat) → zB
  | [] => l
  | (a, b) :: cs =>
    ((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> column_side l cs))

def column_word : List (Nat × Nat) → zF
  | [] => []
  | (a, b) :: cs =>
    column_word cs ++ ([1, 0] : zF) ^ (2 + b * 2) ++ ([1, 0, 1, 0, 0, 1] : zF) ^ (1 + a)

def column_image : List (Nat × Nat) → zF
  | [] => []
  | (a, b) :: cs =>
    column_image cs ++ ([0, 1] : zF) ^ (2 + b * 2) ++ ([0, 1, 1, 0, 1, 1] : zF) ^ (1 + a)

inductive ColumnRun : Nat → List (Nat × Nat) → Nat → Prop where
  | Columns_nil (n : Nat) : ColumnRun n [] n
  | Columns_cons (n a b : Nat) (cs : List (Nat × Nat)) (m : Nat) :
      a ≤ n → ColumnRun (n - a + b) cs m → ColumnRun n ((a, b) :: cs) m

theorem column_word_spec (cs : List (Nat × Nat)) : ∃ x, Word (column_word cs)
    x (column_image cs) := by
  induction cs with
  | nil => exact ⟨[], Word_nil⟩
  | cons ab cs ih =>
    rcases ab with ⟨a, b⟩
    rcases ih with ⟨x, HW⟩
    exact ⟨_, Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ HW (Word_pow _ _ _ (2 + b * 2) Word_U))
        (Word_pow _ _ _ (1 + a) Word_V)⟩

theorem Counter_columns (n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : ColumnRun n cs m)
    (l r : zB) (w : zF) (C_out e : Nat) (HR : Counter r n w C_out e) :
    ∃ r', Counter r' m (column_word cs ++ w) C_out e ∧
      (column_side l cs <{{C}} (([0, 1] : zF) +> r)) [target_tm]⊢* (l <{{C}} (([0, 1] : zF)
          +> r')) := by
  induction H generalizing l r w with
  | Columns_nil n => exact ⟨r, HR, step_eq rfl⟩
  | Columns_cons n a b cs m Ha H ih =>
    rcases Counter_step (column_side l cs) r n w C_out e a b HR Ha with ⟨r1, H1, HS⟩
    rcases ih l r1 _ H1 with ⟨r2, H2, HT⟩
    refine ⟨r2, Counter_eq H2 (hw := by dsimp [column_word]; simp only [List.append_assoc]),
        ReachesStar.trans HS HT⟩

theorem Counter_columns_normal (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (cs : List (Nat × Nat))
    (m s : Nat) (x y : zF)
    (HR : Counter r n w C_out e) (HC : ColumnRun n cs m) (Hs : s ≤ m) (He : e ≤ 1)
    (HW : Word (column_word cs ++ w) x y) :
    (column_side (((([1, 0] : zF) ^ (3 + s * 2)) +> default)) cs <{{C}} (([0, 1] : zF) +> r))
        [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + s) ++ y).reverse)
        +> ((([1, 0] : zF) ^ (5 + (m - s) * 2)) +> default))) {{B}}> default)) := by
  rcases Counter_columns n cs m HC (((([1, 0] : zF) ^ (3 + s * 2)) +> default))
      r w C_out e HR with ⟨r', HT, HS⟩
  exact evstep_progress_trans HS (Counter_normal r' m _ C_out e s x y HT Hs He HW)

theorem Counter_columns_overflow (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (cs : List (Nat × Nat))
    (m s : Nat) (x y : zF)
    (HR : Counter r n w C_out e) (HC : ColumnRun n cs m) (He : e ≤ 1)
    (HW : Word (column_word cs ++ w) x y) :
    (column_side (((([1, 0] : zF) ^ (5 + m * 2 + s * 2)) +> default)) cs <{{C}} (([0, 1] : zF)
        +> r)) [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + m) ++ y).reverse)
        +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF) ^ (s * 2)) +> default))))
            {{B}}> default)) := by
  rcases Counter_columns n cs m HC (((([1, 0] : zF) ^ (5 + m * 2 + s * 2)) +> default))
      r w C_out e HR with ⟨r', HT, HS⟩
  exact evstep_progress_trans HS (Counter_overflow r' m _ C_out e s x y HT He HW)

theorem Counter_base (n e : Nat) :
    Counter (((([0, 1, 0] : zF) ^ (2 + n * 2 + e)) +> default)) n [] (1 + n * 2) e :=
  ⟨n * 2 + e, default, by cfg_eq, Route_eq (Route.Route_done 1 n e default)⟩

theorem Counter_link (b : Nat) (v x y : zF) (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat)
    (HV : Word v x y) (HR : Route c d r n w C_out e default) :
    Counter (((([0, 1, 0] : zF) ^ (2 + b * 2)) +> link v c d r)) (b + n)
      ((([1, 0] : zF) ^ (2 + b * 2)) ++ [1, 0, 1, 0, 0, 1] ++ v ++ w) C_out e := by
  have heq : 1 + b * 2 + 1 = 2 + b * 2 := by omega
  exact ⟨b * 2, link v c d r, rfl,
      Route_eq (Route.Route_more 1 b v x y c d r n w C_out e default HV HR) (hw := by rw [heq])⟩

theorem Counter_gap (g b d e : Nat) :
    Counter (((([0, 1, 0] : zF) ^ (2 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) (1 + g * 2)
        (d * 2 + e) default))
      (b + d) ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + g)))
          (1 + g * 2 + d * 2) e := by
  have h1 := Counter_link b _ _ _ (1 + g * 2) (d * 2 + e) default d [] (d * 2 + (1 + g * 2)) e
    (Word_pow _ _ _ g Word_V) (Route.Route_done (1 + g * 2) d e default)
  exact Counter_eq h1 (hw := by rw [pow_add_1]; simp only [List.append_nil, List.append_assoc])

theorem counter_begin (l : zB) (p b : Nat) (HP : P p) :
    ((((([1, 0] : zF) ^ p) +> ((([1, 1, 0] : zF) ^ b) +> l)) {{B}}> default)) [target_tm]⊢*
    (l <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (p + b)) +> default))) := by
  refine ReachesStar.trans (HP ((([1, 1, 0] : zF) ^ b) +> l)) ?_
  exact step_end (pass_011 l ((([0, 1, 0] : zF) ^ p) +> default) b) (by cfg_eq) (by cfg_eq)

theorem counter_begin_gap (l : zB) (g b d e : Nat) (HP : P (2 + g * 2 + (d * 2 + e))) :
    ((((([1, 0] : zF) ^ ((2 + g * 2 + (d * 2 + e)) + (2 + g * 2))) +> ((([1, 1, 0] : zF)
        ^ (2 + b * 2)) +> l)) {{B}}> default)) [target_tm]⊢*
    (l <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (2 + b * 2))
        +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) (1 + g * 2) (d * 2 + e) default))) := by
  refine ReachesStar.trans (return_even ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l) g (d * 2 + e) HP) ?_
  exact step_end (pass_011 l _ (2 + b * 2)) (by cfg_eq) (by cfg_eq)

inductive SectionStart (l : zB) : Nat → zF → Nat → Nat → Cfg (Fin 2) (Fin 6) → Prop where
  | Start_good (d b e : Nat) : P (2 + d * 2 + e) →
      SectionStart l (1 + d + b) [] (3 + d * 2 + b * 2) e
        ((((([1, 0] : zF) ^ (2 + d * 2 + e)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l))
            {{B}}> default))
  | Start_gap (g b d e : Nat) : P (2 + g * 2 + (d * 2 + e)) →
      SectionStart l (b + d) ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
          ^ (1 + g)))
        (1 + g * 2 + d * 2) e
        ((((([1, 0] : zF) ^ ((2 + g * 2 + (d * 2 + e)) + (2 + g * 2))) +> ((([1, 1, 0] : zF)
            ^ (2 + b * 2)) +> l)) {{B}}> default))

theorem SectionStart_spec (l : zB) (n : Nat) (w : zF) (C_out e : Nat) (c : Cfg (Fin 2) (Fin 6))
    (H : SectionStart l n w C_out e c) :
    ∃ r, Counter r n w C_out e ∧ c [target_tm]⊢* (l <{{C}} (([0, 1] : zF) +> r)) := by
  rcases H with ⟨d, b, e, HP⟩ | ⟨g, b, d, e, HP⟩
  · refine ⟨((([0, 1, 0] : zF) ^ ((2 + d * 2 + e) + (2 + b * 2))) +> default), ?_,
        counter_begin l (2 + d * 2 + e) (2 + b * 2) HP⟩
    exact Counter_eq (Counter_base (1 + d + b) e)
  · exact ⟨_, Counter_gap g b d e, counter_begin_gap l g b d e HP⟩

theorem section_columns_normal (n : Nat) (w : zF) (C_out e : Nat) (c : Cfg (Fin 2) (Fin 6))
    (cs : List (Nat × Nat)) (m s : Nat) (x y : zF)
    (HS : SectionStart (column_side (((([1, 0] : zF) ^ (3 + s * 2)) +> default)) cs) n w C_out e c)
    (HC : ColumnRun n cs m) (Hs : s ≤ m) (He : e ≤ 1) (HW : Word (column_word cs ++ w) x y) :
    c [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + s) ++ y).reverse)
        +> ((([1, 0] : zF) ^ (5 + (m - s) * 2)) +> default))) {{B}}> default)) := by
  rcases SectionStart_spec _ _ _ _ _ _ HS with ⟨r, HR, HT⟩
  exact evstep_progress_trans HT (Counter_columns_normal r n w C_out e cs m s x y HR HC Hs He HW)

theorem section_columns_overflow (n : Nat) (w : zF) (C_out e : Nat) (c : Cfg (Fin 2) (Fin 6))
    (cs : List (Nat × Nat)) (m s : Nat) (x y : zF)
    (HS : SectionStart (column_side (((([1, 0] : zF) ^ (5 + m * 2 + s * 2)) +> default)) cs)
        n w C_out e c)
    (HC : ColumnRun n cs m) (He : e ≤ 1) (HW : Word (column_word cs ++ w) x y) :
    c [target_tm]⊢⁺
    ((((([1, 0] : zF) ^ (1 + C_out + e)) +> (((([0, 1, 1, 0, 1, 1] : zF) ^ (1 + m) ++ y).reverse)
        +> ((([1, 1, 0] : zF) ^ 3) +> ((([1, 0] : zF) ^ (s * 2)) +> default))))
            {{B}}> default)) := by
  rcases SectionStart_spec _ _ _ _ _ _ HS with ⟨r, HR, HT⟩
  exact evstep_progress_trans HT (Counter_columns_overflow r n w C_out e cs m s x y HR HC He HW)

inductive EraseWord : zF → Nat → Nat → Prop where
  | Erase_nil : EraseWord [] 0 0
  | Erase_V (n : Nat) (w : zF) (u v : Nat) :
      EraseWord w u v → EraseWord ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) u (n + v)
  | Erase_pair (j k : Nat) (w : zF) (u v : Nat) :
      EraseWord w u v → EraseWord ((([1, 0] : zF) ^ (2 + j * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
          ^ (1 + k)) ++ w) (1 + j + u) (1 + k + v)

theorem EraseWord_eq {w1 w2 : zF} {u1 u2 v1 v2 : Nat}
    (h : EraseWord w1 u1 v1)
    (hw : w1 = w2 :=
        by simp only
            [pow_add_1, list_pow_zero, list_pow_one, List.append_nil, List.nil_append,
                List.append_assoc])
    (hu : u1 = u2 := by omega) (hv : v1 = v2 := by omega) :
    EraseWord w2 u2 v2 := by
  subst hw; subst hu; subst hv; exact h

structure Pass (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6))
    (R : Nat → Nat → Cfg (Fin 2) (Fin 6))
    (D : zB → Nat → Nat → Cfg (Fin 2) (Fin 6))
    (T : Nat → Nat → Cfg (Fin 2) (Fin 6)) (n : Nat) : Prop where
  pass_flow : Flow C R D T n
  pass_even : ∀ s v b, s + v + 1 = n → (C default (2 + s * 2) b) [target_tm]⊢* (T (2 + v * 2)
      (1 + s + b))

theorem Pass_id (C : zB → Nat → Nat → Cfg (Fin 2) (Fin 6)) (R : Nat → Nat → Cfg (Fin 2) (Fin 6)) :
    Pass C R C R 0 :=
  ⟨Flow_id C R, fun s v b h => by omega⟩

theorem Pass_eq {C1 C2 R1 R2 D1 D2 T1 T2} {n1 n2 : Nat}
    (h : Pass C1 R1 D1 T1 n1)
    (hC : ∀ l a b, C1 l a b = C2 l a b := by intros; cfg_eq)
    (hR : ∀ a b, R1 a b = R2 a b := by intros; cfg_eq)
    (hD : ∀ l a b, D1 l a b = D2 l a b := by intros; cfg_eq)
    (hT : ∀ a b, T1 a b = T2 a b := by intros; cfg_eq)
    (hn : n1 = n2 := by omega) :
    Pass C2 R2 D2 T2 n2 := by
  have eC : C1 = C2 := by funext l a b; exact hC l a b
  have eR : R1 = R2 := by funext a b; exact hR a b
  have eD : D1 = D2 := by funext l a b; exact hD l a b
  have eT : T1 = T2 := by funext a b; exact hT a b
  subst eC; subst eR; subst eD; subst eT; subst hn; exact h

theorem Pass_trans {C R D T F U} {n m : Nat} (h1 : Pass C R D T n) (h2 : Pass D T F U m) :
    Pass C R F U (n + m) := by
  refine ⟨Flow_trans h1.pass_flow h2.pass_flow, ?_⟩
  intro s v b H
  by_cases hle : n ≤ s
  · refine step_bridge (h1.pass_flow.flow_cross default (2 + (s - n) * 2) b) (by cfg_eq) ?_
    exact step_end (h2.pass_even (s - n) v (n + b) (by omega)) (by cfg_eq) (by cfg_eq)
  · refine ReachesStar.trans (h1.pass_even s (n - s - 1) b (by omega)) ?_
    exact step_end (h2.pass_flow.flow_root (2 + (n - s - 1) * 2) (1 + s + b)) (by cfg_eq)
        (by cfg_eq)

theorem Pass_W (r : zB) (c d : Nat) :
    Pass (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (2 + d))
         (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d)
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) d) 1 := by
  refine ⟨Flow_W r c d, ?_⟩
  intro s v b E
  have hs : s = 0 := by omega
  have hv : v = 0 := by omega
  subst hs; subst hv
  refine step_bridge ((Flow_W r c d).flow_cross default 0 b) (by cfg_eq) ?_
  exact step_end (crossW_zero r (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + b)) (2 + c) d) (by cfg_eq)
      (by cfg_eq)

theorem Pass_V (r : zB) (c e : Nat) :
    Pass (fun l a b => crossV l r a b (3 + c) (1 + e))
         (fun a b => rootV r a b (3 + c) (1 + e))
         (fun l a b => crossV l r a b (4 + c) e)
         (fun a b => rootV r a b (4 + c) e) 2 := by
  refine ⟨Flow_V r c e, ?_⟩
  intro s v b E
  rcases s with _ | _ | s
  · have hv : v = 1 := by omega
    subst hv
    exact step_end (crossV_two r b c e) (by cfg_eq) (by cfg_eq)
  · have hv : v = 0 := by omega
    subst hv
    refine step_bridge (crossV_step default r 0 b c e) (by cfg_eq) ?_
    exact step_end (crossV_zero r (2 + b) (4 + c) e) (by cfg_eq) (by cfg_eq)
  · omega

theorem Pass_Z (r : zB) (c e : Nat) :
    Pass (fun l a b => crossZ l r a b (3 + c) (2 + e))
         (fun a b => rootZ r a b (3 + c) (2 + e))
         (fun l a b => crossZ l r a b (3 + c) e)
         (fun a b => rootZ r a b (3 + c) e) 2 := by
  refine ⟨Flow_Z r c e, ?_⟩
  intro s v b E
  rcases s with _ | _ | s
  · have hv : v = 1 := by omega
    subst hv
    exact step_end (crossZ_two r b c e) (by cfg_eq) (by cfg_eq)
  · have hv : v = 0 := by omega
    subst hv
    refine step_bridge (crossZ_step default r 0 b c e) (by cfg_eq) ?_
    exact step_end (crossZ_zero r (2 + b) (3 + c) e) (by cfg_eq) (by cfg_eq)
  · omega

theorem Pass_V_end (r : zB) (c e : Nat) :
    Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
         (fun a b => rootV ((([1, 0] : zF) ^ (1 + e)) +> r) a b (3 + c) 0)
         (fun l a b => crossZ l r a b (4 + c) e)
         (fun a b => rootZ r a b (4 + c) e) 2 := by
  refine ⟨Flow_V_end r c e, ?_⟩
  intro s v b E
  rcases s with _ | _ | s
  · have hv : v = 1 := by omega
    subst hv
    exact step_end (crossVend_two r b c e) (by cfg_eq) (by cfg_eq)
  · have hv : v = 0 := by omega
    subst hv
    refine step_bridge (crossV_end default r 0 b c e) (by cfg_eq) ?_
    exact step_end (crossZ_zero r (2 + b) (4 + c) e) (by cfg_eq) (by cfg_eq)
  · omega

theorem Pass_Ws (r : zB) (c d n : Nat) :
    Pass (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (n * 2 + d))
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c (n * 2 + d))
         (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (n * 2 + c) d)
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (n * 2 + c) d) n := by
  induction n generalizing c with
  | zero => exact Pass_eq (Pass_id _ _)
  | succ n ih =>
    have h1 : Pass (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c ((n + 1) * 2 + d))
                   (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c ((n + 1) * 2 + d))
                   (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) (n * 2 + d))
                   (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) (n * 2 + d)) 1 :=
      Pass_eq (Pass_W r c (n * 2 + d))
    exact Pass_eq (Pass_trans h1 (ih (2 + c)))

theorem Pass_Vs (r : zB) (c e n : Nat) :
    Pass (fun l a b => crossV l r a b (3 + c) (e + n))
         (fun a b => rootV r a b (3 + c) (e + n))
         (fun l a b => crossV l r a b (3 + c + n) e)
         (fun a b => rootV r a b (3 + c + n) e) (n * 2) := by
  induction n generalizing c e with
  | zero => exact Pass_eq (Pass_id _ _)
  | succ n ih =>
    have h1 : Pass (fun l a b => crossV l r a b (3 + c) (e + (n + 1)))
                   (fun a b => rootV r a b (3 + c) (e + (n + 1)))
                   (fun l a b => crossV l r a b (3 + (1 + c)) (e + n))
                   (fun a b => rootV r a b (3 + (1 + c)) (e + n)) 2 :=
      Pass_eq (Pass_V r c (e + n))
    exact Pass_eq (Pass_trans h1 (ih (1 + c) e))

theorem Pass_Zs (r : zB) (c e n : Nat) :
    Pass (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
         (fun a b => rootZ r a b (3 + c) (e + n * 2))
         (fun l a b => crossZ l r a b (3 + c) e)
         (fun a b => rootZ r a b (3 + c) e) (n * 2) := by
  induction n generalizing e with
  | zero => exact Pass_eq (Pass_id _ _)
  | succ n ih =>
    have h1 : Pass (fun l a b => crossZ l r a b (3 + c) (e + (n + 1) * 2))
                   (fun a b => rootZ r a b (3 + c) (e + (n + 1) * 2))
                   (fun l a b => crossZ l r a b (3 + c) (e + n * 2))
                   (fun a b => rootZ r a b (3 + c) (e + n * 2)) 2 :=
      Pass_eq (Pass_Z r c (e + n * 2))
    exact Pass_eq (Pass_trans h1 (ih e))

theorem Pass_Z_to_V (r : zB) (c k : Nat) :
    Pass (fun l a b => crossZ l ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) a b (3 + c) 1)
         (fun a b => rootZ ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) a b (3 + c) 1)
         (fun l a b => crossV l r a b (3 + c) k)
         (fun a b => rootV r a b (3 + c) k) 2 :=
  Pass_eq (Pass_Z (([1, 0, 0, 1] : zF) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ k) +> r)) c 0)

theorem Pass_Z_back (r : zB) (c d : Nat) :
    Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + d)) +> r))
                         a b (4 + c) 0)
         (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + d)) +> r)) a b (4 + c) 0)
         (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) (2 + d))
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + c) (2 + d)) 2 :=
  Pass_eq (Pass_Z (([1, 0] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r)) (1 + c) 0)

theorem Pass_Z_empty (c : Nat) :
    Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b (4 + c) 0)
         (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b (4 + c) 0)
         (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) 0)
         (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + c) 0) 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l a b; exact step_end (crossZ_empty l a b c) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootZ_empty a b c) (by cfg_eq) (by cfg_eq)
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv
      exact step_end (crossZ_empty_one b c) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      exact step_end (crossZ_empty_three b c) (by cfg_eq) (by cfg_eq)
    · omega
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv
      exact step_end (crossZ_empty_two b c) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      refine step_bridge (crossZ_empty default 0 b c) (by cfg_eq) ?_
      exact step_end (crossW_zero default (([1, 0, 1, 0, 0, 1] : zF) ^ (2 + b)) (2 + c) 0)
          (by cfg_eq) (by cfg_eq)
    · omega

theorem crossW_last_one (b c e : Nat) (He : e ≤ 1) :
    (crossW default default 1 (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> (([1, 0] : zF)
        +> default))) {{B}}> default)) :=
  crossW_short b c e He

theorem EraseWord_app (w : zF) (u v : Nat) (z : zF) (x y : Nat)
    (H : EraseWord w u v) (K : EraseWord z x y) : EraseWord (w ++ z) (u + x) (v + y) := by
  induction H with
  | Erase_nil => exact EraseWord_eq K
  | Erase_V n w u v _ ih => exact EraseWord_eq (EraseWord.Erase_V n (w ++ z) (u + x) (v + y) ih)
  | Erase_pair j k w u v _ ih =>
    exact EraseWord_eq (EraseWord.Erase_pair j k (w ++ z) (u + x) (v + y) ih)

theorem EraseWord_word (w : zF) (u v : Nat) (H : EraseWord w u v) : ∃ x y, Word w x y := by
  induction H with
  | Erase_nil => exact ⟨[], [], Word_nil⟩
  | Erase_V n w u v _ ih =>
    rcases ih with ⟨X, Y, HW⟩
    exact ⟨_, _, Word_app _ _ _ _ _ _ (Word_pow _ _ _ n Word_V) HW⟩
  | Erase_pair j k w u v _ ih =>
    rcases ih with ⟨X, Y, HW⟩
    exact ⟨_, _, Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (2 + j * 2) Word_U)
        (Word_pow _ _ _ (1 + k) Word_V)) HW⟩

inductive RRoute : Nat → Nat → zB → Nat → zF → Nat → Nat → zB → Prop where
  | RRoute_done (j n e : Nat) (r : zB) : RRoute (1 + j * 2) (n * 2 + e) r n [] (1 + (j + n) * 2) e r
  | RRoute_more (j n : Nat) (v : zF) (u q c' d : Nat) (r : zB) (m : Nat) (w : zF) (C_out e : Nat)
      (R : zB) :
      EraseWord v u q → RRoute c' d r m w C_out e R →
      RRoute (1 + j * 2) (n * 2) (link v c' d r) (n + m)
        (([1, 0] : zF) ^ (2 + (j + n) * 2) ++ [1, 0, 1, 0, 0, 1] ++ v ++ w) C_out e R

theorem RRoute_eq {c1 c2 d1 d2 : Nat} {r1 r2 : zB} {n1 n2 : Nat} {w1 w2 : zF} {C1 C2 e1 e2 : Nat}
    {R1 R2 : zB}
    (h : RRoute c1 d1 r1 n1 w1 C1 e1 R1)
    (hc : c1 = c2 := by omega) (hd : d1 = d2 := by omega) (hr : r1 = r2 := by cfg_eq)
    (hn : n1 = n2 := by omega)
    (hw : w1 = w2 :=
        by simp only
            [list_pow_zero, list_pow_one, List.append_nil, List.nil_append, List.append_assoc])
    (hC : C1 = C2 := by omega) (he : e1 = e2 := by omega) (hR : R1 = R2 := by cfg_eq) :
    RRoute c2 d2 r2 n2 w2 C2 e2 R2 := by
  subst hc; subst hd; subst hr; subst hn; subst hw; subst hC; subst he; subst hR; exact h

theorem RRoute_forget (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : RRoute c d r n w C_out e R) : Route c d r n w C_out e R := by
  induction H with
  | RRoute_done j n e r => exact Route_eq (Route.Route_done (1 + j * 2) n e r)
  | RRoute_more j n v u q c' d r m w C_out e R HV HR ih =>
    rcases EraseWord_word v u q HV with ⟨X, Y, HW⟩
    have heq : 1 + n * 2 + (1 + j * 2) = 2 + (j + n) * 2 := by omega
    exact Route_eq (Route.Route_more (1 + j * 2) n v X Y c' d r m w C_out e R HW ih) (hw :=
        by rw [heq])

theorem RRoute_erase (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : RRoute c d r n w C_out e R) : ∃ u v, EraseWord w u v := by
  induction H with
  | RRoute_done => exact ⟨0, 0, EraseWord.Erase_nil⟩
  | RRoute_more j n z u q c' d r m w C_out e R HZ HR ih =>
    rcases ih with ⟨x, y, HW⟩
    refine ⟨1 + (j + n) + (u + x), 1 + (q + y), ?_⟩
    exact EraseWord_eq (EraseWord.Erase_pair (j + n) 0 (z ++ w) (u + x) (q + y)
        (EraseWord_app z u q w x y HZ HW))

theorem RRoute_cut (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : RRoute c d r n w C_out e R) (k : Nat) (Hk : k ≤ n) :
    ∃ c' d' r' u v, RRoute c d r k u c' d' r' ∧ RRoute c' d' r' (n - k)
        v C_out e R ∧ w = u ++ v := by
  induction H generalizing k with
  | RRoute_done j n e r =>
    refine ⟨1 + (j + k) * 2, (n - k) * 2 + e, r, [], [], ?_, ?_, rfl⟩
    · exact RRoute_eq (RRoute.RRoute_done j k ((n - k) * 2 + e) r)
    · exact RRoute_eq (RRoute.RRoute_done (j + k) (n - k) e r)
  | RRoute_more j n z x y c0 d0 r0 m w C_out e R HZ HR ih =>
    by_cases hle : k ≤ n
    · refine ⟨1 + (j + k) * 2, (n - k) * 2, link z c0 d0 r0, [], ([1, 0] : zF) ^ (2 + (j + n) * 2)
          ++ [1, 0, 1, 0, 0, 1] ++ z ++ w, ?_, ?_, rfl⟩
      · exact RRoute_eq (RRoute.RRoute_done j k ((n - k) * 2) (link z c0 d0 r0))
      · have heq : 2 + (j + k + (n - k)) * 2 = 2 + (j + n) * 2 := by omega
        exact RRoute_eq (RRoute.RRoute_more (j + k) (n - k) z x y c0 d0 r0 m w C_out e R HZ HR)
            (hw := by rw [heq])
    · rcases ih (k - n) (by omega) with ⟨c', d', r', u, v, HU, HV, EW⟩
      refine ⟨c', d', r', ([1, 0] : zF) ^ (2 + (j + n) * 2) ++ [1, 0, 1, 0, 0, 1] ++ z ++ u, v, ?_,
          ?_, ?_⟩
      · exact RRoute_eq (RRoute.RRoute_more j n z x y c0 d0 r0 (k - n) u c' d' r' HZ HU)
      · exact RRoute_eq HV
      · rw [EW]; simp only [List.append_assoc]

theorem scanW_consume (l : zB) (c d : Nat) (r : zB) (a : Nat) (u : zF) (c1 d1 : Nat) (r1 : zB)
    (v : zF) (c2 d2 : Nat) (r2 : zB) (w x y : zF)
    (HU : Route c d r a u c1 d1 r1) (HV : Route c1 d1 r1 1 v c2 d2 r2) (HW : Word w x y) :
    (scanW ((([1, 0] : zF) ^ (2 + a * 2)) +> l) r w c d) [target_tm]⊢*
    (scanW l r2 ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + a)) ++ w ++ u ++ v) c2 d2) := by
  rcases Route_word _ _ _ _ _ _ _ _ HU with ⟨X, Y, EU⟩
  have H1 : Word ([1, 0, 1, 0, 0, 1] ++ w) ([1, 0, 0, 1, 1, 0] ++ x) ([0, 1, 1, 0, 1, 1] ++ y) :=
    Word_app _ _ _ _ _ _ Word_V HW
  refine step_bridge (scanW_entry l r (1 + a * 2) w c d) (by cfg_eq) ?_
  refine step_bridge ((Route_flow _ _ _ _ _ _ _ _ HU _ _ _ H1).flow_cross l 1 0) (by cfg_eq) ?_
  have H2 : Word ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ [1, 0, 1, 0, 0, 1] ++ w ++ u)
                 ((([1, 0, 0, 1, 1, 0] : zF) ^ a) ++ [1, 0, 0, 1, 1, 0] ++ x ++ X)
                 ((([0, 1, 1, 0, 1, 1] : zF) ^ a) ++ [0, 1, 1, 0, 1, 1] ++ y ++ Y) :=
    Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_app _ _ _ _ _ _ (Word_pow _ _ _ a Word_V)
        Word_V) HW) EU
  refine step_end (Route_next _ _ _ _ _ _ _ _ HV rfl l _ _ _ H2) (by cfg_eq) ?_
  rw [pow_add_1]; cfg_eq

theorem RRoute_scan (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : RRoute c d r n w C_out e R) (a : Nat) (l : zB) (v x y : zF) (Ha : a ≤ n)
        (HW : Word v x y) :
    ∃ c' d' r' u z i j, RRoute c' d' r' (n - a) z C_out e R ∧ w = u ++ z ∧ EraseWord u i j ∧
      (scanW ((([1, 0] : zF) ^ (a * 2)) +> l) r v c d) [target_tm]⊢*
        (scanW l r' ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ v ++ u) c' d') := by
  rcases a with _ | a
  · refine ⟨c, d, r, [], w, 0, 0, RRoute_eq H, rfl, EraseWord.Erase_nil, step_eq (by cfg_eq)⟩
  · rcases RRoute_cut c d r n w C_out e R H a (by omega) with ⟨c1, d1, r1, u0, z0, H0, H1, E0⟩
    rcases RRoute_cut c1 d1 r1 (n - a) z0 C_out e R H1 1 (by omega) with ⟨c2, d2, r2, u1, z1, H2,
        H3, E1⟩
    rcases RRoute_erase _ _ _ _ _ _ _ _ H0 with ⟨i, j, EU0⟩
    rcases RRoute_erase _ _ _ _ _ _ _ _ H2 with ⟨k, q, EU1⟩
    refine ⟨c2, d2, r2, u0 ++ u1, z1, i + k, j + q, RRoute_eq H3, by rw [E0, E1, List.append_assoc],
        EraseWord_app _ _ _ _ _ _ EU0 EU1, ?_⟩
    exact step_end (scanW_consume l c d r a u0 c1 d1 r1 u1 c2 d2 r2 v x y (RRoute_forget _ _ _ _ _ _
        _ _ H0) (RRoute_forget _ _ _ _ _ _ _ _ H2) HW)
      (by cfg_eq) (by cfg_eq)

def RCounter (r : zB) (n : Nat) (w : zF) (C_out e : Nat) : Prop :=
  ∃ d s, r = ((([0, 1, 0] : zF) ^ (2 + d)) +> s) ∧ RRoute 1 d s n w C_out e default

theorem RCounter_eq {r1 r2 : zB} {n1 n2 : Nat} {w1 w2 : zF} {C1 C2 e1 e2 : Nat}
    (h : RCounter r1 n1 w1 C1 e1)
    (hr : r1 = r2 := by cfg_eq) (hn : n1 = n2 := by omega)
    (hw : w1 = w2 :=
        by simp only
            [list_pow_zero, list_pow_one, List.append_nil, List.nil_append, List.append_assoc])
    (hC : C1 = C2 := by omega) (he : e1 = e2 := by omega) :
    RCounter r2 n2 w2 C2 e2 := by
  subst hr; subst hn; subst hw; subst hC; subst he; exact h

theorem RCounter_step (l r : zB) (n : Nat) (w : zF) (C_out e a b : Nat)
    (HR : RCounter r n w C_out e) (Ha : a ≤ n) :
    ∃ r', RCounter r' (n - a + b) ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
        ^ (1 + a)) ++ w) C_out e ∧
      ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l))
          <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
        (l <{{C}} (([0, 1] : zF) +> r')) := by
  rcases HR with ⟨d, s, rfl, HR⟩
  rcases RRoute_scan 1 d s n w C_out e default HR a ((([1, 1, 0] : zF) ^ (2 + b * 2)) +> l)
      [] [] [] Ha Word_nil with
    ⟨c', d', s', u, z, i, j, HZ, EW, HU, HS⟩
  refine ⟨((([0, 1, 0] : zF) ^ (2 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u)
      c' d' s'), ?_, ?_⟩
  · refine ⟨b * 2, link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) c' d' s', rfl, ?_⟩
    exact RRoute_eq (RRoute.RRoute_more 0 b _ _ _ c' d' s' (n - a)
        z C_out e default (EraseWord.Erase_V a u i j HU) HZ)
      (hw := by rw [EW, pow_add_1]; simp only [Nat.zero_add, List.append_assoc])
  · refine step_bridge (scan_pair ((([1, 0] : zF) ^ (a * 2)) +> ((([1, 1, 0] : zF) ^ (2 + b * 2))
        +> l)) s 0 d) (by cfg_eq) ?_
    refine ReachesStar.trans HS ?_
    exact step_end (pass_011 l (link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) c' d' s') (2 + b * 2))
        (by cfg_eq) (by cfg_eq)

theorem RCounter_columns (n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : ColumnRun n cs m)
    (l r : zB) (w : zF) (C_out e : Nat) (HR : RCounter r n w C_out e) :
    ∃ r', RCounter r' m (column_word cs ++ w) C_out e ∧
      (column_side l cs <{{C}} (([0, 1] : zF) +> r)) [target_tm]⊢* (l <{{C}} (([0, 1] : zF)
          +> r')) := by
  induction H generalizing l r w with
  | Columns_nil n => exact ⟨r, HR, step_eq rfl⟩
  | Columns_cons n a b cs m Ha H ih =>
    rcases RCounter_step (column_side l cs) r n w C_out e a b HR Ha with ⟨r1, H1, HS⟩
    rcases ih l r1 _ H1 with ⟨r2, H2, HT⟩
    refine ⟨r2, RCounter_eq H2 (hw := by dsimp [column_word]; simp only [List.append_assoc]),
        ReachesStar.trans HS HT⟩

theorem RCounter_base (n e : Nat) :
    RCounter (((([0, 1, 0] : zF) ^ (2 + n * 2 + e)) +> default)) n [] (1 + n * 2) e :=
  ⟨n * 2 + e, default, by cfg_eq, RRoute_eq (RRoute.RRoute_done 0 n e default)⟩

theorem RCounter_gap (g b d e : Nat) :
    RCounter (((([0, 1, 0] : zF) ^ (2 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ g))
        (1 + g * 2) (d * 2 + e) default))
      (b + d) ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + g)))
          (1 + g * 2 + d * 2) e := by
  refine ⟨b * 2, link ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) (1 + g * 2) (d * 2 + e) default, rfl, ?_⟩
  exact RRoute_eq (RRoute.RRoute_more 0 b ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) 0 g (1 + g * 2)
      (d * 2 + e) default d [] (1 + (g + d) * 2) e default
    (EraseWord_eq (EraseWord.Erase_V g [] 0 0 EraseWord.Erase_nil))
        (RRoute.RRoute_done g d e default))
    (hw := by rw [pow_add_1]; simp only [Nat.zero_add, List.append_nil, List.append_assoc])

theorem SectionStart_Rspec (l : zB) (n : Nat) (w : zF) (C_out e : Nat) (c : Cfg (Fin 2) (Fin 6))
    (H : SectionStart l n w C_out e c) :
    ∃ r, RCounter r n w C_out e ∧ c [target_tm]⊢* (l <{{C}} (([0, 1] : zF) +> r)) := by
  rcases H with ⟨d, b, e, HP⟩ | ⟨g, b, d, e, HP⟩
  · refine ⟨((([0, 1, 0] : zF) ^ ((2 + d * 2 + e) + (2 + b * 2))) +> default), ?_,
        counter_begin l (2 + d * 2 + e) (2 + b * 2) HP⟩
    exact RCounter_eq (RCounter_base (1 + d + b) e)
  · exact ⟨_, RCounter_gap g b d e, counter_begin_gap l g b d e HP⟩

theorem Pass_erase_pair (r : zB) (c j k : Nat) :
    Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF)
                         ^ (1 + k)) +> r)) a b (3 + c) 0)
         (fun a b => rootV ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k))
                       +> r)) a b (3 + c) 0)
         (fun l a b => crossV l r a b (4 + c + k) 0)
         (fun a b => rootV r a b (4 + c + k) 0) ((2 + j + k) * 2) := by
  have h1 : Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (2 + j * 2))
                                 +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r)) a b (3 + c) 0)
                 (fun a b => rootV ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF)
                               ^ (1 + k)) +> r)) a b (3 + c) 0)
                 (fun l a b => crossZ l ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r)
                                 a b (3 + (1 + c)) (1 + j * 2))
                 (fun a b => rootZ ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) a b (3 + (1 + c))
                               (1 + j * 2)) 2 :=
    Pass_eq (Pass_V_end ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) c (1 + j * 2))
  have h2 := Pass_Zs ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) (1 + c) 1 j
  have h3 := Pass_Z_to_V r (1 + c) k
  have h4 : Pass (fun l a b => crossV l r a b (3 + (1 + c)) k)
                 (fun a b => rootV r a b (3 + (1 + c)) k)
                 (fun l a b => crossV l r a b (3 + (1 + c) + k) 0)
                 (fun a b => rootV r a b (3 + (1 + c) + k) 0) (k * 2) :=
    Pass_eq (Pass_Vs r (1 + c) 0 k)
  exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))

theorem EraseWord_pass (w : zF) (u v : Nat) (H : EraseWord w u v) (r : zB) (c : Nat) :
    Pass (fun l a b => crossV l (w +> r) a b (3 + c) 0)
         (fun a b => rootV (w +> r) a b (3 + c) 0)
         (fun l a b => crossV l r a b (3 + c + v) 0)
         (fun a b => rootV r a b (3 + c + v) 0) ((u + v) * 2) := by
  induction H generalizing r c with
  | Erase_nil => exact Pass_eq (Pass_id _ _)
  | Erase_V n w u v _ ih =>
    have h1 : Pass (fun l a b => crossV l (((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) +> r) a b (3 + c)
                                   0)
                   (fun a b => rootV (((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) +> r) a b (3 + c) 0)
                   (fun l a b => crossV l (w +> r) a b (3 + (c + n)) 0)
                   (fun a b => rootV (w +> r) a b (3 + (c + n)) 0) (n * 2) :=
      Pass_eq (Pass_Vs (w +> r) c 0 n)
    exact Pass_eq (Pass_trans h1 (ih r (c + n)))
  | Erase_pair j k w u v _ ih =>
    have h1 : Pass (fun l a b => crossV l (((([1, 0] : zF) ^ (2 + j * 2))
                                   ++ (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) ++ w) +> r) a b (3 + c)
                                       0)
                   (fun a b => rootV (((([1, 0] : zF) ^ (2 + j * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
                                 ^ (1 + k)) ++ w) +> r) a b (3 + c) 0)
                   (fun l a b => crossV l (w +> r) a b (3 + (1 + c + k)) 0)
                   (fun a b => rootV (w +> r) a b (3 + (1 + c + k)) 0) ((2 + j + k) * 2) :=
      Pass_eq (Pass_erase_pair (w +> r) c j k)
    exact Pass_eq (Pass_trans h1 (ih r (1 + c + k)))

theorem Pass_odd_join (r : zB) (c : Nat) (w : zF) (c' d : Nat) :
    Pass (fun l a b => crossW l (link w c' d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c 1)
         (fun a b => rootW (link w c' d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c 1)
         (fun l a b => crossV l (w +> clean_input c' d r) a b (3 + c) 0)
         (fun a b => rootV (w +> clean_input c' d r) a b (3 + c) 0) 0 :=
  Pass_eq (Pass_id _ _)

theorem Pass_clean_tail (j n e k : Nat) (He : e ≤ 1) :
    ∃ C_out E, E ≤ 1 ∧ C_out + E = 2 + k + n * 2 + e ∧
      Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2 + e) default) a b (3 + k) 0)
           (fun a b => rootV (clean_input (1 + j * 2) (n * 2 + e) default) a b (3 + k) 0)
           (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C_out E)
           (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C_out E)
                         (4 + j * 2 + n + e) := by
  rcases e with _ | _ | e
  · rcases n with _ | n
    · refine ⟨2 + k, 0, by omega, by omega, ?_⟩
      have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) 0 default) a b (3 + k) 0)
                     (fun a b => rootV (clean_input (1 + j * 2) 0 default) a b (3 + k) 0)
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b (3 + (1 + k))
                                     (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b (3 + (1 + k)) (0 + j * 2))
                                   2 :=
        Pass_eq (Pass_V_end (([1, 0, 1] : zF) +> default) k (j * 2))
      have h2 : Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b (3 + (1 + k))
                                     (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b (3 + (1 + k)) (0 + j * 2))
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b (4 + k) 0)
                     (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b (4 + k) 0) (j * 2) :=
        Pass_eq (Pass_Zs (([1, 0, 1] : zF) +> default) (1 + k) 0 j)
      have h3 := Pass_Z_empty k
      exact Pass_eq (Pass_trans h1 (Pass_trans h2 h3))
    · refine ⟨3 + k + n * 2, 1, by omega, by omega, ?_⟩
      have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) ((n + 1) * 2) default)
                                     a b (3 + k) 0)
                     (fun a b => rootV (clean_input (1 + j * 2) ((n + 1) * 2) default) a b (3 + k)
                                   0)
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                     ^ (1 + (1 + n * 2))) +> default)) a b (3 + (1 + k))
                                         (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                   +> default)) a b (3 + (1 + k)) (0 + j * 2)) 2 :=
        Pass_eq (Pass_V_end (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
            +> default)) k (j * 2))
      have h2 : Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                     ^ (1 + (1 + n * 2))) +> default)) a b (3 + (1 + k))
                                         (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                   +> default)) a b (3 + (1 + k)) (0 + j * 2))
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                     ^ (1 + (1 + n * 2))) +> default)) a b (4 + k) 0)
                     (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                   +> default)) a b (4 + k) 0) (j * 2) :=
        Pass_eq (Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2))) +> default))
            (1 + k) 0 j)
      have h3 := Pass_Z_back default k (1 + n * 2)
      have h4 : Pass (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k)
                                     (2 + (1 + n * 2)))
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k)
                                   (2 + (1 + n * 2)))
                     (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                     (3 + k + n * 2) 1)
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + k + n * 2) 1)
                                   (1 + n) :=
        Pass_eq (Pass_Ws default (1 + k) 1 (1 + n))
      exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))
  · refine ⟨3 + k + n * 2, 0, by omega, by omega, ?_⟩
    have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2 + 1) default) a b (3 + k)
                                   0)
                   (fun a b => rootV (clean_input (1 + j * 2) (n * 2 + 1) default) a b (3 + k) 0)
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                   +> default)) a b (3 + (1 + k)) (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                 +> default)) a b (3 + (1 + k)) (0 + j * 2)) 2 :=
      Pass_eq (Pass_V_end (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2)) +> default))
          k (j * 2))
    have h2 : Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                   +> default)) a b (3 + (1 + k)) (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                 +> default)) a b (3 + (1 + k)) (0 + j * 2))
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                   +> default)) a b (4 + k) 0)
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                 +> default)) a b (4 + k) 0) (j * 2) :=
      Pass_eq (Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2)) +> default)) (1 + k)
          0 j)
    have h3 := Pass_Z_back default k (n * 2)
    have h4 : Pass (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k)
                                   (2 + n * 2))
                   (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k) (2 + n * 2))
                   (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + k + n * 2)
                                   0)
                   (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (3 + k + n * 2) 0)
                                 (1 + n) :=
      Pass_eq (Pass_Ws default (1 + k) 0 (1 + n))
    exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))
  · omega

theorem Pass_clean_link (j n : Nat) (z : zF) (u v c d : Nat) (r : zB) (k : Nat)
    (HZ : EraseWord z u v) :
    Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2) (link z c d r)) a b (3 + k) 0)
         (fun a b => rootV (clean_input (1 + j * 2) (n * 2) (link z c d r)) a b (3 + k) 0)
         (fun l a b => crossV l (clean_input c d r) a b (4 + k + n * 2 + v) 0)
         (fun a b => rootV (clean_input c d r) a b (4 + k + n * 2 + v) 0) (4 + j * 2 + n + (u + v)
                       * 2) := by
  rcases n with _ | n
  · have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) 0 (link z c d r)) a b (3 + k) 0)
                   (fun a b => rootV (clean_input (1 + j * 2) 0 (link z c d r)) a b (3 + k) 0)
                   (fun l a b => crossV l (z +> clean_input c d r) a b (3 + (1 + k)) 0)
                   (fun a b => rootV (z +> clean_input c d r) a b (3 + (1 + k)) 0) ((2 + j) * 2) :=
      Pass_eq (Pass_erase_pair (z +> clean_input c d r) k j 0)
    have h2 := EraseWord_pass z u v HZ (clean_input c d r) (1 + k)
    exact Pass_eq (Pass_trans h1 h2)
  · have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) ((n + 1) * 2) (link z c d r))
                                   a b (3 + k) 0)
                   (fun a b => rootV (clean_input (1 + j * 2) ((n + 1) * 2) (link z c d r))
                                 a b (3 + k) 0)
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                   ^ (1 + (1 + n * 2))) +> link z c d r)) a b (3 + (1 + k))
                                       (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                 +> link z c d r)) a b (3 + (1 + k)) (0 + j * 2)) 2 :=
      Pass_eq (Pass_V_end (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
          +> link z c d r)) k (j * 2))
    have h2 : Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                   ^ (1 + (1 + n * 2))) +> link z c d r)) a b (3 + (1 + k))
                                       (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                 +> link z c d r)) a b (3 + (1 + k)) (0 + j * 2))
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                   ^ (1 + (1 + n * 2))) +> link z c d r)) a b (4 + k) 0)
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                 +> link z c d r)) a b (4 + k) 0) (j * 2) :=
      Pass_eq (Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
          +> link z c d r)) (1 + k) 0 j)
    have h3 := Pass_Z_back (link z c d r) k (1 + n * 2)
    have h4 : Pass (fun l a b => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k)
                                   (2 + (1 + n * 2)))
                   (fun a b => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (1 + k)
                                 (2 + (1 + n * 2)))
                   (fun l a b => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) ((1 + n)
                                   * 2 + (1 + k)) 1)
                   (fun a b => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) ((1 + n)
                                 * 2 + (1 + k)) 1) (1 + n) :=
      Pass_eq (Pass_Ws (link z c d r) (1 + k) 1 (1 + n))
    have h5 := Pass_odd_join r ((1 + n) * 2 + (1 + k)) z c d
    have h6 := EraseWord_pass z u v HZ (clean_input c d r) ((1 + n) * 2 + (1 + k))
    exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 (Pass_trans h4 (Pass_trans h5 h6)))))

theorem root_plain_terminal (a b c e : Nat) (He : e ≤ 1) :
    (rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ (3 + a))
        +> default))) {{B}}> default)) :=
  step_end (rootW_terminal a _ _ _ c e He (Word_pow _ _ _ b Word_V)) (by cfg_eq) (by cfg_eq)

theorem cross_plain_terminal (l : zB) (a b c e : Nat) (He : e ≤ 1) :
    (crossW l default (2 + a) (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) [target_tm]⊢*
    ((((([1, 0] : zF) ^ (1 + c + e)) +> ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> ((([1, 0] : zF) ^ a)
        +> l))) {{B}}> default)) :=
  step_end (crossW_terminal l a _ _ _ c e He (Word_pow _ _ _ b Word_V)) (by cfg_eq) (by cfg_eq)

theorem cleanup_start0 (r : zB) (d : Nat) :
    ((default <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (2 + d)) +> r)))) [target_tm]⊢*
    (rootW r 2 [] 1 d) := by
  refine ReachesStar.trans (scan_left_zero r (2 + d)) ?_
  exact step_end (scan_left_step r 1 d) (by cfg_eq) (by cfg_eq)

theorem cleanup_start1 (r : zB) (d : Nat) :
    (((([1, 0] : zF) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (2 + d)) +> r))))
        [target_tm]⊢*
    (rootW r 4 [] 1 d) := by
  refine ReachesStar.trans (scan_left_entry r (2 + d)) ?_
  exact step_end (scan_left_step r 3 d) (by cfg_eq) (by cfg_eq)

theorem cleanup_start2 (r : zB) (d : Nat) :
    ((((([1, 0] : zF) ^ 2) +> default) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (2 + d))
        +> r)))) [target_tm]⊢*
    (rootW r 0 [1, 0, 1, 0, 0, 1] 1 d) := by
  refine step_bridge (scan_pair default r 0 d) (by cfg_eq) ?_
  exact step_end (scanW_zero r [] 1 d) (by cfg_eq) (by cfg_eq)

theorem cleanup_start (l : zB) (a : Nat) (r : zB) (d : Nat) :
    ((((([1, 0] : zF) ^ (3 + a)) +> l) <{{C}} (([0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (2 + d))
        +> r)))) [target_tm]⊢*
    (crossW l r a [1, 0, 1, 0, 0, 1] 1 d) := by
  refine step_bridge (scan_pair ((([1, 0] : zF) ^ (1 + a)) +> l) r 0 d) (by cfg_eq) ?_
  exact step_end (scanW_entry l r a [] 1 d) (by cfg_eq) (by cfg_eq)

def Cleanup (r : zB) (N X : Nat) : Prop :=
  ∃ d s c e, r = ((([0, 1, 0] : zF) ^ (2 + d)) +> s) ∧ e ≤ 1 ∧ X = 1 + c + e ∧
    Pass (fun l a b => crossW l s a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 1 d)
         (fun a b => rootW s a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 1 d)
         (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e)
         (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) N

theorem Cleanup_eq {r1 r2 : zB} {N1 N2 X1 X2 : Nat}
    (h : Cleanup r1 N1 X1)
    (hr : r1 = r2 := by cfg_eq) (hN : N1 = N2 := by omega) (hX : X1 = X2 := by omega) :
    Cleanup r2 N2 X2 := by
  subst hr; subst hN; subst hX; exact h

inductive CleanLast (N X : Nat) : Nat → List Nat → Prop where
  | Clean0 : CleanLast N X 0 [X + 5 + N * 2]
  | Clean1 : CleanLast N X 1 [X + 7 + N * 2]
  | CleanEven (s : Nat) : s ≤ N → CleanLast N X (2 + s * 2) [X, 2 + s * 2, 3 + (N - s) * 2]
  | CleanOdd (s : Nat) : s ≤ N → CleanLast N X (3 + s * 2) [X, 2 + s * 2, 5 + (N - s) * 2]
  | CleanBorder : CleanLast N X (4 + N * 2) [X, 4 + N * 2, 1]
  | CleanOver (a : Nat) : CleanLast N X (5 + N * 2 + a) [X, 5 + N * 2, a]

theorem CleanLast_eq {N1 N2 X1 X2 t1 t2 : Nat} {xs1 xs2 : List Nat}
    (h : CleanLast N1 X1 t1 xs1)
    (hN : N1 = N2 := by omega) (hX : X1 = X2 := by omega) (ht : t1 = t2 := by omega)
    (hxs : xs1 = xs2 := by
      first
      | rfl
      | (try simp only [List.cons.injEq, and_true, true_and])
        (repeat' constructor) <;> first | trivial | omega) :
    CleanLast N2 X2 t2 xs2 := by
  subst hN; subst hX; subst ht; subst hxs; exact h

theorem Cleanup_spec (r : zB) (N X t : Nat) (xs : List Nat)
    (HC : Cleanup r N X) (HL : CleanLast N X t xs) :
    ((((([1, 0] : zF) ^ t) +> default) <{{C}} (([0, 1] : zF) +> r)))
        [target_tm]⊢⁺ (section_481 xs) := by
  rcases HC with ⟨d, r0, c, e, rfl, He, rfl, ⟨HF, HE⟩⟩
  refine evstep_progress ?_ (by ne_cfg)
  rcases HL with _ | _ | ⟨s, Hs⟩ | ⟨s, Hs⟩ | _ | a
  · refine step_bridge (cleanup_start0 r0 d) (by cfg_eq) ?_
    refine step_bridge (HF.flow_root 2 0) (by cfg_eq) ?_
    exact step_end (root_plain_terminal (N * 2 + 2) 0 c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_start1 r0 d) (by cfg_eq) ?_
    refine step_bridge (HF.flow_root 4 0) (by cfg_eq) ?_
    exact step_end (root_plain_terminal (N * 2 + 4) 0 c e He) (by cfg_eq) (by cfg_eq)
  · rcases s with _ | s
    · refine step_bridge (cleanup_start2 r0 d) (by cfg_eq) ?_
      refine step_bridge (HF.flow_root 0 1) (by cfg_eq) ?_
      exact step_end (root_plain_terminal (N * 2 + 0) 1 c e He) (by cfg_eq) (by cfg_eq)
    · refine step_bridge (cleanup_start default (1 + s * 2) r0 d) (by cfg_eq) ?_
      refine step_bridge (HF.flow_border s (N - s - 1) 1 (by omega)) (by cfg_eq) ?_
      exact step_end (root_plain_terminal ((N - s - 1) * 2) (2 + s) c e He) (by cfg_eq) (by cfg_eq)
  · rcases s with _ | s
    · refine step_bridge (cleanup_start default 0 r0 d) (by cfg_eq) ?_
      refine step_bridge (crossW_zero r0 [1, 0, 1, 0, 0, 1] 1 d) (by cfg_eq) ?_
      refine step_bridge (HF.flow_root 2 1) (by cfg_eq) ?_
      exact step_end (root_plain_terminal (N * 2 + 2) 1 c e He) (by cfg_eq) (by cfg_eq)
    · refine step_bridge (cleanup_start default (2 + s * 2) r0 d) (by cfg_eq) ?_
      refine step_bridge (HE s (N - s - 1) 1 (by omega)) (by cfg_eq) ?_
      exact step_end (root_plain_terminal (2 + (N - s - 1) * 2) (2 + s) c e He) (by cfg_eq)
          (by cfg_eq)
  · refine step_bridge (cleanup_start default (1 + N * 2) r0 d) (by cfg_eq) ?_
    refine step_bridge (HF.flow_cross default 1 1) (by cfg_eq) ?_
    exact step_end (crossW_last_one (1 + N) c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_start default (2 + N * 2 + a) r0 d) (by cfg_eq) ?_
    refine step_bridge (HF.flow_cross default (2 + a) 1) (by cfg_eq) ?_
    exact step_end (cross_plain_terminal default a (1 + N) c e He) (by cfg_eq) (by cfg_eq)

theorem RRoute_clean (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (H : RRoute c d r n w C_out e R) (ER : R = default) (He : e ≤ 1) :
    ∃ u v, EraseWord w u v ∧ ∀ k, ∃ N C' E,
      E ≤ 1 ∧ N + n = (u + v) * 2 + 3 + C_out + e ∧ C' + E = 2 + k + v + n * 2 + e ∧
      Pass (fun l a b => crossV l (clean_input c d r) a b (3 + k) 0)
           (fun a b => rootV (clean_input c d r) a b (3 + k) 0)
           (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E)
           (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E) N := by
  induction H with
  | RRoute_done j n e r =>
    subst ER
    refine ⟨0, 0, EraseWord.Erase_nil, fun k => ?_⟩
    rcases Pass_clean_tail j n e k He with ⟨C', E, HE, HC, HP⟩
    exact ⟨4 + j * 2 + n + e, C', E, HE, by omega, by omega, HP⟩
  | RRoute_more j n z x y c' d r m w C_out e R HZ HR ih =>
    rcases ih ER He with ⟨u, v, HW, IHk⟩
    refine ⟨1 + (j + n) + x + u, 1 + y + v, ?_, fun k => ?_⟩
    · exact EraseWord_eq (EraseWord.Erase_pair (j + n) 0 (z ++ w) (x + u) (y + v)
          (EraseWord_app z x y w u v HZ HW))
    · rcases IHk (1 + k + n * 2 + y) with ⟨N, C0, E, HE, HN, HC, HP⟩
      refine ⟨4 + j * 2 + n + (x + y) * 2 + N, C0, E, HE, by omega, by omega, ?_⟩
      have h1 := Pass_clean_link j n z x y c' d r k HZ
      have h2 : Pass (fun l a b => crossV l (clean_input c' d r) a b (4 + k + n * 2 + y) 0)
                     (fun a b => rootV (clean_input c' d r) a b (4 + k + n * 2 + y) 0)
                     (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C0 E)
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C0 E) N :=
        Pass_eq HP
      exact Pass_eq (Pass_trans h1 h2)

theorem RRoute_cleanup (b : Nat) (z : zF) (i j c d : Nat) (r : zB) (n : Nat) (w : zF)
    (C_out e : Nat)
    (HZ : EraseWord z i j) (HR : RRoute c d r n w C_out e default) (He : e ≤ 1) :
    ∃ u v N X, EraseWord w u v ∧
      N + n = b + (i + j + u + v) * 2 + 3 + C_out + e ∧ X = 4 + b * 2 + j + v + n * 2 + e ∧
      Cleanup ((([0, 1, 0] : zF) ^ (3 + b * 2)) +> link z c d r) N X := by
  rcases RRoute_clean c d r n w C_out e default HR rfl He with ⟨u, v, HW, HK⟩
  rcases HK (1 + b * 2 + j) with ⟨N, c', e', He', HN, HX, HP⟩
  refine ⟨u, v, b + (i + j) * 2 + N, 1 + c' + e', HW, by omega, by omega, ?_⟩
  refine ⟨1 + b * 2, link z c d r, c', e', by cfg_eq, He', rfl, ?_⟩
  have h1 : Pass (fun l a b_blk => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk)
                                     1 (1 + b * 2))
                 (fun a b_blk => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk)
                                   1 (1 + b * 2))
                 (fun l a b_blk => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk)
                                     (b * 2 + 1) 1)
                 (fun a b_blk => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk)
                                   (b * 2 + 1) 1) b :=
    Pass_eq (Pass_Ws (link z c d r) 1 1 b)
  have h2 := Pass_odd_join r (b * 2 + 1) z c d
  have h3 := EraseWord_pass z i j HZ (clean_input c d r) (b * 2 + 1)
  have h4 : Pass (fun l a b_blk => crossV l (clean_input c d r) a b_blk (3 + (b * 2 + 1) + j) 0)
                 (fun a b_blk => rootV (clean_input c d r) a b_blk (3 + (b * 2 + 1) + j) 0)
                 (fun l a b_blk => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk) c' e')
                 (fun a b_blk => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b_blk) c' e') N :=
    Pass_eq HP
  exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))

theorem pow_length (w : zF) (n : Nat) : (w ^ n).length = w.length * n := by
  induction n with
  | zero => simp only [list_pow_zero, List.length_nil, Nat.mul_zero]
  | succ n ih => rw [list_pow_succ, List.length_append, ih, Nat.mul_add, Nat.mul_one, Nat.add_comm]

theorem EraseWord_size (w : zF) (u v : Nat) (H : EraseWord w u v) : w.length = u * 4 + v * 6 := by
  induction H with
  | Erase_nil => rfl
  | Erase_V n w u v _ ih =>
    simp only [List.length_append, pow_length, List.length_cons, List.length_nil, ih]
    omega
  | Erase_pair j k w u v _ ih =>
    simp only [List.length_append, pow_length, List.length_cons, List.length_nil, ih]
    omega

theorem Cleanup_triple (g b d e : Nat) (He : e ≤ 1) :
    Cleanup ((([0, 1, 0] : zF) ^ (3 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) (1 + g * 2)
        (d * 2 + e) default)
      (4 + b + g * 4 + d + e) (4 + b * 2 + g + d * 2 + e) := by
  rcases RRoute_cleanup b ((([1, 0, 1, 0, 0, 1] : zF) ^ g)) 0 g (1 + g * 2) (d * 2 + e)
      default d [] (1 + (g + d) * 2) e
    (EraseWord_eq (EraseWord.Erase_V g [] 0 0 EraseWord.Erase_nil))
        (RRoute.RRoute_done g d e default) He with
    ⟨u, v, N, X, HW, HN, HX, HC⟩
  have hlen := EraseWord_size [] u v HW
  have hu : u = 0 := by dsimp at hlen; omega
  have hv : v = 0 := by dsimp at hlen; omega
  subst hu; subst hv
  exact Cleanup_eq HC

theorem cleanup_triple_section (g b d e t : Nat) (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1)
    (HL : CleanLast (4 + b + g * 4 + d + e) (4 + b * 2 + g + d * 2 + e) t xs) :
    (section_481 [(2 + g * 2 + (d * 2 + e)) + (2 + g * 2), 3 + b * 2, t])
        [target_tm]⊢⁺ (section_481 xs) := by
  refine evstep_progress_trans ?_ (Cleanup_spec _ _ _ t xs (Cleanup_triple g b d e He) HL)
  refine step_bridge (return_even ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> ((([1, 0] : zF) ^ t)
      +> default)) g (d * 2 + e) HP) (by cfg_eq) ?_
  exact step_end (pass_011 ((([1, 0] : zF) ^ t) +> default) _ (3 + b * 2)) (by cfg_eq) (by cfg_eq)

theorem RCounter_cleanup (l r : zB) (n : Nat) (w : zF) (C_out e a b : Nat)
    (HR : RCounter r n w C_out e) (Ha : a ≤ n) (He : e ≤ 1) :
    ∃ u v N X r', EraseWord w u v ∧
      N + n = b + a * 3 + (u + v)
          * 2 + 3 + C_out + e ∧ X + a = 4 + b * 2 + v + n * 2 + e ∧ Cleanup r' N X ∧
      ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> l))
          <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
        (l <{{C}} (([0, 1] : zF) +> r')) := by
  rcases HR with ⟨d, s, rfl, HR⟩
  rcases RRoute_scan 1 d s n w C_out e default HR a ((([1, 1, 0] : zF) ^ (3 + b * 2)) +> l)
      [] [] [] Ha Word_nil with
    ⟨c', d', s', u, z, i, j, HZ, EW, HU, HS⟩
  rcases RRoute_cleanup b ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) i (a + j) c' d' s' (n - a)
      z C_out e
    (EraseWord.Erase_V a u i j HU) HZ He with ⟨x, y, N, X, HW, HN, HX, HC⟩
  refine ⟨i + x, j + y, N, X, ((([0, 1, 0] : zF) ^ (3 + b * 2)) +> link ((([1, 0, 1, 0, 0, 1] : zF)
      ^ a) ++ u) c' d' s'), ?_, by omega, by omega, HC, ?_⟩
  · rw [EW]; exact EraseWord_app u i j z x y HU HW
  · refine step_bridge (scan_pair ((([1, 0] : zF) ^ (a * 2)) +> ((([1, 1, 0] : zF) ^ (3 + b * 2))
        +> l)) s 0 d) (by cfg_eq) ?_
    refine ReachesStar.trans HS ?_
    exact step_end (pass_011 l (link ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) c' d' s') (3 + b * 2))
        (by cfg_eq) (by cfg_eq)

theorem CleanLast_total (N X t : Nat) : ∃ xs, CleanLast N X t xs := by
  rcases t with _ | _ | t
  · exact ⟨_, CleanLast.Clean0⟩
  · exact ⟨_, CleanLast.Clean1⟩
  · rcases parity t with ⟨s, rfl | rfl⟩
    · by_cases hle : s ≤ N
      · exact ⟨_, CleanLast_eq (@CleanLast.CleanEven N X s hle) rfl rfl (by omega) rfl⟩
      · by_cases heq : s = N + 1
        · exact ⟨_, CleanLast_eq (@CleanLast.CleanBorder N X) rfl rfl (by omega) rfl⟩
        · exact ⟨_, CleanLast_eq (@CleanLast.CleanOver N X (2 + s * 2 - (5 + N * 2))) rfl rfl
              (by omega) rfl⟩
    · by_cases hle : s ≤ N
      · exact ⟨_, CleanLast_eq (@CleanLast.CleanOdd N X s hle) rfl rfl (by omega) rfl⟩
      · exact ⟨_, CleanLast_eq (@CleanLast.CleanOver N X (3 + s * 2 - (5 + N * 2))) rfl rfl
            (by omega) rfl⟩

theorem Pass_V_low (r : zB) (e : Nat) :
    Pass (fun l a b => crossV l r a b 2 (1 + e))
         (fun a b => rootV r a b 2 (1 + e))
         (fun l a b => crossV l r a b 3 e)
         (fun a b => rootV r a b 3 e) 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l a b; exact step_end (crossV_low l r a b e) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootV_low r a b e) (by cfg_eq) (by cfg_eq)
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossV_low_one r b e) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv; exact step_end (crossV_low_three r b e) (by cfg_eq) (by cfg_eq)
    · omega
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossV_low_two r b e) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      refine step_bridge (crossV_low default r 0 b e) (by cfg_eq) ?_
      exact step_end (crossV_zero r (2 + b) 3 e) (by cfg_eq) (by cfg_eq)
    · omega

theorem Pass_Vend_low (r : zB) (e : Nat) :
    Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (1 + e)) +> r) a b 2 0)
         (fun a b => rootV ((([1, 0] : zF) ^ (1 + e)) +> r) a b 2 0)
         (fun l a b => crossZ l r a b 3 e)
         (fun a b => rootZ r a b 3 e) 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l a b; exact step_end (crossVend_low l r a b e) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootVend_low r a b e) (by cfg_eq) (by cfg_eq)
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossVend_low_one r b e) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv; exact step_end (crossVend_low_three r b e) (by cfg_eq) (by cfg_eq)
    · omega
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossVend_low_two r b e) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      refine step_bridge (crossVend_low default r 0 b e) (by cfg_eq) ?_
      exact step_end (crossZ_zero r (2 + b) 3 e) (by cfg_eq) (by cfg_eq)
    · omega

theorem Pass_Z_empty_low :
    Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b 3 0)
         (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b 3 0)
         (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 1 0)
         (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 1 0) 2 := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro l a b; exact step_end (crossZ_empty_low l a b) (by cfg_eq) (by cfg_eq)
  · intro a b; exact step_end (rootZ_empty_low a b) (by cfg_eq) (by cfg_eq)
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossZ_empty_low_one b) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv; exact step_end (crossZ_empty_low_three b) (by cfg_eq) (by cfg_eq)
    · omega
  · intro s v b E
    rcases s with _ | _ | s
    · have hv : v = 1 := by omega
      subst hv; exact step_end (crossZ_empty_low_two b) (by cfg_eq) (by cfg_eq)
    · have hv : v = 0 := by omega
      subst hv
      refine step_bridge (crossZ_empty_low default 0 b) (by cfg_eq) ?_
      exact step_end (crossW_zero default (([1, 0, 1, 0, 0, 1] : zF) ^ (2 + b)) 1 0) (by cfg_eq)
          (by cfg_eq)
    · omega

theorem Pass_Z_back_low (r : zB) (d : Nat) :
    Pass (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + d)) +> r)) a b 3 0)
         (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + d)) +> r)) a b 3 0)
         (fun l a b => crossW l r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 0 (2 + d))
         (fun a b => rootW r a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 0 (2 + d)) 2 :=
  Pass_eq (Pass_Z (([1, 0] : zF) +> ((([0, 1, 0] : zF) ^ d) +> r)) 0 0)

theorem Pass_clean_tail_low (j n e : Nat) (He : e ≤ 1) :
    ∃ C_out E, E ≤ 1 ∧ C_out + E = 1 + n * 2 + e ∧
      Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2 + e) default) a b 2 0)
           (fun a b => rootV (clean_input (1 + j * 2) (n * 2 + e) default) a b 2 0)
           (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C_out E)
           (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C_out E)
                         (4 + j * 2 + n + e) := by
  rcases e with _ | _ | e
  · rcases n with _ | n
    · refine ⟨1, 0, by omega, by omega, ?_⟩
      have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) 0 default) a b 2 0)
                     (fun a b => rootV (clean_input (1 + j * 2) 0 default) a b 2 0)
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> default) a b 3 (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> default) a b 3 (0 + j * 2)) 2 :=
        Pass_eq (Pass_Vend_low (([1, 0, 1] : zF) +> default) (j * 2))
      have h2 := Pass_Zs (([1, 0, 1] : zF) +> default) 0 0 j
      have h3 := Pass_Z_empty_low
      exact Pass_eq (Pass_trans h1 (Pass_trans h2 h3))
    · refine ⟨2 + n * 2, 1, by omega, by omega, ?_⟩
      have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) ((n + 1) * 2) default) a b 2 0)
                     (fun a b => rootV (clean_input (1 + j * 2) ((n + 1) * 2) default) a b 2 0)
                     (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                     ^ (1 + (1 + n * 2))) +> default)) a b 3 (0 + j * 2))
                     (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                   +> default)) a b 3 (0 + j * 2)) 2 :=
        Pass_eq (Pass_Vend_low (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
            +> default)) (j * 2))
      have h2 := Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2))) +> default))
          0 0 j
      have h3 := Pass_Z_back_low default (1 + n * 2)
      have h4 : Pass (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                     0 (2 + (1 + n * 2)))
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                   0 (2 + (1 + n * 2)))
                     (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + n * 2) 1)
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + n * 2) 1)
                                   (1 + n) :=
        Pass_eq (Pass_Ws default 0 1 (1 + n))
      exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))
  · refine ⟨2 + n * 2, 0, by omega, by omega, ?_⟩
    have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2 + 1) default) a b 2 0)
                   (fun a b => rootV (clean_input (1 + j * 2) (n * 2 + 1) default) a b 2 0)
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                   +> default)) a b 3 (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2))
                                 +> default)) a b 3 (0 + j * 2)) 2 :=
      Pass_eq (Pass_Vend_low (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2)) +> default))
          (j * 2))
    have h2 := Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + n * 2)) +> default)) 0 0 j
    have h3 := Pass_Z_back_low default (n * 2)
    have h4 : Pass (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 0 (2 + n * 2))
                   (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) 0 (2 + n * 2))
                   (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + n * 2) 0)
                   (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) (2 + n * 2) 0)
                                 (1 + n) :=
      Pass_eq (Pass_Ws default 0 0 (1 + n))
    exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))
  · omega

def OneCleanup (r : zB) (N X : Nat) : Prop :=
  ∃ c e, e ≤ 1 ∧ X = 1 + c + e ∧
    Pass (fun l a b => crossV l r a b 2 0)
         (fun a b => rootV r a b 2 0)
         (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e)
         (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) c e) (1 + N)

theorem OneCleanup_spec (r : zB) (N X t : Nat) (xs : List Nat)
    (HC : OneCleanup r N X) (HL : CleanLast N X t xs) :
    ((((([1, 0] : zF) ^ t) +> default) <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> r)))
        [target_tm]⊢⁺
    (section_481 xs) := by
  rcases HC with ⟨c, e, He, rfl, ⟨HF, HE⟩⟩
  refine evstep_progress ?_ (by ne_cfg)
  rcases HL with _ | _ | ⟨s, Hs⟩ | ⟨s, Hs⟩ | _ | a
  · refine step_bridge (cleanup_one_zero r) (by cfg_eq) ?_
    refine step_bridge (HF.flow_root 0 0) (by cfg_eq) ?_
    exact step_end (root_plain_terminal ((1 + N) * 2) 0 c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_one_entry default 0 r) (by cfg_eq) ?_
    refine step_bridge (crossV_zero r 0 2 0) (by cfg_eq) ?_
    refine step_bridge (HF.flow_root 2 0) (by cfg_eq) ?_
    exact step_end (root_plain_terminal ((1 + N) * 2 + 2) 0 c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_one_entry default (1 + s * 2) r) (by cfg_eq) ?_
    refine step_bridge (HF.flow_border s (N - s) 0 (by omega)) (by cfg_eq) ?_
    exact step_end (root_plain_terminal ((N - s) * 2) (1 + s) c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_one_entry default (2 + s * 2) r) (by cfg_eq) ?_
    refine step_bridge (HE s (N - s) 0 (by omega)) (by cfg_eq) ?_
    exact step_end (root_plain_terminal (2 + (N - s) * 2) (1 + s) c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_one_entry default (3 + N * 2) r) (by cfg_eq) ?_
    refine step_bridge (HF.flow_cross default 1 0) (by cfg_eq) ?_
    exact step_end (crossW_last_one (1 + N) c e He) (by cfg_eq) (by cfg_eq)
  · refine step_bridge (cleanup_one_entry default (4 + N * 2 + a) r) (by cfg_eq) ?_
    refine step_bridge (HF.flow_cross default (2 + a) 0) (by cfg_eq) ?_
    exact step_end (cross_plain_terminal default a (1 + N) c e He) (by cfg_eq) (by cfg_eq)

theorem OneCleanup_triple (g d e : Nat) (He : e ≤ 1) :
    OneCleanup ((([1, 0, 1, 0, 0, 1] : zF) ^ g) +> clean_input (1 + g * 2) (d * 2 + e) default)
      (3 + g * 4 + d + e) (2 + g + d * 2 + e) := by
  rcases g with _ | g
  · rcases Pass_clean_tail_low 0 d e He with ⟨C_out, E, HE, HC, HP⟩
    exact ⟨C_out, E, HE, by omega, Pass_eq HP⟩
  · rcases Pass_clean_tail (1 + g) d e g He with ⟨C_out, E, HE, HC, HP⟩
    refine ⟨C_out, E, HE, by omega, ?_⟩
    have h1 : Pass (fun l a b => crossV l ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + g))
                                   +> clean_input (1 + (1 + g) * 2) (d * 2 + e) default) a b 2 0)
                   (fun a b => rootV ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + g))
                                 +> clean_input (1 + (1 + g) * 2) (d * 2 + e) default) a b 2 0)
                   (fun l a b => crossV l (clean_input (1 + (1 + g) * 2) (d * 2 + e) default)
                                   a b (3 + 0) (0 + g))
                   (fun a b => rootV (clean_input (1 + (1 + g) * 2) (d * 2 + e) default) a b (3 + 0)
                                 (0 + g)) 2 :=
      Pass_eq (Pass_V_low (clean_input (1 + (1 + g) * 2) (d * 2 + e) default) g)
    have h2 : Pass (fun l a b => crossV l (clean_input (1 + (1 + g) * 2) (d * 2 + e) default)
                                   a b (3 + 0) (0 + g))
                   (fun a b => rootV (clean_input (1 + (1 + g) * 2) (d * 2 + e) default) a b (3 + 0)
                                 (0 + g))
                   (fun l a b => crossV l (clean_input (1 + (1 + g) * 2) (d * 2 + e) default)
                                   a b (3 + g) 0)
                   (fun a b => rootV (clean_input (1 + (1 + g) * 2) (d * 2 + e) default) a b (3 + g)
                                 0) (g * 2) :=
      Pass_eq (Pass_Vs (clean_input (1 + (1 + g) * 2) (d * 2 + e) default) 0 0 g)
    exact Pass_eq (Pass_trans h1 (Pass_trans h2 HP))

theorem cleanup_triple_one_section (g d e t : Nat) (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1)
    (HL : CleanLast (3 + g * 4 + d + e) (2 + g + d * 2 + e) t xs) :
    (section_481 [(2 + g * 2 + (d * 2 + e)) + (2 + g * 2), 1, t])
        [target_tm]⊢⁺ (section_481 xs) := by
  refine evstep_progress_trans ?_ (OneCleanup_spec _ _ _ t xs (OneCleanup_triple g d e He) HL)
  refine step_bridge (return_even ((([1, 1, 0] : zF) ^ 1) +> ((([1, 0] : zF) ^ t) +> default))
      g (d * 2 + e) HP) (by cfg_eq) ?_
  exact step_end (pass_011 ((([1, 0] : zF) ^ t) +> default) _ 1) (by cfg_eq) (by cfg_eq)

theorem cleanup_odd_triple_section (g b d e t : Nat) (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1)
    (HL : CleanLast (3 + b + g * 4 + d + e) (2 + b * 2 + g + d * 2 + e) t xs) :
    (section_481 [(2 + g * 2 + (d * 2 + e)) + (2 + g * 2), 1 + b * 2, t])
        [target_tm]⊢⁺ (section_481 xs) := by
  rcases b with _ | b
  · exact cleanup_triple_one_section g d e t xs HP He (CleanLast_eq HL)
  · exact step_end_plus_eq (cleanup_triple_section g b d e t xs HP He (CleanLast_eq HL)) (by cfg_eq)
        rfl

def count00 : Fin 2 → zF → Nat
  | _, [] => 0
  | p, x :: w => (if p == 0 && x == 0 then 1 else 0) + count00 x w

theorem count00_U (n : Nat) (w : zF) (k : Nat) (H : ∀ p, count00 p w = k) (p : Fin 2) :
    count00 p ((([1, 0] : zF) ^ n) ++ w) = k := by
  induction n generalizing p with
  | zero => exact H p
  | succ n ih =>
    rcases p with ⟨_ | _ | p, hp⟩ <;> try omega
    · dsimp [list_pow_succ, count00]; rw [ih 0]; omega
    · dsimp [list_pow_succ, count00]; rw [ih 0]; omega

theorem count00_V (n : Nat) (w : zF) (k : Nat) (H : ∀ p, count00 p w = k) (p : Fin 2) :
    count00 p ((([1, 0, 1, 0, 0, 1] : zF) ^ n) ++ w) = n + k := by
  induction n generalizing p with
  | zero => simp only [list_pow_zero, List.nil_append, Nat.zero_add, H p]
  | succ n ih =>
    rcases p with ⟨_ | _ | p, hp⟩ <;> try omega
    · dsimp [list_pow_succ, count00]; rw [ih 1]; omega
    · dsimp [list_pow_succ, count00]; rw [ih 1]; omega

theorem EraseWord_count00 (w : zF) (u v : Nat) (H : EraseWord w u v) (p : Fin 2) :
    count00 p w = v := by
  induction H generalizing p with
  | Erase_nil => rfl
  | Erase_V n w u v _ ih => exact count00_V n w v ih p
  | Erase_pair j k w u v _ ih =>
    rw [List.append_assoc]
    exact count00_U (2 + j * 2) _ (1 + k + v) (fun q => count00_V (1 + k) w v ih q) p

theorem EraseWord_unique (w : zF) (u v u' v' : Nat)
    (H : EraseWord w u v) (K : EraseWord w u' v') : u = u' ∧ v = v' := by
  have hc1 := EraseWord_count00 w u v H 1
  have hc2 := EraseWord_count00 w u' v' K 1
  have hs1 := EraseWord_size w u v H
  have hs2 := EraseWord_size w u' v' K
  omega

def column_U : List (Nat × Nat) → Nat
  | [] => 0
  | (_, b) :: cs => 1 + b + column_U cs

def column_V : List (Nat × Nat) → Nat
  | [] => 0
  | (a, _) :: cs => 1 + a + column_V cs

theorem column_word_erase (cs : List (Nat × Nat)) : EraseWord (column_word cs) (column_U cs)
    (column_V cs) := by
  induction cs with
  | nil => exact EraseWord.Erase_nil
  | cons ab cs ih =>
    rcases ab with ⟨a, b⟩
    dsimp [column_word, column_U, column_V]
    exact EraseWord_eq (EraseWord_app _ _ _ _ _ _ ih (EraseWord.Erase_pair b a [] 0 0
        EraseWord.Erase_nil))

theorem ColumnRun_balance (n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : ColumnRun n cs m) :
    m + column_V cs = n + column_U cs := by
  induction H with
  | Columns_nil => rfl
  | Columns_cons n a b cs m Ha _ ih => dsimp [column_U, column_V]; omega

theorem Pass_erase_pair_low (r : zB) (j k : Nat) :
    Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF)
                         ^ (1 + k)) +> r)) a b 2 0)
         (fun a b => rootV ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k))
                       +> r)) a b 2 0)
         (fun l a b => crossV l r a b (3 + k) 0)
         (fun a b => rootV r a b (3 + k) 0) ((2 + j + k) * 2) := by
  have h1 : Pass (fun l a b => crossV l ((([1, 0] : zF) ^ (2 + j * 2))
                                 +> ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r)) a b 2 0)
                 (fun a b => rootV ((([1, 0] : zF) ^ (2 + j * 2)) +> ((([1, 0, 1, 0, 0, 1] : zF)
                               ^ (1 + k)) +> r)) a b 2 0)
                 (fun l a b => crossZ l ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) a b (3 + 0)
                                 (1 + j * 2))
                 (fun a b => rootZ ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) a b (3 + 0)
                               (1 + j * 2)) 2 :=
    Pass_eq (Pass_Vend_low ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) (1 + j * 2))
  have h2 := Pass_Zs ((([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) +> r) 0 1 j
  have h3 := Pass_Z_to_V r 0 k
  have h4 : Pass (fun l a b => crossV l r a b (3 + 0) k)
                 (fun a b => rootV r a b (3 + 0) k)
                 (fun l a b => crossV l r a b (3 + k) 0)
                 (fun a b => rootV r a b (3 + k) 0) (k * 2) :=
    Pass_eq (Pass_Vs r 0 0 k)
  exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 h4)))

theorem Pass_Vs_low (r : zB) (e n : Nat) :
    Pass (fun l a b => crossV l r a b 2 (e + n))
         (fun a b => rootV r a b 2 (e + n))
         (fun l a b => crossV l r a b (2 + n) e)
         (fun a b => rootV r a b (2 + n) e) (n * 2) := by
  rcases n with _ | n
  · exact Pass_eq (Pass_id _ _)
  · have h1 : Pass (fun l a b => crossV l r a b 2 (e + (n + 1)))
                   (fun a b => rootV r a b 2 (e + (n + 1)))
                   (fun l a b => crossV l r a b (3 + 0) (e + n))
                   (fun a b => rootV r a b (3 + 0) (e + n)) 2 :=
      Pass_eq (Pass_V_low r (e + n))
    exact Pass_eq (Pass_trans h1 (Pass_Vs r 0 e n))

theorem EraseWord_pass_low (w : zF) (u v : Nat) (H : EraseWord w u v) (r : zB) :
    Pass (fun l a b => crossV l (w +> r) a b 2 0)
         (fun a b => rootV (w +> r) a b 2 0)
         (fun l a b => crossV l r a b (2 + v) 0)
         (fun a b => rootV r a b (2 + v) 0) ((u + v) * 2) := by
  induction H generalizing r with
  | Erase_nil => exact Pass_eq (Pass_id _ _)
  | Erase_V n w u v H ih =>
    rcases n with _ | n
    · exact Pass_eq (ih r)
    · have h1 : Pass (fun l a b => crossV l (((([1, 0, 1, 0, 0, 1] : zF) ^ (n + 1)) ++ w) +> r)
                                     a b 2 0)
                     (fun a b => rootV (((([1, 0, 1, 0, 0, 1] : zF) ^ (n + 1)) ++ w) +> r) a b 2 0)
                     (fun l a b => crossV l (w +> r) a b (3 + n) 0)
                     (fun a b => rootV (w +> r) a b (3 + n) 0) ((1 + n) * 2) :=
        Pass_eq (Pass_Vs_low (w +> r) 0 (1 + n))
      exact Pass_eq (Pass_trans h1 (EraseWord_pass w u v H r n))
  | Erase_pair j k w u v H ih =>
    have h1 : Pass (fun l a b => crossV l (((([1, 0] : zF) ^ (2 + j * 2))
                                   ++ (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + k)) ++ w) +> r) a b 2 0)
                   (fun a b => rootV (((([1, 0] : zF) ^ (2 + j * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
                                 ^ (1 + k)) ++ w) +> r) a b 2 0)
                   (fun l a b => crossV l (w +> r) a b (3 + k) 0)
                   (fun a b => rootV (w +> r) a b (3 + k) 0) ((2 + j + k) * 2) :=
      Pass_eq (Pass_erase_pair_low (w +> r) j k)
    exact Pass_eq (Pass_trans h1 (EraseWord_pass w u v H r k))

theorem Pass_clean_link_low (j n : Nat) (z : zF) (u v c d : Nat) (r : zB) (HZ : EraseWord z u v) :
    Pass (fun l a b => crossV l (clean_input (1 + j * 2) (n * 2) (link z c d r)) a b 2 0)
         (fun a b => rootV (clean_input (1 + j * 2) (n * 2) (link z c d r)) a b 2 0)
         (fun l a b => crossV l (clean_input c d r) a b (3 + n * 2 + v) 0)
         (fun a b => rootV (clean_input c d r) a b (3 + n * 2 + v) 0) (4 + j * 2 + n + (u + v)
                       * 2) := by
  rcases n with _ | n
  · have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) 0 (link z c d r)) a b 2 0)
                   (fun a b => rootV (clean_input (1 + j * 2) 0 (link z c d r)) a b 2 0)
                   (fun l a b => crossV l (z +> clean_input c d r) a b (3 + 0) 0)
                   (fun a b => rootV (z +> clean_input c d r) a b (3 + 0) 0) ((2 + j) * 2) :=
      Pass_eq (Pass_erase_pair_low (z +> clean_input c d r) j 0)
    exact Pass_eq (Pass_trans h1 (EraseWord_pass z u v HZ (clean_input c d r) 0))
  · have h1 : Pass (fun l a b => crossV l (clean_input (1 + j * 2) ((n + 1) * 2) (link z c d r))
                                   a b 2 0)
                   (fun a b => rootV (clean_input (1 + j * 2) ((n + 1) * 2) (link z c d r)) a b 2 0)
                   (fun l a b => crossZ l (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF)
                                   ^ (1 + (1 + n * 2))) +> link z c d r)) a b (3 + 0) (0 + j * 2))
                   (fun a b => rootZ (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
                                 +> link z c d r)) a b (3 + 0) (0 + j * 2)) 2 :=
      Pass_eq (Pass_Vend_low (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
          +> link z c d r)) (j * 2))
    have h2 := Pass_Zs (([1, 0, 1] : zF) +> ((([0, 1, 0] : zF) ^ (1 + (1 + n * 2)))
        +> link z c d r)) 0 0 j
    have h3 := Pass_Z_back_low (link z c d r) (1 + n * 2)
    have h4 : Pass (fun l a b => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                   0 (2 + (1 + n * 2)))
                   (fun a b => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b)
                                 0 (2 + (1 + n * 2)))
                   (fun l a b => crossW l (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) ((1 + n)
                                   * 2) 1)
                   (fun a b => rootW (link z c d r) a (([1, 0, 1, 0, 0, 1] : zF) ^ b) ((1 + n) * 2)
                                 1) (1 + n) :=
      Pass_eq (Pass_Ws (link z c d r) 0 1 (1 + n))
    have h5 := Pass_odd_join r ((1 + n) * 2) z c d
    have h6 := EraseWord_pass z u v HZ (clean_input c d r) ((1 + n) * 2)
    exact Pass_eq (Pass_trans h1 (Pass_trans h2 (Pass_trans h3 (Pass_trans h4 (Pass_trans h5 h6)))))

theorem RRoute_clean_low (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat)
    (HR : RRoute c d r n w C_out e default) (He : e ≤ 1) :
    ∃ u v N C' E, EraseWord w u v ∧ E ≤ 1 ∧
      N + n = (u + v) * 2 + 3 + C_out + e ∧ C' + E = 1 + v + n * 2 + e ∧
      Pass (fun l a b => crossV l (clean_input c d r) a b 2 0)
           (fun a b => rootV (clean_input c d r) a b 2 0)
           (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E)
           (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E) N := by
  generalize hR : (default : zB) = R at HR
  rcases HR with ⟨j, n, e, r⟩ | ⟨j, n, z, x, y, c', d, r, m, w, C_out, e, R, HZ, HR⟩
  · subst hR
    rcases Pass_clean_tail_low j n e He with ⟨C', E, HE, HC, HP⟩
    exact ⟨0, 0, 4 + j * 2 + n + e, C', E, EraseWord.Erase_nil, HE, by omega, by omega, HP⟩
  · subst hR
    rcases RRoute_clean c' d r m w C_out e default HR rfl He with ⟨u, v, HW, HK⟩
    rcases HK (n * 2 + y) with ⟨N, C', E, HE, HN, HC, HP⟩
    refine ⟨1 + (j + n) + x + u, 1 + y + v, 4 + j * 2 + n + (x + y) * 2 + N, C', E, ?_, HE,
        by omega, by omega, ?_⟩
    · exact EraseWord_eq (EraseWord.Erase_pair (j + n) 0 (z ++ w) (x + u) (y + v)
          (EraseWord_app z x y w u v HZ HW))
    · have h1 := Pass_clean_link_low j n z x y c' d r HZ
      have h2 : Pass (fun l a b => crossV l (clean_input c' d r) a b (3 + n * 2 + y) 0)
                     (fun a b => rootV (clean_input c' d r) a b (3 + n * 2 + y) 0)
                     (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E)
                     (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E) N :=
        Pass_eq HP
      exact Pass_eq (Pass_trans h1 h2)

theorem RRoute_clean_at2 (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e u v k : Nat)
    (HR : RRoute c d r n w C_out e default) (HW : EraseWord w u v) (He : e ≤ 1) :
    ∃ N C' E, E ≤ 1 ∧ N + n = (u + v) * 2 + 3 + C_out + e ∧ C' + E = 1 + k + v + n * 2 + e ∧
      Pass (fun l a b => crossV l (clean_input c d r) a b (2 + k) 0)
           (fun a b => rootV (clean_input c d r) a b (2 + k) 0)
           (fun l a b => crossW l default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E)
           (fun a b => rootW default a (([1, 0, 1, 0, 0, 1] : zF) ^ b) C' E) N := by
  rcases k with _ | k
  · rcases RRoute_clean_low c d r n w C_out e HR He with ⟨x, y, N, C', E, HZ, HE, HN, HC, HP⟩
    rcases EraseWord_unique w x y u v HZ HW with ⟨rfl, rfl⟩
    exact ⟨N, C', E, HE, HN, by omega, Pass_eq HP⟩
  · rcases RRoute_clean c d r n w C_out e default HR rfl He with ⟨x, y, HZ, HK⟩
    rcases EraseWord_unique w x y u v HZ HW with ⟨rfl, rfl⟩
    rcases HK k with ⟨N, C', E, HE, HN, HC, HP⟩
    exact ⟨N, C', E, HE, HN, by omega, Pass_eq HP⟩

theorem RRoute_capacity_bound (c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat) (R : zB)
    (HR : RRoute c d r n w C_out e R) (u v : Nat) (HW : EraseWord w u v) : n ≤ u + C_out := by
  induction HR generalizing u v with
  | RRoute_done => omega
  | RRoute_more j n z x y c' d r m w C_out e R HZ HR ih =>
    rcases RRoute_erase _ _ _ _ _ _ _ _ HR with ⟨i, k, HK⟩
    have hi := ih i k HK
    have HT : EraseWord (([1, 0] : zF) ^ (2 + (j + n) * 2) ++ [1, 0, 1, 0, 0, 1] ++ z ++ w)
        (1 + (j + n) + x + i) (1 + y + k) :=
      EraseWord_eq (EraseWord.Erase_pair (j + n) 0 (z ++ w) (x + i) (y + k)
          (EraseWord_app z x y w i k HZ HK))
    rcases EraseWord_unique _ _ _ _ _ HW HT with ⟨rfl, rfl⟩
    omega

theorem RRoute_one_cleanup (z : zF) (i j c d : Nat) (r : zB) (n : Nat) (w : zF) (C_out e : Nat)
    (HZ : EraseWord z i j) (HR : RRoute c d r n w C_out e default) (He : e ≤ 1) :
    ∃ u v N X, EraseWord w u v ∧
      N + n = (i + j + u + v) * 2 + 2 + C_out + e ∧ X = 2 + j + v + n * 2 + e ∧
      OneCleanup (z +> clean_input c d r) N X := by
  rcases RRoute_erase _ _ _ _ _ _ _ _ HR with ⟨u, v, HW⟩
  rcases RRoute_clean_at2 c d r n w C_out e u v j HR HW He with ⟨N, C', E, HE, HN, HC, HP⟩
  have hcap := RRoute_capacity_bound c d r n w C_out e default HR u v HW
  refine ⟨u, v, (i + j) * 2 + N - 1, 1 + C' + E, HW, by omega, by omega, ?_⟩
  refine ⟨C', E, HE, rfl, ?_⟩
  exact Pass_eq (Pass_trans (EraseWord_pass_low z i j HZ (clean_input c d r)) HP)

theorem RCounter_one_cleanup (l r : zB) (n : Nat) (w : zF) (C_out e a : Nat)
    (HR : RCounter r n w C_out e) (Ha : a ≤ n) (He : e ≤ 1) :
    ∃ u v N X r', EraseWord w u v ∧
      N + n = a * 3 + (u + v) * 2 + 2 + C_out + e ∧ X + a = 2 + v + n * 2 + e ∧ OneCleanup r' N X ∧
      ((((([1, 0] : zF) ^ (2 + a * 2)) +> (([1, 1, 0] : zF) +> l)) <{{C}} (([0, 1] : zF) +> r)))
          [target_tm]⊢*
        (l <{{C}} (([0, 1, 0, 1, 0, 0, 1, 0, 0, 1] : zF) +> r')) := by
  rcases HR with ⟨d, s, rfl, HR⟩
  rcases RRoute_scan 1 d s n w C_out e default HR a (([1, 1, 0] : zF) +> l)
      [] [] [] Ha Word_nil with
    ⟨c', d', s', u, z, i, j, HZ, EW, HU, HS⟩
  rcases RRoute_one_cleanup ((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) i (a + j) c' d' s' (n - a)
      z C_out e
    (EraseWord.Erase_V a u i j HU) HZ He with ⟨x, y, N, X, HW, HN, HX, HC⟩
  refine ⟨i + x, j + y, N, X, (((([1, 0, 1, 0, 0, 1] : zF) ^ a) ++ u) +> clean_input c' d' s'), ?_,
      by omega, by omega, HC, ?_⟩
  · rw [EW]; exact EraseWord_app u i j z x y HU HW
  · refine step_bridge (scan_pair ((([1, 0] : zF) ^ (a * 2)) +> (([1, 1, 0] : zF) +> l)) s 0 d)
        (by cfg_eq) ?_
    refine ReachesStar.trans HS ?_
    exact step_end (pass_011 l _ 1) (by cfg_eq) (by cfg_eq)

def CleanRight (r : zB) (N X : Nat) : Prop :=
  ∀ t xs, CleanLast N X t xs →
    ((((([1, 0] : zF) ^ t) +> default) <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢⁺ (section_481 xs)

theorem Cleanup_right (r : zB) (N X : Nat) (H : Cleanup r N X) : CleanRight r N X :=
  fun t xs HL => Cleanup_spec r N X t xs H HL

theorem OneCleanup_right (r : zB) (N X : Nat) (H : OneCleanup r N X) :
    CleanRight (([0, 1, 0, 0, 1, 0, 0, 1] : zF) +> r) N X :=
  fun t xs HL => step_end_plus_eq (OneCleanup_spec r N X t xs H HL) (by cfg_eq) rfl

theorem RCounter_odd_cleanup (l r : zB) (n : Nat) (w : zF) (C_out e a b : Nat)
    (HR : RCounter r n w C_out e) (Ha : a ≤ n) (He : e ≤ 1) :
    ∃ u v N X r', EraseWord w u v ∧
      N + n = b + a * 3 + (u + v)
          * 2 + 2 + C_out + e ∧ X + a = 2 + b * 2 + v + n * 2 + e ∧ CleanRight r' N X ∧
      ((((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF) ^ (1 + b * 2)) +> l))
          <{{C}} (([0, 1] : zF) +> r))) [target_tm]⊢*
        (l <{{C}} (([0, 1] : zF) +> r')) := by
  rcases b with _ | b
  · rcases RCounter_one_cleanup l r n w C_out e a HR Ha He with ⟨u, v, N, X, r', HW, HN, HX, HC, HT⟩
    refine ⟨u, v, N, X, (([0, 1, 0, 0, 1, 0, 0, 1] : zF) +> r'), HW, by omega, by omega,
        OneCleanup_right r' N X HC, ?_⟩
    exact step_end HT (by cfg_eq) (by cfg_eq)
  · rcases RCounter_cleanup l r n w C_out e a b HR Ha He with ⟨u, v, N, X, r', HW, HN, HX, HC, HT⟩
    refine ⟨u, v, N, X, r', HW, by omega, by omega, Cleanup_right r' N X HC, ?_⟩
    exact step_end HT (by cfg_eq) (by cfg_eq)

def column_list : List (Nat × Nat) → List Nat
  | [] => []
  | (a, b) :: cs => (2 + a * 2) :: (2 + b * 2) :: column_list cs

theorem column_list_side (cs : List (Nat × Nat)) (xs : List Nat) :
    section_side (column_list cs ++ xs) true = column_side (section_side xs true) cs := by
  induction cs with
  | nil => rfl
  | cons ab cs ih =>
    rcases ab with ⟨a, b⟩
    dsimp [column_list, section_side, column_side]
    rw [ih]

theorem column_image_side (cs : List (Nat × Nat)) (xs : List Nat) :
    section_side (column_list cs ++ xs)
        false = (column_image cs).reverse +> section_side xs false := by
  induction cs with
  | nil => rfl
  | cons ab cs ih =>
    rcases ab with ⟨a, b⟩
    dsimp [column_list, section_side, column_image]
    rw [ih]
    cfg_eq

theorem restored_section (p g b : Nat) (cs : List (Nat × Nat)) (a t : Nat) :
    section_481 (p :: (2 + g * 2) :: b :: column_list cs ++ [a, t]) =
    (((([1, 0] : zF) ^ p) +> (((column_image cs ++ ([0, 1] : zF) ^ b ++ ([0, 1, 1, 0, 1, 1] : zF)
        ^ (1 + g)).reverse) +> ((([1, 1, 0] : zF) ^ a) +> ((([1, 0] : zF) ^ t) +> default))))
            {{B}}> default) := by
  dsimp only [section_481, section_side, List.cons_append]
  rw [column_image_side]
  dsimp only [section_side]
  cfg_eq

theorem restored_section_good (p : Nat) (cs : List (Nat × Nat)) (a t : Nat) :
    section_481 (p :: column_list cs ++ [a, t]) =
    (((([1, 0] : zF) ^ p) +> ((column_image cs).reverse +> ((([1, 1, 0] : zF) ^ a)
        +> ((([1, 0] : zF) ^ t) +> default)))) {{B}}> default) := by
  dsimp only [section_481, section_side, List.cons_append]
  rw [column_image_side]
  dsimp only [section_side]

theorem gap_column_word (g b : Nat) (cs : List (Nat × Nat)) :
    ∃ x, Word (column_word cs ++ ((([1, 0] : zF) ^ (2 + b * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF)
        ^ (1 + g)))) x
      (column_image cs ++ ((([0, 1] : zF) ^ (2 + b * 2)) ++ (([0, 1, 1, 0, 1, 1] : zF)
          ^ (1 + g)))) := by
  rcases column_word_spec cs with ⟨x, HX⟩
  exact ⟨_, Word_app _ _ _ _ _ _ HX (Word_app _ _ _ _ _ _ (Word_pow _ _ _ (2 + b * 2) Word_U)
      (Word_pow _ _ _ (1 + g) Word_V))⟩

theorem gap_normal_section (g b d e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (HC : ColumnRun (b + d) cs m) (Hs : s ≤ m) (He : e ≤ 1) :
    (section_481 (((2 + g * 2 + (d * 2 + e))
        + (2 + g * 2)) :: (2 + b * 2) :: column_list cs ++ [3 + s * 2])) [target_tm]⊢⁺
    (section_481 ((2 + g * 2 + (d * 2 + e)) :: (2 + g * 2) :: (2 + b * 2) :: column_list cs ++
        [2 + s * 2, 5 + (m - s) * 2])) := by
  rcases gap_column_word g b cs with ⟨x, HW⟩
  have h1 := section_columns_normal (b + d) _ (1 + g * 2 + d * 2) e _ cs m s x _
    (SectionStart.Start_gap g b d e HP) HC Hs He HW
  refine step_end_plus_eq h1 ?_ ?_
  · dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]
  · rw [restored_section]; cfg_eq

theorem gap_overflow_section (g b d e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (HC : ColumnRun (b + d) cs m) (He : e ≤ 1) :
    (section_481 (((2 + g * 2 + (d * 2 + e))
        + (2 + g * 2)) :: (2 + b * 2) :: column_list cs ++ [5 + m * 2 + s * 2])) [target_tm]⊢⁺
    (section_481 ((2 + g * 2 + (d * 2 + e)) :: (2 + g * 2) :: (2 + b * 2) :: column_list cs ++
        [5 + m * 2, s * 2])) := by
  rcases gap_column_word g b cs with ⟨x, HW⟩
  have h1 := section_columns_overflow (b + d) _ (1 + g * 2 + d * 2) e _ cs m s x _
    (SectionStart.Start_gap g b d e HP) HC He HW
  refine step_end_plus_eq h1 ?_ ?_
  · dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]
  · rw [restored_section]; cfg_eq

theorem good_normal_section (d b e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (HP : P (2 + d * 2 + e)) (HC : ColumnRun (1 + d + b) cs m) (Hs : s ≤ m) (He : e ≤ 1) :
    (section_481 ((2 + d * 2 + e) :: (2 + b * 2) :: column_list cs ++ [3 + s * 2])) [target_tm]⊢⁺
    (section_481 ((4 + d * 2 + b * 2 + e) :: column_list cs ++ [2 + s * 2, 5 + (m - s) * 2])) := by
  rcases column_word_spec cs with ⟨x, HW⟩
  rw [← List.append_nil (column_word cs)] at HW
  have h1 := section_columns_normal (1 + d + b) [] (3 + d * 2 + b * 2) e _ cs m s x _
    (SectionStart.Start_good d b e HP) HC Hs He HW
  refine step_end_plus_eq h1 ?_ ?_
  · dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]
  · rw [restored_section_good]; cfg_eq

theorem good_overflow_section (d b e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (HP : P (2 + d * 2 + e)) (HC : ColumnRun (1 + d + b) cs m) (He : e ≤ 1) :
    (section_481 ((2 + d * 2 + e) :: (2 + b * 2) :: column_list cs ++ [5 + m * 2 + s * 2]))
        [target_tm]⊢⁺
    (section_481 ((4 + d * 2 + b * 2 + e) :: column_list cs ++ [5 + m * 2, s * 2])) := by
  rcases column_word_spec cs with ⟨x, HW⟩
  rw [← List.append_nil (column_word cs)] at HW
  have h1 := section_columns_overflow (1 + d + b) [] (3 + d * 2 + b * 2) e _ cs m s x _
    (SectionStart.Start_good d b e HP) HC He HW
  refine step_end_plus_eq h1 ?_ ?_
  · dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]
  · rw [restored_section_good]; cfg_eq

theorem section_columns_cleanup (n : Nat) (w : zF) (C_out e : Nat) (c : Cfg (Fin 2) (Fin 6))
    (cs : List (Nat × Nat)) (m a b u v t : Nat)
    (HStart : SectionStart (column_side (((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF)
        ^ (1 + b * 2)) +> ((([1, 0] : zF) ^ t) +> default)))) cs) n w C_out e c)
    (HW : EraseWord w u v) (HCols : ColumnRun n cs m) (Ha : a ≤ m) (He : e ≤ 1) :
    ∃ N X, N + m = b + a * 3 + (column_U cs + column_V cs + u + v) * 2 + 2 + C_out + e ∧
      X + a = 2 + b * 2 + column_V cs + v + m * 2 + e ∧
      ∀ xs, CleanLast N X t xs → c [target_tm]⊢⁺ (section_481 xs) := by
  rcases SectionStart_Rspec _ _ _ _ _ _ HStart with ⟨r, HR, T0⟩
  rcases RCounter_columns n cs m HCols (((([1, 0] : zF) ^ (2 + a * 2)) +> ((([1, 1, 0] : zF)
      ^ (1 + b * 2)) +> ((([1, 0] : zF) ^ t) +> default)))) r w C_out e HR with ⟨r0, H0, T1⟩
  rcases RCounter_odd_cleanup ((([1, 0] : zF) ^ t) +> default) r0 m _ C_out e a b H0 Ha He with ⟨i,
      j, N, X, r1, H1, HN, HX, HC, T2⟩
  rcases EraseWord_unique _ _ _ _ _ H1 (EraseWord_app _ _ _ _ _ _ (column_word_erase cs) HW)
      with ⟨rfl, rfl⟩
  refine ⟨N, X, by omega, by omega, fun xs HL => ?_⟩
  exact evstep_progress_trans T0 (evstep_progress_trans T1 (evstep_progress_trans T2 (HC t xs HL)))

theorem gap_cleanup_section (g b0 d e : Nat) (cs : List (Nat × Nat)) (m a b t N X : Nat)
    (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (HCols : ColumnRun (b0 + d) cs m) (Ha : a ≤ m) (He : e ≤ 1)
    (HN : N + m = b + a * 3 + (column_U cs + column_V cs + (1 + b0) + (1 + g))
        * 2 + 3 + g * 2 + d * 2 + e)
    (HX : X + a = 3 + b * 2 + column_V cs + g + m * 2 + e) (HL : CleanLast N X t xs) :
    (section_481 (((2 + g * 2 + (d * 2 + e))
        + (2 + g * 2)) :: (2 + b0 * 2) :: column_list cs ++ [2 + a * 2, 1 + b * 2, t]))
            [target_tm]⊢⁺
    (section_481 xs) := by
  have HW : EraseWord ((([1, 0] : zF) ^ (2 + b0 * 2)) ++ (([1, 0, 1, 0, 0, 1] : zF) ^ (1 + g)))
      (1 + b0) (1 + g) :=
    EraseWord_eq (EraseWord.Erase_pair b0 g [] 0 0 EraseWord.Erase_nil)
  rcases section_columns_cleanup (b0 + d) _ (1 + g * 2 + d * 2) e _ cs m a b (1 + b0) (1 + g) t
    (SectionStart.Start_gap g b0 d e HP) HW HCols Ha He with ⟨N0, X0, HN0, HX0, HT⟩
  have hN : N0 = N := by omega
  have hX : X0 = X := by omega
  subst hN; subst hX
  refine step_end_plus_eq (HT xs HL) ?_ rfl
  dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]

theorem good_cleanup_section (d b0 e : Nat) (cs : List (Nat × Nat)) (m a b t N X : Nat)
    (xs : List Nat)
    (HP : P (2 + d * 2 + e)) (HCols : ColumnRun (1 + d + b0) cs m) (Ha : a ≤ m) (He : e ≤ 1)
    (HN : N + m = b + a * 3 + (column_U cs + column_V cs) * 2 + 5 + d * 2 + b0 * 2 + e)
    (HX : X + a = 2 + b * 2 + column_V cs + m * 2 + e) (HL : CleanLast N X t xs) :
    (section_481 ((2 + d * 2 + e) :: (2 + b0 * 2) :: column_list cs ++ [2 + a * 2, 1 + b * 2, t]))
        [target_tm]⊢⁺
    (section_481 xs) := by
  rcases section_columns_cleanup (1 + d + b0) [] (3 + d * 2 + b0 * 2) e _ cs m a b 0 0 t
    (SectionStart.Start_good d b0 e HP) EraseWord.Erase_nil HCols Ha He with ⟨N0, X0, HN0, HX0, HT⟩
  have hN : N0 = N := by omega
  have hX : X0 = X := by omega
  subst hN; subst hX
  refine step_end_plus_eq (HT xs HL) ?_ rfl
  dsimp [section_481, section_side]; rw [column_list_side]; dsimp [section_side]

theorem P_eq {n1 n2 : Nat} (h : P n1) (heq : n1 = n2 := by omega) : P n2 := by subst heq; exact h
theorem PP_eq {n1 n2 : Nat} (h : PP n1) (heq : n1 = n2 := by omega) : PP n2 := by subst heq; exact h

inductive BoundedRun (h : Nat) : Nat → List (Nat × Nat) → Nat → Prop where
  | Bounded_nil (n : Nat) : n ≤ h → BoundedRun h n [] n
  | Bounded_cons (n a b : Nat) (cs : List (Nat × Nat)) (m : Nat) :
      n ≤ h → a ≤ n → BoundedRun h (n - a + b) cs m → BoundedRun h n ((a, b) :: cs) m

theorem Bounded_eq {h1 h2 n1 n2 m1 m2 : Nat} {cs1 cs2 : List (Nat × Nat)}
    (H : BoundedRun h1 n1 cs1 m1)
    (hh : h1 = h2 := by omega) (hn : n1 = n2 := by omega)
    (hcs : cs1 = cs2 := by rfl) (hm : m1 = m2 := by omega) :
    BoundedRun h2 n2 cs2 m2 := by
  subst hh; subst hn; subst hcs; subst hm; exact H

theorem Bounded_forget (h n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : BoundedRun h n cs m) :
    ColumnRun n cs m := by
  induction H with
  | Bounded_nil n _ => exact ColumnRun.Columns_nil n
  | Bounded_cons n a b cs m _ ha _ ih => exact ColumnRun.Columns_cons n a b cs m ha ih

theorem Bounded_ends (h n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : BoundedRun h n cs m) :
    n ≤ h ∧ m ≤ h := by
  induction H with
  | Bounded_nil n hn => exact ⟨hn, hn⟩
  | Bounded_cons n a b cs m hn _ _ ih => exact ⟨hn, ih.2⟩

def flip_columns (b : Nat) : List (Nat × Nat) → Nat → List (Nat × Nat)
  | [], s => [(b, s)]
  | (a, b') :: cs, s => (b, a) :: flip_columns b' cs s

def flip_front (b : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (a, b') :: cs => (b, a) :: flip_front b' cs

def last_column (b : Nat) : List (Nat × Nat) → Nat
  | [] => b
  | (_, b') :: cs => last_column b' cs

theorem flip_columns_list (b : Nat) (cs : List (Nat × Nat)) (s : Nat) :
    column_list (flip_columns b cs s) = (2 + b * 2) :: column_list cs ++ [2 + s * 2] := by
  induction cs generalizing b with
  | nil => rfl
  | cons ab cs ih =>
    rcases ab with ⟨a, b'⟩
    dsimp [flip_columns, column_list]
    rw [ih b']; rfl

theorem flip_front_list (b : Nat) (cs : List (Nat × Nat)) (xs : List Nat) :
    column_list (flip_front b cs) ++ (2 + last_column b cs * 2) :: xs =
      (2 + b * 2) :: column_list cs ++ xs := by
  induction cs generalizing b with
  | nil => rfl
  | cons ab cs ih =>
    rcases ab with ⟨a, b'⟩
    dsimp [flip_front, last_column, column_list]
    rw [ih b']; rfl

theorem flip_front_counts (b : Nat) (cs : List (Nat × Nat)) :
    column_U (flip_front b cs) = column_V cs ∧
    column_V (flip_front b cs) + last_column b cs = b + column_U cs := by
  induction cs generalizing b with
  | nil => dsimp [flip_front, last_column, column_U, column_V]; omega
  | cons ab cs ih =>
    rcases ab with ⟨a, b'⟩
    rcases ih b' with ⟨h1, h2⟩
    dsimp [flip_front, last_column, column_U, column_V]
    omega

theorem Bounded_flip (h n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : BoundedRun h n cs m)
    (b r s : Nat) (Hb : b ≤ n) (Hr : r + n = h + b) (Hs : s ≤ m) :
    BoundedRun h r (flip_columns b cs s) (h - m + s) := by
  induction H generalizing b r with
  | Bounded_nil n hn =>
    dsimp [flip_columns]
    refine BoundedRun.Bounded_cons r b s [] (h - n + s) (by omega) (by omega) ?_
    exact Bounded_eq (@BoundedRun.Bounded_nil h (h - n + s) (by omega))
  | Bounded_cons n a b' cs m hn ha _ ih =>
    dsimp [flip_columns]
    exact BoundedRun.Bounded_cons r b a (flip_columns b' cs s) (h - m + s) (by omega) (by omega)
      (ih b' (r - b + a) (by omega) (by omega) Hs)

theorem Bounded_flip_front (h n : Nat) (cs : List (Nat × Nat)) (m : Nat) (H : BoundedRun h n cs m)
    (b r : Nat) (Hb : b ≤ n) (Hr : r + n = h + b) :
    ∃ q, BoundedRun h r (flip_front b cs)
        q ∧ last_column b cs ≤ q ∧ q + m = h + last_column b cs := by
  induction H generalizing b r with
  | Bounded_nil n hn =>
    exact ⟨r, BoundedRun.Bounded_nil r (by omega), by dsimp [last_column]; omega,
        by dsimp [last_column]; omega⟩
  | Bounded_cons n a b' cs m hn ha _ ih =>
    rcases ih b' (r - b + a) (by omega) (by omega) with ⟨q, HQ, HL, HE⟩
    exact ⟨q, BoundedRun.Bounded_cons r b a (flip_front b' cs) q (by omega) (by omega) HQ, HL, HE⟩

inductive Stair (p e : Nat) : List Nat → Prop where
  | Stair_good (d b : Nat) (cs : List (Nat × Nat)) (m s : Nat) :
      p = 2 + d * 2 + e → BoundedRun (p - 1 - e) (1 + d + b) cs m → m + s = p - e →
      Stair p e (p :: (2 + b * 2) :: column_list cs ++ [3 + s * 2])
  | Stair_gap (g b d : Nat) (cs : List (Nat × Nat)) (m s : Nat) :
      p = 2 + g * 2 + (d * 2 + e) → BoundedRun (p - 1 - e) (b + d) cs m → m + s = p - e →
      Stair p e ((p + (2 + g * 2)) :: (2 + b * 2) :: column_list cs ++ [3 + s * 2])

macro "list_nat_eq" : tactic =>
  `(tactic| first
    | rfl
    | ((try simp only [flip_columns_list, flip_front_list, column_list,
          List.cons_append, List.nil_append, List.append_assoc,
          List.cons.injEq, list_append_inj, and_true, true_and]);
       ((repeat' constructor) <;> first | trivial | omega)))

theorem Stair_eq {p1 p2 e1 e2 : Nat} {xs1 xs2 : List Nat}
    (H : Stair p1 e1 xs1)
    (hp : p1 = p2 := by omega) (he : e1 = e2 := by omega) (hxs : xs1 = xs2 := by list_nat_eq) :
    Stair p2 e2 xs2 := by
  subst hp; subst he; subst hxs; exact H

theorem section_step_eq {xs1 xs2 ys1 ys2 : List Nat}
    (H : (section_481 xs1) [target_tm]⊢⁺ (section_481 ys1))
    (hxs : xs1 = xs2 := by list_nat_eq) (hys : ys1 = ys2 := by list_nat_eq) :
    (section_481 xs2) [target_tm]⊢⁺ (section_481 ys2) := by
  subst hxs; subst hys; exact H

theorem section_evstep_eq {xs1 xs2 ys1 ys2 : List Nat}
    (H : (section_481 xs1) [target_tm]⊢* (section_481 ys1))
    (hxs : xs1 = xs2 := by list_nat_eq) (hys : ys1 = ys2 := by list_nat_eq) :
    (section_481 xs2) [target_tm]⊢* (section_481 ys2) := by
  subst hxs; subst hys; exact H

theorem stair_gap_normal (g b d e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (_He : e ≤ 1) (HR : BoundedRun ((2 + g * 2 + (d * 2 + e)) - 1 - e) (b + d) cs m)
    (HS : m + s = (2 + g * 2 + (d * 2 + e)) - e) (Hs : s ≤ m) :
    Stair (2 + g * 2 + (d * 2 + e)) e
      ((2 + g * 2 + (d * 2 + e)) :: (2 + g * 2) :: (2 + b * 2) :: column_list cs ++
          [2 + s * 2, 5 + (m - s) * 2]) := by
  rcases Bounded_ends _ _ _ _ HR with ⟨Hn, Hm⟩
  refine Stair_eq (@Stair.Stair_good (2 + g * 2 + (d * 2 + e)) e (g + d) g (flip_columns b cs s)
    ((2 + g * 2 + (d * 2 + e)) - 1 - e - m + s) (1 + m - s) (by omega) ?_ (by omega))
  exact Bounded_flip _ _ _ _ HR b (1 + (g + d) + g) s (by omega) (by omega) Hs

theorem stair_good_normal (d b e : Nat) (cs : List (Nat × Nat)) (m s : Nat)
    (_He : e ≤ 1) (HR : BoundedRun ((2 + d * 2 + e) - 1 - e) (1 + d + b) cs m)
    (HS : m + s = (2 + d * 2 + e) - e) (Hs : s ≤ m) :
    Stair (2 + d * 2 + e)
        e ((4 + d * 2 + b * 2 + e) :: column_list cs ++ [2 + s * 2, 5 + (m - s) * 2]) := by
  rcases Bounded_ends _ _ _ _ HR with ⟨Hn, Hm⟩
  have Hb : b ≤ d := by omega
  rcases cs with _ | ⟨⟨a, b'⟩, cs⟩
  · cases HR with
    | Bounded_nil _ _ =>
      refine Stair_eq (@Stair.Stair_gap (2 + d * 2 + e) e b s (d - b) [] (s + (d - b))
          (1 + (1 + d + b) - s)
        (by omega) ?_ (by omega))
      exact BoundedRun.Bounded_nil _ (by omega)
  · cases HR with
    | Bounded_cons _ _ _ _ _ Hn' Ha HT =>
      refine Stair_eq (@Stair.Stair_gap (2 + d * 2 + e) e b a (d - b) (flip_columns b' cs s)
        ((2 + d * 2 + e) - 1 - e - m + s) (1 + m - s) (by omega) ?_ (by omega))
      exact Bounded_flip _ _ _ _ HT b' (a + (d - b)) s (by omega) (by omega) Hs

theorem clean_after_gap (g b d e : Nat) (cs : List (Nat × Nat)) (m t : Nat) (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1)
    (HR : BoundedRun ((2 + g * 2 + (d * 2 + e)) - 1 - e) (b + d) cs m)
    (HC : CleanLast ((2 + g * 2 + (d * 2 + e)) + (1 + b + column_U cs) * 4)
            ((2 + g * 2 + (d * 2 + e)) * 2 + 3 - e + (1 + b + column_U cs)) t xs) :
    (section_481 ((2 + g * 2 + (d * 2 + e)) :: (2 + g * 2) :: (2 + b * 2) :: column_list cs ++
        [5 + m * 2, t])) [target_tm]⊢⁺
    (section_481 xs) := by
  rcases Bounded_Ends : Bounded_ends _ _ _ _ HR with ⟨Hn, Hm⟩
  rcases Bounded_flip_front _ _ _ _ HR b (1 + (g + d) + g) (by omega) (by omega) with ⟨q, HQ, HL,
      HE⟩
  have HB := ColumnRun_balance _ _ _ (Bounded_forget _ _ _ _ HR)
  rcases flip_front_counts b cs with ⟨HU, HV⟩
  have HP' : P (2 + (g + d) * 2 + e) := P_eq HP
  have hstep := good_cleanup_section (g + d) g e (flip_front b cs) q (last_column b cs)
    (2 + m) t ((2 + g * 2 + (d * 2 + e)) + (1 + b + column_U cs) * 4)
    ((2 + g * 2 + (d * 2 + e)) * 2 + 3 - e + (1 + b + column_U cs)) xs
    HP' (Bounded_forget _ _ _ _ HQ) HL He (by omega) (by omega) HC
  refine section_step_eq hstep ?_ rfl
  have hfl := flip_front_list b cs [1 + (2 + m) * 2, t]
  simp only [List.cons_append] at hfl ⊢
  rw [hfl]
  list_nat_eq

theorem clean_after_good (d b e : Nat) (cs : List (Nat × Nat)) (m t : Nat) (xs : List Nat)
    (HP : P (2 + d * 2 + e)) (He : e ≤ 1)
    (HR : BoundedRun ((2 + d * 2 + e) - 1 - e) (1 + d + b) cs m)
    (HC : CleanLast ((2 + d * 2 + e) + (1 + b + column_U cs) * 4)
            ((2 + d * 2 + e) * 2 + 3 - e + (1 + b + column_U cs)) t xs) :
    (section_481 ((4 + d * 2 + b * 2 + e) :: column_list cs ++ [5 + m * 2, t])) [target_tm]⊢⁺
    (section_481 xs) := by
  rcases Bounded_ends _ _ _ _ HR with ⟨Hn, Hm⟩
  have Hb : b ≤ d := by omega
  rcases cs with _ | ⟨⟨a, b'⟩, cs⟩
  · cases HR with
    | Bounded_nil _ _ =>
      dsimp [column_list, column_U] at HC ⊢
      exact section_step_eq (cleanup_odd_triple_section b (2 + (1 + d + b)) (d - b) e t xs (P_eq HP)
          He (CleanLast_eq HC))
  · cases HR with
    | Bounded_cons _ _ _ _ _ Hn' Ha HT =>
      rcases Bounded_flip_front _ _ _ _ HT b' (a + (d - b)) (by omega) (by omega) with ⟨q, HQ, HL,
          HE⟩
      have HB := ColumnRun_balance _ _ _ (Bounded_forget _ _ _ _ HT)
      rcases flip_front_counts b' cs with ⟨HU, HV⟩
      have HP' : P (2 + b * 2 + ((d - b) * 2 + e)) := P_eq HP
      have hstep := gap_cleanup_section b a (d - b) e (flip_front b' cs) q (last_column b' cs)
        (2 + m) t ((2 + d * 2 + e) + (1 + b + column_U ((a, b') :: cs)) * 4)
        ((2 + d * 2 + e) * 2 + 3 - e + (1 + b + column_U ((a, b') :: cs))) xs
        HP' (Bounded_forget _ _ _ _ HQ) HL He (by dsimp [column_U]; omega)
            (by dsimp [column_U]; omega) HC
      refine section_step_eq hstep ?_ rfl
      have hfl := flip_front_list b' cs [1 + (2 + m) * 2, t]
      dsimp [column_list]
      simp only [List.cons_append] at hfl ⊢
      rw [hfl]
      list_nat_eq

theorem Band_eq {p1 p2 n1 n2 : Nat} (H : Band p1 n1) (hp : p1 = p2 := by omega) (hn : n1 = n2 :=
    by omega) :
    Band p2 n2 := by
  subst hp; subst hn; exact H

theorem Band_offset (p k : Nat) (HP : Chain p) : ∃ q, p ≤ q ∧ Band q (p + k) := by
  induction k with
  | zero =>
    have hg := next_p_grows p
    exact ⟨p, by omega, HP, by omega, by omega⟩
  | succ k ih =>
    rcases ih with ⟨q, Hpq, HQ, Hlo, Hhi⟩
    by_cases hlt : p + (k + 1) < next_p q
    · exact ⟨q, Hpq, HQ, by omega, hlt⟩
    · have hg1 := next_p_grows q
      have hg2 := next_p_grows (next_p q)
      exact ⟨next_p q, by omega, Chain.ChainS q HQ, by omega, by omega⟩

theorem Band_above (p n : Nat) (HP : Chain p) (Hn : p ≤ n) : ∃ q, p ≤ q ∧ Band q n := by
  rcases Band_offset p (n - p) HP with ⟨q, HQ, HB⟩
  exact ⟨q, HQ, Band_eq HB⟩

inductive CoreEntry : List Nat → Prop where
  | Entry_unary (n : Nat) : CoreEntry [n]
  | Entry_small (p n b t : Nat) :
      Band p n → 2 ≤ b → b % 2 = 0 → 1 ≤ t → t % 2 = 1 → b ≤ p → b + t ≤ n * 8 →
      CoreEntry [n, b, t]

theorem next_p_parity (p e : Nat) (He : e ≤ 1) (HP : p % 2 = e) : next_p p = p * 2 + 3 - e := by
  dsimp [next_p]; omega

theorem Stair_parity (p e : Nat) (xs : List Nat) (He : e ≤ 1) (H : Stair p e xs) : p % 2 = e := by
  cases H <;> omega

theorem core_even_exit (p e f r : Nat) (HP : Chain p) (He : e ≤ 1) (Hpar : p % 2 = e) (Hf : 1 ≤ f)
    (Hr : r ≤ p - 1 - e) :
    ∃ xs, CleanLast (p + f * 4) (next_p p + f) (r * 2) xs ∧ CoreEntry xs := by
  rcases Chain_spec p HP with ⟨Hp, _⟩
  have Hnext := next_p_parity p e He Hpar
  rcases r with _ | r
  · exact ⟨_, CleanLast.Clean0, CoreEntry.Entry_unary _⟩
  · refine ⟨[next_p p + f, 2 + r * 2, 3 + (p + f * 4 - r) * 2], ?_, ?_⟩
    · exact CleanLast_eq (@CleanLast.CleanEven (p + f * 4) (next_p p + f) r (by omega))
    · rcases Band_above (next_p p) (next_p p + f) (Chain.ChainS p HP) (by omega) with ⟨q, Hq, HB⟩
      exact CoreEntry.Entry_small q (next_p p + f) (2 + r * 2) (3 + (p + f * 4 - r) * 2) HB
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

theorem Stair_progress (p e : Nat) (xs : List Nat) (HChain : Chain p) (He : e ≤ 1)
    (HStair : Stair p e xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys)) ∧ (Stair p e ys ∨ CoreEntry ys) := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  have Hpar := Stair_parity p e xs He HStair
  have Hnext := next_p_parity p e He Hpar
  rcases HStair with ⟨d, b, cs, m, s, rfl, HR, HS⟩ | ⟨g, b, d, cs, m, s, rfl, HR, HS⟩
  · by_cases Hs : s ≤ m
    · refine ⟨(4 + d * 2 + b * 2 + e) :: column_list cs ++ [2 + s * 2, 5 + (m - s) * 2], ?_,
          Or.inl ?_⟩
      · exact good_normal_section d b e cs m s HP (Bounded_forget _ _ _ _ HR) Hs He
      · exact stair_good_normal d b e cs m s He HR HS Hs
    · rcases core_even_exit (2 + d * 2 + e) e (1 + b + column_U cs) (s - m - 1) HChain He Hpar
          (by omega) (by omega) with ⟨ys, HC, HY⟩
      refine ⟨ys, ?_, Or.inr HY⟩
      refine progress_trans (good_overflow_section d b e cs m (s - m - 1)
          HP (Bounded_forget _ _ _ _ HR) He |> fun h => section_step_eq h) ?_
      rw [Hnext] at HC
      exact clean_after_good d b e cs m ((s - m - 1) * 2) ys HP He HR HC
  · by_cases Hs : s ≤ m
    · refine ⟨(2 + g * 2 + (d * 2 + e)) :: (2 + g * 2) :: (2 + b * 2) :: column_list cs ++
          [2 + s * 2, 5 + (m - s) * 2], ?_, Or.inl ?_⟩
      · exact gap_normal_section g b d e cs m s HP (Bounded_forget _ _ _ _ HR) Hs He
      · exact stair_gap_normal g b d e cs m s He HR HS Hs
    · rcases core_even_exit (2 + g * 2 + (d * 2 + e)) e (1 + b + column_U cs) (s - m - 1)
          HChain He Hpar (by omega) (by omega) with ⟨ys, HC, HY⟩
      refine ⟨ys, ?_, Or.inr HY⟩
      refine progress_trans (gap_overflow_section g b d e cs m (s - m - 1)
          HP (Bounded_forget _ _ _ _ HR) He |> fun h => section_step_eq h) ?_
      rw [Hnext] at HC
      exact clean_after_gap g b d e cs m ((s - m - 1) * 2) ys HP He HR HC

theorem good_relation (p b t : Nat) (xs : List Nat) (HP : P p) (H : 0 < p + b) (HL : Last t (p + b)
    xs) :
    (section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 xs) := by
  rw [Last_output t (p + b) xs HL]
  exact good_section_formula p b t HP H

theorem odd_gap_odd_progress (g j t d : Nat) (HP : P (1 + g * 2 + d)) :
    (section_481 [(1 + g * 2 + d) + (1 + g * 2), 1 + j * 2, t]) [target_tm]⊢⁺
    (section_481 [1 + g * 2 + d, 2 + (j + g) * 2, 2 + t + d + d % 2]) :=
  evstep_progress_trans (odd_gap_seed g j t d HP) (evstep_progress (seed_section t (j + g) g d)
      (by ne_cfg))

theorem odd_gap_even_progress (g j v d : Nat) (HP : P (1 + g * 2 + d)) :
    (section_481 [(1 + g * 2 + d) + (1 + g * 2), j * 2, 1 + v * 2]) [target_tm]⊢⁺
    (section_481 (S_odd_output (j + g) (g * 2) v d)) := by
  refine evstep_progress_trans (odd_gap_S g j (1 + v * 2) d HP) ?_
  exact step_end_plus_eq (S_odd_progress (j + g) (g * 2) v d) (by cfg_eq) rfl

theorem odd_last_odd_progress (g j t : Nat) (HP : P (2 + g * 2)) :
    (section_481 [(2 + g * 2) + (3 + g * 2), 1 + j * 2, t]) [target_tm]⊢⁺
    (section_481 [2 + g * 2, 4 + (j + g) * 2, 2 + t]) := by
  refine evstep_progress_trans ?_ (evstep_progress (step_end (bare_root t (1 + j + g) (1 + g * 2))
      (by cfg_eq) (by cfg_eq)) (by ne_cfg))
  refine step_bridge (return_last ((([1, 1, 0] : zF) ^ (1 + j * 2)) +> ((([1, 0] : zF) ^ t)
      +> default)) g HP) (by cfg_eq) ?_
  refine step_bridge (odd_block ((([1, 0] : zF) ^ t) +> default) ((([0, 1, 1, 0, 1, 0] : zF)
      ^ (2 + g)) +> ((([1, 0] : zF) ^ (1 + g * 2)) +> default)) j) (by cfg_eq) ?_
  exact step_end (sr_2 t default (([1, 0, 1, 0] : zF) +> ((([0, 1, 1, 0, 1, 0] : zF) ^ (2 + j + g))
      +> ((([1, 0] : zF) ^ (1 + g * 2)) +> default)))) (by cfg_eq) (by cfg_eq)

def odd_output (p e k b t : Nat) : List Nat :=
  if t < p + 2 + e - k then [p, b + k + t, p + 2 + e - k - t]
  else [p, p + b + 2 + e, t - (p + 2 + e - k)]

theorem odd_odd_section (p e k b t : Nat)
    (HP : P p) (Hp : 3 ≤ p) (He : e ≤ 1) (Hpar : p % 2 + e = 1)
    (Hk : k % 2 = 1) (Hkp : k ≤ p + e) (Hb : b % 2 = 1) :
    (section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 [p, b + k, t + p + 2 + e - k]) := by
  rcases parity k with ⟨g, rfl | rfl⟩ <;> try omega
  rcases parity b with ⟨j, rfl | rfl⟩ <;> try omega
  by_cases Hle : 1 + g * 2 ≤ p
  · have HD : (p - (1 + g * 2)) % 2 = e := by omega
    exact section_step_eq (odd_gap_odd_progress g j t (p - (1 + g * 2)) (P_eq HP))
  · rcases g with _ | g
    · omega
    · exact section_step_eq (odd_last_odd_progress g j t (P_eq HP))

theorem odd_even_section (p e k b t : Nat)
    (HP : P p) (Hp : 3 ≤ p) (He : e ≤ 1) (Hpar : p % 2 + e = 1)
    (Hk : k % 2 = 1) (Hkp : k ≤ p + e) (Hb : b % 2 = 0) (Ht : t % 2 = 1) :
    (section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 (odd_output p e k b t)) := by
  rcases parity k with ⟨g, rfl | rfl⟩ <;> try omega
  rcases parity b with ⟨j, rfl | rfl⟩ <;> try omega
  rcases parity t with ⟨v, rfl | rfl⟩ <;> try omega
  by_cases Hle : 1 + g * 2 ≤ p
  · have HD : (p - (1 + g * 2)) % 2 = e := by omega
    refine section_step_eq (odd_gap_even_progress g j v (p - (1 + g * 2)) (P_eq HP))
        (by list_nat_eq) ?_
    dsimp [odd_output, S_odd_output]
    by_cases hlt : 1 + v * 2 < p - (1 + g * 2) + 2 + (p - (1 + g * 2)) % 2
    · rw [ite_eq_left hlt, ite_eq_left (by omega)]; list_nat_eq
    · rw [ite_eq_right hlt, ite_eq_right (by omega)]; list_nat_eq
  · rcases g with _ | g
    · omega
    · refine section_step_eq (odd_last_even_formula g j v (P_eq HP)) (by list_nat_eq) ?_
      dsimp [odd_output, S_odd_output]
      by_cases hlt : 1 + v * 2 < 0 + 2 + 0 % 2
      · rw [ite_eq_left hlt, ite_eq_left (by omega)]; list_nat_eq
      · rw [ite_eq_right hlt, ite_eq_right (by omega)]; list_nat_eq

theorem predecessor_P (p : Nat) (H : Chain p) : PP (next_p p - 1) := by
  rcases Chain_spec p H with ⟨Hp, HP, _⟩
  rcases parity p with ⟨a, rfl | rfl⟩ <;> dsimp [next_p]
  · rcases a with _ | a
    · omega
    · exact PP_eq (pred_even a (P_eq HP))
  · exact PP_eq (pred_odd a HP)

theorem predecessor_section (p b t : Nat) (HP : Chain p) (Hb : 2 ≤ b) (Hbp : b % 2 = 0)
    (Htp : t % 2 = 1) :
    (section_481 [next_p p - 1, b, t]) [target_tm]⊢⁺ (section_481 (pred_output (next_p p - 1)
        b t)) := by
  rcases parity b with ⟨a, rfl | rfl⟩ <;> try omega
  rcases parity t with ⟨v, rfl | rfl⟩ <;> try omega
  rcases a with _ | a
  · omega
  · have heq : (a + 1) * 2 = 2 + a * 2 := by omega
    rw [heq]
    exact pred_section (next_p p - 1) a v (predecessor_P p HP)

theorem even_odd_section (p e k b t : Nat) (xs : List Nat)
    (HP : P p) (He : e ≤ 1) (Hpar : p % 2 = e) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
        (Hb : b % 2 = 1)
    (HC : CleanLast ((p + k * 3 + b + e - 2) / 2) (p + b - k / 2) t xs) :
    (section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases parity k with ⟨g, rfl | rfl⟩ <;> try omega
  rcases parity b with ⟨j, rfl | rfl⟩ <;> try omega
  rcases g with _ | g
  · omega
  · have Hd : p = 2 + g * 2 + (((p - 2 - g * 2 - e) / 2) * 2 + e) := by omega
    exact section_step_eq (cleanup_odd_triple_section g j ((p - 2 - g * 2 - e) / 2) e t xs (P_eq HP)
        He (CleanLast_eq HC))

theorem even_normal_stair (g b d e s : Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1) (Hb : b ≤ 1 + g * 2 + d) (Hs : s ≤ b + d) :
    ∃ ys, ((section_481 [(2 + g * 2 + (d * 2 + e)) + (2 + g * 2), 2 + b * 2, 3 + s * 2])
        [target_tm]⊢⁺ (section_481 ys)) ∧
      Stair (2 + g * 2 + (d * 2 + e)) e ys := by
  refine ⟨[2 + g * 2 + (d * 2 + e), 2 + g * 2, 2 + b * 2, 2 + s * 2, 5 + (b + d - s) * 2], ?_, ?_⟩
  · exact section_step_eq (gap_normal_section g b d e [] (b + d) s HP (ColumnRun.Columns_nil _)
        Hs He)
  · refine Stair_eq (@Stair.Stair_good (2 + g * 2 + (d * 2 + e)) e (g + d) g [(b, s)]
      (1 + g * 2 + d - b + s) (1 + b + d - s) (by omega) ?_ (by omega))
    exact BoundedRun.Bounded_cons _ b s [] _ (by omega) (by omega)
        (Bounded_eq (@BoundedRun.Bounded_nil (2 + g * 2 + (d * 2 + e) - 1 - e)
            (1 + g * 2 + d - b + s) (by omega)))

theorem even_overflow_clean (g b d e r : Nat) (xs : List Nat)
    (HP : P (2 + g * 2 + (d * 2 + e))) (He : e ≤ 1) (Hb : b ≤ 1 + g * 2 + d)
    (HC : CleanLast ((2 + g * 2 + (d * 2 + e)) + (1 + b) * 4)
            ((2 + g * 2 + (d * 2 + e)) * 2 + 3 - e + (1 + b)) (r * 2) xs) :
    (section_481 [(2 + g * 2 + (d * 2 + e)) + (2 + g * 2), 2 + b * 2, 5 + (b + d) * 2 + r * 2])
        [target_tm]⊢⁺
    (section_481 xs) := by
  refine progress_trans (section_step_eq (gap_overflow_section g b d e [] (b + d)
      r HP (ColumnRun.Columns_nil _) He)) ?_
  have HR : BoundedRun (2 + g * 2 + (d * 2 + e) - 1 - e) (b + d) [] (b + d) :=
    BoundedRun.Bounded_nil _ (by omega)
  exact section_step_eq (clean_after_gap g b d e [] (b + d) (r * 2) xs HP He HR (CleanLast_eq HC
      (by dsimp [column_U]) (by dsimp [column_U]) rfl rfl))

theorem even_parameters (p e k b : Nat)
    (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0) (Hb : 2 ≤ b)
        (Hbe : b % 2 = 0) :
    ∃ g j d, k = 2 + g * 2 ∧ b = 2 + j * 2 ∧ p = 2 + g * 2 + (d * 2 + (1 - e)) :=
  ⟨(k - 2) / 2, (b - 2) / 2, (p - k - (1 - e)) / 2, by omega, by omega, by omega⟩

theorem even_normal_section (p e k b t : Nat)
    (HP : P p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Ht : 3 ≤ t) (Hte : t % 2 = 1)
    (Hbn : b ≤ p + k) (Hcap : t + k ≤ p + b + e) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Stair p (1 - e) ys := by
  rcases even_parameters p e k b He Hpar Hk Hkp Hke Hb Hbe with ⟨g, j, d, rfl, rfl, rfl⟩
  have Et : t = 3 + ((t - 3) / 2) * 2 := by omega
  rw [Et]
  exact even_normal_stair g j d (1 - e) ((t - 3) / 2) HP (by omega) (by omega) (by omega)

theorem even_overflow_section (p e k b t : Nat) (xs : List Nat)
    (HP : P p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hbn : b ≤ p + k) (Hcap : p + b + e < t + k)
    (HC : CleanLast (p + b * 2) (next_p p + b / 2) (t + k - (p + b + 2 + e)) xs) :
    (section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases even_parameters p e k b He Hpar Hk Hkp Hke Hb Hbe with ⟨g, j, d, rfl, rfl, rfl⟩
  have Hr : t = 5 + (j + d) * 2 + ((t - (5 + (j + d) * 2)) / 2) * 2 := by omega
  refine section_step_eq (even_overflow_clean g j d (1 - e) ((t - (5 + (j + d) * 2)) / 2) xs HP
      (by omega) (by omega) ?_)
  exact CleanLast_eq HC (by omega) (by dsimp [next_p]; omega) (by omega) rfl

theorem even_short_section (p e k b : Nat)
    (HP : P p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
        (Hb : b % 2 = 0) :
    (section_481 [p + k, b, 1]) [target_tm]⊢⁺ (section_481 [p, k, p + b * 2 + 4 + e - k]) := by
  rcases parity k with ⟨g, rfl | rfl⟩ <;> try omega
  rcases parity b with ⟨j, rfl | rfl⟩ <;> try omega
  rcases g with _ | g
  · omega
  · exact section_step_eq (short_section g j (p - (2 + g * 2)) (P_eq HP))

def Diagonal (n b t : Nat) : Prop :=
  2 ≤ b ∧ b % 2 = 0 ∧ 1 ≤ t ∧ t % 2 = 1 ∧
  (b + t = n + 2 + (1 - n % 2) ∨ (5 ≤ t ∧ b + t = n + 4 + (1 - n % 2)))

inductive Core : List Nat → Prop where
  | Core_entry (xs : List Nat) : CoreEntry xs → Core xs
  | Core_diagonal (n b t : Nat) : 3 ≤ n → Diagonal n b t → Core [n, b, t]

theorem Last_core (t m : Nat) (xs : List Nat) (Hm : 3 ≤ m) (Ht : t ≤ m + 1 + (1 - m % 2))
    (HL : Last t m xs) :
    Core xs := by
  rw [Last_output t m xs HL]
  dsimp only [last_output]
  split_ifs with h1 h2
  · exact Core.Core_entry _ (CoreEntry.Entry_unary _)
  · refine Core.Core_diagonal m (t - t % 2) (m + 2 + t % 2 * 3 + (1 - m % 2) - t) Hm
      ⟨by omega, by omega, by omega, by omega, ?_⟩
    by_cases hr : t % 2 = 0
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by omega, by omega⟩
  · omega

theorem unary_core_progress (n : Nat) :
    ∃ ys, ((section_481 [n]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  by_cases Hn : n < 3
  · rcases n with _ | _ | _ | n
    · exact ⟨[3], unary_zero, Core.Core_entry _ (CoreEntry.Entry_unary _)⟩
    · exact ⟨[5], unary_one, Core.Core_entry _ (CoreEntry.Entry_unary _)⟩
    · exact ⟨[9], unary_two, Core.Core_entry _ (CoreEntry.Entry_unary _)⟩
    · omega
  · rcases Band_total n (by omega) with ⟨p, HP, Hlo, Hhi⟩
    rcases Chain_spec p HP with ⟨Hp, HP', _⟩
    rcases Last_total (n - p) p (by omega) with ⟨ys, HL⟩
    refine ⟨ys, ?_, Last_core (n - p) p ys (by omega) (by dsimp [next_p] at Hhi; omega) HL⟩
    rw [Last_output (n - p) p ys HL]
    exact section_step_eq (unary_progress p (n - p) HP' (by omega))

theorem good_core_or_overflow (p b t : Nat) (HChain : Chain p) (Hb : 1 ≤ b) :
    ∃ ys, ((section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧
      (Core ys ∨ ∃ u, ys = [p + b, p + b + 2 + (1 - (p + b) % 2), u] ∧
        t = p + b + 2 + (1 - (p + b) % 2) + u) := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  rcases Last_total t (p + b) (by omega) with ⟨ys, HL⟩
  refine ⟨ys, ?_, ?_⟩
  · rw [Last_output t (p + b) ys HL]
    exact good_section_formula p b t HP (by omega)
  · by_cases Ht : t ≤ p + b + 1 + (1 - (p + b) % 2)
    · exact Or.inl (Last_core t (p + b) ys (by omega) Ht HL)
    · refine Or.inr ⟨t - (p + b + 2 + (1 - (p + b) % 2)), ?_, by omega⟩
      rw [Last_output t (p + b) ys HL]
      dsimp only [last_output]
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem good_bounded_core (p b t : Nat) (HChain : Chain p) (Ht : t ≤ p + b + 1 + (1 - (p + b)
    % 2)) :
    ∃ ys, ((section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  rcases Last_total t (p + b) (by omega) with ⟨ys, HL⟩
  exact ⟨ys, good_relation p b t ys HP (by omega) HL, Last_core t (p + b) ys (by omega) Ht HL⟩

theorem odd_even_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : k % 2 = 1) (Hkp : k ≤ p + e)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hcap : t + k ≤ p + b + e) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  have Hstep := odd_even_section p e k b t HP Hp He Hpar Hk Hkp Hbe Hte
  dsimp [odd_output] at Hstep
  by_cases E : t < p + 2 + e - k
  · rw [ite_eq_left E] at Hstep
    rcases good_bounded_core p (b + k + t) (p + 2 + e - k - t) HChain (by omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, progress_trans Hstep HT, HY⟩
  · rw [ite_eq_right E] at Hstep
    rcases good_bounded_core p (p + b + 2 + e) (t - (p + 2 + e - k)) HChain (by omega) with ⟨ys, HT,
        HY⟩
    exact ⟨ys, progress_trans Hstep HT, HY⟩

theorem even_short_core (p e k b : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0)
    (Hbe : b % 2 = 0) (Hb : b < k) :
    ∃ ys, ((section_481 [p + k, b, 1]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  rcases good_bounded_core p k (p + b * 2 + 4 + e - k) HChain (by omega) with ⟨ys, HT, HY⟩
  exact ⟨ys, progress_trans (even_short_section p e k b HP He Hpar Hk Hkp Hke Hbe) HT, HY⟩

theorem odd_recovery_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
        (Hke : k % 2 = 1)
    (Hbe : b % 2 = 1) (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hb : p + k * 8 + 2 + e ≤ b)
        (Hsum : b + t + 4 ≤ p * 3) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  have Hfirst := odd_odd_section p e k b t HP Hp He Hpar Hke (by omega) Hbe
  rcases good_core_or_overflow p (b + k) (t + p + 2 + e - k) HChain (by omega) with ⟨zs, Hsecond,
      HZ | ⟨u, rfl, HU⟩⟩
  · exact ⟨zs, progress_trans Hfirst Hsecond, HZ⟩
  · let P_val := next_p p
    have HC : Chain P_val := Chain.ChainS p HChain
    have EP : P_val = p * 2 + 2 + e := by dsimp [P_val, next_p]; omega
    have HPpar : P_val % 2 + (1 - e) = 1 := by omega
    rcases Chain_spec P_val HC with ⟨HPlo, HPP, _⟩
    let j := p + (b + k) - P_val
    have Hje : j % 2 = 1 := by dsimp [j]; omega
    have Hj : j ≤ P_val + (1 - e) := by dsimp [j]; omega
    have ET : (section_481 [p + (b + k), p + (b + k) + 2 + (1 - (p + (b + k)) % 2), u])
        [target_tm]⊢⁺
              (section_481 [P_val, p + (b + k) + 2 + e + j, u + P_val + 2 + (1 - e) - j]) :=
      section_step_eq (odd_odd_section P_val (1 - e) j (p + (b + k) + 2 + e) u HPP HPlo (by omega)
          HPpar Hje Hj (by omega))
        (by dsimp [j]; list_nat_eq) rfl
    rcases good_bounded_core P_val (p + (b + k) + 2 + e + j) (u + P_val + 2 + (1 - e) - j) HC
        (by dsimp [j]; omega) with ⟨ys, Hlast, HY⟩
    exact ⟨ys, progress_trans Hfirst (progress_trans Hsecond (progress_trans ET Hlast)), HY⟩

theorem even_recovery_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
        (Hke : k % 2 = 0)
    (Hbe : b % 2 = 1) (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hb : p + k * 8 + 2 + e ≤ b)
        (Hsum : b + t + 4 ≤ p * 3) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  let N := (p + k * 3 + b + (1 - e) - 2) / 2
  let X := p + b - k / 2
  let P_val := next_p p
  have HN : N * 2 + 5 = p + k * 3 + b + 3 - e := by dsimp [N]; omega
  have EP : P_val = p * 2 + 2 + e := by dsimp [P_val, next_p]; omega
  have EX : Band P_val X := ⟨Chain.ChainS p HChain, by dsimp [X, P_val, next_p]; omega,
      by dsimp [X, P_val, next_p]; omega⟩
  rcases CleanLast_total N X t with ⟨ys, HC⟩
  refine ⟨ys, even_odd_section p (1 - e) k b t ys HP (by omega) (by omega) (by omega) (by omega)
      Hke Hbe HC, ?_⟩
  cases HC with
  | Clean0 => exact Core.Core_entry _ (CoreEntry.Entry_unary _)
  | Clean1 => exact Core.Core_entry _ (CoreEntry.Entry_unary _)
  | CleanEven s Hs => omega
  | CleanOdd s Hs =>
    exact Core.Core_entry _ (CoreEntry.Entry_small P_val X (2 + s * 2) (5 + (N - s) * 2) EX
      (by omega) (by omega) (by omega) (by omega) (by omega) (by dsimp [X]; omega))
  | CleanBorder => omega
  | CleanOver a => omega

theorem recovery_core (p k b t : Nat)
    (HChain : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p) (Hbe : b % 2 = 1) (Ht : 1 ≤ t)
        (Hte : t % 2 = 1)
    (Hb : p + k * 8 + 2 + (1 - p % 2) ≤ b) (Hsum : b + t + 4 ≤ p * 3) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases parity k with ⟨a, rfl | rfl⟩
  · exact even_recovery_core p (1 - p % 2) (a * 2) b t HChain (by omega) (by omega) Hk Hkp
        (by omega) Hbe Ht Hte Hb Hsum
  · exact odd_recovery_core p (1 - p % 2) (1 + a * 2) b t HChain (by omega) (by omega) Hk Hkp
        (by omega) Hbe Ht Hte Hb Hsum

theorem negative_positive_small (a n e d b t u : Nat)
    (HP : P (3 + a * 2 - e)) (He : e ≤ 1) (Hn : n ≤ a) (Hd : d ≤ a + n + 3)
    (Hu : b + n * 4 + 2 = d * 2 + e + u) (Ht : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2 - e)
        n d e) [target_tm]⊢*
    (section_481 [9 + a * 4 + n - e, 14 + a * 4 + d * 4, 1 + u * 2]) := by
  rcases u with _ | u
  · rcases e with _ | _ | e
    · exact step_end (negativeN_one_odd a n d b (a + n + 3 - d) (a - n) t (P_eq HP) (by omega)
          (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
    · exact step_end (negativeN_one_even a n d b (a + n + 3 - d) (a - n) t (P_eq HP) (by omega)
          (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
    · omega
  · by_cases Hcross : u + e + n ≤ a
    · rcases e with _ | _ | e
      · exact step_end (negativeN_positive_odd a n d b (a + n + 3 - d) u (a - n - u) t (P_eq HP)
            (by omega) (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
      · exact step_end (negativeN_positive_even a n d b (a + n + 3 - d) u (a - 1 - n - u)
            t (P_eq HP) (by omega) (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
      · omega
    · rcases e with _ | _ | e
      · exact step_end (negativeN_root_odd a n d b (a + n + 3 - d) (a - n) ((t - 1) / 2)
            (u - (a - n) - 1) (P_eq HP) (by omega) (by omega) (by omega) (by omega)) (by cfg_eq)
                (by cfg_eq)
      · exact step_end (negativeN_root_even a n d b (a + n + 3 - d) (a - n) ((t - 1) / 2)
            (u - (a - n)) (P_eq HP) (by omega) (by omega) (by omega) (by omega)) (by cfg_eq)
                (by cfg_eq)
      · omega

theorem negative_negative_small (a n e d b t u : Nat)
    (HP : P (3 + a * 2 - e)) (He : e ≤ 1) (Hn : n ≤ a) (Hd : d ≤ a + n + 3)
    (Hu : d * 2 + e = b + n * 4 + 3 + u) (Ht : t + b * 2 = 13 + a * 4 + d * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2 - e)
        n d e) [target_tm]⊢*
    (section_481 [9 + a * 4 + n - e, 19 + a * 4 + n * 8 + b * 2 - e * 2, 1 + u * 2]) := by
  rcases e with _ | _ | e
  · exact step_end (negativeN_bounded_odd a n d b (a + n + 3 - d) (a - n) u t (P_eq HP) (by omega)
        (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
  · exact step_end (negativeN_bounded_even a n d b (a + n + 3 - d) (a - n) u t (P_eq HP) (by omega)
        (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
  · omega

theorem negative_positive_large (a n e k b t u : Nat)
    (HP : P (3 + a * 2 - e)) (He : e ≤ 1) (Hn : n ≤ a) (Hk : k ≤ 5 + n * 3 + a - e)
    (Hu : b + n * 4 + 2 = (a + n + 3 + k) * 2 + e + u)
        (Ht : t + b * 2 = 13 + a * 4 + (a + n + 3 + k) * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2 - e)
        n (a + n + 3 + k) e) [target_tm]⊢*
    (section_481 [9 + a * 4 + n - e, 14 + a * 4 + (a + n + 3 + k) * 4, 1 + u * 2]) := by
  rcases u with _ | u
  · exact step_end (negativeN_large_short (3 + a * 2 - e) n e (a + n + 3) k
      (3 + a * 2 - e - (2 + n * 2)) (1 + a - n - e) (5 + n * 3 + a - e) b ((t - 1) / 2)
      HP (by omega) (by omega) (by omega) He (by omega) (by omega) (by omega)) (by cfg_eq)
          (by cfg_eq)
  · exact step_end (negativeN_large_root (3 + a * 2 - e) n e (a + n + 3) k
      (3 + a * 2 - e - (2 + n * 2)) (1 + a - n - e) (5 + n * 3 + a - e) b ((t - 1) / 2) u
      HP (by omega) (by omega) (by omega) He (by omega) (by omega) (by omega)) (by cfg_eq)
          (by cfg_eq)

theorem negative_negative_large (a n e k b t u : Nat)
    (HP : P (3 + a * 2 - e)) (He : e ≤ 1) (Hn : n ≤ a) (Hk : k ≤ 5 + n * 3 + a - e)
    (Hu : (a + n + 3 + k) * 2 + e = b + n * 4 + 3 + u)
        (Ht : t + b * 2 = 13 + a * 4 + (a + n + 3 + k) * 2) :
    (negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2 - e)
        n (a + n + 3 + k) e) [target_tm]⊢*
    (section_481 [9 + a * 4 + n - e, 19 + a * 4 + n * 8 + b * 2 - e * 2, 1 + u * 2]) := by
  exact step_end (negativeN_large_late (3 + a * 2 - e) n e (a + n + 3) k
    (3 + a * 2 - e - (2 + n * 2)) (1 + a - n - e) (5 + n * 3 + a - e) b ((5 + n * 3 + a - e) - k) u
    HP (by omega) (by omega) (by omega) He (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)

theorem lone_positive (a n e b t : Nat)
    (HP : P (3 + a * 2 - e)) (He : e ≤ 1) (Hn : n ≤ a) (Ht : 3 ≤ t) (HE : t + b * 2 = 11 + a * 4) :
    (loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t) +> default)) (3 + a * 2 - e) n e)
        [target_tm]⊢*
    (section_481 [9 + a * 4 + n - e, 10 + a * 4, 9 + n * 8 + b * 2 - e * 2]) := by
  by_cases Hcross : 3 + n * 5 + b ≤ a
  · rcases e with _ | _ | e
    · exact step_end (loneN_odd a n b (a - 3 - n * 5 - b) t (P_eq HP) (by omega) (by omega))
          (by cfg_eq) (by cfg_eq)
    · exact step_end (loneN_even a n b (a - 3 - n * 5 - b) t (P_eq HP) (by omega) (by omega))
          (by cfg_eq) (by cfg_eq)
    · omega
  · rcases e with _ | _ | e
    · exact step_end (loneN_root_odd a n b (a - n) ((t - 3) / 2) (n * 5 + b + 2 - a) (P_eq HP)
          (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
    · exact step_end (loneN_root_even a n b (a - n) ((t - 3) / 2) (n * 5 + b + 2 - a) (P_eq HP)
          (by omega) (by omega) (by omega)) (by cfg_eq) (by cfg_eq)
    · omega

inductive Repair (p e A delta B : Nat) : List Nat → Prop where
  | Repair_positive (x : Nat) : 1 ≤ x → x + delta * 2 = B + A * 4 + 3 →
      Repair p e A delta B [next_p p + A / 2, p * 2 + delta * 2 + 2, x]
  | Repair_negative (x : Nat) : 1 ≤ x → B + A * 4 + 3 + x = delta * 2 →
      Repair p e A delta B [next_p p + A / 2, p * 2 + A * 4 + B + 5, x]

theorem Repair_eq {p1 p2 e1 e2 A1 A2 d1 d2 B1 B2 : Nat} {xs1 xs2 : List Nat}
    (H : Repair p1 e1 A1 d1 B1 xs1)
    (hp : p1 = p2 := by omega) (he : e1 = e2 := by omega) (hA : A1 = A2 := by omega)
    (hd : d1 = d2 := by omega) (hB : B1 = B2 := by omega) (hxs : xs1 = xs2 := by list_nat_eq) :
    Repair p2 e2 A2 d2 B2 xs2 := by
  subst hp; subst he; subst hA; subst hd; subst hB; subst hxs; exact H

theorem wide_section (p e A delta B t : Nat) (xs : List Nat)
    (HP : P p) (Hp : 3 ≤ p) (He : e ≤ 1) (Hpar : p % 2 + e = 1)
    (HA : 2 ≤ A) (HAp : A ≤ p) (HAe : A % 2 = 0) (HB : 2 ≤ B) (HBe : B % 2 = 0)
    (HD : 1 + e ≤ delta) (HDe : (delta + e) % 2 = 1) (HDhi : delta < p * 2 + A * 4 + 7 + e)
    (Hbal : t + B = p * 2 + 4 + e + delta) (Hlone : delta = 1 + e → 3 ≤ t)
        (HR : Repair p e A delta B xs) :
    (section_481 [p, A, p + A + delta, B, t]) [target_tm]⊢* (section_481 xs) := by
  have hparams : ∃ a n b, p = 3 + a * 2 - e ∧ A = 2 + n * 2 ∧ B = b * 2 ∧ n ≤ a :=
    ⟨(p + e - 3) / 2, (A - 2) / 2, B / 2, by omega, by omega, by omega, by omega⟩
  rcases hparams with ⟨a, n, b, rfl, rfl, rfl, Hn⟩
  by_cases Hdelta : delta = 1 + e
  · subst Hdelta
    refine ReachesStar.trans (c₂ := loneN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
        +> default)) (3 + a * 2 - e) n e) ?_ ?_
    · rcases e with _ | _ | e
      · exact step_end (loneN_first_odd ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
            +> default)) a n (P_eq HP)) (by cfg_eq) (by cfg_eq)
      · exact step_end (loneN_first_even ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
            +> default)) a n (P_eq HP)) (by cfg_eq) (by cfg_eq)
      · omega
    · cases HR with
      | Repair_positive x Hx Hex =>
        exact step_end (lone_positive a n e b t HP He Hn (Hlone rfl) (by omega)) rfl
            (by dsimp [next_p]; cfg_eq)
      | Repair_negative x Hx Hex => omega
  · have hd_ex : ∃ d, delta = 3 + e + d * 2 := ⟨(delta - 3 - e) / 2, by omega⟩
    rcases hd_ex with ⟨d, rfl⟩
    refine ReachesStar.trans (c₂ := negativeN ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
        +> default)) (3 + a * 2 - e) n d e) ?_ ?_
    · rcases e with _ | _ | e
      · exact step_end (negativeN_first_odd ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
            +> default)) a n d (P_eq HP)) (by cfg_eq) (by cfg_eq)
      · exact step_end (negativeN_first_even ((([1, 1, 0] : zF) ^ (b * 2)) +> ((([1, 0] : zF) ^ t)
            +> default)) a n d (P_eq HP)) (by cfg_eq) (by cfg_eq)
      · omega
    · cases HR with
      | Repair_positive x Hx Hex =>
        by_cases Hsmall : d ≤ a + n + 3
        · exact step_end (negative_positive_small a n e d b t ((x - 1) / 2) HP He Hn Hsmall
              (by omega) (by omega)) rfl (by dsimp [next_p]; cfg_eq)
        · exact step_end (negative_positive_large a n e (d - (a + n + 3)) b t ((x - 1) / 2) HP He Hn
              (by omega) (by omega) (by omega)) (by cfg_eq) (by dsimp [next_p]; cfg_eq)
      | Repair_negative x Hx Hex =>
        by_cases Hsmall : d ≤ a + n + 3
        · exact step_end (negative_negative_small a n e d b t ((x - 1) / 2) HP He Hn Hsmall
              (by omega) (by omega)) rfl (by dsimp [next_p]; cfg_eq)
        · exact step_end (negative_negative_large a n e (d - (a + n + 3)) b t ((x - 1) / 2) HP He Hn
              (by omega) (by omega) (by omega)) (by cfg_eq) (by dsimp [next_p]; cfg_eq)

theorem Repair_total (p e A delta B : Nat) (HB : B % 2 = 0) : ∃ xs, Repair p e A delta B xs := by
  by_cases hle : delta * 2 ≤ B + A * 4 + 3
  · exact ⟨_, Repair.Repair_positive (B + A * 4 + 3 - delta * 2) (by omega) (by omega)⟩
  · exact ⟨_, Repair.Repair_negative (delta * 2 - (B + A * 4 + 3)) (by omega) (by omega)⟩

theorem wide_triple (p e k b t : Nat) (xs : List Nat)
    (HP : P p) (Hp : 3 ≤ p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Ht : 3 ≤ t) (Hte : t % 2 = 1) (Hbn : p + k < b)
        (Hcap : t + k ≤ p + b + e)
    (Hdelta : b - (p + k) < p * 2 + k * 4 + 7 + e)
    (HR : Repair p e k (b - (p + k)) (t - 1) xs) :
    (section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases even_parameters p e k b He Hpar Hk Hkp Hke Hb Hbe with ⟨g, j, d, Ek, Eb, Ep⟩
  refine progress_evstep_trans (c₂ := section_481 [p, k, b, t - 1, p + b + 5 + e - k - t]) ?_ ?_
  · exact section_step_eq (gap_normal_section g j d (1 - e) [] (j + d) ((t - 3) / 2) (P_eq HP)
        (ColumnRun.Columns_nil _) (by omega) (by omega))
  · exact section_evstep_eq (wide_section p e k (b - (p + k)) (t - 1) (p + b + 5 + e - k - t) xs
      HP Hp He Hpar Hk Hkp Hke (by omega) (by omega) (by omega) (by omega) Hdelta (by omega)
          (by omega) HR)

theorem short_overflow_output (p e k b : Nat)
    (_Hp : 3 ≤ p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (_Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
        (Hb : k ≤ b) :
    last_output (p + b * 2 + 4 + e - k) (p + k) = [p + k, p + k + 2 + e, (b - k) * 2 + 2] := by
  dsimp [last_output]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  list_nat_eq

theorem even_short_clean (p e k b : Nat) (xs : List Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0)
    (Hb : b % 2 = 0) (Hbk : k ≤ b)
    (HC : CleanLast (p + k * 2) (next_p p + k / 2) ((b - k) * 2 + 2) xs) :
    (section_481 [p + k, b, 1]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  refine progress_trans (even_short_section p e k b HP He Hpar Hk Hkp Hke Hb) ?_
  refine progress_trans (c₂ := section_481 [p + k, p + k + 2 + e, (b - k) * 2 + 2]) ?_ ?_
  · rw [← short_overflow_output p e k b Hp He Hpar Hk Hkp Hke Hbk]
    exact good_section_formula p k (p + b * 2 + 4 + e - k) HP (by omega)
  · exact even_odd_section p (1 - e) k (p + k + 2 + e) ((b - k) * 2 + 2) xs HP
      (by omega) (by omega) Hk Hkp Hke (by omega) (CleanLast_eq HC (by omega)
          (by dsimp [next_p]; omega) rfl rfl)

theorem short_repair (p e k b : Nat) (xs : List Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0)
    (Hb : b % 2 = 0) (Hbn : p + k < b) (HR : Repair p e k (b - (p + k)) 0 xs) :
    (section_481 [p + k, b, 1]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  refine even_short_clean p e k b xs HChain He Hpar Hk Hkp Hke Hb (by omega) ?_
  cases HR with
  | Repair_positive x Hx HE =>
    by_cases Hx1 : x = 1
    · subst Hx1
      exact CleanLast_eq (@CleanLast.CleanBorder (p + k * 2) (p * 2 + 2 + (1 - p % 2) + k / 2))
        rfl (by dsimp [next_p]) (by omega) (by dsimp [next_p] ; list_nat_eq)
    · exact CleanLast_eq (@CleanLast.CleanEven (p + k * 2) (p * 2 + 2 + (1 - p % 2) + k / 2) (b - k)
          (by omega))
        rfl (by dsimp [next_p]) (by omega) (by dsimp [next_p] ; list_nat_eq)
  | Repair_negative x Hx HE =>
    exact CleanLast_eq (@CleanLast.CleanOver (p + k * 2) (p * 2 + 2 + (1 - p % 2) + k / 2) x)
      rfl (by dsimp [next_p]) (by omega) (by dsimp [next_p] ; list_nat_eq)

theorem halving_step (p e k d t : Nat) (xs : List Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k * 4 ≤ p)
        (Hke : k % 2 = 0)
    (Hd : 1 ≤ d) (Hdp : d ≤ p * 2) (Hde : (p + d) % 2 = 0) (Ht : 1 ≤ t) (Hte : t % 2 = 1)
        (Hcap : t ≤ p * 2 + d + e)
    (HR : Repair p e k d (t - 1) xs) :
    (section_481 [p + k, p + k + d, t]) [target_tm]⊢⁺ (section_481 xs) := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  by_cases Ht1 : t = 1
  · subst Ht1
    exact short_repair p e k (p + k + d) xs HChain He Hpar Hk (by omega) Hke (by omega) (by omega)
        (Repair_eq HR)
  · exact wide_triple p e k (p + k + d) t xs HP Hp He Hpar Hk (by omega) Hke (by omega) (by omega)
      (by omega) Hte (by omega) (by omega) (by omega) (Repair_eq HR)

inductive Safe : List Nat → Prop where
  | Safe_core (xs : List Nat) : Core xs → Safe xs
  | Safe_stair (p e : Nat) (xs : List Nat) : Chain p → e ≤ 1 → Stair p e xs → Safe xs
  | Safe_half (p k d t : Nat) :
      Chain p → 2 ≤ k → k * 4 ≤ p → k % 2 = 0 →
      1 ≤ d → d ≤ p * 2 → (p + d) % 2 = 0 → 1 ≤ t → t % 2 = 1 →
      t ≤ p * 2 + d + (1 - p % 2) → Safe [p + k, p + k + d, t]

theorem Safe_eq {xs1 xs2 : List Nat} (H : Safe xs1) (hxs : xs1 = xs2 :=
    by list_nat_eq) : Safe xs2 := by
  subst hxs; exact H

theorem near_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
    (Hb : p < b) (Hbn : b ≤ p + k) (Hbe : b % 2 = 0) (Ht : 1 ≤ t) (Hte : t % 2 = 1)
        (Hcap : t + k ≤ p + b + e) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  by_cases Hko : k % 2 = 1
  · rcases odd_even_core p e k b t HChain He Hpar Hko (by omega) (by omega) Hbe Hte Hcap with ⟨ys,
        HT, HY⟩
    exact ⟨ys, HT, Safe.Safe_core ys HY⟩
  · have Hk0 : k % 2 = 0 := by omega
    by_cases Ht1 : t = 1
    · subst Ht1
      refine ⟨[next_p p + k / 2, (b - k) * 2 + 2, 3 + (p + k * 2 - (b - k)) * 2], ?_, ?_⟩
      · refine even_short_clean p e k b _ HChain He Hpar (by omega) (by omega) Hk0 Hbe (by omega) ?_
        exact CleanLast_eq (@CleanLast.CleanEven (p + k * 2) (next_p p + k / 2) (b - k) (by omega))
      · refine Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_small (next_p p)
            (next_p p + k / 2)
          ((b - k) * 2 + 2) (3 + (p + k * 2 - (b - k)) * 2) ?_
          (by omega) (by omega) (by omega) (by omega)
          (by dsimp [next_p]; omega) (by dsimp [next_p]; omega)))
        exact ⟨Chain.ChainS p HChain, by dsimp [next_p]; omega, by dsimp [next_p]; omega⟩
    · rcases even_normal_section p e k b t HP He Hpar (by omega) (by omega) Hk0 (by omega) Hbe
          (by omega) Hte Hbn Hcap with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Safe.Safe_stair p (1 - e) ys HChain (by omega) HY⟩

theorem halving_progress (p k d t : Nat)
    (HChain : Chain p) (Hk : 2 ≤ k) (Hkp : k * 4 ≤ p) (Hke : k % 2 = 0) (Hd : 1 ≤ d)
        (Hdp : d ≤ p * 2)
    (Hde : (p + d) % 2 = 0) (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hcap : t ≤ p * 2 + d + (1 - p % 2)) :
    ∃ ys, ((section_481 [p + k, p + k + d, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpar : p % 2 + e = 1 := by dsimp [e]; omega
  rcases Repair_total p e k d (t - 1) (by omega) with ⟨xs, HR⟩
  have HT := halving_step p e k d t xs HChain He Hpar Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap HR
  let P_val := next_p p
  let K := k / 2
  have EP : P_val = p * 2 + 2 + e := by dsimp [P_val, next_p, e]
  have HPpar : P_val % 2 + (1 - e) = 1 := by omega
  have HC : Chain P_val := Chain.ChainS p HChain
  have HK : 1 ≤ K := by dsimp [K]; omega
  have HKP : K * 4 ≤ P_val := by dsimp [K]; omega
  have EK : k = K * 2 := by dsimp [K]; omega
  cases HR with
  | Repair_positive x Hx Hex =>
    let B := p * 2 + d * 2 + 2
    have HBe : B % 2 = 0 := by dsimp [B]; omega
    have HX : x % 2 = 1 := by dsimp [B] at *; omega
    have Hcap' : x + K ≤ P_val + B + (1 - e) := by dsimp [B] at *; omega
    by_cases Hko : K % 2 = 1
    · rcases odd_even_core P_val (1 - e) K B x HC (by omega) HPpar Hko (by omega)
          (by dsimp [B]; omega) HBe HX Hcap' with ⟨ys, HY, HZ⟩
      exact ⟨ys, progress_trans HT HY, Safe.Safe_core ys HZ⟩
    · have HK0 : K % 2 = 0 := by omega
      by_cases Hnear : B ≤ P_val + K
      · rcases near_core P_val (1 - e) K B x HC (by omega) HPpar HK HKP (by dsimp [B]; omega)
            Hnear HBe Hx HX Hcap' with ⟨ys, HY, HZ⟩
        exact ⟨ys, progress_trans HT HY, HZ⟩
      · refine ⟨[P_val + K, B, x], HT, ?_⟩
        exact Safe_eq (Safe.Safe_half P_val K (B - (P_val + K)) x HC (by omega) HKP HK0
          (by omega) (by dsimp [B, P_val, next_p, e] at *; omega)
          (by dsimp [B, P_val, next_p, e] at *; omega) Hx HX
          (by dsimp [B, P_val, next_p, e] at *; omega))
  | Repair_negative x Hx Hex =>
    have HX : x % 2 = 1 := by omega
    rcases recovery_core P_val K (p * 2 + k * 4 + (t - 1) + 5) x HC HK HKP
      (by omega) Hx HX (by dsimp [P_val, next_p]; omega) (by omega) with ⟨ys, HY, HZ⟩
    exact ⟨ys, progress_trans HT HY, Safe.Safe_core ys HZ⟩

theorem clean_small_core (p X N t : Nat)
    (HP : Chain p) (HX : p ≤ X) (Hte : t % 2 = 0) (Htp : t ≤ p) (Ht : t < N * 2 + 5)
        (HN : N * 2 + 5 ≤ X * 8) :
    ∃ xs, CleanLast N X t xs ∧ Core xs := by
  rcases Band_above p X HP HX with ⟨q, Hq, HQ⟩
  rcases CleanLast_total N X t with ⟨xs, HC⟩
  refine ⟨xs, HC, ?_⟩
  cases HC with
  | Clean0 => exact Core.Core_entry _ (CoreEntry.Entry_unary _)
  | Clean1 => omega
  | CleanEven s Hs =>
    exact Core.Core_entry _ (CoreEntry.Entry_small q X (2 + s * 2) (3 + (N - s) * 2) HQ
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  | CleanOdd s Hs => omega
  | CleanBorder =>
    exact Core.Core_entry _ (CoreEntry.Entry_small q X (4 + N * 2) 1 HQ
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  | CleanOver a => omega

theorem even_overflow_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hbn : b ≤ p + k) (Hcap : p + b + e < t + k)
    (Hmax : t + k ≤ p + b + 2 + e + next_p p) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  rcases clean_small_core (next_p p) (next_p p + b / 2) (p + b * 2) (t + k - (p + b + 2 + e))
    (Chain.ChainS p HChain) (by omega) (by omega) (by dsimp [next_p] at *; omega)
    (by dsimp [next_p] at *; omega) (by dsimp [next_p] at *; omega) with ⟨ys, HC, HY⟩
  exact ⟨ys, even_overflow_section p e k b t ys HP He Hpar Hk Hkp Hke Hb Hbe Hte Hbn Hcap HC, HY⟩

theorem odd_even_bounded_core (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : k % 2 = 1) (Hkp : k ≤ p + e)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hcap : t + k ≤ p * 3 + b + 6 + e) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  have Hstep := odd_even_section p e k b t HP Hp He Hpar Hk Hkp Hbe Hte
  dsimp [odd_output] at Hstep
  by_cases E : t < p + 2 + e - k
  · rw [ite_eq_left E] at Hstep
    rcases good_bounded_core p (b + k + t) (p + 2 + e - k - t) HChain (by omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, progress_trans Hstep HT, HY⟩
  · rw [ite_eq_right E] at Hstep
    rcases good_bounded_core p (p + b + 2 + e) (t - (p + 2 + e - k)) HChain (by omega) with ⟨ys, HT,
        HY⟩
    exact ⟨ys, progress_trans Hstep HT, HY⟩

theorem bounded_small_advance (p e k b t : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
        (Hb : p < b) (Hbhi : b ≤ p + 3)
    (Hbe : b % 2 = 0) (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hthi : t ≤ k * 8 + 1) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  by_cases Hko : k % 2 = 1
  · rcases odd_even_bounded_core p e k b t HChain He Hpar Hko (by omega) (by omega) Hbe Hte
        (by omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, HT, Safe.Safe_core ys HY⟩
  · have Hk0 : k % 2 = 0 := by omega
    by_cases Hnear : b ≤ p + k
    · by_cases Hcap : t + k ≤ p + b + e
      · exact near_core p e k b t HChain He Hpar Hk Hkp Hb Hnear Hbe Ht Hte Hcap
      · rcases even_overflow_core p e k b t HChain He Hpar (by omega) (by omega) Hk0 (by omega)
            Hbe Hte Hnear (by omega) (by dsimp [next_p]; omega) with ⟨ys, HT, HY⟩
        exact ⟨ys, HT, Safe.Safe_core ys HY⟩
    · rcases halving_progress p k (b - (p + k)) t HChain (by omega) Hkp Hk0 (by omega) (by omega)
          (by omega) Ht Hte (by omega) with ⟨ys, HT, HY⟩
      exact ⟨ys, section_step_eq HT, HY⟩

theorem short_diagonal_safe (p e k : Nat)
    (HChain : Chain p) (He : e ≤ 1) (Hpar : p % 2 + e = 1) (Hk : 2 ≤ k) (Hkp : k ≤ p)
        (Hke : k % 2 = 0) :
    ∃ ys, ((section_481 [p + k, p + k + 1 + e, 1]) [target_tm]⊢⁺ (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  let P_val := next_p p
  let K := k / 2
  have EP : P_val = p * 2 + 2 + e := by dsimp [P_val, next_p]; omega
  have HC : Chain P_val := Chain.ChainS p HChain
  have ET : (section_481 [p + k, p + k + 1 + e, 1])
      [target_tm]⊢⁺ (section_481 [P_val + K, P_val + 2 + e, k * 4 + 1 - e * 2]) := by
    refine even_short_clean p e k (p + k + 1 + e) _ HChain He Hpar Hk Hkp Hke (by omega) (by omega)
        ?_
    exact CleanLast_eq (@CleanLast.CleanEven (p + k * 2) (next_p p + k / 2) (p + 1 + e) (by omega))
      rfl rfl (by omega) (by dsimp [P_val, K]; list_nat_eq)
  rcases bounded_small_advance P_val (1 - e) K (P_val + 2 + e) (k * 4 + 1 - e * 2) HC
    (by omega) (by omega) (by dsimp [K]; omega) (by dsimp [K]; omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by dsimp [K]; omega) with ⟨ys, HT, HY⟩
  exact ⟨ys, progress_trans ET HT, HY⟩

theorem predecessor_core (p b t : Nat)
    (HChain : Chain p) (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Ht : 1 ≤ t) (Hte : t % 2 = 1)
    (Hhi : t < next_p p + 3 + (1 - next_p p % 2)) :
    ∃ ys, ((section_481 [next_p p - 1, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  have HP := next_p_grows p
  have HT := predecessor_section p b t HChain Hb Hbe Hte
  dsimp [pred_output] at HT
  rw [ite_eq_left (by omega)] at HT
  rcases good_bounded_core (next_p p) (b + t - 1) (next_p p + 3 + (1 - next_p p % 2) - t)
    (Chain.ChainS p HChain) (by omega) with ⟨ys, HY, HZ⟩
  exact ⟨ys, progress_trans (section_step_eq HT) HY, HZ⟩

theorem diagonal_progress (n b t : Nat) (Hn : 3 ≤ n) (HD : Diagonal n b t) :
    ∃ ys, ((section_481 [n, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Safe ys := by
  rcases HD with ⟨Hb, Hbe, Ht, Hte, Hsum⟩
  rcases Band_total n Hn with ⟨p, HChain, Hlo, Hhi⟩
  rcases Chain_spec p HChain with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  let k := n - p
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpar : p % 2 + e = 1 := by dsimp [e]; omega
  have En : n = p + k := by dsimp [k]; omega
  by_cases Hk0 : k = 0
  · have Enp : n = p := by omega
    rw [Enp]
    rcases good_bounded_core p b t HChain (by omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, HT, Safe.Safe_core ys HY⟩
  · by_cases Enp : n = next_p p - 1
    · subst Enp
      rcases predecessor_core p b t HChain Hb Hbe Ht Hte (by dsimp [next_p] at *; omega) with ⟨ys,
          HT, HY⟩
      exact ⟨ys, HT, Safe.Safe_core ys HY⟩
    · rw [En]
      dsimp [next_p] at Hhi
      by_cases Hko : k % 2 = 1
      · rcases odd_even_bounded_core p e k b t HChain He Hpar Hko (by dsimp [next_p] at Enp; omega)
            Hb Hbe Hte (by omega) with ⟨ys, HT, HY⟩
        exact ⟨ys, HT, Safe.Safe_core ys HY⟩
      · have Hk : 2 ≤ k := by dsimp [next_p] at Enp; omega
        have Hkp : k ≤ p := by dsimp [next_p] at Enp; omega
        have Hke0 : k % 2 = 0 := by omega
        by_cases Ht1 : t = 1
        · subst Ht1
          rcases short_diagonal_safe p e k HChain He Hpar Hk Hkp Hke0 with ⟨ys, HT, HY⟩
          exact ⟨ys, section_step_eq HT, HY⟩
        · have Hbn : b ≤ p + k := by omega
          by_cases Hcap : t + k ≤ p + b + e
          · rcases even_normal_section p e k b t HP He Hpar Hk Hkp Hke0 Hb Hbe (by omega)
                Hte Hbn Hcap with ⟨ys, HT, HY⟩
            exact ⟨ys, HT, Safe.Safe_stair p (1 - e) ys HChain (by omega) HY⟩
          · rcases even_overflow_core p e k b t HChain He Hpar Hk Hkp Hke0 Hb Hbe Hte Hbn (by omega)
                (by dsimp [next_p]; omega) with ⟨ys, HT, HY⟩
            exact ⟨ys, HT, Safe.Safe_core ys HY⟩

theorem small_cleanup_low (p k b t : Nat)
    (HC : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p) (Hb : 2 ≤ b) (Hbe : b % 2 = 0)
    (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hsum : b + t = p + k * 8 + 2 + (1 - p % 2)) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢* (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  by_cases Hsmall : b ≤ p
  · refine ⟨[p + k, b, t], ⟨0, rfl⟩, ?_⟩
    exact Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_small p (p + k) b t
      ⟨HC, by omega, by dsimp [next_p]; omega⟩ Hb Hbe Ht Hte Hsmall (by omega)))
  · by_cases Hko : k % 2 = 1
    · rcases odd_even_bounded_core p e k b t HC He Hpe Hko (by omega) Hb Hbe Hte
          (by dsimp [e] at *; omega) with ⟨ys, HT, HY⟩
      exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
    · have Hke0 : k % 2 = 0 := by omega
      have Hk2 : 2 ≤ k := by omega
      by_cases Hnear : b ≤ p + k
      · by_cases Hcap : t + k ≤ p + b + e
        · rcases near_core p e k b t HC He Hpe Hk Hkp (by omega) Hnear Hbe Ht Hte Hcap with ⟨ys, HT,
              HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, HY⟩
        · rcases even_overflow_core p e k b t HC He Hpe Hk2 (by omega) Hke0 Hb Hbe Hte Hnear
              (by omega) (by dsimp [next_p, e] at *; omega) with ⟨ys, HT, HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
      · refine ⟨[p + k, b, t], ⟨0, rfl⟩, ?_⟩
        exact Safe_eq (Safe.Safe_half p k (b - (p + k)) t HC Hk2 Hkp Hke0 (by omega)
            (by dsimp [e] at *; omega) (by dsimp [e] at *; omega) Ht Hte (by dsimp [e] at *; omega))

theorem cleanup_low_reaches (p k N t : Nat) (xs : List Nat)
    (HC : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
    (Hsum : N * 2 + 5 = p + k * 8 + 2 + (1 - p % 2)) (Hte : t % 2 = 0) (Ht : t < N * 2 + 5)
    (HL : CleanLast N (p + k) t xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢* (section_481 ys)) ∧ Safe ys := by
  cases HL with
  | Clean0 =>
    exact ⟨[p + k + 5 + N * 2], ⟨0, rfl⟩,
        Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_unary _))⟩
  | Clean1 => omega
  | CleanEven s Hs =>
    exact small_cleanup_low p k (2 + s * 2) (3 + (N - s) * 2) HC Hk Hkp (by omega) (by omega)
        (by omega) (by omega) (by omega)
  | CleanOdd s Hs => omega
  | CleanBorder =>
    exact small_cleanup_low p k (4 + N * 2) 1 HC Hk Hkp (by omega) (by omega) (by omega) (by omega)
        (by omega)
  | CleanOver a => omega

inductive HighExit : List Nat → Prop where
  | High_exit (p k t : Nat) :
      Chain p → 1 ≤ k → k * 4 ≤ p → 1 ≤ t → t % 2 = 1 →
      t + k * 12 + 2 + (1 - p % 2) ≤ p * 7 →
      HighExit [p + k, p + k * 8 + 2 + (1 - p % 2), t]

def EntryExit (xs : List Nat) : Prop := Safe xs ∨ HighExit xs

theorem cleanup_entry_exit (p k N t : Nat) (xs : List Nat)
    (HC : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
    (Hsum : N * 2 + 5 = p + k * 8 + 2 + (1 - p % 2)) (Hte : t % 2 = 0) (Hcap : t + k * 4 ≤ p * 8)
    (HL : CleanLast N (p + k) t xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢* (section_481 ys)) ∧ EntryExit ys := by
  by_cases Hlow : t < N * 2 + 5
  · rcases cleanup_low_reaches p k N t xs HC Hk Hkp Hsum Hte Hlow HL with ⟨ys, HT, HY⟩
    exact ⟨ys, HT, Or.inl HY⟩
  · cases HL with
    | CleanOver a =>
      refine ⟨[p + k, 5 + N * 2, a], ⟨0, rfl⟩, Or.inr ?_⟩
      have heq : 5 + N * 2 = p + k * 8 + 2 + (1 - p % 2) := by omega
      rw [heq]
      exact HighExit.High_exit p k a HC Hk Hkp (by omega) (by omega) (by omega)
    | _ => omega

theorem post_good_cleanup (p e b t : Nat) (xs : List Nat)
    (HP : P p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0)
    (HL : CleanLast (p + b * 2) (next_p p + b / 2) t xs) :
    (section_481 [p + b, p + b + 2 + e, t]) [target_tm]⊢⁺ (section_481 xs) :=
  even_odd_section p (1 - e) b (p + b + 2 + e) t xs HP (by omega) (by omega) Hb Hbp Hbe (by omega)
    (CleanLast_eq HL (by omega) (by dsimp [next_p]; omega) rfl rfl)

theorem good_even_cleanup (p e b t : Nat) (xs : List Nat)
    (HP : P p) (Hp : 3 ≤ p) (He : e ≤ 1) (Hpe : p % 2 + e = 1)
    (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Ht : p + b + 1 + e < t)
    (HL : CleanLast (p + b * 2) (next_p p + b / 2) (t - (p + b + 2 + e)) xs) :
    (section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 xs) := by
  have HT := good_section_formula p b t HP (by omega)
  have E : last_output t (p + b) = [p + b, p + b + 2 + e, t - (p + b + 2 + e)] := by
    dsimp [last_output]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    list_nat_eq
  rw [E] at HT
  exact progress_trans HT (post_good_cleanup p e b (t - (p + b + 2 + e)) xs HP He Hpe Hb Hbp Hbe HL)

theorem mixed_good_entry (p b t : Nat)
    (HC : Chain p) (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1)
        (Hsum : b + t ≤ p * 18) :
    ∃ ys, ((section_481 [p, p + b + 2 + (1 - p % 2), t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ EntryExit ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  let q := next_p p
  have HQ : Chain q := Chain.ChainS p HC
  rcases Chain_spec q HQ with ⟨Hq, HPq, _⟩
  rcases good_core_or_overflow p (p + b + 2 + e) t HC (by omega) with ⟨xs, HT, HY | ⟨u, rfl, EU⟩⟩
  · exact ⟨xs, HT, Or.inl (Safe.Safe_core xs HY)⟩
  · rcases CleanLast_total (q + b * 2) (next_p q + b / 2) u with ⟨zs, HL⟩
    have HU := post_good_cleanup q (1 - e) b u zs HPq (by dsimp [e]; omega)
        (by dsimp [q, next_p, e]; omega)
      Hb (by dsimp [q, next_p]; omega) Hbe HL
    rcases cleanup_entry_exit (next_p q) (b / 2) (q + b * 2) u zs (Chain.ChainS q HQ)
      (by omega) (by dsimp [q, next_p]; omega) (by dsimp [q, next_p, e]; omega)
      (by dsimp [q, next_p, e] at *; omega) (by dsimp [q, next_p, e] at *; omega) HL with ⟨ys, HV,
          HY⟩
    exact ⟨ys, progress_trans HT (progress_evstep_trans (section_step_eq HU
        (by dsimp [q, next_p, e]; list_nat_eq) rfl) HV), HY⟩

theorem odd_entry_exit (p k b t : Nat)
    (HC : Chain p) (Hko : k % 2 = 1) (Hkp : k ≤ p + (1 - p % 2))
    (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hsum : b + t ≤ (p + k) * 8) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  have HT := odd_even_section p e k b t HP Hp He Hpe Hko Hkp Hbe Hte
  dsimp [odd_output] at HT
  by_cases E : t < p + 2 + e - k
  · rw [ite_eq_left E] at HT
    rcases good_bounded_core p (b + k + t) (p + 2 + e - k - t) HC (by omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans HT HU, Or.inl (Safe.Safe_core ys HY)⟩
  · rw [ite_eq_right E] at HT
    rcases mixed_good_entry p b (t - (p + 2 + e - k)) HC Hb Hbp Hbe (by omega)
        (by dsimp [e] at *; omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans HT HU, HY⟩

theorem predecessor_entry_exit (p b t : Nat)
    (HC : Chain p) (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1)
        (Hsum : b + t ≤ (next_p p - 1) * 8) :
    ∃ ys, ((section_481 [next_p p - 1, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  have HT := predecessor_section p b t HC Hb Hbe Hte
  let q := next_p p
  have HQ : Chain q := Chain.ChainS p HC
  rcases Chain_spec q HQ with ⟨Hq, HPq, _⟩
  dsimp [pred_output] at HT
  by_cases E : t < (next_p p - 1) + 4 + (next_p p - 1) % 2
  · rw [ite_eq_left E] at HT
    rcases good_bounded_core q (b + t - 1) (q + 3 + (1 - q % 2) - t) HQ (by dsimp [q] at *; omega)
        with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans (section_step_eq HT (by rfl) (by dsimp [q] at *; list_nat_eq)) HU,
        Or.inl (Safe.Safe_core ys HY)⟩
  · rw [ite_eq_right E] at HT
    rcases mixed_good_entry q b (t - (q + 3 + (1 - q % 2))) HQ Hb (by dsimp [q, next_p]; omega) Hbe
        (by dsimp [q] at *; omega) (by dsimp [q] at *; omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans (section_step_eq HT (by rfl) (by dsimp [q] at *; list_nat_eq)) HU, HY⟩

theorem good_entry_exit (p b t : Nat)
    (HC : Chain p) (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1)
        (Hsum : b + t ≤ p * 8) :
    ∃ ys, ((section_481 [p, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  by_cases Hlow : t ≤ p + b + 1 + e
  · rcases good_bounded_core p b t HC (by dsimp [e] at *; omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, HT, Or.inl (Safe.Safe_core ys HY)⟩
  · rcases CleanLast_total (p + b * 2) (next_p p + b / 2) (t - (p + b + 2 + e)) with ⟨xs, HL⟩
    have HT := good_even_cleanup p e b t xs HP Hp He Hpe Hb Hbp Hbe (by omega) HL
    rcases cleanup_entry_exit (next_p p) (b / 2) (p + b * 2) (t - (p + b + 2 + e)) xs
      (Chain.ChainS p HC) (by omega) (by dsimp [next_p]; omega) (by dsimp [next_p, e]; omega)
      (by dsimp [e] at *; omega) (by dsimp [next_p, e] at *; omega) HL with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_evstep_trans HT HU, HY⟩

theorem even_entry_exit (p k b t : Nat)
    (HC : Chain p) (Hk : 2 ≤ k) (Hkp : k ≤ p) (Hke : k % 2 = 0)
    (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1) (Hsum : b + t ≤ (p + k) * 8) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  by_cases Ht1 : t = 1
  · subst Ht1
    by_cases Hsmall : b < k
    · rcases even_short_core p e k b HC He Hpe Hk Hkp Hke Hbe Hsmall with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Or.inl (Safe.Safe_core ys HY)⟩
    · rcases CleanLast_total (p + k * 2) (next_p p + k / 2) ((b - k) * 2 + 2) with ⟨xs, HL⟩
      have HT := even_short_clean p e k b xs HC He Hpe Hk Hkp Hke Hbe (by omega) HL
      rcases cleanup_entry_exit (next_p p) (k / 2) (p + k * 2) ((b - k) * 2 + 2) xs
        (Chain.ChainS p HC) (by omega) (by dsimp [next_p]; omega) (by dsimp [next_p, e]; omega)
        (by omega) (by dsimp [next_p, e] at *; omega) HL with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_evstep_trans HT HU, HY⟩
  · by_cases Hnormal : t + k ≤ p + b + e
    · rcases even_normal_section p e k b t HP He Hpe Hk Hkp Hke Hb Hbe (by omega) Hte (by omega)
          Hnormal with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Or.inl (Safe.Safe_stair p (1 - e) ys HC (by omega) HY)⟩
    · rcases CleanLast_total (p + b * 2) (next_p p + b / 2) (t + k - (p + b + 2 + e)) with ⟨xs, HL⟩
      have HT := even_overflow_section p e k b t xs HP He Hpe Hk Hkp Hke Hb Hbe Hte (by omega)
          (by omega) HL
      rcases cleanup_entry_exit (next_p p) (b / 2) (p + b * 2) (t + k - (p + b + 2 + e)) xs
        (Chain.ChainS p HC) (by omega) (by dsimp [next_p]; omega) (by dsimp [next_p, e]; omega)
        (by dsimp [e] at *; omega) (by dsimp [next_p, e] at *; omega) HL with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_evstep_trans HT HU, HY⟩

theorem entry_exit (p n b t : Nat)
    (HB : Band p n) (Hb : 2 ≤ b) (Hbp : b ≤ p) (Hbe : b % 2 = 0) (Hte : t % 2 = 1)
        (Hsum : b + t ≤ n * 8) :
    ∃ ys, ((section_481 [n, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  rcases HB with ⟨HC, Hpn, Hnp⟩
  let k := n - p
  have En : n = p + k := by dsimp [k]; omega
  by_cases Hk0 : k = 0
  · have heq : n = p := by omega
    rw [heq]
    exact good_entry_exit p b t HC Hb Hbp Hbe Hte (by omega)
  · by_cases Hpred : n = next_p p - 1
    · rw [Hpred] at Hsum ⊢
      exact predecessor_entry_exit p b t HC Hb Hbp Hbe Hte Hsum
    · rw [En] at Hsum ⊢
      by_cases Hko : k % 2 = 1
      · exact odd_entry_exit p k b t HC Hko (by dsimp [next_p] at *; omega) Hb Hbp Hbe Hte Hsum
      · exact even_entry_exit p k b t HC (by dsimp [next_p] at *; omega)
            (by dsimp [next_p] at *; omega) (by omega) Hb Hbp Hbe Hte Hsum

theorem core_entry_exit (xs : List Nat) (H : Core xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  cases H with
  | Core_entry xs H =>
    cases H with
    | Entry_unary n =>
      rcases unary_core_progress n with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Or.inl (Safe.Safe_core ys HY)⟩
    | Entry_small p n b t HB Hb Hbe Ht Hte Hbp Hsum =>
      exact entry_exit p n b t HB Hb Hbp Hbe Hte Hsum
  | Core_diagonal n b t Hn HD =>
    rcases diagonal_progress n b t Hn HD with ⟨ys, HT, HY⟩
    exact ⟨ys, HT, Or.inl HY⟩

theorem entry_exit_progress
    (Hhigh : ∀ xs, HighExit xs → ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys))
        ∧ EntryExit ys)
    (xs : List Nat) (H : EntryExit xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  rcases H with H | H
  · cases H with
    | Safe_core xs H => exact core_entry_exit xs H
    | Safe_stair p e xs HP He H =>
      rcases Stair_progress p e xs HP He H with ⟨ys, HT, HY | HY⟩
      · exact ⟨ys, HT, Or.inl (Safe.Safe_stair p e ys HP He HY)⟩
      · exact ⟨ys, HT, Or.inl (Safe.Safe_core ys (Core.Core_entry ys HY))⟩
    | Safe_half p k d t HP Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap =>
      rcases halving_progress p k d t HP Hk Hkp Hke Hd Hdp Hde Ht Hte Hcap with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Or.inl HY⟩
  · exact Hhigh xs H

theorem odd_post_good_finish (p e k t : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hko : k % 2 = 1) (Hkp : k ≤ p + e)
    (Hcap : t + e ≤ p + k * 3 + 2) :
    ∃ ys, ((section_481 [p + k, p + k + 2 + (1 - (p + k) % 2), t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ Core ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  have HT := odd_odd_section p e k (p + k + 2 + (1 - (p + k) % 2)) t HP Hp He Hpe Hko Hkp (by omega)
  rcases good_bounded_core p (p + k + 2 + (1 - (p + k) % 2) + k) (t + p + 2 + e - k) HC (by omega)
      with ⟨ys, HU, HY⟩
  exact ⟨ys, progress_trans HT HU, HY⟩

theorem odd_post_good_core (p e k t : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hko : k % 2 = 1) (Hkp : k ≤ p + e)
        (Hcap : t ≤ (p + k) * 3) :
    ∃ ys, ((section_481 [p + k, p + k + 2 + (1 - (p + k) % 2), t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ Core ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  have HT := odd_odd_section p e k (p + k + 2 + (1 - (p + k) % 2)) t HP Hp He Hpe Hko Hkp (by omega)
  let b := p + k + 2 + (1 - (p + k) % 2) + k
  rcases good_core_or_overflow p b (t + p + 2 + e - k) HC (by dsimp [b]; omega) with ⟨xs, HU,
      HY | ⟨u, rfl, EU⟩⟩
  · exact ⟨xs, progress_trans HT HU, HY⟩
  · let q := next_p p
    let j := k * 2 + 1 - e * 2
    have HQ : Chain q := Chain.ChainS p HC
    have E : p + b = q + j := by dsimp [b, q, j, next_p]; omega
    rcases odd_post_good_finish q (1 - e) j u HQ (by omega) (by dsimp [q, next_p]; omega)
      (by dsimp [j]; omega) (by dsimp [q, j, next_p]; omega)
          (by dsimp [q, j, b, next_p] at *; omega) with ⟨ys, HV, HY⟩
    exact ⟨ys, progress_trans HT (progress_trans (section_step_eq HU rfl (by rw [E])) HV), HY⟩

theorem post_good_even_entry (p n t : Nat)
    (HB : Band p n) (Hpred : n ≠ next_p p - 1) (Hte : t % 2 = 0) (Hcap : t ≤ n * 3) :
    ∃ ys, ((section_481 [n, n + 2 + (1 - n % 2), t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ EntryExit ys := by
  rcases HB with ⟨HC, Hpn, Hnp⟩
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  let k := n - p
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  have En : n = p + k := by dsimp [k]; omega
  by_cases Hk0 : k = 0
  · have heq : n = p := by omega
    rw [heq]
    rcases good_core_or_overflow p (p + 2 + e) t HC (by omega) with ⟨xs, HT, HY | ⟨u, rfl, EU⟩⟩
    · exact ⟨xs, HT, Or.inl (Safe.Safe_core xs HY)⟩
    · rcases good_bounded_core (next_p p) (next_p p + 2 + (1 - next_p p % 2)) u
        (Chain.ChainS p HC) (by dsimp [next_p, e] at *; omega) with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_trans (section_step_eq HT rfl (by dsimp [next_p, e] ; list_nat_eq)) HU,
          Or.inl (Safe.Safe_core ys HY)⟩
  · rw [En] at Hcap ⊢
    by_cases Hko : k % 2 = 1
    · rcases odd_post_good_core p e k t HC He Hpe Hko (by dsimp [next_p, k] at *; omega)
          Hcap with ⟨ys, HT, HY⟩
      exact ⟨ys, HT, Or.inl (Safe.Safe_core ys HY)⟩
    · have Hk : 2 ≤ k := by dsimp [next_p, k] at *; omega
      have Hkp : k ≤ p := by dsimp [next_p, k] at *; omega
      have Hke0 : k % 2 = 0 := by omega
      rcases CleanLast_total (p + k * 2) (next_p p + k / 2) t with ⟨xs, HL⟩
      have HT := post_good_cleanup p e k t xs HP He Hpe Hk Hkp Hke0 HL
      rcases cleanup_entry_exit (next_p p) (k / 2) (p + k * 2) t xs (Chain.ChainS p HC)
        (by omega) (by dsimp [next_p]; omega) (by dsimp [next_p, e]; omega)
        Hte (by dsimp [next_p, e] at *; omega) HL with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_evstep_trans (section_step_eq HT) HU, HY⟩

theorem high_odd_progress (p e k t : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
        (Hko : k % 2 = 1)
    (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hcap : t + k * 12 + 2 + e ≤ p * 7) :
    ∃ ys, ((section_481 [p + k, p + k * 8 + 2 + e, t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ EntryExit ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  have HT := odd_odd_section p e k (p + k * 8 + 2 + e) t HP Hp He Hpe Hko (by omega) (by omega)
  rcases good_core_or_overflow p (p + k * 8 + 2 + e + k) (t + p + 2 + e - k) HC (by omega) with ⟨xs,
      HU, HY | ⟨u, rfl, EU⟩⟩
  · exact ⟨xs, progress_trans HT HU, Or.inl (Safe.Safe_core xs HY)⟩
  · let q := next_p p
    have HQ : Chain q := Chain.ChainS p HC
    have E : p + (p + k * 8 + 2 + e + k) = q + k * 9 := by dsimp [q, next_p]; omega
    have Hbound : u ≤ (q + k * 9) * 3 := by dsimp [q, next_p] at *; omega
    have Hue : u % 2 = 0 := by dsimp [q, next_p] at *; omega
    have HR : ∃ r, Band r (q + k * 9) ∧ q + k * 9 ≠ next_p r - 1 := by
      by_cases Hlo : q + k * 9 < next_p q
      · exact ⟨q, ⟨HQ, by dsimp [q, next_p] at *; omega, Hlo⟩, by dsimp [q, next_p] at *; omega⟩
      · exact ⟨next_p q, ⟨Chain.ChainS q HQ, by dsimp [q, next_p] at *; omega,
            by dsimp [q, next_p] at *; omega⟩, by dsimp [q, next_p] at *; omega⟩
    rcases HR with ⟨r, HB, Hpred⟩
    rcases post_good_even_entry r (q + k * 9) u HB Hpred Hue Hbound with ⟨ys, HV, HY⟩
    exact ⟨ys, progress_trans HT (progress_trans (section_step_eq HU rfl (by rw [E])) HV), HY⟩

theorem small_cleanup_upper (p k b t : Nat)
    (HC : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 + 2 ≤ p) (Hb : 2 ≤ b) (Hbe : b % 2 = 0)
    (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hsum : b + t ≤ p + k * 8 + 4 + (1 - p % 2)) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢* (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  by_cases Hsmall : b ≤ p
  · refine ⟨[p + k, b, t], ⟨0, rfl⟩, ?_⟩
    exact Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_small p (p + k) b t
      ⟨HC, by omega, by dsimp [next_p]; omega⟩ Hb Hbe Ht Hte Hsmall (by omega)))
  · by_cases Hko : k % 2 = 1
    · rcases odd_even_bounded_core p e k b t HC He Hpe Hko (by omega) Hb Hbe Hte
          (by dsimp [e] at *; omega) with ⟨ys, HT, HY⟩
      exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
    · have Hke0 : k % 2 = 0 := by omega
      have Hk2 : 2 ≤ k := by omega
      by_cases Hnear : b ≤ p + k
      · by_cases Hcap : t + k ≤ p + b + e
        · rcases near_core p e k b t HC He Hpe Hk (by omega) (by omega)
              Hnear Hbe Ht Hte Hcap with ⟨ys, HT, HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, HY⟩
        · rcases even_overflow_core p e k b t HC He Hpe Hk2 (by omega) Hke0 Hb Hbe Hte Hnear
              (by omega) (by dsimp [next_p, e] at *; omega) with ⟨ys, HT, HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
      · refine ⟨[p + k, b, t], ⟨0, rfl⟩, ?_⟩
        exact Safe_eq (Safe.Safe_half p k (b - (p + k)) t HC Hk2 (by omega) Hke0 (by omega)
            (by dsimp [e] at *; omega) (by dsimp [e] at *; omega) Ht Hte (by dsimp [e] at *; omega))

theorem small_near_reaches (p k b t : Nat)
    (HC : Chain p) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p) (Hb : p < b) (Hbe : b % 2 = 0)
    (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hdelta : b - (p + k) ≤ p * 2)
    (Hbound : t + k ≤ p + b + 2 + (1 - p % 2) + next_p p)
    (Hcap : b ≤ p + k ∨ t + k ≤ p + b + (1 - p % 2)) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢* (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let e := 1 - p % 2
  have He : e ≤ 1 := by dsimp [e]; omega
  have Hpe : p % 2 + e = 1 := by dsimp [e]; omega
  by_cases Hko : k % 2 = 1
  · rcases odd_even_bounded_core p e k b t HC He Hpe Hko (by omega) (by omega) Hbe Hte
        (by dsimp [next_p, e] at *; omega) with ⟨ys, HT, HY⟩
    exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
  · have Hke0 : k % 2 = 0 := by omega
    have Hk2 : 2 ≤ k := by omega
    by_cases Hnear : b ≤ p + k
    · by_cases Hnormal : t + k ≤ p + b + e
      · rcases near_core p e k b t HC He Hpe Hk Hkp Hb Hnear Hbe Ht Hte Hnormal with ⟨ys, HT, HY⟩
        exact ⟨ys, ReachesPlus.to_star HT, HY⟩
      · rcases even_overflow_core p e k b t HC He Hpe Hk2 (by omega) Hke0 (by omega) Hbe Hte Hnear
            (by omega) Hbound with ⟨ys, HT, HY⟩
        exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
    · refine ⟨[p + k, b, t], ⟨0, rfl⟩, ?_⟩
      exact Safe_eq (Safe.Safe_half p k (b - (p + k)) t HC Hk2 Hkp Hke0 (by omega) Hdelta
          (by dsimp [e] at *; omega) Ht Hte (by dsimp [e] at *; omega))

theorem odd_block_short (p e k b t : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hk : 1 ≤ k) (Hkp : k * 4 ≤ p)
    (Hb : p ≤ b) (Hbo : b % 2 = 1) (Ht : t ≤ p) :
    ∃ ys, ((section_481 [p + k, b, t]) [target_tm]⊢⁺ (section_481 ys)) ∧ Core ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  by_cases Hko : k % 2 = 1
  · have HT := odd_odd_section p e k b t HP Hp He Hpe Hko (by omega) Hbo
    rcases good_bounded_core p (b + k) (t + p + 2 + e - k) HC (by omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans HT HU, HY⟩
  · let N := (p + k * 3 + b + (1 - e) - 2) / 2
    let X := p + b - k / 2
    rcases Band_above p X HC (by dsimp [X]; omega) with ⟨q, Hq, HB⟩
    rcases CleanLast_total N X t with ⟨ys, HL⟩
    refine ⟨ys, even_odd_section p (1 - e) k b t ys HP (by omega) (by omega) (by omega) (by omega)
        (by omega) Hbo HL, ?_⟩
    cases HL with
    | Clean0 => exact Core.Core_entry _ (CoreEntry.Entry_unary _)
    | Clean1 => exact Core.Core_entry _ (CoreEntry.Entry_unary _)
    | CleanEven s Hs =>
      exact Core.Core_entry _ (CoreEntry.Entry_small q X (2 + s * 2) (3 + (N - s) * 2) HB
        (by omega) (by omega) (by omega) (by omega) (by dsimp [N, X] at *; omega)
            (by dsimp [N, X] at *; omega))
    | CleanOdd s Hs =>
      exact Core.Core_entry _ (CoreEntry.Entry_small q X (2 + s * 2) (5 + (N - s) * 2) HB
        (by omega) (by omega) (by omega) (by omega) (by dsimp [N, X] at *; omega)
            (by dsimp [N, X] at *; omega))
    | CleanBorder => omega
    | CleanOver a => omega

theorem high_even_low (p e j b u : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hj : 1 ≤ j) (Hjp : j * 8 ≤ p)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hu : 5 ≤ u) (Hue : u % 2 = 1)
    (Hsum : b + u = p * 2 + j * 22 + 7) (Hcap : b + j * 24 + 3 + e ≤ p * 7) :
    ∃ ys, ((section_481 [next_p p + j * 15, b, u]) [target_tm]⊢* (section_481 ys)) ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let q := next_p p
  have HQ : Chain q := Chain.ChainS p HC
  rcases Chain_spec q HQ with ⟨Hq, HPq, _⟩
  have Hqe : q % 2 = e := by dsimp [q, next_p]; omega
  by_cases Hsmall : b ≤ q
  · refine ⟨[q + j * 15, b, u], ⟨0, rfl⟩, ?_⟩
    exact Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_small q (q + j * 15) b u
      ⟨HQ, by omega, by dsimp [q, next_p] at *; omega⟩ Hb Hbe (by omega) Hue Hsmall
          (by dsimp [q, next_p] at *; omega)))
  · by_cases Hjo : j % 2 = 1
    · rcases odd_even_bounded_core q (1 - e) (j * 15) b u HQ (by omega) (by omega) (by omega)
          (by dsimp [q, next_p]; omega) Hb Hbe Hue (by dsimp [q, next_p] at *; omega) with ⟨ys, HT,
              HY⟩
      exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
    · have Hje0 : j % 2 = 0 := by omega
      by_cases Hnear : b ≤ q + j * 15
      · by_cases Hnormal : u + j * 15 ≤ q + b + (1 - e)
        · rcases even_normal_section q (1 - e) (j * 15) b u HPq (by omega) (by omega) (by omega)
              (by dsimp [q, next_p]; omega) (by omega) Hb Hbe (by omega) Hue Hnear Hnormal with ⟨ys,
                  HT, HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_stair q e ys HQ He (Stair_eq HY)⟩
        · rcases even_overflow_core q (1 - e) (j * 15) b u HQ (by omega) (by omega) (by omega)
              (by dsimp [q, next_p]; omega) (by omega) Hb Hbe Hue Hnear (by omega)
                  (by dsimp [q, next_p] at *; omega) with ⟨ys, HT, HY⟩
          exact ⟨ys, ReachesPlus.to_star HT, Safe.Safe_core ys HY⟩
      · rcases Repair_total q (1 - e) (j * 15) (b - (q + j * 15)) (u - 1) (by omega) with ⟨xs, HR⟩
        have HT := wide_triple q (1 - e) (j * 15) b u xs HPq Hq (by omega) (by omega) (by omega)
          (by dsimp [q, next_p]; omega) (by omega) Hb Hbe (by omega) Hue (by omega)
          (by dsimp [q, next_p] at *; omega) (by dsimp [q, next_p] at *; omega) HR
        cases HR with
        | Repair_positive x Hx HX =>
          rcases small_near_reaches (next_p q) (j * 15 / 2) (q * 2 + (b - (q + j * 15)) * 2 + 2) x
            (Chain.ChainS q HQ) (by omega) (by dsimp [q, next_p] at *; omega)
                (by dsimp [q, next_p] at *; omega)
            (by omega) Hx (by omega) (by dsimp [q, next_p] at *; omega)
                (by dsimp [q, next_p] at *; omega)
            (by dsimp [q, next_p] at *; omega) with ⟨ys, HU, HY⟩
          exact ⟨ys, ReachesStar.trans (ReachesPlus.to_star HT) HU, HY⟩
        | Repair_negative x Hx HX => dsimp [q, next_p] at *; omega

theorem high_second_low (p e j b u : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hj : 1 ≤ j) (_Hjp : j * 8 ≤ p)
        (Hje : j % 2 = 0)
    (Hb : 2 ≤ b) (Hbe : b % 2 = 0) (Hu : 1 ≤ u) (Hue : u % 2 = 1)
    (Hsum : b + u = (next_p p + (j / 2) * 67) * 2 + 5) (Hcap : b + j * 46 + 7 + e ≤ p * 5) :
    ∃ ys, ((section_481 [next_p (next_p p) + (j / 2) * 29, b, u]) [target_tm]⊢* (section_481 ys))
        ∧ Safe ys := by
  let q := next_p (next_p p)
  have HQ : Chain q := Chain.ChainS _ (Chain.ChainS p HC)
  by_cases Hsmall : b ≤ q
  · refine ⟨[q + (j / 2) * 29, b, u], ⟨0, rfl⟩, ?_⟩
    exact Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_small q (q + (j / 2) * 29) b u
      ⟨HQ, by omega, by dsimp [q, next_p] at *; omega⟩ Hb Hbe Hu Hue Hsmall
          (by dsimp [q, next_p] at *; omega)))
  · exact small_cleanup_upper q ((j / 2) * 29) b u HQ (by omega) (by dsimp [q, next_p] at *; omega)
      Hb Hbe Hu Hue (by dsimp [q, next_p] at *; omega)

theorem high_even_high (p e j c : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hj : 1 ≤ j) (Hjp : j * 8 ≤ p)
    (Hce : c % 2 = 0) (Hcap : c + j * 46 + 7 + e ≤ p * 5) :
    ∃ ys, ((section_481 [next_p p + j * 15, p * 2 + j * 22 + 5, c]) [target_tm]⊢⁺ (section_481 ys))
        ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  let q := next_p p
  have HQ : Chain q := Chain.ChainS p HC
  rcases Chain_spec q HQ with ⟨Hq, HPq, _⟩
  have Hqe : q % 2 = e := by dsimp [q, next_p]; omega
  by_cases Hjo : j % 2 = 1
  · have HT := odd_odd_section q (1 - e) (j * 15) (p * 2 + j * 22 + 5) c HPq Hq
      (by omega) (by omega) (by omega) (by dsimp [q, next_p]; omega) (by omega)
    rcases good_core_or_overflow q (p * 2 + j * 22 + 5 + j * 15) (c + q + 2 + (1 - e) - j * 15) HQ
        (by omega) with ⟨xs, HU, HY | ⟨u, rfl, EU⟩⟩
    · exact ⟨xs, progress_trans HT HU, Safe.Safe_core xs HY⟩
    · let r := next_p q
      have HR : Chain r := Chain.ChainS q HQ
      have E : q + (p * 2 + j * 22 + 5 + j * 15) = r + j * 37 := by dsimp [r, q, next_p]; omega
      rcases odd_post_good_core r e (j * 37) u HR He (by dsimp [r, q, next_p]; omega)
        (by omega) (by dsimp [r, q, next_p] at *; omega) (by dsimp [r, q, next_p] at *; omega)
            with ⟨ys, HV, HY⟩
      exact ⟨ys, progress_trans HT (progress_trans (section_step_eq HU rfl (by rw [E])) HV),
          Safe.Safe_core ys HY⟩
  · have Hje0 : j % 2 = 0 := by omega
    let N := q + (j / 2) * 67
    let X := next_p q + (j / 2) * 29
    rcases CleanLast_total N X c with ⟨xs, HL⟩
    have HT : (section_481 [q + j * 15, p * 2 + j * 22 + 5, c]) [target_tm]⊢⁺ (section_481 xs) := by
      refine even_odd_section q e (j * 15) (p * 2 + j * 22 + 5) c xs HPq He Hqe (by omega)
          (by dsimp [q, next_p]; omega) (by omega) (by omega) ?_
      exact CleanLast_eq HL (by dsimp [N, X, q, next_p]; omega) (by dsimp [N, X, q, next_p]; omega)
          rfl rfl
    cases HL with
    | Clean0 => exact ⟨_, HT, Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_unary _))⟩
    | Clean1 => omega
    | CleanEven s Hs =>
      rcases high_second_low p e j (2 + s * 2) (3 + (N - s) * 2) HC He Hpe Hj Hjp Hje0
        (by omega) (by omega) (by omega) (by omega) (by dsimp [N, q] at *; omega)
            (by dsimp [N, q, next_p] at *; omega) with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_evstep_trans HT HU, HY⟩
    | CleanOdd s Hs => omega
    | CleanBorder =>
      rcases high_second_low p e j (4 + N * 2) 1 HC He Hpe Hj Hjp Hje0
        (by omega) (by omega) (by omega) (by omega) (by dsimp [N, q] at *; omega)
            (by dsimp [N, q, next_p] at *; omega) with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_evstep_trans HT HU, HY⟩
    | CleanOver a =>
      rcases odd_block_short (next_p q) e ((j / 2) * 29) (5 + N * 2) a (Chain.ChainS q HQ) He
        (by dsimp [q, next_p]; omega) (by omega) (by dsimp [q, next_p] at *; omega)
        (by dsimp [N, q, next_p] at *; omega) (by omega) (by dsimp [N, q, next_p] at *; omega)
            with ⟨ys, HU, HY⟩
      exact ⟨ys, progress_trans HT HU, Safe.Safe_core ys HY⟩

theorem high_even_progress (p e j t : Nat)
    (HC : Chain p) (He : e ≤ 1) (Hpe : p % 2 + e = 1) (Hj : 1 ≤ j) (Hjp : j * 8 ≤ p)
    (Ht : 1 ≤ t) (Hte : t % 2 = 1) (Hcap : t + j * 24 + 2 + e ≤ p * 7) :
    ∃ ys, ((section_481 [p + j * 2, p + j * 16 + 2 + e, t]) [target_tm]⊢⁺ (section_481 ys))
        ∧ Safe ys := by
  rcases Chain_spec p HC with ⟨Hp, HP, _⟩
  rcases CleanLast_total (p + j * 11) (next_p p + j * 15) t with ⟨xs, HL⟩
  have HT : (section_481 [p + j * 2, p + j * 16 + 2 + e, t]) [target_tm]⊢⁺ (section_481 xs) := by
    refine even_odd_section p (1 - e) (j * 2) (p + j * 16 + 2 + e) t xs HP (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) ?_
    exact CleanLast_eq HL (by omega) (by dsimp [next_p]; omega) rfl rfl
  cases HL with
  | Clean0 => omega
  | Clean1 => exact ⟨_, HT, Safe.Safe_core _ (Core.Core_entry _ (CoreEntry.Entry_unary _))⟩
  | CleanEven s Hs => omega
  | CleanOdd s Hs =>
    rcases high_even_low p e j (2 + s * 2) (5 + (p + j * 11 - s) * 2) HC He Hpe Hj Hjp
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_evstep_trans HT HU, HY⟩
  | CleanBorder => omega
  | CleanOver a =>
    rcases high_even_high p e j a HC He Hpe Hj Hjp (by omega) (by omega) with ⟨ys, HU, HY⟩
    exact ⟨ys, progress_trans HT (section_step_eq HU), HY⟩

theorem high_exit_progress (xs : List Nat) (H : HighExit xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys := by
  cases H with
  | High_exit p k t HC Hk Hkp Ht Hte Hcap =>
    by_cases Hko : k % 2 = 1
    · exact high_odd_progress p (1 - p % 2) k t HC (by omega) (by omega) Hk Hkp Hko Ht Hte Hcap
    · rcases high_even_progress p (1 - p % 2) (k / 2) t HC (by omega) (by omega) (by omega)
          (by omega) Ht Hte (by omega) with ⟨ys, HT, HY⟩
      exact ⟨ys, section_step_eq HT, Or.inl HY⟩

theorem closed_progress (xs : List Nat) (H : EntryExit xs) :
    ∃ ys, ((section_481 xs) [target_tm]⊢⁺ (section_481 ys)) ∧ EntryExit ys :=
  entry_exit_progress high_exit_progress xs H

theorem entry_unary_in_entryExit (n : Nat) : EntryExit [n] :=
  Or.inl (Safe.Safe_core [n] (Core.Core_entry [n] (CoreEntry.Entry_unary n)))

theorem neverHaltsFrom_of_reachesStar {M : Machine (Fin 2) (Fin 6)} {c₁ c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : c₁ [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : NeverHaltsFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩

theorem section_nonhalt {xs : List Nat} (h : EntryExit xs) :
    NeverHaltsFrom target_tm (section_481 xs) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant
      (P := fun c => ∃ ys, c = section_481 ys ∧ EntryExit ys) ?_ ⟨xs, rfl, h⟩
  rintro _ ⟨ys, rfl, hys⟩
  rcases closed_progress ys hys with ⟨zs, hstep, hzs⟩
  exact ⟨section_481 zs, hstep, zs, rfl, hzs⟩

theorem init_481 : (init []) [target_tm]⊢* section_481 [1] := init_tm1

theorem init_221 : ((default : ListBlank (Fin 2)) {{2}}> default) [target_tm]⊢* section_481 [2] :=
  step_end (simSteps_star_ex 6 ⟨C, .right, [0], [0, 0]⟩ ⟨B, .right, [1, 0, 1], []⟩
    rfl default default) (by norm_cfg) (by norm_cfg)

theorem init_554 : ((default : ListBlank (Fin 2)) {{5}}> default) [target_tm]⊢* section_481 [4] :=
  step_end (simSteps_star_ex 31 ⟨F, .right, [0, 0, 0, 0, 0, 0], [0]⟩
    ⟨B, .right, [1, 0, 1, 0, 1, 0, 1], []⟩ rfl default default) (by norm_cfg) (by norm_cfg)

end

public section

theorem is_not_halt_from_0221 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{2}}> default) [target]⊢* cfg) →
      (step target cfg).isSome :=
  neverHaltsFrom_of_reachesStar init_221 (section_nonhalt (entry_unary_in_entryExit 2))

theorem is_not_halt_from_0554 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{5}}> default) [target]⊢* cfg) →
      (step target cfg).isSome :=
  neverHaltsFrom_of_reachesStar init_554 (section_nonhalt (entry_unary_in_entryExit 4))

theorem is_not_halt : IsNotHalt target := by
  exact neverHaltsFrom_of_reachesStar init_481 (section_nonhalt (entry_unary_in_entryExit 1))

end

end BusyBeaver.M_1RB0LC_1RC0RA_1RD0RF_0LEHHH_1LB1LA_1LD1RA
