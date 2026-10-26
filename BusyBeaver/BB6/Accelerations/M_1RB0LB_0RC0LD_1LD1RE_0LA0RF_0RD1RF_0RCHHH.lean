/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Machine `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`

Formal `HasOdometerReduction` proof for the 6-state, 2-symbol Busy Beaver machine
`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---` (Beaver Math Olympiad Problem 10):
- <https://wiki.bbchallenge.org/wiki/1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC--->
- <https://wiki.bbchallenge.org/wiki/Beaver_Math_Olympiad>

The left half-tape encodes a mixed-radix odometer stack over `L0 = [0, 0, 1, 0]` (`2c + 1`),
`L1 = [1, 0, 1, 0]` (`2c`), and `L2 = [1, 1, 0]` (`⌊c / 2⌋`), while the right half-tape holds the
active binary stream scanned from state `C` (`2 : Fin 6`).
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH

open Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Mixed-Radix Odometer Alphabet and Configurations -/

private theorem fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  match b with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr rfl

private inductive OdomTok where
  | L0
  | L1
  | L2
  deriving DecidableEq, Repr

@[simp]
private def odomWord : OdomTok → List (Fin 2)
  | .L0 => [0, 0, 1, 0]
  | .L1 => [1, 0, 1, 0]
  | .L2 => [1, 1, 0]

@[simp]
private def encOdom : List OdomTok → ListBlank (Fin 2)
  | [] => [1] +> default
  | t :: l => odomWord t +> encOdom l

private theorem encOdom_non_surjective :
    ∃ t : ListBlank (Fin 2), ∀ stk : List OdomTok, encOdom stk ≠ t := by
  refine ⟨default, fun stk h => ?_⟩
  cases stk with
  | nil =>
    have h1 : (encOdom []).head = (default : ListBlank (Fin 2)).head :=
      congrArg ListBlank.head h
    simp only [encOdom, ListBlank.append, ListBlank.head_cons, ListBlank.head_default_fin] at h1
    revert h1; decide
  | cons t tl =>
    cases t with
    | L0 =>
      have h1 : (encOdom (.L0 :: tl)).tail.tail.head =
          (default : ListBlank (Fin 2)).tail.tail.head :=
        congrArg (fun x => x.tail.tail.head) h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.tail_cons, ListBlank.head_cons,
        ListBlank.tail_default, ListBlank.head_default_fin] at h1
      revert h1; decide
    | L1 =>
      have h1 : (encOdom (.L1 :: tl)).head = (default : ListBlank (Fin 2)).head :=
        congrArg ListBlank.head h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.head_cons,
        ListBlank.head_default_fin] at h1
      revert h1; decide
    | L2 =>
      have h1 : (encOdom (.L2 :: tl)).head = (default : ListBlank (Fin 2)).head :=
        congrArg ListBlank.head h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.head_cons,
        ListBlank.head_default_fin] at h1
      revert h1; decide

@[simp]
private def cfg_R (l : List OdomTok) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  evalOdomR .leftOdom 2 [0] (encOdom l) r

@[simp]
private def cfg_L (l : List OdomTok) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  evalOdomL .leftOdom 0 [0] (encOdom l) r

private def IsInOdomSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ stk w, cfg = evalOdomR .leftOdom 2 [0] (encOdom stk) w

/-! ## Local Step Rules -/

private theorem step_init : (init []) [target]⊢⁺ cfg_R [] default := by
  simp only [cfg_R, evalOdomR, encOdom, ListBlank.append]
  bb_steps

private theorem step_R_0 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_R l ((0 : Fin 2) >> r)) [target]⊢⁺ cfg_L l ((1 : Fin 2) >> r) := by
  simp only [cfg_L, cfg_R, evalOdomL, evalOdomR, ListBlank.append]
  bb_steps

private theorem step_R_100 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_R l ((1 : Fin 2) >> 0 >> 0 >> r)) [target]⊢⁺ cfg_R (.L2 :: l) r := by
  simp only [cfg_R, evalOdomR, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_R_110 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_R l ((1 : Fin 2) >> 1 >> 0 >> r)) [target]⊢⁺ cfg_R (.L2 :: l) r := by
  simp only [cfg_R, evalOdomR, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_R_1010 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_R l ((1 : Fin 2) >> 0 >> 1 >> 0 >> r)) [target]⊢⁺ cfg_R (.L0 :: l) r := by
  simp only [cfg_R, evalOdomR, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_R_1011_halt (l : List OdomTok) (r : ListBlank (Fin 2)) :
    ∃ cfg_halt,
      ((cfg_R l ((1 : Fin 2) >> 0 >> 1 >> 1 >> r)) [target]⊢⁺ cfg_halt) ∧
      (step target cfg_halt).isNone := by
  refine ⟨⟨some 5, ⟨1, (0 : Fin 2) >> 0 >> 1 >> 0 >> encOdom l, r⟩⟩, ?_, ?_⟩
  · simp only [cfg_R, evalOdomR, ListBlank.append]
    bb_steps
  · bb_halt

private theorem step_R_111_halt (l : List OdomTok) (r : ListBlank (Fin 2)) :
    ∃ cfg_halt,
      ((cfg_R l ((1 : Fin 2) >> 1 >> 1 >> r)) [target]⊢⁺ cfg_halt) ∧
      (step target cfg_halt).isNone := by
  refine ⟨⟨some 5, ⟨1, (1 : Fin 2) >> 1 >> 0 >> encOdom l, r⟩⟩, ?_, ?_⟩
  · simp only [cfg_R, evalOdomR, ListBlank.append]
    bb_steps
  · bb_halt

private theorem step_L_L0 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_L (.L0 :: l) r) [target]⊢⁺ cfg_R (.L1 :: l) r := by
  simp only [cfg_L, cfg_R, evalOdomL, evalOdomR, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_L_L1 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_L (.L1 :: l) r) [target]⊢⁺ cfg_L l ((1 : Fin 2) >> 0 >> 1 >> 0 >> r) := by
  simp only [cfg_L, evalOdomL, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_L_L2 (l : List OdomTok) (r : ListBlank (Fin 2)) :
    (cfg_L (.L2 :: l) r) [target]⊢⁺ cfg_L l ((0 : Fin 2) >> 0 >> 0 >> r) := by
  simp only [cfg_L, evalOdomL, encOdom, odomWord, ListBlank.append]
  bb_steps

private theorem step_L_nil (r : ListBlank (Fin 2)) :
    (cfg_L [] r) [target]⊢⁺ cfg_R [] ((1 : Fin 2) >> 0 >> r) := by
  simp only [cfg_L, cfg_R, evalOdomL, evalOdomR, encOdom, ListBlank.append]
  bb_steps

/-! ## Odometer Capacity, Decrement, and Drain Soundness -/

@[simp]
private def cap : List OdomTok → ℕ
  | [] => 0
  | .L0 :: l => 2 * cap l + 1
  | .L1 :: l => 2 * cap l
  | .L2 :: l => cap l / 2

@[simp]
private def dec_fuel : ℕ → List OdomTok → List OdomTok
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, .L0 :: l => .L1 :: l
  | n + 1, .L1 :: l => .L0 :: dec_fuel n l
  | n + 1, .L2 :: l => .L2 :: dec_fuel n (dec_fuel n l)

private def dec (l : List OdomTok) : List OdomTok :=
  dec_fuel l.length l

@[simp]
private theorem length_dec_fuel (n : ℕ) (l : List OdomTok) :
    (dec_fuel n l).length = l.length := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons t tl => cases t <;> simp [dec_fuel, ih]

@[simp]
private theorem length_dec (l : List OdomTok) : (dec l).length = l.length :=
  length_dec_fuel l.length l

@[simp] private theorem dec_L0 (l : List OdomTok) : dec (.L0 :: l) = .L1 :: l := rfl
@[simp] private theorem dec_L1 (l : List OdomTok) : dec (.L1 :: l) = .L0 :: dec l := rfl

@[simp]
private theorem dec_L2 (l : List OdomTok) : dec (.L2 :: l) = .L2 :: dec (dec l) := by
  simp only [dec, List.length_cons, dec_fuel, length_dec_fuel]

private theorem cap_dec_aux (n : ℕ) :
    ∀ l : List OdomTok, l.length ≤ n → cap l ≥ 1 → cap (dec l) = cap l - 1 := by
  induction n with
  | zero =>
    intro l hlen h
    cases l <;> simp at hlen h
  | succ n ih =>
    intro l hlen h
    cases l with
    | nil => simp at h
    | cons t l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => simp
      | L1 =>
        simp only [cap, dec_L1] at h ⊢
        have h1 : cap l ≥ 1 := by omega
        rw [ih l hlen h1]; omega
      | L2 =>
        simp only [cap, dec_L2] at h ⊢
        have h2 : cap l ≥ 1 := by omega
        have ih1 := ih l hlen h2
        have h3 : cap (dec l) ≥ 1 := by omega
        have ih2 := ih (dec l) (by rw [length_dec]; exact hlen) h3
        rw [ih2, ih1]; omega

private theorem cap_dec (l : List OdomTok) (h : cap l ≥ 1) : cap (dec l) = cap l - 1 :=
  cap_dec_aux l.length l (Nat.le_refl _) h

private theorem runHL_dec_aux (n : ℕ) :
    ∀ (l : List OdomTok) (r : ListBlank (Fin 2)), l.length ≤ n → cap l ≥ 1 →
      (cfg_L l r) [target]⊢⁺ cfg_R (dec l) r := by
  induction n with
  | zero =>
    intro l _ hlen h
    cases l <;> simp at hlen h
  | succ n ih =>
    intro l r hlen h
    cases l with
    | nil => simp at h
    | cons t l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 =>
        simp only [dec_L0]
        exact step_L_L0 l r
      | L1 =>
        simp only [cap, dec_L1] at h ⊢
        have h1 : cap l ≥ 1 := by omega
        exact (step_L_L1 l r).trans ((ih l _ hlen h1).trans (step_R_1010 (dec l) r))
      | L2 =>
        simp only [cap, dec_L2] at h ⊢
        have h2 : cap l ≥ 1 := by omega
        have h3 : cap (dec l) ≥ 1 := by have := cap_dec l h2; omega
        have hlen2 : (dec l).length ≤ n := by rw [length_dec]; exact hlen
        exact (step_L_L2 l r).trans
          ((ih l _ hlen h2).trans
            ((step_R_0 (dec l) _).trans
              ((ih (dec l) _ hlen2 h3).trans
                (step_R_100 (dec (dec l)) r))))

private theorem runHL_dec (l : List OdomTok) (r : ListBlank (Fin 2)) (h : cap l ≥ 1) :
    (cfg_L l r) [target]⊢⁺ cfg_R (dec l) r :=
  runHL_dec_aux l.length l r (Nat.le_refl _) h

@[simp]
private def drain : List OdomTok → List (Fin 2)
  | [] => [1, 0]
  | .L0 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L1 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L2 :: tl => drain tl ++ (if cap tl % 2 = 0 then [0, 0, 0] else [1, 0, 0])

private theorem drain_ne_nil : ∀ l : List OdomTok, drain l ≠ []
  | [] => by decide
  | .L0 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _
  | .L1 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _
  | .L2 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _

private theorem drain_dec_aux (n : ℕ) :
    ∀ l : List OdomTok, l.length ≤ n → cap l ≥ 1 → drain (dec l) = drain l := by
  induction n with
  | zero =>
    intro l hlen hcap
    cases l <;> simp at hlen hcap
  | succ n ih =>
    intro l hlen hcap
    cases l with
    | nil => simp at hcap
    | cons t tl =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => rfl
      | L1 =>
        simp only [cap, dec_L1, drain] at hcap ⊢
        rw [ih tl hlen (by omega)]
      | L2 =>
        simp only [cap, dec_L2, drain] at hcap ⊢
        have hdec1_cap : cap (dec tl) = cap tl - 1 := cap_dec tl (by omega)
        have hdec2_cap : cap (dec (dec tl)) = cap tl - 2 := by
          rw [cap_dec (dec tl) (by omega), hdec1_cap]; omega
        have hpar : (cap (dec (dec tl)) % 2 = 0) ↔ (cap tl % 2 = 0) := by omega
        have ih1 := ih tl hlen (by omega)
        have ih2 := ih (dec tl) (by rw [length_dec]; exact hlen) (by omega)
        have hif :
            (if cap (dec (dec tl)) % 2 = 0 then ([0, 0, 0] : List (Fin 2)) else [1, 0, 0]) =
              (if cap tl % 2 = 0 then ([0, 0, 0] : List (Fin 2)) else [1, 0, 0]) := by
          by_cases h1 : cap tl % 2 = 0
          · rw [ite_eq_left h1, ite_eq_left (hpar.mpr h1)]
          · rw [ite_eq_right h1, ite_eq_right (mt hpar.mp h1)]
        rw [ih2, ih1, hif]

private theorem drain_dec (l : List OdomTok) (hcap : cap l ≥ 1) : drain (dec l) = drain l :=
  drain_dec_aux l.length l (Nat.le_refl _) hcap

private theorem run_drain_aux (n : ℕ) :
    ∀ (l : List OdomTok) (w : ListBlank (Fin 2)), l.length ≤ n → cap l = 0 →
      (cfg_L l w) [target]⊢⁺ cfg_R [] (drain l +> w) := by
  induction n with
  | zero =>
    intro l w hlen _
    cases l with
    | nil => exact step_L_nil w
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro l w hlen hcap
    cases l with
    | nil => exact step_L_nil w
    | cons t tl =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => simp only [cap] at hcap; omega
      | L1 =>
        simp only [cap] at hcap
        have htl : cap tl = 0 := by omega
        simp only [drain, ListBlank.append_assoc]
        exact (step_L_L1 tl w).trans (ih tl ([1, 0, 1, 0] +> w) hlen htl)
      | L2 =>
        simp only [cap] at hcap
        simp only [drain, ListBlank.append_assoc]
        by_cases h0 : cap tl = 0
        · have hpar : cap tl % 2 = 0 := by omega
          rw [ite_eq_left hpar]
          exact (step_L_L2 tl w).trans (ih tl ([0, 0, 0] +> w) hlen h0)
        · have hpar : ¬ (cap tl % 2 = 0) := by omega
          rw [ite_eq_right hpar]
          have hdec_cap : cap (dec tl) = 0 := by have := cap_dec tl (by omega); omega
          have hdec_len : (dec tl).length ≤ n := by rw [length_dec]; exact hlen
          have h_ih := ih (dec tl) ([1, 0, 0] +> w) hdec_len hdec_cap
          rw [drain_dec tl (by omega)] at h_ih
          exact (step_L_L2 tl w).trans
            ((runHL_dec tl ((0 : Fin 2) >> 0 >> 0 >> w) (by omega)).trans
              ((step_R_0 (dec tl) ((0 : Fin 2) >> 0 >> w)).trans h_ih))

private theorem run_drain (l : List OdomTok) (w : ListBlank (Fin 2)) (hcap : cap l = 0) :
    (cfg_L l w) [target]⊢⁺ cfg_R [] (drain l +> w) :=
  run_drain_aux l.length l w (Nat.le_refl _) hcap

/-! ## Hub Closure and `HasOdometerReduction` Proof -/

private def stepL_state (l : List OdomTok) (w : ListBlank (Fin 2)) :
    List OdomTok × ListBlank (Fin 2) :=
  if cap l ≥ 1 then (dec l, w) else ([], drain l +> w)

private theorem stepL_state_sound (l : List OdomTok) (w : ListBlank (Fin 2)) :
    (cfg_L l w) [target]⊢⁺ cfg_R (stepL_state l w).1 (stepL_state l w).2 := by
  unfold stepL_state
  split_ifs with hcap
  · exact runHL_dec l w hcap
  · exact run_drain l w (by omega)

private def nextOdom (s : List OdomTok × ListBlank (Fin 2)) :
    Option (List OdomTok × ListBlank (Fin 2)) :=
  let l := s.1
  let w := s.2
  if w.head = 0 then
    some (stepL_state l ((1 : Fin 2) >> w.tail))
  else if w.tail.head = 0 then
    if w.tail.tail.head = 0 then
      some (.L2 :: l, w.tail.tail.tail)
    else if w.tail.tail.tail.head = 0 then
      some (.L0 :: l, w.tail.tail.tail.tail)
    else
      none
  else
    if w.tail.tail.head = 0 then
      some (.L2 :: l, w.tail.tail.tail)
    else
      none

private theorem nextOdom_step (s : List OdomTok × ListBlank (Fin 2)) :
    match nextOdom s with
    | some s' => (cfg_R s.1 s.2) [target]⊢⁺ cfg_R s'.1 s'.2
    | none =>
      ∃ cfg_halt, ((cfg_R s.1 s.2) [target]⊢⁺ cfg_halt) ∧ (step target cfg_halt).isNone := by
  rcases s with ⟨l, w⟩
  unfold nextOdom
  dsimp only
  rcases fin2_cases w.head with h0 | h1
  · rw [ite_eq_left h0]; dsimp only
    have hw : w = (0 : Fin 2) >> w.tail := by
      conv_lhs => rw [← ListBlank.cons_head_tail w, h0]
    nth_rw 1 [hw]
    exact (step_R_0 l w.tail).trans (stepL_state_sound l ((1 : Fin 2) >> w.tail))
  · have h1_ne : w.head ≠ 0 := by rw [h1]; decide
    rw [ite_eq_right h1_ne]
    rcases fin2_cases w.tail.head with h10 | h11
    · rw [ite_eq_left h10]
      rcases fin2_cases w.tail.tail.head with h100 | h101
      · rw [ite_eq_left h100]; dsimp only
        have hw : w = (1 : Fin 2) >> 0 >> 0 >> w.tail.tail.tail := by
          conv_lhs =>
            rw [← ListBlank.cons_head_tail w, h1,
                ← ListBlank.cons_head_tail w.tail, h10,
                ← ListBlank.cons_head_tail w.tail.tail, h100]
        nth_rw 1 [hw]
        exact step_R_100 l w.tail.tail.tail
      · have h101_ne : w.tail.tail.head ≠ 0 := by rw [h101]; decide
        rw [ite_eq_right h101_ne]
        rcases fin2_cases w.tail.tail.tail.head with h1010 | h1011
        · rw [ite_eq_left h1010]; dsimp only
          have hw : w = (1 : Fin 2) >> 0 >> 1 >> 0 >> w.tail.tail.tail.tail := by
            conv_lhs =>
              rw [← ListBlank.cons_head_tail w, h1,
                  ← ListBlank.cons_head_tail w.tail, h10,
                  ← ListBlank.cons_head_tail w.tail.tail, h101,
                  ← ListBlank.cons_head_tail w.tail.tail.tail, h1010]
          nth_rw 1 [hw]
          exact step_R_1010 l w.tail.tail.tail.tail
        · have h1011_ne : w.tail.tail.tail.head ≠ 0 := by rw [h1011]; decide
          rw [ite_eq_right h1011_ne]; dsimp only
          have hw : w = (1 : Fin 2) >> 0 >> 1 >> 1 >> w.tail.tail.tail.tail := by
            conv_lhs =>
              rw [← ListBlank.cons_head_tail w, h1,
                  ← ListBlank.cons_head_tail w.tail, h10,
                  ← ListBlank.cons_head_tail w.tail.tail, h101,
                  ← ListBlank.cons_head_tail w.tail.tail.tail, h1011]
          nth_rw 1 [hw]
          exact step_R_1011_halt l w.tail.tail.tail.tail
    · have h11_ne : w.tail.head ≠ 0 := by rw [h11]; decide
      rw [ite_eq_right h11_ne]
      rcases fin2_cases w.tail.tail.head with h110 | h111
      · rw [ite_eq_left h110]; dsimp only
        have hw : w = (1 : Fin 2) >> 1 >> 0 >> w.tail.tail.tail := by
          conv_lhs =>
            rw [← ListBlank.cons_head_tail w, h1,
                ← ListBlank.cons_head_tail w.tail, h11,
                ← ListBlank.cons_head_tail w.tail.tail, h110]
        nth_rw 1 [hw]
        exact step_R_110 l w.tail.tail.tail
      · have h111_ne : w.tail.tail.head ≠ 0 := by rw [h111]; decide
        rw [ite_eq_right h111_ne]; dsimp only
        have hw : w = (1 : Fin 2) >> 1 >> 1 >> w.tail.tail.tail := by
          conv_lhs =>
            rw [← ListBlank.cons_head_tail w, h1,
                ← ListBlank.cons_head_tail w.tail, h11,
                ← ListBlank.cons_head_tail w.tail.tail, h111]
        nth_rw 1 [hw]
        exact step_R_111_halt l w.tail.tail.tail

private theorem step_R_partition (l : List OdomTok) (w : ListBlank (Fin 2)) :
    (∃ t w', (cfg_R l w) [target]⊢⁺ cfg_R (t :: l) w') ∨
    (∃ w', (cfg_R l w) [target]⊢⁺ cfg_L l w') ∨
    (∃ cfg', ((cfg_R l w) [target]⊢⁺ cfg') ∧ (step target cfg').isNone) := by
  have hw0 : w = w.head >> w.tail := (ListBlank.cons_head_tail w).symm
  rw [hw0]
  rcases fin2_cases w.head with h0 | h1
  · rw [h0]
    exact Or.inr (Or.inl ⟨(1 : Fin 2) >> w.tail, step_R_0 l w.tail⟩)
  · rw [h1]
    have hw1 : w.tail = w.tail.head >> w.tail.tail := (ListBlank.cons_head_tail w.tail).symm
    rw [hw1]
    rcases fin2_cases w.tail.head with h10 | h11
    · rw [h10]
      have hw2 : w.tail.tail = w.tail.tail.head >> w.tail.tail.tail :=
        (ListBlank.cons_head_tail w.tail.tail).symm
      rw [hw2]
      rcases fin2_cases w.tail.tail.head with h100 | h101
      · rw [h100]
        exact Or.inl ⟨.L2, w.tail.tail.tail, step_R_100 l w.tail.tail.tail⟩
      · rw [h101]
        have hw3 : w.tail.tail.tail = w.tail.tail.tail.head >> w.tail.tail.tail.tail :=
          (ListBlank.cons_head_tail w.tail.tail.tail).symm
        rw [hw3]
        rcases fin2_cases w.tail.tail.tail.head with h1010 | h1011
        · rw [h1010]
          exact Or.inl ⟨.L0, w.tail.tail.tail.tail, step_R_1010 l w.tail.tail.tail.tail⟩
        · rw [h1011]
          exact Or.inr (Or.inr (step_R_1011_halt l w.tail.tail.tail.tail))
    · rw [h11]
      have hw2 : w.tail.tail = w.tail.tail.head >> w.tail.tail.tail :=
        (ListBlank.cons_head_tail w.tail.tail).symm
      rw [hw2]
      rcases fin2_cases w.tail.tail.head with h110 | h111
      · rw [h110]
        exact Or.inl ⟨.L2, w.tail.tail.tail, step_R_110 l w.tail.tail.tail⟩
      · rw [h111]
        exact Or.inr (Or.inr (step_R_111_halt l w.tail.tail.tail))

private theorem step_R_closed (l : List OdomTok) (w : ListBlank (Fin 2)) :
    ∃ cfg', ((cfg_R l w) [target]⊢⁺ cfg') ∧
      (IsInOdomSystem cfg' ∨ (step target cfg').isNone) := by
  rcases hnext : nextOdom (l, w) with _ | ⟨l', w'⟩
  · have hs := nextOdom_step (l, w)
    rw [hnext] at hs
    rcases hs with ⟨cfg_halt, hh, hnone⟩
    exact ⟨cfg_halt, hh, Or.inr hnone⟩
  · have hs := nextOdom_step (l, w)
    rw [hnext] at hs
    exact ⟨cfg_R l' w', hs, Or.inl ⟨l', w', rfl⟩⟩

/-- `target` satisfies `HasOdometerReduction`. -/
theorem has_odometer_reduction : HasOdometerReduction target := by
  refine ⟨OdomTok, .leftOdom, (fun _ => 2), 0, [0], [0], [1], odomWord, encOdom, cap, dec,
    (fun _ => []), drain, IsInOdomSystem, ?_, ?_, ?_, rfl, ?_, encOdom_non_surjective, rfl, ?_,
    length_dec, cap_dec, runHL_dec, (fun stk _ => drain_ne_nil stk), run_drain,
    step_R_0, (fun stk w _ => step_R_partition stk w), (fun _ => Iff.rfl),
    ⟨cfg_R [] default, step_init, ⟨[], default, rfl⟩⟩, (fun stk w _ => step_R_closed stk w)⟩
  · refine ⟨[.L0, .L1, .L2], by decide, by decide, ?_⟩
    intro t; cases t <;> decide
  · decide
  · intro t; cases t <;> decide
  · intro t stk; rfl
  · refine ⟨.L0, .L1, .L2, 2, [1, 0, 1, 0], [1, 0, 0],
      by decide, by decide, by decide, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
      step_R_1010, step_R_100⟩

end BusyBeaver.M_1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RCHHH
