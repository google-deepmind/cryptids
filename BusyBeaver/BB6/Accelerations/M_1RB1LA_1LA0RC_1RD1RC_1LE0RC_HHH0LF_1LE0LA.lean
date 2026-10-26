/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $D(1, 0, [], [])$ in 7 raw steps, where:
- $D(a, b, L, R)$ has state `D` reading `0` between `encStack (a :: b :: L)` and `encStack R`.
- $E(a, L, R)$ has state `<E` reading `10` on the left of `encStack (a :: L)` and `encStack R`.

## Accelerated Transition Rules

```text
sweepD(a, b, L, [])     = D(a, b, L, [])
sweepD(a, b, L, d :: R) = sweepD(d, a, b :: L, R)

D(2k, b, L, [])         -> E(b + k, L, [k])
D(2k, b, L, d :: R)     -> E(b + k, L, (d + k + 1) :: R)
D(2k + 1, b, L, [])     -> D(k, b + k + 2, bumpHead L, [])
D(2k + 1, b, L, d :: R) -> sweepD(d + k + 1, b + k + 2, bumpHead L, R)
E(0, [], R)             -> Halt
E(0, b :: L, R)         -> E(b, L, 0 :: R)
E(1, [], R)             -> sweepD(0, 1, [0], R)
E(1, b :: L, R)         -> sweepD(0, b + 2, bumpHead L, R)
E(a + 2, [], R)         -> D(a, 0, [], 0 :: R)
E(a + 2, b :: L, R)     -> D(a, b + 1, L, 0 :: R)

Start: D(1, 0, [], []), reached after 7 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1LA0RC_1RD1RC_1LE0RC_---0LF_1LE0LA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Separator configuration `D(a, b, L, R)`: state `D` on `0` between `a :: b :: L` and `R`. -/
  | D (a b : ℕ) (L R : List ℕ)
  /-- Separator configuration `E(a, L, R)`: state `<E` reading `10` over `a :: L` and `R`. -/
  | E (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep all digits of `R` onto `a :: b :: L`, entering `D(..., [])` at the right blank. -/
def sweepD (a b : ℕ) (L R : List ℕ) : State :=
  let t := R.foldl (fun t d => (d, t.1, t.2.1 :: t.2.2)) (a, b, L)
  .D t.1 t.2.1 t.2.2 []

/-- Initial symbolic state `D(1, 0, [], [])`, reached from `init []` in 7 raw steps. -/
def start : State := .D 1 0 [] []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b L R =>
    Cfg.headRight D (encStack (a :: b :: L)) (ListBlank.cons 0 (encStack R))
  | .E a L R =>
    Cfg.headLeft E (ListBlank.append [1, 0] (encStack (a :: L))) (encStack R)

/-- Accelerated transition function (`none` indicates halting, reached only at `E(0, [], R)`). -/
def next : State → Option State
  | .D a b L R =>
    let k := a / 2
    if a % 2 = 0 then
      List.casesOn R (some (.E (b + k) L [k]))
        fun d R' => some (.E (b + k) L ((d + k + 1) :: R'))
    else
      List.casesOn R (some (.D k (b + k + 2) (bumpHead L) []))
        fun d R' => some (sweepD (d + k + 1) (b + k + 2) (bumpHead L) R')
  | .E 0 [] _ => none
  | .E 0 (b :: L) R => some (.E b L (0 :: R))
  | .E 1 [] R => some (sweepD 0 1 [0] R)
  | .E 1 (b :: L) R => some (sweepD 0 (b + 2) (bumpHead L) R)
  | .E (a + 2) [] R => some (.D a 0 [] (0 :: R))
  | .E (a + 2) (b :: L) R => some (.D a (b + 1) L (0 :: R))

/-! ## Stack Encoding and Sweep Helpers -/

private theorem encStack_cons_one (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

private theorem sweep_A (k : ℕ) (l r : ListBlank (Fin 2)) :
    (((l <+ (([1] : List (Fin 2)) ^ k))) <{{A}} r) [target]⊢*
      (l <{{A}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{A}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{A}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem sweep_C (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{C}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{C}}> r) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        (l {{C}}> ((([1] : List (Fin 2)) ^ (k + 1)) +> r)) [target]⊢⁺
          (([1] +> l) {{C}}> ((([1] : List (Fin 2)) ^ k) +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l) r
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Local Rules -/

private def cfgDR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encStack L) {{D}}> (encStack R)

private def cfgD (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgE (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encStack L) <{{E}} (encStack R)

private def cfgEL10 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft E (ListBlank.append [1, 0] (encStack L)) (encStack R)

private theorem step_D_to_E (L R : List ℕ) :
    (cfgD L R) [target]⊢⁺ (cfgE L (bumpHead R)) := by
  unfold cfgD cfgE
  rw [← encStack_cons_one]
  bb_steps

private theorem step_EL10_to_E (L R : List ℕ) :
    (cfgEL10 L R) [target]⊢⁺ (cfgE L (0 :: R)) := by
  unfold cfgEL10 cfgE
  simp only [encStack, Nat.zero_add, list_pow_one]
  bb_steps

private theorem rule_E_one_nil (R : List ℕ) :
    (cfgE [1] R) [target]⊢⁺ (cfgDR [1, 0] R) := by
  unfold cfgE cfgDR
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_E_one_cons (a : ℕ) (L R : List ℕ) :
    (cfgE (1 :: a :: L) R) [target]⊢⁺ (cfgDR ((a + 2) :: bumpHead L) R) := by
  unfold cfgE cfgDR
  have h_pre :
      ((encStack (1 :: a :: L)) <{{E}} (encStack R)) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <{{A}}
          (([1, 1] : List (Fin 2)) +> ((encStack R).cons 0))) := by
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have h_swA :=
    sweep_A (a + 1) ((encStack L).cons 0) (([1, 1] : List (Fin 2)) +> ((encStack R).cons 0))
  have h_mid :
      (((encStack L).cons 0) <{{A}}
        ((([1] : List (Fin 2)) ^ (a + 1)) +>
          (([1, 1] : List (Fin 2)) +> ((encStack R).cons 0)))) [target]⊢⁺
        (((encStack (bumpHead L)).cons 0) {{C}}>
          ((([1] : List (Fin 2)) ^ (a + 2)) +> ((encStack R).cons 0))) := by
    have hr :
        ((([1] : List (Fin 2)) ^ (a + 1)) +>
          (([1, 1] : List (Fin 2)) +> ((encStack R).cons 0))) =
          [1] +> ((([1] : List (Fin 2)) ^ (a + 2)) +> ((encStack R).cons 0)) := by
      have h2 : ([1, 1] : List (Fin 2)) = ([1] : List (Fin 2)) ^ 2 := rfl
      rw [h2, ← ListBlank.append_pow_add, show a + 1 + 2 = 1 + (a + 2) by omega,
        ListBlank.append_pow_add, list_pow_one]
    rw [hr, ← encStack_cons_one]
    bb_steps
  have h_swC := sweep_C (a + 2) ((encStack (bumpHead L)).cons 0) ((encStack R).cons 0)
  have h_post :
      ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 2))) {{C}}>
        ((encStack R).cons 0)) [target]⊢⁺
        ((encStack ((a + 2) :: bumpHead L)) {{D}}> (encStack R)) := by
    simp only [encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (((h_pre.trans_star h_swA).trans h_mid).trans_star h_swC).trans h_post

private theorem rule_E_ge2 (a : ℕ) (L R : List ℕ) :
    (cfgE ((a + 2) :: L) R) [target]⊢⁺ (cfgD (a :: bumpHead L) R) := by
  unfold cfgE cfgD
  have h_pre :
      ((encStack ((a + 2) :: L)) <{{E}} (encStack R)) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <{{A}}
          (((encStack R).cons 0).cons 0)) := by
    simp only [encStack]
    rw [show a + 2 + 1 = 2 + (a + 1) by omega, ListBlank.append_pow_add]
    change (([1, 1] +> (([1] ^ (a + 1)) +> ((encStack L).cons 0))) <{{E}} (encStack R)) [target]⊢⁺ _
    bb_steps
  have h_swA := sweep_A (a + 1) ((encStack L).cons 0) (((encStack R).cons 0).cons 0)
  have h_mid :
      (((encStack L).cons 0) <{{A}}
        ((([1] : List (Fin 2)) ^ (a + 1)) +> (((encStack R).cons 0).cons 0))) [target]⊢⁺
        (((encStack (bumpHead L)).cons 0) {{C}}>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack R).cons 0).cons 0))) := by
    rw [ListBlank.append_pow_succ, ← encStack_cons_one]
    bb_steps
  have h_swC := sweep_C a ((encStack (bumpHead L)).cons 0) (((encStack R).cons 0).cons 0)
  have h_post :
      ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ a)) {{C}}>
        (((encStack R).cons 0).cons 0)) [target]⊢⁺
        Cfg.headRight D (encStack (a :: bumpHead L)) (ListBlank.cons 0 (encStack R)) := by
    simp only [encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (((h_pre.trans_star h_swA).trans h_mid).trans_star h_swC).trans h_post

private theorem rule_DR_cons (d : ℕ) (L R : List ℕ) :
    (cfgDR L (d :: R)) [target]⊢⁺ (cfgDR (d :: L) R) := by
  unfold cfgDR
  have h_pre :
      ((encStack L) {{D}}> (encStack (d :: R))) [target]⊢⁺
        (((encStack L).cons 0) {{C}}> ((([1] : List (Fin 2)) ^ d) +> ((encStack R).cons 0))) := by
    simp only [encStack]
    rw [ListBlank.append_pow_succ]
    bb_steps
  have h_swC := sweep_C d ((encStack L).cons 0) ((encStack R).cons 0)
  have h_post :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ d)) {{C}}> ((encStack R).cons 0))
        [target]⊢⁺ ((encStack (d :: L)) {{D}}> (encStack R)) := by
    simp only [encStack]
    rw [ListBlank.append_pow_succ]
    bb_steps
  exact (h_pre.trans_star h_swC).trans h_post

/-! ## Multi-Step Sweep and Parity Peel Contractions -/

private theorem reaches_sweepD (a b : ℕ) (L R : List ℕ) :
    (cfgDR (a :: b :: L) R) [target]⊢* (encode (sweepD a b L R)) := by
  induction R generalizing a b L with
  | nil =>
    simp only [sweepD, List.foldl_nil, cfgDR, encode, encStack]
    bb_refl
  | cons d R ih =>
    exact (rule_DR_cons d (a :: b :: L) R).to_star.trans (ih d a (b :: L))

private theorem rule_D_ge2 (a : ℕ) (L R : List ℕ) :
    (cfgD ((a + 2) :: L) R) [target]⊢⁺ (cfgD (a :: bumpHead L) (bumpHead R)) :=
  (step_D_to_E ((a + 2) :: L) R).trans (rule_E_ge2 a L (bumpHead R))

private theorem rule_D_ge2_iter (k a b : ℕ) (L R : List ℕ) :
    (cfgD ((2 * k + a) :: b :: L) R) [target]⊢*
      (cfgD (a :: (b + k) :: L) (bumpHead^[k] R)) := by
  induction k generalizing b R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Function.iterate_zero_apply]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [show 2 * (k + 1) + a = (2 * k + a) + 2 by omega, Function.iterate_succ_apply]
    have h1 := rule_D_ge2 (2 * k + a) (b :: L) R
    dsimp only [bumpHead] at h1
    have h2 := ih (b + 1) (bumpHead R)
    rw [show b + 1 + k = b + (k + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

private theorem bumpHead_iter_nil (k : ℕ) :
    bumpHead (bumpHead^[k] []) = [k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

private theorem bumpHead_iter_cons (k d : ℕ) (R : List ℕ) :
    bumpHead (bumpHead^[k] (d :: R)) = (d + k + 1) :: R := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, bumpHead, ih (d + 1)]
    congr 1
    omega

private theorem encStack_zero_cons (s : List ℕ) :
    encStack (0 :: s) = ListBlank.append [1, 0] (encStack s) := by
  simp [encStack]

private theorem step_D_even (k b : ℕ) (L R : List ℕ) :
    (cfgD ((2 * k) :: b :: L) R) [target]⊢⁺
      (cfgEL10 ((b + k) :: L) (bumpHead (bumpHead^[k] R))) := by
  have h1 := rule_D_ge2_iter k 0 b L R
  rw [Nat.add_zero] at h1
  have h2 :
      (cfgD (0 :: (b + k) :: L) (bumpHead^[k] R)) [target]⊢⁺
        (cfgEL10 ((b + k) :: L) (bumpHead (bumpHead^[k] R))) := by
    have hs := step_D_to_E (0 :: (b + k) :: L) (bumpHead^[k] R)
    simpa only [cfgE, cfgEL10, encStack_zero_cons] using hs
  exact h1.trans_plus h2

private theorem step_D_odd (k b : ℕ) (L R : List ℕ) :
    (cfgD ((2 * k + 1) :: b :: L) R) [target]⊢⁺
      (cfgDR ((b + k + 2) :: bumpHead L) (bumpHead (bumpHead^[k] R))) := by
  have h1 := rule_D_ge2_iter k 1 b L R
  have h2 :=
    (step_D_to_E (1 :: (b + k) :: L) (bumpHead^[k] R)).trans
      (rule_E_one_cons (b + k) L (bumpHead (bumpHead^[k] R)))
  exact h1.trans_plus h2

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

private theorem halt_E_zero_nil (R : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.E 0 [] R)) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight E default (ListBlank.cons 0 (encStack (0 :: 0 :: R))), ?_, ?_⟩
  · have h :
        ReachesPlus target (encode (.E 0 [] R))
          (Cfg.headRight E default (ListBlank.cons 0 (encStack (0 :: 0 :: R)))) := by
      simp only [encode, encStack, Nat.zero_add, list_pow_one]
      bb_steps
    exact h.to_star
  · bb_halt

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  rcases s with ⟨a, b, L, R⟩ | ⟨a, L, R⟩
  · by_cases hev : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases R with _ | ⟨d, R'⟩
      · simp only [next, hev, ↓reduceIte, encode]
        have h := step_D_even (a / 2) b L []
        rw [← ha, bumpHead_iter_nil] at h
        exact h
      · simp only [next, hev, ↓reduceIte, encode]
        have h := step_D_even (a / 2) b L (d :: R')
        rw [← ha, bumpHead_iter_cons] at h
        exact h
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases R with _ | ⟨d, R'⟩
      · simp only [next, hev, ↓reduceIte, encode]
        have h1 := step_D_odd (a / 2) b L []
        rw [← ha, bumpHead_iter_nil] at h1
        have h2 := rule_DR_cons (a / 2) ((b + a / 2 + 2) :: bumpHead L) []
        unfold cfgD at h1
        simpa only [cfgDR, encStack, ListBlank.cons_zero_default] using h1.trans h2
      · simp only [next, hev, ↓reduceIte]
        have h1 := step_D_odd (a / 2) b L (d :: R')
        rw [← ha, bumpHead_iter_cons] at h1
        have h2 := rule_DR_cons (d + a / 2 + 1) ((b + a / 2 + 2) :: bumpHead L) R'
        have h3 := reaches_sweepD (d + a / 2 + 1) (b + a / 2 + 2) (bumpHead L) R'
        exact (h1.trans h2).trans_star h3
  · rcases a with _ | _ | a
    · rcases L with _ | ⟨b, L'⟩
      · exact halt_E_zero_nil R
      · simp only [next, encode]
        have h := step_EL10_to_E (0 :: b :: L') R
        simpa only [cfgEL10, cfgE, encStack_zero_cons] using h
    · rcases L with _ | ⟨b, L'⟩
      · simp only [next]
        have h1 := (step_EL10_to_E [1] R).trans (rule_E_one_nil (0 :: R))
        have h2 := rule_DR_cons 0 [1, 0] R
        have h3 := reaches_sweepD 0 1 [0] R
        exact (h1.trans h2).trans_star h3
      · simp only [next]
        have h1 := (step_EL10_to_E (1 :: b :: L') R).trans (rule_E_one_cons b L' (0 :: R))
        have h2 := rule_DR_cons 0 ((b + 2) :: bumpHead L') R
        have h3 := reaches_sweepD 0 (b + 2) (bumpHead L') R
        exact (h1.trans h2).trans_star h3
    · rcases L with _ | ⟨b, L'⟩
      · simp only [next, encode]
        exact (step_EL10_to_E [a + 2] R).trans (rule_E_ge2 a [] (0 :: R))
      · simp only [next, encode]
        exact (step_EL10_to_E ((a + 2) :: b :: L') R).trans (rule_E_ge2 a (b :: L') (0 :: R))

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LA_1LA0RC_1RD1RC_1LE0RC_HHH0LF_1LE0LA
