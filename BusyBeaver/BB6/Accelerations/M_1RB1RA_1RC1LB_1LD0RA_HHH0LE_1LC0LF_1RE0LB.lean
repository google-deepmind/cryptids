/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB`.

Left stack `encStack` encodes digits as `1^{a+1} 0 ...`, and right stack `encStack2` encodes digits
as `1^{d+1} 00 ...`, ordered from the tape head outward. Starting from `init []`, the machine
reaches $C(3, [0], [])$ in 19 raw steps, where $C(a, L, R)$ has state `C` reading `0` between
`encStack (a :: L)` and `(encStack2 R).tail`.

## Accelerated Transition Rules

```text
transferB([], [])      = C(0, [], [])
transferB(a :: L, [])  = C(a + 1, L, [])
transferB(L, d :: R)   = transferB(d :: bumpHead L, R)

r := R.headD 0, R' := R.tail

C(0, [], R)            -> Halt
C(0, 0 :: L, R)        -> transferB((r + 2) :: 0 :: L, R')
C(0, (b + 1) :: L, R)  -> transferB(b :: L, (r + 2) :: R')
C(2k + 1, L, R)        -> transferB(bumpHead^[k] L, (r + k + 2) :: R')
C(2k + 2, [], R)       -> C(k, [], 0 :: (r + k) :: R')
C(2k + 2, b :: L, R)   -> C(b + k + 1, L, 0 :: (r + k) :: R')

Start: C(3, [0], []), reached after 19 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1RC1LB_1LD0RA_---0LE_1LC0LF_1RE0LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- Separator configuration `C(a, L, R)`: state `C` reading `0` over `a :: L` and `R`. -/
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Sweep all digits of `R` onto `L` in state `B` and turn around at the right blank into `C`. -/
def transferB : List ℕ → List ℕ → State
  | [], [] => .C 0 [] []
  | a :: L, [] => .C (a + 1) L []
  | L, d :: R => transferB (d :: bumpHead L) R

/-- Initial symbolic state `C(3, [0], [])`, reached from `init []` in 19 raw steps. -/
def start : State := .C 3 [0] []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack (a :: L)) (ListBlank.cons 0 (encStack2 R).tail)

/-- Accelerated transition function (`none` indicates halting, reached only at `C(0, [], R)`). -/
def next : State → Option State
  | .C 0 [] _ => none
  | .C 0 (0 :: L) R => some (transferB ((R.headD 0 + 2) :: 0 :: L) R.tail)
  | .C 0 ((b + 1) :: L) R => some (transferB (b :: L) ((R.headD 0 + 2) :: R.tail))
  | .C (a + 1) L R =>
    let k := a / 2
    let r := R.headD 0
    if a % 2 = 0 then
      some (transferB (bumpHead^[k] L) ((r + k + 2) :: R.tail))
    else
      List.casesOn L (some (.C k [] (0 :: (r + k) :: R.tail)))
        fun b L' => some (.C (b + k + 1) L' (0 :: (r + k) :: R.tail))

/-! ## Stack Encoding and Sweep Helpers -/

private theorem encStack_cons_one (L : List ℕ) :
    ListBlank.cons 1 (encStack L) = encStack (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack]
  | cons a L' => rfl

private theorem encStack2_tail_cons_one (R : List ℕ) :
    ListBlank.cons 1 (encStack2 R).tail = encStack2 (R.headD 0 :: R.tail) := by
  cases R with
  | nil => simp [encStack2]
  | cons d R' =>
    simp only [List.headD_cons, List.tail_cons, encStack2, ListBlank.append_pow_succ,
      ListBlank.append_cons, ListBlank.append_nil, ListBlank.tail_cons]

private theorem encStack2_tail_decomp (R : List ℕ) :
    (encStack2 R).tail =
      ListBlank.append (([1] : List (Fin 2)) ^ R.headD 0)
        (ListBlank.cons 0 (ListBlank.cons 0 (encStack2 R.tail))) := by
  cases R with
  | nil => simp [encStack2]
  | cons d R' =>
    simp only [List.headD_cons, List.tail_cons, encStack2, ListBlank.append_pow_succ,
      ListBlank.append_cons, ListBlank.append_nil, ListBlank.tail_cons]

private theorem encStack2_zero_cons_tail (s : List ℕ) :
    (encStack2 (0 :: s)).tail = ListBlank.cons 0 (ListBlank.cons 0 (encStack2 s)) := by
  simp [encStack2]

private theorem walk_A (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        (l {{A}}> ((([1] : List (Fin 2)) ^ (k + 1)) +> r)) [target]⊢⁺
          (([1] +> l) {{A}}> ((([1] : List (Fin 2)) ^ k) +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l) r
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem walk_B (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} r) [target]⊢*
      (l <{{B}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{B}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{B}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Local Rules -/

private def cfgB (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack2 R))

private def cfgCR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L) (ListBlank.cons 0 (encStack2 R).tail)

private theorem cfgCR_norm (L R : List ℕ) :
    cfgCR L R = cfgCR L (R.headD 0 :: R.tail) := by
  cases R with
  | nil => simp [cfgCR, encStack2]
  | cons d R' => rfl

private theorem c_sweep_right (K R : List ℕ) (d : ℕ) :
    (Cfg.headRight C (encStack K)
      (ListBlank.cons 1
        ((([1] : List (Fin 2)) ^ d) +> (((encStack2 R).cons 0).cons 0)))) [target]⊢⁺
      (cfgB (d :: K) R) := by
  unfold cfgB
  have h_pre :
      (Cfg.headRight C (encStack K)
        (ListBlank.cons 1
          ((([1] : List (Fin 2)) ^ d) +> (((encStack2 R).cons 0).cons 0)))) [target]⊢⁺
        (((encStack K).cons 0) {{A}}>
          ((([1] : List (Fin 2)) ^ d) +> (((encStack2 R).cons 0).cons 0))) := by
    bb_steps
  have h_sw := walk_A d ((encStack K).cons 0) (((encStack2 R).cons 0).cons 0)
  have h_post :
      ((((encStack K).cons 0) <+ (([1] : List (Fin 2)) ^ d)) {{A}}>
        (((encStack2 R).cons 0).cons 0)) [target]⊢⁺
        Cfg.headRight B (encStack (d :: K)) (ListBlank.cons 0 (encStack2 R)) := by
    simp only [encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (h_pre.trans_star h_sw).trans h_post

private theorem rule_B_nil (L : List ℕ) :
    (cfgB L []) [target]⊢⁺ (cfgCR (bumpHead L) []) := by
  unfold cfgB cfgCR
  simp only [encStack2]
  rw [← encStack_cons_one L]
  bb_steps

private theorem rule_B_cons (d : ℕ) (L R : List ℕ) :
    (cfgB L (d :: R)) [target]⊢⁺ (cfgB (d :: bumpHead L) R) := by
  have h1 :
      (cfgB L (d :: R)) [target]⊢⁺
        Cfg.headRight C (encStack (bumpHead L))
          (ListBlank.cons 1
            ((([1] : List (Fin 2)) ^ d) +> (((encStack2 R).cons 0).cons 0))) := by
    unfold cfgB
    simp only [encStack2, ListBlank.append_pow_succ]
    rw [← encStack_cons_one L]
    bb_steps
  exact h1.trans (c_sweep_right (bumpHead L) R d)

private theorem reaches_transferB (L R : List ℕ) :
    (cfgB L R) [target]⊢⁺ (encode (transferB L R)) := by
  induction R generalizing L with
  | nil =>
    cases L with
    | nil =>
      simpa only [transferB, bumpHead, encode, cfgCR] using rule_B_nil []
    | cons a L' =>
      simpa only [transferB, bumpHead, encode, cfgCR] using rule_B_nil (a :: L')
  | cons d R ih =>
    simp only [transferB]
    exact (rule_B_cons d L R).trans (ih (d :: bumpHead L))

private theorem halt_CR_zero_nil (R : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.C 0 [] R)) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight D default
    (ListBlank.cons 0
      (ListBlank.append [1, 1, 0] (encStack2 (R.headD 0 :: R.tail)))), ?_, ?_⟩
  · have h :
        ReachesPlus target (encode (.C 0 [] R))
          (Cfg.headRight D default
            (ListBlank.cons 0
              (ListBlank.append [1, 1, 0] (encStack2 (R.headD 0 :: R.tail))))) := by
      simp only [encode, encStack, Nat.zero_add, list_pow_one]
      rw [← encStack2_tail_cons_one R]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_CR_zero_zero (L R : List ℕ) :
    (cfgCR (0 :: 0 :: L) R) [target]⊢⁺ (cfgB ((R.headD 0 + 2) :: 0 :: L) R.tail) := by
  have h1 :
      (cfgCR (0 :: 0 :: L) R) [target]⊢⁺
        Cfg.headRight C (encStack (0 :: L))
          (ListBlank.cons 1
            ((([1] : List (Fin 2)) ^ (R.headD 0 + 2)) +>
              (((encStack2 R.tail).cons 0).cons 0))) := by
    unfold cfgCR
    rw [encStack2_tail_decomp R]
    simp only [encStack, Nat.zero_add, list_pow_one]
    rw [show R.headD 0 + 2 = 2 + R.headD 0 by omega, ListBlank.append_pow_add]
    change _ [target]⊢⁺
      Cfg.headRight C _
        (ListBlank.cons 1 ([1, 1] +> ((([1] ^ R.headD 0) +> _))))
    bb_steps
  exact h1.trans (c_sweep_right (0 :: L) R.tail (R.headD 0 + 2))

private theorem rule_CR_zero_succ (b : ℕ) (L R : List ℕ) :
    (cfgCR (0 :: (b + 1) :: L) R) [target]⊢⁺ (cfgB (b :: L) ((R.headD 0 + 2) :: R.tail)) := by
  have h1 :
      (cfgCR (0 :: (b + 1) :: L) R) [target]⊢⁺
        Cfg.headRight A (encStack (0 :: b :: L))
          (ListBlank.cons 0 (encStack2 (R.headD 0 :: R.tail))) := by
    unfold cfgCR
    simp only [encStack, Nat.zero_add, list_pow_one]
    rw [ListBlank.append_pow_succ, ← encStack2_tail_cons_one R]
    bb_steps
  have h2 :
      (Cfg.headRight A (encStack (0 :: b :: L))
        (ListBlank.cons 0 (encStack2 (R.headD 0 :: R.tail)))) [target]⊢⁺
        (cfgB (b :: L) ((R.headD 0 + 2) :: R.tail)) := by
    unfold cfgB
    simp only [encStack, encStack2, Nat.zero_add, list_pow_one]
    rw [show R.headD 0 + 2 + 1 = 3 + R.headD 0 by omega,
      ListBlank.append_pow_add _ 3 (R.headD 0),
      ListBlank.append_pow_succ _ (R.headD 0)]
    change _ [target]⊢⁺
      Cfg.headRight B _ (ListBlank.cons 0 ([1, 1, 1] +> _))
    bb_steps
  exact h1.trans h2

private theorem rule_CR_one (L R : List ℕ) :
    (cfgCR (1 :: L) R) [target]⊢⁺ (cfgB L ((R.headD 0 + 2) :: R.tail)) := by
  have h1 :
      (cfgCR (1 :: L) R) [target]⊢⁺
        Cfg.headRight A (encStack (0 :: L))
          (ListBlank.cons 0 (encStack2 (R.headD 0 :: R.tail))) := by
    unfold cfgCR
    simp only [encStack, list_pow_succ, list_pow_zero, Nat.zero_add]
    rw [← encStack2_tail_cons_one R]
    bb_steps
  have h2 :
      (Cfg.headRight A (encStack (0 :: L))
        (ListBlank.cons 0 (encStack2 (R.headD 0 :: R.tail)))) [target]⊢⁺
        (cfgB L ((R.headD 0 + 2) :: R.tail)) := by
    unfold cfgB
    simp only [encStack, encStack2, Nat.zero_add, list_pow_one]
    rw [show R.headD 0 + 2 + 1 = 3 + R.headD 0 by omega,
      ListBlank.append_pow_add _ 3 (R.headD 0),
      ListBlank.append_pow_succ _ (R.headD 0)]
    change _ [target]⊢⁺
      Cfg.headRight B _ (ListBlank.cons 0 ([1, 1, 1] +> _))
    bb_steps
  exact h1.trans h2

private theorem rule_CR_two (L R : List ℕ) :
    (cfgCR (2 :: L) R) [target]⊢⁺ (cfgCR (bumpHead L) (0 :: R.headD 0 :: R.tail)) := by
  unfold cfgCR
  rw [encStack2_zero_cons_tail, ← encStack2_tail_cons_one R, ← encStack_cons_one L]
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem c_ge3_gen (L : List ℕ) (a : ℕ) (r : ListBlank (Fin 2)) :
    (Cfg.headRight C (encStack ((a + 3) :: L)) (ListBlank.cons 0 r)) [target]⊢⁺
      (Cfg.headRight C (encStack ((a + 1) :: bumpHead L))
        (ListBlank.cons 0 (ListBlank.cons 1 r))) := by
  have h_pre :
      (Cfg.headRight C (encStack ((a + 3) :: L)) (ListBlank.cons 0 r)) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1))) <{{B}}
          ([0, 0, 0, 1] +> r)) := by
    simp only [encStack]
    rw [show a + 3 + 1 = 3 + (a + 1) by omega, ListBlank.append_pow_add]
    change (Cfg.headRight C ([1, 1, 1] +> _) _) [target]⊢⁺ _
    bb_steps
  have h_swB := walk_B (a + 1) ((encStack L).cons 0) ([0, 0, 0, 1] +> r)
  have h_mid :
      (((encStack L).cons 0) <{{B}}
        ((([1] : List (Fin 2)) ^ (a + 1)) +> ([0, 0, 0, 1] +> r))) [target]⊢⁺
        (((encStack (bumpHead L)).cons 0) {{A}}>
          ((([1] : List (Fin 2)) ^ a) +> ([0, 0, 0, 1] +> r))) := by
    rw [ListBlank.append_pow_succ, ← encStack_cons_one L]
    bb_steps
  have h_swA := walk_A a ((encStack (bumpHead L)).cons 0) ([0, 0, 0, 1] +> r)
  have h_post :
      ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ a)) {{A}}>
        ([0, 0, 0, 1] +> r)) [target]⊢⁺
        Cfg.headRight C (encStack ((a + 1) :: bumpHead L))
          (ListBlank.cons 0 (ListBlank.cons 1 r)) := by
    simp only [encStack]
    rw [show a + 1 + 1 = 2 + a by omega, ListBlank.append_pow_add]
    change _ [target]⊢⁺ Cfg.headRight C ([1, 1] +> _) _
    bb_steps
  exact (((h_pre.trans_star h_swB).trans h_mid).trans_star h_swA).trans h_post

private theorem rule_CR_ge3 (a : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (cfgCR ((a + 3) :: L) (r :: R)) [target]⊢⁺
      (cfgCR ((a + 1) :: bumpHead L) ((r + 1) :: R)) := by
  unfold cfgCR
  have hr : ListBlank.cons 1 (encStack2 (r :: R)).tail = (encStack2 ((r + 1) :: R)).tail := by
    simp only [encStack2, ListBlank.append_pow_succ, ListBlank.append_cons,
      ListBlank.append_nil, ListBlank.tail_cons]
  rw [← hr]
  exact c_ge3_gen L a (encStack2 (r :: R)).tail

private theorem rule_CR_ge3_iter (k a : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (cfgCR ((2 * k + a + 1) :: L) (r :: R)) [target]⊢*
      (cfgCR ((a + 1) :: bumpHead^[k] L) ((r + k) :: R)) := by
  induction k generalizing L r with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, Function.iterate_zero_apply]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [show 2 * (k + 1) + a + 1 = (2 * k + a) + 3 by omega, Function.iterate_succ_apply]
    have h1 := rule_CR_ge3 (2 * k + a) L r R
    have h2 := ih (bumpHead L) (r + 1)
    rw [show r + 1 + k = r + (k + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

private theorem bumpHead_iter_nil (k : ℕ) :
    bumpHead (bumpHead^[k] []) = [k] := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rfl

private theorem bumpHead_iter_cons (k b : ℕ) (L : List ℕ) :
    bumpHead (bumpHead^[k] (b :: L)) = (b + k + 1) :: L := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, bumpHead, ih (b + 1)]
    congr 1
    omega

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, encStack2, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  rcases s with ⟨_ | a, L, R⟩
  · rcases L with _ | ⟨_ | b, L'⟩
    · exact halt_CR_zero_nil R
    · simp only [next]
      exact (rule_CR_zero_zero L' R).trans (reaches_transferB ((R.headD 0 + 2) :: 0 :: L') R.tail)
    · simp only [next]
      exact (rule_CR_zero_succ b L' R).trans
        (reaches_transferB (b :: L') ((R.headD 0 + 2) :: R.tail))
  · by_cases hev : a % 2 = 0
    · have ha : a + 1 = 2 * (a / 2) + 0 + 1 := by omega
      simp only [next, hev, ↓reduceIte]
      have h0 : encode (.C (a + 1) L R) = cfgCR ((a + 1) :: L) (R.headD 0 :: R.tail) :=
        cfgCR_norm ((a + 1) :: L) R
      rw [h0, ha]
      have h1 := rule_CR_ge3_iter (a / 2) 0 L (R.headD 0) R.tail
      have h2 := rule_CR_one (bumpHead^[a / 2] L) ((R.headD 0 + a / 2) :: R.tail)
      dsimp only [List.headD_cons, List.tail_cons] at h2
      have h3 := reaches_transferB (bumpHead^[a / 2] L) ((R.headD 0 + a / 2 + 2) :: R.tail)
      exact (h1.trans_plus h2).trans h3
    · have ha : a + 1 = 2 * (a / 2) + 1 + 1 := by omega
      have h0 : encode (.C (a + 1) L R) = cfgCR ((a + 1) :: L) (R.headD 0 :: R.tail) :=
        cfgCR_norm ((a + 1) :: L) R
      have h1 := rule_CR_ge3_iter (a / 2) 1 L (R.headD 0) R.tail
      have h2 := rule_CR_two (bumpHead^[a / 2] L) ((R.headD 0 + a / 2) :: R.tail)
      dsimp only [List.headD_cons, List.tail_cons] at h2
      have h12 :
          ReachesPlus target (encode (.C (a + 1) L R))
            (cfgCR (bumpHead (bumpHead^[a / 2] L)) (0 :: (R.headD 0 + a / 2) :: R.tail)) := by
        rw [h0, ha]
        exact h1.trans_plus h2
      rcases L with _ | ⟨b, L'⟩
      · simp only [next, hev, ↓reduceIte]
        rwa [bumpHead_iter_nil] at h12
      · simp only [next, hev, ↓reduceIte]
        rwa [bumpHead_iter_cons] at h12

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RA_1RC1LB_1LD0RA_HHH0LE_1LC0LF_1RE0LB
