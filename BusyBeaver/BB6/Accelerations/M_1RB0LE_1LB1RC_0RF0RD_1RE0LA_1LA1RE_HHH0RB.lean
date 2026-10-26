/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB`.

Left-stack digits $L = [a_0, a_1, \dots]$ encode unary blocks $1^{a_i + 1}$ separated by `00`
(`encStack2`), and right-stack digits $R = [d_0, d_1, \dots]$ encode unary blocks $1^{d_i + 1}$
separated by single zeros (`encStack`), both ordered from the tape head outward. Starting from
`init []`, the machine reaches $C(1, [], [0, 0])$ in 12 raw steps, where $C(a, L, R)$ has state
`C` reading `0` between `encStack2 (a :: L)` and `encStack R`.

## Accelerated Transition Rules

```text
bump2([])      = (1, [])
bump2(b :: L)  = (b + 2, L)

d0Out([])           = [0]
d0Out([d])          = [d + 1]
d0Out(d :: r :: R)  = (r + d + 2) :: R

scanOnes(a, L, [])           = Halt
scanOnes(a, L, [0])          = C(b, L', [a + 2, 0])               where (b, L') = bump2(L)
scanOnes(a, L, 0 :: r :: R)  = C(b, L', (a + r + 3) :: d0Out(R))  where (b, L') = bump2(L)
scanOnes(a, L, 1 :: R)       = scanOnes(0, a :: L, R)
scanOnes(a, L, (r + 2) :: R) = C(a + 2, L, r :: d0Out(R))

C(a, L, R) -> scanOnes(a, L, R)

Start: C(1, [], [0, 0]), reached after 12 raw TM steps
```

Contracting full parity peels $r_0 = 2k + (r_0 \bmod 2)$ via `d0Iter` and leading `1`-peels via
`scanEpoch` yields a single-epoch high-level transition system $C_{\mathrm{HL}}(a, L, R)$ starting
at $C_{\mathrm{HL}}(1, [], [0, 0])$.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_---0RB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Increment the head digit of `L` twice (pushing `1` when `L = []`), split as `(head, tail)`. -/
def bump2 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun b xs => (b + 2, xs)

/-- Right-stack output produced by contracting a `D` right-block shift on `R`. -/
def d0Out : List ℕ → List ℕ
  | [] => [0]
  | [d] => [d + 1]
  | d :: r :: s => (r + d + 2) :: s

/-- Symbolic state space for the accelerated stack transition system of `target`. -/
inductive State where
  /-- Separator configuration `C(a, L, R)`: state `C` on `0` between `a :: L` and `R`. -/
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Peel all leading `1`s from `R` in `C` and contract the exit cycle (`none` indicates halting). -/
def scanOnes (a : ℕ) (L : List ℕ) : List ℕ → Option State
  | [] => none
  | [0] =>
    let (b, L') := bump2 L
    some (.C b L' [a + 2, 0])
  | 0 :: r :: R =>
    let (b, L') := bump2 L
    some (.C b L' ((a + r + 3) :: d0Out R))
  | 1 :: R => scanOnes 0 (a :: L) R
  | (r + 2) :: R => some (.C (a + 2) L (r :: d0Out R))

/-- Initial symbolic state `C(1, [], [0, 0])`, reached from `init []` in 12 raw steps. -/
def start : State := .C 1 [] [0, 0]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a L R => Cfg.headRight C (encStack2 (a :: L)) (ListBlank.cons 0 (encStack R))

/-- Accelerated transition function (`none` indicates halting, reached only when `R` drains). -/
def next : State → Option State
  | .C a L R => scanOnes a L R

/-! ## Stack Encoding and Block-Shift Helpers -/

private theorem bumpHead_twice (L : List ℕ) :
    bumpHead (bumpHead L) = (bump2 L).1 :: (bump2 L).2 := by
  cases L <;> rfl

private theorem encStack2_cons_one (L : List ℕ) :
    ListBlank.cons 1 (encStack2 L) = encStack2 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack2, list_pow_one]
  | cons a L' =>
    simp only [bumpHead, encStack2]
    rw [ListBlank.append_pow_succ]
    rfl

private theorem encStack_cons_one (R : List ℕ) :
    ListBlank.cons 1 (encStack R) = encStack (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encStack, list_pow_one]
  | cons d R' =>
    simp only [bumpHead, encStack]
    rw [ListBlank.append_pow_succ]
    rfl

private theorem encStack2_zero (L : List ℕ) :
    encStack2 (0 :: L) = ListBlank.cons 1 (ListBlank.cons 0 (ListBlank.cons 0 (encStack2 L))) := by
  simp [encStack2, list_pow_one]

private theorem encStack2_succ (a : ℕ) (L : List ℕ) :
    encStack2 ((a + 1) :: L) = ListBlank.cons 1 (encStack2 (a :: L)) := by
  simp only [encStack2]
  rw [ListBlank.append_pow_succ]
  rfl

private theorem encStack_zero (R : List ℕ) :
    encStack (0 :: R) = ListBlank.cons 1 (ListBlank.cons 0 (encStack R)) := by
  simp [encStack, list_pow_one]

private theorem encStack_succ (d : ℕ) (R : List ℕ) :
    encStack ((d + 1) :: R) = ListBlank.cons 1 (encStack (d :: R)) := by
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  rfl

private theorem walk_E_right (d : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{E}}> ((([1] : List (Fin 2)) ^ d) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ d)) {{E}}> r) := by
  induction d generalizing l r with
  | zero => bb_refl
  | succ d ih =>
    have h1 :
        (l {{E}}> ((([1] : List (Fin 2)) ^ (d + 1)) +> r)) [target]⊢⁺
          (([1] +> l) {{E}}> ((([1] : List (Fin 2)) ^ d) +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih ([1] +> l) r
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem shift_A1_left (d : ℕ) (l r : ListBlank (Fin 2)) :
    (Cfg.headRight A (l <+ (([1] : List (Fin 2)) ^ d)) (ListBlank.cons 1 r)) [target]⊢*
      (Cfg.headRight A l (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ d) +> r))) := by
  induction d generalizing l r with
  | zero => bb_refl
  | succ d ih =>
    have h1 :
        (Cfg.headRight A (l <+ (([1] : List (Fin 2)) ^ (d + 1))) (ListBlank.cons 1 r)) [target]⊢⁺
          (Cfg.headRight A (l <+ (([1] : List (Fin 2)) ^ d))
            (ListBlank.cons 1 (ListBlank.cons 1 r))) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.cons 1 r)
    have hr :
        (([1] : List (Fin 2)) ^ d) +> (ListBlank.cons 1 r) =
          (([1] : List (Fin 2)) ^ (d + 1)) +> r :=
      ListBlank.append_pow_succ' ([1] : List (Fin 2)) d r
    rw [hr] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Mode Contractions (`A0`, `A1`, `B0`, `D0`, `E0`) -/

private def cfgA0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (encStack2 L) (ListBlank.cons 0 (encStack R))

private def cfgA1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (encStack2 L) (ListBlank.cons 1 (encStack R))

private def cfgB0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack2 L) (ListBlank.cons 0 (encStack R))

private def cfgD0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (ListBlank.cons 0 (encStack2 L)) (ListBlank.cons 0 (encStack R))

private def cfgE0 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack2 L) (ListBlank.cons 0 (ListBlank.cons 0 (encStack R)))

private theorem d0Out_enc (d : ℕ) (R : List ℕ) :
    ((([1] : List (Fin 2)) ^ (d + 1)) +> (ListBlank.cons 1 (encStack R))) =
      encStack (d0Out (d :: R)) := by
  rcases R with _ | ⟨r, R'⟩
  · change ((([1] : List (Fin 2)) ^ (d + 1)) +> ([1] +> default)) = _
    rw [ListBlank.append_pow_succ']
    simp [d0Out, encStack]
  · simp only [d0Out, encStack]
    change ((([1] : List (Fin 2)) ^ (d + 1)) +>
        (([1] : List (Fin 2)) +> ((([1] : List (Fin 2)) ^ (r + 1)) +> ((encStack R').cons 0)))) = _
    rw [← ListBlank.append_pow_succ ([1] : List (Fin 2)) (r + 1),
      ← ListBlank.append_pow_add ([1] : List (Fin 2)) (d + 1) (r + 2),
      show d + 1 + (r + 2) = r + d + 2 + 1 by omega]

private theorem d0_to_e0 (L R : List ℕ) :
    (cfgD0 L R) [target]⊢⁺ (cfgE0 L (d0Out R)) := by
  rcases R with _ | ⟨d, R'⟩
  · unfold cfgD0 cfgE0
    simp only [d0Out]
    rw [encStack_zero]
    simp only [encStack]
    bb_steps
  · have h1 :
        (cfgD0 L (d :: R')) [target]⊢⁺
          ((ListBlank.append [1, 1, 0] (encStack2 L)) {{E}}>
            ((([1] : List (Fin 2)) ^ d) +> (ListBlank.cons 0 (encStack R')))) := by
      unfold cfgD0
      simp only [encStack]
      rw [show d + 1 = 1 + d by omega, ListBlank.append_pow_add, list_pow_one]
      bb_steps
    have h2 := walk_E_right d (ListBlank.append [1, 1, 0] (encStack2 L))
      (ListBlank.cons 0 (encStack R'))
    have hl :
        ((ListBlank.append [1, 1, 0] (encStack2 L)) <+ (([1] : List (Fin 2)) ^ d)) =
          ListBlank.cons 1
            (((ListBlank.cons 0 (encStack2 L)) <+ (([1] : List (Fin 2)) ^ (d + 1)))) := by
      change (((ListBlank.cons 0 (encStack2 L)) <+ (([1] : List (Fin 2)) ^ 2)) <+
          (([1] : List (Fin 2)) ^ d)) =
        (((ListBlank.cons 0 (encStack2 L)) <+ (([1] : List (Fin 2)) ^ (d + 1))) <+
          (([1] : List (Fin 2)) ^ 1))
      rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
        show d + 2 = 1 + (d + 1) by omega]
    rw [hl] at h2
    have h3 :
        ((ListBlank.cons 1 (((ListBlank.cons 0 (encStack2 L)) <+ (([1] : List (Fin 2)) ^ (d + 1)))))
          {{E}}> (ListBlank.cons 0 (encStack R'))) [target]⊢⁺
          (Cfg.headRight A ((ListBlank.cons 0 (encStack2 L)) <+ (([1] : List (Fin 2)) ^ (d + 1)))
            (ListBlank.cons 1 (ListBlank.cons 1 (encStack R')))) := by
      bb_steps
    have h4 := shift_A1_left (d + 1) (ListBlank.cons 0 (encStack2 L))
      (ListBlank.cons 1 (encStack R'))
    have h5 :
        (Cfg.headRight A (ListBlank.cons 0 (encStack2 L))
          (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ (d + 1)) +> (ListBlank.cons 1 (encStack R')))))
          [target]⊢⁺ (cfgE0 L (d0Out (d :: R'))) := by
      unfold cfgE0
      rw [d0Out_enc]
      bb_steps
    exact (((h1.trans_star h2).trans h3).trans_star h4).trans h5

private theorem rule_A0_zero (L R : List ℕ) :
    (cfgA0 L (0 :: R)) [target]⊢⁺ (encode (.C (bump2 L).1 (bump2 L).2 R)) := by
  unfold cfgA0
  simp only [encode]
  rw [← bumpHead_twice, encStack_zero, ← encStack2_cons_one, ← encStack2_cons_one]
  bb_steps

private theorem rule_A1_succ (a : ℕ) (L R : List ℕ) :
    (cfgA1 ((a + 1) :: L) R) [target]⊢⁺ (cfgA1 (a :: L) (bumpHead R)) := by
  unfold cfgA1
  rw [encStack2_succ, ← encStack_cons_one]
  bb_steps

private theorem a1_peel (k : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgA1 (k :: L) (d :: R)) [target]⊢* (cfgA1 (0 :: L) ((d + k) :: R)) := by
  induction k generalizing d with
  | zero => rw [Nat.add_zero]
  | succ k ih =>
    have h1 := rule_A1_succ k L (d :: R)
    simp only [bumpHead] at h1
    have h2 := ih (d + 1)
    rw [show d + 1 + k = d + (k + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

private theorem a1_zero_exit (L : List ℕ) (d : ℕ) (R : List ℕ) :
    (cfgA1 (0 :: L) (d :: R)) [target]⊢⁺ (encode (.C (bump2 L).1 (bump2 L).2 ((d + 1) :: R))) := by
  rcases L with _ | ⟨b, L'⟩
  · have h1 : (cfgA1 [0] (d :: R)) [target]⊢⁺ (cfgA0 [] (0 :: (d + 1) :: R)) := by
      unfold cfgA1 cfgA0
      rw [encStack2_zero, encStack_zero, encStack_succ]
      simp only [encStack2]
      bb_steps
    exact h1.trans (rule_A0_zero [] ((d + 1) :: R))
  · have h1 :
        (cfgA1 (0 :: b :: L') (d :: R)) [target]⊢⁺ (cfgA0 (b :: L') (0 :: (d + 1) :: R)) := by
      unfold cfgA1 cfgA0
      rw [encStack2_zero, encStack_zero, encStack_succ]
      bb_steps
    exact h1.trans (rule_A0_zero (b :: L') ((d + 1) :: R))

private theorem e0_to_c0 (a : ℕ) (L R : List ℕ) :
    (cfgE0 (a :: L) R) [target]⊢⁺ (encode (.C (bump2 L).1 (bump2 L).2 (a :: R))) := by
  rcases a with _ | a
  · rcases L with _ | ⟨b, L'⟩
    · have h1 : (cfgE0 [0] R) [target]⊢⁺ (cfgA0 [] (0 :: 0 :: R)) := by
        unfold cfgE0 cfgA0
        rw [encStack2_zero, encStack_zero, encStack_zero]
        simp only [encStack2]
        bb_steps
      exact h1.trans (rule_A0_zero [] (0 :: R))
    · have h1 : (cfgE0 (0 :: b :: L') R) [target]⊢⁺ (cfgA0 (b :: L') (0 :: 0 :: R)) := by
        unfold cfgE0 cfgA0
        rw [encStack2_zero, encStack_zero, encStack_zero]
        bb_steps
      exact h1.trans (rule_A0_zero (b :: L') (0 :: R))
  · have h1 : (cfgE0 ((a + 1) :: L) R) [target]⊢⁺ (cfgA1 (a :: L) (0 :: R)) := by
      unfold cfgE0 cfgA1
      rw [encStack2_succ, encStack_zero]
      bb_steps
    have h2 := a1_peel a L 0 R
    rw [Nat.zero_add] at h2
    exact (h1.trans_star h2).trans (a1_zero_exit L a R)

private theorem d0_to_c0 (a : ℕ) (L R : List ℕ) :
    (cfgD0 (a :: L) R) [target]⊢⁺ (encode (.C (bump2 L).1 (bump2 L).2 (a :: d0Out R))) :=
  (d0_to_e0 (a :: L) R).trans (e0_to_c0 a L (d0Out R))

/-! ## `B0` and `C0` Contractions -/

private theorem rule_B0_cons_zero (a : ℕ) (L R : List ℕ) :
    (cfgB0 (a :: L) (0 :: R)) [target]⊢⁺ (cfgD0 ((a + 1) :: L) R) := by
  unfold cfgB0 cfgD0
  rw [encStack2_succ, encStack_zero]
  simp only [encStack2]
  rw [ListBlank.append_pow_succ]
  bb_steps

private theorem rule_B0_cons_succ (a d : ℕ) (L R : List ℕ) :
    (cfgB0 (a :: L) ((d + 1) :: R)) [target]⊢⁺ (cfgB0 ((a + 1) :: L) (d :: R)) := by
  unfold cfgB0
  rw [encStack2_succ, encStack_succ]
  simp only [encStack2]
  rw [ListBlank.append_pow_succ]
  bb_steps

private theorem b0_peel (d a : ℕ) (L R : List ℕ) :
    (cfgB0 (a :: L) (d :: R)) [target]⊢⁺ (cfgD0 ((a + d + 1) :: L) R) := by
  induction d generalizing a with
  | zero =>
    simpa using rule_B0_cons_zero a L R
  | succ d ih =>
    have h := (rule_B0_cons_succ a d L R).trans (ih (a + 1))
    rw [show a + 1 + d + 1 = a + (d + 1) + 1 by omega] at h
    exact h

private theorem halt_C_nil (a : ℕ) (L : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.C a L [])) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F (ListBlank.cons 0 (encStack2 (a :: L))) default, ?_, ?_⟩
  · have h :
        (encode (.C a L [])) [target]⊢⁺
          Cfg.headRight F (ListBlank.cons 0 (encStack2 (a :: L))) default := by
      simp only [encode, encStack]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_C_zero_nil (a : ℕ) (L : List ℕ) :
    (encode (.C a L [0])) [target]⊢⁺ (encode (.C (bump2 L).1 (bump2 L).2 [a + 2, 0])) := by
  have h1 : (encode (.C a L [0])) [target]⊢⁺ (cfgB0 (a :: L) [1]) := by
    simp only [encode, cfgB0]
    rw [encStack_zero, encStack_succ, encStack_zero]
    simp only [encStack]
    bb_steps
  have h2 := b0_peel 1 a L []
  rw [show a + 1 + 1 = a + 2 by omega] at h2
  exact (h1.trans h2).trans (d0_to_c0 (a + 2) L [])

private theorem rule_C_zero_cons (a r : ℕ) (L R : List ℕ) :
    (encode (.C a L (0 :: r :: R))) [target]⊢⁺
      (encode (.C (bump2 L).1 (bump2 L).2 ((a + r + 3) :: d0Out R))) := by
  have h1 : (encode (.C a L (0 :: r :: R))) [target]⊢⁺ (cfgB0 (a :: L) ((r + 2) :: R)) := by
    simp only [encode, cfgB0]
    rw [encStack_zero, encStack_succ (r + 1) R, encStack_succ r R]
    bb_steps
  have h2 := b0_peel (r + 2) a L R
  rw [show a + (r + 2) + 1 = a + r + 3 by omega] at h2
  exact (h1.trans h2).trans (d0_to_c0 (a + r + 3) L R)

private theorem rule_C_one (a : ℕ) (L R : List ℕ) :
    (encode (.C a L (1 :: R))) [target]⊢⁺ (encode (.C 0 (a :: L) R)) := by
  simp only [encode]
  rw [encStack_succ 0 R, encStack_zero R, encStack2_zero (a :: L)]
  bb_steps

private theorem rule_C_ge2 (a r : ℕ) (L R : List ℕ) :
    (encode (.C a L ((r + 2) :: R))) [target]⊢⁺ (encode (.C (a + 2) L (r :: d0Out R))) := by
  rcases r with _ | _ | d
  · have h1 : (encode (.C a L (2 :: R))) [target]⊢⁺ (cfgD0 (0 :: a :: L) R) := by
      simp only [encode, cfgD0]
      rw [encStack_succ 1 R, encStack_succ 0 R, encStack_zero R, encStack2_zero (a :: L)]
      bb_steps
    exact h1.trans (d0_to_c0 0 (a :: L) R)
  · have h1 : (encode (.C a L (3 :: R))) [target]⊢⁺ (cfgD0 (1 :: a :: L) R) := by
      simp only [encode, cfgD0]
      rw [encStack_succ 2 R, encStack_succ 1 R, encStack_succ 0 R, encStack_zero R,
        encStack2_succ 0 (a :: L), encStack2_zero (a :: L)]
      bb_steps
    exact h1.trans (d0_to_c0 1 (a :: L) R)
  · have h1 : (encode (.C a L ((d + 4) :: R))) [target]⊢⁺ (cfgB0 (1 :: a :: L) (d :: R)) := by
      simp only [encode, cfgB0]
      rw [encStack_succ (d + 3) R, encStack_succ (d + 2) R, encStack_succ (d + 1) R,
        encStack_succ d R, encStack2_succ 0 (a :: L), encStack2_zero (a :: L)]
      bb_steps
    have h2 := b0_peel d 1 (a :: L) R
    rw [show 1 + d + 1 = d + 2 by omega] at h2
    exact (h1.trans h2).trans (d0_to_c0 (d + 2) (a :: L) R)

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : (init []) [target]⊢* (encode start) := by
  have h : (init []) [target]⊢⁺ (encode start) := by
    simp only [start, encode]
    rw [encStack2_succ, encStack2_zero, encStack_zero, encStack_zero]
    simp only [encStack2, encStack]
    bb_steps
  exact h.to_star

private theorem reaches_scanOnes (a : ℕ) (L R : List ℕ) :
    match scanOnes a L R with
    | some s' => ReachesPlus target (encode (.C a L R)) (encode s')
    | none => ∃ cfg', ReachesStar target (encode (.C a L R)) cfg' ∧ (step target cfg').isNone := by
  match R with
  | [] =>
    simp only [scanOnes]
    exact halt_C_nil a L
  | [0] =>
    simp only [scanOnes]
    exact rule_C_zero_nil a L
  | 0 :: r :: R' =>
    simp only [scanOnes]
    exact rule_C_zero_cons a r L R'
  | 1 :: R' =>
    simp only [scanOnes]
    have h1 := rule_C_one a L R'
    have ih := reaches_scanOnes 0 (a :: L) R'
    rcases h : scanOnes 0 (a :: L) R' with _ | s'
    · rw [h] at ih
      obtain ⟨cfg', hstar, hnone⟩ := ih
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · rw [h] at ih
      exact h1.trans ih
  | (r + 2) :: R' =>
    simp only [scanOnes]
    exact rule_C_ge2 a r L R'

private theorem step_accel (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, L, R⟩
  exact reaches_scanOnes a L R

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next :=
  IsValidAcceleration.of_step init_reaches_start fun s => by
    cases h : next s <;> simpa [h] using step_accel s

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Acceleration -/

/-- High-level symbolic state space contracting full parity peels and leading `1`-scans. -/
inductive HighLevelState where
  /-- Separator configuration $C(a, L, R)$ at the start of an epoch. -/
  | C (a : ℕ) (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $C_{\mathrm{HL}}(1, [], [0, 0])$. -/
def highLevelStart : HighLevelState := .C 1 [] [0, 0]

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a L R => .C a L R

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Iterate `d0Out` `k` times on right stack `R`. -/
def d0Iter (k : ℕ) (R : List ℕ) : List ℕ :=
  if k = 0 then R else d0Iter (k - 1) (d0Out R)
termination_by k
decreasing_by omega

/-- Contract consecutive `(r + 2)` right-block shifts and leading `1`-peels from `C(a, L, R)`. -/
def scanEpoch (a : ℕ) (L R : List ℕ) : Option HighLevelState :=
  if R = [] then
    none
  else
    let r₀ := R.headD 0
    let R' := R.tail
    let k := r₀ / 2
    let Rk := d0Iter k R'
    let a₁ := a + 2 * k
    if r₀ % 2 = 0 then
      let p := bump2 L
      List.casesOn Rk (some (.C p.1 p.2 [a₁ + 2, 0])) fun r R'' =>
        some (.C p.1 p.2 ((a₁ + r + 3) :: d0Out R''))
    else if Rk.length - 1 < R'.length ∨
        (R'.length = 0 ∧ Rk.length ≤ 1 ∧ Rk.headD 0 < r₀) then
      scanEpoch 0 (a₁ :: L) Rk
    else
      none
termination_by (R.length - 1, R.headD 0)
decreasing_by
  simp_wf
  cases R with
  | nil => contradiction
  | cons head tail =>
    simp +zetaDelta only [Prod.lex_def, List.headD_eq_head?, List.head?_cons, Option.getD_some,
      List.tail_cons, List.length_cons] at *
    omega

/-- High-level accelerated transition function on $C_{\mathrm{HL}}(a, L, R)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C a L R => scanEpoch a L R

private theorem d0Iter_zero (R : List ℕ) : d0Iter 0 R = R := by
  rw [d0Iter]
  rfl

private theorem d0Iter_succ (k : ℕ) (R : List ℕ) :
    d0Iter (k + 1) R = d0Iter k (d0Out R) := by
  rw [d0Iter]
  simp

private theorem d0Iter_singleton (k d : ℕ) : d0Iter k [d] = [d + k] := by
  induction k generalizing d with
  | zero => rw [d0Iter_zero, Nat.add_zero]
  | succ k ih =>
    rw [d0Iter_succ, d0Out, ih (d + 1)]
    congr 1
    omega

private theorem d0Iter_nil_succ (k : ℕ) : d0Iter (k + 1) [] = [k] := by
  rw [d0Iter_succ, d0Out, d0Iter_singleton, Nat.zero_add]

private theorem d0Out_length_le {R : List ℕ} (h : R ≠ []) :
    1 ≤ (d0Out R).length ∧ (d0Out R).length ≤ R.length := by
  rcases R with _ | ⟨d, _ | ⟨r, s⟩⟩
  · contradiction
  · simp [d0Out]
  · simp [d0Out]

private theorem d0Iter_length_le (k : ℕ) {R : List ℕ} (h : R ≠ []) :
    1 ≤ (d0Iter k R).length ∧ (d0Iter k R).length ≤ R.length := by
  induction k generalizing R with
  | zero =>
    rw [d0Iter_zero]
    cases R with
    | nil => contradiction
    | cons _ _ => simp
  | succ k ih =>
    rw [d0Iter_succ]
    obtain ⟨h1, h2⟩ := d0Out_length_le h
    obtain ⟨ih1, ih2⟩ := ih (List.ne_nil_of_length_pos h1)
    exact ⟨ih1, Nat.le_trans ih2 h2⟩

private theorem scanEpoch_guard {r₀ : ℕ} (hodd : r₀ % 2 = 1) (R' : List ℕ) :
    (d0Iter (r₀ / 2) R').length - 1 < R'.length ∨
      (R'.length = 0 ∧ (d0Iter (r₀ / 2) R').length ≤ 1 ∧
        (d0Iter (r₀ / 2) R').headD 0 < r₀) := by
  rcases R' with _ | ⟨d, R''⟩
  · right
    rcases hk : r₀ / 2 with _ | m
    · rw [d0Iter_zero]
      simp only [List.length_nil, Nat.zero_le, List.headD_nil, true_and]
      omega
    · rw [d0Iter_nil_succ]
      simp only [List.length_nil, List.length_singleton, le_refl, List.headD_cons, true_and]
      omega
  · left
    obtain ⟨_, hle⟩ := d0Iter_length_le (r₀ / 2) (List.cons_ne_nil d R'')
    simp only [List.length_cons] at hle ⊢
    omega

private theorem reaches_d0Iter (k a m : ℕ) (L R : List ℕ) :
    CollatzReachesStar next (.C a L ((2 * k + m) :: R))
      (.C (a + 2 * k) L (m :: d0Iter k R)) := by
  induction k generalizing a R with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero, d0Iter_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h1 : next (.C a L ((2 * (k + 1) + m) :: R)) =
        some (.C (a + 2) L ((2 * k + m) :: d0Out R)) := by
      rw [show 2 * (k + 1) + m = (2 * k + m) + 2 by omega]
      rfl
    have h2 := ih (a + 2) (d0Out R)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) by omega, ← d0Iter_succ] at h2
    exact CollatzReachesStar.head h1 h2

private theorem stepsTo_of_next_eq {s₁ s₂ : State} {res : Option State}
    (h : next s₁ = next s₂) (hs : CollatzStepsTo next s₂ res) :
    CollatzStepsTo next s₁ res := by
  rcases res with _ | s'
  · obtain ⟨n, hn⟩ := hs
    rcases n with _ | m
    · simp at hn
    · refine ⟨m + 1, ?_⟩
      rw [Function.iterate_succ_apply] at hn ⊢
      change ((Option.bind · next)^[m] (next s₁)).isNone
      rw [h]
      exact hn
  · obtain ⟨n, hpos, hn⟩ := hs
    rcases n with _ | m
    · omega
    · refine ⟨m + 1, Nat.succ_pos m, ?_⟩
      unfold CollatzReachesIn at hn ⊢
      rw [Function.iterate_succ_apply] at hn ⊢
      change (Option.bind · next)^[m] (next s₁) = some s'
      rw [h]
      exact hn

private theorem stepsTo_peel_one (a : ℕ) (L R : List ℕ) {res : Option State}
    (hs : CollatzStepsTo next (.C 0 (a :: L) R) res) :
    CollatzStepsTo next (.C a L (1 :: R)) res :=
  stepsTo_of_next_eq (s₁ := .C a L (1 :: R)) (s₂ := .C 0 (a :: L) R) rfl hs

private theorem stepsTo_even_exit (a : ℕ) (L Rk : List ℕ) :
    CollatzStepsTo next (.C a L (0 :: Rk))
      ((List.casesOn (motive := fun _ => Option HighLevelState) Rk
          (some (HighLevelState.C (bump2 L).1 (bump2 L).2 [a + 2, 0]))
          fun r R'' =>
            some (HighLevelState.C (bump2 L).1 (bump2 L).2 ((a + r + 3) :: d0Out R''))).map
        toState) := by
  rcases Rk with _ | ⟨r, R''⟩
  · exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.of_eq rfl

private theorem stepsTo_scanEpoch_short (r₀ : ℕ) :
    ∀ (a : ℕ) (L R : List ℕ), R.length ≤ 1 → R.headD 0 = r₀ →
      CollatzStepsTo next (.C a L R) ((scanEpoch a L R).map toState) := by
  induction r₀ using Nat.strong_induction_on with
  | h r₀ ihr =>
    intro a L R hlen hhead
    rcases R with _ | ⟨r, _ | ⟨_, _⟩⟩
    · rw [scanEpoch]
      simp only [↓reduceIte]
      exact CollatzStepsTo.of_eq rfl
    · dsimp only [List.headD] at hhead
      subst r
      rw [scanEpoch]
      simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
      have hr : 2 * (r₀ / 2) + r₀ % 2 = r₀ := by omega
      have hstar := hr ▸ reaches_d0Iter (r₀ / 2) a (r₀ % 2) L []
      refine CollatzStepsTo.of_reachesStar hstar ?_
      by_cases hev : r₀ % 2 = 0
      · simp only [hev, ↓reduceIte]
        exact stepsTo_even_exit (a + 2 * (r₀ / 2)) L (d0Iter (r₀ / 2) [])
      · have hodd : r₀ % 2 = 1 := by omega
        have hg := scanEpoch_guard hodd []
        simp only [hev, ↓reduceIte, hg]
        rw [hodd]
        have hlen' : (d0Iter (r₀ / 2) []).length ≤ 1 := by
          rcases hg with hlt | ⟨_, hle, _⟩
          · simp at hlt
          · exact hle
        have hlt' : (d0Iter (r₀ / 2) []).headD 0 < r₀ := by
          rcases hg with hlt | ⟨_, _, hhd⟩
          · simp at hlt
          · exact hhd
        exact stepsTo_peel_one _ _ _
          (ihr _ hlt' 0 ((a + 2 * (r₀ / 2)) :: L) (d0Iter (r₀ / 2) []) hlen' rfl)
    · simp at hlen

private theorem stepsTo_scanEpoch_len (n : ℕ) :
    ∀ (a : ℕ) (L R : List ℕ), R.length = n →
      CollatzStepsTo next (.C a L R) ((scanEpoch a L R).map toState) := by
  induction n using Nat.strong_induction_on with
  | h n ihn =>
    intro a L R hlen
    by_cases hle1 : n ≤ 1
    · exact stepsTo_scanEpoch_short (R.headD 0) a L R (hlen ▸ hle1) rfl
    · rcases R with _ | ⟨r₀, R'⟩
      · simp at hlen
        omega
      · rw [scanEpoch]
        simp only [reduceCtorEq, ↓reduceIte, List.headD_cons, List.tail_cons]
        have hr : 2 * (r₀ / 2) + r₀ % 2 = r₀ := by omega
        have hstar := hr ▸ reaches_d0Iter (r₀ / 2) a (r₀ % 2) L R'
        refine CollatzStepsTo.of_reachesStar hstar ?_
        by_cases hev : r₀ % 2 = 0
        · simp only [hev, ↓reduceIte]
          exact stepsTo_even_exit (a + 2 * (r₀ / 2)) L (d0Iter (r₀ / 2) R')
        · have hodd : r₀ % 2 = 1 := by omega
          have hg := scanEpoch_guard hodd R'
          simp only [hev, ↓reduceIte, hg]
          rw [hodd]
          have hne : R' ≠ [] := by
            intro hnil
            subst hnil
            simp at hlen
            omega
          obtain ⟨_, hkle⟩ := d0Iter_length_le (r₀ / 2) hne
          have hklt : (d0Iter (r₀ / 2) R').length < n := by
            simp only [List.length_cons] at hlen
            omega
          exact stepsTo_peel_one _ _ _
            (ihn _ hklt 0 ((a + 2 * (r₀ / 2)) :: L) (d0Iter (r₀ / 2) R') rfl)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, L, R⟩
  exact stepsTo_scanEpoch_len R.length a L R rfl

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0LE_1LB1RC_0RF0RD_1RE0LA_1LA1RE_HHH0RB
