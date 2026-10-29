/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $CR(0, 0, [], 0, [])$ in 5 raw steps, where $CR(a, b, L, d, R)$ has state `C` reading `0`
with `encStack (a :: b :: L)` on the left and `1^d 0 (encStack R)` to its right.

## Accelerated Transition Rules

```text
stepZero(0, d, L, R)      = CR(d + 1, c, L', r, R')   where (c, L') = bump2(L), (r, R') = bump1(R)
stepZero(1, d, L, R)      = CR(0, c, L', d + 1, R)    where (c, L') = bump2(L)
stepZero(b + 2, d, L, R)  = CR(b, c, L', 0, d :: R)   where (c, L') = bump2(L)

stepOne(b, L, [])             = CR(0, b + 5, L, 0, [])
stepOne(b, L, [0])            = CR(0, b + 5, L, 0, [])
stepOne(b, L, 0 :: r2 :: R3)  = CR(r2 + 1, b + 5, L, r, R')  where (r, R') = bump1(R3)
stepOne(b, L, (e + 1) :: R2)  = CR(e, b + 5, L, r, R')       where (r, R') = bump1(R2)

For d = 0, let q = a / 3, b1 = b + 2*q, R1 = bumpHeadBy(q, R):
CR(a, b, L, 0, R) [a % 3 = 0] -> stepZero(b1, 0, L, R1)
CR(a, b, L, 0, R) [a % 3 = 1] -> stepOne(b1, L, R1)
CR(a, b, L, 0, R) [a % 3 = 2] -> CR(0, b1 + 2, L, r + 1, R')   where (r, R') = bump1(R1)

CR(0, b, L, d + 1, R)         -> stepZero(b, d + 1, L, R)
CR(1, b, L, d + 1, R)         -> Halt
CR(a + 2, b, L, d + 1, R)     -> CR(d + 1, a + 1, b :: L, r, R')  where (r, R') = bump1(R)

Start: CR(0, 0, [], 0, []), reached after 5 raw TM steps
```

<!-- hardness:begin -->
## Hardness

*Hardness class:* S5 sibling — trigger **POW**, growth —, shield partial.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* E1 Group 39 with #549 (same table, different seed); not separately measured

*Simulated horizon:* family-level

*Why it is hard:* see #549

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Increment the head digit of `s` once, returning `(head, tail)`. -/
def bump1 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (0, []) fun r xs => (r + 1, xs)

/-- Increment the head digit of `s` twice, returning `(head, tail)`. -/
def bump2 (s : List ℕ) : ℕ × List ℕ :=
  List.casesOn s (1, []) fun c xs => (c + 2, xs)

/-- Symbolic state space for the accelerated stack transition system of `target`. -/
inductive State where
  /-- Configuration `CR(a, b, L, d, R)`: state `C` on `0` between `a :: b :: L` and `1^d 0 R`. -/
  | CR (a b : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Exit transition from `CR(0, b, L, d, R)` across all `b` and `d`. -/
def stepZero (b d : ℕ) (L R : List ℕ) : State :=
  let pL := bump2 L
  if b = 0 then
    let pR := bump1 R
    .CR (d + 1) pL.1 pL.2 pR.1 pR.2
  else if b = 1 then
    .CR 0 pL.1 pL.2 (d + 1) R
  else
    .CR (b - 2) pL.1 pL.2 0 (d :: R)

/-- Exit transition from `CR(1, b, L, 0, R)` across all right stacks `R`. -/
def stepOne (b : ℕ) (L R : List ℕ) : State :=
  List.casesOn R (.CR 0 (b + 5) L 0 []) fun r₀ R₂ =>
    Nat.casesOn r₀
      (List.casesOn R₂ (.CR 0 (b + 5) L 0 []) fun r₂ R₃ =>
        let pR := bump1 R₃
        .CR (r₂ + 1) (b + 5) L pR.1 pR.2)
      fun e =>
        let pR := bump1 R₂
        .CR e (b + 5) L pR.1 pR.2

/-- Initial symbolic state `CR(0, 0, [], 0, [])`, reached from `init []` in 5 raw steps. -/
def start : State := .CR 0 0 [] 0 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .CR a b L d R =>
    Cfg.headRight C (encStack (a :: b :: L))
      (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ d)
        (ListBlank.cons 0 (encStack R))))

/-- Accelerated transition function (`none` indicates halting, reached at `a = 1, d ≥ 1`). -/
def next : State → Option State
  | .CR a b L 0 R =>
    let q := a / 3
    let b₁ := b + 2 * q
    let R₁ := bumpHeadBy q R
    if a % 3 = 0 then
      some (stepZero b₁ 0 L R₁)
    else if a % 3 = 1 then
      some (stepOne b₁ L R₁)
    else
      let pR := bump1 R₁
      some (.CR 0 (b₁ + 2) L (pR.1 + 1) pR.2)
  | .CR 0 b L (d + 1) R => some (stepZero b (d + 1) L R)
  | .CR 1 _ _ (_ + 1) _ => none
  | .CR (a + 2) b L (d + 1) R =>
    let pR := bump1 R
    some (.CR (d + 1) (a + 1) (b :: L) pR.1 pR.2)

/-! ## Stack Encoding and Sweep Helpers -/

private theorem bump1_eq (R : List ℕ) : (bump1 R).1 :: (bump1 R).2 = bumpHead R := by
  cases R <;> rfl

private theorem bump2_eq (L : List ℕ) : (bump2 L).1 :: (bump2 L).2 = bumpHead (bumpHead L) := by
  cases L <;> rfl

private theorem encStack_cons_one (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack, list_pow_one]
  | cons a s' =>
    simp only [bumpHead, encStack]
    rw [ListBlank.append_pow_succ]
    rfl

private theorem encStack_zero (s : List ℕ) :
    encStack (0 :: s) = ListBlank.cons 1 (ListBlank.cons 0 (encStack s)) := by
  simp [encStack, list_pow_one]

private theorem encStack_succ (a : ℕ) (s : List ℕ) :
    encStack ((a + 1) :: s) = ListBlank.cons 1 (encStack (a :: s)) := by
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  rfl

private theorem walk_C_right (k : ℕ) (l r : ListBlank (Fin 2)) :
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

private theorem walk_E_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{E}} r) [target]⊢*
      (l <{{E}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => bb_refl
  | succ k ih =>
    have h1 :
        ((l <+ (([1] : List (Fin 2)) ^ (k + 1))) <{{E}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{E}} ([1] +> r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l ([1] +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

/-! ## Intermediate Configurations and Local Rules -/

private def cfgB (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgCR (L : List ℕ) (d : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L)
    (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ d)
      (ListBlank.cons 0 (encStack R))))

private theorem cfgCR_eq_encode (a b : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ) :
    cfgCR (a :: b :: L) d R = encode (.CR a b L d R) := rfl

private theorem rule_B_cons_nil (a : ℕ) (L : List ℕ) :
    (cfgB (a :: L) []) [target]⊢⁺ (cfgB (a :: L) [0]) := by
  unfold cfgB
  rw [encStack_zero]
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  bb_steps

private theorem rule_B_cons (a d : ℕ) (L R : List ℕ) :
    (cfgB (a :: L) (d :: R)) [target]⊢⁺
      (encode (.CR d a L (bump1 R).1 (bump1 R).2)) := by
  unfold cfgB
  simp only [encode]
  have h_pre :
      (Cfg.headRight B (encStack (a :: L)) (ListBlank.cons 0 (encStack (d :: R)))) [target]⊢⁺
        (((encStack (a :: L)).cons 0) {{C}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> ((encStack R).cons 0))) := by
    simp only [encStack]
    bb_steps
  have h_walk := walk_C_right (d + 1) ((encStack (a :: L)).cons 0) ((encStack R).cons 0)
  have h_end := h_pre.trans_star h_walk
  have h_r :
      (encStack R).cons 0 =
        ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ (bump1 R).1)
          (ListBlank.cons 0 (encStack (bump1 R).2))) := by
    rcases R with _ | ⟨r, R'⟩
    · simp [bump1, encStack]
    · simp only [bump1, encStack]
  rw [h_r] at h_end
  simpa only [encStack] using h_end

private theorem rule_CR_zero_zero (d : ℕ) (L R : List ℕ) :
    (cfgCR (0 :: 0 :: L) d R) [target]⊢⁺ (cfgB (bumpHead (bumpHead L)) ((d + 1) :: R)) := by
  unfold cfgCR cfgB
  rw [encStack_zero (0 :: L), encStack_zero L, ← encStack_cons_one, ← encStack_cons_one,
    encStack_succ]
  simp only [encStack]
  bb_steps

private theorem rule_CR_zero_one (d : ℕ) (L R : List ℕ) :
    (cfgCR (0 :: 1 :: L) d R) [target]⊢⁺ (cfgB (bumpHead (bumpHead L)) (0 :: d :: R)) := by
  unfold cfgCR cfgB
  rw [encStack_zero (1 :: L), encStack_succ 0 L, encStack_zero L,
    ← encStack_cons_one, ← encStack_cons_one, encStack_zero (d :: R)]
  simp only [encStack]
  bb_steps

private theorem rule_CR_zero_ge2 (b d : ℕ) (L R : List ℕ) :
    (cfgCR (0 :: (b + 2) :: L) d R) [target]⊢⁺
      (encode (.CR b (bump2 L).1 (bump2 L).2 0 (d :: R))) := by
  unfold cfgCR
  simp only [encode]
  have h_pre :
      (Cfg.headRight C (encStack (0 :: (b + 2) :: L))
        (ListBlank.cons 0 (ListBlank.append (([1] : List (Fin 2)) ^ d)
          (ListBlank.cons 0 (encStack R))))) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (b + 3))) <{{E}}
          (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R))))) := by
    rw [encStack_zero]
    simp only [encStack]
    bb_steps
  have h_walkE := walk_E_left (b + 3) ((encStack L).cons 0)
    (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R))))
  have h_split :
      ((([1] : List (Fin 2)) ^ (b + 3)) +>
        (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R))))) =
        ListBlank.cons 1 (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ (b + 1)) +>
          (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R)))))) := by
    rw [show b + 3 = 1 + (1 + (b + 1)) by omega, ListBlank.append_pow_add,
      ListBlank.append_pow_add, list_pow_one]
    rfl
  have h_e := h_pre.trans_star h_walkE
  rw [h_split] at h_e
  have h_mid :
      (((encStack L).cons 0) <{{E}}
        (ListBlank.cons 1 (ListBlank.cons 1 ((([1] : List (Fin 2)) ^ (b + 1)) +>
          (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R)))))))) [target]⊢⁺
        (((encStack (bumpHead (bumpHead L))).cons 0) {{C}}>
          ((([1] : List (Fin 2)) ^ (b + 1)) +>
            (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R)))))) := by
    rw [← encStack_cons_one, ← encStack_cons_one]
    bb_steps
  have h_walkC := walk_C_right (b + 1) ((encStack (bumpHead (bumpHead L))).cons 0)
    (ListBlank.cons 0 (ListBlank.cons 0 (encStack (d :: R))))
  have h_end := (h_e.trans h_mid).trans_star h_walkC
  rw [bump2_eq]
  simpa only [encStack, list_pow_zero, ListBlank.append_nil] using h_end

private theorem reaches_stepZero (b d : ℕ) (L R : List ℕ) :
    (encode (.CR 0 b L d R)) [target]⊢⁺ (encode (stepZero b d L R)) := by
  rw [← cfgCR_eq_encode]
  rcases b with _ | _ | b'
  · simp only [stepZero]
    have h1 := rule_CR_zero_zero d L R
    rw [← bump2_eq] at h1
    exact h1.trans (rule_B_cons (bump2 L).1 (d + 1) (bump2 L).2 R)
  · simp only [stepZero]
    have h1 := rule_CR_zero_one d L R
    rw [← bump2_eq] at h1
    have h2 := rule_B_cons (bump2 L).1 0 (bump2 L).2 (d :: R)
    simpa [bump1] using h1.trans h2
  · simp only [stepZero]
    exact rule_CR_zero_ge2 b' d L R

private theorem rule_CR_ge2 (a b d : ℕ) (L R : List ℕ) :
    (encode (.CR (a + 2) b L d R)) [target]⊢⁺ (cfgB ((a + 1) :: b :: L) (d :: R)) := by
  simp only [encode, cfgB]
  rw [encStack_succ (a + 1) (b :: L), encStack_succ a (b :: L)]
  simp only [encStack]
  rw [ListBlank.append_pow_succ]
  bb_steps

private theorem halt_CR_one_succ (b d : ℕ) (L R : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.CR 1 b L (d + 1) R)) cfg' ∧
      (step target cfg').isNone := by
  refine ⟨Cfg.headRight A (encStack ((b + 4) :: L))
    (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ d)
      (ListBlank.cons 0 (encStack R)))), ?_, ?_⟩
  · have h :
        (encode (.CR 1 b L (d + 1) R)) [target]⊢⁺
          Cfg.headRight A (encStack ((b + 4) :: L))
            (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ d)
              (ListBlank.cons 0 (encStack R)))) := by
      simp only [encode]
      rw [encStack_succ 0 (b :: L), encStack_zero (b :: L),
        encStack_succ (b + 3) L, encStack_succ (b + 2) L, encStack_succ (b + 1) L,
        encStack_succ b L, ListBlank.append_pow_succ]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_CR_one_zero (b : ℕ) (L R₁ : List ℕ) :
    (encode (.CR 1 b L 0 R₁)) [target]⊢⁺ (encode (stepOne b L R₁)) := by
  rcases R₁ with _ | ⟨_ | e, R₂⟩
  · have h1 : (encode (.CR 1 b L 0 [])) [target]⊢⁺ (cfgB ((b + 5) :: L) []) := by
      simp only [encode, cfgB]
      rw [encStack_succ 0 (b :: L), encStack_zero (b :: L),
        encStack_succ (b + 4) L, encStack_succ (b + 3) L, encStack_succ (b + 2) L,
        encStack_succ (b + 1) L, encStack_succ b L]
      simp only [encStack, list_pow_zero, ListBlank.append_nil]
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := rule_B_cons_nil (b + 5) L
    have h3 := rule_B_cons (b + 5) 0 L []
    simpa [stepOne, bump1] using (h1.trans h2).trans h3
  · rcases R₂ with _ | ⟨r₂, R₃⟩
    · have h1 : (encode (.CR 1 b L 0 [0])) [target]⊢⁺ (cfgB ((b + 5) :: L) []) := by
        simp only [encode, cfgB]
        rw [encStack_succ 0 (b :: L), encStack_zero (b :: L),
          encStack_succ (b + 4) L, encStack_succ (b + 3) L, encStack_succ (b + 2) L,
          encStack_succ (b + 1) L, encStack_succ b L, encStack_zero []]
        simp only [encStack, list_pow_zero, ListBlank.append_nil]
        rw [ListBlank.append_pow_succ]
        bb_steps
      have h2 := rule_B_cons_nil (b + 5) L
      have h3 := rule_B_cons (b + 5) 0 L []
      simpa [stepOne, bump1] using (h1.trans h2).trans h3
    · have h1 :
          (encode (.CR 1 b L 0 (0 :: r₂ :: R₃))) [target]⊢⁺
            (cfgB ((b + 5) :: L) ((r₂ + 1) :: R₃)) := by
        simp only [encode, cfgB]
        rw [encStack_succ 0 (b :: L), encStack_zero (b :: L),
          encStack_succ (b + 4) L, encStack_succ (b + 3) L, encStack_succ (b + 2) L,
          encStack_succ (b + 1) L, encStack_succ b L, encStack_zero (r₂ :: R₃),
          encStack_succ r₂ R₃]
        simp only [encStack, list_pow_zero, ListBlank.append_nil]
        rw [ListBlank.append_pow_succ]
        bb_steps
      exact h1.trans (rule_B_cons (b + 5) (r₂ + 1) L R₃)
  · have h1 :
        (encode (.CR 1 b L 0 ((e + 1) :: R₂))) [target]⊢⁺ (cfgB ((b + 5) :: L) (e :: R₂)) := by
      simp only [encode, cfgB]
      rw [encStack_succ 0 (b :: L), encStack_zero (b :: L),
        encStack_succ (b + 4) L, encStack_succ (b + 3) L, encStack_succ (b + 2) L,
        encStack_succ (b + 1) L, encStack_succ b L, encStack_succ e R₂]
      simp only [encStack, list_pow_zero, ListBlank.append_nil]
      rw [ListBlank.append_pow_succ, ListBlank.append_pow_succ]
      bb_steps
    exact h1.trans (rule_B_cons (b + 5) e L R₂)

/-! ## Stride-3 Countdown and Accelerated Step Verification -/

private theorem peel_three_step (a b : ℕ) (L R : List ℕ) :
    (encode (.CR (a + 3) b L 0 R)) [target]⊢⁺ (encode (.CR a (b + 2) L 0 (bumpHead R))) := by
  have h1 := rule_CR_ge2 (a + 1) b 0 L R
  have h2 := rule_B_cons (a + 2) 0 (b :: L) R
  have h3 := rule_CR_zero_ge2 a (bump1 R).1 (b :: L) (bump1 R).2
  simp only [bump2] at h3
  rw [bump1_eq] at h3
  exact (h1.trans h2).trans h3

private theorem peel_three_loop (q r b : ℕ) (L R : List ℕ) :
    (encode (.CR (r + 3 * q) b L 0 R)) [target]⊢*
      (encode (.CR r (b + 2 * q) L 0 (bumpHeadBy q R))) := by
  induction q generalizing b R with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, bumpHeadBy]
    bb_refl
  | succ q ih =>
    rw [show r + 3 * (q + 1) = (r + 3 * q) + 3 by omega, bumpHeadBy]
    have h1 := peel_three_step (r + 3 * q) b L R
    have h2 := ih (b + 2) (bumpHead R)
    rw [show b + 2 + 2 * q = b + 2 * (q + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

private theorem rule_CR_two_zero (b : ℕ) (L R₁ : List ℕ) :
    (encode (.CR 2 b L 0 R₁)) [target]⊢⁺
      (encode (.CR 0 (b + 2) L ((bump1 R₁).1 + 1) (bump1 R₁).2)) := by
  have h1 := rule_CR_ge2 0 b 0 L R₁
  have h2 := rule_B_cons 1 0 (b :: L) R₁
  have h3 := reaches_stepZero 1 (bump1 R₁).1 (b :: L) (bump1 R₁).2
  simpa [stepZero, bump2] using (h1.trans h2).trans h3

private theorem init_reaches_start : (init []) [target]⊢* (encode start) := by
  have h : (init []) [target]⊢⁺ (encode start) := by
    simp only [start, encode]
    rw [encStack_zero, encStack_zero]
    simp only [encStack, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h.to_star

private theorem step_accel (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨a, b, L, _ | d, R⟩
  · have h_div : a = a % 3 + 3 * (a / 3) := (Nat.mod_add_div a 3).symm
    have h_loop := peel_three_loop (a / 3) (a % 3) b L R
    rw [← h_div] at h_loop
    have h_mod : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
    rcases h_mod with hm0 | hm1 | hm2
    · simp only [next, hm0]
      rw [hm0] at h_loop
      exact h_loop.trans_plus (reaches_stepZero (b + 2 * (a / 3)) 0 L (bumpHeadBy (a / 3) R))
    · simp only [next, hm1]
      rw [hm1] at h_loop
      exact h_loop.trans_plus (rule_CR_one_zero (b + 2 * (a / 3)) L (bumpHeadBy (a / 3) R))
    · simp only [next, hm2]
      rw [hm2] at h_loop
      exact h_loop.trans_plus (rule_CR_two_zero (b + 2 * (a / 3)) L (bumpHeadBy (a / 3) R))
  · rcases a with _ | _ | a'
    · simp only [next]
      exact reaches_stepZero b (d + 1) L R
    · simp only [next]
      exact halt_CR_one_succ b d L R
    · simp only [next]
      exact (rule_CR_ge2 a' b (d + 1) L R).trans (rule_B_cons (a' + 1) (d + 1) (b :: L) R)

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next :=
  IsValidAcceleration.of_step init_reaches_start fun s => by
    cases h : next s <;> simpa [h] using step_accel s

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RBHHH_0RC0LD_1LB1RC_0LE0LF_1RD1LE_1RF1RA
