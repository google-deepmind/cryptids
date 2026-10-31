/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $F(1, 0, [], 0, [])$ in 16 raw steps, where:
- $C(a, b, L, r, R)$ has state `C` reading `0` between `(a + 1) :: b :: L` and `1^r 0` + `R`.
- $F(a, b, L, r, R)$ has state `F` reading `0` between `a :: b :: L` and `1^r 0` + `R`.

## Accelerated Transition Rules

```text
C(0, 0, L, r, R)                  -> Halt
C(0, 2k + 1, [], r, R)            -> F(2k + 3, 0, [], r, R)
C(0, 2k + 1, c :: L, r, R)        -> F(2k + 3, c + 1, L, r, R)
C(0, 2k + 2, [], r, R)            -> C(2k, 0, [], 0, (r + 1) :: R)
C(0, 2k + 2, c :: L, r, R)        -> C(2k, c + 1, L, 0, (r + 1) :: R)
C(a + 1, b, L, r, R)              -> F(a, b, L, 0, r :: R)

a' := a + 2 * (r / 2)
F(a, b, L, 2m, [])                -> C(a' + 2, b, L, 0, [])
F(a, b, L, 2m, [0])               -> F(0, b + 1, L, a', [])
F(a, b, L, 2m, 0 :: e :: R)       -> F(a' + 3, b + 1, L, e, R)           (a' even)
F(a, b, L, 2m, 0 :: e :: R)       -> C(2 * (a' / 2), b + 1, L, 0, (e + 1) :: R) (a' odd)
F(a, b, L, 2m, (d + 1) :: R)      -> F(0, b + 1, L, a', d :: R)
F(a, b, L, 2m + 1, [])            -> C(a', b, L, 0, [0])
F(a, b, L, 2m + 1, e :: R)        -> F(0, a' + 1, b :: L, e, R)

Start: F(1, 0, [], 0, []), reached after 16 raw TM steps
```

Contracting every intermediate $C$-chain via structural recursion on $L$ (`exitC`) eliminates
state $C$ completely, yielding a single-constructor high-level transition system
$F_{\mathrm{HL}}(a, b, L, r, R)$ starting at $F_{\mathrm{HL}}(1, 0, [], 0, [])$.

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem S3 — trigger **EQ (depth-two gate)**, growth —, shield partial
(`ValidStack129` kills $\mathrm{CR}\,[]\,R$ and all $0::0::L$ states).

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting (weak race).

*Hazard:* 232 depth-two visits in $10^7$ steps, $a\in\lbrace 3,4,7,9,11,15 \rbrace$ on 8 of them
($a=1$ halts); $\approx2$ expected halts, 0 observed

*Simulated horizon:* $10^7$ macro-steps (exact)

*Why it is hard:* two-mode halving sweeper; halts iff $L$ drains to $[1,0]$ in $\mathrm{CR}$

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_1RC0LE_1LD1LA_---0LC_1RF1LE_1RA0RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic state space for the accelerated transition system of `target`. -/
inductive State where
  /-- State `C` on `0` with left stack `(a + 1) :: b :: L` and right run `1^r 0` + `R`. -/
  | C (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  /-- State `F` on `0` with left stack `a :: b :: L` and right run `1^r 0` + `R`. -/
  | F (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial symbolic state `F(1, 0, [], 0, [])`, reached from `init []` in 16 raw steps. -/
def start : State := .F 1 0 [] 0 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b L r R =>
      Cfg.headRight C (encStack ((a + 1) :: b :: L))
        (ListBlank.cons 0
          (ListBlank.append (([1] : List (Fin 2)) ^ r) (ListBlank.cons 0 (encStack R))))
  | .F a b L r R =>
      Cfg.headRight F (encStack (a :: b :: L))
        (ListBlank.cons 0
          (ListBlank.append (([1] : List (Fin 2)) ^ r) (ListBlank.cons 0 (encStack R))))

/-- Accelerated step function (`none` indicates halting, reached only at `C(0, 0, L, r, R)`). -/
def next : State → Option State
  | .C 0 0 _ _ _ => none
  | .C 0 (b + 1) L r R =>
      if b % 2 = 0 then
        List.casesOn L (some (.F (b + 3) 0 [] r R))
          fun c L' => some (.F (b + 3) (c + 1) L' r R)
      else
        List.casesOn L (some (.C (2 * (b / 2)) 0 [] 0 ((r + 1) :: R)))
          fun c L' => some (.C (2 * (b / 2)) (c + 1) L' 0 ((r + 1) :: R))
  | .C (a + 1) b L r R => some (.F a b L 0 (r :: R))
  | .F a b L r R =>
      let a' := a + 2 * (r / 2)
      if r % 2 = 0 then
        match R with
        | [] => some (.C (a' + 2) b L 0 [])
        | 0 :: [] => some (.F 0 (b + 1) L a' [])
        | 0 :: e :: R' =>
            if a' % 2 = 0 then
              some (.F (a' + 3) (b + 1) L e R')
            else
              some (.C (2 * (a' / 2)) (b + 1) L 0 ((e + 1) :: R'))
        | (d + 1) :: R' => some (.F 0 (b + 1) L a' (d :: R'))
      else
        List.casesOn R (some (.C a' b L 0 [0]))
          fun e R' => some (.F 0 (a' + 1) (b :: L) e R')

/-! ## Stack Encoding Helpers -/

private def encRightTail (r : ℕ) (R : List ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (([1] : List (Fin 2)) ^ r) (ListBlank.cons 0 (encStack R))

private theorem encStack_cons_one (L : List ℕ) :
    ListBlank.cons 1 (encStack L) = encStack (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack]
  | cons c L' =>
    simp only [bumpHead, encStack, ListBlank.append_pow_succ,
      ListBlank.append_cons, ListBlank.append_nil]

private theorem cons_one_encRightTail (r : ℕ) (R : List ℕ) :
    ListBlank.cons 1 (encRightTail r R) = encStack (r :: R) := by
  simp only [encRightTail, encStack, ListBlank.append_pow_succ,
    ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_zero_cons (R : List ℕ) :
    encStack (0 :: R) = ListBlank.cons 1 (ListBlank.cons 0 (encStack R)) := by
  simp [encStack]

private theorem encStack_succ_cons (d : ℕ) (R : List ℕ) :
    encStack ((d + 1) :: R) = ListBlank.cons 1 (encStack (d :: R)) := by
  simp [encStack, ListBlank.append_pow_succ]

/-! ## Inductive Walk and Peel Loops -/

private theorem walk_E (k : ℕ) (l r : ListBlank (Fin 2)) :
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

private theorem loop_F_peel_two (k a : ℕ) (L : List ℕ) (m : ℕ) (r : ListBlank (Fin 2)) :
    (Cfg.headRight F (encStack (a :: L))
      (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ (2 * k + m)) +> r))) [target]⊢*
      (Cfg.headRight F (encStack ((a + 2 * k) :: L))
        (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ m) +> r))) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add]
    bb_refl
  | succ k ih =>
    rw [show 2 * (k + 1) + m = 2 + (2 * k + m) by omega,
      ListBlank.append_pow_add [1] 2 (2 * k + m) r]
    have h1 :
        (Cfg.headRight F (encStack (a :: L))
          (ListBlank.cons 0 (([1] : List (Fin 2)) ^ 2 +>
            ((([1] : List (Fin 2)) ^ (2 * k + m)) +> r)))) [target]⊢⁺
          (Cfg.headRight F (encStack ((a + 2) :: L))
            (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ (2 * k + m)) +> r))) := by
      simp only [encStack]
      rw [show a + 2 + 1 = 2 + (a + 1) by omega, ListBlank.append_pow_add _ 2 (a + 1)]
      change (Cfg.headRight F _ (ListBlank.cons 0 ([1, 1] +> _))) [target]⊢⁺
        Cfg.headRight F ([1, 1] +> _) _
      bb_steps
    have h2 := ih (a + 2)
    rw [show a + 2 + 2 * k = a + 2 * (k + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

/-! ## Shared Block-Shift and Parity-Peel Lemmas -/

private theorem f_zero_one_gen (a : ℕ) (L : List ℕ) (r_tail : ListBlank (Fin 2)) :
    (Cfg.headRight F (encStack (a :: L))
      (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 r_tail)))) [target]⊢⁺
      (Cfg.headRight F (encStack (0 :: bumpHead L))
        (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ a) +> (ListBlank.cons 0 r_tail)))) := by
  have h_pre :
      (Cfg.headRight F (encStack (a :: L))
        (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 1 r_tail)))) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (2 + (a + 1)))) <{{E}}
          (ListBlank.cons 0 r_tail)) := by
    simp only [encStack]
    rw [ListBlank.append_pow_add _ 2 (a + 1)]
    change _ [target]⊢⁺ (([1, 1] +> _) <{{E}} _)
    bb_steps
  have h_walk := walk_E (2 + (a + 1)) ((encStack L).cons 0) (ListBlank.cons 0 r_tail)
  have h_post :
      (((encStack L).cons 0) <{{E}}
        ((([1] : List (Fin 2)) ^ (2 + (a + 1))) +> (ListBlank.cons 0 r_tail))) [target]⊢⁺
        (Cfg.headRight F (encStack (0 :: bumpHead L))
          (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ a) +> (ListBlank.cons 0 r_tail)))) := by
    rw [show 2 + (a + 1) = 3 + a by omega, ListBlank.append_pow_add _ 3 a]
    simp only [encStack, Nat.zero_add, list_pow_one]
    rw [← encStack_cons_one L]
    change (_ <{{E}} ([1, 1, 1] +> _)) [target]⊢⁺ _
    bb_steps
  exact (h_pre.trans_star h_walk).trans h_post

private theorem a_zero_to_f_peel (a : ℕ) (L R_rest : List ℕ) :
    (Cfg.headRight A (encStack ((a + 1) :: L))
      (ListBlank.cons 0 (encStack (0 :: R_rest)))) [target]⊢⁺
      (Cfg.headRight F (encStack (0 :: bumpHead L))
        (ListBlank.cons 0
          ((([1] : List (Fin 2)) ^ a) +>
            (ListBlank.cons 0 (ListBlank.cons 0 (encStack R_rest)))))) := by
  have h_pre :
      (Cfg.headRight A (encStack ((a + 1) :: L))
        (ListBlank.cons 0 (encStack (0 :: R_rest)))) [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (1 + (a + 2)))) <{{E}}
          (ListBlank.cons 0 (ListBlank.cons 0 (encStack R_rest)))) := by
    simp only [encStack, Nat.zero_add, list_pow_one]
    rw [ListBlank.append_pow_add _ 1 (a + 2)]
    change _ [target]⊢⁺ (([1] +> _) <{{E}} _)
    bb_steps
  have h_walk :=
    walk_E (1 + (a + 2)) ((encStack L).cons 0)
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack R_rest)))
  have h_post :
      (((encStack L).cons 0) <{{E}}
        ((([1] : List (Fin 2)) ^ (1 + (a + 2))) +>
          (ListBlank.cons 0 (ListBlank.cons 0 (encStack R_rest))))) [target]⊢⁺
        (Cfg.headRight F (encStack (0 :: bumpHead L))
          (ListBlank.cons 0
            ((([1] : List (Fin 2)) ^ a) +>
              (ListBlank.cons 0 (ListBlank.cons 0 (encStack R_rest)))))) := by
    rw [show 1 + (a + 2) = 3 + a by omega, ListBlank.append_pow_add _ 3 a]
    simp only [encStack, Nat.zero_add, list_pow_one]
    rw [← encStack_cons_one L]
    change (_ <{{E}} ([1, 1, 1] +> _)) [target]⊢⁺ _
    bb_steps
  exact (h_pre.trans_star h_walk).trans h_post

private theorem a_zero_peel_even (k e : ℕ) (L R : List ℕ) :
    (Cfg.headRight A (encStack ((2 * k + 1) :: L))
      (ListBlank.cons 0 (encStack (0 :: e :: R)))) [target]⊢⁺
      (Cfg.headRight F (encStack ((2 * k + 3) :: bumpHead L))
        (ListBlank.cons 0 (encRightTail e R))) := by
  have h1 := a_zero_to_f_peel (2 * k) L (e :: R)
  have h2 :=
    loop_F_peel_two k 0 (bumpHead L) 0
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack (e :: R))))
  simp only [Nat.zero_add, list_pow_zero, ListBlank.append_nil] at h2
  have h3 :
      (Cfg.headRight F (encStack ((2 * k) :: bumpHead L))
        (ListBlank.cons 0 (ListBlank.cons 0 (ListBlank.cons 0 (encStack (e :: R)))))) [target]⊢⁺
        (Cfg.headRight F (encStack ((2 * k + 3) :: bumpHead L))
          (ListBlank.cons 0 (encRightTail e R))) := by
    rw [← cons_one_encRightTail e R]
    simp only [encStack]
    rw [show 2 * k + 3 + 1 = 3 + (2 * k + 1) by omega,
      ListBlank.append_pow_add _ 3 (2 * k + 1)]
    change _ [target]⊢⁺ Cfg.headRight F ([1, 1, 1] +> _) _
    bb_steps
  exact (h1.trans_star h2).trans h3

private theorem a_zero_peel_odd_shift (k e : ℕ) (L R : List ℕ) :
    (Cfg.headRight A (encStack ((2 * k + 2) :: L))
      (ListBlank.cons 0 (encStack (0 :: e :: R)))) [target]⊢⁺
      (Cfg.headRight C (encStack ((2 * k + 1) :: bumpHead L))
        (ListBlank.cons 0 (encRightTail 0 ((e + 1) :: R)))) := by
  have h1 := a_zero_to_f_peel (2 * k + 1) L (e :: R)
  have h2 :=
    loop_F_peel_two k 0 (bumpHead L) 1
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack (e :: R))))
  simp only [Nat.zero_add, list_pow_one] at h2
  have h3 :
      (Cfg.headRight F (encStack ((2 * k) :: bumpHead L))
        (ListBlank.cons 0
          ([1] +> (ListBlank.cons 0 (ListBlank.cons 0 (encStack (e :: R))))))) [target]⊢⁺
        (Cfg.headRight C (encStack ((2 * k + 1) :: bumpHead L))
          (ListBlank.cons 0 (encRightTail 0 ((e + 1) :: R)))) := by
    simp only [encRightTail, list_pow_zero, ListBlank.append_nil, encStack_succ_cons]
    simp only [encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (h1.trans_star h2).trans h3

/-! ## Local Mode Rules -/

private theorem halt_C_zero_zero (L : List ℕ) (r : ℕ) (R : List ℕ) :
    ∃ cfg', ReachesStar target (encode (.C 0 0 L r R)) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight D (encStack (bumpHead L))
    (ListBlank.cons 0 ([1, 0, 1, 1] +> encRightTail r R)), ?_, ?_⟩
  · have h :
        ReachesPlus target (encode (.C 0 0 L r R))
          (Cfg.headRight D (encStack (bumpHead L))
            (ListBlank.cons 0 ([1, 0, 1, 1] +> encRightTail r R))) := by
      change (Cfg.headRight C (encStack (1 :: 0 :: L))
        (ListBlank.cons 0 (encRightTail r R))) [target]⊢⁺ _
      simp only [encStack, Nat.zero_add, list_pow_succ, list_pow_zero]
      rw [← encStack_cons_one L]
      bb_steps
    exact h.to_star
  · bb_halt

private theorem rule_C_zero_even (k : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (encode (.C 0 (2 * k + 1) L r R)) [target]⊢⁺
      (Cfg.headRight F (encStack ((2 * k + 3) :: bumpHead L))
        (ListBlank.cons 0 (encRightTail r R))) := by
  have h1 :
      (encode (.C 0 (2 * k + 1) L r R)) [target]⊢⁺
        (Cfg.headRight A (encStack ((2 * k + 1) :: L))
          (ListBlank.cons 0 (encStack (0 :: r :: R)))) := by
    change (Cfg.headRight C (encStack (1 :: (2 * k + 1) :: L))
      (ListBlank.cons 0 (encRightTail r R))) [target]⊢⁺ _
    rw [encStack_zero_cons, ← cons_one_encRightTail r R]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h1.trans (a_zero_peel_even k r L R)

private theorem rule_C_zero_odd (k : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (encode (.C 0 (2 * k + 2) L r R)) [target]⊢⁺
      (Cfg.headRight C (encStack ((2 * k + 1) :: bumpHead L))
        (ListBlank.cons 0 (encRightTail 0 ((r + 1) :: R)))) := by
  have h1 :
      (encode (.C 0 (2 * k + 2) L r R)) [target]⊢⁺
        (Cfg.headRight A (encStack ((2 * k + 2) :: L))
          (ListBlank.cons 0 (encStack (0 :: r :: R)))) := by
    change (Cfg.headRight C (encStack (1 :: (2 * k + 2) :: L))
      (ListBlank.cons 0 (encRightTail r R))) [target]⊢⁺ _
    rw [encStack_zero_cons, ← cons_one_encRightTail r R]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h1.trans (a_zero_peel_odd_shift k r L R)

private theorem rule_C_succ (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) :
    (encode (.C (a + 1) b L r R)) [target]⊢⁺ (encode (.F a b L 0 (r :: R))) := by
  change (Cfg.headRight C (encStack ((a + 2) :: b :: L))
    (ListBlank.cons 0 (encRightTail r R))) [target]⊢⁺
    Cfg.headRight F (encStack (a :: b :: L))
      (ListBlank.cons 0 (encRightTail 0 (r :: R)))
  simp only [encRightTail, list_pow_zero, ListBlank.append_nil]
  rw [← cons_one_encRightTail r R]
  simp only [encStack]
  rw [show a + 2 + 1 = 3 + a by omega, ListBlank.append_pow_add [1] 3 a,
    ListBlank.append_pow_succ [1] a]
  change (Cfg.headRight C ([1, 1, 1] +> _) _) [target]⊢⁺ _
  bb_steps

private theorem rule_F_zero_nil (a b : ℕ) (L : List ℕ) :
    (encode (.F a b L 0 [])) [target]⊢⁺ (encode (.C (a + 2) b L 0 [])) := by
  simp only [encode, list_pow_zero, ListBlank.append_nil, encStack]
  rw [show a + 2 + 1 + 1 = 3 + (a + 1) by omega, ListBlank.append_pow_add [1] 3 (a + 1)]
  change _ [target]⊢⁺ Cfg.headRight C ([1, 1, 1] +> _) _
  bb_steps

private theorem rule_F_zero_zero_nil (a b : ℕ) (L : List ℕ) :
    (encode (.F a b L 0 [0])) [target]⊢⁺ (encode (.F 0 (b + 1) L a [])) := by
  have h0 : encStack [0] = ListBlank.cons 1 default := by simp [encStack]
  change (Cfg.headRight F (encStack (a :: b :: L))
    (ListBlank.cons 0 (ListBlank.append ([] : List (Fin 2))
      (ListBlank.cons 0 (encStack [0]))))) [target]⊢⁺
    Cfg.headRight F (encStack (0 :: bumpHead (b :: L)))
      (ListBlank.cons 0 ((([1] : List (Fin 2)) ^ a) +> (ListBlank.cons 0 default)))
  rw [ListBlank.append_nil, h0]
  exact f_zero_one_gen a (b :: L) default

private theorem rule_F_zero_zero_cons_even (k b e : ℕ) (L R : List ℕ) :
    (encode (.F (2 * k) b L 0 (0 :: e :: R))) [target]⊢⁺
      (encode (.F (2 * k + 3) (b + 1) L e R)) := by
  have h1 :
      (encode (.F (2 * k) b L 0 (0 :: e :: R))) [target]⊢⁺
        (Cfg.headRight A (encStack ((2 * k + 1) :: b :: L))
          (ListBlank.cons 0 (encStack (0 :: e :: R)))) := by
    change (Cfg.headRight F (encStack ((2 * k) :: b :: L))
      (ListBlank.cons 0 (encRightTail 0 (0 :: e :: R)))) [target]⊢⁺ _
    simp only [encRightTail, list_pow_zero, ListBlank.append_nil, encStack,
      Nat.zero_add, list_pow_one, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans (a_zero_peel_even k e (b :: L) R)

private theorem rule_F_zero_zero_cons_odd (k b e : ℕ) (L R : List ℕ) :
    (encode (.F (2 * k + 1) b L 0 (0 :: e :: R))) [target]⊢⁺
      (encode (.C (2 * k) (b + 1) L 0 ((e + 1) :: R))) := by
  have h1 :
      (encode (.F (2 * k + 1) b L 0 (0 :: e :: R))) [target]⊢⁺
        (Cfg.headRight A (encStack ((2 * k + 2) :: b :: L))
          (ListBlank.cons 0 (encStack (0 :: e :: R)))) := by
    change (Cfg.headRight F (encStack ((2 * k + 1) :: b :: L))
      (ListBlank.cons 0 (encRightTail 0 (0 :: e :: R)))) [target]⊢⁺ _
    simp only [encRightTail, list_pow_zero, ListBlank.append_nil, encStack,
      Nat.zero_add, list_pow_one, ListBlank.append_pow_succ]
    bb_steps
  exact h1.trans (a_zero_peel_odd_shift k e (b :: L) R)

private theorem rule_F_zero_succ (a b d : ℕ) (L R : List ℕ) :
    (encode (.F a b L 0 ((d + 1) :: R))) [target]⊢⁺
      (encode (.F 0 (b + 1) L a (d :: R))) := by
  change (Cfg.headRight F (encStack (a :: b :: L))
    (ListBlank.cons 0 (encRightTail 0 ((d + 1) :: R)))) [target]⊢⁺
    Cfg.headRight F (encStack (0 :: bumpHead (b :: L)))
      (ListBlank.cons 0 (encRightTail a (d :: R)))
  simp only [encRightTail, list_pow_zero, ListBlank.append_nil, encStack_succ_cons]
  exact f_zero_one_gen a (b :: L) (encStack (d :: R))

private theorem rule_F_one_nil (a b : ℕ) (L : List ℕ) :
    (encode (.F a b L 1 [])) [target]⊢⁺ (encode (.C a b L 0 [0])) := by
  simp only [encode, list_pow_one, list_pow_zero, ListBlank.append_nil,
    encStack, Nat.zero_add]
  bb_steps

private theorem rule_F_one_cons (a b e : ℕ) (L R : List ℕ) :
    (encode (.F a b L 1 (e :: R))) [target]⊢⁺
      (encode (.F 0 (a + 1) (b :: L) e R)) := by
  change (Cfg.headRight F (encStack (a :: b :: L))
    (ListBlank.cons 0 (encRightTail 1 (e :: R)))) [target]⊢⁺
    Cfg.headRight F (encStack (0 :: (a + 1) :: b :: L))
      (ListBlank.cons 0 (encRightTail e R))
  simp only [encRightTail, list_pow_one]
  rw [← cons_one_encRightTail e R]
  simp only [encRightTail, encStack, Nat.zero_add, list_pow_one, ListBlank.append_pow_succ]
  bb_steps

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  rcases s with ⟨_ | a, b, L, r, R⟩ | ⟨a, b, L, r, R⟩
  · rcases b with _ | b
    · exact halt_C_zero_zero L r R
    · by_cases hb : b % 2 = 0
      · have hbe : b + 1 = 2 * (b / 2) + 1 := by omega
        have h1 := rule_C_zero_even (b / 2) L r R
        rw [← hbe, show 2 * (b / 2) + 3 = b + 3 by omega] at h1
        rcases L with _ | ⟨c, L'⟩
        · simpa only [next, hb, ↓reduceIte, bumpHead, encode, encRightTail] using h1
        · simpa only [next, hb, ↓reduceIte, bumpHead, encode, encRightTail] using h1
      · have hbo : b + 1 = 2 * (b / 2) + 2 := by omega
        have h1 := rule_C_zero_odd (b / 2) L r R
        rw [← hbo] at h1
        rcases L with _ | ⟨c, L'⟩
        · simpa only [next, hb, ↓reduceIte, bumpHead, encode, encRightTail] using h1
        · simpa only [next, hb, ↓reduceIte, bumpHead, encode, encRightTail] using h1
  · simp only [next]
    exact rule_C_succ a b L r R
  · by_cases hr : r % 2 = 0
    · have hre : r = 2 * (r / 2) + 0 := by omega
      have h_peel :
          ReachesStar target (encode (.F a b L r R))
            (encode (.F (a + 2 * (r / 2)) b L 0 R)) := by
        simpa only [encode, ← hre] using
          loop_F_peel_two (r / 2) a (b :: L) 0 (ListBlank.cons 0 (encStack R))
      rcases R with _ | ⟨_ | d, R'⟩
      · simp only [next, hr, ↓reduceIte]
        exact h_peel.trans_plus (rule_F_zero_nil (a + 2 * (r / 2)) b L)
      · rcases R' with _ | ⟨e, R''⟩
        · simp only [next, hr, ↓reduceIte]
          exact h_peel.trans_plus (rule_F_zero_zero_nil (a + 2 * (r / 2)) b L)
        · by_cases ha : (a + 2 * (r / 2)) % 2 = 0
          · have hae : a + 2 * (r / 2) = 2 * ((a + 2 * (r / 2)) / 2) := by omega
            simp only [next, hr, ha, ↓reduceIte]
            have h2 := rule_F_zero_zero_cons_even ((a + 2 * (r / 2)) / 2) b e L R''
            rw [← hae] at h2
            exact h_peel.trans_plus h2
          · have hao : a + 2 * (r / 2) = 2 * ((a + 2 * (r / 2)) / 2) + 1 := by omega
            simp only [next, hr, ha, ↓reduceIte]
            have h2 := rule_F_zero_zero_cons_odd ((a + 2 * (r / 2)) / 2) b e L R''
            rw [← hao] at h2
            exact h_peel.trans_plus h2
      · simp only [next, hr, ↓reduceIte]
        exact h_peel.trans_plus (rule_F_zero_succ (a + 2 * (r / 2)) b d L R')
    · have hro : r = 2 * (r / 2) + 1 := by omega
      have h_peel :
          ReachesStar target (encode (.F a b L r R))
            (encode (.F (a + 2 * (r / 2)) b L 1 R)) := by
        simpa only [encode, ← hro] using
          loop_F_peel_two (r / 2) a (b :: L) 1 (ListBlank.cons 0 (encStack R))
      rcases R with _ | ⟨e, R'⟩
      · simp only [next, hr, ↓reduceIte]
        exact h_peel.trans_plus (rule_F_one_nil (a + 2 * (r / 2)) b L)
      · simp only [next, hr, ↓reduceIte]
        exact h_peel.trans_plus (rule_F_one_cons (a + 2 * (r / 2)) b e L R')

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Acceleration -/

/-- Reduced single-constructor state space $F_{\mathrm{HL}}(a, b, L, r, R)$ eliminating state
`C`. -/
inductive HighLevelState where
  /-- State `F` on `0` with left stack `a :: b :: L` and right run `1^r 0` + `R`. -/
  | F (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level state $F_{\mathrm{HL}}(1, 0, [], 0, [])$. -/
def highLevelStart : HighLevelState := .F 1 0 [] 0 []

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .F a b L r R => .F a b L r R

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- Contract intermediate `C(a, b, L, r, R)` steps until re-entering `F` or halting. -/
def exitC (a b : ℕ) (L : List ℕ) (r : ℕ) (R : List ℕ) : Option HighLevelState :=
  List.rec
    (fun a b r R =>
      if a ≥ 1 then some (.F (a - 1) b [] 0 (r :: R))
      else if b = 0 then none
      else
        let b' := b - 1
        if b' % 2 = 0 then some (.F (b' + 3) 0 [] r R)
        else if b' = 1 then none
        else some (.F (2 * (b' / 2) - 1) 0 [] 0 (0 :: (r + 1) :: R)))
    (fun c L' ih a b r R =>
      if a ≥ 1 then some (.F (a - 1) b (c :: L') 0 (r :: R))
      else if b = 0 then none
      else
        let b' := b - 1
        if b' % 2 = 0 then some (.F (b' + 3) (c + 1) L' r R)
        else if b' = 1 then ih 0 (c + 1) 0 ((r + 1) :: R)
        else some (.F (2 * (b' / 2) - 1) (c + 1) L' 0 (0 :: (r + 1) :: R)))
    L a b r R

/-- High-level accelerated transition function on $F_{\mathrm{HL}}(a, b, L, r, R)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .F a b L r R =>
    let a' := a + 2 * (r / 2)
    if r % 2 = 0 then
      List.casesOn R (exitC (a' + 2) b L 0 []) fun d R' =>
        if d = 0 then
          List.casesOn R' (some (.F 0 (b + 1) L a' [])) fun e R'' =>
            if a' % 2 = 0 then
              some (.F (a' + 3) (b + 1) L e R'')
            else
              exitC (2 * (a' / 2)) (b + 1) L 0 ((e + 1) :: R'')
        else
          some (.F 0 (b + 1) L a' ((d - 1) :: R'))
    else
      List.casesOn R (exitC a' b L 0 [0]) fun e R' =>
        some (.F 0 (a' + 1) (b :: L) e R')

private theorem stepsTo_exitC (L : List ℕ) :
    ∀ (a b r : ℕ) (R : List ℕ),
      CollatzStepsTo next (.C a b L r R) ((exitC a b L r R).map toState) := by
  induction L with
  | nil =>
    intro a b r R
    unfold exitC
    by_cases ha : a ≥ 1
    · simp only [ha, ↓reduceIte, Option.map_some, toState]
      refine CollatzStepsTo.of_eq ?_
      rw [show a = (a - 1) + 1 by omega]
      rfl
    · have ha0 : a = 0 := by omega
      subst ha0
      simp only [ha, ↓reduceIte]
      rcases b with _ | b'
      · exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        by_cases hb0 : b' % 2 = 0
        · simp only [hb0, ↓reduceIte, Option.map_some, toState]
          exact CollatzStepsTo.of_eq (by simp [next, hb0])
        · by_cases hb1 : b' = 1
          · subst hb1
            simp only [hb0, ↓reduceIte, Option.map_none]
            exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
          · simp only [hb0, hb1, ↓reduceIte, Option.map_some, toState]
            have hstep1 : next (.C 0 (b' + 1) [] r R) =
                some (.C (2 * (b' / 2)) 0 [] 0 ((r + 1) :: R)) := by
              simp [next, hb0]
            have hstep2 : next (.C (2 * (b' / 2)) 0 [] 0 ((r + 1) :: R)) =
                some (.F (2 * (b' / 2) - 1) 0 [] 0 (0 :: (r + 1) :: R)) := by
              rw [show 2 * (b' / 2) = (2 * (b' / 2) - 1) + 1 by omega]
              rfl
            exact CollatzStepsTo.head hstep1 (CollatzStepsTo.of_eq hstep2)
  | cons c L' ihL =>
    intro a b r R
    unfold exitC
    by_cases ha : a ≥ 1
    · simp only [ha, ↓reduceIte, Option.map_some, toState]
      refine CollatzStepsTo.of_eq ?_
      rw [show a = (a - 1) + 1 by omega]
      rfl
    · have ha0 : a = 0 := by omega
      subst ha0
      simp only [ha, ↓reduceIte]
      rcases b with _ | b'
      · exact CollatzStepsTo.of_eq rfl
      · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel]
        by_cases hb0 : b' % 2 = 0
        · simp only [hb0, ↓reduceIte, Option.map_some, toState]
          exact CollatzStepsTo.of_eq (by simp [next, hb0])
        · by_cases hb1 : b' = 1
          · subst hb1
            simp only [hb0, ↓reduceIte]
            exact CollatzStepsTo.head rfl (ihL 0 (c + 1) 0 ((r + 1) :: R))
          · simp only [hb0, hb1, ↓reduceIte, Option.map_some, toState]
            have hstep1 : next (.C 0 (b' + 1) (c :: L') r R) =
                some (.C (2 * (b' / 2)) (c + 1) L' 0 ((r + 1) :: R)) := by
              simp [next, hb0]
            have hstep2 : next (.C (2 * (b' / 2)) (c + 1) L' 0 ((r + 1) :: R)) =
                some (.F (2 * (b' / 2) - 1) (c + 1) L' 0 (0 :: (r + 1) :: R)) := by
              rw [show 2 * (b' / 2) = (2 * (b' / 2) - 1) + 1 by omega]
              rfl
            exact CollatzStepsTo.head hstep1 (CollatzStepsTo.of_eq hstep2)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid acceleration of
`target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨a, b, L, r, R⟩
  simp only [toState, highLevelNext]
  by_cases hr : r % 2 = 0
  · simp only [hr, ↓reduceIte]
    rcases R with _ | ⟨_ | d, R'⟩
    · exact CollatzStepsTo.head (by simp [next, hr]) (stepsTo_exitC L _ b 0 [])
    · rcases R' with _ | ⟨e, R''⟩
      · exact CollatzStepsTo.of_eq (by simp [next, hr, toState])
      · by_cases ha' : (a + 2 * (r / 2)) % 2 = 0
        · simp only [↓reduceIte, ha', Option.map_some, toState]
          exact CollatzStepsTo.of_eq (by simp [next, hr, ha'])
        · simp only [↓reduceIte, ha']
          exact CollatzStepsTo.head (by simp [next, hr]; omega)
            (stepsTo_exitC L (2 * ((a + 2 * (r / 2)) / 2)) (b + 1) 0 ((e + 1) :: R''))
    · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Nat.add_sub_cancel,
        Option.map_some, toState]
      exact CollatzStepsTo.of_eq (by simp [next, hr])
  · simp only [hr, ↓reduceIte]
    rcases R with _ | ⟨e, R'⟩
    · exact CollatzStepsTo.head (by simp [next, hr]) (stepsTo_exitC L _ b 0 [0])
    · exact CollatzStepsTo.of_eq (by simp [next, hr, toState])

/-- `target` halts from the blank tape iff `highLevelNext` halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` iff `highLevelNext` halts from
`highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0RB_1RC0LE_1LD1LA_HHH0LC_1RF1LE_1RA0RA
