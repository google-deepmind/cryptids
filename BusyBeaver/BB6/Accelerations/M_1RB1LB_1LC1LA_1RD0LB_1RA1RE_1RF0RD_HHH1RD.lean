/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $E(1, [], 0, [])$ in 6 raw steps, where $E(a, L, d, R)$ has state `E` reading `0` between
`encStack (a :: L)` and `encStack (d :: R)`.

## Accelerated Transition Rules

```text
E(a, L, 0, [])             -> drainLeft(parityMode(a + 3), L, a + 3, [0])
E(a, L, 0, e :: R)         -> drainLeft(flipParityMode(a), L, a + e + 4, R)
E(a, L, 2k + 1, [])        -> Halt
E(a, L, 1, e :: R)         -> E(a + 3, L, e, R)
E(a, L, 2(k + 1) + 1, e::R)-> E(0, 0^k ++ (a + 3) :: L, e, R)
E(a, L, 2k + 2, [])        -> drainLeft(A, 0^k ++ (a + 3) :: L, 0, [0])
E(a, L, 2k + 2, e :: R)    -> drainLeft(A, 0^k ++ (a + 3) :: L, e + 1, R)

drainLeft sweeps L into R and bounces at L = [] via bounceBEmpty, which halts iff R collapses to a
singleton odd digit [2k + 1].

Start: E(1, [], 0, []), reached after 6 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_---1RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Intermediate separator mode during a leftward stack drain (`A`, `B`, or `0`-buffered `BR`). -/
inductive DrainMode where
  /-- State `A` at separator `0`. -/
  | A
  /-- State `B` at separator `0`. -/
  | B
  /-- State `B` at separator `0` with an extra `0` buffered on the right. -/
  | BR
  deriving DecidableEq, Repr

/-- Symbolic state space for the accelerated reservoir-odometer system of `target`. -/
inductive State where
  /-- Canonical configuration `E(a, L, d, R)`: state `E` at `0` between `a :: L` and `d :: R`. -/
  | E (a : ℕ) (L : List ℕ) (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Left-boundary turnaround from `B([], d :: R)`, halting iff `R = []` and `d` is odd. -/
def bounceBEmpty : ℕ → List ℕ → Option State
  | d, [] =>
    if d % 2 = 1 then none
    else some (.E 0 (List.replicate (d / 2 + 1) 0 ++ [1]) 0 [])
  | d, e :: R =>
    if d % 2 = 1 then some (.E 0 (List.replicate (d / 2) 0 ++ [1]) e R)
    else bounceBEmpty (e + d + 4) R

/-- Drain `L` leftward onto `d :: R` in mode `m` and rebound into `State.E` (or halt). -/
def drainLeft : DrainMode → List ℕ → ℕ → List ℕ → Option State
  | .A, [], d, R => bounceBEmpty (d + 1) R
  | .B, [], d, R => bounceBEmpty d R
  | .BR, [], d, R => some (.E 1 [] d R)
  | .A, a :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L (a + d + 2) R
  | .B, 0 :: L, d, R => drainLeft .BR L (d + 1) R
  | .B, (a + 1) :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L a ((d + 1) :: R)
  | .BR, 0 :: L, d, R => drainLeft .BR L 0 (d :: R)
  | .BR, (a + 1) :: L, d, R =>
    drainLeft (if a % 2 = 0 then .A else .B) L a (0 :: d :: R)

/-- Initial symbolic state `E(1, [], 0, [])`, reached from `init []` in 6 raw steps. -/
def start : State := .E 1 [] 0 []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E a L d R => Cfg.headRight E (encStack (a :: L)) (ListBlank.cons 0 (encStack (d :: R)))

/-- Accelerated transition function (`none` indicates halting on singleton odd right stacks). -/
def next : State → Option State
  | .E a L 0 [] =>
    drainLeft (if (a + 3) % 2 = 0 then .A else .B) L (a + 3) [0]
  | .E a L 0 (e :: R) =>
    drainLeft (if a % 2 = 0 then .B else .A) L (a + e + 4) R
  | .E a L (d + 1) R =>
    if d % 2 = 0 then
      List.casesOn R none fun e R' =>
        if d / 2 = 0 then some (.E (a + 3) L e R')
        else some (.E 0 (List.replicate (d / 2 - 1) 0 ++ (a + 3) :: L) e R')
    else
      List.casesOn R
        (drainLeft .A (List.replicate (d / 2) 0 ++ (a + 3) :: L) 0 [0])
        fun e R' => drainLeft .A (List.replicate (d / 2) 0 ++ (a + 3) :: L) (e + 1) R'

/-! ## Stack Encoding and Inner Walk Helpers -/

private theorem encStack_succ (a : ℕ) (s : List ℕ) :
    encStack ((a + 1) :: s) = ListBlank.cons 1 (encStack (a :: s)) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_bumpHead (s : List ℕ) :
    ListBlank.cons 1 (encStack s) = encStack (bumpHead s) := by
  rcases s with _ | ⟨a, s'⟩
  · simp [bumpHead, encStack]
  · exact (encStack_succ a s').symm

private def cfgA (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgB (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgBR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight B (encStack L) (ListBlank.cons 0 (ListBlank.cons 0 (encStack R)))

private def cfgD (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgE (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgDrain : DrainMode → List ℕ → ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .A, L, d, R => cfgA L (d :: R)
  | .B, L, d, R => cfgB L (d :: R)
  | .BR, L, d, R => cfgBR L (d :: R)

private theorem ab_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft A (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r)
      (Cfg.headLeft A l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headLeft A (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l) r)
        (Cfg.headLeft A (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
          (ListBlank.append ([1, 1] : List (Fin 2)) r)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih l (ListBlank.append ([1, 1] : List (Fin 2)) r)
    have hpow : ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append ([1, 1] : List (Fin 2)) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r := by
      change ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) r) = _
      rw [← ListBlank.append_pow_add, show 2 * k + 2 = 2 * (k + 1) by omega]
    rw [hpow] at h2
    exact (h1.trans_star h2).to_star

private theorem ba_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r)
      (Cfg.headLeft B l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l) r)
        (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
          (ListBlank.append ([1, 1] : List (Fin 2)) r)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih l (ListBlank.append ([1, 1] : List (Fin 2)) r)
    have hpow : ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append ([1, 1] : List (Fin 2)) r) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r := by
      change ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) r) = _
      rw [← ListBlank.append_pow_add, show 2 * k + 2 = 2 * (k + 1) by omega]
    rw [hpow] at h2
    exact (h1.trans_star h2).to_star

private theorem ed_walk_right (k : ℕ) (L : List ℕ) (r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E (encStack L) (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight E (encStack (List.replicate k 0 ++ L)) r) := by
  induction k generalizing L r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headRight E (encStack L)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r))
        (Cfg.headRight E (encStack (0 :: L))
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [encStack, list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih (0 :: L) r
    have hrep : List.replicate k 0 ++ (0 :: L) = List.replicate (k + 1) 0 ++ L := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hrep] at h2
    exact (h1.trans_star h2).to_star

/-! ## Separator Macro-Transition Rules -/

private theorem rule_A_nil (L : List ℕ) :
    ReachesPlus target (cfgA L []) (cfgB (bumpHead L) []) := by
  rw [cfgA, cfgB, ← encStack_bumpHead L, encStack]
  bb_steps

private theorem rule_A_nil_cons (R : List ℕ) (d : ℕ) :
    ReachesPlus target (cfgA [] (d :: R)) (cfgB [] ((d + 1) :: R)) := by
  simp only [cfgA, cfgB, encStack, list_pow_succ]
  bb_steps

private theorem rule_A_even_cons (L R : List ℕ) (k d : ℕ) :
    ReachesPlus target (cfgA ((2 * k) :: L) (d :: R)) (cfgA L ((2 * k + d + 2) :: R)) := by
  have hpre : ReachesPlus target (cfgA ((2 * k) :: L) (d :: R))
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack L))))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) := by
    rw [cfgA, encStack, ListBlank.append_pow_succ', encStack,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left k (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))
  have hpost : ReachesPlus target
      (Cfg.headLeft B (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))))
      (cfgA L ((2 * k + d + 2) :: R)) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add, cfgA, encStack,
      show 2 * k + d + 2 + 1 = 1 + (2 * k + 2 + d) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_A_odd_cons (L R : List ℕ) (k d : ℕ) :
    ReachesPlus target (cfgA ((2 * k + 1) :: L) (d :: R)) (cfgB L ((2 * k + d + 3) :: R)) := by
  have hpre : ReachesPlus target (cfgA ((2 * k + 1) :: L) (d :: R))
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) := by
    rw [cfgA, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, encStack,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left (k + 1) (ListBlank.cons 0 (encStack L))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))
  have hfin :
      Cfg.headLeft B (ListBlank.cons 0 (encStack L))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) =
      cfgB L ((2 * k + d + 3) :: R) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
      show 2 * (k + 1) + 2 + d = 2 * k + d + 3 + 1 by omega, Cfg.headLeft_cons]
    rfl
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_B_nil_odd (R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgB [] ((2 * k + 1) :: R))
      (cfgE (List.replicate (k + 1) 0 ++ [1]) R) := by
  have hpre : ReachesPlus target (cfgB [] ((2 * k + 1) :: R))
      (Cfg.headRight E (encStack [1])
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
          (ListBlank.cons 0 (encStack R)))) := by
    rw [cfgB, encStack, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right (k + 1) [1] (ListBlank.cons 0 (encStack R))
  exact hpre.trans_star hwalk

private theorem rule_B_nil_even_nil (k : ℕ) :
    ReachesPlus target (cfgB [] [2 * k]) (cfgA (List.replicate (k + 1) 0 ++ [1]) []) := by
  have hpre : ReachesPlus target (cfgB [] [2 * k])
      (Cfg.headRight E (encStack [1])
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 default)))) := by
    rw [cfgB, encStack, encStack, ListBlank.append_pow_succ', encStack]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right k [1] (ListBlank.append [1] (ListBlank.cons 0 default))
  have hpost : ReachesPlus target
      (Cfg.headRight E (encStack (List.replicate k 0 ++ [1]))
        (ListBlank.append [1] (ListBlank.cons 0 default)))
      (cfgA (List.replicate (k + 1) 0 ++ [1]) []) := by
    rw [List.replicate_succ, List.cons_append, cfgA, encStack]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_B_nil_even_cons (R : List ℕ) (k e : ℕ) :
    ReachesPlus target (cfgB [] ((2 * k) :: e :: R))
      (cfgA (List.replicate k 0 ++ [1]) ((e + 1) :: R)) := by
  have hpre : ReachesPlus target (cfgB [] ((2 * k) :: e :: R))
      (Cfg.headRight E (encStack [1])
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R)))))) := by
    rw [cfgB, encStack, encStack, ListBlank.append_pow_succ']
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right k [1] (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R))))
  have hpost : ReachesPlus target
      (Cfg.headRight E (encStack (List.replicate k 0 ++ [1]))
        (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R)))))
      (cfgA (List.replicate k 0 ++ [1]) ((e + 1) :: R)) := by
    rw [cfgA, encStack_succ e R, encStack, ListBlank.append_pow_succ ([1] : List (Fin 2)) e]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_B_zero (L R : List ℕ) :
    ReachesPlus target (cfgB (0 :: L) R) (cfgBR L (bumpHead R)) := by
  rw [cfgB, cfgBR, ← encStack_bumpHead R, encStack]
  simp only [list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_B_odd (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgB ((2 * k + 1) :: L) R) (cfgA L ((2 * k) :: bumpHead R)) := by
  have hpre : ReachesPlus target (cfgB ((2 * k + 1) :: L) R)
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack L))))
        (ListBlank.cons 0 (encStack (bumpHead R)))) := by
    rw [cfgB, encStack, show 2 * k + 1 + 1 = 1 + (2 * k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1, ListBlank.append_pow_succ',
      ← encStack_bumpHead R]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left k (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
    (ListBlank.cons 0 (encStack (bumpHead R)))
  have hpost : ReachesPlus target
      (Cfg.headLeft B (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.cons 0 (encStack (bumpHead R)))))
      (cfgA L ((2 * k) :: bumpHead R)) := by
    rw [cfgA, encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_B_even_succ (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgB ((2 * k + 2) :: L) R) (cfgB L ((2 * k + 1) :: bumpHead R)) := by
  have hpre : ReachesPlus target (cfgB ((2 * k + 2) :: L) R)
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.cons 0 (encStack L)))
        (ListBlank.cons 0 (encStack (bumpHead R)))) := by
    rw [cfgB, encStack, show 2 * k + 2 + 1 = 1 + 2 * (k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1, ← encStack_bumpHead R]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left (k + 1) (ListBlank.cons 0 (encStack L))
    (ListBlank.cons 0 (encStack (bumpHead R)))
  have hfin :
      Cfg.headLeft B (ListBlank.cons 0 (encStack L))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
          (ListBlank.cons 0 (encStack (bumpHead R)))) =
      cfgB L ((2 * k + 1) :: bumpHead R) := by
    rw [Cfg.headLeft_cons, cfgB, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_BR_nil (R : List ℕ) :
    ReachesPlus target (cfgBR [] R) (cfgE [1] R) := by
  rw [cfgBR, cfgE, encStack]
  simp only [encStack, list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_BR_zero (L R : List ℕ) :
    ReachesPlus target (cfgBR (0 :: L) R) (cfgBR L (0 :: R)) := by
  rw [cfgBR, cfgBR, encStack, encStack]
  simp only [list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_BR_odd (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgBR ((2 * k + 1) :: L) R) (cfgA L ((2 * k) :: 0 :: R)) := by
  have hpre : ReachesPlus target (cfgBR ((2 * k + 1) :: L) R)
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack L))))
        (ListBlank.cons 0 (encStack (0 :: R)))) := by
    rw [cfgBR, encStack, show 2 * k + 1 + 1 = 1 + (2 * k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1, ListBlank.append_pow_succ']
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left k (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
    (ListBlank.cons 0 (encStack (0 :: R)))
  have hpost : ReachesPlus target
      (Cfg.headLeft B (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.cons 0 (encStack (0 :: R)))))
      (cfgA L ((2 * k) :: 0 :: R)) := by
    rw [cfgA, encStack, ListBlank.append_pow_succ]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_BR_even_succ (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgBR ((2 * k + 2) :: L) R) (cfgB L ((2 * k + 1) :: 0 :: R)) := by
  have hpre : ReachesPlus target (cfgBR ((2 * k + 2) :: L) R)
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.cons 0 (encStack L)))
        (ListBlank.cons 0 (encStack (0 :: R)))) := by
    rw [cfgBR, encStack, show 2 * k + 2 + 1 = 1 + 2 * (k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ba_walk_left (k + 1) (ListBlank.cons 0 (encStack L))
    (ListBlank.cons 0 (encStack (0 :: R)))
  have hfin :
      Cfg.headLeft B (ListBlank.cons 0 (encStack L))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
          (ListBlank.cons 0 (encStack (0 :: R)))) =
      cfgB L ((2 * k + 1) :: 0 :: R) := by
    rw [Cfg.headLeft_cons]
    conv_rhs => rw [cfgB, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega]
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_D_nil (L : List ℕ) :
    ReachesPlus target (cfgD L []) (cfgA (bumpHead L) []) := by
  rw [cfgD, cfgA, ← encStack_bumpHead L, encStack]
  bb_steps

private theorem rule_D_even_cons (L R : List ℕ) (k d : ℕ) :
    ReachesPlus target (cfgD ((2 * k) :: L) (d :: R)) (cfgB L ((2 * k + d + 2) :: R)) := by
  have hpre : ReachesPlus target (cfgD ((2 * k) :: L) (d :: R))
      (Cfg.headLeft A
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack L))))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) := by
    rw [cfgD, encStack, ListBlank.append_pow_succ', encStack,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ab_walk_left k (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))
  have hpost : ReachesPlus target
      (Cfg.headLeft A (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))))
      (cfgB L ((2 * k + d + 2) :: R)) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add, cfgB, encStack,
      show 2 * k + d + 2 + 1 = 1 + (2 * k + 2 + d) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 1]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_D_odd_cons (L R : List ℕ) (k d : ℕ) :
    ReachesPlus target (cfgD ((2 * k + 1) :: L) (d :: R)) (cfgA L ((2 * k + d + 3) :: R)) := by
  have hpre : ReachesPlus target (cfgD ((2 * k + 1) :: L) (d :: R))
      (Cfg.headLeft A
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) := by
    rw [cfgD, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, encStack,
      ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ab_walk_left (k + 1) (ListBlank.cons 0 (encStack L))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))
  have hfin :
      Cfg.headLeft A (ListBlank.cons 0 (encStack L))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1)))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) =
      cfgA L ((2 * k + d + 3) :: R) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
      show 2 * (k + 1) + 2 + d = 2 * k + d + 3 + 1 by omega, Cfg.headLeft_cons]
    rfl
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_E_nil_halt (L : List ℕ) :
    ∃ cfg', ReachesStar target (cfgE L []) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F (encStack (bumpHead L)) default, ?_, by bb_halt⟩
  rw [cfgE, ← encStack_bumpHead L, encStack]
  bb_steps

private theorem rule_E_zero (L R : List ℕ) :
    ReachesPlus target (cfgE L (0 :: R)) (cfgD (bumpHead (bumpHead L)) R) := by
  rw [cfgE, cfgD, ← encStack_bumpHead (bumpHead L), ← encStack_bumpHead L, encStack]
  simp only [list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_E_odd (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgE L ((2 * k + 1) :: R))
      (cfgE (List.replicate k 0 ++ bumpHead (bumpHead (bumpHead L))) R) := by
  have hpre : ReachesPlus target (cfgE L ((2 * k + 1) :: R))
      (Cfg.headRight E (encStack (bumpHead (bumpHead (bumpHead L))))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.cons 0 (encStack R)))) := by
    rw [cfgE, encStack, show 2 * k + 1 + 1 = 2 + 2 * k by omega, ListBlank.append_pow_add,
      ← encStack_bumpHead (bumpHead (bumpHead L)), ← encStack_bumpHead (bumpHead L),
      ← encStack_bumpHead L]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right k (bumpHead (bumpHead (bumpHead L))) (ListBlank.cons 0 (encStack R))
  exact hpre.trans_star hwalk

private theorem rule_E_even_succ_nil (L : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgE L [2 * k + 2])
      (cfgA (List.replicate (k + 1) 0 ++ bumpHead (bumpHead (bumpHead L))) []) := by
  have hpre : ReachesPlus target (cfgE L [2 * k + 2])
      (Cfg.headRight E (encStack (bumpHead (bumpHead (bumpHead L))))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 default)))) := by
    rw [cfgE, encStack, show 2 * k + 2 + 1 = 2 + (2 * k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 2, ListBlank.append_pow_succ',
      ← encStack_bumpHead (bumpHead (bumpHead L)), ← encStack_bumpHead (bumpHead L),
      ← encStack_bumpHead L, encStack]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right k (bumpHead (bumpHead (bumpHead L)))
    (ListBlank.append [1] (ListBlank.cons 0 default))
  have hpost : ReachesPlus target
      (Cfg.headRight E (encStack (List.replicate k 0 ++ bumpHead (bumpHead (bumpHead L))))
        (ListBlank.append [1] (ListBlank.cons 0 default)))
      (cfgA (List.replicate (k + 1) 0 ++ bumpHead (bumpHead (bumpHead L))) []) := by
    rw [List.replicate_succ, List.cons_append, cfgA, encStack]
    simp only [encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

private theorem rule_E_even_succ_cons (L R : List ℕ) (k e : ℕ) :
    ReachesPlus target (cfgE L ((2 * k + 2) :: e :: R))
      (cfgA (List.replicate k 0 ++ bumpHead (bumpHead (bumpHead L))) ((e + 1) :: R)) := by
  have hpre : ReachesPlus target (cfgE L ((2 * k + 2) :: e :: R))
      (Cfg.headRight E (encStack (bumpHead (bumpHead (bumpHead L))))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
          (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R)))))) := by
    rw [cfgE, encStack, show 2 * k + 2 + 1 = 2 + (2 * k + 1) by omega,
      ListBlank.append_pow_add ([1] : List (Fin 2)) 2, ListBlank.append_pow_succ',
      ← encStack_bumpHead (bumpHead (bumpHead L)), ← encStack_bumpHead (bumpHead L),
      ← encStack_bumpHead L]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ed_walk_right k (bumpHead (bumpHead (bumpHead L)))
    (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R))))
  have hpost : ReachesPlus target
      (Cfg.headRight E (encStack (List.replicate k 0 ++ bumpHead (bumpHead (bumpHead L))))
        (ListBlank.append [1] (ListBlank.cons 0 (encStack (e :: R)))))
      (cfgA (List.replicate k 0 ++ bumpHead (bumpHead (bumpHead L))) ((e + 1) :: R)) := by
    rw [cfgA, encStack_succ e R, encStack, ListBlank.append_pow_succ ([1] : List (Fin 2)) e]
    bb_steps
  exact (hpre.trans_star hwalk).trans hpost

/-! ## Multi-Block Drain and Turnaround Verification -/

private theorem rule_A_zeros_all (L R : List ℕ) (k : ℕ) :
    ∀ (d : ℕ), ReachesStar target
      (cfgA (List.replicate k 0 ++ L) (d :: R)) (cfgA L ((d + 2 * k) :: R)) := by
  induction k with
  | zero =>
    intro d
    simp only [List.replicate_zero, List.nil_append, Nat.mul_zero, Nat.add_zero]
    exact ReachesStar.refl _ _
  | succ k ih =>
    intro d
    rw [List.replicate_succ, List.cons_append]
    have h1 := rule_A_even_cons (List.replicate k 0 ++ L) R 0 d
    rw [show 2 * 0 + d + 2 = d + 2 by omega] at h1
    have h2 := ih (d + 2)
    rw [show d + 2 + 2 * k = d + 2 * (k + 1) by omega] at h2
    exact (h1.trans_star h2).to_star

private theorem a_zeros_one_drain (R : List ℕ) (k d : ℕ) :
    ReachesPlus target (cfgA (List.replicate k 0 ++ [1]) (d :: R))
      (cfgB [] ((d + 2 * k + 3) :: R)) := by
  have h1 := rule_A_zeros_all [1] R k d
  have h2 := rule_A_odd_cons [] R 0 (d + 2 * k)
  rw [show 2 * 0 + (d + 2 * k) + 3 = d + 2 * k + 3 by omega] at h2
  exact h1.trans_plus h2

private def AccelFrom (c : Cfg (Fin 2) (Fin 6)) (res : Option State) : Prop :=
  match res with
  | some s' => ReachesPlus target c (encode s')
  | none => ∃ cfg', ReachesStar target c cfg' ∧ (step target cfg').isNone

private theorem compose_opt {c1 c2 : Cfg (Fin 2) (Fin 6)} {res : Option State}
    (h1 : ReachesPlus target c1 c2) (h2 : AccelFrom c2 res) : AccelFrom c1 res := by
  rcases res with _ | s'
  · obtain ⟨cfg', hstar, hnone⟩ := h2
    exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
  · exact h1.trans h2

private theorem step_bounceBEmpty (R : List ℕ) :
    ∀ (d : ℕ), AccelFrom (cfgB [] (d :: R)) (bounceBEmpty d R) := by
  induction R with
  | nil =>
    intro d
    simp only [bounceBEmpty]
    by_cases hodd : d % 2 = 1
    · simp only [hodd, ↓reduceIte, AccelFrom]
      have hd : d = 2 * (d / 2) + 1 := by omega
      have h1 : ReachesPlus target (cfgB [] [d])
          (cfgE (List.replicate (d / 2 + 1) 0 ++ [1]) []) := by
        conv_lhs => rw [hd]
        exact rule_B_nil_odd [] (d / 2)
      obtain ⟨cfg', hstar, hnone⟩ := rule_E_nil_halt (List.replicate (d / 2 + 1) 0 ++ [1])
      exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
    · simp only [hodd, ↓reduceIte, AccelFrom]
      have hd : d = 2 * (d / 2) := by omega
      have h1 : ReachesPlus target (cfgB [] [d])
          (cfgA (0 :: (List.replicate (d / 2) 0 ++ [1])) []) := by
        conv_lhs => rw [hd]
        simpa [List.replicate_succ] using rule_B_nil_even_nil (d / 2)
      have h2 := rule_A_nil (0 :: (List.replicate (d / 2) 0 ++ [1]))
      simp only [bumpHead] at h2
      have h3 := rule_B_odd (List.replicate (d / 2) 0 ++ [1]) [] 0
      simp only [Nat.mul_zero, bumpHead] at h3
      have h4 := a_zeros_one_drain [0] (d / 2) 0
      rw [show 0 + 2 * (d / 2) + 3 = 2 * (d / 2 + 1) + 1 by omega] at h4
      have h5 := rule_B_nil_odd [0] (d / 2 + 1)
      have hfin : cfgE (List.replicate (d / 2 + 2) 0 ++ [1]) [0] =
          encode (.E 0 (List.replicate (d / 2 + 1) 0 ++ [1]) 0 []) := by
        rw [show d / 2 + 2 = (d / 2 + 1) + 1 by rfl, List.replicate_succ, List.cons_append]
        rfl
      rw [hfin] at h5
      exact (((h1.trans h2).trans h3).trans h4).trans h5
  | cons e R' ih =>
    intro d
    simp only [bounceBEmpty]
    by_cases hodd : d % 2 = 1
    · simp only [hodd, ↓reduceIte, AccelFrom]
      have hd : d = 2 * (d / 2) + 1 := by omega
      have h1 : ReachesPlus target (cfgB [] (d :: e :: R'))
          (cfgE (List.replicate (d / 2 + 1) 0 ++ [1]) (e :: R')) := by
        conv_lhs => rw [hd]
        exact rule_B_nil_odd (e :: R') (d / 2)
      have hfin : cfgE (List.replicate (d / 2 + 1) 0 ++ [1]) (e :: R') =
          encode (.E 0 (List.replicate (d / 2) 0 ++ [1]) e R') := by
        rw [List.replicate_succ, List.cons_append]
        rfl
      rwa [hfin] at h1
    · simp only [hodd, ↓reduceIte]
      have hd : d = 2 * (d / 2) := by omega
      have h1 : ReachesPlus target (cfgB [] (d :: e :: R'))
          (cfgA (List.replicate (d / 2) 0 ++ [1]) ((e + 1) :: R')) := by
        conv_lhs => rw [hd]
        exact rule_B_nil_even_cons R' (d / 2) e
      have h2 := a_zeros_one_drain R' (d / 2) (e + 1)
      rw [show e + 1 + 2 * (d / 2) + 3 = e + d + 4 by omega] at h2
      exact compose_opt (h1.trans h2) (ih (e + d + 4))

private theorem step_drainLeft (L : List ℕ) :
    ∀ (m : DrainMode) (d : ℕ) (R : List ℕ),
      AccelFrom (cfgDrain m L d R) (drainLeft m L d R) := by
  induction L with
  | nil =>
    intro m d R
    cases m with
    | A =>
      simp only [drainLeft, cfgDrain]
      exact compose_opt (rule_A_nil_cons R d) (step_bounceBEmpty R (d + 1))
    | B =>
      simp only [drainLeft, cfgDrain]
      exact step_bounceBEmpty R d
    | BR =>
      simp only [drainLeft, cfgDrain, AccelFrom]
      exact rule_BR_nil (d :: R)
  | cons a L' ih =>
    intro m d R
    cases m with
    | A =>
      simp only [drainLeft, cfgDrain]
      by_cases heven : a % 2 = 0
      · simp only [heven, ↓reduceIte]
        have ha : a = 2 * (a / 2) := by omega
        have h1 : ReachesPlus target (cfgA (a :: L') (d :: R)) (cfgA L' ((a + d + 2) :: R)) := by
          conv_lhs => rw [ha]
          simpa [← ha] using rule_A_even_cons L' R (a / 2) d
        exact compose_opt h1 (ih .A (a + d + 2) R)
      · simp only [heven, ↓reduceIte]
        have ha : a = 2 * (a / 2) + 1 := by omega
        have h1 : ReachesPlus target (cfgA (a :: L') (d :: R)) (cfgB L' ((a + d + 2) :: R)) := by
          conv_lhs => rw [ha]
          have h := rule_A_odd_cons L' R (a / 2) d
          rwa [show 2 * (a / 2) + d + 3 = a + d + 2 by omega] at h
        exact compose_opt h1 (ih .B (a + d + 2) R)
    | B =>
      rcases a with _ | a'
      · simp only [drainLeft, cfgDrain]
        exact compose_opt (rule_B_zero L' (d :: R)) (ih .BR (d + 1) R)
      · simp only [drainLeft, cfgDrain]
        by_cases heven : a' % 2 = 0
        · simp only [heven, ↓reduceIte]
          have h1 : ReachesPlus target (cfgB ((a' + 1) :: L') (d :: R))
              (cfgA L' (a' :: (d + 1) :: R)) := by
            have h := rule_B_odd L' (d :: R) (a' / 2)
            rwa [show 2 * (a' / 2) = a' by omega] at h
          exact compose_opt h1 (ih .A a' ((d + 1) :: R))
        · simp only [heven, ↓reduceIte]
          have ha : a' + 1 = 2 * (a' / 2) + 2 := by omega
          have h1 : ReachesPlus target (cfgB ((a' + 1) :: L') (d :: R))
              (cfgB L' (a' :: (d + 1) :: R)) := by
            conv_lhs => rw [ha]
            have h := rule_B_even_succ L' (d :: R) (a' / 2)
            rwa [show 2 * (a' / 2) + 1 = a' by omega] at h
          exact compose_opt h1 (ih .B a' ((d + 1) :: R))
    | BR =>
      rcases a with _ | a'
      · simp only [drainLeft, cfgDrain]
        exact compose_opt (rule_BR_zero L' (d :: R)) (ih .BR 0 (d :: R))
      · simp only [drainLeft, cfgDrain]
        by_cases heven : a' % 2 = 0
        · simp only [heven, ↓reduceIte]
          have h1 : ReachesPlus target (cfgBR ((a' + 1) :: L') (d :: R))
              (cfgA L' (a' :: 0 :: d :: R)) := by
            have h := rule_BR_odd L' (d :: R) (a' / 2)
            rwa [show 2 * (a' / 2) = a' by omega] at h
          exact compose_opt h1 (ih .A a' (0 :: d :: R))
        · simp only [heven, ↓reduceIte]
          have ha : a' + 1 = 2 * (a' / 2) + 2 := by omega
          have h1 : ReachesPlus target (cfgBR ((a' + 1) :: L') (d :: R))
              (cfgB L' (a' :: 0 :: d :: R)) := by
            conv_lhs => rw [ha]
            have h := rule_BR_even_succ L' (d :: R) (a' / 2)
            rwa [show 2 * (a' / 2) + 1 = a' by omega] at h
          exact compose_opt h1 (ih .B a' (0 :: d :: R))

/-! ## Accelerated Step Verification -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

private theorem step_accel (s : State) : AccelFrom (encode s) (next s) := by
  rcases s with ⟨a, L, d, R⟩
  rcases d with _ | d'
  · rcases R with _ | ⟨e, R'⟩
    · simp only [next]
      have h1 : ReachesPlus target (encode (.E a L 0 [])) (cfgD ((a + 2) :: L) []) :=
        rule_E_zero (a :: L) []
      have h2 := rule_D_nil ((a + 2) :: L)
      have h3 := rule_A_nil ((a + 3) :: L)
      simp only [bumpHead] at h2 h3
      have hpre := (h1.trans h2).trans h3
      by_cases heven : (a + 3) % 2 = 0
      · simp only [heven, ↓reduceIte]
        have h4 : ReachesPlus target (cfgB ((a + 4) :: L) []) (cfgA L ((a + 3) :: [0])) := by
          have hb := rule_B_odd L [] ((a + 3) / 2)
          rw [show 2 * ((a + 3) / 2) = a + 3 by omega,
            show a + 3 + 1 = a + 4 by rfl] at hb
          exact hb
        exact compose_opt (hpre.trans h4) (step_drainLeft L .A (a + 3) [0])
      · simp only [heven, ↓reduceIte]
        have ha : a + 4 = 2 * ((a + 3) / 2) + 2 := by omega
        have h4 : ReachesPlus target (cfgB ((a + 4) :: L) []) (cfgB L ((a + 3) :: [0])) := by
          conv_lhs => rw [ha]
          have hb := rule_B_even_succ L [] ((a + 3) / 2)
          rwa [show 2 * ((a + 3) / 2) + 1 = a + 3 by omega] at hb
        exact compose_opt (hpre.trans h4) (step_drainLeft L .B (a + 3) [0])
    · simp only [next]
      have h1 : ReachesPlus target (encode (.E a L 0 (e :: R')))
          (cfgD ((a + 2) :: L) (e :: R')) :=
        rule_E_zero (a :: L) (e :: R')
      by_cases heven : a % 2 = 0
      · simp only [heven, ↓reduceIte]
        have ha : a + 2 = 2 * (a / 2 + 1) := by omega
        have h2 : ReachesPlus target (cfgD ((a + 2) :: L) (e :: R'))
            (cfgB L ((a + e + 4) :: R')) := by
          conv_lhs => rw [ha]
          have hd := rule_D_even_cons L R' (a / 2 + 1) e
          rwa [show 2 * (a / 2 + 1) + e + 2 = a + e + 4 by omega] at hd
        exact compose_opt (h1.trans h2) (step_drainLeft L .B (a + e + 4) R')
      · simp only [heven, ↓reduceIte]
        have ha : a + 2 = 2 * (a / 2 + 1) + 1 := by omega
        have h2 : ReachesPlus target (cfgD ((a + 2) :: L) (e :: R'))
            (cfgA L ((a + e + 4) :: R')) := by
          conv_lhs => rw [ha]
          have hd := rule_D_odd_cons L R' (a / 2 + 1) e
          rwa [show 2 * (a / 2 + 1) + e + 3 = a + e + 4 by omega] at hd
        exact compose_opt (h1.trans h2) (step_drainLeft L .A (a + e + 4) R')
  · by_cases heven : d' % 2 = 0
    · have hd : d' + 1 = 2 * (d' / 2) + 1 := by omega
      rcases R with _ | ⟨e, R'⟩
      · simp only [next, heven, ↓reduceIte, AccelFrom]
        have h1 : ReachesPlus target (encode (.E a L (d' + 1) []))
            (cfgE (List.replicate (d' / 2) 0 ++ (a + 3) :: L) []) := by
          change ReachesPlus target (cfgE (a :: L) [d' + 1]) _
          conv_lhs => rw [hd]
          exact rule_E_odd (a :: L) [] (d' / 2)
        obtain ⟨cfg', hstar, hnone⟩ :=
          rule_E_nil_halt (List.replicate (d' / 2) 0 ++ (a + 3) :: L)
        exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
      · simp only [next, heven, ↓reduceIte]
        have h1 : ReachesPlus target (encode (.E a L (d' + 1) (e :: R')))
            (cfgE (List.replicate (d' / 2) 0 ++ (a + 3) :: L) (e :: R')) := by
          change ReachesPlus target (cfgE (a :: L) ((d' + 1) :: e :: R')) _
          conv_lhs => rw [hd]
          exact rule_E_odd (a :: L) (e :: R') (d' / 2)
        rcases hk : d' / 2 with _ | k
        · rw [hk, List.replicate_zero, List.nil_append] at h1
          exact h1
        · rw [hk, List.replicate_succ, List.cons_append] at h1
          exact h1
    · have hd : d' + 1 = 2 * (d' / 2) + 2 := by omega
      rcases R with _ | ⟨e, R'⟩
      · simp only [next, heven, ↓reduceIte]
        have h1 : ReachesPlus target (encode (.E a L (d' + 1) []))
            (cfgA (0 :: (List.replicate (d' / 2) 0 ++ (a + 3) :: L)) []) := by
          change ReachesPlus target (cfgE (a :: L) [d' + 1]) _
          conv_lhs => rw [hd]
          simpa [List.replicate_succ, bumpHead] using rule_E_even_succ_nil (a :: L) (d' / 2)
        have h2 := rule_A_nil (0 :: (List.replicate (d' / 2) 0 ++ (a + 3) :: L))
        simp only [bumpHead] at h2
        have h3 := rule_B_odd (List.replicate (d' / 2) 0 ++ (a + 3) :: L) [] 0
        simp only [Nat.mul_zero, bumpHead] at h3
        exact compose_opt ((h1.trans h2).trans h3)
          (step_drainLeft (List.replicate (d' / 2) 0 ++ (a + 3) :: L) .A 0 [0])
      · simp only [next, heven, ↓reduceIte]
        have h1 : ReachesPlus target (encode (.E a L (d' + 1) (e :: R')))
            (cfgA (List.replicate (d' / 2) 0 ++ (a + 3) :: L) ((e + 1) :: R')) := by
          change ReachesPlus target (cfgE (a :: L) ((d' + 1) :: e :: R')) _
          conv_lhs => rw [hd]
          exact rule_E_even_succ_cons (a :: L) R' (d' / 2) e
        exact compose_opt h1
          (step_drainLeft (List.replicate (d' / 2) 0 ++ (a + 3) :: L) .A (e + 1) R')

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  have hs := step_accel s
  rcases h : next s with _ | s' <;> simpa [AccelFrom, h] using hs

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LB_1LC1LA_1RD0LB_1RA1RE_1RF0RD_HHH1RD
