/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`

Formal `IsValidAcceleration` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA`.

Each digit stack $S = [s_0, s_1, \dots]$ encodes unary blocks $1^{s_i + 1}$ separated by single
zeros (`encStack`), ordered from the tape head outward. Starting from `init []`, the machine
reaches $E(0, [0])$ in 4 raw steps, where $E(d, R)$ has state `E` reading `0` between the blank
left tape and `encStack (d :: R)`.

## Accelerated Transition Rules

```text
scanE(ks, 2k + 1, [])     = Halt
scanE([], 2k, [])         = E(1, 0^(k + 1))
scanE(j2 :: ks, 2k, [])   = drainOddB(ks, 2 * j2 + 5, 0^k)
scanE(ks, 2k + 1, e :: R) = scanE(k :: ks, e, R)
scanE(ks, 2k, e :: R)     = drainOddB(ks, 2k + e + 2, R)

drainOddB([], d, R)                   = E(d + 2, R)
drainOddB([j], d, R)                  = E(1, 0^j ++ (d + 1) :: R)
drainOddB(0 :: j2 :: ks, d, R)        = drainOddB(ks, 2 * j2 + d + 6, R)
drainOddB((j1 + 1) :: j2 :: ks, d, R) = drainOddB(ks, 2 * j2 + 5, 0^j1 ++ (d + 1) :: R)

E(d, R) -> scanE([], d, R)

Start: E(0, [0]), reached after 4 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_---1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic state space for the accelerated reservoir-odometer system of `target`. -/
inductive State where
  /-- Left-boundary configuration `E(d, R)`: state `E` reading `0` before `d :: R`. -/
  | E (d : ℕ) (R : List ℕ)
  deriving DecidableEq, Repr

/-- Drain accumulated odd left-stack digits `ks` (representing `2 * j + 1`) back to `State.E`. -/
def drainOddB : List ℕ → ℕ → List ℕ → State
  | [], d, R => .E (d + 2) R
  | [j], d, R => .E 1 (List.replicate j 0 ++ (d + 1) :: R)
  | 0 :: j2 :: ks, d, R => drainOddB ks (2 * j2 + d + 6) R
  | (j1 + 1) :: j2 :: ks, d, R =>
    drainOddB ks (2 * j2 + 5) (List.replicate j1 0 ++ (d + 1) :: R)

/-- Scan rightward across odd digits of `d :: R` in state `E`, halting iff all digits are odd. -/
def scanE : List ℕ → ℕ → List ℕ → Option State
  | ks, d, [] =>
    if d % 2 = 1 then none
    else
      List.casesOn ks (some (.E 1 (List.replicate (d / 2 + 1) 0)))
        fun j2 ks' => some (drainOddB ks' (2 * j2 + 5) (List.replicate (d / 2) 0))
  | ks, d, e :: R =>
    if d % 2 = 1 then scanE ((d / 2) :: ks) e R
    else some (drainOddB ks (d + e + 2) R)

/-- Initial symbolic state `E(0, [0])`, reached from `init []` in 4 raw steps. -/
def start : State := .E 0 [0]

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E d R => Cfg.headRight E default (ListBlank.cons 0 (encStack (d :: R)))

/-- Accelerated transition function (`none` indicates halting when `d :: R` has all odd digits). -/
def next : State → Option State
  | .E d R => scanE [] d R

/-! ## Stack Encoding and Inner Walk Helpers -/

private def encOdds : List ℕ → List ℕ
  | [] => []
  | j :: ks => (2 * j + 1) :: encOdds ks

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

private def cfgC (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight C (encStack L) (ListBlank.cons 0 (encStack R))

private def cfgE (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight E (encStack L) (ListBlank.cons 0 (encStack R))

private theorem b_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft B l (ListBlank.append (([1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ (k + 1)) l) r)
        (Cfg.headLeft B (ListBlank.append (([1] : List (Fin 2)) ^ k) l)
          (ListBlank.append [1] r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih l (ListBlank.append [1] r)
    rw [ListBlank.append_pow_succ'] at h2
    exact (h1.trans_star h2).to_star

private theorem cd_walk_left (k : ℕ) (l : ListBlank (Fin 2)) (R : List ℕ) :
    ReachesStar target
      (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) (encStack R))
      (Cfg.headLeft C l (encStack (List.replicate k 0 ++ R))) := by
  induction k generalizing l R with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l) (encStack R))
        (Cfg.headLeft C (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l)
          (encStack (0 :: R))) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [encStack, list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih l (0 :: R)
    have hrep : List.replicate k 0 ++ (0 :: R) = List.replicate (k + 1) 0 ++ R := by
      rw [List.replicate_succ', List.append_assoc, List.singleton_append]
    rw [hrep] at h2
    exact (h1.trans_star h2).to_star

private theorem ae_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight E (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headRight E l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r))
        (Cfg.headRight E (ListBlank.append ([1, 1] : List (Fin 2)) l)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih (ListBlank.append ([1, 1] : List (Fin 2)) l) r
    have hpow : ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append ([1, 1] : List (Fin 2)) l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l := by
      change ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) l) = _
      rw [← ListBlank.append_pow_add, show 2 * k + 2 = 2 * (k + 1) by omega]
    rw [hpow] at h2
    exact (h1.trans_star h2).to_star

private theorem ea_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight A (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 : ReachesPlus target
        (Cfg.headRight A l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r))
        (Cfg.headRight A (ListBlank.append ([1, 1] : List (Fin 2)) l)
          (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      rw [show 2 * (k + 1) = 2 + 2 * k by omega, ListBlank.append_pow_add]
      simp only [list_pow_succ, list_pow_zero]
      bb_steps
    have h2 := ih (ListBlank.append ([1, 1] : List (Fin 2)) l) r
    have hpow : ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append ([1, 1] : List (Fin 2)) l) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) l := by
      change ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2) l) = _
      rw [← ListBlank.append_pow_add, show 2 * k + 2 = 2 * (k + 1) by omega]
    rw [hpow] at h2
    exact (h1.trans_star h2).to_star

/-! ## Separator Macro-Transition Rules -/

private theorem rule_A_nil (L : List ℕ) :
    ReachesPlus target (cfgA L []) (cfgB (bumpHead L) []) := by
  rw [cfgA, cfgB, ← encStack_bumpHead L, encStack]
  bb_steps

private theorem rule_A_cons_cons (L R : List ℕ) (a d : ℕ) :
    ReachesPlus target (cfgA (a :: L) (d :: R)) (cfgB L ((a + d + 2) :: R)) := by
  have hpre : ReachesPlus target (cfgA (a :: L) (d :: R))
      (Cfg.headLeft B
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ 2)
          (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) := by
    rw [cfgA, encStack, encStack, ListBlank.append_pow_succ ([1] : List (Fin 2)) d]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := b_walk_left (a + 1) (ListBlank.cons 0 (encStack L))
    (ListBlank.append (([1] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))
  have hfin :
      Cfg.headLeft B (ListBlank.cons 0 (encStack L))
        (ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
          (ListBlank.append (([1] : List (Fin 2)) ^ 2)
            (ListBlank.append (([1] : List (Fin 2)) ^ d) (ListBlank.cons 0 (encStack R))))) =
      cfgB L ((a + d + 2) :: R) := by
    rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add,
      show a + 1 + 2 + d = a + d + 2 + 1 by omega, Cfg.headLeft_cons]
    rfl
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_B_nil (R : List ℕ) :
    ReachesPlus target (cfgB [] R) (cfgC [] (bumpHead R)) := by
  rw [cfgB, cfgC, ← encStack_bumpHead R, encStack]
  bb_steps

private theorem rule_B_odd (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgB ((2 * k + 1) :: L) R)
      (cfgC L (List.replicate (k + 1) 0 ++ bumpHead R)) := by
  have hpre : ReachesPlus target (cfgB ((2 * k + 1) :: L) R)
      (Cfg.headLeft C
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) (ListBlank.cons 0 (encStack L)))
        (encStack (bumpHead R))) := by
    rw [cfgB, encStack, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, ← encStack_bumpHead R]
    bb_steps
  have hwalk := cd_walk_left (k + 1) (ListBlank.cons 0 (encStack L)) (bumpHead R)
  rw [Cfg.headLeft_cons] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_C_nil (R : List ℕ) :
    ReachesPlus target (cfgC [] R) (cfgE [] (bumpHead R)) := by
  rw [cfgC, cfgE, ← encStack_bumpHead R, encStack]
  bb_steps

private theorem rule_C_cons_zero (L R : List ℕ) (a : ℕ) :
    ReachesPlus target (cfgC (a :: L) (0 :: R)) (cfgA ((a + 2) :: L) R) := by
  rw [cfgC, cfgA, encStack_succ (a + 1) L, encStack_succ a L, encStack,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) a, encStack]
  simp only [list_pow_succ, list_pow_zero]
  bb_steps

private theorem rule_E_even (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgE L ((2 * k) :: R)) (cfgA ((2 * k) :: L) R) := by
  have hpre : ReachesPlus target (cfgE L ((2 * k) :: R))
      (Cfg.headRight A
        (ListBlank.append [1] (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.cons 0 (encStack R)))) := by
    rw [cfgE, encStack, ListBlank.append_pow_succ]
    bb_steps
  have hwalk := ea_walk_right k
    (ListBlank.append [1] (ListBlank.cons 0 (encStack L))) (ListBlank.cons 0 (encStack R))
  rw [ListBlank.append_pow_succ'] at hwalk
  exact hpre.trans_star hwalk

private theorem rule_E_odd (L R : List ℕ) (k : ℕ) :
    ReachesPlus target (cfgE L ((2 * k + 1) :: R)) (cfgE ((2 * k + 1) :: L) R) := by
  have hpre : ReachesPlus target (cfgE L ((2 * k + 1) :: R))
      (Cfg.headRight E
        (ListBlank.append ([1, 1] : List (Fin 2)) (ListBlank.cons 0 (encStack L)))
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) (ListBlank.cons 0 (encStack R)))) := by
    rw [cfgE, encStack, show 2 * k + 1 + 1 = 2 + 2 * k by omega, ListBlank.append_pow_add]
    simp only [list_pow_succ, list_pow_zero]
    bb_steps
  have hwalk := ae_walk_right k
    (ListBlank.append ([1, 1] : List (Fin 2)) (ListBlank.cons 0 (encStack L)))
    (ListBlank.cons 0 (encStack R))
  have hfin : ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
      (ListBlank.append ([1, 1] : List (Fin 2)) (ListBlank.cons 0 (encStack L))) =
      encStack ((2 * k + 1) :: L) := by
    change ListBlank.append (([1] : List (Fin 2)) ^ (2 * k))
      (ListBlank.append (([1] : List (Fin 2)) ^ 2) (ListBlank.cons 0 (encStack L))) = _
    rw [← ListBlank.append_pow_add, show 2 * k + 2 = 2 * k + 1 + 1 by omega]
    rfl
  rw [hfin] at hwalk
  exact hpre.trans_star hwalk

/-! ## Contracted Odometer Verification -/

private theorem step_drainOddB :
    ∀ (n : ℕ) (ks : List ℕ), ks.length ≤ n →
      ∀ (d : ℕ) (R : List ℕ),
        ReachesPlus target (cfgB (encOdds ks) (d :: R)) (encode (drainOddB ks d R))
  | _, [], _ => by
      intro d R
      simp only [encOdds, drainOddB]
      exact (rule_B_nil (d :: R)).trans (rule_C_nil ((d + 1) :: R))
  | 0, _ :: _, hlen => by
      simp at hlen
  | n + 1, [j], _ => by
      intro d R
      simp only [encOdds, drainOddB]
      have h1 := rule_B_odd [] (d :: R) j
      rw [List.replicate_succ, List.cons_append] at h1
      exact h1.trans (rule_C_nil (0 :: (List.replicate j 0 ++ (d + 1) :: R)))
  | n + 1, j1 :: j2 :: ks, hlen => by
      have hlen' : ks.length ≤ n := by
        simp only [List.length_cons] at hlen
        omega
      have ih := step_drainOddB n ks hlen'
      intro d R
      rcases j1 with _ | j1'
      · simp only [encOdds, drainOddB, Nat.mul_zero, Nat.zero_add]
        have h1 := rule_B_odd ((2 * j2 + 1) :: encOdds ks) (d :: R) 0
        simp only [List.replicate_succ, List.replicate_zero, List.cons_append, List.nil_append,
          bumpHead] at h1
        have h2 := rule_C_cons_zero (encOdds ks) ((d + 1) :: R) (2 * j2 + 1)
        have h3 := rule_A_cons_cons (encOdds ks) R (2 * j2 + 1 + 2) (d + 1)
        rw [show 2 * j2 + 1 + 2 + (d + 1) + 2 = 2 * j2 + d + 6 by omega] at h3
        exact ((h1.trans h2).trans h3).trans (ih (2 * j2 + d + 6) R)
      · simp only [encOdds, drainOddB]
        have h1 := rule_B_odd ((2 * j2 + 1) :: encOdds ks) (d :: R) (j1' + 1)
        rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at h1
        simp only [bumpHead] at h1
        have h2 := rule_C_cons_zero (encOdds ks)
          (0 :: (List.replicate j1' 0 ++ (d + 1) :: R)) (2 * j2 + 1)
        have h3 := rule_A_cons_cons (encOdds ks)
          (List.replicate j1' 0 ++ (d + 1) :: R) (2 * j2 + 1 + 2) 0
        rw [show 2 * j2 + 1 + 2 + 0 + 2 = 2 * j2 + 5 by omega] at h3
        exact ((h1.trans h2).trans h3).trans
          (ih (2 * j2 + 5) (List.replicate j1' 0 ++ (d + 1) :: R))

private theorem step_drainOddB_all (ks : List ℕ) (d : ℕ) (R : List ℕ) :
    ReachesPlus target (cfgB (encOdds ks) (d :: R)) (encode (drainOddB ks d R)) :=
  step_drainOddB ks.length ks (Nat.le_refl _) d R

private theorem step_scanE (R : List ℕ) :
    ∀ (ks : List ℕ) (d : ℕ),
      match scanE ks d R with
      | some s' => ReachesPlus target (cfgE (encOdds ks) (d :: R)) (encode s')
      | none =>
        ∃ cfg', ReachesStar target (cfgE (encOdds ks) (d :: R)) cfg' ∧
          (step target cfg').isNone := by
  induction R with
  | nil =>
    intro ks d
    simp only [scanE]
    by_cases hodd : d % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have hd : d = 2 * (d / 2) + 1 := by omega
      have h1 : ReachesPlus target (cfgE (encOdds ks) [d]) (cfgE (d :: encOdds ks) []) := by
        conv_lhs => rw [hd]
        simpa [← hd] using rule_E_odd (encOdds ks) [] (d / 2)
      refine ⟨Cfg.headRight F (ListBlank.cons 0 (encStack (d :: encOdds ks))) default,
        ?_, by bb_halt⟩
      have h2 : ReachesPlus target (cfgE (d :: encOdds ks) [])
          (Cfg.headRight F (ListBlank.cons 0 (encStack (d :: encOdds ks))) default) := by
        rw [cfgE, encStack]
        bb_steps
      exact (h1.trans h2).to_star
    · simp only [hodd, ↓reduceIte]
      have hd : d = 2 * (d / 2) := by omega
      have h1 : ReachesPlus target (cfgE (encOdds ks) [d]) (cfgA (d :: encOdds ks) []) := by
        conv_lhs => rw [hd]
        simpa [← hd] using rule_E_even (encOdds ks) [] (d / 2)
      have h2 := rule_A_nil (d :: encOdds ks)
      simp only [bumpHead] at h2
      have h3 : ReachesPlus target (cfgB ((d + 1) :: encOdds ks) [])
          (cfgC (encOdds ks) (List.replicate (d / 2 + 1) 0 ++ [0])) := by
        have hb := rule_B_odd (encOdds ks) [] (d / 2)
        simpa [bumpHead, ← hd] using hb
      rcases ks with _ | ⟨j2, ks'⟩
      · simp only [encOdds] at h1 h2 h3 ⊢
        have hrep : List.replicate (d / 2 + 1) 0 ++ [0] = 0 :: List.replicate (d / 2 + 1) 0 := by
          change List.replicate (d / 2 + 1) 0 ++ List.replicate 1 0 = _
          rw [← List.replicate_add, show d / 2 + 1 + 1 = (d / 2 + 1) + 1 by rfl,
            List.replicate_succ]
        rw [hrep] at h3
        exact ((h1.trans h2).trans h3).trans (rule_C_nil (0 :: List.replicate (d / 2 + 1) 0))
      · simp only [encOdds] at h3 ⊢
        have hrep : List.replicate (d / 2 + 1) 0 ++ [0] =
            0 :: 0 :: List.replicate (d / 2) 0 := by
          change List.replicate (d / 2 + 1) 0 ++ List.replicate 1 0 = _
          rw [← List.replicate_add, List.replicate_succ, List.replicate_succ]
        rw [hrep] at h3
        have h4 := rule_C_cons_zero (encOdds ks') (0 :: List.replicate (d / 2) 0) (2 * j2 + 1)
        have h5 := rule_A_cons_cons (encOdds ks') (List.replicate (d / 2) 0) (2 * j2 + 1 + 2) 0
        rw [show 2 * j2 + 1 + 2 + 0 + 2 = 2 * j2 + 5 by omega] at h5
        exact ((((h1.trans h2).trans h3).trans h4).trans h5).trans
          (step_drainOddB_all ks' (2 * j2 + 5) (List.replicate (d / 2) 0))
  | cons e R' ih =>
    intro ks d
    simp only [scanE]
    by_cases hodd : d % 2 = 1
    · simp only [hodd, ↓reduceIte]
      have hd : d = 2 * (d / 2) + 1 := by omega
      have h1 : ReachesPlus target (cfgE (encOdds ks) (d :: e :: R'))
          (cfgE (encOdds ((d / 2) :: ks)) (e :: R')) := by
        simp only [encOdds]
        conv_lhs => rw [hd]
        exact rule_E_odd (encOdds ks) (e :: R') (d / 2)
      have ih' := ih ((d / 2) :: ks) e
      rcases hres : scanE ((d / 2) :: ks) e R' with _ | s'
      · rw [hres] at ih'
        obtain ⟨cfg', hstar, hnone⟩ := ih'
        exact ⟨cfg', h1.to_star.trans hstar, hnone⟩
      · rw [hres] at ih'
        exact h1.trans ih'
    · simp only [hodd, ↓reduceIte]
      have hd : d = 2 * (d / 2) := by omega
      have h1 : ReachesPlus target (cfgE (encOdds ks) (d :: e :: R'))
          (cfgA (d :: encOdds ks) (e :: R')) := by
        conv_lhs => rw [hd]
        simpa [← hd] using rule_E_even (encOdds ks) (e :: R') (d / 2)
      have h2 := rule_A_cons_cons (encOdds ks) R' d e
      exact (h1.trans h2).trans (step_drainOddB_all ks (d + e + 2) R')

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  have h : ReachesPlus target (init []) (encode start) := by
    simp only [start, encode, encStack, list_pow_succ, list_pow_zero]
    bb_steps
  exact h.to_star

/-- `next` is a valid accelerated transition function for `target` from `start`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start fun s => ?_
  rcases s with ⟨d, R⟩
  have hs := step_scanE R [] d
  have heq : cfgE (encOdds []) (d :: R) = encode (.E d R) := rfl
  rw [heq] at hs
  rcases h : scanE [] d R with _ | s' <;> simpa [next, h] using hs

/-- `target` halts from the blank tape iff iterating `next` from `start` reaches `none`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RE_1LC1LB_1LE0LD_1LE1LC_0RF1RA_HHH1RA
