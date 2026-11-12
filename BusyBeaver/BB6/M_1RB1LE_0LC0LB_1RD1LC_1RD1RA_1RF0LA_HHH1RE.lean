/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE` (#424)

Formal `IsClosedPatternSet`, `HasCollatzReduction`, `IsCryptid`, and `IsValidAcceleration`
proofs for the 6-state, 2-symbol Busy Beaver holdout `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`
(bbchallenge holdout #424, discovered by Racheline).

Starting from the blank tape (`init []`), the trajectory enters the closed 2-pattern system
`ps = [(pat_A, .true), (pat_Run, .true)]` at `A(2, 0, 1)` in 12 steps, where:
$$A(a, c, d) := 0^\infty\,1^a\,\mathrm{A}{>}\,(10)^c\,1^{d+1}\,0^\infty, \qquad
  \mathrm{Run}(a) := 0^\infty\,1^a\,\mathrm{D}{>}\,0^\infty.$$

## Collatz-like Acceleration Rules

- `Run(a) -> Run(a + 1)`
- `A(a + 2, c, d) -> A(a, c + 1, d)`
- `A(0, c, 0) -> Halt`
- `A(0, c, 1) -> A(2*c + 1, 0, 0)`
- `A(0, c, d + 2) -> A(2*c + 1, 1, d)`
- `A(1, 2*k, 0) -> Run(1)`
- `A(1, 2*k + 1, 0) -> A(2, 0, 6*k + 7)`
- `A(1, 2*k, 1) -> A(2, 0, 6*k + 6)`
- `A(1, 2*k + 1, d + 1) -> A(6*k + 8, 0, d)`
- `A(1, 2*k, d + 2) -> A(6*k + 7, 0, d)`
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Pattern `pat_A` matching `A(a, c, d) := 0^∞ 1^a A> (10)^c 1^(d+1) 0^∞`. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some A
    right := .rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)) }

/-- Pattern `pat_Run` matching `Run(a) := 0^∞ 1^a D> 0^∞`. -/
def pat_Run : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [1] 0 .default
    head := some D
    right := .default }

/-- Explicit closed 2-pattern invariant certificate (`ps.length ≤ 16`). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true), (pat_Run, .true)]

/-- Symbolic states for the closed acceleration of #424. -/
inductive State where
  /-- $A(a, c, d) := 0^\infty\,1^a\,\mathrm{A}{>}\,(10)^c\,1^{d+1}\,0^\infty$. -/
  | A (a c d : ℕ)
  /-- $\mathrm{Run}(a) := 0^\infty\,1^a\,\mathrm{D}{>}\,0^\infty$. -/
  | Run (a : ℕ)
  deriving DecidableEq, Repr

/-- Entry state from the blank tape, reached after 12 raw steps. -/
def start : State := .A 2 0 1

/-- Configuration encoder for `State`. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A a c d =>
      Cfg.headRight A (([1] : List (Fin 2)) ^ a +> default)
        (([1, 0] : List (Fin 2)) ^ c +>
          ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> default)))
  | .Run a =>
      Cfg.headRight D (([1] : List (Fin 2)) ^ a +> default) default

/-- Deterministic accelerated transition function on `State`. -/
def next : State → Option State
  | .Run a => some (.Run (a + 1))
  | .A (a + 2) c d => some (.A a (c + 1) d)
  | .A 0 _ 0 => none
  | .A 0 c 1 => some (.A (2 * c + 1) 0 0)
  | .A 0 c (d + 2) => some (.A (2 * c + 1) 1 d)
  | .A 1 c 0 =>
      if c % 2 = 0 then some (.Run 1) else some (.A 2 0 (3 * c + 4))
  | .A 1 c 1 =>
      if c % 2 = 0 then some (.A 2 0 (3 * c + 6)) else some (.A (3 * c + 5) 0 0)
  | .A 1 c (d + 2) =>
      if c % 2 = 0 then some (.A (3 * c + 7) 0 d) else some (.A (3 * c + 5) 0 (d + 1))

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some E, Stmt.write 1 Dir.left) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 0 Dir.left) := rfl
private theorem target_B_1 : target B 1 = some (some B, Stmt.write 0 Dir.left) := rfl
private theorem target_C_0 : target C 0 = some (some D, Stmt.write 1 Dir.right) := rfl
private theorem target_C_1 : target C 1 = some (some C, Stmt.write 1 Dir.left) := rfl
private theorem target_D_0 : target D 0 = some (some D, Stmt.write 1 Dir.right) := rfl
private theorem target_D_1 : target D 1 = some (some A, Stmt.write 1 Dir.right) := rfl
private theorem target_E_0 : target E 0 = some (some F, Stmt.write 1 Dir.right) := rfl
private theorem target_E_1 : target E 1 = some (some A, Stmt.write 0 Dir.left) := rfl
private theorem target_F_0 : target F 0 = none := rfl
private theorem target_F_1 : target F 1 = some (some E, Stmt.write 1 Dir.right) := rfl

local macro "mstep" : tactic =>
  `(tactic| (
    simp only [step, Cfg.headRight, Cfg.headLeft,
      target_A_0, target_A_1, target_B_0, target_B_1,
      target_C_0, target_C_1, target_D_0, target_D_1,
      target_E_0, target_E_1, target_F_0, target_F_1,
      list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append, List.nil_append,
      Tape.write, Tape.move, ListBlank.append_nil, ListBlank.append_cons,
      ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.cons_zero_default, ListBlank.cons_default_default,
      ListBlank.head_default_fin, ListBlank.tail_default, Option.map]
    try rfl))

private theorem pow_zeros_append_default :
    ∀ n : ℕ, (([0] : List (Fin 2)) ^ n) +> (default : ListBlank (Fin 2)) = default
  | 0 => rfl
  | n + 1 => by
      simp only [list_pow_succ, List.singleton_append, ListBlank.append_cons,
        pow_zeros_append_default n, ListBlank.cons_zero_default]

private theorem pow10_append_one :
    ∀ (c : ℕ) (R : ListBlank (Fin 2)),
      ([1, 0] : List (Fin 2)) ^ c +> ((1 : Fin 2) >> R) =
        (1 : Fin 2) >> (([0, 1] : List (Fin 2)) ^ c +> R)
  | 0, _ => rfl
  | c + 1, R => by
      simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
        pow10_append_one c R]

private theorem pow01_split_even :
    ∀ (k : ℕ) (R : ListBlank (Fin 2)),
      ([0, 1] : List (Fin 2)) ^ (2 * k + 1) +> R =
        ([0, 1, 0, 1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> ((1 : Fin 2) >> R))
  | 0, _ => by simp [list_pow_zero, list_pow_succ]
  | k + 1, R => by
      have h : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by omega
      rw [h, list_pow_succ ([0, 1]), list_pow_succ ([0, 1]), list_pow_succ ([0, 1, 0, 1])]
      simp only [List.cons_append, List.nil_append, ListBlank.append_cons, pow01_split_even k R]

private theorem pow01_split_odd :
    ∀ (k : ℕ) (R : ListBlank (Fin 2)),
      ([0, 1] : List (Fin 2)) ^ (2 * k + 2) +> R =
        ([0, 1, 0, 1] : List (Fin 2)) ^ (k + 1) +> R
  | 0, _ => by simp [list_pow_succ, list_pow_zero]
  | k + 1, R => by
      have h : 2 * (k + 1) + 2 = (2 * k + 2) + 1 + 1 := by omega
      rw [h, list_pow_succ ([0, 1]), list_pow_succ ([0, 1]), list_pow_succ ([0, 1, 0, 1])]
      simp only [List.cons_append, List.nil_append, ListBlank.append_cons, pow01_split_odd k R]

private theorem append_sym_pow (x : Fin 2) :
    ∀ (n : ℕ) (R : ListBlank (Fin 2)),
      (([x] : List (Fin 2)) ^ n) +> (x >> R) = ([x] : List (Fin 2)) ^ (n + 1) +> R
  | n, R => by
      simpa only [list_pow_one, ListBlank.append_cons, ListBlank.append_nil] using
        (ListBlank.append_pow_succ' [x] n R)

private theorem reachesStar_F_10 :
    ∀ (c n : ℕ) (L R : ListBlank (Fin 2)),
      ReachesStar target
        (Cfg.headRight F (([1] : List (Fin 2)) ^ n +> L) (([1, 0] : List (Fin 2)) ^ c +> R))
        (Cfg.headRight F (([1] : List (Fin 2)) ^ (n + 2 * c) +> L) R)
  | 0, _, _, _ => ReachesStar.refl _ _
  | c + 1, n, L, R => by
      have h1 :
          step target
            (Cfg.headRight F (([1] : List (Fin 2)) ^ n +> L)
              (([1, 0] : List (Fin 2)) ^ (c + 1) +> R)) =
          some (Cfg.headRight E (([1] : List (Fin 2)) ^ (n + 1) +> L)
            ((0 : Fin 2) >> (([1, 0] : List (Fin 2)) ^ c +> R))) := by
        mstep
      have h2 :
          step target
            (Cfg.headRight E (([1] : List (Fin 2)) ^ (n + 1) +> L)
              ((0 : Fin 2) >> (([1, 0] : List (Fin 2)) ^ c +> R))) =
          some (Cfg.headRight F (([1] : List (Fin 2)) ^ (n + 2) +> L)
            (([1, 0] : List (Fin 2)) ^ c +> R)) := by
        mstep
      refine ReachesStar.head h1 (ReachesStar.head h2 ?_)
      simpa only [Nat.add_assoc, show 2 + 2 * c = 2 * (c + 1) from by omega] using
        reachesStar_F_10 c (n + 2) L R

private theorem sweep_B_left :
    ∀ (n : ℕ) (L R : ListBlank (Fin 2)),
      ReachesStar target
        (Cfg.headLeft B (([1] : List (Fin 2)) ^ n +> L) R)
        (Cfg.headLeft B L (([0] : List (Fin 2)) ^ n +> R))
  | 0, _, _ => ReachesStar.refl _ _
  | n + 1, L, R => by
      have h1 :
          step target (Cfg.headLeft B (([1] : List (Fin 2)) ^ (n + 1) +> L) R) =
            some (Cfg.headLeft B (([1] : List (Fin 2)) ^ n +> L) ((0 : Fin 2) >> R)) := by
        mstep
      refine ReachesStar.head h1 ?_
      have ih := sweep_B_left n L ((0 : Fin 2) >> R)
      simpa only [append_sym_pow] using ih

private theorem sweep_D_right :
    ∀ (n m : ℕ) (L R : ListBlank (Fin 2)),
      ReachesStar target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ m +> L) (([0] : List (Fin 2)) ^ n +> R))
        (Cfg.headRight D (([1] : List (Fin 2)) ^ (m + n) +> L) R)
  | 0, _, _, _ => ReachesStar.refl _ _
  | n + 1, m, L, R => by
      have h1 :
          step target
            (Cfg.headRight D (([1] : List (Fin 2)) ^ m +> L)
              (([0] : List (Fin 2)) ^ (n + 1) +> R)) =
          some (Cfg.headRight D (([1] : List (Fin 2)) ^ (m + 1) +> L)
            (([0] : List (Fin 2)) ^ n +> R)) := by
        mstep
      refine ReachesStar.head h1 ?_
      simpa only [Nat.add_assoc, Nat.add_comm 1 n] using sweep_D_right n (m + 1) L R

private theorem sweep_C_left :
    ∀ (n : ℕ) (L R : ListBlank (Fin 2)),
      ReachesStar target
        (Cfg.headLeft C (([1] : List (Fin 2)) ^ n +> L) R)
        (Cfg.headLeft C L (([1] : List (Fin 2)) ^ n +> R))
  | 0, _, _ => ReachesStar.refl _ _
  | n + 1, L, R => by
      have h1 :
          step target (Cfg.headLeft C (([1] : List (Fin 2)) ^ (n + 1) +> L) R) =
            some (Cfg.headLeft C (([1] : List (Fin 2)) ^ n +> L) ((1 : Fin 2) >> R)) := by
        mstep
      refine ReachesStar.head h1 ?_
      have ih := sweep_C_left n L ((1 : Fin 2) >> R)
      simpa only [append_sym_pow] using ih

private theorem loop_0101_step (m : ℕ) (R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (([1] : List (Fin 2)) ^ m +> default) (([0, 1, 0, 1] : List (Fin 2)) +> R))
      (Cfg.headRight A (([1] : List (Fin 2)) ^ (m + 6) +> default) R) := by
  have h1 :
      step target
        (Cfg.headRight A (([1] : List (Fin 2)) ^ m +> default)
          (([0, 1, 0, 1] : List (Fin 2)) +> R)) =
      some (Cfg.headRight B (([1] : List (Fin 2)) ^ (m + 1) +> default)
        ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  have h2 :
      step target
        (Cfg.headRight B (([1] : List (Fin 2)) ^ (m + 1) +> default)
          ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) =
      some (Cfg.headLeft B (([1] : List (Fin 2)) ^ (m + 1) +> default)
        ((0 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  have hB :=
    sweep_B_left (m + 1) default ((0 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))
  have hB' :
      ReachesStar target
        (Cfg.headLeft B (([1] : List (Fin 2)) ^ (m + 1) +> default)
          ((0 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R))))
        (Cfg.headLeft B default (([0] : List (Fin 2)) ^ (m + 3) +> ((1 : Fin 2) >> R))) := by
    rw [append_sym_pow (0 : Fin 2) (m + 1) ((0 : Fin 2) >> ((1 : Fin 2) >> R)),
      append_sym_pow (0 : Fin 2) (m + 2) ((1 : Fin 2) >> R)] at hB
    exact hB
  have h3 :
      step target
        (Cfg.headLeft B default (([0] : List (Fin 2)) ^ (m + 3) +> ((1 : Fin 2) >> R))) =
      some (Cfg.headLeft C default (([0] : List (Fin 2)) ^ (m + 4) +> ((1 : Fin 2) >> R))) := by
    mstep
  have h4 :
      step target
        (Cfg.headLeft C default (([0] : List (Fin 2)) ^ (m + 4) +> ((1 : Fin 2) >> R))) =
      some (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
        (([0] : List (Fin 2)) ^ (m + 4) +> ((1 : Fin 2) >> R))) := by
    mstep
  have hD := sweep_D_right (m + 4) 1 default ((1 : Fin 2) >> R)
  have hD' :
      ReachesStar target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          (([0] : List (Fin 2)) ^ (m + 4) +> ((1 : Fin 2) >> R)))
        (Cfg.headRight D (([1] : List (Fin 2)) ^ (m + 5) +> default) ((1 : Fin 2) >> R)) := by
    simpa only [Nat.add_comm 1 (m + 4)] using hD
  have h5 :
      step target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ (m + 5) +> default) ((1 : Fin 2) >> R)) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ (m + 6) +> default) R) := by
    mstep
  exact ReachesPlus.head h1 (ReachesStar.head h2
    (hB'.trans (ReachesStar.head h3 (ReachesStar.head h4 (hD'.trans (ReachesStar.single h5))))))

private theorem loop_0101 :
    ∀ (k m : ℕ) (R : ListBlank (Fin 2)),
      ReachesStar target
        (Cfg.headRight A (([1] : List (Fin 2)) ^ m +> default)
          (([0, 1, 0, 1] : List (Fin 2)) ^ k +> R))
        (Cfg.headRight A (([1] : List (Fin 2)) ^ (m + 6 * k) +> default) R)
  | 0, _, _ => ReachesStar.refl _ _
  | k + 1, m, R => by
      have hk :
          (([0, 1, 0, 1] : List (Fin 2)) ^ (k + 1) +> R) =
            ([0, 1, 0, 1] : List (Fin 2)) +> (([0, 1, 0, 1] : List (Fin 2)) ^ k +> R) := by
        simp only [list_pow_succ, ListBlank.append_assoc]
      rw [hk]
      refine (loop_0101_step m _).to_star.trans ?_
      simpa only [Nat.add_assoc, show 6 + 6 * k = 6 * (k + 1) from by omega] using
        loop_0101 k (m + 6) R

private theorem step_Run (a : ℕ) :
    ReachesPlus target (encode (.Run a)) (encode (.Run (a + 1))) :=
  ReachesPlus.single (by simp only [encode]; mstep)

private theorem step_A_ge2 (a c d : ℕ) :
    ReachesPlus target (encode (.A (a + 2) c d)) (encode (.A a (c + 1) d)) := by
  simp only [encode]
  rw [pow10_append_one]
  set R := ([0, 1] : List (Fin 2)) ^ c +> (([1] : List (Fin 2)) ^ d +> default)
  have h1 :
      step target
        (Cfg.headRight A (([1] : List (Fin 2)) ^ (a + 2) +> default) ((1 : Fin 2) >> R)) =
      some (Cfg.headLeft E (([1] : List (Fin 2)) ^ (a + 2) +> default) ((1 : Fin 2) >> R)) := by
    mstep
  have h2 :
      step target
        (Cfg.headLeft E (([1] : List (Fin 2)) ^ (a + 2) +> default) ((1 : Fin 2) >> R)) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ a +> default)
        ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  refine ReachesPlus.head h1 (ReachesStar.single ?_)
  simpa only [R, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
    ← pow10_append_one] using h2

private theorem step_A0_to_F (c : ℕ) (R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default (([1, 0] : List (Fin 2)) ^ c +> ((1 : Fin 2) >> R)))
      (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default) ((1 : Fin 2) >> R)) := by
  rw [pow10_append_one]
  have h1 :
      step target (Cfg.headRight A default ((1 : Fin 2) >> (([0, 1] : List (Fin 2)) ^ c +> R))) =
        some (Cfg.headLeft E default ((1 : Fin 2) >> (([0, 1] : List (Fin 2)) ^ c +> R))) := by
    mstep
  have h2 :
      step target (Cfg.headLeft E default ((1 : Fin 2) >> (([0, 1] : List (Fin 2)) ^ c +> R))) =
        some (Cfg.headRight F (([1] : List (Fin 2)) ^ 1 +> default)
          (([1, 0] : List (Fin 2)) ^ c +> ((1 : Fin 2) >> R))) := by
    rw [pow10_append_one]
    mstep
  have hF := reachesStar_F_10 c 1 default ((1 : Fin 2) >> R)
  have hF' :
      ReachesStar target
        (Cfg.headRight F (([1] : List (Fin 2)) ^ 1 +> default)
          (([1, 0] : List (Fin 2)) ^ c +> ((1 : Fin 2) >> R)))
        (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default) ((1 : Fin 2) >> R)) := by
    simpa only [Nat.add_comm 1 (2 * c)] using hF
  exact ReachesPlus.head h1 (ReachesStar.head h2 hF')

private theorem step_A0_c0_halt (c : ℕ) :
    ∃ cfg', ReachesPlus target (encode (.A 0 c 0)) cfg' ∧ (step target cfg').isNone := by
  simp only [encode, list_pow_zero, ListBlank.append_nil]
  refine ⟨Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 3) +> default) default, ?_, ?_⟩
  · have hF := step_A0_to_F c default
    have h1 :
        step target
          (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
            ((1 : Fin 2) >> default)) =
          some (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default) default) := by
      mstep
    have h2 :
        step target
          (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default) default) =
          some (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 3) +> default) default) := by
      mstep
    exact hF.trans_star (ReachesStar.head h1 (ReachesStar.single h2))
  · mstep

private theorem step_A0_c1 (c : ℕ) :
    ReachesPlus target (encode (.A 0 c 1)) (encode (.A (2 * c + 1) 0 0)) := by
  simp only [encode, list_pow_zero, ListBlank.append_nil]
  have hF := step_A0_to_F c ((1 : Fin 2) >> default)
  have h1 :
      step target
        (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
          ((1 : Fin 2) >> ((1 : Fin 2) >> default))) =
      some (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default)
        ((1 : Fin 2) >> default)) := by
    mstep
  have h2 :
      step target
        (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default)
          ((1 : Fin 2) >> default)) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
        ((1 : Fin 2) >> default)) := by
    mstep
  exact hF.trans_star (ReachesStar.head h1 (ReachesStar.single h2))

private theorem step_A0_cd2 (c d : ℕ) :
    ReachesPlus target (encode (.A 0 c (d + 2))) (encode (.A (2 * c + 1) 1 d)) := by
  simp only [encode, list_pow_zero, ListBlank.append_nil]
  let R := ([1] : List (Fin 2)) ^ d +> default
  have hF := step_A0_to_F c ((1 : Fin 2) >> ((1 : Fin 2) >> R))
  have h1 :
      step target
        (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
          ((1 : Fin 2) >> ((1 : Fin 2) >> ((1 : Fin 2) >> R)))) =
      some (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default)
        ((1 : Fin 2) >> ((1 : Fin 2) >> R))) := by
    mstep
  have h2 :
      step target
        (Cfg.headRight E (([1] : List (Fin 2)) ^ (2 * c + 2) +> default)
          ((1 : Fin 2) >> ((1 : Fin 2) >> R))) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
        ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  have hF' :
      ReachesPlus target
        (Cfg.headRight A default
          (([1, 0] : List (Fin 2)) ^ c +>
            ((1 : Fin 2) >> ((1 : Fin 2) >> ((1 : Fin 2) >> R)))))
        (Cfg.headRight F (([1] : List (Fin 2)) ^ (2 * c + 1) +> default)
          ((1 : Fin 2) >> ((1 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    simpa only [R, list_pow_succ, List.singleton_append, ListBlank.append_cons] using hF
  simpa only [R, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil] using
    hF'.trans_star (ReachesStar.head h1 (ReachesStar.single h2))

private theorem step_A1_preamble (c d : ℕ) :
    ReachesPlus target (encode (.A 1 c d))
      (Cfg.headRight A (([1] : List (Fin 2)) ^ 2 +> default)
        (([0, 1] : List (Fin 2)) ^ (c + 1) +> (([1] : List (Fin 2)) ^ d +> default))) := by
  simp only [encode]
  rw [pow10_append_one]
  set R := ([0, 1] : List (Fin 2)) ^ c +> (([1] : List (Fin 2)) ^ d +> default)
  have h01 :
      ([0, 1] : List (Fin 2)) ^ (c + 1) +> (([1] : List (Fin 2)) ^ d +> default) =
        (0 : Fin 2) >> ((1 : Fin 2) >> R) := by
    simp only [R, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]
  rw [h01]
  have h1 :
      step target (Cfg.headRight A (([1] : List (Fin 2)) ^ 1 +> default) ((1 : Fin 2) >> R)) =
        some (Cfg.headLeft E (([1] : List (Fin 2)) ^ 1 +> default) ((1 : Fin 2) >> R)) := by
    mstep
  have h2 :
      step target (Cfg.headLeft E (([1] : List (Fin 2)) ^ 1 +> default) ((1 : Fin 2) >> R)) =
        some (Cfg.headLeft A default ((0 : Fin 2) >> ((1 : Fin 2) >> R))) := by
    mstep
  have h3 :
      step target (Cfg.headLeft A default ((0 : Fin 2) >> ((1 : Fin 2) >> R))) =
        some (Cfg.headRight B (([1] : List (Fin 2)) ^ 1 +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> R))) := by
    mstep
  have h4 :
      step target
        (Cfg.headRight B (([1] : List (Fin 2)) ^ 1 +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> R))) =
      some (Cfg.headLeft C (([1] : List (Fin 2)) ^ 1 +> default)
        ((0 : Fin 2) >> ((1 : Fin 2) >> R))) := by
    mstep
  have h5 :
      step target
        (Cfg.headLeft C (([1] : List (Fin 2)) ^ 1 +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> R))) =
      some (Cfg.headLeft C default
        ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  have h6 :
      step target (Cfg.headLeft C default ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) =
        some (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) := by
    mstep
  have h7 :
      step target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          ((1 : Fin 2) >> ((0 : Fin 2) >> ((1 : Fin 2) >> R)))) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ 2 +> default)
        ((0 : Fin 2) >> ((1 : Fin 2) >> R))) := by
    mstep
  exact ReachesPlus.head h1 (ReachesStar.head h2 (ReachesStar.head h3
    (ReachesStar.head h4 (ReachesStar.head h5 (ReachesStar.head h6 (ReachesStar.single h7))))))

private theorem end_odd_0 (n : ℕ) :
    ReachesPlus target
      (Cfg.headRight A (([1] : List (Fin 2)) ^ (n + 1) +> default) default)
      (encode (.A 2 0 n)) := by
  have h1 :
      step target (Cfg.headRight A (([1] : List (Fin 2)) ^ (n + 1) +> default) default) =
        some (Cfg.headRight B (([1] : List (Fin 2)) ^ (n + 2) +> default) default) := by
    mstep
  have h2 :
      step target (Cfg.headRight B (([1] : List (Fin 2)) ^ (n + 2) +> default) default) =
        some (Cfg.headLeft C (([1] : List (Fin 2)) ^ (n + 2) +> default) default) := by
    mstep
  have hC := sweep_C_left (n + 2) default (default : ListBlank (Fin 2))
  have h3 :
      step target (Cfg.headLeft C default (([1] : List (Fin 2)) ^ (n + 2) +> default)) =
        some (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          (([1] : List (Fin 2)) ^ (n + 2) +> default)) := by
    mstep
  have h4 :
      step target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          (([1] : List (Fin 2)) ^ (n + 2) +> default)) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ 2 +> default)
        ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ n +> default))) := by
    simp only [list_pow_succ, List.singleton_append, ListBlank.append_cons]
    mstep
  exact ReachesPlus.head h1 (ReachesStar.head h2 (hC.trans
    (ReachesStar.head h3 (ReachesStar.single h4))))

private theorem end_even_tail_to_D (m : ℕ) (R : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A (([1] : List (Fin 2)) ^ m +> default) ((0 : Fin 2) >> ((1 : Fin 2) >> R)))
      (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
        (([0] : List (Fin 2)) ^ (m + 3) +> R)) := by
  have h1 :
      step target
        (Cfg.headRight A (([1] : List (Fin 2)) ^ m +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> R))) =
      some (Cfg.headRight B (([1] : List (Fin 2)) ^ (m + 1) +> default) ((1 : Fin 2) >> R)) := by
    mstep
  have h2 :
      step target
        (Cfg.headRight B (([1] : List (Fin 2)) ^ (m + 1) +> default) ((1 : Fin 2) >> R)) =
      some (Cfg.headLeft B (([1] : List (Fin 2)) ^ (m + 1) +> default) ((0 : Fin 2) >> R)) := by
    mstep
  have hB := sweep_B_left (m + 1) default ((0 : Fin 2) >> R)
  have hB' :
      ReachesStar target
        (Cfg.headLeft B (([1] : List (Fin 2)) ^ (m + 1) +> default) ((0 : Fin 2) >> R))
        (Cfg.headLeft B default (([0] : List (Fin 2)) ^ (m + 2) +> R)) := by
    simpa only [append_sym_pow] using hB
  have h3 :
      step target (Cfg.headLeft B default (([0] : List (Fin 2)) ^ (m + 2) +> R)) =
        some (Cfg.headLeft C default (([0] : List (Fin 2)) ^ (m + 3) +> R)) := by
    mstep
  have h4 :
      step target (Cfg.headLeft C default (([0] : List (Fin 2)) ^ (m + 3) +> R)) =
        some (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          (([0] : List (Fin 2)) ^ (m + 3) +> R)) := by
    mstep
  exact ReachesPlus.head h1 (ReachesStar.head h2
    (hB'.trans (ReachesStar.head h3 (ReachesStar.single h4))))

private theorem step_A1_even_0 (k : ℕ) :
    ReachesPlus target (encode (.A 1 (2 * k) 0)) (encode (.Run 1)) := by
  have hpre := step_A1_preamble (2 * k) 0
  rw [list_pow_zero, ListBlank.append_nil, pow01_split_even] at hpre
  have hloop := loop_0101 k 2 ((0 : Fin 2) >> ((1 : Fin 2) >> default))
  have hend := end_even_tail_to_D (2 + 6 * k) default
  rw [pow_zeros_append_default] at hend
  exact (hpre.trans_star hloop).trans hend

private theorem step_A1_odd_0 (k : ℕ) :
    ReachesPlus target (encode (.A 1 (2 * k + 1) 0)) (encode (.A 2 0 (6 * k + 7))) := by
  have hpre := step_A1_preamble (2 * k + 1) 0
  rw [list_pow_zero, ListBlank.append_nil, show 2 * k + 1 + 1 = 2 * k + 2 from rfl,
    pow01_split_odd] at hpre
  have hloop := loop_0101 (k + 1) 2 (default : ListBlank (Fin 2))
  have hend := end_odd_0 (6 * k + 7)
  rw [show 2 + 6 * (k + 1) = 6 * k + 7 + 1 from by omega] at hloop
  exact (hpre.trans_star hloop).trans hend

private theorem step_A1_even_1 (k : ℕ) :
    ReachesPlus target (encode (.A 1 (2 * k) 1)) (encode (.A 2 0 (6 * k + 6))) := by
  have hpre := step_A1_preamble (2 * k) 1
  rw [pow01_split_even] at hpre
  have hloop :=
    loop_0101 k 2 ((0 : Fin 2) >> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ 1 +> default)))
  have hend := end_even_tail_to_D (2 + 6 * k) ((1 : Fin 2) >> default)
  have hD := sweep_D_right (2 + 6 * k + 3) 1 default ((1 : Fin 2) >> default)
  have hD1 :
      step target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ (1 + (2 + 6 * k + 3)) +> default)
          ((1 : Fin 2) >> default)) =
      some (Cfg.headRight A (([1] : List (Fin 2)) ^ (6 * k + 7) +> default) default) := by
    rw [show 1 + (2 + 6 * k + 3) = 6 * k + 6 from by omega]
    mstep
  have hodd := end_odd_0 (6 * k + 6)
  have hpre' :
      ReachesPlus target (encode (.A 1 (2 * k) 1))
        (Cfg.headRight A (([1] : List (Fin 2)) ^ (2 + 6 * k) +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> ((1 : Fin 2) >> default)))) := by
    refine hpre.trans_star ?_
    simpa only [list_pow_one, List.singleton_append, ListBlank.append_cons,
      ListBlank.append_nil] using hloop
  exact ((hpre'.trans hend).trans_star (hD.trans (ReachesStar.single hD1))).trans hodd

private theorem step_A1_even_d2 (k d : ℕ) :
    ReachesPlus target (encode (.A 1 (2 * k) (d + 2))) (encode (.A (6 * k + 7) 0 d)) := by
  have hpre := step_A1_preamble (2 * k) (d + 2)
  rw [pow01_split_even] at hpre
  have hloop :=
    loop_0101 k 2 ((0 : Fin 2) >> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ (d + 2) +> default)))
  let R := (1 : Fin 2) >> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ d +> default))
  have hend := end_even_tail_to_D (2 + 6 * k) R
  have hD := sweep_D_right (2 + 6 * k + 3) 1 default R
  have hD1 :
      step target
        (Cfg.headRight D (([1] : List (Fin 2)) ^ (1 + (2 + 6 * k + 3)) +> default) R) =
      some (encode (.A (6 * k + 7) 0 d)) := by
    simp only [encode, list_pow_zero, ListBlank.append_nil, R]
    rw [show 1 + (2 + 6 * k + 3) = 6 * k + 6 from by omega]
    mstep
  have hend' :
      ReachesPlus target
        (Cfg.headRight A (([1] : List (Fin 2)) ^ (2 + 6 * k) +> default)
          ((0 : Fin 2) >> ((1 : Fin 2) >> (([1] : List (Fin 2)) ^ (d + 2) +> default))))
        (Cfg.headRight D (([1] : List (Fin 2)) ^ 1 +> default)
          (([0] : List (Fin 2)) ^ (2 + 6 * k + 3) +> R)) := by
    simpa only [R, list_pow_succ, List.singleton_append, ListBlank.append_cons] using hend
  exact (hpre.trans_star hloop).trans (hend'.trans_star (hD.trans (ReachesStar.single hD1)))

private theorem step_A1_odd_d1 (k d : ℕ) :
    ReachesPlus target (encode (.A 1 (2 * k + 1) (d + 1))) (encode (.A (6 * k + 8) 0 d)) := by
  have hpre := step_A1_preamble (2 * k + 1) (d + 1)
  rw [show 2 * k + 1 + 1 = 2 * k + 2 from rfl, pow01_split_odd] at hpre
  have hloop := loop_0101 (k + 1) 2 (([1] : List (Fin 2)) ^ (d + 1) +> default)
  simpa only [encode, list_pow_zero, list_pow_succ, List.singleton_append, ListBlank.append_cons,
    ListBlank.append_nil, show 2 + 6 * (k + 1) = 6 * k + 8 from by omega] using
    hpre.trans_star hloop

private theorem init_reaches_start : ReachesPlus target (init []) (encode start) := by
  dsimp only [start, encode, list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append,
    List.nil_append, ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

/-- Level B valid acceleration theorem for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_start.to_star ?_
  intro s
  cases s with
  | Run a => exact step_Run a
  | A a c d =>
      rcases a with _ | _ | a
      · rcases d with _ | _ | d
        · obtain ⟨cfg', hplus, hnone⟩ := step_A0_c0_halt c
          exact ⟨cfg', hplus.to_star, hnone⟩
        · simpa [next] using step_A0_c1 c
        · simpa [next] using step_A0_cd2 c d
      · rcases Nat.even_or_odd' c with ⟨k, rfl | rfl⟩
        · rcases d with _ | _ | d
          · simpa [next] using step_A1_even_0 k
          · simpa [next, show 3 * (2 * k) + 6 = 6 * k + 6 from by omega] using
              step_A1_even_1 k
          · simpa [next, show 3 * (2 * k) + 7 = 6 * k + 7 from by omega] using
              step_A1_even_d2 k d
        · have hmod : (2 * k + 1) % 2 ≠ 0 := by omega
          rcases d with _ | d
          · simpa [next, hmod, show 3 * (2 * k + 1) + 4 = 6 * k + 7 from by omega] using
              step_A1_odd_0 k
          · rcases d with _ | d
            · simpa [next, hmod, show 3 * (2 * k + 1) + 5 = 6 * k + 8 from by omega] using
                step_A1_odd_d1 k 0
            · simpa [next, hmod, show 3 * (2 * k + 1) + 5 = 6 * k + 8 from by omega] using
                step_A1_odd_d1 k (d + 1)
      · simpa [next] using step_A_ge2 a c d

/-- Machine halting equivalence for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

private theorem encode_in_ps : ∀ s, IsInPatternSet ps (encode s)
  | .A a c d => by
      refine ⟨(pat_A, .true), by simp [ps], fun k => match k with | 0 => a | 1 => c | _ => d,
        ?_, trivial⟩
      rfl
  | .Run a => by
      refine ⟨(pat_Run, .true), by simp [ps], fun _ => a, ?_, trivial⟩
      rfl

private theorem of_in_ps : ∀ cfg, IsInPatternSet ps cfg → ∃ s, cfg = encode s := by
  rintro cfg ⟨⟨pat, cond⟩, hmem, v, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact ⟨.A (v 0) (v 1) (v 2), rfl⟩
  · exact ⟨.Run (v 0), rfl⟩

/-- Level A closed pattern-set invariant for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine is_valid_acceleration.isClosedPatternSet encode_in_ps of_in_ps ?_
  intro s hnext
  cases s with
  | Run _ => simp [next] at hnext
  | A a c d =>
      rcases a with _ | _ | a
      · rcases d with _ | _ | d
        · exact step_A0_c0_halt c
        · simp [next] at hnext
        · simp [next] at hnext
      · change next (.A 1 c d) = none at hnext
        rcases d with _ | _ | d <;> simp only [next] at hnext <;> split_ifs at hnext
      · simp [next] at hnext

/-- Level A Collatz-like reduction for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-- Rule-bounded cryptid certificate for `1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_---1RE`. -/
theorem is_cryptid : IsCryptid target :=
  ⟨ps, by decide, is_closed_pattern_set⟩

end BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE
