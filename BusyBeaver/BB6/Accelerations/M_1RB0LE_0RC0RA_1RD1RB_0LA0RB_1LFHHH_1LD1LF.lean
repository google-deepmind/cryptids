/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`

Formal Collatz-like transducer acceleration (`IsValidAcceleration`) for the 6-state, 2-symbol
Busy Beaver holdout `1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF`.

Both half-tapes are represented as zero-run stacks `List ℕ` via `encRun`, where each entry `k`
encodes the block `0^k 1`:
$$E(L, R) := \mathrm{encRun}(L) <\!\mathrm{E}\, \mathrm{encRun}(R).$$
Starting from the blank tape (`init []`), the machine reaches `start = .E [1] []` after 5 raw
Turing machine steps. Halting (`E1 -> ---`) occurs immediately when the left zero-run stack begins
with `0 :: _`.

## Accelerated Transition Rules

```text
encRun []        = 0^inf
encRun (k :: xs) = 0^k 1 ++ encRun xs

incRun []        = []
incRun (k :: xs) = (k + 1) :: xs

E([], R)          -> sweepFL([], 0 :: R)
E(0 :: _, _)      -> Halt
E((a+1) :: Lt, R) -> sweepFL(a :: Lt, 0 :: R)

sweepFL([], R)          = sweepRight(ar, [], 2 :: R)
sweepFL(0 :: Lt, R)     = sweepFL(Lt, 0 :: R)
sweepFL(1 :: Lt, R)     = sweepRight(br, incRun Lt, 0 :: R)
sweepFL(2 :: Lt, R)     = E(Lt, 2 :: R)
sweepFL((a+3) :: Lt, R) = sweepRight(ar, a :: Lt, 2 :: R)

Start: E([1], []), reached after 5 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LF---_1LD1LF"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Rightward sweep control state (`A`, `B`, or `C`). -/
inductive RightMode where
  | ar
  | br
  | cr
  deriving DecidableEq, Repr

/-- Symbolic configuration state `E(L, R)` over zero-run stacks. -/
inductive State where
  | E (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Step across a single zero-run stack entry `0^d 1` during a rightward `{A, B, C}` sweep. -/
def sweepElem (stepRt : RightMode → List ℕ → State) :
    ℕ → RightMode → List ℕ → List ℕ → State
  | 0, .ar, L, Rt => .E L (incRun Rt)
  | 0, .br, L, _ => stepRt .ar (incRun L)
  | 0, .cr, L, _ => stepRt .br (0 :: L)
  | d + 1, .ar, L, Rt => sweepElem stepRt d .br (0 :: L) Rt
  | d + 1, .br, L, Rt => sweepElem stepRt d .cr (incRun L) Rt
  | 1, .cr, L, _ => stepRt .br (1 :: L)
  | d + 2, .cr, L, Rt => .E L ((d + 2) :: Rt)

/-- Rightward `{A, B, C}` sweep across `encRun R`, returning to an `E`-mode configuration. -/
def sweepRight : RightMode → List ℕ → List ℕ → State
  | .ar, L, [] => .E (1 :: L) []
  | .br, L, [] => .E (incRun L) []
  | .cr, L, [] => .E L []
  | m, L, d :: Rt => sweepElem (fun m' L' => sweepRight m' L' Rt) d m L Rt

/-- Leftward `F`-mode sweep across `encRun L`, transitioning into `sweepRight` or `E`. -/
def sweepFL : List ℕ → List ℕ → State
  | [], R => sweepRight .ar [] (2 :: R)
  | 0 :: Lt, R => sweepFL Lt (0 :: R)
  | 1 :: Lt, R => sweepRight .br (incRun Lt) (0 :: R)
  | 2 :: Lt, R => .E Lt (2 :: R)
  | (a + 3) :: Lt, R => sweepRight .ar (a :: Lt) (2 :: R)

/-- Initial accelerated state, reached after 5 raw Turing machine steps from `init []`. -/
def start : State := .E [1] []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .E L R => Cfg.headLeft SixState.E (encRun L) (encRun R)

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .E [] R => some (sweepFL [] (0 :: R))
  | .E (0 :: _) _ => none
  | .E ((a + 1) :: Lt) R => some (sweepFL (a :: Lt) (0 :: R))

/-! ## Zero-Run Encoding Lemmas -/

private theorem encRun_nil : encRun [] = default :=
  rfl

private theorem encRun_zero (xs : List ℕ) :
    encRun (0 :: xs) = ListBlank.cons 1 (encRun xs) :=
  rfl

private theorem encRun_succ (k : ℕ) (xs : List ℕ) :
    encRun ((k + 1) :: xs) = ListBlank.cons 0 (encRun (k :: xs)) := by
  simp only [encRun, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem zero_cons_encRun (xs : List ℕ) :
    ListBlank.cons 0 (encRun xs) = encRun (incRun xs) := by
  rcases xs with _ | ⟨k, xs'⟩
  · simp [encRun, incRun]
  · exact (encRun_succ k xs').symm

/-! ## Rightward and Leftward Sweep Lemmas -/

private def rightCfg : RightMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .ar, L, R => Cfg.headRight A (encRun L) (encRun R)
  | .br, L, R => Cfg.headRight B (encRun L) (encRun R)
  | .cr, L, R => Cfg.headRight C (encRun L) (encRun R)

private theorem sweepElem_spec (stepRt : RightMode → List ℕ → State) (Rt : List ℕ)
    (hRt : ∀ m' L', ReachesPlus target (rightCfg m' L' Rt) (encode (stepRt m' L')))
    (d : ℕ) (m : RightMode) (L : List ℕ) :
    ReachesPlus target (rightCfg m L (d :: Rt)) (encode (sweepElem stepRt d m L Rt)) := by
  induction d generalizing m L with
  | zero =>
    cases m with
    | ar =>
      dsimp only [sweepElem, rightCfg, encode]
      rw [encRun_zero, ← zero_cons_encRun Rt]
      bb_steps
    | br =>
      dsimp only [sweepElem, rightCfg]
      have h1 : ReachesPlus target
          (Cfg.headRight B (encRun L) (encRun (0 :: Rt)))
          (rightCfg .ar (incRun L) Rt) := by
        dsimp only [rightCfg]
        rw [encRun_zero, ← zero_cons_encRun L]
        bb_steps
      exact h1.trans (hRt .ar (incRun L))
    | cr =>
      dsimp only [sweepElem, rightCfg]
      have h1 : ReachesPlus target
          (Cfg.headRight C (encRun L) (encRun (0 :: Rt)))
          (rightCfg .br (0 :: L) Rt) := by
        dsimp only [rightCfg]
        rw [encRun_zero, encRun_zero]
        bb_steps
      exact h1.trans (hRt .br (0 :: L))
  | succ d ih =>
    cases m with
    | ar =>
      dsimp only [sweepElem, rightCfg]
      have h1 : ReachesPlus target
          (Cfg.headRight A (encRun L) (encRun ((d + 1) :: Rt)))
          (rightCfg .br (0 :: L) (d :: Rt)) := by
        dsimp only [rightCfg]
        rw [encRun_succ, encRun_zero]
        bb_steps
      exact h1.trans (ih .br (0 :: L))
    | br =>
      dsimp only [sweepElem, rightCfg]
      have h1 : ReachesPlus target
          (Cfg.headRight B (encRun L) (encRun ((d + 1) :: Rt)))
          (rightCfg .cr (incRun L) (d :: Rt)) := by
        dsimp only [rightCfg]
        rw [encRun_succ, ← zero_cons_encRun L]
        bb_steps
      exact h1.trans (ih .cr (incRun L))
    | cr =>
      rcases d with _ | d'
      · dsimp only [sweepElem, rightCfg]
        have h1 : ReachesPlus target
            (Cfg.headRight C (encRun L) (encRun (1 :: Rt)))
            (rightCfg .br (1 :: L) Rt) := by
          dsimp only [rightCfg]
          rw [encRun_succ, encRun_zero, encRun_succ, encRun_zero]
          bb_steps
        exact h1.trans (hRt .br (1 :: L))
      · dsimp only [sweepElem, rightCfg, encode]
        rw [encRun_succ (d' + 1), encRun_succ d']
        bb_steps

private theorem sweepRight_spec (m : RightMode) (L R : List ℕ) :
    ReachesPlus target (rightCfg m L R) (encode (sweepRight m L R)) := by
  induction R generalizing m L with
  | nil =>
    cases m with
    | ar =>
      dsimp only [sweepRight, rightCfg, encode]
      rw [encRun_nil, encRun_succ, encRun_zero]
      bb_steps
    | br =>
      dsimp only [sweepRight, rightCfg, encode]
      rw [encRun_nil, ← zero_cons_encRun L]
      bb_steps
    | cr =>
      dsimp only [sweepRight, rightCfg, encode]
      rw [encRun_nil]
      bb_steps
  | cons d Rt ih =>
    cases m <;> exact sweepElem_spec (fun m' L' => sweepRight m' L' Rt) Rt ih d _ L

private theorem sweepFL_spec (L R : List ℕ) :
    ReachesPlus target (Cfg.headLeft F (encRun L) (encRun R)) (encode (sweepFL L R)) := by
  induction L generalizing R with
  | nil =>
    dsimp only [sweepFL]
    have h1 : ReachesPlus target
        (Cfg.headLeft F (encRun []) (encRun R))
        (rightCfg .ar [] (2 :: R)) := by
      dsimp only [rightCfg]
      rw [encRun_nil, encRun_succ, encRun_succ, encRun_zero]
      bb_steps
    exact h1.trans (sweepRight_spec .ar [] (2 :: R))
  | cons a Lt ih =>
    rcases a with _ | _ | _ | a
    · dsimp only [sweepFL]
      have h1 : ReachesPlus target
          (Cfg.headLeft F (encRun (0 :: Lt)) (encRun R))
          (Cfg.headLeft F (encRun Lt) (encRun (0 :: R))) := by
        rw [encRun_zero, encRun_zero]
        bb_steps
      exact h1.trans (ih (0 :: R))
    · dsimp only [sweepFL]
      have h1 : ReachesPlus target
          (Cfg.headLeft F (encRun (1 :: Lt)) (encRun R))
          (rightCfg .br (incRun Lt) (0 :: R)) := by
        dsimp only [rightCfg]
        rw [encRun_succ, encRun_zero, ← zero_cons_encRun Lt, encRun_zero]
        bb_steps
      exact h1.trans (sweepRight_spec .br (incRun Lt) (0 :: R))
    · dsimp only [sweepFL, encode]
      rw [encRun_succ, encRun_succ, encRun_zero, encRun_succ, encRun_succ, encRun_zero]
      bb_steps
    · dsimp only [sweepFL]
      have h1 : ReachesPlus target
          (Cfg.headLeft F (encRun ((a + 3) :: Lt)) (encRun R))
          (rightCfg .ar (a :: Lt) (2 :: R)) := by
        dsimp only [rightCfg]
        rw [encRun_succ (a + 2), encRun_succ (a + 1), encRun_succ a,
          encRun_succ, encRun_succ, encRun_zero]
        bb_steps
      exact h1.trans (sweepRight_spec .ar (a :: Lt) (2 :: R))

/-! ## Acceleration Validity -/

private theorem init_reaches_start : ReachesStar target (init []) (encode start) := by
  refine (?_ : ReachesPlus target (init []) (encode start)).to_star
  dsimp only [start, encode]
  rw [encRun_succ, encRun_zero, encRun_nil]
  bb_steps

private theorem step_all (s : State) :
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone := by
  rcases s with ⟨_ | ⟨_ | a, Lt⟩, R⟩
  · dsimp only [next, encode]
    have h1 : ReachesPlus target
        (Cfg.headLeft E (encRun []) (encRun R))
        (Cfg.headLeft F (encRun []) (encRun (0 :: R))) := by
      rw [encRun_nil, encRun_zero]
      bb_steps
    exact h1.trans (sweepFL_spec [] (0 :: R))
  · dsimp only [next]
    refine ⟨encode (.E (0 :: Lt) R), ReachesStar.refl _ _, ?_⟩
    dsimp only [encode]
    rw [encRun_zero]
    bb_halt
  · dsimp only [next, encode]
    have h1 : ReachesPlus target
        (Cfg.headLeft E (encRun ((a + 1) :: Lt)) (encRun R))
        (Cfg.headLeft F (encRun (a :: Lt)) (encRun (0 :: R))) := by
      rw [encRun_succ, encRun_zero]
      bb_steps
    exact h1.trans (sweepFL_spec (a :: Lt) (0 :: R))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some s s' h := by
    have hs := step_all s
    rw [h] at hs
    exact hs
  step_none s h := by
    have hs := step_all s
    rw [h] at hs
    exact hs

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0LE_0RC0RA_1RD1RB_0LA0RB_1LFHHH_1LD1LF
