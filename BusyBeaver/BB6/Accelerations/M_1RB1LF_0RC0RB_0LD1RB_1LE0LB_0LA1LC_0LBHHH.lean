/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`

Formal Collatz-like transducer acceleration (`IsValidAcceleration`) for the 6-state, 2-symbol
Busy Beaver holdout `1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---`.

Both half-tapes are represented as zero-run stacks `List ℕ` via `encRun`, where each entry `k`
encodes the block `0^k 1`:
$$D(L, R) := \mathrm{encRun}(L) <\!\mathrm{D}\, \mathrm{encRun}(R).$$
Starting from the blank tape (`init []`), the machine reaches `start = .D [1] []` after 3 raw
Turing machine steps. Halting (`F1 -> ---`) occurs only when the left zero-run stack begins with
`2 :: 0 :: _`.

## Accelerated Transition Rules

```text
encRun []        = 0^inf
encRun (k :: xs) = 0^k 1 ++ encRun xs

incRun []        = []
incRun (k :: xs) = (k + 1) :: xs

sweepB(L, [])            = D(incRun L, [])
sweepB(L, 0 :: Rt)       = sweepB(incRun L, Rt)
sweepB(L, 1 :: Rt)       = sweepB(0 :: incRun L, Rt)
sweepB(L, (d + 2) :: Rt) = D(incRun L, (d + 1) :: Rt)

D([], R)                -> sweepB([0], 1 :: R)
D([0], R)               -> sweepB([], incRun (incRun R))
D(0 :: 0 :: L'', R)     -> sweepB(L'', 0 :: incRun R)
D(0 :: (k+1) :: L'', R) -> sweepB(k :: L'', incRun (incRun R))
D([1], R)               -> D([], 1 :: 0 :: R)
D(1 :: 0 :: L'', R)     -> sweepB(0 :: L'', 0 :: 0 :: R)
D(1 :: (k+1) :: L'', R) -> D(k :: L'', 1 :: 0 :: R)
D([2], R)               -> sweepB([], 2 :: 1 :: R)
D(2 :: 0 :: _, _)       -> Halt
D(2 :: 1 :: L'', R)     -> sweepB(L'', 0 :: 1 :: 1 :: R)
D(2 :: (k+2) :: L'', R) -> sweepB(k :: L'', 2 :: 1 :: R)
D((k+3) :: L', R)       -> sweepB(0 :: k :: L', 1 :: R)

Start: D([1], []), reached after 3 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- Symbolic configuration state `D(L, R)` over zero-run stacks. -/
inductive State where
  | D (L R : List ℕ)
  deriving DecidableEq, Repr

/-- Rightward `B`-mode sweep across `encRun R`, returning to a `D`-mode configuration. -/
def sweepB : List ℕ → List ℕ → State
  | L, [] => .D (incRun L) []
  | L, 0 :: Rt => sweepB (incRun L) Rt
  | L, 1 :: Rt => sweepB (0 :: incRun L) Rt
  | L, (d + 2) :: Rt => .D (incRun L) ((d + 1) :: Rt)

/-- Initial accelerated state, reached after 3 raw Turing machine steps from `init []`. -/
def start : State := .D [1] []

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D L R => Cfg.headLeft SixState.D (encRun L) (encRun R)

/-- Accelerated transition function (`none` indicates halting). -/
def next : State → Option State
  | .D [] R => some (sweepB [0] (1 :: R))
  | .D [0] R => some (sweepB [] (incRun (incRun R)))
  | .D (0 :: 0 :: L'') R => some (sweepB L'' (0 :: incRun R))
  | .D (0 :: (k + 1) :: L'') R => some (sweepB (k :: L'') (incRun (incRun R)))
  | .D [1] R => some (.D [] (1 :: 0 :: R))
  | .D (1 :: 0 :: L'') R => some (sweepB (0 :: L'') (0 :: 0 :: R))
  | .D (1 :: (k + 1) :: L'') R => some (.D (k :: L'') (1 :: 0 :: R))
  | .D [2] R => some (sweepB [] (2 :: 1 :: R))
  | .D (2 :: 0 :: _) _ => none
  | .D (2 :: 1 :: L'') R => some (sweepB L'' (0 :: 1 :: 1 :: R))
  | .D (2 :: (k + 2) :: L'') R => some (sweepB (k :: L'') (2 :: 1 :: R))
  | .D ((k + 3) :: L') R => some (sweepB (0 :: k :: L') (1 :: R))

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

/-! ## Rightward `B`-Sweep Lemma -/

private theorem sweepB_spec (L R : List ℕ) :
    ReachesPlus target (Cfg.headRight B (encRun L) (encRun R)) (encode (sweepB L R)) := by
  induction R generalizing L with
  | nil =>
    dsimp only [sweepB, encode]
    rw [← zero_cons_encRun L, encRun_nil]
    bb_steps
  | cons d Rt ih =>
    rcases d with _ | _ | d
    · dsimp only [sweepB]
      have h1 : ReachesPlus target
          (Cfg.headRight B (encRun L) (encRun (0 :: Rt)))
          (Cfg.headRight B (encRun (incRun L)) (encRun Rt)) := by
        rw [encRun_zero, ← zero_cons_encRun L]
        bb_steps
      exact h1.trans (ih (incRun L))
    · dsimp only [sweepB]
      have h1 : ReachesPlus target
          (Cfg.headRight B (encRun L) (encRun (1 :: Rt)))
          (Cfg.headRight B (encRun (0 :: incRun L)) (encRun Rt)) := by
        rw [encRun_succ, encRun_zero, encRun_zero, ← zero_cons_encRun L]
        bb_steps
      exact h1.trans (ih (0 :: incRun L))
    · dsimp only [sweepB, encode]
      rw [encRun_succ (d + 1), encRun_succ d, ← zero_cons_encRun L]
      bb_steps

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
  rcases s with ⟨_ | ⟨_ | _ | _ | k, L'⟩, R⟩
  · dsimp only [next, encode]
    have h1 : ReachesPlus target
        (Cfg.headLeft D (encRun []) (encRun R))
        (Cfg.headRight B (encRun [0]) (encRun (1 :: R))) := by
      rw [encRun_nil, encRun_succ, encRun_zero, encRun_zero, encRun_nil]
      bb_steps
    exact h1.trans (sweepB_spec [0] (1 :: R))
  · rcases L' with _ | ⟨_ | k, L''⟩
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun [0]) (encRun R))
          (Cfg.headRight B (encRun []) (encRun (incRun (incRun R)))) := by
        rw [encRun_zero, encRun_nil, ← zero_cons_encRun (incRun R), ← zero_cons_encRun R]
        bb_steps
      exact h1.trans (sweepB_spec [] (incRun (incRun R)))
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun (0 :: 0 :: L'')) (encRun R))
          (Cfg.headRight B (encRun L'') (encRun (0 :: incRun R))) := by
        rw [encRun_zero, encRun_zero, encRun_zero, ← zero_cons_encRun R]
        bb_steps
      exact h1.trans (sweepB_spec L'' (0 :: incRun R))
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun (0 :: (k + 1) :: L'')) (encRun R))
          (Cfg.headRight B (encRun (k :: L'')) (encRun (incRun (incRun R)))) := by
        rw [encRun_zero, encRun_succ, ← zero_cons_encRun (incRun R), ← zero_cons_encRun R]
        bb_steps
      exact h1.trans (sweepB_spec (k :: L'') (incRun (incRun R)))
  · rcases L' with _ | ⟨_ | k, L''⟩
    · dsimp only [next, encode]
      rw [encRun_succ, encRun_zero, encRun_nil, encRun_succ, encRun_zero, encRun_zero]
      bb_steps
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun (1 :: 0 :: L'')) (encRun R))
          (Cfg.headRight B (encRun (0 :: L'')) (encRun (0 :: 0 :: R))) := by
        rw [encRun_succ, encRun_zero, encRun_zero, encRun_zero, encRun_zero]
        bb_steps
      exact h1.trans (sweepB_spec (0 :: L'') (0 :: 0 :: R))
    · dsimp only [next, encode]
      rw [encRun_succ, encRun_zero, encRun_succ, encRun_succ, encRun_zero, encRun_zero]
      bb_steps
  · rcases L' with _ | ⟨_ | _ | k, L''⟩
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun [2]) (encRun R))
          (Cfg.headRight B (encRun []) (encRun (2 :: 1 :: R))) := by
        rw [encRun_succ, encRun_succ, encRun_zero, encRun_nil, encRun_succ, encRun_succ,
          encRun_zero, encRun_succ, encRun_zero]
        bb_steps
      exact h1.trans (sweepB_spec [] (2 :: 1 :: R))
    · dsimp only [next, encode]
      rw [encRun_succ, encRun_succ, encRun_zero, encRun_zero]
      refine ⟨Cfg.headLeft F (ListBlank.cons 1 (encRun L''))
        (ListBlank.append [1, 0, 1] (encRun R)), ?_, by bb_halt⟩
      exact (by bb_steps : ReachesPlus target _ _).to_star
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun (2 :: 1 :: L'')) (encRun R))
          (Cfg.headRight B (encRun L'') (encRun (0 :: 1 :: 1 :: R))) := by
        rw [encRun_succ, encRun_succ, encRun_zero, encRun_succ, encRun_zero, encRun_zero,
          encRun_succ, encRun_zero, encRun_succ, encRun_zero]
        bb_steps
      exact h1.trans (sweepB_spec L'' (0 :: 1 :: 1 :: R))
    · dsimp only [next, encode]
      have h1 : ReachesPlus target
          (Cfg.headLeft D (encRun (2 :: (k + 2) :: L'')) (encRun R))
          (Cfg.headRight B (encRun (k :: L'')) (encRun (2 :: 1 :: R))) := by
        rw [encRun_succ, encRun_succ, encRun_zero, encRun_succ (k + 1), encRun_succ k,
          encRun_succ, encRun_succ, encRun_zero, encRun_succ, encRun_zero]
        bb_steps
      exact h1.trans (sweepB_spec (k :: L'') (2 :: 1 :: R))
  · dsimp only [next, encode]
    have h1 : ReachesPlus target
        (Cfg.headLeft D (encRun ((k + 3) :: L')) (encRun R))
        (Cfg.headRight B (encRun (0 :: k :: L')) (encRun (1 :: R))) := by
      rw [encRun_succ (k + 2), encRun_succ (k + 1), encRun_succ k, encRun_zero,
        encRun_succ, encRun_zero]
      bb_steps
    exact h1.trans (sweepB_spec (0 :: k :: L') (1 :: R))

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

end BusyBeaver.M_1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LBHHH
