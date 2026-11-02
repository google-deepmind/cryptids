/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.BB6.Accelerations.M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---`
(https://wiki.bbchallenge.org/wiki/1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---, which redirects to the
wiki page of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`).

This machine is the transition table of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` restarted from
its state `D` and brought to tree normal form: reading its states `A`, `B`, `C`, `D`, `E`, `F` as
the states `D`, `E`, `C`, `F`, `B`, `A` of that machine and mirroring the tape left/right, the two
transition tables coincide, so both machines run the same closed pair-stack system. The proof below
transports the closed stack witness of
[`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](./M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean)
via `ClosedStackSystem.mirror`; only the blank-tape entry theorem `init_reaches_nontrivial` is
specific to this start state.

## Hardness

*Hardness class:* Wiki stack — trigger **as #85 (same table, started from its state `D`,
mirrored)**, growth as #85, shield as #85.

*Verdict (heuristic; community analysis, see the wiki page):* same dynamics as
`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85); this is the start state analysed by @-d on the
wiki (halting path of length 108, $\approx 235{,}000$ right-side words explored).

*Hazard:* as #85 (community estimate)

*Simulated horizon:* as #85

*Why it is hard:* the proof is the relabelling and left/right mirror of the #85 proof with its own
blank-tape entry (7 raw steps)

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH

open SixState Turing Stack
open M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LE---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- State bijection from #85 (`1RB---_...`) to #490 (`1RB0RE_...`). -/
def f : Fin 6 → Fin 6 := ![5, 4, 2, 0, 1, 3]

/-- Transition table isomorphism between #85 and #490 under state relabelling `f` and mirror. -/
theorem hM : ∀ (q : Fin 6) (a : Fin 2),
    target (f q) a =
      (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.target q a).map fun ⟨q', Stmt.write b d⟩ =>
        ⟨q'.map f, Stmt.write b (reflectDir d)⟩ := by
  intro q a
  fin_cases q <;> fin_cases a <;> rfl

/-- Transport the closed pair-stack system of #85 to `target` along `f` and tape reflection. -/
def closedStackSystem : ClosedStackSystem target :=
  M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.mirror f
    M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.encLeft_eq_encRight hM

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  refine ReachesPlus.head (by rfl) ?_
  simp only [Tape.move, Tape.write,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  simp only [multiStep_zero]
  try rfl))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

private theorem init_reaches_nontrivial :
    ReachesPlus target (init [])
      (closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)]) := by
  have htarget : closedStackSystem.evalStackCfg StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)] =
      ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) <{{A}}
        ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) := by
    rfl
  rw [htarget]
  execute 7

/-! ## Stack Reduction Witness -/

/-- `target` reduces to a closed 2nd-order digit-stack transition system. -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_closedSystem closedStackSystem StackMode.DR_n_n [(0, 0), (0, 0)] [(1, 0)]
    init_reaches_nontrivial (by decide) ⟨(1, 0), by decide, by decide⟩

end BusyBeaver.M_1RB0RE_1LC0RA_1LA1LD_1LC1LF_0LC0LB_1LEHHH
