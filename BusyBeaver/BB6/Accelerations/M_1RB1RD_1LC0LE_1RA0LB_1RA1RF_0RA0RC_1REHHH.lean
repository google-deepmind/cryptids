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
# Busy Beaver Holdout `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`
(https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---, which redirects to the
wiki page of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`).

This machine is the transition table of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` restarted from
its state `C` and brought to tree normal form: reading its states `A`, `B`, `C`, `D`, `E`, `F` as
the states `C`, `D`, `E`, `F`, `B`, `A` of that machine, the two transition tables coincide, so both
machines run the same closed pair-stack system. The proof below transports the closed stack witness
of [`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](./M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean)
via `ClosedStackSystem.relabel`; only the blank-tape entry theorem `init_reaches_nontrivial` is
specific to this start state.

## Hardness

*Hardness class:* Wiki stack — trigger **as #85 (same table, started from its state `C`)**, growth
as #85, shield as #85.

*Verdict (heuristic; community analysis, see the wiki page):* same dynamics as
`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85) (wiki: "when the TM starts on any starting state,
it exhibits the same probviously halting behaviour").

*Hazard:* as #85 (community estimate)

*Simulated horizon:* as #85

*Why it is hard:* the proof is the state relabelling of the #85 proof with its own blank-tape entry
(12 raw steps)

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH

open SixState Turing Stack
open M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-- State bijection from #85 (`1RB---_...`) to #285 (`1RB1RD_...`). -/
def f : Fin 6 → Fin 6 := ![5, 4, 0, 1, 2, 3]

/-- Transition table isomorphism between #85 and #285 under state relabelling `f`. -/
theorem hM : ∀ (q : Fin 6) (a : Fin 2),
    target (f q) a =
      (M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.target q a).map fun ⟨q', Stmt.write b d⟩ =>
        ⟨q'.map f, Stmt.write b d⟩ := by
  intro q a
  fin_cases q <;> fin_cases a <;> rfl

/-- Transport the closed pair-stack system of #85 to `target` along `f`. -/
def closedStackSystem : ClosedStackSystem target :=
  M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.closedStackSystem.relabel f hM

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
      (closedStackSystem.evalStackCfg StackMode.DR_n_n [(3, 0)] [(0, 0), (0, 0)]) := by
  have htarget : closedStackSystem.evalStackCfg StackMode.DR_n_n [(3, 0)] [(0, 0), (0, 0)] =
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) {{B}}>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default) := by
    rfl
  rw [htarget]
  execute 12

/-! ## Stack Reduction Witness -/

/-- `target` reduces to a closed 2nd-order digit-stack transition system. -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_closedSystem closedStackSystem StackMode.DR_n_n [(3, 0)] [(0, 0), (0, 0)]
    init_reaches_nontrivial (by decide) ⟨(3, 0), by decide, by decide⟩

end BusyBeaver.M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH
