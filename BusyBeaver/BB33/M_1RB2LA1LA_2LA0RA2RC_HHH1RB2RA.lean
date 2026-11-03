/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.BB33.WilyCoyote

/-!
# Busy Beaver Holdout `1RB2LA1LA_2LA0RA2RC_---1RB2RA` (Wily Coyote Twin, Holdout #532)

Formal `IsClosedStackPatternSet`, `HasStackedCollatzReduction`, and `IsValidAcceleration` proofs
for the 3-state, 3-symbol Busy Beaver holdout `1RB2LA1LA_2LA0RA2RC_---1RB2RA`
(**Wily Coyote Twin**, Holdout #532; see <https://wiki.bbchallenge.org/wiki/Wily_Coyote>).

Starting from the blank tape (`init []`), the trajectory reaches the left-bounce family
$$W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty
  \quad (w \in \{\mathtt{false}, \mathtt{true}\}^*, \quad
  \overline{\mathtt{false}} = 2, \; \overline{\mathtt{true}} = 1)$$
at $W([\mathtt{false}, \mathtt{false}]) = 0^\infty\,\mathrm{A}{>}\,0\,2\,2\,0^\infty$ in 3 raw
Turing machine steps. Because `(C, 1)` is always entered with `2` immediately to the left of the
tape head, `C1 -> 1RB` (`1` raw step) has the exact same net effect as `C1 -> 0LC -> C2 -> 2RA ->
A0 -> 1RB` (`3` raw steps on `1RB2LA1LA_2LA0RA2RC_---0LC2RA`), so both machines share the identical
accelerated transition system `(State, start, next)` (see `BusyBeaver/BB33/WilyCoyote.lean`).
-/

@[expose] public section

namespace BusyBeaver.M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA

open ThreeState Turing WilyCoyote

/-- The `(3, 3)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 3 3 :=
  load_rle_machine% "1RB2LA1LA_2LA0RA2RC_---1RB2RA"

/-- The `(3, 3)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 3) (Fin 3) :=
  machine.toBB

/-- Canonical left-bounce configuration family
$W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty$. -/
abbrev State := WilyCoyote.State

/-- Carry/pass modes of Racheline's left-to-right sweep transducer for Wily Coyote. -/
abbrev WilyMode := WilyCoyote.WilyMode

/-- Left-to-right pass transducer across a boolean cell word (`false` = symbol `2`,
`true` = symbol `1`). -/
abbrev wilyPass := WilyCoyote.wilyPass

/-- Initial accelerated state $W([\mathtt{false}, \mathtt{false}])$, reached from `init []` in 3
steps. -/
abbrev start : State := WilyCoyote.start

/-- Decode an accelerated `State` into its concrete Turing machine configuration. -/
abbrev encode : State → Cfg (Fin 3) (Fin 3) := WilyCoyote.encode

/-- One full sweep of the accelerated Wily Coyote transducer (`none` indicates halting). -/
abbrev next : State → Option State := WilyCoyote.next

/-- Stack pattern for $W(w) = 0^\infty\,\mathrm{A}{>}\,0\,\overline{w}\,0^\infty$. -/
abbrev pat_W : StackPattern (Fin 3) (Fin 3) := WilyCoyote.pat_W

/-- Full `StackPatternSet` for `1RB2LA1LA_2LA0RA2RC_---1RB2RA`. -/
abbrev ps : StackPatternSet (Fin 3) (Fin 3) := WilyCoyote.ps

private theorem stepSpec : StepSpec target := by
  prove_wily_step_spec

/-- `next` is a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next :=
  stepSpec.is_valid_acceleration

/-- `target` halts iff the accelerated transition function `next` halts from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-- `ps` is a closed stacked pattern set for `target`. -/
theorem is_closed_stack_pattern_set : IsClosedStackPatternSet target ps :=
  stepSpec.is_closed_stack_pattern_set

/-- `target` has a stacked Collatz-like reduction via `ps`. -/
theorem has_stacked_collatz_reduction : HasStackedCollatzReduction target :=
  ⟨ps, is_closed_stack_pattern_set⟩

end BusyBeaver.M_1RB2LA1LA_2LA0RA2RC_HHH1RB2RA
