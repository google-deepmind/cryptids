# Riemann95 proof guide

The public result is in [`../../Riemann95.lean`](../../Riemann95.lean): the literal
95-state machine halts from the blank tape exactly when `Riemann104.candidate`
does. [`../../Semantics/Riemann95.lean`](../../Semantics/Riemann95.lean) composes
that result with the existing mathematical semantics.

The construction retains the stage counter in `x` after `FOLD` and permutes the
physical register banks. This changes the register program and its tape
implementation, so the proof establishes both program correctness and physical
execution rather than a quotient of the 104-state transition table.

Read the layers in this order:

| Layer | Entry points | Purpose |
| --- | --- | --- |
| Literal machine | [`../../Riemann95Definition.lean`](../../Riemann95Definition.lean) | Defines all 190 transition cells and the initial root configuration. |
| Blank initialization | [`BootFast95.lean`](BootFast95.lean), [`BootEndpoint95.lean`](BootEndpoint95.lean) | Checks all 3,634 steps and identifies the entire resulting tape. |
| Reference program | [`ReferenceLogical95.lean`](ReferenceLogical95.lean), [`ReferenceLogicalSemantics95.lean`](ReferenceLogicalSemantics95.lean), [`ReferencePermutation95.lean`](ReferencePermutation95.lean), [`ReferenceBridge95.lean`](ReferenceBridge95.lean) | Relates the reordered program and register permutation to the original 104-state semantics, including the stopped pre-width computation. |
| Decoder and tape operations | [`Parser95.lean`](Parser95.lean), [`Auxiliary95Contracts.lean`](Auxiliary95Contracts.lean), [`ArithmeticFrame95.lean`](ArithmeticFrame95.lean) | Proves recursive control decoding, arithmetic operations, and preservation of surrounding tape. |
| Physical execution | [`PhysicalTrace95.lean`](PhysicalTrace95.lean), [`PrecreditTrace95.lean`](PrecreditTrace95.lean), [`WidthLift95.lean`](WidthLift95.lean) | Lifts program steps to the actual machine and handles growing padding and width changes. |
| Complete stages and halting | [`Stage95.lean`](Stage95.lean), [`Cofinality95.lean`](Cofinality95.lean), [`Witness95.lean`](Witness95.lean) | Proves stage-zero safety and cofinal positive stages, then characterizes halting by the original counterexample predicate. |

Shared reference facts live in [`../Riemann/`](../Riemann/).
`ControlWords`, `ControlSoundness`, and `WordGuard` certify the reference control
invariants; `FiniteStage` and `ReferenceStageRange` connect safe finite starting
stages to the original blank run. These facts do not depend on another reduced
machine.

All new proof modules use the pinned toolchain and existing Lean limits. The
three public results are checked against the independent table specification in
`Riemann95Challenge.lean` by `comparator/riemann_95.json` and `comparator/all.json`.
