# Busy Beaver Holdouts (`BusyBeaver/`)

This library contains formal Lean 4 specifications and kernel-verified behavioral proofs for Busy Beaver 6 (`BB(6)`) and Busy Beaver (3, 3) (`BB(3, 3)`) holdouts, connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](./Bridge.lean):

- **[`BusyBeaver/BB6/`](./BB6/README.md)** — 302 `BB(6)` (6-state, 2-symbol) Turing machines: 55 holdouts in `BB6/` (the [A6 nonhalting certificate](../artifacts/a6/README.md) and 54 holdouts with certified closed `TapePatternSet` invariants `IsClosedPatternSet`, `HasCollatzReduction` and Collatz-like accelerations `IsValidAcceleration`, including a self-contained, Baker-free 2-adic Laurent-determinant `IsNotHalt` proof for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`), plus 56 stacked, odometer, transducer, and cryptid holdouts (15 machines formalized under `HasStackReduction`, `HasOdometerReduction`, and `HasTransducerReduction`—12 `bbchallenge` Wiki machines and 3 Halving Tower holdouts—20 open acceleration problems under `IsValidAcceleration`, 13 of which additionally carry higher-level Poincaré/contraction accelerations `highLevelNext`, and 21 Hard holdout cryptid machines under `IsSegmentedCryptid`, `IsStackCryptid`, and `IsOdometerCryptid`) in **[`BusyBeaver/BB6/Accelerations/`](./BB6/Accelerations/README.md)**, together with machine-level halting equivalences ([`Equivalences.lean`](./BB6/Equivalences.lean)), hardness classification ([`Hardness.lean`](./BB6/Hardness.lean)), and formal hardness evidence ([`HardnessEvidence.lean`](./BB6/HardnessEvidence.lean)), alongside 191 resolved holdouts in **[`BusyBeaver/BB6/Halt/`](./BB6/Halt/)** (32 `IsHalt` proofs) and **[`BusyBeaver/BB6/NonHalt/`](./BB6/NonHalt/)** (159 `IsNotHalt` proofs) reproducing community and `busycoq` results.
- **[`BusyBeaver/BB33/`](./BB33/README.md)** — All 6 remaining unsolved `BB(3, 3)` (3-state, 3-symbol) holdout Turing machines (4 equivalence classes: *Bigfoot* (holdout #829), the *Wily Coyote* pair (holdouts #531 & #532), the holdout #758 / #153 pair (probvious champion), and holdout #397), with certified Collatz-like (`HasCollatzReduction`) or stacked Collatz-like (`HasStackedCollatzReduction`) reductions and exact halting equivalences (`IsValidAcceleration`).

## Cryptids, Collatz-like, and Stacked Collatz Reductions

Broadly speaking, [cryptids](https://wiki.bbchallenge.org/wiki/Cryptids) are Turing machines whose halting problem corresponds to a known open mathematical problem (such as the machines for Goldbach's conjecture, ZF consistency, and the Riemann Hypothesis in [`Cryptids/`](../Cryptids/README.md)). In the Busy Beaver community, however, the term is commonly used more broadly for holdout machines whose dynamics exhibit a **Collatz-like structure** (piecewise-affine or modular transitions on integer counters) or a **stacked Collatz structure** (sweep-by-sweep transducer rewrites over an unbounded word of blocks), rather than encoding the classical Collatz conjecture itself or a named open problem.

Accordingly, for these machines we look for and formalize **Collatz-like reductions** (`HasCollatzReduction` and `IsValidAcceleration`) and **stacked Collatz reductions** (`HasStackedCollatzReduction` and `IsValidAcceleration`). Some well-known holdouts, such as [`BB(6)` Antihydra](https://wiki.bbchallenge.org/wiki/Antihydra) and [`BB(3, 3)` Bigfoot](https://wiki.bbchallenge.org/wiki/Bigfoot), are widely considered genuinely hard and have attracted dedicated mathematical research. At the same time, other machines with Collatz-like reductions have subsequently been resolved—either through automated deciders or via number-theoretic methods such as Baker's theorem on linear forms in logarithms (e.g., [`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---)). It is therefore reasonable to expect that some of the machines in this directory will eventually be resolved as halting (`IsHalt`) or non-halting (`IsNotHalt`) over time, with or without the reductions provided here.

The original reductions and formal Lean 4 proofs in this library were produced by the Gemini-based agentic discovery pipeline introduced in [*At the Limits of Computability: Steps Towards Autonomous AI Discovery on the Busy Beaver Frontier*](https://arxiv.org/abs/2610.22603) (Dos Santos, Veeriah, Havrilla, Bolt, Zuzic, Singh, and Zahavy, 2026). Starting from raw blank-tape execution traces of unresolved holdouts, the system integrates automated pattern recognition, symbolic conjecturing of recurrent tape configurations (`TapePatternSet` and `StackPatternSet`) and accelerated transition rules, informal mathematical reasoning, and formal theorem proving in Lean 4 to synthesize and verify closed-set invariants (`IsClosedPatternSet`, `IsClosedStackPatternSet`) and multi-step accelerations (`IsValidAcceleration`).

The A6 nonhalting proof uses the reusable reflective RLE and affine-return engine in
[`WordRLE.lean`](./WordRLE.lean), [`AffRLE.lean`](./AffRLE.lean), and
[`ElabRLE.lean`](./ElabRLE.lean); its [proof guide](../artifacts/a6/README.md) records the
reflective architecture and verification procedure.

## Behavioral Predicates ([`Defs.lean`](./Defs.lean))

The definition surface is partitioned into modular submodules under [`BusyBeaver/Defs/`](./Defs/) and re-exported through the umbrella module [`BusyBeaver/Defs.lean`](./Defs.lean):

- **[`Defs/Core.lean`](./Defs/Core.lean)** — Post-Turing execution model (`Stmt`, `Machine`, `Cfg`), reachability relations (`step`, `init`, `multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus`), and foundational halting predicates (`IsHalt`, `IsNotHalt`, `IsDoesNotHalt`).
- **[`Defs/Patterns.lean`](./Defs/Patterns.lean)** — Regular-expression tape patterns (`TapeExpr`, `TapePattern`, `VarCond`), pattern set closure (`IsClosedPatternSet`, `HasCollatzReduction`), abstract acceleration halting (`CollatzHalts`, `IsValidAcceleration`), and rule-bounded cryptids (`IsCryptid`).
- **[`Defs/Stack.lean`](./Defs/Stack.lean)** — Stack-word tape patterns (`StackSeg`, `StackExpr`, `StackPattern`), stacked Collatz reductions (`IsClosedStackPatternSet`, `HasStackedCollatzReduction`), bounded half-tape views (`HalfTapeView`, `applyView`), and 2nd-order digit-stack reductions (`HasStackReduction`).
- **[`Defs/Odometer.lean`](./Defs/Odometer.lean)** — Mixed-radix odometer stack and bitstream systems (`OdomSide`, `evalOdomR`, `evalOdomL`, `HasOdometerReduction`).
- **[`Defs/Transducer.lean`](./Defs/Transducer.lean)** — Bidirectional word-stack transducers (`IsValidTransducerModes`, `kraftSum`, `iterTransducerMacro`, `HasTransducerReduction`).
- **[`Defs/WordRun.lean`](./Defs/WordRun.lean)** — Invariant-relative word-run stack systems with accumulator registers (`WordStackSpec`, `IsWordRunCryptid`).
- **[`Defs/Segmented.lean`](./Defs/Segmented.lean)** — Partitioned segmented half-tape schemas (`SegRegionKind`, `IsSegmentedCryptid`).

All proofs in `BusyBeaver/` target machine-checked behavioral predicates starting from the all-blank tape (`BusyBeaver.init []`):

| Predicate | Defining Module | Meaning |
| :--- | :--- | :--- |
| `IsHalt M` | `Defs/Core.lean` | `M` eventually reaches a halting configuration (`(step M cfg).isNone`) from `init []`. |
| `IsNotHalt M` (`IsDoesNotHalt M`) | `Defs/Core.lean` | Every configuration reachable from `init []` has a well-defined successor (`(step M cfg).isSome`). |
| `IsClosedPatternSet M ps` | `Defs/Patterns.lean` | **Level A (Counter)**: `M`'s blank-tape trajectory enters the explicit `TapePatternSet` `ps`, and every member configuration advances (`ReachesPlus`) either to another member of `ps` or to a halting configuration. |
| `HasCollatzReduction M` | `Defs/Patterns.lean` | `∃ ps, IsClosedPatternSet M ps`. |
| `IsCryptid M` | `Defs/Patterns.lean` | `M` admits an invariant certificate with at most 16 patterns and 32 rules over alphabet size `k + 2`. |
| `IsClosedStackPatternSet M ps` | `Defs/Stack.lean` | **Level A (Stacked)**: `ps` is well-formed (`IsWellFormedStackPatternSet ps`: non-empty, blank-free block vocabularies, and single-sided stack configuration with at most one `.word` segment), `M`'s blank-tape trajectory enters `ps`, and every member configuration advances (`ReachesPlus`) either to another member of `ps` or to a halting configuration. |
| `HasStackedCollatzReduction M` | `Defs/Stack.lean` | `∃ ps, IsClosedStackPatternSet M ps` (an existential summary paired in `BusyBeaverChallenge.lean` with a concrete `ps` and an explicit Level B finite-state transducer acceleration). |
| `HasStackReduction M` | `Defs/Stack.lean` | **Level A (Two-Sided Stack)**: `M`'s blank-tape trajectory enters a closed two-sided variable-length digit-stack system (`StackTuple`, `IsValidStackModes`) with bounded-prefix views, blank-tape multi-digit stack reachability, and an arbitrary-depth stack-frame transfer transition. |
| `HasOdometerReduction M` | `Defs/Odometer.lean` | **Level A (Odometer)**: `M`'s blank-tape trajectory enters a closed mixed-radix odometer stack + bit-stream system (`evalOdomR` / `evalOdomL`) with non-trivial odometer stack reachability, certified decrement, zero-capacity drain, reflection, and unconditional push/reflect/halt closure. |
| `HasTransducerReduction M` | `Defs/Transducer.lean` | **Level A (Transducer)**: `M`'s blank-tape trajectory enters a closed bidirectional macro-word transducer (`IsValidTransducerModes`, `iterTransducerMacro`) over strict-sub-Kraft block alphabets with a halting-verified exit gate and unbounded sweeps in both directions. |
| `IsWordRunCryptid M` | `Defs/WordRun.lean` | `M`'s blank-tape trajectory enters a closed invariant-relative word-run stack system with bottom accumulator registers. |
| `IsSegmentedCryptid M` | `Defs/Segmented.lean` | `M`'s blank-tape trajectory enters a closed segmented schema over partitioned half-tapes with register, word-run, finite-word, and gadget regions. |
| `IsValidAcceleration M start encode next` | `Defs/Patterns.lean` | **Level B**: `encode : S → Cfg Γ Λ` and `next : S → Option S` form a certified acceleration of `M` from `start : S` (`init []` reaches `encode start`, `next s = some s'` implies `ReachesPlus M (encode s) (encode s')`, and `next s = none` implies halting from `encode s`), yielding `IsHalt M ↔ CollatzHalts next start`. |

## Foundational Lemmas ([`Basic.lean`](./Basic.lean))

[`BusyBeaver/Basic.lean`](./Basic.lean) provides clean-room multi-step and reachability lemmas (`multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus` with `Trans` instances), closed-invariant non-halting theorems (`NeverHaltsFrom.of_reachesPlus_invariant`, `IsNotHalt.of_reachesPlus_invariant`), certified acceleration halting equivalence, higher-level Collatz composition, and pattern-set closure bridges (`IsValidAcceleration.isHalt_iff`, `IsValidAcceleration.collatzHalts_iff`, `IsValidAcceleration.of_step`, `IsValidAcceleration.of_collatz`, `IsValidAcceleration.isClosedPatternSet`, `IsValidAcceleration.isClosedStackPatternSet`), finite block repetition (`l ^ n`) and `ListBlank` identities, standard 6-state (`BusyBeaver.SixState.A..F`) and 3-state (`BusyBeaver.ThreeState.A..C`) labels, directed-head (`Cfg.headRight` / `Cfg.headLeft`) step transitions, scoped directed-head and reachability notations (`l {{q}}> r`, `l <{{q}} r`, `s <+ l`, `l +> s`, `c₁ [M]⊢⁺ c₂`, ...), and concrete execution/halting tactics (`bb_steps`, `bb_halt`).

## Certificate Checkers ([`Cert.lean`](./Cert.lean), [`WordRLE.lean`](./WordRLE.lean), [`AffRLE.lean`](./AffRLE.lean), [`ElabRLE.lean`](./ElabRLE.lean))

- [`BusyBeaver/Cert.lean`](./Cert.lean) provides a small verified certificate checker (symbolic configurations over block-repetition variables, validated rewrite rules, and a `Bool`-valued proof-script interpreter whose success is sound for `ReachesStar` / `ReachesPlus` and hub-pattern membership). It is used by the machines whose closure proofs are produced as certificates (e.g. `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` and `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`).
- [`BusyBeaver/WordRLE.lean`](./WordRLE.lean), [`BusyBeaver/AffRLE.lean`](./AffRLE.lean), and [`BusyBeaver/ElabRLE.lean`](./ElabRLE.lean) provide a machine-polymorphic **proof-by-reflection and elaboration-time certificate synthesis** framework directly over `BusyBeaver.Cfg Γ Λ` (`ListBlank` half-tapes): strict call-by-value `withNat` accumulators, binary `NatTrie` exit tables, concrete RLE replay (`EntryReaches`), affine-exponent symbolic RLE + countdown-cycle replay (`AffReplayReaches`, `verifyReturnCert_sound`), and pure-Lean elaboration-time certificate discovery (`discoverReturnCert`) and sliced `mkAuxTheorem` kernel drivers (`proveEntryPhase`, `proveCheckAll`, `proveAffReplay`).

## Machine Loader and Bridge ([`Bridge.lean`](./Bridge.lean))

Machines can be defined using either the `.txt` transition-table loader `load_machine_rows%` from [`Cryptids/Machines.lean`](../Cryptids/Machines.lean) or the elaboration-time `bbchallenge.org` RLE string parsers `load_rle_machine%` and `load_rle_rows%`:

```lean
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA"

abbrev target : BusyBeaver.Machine (Fin 2) (Fin 6) :=
  machine.toBB
```

The canonical embedding `ConjectureMachines.Machine.toBB` maps any `ConjectureMachines.Machine states symbols` to `BusyBeaver.Machine (Fin symbols) (Fin states)`, with certified halting equivalence:

```lean
theorem isHalt_toBB_iff_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsHalt M.toBB ↔ ConjectureMachines.Halts M

theorem isNotHalt_toBB_iff_not_halts (M : ConjectureMachines.Machine states symbols) :
    BusyBeaver.IsNotHalt M.toBB ↔ ¬ ConjectureMachines.Halts M
```

## Formalized Machine Catalogs

- **[`BB(6)` Holdouts (`BusyBeaver/BB6/`)](./BB6/README.md)** — 54 holdouts (the [A6 nonhalting certificate](../artifacts/a6/README.md) and 53 closed-pattern 6-state 2-symbol holdouts; 312 theorems), **[`BB(6)` Accelerations (`BusyBeaver/BB6/Accelerations/`)](./BB6/Accelerations/README.md)** — 35 stacked, odometer, and transducer holdouts (95 theorems: 15 structural reductions and 20 open acceleration problems, including 13 higher-level accelerations), **[`Equivalences.lean`](./BB6/Equivalences.lean)** (1 halting equivalence theorem), and **[`HardnessEvidence.lean`](./BB6/HardnessEvidence.lean)** (74 live-hazard witness and halting residue-class theorems across 26 `BB(6)` holdouts).
- **[`BB(3, 3)` Holdouts (`BusyBeaver/BB33/`)](./BB33/README.md)** — 6 3-state 3-symbol holdouts (24 theorems).

## Building and Verifying

Build the `BusyBeaver` and `BusyBeaverChallenge` targets and audit with [`leanprover/comparator`](../comparator/README.md):

```bash
lake exe cache get
lake build BusyBeaver BusyBeaverChallenge
lake comparator --config comparator/busy_beaver.json
```

## Acknowledgements

We thank the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project for the Busy Beaver Post-Turing machine model (`BusyBeaver.Machine`), the Busy Beaver Challenge community (including Shawn Ligocki, `@savask`, Racheline, `@LegionMammal978`, and `@dyuan01` for their `BB(3, 3)` analyses), and `int-y1` (`BusyLean`) for pioneering Lean 4 Busy Beaver holdout formalizations and inspiring the directed-head configuration style (`Cfg.headRight` / `Cfg.headLeft`).
