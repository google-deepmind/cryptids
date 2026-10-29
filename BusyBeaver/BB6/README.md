# Busy Beaver 6 Holdouts (`BusyBeaver/BB6/`)

This directory contains formal Lean 4 specifications and kernel-verified Collatz-like reductions for 53 Busy Beaver 6 (`BB(6)`, 6-state 2-symbol) holdout Turing machines, together with 29 stacked, odometer, and transducer holdouts (9 `bbchallenge` Wiki machines formalized under `HasStackReduction`, `HasOdometerReduction`, and `HasTransducerReduction`, plus 20 open acceleration problems under `IsValidAcceleration`, 13 with higher-level accelerations) in **[`BusyBeaver/BB6/Accelerations/`](./Accelerations/README.md)** (82 `BB(6)` holdouts total). Each machine module in `BusyBeaver/BB6/` below exposes both **Level A** (`ps`, `is_closed_pattern_set`, `has_collatz_reduction`) and **Level B** (`State`, `start`, `encode`, `next`, `is_valid_acceleration`, `isHalt_iff_acceleration`), and 33 modules (all 20 novel discovery modules together with 13 multi-family or multi-counter wiki/busycoq holdouts) additionally expose a higher-level Collatz-like acceleration (`HighLevelState`, `highLevelStart`, `highLevelEncode`, `highLevelNext`, `is_valid_highLevel_acceleration`, `isHalt_iff_highLevel_acceleration`, `acceleration_iff_highLevel_acceleration`); see [`BusyBeaver/README.md`](../README.md) for definitions of the behavioral predicates and [`BusyBeaver/BB6/Accelerations/README.md`](./Accelerations/README.md) for the stacked, odometer, and transducer formalizations and open problem statements.

> **Hardness.** Why the hardest of these holdouts are hard (halting trigger, growth regime, shields, heuristic hazards, and the calibration case `#72` that the community proved halting) is recorded in [`Hardness.lean`](./Hardness.lean) (rendered on the docs site as `BusyBeaver.BB6.Hardness`); each machine in that core also carries a `## Hardness` section in its module docstring.

## Formalized `BB(6)` Machines

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Properties | Wiki / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB) | [`M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean`](./M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean) |
| `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA) | [`M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA.lean`](./M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA.lean) |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA) | [`M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean`](./M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean) |
| `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE) | [`M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE.lean`](./M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE.lean) |
| `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA) (BMO base-3) | [`M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.lean`](./M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.lean) |
| `1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE) (BMO5) | [`M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.lean`](./M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.lean) |
| `1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [busycoq `CubicCapLoop_v2.v` (`TM1`)](https://github.com/ccz181078/busycoq/blob/BB6/verify/CubicCapLoop_v2.v) (**resolved non-halting**) | [`M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE.lean`](./M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE.lean) |
| `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE) | [`M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean`](./M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean) |
| `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---) | [`M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean`](./M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean) |
| `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean) |
| `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | equivalent to `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` (same orbit after two macro-steps; busycoq [`Eqv_RegularPairs.v`](https://github.com/ccz181078/busycoq/blob/BB6/verify/Eqv_RegularPairs.v)) | [`M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean) |
| `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean`](./M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean) |
| `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean`](./M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean) |
| `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`](./M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean) |
| `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](./M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) |
| `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB) | [`M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean`](./M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean) |
| `1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC) (*Space Needle* family) | [`M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC.lean`](./M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC.lean) |
| `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean`](./M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean) |
| `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA) (*Lucy's Moonlight*) | [`M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA.lean`](./M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA.lean) |
| `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean`](./M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean) |
| `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB) | [`M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB.lean`](./M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB.lean) |
| `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB) (Parity-Collatz) | [`M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB.lean`](./M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB.lean) |
| `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE) (*The Sheep Machine*) | [`M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean`](./M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean) |
| `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD) (*Space Needle* / BMO6) | [`M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean`](./M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean) |
| `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean`](./M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean) |
| `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---) (*Pomme* / Baker machine; **resolved non-halting**) | [`M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH.lean`](./M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH.lean) |
| `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) | [`M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`](./M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean) |
| `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE) (redirects to BMO5) | [`M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.lean`](./M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.lean) |
| `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean`](./M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean) |
| `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean`](./M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean) |
| `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC) | [`M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC.lean`](./M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC.lean) |
| `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`Cryptids`)](https://wiki.bbchallenge.org/wiki/Cryptids) | [`M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean`](./M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean) |
| `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC) (TMBR Aug 2025) | [`M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean`](./M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean) |
| `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean`](./M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean) |
| `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean`](./M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean) |
| `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean`](./M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean) |
| `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean`](./M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean) |
| `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`Antihydra`)](https://wiki.bbchallenge.org/wiki/Antihydra) (*Antihydra*) | [`M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`](./M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean) |
| `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC) (*Counter6*) | [`M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean`](./M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean) |
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean`](./M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean) |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean`](./M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean) |
| `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA) | [`M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA.lean`](./M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA.lean) |
| `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean`](./M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean`](./M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean`](./M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.lean`](./M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.lean) |
| `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE) (BMO1) | [`M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE.lean`](./M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE.lean) |
| `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE) | [`M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean`](./M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean) |
| `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF) (*HydraShift6*) | [`M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF.lean`](./M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF.lean) |
| `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE) | [`M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE.lean`](./M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE.lean) |
| `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD) | [`M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean`](./M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean) |
| `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean`](./M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean) |
| `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean`](./M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean) |

## High-Level Acceleration Equations

### [`1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`](./M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean)

Contracting all five $\bmod\ 3$ sweeps (`S0p`, `T1`, `T11`, `T3`, `T10`, `T0`) and eliminating `S0z`, `Ea`, and `Ec` reduces the 12-constructor `State` system to a closed-form map (with zero recursive helpers) over $S(b, c) := S_{0+}(0, b, c)$, $T(m) := T_1(0, m)$, and the three non-halting self-loops $T_n(j)$, $E_b(k, t)$, and $E_d(k, t)$. Starting from $T(1)$, the machine follows:

$$
\begin{aligned}
  T_{\mathrm{HL}}(S(b, c)) &= \begin{cases}
    S(4\lfloor b/3 \rfloor + 1,\ c + 4) & \text{if } b \equiv 0 \pmod{3}, \\
    S(4\lfloor b/3 \rfloor + 5,\ c + 6) & \text{if } b \equiv 1 \pmod{3}, \\
    T(4\lfloor b/3 \rfloor + 7) & \text{if } b \equiv 2 \pmod{3} \text{ and } c = 0, \\
    S(4\lfloor b/3 \rfloor + 8,\ c - 1) & \text{if } b \equiv 2 \pmod{3} \text{ and } c \ge 1,
  \end{cases} \\
  T_{\mathrm{HL}}(T_n(j)) &= T_n(j + 2), \quad T_{\mathrm{HL}}(E_b(k, t)) = E_b(k + 1, t), \quad T_{\mathrm{HL}}(E_d(k, t)) = E_d(k + 1, t),
\end{aligned}
$$

while from $T(m)$, writing $j_0 = 2\lfloor m/3 \rfloor$, $m_1 = 2j_0 + 7$, $j_1 = 2\lfloor m_1/3 \rfloor$, $m_2 = 2j_1 + 7$, $j_2 = 2\lfloor m_2/3 \rfloor$, $m_3 = 2j_2 + 7$, $j_3 = 2\lfloor m_3/3 \rfloor$, $m_4 = 2j_3 + 6$, and $j_4 = 2\lfloor m_4/3 \rfloor$:

$$
T_{\mathrm{HL}}(T(m)) = \begin{cases}
  T_n(0) & \text{if } m \equiv 0 \pmod{3}, \\
  S(2j_0 + 5,\ 3) & \text{if } m \equiv 2 \pmod{3}, \\
  T(2j_1 + 6) & \text{if } m \equiv 1 \text{ and } m_1 \equiv 0 \pmod{3}, \\
  E_b(0,\ 2j_1 + 1) & \text{if } m \equiv 1 \text{ and } m_1 \equiv 2 \pmod{3}, \\
  T(2j_2 + 8) & \text{if } m \equiv 1,\ m_1 \equiv 1,\text{ and } m_2 \equiv 0 \pmod{3}, \\
  E_d(0,\ 2j_2 + 1) & \text{if } m \equiv 1,\ m_1 \equiv 1,\text{ and } m_2 \equiv 2 \pmod{3}, \\
  \text{Halt} & \text{if } m \equiv 1,\ m_1 \equiv 1,\ m_2 \equiv 1,\text{ and } (m_3 \not\equiv 0 \text{ or } m_4 \equiv 1 \pmod{3}), \\
  T(2j_4 + 5) & \text{if } m \equiv 1,\ m_1 \equiv 1,\ m_2 \equiv 1,\ m_3 \equiv 0,\text{ and } m_4 \equiv 0 \pmod{3}, \\
  T(2j_4 + 7) & \text{if } m \equiv 1,\ m_1 \equiv 1,\ m_2 \equiv 1,\ m_3 \equiv 0,\text{ and } m_4 \equiv 2 \pmod{3}.
\end{cases}
$$

This transition map is identical to that of [`1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`](./M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean), which starts from $S(1, 3)$.

### [`1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA`](./M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean)

Restricting $E(a, k, c) := 0^\infty \ 1^a \ \mathrm{A}{>} \ 0 \ (11)^k \ 0 \ 1^c \ 0^\infty$ to the canonical return section $a \in \lbrace 3, 4 \rbrace$ (`E_p(k, c) := E(3 + p, k, c)` for $p \in \lbrace 0, 1 \rbrace$) and composing through transient accumulation steps yields a closed-form 2-counter + 1-bit map $T$ (with zero helper functions), starting from $E_0(0, 2)$ (encoded as `.E false 0 2`, reached after 23 steps):

$$
T(E_p(k, c)) = \begin{cases}
  E_{1-p}(3\lfloor k/2 \rfloor + 2,\ c) & \text{if } c \text{ is odd and } k \text{ is even}, \\
  \text{Halt} & \text{if } c = 1 \text{ and } k \text{ is odd}, \\
  E_0(0,\ 6\lfloor k/2 \rfloor + 10 + p) & \text{if } c = 3 \text{ and } k \text{ is odd}, \\
  E_p(3\lfloor k/2 \rfloor + 5 + p,\ c - 5) & \text{if } c \ge 5 \text{ is odd and } k \text{ is odd}, \\
  E_0(0,\ 6k + 5 + p) & \text{if } c = 2k, \\
  E_0(0,\ 6k + 2 + p) & \text{if } c \text{ is even and } 2k = c + 2, \\
  E_{1-p}(3(c/2) + 3,\ 2k - c - 3) & \text{if } c \text{ is even and } 2k \ge c + 4, \\
  E_{1-p}(3,\ c - 2) & \text{if } c \ge 2 \text{ is even and } k = 0, \\
  E_p(3k + 1 + p,\ c - 2k - 1) & \text{if } c \text{ is even and } 2 \le 2k \le c - 2.
\end{cases}
$$

### [`1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`](./M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE.lean)

Eliminating $(a, f)$ from the 4-counter configuration $C(a, f, g, d) := 0^\infty \ 1^{a+1} \ \mathrm{C}{>} \ 00 \ 1^{f+4} \ (01)^g \ 1^3 \ (01111)^d \ 011 \ 0^\infty$ reduces the dynamics to two counters $(g, d)$ over the three entry families $C_0(g, d) := C(0, 0, g, d)$, $C_2(g, d) := C(2, 0, g, d)$, and $C_5(g, d) := C(5, 0, g, d)$. Starting from $C_2(0, 0)$, the machine follows:

$$
T(C_0(g, d)) = G(0, 0, g, d), \quad T(C_2(g, d)) = G(0, 3, g, d), \quad T(C_5(g, d)) = G(1, 6, g, d),
$$

where the $g$-scan $G(r, f, g, d)$ (`scanG`, for $r \in \lbrace 0, 1 \rbrace$) is defined recursively on $g$ (with $s = f + 3 + r$):

$$
G(r, f, g, d) = \begin{cases}
  C_2(\lfloor f/2 \rfloor + 2,\ d) & \text{if } g = 0,\ r = 0,\text{ and } f \text{ is even}, \\
  C_5(\lfloor f/2 \rfloor + 1,\ d) & \text{if } g = 0,\ r = 0,\text{ and } f \text{ is odd}, \\
  C_0(\lfloor f/2 \rfloor + 3,\ d) & \text{if } g = 0,\ r = 1,\text{ and } f \text{ is even}, \\
  \text{Halt} & \text{if } (g = 0,\ r = 1,\ f \text{ odd}) \text{ or } (g = 1,\ r = 1,\ f \text{ even}), \\
  C_2(0,\ d + 2) & \text{if } g = 1,\ r = 0,\text{ and } f = 0, \\
  C_5(\lfloor f/2 \rfloor - 1,\ d + 1) & \text{if } g = 1,\ r = 0,\text{ and } f \ge 2 \text{ is even}, \\
  C_2(\lfloor f/2 \rfloor + 1,\ d + 1) & \text{if } g = 1,\ r = 0,\text{ and } f \text{ is odd}, \\
  C_0(\lfloor f/2 \rfloor + 2,\ d + 1) & \text{if } g = 1,\ r = 1,\text{ and } f \text{ is odd}, \\
  G(s \bmod 2,\ 3\lfloor s/2 \rfloor + 3,\ g - 2,\ d) & \text{if } g \ge 2.
\end{cases}
$$

### [`1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE`](./M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE.lean)

Eliminating `H3`, `H2_even`, `H2_odd0`, and `H1_even` reduces the 5-constructor `CubicCapLoop_v2` system to a single-family 2-counter map on $H(a, g) := 0^\infty \ (01)^a \ 1^{g+1} \ \mathrm{A}{>} \ 0^\infty$, starting from $H(0, 3)$:

$$
T(H(a, g)) = \begin{cases}
  D(0, 1, g) & \text{if } a = 0, \\
  D(0, 1, g + 1) & \text{if } a = 1, \\
  D(2, 0, g + 1) & \text{if } a = 2, \\
  D(a', k' - 1, g + 1) & \text{if } a \ge 3,
\end{cases}
$$

where for $a_0 = a - 1 \ge 2$, $S(j) = 2^{j+1} - j - 1$, and $S(j) \le a_0 < S(j + 1)$, we set $(a', k') = (2^{j+1}, 1)$ if $a_0 = S(j)$ and $(a', k') = (S(j + 1) - 1 - a_0,\ a_0 + j + 2 - a')$ otherwise, and `drainEven` ($D(a, k, h)$) is defined recursively on $h$:

$$
D(a, k, h) = \begin{cases}
  \text{Halt} & \text{if } h \le 1 \text{ and } a = 0, \\
  H(a - 1,\ 2k + 3 + 2h) & \text{if } h \le 1 \text{ and } a \ge 1, \\
  D(k + 2,\ 0,\ h - 2) & \text{if } h \ge 2 \text{ and } a = 0, \\
  D(a - 1,\ k + 2,\ h - 2) & \text{if } h \ge 2 \text{ and } a \ge 1.
\end{cases}
$$

### [`1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---`](./M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean)

Contracting all five $\bmod\ 3$ sweeps reduces the 12-constructor `State` system to the exact same closed-form transition map $T_{\mathrm{HL}}$ over $\lbrace S(b, c),\ T(m),\ T_n(j),\ E_b(k, t),\ E_d(k, t) \rbrace$ (with zero recursive helpers) as [`1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB`](./M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean), starting from $S(1, 3)$.

### [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean)

Restricting $D(a, b, d) := 0^\infty \ \mathrm{D}{>} \ (10)^{a+1} \ (110)^b \ 0 \ 1^d \ 0^\infty$ to the $b = 0$ Poincaré section $D(a, d) := D(a, 0, d)$ (draining $b \ge 1$ via $B$, since each base-3 evaluation $A$ sends $b \mapsto b' \le \lfloor (b - 1)/3 \rfloor < b$) gives a 2-counter map $T$ starting from $D(0, 7)$ (reached after 66 steps):

$$
T(D(a, d)) = \begin{cases}
  B(d + 1,\ 2,\ 2) & \text{if } a = 0 \text{ and } d \text{ is odd}, \\
  D(d,\ 7) & \text{if } a = 0 \text{ and } d \text{ is even}, \\
  B(a - d - 5,\ d + 3,\ 5) & \text{if } a \ge d + 5 \text{ and } d \text{ is odd}, \\
  B(a - d - 2,\ d + 2,\ 2) & \text{if } a \ge d + 3 \text{ and } d \text{ is even}, \\
  \text{Halt} & \text{otherwise, if } a \text{ is odd}, \\
  B(0,\ a,\ 2) & \text{otherwise, if } a = d + 2, \\
  B(d + 4 - a,\ a - 1,\ 3) & \text{otherwise, if } d \text{ is odd}, \\
  B(A(d + 1 - a,\ a,\ 2a + 5)) & \text{otherwise (} 2 \le a \le d \text{ both even),}
\end{cases}
$$

where $A(a, 3j + r, m)$ ($r \in \lbrace 0, 1, 2 \rbrace$) and $B(a, b, d)$ (`evalA` and `drainB`) are defined recursively on $a$ and $b$:

$$
A(a, 3j + r, m) = \begin{cases}
  (a + 1, j, m) & \text{if } r = 2, \\
  \text{Halt} & \text{if } r = 0 \text{ and } a = 0, \\
  (a - 1, j, m + 2) & \text{if } r = 0 \text{ and } a \ge 1, \\
  (0, j, m) & \text{if } r = 1 \text{ and } a = 0, \\
  A(a - 1, j, m + 2j + 3) & \text{if } r = 1 \text{ and } a \ge 1,
\end{cases}
\qquad
B(a, b, d) = \begin{cases}
  D(a, d) & \text{if } b = 0, \\
  B(A(a, b - 1, d + 2b + 3)) & \text{if } b \ge 1.
\end{cases}
$$

This 2-counter system is identical to that of [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean), proving that the two machines have identical halting behavior.

### [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean)

Restricting $D(a, b, d) := 0^\infty \ \mathrm{D}{>} \ (10)^{a+1} \ (110)^b \ 0 \ 1^d \ 0^\infty$ to the $b = 0$ Poincaré section $D(a, d) := D(a, 0, d)$ gives the exact same 2-counter map $T$ (with initial state $D(0, 7)$, reached after 68 steps, and helpers $A$ and $B$) as [`1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`](./M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean).

### [`1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`](./M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean)

We define the configuration for $b, c \ge 0$:

$$
A(b, c) := 0^\infty \ 1^b \ \mathrm{F}{>} \ 00 \ 1^c \ 0^\infty.
$$

Starting from $A(5, 2)$ (reached after 33 steps from the blank tape), the machine follows the map $T$, where $h = \lfloor c/2 \rfloor$:

$$
T(A(b, c)) = \begin{cases}
  A(2c+4, 3) & \text{if } b = 0, \\
  A(3, 3) & \text{if } b = 2 \text{ and } c = 0, \\
  A(5, c-1) & \text{if } b = 2 \text{ and } c \ge 1, \\
  A(b-2h-4, 2c+5) & \text{if } b \ge 2h+5, \\
  A(2c+6, 3) & \text{if } b \text{ is odd and } b \le 2h+3, \\
  F(b-3, 2, 0, c-b+1) & \text{if } b \ge 4 \text{ is even and } b \le 2h, \\
  F(b-4+(c \bmod 2), 2, 0, 0) & \text{if } b \ge 4 \text{ is even and } b = 2h+2, \\
  \text{Halt} & \text{if } b \ge 4 \text{ is even and } b = 2h+4,
\end{cases}
$$

where $F(m, p, n, c)$ (`evalOdd`) is defined recursively on $m$:

$$
F(m, p, n, c) = \begin{cases}
  A(4n+c+7, 3) & \text{if } m = 0 \text{ and } p \le n+1, \\
  A(2(p-n-2)+1, 4n+c+6) & \text{if } m = 0 \text{ and } p \ge n+2, \\
  A(4n+9, c) & \text{if } m = 1 \text{ and } p \le n+1, \\
  F(0, p-n-2, 2n+3, c) & \text{if } m = 1 \text{ and } p \ge n+2, \\
  F(m-2, 2n+4, 0, c) & \text{if } m \ge 2 \text{ and } p \le n+1, \\
  F(m-1, p-n-2, 2n+3, c) & \text{if } m \ge 2 \text{ and } p \ge n+2.
\end{cases}
$$

This machine shares the exact same transition map $T$ and helper $F$ with [`1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`](./M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean), which starts from $A(4, 3)$.

### [`1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA`](./M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean)

We define the configuration for $a \ge 0$, $b \ge 1$:

$$
C(a, b) := 0^\infty \ \mathrm{E}{>} \ (10)^a \ 1^b \ 0^\infty.
$$

Starting from $C(0, 3)$ (encoded as `.C 0 2`, reached after 7 steps from the blank tape), the machine follows the map $T$:

$$
T(C(a, b)) = \begin{cases}
  C(2a+2, b-2a-2) & \text{if } b > 2a+2, \\
  C(2, 2a+2) & \text{if } b = 1, \\
  \text{Halt} & \text{if } b = 2, \\
  C(\lfloor(6a+2k+2)/4\rfloor, (6a+2k+2) \bmod 4 + 1)
    & \text{if } a \ge 1,\ b = 2k,\ 2 \le k \le a+1, \\
  C(\lfloor(6a+2k+6)/4\rfloor, (6a+2k+6) \bmod 4 + 1)
    & \text{if } a \ge 1,\ b = 2k+1,\ 1 \le k \le a.
\end{cases}
$$

### [`1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA`](./M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean)

We define the configuration for $u, w \ge 0$:

$$
J(u, w) := 0^\infty \ 1^5 \ (10)^u \ 1 \ \mathrm{A}{>} \ 1^{w+2} \ 01 \ 0^\infty.
$$

Starting from $J(0, 0)$ (reached after 35 steps from the blank tape), with $m = \lfloor w/2 \rfloor$ and $d = u - m$, the machine follows the map $T$:

$$
T(J(u, w)) = \begin{cases}
  J(2u+3, w-2u-3) & \text{if } w \ge 2u+3, \\
  J(0, 4u+18) & \text{if } w = 2u+2, \\
  J(11, 4u+2) & \text{if } w = 2u+1, \\
  J(0, 4u+12) & \text{if } w = 2u, \\
  J(0, 2w+12) & \text{if } w = 2m < 2u \text{ and } d = 1, \\
  J(11, 2u+w-2) & \text{if } w = 2m < 2u \text{ and } d \ge 2 \text{ is even}, \\
  J(0, 2u+w+10) & \text{if } w = 2m < 2u \text{ and } d \ge 3 \text{ is odd}, \\
  \text{Halt} & \text{if } w = 2m+1 < 2u \text{ and } d = 1, \\
  J(0, 2w+8) & \text{if } w = 2m+1 < 2u \text{ and } d = 2, \\
  J(11, 2u+10) & \text{if } w = 1 < 2u \text{ and } d \ge 4 \text{ is even}, \\
  J(d+7, 2w-4) & \text{if } w = 2m+1 \ge 3,\ w < 2u,\text{ and } d \ge 4 \text{ is even}, \\
  J(d+3, 2w) & \text{if } w = 2m+1 < 2u \text{ and } d \ge 3 \text{ is odd}.
\end{cases}
$$

### [`1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`](./M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean)

We define the configuration for $p \in \lbrace 0, 1 \rbrace$ and $k, c \ge 0$:

$$
S(p, k, c) := 0^\infty \ (1110)^p \ 1^k \ \mathrm{D}{>} \ 11 \ 1^c \ 0^\infty.
$$

Starting from $S(0, 2, 0)$ (encoded as `.S false 2 0`, reached after 10 steps from the blank tape), writing $k = 3q + r$ with $r \in \lbrace 0, 1, 2 \rbrace$ and $d = c - q$, the machine follows the map $T$:

$$
\begin{aligned}
  T(S(p, k, c)) &= S(p, k - 3c - 2, 4c + 5) \quad \text{if } c < q, \\
  T(S(p, 3q, c)) &= \begin{cases}
    S(0, 2, 3) & \text{if } c \ge q,\ p = 0,\ q = 0,\text{ and } c = 0, \\
    S(0, 4, c - 1) & \text{if } c \ge q,\ p = 0,\ q = 0,\text{ and } c \ge 1, \\
    S(1, 4q, 1) & \text{if } c \ge q,\ p = 0,\ q \ge 1,\text{ and } d = 0, \\
    S(1, 4q - 1, d) & \text{if } c \ge q,\ p = 0,\ q \ge 1,\text{ and } d \ge 1, \\
    S(0, 2, c + 2) & \text{if } c \ge q,\ p = 1,\text{ and } q = 0, \\
    S(0, 4, 4q + 5) & \text{if } c \ge q,\ p = 1,\ q \ge 1,\text{ and } d = 0, \\
    S(0, 1, 4q + 9) & \text{if } c \ge q,\ p = 1,\ q \ge 1,\text{ and } d = 1, \\
    S(1, 4q + 8, 1) & \text{if } c \ge q,\ p = 1,\ q \ge 1,\text{ and } d = 2, \\
    S(1, 4q + 7, d - 2) & \text{if } c \ge q,\ p = 1,\ q \ge 1,\text{ and } d \ge 3,
  \end{cases} \\
  T(S(p, 3q + 1, c)) &= \begin{cases}
    S(0, 0, 4q + 3) & \text{if } c \ge q,\ p = 0,\text{ and } d = 0, \\
    S(0, 8, 4q + 1) & \text{if } c \ge q,\ p = 1,\text{ and } d = 0, \\
    S(0, 4q + 3p + 4, 1) & \text{if } c \ge q \text{ and } d = 1, \\
    S(0, 4q + 3p + 3, d - 1) & \text{if } c \ge q \text{ and } d \ge 2,
  \end{cases} \\
  T(S(p, 3q + 2, c)) &= \begin{cases}
    S(p, 0, 4q + 5) & \text{if } c \ge q \text{ and } d = 0, \\
    S(0, 0, 4q + 9) & \text{if } c \ge q,\ p = 1,\text{ and } d = 1, \\
    \text{Halt} & \text{if } c \ge q \text{ and } d = p + 1, \\
    S(0, 4q + 4p + 6, 0) & \text{if } c \ge q \text{ and } d = p + 2, \\
    S(0, 4q + 4p + 6, 3) & \text{if } c \ge q \text{ and } d = p + 3, \\
    S(0, 4q + 4p + 8, d - p - 4) & \text{if } c \ge q \text{ and } d \ge p + 4.
  \end{cases}
\end{aligned}
$$

### [`1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA`](./M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA.lean)

Eliminating $(c, a)$ from the 4-counter *Lucy's Moonlight* configuration $C(c, b, a, d)$ reduces the dynamics to a single counter $b \ge 0$ and bit $p \in \lbrace 0, 1 \rbrace$ on $L_p(b) := C(0, b, 0, p)$, starting from $L_0(0)$ (encoded as `.L false 0`). Writing $q = \lfloor b/3 \rfloor$:

$$
T(L_0(b)) = \begin{cases}
  D(0,\ 2q + 1,\ 1) & \text{if } b \equiv 0 \pmod{3}, \\
  L_0(8q + 5) & \text{if } b \not\equiv 0 \pmod{3},
\end{cases}
\qquad
T(L_1(b)) = \begin{cases}
  \text{Halt} & \text{if } b \equiv 0 \pmod{3}, \\
  D(0,\ 2q + 3,\ 1) & \text{if } b \equiv 1 \pmod{3}, \\
  L_0(8q + 6) & \text{if } b \equiv 2 \pmod{3},
\end{cases}
$$

where `drainA` ($D(b, a, p)$) drains $a$ strictly to $0$ (with $q = \lfloor b/3 \rfloor$):

$$
D(b, a, p) = \begin{cases}
  L_p(b) & \text{if } a = 0, \\
  L_0(8q + 7 + p) & \text{if } a = 1 \text{ and } b \equiv 0 \pmod{3}, \\
  L_0(8q + 13 + p) & \text{if } a = 1 \text{ and } b \equiv 1 \pmod{3}, \\
  L_p(8q + 8) & \text{if } a = 1 \text{ and } b \equiv 2 \pmod{3}, \\
  D(8q + 10,\ a - 2,\ p) & \text{if } a \ge 2 \text{ and } b \equiv 0 \pmod{3}, \\
  D(8q + 16,\ a - 2,\ p) & \text{if } a \ge 2 \text{ and } b \equiv 1 \pmod{3}, \\
  D(8q + 8,\ a - 1,\ p) & \text{if } a \ge 2 \text{ and } b \equiv 2 \pmod{3}.
\end{cases}
$$

### [`1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC`](./M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean)

We define the configuration for $b, c \ge 0$:

$$
A(b, c) := 0^\infty \ 1^c \ 0 \ \mathrm{A}{>} \ 0 \ 1^b \ 0^\infty.
$$

Starting from $A(4, 3)$ (reached after 27 steps from the blank tape), the machine follows the map $T$, where $h = \lfloor c/2 \rfloor$:

$$
T(A(b, c)) = \begin{cases}
  A(2c+4, 3) & \text{if } b = 0, \\
  A(3, 3) & \text{if } b = 2 \text{ and } c = 0, \\
  A(5, c-1) & \text{if } b = 2 \text{ and } c \ge 1, \\
  A(b-2h-4, 2c+5) & \text{if } b \ge 2h+5, \\
  A(2c+6, 3) & \text{if } b \text{ is odd and } b \le 2h+3, \\
  F(b-3, 2, 0, c-b+1) & \text{if } b \ge 4 \text{ is even and } b \le 2h, \\
  F(b-4+(c \bmod 2), 2, 0, 0) & \text{if } b \ge 4 \text{ is even and } b = 2h+2, \\
  \text{Halt} & \text{if } b \ge 4 \text{ is even and } b = 2h+4,
\end{cases}
$$

where $F(m, p, n, c)$ (`evalOdd`) is defined recursively on $m$:

$$
F(m, p, n, c) = \begin{cases}
  A(4n+c+7, 3) & \text{if } m = 0 \text{ and } p \le n+1, \\
  A(2(p-n-2)+1, 4n+c+6) & \text{if } m = 0 \text{ and } p \ge n+2, \\
  A(4n+9, c) & \text{if } m = 1 \text{ and } p \le n+1, \\
  F(0, p-n-2, 2n+3, c) & \text{if } m = 1 \text{ and } p \ge n+2, \\
  F(m-2, 2n+4, 0, c) & \text{if } m \ge 2 \text{ and } p \le n+1, \\
  F(m-1, p-n-2, 2n+3, c) & \text{if } m \ge 2 \text{ and } p \ge n+2.
\end{cases}
$$

This machine shares the exact same transition map $T$ and helper $F$ with [`1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`](./M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean), which starts from $A(5, 2)$.

### [`1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD`](./M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean)

Eliminating $(k, a, b)$ from the 4-counter *Space Needle* (`BMO6`) configuration $C(d, k, a, b)$ reduces the dynamics to a **single-counter** map on $N(d) := C(d, 0, 0, 0)$, starting from $N(1)$:

$$
T(N(d)) = S(d, 0), \qquad
S(d, b) = \begin{cases}
  \text{Halt} & \text{if } d = 0, \\
  S(d/2 - 1,\ b + d/2 + 2) & \text{if } d \ge 2 \text{ is even}, \\
  N(b + 4) & \text{if } d = 1, \\
  N\bigl(b + 5(\lfloor d/2 \rfloor - 1) + 9\bigr) & \text{if } d \ge 3 \text{ is odd}.
\end{cases}
$$

### [`1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA`](./M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean)

Contracting the Syracuse $c + 2 \mapsto c$ sweep $(r, b) \mapsto \bigl((b + r) \bmod 2,\ 3\lfloor (b + r)/2 \rfloor + 9\bigr)$ (`syracuseScan`) on $C_d(r, b, c) := 0^\infty \ 1^{r+1} \ \mathrm{C}{>} \ 00 \ 1^{b+4} \ (01)^c \ 1^d \ 011 \ 0^\infty$ restricts $b \in \lbrace 0, 12 \rbrace$ and reduces the machine to a **single counter** $c \ge 0$ across $C_{3,0}(r, c) := C_3(r, 0, c)$, $C_{3,12}(c) := C_3(0, 12, c)$, $C_{6,0}(r, c) := C_6(r, 0, c)$, and $C_{6,12}(c) := C_6(0, 12, c)$. Starting from $C_{3,0}(0, 6)$ (encoded as `.C3_0 false 6`, reached after 322 steps, one macro-step after $C_3(0, 6, 0)$ at step 200), let $\Sigma(r, b, k)$ iterate $(r, b) \mapsto \bigl((b + r) \bmod 2,\ 3\lfloor (b + r)/2 \rfloor + 9\bigr)$ $k$ times; then:

$$
\begin{aligned}
  T(C_{3,0}(r, c)) &= F_3(\Sigma(r, 0, \lfloor c/2 \rfloor),\ c \bmod 2), &
  T(C_{3,12}(c)) &= F_3(\Sigma(0, 12, \lfloor c/2 \rfloor),\ c \bmod 2), \\
  T(C_{6,0}(r, c)) &= F_6(\Sigma(r, 0, \lfloor c/2 \rfloor),\ c \bmod 2), &
  T(C_{6,12}(c)) &= F_6(\Sigma(0, 12, \lfloor c/2 \rfloor),\ c \bmod 2),
\end{aligned}
$$

where `finishC3` ($F_3((r, b), p)$) and `finishC6` ($F_6((r, b), p)$) evaluate the terminal $p = c \bmod 2 \in \lbrace 0, 1 \rbrace$ exit in closed form:

$$
\begin{aligned}
  F_3((r, b), 0) &= \begin{cases}
    C_{3,0}(r, \lfloor b/2 \rfloor + 3) & \text{if } b \text{ is even}, \\
    C_{3,12}(\lfloor b/2 \rfloor) & \text{if } b \text{ is odd and } r = 1, \\
    \text{Halt} & \text{if } b \text{ is odd and } r = 0,
  \end{cases} \\
  F_3((r, b), 1) &= \begin{cases}
    C_{6,0}(r, \lfloor b/2 \rfloor + 3) & \text{if } b \text{ is odd}, \\
    \text{Halt} & \text{if } b \text{ is even and } r = 0, \\
    C_{6,0}(1, 13) & \text{if } b = 0 \text{ and } r = 1, \\
    C_{6,12}(\lfloor b/2 \rfloor - 1) & \text{if } b \ge 2 \text{ is even and } r = 1,
  \end{cases} \\
  F_6((r, b), 0) &= \begin{cases}
    C_{3,0}(r, \lfloor b/2 \rfloor + 5) & \text{if } b \text{ is odd}, \\
    C_{3,12}(\lfloor b/2 \rfloor + 1) & \text{if } b \text{ is even and } r = 1, \\
    \text{Halt} & \text{if } b \text{ is even and } r = 0,
  \end{cases} \\
  F_6((r, b), 1) &= F_3\bigl((s_1 \bmod 2,\ 3\lfloor s_1/2 \rfloor + 9),\ 1\bigr),
    \quad s = b + r,\ s_1 = 3\lfloor s/2 \rfloor + 6 + (s \bmod 2).
\end{aligned}
$$

### [`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`](./M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH.lean)

Contracting the diagonal sweep $P_{270}(a + 2, b, c + 4) \to P_{270}(a, b + 3, c)$ via $k = \min(\lfloor a/2 \rfloor, \lfloor c/4 \rfloor)$ and draining any intermediate $P_{61}(a', c')$ with $a' > 0$ (which decreases $c$ by at least $6$) reduces the *Pomme* / Baker machine to a **single-counter** map on $P(c) := P_{61}(0, c) = 0^\infty \ 1 \ \mathrm{B}{>} \ 1^{c+3} \ 01 \ 0^\infty$, starting from $P(7)$:

$$
T(P(c)) = D(0, c),
$$

where `drainP` ($D(a, c)$) is defined recursively on $c$ (writing $c_0 = c - 3$, $k = \min(\lfloor a/2 \rfloor, \lfloor c_0/4 \rfloor)$, $a_1 = a - 2k$, $b_1 = 3k$, and $c_1 = c_0 - 4k$ when $c \ge 3$):

$$
D(a, c) = \begin{cases}
  P(4a + 4\lfloor a/2 \rfloor + 15) & \text{if } c = 0, \\
  P(2a + 11) & \text{if } c = 1, \\
  \text{Halt} & \text{if } c = 2, \text{ or } (c \ge 3,\ c_1 \le 1,\ a_1 < 2), \text{ or } (c \ge 3,\ c_1 = 3,\ a_1 \ge 2), \\
  P\bigl(4(a_1 - 2) + 4\lfloor (a_1 - 2)/2 \rfloor + 4b_1 + 35 - 8c_1\bigr) & \text{if } c \ge 3,\ c_1 \in \lbrace 0, 1 \rbrace,\text{ and } a_1 \ge 2, \\
  P(2a_1 + 2b_1 + 13) & \text{if } c \ge 3 \text{ and } c_1 = 2, \\
  P(12b_1 + 63 + 12a_1) & \text{if } c \ge 3,\ c_1 = 3,\text{ and } a_1 \in \lbrace 0, 1 \rbrace, \\
  D(2b_1 + 8 + 2a_1,\ c_1 - 3) & \text{if } c \ge 3 \text{ and } c_1 \ge 4 \text{ (here } a_1 \in \lbrace 0, 1 \rbrace\text{)}.
\end{cases}
$$

### [`1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA`](./M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean)

We define the configurations for $n \ge 0$ (where $L(n) := 0^\infty \ (1100)^n$):

$$
\begin{aligned}
  R_1(n) &:= L(n) \ 100 \ \mathrm{A}{>} \ 0^\infty, \\
  R_2(n) &:= L(n) \ 100100 \ \mathrm{A}{>} \ 0^\infty, \\
  Q(n)   &:= L(n) \ 111100 \ \mathrm{A}{>} \ 0^\infty, \\
  S_4(n) &:= L(n) \ 111100100100 \ \mathrm{A}{>} \ 0^\infty, \\
  S_6(n) &:= L(n) \ 11111100100100 \ \mathrm{A}{>} \ 0^\infty.
\end{aligned}
$$

Starting from $S_6(1)$ (reached after 169 steps from the blank tape), the machine follows the map $T$ (with $w = \lfloor (n-1)/2 \rfloor = 5q + r$
for $n \ge 1$ and $r \in \lbrace 0, 1, 2, 3, 4 \rbrace$):

$$
\begin{aligned}
  T(R_1(n)) &= \begin{cases}
    R_1(4) & \text{if } n = 0, \\
    R_1(6) & \text{if } n = 1, \\
    R_1(n+5) & \text{if } n \ge 2,
  \end{cases} \\
  T(R_2(n)) &= \begin{cases}
    R_1(4) & \text{if } n = 0, \\
    R_1(31q + 8) & \text{if } n \ge 1 \text{ and } r = 0, \\
    R_2(31q + 11) & \text{if } n \ge 1 \text{ and } r = 1, \\
    Q(31q + 19) & \text{if } n \ge 1 \text{ and } r = 2, \\
    R_2(31q + 26) & \text{if } n \ge 1 \text{ and } r = 3, \\
    R_1(31q + 44) & \text{if } n \ge 1 \text{ and } r = 4,
  \end{cases} \\
  T(Q(0)) &= R_1(6), \quad T(S_4(0)) = R_1(10), \quad T(S_6(0)) = R_1(9), \quad T(S_6(1)) = R_2(23), \\
  T(Q(b+1)) &= \Phi_Q(2, b, 3), \quad T(S_4(b+1)) = \Phi_{S_4}(2, b, 3), \quad T(S_6(b+2)) = \Phi_{S_6}(2, b, 3),
\end{aligned}
$$

where for each $H \in \lbrace Q, S_4, S_6 \rbrace$, the scan transducer $\Phi_H(a, b, i)$ with prefix index
$i \in \lbrace 0, 1, 2, 3, 4, 5, 6 \rbrace$ (corresponding to `[0]`, `[0,0,1,0,1,0]`, `[0,0,1,0]`,
`[0,0,1,0,1,1,0]`, `[0,0]`, `[0,1,0]`, `[]`) is defined recursively on $b \ge 0$ (writing
$\lfloor (a + 3)/2 \rfloor = 5q + r$ with $r \in \lbrace 0, 1, 2, 3, 4 \rbrace$) by:

$$
\begin{aligned}
  \Phi_H(a, 0, i) &= \bigl(E_H^{(0)}(a)\bigr)_i, \\
  \Phi_H(a, 1, 0) &= E_H^{(1)}(a), \quad \Phi_H(a, 1, 2) = E_H^{(2)}(a), \\
  \Phi_H(a, b+2, 0) &= \Phi_H(31q + c_r, b, j_r), \quad
    (c_r, j_r) = \bigl((4, 0), (7, 5), (16, 4), (22, 2), (28, 1)\bigr)_r, \\
  \Phi_H(a, b+2, 2) &= \Phi_H(a + 5, b, 3), \\
  \Phi_H(a, b+1, i) &= \begin{cases}
    \Phi_H(a + 6, b, 0) & \text{if } i = 1, \\
    \Phi_H(a + 9, b, 4) & \text{if } i = 3, \\
    \Phi_H(a + 3, b, 5) & \text{if } i = 4, \\
    \Phi_H(a + 4, b, 6) & \text{if } i = 5, \\
    \Phi_H(a + 3, b, 0) & \text{if } i = 6,
  \end{cases}
\end{aligned}
$$

with base-case tables $E_H^{(0)}(a)$ (for $i = 0, \dots, 6$), $E_H^{(1)}(a)$, $E_H^{(2)}(a)$ and
tail maps $\tau_3(w), \tau_4(w), \tau_5(w)$ (writing $w = 5q + r$ with $r \in \lbrace 0, 1, 2, 3, 4 \rbrace$):

$$
\begin{aligned}
  E_Q^{(0)}(a) &= \bigl(R_1(a+4),\ S_6(a+6),\ R_2(a+4),\ S_6(a+8),\ R_1(a+4),\ S_6(a+5),\ S_6(a+3)\bigr), \\
  E_{S_4}^{(0)}(a) &= \bigl(R_2(a+7),\ R_1(a+9),\ R_1(a+9),\ S_4(a+9),\ R_1(a+11),\ Q(a+9),\ R_1(a+6)\bigr), \\
  E_{S_6}^{(0)}(a) &= \bigl(S_4(a+9),\ R_1(a+18),\ R_1(a+10),\ \text{Halt},\ R_2(a+11),\ R_1(a+14),\ R_1(a+15)\bigr), \\
  E_Q^{(1)}(a) &= S_6(a+2), \quad E_Q^{(2)}(a) = R_1(a+9), \\
  E_{S_4}^{(1)}(a) &= \tau_5(\lfloor (a+1)/2 \rfloor + 1), \quad E_{S_4}^{(2)}(a) = R_1(a+13), \\
  E_{S_6}^{(1)}(a) &= \tau_4(\lfloor (a+1)/2 \rfloor + 1), \quad E_{S_6}^{(2)}(a) = \tau_3(\lfloor (a+8)/2 \rfloor), \\
  \tau_3(5q + r) &= \bigl(R_1(31q+10),\ Q(31q+16),\ R_2(31q+23),\ \text{Halt},\ R_2(31q+37)\bigr)_r, \\
  \tau_4(5q + r) &= \bigl(R_1(31q+16),\ R_2(31q+15),\ R_1(31q+25),\ S_6(31q+28),\ R_2(31q+41)\bigr)_r, \\
  \tau_5(5q + r) &= \bigl(R_1(31q+12),\ R_1(31q+15),\ R_2(31q+26),\ Q(31q+34),\ R_1(31q+45)\bigr)_r.
\end{aligned}
$$

### [`1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD`](./M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean)

Restricting $C(a, b, d) := 0^\infty \ 1^a \ (10)^b \ \mathrm{A}{>} \ 1^d \ 0^\infty$ to the $a = 0$ Poincaré section $C(b, d) := C(0, b, d)$ reduces the machine to 2 counters starting from the blank tape $C(0, 0)$:

$$
T(C(b, d)) = \begin{cases}
  C(0,\ 2b + 4) & \text{if } d = 0, \\
  C(2,\ 5) & \text{if } b = 0 \text{ and } d = 1, \\
  C(2,\ 2b + 1) & \text{if } b \ge 1 \text{ and } d = 1, \\
  D(3d - 4,\ 3,\ 2b - 2d + 3) & \text{if } d \ge 2 \text{ and } b \ge d - 1, \\
  \text{Halt} & \text{if } d = b + 2, \\
  D(3b + 2,\ 0,\ 6) & \text{if } d = b + 3, \\
  D(3b + 4,\ 0,\ 4) & \text{if } d = b + 4, \\
  D(3b + 3,\ 2,\ d - b - 5) & \text{if } d \ge b + 5,
\end{cases}
$$

where `drainA` ($D(a, b, d)$) drains $a$ strictly to $0$ (writing $(a_1, b_1, d_1) = (a + 1, 0, 2b + 2)$ when $d = 0$ and $(a_1, b_1, d_1) = (a, b, d)$ when $d \ge 1$, and $k = \min(\lfloor a_1/3 \rfloor, d_1)$):

$$
D(a, b, d) = \begin{cases}
  C(b, d) & \text{if } a = 0, \\
  C(1,\ 2b + 1) & \text{if } a = 1 \text{ and } d = 0, \\
  C(0,\ d + 2) & \text{if } a = 1,\ b = 0,\text{ and } d \ge 1, \\
  C(1,\ 2b + 4d + 1) & \text{if } a = 1,\ b \ge 1,\text{ and } d \ge 1, \\
  C(b + 1,\ d - 1) & \text{if } a = 2 \text{ and } d \ge 1, \\
  D(a_1 - 3k,\ b_1 + 2k,\ d_1 - k) & \text{otherwise.}
\end{cases}
$$

### [`1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD`](./M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean)

Restricting to canonical parity $q = a \bmod 2$, contracting the odd-$a$ drain, and eliminating all even-block $F$-sweeps (`evalF0`, `evalF1`, `evalFGe2` with termination measure $5k + 3b + 4c$) reduces the machine to a single-family, 3-counter map on $E(a, b, c) := 0^\infty \ \mathrm{E}{>} \ 0 \ 0^{a \bmod 2} \ 1^a \ 0 \ 1^b \ 0 \ 1^c \ 0^\infty$, starting from $E(3, 0, 0)$:

$$
T(E(a, b, c)) = \begin{cases}
  F_0(\lfloor a/2 \rfloor, b, c) & \text{if } a \text{ is even}, \\
  \text{Halt} & \text{if } a = 1, \\
  E(b + 3a - 6,\ c + 3,\ 0) & \text{if } a \ge 3 \text{ is odd},
\end{cases}
$$

where $F_0(k, b, c)$, $F_1(k, b, c)$, and $F_{\ge 2}(d, k, b, c)$ (`evalF0`, `evalF1`, and `evalFGe2`, evaluating $F(0, 2k, b, c)$, $F(1, 2k, b, c)$, and $F(d + 2, 2k, b, c)$) are defined by:

$$
\begin{aligned}
  F_0(k, b, c) &= \begin{cases}
    E(1, 3, 0) & \text{if } k = 0,\ b = 0,\text{ and } c = 0, \\
    F_1(0, c, 0) & \text{if } k = 0,\ b = 0,\text{ and } c \ge 1, \\
    F_1(b/2, c, 0) & \text{if } k = 0 \text{ and } b \ge 2 \text{ is even}, \\
    \text{Halt} & \text{if } k = 0 \text{ and } b = 1, \\
    E(c + 3, 3, 0) & \text{if } k = 0 \text{ and } b = 3, \\
    E(2, b - 4, c + 3) & \text{if } k = 0 \text{ and } b \ge 5 \text{ is odd}, \\
    E(b + 2, c + 3, 0) & \text{if } k = 1, \\
    F_1(k - 2, b + 3, c) & \text{if } k \ge 2,
  \end{cases} \\
  F_1(k, b, c) &= \begin{cases}
    E(2, 3, 0) & \text{if } k = 0,\ b = 0,\text{ and } c = 0, \\
    F_{\ge 2}(0, 0, c, 0) & \text{if } k = 0,\ b = 0,\text{ and } c \ge 1, \\
    F_{\ge 2}(0, b/2, c, 0) & \text{if } k = 0 \text{ and } b \ge 2 \text{ is even}, \\
    \text{Halt} & \text{if } k = 0 \text{ and } b = 1, \\
    E(c + 4, 3, 0) & \text{if } k = 0 \text{ and } b = 3, \\
    E(3, b - 4, c + 3) & \text{if } k = 0 \text{ and } b \ge 5 \text{ is odd}, \\
    E(b + 4, c, 0) & \text{if } k = 1 \text{ and } b \text{ is odd}, \\
    F_{\ge 2}(0, b/2, c + 3, 0) & \text{if } k = 1 \text{ and } b \text{ is even}, \\
    F_{\ge 2}(0, k - 2, b + 3, c) & \text{if } k \ge 2,
  \end{cases} \\
  F_{\ge 2}(d, k, b, c) &= \begin{cases}
    E(d + 3, 3, 0) & \text{if } k = 0,\ b = 0,\text{ and } c = 0, \\
    F_{\ge 2}(d + 1, 0, c, 0) & \text{if } k = 0,\ b = 0,\text{ and } c \ge 1, \\
    F_{\ge 2}(d + 1, b/2, c, 0) & \text{if } k = 0 \text{ and } b \ge 2 \text{ is even}, \\
    \text{Halt} & \text{if } k = 0 \text{ and } b = 1, \\
    E(d + c + 5, 3, 0) & \text{if } k = 0 \text{ and } b = 3, \\
    E(d + 4, b - 4, c + 3) & \text{if } k = 0 \text{ and } b \ge 5 \text{ is odd}, \\
    E(d + 1, b + 4, c) & \text{if } k = 1, \\
    F_{\ge 2}(d + 1, k - 2, b + 3, c) & \text{if } k \ge 2.
  \end{cases}
\end{aligned}
$$

### [`1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC`](./M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean)

Eliminating the auxiliary family $B(a, b, c)$ via `evalB` and draining $2k + 2 < b$ via `drainA` reduces the machine to a single-family, 2-counter map on $A(k, b) := 0^\infty \ \mathrm{C}{>} \ 0 \ (10)^{2k+2} \ 110 \ (10)^b \ 0^\infty$, starting from $A(0, 0)$:

$$
T(A(k, b)) = \begin{cases}
  T(A(2k + 2,\ b - 2k - 3)) & \text{if } 2k + 2 < b, \\
  \text{Halt} & \text{if } 2k + 2 = b, \\
  A\bigl(\lfloor (2k + 1 - b)/2 \rfloor,\ 2b + 2\bigr) & \text{if } 2k + 2 > b \text{ and } 2k + 1 - b \text{ is even}, \\
  B\bigl(2,\ 2\lfloor (2k + 1 - b)/2 \rfloor + 1,\ b + 1\bigr) & \text{if } 2k + 2 > b \text{ and } 2k + 1 - b \text{ is odd},
\end{cases}
$$

where $B(a, b, c)$ evaluates to $A(0, b')$ via $B(a, b, c) = B(2a + 2, b - a - 1, c)$ for $a < b$, $A(0, 4a + 2c + 6)$ for $a = b$, and $A(0, 2a + 2c + 2)$ for $a > b$.

### [`1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`](./M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean)

We define the configuration for $b, d \ge 0$:

$$
E(b, d) := 0^\infty \ (10)^b \ 1111 \ \mathrm{E}{>} \ 1^{d+2} \ 0^\infty.
$$

Starting from $E(0, 1)$ (reached after 28 steps from the blank tape), with $c = d + 1$ and $m = \lfloor d / 2 \rfloor$, the machine follows the map $T$:

$$
T(E(b, d)) = \begin{cases}
  E(0, 2c+3) & \text{if } b = m+1, \\
  E(2, 2c+1) & \text{if } b = m+2, \\
  E(b-m-3, 2c+5) & \text{if } b \ge m+3, \\
  E(0, 2c+2) & \text{if } b \le m \text{ and } c - 2b \le 2, \\
  \text{Halt} & \text{if } b \le m \text{ and } c - 2b = 3, \\
  E(2b+2, 2(c-2b)-7) & \text{if } b \le m \text{ and } 4 \le c - 2b \le 6, \\
  E(2b+4, c-2b-7) & \text{if } b \le m \text{ and } c - 2b \ge 7.
\end{cases}
$$

### [`1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA`](./M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean)

We define the configuration for $a \ge 0$, $b \ge 6$:

$$
C(a, b) := 0^\infty \ 110 \ \mathrm{A}{>} \ (11)^a \ 0 \ 1^b \ 0^\infty.
$$

Starting from $C(0, 9)$ (encoded as `.C 0 3`, reached after 74 steps from the blank tape), the machine follows the map $T$:

$$
T(C(a, b)) = \begin{cases}
  C(k+1, 9) & \text{if } a = 0,\ b = 2k+6, \\
  C(a-k+3, 6k+12) & \text{if } a \ge 1,\ b = 2k+6,\ k \le a+2, \\
  \text{Halt} & \text{if } a \ge 1,\ b = 2k+6,\ k \in \lbrace a+3, a+4 \rbrace, \\
  C(k-a-4, 6a+33) & \text{if } a \ge 1,\ b = 2k+6,\ k \ge a+5, \\
  C(k-a, 6a+6) & \text{if } b = 2k+1,\ k > a, \\
  \text{Halt} & \text{if } b = 2k+1,\ a \in \lbrace k, k+1 \rbrace, \\
  C(a-k-1, 6k+9) & \text{if } b = 2k+1,\ a \ge k+2.
\end{cases}
$$

### [`1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE`](./M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean)

Eliminating the four transient families $W, M, S, R$ (via `evalCPos`, `evalW`, `evalM` with termination measure $k$, `evalS`, and `evalR`) reduces the 5-constructor, up-to-5-counter system to the two canonical return families $C_0(a, b) := C(a, b, 0, 0)$ and $C_1(a, b, c) := C(a, b, c, 1)$, starting from $C_0(0, 3)$:

$$
\begin{aligned}
  T(C_0(a, b)) &= \begin{cases}
    C_+(2, 1, 0, 0) & \text{if } a = 0 \text{ and } b = 0, \\
    \text{Halt} & \text{if } a = 0 \text{ and } b = 1, \\
    C_+(2, b - 2, 0, 0) & \text{if } a = 0 \text{ and } b \ge 2, \\
    C_+(a, b, 0, 0) & \text{if } a \ge 1,
  \end{cases} \\
  T(C_1(a, b, c)) &= \begin{cases}
    \text{Halt} & \text{if } a = 0,\ b = 0,\text{ and } c = 0, \\
    C_+(2, 1, c, 1) & \text{if } a = 0,\ b = 0,\text{ and } c \ge 1, \\
    C_0(c + 2,\ 0) & \text{if } a = 0 \text{ and } b = 1, \\
    C_+(2, b - 2, c, 1) & \text{if } a = 0 \text{ and } b \ge 2, \\
    C_+(a, b, c, 1) & \text{if } a \ge 1,
  \end{cases}
\end{aligned}
$$

where for $d \in \lbrace 0, 1 \rbrace$ (with $c = 0$ whenever $d = 0$), the helpers $C_+$ (`evalCPos`), $W$ (`evalW`), $M$ (`evalM`, recursive on $k$), $S$ (`evalS`), and $R$ (`evalR`) are defined by:

$$
\begin{aligned}
  C_+(a, b, c, d) &= \begin{cases}
    S(0, 2, 0, 0) & \text{if } b = 0,\ d = 1,\ c = 0,\text{ and } a = 1, \\
    M(a - 2, 0, 0, 0, 0) & \text{if } b = 0,\ d = 1,\ c = 0,\text{ and } a \ge 2, \\
    S(0, 1, c, d) & \text{if } b = 0,\ (d = 0 \text{ or } c \ge 1),\text{ and } a = 1, \\
    W(a - 2, 2, c, d) & \text{if } b = 0,\ (d = 0 \text{ or } c \ge 1),\text{ and } a \ge 2, \\
    S(0, b + 1, c, d) & \text{if } b \ge 1 \text{ and } a = 1, \\
    M(a - 2, 0, b - 1, c, d) & \text{if } b \ge 1 \text{ and } a \ge 2,
  \end{cases} \\
  W(k, b, c, d) &= \begin{cases}
    C_0(2, b) & \text{if } k = 0 \text{ and } d = 0, \\
    C_1(2, b, c) & \text{if } k = 0 \text{ and } d = 1, \\
    S(0, b + 3, c, d) & \text{if } k = 1, \\
    M(k - 2, 0, b + 1, c, d) & \text{if } k \ge 2,
  \end{cases} \\
  M(k, u, b, c, d) &= \begin{cases}
    S(u + 2, b, c, d) & \text{if } k = 0, \\
    C_1(0, 0, u + 5) & \text{if } k = 1,\ b = 0,\text{ and } d = 0, \\
    C_1(0, 3, u + 5) & \text{if } k = 2,\ b = 0,\text{ and } d = 0, \\
    C_1(0, 4, u + 5) & \text{if } k = 3,\ b = 0,\text{ and } d = 0, \\
    C_1(2, 2, u + 5) & \text{if } k = 4,\ b = 0,\text{ and } d = 0, \\
    S(0, 5, u + 5, 1) & \text{if } k = 5,\ b = 0,\text{ and } d = 0, \\
    M(k - 6, 0, 3, u + 5, 1) & \text{if } k \ge 6,\ b = 0,\text{ and } d = 0, \\
    W(k - 1, 2(u + c) + 6, 0, 0) & \text{if } k \ge 1,\ b = 0,\text{ and } d = 1, \\
    W(k - 1, 2u + 6, 0, 0) & \text{if } k \ge 1,\ b = 1,\text{ and } d = 0, \\
    M(k - 1, u + 2, 0, 0, 0) & \text{if } k \ge 1,\ b = 1,\ d = 1,\text{ and } c = 0, \\
    W(k - 1, 2u + 6, c, 1) & \text{if } k \ge 1,\ b = 1,\ d = 1,\text{ and } c \ge 1, \\
    M(k - 1, u + 2, b - 2, c, d) & \text{if } k \ge 1 \text{ and } b \ge 2,
  \end{cases} \\
  S(a, b, c, d) &= \begin{cases}
    C_0(a + 2, 0) & \text{if } b = 0 \text{ and } d = 0, \\
    C_0(0, 2(a + c) + 4) & \text{if } b = 0 \text{ and } d = 1, \\
    C_0(0, 2a + 4) & \text{if } b = 1 \text{ and } d = 0, \\
    R(a + 1, 0, 0, 0) & \text{if } b = 1,\ d = 1,\text{ and } c = 0, \\
    C_1(0, 2a + 4, c) & \text{if } b = 1,\ d = 1,\text{ and } c \ge 1, \\
    R(a + 1, b - 2, c, d) & \text{if } b \ge 2,
  \end{cases} \\
  R(a, b, c, d) &= \begin{cases}
    C_0(0, 2a + 7) & \text{if } b = 0 \text{ and } d = 0, \\
    C_0(0, 2(a + c) + 5) & \text{if } b = 0 \text{ and } d = 1, \\
    C_0(0, 2a + 5) & \text{if } b = 1 \text{ and } d = 0, \\
    \text{Halt} & \text{if } (b = 1,\ d = 1,\ c = 0) \text{ or } (b = 2,\ d = 0), \\
    C_1(0, 2a + 5, c) & \text{if } b = 1,\ d = 1,\text{ and } c \ge 1, \\
    C_0(a + c + 3, 0) & \text{if } b = 2 \text{ and } d = 1, \\
    C_0(a + 3, b - 3) & \text{if } b \ge 3 \text{ and } d = 0, \\
    C_1(a + 3, b - 3, c) & \text{if } b \ge 3 \text{ and } d = 1.
  \end{cases}
\end{aligned}
$$

### [`1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`](./M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean)

Restricting $C(a, k, d, c) := 0^\infty \ (10)^a \ (11)^k \ \mathrm{C}{>} \ (11)^d \ (10)^c \ 1111 \ 0^\infty$ to the $k = 0,\ d = 0$ Poincaré section $D(a, c) := C(a, 0, 0, c)$ reduces the machine to a single-family, 2-counter map starting from $D(0, 1)$ (reached after 27 steps):

$$
T(D(a, c)) = \Delta(a, 0, c),
$$

where `evalK` ($K(k, c)$, writing $c_1 = \max(c, 1)$) and `drainD` ($\Delta(a, d, c)$) are defined recursively on $k$ and $a$:

$$
K(k, c) = \begin{cases}
  K(k - c_1,\ 2c_1 + 1) & \text{if } c_1 \le k, \\
  (2k + 2,\ c_1 - k - 1) & \text{if } c_1 > k,
\end{cases}
\qquad
\Delta(a, d, c) = \begin{cases}
  \text{Halt} & \text{if } a = 0 \text{ and } c = 0, \\
  D(d + 1,\ c) & \text{if } a = 0 \text{ and } c \ge 1, \\
  \Delta\bigl(a - 1,\ K(d + 1,\ 0)\bigr) & \text{if } a \ge 1 \text{ and } c = 0, \\
  \Delta\bigl(a - 1,\ K(d + 2 - c,\ 2c - 1)\bigr) & \text{if } a \ge 1 \text{ and } 1 \le c \le d + 2, \\
  \Delta(a - 1,\ 2d + 4,\ c - d - 3) & \text{if } a \ge 1 \text{ and } c \ge d + 3.
\end{cases}
$$

### [`1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC`](./M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean)

Collapsing all 12 `State` families (`D7..D296`, up to 4 counters) into $D_0(x, d) := D_{76}(0, x, d)$ and $D_1(x, d) := D_{231}(0, 0, x, d)$ reduces *Counter6* to a single-constructor, 2-counter + 1-bit closed-form map (with zero recursive helpers) starting from $D_1(3, 1)$ (encoded as `.D true 3 1`):

$$
\begin{aligned}
  T(D_0(2m, 0)) &= \begin{cases}
    \text{Halt} & \text{if } m \text{ is odd}, \\
    D_1\bigl(3,\ 3\lfloor (3m + 7)/2 \rfloor + 4\bigr) & \text{if } m \text{ is even},
  \end{cases} \\
  T(D_0(2m + 1, 0)) &= D_1(3,\ 3m + 9), \\
  T(D_0(x, d + 1)) &= D_{1 - (x \bmod 2)}\bigl(3\lfloor (x + 2)/2 \rfloor + 3,\ d\bigr), \\
  T(D_1(2m, d)) &= D_0(3m + 1,\ d), \\
  T(D_1(2m + 1, 0)) &= \begin{cases}
    \text{Halt} & \text{if } m \text{ is even}, \\
    D_1\bigl(3,\ 3\lfloor (3m + 6)/2 \rfloor + 4\bigr) & \text{if } m \text{ is odd},
  \end{cases} \\
  T(D_1(2m + 1, d + 1)) &= D_1(3m + 5,\ d).
\end{aligned}
$$

### [`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`](./M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean)

We define the configuration for $a, b \ge 0$ and $p \in \lbrace 0, 1 \rbrace$:

$$
D_p(a, b) := 0^\infty \ (11)^{a+1} \ 0 \ (11)^{b+1} \ 0 \ \mathrm{D}{>} \ 1 \ 1^{2+3p} \ 0^\infty.
$$

Starting from $D_0(2, 0)$ (encoded as `.C 2 0 false`, reached after 76 steps from the blank tape), the machine follows the map $T$:

$$
T(D_p(a, b)) = \begin{cases}
  D_p(a-b-2, 3b+p+4) & \text{if } a \ge b+2, \\
  D_0(3b+5, 0) & \text{if } a = b+1,\ p = 1, \\
  D_1(3b+2, 2) & \text{if } a = b+1,\ p = 0, \\
  \text{Halt} & \text{if } a \le b \le a+1, \\
  D_1(3a+5, 2) & \text{if } b = a+2,\ p = 1, \\
  D_0(3a+5, 0) & \text{if } b = a+2,\ p = 0, \\
  D_{1-p}(b-a-3, 3a+2p+5) & \text{if } b \ge a+3.
\end{cases}
$$

### [`1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD`](./M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean)

We define the configuration for $a, c \ge 0$:

$$
C(a, c) := 0^\infty \ 1^{a+2} \ \mathrm{E}{>} \ 110 \ 1^{2c+2} \ 0^\infty.
$$

Starting from $C(8, 1)$ (reached after 127 steps from the blank tape), with $k = \lfloor a / 2 \rfloor$, the machine follows the map $T$:

$$
T(C(a, c)) = \begin{cases}
  \text{Halt} & \text{if } c = 0, \\
  C(2, k + 3) & \text{if } c = 1 \text{ and } a \text{ is odd}, \\
  C(14, 0) & \text{if } a = 0 \text{ and } c = 1, \\
  C(17, k - 1) & \text{if } a \ge 2 \text{ is even and } c = 1, \\
  C(3a + 20, d - k - 3) & \text{if } c = d + 2 \text{ and } k + 3 \le d, \\
  C(6d + 3(a \bmod 2) + 5, k + 2 - d) & \text{if } c = d + 2 \text{ and } d \le k + 2.
\end{cases}
$$

### [`1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE`](./M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean)

Restricting $D(a, k, w) := 0^\infty \ (10)^a \ 1^{2k+1} \ \mathrm{D}{>} \ 1^{w+1} \ 0^\infty$ to the $k = 0$ Poincaré section $D(a, w) := D(a, 0, w)$ reduces the machine to 2 counters starting from $D(0, 1)$ (reached after 13 steps), with $m = \lfloor w/2 \rfloor$:

$$
T(D(a, w)) = \begin{cases}
  D(a - m - 1,\ 2w + 3) & \text{if } a > m, \\
  D(0,\ 2w + 2) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D(2a + 2,\ 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  K_2(2a + 2,\ w - 2a - 6) & \text{if } w \ge 2a + 6,
\end{cases}
$$

where `evalK2` ($K_2(a, w)$, evaluating $D(a, 2, w)$ with $m = \lfloor w/2 \rfloor$) decreases strictly in $w$:

$$
K_2(a, w) = \begin{cases}
  D(a - m - 1,\ 2w + 7) & \text{if } a > m, \\
  D(0,\ 2w + 6) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D(2a + 4,\ 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  K_2(2a + 4,\ w - 2a - 6) & \text{if } w \ge 2a + 6.
\end{cases}
$$

### [`1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE`](./M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean)

We define the configuration for $a, c \ge 0$:

$$
P_1(a, c) := 0^\infty \ 1^a \ \mathrm{A}{>} \ 1^c \ 0^\infty.
$$

Starting from $P_1(2, 1)$ (reached after 6 steps from the blank tape), the machine follows the map $T$:

$$
T(P_1(a, c)) = \begin{cases}
  P_1(2, a+1) & \text{if } c = 0, \\
  P_1(a+2, 0) & \text{if } c = 1, \\
  P_1(a+3, c-2) & \text{if } c \ge 2 \text{ and } a \text{ is even}, \\
  \text{Halt} & \text{if } c = 2 \text{ and } a \text{ is odd}, \\
  G(\lfloor a/2 \rfloor, 1) & \text{if } c = 3 \text{ and } a \text{ is odd}, \\
  G(\lfloor a/2 \rfloor + 1, c-2) & \text{if } c \ge 4 \text{ and } a \text{ is odd},
\end{cases}
$$

where $G(k, c)$ (`evalP2`) is defined recursively by:

$$
G(k, c) = \begin{cases}
  P_1(0, 2c+3) & \text{if } 2k \le c \le 2k+1, \\
  P_1(4k+4, c-2k-2) & \text{if } c \ge 2k+2, \\
  G(k - \lfloor c/2 \rfloor - 1, 2c+3) & \text{if } c < 2k.
\end{cases}
$$

### [`1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE`](./M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean)

Encoding $j \in \lbrace 0, 1 \rbrace$ as a Boolean bit $p$ on $D_p(a, w) := 0^\infty \ (10)^a \ 1^{2p+3} \ \mathrm{D}{>} \ 1 \ 1^w \ 0^\infty$ and contracting the quadratic $w$-drain via `drainJ1` ($J_1$) gives a 2-counter + 1-bit map starting from $D_0(0, 3)$ (encoded as `.D false 0 3`, reached after 38 steps), with $m = \lfloor w/2 \rfloor$:

$$
T(D_0(a, w)) = \begin{cases}
  D_0(a - m - 2,\ 2w + 5) & \text{if } a \ge m + 2, \\
  D_1(1,\ 2w + 1) & \text{if } a = m + 1, \\
  D_1(1,\ 2w) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D_0(2a + 2,\ 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  J_1(2a + 3,\ w - 2a - 6) & \text{if } w \ge 2a + 6,
\end{cases}
\qquad
T(D_1(a, w)) = J_1(a, w),
$$

where $J_1(a, w)$ (`drainJ1`, with $m = \lfloor w/2 \rfloor$) decreases strictly in $w$:

$$
J_1(a, w) = \begin{cases}
  D_0(a - m - 2,\ 2w + 7) & \text{if } a \ge m + 2, \\
  D_1(1,\ 2w + 3) & \text{if } a = m + 1, \\
  D_1(1,\ 2w + 2) & \text{if } a = m, \\
  \text{Halt} & \text{if } w = 2a + 2, \\
  D_0(2a + 3,\ 2w - 4a - 5) & \text{if } 2a + 3 \le w \le 2a + 5, \\
  J_1(2a + 4,\ w - 2a - 6) & \text{if } w \ge 2a + 6.
\end{cases}
$$

### [`1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE`](./M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean)

Contracting the $C_2(a, b) \to^* C_1(2a + 2b + 7)$ sweep and evaluating the $D(a, b, c)$ diagonal drain $k = \min(\lfloor b/2 \rfloor, c)$ across cycles $D(a, b + 6, 0) \to D(0, b, a + 4)$ reduces the three-family system to a **single-counter** map on $C(a) := C_1(a) = 0^\infty \ 1^{a+1} \ \mathrm{C}{>} \ 0^\infty$, starting from $C(3)$:

$$
T(C(0)) = \text{Halt}, \qquad T(C(1)) = C(9), \qquad T(C(a + 2)) = D_0(a, 1),
$$

where `evalD0` ($D_0(b, c)$, writing $k = \min(\lfloor b/2 \rfloor, c)$, $a_1 = 2k$, $b_1 = b - 2k$, and $c_1 = c - k$) decreases strictly in $b$:

$$
D_0(b, c) = \begin{cases}
  C(4a_1 + 2c_1 + 11) & \text{if } c_1 > 0 \text{ and } b_1 = 0, \\
  C(4a_1 + 15) & \text{if } c_1 = 1 \text{ and } b_1 = 1, \\
  C(4a_1 + 2c_1 + 13) & \text{if } c_1 \ge 2 \text{ and } b_1 = 1, \\
  C(4a_1 + 11 + 2b_1) & \text{if } c_1 = 0 \text{ and } b_1 \in \lbrace 0, 1 \rbrace, \\
  C(4a_1 + 17) & \text{if } c_1 = 0 \text{ and } b_1 = 2, \\
  \text{Halt} & \text{if } c_1 = 0 \text{ and } b_1 \in \lbrace 3, 4 \rbrace, \\
  C(2a_1 + 15) & \text{if } c_1 = 0 \text{ and } b_1 = 5, \\
  D_0(b_1 - 6,\ a_1 + 4) & \text{if } c_1 = 0 \text{ and } b_1 \ge 6.
\end{cases}
$$

### [`1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`](./M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean)

We define the configuration for $b, c \ge 0$:

$$
P(b, c) := 0^\infty \ 11 \ (01)^b \ 10101 \ \mathrm{D}{>} \ (10)^c \ 1111 \ 0^\infty.
$$

Starting from $P(1, 0)$ (reached after 73 steps from the blank tape), the machine follows the map $T$:

$$
T(P(b, c)) = \begin{cases}
  P(2b+4, c-b-3) & \text{if } c \ge b+3, \\
  \text{Halt} & \text{if } c = b+2, \\
  P(0, 2b+6) & \text{if } c = b+1, \\
  P(b-3c, 4c+6) & \text{if } c \le b \text{ and } 3c+1 \le b, \\
  P(1, 4c+6) & \text{if } b < 3c+1 \le 3b+1 \text{ and } b - c \text{ is odd}, \\
  P(0, 4c+6) & \text{if } b < 3c+1 \le 3b+1 \text{ and } b - c \text{ is even}.
\end{cases}
$$

Under $(a, d) = (c, b + 1)$, this map is identical to that of [`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`](./M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean), which starts from $P(1, 1)$.

### [`1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`](./M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean)

We define the configuration for $a, d \ge 0$:

$$
P(a, d) := 0^\infty \ 1111 \ (01)^a \ 1 \ \mathrm{C}{>} \ 011 \ (01)^d \ 1 \ 0^\infty.
$$

Starting from $P(1, 1)$ (reached after 70 steps from the blank tape), the machine follows the map $T$:

$$
T(P(a, d)) = \begin{cases}
  P(a-d-2, 2d+3) & \text{if } a \ge d+2, \\
  \text{Halt} & \text{if } a = d+1, \\
  P(2a+4, 1) & \text{if } a = d, \\
  P(4a+6, d-3a) & \text{if } a < d \text{ and } 3a+1 \le d, \\
  P(4a+6, 2) & \text{if } a < d < 3a+1 \text{ and } d - a \text{ is even}, \\
  P(4a+6, 1) & \text{if } a < d < 3a+1 \text{ and } d - a \text{ is odd}.
\end{cases}
$$

Under $(a, d) = (c, b + 1)$ (for $d \ge 1$), this map is identical to that of [`1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`](./M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean), which starts from $(b, c) = (1, 0)$ (corresponding to $(a, d) = (0, 2)$).
