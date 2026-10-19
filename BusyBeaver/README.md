# Busy Beaver Holdouts (`BusyBeaver/`)

This library contains formal Lean 4 specifications and kernel-verified behavioral proofs for Busy Beaver 6 (`BB(6)`) holdouts, connected to `ConjectureMachines.Machine` via [`BusyBeaver/Bridge.lean`](./Bridge.lean).

## Cryptids and Collatz-like Reductions in `BB(6)`

Broadly speaking, [cryptids](https://wiki.bbchallenge.org/wiki/Cryptids) are Turing machines whose halting problem corresponds to a known open mathematical problem (such as the machines for Goldbach's conjecture, ZF consistency, and the Riemann Hypothesis in [`Cryptids/`](../Cryptids/README.md)). In the context of `BB(6)`, however, the term is commonly used more broadly for holdout machines whose dynamics exhibit a **Collatz-like structure** (piecewise affine or modular transitions on integer counters), rather than encoding the classical Collatz conjecture itself or a named open problem.

Accordingly, for these machines we look for and formalize **Collatz-like reductions** (`HasCollatzReduction` and `IsValidAcceleration`). Some well-known `BB(6)` cryptids, such as [Antihydra](https://wiki.bbchallenge.org/wiki/Antihydra), are widely considered genuinely hard and have attracted dedicated mathematical research. At the same time, other machines with Collatz-like reductions have subsequently been resolved—either through automated deciders or via number-theoretic methods such as Baker's theorem on linear forms in logarithms (e.g., [`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---)). It is therefore reasonable to expect that some of the machines in this directory will eventually be resolved as halting (`IsHalt`) or non-halting (`IsNotHalt`) over time, with or without the reductions provided here.

## Behavioral Predicates ([`Defs.lean`](./Defs.lean))

All proofs in `BusyBeaver/` target machine-checked behavioral predicates over the Post-Turing execution model `BusyBeaver.Machine Γ Λ` starting from the all-blank tape (`BusyBeaver.init []`), capturing both **Level A** (explicit closed `TapePatternSet` invariants) and **Level B** (explicit Collatz-like arithmetic accelerations):

| Predicate | Meaning |
| :--- | :--- |
| `IsHalt M` | `M` eventually reaches a halting configuration (`(step M cfg).isNone`) from `init []`. |
| `IsNotHalt M` (`IsDoesNotHalt M`) | Every configuration reachable from `init []` has a well-defined successor (`(step M cfg).isSome`). |
| `IsClosedPatternSet M ps` | **Level A**: `M`'s blank-tape trajectory enters the explicit `TapePatternSet` `ps`, and every member configuration advances (`ReachesPlus`) either to another member of `ps` or to a halting configuration. |
| `HasCollatzReduction M` | `∃ ps, IsClosedPatternSet M ps`. |
| `IsValidAcceleration M start encode next` | **Level B**: `encode : S → Cfg Γ Λ` and `next : S → Option S` form a certified Collatz-like acceleration of `M` from `start : S` (`init []` reaches `encode start`, `next s = some s'` implies `ReachesPlus M (encode s) (encode s')`, and `next s = none` implies halting from `encode s`), yielding `IsHalt M ↔ CollatzHalts next start`. |

## Foundational Lemmas ([`Basic.lean`](./Basic.lean))

[`BusyBeaver/Basic.lean`](./Basic.lean) provides clean-room multi-step and reachability lemmas (`multiStep`, `ReachesIn`, `ReachesStar`, `ReachesPlus` with `Trans` instances), closed-invariant non-halting theorems (`NeverHaltsFrom.of_reachesPlus_invariant`, `IsNotHalt.of_reachesPlus_invariant`), certified Collatz acceleration halting equivalence (`IsValidAcceleration.isHalt_iff`, `IsValidAcceleration.of_step`), finite block repetition (`l ^ n`) and `ListBlank` identities, standard 6-state labels (`BusyBeaver.SixState.A..F`), directed-head (`Cfg.headRight` / `Cfg.headLeft`) step transitions, scoped directed-head and reachability notations (`l {{q}}> r`, `l <{{q}} r`, `s <+ l`, `l +> s`, `c₁ [M]⊢⁺ c₂`, ...), and concrete execution/halting tactics (`bb_steps`, `bb_halt`).

## Certificate Checker ([`Cert.lean`](./Cert.lean))

[`BusyBeaver/Cert.lean`](./Cert.lean) provides a small verified certificate checker (symbolic configurations over block-repetition variables, validated rewrite rules, and a `Bool`-valued proof-script interpreter whose success is sound for `ReachesStar` / `ReachesPlus` and hub-pattern membership). It is used by the machines whose closure proofs are produced as certificates (e.g. `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` and `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`).

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

## Formalized Machines

Each machine module exposes both **Level A** (`ps`, `is_closed_pattern_set`, `has_collatz_reduction`) and **Level B** (`State`, `start`, `encode`, `next`, `is_valid_acceleration`, `isHalt_iff_acceleration`):

| Machine (`bbchallenge` RLE) | States | Symbols | Proved Properties | Wiki / Notes | Lean 4 Proof |
| :--- | :--- | :--- | :--- | :--- | :--- |
| `1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LB_1LC0RE_1LA1LD_0LC---_0RB0RF_1RE1RB) | [`M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean`](./Machines/M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.lean) |
| `1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_0LC0RF_1RD1LC_0RA1LE_---0LD_1LF1LA) | [`M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA.lean`](./Machines/M_1RB0LC_0LC0RF_1RD1LC_0RA1LE_HHH0LD_1LF1LA.lean) |
| `1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_---1RA) | [`M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean`](./Machines/M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.lean) |
| `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE) | [`M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE.lean`](./Machines/M_1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_HHH0LE.lean) |
| `1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA) (BMO base-3) | [`M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.lean`](./Machines/M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.lean) |
| `1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_---0RE) (BMO5) | [`M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.lean`](./Machines/M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.lean) |
| `1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_---1RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [busycoq `CubicCapLoop_v2.v` (`TM1`)](https://github.com/ccz181078/busycoq/blob/BB6/verify/CubicCapLoop_v2.v) (**resolved non-halting**) | [`M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE.lean`](./Machines/M_1RB0LD_1LC1RA_1RA1LC_1LE1LA_0RF1LD_HHH1RE.lean) |
| `1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_---1RE) | [`M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean`](./Machines/M_1RB0LD_1RC1RA_1LD0RB_1LE1LA_1RF0RC_HHH1RE.lean) |
| `1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RB---) | [`M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean`](./Machines/M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.lean) |
| `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean`](./Machines/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.lean) |
| `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean`](./Machines/M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC.lean) |
| `1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RC---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean`](./Machines/M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.lean) |
| `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean`](./Machines/M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE.lean) |
| `1RB0LF_1LC1RA_0RE0RD_---1LE_1LF1RC_1LC1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean`](./Machines/M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA.lean) |
| `1RB0LF_1RC1RA_0RD0RB_1LE---_0LA1LE_1RD1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean`](./Machines/M_1RB0LF_1RC1RA_0RD0RB_1LEHHH_0LA1LE_1RD1LA.lean) |
| `1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_---1LB) | [`M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean`](./Machines/M_1RB0RB_1LB0LC_1RD1LC_1RE0RA_0RF1RA_HHH1LB.lean) |
| `1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_---1LC) (*Space Needle* family) | [`M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC.lean`](./Machines/M_1RB0RB_1LC1RE_1LF0LD_1RA1LD_1RC1RB_HHH1LC.lean) |
| `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean`](./Machines/M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD.lean) |
| `1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_---0RA) (*Lucy's Moonlight*) | [`M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA.lean`](./Machines/M_1RB0RD_0RC1RE_1RD0LA_1LE1LC_1RF0LD_HHH0RA.lean) |
| `1RB0RE_1LC0RA_1RF0RD_---1LE_0LB1LE_1LE1RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean`](./Machines/M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.lean) |
| `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB) | [`M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB.lean`](./Machines/M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB.lean) |
| `1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB0RF_1RC1RF_1LD0LE_---1LC_1RA1LE_1LC1RB) (Parity-Collatz) | [`M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB.lean`](./Machines/M_1RB0RF_1RC1RF_1LD0LE_HHH1LC_1RA1LE_1LC1RB.lean) |
| `1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE) (*The Sheep Machine*) | [`M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean`](./Machines/M_1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_HHH1LE.lean) |
| `1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_---0LD) (*Space Needle* / BMO6) | [`M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean`](./Machines/M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.lean) |
| `1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_---0LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean`](./Machines/M_1RB1LA_1LC0RE_1LF1LD_1RE0LC_1LB1RA_HHH0LA.lean) |
| `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---) (*Pomme* / Baker machine; **resolved non-halting**) | [`M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH.lean`](./Machines/M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH.lean) |
| `1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_---0RC) | [`M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean`](./Machines/M_1RB1LC_1LC1RD_1LA0LB_0RB1RE_1RF0RA_HHH0RC.lean) |
| `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE) (redirects to BMO5) | [`M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.lean`](./Machines/M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE.lean) |
| `1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean`](./Machines/M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.lean) |
| `1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_---1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean`](./Machines/M_1RB1LD_1RC0RA_1LA1RE_0LA0LB_0RB1RF_HHH1RD.lean) |
| `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC) | [`M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC.lean`](./Machines/M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC.lean) |
| `1RB1LE_1LB1LC_1RD0LE_---0RB_1RF1LA_0RA0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`Cryptids`)](https://wiki.bbchallenge.org/wiki/Cryptids) | [`M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean`](./Machines/M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.lean) |
| `1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_---1RC) (TMBR Aug 2025) | [`M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean`](./Machines/M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.lean) |
| `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean`](./Machines/M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE.lean) |
| `1RB1LF_0RC1RD_1LA1LD_1LE0RA_---1LC_0LA1LA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean`](./Machines/M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.lean) |
| `1RB1LF_1RC1RF_0LD1RE_---1LC_0RB1RE_1LA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean`](./Machines/M_1RB1LF_1RC1RF_0LD1RE_HHH1LC_0RB1RE_1LA0LE.lean) |
| `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean`](./Machines/M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC.lean) |
| `1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_---0RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`Antihydra`)](https://wiki.bbchallenge.org/wiki/Antihydra) (*Antihydra*) | [`M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean`](./Machines/M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean) |
| `1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_---0LC) (*Counter6*) | [`M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean`](./Machines/M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.lean) |
| `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean`](./Machines/M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE.lean) |
| `1RB1RC_1LC1LC_1RE0LD_1LB1RF_---1RA_0RD1RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean`](./Machines/M_1RB1RC_1LC1LC_1RE0LD_1LB1RF_HHH1RA_0RD1RD.lean) |
| `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA) | [`M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA.lean`](./Machines/M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA.lean) |
| `1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean`](./Machines/M_1RB1RD_0LC1RA_0RA1LC_1RA1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean`](./Machines/M_1RB1RD_0LC1RA_1LA1LC_1RA1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_---0RE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean`](./Machines/M_1RB1RD_0LC1RA_1RA1LC_0RB1LE_1RF0LD_HHH0RE.lean) |
| `1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_---0RC` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki (`User:RobinCodes/Next_Steps`)](https://wiki.bbchallenge.org/wiki/User:RobinCodes/Next_Steps) | [`M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.lean`](./Machines/M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.lean) |
| `1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_0RD1LB_---1RC_1LF1RE_0LB0LE) (BMO1) | [`M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE.lean`](./Machines/M_1RB1RE_1LC0RA_0RD1LB_HHH1RC_1LF1RE_0LB0LE.lean) |
| `1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_---0LE) | [`M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean`](./Machines/M_1RB1RE_1LC0RA_1RD0LB_1LB1RC_1LF0RD_HHH0LE.lean) |
| `1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RE_1LC1LD_---1LA_1LB1LE_0RF0RA_1LD1RF) (*HydraShift6*) | [`M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF.lean`](./Machines/M_1RB1RE_1LC1LD_HHH1LA_1LB1LE_0RF0RA_1LD1RF.lean) |
| `1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RF_0LC0RF_1RD1LC_---0LE_0RC1LF_1RA0LE) | [`M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE.lean`](./Machines/M_1RB1RF_0LC0RF_1RD1LC_HHH0LE_0RC1LF_1RA0LE.lean) |
| `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | [Wiki](https://wiki.bbchallenge.org/wiki/1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD) | [`M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean`](./Machines/M_1RB1RF_1LC1LF_0RE1LD_0LB1LD_HHH1RC_1RA0RD.lean) |
| `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean`](./Machines/M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB.lean) |
| `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD` | `6` | `2` | `IsClosedPatternSet`, `HasCollatzReduction`, `IsValidAcceleration` | — | [`M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean`](./Machines/M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD.lean) |

## Building and Verifying

Build the `BusyBeaver` and `BusyBeaverChallenge` targets and audit with [`leanprover/comparator`](../comparator/README.md):

```bash
lake exe cache get
lake build BusyBeaver BusyBeaverChallenge
lake comparator --config comparator/busy_beaver.json
```

## Acknowledgements

We thank the [Formal Conjectures](https://github.com/google-deepmind/formal-conjectures) project for the Busy Beaver Post-Turing machine model (`BusyBeaver.Machine`), the Busy Beaver Challenge community, and `int-y1` (`BusyLean`) for pioneering Lean 4 Busy Beaver holdout formalizations and inspiring the directed-head configuration style (`Cfg.headRight` / `Cfg.headLeft`).
