/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs.Core
public import BusyBeaver.Defs.Patterns
public import BusyBeaver.Defs.Stack
public import BusyBeaver.Defs.Odometer
public import BusyBeaver.Defs.Transducer
public import BusyBeaver.Defs.WordRun
public import BusyBeaver.Defs.Segmented

/-!
# Busy Beaver Holdout Definitions (`BusyBeaver.Defs`)

Umbrella module re-exporting the canonical Post-Turing machine execution model and behavioral
goal predicates for Busy Beaver holdouts.

## Goal Predicates by Defining Module

- `BusyBeaver.Defs.Core`:
  - `IsHalt` — `M` eventually reaches a halting configuration from the blank tape (`init []`).
  - `IsNotHalt` (`IsDoesNotHalt`) — `M` never halts from the blank tape.
- `BusyBeaver.Defs.Patterns`:
  - `HasCollatzReduction` — `M` is governed by a closed accelerated regular-expression tape
    pattern set.
  - `IsCryptid` — `M` is governed by a compact (length ≤ 16) closed accelerated tape pattern set.
- `BusyBeaver.Defs.Stack`:
  - `HasStackedCollatzReduction` — `M` is governed by a closed accelerated stack-word tape
    pattern set.
  - `HasStackReduction` — `M` is governed by a closed 2nd-order digit-stack system.
- `BusyBeaver.Defs.Odometer`:
  - `HasOdometerReduction` — `M` is governed by a closed mixed-radix odometer-word hub.
- `BusyBeaver.Defs.Transducer`:
  - `HasTransducerReduction` — `M` is governed by a closed bidirectional word-stack transducer.
- `BusyBeaver.Defs.WordRun`:
  - `IsWordRunCryptid` — `M` is governed by a closed invariant-relative word-run stack system.
- `BusyBeaver.Defs.Segmented`:
  - `IsSegmentedCryptid` — `M` is governed by a unifying ≤ 3-region segmented tape schema.
-/
