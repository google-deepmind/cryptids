# A6 nonhalting proof (reflective certificate)

The machine

```text
1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---
```

is proved nonhalting from blank tape in Cryptids' shared execution model:

```lean
BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.is_not_halt :
  BusyBeaver.IsNotHalt
    BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.target
```

The public machine module is
[`M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.lean`](../../BusyBeaver/BB6/M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.lean).
The [self-contained proof](PROOF.md) gives the exact tape family and the
entry, transfer, return, and infinite-run arguments. A6 is a local label;
the complete transition string identifies the machine.

## Proof structure and reflective infrastructure

Fix `N = 791761176`. A compressed RLE execution reaches `C(8)` from `init []`
at the exact literal step `752265440525431967` (passing `C(0)` at step
`752263008230408399`). For every `k : ℕ`, the machine then reaches `C(k+9)`
from `C(k+8)` in `304037417082 + 119808 * k > 0` steps. Positive return times
establish `IsNotHalt target` directly via `IsNotHalt.of_reachesPlus_invariant`.

Instead of relying on external code generation or an intermediate integer-tape
model, the proof uses Cryptids' reusable machine-polymorphic reflective RLE
framework directly over `BusyBeaver.Cfg Γ Λ` (`ListBlank` half-tapes):

- **[`BusyBeaver/WordRLE.lean`](../../BusyBeaver/WordRLE.lean)** — Strict CBV
  accumulators (`withNat`, `withBool`), binary `NatTrie` lookup and bulk
  verification (`NatTrie.checkAll_sound`), finite and composite word-exit
  zippers (`runWordExit_sound`, `sweepWord_sound`, `runCompositeExit_sound`),
  and concrete RLE replay (`EntryReaches.sound`).
- **[`BusyBeaver/AffRLE.lean`](../../BusyBeaver/AffRLE.lean)** — Symbolic
  affine exponents `a * k + b` (`AffNat`), bivariate loop exponents
  `a * k + b + c * j` (`Aff2Nat`), verified countdown-cycle soundness
  (`verifyCycle_sound`), balanced `BTree AffOp` symbolic replay
  (`verifyReturnCert_sound`), and non-halting closure (`isNotHalt_of_family`).
- **[`BusyBeaver/ElabRLE.lean`](../../BusyBeaver/ElabRLE.lean)** — Pure-Lean
  elaboration-time cycle-discovering certificate synthesis
  (`discoverReturnCert`) and sliced `mkAuxTheorem` kernel proof drivers
  (`proveEntryPhase`, `proveCheckAll`, `proveAffReplay`).

The A6 specialization in [`BusyBeaver/BB6/A6/`](../../BusyBeaver/BB6/A6/)
contains no generated files and no external Python scripts:

- **[`Defs.lean`](../../BusyBeaver/BB6/A6/Defs.lean)** — Machine definition,
  2-bit base-word exit table (`fastExit2_sound`), quadratic counter transfers
  (`transferB_batch`, `transferD_batch`), Entry step soundness
  (`stepEntry_sound`), and milestone specifications (`entryMilestone`,
  `initReturnCfg`, `returnTarget`).
- **[`Cert.lean`](../../BusyBeaver/BB6/A6/Cert.lean)** — Elaboration-time
  synthesis of A6's 414-word composite vocabulary, 462-entry composite exit
  trie, 202-operation `BTree AffOp` (9,844 affine sweeps + 67 countdown
  cycles), and post-return configuration `a6FinalCfg`.
- **[`Entry0.lean`](../../BusyBeaver/BB6/A6/Entry0.lean) ..
  [`Entry5.lean`](../../BusyBeaver/BB6/A6/Entry5.lean)** — Six parallel
  kernel-checked Entry milestone derivations (`init [] → C(0) → C(3) → C(5)
  → C(6) → C(7) → C(8)`, 166,491 RLE steps total).
- **[`ReturnExits.lean`](../../BusyBeaver/BB6/A6/ReturnExits.lean) &
  [`ReturnReplay.lean`](../../BusyBeaver/BB6/A6/ReturnReplay.lean)** — Parallel
  kernel verification of all 462 composite exits (`a6_exits_ok`) and the
  symbolic affine return tree (`a6_replay_ok`).

All evaluations run inside the trusted Lean 4 kernel (`Eq.refl true` via
`mkAuxTheorem` and `decide`), with zero `native_decide` and only standard
axioms (`propext`, `Classical.choice`, `Quot.sound`).

## Build and verify

Use this repository's pinned Lean toolchain and fetch its Mathlib cache:

```sh
lake exe cache get
lake build BusyBeaver.BB6.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH
lake env lean artifacts/a6/Audit.lean
```

On Linux with Bubblewrap installed, the focused independent specification
check is:

```sh
lake comparator --config comparator/a6.json
```

The result is also registered in `comparator/busy_beaver.json`, and the
library root imports its machine module.

## Provenance and AI assistance

The machine was investigated from the community's BB6 holdout snapshots.
The mathematical invariant and initial certificate were developed with AI
assistance (including GPT-6.1 Sol and GPT-6.1 Terra), and subsequently
refactored into Cryptids' pure-Lean reflective RLE and affine-return engine.
No priority or community-status update is implied by the formal statement alone.

Software is Apache-2.0 and prose is CC-BY-4.0 under the repository's licenses.
