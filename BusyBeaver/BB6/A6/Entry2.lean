/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.BB6.A6.Defs
meta import BusyBeaver.WordRLE
meta import BusyBeaver.ElabRLE
meta import BusyBeaver.BB6.A6.Defs

/-!
# Entry Phase 2 for BB6 `A6`: `C(3)` to `C(5)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry2%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    34892 1500 608073755892 (entryMilestone 3) (entryMilestone 5)
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (3 : ℕ))))
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (5 : ℕ))))

/-- Kernel-verified RLE derivation from `C(3)` to `C(5)` in `608,073,755,892` steps
(`34,892` accelerated RLE steps). -/
theorem entry_phase2 :
    EntryReaches stepEntry 608073755892 (entryMilestone 3) (entryMilestone 5) :=
  prove_entry2%

end BusyBeaver.BB6.A6

end
