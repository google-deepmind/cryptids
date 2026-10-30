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
# Entry Phase 3 for BB6 `A6`: `C(5)` to `C(6)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry3%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    22054 1500 304037057658 (entryMilestone 5) (entryMilestone 6)
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (5 : ℕ))))
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (6 : ℕ))))

/-- Kernel-verified RLE derivation from `C(5)` to `C(6)` in `304,037,057,658` steps
(`22,054` accelerated RLE steps). -/
theorem entry_phase3 :
    EntryReaches stepEntry 304037057658 (entryMilestone 5) (entryMilestone 6) :=
  prove_entry3%

end BusyBeaver.BB6.A6

end
