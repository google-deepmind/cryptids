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
# Entry Phase 4 for BB6 `A6`: `C(6)` to `C(7)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry4%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    25126 1500 304037177466 (entryMilestone 6) (entryMilestone 7)
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (6 : ℕ))))
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (7 : ℕ))))

/-- Kernel-verified RLE derivation from `C(6)` to `C(7)` in `304,037,177,466` steps
(`25,126` accelerated RLE steps). -/
theorem entry_phase4 :
    EntryReaches stepEntry 304037177466 (entryMilestone 6) (entryMilestone 7) :=
  prove_entry4%

end BusyBeaver.BB6.A6

end
