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
# Entry Phase 1 for BB6 `A6`: `C(0)` to `C(3)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry1%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    29298 1500 912109735278 (entryMilestone 0) (entryMilestone 3)
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (0 : ℕ))))
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (3 : ℕ))))

/-- Kernel-verified RLE derivation from `C(0)` to `C(3)` in `912,109,735,278` steps
(`29,298` accelerated RLE steps). -/
theorem entry_phase1 :
    EntryReaches stepEntry 912109735278 (entryMilestone 0) (entryMilestone 3) :=
  prove_entry1%

end BusyBeaver.BB6.A6

end
