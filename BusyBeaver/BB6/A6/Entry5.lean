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
# Entry Phase 5 for BB6 `A6`: `C(7)` to `C(8)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry5%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    28198 1500 304037297274 (entryMilestone 7) (entryMilestone 8)
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (7 : ℕ))))
    (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (8 : ℕ))))

/-- Kernel-verified RLE derivation from `C(7)` to `C(8)` in `304,037,297,274` steps
(`28,198` accelerated RLE steps). -/
theorem entry_phase5 :
    EntryReaches stepEntry 304037297274 (entryMilestone 7) (entryMilestone 8) :=
  prove_entry5%

end BusyBeaver.BB6.A6

end
