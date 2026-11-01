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
# Entry Phase 0 for BB6 `A6`: Blank Tape to `C(0)`
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE

local elab "prove_entry0%" : term =>
  ElabRLE.proveEntryPhase stepEntry (Lean.mkConst ``stepEntry)
    26923 1500 752263008230408399 ⟨0, false, [], []⟩ (entryMilestone 0)
    none (some (Lean.mkApp (Lean.mkConst ``entryMilestone) (Lean.toExpr (0 : ℕ))))

/-- Kernel-verified RLE derivation from the blank tape to `C(0)` in `752,263,008,230,408,399`
steps (`26,923` accelerated RLE steps). -/
theorem entry_phase0 :
    EntryReaches stepEntry 752263008230408399 ⟨0, false, [], []⟩ (entryMilestone 0) :=
  prove_entry0%

end BusyBeaver.BB6.A6

end
