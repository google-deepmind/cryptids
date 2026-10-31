/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.BB6.A6.Cert
meta import BusyBeaver.WordRLE
meta import BusyBeaver.AffRLE
meta import BusyBeaver.ElabRLE
meta import BusyBeaver.BB6.A6.Defs
meta import BusyBeaver.BB6.A6.Cert

/-!
# Composite Word-Exit Verification for BB6 `A6`

Verifies all 462 composite word exits in `a6Exits` against `WordRLE.runCompositeExit` via
depth-sliced `mkAuxTheorem` kernel evaluation.
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-- Composite word `0` in `a6Vocab` consists exclusively of blank base words. -/
theorem a6_vocab_blank0 : checkVocabBlank0 a6Vocab = true := by
  decide

local elab "prove_a6_exits%" : term => do
  let pE := Lean.mkApp3 (Lean.mkConst ``checkExitEntry)
    (Lean.toExpr (6 : ℕ)) (Lean.mkConst ``fastExit2) (Lean.mkConst ``a6Vocab)
  ElabRLE.proveCheckAll pE a6Exits 5

/-- Kernel-verified composite exit certificate for all 462 entries of `a6Exits`. -/
theorem a6_exits_ok :
    NatTrie.checkAll (checkExitEntry 6 fastExit2 a6Vocab) 0 1 a6Exits = true :=
  prove_a6_exits%

end BusyBeaver.BB6.A6

end
