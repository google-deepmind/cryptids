/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.BB6.A6.Defs
meta import BusyBeaver.WordRLE
meta import BusyBeaver.AffRLE
meta import BusyBeaver.ElabRLE
meta import BusyBeaver.BB6.A6.Defs

/-!
# Elaboration-Time Symbolic Return Certificate Synthesis for BB6 `A6`

Invokes `BusyBeaver.ElabRLE.discoverReturnCert` during elaboration to synthesize `A6`'s
414-word composite vocabulary, 462-entry composite exit trie, 202-operation `BTree AffOp`
(9,844 affine sweeps + 67 countdown cycles), and post-return symbolic configuration `a6FinalCfg`.
-/

@[expose] public section

namespace BusyBeaver.BB6.A6

open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-- Synthesize `(a6Cert, a6FinalCfg)` at elaboration time using the pure-Lean cycle-discovering
symbolic simulator. -/
local elab "synthesize_a6_return_cert%" : term => do
  match ElabRLE.discoverReturnCert 6 fastExit2 [[1], [2], [3], pWord, qWord]
      initReturnCfg returnTarget with
  | some pair => return Lean.toExpr pair
  | none => Lean.throwError "Failed to synthesize A6 symbolic return certificate"

/-- Synthesized symbolic return certificate and final `AffCfg` for `A6`. -/
def a6CertPair : ReturnCert × AffCfg :=
  synthesize_a6_return_cert%

/-- Synthesized `ReturnCert` for `A6`. -/
def a6Cert : ReturnCert := a6CertPair.1

/-- Synthesized 414-word composite vocabulary trie for `A6`. -/
def a6Vocab : NatTrie (BTree ℕ) := a6Cert.vocab

/-- Synthesized 462-entry composite word-exit trie for `A6`. -/
def a6Exits : NatTrie CompExit := a6Cert.exits

/-- Synthesized balanced `BTree AffOp` for `A6`. -/
def a6Ops : BTree AffOp := a6Cert.ops

/-- Post-return symbolic configuration reached after `returnTarget` steps from `initReturnCfg`. -/
def a6FinalCfg : AffCfg := a6CertPair.2

end BusyBeaver.BB6.A6

end
