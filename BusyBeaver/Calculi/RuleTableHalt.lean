/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs

/-!
# Shared Rule-Table Block Indexing and Hex Table Packing (`BusyBeaver.RuleTableHalt`)

Shared infrastructure for compressed `@Bool.rec` rule-table halting proofs:
- Kernel-friendly `Nat` arithmetic normalization lemmas (`nat_add_eq`, `nat_sub_eq`, `nat_mul_eq`).
- `pack256`: reconstructs large 256-bit-chunked hex tables cleanly inside source line limits.
- `entFromBlkF` and `bsel2F`: `@Bool.rec` binary block selector and 64-bit table entry lookup.
-/

@[expose] public section

namespace BusyBeaver.RuleTableHalt

@[scoped simp] theorem nat_add_eq (a b : Nat) : Nat.add a b = a + b := rfl
@[scoped simp] theorem nat_sub_eq (a b : Nat) : Nat.sub a b = a - b := rfl
@[scoped simp] theorem nat_mul_eq (a b : Nat) : Nat.mul a b = a * b := rfl

/-- Reconstructs a `Nat` from big-endian `256`-bit (`64`-hex-digit) chunks. -/
def pack256 (ws : List Nat) (acc : Nat := 0) : Nat :=
  match ws with
  | [] => acc
  | w :: rest =>
    pack256 rest
      (Nat.add w (Nat.mul 0x10000000000000000000000000000000000000000000000000000000000000000 acc))

/-- Extracts the 64-bit entry at index `g % 256` from a 256-entry block `blk`. -/
def ent256F (blk g : Nat) : Nat :=
  Nat.land (Nat.shiftRight blk (Nat.mul 64 (Nat.mod g 256))) 18446744073709551615

/-- Looks up global 64-bit entry `g` from a block selector `blkF : Nat → Nat`. -/
def entFromBlkF (blkF : Nat → Nat) (g : Nat) : Nat :=
  ent256F (blkF (Nat.div g 256)) g

/-- Binary `@Bool.rec` selector between blocks `base` (`b0`) and `base + 1` (`b1`). -/
def bsel2F (base b0 b1 : Nat) (j : Nat) : Nat :=
  @Bool.rec (fun _ => Nat) b1 b0 (Nat.ble j base)

end BusyBeaver.RuleTableHalt
