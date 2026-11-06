/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

def ctlLeftDfaTable : List (Fin 3) := [0, 1, 2, 2, 2, 2]

def ctlLeftDfa (p : Fin 3) (a : Fin 2) : Fin 3 :=
  ctlLeftDfaTable.getD (2 * p.val + a.val) 0

def ctlRightDfaTable : List (Fin 2) := [0, 1, 1, 1]

def ctlRightDfa (p : Fin 2) (a : Fin 2) : Fin 2 :=
  ctlRightDfaTable.getD (2 * p.val + a.val) 0

def ctlAcc : List (Fin 3 × Fin 6 × Fin 2 × Fin 2) := [
  (0, 0, 0, 0), (0, 2, 1, 1), (0, 4, 0, 1), (1, 1, 0, 0)
]

public section

theorem is_not_halt : IsNotHalt target :=
  CtlCert.ctl_certificate_implies_is_does_not_halt
    target ctlLeftDfa ctlRightDfa ctlAcc (by decide +kernel)

end

end BusyBeaver.M_1RB0RC_1LC1RD_1RA1LE_1LA0RD_0LE1RF_1LBHHH
