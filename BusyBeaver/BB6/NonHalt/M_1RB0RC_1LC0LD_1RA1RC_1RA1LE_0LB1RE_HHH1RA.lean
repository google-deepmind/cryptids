/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.CtlCertificate

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

def ctlLeftDfaTable : List (Fin 1) := [0, 0]

def ctlLeftDfa (p : Fin 1) (a : Fin 2) : Fin 1 :=
  ctlLeftDfaTable.getD (2 * p.val + a.val) 0

def ctlRightDfaTable : List (Fin 3) := [0, 1, 2, 2, 2, 2]

def ctlRightDfa (p : Fin 3) (a : Fin 2) : Fin 3 :=
  ctlRightDfaTable.getD (2 * p.val + a.val) 0

def ctlAcc : List (Fin 1 × Fin 6 × Fin 2 × Fin 3) := [
  (0, 0, 0, 0), (0, 0, 1, 0), (0, 1, 0, 0), (0, 2, 0, 0),
  (0, 2, 0, 1), (0, 2, 1, 0), (0, 2, 1, 1)
]

public section

theorem is_not_halt : IsNotHalt target :=
  CtlCert.ctl_certificate_implies_is_does_not_halt
    target ctlLeftDfa ctlRightDfa ctlAcc (by decide +kernel)

end

end BusyBeaver.M_1RB0RC_1LC0LD_1RA1RC_1RA1LE_0LB1RE_HHH1RA
