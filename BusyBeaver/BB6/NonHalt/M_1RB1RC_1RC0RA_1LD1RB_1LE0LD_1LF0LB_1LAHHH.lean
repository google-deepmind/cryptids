/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Calculi.WordCalculusH
public import BusyBeaver.Calculi.WordCalculusI

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
open WordCalculus Word WordCanonBR WordCanonBR.BRIncs WordCanonBR.Choice
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
local notation "WordList" => List Word

def loc_z29 : WordList := [V,V,V,K,K,V,V,Q,V,Q,Q,V,V,V,V,V,Q,K,Q,Q,Q,Q,K,Q,Q,Q]

def loc_z2a : List (List Choice) := [
  [CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,CT,CP1,CT,CT,CT,CT,CT,CP0,CS11,CP1,CP0,CP1,CP0],
  [CT, (COC1 0), CSP1, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CP1, CP1, CP1, CP1, CP0, CS10, CS01, CP0, 
      CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, 
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CP0, CT, CP1, CT, CT, CP0, CS10, CP0, CS00, CS00, CS00, CS11, CP1, CP1, CP1, CP0, CS10, 
      CP0, CS00, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), 
      CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS10, CS10, 
      CS11, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS11, CT, CT, CP0, CS10, CS11, CP1, 
      CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP0, CP1, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, 
      (COC0 0), CSP0, CS10, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      (COC1 0), CSP1, CP1, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CP1, 
      CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CP1, CT, CT, CP0, CS10, CS11, 
      CP0, CS10, CS11, CP1, CP0, CS10, CS00, CS10, CS10, CS11, CP1, CP1, CP1, CP1, CP0, CS10, 
      CS01, CP1, CP1, CP0, CS10, CS00, CP1, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), 
      CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, CP1, CT, CP1, CT, CT, CP0, CS11, CP1, CT, CT, CT, CT, CT, CP0, CT, CT, CT, 
      CP0, CT, CT, CP1, CT, CT, CP0, CS11, CP0, CS11, CP0, CS11, CP0, CS11, CP1, CP0, CS10, 
      CS00, CS10, CP0, CP0, CS00, CS10, CS01, CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, 
      CP1, CP0, CP0, CS00, CS01, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, 
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, 
      (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CP0, CS11, CT, (COC0 0), CSP0, CP0, CT, CT, CT, 
      CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CS10, CT, CP1, CT, CT, CP0, CS10, 
      CS10, CS00, CP1, CP1, CP0, CS10, CS00, CS10, CS10, CP0, CS00, CS10, CS00, CS00, CS10, 
      CP1, CP0, CS10, CP0, CS00, CS00, CS00, CS00, CS10, CS10, CS00, CS10, CS00, CP0, CS01, 
      CP1, CP1, CP1, CP0, CP0, CS00, CP0, CS01, CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, 
      CP1, CP0, CS10, CP0, CS00, CS11, CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), CSP1, 
      (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP1, (COC1 0), 
      CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      CT, CT, CT, CT, (COC0 0), CSP1, CP0, CT, CT, CT, CP0, CP1, (COC0 0), CSP0, CP0, CS00, 
      CS01, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS10, CS00, CS10, CS11, (COC0 2), CSP0, CT, CT, 
      CT, CT, (COC0 0), (CSC1 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, 
      (COC0 0), CSP1, (COC1 0), CSP0, CS11, CT, CP0, CT, CT, CP0, CS11, CP0, CS11, CP1, CP0, 
      CP1, CP1, CP1, CP0, CS11, CP1, CP1, CP1, CP1, CP1, CP0, CP1, CP1, CP1, CP1, CP1, CP1, 
      CP1, CP0, CS10, CP1, CP1, CP1, CP0, CS10, CS00, CS01, CP1, CP0, CP1, CP1, CP1, CP1, CP1, 
      CP0, CS10, CP1, CP1, CP1, CP0, CP1, CP0, CS10, CS11, CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, 
      (COC0 0), CSP0, CS10, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      (COC1 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, 
      CS11, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      (COC1 0), CSP0, (CEC 0), (CSC0 0), CSP1, CT, CP0, CS11, CP0, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, 
      CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP1, CT, CT, CT, CT, CP0, CS10, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, 
      CT, CT, CT, CP1, CT, CP0, CT, CT, CP0, CS10, CP0, CS00, CP1, CP0, CS11, CP1, CP0, CS11, 
      CP1, CP0, CS11, CP1, CP1, CP0, CP0, CS01, CP0, CS10, CS10, CS10, CP0, CS00, CP1, CP0, 
      CS10, CP0, CS00, CS00, CS01, CP0, CS10, CP1, CP0, CP0, CS00, CS00, CS11, CP1, CP0, CS10, 
      CS00, CP0, CS01, CP0, CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP1, CP1, CP1, 
      CP1, CP0, CS10, CS01, CP1, CP1, CP1, CP0, CP0, CS00, CP0, CS01, CP1, CP1, CP1, CP1, CP1, 
      CP0, CS10, CS01, CP1, CP1, CP0, CS10, CS00, CP1, CP0, CS10, CS11, CP0, CS10, CS11, CP1, 
      CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), (CSC0 0), CSP1, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP1, CT, 
      CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CP1, (COC1 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP0, CS10, (CEC 0), CSP1, CT, 
      CT, (COC0 0), CSP0, CS10, CS01, CT, CT, (COC0 1), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CP0, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP0, CT, 
      CT, CT, CT, CT, CT, CP0, CT, CT, CT, CP0, CT, CT, CP1, CT, CP1, CT, CT, CP0, CS10, CS10, 
      CP1, CP0, CS11, CP0, CS11, CP1, CP0, CS10, CP1, CP0, CP0, CS00, CP0, CP1, CP0, CS10, 
      CS10, CS00, CS00, CS00, CS00, CS01, CP1, CP1, CP0, CS10, CP1, CP0, CS11, CP1, CP1, CP1, 
      CP1, CP1, CP0, CS11, CP1, CP0, CS10, CS01, CP0, CS10, CS01, CP0, CP1, CP1, CP0, CS11, 
      CP0, CS10, CP0, CP0, CS00, CS10, CP1, CP0, CS10, CP1, CP1, CP0, CS10, CS00, CP1, CP1, 
      CP0, CP0, CS00, CS00, CS00, CS11, CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP1, 
      CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP0, CS10, CS00, CS01, CP1, CP0, CP1, CP1, CP1, 
      CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP0, CP0, CS00, CS01, CP0, CS10, CS11, CP0, CS10, 
      CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CP0, CT, CT, 
      CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, 
      CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, 
      (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, 
      CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, 
      (COC0 0), CSP0, CT, CP0, CT, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CP1, CT, (COC0 0), 
      CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP1, 
      CP0, CS10, CS00, CS10, CS00, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, 
      CT, (COC0 0), CSP1, CT, CT, CP0, CT, CP0, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, 
      (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, CP0, CT, CT, CT, (COC0 0), CSP0, 
      CS10, CS00, CS11, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP1, CT, CT, CT, CT, CP0, CS10, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, 
      CT, CT, CT, CT, (COC0 0), CSP0, CS10, CT, CP1, CT, CP0, CT, CT, CP0, CS11, CP0, CS11, 
      CP0, CS11, CP1, CP0, CS11, CP1, CP0, CS10, CP1, CP1, CP1, CP1, CP0, CS10, CS01, CP1, CP0, 
      CP0, CP0, CS00, CP0, CS00, CS00, CP0, CS00, CS00, CS10, CS00, CS10, CP0, CP0, CS00, CS10, 
      CS00, CS10, CS10, CS00, CS10, CS10, CS10, CS00, CP1, CP1, CP0, CS10, CS01, CP0, CP0, 
      CS01, CP1, CP1, CP0, CP0, CS01, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP0, CP1, CP0, CS10, 
      CP1, CP1, CP1, CP1, CP1, CP0, CS10, CS01, CP1, CP0, CP0, CP0, CP1, CP0, CP1, CP0, CP0, 
      CP1, CP0, CP0, CS00, CS00, CP0, CP1, CP0, CS10, CP1, CP0, CP0, CS00, CS00, CP1, CP1, CP1, 
      CP0, CS10, CS01, CP0, CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP1, CP1, CP1, 
      CP1, CP0, CS10, CS01, CP1, CP1, CP1, CP0, CP0, CS00, CP0, CS01, CP1, CP1, CP1, CP1, CP1, 
      CP0, CS10, CP1, CP1, CP1, CP0, CS10, CP0, CS00, CS11, CP0, CS10, CS01, CP0, CS10, CS11, 
      CP1, CP0]
]

def loc_z2b : WordList := [V, V, V, K, V, Q, V, K, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V, 
    V, V, V, V, V, V, V, V, V, V, V, V, K, Q, V, V, Q, V, V, V, V, K, Q, V, V, Q, V, V, V, V, 
    V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, 
    V, V, V, V, V, V, V, V, V, V, V, V, V, K, V, Q, V, V, V, V, V, V, V, K, Q, V, V, V, V, V, 
    V, V, V, K, V, V, V, V, V, K, V, Q, V, V, V, V, V, K, V, V, V, V, V, V, V, K, V, V, Q, V, 
    V, K, V, V, V, V, K, V, V, V, V, V, V, V, K, V, Q, V, V, V, V, V, V, K, V, V, V, V, K, Q, 
    V, V, Q, V, V, V, V, V, K, V, Q, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, 
    V, V, K, V, V, V, V, V, V, K, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, 
    V, K, Q, V, V, V, K, V, V, K, V, V, Q, V, V, V, V, K, V, Q, V, V, K, V, V, K, V, Q, V, Q, 
    V, V, V, V, K, V, V, V, V, Q, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, 
    V, V, V, K, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, K, 
    V, Q, V, V, K, V, V, V, K, V, V, V, K, V, V, Q, K, Q, K, V, V, K, V, V, K, V, V, V, V, V, 
    V, K, V, V, V, V, V, V, V, V, V, K, V, Q, V, V, K, V, Q, V, K, V, V, V, V, V, V, V, V, K, 
    V, Q, K, Q, V, V, V, V, V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, Q, V, V, V, V, 
    V, V, V, K, V, V, V, V, V, K, V, Q, V, V, V, V, V, V, V, Q, V, Q, V, Q, V, V, Q, V, V, Q, 
    V, V, V, V, V, Q, K, V, V, V, V, K, V, K, K, V, K, K, Q, K, Q, V, V, K, Q, K, Q, Q, K, Q, 
    Q, Q, K, V, V, V, Q, K, V, V, K, V, V, V, V, K, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, 
    V, V, V, Q, K, V, V, V, V, V, V, V, V, V, V, V, V, K, K, V, V, V, Q, V, V, V, K, K, V, V, 
    V, V, Q, K, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, Q, K, V, V, V, V, V, K, V, K, 
    V, V, V, V, V, V, Q, V, V, V, V, Q, V, K, Q, V, Q, K, V, Q, Q, V, V]

def z2c_low : WordList := [Q, K, K, K, Q, Q, Q, Q, K, Q, Q, K, Q, Q, Q, Q, K, K, Q, Q, Q, K, Q, 
    K, K, Q, K, Q, K, Q, K, K, Q, K, K, K, Q, Q, K, Q, Q, K, Q, K, Q, K, K, Q, Q, K, Q, Q, K, 
    Q, K, K, K, Q, K, Q, Q, Q, Q, Q, K, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, K, 
    Q, Q, K, K, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, K, K, K, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, 
    Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, 
    Q, Q, K, K, Q, K, K, Q, Q, K, K, K, Q, Q, Q, K, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, 
    Q, Q, Q, Q, K, K, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, 
    K, K, K, K, Q, Q, K, Q, Q, Q, Q, Q, K, Q, Q, K, K, Q, K, K, K, Q, K, Q, Q, Q, K, K, Q, Q, 
    Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, K, Q, K, K, K, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, 
    Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, K, K, 
    K, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q]

def z2c_top : WordList := [Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,K]

def loc_z2c : WordList := z2c_low ++ z2c_top

theorem loc_z2d :
    CanonRounds (evalWords loc_z29 default)
        (evalWords (prefix33Words ++ (loc_z2b ++ (loc_z2c ++ tail8Words))) default) :=
  evalCanonRounds_sound loc_z2a loc_z29
      (prefix33Words ++ (loc_z2b ++ (loc_z2c ++ tail8Words)))
      (by decide +kernel)

theorem loc_z2e :
    BGood (loc_z2b ++ (loc_z2c ++ tail8Words)) := by
  apply bGood_of_check loc_z2b z2c_low z2c_top <;> decide +kernel

def zCk0 : CCfg := ⟨E,0,[],[]⟩

def zCk1 : CCfg := ⟨C,1,
    [0, 1],
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 
      0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 
      1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 
      1, 0, 1, 0, 1]⟩

def zCk2 : CCfg := ⟨E,0,
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 
      1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 
      0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 
      1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]⟩

def zCk3 : CCfg := ⟨E,0,
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 
      0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 
      0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]⟩

def zCk4 : CCfg := ⟨C,1,
    [0, 1],
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 
      0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 1, 
      0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 
      1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 
      1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1]⟩

private theorem zCk_step1 : (c_to_cfg zCk0) [canon_tm]⊢⁺ (c_to_cfg zCk1) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk0 8179 = some zCk1)

private theorem zCk_step2 : (c_to_cfg zCk1) [canon_tm]⊢⁺ (c_to_cfg zCk2) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk1 10000 = some zCk2)

private theorem zCk_step3 : (c_to_cfg zCk2) [canon_tm]⊢⁺ (c_to_cfg zCk3) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk2 10000 = some zCk3)

private theorem zCk_step4 : (c_to_cfg zCk3) [canon_tm]⊢⁺ (c_to_cfg zCk4) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk3 10405 = some zCk4)

theorem z0E : (c_to_cfg zCk0) [canon_tm]⊢⁺ (cfgCanon (evalWords loc_z29 default)) := by
  have h_all := stepPlus_trans_canon zCk_step1
    (stepPlus_trans_canon zCk_step2
    (stepPlus_trans_canon zCk_step3 zCk_step4))
  have heq : c_to_cfg zCk4 = cfgCanon (evalWords loc_z29 default) := by
    simp only [c_to_cfg, C, WordCanonBR.C, zCk4, zCf, cfgCanon, zCL, cfgLeft, lh, w_base, w_word,
        w_rest, loc_z29, evalWords, t, d0, d1, one, List.cons_append, List.nil_append,
        append_cons, append_nil, z00, zero_cons_default_canon,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  rwa [heq] at h_all

theorem loc_z2s (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0) N = 
        some (cfgCanon (evalWords (prefix33Words ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E with ⟨k1,_,hk1⟩
    rcases stepStar_of_canonRounds loc_z2d with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,loc_z2b ++ (loc_z2c ++ tail8Words),
      multiStep_trans_canon canon_tm _ _ _ k1 k2 hk1 hk2,loc_z2e⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases bGood_progress h_good with ⟨w',hStep,h_good'⟩
    rcases stepPlus_of_bStep hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      multiStep_trans_canon canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap : Fin 6 -> Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 3
  | 3 => 4
  | 4 => 0
  | 5 => 5

def zCfgMap (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap,c.tape⟩

theorem zStepMap (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap c) = (step canon_tm c).map zCfgMap := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

theorem zMultiStepMap (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap c) n = (multiStep canon_tm c n).map zCfgMap := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ_canon,multiStep_succ_canon,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap c'



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases loc_z2s (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap (c_to_cfg zCk0) = init [] := rfl
  have h_map := zMultiStepMap (c_to_cfg zCk0) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := multiStep_add_Intermediate h_map
  rw [multiStep_succ_canon,hn] at h_some
  exact h_some

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end BusyBeaver.M_1RB1RC_1RC0RA_1LD1RB_1LE0LD_1LF0LB_1LAHHH
