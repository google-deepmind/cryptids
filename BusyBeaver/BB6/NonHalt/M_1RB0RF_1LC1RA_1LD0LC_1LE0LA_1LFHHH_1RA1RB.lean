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


open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RB


@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

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

def z29_0539 : WordList := [V, V, V, V, V, V, V, V, K, V, Q, V, V, K, V, V, Q, V, V, V, Q, V, 
    V, V, K, V, V, Q, K, V, V, V, Q, Q, Q, V, K, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q, K, K, K, K, 
    K, K, Q]

def z2a_0539 : List (List Choice) := [
  [CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, CT, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CP0, CT, CT, (COC0 0), 
      CSP1, CP1, (COC1 0), CSP0, CS11, CP1, CP0, CS10, CP0, CP1, CP0, CS10, CS10, CS00, CS00, 
      CS10, CP0],
  [CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), 
      CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, 
      (COC0 0), CSP1, CP0, CS10, CS01, (COC0 0), CSP0, CS10, CS01, CP0, CS10, CP0, CP0, CS01, 
      CP0, CS10, CP1, CP0, CS10, CP1, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CP0, CS10, CT, (COC1 1), CSP1, CT, 
      (COC0 0), (CSC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CP0, CP1, CP1, CP0, CS10, CP0, 
      CS00, CS10, CS00, CP0, CP0, CP0, CS01, CP1, CP0, CP0, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), 
      CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP1, (COC1 0), 
      CSP1, CT, CT, (COC0 0), CSP0, CS10, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP1, (COC1 0), CSP0, CP0, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, 
      CT, CP0, CS11, CP1, CP0, CP1, CP0, CS10, CP0, CS01, CP1, CP1, CP1, CP0, CP0, CS00, CS00, 
      CS00, CP0, CS01, CP0, CS10, CS01, CP1, CP0, CS10, CP0, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS10, (CEC 0), CSP0, CT, CP0, CT, (COC1 0), CSP1, (COC1 0), CSP0, CT, CT, 
      CP0, CS10, CP1, CP0, CP0, CS00, CS00, CS10, CS10, CP0, CS00, CS11, CP1, CP0, CS10, CS00, 
      CS01, CP1, CP1, CP1, CP1, CP0, CP0, CS00, CS00, CS00, CP0, CP0, CP0, CP1, CP0, CS10, 
      CS10, CS00, CP0, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, 
      CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS10, CP1, (COC0 0), 
      CSP0, CS11, CT, CT, CP0, CS10, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS10, CS00, CT, CT, 
      CT, CT, (COC0 0), CSP1, (COC1 1), CSP0, CT, CT, CP0, CS10, CS11, CP0, CS11, CP0, CP1, 
      CP1, CP1, CP0, CS10, CP0, CS00, CS10, CS10, CS01, CP0, CP0, CP1, CP0, CS10, CS10, CS01, 
      CP0, CP1, CP1, CP1, CP0, CP0, CS00, CS00, CS00, CP0, CS01, CP0, CS10, CP1, CP0, CS10, 
      CP1, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), 
      CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, 
      CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), CSP1, 
      (COC1 0), (CSC0 0), CSP1, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      CP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CP1, (COC1 0), CSP1, CT, 
      CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS11, CP0, CT, CT, CT, (COC0 0), CSP1, CP0, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CS10, (CEC 0), (CSC0 0), CSP1, CT, (COC0 0), CSP1, 
      CT, CT, CP1, CT, CT, CP0, CS10, CP0, CS00, CP0, CP0, CS00, CS10, CP0, CP0, CS00, CS10, 
      CS01, CP0, CS10, CP0, CS00, CS01, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CS00, CS11, 
      CP1, CP0, CP1, CP0, CS10, CS11, CP0, CS11, CP1, CP1, CP1, CP0, CP0, CS00, CS00, CS00, 
      CP0, CP0, CP0, CS01, CP1, CP0, CP0, CS01, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), 
      CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, 
      CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, 
      (COC0 0), CSP0, CS10, CT, CT, CP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP1, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CT, (COC1 0), CSP0, CS11, 
      CT, (COC0 0), (CSC1 1), CSP1, (COC1 0), CSP0, CS10, CT, CT, CT, CT, (COC0 0), CSP1, CP0, 
      CS10, CS01, CT, CT, CT, CT, CP1, (COC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CS10, 
      CS00, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CP1, CT, CT, CP0, CS10, CP1, 
      CP0, CS10, CS10, CS11, CP0, CS10, CS00, CP1, CP0, CS10, CS10, CS01, CP0, CS10, CP0, CP0, 
      CP1, CP1, CP0, CP1, CP0, CS10, CP1, CP0, CP0, CP0, CS00, CP0, CP0, CP1, CP0, CP1, CP1, 
      CP0, CS10, CS00, CS10, CS10, CS01, CP0, CP0, CP1, CP0, CS10, CS10, CS01, CP0, CP1, CP1, 
      CP1, CP0, CP0, CS00, CS00, CS00, CP0, CS01, CP0, CS10, CS01, CP1, CP0, CS10, CP0, CS01, 
      CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP1, 
      (COC1 0), CSP1, (COC1 0), CSP0, CS11, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CP0, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CP0, CT, (COC1 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), 
      CSP1, CT, (COC0 0), CSP1, CP1, CT, CP0, CT, (COC1 0), CSP1, (COC1 1), CSP1, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CP0, 
      CS11, CP0, CT, CT, CT, (COC0 0), CSP1, CP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS10, 
      (CEC 0), CSP0, CT, CP0, CT, (COC1 0), CSP1, (COC1 0), CSP0, CT, CP0, CT, CT, CP0, CS11, 
      CP0, CP0, CS00, CS00, CS00, CP0, CP0, CS00, CS10, CP0, CP1, CP0, CS10, CS10, CP1, CP1, 
      CP0, CS10, CS00, CS10, CS01, CP0, CP0, CS00, CS00, CS10, CS10, CS10, CS11, CP0, CS10, 
      CS01, CP0, CS10, CS00, CP0, CP1, CP1, CP1, CP0, CP0, CS00, CS01, CP0, CS10, CP0, CS00, 
      CS00, CP0, CP0, CP1, CP0, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CS00, CS01, CP1, 
      CP0, CP1, CP0, CS10, CS11, CP0, CS11, CP1, CP1, CP1, CP0, CP0, CS00, CS00, CS00, CP0, 
      CP0, CP0, CP1, CP0, CS10, CS10, CS00, CP0, CS01, CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, 
      CS11, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CS10, CT, CT, CT, CT, CT, 
      CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CS11, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, (COC1 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CS11, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, 
      (COC0 0), (CSC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP1, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CS10, CS10, CT, 
      (COC1 0), CSP0, CS11, CT, CT, CT, CP1, CT, CT, CT, CP0, CP0, CT, (COC1 0), CSP0, CS10, 
      CP1, CP1, CT, CP0, CT, CP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, (CEC 0), CSP1, (COC1 0), 
      CSP0, CS10, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CP0, CS10, CS00, CT, CT, CT, 
      CT, CP1, (COC1 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CS10, CS00, CT, CT, CT, CT, 
      (COC0 0), CSP1, (COC1 1), CSP0, CT, CP0, CT, CT, CP0, CS10, CP0, CS00, CS00, CS11, CP1, 
      CP0, CS11, CP0, CS10, CS11, CP0, CS10, CS10, CS11, CP0, CS10, CS01, CP1, CP1, CP0, CS10, 
      CS01, CP0, CP1, CP1, CP0, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CP0, CS00, CP1, CP0, 
      CS11, CP0, CS10, CS00, CP0, CS01, CP0, CS10, CS10, CS11, CP0, CP0, CS00, CP0, CP0, CS01, 
      CP0, CS10, CS01, CP0, CP0, CS00, CS00, CP1, CP1, CP0, CP0, CP0, CS00, CS11, CP0, CS10, 
      CS01, CP1, CP0, CS11, CP0, CP0, CP0, CP1, CP0, CP1, CP1, CP0, CS10, CS00, CS10, CS10, 
      CS01, CP0, CP0, CP1, CP0, CS10, CS10, CS01, CP0, CP1, CP1, CP1, CP0, CP0, CS00, CS00, 
      CS00, CP0, CS01, CP0, CS10, CP1, CP0, CS10, CP1, CP0, CS10, CS11, CP0, CS10, CS01, CP1, 
      CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), CSP0, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, 
      CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), CSP1, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, (COC1 0), 
      CSP1, CT, (COC0 0), CSP0, CS10, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CP1, 
      (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), 
      CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CP0, CT, CT, 
      CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, CP0, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS10, CS11, CT, 
      (COC0 0), CSP1, CT, CP1, (COC1 0), CSP1, CP1, CT, CP0, CT, CT, CT, CP0, CT, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), CSP1, (COC1 1), CSP0, CT, (COC1 0), CSP1, CT, (COC0 1), 
      (CSC1 0), CSP1, CP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CP0, CT, (COC1 0), CSP0, 
      CS10, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, 
      CT, CT, CT, CT, CP0, CS11, CP0, CT, CT, CT, (COC0 0), CSP1, CP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS10, (CEC 0), (CSC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CP1, CT, CP0, 
      CT, CT, CP0, CS10, CS10, CS10, CS01, CP0, CS10, CS10, CS01, CP0, CP0, CP0, CS00, CS10, 
      CP0, CS00, CP0, CS00, CP1, CP0, CP0, CS01, CP1, CP0, CP1, CP0, CP0, CS00, CP0, CS00, CP0, 
      CP1, CP1, CP0, CS10, CS00, CS10, CS00, CP0, CP0, CS00, CS11, CP0, CP0, CS01, CP0, CS10, 
      CS11, CP0, CS11, CP1, CP1, CP0, CS10, CP0, CS00, CS11, CP1, CP1, CP0, CS10, CP0, CS00, 
      CP0, CS01, CP0, CS10, CP0, CP0, CS00, CS11, CP0, CS10, CP1, CP1, CP0, CS10, CS01, CP0, 
      CP0, CS01, CP0, CP0, CS00, CS00, CS10, CS10, CS10, CS11, CP0, CS10, CP0, CS00, CS10, 
      CS10, CS00, CS00, CP1, CP1, CP1, CP0, CP0, CS00, CS01, CP0, CS10, CS11, CP1, CP0, CS10, 
      CP0, CP1, CP0, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CS00, CS01, CP1, CP0, CP1, CP0, 
      CS10, CS11, CP0, CS11, CP1, CP1, CP1, CP0, CP0, CS00, CS00, CS00, CP0, CP0, CP0, CS01, 
      CP1, CP0, CP0, CS01, CP0, CS10, CS11, CP0, CS10, CS01, CP1, CP0]
]

def z2b_0539 : WordList := [V, V, V, V, V, V, V, V, K, Q, V, V, V, K, V, V, Q, V, V, V, K, V, 
    V, V, K, V, V, V, V, V, V, K, V, V, Q, V, Q, V, V, K, V, V, V, K, V, V, V, V, K, Q, V, V, 
    V, V, K, Q, V, V, V, K, V, V, V, V, V, V, V, V, K, Q, V, V, V, V, V, K, V, V, V, K, V, V, 
    V, V, K, V, V, V, V, K, V, Q, V, V, V, V, V, K, V, Q, V, V, V, V, V, K, Q, V, V, V, V, V, 
    K, V, V, V, K, K, V, V, V, V, V, V, V, K, V, V, V, V, V, K, V, V, V, V, V, V, K, Q, V, V, 
    V, V, V, V, V, V, K, V, V, V, V, V, K, V, Q, V, K, V, V, V, V, K, V, V, V, V, V, V, V, K, 
    V, Q, V, K, V, V, V, K, V, V, V, V, V, V, V, K, Q, V, V, V, K, V, Q, V, K, V, Q, V, V, K, 
    V, Q, V, V, V, V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, V, K, V, V, V, V, K, V, V, V, 
    K, V, V, V, V, V, V, K, V, V, Q, V, V, V, V, V, K, Q, V, V, V, V, V, V, V, V, V, K, V, V, 
    V, V, K, V, V, V, V, V, V, V, V, V, K, V, V, V, V, K, V, V, V, V, V, V, V, K, V, Q, V, V, 
    V, V, V, K, Q, V, V, V, V, V, V, V, K, V, V, Q, V, V, V, Q, V, Q, V, V, V, V, V, V, V, V, 
    V, V, K, V, Q, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, K, V, Q, V, V, V, V, V, V, V, 
    V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, V, K, V, V, V, V, V, V, K, Q, V, V, V, V, V, 
    V, V, V, K, V, Q, V, Q, Q, V, K, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, 
    V, K, V, Q, V, V, V, Q, V, V, K, V, Q, V, V, V, V, K, V, V, Q, V, V, V, V, Q, V, Q, V, V, 
    V, V, K, V, Q, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, V, K, V, V, V, V, V, 
    V, V, K, V, Q, V, K, V, V, V, K, V, V, V, V, V, V, V, V, V, Q, Q, Q, K, V, Q, Q, K, V, V, 
    V, K, Q, V, K, V, K, V, V, V, K, V, V, V, V, V, K, V, K, V, V, V, V, Q, K, Q, K, V, V, K, 
    Q, V, V, K, V, Q, Q, V, Q, V, V, V, Q, V, K, Q, V, V, V, Q, V, K, V, K, V, Q, V, V, K, Q, 
    V, Q, V, V, V, Q, K, V, V, K, V, V, K, K, Q, Q, Q, Q, V, Q, V, K, Q, Q, K, K, V, V, V, V, 
    V, K, K, V, Q, Q, V, V, Q, V, V, V, V, V, V, V, V, Q, Q, K, K, K, V, V, V, V, Q, Q, V, Q, 
    V, V, V, V, V, K, K, K, V, V, V, K, V, V, V, K, V, Q, Q, V, Q, K, V, V]

def z2c_low_0539 : WordList := [Q, K, K, Q, Q, K, K, K, Q, Q, Q, Q, K, Q, Q, K, Q, K, K, K, K, 
    K, Q, Q, Q, K, K, K, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K, Q, Q, Q, K, Q, 
    K, Q, Q, K, K, K, Q, Q, Q, Q, Q, K, K, K, K, Q, K, K, Q, Q, Q, K, K, K, Q, Q, K, Q, Q, Q, 
    K, K, Q, Q, Q, K, Q, Q, K, K, K, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, 
    Q, K, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, K, K, Q, Q, Q, K, Q, K, Q, Q, Q, K, Q, Q, K, K, Q, 
    K, K, Q, Q, Q, Q, Q, Q, K, K, Q, K, K, Q, Q, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, Q, Q, K, K, 
    K, K, Q, K, K, Q, Q, K, K, Q, Q, Q, Q, Q, K, K, Q, Q, K, K, K, Q, Q, K, Q, K, K, Q, K, Q, 
    K, Q, Q, K, K, Q, Q, K, Q, K, K, K, Q, Q, Q, Q, Q, K, Q, K, Q, K, K, Q, Q, K, K, Q, Q, Q, 
    Q, K, Q, Q, K, Q, K, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, K, K, K, K, K, Q, Q, K, Q, K, Q, Q, 
    Q, K, K, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, K, K, K, K, Q, K]

def z2c_top_0539 : WordList := [Q,Q,K,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K]

def z2c_0539 : WordList := z2c_low_0539 ++ z2c_top_0539

theorem z2d_0539 :
    CanonRounds (evalWords z29_0539 default)
        (evalWords (prefix33Words ++ (z2b_0539 ++ (z2c_0539 ++ tail8Words))) default) :=
  evalCanonRounds_sound z2a_0539 z29_0539
      (prefix33Words ++ (z2b_0539 ++ (z2c_0539 ++ tail8Words)))
      (by decide +kernel)

theorem z2e_0539 :
    BGood (z2b_0539 ++ (z2c_0539 ++ tail8Words)) := by
  apply bGood_of_check z2b_0539 z2c_low_0539 z2c_top_0539 <;> decide +kernel

def zRem1Pad_0539 : WordList := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,K,K,K,K,Q,Q,Q,Q,Q,K,K,K,K]

def zMid1_0539 : WordList := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,K,K,K,K,Q,Q,Q,Q,Q,K,K,K,Q]

def zCh1_0539 : List Choice := [CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, 
    (COC0 0), CSP0, CT, (COC1 0), CSP0, CS10, CS00, CS00, CP1, CP1, CP0, CS10, CS00, CP0]

def zOut1_0539 : WordList := [V,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,Q,K,K,V,V,V,Q,K,V,K,K,Q,Q,K,Q,Q,Q]

def zRem2Pad_0539 : WordList := [V, V, V, V, V, V, V, V, K, Q, V, V, V, K, V, V, Q, V, Q, K, K, 
    V, V, V, Q, K, V, K, K, Q, Q, K, Q, Q, Q, K, K, K, K, K]

def zMid2_0539 : WordList := [V, V, V, V, V, V, V, V, K, Q, V, V, V, K, V, V, Q, V, Q, K, K, V, 
    V, V, Q, K, V, K, K, Q, Q, K, Q, Q, Q, K, K, K, K, Q]

def zCh2_0539 : List Choice := [CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, 
    (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CP0, CS10, CT, CT, CT, (COC0 1), CSP0, CS10, CS01, 
    CP0, CP1, CP0, CS10, CS10, CS10, CP0]

def zOut2_0539 : WordList := [V, V, V, V, V, V, V, K, V, Q, V, V, K, V, V, Q, V, V, V, Q, V, V, 
    V, K, V, V, Q, K, V, V, V, Q, Q, Q, V, K, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q]

def zRem3Pad_0539 : WordList := [V, V, V, V, V, V, V, V, K, V, Q, V, V, K, V, V, Q, V, V, V, Q, 
    V, V, V, K, V, V, Q, K, V, V, V, Q, Q, Q, V, K, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q, K, K, K, 
    K, K, K, K]

def zCk0_0539 : CCfg := ⟨A,0,[],[]⟩

def zCk1_0539 : CCfg := ⟨C,1,
    [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 
      0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1]⟩

def zCk2_0539 : CCfg := ⟨A,0,
    [1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 
      1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]⟩

def zCk3_0539 : CCfg := ⟨C,0,
    [1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 
      1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 
      1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    [0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]⟩

def zCk4_0539 : CCfg := ⟨C,1,
    [0, 1],
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 
      0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 
      0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 
      0, 1, 0, 1, 0, 1, 0, 1]⟩

private theorem zCk_step1_0539 : (c_to_cfg zCk0_0539) [canon_tm]⊢⁺ (c_to_cfg zCk1_0539) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk0_0539 10000 = some zCk1_0539)

private theorem zCk_step2_0539 : (c_to_cfg zCk1_0539) [canon_tm]⊢⁺ (c_to_cfg zCk2_0539) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk1_0539 10000 = some zCk2_0539)

private theorem zCk_step3_0539 : (c_to_cfg zCk2_0539) [canon_tm]⊢⁺ (c_to_cfg zCk3_0539) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk2_0539 10000 = some zCk3_0539)

private theorem zCk_step4_0539 : (c_to_cfg zCk3_0539) [canon_tm]⊢⁺ (c_to_cfg zCk4_0539) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk3_0539 6519 = some zCk4_0539)

private theorem zH1_0539 :
    Side ([Call.ch] ^ 4) (evalWords zRem1Pad_0539 default) (evalWords zMid1_0539 default) :=
  evalChPow_sound zRem1Pad_0539 4 zMid1_0539 (by decide +kernel)

private theorem zB1_0539 :
    BRIncs false 5 (evalWords (zMid1_0539 ++ [K]) default) (evalWords zOut1_0539 default) :=
  evalChoiceList_sound zCh1_0539 false 5 (zMid1_0539 ++ [K]) zOut1_0539 (by decide +kernel)

private theorem zH2_0539 :
    Side ([Call.ch] ^ 8) (evalWords zRem2Pad_0539 default) (evalWords zMid2_0539 default) :=
  evalChPow_sound zRem2Pad_0539 8 zMid2_0539 (by decide +kernel)

private theorem zB2_0539 :
    BRIncs false 4 (evalWords (zMid2_0539 ++ [K]) default) (evalWords zOut2_0539 default) :=
  evalChoiceList_sound zCh2_0539 false 4 (zMid2_0539 ++ [K]) zOut2_0539 (by decide +kernel)

private theorem zH3_0539 :
    Side ([Call.ch] ^ 16) (evalWords zRem3Pad_0539 default) (evalWords z29_0539 default) :=
  evalChPow_sound zRem3Pad_0539 16 z29_0539 (by decide +kernel)

theorem z0E_0539 : (c_to_cfg zCk0_0539) [canon_tm]⊢⁺ (cfgCanon (evalWords z29_0539 default)) := by
  have h_all := stepPlus_trans_canon zCk_step1_0539
    (stepPlus_trans_canon zCk_step2_0539
    (stepPlus_trans_canon zCk_step3_0539 zCk_step4_0539))
  have heq1 : c_to_cfg zCk4_0539 = cfgLeft lh (w_pre3 +> evalWords zRem1Pad_0539 default) := by
    simp only [c_to_cfg, C, WordCanonBR.C, zCk4_0539, zCL, cfgLeft, lh, w_pre3, w_pre3_rest,
        w_word, zRem1Pad_0539, evalWords, t, d0, d1, one, List.cons_append, List.nil_append,
        append_cons, append_nil, z00, zero_cons_default_canon,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  rw [heq1] at h_all
  have h_h1 := zH1_0539
  have h_b1_0 := zB1_0539
  have h_b1 : BRIncs false 5 (evalWords zMid1_0539 default) (evalWords zOut1_0539 default) := by
    simpa only [evalWords_append,evalWords,d0_append_default] using! h_b1_0
  have h_s1 :
      Side ([.cp] ++ [.ch] ^ 2) (evalWords zMid1_0539 default) (evalWords zOut1_0539 default) := by
    simpa only [append_nil] using! numSide_of_brIncs h_b1 [] ([.cp] ++ [.ch] ^ 2) (Num.odd 2)
  have h_turn1 := stepPlus_word_pre3_full (by have h := side_append h_h1 h_s1; exact h)
  have heq2 : t +> evalWords zOut1_0539 default = evalWords zRem2Pad_0539 default := by
    simp only [zOut1_0539, zRem2Pad_0539, evalWords, t, d0, d1, List.cons_append, 
        List.nil_append, append_cons, append_nil, z00, zero_cons_default_canon]
  rw [heq2] at h_turn1
  have h_h2 := zH2_0539
  have h_b2_0 := zB2_0539
  have h_b2 : BRIncs false 4 (evalWords zMid2_0539 default) (evalWords zOut2_0539 default) := by
    simpa only [evalWords_append,evalWords,d0_append_default] using! h_b2_0
  have h_s2 : Side ([.cj,.ch]) (evalWords zMid2_0539 default) (evalWords zOut2_0539 default) := by
    simpa only [z06, list_pow_one_canon, List.cons_append, List.nil_append,
        append_nil] using! numSide_of_brIncs h_b2 [] ([.cj] ++ [.ch] ^ 1) (Num.even 1)
  have h_turn2 := stepPlus_word_pre5_full (side_append h_h2 h_s2)
  have heq3 : t +> evalWords zOut2_0539 default = evalWords zRem3Pad_0539 default := by
    simp only [zOut2_0539, zRem3Pad_0539, evalWords, t, d0, d1, List.cons_append, 
        List.nil_append, append_cons, append_nil, z00, zero_cons_default_canon]
  rw [heq3] at h_turn2
  have h_h3 := zH3_0539
  have h_turn3 := stepPlus_word_pre_full h_h3
  exact stepPlus_trans_canon h_all
    (stepPlus_trans_canon h_turn1
    (stepPlus_trans_canon h_turn2 h_turn3))

theorem z2s_0539 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0539) N = 
        some (cfgCanon (evalWords (prefix33Words ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0539 with ⟨k1,_,hk1⟩
    rcases stepStar_of_canonRounds z2d_0539 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0539 ++ (z2c_0539 ++ tail8Words),
      multiStep_trans_canon canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0539⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases bGood_progress h_good with ⟨w',hStep,h_good'⟩
    rcases stepPlus_of_bStep hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      multiStep_trans_canon canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0539 : Fin 6 -> Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 4

def zCfgMap_0539 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0539,c.tape⟩

theorem zStepMap_0539 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0539 c) = (step canon_tm c).map zCfgMap_0539 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

theorem zMultiStepMap_0539 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0539 c) n = (multiStep canon_tm c n).map zCfgMap_0539 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ_canon,multiStep_succ_canon,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0539 c'



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0539 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0539 (c_to_cfg zCk0_0539) = init [] := rfl
  have h_map := zMultiStepMap_0539 (c_to_cfg zCk0_0539) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := multiStep_add_Intermediate h_map
  rw [multiStep_succ_canon,hn] at h_some
  exact h_some

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RB
