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

namespace BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LA_1LA0LE

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LA_1LA0LE"

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

def z29_0813 : WordList := [V, V, V, V, V, V, V, K, V, V, Q, V, V, Q, K, V, V, V, K, V, Q, Q, 
    Q, V, K, Q, Q, K, Q, Q, K, K, K, K, K, K, Q]

def z2a_0813 : List (List Choice) := [
  [CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CP0, CT, CT, (COC0 0), 
      (CSC0 0), CSP1, CP1, (COC1 0), CSP0, CS11, CP0, CS11, CP0, CS10, CS10, CS00, CS10, CS10, 
      CP0],
  [CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CS10, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, 
      (COC1 0), CSP1, CP0, CP1, (COC0 0), CSP0, CS10, CS10, CP0, CP1, CP0, CS10, CP1, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), (CSC0 0), 
      CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CP1, CT, CT, (COC0 0), 
      CSP1, CT, CT, CT, CP0, CP1, CP0, CS10, CS11, CP0, CP0, CP0, CS01, CP1, CP0, CP0, CS01, 
      CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, 
      (COC0 0), CSP0, CS10, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CP1, CT, CT, (COC0 0), CSP0, CT, CT, 
      (COC0 0), CSP0, CT, CT, CP0, CP1, CP0, CS11, CP1, CP0, CP0, CP0, CP0, CP1, CP0, CP0, CP0, 
      CS01, CP1, CP0, CS10, CP0, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CT, (COC0 0), (CSC0 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP0, CT, CT, CP0, CS10, CP0, CS00, 
      CS00, CS10, CS00, CP1, CP0, CS10, CP0, CS00, CS00, CP0, CS00, CS10, CS00, CS00, CS10, 
      CS10, CP0, CS01, CP0, CS10, CP0, CP1, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CP0, 
      CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CS10, CT, (COC1 0), CSP1, (COC1 0), 
      CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, 
      CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS10, CP0, CT, (COC1 0), CSP1, (COC1 0), CSP0, 
      (CEC 0), CSP0, CP0, CS00, CP1, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, 
      (COC0 0), CSP1, (COC1 1), CSP0, CT, CT, CP0, CS10, CS10, CS10, CS00, CS11, CP0, CS10, 
      CP1, CP0, CS10, CS10, CS10, CS11, CP1, CP1, CP1, CP0, CS10, CS01, CP0, CS10, CP0, CP1, 
      CP0, CP0, CP0, CP1, CP0, CS10, CP1, CP0, CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), (CSC0 0), CSP1, 
      (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, 
      CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT, (COC0 0), 
      CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), (CSC1 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, 
      CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CP1, CP0, CS11, (COC0 0), CSP1, CT, CT, 
      CP1, CP1, CT, CT, CT, CT, (COC0 1), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, 
      CP1, CT, CT, CP0, CS10, CS11, CP0, CS10, CS10, CP0, CS00, CS10, CP0, CP0, CS00, CS10, 
      CP1, CP1, CP0, CS11, CP1, CP0, CS10, CP1, CP0, CS10, CS10, CS00, CS01, CP1, CP1, CP1, 
      CP0, CS10, CS01, CP0, CS10, CP0, CP1, CP0, CP0, CP0, CS01, CP1, CP0, CP0, CS01, CP0, 
      CS10, CS11, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), 
      CSP0, CS10, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, 
      CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT, CT, CP0, CT, 
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CT, CT, CT, CT, CT, CT, CT, CP1, CT, CP1, (COC1 0), CSP0, CS11, CT, (COC0 0), CSP0, CS11, 
      CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CP0, CS10, CT, CT, CT, 
      CT, (COC0 1), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CP1, CT, 
      CT, CP0, CS10, CP0, CS00, CS00, CP0, CS00, CS10, CS01, CP0, CS11, CP1, CP0, CS11, CP1, 
      CP0, CP0, CS00, CS01, CP1, CP1, CP0, CP0, CP1, CP1, CP1, CP0, CP1, CP1, CP0, CS11, CP1, 
      CP0, CS10, CP1, CP0, CS10, CS10, CS00, CS01, CP1, CP1, CP1, CP0, CS10, CS01, CP0, CS10, 
      CP0, CP1, CP0, CP0, CP0, CS01, CP1, CP0, CS10, CP0, CS01, CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, 
      CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), 
      CSP1, CT, (COC0 0), (CSC0 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP0, CT, (COC1 0), CSP0, CS10, CT, CT, CT, CT, (COC0 0), 
      (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 0), CSP1, (COC1 0), (CSC1 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP1, (COC1 0), 
      CSP0, (CEC 0), (CSC0 1), CSP1, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS10, CT, CT, 
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, 
      CP0, CS10, CT, CT, CT, CT, (COC0 1), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), 
      CSP1, (COC1 0), CSP0, CT, CP0, CT, CT, CP0, CS10, CS10, CS10, CS00, CP0, CS00, CS00, 
      CS01, CP0, CS10, CP1, CP0, CS10, CS10, CP1, CP0, CS11, CP0, CP1, CP0, CP1, CP0, CP0, 
      CS01, CP1, CP1, CP0, CS10, CP1, CP1, CP0, CS10, CS01, CP1, CP1, CP0, CS10, CS00, CS00, 
      CS00, CS00, CS10, CS00, CS00, CS10, CS00, CS10, CS11, CP1, CP0, CP0, CS00, CP0, CS00, 
      CS10, CS10, CS00, CP1, CP1, CP0, CS10, CP1, CP0, CS10, CS10, CS00, CS01, CP1, CP1, CP1, 
      CP0, CS10, CS01, CP0, CS10, CP0, CP1, CP0, CP0, CP0, CP1, CP0, CS10, CS10, CS00, CP0, 
      CS01, CP0, CS10, CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP0, CS10, CT, (COC1 0), CSP1, (COC1 0), CSP1, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, 
      CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, 
      CS11, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      (COC0 0), (CSC1 0), CSP1, CT, CP1, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, 
      (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, 
      (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CP1, (COC1 1), CSP0, CS10, 
      (CEC 0), CSP1, CT, CT, CP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, (COC0 0), CSP1, CT, CT, CT, CP0, CT, CT, CT, CP0, CS10, CS10, CS00, CP0, CS00, CP0, 
      CP1, CT, CT, (COC0 0), (CSC1 0), CSP0, CS11, CP0, CT, CT, (COC0 0), CSP1, CT, (COC0 0), 
      CSP1, CP0, CS10, CT, CT, CT, CT, (COC0 1), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 1), CSP0, CT, CP0, CT, CT, CP0, CP1, CP0, CS10, CS10, CP1, CP0, CS11, CP0, CP1, 
      CP0, CP1, CP1, CP1, CP0, CP1, CP0, CP0, CP0, CP0, CS00, CS10, CS00, CP1, CP0, CS10, CS11, 
      CP0, CP0, CS00, CP0, CP0, CP1, CP1, CP0, CS10, CP1, CP1, CP0, CS10, CS01, CP1, CP1, CP1, 
      CP1, CP1, CP1, CP1, CP0, CP0, CS01, CP0, CS10, CS10, CS10, CS10, CP0, CS01, CP1, CP0, 
      CS11, CP1, CP0, CS10, CP1, CP0, CS10, CS10, CS00, CS01, CP1, CP1, CP1, CP0, CS10, CS01, 
      CP0, CS10, CP0, CP1, CP0, CP0, CP0, CP1, CP0, CS10, CP1, CP0, CS10, CS11, CP0, CS10, 
      CS01, CP1, CP0],
  [CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), 
      CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, 
      CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0), (CSC0 0), CSP1, (COC1 0), CSP1, 
      (COC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, 
      (COC1 0), CSP1, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, (COC1 0), 
      (CSC1 0), CSP1, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT, CT, CT, CT, 
      CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, 
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, 
      (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, 
      CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), 
      CSP0, CS11, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, 
      CS10, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, 
      (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), 
      CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, 
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, 
      (COC1 1), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, CT, (COC0 0), 
      CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, 
      CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CP1, CT, 
      (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CP0, CT, CT, 
      CP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CP0, CT, CT, CT, CT, 
      CT, CT, CT, CT, (COC0 0), CSP0, CT, CP1, CP1, (COC1 0), CSP0, CT, (COC1 0), CSP1, CT, 
      (COC0 0), CSP1, CT, (COC0 0), CSP1, CP0, CS10, CT, CT, CT, CT, (COC0 1), CSP1, CT, CT, 
      CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CP1, CT, CP0, CT, CT, CP0, CS10, CP0, CS00, CS00, 
      CP0, CS00, CP0, CS01, CP1, CP1, CP1, CP0, CS10, CS00, CS01, CP0, CP0, CS01, CP0, CP0, 
      CS00, CP0, CP0, CS01, CP1, CP0, CP1, CP0, CS11, CP1, CP1, CP0, CP0, CP1, CP0, CS10, CS10, 
      CS01, CP1, CP0, CS10, CS00, CS00, CP0, CS00, CS00, CP1, CP1, CP0, CS10, CS00, CS11, CP0, 
      CS10, CS01, CP0, CP0, CS00, CS00, CP1, CP1, CP1, CP0, CS11, CP0, CS10, CS10, CS10, CP0, 
      CP0, CS00, CS10, CS00, CP1, CP0, CS10, CS11, CP0, CS10, CS10, CP0, CS00, CS10, CS01, CP0, 
      CS11, CP1, CP1, CP0, CS10, CP1, CP1, CP0, CS10, CS01, CP1, CP1, CP1, CP1, CP1, CP1, CP1, 
      CP1, CP0, CP1, CP0, CP0, CS00, CP0, CS00, CS10, CS00, CS10, CP1, CP1, CP0, CS10, CP1, 
      CP0, CS10, CS10, CS00, CS01, CP1, CP1, CP1, CP0, CS10, CS01, CP0, CS10, CP0, CP1, CP0, 
      CP0, CP0, CS01, CP1, CP0, CP0, CS01, CP0, CS10, CS11, CP0, CS10, CS01, CP1, CP0]
]

def z2b_0813 : WordList := [V, V, V, V, V, V, V, K, V, V, Q, V, V, V, V, V, V, K, Q, V, V, V, 
    K, K, V, V, Q, V, Q, V, V, V, K, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, K, V, 
    V, V, K, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, K, V, V, Q, V, Q, V, V, V, V, K, 
    Q, V, V, Q, V, V, Q, Q, V, V, V, V, V, K, Q, V, V, Q, V, V, V, V, V, V, V, K, Q, V, V, V, 
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, 
    V, V, V, V, V, V, V, K, V, Q, V, V, V, V, V, K, V, V, Q, V, V, K, V, V, Q, V, V, V, V, K, 
    V, V, V, V, V, V, K, V, V, V, K, V, V, V, V, V, V, K, V, Q, V, V, K, V, V, V, V, K, V, V, 
    V, K, V, Q, V, V, V, V, V, V, V, V, V, V, K, V, V, Q, V, V, K, V, V, K, V, V, V, V, K, V, 
    V, V, V, V, V, K, V, V, Q, V, Q, V, V, V, V, V, V, V, V, K, V, V, K, V, V, V, V, V, V, K, 
    V, V, V, V, V, V, K, V, V, V, K, V, V, V, V, V, V, V, V, V, K, V, Q, V, V, V, V, V, K, V, 
    Q, V, K, V, V, V, K, V, V, Q, V, V, Q, V, V, V, V, K, V, V, V, V, V, V, V, V, K, Q, V, V, 
    V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V, 
    V, K, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, Q, V, V, Q, 
    V, V, K, V, V, K, V, V, Q, V, V, V, V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, 
    V, V, Q, V, K, K, V, K, V, K, V, V, V, V, Q, K, K, V, V, K, V, V, K, V, V, K, V, V, V, V, 
    Q, V, V, V, V, V, V, Q, Q, K, V, V, Q, K, K, V, K, K, V, V, V, Q, K, Q, V, Q, K, V, V, K, 
    K, V, V, V, V, Q, V, Q, Q, Q, V, V, K, Q, K, V, V, Q, Q, V, Q, Q, V, K, Q, K, V, Q, V, V, 
    V, Q, V, V, V, Q, K, V, V, V, V, V, V, V, V, V, V, V, V, K, V, K, Q, K, Q, V, V, V, Q, V, 
    V, Q, Q, K, K, V, V, V, V, Q, K, V, Q, V, V, V, V, V, K, V, V, V, K, V, Q, Q, V, Q, K, V, V]

def z2c_low_0813 : WordList := [Q, K, K, K, K, K, Q, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, 
    K, Q, K, K, Q, K, K, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, K, Q, K, K, Q, Q, Q, Q, 
    Q, Q, K, K, K, K, K, Q, Q, Q, K, K, K, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, K, 
    K, K, K, K, K, K, K, K, Q, Q, K, Q, Q, Q, K, K, Q, Q, K, Q, K, K, K, Q, Q, Q, K, K, Q, Q, 
    Q, Q, Q, K, K, K, K, Q, Q, Q, K, K, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, K, K, K, Q, Q, K, 
    K, Q, Q, K, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, K, Q, K, K, K, Q, Q, K, Q, K, K, K, K, Q, 
    Q, Q, K, K, Q, K, K, Q, Q, K, K, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, K, 
    K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, Q, K, K, K, K, K, Q, K, Q, 
    Q, Q, Q, K, Q, Q, Q, Q, K, K, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, K, 
    K, Q, K, Q, Q, Q, K]

def z2c_top_0813 : WordList := [Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K]

def z2c_0813 : WordList := z2c_low_0813 ++ z2c_top_0813

theorem z2d_0813 :
    CanonRounds (evalWords z29_0813 default)
        (evalWords (prefix33Words ++ (z2b_0813 ++ (z2c_0813 ++ tail8Words))) default) :=
  evalCanonRounds_sound z2a_0813 z29_0813
      (prefix33Words ++ (z2b_0813 ++ (z2c_0813 ++ tail8Words)))
      (by decide +kernel)

theorem z2e_0813 :
    BGood (z2b_0813 ++ (z2c_0813 ++ tail8Words)) := by
  apply bGood_of_check z2b_0813 z2c_low_0813 z2c_top_0813 <;> decide +kernel

def zPre_0813 : WordList := [V, V, V, V, V, V, V, K, V, V, Q, V, V, Q, K, V, V, V, K, V, Q, Q, 
    Q, V, K, Q, Q, K, Q, Q, K, K, K, K, K, K, K]

def zCk0_0813 : CCfg := ⟨B,0,[],[]⟩

def zCk1_0813 : CCfg := ⟨C,1,
    [1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 
      1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 
      0, 1, 0, 0, 1],
    [1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]⟩

def zCk2_0813 : CCfg := ⟨C,1,
    [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 
      0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 
      0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 
      1, 1, 1, 0, 1, 0, 0, 1],
    [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]⟩

def zCk3_0813 : CCfg := ⟨C,1,
    [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 
      1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 
      1, 0, 0, 1],
    [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 
      0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]⟩

def zCk4_0813 : CCfg := ⟨E,0,
    [0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 
      1, 0, 1, 0, 0, 1],
    [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 
      1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 
      1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]⟩

def zCk5_0813 : CCfg := ⟨B,1,
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 
      0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 
      0, 1],
    [1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 
      0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1]⟩

def zCk6_0813 : CCfg := ⟨D,1,
    [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 
      0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 
      1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 
      0, 1, 0, 0, 0, 0, 0, 1, 0, 1]⟩

def zCk7_0813 : CCfg := ⟨C,1,
    [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 
      1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 
      1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1],
    [0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 1, 0, 1, 
      0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1]⟩

def zCk8_0813 : CCfg := ⟨C,1,
    [1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 
      1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 
      1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 
      1, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    [1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]⟩

def zCk9_0813 : CCfg := ⟨C,1,
    [0, 1],
    [0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 
      0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 
      1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 
      0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 
      1, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]⟩

private theorem zCk_step1 : (c_to_cfg zCk0_0813) [canon_tm]⊢⁺ (c_to_cfg zCk1_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk0_0813 10000 = some zCk1_0813)

private theorem zCk_step2 : (c_to_cfg zCk1_0813) [canon_tm]⊢⁺ (c_to_cfg zCk2_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk1_0813 10000 = some zCk2_0813)

private theorem zCk_step3 : (c_to_cfg zCk2_0813) [canon_tm]⊢⁺ (c_to_cfg zCk3_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk2_0813 10000 = some zCk3_0813)

private theorem zCk_step4 : (c_to_cfg zCk3_0813) [canon_tm]⊢⁺ (c_to_cfg zCk4_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk3_0813 10000 = some zCk4_0813)

private theorem zCk_step5 : (c_to_cfg zCk4_0813) [canon_tm]⊢⁺ (c_to_cfg zCk5_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk4_0813 10000 = some zCk5_0813)

private theorem zCk_step6 : (c_to_cfg zCk5_0813) [canon_tm]⊢⁺ (c_to_cfg zCk6_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk5_0813 10000 = some zCk6_0813)

private theorem zCk_step7 : (c_to_cfg zCk6_0813) [canon_tm]⊢⁺ (c_to_cfg zCk7_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk6_0813 10000 = some zCk7_0813)

private theorem zCk_step8 : (c_to_cfg zCk7_0813) [canon_tm]⊢⁺ (c_to_cfg zCk8_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk7_0813 10000 = some zCk8_0813)

private theorem zCk_step9 : (c_to_cfg zCk8_0813) [canon_tm]⊢⁺ (c_to_cfg zCk9_0813) :=
  canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCk8_0813 7731 = some zCk9_0813)

private theorem zPre_side_0813 :
    Side ([Call.ch] ^ 16) (evalWords zPre_0813 default) (evalWords z29_0813 default) :=
  evalChPow_sound zPre_0813 16 z29_0813 (by decide +kernel)

theorem z0E_0813 : (c_to_cfg zCk0_0813) [canon_tm]⊢⁺ (cfgCanon (evalWords z29_0813 default)) := by
  have h_all := stepPlus_trans_canon zCk_step1
    (stepPlus_trans_canon zCk_step2
    (stepPlus_trans_canon zCk_step3
    (stepPlus_trans_canon zCk_step4
      (stepPlus_trans_canon zCk_step5
      (stepPlus_trans_canon zCk_step6
      (stepPlus_trans_canon zCk_step7
      (stepPlus_trans_canon zCk_step8 zCk_step9)))))))
  have heq : c_to_cfg zCk9_0813 = cfgLeft lh (w_pre +> evalWords zPre_0813 default) := by
    simp only [c_to_cfg, C, WordCanonBR.C, zCk9_0813, zCL, cfgLeft, lh, w_pre, w_pre_rest,
        w_pre5_rest, w_pre3_rest, w_word,
      zPre_0813, evalWords, t, d0, d1, one, List.cons_append, List.nil_append, append_cons,
          append_nil, z00, zero_cons_default_canon,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  rw [heq] at h_all
  exact stepPlus_trans_canon h_all (stepPlus_word_pre_full zPre_side_0813)

theorem z2s_0813 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0813) N = 
        some (cfgCanon (evalWords (prefix33Words ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0813 with ⟨k1,_,hk1⟩
    rcases stepStar_of_canonRounds z2d_0813 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0813 ++ (z2c_0813 ++ tail8Words),
      multiStep_trans_canon canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0813⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases bGood_progress h_good with ⟨w',hStep,h_good'⟩
    rcases stepPlus_of_bStep hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      multiStep_trans_canon canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0813 : Fin 6 -> Fin 6
  | 0 => 5
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 3

def zCfgMap_0813 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0813,⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

theorem zStepMap_0813 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0813 c) = (step canon_tm c).map zCfgMap_0813 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

theorem zMultiStepMap_0813 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0813 c) n = (multiStep canon_tm c n).map zCfgMap_0813 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ_canon,multiStep_succ_canon,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0813 c'



theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0813 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0813 (c_to_cfg zCk0_0813) = init [] := rfl
  have h_map := zMultiStepMap_0813 (c_to_cfg zCk0_0813) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := multiStep_add_Intermediate h_map
  rw [multiStep_succ_canon,hn] at h_some
  exact h_some

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LA_1LA0LE
