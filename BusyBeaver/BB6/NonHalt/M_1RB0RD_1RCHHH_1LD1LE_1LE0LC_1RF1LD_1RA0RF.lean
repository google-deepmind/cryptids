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

namespace BusyBeaver.M_1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
open Counter

open WordCalculus Word WordCanonBR WordCanonBR.BRIncs WordCanonBR.Choice
namespace Solution

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

def z29_0108 : WordList := ([K, V, V, V, V, V, K, V, V, V, V, K, Q, V, V, V, V, V, V, V, Q, Q, 
    Q, K, Q, Q, Q, Q, Q, K, Q, K] ++ [Q, Q, Q, Q])

def z2a_0108 : List (List Choice) := [
  [CS10, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, 
      CT, CT, CP1, CP0, CP1, CP1, CP0, CP0, CS01, CP1, CP0],
  ([CT, (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0),
      (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      CT] ++ [CP0, CS11, CP0, CS11, CP0, CS10, CS10, CS00, CS00, CS10, CS10, CS10, CS10, CS10,
      CS11, CP0, CP0, CP1, CP0]),
  (([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT,
      CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT] ++ [(COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, (COC1 0), CSP1, CP0,
      CS10, CP1, CP1, CP1, CT, CT, CT, (COC0 0), CSP1, CP0, CS11, CP0, CP1, CP0, CP1, CP0, CP0,
      CS00, CS00, CS11]) ++ [CP1, CP0]),
  (([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT, (COC0 0),
      CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT] ++ [CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1, CT,
      (COC0 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT,
      CT, (COC0 0), CSP0, CS10]) ++ [CS01, CT, CT, CP0, CS10, CS10, CP0, CS01, CP0, CP0, CS00,
      CP1, CP0, CS11, CP1, CP1, CP1, CP1, CP1, CP1, CP0, CP0, CP0, CS00, CS11, CP1, CP0]),
  (([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CS10, CT,
      CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT,
      CT] ++ [CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT,
      (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0),
      CSP1, CT, CT]) ++ ([CT, CT, CT, (COC0 0), CSP0, CT, CP0, CT, CT, CT, CP1, (COC1 0), CSP0,
      CT, (COC1 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CS11, CT, CT] ++ [CP0, CS10, CS11, CP1, CP1, CP1, CP0, CS10, CS00, CP0, CP0, CP1, CP0,
      CS10, CS10, CS01, CP0, CS11, CP1, CP1, CP1, CP1, CP0, CP1, CP0, CP0, CS01, CP0, CS10,
      CS11, CP1, CP0])),
  ((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0),
      (CSC1 0), CSP1, CT, CT, CT, CT] ++ [CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT]) ++ ([CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT] ++ [CT, CT, CP1, CT, CT, CT, CT, CP0, CT, CT,
      CT, (COC0 0), CSP1, (COC1 1), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CP1,
      CT, CT, CP0, CP0, CP1, CP1])) ++ ([CP0, CS10, CS00, CP0, CP1, CP1, CP0, CP0, CS00, CP0,
      CS00, CP0, CS01, CP1, CP0, CP0, CS01, CP0, CS10, CS10, CP1, CP0, CS11, CP1, CP1, CP1, CP1,
      CP1, CP1, CP0, CP0, CP0] ++ [CP0, CS00, CS11, CP1, CP0])),
  ((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT,
      CT, (COC0 0), CSP0, CS11, CT] ++ [CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1,
      CT, CT, CT, CT, CT, (COC0 0)]) ++ ([CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0),
      CSP0, CT, CT, CT, CT, CT, CT, CT] ++ [CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT])) ++ (([CT, CT, CT, CT, CT, CT, CT, CT, CP0, CT, CT, CT, CT,
      (COC0 0), (CSC1 0), (CSC1 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CP1, CT, (COC0 0), CSP1,
      CT, CT, CT, CT, CT, CT] ++ [CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CP0, CP0, CP1, CP1,
      CP1, CP0, CS11, CP1, CP0, CP0, CS00, CS00, CS01, CP0, CS11, CP1, CP1, CP0, CP0, CS00,
      CS00, CS00, CS00, CS10]) ++ ([CS00, CP0, CS00, CS10, CS11, CP0, CP1, CP1, CP0, CS10, CS00,
      CS11, CP1, CP0, CS10, CS01, CP1, CP0, CP0, CS01, CP0, CS10, CS11, CP0, CP0, CS01, CP1,
      CP1, CP1, CP1, CP0, CP1] ++ [CP0, CP0, CS00, CS00, CS11, CP0, CS10, CS01, CP1, CP0]))),
  (((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT, (COC0 0),
      CSP0, CT, CT, CT, (COC0 0), (CSC1 0)] ++ [CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT,
      (COC1 0), CSP0, CT, CT, CT, CT, CT, (COC0 0)]) ++ ([CSP0, CT, (COC1 0), CSP1, CT, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT,
      (COC0 0), CSP1, CT, CT, CT, CT, CT, CT, CT] ++ [CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, (COC0 0), CSP0, CT, CT])) ++ (([CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CS11, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0),
      CSP0, CT, CT, CT, CT] ++ [CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CS10, (CEC 0), CSP1, CT, CT, CT,
      (COC0 0), CSP0, CS10, CS00, (CEC 1)]) ++ ([CSP0, CP1, CT, CT, CT, CT, CP0, CS11, CT, CT,
      CP0, CT, CT, (COC0 0), CSP0, CT, CP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CS10, CS01, CT] ++ [CP0, CT, CT, CP0, CS10, CP1, CP0, CS11, CP0, CS10,
      CS01, CP0, CS11, CP1, CP1, CP0, CS10, CP0, CS00, CS10, CP1, CP1, CP1, CP1, CP1, CP1, CP0,
      CS10, CP1, CP1, CP1, CP0]))) ++ ([CP0, CP1, CP1, CP1, CP1, CP1, CP0, CS11, CP1, CP0, CS10,
      CP0, CS00, CP1, CP0, CS10, CS11, CP1, CP0, CP0, CP1, CP0, CS10, CP1, CP0, CS11, CP1, CP1,
      CP1, CP1, CP1, CP1] ++ [CP0, CP0, CP0, CS00, CS11, CP0, CS10, CS01, CP1, CP0])),
  (((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CS10, CT, CT,
      CT, CT, (COC0 0), CSP0, CT] ++ [CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CS11, CT, (COC0 0),
      CSP1, CT, (COC0 0), CSP1]) ++ ([CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1,
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0),
      CSP1, CT, (COC0 0), CSP0, CT] ++ [CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT,
      CT, CT])) ++ (([CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP0, CT, CP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      (COC0 0)] ++ [CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT,
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), (CSC0 0), CSP1, CT, CT, CT,
      CT]) ++ ([(COC0 0), CSP0, CT, CP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT,
      CT] ++ [(COC0 0), CSP0, CT, CP0, CT, CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT,
      (COC0 1), CSP1, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS11, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP1, CT]))) ++ ((([CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT,
      (COC0 0), CSP1, (COC1 0), CSP0, CT, CT, CP1, CT, CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0),
      CSP1, CT, CT, CT, CT] ++ [CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CP0, CT, CT, CP0,
      CS10, CS11, CP1, CP1, CP0, CP0, CS01, CP0, CS10, CS11, CP0, CS10, CP1, CP0, CS10, CS11,
      CP1, CP0, CS11, CP0]) ++ ([CP1, CP0, CS11, CP0, CS10, CS00, CP0, CS00, CS00, CS00, CS00,
      CP1, CP1, CP0, CP0, CS00, CP1, CP0, CS10, CP1, CP1, CP0, CP0, CP1, CP1, CP0, CS10, CP0,
      CS00, CS11, CP0, CS10] ++ [CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP1, CP0,
      CP1, CP1, CP1, CP1, CP0, CP0, CP1, CP1, CP0, CS10, CP0, CP1, CP0, CS10, CS11, CP1, CP0,
      CP0, CS01, CP0])) ++ [CS10, CS11, CP0, CP0, CS01, CP1, CP1, CP1, CP1, CP0, CP1, CP0, CP0,
      CS01, CP0, CS10, CS11, CP0, CS10, CS11, CP1, CP0])),
  ((((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0),
      CSP1, (COC1 0), CSP1, CT, CT, CT] ++ [(COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0),
      CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP0, CT, (COC1 0)]) ++ ([CSP0, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, (COC0 0), CSP0] ++ [CT, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT])) ++ (([CT, CT, CT, (COC0 0), CSP0, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT] ++ [(COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0),
      CSP0, CS10, CT, CT, CT, CT]) ++ ([CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT,
      CT, CT, CT, CT] ++ [CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      (COC1 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, (COC1 0), CSP1,
      CT, CT, CT, CT, CT, (COC0 0), CSP0]))) ++ ((([CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CT, (COC1 0), CSP0, CT, CT, CT, CT] ++ [CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT,
      CT, CT, CT, CP1, CT, CT, CT, (COC0 0), CSP0, CT, CP1, (COC1 0), CSP1, CT, CT, CP1, CT,
      (COC0 0), CSP1, CT, CT, (COC0 0), CSP1]) ++ ([CT, (COC0 1), CSP0, CS10, CS00, CS10, CT,
      CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1,
      (COC1 0), CSP0, CS11, (COC1 0), CSP1, CT, CT, CT, CT, CT] ++ [(COC0 0), CSP1, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT, CP1, CT, CT, (COC0 0),
      CSP0, CT, CP1, CT, (COC0 0), CSP0, CT, CT])) ++ (([CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      CP1, CT, CP1, CT, CT, CP0, CP0, CP1, CP0, CS11, CP0, CS11, CP0, CP1, CP0, CS11, CP1, CP0,
      CS10, CP1, CP0, CP0, CS00, CP0] ++ [CS01, CP0, CS10, CS01, CP0, CS11, CP0, CP1, CP1, CP0,
      CS10, CP1, CP0, CS10, CP0, CP0, CS01, CP1, CP1, CP1, CP0, CP1, CP1, CP0, CP0, CS00, CS00,
      CS01, CP0, CS10, CP0, CP1]) ++ ([CP1, CP0, CS10, CP0, CS00, CP1, CP0, CS11, CP1, CP1, CP0,
      CS10, CP0, CP1, CP0, CS11, CP0, CP1, CP1, CP1, CP0, CP1, CP1, CP0, CS10, CP0, CS00, CP0,
      CS00, CP0, CP1, CP1] ++ [CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP0, CP0, CP1, CP1,
      CP1, CP1, CP1, CP0, CS11, CP1, CP0, CS10, CS00, CP0, CP1, CP0, CS10, CS11, CP1, CP0, CP0,
      CP1, CP0])))) ++ [CS10, CP1, CP0, CS11, CP1, CP1, CP1, CP1, CP1, CP1, CP0, CP0, CP0, CP0,
      CS00, CS11, CP0, CS10, CS11, CP1, CP0]),
  ((((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0),
      CSP1, CT, (COC0 0), CSP1, (COC1 0), CSP1] ++ [CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CT, CT, CT, (COC0 0), CSP0, CS11]) ++ ([CT, (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, CT,
      CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      CT, CT, CT, CT, CT, (COC0 0), CSP0, CT] ++ [(COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT,
      CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, (COC0 0), (CSC1 0), CSP1])) ++ (([CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT] ++ [(COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT,
      (COC0 0)]) ++ ([(CSC0 0), CSP1, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0),
      CSP0, CT] ++ [CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0),
      CSP0, CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0, CS11, CT,
      (COC0 0), CSP1, CT]))) ++ ((([CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP0, CT, CT, CP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CT] ++ [(COC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP1, CT, CT, CT]) ++ ([CT,
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CP0, CS11, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT,
      CP1] ++ [CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT])) ++ (([CT,
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP1, CT, CT, (COC0 0), CSP1, CT,
      (COC0 0)] ++ [CSP1, CT, CT, (COC0 0), (CSC1 0), CSP0, CT, (COC1 1), CSP1, CT, CT, CT,
      (COC0 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CS10, (CEC 0), CSP1]) ++ ([CT, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, CT, (COC0 0), CSP1, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT, CT, CT,
      CT, (COC0 0), CSP1, (COC1 0), (CSC0 0), CSP0, CT, CT] ++ [CT, CT, CT, CT, CT, (COC0 0),
      CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CP0, CT, CT, CT,
      CP1, CT, CT, CT, CT, (COC0 0), CSP1])))) ++ ((([CT, (COC0 0), CSP1, CT, CT, CT, CT, CT,
      CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT, CP1, CT, CT, CP0, CP0, CS01, CP1, CP1, CP0, CP0,
      CP0, CS00, CS10, CS11, CP0, CS10] ++ [CP1, CP0, CS10, CS11, CP1, CP0, CS10, CS00, CP0,
      CS01, CP0, CS11, CP1, CP0, CP0, CS01, CP1, CP0, CP1, CP0, CS11, CP0, CP0, CS00, CS00,
      CS00, CP0, CS00, CS00, CP0, CS01, CP0]) ++ ([CP1, CP1, CP0, CS10, CS00, CP0, CP0, CS00,
      CS10, CS10, CP1, CP1, CP1, CP1, CP1, CP1, CP0, CS11, CP1, CP0, CP0, CS01, CP0, CP0, CS00,
      CS00, CS11, CP1, CP0, CS10, CS00, CS01] ++ [CP0, CS10, CS10, CS00, CS10, CS10, CS11, CP0,
      CS11, CP1, CP0, CS10, CP0, CP1, CP1, CP0, CS11, CP0, CS11, CP1, CP1, CP0, CS10, CS01, CP1,
      CP0, CS10, CS01, CP0, CS10, CS00, CP1])) ++ (([CP0, CS10, CP1, CP1, CP0, CS10, CP0, CS00,
      CS11, CP0, CS10, CS11, CP1, CP1, CP1, CP0, CS10, CP1, CP0, CS10, CP0, CP1, CP1, CP0, CP0,
      CP1, CP1, CP0, CS10, CP0, CS00, CP1] ++ [CP0, CS10, CP1, CP1, CP1, CP1, CP1, CP1, CP0,
      CS10, CP1, CP1, CP1, CP1, CP0, CP1, CP1, CP1, CP1, CP0, CP0, CS01, CP1, CP0, CS10, CS00,
      CP0, CP1, CP0, CS10, CS11, CP1]) ++ [CP0, CP0, CS01, CP0, CS10, CS11, CP0, CP0, CS01, CP1,
      CP1, CP1, CP1, CP0, CP1, CP0, CP0, CS00, CS00, CS11, CP0, CS10, CS01, CP0, CS10, CS01,
      CP1, CP0]))),
  ((((([CT, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT,
      (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0),
      CSP1, CT, (COC0 0), CSP1, CT, (COC0 0)] ++ [(CSC0 0), CSP1, CT, CT, CT, (COC0 0), CSP0,
      CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0)]) ++ ([CSP1, (COC1 0), CSP0, CT, (COC1 0),
      CSP0, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT] ++ [(COC1 0), CSP1, CT,
      (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CS11, CT])) ++ (([CT, CT, CT, CT, CT, CT,
      CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, CT, CT] ++ [(COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP0, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CT, (COC0 0), CSP0]) ++ ([CS10, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0), CSP0,
      CT, CT, CT, (COC0 0), CSP0, CT] ++ [CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0),
      (CSC1 0), CSP1, (COC1 0), CSP0, CT, CT]))) ++ ((([CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0)] ++ [CSP1, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0),
      (CSC1 0), CSP1, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0),
      CSP0, CT, CT, CT, CT, (COC0 0)]) ++ ([CSP0, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1,
      CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT,
      CT, (COC0 0), CSP0, CS11, CT, CT, CT, CT] ++ [CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, (COC0 0),
      CSP0, CT, CT, CT])) ++ (([(COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT,
      CT, CT, CT, CT, CT, CT, CT, CT, CT, (COC0 0), (CSC1 0), CSP1, CT, CT, (COC0 0), CSP0, CT,
      (COC1 0), CSP0, CT] ++ [CT, (COC0 0), CSP0, CS11, CT, CT, (COC0 0), CSP1, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0), CSP0, CT, (COC1 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), (CSC1 0), CSP1, CT, CT]) ++ ([CT, CT, (COC0 0), (CSC1 0), CSP1, CT, (COC0 0),
      CSP1, CT, CT, (COC0 0), CSP0, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, CP0, CT, CT, CT, CT, CT] ++ [CT, CT, CT, (COC0 0), CSP0, CT, CT, CT,
      CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), CSP0, CT, (COC1 0)])))) ++ (((([CSP0, CT, CT, CT, CT, CT, CT, CT, CT, CT,
      (COC0 0), (CSC1 0), CSP1, CT, CT, CT, CT, CT, (COC0 0), CSP0, CT, CT, CT, CT, (COC0 0),
      CSP0, CP1, (COC0 0), CSP1, CT, CT, CP1] ++ [CT, CT, (COC0 1), (CSC1 0), CSP1, CT, CT,
      (COC0 0), CSP0, CT, CT, CT, (COC0 0), CSP1, CT, (COC0 0), CSP0, CS10, (CEC 0), CSP0,
      (CEC 0), CSP0, CT, CT, CT, CT, CP0, CT, (COC1 0), CSP0, CP1, CT]) ++ ([CT, CT, CT, CT, CT,
      (COC0 0), CSP1, CT, CT, (COC0 0), CSP0, CT, (COC1 0), CSP0, CS10, CS01, CT, CT, CP0,
      (CEC 0), CSP1, CP0, CS11, CP1, (COC1 0), CSP1, CT, (COC0 0), CSP1, CT, CT,
      CT] ++ [(COC0 0), CSP1, (COC1 0), CSP1, CT, CT, CT, CP0, CT, CT, CP0, CT, CP0, CT,
      (COC1 0), CSP1, CT, CT, (COC0 0), CSP1, (COC1 0), CSP0, CS11, CT, CP1, CT, CT, CT,
      (COC0 0), CSP1, CT, (COC0 0)])) ++ (([CSP1, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1,
      (COC1 0), CSP0, CT, (COC1 0), CSP1, CT, CT, CT, CT, CT, CT, (COC0 0), CSP1, CT, CT, CT,
      CT, CT, CT, CT, CT, CT] ++ [CT, (COC0 0), CSP0, CT, CT, CP0, CT, CT, CT, CP1, CT, CT,
      (COC0 0), CSP0, CT, CP1, CT, (COC0 0), CSP0, CT, CT, CT, CT, CT, CT, CT, (COC0 0), CSP0,
      CS10, CS01, CT, CP0]) ++ ([CT, CP0, CT, CT, CP0, CS10, CS11, CP0, CS11, CP1, CP0, CP0,
      CS01, CP1, CP0, CS10, CS01, CP1, CP0, CP0, CS01, CP0, CP0, CS00, CS01, CP0, CP0, CS01,
      CP0, CP0, CS00, CS00] ++ [CS10, CS10, CS01, CP0, CS11, CP0, CS10, CS10, CP1, CP1, CP1,
      CP0, CS10, CP1, CP0, CS10, CS10, CP0, CS00, CS10, CS01, CP1, CP1, CP1, CP1, CP0, CP1, CP1,
      CP0, CS10, CP0, CS01]))) ++ ((([CP1, CP0, CP0, CP0, CS01, CP0, CS10, CS00, CS10, CS10,
      CP1, CP0, CS10, CS10, CS10, CS01, CP0, CS11, CP0, CS11, CP0, CS10, CS10, CP1, CP1, CP1,
      CP0, CS10, CP1, CP1, CP0, CS10] ++ [CP0, CS00, CS11, CP1, CP0, CS10, CP1, CP1, CP1, CP1,
      CP1, CP0, CS10, CS01, CP1, CP0, CS10, CS01, CP0, CP1, CP0, CP0, CS00, CS00, CS10, CP1,
      CP0, CS11, CP0, CS10, CS00, CS11]) ++ ([CP1, CP1, CP1, CP1, CP0, CP1, CP1, CP0, CP0, CS01,
      CP1, CP1, CP0, CS10, CP0, CS01, CP1, CP1, CP1, CP0, CS10, CS01, CP1, CP0, CP0, CS00, CS00,
      CP0, CP1, CP0, CS10, CP1] ++ [CP1, CP0, CS10, CP0, CS00, CS11, CP0, CS10, CS11, CP1, CP1,
      CP1, CP0, CS10, CP1, CP0, CS11, CP0, CP1, CP1, CP1, CP0, CP1, CP1, CP0, CS10, CP0, CS00,
      CP1, CP0, CS10, CP1])) ++ ([CP1, CP1, CP1, CP1, CP1, CP0, CS10, CP1, CP1, CP1, CP0, CP0,
      CP1, CP1, CP1, CP1, CP1, CP0, CS11, CP1, CP0, CS10, CS00, CP0, CP1, CP0, CS10, CS11, CP1,
      CP0, CP0, CP1] ++ [CP0, CS10, CP1, CP0, CS11, CP1, CP1, CP1, CP1, CP1, CP1, CP0, CP0, CP0,
      CS00, CS11, CP0, CS10, CS01, CP0, CS10, CS01, CP1, CP0]))))
]

def z2b_0108 : WordList := ((((([V, V, K, K, V, V, V, V, V, K, V, V, V, V, K, Q, V, V, V, V, V,
    V, V, V, V, V, V, V, V, V, K, V] ++ [V, V, V, K, Q, V, V, Q, V, V, Q, V, V, V, V, V, V, K,
    V, V, Q, V, V, V, V, V, V, K, V, V, V, V]) ++ ([V, V, V, K, V, V, Q, V, V, K, V, V, V, V, V,
    V, V, V, V, K, Q, V, V, V, V, V, V, V, V, V, V, V] ++ [V, V, V, K, V, Q, V, V, V, V, V, V,
    V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V])) ++ (([K, V, V, V, V, V, V, K,
    V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, K, Q, V, V, V, V, V, V, V] ++ [V, V, K, V, V,
    V, K, V, Q, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V]) ++ ([K, V,
    V, V, V, K, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, K, V, V, Q, V, V, K, V, V,
    V] ++ [V, K, Q, V, V, Q, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V,
    V, V, V, V]))) ++ ((([V, V, V, V, V, K, V, V, Q, V, V, V, V, V, V, V, V, V, K, Q, V, V, V,
    V, V, V, V, V, V, V, V, K] ++ [V, V, V, K, V, V, V, V, V, K, V, V, V, K, V, V, Q, V, V, V,
    V, K, V, V, K, V, V, Q, V, V, V, V]) ++ ([V, V, V, K, V, Q, V, V, V, V, V, V, V, V, K, V, V,
    V, V, V, V, V, V, V, V, V, V, V, V, K, V, V] ++ [V, V, V, V, V, K, V, V, V, V, K, V, V, V,
    V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, K])) ++ (([Q, V, V, V, V, K, V, V, Q, V,
    V, V, K, V, Q, V, V, K, V, V, V, V, V, K, V, V, Q, V, V, Q, V, V] ++ [V, V, V, V, V, V, K,
    Q, V, V, V, V, V, V, K, Q, V, V, V, K, V, V, V, K, V, V, V, K, V, V, V, V]) ++ ([V, V, V, V,
    K, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, K, V, V, V] ++ [V,
    V, V, V, V, V, V, V, V, K, V, V, Q, V, V, V, V, V, V, V, V, V, V, K, Q, V, V, V, V, V, V,
    V])))) ++ (((([K, V, V, V, V, V, K, V, V, K, V, V, V, V, V, V, K, V, Q, V, V, V, V, K, V, V,
    V, V, K, V, V, K] ++ [V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, K, V,
    V, V, K, V, V, Q, V, Q, K]) ++ ([V, V, V, V, V, V, Q, V, Q, V, V, K, V, V, V, V, K, V, Q, V,
    V, V, V, V, V, V, V, V, V, V, Q, V] ++ [V, V, K, V, Q, V, Q, V, V, V, V, V, K, V, V, K, V,
    V, V, V, V, V, V, V, K, V, Q, V, V, Q, V, V])) ++ (([V, V, V, V, V, K, V, V, V, V, V, V, V,
    V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, K, V, V, V] ++ [V, K, V, V, V, V, V, V, V, V,
    K, V, Q, K, V, V, V, V, V, V, V, Q, Q, V, Q, V, V, V, K, V, V, Q]) ++ ([K, V, V, V, K, V, V,
    K, K, V, V, K, V, V, K, K, Q, Q, K, V, Q, V, Q, Q, V, V, V, V, Q, V, V, Q] ++ [Q, V, K, Q,
    K, V, V, V, V, V, V, V, V, Q, V, K, V, V, V, V, K, V, Q, K, Q, Q, V, V, Q, Q, Q,
    K]))) ++ ((([V, Q, V, Q, V, Q, Q, V, V, V, V, Q, V, V, V, Q, V, K, Q, V, V, Q, V, V, V, V,
    V, V, Q, K, V, V] ++ [Q, K, V, V, V, V, K, K, Q, V, V, Q, V, Q, K, Q, V, V, V, V, V, V, V,
    V, V, K, V, V, V, Q, V, K]) ++ ([V, V, V, V, Q, K, V, V, V, K, K, V, V, V, Q, V, V, V, Q, V,
    K, Q, V, Q, Q, V, V, V, V, Q, V, V] ++ [Q, V, V, V, V, V, V, V, V, Q, V, K, V, V, Q, V, V,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V])) ++ ([V, V, Q, V, V, Q, K, V, V, V, Q, Q, V,
    V, V, V, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, K, Q] ++ [V, Q, K, V, Q, K, V, V]))))

def z2c_low_0108 : WordList := (((([Q, K, K, Q, Q, Q, Q, Q, K, Q, K, Q, K, K, K, Q, Q, K, K, Q,
    Q, Q, K, K, Q, Q, Q, Q, K, Q, K, Q] ++ [K, Q, Q, K, Q, Q, Q, K, Q, K, K, Q, Q, K, Q, K, K,
    Q, K, Q, Q, Q, Q, Q, K, Q, K, K, K, K, Q, K]) ++ ([K, Q, Q, K, Q, K, K, K, K, K, K, K, K, Q,
    Q, Q, K, K, K, Q, K, Q, K, K, K, Q, K, K, Q, K, Q, Q] ++ [Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q,
    Q, Q, K, Q, Q, K, Q, Q, Q, Q, K, K, Q, Q, K, K, Q, Q, K, K, K])) ++ (([K, Q, K, K, K, K, Q,
    K, Q, K, K, Q, Q, K, Q, Q, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, K, K, K] ++ [Q, Q, K, Q,
    Q, Q, K, K, Q, K, K, K, K, Q, K, Q, Q, K, K, Q, Q, Q, Q, K, Q, K, Q, Q, Q, Q, Q, K]) ++ ([K,
    Q, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, K, K,
    Q] ++ [K, Q, Q, Q, Q, Q, K, K, K, K, Q, K, K, Q, K, Q, K, Q, K, Q, Q, Q, K, K, Q, K, K, Q,
    Q, K, Q, K]))) ++ ((([Q, K, K, K, Q, K, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, K, K, Q, K,
    K, Q, Q, Q, Q, K, K, Q, Q] ++ [Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K,
    Q, Q, Q, K, Q, Q, K, Q, K, Q, Q, Q]) ++ ([K, Q, K, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K,
    Q, Q, Q, Q, Q, K, Q, K, Q, Q, Q, Q, Q, Q, Q] ++ [Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q,
    Q, Q, K, K, K, Q, Q, Q, K, K, Q, Q, Q, K, K, Q, Q, Q])) ++ (([Q, Q, K, K, Q, K, K, Q, Q, K,
    K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, K, K, Q, K, Q, Q, Q, Q] ++ [Q, K, Q, K, Q, Q, Q,
    Q, Q, K, K, Q, K, K, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q]) ++ ([K, K, Q, Q,
    Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, Q, Q, Q, K, K, K, Q] ++ [K,
    Q, Q, Q, K, K, Q, Q, Q, Q, K, Q, K, Q, Q, K, K, Q, Q, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q,
    Q]))))

def z2c_top_0108 : WordList := [Q,K,Q,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K]

def z2c_0108 : WordList := z2c_low_0108 ++ z2c_top_0108

theorem z2d_0108 :
    CanonRounds (evalWords z29_0108 default)
        (evalWords (prefix33Words ++ (z2b_0108 ++ (z2c_0108 ++ tail8Words))) default) :=
  evalCanonRounds_sound z2a_0108 z29_0108
      (prefix33Words ++ (z2b_0108 ++ (z2c_0108 ++ tail8Words)))
      (by decide +kernel)

theorem z2e_0108 :
    BGood (z2b_0108 ++ (z2c_0108 ++ tail8Words)) := by
  apply bGood_of_check z2b_0108 z2c_low_0108 z2c_top_0108 <;> decide +kernel

def zTail_0108 : WordList := [Q,Q,V,V,V,K,V,V,V,V,K,V,Q,Q,K,Q,Q,Q,K,Q,Q,Q]

def zCh_0108 : List Choice := [CP1, CT, CT, (COC0 0), CSP0, CT, CT, CT, (COC0 0), (CSC1 0), 
    CSP1, CP0, CP1, CP0, CP1, CP0]

def zBrOut_0108 : WordList := ([V, V, V, K, V, V, V, V, K, Q, V, V, V, V, V, V, V, Q, Q, Q, K, 
    Q, Q, Q, Q, Q, K, Q, K, Q, Q, Q] ++ [Q])

def zCk0_0108 : CCfg := ⟨D,0,[],[]⟩

def zCk1_0108 : CCfg := ⟨B, 0, (([1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]⟩

def zCk2_0108 : CCfg := ⟨B, 0, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]),
    [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]⟩

def zCk3_0108 : CCfg := ⟨B, 0, (([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1]) ++ [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    1]⟩

def zCk4_0108 : CCfg := ⟨C, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]) ++ [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
    1, 1, 0, 1, 0, 0, 1]), [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0,
    1]⟩

def zCk5_0108 : CCfg := ⟨C, 1, [0, 1], (([0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1,
    1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0] ++ [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1,
    0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1]) ++ ([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0] ++ [1, 0, 0, 0, 1, 0, 1, 0, 1,
    0, 0, 0, 1, 0, 1, 0, 1]))⟩

def zCkK0_0108 : CCfg := zCk0_0108

def zCkK1_0108 : CCfg := ⟨2,0,
    [1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 0, 1],
    [0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1]⟩

theorem zStK_1 : (c_to_cfg zCkK0_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK1_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK0_0108 800 = some zCkK1_0108)

def zCkK2_0108 : CCfg := ⟨0, 0, ([1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0] ++ [1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1]⟩

theorem zStK_2 : (c_to_cfg zCkK1_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK2_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK1_0108 800 = some zCkK2_0108)

def zCkK3_0108 : CCfg := ⟨0, 0, ([1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0] ++ [1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

theorem zStK_3 : (c_to_cfg zCkK2_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK3_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK2_0108 800 = some zCkK3_0108)

def zCkK4_0108 : CCfg := ⟨2, 0, [1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1], ([0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
    0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0] ++ [1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1])⟩

theorem zStK_4 : (c_to_cfg zCkK3_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK4_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK3_0108 800 = some zCkK4_0108)

def zCkK5_0108 : CCfg := ⟨1, 0, (([1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    1]), [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1]⟩

theorem zStK_5 : (c_to_cfg zCkK4_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK5_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK4_0108 800 = some zCkK5_0108)

def zCkK6_0108 : CCfg := ⟨3, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    1]), [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1]⟩

theorem zStK_6 : (c_to_cfg zCkK5_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK6_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK5_0108 800 = some zCkK6_0108)

def zCkK7_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 0, 1, 0, 0, 0, 1]⟩

theorem zStK_7 : (c_to_cfg zCkK6_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK7_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK6_0108 800 = some zCkK7_0108)

def zCkK8_0108 : CCfg := ⟨4, 0, (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

theorem zStK_8 : (c_to_cfg zCkK7_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK8_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK7_0108 800 = some zCkK8_0108)

def zCkK9_0108 : CCfg := ⟨1, 1, (([1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1]⟩

theorem zStK_9 : (c_to_cfg zCkK8_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK9_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK8_0108 800 = some zCkK9_0108)

def zCkK10_0108 : CCfg := ⟨1, 0, (([1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1]⟩

theorem zStK_10 : (c_to_cfg zCkK9_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK10_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK9_0108 800 = some zCkK10_0108)

def zCkK11_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]⟩

theorem zStK_11 : (c_to_cfg zCkK10_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK11_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK10_0108 800 = some zCkK11_0108)

def zCkK12_0108 : CCfg := ⟨1, 0, (([1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]) ++ ([1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0] ++ [0, 1])), [0, 1, 0, 0, 0, 0, 0, 1]⟩

theorem zStK_12 : (c_to_cfg zCkK11_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK12_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK11_0108 800 = some zCkK12_0108)

def zCkK13_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1]⟩

theorem zStK_13 : (c_to_cfg zCkK12_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK13_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK12_0108 800 = some zCkK13_0108)

def zCkK14_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1]⟩

theorem zStK_14 : (c_to_cfg zCkK13_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK14_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK13_0108 800 = some zCkK14_0108)

def zCkK15_0108 : CCfg := ⟨1, 1, (([1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1]) ++ [0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]⟩

theorem zStK_15 : (c_to_cfg zCkK14_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK15_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK14_0108 800 = some zCkK15_0108)

def zCkK16_0108 : CCfg := ⟨4, 0, ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1] ++ [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), ([0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1,
    1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1] ++ [0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1])⟩

theorem zStK_16 : (c_to_cfg zCkK15_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK16_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK15_0108 800 = some zCkK16_0108)

def zCkK17_0108 : CCfg := ⟨1, 1, (([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1]) ++ ([0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1] ++ [1, 0, 1, 1, 1, 0, 1, 0, 0, 1])),
    []⟩

theorem zStK_17 : (c_to_cfg zCkK16_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK17_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK16_0108 800 = some zCkK17_0108)

def zCkK18_0108 : CCfg := ⟨1, 0, (([1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1]) ++ [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0,
    1]⟩

theorem zStK_18 : (c_to_cfg zCkK17_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK18_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK17_0108 800 = some zCkK18_0108)

def zCkK19_0108 : CCfg := ⟨1, 0, (([1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0]) ++ [1, 0, 0, 1]), ([0, 1, 1, 0, 0, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0] ++ [0, 1, 0, 0, 0, 0,
    0, 1])⟩

theorem zStK_19 : (c_to_cfg zCkK18_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK19_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK18_0108 800 = some zCkK19_0108)

def zCkK20_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1] ++ [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
    0, 1]), [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0,
    1]⟩

theorem zStK_20 : (c_to_cfg zCkK19_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK20_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK19_0108 800 = some zCkK20_0108)

def zCkK21_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1]) ++ [0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0,
    1]⟩

theorem zStK_21 : (c_to_cfg zCkK20_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK21_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK20_0108 800 = some zCkK21_0108)

def zCkK22_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0,
    1]⟩

theorem zStK_22 : (c_to_cfg zCkK21_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK22_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK21_0108 800 = some zCkK22_0108)

def zCkK23_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    1]), [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0,
    1]⟩

theorem zStK_23 : (c_to_cfg zCkK22_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK23_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK22_0108 800 = some zCkK23_0108)

def zCkK24_0108 : CCfg := ⟨3, 1, (([0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0,
    1]⟩

theorem zStK_24 : (c_to_cfg zCkK23_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK24_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK23_0108 800 = some zCkK24_0108)

def zCkK25_0108 : CCfg := ⟨1, 0, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    1]), [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0,
    1]⟩

theorem zStK_25 : (c_to_cfg zCkK24_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK25_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK24_0108 800 = some zCkK25_0108)

def zCkK26_0108 : CCfg := ⟨4, 0, (([0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0,
    1]⟩

theorem zStK_26 : (c_to_cfg zCkK25_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK26_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK25_0108 800 = some zCkK26_0108)

def zCkK27_0108 : CCfg := ⟨1, 0, (([1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0,
    1]⟩

theorem zStK_27 : (c_to_cfg zCkK26_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK27_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK26_0108 800 = some zCkK27_0108)

def zCkK28_0108 : CCfg := ⟨2, 1, (([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0,
    1]⟩

theorem zStK_28 : (c_to_cfg zCkK27_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK28_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK27_0108 800 = some zCkK28_0108)

def zCkK29_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0,
    1]⟩

theorem zStK_29 : (c_to_cfg zCkK28_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK29_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK28_0108 800 = some zCkK29_0108)

def zCkK30_0108 : CCfg := ⟨2, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1]) ++ [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 1]⟩

theorem zStK_30 : (c_to_cfg zCkK29_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK30_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK29_0108 800 = some zCkK30_0108)

def zCkK31_0108 : CCfg := ⟨2, 1, (([0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1]) ++ [1, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 1]⟩

theorem zStK_31 : (c_to_cfg zCkK30_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK31_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK30_0108 800 = some zCkK31_0108)

def zCkK32_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), ([1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0,
    0] ++ [0, 0, 0, 1])⟩

theorem zStK_32 : (c_to_cfg zCkK31_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK32_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK31_0108 800 = some zCkK32_0108)

def zCkK33_0108 : CCfg := ⟨4, 0, (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1] ++ [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 1, 0]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0,
    0, 1]), [0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0,
    0, 1]⟩

theorem zStK_33 : (c_to_cfg zCkK32_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK33_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK32_0108 800 = some zCkK33_0108)

def zCkK34_0108 : CCfg := ⟨3, 1, (([1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), ([1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0,
    0] ++ [0, 0, 0, 1])⟩

theorem zStK_34 : (c_to_cfg zCkK33_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK34_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK33_0108 800 = some zCkK34_0108)

def zCkK35_0108 : CCfg := ⟨2, 1, (([0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1] ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 0, 1]), [0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0,
    0, 1]⟩

theorem zStK_35 : (c_to_cfg zCkK34_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK35_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK34_0108 800 = some zCkK35_0108)

def zCkK36_0108 : CCfg := ⟨3, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0,
    0, 1]⟩

theorem zStK_36 : (c_to_cfg zCkK35_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK36_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK35_0108 800 = some zCkK36_0108)

def zCkK37_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0,
    0, 1]⟩

theorem zStK_37 : (c_to_cfg zCkK36_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK37_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK36_0108 800 = some zCkK37_0108)

def zCkK38_0108 : CCfg := ⟨4, 0, [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 0, 0, 1], (([1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1,
    0, 1, 1, 0, 0, 1, 1, 0] ++ [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
    0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0]) ++ [0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0,
    0, 1])⟩

theorem zStK_38 : (c_to_cfg zCkK37_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK38_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK37_0108 800 = some zCkK38_0108)

def zCkK39_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0,
    0, 1]⟩

theorem zStK_39 : (c_to_cfg zCkK38_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK39_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK38_0108 800 = some zCkK39_0108)

def zCkK40_0108 : CCfg := ⟨1, 0, (([1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 0, 0, 1]), [1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0,
    0, 1]⟩

theorem zStK_40 : (c_to_cfg zCkK39_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK40_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK39_0108 800 = some zCkK40_0108)

def zCkK41_0108 : CCfg := ⟨2, 1, (([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1] ++ [1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0]) ++ [0, 1]), ([0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1] ++ [0, 1, 0, 1, 0, 1, 0, 1,
    0, 0, 0, 1])⟩

theorem zStK_41 : (c_to_cfg zCkK40_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK41_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK40_0108 800 = some zCkK41_0108)

def zCkK42_0108 : CCfg := ⟨2, 1, (([0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1]) ++ [1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 0, 1]), [0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1,
    0, 1]⟩

theorem zStK_42 : (c_to_cfg zCkK41_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK42_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK41_0108 800 = some zCkK42_0108)

def zCkK43_0108 : CCfg := ⟨4, 0, (([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1]) ++ [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0,
    1]), [1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0,
    1, 0, 1]⟩

theorem zStK_43 : (c_to_cfg zCkK42_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK43_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK42_0108 800 = some zCkK43_0108)

def zCkK44_0108 : CCfg := ⟨2, 1, ([0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1] ++ [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), ([0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1,
    1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0, 1] ++ [0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0,
    1, 0, 1])⟩

theorem zStK_44 : (c_to_cfg zCkK43_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK44_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK43_0108 800 = some zCkK44_0108)

def zCkK45_0108 : CCfg := ⟨4, 0, (([0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1]) ++ [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1,
    0, 1]⟩

theorem zStK_45 : (c_to_cfg zCkK44_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK45_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK44_0108 800 = some zCkK45_0108)

def zCkK46_0108 : CCfg := ⟨1, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1] ++ [0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]) ++ [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1]⟩

theorem zStK_46 : (c_to_cfg zCkK45_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK46_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK45_0108 800 = some zCkK46_0108)

def zCkK47_0108 : CCfg := ⟨4, 0, (([0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0,
    1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1]) ++ [0, 1, 0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1,
    0, 1]⟩

theorem zStK_47 : (c_to_cfg zCkK46_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK47_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK46_0108 800 = some zCkK47_0108)

def zCkK48_0108 : CCfg := ⟨1, 0, (([1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1,
    1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0,
    1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1]) ++ [0, 1, 0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 1]⟩

theorem zStK_48 : (c_to_cfg zCkK47_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK48_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK47_0108 800 = some zCkK48_0108)

def zCkK49_0108 : CCfg := ⟨1, 0, (([1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1] ++ [0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1]) ++ [0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 0, 1]), [0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1,
    0, 1]⟩

theorem zStK_49 : (c_to_cfg zCkK48_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK49_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK48_0108 800 = some zCkK49_0108)

def zCkK50_0108 : CCfg := ⟨2, 1, (([1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1,
    0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1] ++ [0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0,
    1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1]) ++ [0, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0,
    1, 1, 1, 0, 1, 0, 0, 1]), [0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1, 0, 1, 0, 0, 0, 1, 0, 1,
    0, 1]⟩

theorem zStK_50 : (c_to_cfg zCkK49_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK50_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK49_0108 800 = some zCkK50_0108)

def zCkK51_0108 : CCfg := ⟨2, 1, [0, 1], (([0, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0,
    1, 1, 0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0] ++ [0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1,
    1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 1, 0, 1, 1, 0, 0, 1, 1]) ++ ([0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0,
    0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 1, 1, 0, 0, 1, 0] ++ [1, 0, 0, 0, 1, 0, 1, 0,
    1, 0, 0, 0, 1, 0, 1, 0, 1]))⟩

theorem zStK_51 : (c_to_cfg zCkK50_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK51_0108) :=
    canonBMultiStepFast_sound (by decide)
      (by decide +kernel : canonBMultiStepFast zCkK50_0108 537 = some zCkK51_0108)

private theorem zBr0_0108 :
    BRIncs false 64 (evalWords (zTail_0108 ++ [K]) default) (evalWords zBrOut_0108 default) :=
  evalChoiceList_sound zCh_0108 false 64 (zTail_0108 ++ [K]) zBrOut_0108 (by decide +kernel)

theorem z0E_0108 : (c_to_cfg zCk0_0108) [canon_tm]⊢⁺ (cfgCanon (evalWords z29_0108 default)) := by
  have h_all : (c_to_cfg zCk0_0108) [canon_tm]⊢⁺ (c_to_cfg zCk5_0108) :=
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_1 zStK_2)
    (stepPlus_trans_canon zStK_3 zStK_4))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_5 zStK_6)
    (stepPlus_trans_canon zStK_7 zStK_8)))
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_9 zStK_10)
    (stepPlus_trans_canon zStK_11 zStK_12))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_13 zStK_14)
    (stepPlus_trans_canon zStK_15 zStK_16))))
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_17 zStK_18)
    (stepPlus_trans_canon zStK_19 zStK_20))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_21 zStK_22)
    (stepPlus_trans_canon zStK_23 zStK_24)))
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_25 zStK_26)
    (stepPlus_trans_canon zStK_27 zStK_28))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_29 zStK_30)
    (stepPlus_trans_canon zStK_31 zStK_32)))))
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_33 zStK_34)
    (stepPlus_trans_canon zStK_35 zStK_36))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_37 zStK_38)
    (stepPlus_trans_canon zStK_39 zStK_40)))
    (stepPlus_trans_canon
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_41 zStK_42)
    (stepPlus_trans_canon zStK_43 zStK_44))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_45 zStK_46)
    (stepPlus_trans_canon zStK_47 zStK_48))))
    (stepPlus_trans_canon
    (stepPlus_trans_canon zStK_49 zStK_50) zStK_51)))
  have heq : c_to_cfg zCk5_0108 =
      cfgLeft lh (w_pre +> ((d0 ++ t ++ (t ++ one)) +> evalWords zTail_0108 default)) := by
    simp only [c_to_cfg, C, WordCanonBR.C, zCk5_0108, zCL, cfgLeft, lh, w_pre, w_pre_rest,
        w_pre5_rest, w_pre3_rest, w_word,
      zTail_0108, evalWords, t, d0, d1, one, List.cons_append, List.nil_append, append_cons,
          append_nil, z00, zero_cons_default_canon,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  rw [heq] at h_all
  have h_br0 := zBr0_0108
  have h_br : BRIncs false 64 (evalWords zTail_0108 default) (evalWords zBrOut_0108 default) := by
    simpa only [evalWords_append,evalWords,d0_append_default] using! h_br0
  have h_side31 :
      Side ([.cj] ++ [.ch] ^ 31) (evalWords zTail_0108 default)
          (evalWords zBrOut_0108 default) := by
    simpa only [append_nil] using! numSide_of_brIncs h_br [] ([.cj] ++ [.ch] ^ 31) (Num.even 31)
  have h_side16 := side_of_seg seg_ch_16_to_31 h_side31
  have h_turn := stepPlus_word_pre_full h_side16
  have h_out : (d0 ++ t ++ t) +> evalWords zBrOut_0108 default = evalWords z29_0108 default := by
    simp only [zBrOut_0108, z29_0108, evalWords, t, d0, d1, List.cons_append, List.nil_append, 
        append_cons, append_nil]
  rw [h_out] at h_turn
  exact stepPlus_trans_canon h_all h_turn

theorem z2s_0108 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0108) N = 
        some (cfgCanon (evalWords (prefix33Words ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0108 with ⟨k1,_,hk1⟩
    rcases stepStar_of_canonRounds z2d_0108 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0108 ++ (z2c_0108 ++ tail8Words),
      multiStep_trans_canon canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0108⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases bGood_progress h_good with ⟨w',hStep,h_good'⟩
    rcases stepPlus_of_bStep hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      multiStep_trans_canon canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0108 : Fin 6 -> Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 2
  | 5 => 1

def zCfgMap_0108 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0108,⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

theorem zStepMap_0108 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0108 c) = (step canon_tm c).map zCfgMap_0108 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

theorem zMultiStepMap_0108 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0108 c) n = (multiStep canon_tm c n).map zCfgMap_0108 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ_canon,multiStep_succ_canon,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0108 c'

end Solution
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000



open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0108 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0108 (c_to_cfg zCk0_0108) = init [] := rfl
  have h_map := zMultiStepMap_0108 (c_to_cfg zCk0_0108) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := multiStep_add_Intermediate h_map
  rw [multiStep_succ_canon,hn] at h_some
  exact h_some

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end BusyBeaver.M_1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF
