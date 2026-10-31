/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RD_1RC---_1LD1LE_1LE0LC_1RF1LD_1RA0RF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RD_1RC---_1LD1LE_1LE0LC_1RF1LD_1RA0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RD_1RC---_1LD1LE_1LE0LC_1RF1LD_1RA0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

open WordCalculus Word WordCanonBR WordCanonBR.BRIncs WordCanonBR.Choice
namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
open WordCalculus Word WordCanonBR WordCanonBR.BRIncs WordCanonBR.Choice
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
local notation "zW" => List Word
local notation "zR" => List.replicate

def z29_0108 : zW := ([K,V,V,V,V,V,K,V,V,V,V,K,Q,V,V,V,V,V,V,V,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K] ++ [Q,Q,Q,Q])

def z2a_0108 : List (List Choice) := [
  [CS10,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CP1,CP0,CP1,CP1,CP0,CP0,CS01,CP1,CP0],
  ([CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT] ++ [CP0,CS11,CP0,CS11,CP0,CS10,CS10,CS00,CS00,CS10,CS10,CS10,CS10,CS10,CS11,CP0,CP0,CP1,CP0]),
  (([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CP0,CS10,CP1,CP1,CP1,CT,CT,CT,(COC0 0),CSP1,CP0,CS11,CP0,CP1,CP0,CP1,CP0,CP0,CS00,CS00,CS11]) ++ [CP1,CP0]),
  (([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT] ++ [CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10]) ++ [CS01,CT,CT,CP0,CS10,CS10,CP0,CS01,CP0,CP0,CS00,CP1,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP0,CP0,CS00,CS11,CP1,CP0]),
  (([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT] ++ [CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT]) ++ ([CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,CP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT] ++ [CP0,CS10,CS11,CP1,CP1,CP1,CP0,CS10,CS00,CP0,CP0,CP1,CP0,CS10,CS10,CS01,CP0,CS11,CP1,CP1,CP1,CP1,CP0,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP1,CP0])),
  ((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT] ++ [CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT]) ++ ([CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT] ++ [CT,CT,CP1,CT,CT,CT,CT,CP0,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CT,CP0,CP0,CP1,CP1])) ++ ([CP0,CS10,CS00,CP0,CP1,CP1,CP0,CP0,CS00,CP0,CS00,CP0,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS10,CP1,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP0,CP0] ++ [CP0,CS00,CS11,CP1,CP0])),
  ((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT] ++ [CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0)]) ++ ([CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT] ++ [CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT])) ++ (([CT,CT,CT,CT,CT,CT,CT,CT,CP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),(CSC1 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT] ++ [CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CP0,CP0,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CP0,CS00,CS00,CS01,CP0,CS11,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CS00,CS10]) ++ ([CS00,CP0,CS00,CS10,CS11,CP0,CP1,CP1,CP0,CS10,CS00,CS11,CP1,CP0,CS10,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CP0,CS01,CP1,CP1,CP1,CP1,CP0,CP1] ++ [CP0,CP0,CS00,CS00,CS11,CP0,CS10,CS01,CP1,CP0]))),
  (((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0)] ++ [CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,(COC0 0)]) ++ ([CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT] ++ [CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT])) ++ (([CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT] ++ [CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS10,CS00,(CEC 1)]) ++ ([CSP0,CP1,CT,CT,CT,CT,CP0,CS11,CT,CT,CP0,CT,CT,(COC0 0),CSP0,CT,CP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CS01,CT] ++ [CP0,CT,CT,CP0,CS10,CP1,CP0,CS11,CP0,CS10,CS01,CP0,CS11,CP1,CP1,CP0,CS10,CP0,CS00,CS10,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP1,CP0]))) ++ ([CP0,CP1,CP1,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CS10,CP0,CS00,CP1,CP0,CS10,CS11,CP1,CP0,CP0,CP1,CP0,CS10,CP1,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1] ++ [CP0,CP0,CP0,CS00,CS11,CP0,CS10,CS01,CP1,CP0])),
  (((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),CSP0,CT] ++ [CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1]) ++ ([CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT] ++ [CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT])) ++ (([CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0)] ++ [CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,CT]) ++ ([(COC0 0),CSP0,CT,CP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CP0,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 1),CSP1,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT]))) ++ ((([CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CT,CP1,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT] ++ [CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CP0,CT,CT,CP0,CS10,CS11,CP1,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS10,CP1,CP0,CS10,CS11,CP1,CP0,CS11,CP0]) ++ ([CP1,CP0,CS11,CP0,CS10,CS00,CP0,CS00,CS00,CS00,CS00,CP1,CP1,CP0,CP0,CS00,CP1,CP0,CS10,CP1,CP1,CP0,CP0,CP1,CP1,CP0,CS10,CP0,CS00,CS11,CP0,CS10] ++ [CP1,CP1,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP1,CP1,CP0,CP1,CP1,CP1,CP1,CP0,CP0,CP1,CP1,CP0,CS10,CP0,CP1,CP0,CS10,CS11,CP1,CP0,CP0,CS01,CP0])) ++ [CS10,CS11,CP0,CP0,CS01,CP1,CP1,CP1,CP1,CP0,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS10,CS11,CP1,CP0])),
  ((((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,(COC1 0)]) ++ ([CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0] ++ [CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT])) ++ (([CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT]) ++ ([CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT] ++ [CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0]))) ++ ((([CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT] ++ [CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CP1,CT,CT,CT,(COC0 0),CSP0,CT,CP1,(COC1 0),CSP1,CT,CT,CP1,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP1]) ++ ([CT,(COC0 1),CSP0,CS10,CS00,CS10,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS11,(COC1 0),CSP1,CT,CT,CT,CT,CT] ++ [(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CP1,CT,CT,(COC0 0),CSP0,CT,CP1,CT,(COC0 0),CSP0,CT,CT])) ++ (([CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CP1,CT,CT,CP0,CP0,CP1,CP0,CS11,CP0,CS11,CP0,CP1,CP0,CS11,CP1,CP0,CS10,CP1,CP0,CP0,CS00,CP0] ++ [CS01,CP0,CS10,CS01,CP0,CS11,CP0,CP1,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CS01,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CP0,CS00,CS00,CS01,CP0,CS10,CP0,CP1]) ++ ([CP1,CP0,CS10,CP0,CS00,CP1,CP0,CS11,CP1,CP1,CP0,CS10,CP0,CP1,CP0,CS11,CP0,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CS10,CP0,CS00,CP0,CS00,CP0,CP1,CP1] ++ [CP1,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP1,CP0,CP0,CP1,CP1,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CS10,CS00,CP0,CP1,CP0,CS10,CS11,CP1,CP0,CP0,CP1,CP0])))) ++ [CS10,CP1,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP0,CP0,CP0,CS00,CS11,CP0,CS10,CS11,CP1,CP0]),
  ((((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1] ++ [CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11]) ++ ([CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT] ++ [(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1])) ++ (([CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0)]) ++ ([(CSC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT] ++ [CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT]))) ++ ((([CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT] ++ [(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP1,CT,CT,CT]) ++ ([CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CP1] ++ [CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT])) ++ (([CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP1,CT,(COC0 0)] ++ [CSP1,CT,CT,(COC0 0),(CSC1 0),CSP0,CT,(COC1 1),CSP1,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),CSP1]) ++ ([CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),(CSC0 0),CSP0,CT,CT] ++ [CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CP0,CT,CT,CT,CP1,CT,CT,CT,CT,(COC0 0),CSP1])))) ++ ((([CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CP1,CT,CT,CP0,CP0,CS01,CP1,CP1,CP0,CP0,CP0,CS00,CS10,CS11,CP0,CS10] ++ [CP1,CP0,CS10,CS11,CP1,CP0,CS10,CS00,CP0,CS01,CP0,CS11,CP1,CP0,CP0,CS01,CP1,CP0,CP1,CP0,CS11,CP0,CP0,CS00,CS00,CS00,CP0,CS00,CS00,CP0,CS01,CP0]) ++ ([CP1,CP1,CP0,CS10,CS00,CP0,CP0,CS00,CS10,CS10,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CP0,CS01,CP0,CP0,CS00,CS00,CS11,CP1,CP0,CS10,CS00,CS01] ++ [CP0,CS10,CS10,CS00,CS10,CS10,CS11,CP0,CS11,CP1,CP0,CS10,CP0,CP1,CP1,CP0,CS11,CP0,CS11,CP1,CP1,CP0,CS10,CS01,CP1,CP0,CS10,CS01,CP0,CS10,CS00,CP1])) ++ (([CP0,CS10,CP1,CP1,CP0,CS10,CP0,CS00,CS11,CP0,CS10,CS11,CP1,CP1,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP1,CP1,CP0,CP0,CP1,CP1,CP0,CS10,CP0,CS00,CP1] ++ [CP0,CS10,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP1,CP1,CP0,CP1,CP1,CP1,CP1,CP0,CP0,CS01,CP1,CP0,CS10,CS00,CP0,CP1,CP0,CS10,CS11,CP1]) ++ [CP0,CP0,CS01,CP0,CS10,CS11,CP0,CP0,CS01,CP1,CP1,CP1,CP1,CP0,CP1,CP0,CP0,CS00,CS00,CS11,CP0,CS10,CS01,CP0,CS10,CS01,CP1,CP0]))),
  ((((([CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0)] ++ [(CSC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0)]) ++ ([CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT] ++ [(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT])) ++ (([CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT] ++ [(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0]) ++ ([CS10,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT] ++ [CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT]))) ++ ((([CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0)] ++ [CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0)]) ++ ([CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT] ++ [CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT])) ++ (([(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT] ++ [CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT]) ++ ([CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,CT,CT] ++ [CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0)])))) ++ (((([CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CP1,(COC0 0),CSP1,CT,CT,CP1] ++ [CT,CT,(COC0 1),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CS10,(CEC 0),CSP0,(CEC 0),CSP0,CT,CT,CT,CT,CP0,CT,(COC1 0),CSP0,CP1,CT]) ++ ([CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CS10,CS01,CT,CT,CP0,(CEC 0),CSP1,CP0,CS11,CP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT] ++ [(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CP0,CT,CT,CP0,CT,CP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS11,CT,CP1,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0)])) ++ (([CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT] ++ [CT,(COC0 0),CSP0,CT,CT,CP0,CT,CT,CT,CP1,CT,CT,(COC0 0),CSP0,CT,CP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CS01,CT,CP0]) ++ ([CT,CP0,CT,CT,CP0,CS10,CS11,CP0,CS11,CP1,CP0,CP0,CS01,CP1,CP0,CS10,CS01,CP1,CP0,CP0,CS01,CP0,CP0,CS00,CS01,CP0,CP0,CS01,CP0,CP0,CS00,CS00] ++ [CS10,CS10,CS01,CP0,CS11,CP0,CS10,CS10,CP1,CP1,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CP0,CS00,CS10,CS01,CP1,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CS10,CP0,CS01]))) ++ ((([CP1,CP0,CP0,CP0,CS01,CP0,CS10,CS00,CS10,CS10,CP1,CP0,CS10,CS10,CS10,CS01,CP0,CS11,CP0,CS11,CP0,CS10,CS10,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CS10] ++ [CP0,CS00,CS11,CP1,CP0,CS10,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CS01,CP1,CP0,CS10,CS01,CP0,CP1,CP0,CP0,CS00,CS00,CS10,CP1,CP0,CS11,CP0,CS10,CS00,CS11]) ++ ([CP1,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CP0,CS01,CP1,CP1,CP0,CS10,CP0,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP1,CP0,CP0,CS00,CS00,CP0,CP1,CP0,CS10,CP1] ++ [CP1,CP0,CS10,CP0,CS00,CS11,CP0,CS10,CS11,CP1,CP1,CP1,CP0,CS10,CP1,CP0,CS11,CP0,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CS10,CP0,CS00,CP1,CP0,CS10,CP1])) ++ ([CP1,CP1,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP1,CP0,CP0,CP1,CP1,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CS10,CS00,CP0,CP1,CP0,CS10,CS11,CP1,CP0,CP0,CP1] ++ [CP0,CS10,CP1,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP0,CP0,CS00,CS11,CP0,CS10,CS01,CP0,CS10,CS01,CP1,CP0]))))
]

def z2b_0108 : zW := ((((([V,V,K,K,V,V,V,V,V,K,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V] ++ [V,V,V,K,Q,V,V,Q,V,V,Q,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,V,K,V,V,V,V]) ++ ([V,V,V,K,V,V,Q,V,V,K,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V] ++ [V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V])) ++ (([K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V] ++ [V,V,K,V,V,V,K,V,Q,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V]) ++ ([K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,Q,V,V,K,V,V,V] ++ [V,K,Q,V,V,Q,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V]))) ++ ((([V,V,V,V,V,K,V,V,Q,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,K] ++ [V,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,Q,V,V,V,V,K,V,V,K,V,V,Q,V,V,V,V]) ++ ([V,V,V,K,V,Q,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V] ++ [V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K])) ++ (([Q,V,V,V,V,K,V,V,Q,V,V,V,K,V,Q,V,V,K,V,V,V,V,V,K,V,V,Q,V,V,Q,V,V] ++ [V,V,V,V,V,V,K,Q,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,V,K,V,V,V,K,V,V,V,V]) ++ ([V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V] ++ [V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V])))) ++ (((([K,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,Q,V,V,V,V,K,V,V,V,V,K,V,V,K] ++ [V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,K,V,V,V,K,V,V,Q,V,Q,K]) ++ ([V,V,V,V,V,V,Q,V,Q,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,Q,V] ++ [V,V,K,V,Q,V,Q,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,Q,V,V,Q,V,V])) ++ (([V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V] ++ [V,K,V,V,V,V,V,V,V,V,K,V,Q,K,V,V,V,V,V,V,V,Q,Q,V,Q,V,V,V,K,V,V,Q]) ++ ([K,V,V,V,K,V,V,K,K,V,V,K,V,V,K,K,Q,Q,K,V,Q,V,Q,Q,V,V,V,V,Q,V,V,Q] ++ [Q,V,K,Q,K,V,V,V,V,V,V,V,V,Q,V,K,V,V,V,V,K,V,Q,K,Q,Q,V,V,Q,Q,Q,K]))) ++ ((([V,Q,V,Q,V,Q,Q,V,V,V,V,Q,V,V,V,Q,V,K,Q,V,V,Q,V,V,V,V,V,V,Q,K,V,V] ++ [Q,K,V,V,V,V,K,K,Q,V,V,Q,V,Q,K,Q,V,V,V,V,V,V,V,V,V,K,V,V,V,Q,V,K]) ++ ([V,V,V,V,Q,K,V,V,V,K,K,V,V,V,Q,V,V,V,Q,V,K,Q,V,Q,Q,V,V,V,V,Q,V,V] ++ [Q,V,V,V,V,V,V,V,V,Q,V,K,V,V,Q,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,V])) ++ ([V,V,Q,V,V,Q,K,V,V,V,Q,Q,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,K,Q] ++ [V,Q,K,V,Q,K,V,V]))))

def z2c_low_0108 : zW := (((([Q,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,K,K,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,K,Q] ++ [K,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,K,K,K,Q,K]) ++ ([K,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,Q,Q,K,K,K,Q,K,Q,K,K,K,Q,K,K,Q,K,Q,Q] ++ [Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,K,K,K])) ++ (([K,Q,K,K,K,K,Q,K,Q,K,K,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,K] ++ [Q,Q,K,Q,Q,Q,K,K,Q,K,K,K,K,Q,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K]) ++ ([K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q] ++ [K,Q,Q,Q,Q,Q,K,K,K,K,Q,K,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K]))) ++ ((([Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,Q,K,K,Q,Q] ++ [Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q]) ++ ([K,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q] ++ [Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,Q])) ++ (([Q,Q,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,Q] ++ [Q,K,Q,K,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q]) ++ ([K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q,Q,K,K,K,Q] ++ [K,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]))))

def z2c_top_0108 : zW := [Q,K,Q,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,K,K]

def z2c_0108 : zW := z2c_low_0108 ++ z2c_top_0108

lemma z2d_0108 :
    loc_Rounds (zTs z29_0108 default) (zTs (zP33 ++ (z2b_0108 ++ (z2c_0108 ++ zTail8))) default) :=
  loc_z25 z2a_0108 z29_0108 (zP33 ++ (z2b_0108 ++ (z2c_0108 ++ zTail8))) (by decide +kernel)

lemma z2e_0108 :
    BGood (z2b_0108 ++ (z2c_0108 ++ zTail8)) := by
  apply loc_z28 z2b_0108 z2c_low_0108 z2c_top_0108 <;> decide +kernel

def zTail_0108 : zW := [Q,Q,V,V,V,K,V,V,V,V,K,V,Q,Q,K,Q,Q,Q,K,Q,Q,Q]

def zCh_0108 : List Choice := [CP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CP0,CP1,CP0,CP1,CP0]

def zBrOut_0108 : zW := ([V,V,V,K,V,V,V,V,K,Q,V,V,V,V,V,V,V,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,Q] ++ [Q])

def zCk0_0108 : CCfg := ⟨D,0,[],[]⟩

def zCk1_0108 : CCfg := ⟨B,0,(([1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1]) ++ [0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,0,0,0,0,0,0,1,0,0,0,1]⟩

def zCk2_0108 : CCfg := ⟨B,0,(([1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1]⟩

def zCk3_0108 : CCfg := ⟨B,0,(([1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1] ++ [0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1]) ++ [1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,0,0,1,0,1,0,0,0,1,0,0,0,1]⟩

def zCk4_0108 : CCfg := ⟨C,1,(([1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1] ++ [0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1]) ++ [0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1]⟩

def zCk5_0108 : CCfg := ⟨C,1,[0,1],(([0,0,0,0,1,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0] ++ [0,1,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,1,0,1,1,0,0,1,1]) ++ ([0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0] ++ [1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1]))⟩

def zCkK0_0108 : CCfg := zCk0_0108

def zCkK1_0108 : CCfg := ⟨2,0,[1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,0,1],[0,1,0,0,0,1,1,0,0,1,1,0,0,1,0,0,0,1,0,1]⟩

lemma zStK_1 : (c_to_cfg zCkK0_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK1_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK0_0108 800 = some zCkK1_0108)

def zCkK2_0108 : CCfg := ⟨0,0,([1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,1,1,0] ++ [1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,1,0,0,1,0,1,0,0,0,1]⟩

lemma zStK_2 : (c_to_cfg zCkK1_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK2_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK1_0108 800 = some zCkK2_0108)

def zCkK3_0108 : CCfg := ⟨0,0,([1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,0] ++ [1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,0,1,0,0,0,0,0,0,0,0,0,1]⟩

lemma zStK_3 : (c_to_cfg zCkK2_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK3_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK2_0108 800 = some zCkK3_0108)

def zCkK4_0108 : CCfg := ⟨2,0,[1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],([0,0,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0] ++ [1,0,0,0,1,0,0,0,1,0,1])⟩

lemma zStK_4 : (c_to_cfg zCkK3_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK4_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK3_0108 800 = some zCkK4_0108)

def zCkK5_0108 : CCfg := ⟨1,0,(([1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1]⟩

lemma zStK_5 : (c_to_cfg zCkK4_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK5_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK4_0108 800 = some zCkK5_0108)

def zCkK6_0108 : CCfg := ⟨3,1,(([1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,0,0,1,0,1]⟩

lemma zStK_6 : (c_to_cfg zCkK5_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK6_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK5_0108 800 = some zCkK6_0108)

def zCkK7_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1]) ++ [0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,0,1,0,0,0,1]⟩

lemma zStK_7 : (c_to_cfg zCkK6_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK7_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK6_0108 800 = some zCkK7_0108)

def zCkK8_0108 : CCfg := ⟨4,0,(([0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,1,1,0,0,1,0,0,0,0,0,0,0,0,0,0,0,1]⟩

lemma zStK_8 : (c_to_cfg zCkK7_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK8_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK7_0108 800 = some zCkK8_0108)

def zCkK9_0108 : CCfg := ⟨1,1,(([1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1]) ++ [0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1]⟩

lemma zStK_9 : (c_to_cfg zCkK8_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK9_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK8_0108 800 = some zCkK9_0108)

def zCkK10_0108 : CCfg := ⟨1,0,(([1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1]) ++ [0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,0,1,0,0,0,1,0,1]⟩

lemma zStK_10 : (c_to_cfg zCkK9_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK10_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK9_0108 800 = some zCkK10_0108)

def zCkK11_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1]) ++ [0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩

lemma zStK_11 : (c_to_cfg zCkK10_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK11_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK10_0108 800 = some zCkK11_0108)

def zCkK12_0108 : CCfg := ⟨1,0,(([1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1] ++ [0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1]) ++ ([1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0] ++ [0,1])),[0,1,0,0,0,0,0,1]⟩

lemma zStK_12 : (c_to_cfg zCkK11_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK12_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK11_0108 800 = some zCkK12_0108)

def zCkK13_0108 : CCfg := ⟨2,1,(([0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1] ++ [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,0,0,1,0,0,0,1]⟩

lemma zStK_13 : (c_to_cfg zCkK12_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK13_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK12_0108 800 = some zCkK13_0108)

def zCkK14_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1]) ++ [0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,1,0,1,0,1,0,1,0,0,0,1]⟩

lemma zStK_14 : (c_to_cfg zCkK13_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK14_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK13_0108 800 = some zCkK14_0108)

def zCkK15_0108 : CCfg := ⟨1,1,(([1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1]) ++ [0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1]⟩

lemma zStK_15 : (c_to_cfg zCkK14_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK15_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK14_0108 800 = some zCkK15_0108)

def zCkK16_0108 : CCfg := ⟨4,0,([0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1] ++ [1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),([0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1] ++ [0,0,0,1,0,0,0,1,0,1,0,1])⟩

lemma zStK_16 : (c_to_cfg zCkK15_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK16_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK15_0108 800 = some zCkK16_0108)

def zCkK17_0108 : CCfg := ⟨1,1,(([1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1] ++ [0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1]) ++ ([0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1] ++ [1,0,1,1,1,0,1,0,0,1])),[]⟩

lemma zStK_17 : (c_to_cfg zCkK16_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK17_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK16_0108 800 = some zCkK17_0108)

def zCkK18_0108 : CCfg := ⟨1,0,(([1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1] ++ [0,1,0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1]) ++ [1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,0,0,1,0,0,0,0,0,0,0,1]⟩

lemma zStK_18 : (c_to_cfg zCkK17_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK18_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK17_0108 800 = some zCkK18_0108)

def zCkK19_0108 : CCfg := ⟨1,0,(([1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1] ++ [1,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0]) ++ [1,0,0,1]),([0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,0] ++ [0,1,0,0,0,0,0,1])⟩

lemma zStK_19 : (c_to_cfg zCkK18_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK19_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK18_0108 800 = some zCkK19_0108)

def zCkK20_0108 : CCfg := ⟨2,1,(([0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1] ++ [0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,0,1]⟩

lemma zStK_20 : (c_to_cfg zCkK19_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK20_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK19_0108 800 = some zCkK20_0108)

def zCkK21_0108 : CCfg := ⟨2,1,(([0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1] ++ [0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1]) ++ [0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,0,0,1]⟩

lemma zStK_21 : (c_to_cfg zCkK20_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK21_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK20_0108 800 = some zCkK21_0108)

def zCkK22_0108 : CCfg := ⟨2,1,(([0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1] ++ [1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,1,0,0,0,1]⟩

lemma zStK_22 : (c_to_cfg zCkK21_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK22_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK21_0108 800 = some zCkK22_0108)

def zCkK23_0108 : CCfg := ⟨1,1,(([1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,1]⟩

lemma zStK_23 : (c_to_cfg zCkK22_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK23_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK22_0108 800 = some zCkK23_0108)

def zCkK24_0108 : CCfg := ⟨3,1,(([0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,1,1,0,0,1,0,0,0,1,0,0,0,1,0,0,0,0,0,1,0,1]⟩

lemma zStK_24 : (c_to_cfg zCkK23_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK24_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK23_0108 800 = some zCkK24_0108)

def zCkK25_0108 : CCfg := ⟨1,0,(([1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,0,0,1,0,0,0,1,0,1]⟩

lemma zStK_25 : (c_to_cfg zCkK24_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK25_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK24_0108 800 = some zCkK25_0108)

def zCkK26_0108 : CCfg := ⟨4,0,(([0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1]) ++ [0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,0,0,1,0,1,0,1,0,1,0,0,0,1,0,1]⟩

lemma zStK_26 : (c_to_cfg zCkK25_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK26_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK25_0108 800 = some zCkK26_0108)

def zCkK27_0108 : CCfg := ⟨1,0,(([1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1]) ++ [0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,1,0,1]⟩

lemma zStK_27 : (c_to_cfg zCkK26_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK27_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK26_0108 800 = some zCkK27_0108)

def zCkK28_0108 : CCfg := ⟨2,1,(([1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1] ++ [1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1]) ++ [0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,0,0,1,0,0,0,1,0,1,0,1,0,1]⟩

lemma zStK_28 : (c_to_cfg zCkK27_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK28_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK27_0108 800 = some zCkK28_0108)

def zCkK29_0108 : CCfg := ⟨2,1,(([0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1] ++ [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,1,0,0,1,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1]⟩

lemma zStK_29 : (c_to_cfg zCkK28_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK29_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK28_0108 800 = some zCkK29_0108)

def zCkK30_0108 : CCfg := ⟨2,1,(([1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1] ++ [0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1]) ++ [0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1]⟩

lemma zStK_30 : (c_to_cfg zCkK29_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK30_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK29_0108 800 = some zCkK30_0108)

def zCkK31_0108 : CCfg := ⟨2,1,(([0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1] ++ [0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1]) ++ [1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1]⟩

lemma zStK_31 : (c_to_cfg zCkK30_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK31_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK30_0108 800 = some zCkK31_0108)

def zCkK32_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,1,1,1,1] ++ [0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,0,0,1]),([1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,0] ++ [0,0,0,1])⟩

lemma zStK_32 : (c_to_cfg zCkK31_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK32_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK31_0108 800 = some zCkK32_0108)

def zCkK33_0108 : CCfg := ⟨4,0,(([0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1] ++ [0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,1]⟩

lemma zStK_33 : (c_to_cfg zCkK32_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK33_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK32_0108 800 = some zCkK33_0108)

def zCkK34_0108 : CCfg := ⟨3,1,(([1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1] ++ [0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,0,0,1]),([1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,0,0,0,0,1,0,1,0,0] ++ [0,0,0,1])⟩

lemma zStK_34 : (c_to_cfg zCkK33_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK34_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK33_0108 800 = some zCkK34_0108)

def zCkK35_0108 : CCfg := ⟨2,1,(([0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1] ++ [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,1]⟩

lemma zStK_35 : (c_to_cfg zCkK34_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK35_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK34_0108 800 = some zCkK35_0108)

def zCkK36_0108 : CCfg := ⟨3,1,(([1,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,1,1,0,0,1,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,1]⟩

lemma zStK_36 : (c_to_cfg zCkK35_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK36_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK35_0108 800 = some zCkK36_0108)

def zCkK37_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,1]⟩

lemma zStK_37 : (c_to_cfg zCkK36_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK37_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK36_0108 800 = some zCkK37_0108)

def zCkK38_0108 : CCfg := ⟨4,0,[0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],(([1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0] ++ [0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0]) ++ [0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,0,0,1])⟩

lemma zStK_38 : (c_to_cfg zCkK37_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK38_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK37_0108 800 = some zCkK38_0108)

def zCkK39_0108 : CCfg := ⟨1,1,(([1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,1,0,1,0,0,0,1]⟩

lemma zStK_39 : (c_to_cfg zCkK38_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK39_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK38_0108 800 = some zCkK39_0108)

def zCkK40_0108 : CCfg := ⟨1,0,(([1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1] ++ [1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,1,0,1,0,0,0,1]⟩

lemma zStK_40 : (c_to_cfg zCkK39_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK40_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK39_0108 800 = some zCkK40_0108)

def zCkK41_0108 : CCfg := ⟨2,1,(([0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1] ++ [1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0]) ++ [0,1]),([0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,0,0,1] ++ [0,1,0,1,0,1,0,1,0,0,0,1])⟩

lemma zStK_41 : (c_to_cfg zCkK40_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK41_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK40_0108 800 = some zCkK41_0108)

def zCkK42_0108 : CCfg := ⟨2,1,(([0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1] ++ [0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1]) ++ [1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,0,1,1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,1]⟩

lemma zStK_42 : (c_to_cfg zCkK41_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK42_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK41_0108 800 = some zCkK42_0108)

def zCkK43_0108 : CCfg := ⟨4,0,(([0,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1] ++ [1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1]) ++ [1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1]⟩

lemma zStK_43 : (c_to_cfg zCkK42_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK43_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK42_0108 800 = some zCkK43_0108)

def zCkK44_0108 : CCfg := ⟨2,1,([0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1] ++ [1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),([0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1] ++ [0,0,0,1,0,1,0,1,0,0,0,0,0,1,0,1])⟩

lemma zStK_44 : (c_to_cfg zCkK43_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK44_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK43_0108 800 = some zCkK44_0108)

def zCkK45_0108 : CCfg := ⟨4,0,(([0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1]) ++ [0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,0,0,1,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,1]⟩

lemma zStK_45 : (c_to_cfg zCkK44_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK45_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK44_0108 800 = some zCkK45_0108)

def zCkK46_0108 : CCfg := ⟨1,1,(([1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1] ++ [0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1]) ++ [0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,1,0,1,0,0,0,0,0,0,0,1,0,1,0,0,0,1,0,1]⟩

lemma zStK_46 : (c_to_cfg zCkK45_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK46_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK45_0108 800 = some zCkK46_0108)

def zCkK47_0108 : CCfg := ⟨4,0,(([0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1] ++ [0,1,0,1,0,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1]) ++ [0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,1,0,1]⟩

lemma zStK_47 : (c_to_cfg zCkK46_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK47_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK46_0108 800 = some zCkK47_0108)

def zCkK48_0108 : CCfg := ⟨1,0,(([1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1] ++ [1,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1]) ++ [0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[1,0,0,1,0,1,0,1,0,1,0,0,0,0,0,0,0,1,0,1,0,1]⟩

lemma zStK_48 : (c_to_cfg zCkK47_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK48_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK47_0108 800 = some zCkK48_0108)

def zCkK49_0108 : CCfg := ⟨1,0,(([1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1] ++ [0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1]) ++ [0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,0,0,0,0,1,0,0,0,1,0,1,0,1]⟩

lemma zStK_49 : (c_to_cfg zCkK48_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK49_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK48_0108 800 = some zCkK49_0108)

def zCkK50_0108 : CCfg := ⟨2,1,(([1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1] ++ [0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1]) ++ [0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1]),[0,1,1,0,0,1,0,1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1]⟩

lemma zStK_50 : (c_to_cfg zCkK49_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK50_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK49_0108 800 = some zCkK50_0108)

def zCkK51_0108 : CCfg := ⟨2,1,[0,1],(([0,0,0,0,1,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0] ++ [0,1,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,1,0,1,1,0,0,1,1]) ++ ([0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0] ++ [1,0,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1]))⟩

lemma zStK_51 : (c_to_cfg zCkK50_0108) [canon_tm]⊢⁺ (c_to_cfg zCkK51_0108) := zTcF (by decide) (by decide +kernel : zCmF zCkK50_0108 537 = some zCkK51_0108)

private lemma zBr0_0108 : BRIncs false 64 (zTs (zTail_0108 ++ [K]) default) (zTs zBrOut_0108 default) :=
  loc_z21 zCh_0108 false 64 (zTail_0108 ++ [K]) zBrOut_0108 (by decide +kernel)

lemma z0E_0108 : (c_to_cfg zCk0_0108) [canon_tm]⊢⁺ (zCf (zTs z29_0108 default)) := by
  have h_all : (c_to_cfg zCk0_0108) [canon_tm]⊢⁺ (c_to_cfg zCk5_0108) := (zPt (zPt (zPt (zPt (zPt (zPt zStK_1 zStK_2) (zPt zStK_3 zStK_4)) (zPt (zPt zStK_5 zStK_6) (zPt zStK_7 zStK_8))) (zPt (zPt (zPt zStK_9 zStK_10) (zPt zStK_11 zStK_12)) (zPt (zPt zStK_13 zStK_14) (zPt zStK_15 zStK_16)))) (zPt (zPt (zPt (zPt zStK_17 zStK_18) (zPt zStK_19 zStK_20)) (zPt (zPt zStK_21 zStK_22) (zPt zStK_23 zStK_24))) (zPt (zPt (zPt zStK_25 zStK_26) (zPt zStK_27 zStK_28)) (zPt (zPt zStK_29 zStK_30) (zPt zStK_31 zStK_32))))) (zPt (zPt (zPt (zPt (zPt zStK_33 zStK_34) (zPt zStK_35 zStK_36)) (zPt (zPt zStK_37 zStK_38) (zPt zStK_39 zStK_40))) (zPt (zPt (zPt zStK_41 zStK_42) (zPt zStK_43 zStK_44)) (zPt (zPt zStK_45 zStK_46) (zPt zStK_47 zStK_48)))) (zPt (zPt zStK_49 zStK_50) zStK_51)))
  have heq : c_to_cfg zCk5_0108 = zCL lh (w_pre +> ((d0 ++ t ++ (t ++ one)) +> zTs zTail_0108 default)) := by
    simp only [c_to_cfg,C,WordCanonBR.C,zCk5_0108,zCL,lh,w_pre,w_pre_rest,w_pre5_rest,w_pre3_rest,w_word,
      zTail_0108,zTs,t,d0,d1,one,List.cons_append,List.nil_append,append_cons,append_nil,z00,
      Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  rw [heq] at h_all
  have h_br0 := zBr0_0108
  have h_br : BRIncs false 64 (zTs zTail_0108 default) (zTs zBrOut_0108 default) := by
    simpa only [z15,zTs,zDd] using! h_br0
  have h_side31 : Side ([.cj] ++ [.ch] ^ 31) (zTs zTail_0108 default) (zTs zBrOut_0108 default) := by
    simpa only [append_nil] using! loc_z2o h_br [] ([.cj] ++ [.ch] ^ 31) (Num.even 31)
  have h_side16 := zSc z108_seg h_side31
  have h_turn := zW_pre_full h_side16
  have h_out : (d0 ++ t ++ t) +> zTs zBrOut_0108 default = zTs z29_0108 default := by
    simp only [zBrOut_0108,z29_0108,zTs,t,d0,d1,List.cons_append,List.nil_append,append_cons,append_nil]
  rw [h_out] at h_turn
  exact zPt h_all h_turn

lemma z2s_0108 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0108) N = some (zCf (zTs (zP33 ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0108 with ⟨k1,_,hk1⟩
    rcases loc_z2r z2d_0108 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0108 ++ (z2c_0108 ++ zTail8),
      zMt canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0108⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases loc_z1N h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2q hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      zMt canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0108 : Fin 6 -> Fin 6
  | 0 => 3
  | 1 => 4
  | 2 => 5
  | 3 => 0
  | 4 => 2
  | 5 => 1

def zCfgMap_0108 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0108,⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

lemma zStepMap_0108 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0108 c) = (step canon_tm c).map zCfgMap_0108 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

lemma zMultiStepMap_0108 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0108 c) n = (multiStep canon_tm c n).map zCfgMap_0108 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs,zMs,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0108 c'

end Solution
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

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
  have h_some := zIm h_map
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RD_1RCHHH_1LD1LE_1LE0LC_1RF1LD_1RA0RF
