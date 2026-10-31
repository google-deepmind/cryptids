/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB---_1LC1LD_1LD0LB_1RE1LC_1RF0RE_1RA0RC` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB---_1LC1LD_1LD0LB_1RE1LC_1RF0RE_1RA0RC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1LC1LD_1LD0LB_1RE1LC_1RF0RE_1RA0RC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB---_1LC1LD_1LD0LB_1RE1LC_1RF0RE_1RA0RC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open Counter

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

def z29_0581 : zW := [V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,Q,K,K,V,K,K,Q,K,Q,Q,K,K,K,K,K,K,Q]

def z2a_0581 : List (List Choice) := [
  [CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,(COC0 0),CSP1,CT,CT,CP0,(CEC 0),CSP0,CS10,CP0,CS01,CP0,CS10,CS10,CS00,CS10,CS10,CP0],
  [CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),(CSC0 0),CSP1,CP0,CP1,(COC0 0),CSP0,CP1,CP0,CS10,CS11,CP0,CS10,CP1,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CP1,(COC1 0),CSP1,CT,CT,CT,CP0,CP0,CP0,CP0,CP0,CS00,CP0,CP0,CP1,CP0,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CP0,CS00,CS00,CP1,CP0,CS10,CS10,CS10,CP1,CP0,CS10,CP0,CS00,CP0,CP1,CP0,CS10,CP0,CP0,CP1,CP0,CS10,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,CP1,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CT,CP0,CP1,CP0,CS11,CP0,CS10,CS00,CP0,CS00,CP1,CP1,CP1,CP0,CS11,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CS01,CP0,CS10,CS00,CS10,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 1),CSP0,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CP0,CS11,(COC0 0),CSP0,CT,CT,CP0,CS10,CS11,CP1,CP0,CS10,CS00,CS00,CP0,CS00,CS10,CP0,CS00,CS10,CS00,CS10,CS11,CP0,CS10,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CS01,CP0,CS10,CP1,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CP0,CT,CT,CT,CT,CP1,CT,CT,CP0,(CEC 0),CSP0,CS11,(COC1 0),CSP0,CP0,CP1,CT,CP0,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CP1,CT,CT,CP0,CS11,CP1,CP1,CP1,CP0,CP1,CP0,CP1,CP0,CS10,CS11,CP1,CP1,CP0,CP0,CS00,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CP1,CT,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CT,CP0,CP1,CP0,CS10,CS10,CP0,CS01,CP0,CP1,CP1,CP0,CS10,CS00,CS11,CP1,CP0,CP0,CS00,CS00,CS00,CS00,CS01,CP0,CP0,CS00,CS00,CS00,CP0,CS00,CS00,CP0,CP0,CP0,CS00,CS10,CS00,CP0,CP1,CP1,CP1,CP0,CP1,CP0,CS10,CS10,CS10,CS11,CP0,CS10,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CP1,CP0,CS10,CP0,CS01,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CP1,(COC1 0),CSP0,CT,CT,CT,CT,CP0,CS11,CT,CT,(COC0 0),CSP0,CS10,CS00,CS10,CS10,CT,(COC1 0),CSP0,CS10,(CEC 0),CSP0,CS10,CT,CT,(COC0 0),CSP0,CP0,CT,CT,CT,CT,CT,CT,CT,CP1,CP1,CT,CP0,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CP1,CT,CT,CP0,CS10,CP0,CS00,CS00,CP0,CP0,CP0,CS01,CP0,CS10,CS00,CS01,CP0,CP0,CS00,CS00,CS10,CS10,CS00,CS00,CS00,CS10,CS00,CS01,CP1,CP1,CP0,CS11,CP0,CP0,CP1,CP1,CP0,CS10,CS00,CS10,CS00,CS10,CS00,CS10,CS00,CS00,CS10,CS00,CS00,CS00,CS10,CS10,CP0,CP0,CP0,CP0,CP0,CP1,CP0,CP1,CP0,CS10,CS11,CP1,CP1,CP0,CP0,CS00,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CS01,CP0,CS10,CS00,CS10,CP0,CS01,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CP0,CP1,(COC0 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS10,CT,CT,(COC0 0),CSP0,CT,CP0,CS10,CT,(COC1 0),CSP0,CS10,CS11,CP0,CS10,CS00,CP0,CS00,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CP0,CP0,CP0,CP0,CS00,CP0,CS00,CS00,CP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CP1,CT,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CP0,CS11,(COC0 0),CSP0,CT,CP0,CT,CT,CP0,CS10,CS10,CS10,CS01,CP1,CP1,CP1,CP0,CS11,CP1,CP0,CP0,CS00,CS00,CP0,CS00,CS10,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP0,CS01,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CP0,CS01,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CS00,CS01,CP0,CS10,CP0,CP0,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CS10,CS00,CS01,CP0,CS10,CS11,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CS01,CP0,CS10,CP1,CP0,CS10,CS11,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CP1,CT,(COC0 1),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CP0,CT,CT,CT,CT,CT,CT,CP1,CP0,CT,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,(CEC 0),CSP0,CP0,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CP0,(CEC 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 1),CSP1,CP0,CS10,CT,CP1,CT,CT,CT,(COC0 1),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CP1,CT,CP1,CT,CT,CP0,CS10,CS11,CP0,CS10,CS10,CP1,CP1,CP0,CS10,CS00,CS11,CP0,CS10,CS10,CS00,CS01,CP0,CP1,CP0,CP0,CP0,CS00,CS10,CS10,CS00,CS10,CS00,CS10,CS00,CS10,CS10,CS10,CS00,CS10,CS10,CS00,CS10,CS10,CS00,CP0,CS01,CP0,CS10,CP0,CP1,CP0,CS11,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CS00,CS00,CP0,CS00,CS10,CS11,CP1,CP0,CP1,CP1,CP1,CP0,CS10,CP1,CP0,CP1,CP0,CS11,CP0,CS11,CP1,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CP0,CS01,CP0,CS11,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CS10,CS00,CP0,CP0,CP0,CP0,CP1,CP0,CP1,CP0,CS10,CS11,CP1,CP1,CP0,CP0,CS00,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CP0,CP0,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS10,CS11,CP1,CP0]
]

def z2b_0581 : zW := [V,V,V,V,V,V,K,V,V,Q,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,K,V,Q,V,K,V,V,V,K,V,Q,V,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,K,V,V,Q,V,V,K,V,Q,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,K,V,V,V,K,V,V,Q,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,K,V,V,Q,V,V,V,V,K,V,Q,V,V,V,V,V,V,K,Q,V,V,Q,V,V,K,V,V,V,K,V,Q,V,V,V,V,K,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,K,V,V,V,K,V,V,Q,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,Q,V,V,V,V,K,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,Q,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,K,K,V,V,V,V,V,V,V,V,V,V,Q,Q,V,Q,Q,V,V,V,Q,K,Q,V,Q,Q,K,K,V,V,V,V,V,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,V,K,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,Q,K,K,V,K,Q,Q,V,V,V,V,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,Q,V,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,Q,K,V,V,V,V,V,V,V,V,Q,Q,V,V,V,V,K,K,V,V,V,Q,K,V,Q,V,V,Q,V,V,Q,V,V,V,V,V,K,V,Q,Q,V,Q,Q,V,V]

def z2c_low_0581 : zW := [Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,K,K,K,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,K,K,Q,K,Q,K,Q,K,K,Q,K,K,Q,K,K,Q,K,K,K,K,K,Q,K,K,K,Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,K,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,Q,Q,K,K,Q,Q,Q,K]

def z2c_top_0581 : zW := [K,Q,K,Q,K,Q,Q,Q,K,K,Q,K,Q,Q,K,K]

def z2c_0581 : zW := z2c_low_0581 ++ z2c_top_0581

lemma z2d_0581 :
    loc_Rounds (zTs z29_0581 default) (zTs (zP33 ++ (z2b_0581 ++ (z2c_0581 ++ zTail8))) default) :=
  loc_z25 z2a_0581 z29_0581 (zP33 ++ (z2b_0581 ++ (z2c_0581 ++ zTail8))) (by decide +kernel)

lemma z2e_0581 :
    BGood (z2b_0581 ++ (z2c_0581 ++ zTail8)) := by
  apply loc_z28 z2b_0581 z2c_low_0581 z2c_top_0581 <;> decide +kernel

def zPre_0581 : zW := [V,V,V,V,V,V,K,V,V,K,V,V,V,Q,V,V,Q,K,K,V,K,K,Q,K,Q,Q,K,K,K,K,K,K,K]

def zCk0_0581 : CCfg := ⟨F,0,[],[]⟩

def zCk1_0581 : CCfg := ⟨B,0,[1,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[1,0,0,0,0,1,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,0,0,1]⟩

def zCk2_0581 : CCfg := ⟨E,0,[0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0,1,0,1,0,1,0,0,0,1,0,1]⟩

def zCk3_0581 : CCfg := ⟨E,0,[0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,1]⟩

def zCk4_0581 : CCfg := ⟨E,0,[0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,1,1,0,0,0,0,0,0,1,1,0,0,0,0,1,0,0,0,0,0,1,0,1,0,1,0,1,0,1]⟩

def zCk5_0581 : CCfg := ⟨A,0,[1,1,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1],[1,1,0,0,0,0,0,0,0,0,1,0,0,0,1]⟩

def zCk6_0581 : CCfg := ⟨C,1,[0,1],[0,0,0,0,1,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,0,0,0,0,0,1,1,0,0,0,0,0,0,1,0,0,0,1,0,1]⟩

private lemma zCk_step1_0581 : (c_to_cfg zCk0_0581) [canon_tm]⊢⁺ (c_to_cfg zCk1_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk0_0581 10000 = some zCk1_0581)

private lemma zCk_step2_0581 : (c_to_cfg zCk1_0581) [canon_tm]⊢⁺ (c_to_cfg zCk2_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk1_0581 10000 = some zCk2_0581)

private lemma zCk_step3_0581 : (c_to_cfg zCk2_0581) [canon_tm]⊢⁺ (c_to_cfg zCk3_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk2_0581 10000 = some zCk3_0581)

private lemma zCk_step4_0581 : (c_to_cfg zCk3_0581) [canon_tm]⊢⁺ (c_to_cfg zCk4_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk3_0581 10000 = some zCk4_0581)

private lemma zCk_step5_0581 : (c_to_cfg zCk4_0581) [canon_tm]⊢⁺ (c_to_cfg zCk5_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk4_0581 10000 = some zCk5_0581)

private lemma zCk_step6_0581 : (c_to_cfg zCk5_0581) [canon_tm]⊢⁺ (c_to_cfg zCk6_0581) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk5_0581 1601 = some zCk6_0581)

private lemma zPre_side_0581 : Side ([Call.ch] ^ 16) (zTs zPre_0581 default) (zTs z29_0581 default) :=
  zHExec_ok zPre_0581 16 z29_0581 (by decide +kernel)

lemma z0E_0581 : (c_to_cfg zCk0_0581) [canon_tm]⊢⁺ (zCf (zTs z29_0581 default)) := by
  have h_all := zPt zCk_step1_0581 (zPt zCk_step2_0581 (zPt zCk_step3_0581 (zPt zCk_step4_0581 (zPt zCk_step5_0581 zCk_step6_0581))))
  have heq : c_to_cfg zCk6_0581 = zCL lh (w_pre +> zTs zPre_0581 default) := by
    simp only [c_to_cfg,C,WordCanonBR.C,zCk6_0581,zCL,lh,w_pre,w_pre_rest,w_pre5_rest,w_pre3_rest,w_word,
      zPre_0581,zTs,t,d0,d1,one,List.cons_append,List.nil_append,append_cons,append_nil,z00,
      Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  rw [heq] at h_all
  exact zPt h_all (zW_pre_full zPre_side_0581)

lemma z2s_0581 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0581) N = some (zCf (zTs (zP33 ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0581 with ⟨k1,_,hk1⟩
    rcases loc_z2r z2d_0581 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0581 ++ (z2c_0581 ++ zTail8),
      zMt canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0581⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases loc_z1N h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2q hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      zMt canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0581 : Fin 6 -> Fin 6
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 5
  | 4 => 1
  | 5 => 0

def zCfgMap_0581 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0581,⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

lemma zStepMap_0581 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0581 c) = (step canon_tm c).map zCfgMap_0581 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

lemma zMultiStepMap_0581 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0581 c) n = (multiStep canon_tm c n).map zCfgMap_0581 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs,zMs,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0581 c'

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0581 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0581 (c_to_cfg zCk0_0581) = init [] := rfl
  have h_map := zMultiStepMap_0581 (c_to_cfg zCk0_0581) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := zIm h_map
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RBHHH_1LC1LD_1LD0LB_1RE1LC_1RF0RE_1RA0RC
