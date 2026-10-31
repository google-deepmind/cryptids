/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LA_1LA0LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LA_1LA0LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LA_1LA0LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LF_1RC0RB_1RD0RF_1RE---_1LF1LA_1LA0LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => none
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

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

def z29_0813 : zW := [V,V,V,V,V,V,V,K,V,V,Q,V,V,Q,K,V,V,V,K,V,Q,Q,Q,V,K,Q,Q,K,Q,Q,K,K,K,K,K,K,Q]

def z2a_0813 : List (List Choice) := [
  [CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CP1,(COC1 0),CSP0,CS11,CP0,CS11,CP0,CS10,CS10,CS00,CS10,CS10,CP0],
  [CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CP0,CP1,(COC0 0),CSP0,CS10,CS10,CP0,CP1,CP0,CS10,CP1,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CT,(COC0 0),CSP1,CT,CT,CT,CP0,CP1,CP0,CS10,CS11,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CP1,CP0,CS11,CP1,CP0,CP0,CP0,CP0,CP1,CP0,CP0,CP0,CS01,CP1,CP0,CS10,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP0,CT,CT,CP0,CS10,CP0,CS00,CS00,CS10,CS00,CP1,CP0,CS10,CP0,CS00,CS00,CP0,CS00,CS10,CS00,CS00,CS10,CS10,CP0,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS10,CP0,CT,(COC1 0),CSP1,(COC1 0),CSP0,(CEC 0),CSP0,CP0,CS00,CP1,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,CT,CP0,CS10,CS10,CS10,CS00,CS11,CP0,CS10,CP1,CP0,CS10,CS10,CS10,CS11,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CP1,CP0,CS10,CP1,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CP1,CP0,CS11,(COC0 0),CSP1,CT,CT,CP1,CP1,CT,CT,CT,CT,(COC0 1),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CP1,CT,CT,CP0,CS10,CS11,CP0,CS10,CS10,CP0,CS00,CS10,CP0,CP0,CS00,CS10,CP1,CP1,CP0,CS11,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CS00,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CP1,CT,CP1,(COC1 0),CSP0,CS11,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CP0,CS10,CT,CT,CT,CT,(COC0 1),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CT,CP0,CS10,CP0,CS00,CS00,CP0,CS00,CS10,CS01,CP0,CS11,CP1,CP0,CS11,CP1,CP0,CP0,CS00,CS01,CP1,CP1,CP0,CP0,CP1,CP1,CP1,CP0,CP1,CP1,CP0,CS11,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CS00,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CS01,CP1,CP0,CS10,CP0,CS01,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,(COC1 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,(CEC 0),(CSC0 1),CSP1,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CP0,CS10,CT,CT,CT,CT,(COC0 1),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP0,CT,CP0,CT,CT,CP0,CS10,CS10,CS10,CS00,CP0,CS00,CS00,CS01,CP0,CS10,CP1,CP0,CS10,CS10,CP1,CP0,CS11,CP0,CP1,CP0,CP1,CP0,CP0,CS01,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CS10,CS01,CP1,CP1,CP0,CS10,CS00,CS00,CS00,CS00,CS10,CS00,CS00,CS10,CS00,CS10,CS11,CP1,CP0,CP0,CS00,CP0,CS00,CS10,CS10,CS00,CP1,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CS00,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CP0,CS01,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CS10,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CP1,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CP1,(COC1 1),CSP0,CS10,(CEC 0),CSP1,CT,CT,CP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP1,CT,CT,CT,CP0,CT,CT,CT,CP0,CS10,CS10,CS00,CP0,CS00,CP0,CP1,CT,CT,(COC0 0),(CSC1 0),CSP0,CS11,CP0,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CP0,CS10,CT,CT,CT,CT,(COC0 1),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,CP0,CT,CT,CP0,CP1,CP0,CS10,CS10,CP1,CP0,CS11,CP0,CP1,CP0,CP1,CP1,CP1,CP0,CP1,CP0,CP0,CP0,CP0,CS00,CS10,CS00,CP1,CP0,CS10,CS11,CP0,CP0,CS00,CP0,CP0,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CS10,CS01,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP0,CS01,CP0,CS10,CS10,CS10,CS10,CP0,CS01,CP1,CP0,CS11,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CS00,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CP1,CP0,CS10,CP1,CP0,CS10,CS11,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CP0,CT,CT,CP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP1,CP1,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CP0,CS10,CT,CT,CT,CT,(COC0 1),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CP1,CT,CP0,CT,CT,CP0,CS10,CP0,CS00,CS00,CP0,CS00,CP0,CS01,CP1,CP1,CP1,CP0,CS10,CS00,CS01,CP0,CP0,CS01,CP0,CP0,CS00,CP0,CP0,CS01,CP1,CP0,CP1,CP0,CS11,CP1,CP1,CP0,CP0,CP1,CP0,CS10,CS10,CS01,CP1,CP0,CS10,CS00,CS00,CP0,CS00,CS00,CP1,CP1,CP0,CS10,CS00,CS11,CP0,CS10,CS01,CP0,CP0,CS00,CS00,CP1,CP1,CP1,CP0,CS11,CP0,CS10,CS10,CS10,CP0,CP0,CS00,CS10,CS00,CP1,CP0,CS10,CS11,CP0,CS10,CS10,CP0,CS00,CS10,CS01,CP0,CS11,CP1,CP1,CP0,CS10,CP1,CP1,CP0,CS10,CS01,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP1,CP0,CP1,CP0,CP0,CS00,CP0,CS00,CS10,CS00,CS10,CP1,CP1,CP0,CS10,CP1,CP0,CS10,CS10,CS00,CS01,CP1,CP1,CP1,CP0,CS10,CS01,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS10,CS01,CP1,CP0]
]

def z2b_0813 : zW := [V,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,V,K,Q,V,V,V,K,K,V,V,Q,V,Q,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,Q,V,V,V,V,K,Q,V,V,Q,V,V,Q,Q,V,V,V,V,V,K,Q,V,V,Q,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,V,K,V,V,Q,V,V,K,V,V,Q,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,V,V,K,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,K,V,V,Q,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,V,K,V,V,Q,V,Q,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,V,K,V,Q,V,K,V,V,V,K,V,V,Q,V,V,Q,V,V,V,V,K,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,Q,V,V,Q,V,V,K,V,V,K,V,V,Q,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,Q,V,K,K,V,K,V,K,V,V,V,V,Q,K,K,V,V,K,V,V,K,V,V,K,V,V,V,V,Q,V,V,V,V,V,V,Q,Q,K,V,V,Q,K,K,V,K,K,V,V,V,Q,K,Q,V,Q,K,V,V,K,K,V,V,V,V,Q,V,Q,Q,Q,V,V,K,Q,K,V,V,Q,Q,V,Q,Q,V,K,Q,K,V,Q,V,V,V,Q,V,V,V,Q,K,V,V,V,V,V,V,V,V,V,V,V,V,K,V,K,Q,K,Q,V,V,V,Q,V,V,Q,Q,K,K,V,V,V,V,Q,K,V,Q,V,V,V,V,V,K,V,V,V,K,V,Q,Q,V,Q,K,V,V]

def z2c_low_0813 : zW := [Q,K,K,K,K,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,Q,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,K,K,Q,Q,Q,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,K,K,K,K,K,K,K,K,Q,Q,K,Q,Q,Q,K,K,Q,Q,K,Q,K,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,K,K,Q,Q,K,Q,K,K,K,K,Q,Q,Q,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,K,K,K,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,Q,K,Q,Q,Q,K]

def z2c_top_0813 : zW := [Q,K,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K]

def z2c_0813 : zW := z2c_low_0813 ++ z2c_top_0813

lemma z2d_0813 :
    loc_Rounds (zTs z29_0813 default) (zTs (zP33 ++ (z2b_0813 ++ (z2c_0813 ++ zTail8))) default) :=
  loc_z25 z2a_0813 z29_0813 (zP33 ++ (z2b_0813 ++ (z2c_0813 ++ zTail8))) (by decide +kernel)

lemma z2e_0813 :
    BGood (z2b_0813 ++ (z2c_0813 ++ zTail8)) := by
  apply loc_z28 z2b_0813 z2c_low_0813 z2c_top_0813 <;> decide +kernel

def zPre_0813 : zW := [V,V,V,V,V,V,V,K,V,V,Q,V,V,Q,K,V,V,V,K,V,Q,Q,Q,V,K,Q,Q,K,Q,Q,K,K,K,K,K,K,K]

def zCk0_0813 : CCfg := ⟨B,0,[],[]⟩

def zCk1_0813 : CCfg := ⟨C,1,[1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[1,0,0,0,0,0,1,0,1,0,1,0,0,0,1]⟩

def zCk2_0813 : CCfg := ⟨C,1,[0,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,0,0,1,0,0,0,0,0,0,0,1]⟩

def zCk3_0813 : CCfg := ⟨C,1,[0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1]⟩

def zCk4_0813 : CCfg := ⟨E,0,[0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,0,0,1,0,1,0,0,0,1,0,1]⟩

def zCk5_0813 : CCfg := ⟨B,1,[1,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,0,0,1,1,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,0,0,0,1]⟩

def zCk6_0813 : CCfg := ⟨D,1,[0,1,1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[1,0,0,1,0,1,0,1,1,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,1,0,1]⟩

def zCk7_0813 : CCfg := ⟨C,1,[1,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,1,1,0,0,1,0,1,0,1,1,0,0,1,0,1,1,0,0,0,0,1,1,0,0,0,0,1,0,1,0,1,0,0,0,1,0,1,0,1,0,1]⟩

def zCk8_0813 : CCfg := ⟨C,1,[1,0,1,0,1,0,1,0,1,1,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1],[1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,0,0,1,0,0,0,0,0,1]⟩

def zCk9_0813 : CCfg := ⟨C,1,[0,1],[0,0,0,0,1,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,0,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,0,1,0,1,1,0,0,0,0,1,0,1,0,0,0,1,0,1]⟩

private lemma zCk_step1 : (c_to_cfg zCk0_0813) [canon_tm]⊢⁺ (c_to_cfg zCk1_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk0_0813 10000 = some zCk1_0813)

private lemma zCk_step2 : (c_to_cfg zCk1_0813) [canon_tm]⊢⁺ (c_to_cfg zCk2_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk1_0813 10000 = some zCk2_0813)

private lemma zCk_step3 : (c_to_cfg zCk2_0813) [canon_tm]⊢⁺ (c_to_cfg zCk3_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk2_0813 10000 = some zCk3_0813)

private lemma zCk_step4 : (c_to_cfg zCk3_0813) [canon_tm]⊢⁺ (c_to_cfg zCk4_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk3_0813 10000 = some zCk4_0813)

private lemma zCk_step5 : (c_to_cfg zCk4_0813) [canon_tm]⊢⁺ (c_to_cfg zCk5_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk4_0813 10000 = some zCk5_0813)

private lemma zCk_step6 : (c_to_cfg zCk5_0813) [canon_tm]⊢⁺ (c_to_cfg zCk6_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk5_0813 10000 = some zCk6_0813)

private lemma zCk_step7 : (c_to_cfg zCk6_0813) [canon_tm]⊢⁺ (c_to_cfg zCk7_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk6_0813 10000 = some zCk7_0813)

private lemma zCk_step8 : (c_to_cfg zCk7_0813) [canon_tm]⊢⁺ (c_to_cfg zCk8_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk7_0813 10000 = some zCk8_0813)

private lemma zCk_step9 : (c_to_cfg zCk8_0813) [canon_tm]⊢⁺ (c_to_cfg zCk9_0813) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk8_0813 7731 = some zCk9_0813)

private lemma zPre_side_0813 : Side ([Call.ch] ^ 16) (zTs zPre_0813 default) (zTs z29_0813 default) :=
  zHExec_ok zPre_0813 16 z29_0813 (by decide +kernel)

lemma z0E_0813 : (c_to_cfg zCk0_0813) [canon_tm]⊢⁺ (zCf (zTs z29_0813 default)) := by
  have h_all := zPt zCk_step1 (zPt zCk_step2 (zPt zCk_step3 (zPt zCk_step4
    (zPt zCk_step5 (zPt zCk_step6 (zPt zCk_step7 (zPt zCk_step8 zCk_step9)))))))
  have heq : c_to_cfg zCk9_0813 = zCL lh (w_pre +> zTs zPre_0813 default) := by
    simp only [c_to_cfg,C,WordCanonBR.C,zCk9_0813,zCL,lh,w_pre,w_pre_rest,w_pre5_rest,w_pre3_rest,w_word,
      zPre_0813,zTs,t,d0,d1,one,List.cons_append,List.nil_append,append_cons,append_nil,z00,
      Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  rw [heq] at h_all
  exact zPt h_all (zW_pre_full zPre_side_0813)

lemma z2s_0813 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0813) N = some (zCf (zTs (zP33 ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0813 with ⟨k1,_,hk1⟩
    rcases loc_z2r z2d_0813 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0813 ++ (z2c_0813 ++ zTail8),
      zMt canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0813⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases loc_z1N h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2q hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      zMt canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0813 : Fin 6 -> Fin 6
  | 0 => 5
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 4
  | 5 => 3

def zCfgMap_0813 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0813,⟨c.tape.head,c.tape.right,c.tape.left⟩⟩

lemma zStepMap_0813 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0813 c) = (step canon_tm c).map zCfgMap_0813 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

lemma zMultiStepMap_0813 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0813 c) n = (multiStep canon_tm c n).map zCfgMap_0813 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs,zMs,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0813 c'

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0813 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0813 (c_to_cfg zCk0_0813) = init [] := rfl
  have h_map := zMultiStepMap_0813 (c_to_cfg zCk0_0813) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := zIm h_map
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB1LF_1RC0RB_1RD0RF_1REHHH_1LF1LA_1LA0LE
