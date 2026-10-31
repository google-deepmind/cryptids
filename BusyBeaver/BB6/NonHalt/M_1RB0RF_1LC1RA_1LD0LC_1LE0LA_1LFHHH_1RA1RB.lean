/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RB` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LF---_1RA1RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => none
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 1 Dir.right)

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

def z29_0539 : zW := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,Q,V,V,V,Q,V,V,V,K,V,V,Q,K,V,V,V,Q,Q,Q,V,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,Q]

def z2a_0539 : List (List Choice) := [
  [CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CT,CT,(COC0 0),CSP1,CP1,(COC1 0),CSP0,CS11,CP1,CP0,CS10,CP0,CP1,CP0,CS10,CS10,CS00,CS00,CS10,CP0],
  [CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP1,CP0,CS10,CS01,(COC0 0),CSP0,CS10,CS01,CP0,CS10,CP0,CP0,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CS10,CT,(COC1 1),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CP0,CP1,CP1,CP0,CS10,CP0,CS00,CS10,CS00,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CP0,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CS11,CP1,CP0,CP1,CP0,CS10,CP0,CS01,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CS01,CP0,CS10,CS01,CP1,CP0,CS10,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),CSP0,CT,CP0,CT,(COC1 0),CSP1,(COC1 0),CSP0,CT,CT,CP0,CS10,CP1,CP0,CP0,CS00,CS00,CS10,CS10,CP0,CS00,CS11,CP1,CP0,CS10,CS00,CS01,CP1,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CP0,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CS10,CP1,(COC0 0),CSP0,CS11,CT,CT,CP0,CS10,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CS00,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,CT,CP0,CS10,CS11,CP0,CS11,CP0,CP1,CP1,CP1,CP0,CS10,CP0,CS00,CS10,CS10,CS01,CP0,CP0,CP1,CP0,CS10,CS10,CS01,CP0,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,(COC1 0),(CSC0 0),CSP1,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CP1,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS11,CP0,CT,CT,CT,(COC0 0),CSP1,CP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),(CSC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CP1,CT,CT,CP0,CS10,CP0,CS00,CP0,CP0,CS00,CS10,CP0,CP0,CS00,CS10,CS01,CP0,CS10,CP0,CS00,CS01,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CS00,CS11,CP1,CP0,CP1,CP0,CS10,CS11,CP0,CS11,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CT,(COC1 0),CSP0,CS11,CT,(COC0 0),(CSC1 1),CSP1,(COC1 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),CSP1,CP0,CS10,CS01,CT,CT,CT,CT,CP1,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CS00,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CP1,CT,CT,CP0,CS10,CP1,CP0,CS10,CS10,CS11,CP0,CS10,CS00,CP1,CP0,CS10,CS10,CS01,CP0,CS10,CP0,CP0,CP1,CP1,CP0,CP1,CP0,CS10,CP1,CP0,CP0,CP0,CS00,CP0,CP0,CP1,CP0,CP1,CP1,CP0,CS10,CS00,CS10,CS10,CS01,CP0,CP0,CP1,CP0,CS10,CS10,CS01,CP0,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CS01,CP0,CS10,CS01,CP1,CP0,CS10,CP0,CS01,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP0,CS11,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,(COC1 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP1,CP1,CT,CP0,CT,(COC1 0),CSP1,(COC1 1),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CP0,CS11,CP0,CT,CT,CT,(COC0 0),CSP1,CP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),CSP0,CT,CP0,CT,(COC1 0),CSP1,(COC1 0),CSP0,CT,CP0,CT,CT,CP0,CS11,CP0,CP0,CS00,CS00,CS00,CP0,CP0,CS00,CS10,CP0,CP1,CP0,CS10,CS10,CP1,CP1,CP0,CS10,CS00,CS10,CS01,CP0,CP0,CS00,CS00,CS10,CS10,CS10,CS11,CP0,CS10,CS01,CP0,CS10,CS00,CP0,CP1,CP1,CP1,CP0,CP0,CS00,CS01,CP0,CS10,CP0,CS00,CS00,CP0,CP0,CP1,CP0,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CS00,CS01,CP1,CP0,CP1,CP0,CS10,CS11,CP0,CS11,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CP0,CS01,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),(CSC1 0),CSP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CS10,CS10,CT,(COC1 0),CSP0,CS11,CT,CT,CT,CP1,CT,CT,CT,CP0,CP0,CT,(COC1 0),CSP0,CS10,CP1,CP1,CT,CP0,CT,CP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,(CEC 0),CSP1,(COC1 0),CSP0,CS10,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,CP0,CS10,CS00,CT,CT,CT,CT,CP1,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CS10,CS00,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,CP0,CT,CT,CP0,CS10,CP0,CS00,CS00,CS11,CP1,CP0,CS11,CP0,CS10,CS11,CP0,CS10,CS10,CS11,CP0,CS10,CS01,CP1,CP1,CP0,CS10,CS01,CP0,CP1,CP1,CP0,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CP0,CS00,CP1,CP0,CS11,CP0,CS10,CS00,CP0,CS01,CP0,CS10,CS10,CS11,CP0,CP0,CS00,CP0,CP0,CS01,CP0,CS10,CS01,CP0,CP0,CS00,CS00,CP1,CP1,CP0,CP0,CP0,CS00,CS11,CP0,CS10,CS01,CP1,CP0,CS11,CP0,CP0,CP0,CP1,CP0,CP1,CP1,CP0,CS10,CS00,CS10,CS10,CS01,CP0,CP0,CP1,CP0,CS10,CS10,CS01,CP0,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CS01,CP0,CS10,CP1,CP0,CS10,CP1,CP0,CS10,CS11,CP0,CS10,CS01,CP1,CP0],
  [CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,(COC1 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),(CSC0 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CS11,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,(COC0 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,(COC0 0),CSP0,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CP1,(COC1 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,(COC0 0),CSP1,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CT,CT,CP0,CT,CT,CT,CT,(COC0 0),CSP1,CT,CT,CT,CT,(COC0 0),CSP0,CT,CP0,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 0),CSP0,CS10,CS11,CT,(COC0 0),CSP1,CT,CP1,(COC1 0),CSP1,CP1,CT,CP0,CT,CT,CT,CP0,CT,CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP1,(COC1 1),CSP0,CT,(COC1 0),CSP1,CT,(COC0 1),(CSC1 0),CSP1,CP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CT,CP0,CT,(COC1 0),CSP0,CS10,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CP0,CT,(COC1 0),CSP1,CT,CT,CT,CT,CT,CT,CT,CT,CP0,CS11,CP0,CT,CT,CT,(COC0 0),CSP1,CP0,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS10,(CEC 0),(CSC0 0),CSP1,CT,(COC0 0),CSP1,CT,CT,CP1,CT,CP0,CT,CT,CP0,CS10,CS10,CS10,CS01,CP0,CS10,CS10,CS01,CP0,CP0,CP0,CS00,CS10,CP0,CS00,CP0,CS00,CP1,CP0,CP0,CS01,CP1,CP0,CP1,CP0,CP0,CS00,CP0,CS00,CP0,CP1,CP1,CP0,CS10,CS00,CS10,CS00,CP0,CP0,CS00,CS11,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS11,CP1,CP1,CP0,CS10,CP0,CS00,CS11,CP1,CP1,CP0,CS10,CP0,CS00,CP0,CS01,CP0,CS10,CP0,CP0,CS00,CS11,CP0,CS10,CP1,CP1,CP0,CS10,CS01,CP0,CP0,CS01,CP0,CP0,CS00,CS00,CS10,CS10,CS10,CS11,CP0,CS10,CP0,CS00,CS10,CS10,CS00,CS00,CP1,CP1,CP1,CP0,CP0,CS00,CS01,CP0,CS10,CS11,CP1,CP0,CS10,CP0,CP1,CP0,CP0,CP0,CP0,CP1,CP0,CS10,CS10,CS00,CS00,CS01,CP1,CP0,CP1,CP0,CS10,CS11,CP0,CS11,CP1,CP1,CP1,CP0,CP0,CS00,CS00,CS00,CP0,CP0,CP0,CS01,CP1,CP0,CP0,CS01,CP0,CS10,CS11,CP0,CS10,CS01,CP1,CP0]
]

def z2b_0539 : zW := [V,V,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,V,Q,V,Q,V,V,K,V,V,V,K,V,V,V,V,K,Q,V,V,V,V,K,Q,V,V,V,K,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,V,K,V,Q,V,V,V,V,V,K,Q,V,V,V,V,V,K,V,V,V,K,K,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,Q,V,K,V,V,V,V,K,V,V,V,V,V,V,V,K,V,Q,V,K,V,V,V,K,V,V,V,V,V,V,V,K,Q,V,V,V,K,V,Q,V,K,V,Q,V,V,K,V,Q,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,V,V,K,V,V,Q,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,K,V,V,Q,V,V,V,Q,V,Q,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,K,Q,V,V,V,V,V,V,V,V,K,V,Q,V,Q,Q,V,K,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,Q,V,V,K,V,Q,V,V,V,V,K,V,V,Q,V,V,V,V,Q,V,Q,V,V,V,V,K,V,Q,V,V,V,Q,V,V,V,V,V,V,V,V,V,V,Q,V,V,V,V,K,V,V,V,V,V,V,V,K,V,Q,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,Q,Q,Q,K,V,Q,Q,K,V,V,V,K,Q,V,K,V,K,V,V,V,K,V,V,V,V,V,K,V,K,V,V,V,V,Q,K,Q,K,V,V,K,Q,V,V,K,V,Q,Q,V,Q,V,V,V,Q,V,K,Q,V,V,V,Q,V,K,V,K,V,Q,V,V,K,Q,V,Q,V,V,V,Q,K,V,V,K,V,V,K,K,Q,Q,Q,Q,V,Q,V,K,Q,Q,K,K,V,V,V,V,V,K,K,V,Q,Q,V,V,Q,V,V,V,V,V,V,V,V,Q,Q,K,K,K,V,V,V,V,Q,Q,V,Q,V,V,V,V,V,K,K,K,V,V,V,K,V,V,V,K,V,Q,Q,V,Q,K,V,V]

def z2c_low_0539 : zW := [Q,K,K,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,K,K,K,K,K,Q,Q,Q,K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,K,K,Q,K,K,Q,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,K,K,Q,Q,Q,K,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,K,K,K,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,K,K,K,Q,Q,K,Q,K,K,Q,K,Q,K,Q,Q,K,K,Q,Q,K,Q,K,K,K,Q,Q,Q,Q,Q,K,Q,K,Q,K,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,K,K,K,Q,Q,K,Q,K,Q,Q,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,K,K,Q,K]

def z2c_top_0539 : zW := [Q,Q,K,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,K,K]

def z2c_0539 : zW := z2c_low_0539 ++ z2c_top_0539

lemma z2d_0539 :
    loc_Rounds (zTs z29_0539 default) (zTs (zP33 ++ (z2b_0539 ++ (z2c_0539 ++ zTail8))) default) :=
  loc_z25 z2a_0539 z29_0539 (zP33 ++ (z2b_0539 ++ (z2c_0539 ++ zTail8))) (by decide +kernel)

lemma z2e_0539 :
    BGood (z2b_0539 ++ (z2c_0539 ++ zTail8)) := by
  apply loc_z28 z2b_0539 z2c_low_0539 z2c_top_0539 <;> decide +kernel

def zRem1Pad_0539 : zW := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,K,K,K,K,Q,Q,Q,Q,Q,K,K,K,K]

def zMid1_0539 : zW := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,K,K,K,K,Q,Q,Q,Q,Q,K,K,K,Q]

def zCh1_0539 : List Choice := [CT,CT,CT,CT,CT,CT,CT,(COC0 0),(CSC1 0),CSP1,CT,(COC0 0),CSP0,CT,(COC1 0),CSP0,CS10,CS00,CS00,CP1,CP1,CP0,CS10,CS00,CP0]

def zOut1_0539 : zW := [V,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,Q,K,K,V,V,V,Q,K,V,K,K,Q,Q,K,Q,Q,Q]

def zRem2Pad_0539 : zW := [V,V,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,Q,K,K,V,V,V,Q,K,V,K,K,Q,Q,K,Q,Q,Q,K,K,K,K,K]

def zMid2_0539 : zW := [V,V,V,V,V,V,V,V,K,Q,V,V,V,K,V,V,Q,V,Q,K,K,V,V,V,Q,K,V,K,K,Q,Q,K,Q,Q,Q,K,K,K,K,Q]

def zCh2_0539 : List Choice := [CT,CT,CT,CT,CT,CT,CT,(COC0 0),CSP0,CS11,CT,CT,(COC0 0),CSP0,CT,(COC1 0),CSP1,CT,CP0,CS10,CT,CT,CT,(COC0 1),CSP0,CS10,CS01,CP0,CP1,CP0,CS10,CS10,CS10,CP0]

def zOut2_0539 : zW := [V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,Q,V,V,V,Q,V,V,V,K,V,V,Q,K,V,V,V,Q,Q,Q,V,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q]

def zRem3Pad_0539 : zW := [V,V,V,V,V,V,V,V,K,V,Q,V,V,K,V,V,Q,V,V,V,Q,V,V,V,K,V,V,Q,K,V,V,V,Q,Q,Q,V,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K]

def zCk0_0539 : CCfg := ⟨A,0,[],[]⟩

def zCk1_0539 : CCfg := ⟨C,1,[0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,1,1,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,0,1],[0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,1]⟩

def zCk2_0539 : CCfg := ⟨A,0,[1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1],[0,1,0,0,0,0,0,0,0,0,1,0,0,0,1]⟩

def zCk3_0539 : CCfg := ⟨C,0,[1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,1,1,0,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,1,1,0,1,0,1,0,1,0,1,1,1,0,1,1,1,0,1,0,1,0,1,0,1,0,1,0,0,1],[0,0,1,0,0,0,1,0,1,0,1,0,1,0,0,0,0,0,1]⟩

def zCk4_0539 : CCfg := ⟨C,1,[0,1],[0,0,0,0,1,1,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,0,1,1,0,0,1,1,0,0,0,0,1,1,0,0,1,1,0,0,0,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1]⟩

private lemma zCk_step1_0539 : (c_to_cfg zCk0_0539) [canon_tm]⊢⁺ (c_to_cfg zCk1_0539) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk0_0539 10000 = some zCk1_0539)

private lemma zCk_step2_0539 : (c_to_cfg zCk1_0539) [canon_tm]⊢⁺ (c_to_cfg zCk2_0539) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk1_0539 10000 = some zCk2_0539)

private lemma zCk_step3_0539 : (c_to_cfg zCk2_0539) [canon_tm]⊢⁺ (c_to_cfg zCk3_0539) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk2_0539 10000 = some zCk3_0539)

private lemma zCk_step4_0539 : (c_to_cfg zCk3_0539) [canon_tm]⊢⁺ (c_to_cfg zCk4_0539) :=
  zTcF (by decide) (by decide +kernel : zCmF zCk3_0539 6519 = some zCk4_0539)

private lemma zH1_0539 : Side ([Call.ch] ^ 4) (zTs zRem1Pad_0539 default) (zTs zMid1_0539 default) :=
  zHExec_ok zRem1Pad_0539 4 zMid1_0539 (by decide +kernel)

private lemma zB1_0539 : BRIncs false 5 (zTs (zMid1_0539 ++ [K]) default) (zTs zOut1_0539 default) :=
  loc_z21 zCh1_0539 false 5 (zMid1_0539 ++ [K]) zOut1_0539 (by decide +kernel)

private lemma zH2_0539 : Side ([Call.ch] ^ 8) (zTs zRem2Pad_0539 default) (zTs zMid2_0539 default) :=
  zHExec_ok zRem2Pad_0539 8 zMid2_0539 (by decide +kernel)

private lemma zB2_0539 : BRIncs false 4 (zTs (zMid2_0539 ++ [K]) default) (zTs zOut2_0539 default) :=
  loc_z21 zCh2_0539 false 4 (zMid2_0539 ++ [K]) zOut2_0539 (by decide +kernel)

private lemma zH3_0539 : Side ([Call.ch] ^ 16) (zTs zRem3Pad_0539 default) (zTs z29_0539 default) :=
  zHExec_ok zRem3Pad_0539 16 z29_0539 (by decide +kernel)

lemma z0E_0539 : (c_to_cfg zCk0_0539) [canon_tm]⊢⁺ (zCf (zTs z29_0539 default)) := by
  have h_all := zPt zCk_step1_0539 (zPt zCk_step2_0539 (zPt zCk_step3_0539 zCk_step4_0539))
  have heq1 : c_to_cfg zCk4_0539 = zCL lh (w_pre3 +> zTs zRem1Pad_0539 default) := by
    simp only [c_to_cfg,C,WordCanonBR.C,zCk4_0539,zCL,lh,w_pre3,w_pre3_rest,w_word,
      zRem1Pad_0539,zTs,t,d0,d1,one,List.cons_append,List.nil_append,append_cons,append_nil,z00,
      Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  rw [heq1] at h_all
  have h_h1 := zH1_0539
  have h_b1_0 := zB1_0539
  have h_b1 : BRIncs false 5 (zTs zMid1_0539 default) (zTs zOut1_0539 default) := by
    simpa only [z15,zTs,zDd] using! h_b1_0
  have h_s1 : Side ([.cp] ++ [.ch] ^ 2) (zTs zMid1_0539 default) (zTs zOut1_0539 default) := by
    simpa only [append_nil] using! loc_z2o h_b1 [] ([.cp] ++ [.ch] ^ 2) (Num.odd 2)
  have h_turn1 := zW_pre3_full (by have h := z08 h_h1 h_s1; exact h)
  have heq2 : t +> zTs zOut1_0539 default = zTs zRem2Pad_0539 default := by
    simp only [zOut1_0539,zRem2Pad_0539,zTs,t,d0,d1,List.cons_append,List.nil_append,append_cons,append_nil,z00]
  rw [heq2] at h_turn1
  have h_h2 := zH2_0539
  have h_b2_0 := zB2_0539
  have h_b2 : BRIncs false 4 (zTs zMid2_0539 default) (zTs zOut2_0539 default) := by
    simpa only [z15,zTs,zDd] using! h_b2_0
  have h_s2 : Side ([.cj,.ch]) (zTs zMid2_0539 default) (zTs zOut2_0539 default) := by
    simpa only [z06,List.cons_append,List.nil_append,append_nil] using! loc_z2o h_b2 [] ([.cj] ++ [.ch] ^ 1) (Num.even 1)
  have h_turn2 := zW_pre5_full (z08 h_h2 h_s2)
  have heq3 : t +> zTs zOut2_0539 default = zTs zRem3Pad_0539 default := by
    simp only [zOut2_0539,zRem3Pad_0539,zTs,t,d0,d1,List.cons_append,List.nil_append,append_cons,append_nil,z00]
  rw [heq3] at h_turn2
  have h_h3 := zH3_0539
  have h_turn3 := zW_pre_full h_h3
  exact zPt h_all (zPt h_turn1 (zPt h_turn2 h_turn3))

lemma z2s_0539 (m : Nat) :
    ∃ N ≥ m,∃ w,multiStep canon_tm (c_to_cfg zCk0_0539) N = some (zCf (zTs (zP33 ++ w) default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases z0E_0539 with ⟨k1,_,hk1⟩
    rcases loc_z2r z2d_0539 with ⟨k2,hk2⟩
    exact ⟨k1 + k2,Nat.zero_le _,z2b_0539 ++ (z2c_0539 ++ zTail8),
      zMt canon_tm _ _ _ k1 k2 hk1 hk2,z2e_0539⟩
  | succ m ih =>
    rcases ih with ⟨N,hN,w,h_ms,h_good⟩
    rcases loc_z1N h_good with ⟨w',hStep,h_good'⟩
    rcases loc_z2q hStep with ⟨k,hk_pos,h_step_k⟩
    exact ⟨N + k,Nat.add_le_add hN hk_pos,w',
      zMt canon_tm _ _ _ N k h_ms h_step_k,h_good'⟩

def zStMap_0539 : Fin 6 -> Fin 6
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 5
  | 5 => 4

def zCfgMap_0539 (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map zStMap_0539,c.tape⟩

lemma zStepMap_0539 (c : Cfg (Fin 2) (Fin 6)) :
    step target_tm (zCfgMap_0539 c) = (step canon_tm c).map zCfgMap_0539 := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q,hq⟩,⟨h,l,r⟩⟩ <;>
    rcases h with ⟨_ | _ | a,ha⟩ <;>
    first | omega | rfl

lemma zMultiStepMap_0539 (c : Cfg (Fin 2) (Fin 6)) (n : Nat) :
    multiStep target_tm (zCfgMap_0539 c) n = (multiStep canon_tm c n).map zCfgMap_0539 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zMs,zMs,ih]
    cases multiStep canon_tm c n with
    | none => rfl
    | some c' => exact zStepMap_0539 c'

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases z2s_0539 (n + 1) with ⟨N,hN,_,h_N,_⟩
  have h_init : zCfgMap_0539 (c_to_cfg zCk0_0539) = init [] := rfl
  have h_map := zMultiStepMap_0539 (c_to_cfg zCk0_0539) N
  rw [h_init,h_N] at h_map
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_map
  have h_some := zIm h_map
  rw [zMs,hn] at h_some
  exact h_some

end BusyBeaver.M_1RB0RF_1LC1RA_1LD0LC_1LE0LA_1LFHHH_1RA1RB
