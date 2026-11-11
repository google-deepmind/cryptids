/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.Zf.Boot

/-!
# Layer 1 for `riemann120`: TM Tables, `121 → 120` Window Quotient, Boot & 5-Reg Gadgets
-/

@[expose] public section

namespace ConjectureMachines.Riemann120

open Turing (Dir)
open StateTransition ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps
   mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)
open ConjectureMachines.Semantics.Zf.Layer1
  (rootLeft rootLeft_eq_append stackLeft stackLeft_nil stackLeft_eq_append
   stackLeft_append stackLeft_append_singleton)
open ConjectureMachines.Semantics.Zf.Boot
  (pair01 pair10 pair01_snoc pair10_snoc cons_one_pair01 pair10_succ_eq
   bootLeft bootLeft_zero)

abbrev TM (states symbols : ℕ) := Machine states symbols

/-- Number of states of a `Machine states symbols`. -/
def _root_.ConjectureMachines.Machine.states {n k : ℕ} (_ : Machine n k) : ℕ := n

set_option maxRecDepth 200000

/-!
## 1. Machine Tables & Transition Lookup (`riemann120` and `riemann121`)
-/

/-- Shunia's 120-state Riemann Hypothesis Turing machine (`baselines/tables/riemann_120.txt`). -/
abbrev riemann120 : Machine 120 2 := Machines.riemann120

@[simp] theorem riemann120_states : riemann120.states = 120 := rfl




def rh121Trans (q : Fin 121) (a : Fin 2) :
    Option (Fin 2 × Dir × Fin 121) :=
  if q.val < 60 then
    if q.val < 30 then
      if q.val < 15 then
        if q.val < 7 then
          if q.val < 3 then
            if q.val < 1 then
              if a.val == 0 then some (1, .right, 1)
              else some (1, .left, 2)
            else
              if q.val < 2 then
                if a.val == 0 then some (0, .left, 0)
                else some (0, .left, 3)
              else
                if a.val == 0 then some (1, .left, 0)
                else some (1, .right, 4)
          else
            if q.val < 5 then
              if q.val < 4 then
                if a.val == 0 then some (1, .left, 1)
                else some (1, .right, 5)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 7)
            else
              if q.val < 6 then
                if a.val == 0 then some (0, .right, 3)
                else some (0, .right, 1)
              else
                if a.val == 0 then some (0, .right, 8)
                else none
        else
          if q.val < 11 then
            if q.val < 9 then
              if q.val < 8 then
                if a.val == 0 then some (0, .right, 9)
                else some (1, .right, 7)
              else
                if a.val == 0 then some (1, .right, 8)
                else some (1, .left, 10)
            else
              if q.val < 10 then
                if a.val == 0 then some (0, .right, 11)
                else some (1, .right, 9)
              else
                if a.val == 0 then some (0, .left, 10)
                else some (1, .left, 12)
          else
            if q.val < 13 then
              if q.val < 12 then
                if a.val == 0 then some (1, .right, 13)
                else some (1, .right, 11)
              else
                if a.val == 0 then some (0, .left, 14)
                else some (1, .left, 12)
            else
              if q.val < 14 then
                if a.val == 0 then some (0, .left, 15)
                else some (0, .right, 11)
              else
                if a.val == 0 then some (0, .left, 16)
                else some (1, .left, 12)
      else
        if q.val < 22 then
          if q.val < 18 then
            if q.val < 16 then
              if a.val == 0 then some (0, .left, 17)
              else some (1, .left, 15)
            else
              if q.val < 17 then
                if a.val == 0 then some (0, .left, 18)
                else some (1, .left, 12)
              else
                if a.val == 0 then some (0, .left, 19)
                else some (1, .left, 15)
          else
            if q.val < 20 then
              if q.val < 19 then
                if a.val == 0 then some (0, .right, 20)
                else some (1, .left, 12)
              else
                if a.val == 0 then some (1, .right, 21)
                else some (0, .left, 19)
            else
              if q.val < 21 then
                if a.val == 0 then some (0, .right, 20)
                else some (1, .right, 22)
              else
                if a.val == 0 then some (0, .right, 21)
                else some (0, .right, 23)
        else
          if q.val < 26 then
            if q.val < 24 then
              if q.val < 23 then
                if a.val == 0 then some (0, .right, 24)
                else some (1, .right, 25)
              else
                if a.val == 0 then some (0, .left, 24)
                else some (0, .right, 23)
            else
              if q.val < 25 then
                if a.val == 0 then some (1, .left, 10)
                else some (1, .right, 26)
              else
                if a.val == 0 then some (0, .right, 27)
                else some (0, .right, 27)
          else
            if q.val < 28 then
              if q.val < 27 then
                if a.val == 0 then some (0, .right, 24)
                else some (1, .right, 28)
              else
                if a.val == 0 then some (0, .right, 29)
                else some (1, .right, 30)
            else
              if q.val < 29 then
                if a.val == 0 then some (0, .right, 4)
                else some (1, .right, 31)
              else
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 32)
    else
      if q.val < 45 then
        if q.val < 37 then
          if q.val < 33 then
            if q.val < 31 then
              if a.val == 0 then some (0, .right, 33)
              else some (1, .right, 34)
            else
              if q.val < 32 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 35)
              else
                if a.val == 0 then some (0, .right, 36)
                else some (0, .left, 37)
          else
            if q.val < 35 then
              if q.val < 34 then
                if a.val == 0 then some (0, .right, 38)
                else some (1, .right, 39)
              else
                if a.val == 0 then some (0, .right, 40)
                else some (1, .right, 41)
            else
              if q.val < 36 then
                if a.val == 0 then some (0, .right, 42)
                else some (1, .right, 35)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 43)
        else
          if q.val < 41 then
            if q.val < 39 then
              if q.val < 38 then
                if a.val == 0 then some (0, .left, 37)
                else some (0, .left, 10)
              else
                if a.val == 0 then some (0, .right, 44)
                else some (1, .right, 45)
            else
              if q.val < 40 then
                if a.val == 0 then some (0, .right, 46)
                else some (0, .left, 37)
              else
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 48)
          else
            if q.val < 43 then
              if q.val < 42 then
                if a.val == 0 then some (0, .right, 49)
                else some (1, .right, 50)
              else
                if a.val == 0 then some (0, .right, 51)
                else some (1, .right, 42)
            else
              if q.val < 44 then
                if a.val == 0 then some (0, .right, 52)
                else some (1, .right, 43)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 53)
      else
        if q.val < 52 then
          if q.val < 48 then
            if q.val < 46 then
              if a.val == 0 then some (0, .right, 54)
              else some (1, .right, 55)
            else
              if q.val < 47 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 56)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 57)
          else
            if q.val < 50 then
              if q.val < 49 then
                if a.val == 0 then some (0, .right, 58)
                else some (0, .left, 37)
              else
                if a.val == 0 then some (0, .right, 59)
                else some (1, .right, 60)
            else
              if q.val < 51 then
                if a.val == 0 then some (0, .right, 61)
                else some (1, .right, 62)
              else
                if a.val == 0 then some (1, .left, 63)
                else some (0, .right, 64)
        else
          if q.val < 56 then
            if q.val < 54 then
              if q.val < 53 then
                if a.val == 0 then some (0, .right, 53)
                else some (1, .right, 52)
              else
                if a.val == 0 then some (0, .right, 7)
                else some (1, .right, 53)
            else
              if q.val < 55 then
                if a.val == 0 then some (0, .right, 65)
                else some (1, .right, 66)
              else
                if a.val == 0 then some (0, .right, 67)
                else some (1, .right, 68)
          else
            if q.val < 58 then
              if q.val < 57 then
                if a.val == 0 then some (0, .right, 69)
                else some (1, .right, 56)
              else
                if a.val == 0 then some (0, .right, 35)
                else some (1, .right, 57)
            else
              if q.val < 59 then
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 36)
              else
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 72)
  else
    if q.val < 90 then
      if q.val < 75 then
        if q.val < 67 then
          if q.val < 63 then
            if q.val < 61 then
              if a.val == 0 then some (0, .right, 73)
              else some (1, .right, 74)
            else
              if q.val < 62 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 75)
              else
                if a.val == 0 then some (0, .right, 76)
                else some (1, .right, 77)
          else
            if q.val < 65 then
              if q.val < 64 then
                if a.val == 0 then some (0, .left, 78)
                else some (1, .left, 63)
              else
                if a.val == 0 then some (0, .left, 51)
                else some (1, .right, 79)
            else
              if q.val < 66 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 80)
              else
                if a.val == 0 then some (0, .right, 81)
                else some (1, .right, 82)
        else
          if q.val < 71 then
            if q.val < 69 then
              if q.val < 68 then
                if a.val == 0 then some (0, .right, 73)
                else some (1, .right, 83)
              else
                if a.val == 0 then some (0, .right, 84)
                else some (1, .right, 84)
            else
              if q.val < 70 then
                if a.val == 0 then some (0, .right, 57)
                else some (1, .right, 69)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 85)
          else
            if q.val < 73 then
              if q.val < 72 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 69)
              else
                if a.val == 0 then some (0, .right, 54)
                else some (1, .right, 86)
            else
              if q.val < 74 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 87)
              else
                if a.val == 0 then some (0, .right, 44)
                else some (0, .left, 37)
      else
        if q.val < 82 then
          if q.val < 78 then
            if q.val < 76 then
              if a.val == 0 then some (0, .right, 88)
              else some (1, .right, 89)
            else
              if q.val < 77 then
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 90)
              else
                if a.val == 0 then some (0, .right, 46)
                else none
          else
            if q.val < 80 then
              if q.val < 79 then
                if a.val == 0 then some (0, .left, 91)
                else some (1, .left, 63)
              else
                if a.val == 0 then some (0, .right, 92)
                else some (1, .right, 79)
            else
              if q.val < 81 then
                if a.val == 0 then some (0, .right, 70)
                else some (0, .left, 37)
              else
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 93)
        else
          if q.val < 86 then
            if q.val < 84 then
              if q.val < 83 then
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 94)
              else
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 84)
            else
              if q.val < 85 then
                if a.val == 0 then some (0, .right, 81)
                else some (1, .right, 95)
              else
                if a.val == 0 then some (0, .right, 43)
                else some (1, .right, 85)
          else
            if q.val < 88 then
              if q.val < 87 then
                if a.val == 0 then some (0, .right, 96)
                else some (0, .left, 97)
              else
                if a.val == 0 then some (0, .right, 56)
                else some (1, .right, 87)
            else
              if q.val < 89 then
                if a.val == 0 then some (0, .right, 4)
                else some (1, .right, 98)
              else
                if a.val == 0 then some (0, .right, 99)
                else some (0, .left, 97)
    else
      if q.val < 105 then
        if q.val < 97 then
          if q.val < 93 then
            if q.val < 91 then
              if a.val == 0 then some (0, .right, 96)
              else some (0, .left, 37)
            else
              if q.val < 92 then
                if a.val == 0 then some (0, .left, 19)
                else some (0, .left, 91)
              else
                if a.val == 0 then some (0, .left, 100)
                else some (1, .right, 79)
          else
            if q.val < 95 then
              if q.val < 94 then
                if a.val == 0 then some (0, .right, 4)
                else some (0, .left, 37)
              else
                if a.val == 0 then some (0, .right, 101)
                else some (0, .left, 37)
            else
              if q.val < 96 then
                if a.val == 0 then some (0, .right, 102)
                else some (1, .right, 103)
              else
                if a.val == 0 then some (0, .right, 46)
                else some (0, .left, 19)
        else
          if q.val < 101 then
            if q.val < 99 then
              if q.val < 98 then
                if a.val == 0 then some (0, .left, 97)
                else some (0, .left, 37)
              else
                if a.val == 0 then some (0, .right, 104)
                else some (1, .right, 105)
            else
              if q.val < 100 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 52)
              else
                if a.val == 0 then some (1, .left, 106)
                else some (1, .left, 100)
          else
            if q.val < 103 then
              if q.val < 102 then
                if a.val == 0 then some (0, .right, 107)
                else some (1, .right, 108)
              else
                if a.val == 0 then some (0, .right, 109)
                else some (1, .right, 60)
            else
              if q.val < 104 then
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 89)
              else
                if a.val == 0 then some (0, .right, 110)
                else some (1, .right, 60)
      else
        if q.val < 113 then
          if q.val < 109 then
            if q.val < 107 then
              if q.val < 106 then
                if a.val == 0 then some (0, .right, 104)
                else some (1, .right, 111)
              else
                if a.val == 0 then some (0, .left, 15)
                else some (0, .left, 100)
            else
              if q.val < 108 then
                if a.val == 0 then some (0, .right, 73)
                else some (1, .right, 112)
              else
                if a.val == 0 then some (0, .right, 65)
                else some (1, .right, 99)
          else
            if q.val < 111 then
              if q.val < 110 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 113)
              else
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 114)
            else
              if q.val < 112 then
                if a.val == 0 then some (0, .right, 115)
                else some (1, .right, 116)
              else
                if a.val == 0 then some (0, .right, 44)
                else some (0, .left, 91)
        else
          if q.val < 117 then
            if q.val < 115 then
              if q.val < 114 then
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 89)
              else
                if a.val == 0 then some (0, .right, 117)
                else some (0, .left, 37)
            else
              if q.val < 116 then
                if a.val == 0 then some (0, .right, 46)
                else some (1, .right, 118)
              else
                if a.val == 0 then some (0, .right, 73)
                else some (1, .right, 32)
          else
            if q.val < 119 then
              if q.val < 118 then
                if a.val == 0 then some (0, .right, 4)
                else some (1, .right, 119)
              else
                if a.val == 0 then some (0, .right, 120)
                else some (0, .left, 37)
            else
              if q.val < 120 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 70)
              else
                if a.val == 0 then some (0, .right, 46)
                else some (1, .right, 70)

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
-- Finite window decision / large-step symbolic transition reduction.


def ed121Trans (q : Fin 121) (a : Fin 2) : Option (Fin 2 × Dir × Fin 121) :=
  if q.val < 60 then
    if q.val < 30 then
      if q.val < 15 then
        if q.val < 7 then
          if q.val < 3 then
            if q.val < 1 then
              if a.val == 0 then none
              else none
            else
              if q.val < 2 then
                if a.val == 0 then none
                else none
              else
                none
          else
            if q.val < 5 then
              if q.val < 4 then
                none
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 7)
            else
              if q.val < 6 then
                none
              else
                if a.val == 0 then some (0, .right, 8)
                else some (0, .right, 57)
        else
          if q.val < 11 then
            if q.val < 9 then
              if q.val < 8 then
                if a.val == 0 then some (0, .right, 9)
                else some (1, .right, 7)
              else
                if a.val == 0 then some (1, .right, 8)
                else some (1, .left, 10)
            else
              if q.val < 10 then
                if a.val == 0 then some (0, .right, 11)
                else some (1, .right, 9)
              else
                if a.val == 0 then some (0, .left, 10)
                else some (1, .left, 12)
          else
            if q.val < 13 then
              if q.val < 12 then
                if a.val == 0 then some (1, .right, 13)
                else some (1, .right, 11)
              else
                if a.val == 0 then some (0, .left, 14)
                else some (1, .left, 12)
            else
              if q.val < 14 then
                if a.val == 0 then some (0, .left, 15)
                else some (0, .right, 11)
              else
                if a.val == 0 then some (0, .left, 16)
                else some (1, .left, 12)
      else
        if q.val < 22 then
          if q.val < 18 then
            if q.val < 16 then
              if a.val == 0 then some (0, .left, 17)
              else some (1, .left, 15)
            else
              if q.val < 17 then
                if a.val == 0 then some (0, .left, 18)
                else some (1, .left, 12)
              else
                if a.val == 0 then some (0, .left, 19)
                else some (1, .left, 15)
          else
            if q.val < 20 then
              if q.val < 19 then
                if a.val == 0 then some (0, .right, 20)
                else some (1, .left, 12)
              else
                if a.val == 0 then some (1, .right, 21)
                else some (0, .left, 19)
            else
              if q.val < 21 then
                if a.val == 0 then some (0, .right, 20)
                else some (1, .right, 27)
              else
                if a.val == 0 then some (0, .right, 21)
                else some (0, .right, 23)
        else
          if q.val < 26 then
            if q.val < 24 then
              if q.val < 23 then
                if a.val == 0 then none
                else none
              else
                if a.val == 0 then some (0, .left, 24)
                else some (0, .right, 23)
            else
              if q.val < 25 then
                if a.val == 0 then some (1, .left, 10)
                else some (0, .left, 10)
              else
                if a.val == 0 then none
                else none
          else
            if q.val < 28 then
              if q.val < 27 then
                none
              else
                if a.val == 0 then some (0, .right, 29)
                else some (1, .right, 30)
            else
              if q.val < 29 then
                none
              else
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 32)
    else
      if q.val < 45 then
        if q.val < 37 then
          if q.val < 33 then
            if q.val < 31 then
              if a.val == 0 then some (0, .right, 33)
              else some (1, .right, 34)
            else
              if q.val < 32 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 35)
              else
                if a.val == 0 then some (0, .right, 36)
                else some (0, .left, 24)
          else
            if q.val < 35 then
              if q.val < 34 then
                if a.val == 0 then some (0, .right, 38)
                else some (1, .right, 39)
              else
                if a.val == 0 then some (0, .right, 40)
                else some (1, .right, 41)
            else
              if q.val < 36 then
                if a.val == 0 then some (0, .right, 42)
                else some (1, .right, 35)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 43)
        else
          if q.val < 41 then
            if q.val < 39 then
              if q.val < 38 then
                if a.val == 0 then none
                else none
              else
                if a.val == 0 then some (0, .right, 44)
                else some (1, .right, 45)
            else
              if q.val < 40 then
                if a.val == 0 then some (0, .right, 46)
                else some (0, .left, 24)
              else
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 48)
          else
            if q.val < 43 then
              if q.val < 42 then
                if a.val == 0 then some (0, .right, 49)
                else some (1, .right, 50)
              else
                if a.val == 0 then some (0, .right, 51)
                else some (1, .right, 42)
            else
              if q.val < 44 then
                if a.val == 0 then some (0, .right, 52)
                else some (1, .right, 43)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 53)
      else
        if q.val < 52 then
          if q.val < 48 then
            if q.val < 46 then
              if a.val == 0 then some (0, .right, 54)
              else some (1, .right, 55)
            else
              if q.val < 47 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 56)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 57)
          else
            if q.val < 50 then
              if q.val < 49 then
                if a.val == 0 then some (0, .right, 58)
                else some (0, .left, 24)
              else
                if a.val == 0 then some (0, .right, 59)
                else some (1, .right, 60)
            else
              if q.val < 51 then
                if a.val == 0 then some (0, .right, 62)
                else some (1, .right, 77)
              else
                if a.val == 0 then some (1, .left, 63)
                else some (0, .right, 64)
        else
          if q.val < 56 then
            if q.val < 54 then
              if q.val < 53 then
                if a.val == 0 then some (0, .right, 53)
                else some (1, .right, 52)
              else
                if a.val == 0 then some (0, .right, 7)
                else some (1, .right, 53)
            else
              if q.val < 55 then
                if a.val == 0 then some (0, .right, 65)
                else some (1, .right, 66)
              else
                if a.val == 0 then some (0, .right, 67)
                else some (1, .right, 68)
          else
            if q.val < 58 then
              if q.val < 57 then
                if a.val == 0 then some (0, .right, 69)
                else some (1, .right, 56)
              else
                if a.val == 0 then some (0, .right, 35)
                else some (1, .right, 57)
            else
              if q.val < 59 then
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 36)
              else
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 72)
  else
    if q.val < 90 then
      if q.val < 75 then
        if q.val < 67 then
          if q.val < 63 then
            if q.val < 61 then
              if a.val == 0 then some (0, .right, 73)
              else some (1, .right, 74)
            else
              if q.val < 62 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 75)
              else
                if a.val == 0 then some (0, .right, 61)
                else some (1, .right, 76)
          else
            if q.val < 65 then
              if q.val < 64 then
                if a.val == 0 then some (0, .left, 78)
                else some (1, .left, 63)
              else
                if a.val == 0 then some (0, .left, 51)
                else some (1, .right, 79)
            else
              if q.val < 66 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 80)
              else
                if a.val == 0 then some (0, .right, 81)
                else some (1, .right, 82)
        else
          if q.val < 71 then
            if q.val < 69 then
              if q.val < 68 then
                if a.val == 0 then some (0, .right, 73)
                else some (1, .right, 83)
              else
                if a.val == 0 then some (0, .right, 84)
                else some (1, .right, 84)
            else
              if q.val < 70 then
                if a.val == 0 then some (0, .right, 57)
                else some (1, .right, 69)
              else
                if a.val == 0 then some (1, .right, 6)
                else some (1, .right, 32)
          else
            if q.val < 73 then
              if q.val < 72 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 69)
              else
                if a.val == 0 then some (0, .right, 54)
                else some (1, .right, 86)
            else
              if q.val < 74 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 87)
              else
                if a.val == 0 then some (0, .right, 44)
                else some (0, .left, 87)
      else
        if q.val < 82 then
          if q.val < 78 then
            if q.val < 76 then
              if a.val == 0 then some (0, .right, 88)
              else some (1, .right, 89)
            else
              if q.val < 77 then
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 86)
              else
                if a.val == 0 then some (0, .right, 46)
                else none
          else
            if q.val < 80 then
              if q.val < 79 then
                if a.val == 0 then some (0, .left, 17)
                else some (1, .left, 63)
              else
                if a.val == 0 then some (0, .right, 92)
                else some (1, .right, 79)
            else
              if q.val < 81 then
                if a.val == 0 then some (0, .right, 70)
                else some (0, .left, 24)
              else
                if a.val == 0 then some (0, .right, 71)
                else some (1, .right, 93)
        else
          if q.val < 86 then
            if q.val < 84 then
              if q.val < 83 then
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 94)
              else
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 84)
            else
              if q.val < 85 then
                if a.val == 0 then some (0, .right, 81)
                else some (1, .right, 95)
              else
                if a.val == 0 then none
                else none
          else
            if q.val < 88 then
              if q.val < 87 then
                if a.val == 0 then some (0, .right, 39)
                else some (0, .left, 32)
              else
                if a.val == 0 then some (0, .right, 56)
                else some (0, .left, 23)
            else
              if q.val < 89 then
                if a.val == 0 then some (0, .right, 4)
                else some (1, .right, 98)
              else
                if a.val == 0 then some (0, .right, 99)
                else some (0, .left, 32)
    else
      if q.val < 105 then
        if q.val < 97 then
          if q.val < 93 then
            if q.val < 91 then
              if a.val == 0 then none
              else none
            else
              if q.val < 92 then
                if a.val == 0 then none
                else none
              else
                if a.val == 0 then some (0, .left, 100)
                else some (1, .right, 79)
          else
            if q.val < 95 then
              if q.val < 94 then
                if a.val == 0 then some (0, .right, 4)
                else some (0, .left, 24)
              else
                if a.val == 0 then some (0, .right, 101)
                else some (0, .left, 24)
            else
              if q.val < 96 then
                if a.val == 0 then some (0, .right, 102)
                else some (1, .right, 103)
              else
                if a.val == 0 then none
                else none
        else
          if q.val < 101 then
            if q.val < 99 then
              if q.val < 98 then
                if a.val == 0 then none
                else none
              else
                if a.val == 0 then some (0, .right, 104)
                else some (1, .right, 105)
            else
              if q.val < 100 then
                if a.val == 0 then some (1, .right, 6)
                else some (0, .right, 52)
              else
                if a.val == 0 then some (1, .left, 106)
                else some (1, .left, 100)
          else
            if q.val < 103 then
              if q.val < 102 then
                if a.val == 0 then some (0, .right, 60)
                else some (1, .right, 108)
              else
                if a.val == 0 then some (0, .right, 109)
                else some (1, .right, 60)
            else
              if q.val < 104 then
                if a.val == 0 then some (0, .right, 31)
                else some (1, .right, 89)
              else
                if a.val == 0 then some (0, .right, 110)
                else some (1, .right, 60)
      else
        if q.val < 113 then
          if q.val < 109 then
            if q.val < 107 then
              if q.val < 106 then
                if a.val == 0 then some (0, .right, 104)
                else some (1, .right, 111)
              else
                if a.val == 0 then some (0, .left, 15)
                else some (0, .left, 100)
            else
              if q.val < 108 then
                if a.val == 0 then none
                else none
              else
                if a.val == 0 then some (0, .right, 65)
                else some (1, .right, 99)
          else
            if q.val < 111 then
              if q.val < 110 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 113)
              else
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 114)
            else
              if q.val < 112 then
                if a.val == 0 then some (0, .right, 115)
                else some (1, .right, 116)
              else
                if a.val == 0 then none
                else none
        else
          if q.val < 117 then
            if q.val < 115 then
              if q.val < 114 then
                if a.val == 0 then some (0, .right, 70)
                else some (1, .right, 89)
              else
                if a.val == 0 then some (0, .right, 117)
                else some (0, .left, 24)
            else
              if q.val < 116 then
                if a.val == 0 then some (0, .right, 46)
                else some (1, .right, 118)
              else
                if a.val == 0 then some (0, .right, 73)
                else some (1, .right, 32)
          else
            if q.val < 119 then
              if q.val < 118 then
                if a.val == 0 then some (0, .right, 4)
                else some (1, .right, 119)
              else
                if a.val == 0 then some (0, .right, 120)
                else some (0, .left, 24)
            else
              if q.val < 120 then
                if a.val == 0 then some (0, .right, 47)
                else some (1, .right, 70)
              else
                if a.val == 0 then some (0, .right, 46)
                else some (1, .right, 70)


def commonTrans (q : Fin 121) (a : Fin 2) : Option (Fin 2 × Dir × Fin 121) :=
  if rh121Trans q a == ed121Trans q a then rh121Trans q a else none

def riemann121 : Machine 121 2 := ⟨rh121Trans⟩
def edited121 : Machine 121 2 := ⟨ed121Trans⟩
def common121 : Machine 121 2 := ⟨commonTrans⟩

@[simp]
theorem rh121Trans_eq (q : Fin 121) (a : Fin 2) :
    riemann121.transition q a = rh121Trans q a := rfl

@[simp]
theorem ed121Trans_eq (q : Fin 121) (a : Fin 2) :
    edited121.transition q a = ed121Trans q a := rfl

@[simp]
theorem commonTrans_eq (q : Fin 121) (a : Fin 2) :
    common121.transition q a = commonTrans q a := rfl

def win5Masks (q : Fin 121) : UInt32 :=
  if q.val < 60 then
    if q.val < 30 then
      if q.val < 15 then
        if q.val < 7 then
          if q.val < 3 then
            if q.val < 1 then
              0xbbbabbbb
            else
              if q.val < 2 then
                0xcfffcf44
              else
                0xcccccccc
          else
            if q.val < 5 then
              if q.val < 4 then
                0x23ff2322
              else
                0xf0fff0ff
            else
              if q.val < 6 then
                0x0c00ff00
              else
                0xff00ff00
        else
          if q.val < 11 then
            if q.val < 9 then
              if q.val < 8 then
                0xffffffff
              else
                0xffffff00
            else
              if q.val < 10 then
                0xffffffff
              else
                0xfff7fff7
          else
            if q.val < 13 then
              if q.val < 12 then
                0xffffffff
              else
                0xcccccccc
            else
              if q.val < 14 then
                0xff00ff00
              else
                0x22222222
      else
        if q.val < 22 then
          if q.val < 18 then
            if q.val < 16 then
              0xfefefefe
            else
              if q.val < 17 then
                0x11111111
              else
                0x33333333
          else
            if q.val < 20 then
              if q.val < 19 then
                0x11111111
              else
                0x13111311
            else
              if q.val < 21 then
                0x000300ff
              else
                0x0fff03ff
        else
          if q.val < 26 then
            if q.val < 24 then
              if q.val < 23 then
                0x0000ff00
              else
                0x000000ff
            else
              if q.val < 25 then
                0x00ff0003
              else
                0xff000000
          else
            if q.val < 28 then
              if q.val < 27 then
                0x0000ff00
              else
                0x00ff0000
            else
              if q.val < 29 then
                0xff000000
              else
                0x000000ff
    else
      if q.val < 45 then
        if q.val < 37 then
          if q.val < 33 then
            if q.val < 31 then
              0x0000ff00
            else
              if q.val < 32 then
                0xffff00ff
              else
                0xff00ff00
          else
            if q.val < 35 then
              if q.val < 34 then
                0x00ff0000
              else
                0xff000000
            else
              if q.val < 36 then
                0xffffffff
              else
                0x00ffff00
        else
          if q.val < 41 then
            if q.val < 39 then
              if q.val < 38 then
                0x30303030
              else
                0x000000ff
            else
              if q.val < 40 then
                0x0000ff00
              else
                0x00ff0000
          else
            if q.val < 43 then
              if q.val < 42 then
                0xff000000
              else
                0xffffffff
            else
              if q.val < 44 then
                0xffffffff
              else
                0x00ff00ff
      else
        if q.val < 52 then
          if q.val < 48 then
            if q.val < 46 then
              0x0000ff00
            else
              if q.val < 47 then
                0x00ff00ff
              else
                0x00ff00ff
          else
            if q.val < 50 then
              if q.val < 49 then
                0x0000ff00
              else
                0x00ff0000
            else
              if q.val < 51 then
                0xff000000
              else
                0x00ff00ff
        else
          if q.val < 56 then
            if q.val < 54 then
              if q.val < 53 then
                0xffffffff
              else
                0xffffffff
            else
              if q.val < 55 then
                0x00ff0000
              else
                0xff000000
          else
            if q.val < 58 then
              if q.val < 57 then
                0xffffffff
              else
                0xffffffff
            else
              if q.val < 59 then
                0x00ff0000
              else
                0x000000ff
  else
    if q.val < 90 then
      if q.val < 75 then
        if q.val < 67 then
          if q.val < 63 then
            if q.val < 61 then
              0x0000ff00
            else
              if q.val < 62 then
                0x00ff0000
              else
                0xff000000
          else
            if q.val < 65 then
              if q.val < 64 then
                0xcccccccc
              else
                0x000000ff
            else
              if q.val < 66 then
                0x00ff00ff
              else
                0x0000ff00
        else
          if q.val < 71 then
            if q.val < 69 then
              if q.val < 68 then
                0x00ff0000
              else
                0xff000000
            else
              if q.val < 70 then
                0xffffffff
              else
                0xffffffff
          else
            if q.val < 73 then
              if q.val < 72 then
                0x000000ff
              else
                0x0000ff00
            else
              if q.val < 74 then
                0x00ff00ff
              else
                0xff000000
      else
        if q.val < 82 then
          if q.val < 78 then
            if q.val < 76 then
              0x0000ff00
            else
              if q.val < 77 then
                0x00ff0000
              else
                0xff000000
          else
            if q.val < 80 then
              if q.val < 79 then
                0x22222222
              else
                0xff00ff00
            else
              if q.val < 81 then
                0x0000ff00
              else
                0x00ff00ff
        else
          if q.val < 86 then
            if q.val < 84 then
              if q.val < 83 then
                0xff000000
              else
                0x0000ff00
            else
              if q.val < 85 then
                0xffff0000
              else
                0xffffffff
          else
            if q.val < 88 then
              if q.val < 87 then
                0xff000000
              else
                0xff00ffff
            else
              if q.val < 89 then
                0x00ff0000
              else
                0xff000000
    else
      if q.val < 105 then
        if q.val < 97 then
          if q.val < 93 then
            if q.val < 91 then
              0x0000ff00
            else
              if q.val < 92 then
                0x11311131
              else
                0x00ff0000
          else
            if q.val < 95 then
              if q.val < 94 then
                0x0000ff00
              else
                0xff000000
            else
              if q.val < 96 then
                0xff00ff00
              else
                0x00ff0000
        else
          if q.val < 101 then
            if q.val < 99 then
              if q.val < 98 then
                0x30003000
              else
                0x0000ff00
            else
              if q.val < 100 then
                0xffff0000
              else
                0xefeeefee
          else
            if q.val < 103 then
              if q.val < 102 then
                0x00ff0000
              else
                0x00ff0000
            else
              if q.val < 104 then
                0xff000000
              else
                0x00ff0000
      else
        if q.val < 113 then
          if q.val < 109 then
            if q.val < 107 then
              if q.val < 106 then
                0xff000000
              else
                0xcccccccc
            else
              if q.val < 108 then
                0x000000ff
              else
                0x0000ff00
          else
            if q.val < 111 then
              if q.val < 110 then
                0x000000ff
              else
                0x000000ff
            else
              if q.val < 112 then
                0xff000000
              else
                0x0000ff00
        else
          if q.val < 117 then
            if q.val < 115 then
              if q.val < 114 then
                0x0000ff00
              else
                0x0000ff00
            else
              if q.val < 116 then
                0x00ff0000
              else
                0xff000000
          else
            if q.val < 119 then
              if q.val < 118 then
                0x00ff0000
              else
                0x0000ff00
            else
              if q.val < 120 then
                0x0000ff00
              else
                0x00ff0000
/-!
## 2. Five-Cell Window Invariant (`Win5Inv`) & `Halts reference ↔ Halts riemann121`
-/

/-- Pack 5 consecutive tape cells `[l₁, l₀, h, r₀, r₁]` into `Fin 32` (MSB = `l₁`). -/
def packWin5 (l₁ l₀ h r₀ r₁ : Fin 2) : Fin 32 :=
  ⟨16 * l₁.val + 8 * l₀.val + 4 * h.val + 2 * r₀.val + r₁.val, by omega⟩

/-- Extract the 5-cell window `[t.left.nth 1, t.left.nth 0, t.head, t.right.nth 0, t.right.nth 1]`
around the tape head. -/
def win5 (t : Tape (Fin 2)) : Fin 32 :=
  packWin5 (t.left.nth 1) (t.left.nth 0) t.head (t.right.nth 0) (t.right.nth 1)

/-- Test whether `(q, packWin5 l₁ l₀ h r₀ r₁)` belongs to the radius-2 window certificate. -/
def checkWin5Valid (q : Fin 121) (l₁ l₀ h r₀ r₁ : Fin 2) : Bool :=
  ((win5Masks q >>> (packWin5 l₁ l₀ h r₀ r₁).val.toUInt32) &&& 1) == 1

/-- 5-cell local window invariant for configurations of `riemann121`. -/
def Win5Inv (c : Cfg 121 2) : Bool :=
  checkWin5Valid c.state (c.tape.left.nth 1) (c.tape.left.nth 0) c.tape.head
    (c.tape.right.nth 0) (c.tape.right.nth 1)

/-- Check that stepping `(q, [l₁, l₀, h, r₀, r₁])` with newly exposed cell `ext` preserves
`checkWin5Valid`. -/
def checkWin5Step (q : Fin 121) (l₁ l₀ h r₀ r₁ ext : Fin 2) : Bool :=
  match rh121Trans q h with
  | none => true
  | some (w, Dir.right, q') => checkWin5Valid q' l₀ w r₀ r₁ ext
  | some (w, Dir.left, q') => checkWin5Valid q' ext l₁ l₀ w r₀

/-- Quotient state projection from `riemann121` (`Fin 121`) to `reference` (`Fin 120`),
merging compatible states `32` (`N24`) and `97` (`6.continue.2`) into state `32`. -/
def proj121To120 (q : Fin 121) : Fin 120 :=
  if q.val = 97 then ⟨32, by decide⟩
  else if h : q.val < 97 then ⟨q.val, by omega⟩
  else ⟨q.val - 1, by omega⟩

/-- Lift `proj121To120` to configurations. -/
def projCfg (c : Cfg 121 2) : Cfg 120 2 :=
  ⟨proj121To120 c.state, c.tape⟩

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
-- Finite window decision / large-step symbolic transition reduction.
theorem checkWin5Step_ok (q : Fin 121) (l₁ l₀ h r₀ r₁ ext : Fin 2) :
    checkWin5Valid q l₁ l₀ h r₀ r₁ = true →
    checkWin5Step q l₁ l₀ h r₀ r₁ ext = true := by
  revert q l₁ l₀ h r₀ r₁ ext; decide

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
-- Finite window decision / large-step symbolic transition reduction.
theorem proj_transition_eq (q : Fin 121) (l₁ l₀ h r₀ r₁ : Fin 2) :
    checkWin5Valid q l₁ l₀ h r₀ r₁ = true →
    riemann120.transition (proj121To120 q) h =
      (riemann121.transition q h).map fun t => (t.1, t.2.1, proj121To120 t.2.2) := by
  revert q l₁ l₀ h r₀ r₁; decide

theorem win5Inv_init : Win5Inv init = true := by
  decide

theorem win5Inv_step {c c' : Cfg 121 2} (hinv : Win5Inv c = true)
    (hs : step riemann121 c = some c') : Win5Inv c' = true := by
  obtain ⟨q, t⟩ := c
  dsimp only [Win5Inv] at hinv
  dsimp only [step] at hs
  rw [rh121Trans_eq] at hs
  rcases htr : rh121Trans q t.head with _ | ⟨w, d, q'⟩
  · rw [htr] at hs; cases hs
  · rw [htr] at hs
    injection hs with hs'
    subst hs'
    cases d with
    | left =>
      have hok := checkWin5Step_ok q (t.left.nth 1) (t.left.nth 0) t.head
        (t.right.nth 0) (t.right.nth 1) (t.left.nth 2) hinv
      simpa [checkWin5Step, htr, Win5Inv, Tape.move, Tape.write,
        ListBlank.nth_zero, ListBlank.nth_succ] using hok
    | right =>
      have hok := checkWin5Step_ok q (t.left.nth 1) (t.left.nth 0) t.head
        (t.right.nth 0) (t.right.nth 1) (t.right.nth 2) hinv
      simpa [checkWin5Step, htr, Win5Inv, Tape.move, Tape.write,
        ListBlank.nth_zero, ListBlank.nth_succ] using hok

theorem projCfg_step {c : Cfg 121 2} (hinv : Win5Inv c = true) :
    Option.map projCfg (step riemann121 c) = step riemann120 (projCfg c) := by
  obtain ⟨q, t⟩ := c
  dsimp only [step, projCfg]
  have htr := proj_transition_eq q (t.left.nth 1) (t.left.nth 0) t.head
    (t.right.nth 0) (t.right.nth 1) hinv
  rw [htr, Option.map_map, Option.map_map]
  rfl

theorem win5Inv_nSteps {n : ℕ} {c : Cfg 121 2} :
    ∀ {c₀ : Cfg 121 2}, Win5Inv c₀ = true → nSteps riemann121 n c₀ = some c → Win5Inv c = true := by
  induction n with
  | zero =>
    intro c₀ h₀ hs
    injection hs with hs'
    subst hs'
    exact h₀
  | succ n ih =>
    intro c₀ h₀ hs
    rw [nSteps_succ, Option.bind_eq_some_iff] at hs
    obtain ⟨c₁, hstep, hrest⟩ := hs
    exact ih (win5Inv_step h₀ hstep) hrest

theorem projCfg_nSteps_aux (n : ℕ) :
    ∀ (c₀ : Cfg 121 2), Win5Inv c₀ = true →
      Option.map projCfg (nSteps riemann121 n c₀) = nSteps riemann120 n (projCfg c₀) := by
  induction n with
  | zero =>
    intro c₀ _
    rfl
  | succ n ih =>
    intro c₀ h₀
    rw [nSteps_succ, nSteps_succ, ← projCfg_step h₀]
    rcases hs : step riemann121 c₀ with _ | c₁
    · rfl
    · exact ih c₁ (win5Inv_step h₀ hs)

theorem projCfg_nSteps (n : ℕ) :
    Option.map projCfg (nSteps riemann121 n init) = nSteps riemann120 n init :=
  projCfg_nSteps_aux n init win5Inv_init

theorem halts_riemann120_iff_halts_riemann121 :
    ConjectureMachines.Halts riemann120 ↔ ConjectureMachines.Halts riemann121 := by
  have hrel : Respects (step riemann121) (step riemann120)
      (fun c₁ c₂ => Win5Inv c₁ = true ∧ c₂ = projCfg c₁) := by
    intro c₁ c₂ ⟨hinv, hc₂⟩
    subst hc₂
    have hst := projCfg_step hinv
    rcases hs : step riemann121 c₁ with _ | c₁'
    · dsimp only
      rw [hs] at hst; simp only [Option.map_none] at hst; exact hst.symm
    · dsimp only
      rw [hs] at hst; simp only [Option.map_some] at hst
      exact ⟨projCfg c₁', ⟨win5Inv_step hinv hs, rfl⟩,
        Relation.TransGen.single hst.symm⟩
  exact tr_eval_dom' hrel ⟨win5Inv_init, rfl⟩




/-- Constructive trial-division primality test for `p : ℕ` avoiding `Classical.choice`. -/
def isPrimeBool (p : ℕ) : Bool :=
  decide (2 ≤ p) && (List.range p).all fun d => decide (d < 2) || (p % d != 0)

/-- Product of all primes `p ≤ n`. -/
def primorial : ℕ → ℕ
  | 0 => 1
  | n + 1 => if isPrimeBool (n + 1) then (n + 1) * primorial n else primorial n

/-- Self-sieving sequence `A_n = n! * P(n)`. -/
def shuniaProd (n : ℕ) : ℕ :=
  n.factorial * primorial n

/-- Offset base-`b` digit count `β_b(B)`: iterations of `B ↦ ⌊(B - 1) / b⌋` while `B > 0`. -/
def offsetDigits (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | B + 1 =>
    if _ : 2 ≤ b then 1 + offsetDigits b (B / b) else 0
  termination_by B => B
  decreasing_by exact Nat.lt_succ_of_le (Nat.div_le_self B b)

/-- Integer deficit `Δ_n = n - 1 - β_n(A_n - 1)`. -/
def shuniaDeficit (n : ℕ) : ℕ :=
  n - 1 - offsetDigits n (shuniaProd n - 1)

/-- Quartering clock `q_n = ⌊log_4(3n)⌋` computed on `z = n - 1`. -/
def quarterClock : ℕ → ℕ
  | 0 => 0
  | z + 1 => 1 + quarterClock (z / 4)

/-- Counterexample predicate `(q_n + 1) * 2 ^ q_n ≤ Δ_n`. -/
def ShuniaCounterexample (n : ℕ) : Prop :=
  (quarterClock (n - 1) + 1) * 2 ^ quarterClock (n - 1) ≤ shuniaDeficit n

instance instDecidableShuniaCounterexample (n : ℕ) : Decidable (ShuniaCounterexample n) :=
  inferInstanceAs (Decidable (_ ≤ _))

end ConjectureMachines.Riemann120

end
