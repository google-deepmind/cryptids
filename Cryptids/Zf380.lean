/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Zf393

/-!
# Zf380

380-state Turing machine halting-equivalent to the 393-state ZF machine.
-/

@[expose] public section

namespace ConjectureMachines.Zf380

open Turing (Dir)
open StateTransition Machines
open Zf393
  (zf393Trans_eq BootState stateOfBoot bitOfBool stepBootR stepBootL stepBoot runBoot
   bootChkL_7 bootChkR_7 boot_phase1_39734)

/-- 393-state ZF consistency reference machine (`zf_393`, Wade 2026). -/
abbrev reference : BundledMachine 2 := Machines.zf393.bundle

/-- 380-state ZF consistency candidate machine (`zf_380`). -/
abbrev candidate : BundledMachine 2 := Machines.zf380.bundle

/-- Alias for `Machines.zf393`. -/
abbrev refM : Machine 393 2 := Machines.zf393

/-- Alias for `Machines.zf380`. -/
abbrev candM : Machine 380 2 := Machines.zf380

def zf380Trans_0 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 6 then
    if q < 3 then
      if q < 1 then
        if a == 0 then some (1, .right, 1) else some (0, .left, 2)
      else
        if q < 2 then
          if a == 0 then some (0, .right, 2) else some (0, .right, 1)
        else
          if a == 0 then some (1, .left, 3) else some (0, .right, 4)
    else
      if q < 4 then
        if a == 0 then some (0, .left, 4) else some (0, .left, 65)
      else
        if q < 5 then
          if a == 0 then some (1, .left, 0) else some (0, .left, 1)
        else
          if a == 0 then some (1, .right, 6) else some (1, .left, 10)
  else
    if q < 9 then
      if q < 7 then
        if a == 0 then some (0, .right, 6) else some (0, .right, 7)
      else
        if q < 8 then
          if a == 0 then some (1, .right, 8) else some (1, .right, 7)
        else
          if a == 0 then some (0, .right, 9) else some (0, .right, 7)
    else
      if q < 10 then
        if a == 0 then some (0, .left, 5) else some (1, .right, 9)
      else
        if q < 11 then
          if a == 0 then some (0, .left, 26) else some (1, .right, 11)
        else
          if a == 0 then some (1, .right, 12) else some (0, .right, 11)

def zf380Trans_1 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 18 then
    if q < 15 then
      if q < 13 then
        if a == 0 then some (0, .left, 17) else some (1, .right, 9)
      else
        if q < 14 then
          if a == 0 then some (1, .right, 14) else none
        else
          if a == 0 then some (0, .right, 14) else some (1, .right, 15)
    else
      if q < 16 then
        if a == 0 then some (0, .right, 16) else some (1, .right, 15)
      else
        if q < 17 then
          if a == 0 then some (1, .left, 23) else some (1, .right, 15)
        else
          if a == 0 then some (1, .right, 18) else some (0, .left, 23)
  else
    if q < 21 then
      if q < 19 then
        if a == 0 then some (0, .right, 18) else some (1, .right, 19)
      else
        if q < 20 then
          if a == 0 then some (0, .right, 20) else some (1, .right, 19)
        else
          if a == 0 then some (0, .left, 21) else some (1, .right, 19)
    else
      if q < 22 then
        if a == 0 then some (1, .left, 22) else some (1, .right, 331)
      else
        if q < 23 then
          if a == 0 then some (0, .right, 17) else some (1, .left, 22)
        else
          if a == 0 then some (0, .left, 24) else some (1, .left, 23)

def zf380Trans_2 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 30 then
    if q < 27 then
      if q < 25 then
        if a == 0 then some (0, .left, 25) else some (1, .left, 23)
      else
        if q < 26 then
          if a == 0 then some (0, .left, 25) else some (0, .left, 61)
        else
          if a == 0 then some (0, .left, 27) else some (1, .left, 26)
    else
      if q < 28 then
        if a == 0 then some (0, .left, 28) else some (1, .left, 26)
      else
        if q < 29 then
          if a == 0 then some (0, .left, 28) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 49)
  else
    if q < 33 then
      if q < 31 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 50)
      else
        if q < 32 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 39)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 40)
    else
      if q < 34 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 29)
      else
        if q < 35 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 30)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 33)

def zf380Trans_3 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 42 then
    if q < 39 then
      if q < 37 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 34)
      else
        if q < 38 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 35)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 36)
    else
      if q < 40 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 5)
      else
        if q < 41 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 13)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 37)
  else
    if q < 45 then
      if q < 43 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 38)
      else
        if q < 44 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 41)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 42)
    else
      if q < 46 then
        if a == 0 then some (0, .left, 335) else some (1, .right, 43)
      else
        if q < 47 then
          if a == 0 then some (0, .left, 337) else some (1, .right, 44)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 31)

def zf380Trans_4 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 54 then
    if q < 51 then
      if q < 49 then
        if a == 0 then some (0, .right, 17) else some (1, .right, 32)
      else
        if q < 50 then
          if a == 0 then some (0, .right, 17) else some (1, .right, 47)
        else
          if a == 0 then some (0, .right, 17) else some (1, .right, 48)
    else
      if q < 52 then
        if a == 0 then some (0, .left, 52) else some (1, .left, 64)
      else
        if q < 53 then
          if a == 0 then some (0, .left, 53) else some (1, .left, 64)
        else
          if a == 0 then some (0, .left, 54) else some (1, .left, 64)
  else
    if q < 57 then
      if q < 55 then
        if a == 0 then some (0, .left, 55) else some (1, .left, 64)
      else
        if q < 56 then
          if a == 0 then some (0, .left, 56) else some (1, .left, 64)
        else
          if a == 0 then some (0, .left, 57) else some (1, .left, 64)
    else
      if q < 58 then
        if a == 0 then some (0, .left, 58) else some (1, .left, 64)
      else
        if q < 59 then
          if a == 0 then some (0, .left, 59) else some (1, .left, 64)
        else
          if a == 0 then some (0, .right, 60) else some (1, .left, 64)

def zf380Trans_5 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 66 then
    if q < 63 then
      if q < 61 then
        if a == 0 then some (0, .right, 60) else some (1, .right, 97)
      else
        if q < 62 then
          if a == 0 then some (1, .left, 64) else some (0, .left, 61)
        else
          if a == 0 then some (0, .left, 61) else some (0, .left, 62)
    else
      if q < 64 then
        if a == 0 then some (0, .left, 62) else some (0, .left, 63)
      else
        if q < 65 then
          if a == 0 then some (0, .left, 51) else some (1, .left, 64)
        else
          if a == 0 then some (0, .left, 66) else some (1, .left, 64)
  else
    if q < 69 then
      if q < 67 then
        some (0, .left, 65)
      else
        if q < 68 then
          if a == 0 then some (0, .right, 285) else some (1, .right, 68)
        else
          if a == 0 then some (0, .right, 290) else some (1, .right, 366)
    else
      if q < 70 then
        if a == 0 then some (0, .right, 70) else some (0, .left, 62)
      else
        if q < 71 then
          if a == 0 then some (0, .right, 29) else some (1, .right, 71)
        else
          if a == 0 then some (0, .right, 72) else some (1, .right, 75)

def zf380Trans_6 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 78 then
    if q < 75 then
      if q < 73 then
        if a == 0 then some (0, .right, 29) else some (1, .right, 73)
      else
        if q < 74 then
          if a == 0 then some (0, .right, 74) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 30) else some (1, .left, 355)
    else
      if q < 76 then
        if a == 0 then some (0, .right, 76) else some (0, .left, 62)
      else
        if q < 77 then
          if a == 0 then some (0, .right, 30) else some (1, .right, 285)
        else
          if a == 0 then some (0, .right, 69) else some (1, .right, 78)
  else
    if q < 81 then
      if q < 79 then
        if a == 0 then some (0, .left, 99) else some (1, .left, 340)
      else
        if q < 80 then
          if a == 0 then some (0, .right, 69) else some (1, .right, 80)
        else
          if a == 0 then some (0, .left, 100) else some (1, .left, 340)
    else
      if q < 82 then
        if a == 0 then some (0, .right, 29) else some (1, .right, 82)
      else
        if q < 83 then
          if a == 0 then some (0, .right, 371) else some (1, .right, 361)
        else
          if a == 0 then some (0, .right, 84) else some (1, .right, 88)

def zf380Trans_7 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 90 then
    if q < 87 then
      if q < 85 then
        if a == 0 then some (0, .right, 43) else some (1, .right, 85)
      else
        if q < 86 then
          if a == 0 then some (0, .right, 86) else some (1, .right, 87)
        else
          if a == 0 then some (0, .right, 45) else some (0, .left, 45)
    else
      if q < 88 then
        if a == 0 then some (0, .right, 366) else some (0, .left, 63)
      else
        if q < 89 then
          if a == 0 then some (0, .right, 45) else some (1, .right, 89)
        else
          if a == 0 then some (0, .right, 370) else some (0, .left, 62)
  else
    if q < 93 then
      if q < 91 then
        if a == 0 then some (0, .right, 83) else some (1, .right, 371)
      else
        if q < 92 then
          if a == 0 then some (0, .right, 83) else some (1, .right, 92)
        else
          if a == 0 then some (0, .right, 341) else some (1, .right, 354)
    else
      if q < 94 then
        if a == 0 then some (0, .right, 94) else some (1, .right, 95)
      else
        if q < 95 then
          if a == 0 then some (0, .right, 39) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 336) else some (1, .right, 96)

def zf380Trans_8 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 102 then
    if q < 99 then
      if q < 97 then
        if a == 0 then some (0, .right, 352) else some (1, .right, 32)
      else
        if q < 98 then
          if a == 0 then some (0, .right, 93) else some (1, .right, 98)
        else
          if a == 0 then some (0, .right, 335) else some (1, .right, 99)
    else
      if q < 100 then
        if a == 0 then some (0, .right, 339) else some (1, .right, 100)
      else
        if q < 101 then
          if a == 0 then some (0, .right, 345) else some (1, .right, 101)
        else
          if a == 0 then some (0, .right, 348) else some (1, .right, 102)
  else
    if q < 105 then
      if q < 103 then
        if a == 0 then some (0, .right, 266) else some (1, .right, 103)
      else
        if q < 104 then
          if a == 0 then some (0, .right, 351) else some (1, .right, 104)
        else
          if a == 0 then some (0, .right, 266) else some (1, .right, 105)
    else
      if q < 106 then
        if a == 0 then some (0, .right, 354) else some (1, .right, 106)
      else
        if q < 107 then
          if a == 0 then some (0, .right, 266) else some (1, .right, 107)
        else
          if a == 0 then some (0, .right, 356) else some (1, .right, 108)

def zf380Trans_9 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 114 then
    if q < 111 then
      if q < 109 then
        if a == 0 then some (0, .right, 266) else some (1, .right, 109)
      else
        if q < 110 then
          if a == 0 then some (0, .right, 358) else some (1, .right, 110)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 111)
    else
      if q < 112 then
        if a == 0 then some (0, .right, 317) else some (1, .right, 112)
      else
        if q < 113 then
          if a == 0 then some (0, .right, 274) else some (1, .right, 113)
        else
          if a == 0 then some (0, .right, 263) else some (1, .right, 114)
  else
    if q < 117 then
      if q < 115 then
        if a == 0 then some (0, .right, 316) else some (1, .right, 115)
      else
        if q < 116 then
          if a == 0 then some (0, .right, 255) else some (1, .right, 116)
        else
          if a == 0 then some (0, .right, 267) else some (1, .right, 117)
    else
      if q < 118 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 118)
      else
        if q < 119 then
          if a == 0 then some (0, .right, 315) else some (1, .right, 119)
        else
          if a == 0 then some (0, .right, 247) else some (1, .right, 120)

def zf380Trans_10 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 126 then
    if q < 123 then
      if q < 121 then
        if a == 0 then some (0, .right, 236) else some (1, .right, 121)
      else
        if q < 122 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 122)
        else
          if a == 0 then some (0, .right, 236) else some (1, .right, 123)
    else
      if q < 124 then
        if a == 0 then some (0, .right, 246) else some (1, .right, 124)
      else
        if q < 125 then
          if a == 0 then some (0, .right, 318) else some (1, .right, 125)
        else
          if a == 0 then some (0, .right, 267) else some (1, .right, 126)
  else
    if q < 129 then
      if q < 127 then
        if a == 0 then some (0, .right, 243) else some (1, .right, 127)
      else
        if q < 128 then
          if a == 0 then some (0, .right, 317) else some (1, .right, 128)
        else
          if a == 0 then some (0, .right, 316) else some (1, .right, 129)
    else
      if q < 130 then
        if a == 0 then some (0, .right, 245) else some (1, .right, 130)
      else
        if q < 131 then
          if a == 0 then some (0, .right, 269) else some (1, .right, 131)
        else
          if a == 0 then some (0, .right, 239) else some (1, .right, 132)

def zf380Trans_11 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 138 then
    if q < 135 then
      if q < 133 then
        if a == 0 then some (0, .right, 379) else some (1, .right, 133)
      else
        if q < 134 then
          if a == 0 then some (0, .right, 294) else some (1, .right, 134)
        else
          if a == 0 then some (0, .right, 271) else some (1, .right, 135)
    else
      if q < 136 then
        if a == 0 then some (0, .right, 243) else some (1, .right, 136)
      else
        if q < 137 then
          if a == 0 then some (0, .right, 281) else some (1, .right, 137)
        else
          if a == 0 then some (0, .right, 245) else some (1, .right, 138)
  else
    if q < 141 then
      if q < 139 then
        if a == 0 then some (0, .right, 250) else some (1, .right, 139)
      else
        if q < 140 then
          if a == 0 then some (0, .right, 239) else some (1, .right, 140)
        else
          if a == 0 then some (0, .right, 294) else some (1, .right, 141)
    else
      if q < 142 then
        if a == 0 then some (0, .right, 379) else some (1, .right, 142)
      else
        if q < 143 then
          if a == 0 then some (0, .right, 296) else some (1, .right, 143)
        else
          if a == 0 then some (0, .right, 224) else some (1, .right, 144)

def zf380Trans_12 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 150 then
    if q < 147 then
      if q < 145 then
        if a == 0 then some (0, .right, 296) else some (1, .right, 145)
      else
        if q < 146 then
          if a == 0 then some (0, .right, 324) else some (1, .right, 146)
        else
          if a == 0 then some (0, .right, 268) else some (1, .right, 147)
    else
      if q < 148 then
        if a == 0 then some (0, .right, 252) else some (1, .right, 148)
      else
        if q < 149 then
          if a == 0 then some (0, .right, 298) else some (1, .right, 149)
        else
          if a == 0 then some (0, .right, 252) else some (1, .right, 150)
  else
    if q < 153 then
      if q < 151 then
        if a == 0 then some (0, .right, 268) else some (1, .right, 151)
      else
        if q < 152 then
          if a == 0 then some (0, .right, 318) else some (1, .right, 152)
        else
          if a == 0 then some (0, .right, 344) else some (1, .right, 153)
    else
      if q < 154 then
        if a == 0 then some (0, .right, 354) else some (1, .right, 154)
      else
        if q < 155 then
          if a == 0 then some (0, .right, 253) else some (1, .right, 155)
        else
          if a == 0 then some (0, .right, 347) else some (1, .right, 156)

def zf380Trans_13 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 162 then
    if q < 159 then
      if q < 157 then
        if a == 0 then some (0, .right, 356) else some (1, .right, 157)
      else
        if q < 158 then
          if a == 0 then some (0, .right, 253) else some (1, .right, 158)
        else
          if a == 0 then some (0, .right, 229) else some (1, .right, 159)
    else
      if q < 160 then
        if a == 0 then some (0, .right, 324) else some (1, .right, 160)
      else
        if q < 161 then
          if a == 0 then some (0, .right, 326) else some (1, .right, 161)
        else
          if a == 0 then some (0, .right, 251) else some (1, .right, 162)
  else
    if q < 165 then
      if q < 163 then
        if a == 0 then some (0, .right, 269) else some (1, .right, 163)
      else
        if q < 164 then
          if a == 0 then some (0, .right, 275) else some (1, .right, 164)
        else
          if a == 0 then some (0, .right, 320) else some (1, .right, 165)
    else
      if q < 166 then
        if a == 0 then some (0, .right, 257) else some (1, .right, 166)
      else
        if q < 167 then
          if a == 0 then some (0, .right, 241) else some (1, .right, 167)
        else
          if a == 0 then some (0, .right, 324) else some (1, .right, 168)

def zf380Trans_14 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 174 then
    if q < 171 then
      if q < 169 then
        if a == 0 then some (0, .right, 270) else some (1, .right, 169)
      else
        if q < 170 then
          if a == 0 then some (0, .right, 324) else some (1, .right, 170)
        else
          if a == 0 then some (0, .right, 224) else some (1, .right, 171)
    else
      if q < 172 then
        if a == 0 then some (0, .right, 322) else some (1, .right, 172)
      else
        if q < 173 then
          if a == 0 then some (0, .right, 298) else some (1, .right, 173)
        else
          if a == 0 then some (0, .right, 296) else some (1, .right, 174)
  else
    if q < 177 then
      if q < 175 then
        if a == 0 then some (0, .right, 242) else some (1, .right, 175)
      else
        if q < 176 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 176)
        else
          if a == 0 then some (0, .right, 270) else some (1, .right, 177)
    else
      if q < 178 then
        if a == 0 then some (0, .right, 271) else some (1, .right, 178)
      else
        if q < 179 then
          if a == 0 then some (0, .right, 298) else some (1, .right, 179)
        else
          if a == 0 then some (0, .right, 377) else some (1, .right, 180)

def zf380Trans_15 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 186 then
    if q < 183 then
      if q < 181 then
        if a == 0 then some (0, .right, 265) else some (1, .right, 181)
      else
        if q < 182 then
          if a == 0 then some (0, .right, 316) else some (1, .right, 182)
        else
          if a == 0 then some (0, .right, 272) else some (1, .right, 183)
    else
      if q < 184 then
        if a == 0 then some (0, .right, 322) else some (1, .right, 184)
      else
        if q < 185 then
          if a == 0 then some (0, .right, 246) else some (1, .right, 185)
        else
          if a == 0 then some (0, .right, 261) else some (1, .right, 186)
  else
    if q < 189 then
      if q < 187 then
        if a == 0 then some (0, .right, 272) else some (1, .right, 187)
      else
        if q < 188 then
          if a == 0 then some (0, .right, 248) else some (1, .right, 188)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 189)
    else
      if q < 190 then
        if a == 0 then some (0, .right, 255) else some (1, .right, 190)
      else
        if q < 191 then
          if a == 0 then some (0, .right, 273) else some (1, .right, 191)
        else
          if a == 0 then some (0, .right, 77) else some (1, .right, 192)

def zf380Trans_16 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 198 then
    if q < 195 then
      if q < 193 then
        if a == 0 then some (0, .right, 278) else some (1, .right, 193)
      else
        if q < 194 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 194)
        else
          if a == 0 then some (0, .right, 376) else some (1, .right, 195)
    else
      if q < 196 then
        if a == 0 then some (0, .right, 346) else some (1, .right, 196)
      else
        if q < 197 then
          if a == 0 then some (0, .right, 356) else some (1, .right, 197)
        else
          if a == 0 then some (0, .right, 91) else some (1, .right, 198)
  else
    if q < 201 then
      if q < 199 then
        if a == 0 then some (0, .right, 273) else some (1, .right, 199)
      else
        if q < 200 then
          if a == 0 then some (0, .right, 257) else some (1, .right, 200)
        else
          if a == 0 then some (0, .right, 229) else some (1, .right, 201)
    else
      if q < 202 then
        if a == 0 then some (0, .right, 267) else some (1, .right, 202)
      else
        if q < 203 then
          if a == 0 then some (0, .right, 296) else some (1, .right, 203)
        else
          if a == 0 then some (0, .right, 264) else some (1, .right, 204)

def zf380Trans_17 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 210 then
    if q < 207 then
      if q < 205 then
        if a == 0 then some (0, .right, 258) else some (1, .right, 205)
      else
        if q < 206 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 206)
        else
          if a == 0 then some (0, .right, 258) else some (1, .right, 207)
    else
      if q < 208 then
        if a == 0 then some (0, .right, 247) else some (1, .right, 208)
      else
        if q < 209 then
          if a == 0 then some (0, .right, 315) else some (1, .right, 209)
        else
          if a == 0 then some (0, .right, 274) else some (1, .right, 210)
  else
    if q < 213 then
      if q < 211 then
        if a == 0 then some (0, .right, 322) else some (1, .right, 211)
      else
        if q < 212 then
          if a == 0 then some (0, .right, 259) else some (1, .right, 212)
        else
          if a == 0 then some (0, .right, 377) else some (1, .right, 213)
    else
      if q < 214 then
        if a == 0 then some (0, .right, 259) else some (1, .right, 214)
      else
        if q < 215 then
          if a == 0 then some (0, .right, 274) else some (1, .right, 215)
        else
          if a == 0 then some (0, .right, 248) else some (1, .right, 216)

def zf380Trans_18 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 222 then
    if q < 219 then
      if q < 217 then
        if a == 0 then some (0, .right, 250) else some (1, .right, 217)
      else
        if q < 218 then
          if a == 0 then some (0, .right, 269) else some (1, .right, 218)
        else
          if a == 0 then some (0, .right, 250) else some (1, .right, 219)
    else
      if q < 220 then
        if a == 0 then some (0, .right, 301) else some (1, .right, 220)
      else
        if q < 221 then
          if a == 0 then some (0, .right, 47) else some (1, .right, 221)
        else
          if a == 0 then some (0, .right, 222) else none
  else
    if q < 225 then
      if q < 223 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 223)
      else
        if q < 224 then
          if a == 0 then some (0, .right, 284) else some (0, .left, 62)
        else
          if a == 0 then some (0, .right, 241) else some (1, .right, 225)
    else
      if q < 226 then
        if a == 0 then some (0, .right, 322) else some (1, .right, 226)
      else
        if q < 227 then
          if a == 0 then some (0, .right, 270) else some (1, .right, 227)
        else
          if a == 0 then some (0, .right, 242) else some (1, .right, 228)

def zf380Trans_19 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 234 then
    if q < 231 then
      if q < 229 then
        if a == 0 then some (0, .right, 324) else some (1, .right, 278)
      else
        if q < 230 then
          if a == 0 then some (0, .right, 251) else some (1, .right, 230)
        else
          if a == 0 then some (0, .right, 320) else some (1, .right, 231)
    else
      if q < 232 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 232)
      else
        if q < 233 then
          if a == 0 then some (0, .right, 296) else some (1, .right, 233)
        else
          if a == 0 then some (0, .right, 257) else some (1, .right, 234)
  else
    if q < 237 then
      if q < 235 then
        if a == 0 then some (0, .right, 268) else some (1, .right, 235)
      else
        if q < 236 then
          if a == 0 then some (0, .right, 279) else some (1, .right, 275)
        else
          if a == 0 then some (0, .right, 317) else some (1, .right, 237)
    else
      if q < 238 then
        if a == 0 then some (0, .right, 262) else some (1, .right, 238)
      else
        if q < 239 then
          if a == 0 then some (0, .right, 263) else some (1, .right, 267)
        else
          if a == 0 then some (0, .right, 246) else some (1, .right, 240)

def zf380Trans_20 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 246 then
    if q < 243 then
      if q < 241 then
        if a == 0 then some (0, .right, 267) else some (1, .right, 279)
      else
        if q < 242 then
          if a == 0 then some (0, .right, 244) else some (1, .right, 282)
        else
          if a == 0 then some (0, .right, 322) else some (1, .right, 244)
    else
      if q < 244 then
        if a == 0 then some (0, .right, 264) else some (1, .right, 281)
      else
        if q < 245 then
          if a == 0 then some (0, .right, 265) else some (1, .right, 275)
        else
          if a == 0 then some (0, .right, 322) else some (1, .right, 262)
  else
    if q < 249 then
      if q < 247 then
        if a == 0 then some (0, .right, 261) else some (1, .right, 377)
      else
        if q < 248 then
          if a == 0 then some (0, .right, 316) else some (1, .right, 261)
        else
          if a == 0 then some (0, .right, 322) else some (1, .right, 249)
    else
      if q < 250 then
        if a == 0 then some (0, .right, 377) else some (1, .right, 250)
      else
        if q < 251 then
          if a == 0 then some (0, .right, 318) else some (1, .left, 263)
        else
          if a == 0 then some (0, .right, 279) else some (1, .right, 270)

def zf380Trans_21 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 258 then
    if q < 255 then
      if q < 253 then
        if a == 0 then some (0, .right, 275) else some (1, .right, 322)
      else
        if q < 254 then
          if a == 0 then some (0, .right, 350) else some (1, .right, 254)
        else
          if a == 0 then some (0, .right, 358) else some (1, .right, 90)
    else
      if q < 256 then
        if a == 0 then some (0, .right, 315) else some (1, .right, 256)
      else
        if q < 257 then
          if a == 0 then some (0, .right, 324) else some (1, .right, 377)
        else
          if a == 0 then some (0, .right, 280) else some (1, .right, 320)
  else
    if q < 261 then
      if q < 259 then
        if a == 0 then some (0, .right, 300) else some (1, .right, 276)
      else
        if q < 260 then
          if a == 0 then some (0, .right, 315) else some (1, .right, 260)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 324)
    else
      if q < 262 then
        if a == 0 then some (0, .right, 316) else some (1, .right, 276)
      else
        if q < 263 then
          if a == 0 then some (0, .right, 317) else some (1, .right, 283)
        else
          if a == 0 then some (0, .left, 115) else some (1, .right, 269)

def zf380Trans_22 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 270 then
    if q < 267 then
      if q < 265 then
        if a == 0 then some (0, .right, 277) else some (1, .right, 315)
      else
        if q < 266 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 277)
        else
          if a == 0 then some (0, .right, 309) else some (1, .right, 367)
    else
      if q < 268 then
        if a == 0 then some (0, .left, 150) else some (1, .right, 326)
      else
        if q < 269 then
          if a == 0 then some (0, .right, 320) else some (1, .right, 377)
        else
          if a == 0 then some (0, .left, 244) else some (1, .right, 320)
  else
    if q < 273 then
      if q < 271 then
        if a == 0 then some (0, .right, 296) else some (1, .right, 298)
      else
        if q < 272 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 294)
        else
          if a == 0 then some (0, .right, 316) else some (1, .right, 300)
    else
      if q < 274 then
        if a == 0 then some (0, .right, 301) else some (1, .right, 79)
      else
        if q < 275 then
          if a == 0 then some (0, .right, 315) else some (1, .right, 316)
        else
          if a == 0 then some (0, .right, 294) else some (1, .right, 296)

def zf380Trans_23 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 282 then
    if q < 279 then
      if q < 277 then
        if a == 0 then some (0, .left, 207) else some (1, .left, 262)
      else
        if q < 278 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 301)
        else
          if a == 0 then some (0, .right, 298) else some (1, .right, 294)
    else
      if q < 280 then
        if a == 0 then some (0, .right, 301) else some (1, .right, 294)
      else
        if q < 281 then
          if a == 0 then some (0, .right, 294) else some (1, .right, 298)
        else
          if a == 0 then some (0, .right, 316) else some (1, .right, 317)
  else
    if q < 285 then
      if q < 283 then
        if a == 0 then some (0, .right, 324) else some (1, .right, 280)
      else
        if q < 284 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 322)
        else
          if a == 0 then some (0, .right, 48) else some (1, .right, 48)
    else
      if q < 286 then
        if a == 0 then some (0, .right, 310) else some (1, .right, 369)
      else
        if q < 287 then
          if a == 0 then some (0, .right, 372) else some (1, .right, 287)
        else
          if a == 0 then some (0, .right, 49) else some (1, .right, 288)

def zf380Trans_24 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 294 then
    if q < 291 then
      if q < 289 then
        if a == 0 then some (0, .right, 289) else some (0, .left, 332)
      else
        if q < 290 then
          if a == 0 then some (0, .right, 42) else some (1, .right, 376)
        else
          if a == 0 then some (0, .right, 363) else some (1, .right, 291)
    else
      if q < 292 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 292)
      else
        if q < 293 then
          if a == 0 then some (0, .right, 293) else some (0, .left, 332)
        else
          if a == 0 then some (0, .right, 44) else some (1, .right, 375)
  else
    if q < 297 then
      if q < 295 then
        if a == 0 then some (0, .right, 300) else some (1, .right, 295)
      else
        if q < 296 then
          if a == 0 then some (0, .right, 78) else some (1, .right, 354)
        else
          if a == 0 then some (0, .right, 300) else some (1, .right, 297)
    else
      if q < 298 then
        if a == 0 then some (0, .right, 80) else some (1, .right, 356)
      else
        if q < 299 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 299)
        else
          if a == 0 then some (0, .right, 349) else some (1, .right, 358)

def zf380Trans_25 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 306 then
    if q < 303 then
      if q < 301 then
        if a == 0 then some (0, .right, 286) else some (1, .right, 362)
      else
        if q < 302 then
          if a == 0 then some (0, .right, 375) else some (1, .right, 302)
        else
          if a == 0 then some (0, .right, 311) else some (1, .right, 303)
    else
      if q < 304 then
        if a == 0 then some (0, .right, 369) else some (1, .right, 304)
      else
        if q < 305 then
          if a == 0 then some (0, .right, 81) else some (1, .right, 348)
        else
          if a == 0 then some (0, .right, 43) else some (0, .left, 343)
  else
    if q < 309 then
      if q < 307 then
        if a == 0 then some (0, .right, 42) else some (1, .right, 307)
      else
        if q < 308 then
          if a == 0 then some (0, .right, 305) else some (1, .right, 308)
        else
          if a == 0 then some (0, .right, 361) else some (0, .left, 288)
    else
      if q < 310 then
        if a == 0 then some (0, .right, 39) else some (1, .right, 306)
      else
        if q < 311 then
          if a == 0 then some (0, .right, 49) else some (1, .right, 306)
        else
          if a == 0 then some (0, .right, 49) else some (1, .right, 312)

def zf380Trans_26 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 318 then
    if q < 315 then
      if q < 313 then
        if a == 0 then some (0, .right, 48) else some (1, .right, 313)
      else
        if q < 314 then
          if a == 0 then some (0, .right, 305) else some (1, .right, 314)
        else
          if a == 0 then some (0, .right, 376) else some (0, .left, 288)
    else
      if q < 316 then
        if a == 0 then some (0, .right, 300) else some (1, .right, 48)
      else
        if q < 317 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 284)
        else
          if a == 0 then some (0, .right, 315) else some (1, .right, 284)
  else
    if q < 321 then
      if q < 319 then
        if a == 0 then some (0, .right, 379) else some (1, .right, 319)
      else
        if q < 320 then
          if a == 0 then some (0, .right, 377) else some (1, .right, 379)
        else
          if a == 0 then some (0, .right, 67) else some (1, .right, 321)
    else
      if q < 322 then
        if a == 0 then some (0, .right, 276) else some (1, .right, 67)
      else
        if q < 323 then
          if a == 0 then some (0, .right, 67) else some (1, .right, 323)
        else
          if a == 0 then some (0, .right, 315) else some (1, .right, 67)

def zf380Trans_27 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 330 then
    if q < 327 then
      if q < 325 then
        if a == 0 then some (0, .right, 67) else some (1, .right, 325)
      else
        if q < 326 then
          if a == 0 then some (0, .right, 300) else some (1, .right, 67)
        else
          if a == 0 then some (0, .right, 379) else some (1, .right, 327)
    else
      if q < 328 then
        if a == 0 then some (0, .right, 320) else some (1, .right, 379)
      else
        if q < 329 then
          if a == 0 then some (0, .right, 44) else some (0, .left, 335)
        else
          if a == 0 then some (0, .right, 44) else some (1, .right, 328)
  else
    if q < 333 then
      if q < 331 then
        if a == 0 then some (0, .right, 331) else some (0, .left, 335)
      else
        if q < 332 then
          if a == 0 then some (0, .right, 48) else some (1, .left, 329)
        else
          if a == 0 then some (0, .right, 333) else some (0, .left, 335)
    else
      if q < 334 then
        if a == 0 then some (0, .right, 42) else some (1, .right, 46)
      else
        if q < 335 then
          if a == 0 then some (0, .right, 46) else some (0, .left, 335)
        else
          if a == 0 then some (0, .right, 29) else some (0, .left, 64)

def zf380Trans_28 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 342 then
    if q < 339 then
      if q < 337 then
        if a == 0 then some (0, .right, 31) else some (1, .right, 337)
      else
        if q < 338 then
          if a == 0 then some (0, .right, 338) else some (1, .left, 329)
        else
          if a == 0 then some (0, .right, 42) else some (1, .left, 346)
    else
      if q < 340 then
        if a == 0 then some (0, .left, 152) else some (1, .left, 98)
      else
        if q < 341 then
          if a == 0 then some (0, .right, 349) else some (1, .left, 270)
        else
          if a == 0 then some (0, .right, 33) else some (1, .right, 342)
  else
    if q < 345 then
      if q < 343 then
        if a == 0 then some (0, .right, 343) else some (0, .left, 335)
      else
        if q < 344 then
          if a == 0 then some (0, .left, 332) else some (1, .right, 48)
        else
          if a == 0 then some (0, .right, 33) else some (1, .right, 334)
    else
      if q < 346 then
        if a == 0 then some (0, .right, 35) else some (0, .left, 64)
      else
        if q < 347 then
          if a == 0 then some (0, .left, 352) else some (1, .right, 332)
        else
          if a == 0 then some (0, .left, 195) else some (1, .right, 334)

def zf380Trans_29 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 354 then
    if q < 351 then
      if q < 349 then
        if a == 0 then some (0, .left, 299) else some (0, .left, 64)
      else
        if q < 350 then
          if a == 0 then some (0, .right, 37) else some (1, .right, 330)
        else
          if a == 0 then some (0, .right, 37) else some (1, .right, 332)
    else
      if q < 352 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 74)
      else
        if q < 353 then
          if a == 0 then some (0, .left, 339) else some (1, .right, 353)
        else
          if a == 0 then some (0, .right, 32) else some (0, .left, 335)
  else
    if q < 357 then
      if q < 355 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 355)
      else
        if q < 356 then
          if a == 0 then some (0, .right, 34) else some (1, .left, 347)
        else
          if a == 0 then some (0, .right, 41) else some (1, .right, 357)
    else
      if q < 358 then
        if a == 0 then some (0, .right, 36) else some (0, .left, 335)
      else
        if q < 359 then
          if a == 0 then some (0, .right, 41) else some (1, .right, 359)
        else
          if a == 0 then some (0, .right, 38) else some (0, .left, 335)

def zf380Trans_30 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 366 then
    if q < 363 then
      if q < 361 then
        if a == 0 then some (0, .right, 329) else some (1, .right, 21)
      else
        if q < 362 then
          if a == 0 then some (0, .right, 41) else some (1, .left, 360)
        else
          if a == 0 then some (0, .right, 41) else some (1, .right, 374)
    else
      if q < 364 then
        if a == 0 then some (0, .right, 41) else some (1, .right, 364)
      else
        if q < 365 then
          if a == 0 then some (0, .right, 365) else some (0, .left, 335)
        else
          if a == 0 then some (0, .right, 48) else some (1, .right, 44)
  else
    if q < 369 then
      if q < 367 then
        if a == 0 then some (0, .right, 43) else some (1, .left, 82)
      else
        if q < 368 then
          if a == 0 then some (0, .right, 43) else some (1, .right, 368)
        else
          if a == 0 then some (0, .right, 40) else some (0, .left, 335)
    else
      if q < 370 then
        if a == 0 then some (0, .right, 43) else some (1, .right, 374)
      else
        if q < 371 then
          if a == 0 then some (0, .right, 45) else some (0, .left, 64)
        else
          if a == 0 then some (0, .right, 47) else some (0, .left, 64)

def zf380Trans_31 (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 376 then
    if q < 374 then
      if q < 373 then
        if a == 0 then some (0, .right, 47) else some (1, .right, 373)
      else
        if a == 0 then some (0, .right, 374) else some (0, .left, 335)
    else
      if q < 375 then
        if a == 0 then some (0, .right, 50) else some (1, .left, 329)
      else
        if a == 0 then some (0, .right, 47) else some (1, .right, 338)
  else
    if q < 378 then
      if q < 377 then
        if a == 0 then some (0, .left, 286) else some (1, .left, 360)
      else
        if a == 0 then some (0, .right, 67) else some (1, .right, 378)
    else
      if q < 379 then
        if a == 0 then some (0, .right, 316) else some (1, .right, 67)
      else
        if a == 0 then some (0, .right, 317) else some (1, .right, 67)

def zf380Trans (q : Nat) (a : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  if q < 192 then
    if q < 96 then
      if q < 48 then
        if q < 24 then
          if q < 12 then
            zf380Trans_0 q a
          else
            zf380Trans_1 q a
        else
          if q < 36 then
            zf380Trans_2 q a
          else
            zf380Trans_3 q a
      else
        if q < 72 then
          if q < 60 then
            zf380Trans_4 q a
          else
            zf380Trans_5 q a
        else
          if q < 84 then
            zf380Trans_6 q a
          else
            zf380Trans_7 q a
    else
      if q < 144 then
        if q < 120 then
          if q < 108 then
            zf380Trans_8 q a
          else
            zf380Trans_9 q a
        else
          if q < 132 then
            zf380Trans_10 q a
          else
            zf380Trans_11 q a
      else
        if q < 168 then
          if q < 156 then
            zf380Trans_12 q a
          else
            zf380Trans_13 q a
        else
          if q < 180 then
            zf380Trans_14 q a
          else
            zf380Trans_15 q a
  else
    if q < 288 then
      if q < 240 then
        if q < 216 then
          if q < 204 then
            zf380Trans_16 q a
          else
            zf380Trans_17 q a
        else
          if q < 228 then
            zf380Trans_18 q a
          else
            zf380Trans_19 q a
      else
        if q < 264 then
          if q < 252 then
            zf380Trans_20 q a
          else
            zf380Trans_21 q a
        else
          if q < 276 then
            zf380Trans_22 q a
          else
            zf380Trans_23 q a
    else
      if q < 336 then
        if q < 312 then
          if q < 300 then
            zf380Trans_24 q a
          else
            zf380Trans_25 q a
        else
          if q < 324 then
            zf380Trans_26 q a
          else
            zf380Trans_27 q a
      else
        if q < 360 then
          if q < 348 then
            zf380Trans_28 q a
          else
            zf380Trans_29 q a
        else
          if q < 372 then
            zf380Trans_30 q a
          else
            zf380Trans_31 q a

set_option maxRecDepth 200000

def allBelowNat : Nat → (Nat → Bool) → Bool
  | 0, _ => true
  | n + 1, p => p n && allBelowNat n p

theorem of_allBelowNat {p : Nat → Bool} : ∀ {n : Nat}, allBelowNat n p = true → ∀ q < n, p q = true
  | 0, _, _, hq => absurd hq (Nat.not_lt_zero _)
  | _ + 1, h, q, hq => by
    simp only [allBelowNat, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hlt | rfl
    · exact of_allBelowNat h.2 q hlt
    · exact h.1

theorem of_fin_nat {n : Nat} {p : Nat → Bool} (h : allBelowNat n p = true) (q : Fin n) :
    p q.val = true :=
  of_allBelowNat h q.val q.isLt

def all2 (f : Fin 2 → Bool) : Bool := f 0 && f 1

theorem of_all2 {f : Fin 2 → Bool} (h : all2 f = true) (a : Fin 2) : f a = true := by
  rcases a with ⟨_ | _ | _, ha⟩
  · exact ((Bool.and_eq_true _ _).mp h).1
  · exact ((Bool.and_eq_true _ _).mp h).2
  · omega

theorem candM_transition_eq_nat (q : Fin 380) (a : Fin 2) :
    candM.transition q a = zf380Trans q.val a := by
  revert q a; decide


theorem candidate_fewer_states : candidate.states < reference.states := by
  decide

set_option maxRecDepth 200000

def nSteps {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) : Cfg N 2 → Option (Cfg N 2) :=
  Nat.rec (motive := fun _ => Cfg N 2 → Option (Cfg N 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero {N : ℕ} [NeZero N] (M : Machine N 2) (c : Cfg N 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) (c : Cfg N 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {N : ℕ} [NeZero N] {M : Machine N 2} {n : ℕ} {c c' : Cfg N 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_eval_dom {N : ℕ} [NeZero N] {M : Machine N 2} {n : ℕ} {c c' : Cfg N 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [reaches_eval' (nSteps_reaches h)]

def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

theorem mkL_cons_eq_mk'_cons (l : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons l) R = Tape.mk' L (R.cons l) := by
  simp [Tape.mkL, Tape.mk']

theorem default_cons_zero :
    (default : ListBlank (Fin 2)).cons 0 = default :=
  ListBlank.cons_default_default

theorem step_mk'_none {N : ℕ} [NeZero N] {M : Machine N 2} {q : Fin N} {a : Fin 2}
    (h : M.transition q a = none) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, h, Tape.mk']

theorem step_mk'_right {N : ℕ} [NeZero N] {M : Machine N 2} {q q' : Fin N} {a b : Fin 2}
    (h : M.transition q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {N : ℕ} [NeZero N] {M : Machine N 2} {q q' : Fin N} {a b : Fin 2}
    (h : M.transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step M ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

def cfgOfFast {N : ℕ} [NeZero N] (q : Fin N) (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) : Cfg N 2 :=
  ⟨q, Tape.mk' (ListBlank.append L default) ((ListBlank.append R default).cons h)⟩

def stepFast {N : ℕ} [NeZero N] (M : Machine N 2) (q : Fin N) (L : List (Fin 2))
    (h : Fin 2) (R : List (Fin 2)) :
    Option (Fin N × List (Fin 2) × Fin 2 × List (Fin 2)) :=
  match M.transition q h with
  | none => none
  | some (w, .right, q') =>
    match R with
    | [] => some (q', w :: L, 0, [])
    | r :: rs => some (q', w :: L, r, rs)
  | some (w, .left, q') =>
    match L with
    | [] => some (q', [], 0, w :: R)
    | l :: ls => some (q', ls, l, w :: R)

def runFast {N : ℕ} [NeZero N] (M : Machine N 2) :
    ℕ → Fin N → List (Fin 2) → Fin 2 → List (Fin 2) →
    Option (Fin N × List (Fin 2) × Fin 2 × List (Fin 2))
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match stepFast M q L h R with
    | none => none
    | some (q', L', h', R') => runFast M n q' L' h' R'

theorem step_cfgOfFast {N : ℕ} [NeZero N] (M : Machine N 2) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) :
    step M (cfgOfFast q L h R) =
      (stepFast M q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  dsimp only [stepFast, cfgOfFast]
  rcases htr : M.transition q h with _ | ⟨w, d, q'⟩
  · exact step_mk'_none htr _ _
  · cases d with
    | right =>
      cases R with
      | nil =>
        have hs := step_mk'_right htr (ListBlank.append L default) default
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some]
        simp only [ListBlank.append, default_cons_zero]
      | cons r rs =>
        exact step_mk'_right htr (ListBlank.append L default)
          ((ListBlank.append rs default).cons r)
    | left =>
      cases L with
      | nil =>
        have hs := step_mk'_left htr default (ListBlank.append R default)
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some, default_cons_zero.symm, mkL_cons_eq_mk'_cons]
        simp only [ListBlank.append, default_cons_zero]
      | cons l ls =>
        have hs := step_mk'_left htr ((ListBlank.append ls default).cons l)
          (ListBlank.append R default)
        dsimp only [ListBlank.append] at hs ⊢
        rw [hs, Option.map_some, mkL_cons_eq_mk'_cons]
        rfl

theorem nSteps_of_runFast {N : ℕ} [NeZero N] (M : Machine N 2) (n : ℕ) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    nSteps M n (cfgOfFast q L h R) =
      (runFast M n q L h R).map fun x => cfgOfFast x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  induction n generalizing q L h R with
  | zero => rfl
  | succ n ih =>
    rw [nSteps_succ, step_cfgOfFast, runFast]
    rcases stepFast M q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem runFast_add {N : ℕ} [NeZero N] (M : Machine N 2) (m n : ℕ) (q : Fin N)
    (L : List (Fin 2)) (h : Fin 2)
    (R : List (Fin 2)) :
    runFast M (m + n) q L h R =
      match runFast M m q L h R with
      | none => none
      | some (q', L', h', R') => runFast M n q' L' h' R' := by
  induction m generalizing q L h R with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih =>
    rw [Nat.succ_add, runFast, runFast]
    rcases stepFast M q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

theorem init_eq_cfgOfFast {N : ℕ} [NeZero N] : (init : Cfg N 2) = cfgOfFast 0 [] 0 [] := by
  simp only [init, Tape.mk₁, Tape.mk₂, cfgOfFast, ListBlank.append, default_cons_zero]
  rfl

abbrev stateOfBootRef : BootState → Fin 393 := stateOfBoot

def stateOfBootCand : BootState → Fin 380
  | .b0 => 0 | .b1 => 1 | .b2 => 2 | .b3 => 3 | .b4 => 4 | .b68 => 65


theorem stepFast_of_stepBootRef {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hs : stepBoot q L h R = some (q', L', h', R')) :
    stepFast refM (stateOfBootRef q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootRef q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  cases q <;> cases h <;> simp only [stepBoot] at hs
  all_goals try cases hs
  all_goals
    cases L <;> cases R <;>
    simp only [stepBootR, stepBootL, Option.some.injEq, Prod.mk.injEq] at hs <;>
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ <;>
    rfl

theorem runFast_of_runBootRef (n : ℕ) {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hr : runBoot n q L h R = some (q', L', h', R')) :
    runFast refM n (stateOfBootRef q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootRef q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  induction n generalizing q L h R with
  | zero =>
    simp only [runBoot, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [runBoot] at hr
    rcases hst : stepBoot q L h R with _ | ⟨q1, L1, h1, R1⟩
    · rw [hst] at hr; cases hr
    · rw [hst] at hr
      rw [runFast, stepFast_of_stepBootRef hst]
      exact ih hr

theorem stepFast_of_stepBootCand {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hs : stepBoot q L h R = some (q', L', h', R')) :
    stepFast candM (stateOfBootCand q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootCand q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  cases q <;> cases h <;> simp only [stepBoot] at hs
  all_goals try cases hs
  all_goals
    cases L <;> cases R <;>
    simp only [stepBootR, stepBootL, Option.some.injEq, Prod.mk.injEq] at hs <;>
    rcases hs with ⟨rfl, rfl, rfl, rfl⟩ <;>
    rfl

theorem runFast_of_runBootCand (n : ℕ) {q q' : BootState} {L L' : List Bool} {h h' : Bool}
    {R R' : List Bool} (hr : runBoot n q L h R = some (q', L', h', R')) :
    runFast candM n (stateOfBootCand q) (L.map bitOfBool) (bitOfBool h) (R.map bitOfBool) =
      some (stateOfBootCand q', L'.map bitOfBool, bitOfBool h', R'.map bitOfBool) := by
  induction n generalizing q L h R with
  | zero =>
    simp only [runBoot, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl, rfl⟩
    rfl
  | succ n ih =>
    simp only [runBoot] at hr
    rcases hst : stepBoot q L h R with _ | ⟨q1, L1, h1, R1⟩
    · rw [hst] at hr; cases hr
    · rw [hst] at hr
      rw [runFast, stepFast_of_stepBootCand hst]
      exact ih hr

def bootR_39753 : List (Fin 2) :=
  (1 :: List.replicate 18 0) ++ bootChkR_7.map bitOfBool

theorem boot_fast_19_ref :
    runFast refM 19 68 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (64, [], 0, bootR_39753) := by
  rfl

theorem boot_fast_19_cand :
    runFast candM 19 65 (bootChkL_7.map bitOfBool) 0 (bootChkR_7.map bitOfBool) =
      some (64, [], 0, bootR_39753) := by
  rfl

attribute [irreducible] runFast

theorem boot_ref :
    nSteps refM 39753 init = some (cfgOfFast 64 [] 0 bootR_39753) := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast]
  have hadd : (39753 : ℕ) = 39734 + 19 := rfl
  have h0 : (0 : Fin 393) = stateOfBootRef .b0 := rfl
  have hL : ([] : List (Fin 2)) = [].map bitOfBool := rfl
  have hh : (0 : Fin 2) = bitOfBool false := rfl
  have h34 :=
    runFast_of_runBootRef 39734 (q := .b0) (L := []) (h := false) (R := []) boot_phase1_39734
  have h68 : stateOfBootRef .b68 = 68 := rfl
  have hhh : bitOfBool false = 0 := rfl
  rw [hadd, runFast_add, h0, hL, hh, h34]
  simp only [h68, hhh]
  rw [boot_fast_19_ref, Option.map_some, List.map_nil]

theorem boot_cand :
    nSteps candM 39753 init = some (cfgOfFast 64 [] 0 bootR_39753) := by
  rw [init_eq_cfgOfFast, nSteps_of_runFast]
  have hadd : (39753 : ℕ) = 39734 + 19 := rfl
  have h0 : (0 : Fin 380) = stateOfBootCand .b0 := rfl
  have hL : ([] : List (Fin 2)) = [].map bitOfBool := rfl
  have hh : (0 : Fin 2) = bitOfBool false := rfl
  have h34 :=
    runFast_of_runBootCand 39734 (q := .b0) (L := []) (h := false) (R := []) boot_phase1_39734
  have h65 : stateOfBootCand .b68 = 65 := rfl
  have hhh : bitOfBool false = 0 := rfl
  rw [hadd, runFast_add, h0, hL, hh, h34]
  simp only [h65, hhh]
  rw [boot_fast_19_cand, Option.map_some, List.map_nil]

def renum (q : Nat) : Fin 380 :=
  let s :=
    (if q > 65 then 1 else 0) +
    (if q > 68 then 1 else 0) +
    (if q > 266 then 1 else 0) +
    (if q > 278 then 1 else 0) +
    (if q > 322 then 1 else 0) +
    (if q > 335 then 1 else 0) +
    (if q > 341 then 1 else 0) +
    (if q > 353 then 1 else 0) +
    (if q > 359 then 1 else 0) +
    (if q > 361 then 1 else 0) +
    (if q > 379 then 1 else 0) +
    (if q > 387 then 1 else 0) +
    (if q > 389 then 1 else 0)
  if h : q - s < 380 then ⟨q - s, h⟩ else ⟨0, by decide⟩

def mapState (q : Nat) (l0 h : Fin 2) : Fin 380 :=
  if q = 67 then renum 292
  else if q = 66 then renum (if h.val = 0 then 350 else 338)
  else if q = 65 then renum (if h.val = 0 then 45 else 342)
  else if q = 21 ∧ h.val = 1 then renum 17
  else if q = 266 then renum 272
  else if q = 278 then renum (if l0.val = 0 then 252 else 270)
  else if q = 322 then renum 280
  else if q = 341 then renum 46
  else if q = 347 then renum 80
  else if q = 353 then renum 82
  else if q = 359 then renum 356
  else if q = 379 then renum 376
  else if q = 334 then renum 385
  else if q = 335 then renum 337
  else if q = 370 then renum 371
  else if q = 389 then renum 388
  else if q = 361 then renum 76
  else if q = 387 then renum 345
  else renum q

def isL0Eq1State (q : Nat) : Bool :=
  q == 87 || q == 291 || q == 295 || q == 310 || q == 316 ||
  q == 333 || q == 334 || q == 335 || q == 336 || q == 338 ||
  q == 340 || q == 344 || q == 349 || q == 361 || q == 363 ||
  q == 365 || q == 367 || q == 369 || q == 374 || q == 378 ||
  q == 384 || q == 387 || q == 266 || q == 280 || q == 359 || q == 379 ||
  q == 371 || q == 389 ||
  q == 140 || q == 218 || q == 220 || q == 240 || q == 252 ||
  q == 80 || q == 81 || q == 82 ||
  q == 98 || q == 105 || q == 155 || q == 195

def isL0Eq0State (q : Nat) : Bool :=
  q == 45 || q == 350 || q == 272 || q == 322 || q == 337 || q == 346 ||
  q == 376 || q == 385 || q == 370 || q == 388 || q == 339 || q == 341 ||
  q == 76 || q == 345 || q == 351 || q == 360 ||
  q == 265 || q == 270 ||
  q == 79 || q == 347 || q == 353 ||
  q == 356 || q == 362 || q == 354 || q == 355

def validState (q : Nat) (l2 l1 l0 h r0 : Fin 2) : Bool :=
  q >= 5 && q != 68 &&
  (q != 22 || r0 == 1) &&
  (q != 20 || !(h == 0 && l0 == 1)) &&
  (!isL0Eq1State q || l0 == 1) &&
  (!isL0Eq0State q || l0 == 0) &&
  (q != 46 || (l0 == 1 && l1 == 0)) &&
  (q != 361 || (l0 == 1 && l1 == 0 && l2 == 1)) &&
  (q != 80 || (l0 == 1 && l1 == 0)) &&
  (q != 82 || (l0 == 1 && l1 == 1)) &&
  (!(q == 345 || q == 360 || q == 362) || (l0 == 0 && l1 == 1)) &&
  (!(q == 354 || q == 355) || (l0 == 0 && l1 == 1 && l2 == 1)) &&
  (q != 278 || l1 == 1) &&
  (!(q == 156 || q == 157 || q == 196 || q == 197 ||
    q == 292 || q == 296 || q == 311 || q == 317) || (l0 == 1 && l1 == 1)) &&
  (!(q == 312 || q == 318) || (l0 == 1 && l1 == 1 && l2 == 1)) &&
  (q != 88 || (l0 == 0 && l1 == 1)) &&
  (q != 309 || (l0 == 0 && l1 == 1 && l2 == 1)) &&
  (q != 67 || (h == 1 && l0 == 1 && l1 == 1)) &&
  (q != 66 || ((h == 0 && l0 == 1 && l1 == 1) || (h == 1 && l0 == 1))) &&
  (q != 65 || ((h == 0 && l0 == 1) || h == 1))

def checkNext (q : Nat) (l2 l1 l0 h r0 x : Fin 2) : Bool :=
  match Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h with
  | none => true
  | some (w, Dir.right, q') => validState q'.val l1 l0 w r0 x
  | some (w, Dir.left, q') => validState q'.val x l2 l1 l0 w

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem validState_next (q : Fin 393) (l2 l1 l0 h r0 x : Fin 2) :
    validState q.val l2 l1 l0 h r0 = true → checkNext q.val l2 l1 l0 h r0 x = true := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => all2 (fun l1 => all2 (fun
    l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) || all2 (fun x => checkNext q l2 l1 l0
    h r0 x))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq x
  exact hq

def expectedTransition (q : Nat) (l1 l0 h r0 : Fin 2) : Option (Fin 2 × Dir × Fin 380) :=
  match Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h with
  | none => none
  | some (w, Dir.right, q') => some (w, Dir.right, mapState q'.val w r0)
  | some (w, Dir.left, q') => some (w, Dir.left, mapState q'.val l1 l0)

def isThreeStep (q : Nat) (l0 h : Fin 2) : Bool :=
  ((q == 45 || q == 350 || q == 272 || q == 266 || q == 346 ||
    q == 356 || q == 359 || q == 280 || q == 322 || q == 388 ||
    q == 389 || q == 341 || q == 265 || q == 270 || q == 80 ||
    q == 82 || q == 353 || (q == 278 && l0.val == 1)) && h.val == 0) ||
  ((q == 376 || q == 385 || q == 334 || q == 337 || q == 335 ||
    q == 280 || q == 322 || q == 370 || q == 371 || q == 388 ||
    q == 389 || q == 344 || q == 346 || q == 76 || q == 365 ||
    q == 387 || q == 252 || q == 347 || q == 353) && h.val == 1)

def isFiveStepLRLR (q : Nat) (h : Fin 2) : Bool :=
  (q == 379 && h.val == 1) || (q == 347 && h.val == 0)

def isFiveStepLLRR (q : Nat) (l0 h : Fin 2) : Bool :=
  ((q == 46 || q == 362) && h.val == 0) ||
  ((q == 345 || q == 80 || q == 82 || (q == 278 && l0.val == 0)) && h.val == 1)

def isSevenStepLLLRRR (q : Nat) (h : Fin 2) : Bool :=
  (q == 361 && h.val == 1) || (q == 354 && h.val == 0)

def isNineStepLRLLLRRR (q : Nat) (h : Fin 2) : Bool :=
  q == 355 && h.val == 0

def isMultiStep (q : Nat) (l0 h : Fin 2) : Bool :=
  isThreeStep q l0 h || isFiveStepLRLR q h || isFiveStepLLRR q l0 h ||
  isSevenStepLLLRRR q h || isNineStepLRLLLRRR q h

def midP (q : Nat) (h : Fin 2) : Fin 380 :=
  if q == 45 then renum 342
  else if q == 350 then renum 338
  else if q == 272 || q == 266 then renum 246
  else if q == 346 then renum (if h.val == 0 then 154 else 100)
  else if q == 356 || q == 359 then renum 303
  else if q == 280 || q == 322 then renum (if h.val == 0 then 209 else 264)
  else if q == 376 then renum 84
  else if q == 341 then renum 344
  else if q == 365 then renum 355
  else if q == 76 then renum 365
  else if q == 387 then renum 354
  else if q == 265 then renum 117
  else if q == 270 || q == 278 then renum 152
  else if q == 252 then renum 265
  else if q == 80 && h.val == 0 then renum 101
  else if (q == 82 || q == 353) && h.val == 0 then renum 102
  else if (q == 347 || q == 353) && h.val == 1 then renum 347
  else if (q == 388 || q == 389) && h.val == 0 then renum 290
  else if (q == 370 || q == 371 || q == 388 || q == 389) && h.val == 1 then
    renum 370
  else renum 334

def midS (q : Nat) (l0 h : Fin 2) : Fin 380 :=
  if q == 45 then renum 29
  else if q == 350 then renum 339
  else if q == 272 || q == 266 then
    if l0.val == 0 then renum 268 else renum 279
  else if q == 346 then
    if h.val == 0 then renum 351 else renum 342
  else if q == 356 || q == 359 then
    if l0.val == 0 then renum 357 else renum 368
  else if q == 280 || q == 322 then
    if h.val == 0 then
      if l0.val == 0 then renum 249 else renum 210
    else
      if l0.val == 0 then renum 321 else renum 287
  else if q == 376 then renum 382
  else if q == 341 then renum 345
  else if q == 365 then renum 340
  else if q == 76 then renum 34
  else if q == 387 then renum 338
  else if q == 265 then renum 257
  else if q == 270 || q == 278 then
    if l0.val == 0 then renum 271 else renum 153
  else if q == 252 then renum 272
  else if q == 80 && h.val == 0 then renum 102
  else if (q == 82 || q == 353) && h.val == 0 then
    if l0.val == 0 then renum 352 else renum 103
  else if (q == 347 || q == 353) && h.val == 1 then renum 357
  else if (q == 388 || q == 389) && h.val == 0 then
    if l0.val == 0 then renum 383 else renum 291
  else if (q == 370 || q == 371 || q == 388 || q == 389) && h.val == 1 then
    if l0.val == 0 then renum 334 else renum 21
  else
    if l0.val == 0 then renum 44 else renum 333

def validState1 (q : Nat) (l1 l0 h r0 : Fin 2) : Bool :=
  validState q 0 l1 l0 h r0 || validState q 1 l1 l0 h r0

theorem validState1_of_validState (q : Nat) (l2 l1 l0 h r0 : Fin 2) :
    validState q l2 l1 l0 h r0 = true → validState1 q l1 l0 h r0 = true := by
  intro hv
  rcases l2 with ⟨_ | _ | n, isLt⟩
  · rw [show (⟨0, isLt⟩ : Fin 2) = 0 from rfl] at hv
    simp [validState1, hv]
  · rw [show (⟨1, isLt⟩ : Fin 2) = 1 from rfl] at hv
    simp [validState1, hv]
  · omega

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_oneStep (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isMultiStep q.val l0 h = false →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => (isMultiStep q l0 h) ||
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (mapState q l0
    h).val h == expectedTransition q l1 l0 h r0)))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = some (h, Dir.left, midP q.val h) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isThreeStep q l0 h) ||
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (mapState q l0
    h).val h == some (h, Dir.left, midP q h))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (midP q.val h).val l0 = some (l0, Dir.right, midS q.val l0 h) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isThreeStep q l0 h) ||
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (midP q h).val
    l0 == some (l0, Dir.right, midS q l0 h))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_threeStep_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isThreeStep q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (midS q.val l0 h).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isThreeStep q l0 h) ||
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (midS q l0
    h).val h == expectedTransition q l1 l0 h r0)))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem threeStep_not_none (q : Fin 393) (l0 h : Fin 2) :
    isThreeStep q.val l0 h = true →
    Zf393.zf393Trans q h ≠ none := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isThreeStep q l0 h) ||
    (Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h != none)))) (by rfl) q
  simp only [Nat.mod_eq_of_lt q.isLt] at hq
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  intro heq; rw [heq] at hq; exact Bool.noConfusion hq

def lrlrP1 (q : Nat) : Fin 380 :=
  if q == 379 then renum 84 else renum 101

def lrlrS1 (q : Nat) : Fin 380 :=
  if q == 379 then renum 371 else renum 346

def lrlrP2 (q : Nat) : Fin 380 :=
  if q == 379 then renum 370 else renum 154

def lrlrS2 (q : Nat) : Fin 380 :=
  if q == 379 then renum 21 else renum 351

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q.val h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = some (h, Dir.left, lrlrP1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) || all2 (fun l0 =>
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (mapState q l0
    h).val h == some (h, Dir.left, lrlrP1 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q.val h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (lrlrP1 q.val).val l0 = some (l0, Dir.right, lrlrS1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) || all2 (fun l0 =>
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (lrlrP1 q).val
    l0 == some (l0, Dir.right, lrlrS1 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q.val h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (lrlrS1 q.val).val h = some (h, Dir.left, lrlrP2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) || all2 (fun l0 =>
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (lrlrS1 q).val h
    == some (h, Dir.left, lrlrP2 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_4 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q.val h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (lrlrP2 q.val).val l0 = some (l0, Dir.right, lrlrS2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) || all2 (fun l0 =>
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (lrlrP2 q).val
    l0 == some (l0, Dir.right, lrlrS2 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLRLR_5 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLRLR q.val h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (lrlrS2 q.val).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) || all2 (fun l0 =>
    all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (lrlrS2 q).val h
    == expectedTransition q l1 l0 h r0)))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem fiveStepLRLR_not_none (q : Fin 393) (h : Fin 2) :
    isFiveStepLRLR q.val h = true →
    Zf393.zf393Trans q h ≠ none := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isFiveStepLRLR q h) ||
    (Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h != none))) (by rfl) q
  simp only [Nat.mod_eq_of_lt q.isLt] at hq
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  intro heq; rw [heq] at hq; exact Bool.noConfusion hq

def llrrP1 (q : Nat) : Fin 380 :=
  if q == 46 then renum 344
  else if q == 362 then renum 346
  else if q == 345 then renum 354
  else if q == 278 then renum 265
  else renum 347

def llrrP2 (q : Nat) : Fin 380 :=
  if q == 46 then renum 334
  else if q == 362 then renum 154
  else if q == 278 then renum 117
  else if q == 345 then renum 362
  else renum 273

def llrrS1 (q : Nat) : Fin 380 :=
  if q == 46 then renum 44
  else if q == 362 then renum 155
  else if q == 345 then renum 363
  else if q == 278 then renum 118
  else if q == 80 then renum 300
  else renum 302

def llrrS2 (q : Nat) : Fin 380 :=
  if q == 46 then renum 42
  else if q == 362 then renum 364
  else if q == 345 then renum 32
  else if q == 278 then renum 270
  else if q == 80 then renum 301
  else renum 303

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_1 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = some (h, Dir.left, llrrP1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (mapState q
    l0 h).val h == some (h, Dir.left, llrrP1 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_2 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (llrrP1 q.val).val l0 = some (l0, Dir.left, llrrP2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (llrrP1
    q).val l0 == some (l0, Dir.left, llrrP2 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_3 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (llrrP2 q.val).val l1 = some (l1, Dir.right, llrrS1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (llrrP2
    q).val l1 == some (l1, Dir.right, llrrS1 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_4 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (llrrS1 q.val).val l0 = some (l0, Dir.right, llrrS2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (llrrS1
    q).val l0 == some (l0, Dir.right, llrrS2 q))))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_fiveStepLLRR_5 (q : Fin 393) (l1 l0 h r0 : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    validState1 q.val l1 l0 h r0 = true →
    zf380Trans (llrrS2 q.val).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || all2 (fun l1 => all2 (fun r0 => !(validState1 q l1 l0 h r0) || (zf380Trans (llrrS2
    q).val h == expectedTransition q l1 l0 h r0)))))) (by rfl) q
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem fiveStepLLRR_not_none (q : Fin 393) (l0 h : Fin 2) :
    isFiveStepLLRR q.val l0 h = true →
    Zf393.zf393Trans q h ≠ none := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => all2 (fun l0 => !(isFiveStepLLRR q l0 h)
    || (Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h != none)))) (by rfl) q
  simp only [Nat.mod_eq_of_lt q.isLt] at hq
  replace hq := of_all2 hq h
  replace hq := of_all2 hq l0
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  intro heq; rw [heq] at hq; exact Bool.noConfusion hq

def lllrrrP1 (q : Nat) : Fin 380 :=
  if q == 361 then renum 365 else renum 362

def lllrrrP2 (q : Nat) : Fin 380 :=
  if q == 361 then renum 355 else renum 346

def lllrrrP3 (q : Nat) : Fin 380 :=
  if q == 361 then renum 197 else renum 100

def lllrrrS1 (q : Nat) : Fin 380 :=
  if q == 361 then renum 198 else renum 101

def lllrrrS2 (q : Nat) : Fin 380 :=
  if q == 361 then renum 366 else renum 102

def lllrrrS3 (q : Nat) : Fin 380 :=
  if q == 361 then renum 367 else renum 352

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_1 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = some (h, Dir.left, lllrrrP1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (mapState q l0 h).val h == some (h, Dir.left, lllrrrP1 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_2 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrP1 q.val).val l0 = some (l0, Dir.left, lllrrrP2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrP1 q).val l0 == some (l0, Dir.left, lllrrrP2 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_3 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrP2 q.val).val l1 = some (l1, Dir.left, lllrrrP3 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrP2 q).val l1 == some (l1, Dir.left, lllrrrP3 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_4 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrP3 q.val).val l2 = some (l2, Dir.right, lllrrrS1 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrP3 q).val l2 == some (l2, Dir.right, lllrrrS1 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_5 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrS1 q.val).val l1 = some (l1, Dir.right, lllrrrS2 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrS1 q).val l1 == some (l1, Dir.right, lllrrrS2 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_6 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrS2 q.val).val l0 = some (l0, Dir.right, lllrrrS3 q.val) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrS2 q).val l0 == some (l0, Dir.right, lllrrrS3 q)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_sevenStepLLLRRR_7 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (lllrrrS3 q.val).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (lllrrrS3 q).val h == expectedTransition q l1 l0 h r0))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem sevenStepLLLRRR_not_none (q : Fin 393) (h : Fin 2) :
    isSevenStepLLLRRR q.val h = true →
    Zf393.zf393Trans q h ≠ none := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isSevenStepLLLRRR q h) ||
    (Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h != none))) (by rfl) q
  simp only [Nat.mod_eq_of_lt q.isLt] at hq
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  intro heq; rw [heq] at hq; exact Bool.noConfusion hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_0a (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (mapState q.val l0 h).val h = some (h, Dir.left, renum 197) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (mapState q l0 h).val h == some (h, Dir.left, renum 197)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_0b (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 197).val l0 = some (l0, Dir.right, renum 354) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 197).val l0 == some (l0, Dir.right, renum 354)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_1 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 354).val h = some (h, Dir.left, renum 362) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 354).val h == some (h, Dir.left, renum 362)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_2 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 362).val l0 = some (l0, Dir.left, renum 346) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 362).val l0 == some (l0, Dir.left, renum 346)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_3 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 346).val l1 = some (l1, Dir.left, renum 100) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 346).val l1 == some (l1, Dir.left, renum 100)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_4 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 100).val l2 = some (l2, Dir.right, renum 101) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 100).val l2 == some (l2, Dir.right, renum 101)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_5 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 101).val l1 = some (l1, Dir.right, renum 102) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 101).val l1 == some (l1, Dir.right, renum 102)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_6 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 102).val l0 = some (l0, Dir.right, renum 352) := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 102).val l0 == some (l0, Dir.right, renum 352)))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem transition_nineStep_7 (q : Fin 393) (l2 l1 l0 h r0 : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    validState q.val l2 l1 l0 h r0 = true →
    zf380Trans (renum 352).val h = expectedTransition q.val l1 l0 h r0 := by
  intro h0 h1
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) || all2 (fun l0
    => all2 (fun l1 => all2 (fun l2 => all2 (fun r0 => !(validState q l2 l1 l0 h r0) ||
    (zf380Trans (renum 352).val h == expectedTransition q l1 l0 h r0))))))) (by rfl) q
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  replace hq := of_all2 hq l0
  replace hq := of_all2 hq l1
  replace hq := of_all2 hq l2
  replace hq := of_all2 hq r0
  simp only [h1, Bool.not_true, Bool.false_or] at hq
  exact LawfulBEq.eq_of_beq hq

set_option maxHeartbeats 0 in
-- Finite state-table decision procedure.
theorem nineStepLRLLLRRR_not_none (q : Fin 393) (h : Fin 2) :
    isNineStepLRLLLRRR q.val h = true →
    Zf393.zf393Trans q h ≠ none := by
  intro h0
  have hq := of_fin_nat (p := fun q => all2 (fun h => !(isNineStepLRLLLRRR q h) ||
    (Zf393.zf393Trans ⟨q % 393, Nat.mod_lt q (by decide)⟩ h != none))) (by rfl) q
  simp only [Nat.mod_eq_of_lt q.isLt] at hq
  replace hq := of_all2 hq h
  simp only [h0, Bool.not_true, Bool.false_or] at hq
  intro heq; rw [heq] at hq; exact Bool.noConfusion hq

theorem step_of_transition_eq {q : Fin 393} {S : Fin 380} (T : Tape (Fin 2))
    (htr : zf380Trans S.val T.head =
      expectedTransition q.val T.left.tail.head T.left.head T.head T.right.head) :
    step candM ⟨S, T⟩ =
      (step refM ⟨q, T⟩).map fun c =>
        ⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩ := by
  dsimp only [step]
  rw [candM_transition_eq_nat S T.head, htr, Zf393.zf393Trans_eq q T.head]
  rcases e : Zf393.zf393Trans q T.head with _ | ⟨w, d, q'⟩
  · simp [expectedTransition, Nat.mod_eq_of_lt q.isLt, e]
  · cases T; cases d <;> simp [expectedTransition, Nat.mod_eq_of_lt q.isLt, e, Tape.move,
    Tape.write]

theorem tape_left_right_self (T : Tape (Fin 2)) :
    (((T.write T.head).move Dir.left).write T.left.head).move Dir.right = T := by
  cases T
  simp [Tape.write, Tape.move]

theorem step_three_left_right
    {q₁ P S : Fin 380} (T : Tape (Fin 2))
    (h1 : zf380Trans q₁.val T.head = some (T.head, Dir.left, P))
    (h2 : zf380Trans P.val T.left.head = some (T.left.head, Dir.right, S))
    {c' : Cfg 380 2}
    (h3 : step candM ⟨S, T⟩ = some c') :
    Reaches₁ (step candM) ⟨q₁, T⟩ c' := by
  have hs1 : step candM ⟨q₁, T⟩ = some ⟨P, (T.write T.head).move Dir.left⟩ := by
    simp [step, candM_transition_eq_nat, h1]
  have hhead : ((T.write T.head).move Dir.left).head = T.left.head := by
    cases T; rfl
  have hs2 : step candM ⟨P, (T.write T.head).move Dir.left⟩ = some ⟨S, T⟩ := by
    dsimp only [step]
    rw [hhead, candM_transition_eq_nat, h2]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  exact Relation.TransGen.tail (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2) h3

theorem step_five_left_right
    {q₁ P₁ S₁ P₂ S₂ : Fin 380} (T : Tape (Fin 2))
    (h1 : zf380Trans q₁.val T.head = some (T.head, Dir.left, P₁))
    (h2 : zf380Trans P₁.val T.left.head = some (T.left.head, Dir.right, S₁))
    (h3 : zf380Trans S₁.val T.head = some (T.head, Dir.left, P₂))
    (h4 : zf380Trans P₂.val T.left.head = some (T.left.head, Dir.right, S₂))
    {c' : Cfg 380 2}
    (h5 : step candM ⟨S₂, T⟩ = some c') :
    Reaches₁ (step candM) ⟨q₁, T⟩ c' := by
  have hs1 : step candM ⟨q₁, T⟩ = some ⟨P₁, (T.write T.head).move Dir.left⟩ := by
    simp [step, candM_transition_eq_nat, h1]
  have hhead : ((T.write T.head).move Dir.left).head = T.left.head := by
    cases T; rfl
  have hs2 : step candM ⟨P₁, (T.write T.head).move Dir.left⟩ = some ⟨S₁, T⟩ := by
    dsimp only [step]
    rw [hhead, candM_transition_eq_nat, h2]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  have hs3 : step candM ⟨S₁, T⟩ = some ⟨P₂, (T.write T.head).move Dir.left⟩ := by
    simp [step, candM_transition_eq_nat, h3]
  have hs4 : step candM ⟨P₂, (T.write T.head).move Dir.left⟩ = some ⟨S₂, T⟩ := by
    dsimp only [step]
    rw [hhead, candM_transition_eq_nat, h4]
    dsimp only [Option.map]
    rw [tape_left_right_self]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
        hs3)
      hs4)
    h5

theorem step_five_left_left_right_right
    {q₁ P₁ P₂ S₁ S₂ : Fin 380} (T : Tape (Fin 2))
    (h1 : zf380Trans q₁.val T.head = some (T.head, Dir.left, P₁))
    (h2 : zf380Trans P₁.val T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : zf380Trans P₂.val T.left.tail.head = some (T.left.tail.head, Dir.right, S₁))
    (h4 : zf380Trans S₁.val T.left.head = some (T.left.head, Dir.right, S₂))
    {c' : Cfg 380 2}
    (h5 : step candM ⟨S₂, T⟩ = some c') :
    Reaches₁ (step candM) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  have hs1 : step candM ⟨q₁, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, candM_transition_eq_nat, h1]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs2 : step candM ⟨P₁, T₁⟩ = some ⟨P₂, (T₁.write T₁.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead1, candM_transition_eq_nat, h2]
    rfl
  have hhead2 : ((T₁.write T₁.head).move Dir.left).head = T.left.tail.head := by
    cases T; rfl
  have hs3 : step candM ⟨P₂, (T₁.write T₁.head).move Dir.left⟩ = some ⟨S₁, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, candM_transition_eq_nat, h3]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs4 : step candM ⟨S₁, T₁⟩ = some ⟨S₂, T⟩ := by
    dsimp only [step]
    rw [hhead1, candM_transition_eq_nat, h4]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
        hs3)
      hs4)
    h5

theorem step_seven_left_left_left_right_right_right
    {q₁ P₁ P₂ P₃ S₁ S₂ S₃ : Fin 380} (T : Tape (Fin 2))
    (h1 : zf380Trans q₁.val T.head = some (T.head, Dir.left, P₁))
    (h2 : zf380Trans P₁.val T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : zf380Trans P₂.val T.left.tail.head = some (T.left.tail.head, Dir.left, P₃))
    (h4 : zf380Trans P₃.val T.left.tail.tail.head = some (T.left.tail.tail.head, Dir.right, S₁))
    (h5 : zf380Trans S₁.val T.left.tail.head = some (T.left.tail.head, Dir.right, S₂))
    (h6 : zf380Trans S₂.val T.left.head = some (T.left.head, Dir.right, S₃))
    {c' : Cfg 380 2}
    (h7 : step candM ⟨S₃, T⟩ = some c') :
    Reaches₁ (step candM) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  let T₂ := (T₁.write T₁.head).move Dir.left
  have hs1 : step candM ⟨q₁, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, candM_transition_eq_nat, h1]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs2 : step candM ⟨P₁, T₁⟩ = some ⟨P₂, T₂⟩ := by
    dsimp only [T₂, step]
    rw [hhead1, candM_transition_eq_nat, h2]
    rfl
  have hhead2 : T₂.head = T.left.tail.head := by
    cases T; rfl
  have hleft2 : T₂.left.head = T.left.tail.tail.head := by
    cases T; rfl
  have hs3 : step candM ⟨P₂, T₂⟩ = some ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead2, candM_transition_eq_nat, h3]
    rfl
  have hhead3 : ((T₂.write T₂.head).move Dir.left).head = T.left.tail.tail.head := by
    cases T; rfl
  have hs4 : step candM ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ = some ⟨S₁, T₂⟩ := by
    dsimp only [step]
    rw [hhead3, candM_transition_eq_nat, h4]
    dsimp only [Option.map]
    rw [← hleft2, tape_left_right_self T₂]
  have hs5 : step candM ⟨S₁, T₂⟩ = some ⟨S₂, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, candM_transition_eq_nat, h5]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs6 : step candM ⟨S₂, T₁⟩ = some ⟨S₃, T⟩ := by
    dsimp only [step]
    rw [hhead1, candM_transition_eq_nat, h6]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.tail
            (Relation.TransGen.tail (Relation.TransGen.single hs1) hs2)
            hs3)
          hs4)
        hs5)
      hs6)
    h7

theorem step_nine_left_right_left_left_left_right_right_right
    {q₁ P₀ q₂ P₁ P₂ P₃ S₁ S₂ S₃ : Fin 380} (T : Tape (Fin 2))
    (h0a : zf380Trans q₁.val T.head = some (T.head, Dir.left, P₀))
    (h0b : zf380Trans P₀.val T.left.head = some (T.left.head, Dir.right, q₂))
    (h1 : zf380Trans q₂.val T.head = some (T.head, Dir.left, P₁))
    (h2 : zf380Trans P₁.val T.left.head = some (T.left.head, Dir.left, P₂))
    (h3 : zf380Trans P₂.val T.left.tail.head = some (T.left.tail.head, Dir.left, P₃))
    (h4 : zf380Trans P₃.val T.left.tail.tail.head = some (T.left.tail.tail.head, Dir.right, S₁))
    (h5 : zf380Trans S₁.val T.left.tail.head = some (T.left.tail.head, Dir.right, S₂))
    (h6 : zf380Trans S₂.val T.left.head = some (T.left.head, Dir.right, S₃))
    {c' : Cfg 380 2}
    (h7 : step candM ⟨S₃, T⟩ = some c') :
    Reaches₁ (step candM) ⟨q₁, T⟩ c' := by
  let T₁ := (T.write T.head).move Dir.left
  let T₂ := (T₁.write T₁.head).move Dir.left
  have hs0a : step candM ⟨q₁, T⟩ = some ⟨P₀, T₁⟩ := by
    simp [T₁, step, candM_transition_eq_nat, h0a]
  have hhead1 : T₁.head = T.left.head := by
    cases T; rfl
  have hleft1 : T₁.left.head = T.left.tail.head := by
    cases T; rfl
  have hs0b : step candM ⟨P₀, T₁⟩ = some ⟨q₂, T⟩ := by
    dsimp only [step]
    rw [hhead1, candM_transition_eq_nat, h0b]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  have hs1 : step candM ⟨q₂, T⟩ = some ⟨P₁, T₁⟩ := by
    simp [T₁, step, candM_transition_eq_nat, h1]
  have hs2 : step candM ⟨P₁, T₁⟩ = some ⟨P₂, T₂⟩ := by
    dsimp only [T₂, step]
    rw [hhead1, candM_transition_eq_nat, h2]
    rfl
  have hhead2 : T₂.head = T.left.tail.head := by
    cases T; rfl
  have hleft2 : T₂.left.head = T.left.tail.tail.head := by
    cases T; rfl
  have hs3 : step candM ⟨P₂, T₂⟩ = some ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ := by
    dsimp only [step]
    rw [hhead2, candM_transition_eq_nat, h3]
    rfl
  have hhead3 : ((T₂.write T₂.head).move Dir.left).head = T.left.tail.tail.head := by
    cases T; rfl
  have hs4 : step candM ⟨P₃, (T₂.write T₂.head).move Dir.left⟩ = some ⟨S₁, T₂⟩ := by
    dsimp only [step]
    rw [hhead3, candM_transition_eq_nat, h4]
    dsimp only [Option.map]
    rw [← hleft2, tape_left_right_self T₂]
  have hs5 : step candM ⟨S₁, T₂⟩ = some ⟨S₂, T₁⟩ := by
    dsimp only [step]
    rw [hhead2, candM_transition_eq_nat, h5]
    dsimp only [Option.map]
    rw [← hleft1, tape_left_right_self T₁]
  have hs6 : step candM ⟨S₂, T₁⟩ = some ⟨S₃, T⟩ := by
    dsimp only [step]
    rw [hhead1, candM_transition_eq_nat, h6]
    dsimp only [Option.map]
    rw [tape_left_right_self T]
  exact Relation.TransGen.tail
    (Relation.TransGen.tail
      (Relation.TransGen.tail
        (Relation.TransGen.tail
          (Relation.TransGen.tail
            (Relation.TransGen.tail
              (Relation.TransGen.tail
                (Relation.TransGen.tail (Relation.TransGen.single hs0a) hs0b)
                hs1)
              hs2)
            hs3)
          hs4)
        hs5)
      hs6)
    h7

theorem step_preserves_valid (q : Fin 393) (T : Tape (Fin 2))
    (hv : validState q.val T.left.tail.tail.head T.left.tail.head T.left.head T.head T.right.head =
      true) :
    match step refM ⟨q, T⟩ with
    | none => True
    | some c =>
      validState c.state.val c.tape.left.tail.tail.head c.tape.left.tail.head
        c.tape.left.head c.tape.head c.tape.right.head = true := by
  have hnext :=
    validState_next q T.left.tail.tail.head T.left.tail.head T.left.head T.head T.right.head
  dsimp only [step]
  rw [Zf393.zf393Trans_eq q T.head]
  rcases e : Zf393.zf393Trans q T.head with _ | ⟨w, d, q'⟩
  · trivial
  · cases d
    · simpa [checkNext, Nat.mod_eq_of_lt q.isLt, e, Tape.move, Tape.write] using
        hnext T.left.tail.tail.tail.head hv
    · simpa [checkNext, Nat.mod_eq_of_lt q.isLt, e, Tape.move, Tape.write] using
        hnext T.right.tail.head hv

def Rel (c₁ : Cfg 393 2) (c₂ : Cfg 380 2) : Prop :=
  validState c₁.state.val c₁.tape.left.tail.tail.head c₁.tape.left.tail.head c₁.tape.left.head
    c₁.tape.head c₁.tape.right.head = true ∧
  c₂ = ⟨mapState c₁.state.val c₁.tape.left.head c₁.tape.head, c₁.tape⟩

theorem respects : Respects (step refM) (step candM) Rel := by
  intro c₁ c₂ ⟨hv, h⟩
  subst h
  obtain ⟨q, T⟩ := c₁
  have hpres := step_preserves_valid q T hv
  have hv1 :=
    validState1_of_validState q.val T.left.tail.tail.head T.left.tail.head T.left.head T.head
      T.right.head hv
  cases h3 : isThreeStep q.val T.left.head T.head
  · cases h5a : isFiveStepLRLR q.val T.head
    · cases h5b : isFiveStepLLRR q.val T.left.head T.head
      · cases h7 : isSevenStepLLLRRR q.val T.head
        · cases h9 : isNineStepLRLLLRRR q.val T.head
          · have hm : isMultiStep q.val T.left.head T.head = false := by
              simp [isMultiStep, h3, h5a, h5b, h7, h9]
            have hstep := step_of_transition_eq T
              (transition_oneStep q T.left.tail.head T.left.head T.head T.right.head hm hv1)
            rcases e : step refM ⟨q, T⟩ with _ | c
            · simpa [hstep] using e
            · rw [e] at hpres
              exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
                ⟨hpres, rfl⟩,
                Relation.TransGen.single (by simp [hstep, e])⟩
          · have h0a := transition_nineStep_0a q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h0b := transition_nineStep_0b q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h1 := transition_nineStep_1 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h2 := transition_nineStep_2 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h3' := transition_nineStep_3 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h4 := transition_nineStep_4 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h5 := transition_nineStep_5 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have h6 := transition_nineStep_6 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h9 hv
            have hstep9 := step_of_transition_eq T
              (transition_nineStep_7 q T.left.tail.tail.head T.left.tail.head
                T.left.head T.head T.right.head h9 hv)
            rcases e : step refM ⟨q, T⟩ with _ | c
            · exfalso
              apply nineStepLRLLLRRR_not_none q T.head h9
              rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
              · rw [← Zf393.zf393Trans_eq]; exact htr
              · simp only [step, htr, Option.map_some, reduceCtorEq] at e
            · rw [e] at hpres hstep9
              exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
                ⟨hpres, rfl⟩,
                step_nine_left_right_left_left_left_right_right_right T h0a h0b h1 h2 h3'
                  h4 h5 h6 hstep9⟩
        · have h1 := transition_sevenStepLLLRRR_1 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h2 := transition_sevenStepLLLRRR_2 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h3' := transition_sevenStepLLLRRR_3 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h4 := transition_sevenStepLLLRRR_4 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h5 := transition_sevenStepLLLRRR_5 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have h6 := transition_sevenStepLLLRRR_6 q T.left.tail.tail.head T.left.tail.head
            T.left.head T.head T.right.head h7 hv
          have hstep7 := step_of_transition_eq T
            (transition_sevenStepLLLRRR_7 q T.left.tail.tail.head T.left.tail.head
              T.left.head T.head T.right.head h7 hv)
          rcases e : step refM ⟨q, T⟩ with _ | c
          · exfalso
            apply sevenStepLLLRRR_not_none q T.head h7
            rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
            · rw [← Zf393.zf393Trans_eq]; exact htr
            · simp only [step, htr, Option.map_some, reduceCtorEq] at e
          · rw [e] at hpres hstep7
            exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
              ⟨hpres, rfl⟩,
              step_seven_left_left_left_right_right_right T h1 h2 h3' h4 h5 h6 hstep7⟩
      · have h1 := transition_fiveStepLLRR_1 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h2 := transition_fiveStepLLRR_2 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h3' := transition_fiveStepLLRR_3 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have h4 := transition_fiveStepLLRR_4 q T.left.tail.head T.left.head T.head
          T.right.head h5b hv1
        have hstep5 := step_of_transition_eq T
          (transition_fiveStepLLRR_5 q T.left.tail.head T.left.head T.head T.right.head h5b hv1)
        rcases e : step refM ⟨q, T⟩ with _ | c
        · exfalso
          apply fiveStepLLRR_not_none q T.left.head T.head h5b
          rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
          · rw [← Zf393.zf393Trans_eq]; exact htr
          · simp only [step, htr, Option.map_some, reduceCtorEq] at e
        · rw [e] at hpres hstep5
          exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
            ⟨hpres, rfl⟩,
            step_five_left_left_right_right T h1 h2 h3' h4 hstep5⟩
    · have h1 := transition_fiveStepLRLR_1 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h2 := transition_fiveStepLRLR_2 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h3' := transition_fiveStepLRLR_3 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have h4 := transition_fiveStepLRLR_4 q T.left.tail.head T.left.head T.head
        T.right.head h5a hv1
      have hstep5 := step_of_transition_eq T
        (transition_fiveStepLRLR_5 q T.left.tail.head T.left.head T.head T.right.head h5a hv1)
      rcases e : step refM ⟨q, T⟩ with _ | c
      · exfalso
        apply fiveStepLRLR_not_none q T.head h5a
        rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
        · rw [← Zf393.zf393Trans_eq]; exact htr
        · simp only [step, htr, Option.map_some, reduceCtorEq] at e
      · rw [e] at hpres hstep5
        exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
          ⟨hpres, rfl⟩,
          step_five_left_right T h1 h2 h3' h4 hstep5⟩
  · have h1 := transition_threeStep_1 q T.left.tail.head T.left.head T.head T.right.head h3 hv1
    have h2 := transition_threeStep_2 q T.left.tail.head T.left.head T.head T.right.head h3 hv1
    have hstep3 := step_of_transition_eq T
      (transition_threeStep_3 q T.left.tail.head T.left.head T.head T.right.head h3 hv1)
    rcases e : step refM ⟨q, T⟩ with _ | c
    · exfalso
      apply threeStep_not_none q T.left.head T.head h3
      rcases htr : refM.transition q T.head with _ | ⟨w, d, q'⟩
      · rw [← Zf393.zf393Trans_eq]; exact htr
      · simp only [step, htr, Option.map_some, reduceCtorEq] at e
    · rw [e] at hpres hstep3
      exact ⟨⟨mapState c.state.val c.tape.left.head c.tape.head, c.tape⟩,
        ⟨hpres, rfl⟩,
        step_three_left_right T h1 h2 hstep3⟩

theorem rel_boot : Rel (cfgOfFast 64 [] 0 bootR_39753) (cfgOfFast 64 [] 0 bootR_39753) :=
  ⟨by decide, rfl⟩

theorem candidate_equivalent : Halts candidate ↔ Halts reference := by
  unfold BundledMachine.Halts ConjectureMachines.Halts
  rw [nSteps_eval_dom boot_cand, nSteps_eval_dom boot_ref]
  exact tr_eval_dom' respects rel_boot
end ConjectureMachines.Zf380
