/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

/-!
# Layer 1: Tape Layout and Primitive Register Gadgets for `riemann_744`

This file formalizes the canonical tape layout, unary register encodings, return-scan gadgets,
11-bit PC carry chain, and primitive register operations (`reg_init`, `reg_incr`, `reg_decr`)
for the 744-state Riemann Hypothesis Turing machine `reference` (`riemann_744`).
-/

@[expose] public section

namespace ConjectureMachines.Semantics.Riemann.Layer1

open Turing (Dir)
open StateTransition ConjectureMachines

abbrev reference : Machine 744 2 := Machines.riemann744

def refRow0 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 46 then (if q < 23 then (if q < 11 then (if q < 5 then (if q < 2 then (if q < 1 then
  (some (0, .right, 523), some (1, .right, 523)) else (some (0, .left, 3), some (1, .right,
  5))) else (if q < 3 then (some (0, .right, 1), some (0, .right, 1)) else (if q < 4 then
  (some (1, .left, 566), some (1, .left, 566)) else (some (0, .left, 6), some (1, .right,
  5))))) else (if q < 8 then (if q < 6 then (some (0, .right, 4), some (1, .right, 5)) else
  (if q < 7 then (some (0, .left, 7), some (1, .left, 7)) else (some (0, .left, 567), some (0,
  .left, 8)))) else (if q < 9 then (some (1, .left, 7), some (1, .left, 8)) else (if q < 10
  then (some (1, .left, 10), some (0, .left, 11)) else (some (0, .left, 14), some (1, .left,
  14)))))) else (if q < 17 then (if q < 14 then (if q < 12 then (some (1, .left, 14), some (0,
  .left, 15)) else (if q < 13 then (some (0, .left, 0), some (1, .left, 0)) else (some (1,
  .left, 0), some (0, .left, 0)))) else (if q < 15 then (some (0, .left, 16), some (1, .left,
  16)) else (if q < 16 then (some (1, .left, 16), some (0, .left, 17)) else (some (0, .left,
  18), some (1, .left, 18))))) else (if q < 20 then (if q < 18 then (some (1, .left, 18), some
  (0, .left, 19)) else (if q < 19 then (some (0, .left, 20), some (1, .left, 20)) else (some
  (1, .left, 20), some (0, .left, 21)))) else (if q < 21 then (some (0, .left, 22), some (1,
  .left, 22)) else (if q < 22 then (some (1, .left, 22), some (0, .left, 23)) else (some (0,
  .left, 24), some (1, .left, 24))))))) else (if q < 34 then (if q < 28 then (if q < 25 then
  (if q < 24 then (some (1, .left, 24), some (0, .left, 25)) else (some (0, .left, 26), some
  (1, .left, 26))) else (if q < 26 then (some (1, .left, 26), some (0, .left, 27)) else (if q
  < 27 then (some (0, .left, 28), some (1, .left, 28)) else (some (1, .left, 28), some (0,
  .left, 29))))) else (if q < 31 then (if q < 29 then (some (0, .left, 12), some (1, .left,
  12)) else (if q < 30 then (some (1, .left, 12), some (0, .left, 13)) else (some (0, .left,
  565), some (0, .right, 31)))) else (if q < 32 then (some (1, .right, 30), some (1, .right,
  31)) else (if q < 33 then (some (0, .right, 33), some (1, .right, 33)) else (some (0,
  .right, 34), some (1, .right, 34)))))) else (if q < 40 then (if q < 37 then (if q < 35 then
  (some (1, .left, 566), some (1, .right, 35)) else (if q < 36 then (some (0, .right, 34),
  some (1, .right, 35)) else (some (0, .left, 37), some (1, .left, 37)))) else (if q < 38 then
  (some (1, .left, 38), some (1, .left, 38)) else (if q < 39 then (some (1, .left, 177), some
  (1, .left, 177)) else (some (0, .left, 40), some (1, .left, 40))))) else (if q < 43 then (if
  q < 41 then (some (0, .left, 41), some (0, .left, 41)) else (if q < 42 then (some (1, .left,
  42), some (1, .left, 42)) else (some (0, .left, 43), some (0, .left, 43)))) else (if q < 44
  then (some (0, .left, 59), some (0, .left, 59)) else (if q < 45 then (some (0, .left, 45),
  some (1, .left, 45)) else (some (0, .left, 46), some (0, .left, 46)))))))) else (if q < 69
  then (if q < 57 then (if q < 51 then (if q < 48 then (if q < 47 then (some (0, .left, 47),
  some (0, .left, 47)) else (some (1, .left, 172), some (1, .left, 172))) else (if q < 49 then
  (some (0, .left, 49), some (1, .left, 49)) else (if q < 50 then (some (0, .left, 50), some
  (0, .left, 50)) else (some (0, .left, 51), some (0, .left, 51))))) else (if q < 54 then (if
  q < 52 then (some (1, .left, 52), some (1, .left, 52)) else (if q < 53 then (some (1, .left,
  53), some (1, .left, 53)) else (some (0, .left, 121), some (0, .left, 121)))) else (if q <
  55 then (some (0, .left, 55), some (1, .left, 55)) else (if q < 56 then (some (0, .left,
  56), some (0, .left, 56)) else (some (0, .left, 57), some (0, .left, 57)))))) else (if q <
  63 then (if q < 60 then (if q < 58 then (some (0, .left, 58), some (0, .left, 58)) else (if
  q < 59 then (some (1, .left, 59), some (1, .left, 59)) else (some (1, .left, 60), some (1,
  .left, 60)))) else (if q < 61 then (some (1, .left, 23), some (1, .left, 23)) else (if q <
  62 then (some (0, .left, 62), some (1, .left, 62)) else (some (0, .left, 63), some (0,
  .left, 63))))) else (if q < 66 then (if q < 64 then (some (1, .left, 57), some (1, .left,
  57)) else (if q < 65 then (some (0, .left, 65), some (1, .left, 65)) else (some (1, .left,
  66), some (1, .left, 66)))) else (if q < 67 then (some (0, .left, 67), some (0, .left, 67))
  else (if q < 68 then (some (1, .left, 68), some (1, .left, 68)) else (some (1, .left, 69),
  some (1, .left, 69))))))) else (if q < 81 then (if q < 75 then (if q < 72 then (if q < 70
  then (some (1, .left, 70), some (1, .left, 70)) else (if q < 71 then (some (1, .left, 71),
  some (1, .left, 71)) else (some (1, .left, 72), some (1, .left, 72)))) else (if q < 73 then
  (some (0, .left, 26), some (0, .left, 26)) else (if q < 74 then (some (0, .left, 74), some
  (1, .left, 74)) else (some (1, .left, 46), some (1, .left, 46))))) else (if q < 78 then (if
  q < 76 then (some (0, .left, 76), some (1, .left, 76)) else (if q < 77 then (some (0, .left,
  77), some (0, .left, 77)) else (some (0, .left, 78), some (0, .left, 78)))) else (if q < 79
  then (some (0, .left, 79), some (0, .left, 79)) else (if q < 80 then (some (0, .left, 120),
  some (0, .left, 120)) else (some (0, .left, 81), some (1, .left, 81)))))) else (if q < 87
  then (if q < 84 then (if q < 82 then (some (1, .left, 82), some (1, .left, 82)) else (if q <
  83 then (some (0, .left, 83), some (0, .left, 83)) else (some (0, .left, 84), some (0,
  .left, 84)))) else (if q < 85 then (some (0, .left, 19), some (0, .left, 19)) else (if q <
  86 then (some (0, .left, 86), some (1, .left, 86)) else (some (0, .left, 87), some (0,
  .left, 87))))) else (if q < 90 then (if q < 88 then (some (0, .left, 88), some (0, .left,
  88)) else (if q < 89 then (some (1, .left, 79), some (1, .left, 79)) else (some (0, .left,
  90), some (1, .left, 90)))) else (if q < 91 then (some (1, .left, 93), some (1, .left, 93))
  else (if q < 92 then (some (0, .left, 92), some (0, .left, 92)) else (some (0, .left, 0),
  some (0, .left, 0)))))))))

def refRow1 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 139 then (if q < 116 then (if q < 104 then (if q < 98 then (if q < 95 then (if q <
  94 then (some (0, .left, 94), some (0, .left, 94)) else (some (1, .left, 95), some (1,
  .left, 95))) else (if q < 96 then (some (0, .left, 96), some (0, .left, 96)) else (if q < 97
  then (some (1, .left, 97), some (1, .left, 97)) else (some (0, .left, 98), some (0, .left,
  98))))) else (if q < 101 then (if q < 99 then (some (0, .left, 99), some (0, .left, 99))
  else (if q < 100 then (some (0, .left, 100), some (0, .left, 100)) else (some (0, .left,
  91), some (0, .left, 91)))) else (if q < 102 then (some (0, .left, 102), some (1, .left,
  102)) else (if q < 103 then (some (1, .left, 103), some (1, .left, 103)) else (some (0,
  .left, 104), some (0, .left, 104)))))) else (if q < 110 then (if q < 107 then (if q < 105
  then (some (1, .left, 84), some (1, .left, 84)) else (if q < 106 then (some (0, .left, 106),
  some (1, .left, 106)) else (some (0, .left, 109), some (0, .left, 109)))) else (if q < 108
  then (some (0, .left, 108), some (1, .left, 108)) else (if q < 109 then (some (1, .left,
  109), some (1, .left, 109)) else (some (0, .left, 113), some (0, .left, 113))))) else (if q
  < 113 then (if q < 111 then (some (0, .left, 111), some (1, .left, 111)) else (if q < 112
  then (some (0, .left, 112), some (0, .left, 112)) else (some (1, .left, 113), some (1,
  .left, 113)))) else (if q < 114 then (some (0, .left, 114), some (0, .left, 114)) else (if q
  < 115 then (some (1, .left, 19), some (1, .left, 19)) else (some (0, .left, 116), some (1,
  .left, 116))))))) else (if q < 127 then (if q < 121 then (if q < 118 then (if q < 117 then
  (some (0, .left, 117), some (0, .left, 117)) else (some (0, .left, 118), some (0, .left,
  118))) else (if q < 119 then (some (1, .left, 119), some (1, .left, 119)) else (if q < 120
  then (some (1, .left, 120), some (1, .left, 120)) else (some (1, .left, 121), some (1,
  .left, 121))))) else (if q < 124 then (if q < 122 then (some (0, .left, 22), some (0, .left,
  22)) else (if q < 123 then (some (0, .left, 123), some (1, .left, 123)) else (some (1,
  .left, 124), some (1, .left, 124)))) else (if q < 125 then (some (0, .left, 125), some (0,
  .left, 125)) else (if q < 126 then (some (1, .left, 114), some (1, .left, 114)) else (some
  (0, .left, 127), some (1, .left, 127)))))) else (if q < 133 then (if q < 130 then (if q <
  128 then (some (1, .left, 128), some (1, .left, 128)) else (if q < 129 then (some (0, .left,
  129), some (0, .left, 129)) else (some (1, .left, 130), some (1, .left, 130)))) else (if q <
  131 then (some (1, .left, 131), some (1, .left, 131)) else (if q < 132 then (some (1, .left,
  132), some (1, .left, 132)) else (some (0, .left, 145), some (0, .left, 145))))) else (if q
  < 136 then (if q < 134 then (some (0, .left, 134), some (1, .left, 134)) else (if q < 135
  then (some (0, .left, 135), some (0, .left, 135)) else (some (0, .left, 136), some (0,
  .left, 136)))) else (if q < 137 then (some (1, .left, 137), some (1, .left, 137)) else (if q
  < 138 then (some (0, .left, 173), some (0, .left, 173)) else (some (0, .left, 139), some (1,
  .left, 139)))))))) else (if q < 162 then (if q < 150 then (if q < 144 then (if q < 141 then
  (if q < 140 then (some (0, .left, 140), some (0, .left, 140)) else (some (0, .left, 141),
  some (0, .left, 141))) else (if q < 142 then (some (1, .left, 142), some (1, .left, 142))
  else (if q < 143 then (some (1, .left, 143), some (1, .left, 143)) else (some (0, .left,
  144), some (0, .left, 144))))) else (if q < 147 then (if q < 145 then (some (1, .left, 145),
  some (1, .left, 145)) else (if q < 146 then (some (0, .left, 72), some (0, .left, 72)) else
  (some (0, .left, 147), some (1, .left, 147)))) else (if q < 148 then (some (1, .left, 135),
  some (1, .left, 135)) else (if q < 149 then (some (0, .left, 149), some (1, .left, 149))
  else (some (0, .left, 150), some (0, .left, 150)))))) else (if q < 156 then (if q < 153 then
  (if q < 151 then (some (0, .left, 151), some (0, .left, 151)) else (if q < 152 then (some
  (1, .left, 152), some (1, .left, 152)) else (some (0, .left, 153), some (0, .left, 153))))
  else (if q < 154 then (some (1, .left, 154), some (1, .left, 154)) else (if q < 155 then
  (some (1, .left, 155), some (1, .left, 155)) else (some (0, .left, 24), some (0, .left,
  24))))) else (if q < 159 then (if q < 157 then (some (0, .left, 157), some (1, .left, 157))
  else (if q < 158 then (some (0, .left, 165), some (0, .left, 165)) else (some (0, .left,
  159), some (1, .left, 159)))) else (if q < 160 then (some (0, .left, 160), some (0, .left,
  160)) else (if q < 161 then (some (0, .left, 161), some (0, .left, 161)) else (some (1,
  .left, 162), some (1, .left, 162))))))) else (if q < 174 then (if q < 168 then (if q < 165
  then (if q < 163 then (some (1, .left, 153), some (1, .left, 153)) else (if q < 164 then
  (some (0, .left, 164), some (1, .left, 164)) else (some (1, .left, 165), some (1, .left,
  165)))) else (if q < 166 then (some (1, .left, 15), some (1, .left, 15)) else (if q < 167
  then (some (0, .left, 167), some (1, .left, 167)) else (some (0, .left, 176), some (0,
  .left, 176))))) else (if q < 171 then (if q < 169 then (some (0, .left, 169), some (1,
  .left, 169)) else (if q < 170 then (some (0, .left, 170), some (0, .left, 170)) else (some
  (0, .left, 171), some (0, .left, 171)))) else (if q < 172 then (some (0, .left, 172), some
  (0, .left, 172)) else (if q < 173 then (some (1, .left, 173), some (1, .left, 173)) else
  (some (0, .left, 20), some (0, .left, 20)))))) else (if q < 180 then (if q < 177 then (if q
  < 175 then (some (0, .left, 175), some (1, .left, 175)) else (if q < 176 then (some (1,
  .left, 176), some (1, .left, 176)) else (some (0, .left, 177), some (0, .left, 177)))) else
  (if q < 178 then (some (0, .left, 17), some (0, .left, 17)) else (if q < 179 then (some (0,
  .left, 179), some (1, .left, 179)) else (some (1, .left, 180), some (1, .left, 180))))) else
  (if q < 183 then (if q < 181 then (some (0, .left, 181), some (0, .left, 181)) else (if q <
  182 then (some (0, .left, 182), some (0, .left, 182)) else (some (0, .left, 183), some (0,
  .left, 183)))) else (if q < 184 then (some (0, .left, 70), some (0, .left, 70)) else (if q <
  185 then (some (0, .right, 32), some (1, .right, 32)) else (some (0, .right, 184), some (1,
  .right, 184)))))))))

def refRow2 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 232 then (if q < 209 then (if q < 197 then (if q < 191 then (if q < 188 then (if q <
  187 then (some (0, .right, 185), some (1, .right, 185)) else (some (0, .right, 186), some
  (1, .right, 186))) else (if q < 189 then (some (0, .right, 551), some (1, .right, 188)) else
  (if q < 190 then (some (0, .right, 188), some (1, .right, 524)) else (some (0, .right, 639),
  some (1, .right, 189))))) else (if q < 194 then (if q < 192 then (some (0, .right, 190),
  some (1, .right, 652)) else (if q < 193 then (some (0, .right, 187), some (1, .right, 191))
  else (some (0, .right, 714), some (1, .right, 625)))) else (if q < 195 then (some (0,
  .right, 694), some (1, .right, 526)) else (if q < 196 then (some (0, .right, 193), some (1,
  .right, 194)) else (some (0, .right, 714), some (1, .right, 526)))))) else (if q < 203 then
  (if q < 200 then (if q < 198 then (some (0, .right, 652), some (1, .right, 196)) else (if q
  < 199 then (some (0, .right, 195), some (1, .right, 197)) else (some (0, .right, 192), some
  (1, .right, 198)))) else (if q < 201 then (some (0, .right, 741), some (1, .right, 526))
  else (if q < 202 then (some (0, .right, 661), some (1, .right, 200)) else (some (0, .right,
  547), some (1, .right, 644))))) else (if q < 206 then (if q < 204 then (some (0, .right,
  546), some (1, .right, 163)) else (if q < 205 then (some (0, .right, 202), some (1, .right,
  203)) else (some (0, .right, 739), some (1, .right, 204)))) else (if q < 207 then (some (0,
  .right, 631), some (1, .right, 205)) else (if q < 208 then (some (0, .right, 201), some (1,
  .right, 206)) else (some (0, .right, 115), some (1, .right, 560))))))) else (if q < 220 then
  (if q < 214 then (if q < 211 then (if q < 210 then (some (0, .right, 48), some (1, .right,
  525)) else (some (0, .right, 208), some (1, .right, 209))) else (if q < 212 then (some (0,
  .right, 210), some (1, .right, 734)) else (if q < 213 then (some (0, .right, 545), some (1,
  .right, 64)) else (some (0, .right, 212), some (1, .right, 524))))) else (if q < 217 then
  (if q < 215 then (some (0, .right, 213), some (1, .right, 526)) else (if q < 216 then (some
  (0, .right, 211), some (1, .right, 214)) else (some (0, .right, 168), some (1, .right,
  543)))) else (if q < 218 then (some (0, .right, 156), some (1, .right, 542)) else (if q <
  219 then (some (0, .right, 216), some (1, .right, 217)) else (some (0, .right, 737), some
  (1, .right, 218)))))) else (if q < 226 then (if q < 223 then (if q < 221 then (some (0,
  .right, 628), some (1, .right, 219)) else (if q < 222 then (some (0, .right, 215), some (1,
  .right, 220)) else (some (0, .right, 207), some (1, .right, 221)))) else (if q < 224 then
  (some (0, .right, 199), some (1, .right, 222)) else (if q < 225 then (some (0, .right, 174),
  some (1, .right, 64)) else (some (0, .right, 542), some (1, .right, 80))))) else (if q < 229
  then (if q < 227 then (some (0, .right, 224), some (1, .right, 225)) else (if q < 228 then
  (some (0, .right, 226), some (1, .right, 684)) else (some (0, .right, 54), some (1, .right,
  525)))) else (if q < 230 then (some (0, .right, 228), some (1, .right, 524)) else (if q <
  231 then (some (0, .right, 229), some (1, .right, 700)) else (some (0, .right, 227), some
  (1, .right, 230)))))))) else (if q < 255 then (if q < 243 then (if q < 237 then (if q < 234
  then (if q < 233 then (some (0, .right, 229), some (1, .right, 526)) else (some (0, .right,
  232), some (1, .right, 655))) else (if q < 235 then (some (0, .right, 231), some (1, .right,
  233)) else (if q < 236 then (some (0, .right, 695), some (1, .right, 526)) else (some (0,
  .right, 235), some (1, .right, 663))))) else (if q < 240 then (if q < 238 then (some (0,
  .right, 200), some (1, .right, 682)) else (if q < 239 then (some (0, .right, 236), some (1,
  .right, 237)) else (some (0, .right, 234), some (1, .right, 238)))) else (if q < 241 then
  (some (0, .right, 546), some (1, .right, 644)) else (if q < 242 then (some (0, .right, 547),
  some (1, .right, 163)) else (some (0, .right, 240), some (1, .right, 241)))))) else (if q <
  249 then (if q < 246 then (if q < 244 then (some (0, .right, 743), some (1, .right, 242))
  else (if q < 245 then (some (0, .right, 133), some (1, .right, 560)) else (some (0, .right,
  148), some (1, .right, 525)))) else (if q < 247 then (some (0, .right, 244), some (1,
  .right, 245)) else (if q < 248 then (some (0, .right, 246), some (1, .right, 728)) else
  (some (0, .right, 243), some (1, .right, 247))))) else (if q < 252 then (if q < 250 then
  (some (0, .right, 545), some (1, .right, 101)) else (if q < 251 then (some (0, .right, 249),
  some (1, .right, 524)) else (some (0, .right, 250), some (1, .right, 526)))) else (if q <
  253 then (some (0, .right, 251), some (1, .right, 674)) else (if q < 254 then (some (0,
  .right, 248), some (1, .right, 252)) else (some (0, .right, 75), some (1, .right, 542)))))))
  else (if q < 267 then (if q < 261 then (if q < 258 then (if q < 256 then (some (0, .right,
  156), some (1, .right, 543)) else (if q < 257 then (some (0, .right, 254), some (1, .right,
  255)) else (some (0, .right, 732), some (1, .right, 256)))) else (if q < 259 then (some (0,
  .right, 80), some (1, .right, 146)) else (if q < 260 then (some (0, .right, 543), some (1,
  .right, 110)) else (some (0, .right, 258), some (1, .right, 259))))) else (if q < 264 then
  (if q < 262 then (some (0, .right, 260), some (1, .right, 700)) else (if q < 263 then (some
  (0, .right, 257), some (1, .right, 261)) else (some (0, .right, 166), some (1, .right,
  525)))) else (if q < 265 then (some (0, .right, 263), some (1, .right, 524)) else (if q <
  266 then (some (0, .right, 264), some (1, .right, 684)) else (some (0, .right, 551), some
  (1, .right, 138)))))) else (if q < 273 then (if q < 270 then (if q < 268 then (some (0,
  .right, 266), some (1, .right, 524)) else (if q < 269 then (some (0, .right, 267), some (1,
  .right, 526)) else (some (0, .right, 265), some (1, .right, 268)))) else (if q < 271 then
  (some (0, .right, 262), some (1, .right, 269)) else (if q < 272 then (some (0, .right, 253),
  some (1, .right, 270)) else (some (0, .right, 239), some (1, .right, 271))))) else (if q <
  276 then (if q < 274 then (some (0, .right, 223), some (1, .right, 272)) else (if q < 275
  then (some (0, .right, 542), some (1, .right, 89)) else (some (0, .right, 274), some (1,
  .right, 274)))) else (if q < 277 then (some (0, .right, 716), some (1, .right, 275)) else
  (if q < 278 then (some (0, .right, 671), some (1, .right, 276)) else (some (0, .right, 275),
  some (1, .right, 275)))))))))

def refRow3 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 325 then (if q < 302 then (if q < 290 then (if q < 284 then (if q < 281 then (if q <
  280 then (some (0, .right, 278), some (1, .right, 278)) else (some (0, .right, 277), some
  (1, .right, 279))) else (if q < 282 then (some (0, .right, 279), some (1, .right, 279)) else
  (if q < 283 then (some (0, .right, 280), some (1, .right, 281)) else (some (0, .right, 281),
  some (1, .right, 281))))) else (if q < 287 then (if q < 285 then (some (0, .right, 282),
  some (1, .right, 283)) else (if q < 286 then (some (0, .right, 283), some (1, .right, 283))
  else (some (0, .right, 284), some (1, .right, 285)))) else (if q < 288 then (some (0,
  .right, 273), some (1, .right, 286)) else (if q < 289 then (some (0, .right, 285), some (1,
  .right, 285)) else (some (0, .right, 684), some (1, .right, 665)))))) else (if q < 296 then
  (if q < 293 then (if q < 291 then (some (0, .right, 278), some (1, .right, 289)) else (if q
  < 292 then (some (0, .right, 552), some (1, .right, 525)) else (some (0, .right, 291), some
  (1, .right, 524)))) else (if q < 294 then (some (0, .right, 605), some (1, .right, 292))
  else (if q < 295 then (some (0, .right, 553), some (1, .right, 525)) else (some (0, .right,
  294), some (1, .right, 524))))) else (if q < 299 then (if q < 297 then (some (0, .right,
  616), some (1, .right, 295)) else (if q < 298 then (some (0, .right, 293), some (1, .right,
  296)) else (some (0, .right, 290), some (1, .right, 297)))) else (if q < 300 then (some (0,
  .right, 709), some (1, .right, 526)) else (if q < 301 then (some (0, .right, 619), some (1,
  .right, 299)) else (some (0, .right, 543), some (1, .right, 644))))))) else (if q < 313 then
  (if q < 307 then (if q < 304 then (if q < 303 then (some (0, .right, 542), some (1, .right,
  107)) else (some (0, .right, 301), some (1, .right, 302))) else (if q < 305 then (some (0,
  .right, 724), some (1, .right, 303)) else (if q < 306 then (some (0, .right, 658), some (1,
  .right, 304)) else (some (0, .right, 300), some (1, .right, 305))))) else (if q < 310 then
  (if q < 308 then (some (0, .right, 298), some (1, .right, 306)) else (if q < 309 then (some
  (0, .right, 158), some (1, .right, 542)) else (some (0, .right, 75), some (1, .right,
  525)))) else (if q < 311 then (some (0, .right, 308), some (1, .right, 309)) else (if q <
  312 then (some (0, .right, 310), some (1, .right, 684)) else (some (0, .right, 39), some (1,
  .right, 525)))))) else (if q < 319 then (if q < 316 then (if q < 314 then (some (0, .right,
  312), some (1, .right, 524)) else (if q < 315 then (some (0, .right, 313), some (1, .right,
  700)) else (some (0, .right, 311), some (1, .right, 314)))) else (if q < 317 then (some (0,
  .right, 542), some (1, .right, 122)) else (if q < 318 then (some (0, .right, 316), some (1,
  .right, 524)) else (some (0, .right, 726), some (1, .right, 317))))) else (if q < 322 then
  (if q < 320 then (some (0, .right, 669), some (1, .right, 318)) else (if q < 321 then (some
  (0, .right, 315), some (1, .right, 319)) else (some (0, .right, 115), some (1, .right,
  525)))) else (if q < 323 then (some (0, .right, 321), some (1, .right, 524)) else (if q <
  324 then (some (0, .right, 722), some (1, .right, 322)) else (some (0, .right, 621), some
  (1, .right, 323)))))))) else (if q < 348 then (if q < 336 then (if q < 330 then (if q < 327
  then (if q < 326 then (some (0, .right, 690), some (1, .right, 665)) else (some (0, .right,
  610), some (1, .right, 325))) else (if q < 328 then (some (0, .right, 324), some (1, .right,
  326)) else (if q < 329 then (some (0, .right, 320), some (1, .right, 327)) else (some (0,
  .right, 307), some (1, .right, 328))))) else (if q < 333 then (if q < 331 then (some (0,
  .right, 715), some (1, .right, 526)) else (if q < 332 then (some (0, .right, 330), some (1,
  .right, 607)) else (some (0, .right, 542), some (1, .right, 101)))) else (if q < 334 then
  (some (0, .right, 332), some (1, .right, 524)) else (if q < 335 then (some (0, .right, 721),
  some (1, .right, 333)) else (some (0, .right, 334), some (1, .right, 621)))))) else (if q <
  342 then (if q < 339 then (if q < 337 then (some (0, .right, 331), some (1, .right, 335))
  else (if q < 338 then (some (0, .right, 85), some (1, .right, 525)) else (some (0, .right,
  337), some (1, .right, 524)))) else (if q < 340 then (some (0, .right, 722), some (1,
  .right, 338)) else (if q < 341 then (some (0, .right, 605), some (1, .right, 707)) else
  (some (0, .right, 339), some (1, .right, 340))))) else (if q < 345 then (if q < 343 then
  (some (0, .right, 553), some (1, .right, 126)) else (if q < 344 then (some (0, .right, 342),
  some (1, .right, 524)) else (some (0, .right, 343), some (1, .right, 526)))) else (if q <
  346 then (some (0, .right, 344), some (1, .right, 669)) else (if q < 347 then (some (0,
  .right, 341), some (1, .right, 345)) else (some (0, .right, 336), some (1, .right,
  346))))))) else (if q < 360 then (if q < 354 then (if q < 351 then (if q < 349 then (some
  (0, .right, 726), some (1, .right, 526)) else (if q < 350 then (some (0, .right, 348), some
  (1, .right, 614)) else (some (0, .right, 546), some (1, .right, 101)))) else (if q < 352
  then (some (0, .right, 350), some (1, .right, 524)) else (if q < 353 then (some (0, .right,
  735), some (1, .right, 351)) else (some (0, .right, 352), some (1, .right, 679))))) else (if
  q < 357 then (if q < 355 then (some (0, .right, 349), some (1, .right, 353)) else (if q <
  356 then (some (0, .right, 738), some (1, .right, 338)) else (some (0, .right, 545), some
  (1, .right, 644)))) else (if q < 358 then (some (0, .right, 543), some (1, .right, 525))
  else (if q < 359 then (some (0, .right, 356), some (1, .right, 357)) else (some (0, .right,
  698), some (1, .right, 358)))))) else (if q < 366 then (if q < 363 then (if q < 361 then
  (some (0, .right, 355), some (1, .right, 359)) else (if q < 362 then (some (0, .right, 44),
  some (1, .right, 525)) else (some (0, .right, 361), some (1, .right, 524)))) else (if q <
  364 then (some (0, .right, 362), some (1, .right, 570)) else (if q < 365 then (some (0,
  .right, 702), some (1, .right, 526)) else (some (0, .right, 363), some (1, .right, 364)))))
  else (if q < 369 then (if q < 367 then (some (0, .right, 360), some (1, .right, 365)) else
  (if q < 368 then (some (0, .right, 354), some (1, .right, 366)) else (some (0, .right, 347),
  some (1, .right, 367)))) else (if q < 370 then (some (0, .right, 329), some (1, .right,
  368)) else (if q < 371 then (some (0, .right, 288), some (1, .right, 369)) else (some (0,
  .right, 287), some (1, .right, 370)))))))))

def refRow4 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 418 then (if q < 395 then (if q < 383 then (if q < 377 then (if q < 374 then (if q <
  373 then (some (0, .right, 545), some (1, .right, 126)) else (some (0, .right, 372), some
  (1, .right, 524))) else (if q < 375 then (some (0, .right, 685), some (1, .right, 373)) else
  (if q < 376 then (some (0, .right, 576), some (1, .right, 374)) else (some (0, .right, 209),
  some (1, .right, 524))))) else (if q < 380 then (if q < 378 then (some (0, .right, 685),
  some (1, .right, 376)) else (if q < 379 then (some (0, .right, 572), some (1, .right, 377))
  else (some (0, .right, 375), some (1, .right, 378)))) else (if q < 381 then (some (0,
  .right, 570), some (1, .right, 702)) else (if q < 382 then (some (0, .right, 380), some (1,
  .right, 612)) else (some (0, .right, 690), some (1, .right, 250)))))) else (if q < 389 then
  (if q < 386 then (if q < 384 then (some (0, .right, 382), some (1, .right, 610)) else (if q
  < 385 then (some (0, .right, 381), some (1, .right, 383)) else (some (0, .right, 379), some
  (1, .right, 384)))) else (if q < 387 then (some (0, .right, 245), some (1, .right, 524))
  else (if q < 388 then (some (0, .right, 690), some (1, .right, 386)) else (some (0, .right,
  578), some (1, .right, 704))))) else (if q < 392 then (if q < 390 then (some (0, .right,
  387), some (1, .right, 388)) else (if q < 391 then (some (0, .right, 583), some (1, .right,
  595)) else (some (0, .right, 557), some (1, .right, 525)))) else (if q < 393 then (some (0,
  .right, 391), some (1, .right, 524)) else (if q < 394 then (some (0, .right, 392), some (1,
  .right, 616)) else (some (0, .right, 390), some (1, .right, 393))))))) else (if q < 406 then
  (if q < 400 then (if q < 397 then (if q < 396 then (some (0, .right, 389), some (1, .right,
  394)) else (some (0, .right, 295), some (1, .right, 526))) else (if q < 398 then (some (0,
  .right, 396), some (1, .right, 621)) else (if q < 399 then (some (0, .right, 722), some (1,
  .right, 526)) else (some (0, .right, 398), some (1, .right, 676))))) else (if q < 403 then
  (if q < 401 then (some (0, .right, 397), some (1, .right, 399)) else (if q < 402 then (some
  (0, .right, 395), some (1, .right, 400)) else (some (0, .right, 385), some (1, .right,
  401)))) else (if q < 404 then (some (0, .right, 543), some (1, .right, 80)) else (if q < 405
  then (some (0, .right, 356), some (1, .right, 403)) else (some (0, .right, 696), some (1,
  .right, 404)))))) else (if q < 412 then (if q < 409 then (if q < 407 then (some (0, .right,
  133), some (1, .right, 543)) else (if q < 408 then (some (0, .right, 105), some (1, .right,
  525)) else (some (0, .right, 406), some (1, .right, 407)))) else (if q < 410 then (some (0,
  .right, 408), some (1, .right, 700)) else (if q < 411 then (some (0, .right, 405), some (1,
  .right, 409)) else (some (0, .right, 61), some (1, .right, 525))))) else (if q < 415 then
  (if q < 413 then (some (0, .right, 411), some (1, .right, 524)) else (if q < 414 then (some
  (0, .right, 412), some (1, .right, 718)) else (some (0, .right, 413), some (1, .right,
  588)))) else (if q < 416 then (some (0, .right, 410), some (1, .right, 414)) else (if q <
  417 then (some (0, .right, 543), some (1, .right, 101)) else (some (0, .right, 416), some
  (1, .right, 524)))))))) else (if q < 441 then (if q < 429 then (if q < 423 then (if q < 420
  then (if q < 419 then (some (0, .right, 687), some (1, .right, 417)) else (some (0, .right,
  418), some (1, .right, 623))) else (if q < 421 then (some (0, .right, 133), some (1, .right,
  525)) else (if q < 422 then (some (0, .right, 420), some (1, .right, 524)) else (some (0,
  .right, 691), some (1, .right, 421))))) else (if q < 426 then (if q < 424 then (some (0,
  .right, 422), some (1, .right, 603)) else (if q < 425 then (some (0, .right, 419), some (1,
  .right, 423)) else (some (0, .right, 415), some (1, .right, 424)))) else (if q < 427 then
  (some (0, .right, 706), some (1, .right, 583)) else (if q < 428 then (some (0, .right, 719),
  some (1, .right, 526)) else (some (0, .right, 426), some (1, .right, 427)))))) else (if q <
  435 then (if q < 432 then (if q < 430 then (some (0, .right, 543), some (1, .right, 122))
  else (if q < 431 then (some (0, .right, 429), some (1, .right, 524)) else (some (0, .right,
  688), some (1, .right, 430)))) else (if q < 433 then (some (0, .right, 597), some (1,
  .right, 431)) else (if q < 434 then (some (0, .right, 428), some (1, .right, 432)) else
  (some (0, .right, 691), some (1, .right, 322))))) else (if q < 438 then (if q < 436 then
  (some (0, .right, 623), some (1, .right, 434)) else (if q < 437 then (some (0, .right, 595),
  some (1, .right, 720)) else (some (0, .right, 553), some (1, .right, 178)))) else (if q <
  439 then (some (0, .right, 437), some (1, .right, 524)) else (if q < 440 then (some (0,
  .right, 438), some (1, .right, 526)) else (some (0, .right, 436), some (1, .right,
  439))))))) else (if q < 453 then (if q < 447 then (if q < 444 then (if q < 442 then (some
  (0, .right, 435), some (1, .right, 440)) else (if q < 443 then (some (0, .right, 433), some
  (1, .right, 441)) else (some (0, .right, 425), some (1, .right, 442)))) else (if q < 445
  then (some (0, .right, 402), some (1, .right, 443)) else (if q < 446 then (some (0, .right,
  543), some (1, .right, 126)) else (some (0, .right, 445), some (1, .right, 524))))) else (if
  q < 450 then (if q < 448 then (some (0, .right, 687), some (1, .right, 446)) else (if q <
  449 then (some (0, .right, 588), some (1, .right, 447)) else (some (0, .right, 687), some
  (1, .right, 376)))) else (if q < 451 then (some (0, .right, 593), some (1, .right, 449))
  else (if q < 452 then (some (0, .right, 448), some (1, .right, 450)) else (some (0, .right,
  583), some (1, .right, 719)))))) else (if q < 459 then (if q < 456 then (if q < 454 then
  (some (0, .right, 452), some (1, .right, 585)) else (if q < 455 then (some (0, .right, 730),
  some (1, .right, 333)) else (some (0, .right, 454), some (1, .right, 591)))) else (if q <
  457 then (some (0, .right, 453), some (1, .right, 455)) else (if q < 458 then (some (0,
  .right, 451), some (1, .right, 456)) else (some (0, .right, 148), some (1, .right, 543)))))
  else (if q < 462 then (if q < 460 then (some (0, .right, 101), some (1, .right, 525)) else
  (if q < 461 then (some (0, .right, 458), some (1, .right, 459)) else (some (0, .right, 730),
  some (1, .right, 460)))) else (if q < 463 then (some (0, .right, 461), some (1, .right,
  676)) else (if q < 464 then (some (0, .right, 146), some (1, .right, 525)) else (some (0,
  .right, 463), some (1, .right, 524)))))))))

def refRow5 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 511 then (if q < 488 then (if q < 476 then (if q < 470 then (if q < 467 then (if q <
  466 then (some (0, .right, 696), some (1, .right, 464)) else (some (0, .right, 465), some
  (1, .right, 452))) else (if q < 468 then (some (0, .right, 462), some (1, .right, 466)) else
  (if q < 469 then (some (0, .right, 543), some (1, .right, 64)) else (some (0, .right, 468),
  some (1, .right, 524))))) else (if q < 473 then (if q < 471 then (some (0, .right, 688),
  some (1, .right, 469)) else (if q < 472 then (some (0, .right, 597), some (1, .right, 470))
  else (some (0, .right, 688), some (1, .right, 362)))) else (if q < 474 then (some (0,
  .right, 599), some (1, .right, 472)) else (if q < 475 then (some (0, .right, 471), some (1,
  .right, 473)) else (some (0, .right, 467), some (1, .right, 474)))))) else (if q < 482 then
  (if q < 479 then (if q < 477 then (some (0, .right, 457), some (1, .right, 475)) else (if q
  < 478 then (some (0, .right, 436), some (1, .right, 597)) else (some (0, .right, 688), some
  (1, .right, 417)))) else (if q < 480 then (some (0, .right, 478), some (1, .right, 599))
  else (if q < 481 then (some (0, .right, 477), some (1, .right, 479)) else (some (0, .right,
  688), some (1, .right, 338))))) else (if q < 485 then (if q < 483 then (some (0, .right,
  481), some (1, .right, 436)) else (if q < 484 then (some (0, .right, 685), some (1, .right,
  430)) else (some (0, .right, 572), some (1, .right, 483)))) else (if q < 486 then (some (0,
  .right, 482), some (1, .right, 484)) else (if q < 487 then (some (0, .right, 480), some (1,
  .right, 485)) else (some (0, .right, 158), some (1, .right, 525))))))) else (if q < 499 then
  (if q < 493 then (if q < 490 then (if q < 489 then (some (0, .right, 487), some (1, .right,
  524)) else (some (0, .right, 688), some (1, .right, 488))) else (if q < 491 then (some (0,
  .right, 599), some (1, .right, 489)) else (if q < 492 then (some (0, .right, 729), some (1,
  .right, 317)) else (some (0, .right, 581), some (1, .right, 491))))) else (if q < 496 then
  (if q < 494 then (some (0, .right, 490), some (1, .right, 492)) else (if q < 495 then (some
  (0, .right, 115), some (1, .right, 543)) else (some (0, .right, 156), some (1, .right,
  545)))) else (if q < 497 then (some (0, .right, 494), some (1, .right, 495)) else (if q <
  498 then (some (0, .right, 730), some (1, .right, 496)) else (some (0, .right, 591), some
  (1, .right, 497)))))) else (if q < 505 then (if q < 502 then (if q < 500 then (some (0,
  .right, 174), some (1, .right, 73)) else (if q < 501 then (some (0, .right, 545), some (1,
  .right, 89)) else (some (0, .right, 499), some (1, .right, 500)))) else (if q < 503 then
  (some (0, .right, 501), some (1, .right, 718)) else (if q < 504 then (some (0, .right, 36),
  some (1, .right, 525)) else (some (0, .right, 503), some (1, .right, 524))))) else (if q <
  508 then (if q < 506 then (some (0, .right, 504), some (1, .right, 700)) else (if q < 507
  then (some (0, .right, 502), some (1, .right, 505)) else (some (0, .right, 498), some (1,
  .right, 506)))) else (if q < 509 then (some (0, .right, 493), some (1, .right, 507)) else
  (if q < 510 then (some (0, .right, 486), some (1, .right, 508)) else (some (0, .right, 476),
  some (1, .right, 509)))))))) else (if q < 534 then (if q < 522 then (if q < 516 then (if q <
  513 then (if q < 512 then (some (0, .right, 444), some (1, .right, 510)) else (some (0,
  .right, 89), some (1, .right, 635))) else (if q < 514 then (some (0, .right, 89), none) else
  (if q < 515 then (some (0, .right, 512), some (1, .right, 513)) else (some (0, .right, 514),
  some (1, .right, 526))))) else (if q < 519 then (if q < 517 then (some (0, .right, 515),
  some (1, .right, 527)) else (if q < 518 then (some (0, .right, 516), some (1, .right, 528))
  else (some (0, .right, 517), some (1, .right, 529)))) else (if q < 520 then (some (0,
  .right, 518), some (1, .right, 530)) else (if q < 521 then (some (0, .right, 519), some (1,
  .right, 531)) else (some (0, .right, 520), some (1, .right, 532)))))) else (if q < 528 then
  (if q < 525 then (if q < 523 then (some (0, .right, 511), some (1, .right, 521)) else (if q
  < 524 then (some (0, .right, 371), some (1, .right, 522)) else (some (0, .left, 11), some
  (1, .left, 11)))) else (if q < 526 then (some (0, .left, 9), some (1, .left, 9)) else (if q
  < 527 then (some (0, .left, 15), some (1, .left, 15)) else (some (0, .left, 17), some (1,
  .left, 17))))) else (if q < 531 then (if q < 529 then (some (0, .left, 19), some (1, .left,
  19)) else (if q < 530 then (some (0, .left, 21), some (1, .left, 21)) else (some (0, .left,
  23), some (1, .left, 23)))) else (if q < 532 then (some (0, .left, 25), some (1, .left, 25))
  else (if q < 533 then (some (0, .left, 27), some (1, .left, 27)) else (some (0, .right, 2),
  some (1, .right, 533))))))) else (if q < 546 then (if q < 540 then (if q < 537 then (if q <
  535 then (some (0, .right, 533), some (1, .right, 534)) else (if q < 536 then (some (0,
  .right, 534), some (1, .right, 535)) else (some (0, .right, 549), some (1, .right, 536))))
  else (if q < 538 then (some (0, .right, 536), some (1, .right, 537)) else (if q < 539 then
  (some (0, .right, 537), some (1, .right, 538)) else (some (0, .right, 538), some (1, .right,
  539))))) else (if q < 543 then (if q < 541 then (some (0, .right, 539), some (1, .right,
  540)) else (if q < 542 then (some (0, .right, 540), some (1, .right, 541)) else (some (0,
  .right, 535), some (1, .right, 542)))) else (if q < 544 then (some (0, .right, 542), some
  (1, .right, 543)) else (if q < 545 then (some (0, .right, 543), some (1, .right, 544)) else
  (some (0, .right, 544), some (1, .right, 545)))))) else (if q < 552 then (if q < 549 then
  (if q < 547 then (some (0, .right, 545), some (1, .right, 546)) else (if q < 548 then (some
  (0, .right, 546), some (1, .right, 547)) else (some (0, .right, 547), some (1, .right,
  548)))) else (if q < 550 then (some (0, .right, 548), some (1, .right, 549)) else (if q <
  551 then (some (0, .right, 31), some (1, .right, 550)) else (some (0, .right, 550), some (1,
  .right, 551))))) else (if q < 555 then (if q < 553 then (some (0, .right, 564), some (1,
  .right, 552)) else (if q < 554 then (some (0, .right, 552), some (1, .right, 553)) else
  (some (0, .right, 553), some (1, .right, 554)))) else (if q < 556 then (some (0, .right,
  554), some (1, .right, 555)) else (if q < 557 then (some (0, .right, 555), some (1, .right,
  556)) else (some (0, .right, 556), some (1, .right, 557)))))))))

def refRow6 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 604 then (if q < 581 then (if q < 569 then (if q < 563 then (if q < 560 then (if q <
  559 then (some (0, .right, 188), some (1, .right, 558)) else (some (0, .right, 648), some
  (1, .right, 559))) else (if q < 561 then (some (0, .right, 559), some (1, .right, 560)) else
  (if q < 562 then (some (0, .right, 560), some (1, .right, 561)) else (some (0, .right, 561),
  some (1, .right, 562))))) else (if q < 566 then (if q < 564 then (some (0, .right, 562),
  some (1, .right, 563)) else (if q < 565 then (some (0, .right, 563), some (1, .right, 564))
  else (some (0, .left, 9), some (1, .left, 566)))) else (if q < 567 then (some (0, .left,
  565), some (1, .left, 566)) else (if q < 568 then (some (0, .left, 524), some (1, .left,
  568)) else (some (0, .left, 567), some (1, .left, 568)))))) else (if q < 575 then (if q <
  572 then (if q < 570 then (some (0, .right, 538), some (1, .right, 635)) else (if q < 571
  then (some (0, .right, 569), some (1, .right, 638)) else (some (0, .right, 573), some (1,
  .right, 653)))) else (if q < 573 then (some (0, .right, 571), some (1, .right, 651)) else
  (if q < 574 then (some (0, .right, 538), some (1, .right, 644)) else (some (0, .right, 560),
  some (1, .right, 558))))) else (if q < 578 then (if q < 576 then (some (0, .right, 573),
  some (1, .right, 574)) else (if q < 577 then (some (0, .right, 575), some (1, .right, 651))
  else (some (0, .right, 539), some (1, .right, 635)))) else (if q < 579 then (some (0,
  .right, 577), some (1, .right, 638)) else (if q < 580 then (some (0, .right, 539), some (1,
  .right, 644)) else (some (0, .right, 579), some (1, .right, 672))))))) else (if q < 592 then
  (if q < 586 then (if q < 583 then (if q < 582 then (some (0, .right, 580), some (1, .right,
  651)) else (some (0, .right, 540), some (1, .right, 635))) else (if q < 584 then (some (0,
  .right, 582), some (1, .right, 638)) else (if q < 585 then (some (0, .right, 586), some (1,
  .right, 672)) else (some (0, .right, 584), some (1, .right, 651))))) else (if q < 589 then
  (if q < 587 then (some (0, .right, 540), some (1, .right, 644)) else (if q < 588 then (some
  (0, .right, 586), some (1, .right, 653)) else (some (0, .right, 587), some (1, .right,
  651)))) else (if q < 590 then (some (0, .right, 648), some (1, .right, 561)) else (if q <
  591 then (some (0, .right, 586), some (1, .right, 589)) else (some (0, .right, 590), some
  (1, .right, 651)))))) else (if q < 598 then (if q < 595 then (if q < 593 then (some (0,
  .right, 586), some (1, .right, 574)) else (if q < 594 then (some (0, .right, 592), some (1,
  .right, 651)) else (some (0, .right, 541), some (1, .right, 635)))) else (if q < 596 then
  (some (0, .right, 594), some (1, .right, 638)) else (if q < 597 then (some (0, .right, 600),
  some (1, .right, 653)) else (some (0, .right, 596), some (1, .right, 651))))) else (if q <
  601 then (if q < 599 then (some (0, .right, 600), some (1, .right, 574)) else (if q < 600
  then (some (0, .right, 598), some (1, .right, 651)) else (some (0, .right, 541), some (1,
  .right, 644)))) else (if q < 602 then (some (0, .right, 560), some (1, .right, 648)) else
  (if q < 603 then (some (0, .right, 600), some (1, .right, 601)) else (some (0, .right, 602),
  some (1, .right, 651)))))))) else (if q < 627 then (if q < 615 then (if q < 609 then (if q <
  606 then (if q < 605 then (some (0, .right, 536), some (1, .right, 635)) else (some (0,
  .right, 604), some (1, .right, 638))) else (if q < 607 then (some (0, .right, 608), some (1,
  .right, 667)) else (if q < 608 then (some (0, .right, 606), some (1, .right, 651)) else
  (some (0, .right, 536), some (1, .right, 644))))) else (if q < 612 then (if q < 610 then
  (some (0, .right, 608), some (1, .right, 653)) else (if q < 611 then (some (0, .right, 609),
  some (1, .right, 651)) else (some (0, .right, 608), some (1, .right, 574)))) else (if q <
  613 then (some (0, .right, 611), some (1, .right, 651)) else (if q < 614 then (some (0,
  .right, 608), some (1, .right, 562)) else (some (0, .right, 613), some (1, .right, 651))))))
  else (if q < 621 then (if q < 618 then (if q < 616 then (some (0, .right, 537), some (1,
  .right, 635)) else (if q < 617 then (some (0, .right, 615), some (1, .right, 638)) else
  (some (0, .right, 537), some (1, .right, 644)))) else (if q < 619 then (some (0, .right,
  617), some (1, .right, 648)) else (if q < 620 then (some (0, .right, 618), some (1, .right,
  651)) else (some (0, .right, 617), some (1, .right, 656))))) else (if q < 624 then (if q <
  622 then (some (0, .right, 620), some (1, .right, 651)) else (if q < 623 then (some (0,
  .right, 617), some (1, .right, 574)) else (some (0, .right, 622), some (1, .right, 651))))
  else (if q < 625 then (some (0, .right, 544), some (1, .right, 635)) else (if q < 626 then
  (some (0, .right, 624), some (1, .right, 638)) else (some (0, .right, 648), some (1, .right,
  562))))))) else (if q < 639 then (if q < 633 then (if q < 630 then (if q < 628 then (some
  (0, .right, 629), some (1, .right, 626)) else (if q < 629 then (some (0, .right, 627), some
  (1, .right, 651)) else (some (0, .right, 544), some (1, .right, 644)))) else (if q < 631
  then (some (0, .right, 629), some (1, .right, 563)) else (if q < 632 then (some (0, .right,
  630), some (1, .right, 651)) else (some (0, .left, 633), some (1, .left, 633))))) else (if q
  < 636 then (if q < 634 then (some (0, .left, 634), some (0, .left, 634)) else (if q < 635
  then (some (0, .left, 14), some (0, .left, 14)) else (some (0, .left, 636), some (1, .left,
  636)))) else (if q < 637 then (some (1, .left, 11), some (1, .left, 11)) else (if q < 638
  then (some (0, .right, 534), some (1, .right, 635)) else (some (0, .right, 632), some (1,
  .right, 525)))))) else (if q < 645 then (if q < 642 then (if q < 640 then (some (0, .right,
  637), some (1, .right, 638)) else (if q < 641 then (some (0, .left, 641), some (1, .left,
  641)) else (some (0, .left, 642), some (0, .left, 642)))) else (if q < 643 then (some (0,
  .left, 643), some (0, .left, 643)) else (if q < 644 then (some (0, .left, 16), some (0,
  .left, 16)) else (some (0, .left, 645), some (1, .left, 645))))) else (if q < 648 then (if q
  < 646 then (some (1, .left, 646), some (1, .left, 646)) else (if q < 647 then (some (0,
  .left, 15), some (0, .left, 15)) else (some (0, .right, 534), some (1, .right, 644)))) else
  (if q < 649 then (some (0, .right, 558), some (1, .right, 648)) else (if q < 650 then (some
  (0, .right, 647), some (1, .right, 648)) else (some (0, .right, 640), some (1, .right,
  525)))))))))

def refRow7 (q : Nat) : Option (Fin 2 × Dir × Fin 744) × Option (Fin 2 × Dir × Fin 744) :=
  (if q < 697 then (if q < 674 then (if q < 662 then (if q < 656 then (if q < 653 then (if q <
  652 then (some (0, .right, 650), some (1, .right, 524)) else (some (0, .right, 649), some
  (1, .right, 651))) else (if q < 654 then (some (0, .right, 648), some (1, .right, 558)) else
  (if q < 655 then (some (0, .right, 647), some (1, .right, 653)) else (some (0, .right, 654),
  some (1, .right, 651))))) else (if q < 659 then (if q < 657 then (some (0, .right, 648),
  some (1, .right, 560)) else (if q < 658 then (some (0, .right, 647), some (1, .right, 656))
  else (some (0, .right, 657), some (1, .right, 651)))) else (if q < 660 then (some (0,
  .right, 561), some (1, .right, 563)) else (if q < 661 then (some (0, .right, 647), some (1,
  .right, 659)) else (some (0, .right, 660), some (1, .right, 651)))))) else (if q < 668 then
  (if q < 665 then (if q < 663 then (some (0, .right, 647), some (1, .right, 563)) else (if q
  < 664 then (some (0, .right, 662), some (1, .right, 651)) else (some (0, .right, 549), some
  (1, .right, 635)))) else (if q < 666 then (some (0, .right, 664), some (1, .right, 638))
  else (if q < 667 then (some (0, .right, 549), some (1, .right, 644)) else (some (0, .right,
  558), some (1, .right, 560))))) else (if q < 671 then (if q < 669 then (some (0, .right,
  666), some (1, .right, 667)) else (if q < 670 then (some (0, .right, 668), some (1, .right,
  651)) else (some (0, .right, 680), some (1, .right, 648)))) else (if q < 672 then (some (0,
  .right, 670), some (1, .right, 651)) else (if q < 673 then (some (0, .right, 558), some (1,
  .right, 561)) else (some (0, .right, 680), some (1, .right, 672))))))) else (if q < 685 then
  (if q < 679 then (if q < 676 then (if q < 675 then (some (0, .right, 673), some (1, .right,
  651)) else (some (0, .right, 680), some (1, .right, 574))) else (if q < 677 then (some (0,
  .right, 675), some (1, .right, 651)) else (if q < 678 then (some (0, .right, 560), some (1,
  .right, 562)) else (some (0, .right, 680), some (1, .right, 677))))) else (if q < 682 then
  (if q < 680 then (some (0, .right, 678), some (1, .right, 651)) else (if q < 681 then (some
  (0, .right, 535), some (1, .right, 644)) else (some (0, .right, 680), some (1, .right,
  659)))) else (if q < 683 then (some (0, .right, 681), some (1, .right, 651)) else (if q <
  684 then (some (0, .right, 542), some (1, .right, 635)) else (some (0, .right, 683), some
  (1, .right, 638)))))) else (if q < 691 then (if q < 688 then (if q < 686 then (some (0,
  .right, 692), some (1, .right, 701)) else (if q < 687 then (some (0, .right, 556), some (1,
  .right, 632)) else (some (0, .right, 692), some (1, .right, 686)))) else (if q < 689 then
  (some (0, .right, 692), some (1, .right, 705)) else (if q < 690 then (some (0, .right, 552),
  some (1, .right, 632)) else (some (0, .right, 692), some (1, .right, 689))))) else (if q <
  694 then (if q < 692 then (some (0, .right, 692), some (1, .right, 708)) else (if q < 693
  then (some (0, .right, 542), some (1, .right, 710)) else (some (0, .right, 559), some (1,
  .right, 632)))) else (if q < 695 then (some (0, .right, 692), some (1, .right, 693)) else
  (if q < 696 then (some (0, .right, 692), some (1, .right, 713)) else (some (0, .right, 692),
  some (1, .right, 742)))))))) else (if q < 720 then (if q < 708 then (if q < 702 then (if q <
  699 then (if q < 698 then (some (0, .right, 648), some (1, .right, 632)) else (some (0,
  .right, 692), some (1, .right, 697))) else (if q < 700 then (some (0, .right, 543), some (1,
  .right, 635)) else (if q < 701 then (some (0, .right, 699), some (1, .right, 638)) else
  (some (0, .right, 554), some (1, .right, 632))))) else (if q < 705 then (if q < 703 then
  (some (0, .right, 712), some (1, .right, 701)) else (if q < 704 then (some (0, .right, 555),
  some (1, .right, 632)) else (some (0, .right, 712), some (1, .right, 703)))) else (if q <
  706 then (some (0, .right, 557), some (1, .right, 632)) else (if q < 707 then (some (0,
  .right, 712), some (1, .right, 705)) else (some (0, .right, 712), some (1, .right, 689))))))
  else (if q < 714 then (if q < 711 then (if q < 709 then (some (0, .right, 553), some (1,
  .right, 632)) else (if q < 710 then (some (0, .right, 712), some (1, .right, 708)) else
  (some (0, .left, 711), some (1, .left, 711)))) else (if q < 712 then (some (0, .left, 646),
  some (0, .left, 646)) else (if q < 713 then (some (0, .right, 543), some (1, .right, 710))
  else (some (0, .right, 551), some (1, .right, 632))))) else (if q < 717 then (if q < 715
  then (some (0, .right, 712), some (1, .right, 713)) else (if q < 716 then (some (0, .right,
  712), some (1, .right, 725)) else (some (0, .right, 712), some (1, .right, 742)))) else (if
  q < 718 then (some (0, .right, 545), some (1, .right, 635)) else (if q < 719 then (some (0,
  .right, 717), some (1, .right, 638)) else (some (0, .right, 723), some (1, .right,
  686))))))) else (if q < 732 then (if q < 726 then (if q < 723 then (if q < 721 then (some
  (0, .right, 723), some (1, .right, 705)) else (if q < 722 then (some (0, .right, 723), some
  (1, .right, 689)) else (some (0, .right, 723), some (1, .right, 708)))) else (if q < 724
  then (some (0, .right, 545), some (1, .right, 710)) else (if q < 725 then (some (0, .right,
  723), some (1, .right, 713)) else (some (0, .right, 564), some (1, .right, 632))))) else (if
  q < 729 then (if q < 727 then (some (0, .right, 723), some (1, .right, 725)) else (if q <
  728 then (some (0, .right, 546), some (1, .right, 635)) else (some (0, .right, 727), some
  (1, .right, 638)))) else (if q < 730 then (some (0, .right, 731), some (1, .right, 703))
  else (if q < 731 then (some (0, .right, 731), some (1, .right, 686)) else (some (0, .right,
  546), some (1, .right, 710)))))) else (if q < 738 then (if q < 735 then (if q < 733 then
  (some (0, .right, 731), some (1, .right, 742)) else (if q < 734 then (some (0, .right, 547),
  some (1, .right, 635)) else (some (0, .right, 733), some (1, .right, 638)))) else (if q <
  736 then (some (0, .right, 736), some (1, .right, 689)) else (if q < 737 then (some (0,
  .right, 547), some (1, .right, 710)) else (some (0, .right, 736), some (1, .right, 693)))))
  else (if q < 741 then (if q < 739 then (some (0, .right, 736), some (1, .right, 742)) else
  (if q < 740 then (some (0, .right, 740), some (1, .right, 693)) else (some (0, .right, 548),
  some (1, .right, 710)))) else (if q < 742 then (some (0, .right, 740), some (1, .right,
  713)) else (if q < 743 then (some (0, .right, 188), some (1, .right, 632)) else (some (0,
  .right, 740), some (1, .right, 742)))))))))

/-- Fast logarithmic-depth transition lookup for `reference` (`riemann_744`). -/
def refTrans (q : Fin 744) (b : Fin 2) : Option (Fin 2 × Dir × Fin 744) :=
  let row :=
    if q.val < 372 then
      if q.val < 186 then (if q.val < 93 then refRow0 q.val else refRow1 q.val)
      else (if q.val < 279 then refRow2 q.val else refRow3 q.val)
    else
      if q.val < 558 then (if q.val < 465 then refRow4 q.val else refRow5 q.val)
      else (if q.val < 651 then refRow6 q.val else refRow7 q.val)
  if b == 0 then row.1 else row.2

set_option maxRecDepth 8000 in
theorem refTrans_eq (q : Fin 744) (b : Fin 2) : reference.transition q b = refTrans q b := by
  revert q b; decide

/-!
## 1. `nSteps` and Symbolic Tape Primitives (`Tape.mkL`, `Tape.mk'`)
-/

/-- Bounded `n`-step execution of a Turing machine from configuration `c`. -/
def nSteps {K : ℕ} [NeZero K] (M : Machine K 2) : ℕ → Cfg K 2 → Option (Cfg K 2)
  | 0, c => some c
  | n + 1, c => (step M c).bind (nSteps M n)

@[simp]
theorem nSteps_zero {K : ℕ} [NeZero K] (M : Machine K 2) (c : Cfg K 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ {K : ℕ} [NeZero K] (M : Machine K 2) (n : ℕ) (c : Cfg K 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

theorem nSteps_add {K : ℕ} [NeZero K] {M : Machine K 2} (m n : ℕ) (c : Cfg K 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, nSteps_succ, nSteps_succ]
    cases step M c with
    | none => rfl
    | some c' => exact ih c'

theorem nSteps_bind_eq {K : ℕ} [NeZero K] {M : Machine K 2} {m n : ℕ} {c c₁ c₂ : Cfg K 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_nSteps {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c₁ c₂ : Cfg K 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps_succ, h₁, Option.bind_some, h₂]

theorem step_one {K : ℕ} [NeZero K] {M : Machine K 2} {c c₁ : Cfg K 2}
    (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps_succ, h]; rfl

theorem nSteps_reaches {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c' : Cfg K 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps_succ, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_eval_dom {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c c' : Cfg K 2}
    (h : nSteps M n c = some c') :
    (eval (step M) c).Dom ↔ (eval (step M) c').Dom := by
  rw [reaches_eval' (nSteps_reaches h)]

theorem nSteps_reaches₁ {K : ℕ} [NeZero K] {M : Machine K 2} {n : ℕ} {c₁ c₂ : Cfg K 2}
    (hn : 1 ≤ n) (h : nSteps M n c₁ = some c₂) :
    Reaches₁ (step M) c₁ c₂ := by
  cases n with
  | zero => omega
  | succ n =>
    rw [nSteps_succ] at h
    rcases hs : step M c₁ with _ | c'
    · rw [hs] at h; cases h
    · rw [hs, Option.bind_some] at h
      exact Relation.TransGen.head' hs (nSteps_reaches h)

theorem nSteps_of_halt {K : ℕ} [NeZero K] {M : Machine K 2} {c : Cfg K 2}
    (h : step M c = none) {k : ℕ} (hk : 1 ≤ k) :
    nSteps M k c = none := by
  cases k with
  | zero => omega
  | succ k => simp [nSteps_succ, h]

theorem mem_eval_iff_nSteps {K : ℕ} [NeZero K] {M : Machine K 2} {c₀ ch : Cfg K 2} :
    ch ∈ eval (step M) c₀ ↔ ∃ N, nSteps M N c₀ = some ch ∧ step M ch = none := by
  constructor
  · intro h
    refine evalInduction' h fun a ha ih => ?_
    rcases hs : step M a with _ | a'
    · have hmem : a ∈ eval (step M) a :=
        mem_eval'.mpr ⟨Relation.ReflTransGen.refl, hs⟩
      have heq : ch = a := Part.mem_unique ha hmem
      subst heq
      exact ⟨0, rfl, hs⟩
    · obtain ⟨N, hN, hnone⟩ := ih a' hs
      exact ⟨N + 1, by rw [nSteps_succ, hs, Option.bind_some, hN], hnone⟩
  · rintro ⟨N, hN, hnone⟩
    exact mem_eval'.mpr ⟨nSteps_reaches hN, hnone⟩

theorem mk_append_replicate_zero (l : List (Fin 2)) (n : ℕ) :
    ListBlank.mk (l ++ List.replicate n 0) = ListBlank.mk l :=
  ListBlank.mk_append_replicate_default l n

theorem default_eq_mk_nil : (default : ListBlank (Fin 2)) = ListBlank.mk [] := rfl

@[simp]
theorem default_cons_zero : ListBlank.cons 0 (default : ListBlank (Fin 2)) = default := by
  change ListBlank.mk [0] = ListBlank.mk []
  exact mk_append_replicate_zero [] 1

theorem append_replicate_zero_default (n : ℕ) :
    ListBlank.append (List.replicate n 0) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, ListBlank.append, ih, default_cons_zero]

theorem fin2_cases (a : Fin 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- Tape constructor with the head taken from the left half-tape `L`. -/
def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

@[simp]
theorem Tape.mkL_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons a) R = ⟨a, L, R⟩ := by
  simp [Tape.mkL]

@[simp]
theorem Tape.mk'_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mk' L (R.cons a) = ⟨a, L, R⟩ := by
  simp [Tape.mk']

theorem Tape.mkL_default (R : ListBlank (Fin 2)) :
    Tape.mkL default R = Tape.mk' default (R.cons 0) := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  conv_lhs => rw [hdef]
  rw [Tape.mkL_cons, Tape.mk'_cons]

theorem step_mkL_left {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, refTrans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, refTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mkL_left_any {q q' : Fin 744}
    (h0 : refTrans q 0 = some (0, .left, q'))
    (h1 : refTrans q 1 = some (1, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons a)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem step_mk'_right_any {q q' : Fin 744}
    (h0 : refTrans q 0 = some (0, .right, q'))
    (h1 : refTrans q 1 = some (1, .right, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons a) R⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mk'_right h0 L R
  · exact step_mk'_right h1 L R

theorem step_mkL_left_const {q q' : Fin 744} {b : Fin 2}
    (h0 : refTrans q 0 = some (b, .left, q'))
    (h1 : refTrans q 1 = some (b, .left, q'))
    (a : Fin 2) (L R : ListBlank (Fin 2)) :
    step reference ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  rcases fin2_cases a with rfl | rfl
  · exact step_mkL_left h0 L R
  · exact step_mkL_left h1 L R

theorem append_replicate_cons (k : ℕ) (b : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate k b) (L.cons b) =
      ListBlank.append (List.replicate (k + 1) b) L := by
  rw [List.replicate_succ', ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem append_cons_snoc (l : List (Fin 2)) (a : Fin 2) (L : ListBlank (Fin 2)) :
    ListBlank.append l (L.cons a) = ListBlank.append (l ++ [a]) L := by
  rw [ListBlank.append_assoc, ListBlank.append, ListBlank.append]

theorem append_reverse_cons (a : Fin 2) (l : List (Fin 2)) (L : ListBlank (Fin 2)) :
    ListBlank.append l.reverse (L.cons a) = ListBlank.append (a :: l).reverse L := by
  rw [List.reverse_cons, append_cons_snoc]

theorem move_right_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 744}
    (h0 : refTrans q 0 = some (0, .right, q))
    (h1 : refTrans q 1 = some (1, .right, q)) :
    nSteps reference l.length ⟨q, Tape.mk' L (ListBlank.append l R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append l.reverse L) R⟩ := by
  induction l generalizing L with
  | nil => rfl
  | cons a l ih =>
    have hstep : step reference ⟨q, Tape.mk' L ((ListBlank.append l R).cons a)⟩ =
        some ⟨q, Tape.mk' (L.cons a) (ListBlank.append l R)⟩ :=
      step_mk'_right_any h0 h1 a L (ListBlank.append l R)
    rw [List.length_cons, ListBlank.append, step_nSteps hstep (ih (L.cons a)), append_reverse_cons]

theorem move_left_append (l : List (Fin 2)) (L R : ListBlank (Fin 2))
    {q : Fin 744}
    (h0 : refTrans q 0 = some (0, .left, q))
    (h1 : refTrans q 1 = some (1, .left, q)) :
    nSteps reference l.length ⟨q, Tape.mkL (ListBlank.append l.reverse L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append l R)⟩ := by
  induction l using List.reverseRecOn generalizing R with
  | nil => rfl
  | append_singleton l a ih =>
    rw [List.reverse_append, List.reverse_singleton, List.singleton_append,
      ListBlank.append, List.length_append, List.length_singleton]
    have hstep : step reference ⟨q, Tape.mkL ((ListBlank.append l.reverse L).cons a) R⟩ =
        some ⟨q, Tape.mkL (ListBlank.append l.reverse L) (R.cons a)⟩ :=
      step_mkL_left_any h0 h1 a (ListBlank.append l.reverse L) R
    rw [step_nSteps hstep (ih (R.cons a)), append_cons_snoc]

theorem nSteps_mkL_left_scan {q : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 744} {a b : Fin 2}
    (h : refTrans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-!
## 2. Unary Register Encodings & `entryCfg`
-/

/-- Unary encoding of a single register value `r : ℕ`: `1^{r+1} ++ [0]`. -/
def encodeReg (r : ℕ) : List (Fin 2) :=
  List.replicate (r + 1) 1 ++ [0]

@[simp]
theorem encodeReg_length (r : ℕ) : (encodeReg r).length = r + 2 := by
  simp [encodeReg]

theorem encodeReg_reverse (r : ℕ) :
    (encodeReg r).reverse = 0 :: List.replicate (r + 1) 1 := by
  simp [encodeReg]

theorem append_encodeReg_reverse (r : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append (encodeReg r).reverse L =
      (ListBlank.append (List.replicate (r + 1) 1) L).cons 0 := by
  rw [encodeReg_reverse, ListBlank.append]

theorem append_encodeReg (r : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (encodeReg r) R =
      ListBlank.append (List.replicate (r + 1) 1) (R.cons 0) := by
  rw [encodeReg, ← append_cons_snoc]

/-- Unary encoding of a bank of registers `regs : List ℕ`. -/
def encodeRegs : List ℕ → List (Fin 2)
  | [] => []
  | r :: rs => encodeReg r ++ encodeRegs rs

@[simp]
theorem encodeRegs_nil : encodeRegs [] = [] := rfl

@[simp]
theorem encodeRegs_cons (r : ℕ) (rs : List ℕ) :
    encodeRegs (r :: rs) = encodeReg r ++ encodeRegs rs := rfl

theorem encodeRegs_append (rs₁ rs₂ : List ℕ) :
    encodeRegs (rs₁ ++ rs₂) = encodeRegs rs₁ ++ encodeRegs rs₂ := by
  induction rs₁ with
  | nil => rfl
  | cons r rs₁ ih => simp [ih, List.append_assoc]

/-- The right half-tape encoding `regs` followed by blank zeros. -/
def regsTape (regs : List ℕ) : ListBlank (Fin 2) :=
  ListBlank.append (encodeRegs regs) default

@[simp]
theorem regsTape_nil : regsTape [] = default := rfl

theorem regsTape_cons (r : ℕ) (rs : List ℕ) :
    regsTape (r :: rs) = ListBlank.append (encodeReg r) (regsTape rs) := by
  simp [regsTape, ListBlank.append_assoc]

theorem regsTape_append (rs₁ rs₂ : List ℕ) :
    regsTape (rs₁ ++ rs₂) = ListBlank.append (encodeRegs rs₁) (regsTape rs₂) := by
  simp [regsTape, encodeRegs_append, ListBlank.append_assoc]

/-- Big-endian `k`-bit binary representation of `pc`. -/
def pcBits : ℕ → ℕ → List (Fin 2)
  | 0, _ => []
  | k + 1, pc => (if pc.testBit k then 1 else 0) :: pcBits k pc

@[simp]
theorem pcBits_zero (pc : ℕ) : pcBits 0 pc = [] := rfl

@[simp]
theorem pcBits_succ (k pc : ℕ) :
    pcBits (k + 1) pc = (if pc.testBit k then 1 else 0) :: pcBits k pc := rfl

@[simp]
theorem pcBits_length (k pc : ℕ) : (pcBits k pc).length = k := by
  induction k <;> simp [*]

/-- Canonical entry configuration at `!ENTRY` (State `0`), where the tape head sits on the `0`
immediately to the left of the 11-bit big-endian PC, followed by the `[0, 0]` fence and `regs`. -/
def entryCfg (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨0, Tape.mkL default (ListBlank.append (pcBits 11 pc ++ [0, 0]) (regsTape regs))⟩

/-- Configuration at `main()[]` (State `523`), 1 step after `entryCfg`, where the tape head sits
on the MSB (`bit 10`) of the 11-bit PC. -/
def mainCfg (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨523, Tape.mk' default (ListBlank.append (pcBits 11 pc ++ [0, 0]) (regsTape regs))⟩

/-- Configuration immediately after the 11-bit PC decision tree, with the tape head on the
first `0` of the `[0, 0]` fence. -/
def postPcCfg (q : Fin 744) (pc : ℕ) (regs : List ℕ) : Cfg 744 2 :=
  ⟨q, Tape.mk' (ListBlank.append (pcBits 11 pc).reverse default) ((regsTape regs).cons 0 |>.cons 0)⟩

theorem step_entryCfg (pc : ℕ) (regs : List ℕ) :
    step reference (entryCfg pc regs) = some (mainCfg pc regs) := by
  unfold entryCfg mainCfg
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  conv_lhs => rw [hdef]
  rw [step_mkL_right (by rfl), default_cons_zero]

theorem entryCfg_zero_nil : entryCfg 0 [] = init := by
  unfold entryCfg init
  have h13 : pcBits 11 0 ++ [0, 0] = List.replicate 13 0 := by decide
  rw [h13, regsTape_nil, append_replicate_zero_default, Tape.mkL_default, default_cons_zero]
  rfl

/-!
## 3. Return Scan Gadgets (`return.0/1` = States `565`/`566`, `return2.0/1` = States `567`/`568`)
-/

/-- State `566` (`return.1`) scans left across a single unary register `encodeReg r` in `r + 2`
steps, landing back in State `566`. -/
theorem return1_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨566, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨566, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨566, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨565, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨565, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨566, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 566) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `566` (`return.1`) scans left across any bank of registers `regs` in
`(encodeRegs regs).length` steps. -/
theorem return1_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨566, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return1_scan_reg, ListBlank.append_assoc]

/-- State `566` (`return.1`) scans left across `regs` and the `[0, 0]` fence to reach
State `9` (`dispatch.0.carry`). -/
theorem return1_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨9, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return1_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step reference
      ⟨566, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨565, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨565, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨9, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- State `568` (`return2.1`) scans left across a single unary register `encodeReg r` in `r + 2`
steps, landing back in State `568`. -/
theorem return2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨568, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨568, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨568, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨567, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨567, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨568, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 568) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

/-- State `568` (`return2.1`) scans left across any bank of registers `regs` in
`(encodeRegs regs).length` steps. -/
theorem return2_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨568, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return2_scan_reg, ListBlank.append_assoc]

/-- State `568` (`return2.1`) scans left across `regs` and the `[0, 0]` fence to reach
State `524` (`nextstate_2`). -/
theorem return2_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨524, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return2_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step reference
      ⟨568, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨567, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step reference
      ⟨567, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨524, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-!
## 4. PC Carry/Return Chain (`States 9..29, 12, 13 → 0`)
-/

/-- The `dispatch.k` / `dispatch.k.carry` states for `0 ≤ order ≤ 10`, plus `0` (`!ENTRY`)
at `order = 11`. -/
def dispatchState (order : ℕ) (carry : Bool) : Fin 744 :=
  match order, carry with
  | 0, _ => 9
  | 1, false => 10
  | 1, true => 11
  | 2, false => 14
  | 2, true => 15
  | 3, false => 16
  | 3, true => 17
  | 4, false => 18
  | 4, true => 19
  | 5, false => 20
  | 5, true => 21
  | 6, false => 22
  | 6, true => 23
  | 7, false => 24
  | 7, true => 25
  | 8, false => 26
  | 8, true => 27
  | 9, false => 28
  | 9, true => 29
  | 10, false => 12
  | 10, true => 13
  | _, _ => 0

theorem testBit_zero_eq (m : ℕ) :
    (if m.testBit 0 then (1 : Fin 2) else 0) = if m % 2 = 1 then 1 else 0 := by
  rw [Nat.testBit_zero]
  by_cases h : m % 2 = 1 <;> simp [h]

theorem testBit_succ_div (m k : ℕ) : m.testBit (k + 1) = (m / 2).testBit k := by
  rw [Nat.testBit_succ]

theorem pcBits_succ_snoc (k m : ℕ) :
    pcBits (k + 1) m = pcBits k (m / 2) ++ [if m.testBit 0 then 1 else 0] := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [pcBits_succ, ih m, ← List.cons_append, testBit_succ_div]
    rfl

theorem pcBits_succ_reverse (k m : ℕ) :
    (pcBits (k + 1) m).reverse =
      (if m.testBit 0 then 1 else 0) :: (pcBits k (m / 2)).reverse := by
  rw [pcBits_succ_snoc, List.reverse_append, List.reverse_singleton, List.singleton_append]

theorem append_pcBits_succ_reverse (k m : ℕ) (L : ListBlank (Fin 2)) :
    ListBlank.append (pcBits (k + 1) m).reverse L =
      (ListBlank.append (pcBits k (m / 2)).reverse L).cons (if m.testBit 0 then 1 else 0) := by
  rw [pcBits_succ_reverse, ListBlank.append]

theorem append_pcBits_succ_snoc (k m : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (pcBits k (m / 2)) (R.cons (if m.testBit 0 then 1 else 0)) =
      ListBlank.append (pcBits (k + 1) m) R := by
  rw [append_cons_snoc, ← pcBits_succ_snoc]

theorem testBit_div_pow (m b a : ℕ) : (m / 2 ^ b).testBit a = m.testBit (a + b) := by
  induction b generalizing m a with
  | zero => simp
  | succ b ih =>
    rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul, ← testBit_succ_div, ih m (a + 1),
      Nat.add_right_comm, Nat.add_assoc]

theorem pcBits_add (a b pc : ℕ) :
    pcBits (a + b) pc = pcBits a (pc / 2 ^ b) ++ pcBits b pc := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_add, pcBits_succ, pcBits_succ, ih, List.cons_append, testBit_div_pow]


theorem dispatchState_trans_false_0 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d false) 0 = some (0, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_false_1 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d false) 1 = some (1, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_true_0 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d true) 0 = some (1, .left, dispatchState (d + 1) false) := by
  revert d hd; decide

theorem dispatchState_trans_true_1 (d : ℕ) (hd : d ≤ 10) :
    d = 0 ∨ refTrans (dispatchState d true) 1 = some (0, .left, dispatchState (d + 1) true) := by
  revert d hd; decide

/-- One step in the PC carry chain at bit `0` of `m`: consumes the LSB of `m` from `L`,
pushes the LSB of `m + c.toNat` onto `R`, and updates the carry for `m / 2`. -/
theorem step_dispatch_bit (d : ℕ) (hd1 : 1 ≤ d) (hd10 : d ≤ 10) (c : Bool)
    (m : ℕ) (L R : ListBlank (Fin 2)) :
    let c' := c && decide (m % 2 = 1)
    step reference
      ⟨dispatchState d c,
        Tape.mkL (L.cons (if m.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState (d + 1) c',
        Tape.mkL L (R.cons (if (m + c.toNat).testBit 0 then 1 else 0))⟩ := by
  intro c'
  have hd0 : d ≠ 0 := by omega
  have hf0 := (dispatchState_trans_false_0 d hd10).resolve_left hd0
  have hf1 := (dispatchState_trans_false_1 d hd10).resolve_left hd0
  have ht0 := (dispatchState_trans_true_0 d hd10).resolve_left hd0
  have ht1 := (dispatchState_trans_true_1 d hd10).resolve_left hd0
  rw [testBit_zero_eq m, testBit_zero_eq (m + c.toNat)]
  cases c with
  | false =>
    have hc' : c' = false := rfl
    rw [hc']
    by_cases hm : m % 2 = 1
    · simp only [Bool.toNat_false, Nat.add_zero, hm, ↓reduceIte]
      exact step_mkL_left hf1 L R
    · simp only [Bool.toNat_false, Nat.add_zero, hm, ↓reduceIte]
      exact step_mkL_left hf0 L R
  | true =>
    by_cases hm : m % 2 = 1
    · have hm1 : ¬((m + 1) % 2 = 1) := by omega
      have hc' : c' = true := by simp [c', hm]
      rw [hc']
      simp only [Bool.toNat_true, hm, ↓reduceIte, hm1]
      exact step_mkL_left ht1 L R
    · have hm1 : (m + 1) % 2 = 1 := by omega
      have hc' : c' = false := by simp [c', hm]
      rw [hc']
      simp only [Bool.toNat_true, hm, ↓reduceIte, hm1]
      exact step_mkL_left ht0 L R

theorem div2_add_carry (m : ℕ) (c : Bool) :
    (m + c.toNat) / 2 = m / 2 + (c && decide (m % 2 = 1)).toNat := by
  cases c <;> by_cases hm : m % 2 = 1 <;> simp [hm] <;> omega

/-- General PC carry chain theorem: starting at `dispatchState (11 - k) c` with `k` bits of `m`
reversed on the left tape (`1 ≤ k ≤ 10`), `reference` runs for `k` steps to reach State `0`
(`!ENTRY`) with `pcBits k (m + c.toNat)` prepended to `R`. -/
theorem dispatch_chain (k : ℕ) (hk1 : 1 ≤ k) (hk10 : k ≤ 10) (c : Bool) (m : ℕ)
    (L R : ListBlank (Fin 2)) :
    nSteps reference k
      ⟨dispatchState (11 - k) c, Tape.mkL (ListBlank.append (pcBits k m).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits k (m + c.toNat)) R)⟩ := by
  induction k generalizing c m R with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · subst hk0
      rw [append_pcBits_succ_reverse, pcBits_zero, List.reverse_nil, ListBlank.append]
      have hstep := step_dispatch_bit 10 (by decide) (by decide) c m L R
      simpa [dispatchState, append_pcBits_succ_snoc] using step_one hstep
    · have hk_ge : 1 ≤ k := by omega
      have hk_le : k ≤ 10 := by omega
      have hd1 : 1 ≤ 11 - (k + 1) := by omega
      have hd10 : 11 - (k + 1) ≤ 10 := by omega
      have hd_succ : 11 - (k + 1) + 1 = 11 - k := by omega
      rw [append_pcBits_succ_reverse]
      have hstep := step_dispatch_bit (11 - (k + 1)) hd1 hd10 c m
        (ListBlank.append (pcBits k (m / 2)).reverse L) R
      rw [hd_succ] at hstep
      have hrest := ih hk_ge hk_le (c && decide (m % 2 = 1)) (m / 2)
        (R.cons (if (m + c.toNat).testBit 0 then 1 else 0))
      rw [← div2_add_carry, append_pcBits_succ_snoc] at hrest
      exact step_nSteps hstep hrest

/-- Full 11-bit PC increment from State `9` (`dispatch.0.carry`). -/
theorem dispatch_from_0_carry (pc : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference 11
      ⟨9, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits 11 (pc + 1)) R)⟩ := by
  rw [append_pcBits_succ_reverse 10 pc L]
  have h1 : step reference
      ⟨9, Tape.mkL ((ListBlank.append (pcBits 10 (pc / 2)).reverse L).cons
        (if pc.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState 1 (true && decide (pc % 2 = 1)),
        Tape.mkL (ListBlank.append (pcBits 10 (pc / 2)).reverse L)
          (R.cons (if (pc + 1).testBit 0 then 1 else 0))⟩ := by
    rw [testBit_zero_eq pc, testBit_zero_eq (pc + 1)]
    by_cases hm : pc % 2 = 1
    · have hm1 : ¬((pc + 1) % 2 = 1) := by omega
      simp only [hm, decide_true, Bool.true_and, ↓reduceIte, hm1]
      exact step_mkL_left (by rfl) _ _
    · have hm1 : (pc + 1) % 2 = 1 := by omega
      simp only [hm, decide_false, Bool.true_and, ↓reduceIte, hm1]
      exact step_mkL_left (by rfl) _ _
  have hrest := dispatch_chain 10 (by decide) (by decide)
    (true && decide (pc % 2 = 1)) (pc / 2) L (R.cons (if (pc + 1).testBit 0 then 1 else 0))
  have hdiv := div2_add_carry pc true
  simp only [Bool.toNat_true] at hdiv
  rw [← hdiv, append_pcBits_succ_snoc] at hrest
  exact step_nSteps h1 hrest

/-- Full 11-bit PC `+ 2` increment from State `524` (`nextstate_2`). -/
theorem dispatch_from_524 (pc : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference 11
      ⟨524, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (pcBits 11 (pc + 2)) R)⟩ := by
  rw [append_pcBits_succ_reverse 10 pc L]
  have h1 : step reference
      ⟨524, Tape.mkL ((ListBlank.append (pcBits 10 (pc / 2)).reverse L).cons
        (if pc.testBit 0 then 1 else 0)) R⟩ =
      some ⟨dispatchState 1 true,
        Tape.mkL (ListBlank.append (pcBits 10 (pc / 2)).reverse L)
          (R.cons (if pc.testBit 0 then 1 else 0))⟩ :=
    step_mkL_left_any (by rfl) (by rfl) _ _ _
  have hbit0 : (if (pc + 2).testBit 0 then (1 : Fin 2) else 0) = if pc.testBit 0 then 1 else 0 := by
    rw [testBit_zero_eq, testBit_zero_eq]
    have hmod : (pc + 2) % 2 = pc % 2 := by omega
    rw [hmod]
  have hdiv2 : (pc + 2) / 2 = pc / 2 + 1 := by omega
  have hsnoc := append_pcBits_succ_snoc 10 (pc + 2) R
  rw [hdiv2, hbit0] at hsnoc
  have hrest := dispatch_chain 10 (by decide) (by decide)
    true (pc / 2) L (R.cons (if pc.testBit 0 then 1 else 0))
  simp only [Bool.toNat_true] at hrest
  rw [hsnoc] at hrest
  exact step_nSteps h1 hrest

theorem dispatch_from_9_entryCfg (pc : ℕ) (regs : List ℕ) :
    nSteps reference 11
      ⟨9, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse default)
        ((regsTape regs).cons 0 |>.cons 0)⟩ =
      some (entryCfg (pc + 1) regs) := by
  have h := dispatch_from_0_carry pc default ((regsTape regs).cons 0 |>.cons 0)
  simpa [entryCfg, ListBlank.append_assoc] using h

theorem dispatch_from_524_entryCfg (pc : ℕ) (regs : List ℕ) :
    nSteps reference 11
      ⟨524, Tape.mkL (ListBlank.append (pcBits 11 pc).reverse default)
        ((regsTape regs).cons 0 |>.cons 0)⟩ =
      some (entryCfg (pc + 2) regs) := by
  have h := dispatch_from_524 pc default ((regsTape regs).cons 0 |>.cons 0)
  simpa [entryCfg, ListBlank.append_assoc] using h

/-!
## 5. Primitive Register Operations (`reg_init`, `reg_incr`, `reg_decr`)
-/

/-!
### 5.1 `reg_init` (States `32..35`)
-/

theorem init_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (r + 2)
      ⟨34, Tape.mk' L (ListBlank.append (encodeReg r) R)⟩ =
      some ⟨34, Tape.mk' (ListBlank.append (encodeReg r).reverse L) R⟩ := by
  rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨34, Tape.mk' L ((ListBlank.append (List.replicate r 1) (R.cons 0)).cons 1)⟩ =
      some ⟨35, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate r 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 35) (a := 1) (b := 1) (by rfl) r (L.cons 1) (R.cons 0)
  have h2 : step reference
      ⟨35, Tape.mk' (ListBlank.append (List.replicate r 1) (L.cons 1)) (R.cons 0)⟩ =
      some ⟨34, Tape.mk' ((ListBlank.append (List.replicate r 1) (L.cons 1)).cons 0) R⟩ :=
    step_mk'_right (by rfl) _ _
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  rw [append_replicate_cons, ← append_encodeReg_reverse] at hcomb
  simpa [Nat.add_assoc] using hcomb

theorem init_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (encodeRegs regs).length
      ⟨34, Tape.mk' L (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨34, Tape.mk' (ListBlank.append (encodeRegs regs).reverse L) R⟩ := by
  induction regs generalizing L with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.length_append, ListBlank.append_assoc, nSteps_add,
      encodeReg_length, init_scan_reg, Option.bind_some, ih,
      List.reverse_append, ListBlank.append_assoc]

/-- `reg_init` gadget evaluation: from `postPcCfg 32 pc regs`, `reference` appends a new
zero-initialized register (`regs ++ [0]`) and advances to `entryCfg (pc + 1) (regs ++ [0])`. -/
theorem reg_init_eval (pc : ℕ) (regs : List ℕ) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg 32 pc regs) =
      some (entryCfg (pc + 1) (regs ++ [0])) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  have h1 : step reference (postPcCfg 32 pc regs) =
      some ⟨33, Tape.mk' (L_pc.cons 0) ((regsTape regs).cons 0)⟩ :=
    step_mk'_right (by rfl) _ _
  have h2 : step reference ⟨33, Tape.mk' (L_pc.cons 0) ((regsTape regs).cons 0)⟩ =
      some ⟨34, Tape.mk' ((L_pc.cons 0).cons 0) (regsTape regs)⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := init_scan_regs regs ((L_pc.cons 0).cons 0) default
  have h3 : step reference
      ⟨34, Tape.mk' (ListBlank.append (encodeRegs regs).reverse ((L_pc.cons 0).cons 0)) default⟩ =
      some ⟨566, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L_pc.cons 0).cons 0))
        (regsTape [0])⟩ := by
    have hdef : (default : ListBlank (Fin 2)) =
        ListBlank.cons 0 (ListBlank.cons 0 default) := by simp
    conv_lhs => rw [hdef]
    exact step_mk'_left (by rfl) _ (ListBlank.cons 0 default)
  have hret := return1_scan_fence regs L_pc (regsTape [0])
  rw [← regsTape_append] at hret
  have hdisp := dispatch_from_9_entryCfg pc (regs ++ [0])
  have htotal := step_nSteps h1 (step_nSteps h2
    (nSteps_bind_eq hscan (step_nSteps h3 (nSteps_bind_eq hret hdisp))))
  exact ⟨_, by omega, htotal⟩

/-!
### 5.2 `reg_incr` (`regIncrState k`, States `30, 31`)
-/

/-- Entry state for incrementing register `k` (`0 ≤ k < 16`). -/
def regIncrState : ℕ → Fin 744
  | 0 => 551
  | 1 => 188
  | 2 => 558
  | 3 => 648
  | 4 => 559
  | 5 => 560
  | 6 => 561
  | 7 => 562
  | 8 => 563
  | 9 => 564
  | 10 => 552
  | 11 => 553
  | 12 => 554
  | 13 => 555
  | 14 => 556
  | 15 => 557
  | _ => 550

/-- Chain of `reg_incr` states where `0 ↦ 550` (`reg_incr(-1)`) and `k + 1 ↦ regIncrState k`. -/
def regIncrChain : ℕ → Fin 744
  | 0 => 550
  | k + 1 => regIncrState k

theorem regIncrChain_trans_one (m : ℕ) (hm : m ≤ 16) :
    refTrans (regIncrChain m) 1 = some (1, .right, regIncrChain m) := by
  revert m hm; decide

theorem regIncrChain_trans_zero (m : ℕ) (hm : m < 16) :
    refTrans (regIncrChain (m + 1)) 0 = some (0, .right, regIncrChain m) := by
  revert m hm; decide

theorem regIncrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 15)
    (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs pref).length + 1)
      ⟨regIncrChain pref.length, Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨31, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length < 16 := by omega
    have hrs_le : rs.length ≤ 15 := by omega
    have h0 : step reference
        ⟨regIncrChain (rs.length + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨regIncrChain rs.length,
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (regIncrChain_trans_zero rs.length hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (regIncrChain_trans_one rs.length (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Rightward shift and return scan in States `30`/`31` (`inc.shift_0`/`inc.shift_1`). -/
theorem inc_shift_eval (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨30, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨566, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨30, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨565, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have h2 : step reference
        ⟨565, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ =
        some ⟨566, Tape.mkL (ListBlank.append (List.replicate m 1) L_prev)
          (ListBlank.cons 1 (ListBlank.cons 0 default))⟩ :=
      step_mkL_left (by rfl) _ _
    have hscan := nSteps_mkL_left_scan (q := 566) (a := 1) (b := 1) (by rfl)
      m L_prev (ListBlank.cons 1 (ListBlank.cons 0 default))
    have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
    rw [append_replicate_cons, ← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨30, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨31, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 31) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨31, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨30, Tape.mk' ((ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)).cons 1) (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcons1 : (ListBlank.append (List.replicate r 1)
        (ListBlank.append (encodeReg m).reverse L_prev)).cons 1 =
        ListBlank.append (List.replicate (r + 1) 1)
          (ListBlank.append (encodeReg m).reverse L_prev) := by
      rw [List.replicate_succ, ListBlank.append]
    rw [hcons1] at h2
    obtain ⟨s, hs1, hs⟩ := ih r (ListBlank.append (encodeReg m).reverse L_prev)
    have hret := return1_scan_reg m L_prev (regsTape (r :: rs))
    rw [← regsTape_cons] at hret
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
      (step_nSteps h2 (nSteps_bind_eq hs hret)))
    exact ⟨_, by omega, hcomb⟩

theorem list_take_cons_drop (regs : List ℕ) (k : ℕ) (hk : k < regs.length) :
    regs.take k ++ regs[k] :: regs.drop (k + 1) = regs := by
  induction regs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp

theorem list_take_set_drop (regs : List ℕ) (k v : ℕ) (hk : k < regs.length) :
    regs.take k ++ v :: regs.drop (k + 1) = regs.set k v := by
  induction regs generalizing k with
  | nil => simp at hk
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hk
      simp only [List.take_succ_cons, List.drop_succ_cons, List.cons_append, List.set_cons_succ]
      congr 1
      exact ih k hk

/-- `reg_incr` gadget evaluation: from `postPcCfg (regIncrState k) pc regs` (`k < 16`,
`k < regs.length`), `reference` increments `regs[k]` by `1` and advances to
`entryCfg (pc + 1) (regs.set k (regs[k] + 1))`. -/
theorem reg_incr_eval (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regIncrState k) pc regs) =
      some (entryCfg (pc + 1) (regs.set k (regs[k] + 1))) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs = ListBlank.append (encodeRegs pref) (regsTape (r :: suff)) := by
    rw [← regsTape_append, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regIncrState k) pc regs) =
      some ⟨regIncrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape (r :: suff))).cons
          0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regIncrChain_trans_zero k hk16) L_pc _
  have hpref_scan := regIncrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape (r :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have hr_scan : nSteps reference ((r + 1) + 1)
      ⟨31, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨30, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 31) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step reference
        ⟨31, Tape.mk' (ListBlank.append (List.replicate (r +
          1) 1) L_pref) ((regsTape suff).cons 0)⟩ =
        some ⟨30, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := inc_shift_eval suff (r + 1) L_pref
  have hret := return1_scan_fence pref L_pc (regsTape ((r + 1) :: suff))
  rw [← regsTape_append, list_take_set_drop regs k (r + 1) hk] at hret
  have hdisp := dispatch_from_9_entryCfg pc (regs.set k (r + 1))
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift (nSteps_bind_eq hret hdisp))))
  exact ⟨_, by omega, htotal⟩

/-!
### 5.3 `reg_decr` (`regDecrState k`, States `1..8`)
-/

/-- Entry state for decrementing register `k` (`0 ≤ k < 16`). -/
def regDecrState : ℕ → Fin 744
  | 0 => 534
  | 1 => 535
  | 2 => 542
  | 3 => 543
  | 4 => 544
  | 5 => 545
  | 6 => 546
  | 7 => 547
  | 8 => 548
  | 9 => 549
  | 10 => 536
  | 11 => 537
  | 12 => 538
  | 13 => 539
  | 14 => 540
  | 15 => 541
  | _ => 533

/-- Chain of `reg_decr` states where `0 ↦ 533` (`reg_decr(-1)`) and `k + 1 ↦ regDecrState k`. -/
def regDecrChain : ℕ → Fin 744
  | 0 => 533
  | k + 1 => regDecrState k

theorem regDecrChain_trans_one (m : ℕ) (hm : m ≤ 16) :
    refTrans (regDecrChain m) 1 = some (1, .right, regDecrChain m) := by
  revert m hm; decide

theorem regDecrChain_trans_zero (m : ℕ) (hm : m < 16) :
    refTrans (regDecrChain (m + 1)) 0 = some (0, .right, regDecrChain m) := by
  revert m hm; decide

theorem regDecrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 15)
    (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs pref).length + 1)
      ⟨regDecrChain pref.length, Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨2, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length < 16 := by omega
    have hrs_le : rs.length ≤ 15 := by omega
    have h0 : step reference
        ⟨regDecrChain (rs.length + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨regDecrChain rs.length,
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (regDecrChain_trans_zero rs.length hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (regDecrChain_trans_one rs.length (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Leftward shift of a single register `m` in States `7`/`8` (`dec.shift_0`/`dec.shift_1`). -/
theorem dec_shift_reg (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference (m + 2)
      ⟨7, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨7, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step reference
      ⟨7, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨8, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 8) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step reference
      ⟨8, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨7, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

/-- Forward scan and leftward shift across `suff` in States `4, 5, 6, 7, 8`. -/
theorem dec_scan_and_shift (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps reference s
      ⟨4, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨7, Tape.mkL L (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step reference
        ⟨4, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨6, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0)
          default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step reference
        ⟨6, Tape.mkL ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨7, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default⟩ := by
      have h := step_mkL_left (q := 6) (q' := 7) (a := 0) (b := 0) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      rw [default_cons_zero] at h
      exact h
    have hshift := dec_shift_reg m L default
    rw [← regsTape_nil, ← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨4, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨5, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 5) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step reference
        ⟨5, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨4, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg m L (regsTape (r :: rs))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

theorem step_state7_eq_state568 (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    step reference ⟨7, Tape.mkL (ListBlank.append (encodeRegs regs).reverse (L.cons 0)) R⟩ =
      step reference ⟨568, Tape.mkL (ListBlank.append (encodeRegs regs).reverse (L.cons 0)) R⟩ := by
  induction regs using List.reverseRecOn with
  | nil =>
    simp only [encodeRegs_nil, List.reverse_nil, ListBlank.append]
    rw [step_mkL_left (by rfl), step_mkL_left (by rfl)]
  | append_singleton rs r _ =>
    rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
      List.reverse_append, ListBlank.append_assoc, append_encodeReg_reverse]
    rw [step_mkL_left (by rfl), step_mkL_left (by rfl)]

theorem dec_return2_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps reference ((encodeRegs regs).length + 2)
      ⟨7, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨524, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have h568 := return2_scan_fence regs L R
  obtain ⟨m, hm⟩ : ∃ m, (encodeRegs regs).length + 2 = m + 1 :=
    ⟨(encodeRegs regs).length + 1, rfl⟩
  rw [hm, nSteps_succ, step_state7_eq_state568, ← nSteps_succ, ← hm, h568]

/-- `reg_decr` gadget evaluation when `regs[k] = 0`: from `postPcCfg (regDecrState k) pc regs`,
`reference` leaves `regs` unchanged and advances to `entryCfg (pc + 1) regs`. -/
theorem reg_decr_eval_zero (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hz : regs[k] = 0) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (entryCfg (pc + 1) regs) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set suff := regs.drop (k + 1)
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs = ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
    rw [← regsTape_append, ← hz, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regDecrState k) pc regs) =
      some ⟨regDecrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons
          0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecrChain_trans_zero k hk16) L_pc _
  have hpref_scan := regDecrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape (0 :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have h1 : step reference ⟨2, Tape.mk' L_pref (regsTape (0 :: suff))⟩ =
      some ⟨1, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mk'_right (by rfl) L_pref ((regsTape suff).cons 0)
  have h2 : step reference ⟨1, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨3, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ :=
    step_mk'_left (by rfl) (L_pref.cons 0) (regsTape suff)
  have h3 : step reference ⟨3, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨566, Tape.mkL L_pref (regsTape (0 :: suff))⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mkL_left (by rfl) L_pref ((regsTape suff).cons 0)
  have hret := return1_scan_fence pref L_pc (regsTape (0 :: suff))
  rw [← hregs_split] at hret
  have hdisp := dispatch_from_9_entryCfg pc regs
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hret hdisp)))))
  exact ⟨_, by omega, htotal⟩

/-- `reg_decr` gadget evaluation when `regs[k] > 0`: from `postPcCfg (regDecrState k) pc regs`,
`reference` decrements `regs[k]` by `1` and advances to
`entryCfg (pc + 2) (regs.set k (regs[k] - 1))`. -/
theorem reg_decr_eval_pos (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hpos : 0 < regs[k]) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (entryCfg (pc + 2) (regs.set k (regs[k] - 1))) := by
  set L_pc := ListBlank.append (pcBits 11 pc).reverse default
  set pref := regs.take k
  set r' := regs[k] - 1
  set suff := regs.drop (k + 1)
  have hr_eq : regs[k] = r' + 1 := by omega
  have hpref_len : pref.length = k := List.length_take_of_le (by omega)
  have hregs_split : regsTape regs =
      ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff)) := by
    rw [← regsTape_append, ← hr_eq, list_take_cons_drop regs k hk]
  have h0 : step reference (postPcCfg (regDecrState k) pc regs) =
      some ⟨regDecrChain pref.length,
        Tape.mk' (L_pc.cons 0) ((ListBlank.append (encodeRegs pref) (regsTape ((r' +
          1) :: suff))).cons 0)⟩ := by
    unfold postPcCfg
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecrChain_trans_zero k hk16) L_pc _
  have hpref_scan :=
      regDecrChain_scan_pref pref (by omega) (L_pc.cons 0) (regsTape ((r' + 1) :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_pc.cons 0).cons 0)
  have hinit : step reference ⟨2, Tape.mk' L_pref (regsTape ((r' + 1) :: suff))⟩ =
      some ⟨1, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ := by
    have hcons : regsTape ((r' + 1) :: suff) = (regsTape (r' :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hcons]
    exact step_mk'_right (by rfl) L_pref (regsTape (r' :: suff))
  have hr'_scan : nSteps reference (r' + 2)
      ⟨1, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ =
      some ⟨4, Tape.mk' (ListBlank.append (encodeReg r').reverse (L_pref.cons 0)) (regsTape suff)⟩
        := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step reference
        ⟨1, Tape.mk' (L_pref.cons 0)
          ((ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0)).cons 1)⟩ =
        some ⟨5, Tape.mk' ((L_pref.cons 0).cons 1)
          (ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 5) (a := 1) (b := 1) (by rfl)
      r' ((L_pref.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 : step reference
        ⟨5, Tape.mk' (ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1))
          ((regsTape suff).cons 0)⟩ =
        some ⟨4, Tape.mk' ((ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1)).cons 0)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r' (L_pref.cons 0)] at hcomb
    simpa [Nat.add_assoc] using hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := dec_scan_and_shift suff r' L_pref
  have hret := dec_return2_scan_fence pref L_pc (regsTape (r' :: suff))
  rw [← regsTape_append, list_take_set_drop regs k r' hk] at hret
  have hdisp := dispatch_from_524_entryCfg pc (regs.set k r')
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps hinit (nSteps_bind_eq hr'_scan
      (nSteps_bind_eq hshift (nSteps_bind_eq hret hdisp)))))
  exact ⟨_, by omega, htotal⟩

/-- Combined `reg_decr` gadget evaluation for any `k < 16` and `k < regs.length`. -/
theorem reg_decr_eval (k : ℕ) (hk16 : k < 16) (pc : ℕ) (regs : List ℕ)
    (hk : k < regs.length) :
    ∃ s, 1 ≤ s ∧ nSteps reference s (postPcCfg (regDecrState k) pc regs) =
      some (if regs[k] = 0 then entryCfg (pc + 1) regs
            else entryCfg (pc + 2) (regs.set k (regs[k] - 1))) := by
  by_cases hz : regs[k] = 0
  · simp only [hz, ↓reduceIte]
    exact reg_decr_eval_zero k hk16 pc regs hk hz
  · simp only [hz, ↓reduceIte]
    exact reg_decr_eval_pos k hk16 pc regs hk (by omega)

end ConjectureMachines.Semantics.Riemann.Layer1
