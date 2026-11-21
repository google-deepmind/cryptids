/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.FractalReturn
import BusyBeaver.Calculi.RunWin


/-!
# Busy Beaver Machine `1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`, `BusyBeaver.FractalReturn`,
  `BusyBeaver.RunWin`
and defines `target_tm` for `1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS


abbrev stA : Fin 6 := 0
abbrev stE : Fin 6 := 4

def W1000 : List (Fin 2) := [1, 0, 0, 0]
def W10 : List (Fin 2) := [1, 0]
def W01 : List (Fin 2) := [0, 1]
def W0010 : List (Fin 2) := [0, 0, 1, 0]
def M3 : List (Fin 2) := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def S1w : List (Fin 2) := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
def T1w : List (Fin 2) := [0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1]
def S2w : List (Fin 2) := [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1]
def T2w : List (Fin 2) := [0, 0, 0, 1, 0, 1]
def S3w : List (Fin 2) := [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def S4w : List (Fin 2) := [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def M5 : List (Fin 2) := [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0]
def W7 : List (Fin 2) := [0, 1, 1, 1, 1, 1, 1]
def W1110 : List (Fin 2) := [0, 1, 1, 1]
def B4 : List (Fin 2) := [0, 1, 1, 1, 1, 0, 1]
def Y2 : List (Fin 2) := [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0]
def R6 : List (Fin 2) := [1, 0, 0, 1, 1, 1]
def Zk (k : ℕ) : List (Fin 2) := ([0] : List (Fin 2)) ^ k

def N1 (a b d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ a +> (M3 +> (W10 ^ b +> (S1w ^ d +> (T1w +> r)))))

def N2 (a b c d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ a +> (M3 +> (W10 ^ b +> (([0] : List (Fin 2)) +> (W01 ^ c +> (S2w ^ d +> (T2w
    +> r)))))))

def N3 (a b z c d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ a +> (M3 +> (W10 ^ b +> (([0] : List (Fin 2)) +> (W01 ^ z +> (M5 +> (W10 ^ c +>
    (S1w ^ d +> (T1w +> r)))))))))

def LC (x y z Z c d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ x +> (W10 ^ y +> (W0010 ^ z +> (W10 ^ Z +> (M3 +> (W10 ^ c +> (S1w ^ d +> (T1w
    +> r))))))))

def P1 (a s : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ a +> (S3w ^ s +> ([1, 0, 1] +> r)))

def P2 (a b s : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ a +> (W10 ^ b +> (S3w ^ s +> ([1, 0, 1] +> r))))

def T0f (a s : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 4 +> (W1000 ^ a +> (S4w ^ s +> ([0, 0, 1, 0, 0, 0, 1, 0, 1] +> r)))

def T1f (a b c d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 4 +> (W1000 ^ a +> ([0, 0, 1, 0, 0, 0] +> (W10 ^ b +> (([0] : List (Fin 2)) +> (W01 ^ c +>
    (S2w ^ d +> (T2w +> r)))))))

def LCm (x y n Z c d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ x +> (W10 ^ y +> (W10 ^ n +> (W10 ^ Z +> (M3 +> (W10 ^ c +> (S1w ^ d +> (T1w +>
    r))))))))

def LCc (x y z Z c1 n c2 d : ℕ) (r : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  Zk 6 +> (W1000 ^ x +> (W10 ^ y +> (W0010 ^ z +> (W10 ^ Z +> (M3 +> (W10 ^ c1 +> (W10 ^ n +> (W10
    ^ c2 +> (S1w ^ d +> (T1w +> r))))))))))

-- Symbolic VSide constructors matching ES_v3
def vsSeg (w : List (Fin 2)) (t : FractalReturn.VSide (Fin 2)) : FractalReturn.VSide (Fin 2) :=
  FractalReturn.vsideAppSeg w t

def vsConstPow (w : List (Fin 2)) (c : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    FractalReturn.VSide (Fin 2) :=
  FractalReturn.vsideAppSeg (w ^ c) t

def vsPowC (w : List (Fin 2)) (c v : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    FractalReturn.VSide (Fin 2) :=
  FractalReturn.vsideAppSeg (w ^ c) (.app w v t)

def vsPow2C (w : List (Fin 2)) (c v : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    FractalReturn.VSide (Fin 2) :=
  FractalReturn.vsideAppSeg (w ^ c) (.app (w ^ 2) v t)

theorem vsSeg_toSide (fN : ℕ → ℕ) (fS : ℕ → ListBlank (Fin 2))
    (w : List (Fin 2)) (t : FractalReturn.VSide (Fin 2)) :
    (vsSeg w t).toSide fN fS = w +> t.toSide fN fS :=
  FractalReturn.vsideAppSeg_spec fN fS w t

theorem vsConstPow_toSide (fN : ℕ → ℕ) (fS : ℕ → ListBlank (Fin 2))
    (w : List (Fin 2)) (c : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    (vsConstPow w c t).toSide fN fS = (w ^ c) +> t.toSide fN fS :=
  FractalReturn.vsideAppSeg_spec fN fS (w ^ c) t

theorem vsPowC_toSide (fN : ℕ → ℕ) (fS : ℕ → ListBlank (Fin 2))
    (w : List (Fin 2)) (c v : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    (vsPowC w c v t).toSide fN fS = (w ^ (c + fN v)) +> t.toSide fN fS := by
  unfold vsPowC
  rw [FractalReturn.vsideAppSeg_spec, FractalReturn.VSide.toSide,
    ListBlank.append_append, ← list_pow_add]

theorem vsPow2C_toSide (fN : ℕ → ℕ) (fS : ℕ → ListBlank (Fin 2))
    (w : List (Fin 2)) (c v : ℕ) (t : FractalReturn.VSide (Fin 2)) :
    (vsPow2C w c v t).toSide fN fS = (w ^ (c + fN v * 2)) +> t.toSide fN fS := by
  unfold vsPow2C
  rw [FractalReturn.vsideAppSeg_spec, FractalReturn.VSide.toSide,
    ← list_pow_mul w 2 (fN v), Nat.mul_comm 2 (fN v),
    ListBlank.append_append, ← list_pow_add]

def fN6 (n0 n1 n2 n3 n4 n5 : ℕ) : ℕ → ℕ
  | 0 => n0
  | 1 => n1
  | 2 => n2
  | 3 => n3
  | 4 => n4
  | _ => n5

def fS2 (l r : ListBlank (Fin 2)) : ℕ → ListBlank (Fin 2)
  | 0 => l
  | _ => r

abbrev vL : FractalReturn.VSide (Fin 2) := .var 0
abbrev vR : FractalReturn.VSide (Fin 2) := .var 1


private def n1_cyc_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 2 1 (vsPowC S1w 4 2
    (vsSeg T1w (vR))))))) stA

private def n1_cyc_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 14 1 (vsPowC S1w 2 2 (vsSeg T1w
    (vR))))))) stA

private theorem n1_cyc_cert :
    FractalReturn.checkEs target_tm n1_cyc_lhs n1_cyc_rhs true 18 6 300 = true := by
  decide +kernel

theorem n1_cyc (a b d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N1 a (2 + b) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} N1 (3 + a) (14 + b) (2
      + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b d 0 0 0) (fS2 l r) n1_cyc_cert
  simpa only [n1_cyc_lhs, n1_cyc_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N1] using h


private def n1_d2_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 2 1 (vsConstPow S1w
    2 (vsSeg T1w (vR))))))) stA

private def n1_d2_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 14 1 (vsConstPow S1w 0 (vsSeg T1w
    (vR))))))) stA

private theorem n1_d2_cert :
    FractalReturn.checkEs target_tm n1_d2_lhs n1_d2_rhs true 18 6 300 = true := by
  decide +kernel

theorem n1_d2 (a b : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N1 a (2 + b) 2 r) [target_tm]⊢⁺ (l <{{stA}} N1 (3 + a) (14 + b) 0 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b 0 0 0 0) (fS2 l r) n1_d2_cert
  simpa only [n1_d2_lhs, n1_d2_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N1] using h


private def n1_d3_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 2 1 (vsConstPow S1w
    3 (vsSeg T1w (vR))))))) stA

private def n1_d3_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 14 1 (vsConstPow S1w 1 (vsSeg T1w
    (vR))))))) stA

private theorem n1_d3_cert :
    FractalReturn.checkEs target_tm n1_d3_lhs n1_d3_rhs true 18 6 300 = true := by
  decide +kernel

theorem n1_d3 (a b : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N1 a (2 + b) 3 r) [target_tm]⊢⁺ (l <{{stA}} N1 (3 + a) (14 + b) 1 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b 0 0 0 0) (fS2 l r) n1_d3_cert
  simpa only [n1_d3_lhs, n1_d3_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N1] using h


private def p1_r_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC S3w 6 1 (vsSeg [1, 0, 1] (vR)))))
    stA

private def p1_r_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsSeg M3 (vsConstPow W10 7 (vsPowC S1w 3 1 (vsSeg T1w
    (vR))))))) stA

private theorem p1_r_cert :
    FractalReturn.checkEs target_tm p1_r_lhs p1_r_rhs true 8 5 470 = true := by
  decide +kernel

theorem p1_r (a s : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} P1 a (6 + s) r) [target_tm]⊢⁺ (l <{{stA}} N1 (2 + a) 7 (3 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a s 0 0 0 0) (fS2 l r) p1_r_cert
  simpa only [p1_r_lhs, p1_r_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, P1, N1] using h


private def p2_r_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 2) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsPowC S3w 6 2 (vsSeg
    [1, 0, 1] (vR)))))) stA

private def p2_r_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 1 0 (vsSeg M3 (vsPowC W10 6 1 (vsPowC S1w 4 2 (vsSeg T1w
    (vR))))))) stA

private theorem p2_r_cert :
    FractalReturn.checkEs target_tm p2_r_lhs p2_r_rhs true 10 6 130 = true := by
  decide +kernel

theorem p2_r (a b s : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 2 +> l) <{{stA}} P2 a (6 + b) (6 + s) r) [target_tm]⊢⁺ (l <{{stA}} N1 (1 + a) (6 + b) (4
      + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b s 0 0 0) (fS2 l r) p2_r_cert
  simpa only [p2_r_lhs, p2_r_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, P2, N1] using h


private def t0_r_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 12) (vL)) (vsSeg (Zk 4) (vsPowC W1000 14 0 (vsPowC S4w 8 1 (vsSeg [0, 0, 1, 0, 0,
    0, 1, 0, 1] (vR))))) stA

private def t0_r_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsConstPow W1000 5 (vsConstPow W10 14 (vsPowC W0010 6 0 (vsConstPow W10 8
    (vsSeg M3 (vsConstPow W10 7 (vsPowC S1w 4 1 (vsSeg T1w (vR)))))))))) stA

private theorem t0_r_cert :
    FractalReturn.checkEs target_tm t0_r_lhs t0_r_rhs true 14 4 620 = true := by
  decide +kernel

theorem t0_r (z d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 12 +> l) <{{stA}} T0f (14 + z) (8 + d) r) [target_tm]⊢⁺ (l <{{stA}} LC 5 14 (6 + z) 8 7
      (4 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 z d 0 0 0 0) (fS2 l r) t0_r_cert
  simpa only [t0_r_lhs, t0_r_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, T0f, LC] using h


private def t1_r_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 4) (vL)) (vsSeg (Zk 4) (vsPowC W1000 9 0 (vsSeg [0, 0, 1, 0, 0, 0] (vsPowC W10 7 1
    (vsSeg [0] (vsPowC W01 6 2 (vsPowC S2w 6 3 (vsSeg T2w (vR))))))))) stA

private def t1_r_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsConstPow W1000 1 (vsConstPow W10 6 (vsPowC W0010 6 0 (vsPowC W10 11 1
    (vsSeg M3 (vsPowC W10 7 2 (vsPowC S1w 4 3 (vsSeg T1w (vR)))))))))) stA

private theorem t1_r_cert :
    FractalReturn.checkEs target_tm t1_r_lhs t1_r_rhs true 14 6 165 = true := by
  decide +kernel

theorem t1_r (z b c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 4 +> l) <{{stA}} T1f (9 + z) (7 + b) (6 + c) (6 + d) r) [target_tm]⊢⁺ (l <{{stA}} LC 1 6
      (6 + z) (11 + b) (7 + c) (4 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 z b c d 0 0) (fS2 l r) t1_r_cert
  simpa only [t1_r_lhs, t1_r_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, T1f, LC] using h


private def lc_cyc_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsPowC W0010 6 2 (vsPowC
    W10 8 3 (vsSeg M3 (vsPowC W10 7 4 (vsPowC S1w 4 5 (vsSeg T1w (vR)))))))))) stA

private def lc_cyc_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 4 0 (vsPowC W10 14 1 (vsPowC W0010 1 2 (vsPowC W10 15 3 (vsSeg
    M3 (vsPowC W10 12 4 (vsPowC S1w 2 5 (vsSeg T1w (vR)))))))))) stA

private theorem lc_cyc_cert :
    FractalReturn.checkEs target_tm lc_cyc_lhs lc_cyc_rhs true 42 6 250 = true := by
  decide +kernel

theorem lc_cyc (x y z Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} LC x (6 + y) (6 + z) (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l
      <{{stA}} LC (4 + x) (14 + y) (1 + z) (15 + Z) (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y z Z c d) (fS2 l r) lc_cyc_cert
  simpa only [lc_cyc_lhs, lc_cyc_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC] using h


private def lc_z5_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 5
    (vsPowC W10 8 2 (vsSeg M3 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR)))))))))) stA

private def lc_z5_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 4 0 (vsPowC W10 0 1 (vsConstPow W10 29 (vsPowC W10 0 2 (vsSeg
    M3 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR)))))))))) stA

private theorem lc_z5_cert :
    FractalReturn.checkEs target_tm lc_z5_lhs lc_z5_rhs true 34 6 250 = true := by
  decide +kernel

theorem lc_z5 (x y Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} LC x (6 + y) 5 (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} LCm
      (4 + x) y 29 Z (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y Z c d 0) (fS2 l r) lc_z5_cert
  simpa only [lc_z5_lhs, lc_z5_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, LCm] using h


private def lc_z4_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 4
    (vsPowC W10 8 2 (vsSeg M3 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR)))))))))) stA

private def lc_z4_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 4 0 (vsPowC W10 0 1 (vsConstPow W10 27 (vsPowC W10 0 2 (vsSeg
    M3 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR)))))))))) stA

private theorem lc_z4_cert :
    FractalReturn.checkEs target_tm lc_z4_lhs lc_z4_rhs true 34 6 250 = true := by
  decide +kernel

theorem lc_z4 (x y Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} LC x (6 + y) 4 (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} LCm
      (4 + x) y 27 Z (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y Z c d 0) (fS2 l r) lc_z4_cert
  simpa only [lc_z4_lhs, lc_z4_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, LCm] using h


private def lc_z3_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 3
    (vsPowC W10 8 2 (vsSeg M3 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR)))))))))) stA

private def lc_z3_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 4 0 (vsPowC W10 0 1 (vsConstPow W10 25 (vsPowC W10 0 2 (vsSeg
    M3 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR)))))))))) stA

private theorem lc_z3_cert :
    FractalReturn.checkEs target_tm lc_z3_lhs lc_z3_rhs true 34 6 250 = true := by
  decide +kernel

theorem lc_z3 (x y Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} LC x (6 + y) 3 (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} LCm
      (4 + x) y 25 Z (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y Z c d 0) (fS2 l r) lc_z3_cert
  simpa only [lc_z3_lhs, lc_z3_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, LCm] using h


private def lc_z2_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 4) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 2
    (vsPowC W10 8 2 (vsSeg M3 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR)))))))))) stA

private def lc_z2_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsSeg M3 (vsPowC W10 8 1 (vsSeg [0] (vsPowC W01 9 2
    (vsSeg M5 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR))))))))))) stA

private theorem lc_z2_cert :
    FractalReturn.checkEs target_tm lc_z2_lhs lc_z2_rhs true 30 6 250 = true := by
  decide +kernel

theorem lc_z2 (x y Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 4 +> l) <{{stA}} LC x (6 + y) 2 (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} N3
      (2 + x) (8 + y) (9 + Z) (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y Z c d 0) (fS2 l r) lc_z2_cert
  simpa only [lc_z2_lhs, lc_z2_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N3] using h


private def lc_z1_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 4) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 1
    (vsPowC W10 8 2 (vsSeg M3 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR)))))))))) stA

private def lc_z1_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0] (vsPowC W01 9 2
    (vsSeg M5 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR))))))))))) stA

private theorem lc_z1_cert :
    FractalReturn.checkEs target_tm lc_z1_lhs lc_z1_rhs true 30 6 250 = true := by
  decide +kernel

theorem lc_z1 (x y Z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 4 +> l) <{{stA}} LC x (6 + y) 1 (8 + Z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} N3
      (2 + x) (6 + y) (9 + Z) (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y Z c d 0) (fS2 l r) lc_z1_cert
  simpa only [lc_z1_lhs, lc_z1_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N3] using h


private def lh_r_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 2) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsPowC W10 6 1 (vsConstPow W0010 0
    (vsConstPow W10 0 (vsSeg M3 (vsPowC W10 7 2 (vsPowC S1w 0 3 (vsSeg T1w (vR)))))))))) stA

private def lh_r_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 1 0 (vsSeg M3 (vsPowC W10 5 1 (vsSeg [0] (vsPowC W01 11 2
    (vsPowC S2w 0 3 (vsSeg T2w (vR))))))))) stA

private theorem lh_r_cert :
    FractalReturn.checkEs target_tm lh_r_lhs lh_r_rhs true 12 6 130 = true := by
  decide +kernel

theorem lh_r (x y c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 2 +> l) <{{stA}} LC x (6 + y) 0 0 (7 + c) d r) [target_tm]⊢⁺ (l <{{stA}} N2 (1 + x) (5 +
      y) (11 + c) d r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 x y c d 0 0) (fS2 l r) lh_r_cert
  simpa only [lh_r_lhs, lh_r_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N2] using h


private def n2_cyc_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 7 2 (vsPowC S2w 4 3 (vsSeg T2w (vR))))))))) stA

private def n2_cyc_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsPowC W10 14 1 (vsConstPow W0010 0 (vsConstPow W10 0
    (vsSeg M3 (vsPowC W10 8 2 (vsPowC S1w 2 3 (vsSeg T1w (vR)))))))))) stA

private theorem n2_cyc_cert :
    FractalReturn.checkEs target_tm n2_cyc_lhs n2_cyc_rhs true 16 6 160 = true := by
  decide +kernel

theorem n2_cyc (a b c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} N2 a (6 + b) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} LC (2 + a) (14
      + b) 0 0 (8 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b c d 0 0) (fS2 l r) n2_cyc_cert
  simpa only [n2_cyc_lhs, n2_cyc_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N2] using h


private def n2_d2_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 7 2 (vsConstPow S2w 2 (vsSeg T2w (vR))))))))) stA

private def n2_d2_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsPowC W10 14 1 (vsConstPow W0010 0 (vsConstPow W10 0
    (vsSeg M3 (vsPowC W10 8 2 (vsConstPow S1w 0 (vsSeg T1w (vR)))))))))) stA

private theorem n2_d2_cert :
    FractalReturn.checkEs target_tm n2_d2_lhs n2_d2_rhs true 16 6 160 = true := by
  decide +kernel

theorem n2_d2 (a b c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} N2 a (6 + b) (7 + c) 2 r) [target_tm]⊢⁺ (l <{{stA}} LC (2 + a) (14 + b)
      0 0 (8 + c) 0 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b c 0 0 0) (fS2 l r) n2_d2_cert
  simpa only [n2_d2_lhs, n2_d2_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N2] using h


private def n2_d3_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 7 2 (vsConstPow S2w 3 (vsSeg T2w (vR))))))))) stA

private def n2_d3_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 2 0 (vsPowC W10 14 1 (vsConstPow W0010 0 (vsConstPow W10 0
    (vsSeg M3 (vsPowC W10 8 2 (vsConstPow S1w 1 (vsSeg T1w (vR)))))))))) stA

private theorem n2_d3_cert :
    FractalReturn.checkEs target_tm n2_d3_lhs n2_d3_rhs true 16 6 160 = true := by
  decide +kernel

theorem n2_d3 (a b c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} N2 a (6 + b) (7 + c) 3 r) [target_tm]⊢⁺ (l <{{stA}} LC (2 + a) (14 + b)
      0 0 (8 + c) 1 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b c 0 0 0) (fS2 l r) n2_d3_cert
  simpa only [n2_d3_lhs, n2_d3_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC, N2] using h


private def n3_cyc_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 6 2 (vsSeg M5 (vsPowC W10 7 3 (vsPowC S1w 4 4 (vsSeg T1w (vR))))))))))) stA

private def n3_cyc_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 13 1 (vsSeg [0] (vsPowC W01 6 2
    (vsSeg M5 (vsPowC W10 12 3 (vsPowC S1w 2 4 (vsSeg T1w (vR))))))))))) stA

private theorem n3_cyc_cert :
    FractalReturn.checkEs target_tm n3_cyc_lhs n3_cyc_rhs true 34 6 325 = true := by
  decide +kernel

theorem n3_cyc (a b z c d : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N3 a (6 + b) (6 + z) (7 + c) (4 + d) r) [target_tm]⊢⁺ (l <{{stA}} N3 (3
      + a) (13 + b) (6 + z) (12 + c) (2 + d) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b z c d 0) (fS2 l r) n3_cyc_cert
  simpa only [n3_cyc_lhs, n3_cyc_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N3] using h


private def n3_d2_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 6 2 (vsSeg M5 (vsPowC W10 7 3 (vsConstPow S1w 2 (vsSeg T1w (vR))))))))))) stA

private def n3_d2_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 13 1 (vsSeg [0] (vsPowC W01 6 2
    (vsSeg M5 (vsPowC W10 12 3 (vsConstPow S1w 0 (vsSeg T1w (vR))))))))))) stA

private theorem n3_d2_cert :
    FractalReturn.checkEs target_tm n3_d2_lhs n3_d2_rhs true 34 6 325 = true := by
  decide +kernel

theorem n3_d2 (a b z c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N3 a (6 + b) (6 + z) (7 + c) 2 r) [target_tm]⊢⁺ (l <{{stA}} N3 (3 + a)
      (13 + b) (6 + z) (12 + c) 0 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b z c 0 0) (fS2 l r) n3_d2_cert
  simpa only [n3_d2_lhs, n3_d2_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N3] using h


private def n3_d3_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 6 2 (vsSeg M5 (vsPowC W10 7 3 (vsConstPow S1w 3 (vsSeg T1w (vR))))))))))) stA

private def n3_d3_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsSeg M3 (vsPowC W10 13 1 (vsSeg [0] (vsPowC W01 6 2
    (vsSeg M5 (vsPowC W10 12 3 (vsConstPow S1w 1 (vsSeg T1w (vR))))))))))) stA

private theorem n3_d3_cert :
    FractalReturn.checkEs target_tm n3_d3_lhs n3_d3_rhs true 34 6 325 = true := by
  decide +kernel

theorem n3_d3 (a b z c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N3 a (6 + b) (6 + z) (7 + c) 3 r) [target_tm]⊢⁺ (l <{{stA}} N3 (3 + a)
      (13 + b) (6 + z) (12 + c) 1 r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b z c 0 0) (fS2 l r) n3_d3_cert
  simpa only [n3_d3_lhs, n3_d3_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N3] using h


private def n1s0_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 2 1 (vsConstPow S1w
    0 (vsSeg T1w (vsSeg (Zk 18) (vR)))))))) stA

private def n1s0_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 9 1 (vsSeg R6 (vsConstPow W7 4 (vsPowC W1110 3 0 (vL)))))) vR stE

private theorem n1s0_cert :
    FractalReturn.checkEs target_tm n1s0_lhs n1s0_rhs true 20 6 420 = true := by
  decide +kernel

theorem n1s0 (a b : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N1 a (2 + b) 0 (Zk 18 +> r)) [target_tm]⊢⁺ (([1] +> (W01 ^ (9 + b) +>
      (R6 +> (W7 ^ 4 +> (W1110 ^ (3 + a) +> l))))) {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b 0 0 0 0) (fS2 l r) n1s0_cert
  simpa only [n1s0_lhs, n1s0_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N1] using h


private def n1s1_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 2 1 (vsConstPow S1w
    1 (vsSeg T1w (vsSeg (Zk 9) (vR)))))))) stA

private def n1s1_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 8 1 (vsSeg R6 (vsConstPow W7 5 (vsPowC W1110 3 0 (vL)))))) vR stE

private theorem n1s1_cert :
    FractalReturn.checkEs target_tm n1s1_lhs n1s1_rhs true 22 6 400 = true := by
  decide +kernel

theorem n1s1 (a b : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N1 a (2 + b) 1 (Zk 9 +> r)) [target_tm]⊢⁺ (([1] +> (W01 ^ (8 + b) +> (R6
      +> (W7 ^ 5 +> (W1110 ^ (3 + a) +> l))))) {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b 0 0 0 0) (fS2 l r) n1s1_cert
  simpa only [n1s1_lhs, n1s1_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N1] using h


private def n2s0_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 8 1 (vsSeg [0]
    (vsPowC W01 4 2 (vsConstPow S2w 0 (vsSeg T2w (vsSeg (Zk 18) (vR)))))))))) stA

private def n2s0_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 0 2 (vsSeg R6 (vsConstPow W7 3 (vsSeg B4 (vsPowC W01 0 1 (vsSeg Y2
    (vsSeg Y2 (vsPowC W1110 3 0 (vL)))))))))) vR stE

private theorem n2s0_cert :
    FractalReturn.checkEs target_tm n2s0_lhs n2s0_rhs true 18 6 200 = true := by
  decide +kernel

theorem n2s0 (a b c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} N2 a (8 + b) (4 + c) 0 (Zk 18 +> r)) [target_tm]⊢⁺ (([1] +> (W01 ^ c +>
      (R6 +> (W7 ^ 3 +> (B4 +> (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + a) +> l))))))))) {{stE}}>
      r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b c 0 0 0) (fS2 l r) n2s0_cert
  simpa only [n2s0_lhs, n2s0_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N2] using h


private def n2s1_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 6) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 8 1 (vsSeg [0]
    (vsPowC W01 5 2 (vsConstPow S2w 1 (vsSeg T2w (vsSeg (Zk 9) (vR)))))))))) stA

private def n2s1_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 0 2 (vsSeg R6 (vsConstPow W7 4 (vsSeg B4 (vsPowC W01 0 1 (vsSeg Y2
    (vsSeg Y2 (vsPowC W1110 3 0 (vL)))))))))) vR stE

private theorem n2s1_cert :
    FractalReturn.checkEs target_tm n2s1_lhs n2s1_rhs true 20 6 200 = true := by
  decide +kernel

theorem n2s1 (a b c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 6 +> l) <{{stA}} N2 a (8 + b) (5 + c) 1 (Zk 9 +> r)) [target_tm]⊢⁺ (([1] +> (W01 ^ c +>
      (R6 +> (W7 ^ 4 +> (B4 +> (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + a) +> l))))))))) {{stE}}>
      r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b c 0 0 0) (fS2 l r) n2s1_cert
  simpa only [n2s1_lhs, n2s1_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N2] using h


private def n3s0_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 9 2 (vsSeg M5 (vsPowC W10 7 3 (vsConstPow S1w 0 (vsSeg T1w (vsSeg (Zk 18)
    (vR)))))))))))) stA

private def n3s0_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 7 3 (vsSeg R6 (vsConstPow W7 3 (vsSeg B4 (vsPowC W01 6 2 (vsSeg R6
    (vsPowC W01 11 1 (vsSeg R6 (vsSeg W7 (vsSeg W7 (vsPowC W1110 3 0 (vL))))))))))))) vR stE

private theorem n3s0_cert :
    FractalReturn.checkEs target_tm n3s0_lhs n3s0_rhs true 34 6 370 = true := by
  decide +kernel

theorem n3s0 (a b z c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N3 a (6 + b) (9 + z) (7 + c) 0 (Zk 18 +> r)) [target_tm]⊢⁺ (([1] +> (W01
      ^ (7 + c) +> (R6 +> (W7 ^ 3 +> (B4 +> (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7
      +> (W7 +> (W1110 ^ (3 + a) +> l)))))))))))) {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b z c 0 0) (fS2 l r) n3s0_cert
  simpa only [n3s0_lhs, n3s0_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N3] using h


private def n3s1_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L (vsSeg (Zk 8) (vL)) (vsSeg (Zk 6) (vsPowC W1000 0 0 (vsSeg M3 (vsPowC W10 6 1 (vsSeg [0]
    (vsPowC W01 9 2 (vsSeg M5 (vsPowC W10 7 3 (vsConstPow S1w 1 (vsSeg T1w (vsSeg (Zk 9)
    (vR)))))))))))) stA

private def n3s1_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 6 3 (vsSeg R6 (vsConstPow W7 4 (vsSeg B4 (vsPowC W01 6 2 (vsSeg R6
    (vsPowC W01 11 1 (vsSeg R6 (vsSeg W7 (vsSeg W7 (vsPowC W1110 3 0 (vL))))))))))))) vR stE

private theorem n3s1_cert :
    FractalReturn.checkEs target_tm n3s1_lhs n3s1_rhs true 36 6 350 = true := by
  decide +kernel

theorem n3s1 (a b z c : ℕ) (l r : ListBlank (Fin 2)) :
    ((Zk 8 +> l) <{{stA}} N3 a (6 + b) (9 + z) (7 + c) 1 (Zk 9 +> r)) [target_tm]⊢⁺ (([1] +> (W01
      ^ (6 + c) +> (R6 +> (W7 ^ 4 +> (B4 +> (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7
      +> (W7 +> (W1110 ^ (3 + a) +> l)))))))))))) {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b z c 0 0) (fS2 l r) n3s1_cert
  simpa only [n3s1_lhs, n3s1_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, N3] using h


private def qa_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 1 2 (vsSeg R6 (vsPowC W7 0 1 (vsPowC W1110 1 0 (vL)))))) (vsSeg (Zk 5)
    (vR)) stE

private def qa_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 0 2 (vsSeg R6 (vsPowC W7 1 1 (vsPowC W1110 1 0 (vL)))))) vR stE

private theorem qa_cert :
    FractalReturn.checkEs target_tm qa_lhs qa_rhs true 4 6 60 = true := by
  decide +kernel

theorem qa (k q m : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (W01 ^ (1 + m) +> (R6 +> (W7 ^ q +> (W1110 ^ (1 + k) +> l))))) {{stE}}> (Zk 5 +> r))
      [target_tm]⊢⁺ (([1] +> (W01 ^ m +> (R6 +> (W7 ^ (1 + q) +> (W1110 ^ (1 + k) +> l)))))
      {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 k q m 0 0 0) (fS2 l r) qa_cert
  simpa only [qa_lhs, qa_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add] using h


private def qb_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 1 1 (vsSeg R6 (vsPowC W7 0 0 (vsSeg B4 (vL)))))) (vsSeg (Zk 5) (vR)) stE

private def qb_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsPowC W01 0 1 (vsSeg R6 (vsPowC W7 1 0 (vsSeg B4 (vL)))))) vR stE

private theorem qb_cert :
    FractalReturn.checkEs target_tm qb_lhs qb_rhs true 4 6 60 = true := by
  decide +kernel

theorem qb (q m : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (W01 ^ (1 + m) +> (R6 +> (W7 ^ q +> (B4 +> l))))) {{stE}}> (Zk 5 +> r)) [target_tm]⊢⁺
      (([1] +> (W01 ^ m +> (R6 +> (W7 ^ (1 + q) +> (B4 +> l))))) {{stE}}> r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 q m 0 0 0 0) (fS2 l r) qb_cert
  simpa only [qb_lhs, qb_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add] using h


private def q1odd_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 9 1 (vsPowC W1110 4 0 (vL))))) (vsSeg (Zk 9) (vR)) stE

private def q1odd_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 4 0 (vsPowC S3w 5 1 (vsSeg [1, 0, 1] (vR))))) stA

private theorem q1odd_cert :
    FractalReturn.checkEs target_tm q1odd_lhs q1odd_rhs true 4 5 320 = true := by
  decide +kernel

theorem q1odd (k s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (9 + s * 2) +> (W1110 ^ (4 + k) +> l)))) {{stE}}> (Zk 9 +> r))
      [target_tm]⊢⁺ (l <{{stA}} P1 (4 + k) (5 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 k s 0 0 0 0) (fS2 l r) q1odd_cert
  simpa only [q1odd_lhs, q1odd_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, P1] using h


private def q1even_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 10 1 (vsPowC W1110 4 0 (vsSeg [0] (vL)))))) (vsSeg (Zk 9)
    (vR)) stE

private def q1even_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 4) (vsPowC W1000 5 0 (vsPowC S4w 5 1 (vsSeg [0, 0, 1, 0, 0, 0, 1, 0, 1]
    (vR))))) stA

private theorem q1even_cert :
    FractalReturn.checkEs target_tm q1even_lhs q1even_rhs true 4 3 350 = true := by
  decide +kernel

theorem q1even (k s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (10 + s * 2) +> (W1110 ^ (4 + k) +> (([0] : List (Fin 2)) +> l)))))
      {{stE}}> (Zk 9 +> r)) [target_tm]⊢⁺ (l <{{stA}} T0f (5 + k) (5 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 k s 0 0 0 0) (fS2 l r) q1even_cert
  simpa only [q1even_lhs, q1even_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, T0f] using h


private def q2even_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 10 2 (vsSeg B4 (vsPowC W01 0 1 (vsSeg Y2 (vsSeg Y2 (vsPowC
    W1110 4 0 (vL))))))))) (vsSeg (Zk 9) (vR)) stE

private def q2even_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 3 0 (vsPowC W10 16 1 (vsPowC S3w 6 2 (vsSeg [1, 0, 1]
    (vR)))))) stA

private theorem q2even_cert :
    FractalReturn.checkEs target_tm q2even_lhs q2even_rhs true 5 5 350 = true := by
  decide +kernel

theorem q2even (a b s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (10 + s * 2) +> (B4 +> (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (4 + a) +>
      l)))))))) {{stE}}> (Zk 9 +> r)) [target_tm]⊢⁺ (l <{{stA}} P2 (3 + a) (16 + b) (6 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b s 0 0 0) (fS2 l r) q2even_cert
  simpa only [q2even_lhs, q2even_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, P2] using h


private def q2odd_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 9 2 (vsSeg B4 (vsPowC W01 0 1 (vsSeg Y2 (vsSeg Y2 (vsPowC
    W1110 4 0 (vsSeg [0] (vL)))))))))) (vsSeg (Zk 9) (vR)) stE

private def q2odd_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 4) (vsPowC W1000 4 0 (vsSeg [0, 0, 1, 0, 0, 0] (vsConstPow W10 7 (vsSeg [0]
    (vsPowC W01 14 1 (vsPowC S2w 4 2 (vsSeg T2w (vR))))))))) stA

private theorem q2odd_cert :
    FractalReturn.checkEs target_tm q2odd_lhs q2odd_rhs true 9 6 320 = true := by
  decide +kernel

theorem q2odd (a b s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (9 + s * 2) +> (B4 +> (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (4 + a) +>
      (([0] : List (Fin 2)) +> l))))))))) {{stE}}> (Zk 9 +> r)) [target_tm]⊢⁺ (l <{{stA}} T1f (4 +
      a) 7 (14 + b) (4 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 a b s 0 0 0) (fS2 l r) q2odd_cert
  simpa only [q2odd_lhs, q2odd_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, T1f] using h


private def q3even_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 10 3 (vsSeg B4 (vsPowC W01 6 2 (vsSeg R6 (vsPowC W01 6 1
    (vsSeg R6 (vsSeg W7 (vsSeg W7 (vsPowC W1110 4 0 (vsSeg (Zk 6) (vL))))))))))))) (vsSeg (Zk 9)
    (vR)) stE

private def q3even_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsPowC W1000 6 0 (vsPowC W10 16 1 (vsConstPow W0010 0 (vsConstPow W10 0
    (vsSeg M3 (vsPowC W10 9 2 (vsPowC S1w 4 3 (vsSeg T1w (vR)))))))))) stA

private theorem q3even_cert :
    FractalReturn.checkEs target_tm q3even_lhs q3even_rhs true 20 6 350 = true := by
  decide +kernel

theorem q3even (k b z s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (10 + s * 2) +> (B4 +> (W01 ^ (6 + z) +> (R6 +> (W01 ^ (6 + b) +> (R6 +>
      (W7 +> (W7 +> (W1110 ^ (4 + k) +> (Zk 6 +> l)))))))))))) {{stE}}> (Zk 9 +> r)) [target_tm]⊢⁺
      (l <{{stA}} LC (6 + k) (16 + b) 0 0 (9 + z) (4 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 k b z s 0 0) (fS2 l r) q3even_cert
  simpa only [q3even_lhs, q3even_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LC] using h


private def q3odd_lhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .R (vsSeg [1] (vsSeg R6 (vsPow2C W7 9 3 (vsSeg B4 (vsPowC W01 6 2 (vsSeg R6 (vsPowC W01 6 1
    (vsSeg R6 (vsSeg W7 (vsSeg W7 (vsPowC W1110 13 0 (vsSeg (Zk 13) (vL))))))))))))) (vsSeg (Zk 9)
    (vR)) stE

private def q3odd_rhs : FractalReturn.VConfig (Fin 2) (Fin 6) :=
  .L vL (vsSeg (Zk 6) (vsConstPow W1000 5 (vsConstPow W10 14 (vsPowC W0010 6 0 (vsConstPow W10 15
    (vsSeg M3 (vsPowC W10 6 1 (vsConstPow W10 6 (vsPowC W10 6 2 (vsPowC S1w 2 3 (vsSeg T1w
    (vR)))))))))))) stA

private theorem q3odd_cert :
    FractalReturn.checkEs target_tm q3odd_lhs q3odd_rhs true 40 6 510 = true := by
  decide +kernel

theorem q3odd (k b z s : ℕ) (l r : ListBlank (Fin 2)) :
    (([1] +> (R6 +> (W7 ^ (9 + s * 2) +> (B4 +> (W01 ^ (6 + z) +> (R6 +> (W01 ^ (6 + b) +> (R6 +>
      (W7 +> (W7 +> (W1110 ^ (13 + k) +> (Zk 13 +> l)))))))))))) {{stE}}> (Zk 9 +> r))
      [target_tm]⊢⁺ (l <{{stA}} LCc 5 14 (6 + k) 15 (6 + b) 6 (6 + z) (2 + s) r) := by
  have h := FractalReturn.checkEs_spec_plus target_tm (fN6 k b z s 0 0) (fS2 l r) q3odd_cert
  simpa only [q3odd_lhs, q3odd_rhs, FractalReturn.VConfig.toCfg, FractalReturn.VSide.toSide,
    vsSeg_toSide, vsConstPow_toSide, vsPowC_toSide, vsPow2C_toSide,
    fN6, fS2, Nat.zero_add, LCc] using h


theorem Zk_default (k : ℕ) : Zk k +> (default : ListBlank (Fin 2)) = default :=
  zeros_append_default k

theorem z0_default : ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
  zeros_append_default 1

theorem qa_loop (k m : ℕ) :
    ∀ q (l : ListBlank (Fin 2)),
      (([1] +> (W01 ^ m +> (R6 +> (W7 ^ q +> (W1110 ^ (1 + k) +> l))))) {{stE}}> default)
        [target_tm]⊢*
      (([1] +> (W01 ^ 0 +> (R6 +> (W7 ^ (q + m) +> (W1110 ^ (1 + k) +> l))))) {{stE}}> default) :=
        by
  induction m with
  | zero =>
    intro q l
    rw [Nat.add_zero]
  | succ m ih =>
    intro q l
    have h1 := qa k q m l default
    rw [Zk_default 5] at h1
    have h1m : 1 + m = m + 1 := by omega
    rw [h1m] at h1
    refine ReachesStar.trans (ReachesPlus.to_star h1) ?_
    have hqm : q + (m + 1) = (1 + q) + m := by omega
    rw [hqm]
    exact ih (1 + q) l

theorem qb_loop (m : ℕ) :
    ∀ q (l : ListBlank (Fin 2)),
      (([1] +> (W01 ^ m +> (R6 +> (W7 ^ q +> (B4 +> l))))) {{stE}}> default)
        [target_tm]⊢*
      (([1] +> (W01 ^ 0 +> (R6 +> (W7 ^ (q + m) +> (B4 +> l))))) {{stE}}> default) := by
  induction m with
  | zero =>
    intro q l
    rw [Nat.add_zero]
  | succ m ih =>
    intro q l
    have h1 := qb q m l default
    rw [Zk_default 5] at h1
    have h1m : 1 + m = m + 1 := by omega
    rw [h1m] at h1
    refine ReachesStar.trans (ReachesPlus.to_star h1) ?_
    have hqm : q + (m + 1) = (1 + q) + m := by omega
    rw [hqm]
    exact ih (1 + q) l

def cN1 (a b d : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} N1 a b d default
def cN2 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} N2 a b c d default
def cN3 (a b z c d : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} N3 a b z c d default
def cLC (x y z Z c d : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} LC x y z Z c d default
def cP1 (a s : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} P1 a s default
def cP2 (a b s : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} P2 a b s default
def cT0 (a s : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} T0f a s default
def cT1 (a b c d : ℕ) : Cfg (Fin 2) (Fin 6) := default <{{stA}} T1f a b c d default

theorem n1e0_even (k t : ℕ) : (cN1 (1 + k) (2 + t * 2) 0) [target_tm]⊢⁺ cP1 (4 + k) (7 + t) := by
  have h1 := n1s0 (1 + k) (t * 2) default default
  rw [Zk_default 8, Zk_default 18] at h1
  have h2 := qa_loop (2 + (1 + k)) (9 + t * 2) 4 default
  have h3 := q1odd k (2 + t) default default
  rw [Zk_default 9] at h3
  have ha : 1 + (2 + (1 + k)) = 3 + (1 + k) := by omega
  have ha2 : 3 + (1 + k) = 4 + k := by omega
  have hb : 4 + (9 + t * 2) = 9 + (2 + t) * 2 := by omega
  have hs : 5 + (2 + t) = 7 + t := by omega
  rw [ha2] at h1
  rw [ha] at h2
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  rw [ha2, hb] at h2
  rw [hs] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n1e1_even (k t : ℕ) : (cN1 (1 + k) (2 + t * 2) 1) [target_tm]⊢⁺ cP1 (4 + k) (7 + t) := by
  have h1 := n1s1 (1 + k) (t * 2) default default
  rw [Zk_default 8, Zk_default 9] at h1
  have h2 := qa_loop (2 + (1 + k)) (8 + t * 2) 5 default
  have h3 := q1odd k (2 + t) default default
  rw [Zk_default 9] at h3
  have ha : 1 + (2 + (1 + k)) = 3 + (1 + k) := by omega
  have ha2 : 3 + (1 + k) = 4 + k := by omega
  have hb : 5 + (8 + t * 2) = 9 + (2 + t) * 2 := by omega
  have hs : 5 + (2 + t) = 7 + t := by omega
  rw [ha2] at h1
  rw [ha] at h2
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  rw [ha2, hb] at h2
  rw [hs] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n1e0_odd (k t : ℕ) : (cN1 (1 + k) (3 + t * 2) 0) [target_tm]⊢⁺ cT0 (5 + k) (7 + t) := by
  have h1 := n1s0 (1 + k) (1 + t * 2) default default
  rw [Zk_default 8, Zk_default 18] at h1
  have h2 := qa_loop (2 + (1 + k)) (9 + (1 + t * 2)) 4 default
  have h3 := q1even k (2 + t) default default
  rw [z0_default, Zk_default 9] at h3
  have h23 : 2 + (1 + t * 2) = 3 + t * 2 := by omega
  have ha : 1 + (2 + (1 + k)) = 3 + (1 + k) := by omega
  have ha2 : 3 + (1 + k) = 4 + k := by omega
  have hb : 4 + (9 + (1 + t * 2)) = 10 + (2 + t) * 2 := by omega
  have hs : 5 + (2 + t) = 7 + t := by omega
  rw [h23, ha2] at h1
  rw [ha] at h2
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  rw [ha2, hb] at h2
  rw [hs] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n1e1_odd (k t : ℕ) : (cN1 (1 + k) (3 + t * 2) 1) [target_tm]⊢⁺ cT0 (5 + k) (7 + t) := by
  have h1 := n1s1 (1 + k) (1 + t * 2) default default
  rw [Zk_default 8, Zk_default 9] at h1
  have h2 := qa_loop (2 + (1 + k)) (8 + (1 + t * 2)) 5 default
  have h3 := q1even k (2 + t) default default
  rw [z0_default, Zk_default 9] at h3
  have h23 : 2 + (1 + t * 2) = 3 + t * 2 := by omega
  have ha : 1 + (2 + (1 + k)) = 3 + (1 + k) := by omega
  have ha2 : 3 + (1 + k) = 4 + k := by omega
  have hb : 5 + (8 + (1 + t * 2)) = 10 + (2 + t) * 2 := by omega
  have hs : 5 + (2 + t) = 7 + t := by omega
  rw [h23, ha2] at h1
  rw [ha] at h2
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  rw [ha2, hb] at h2
  rw [hs] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n2e0_odd (k b s : ℕ) :
    (cN2 (1 + k) (8 + b) (4 + (7 + s * 2)) 0) [target_tm]⊢⁺ cP2 (3 + k) (16 + b) (6 + s) := by
  have h1 := n2s0 (1 + k) b (7 + s * 2) default default
  rw [Zk_default 6, Zk_default 18] at h1
  have h2 := qb_loop (7 + s * 2) 3 (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + (1 + k)) +> default))))
  have h3 := q2even k b s default default
  rw [Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 3 + (7 + s * 2) = 10 + s * 2 := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n2e1_odd (k b s : ℕ) :
    (cN2 (1 + k) (8 + b) (5 + (6 + s * 2)) 1) [target_tm]⊢⁺ cP2 (3 + k) (16 + b) (6 + s) := by
  have h1 := n2s1 (1 + k) b (6 + s * 2) default default
  rw [Zk_default 6, Zk_default 9] at h1
  have h2 := qb_loop (6 + s * 2) 4 (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + (1 + k)) +> default))))
  have h3 := q2even k b s default default
  rw [Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 4 + (6 + s * 2) = 10 + s * 2 := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n2e0_even (k b s : ℕ) :
    (cN2 (1 + k) (8 + b) (4 + (6 + s * 2)) 0) [target_tm]⊢⁺ cT1 (4 + k) 7 (14 + b) (4 + s) := by
  have h1 := n2s0 (1 + k) b (6 + s * 2) default default
  rw [Zk_default 6, Zk_default 18] at h1
  have h2 := qb_loop (6 + s * 2) 3 (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + (1 + k)) +> default))))
  have h3 := q2odd k b s default default
  rw [z0_default, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 3 + (6 + s * 2) = 9 + s * 2 := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n2e1_even (k b s : ℕ) :
    (cN2 (1 + k) (8 + b) (5 + (5 + s * 2)) 1) [target_tm]⊢⁺ cT1 (4 + k) 7 (14 + b) (4 + s) := by
  have h1 := n2s1 (1 + k) b (5 + s * 2) default default
  rw [Zk_default 6, Zk_default 9] at h1
  have h2 := qb_loop (5 + s * 2) 4 (W01 ^ b +> (Y2 +> (Y2 +> (W1110 ^ (3 + (1 + k)) +> default))))
  have h3 := q2odd k b s default default
  rw [z0_default, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 4 + (5 + s * 2) = 9 + s * 2 := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n3e0_odd (k b z s : ℕ) :
    (cN3 (1 + k) (6 + b) (9 + z) (7 + s * 2) 0) [target_tm]⊢⁺
      cLC (6 + k) (21 + b) 0 0 (9 + z) (4 + s) := by
  have h1 := n3s0 (1 + k) b z (s * 2) default default
  rw [Zk_default 8, Zk_default 18] at h1
  have h2 := qb_loop (7 + s * 2) 3
    (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7 +> (W7 +> (W1110 ^ (3 + (1 + k)) +>
      default)))))))
  have h3 := q3even k (5 + b) z s default default
  rw [Zk_default 6, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 3 + (7 + s * 2) = 10 + s * 2 := by omega
  have hb2 : 6 + (5 + b) = 11 + b := by omega
  have hb3 : 16 + (5 + b) = 21 + b := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  rw [hb2, hb3] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n3e1_odd (k b z s : ℕ) :
    (cN3 (1 + k) (6 + b) (9 + z) (7 + s * 2) 1) [target_tm]⊢⁺
      cLC (6 + k) (21 + b) 0 0 (9 + z) (4 + s) := by
  have h1 := n3s1 (1 + k) b z (s * 2) default default
  rw [Zk_default 8, Zk_default 9] at h1
  have h2 := qb_loop (6 + s * 2) 4
    (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7 +> (W7 +> (W1110 ^ (3 + (1 + k)) +>
      default)))))))
  have h3 := q3even k (5 + b) z s default default
  rw [Zk_default 6, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (1 + k) = 4 + k := by omega
  have hb : 4 + (6 + s * 2) = 10 + s * 2 := by omega
  have hb2 : 6 + (5 + b) = 11 + b := by omega
  have hb3 : 16 + (5 + b) = 21 + b := by omega
  rw [ha, hb] at h2
  rw [ha] at h1
  rw [hb2, hb3] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n3e0_even (k b z s : ℕ) :
    (cN3 (10 + k) (6 + b) (9 + z) (7 + (1 + s * 2)) 0) [target_tm]⊢⁺
      (default <{{stA}} LCc 5 14 (6 + k) 15 (6 + (5 + b)) 6 (6 + z) (2 + (1 + s)) default) := by
  have h1 := n3s0 (10 + k) b z (1 + s * 2) default default
  rw [Zk_default 8, Zk_default 18] at h1
  have h2 := qb_loop (7 + (1 + s * 2)) 3
    (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7 +> (W7 +> (W1110 ^ (3 + (10 + k)) +>
      default)))))))
  have h3 := q3odd k (5 + b) z (1 + s) default default
  rw [Zk_default 13, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (10 + k) = 13 + k := by omega
  have hb : 3 + (7 + (1 + s * 2)) = 9 + (1 + s) * 2 := by omega
  have hb2 : 11 + b = 6 + (5 + b) := by omega
  rw [ha, hb, hb2] at h2
  rw [ha, hb2] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem n3e1_even (k b z s : ℕ) :
    (cN3 (10 + k) (6 + b) (9 + z) (7 + (1 + s * 2)) 1) [target_tm]⊢⁺
      (default <{{stA}} LCc 5 14 (6 + k) 15 (6 + (5 + b)) 6 (6 + z) (2 + (1 + s)) default) := by
  have h1 := n3s1 (10 + k) b z (1 + s * 2) default default
  rw [Zk_default 8, Zk_default 9] at h1
  have h2 := qb_loop (6 + (1 + s * 2)) 4
    (W01 ^ (6 + z) +> (R6 +> (W01 ^ (11 + b) +> (R6 +> (W7 +> (W7 +> (W1110 ^ (3 + (10 + k)) +>
      default)))))))
  have h3 := q3odd k (5 + b) z (1 + s) default default
  rw [Zk_default 13, Zk_default 9] at h3
  dsimp only [list_pow_zero, ListBlank.append_nil] at h2
  have ha : 3 + (10 + k) = 13 + k := by omega
  have hb : 4 + (6 + (1 + s * 2)) = 9 + (1 + s) * 2 := by omega
  have hb2 : 11 + b = 6 + (5 + b) := by omega
  rw [ha, hb, hb2] at h2
  rw [ha, hb2] at h1
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

theorem LCm_eq (x y n Z c d : ℕ) (r : ListBlank (Fin 2)) :
    LCm x y n Z c d r = LC x (y + n + Z) 0 0 c d r := by
  unfold LCm LC
  dsimp only [list_pow_zero, ListBlank.append_nil]
  have h : y + n + Z = y + (n + Z) := by omega
  rw [h, list_pow_add W10 y (n + Z), list_pow_add W10 n Z,
    ← ListBlank.append_append, ← ListBlank.append_append]

theorem LCc_eq (x y z Z c1 n c2 d : ℕ) (r : ListBlank (Fin 2)) :
    LCc x y z Z c1 n c2 d r = LC x y z Z (c1 + n + c2) d r := by
  unfold LCc LC
  have h : c1 + n + c2 = c1 + (n + c2) := by omega
  rw [h, list_pow_add W10 c1 (n + c2), list_pow_add W10 n c2,
    ← ListBlank.append_append, ← ListBlank.append_append]

inductive P : Cfg (Fin 2) (Fin 6) → Prop where
  | PN1 (a b d : ℕ) : 24 ≤ a → 7 ≤ b → 4 * a + 29 ≤ 5 * b + 24 * d → P (cN1 a b d)
  | PP1 (a s : ℕ) : 22 ≤ a → 6 ≤ s → 4 * a + 74 ≤ 24 * s → P (cP1 a s)
  | PP2 (a b s : ℕ) : 23 ≤ a → 7 ≤ b → 6 ≤ s → 4 * a + 81 ≤ 5 * b + 24 * s → P (cP2 a b s)
  | PT0 (a s : ℕ) : 28 ≤ a → 16 ≤ s → 2 * a + 22 ≤ 5 * s → P (cT0 a s)
  | PT1 (a b c d : ℕ) : 24 ≤ a → 7 ≤ b → 6 ≤ c → 6 ≤ d → 2 * a + 22 ≤ 5 * d →
      8 * a + 702 ≤ 50 * c + 65 * d → 676 ≤ 40 * b + 26 * c + 17 * d + 49 * a →
      261 ≤ 15 * d + 2 * a → 4 * a + 29 ≤ 5 * b + 12 * c + 24 * d → P (cT1 a b c d)
  | PLC (x y z Z c d : ℕ) : 1 ≤ z → 6 ≤ y → 8 ≤ Z → 7 ≤ c → 2 * z + 18 ≤ 5 * d →
      40 * x + 8 * z + 606 ≤ 50 * c + 65 * d → 32 * x + 649 ≤ 40 * Z + 26 * c + 17 * d + 49 * z →
      4 * x ≤ 5 * y + 12 * Z + 37 → 235 ≤ 10 * x + 15 * d + 2 * z →
      4 * x ≤ 5 * y + 5 * Z + 12 * c + 9 → P (cLC x y z Z c d)
  | PLH (x y c d : ℕ) : 9 ≤ y → 7 ≤ c → 43 ≤ 2 * x + 3 * d →
      8 * x + 118 ≤ 10 * c + 13 * d → 4 * x ≤ 5 * y + 12 * c + 2 → P (cLC x y 0 0 c d)
  | PN2 (a b c d : ℕ) : 8 ≤ b → 11 ≤ c → 45 ≤ 2 * a + 3 * d →
      8 * a + 150 ≤ 10 * c + 13 * d → 4 * a + 37 ≤ 5 * b + 12 * c → P (cN2 a b c d)
  | PN3 (a b z c d : ℕ) : 6 ≤ b → 9 ≤ z → 7 ≤ c → 45 ≤ 2 * a + 3 * d →
      8 * a + 73 ≤ 10 * c + 13 * d → 32 * a + 623 ≤ 40 * z + 26 * c + 17 * d →
      4 * a ≤ 5 * b + 12 * z + 37 → P (cN3 a b z c d)

theorem step_N1 (a b d : ℕ) (ha : 24 ≤ a) (hb : 7 ≤ b) (hi : 4 * a + 29 ≤ 5 * b + 24 * d) :
    ∃ c', ((cN1 a b d) [target_tm]⊢⁺ c') ∧ P c' := by
  rcases d with _ | _ | _ | _ | d
  · have ha1 : a = 1 + (a - 1) := by omega
    rcases nat_even_or_odd_two_mul b with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hb1 : b = 2 + (t - 1) * 2 := by omega
      rw [ha1, hb1]
      exact ⟨_, n1e0_even (a - 1) (t - 1), P.PP1 _ _ (by omega) (by omega) (by omega)⟩
    · have hb1 : b = 3 + (t - 1) * 2 := by omega
      rw [ha1, hb1]
      exact ⟨_, n1e0_odd (a - 1) (t - 1), P.PT0 _ _ (by omega) (by omega) (by omega)⟩
  · have ha1 : a = 1 + (a - 1) := by omega
    rcases nat_even_or_odd_two_mul b with ⟨t, ht⟩ | ⟨t, ht⟩
    · have hb1 : b = 2 + (t - 1) * 2 := by omega
      rw [ha1, hb1]
      exact ⟨_, n1e1_even (a - 1) (t - 1), P.PP1 _ _ (by omega) (by omega) (by omega)⟩
    · have hb1 : b = 3 + (t - 1) * 2 := by omega
      rw [ha1, hb1]
      exact ⟨_, n1e1_odd (a - 1) (t - 1), P.PT0 _ _ (by omega) (by omega) (by omega)⟩
  · have hb1 : b = 2 + (b - 2) := by omega
    rw [hb1]
    have h := n1_d2 a (b - 2) default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN1 _ _ _ (by omega) (by omega) (by omega)⟩
  · have hb1 : b = 2 + (b - 2) := by omega
    rw [hb1]
    have h := n1_d3 a (b - 2) default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN1 _ _ _ (by omega) (by omega) (by omega)⟩
  · have hb1 : b = 2 + (b - 2) := by omega
    have hd1 : d + 4 = 4 + d := by omega
    rw [hb1, hd1]
    have h := n1_cyc a (b - 2) d default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN1 _ _ _ (by omega) (by omega) (by omega)⟩

theorem step_P1 (a s : ℕ) (ha : 22 ≤ a) (hs : 6 ≤ s) (hi : 4 * a + 74 ≤ 24 * s) :
    ∃ c', ((cP1 a s) [target_tm]⊢⁺ c') ∧ P c' := by
  have hs1 : s = 6 + (s - 6) := by omega
  rw [hs1]
  have h := p1_r a (s - 6) default default
  rw [Zk_default 6] at h
  exact ⟨_, h, P.PN1 _ _ _ (by omega) (by omega) (by omega)⟩

theorem step_P2 (a b s : ℕ) (ha : 23 ≤ a) (hb : 7 ≤ b) (hs : 6 ≤ s)
    (hi : 4 * a + 81 ≤ 5 * b + 24 * s) :
    ∃ c', ((cP2 a b s) [target_tm]⊢⁺ c') ∧ P c' := by
  have hs1 : s = 6 + (s - 6) := by omega
  have hb1 : b = 6 + (b - 6) := by omega
  rw [hs1, hb1]
  have h := p2_r a (b - 6) (s - 6) default default
  rw [Zk_default 2] at h
  exact ⟨_, h, P.PN1 _ _ _ (by omega) (by omega) (by omega)⟩

theorem step_T0 (a s : ℕ) (ha : 28 ≤ a) (hs : 16 ≤ s) (hi : 2 * a + 22 ≤ 5 * s) :
    ∃ c', ((cT0 a s) [target_tm]⊢⁺ c') ∧ P c' := by
  have hs1 : s = 8 + (s - 8) := by omega
  have ha1 : a = 14 + (a - 14) := by omega
  rw [hs1, ha1]
  have h := t0_r (a - 14) (s - 8) default default
  rw [Zk_default 12] at h
  exact ⟨_, h, P.PLC _ _ _ _ _ _
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_T1 (a b c d : ℕ) (ha : 24 ≤ a) (hb : 7 ≤ b) (hc : 6 ≤ c) (hd : 6 ≤ d)
    (h1 : 2 * a + 22 ≤ 5 * d) (h2 : 8 * a + 702 ≤ 50 * c + 65 * d)
    (h3 : 676 ≤ 40 * b + 26 * c + 17 * d + 49 * a)
    (h4 : 261 ≤ 15 * d + 2 * a) (h5 : 4 * a + 29 ≤ 5 * b + 12 * c + 24 * d) :
    ∃ c', ((cT1 a b c d) [target_tm]⊢⁺ c') ∧ P c' := by
  have e1 : a = 9 + (a - 9) := by omega
  have e2 : b = 7 + (b - 7) := by omega
  have e3 : c = 6 + (c - 6) := by omega
  have e4 : d = 6 + (d - 6) := by omega
  rw [e1, e2, e3, e4]
  have h := t1_r (a - 9) (b - 7) (c - 6) (d - 6) default default
  rw [Zk_default 4] at h
  exact ⟨_, h, P.PLC _ _ _ _ _ _
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_LC (x y z Z c d : ℕ) (hz : 1 ≤ z) (hy : 6 ≤ y) (hZ : 8 ≤ Z) (hc : 7 ≤ c)
    (h1 : 2 * z + 18 ≤ 5 * d) (h2 : 40 * x + 8 * z + 606 ≤ 50 * c + 65 * d)
    (h3 : 32 * x + 649 ≤ 40 * Z + 26 * c + 17 * d + 49 * z)
    (h4 : 4 * x ≤ 5 * y + 12 * Z + 37) (h5 : 235 ≤ 10 * x + 15 * d + 2 * z)
    (h6 : 4 * x ≤ 5 * y + 5 * Z + 12 * c + 9) :
    ∃ c', ((cLC x y z Z c d) [target_tm]⊢⁺ c') ∧ P c' := by
  have e1 : y = 6 + (y - 6) := by omega
  have e2 : Z = 8 + (Z - 8) := by omega
  have e3 : c = 7 + (c - 7) := by omega
  have e4 : d = 4 + (d - 4) := by omega
  rcases z with _ | _ | _ | _ | _ | _ | z
  · omega
  · rw [e1, e2, e3, e4]
    have h := lc_z1 x (y - 6) (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 4] at h
    exact ⟨_, h, P.PN3 _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [e1, e2, e3, e4]
    have h := lc_z2 x (y - 6) (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 4] at h
    exact ⟨_, h, P.PN3 _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [e1, e2, e3, e4]
    have h := lc_z3 x (y - 6) (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 8, LCm_eq] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [e1, e2, e3, e4]
    have h := lc_z4 x (y - 6) (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 8, LCm_eq] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · rw [e1, e2, e3, e4]
    have h := lc_z5 x (y - 6) (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 8, LCm_eq] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have ez : z + 6 = 6 + z := by omega
    rw [e1, ez, e2, e3, e4]
    have h := lc_cyc x (y - 6) z (Z - 8) (c - 7) (d - 4) default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PLC _ _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_LH (x y c d : ℕ) (hy : 9 ≤ y) (hc : 7 ≤ c) (h1 : 43 ≤ 2 * x + 3 * d)
    (h2 : 8 * x + 118 ≤ 10 * c + 13 * d) (h3 : 4 * x ≤ 5 * y + 12 * c + 2) :
    ∃ c', ((cLC x y 0 0 c d) [target_tm]⊢⁺ c') ∧ P c' := by
  have e1 : y = 6 + (y - 6) := by omega
  have e3 : c = 7 + (c - 7) := by omega
  rw [e1, e3]
  have h := lh_r x (y - 6) (c - 7) d default default
  rw [Zk_default 2] at h
  exact ⟨_, h, P.PN2 _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_N2 (a b c d : ℕ) (hb : 8 ≤ b) (hc : 11 ≤ c) (h1 : 45 ≤ 2 * a + 3 * d)
    (h2 : 8 * a + 150 ≤ 10 * c + 13 * d) (h3 : 4 * a + 37 ≤ 5 * b + 12 * c) :
    ∃ c', ((cN2 a b c d) [target_tm]⊢⁺ c') ∧ P c' := by
  rcases d with _ | _ | _ | _ | d
  · have ea : a = 1 + (a - 1) := by omega
    have eb : b = 8 + (b - 8) := by omega
    rcases nat_even_or_odd_two_mul c with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ec : c = 4 + (6 + (t - 5) * 2) := by omega
      rw [ea, eb, ec]
      exact ⟨_, n2e0_even (a - 1) (b - 8) (t - 5), P.PT1 _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)⟩
    · have ec : c = 4 + (7 + (t - 5) * 2) := by omega
      rw [ea, eb, ec]
      exact ⟨_, n2e0_odd (a - 1) (b - 8) (t - 5), P.PP2 _ _ _
        (by omega) (by omega) (by omega) (by omega)⟩
  · have ea : a = 1 + (a - 1) := by omega
    have eb : b = 8 + (b - 8) := by omega
    rcases nat_even_or_odd_two_mul c with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ec : c = 5 + (5 + (t - 5) * 2) := by omega
      rw [ea, eb, ec]
      exact ⟨_, n2e1_even (a - 1) (b - 8) (t - 5), P.PT1 _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)⟩
    · have ec : c = 5 + (6 + (t - 5) * 2) := by omega
      rw [ea, eb, ec]
      exact ⟨_, n2e1_odd (a - 1) (b - 8) (t - 5), P.PP2 _ _ _
        (by omega) (by omega) (by omega) (by omega)⟩
  · have eb : b = 6 + (b - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    rw [eb, ec]
    have h := n2_d2 a (b - 6) (c - 7) default default
    rw [Zk_default 6] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have eb : b = 6 + (b - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    rw [eb, ec]
    have h := n2_d3 a (b - 6) (c - 7) default default
    rw [Zk_default 6] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have eb : b = 6 + (b - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    have ed : d + 4 = 4 + d := by omega
    rw [eb, ec, ed]
    have h := n2_cyc a (b - 6) (c - 7) d default default
    rw [Zk_default 6] at h
    exact ⟨_, h, P.PLH _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_N3 (a b z c d : ℕ) (hb : 6 ≤ b) (hz : 9 ≤ z) (hc : 7 ≤ c)
    (h1 : 45 ≤ 2 * a + 3 * d) (h2 : 8 * a + 73 ≤ 10 * c + 13 * d)
    (h3 : 32 * a + 623 ≤ 40 * z + 26 * c + 17 * d) (h4 : 4 * a ≤ 5 * b + 12 * z + 37) :
    ∃ c', ((cN3 a b z c d) [target_tm]⊢⁺ c') ∧ P c' := by
  have eb : b = 6 + (b - 6) := by omega
  rcases d with _ | _ | _ | _ | d
  · have ez : z = 9 + (z - 9) := by omega
    rcases nat_even_or_odd_two_mul c with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ec : c = 7 + (1 + (t - 4) * 2) := by omega
      have ea : a = 10 + (a - 10) := by omega
      rw [ea, eb, ez, ec]
      have h := n3e0_even (a - 10) (b - 6) (z - 9) (t - 4)
      rw [LCc_eq] at h
      exact ⟨_, h, P.PLC _ _ _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)⟩
    · have ec : c = 7 + (t - 3) * 2 := by omega
      have ea : a = 1 + (a - 1) := by omega
      rw [ea, eb, ez, ec]
      exact ⟨_, n3e0_odd (a - 1) (b - 6) (z - 9) (t - 3), P.PLH _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have ez : z = 9 + (z - 9) := by omega
    rcases nat_even_or_odd_two_mul c with ⟨t, ht⟩ | ⟨t, ht⟩
    · have ec : c = 7 + (1 + (t - 4) * 2) := by omega
      have ea : a = 10 + (a - 10) := by omega
      rw [ea, eb, ez, ec]
      have h := n3e1_even (a - 10) (b - 6) (z - 9) (t - 4)
      rw [LCc_eq] at h
      exact ⟨_, h, P.PLC _ _ _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega)⟩
    · have ec : c = 7 + (t - 3) * 2 := by omega
      have ea : a = 1 + (a - 1) := by omega
      rw [ea, eb, ez, ec]
      exact ⟨_, n3e1_odd (a - 1) (b - 6) (z - 9) (t - 3), P.PLH _ _ _ _
        (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have ez : z = 6 + (z - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    rw [eb, ez, ec]
    have h := n3_d2 a (b - 6) (z - 6) (c - 7) default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN3 _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have ez : z = 6 + (z - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    rw [eb, ez, ec]
    have h := n3_d3 a (b - 6) (z - 6) (c - 7) default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN3 _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩
  · have ez : z = 6 + (z - 6) := by omega
    have ec : c = 7 + (c - 7) := by omega
    have ed : d + 4 = 4 + d := by omega
    rw [eb, ez, ec, ed]
    have h := n3_cyc a (b - 6) (z - 6) (c - 7) d default default
    rw [Zk_default 8] at h
    exact ⟨_, h, P.PN3 _ _ _ _ _
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)⟩

theorem step_P (c : Cfg (Fin 2) (Fin 6)) (hc : P c) :
    ∃ c', (c [target_tm]⊢⁺ c') ∧ P c' := by
  cases hc with
  | PN1 a b d h1 h2 h3 => exact step_N1 a b d h1 h2 h3
  | PP1 a s h1 h2 h3 => exact step_P1 a s h1 h2 h3
  | PP2 a b s h1 h2 h3 h4 => exact step_P2 a b s h1 h2 h3 h4
  | PT0 a s h1 h2 h3 => exact step_T0 a s h1 h2 h3
  | PT1 a b c d h1 h2 h3 h4 h5 h6 h7 h8 h9 => exact step_T1 a b c d h1 h2 h3 h4 h5 h6 h7 h8 h9
  | PLC x y z Z c d h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact step_LC x y z Z c d h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
  | PLH x y c d h1 h2 h3 h4 h5 => exact step_LH x y c d h1 h2 h3 h4 h5
  | PN2 a b c d h1 h2 h3 h4 h5 => exact step_N2 a b c d h1 h2 h3 h4 h5
  | PN3 a b z c d h1 h2 h3 h4 h5 h6 h7 => exact step_N3 a b z c d h1 h2 h3 h4 h5 h6 h7



private def stem_s0 : RunWin.SymCfg (Fin 2) (Fin 6) := ⟨some 0, .mid [] 0 []⟩

private def stem_s1 : RunWin.SymCfg (Fin 2) (Fin 6) :=
  ⟨some stA, .mid [] 0 ((([0] : List (Fin 2)) ^ 2) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin
    2)) ^ 4) ++ (W1000 ^ 4) ++ (([0] : List (Fin 2)) ^ 2) ++ ([1] : List (Fin 2)) ++ (([0] : List
    (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++
    (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] :
    List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^
    5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] :
    List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin
    2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++
    ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++ (([0] : List
    (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++
    (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] :
    List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^
    5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 3) ++ ([1, 0, 1] : List (Fin 2)))⟩

private def stem_s2 : RunWin.SymCfg (Fin 2) (Fin 6) :=
  ⟨some stA, .mid [] 0 ((([0] : List (Fin 2)) ^ 6) ++ (W1000 ^ 11) ++ (W10 ^ 30) ++ (([0] : List
    (Fin 2)) ^ 4) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++
    (([0] : List (Fin 2)) ^ 3) ++ (W10 ^ 17) ++ (([0] : List (Fin 2)) ^ 2) ++ ([1] : List (Fin 2))
    ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 7) ++ ([1] :
    List (Fin 2)) ++ (([0] : List (Fin 2)) ^ 5) ++ ([1] : List (Fin 2)) ++ (([0] : List (Fin 2)) ^
    3) ++ ([1, 0, 1] : List (Fin 2)))⟩

private def stem_s3 : RunWin.SymCfg (Fin 2) (Fin 6) :=
  ⟨some stA, .mid [] 0 (Zk 6 ++ W1000 ^ 14 ++ W10 ^ 37 ++ S3w ^ 11 ++ [1, 0, 1])⟩

private theorem stem_chk1 :
    (RunWin.symRun true true target_tm stem_s0 8826 == some stem_s1) = true := by
  decide +kernel

private theorem stem_chk2 :
    (RunWin.symRun true true target_tm stem_s1 8985 == some stem_s2) = true := by
  decide +kernel

private theorem stem_chk3 :
    (RunWin.symRun true true target_tm stem_s2 11490 == some stem_s3) = true := by
  decide +kernel

theorem init_reaches_cP2 : (init []) [target_tm]⊢* cP2 14 37 11 := by
  have h1 := RunWin.symRun_blank_star target_tm stem_s0 stem_s1 8826 (eq_of_beq stem_chk1)
  have h2 := RunWin.symRun_blank_star target_tm stem_s1 stem_s2 8985 (eq_of_beq stem_chk2)
  have h3 := RunWin.symRun_blank_star target_tm stem_s2 stem_s3 11490 (eq_of_beq stem_chk3)
  have hall := ReachesStar.trans h1 (ReachesStar.trans h2 h3)
  rw [RunWin.eval_init]
  have hend : stem_s3.eval default default = cP2 14 37 11 := by
    simp only [stem_s3, RunWin.SymCfg.eval, RunWin.SymCursor.eval, cP2, P2,
      Cfg.headLeft, ListBlank.head_default, ListBlank.tail_default,
      ListBlank.append_nil, ListBlank.append_append, List.append_assoc]
    rfl
  rw [← hend]
  exact hall

theorem init_reaches_cN1 : (init []) [target_tm]⊢* cN1 24 73 3 := by
  have h0 := init_reaches_cP2
  have m1 := p2_r 14 31 5 default default
  rw [Zk_default 2] at m1
  have m2 := n1_cyc 15 35 5 default default
  rw [Zk_default 8] at m2
  have m3 := n1_cyc 18 47 3 default default
  rw [Zk_default 8] at m3
  have m4 := n1_cyc 21 59 1 default default
  rw [Zk_default 8] at m4
  exact ReachesStar.trans h0
    (ReachesPlus.to_star
      (ReachesPlus.trans m1 (ReachesPlus.trans m2 (ReachesPlus.trans m3 m4))))

theorem init_P : P (cN1 24 73 3) :=
  P.PN1 24 73 3 (by omega) (by omega) (by omega)

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact IsNotHalt.of_reachesPlus_invariant init_reaches_cN1 init_P step_P


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LE_1RCHHH_1RD1RE_1LA0RF_0RC0LA_0LC0RB
