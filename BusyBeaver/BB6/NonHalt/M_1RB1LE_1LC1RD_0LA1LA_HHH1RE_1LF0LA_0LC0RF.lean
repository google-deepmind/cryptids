/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic
import BusyBeaver.Longitudinal

/-!
# Busy Beaver Machine `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`, `BusyBeaver.Longitudinal`
and defines `target_tm` for `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LE_1LC1RD_0LA1LA_---1RE_1LF0LA_0LC0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option linter.constructorNameAsVariable false
set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

open BusyBeaver.Counter

-- ============================================================================
-- 0. Partner Machine `tm1` (`TM1`) & Mirror-Permutation Transfer for Holdout #458
-- ============================================================================

/-- Transition function of `TM1` (`1RB1LD_0RC1RC_1LA1RE_---1LE_1RF0RC_0RB0LF`),
which is the left-right mirror of `target_tm` under state permutation `phi`. -/
def tm1 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.left)

def phi : Fin 6 → Fin 6
  | 0 => 2
  | 1 => 0
  | 2 => 1
  | 3 => 3
  | 4 => 4
  | 5 => 5

def mirrorCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map phi, ⟨c.tape.1, c.tape.3, c.tape.2⟩⟩

lemma step_mirrorCfg (c : Cfg (Fin 2) (Fin 6)) :
    step tm1 (mirrorCfg c) = (step target_tm c).map mirrorCfg := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    first | rfl | omega

lemma multiStep_mirrorCfg (n : Nat) (c : Cfg (Fin 2) (Fin 6)) :
    multiStep tm1 (mirrorCfg c) n = (multiStep target_tm c n).map mirrorCfg := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ', multiStep_succ', step_mirrorCfg]
    rcases step target_tm c with _ | c'
    · rfl
    · exact ih c'

lemma reachesStar_mirrorCfg {c c' : Cfg (Fin 2) (Fin 6)}
    (h : c [target_tm]⊢* c') :
    (mirrorCfg c) [tm1]⊢* (mirrorCfg c') := by
  rcases h with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  rw [multiStep_mirrorCfg, hn]
  rfl

lemma isSome_step_of_mirrorCfg {c : Cfg (Fin 2) (Fin 6)}
    (h : (step tm1 (mirrorCfg c)).isSome) :
    (step target_tm c).isSome := by
  rw [step_mirrorCfg, Option.isSome_map] at h
  exact h

def initC : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{(2 : Fin 6)}}> default

lemma mirrorCfg_init : mirrorCfg (init []) = initC :=
  rfl

-- ============================================================================
-- 1. Canonical Configuration Family `Kr n a b c d` & `Ev N X`
-- ============================================================================

def G : List (Fin 2) :=
  [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
   0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0]

def l39Bits : List (Fin 2) :=
  [1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0,
   0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1]

def l41Bits : List (Fin 2) := [0, 1] ++ l39Bits

def krRightList (n a b c d : Nat) : List (Fin 2) :=
  G ++ [1] ++ ([1, 1] : List (Fin 2)) ^ n ++
  [0] ++ ([1, 1] : List (Fin 2)) ^ a ++
  [0, 1, 1, 0] ++ ([1, 1] : List (Fin 2)) ^ b ++
  [0, 0, 0, 0, 0, 0, 1] ++ ([1, 1] : List (Fin 2)) ^ c ++
  [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] ++ ([1, 1] : List (Fin 2)) ^ d ++
  [0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1]

def Kr (n a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{5}} (krRightList n a b c d +> default)

lemma Kr_congr {n1 n2 a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (hn : n1 = n2) (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    Kr n1 a1 b1 c1 d1 = Kr n2 a2 b2 c2 d2 := by
  subst hn; subst ha; subst hb; subst hc; subst hd; rfl

def Ev (N X : Nat) : Cfg (Fin 2) (Fin 6) :=
  Kr N (4 * X + 26) (2 * X + 32) 17 9

-- ============================================================================
-- 2. Elementary 2-Cell Shift Lemmas, Word Commutations & Chaotic-Edge Jumps
-- ============================================================================

lemma shiftR_2_11_one (l r : ListBlank (Fin 2)) :
    (l {{2}}> ([1, 1] +> r)) [tm1]⊢* (([0, 1] +> l) {{2}}> r) :=
  run_local_spec (tm := tm1) (n := 2)
    (s1 := ⟨[], [1, 1], 2, .right⟩) (s2 := ⟨[0, 1], [], 2, .right⟩) rfl l r

lemma shiftR_2_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{2}}> (([1, 1] : List (Fin 2)) ^ k +> r)) [tm1]⊢*
      ((([0, 1] : List (Fin 2)) ^ k +> l) {{2}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k r,
        right_pow_succ_right ([0, 1] : List (Fin 2)) k l]
    exact stepStar_trans (shiftR_2_11_one l _) (ih ([0, 1] +> l))

lemma shiftR_2_11_plus (l r : ListBlank (Fin 2)) :
    (l {{2}}> ([1] +> ([1] +> r))) [tm1]⊢⁺ (([0, 1] +> l) {{2}}> r) := by
  have h1 : (l {{2}}> ([1] +> ([1] +> r))) [tm1]⊢ (([1] +> l) {{4}}> ([1] +> r)) :=
    step_local_spec (tm := tm1) (s1 := ⟨[], [1], 2, .right⟩) (s2 := ⟨[1], [], 4, .right⟩)
      rfl l ([1] +> r)
  have h2 : (([1] +> l) {{4}}> ([1] +> r)) [tm1]⊢ (([0, 1] +> l) {{2}}> r) :=
    step_local_spec (tm := tm1) (s1 := ⟨[1], [1], 4, .right⟩) (s2 := ⟨[0, 1], [], 2, .right⟩)
      rfl l r
  exact stepPlus_trans (step_stepPlus tm1 _ _ h1) (step_stepPlus tm1 _ _ h2)

lemma shiftR_4_11_one (l r : ListBlank (Fin 2)) :
    (l {{4}}> ([1, 1] +> r)) [tm1]⊢* (([1, 0] +> l) {{4}}> r) :=
  run_local_spec (tm := tm1) (n := 2)
    (s1 := ⟨[], [1, 1], 4, .right⟩) (s2 := ⟨[1, 0], [], 4, .right⟩) rfl l r

lemma shiftR_4_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{4}}> (([1, 1] : List (Fin 2)) ^ k +> r)) [tm1]⊢*
      ((([1, 0] : List (Fin 2)) ^ k +> l) {{4}}> r) := by
  induction k generalizing l with
  | zero => exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k r,
        right_pow_succ_right ([1, 0] : List (Fin 2)) k l]
    exact stepStar_trans (shiftR_4_11_one l _) (ih ([1, 0] +> l))

lemma shiftR_4_11_plus (l r : ListBlank (Fin 2)) :
    (l {{4}}> ([1] +> ([1] +> r))) [tm1]⊢⁺ (([1, 0] +> l) {{4}}> r) := by
  have h1 : (l {{4}}> ([1] +> ([1] +> r))) [tm1]⊢ (([0] +> l) {{2}}> ([1] +> r)) :=
    step_local_spec (tm := tm1) (s1 := ⟨[], [1], 4, .right⟩) (s2 := ⟨[0], [], 2, .right⟩)
      rfl l ([1] +> r)
  have h2 : (([0] +> l) {{2}}> ([1] +> r)) [tm1]⊢ (([1, 0] +> l) {{4}}> r) :=
    step_local_spec (tm := tm1) (s1 := ⟨[0], [1], 2, .right⟩) (s2 := ⟨[1, 0], [], 4, .right⟩)
      rfl l r
  exact stepPlus_trans (step_stepPlus tm1 _ _ h1) (step_stepPlus tm1 _ _ h2)

lemma shiftL_5_10_one (l r : ListBlank (Fin 2)) :
    (([1, 0] +> l) <{{5}} ([0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0] +> ([1, 1] +> r))) :=
  run_local_spec (tm := tm1) (n := 12)
    (s1 := ⟨[1, 0], [0, 0], 5, .left⟩) (s2 := ⟨[], [0, 0, 1, 1], 5, .left⟩) rfl l r

lemma shiftL_5_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((([1, 0] : List (Fin 2)) ^ k +> l) <{{5}} ([0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing r with
  | zero => exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 0] : List (Fin 2)) k l,
        right_pow_succ_right ([1, 1] : List (Fin 2)) k r]
    exact stepStar_trans (shiftL_5_10_one _ r) (ih ([1, 1] +> r))

lemma shiftL_5_01_one (l r : ListBlank (Fin 2)) :
    (([0, 1] +> l) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0, 0] +> ([1, 1] +> r))) :=
  run_local_spec (tm := tm1) (n := 12)
    (s1 := ⟨[0, 1], [0, 0, 0], 5, .left⟩) (s2 := ⟨[], [0, 0, 0, 1, 1], 5, .left⟩) rfl l r

lemma shiftL_5_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((([0, 1] : List (Fin 2)) ^ k +> l) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0, 0] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing r with
  | zero => exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([0, 1] : List (Fin 2)) k l,
        right_pow_succ_right ([1, 1] : List (Fin 2)) k r]
    exact stepStar_trans (shiftL_5_01_one _ r) (ih ([1, 1] +> r))

lemma rot_w11 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2)) ^ k +> ([1] +> s)) =
      [1] +> (([1, 1] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k,
        right_pow_succ ([1, 1] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

lemma rot_w10 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k +> ([1] +> s)) =
      [1] +> (([0, 1] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([1, 0] : List (Fin 2)) k,
        right_pow_succ ([0, 1] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

lemma rot_w01 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k +> ([0] +> s)) =
      [0] +> (([1, 0] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([0, 1] : List (Fin 2)) k,
        right_pow_succ ([1, 0] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

lemma zero_list_default : ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
  zero_cons_default

lemma zeros2_list_default : ([0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := by
  change [0] +> ([0] +> default) = default
  rw [zero_list_default, zero_list_default]

lemma nil_list_default : ([] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := rfl

lemma edge_in_raw (r : ListBlank (Fin 2)) :
    (((l39Bits ++ [0]) +> default) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (([] +> default) <{{5}} (G +> r)) :=
  run_local_spec (tm := tm1) (n := 524)
    (s1 := ⟨l39Bits ++ [0], [0, 0, 0], 5, .left⟩)
    (s2 := ⟨[], G, 5, .left⟩) rfl default r

lemma edge_in (r : ListBlank (Fin 2)) :
    ((l39Bits +> default) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (default <{{5}} (G +> r)) := by
  have h := edge_in_raw r
  rw [listblank_append_assoc l39Bits [0] default, zero_list_default, nil_list_default] at h
  exact h

lemma edge_out_raw (r : ListBlank (Fin 2)) :
    (([0, 0] +> default) <{{5}} ((G ++ [1]) +> r)) [tm1]⊢*
      (((l41Bits ++ [0]) +> default) {{2}}> ([1, 1, 1, 1] +> r)) :=
  run_local_spec (tm := tm1) (n := 237)
    (s1 := ⟨[0, 0], G ++ [1], 5, .left⟩)
    (s2 := ⟨l41Bits ++ [0], [1, 1, 1, 1], 2, .right⟩) rfl default r

lemma edge_out (r : ListBlank (Fin 2)) :
    (default <{{5}} (G +> ([1] +> r))) [tm1]⊢*
      ((l41Bits +> default) {{2}}> ([1, 1, 1, 1] +> r)) := by
  have h := edge_out_raw r
  rw [zeros2_list_default, listblank_append_assoc l41Bits [0] default, zero_list_default,
      listblank_append_assoc G [1] r] at h
  exact h

-- ============================================================================
-- 3. Compressed Symbolic Bouncer Verifier (`Q6`, `SymTok`, `runSym`, `checkSym`)
-- ============================================================================

inductive Q6 where
  | q0 | q1 | q2 | q3 | q4 | q5
  deriving DecidableEq

def q6Eq : Q6 → Q6 → Bool
  | .q0, .q0 | .q1, .q1 | .q2, .q2 | .q3, .q3 | .q4, .q4 | .q5, .q5 => true
  | _, _ => false

lemma q6Eq_sound {q1 q2 : Q6} (h : q6Eq q1 q2 = true) : q1 = q2 := by
  cases q1 <;> cases q2 <;> first | rfl | nomatch h

def dirEq : Dir → Dir → Bool
  | .left, .left | .right, .right => true
  | _, _ => false

lemma dirEq_sound {d1 d2 : Dir} (h : dirEq d1 d2 = true) : d1 = d2 := by
  cases d1 <;> cases d2 <;> first | rfl | nomatch h

def evalQ : Q6 → Fin 6
  | .q0 => 0
  | .q1 => 1
  | .q2 => 2
  | .q3 => 3
  | .q4 => 4
  | .q5 => 5

def evalBit : Bool → Fin 2
  | false => 0
  | true => 1

def stepQ : Q6 → Bool → Option (Q6 × Bool × Dir)
  | .q0, false => some (.q1, true, .right)
  | .q0, true  => some (.q3, true, .left)
  | .q1, false => some (.q2, false, .right)
  | .q1, true  => some (.q2, true, .right)
  | .q2, false => some (.q0, true, .left)
  | .q2, true  => some (.q4, true, .right)
  | .q3, false => none
  | .q3, true  => some (.q4, true, .left)
  | .q4, false => some (.q5, true, .right)
  | .q4, true  => some (.q2, false, .right)
  | .q5, false => some (.q1, false, .right)
  | .q5, true  => some (.q5, false, .left)

lemma stepQ_sound {q q' : Q6} {x w_bit : Bool} {d' : Dir}
    (h : stepQ q x = some (q', w_bit, d')) :
    tm1 (evalQ q) (evalBit x) = some (some (evalQ q'), Stmt.write (evalBit w_bit) d') := by
  cases q <;> cases x <;> simp [stepQ] at h <;> rcases h with ⟨rfl, rfl, rfl⟩ <;> rfl

inductive W2 where
  | w01
  | w10
  | w11
  deriving DecidableEq

def w2Eq : W2 → W2 → Bool
  | .w01, .w01 | .w10, .w10 | .w11, .w11 => true
  | _, _ => false

lemma w2Eq_sound {w1 w2 : W2} (h : w2Eq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | nomatch h

def evalW2 : W2 → List (Fin 2)
  | .w01 => [0, 1]
  | .w10 => [1, 0]
  | .w11 => [1, 1]

inductive Var where
  | v0
  | vn
  | va
  | vb
  | vc
  | vd
  | vbc
  deriving DecidableEq

def varEq : Var → Var → Bool
  | .v0, .v0 | .vn, .vn | .va, .va | .vb, .vb | .vc, .vc | .vd, .vd | .vbc, .vbc => true
  | _, _ => false

lemma varEq_sound {v1 v2 : Var} (h : varEq v1 v2 = true) : v1 = v2 := by
  cases v1 <;> cases v2 <;> first | rfl | nomatch h

def evalVar (n a b c d : Nat) : Var → Nat
  | .v0 => 0
  | .vn => n
  | .va => a
  | .vb => b
  | .vc => c
  | .vd => d
  | .vbc => b + c

def canMergeVars : Var → Var → Option Var
  | .v0, v2 => some v2
  | v1, .v0 => some v1
  | .vb, .vc => some .vbc
  | .vc, .vb => some .vbc
  | _, _ => none

lemma canMergeVars_sound (n a b c d : Nat) {v1 v2 vm : Var}
    (h : canMergeVars v1 v2 = some vm) :
    evalVar n a b c d v1 + evalVar n a b c d v2 = evalVar n a b c d vm := by
  cases v1 <;> cases v2 <;> simp [canMergeVars] at h <;> subst h <;> simp [evalVar] <;> omega

inductive SymTok where
  | b0
  | b1
  | pow (w : W2) (k : Nat) (v : Var)
  deriving DecidableEq

def tokEq : SymTok → SymTok → Bool
  | .b0, .b0 => true
  | .b1, .b1 => true
  | .pow w1 k1 v1, .pow w2 k2 v2 => w2Eq w1 w2 && Nat.beq k1 k2 && varEq v1 v2
  | _, _ => false

lemma tokEq_sound {t1 t2 : SymTok} (h : tokEq t1 t2 = true) : t1 = t2 := by
  rcases t1 with _ | _ | ⟨w1, k1, v1⟩ <;> rcases t2 with _ | _ | ⟨w2, k2, v2⟩
  · rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · dsimp [tokEq] at h
    simp only [Bool.and_assoc, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨hw, rfl, hv⟩
    rw [w2Eq_sound hw, varEq_sound hv]

def tokListEq : List SymTok → List SymTok → Bool
  | [], [] => true
  | x :: xs, y :: ys => tokEq x y && tokListEq xs ys
  | _, _ => false

lemma tokListEq_sound {l1 l2 : List SymTok} (h : tokListEq l1 l2 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x xs ih =>
    cases l2 with
    | nil => nomatch h
    | cons y ys =>
      dsimp [tokListEq] at h
      simp only [Bool.and_eq_true] at h
      rw [tokEq_sound h.1, ih h.2]

def bitToTok : Fin 2 → SymTok
  | 0 => .b0
  | 1 => .b1

def evalTok (n a b c d : Nat) : SymTok → List (Fin 2)
  | .b0 => [0]
  | .b1 => [1]
  | .pow w k v => evalW2 w ^ (k + evalVar n a b c d v)

lemma evalTok_bitToTok (n a b c d : Nat) : ∀ (x : Fin 2), evalTok n a b c d (bitToTok x) = [x]
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

def evalHalf (n a b c d : Nat) : List SymTok → ListBlank (Fin 2)
  | [] => default
  | t :: ts => evalTok n a b c d t +> evalHalf n a b c d ts

lemma evalHalf_map_bit (bs : List (Fin 2)) (rest : List SymTok) (n a b c d : Nat) :
    evalHalf n a b c d (bs.map bitToTok ++ rest) = bs +> evalHalf n a b c d rest := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append, evalHalf, evalTok_bitToTok, ih]
    rfl

lemma evalHalf_map_bit_end (bs : List (Fin 2)) (n a b c d : Nat) :
    evalHalf n a b c d (bs.map bitToTok) = bs +> default := by
  simpa only [List.append_nil, evalHalf] using evalHalf_map_bit bs [] n a b c d

def gToks : List SymTok :=
  [SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0]

lemma gToks_eq : gToks = G.map bitToTok := rfl

def l39Toks : List SymTok :=
  [SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1]

lemma l39Toks_eq : l39Toks = l39Bits.map bitToTok := rfl

def l41Toks : List SymTok :=
  [SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1]

lemma l41Toks_eq : l41Toks = l41Bits.map bitToTok := rfl

structure SymState where
  q : Q6
  dir : Dir
  l : List SymTok
  r : List SymTok
  prog : Bool
  deriving DecidableEq

def evalState (n a b c d : Nat) (s : SymState) : Cfg (Fin 2) (Fin 6) :=
  cfg_of (evalQ s.q) s.dir (evalHalf n a b c d s.l) (evalHalf n a b c d s.r)

def pushBit : Bool → List SymTok → List SymTok
  | false, [] => []
  | false, xs => .b0 :: xs
  | true, xs => .b1 :: xs

lemma pushBit_sound (n a b c d : Nat) (x : Bool) (xs : List SymTok) :
    evalHalf n a b c d (pushBit x xs) = ([evalBit x] : List (Fin 2)) +> evalHalf n a b c d xs := by
  cases x <;> cases xs
  · exact zero_cons_default.symm
  · rfl
  · rfl
  · rfl

def pushPowAux (w : W2) (k : Nat) (v : Var) : List SymTok → List SymTok
  | [] => [.pow w k v]
  | .pow w2 k2 v2 :: ys =>
    match w2Eq w w2 with
    | true =>
      match canMergeVars v v2 with
      | some vm => pushPowAux w (k + k2) vm ys
      | none => .pow w k v :: .pow w2 k2 v2 :: ys
    | false =>
      .pow w k v :: .pow w2 k2 v2 :: ys
  | .b0 :: ys =>
    match w with
    | .w01 => .b0 :: pushPowAux .w10 k v ys
    | .w10 => .pow .w10 k v :: .b0 :: ys
    | .w11 => .pow .w11 k v :: .b0 :: ys
  | .b1 :: ys =>
    match w with
    | .w11 => .b1 :: pushPowAux .w11 k v ys
    | .w10 => .b1 :: pushPowAux .w01 k v ys
    | .w01 => .pow .w01 k v :: .b1 :: ys

lemma pushPowAux_sound (n a b c d : Nat) (w : W2) (k : Nat) (v : Var) (xs : List SymTok) :
    evalHalf n a b c d (pushPowAux w k v xs) =
      evalTok n a b c d (.pow w k v) +> evalHalf n a b c d xs := by
  induction xs generalizing w k v with
  | nil => rfl
  | cons y ys ih =>
    rcases y with _ | _ | ⟨w2, k2, v2⟩
    · cases w <;> dsimp [pushPowAux]
      · simp only [evalHalf, evalTok, evalW2, ih .w10 k v]
        exact (rot_w01 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
      · rfl
      · rfl
    · cases w <;> dsimp [pushPowAux]
      · rfl
      · simp only [evalHalf, evalTok, evalW2, ih .w01 k v]
        exact (rot_w10 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
      · simp only [evalHalf, evalTok, evalW2, ih .w11 k v]
        exact (rot_w11 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
    · dsimp [pushPowAux]
      cases hw : w2Eq w w2 with
      | false => rfl
      | true =>
        have hw_eq := w2Eq_sound hw
        subst hw_eq
        cases hm : canMergeVars v v2 with
        | none => rfl
        | some vm =>
          dsimp only
          rw [ih w (k + k2) vm]
          have hvm := canMergeVars_sound n a b c d hm
          have hexp :
              (k + evalVar n a b c d v) + (k2 + evalVar n a b c d v2) =
                (k + k2) + evalVar n a b c d vm := by omega
          simp only [evalHalf, evalTok, ← listblank_append_assoc, ← list_pow_add, hexp]

def pushPow (w : W2) (k : Nat) (v : Var) (xs : List SymTok) : List SymTok :=
  match k, v with
  | 0, .v0 => xs
  | _, _ => pushPowAux w k v xs

lemma pushPow_sound (n a b c d : Nat) (w : W2) (k : Nat) (v : Var) (xs : List SymTok) :
    evalHalf n a b c d (pushPow w k v xs) =
      evalTok n a b c d (.pow w k v) +> evalHalf n a b c d xs := by
  rcases k with _ | k' <;> cases v <;> try exact pushPowAux_sound n a b c d w _ _ xs
  rfl

def unrollPow1 (w : W2) (k : Nat) (v : Var) (tail : List SymTok) : Option (List SymTok) :=
  match k with
  | 0 => none
  | k' + 1 =>
    match w with
    | .w01 => some (.b0 :: .b1 :: pushPow .w01 k' v tail)
    | .w10 => some (.b1 :: .b0 :: pushPow .w10 k' v tail)
    | .w11 => some (.b1 :: .b1 :: pushPow .w11 k' v tail)

lemma unrollPow1_sound (n a b c d : Nat) {w : W2} {k : Nat} {v : Var}
    {tail ys : List SymTok} (h : unrollPow1 w k v tail = some ys) :
    evalHalf n a b c d (.pow w k v :: tail) = evalHalf n a b c d ys := by
  rcases k with _ | k'
  · nomatch h
  · cases w <;> simp [unrollPow1] at h <;> subst h <;>
      simp only [evalHalf, evalTok, evalW2, pushPow_sound, Nat.succ_add] <;>
      exact right_pow_succ _ (k' + evalVar n a b c d v) (evalHalf n a b c d tail)

def rotateHead : List SymTok → Option (List SymTok)
  | .pow w1 k1 v1 :: .pow w2 k2 v2 :: ys =>
    match w2Eq w1 w2 with
    | true =>
      match canMergeVars v1 v2 with
      | some vm => some (.pow w1 (k1 + k2) vm :: ys)
      | none => unrollPow1 w1 k1 v1 (.pow w2 k2 v2 :: ys)
    | false =>
      unrollPow1 w1 k1 v1 (.pow w2 k2 v2 :: ys)
  | .pow w k v :: .b0 :: ys =>
    match w with
    | .w01 => some (.b0 :: pushPow .w10 k v ys)
    | .w10 => unrollPow1 .w10 k v (.b0 :: ys)
    | .w11 => unrollPow1 .w11 k v (.b0 :: ys)
  | .pow w k v :: .b1 :: ys =>
    match w with
    | .w11 => some (.b1 :: pushPow .w11 k v ys)
    | .w10 => some (.b1 :: pushPow .w01 k v ys)
    | .w01 => unrollPow1 .w01 k v (.b1 :: ys)
  | .pow w k v :: [] => unrollPow1 w k v []
  | _ => none

lemma rotateHead_sound (n a b c d : Nat) {xs ys : List SymTok}
    (h : rotateHead xs = some ys) :
    evalHalf n a b c d xs = evalHalf n a b c d ys := by
  rcases xs with _ | ⟨_ | _ | ⟨w1, k1, v1⟩, tail⟩
  · nomatch h
  · nomatch h
  · nomatch h
  · rcases tail with _ | ⟨_ | _ | ⟨w2, k2, v2⟩, rest⟩
    · exact unrollPow1_sound n a b c d h
    · cases w1
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w01 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
      · exact unrollPow1_sound n a b c d h
      · exact unrollPow1_sound n a b c d h
    · cases w1
      · exact unrollPow1_sound n a b c d h
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w10 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w11 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
    · dsimp [rotateHead] at h
      cases hw : w2Eq w1 w2 with
      | false =>
        rw [hw] at h
        exact unrollPow1_sound n a b c d h
      | true =>
        rw [hw] at h
        have hw_eq := w2Eq_sound hw
        subst hw_eq
        cases hm : canMergeVars v1 v2 with
        | none =>
          rw [hm] at h
          exact unrollPow1_sound n a b c d h
        | some vm =>
          rw [hm] at h
          injection h with h'; subst h'
          have hvm := canMergeVars_sound n a b c d hm
          have hexp :
              (k1 + evalVar n a b c d v1) + (k2 + evalVar n a b c d v2) =
                (k1 + k2) + evalVar n a b c d vm := by omega
          simp only [evalHalf, evalTok, ← listblank_append_assoc, ← list_pow_add, hexp]

def popBitOpt : List SymTok → Option (Bool × List SymTok)
  | [] => some (false, [])
  | .b0 :: xs => some (false, xs)
  | .b1 :: xs => some (true, xs)
  | .pow w (k' + 1) .v0 :: xs =>
    match w with
    | .w01 => some (false, pushBit true (pushPow .w01 k' .v0 xs))
    | .w10 => some (true, pushBit false (pushPow .w10 k' .v0 xs))
    | .w11 => some (true, pushBit true (pushPow .w11 k' .v0 xs))
  | .pow _ _ _ :: _ => none

lemma popBitOpt_sound (n a b c d : Nat) {xs : List SymTok} {cur : Bool} {rest : List SymTok}
    (h : popBitOpt xs = some (cur, rest)) :
    evalHalf n a b c d xs = ([evalBit cur] : List (Fin 2)) +> evalHalf n a b c d rest := by
  rcases xs with _ | ⟨_ | _ | ⟨w, _ | k', v⟩, tail⟩
  · simp [popBitOpt] at h
    rcases h with ⟨rfl, rfl⟩
    exact zero_cons_default.symm
  · simp [popBitOpt] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · simp [popBitOpt] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · nomatch h
  · cases v <;> try (simp [popBitOpt] at h)
    cases w <;> simp [popBitOpt] at h <;> rcases h with ⟨rfl, rfl⟩ <;>
      simp only [evalHalf, evalTok, evalVar, evalW2, evalBit, pushBit_sound, pushPow_sound, Nat.add_zero] <;>
      exact right_pow_succ _ k' (evalHalf n a b c d tail)

def popOne1 : List SymTok → Option (List SymTok)
  | .b1 :: rest => some rest
  | .pow .w11 (k' + 1) v :: rest => some (.b1 :: pushPow .w11 k' v rest)
  | _ => none

lemma popOne1_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : popOne1 xs = some rem) :
    evalHalf n a b c d xs = [1] +> evalHalf n a b c d rem := by
  rcases xs with _ | ⟨_ | _ | ⟨w, _ | k', v⟩, rest⟩
  · nomatch h
  · nomatch h
  · injection h with h'; subst h'; rfl
  · cases w <;> simp [popOne1] at h
  · cases w <;> simp [popOne1] at h
    subst h
    simp only [evalHalf, evalTok, evalW2, pushPow_sound, Nat.succ_add]
    exact right_pow_succ [1, 1] (k' + evalVar n a b c d v) (evalHalf n a b c d rest)

def stripPrefix : List SymTok → List SymTok → Option (List SymTok)
  | [], xs => some xs
  | p :: ps, x :: xs =>
    match tokEq p x with
    | true => stripPrefix ps xs
    | false => none
  | _ :: _, [] => none

lemma stripPrefix_eq {pre xs rem : List SymTok}
    (h : stripPrefix pre xs = some rem) : xs = pre ++ rem := by
  induction pre generalizing xs with
  | nil => simpa [stripPrefix] using h
  | cons p ps ih =>
    rcases xs with _ | ⟨x, rest⟩
    · nomatch h
    · dsimp [stripPrefix] at h
      cases heq : tokEq p x with
      | false => rw [heq] at h; nomatch h
      | true =>
        rw [heq] at h
        rw [tokEq_sound heq, ih h]
        rfl

def matchZero1 : List SymTok → Option (List SymTok)
  | [] => some []
  | .b0 :: xs => some xs
  | _ => none

lemma matchZero1_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZero1 xs = some rem) :
    evalHalf n a b c d xs = [0] +> evalHalf n a b c d rem := by
  rcases xs with _ | ⟨_ | _ | ⟨w, k, v⟩, rest⟩
  · injection h with h'; subst h'
    exact zero_list_default.symm
  · injection h with h'; subst h'
    rfl
  · nomatch h
  · nomatch h

def matchZeros2 (xs : List SymTok) : Option (List SymTok) :=
  (matchZero1 xs).bind matchZero1

lemma matchZeros2_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZeros2 xs = some rem) :
    evalHalf n a b c d xs = [0, 0] +> evalHalf n a b c d rem := by
  unfold matchZeros2 at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨m1, h1, h2⟩
  rw [matchZero1_sound n a b c d h1, matchZero1_sound n a b c d h2]
  rfl

def matchZeros3 (xs : List SymTok) : Option (List SymTok) :=
  (matchZeros2 xs).bind matchZero1

lemma matchZeros3_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZeros3 xs = some rem) :
    evalHalf n a b c d xs = [0, 0, 0] +> evalHalf n a b c d rem := by
  unfold matchZeros3 at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨m2, h1, h2⟩
  rw [matchZeros2_sound n a b c d h1, matchZero1_sound n a b c d h2]
  rfl

def ReachRel (prog : Bool) (c1 c2 : Cfg (Fin 2) (Fin 6)) : Prop :=
  if prog then c1 [tm1]⊢⁺ c2 else c1 [tm1]⊢* c2

lemma ReachRel_eq {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 = c3) : ReachRel prog c1 c3 :=
  h2 ▸ h1

lemma ReachRel_star {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢* c3) : ReachRel prog c1 c3 := by
  cases prog
  · exact stepStar_trans h1 h2
  · exact stepPlus_stepStar_trans h1 h2

lemma ReachRel_plus {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢⁺ c3) : ReachRel true c1 c3 := by
  cases prog
  · exact stepStar_stepPlus_trans h1 h2
  · exact stepPlus_trans h1 h2

lemma ReachRel_step {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢ c3) : ReachRel true c1 c3 :=
  ReachRel_plus h1 (step_stepPlus tm1 c2 c3 h2)

def fallbackRightRot (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match rotateHead r with
  | some r' => some ⟨q, .right, l, r', prog⟩
  | none => none

lemma fallbackRightRot_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok} {prog : Bool}
    {s' : SymState} (h : fallbackRightRot q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold fallbackRightRot at h
  cases hr : rotateHead r with
  | none => simp [hr] at h
  | some r' =>
    simp [hr] at h; subst h
    refine ReachRel_eq h0 ?_
    simp only [evalState]
    rw [rotateHead_sound n a b c d hr]

def fallbackLeftRot (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match rotateHead l with
  | some l' => some ⟨q, .left, l', r, prog⟩
  | none => none

lemma fallbackLeftRot_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok} {prog : Bool}
    {s' : SymState} (h : fallbackLeftRot q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold fallbackLeftRot at h
  cases hl : rotateHead l with
  | none => simp [hl] at h
  | some l' =>
    simp [hl] at h; subst h
    refine ReachRel_eq h0 ?_
    simp only [evalState]
    rw [rotateHead_sound n a b c d hl]

def tryRightShift (q : Q6) (w : W2) (k : Nat) (v : Var) (l r_rest : List SymTok) (prog : Bool) :
    Option SymState :=
  match q, w with
  | .q2, .w11 => some ⟨.q2, .right, pushPow .w01 k v l, r_rest, prog⟩
  | .q4, .w11 => some ⟨.q4, .right, pushPow .w10 k v l, r_rest, prog⟩
  | _, _ => fallbackRightRot q l (.pow w k v :: r_rest) prog

lemma tryRightShift_sound (n a b c d : Nat) {q : Q6} {w : W2} {k : Nat} {v : Var}
    {l r_rest : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryRightShift q w k v l r_rest prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, .pow w k v :: r_rest, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases w <;> try exact fallbackRightRot_sound n a b c d h h0
  · injection h with h'; subst h'
    refine ReachRel_star h0 ?_
    simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, pushPow_sound]
    exact shiftR_2_11 (k + evalVar n a b c d v) (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
  · injection h with h'; subst h'
    refine ReachRel_star h0 ?_
    simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, pushPow_sound]
    exact shiftR_4_11 (k + evalVar n a b c d v) (evalHalf n a b c d l) (evalHalf n a b c d r_rest)

def tryLeftShift01 (k : Nat) (v : Var) (l_rest r : List SymTok) (prog : Bool) :
    Option SymState :=
  match matchZeros3 r with
  | some rem_r =>
    match tokListEq l_rest l39Toks with
    | true =>
      some ⟨.q5, .left, [], List.append gToks (pushPow .w11 k v rem_r), prog⟩
    | false =>
      some ⟨.q5, .left, l_rest, pushBit false (pushBit false (pushBit false (pushPow .w11 k v rem_r))), prog⟩
  | none => fallbackLeftRot .q5 (.pow .w01 k v :: l_rest) r prog

lemma tryLeftShift01_sound (n a b c d : Nat) {k : Nat} {v : Var}
    {l_rest r : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryLeftShift01 k v l_rest r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨.q5, .left, .pow .w01 k v :: l_rest, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold tryLeftShift01 at h
  cases hm : matchZeros3 r with
  | none =>
    simp only [hm] at h
    exact fallbackLeftRot_sound n a b c d h h0
  | some rem_r =>
    simp only [hm] at h
    have hr := matchZeros3_sound n a b c d hm
    cases hl39 : tokListEq l_rest l39Toks with
    | true =>
      rw [hl39] at h
      have hl_eq := tokListEq_sound hl39
      subst hl_eq
      injection h with h'; subst h'
      have hsh := shiftL_5_01 (k + evalVar n a b c d v)
        (evalHalf n a b c d l39Toks) (evalHalf n a b c d rem_r)
      have hl_eval : evalHalf n a b c d l39Toks = l39Bits +> default := by
        rw [l39Toks_eq]
        exact evalHalf_map_bit_end l39Bits n a b c d
      have hg_eval :
          evalHalf n a b c d (List.append gToks (pushPow .w11 k v rem_r)) =
            G +> (([1, 1] : List (Fin 2)) ^ (k + evalVar n a b c d v) +>
              evalHalf n a b c d rem_r) := by
        change evalHalf n a b c d (gToks ++ pushPow .w11 k v rem_r) = _
        rw [gToks_eq, evalHalf_map_bit, pushPow_sound, evalTok, evalW2]
      have hed := edge_in (([1, 1] : List (Fin 2)) ^ (k + evalVar n a b c d v) +>
        evalHalf n a b c d rem_r)
      rw [hl_eval] at hsh
      refine ReachRel_star h0 ?_
      simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, hr, hl_eval, hg_eval]
      exact stepStar_trans hsh hed
    | false =>
      rw [hl39] at h
      injection h with h'; subst h'
      have hsh := shiftL_5_01 (k + evalVar n a b c d v)
        (evalHalf n a b c d l_rest) (evalHalf n a b c d rem_r)
      refine ReachRel_star h0 ?_
      simpa only [evalState, evalQ, evalBit, cfg_of, evalHalf, evalTok, evalW2, hr,
        pushBit_sound, pushPow_sound, listblank_append_cons, listblank_append_nil] using hsh

def tryLeftShift (q : Q6) (w : W2) (k : Nat) (v : Var) (l_rest r : List SymTok) (prog : Bool) :
    Option SymState :=
  match q, w with
  | .q5, .w10 =>
    match matchZeros2 r with
    | some rem_r =>
      some ⟨.q5, .left, l_rest, pushBit false (pushBit false (pushPow .w11 k v rem_r)), prog⟩
    | none => fallbackLeftRot q (.pow w k v :: l_rest) r prog
  | .q5, .w01 =>
    tryLeftShift01 k v l_rest r prog
  | _, _ =>
    fallbackLeftRot q (.pow w k v :: l_rest) r prog

lemma tryLeftShift_sound (n a b c d : Nat) {q : Q6} {w : W2} {k : Nat} {v : Var}
    {l_rest r : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryLeftShift q w k v l_rest r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, .pow w k v :: l_rest, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases w <;> try exact fallbackLeftRot_sound n a b c d h h0
  · exact tryLeftShift01_sound n a b c d h h0
  · dsimp [tryLeftShift] at h
    cases hm : matchZeros2 r with
    | none =>
      simp only [hm] at h
      exact fallbackLeftRot_sound n a b c d h h0
    | some rem_r =>
      simp only [hm] at h
      injection h with h'; subst h'
      have hr := matchZeros2_sound n a b c d hm
      have hsh := shiftL_5_10 (k + evalVar n a b c d v)
        (evalHalf n a b c d l_rest) (evalHalf n a b c d rem_r)
      refine ReachRel_star h0 ?_
      simpa only [evalState, evalQ, evalBit, cfg_of, evalHalf, evalTok, evalW2, hr,
        pushBit_sound, pushPow_sound, listblank_append_cons, listblank_append_nil] using hsh

def canCreatePow (usePow : Bool) (l : List SymTok) : Bool :=
  match usePow, l with
  | true, .b0 :: .pow _ _ _ :: _ => false
  | true, _ => true
  | false, _ => false

def matchTwoOnes : List SymTok → Option (List SymTok)
  | .b1 :: .b1 :: rest => some rest
  | _ => none

lemma matchTwoOnes_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchTwoOnes xs = some rem) :
    evalHalf n a b c d xs = [1] +> ([1] +> evalHalf n a b c d rem) := by
  rcases xs with _ | ⟨t1, rest1⟩
  · nomatch h
  · rcases t1 with _ | _ | _
    · nomatch h
    · rcases rest1 with _ | ⟨t2, rest⟩
      · nomatch h
      · rcases t2 with _ | _ | _
        · nomatch h
        · injection h with h'; subst h'; rfl
        · nomatch h
    · nomatch h

def stepConcreteRightPop (q : Q6) (l r : List SymTok) : Option SymState :=
  match popBitOpt r with
  | none => none
  | some (cur, r_rest) =>
    match stepQ q cur with
    | some (q', w_bit, .right) =>
      some ⟨q', .right, pushBit w_bit l, r_rest, true⟩
    | some (q', w_bit, .left) =>
      some ⟨q', .left, l, pushBit w_bit r_rest, true⟩
    | none => none

lemma stepConcreteRightPop_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteRightPop q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteRightPop at h
  cases hp : popBitOpt r with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨cur, r_rest⟩
    simp only [hp] at h
    have hr := popBitOpt_sound n a b c d hp
    cases hsq : stepQ q cur with
    | none => simp [hsq] at h
    | some val =>
      rcases val with ⟨q', w_bit, d'⟩
      have htm := stepQ_sound hsq
      cases d' with
      | left =>
        simp [hsq] at h; subst h
        have hsl : step_local tm1 ⟨[], [evalBit cur], evalQ q, .right⟩ =
            some ⟨[], [evalBit w_bit], evalQ q', .left⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hr, ← pushBit_sound n a b c d w_bit r_rest] at hst
        exact ReachRel_step h0 hst
      | right =>
        simp [hsq] at h; subst h
        have hsl : step_local tm1 ⟨[], [evalBit cur], evalQ q, .right⟩ =
            some ⟨[evalBit w_bit], [], evalQ q', .right⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hr, ← pushBit_sound n a b c d w_bit l] at hst
        exact ReachRel_step h0 hst

def stepConcreteRight (usePow : Bool) (q : Q6) (l r : List SymTok) : Option SymState :=
  match matchTwoOnes r with
  | some r_rest =>
    match canCreatePow usePow l, q with
    | true, .q2 => some ⟨.q2, .right, pushPow .w01 1 .v0 l, r_rest, true⟩
    | true, .q4 => some ⟨.q4, .right, pushPow .w10 1 .v0 l, r_rest, true⟩
    | _, _ => stepConcreteRightPop q l r
  | none => stepConcreteRightPop q l r

lemma stepConcreteRight_sound (n a b c d : Nat) {usePow : Bool} {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteRight usePow q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteRight at h
  cases hm : matchTwoOnes r with
  | none =>
    simp only [hm] at h
    exact stepConcreteRightPop_sound n a b c d h h0
  | some r_rest =>
    simp only [hm] at h
    have hr := matchTwoOnes_sound n a b c d hm
    cases hcan : canCreatePow usePow l with
    | false =>
      rw [hcan] at h
      exact stepConcreteRightPop_sound n a b c d h h0
    | true =>
      rw [hcan] at h
      cases q <;> try exact stepConcreteRightPop_sound n a b c d h h0
      · injection h with h'; subst h'
        refine ReachRel_plus h0 ?_
        simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalVar, evalW2, hr, pushPow_sound]
        exact shiftR_2_11_plus (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
      · injection h with h'; subst h'
        refine ReachRel_plus h0 ?_
        simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalVar, evalW2, hr, pushPow_sound]
        exact shiftR_4_11_plus (evalHalf n a b c d l) (evalHalf n a b c d r_rest)

def stepConcreteLeftPop (q : Q6) (l r : List SymTok) : Option SymState :=
  match popBitOpt l with
  | none => none
  | some (cur, l_rest) =>
    match stepQ q cur with
    | some (q', w_bit, .right) =>
      some ⟨q', .right, pushBit w_bit l_rest, r, true⟩
    | some (q', w_bit, .left) =>
      some ⟨q', .left, l_rest, pushBit w_bit r, true⟩
    | none => none

lemma stepConcreteLeftPop_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteLeftPop q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteLeftPop at h
  cases hp : popBitOpt l with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨cur, l_rest⟩
    simp only [hp] at h
    have hl := popBitOpt_sound n a b c d hp
    cases hsq : stepQ q cur with
    | none => simp [hsq] at h
    | some val =>
      rcases val with ⟨q', w_bit, d'⟩
      have htm := stepQ_sound hsq
      cases d' with
      | left =>
        simp [hsq] at h; subst h
        have hsl : step_local tm1 ⟨[evalBit cur], [], evalQ q, .left⟩ =
            some ⟨[], [evalBit w_bit], evalQ q', .left⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l_rest) (evalHalf n a b c d r)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hl, ← pushBit_sound n a b c d w_bit r] at hst
        exact ReachRel_step h0 hst
      | right =>
        simp [hsq] at h; subst h
        have hsl : step_local tm1 ⟨[evalBit cur], [], evalQ q, .left⟩ =
            some ⟨[evalBit w_bit], [], evalQ q', .right⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l_rest) (evalHalf n a b c d r)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hl, ← pushBit_sound n a b c d w_bit l_rest] at hst
        exact ReachRel_step h0 hst

def stepConcreteLeft (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match q, l with
  | .q5, [] =>
    match stripPrefix gToks r with
    | some r_after_g =>
      match popOne1 r_after_g with
      | some rem_r => some ⟨.q2, .right, l41Toks, pushPow .w11 2 .v0 rem_r, prog⟩
      | none => stepConcreteLeftPop .q5 [] r
    | none => stepConcreteLeftPop .q5 [] r
  | q, l => stepConcreteLeftPop q l r

lemma stepConcreteLeft_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteLeft q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases l <;> dsimp [stepConcreteLeft] at h <;>
    try exact stepConcreteLeftPop_sound n a b c d h h0
  cases hs : stripPrefix gToks r with
  | none =>
    simp only [hs] at h
    exact stepConcreteLeftPop_sound n a b c d h h0
  | some r_after_g =>
    simp only [hs] at h
    cases hp1 : popOne1 r_after_g with
    | none =>
      simp only [hp1] at h
      exact stepConcreteLeftPop_sound n a b c d h h0
    | some rem_r =>
      simp only [hp1] at h
      injection h with h'; subst h'
      have hr_eq := stripPrefix_eq hs
      have hp1_eq := popOne1_sound n a b c d hp1
      have hr_eval : evalHalf n a b c d r = G +> ([1] +> evalHalf n a b c d rem_r) := by
        rw [hr_eq, gToks_eq, evalHalf_map_bit, hp1_eq]
      have hl41_eval : evalHalf n a b c d l41Toks = l41Bits +> default := by
        rw [l41Toks_eq]
        exact evalHalf_map_bit_end l41Bits n a b c d
      have hr_out :
          evalHalf n a b c d (pushPow .w11 2 .v0 rem_r) =
            [1, 1, 1, 1] +> evalHalf n a b c d rem_r := by
        rw [pushPow_sound]
        rfl
      refine ReachRel_star h0 ?_
      simp only [evalState, evalQ, cfg_of, evalHalf, hr_eval, hl41_eval, hr_out]
      exact edge_out (evalHalf n a b c d rem_r)

def symStep (usePow : Bool) (s : SymState) : Option SymState :=
  match s.dir with
  | .right =>
    match s.r with
    | .pow w k v :: r_rest => tryRightShift s.q w k v s.l r_rest s.prog
    | _ => stepConcreteRight usePow s.q s.l s.r
  | .left =>
    match s.l with
    | .pow w k v :: l_rest => tryLeftShift s.q w k v l_rest s.r s.prog
    | _ => stepConcreteLeft s.q s.l s.r s.prog

lemma symStep_sound (n a b c d : Nat) {usePow : Bool} {s s' : SymState}
    (h : symStep usePow s = some s')
    {c0 : Cfg (Fin 2) (Fin 6)} (h0 : ReachRel s.prog c0 (evalState n a b c d s)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  rcases s with ⟨q, dir, l, r, prog⟩
  cases dir with
  | left =>
    rcases l with _ | ⟨_ | _ | ⟨w, k, v⟩, l_rest⟩ <;> dsimp [symStep] at h
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact tryLeftShift_sound n a b c d h h0
  | right =>
    rcases r with _ | ⟨_ | _ | ⟨w, k, v⟩, r_rest⟩ <;> dsimp [symStep] at h
    · exact stepConcreteRight_sound n a b c d h h0
    · exact stepConcreteRight_sound n a b c d h h0
    · exact stepConcreteRight_sound n a b c d h h0
    · exact tryRightShift_sound n a b c d h h0

def runSym (usePow : Bool) : Nat → SymState → Option SymState
  | 0, s => some s
  | k + 1, s =>
    match symStep usePow s with
    | some s' => runSym usePow k s'
    | none => none

lemma runSym_sound (n a b c d : Nat) {usePow : Bool} :
    ∀ (k : Nat) {s s' : SymState},
      runSym usePow k s = some s' →
      ∀ {c0 : Cfg (Fin 2) (Fin 6)},
        ReachRel s.prog c0 (evalState n a b c d s) →
        ReachRel s'.prog c0 (evalState n a b c d s')
  | 0, s, s', h, _, h0 => by
    injection h with h'; subst h'; exact h0
  | k + 1, s, s', h, _, h0 => by
    unfold runSym at h
    cases hs : symStep usePow s with
    | none => simp [hs] at h
    | some sm =>
      simp only [hs] at h
      exact runSym_sound n a b c d k h (symStep_sound n a b c d hs h0)

def insertCanon (t : SymTok) (xs : List SymTok) : List SymTok :=
  match t with
  | .b0 => pushBit false xs
  | .b1 =>
    match xs with
    | .b1 :: rest => pushPow .w11 1 .v0 rest
    | _ => pushBit true xs
  | .pow w k v => pushPow w k v xs

lemma evalHalf_insertCanon (n a b c d : Nat) (t : SymTok) (xs : List SymTok) :
    evalHalf n a b c d (insertCanon t xs) =
      evalTok n a b c d t +> evalHalf n a b c d xs := by
  rcases t with _ | _ | ⟨w, k, v⟩
  · exact pushBit_sound n a b c d false xs
  · rcases xs with _ | ⟨_ | _ | ⟨w2, k2, v2⟩, rest⟩
    · exact pushBit_sound n a b c d true []
    · exact pushBit_sound n a b c d true (.b0 :: rest)
    · dsimp [insertCanon]
      rw [pushPow_sound]
      rfl
    · exact pushBit_sound n a b c d true (.pow w2 k2 v2 :: rest)
  · exact pushPow_sound n a b c d w k v xs

def canonHalf : List SymTok → List SymTok
  | [] => []
  | x :: xs => insertCanon x (canonHalf xs)

lemma evalHalf_canonHalf (n a b c d : Nat) (xs : List SymTok) :
    evalHalf n a b c d (canonHalf xs) = evalHalf n a b c d xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [canonHalf, evalHalf_insertCanon, ih, evalHalf]

def checkMid (usePow : Bool) (fuel : Nat) (s1 s2 : SymState) : Bool :=
  match runSym usePow fuel { s1 with prog := false } with
  | some s' =>
    s'.prog &&
    q6Eq s'.q s2.q &&
    dirEq s'.dir s2.dir &&
    tokListEq s'.l s2.l &&
    tokListEq s'.r s2.r
  | none => false

lemma checkMid_sound (n a b c d : Nat) {usePow : Bool} {fuel : Nat} {s1 s2 : SymState}
    (h : checkMid usePow fuel s1 s2 = true) :
    (evalState n a b c d s1) [tm1]⊢* (evalState n a b c d s2) := by
  unfold checkMid at h
  cases hr : runSym usePow fuel { s1 with prog := false } with
  | none => simp [hr] at h
  | some s' =>
    simp only [hr, Bool.and_assoc, Bool.and_eq_true] at h
    rcases h with ⟨hp, hq, hdir, hl, hr_eq⟩
    have h0 : ReachRel false (evalState n a b c d s1)
        (evalState n a b c d { s1 with prog := false }) :=
      stepStar_refl tm1 _
    have hreach := runSym_sound n a b c d fuel hr h0
    rw [hp] at hreach
    have heq : evalState n a b c d s' = evalState n a b c d s2 := by
      simp only [evalState, q6Eq_sound hq, dirEq_sound hdir, tokListEq_sound hl, tokListEq_sound hr_eq]
    rw [heq] at hreach
    exact stepPlus_stepStar hreach

def checkSym (usePow : Bool) (fuel : Nat) (s1 s2 : SymState) : Bool :=
  match runSym usePow fuel { s1 with prog := false } with
  | some s' =>
    s'.prog &&
    q6Eq s'.q s2.q &&
    dirEq s'.dir s2.dir &&
    tokListEq (canonHalf s'.l) (canonHalf s2.l) &&
    tokListEq (canonHalf s'.r) (canonHalf s2.r)
  | none => false

lemma checkSym_sound (n a b c d : Nat) {usePow : Bool} {fuel : Nat} {s1 s2 : SymState}
    (h : checkSym usePow fuel s1 s2 = true) :
    (evalState n a b c d s1) [tm1]⊢⁺ (evalState n a b c d s2) := by
  unfold checkSym at h
  cases hr : runSym usePow fuel { s1 with prog := false } with
  | none => simp [hr] at h
  | some s' =>
    simp only [hr, Bool.and_assoc, Bool.and_eq_true] at h
    rcases h with ⟨hp, hq, hdir, hl_c, hr_c⟩
    have h0 : ReachRel false (evalState n a b c d s1)
        (evalState n a b c d { s1 with prog := false }) :=
      stepStar_refl tm1 _
    have hreach := runSym_sound n a b c d fuel hr h0
    rw [hp] at hreach
    have heq : evalState n a b c d s' = evalState n a b c d s2 := by
      have hl_eq : evalHalf n a b c d s'.l = evalHalf n a b c d s2.l := by
        rw [← evalHalf_canonHalf n a b c d s'.l, tokListEq_sound hl_c, evalHalf_canonHalf]
      have hr_eq : evalHalf n a b c d s'.r = evalHalf n a b c d s2.r := by
        rw [← evalHalf_canonHalf n a b c d s'.r, tokListEq_sound hr_c, evalHalf_canonHalf]
      simp only [evalState, q6Eq_sound hq, dirEq_sound hdir, hl_eq, hr_eq]
    rwa [heq] at hreach

-- ============================================================================
-- 4. Symbolic `Kr` Builders & The Five Macro Transitions (`S_step`, `TE`, `TO`, `T6`, `T8`)
-- ============================================================================

def segVar (pre : List (Fin 2)) (k0 : Nat) (v : Var) : List SymTok :=
  pre.map bitToTok ++ [.pow .w11 k0 v]

def segConst (pre : List (Fin 2)) (k0 : Nat) : List SymTok :=
  segVar pre k0 .v0

lemma evalHalf_segVar (pre : List (Fin 2)) (k0 : Nat) (v : Var) (rest : List SymTok)
    (n a b c d : Nat) :
    evalHalf n a b c d (segVar pre k0 v ++ rest) =
      pre +> (([1, 1] : List (Fin 2)) ^ (k0 + evalVar n a b c d v) +> evalHalf n a b c d rest) := by
  rw [segVar, List.append_assoc, evalHalf_map_bit]
  rfl

lemma evalHalf_segConst (pre : List (Fin 2)) (k0 : Nat) (rest : List SymTok) (n a b c d : Nat) :
    evalHalf n a b c d (segConst pre k0 ++ rest) =
      pre +> (([1, 1] : List (Fin 2)) ^ k0 +> evalHalf n a b c d rest) := by
  rw [segConst, evalHalf_segVar]
  rfl

def krTailToks : List SymTok :=
  [SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1]

lemma krTailToks_eq : krTailToks = ([0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1] : List (Fin 2)).map bitToTok := rfl

def mkSymKr (r : List SymTok) : SymState :=
  ⟨.q5, .left, [], r, false⟩

def symS_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segVar [0] 5 .va ++
    segVar [0, 1, 1, 0] 3 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 3 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 1 .vd ++
    krTailToks)

def symS_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 24 .vn ++
    segVar [0] 1 .va ++
    segVar [0, 1, 1, 0] 5 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 3 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 3 .vd ++
    krTailToks)

lemma S_step_cert : checkSym true 2192 symS_lhs symS_rhs = true := by
  decide

lemma S_step (n a b c d : Nat) :
    (Kr n (5 + a) (3 + b) (3 + c) (1 + d)) [tm1]⊢⁺
      (Kr (24 + n) (1 + a) (5 + b) (3 + c) (3 + d)) := by
  have h := checkSym_sound n a b c d S_step_cert
  have h1 : evalState n a b c d symS_lhs = Kr n (5 + a) (3 + b) (3 + c) (1 + d) := by
    simp only [symS_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar, Nat.zero_add,
      listblank_append_assoc, listblank_append_nil]
  have h2 : evalState n a b c d symS_rhs = Kr (24 + n) (1 + a) (5 + b) (3 + c) (3 + d) := by
    simp only [symS_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

lemma S_iter (k n a b c d : Nat) :
    (Kr n (4 * k + 1 + a) (3 + b) (3 + c) (1 + d)) [tm1]⊢*
      (Kr (24 * k + n) (1 + a) (2 * k + 3 + b) (3 + c) (2 * k + 1 + d)) := by
  induction k generalizing n b d with
  | zero =>
    have h0 : Kr n (4 * 0 + 1 + a) (3 + b) (3 + c) (1 + d) =
        Kr (24 * 0 + n) (1 + a) (2 * 0 + 3 + b) (3 + c) (2 * 0 + 1 + d) :=
      Kr_congr (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    exact stepStar_refl tm1 _
  | succ k ih =>
    have h_lhs : Kr n (4 * (k + 1) + 1 + a) (3 + b) (3 + c) (1 + d) =
        Kr n (5 + (4 * k + a)) (3 + b) (3 + c) (1 + d) :=
      Kr_congr rfl (by omega) rfl rfl rfl
    have h1 : (Kr n (5 + (4 * k + a)) (3 + b) (3 + c) (1 + d)) [tm1]⊢*
        (Kr (24 + n) (4 * k + 1 + a) (3 + (2 + b)) (3 + c) (1 + (2 + d))) := by
      have hs := stepPlus_stepStar (S_step n (4 * k + a) b c d)
      have h_mid : Kr (24 + n) (1 + (4 * k + a)) (5 + b) (3 + c) (3 + d) =
          Kr (24 + n) (4 * k + 1 + a) (3 + (2 + b)) (3 + c) (1 + (2 + d)) :=
        Kr_congr rfl (by omega) (by omega) rfl (by omega)
      rwa [h_mid] at hs
    have h2 := ih (24 + n) (2 + b) (2 + d)
    have h_rhs :
        Kr (24 * k + (24 + n)) (1 + a) (2 * k + 3 + (2 + b)) (3 + c) (2 * k + 1 + (2 + d)) =
          Kr (24 * (k + 1) + n) (1 + a) (2 * (k + 1) + 3 + b) (3 + c) (2 * (k + 1) + 1 + d) :=
      Kr_congr (by omega) rfl (by omega) rfl (by omega)
    rw [h_lhs]
    rw [h_rhs] at h2
    exact stepStar_trans h1 h2

def symTE_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 2 ++
    segVar [0, 1, 1, 0] 44 .vb ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 10 .vd ++
    krTailToks)

def symTE_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 278 .vn ++
    segVar [0] 1 .vb ++
    segConst [0, 1, 1, 0] 41 ++
    segVar [0, 0, 0, 0, 0, 0, 1] 35 .vd ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def TE_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 91 .vn, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 30 .vb, SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 24 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 29 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def TE_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 184 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 16 .vb, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 31 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 37 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def TE_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 269 .vn, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 0 .vb, SymTok.b0, SymTok.b0, SymTok.pow .w11 43 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 34 .vd, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.pow .w11 1 .v0])

lemma TE_cert1 : checkMid true 8440 symTE_lhs TE_mid1 = true := by
  decide

lemma TE_cert2 : checkMid true 8286 TE_mid1 TE_mid2 = true := by
  decide

lemma TE_cert3 : checkMid true 8494 TE_mid2 TE_mid3 = true := by
  decide

lemma TE_cert_end : checkSym true 226 TE_mid3 symTE_rhs = true := by
  decide

lemma TE (n b d : Nat) :
    (Kr n 2 (44 + b) 17 (10 + d)) [tm1]⊢⁺
      (Kr (278 + n) (1 + b) 41 (35 + d) 9) := by
  have h := (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d TE_cert1) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d TE_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d TE_cert3) (checkSym_sound n 0 b 0 d TE_cert_end))))
  have h1 : evalState n 0 b 0 d symTE_lhs = Kr n 2 (44 + b) 17 (10 + d) := by
    simp only [symTE_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      Nat.zero_add, listblank_append_assoc, listblank_append_nil]
  have h2 : evalState n 0 b 0 d symTE_rhs = Kr (278 + n) (1 + b) 41 (35 + d) 9 := by
    simp only [symTE_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

def symTO_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 1 ++
    segVar [0, 1, 1, 0] 41 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 18 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 .vd ++
    krTailToks)

def symTO_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 294 .vn ++
    segVar [0] 14 .vbc ++
    segVar [0, 1, 1, 0] 40 .vd ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def TO_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 121 .vn, SymTok.b0, SymTok.b0, SymTok.pow .w11 43 .vbc, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 26 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def TO_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 212 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 27 .vbc, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 31 .vd, SymTok.b0, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 5 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

lemma TO_cert1 : checkMid true 8454 symTO_lhs TO_mid1 = true := by
  decide

lemma TO_cert2 : checkMid true 8069 TO_mid1 TO_mid2 = true := by
  decide

lemma TO_cert_end : checkSym true 7854 TO_mid2 symTO_rhs = true := by
  decide

lemma TO (n b c d : Nat) :
    (Kr n 1 (41 + b) (18 + c) (9 + d)) [tm1]⊢⁺
      (Kr (294 + n) (14 + b + c) (40 + d) 17 9) := by
  have h := (stepStar_stepPlus_trans (checkMid_sound n 0 b c d TO_cert1) (stepStar_stepPlus_trans (checkMid_sound n 0 b c d TO_cert2) (checkSym_sound n 0 b c d TO_cert_end)))
  have h1 : evalState n 0 b c d symTO_lhs = Kr n 1 (41 + b) (18 + c) (9 + d) := by
    simp only [symTO_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      Nat.zero_add, listblank_append_assoc, listblank_append_nil]
  have h2 : evalState n 0 b c d symTO_rhs = Kr (294 + n) (14 + b + c) (40 + d) 17 9 := by
    rw [show 14 + b + c = 14 + (b + c) from Nat.add_assoc 14 b c]
    simp only [symTO_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

def symT6_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 3 ++
    segVar [0, 1, 1, 0] 41 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 17 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 .vd ++
    krTailToks)

def symT6_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 296 .vn ++
    segVar [0] 13 .vbc ++
    segVar [0, 1, 1, 0] 40 .vd ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def T6_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 118 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 42 .vbc, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 23 .vd, SymTok.b0, SymTok.pow .w11 10 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T6_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 202 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 28 .vbc, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 30 .vd, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 19 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T6_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 287 .vn, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 12 .vbc, SymTok.b0, SymTok.b0, SymTok.pow .w11 42 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 16 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.pow .w11 1 .v0])

lemma T6_cert1 : checkMid true 7880 symT6_lhs T6_mid1 = true := by
  decide

lemma T6_cert2 : checkMid true 8036 T6_mid1 T6_mid2 = true := by
  decide

lemma T6_cert3 : checkMid true 8494 T6_mid2 T6_mid3 = true := by
  decide

lemma T6_cert_end : checkSym true 226 T6_mid3 symT6_rhs = true := by
  decide

lemma T6 (n b c d : Nat) :
    (Kr n 3 (41 + b) (17 + c) (9 + d)) [tm1]⊢⁺
      (Kr (296 + n) (13 + b + c) (40 + d) 17 9) := by
  have h := (stepStar_stepPlus_trans (checkMid_sound n 0 b c d T6_cert1) (stepStar_stepPlus_trans (checkMid_sound n 0 b c d T6_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b c d T6_cert3) (checkSym_sound n 0 b c d T6_cert_end))))
  have h1 : evalState n 0 b c d symT6_lhs = Kr n 3 (41 + b) (17 + c) (9 + d) := by
    simp only [symT6_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      Nat.zero_add, listblank_append_assoc, listblank_append_nil]
  have h2 : evalState n 0 b c d symT6_rhs = Kr (296 + n) (13 + b + c) (40 + d) 17 9 := by
    rw [show 13 + b + c = 13 + (b + c) from Nat.add_assoc 13 b c]
    simp only [symT6_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

def symT8_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 4 ++
    segVar [0, 1, 1, 0] 44 .vb ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 10 .vd ++
    krTailToks)

def symT8_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 270 .vn ++
    segVar [0] 7 .vb ++
    segConst [0, 1, 1, 0] 43 ++
    segVar [0, 0, 0, 0, 0, 0, 1] 33 .vd ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def T8_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 92 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 36 .vb, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 26 .v0, SymTok.b0, SymTok.pow .w11 20 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 10 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T8_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 176 .vn, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 22 .vb, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 33 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 35 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T8_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 261 .vn, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .vb, SymTok.b0, SymTok.b0, SymTok.pow .w11 45 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 32 .vd, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.pow .w11 1 .v0])

lemma T8_cert1 : checkMid true 8149 symT8_lhs T8_mid1 = true := by
  decide

lemma T8_cert2 : checkMid true 8036 T8_mid1 T8_mid2 = true := by
  decide

lemma T8_cert3 : checkMid true 8494 T8_mid2 T8_mid3 = true := by
  decide

lemma T8_cert_end : checkSym true 226 T8_mid3 symT8_rhs = true := by
  decide

lemma T8 (n b d : Nat) :
    (Kr n 4 (44 + b) 17 (10 + d)) [tm1]⊢⁺
      (Kr (270 + n) (7 + b) 43 (33 + d) 9) := by
  have h := (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d T8_cert1) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d T8_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d T8_cert3) (checkSym_sound n 0 b 0 d T8_cert_end))))
  have h1 : evalState n 0 b 0 d symT8_lhs = Kr n 4 (44 + b) 17 (10 + d) := by
    simp only [symT8_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      Nat.zero_add, listblank_append_assoc, listblank_append_nil]
  have h2 : evalState n 0 b 0 d symT8_rhs = Kr (270 + n) (7 + b) 43 (33 + d) 9 := by
    simp only [symT8_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf, evalVar,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

lemma DC (N X : Nat) : (Ev N X) [tm1]⊢⁺ Ev (48 * X + 716 + N) (4 + X) := by
  have h1 : (Ev N X) [tm1]⊢*
      Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11)) := by
    have hs := S_iter (X + 6) N 1 (2 * X + 29) 14 8
    have hl : Kr N (4 * (X + 6) + 1 + 1) (3 + (2 * X + 29)) (3 + 14) (1 + 8) = Ev N X :=
      Kr_congr rfl (by omega) (by omega) rfl rfl
    have hr :
        Kr (24 * (X + 6) + N) (1 + 1) (2 * (X + 6) + 3 + (2 * X + 29)) (3 + 14)
            (2 * (X + 6) + 1 + 8) =
          Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11)) :=
      Kr_congr rfl rfl (by omega) rfl (by omega)
    rwa [hl, hr] at hs
  have h2 : (Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11))) [tm1]⊢⁺
      Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8) := by
    have hte := TE (24 * (X + 6) + N) (4 * X) (2 * X + 11)
    have hr :
        Kr (278 + (24 * (X + 6) + N)) (1 + 4 * X) 41 (35 + (2 * X + 11)) 9 =
          Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8) :=
      Kr_congr (by omega) (by omega) rfl (by omega) rfl
    rwa [hr] at hte
  have h3 : (Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8))
      [tm1]⊢*
        Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X) := by
    have hs := S_iter X (422 + 24 * X + N) 0 38 (2 * X + 43) 8
    have hr :
        Kr (24 * X + (422 + 24 * X + N)) (1 + 0) (2 * X + 3 + 38) (3 + (2 * X + 43))
            (2 * X + 1 + 8) =
          Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X) :=
      Kr_congr (by omega) rfl (by omega) (by omega) (by omega)
    rwa [hr] at hs
  have h4 :
      (Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X)) [tm1]⊢⁺
        Ev (48 * X + 716 + N) (4 + X) := by
    have hto := TO (422 + 48 * X + N) (2 * X) (2 * X + 28) (2 * X)
    have hr :
        Kr (294 + (422 + 48 * X + N)) (14 + 2 * X + (2 * X + 28)) (40 + 2 * X) 17 9 =
          Ev (48 * X + 716 + N) (4 + X) := by
      unfold Ev
      exact Kr_congr (by omega) (by omega) (by omega) rfl rfl
    rwa [hr] at hto
  exact stepPlus_trans (stepStar_stepPlus_trans h1 h2) (stepStar_stepPlus_trans h3 h4)

-- ============================================================================
-- 5. Stem `initC ⊢* Kr 976 17 34 22 9`, Transient to `Ev 6428 20`, and Goal
-- ============================================================================

def symInitC : SymState := ⟨.q2, .right, [], [], false⟩

def stem_mid0 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 11 .v0, SymTok.b0, SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.pow .w11 1 .v0])

lemma stem_cert0 : checkSym false 5986 symInitC stem_mid0 = true := by
  decide

def symKr976 : SymState :=
  mkSymKr (
    segConst (G ++ [1]) 976 ++
    segConst [0] 17 ++
    segConst [0, 1, 1, 0] 34 ++
    segConst [0, 0, 0, 0, 0, 0, 1] 22 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def stem_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 167 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 10 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 1 .v0])

def stem_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 281 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 20 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 14 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 401 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 32 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.pow .w11 7 .v0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid4 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 539 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 20 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 11 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid5 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 653 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 28 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 38 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid6 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 775 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 48 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 20 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 10 .v0])

def stem_mid7 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 870 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 34 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 23 .v0, SymTok.b0, SymTok.pow .w11 22 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 4 .v0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def stem_mid8 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 955 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 18 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 31 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 22 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.pow .w11 9 .v0])

lemma stem_cert1 : checkMid true 8266 stem_mid0 stem_mid1 = true := by
  decide

lemma stem_cert2 : checkMid true 8218 stem_mid1 stem_mid2 = true := by
  decide

lemma stem_cert3 : checkMid true 8330 stem_mid2 stem_mid3 = true := by
  decide

lemma stem_cert4 : checkMid true 8520 stem_mid3 stem_mid4 = true := by
  decide

lemma stem_cert5 : checkMid true 8239 stem_mid4 stem_mid5 = true := by
  decide

lemma stem_cert6 : checkMid true 8570 stem_mid5 stem_mid6 = true := by
  decide

lemma stem_cert7 : checkMid true 8210 stem_mid6 stem_mid7 = true := by
  decide

lemma stem_cert8 : checkMid true 8598 stem_mid7 stem_mid8 = true := by
  decide

lemma stem_cert_end : checkSym true 1347 stem_mid8 symKr976 = true := by
  decide

lemma initC_to_kr976 : initC [tm1]⊢* Kr 976 17 34 22 9 := by
  have h := stepPlus_stepStar (stepStar_stepPlus_trans (stepPlus_stepStar (checkSym_sound 0 0 0 0 0 stem_cert0)) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert1) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert2) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert3) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert4) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert5) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert6) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert7) (stepStar_stepPlus_trans (checkMid_sound 0 0 0 0 0 stem_cert8) (checkSym_sound 0 0 0 0 0 stem_cert_end))))))))))
  have h1 : evalState 0 0 0 0 0 symInitC = initC := rfl
  have h2 : evalState 0 0 0 0 0 symKr976 = Kr 976 17 34 22 9 := by
    simp only [symKr976, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
      List.append_assoc, evalHalf_segConst, evalHalf_map_bit, evalHalf_map_bit_end, evalHalf,
      listblank_append_assoc, listblank_append_nil]
  rwa [h1, h2] at h

lemma kr976_to_ev : (Kr 976 17 34 22 9) [tm1]⊢* Ev 6428 20 :=
  stepStar_trans (S_iter 4 976 0 31 19 8) <|
  stepStar_trans (stepPlus_stepStar (TO 1072 1 4 8)) <|
  stepStar_trans (S_iter 4 1366 2 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T6 1462 15 0 8)) <|
  stepStar_trans (S_iter 6 1758 3 45 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 1902 16 11)) <|
  stepStar_trans (S_iter 5 2172 2 40 41 8) <|
  stepStar_trans (stepPlus_stepStar (T6 2292 12 27 10)) <|
  stepStar_trans (S_iter 12 2588 3 47 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 2876 30 23)) <|
  stepStar_trans (S_iter 9 3146 0 40 53 8) <|
  stepStar_trans (stepPlus_stepStar (TO 3362 20 38 18)) <|
  stepStar_trans (S_iter 17 3656 3 55 14 8) <|
  stepStar_trans (stepPlus_stepStar (T8 4064 48 33)) <|
  stepStar_trans (S_iter 13 4334 2 40 63 8) <|
  stepStar_trans (stepPlus_stepStar (T6 4646 28 49 26)) <|
  stepStar_trans (S_iter 22 4942 1 63 14 8) <|
  stepStar_trans (stepPlus_stepStar (TE 5470 66 43)) <|
  stepStar_trans (S_iter 16 5748 2 38 75 8) <|
  stepPlus_stepStar (T6 6132 32 61 32)

lemma initC_to_ev : initC [tm1]⊢* Ev 6428 20 :=
  stepStar_trans initC_to_kr976 kr976_to_ev

def Inv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ N X : Nat, cfg = Ev N X

lemma neverHalts_ev6428 : NeverHaltsFrom tm1 (Ev 6428 20) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant (P := Inv) ?_ ⟨6428, 20, rfl⟩
  rintro _ ⟨N, X, rfl⟩
  exact ⟨Ev (48 * X + 716 + N) (4 + X), DC N X, 48 * X + 716 + N, 4 + X, rfl⟩

lemma neverHalts_initC : NeverHaltsFrom tm1 initC := by
  obtain ⟨k₀, hk₀⟩ := initC_to_ev
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step tm1 cfg with _ | _
    · have hnone : (step tm1 cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep tm1 initC k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, multiStep_add, hk₀, Option.bind_some] at hk
    exact neverHalts_ev6428 cfg ⟨k - k₀, hk⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg hreach
  apply isSome_step_of_mirrorCfg
  have hmir := reachesStar_mirrorCfg hreach
  rw [mirrorCfg_init] at hmir
  exact neverHalts_initC (mirrorCfg cfg) hmir

end BusyBeaver.M_1RB1LE_1LC1RD_0LA1LA_HHH1RE_1LF0LA_0LC0RF
