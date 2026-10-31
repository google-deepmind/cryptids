module

public import BusyBeaver.WordCalculusF
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordVKQ

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

open Word

lemma zW_nonneg_and_le_two (u : List Word) :
    0 <= zW u ∧ 0 <= zW_V u ∧ zW u <= 2 * zW_V u := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rcases ih with ⟨h1, h2, h3⟩
    cases a <;> (simp only [zW_cons_V, zW_V_cons_V, zW_cons_K, zW_V_cons_K, zW_cons_Q, zW_V_cons_Q]; constructor; linarith; constructor <;> linarith)

lemma zW_nonneg (u : List Word) : 0 <= zW u := (zW_nonneg_and_le_two u).1
lemma zW_V_nonneg (u : List Word) : 0 <= zW_V u := (zW_nonneg_and_le_two u).2.1
lemma zW_le_two_zW_V (u : List Word) : zW u <= 2 * zW_V u := (zW_nonneg_and_le_two u).2.2

lemma z10_z12_le_zW (u : List Word) : 2 * z10 u + z12 u <= 2 * zW u := by
  induction u with
  | nil => simp [z10, z12]
  | cons a u ih =>
    have hle := zW_le_two_zW_V u
    cases a <;> (dsimp only [z10, z12]; simp only [zW_cons_V, zW_cons_K, zW_cons_Q]; linarith)

lemma z10_z12_le_four_zW_V (u : List Word) : 2 * z10 u + z12 u <= 4 * zW_V u := by
  have h1 := z10_z12_le_zW u
  have h2 := zW_le_two_zW_V u
  linarith

lemma z13_pos (u : List Word) : 0 < z13 u := by
  induction u with
  | nil => simp [z13]
  | cons a u ih => cases a <;> (dsimp [z13]; linarith)

lemma z13_append (u v : List Word) : z13 (u ++ v) = z13 u * z13 v := by
  induction u with
  | nil => simp [z13]
  | cons a u ih => cases a <;> (dsimp [z13]; rw [ih]; ring)

lemma zW_append_both (u t : List Word) :
    (zW (u ++ t) <= zW u + 2 * z13 u * zW_V t) ∧
    (zW_V (u ++ t) <= zW_V u + z13 u * zW_V t) := by
  induction u with
  | nil =>
    simp [z13, zW_le_two_zW_V t]
  | cons a u ih =>
    rcases ih with ⟨ihW, ihWV⟩
    cases a <;> (
      dsimp only [z13]
      simp only [List.cons_append, zW_cons_V, zW_V_cons_V, zW_cons_K, zW_V_cons_K, zW_cons_Q, zW_V_cons_Q]
      constructor <;> linarith
    )

lemma zW_V_append (u t : List Word) : zW_V (u ++ t) <= zW_V u + z13 u * zW_V t :=
  (zW_append_both u t).2

def cPar (b : Nat) : Rat :=
  if b % 2 == 1 then 2 / 16 else 3 / 16

lemma cPar_bounds (b : Nat) : 2 / 16 <= cPar b ∧ cPar b <= 3 / 16 := by
  unfold cPar
  split_ifs <;> constructor <;> norm_num

lemma Scan_zW_contract {a b a' b' g : Nat} {u v : List Word}
    (h : Scan a b u a' b' v g) :
    zW_V v <= (15 / 16) * zW u + cPar b := by
  induction h with
  | nil a b _ =>
    have hc := (cPar_bounds b).1
    simp; linarith
  | @T a b a' b' g u v _ _ ih =>
    have hc_in := (cPar_bounds b).1
    have hc_next : cPar ((b - 1) * 2) = 3 / 16 := by
      unfold cPar; have hmod : ((b - 1) * 2) % 2 = 0 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    have hle := zW_le_two_zW_V u
    simp only [zW_V_cons_V, zW_cons_V]
    linarith
  | @VK0 a k a' b' g u v _ _ ih =>
    have hc_in : cPar (k * 2) = 3 / 16 := by
      unfold cPar; have hmod : (k * 2) % 2 = 0 := by omega
      rw [hmod]; rfl
    have hc_next : cPar (1 + (k - 1) * 2) = 2 / 16 := by
      unfold cPar; have hmod : (1 + (k - 1) * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    rw [hc_in]
    simp only [zW_V_cons_K, zW_cons_V, zW_cons_K]
    linarith
  | @VK1 a k a' b' g u v _ _ ih =>
    have hc_in : cPar (1 + k * 2) = 2 / 16 := by
      unfold cPar; have hmod : (1 + k * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    have hc_next : cPar (1 + (k - 1) * 2) = 2 / 16 := by
      unfold cPar; have hmod : (1 + (k - 1) * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    rw [hc_in]
    simp only [zW_V_cons_Q, zW_cons_V, zW_V_cons_K]
    linarith
  | @D a b q1 a' b' g w0 u v hw0 _ _ _ ih =>
    have hc_next := (cPar_bounds (b / 2)).2
    have hle := zW_le_two_zW_V v
    rw [zW_cons_d hw0]
    unfold cPar
    split_ifs <;> (simp only [zW_V_cons_Q, zW_V_cons_K]; linarith)
  | @P0 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    have hc_in := (cPar_bounds b).1
    have hc_next := (cPar_bounds ((b - 1) * 2)).2
    have hzW := zW_nonneg u
    rw [zW_cons_d hw0, zW_cons_d hw1]
    simp only [zW_V_cons_V]
    linarith
  | @P1 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    have hc_in := (cPar_bounds b).1
    have hc_next := (cPar_bounds (1 + (b - 1) * 2)).2
    have hzW := zW_nonneg u
    rw [zW_cons_d hw0, zW_cons_d hw1]
    simp only [zW_V_cons_V]
    linarith

lemma dCount_bound (v : List Word) :
    (zW v <= (3 / 2) * (((2 ^ (dCount v) : Nat) : Rat) - 1)) ∧
    (zW_V v <= ((2 ^ (dCount v) : Nat) : Rat) - 1) := by
  induction v with
  | nil => simp [dCount]
  | cons a v ih =>
    rcases ih with ⟨ihW, ihWV⟩
    have hpow_pos : (1 : Rat) <= ((2 ^ (dCount v) : Nat) : Rat) := by
      exact_mod_cast (zPp (dCount v))
    cases a with
    | V =>
      dsimp only [dCount]; simp only [zW_cons_V, zW_V_cons_V]
      constructor <;> linarith
    | K =>
      dsimp only [dCount]; rw [zPow1 (dCount v), Nat.cast_add]
      simp only [zW_cons_K, zW_V_cons_K]
      constructor <;> linarith
    | Q =>
      dsimp only [dCount]; rw [zPow1 (dCount v), Nat.cast_add]
      simp only [zW_cons_Q, zW_V_cons_Q]
      constructor <;> linarith

lemma zDg_Scan_dCount {a b a' b' g : Nat} {u v : List Word}
    (hS : Scan a b u a' b' v g) :
    ∀ {A m : Nat}, zDg A m u -> dCount v + 2 * g = m := by
  induction hS with
  | nil _ _ _ =>
    intro A m hDg; cases hDg; rfl
  | T _ _ _ =>
    intro A m hDg; cases hDg
  | VK0 _ _ _ =>
    intro A m hDg; cases hDg
  | VK1 _ _ _ =>
    intro A m hDg; cases hDg
  | @D a b q1 a' b' g w0 u v hw0 _ _ _ ih =>
    intro A m hDg
    have hd_out : dCount ((if b % 2 == 1 then Q else K) :: v) = 1 + dCount v := by
      split_ifs <;> rfl
    rw [hd_out]
    cases hDg with
    | zero hD => have hI := ih hD; omega
    | one hD => have hI := ih hD; omega
  | @P0 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    intro A m hDg
    dsimp [dCount]
    cases hDg with
    | zero hD1 =>
      cases hD1 with
      | zero hD2 => have hI := ih hD2; omega
      | one hD2 => have hI := ih hD2; omega
    | one hD1 =>
      cases hD1 with
      | zero hD2 => have hI := ih hD2; omega
      | one hD2 => have hI := ih hD2; omega
  | @P1 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    intro A m hDg
    dsimp [dCount]
    cases hDg with
    | zero hD1 =>
      cases hD1 with
      | zero hD2 => have hI := ih hD2; omega
      | one hD2 => have hI := ih hD2; omega
    | one hD1 =>
      cases hD1 with
      | zero hD2 => have hI := ih hD2; omega
      | one hD2 => have hI := ih hD2; omega

lemma zDg_z13_z10 {A m : Nat} {u : List Word} (h : zDg A m u) :
    z13 u = ((2 ^ m : Nat) : Rat) ∧ z10 u = ((2 ^ m : Nat) : Rat) - 1 := by
  induction h with
  | nil => simp [z13, z10]
  | @zero A m u _ ih =>
    rw [zPow1 m, Nat.cast_add]; dsimp only [z13, z10]; constructor <;> linarith
  | @one A m u _ ih =>
    rw [zPow1 m, Nat.cast_add]; dsimp only [z13, z10]; constructor <;> linarith

lemma z13_Scan {a b a' b' g : Nat} {u v : List Word}
    (h : Scan a b u a' b' v g) :
    z13 v * ((2 ^ (3 * g) : Nat) : Rat) = z13 u := by
  induction h with
  | nil _ _ _ => simp [z13]
  | T _ _ ih => dsimp [z13]; linarith
  | VK0 _ _ ih => dsimp [z13]; linarith
  | VK1 _ _ ih => dsimp [z13]; linarith
  | @D _ b _ _ _ _ w0 u v hw0 _ _ _ ih =>
    have hv : z13 ((if b % 2 == 1 then Q else K) :: v) = 2 * z13 v := by
      split_ifs <;> rfl
    rw [hv, z13_cons_d hw0]; linarith
  | @P0 _ _ _ _ _ _ g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    rw [z13_cons_d hw0, z13_cons_d hw1]
    have hpow : 2 ^ (3 * (1 + g)) = 2 ^ (3 * g) * 8 := by
      have : 3 * (1 + g) = 3 * g + 3 := by omega
      rw [this, Nat.pow_add]
    have h8 : ((8 : Nat) : Rat) = 8 := by norm_num
    rw [hpow, Nat.cast_mul, h8]; dsimp [z13]; linarith
  | @P1 _ _ _ _ _ _ g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    rw [z13_cons_d hw0, z13_cons_d hw1]
    have hpow : 2 ^ (3 * (1 + g)) = 2 ^ (3 * g) * 8 := by
      have : 3 * (1 + g) = 3 * g + 3 := by omega
      rw [this, Nat.pow_add]
    have h8 : ((8 : Nat) : Rat) = 8 := by norm_num
    rw [hpow, Nat.cast_mul, h8]; dsimp [z13]; linarith

lemma Parse_la {a a' g : Nat} {u : List Word} (h : Parse a u a' g) :
    0 <= ((a' : Rat) + 1) * z13 u - ((a : Rat) + 1) ∧
    ((a' : Rat) + 1) * z13 u - ((a : Rat) + 1) <= 2 * z10 u := by
  induction h with
  | nil a => simp [z13, z10]
  | @T a a' g u _ ih =>
    dsimp [z13, z10]; push_cast at ih ⊢; constructor <;> linarith
  | @VK a a' g u _ ih =>
    dsimp [z13, z10]; constructor <;> linarith
  | @D a q1 a' g w0 u hw0 hq1 _ ih =>
    rw [z13_cons_d hw0, z10_cons_d hw0]
    have hd := dVal_le_one w0
    have hq1_r : (a : Rat) + (dVal w0 : Rat) = (q1 : Rat) * 2 := by exact_mod_cast hq1
    have hd_r0 : (0 : Rat) <= (dVal w0 : Rat) := Nat.cast_nonneg _
    have hd_r1 : (dVal w0 : Rat) <= 1 := by exact_mod_cast hd
    constructor <;> linarith
  | @P a q2 a' g w0 w1 u hw0 hw1 hq2 _ ih =>
    rw [z13_cons_d hw0, z13_cons_d hw1, z10_cons_d hw0, z10_cons_d hw1]
    have hd0 := dVal_le_one w0
    have hd1 := dVal_le_one w1
    let q1 := (a + dVal w0) / 2
    let r1 := (a + dVal w0) % 2
    have hr1 : r1 <= 1 := by omega
    have h1 : a + dVal w0 = r1 + q1 * 2 := by omega
    have h2 : q1 + dVal w1 = 1 + q2 * 2 := hq2
    have h_rel : 4 * q2 + 2 + r1 = a + dVal w0 + 2 * dVal w1 := by omega
    have h_rel_r : 4 * (q2 : Rat) + 2 + (r1 : Rat) = (a : Rat) + (dVal w0 : Rat) + 2 * (dVal w1 : Rat) := by
      exact_mod_cast h_rel
    have hr1_0 : (0 : Rat) <= (r1 : Rat) := Nat.cast_nonneg _
    have hr1_1 : (r1 : Rat) <= 1 := by exact_mod_cast hr1
    have hd0_0 : (0 : Rat) <= (dVal w0 : Rat) := Nat.cast_nonneg _
    have hd0_1 : (dVal w0 : Rat) <= 1 := by exact_mod_cast hd0
    have hd1_0 : (0 : Rat) <= (dVal w1 : Rat) := Nat.cast_nonneg _
    have hd1_1 : (dVal w1 : Rat) <= 1 := by exact_mod_cast hd1
    constructor <;> linarith

lemma zDg_cons_inv {A m : Nat} {w0 : Word} {u : List Word}
    (h : zDg A m (w0 :: u)) :
    ∃ A' m', zDg A' m' u ∧ A = dVal w0 + A' * 2 ∧ m = 1 + m' := by
  cases h with
  | zero hD => exact ⟨_, _, hD, by dsimp only [dVal]; omega, rfl⟩
  | one hD => exact ⟨_, _, hD, rfl, rfl⟩

lemma Parse_zDg_a {a a' g : Nat} {u : List Word} (hP : Parse a u a' g) :
    ∀ {A m : Nat}, zDg A m u -> a' * 2 ^ m <= a + A ∧ a + A < (a' + 1) * 2 ^ m := by
  induction hP with
  | nil a =>
    intro A m hDg; cases hDg; simp
  | T _ _ => intro A m hDg; cases hDg
  | VK _ _ => intro A m hDg; cases hDg
  | @D a q1 a' g w0 u _ hq1 _ ih =>
    intro A m hDg
    rcases zDg_cons_inv hDg with ⟨A', m', hD', rfl, rfl⟩
    rcases ih hD' with ⟨hL, hR⟩
    rw [zPow1 m']
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hL hR ⊢
    omega
  | @P a q2 a' g w0 w1 u _ _ hq2 _ ih =>
    intro A m hDg
    rcases zDg_cons_inv hDg with ⟨A1, m1, hD1, rfl, rfl⟩
    rcases zDg_cons_inv hD1 with ⟨A2, m2, hD2, rfl, rfl⟩
    rcases ih hD2 with ⟨hL, hR⟩
    rw [zPow1 (1 + m2), zPow1 m2]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul] at hL hR ⊢
    let q1 := (a + dVal w0) / 2
    let r1 := (a + dVal w0) % 2
    have hr1 : r1 <= 1 := by omega
    have h1 : a + dVal w0 = r1 + q1 * 2 := by omega
    have h2 : q1 + dVal w1 = 1 + q2 * 2 := hq2
    omega

lemma Scan_delta {a b a' b' g : Nat} {u v : List Word}
    (h : Scan a b u a' b' v g) :
    -1 <= ((b : Rat) - 2) - ((b' : Rat) - 2) * z13 v ∧
    ((b : Rat) - 2) - ((b' : Rat) - 2) * z13 v <= 2 * z10 v + z12 v := by
  induction h with
  | nil _ _ _ => simp [z13, z10, z12]
  | @T a b a' b' g u v hb _ ih =>
    dsimp [z13, z10, z12]
    have hcast : (((b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 2 := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
    rw [hcast] at ih
    constructor <;> linarith
  | @VK0 a k a' b' g u v hk _ ih =>
    dsimp [z13, z10, z12]
    have hcast : ((1 + (k - 1) * 2 : Nat) : Rat) = ((k * 2 : Nat) : Rat) - 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk]; push_cast; ring
    rw [hcast] at ih
    constructor <;> linarith
  | @VK1 a k a' b' g u v hk _ ih =>
    dsimp [z13, z10, z12]
    have hcast : ((1 + (k - 1) * 2 : Nat) : Rat) = ((1 + k * 2 : Nat) : Rat) - 2 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hk]; push_cast; ring
    rw [hcast] at ih
    constructor <;> linarith
  | @D a b q1 a' b' g w0 u v _ _ _ _ ih =>
    rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
    · have hb_eq : b = 2 * (b / 2) := by omega
      have hcast : (b : Rat) = 2 * ((b / 2 : Nat) : Rat) := by exact_mod_cast hb_eq
      have h_if : (if b % 2 == 1 then Q else K) = K := by rw [hb0]; rfl
      rw [h_if]
      dsimp [z13, z10, z12]
      constructor <;> linarith
    · have hb_eq : b = 1 + 2 * (b / 2) := by omega
      have hcast : (b : Rat) = 1 + 2 * ((b / 2 : Nat) : Rat) := by exact_mod_cast hb_eq
      have h_if : (if b % 2 == 1 then Q else K) = Q := by rw [hb1]; rfl
      rw [h_if]
      dsimp [z13, z10, z12]
      constructor <;> linarith
  | @P0 a b q1 q2 a' b' g w0 w1 u v _ _ _ _ hb _ ih =>
    dsimp [z13, z10, z12]
    have hcast : (((b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 2 := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
    rw [hcast] at ih
    constructor <;> linarith
  | @P1 a b q1 q2 a' b' g w0 w1 u v _ _ _ _ hb _ ih =>
    dsimp [z13, z10, z12]
    have hcast : ((1 + (b - 1) * 2 : Nat) : Rat) = 2 * (b : Rat) - 1 := by
      rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 1 <= b)]; push_cast; ring
    rw [hcast] at ih
    constructor <;> linarith

-- Pure Nat evaluators for concrete word lists (avoids decide on Rat)
def vCount : List Word -> Nat
  | [] => 0
  | V :: u => 1 + vCount u
  | _ :: u => vCount u

lemma z13_mul_pow_vCount (u : List Word) :
    z13 u * ((2 ^ (vCount u) : Nat) : Rat) = ((2 ^ (dCount u) : Nat) : Rat) := by
  induction u with
  | nil => simp [z13, vCount, dCount]
  | cons w u ih =>
    cases w with
    | V =>
      dsimp only [z13, vCount, dCount]
      rw [zPow1 (vCount u), Nat.cast_add]; linarith
    | K =>
      dsimp only [z13, vCount, dCount]
      rw [zPow1 (dCount u), Nat.cast_add]; linarith
    | Q =>
      dsimp only [z13, vCount, dCount]
      rw [zPow1 (dCount u), Nat.cast_add]; linarith

def checkZ13Pow (u : List Word) (L target : Nat) : Bool :=
  dCount u + L == vCount u + target

lemma checkZ13Pow_sound (u : List Word) (L target : Nat)
    (h : checkZ13Pow u L target = true) :
    z13 u * ((2 ^ L : Nat) : Rat) = ((2 ^ target : Nat) : Rat) := by
  unfold checkZ13Pow at h
  rw [beq_iff_eq] at h
  have h_vc := z13_mul_pow_vCount u
  have h_pow_pos : (0 : Rat) < ((2 ^ (vCount u) : Nat) : Rat) := by exact_mod_cast (zPp (vCount u))
  have h_nat : 2 ^ dCount u * 2 ^ L = 2 ^ vCount u * 2 ^ target := by
    rw [<- Nat.pow_add, <- Nat.pow_add, h]
  have h_rat : ((2 ^ dCount u : Nat) : Rat) * ((2 ^ L : Nat) : Rat) =
      ((2 ^ (vCount u) : Nat) : Rat) * ((2 ^ target : Nat) : Rat) := by exact_mod_cast h_nat
  have h_eq : (z13 u * ((2 ^ L : Nat) : Rat) - ((2 ^ target : Nat) : Rat)) *
      ((2 ^ (vCount u) : Nat) : Rat) = 0 := by
    calc (z13 u * ((2 ^ L : Nat) : Rat) - ((2 ^ target : Nat) : Rat)) * ((2 ^ (vCount u) : Nat) : Rat)
      _ = (z13 u * ((2 ^ (vCount u) : Nat) : Rat)) * ((2 ^ L : Nat) : Rat) -
          ((2 ^ (vCount u) : Nat) : Rat) * ((2 ^ target : Nat) : Rat) := by ring
      _ = ((2 ^ dCount u : Nat) : Rat) * ((2 ^ L : Nat) : Rat) -
          ((2 ^ (vCount u) : Nat) : Rat) * ((2 ^ target : Nat) : Rat) := by rw [h_vc]
      _ = 0 := by linarith
  rcases mul_eq_zero.mp h_eq with h0 | h0
  · linarith
  · linarith

def zWNat : List Word -> Nat × Nat
  | [] => (0, 0)
  | V :: u =>
    let p := zWNat u
    (4 * p.2, 2 * p.2)
  | K :: u =>
    let p := zWNat u
    (6 * 4 ^ u.length + 8 * p.1, 4 * 4 ^ u.length + 4 * p.1)
  | Q :: u =>
    let p := zWNat u
    (6 * 4 ^ u.length + 8 * p.1, 3 * 4 ^ u.length + 4 * p.1)

lemma zWNat_sound (u : List Word) :
    zW u * ((4 ^ u.length : Nat) : Rat) = ((zWNat u).1 : Rat) ∧
    zW_V u * ((4 ^ u.length : Nat) : Rat) = ((zWNat u).2 : Rat) := by
  induction u with
  | nil => simp [zWNat]
  | cons w u ih =>
    rcases ih with ⟨hW, hWV⟩
    have hpow : ((4 ^ (u.length + 1) : Nat) : Rat) = 4 * ((4 ^ u.length : Nat) : Rat) := by
      rw [Nat.pow_succ, Nat.cast_mul]; simp only [Nat.cast_ofNat]; ring
    cases w with
    | V =>
      dsimp only [zWNat, List.length]
      simp only [zW_cons_V, zW_V_cons_V]
      rw [hpow, Nat.cast_mul, Nat.cast_mul]; simp only [Nat.cast_ofNat]
      constructor <;> linarith
    | K =>
      dsimp only [zWNat, List.length]
      simp only [zW_cons_K, zW_V_cons_K]
      rw [hpow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]; simp only [Nat.cast_ofNat]
      constructor <;> linarith
    | Q =>
      dsimp only [zWNat, List.length]
      simp only [zW_cons_Q, zW_V_cons_Q]
      rw [hpow, Nat.cast_add, Nat.cast_mul, Nat.cast_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_mul]; simp only [Nat.cast_ofNat]
      constructor <;> linarith

lemma le_of_mul_pow4_le {x y : Rat} {n : Nat}
    (h : x * ((4 ^ n : Nat) : Rat) <= y * ((4 ^ n : Nat) : Rat)) :
    x <= y := by
  have hp : 0 < 4 ^ n := by
    have h4 : 4 ^ n = 2 ^ (2 * n) := by rw [Nat.pow_mul]
    rw [h4]; exact zPp (2 * n)
  have hpos : (0 : Rat) < ((4 ^ n : Nat) : Rat) := by exact_mod_cast hp
  rcases lt_or_ge y x with hlt | hle
  · nlinarith
  · exact hle

def checkZWLe (u : List Word) (num den : Nat) : Bool :=
  (zWNat u).1 * den <= num * 4 ^ u.length

lemma checkZWLe_sound (u : List Word) (num den : Nat)
    (h : checkZWLe u num den = true) :
    zW u * (den : Rat) <= (num : Rat) := by
  unfold checkZWLe at h
  rw [decide_eq_true_eq] at h
  have h_rat : ((zWNat u).1 : Rat) * (den : Rat) <= (num : Rat) * ((4 ^ u.length : Nat) : Rat) := by
    exact_mod_cast h
  have hW := (zWNat_sound u).1
  have h_mul : (zW u * (den : Rat)) * ((4 ^ u.length : Nat) : Rat) <=
      (num : Rat) * ((4 ^ u.length : Nat) : Rat) := by
    calc (zW u * (den : Rat)) * ((4 ^ u.length : Nat) : Rat)
      _ = (zW u * ((4 ^ u.length : Nat) : Rat)) * (den : Rat) := by ring
      _ = ((zWNat u).1 : Rat) * (den : Rat) := by rw [hW]
      _ <= (num : Rat) * ((4 ^ u.length : Nat) : Rat) := h_rat
  exact le_of_mul_pow4_le h_mul

def checkZWVLe (u : List Word) (num den : Nat) : Bool :=
  (zWNat u).2 * den <= num * 4 ^ u.length

lemma checkZWVLe_sound (u : List Word) (num den : Nat)
    (h : checkZWVLe u num den = true) :
    zW_V u * (den : Rat) <= (num : Rat) := by
  unfold checkZWVLe at h
  rw [decide_eq_true_eq] at h
  have h_rat : ((zWNat u).2 : Rat) * (den : Rat) <= (num : Rat) * ((4 ^ u.length : Nat) : Rat) := by
    exact_mod_cast h
  have hWV := (zWNat_sound u).2
  have h_mul : (zW_V u * (den : Rat)) * ((4 ^ u.length : Nat) : Rat) <=
      (num : Rat) * ((4 ^ u.length : Nat) : Rat) := by
    calc (zW_V u * (den : Rat)) * ((4 ^ u.length : Nat) : Rat)
      _ = (zW_V u * ((4 ^ u.length : Nat) : Rat)) * (den : Rat) := by ring
      _ = ((zWNat u).2 : Rat) * (den : Rat) := by rw [hWV]
      _ <= (num : Rat) * ((4 ^ u.length : Nat) : Rat) := h_rat
  exact le_of_mul_pow4_le h_mul

lemma z10_le_pow_len (u : List Word) :
    z10 u <= ((2 ^ u.length : Nat) : Rat) - 1 := by
  induction u with
  | nil => simp [z10]
  | cons w u ih =>
    have hpow : ((2 ^ (u.length + 1) : Nat) : Rat) = 2 * ((2 ^ u.length : Nat) : Rat) := by
      rw [Nat.pow_succ, Nat.cast_mul]; norm_num; ring
    have hpos : (1 : Rat) <= ((2 ^ u.length : Nat) : Rat) := by exact_mod_cast (zPp u.length)
    cases w <;> (dsimp only [z10, List.length]; rw [hpow]; linarith)


lemma Parse_VV_inv {a a' g : Nat} {u : List Word} (h : Parse a (V :: V :: u) a' g) :
    Parse (1 + a * 2) (V :: u) a' g := by
  cases h with
  | T hp => exact hp
  | D hw0 _ _ => exact False.elim (hw0 rfl)
  | P hw0 _ _ _ => exact False.elim (hw0 rfl)

lemma Parse_VQ_inv {a a' g : Nat} {u : List Word} (h : Parse a (V :: Q :: u) a' g) :
    Parse (1 + a * 2) (Q :: u) a' g := by
  cases h with
  | T hp => exact hp
  | D hw0 _ _ => exact False.elim (hw0 rfl)
  | P hw0 _ _ _ => exact False.elim (hw0 rfl)

lemma Parse_VK_inv {a a' g : Nat} {u : List Word} (h : Parse a (V :: K :: u) a' g) :
    Parse a u a' g ∨ Parse (1 + a * 2) (K :: u) a' g := by
  cases h with
  | VK hp => exact Or.inl hp
  | T hp => exact Or.inr hp
  | D hw0 _ _ => exact False.elim (hw0 rfl)
  | P hw0 _ _ _ => exact False.elim (hw0 rfl)


lemma dCount_bound_WV (v : List Word) :
    zW_V v <= (3 / 4) * ((2 ^ (dCount v) : Nat) : Rat) + 1 / 4 := by
  cases v with
  | nil => simp [dCount]; norm_num
  | cons a u =>
    have hW := (dCount_bound u).1
    have hWV := (dCount_bound u).2
    have hpow_pos : (1 : Rat) <= ((2 ^ (dCount u) : Nat) : Rat) := by
      exact_mod_cast (zPp (dCount u))
    cases a with
    | V =>
      dsimp only [dCount]; simp only [zW_V_cons_V]
      linarith
    | K =>
      dsimp only [dCount]; rw [zPow1 (dCount u), Nat.cast_add]
      simp only [zW_V_cons_K]
      linarith
    | Q =>
      dsimp only [dCount]; rw [zPow1 (dCount u), Nat.cast_add]
      simp only [zW_V_cons_Q]
      linarith

def cPar7 (b : Nat) : Rat :=
  if b % 2 == 1 then 1 / 7 else 2 / 7

lemma cPar77_bounds (b : Nat) : 1 / 7 <= cPar7 b ∧ cPar7 b <= 2 / 7 := by
  unfold cPar7
  split_ifs <;> constructor <;> norm_num

lemma Scan_zW_contract7 {a b a' b' g : Nat} {u v : List Word}
    (h : Scan a b u a' b' v g) :
    zW_V v <= (6 / 7) * zW u + cPar7 b := by
  induction h with
  | nil a b _ =>
    have hc := (cPar77_bounds b).1
    simp; linarith
  | @T a b a' b' g u v _ _ ih =>
    have hc_in := (cPar77_bounds b).1
    have hc_next : cPar7 ((b - 1) * 2) = 2 / 7 := by
      unfold cPar7; have hmod : ((b - 1) * 2) % 2 = 0 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    have hle := zW_le_two_zW_V u
    simp only [zW_V_cons_V, zW_cons_V]
    linarith
  | @VK0 a k a' b' g u v _ _ ih =>
    have hc_in : cPar7 (k * 2) = 2 / 7 := by
      unfold cPar7; have hmod : (k * 2) % 2 = 0 := by omega
      rw [hmod]; rfl
    have hc_next : cPar7 (1 + (k - 1) * 2) = 1 / 7 := by
      unfold cPar7; have hmod : (1 + (k - 1) * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    rw [hc_in]
    simp only [zW_V_cons_K, zW_cons_V, zW_cons_K]
    linarith
  | @VK1 a k a' b' g u v _ _ ih =>
    have hc_in : cPar7 (1 + k * 2) = 1 / 7 := by
      unfold cPar7; have hmod : (1 + k * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    have hc_next : cPar7 (1 + (k - 1) * 2) = 1 / 7 := by
      unfold cPar7; have hmod : (1 + (k - 1) * 2) % 2 = 1 := by omega
      rw [hmod]; rfl
    rw [hc_next] at ih
    rw [hc_in]
    simp only [zW_V_cons_Q, zW_cons_V, zW_V_cons_K]
    linarith
  | @D a b q1 a' b' g w0 u v hw0 _ _ _ ih =>
    have hc_next := (cPar77_bounds (b / 2)).2
    have hle := zW_le_two_zW_V v
    rw [zW_cons_d hw0]
    unfold cPar7
    split_ifs <;> (simp only [zW_V_cons_Q, zW_V_cons_K]; linarith)
  | @P0 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    have hc_in := (cPar77_bounds b).1
    have hc_next := (cPar77_bounds ((b - 1) * 2)).2
    have hzW := zW_nonneg u
    rw [zW_cons_d hw0, zW_cons_d hw1]
    simp only [zW_V_cons_V]
    linarith
  | @P1 a b q1 q2 a' b' g w0 w1 u v hw0 hw1 _ _ _ _ ih =>
    have hc_in := (cPar77_bounds b).1
    have hc_next := (cPar77_bounds (1 + (b - 1) * 2)).2
    have hzW := zW_nonneg u
    rw [zW_cons_d hw0, zW_cons_d hw1]
    simp only [zW_V_cons_V]
    linarith

lemma zIm {tm : Machine (Fin 2) (Fin 6)} {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep tm c (j + d) = some c') :
    (multiStep tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

namespace Traj114

def u_0 : List Word := [V,K,Q,Q]
def tags_0 : List Nat := [1,5]
def da_0 : List Word := [Q,K,K,Q]
def n_0 : Nat := 0
def u_1 : List Word := [V,K,V,V,Q,K,K,Q]
def tags_1 : List Nat := [1,0,0,3,3,5]
def da_1 : List Word := [Q,K,Q]
def n_1 : Nat := 0
def u_2 : List Word := [V,K,V,V,V,K,Q,V,Q,K,Q]
def tags_2 : List Nat := [1,0,0,1,3,0,4,4]
def da_2 : List Word := [K,Q,K,K,K,Q]
def n_2 : Nat := 1
def u_3 : List Word := [V,K,V,V,V,K,V,Q,V,V,V,K,Q,K,K,K,Q]
def tags_3 : List Nat := [1,0,0,1,0,3,0,0,1,3,4,3,4]
def da_3 : List Word := [K,K,Q,K,K,Q]
def n_3 : Nat := 1
def u_4 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,Q,V,K,V,K,K,Q,K,K,Q]
def tags_4 : List Nat := [1,0,0,1,0,1,0,1,0,3,1,2,4,3,3,4]
def da_4 : List Word := [K,K,Q,K,K,Q]
def n_4 : Nat := 1
def u_5 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,K,K,V,Q,V,V,K,K,V,K,K,Q,K,K,Q]
def tags_5 : List Nat := [1,0,0,1,0,1,0,1,0,0,5,0,3,0,0,5,2,4,3,3,4]
def da_5 : List Word := [K,Q,Q,Q,Q,Q,K,K,K,Q,K,Q]
def n_5 : Nat := 1
def u_6 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,Q,V,V,K,K,V,K,Q,Q,Q,Q,Q,K,K,K,Q,K,Q]
def tags_6 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,3,0,0,5,0,5,5,5,3,3,4,3,4]
def da_6 : List Word := [K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_6 : Nat := 1
def u_7 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,Q,K,V,K,V,K,K,K,Q,K,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_7 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,3,3,1,2,3,4,3,3,5,4,5,3,3,4,3,4]
def da_7 : List Word := [K,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_7 : Nat := 1
def u_8 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,Q,K,V,Q,V,Q,V,K,Q,V,V,V,Q,Q,V,K,V,K,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_8 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,3,3,0,3,0,3,0,5,0,0,0,4,1,2,5,4,3,5,4,5,3,3,4,3,4]
def da_8 : List Word := [K,Q,Q,K,K,Q,Q,K,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_8 : Nat := 1
def u_9 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,Q,K,V,K,V,K,V,V,V,V,V,V,K,V,Q,V,V,V,K,V,V,V,Q,Q,V,K,V,K,Q,Q,K,K,Q,Q,K,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_9 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,3,3,1,2,0,0,0,0,0,1,0,3,0,0,1,0,0,0,4,1,2,5,4,5,3,4,4,5,3,5,4,5,3,3,4,3,4]
def da_9 : List Word := [K,Q,K,Q,K,K,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_9 : Nat := 1
def u_10 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,K,K,V,Q,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,Q,V,V,V,V,Q,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,K,Q,K,K,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_10 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,5,0,3,0,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,3,0,0,0,0,3,0,0,0,3,0,0,0,4,1,2,5,5,3,5,5,3,5,4,5,3,3,5,5,3,5,4,5,3,3,4,3,4]
def da_10 : List Word := [K,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_10 : Nat := 1
def u_11 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,Q,V,V,V,Q,V,V,Q,V,V,V,Q,Q,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_11 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,1,0,0,0,1,0,3,0,0,0,3,0,0,3,0,0,0,4,0,0,3,0,0,0,4,1,0,5,3,3,5,5,5,4,4,5,3,5,3,3,4,5,5,3,3,5,5,5,3,5,4,5,3,3,4,3,4]
def da_11 : List Word := [K,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_11 : Nat := 1
def u_12 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,Q,Q,V,V,V,V,V,V,Q,V,Q,K,V,V,V,Q,K,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,Q,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_12 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,4,0,0,0,0,0,0,3,0,4,0,0,0,3,3,0,0,0,3,0,0,0,4,1,0,5,4,4,3,5,4,5,3,5,5,3,3,5,4,4,3,5,3,4,5,3,3,4,5,4,3,3,5,5,5,3,5,4,5,3,3,4,3,4]
def da_12 : List Word := [K,Q,Q,K,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_12 : Nat := 1
def u_13 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,Q,V,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,Q,V,V,Q,K,V,V,V,K,V,Q,V,V,Q,Q,V,V,V,K,K,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,Q,K,Q,Q,K,Q,Q,K,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def tags_13 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,3,0,0,1,0,0,0,1,0,0,0,0,1,0,0,0,3,0,0,3,3,0,0,1,0,3,0,0,4,0,0,0,5,0,0,0,3,0,0,0,4,1,0,5,4,5,5,4,3,3,5,5,4,3,5,3,5,5,5,5,3,5,3,5,5,3,4,3,3,5,4,3,5,3,4,5,3,3,4,5,4,3,3,5,5,5,3,5,4,5,3,3,4,3,4]
def da_13 : List Word := [K,Q,Q,K,Q,K,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def n_13 : Nat := 1
def u_14 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,Q,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,K,Q,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,K,K,V,V,V,K,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,K,Q,V,V,K,V,Q,V,V,Q,Q,V,V,V,K,K,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,Q,K,Q,K,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]

def head114 : List Word := [V,K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K]
def tags_head114 : List Nat := [1,0,0,1,0,1,0,1,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,1,0,1,0,1,0,0,0,0,1,0,1,0,0,0,1,0,0,1,0,0,0,1,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1]
def v_head114 : List Word := [K,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V]
def a_114 : Nat := 73786976294838206463
def b_114 : Nat := 188754406282887020529
def A_top64 : Nat := 11797150392680438782

def s17 : List Word := [V,V,V,K,K,V,V,V,Q,V,V,V,Q,Q,V,K,V]
def s19 : List Word := s17 ++ [K,Q]
def tags_s19 : List Nat := [0,0,0,5,0,0,0,3,0,0,0,4,1,0,5]
def v_s19 : List Word := [V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V]

def top35_ds : List Word := [Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,K,Q,Q,K,Q,K,Q,Q,K,K,Q,Q,Q,K,K]
def tags_top35 : List Nat := [5,5,5,5,3,5,3,5,5,3,4,3,3,5,4,3,5,3,4,5,3,3]
def v_top35_worst : List Word := [V,V,V,V,K,V,K,V,V,K,V,K,K,V,V,K,V,K,V,V,K,K]

def top27 : List Word := [K,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,K,K,Q,K,Q]
def top28 : List Word := top27 ++ [K]
def tags_top28 : List Nat := [4,5,4,3,3,5,5,5,3,5,4,5,3,3,4,3,4]

def p_114_init : List Word := [V,Q,V,V,K,V,V,V,V,K,V,V,V,V,V,K,V,V,V,V,K,V,V,K,Q,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,K,K,V,V,V,K,V,Q,V,V,V,V,Q,V,Q,V,V,Q,V,K,Q,V,V,K,V,Q,V,V,Q,Q]
def ds_core_init : List Word := [Q,K,Q,K,K,Q,K,K,K,Q,K,Q,Q,Q,Q,K,Q,K,K,K,K,K,K,K,K,Q,K,K,K,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q]
def A_core_init : Nat := 785475795493


set_option maxRecDepth 200000 in
lemma step_0 : Step u_0 u_1 := checkStep_sound n_0 tags_0 u_0 da_0 u_1 (by decide)
set_option maxRecDepth 200000 in
lemma step_1 : Step u_1 u_2 := checkStep_sound n_1 tags_1 u_1 da_1 u_2 (by decide)
set_option maxRecDepth 200000 in
lemma step_2 : Step u_2 u_3 := checkStep_sound n_2 tags_2 u_2 da_2 u_3 (by decide)
set_option maxRecDepth 200000 in
lemma step_3 : Step u_3 u_4 := checkStep_sound n_3 tags_3 u_3 da_3 u_4 (by decide)
set_option maxRecDepth 200000 in
lemma step_4 : Step u_4 u_5 := checkStep_sound n_4 tags_4 u_4 da_4 u_5 (by decide)
set_option maxRecDepth 200000 in
lemma step_5 : Step u_5 u_6 := checkStep_sound n_5 tags_5 u_5 da_5 u_6 (by decide)
set_option maxRecDepth 200000 in
lemma step_6 : Step u_6 u_7 := checkStep_sound n_6 tags_6 u_6 da_6 u_7 (by decide)
set_option maxRecDepth 200000 in
lemma step_7 : Step u_7 u_8 := checkStep_sound n_7 tags_7 u_7 da_7 u_8 (by decide)
set_option maxRecDepth 200000 in
lemma step_8 : Step u_8 u_9 := checkStep_sound n_8 tags_8 u_8 da_8 u_9 (by decide)
set_option maxRecDepth 200000 in
lemma step_9 : Step u_9 u_10 := checkStep_sound n_9 tags_9 u_9 da_9 u_10 (by decide)
set_option maxRecDepth 200000 in
lemma step_10 : Step u_10 u_11 := checkStep_sound n_10 tags_10 u_10 da_10 u_11 (by decide)
set_option maxRecDepth 200000 in
lemma step_11 : Step u_11 u_12 := checkStep_sound n_11 tags_11 u_11 da_11 u_12 (by decide)
set_option maxRecDepth 200000 in
lemma step_12 : Step u_12 u_13 := checkStep_sound n_12 tags_12 u_12 da_12 u_13 (by decide)
set_option maxRecDepth 200000 in
lemma step_13 : Step u_13 u_14 := checkStep_sound n_13 tags_13 u_13 da_13 u_14 (by decide)

lemma rounds_0_14 : Rounds u_0 u_14 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3
    (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7
      (Rounds.next step_8 (Rounds.next step_9 (Rounds.next step_10 (Rounds.next step_11
        (Rounds.next step_12 (Rounds.next step_13 (Rounds.refl u_14))))))))))))))

-- Invariant Good u
def Good (u : List Word) : Prop :=
  ∃ p_114 ds_core A_core L,
    u = head114 ++ p_114 ++ s17 ++ [K, Q, Q, K] ++ ds_core ++ [K, Q] ++ top35_ds ++ top27 ∧
    (∃ p_tail, p_114 = V :: p_tail) ∧
    L = 41 + ds_core.length ∧
    54 <= L ∧
    zDg A_core (L - 41) ds_core ∧
    z13 p_114 * ((2 ^ L : Nat) : Rat) = ((2 ^ 45 : Nat) : Rat) ∧
    zW p_114 <= 29 / 8

set_option maxRecDepth 200000 in
lemma good_u14 : Good u_14 := by
  refine ⟨p_114_init, ds_core_init, A_core_init, 81, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_114_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · exact checkZ13Pow_sound p_114_init 81 45 (by decide)
  · have h := checkZWLe_sound p_114_init 29 8 (by decide)
    norm_num at h
    linarith

-- Fixed-piece Scan lemmas
set_option maxRecDepth 200000 in
lemma Scan_head114 : Scan 0 6 head114 a_114 b_114 v_head114 0 := by
  have h := checkAffineScan_sound tags_head114 0 0 0 6 head114 0 a_114 0 b_114 v_head114 0 0 0 (by decide)
  simpa using h

lemma v_head114_eq : V :: v_head114 = head114 ++ [V] := rfl

lemma Scan_s19 (ap bp : Nat) (hbp : 2 <= bp) :
    Scan ap bp s19 (8 * ap + 9) (4096 * (bp - 2) + 191) v_s19 3 := by
  have h := checkAffineScan_sound tags_s19 1 0 1 2 s19 8 9 4096 191 v_s19 3 ap (bp - 2) (by decide)
  have h_bp : 1 * (bp - 2) + 2 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

lemma Scan_top35 (b35 : Nat) (hb35 : 2 + 4 * z10 top35_ds < (b35 : Rat)) :
    ∃ b_top28 v_top35,
      Scan (2 ^ 61) b35 top35_ds (2 ^ 26) b_top28 v_top35 13 ∧
      zW_V v_top35 <= 23 / 64 ∧
      3 <= b_top28 := by
  rcases checkTopTrace_sound tags_top35 (2 ^ 61) top35_ds (2 ^ 26) v_top35_worst 13 b35 (by decide) hb35
    with ⟨b_top28, v_top35, hS, _, hWV, hb_top28⟩
  have hw0 := checkZWVLe_sound v_top35_worst 23 64 (by decide)
  have hw : zW_V v_top35_worst <= 23 / 64 := by norm_num at hw0; linarith
  exact ⟨b_top28, v_top35, hS, le_trans hWV hw, hb_top28⟩

lemma Scan_top28 (b_top28 : Nat) (hb : 3 <= b_top28) :
    Scan (2 ^ 26) b_top28 top28 0 (32 * (b_top28 - 2) - 10) s17 11 := by
  have h := checkAffineScan_sound tags_top28 0 (2 ^ 26) 1 3 top28 0 0 32 22 s17 11 0 (b_top28 - 3) (by decide)
  have h_in : 1 * (b_top28 - 3) + 3 = b_top28 := by omega
  have h_out : 32 * (b_top28 - 3) + 22 = 32 * (b_top28 - 2) - 10 := by omega
  dsimp at h
  rwa [h_in, h_out] at h


lemma Parse_s19_split {ap a_end g_all : Nat} {rest : List Word}
    (h : Parse ap (s19 ++ Q :: rest) a_end g_all) :
    ∃ g_mid, Parse (8 * (ap + 1) + 1) (Q :: rest) a_end g_mid := by
  change Parse ap ([V,V,V,K,K,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q,Q] ++ rest) a_end g_all at h
  simp only [List.cons_append, List.nil_append] at h
  -- i = 0, 1 (V :: V :: V)
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  -- i = 2 (V :: K :: K :: V)
  rcases Parse_VK_inv h with h | h
  · cases h with
    | D _ hq1 _ => dsimp [dVal] at hq1; omega
    | P _ hw1 _ _ => exact False.elim (hw1 rfl)
  · -- i = 3 (K :: K :: V)
    cases h with
    | D _ hq1 _ => dsimp [dVal] at hq1; omega
    | @P _ q2_3 _ _ _ _ _ _ _ hq2_3 h =>
      have hq2_3_eq : q2_3 = 1 + ap * 2 := by dsimp [dVal] at hq2_3; omega
      subst hq2_3_eq
      -- i = 5, 6, 7 (V :: V :: V :: Q)
      have h := Parse_VV_inv h
      have h := Parse_VV_inv h
      have h := Parse_VQ_inv h
      -- i = 8 (Q :: V)
      cases h with
      | P _ hw1 _ _ => exact False.elim (hw1 rfl)
      | @D _ q1_8 _ _ _ _ _ hq1_8 h =>
        have hq1_8_eq : q1_8 = 8 + ap * 8 := by dsimp [dVal] at hq1_8; omega
        subst hq1_8_eq
        -- i = 9, 10, 11 (V :: V :: V :: Q :: Q)
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VQ_inv h
        -- i = 12 (Q :: Q :: V :: K)
        cases h with
        | @D _ q1_12 _ _ _ _ _ hq1_12 h =>
          have hq1_12_eq : q1_12 = 36 + ap * 32 := by dsimp [dVal] at hq1_12; omega
          subst hq1_12_eq
          cases h with
          | P _ hw1 _ _ => exact False.elim (hw1 rfl)
          | D _ hq1_13 _ => dsimp [dVal] at hq1_13; omega
        | @P _ q2_12 _ _ _ _ _ _ _ hq2_12 h =>
          have hq2_12_eq : q2_12 = 18 + ap * 16 := by dsimp [dVal] at hq2_12; omega
          subst hq2_12_eq
          -- i = 14 (V :: K :: V :: K :: Q :: Q)
          rcases Parse_VK_inv h with h | h
          · -- i = 16 (V :: K :: Q :: Q)
            rcases Parse_VK_inv h with h | h
            · cases h with
              | D _ hq1_18 _ => dsimp [dVal] at hq1_18; omega
              | P _ _ hq2_18 _ => dsimp [dVal] at hq2_18; omega
            · -- i = 17 (K :: Q :: Q)
              cases h with
              | D _ hq1_17 _ => dsimp [dVal] at hq1_17; omega
              | @P _ q2_17 _ g_mid _ _ _ _ _ hq2_17 h =>
                have h_end : q2_17 = 8 * (ap + 1) + 1 := by dsimp [dVal] at hq2_17; omega
                subst h_end
                exact ⟨g_mid, h⟩
          · cases h with
            | P _ hw1 _ _ => exact False.elim (hw1 rfl)
            | D _ hq1_15 _ => dsimp [dVal] at hq1_15; omega

-- Section 6: Main Invariant Closure and Goal Proof
lemma zDg_top64 : zDg A_top64 64 ([K, Q] ++ top35_ds ++ top27) :=
  checkDg_sound A_top64 ([K, Q] ++ top35_ds ++ top27) (by decide)

lemma zDg_bot4 : zDg 6 4 [K, Q, Q, K] :=
  checkDg_sound 6 [K, Q, Q, K] (by decide)

lemma zDg_mid35 {A_core L : Nat} {ds_core : List Word}
    (hL : 54 <= L) (hD : zDg A_core (L - 41) ds_core) :
    ∃ A_mid35,
      zDg A_mid35 (L - 37) ([Q, K] ++ ds_core ++ [K, Q]) ∧
      A_mid35 < 3 * 2 ^ (L - 39) := by
  have h_qk : zDg 1 2 [Q, K] := checkDg_sound 1 [Q, K] (by decide)
  have h_kq : zDg 2 2 [K, Q] := checkDg_sound 2 [K, Q] (by decide)
  have h1 := zDg_append h_qk hD
  have h2 := zDg_append h1 h_kq
  have hlen1 : 2 + (L - 41) = L - 39 := by omega
  have hlen2 : (L - 39) + 2 = L - 37 := by omega
  rw [hlen1] at h2
  rw [hlen2] at h2
  have h_lt := zDg_lt hD
  have h_pow : 2 ^ (L - 39) = 4 * 2 ^ (L - 41) := by
    have heq : L - 39 = (L - 41) + 2 := by omega
    rw [heq, Nat.pow_add]; ring
  exact ⟨1 + A_core * 4 + 2 * 2 ^ (L - 39),
         by simpa [List.append_assoc] using h2,
         by omega⟩

lemma force_a35 {p_114 ds_mid35 : List Word} {ap gp L A_mid35 a35 g_mid : Nat}
    (hL : 54 <= L)
    (hP_p : Parse a_114 p_114 ap gp)
    (hz13 : z13 p_114 * ((2 ^ L : Nat) : Rat) = ((2 ^ 45 : Nat) : Rat))
    (hzW : zW p_114 <= 29 / 8)
    (hD_mid : zDg A_mid35 (L - 37) ds_mid35)
    (hA_mid : A_mid35 < 3 * 2 ^ (L - 39))
    (hP_mid : Parse (8 * (ap + 1) + 1) ds_mid35 a35 g_mid) :
    a35 = 2 ^ 61 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := z12_nonneg p_114
  have hz10_le := z10_z12_le_zW p_114
  have h_diff_hi : ((ap : Rat) + 1) * z13 p_114 - ((a_114 : Rat) + 1) < 8 := by linarith
  have h_powL_pos : (0 : Rat) < ((2 ^ L : Nat) : Rat) := by exact_mod_cast (zPp L)
  have h_mul_lo : ((a_114 : Rat) + 1) * ((2 ^ L : Nat) : Rat) <= ((ap : Rat) + 1) * (z13 p_114 * ((2 ^ L : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (z13 p_114 * ((2 ^ L : Nat) : Rat)) < (((a_114 : Rat) + 1) + 8) * ((2 ^ L : Nat) : Rat) := by
    nlinarith
  rw [hz13] at h_mul_lo h_mul_hi
  have ha114_val : a_114 + 1 = 2 ^ 66 := by decide
  have ha114_r : (a_114 : Rat) + 1 = ((2 ^ 66 : Nat) : Rat) := by exact_mod_cast ha114_val
  rw [ha114_r] at h_mul_lo h_mul_hi
  have h_nat_lo : 2 ^ 66 * 2 ^ L <= (ap + 1) * 2 ^ 45 := by exact_mod_cast h_mul_lo
  have h_nat_hi : (ap + 1) * 2 ^ 45 < (2 ^ 66 + 8) * 2 ^ L := by exact_mod_cast h_mul_hi
  have h_split1 : 2 ^ 66 * 2 ^ L = 2 ^ (L + 21) * 2 ^ 45 := by
    have : 66 + L = (L + 21) + 45 := by omega
    rw [<- Nat.pow_add, <- Nat.pow_add, this]
  have h_split2 : (2 ^ 66 + 8) * 2 ^ L = (2 ^ (L + 21) + 2 ^ (L - 42)) * 2 ^ 45 := by
    have h1 : 66 + L = (L + 21) + 45 := by omega
    have h2 : 3 + L = (L - 42) + 45 := by omega
    have h8 : (8 : Nat) = 2 ^ 3 := by decide
    calc (2 ^ 66 + 8) * 2 ^ L
      _ = 2 ^ 66 * 2 ^ L + 2 ^ 3 * 2 ^ L := by rw [h8]; ring
      _ = 2 ^ (66 + L) + 2 ^ (3 + L) := by rw [<- Nat.pow_add, <- Nat.pow_add]
      _ = 2 ^ ((L + 21) + 45) + 2 ^ ((L - 42) + 45) := by rw [h1, h2]
      _ = (2 ^ (L + 21) + 2 ^ (L - 42)) * 2 ^ 45 := by rw [Nat.pow_add, Nat.pow_add]; ring
  rw [h_split1] at h_nat_lo
  rw [h_split2] at h_nat_hi
  have h_pos45 : 0 < 2 ^ 45 := by decide
  have hap_lo : 2 ^ (L + 21) <= ap + 1 := Nat.le_of_mul_le_mul_right h_nat_lo h_pos45
  have hap_hi : ap + 1 < 2 ^ (L + 21) + 2 ^ (L - 42) := Nat.lt_of_mul_lt_mul_right h_nat_hi
  have h_pow_rel1 : 8 * 2 ^ (L + 21) = 2 ^ 61 * 2 ^ (L - 37) := by
    have h1 : (8 : Nat) = 2 ^ 3 := by decide
    have h2 : 3 + (L + 21) = 61 + (L - 37) := by omega
    rw [h1, <- Nat.pow_add, h2, Nat.pow_add]
  have h_pow_rel2 : 8 * 2 ^ (L - 42) = 2 ^ (L - 39) := by
    have h1 : (8 : Nat) = 2 ^ 3 := by decide
    have h2 : 3 + (L - 42) = L - 39 := by omega
    rw [h1, <- Nat.pow_add, h2]
  have h_pow_rel3 : 4 * 2 ^ (L - 39) = 2 ^ (L - 37) := by
    have h1 : (4 : Nat) = 2 ^ 2 := by decide
    have h2 : 2 + (L - 39) = L - 37 := by omega
    rw [h1, <- Nat.pow_add, h2]
  rcases Parse_zDg_a hP_mid hD_mid with ⟨h_a35_lo, h_a35_hi⟩
  have h_sum_lo : 2 ^ 61 * 2 ^ (L - 37) < 8 * (ap + 1) + 1 + A_mid35 := by omega
  have h_sum_hi : 8 * (ap + 1) + 1 + A_mid35 < (2 ^ 61 + 1) * 2 ^ (L - 37) := by
    have : (2 ^ 61 + 1) * 2 ^ (L - 37) = 2 ^ 61 * 2 ^ (L - 37) + 4 * 2 ^ (L - 39) := by
      rw [h_pow_rel3]; ring
    omega
  have h_pos_m : 0 < 2 ^ (L - 37) := zPp (L - 37)
  have h_lt1 : a35 < 2 ^ 61 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_a35_lo h_sum_hi)
  have h_lt2 : 2 ^ 61 < a35 + 1 := Nat.lt_of_mul_lt_mul_right (lt_trans h_sum_lo h_a35_hi)
  omega

lemma bound_b_mid0_and_b35 {p_114 v_p ds_mid35 v_mid : List Word}
    {ap bp gp L A_mid35 b_mid0 b35 g_mid : Nat}
    (hL : 54 <= L)
    (hS_p : Scan a_114 b_114 p_114 ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : z13 p_114 * ((2 ^ L : Nat) : Rat) = ((2 ^ 45 : Nat) : Rat))
    (hzW : zW p_114 <= 29 / 8)
    (hb_mid0 : b_mid0 = 4096 * (bp - 2) + 191)
    (hD_mid : zDg A_mid35 (L - 37) ds_mid35) :
    2 + 4 * z10 ds_mid35 < (b_mid0 : Rat) ∧
    (Scan (8 * (ap + 1) + 1) b_mid0 ds_mid35 (2 ^ 61) b35 v_mid g_mid ->
     2 + 4 * z10 top35_ds < (b35 : Rat)) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := z10_z12_le_four_zW_V v_p
  have h_cw_p := Scan_zW_contract hS_p
  have hc_b114 := (cPar_bounds b_114).2
  have h_wv_p_lt : zW_V v_p < 4 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= z13 p_114 := by nlinarith
  have h_b114_big : ((2 ^ 67 : Nat) : Rat) + 18 < (b_114 : Rat) := by norm_num [b_114]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 67 : Nat) : Rat) < ((bp : Rat) - 2) * z13 p_114 := by nlinarith
  have h_powL_pos : (0 : Rat) < ((2 ^ L : Nat) : Rat) := by exact_mod_cast (zPp L)
  have h_mul_L : ((2 ^ 67 : Nat) : Rat) * ((2 ^ L : Nat) : Rat) < ((bp : Rat) - 2) * (z13 p_114 * ((2 ^ L : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_L
  have h_pow67 : ((2 ^ 67 : Nat) : Rat) = ((2 ^ 22 : Nat) : Rat) * ((2 ^ 45 : Nat) : Rat) := by norm_num
  rw [h_pow67] at h_mul_L
  have h_pos45 : (0 : Rat) < ((2 ^ 45 : Nat) : Rat) := by norm_num
  have h_bp2_gt : ((2 ^ 22 : Nat) : Rat) * ((2 ^ L : Nat) : Rat) < (bp : Rat) - 2 := by nlinarith
  have h_bmid0_r : (b_mid0 : Rat) = 4096 * ((bp : Rat) - 2) + 191 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub (by omega : 2 <= bp)]; push_cast; ring
  have h_z10_mid := (zDg_z13_z10 hD_mid).2
  have h_powL_split : ((2 ^ L : Nat) : Rat) = ((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat) := by
    have h_nat : 2 ^ L = 2 ^ 37 * 2 ^ (L - 37) := by
      rw [<- Nat.pow_add, Nat.add_sub_of_le (by omega : 37 <= L)]
    exact_mod_cast h_nat
  have h_pow37_val : ((2 ^ 37 : Nat) : Rat) = 137438953472 := by norm_num
  have h_pow22_val : ((2 ^ 22 : Nat) : Rat) = 4194304 := by norm_num
  have h_pow_m_ge1 : (1 : Rat) <= ((2 ^ (L - 37) : Nat) : Rat) := by exact_mod_cast (zPp (L - 37))
  have hb_mid0_ok : 2 + 4 * z10 ds_mid35 < (b_mid0 : Rat) := by
    rw [h_z10_mid, h_bmid0_r]
    rw [h_powL_split, h_pow37_val, h_pow22_val] at h_bp2_gt
    linarith
  refine ⟨hb_mid0_ok, ?_⟩
  intro hS_mid
  have h_delta_mid := (Scan_delta hS_mid).2
  have h_4wv_mid := z10_z12_le_four_zW_V v_mid
  have h_dc_eq := zDg_Scan_dCount hS_mid hD_mid
  have h_dc_le : dCount v_mid <= L - 37 := by omega
  have h_pow_dc : 2 ^ (dCount v_mid) <= 2 ^ (L - 37) := Nat.pow_le_pow_right (by decide) h_dc_le
  have h_pow_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ (L - 37) : Nat) : Rat) := by exact_mod_cast h_pow_dc
  have h_wv_mid_le : zW_V v_mid <= ((2 ^ (L - 37) : Nat) : Rat) - 1 := by
    have hd := (dCount_bound v_mid).2
    linarith
  have h_z13_mid := z13_Scan hS_mid
  have h_z13_ds_mid := (zDg_z13_z10 hD_mid).1
  rw [h_z13_ds_mid] at h_z13_mid
  have h_pow_gmid_ge1 : (1 : Rat) <= ((2 ^ (3 * g_mid) : Nat) : Rat) := by exact_mod_cast (zPp (3 * g_mid))
  have h_z13_vmid_pos := z13_pos v_mid
  have h_z13_vmid_le : z13 v_mid <= ((2 ^ (L - 37) : Nat) : Rat) := by nlinarith
  have h_prod_b35 : ((2 ^ 70 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat) < ((b35 : Rat) - 2) * z13 v_mid := by
    rw [h_bmid0_r] at h_delta_mid
    rw [h_powL_split, h_pow37_val, h_pow22_val] at h_bp2_gt
    have h70 : ((2 ^ 70 : Nat) : Rat) = 1180591620717411303424 := by norm_num
    rw [h70]
    linarith
  have h_b35_2_pos : (0 : Rat) < (b35 : Rat) - 2 := by
    rcases lt_or_ge (0 : Rat) ((b35 : Rat) - 2) with hpos | hle
    · exact hpos
    · have : ((b35 : Rat) - 2) * z13 v_mid <= 0 := mul_nonpos_of_nonpos_of_nonneg hle (le_of_lt h_z13_vmid_pos)
      have h70_pos : (0 : Rat) < ((2 ^ 70 : Nat) : Rat) := by norm_num
      nlinarith
  have h_b35_gt : ((2 ^ 70 : Nat) : Rat) < (b35 : Rat) - 2 := by nlinarith
  have h_top35_z10 : 2 + 4 * z10 top35_ds < ((2 ^ 70 : Nat) : Rat) := by
    have h_len : top35_ds.length = 35 := by decide
    have h_z10 := z10_le_pow_len top35_ds
    rw [h_len] at h_z10
    norm_num at h_z10 ⊢
    linarith
  linarith

lemma bound_zW_p114' {p_114 v_p ds_mid35 v_mid v_top35 : List Word}
    {ap bp gp L A_mid35 b_mid0 b35 g_mid : Nat}
    (hL : 54 <= L)
    (hS_p : Scan a_114 b_114 p_114 ap bp v_p gp)
    (hz13 : z13 p_114 * ((2 ^ L : Nat) : Rat) = ((2 ^ 45 : Nat) : Rat))
    (hzW : zW p_114 <= 29 / 8)
    (hD_mid : zDg A_mid35 (L - 37) ds_mid35)
    (hS_mid : Scan (8 * (ap + 1) + 1) b_mid0 ds_mid35 (2 ^ 61) b35 v_mid g_mid)
    (hWV_top : zW_V v_top35 <= 23 / 64) :
    zW_V (v_p ++ v_s19 ++ v_mid ++ v_top35) <= 463 / 128 := by
  -- Step A: zW_V v_p <= 451 / 128
  have h_cw_p := Scan_zW_contract hS_p
  have hc_b114 : cPar b_114 = 2 / 16 := by
    unfold cPar
    have hmod : b_114 % 2 = 1 := by decide
    rw [hmod]; rfl
  rw [hc_b114] at h_cw_p
  have hA : zW_V v_p <= 451 / 128 := by linarith
  -- z13 bounds
  have h_z13_p := z13_Scan hS_p
  have h_z13_mid := z13_Scan hS_mid
  have h_z13_ds_mid := (zDg_z13_z10 hD_mid).1
  rw [h_z13_ds_mid] at h_z13_mid
  have h_z13_s19 : z13 v_s19 = 1 / 4096 := by
    have h := checkZ13Pow_sound v_s19 12 0 (by decide)
    norm_num at h
    linarith
  have h_wv_s19 : zW_V v_s19 <= 1 / 64 := by
    have h := checkZWVLe_sound v_s19 1 64 (by decide)
    norm_num at h
    linarith
  -- Step B: z13 v_p * zW_V v_s19 <= 1 / 128
  have h_powL_ge54 : (2 ^ 54 : Nat) <= 2 ^ L := Nat.pow_le_pow_right (by decide) hL
  have h_powL_r : ((2 ^ 54 : Nat) : Rat) <= ((2 ^ L : Nat) : Rat) := by exact_mod_cast h_powL_ge54
  have h_z13_p_le : z13 p_114 <= 1 / 512 := by
    have h_pos_p := z13_pos p_114
    have h_mul := mul_le_mul_of_nonneg_left h_powL_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= 1 / 512 := by nlinarith
  have hB : z13 v_p * zW_V v_s19 <= 1 / 128 := by
    have h_wv_nn := zW_V_nonneg v_s19
    nlinarith
  -- Step C: z13 (v_p ++ v_s19) * zW_V v_mid <= 8 / 128
  have h_dc_eq := zDg_Scan_dCount hS_mid hD_mid
  have h_wv_mid_dc := (dCount_bound v_mid).2
  have h_pow_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) * ((2 ^ (2 * g_mid) : Nat) : Rat) = ((2 ^ (L - 37) : Nat) : Rat) := by
    rw [<- h_dc_eq, Nat.pow_add, Nat.cast_mul]
  have h_pow_2g_ge1 : (1 : Rat) <= ((2 ^ (2 * g_mid) : Nat) : Rat) := by exact_mod_cast (zPp (2 * g_mid))
  have h_pow_3g_ge_2g : ((2 ^ (2 * g_mid) : Nat) : Rat) <= ((2 ^ (3 * g_mid) : Nat) : Rat) := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide) (by omega : 2 * g_mid <= 3 * g_mid))
  have h_prod_ps : z13 v_p * z13 v_s19 * ((2 ^ (L - 37) : Nat) : Rat) <= 1 / 16 := by
    have h_splitL : ((2 ^ L : Nat) : Rat) = ((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat) := by
      have h_nat : 2 ^ L = 2 ^ 37 * 2 ^ (L - 37) := by
        rw [<- Nat.pow_add, Nat.add_sub_of_le (by omega : 37 <= L)]
      exact_mod_cast h_nat
    have h_eq : z13 v_p * ((2 ^ (3 * gp) : Nat) : Rat) * ((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat) = ((2 ^ 45 : Nat) : Rat) := by
      calc z13 v_p * ((2 ^ (3 * gp) : Nat) : Rat) * ((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat)
        _ = z13 p_114 * (((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat)) := by rw [h_z13_p]; ring
        _ = z13 p_114 * ((2 ^ L : Nat) : Rat) := by rw [<- h_splitL]
        _ = ((2 ^ 45 : Nat) : Rat) := hz13
    have h_37_val : ((2 ^ 37 : Nat) : Rat) = 137438953472 := by norm_num
    have h_45_val : ((2 ^ 45 : Nat) : Rat) = 35184372088832 := by norm_num
    rw [h_37_val, h_45_val] at h_eq
    have h_vp_gp_L37 : z13 v_p * ((2 ^ (L - 37) : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat) = 256 := by linarith
    have h_vp_L37 : z13 v_p * ((2 ^ (L - 37) : Nat) : Rat) <= 256 := by
      have h_pos_L37 : (0 : Rat) < ((2 ^ (L - 37) : Nat) : Rat) := by exact_mod_cast (zPp (L - 37))
      have h_nn : 0 <= z13 v_p * ((2 ^ (L - 37) : Nat) : Rat) := mul_nonneg (le_of_lt h_z13_vp_pos) (le_of_lt h_pos_L37)
      nlinarith
    rw [h_z13_s19]
    linarith
  have hC : z13 (v_p ++ v_s19) * zW_V v_mid <= 8 / 128 := by
    rw [z13_append]
    have h_wv_mid_le : zW_V v_mid <= ((2 ^ (L - 37) : Nat) : Rat) := by
      have h_dc_le_L37 : 2 ^ (dCount v_mid) <= 2 ^ (L - 37) := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ (L - 37) : Nat) : Rat) := by exact_mod_cast h_dc_le_L37
      linarith
    have h_wv_mid_nn := zW_V_nonneg v_mid
    have h_z13_ps_pos : 0 < z13 v_p * z13 v_s19 := mul_pos h_z13_vp_pos (z13_pos v_s19)
    nlinarith
  -- Step D: z13 (v_p ++ v_s19 ++ v_mid) * zW_V v_top35 <= 3 / 128
  have h_prod_psm : z13 v_p * z13 v_s19 * z13 v_mid <= 1 / 16 := by
    have h_vmid_le : z13 v_mid <= ((2 ^ (L - 37) : Nat) : Rat) := by
      have h_pos_vmid := z13_pos v_mid
      nlinarith
    have h_pos_vmid := z13_pos v_mid
    have h_z13_ps_pos : 0 < z13 v_p * z13 v_s19 := mul_pos h_z13_vp_pos (z13_pos v_s19)
    nlinarith
  have hD : z13 (v_p ++ v_s19 ++ v_mid) * zW_V v_top35 <= 3 / 128 := by
    rw [z13_append, z13_append]
    have h_wv_top_nn := zW_V_nonneg v_top35
    have h_z13_psm_pos : 0 < z13 v_p * z13 v_s19 * z13 v_mid :=
      mul_pos (mul_pos h_z13_vp_pos (z13_pos v_s19)) (z13_pos v_mid)
    nlinarith
  -- Combine A + B + C + D
  have h_app1 := zW_V_append v_p v_s19
  have h_app2 := zW_V_append (v_p ++ v_s19) v_mid
  have h_app3 := zW_V_append (v_p ++ v_s19 ++ v_mid) v_top35
  linarith

lemma bound_b_end_zDg {w_114 v_w114 : List Word} {b_top28 g_w114 k : Nat}
    (hk : 8 <= k)
    (hb_top28 : 3 <= b_top28)
    (hS_w : Scan a_114 b_114 w_114 (2 ^ 26) b_top28 v_w114 g_w114)
    (hz13_vw : z13 v_w114 * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : zW_V v_w114 <= 463 / 128) :
    ∃ A_core' ds_core',
      zDg A_core' (k + 5) ds_core' ∧
      ds_core'.length = k + 5 ∧
      zDg (32 * (b_top28 - 2) - 10) (k + 73)
          ([K, Q, Q, K] ++ ds_core' ++ [K, Q] ++ top35_ds ++ top27) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := z10_z12_le_four_zW_V v_w114
  have hd_hi' : ((b_114 : Rat) - 2) - ((b_top28 : Rat) - 2) * z13 v_w114 <= 463 / 32 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_mul_lo : (((b_114 : Rat) - 2) - 463 / 32) * ((2 ^ k : Nat) : Rat) <= ((b_top28 : Rat) - 2) * (z13 v_w114 * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top28 : Rat) - 2) * (z13 v_w114 * ((2 ^ k : Nat) : Rat)) <= ((b_114 : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
    nlinarith
  rw [hz13_vw, mul_one] at h_mul_lo h_mul_hi
  have hb114_r : (b_114 : Rat) - 2 = (A_top64 : Rat) * 16 + 15 := by norm_num [b_114, A_top64]
  have hb114_1_r : (b_114 : Rat) - 1 = ((A_top64 : Rat) + 1) * 16 := by norm_num [b_114, A_top64]
  rw [hb114_r] at h_mul_lo
  rw [hb114_1_r] at h_mul_hi
  let b_end := 32 * (b_top28 - 2) - 10
  have hb_end_r : (b_end : Rat) = 32 * ((b_top28 : Rat) - 2) - 10 := by
    dsimp [b_end]
    rw [Nat.cast_sub (by omega : 10 <= 32 * (b_top28 - 2)), Nat.cast_mul, Nat.cast_sub (by omega : 2 <= b_top28)]
    push_cast; ring
  have h_pow_k9 : ((2 ^ (k + 9) : Nat) : Rat) = 512 * ((2 ^ k : Nat) : Rat) := by
    have h9 : ((2 ^ 9 : Nat) : Rat) = 512 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h9]; ring
  have h_powk_ge256 : (256 : Rat) <= ((2 ^ k : Nat) : Rat) := by
    have h8 : 2 ^ 8 <= 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    have h8_r : ((2 ^ 8 : Nat) : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast h8
    have h8_val : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rwa [h8_val] at h8_r
  have h_bend_lo_r : (A_top64 : Rat) * ((2 ^ (k + 9) : Nat) : Rat) < (b_end : Rat) := by
    rw [hb_end_r, h_pow_k9]; linarith
  have h_bend_hi_r : (b_end : Rat) < ((A_top64 : Rat) + 1) * ((2 ^ (k + 9) : Nat) : Rat) := by
    rw [hb_end_r, h_pow_k9]; linarith
  have h_bend_lo : A_top64 * 2 ^ (k + 9) < b_end := by exact_mod_cast h_bend_lo_r
  have h_bend_hi : b_end < (A_top64 + 1) * 2 ^ (k + 9) := by exact_mod_cast h_bend_hi_r
  have h_bend_mod16 : b_end % 16 = 6 := by dsimp [b_end]; omega
  let A_core' := (b_end / 16) % (2 ^ (k + 5))
  have h_Acore'_lt : A_core' < 2 ^ (k + 5) := Nat.mod_lt _ (zPp (k + 5))
  rcases zDg_exists (k + 5) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := zDg_len hD_core'
  have h_bot_mid := zDg_append zDg_bot4 hD_core'
  have h_all := zDg_append h_bot_mid zDg_top64
  have h_len_all : (4 + (k + 5)) + 64 = k + 73 := by omega
  have h_pow_k9_eq : 2 ^ (k + 9) = 16 * 2 ^ (k + 5) := by
    have : k + 9 = 4 + (k + 5) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 9)) = A_top64 := by
    have h_pos_k9 : 0 < 2 ^ (k + 9) := zPp (k + 9)
    have h1 := (Nat.le_div_iff_mul_le h_pos_k9).mpr (le_of_lt h_bend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul h_pos_k9).mpr h_bend_hi
    omega
  have h_val_all : 6 + A_core' * 2 ^ 4 + A_top64 * 2 ^ (4 + (k + 5)) = b_end := by
    have h1 : 2 ^ 4 = 16 := by decide
    have h2 : 2 ^ (4 + (k + 5)) = 16 * 2 ^ (k + 5) := by rw [Nat.pow_add]
    rw [h1, h2]
    have h_assoc : A_top64 * (16 * 2 ^ (k + 5)) = 16 * (A_top64 * 2 ^ (k + 5)) := by ring
    rw [h_assoc]
    dsimp [A_core']
    have h_div16 : (b_end / 16) / (2 ^ (k + 5)) = A_top64 := by
      rw [Nat.div_div_eq_div_mul, <- h_pow_k9_eq, h_div_top]
    have h_mod_div := Nat.div_add_mod (b_end / 16) (2 ^ (k + 5))
    rw [h_div16, Nat.mul_comm (2 ^ (k + 5)) A_top64] at h_mod_div
    have h_mod16 := Nat.div_add_mod b_end 16
    omega
  rw [h_len_all, h_val_all] at h_all
  exact ⟨A_core', ds_core', hD_core', h_len_core', by simpa [List.append_assoc] using h_all⟩

lemma Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_114, ds_core, A_core, L, rfl, ⟨p_tail, hp_start⟩, hL_def, hL, hD_core, hz13, hzW⟩
  -- Piece 2: p_114
  have hP_p_ex : ∃ ap gp, Parse a_114 p_114 ap gp := by
    rw [hp_start]; exact Parse_V_start a_114 p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_114_ok : 2 + 4 * z10 p_114 < (b_114 : Rat) := by
    have hz12 := z12_nonneg p_114
    have hz10_le := z10_z12_le_zW p_114
    have hb114_gt : (17 : Rat) < (b_114 : Rat) := by norm_num [b_114]
    linarith
  rcases Scan_of_Parse hP_p b_114 hb_114_ok with ⟨bp, v_p, hS_p, hbp⟩
  -- Piece 3: s19
  have hS_s19 := Scan_s19 ap bp (by omega)
  let b_mid0 := 4096 * (bp - 2) + 191
  -- Piece 4: ds_mid35 = [Q, K] ++ ds_core ++ [K, Q]
  let ds_mid35 := [Q, K] ++ ds_core ++ [K, Q]
  rcases zDg_mid35 hL hD_core with ⟨A_mid35, hD_mid, hA_mid⟩
  have hP_s19_all : ∃ a35 g_all, Parse ap (s19 ++ ds_mid35) a35 g_all := by
    change ∃ a35 g_all, Parse ap (V :: ([V,V,K,K,V,V,V,Q,V,V,V,Q,Q,V,K,V,K,Q] ++ ds_mid35)) a35 g_all
    exact Parse_V_start ap _
  rcases hP_s19_all with ⟨a35, g_all, hP_all⟩
  have hP_mid_ex : ∃ g_mid, Parse (8 * (ap + 1) + 1) ds_mid35 a35 g_mid := by
    dsimp [ds_mid35] at hP_all ⊢
    exact Parse_s19_split hP_all
  rcases hP_mid_ex with ⟨g_mid, hP_mid⟩
  have ha35_eq := force_a35 hL hP_p hz13 hzW hD_mid hA_mid hP_mid
  subst ha35_eq
  have hb_bounds := bound_b_mid0_and_b35 (b35 := 0) (v_mid := []) (g_mid := 0) hL hS_p hbp hz13 hzW rfl hD_mid
  rcases Scan_of_Parse hP_mid b_mid0 hb_bounds.1 with ⟨b35, v_mid, hS_mid, hb35_ge3⟩
  have hb35_ok := (bound_b_mid0_and_b35 hL hS_p hbp hz13 hzW rfl hD_mid).2 hS_mid
  -- Piece 5: top35_ds
  rcases Scan_top35 b35 hb35_ok with ⟨b_top28, v_top35, hS_top35, hWV_top35, hb_top28⟩
  -- Piece 6: top28
  have hS_top28 := Scan_top28 b_top28 hb_top28
  -- Combine Pieces 2 + 3 + 4 + 5 into w_114
  let w_114 := p_114 ++ s19 ++ ds_mid35 ++ top35_ds
  let v_w114 := v_p ++ v_s19 ++ v_mid ++ v_top35
  let g_w114 := gp + 3 + g_mid + 13
  have h_ap_eq : 8 * ap + 9 = 8 * (ap + 1) + 1 := by omega
  rw [h_ap_eq] at hS_s19
  have hS_w114 : Scan a_114 b_114 w_114 (2 ^ 26) b_top28 v_w114 g_w114 := by
    have h23 := Scan_append hS_p hS_s19
    have h234 := Scan_append h23 hS_mid
    have h2345 := Scan_append h234 hS_top35
    simpa [w_114, v_w114, g_w114, List.append_assoc, Nat.add_assoc] using h2345
  -- Combine Piece 1 + w_114 + Piece 6
  have h_u_rep1 :
      (head114 ++ p_114 ++ s17 ++ [K, Q, Q, K] ++ ds_core ++ [K, Q] ++ top35_ds ++ top27) ++ List.replicate 1 K =
      head114 ++ w_114 ++ top28 := by
    dsimp [w_114, s19, ds_mid35, top28, List.replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS_full :
      Scan 0 6 ((head114 ++ p_114 ++ s17 ++ [K, Q, Q, K] ++ ds_core ++ [K, Q] ++ top35_ds ++ top27) ++ List.replicate 1 K)
           0 (32 * (b_top28 - 2) - 10) (v_head114 ++ v_w114 ++ s17) (0 + g_w114 + 11) := by
    rw [h_u_rep1]
    exact Scan_append (Scan_append Scan_head114 hS_w114) hS_top28
  -- Closure bounds for p_114' = V :: v_w114 and b_end
  let k := 8 + 3 * gp + 3 * g_mid
  have hk : 8 <= k := by omega
  have hWV_vw : zW_V v_w114 <= 463 / 128 :=
    bound_zW_p114' hL hS_p hz13 hzW hD_mid hS_mid hWV_top35
  have hz13_vw : z13 v_w114 * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := z13_Scan hS_w114
    have h_w_eq : z13 w_114 = ((2 ^ 40 : Nat) : Rat) := by
      dsimp only [w_114]
      rw [z13_append, z13_append, z13_append]
      have h_s19 : z13 s19 = 1 / 8 := by
        have h := checkZ13Pow_sound s19 3 0 (by decide)
        norm_num at h
        linarith
      have h_top35 : z13 top35_ds = ((2 ^ 35 : Nat) : Rat) := by
        have h := checkZ13Pow_sound top35_ds 0 35 (by decide)
        norm_num at h ⊢
        linarith
      have h_mid := (zDg_z13_z10 hD_mid).1
      have h_splitL : ((2 ^ L : Nat) : Rat) = ((2 ^ 37 : Nat) : Rat) * ((2 ^ (L - 37) : Nat) : Rat) := by
        have h_nat : 2 ^ L = 2 ^ 37 * 2 ^ (L - 37) := by
          rw [<- Nat.pow_add, Nat.add_sub_of_le (by omega : 37 <= L)]
        exact_mod_cast h_nat
      rw [h_s19, h_mid, h_top35]
      rw [h_splitL] at hz13
      norm_num at hz13 ⊢
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w114 = k + 40 := by dsimp [g_w114, k]; omega
    have h40 : ((2 ^ 40 : Nat) : Rat) = 1099511627776 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h40] at h_z13_w
    linarith
  rcases bound_b_end_zDg hk hb_top28 hS_w114 hz13_vw hWV_vw
    with ⟨A_core', ds_core', hD_core', hlen_core', hD_bend⟩
  let da := [K, Q, Q, K] ++ ds_core' ++ [K, Q] ++ top35_ds ++ top27
  let u' := V :: (v_head114 ++ v_w114 ++ s17 ++ da)
  refine ⟨u', ⟨1, 32 * (b_top28 - 2) - 10, v_head114 ++ v_w114 ++ s17, da, k + 73, 0 + g_w114 + 11, hS_full, hD_bend, rfl⟩, ?_⟩
  -- Prove Good u'
  let p_114' := V :: v_w114
  let L' := k + 46
  refine ⟨p_114', ds_core', A_core', L', ?_, ⟨v_w114, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [u', p_114', da, v_head114, head114]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp [L']; omega
  · dsimp [L']; omega
  · have h_L'_41 : L' - 41 = k + 5 := by dsimp [L']; omega
    rwa [h_L'_41]
  · dsimp only [p_114', L', z13]
    have h_L'_split : k + 46 = k + 1 + 45 := by omega
    have h1 : ((2 ^ 1 : Nat) : Rat) = 2 := by norm_num
    have h45 : ((2 ^ 45 : Nat) : Rat) = 35184372088832 := by norm_num
    rw [h_L'_split, Nat.pow_add, Nat.pow_add, Nat.cast_mul, Nat.cast_mul, h1, h45]
    linarith
  · dsimp only [p_114']
    rw [zW_cons_V]
    linarith


end Traj114

namespace Traj103

def u_0 : List Word := [K,K,Q]
def tags_0 : List Nat := [3,4]
def da_0 : List Word := [K,K,Q]
def n_0 : Nat := 0
def u_1 : List Word := [V,K,V,K,K,Q]
def tags_1 : List Nat := [1,2,4]
def da_1 : List Word := [K,K,Q]
def n_1 : Nat := 0
def u_2 : List Word := [V,K,V,Q,V,V,K,K,Q]
def tags_2 : List Nat := [1,0,3,0,0,5,4]
def da_2 : List Word := [K,K,Q,K,K,Q]
def n_2 : Nat := 1
def u_3 : List Word := [V,K,V,V,K,V,V,V,V,K,K,Q,K,K,Q]
def tags_3 : List Nat := [1,0,1,0,0,0,0,5,3,3,3,4]
def da_3 : List Word := [K,Q,Q,K,K,Q]
def n_3 : Nat := 1
def u_4 : List Word := [V,K,V,V,K,V,V,V,V,V,V,Q,Q,K,V,K,Q,Q,K,K,Q]
def tags_4 : List Nat := [1,0,1,0,0,0,0,0,0,4,3,2,5,3,3,4]
def da_4 : List Word := [K,K,Q,Q,Q,Q,K,K,Q]
def n_4 : Nat := 1
def u_5 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,Q,V,V,Q,K,V,K,K,Q,Q,Q,Q,K,K,Q]
def tags_5 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,3,0,0,3,3,0,5,5,5,3,3,4]
def da_5 : List Word := [K,Q,K,K,K,Q,Q,Q,Q,K,K,Q]
def n_5 : Nat := 1
def u_6 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,Q,V,V,K,Q,V,V,V,V,Q,K,V,K,Q,K,K,K,Q,Q,Q,Q,K,K,Q]
def tags_6 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,3,0,1,3,0,0,0,0,3,3,0,5,3,4,5,5,3,3,4]
def da_6 : List Word := [K,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q]
def n_6 : Nat := 1
def u_7 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,K,V,Q,V,V,V,V,K,Q,V,V,Q,V,V,V,Q,K,V,K,K,Q,Q,K,Q,Q,K,Q,Q,Q,Q,K,K,Q]
def tags_7 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,2,0,3,0,0,0,1,3,0,0,3,0,0,0,3,3,1,3,3,5,3,4,5,5,3,3,4]
def da_7 : List Word := [K,K,K,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q]
def n_7 : Nat := 1
def u_8 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,Q,V,V,K,V,V,V,K,V,Q,V,V,K,V,V,V,K,Q,K,V,Q,K,V,Q,V,V,V,Q,K,V,K,K,K,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q]
def tags_8 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,3,0,1,0,0,1,0,3,0,1,0,0,1,3,3,0,4,0,3,0,0,0,3,3,1,4,3,5,4,5,5,3,3,4]
def da_8 : List Word := [K,K,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def n_8 : Nat := 1
def u_9 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,K,V,V,V,K,V,V,K,V,K,V,V,V,K,V,Q,K,V,V,V,K,V,V,V,K,Q,K,V,V,K,V,V,V,V,Q,K,V,K,K,Q,K,Q,K,K,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def tags_9 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,2,0,0,1,0,1,2,0,0,1,0,3,3,0,0,1,0,0,1,3,3,0,1,0,0,0,0,3,3,1,4,3,3,5,3,3,3,5,4,5,5,3,3,4]
def da_9 : List Word := [K,K,Q,K,Q,K,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def n_9 : Nat := 1
def u_10 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,Q,V,V,V,K,V,V,K,V,Q,V,V,V,K,V,V,K,K,V,V,K,V,V,V,K,V,Q,K,V,K,V,V,V,V,V,K,Q,K,V,V,K,K,V,Q,K,K,V,V,V,V,Q,K,V,K,K,Q,K,Q,K,Q,K,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def tags_10 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,3,0,0,1,0,1,0,3,0,0,1,0,0,5,0,1,0,0,1,0,3,3,1,0,0,0,0,1,3,3,0,0,5,0,4,3,0,0,0,0,3,3,1,4,3,4,5,3,3,3,3,5,5,5,3,3,4]
def da_10 : List Word := [K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def n_10 : Nat := 1
def u_11 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,K,K,V,V,V,V,V,K,V,Q,K,V,V,V,V,V,K,V,V,V,V,K,Q,K,V,V,K,V,V,Q,Q,K,K,V,V,V,Q,K,V,K,Q,K,Q,Q,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,K,Q]
def tags_11 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,5,0,0,0,0,1,0,3,3,0,0,0,0,1,0,0,0,1,3,3,0,1,0,0,4,4,0,0,0,3,3,0,5,5,5,4,3,5,5,4,5,4,5,4,5,5,3,3,4]
def da_11 : List Word := [K,K,Q,K,Q,K,Q,Q,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_11 : Nat := 1
def u_12 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,K,K,V,V,V,V,K,V,V,V,V,K,V,Q,K,V,K,V,V,V,V,V,V,V,V,K,Q,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,Q,K,V,K,K,Q,K,Q,K,Q,Q,K,Q,Q,K,K,Q,Q,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,Q,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def tags_12 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,5,0,0,0,1,0,0,0,1,0,3,3,1,0,0,0,0,0,0,0,1,3,0,0,0,0,1,0,0,0,0,0,0,0,0,0,3,3,1,4,4,3,5,3,5,4,5,5,3,3,3,5,5,4,4,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]
def da_12 : List Word := [K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_12 : Nat := 1
def u_13 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,K,K,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,Q,K,V,V,V,K,V,Q,V,V,V,V,Q,K,Q,V,V,V,V,V,V,V,Q,Q,K,K,K,Q,Q,Q,V,V,V,Q,K,V,K,Q,Q,K,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,K,Q,Q,K,K,K,Q,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def tags_13 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,5,0,0,0,0,0,0,0,1,0,3,0,0,0,1,0,0,0,0,0,0,0,0,0,1,3,3,0,0,1,0,3,0,0,0,0,3,4,0,0,0,0,0,0,0,4,3,3,3,5,3,0,0,0,3,3,0,5,3,3,5,5,5,4,5,4,5,5,3,3,3,5,3,3,4,5,5,3,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]
def da_13 : List Word := [K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_13 : Nat := 1
def u_14 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,Q,K,V,V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,Q,K,V,Q,V,V,V,K,Q,V,V,Q,Q,V,V,V,V,V,V,V,V,Q,K,Q,V,Q,K,V,V,V,Q,V,V,V,Q,Q,K,K,K,K,K,Q,V,V,V,Q,K,V,K,Q,Q,Q,K,Q,K,Q,Q,Q,K,Q,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,Q,Q,Q,K,Q,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def tags_14 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,3,3,0,1,0,1,0,0,0,1,0,0,0,0,0,0,0,0,1,3,3,0,3,0,0,1,3,0,0,4,0,0,0,0,0,0,0,0,3,4,0,4,0,0,0,3,0,0,0,4,4,4,4,0,0,0,3,3,0,5,3,3,4,5,5,4,5,3,3,5,5,5,4,5,4,5,5,4,3,5,4,5,5,3,5,5,3,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]
def da_14 : List Word := [K,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_14 : Nat := 1
def u_15 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,K,V,K,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,Q,K,V,K,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,Q,V,V,Q,Q,V,V,V,V,V,Q,Q,V,V,V,V,V,V,V,V,V,K,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,K,K,K,K,Q,K,V,V,V,Q,K,V,K,Q,Q,Q,K,K,Q,Q,Q,Q,K,K,K,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def tags_15 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,5,2,0,1,0,0,0,1,0,0,0,0,0,0,0,0,1,0,3,3,1,0,1,0,3,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,3,0,0,4,0,0,0,0,0,4,0,0,0,0,0,0,0,0,1,0,0,0,0,3,0,0,3,0,0,0,4,3,5,4,3,0,0,0,3,3,0,5,3,4,4,5,4,3,4,5,5,5,3,5,5,4,5,5,5,5,4,3,5,5,3,5,3,4,3,5,5,5,4,3,4,5,5,5,3,3,5,4,5,5,3,5,5,3,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]
def da_15 : List Word := [K,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,K,K,K,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_15 : Nat := 1
def u_16 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,Q,V,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,K,K,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,Q,V,V,Q,V,V,V,V,K,V,V,V,V,Q,V,V,V,V,V,V,V,V,K,V,V,Q,V,Q,V,K,V,V,V,V,K,V,V,V,V,Q,K,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,K,K,K,K,Q,K,V,V,V,Q,K,V,K,Q,K,Q,K,Q,K,Q,K,Q,Q,K,Q,Q,K,Q,K,K,K,K,Q,Q,K,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def tags_16 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,3,0,1,0,0,0,1,0,0,0,0,0,0,0,0,1,0,1,5,0,1,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,1,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,1,0,1,0,0,0,1,0,1,0,0,1,3,0,0,3,0,0,0,1,0,0,0,0,3,0,0,0,0,0,0,0,1,0,0,3,0,3,1,0,0,0,1,0,0,0,0,3,3,0,0,0,0,3,0,0,3,0,0,0,4,3,5,3,5,0,0,0,3,3,0,5,5,4,3,4,5,3,5,5,3,3,3,3,3,5,3,5,3,3,5,3,5,5,5,5,5,5,5,5,4,5,5,5,3,5,5,3,5,5,5,5,5,5,3,5,5,3,5,3,3,3,4,5,5,5,5,4,3,4,5,5,5,3,3,5,4,5,5,3,5,5,3,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]
def da_16 : List Word := [K,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def n_16 : Nat := 1
def u_17 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,Q,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,K,K,V,V,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,K,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,K,Q,V,V,V,V,K,V,V,Q,V,V,Q,K,K,K,Q,V,Q,V,Q,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,K,V,V,V,V,V,V,K,V,V,V,V,Q,K,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,K,K,K,K,Q,K,V,V,V,Q,K,V,K,Q,K,Q,K,Q,Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]

def head103 : List Word := [V,K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V]
def tags_head103 : List Nat := [1,0,1,0,0,0,0,0,0,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,1,0,0,0,0,1,0,0,1,0,1,0,0,0,0,0,1,0,0,0,0,0,0,1,0,0,0,1,0,1,0,0,0,0,0,0,0,0,1,0,1,0,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0]
def v_head103 : List Word := [K,V,V,K,V,V,V,V,V,V,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,K,V,V,V,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V]
def a_103 : Nat := 2305843009213693951
def b_103 : Nat := 5746657428456234994
def A_top58 : Nat := 179583044639257343

def s36 : List Word := [V,V,V,V,K,V,V,V,V,Q,K,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,K,K,K,K,Q,K,V,V,V,Q,K,V]
def s40 : List Word := s36 ++ [K,Q,K,Q]
def tags_s40 : List Nat := [0,0,0,1,0,0,0,0,3,3,0,0,0,0,3,0,0,3,0,0,0,4,3,5,3,5,0,0,0,3,3,0,5,5]
def v_s40 : List Word := [V,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,K,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,K,Q,V,V,V]

def top56 : List Word := [Q,Q,Q,Q,Q,Q,K,Q,K,K,Q,Q,Q,Q,Q,Q,Q,K,K,Q,Q,K,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,K,Q,K,Q,Q,Q,K,K,K,K,K,K,K,K,Q,Q,Q,Q,Q,Q,K,K,Q]
def top57 : List Word := top56 ++ [K]
def tags_top57 : List Nat := [5,5,5,4,3,4,5,5,5,3,3,5,4,5,5,3,5,5,3,4,4,5,3,3,3,3,3,3,3,3,5,5,5,3,3,4]

def p_103_init : List Word := [V,K,V,K,V,V,V,V,K,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,V,K,V,V,V,V,V,V,V,V,V,V,K,V,V,K,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,K,V,V,V,V,V,K,V,V,K,V,V,V,V,K,V,V,K,V,V,V,K,V,Q,V,V,K,V,V,V,K,V,V,V,V,V,K,V,V,V,V,V,V,V,K,V,V,V,K,V,K,K,V,V,V,V,K,V,V,V,V,V,K,Q,V,V,V,V,K,V,V,K,V,V,V,V,K,V,Q,V,V,V,V,K,Q,V,V,V,V,K,V,V,Q,V,V,Q,K,K,K,Q,V,Q,V,Q,K,V,Q,V,V,V,V,V,V,V,V,V,V,V,V,Q,V,V,Q,V,V,V,V,V,V,Q,V,V,Q,V,Q,Q,K,V,V]
def ds_core_init : List Word := [Q,K,Q,K,Q,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,Q,K,Q,K,K,Q,Q,Q,K,K,Q,Q,K,Q,K,Q,Q,Q,Q,Q,K,Q,Q,K,Q,Q,K,Q,Q,Q,K,Q,K,K,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,Q,Q,K,Q,Q,Q,Q,Q,Q,Q,Q,K,K,K,Q,K,Q,Q,Q,Q,Q,Q,Q,K,Q,Q,K,K,Q,Q,K]
def A_core_init : Nat := 33423588619483026965005715444596021


set_option maxRecDepth 200000 in
lemma step_0 : Step u_0 u_1 := checkStep_sound n_0 tags_0 u_0 da_0 u_1 (by decide)
set_option maxRecDepth 200000 in
lemma step_1 : Step u_1 u_2 := checkStep_sound n_1 tags_1 u_1 da_1 u_2 (by decide)
set_option maxRecDepth 200000 in
lemma step_2 : Step u_2 u_3 := checkStep_sound n_2 tags_2 u_2 da_2 u_3 (by decide)
set_option maxRecDepth 200000 in
lemma step_3 : Step u_3 u_4 := checkStep_sound n_3 tags_3 u_3 da_3 u_4 (by decide)
set_option maxRecDepth 200000 in
lemma step_4 : Step u_4 u_5 := checkStep_sound n_4 tags_4 u_4 da_4 u_5 (by decide)
set_option maxRecDepth 200000 in
lemma step_5 : Step u_5 u_6 := checkStep_sound n_5 tags_5 u_5 da_5 u_6 (by decide)
set_option maxRecDepth 200000 in
lemma step_6 : Step u_6 u_7 := checkStep_sound n_6 tags_6 u_6 da_6 u_7 (by decide)
set_option maxRecDepth 200000 in
lemma step_7 : Step u_7 u_8 := checkStep_sound n_7 tags_7 u_7 da_7 u_8 (by decide)
set_option maxRecDepth 200000 in
lemma step_8 : Step u_8 u_9 := checkStep_sound n_8 tags_8 u_8 da_8 u_9 (by decide)
set_option maxRecDepth 200000 in
lemma step_9 : Step u_9 u_10 := checkStep_sound n_9 tags_9 u_9 da_9 u_10 (by decide)
set_option maxRecDepth 200000 in
lemma step_10 : Step u_10 u_11 := checkStep_sound n_10 tags_10 u_10 da_10 u_11 (by decide)
set_option maxRecDepth 200000 in
lemma step_11 : Step u_11 u_12 := checkStep_sound n_11 tags_11 u_11 da_11 u_12 (by decide)
set_option maxRecDepth 200000 in
lemma step_12 : Step u_12 u_13 := checkStep_sound n_12 tags_12 u_12 da_12 u_13 (by decide)
set_option maxRecDepth 200000 in
lemma step_13 : Step u_13 u_14 := checkStep_sound n_13 tags_13 u_13 da_13 u_14 (by decide)
set_option maxRecDepth 200000 in
lemma step_14 : Step u_14 u_15 := checkStep_sound n_14 tags_14 u_14 da_14 u_15 (by decide)
set_option maxRecDepth 200000 in
lemma step_15 : Step u_15 u_16 := checkStep_sound n_15 tags_15 u_15 da_15 u_16 (by decide)
set_option maxRecDepth 200000 in
lemma step_16 : Step u_16 u_17 := checkStep_sound n_16 tags_16 u_16 da_16 u_17 (by decide)

lemma rounds_0_17 : Rounds u_0 u_17 :=
  Rounds.next step_0 (Rounds.next step_1 (Rounds.next step_2 (Rounds.next step_3 (Rounds.next step_4 (Rounds.next step_5 (Rounds.next step_6 (Rounds.next step_7 (Rounds.next step_8 (Rounds.next step_9 (Rounds.next step_10 (Rounds.next step_11 (Rounds.next step_12 (Rounds.next step_13 (Rounds.next step_14 (Rounds.next step_15 (Rounds.next step_16 (Rounds.refl u_17)))))))))))))))))
-- Invariant Good u (5-piece decomposition)
abbrev Good (u : List Word) : Prop :=
  ∃ p_103 ds_core A_core m,
    u = head103 ++ p_103 ++ s36 ++ [K, Q, K, Q, K, Q] ++ ds_core ++ [Q, Q] ++ top56 ∧
    (∃ p_tail, p_103 = V :: p_tail) ∧
    m = 4 + ds_core.length ∧
    18 <= m ∧
    zDg A_core (m - 4) ds_core ∧
    A_core * 32 <= 17 * 2 ^ (m - 4) ∧
    z13 p_103 * ((2 ^ m : Nat) : Rat) = 256 ∧
    zW p_103 <= 13 / 4

set_option maxRecDepth 200000 in
lemma good_u17 : Good u_17 := by
  refine ⟨p_103_init, ds_core_init, A_core_init, 120, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · exact ⟨p_103_init.tail, rfl⟩
  · decide
  · decide
  · exact checkDg_sound A_core_init ds_core_init (by decide)
  · decide
  · have h := checkZ13Pow_sound p_103_init 120 8 (by decide)
    norm_num at h
    exact h
  · have h := checkZWLe_sound p_103_init 13 4 (by decide)
    norm_num at h
    linarith

-- Fixed-piece Scan lemmas
set_option maxRecDepth 200000 in
lemma Scan_head103 : Scan 0 6 head103 a_103 b_103 v_head103 0 := by
  have h := checkAffineScan_sound tags_head103 0 0 0 6 head103 0 a_103 0 b_103 v_head103 0 0 0 (by decide)
  simpa using h

lemma v_head103_eq : V :: v_head103 = head103 ++ [V] := rfl

lemma Scan_s40 (ap bp : Nat) (hbp : 3 <= bp) :
    Scan ap bp s40 (4 * ap + 4) (131072 * (bp - 3) + 105669) v_s40 5 := by
  have h := checkAffineScan_sound tags_s40 1 0 1 3 s40 4 4 131072 105669 v_s40 5 ap (bp - 3) (by decide)
  have h_bp : 1 * (bp - 3) + 3 = bp := by omega
  have h_ap : 1 * ap + 0 = ap := by omega
  rwa [h_ap, h_bp] at h

lemma Scan_top57 (b_top57 : Nat) (hb : 2 <= b_top57) :
    Scan (2 ^ 55) b_top57 top57 0 (64 * (b_top57 - 2) + 42) s36 21 := by
  have h := checkAffineScan_sound tags_top57 0 (2 ^ 55) 1 2 top57 0 0 64 42 s36 21 0 (b_top57 - 2) (by decide)
  have h_in : 1 * (b_top57 - 2) + 2 = b_top57 := by omega
  dsimp at h
  rwa [h_in] at h


-- Parse_s40_split: any Parse of s40 ++ K :: rest splits right after s40
lemma Parse_s40_split {ap a_end g_all : Nat} {rest : List Word}
    (h : Parse ap (s40 ++ K :: rest) a_end g_all) :
    ∃ g_mid, Parse (4 * (ap + 1)) (K :: rest) a_end g_mid := by
  change Parse ap ([V,V,V,V,K,V,V,V,V,Q,K,V,V,V,V,Q,V,V,Q,V,V,V,Q,Q,K,K,K,K,Q,K,V,V,V,Q,K,V,K,Q,K,Q,K] ++ rest) a_end g_all at h
  simp only [List.cons_append, List.nil_append] at h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  have h := Parse_VV_inv h
  rcases Parse_VK_inv h with h | h
  · -- VK at i=3
    have h := Parse_VV_inv h
    have h := Parse_VV_inv h
    have h := Parse_VV_inv h
    have h := Parse_VQ_inv h
    cases h with
    | @D _ q1_9 _ _ _ _ _ hq1_9 h =>
      have hq1_9_eq : q1_9 = 64 + ap * 64 := by dsimp [dVal] at hq1_9; omega
      subst hq1_9_eq
      cases h with
      | @D _ q1_10 _ _ _ _ _ hq1_10 h =>
        have hq1_10_eq : q1_10 = 32 + ap * 32 := by dsimp [dVal] at hq1_10; omega
        subst hq1_10_eq
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VV_inv h
        have h := Parse_VQ_inv h
        cases h with
        | @D _ q1_15 _ _ _ _ _ hq1_15 h =>
          have hq1_15_eq : q1_15 = 264 + ap * 256 := by dsimp [dVal] at hq1_15; omega
          subst hq1_15_eq
          have h := Parse_VV_inv h
          have h := Parse_VQ_inv h
          cases h with
          | @D _ q1_18 _ _ _ _ _ hq1_18 h =>
            have hq1_18_eq : q1_18 = 530 + ap * 512 := by dsimp [dVal] at hq1_18; omega
            subst hq1_18_eq
            have h := Parse_VV_inv h
            have h := Parse_VV_inv h
            have h := Parse_VQ_inv h
            cases h with
            | @D _ q1_22 _ _ _ _ _ hq1_22 h =>
              have hq1_22_eq : q1_22 = 2124 + ap * 2048 := by dsimp [dVal] at hq1_22; omega
              subst hq1_22_eq
              cases h with
              | D _ hq1_23 _ => dsimp [dVal] at hq1_23; omega
              | P _ _ hq2_23 _ => dsimp [dVal] at hq2_23; omega
            | @P _ q2_22 _ _ _ _ _ _ _ hq2_22 h =>
              have hq2_22_eq : q2_22 = 1062 + ap * 1024 := by dsimp [dVal] at hq2_22; omega
              subst hq2_22_eq
              cases h with
              | @D _ q1_24 _ _ _ _ _ hq1_24 h =>
                have hq1_24_eq : q1_24 = 531 + ap * 512 := by dsimp [dVal] at hq1_24; omega
                subst hq1_24_eq
                cases h with
                | D _ hq1_25 _ => dsimp [dVal] at hq1_25; omega
                | @P _ q2_25 _ _ _ _ _ _ _ hq2_25 h =>
                  have hq2_25_eq : q2_25 = 132 + ap * 128 := by dsimp [dVal] at hq2_25; omega
                  subst hq2_25_eq
                  cases h with
                  | @D _ q1_27 _ _ _ _ _ hq1_27 h =>
                    have hq1_27_eq : q1_27 = 66 + ap * 64 := by dsimp [dVal] at hq1_27; omega
                    subst hq1_27_eq
                    cases h with
                    | D _ hq1_28 _ => dsimp [dVal] at hq1_28; omega
                    | @P _ q2_28 _ _ _ _ _ _ _ hq2_28 h =>
                      have hq2_28_eq : q2_28 = 16 + ap * 16 := by dsimp [dVal] at hq2_28; omega
                      subst hq2_28_eq
                      have h := Parse_VV_inv h
                      have h := Parse_VV_inv h
                      have h := Parse_VQ_inv h
                      cases h with
                      | @D _ q1_33 _ _ _ _ _ hq1_33 h =>
                        have hq1_33_eq : q1_33 = 68 + ap * 64 := by dsimp [dVal] at hq1_33; omega
                        subst hq1_33_eq
                        cases h with
                        | @D _ q1_34 _ _ _ _ _ hq1_34 h =>
                          have hq1_34_eq : q1_34 = 34 + ap * 32 := by dsimp [dVal] at hq1_34; omega
                          subst hq1_34_eq
                          rcases Parse_VK_inv h with h | h
                          · -- VK at i=35
                            cases h with
                            | D _ hq1_37 _ => dsimp [dVal] at hq1_37; omega
                            | @P _ q2_37 _ _ _ _ _ _ _ hq2_37 h =>
                              have hq2_37_eq : q2_37 = 8 + ap * 8 := by dsimp [dVal] at hq2_37; omega
                              subst hq2_37_eq
                              cases h with
                              | D _ hq1_39 _ => dsimp [dVal] at hq1_39; omega
                              | P _ _ hq2_39 _ => dsimp [dVal] at hq2_39; omega
                          · -- T at i=35
                            cases h with
                            | D _ hq1_36 _ => dsimp [dVal] at hq1_36; omega
                            | @P _ q2_36 _ _ _ _ _ _ _ hq2_36 h =>
                              have hq2_36_eq : q2_36 = 17 + ap * 16 := by dsimp [dVal] at hq2_36; omega
                              subst hq2_36_eq
                              cases h with
                              | D _ hq1_38 _ => dsimp [dVal] at hq1_38; omega
                              | @P _ q2_38 _ _ _ _ _ _ _ hq2_38 h =>
                                have hq2_38_eq : q2_38 = 4 + ap * 4 := by dsimp [dVal] at hq2_38; omega
                                subst hq2_38_eq
                                have h_end : 4 + ap * 4 = 4 * (ap + 1) := by omega
                                rw [h_end] at h
                                exact ⟨_, h⟩
                        | P _ hw1 _ _ => exact False.elim (hw1 rfl)
                      | P _ _ hq2_33 _ => dsimp [dVal] at hq2_33; omega
                  | @P _ q2_27 _ _ _ _ _ _ _ hq2_27 h =>
                    have hq2_27_eq : q2_27 = 33 + ap * 32 := by dsimp [dVal] at hq2_27; omega
                    subst hq2_27_eq
                    cases h with
                    | D _ hq1_29 _ => dsimp [dVal] at hq1_29; omega
                    | P _ hw1 _ _ => exact False.elim (hw1 rfl)
              | @P _ q2_24 _ _ _ _ _ _ _ hq2_24 h =>
                have hq2_24_eq : q2_24 = 265 + ap * 256 := by dsimp [dVal] at hq2_24; omega
                subst hq2_24_eq
                cases h with
                | D _ hq1_26 _ => dsimp [dVal] at hq1_26; omega
                | P _ _ hq2_26 _ => dsimp [dVal] at hq2_26; omega
          | P _ hw1 _ _ => exact False.elim (hw1 rfl)
        | P _ hw1 _ _ => exact False.elim (hw1 rfl)
      | P _ hw1 _ _ => exact False.elim (hw1 rfl)
    | P _ _ hq2_9 _ => dsimp [dVal] at hq2_9; omega
  · -- T at i=3
    cases h with
    | D _ hq1_4 _ => dsimp [dVal] at hq1_4; omega
    | P _ hw1 _ _ => exact False.elim (hw1 rfl)

-- Section 6: Main Invariant Closure and Goal Proof
lemma zDg_top58 : zDg A_top58 58 ([Q, Q] ++ top56) :=
  checkDg_sound A_top58 ([Q, Q] ++ top56) (by decide)

lemma zDg_bot6 : zDg 42 6 [K, Q, K, Q, K, Q] :=
  checkDg_sound 42 [K, Q, K, Q, K, Q] (by decide)

lemma zDg_mid {A_core m : Nat} {ds_core : List Word}
    (hm : 18 <= m) (hD : zDg A_core (m - 4) ds_core)
    (hA_core : A_core * 32 <= 17 * 2 ^ (m - 4)) :
    ∃ A_mid,
      zDg A_mid m ([K, Q] ++ ds_core ++ [Q, Q]) ∧
      2 <= A_mid ∧
      A_mid <= 2 + 113 * 2 ^ (m - 7) := by
  have h_kq : zDg 2 2 [K, Q] := checkDg_sound 2 [K, Q] (by decide)
  have h_qq : zDg 3 2 [Q, Q] := checkDg_sound 3 [Q, Q] (by decide)
  have h1 := zDg_append h_kq hD
  have h2 := zDg_append h1 h_qq
  have hlen1 : 2 + (m - 4) = m - 2 := by omega
  have hlen2 : (m - 2) + 2 = m := by omega
  rw [hlen1] at h2
  rw [hlen2] at h2
  have h_pow1 : 2 ^ (m - 4) = 8 * 2 ^ (m - 7) := by
    have heq : m - 4 = 3 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  have h_pow2 : 2 ^ (m - 2) = 32 * 2 ^ (m - 7) := by
    have heq : m - 2 = 5 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  exact ⟨2 + A_core * 4 + 3 * 2 ^ (m - 2),
         by simpa [List.append_assoc] using h2,
         by omega,
         by omega⟩

lemma force_a55 {p_103 ds_mid : List Word} {ap gp m A_mid a_top g_mid : Nat}
    (hm : 18 <= m)
    (hP_p : Parse a_103 p_103 ap gp)
    (hz13 : z13 p_103 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : zW p_103 <= 13 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hA_lo : 2 <= A_mid)
    (hA_hi : A_mid <= 2 + 113 * 2 ^ (m - 7))
    (hP_mid : Parse (4 * (ap + 1)) ds_mid a_top g_mid) :
    a_top = 2 ^ 55 := by
  rcases Parse_la hP_p with ⟨hla_lo, hla_hi⟩
  have hz12 := z12_nonneg p_103
  have hz10_le := z10_z12_le_zW p_103
  have h_diff_hi : ((ap : Rat) + 1) * z13 p_103 - ((a_103 : Rat) + 1) < 7 := by linarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_lo : ((a_103 : Rat) + 1) * ((2 ^ m : Nat) : Rat) <= ((ap : Rat) + 1) * (z13 p_103 * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((ap : Rat) + 1) * (z13 p_103 * ((2 ^ m : Nat) : Rat)) < (((a_103 : Rat) + 1) + 7) * ((2 ^ m : Nat) : Rat) := by
    nlinarith
  rw [hz13] at h_mul_lo h_mul_hi
  have ha103_val : a_103 + 1 = 2 ^ 61 := by decide
  have ha103_r : (a_103 : Rat) + 1 = ((2 ^ 61 : Nat) : Rat) := by exact_mod_cast ha103_val
  rw [ha103_r] at h_mul_lo h_mul_hi
  have h_nat_lo : 2 ^ 61 * 2 ^ m <= (ap + 1) * 256 := by exact_mod_cast h_mul_lo
  have h_nat_hi : (ap + 1) * 256 < (2 ^ 61 + 7) * 2 ^ m := by exact_mod_cast h_mul_hi
  have h_256 : (ap + 1) * 256 = (4 * (ap + 1)) * 64 := by ring
  rw [h_256] at h_nat_lo h_nat_hi
  have h_split1 : 2 ^ 61 * 2 ^ m = (2 ^ 55 * 2 ^ m) * 64 := by
    have : (2 ^ 61 : Nat) = 2 ^ 55 * 64 := by decide
    rw [this]; ring
  have h_split2 : (2 ^ 61 + 7) * 2 ^ m = (2 ^ 55 * 2 ^ m + 7 * 2 ^ (m - 6)) * 64 := by
    have h61 : (2 ^ 61 : Nat) = 2 ^ 55 * 64 := by decide
    have hm6 : 2 ^ m = 2 ^ (m - 6) * 64 := by
      have h6 : (64 : Nat) = 2 ^ 6 := rfl
      rw [h6, <- Nat.pow_add, Nat.sub_add_cancel (by omega : 6 <= m)]
    calc (2 ^ 61 + 7) * 2 ^ m
      _ = 2 ^ 61 * 2 ^ m + 7 * 2 ^ m := by ring
      _ = (2 ^ 55 * 64) * 2 ^ m + 7 * (2 ^ (m - 6) * 64) := by rw [h61, hm6]
      _ = (2 ^ 55 * 2 ^ m + 7 * 2 ^ (m - 6)) * 64 := by ring
  rw [h_split1] at h_nat_lo
  rw [h_split2] at h_nat_hi
  have h_pos64 : 0 < 64 := by decide
  have hap_lo : 2 ^ 55 * 2 ^ m <= 4 * (ap + 1) := Nat.le_of_mul_le_mul_right h_nat_lo h_pos64
  have hap_hi : 4 * (ap + 1) < 2 ^ 55 * 2 ^ m + 7 * 2 ^ (m - 6) := Nat.lt_of_mul_lt_mul_right h_nat_hi
  have h_pow_m6 : 2 ^ (m - 6) = 2 * 2 ^ (m - 7) := by
    have heq : m - 6 = 1 + (m - 7) := by omega
    rw [heq, Nat.pow_add]
  have h_pow_m : 2 ^ m = 128 * 2 ^ (m - 7) := by
    have h7 : (128 : Nat) = 2 ^ 7 := rfl
    rw [h7, <- Nat.pow_add, Nat.add_sub_of_le (by omega : 7 <= m)]
  have h_pow_m7_ge : 2048 <= 2 ^ (m - 7) := by
    have h11 : 11 <= m - 7 := by omega
    have hle := Nat.pow_le_pow_right (by decide : 1 <= 2) h11
    simpa using hle
  rcases Parse_zDg_a hP_mid hD_mid with ⟨h_atop_lo, h_atop_hi⟩
  have h_sum_lo : 2 ^ 55 * 2 ^ m < 4 * (ap + 1) + A_mid := by omega
  have h_sum_hi : 4 * (ap + 1) + A_mid < (2 ^ 55 + 1) * 2 ^ m := by
    have : (2 ^ 55 + 1) * 2 ^ m = 2 ^ 55 * 2 ^ m + 128 * 2 ^ (m - 7) := by
      rw [Nat.add_mul, Nat.one_mul, h_pow_m]
    omega
  have h_pos_m : 0 < 2 ^ m := zPp m
  have h_lt1 : a_top < 2 ^ 55 + 1 := Nat.lt_of_mul_lt_mul_right (lt_of_le_of_lt h_atop_lo h_sum_hi)
  have h_lt2 : 2 ^ 55 < a_top + 1 := Nat.lt_of_mul_lt_mul_right (lt_trans h_sum_lo h_atop_hi)
  omega

lemma bound_b_mid0 {p_103 v_p ds_mid : List Word}
    {ap bp gp m A_mid b_mid0 : Nat}
    (hm : 18 <= m)
    (hS_p : Scan a_103 b_103 p_103 ap bp v_p gp)
    (hbp : 3 <= bp)
    (hz13 : z13 p_103 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : zW p_103 <= 13 / 4)
    (hb_mid0 : b_mid0 = 131072 * (bp - 3) + 105669)
    (hD_mid : zDg A_mid m ds_mid) :
    2 + 4 * z10 ds_mid < (b_mid0 : Rat) := by
  have h_delta_p := (Scan_delta hS_p).2
  have h_4wv_p := z10_z12_le_four_zW_V v_p
  have h_cw_p := Scan_zW_contract hS_p
  have hc_b103 := (cPar_bounds b_103).2
  have h_wv_p_lt : zW_V v_p < 4 := by linarith
  have h_z13_p := z13_Scan hS_p
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= z13 p_103 := by nlinarith
  have h_b103_big : ((2 ^ 62 : Nat) : Rat) + 18 < (b_103 : Rat) := by norm_num [b_103]
  have h_bp2_pos : (0 : Rat) <= (bp : Rat) - 2 := by
    have : (2 : Rat) <= (bp : Rat) := by exact_mod_cast (by omega : 2 <= bp)
    linarith
  have h_prod_p : ((2 ^ 62 : Nat) : Rat) < ((bp : Rat) - 2) * z13 p_103 := by nlinarith
  have h_powm_pos : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  have h_mul_m : ((2 ^ 62 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < ((bp : Rat) - 2) * (z13 p_103 * ((2 ^ m : Nat) : Rat)) := by
    nlinarith
  rw [hz13] at h_mul_m
  have h_pow62 : ((2 ^ 62 : Nat) : Rat) = ((2 ^ 54 : Nat) : Rat) * 256 := by norm_num
  rw [h_pow62] at h_mul_m
  have h_bp2_gt : ((2 ^ 54 : Nat) : Rat) * ((2 ^ m : Nat) : Rat) < (bp : Rat) - 2 := by linarith
  have h_bmid0_r : (b_mid0 : Rat) = 131072 * ((bp : Rat) - 3) + 105669 := by
    rw [hb_mid0, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hbp]; push_cast; ring
  have h_z10_mid := (zDg_z13_z10 hD_mid).2
  have h_pow54_val : ((2 ^ 54 : Nat) : Rat) = 18014398509481984 := by norm_num
  have h_powm_ge1 : (1 : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
  rw [h_z10_mid, h_bmid0_r]
  rw [h_pow54_val] at h_bp2_gt
  linarith

lemma bound_zW_p103' {p_103 v_p ds_mid v_mid : List Word}
    {ap bp gp m A_mid b_mid0 b_top57 g_mid : Nat}
    (hm : 18 <= m)
    (hS_p : Scan a_103 b_103 p_103 ap bp v_p gp)
    (hz13 : z13 p_103 * ((2 ^ m : Nat) : Rat) = 256)
    (hzW : zW p_103 <= 13 / 4)
    (hD_mid : zDg A_mid m ds_mid)
    (hS_mid : Scan (4 * (ap + 1)) b_mid0 ds_mid (2 ^ 55) b_top57 v_mid g_mid) :
    zW_V (v_p ++ v_s40 ++ v_mid) <= 13 / 4 := by
  -- Step A: zW_V v_p <= 207 / 64
  have h_cw_p := Scan_zW_contract hS_p
  have hc_b103 : cPar b_103 = 3 / 16 := by
    unfold cPar
    have hmod : b_103 % 2 = 0 := by decide
    rw [hmod]; rfl
  rw [hc_b103] at h_cw_p
  have hA : zW_V v_p <= 207 / 64 := by linarith
  -- z13 bounds
  have h_z13_p := z13_Scan hS_p
  have h_z13_s40 : z13 v_s40 = 1 / 131072 := by
    have h := checkZ13Pow_sound v_s40 17 0 (by decide)
    norm_num at h
    linarith
  have h_wv_s40 : zW_V v_s40 <= 1 / 4 := by
    have h := checkZWVLe_sound v_s40 1 4 (by decide)
    norm_num at h
    linarith
  -- Step B: z13 v_p * zW_V v_s40 <= 1 / 4096
  have h_powm_ge18 : (2 ^ 18 : Nat) <= 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have h_powm_r : ((2 ^ 18 : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_powm_ge18
  have h_z13_p_le : z13 p_103 <= 1 / 1024 := by
    have h_pos_p := z13_pos p_103
    have h_mul := mul_le_mul_of_nonneg_left h_powm_r (le_of_lt h_pos_p)
    rw [hz13] at h_mul
    norm_num at h_mul
    linarith
  have h_pow_gp_ge1 : (1 : Rat) <= ((2 ^ (3 * gp) : Nat) : Rat) := by exact_mod_cast (zPp (3 * gp))
  have h_z13_vp_pos := z13_pos v_p
  have h_z13_vp_le : z13 v_p <= 1 / 1024 := by nlinarith
  have hB : z13 v_p * zW_V v_s40 <= 1 / 4096 := by
    have h_wv_nn := zW_V_nonneg v_s40
    nlinarith
  -- Step C: z13 (v_p ++ v_s40) * zW_V v_mid <= 1 / 512
  have h_dc_eq := zDg_Scan_dCount hS_mid hD_mid
  have h_wv_mid_dc := (dCount_bound v_mid).2
  have h_vp_m : z13 v_p * ((2 ^ m : Nat) : Rat) <= 256 := by
    have h_eq : z13 v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat) = 256 := by
      calc z13 v_p * ((2 ^ m : Nat) : Rat) * ((2 ^ (3 * gp) : Nat) : Rat)
        _ = (z13 v_p * ((2 ^ (3 * gp) : Nat) : Rat)) * ((2 ^ m : Nat) : Rat) := by ring
        _ = z13 p_103 * ((2 ^ m : Nat) : Rat) := by rw [h_z13_p]
        _ = 256 := hz13
    have h_pos_m : (0 : Rat) < ((2 ^ m : Nat) : Rat) := by exact_mod_cast (zPp m)
    have h_nn : 0 <= z13 v_p * ((2 ^ m : Nat) : Rat) := mul_nonneg (le_of_lt h_z13_vp_pos) (le_of_lt h_pos_m)
    nlinarith
  have h_prod_ps : z13 v_p * z13 v_s40 * ((2 ^ m : Nat) : Rat) <= 1 / 512 := by
    rw [h_z13_s40]
    linarith
  have hC : z13 (v_p ++ v_s40) * zW_V v_mid <= 1 / 512 := by
    rw [z13_append]
    have h_wv_mid_le : zW_V v_mid <= ((2 ^ m : Nat) : Rat) := by
      have h_dc_le_m : 2 ^ (dCount v_mid) <= 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
      have h_dc_r : ((2 ^ (dCount v_mid) : Nat) : Rat) <= ((2 ^ m : Nat) : Rat) := by exact_mod_cast h_dc_le_m
      linarith
    have h_wv_mid_nn := zW_V_nonneg v_mid
    have h_z13_ps_pos : 0 < z13 v_p * z13 v_s40 := mul_pos h_z13_vp_pos (z13_pos v_s40)
    nlinarith
  -- Combine A + B + C
  have h_app1 := zW_V_append v_p v_s40
  have h_app2 := zW_V_append (v_p ++ v_s40) v_mid
  linarith

lemma bound_b_end_zDg {w_103 v_w103 : List Word} {b_top57 g_w103 k : Nat}
    (hk : 9 <= k)
    (hb_top57 : 2 <= b_top57)
    (hS_w : Scan a_103 b_103 w_103 (2 ^ 55) b_top57 v_w103 g_w103)
    (hz13_vw : z13 v_w103 * ((2 ^ k : Nat) : Rat) = 1)
    (hWV_vw : zW_V v_w103 <= 13 / 4) :
    ∃ A_core' ds_core',
      zDg A_core' (k + 5) ds_core' ∧
      ds_core'.length = k + 5 ∧
      A_core' * 32 <= 17 * 2 ^ (k + 5) ∧
      zDg (64 * (b_top57 - 2) + 42) (k + 69)
          ([K, Q, K, Q, K, Q] ++ ds_core' ++ [Q, Q] ++ top56) := by
  rcases Scan_delta hS_w with ⟨hd_lo, hd_hi⟩
  have h_4wv := z10_z12_le_four_zW_V v_w103
  have hd_hi' : ((b_103 : Rat) - 2) - ((b_top57 : Rat) - 2) * z13 v_w103 <= 13 := by linarith
  have h_powk_pos : (0 : Rat) < ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_mul_lo : (((b_103 : Rat) - 2) - 13) * ((2 ^ k : Nat) : Rat) <= ((b_top57 : Rat) - 2) * (z13 v_w103 * ((2 ^ k : Nat) : Rat)) := by
    nlinarith
  have h_mul_hi : ((b_top57 : Rat) - 2) * (z13 v_w103 * ((2 ^ k : Nat) : Rat)) <= ((b_103 : Rat) - 1) * ((2 ^ k : Nat) : Rat) := by
    nlinarith
  rw [hz13_vw, mul_one] at h_mul_lo h_mul_hi
  have hb103_r : (b_103 : Rat) - 2 = (A_top58 : Rat) * 32 + 16 := by norm_num [b_103, A_top58]
  have hb103_1_r : (b_103 : Rat) - 1 = (A_top58 : Rat) * 32 + 17 := by norm_num [b_103, A_top58]
  rw [hb103_r] at h_mul_lo
  rw [hb103_1_r] at h_mul_hi
  let b_end := 64 * (b_top57 - 2) + 42
  have hb_end_r : (b_end : Rat) = 64 * ((b_top57 : Rat) - 2) + 42 := by
    dsimp [b_end]
    rw [Nat.cast_add, Nat.cast_mul, Nat.cast_sub hb_top57]
    push_cast; ring
  have h_pow_k11 : ((2 ^ (k + 11) : Nat) : Rat) = 2048 * ((2 ^ k : Nat) : Rat) := by
    have h11 : ((2 ^ 11 : Nat) : Rat) = 2048 := by norm_num
    rw [Nat.pow_add, Nat.cast_mul, h11]; ring
  have h_powk_ge1 : (1 : Rat) <= ((2 ^ k : Nat) : Rat) := by exact_mod_cast (zPp k)
  have h_bend_lo_r : (A_top58 : Rat) * ((2 ^ (k + 11) : Nat) : Rat) < (b_end : Rat) := by
    rw [hb_end_r, h_pow_k11]; linarith
  have h_bend_mid_r : (b_end : Rat) <= (A_top58 : Rat) * ((2 ^ (k + 11) : Nat) : Rat) + 64 * 17 * ((2 ^ k : Nat) : Rat) + 42 := by
    rw [hb_end_r, h_pow_k11]; linarith
  have h_bend_hi_r : (b_end : Rat) < ((A_top58 : Rat) + 1) * ((2 ^ (k + 11) : Nat) : Rat) := by
    rw [hb_end_r, h_pow_k11]; linarith
  have h_bend_lo : A_top58 * 2 ^ (k + 11) < b_end := by exact_mod_cast h_bend_lo_r
  have h_bend_mid : b_end <= A_top58 * 2 ^ (k + 11) + 64 * 17 * 2 ^ k + 42 := by exact_mod_cast h_bend_mid_r
  have h_bend_hi : b_end < (A_top58 + 1) * 2 ^ (k + 11) := by exact_mod_cast h_bend_hi_r
  have h_bend_mod64 : b_end % 64 = 42 := by dsimp [b_end]; omega
  let A_core' := (b_end / 64) % (2 ^ (k + 5))
  have h_Acore'_lt : A_core' < 2 ^ (k + 5) := Nat.mod_lt _ (zPp (k + 5))
  rcases zDg_exists (k + 5) A_core' h_Acore'_lt with ⟨ds_core', hD_core'⟩
  have h_len_core' := zDg_len hD_core'
  have h_bot_mid := zDg_append zDg_bot6 hD_core'
  have h_all := zDg_append h_bot_mid zDg_top58
  have h_len_all : (6 + (k + 5)) + 58 = k + 69 := by omega
  have h_pow_k11_eq : 2 ^ (k + 11) = 64 * 2 ^ (k + 5) := by
    have : k + 11 = 6 + (k + 5) := by omega
    rw [this, Nat.pow_add]
  have h_div_top : b_end / (2 ^ (k + 11)) = A_top58 := by
    have h_pos_k11 : 0 < 2 ^ (k + 11) := zPp (k + 11)
    have h1 := (Nat.le_div_iff_mul_le h_pos_k11).mpr (le_of_lt h_bend_lo)
    have h2 := (Nat.div_lt_iff_lt_mul h_pos_k11).mpr h_bend_hi
    omega
  have h_val_all : 42 + A_core' * 2 ^ 6 + A_top58 * 2 ^ (6 + (k + 5)) = b_end := by
    have h1 : 2 ^ 6 = 64 := by decide
    have h2 : 2 ^ (6 + (k + 5)) = 64 * 2 ^ (k + 5) := by rw [Nat.pow_add]
    rw [h1, h2]
    have h_assoc : A_top58 * (64 * 2 ^ (k + 5)) = 64 * (A_top58 * 2 ^ (k + 5)) := by ring
    rw [h_assoc]
    dsimp [A_core']
    have h_div64 : (b_end / 64) / (2 ^ (k + 5)) = A_top58 := by
      rw [Nat.div_div_eq_div_mul, <- h_pow_k11_eq, h_div_top]
    have h_mod_div := Nat.div_add_mod (b_end / 64) (2 ^ (k + 5))
    rw [h_div64, Nat.mul_comm (2 ^ (k + 5)) A_top58] at h_mod_div
    have h_mod64 := Nat.div_add_mod b_end 64
    omega
  have h_Acore'_le_k : A_core' <= 17 * 2 ^ k := by
    have h_eq6 : 2 ^ 6 = 64 := by decide
    have h_eq_k11 : 2 ^ (6 + (k + 5)) = 2 ^ (k + 11) := by
      have : 6 + (k + 5) = k + 11 := by omega
      rw [this]
    rw [h_eq6, h_eq_k11] at h_val_all
    omega
  have h_Acore'_32 : A_core' * 32 <= 17 * 2 ^ (k + 5) := by
    have h_pow_k5 : 2 ^ (k + 5) = 32 * 2 ^ k := by
      have : k + 5 = 5 + k := by omega
      rw [this, Nat.pow_add]
    omega
  rw [h_len_all, h_val_all] at h_all
  exact ⟨A_core', ds_core', hD_core', h_len_core', h_Acore'_32, by simpa [List.append_assoc] using h_all⟩

lemma Good_step {u : List Word} (hG : Good u) :
    ∃ u', Step u u' ∧ Good u' := by
  rcases hG with ⟨p_103, ds_core, A_core, m, rfl, ⟨p_tail, hp_start⟩, hm_def, hm, hD_core, hA_core, hz13, hzW⟩
  -- Piece 2: p_103
  have hP_p_ex : ∃ ap gp, Parse a_103 p_103 ap gp := by
    rw [hp_start]; exact Parse_V_start a_103 p_tail
  rcases hP_p_ex with ⟨ap, gp, hP_p⟩
  have hb_103_ok : 2 + 4 * z10 p_103 < (b_103 : Rat) := by
    have hz12 := z12_nonneg p_103
    have hz10_le := z10_z12_le_zW p_103
    have hb103_gt : (17 : Rat) < (b_103 : Rat) := by norm_num [b_103]
    linarith
  rcases Scan_of_Parse hP_p b_103 hb_103_ok with ⟨bp, v_p, hS_p, hbp⟩
  -- Piece 3: s40
  have hS_s40 := Scan_s40 ap bp hbp
  let b_mid0 := 131072 * (bp - 3) + 105669
  -- Piece 4: ds_mid = [K, Q] ++ ds_core ++ [Q, Q]
  let ds_mid := [K, Q] ++ ds_core ++ [Q, Q]
  rcases zDg_mid hm hD_core hA_core with ⟨A_mid, hD_mid, hA_lo, hA_hi⟩
  have hP_s40_all : ∃ a_top g_all, Parse ap (s40 ++ ds_mid) a_top g_all := by
    change ∃ a_top g_all, Parse ap (V :: (s40.tail ++ ds_mid)) a_top g_all
    exact Parse_V_start ap _
  rcases hP_s40_all with ⟨a_top, g_all, hP_all⟩
  have hP_mid_ex : ∃ g_mid, Parse (4 * (ap + 1)) ds_mid a_top g_mid := by
    dsimp [ds_mid] at hP_all ⊢
    exact Parse_s40_split hP_all
  rcases hP_mid_ex with ⟨g_mid, hP_mid⟩
  have hatop_eq := force_a55 hm hP_p hz13 hzW hD_mid hA_lo hA_hi hP_mid
  subst hatop_eq
  have hb_mid0_ok := bound_b_mid0 hm hS_p hbp hz13 hzW rfl hD_mid
  rcases Scan_of_Parse hP_mid b_mid0 hb_mid0_ok with ⟨b_top57, v_mid, hS_mid, hb_top57_ge3⟩
  -- Piece 5: top57 = top56 ++ [K]
  have hb_top57 : 2 <= b_top57 := by omega
  have hS_top57 := Scan_top57 b_top57 hb_top57
  -- Combine Pieces 2 + 3 + 4 into w_103
  let w_103 := p_103 ++ s40 ++ ds_mid
  let v_w103 := v_p ++ v_s40 ++ v_mid
  let g_w103 := gp + 5 + g_mid
  have h_ap_eq : 4 * ap + 4 = 4 * (ap + 1) := by omega
  rw [h_ap_eq] at hS_s40
  have hS_w103 : Scan a_103 b_103 w_103 (2 ^ 55) b_top57 v_w103 g_w103 := by
    have h23 := Scan_append hS_p hS_s40
    have h234 := Scan_append h23 hS_mid
    simpa [w_103, v_w103, g_w103, List.append_assoc, Nat.add_assoc] using h234
  -- Combine Piece 1 + w_103 + Piece 5
  have h_u_rep1 :
      (head103 ++ p_103 ++ s36 ++ [K, Q, K, Q, K, Q] ++ ds_core ++ [Q, Q] ++ top56) ++ List.replicate 1 K =
      head103 ++ w_103 ++ top57 := by
    dsimp [w_103, s40, ds_mid, top57, List.replicate]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hS_full :
      Scan 0 6 ((head103 ++ p_103 ++ s36 ++ [K, Q, K, Q, K, Q] ++ ds_core ++ [Q, Q] ++ top56) ++ List.replicate 1 K)
           0 (64 * (b_top57 - 2) + 42) (v_head103 ++ v_w103 ++ s36) (0 + g_w103 + 21) := by
    rw [h_u_rep1]
    exact Scan_append (Scan_append Scan_head103 hS_w103) hS_top57
  -- Closure bounds for p_103' = V :: v_w103 and b_end
  let k := 9 + 3 * gp + 3 * g_mid
  have hk : 9 <= k := by omega
  have hWV_vw : zW_V v_w103 <= 13 / 4 :=
    bound_zW_p103' hm hS_p hz13 hzW hD_mid hS_mid
  have hz13_vw : z13 v_w103 * ((2 ^ k : Nat) : Rat) = 1 := by
    have h_z13_w := z13_Scan hS_w103
    have h_w_eq : z13 w_103 = 64 := by
      dsimp only [w_103]
      rw [z13_append, z13_append]
      have h_s40 : z13 s40 = 1 / 4 := by
        have h := checkZ13Pow_sound s40 2 0 (by decide)
        norm_num at h
        linarith
      have h_mid := (zDg_z13_z10 hD_mid).1
      rw [h_s40, h_mid]
      linarith
    rw [h_w_eq] at h_z13_w
    have h_3gw : 3 * g_w103 = k + 6 := by dsimp [g_w103, k]; omega
    have h6 : ((2 ^ 6 : Nat) : Rat) = 64 := by norm_num
    rw [h_3gw, Nat.pow_add, Nat.cast_mul, h6] at h_z13_w
    linarith
  rcases bound_b_end_zDg hk hb_top57 hS_w103 hz13_vw hWV_vw
    with ⟨A_core', ds_core', hD_core', hlen_core', hA_core', hD_bend⟩
  let da := [K, Q, K, Q, K, Q] ++ ds_core' ++ [Q, Q] ++ top56
  let u' := V :: (v_head103 ++ v_w103 ++ s36 ++ da)
  refine ⟨u', ⟨1, 64 * (b_top57 - 2) + 42, v_head103 ++ v_w103 ++ s36, da, k + 69, 0 + g_w103 + 21, hS_full, hD_bend, rfl⟩, ?_⟩
  -- Prove Good u'
  let p_103' := V :: v_w103
  let m' := k + 9
  refine ⟨p_103', ds_core', A_core', m', ?_, ⟨v_w103, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [u', p_103', da, v_head103, head103]
    simp only [List.cons_append, List.nil_append, List.append_assoc]
  · dsimp [m']; omega
  · dsimp [m']; omega
  · have h_m'_4 : m' - 4 = k + 5 := by dsimp [m']; omega
    rwa [h_m'_4]
  · have h_m'_4 : m' - 4 = k + 5 := by dsimp [m']; omega
    rwa [h_m'_4]
  · dsimp only [p_103', m', z13]
    have h_m'_split : k + 9 = k + 1 + 8 := by omega
    have h1 : ((2 ^ 1 : Nat) : Rat) = 2 := by norm_num
    have h8 : ((2 ^ 8 : Nat) : Rat) = 256 := by norm_num
    rw [h_m'_split, Nat.pow_add, Nat.pow_add, Nat.cast_mul, Nat.cast_mul, h1, h8]
    linarith
  · dsimp only [p_103']
    rw [zW_cons_V]
    exact hWV_vw


end Traj103

end BusyBeaver.WordVKQ
