/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Calculi.WordCalculusB
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordCalculus
set_option quotPrecheck false
set_option maxRecDepth 4000000

variable {α β γ : Type*}
local notation "HalfTape" => ListBlank (Fin 2)
local notation "BitWord" => List (Fin 2)
private abbrev t : BitWord := [1, 1, 0, 0]
private abbrev d0 : BitWord := [0, 0]
private abbrev d1 : BitWord := [1, 0]
open Word
local notation "WordList" => List Word
inductive Reserve : Nat -> Rat -> Prop where
  | even (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 1 -> Reserve ((n + 3) * 2) tau
  | odd (n : Nat) (tau : Rat) : tau * ((2 ^ n : Nat) : Rat) = 3 / 4 -> Reserve (1 + (n + 3) * 2) tau
theorem reserve_step_contract {p : Nat} {tau : Rat} (hI : Reserve p tau) :
    ∃ tau', Reserve (1 + p) tau' /\ tau' <= (3 / 4) * tau := by
  cases hI with
  | even n tau hEq =>
    exact ⟨(3 / 4) * tau, Reserve.odd n ((3 / 4) * tau) (by linarith), le_refl _⟩
  | odd n tau hEq =>
    have hPos := rat_pow_two_pos n
    have hTau : 0 < tau := by nlinarith
    refine ⟨(2 / 3) * tau, ?_, by linarith⟩
    have heq : 1 + (1 + (n + 3) * 2) = ((n + 1) + 3) * 2 := by omega
    rw [heq]
    refine Reserve.even (n + 1) ((2 / 3) * tau) ?_
    rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]
    linarith
theorem reserve_pos_and_le {p : Nat} {tau : Rat} (hI : Reserve p tau) (hP : 16 <= p) :
    0 < tau /\ tau <= 1 / 32 := by
  cases hI with
  | even n tau hEq =>
    have hn : 5 <= n := by omega
    have hPos := rat_pow_two_pos n
    have hB : (32 : Rat) <= ((2 ^ n : Nat) : Rat) := by
      have h1 : 2 ^ 5 <= 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      exact_mod_cast h1
    constructor <;> nlinarith
  | odd n tau hEq =>
    have hn : 5 <= n := by omega
    have hPos := rat_pow_two_pos n
    have hB : (32 : Rat) <= ((2 ^ n : Nat) : Rat) := by
      have h1 : 2 ^ 5 <= 2 ^ n := Nat.pow_le_pow_right (by omega) hn
      exact_mod_cast h1
    constructor <;> nlinarith
theorem reserve_linear_bound (alpha unit f t0 q tau : Rat)
    (ht : 0 < t0) (ha : 0 <= alpha) (_hu : 0 <= unit)
    (h1 : 32 * t0 * unit <= alpha) (h2 : 32 * t0 <= q)
    (h3 : f * q <= unit * q + 5 * alpha) (h4 : 3 / 4 <= tau * t0) :
    f <= alpha * tau * (1 / 4) := by
  by_cases hfu : f <= unit
  · nlinarith
  · nlinarith
theorem reserve_height_bound (p H s : Nat) (alpha unit tau f : Rat)
    (hI : Reserve p tau) (hP : 16 <= p) (hH : (3 * p) / 2 + 5 <= H) (hS : s = (p - 2) / 2)
    (_hA : 0 < alpha) (hU : 0 < unit)
    (hAp : 1 / 2 <= alpha * ((2 ^ p : Nat) : Rat))
    (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hF : f * ((2 ^ (s + s / 2) : Nat) : Rat) <=
      unit * ((2 ^ (s + s / 2) : Nat) : Rat) + 5 * alpha) :
    f <= alpha * tau * (1 / 4) := by
  cases hI with
  | even n tau hTau =>
    have hn : 5 <= n := by omega
    have hLow : 32 * ((2 ^ n : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) := by
      have h1 : 2 ^ (5 + n) <= 2 ^ (s + s / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (5 + n) = 32 * 2 ^ n := by rw [Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hHigh : 64 * ((2 ^ ((n + 3) * 2) : Nat) : Rat) * ((2 ^ n : Nat) : Rat) <=
      ((2 ^ H : Nat) : Rat) := by
      have h1 : 2 ^ (6 + (n + 3) * 2 + n) <= 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (6 + (n + 3) * 2 + n) = 64 * 2 ^ ((n + 3) * 2) * 2 ^ n := by
        rw [Nat.pow_add, Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hPosN := rat_pow_two_pos n
    have hPosP := rat_pow_two_pos ((n + 3) * 2)
    have hGap : 32 * ((2 ^ n : Nat) : Rat) * unit <= alpha := by nlinarith
    exact reserve_linear_bound alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s +
      s / 2) : Nat) : Rat) tau
      hPosN (by linarith) (by linarith) hGap hLow hF (by linarith)
  | odd n tau hTau =>
    have hn : 5 <= n := by omega
    have hLow : 32 * ((2 ^ n : Nat) : Rat) <= ((2 ^ (s + s / 2) : Nat) : Rat) := by
      have h1 : 2 ^ (5 + n) <= 2 ^ (s + s / 2) := Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (5 + n) = 32 * 2 ^ n := by rw [Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hHigh : 64 * ((2 ^ (1 + (n + 3) * 2) : Nat) : Rat) * ((2 ^ n : Nat) : Rat) <=
      ((2 ^ H : Nat) : Rat) := by
      have h1 : 2 ^ (6 + (1 + (n + 3) * 2) + n) <= 2 ^ H :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have h2 : 2 ^ (6 + (1 + (n + 3) * 2) + n) = 64 * 2 ^ (1 + (n + 3) * 2) * 2 ^ n := by
        rw [Nat.pow_add, Nat.pow_add]
      rw [h2] at h1; exact_mod_cast h1
    have hPosN := rat_pow_two_pos n
    have hPosP := rat_pow_two_pos (1 + (n + 3) * 2)
    have hGap : 32 * ((2 ^ n : Nat) : Rat) * unit <= alpha := by nlinarith
    exact reserve_linear_bound alpha unit f ((2 ^ n : Nat) : Rat) ((2 ^ (s +
      s / 2) : Nat) : Rat) tau
      hPosN (by linarith) (by linarith) hGap hLow hF (by linarith)
theorem reserve_index_arith (p : Nat) (hP : 16 <= p) :
    (3 * (p + 1)) / 2 + 5 <= 1 + 3 * (((p - 2) / 2 + 1) / 2) + 3 * ((p - 1) / 2) := by
  omega
theorem reserve_next_step_bound (alpha tau tau' e f e' : Rat) (hA : 0 <= alpha)
    (hTau : tau' <= (3 / 4) * tau) (hE : e <= alpha * ((3 / 64) - tau))
    (hF : f <= alpha * tau * (1 / 4)) (hE' : e' <= (e + f) * (1 / 2)) :
    e' <= (alpha * (1 / 2)) * ((3 / 64) - tau') := by
  nlinarith
theorem phaseScan_scale_pow_eight {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) :
    ∃ g : Nat, wordScale u = wordScale v * ((8 ^ g : Nat) : Rat) /\ u.length = v.length + g := by
  induction hI with
  | nil _ => exact ⟨0, by simp [wordScale], rfl⟩
  | T _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring, by simp; omega⟩
  | pair0 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    refine ⟨g + 1, ?_, by simp; omega⟩
    rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; dsimp [wordScale]; rw [hE]; ring
  | pair1 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    refine ⟨g + 1, ?_, by simp; omega⟩
    rw [Nat.pow_succ, Nat.cast_mul, Nat.cast_ofNat]; dsimp [wordScale]; rw [hE]; ring
  | short00 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring, by simp; omega⟩
  | short01 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring, by simp; omega⟩
  | short10 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring, by simp; omega⟩
  | short11 _ ih =>
    rcases ih with ⟨g, hE, hL⟩
    exact ⟨g, by dsimp [wordScale]; rw [hE]; ring, by simp; omega⟩
theorem phaseScan_length_le {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : PhaseScan k u k' v a b) : v.length <= u.length := by
  rcases phaseScan_scale_pow_eight hI with ⟨g, _, hL⟩
  omega
theorem scan_replicate_Q_K_length (c k k' : Nat) (v : WordList) (l : Rat) (hC : 0 < c)
    (hI : Scan k (List.replicate c Q ++ [K]) k' v l) :
    v.length + (c + 1) / 2 = c + 1 := by
  rcases even_or_odd_mul_two c with ⟨r, rfl⟩ | ⟨r, rfl⟩
  · cases r with
    | zero => omega
    | succ r =>
      have heq : (r + 1) * 2 = 2 + r * 2 := by omega
      rw [heq] at hI ⊢
      rcases scan_even_Q_K_inv r k k' v l hI with ⟨d, n, rfl, _, _⟩
      simp; omega
  · rcases scan_odd_Q_K_inv r k k' v l hI with ⟨rfl, _, _⟩
    simp; omega
theorem phaseScan_replicate_Q_K_length (c k k' : Nat) (v : WordList) (a b : Rat) (hC : 0 < c)
    (hI : PhaseScan k (List.replicate c Q ++ [K]) k' v a b) :
    v.length + (c + 1) / 2 = c + 1 := by
  have hD := digitVal_append (digitVal_replicate_Q c) (DigitVal.zero DigitVal.nil)
  rcases phaseScan_digitVal_loss_bound hI hD with ⟨l, hJ, _, _⟩
  exact scan_replicate_Q_K_length c k k' v l hC hJ
theorem phaseScan_mid_length_bound (k : Nat) (u : WordList) (c : Nat) (mid : WordList) (t0 k' : Nat)
    (v : WordList) (a b : Rat)
    (hC : 0 < c) (hT : 0 < t0) (hU : notEndsWithQ u = true) (hM : notEndsWithQ mid = true)
    (hI : PhaseScan k (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++
      [K])) k' v a b) :
    ∃ g : Nat,
      wordScale (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) =
        wordScale v * ((8 ^ g : Nat) : Rat) /\
      (c + 1) / 2 + (t0 + 1) / 2 <= g := by
  rcases phaseScan_scale_pow_eight hI with ⟨g, hG, hL⟩
  refine ⟨g, hG, ?_⟩
  have hEq0 : u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) =
      u ++ (List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K])) := by
    simp [List.append_assoc]
  rw [hEq0] at hI
  rcases phaseScan_split_of_splitCond hI u _ rfl (Or.inl hU) with ⟨m, x, y, a1, b1, a2, b2, hJ,
    hK, hV, _, _⟩
  have hSplit : List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) =
      (List.replicate c Q ++ [K]) ++ (mid ++ List.replicate t0 Q ++ [K]) := by
    simp [List.append_assoc]
  rcases phaseScan_split_of_splitCond hK (List.replicate c Q ++
    [K]) _ hSplit (Or.inl (by rw [notEndsWithQ_append_singleton]; rfl))
    with ⟨m1, x1, y1, a3, b3, a4, b4, hJ1, hK1, hV1, _, _⟩
  have hSplit2 : mid ++ List.replicate t0 Q ++ [K] = mid ++ (List.replicate t0 Q ++ [K]) := by
    simp [List.append_assoc]
  rcases phaseScan_split_of_splitCond hK1 mid (List.replicate t0 Q ++ [K]) hSplit2 (Or.inl hM)
    with ⟨m2, x2, y2, a5, b5, a6, b6, hJ2, hK2, hV2, _, _⟩
  have hL1 := phaseScan_length_le hJ
  have hL2 := phaseScan_length_le hJ2
  have hO1 := phaseScan_replicate_Q_K_length c m m1 x1 a3 b3 hC hJ1
  have hO2 := phaseScan_replicate_Q_K_length t0 m2 k' y2 a6 b6 hT hK2
  rw [hV, hV1, hV2] at hL
  simp only [List.length_append, List.length_replicate, List.length_cons, List.length_nil] at hL
  omega
theorem phaseScan_digitVal_length_bound (u ds : WordList) (A H k k' : Nat) (v : WordList) (a b :
    Rat)
    (p c : Nat) (mid : WordList) (t0 : Nat)
    (hD : DigitVal A H ds) (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hI : PhaseScan k (u ++ ds ++ [K]) k' v a b)
    (hU : notEndsWithQ u = true) (hM : notEndsWithQ mid = true)
    (hDs : ds = List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q))
    (hP : 16 <= p) (hC : (p - 2) / 2 <= c) (hT : p - 2 <= t0) :
    ∃ J : Nat, (3 * (p + 1)) / 2 + 5 <= J /\
      wordScale (V :: (v ++ [V])) * ((2 ^ J : Nat) : Rat) = 1 := by
  have hEq : u ++ ds ++ [K] =
      u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++ [K]) := by
    rw [hDs]; simp [List.append_assoc]
  have hI' : PhaseScan k (u ++ List.replicate c Q ++ K :: (mid ++ List.replicate t0 Q ++
    [K])) k' v a b := by
    rwa [<- hEq]
  rcases phaseScan_mid_length_bound k u c mid t0 k' v a b (by omega) (by omega) hU hM hI' with ⟨g,
    hGain, hCount⟩
  refine ⟨1 + 3 * g, ?_, ?_⟩
  · have hArith := reserve_index_arith p hP
    omega
  · rw [<- hEq] at hGain
    have hWidth := (digitVal_scale_and_mass hD).1
    rw [wordScale_append, wordScale_append] at hGain
    dsimp [wordScale] at hGain
    rw [hWidth] at hGain
    dsimp [wordScale]
    rw [wordScale_append]
    dsimp [wordScale]
    have hPow8 : ((2 ^ (1 + 3 * g) : Nat) : Rat) = 2 * ((8 ^ g : Nat) : Rat) := by
      have h8 : 2 ^ (1 + 3 * g) = 2 * (2 ^ 3) ^ g := by
        rw [pow_two_one_add, Nat.pow_mul]; ring
      rw [h8]; push_cast; ring
    rw [hPow8]
    nlinarith
theorem scale_ratio_pow_two (p H : Nat) (alpha unit : Rat) (hPH : p <= H)
    (hA : alpha * ((2 ^ p : Nat) : Rat) = 1) (hU : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit * ((2 ^ (H - p) : Nat) : Rat) = alpha := by
  have hPos := rat_pow_two_pos p
  have hEq : 2 ^ H = 2 ^ (H - p) * 2 ^ p := by
    rw [<- Nat.pow_add, Nat.sub_add_cancel hPH]
  have hEqQ : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - p) : Nat) : Rat) * ((2 ^ p : Nat) : Rat) := by
    exact_mod_cast hEq
  rw [hEqQ] at hU
  nlinarith
theorem digitVal_massK_scale_bound (p H B : Nat) (ds : WordList) (alpha unit : Rat)
    (hD : DigitVal B H ds) (hP : 2 <= p) (hPH : p <= H)
    (_hA : 0 < alpha) (hU : 0 < unit) (hSmall : unit <= alpha)
    (hAp : alpha * ((2 ^ p : Nat) : Rat) = 1) (hUh : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hDef : unit * wordMassK ds <= (5 / 2) * alpha) :
    ∃ u, ds = u ++ List.replicate (p - 2) Q := by
  have hShift : unit * ((2 ^ (H - (p - 2)) : Nat) : Rat) = 4 * alpha := by
    have heq : H - (p - 2) = (H - p) + 2 := by omega
    rw [heq, Nat.pow_add, Nat.cast_mul]
    have h4 : ((2 ^ 2 : Nat) : Rat) = 4 := by norm_num
    rw [h4]
    have hDS := scale_ratio_pow_two p H alpha unit hPH hAp hUh
    linarith
  have hZ := digitVal_wordMassK_eq hD
  have hD' : DigitVal B ((H - (p - 2)) + (p - 2)) ds := by
    have heq : (H - (p - 2)) + (p - 2) = H := by omega
    rwa [heq]
  refine digitVal_high_ones_suffix (H - (p - 2)) (p - 2) B ds hD' ?_
  have heq : (H - (p - 2)) + (p - 2) = H := by omega
  rw [heq]
  have hle_q : ((2 ^ H : Nat) : Rat) <= (B : Rat) + ((2 ^ (H - (p - 2)) : Nat) : Rat) := by
    nlinarith
  exact_mod_cast hle_q
theorem digitVal_pos_massK_split {B H : Nat} {ds : WordList} (hI : DigitVal B H ds) (hZ : 0 <
    wordMassK ds) :
    ∃ c w, ds = List.replicate c Q ++ K :: w := by
  induction hI with
  | nil => dsimp [wordMassK] at hZ; linarith
  | @zero A H u _ _ => exact ⟨0, u, rfl⟩
  | @one A H u _ ih =>
    dsimp [wordMassK] at hZ
    rcases ih (by linarith) with ⟨c, w, rfl⟩
    exact ⟨c + 1, w, by rw [List.replicate_succ, List.cons_append]⟩
theorem replicate_Q_prefix_le (c : Nat) :
    ∀ (s : Nat) (u v : WordList),
      List.replicate s Q ++ u = List.replicate c Q ++ K :: v -> s <= c := by
  induction c with
  | zero =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s =>
      rw [List.replicate_succ, List.cons_append] at hE
      simp at hE
  | succ c ih =>
    intro s u v hE
    cases s with
    | zero => omega
    | succ s =>
      rw [List.replicate_succ, List.cons_append, List.replicate_succ, List.cons_append] at hE
      injection hE with _ hE'
      have hle := ih s u v hE'
      omega
theorem replicate_Q_suffix_le_of_notEndsWithQ (u v : WordList) (c s : Nat) (hC : notEndsWithQ u =
    true)
    (hE : u ++ List.replicate c Q = v ++ List.replicate s Q) : s <= c := by
  by_contra hGt
  have hlt : c < s := by omega
  have hs : s = (s - c) + c := by omega
  rw [hs, List.replicate_add, <- List.append_assoc] at hE
  have hEq := List.append_inj_left' hE (by simp)
  subst hEq
  have hpos : 0 < s - c := by omega
  have hsc : s - c = (s - c - 1) + 1 := by omega
  rw [hsc, replicate_succ_append, <- List.append_assoc, notEndsWithQ_append_singleton] at hC
  contradiction
theorem notEndsWithQ_of_append_left (u v : WordList) (hC : notEndsWithQ (u ++
    v) = true) : notEndsWithQ v = true := by
  induction u with
  | nil => exact hC
  | cons a u ih =>
    exact ih (notEndsWithQ_of_cons a (u ++ v) hC)
theorem notEndsWithQ_replicate_Q_cons_K (c : Nat) (mid : WordList) (hM : notEndsWithQ mid = true) :
    notEndsWithQ (List.replicate c Q ++ K :: mid) = true := by
  induction c with
  | zero =>
    cases mid with
    | nil => rfl
    | cons x xs => exact hM
  | succ c ih =>
    rw [List.replicate_succ, List.cons_append]
    cases c with
    | zero => exact ih
    | succ c' => exact ih
theorem digitVal_sandwich_split {B H : Nat} {ds : WordList} (s t0 : Nat)
    (hD : DigitVal B H ds) (hZ : 0 < wordMassK ds)
    (hLo : ∃ u, ds = List.replicate s Q ++ u)
    (hHi : ∃ u, ds = u ++ List.replicate t0 Q) :
    ∃ c mid n, ds = List.replicate c Q ++ K :: (mid ++ List.replicate n Q) /\
      notEndsWithQ mid = true /\ s <= c /\ t0 <= n := by
  rcases hLo with ⟨lo, hLo⟩
  rcases hHi with ⟨hi, hHi⟩
  rcases digitVal_pos_massK_split hD hZ with ⟨c, w, hE⟩
  rcases split_trailing_Q w with ⟨mid, n, rfl, hM⟩
  refine ⟨c, mid, n, hE, hM, ?_, ?_⟩
  · exact replicate_Q_prefix_le c s lo (mid ++ List.replicate n Q) (hLo.symm.trans hE)
  · have hEq : (List.replicate c Q ++ K :: mid) ++ List.replicate n Q =
        hi ++ List.replicate t0 Q := by
      simpa [List.append_assoc] using hE.symm.trans hHi
    exact replicate_Q_suffix_le_of_notEndsWithQ (List.replicate c Q ++ K :: mid) hi n t0
      (notEndsWithQ_replicate_Q_cons_K c mid hM) hEq
theorem wordEffect_preserves_ends_with_V {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) (hEnd : ∃ w, u = w ++ [V]) :
    ∃ w, v = w ++ [V] := by
  rcases hEnd with ⟨w, rfl⟩
  change WordEffect n (w ++ List.replicate 1 V) b v at hI
  rcases wordEffect_append_replicate_V_inv w 1 n b v hI with ⟨x, _, hEq, _⟩
  exact ⟨x, hEq⟩
theorem wordScale_replicate_V_le_inv_65536 (p : Nat) (hP : 16 <= p) :
    wordScale (List.replicate p V) <= 1 / 65536 := by
  have hW := (wordMass_and_scale_replicate_V p).2
  have hPos := wordScale_pos (List.replicate p V)
  have hB : (65536 : Rat) <= ((2 ^ p : Nat) : Rat) := by
    have h1 : 2 ^ 16 <= 2 ^ p := Nat.pow_le_pow_right (by omega) hP
    exact_mod_cast h1
  nlinarith
theorem unit_le_alpha_div_1024 (p H : Nat) (alpha unit : Rat) (hPH : p + 11 <= H)
    (_hA : 0 < alpha) (hU : 0 < unit)
    (hAp : 1 / 2 <= alpha * ((2 ^ p : Nat) : Rat))
    (hUh : unit * ((2 ^ H : Nat) : Rat) = 1) :
    unit <= alpha * (1 / 1024) := by
  have hHigh : 2048 * ((2 ^ p : Nat) : Rat) <= ((2 ^ H : Nat) : Rat) := by
    have h1 : 2 ^ (11 + p) <= 2 ^ H := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 ^ (11 + p) = 2048 * 2 ^ p := by rw [Nat.pow_add]
    rw [h2] at h1; exact_mod_cast h1
  have hPos := rat_pow_two_pos p
  nlinarith
theorem step_mass_contraction_ineq (alpha e f unit delta R e' rho : Rat)
    (hA : 0 < alpha) (_hE0 : 0 <= e) (_hF0 : 0 <= f) (hU0 : 0 <= unit)
    (hE : e <= alpha * (3 / 64)) (hF : f <= alpha * (1 / 128)) (hU : unit <= alpha * (1 / 1024))
    (_hE'0 : 0 <= e') (hE' : e' <= (e + f) * (1 / 2))
    (hRlo : rho * (1 / 2) <= R) (hRhi : R <= rho * (1 / 2) + 2 * e')
    (hDlo : 2 * alpha + rho - e * (1 / 4) - 3 * f <= delta)
    (hDhi : delta <= 2 * alpha + rho + 4 * e + 4 * f) :
    (3 / 4) * alpha <= delta * (1 / 2) - 4 * unit - R /\
    delta * (1 / 2) - 4 * unit - R <= (5 / 4) * alpha := by
  constructor <;> linarith
theorem carry_budget_contraction_ineq (J k carry : Nat) (alpha unit delta R rho : Rat)
    (_hPos : 0 < alpha) (hSmall : alpha <= 1 / 32) (hUnit : 0 < unit) (hTiny : unit <=
      alpha * (1 / 1024))
    (hHeight : unit * ((2 ^ J : Nat) : Rat) = 1)
    (hRho0 : 0 <= rho) (hRho : rho <= 2 * alpha)
    (hDl : (7 / 4) * alpha + rho <= delta) (hDu : delta <= (9 / 4) * alpha + rho)
    (hRl : rho * (1 / 2) <= R) (hRu : R <= rho * (1 / 2) + alpha * (1 / 4))
    (hK : (k : Rat) * unit = 2 + 4 * unit - delta * (1 / 2))
    (hC : ((1 + carry : Nat) : Rat) * unit = 1 + R) :
    ∃ A B : Nat, A + 2 ^ J = k /\ B + 2 ^ J = A + carry /\
      2 ^ J <= A * 2 /\ A < 2 ^ J /\ 2 ^ J <= B * 2 /\ B < 2 ^ J := by
  push_cast at hC
  have hK_gt : ((2 ^ J : Nat) : Rat) + ((2 ^ J : Nat) : Rat) * (1 / 2) <= (k : Rat) := by nlinarith
  have hK_lt : (k : Rat) < ((2 ^ J : Nat) : Rat) * 2 := by nlinarith
  have hB_gt : ((2 ^ J : Nat) : Rat) * 2 + ((2 ^ J : Nat) : Rat) * (1 / 2) <=
    (k : Rat) + (carry : Rat) := by nlinarith
  have hB_lt : (k : Rat) + (carry : Rat) < ((2 ^ J : Nat) : Rat) * 3 := by nlinarith
  have hK2 : 2 ^ J * 3 <= k * 2 := by
    have h1 : ((2 ^ J : Nat) : Rat) * 3 <= (k : Rat) * 2 := by linarith
    exact_mod_cast h1
  have hK3 : k < 2 ^ J * 2 := by
    have h1 : (k : Rat) < ((2 ^ J : Nat) : Rat) * 2 := by linarith
    exact_mod_cast h1
  have hB2 : 2 ^ J * 5 <= (k + carry) * 2 := by
    have h1 : ((2 ^ J : Nat) : Rat) * 5 <= ((k : Rat) + (carry : Rat)) * 2 := by linarith
    exact_mod_cast h1
  have hB3 : k + carry < 2 ^ J * 3 := by
    have h1 : (k : Rat) + (carry : Rat) < ((2 ^ J : Nat) : Rat) * 3 := by linarith
    exact_mod_cast h1
  refine ⟨k - 2 ^ J, k + carry - (2 ^ J + 2 ^ J), by omega, by omega, by omega, by omega,
    by omega, by omega⟩
inductive Copy : Nat -> Nat -> WordList -> WordList -> Nat -> Nat -> Prop where
  | nil (n k : Nat) : Copy n k [] [] n k
  | T {n k : Nat} {u v : WordList} {b k' : Nat} :
      Copy (1 + n * 2) (2 + k * 2) u v b k' -> Copy n (3 + k) (V :: u) (V :: v) b k'
  | d00 {n k : Nat} {u v : WordList} {b k' : Nat} :
      Copy n (k * 2) u v b k' -> Copy (n * 2) (2 + k * 4) (K :: u) (K :: v) b k'
  | d01 {n k : Nat} {u v : WordList} {b k' : Nat} :
      Copy n (1 + k * 2) u v b k' -> Copy (1 + n * 2) (2 + k * 4) (K :: u) (Q :: v) b k'
  | d10 {n k : Nat} {u v : WordList} {b k' : Nat} :
      Copy n (1 + k * 2) u v b k' -> Copy (n * 2) (4 + k * 4) (Q :: u) (Q :: v) b k'
  | d11 {n k : Nat} {u v : WordList} {b k' : Nat} :
      Copy (1 + n) (k * 2) u v b k' -> Copy (1 + n * 2) (4 + k * 4) (Q :: u) (K :: v) b k'
theorem wordEffect_of_copy {n k : Nat} {u v : WordList} {b k' : Nat} (hI : Copy n k u v b k') :
    WordEffect n u b v := by
  induction hI with
  | nil n k => exact WordEffect.nil n
  | T _ ih => exact WordEffect.T ih
  | d00 _ ih => exact WordEffect.d00 ih
  | d01 _ ih => exact WordEffect.d01 ih
  | d10 _ ih => exact WordEffect.d10 ih
  | d11 _ ih => exact WordEffect.d11 ih
theorem copy_append {n k : Nat} {u v : WordList} {b k' : Nat} (h1 : Copy n k u v b k') :
    ∀ {w x : WordList} {c k'' : Nat}, Copy b k' w x c k'' -> Copy n k (u ++ w) (v ++ x) c k'' := by
  induction h1 with
  | nil _ _ => intro w x c k'' h2; exact h2
  | T _ ih => intro w x c k'' h2; exact Copy.T (ih h2)
  | d00 _ ih => intro w x c k'' h2; exact Copy.d00 (ih h2)
  | d01 _ ih => intro w x c k'' h2; exact Copy.d01 (ih h2)
  | d10 _ ih => intro w x c k'' h2; exact Copy.d10 (ih h2)
  | d11 _ ih => intro w x c k'' h2; exact Copy.d11 (ih h2)
theorem copy_replicate_V (q : Nat) :
    ∀ (n k : Nat),
      Copy n (4 + k) (List.replicate q V) (List.replicate q V) ((1 + n) * 2 ^ q - 1) (4 +
      k * 2 ^ q) := by
  induction q with
  | zero =>
    intro n k
    have h1 : (1 + n) * 2 ^ 0 - 1 = n := by simp
    have h2 : 4 + k * 2 ^ 0 = 4 + k := by simp
    rw [h1, h2]
    exact Copy.nil n (4 + k)
  | succ q ih =>
    intro n k
    rw [List.replicate_succ]
    have hpos := pow_two_pos q
    have hSub := ih (1 + n * 2) (k * 2)
    have h1 : (1 + (1 + n * 2)) * 2 ^ q - 1 = (1 + n) * 2 ^ (q + 1) - 1 := by
      rw [Nat.pow_succ]; ring_nf
    have h3 : 4 + (k * 2) * 2 ^ q = 4 + k * 2 ^ (q + 1) := by
      rw [Nat.pow_succ]; ring
    rw [h1, h3] at hSub
    have h4 : 4 + k = 3 + (1 + k) := by omega
    have h5 : 2 + (1 + k) * 2 = 4 + k * 2 := by omega
    rw [h4]
    refine Copy.T ?_
    rwa [h5]
theorem wordEffect_excess_bounds {n : Nat} {u : WordList} {b : Nat} {v : WordList}
    (hI : WordEffect n u b v) :
    0 <= ((1 + b : Nat) : Rat) * wordScale u - ((1 + n : Nat) : Rat) /\
    ((1 + b : Nat) : Rat) * wordScale u - ((1 + n : Nat) : Rat) <= 2 * wordMass u := by
  have hBud := wordEffect_budget_eq hI
  have hW := wordEffect_preserves_scale_and_mass hI
  have hSu := wordMass_eq_add u
  have hSv := wordMass_eq_add v
  have hNu := wordMass_nonneg u
  have hNv := wordMass_nonneg v
  constructor <;> linarith
theorem exists_wordEffect_carry_one {n : Nat} {da : WordList} {A H B : Nat}
    (hD : DigitVal A H da) (hSum : A + n = B + 2 ^ H) (hBound : B < 2 ^ H) :
    ∃ d, DigitVal B H d /\ WordEffect n (da ++ [Q]) 1 (d ++ [K]) := by
  rcases exists_wordEffect da n with ⟨b, d, hE⟩
  rcases wordEffect_digitVal hE hD with ⟨C, hCd, hEq⟩
  have hCb := lt_pow_of_digitVal hCd
  have hb1 : b = 1 := by
    rcases b with _ | _ | b'
    · omega
    · rfl
    · have : 2 ^ H + 2 ^ H <= (b' + 1 + 1) * 2 ^ H := by
        have hmul : (b' + 1 + 1) * 2 ^ H = b' * 2 ^ H + 2 ^ H + 2 ^ H := by ring
        omega
      omega
  subst hb1
  have hCB : C = B := by omega
  subst hCB
  refine ⟨d, hCd, wordEffect_append hE ?_⟩
  exact @WordEffect.d11 0 [] 1 [] (WordEffect.nil 1)
def copyDefect (u v : WordList) : Rat := 3 * wordMass u + wordMassQ u - wordMassQ v
theorem copy_defect_bound {n k : Nat} {u v : WordList} {b k' : Nat} (hI : Copy n k u v b k') :
    copyDefect u v - (((1 + b : Nat) : Rat) * wordScale u - ((1 + n : Nat) : Rat)) =
      2 * wordMass u /\
    0 <= ((1 + b : Nat) : Rat) * wordScale u - ((1 + n : Nat) : Rat) /\
    ((1 + b : Nat) : Rat) * wordScale u - ((1 + n : Nat) : Rat) <= 2 * wordMass u := by
  have hE := wordEffect_of_copy hI
  have hBud := wordEffect_budget_eq hE
  have hBnd := wordEffect_excess_bounds hE
  unfold copyDefect
  push_cast at hBud hBnd ⊢
  refine ⟨by linarith, by linarith, by linarith⟩
theorem copy_split_effect {n k : Nat} {u v : WordList} {b k' : Nat} (hC : Copy n k u v b k') :
    ∀ (w : WordList) (c : Nat) (x : WordList),
      WordEffect n (u ++ w) c x -> ∃ y, x = v ++ y /\ WordEffect b w c y := by
  induction hC with
  | nil _ _ => intro w c x hE; exact ⟨x, rfl, hE⟩
  | T _ ih =>
    intro w c x hE
    cases hE with
    | T hSub =>
      rcases ih w c _ hSub with ⟨y, rfl, hY⟩
      exact ⟨y, rfl, hY⟩
  | @d00 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : n0 * 2 = m at hE
    cases hE with
    | @d00 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y, rfl, hY⟩
      exact ⟨y, rfl, hY⟩
    | d01 _ => omega
  | @d01 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : 1 + n0 * 2 = m at hE
    cases hE with
    | d00 _ => omega
    | @d01 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y, rfl, hY⟩
      exact ⟨y, rfl, hY⟩
  | @d10 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : n0 * 2 = m at hE
    cases hE with
    | @d10 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y, rfl, hY⟩
      exact ⟨y, rfl, hY⟩
    | d11 _ => omega
  | @d11 n0 k0 u0 v0 b0 k0' _ ih =>
    intro w c x hE
    generalize hm : 1 + n0 * 2 = m at hE
    cases hE with
    | d10 _ => omega
    | @d11 n1 _ _ _ hSub =>
      have hn : n0 = n1 := by omega
      subst hn
      rcases ih w c _ hSub with ⟨y, rfl, hY⟩
      exact ⟨y, rfl, hY⟩
def isSafePrefix : WordList -> Bool
  | [] => true
  | Q :: V :: v => isSafePrefix (V :: v)
  | Q :: _ => false
  | _ :: v => isSafePrefix v
theorem isSafePrefix_replicate_V_append (q : Nat) (v : WordList) (h : isSafePrefix v = true) :
    isSafePrefix (List.replicate q V ++ v) = true := by
  induction q with
  | zero => exact h
  | succ q ih => rw [List.replicate_succ, List.cons_append]; exact ih
theorem copy_phaseScan_split {n k : Nat} {u v : WordList} {b k' : Nat} (hC : Copy n k u v b k') :
    isSafePrefix v = true ->
    ∀ (w : WordList) (k'' : Nat) (x : WordList) (a c : Rat),
      PhaseScan k (v ++ w) k'' x a c ->
      ∃ y a' c', x = u ++ y /\ PhaseScan k' w k'' y a' c' /\
        a = copyDefect u v + wordScale u * a' /\ c = wordScale u * c' := by
  induction hC with
  | nil _ _ =>
    intro _ w k'' x a c hI
    exact ⟨x, a, c, rfl, hI,
      by unfold copyDefect; simp [wordMass, wordMassQ, wordScale], by simp [wordScale]⟩
  | @T n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : isSafePrefix v0 = true := hSafe
    generalize hm : 3 + k0 = m at hI
    cases hI with
    | @T m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y, a', c', rfl, hY, hA, hC'⟩
      refine ⟨y, a', c', rfl, hY, ?_, ?_⟩
      · unfold copyDefect at hA ⊢; dsimp [wordMass, wordMassQ, wordScale]; linarith
      · dsimp [wordScale]; linarith
  | @d00 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : isSafePrefix v0 = true := hSafe
    generalize hm : 2 + k0 * 4 = m at hI
    cases hI with
    | @short00 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y, a', c', rfl, hY, hA, hC'⟩
      refine ⟨y, a', c', rfl, hY, ?_, ?_⟩
      · unfold copyDefect at hA ⊢; dsimp [wordMass, wordMassQ, wordScale]; linarith
      · dsimp [wordScale]; linarith
    | short10 _ => omega
  | @d01 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : isSafePrefix v0 = true := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact hSafe | contradiction
    have hv0 : ∃ zs, v0 = V :: zs := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact ⟨zs, rfl⟩ | contradiction
    rcases hv0 with ⟨zs, rfl⟩
    simp only [List.cons_append] at hI
    generalize hm : 2 + k0 * 4 = m at hI
    cases hI with
    | @short01 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y, a', c', rfl, hY, hA, hC'⟩
      refine ⟨y, a', c', rfl, hY, ?_, ?_⟩
      · unfold copyDefect at hA ⊢; dsimp [wordMass, wordMassQ, wordScale] at hA ⊢; linarith
      · dsimp [wordScale]; linarith
    | short11 _ => omega
  | @d10 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : isSafePrefix v0 = true := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact hSafe | contradiction
    have hv0 : ∃ zs, v0 = V :: zs := by
      cases v0 with
      | nil => contradiction
      | cons z zs => cases z <;> first | exact ⟨zs, rfl⟩ | contradiction
    rcases hv0 with ⟨zs, rfl⟩
    simp only [List.cons_append] at hI
    generalize hm : 4 + k0 * 4 = m at hI
    cases hI with
    | short01 _ => omega
    | @short11 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y, a', c', rfl, hY, hA, hC'⟩
      refine ⟨y, a', c', rfl, hY, ?_, ?_⟩
      · unfold copyDefect at hA ⊢; dsimp [wordMass, wordMassQ, wordScale] at hA ⊢; linarith
      · dsimp [wordScale]; linarith
  | @d11 n0 k0 u0 v0 b0 k0' _ ih =>
    intro hSafe w k'' x a c hI
    have hSafe' : isSafePrefix v0 = true := hSafe
    generalize hm : 4 + k0 * 4 = m at hI
    cases hI with
    | short00 _ => omega
    | @short10 m0 _ _ _ _ _ hSub =>
      have hk0 : k0 = m0 := by omega
      subst hk0
      rcases ih hSafe' w k'' _ _ _ hSub with ⟨y, a', c', rfl, hY, hA, hC'⟩
      refine ⟨y, a', c', rfl, hY, ?_, ?_⟩
      · unfold copyDefect at hA ⊢; dsimp [wordMass, wordMassQ, wordScale]; linarith
      · dsimp [wordScale]; linarith
set_option maxHeartbeats 2000000 in
-- Justification: Nonlinear rational arithmetic (`nlinarith`) combining phase-scan and copy-defect bounds.
theorem copy_phaseScan_digitVal_bound (pre pe : WordList) (carry budget : Nat) (u ds : WordList)
    (A H k : Nat) (v : WordList) (a b : Rat) (s : Nat) (e f : Rat)
    (hC : Copy 0 12 pre pe carry budget) (hSafe : isSafePrefix pe = true)
    (hI : PhaseScan 12 (pe ++ u ++ ds ++ [K]) k v a b)
    (hD : DigitVal A H ds) (hCut : notEndsWithQ u = true)
    (hLow : ∃ c w, (0 < c /\ s <= c) /\ ds = List.replicate c Q ++ K :: w)
    (hErr : e = wordScale pre * wordMass u)
    (hBound : (wordScale pre * wordScale u) * (((2 ^ (s + s / 2) : Nat) : Rat) +
      2 * wordMassK ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat)) :
    ∃ w, v = pre ++ w /\
      wordMass (V :: (v ++ [V])) <= wordMass pre * (1 / 2) + (e + f) * (1 / 2) /\
      copyDefect pre pe - e * (1 / 4) - 3 * f <= a - b /\
      a - b <= copyDefect pre pe + 4 * e + 4 * f := by
  have hEq : pe ++ u ++ ds ++ [K] = pe ++ (u ++ (ds ++ [K])) := by simp [List.append_assoc]
  rw [hEq] at hI
  rcases copy_phaseScan_split hC hSafe (u ++ (ds ++ [K])) k v a b hI with ⟨w, c, d, rfl, hJ, hPos,
    hNeg⟩
  rcases phaseScan_split_of_splitCond hJ u (ds ++ [K]) rfl (Or.inl hCut)
    with ⟨m, x, y, a1, b1, a2, b2, hK, hL, rfl, hP, hN⟩
  have hBK := phaseScan_loss_bounds hK
  have hBL := phaseScan_loss_bounds hL
  have hSK := phaseScan_scale_le hK
  have hSpre := wordScale_pos pre
  have hSu := wordScale_pos u
  have hSx := wordScale_pos x
  have hWds := wordMass_nonneg ds
  have hPow := rat_pow_two_pos (s + s / 2)
  have hSpx : 0 <= wordScale pre * wordScale x := mul_nonneg (le_of_lt hSpre) (le_of_lt hSx)
  have hSx_le : wordScale pre * wordScale x <= wordScale pre * wordScale u := by nlinarith
  have hZ_pos : 0 <= ((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds := by linarith
  have hF : (wordScale pre * wordScale x) * (((2 ^ (s + s / 2) : Nat) : Rat) + 2 * wordMassK ds) <=
      f * ((2 ^ (s + s / 2) : Nat) : Rat) := by
    nlinarith
  rcases phaseScan_digitVal_weighted_bound s ds A H m k y a2 b2 (wordScale pre * wordScale x) f hD
    hL hLow
    hSpx hF with ⟨hMt, hPt, hNt⟩
  have hMt' : wordScale pre * (wordScale x * wordMass y) <= f := by linarith
  have hPt' : wordScale pre * (wordScale x * a2) <= 4 * f := by linarith
  have hNt' : wordScale pre * (wordScale x * b2) <= 3 * f := by linarith
  have hPa : 0 <= wordScale pre * (wordScale x * a2) := by
    have := mul_nonneg hSpx hBL.2.1; linarith
  have hPb : 0 <= wordScale pre * (wordScale x * b2) := by
    have := mul_nonneg hSpx hBL.2.2.2.1; linarith
  have hMx : wordScale pre * wordMass x <= e := by nlinarith
  have hA1_0 : 0 <= wordScale pre * a1 := by nlinarith
  have hA1 : wordScale pre * a1 <= 4 * e := by nlinarith
  have hB1_0 : 0 <= wordScale pre * b1 := by nlinarith
  have hB1 : wordScale pre * b1 <= e * (1 / 4) := by nlinarith
  refine ⟨x ++ y, by simp, ?_, ?_, ?_⟩
  · dsimp [wordMass]
    rw [wordMass_append, wordMass_append, wordMass_append]
    dsimp [wordMass, wordScale]
    linarith
  · rw [hP] at hPos; rw [hN] at hNeg
    linarith
  · rw [hP] at hPos; rw [hN] at hNeg
    linarith
theorem copy_effect_phaseScan_combine (pre pe : WordList) (b k : Nat) (u : WordList) (carry : Nat)
    (eff : WordList)
    (hC : Copy 0 12 pre pe b k) (hE : WordEffect 0 (pre ++ u) carry eff) :
    copyDefect pre pe - 2 * wordMass pre <= ((1 + carry : Nat) : Rat) * wordScale (pre ++ u) - 1 /\
    ((1 + carry : Nat) : Rat) * wordScale (pre ++
      u) - 1 <= copyDefect pre pe - 2 * wordMass pre + 2 * wordScale pre * wordMass u := by
  rcases copy_split_effect hC u carry eff hE with ⟨v, _, hV⟩
  have hBnd := wordEffect_excess_bounds hV
  have hSpre := wordScale_pos pre
  have hLed := (copy_defect_bound hC).1
  rw [wordScale_append]
  push_cast at hBnd hLed ⊢
  constructor <;> nlinarith
def CopyTwelve (u v : WordList) : Prop := ∃ b k, Copy 0 12 u v b k
inductive Step : WordList -> WordList -> Prop where
  | intro (orig eff : WordList) (k : Nat) (v : WordList) (a b : Rat) (J A : Nat) (da : WordList) :
      WordEffect 0 orig 1 eff -> PhaseScan 12 eff k v a b ->
      DigitVal A J da -> A + 2 ^ J = k ->
      Step orig (V :: (v ++ V :: (da ++ [Q])))
inductive AggState (av : WordList) : Nat -> Nat -> WordList -> Prop where
  | intro (p q H : Nat) (u : WordList) (A : Nat) (da : WordList)
      (carry : Nat) (eff : WordList) (B : Nat) (db : WordList) (tau alpha : Rat) :
      16 <= p -> 5 <= q -> (3 * p) / 2 + 5 <= H ->
      (∃ rest, u = (List.replicate q V ++ av) ++ rest) ->
      (∃ rest, u = rest ++ [V]) ->
      wordMass (List.replicate q V ++ av) = alpha ->
      1 / 2 <= alpha * ((2 ^ p : Nat) : Rat) ->
      alpha * ((2 ^ p : Nat) : Rat) <= 1 ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 1 ->
      DigitVal A H da ->
      WordEffect 0 u carry eff ->
      A + carry = B + 2 ^ H ->
      DigitVal B H db ->
      Reserve p tau ->
      wordMass u <= alpha * (1 + (3 / 64) - tau) ->
      (3 / 2) * alpha <= wordScale u * wordMassK db ->
      wordScale u * wordMassK db <= (5 / 2) * alpha ->
      (∃ rest, db = List.replicate ((p - 2) / 2) Q ++ rest) ->
      AggState av p q (u ++ da ++ [Q])
theorem replicate_one_add_cons (q : Nat) (w : Word) :
    List.replicate (1 + q) w = w :: List.replicate q w := by
  rw [Nat.add_comm 1 q, List.replicate_succ]
set_option maxHeartbeats 4000000 in
-- Justification: Large multi-hypothesis rational arithmetic step combining CopyTwelve, PhaseScan, and Reserve bounds.
theorem aggState_step_of_copyTwelve (av ev : WordList) (hSafe : isSafePrefix ev = true)
    (hStable : ∀ q, 5 <= q -> CopyTwelve (List.replicate q V ++ av) (List.replicate q V ++ ev)) :
    ∀ (p q : Nat) (orig : WordList), AggState av p q orig ->
      ∃ out, Step orig out /\ AggState av (1 + p) (1 + q) out := by
  intro p q orig hG
  rcases hG with ⟨H, u, A, da, carry, eff, B, db, tau, alpha,
    hP, hQ, hHbound, ⟨rest, hStart⟩, hEnd, hMass, hApLow, hApHigh, hHeight,
    hDA, hEff, hSum, hDB, hRes, hM, hDlo, hDhi, hLow⟩
  set pre := List.replicate q V ++ av
  set pe := List.replicate q V ++ ev
  set unit := wordScale u
  have hPowP := rat_pow_two_pos p
  have hAlpha : 0 < alpha := by nlinarith
  have hUnit : 0 < unit := wordScale_pos u
  set dyadic := wordScale (List.replicate p V)
  have hDP : dyadic * ((2 ^ p : Nat) : Rat) = 1 := (wordMass_and_scale_replicate_V p).2
  have hDyadic : 0 < dyadic := wordScale_pos (List.replicate p V)
  have hAupper : alpha <= dyadic := by nlinarith
  have hAsmall : dyadic <= 1 / 65536 := wordScale_replicate_V_le_inv_65536 p hP
  rcases reserve_pos_and_le hRes hP with ⟨hTau, hTauSmall⟩
  have hUsmall : unit <= alpha * (1 / 1024) :=
    unit_le_alpha_div_1024 p H alpha unit (by omega) hAlpha hUnit hApLow hHeight
  rcases hStable q hQ with ⟨bc, kc, hCopyPre⟩
  have hSafePre : isSafePrefix pe = true := isSafePrefix_replicate_V_append q ev hSafe
  rcases copy_defect_bound hCopyPre with ⟨hLedger, hRhoLow, hRhoHigh⟩
  set rho := copyDefect pre pe - 2 * alpha
  have hRho : 0 <= rho /\ rho <= 2 * alpha := by
    unfold rho; rw [<- hMass]; push_cast at hLedger hRhoLow hRhoHigh; constructor <;> linarith
  rcases wordEffect_preserves_scale_and_mass hEff with ⟨hEffScale, hEffMass⟩
  rcases wordEffect_preserves_ends_with_V hEff hEnd with ⟨last_w, hElast⟩
  have hCut : notEndsWithQ eff = true := by rw [hElast, notEndsWithQ_append_singleton]; rfl
  have hNe : eff ≠ [] := by rw [hElast]; simp
  have hEffHeight : wordScale eff * ((2 ^ H : Nat) : Rat) = 1 := by rw [hEffScale]; exact hHeight
  have hEffBound : wordMass eff + wordScale eff * (1 + wordMassK db) <= 1 / 128 := by
    rw [hEffScale]; nlinarith
  rcases exists_phaseScan_twelve eff B H db hDB hEffHeight hCut hNe hEffBound with ⟨k, v, a, b,
    hIscan, hK⟩
  have hZ : 0 < wordMassK db := by nlinarith
  rcases digitVal_massK_scale_bound p H B db dyadic unit hDB (by omega) (by omega)
    hDyadic hUnit (by linarith) hDP hHeight (by nlinarith) with ⟨hi, hHi⟩
  rcases digitVal_sandwich_split ((p - 2) / 2) (p - 2) hDB hZ hLow ⟨hi, hHi⟩
    with ⟨c, mid, t0, hSplit, hMidCut, hC, hT⟩
  rcases phaseScan_digitVal_length_bound eff db B H 12 k v a b p c mid t0 hDB hEffHeight hIscan
    hCut hMidCut hSplit hP hC hT with ⟨J, hJbound, hJheight⟩
  set new_u := V :: (v ++ [V])
  set nu := wordScale new_u
  have hNu : 0 < nu := wordScale_pos new_u
  have hNuSmall : nu <= alpha * (1 / 1024) :=
    unit_le_alpha_div_1024 p J alpha nu (by omega) hAlpha hNu hApLow hJheight
  have hEffRest : ∃ w, eff = pe ++ w /\ WordEffect bc rest carry w := by
    rw [hStart] at hEff
    exact copy_split_effect hCopyPre rest carry eff hEff
  rcases hEffRest with ⟨w, hEstart, hEw⟩
  rcases wordEffect_preserves_scale_and_mass hEw with ⟨hWscale, hWmass⟩
  have hWcut : notEndsWithQ w = true := by
    rw [hEstart] at hCut; exact notEndsWithQ_of_append_left pe w hCut
  set e := wordMass u - alpha
  have hEeq : e = wordScale pre * wordMass w := by
    unfold e; rw [hStart, wordMass_append, <- hWmass, hMass]; ring
  have hWw := wordMass_nonneg w
  have hSpre := wordScale_pos pre
  have hEpos : 0 <= e := by nlinarith
  have hEbound : e <= alpha * ((3 / 64) - tau) := by unfold e; linarith
  set s := (p - 2) / 2
  set pow := ((2 ^ (s + s / 2) : Nat) : Rat)
  have hPow : 0 < pow := rat_pow_two_pos (s + s / 2)
  set f := unit + 2 * unit * wordMassK db / pow
  have hFeq : f * pow = unit * pow + 2 * unit * wordMassK db := by
    unfold f; have hne : pow ≠ 0 := ne_of_gt hPow
    calc (unit + 2 * unit * wordMassK db / pow) * pow
      _ = unit * pow + (2 * unit * wordMassK db / pow) * pow := by ring
      _ = unit * pow + 2 * unit * wordMassK db := by rw [div_mul_cancel₀ _ hne]
  have hFpos : 0 <= f := by
    have h1 : 0 <= f * pow := by rw [hFeq]; nlinarith
    nlinarith
  have hFbound : f <= alpha * tau * (1 / 4) :=
    reserve_height_bound p H s alpha unit tau f hRes hP hHbound rfl hAlpha hUnit hApLow hHeight (by
      nlinarith)
  have hLow' : ∃ c0 w0, (0 < c0 /\ s <= c0) /\ db = List.replicate c0 Q ++ K :: w0 :=
    ⟨c, mid ++ List.replicate t0 Q, ⟨by omega, hC⟩, hSplit⟩
  have hFactor : wordScale pre * wordScale w = unit := by
    unfold unit; rw [hWscale, hStart, <- wordScale_append]
  have hScanStart : PhaseScan 12 (pe ++ w ++ db ++ [K]) k v a b := by
    rw [hEstart] at hIscan; simpa [List.append_assoc] using hIscan
  rcases copy_phaseScan_digitVal_bound pre pe bc kc w db B H k v a b s e f hCopyPre hSafePre
    hScanStart hDB hWcut hLow' hEeq (by rw [hFactor]; nlinarith)
    with ⟨tail, hVstart, hMnext, hDl, hDu⟩
  change wordMass new_u <= wordMass pre * (1 / 2) + (e + f) * (1 / 2) at hMnext
  rw [hMass] at hMnext
  have hDl' : 2 * alpha + rho - e * (1 / 4) - 3 * f <= a - b := by unfold rho; linarith
  have hDu' : a - b <= 2 * alpha + rho + 4 * e + 4 * f := by unfold rho; linarith
  rcases exists_wordEffect new_u 0 with ⟨carry', eff', hEff'⟩
  have hNewStart : new_u = (V :: pre) ++ (tail ++ [V]) := by
    unfold new_u; rw [hVstart]; simp [List.append_assoc]
  have hPre_step : List.replicate (1 + q) V ++ av = V :: pre := by
    unfold pre; rw [replicate_one_add_cons, List.cons_append]
  have hPe_step : List.replicate (1 + q) V ++ ev = V :: pe := by
    unfold pe; rw [replicate_one_add_cons, List.cons_append]
  rcases hStable (1 + q) (by omega) with ⟨bc', kc', hCopyNew⟩
  rw [hPre_step, hPe_step] at hCopyNew
  have hEff'_rw : WordEffect 0 ((V :: pre) ++ (tail ++ [V])) carry' eff' := by
    rwa [<- hNewStart]
  have hRbounds :=
    copy_effect_phaseScan_combine (V :: pre) (V :: pe) bc' kc' (tail ++
    [V]) carry' eff' hCopyNew hEff'_rw
  rw [<- hNewStart] at hRbounds
  have hNewMass : wordMass new_u =
    alpha * (1 / 2) + (wordScale pre * (1 / 2)) * wordMass (tail ++ [V]) := by
    rw [hNewStart, wordMass_append]; dsimp [wordMass, wordScale]; rw [hMass]
  have hCloss_step : copyDefect (V :: pre) (V :: pe) - 2 * wordMass (V :: pre) = rho * (1 / 2) := by
    unfold rho copyDefect; dsimp [wordMass, wordMassQ, wordScale]; rw [hMass]; ring
  have hScale_step : wordScale (V :: pre) * wordMass (tail ++
    [V]) = wordMass new_u - alpha * (1 / 2) := by
    dsimp [wordScale]; linarith
  set R := ((1 + carry' : Nat) : Rat) * nu - 1
  have hRb : rho * (1 / 2) <= R /\ R <= rho * (1 / 2) + 2 * (wordMass new_u - alpha * (1 / 2)) := by
    unfold R nu; constructor <;> linarith
  have hWtail := wordMass_nonneg (tail ++ [V])
  have hEnew : 0 <= wordMass new_u - alpha * (1 / 2) := by nlinarith
  have hFtiny : f <= alpha * (1 / 128) := by nlinarith
  have hEtiny : e <= alpha * (3 / 64) := by nlinarith
  have hBudget := phaseScan_twelve_scale_eq (eff ++ db ++ [K]) k v a b hIscan
  rcases carry_budget_contraction_ineq J k carry' alpha nu (a - b) R rho
    hAlpha (by linarith) hNu hNuSmall hJheight hRho.1 hRho.2
    (by linarith) (by linarith) hRb.1 (by linarith) hBudget (by unfold R; ring)
    with ⟨A', B', hAsum, hBsum, hAl, hAu, hBl, hBu⟩
  rcases exists_digitVal_of_lt_pow J A' hAu with ⟨da', hDA'⟩
  rcases exists_digitVal_of_lt_pow J B' hBu with ⟨db', hDB'⟩
  rcases reserve_step_contract hRes with ⟨tau', hRes', hTauStep⟩
  have hMkeep := reserve_next_step_bound alpha tau tau' e f (wordMass new_u - alpha * (1 / 2))
    (by linarith) hTauStep hEbound hFbound (by linarith)
  have hDkeep :=
    step_mass_contraction_ineq alpha e f nu (a - b) R (wordMass new_u - alpha * (1 / 2)) rho
    hAlpha hEpos hFpos (by linarith) hEtiny hFtiny hNuSmall hEnew (by linarith)
    hRb.1 hRb.2 hDl' hDu'
  have hDef := phaseScan_twelve_height_sum (eff ++ db ++
    [K]) k v a b J A' B' carry' hIscan hJheight hAsum hBsum
  have hZnew := digitVal_wordMassK_eq hDB'
  have hDnew : nu * wordMassK db' = (a - b) * (1 / 2) - 4 * nu - R := by
    have hZ' : nu * wordMassK db' = 1 - ((1 + B' : Nat) : Rat) * nu := by
      calc nu * wordMassK db'
        _ = nu * ((wordMassK db' + (B' : Rat) + 1) - (1 + (B' : Rat))) := by ring
        _ = nu * (((2 ^ J : Nat) : Rat) - (1 + (B' : Rat))) := by rw [hZnew]
        _ = nu * ((2 ^ J : Nat) : Rat) - (1 + (B' : Rat)) * nu := by ring
        _ = 1 - (1 + (B' : Rat)) * nu := by rw [hJheight]
        _ = 1 - ((1 + B' : Nat) : Rat) * nu := by push_cast; ring
    rw [hZ']
    exact hDef
  have hLowNew : ∃ rest, db' = List.replicate (((1 + p) - 2) / 2) Q ++ rest := by
    set r := (((1 + p) - 2) / 2) - 1
    have hHr : 1 + r = ((1 + p) - 2) / 2 /\ 1 + r * 2 <= p - 2 := by omega
    have hHighEnd : ∃ z, db = z ++ List.replicate (1 + r * 2) Q := by
      refine ⟨hi ++ List.replicate ((p - 2) - (1 + r * 2)) Q, ?_⟩
      have heq : ((p - 2) - (1 + r * 2)) + (1 + r * 2) = p - 2 := by omega
      rw [List.append_assoc, <- List.replicate_add, heq, <- hHi]
    rcases hHighEnd with ⟨z, hHZ⟩
    have hSC : PhaseScan 12 ((eff ++ z) ++ List.replicate (1 + r * 2) Q ++ [K]) k v a b := by
      rw [hHZ] at hIscan; simpa [List.append_assoc] using hIscan
    rcases phaseScan_effect_split r 12 (eff ++ z) k v a b carry' eff' A' B' J db'
      hSC hEff' hDB' (by omega) hAsum hBsum with ⟨z', hL⟩
    rw [hHr.1] at hL
    exact ⟨z', hL⟩
  have hAp_step : (alpha * (1 / 2)) * ((2 ^ (1 + p) : Nat) : Rat) =
    alpha * ((2 ^ p : Nat) : Rat) := by
    rw [pow_two_one_add, Nat.cast_add]; ring
  refine ⟨new_u ++ da' ++ [Q], ?_, ?_⟩
  · have hOut_eq : new_u ++ da' ++ [Q] = V :: (v ++ V :: (da' ++ [Q])) := by
      unfold new_u; simp [List.append_assoc]
    rw [hOut_eq]
    have hOrig_eq : (u ++ da ++ [Q]) = u ++ (da ++ [Q]) := by simp [List.append_assoc]
    rw [hOrig_eq]
    rcases exists_wordEffect_carry_one hDA hSum (lt_pow_of_digitVal hDB) with ⟨d, hDD, hEE⟩
    have hd_eq : d = db := digitVal_unique hDD hDB
    rw [hd_eq] at hEE
    have hEffFull : WordEffect 0 (u ++ (da ++ [Q])) 1 (eff ++ db ++ [K]) := by
      simpa [List.append_assoc] using wordEffect_append hEff hEE
    exact Step.intro (u ++ (da ++ [Q])) (eff ++ db ++ [K]) k v a b J A' da'
      hEffFull hIscan hDA' hAsum
  · refine AggState.intro (1 + p) (1 + q) J new_u A' da' carry' eff' B' db' tau' (alpha * (1 / 2))
      (by omega) (by omega) (by omega)
      ⟨tail ++ [V], by rw [hPre_step]; exact hNewStart⟩ ⟨V :: v, rfl⟩
      (by rw [hPre_step]; dsimp [wordMass]; rw [hMass])
      (by rw [hAp_step]; exact hApLow)
      (by rw [hAp_step]; exact hApHigh)
      hJheight hDA' hEff' (by omega) hDB' hRes'
      (by linarith) (by rw [hDnew]; linarith) (by rw [hDnew]; linarith) hLowNew
theorem copy_step_T {n k n' k' m b k'' : Nat} {u v : WordList}
    (hn : n' = 1 + n * 2) (hk : k = 3 + m) (hk' : k' = 2 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (V :: u) (V :: v) b k'' := by
  subst hn hk hk'; exact Copy.T h
theorem copy_step_d00 {n k n' k' m b k'' : Nat} {u v : WordList}
    (hn : n = n' * 2) (hk : k = 2 + m * 4) (hk' : k' = m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (K :: u) (K :: v) b k'' := by
  subst hn hk hk'; exact Copy.d00 h
theorem copy_step_d01 {n k n' k' m b k'' : Nat} {u v : WordList}
    (hn : n = 1 + n' * 2) (hk : k = 2 + m * 4) (hk' : k' = 1 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (K :: u) (Q :: v) b k'' := by
  subst hn hk hk'; exact Copy.d01 h
theorem copy_step_d10 {n k n' k' m b k'' : Nat} {u v : WordList}
    (hn : n = n' * 2) (hk : k = 4 + m * 4) (hk' : k' = 1 + m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (Q :: u) (Q :: v) b k'' := by
  subst hn hk hk'; exact Copy.d10 h
theorem copy_step_d11 {n k n' k' m b k'' : Nat} {u v : WordList}
    (hn : n = 1 + (n' - 1) * 2) (hn' : n' = 1 + (n' - 1)) (hk : k = 4 + m * 4) (hk' : k' = m * 2)
    (h : Copy n' k' u v b k'') : Copy n k (Q :: u) (K :: v) b k'' := by
  rw [hn, hk]; rw [hn', hk'] at h; exact Copy.d11 h
def decodeDigits : Nat -> Nat -> Option (WordList)
  | 0, _ => none
  | fuel + 1, k =>
    if k == 0 then none
    else if k == 1 then some []
    else
      match decodeDigits fuel (k / 2) with
      | none => none
      | some da => some ((if k % 2 == 0 then K else Q) :: da)
theorem decodeDigits_sound (fuel : Nat) :
    ∀ (k : Nat) (da : WordList),
      decodeDigits fuel k = some da ->
      ∃ A J, DigitVal A J da /\ A + 2 ^ J = k := by
  induction fuel with
  | zero => intro k da h; contradiction
  | succ fuel ih =>
    intro k da h
    dsimp [decodeDigits] at h
    cases hk0 : (k == 0) with
    | true => rw [hk0] at h; contradiction
    | false =>
      rw [hk0] at h
      cases hk1 : (k == 1) with
      | true =>
        rw [hk1] at h
        simp only [beq_iff_eq] at hk1; subst hk1
        injection h with h; subst h
        exact ⟨0, 0, DigitVal.nil, rfl⟩
      | false =>
        rw [hk1] at h
        have hk2 : 2 <= k := by
          simp only [beq_eq_false_iff_ne] at hk0 hk1
          omega
        cases hrec : decodeDigits fuel (k / 2) with
        | none => rw [hrec] at h; contradiction
        | some da' =>
          rw [hrec] at h
          injection h with h; subst h
          rcases ih (k / 2) da' hrec with ⟨A, J, hD, hSum⟩
          rcases Nat.mod_two_eq_zero_or_one k with hmod | hmod
          · have hc : (k % 2 == 0) = true := beq_iff_eq.mpr hmod
            rw [hc]
            refine ⟨A * 2, 1 + J, DigitVal.zero hD, ?_⟩
            rw [pow_two_one_add]; omega
          · have hc : (k % 2 == 0) = false := beq_false_of_ne (by omega)
            rw [hc]
            refine ⟨1 + A * 2, 1 + J, DigitVal.one hD, ?_⟩
            rw [pow_two_one_add]; omega
def evalStep (orig : WordList) : Option (WordList) :=
  let (carry, eff) := evalEffect 0 orig
  if carry == 1 then
    match evalPhaseScan 1024 eff 12 with
    | some (k, v) =>
      match decodeDigits 512 k with
      | some da => withNatWordList (V :: (v ++ V :: (da ++ [Q]))) (fun out => some out)
      | none => none
    | none => none
  else none
theorem evalStep_sound (orig out : WordList) (hR : evalStep orig = some out) :
    Step orig out := by
  unfold evalStep at hR
  have hE := evalEffect_sound orig 0
  generalize hEff : evalEffect 0 orig = ce at hR hE
  rcases ce with ⟨carry, eff⟩
  dsimp only at hR hE
  split_ifs at hR with hc1
  simp only [beq_iff_eq] at hc1; subst hc1
  cases hScan : evalPhaseScan 1024 eff 12 with
  | none => rw [hScan] at hR; contradiction
  | some kv =>
    rw [hScan] at hR
    rcases kv with ⟨k, v⟩
    dsimp only at hR
    cases hPw : decodeDigits 512 k with
    | none => rw [hPw] at hR; contradiction
    | some da =>
      rw [hPw] at hR
      simp only [withNatWordList_eq] at hR
      injection hR with hR; subst hR
      rcases evalPhaseScan_sound 1024 eff 12 k v hScan with ⟨a, b, hI⟩
      rcases decodeDigits_sound 512 k da hPw with ⟨A, J, hDA, hSum⟩
      exact Step.intro orig eff k v a b J A da hE hI hDA hSum
inductive Rounds : WordList -> WordList -> Prop where
  | refl (u : WordList) : Rounds u u
  | next {u v w : WordList} : Step u v -> Rounds v w -> Rounds u w
theorem rounds_trans {u v w : WordList} (h1 : Rounds u v) (h2 : Rounds v w) : Rounds u w := by
  induction h1 with
  | refl _ => exact h2
  | next hS _ ih => exact Rounds.next hS (ih h2)
def evalRounds : Nat -> WordList -> Option (WordList)
  | 0, u => some u
  | n + 1, u =>
    match evalStep u with
    | none => none
    | some v => evalRounds n v
theorem evalRounds_sound (n : Nat) :
    ∀ (u w : WordList), evalRounds n u = some w -> Rounds u w := by
  induction n with
  | zero =>
    intro u w h; injection h with h; subst h; exact Rounds.refl u
  | succ n ih =>
    intro u w h
    dsimp [evalRounds] at h
    cases hV : evalStep u with
    | none => rw [hV] at h; contradiction
    | some v =>
      rw [hV] at h
      exact Rounds.next (evalStep_sound u v hV) (ih v w h)
theorem good_of_aggState_entry {B H : Nat} {db : WordList} (u high : WordList) (alpha : Rat)
    (hD : DigitVal B H db)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1)
    (hHi : ∃ lo, db = lo ++ high)
    (hL : (3 / 2) * alpha * wordScale high <= wordMassK high)
    (hR : wordMassK high + 1 <= (5 / 2) * alpha * wordScale high) :
    (3 / 2) * alpha <= wordScale u * wordMassK db /\
      wordScale u * wordMassK db <= (5 / 2) * alpha := by
  rcases hHi with ⟨lo, rfl⟩
  have hDig := all_isDigitWord_of_digitVal hD
  rw [List.all_append, Bool.and_eq_true] at hDig
  rcases exists_digitVal_of_all_isDigitWord lo hDig.1 with ⟨A, hDA⟩
  rcases digitVal_scale_and_mass hDA with ⟨hLs, hLm, hLo⟩
  rcases digitVal_scale_and_mass hD with ⟨hDs, _, _⟩
  have hSplit := wordMass_eq_add lo
  have hWlo := wordMass_nonneg lo
  have hSu := wordScale_pos u
  have hSlo := wordScale_pos lo
  have hShigh := wordScale_pos high
  rw [wordScale_append] at hDs
  set x := wordScale u * wordScale lo
  have hX : x * wordScale high = 1 := by unfold x; nlinarith
  have hXP : 0 < x := by unfold x; nlinarith
  have hXL : (3 / 2) * alpha <= x * wordMassK high := by nlinarith
  have hXR : x * (wordMassK high + 1) <= (5 / 2) * alpha := by nlinarith
  rw [wordMassK_append]
  unfold x at *
  constructor <;> nlinarith

end BusyBeaver.WordCalculus
