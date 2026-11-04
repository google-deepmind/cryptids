/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
import BusyBeaver.Basic

/-!
# 2-Adic Laurent-Determinant Non-Halting Proof for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`

Self-contained, Baker-free non-halting proof for the Pomme / Baker machine
`1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` (following the resolution by mxdys, Pomme,
Autumn Pan, and vyx7). All internal algebraic and trajectory helper lemmas are module-private;
only `machine`, `target`, and `is_not_halt` are exported.
-/

namespace BusyBeaver.Pomme.NonHalt

open Mathlib Relation Nat Turing BusyBeaver

@[expose] public section

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

end

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

theorem dvd_add {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := Int.dvd_add h1 h2
theorem dvd_sub {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := Int.dvd_sub h1 h2
theorem abs_mul (a b : Int) : |a * b| = |a| * |b| := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_neg hb, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt
    hb))]; ring
  · rw [abs_of_neg ha, abs_of_nonneg hb, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha)
    hb)]; ring
  · rw [abs_of_neg ha, abs_of_neg hb, abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha)
    (le_of_lt hb))]; ring
macro "positivity" : tactic =>
  `(tactic| first
    | omega
    | exact pow_pos (by omega) _
    | exact pow_nonneg (by omega) _
    | exact pow_nonneg (pow_nonneg (by omega) _) _
    | exact pow_nonneg (mul_nonneg (pow_nonneg (by omega) _) (pow_nonneg (by omega) _)) _
    | exact mul_pos (pow_pos (by omega) _) (pow_pos (by omega) _)
    | exact mul_pos (by omega) (pow_pos (by omega) _)
    | exact mul_nonneg (pow_nonneg (by omega) _) (pow_nonneg (by omega) _)
    | nlinarith)
namespace FiniteDiff
def fwdDiff : Nat -> (Nat -> Int) -> Nat -> Int
  | 0, f, x => f x
  | d + 1, f, x => fwdDiff d f (x + 1) - fwdDiff d f x
theorem fwdDiff_congr (d : Nat) (f g : Nat -> Int) (h : ∀ x, f x = g x) (x : Nat) :
    fwdDiff d f x = fwdDiff d g x := by
  induction d generalizing x with
  | zero => exact h x
  | succ d ih => simp [fwdDiff, ih]
theorem fwdDiff_add (d : Nat) (f g : Nat -> Int) (x : Nat) :
    fwdDiff d (fun x => f x + g x) x = fwdDiff d f x + fwdDiff d g x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [fwdDiff, ih]; ring
theorem fwdDiff_smul (d : Nat) (c : Int) (f : Nat -> Int) (x : Nat) :
    fwdDiff d (fun x => c * f x) x = c * fwdDiff d f x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [fwdDiff, ih]; ring
theorem fwdDiff_shift (d : Nat) (f : Nat -> Int) (x : Nat) :
    fwdDiff d (fun x => f (x + 1)) x = fwdDiff d f (x + 1) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [fwdDiff, ih]
theorem fwdDiff_mul_self (d : Nat) (f : Nat -> Int) (x : Nat) :
    fwdDiff (d + 1) (fun x => (x : Int) * f x) x =
      (x : Int) * fwdDiff (d + 1) f x + ((d + 1 : Nat) : Int) * fwdDiff d f (x + 1) := by
  induction d generalizing x with
  | zero =>
    simp only [fwdDiff, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring
  | succ d ih =>
    have h1 := ih (x + 1)
    have h2 := ih x
    have h3 : fwdDiff (d + 1 + 1) (fun x => (x : Int) * f x) x =
        fwdDiff (d + 1) (fun x => (x : Int) * f x) (x + 1) -
        fwdDiff (d + 1) (fun x => (x : Int) * f x) x := rfl
    have h4 : fwdDiff (d + 1 + 1) f x = fwdDiff (d + 1) f (x + 1) - fwdDiff (d + 1) f x := rfl
    have h5 : fwdDiff (d + 1) f (x + 1) = fwdDiff d f (x + 1 + 1) - fwdDiff d f (x + 1) := rfl
    rw [h3, h1, h2, h4, h5]
    push_cast
    ring
theorem fwdDiff_geom (d : Nat) (q : Int) (x : Nat) :
    fwdDiff d (fun x => q ^ x) x = (q - 1) ^ d * q ^ x := by
  induction d generalizing x with
  | zero => simp [fwdDiff]
  | succ d ih =>
    simp only [fwdDiff, ih, pow_succ]
    ring
theorem pow_dvd_pow_of_le (a b : Nat) (h : a ≤ b) : ((4 : Int) ^ a) ∣ ((4 : Int) ^ b) := by
  refine ⟨(4 : Int) ^ (b - a), ?_⟩
  rw [<- pow_add, Nat.add_sub_of_le h]
theorem four_pow_dvd_fwdDiff_monomial_geom (q : Int) (hq : (4 : Int) ∣ (q - 1)) (k d x : Nat) :
    ((4 : Int) ^ (d - k)) ∣ fwdDiff d (fun x => (x : Int) ^ k * q ^ x) x := by
  rcases hq with ⟨t, ht⟩
  induction k generalizing d x with
  | zero =>
    rw [Nat.sub_zero]
    have hext : (fun x : Nat => (x : Int) ^ 0 * q ^ x) = (fun x : Nat => q ^ x) := by
      funext y; ring
    rw [hext, fwdDiff_geom, ht, mul_pow]
    refine ⟨t ^ d * q ^ x, ?_⟩
    ring
  | succ k ih =>
    cases d with
    | zero =>
      simp [fwdDiff]
    | succ d =>
      have hext : (fun x : Nat => (x : Int) ^ (k + 1) * q ^ x) =
          (fun x : Nat => (x : Int) * ((x : Int) ^ k * q ^ x)) := by
        funext y; rw [pow_succ]; ring
      rw [hext, fwdDiff_mul_self, Nat.succ_sub_succ_eq_sub]
      apply dvd_add
      · apply dvd_mul_of_dvd_right
        exact dvd_trans (pow_dvd_pow_of_le (d - k) (d + 1 - k) (by omega)) (ih (d + 1) x)
      · apply dvd_mul_of_dvd_right
        exact ih d (x + 1)
def sum : Nat -> (Nat -> Int) -> Int
  | 0, _ => 0
  | n + 1, f => sum n f + f n
theorem sum_congr (n : Nat) (f g : Nat -> Int) (h : ∀ k, k < n -> f k = g k) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]
theorem sum_add (n : Nat) (f g : Nat -> Int) :
    sum n (fun k => f k + g k) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih]; ring
theorem sum_succ_shift (n : Nat) (f : Nat -> Int) :
    sum (n + 1) f = f 0 + sum n (fun k => f (k + 1)) := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    calc sum (n + 1 + 1) f = sum (n + 1) f + f (n + 1) := rfl
      _ = f 0 + sum n (fun k => f (k + 1)) + f (n + 1) := by rw [ih]
      _ = f 0 + sum (n + 1) (fun k => f (k + 1)) := by simp only [sum]; ring
def binomInt : Nat -> Nat -> Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, d + 1 => binomInt n d + binomInt n (d + 1)
theorem binomInt_eq_zero_of_lt (n d : Nat) (h : n < d) : binomInt n d = 0 := by
  induction n generalizing d with
  | zero =>
    cases d with
    | zero => omega
    | succ d => rfl
  | succ n ih =>
    cases d with
    | zero => omega
    | succ d =>
      simp only [binomInt]
      rw [ih d (by omega), ih (d + 1) (by omega)]
      ring
theorem binomInt_zero_right (n : Nat) : binomInt n 0 = 1 := by
  cases n <;> rfl
theorem sum_binomInt_succ (n : Nat) (f : Nat -> Int) :
    sum (n + 2) (fun k => binomInt (n + 1) k * f k) =
      sum (n + 1) (fun k => binomInt n k * f k) + sum (n + 1) (fun k => binomInt n k * f (k + 1)) :=
        by
  rw [sum_succ_shift (n + 1) (fun k => binomInt (n + 1) k * f k)]
  have hext : sum (n + 1) (fun k => binomInt (n + 1) (k + 1) * f (k + 1)) =
      sum (n + 1) (fun k => binomInt n k * f (k + 1) + binomInt n (k + 1) * f (k + 1)) := by
    apply sum_congr
    intro k _
    simp only [binomInt]
    ring
  rw [hext, sum_add]
  rw [sum_succ_shift n (fun k => binomInt n k * f k), binomInt_zero_right, binomInt_zero_right]
  have htail : sum (n + 1) (fun k => binomInt n (k + 1) * f (k + 1)) =
      sum n (fun k => binomInt n (k + 1) * f (k + 1)) + binomInt n (n + 1) * f (n + 1) := rfl
  rw [htail, binomInt_eq_zero_of_lt n (n + 1) (by omega)]
  ring
theorem newton_forward_diff (f : Nat -> Int) (n x : Nat) :
    f (x + n) = sum (n + 1) (fun d => binomInt n d * fwdDiff d f x) := by
  induction n generalizing x with
  | zero =>
    simp [sum, binomInt, fwdDiff]
  | succ n ih =>
    have h1 : x + (n + 1) = (x + 1) + n := by omega
    rw [h1, ih (x + 1), sum_binomInt_succ, <- sum_add]
    apply sum_congr
    intro k _
    simp only [fwdDiff]
    ring
end FiniteDiff
namespace Determinant
def lap {I : Type} : List I -> (I -> List I -> Int) -> Int
  | [], _ => 0
  | c :: cs, f => f c cs - lap cs (fun x xs => f x (c :: xs))
theorem lap_congr {I : Type} (cols : List I) (f g : I -> List I -> Int)
    (h : ∀ c cs, f c cs = g c cs) : lap cols f = lap cols g := by
  induction cols generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    simp only [lap, h]
theorem lap_zero {I : Type} (cols : List I) : lap cols (fun _ _ => 0) = 0 := by
  induction cols with
  | nil => rfl
  | cons c cs ih => simp [lap, ih]
theorem lap_add {I : Type} (cols : List I) (f g : I -> List I -> Int) :
    lap cols (fun c cs => f c cs + g c cs) = lap cols f + lap cols g := by
  induction cols generalizing f g with
  | nil => rfl
  | cons c cs ih => simp only [lap, ih]; ring
theorem lap_sub {I : Type} (cols : List I) (f g : I -> List I -> Int) :
    lap cols (fun c cs => f c cs - g c cs) = lap cols f - lap cols g := by
  induction cols generalizing f g with
  | nil => rfl
  | cons c cs ih => simp only [lap, ih]; ring
theorem lap_smul {I : Type} (cols : List I) (a : Int) (f : I -> List I -> Int) :
    lap cols (fun c cs => a * f c cs) = a * lap cols f := by
  induction cols generalizing f with
  | nil => simp [lap]
  | cons c cs ih => simp only [lap, ih]; ring
theorem lap_swap {I : Type} (cols : List I) (F : I -> I -> List I -> Int) :
    lap cols (fun c cs => lap cs (fun d ds => F c d ds)) =
      -lap cols (fun d ds => lap ds (fun c cs => F c d cs)) := by
  induction cols generalizing F with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap, lap_sub]
    rw [ih (fun x y ys => F x y (c :: ys))]
    ring
theorem perm_cons_swap {I : Type} (c x : I) (cs xs : List I) (h : (x :: xs).Perm cs) :
    (x :: c :: xs).Perm (c :: cs) :=
  (List.Perm.swap c x xs).trans (h.cons c)
theorem lap_congr_perm {I : Type} (cols : List I) (f g : I -> List I -> Int)
    (h : ∀ c cs, (c :: cs).Perm cols -> f c cs = g c cs) : lap cols f = lap cols g := by
  induction cols generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    simp only [lap]
    rw [h c cs (List.Perm.refl _)]
    congr 1
    exact ih _ _ (fun x xs hxs => h x (c :: xs) (perm_cons_swap c x cs xs hxs))
theorem dvd_lap {I : Type} (cols : List I) (f : I -> List I -> Int) (m : Int)
    (h : ∀ c cs, (c :: cs).Perm cols -> m ∣ f c cs) : m ∣ lap cols f := by
  induction cols generalizing f with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap]
    apply dvd_sub
    · exact h c cs (List.Perm.refl _)
    · exact ih _ (fun x xs hxs => h x (c :: xs) (perm_cons_swap c x cs xs hxs))
theorem abs_lap_le {I : Type} (cols : List I) (f : I -> List I -> Int) (b : Int) (_hb : 0 ≤ b)
    (h : ∀ c cs, (c :: cs).Perm cols -> |f c cs| ≤ b) :
    |lap cols f| ≤ (cols.length : Int) * b := by
  induction cols generalizing f with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap, List.length_cons]
    have hhead : |f c cs| ≤ b := h c cs (List.Perm.refl _)
    have htail : |lap cs (fun x xs => f x (c :: xs))| ≤ (cs.length : Int) * b :=
      ih _ (fun x xs hxs => h x (c :: xs) (perm_cons_swap c x cs xs hxs))
    have habs : |f c cs - lap cs (fun x xs => f x (c :: xs))| ≤
        |f c cs| + |lap cs (fun x xs => f x (c :: xs))| := abs_sub _ _
    push_cast
    linarith
def det {I : Type} : List (I -> Int) -> List I -> Int
  | [], _ => 1
  | r :: rs, cols => lap cols (fun c cs => r c * det rs cs)
theorem det_row_add {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int))
    (cols : List I) :
    det (pre ++ (fun c => r c + s c) :: post) cols =
      det (pre ++ r :: post) cols + det (pre ++ s :: post) cols := by
  induction pre generalizing cols with
  | nil =>
    simp only [List.nil_append, det, <- lap_add]
    apply lap_congr; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, det, <- lap_add]
    apply lap_congr; intro c cs; rw [ih]; ring
theorem det_row_smul {I : Type} (pre : List (I -> Int)) (a : Int) (r : I -> Int) (post : List (I ->
    Int)) (cols : List I) :
    det (pre ++ (fun c => a * r c) :: post) cols = a * det (pre ++ r :: post) cols := by
  induction pre generalizing cols with
  | nil =>
    simp only [List.nil_append, det, <- lap_smul]
    apply lap_congr; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, det, <- lap_smul]
    apply lap_congr; intro c cs; rw [ih]; ring
theorem det_row_zero {I : Type} (pre post : List (I -> Int)) (cols : List I) :
    det (pre ++ (fun _ => 0) :: post) cols = 0 := by
  have h : (fun _ : I => (0 : Int)) = (fun _ : I => 0 * (0 : Int)) := by funext _; ring
  rw [h, det_row_smul]; ring
theorem det_swap_head {I : Type} (r s : I -> Int) (post : List (I -> Int)) (cols : List I) :
    det (r :: s :: post) cols = -det (s :: r :: post) cols := by
  simp only [det]
  rw [lap_congr cols (fun c cs => r c * lap cs (fun d ds => s d * det post ds))
    (fun c cs => lap cs (fun d ds => r c * (s d * det post ds)))
    (fun c cs => (lap_smul cs (r c) _).symm)]
  rw [lap_swap]
  congr 1
  apply lap_congr; intro c cs
  rw [<- lap_smul]
  apply lap_congr; intro d ds; ring
theorem det_swap_adj {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int))
    (cols : List I) :
    det (pre ++ r :: s :: post) cols = -det (pre ++ s :: r :: post) cols := by
  induction pre generalizing cols with
  | nil => exact det_swap_head r s post cols
  | cons t pre ih =>
    simp only [List.cons_append, det]
    have h : -lap cols (fun c cs => t c * det (pre ++ s :: r :: post) cs) =
        (-1) * lap cols (fun c cs => t c * det (pre ++ s :: r :: post) cs) := by ring
    rw [h, <- lap_smul]
    apply lap_congr; intro c cs; rw [ih]; ring
theorem det_dup_row {I : Type} (pre mid : List (I -> Int)) (r : I -> Int) (post : List (I -> Int))
    (cols : List I) :
    det (pre ++ r :: mid ++ r :: post) cols = 0 := by
  have hbase : ∀ (ms : List (I -> Int)) (cs : List I), det (r :: ms ++ r :: post) cs = 0 := by
    intro ms
    induction ms with
    | nil =>
      intro cs
      have h := det_swap_head r r post cs
      change det (r :: r :: post) cs = 0
      linarith
    | cons s ms ih =>
      intro cs
      change det (r :: s :: (ms ++ r :: post)) cs = 0
      rw [det_swap_head]
      change -lap cs (fun c xs => s c * det (r :: ms ++ r :: post) xs) = 0
      rw [lap_congr cs (fun c xs => s c * det (r :: ms ++ r :: post) xs) (fun _ _ => 0)
        (fun c xs => by rw [ih xs]; ring)]
      rw [lap_zero]; ring
  induction pre generalizing cols with
  | nil =>
    simp only [List.nil_append]
    exact hbase mid cols
  | cons s pre ih =>
    simp only [List.cons_append, det]
    rw [lap_congr cols (fun c xs => s c * det (pre ++ r :: mid ++ r :: post) xs) (fun _ _ => 0)
      (fun c xs => by rw [ih xs]; ring)]
    exact lap_zero cols
theorem mem_of_cons_perm {I : Type} (c : I) (cs cols : List I) (h : (c :: cs).Perm cols) :
    c ∈ cols /\ ∀ x ∈ cs, x ∈ cols :=
  ⟨h.subset (by simp), fun x hx => h.subset (by simp [hx])⟩
theorem dvd_det_sub_det {I : Type} (m : Int) (rows rows' : List (I -> Int)) (cols : List I)
    (h : List.Forall₂ (fun r s => ∀ c ∈ cols, m ∣ (r c - s c)) rows rows') :
    m ∣ (det rows cols - det rows' cols) := by
  induction rows generalizing rows' cols with
  | nil =>
    cases h
    simp [det]
  | cons r rs ih =>
    cases h with
    | @cons _ s _ ss hr hrs =>
      simp only [det, <- lap_sub]
      apply dvd_lap
      intro c cs hp
      obtain ⟨hc, hcs⟩ := mem_of_cons_perm c cs cols hp
      rcases hr c hc with ⟨a, ha⟩
      have htail : m ∣ (det rs cs - det ss cs) :=
        ih ss cs (hrs.imp (fun _ _ huv d hd => huv d (hcs d hd)))
      rcases htail with ⟨b, hb⟩
      refine ⟨r c * b + a * det ss cs, ?_⟩
      have h1 : s c = r c - m * a := by linarith
      have h2 : det ss cs = det rs cs - m * b := by linarith
      rw [h1, h2]; ring
theorem det_congr_cols {I : Type} (rows rows' : List (I -> Int)) (cols : List I)
    (h : List.Forall₂ (fun r s => ∀ c ∈ cols, r c = s c) rows rows') :
    det rows cols = det rows' cols := by
  have hz : (0 : Int) ∣ (det rows cols - det rows' cols) := by
    apply dvd_det_sub_det
    exact h.imp (fun r s hrs c hc => by rw [hrs c hc]; simp)
  rcases hz with ⟨k, hk⟩
  linarith
def listProd : List Int -> Int
  | [] => 1
  | x :: xs => x * listProd xs
theorem listProd_nonneg (xs : List Int) (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ listProd xs := by
  induction xs with
  | nil => simp [listProd]
  | cons x xs ih =>
    simp only [listProd]
    exact mul_nonneg (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
def RowBounds {I : Type} (cols : List I) (rows : List (I -> Int)) (bounds : List Int) : Prop :=
  List.Forall₂ (fun r b => 0 ≤ b /\ ∀ c ∈ cols, |r c| ≤ b) rows bounds
theorem bounds_nonneg_of_rowBounds {I : Type} (cols : List I) (rows : List (I -> Int)) (bounds :
    List Int)
    (h : RowBounds cols rows bounds) : ∀ b ∈ bounds, 0 ≤ b := by
  induction h with
  | nil => intro b hb; cases hb
  | @cons r b rs bs hrb _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hrb.1
    · exact ih x hmem
theorem rowBounds_mono_cols {I : Type} (cols cs : List I) (rows : List (I -> Int)) (bounds : List
    Int)
    (hcs : ∀ x ∈ cs, x ∈ cols) (h : RowBounds cols rows bounds) : RowBounds cs rows bounds :=
  h.imp (fun _ _ hrb => ⟨hrb.1, fun c hc => hrb.2 c (hcs c hc)⟩)
theorem abs_det_le_factorial_mul_listProd {I : Type} (rows : List (I -> Int)) (cols : List I)
    (bounds : List Int)
    (hlen : rows.length = cols.length) (hbounds : RowBounds cols rows bounds) :
    |det rows cols| ≤ (rows.length.factorial : Int) * listProd bounds := by
  induction rows generalizing cols bounds with
  | nil =>
    cases hbounds
    simp [det, listProd]
  | cons r rs ih =>
    cases hbounds with
    | @cons _ b _ bs hrb hrs =>
      simp only [det, List.length_cons, Nat.factorial_succ, listProd]
      have hprod : 0 ≤ listProd bs := listProd_nonneg bs (bounds_nonneg_of_rowBounds cols rs bs hrs)
      have hfact : (0 : Int) ≤ (rs.length.factorial : Int) := Nat.cast_nonneg _
      have hstep1 : |lap cols (fun c cs => r c * det rs cs)| ≤
          (cols.length : Int) * (b * ((rs.length.factorial : Int) * listProd bs)) := by
        apply abs_lap_le
        · exact mul_nonneg hrb.1 (mul_nonneg hfact hprod)
        · intro c cs hp
          obtain ⟨hc, hcs⟩ := mem_of_cons_perm c cs cols hp
          have hcslen : rs.length = cs.length := by
            have hp_len := hp.length_eq
            simp only [List.length_cons] at hp_len hlen
            omega
          have hd := ih cs bs hcslen (rowBounds_mono_cols cols cs rs bs hcs hrs)
          rw [abs_mul]
          exact mul_le_mul (hrb.2 c hc) hd (abs_nonneg _) hrb.1
      have hstep2 : (cols.length : Int) * (b * ((rs.length.factorial : Int) * listProd bs)) =
          (((rs.length + 1) * rs.length.factorial : Nat) : Int) * (b * listProd bs) := by
        rw [<- hlen]
        simp only [List.length_cons]
        push_cast
        ring
      linarith
theorem sum_smul (n : Nat) (a : Int) (f : Nat -> Int) :
    FiniteDiff.sum n (fun d => a * f d) = a * FiniteDiff.sum n f := by
  induction n with
  | zero => simp [FiniteDiff.sum]
  | succ n ih => simp only [FiniteDiff.sum, ih]; ring
theorem dvd_sum (n : Nat) (m : Int) (f : Nat -> Int)
    (h : ∀ d, d < n -> m ∣ f d) : m ∣ FiniteDiff.sum n f := by
  induction n with
  | zero => simp [FiniteDiff.sum]
  | succ n ih =>
    simp only [FiniteDiff.sum]
    exact dvd_add (ih (fun d hd => h d (by omega))) (h n (by omega))
theorem det_row_sum {I : Type} (pre : List (I -> Int)) (n : Nat) (f : Nat -> I -> Int)
    (post : List (I -> Int)) (cols : List I) :
    det (pre ++ (fun c => FiniteDiff.sum n (fun d => f d c)) :: post) cols =
      FiniteDiff.sum n (fun d => det (pre ++ f d :: post) cols) := by
  induction n with
  | zero => exact det_row_zero pre post cols
  | succ n ih =>
    simp only [FiniteDiff.sum]
    rw [det_row_add, ih]
def coeffProd {J : Type} (coef : J -> Nat -> Int) : List J -> List Nat -> Int
  | [], [] => 1
  | r :: rs, d :: ds => coef r d * coeffProd coef rs ds
  | _, _ => 0
theorem dvd_det_map_sum_basis {I J : Type} (coef : J -> Nat -> Int) (basis : Nat -> I -> Int)
    (D : Nat) (m : Int) (rows : List J) (pre : List (I -> Int)) (cols : List I) (a : Int)
    (h : ∀ ds : List Nat, ds.length = rows.length -> (∀ d ∈ ds, d < D) ->
      m ∣ (a * coeffProd coef rows ds * det (pre ++ ds.map basis) cols)) :
    m ∣ (a * det (pre ++ rows.map (fun r c => FiniteDiff.sum D (fun d => coef r d * basis d c)))
      cols) := by
  induction rows generalizing pre a with
  | nil =>
    have h0 := h [] rfl (by intro d hd; cases hd)
    simp only [List.map_nil, coeffProd, mul_one] at h0 ⊢
    exact h0
  | cons r rs ih =>
    simp only [List.map_cons]
    rw [det_row_sum, <- sum_smul]
    apply dvd_sum
    intro d hd
    rw [det_row_smul]
    have heq : a * (coef r d * det (pre ++ basis d :: rs.map (fun r c => FiniteDiff.sum D (fun d =>
      coef r d * basis d c))) cols) =
        (a * coef r d) * det ((pre ++ [basis d]) ++ rs.map (fun r c => FiniteDiff.sum D (fun d =>
          coef r d * basis d c))) cols := by
      simp only [List.append_assoc, List.singleton_append]
      ring
    rw [heq]
    apply ih (pre ++ [basis d]) (a * coef r d)
    intro ds hlen hds
    have hstep := h (d :: ds) (by simp [hlen]) (by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hd
      · exact hds x hmem)
    simp only [coeffProd, List.map_cons, List.append_assoc, List.singleton_append] at hstep ⊢
    have hmul : a * coef r d * coeffProd coef rs ds * det (pre ++ basis d :: ds.map basis) cols =
        a * (coef r d * coeffProd coef rs ds) * det (pre ++ basis d :: ds.map basis) cols := by ring
    rw [hmul]
    exact hstep
theorem exists_split_of_mem {α : Type} {x : α} {l : List α} (h : x ∈ l) :
    ∃ pre post : List α, l = pre ++ x :: post := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨pre, post, rfl⟩ := ih hmem
      exact ⟨y :: pre, post, rfl⟩
theorem det_map_eq_zero_of_not_nodup_nat {I : Type} (basis : Nat -> I -> Int) (ds : List Nat) (cols
    : List I)
    (h : ¬ ds.Nodup) : det (ds.map basis) cols = 0 := by
  induction ds generalizing cols with
  | nil => exact absurd (by simp) h
  | cons d ds ih =>
    by_cases hin : d ∈ ds
    · obtain ⟨pre, post, rfl⟩ := exists_split_of_mem hin
      have hmap : (d :: (pre ++ d :: post)).map basis =
          [] ++ basis d :: pre.map basis ++ basis d :: post.map basis := by simp
      rw [hmap]
      exact det_dup_row [] (pre.map basis) (basis d) (post.map basis) cols
    · have hds : ¬ ds.Nodup := fun hnd => h (List.Nodup.cons hin hnd)
      simp only [List.map_cons, det]
      rw [lap_congr cols _ (fun _ _ => 0) (fun c cs => by rw [ih cs hds, mul_zero])]
      exact lap_zero cols
end Determinant
namespace DegreeSum
def natListSum : List Nat -> Nat
  | [] => 0
  | d :: ds => d + natListSum ds
def intListSum (ds : List Nat) : Int := (natListSum ds : Int)
@[simp] theorem intListSum_nil : intListSum [] = 0 := rfl
@[simp] theorem intListSum_cons (d : Nat) (ds : List Nat) :
    intListSum (d :: ds) = (d : Int) + intListSum ds := by
  simp [intListSum, natListSum, Nat.cast_add]
theorem intListSum_perm (ds es : List Nat) (h : ds.Perm es) : intListSum ds = intListSum es := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [intListSum_cons, ih]
  | swap x y l => simp only [intListSum_cons]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]
theorem intListSum_nonneg (ds : List Nat) : 0 ≤ intListSum ds := Nat.cast_nonneg _
theorem exists_min_perm_cons (ds : List Nat) (h : ds ≠ []) :
    ∃ d es, ds.Perm (d :: es) /\ ∀ e ∈ es, d ≤ e := by
  induction ds with
  | nil => contradiction
  | cons d ds ih =>
    cases ds with
    | nil =>
      refine ⟨d, [], List.Perm.refl _, ?_⟩
      intro e he; cases he
    | cons e es =>
      obtain ⟨m, ms, hp, hm⟩ := ih (by simp)
      by_cases hdm : d ≤ m
      · refine ⟨d, e :: es, List.Perm.refl _, ?_⟩
        intro x hx
        have hx' : x ∈ m :: ms := hp.subset hx
        rcases List.mem_cons.mp hx' with rfl | hmem
        · exact hdm
        · exact Nat.le_trans hdm (hm x hmem)
      · refine ⟨m, d :: ms, (hp.cons d).trans (List.Perm.swap m d ms), ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · omega
        · exact hm x hmem
theorem nodup_map_pred (ds : List Nat) (hnd : ds.Nodup) (hpos : ∀ d ∈ ds, 0 < d) :
    (ds.map Nat.pred).Nodup := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.map_cons]
    refine List.Nodup.cons ?_ (ih hnd' (fun d hd => hpos d (by simp [hd])))
    intro hin
    rcases List.mem_map.mp hin with ⟨d, hd, hpred⟩
    have hx0 : 0 < x := hpos x (by simp)
    have hd0 : 0 < d := hpos d (by simp [hd])
    simp only [Nat.pred_eq_sub_one] at hpred
    have hxd : x = d := by omega
    subst hxd
    exact hnot hd
theorem intListSum_eq_map_pred_add_length (ds : List Nat) (hpos : ∀ d ∈ ds, 0 < d) :
    intListSum ds = intListSum (ds.map Nat.pred) + (ds.length : Int) := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    simp only [intListSum_cons, List.map_cons, List.length_cons]
    have hx : 0 < x := hpos x (by simp)
    have hih := ih (fun d hd => hpos d (by simp [hd]))
    have hpred : (x : Int) = (x.pred : Int) + 1 := by
      simp only [Nat.pred_eq_sub_one]
      omega
    push_cast
    linarith
theorem length_mul_pred_le_two_mul_intListSum (ds : List Nat) (hdup : ds.Nodup) :
    (ds.length : Int) * ((ds.length : Int) - 1) ≤ 2 * intListSum ds := by
  generalize hlen : ds.length = n
  induction n generalizing ds with
  | zero =>
    cases ds with
    | nil => simp
    | cons _ _ => simp at hlen
  | succ n ih =>
    have hne : ds ≠ [] := by
      intro h; subst h; simp at hlen
    obtain ⟨d, es, hp, hmin⟩ := exists_min_perm_cons ds hne
    have hlen' : es.length = n := by
      have := hp.length_eq
      simp only [List.length_cons] at this
      omega
    have hes : (d :: es).Nodup := hp.nodup_iff.mp hdup
    obtain ⟨hnot, hdup'⟩ := List.nodup_cons.mp hes
    have hpos : ∀ e ∈ es, 0 < e := by
      intro e he
      have hde := hmin e he
      have hne' : e ≠ d := fun h => hnot (h ▸ he)
      omega
    have hlow := ih (es.map Nat.pred) (nodup_map_pred es hdup' hpos) (by simp [hlen'])
    rw [intListSum_perm ds (d :: es) hp, intListSum_cons, intListSum_eq_map_pred_add_length es hpos,
      hlen']
    have hd0 : (0 : Int) ≤ (d : Int) := Nat.cast_nonneg _
    push_cast
    linarith
theorem intListSum_sub_le_map_sub (ds : List Nat) (K : Nat) :
    intListSum ds - (ds.length : Int) * (K : Int) ≤ intListSum (ds.map (fun d => d - K)) := by
  induction ds with
  | nil => simp
  | cons a ds ih =>
    simp only [intListSum_cons, List.map_cons, List.length_cons]
    have ha : (a : Int) - (K : Int) ≤ ((a - K : Nat) : Int) := by omega
    push_cast
    linarith
end DegreeSum
namespace DivisibilityBound
theorem two_pow_dvd_two_pow (a b : Nat) (h : a ≤ b) : ((2 : Int) ^ a) ∣ ((2 : Int) ^ b) := by
  refine ⟨(2 : Int) ^ (b - a), ?_⟩
  rw [<- pow_add, Nat.add_sub_of_le h]
theorem four_pow_dvd_coeffProd {J : Type} (coef : J -> Nat -> Int) (K : Nat) (rows : List J) (ds :
    List Nat)
    (hlen : ds.length = rows.length)
    (hcoef : ∀ r ∈ rows, ∀ d, ((4 : Int) ^ (d - K)) ∣ coef r d) :
    ((4 : Int) ^ (DegreeSum.natListSum (ds.map (fun d => d - K)))) ∣ Determinant.coeffProd coef rows
      ds := by
  induction rows generalizing ds with
  | nil =>
    cases ds with
    | nil => simp [Determinant.coeffProd, DegreeSum.natListSum]
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.map_cons, DegreeSum.natListSum, Determinant.coeffProd, pow_add]
      rcases hcoef r (by simp) d with ⟨a, ha⟩
      have hih := ih ds (by simpa using hlen) (fun s hs => hcoef s (by simp [hs]))
      rcases hih with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      rw [ha, hb]; ring
theorem two_pow_dvd_det_basis {I J : Type} (coef : J -> Nat -> Int) (basis : Nat -> I -> Int)
    (K D e : Nat) (rows : List J) (cols : List I)
    (he : (e : Int) ≤ (rows.length : Int) * ((rows.length : Int) - 1 - 2 * (K : Int)))
    (hcoef : ∀ r ∈ rows, ∀ d, ((4 : Int) ^ (d - K)) ∣ coef r d) :
    ((2 : Int) ^ e) ∣ Determinant.det (rows.map (fun r c => FiniteDiff.sum D (fun d => coef r d *
      basis d c))) cols := by
  have h1 : Determinant.det (rows.map (fun r c => FiniteDiff.sum D (fun d => coef r d * basis d c)))
    cols =
      1 * Determinant.det ([] ++ rows.map (fun r c => FiniteDiff.sum D (fun d => coef r d * basis d
        c))) cols := by
    simp
  rw [h1]
  apply Determinant.dvd_det_map_sum_basis
  intro ds hlen _
  simp only [List.nil_append, one_mul]
  by_cases hnd : ds.Nodup
  · have hsum := DegreeSum.length_mul_pred_le_two_mul_intListSum ds hnd
    have hcost := DegreeSum.intListSum_sub_le_map_sub ds K
    have hexp : e ≤ 2 * DegreeSum.natListSum (ds.map (fun d => d - K)) := by
      rw [hlen] at hsum hcost
      unfold DegreeSum.intListSum at hsum hcost
      have hlin : (rows.length : Int) * ((rows.length : Int) - 1 - 2 * (K : Int)) =
          (rows.length : Int) * ((rows.length : Int) - 1) - 2 * ((rows.length : Int) * (K : Int)) :=
            by ring
      have hexp_int : (e : Int) ≤ 2 * (DegreeSum.natListSum (ds.map (fun d => d - K)) : Int) := by
        linarith
      omega
    have hweight : ((2 : Int) ^ e) ∣ Determinant.coeffProd coef rows ds := by
      apply dvd_trans (two_pow_dvd_two_pow e (2 * DegreeSum.natListSum (ds.map (fun d => d - K)))
        hexp)
      have h4 : ((2 : Int) ^ (2 * DegreeSum.natListSum (ds.map (fun d => d - K)))) =
          ((4 : Int) ^ (DegreeSum.natListSum (ds.map (fun d => d - K)))) := by
        rw [pow_mul]
        rfl
      rw [h4]
      exact four_pow_dvd_coeffProd coef K rows ds hlen hcoef
    exact dvd_mul_of_dvd_left hweight _
  · rw [Determinant.det_map_eq_zero_of_not_nodup_nat basis ds cols hnd, mul_zero]
    exact dvd_zero _
theorem sum_eq_of_eq_zero_range (n m : Nat) (f : Nat -> Int) (hnm : n ≤ m)
    (hz : ∀ d, n ≤ d /\ d < m -> f d = 0) :
    FiniteDiff.sum m f = FiniteDiff.sum n f := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hne : n = m + 1
    · subst hne; rfl
    · simp only [FiniteDiff.sum]
      rw [hz m ⟨by omega, by omega⟩, ih (by omega) (fun d hd => hz d ⟨hd.1, by omega⟩), add_zero]
theorem eq_sum_fwdDiff_binomInt (f : Nat -> Int) (D x : Nat) (hx : x < D) :
    f x = FiniteDiff.sum D (fun d => FiniteDiff.fwdDiff d f 0 * FiniteDiff.binomInt x d) := by
  have h := FiniteDiff.newton_forward_diff f x 0
  rw [Nat.zero_add] at h
  rw [h, sum_eq_of_eq_zero_range (x + 1) D (fun d => FiniteDiff.fwdDiff d f 0 * FiniteDiff.binomInt
    x d) (by omega)]
  · apply FiniteDiff.sum_congr
    intro k _; ring
  · intro d hd
    rw [FiniteDiff.binomInt_eq_zero_of_lt x d (by omega), mul_zero]
theorem two_pow_dvd_det_monomial_geom (K e : Nat) (rows : List (Nat × Int)) (cols : List Nat)
    (he : (e : Int) ≤ (rows.length : Int) * ((rows.length : Int) - 1 - 2 * (K : Int)))
    (hrows : ∀ k q, (k, q) ∈ rows -> k ≤ K /\ ((4 : Int) ∣ (q - 1))) :
    ((2 : Int) ^ e) ∣ Determinant.det (rows.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) cols
      := by
  let D := cols.foldr Nat.max 0 + 1
  have hcols : ∀ x ∈ cols, x < D := by
    change ∀ x ∈ cols, x < cols.foldr Nat.max 0 + 1
    induction cols with
    | nil => intro x hx; cases hx
    | cons y ys ih =>
      intro x hx
      simp only [List.foldr_cons]
      have h1 : y ≤ Nat.max y (ys.foldr Nat.max 0) := Nat.le_max_left y _
      have h2 : ys.foldr Nat.max 0 ≤ Nat.max y (ys.foldr Nat.max 0) := Nat.le_max_right y _
      rcases List.mem_cons.mp hx with rfl | hmem
      · omega
      · have := ih x hmem; omega
  have hext : Determinant.det (rows.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) cols =
      Determinant.det (rows.map (fun p (x : Nat) => FiniteDiff.sum D (fun d =>
        FiniteDiff.fwdDiff d (fun (y : Nat) => (y : Int) ^ p.1 * p.2 ^ y) 0 * FiniteDiff.binomInt x
          d))) cols := by
    apply Determinant.det_congr_cols
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr (fun p _ x hx => eq_sum_fwdDiff_binomInt (fun (y : Nat) => (y : Int)
      ^ p.1 * p.2 ^ y) D x (hcols x hx))
  rw [hext]
  apply two_pow_dvd_det_basis _ (fun d x => FiniteDiff.binomInt x d) K D e rows cols he
  intro ⟨k, q⟩ hp d
  obtain ⟨hk, hq⟩ := hrows k q hp
  exact dvd_trans (FiniteDiff.pow_dvd_pow_of_le (d - K) (d - k) (by omega))
    (FiniteDiff.four_pow_dvd_fwdDiff_monomial_geom q hq k d 0)
end DivisibilityBound
namespace GaussianElim
theorem det_row_sub {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int))
    (cols : List I) :
    Determinant.det (pre ++ (fun c => r c - s c) :: post) cols =
      Determinant.det (pre ++ r :: post) cols - Determinant.det (pre ++ s :: post) cols := by
  induction pre generalizing cols with
  | nil =>
    simp only [List.nil_append, Determinant.det, <- Determinant.lap_sub]
    apply Determinant.lap_congr; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, Determinant.det, <- Determinant.lap_sub]
    apply Determinant.lap_congr; intro c cs; rw [ih]; ring
theorem det_col_zero {I : Type} (rows : List (I -> Int)) (c : I) (cols : List I)
    (hlen : rows.length = cols.length + 1) (hz : ∀ r ∈ rows, r c = 0) :
    Determinant.det rows (c :: cols) = 0 := by
  induction rows generalizing c cols with
  | nil => simp at hlen
  | cons r rs ih =>
    simp only [Determinant.det, Determinant.lap]
    rw [hz r (by simp), zero_mul, zero_sub, neg_eq_zero]
    rw [Determinant.lap_congr_perm cols (fun d ds => r d * Determinant.det rs (c :: ds)) (fun _ _ =>
      0)]
    · exact Determinant.lap_zero cols
    · intro d ds hp
      have hp_len := hp.length_eq
      simp only [List.length_cons] at hlen hp_len
      rw [ih c ds (by omega) (fun s hs => hz s (by simp [hs])), mul_zero]
theorem det_col_head_only {I : Type} (r : I -> Int) (rs : List (I -> Int)) (c : I) (cols : List I)
    (hlen : rs.length = cols.length) (hz : ∀ s ∈ rs, s c = 0) :
    Determinant.det (r :: rs) (c :: cols) = r c * Determinant.det rs cols := by
  simp only [Determinant.det, Determinant.lap]
  rw [Determinant.lap_congr_perm cols (fun d ds => r d * Determinant.det rs (c :: ds)) (fun _ _ =>
    0)]
  · rw [Determinant.lap_zero]; ring
  · intro d ds hp
    have hp_len := hp.length_eq
    simp only [List.length_cons] at hp_len
    rw [det_col_zero rs c ds (by omega) hz, mul_zero]
theorem det_row_elim_one {I : Type} (r s : I -> Int) (a b : Int) (pre post : List (I -> Int)) (cols
    : List I) :
    Determinant.det (r :: (pre ++ (fun x => a * s x - b * r x) :: post)) cols =
      a * Determinant.det (r :: (pre ++ s :: post)) cols := by
  change Determinant.det ((r :: pre) ++ (fun x => a * s x - b * r x) :: post) cols =
    a * Determinant.det ((r :: pre) ++ s :: post) cols
  rw [det_row_sub, Determinant.det_row_smul, Determinant.det_row_smul]
  have hzero := Determinant.det_dup_row [] pre r post cols
  simp only [List.nil_append] at hzero
  change Determinant.det ((r :: pre) ++ r :: post) cols = 0 at hzero
  rw [hzero]; ring
theorem det_row_elim_map {I : Type} (r : I -> Int) (c : I) (a : Int) (rs pre : List (I -> Int))
    (cols : List I) :
    Determinant.det (r :: (pre ++ rs.map (fun s x => a * s x - s c * r x))) cols =
      a ^ rs.length * Determinant.det (r :: (pre ++ rs)) cols := by
  induction rs generalizing pre cols with
  | nil => simp
  | cons s rs ih =>
    simp only [List.map_cons, List.length_cons]
    rw [det_row_elim_one]
    have h1 : pre ++ s :: rs.map (fun s x => a * s x - s c * r x) =
        (pre ++ [s]) ++ rs.map (fun s x => a * s x - s c * r x) := by simp
    have h2 : pre ++ s :: rs = (pre ++ [s]) ++ rs := by simp
    rw [h1, ih (pre ++ [s]) cols, h2, pow_succ]
    ring
def linComb {I : Type} : List (I -> Int) -> List Int -> I -> Int
  | r :: rs, w :: ws, c => w * r c + linComb rs ws c
  | _, _, _ => 0
theorem linComb_replicate_zero {I : Type} (rows : List (I -> Int)) (c : I) :
    linComb rows (List.replicate rows.length 0) c = 0 := by
  induction rows with
  | nil => rfl
  | cons r rs ih => simp [List.replicate_succ, linComb, ih]
theorem linComb_map_smul {I : Type} (rows : List (I -> Int)) (ws : List Int) (a : Int) (c : I) :
    linComb rows (ws.map (fun w => a * w)) c = a * linComb rows ws c := by
  induction rows generalizing ws with
  | nil => simp [linComb]
  | cons r rs ih =>
    cases ws with
    | nil => simp [linComb]
    | cons w ws => simp only [List.map_cons, linComb, ih]; ring
theorem linComb_map_elim {I : Type} (rows : List (I -> Int)) (ws : List Int)
    (r : I -> Int) (c : I) (a : Int) (x : I) :
    linComb (rows.map (fun s x => a * s x - s c * r x)) ws x =
      a * linComb rows ws x - r x * linComb rows ws c := by
  induction rows generalizing ws with
  | nil => simp [linComb]
  | cons s rs ih =>
    cases ws with
    | nil => simp [linComb]
    | cons w ws => simp only [List.map_cons, linComb, ih]; ring
def RowIndep {I : Type} (rows : List (I -> Int)) (cols : List I) : Prop :=
  ∀ ws : List Int, ws.length = rows.length ->
    (∀ c ∈ cols, linComb rows ws c = 0) ->
    ∀ w ∈ ws, w = 0
theorem exists_col_ne_zero_of_rowIndep {I : Type} (r : I -> Int) (rs : List (I -> Int)) (cols : List
    I)
    (hind : RowIndep (r :: rs) cols) : ∃ c ∈ cols, r c ≠ 0 := by
  by_contra h
  push Not at h
  have hbad := hind (1 :: List.replicate rs.length 0) (by simp) (by
    intro c hc
    simp only [linComb, linComb_replicate_zero, h c hc]
    ring)
  have h1 : (1 : Int) = 0 := hbad 1 (by simp)
  omega
theorem rowIndep_elim {I : Type} (r : I -> Int) (rs : List (I -> Int)) (cols : List I) (c : I)
    (hind : RowIndep (r :: rs) cols) (hc : r c ≠ 0) :
    RowIndep (rs.map (fun s x => r c * s x - s c * r x)) cols := by
  intro ws hlen hz
  rw [List.length_map] at hlen
  have hrel := hind (-linComb rs ws c :: ws.map (fun w => r c * w))
    (by simp [hlen])
    (by
      intro x hx
      have hzx := hz x hx
      rw [linComb_map_elim] at hzx
      simp only [linComb, linComb_map_smul]
      linarith)
  intro w hw
  have hmem : r c * w ∈ -linComb rs ws c :: ws.map (fun w => r c * w) :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hmul : r c * w = 0 := hrel (r c * w) hmem
  rcases mul_eq_zero.mp hmul with hrc | hw0
  · exact absurd hrc hc
  · exact hw0
theorem exists_cols_det_ne_zero {I : Type} (rows : List (I -> Int)) (cols : List I)
    (hind : RowIndep rows cols) :
    ∃ cs : List I, cs.length = rows.length /\ (∀ x ∈ cs, x ∈ cols) /\ Determinant.det rows cs ≠ 0 :=
      by
  generalize hlen : rows.length = n
  induction n generalizing rows with
  | zero =>
    cases rows with
    | nil =>
      refine ⟨[], rfl, ?_, by simp [Determinant.det]⟩
      intro x hx; cases hx
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases rows with
    | nil => simp at hlen
    | cons r rs =>
      obtain ⟨c, hc, hr⟩ := exists_col_ne_zero_of_rowIndep r rs cols hind
      obtain ⟨cs, hcs, hin, hdet⟩ := ih (rs.map (fun s x => r c * s x - s c * r x))
        (rowIndep_elim r rs cols c hind hr)
        (by simp only [List.length_cons] at hlen; rw [List.length_map]; omega)
      refine ⟨c :: cs, by simp [hcs], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hc
        · exact hin x hmem
      · intro hzero
        have heq := det_row_elim_map r c (r c) rs [] (c :: cs)
        simp only [List.nil_append] at heq
        rw [hzero, mul_zero] at heq
        rw [det_col_head_only r (rs.map (fun s x => r c * s x - s c * r x)) c cs
          (by simp only [List.length_cons] at hlen; simp [hcs]; omega)
          (by
            intro s hs
            rcases List.mem_map.mp hs with ⟨t, _, rfl⟩
            ring)] at heq
        rcases mul_eq_zero.mp heq with hrc | hdet0
        · exact hr hrc
        · exact hdet hdet0
theorem det_linComb_cons_eq_zero {I : Type} (rows : List (I -> Int)) (ws : List Int)
    (pre : List (I -> Int)) (cols : List I) :
    Determinant.det (linComb rows ws :: (pre ++ rows)) cols = 0 := by
  induction rows generalizing ws pre cols with
  | nil =>
    have : linComb ([] : List (I -> Int)) ws = (fun _ => 0) := by funext _; rfl
    rw [this]
    exact Determinant.det_row_zero [] (pre ++ []) cols
  | cons r rs ih =>
    cases ws with
    | nil =>
      have : linComb (r :: rs) [] = (fun _ => 0) := by funext _; rfl
      rw [this]
      exact Determinant.det_row_zero [] (pre ++ r :: rs) cols
    | cons w ws =>
      change Determinant.det ([] ++ (fun c => w * r c + linComb rs ws c) :: (pre ++ r :: rs)) cols =
        0
      rw [Determinant.det_row_add, Determinant.det_row_smul]
      have hr := Determinant.det_dup_row [] pre r rs cols
      simp only [List.nil_append, List.cons_append] at hr ⊢
      rw [hr]
      have h1 : pre ++ r :: rs = (pre ++ [r]) ++ rs := by simp
      rw [h1, ih ws (pre ++ [r]) cols]
      ring
theorem det_cons_eq_zero_of_linComb_eq_zero {I : Type} (r : I -> Int) (rs : List (I -> Int))
    (a : Int) (ws : List Int) (cols : List I) (ha : a ≠ 0)
    (hrel : ∀ c ∈ cols, a * r c + linComb rs ws c = 0) :
    Determinant.det (r :: rs) cols = 0 := by
  have hdet : Determinant.det ((fun c => a * r c + linComb rs ws c) :: rs) cols = 0 := by
    rw [Determinant.det_congr_cols _ ((fun _ => 0) :: rs) cols]
    · exact Determinant.det_row_zero [] rs cols
    · refine List.Forall₂.cons hrel ?_
      exact List.forall₂_same.mpr (fun _ _ _ _ => rfl)
  change Determinant.det ([] ++ (fun c => a * r c + linComb rs ws c) :: rs) cols = 0 at hdet
  rw [Determinant.det_row_add, Determinant.det_row_smul] at hdet
  have hzero := det_linComb_cons_eq_zero rs ws [] cols
  simp only [List.nil_append] at hdet hzero
  rw [hzero, add_zero] at hdet
  rcases mul_eq_zero.mp hdet with ha0 | hr0
  · exact absurd ha0 ha
  · exact hr0
end GaussianElim
namespace HadamardBound
theorem listProd_replicate (a : Int) (n : Nat) :
    Determinant.listProd (List.replicate n a) = a ^ n := by
  induction n with
  | zero => simp [Determinant.listProd]
  | succ n ih =>
    simp only [List.replicate_succ, Determinant.listProd, ih]; ring
theorem factorial_le_pow (n : Nat) (b : Int) (hb : 0 ≤ b) (hn : (n : Int) ≤ b) :
    (n.factorial : Int) ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.factorial_succ, Nat.cast_mul]
    calc ((n + 1 : Nat) : Int) * (n.factorial : Int)
      _ ≤ b * b ^ n := mul_le_mul hn (ih (by push_cast at hn; linarith)) (Nat.cast_nonneg _) hb
      _ = b ^ (n + 1) := by ring
theorem abs_det_le_two_pow {I : Type} (rows : List (I -> Int)) (cols : List I) (m b : Nat)
    (hlen : rows.length = cols.length)
    (hsize : rows.length ≤ 2 ^ m)
    (hrows : ∀ r ∈ rows, ∀ c ∈ cols, |r c| ≤ (2 : Int) ^ b) :
    |Determinant.det rows cols| ≤ (2 : Int) ^ (rows.length * (m + b)) := by
  have hbounds : Determinant.RowBounds cols rows (List.replicate rows.length ((2 : Int) ^ b)) := by
    clear hlen hsize
    induction rows with
    | nil => exact List.Forall₂.nil
    | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ]
      refine List.Forall₂.cons ⟨by positivity, hrows r (by simp)⟩ ?_
      exact ih (fun s hs => hrows s (by simp [hs]))
  have hdet := Determinant.abs_det_le_factorial_mul_listProd rows cols _ hlen hbounds
  rw [listProd_replicate] at hdet
  have hsize' : (rows.length : Int) ≤ (2 : Int) ^ m := by exact_mod_cast hsize
  have hfact := factorial_le_pow rows.length ((2 : Int) ^ m) (by positivity) hsize'
  have hp : (0 : Int) ≤ ((2 : Int) ^ b) ^ rows.length := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfact hp
  have hpow : ((2 : Int) ^ m) ^ rows.length * ((2 : Int) ^ b) ^ rows.length =
      (2 : Int) ^ (rows.length * (m + b)) := by
    rw [<- pow_mul, <- pow_mul, <- pow_add]
    congr 1
    ring
  linarith
theorem false_of_two_pow_dvd_and_abs_le (D : Int) (U T : Nat)
    (hut : U < T) (hd : D ≠ 0) (hdiv : ((2 : Int) ^ T) ∣ D) (hbound : |D| ≤ (2 : Int) ^ U) :
    False := by
  rcases hdiv with ⟨w, rfl⟩
  have hw0 : w ≠ 0 := fun h => hd (by simp [h])
  have hw_abs : 1 ≤ |w| := Int.one_le_abs hw0
  have hpow_pos : (0 : Int) < (2 : Int) ^ T := by positivity
  have hstrict : (2 : Int) ^ U < (2 : Int) ^ T := by
    exact pow_lt_pow_right₀ (by norm_num) hut
  rw [abs_mul, abs_of_pos hpow_pos] at hbound
  have hle : (2 : Int) ^ T * 1 ≤ (2 : Int) ^ T * |w| :=
    mul_le_mul_of_nonneg_left hw_abs (le_of_lt hpow_pos)
  linarith
theorem lap_map {I J : Type} (f : I -> J) (cs : List I) (g : J -> List J -> Int) :
    Determinant.lap (cs.map f) g = Determinant.lap cs (fun c cs => g (f c) (cs.map f)) := by
  induction cs generalizing g with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, Determinant.lap, ih]
theorem det_map_cols {I J : Type} (f : I -> J) (rows : List (J -> Int)) (cs : List I) :
    Determinant.det rows (cs.map f) = Determinant.det (rows.map (fun r c => r (f c))) cs := by
  induction rows generalizing cs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, Determinant.det, lap_map]
    apply Determinant.lap_congr
    intro c ds
    rw [ih]
end HadamardBound
namespace Poly
def eval : List Int -> Int -> Int
  | [], _ => 0
  | a :: p, x => a + x * Poly.eval p x
def divLinear : List Int -> Int -> List Int
  | [], _ => []
  | _ :: [], _ => []
  | _ :: d :: ps, a => Poly.eval (d :: ps) a :: divLinear (d :: ps) a
theorem length_divLinear (p : List Int) (a : Int) :
    (divLinear p a).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    cases p with
    | nil => rfl
    | cons d ps =>
      simp only [divLinear, List.length_cons, ih]
      omega
theorem eval_sub_eval_eq_mul_divLinear (p : List Int) (a x : Int) :
    Poly.eval p x - Poly.eval p a = (x - a) * Poly.eval (divLinear p a) x := by
  induction p with
  | nil => simp [Poly.eval, divLinear]
  | cons c p ih =>
    cases p with
    | nil => simp [Poly.eval, divLinear]
    | cons d ps =>
      simp only [Poly.eval, divLinear] at ih ⊢
      have h1 : d + x * Poly.eval ps x = d + a * Poly.eval ps a + (x - a) * Poly.eval (divLinear (d
        :: ps) a) x := by linarith
      rw [h1]; ring
theorem eval_eq_zero_of_forall_zero (p : List Int) (x : Int) (h : ∀ a ∈ p, a = 0) : Poly.eval p x =
    0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [Poly.eval, h a (by simp), ih (fun b hb => h b (by simp [hb])), mul_zero, add_zero]
theorem forall_tail_zero_of_divLinear_zero (p : List Int) (a : Int) (h : ∀ c ∈ divLinear p a, c = 0)
    :
    ∀ c ∈ p.tail, c = 0 := by
  induction p with
  | nil => intro c hc; cases hc
  | cons c p ih =>
    cases p with
    | nil => intro x hx; cases hx
    | cons d ps =>
      simp only [divLinear] at h
      have hd : Poly.eval (d :: ps) a = 0 := h (Poly.eval (d :: ps) a) (by simp)
      have hps : ∀ x ∈ ps, x = 0 := ih (fun x hx => h x (by simp [hx]))
      simp only [Poly.eval, eval_eq_zero_of_forall_zero ps a hps, mul_zero, add_zero] at hd
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hd
      · exact hps x hmem
theorem forall_zero_of_nodup_roots (p roots : List Int) (hnd : roots.Nodup)
    (hz : ∀ x ∈ roots, Poly.eval p x = 0) (hsize : p.length ≤ roots.length) :
    ∀ a ∈ p, a = 0 := by
  generalize hlen : p.length = n
  induction n generalizing p roots with
  | zero =>
    cases p with
    | nil => intro a ha; cases ha
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases p with
    | nil => simp at hlen
    | cons c p =>
      cases roots with
      | nil => simp at hsize
      | cons a rs =>
        obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
        have ha : Poly.eval (c :: p) a = 0 := hz a (by simp)
        have hquot : ∀ x ∈ divLinear (c :: p) a, x = 0 := by
          apply ih (divLinear (c :: p) a) rs hnd'
          · intro x hx
            have hq := eval_sub_eval_eq_mul_divLinear (c :: p) a x
            have hzx : Poly.eval (c :: p) x = 0 := hz x (by simp [hx])
            rw [hzx, ha, sub_zero] at hq
            have hxa : x - a ≠ 0 := sub_ne_zero.mpr (fun h => hnot (h ▸ hx))
            rcases mul_eq_zero.mp hq.symm with h1 | h2
            · exact absurd h1 hxa
            · exact h2
          · rw [length_divLinear]
            simp only [List.length_cons] at hsize ⊢
            omega
          · rw [length_divLinear]
            simp only [List.length_cons] at hlen ⊢
            omega
        have hp : ∀ x ∈ p, x = 0 := forall_tail_zero_of_divLinear_zero (c :: p) a hquot
        simp only [Poly.eval, eval_eq_zero_of_forall_zero p a hp, mul_zero, add_zero] at ha
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ha
        · exact hp x hmem
def add : List Int -> List Int -> List Int
  | [], q => q
  | p, [] => p
  | a :: ps, b :: qs => (a + b) :: add ps qs
def smul (a : Int) (p : List Int) : List Int := p.map (a * ·)
def mul : List Int -> List Int -> List Int
  | [], _ => []
  | _, [] => []
  | a :: ps, q => add (smul a q) (0 :: mul ps q)
theorem eval_add (p q : List Int) (x : Int) : Poly.eval (add p q) x = Poly.eval p x + Poly.eval q x
    := by
  induction p generalizing q with
  | nil => simp [add, Poly.eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, Poly.eval]
    | cons b q => simp only [add, Poly.eval, ih]; ring
theorem eval_smul (a : Int) (p : List Int) (x : Int) : Poly.eval (smul a p) x = a * Poly.eval p x :=
    by
  induction p with
  | nil => simp [smul, Poly.eval]
  | cons b p ih =>
    simp only [smul, List.map_cons, Poly.eval]
    rw [ <- smul, ih]
    ring
theorem eval_mul (p q : List Int) (x : Int) : Poly.eval (mul p q) x = Poly.eval p x * Poly.eval q x
    := by
  induction p generalizing q with
  | nil => simp [mul, Poly.eval]
  | cons a p ih =>
    cases q with
    | nil => simp [mul, Poly.eval]
    | cons b q =>
      simp only [mul, eval_add, eval_smul, Poly.eval, ih]
      ring
def shift : List Int -> Int -> List Int
  | [], _ => []
  | c :: ps, a => add [c] (mul [a, 1] (shift ps a))
theorem eval_shift (p : List Int) (a x : Int) : Poly.eval (shift p a) x = Poly.eval p (x + a) := by
  induction p with
  | nil => rfl
  | cons c ps ih =>
    simp only [shift, eval_add, eval_mul, ih, Poly.eval]
    ring
def coeff (p : List Int) (n : Nat) : Int := p.getD n 0
@[simp] theorem coeff_nil (n : Nat) : coeff [] n = 0 := by
  simp [coeff]
@[simp] theorem coeff_cons_zero (a : Int) (p : List Int) : coeff (a :: p) 0 = a := by
  simp [coeff]
@[simp] theorem coeff_cons_succ (a : Int) (p : List Int) (n : Nat) :
    coeff (a :: p) (n + 1) = coeff p n := by
  simp [coeff]
theorem coeff_eq_zero_of_length_le (p : List Int) (n : Nat) (h : p.length ≤ n) : coeff p n = 0 := by
  induction p generalizing n with
  | nil => exact coeff_nil n
  | cons a p ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [coeff_cons_succ]
      exact ih n (by simp at h; omega)
theorem coeff_eq_zero_of_forall_zero (p : List Int) (n : Nat) (h : ∀ a ∈ p, a = 0) :
    coeff p n = 0 := by
  induction p generalizing n with
  | nil => exact coeff_nil n
  | cons a p ih =>
    cases n with
    | zero => exact h a (by simp)
    | succ n => exact ih n (fun b hb => h b (by simp [hb]))
theorem coeff_add (p q : List Int) (n : Nat) :
    coeff (add p q) n = coeff p n + coeff q n := by
  induction p generalizing q n with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      cases n with
      | zero => simp [add]
      | succ n => simp only [add, coeff_cons_succ, ih]
theorem coeff_smul (a : Int) (p : List Int) (n : Nat) :
    coeff (smul a p) n = a * coeff p n := by
  induction p generalizing n with
  | nil => simp [smul]
  | cons b p ih =>
    cases n with
    | zero => simp [smul]
    | succ n =>
      simp only [smul, List.map_cons, coeff_cons_succ]
      exact ih n
theorem length_add (p q : List Int) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      simp only [add, List.length_cons, ih]
      omega
theorem length_smul (a : Int) (p : List Int) : (smul a p).length = p.length := by
  simp [smul]
theorem length_mul_le (p q : List Int) : (mul p q).length ≤ p.length + q.length - 1 := by
  induction p generalizing q with
  | nil => simp [mul]
  | cons a p ih =>
    cases q with
    | nil => simp [mul]
    | cons b q =>
      simp only [mul, length_add, length_smul, List.length_cons]
      have := ih (b :: q)
      simp only [List.length_cons] at this
      omega
theorem length_shift_le (p : List Int) (a : Int) : (shift p a).length ≤ p.length := by
  induction p with
  | nil => simp [shift]
  | cons c p ih =>
    simp only [shift, length_add, List.length_cons, List.length_nil]
    have hmul := length_mul_le [a, 1] (shift p a)
    simp only [List.length_cons, List.length_nil] at hmul
    omega
theorem coeff_mul_top (p q : List Int) (d e : Nat)
    (hp : p.length ≤ d + 1) (hq : q.length ≤ e + 1) :
    coeff (mul p q) (d + e) = coeff p d * coeff q e := by
  induction d generalizing p q with
  | zero =>
    cases p with
    | nil => simp [mul]
    | cons a p =>
      cases p with
      | nil =>
        cases q with
        | nil => simp [mul]
        | cons b q =>
          simp only [mul, coeff_add, coeff_smul, Nat.zero_add, coeff_cons_zero]
          have hz : coeff [0] e = 0 := by
            cases e <;> simp
          rw [hz, add_zero]
      | cons _ _ => simp at hp
  | succ d ih =>
    cases p with
    | nil => simp [mul]
    | cons a p =>
      cases q with
      | nil => simp [mul]
      | cons b q =>
        have hstep : d + 1 + e = (d + e) + 1 := by omega
        rw [hstep]
        simp only [mul, coeff_add, coeff_smul, coeff_cons_succ]
        rw [coeff_eq_zero_of_length_le q (d + e) (by simp at hq; omega), mul_zero, zero_add]
        exact ih p (b :: q) (by simp at hp; omega) hq
theorem coeff_shift_top (p : List Int) (a : Int) (d : Nat) (hp : p.length ≤ d + 1) :
    coeff (shift p a) d = coeff p d := by
  induction d generalizing p with
  | zero =>
    cases p with
    | nil => rfl
    | cons c p =>
      cases p with
      | nil => rfl
      | cons _ _ => simp at hp
  | succ d ih =>
    cases p with
    | nil => rfl
    | cons c p =>
      simp only [shift, coeff_add, coeff_cons_succ, coeff_nil, zero_add]
      have h1 : d + 1 = 1 + d := by omega
      rw [h1, coeff_mul_top [a, 1] (shift p a) 1 d (by simp)
        (Nat.le_trans (length_shift_le p a) (by simp at hp; omega))]
      have h2 : coeff [a, 1] 1 = 1 := rfl
      rw [h2, one_mul]
      exact ih p (by simp at hp; omega)
end Poly
namespace PolyDet
def polyLap {I : Type} : List I -> (I -> List I -> List Int) -> List Int
  | [], _ => []
  | c :: cs, f => Poly.add (f c cs) (Poly.smul (-1) (polyLap cs (fun d ds => f d (c :: ds))))
theorem eval_polyLap {I : Type} (cols : List I) (f : I -> List I -> List Int) (x : Int) :
    Poly.eval (polyLap cols f) x = Determinant.lap cols (fun c cs => Poly.eval (f c cs) x) := by
  induction cols generalizing f with
  | nil => rfl
  | cons c cs ih =>
    simp only [polyLap, Determinant.lap, Poly.eval_add, Poly.eval_smul, ih]
    ring
theorem coeff_polyLap {I : Type} (cols : List I) (f : I -> List I -> List Int) (n : Nat) :
    Poly.coeff (polyLap cols f) n = Determinant.lap cols (fun c cs => Poly.coeff (f c cs) n) := by
  induction cols generalizing f with
  | nil => simp [polyLap, Determinant.lap]
  | cons c cs ih =>
    simp only [polyLap, Determinant.lap, Poly.coeff_add, Poly.coeff_smul, ih]
    ring
theorem length_polyLap_le {I : Type} (cols : List I) (f : I -> List I -> List Int) (n : Nat)
    (h : ∀ c cs, (f c cs).length ≤ n) : (polyLap cols f).length ≤ n := by
  induction cols generalizing f with
  | nil => simp [polyLap]
  | cons c cs ih =>
    simp only [polyLap, Poly.length_add, Poly.length_smul]
    have h1 := h c cs
    have h2 := ih (fun d ds => f d (c :: ds)) (fun d ds => h d (c :: ds))
    omega
def totalDeg {I : Type} : List (Nat × (I -> List Int)) -> Nat
  | [] => 0
  | (d, _) :: rs => d + totalDeg rs
def polyDet {I : Type} : List (Nat × (I -> List Int)) -> List I -> List Int
  | [], _ => [1]
  | (_, r) :: rs, cols => polyLap cols (fun c cs => Poly.mul (r c) (polyDet rs cs))
def DegBounded {I : Type} (rows : List (Nat × (I -> List Int))) : Prop :=
  ∀ p ∈ rows, ∀ c, (p.2 c).length ≤ p.1 + 1
theorem eval_polyDet {I : Type} (rows : List (Nat × (I -> List Int))) (cols : List I) (x : Int) :
    Poly.eval (polyDet rows cols) x =
      Determinant.det (rows.map (fun p c => Poly.eval (p.2 c) x)) cols := by
  induction rows generalizing cols with
  | nil => simp [polyDet, Determinant.det, Poly.eval]
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [polyDet, List.map_cons, Determinant.det, eval_polyLap]
    apply Determinant.lap_congr
    intro c cs
    rw [Poly.eval_mul, ih]
theorem length_polyDet_le {I : Type} (rows : List (Nat × (I -> List Int))) (h : DegBounded rows)
    (cols : List I) :
    (polyDet rows cols).length ≤ totalDeg rows + 1 := by
  induction rows generalizing cols with
  | nil => simp [polyDet, totalDeg]
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [polyDet, totalDeg]
    apply length_polyLap_le
    intro c cs
    have hmul := Poly.length_mul_le (r c) (polyDet rs cs)
    have hr := h (d, r) (by simp) c
    simp only at hr
    have hrs := ih (fun q hq => h q (by simp [hq])) cs
    omega
theorem coeff_polyDet_totalDeg {I : Type} (rows : List (Nat × (I -> List Int))) (h : DegBounded
    rows) (cols : List I) :
    Poly.coeff (polyDet rows cols) (totalDeg rows) =
      Determinant.det (rows.map (fun p c => Poly.coeff (p.2 c) p.1)) cols := by
  induction rows generalizing cols with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [polyDet, totalDeg, List.map_cons, Determinant.det, coeff_polyLap]
    apply Determinant.lap_congr
    intro c cs
    have hvalid_rs : DegBounded rs := fun q hq => h q (by simp [hq])
    rw [Poly.coeff_mul_top (r c) (polyDet rs cs) d (totalDeg rs)
      (h (d, r) (by simp) c) (length_polyDet_le rs hvalid_rs cs)]
    rw [ih hvalid_rs cs]
end PolyDet
namespace DetTranspose
theorem lap_comm {I J : Type} (xs : List I) (ys : List J) (F : I -> List I -> J -> List J -> Int) :
    Determinant.lap xs (fun x xs => Determinant.lap ys (fun y ys => F x xs y ys)) =
      Determinant.lap ys (fun y ys => Determinant.lap xs (fun x xs => F x xs y ys)) := by
  induction xs generalizing F with
  | nil =>
    simp only [Determinant.lap]
    exact (Determinant.lap_zero ys).symm
  | cons x xs ih =>
    simp only [Determinant.lap, ih, Determinant.lap_sub]
theorem det_cons_col_eq_lap_rows {I J : Type} (M : J -> I -> Int) (xs : List J) (y : I) (ys : List
    I)
    (hlen : xs.length = ys.length + 1) :
    Determinant.det (xs.map M) (y :: ys) =
      Determinant.lap xs (fun x xs => M x y * Determinant.det (xs.map M) ys) := by
  induction xs generalizing y ys with
  | nil => simp at hlen
  | cons x xs ih =>
    simp only [List.map_cons, Determinant.det, Determinant.lap]
    congr 1
    rw [Determinant.lap_congr_perm ys
      (fun z zs => M x z * Determinant.det (xs.map M) (y :: zs))
      (fun z zs => Determinant.lap xs (fun t ts => M x z * (M t y * Determinant.det (ts.map M)
        zs)))]
    · rw [lap_comm]
      apply Determinant.lap_congr
      intro t ts
      rw [<- Determinant.lap_smul]
      apply Determinant.lap_congr
      intro z zs; ring
    · intro z zs hp
      have hp_len := hp.length_eq
      simp only [List.length_cons] at hlen hp_len
      rw [ih y zs (by omega), Determinant.lap_smul]
theorem det_transpose {I J : Type} (M : J -> I -> Int) (xs : List J) (ys : List I)
    (hlen : xs.length = ys.length) :
    Determinant.det (xs.map M) ys = Determinant.det (ys.map (fun y x => M x y)) xs := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons y ys ih =>
    rw [det_cons_col_eq_lap_rows M xs y ys hlen]
    simp only [List.map_cons, Determinant.det]
    apply Determinant.lap_congr_perm
    intro x xs' hp
    have hp_len := hp.length_eq
    simp only [List.length_cons] at hlen hp_len
    rw [ih xs' (by omega)]
theorem det_eq_zero_iff_of_perm_rows {I : Type} (rows rows' : List (I -> Int)) (h : rows.Perm rows')
    (pre : List (I -> Int)) (cols : List I) :
    Determinant.det (pre ++ rows) cols = 0 <-> Determinant.det (pre ++ rows') cols = 0 := by
  induction h generalizing pre cols with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    have h1 : pre ++ x :: l₁ = (pre ++ [x]) ++ l₁ := by simp
    have h2 : pre ++ x :: l₂ = (pre ++ [x]) ++ l₂ := by simp
    rw [h1, h2]
    exact ih (pre ++ [x]) cols
  | swap x y l =>
    rw [Determinant.det_swap_adj]
    exact neg_eq_zero
  | trans _ _ ih1 ih2 =>
    exact (ih1 pre cols).trans (ih2 pre cols)
theorem det_eq_zero_iff_of_perm_cols {I J : Type} (M : J -> I -> Int) (xs : List J) (ys zs : List I)
    (hlen : xs.length = ys.length) (hp : ys.Perm zs) :
    Determinant.det (xs.map M) ys = 0 <-> Determinant.det (xs.map M) zs = 0 := by
  have hlen' : xs.length = zs.length := hlen.trans hp.length_eq
  rw [det_transpose M xs ys hlen, det_transpose M xs zs hlen']
  exact det_eq_zero_iff_of_perm_rows _ _ (hp.map (fun y x => M x y)) [] xs
theorem det_map_eq_zero_of_not_nodup {I J : Type} (basis : J -> I -> Int) (xs : List J) (cols : List
    I)
    (h : ¬ xs.Nodup) : Determinant.det (xs.map basis) cols = 0 := by
  induction xs generalizing cols with
  | nil => exact absurd (by simp) h
  | cons x xs ih =>
    by_cases hin : x ∈ xs
    · obtain ⟨pre, post, rfl⟩ := Determinant.exists_split_of_mem hin
      have hmap : (x :: (pre ++ x :: post)).map basis =
          [] ++ basis x :: pre.map basis ++ basis x :: post.map basis := by simp
      rw [hmap]
      exact Determinant.det_dup_row [] (pre.map basis) (basis x) (post.map basis) cols
    · have hxs : ¬ xs.Nodup := fun hnd => h (List.Nodup.cons hin hnd)
      simp only [List.map_cons, Determinant.det]
      rw [Determinant.lap_congr cols _ (fun _ _ => 0) (fun c cs => by rw [ih cs hxs, mul_zero])]
      exact Determinant.lap_zero cols
theorem perm_cons_append {α : Type} (c : α) (pre post : List α) :
    (c :: (pre ++ post)).Perm (pre ++ c :: post) := by
  induction pre with
  | nil => exact List.Perm.refl _
  | cons x pre ih =>
    simp only [List.cons_append]
    exact (List.Perm.swap x c (pre ++ post)).trans (ih.cons x)
theorem perm_of_nodup_length_subset {I : Type} {cs cols : List I}
    (hnd : cs.Nodup) (hlen : cs.length = cols.length) (hsub : ∀ x ∈ cs, x ∈ cols) :
    cs.Perm cols := by
  induction cs generalizing cols with
  | nil =>
    cases cols with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp at hlen
  | cons c cs ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨pre, post, rfl⟩ := Determinant.exists_split_of_mem (hsub c (by simp))
    have hsub' : ∀ x ∈ cs, x ∈ pre ++ post := by
      intro x hx
      have hx_in := hsub x (by simp [hx])
      rcases List.mem_append.mp hx_in with hpre | hpost
      · exact List.mem_append_left post hpre
      · rcases List.mem_cons.mp hpost with rfl | hpost'
        · exact absurd hx hnot
        · exact List.mem_append_right pre hpost'
    have hlen' : cs.length = (pre ++ post).length := by
      simp only [List.length_cons, List.length_append] at hlen ⊢
      omega
    exact ((ih hnd' hlen' hsub').cons c).trans (perm_cons_append c pre post)
theorem det_ne_zero_of_rowIndep {I : Type} (rows : List (I -> Int)) (cols : List I)
    (hlen : rows.length = cols.length) (hind : GaussianElim.RowIndep rows cols) :
    Determinant.det rows cols ≠ 0 := by
  intro hzero
  obtain ⟨cs, hcs, hincl, hdet⟩ := GaussianElim.exists_cols_det_ne_zero rows cols hind
  have hnd : cs.Nodup := by
    by_contra h
    apply hdet
    have ht := det_transpose (fun (r : I -> Int) c => r c) rows cs hcs.symm
    simp only [List.map_id'] at ht
    rw [ht]
    exact det_map_eq_zero_of_not_nodup (fun c (r : I -> Int) => r c) cs rows h
  have hp : cs.Perm cols := perm_of_nodup_length_subset hnd (hcs.trans hlen) hincl
  have hperm := det_eq_zero_iff_of_perm_cols (fun (r : I -> Int) c => r c) rows cs cols hcs.symm hp
  simp only [List.map_id'] at hperm
  exact hdet (hperm.mpr hzero)
end DetTranspose
namespace Vandermonde
def seq : Nat -> Nat -> List Nat
  | _, 0 => []
  | a, n + 1 => a :: seq (a + 1) n
@[simp] theorem length_seq (a n : Nat) : (seq a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [seq, ih]
theorem seq_succ_append (a n : Nat) : seq a (n + 1) = seq a n ++ [a + n] := by
  induction n generalizing a with
  | zero => simp [seq]
  | succ n ih =>
    rw [seq, ih (a + 1), seq, List.cons_append]
    have : a + 1 + n = a + (n + 1) := by omega
    rw [this]
theorem seq_zero_eq_range (n : Nat) : seq 0 n = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [seq_succ_append, ih, List.range_succ, Nat.zero_add]
theorem linComb_seq_pow (n : Nat) (ws : List Int) (a : Nat) (x : Int) (hlen : ws.length = n) :
    GaussianElim.linComb ((seq a n).map (fun k x => x ^ k)) ws x =
      x ^ a * Poly.eval ws x := by
  induction n generalizing ws a with
  | zero =>
    cases ws with
    | nil => simp [seq, GaussianElim.linComb, Poly.eval]
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [seq, List.map_cons, GaussianElim.linComb, Poly.eval]
      rw [ih ws (a + 1) (by simpa using hlen), pow_succ]
      ring
theorem det_vandermonde_ne_zero (qs : List Int) (hnd : qs.Nodup) :
    Determinant.det ((List.range qs.length).map (fun k x => x ^ k)) qs ≠ 0 := by
  apply DetTranspose.det_ne_zero_of_rowIndep
  · simp
  · intro ws hlen hz
    simp only [List.length_map, List.length_range] at hlen
    apply Poly.forall_zero_of_nodup_roots ws qs hnd
    · intro x hx
      have hzx := hz x hx
      rw [<- seq_zero_eq_range, linComb_seq_pow qs.length ws 0 x hlen] at hzx
      simpa using hzx
    · omega
theorem det_vandermonde_transpose_ne_zero (qs : List Int) (hnd : qs.Nodup) :
    Determinant.det (qs.map (fun q a => q ^ a)) (List.range qs.length) ≠ 0 := by
  rw [DetTranspose.det_transpose (fun q a => q ^ a) qs (List.range qs.length) (by simp)]
  exact det_vandermonde_ne_zero qs hnd
end Vandermonde
namespace ExpPoly
theorem det_map_row_scale {I J : Type} (f : J -> I -> Int) (a : J -> Int) (rs : List J) (cols : List
    I) :
    Determinant.det (rs.map (fun r c => a r * f r c)) cols =
      Determinant.listProd (rs.map a) * Determinant.det (rs.map f) cols := by
  induction rs generalizing cols with
  | nil => simp [Determinant.det, Determinant.listProd]
  | cons r rs ih =>
    simp only [List.map_cons, Determinant.listProd, Determinant.det, <- Determinant.lap_smul]
    apply Determinant.lap_congr
    intro c cs
    rw [ih]; ring
theorem listProd_ne_zero (xs : List Int) (h : ∀ x ∈ xs, x ≠ 0) : Determinant.listProd xs ≠ 0 := by
  induction xs with
  | nil => simp [Determinant.listProd]
  | cons x xs ih =>
    simp only [Determinant.listProd]
    exact mul_ne_zero (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
structure ExpTerm where
  base : Int
  order : Nat
  polynomial : List Int
def lc (t : ExpTerm) : Int := Poly.coeff t.polynomial t.order
def ValidExpTerm (t : ExpTerm) : Prop := t.polynomial.length ≤ t.order + 1 /\ lc t ≠ 0
def rows (ts : List ExpTerm) : List (Nat × (Nat -> List Int)) :=
  ts.map (fun t => (t.order, fun a => Poly.smul (t.base ^ a) (Poly.shift t.polynomial (a : Int))))
def cols (ts : List ExpTerm) : List Nat := List.range ts.length
def H (ts : List ExpTerm) : List Int := PolyDet.polyDet (rows ts) (cols ts)
def totalDeg (ts : List ExpTerm) : Nat := PolyDet.totalDeg (rows ts)
theorem degBounded_rows (ts : List ExpTerm) (hg : ∀ t ∈ ts, ValidExpTerm t) :
    PolyDet.DegBounded (rows ts) := by
  intro p hp a
  rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
  obtain ⟨hlen, _⟩ := hg t ht
  simp only [Poly.length_smul]
  exact Nat.le_trans (Poly.length_shift_le t.polynomial (a : Int)) hlen
theorem coeff_H_totalDeg_ne_zero (ts : List ExpTerm) (hnd : (ts.map ExpTerm.base).Nodup) (hg : ∀ t ∈
    ts, ValidExpTerm t) :
    Poly.coeff (H ts) (totalDeg ts) ≠ 0 := by
  unfold H totalDeg
  rw [PolyDet.coeff_polyDet_totalDeg (rows ts) (degBounded_rows ts hg) (cols ts)]
  unfold rows
  rw [List.map_map]
  rw [Determinant.det_congr_cols _ (ts.map (fun t a => lc t * t.base ^ a)) (cols ts)]
  · rw [det_map_row_scale (fun t a => t.base ^ a) lc ts (cols ts)]
    intro heq
    rcases mul_eq_zero.mp heq with h1 | h2
    · apply listProd_ne_zero (ts.map lc) _ h1
      intro x hx
      rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
      exact (hg t ht).2
    · have hv := Vandermonde.det_vandermonde_transpose_ne_zero (ts.map ExpTerm.base) hnd
      simp only [List.map_map, List.length_map] at hv
      exact hv h2
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr ?_
    intro t ht a _
    obtain ⟨hlen, _⟩ := hg t ht
    simp only [Function.comp_apply, Poly.coeff_smul, Poly.coeff_shift_top _ _ _ hlen]
    unfold lc; ring
theorem roots_length_le_totalDeg (ts : List ExpTerm) (roots : List Int)
    (hnd : (ts.map ExpTerm.base).Nodup)
    (hg : ∀ t ∈ ts, ValidExpTerm t)
    (hr : roots.Nodup)
    (hz : ∀ x ∈ roots, Poly.eval (H ts) x = 0) :
    roots.length ≤ totalDeg ts := by
  by_contra hgt
  push Not at hgt
  apply coeff_H_totalDeg_ne_zero ts hnd hg
  have hp : ∀ a ∈ H ts, a = 0 := by
    apply Poly.forall_zero_of_nodup_roots (H ts) roots hr hz
    have hlen := PolyDet.length_polyDet_le (rows ts) (degBounded_rows ts hg) (cols ts)
    unfold H totalDeg at *
    omega
  exact Poly.coeff_eq_zero_of_forall_zero (H ts) (totalDeg ts) hp
end ExpPoly
namespace GrowthBounds
theorem succ_pow_le_mul_pow (a b p c : Nat) (hb : 0 < b) (hba : b ≤ a)
    (hbase : (b + 1) ^ p ≤ c * b ^ p) :
    (a + 1) ^ p ≤ c * a ^ p := by
  have h1 : b * (a + 1) ≤ (b + 1) * a := by nlinarith
  have h2 : (b * (a + 1)) ^ p ≤ ((b + 1) * a) ^ p := Nat.pow_le_pow_left h1 p
  rw [Nat.mul_pow, Nat.mul_pow] at h2
  have h3 : (b + 1) ^ p * a ^ p ≤ (c * b ^ p) * a ^ p := Nat.mul_le_mul_right (a ^ p) hbase
  have h4 : b ^ p * (a + 1) ^ p ≤ b ^ p * (c * a ^ p) := by linarith
  have hbp : 0 < b ^ p := by positivity
  exact Nat.le_of_mul_le_mul_left h4 hbp
theorem two_pow_22_mul_pow_6_lt (m : Nat) (hm : 59 ≤ m) : 2 ^ 22 * m ^ 6 < 2 ^ (m - 1) := by
  have h : ∀ i : Nat, 2 ^ 22 * (59 + i) ^ 6 < 2 ^ (58 + i) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
      have hr : (59 + i + 1) ^ 6 ≤ 2 * (59 + i) ^ 6 :=
        succ_pow_le_mul_pow (59 + i) 16 6 2 (by omega) (by omega) (by decide)
      have hmul : 2 ^ 22 * (59 + (i + 1)) ^ 6 ≤ 2 * (2 ^ 22 * (59 + i) ^ 6) := by
        have : 59 + (i + 1) = 59 + i + 1 := by omega
        rw [this]
        nlinarith
      have hpow : 2 ^ (58 + (i + 1)) = 2 * 2 ^ (58 + i) := by
        have : 58 + (i + 1) = (58 + i) + 1 := by omega
        rw [this, Nat.pow_succ]
        ring
      omega
  have hspec := h (m - 59)
  have hm1 : 59 + (m - 59) = m := by omega
  have hm2 : 58 + (m - 59) = m - 1 := by omega
  rw [hm1, hm2] at hspec
  exact hspec
theorem cube_sq_lt_of_two_pow_le (m n : Nat) (hm : 59 ≤ m) (hn : 2 ^ (m - 1) ≤ n) :
    (2048 * m ^ 3) ^ 2 < n := by
  have h1 := two_pow_22_mul_pow_6_lt m hm
  have h2 : (2048 * m ^ 3) ^ 2 = 2 ^ 22 * m ^ 6 := by ring
  omega
theorem archimedean_lt_padic_exp (m : Nat) (hm : 2 ≤ m) :
    (2048 * m ^ 3) * (1664 * m ^ 3 + m) <
      (2048 * m ^ 3) * (2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2)) := by
  have hpos : 0 < 2048 * m ^ 3 := by positivity
  apply Nat.mul_lt_mul_of_pos_left _ hpos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : 1664 * (k + 2) ^ 3 + (k + 2) + 1 + 2 * (256 * (k + 2) ^ 2) < 2048 * (k + 2) ^ 3 := by
    nlinarith
  omega
end GrowthBounds
namespace SmallModuli
def F (n : Nat) : Int := 2 * (3 : Int) ^ n + (n : Int) + 5
theorem two_pow_pos (a : Nat) : (0 : Int) < (2 : Int) ^ a := by positivity
theorem dvd_sub_iff_emod_eq (m x y : Int) (_hm : 0 < m) : (m ∣ (x - y)) <-> x % m = y % m := by
  constructor
  · rintro ⟨q, hq⟩
    have hx : x = y + m * q := by linarith
    rw [hx, Int.add_mul_emod_self_left]
  · intro h
    refine ⟨x / m - y / m, ?_⟩
    have h1 := Int.mul_ediv_add_emod x m
    have h2 := Int.mul_ediv_add_emod y m
    linarith
theorem pow_dvd_pow_of_le (a b : Nat) (h : a ≤ b) : ((2 : Int) ^ a) ∣ ((2 : Int) ^ b) := by
  refine ⟨(2 : Int) ^ (b - a), ?_⟩
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  conv_lhs => rw [hb]
  rw [pow_add]
theorem three_pow_two_pow_lift (a : Nat) : ∃ t : Int, (3 : Int) ^ (2 ^ a) = 1 + (2 : Int) ^ (a + 1)
    * t := by
  induction a with
  | zero => exact ⟨1, by decide⟩
  | succ a ih =>
    rcases ih with ⟨t, ht⟩
    refine ⟨t + (2 : Int) ^ a * t * t, ?_⟩
    have hpow : 2 ^ (a + 1) = 2 ^ a * 2 := by rw [Nat.pow_succ]
    rw [hpow, pow_mul, ht]
    have h2 : (2 : Int) ^ (a + 1 + 1) = (2 : Int) ^ (a + 1) * 2 := by rw [pow_succ]
    have h3 : (2 : Int) ^ (a + 1) = (2 : Int) ^ a * 2 := by rw [pow_succ]
    rw [h2, h3]
    ring
theorem sub_one_dvd_pow_sub_one (A : Int) (w : Nat) : (A - 1) ∣ (A ^ w - 1) := by
  induction w with
  | zero => exact ⟨0, by ring⟩
  | succ w ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨A * k + 1, ?_⟩
    calc A ^ (w + 1) - 1
        = A * (A ^ w - 1) + (A - 1) := by ring
      _ = A * ((A - 1) * k) + (A - 1) := by rw [hk]
      _ = (A - 1) * (A * k + 1) := by ring
theorem two_pow_succ_dvd_three_pow_sub_le (a x y : Nat) (hxy : y ≤ x)
    (hdvd : ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int))) :
    ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ x - (3 : Int) ^ y) := by
  have hdvd_nat : 2 ^ a ∣ (x - y) := by
    have h1 : ((x - y : Nat) : Int) = (x : Int) - (y : Int) := Int.ofNat_sub hxy
    rw [<- h1] at hdvd
    exact Int.ofNat_dvd.mp hdvd
  rcases hdvd_nat with ⟨w, hw⟩
  have hx : x = y + 2 ^ a * w := by omega
  rcases three_pow_two_pow_lift a with ⟨t, ht⟩
  have hd1 : ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ (2 ^ a) - 1) := ⟨t, by linarith⟩
  have hd2 : ((3 : Int) ^ (2 ^ a) - 1) ∣ (((3 : Int) ^ (2 ^ a)) ^ w - 1) :=
    sub_one_dvd_pow_sub_one ((3 : Int) ^ (2 ^ a)) w
  have hd3 : ((2 : Int) ^ (a + 1)) ∣ (((3 : Int) ^ (2 ^ a)) ^ w - 1) := dvd_trans hd1 hd2
  rcases hd3 with ⟨u, hu⟩
  refine ⟨(3 : Int) ^ y * u, ?_⟩
  calc (3 : Int) ^ x - (3 : Int) ^ y
      = (3 : Int) ^ (y + 2 ^ a * w) - (3 : Int) ^ y := by rw [hx]
    _ = (3 : Int) ^ y * (((3 : Int) ^ (2 ^ a)) ^ w - 1) := by rw [pow_add, pow_mul]; ring
    _ = (3 : Int) ^ y * ((2 : Int) ^ (a + 1) * u) := by rw [hu]
    _ = (2 : Int) ^ (a + 1) * ((3 : Int) ^ y * u) := by ring
theorem two_pow_succ_dvd_three_pow_sub (a x y : Nat)
    (hdvd : ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int))) :
    ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ x - (3 : Int) ^ y) := by
  by_cases hxy : y ≤ x
  · exact two_pow_succ_dvd_three_pow_sub_le a x y hxy hdvd
  · push Not at hxy
    have hdvd' : ((2 : Int) ^ a) ∣ ((y : Int) - (x : Int)) := by
      rcases hdvd with ⟨w, hw⟩
      exact ⟨-w, by linarith⟩
    rcases two_pow_succ_dvd_three_pow_sub_le a y x (by omega) hdvd' with ⟨v, hv⟩
    exact ⟨-v, by linarith⟩
theorem two_pow_dvd_sub_of_dvd_F_sub (a x y : Nat)
    (h : ((2 : Int) ^ a) ∣ (F x - F y)) :
    ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int)) := by
  induction a with
  | zero => exact ⟨(x : Int) - (y : Int), by ring⟩
  | succ a ih =>
    have hlow : ((2 : Int) ^ a) ∣ (F x - F y) := by
      rcases h with ⟨w, hw⟩
      exact ⟨2 * w, by rw [pow_succ] at hw; linarith⟩
    rcases two_pow_succ_dvd_three_pow_sub a x y (ih hlow) with ⟨v, hv⟩
    rcases h with ⟨w, hw⟩
    refine ⟨w - 2 * v, ?_⟩
    have hp2 : (2 : Int) ^ (a + 1) = (2 : Int) ^ a * 2 := by rw [pow_succ]
    unfold F at hw
    linarith
def powMod : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, m => 1 % m
  | k + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      if e % 2 = 0 then ((powMod k b (e / 2) m) * (powMod k b (e / 2) m)) % m
      else (b * (((powMod k b (e / 2) m) * (powMod k b (e / 2) m)) % m)) % m
theorem powMod_eq_pow_mod (k b e m : Nat) (he : e < 2 ^ k) :
    powMod k b e m = (b ^ e) % m := by
  induction k generalizing e with
  | zero =>
    have he0 : e = 0 := by omega
    subst he0
    simp [powMod]
  | succ k ih =>
    unfold powMod
    split_ifs with he0 hmod
    · subst he0; simp
    · have he2 : e / 2 < 2 ^ k := by rw [Nat.pow_succ] at he; omega
      rw [ih (e / 2) he2, <- Nat.mul_mod]
      have he_eq : e = (e / 2) + (e / 2) := by omega
      conv_rhs => rw [he_eq, Nat.pow_add]
    · have he2 : e / 2 < 2 ^ k := by rw [Nat.pow_succ] at he; omega
      rw [ih (e / 2) he2, <- Nat.mul_mod, Nat.mul_mod b, Nat.mod_mod, <- Nat.mul_mod]
      have he_eq : e = 1 + ((e / 2) + (e / 2)) := by omega
      conv_rhs => rw [he_eq, Nat.pow_add, Nat.pow_one, Nat.pow_add]
theorem two_pow_dvd_F_of_powMod (r q a k : Nat)
    (he : r < 2 ^ k)
    (hpow : powMod k 3 r (2 ^ a) = q)
    (hroot : 2 * q + r + 5 = 2 * 2 ^ a) :
    ((2 : Int) ^ a) ∣ F r := by
  have h1 : (3 ^ r) % (2 ^ a) = q := by
    rw [<- powMod_eq_pow_mod k 3 r (2 ^ a) he]
    exact hpow
  have h2 : (2 * 3 ^ r + r + 5) % (2 ^ a) = 0 := by
    have hdiv := Nat.div_add_mod (3 ^ r) (2 ^ a)
    have h3 : 2 * 3 ^ r + r + 5 = 2 ^ a * (2 * (3 ^ r / 2 ^ a) + 2) := by linarith
    rw [h3, Nat.mul_mod_right]
  have hdvd : 2 ^ a ∣ (2 * 3 ^ r + r + 5) := Nat.dvd_of_mod_eq_zero h2
  have hF : F r = ((2 * 3 ^ r + r + 5 : Nat) : Int) := by
    unfold F; push_cast; ring
  rw [hF]
  exact Int.ofNat_dvd.mpr hdvd
theorem two_pow_8_dvd_F_149 : ((2 : Int) ^ 8) ∣ F 149 :=
  two_pow_dvd_F_of_powMod 149 179 8 8 (by decide) (by decide) (by decide)
set_option maxRecDepth 200000 in
theorem two_pow_64_dvd_F_root : ((2 : Int) ^ 64) ∣ F 767351889479380629 :=
  two_pow_dvd_F_of_powMod 767351889479380629 18063068128969861299 64 60 (by decide) (by decide) (by
    decide)
theorem mod_two_pow_eq_of_dvd_F (a n r : Nat) (hroot : ((2 : Int) ^ a) ∣ F r)
    (hn : ((2 : Int) ^ a) ∣ F n) :
    n % (2 ^ a) = r % (2 ^ a) := by
  have hsub : ((2 : Int) ^ a) ∣ (F n - F r) := Int.dvd_sub hn hroot
  have hinj : ((2 : Int) ^ a) ∣ ((n : Int) - (r : Int)) := two_pow_dvd_sub_of_dvd_F_sub a n r hsub
  have hmod := (dvd_sub_iff_emod_eq ((2 : Int) ^ a) (n : Int) (r : Int) (two_pow_pos a)).mp hinj
  exact_mod_cast hmod
theorem not_two_pow_succ_dvd_F_small (n : Nat) (hn1 : 7 ≤ n) (hn2 : n < 2 ^ 58) :
    ¬ (((2 : Int) ^ (n + 1)) ∣ F n) := by
  intro hbad
  by_cases hsmall : n < 64
  · have h8 : ((2 : Int) ^ 8) ∣ F n :=
      dvd_trans (pow_dvd_pow_of_le 8 (n + 1) (by omega)) hbad
    have hu := mod_two_pow_eq_of_dvd_F 8 n 149 two_pow_8_dvd_F_149 h8
    have h1 : n % (2 ^ 8) = n := Nat.mod_eq_of_lt (by omega)
    have h2 : 149 % (2 ^ 8) = 149 := by decide
    omega
  · have h64 : ((2 : Int) ^ 64) ∣ F n :=
      dvd_trans (pow_dvd_pow_of_le 64 (n + 1) (by omega)) hbad
    have hu := mod_two_pow_eq_of_dvd_F 64 n 767351889479380629 two_pow_64_dvd_F_root h64
    have hcut1 : 2 ^ 58 < 767351889479380629 := by decide
    have hcut2 : 767351889479380629 < 2 ^ 64 := by decide
    have h1 : n % (2 ^ 64) = n := Nat.mod_eq_of_lt (by omega)
    have h2 : 767351889479380629 % (2 ^ 64) = 767351889479380629 := Nat.mod_eq_of_lt hcut2
    omega
def large_exclusion : Prop :=
  ∀ n u : Nat, 2 ^ 58 ≤ n -> 1 ≤ u /\ u ≤ n -> ¬ (((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - (u : Int)))
theorem not_two_pow_succ_dvd_F (hlarge : large_exclusion) (n : Nat) (hn : 7 ≤ n) :
    ¬ (((2 : Int) ^ (n + 1)) ∣ F n) := by
  intro hbad
  by_cases hsmall : n < 2 ^ 58
  · exact not_two_pow_succ_dvd_F_small n hn hsmall hbad
  · push Not at hsmall
    have htwo : (2 : Int) ∣ F n := by
      have h1 : ((2 : Int) ^ 1) ∣ F n := dvd_trans (pow_dvd_pow_of_le 1 (n + 1) (by omega)) hbad
      simpa using h1
    rcases htwo with ⟨w, hw⟩
    have hodd : n % 2 = 1 := by
      have h3 : (2 * (3 : Int) ^ n + (n : Int) + 5) % 2 = 0 := by
        unfold F at hw
        omega
      omega
    have hhalf : 2 * ((n + 5) / 2) = n + 5 := by omega
    apply hlarge n ((n + 5) / 2) hsmall ⟨by omega, by omega⟩
    have hopp : (-3 : Int) ^ n = -((3 : Int) ^ n) := by
      obtain ⟨k, hk⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
      have hsq : (-3 : Int) ^ (2 * k) = (3 : Int) ^ (2 * k) := by
        rw [pow_mul, pow_mul]
        have : (-3 : Int) ^ 2 = (3 : Int) ^ 2 := by decide
        rw [this]
      rw [hk, pow_add, pow_one, hsq, pow_add, pow_one]
      ring
    rw [hopp]
    rcases hbad with ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    have h2 : (2 : Int) ^ (n + 1) = 2 * (2 : Int) ^ n := by rw [pow_succ]; ring
    unfold F at hq
    rw [h2] at hq
    have hhalf_int : 2 * (((n + 5) / 2 : Nat) : Int) = (n : Int) + 5 := by exact_mod_cast hhalf
    linarith
end SmallModuli
namespace GridPoints
open Poly
def trimPoly : List Int -> List Int
  | [] => []
  | a :: p =>
    match trimPoly p with
    | [] => if a = 0 then [] else [a]
    | q => a :: q
theorem trimPoly_spec (p : List Int) :
    (trimPoly p).length ≤ p.length /\
    (∀ x, Poly.eval (trimPoly p) x = Poly.eval p x) /\
    (trimPoly p = [] \/ coeff (trimPoly p) ((trimPoly p).length - 1) ≠ 0) := by
  induction p with
  | nil =>
    simp [trimPoly, Poly.eval]
  | cons a p ih =>
    rcases ih with ⟨hlen, he, hlc⟩
    simp only [trimPoly]
    cases hp : trimPoly p with
    | nil =>
      by_cases ha : a = 0
      · refine ⟨by simp [ha], ?_, Or.inl (by simp [ha])⟩
        intro x
        have hpx := he x
        rw [hp] at hpx
        simp [Poly.eval, ha, <- hpx]
      · refine ⟨by simp [ha], ?_, Or.inr (by simp [coeff, ha])⟩
        intro x
        have hpx := he x
        rw [hp] at hpx
        simp [Poly.eval, ha, <- hpx]
    | cons b q =>
      rw [hp] at hlen hlc
      simp only [List.length_cons] at hlen ⊢
      refine ⟨by omega, ?_, Or.inr ?_⟩
      · intro x
        have hpx := he x
        rw [hp] at hpx
        change a + x * Poly.eval (b :: q) x = a + x * Poly.eval p x
        rw [hpx]
      · rcases hlc with hnil | hlc
        · nomatch hnil
        · simpa [coeff] using hlc
theorem forall_zero_of_trimPoly_nil (p : List Int) (h : trimPoly p = []) : ∀ a ∈ p, a = 0 := by
  induction p with
  | nil => intro a ha; nomatch ha
  | cons a p ih =>
    simp only [trimPoly] at h
    cases hp : trimPoly p with
    | nil =>
      rw [hp] at h
      by_cases ha : a = 0
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact ih hp x hx
      · simp [ha] at h
    | cons b q =>
      rw [hp] at h
      nomatch h
def gridX (n : Nat) (rs : Nat × Nat) : Int :=
  (rs.1 : Int) + (n : Int) * (rs.2 : Int)
def gridRect (R : Nat) : Nat -> List (Nat × Nat)
  | 0 => []
  | s + 1 => gridRect R s ++ (List.range R).map (fun r => (r, s))
theorem length_gridRect (R S : Nat) : (gridRect R S).length = R * S := by
  induction S with
  | zero => simp [gridRect]
  | succ s ih =>
    simp [gridRect, ih, Nat.mul_succ]
theorem mem_gridRect_iff (R S r s : Nat) : (r, s) ∈ gridRect R S <-> r < R /\ s < S := by
  induction S with
  | zero => simp [gridRect]
  | succ S ih =>
    simp only [gridRect, List.mem_append, ih, List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨hr, hs⟩ | ⟨r', hr', rfl, rfl⟩)
      · exact ⟨hr, by omega⟩
      · exact ⟨hr', by omega⟩
    · rintro ⟨hr, hs⟩
      by_cases h : s = S
      · subst h
        exact Or.inr ⟨r, hr, rfl, rfl⟩
      · exact Or.inl ⟨hr, by omega⟩
theorem nodup_map_of_injOn {A B : Type} (f : A -> B) (xs : List A) (hnd : xs.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y -> x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd'⟩
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd' (fun u hu v hv h => hinj u (List.mem_cons_of_mem _ hu) v
      (List.mem_cons_of_mem _ hv) h)⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    have hyx : y = x := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy
    subst hyx
    exact hnot hy
theorem nodup_append_of_disjoint {A : Type} (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup)
    (hdis : ∀ x ∈ xs, x ∉ ys) : (xs ++ ys).Nodup := by
  induction xs with
  | nil => exact hy
  | cons x xs ih =>
    rcases List.nodup_cons.mp hx with ⟨hnot, hx'⟩
    rw [List.cons_append, List.nodup_cons]
    refine ⟨?_, ih hx' (fun y hy' => hdis y (List.mem_cons_of_mem _ hy'))⟩
    rw [List.mem_append]
    rintro (h1 | h2)
    · exact hnot h1
    · exact hdis x List.mem_cons_self h2
theorem gridX_inj (n R r s r' s' : Nat) (hn : R ≤ n) (hr : r < R) (hr' : r' < R)
    (he : gridX n (r, s) = gridX n (r', s')) : r = r' /\ s = s' := by
  unfold gridX at he
  dsimp -failIfUnchanged at he
  have hss : s = s' := by
    rcases lt_trichotomy s s' with hlt | rfl | hgt
    · exfalso
      have h1 : (s + 1 : Int) ≤ (s' : Int) := by omega
      have h2 : (n : Int) * (s + 1 : Int) ≤ (n : Int) * (s' : Int) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith
    · rfl
    · exfalso
      have h1 : (s' + 1 : Int) ≤ (s : Int) := by omega
      have h2 : (n : Int) * (s' + 1 : Int) ≤ (n : Int) * (s : Int) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      nlinarith
  subst hss
  exact ⟨by omega, rfl⟩
theorem nodup_map_gridX (n R S : Nat) (hn : R ≤ n) : ((gridRect R S).map (gridX n)).Nodup := by
  induction S with
  | zero => simp [gridRect]
  | succ S ih =>
    simp only [gridRect, List.map_append, List.map_map]
    apply nodup_append_of_disjoint _ _ ih
    · apply nodup_map_of_injOn _ _ List.nodup_range
      intro r hr r' hr' he
      simp only [Function.comp_apply, gridX] at he
      omega
    · intro x hx hy
      rcases List.mem_map.mp hx with ⟨⟨r, s⟩, hrs, rfl⟩
      rcases List.mem_map.mp hy with ⟨r', hr', he⟩
      simp only [Function.comp_apply] at he
      rw [mem_gridRect_iff] at hrs
      rw [List.mem_range] at hr'
      have ⟨_, hss⟩ := gridX_inj n R r s r' S hn hrs.1 hr' he.symm
      omega
end GridPoints
namespace LaurentPoly
open Poly GridPoints
abbrev LaurentTerm := Nat × List Int
def negThreePow (l : Nat) : Int := (-3 : Int) ^ l
def evalLaurent : List LaurentTerm -> Int -> Int -> Int
  | [], _, _ => 0
  | (l, p) :: ts, x, y => Poly.eval p x * y ^ l + evalLaurent ts x y
def trimLaurent : List LaurentTerm -> List LaurentTerm
  | [] => []
  | (l, p) :: ts =>
    match trimPoly p with
    | [] => trimLaurent ts
    | q => (l, q) :: trimLaurent ts
def toExpTerm (t : LaurentTerm) : ExpPoly.ExpTerm :=
  ⟨negThreePow t.1, t.2.length - 1, t.2⟩
theorem evalLaurent_trimLaurent (ts : List LaurentTerm) (x y : Int) : evalLaurent (trimLaurent ts) x
    y = evalLaurent ts x y := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    rcases trimPoly_spec p with ⟨_, he, _⟩
    simp only [trimLaurent]
    cases hp : trimPoly p with
    | nil =>
      simp only [evalLaurent, ih]
      have hpx := he x
      rw [hp] at hpx
      simp [Poly.eval, <- hpx]
    | cons a q =>
      simp only [evalLaurent, ih]
      have hpx := he x
      rw [hp] at hpx
      rw [hpx]
theorem length_trimLaurent_le (ts : List LaurentTerm) : (trimLaurent ts).length ≤ ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    simp only [trimLaurent]
    cases trimPoly p <;> simp <;> omega
theorem forall_zero_of_trimLaurent_nil (ts : List LaurentTerm) (h : trimLaurent ts = []) :
    ∀ t ∈ ts, ∀ a ∈ t.2, a = 0 := by
  induction ts with
  | nil => intro t ht; nomatch ht
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    simp only [trimLaurent] at h
    cases hp : trimPoly p with
    | nil =>
      rw [hp] at h
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact forall_zero_of_trimPoly_nil p hp
      · exact ih h u hu
    | cons a q =>
      rw [hp] at h
      nomatch h
theorem mem_trimLaurent_iff (ts : List LaurentTerm) (l : Nat) (p : List Int) (h : (l, p) ∈
    trimLaurent ts) :
    ∃ q, (l, q) ∈ ts /\ p = trimPoly q /\ p ≠ [] := by
  induction ts with
  | nil => nomatch h
  | cons t ts ih =>
    rcases t with ⟨a, q⟩
    simp only [trimLaurent] at h
    cases hq : trimPoly q with
    | nil =>
      rw [hq] at h
      rcases ih h with ⟨p', hi, hp⟩
      exact ⟨p', List.mem_cons_of_mem _ hi, hp⟩
    | cons b qs =>
      rw [hq] at h
      rcases List.mem_cons.mp h with heq | hi
      · injection heq with hl hp
        subst hl hp
        exact ⟨q, List.mem_cons_self, hq.symm, by simp⟩
      · rcases ih hi with ⟨p', hj, hp⟩
        exact ⟨p', List.mem_cons_of_mem _ hj, hp⟩
theorem validExpTerm_of_mem_trimLaurent (ts : List LaurentTerm) : ∀ t ∈ (trimLaurent ts).map
    toExpTerm, ExpPoly.ValidExpTerm t := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨⟨l, p⟩, hp, rfl⟩
  rcases mem_trimLaurent_iff ts l p hp with ⟨q, _, rfl, hne⟩
  rcases trimPoly_spec q with ⟨_, _, hlc⟩
  unfold ExpPoly.ValidExpTerm ExpPoly.lc toExpTerm
  dsimp -failIfUnchanged
  refine ⟨by omega, ?_⟩
  rcases hlc with hnil | hlc
  · exact absurd hnil hne
  · exact hlc
theorem length_le_of_mem_trimLaurent (ts : List LaurentTerm) (K : Nat) (h : ∀ t ∈ ts, t.2.length ≤
    K) :
    ∀ t ∈ trimLaurent ts, t.2.length ≤ K := by
  rintro ⟨l, p⟩ hp
  rcases mem_trimLaurent_iff ts l p hp with ⟨q, hq, rfl, _⟩
  have h1 := h (l, q) hq
  have h2 := (trimPoly_spec q).1
  dsimp -failIfUnchanged at h1 ⊢
  omega
theorem fst_mem_of_mem_trimLaurent (ts : List LaurentTerm) :
    ∀ l ∈ (trimLaurent ts).map Prod.fst, l ∈ ts.map Prod.fst := by
  intro l hl
  rcases List.mem_map.mp hl with ⟨⟨l', p⟩, hp, rfl⟩
  rcases mem_trimLaurent_iff ts l' p hp with ⟨q, hq, _⟩
  exact List.mem_map.mpr ⟨(l', q), hq, rfl⟩
theorem nodup_fst_trimLaurent (ts : List LaurentTerm) (h : (ts.map Prod.fst).Nodup) :
    ((trimLaurent ts).map Prod.fst).Nodup := by
  induction ts with
  | nil => simp [trimLaurent]
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    rw [List.map_cons, List.nodup_cons] at h
    rcases h with ⟨hnot, hnd⟩
    simp only [trimLaurent]
    cases trimPoly p with
    | nil => exact ih hnd
    | cons a q =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hi => hnot (fst_mem_of_mem_trimLaurent ts l hi), ih hnd⟩
theorem negThreePow_inj (l k : Nat) (he : negThreePow l = negThreePow k) : l = k := by
  unfold negThreePow at he
  have habs : ((-3 : Int) ^ l).natAbs = ((-3 : Int) ^ k).natAbs := congrArg Int.natAbs he
  rw [Int.natAbs_pow, Int.natAbs_pow] at habs
  change 3 ^ l = 3 ^ k at habs
  rcases lt_trichotomy l k with h | rfl | h
  · exfalso
    have := Nat.pow_lt_pow_right (by decide : 1 < 3) h
    omega
  · rfl
  · exfalso
    have := Nat.pow_lt_pow_right (by decide : 1 < 3) h
    omega
theorem nodup_base_map_toExpTerm (ts : List LaurentTerm) (h : (ts.map Prod.fst).Nodup) :
    ((ts.map toExpTerm).map ExpPoly.ExpTerm.base).Nodup := by
  have hmap : (ts.map toExpTerm).map ExpPoly.ExpTerm.base = (ts.map Prod.fst).map negThreePow := by
    induction ts <;> simp [toExpTerm, *]
  rw [hmap]
  exact nodup_map_of_injOn negThreePow (ts.map Prod.fst) h (fun x _ y _ he => negThreePow_inj x y
    he)
theorem totalDeg_map_toExpTerm_le (ts : List LaurentTerm) (K : Nat) (h : ∀ t ∈ ts, t.2.length ≤ K) :
    ExpPoly.totalDeg (ts.map toExpTerm) ≤ (K - 1) * ts.length := by
  induction ts with
  | nil => simp [ExpPoly.totalDeg, ExpPoly.rows, PolyDet.totalDeg]
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    have hp : p.length ≤ K := h (l, p) List.mem_cons_self
    have hts : ∀ u ∈ ts, u.2.length ≤ K := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have ih' := ih hts
    unfold ExpPoly.totalDeg ExpPoly.rows at ih' ⊢
    simp only [List.map_cons, PolyDet.totalDeg, toExpTerm, List.length_cons]
    rw [Nat.mul_succ]
    omega
def gridY (u : Int) (rs : Nat × Nat) : Int :=
  (-3 : Int) ^ rs.1 * u ^ rs.2
def laurentRowFns (ts : List LaurentTerm) (x : Int) : List (Nat -> Int) :=
  ts.map (fun t a => (negThreePow t.1) ^ a * Poly.eval t.2 (x + (a : Int)))
def laurentWeights (ts : List LaurentTerm) (y : Int) : List Int :=
  ts.map (fun t => y ^ t.1)
theorem gridY_ne_zero (u : Int) (rs : Nat × Nat) (hu : u ≠ 0) : gridY u rs ≠ 0 := by
  unfold gridY
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hu)
theorem negThreePow_pow_comm (l a : Nat) : (negThreePow l) ^ a = ((-3 : Int) ^ a) ^ l := by
  unfold negThreePow
  rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
theorem linComb_laurentRowFns (ts : List LaurentTerm) (x y : Int) (a : Nat) :
    GaussianElim.linComb (laurentRowFns ts x) (laurentWeights ts y) a =
      evalLaurent ts (x + (a : Int)) ((-3 : Int) ^ a * y) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    unfold laurentRowFns laurentWeights
    rw [List.map_cons, List.map_cons]
    simp only [GaussianElim.linComb, evalLaurent]
    change y ^ l * (negThreePow l ^ a * Poly.eval p (x + ↑a)) +
      GaussianElim.linComb (laurentRowFns ts x) (laurentWeights ts y) a = _
    rw [ih, mul_pow, negThreePow_pow_comm]
    ring
theorem eval_H_eq_det_laurentRowFns (ts : List LaurentTerm) (x : Int) :
    Poly.eval (ExpPoly.H (ts.map toExpTerm)) x =
      Determinant.det (laurentRowFns ts x) (List.range ts.length) := by
  unfold ExpPoly.H ExpPoly.cols
  rw [List.length_map, PolyDet.eval_polyDet]
  unfold ExpPoly.rows laurentRowFns
  rw [List.map_map, List.map_map]
  generalize List.range ts.length = cs
  apply Determinant.det_congr_cols
  induction ts with
  | nil => exact List.Forall₂.nil
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    refine List.Forall₂.cons ?_ ih
    intro a _
    simp [toExpTerm, eval_smul, eval_shift]
theorem eval_H_eq_zero_of_evalLaurent_zero (ts : List LaurentTerm) (x y : Int) (hts : ts ≠ []) (hy :
    y ≠ 0)
    (hrel : ∀ a, a < ts.length -> evalLaurent ts (x + (a : Int)) ((-3 : Int) ^ a * y) = 0) :
    Poly.eval (ExpPoly.H (ts.map toExpTerm)) x = 0 := by
  rw [eval_H_eq_det_laurentRowFns]
  cases ts with
  | nil => contradiction
  | cons t ts =>
    rcases t with ⟨l, p⟩
    unfold laurentRowFns
    rw [List.map_cons]
    apply GaussianElim.det_cons_eq_zero_of_linComb_eq_zero _ _ (y ^ l) (laurentWeights ts y)
    · exact pow_ne_zero _ hy
    · intro a ha
      change GaussianElim.linComb (laurentRowFns ((l, p) :: ts) x) (laurentWeights ((l, p) :: ts) y)
        a = 0
      rw [linComb_laurentRowFns]
      apply hrel
      exact List.mem_range.mp ha
theorem gridX_shift_fst (n r s a : Nat) : gridX n (r + a, s) = gridX n (r, s) + (a : Int) := by
  unfold gridX
  dsimp -failIfUnchanged
  omega
theorem gridY_shift_fst (u : Int) (r s a : Nat) :
    gridY u (r + a, s) = (-3 : Int) ^ a * gridY u (r, s) := by
  unfold gridY
  dsimp -failIfUnchanged
  rw [pow_add]
  ring
theorem forall_zero_of_evalLaurent_grid_zero (K L n : Nat) (u : Int) (R0 S : Nat) (ts : List
    LaurentTerm)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hlength : ts.length ≤ L) (hu : u ≠ 0)
    (hnd : (ts.map Prod.fst).Nodup) (hbound : ∀ t ∈ ts, t.2.length ≤ K)
    (hz : ∀ r s, r < R0 + L - 1 -> s < S -> evalLaurent ts (gridX n (r, s)) (gridY u (r, s)) = 0) :
    ∀ t ∈ ts, ∀ a ∈ t.2, a = 0 := by
  cases hprep : trimLaurent ts with
  | nil => exact forall_zero_of_trimLaurent_nil ts hprep
  | cons t pts =>
    exfalso
    have hne : trimLaurent ts ≠ [] := by rw [hprep]; simp
    have hroots : ∀ x ∈ (gridRect R0 S).map (gridX n),
        Poly.eval (ExpPoly.H ((trimLaurent ts).map toExpTerm)) x = 0 := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨⟨r, s⟩, hrs, rfl⟩
      rw [mem_gridRect_iff] at hrs
      apply eval_H_eq_zero_of_evalLaurent_zero _ _ (gridY u (r, s)) hne (gridY_ne_zero u (r, s) hu)
      intro a ha
      rw [<- gridX_shift_fst, <- gridY_shift_fst, evalLaurent_trimLaurent]
      have hplen := length_trimLaurent_le ts
      exact hz (r + a) s (by omega) hrs.2
    have hcount := ExpPoly.roots_length_le_totalDeg ((trimLaurent ts).map toExpTerm) ((gridRect R0
      S).map (gridX n))
      (nodup_base_map_toExpTerm _ (nodup_fst_trimLaurent ts hnd)) (validExpTerm_of_mem_trimLaurent
        ts)
      (nodup_map_gridX n R0 S hn) hroots
    have hdegree := totalDeg_map_toExpTerm_le (trimLaurent ts) K (length_le_of_mem_trimLaurent ts K
      hbound)
    have hplen := length_trimLaurent_le ts
    rw [List.length_map, length_gridRect] at hcount
    have hmul : (K - 1) * (trimLaurent ts).length ≤ (K - 1) * L :=
      Nat.mul_le_mul_left (K - 1) (Nat.le_trans hplen hlength)
    omega
end LaurentPoly
namespace LaurentInterp
open Poly GaussianElim GridPoints LaurentPoly
def monomialGrid (K : Nat) : Nat -> Nat -> List (Nat × Nat)
  | _, 0 => []
  | a, len + 1 => (List.range K).map (fun k => (k, a)) ++ monomialGrid K (a + 1) len
def entry (n : Nat) (u : Int) (kl rs : Nat × Nat) : Int :=
  (gridX n rs) ^ kl.1 * (gridY u rs) ^ kl.2
def unflattenLaurent (K : Nat) : Nat -> Nat -> List Int -> List LaurentTerm
  | _, 0, _ => []
  | a, len + 1, ws => (a, ws.take K) :: unflattenLaurent K (a + 1) len (ws.drop K)
theorem length_monomialGrid (K a L : Nat) : (monomialGrid K a L).length = K * L := by
  induction L generalizing a with
  | zero => simp [monomialGrid]
  | succ L ih =>
    simp [monomialGrid, ih (a + 1), Nat.mul_succ, Nat.add_comm]
theorem mem_monomialGrid_iff (K L a k l : Nat) :
    (k, l) ∈ monomialGrid K a L <-> k < K /\ a ≤ l /\ l < a + L := by
  induction L generalizing a with
  | zero => simp [monomialGrid]
  | succ L ih =>
    simp only [monomialGrid, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq, ih (a +
      1)]
    constructor
    · rintro (⟨k', hk', rfl, rfl⟩ | ⟨hk, hl1, hl2⟩)
      · exact ⟨hk', by omega, by omega⟩
      · exact ⟨hk, by omega, by omega⟩
    · rintro ⟨hk, hl1, hl2⟩
      by_cases h : l = a
      · subst h
        exact Or.inl ⟨k, hk, rfl, rfl⟩
      · exact Or.inr ⟨hk, by omega, by omega⟩
theorem map_fst_unflattenLaurent (K a L : Nat) (ws : List Int) :
    (unflattenLaurent K a L ws).map Prod.fst = List.range' a L := by
  induction L generalizing a ws with
  | zero => rfl
  | succ L ih =>
    simp [unflattenLaurent, List.range', ih (a + 1) (ws.drop K)]
theorem length_unflattenLaurent (K a L : Nat) (ws : List Int) : (unflattenLaurent K a L ws).length =
    L := by
  have h := congrArg List.length (map_fst_unflattenLaurent K a L ws)
  simpa using h
theorem length_snd_unflattenLaurent_le (K a L : Nat) (ws : List Int) :
    ∀ t ∈ unflattenLaurent K a L ws, t.2.length ≤ K := by
  induction L generalizing a ws with
  | zero => intro t ht; nomatch ht
  | succ L ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · simp [List.length_take]
    · exact ih (a + 1) (ws.drop K) t ht
theorem forall_zero_of_unflattenLaurent_zero (K a L : Nat) (ws : List Int) (hlen : ws.length = K *
    L)
    (hz : ∀ t ∈ unflattenLaurent K a L ws, ∀ x ∈ t.2, x = 0) :
    ∀ x ∈ ws, x = 0 := by
  induction L generalizing a ws with
  | zero =>
    cases ws with
    | nil => intro x hx; nomatch hx
    | cons _ _ => nomatch hlen
  | succ L ih =>
    rw [<- List.take_append_drop K ws]
    intro x hx
    rcases List.mem_append.mp hx with htake | hdrop
    · exact hz (a, ws.take K) List.mem_cons_self x htake
    · apply ih (a + 1) (ws.drop K)
      · rw [List.length_drop, hlen, Nat.mul_succ]
        omega
      · intro t ht
        exact hz t (List.mem_cons_of_mem _ ht)
      · exact hdrop
theorem linComb_append {I : Type} (rs ss : List (I -> Int)) (ws : List Int) (c : I) :
    linComb (rs ++ ss) ws c =
      linComb rs (ws.take rs.length) c + linComb ss (ws.drop rs.length) c := by
  have hnil : ∀ qs : List (I -> Int), linComb qs [] c = 0 := by
    intro qs; cases qs <;> rfl
  induction rs generalizing ws with
  | nil => simp [linComb]
  | cons r rs ih =>
    cases ws with
    | nil => simp [hnil]
    | cons w ws =>
      simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        linComb]
      rw [ih]
      ring
theorem linComb_range_entry (n : Nat) (u : Int) (l K : Nat) (ws : List Int) (a : Nat) (rs : Nat ×
    Nat)
    (hlen : ws.length = K) :
    linComb ((List.range' a K).map (fun k => entry n u (k, l))) ws rs =
      (gridX n rs) ^ a * Poly.eval ws (gridX n rs) * (gridY u rs) ^ l := by
  induction K generalizing ws a with
  | zero =>
    cases ws with
    | nil => simp [List.range', linComb, Poly.eval]
    | cons _ _ => nomatch hlen
  | succ K ih =>
    cases ws with
    | nil => nomatch hlen
    | cons w ws =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.range', List.map_cons, linComb, Poly.eval]
      rw [ih ws (a + 1) hlen]
      unfold entry
      dsimp -failIfUnchanged
      rw [pow_succ]
      ring
theorem linComb_monomialGrid_eq_evalLaurent (n : Nat) (u : Int) (K a L : Nat) (ws : List Int) (rs :
    Nat × Nat)
    (hlen : ws.length = K * L) :
    linComb ((monomialGrid K a L).map (entry n u)) ws rs =
      evalLaurent (unflattenLaurent K a L ws) (gridX n rs) (gridY u rs) := by
  induction L generalizing a ws with
  | zero =>
    cases ws with
    | nil => rfl
    | cons _ _ => nomatch hlen
  | succ L ih =>
    simp only [monomialGrid, unflattenLaurent, evalLaurent, List.map_append, linComb_append,
      List.map_map,
      List.length_map, List.length_range]
    have htake : (ws.take K).length = K := by
      rw [List.length_take, hlen, Nat.mul_succ]
      omega
    have hdrop : (ws.drop K).length = K * L := by
      rw [List.length_drop, hlen, Nat.mul_succ]
      omega
    have hr : (List.range K).map (entry n u ∘ fun k => (k, a)) =
        (List.range' 0 K).map (fun k => entry n u (k, a)) := by
      rw [List.range_eq_range']
      rfl
    rw [hr, linComb_range_entry n u a K (ws.take K) 0 rs htake, ih (a + 1) (ws.drop K) hdrop]
    ring
theorem rowIndep_monomialGrid (K L n : Nat) (u : Int) (R0 S : Nat)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hu : u ≠ 0) :
    RowIndep ((monomialGrid K 0 L).map (entry n u)) (gridRect (R0 + L - 1) S) := by
  intro ws hlen hz
  rw [List.length_map, length_monomialGrid] at hlen
  apply forall_zero_of_unflattenLaurent_zero K 0 L ws hlen
  apply forall_zero_of_evalLaurent_grid_zero K L n u R0 S (unflattenLaurent K 0 L ws) hn hsize
  · rw [length_unflattenLaurent]
  · exact hu
  · rw [map_fst_unflattenLaurent]
    exact List.nodup_range'
  · exact length_snd_unflattenLaurent_le K 0 L ws
  · intro r s hr hs
    rw [<- linComb_monomialGrid_eq_evalLaurent n u K 0 L ws (r, s) hlen]
    exact hz (r, s) ((mem_gridRect_iff (R0 + L - 1) S r s).mpr ⟨hr, hs⟩)
theorem exists_cols_det_monomialGrid_ne_zero (K L n : Nat) (u : Int) (R0 S : Nat)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hu : u ≠ 0) :
    ∃ cs, cs.length = K * L /\ (∀ x ∈ cs, x ∈ gridRect (R0 + L - 1) S) /\
      Determinant.det ((monomialGrid K 0 L).map (entry n u)) cs ≠ 0 := by
  rcases exists_cols_det_ne_zero _ _ (rowIndep_monomialGrid K L n u R0 S hn hsize hu) with ⟨cs, hcs,
    hrest⟩
  rw [List.length_map, length_monomialGrid] at hcs
  exact ⟨cs, hcs, hrest⟩
end LaurentInterp
namespace LaurentCongr
open Determinant GridPoints LaurentPoly LaurentInterp
theorem det_map_congr {I J : Type} (xs : List J) (f g : J -> I -> Int) (cols : List I)
    (h : ∀ x ∈ xs, ∀ c ∈ cols, f x c = g x c) :
    det (xs.map f) cols = det (xs.map g) cols := by
  apply det_congr_cols
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    refine List.Forall₂.cons ?_ (ih (fun y hy c hc => h y (List.mem_cons_of_mem _ hy) c hc))
    intro c hc
    exact h x List.mem_cons_self c hc
theorem dvd_det_map_sub {I J : Type} (xs : List J) (f g : J -> I -> Int) (cols : List I) (M : Int)
    (h : ∀ x ∈ xs, ∀ c ∈ cols, M ∣ (f x c - g x c)) :
    M ∣ (det (xs.map f) cols - det (xs.map g) cols) := by
  apply dvd_det_sub_det
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    refine List.Forall₂.cons ?_ (ih (fun y hy c hc => h y (List.mem_cons_of_mem _ hy) c hc))
    intro c hc
    exact h x List.mem_cons_self c hc
theorem pow_emod_congr (M a b : Int) (e : Nat) (h : a % M = b % M) :
    (a ^ e) % M = (b ^ e) % M := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ, Int.mul_emod, ih, h, <- Int.mul_emod]
theorem four_dvd_negThreePow_sub_one (l : Nat) : (4 : Int) ∣ (negThreePow l - 1) := by
  rw [SmallModuli.dvd_sub_iff_emod_eq 4 (negThreePow l) 1 (by decide)]
  unfold negThreePow
  have h := pow_emod_congr 4 (-3) 1 l (by decide)
  simpa using h
def gridExp (n : Nat) (rs : Nat × Nat) : Nat :=
  rs.1 + n * rs.2
theorem cast_gridExp_eq_gridX (n : Nat) (rs : Nat × Nat) :
    (gridExp n rs : Int) = gridX n rs := by
  unfold gridExp gridX
  push_cast
  rfl
def approxEntry (n : Nat) (kl rs : Nat × Nat) : Int :=
  (gridX n rs) ^ kl.1 * (negThreePow kl.2) ^ (gridExp n rs)
theorem two_pow_dvd_entry_sub_approxEntry (n : Nat) (u : Int) (kl rs : Nat × Nat)
    (hbad : ((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - u)) :
    ((2 : Int) ^ n) ∣ (entry n u kl rs - approxEntry n kl rs) := by
  set M : Int := (2 : Int) ^ n
  have hM : 0 < M := SmallModuli.two_pow_pos n
  have hb : ((-3 : Int) ^ n) % M = u % M := (SmallModuli.dvd_sub_iff_emod_eq M _ _ hM).mp hbad
  rcases kl with ⟨k, l⟩
  rcases rs with ⟨r, s⟩
  have hy : (gridY u (r, s)) % M = ((-3 : Int) ^ (gridExp n (r, s))) % M := by
    unfold gridY gridExp
    dsimp -failIfUnchanged
    rw [pow_add, pow_mul, Int.mul_emod, Int.mul_emod ((-3 : Int) ^ r)]
    rw [pow_emod_congr M u ((-3 : Int) ^ n) s hb.symm]
  have he : ((gridY u (r, s)) ^ l) % M = ((negThreePow l) ^ (gridExp n (r, s))) % M := by
    unfold negThreePow
    rw [<- pow_mul, Nat.mul_comm l, pow_mul]
    exact pow_emod_congr M _ _ l hy
  rw [SmallModuli.dvd_sub_iff_emod_eq M _ _ hM]
  unfold entry approxEntry
  dsimp -failIfUnchanged
  rw [Int.mul_emod, he, <- Int.mul_emod]
theorem two_pow_dvd_det_approxEntry (K L n : Nat) (cs : List (Nat × Nat)) (E : Nat)
    (hbound : (E : Int) ≤ (K * L : Int) * ((K * L : Int) - 1 - 2 * (K : Int))) :
    ((2 : Int) ^ E) ∣ det ((monomialGrid K 0 L).map (approxEntry n)) cs := by
  set rs := (monomialGrid K 0 L).map (fun kl => (kl.1, negThreePow kl.2))
  have hdiv : ((2 : Int) ^ E) ∣
      det (rs.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) (cs.map (gridExp n)) := by
    apply DivisibilityBound.two_pow_dvd_det_monomial_geom K E
    · simp only [rs, List.length_map, length_monomialGrid, Nat.cast_mul] at hbound ⊢
      exact hbound
    · intro k q hkq
      rcases List.mem_map.mp hkq with ⟨⟨k', l⟩, hin, heq⟩
      injection heq with hk hq
      subst hk hq
      rw [mem_monomialGrid_iff] at hin
      exact ⟨by omega, four_dvd_negThreePow_sub_one l⟩
  rw [HadamardBound.det_map_cols] at hdiv
  simp only [rs, List.map_map] at hdiv
  have hext : det ((monomialGrid K 0 L).map
      ((fun r c => r (gridExp n c)) ∘ (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x) ∘
        (fun kl => (kl.1, negThreePow kl.2)))) cs =
      det ((monomialGrid K 0 L).map (approxEntry n)) cs := by
    apply det_map_congr
    intro ⟨k, l⟩ _ c _
    simp [Function.comp_apply, approxEntry, cast_gridExp_eq_gridX]
  rwa [hext] at hdiv
theorem two_pow_dvd_det_entry (K L n : Nat) (u : Int) (cs : List (Nat × Nat)) (E : Nat)
    (hE : E ≤ n)
    (hbound : (E : Int) ≤ (K * L : Int) * ((K * L : Int) - 1 - 2 * (K : Int)))
    (hbad : ((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - u)) :
    ((2 : Int) ^ E) ∣ det ((monomialGrid K 0 L).map (entry n u)) cs := by
  have hcongr : ((2 : Int) ^ n) ∣
      (det ((monomialGrid K 0 L).map (entry n u)) cs -
        det ((monomialGrid K 0 L).map (approxEntry n)) cs) := by
    apply dvd_det_map_sub
    intro kl _ rs _
    exact two_pow_dvd_entry_sub_approxEntry n u kl rs hbad
  have hd : ((2 : Int) ^ E) ∣
      (det ((monomialGrid K 0 L).map (entry n u)) cs -
        det ((monomialGrid K 0 L).map (approxEntry n)) cs) :=
     dvd_trans (SmallModuli.pow_dvd_pow_of_le E n hE) hcongr
  have hcomp := two_pow_dvd_det_approxEntry K L n cs E hbound
  rcases hd with ⟨a, ha⟩
  rcases hcomp with ⟨b, hb⟩
  refine ⟨a + b, by linarith⟩
end LaurentCongr
namespace LaurentArch
open Determinant GridPoints LaurentPoly LaurentInterp
private theorem pow_le_pow_of_le {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ]
    have hb : 0 ≤ b := le_trans ha hab
    exact mul_le_mul (pow_le_pow_of_le ha hab n) hab ha (pow_nonneg hb n)
private theorem one_le_pow_of_one_le {a : Int} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    have hk := one_le_pow_of_one_le ha k
    nlinarith
private theorem pow_le_pow_right_of_one_le {a : Int} (ha : 1 ≤ a) {n m : Nat} (hnm : n ≤ m) :
    a ^ n ≤ a ^ m := by
  rcases Nat.le.dest hnm with ⟨k, rfl⟩
  rw [pow_add]
  have hk : 1 ≤ a ^ k := one_le_pow_of_one_le ha k
  have hn : 0 ≤ a ^ n := pow_nonneg (by linarith) n
  nlinarith
private theorem abs_mul_eq (a b : Int) : |a * b| = |a| * |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos ha hb)]
    ring
private theorem abs_pow_eq (a : Int) : ∀ n : Nat, |a ^ n| = |a| ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ, abs_mul_eq, abs_pow_eq a n]
theorem gridX_bounds (n m R S r s : Nat)
    (hR : R ≤ n) (hn : n ≤ 2 ^ m) (hS : S ≤ 2 ^ m) (hr : r < R) (hs : s < S) :
    0 ≤ gridX n (r, s) /\ gridX n (r, s) ≤ (2 : Int) ^ (2 * m) := by
  unfold gridX
  dsimp -failIfUnchanged
  refine ⟨by positivity, ?_⟩
  have h1 : (r : Int) + (n : Int) * (s : Int) ≤ (n : Int) * (S : Int) := by
    have : (s + 1 : Int) ≤ (S : Int) := by omega
    have : (n : Int) * (s + 1 : Int) ≤ (n : Int) * (S : Int) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hn' : (n : Int) ≤ (2 : Int) ^ m := by exact_mod_cast hn
  have hS' : (S : Int) ≤ (2 : Int) ^ m := by exact_mod_cast hS
  have h2 : (n : Int) * (S : Int) ≤ (2 : Int) ^ m * (2 : Int) ^ m :=
    mul_le_mul hn' hS' (by positivity) (by positivity)
  have h3 : (2 : Int) ^ m * (2 : Int) ^ m = (2 : Int) ^ (2 * m) := by
    rw [<- pow_add, Nat.two_mul]
  linarith
theorem abs_entry_le_two_pow (n : Nat) (u : Int) (k l r s m : Nat)
    (hu0 : 0 ≤ u) (hu : u ≤ (2 : Int) ^ m)
    (hp0 : 0 ≤ gridX n (r, s)) (hp : gridX n (r, s) ≤ (2 : Int) ^ (2 * m)) :
    |entry n u (k, l) (r, s)| ≤ (2 : Int) ^ (2 * m * k + (2 * r + m * s) * l) := by
  have h3r : (3 : Int) ^ r ≤ (2 : Int) ^ (2 * r) := by
    rw [pow_mul]
    exact pow_le_pow_of_le (by decide) (by decide) r
  have hus : u ^ s ≤ (2 : Int) ^ (m * s) := by
    rw [pow_mul]
    exact pow_le_pow_of_le hu0 hu s
  have hheight : (3 : Int) ^ r * u ^ s ≤ (2 : Int) ^ (2 * r + m * s) := by
    rw [pow_add]
    exact mul_le_mul h3r hus (pow_nonneg hu0 s) (by positivity)
  have hpoint : (gridX n (r, s)) ^ k ≤ ((2 : Int) ^ (2 * m)) ^ k :=
    pow_le_pow_of_le hp0 hp k
  have hpower : ((3 : Int) ^ r * u ^ s) ^ l ≤ ((2 : Int) ^ (2 * r + m * s)) ^ l :=
    pow_le_pow_of_le (mul_nonneg (by positivity) (pow_nonneg hu0 s)) hheight l
  unfold entry gridY
  dsimp -failIfUnchanged
  rw [abs_mul_eq, abs_pow_eq, abs_pow_eq, abs_mul_eq, abs_pow_eq, abs_pow_eq]
  rw [abs_of_nonneg hp0, abs_of_nonneg hu0]
  have habs3 : |(-3 : Int)| = 3 := by decide
  rw [habs3]
  calc (gridX n (r, s)) ^ k * ((3 : Int) ^ r * u ^ s) ^ l
    _ ≤ ((2 : Int) ^ (2 * m)) ^ k * ((2 : Int) ^ (2 * r + m * s)) ^ l :=
      mul_le_mul hpoint hpower (by positivity) (by positivity)
    _ = (2 : Int) ^ (2 * m * k + (2 * r + m * s) * l) := by
      rw [<- pow_mul, <- pow_mul, <- pow_add]
theorem abs_det_entry_le_two_pow (K L n : Nat) (u : Int) (R S : Nat) (cs : List (Nat × Nat)) (m B :
    Nat)
    (hlen : cs.length = K * L) (hcols : ∀ c ∈ cs, c ∈ gridRect R S)
    (hu0 : 0 ≤ u) (hu : u ≤ (2 : Int) ^ m)
    (hR : R ≤ n) (hn : n ≤ 2 ^ m) (hS : S ≤ 2 ^ m)
    (hN : K * L ≤ 2 ^ m)
    (hex : 2 * m * K + (2 * R + m * S) * L ≤ B) :
    |det ((monomialGrid K 0 L).map (entry n u)) cs| ≤ (2 : Int) ^ ((K * L) * (m + B)) := by
  have hlen_rows : ((monomialGrid K 0 L).map (entry n u)).length = K * L := by
    rw [List.length_map, length_monomialGrid]
  have hbound := HadamardBound.abs_det_le_two_pow ((monomialGrid K 0 L).map (entry n u)) cs m B
    (by rw [hlen_rows, hlen]) (by rw [hlen_rows]; exact hN)
  rw [hlen_rows] at hbound
  apply hbound
  intro row hrow ⟨r, s⟩ hrs
  rcases List.mem_map.mp hrow with ⟨⟨k, l⟩, hkl, rfl⟩
  rw [mem_monomialGrid_iff] at hkl
  have hrs_grid := (mem_gridRect_iff R S r s).mp (hcols (r, s) hrs)
  have hpb := gridX_bounds n m R S r s hR hn hS hrs_grid.1 hrs_grid.2
  have heb := abs_entry_le_two_pow n u k l r s m hu0 hu hpb.1 hpb.2
  refine le_trans heb ?_
  apply pow_le_pow_right_of_one_le (by decide : (1 : Int) ≤ 2)
  have h1 : 2 * m * k ≤ 2 * m * K := Nat.mul_le_mul_left (2 * m) (by omega)
  have h2 : 2 * r + m * s ≤ 2 * R + m * S := by
    have : m * s ≤ m * S := Nat.mul_le_mul_left m (by omega)
    omega
  have h3 : (2 * r + m * s) * l ≤ (2 * R + m * S) * L :=
    Nat.mul_le_mul h2 (by omega)
  omega
end LaurentArch
namespace LargeExclusion
open Determinant GridPoints LaurentPoly LaurentInterp LaurentCongr LaurentArch
theorem exclusion : SmallModuli.large_exclusion := by
  intro n u hn hu hbad
  have hn0 : n ≠ 0 := by omega
  set m := Nat.log2 n + 1
  have hbits1 : 2 ^ (m - 1) ≤ n := Nat.log2_self_le hn0
  have hbits2 : n < 2 ^ m := Nat.lt_log2_self
  have hm : 59 ≤ m := by
    by_contra hlt
    push Not at hlt
    have hle : m ≤ 58 := by omega
    have hpow : 2 ^ m ≤ 2 ^ 58 := Nat.pow_le_pow_right (by decide) hle
    omega
  set K := 256 * m ^ 2
  set L := 8 * m
  set R0 := 32 * m ^ 2
  set S := 64 * m
  set R := R0 + L - 1
  have hKL : K * L = 2048 * m ^ 3 := by
    dsimp -failIfUnchanged [K, L]
    ring
  have hRS : R0 * S = K * L := by
    dsimp -failIfUnchanged [R0, S, K, L]
    ring
  have hdim := GrowthBounds.cube_sq_lt_of_two_pow_le m n hm hbits1
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hm3 : m ^ 2 ≤ m ^ 3 := by nlinarith
  have hNsmall : 2048 * m ^ 3 < n := by nlinarith
  have hR_le_n : R ≤ n := by
    have : R0 + L ≤ 2048 * m ^ 3 := by dsimp -failIfUnchanged [R0, L]; omega
    omega
  have hR0_le_n : R0 ≤ n := by
    dsimp -failIfUnchanged [R0]
    omega
  have hS_le_2m : S ≤ 2 ^ m := by
    dsimp -failIfUnchanged [S]
    omega
  have hKL_le_2m : K * L ≤ 2 ^ m := by
    rw [hKL]
    omega
  have hroot : (K - 1) * L < R0 * S := by
    rw [hRS]
    have hKpos : 0 < K := by dsimp -failIfUnchanged [K]; positivity
    have hLpos : 0 < L := by dsimp -failIfUnchanged [L]; positivity
    exact Nat.mul_lt_mul_of_pos_right (by omega) hLpos
  rcases exists_cols_det_monomialGrid_ne_zero K L n (u : Int) R0 S hR0_le_n hroot (by omega) with
    ⟨cs, hlen, hcols, hnz⟩
  set T := (2048 * m ^ 3) * (2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2))
  set B := 1664 * m ^ 3
  set U := (2048 * m ^ 3) * (m + B)
  have hgap := GrowthBounds.archimedean_lt_padic_exp m (by omega)
  have hUT : U < T := by
    dsimp -failIfUnchanged [U, B, T]
    linarith
  have hT_le_n : T ≤ n := by
    dsimp -failIfUnchanged [T]
    have : 2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2) ≤ 2048 * m ^ 3 := by omega
    calc (2048 * m ^ 3) * (2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2))
      _ ≤ (2048 * m ^ 3) * (2048 * m ^ 3) := Nat.mul_le_mul_left _ this
      _ = (2048 * m ^ 3) ^ 2 := by ring
      _ ≤ n := by omega
  have hdiv : ((2 : Int) ^ T) ∣ det ((monomialGrid K 0 L).map (entry n (u : Int))) cs := by
    apply two_pow_dvd_det_entry K L n (u : Int) cs T hT_le_n _ hbad
    have hT_eq : T = (K * L) * (K * L - 1 - 2 * K) := by rw [hKL]
    have hsub1 : 1 ≤ K * L := by rw [hKL]; omega
    have hsub2 : 2 * K ≤ K * L - 1 := by rw [hKL]; dsimp -failIfUnchanged [K]; omega
    rw [hT_eq]
    push_cast [hsub1, hsub2]
    rfl
  have hupper : |det ((monomialGrid K 0 L).map (entry n (u : Int))) cs| ≤ (2 : Int) ^ U := by
    have hU : U = (K * L) * (m + B) := by rw [hKL]
    rw [hU]
    apply abs_det_entry_le_two_pow K L n (u : Int) R S cs m B hlen hcols (by omega)
    · have : (u : Int) ≤ (2 : Int) ^ m := by
        have : u ≤ 2 ^ m := by omega
        exact_mod_cast this
      exact this
    · exact hR_le_n
    · omega
    · exact hS_le_2m
    · exact hKL_le_2m
    · have hR_le : R ≤ R0 + L := by omega
      have hstep1 : 2 * m * K + (2 * R + m * S) * L ≤ 2 * m * K + (2 * (R0 + L) + m * S) * L := by
        have : 2 * R + m * S ≤ 2 * (R0 + L) + m * S := by omega
        have : (2 * R + m * S) * L ≤ (2 * (R0 + L) + m * S) * L := Nat.mul_le_mul_right L this
        omega
      have hstep2 : 2 * m * K + (2 * (R0 + L) + m * S) * L = 1536 * m ^ 3 + 128 * m ^ 2 := by
        dsimp -failIfUnchanged [K, L, R0, S]
        ring
      have hstep3 : 1536 * m ^ 3 + 128 * m ^ 2 ≤ B := by
        dsimp -failIfUnchanged [B]
        omega
      omega
  exact HadamardBound.false_of_two_pow_dvd_and_abs_le _ U T hUT hnz hdiv hupper
end LargeExclusion
namespace TrajectoryGraph
def A (i : Nat) : Nat := 3 ^ i * 4 - 1
def B (i : Nat) : Nat := 3 ^ i * 6 + i + 4
def F (i : Nat) : Nat := 3 ^ i * 2 + i + 5
def core : Prop := ∀ i : Nat, 7 ≤ i -> ¬ (2 ^ (i + 1) ∣ F i)
inductive MacroStep : Nat -> Nat -> Prop where
  | R1 (i n : Nat) : 3 ^ i * 2 - i - 2 ≤ n /\ n ≤ 3 ^ i * 6 - i - 6 -> n % 2 = i % 2 ->
      MacroStep n ((n + B i) / 2)
  | R2 (i n : Nat) : 3 ^ i * 2 - i ≤ n /\ n ≤ 3 ^ i * 6 - i - 10 -> n % 2 = (i + 1) % 2 ->
      MacroStep n (A (i + 1))
inductive MacroReaches : Nat -> Nat -> Prop where
  | one (x y : Nat) : MacroStep x y -> MacroReaches x y
  | cons (x y z : Nat) : MacroStep x y -> MacroReaches y z -> MacroReaches x z
theorem succ_le_three_pow (i : Nat) : i + 1 ≤ 3 ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Nat.pow_succ]
    omega
theorem two_pow_mul_linear_lt_three_pow (i : Nat) (hi : 7 ≤ i) : 2 ^ i * (2 * i + 13) < 3 ^ i * 2 :=
    by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hpos : 0 < 2 ^ m := by positivity
    rw [Nat.pow_succ, Nat.pow_succ]
    nlinarith
theorem exists_two_pow_mul_odd (n : Nat) (hn : 0 < n) : ∃ v q : Nat, n = 2 ^ v * q /\ q % 2 = 1 /\ 0
    < q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases heven : n % 2 = 0
    · obtain ⟨v, q, he, ho, hq⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨v + 1, q, ?_, ho, hq⟩
      have hn2 : n = 2 * (n / 2) := by omega
      rw [hn2, he, Nat.pow_succ]
      ring
    · exact ⟨0, n, by simp, by omega, hn⟩
theorem exists_two_pow_odd_factor_F (i : Nat) (hc : core) (hi : 7 ≤ i) :
    ∃ v q : Nat, F i = 2 ^ v * q /\ q % 2 = 1 /\ 2 * i + 15 ≤ q := by
  obtain ⟨v, q, hf, ho, hq⟩ := exists_two_pow_mul_odd (F i) (by unfold F; omega)
  have hv : v ≤ i := by
    by_contra hgt
    push Not at hgt
    apply hc i hi
    refine ⟨2 ^ (v - (i + 1)) * q, ?_⟩
    have hv_eq : v = (i + 1) + (v - (i + 1)) := by omega
    conv_lhs => rw [hf, hv_eq, Nat.pow_add]
    ring
  have hp : 2 ^ v ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hv
  have hlarge := two_pow_mul_linear_lt_three_pow i hi
  have hqbound : 2 * i + 13 < q := by
    by_contra hle
    push Not at hle
    have hmul : 2 ^ v * q ≤ 2 ^ i * (2 * i + 13) := Nat.mul_le_mul hp hle
    unfold F at hf
    omega
  exact ⟨v, q, hf, ho, by omega⟩
theorem macroReaches_from_sub (i v q : Nat) (hi : 7 ≤ i) (ho : q % 2 = 1)
    (hq : 2 * i + 15 ≤ q) (hd : 2 ^ v * q ≤ F i) :
    MacroReaches (B i - 2 ^ v * q) (A (i + 1)) := by
  induction v with
  | zero =>
    apply MacroReaches.one
    apply MacroStep.R2 i
    · have hp3 := succ_le_three_pow i
      unfold B F at *
      simp only [Nat.pow_zero, Nat.one_mul] at *
      omega
    · unfold B F at *
      simp only [Nat.pow_zero, Nat.one_mul] at *
      omega
  | succ v ih =>
    have hp : 0 < 2 ^ v := by positivity
    rw [Nat.pow_succ] at hd ⊢
    have hmul2 : 2 ^ v * 2 * q = 2 * (2 ^ v * q) := by ring
    have hp3 := succ_le_three_pow i
    have hdiv : (B i - 2 ^ v * 2 * q + B i) / 2 = B i - 2 ^ v * q := by
      unfold B F at *
      omega
    have hstep : MacroStep (B i - 2 ^ v * 2 * q) (B i - 2 ^ v * q) := by
      rw [<- hdiv]
      apply MacroStep.R1 i
      · have hq_pos : 1 * (2 * i + 15) ≤ 2 ^ v * q := Nat.mul_le_mul hp hq
        unfold B F at *
        omega
      · unfold B F at *
        omega
    exact MacroReaches.cons _ _ _ hstep (ih (by omega))
theorem macroReaches_next_layer (i : Nat) (hc : core) (hi : 7 ≤ i) : MacroReaches (A i) (A (i + 1))
    := by
  obtain ⟨v, q, hf, ho, hq⟩ := exists_two_pow_odd_factor_F i hc hi
  have h := macroReaches_from_sub i v q hi ho hq (by omega)
  rw [<- hf] at h
  have hba : B i - F i = A i := by
    have hp3 := succ_le_three_pow i
    unfold A B F
    omega
  rw [hba] at h
  exact h
end TrajectoryGraph
namespace CoreBridge
theorem core (hlarge : SmallModuli.large_exclusion) : TrajectoryGraph.core := by
  intro i hi ⟨q, hq⟩
  apply SmallModuli.not_two_pow_succ_dvd_F hlarge i hi
  refine ⟨(q : Int), ?_⟩
  have hq_int : (TrajectoryGraph.F i : Int) = ((2 ^ (i + 1) * q : Nat) : Int) := by exact_mod_cast
    hq
  unfold TrajectoryGraph.F at hq_int
  unfold SmallModuli.F
  push_cast at hq_int
  linarith
end CoreBridge


variable {Γ₀ Λ₀ α β γ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
abbrev HalfTape := ListBlank (Fin 2)
abbrev BitWord := List (Fin 2)
@[simp] theorem multiStep_zero_eq (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) : multiStep M config 0 =
    some config := rfl
@[simp] theorem multiStep_one_eq (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) : multiStep M config 1 =
    step M config := rfl
@[simp] theorem multiStep_succ_bind (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] theorem cons_zero_default_eq : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem head_default_eq : (default : HalfTape).head = 0 := rfl
@[simp] theorem tail_default_eq : (default : HalfTape).tail = default := rfl
@[simp] theorem nil_append_halfTape (s : HalfTape) : ([] : BitWord) +> s = s := rfl
@[simp] theorem cons_append_halfTape (a : Fin 2) (l : BitWord) (s : HalfTape) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] theorem append_assoc (l1 l2 : BitWord) (s : HalfTape) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, cons_append_halfTape, ih]
theorem step_to_multiStep_one {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c1 c2 : Cfg Γ₀ Λ₀) (h : c1 [tm]⊢ c2) :
    c1 [tm]⊢^{1} c2 := by simp [h]
theorem step_to_reachesPlus {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c1 c2 : Cfg Γ₀ Λ₀) (h : c1 [tm]⊢ c2) :
    c1 [tm]⊢⁺ c2 := ⟨1, by decide, step_to_multiStep_one tm c1 c2 h⟩
theorem multiStep_add_bind {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c1 : Cfg Γ₀ Λ₀) (n m : Nat) :
    multiStep tm c1 (n + m) = (multiStep tm c1 n).bind (fun c2 => multiStep tm c2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ_bind, ih, Option.bind_assoc]
    simp_rw [multiStep_succ_bind]
theorem multiStep_trans_explicit {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c1 c2 c_3 : Cfg Γ₀ Λ₀) (n m : Nat)
    (h₁ : c1 [tm]⊢^{n} c2) (h₂ : c2 [tm]⊢^{m} c_3) :
    c1 [tm]⊢^{n+m} c_3 := by
  rw [multiStep_add_bind, h₁]; simp [h₂]
theorem reachesStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c1 [tm]⊢* c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans_explicit tm c1 c2 c_3 n m hn hm⟩
theorem reachesPlus_to_reachesStar {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 : Cfg Γ₀ Λ₀} (h : c1 [tm]⊢⁺ c2) :
    c1 [tm]⊢* c2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
theorem reachesPlus_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c1 [tm]⊢⁺ c2) (h₂ : c2 [tm]⊢⁺ c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans_explicit tm c1 c2 c_3 n m hn hm⟩
theorem reachesPlus_reachesStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c1 [tm]⊢⁺ c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), multiStep_trans_explicit tm c1 c2 c_3 n
    m hn hm⟩
theorem reachesStar_reachesPlus_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c1 [tm]⊢* c2) (h₂ : c2 [tm]⊢⁺ c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans_explicit tm c1 c2 c_3 n m hn hm⟩
theorem step_reachesStar_reachesPlus {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c1 c2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c1 [tm]⊢ c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢⁺ c_3 :=
  reachesPlus_reachesStar_trans (step_to_reachesPlus tm c1 c2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> rfl)
macro "step" : tactic =>
  `(tactic| (try refine reachesPlus_to_reachesStar ?_) <;>
    refine step_reachesStar_reachesPlus (by (try simp only [BusyBeaver.Cfg.headRight,
      BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons, head_default_eq]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, cons_zero_default_eq,
      head_default_eq, tail_default_eq])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
def rep01 : Nat -> HalfTape -> HalfTape
  | 0, r => r
  | b + 1, r => (0 : Fin 2) >> (1 : Fin 2) >> rep01 b r
def rep11 : Nat -> HalfTape -> HalfTape
  | 0, r => r
  | a + 1, r => (1 : Fin 2) >> (1 : Fin 2) >> rep11 a r
@[simp] theorem rep01_zero (r : HalfTape) : rep01 0 r = r := rfl
@[simp] theorem rep01_succ (b : Nat) (r : HalfTape) : rep01 (b + 1) r = (0 : Fin 2) >> (1 : Fin 2)
    >> rep01 b r := rfl
theorem rep01_succ_inner (b : Nat) (r : HalfTape) :
    rep01 (b + 1) r = rep01 b ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [rep01_succ (b + 1), ih, <- rep01_succ b]
theorem rep01_add (b1 b2 : Nat) (r : HalfTape) : rep01 (b1 + b2) r = rep01 b1 (rep01 b2 r) := by
  induction b1 with
  | zero => simp
  | succ b1 ih => rw [Nat.succ_add, rep01_succ, rep01_succ, ih]
@[simp] theorem rep11_zero (r : HalfTape) : rep11 0 r = r := rfl
@[simp] theorem rep11_succ (a : Nat) (r : HalfTape) : rep11 (a + 1) r = (1 : Fin 2) >> (1 : Fin 2)
    >> rep11 a r := rfl
theorem rep11_succ_inner (a : Nat) (r : HalfTape) :
    rep11 (a + 1) r = rep11 a ((1 : Fin 2) >> (1 : Fin 2) >> r) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [rep11_succ (a + 1), ih, <- rep11_succ a]
theorem rep11_add (a1 a2 : Nat) (r : HalfTape) : rep11 (a1 + a2) r = rep11 a1 (rep11 a2 r) := by
  induction a1 with
  | zero => simp
  | succ a1 ih => rw [Nat.succ_add, rep11_succ, rep11_succ, ih]
theorem shift_B_rep01 (b : Nat) (l r : HalfTape) :
    (l {{B}}> rep01 b r) [target_tm]⊢* (rep01 b l {{B}}> r) := by
  induction b generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [rep01_succ, rep01_succ_inner]
    have h1 : (l {{B}}> ((0 : Fin 2) >> (1 : Fin 2) >> rep01 b r)) [target_tm]⊢⁺
        (((0 : Fin 2) >> (1 : Fin 2) >> l) {{B}}> rep01 b r) := by execute
    exact reachesStar_trans (reachesPlus_to_reachesStar h1) (ih _)
theorem shift_C_rep01 (b : Nat) (l r : HalfTape) :
    (rep01 b l <{{C}} r) [target_tm]⊢* (l <{{C}} rep01 b r) := by
  induction b generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [rep01_succ, rep01_succ_inner]
    have h1 : (((0 : Fin 2) >> (1 : Fin 2) >> rep01 b l) <{{C}} r) [target_tm]⊢⁺
        (rep01 b l <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by execute
    exact reachesStar_trans (reachesPlus_to_reachesStar h1) (ih _)
theorem shift_A_rep01_to_rep11 (b : Nat) (l r : HalfTape) :
    (l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 b r)) [target_tm]⊢*
    (rep11 b l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r)) := by
  induction b generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [rep01_succ, rep11_succ_inner]
    have h1 : (l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      rep01 b r))
        [target_tm]⊢⁺
        (((1 : Fin 2) >> (1 : Fin 2) >> l) {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          rep01 b r)) := by execute
    exact reachesStar_trans (reachesPlus_to_reachesStar h1) (ih _)
theorem shift_A_rep11 (a : Nat) (l r : HalfTape) :
    (rep11 a l <{{A}} r) [target_tm]⊢* (l <{{A}} rep11 a r) := by
  induction a generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ a ih =>
    rw [rep11_succ, rep11_succ_inner]
    have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> rep11 a l) <{{A}} r) [target_tm]⊢⁺
        (rep11 a l <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by execute
    exact reachesStar_trans (reachesPlus_to_reachesStar h1) (ih _)
abbrev d0 : HalfTape := default
def S1 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> rep11 a d0) <{{C}} rep01 b (rep11 c ((0 : Fin 2) >> (1 : Fin 2) >> d0))
def S2 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> rep11 a d0) <{{C}} rep01 b ((1 : Fin 2) >> d0)
def S3 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> rep11 a d0) <{{C}} rep01 b d0
theorem step_S1_one (a b c : Nat) :
    (S1 (1 + a) b (2 + c)) [target_tm]⊢* (S1 a (3 + b) c) := by
  unfold S1
  rw [Nat.add_comm 1 a, Nat.add_comm 2 c, Nat.add_comm 3 b]
  simp only [rep11_succ]
  set l0 := (1 : Fin 2) >> rep11 a d0
  set r0 := rep11 c ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 :
    Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> rep01 b ((1 : Fin 2) >> (1 : Fin 2)
        >> (1 : Fin 2) >> (1 : Fin 2) >> r0)) := by execute
  have h2 := shift_B_rep01 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) ((1 : Fin 2) >> (1 : Fin 2) >> (1 :
    Fin 2) >> (1 : Fin 2) >> r0)
  rw [<- rep01_succ_inner b l0] at h2
  have h3 : (rep01 (b + 1) l0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    r0))
      [target_tm]⊢⁺ (rep01 (b + 2) l0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> r0)) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 2) l0 ((0 : Fin 2) >> (1 : Fin 2) >> r0)
  rw [<- rep01_succ_inner (b + 2) r0] at h4
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) h4))
theorem step_S1_iter (n a b c : Nat) :
    (S1 (n + a) b (n * 2 + c)) [target_tm]⊢* (S1 a (n * 3 + b) c) := by
  induction n generalizing a b c with
  | zero =>
    simp only [Nat.zero_add, Nat.zero_mul]
    exact ⟨0, rfl⟩
  | succ n ih =>
    have h1 : n + 1 + a = 1 + (n + a) := by omega
    have h2 : (n + 1) * 2 + c = 2 + (n * 2 + c) := by omega
    have h3 : (n + 1) * 3 + b = n * 3 + (3 + b) := by omega
    rw [h1, h2, h3]
    exact reachesStar_trans (step_S1_one (n + a) b (n * 2 + c)) (ih a (3 + b) c)
theorem step_S1_zero_left (b c : Nat) :
    (S1 0 b (3 + c)) [target_tm]⊢* (S1 (2 + b) 2 c) := by
  unfold S1
  rw [Nat.add_comm 3 c, Nat.add_comm 2 b]
  simp only [rep11_zero, rep11_succ]
  set r0 := rep11 c ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h1 : (((1 : Fin 2) >> d0) <{{C}} rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 :
    Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (d0 {{B}}> rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> r0)) := by execute
  have h2 := shift_B_rep01 b d0 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 :
    Fin 2) >> (1 : Fin 2) >> r0)
  have h3 : (rep01 b d0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin
    2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (rep01 (b + 1) d0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin
        2) >> r0)) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 1) d0 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    r0)
  have h5 : (d0 <{{C}} rep01 (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    r0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 2) ((1 : Fin
        2) >> (1 : Fin 2) >> r0))) := by
    rw [rep01_succ_inner (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> r0)]
    execute
  have h6 := shift_A_rep01_to_rep11 (b + 2) d0 ((1 : Fin 2) >> (1 : Fin 2) >> r0)
  have h7 : (rep11 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1
    : Fin 2) >> r0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> rep11 (b + 2) d0) <{{C}} rep01 2 r0) := by
    simp only [rep01_succ, rep01_zero]
    execute
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) (reachesStar_trans h4 (reachesStar_trans
    (reachesPlus_to_reachesStar h5) (reachesStar_trans h6 (reachesPlus_to_reachesStar h7))))))
theorem step_S2_one (a b : Nat) :
    (S2 (1 + a) b) [target_tm]⊢* (S2 a (3 + b)) := by
  unfold S2
  rw [Nat.add_comm 1 a, Nat.add_comm 3 b]
  simp only [rep11_succ]
  set l0 := (1 : Fin 2) >> rep11 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} rep01 b ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> rep01 b ((1 : Fin 2) >> d0)) := by
        execute
  have h2 := shift_B_rep01 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) ((1 : Fin 2) >> d0)
  rw [<- rep01_succ_inner b l0] at h2
  have h3 : (rep01 (b + 1) l0 {{B}}> ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (rep01 (b + 3) l0 <{{C}} ((1 : Fin 2) >> d0)) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 3) l0 ((1 : Fin 2) >> d0)
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) h4))
theorem step_S2_iter (a b : Nat) :
    (S2 a b) [target_tm]⊢* (S2 0 (a * 3 + b)) := by
  induction a generalizing b with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add]
    exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : a + 1 = 1 + a := by omega
    have h2 : (a + 1) * 3 + b = a * 3 + (3 + b) := by omega
    rw [h2, h1]
    exact reachesStar_trans (step_S2_one a b) (ih (3 + b))
theorem Ov2 (b : Nat) :
    (S2 0 b) [target_tm]⊢* (S3 (2 + b) 1) := by
  unfold S2 S3
  rw [Nat.add_comm 2 b]
  simp only [rep11_zero]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} rep01 b ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{B}}> rep01 b ((1 : Fin 2) >> d0)) := by execute
  have h2 := shift_B_rep01 b d0 ((1 : Fin 2) >> d0)
  have h3 : (rep01 b d0 {{B}}> ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (rep01 (b + 2) d0 <{{C}} ((1 : Fin 2) >> d0)) := by
    cases b with
    | zero =>
      simp only [Nat.zero_add, rep01_succ, rep01_zero]
      execute
    | succ b =>
      simp only [Nat.succ_add, rep01_succ]
      execute
  have h4 := shift_C_rep01 (b + 2) d0 ((1 : Fin 2) >> d0)
  have h5 : (d0 <{{C}} rep01 (b + 2) ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 2) ((1 : Fin
        2) >> d0))) := by execute
  have h6 := shift_A_rep01_to_rep11 (b + 2) d0 ((1 : Fin 2) >> d0)
  have h7 : (rep11 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
    d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> rep11 (b + 2) d0) <{{C}} rep01 1 d0) := by
    simp only [rep01_succ, rep01_zero]
    execute
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) (reachesStar_trans h4 (reachesStar_trans
    (reachesPlus_to_reachesStar h5) (reachesStar_trans h6 (reachesPlus_to_reachesStar h7))))))
theorem step_S3_one (a b : Nat) :
    (S3 (1 + a) b) [target_tm]⊢* (S3 a (2 + b)) := by
  unfold S3
  rw [Nat.add_comm 1 a, Nat.add_comm 2 b]
  simp only [rep11_succ]
  set l0 := (1 : Fin 2) >> rep11 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} rep01 b d0)
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> rep01 b d0) := by execute
  have h2 := shift_B_rep01 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) d0
  rw [<- rep01_succ_inner b l0] at h2
  have h3 : (rep01 (b + 1) l0 {{B}}> d0)
      [target_tm]⊢⁺ (rep01 (b + 2) l0 <{{C}} d0) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 2) l0 d0
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) h4))
theorem step_S3_iter (a b : Nat) :
    (S3 a b) [target_tm]⊢* (S3 0 (a * 2 + b)) := by
  induction a generalizing b with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add]
    exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : a + 1 = 1 + a := by omega
    have h2 : (a + 1) * 2 + b = a * 2 + (2 + b) := by omega
    rw [h2, h1]
    exact reachesStar_trans (step_S3_one a b) (ih (2 + b))
theorem Ov3 (b : Nat) :
    (S3 0 b) [target_tm]⊢⁺ (S1 0 2 (2 + b)) := by
  unfold S3 S1
  rw [Nat.add_comm 2 b]
  simp only [rep11_zero]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} rep01 b d0)
      [target_tm]⊢⁺ (d0 {{B}}> rep01 b d0) := by execute
  have h2 := shift_B_rep01 b d0 d0
  have h3 : (rep01 b d0 {{B}}> d0)
      [target_tm]⊢⁺ (rep01 (b + 1) d0 <{{C}} d0) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 1) d0 d0
  have h5 : (d0 <{{C}} rep01 (b + 1) d0)
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 1) d0)) :=
        by execute
  have h6 := shift_A_rep01_to_rep11 (b + 1) d0 d0
  have h7 : (rep11 (b + 1) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (rep11 (b + 3) d0 <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
        2) >> d0)) := by
    simp only [rep11_succ]
    execute
  have h8 := shift_A_rep11 (b + 3) d0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0)
  have h9 : (d0 <{{A}} rep11 (b + 3) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> d0) <{{C}} rep01 2 (rep11 (b + 2) ((0 : Fin 2) >> (1 : Fin 2)
        >> d0))) := by
    rw [<- rep11_succ_inner (b + 3) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    simp only [rep11_succ, rep01_succ, rep01_zero]
    execute
  exact reachesPlus_reachesStar_trans h1 (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) (reachesStar_trans h4 (reachesStar_trans
    (reachesPlus_to_reachesStar h5) (reachesStar_trans h6 (reachesStar_trans
    (reachesPlus_to_reachesStar h7) (reachesStar_trans h8 (reachesPlus_to_reachesStar h9))))))))
theorem step_S3_to_S1 (a b : Nat) :
    (S3 a b) [target_tm]⊢⁺ (S1 0 2 (2 + a * 2 + b)) := by
  have h1 := step_S3_iter a b
  have h2 := Ov3 (a * 2 + b)
  have heq : 2 + (a * 2 + b) = 2 + a * 2 + b := by omega
  rw [heq] at h2
  exact reachesStar_reachesPlus_trans h1 h2
theorem step_S2_to_S1 (a b : Nat) :
    (S2 a b) [target_tm]⊢* (S1 0 2 (7 + a * 6 + b * 2)) := by
  have h1 := step_S2_iter a b
  have h2 := Ov2 (a * 3 + b)
  have h3 := reachesPlus_to_reachesStar (step_S3_to_S1 (2 + (a * 3 + b)) 1)
  have heq : 2 + (2 + (a * 3 + b)) * 2 + 1 = 7 + a * 6 + b * 2 := by omega
  rw [heq] at h3
  exact reachesStar_trans h1 (reachesStar_trans h2 h3)
theorem step_S1_to_S2 (a b : Nat) :
    (S1 (2 + a) b 1) [target_tm]⊢⁺ (S2 a (6 + b)) := by
  unfold S1 S2
  rw [Nat.add_comm 2 a, Nat.add_comm 6 b]
  simp only [rep11_succ, rep11_zero]
  set l0 := (1 : Fin 2) >> rep11 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h2 := shift_B_rep01 b ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0)
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  rw [<- rep01_succ_inner b ((1 : Fin 2) >> (1 : Fin 2) >> l0)] at h2
  have h3 : (rep01 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >>
        l0)) <{{A}}
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        d0)) := by
    simp only [rep01_succ]
    execute
  have h4 : (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 1) ((1 : Fin 2) >> (1 : Fin 2)
    >> l0)) <{{A}}
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        d0))
      [target_tm]⊢⁺
      (rep01 (b + 4) ((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [rep01_succ]
    execute
  have h5 := shift_C_rep01 (b + 4) ((1 : Fin 2) >> (1 : Fin 2) >> l0)
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h6 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      rep01 (b + 4) ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      rep01 (b + 4) ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h7 := shift_B_rep01 (b + 4) ((0 : Fin 2) >> (1 : Fin 2) >> l0)
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  rw [<- rep01_succ_inner (b + 4) l0] at h7
  have h8 : (rep01 (b + 5) l0 {{B}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (rep01 (b + 6) l0 <{{C}} ((1 : Fin 2) >> d0)) := by
    simp only [rep01_succ]
    execute
  have h9 := shift_C_rep01 (b + 6) l0 ((1 : Fin 2) >> d0)
  exact reachesPlus_reachesStar_trans h1 (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) (reachesStar_trans (reachesPlus_to_reachesStar h4)
    (reachesStar_trans h5 (reachesStar_trans (reachesPlus_to_reachesStar h6) (reachesStar_trans h7
    (reachesStar_trans (reachesPlus_to_reachesStar h8) h9)))))))
theorem step_S1_odd (a b : Nat) :
    (S1 (2 + a) b 1) [target_tm]⊢⁺ (S1 0 2 (19 + a * 6 + b * 2)) := by
  have h1 := step_S1_to_S2 a b
  have h2 := step_S2_to_S1 a (6 + b)
  have heq : 7 + a * 6 + (6 + b) * 2 = 19 + a * 6 + b * 2 := by omega
  rw [heq] at h2
  exact reachesPlus_reachesStar_trans h1 h2
theorem step_S1_zero_right (a b : Nat) :
    (S1 a b 0) [target_tm]⊢⁺ (S1 0 2 (3 + a * 2 + b)) := by
  have heq1 : S1 a b 0 = S3 a (1 + b) := by
    rw [Nat.add_comm 1 b]
    unfold S1 S3
    simp only [rep11_zero, <- rep01_succ_inner]
  rw [heq1]
  have h := step_S3_to_S1 a (1 + b)
  have heq2 : 2 + a * 2 + (1 + b) = 3 + a * 2 + b := by omega
  rw [heq2] at h
  exact h
def P (n1 n2 : Nat) : Prop :=
  ∀ c : Nat, (S1 0 2 (n1 + c)) [target_tm]⊢* (S1 n2 2 c)
theorem P_O : P 0 0 := by
  intro c
  simp only [Nat.zero_add]
  exact ⟨0, rfl⟩
theorem P_S (n1 n2 : Nat) (hp : P n1 n2) :
    P (n1 + n2 * 2 + 3) (4 + n2 * 3) := by
  intro c
  have h1 := hp (n2 * 2 + (3 + c))
  have heq1 : n1 + (n2 * 2 + (3 + c)) = n1 + n2 * 2 + 3 + c := by omega
  rw [heq1] at h1
  have h2 := step_S1_iter n2 0 2 (3 + c)
  simp only [Nat.add_zero] at h2
  have h3 := step_S1_zero_left (n2 * 3 + 2) c
  have heq2 : 2 + (n2 * 3 + 2) = 4 + n2 * 3 := by omega
  rw [heq2] at h3
  exact reachesStar_trans h1 (reachesStar_trans h2 h3)
theorem P_n (i : Nat) : P (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 2) := by
  induction i with
  | zero => exact P_O
  | succ i ih =>
    have hps := P_S _ _ ih
    have hp3 := TrajectoryGraph.succ_le_three_pow i
    have heq1 : 3 ^ i * 2 - i - 2 + (3 ^ i * 2 - 2) * 2 + 3 = 3 ^ (i + 1) * 2 - (i + 1) - 2 := by
      rw [Nat.pow_succ]
      omega
    have heq2 : 4 + (3 ^ i * 2 - 2) * 3 = 3 ^ (i + 1) * 2 - 2 := by
      rw [Nat.pow_succ]
      omega
    rw [heq1, heq2] at hps
    exact hps
def S' (n : Nat) : Cfg (Fin 2) (Fin 6) := S1 0 2 n
theorem step_S'_odd (n1 n2 c : Nat) (hp : P n1 (c + (2 + n2))) :
    (S' (n1 + c * 2 + 1)) [target_tm]⊢⁺ (S' (23 + n2 * 6 + c * 6)) := by
  unfold S'
  have h1 := hp (c * 2 + 1)
  have heq1 : n1 + (c * 2 + 1) = n1 + c * 2 + 1 := by omega
  rw [heq1] at h1
  have h2 := step_S1_iter c (2 + n2) 2 1
  have h3 := step_S1_odd n2 (c * 3 + 2)
  have heq2 : 19 + n2 * 6 + (c * 3 + 2) * 2 = 23 + n2 * 6 + c * 6 := by omega
  rw [heq2] at h3
  exact reachesStar_reachesPlus_trans h1 (reachesStar_reachesPlus_trans h2 h3)
theorem step_S'_even (n1 n2 c : Nat) (hp : P n1 (c + n2)) :
    (S' (n1 + c * 2 + 0)) [target_tm]⊢⁺ (S' (5 + n2 * 2 + c * 3)) := by
  unfold S'
  have h1 := hp (c * 2 + 0)
  have heq1 : n1 + (c * 2 + 0) = n1 + c * 2 + 0 := by omega
  rw [heq1] at h1
  have h2 := step_S1_iter c n2 2 0
  have h3 := step_S1_zero_right n2 (c * 3 + 2)
  have heq2 : 3 + n2 * 2 + (c * 3 + 2) = 5 + n2 * 2 + c * 3 := by omega
  rw [heq2] at h3
  exact reachesStar_reachesPlus_trans h1 (reachesStar_reachesPlus_trans h2 h3)
theorem step_S'_R1 (i n : Nat) (hn : 3 ^ i * 2 - i - 2 ≤ n /\ n ≤ 3 ^ i * 6 - i - 6)
    (hp : n % 2 = i % 2) :
    (S' n) [target_tm]⊢⁺ (S' ((n + (3 ^ i * 6 + i + 4)) / 2)) := by
  have hp3 := TrajectoryGraph.succ_le_three_pow i
  have hpn := P_n i
  set c := (n - (3 ^ i * 2 - i - 2)) / 2
  have hc_eq : c + (3 ^ i * 2 - 2 - c) = 3 ^ i * 2 - 2 := by omega
  rw [<- hc_eq] at hpn
  have hbs := step_S'_even (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 2 - c) c hpn
  have heq1 : 3 ^ i * 2 - i - 2 + c * 2 + 0 = n := by omega
  have heq2 : 5 + (3 ^ i * 2 - 2 - c) * 2 + c * 3 = (n + (3 ^ i * 6 + i + 4)) / 2 := by omega
  rw [heq1, heq2] at hbs
  exact hbs
theorem step_S'_R2 (i n : Nat) (hn : 3 ^ i * 2 - i ≤ n /\ n ≤ 3 ^ i * 6 - i - 10)
    (hp : n % 2 = (i + 1) % 2) :
    (S' n) [target_tm]⊢⁺ (S' (3 ^ i * 12 - 1)) := by
  have hp3 := TrajectoryGraph.succ_le_three_pow i
  have hpn := P_n i
  set c := (n - (3 ^ i * 2 - i - 2)) / 2
  have hc_eq : c + (2 + (3 ^ i * 2 - 4 - c)) = 3 ^ i * 2 - 2 := by omega
  rw [<- hc_eq] at hpn
  have hbs := step_S'_odd (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 4 - c) c hpn
  have heq1 : 3 ^ i * 2 - i - 2 + c * 2 + 1 = n := by omega
  have heq2 : 23 + (3 ^ i * 2 - 4 - c) * 6 + c * 6 = 3 ^ i * 12 - 1 := by omega
  rw [heq1, heq2] at hbs
  exact hbs
theorem step_S1_two (b : Nat) :
    (S1 0 b 2) [target_tm]⊢* (S1 0 2 (b + 4)) := by
  unfold S1
  simp only [rep11_zero, rep11_succ]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 :
    Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{B}}> rep01 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h2 := shift_B_rep01 b d0 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 :
    Fin 2) >> (1 : Fin 2) >> d0)
  have h3 : (rep01 b d0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin
    2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (rep01 (b + 1) d0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
        2) >> d0)) := by
    simp only [rep01_succ]
    execute
  have h4 := shift_C_rep01 (b + 1) d0 ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0)
  have h5 : (d0 <{{C}} rep01 (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> rep01 (b + 2) ((0 : Fin
        2) >> (1 : Fin 2) >> d0))) := by
    rw [rep01_succ_inner (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    execute
  have h6 := shift_A_rep01_to_rep11 (b + 2) d0 ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h7 : (rep11 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1
    : Fin 2) >> d0))
      [target_tm]⊢⁺ (rep11 (b + 5) d0 <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin
        2) >> d0)) := by
    simp only [rep11_succ]
    execute
  have h8 := shift_A_rep11 (b + 5) d0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0)
  have h9 : (d0 <{{A}} rep11 (b + 5) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
    d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> d0) <{{C}} rep01 2 (rep11 (b + 4) ((0 : Fin 2) >> (1 : Fin 2)
        >> d0))) := by
    rw [<- rep11_succ_inner (b + 5) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    simp only [rep11_succ, rep01_succ, rep01_zero]
    execute
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    (reachesPlus_to_reachesStar h3) (reachesStar_trans h4 (reachesStar_trans
    (reachesPlus_to_reachesStar h5) (reachesStar_trans h6 (reachesStar_trans
    (reachesPlus_to_reachesStar h7) (reachesStar_trans h8 (reachesPlus_to_reachesStar h9))))))))
theorem init_reaches_S'_18 : (init []) [target_tm]⊢* (S' 18) := by
  have h1 : (init []) [target_tm]⊢⁺ (S3 0 1) := by
    change (d0 {{A}}> d0) [target_tm]⊢⁺ (S3 0 1)
    unfold S3
    simp only [rep11_zero, rep01_succ, rep01_zero]
    execute
  have h2 := reachesPlus_to_reachesStar (Ov3 1)
  have h3 := reachesPlus_to_reachesStar (step_S'_R1 1 3 ⟨by decide, by decide⟩ (by decide))
  have h4 := step_S1_zero_left 2 10
  have h5 := step_S1_iter 4 0 2 2
  have h6 := step_S1_two 14
  exact reachesStar_trans (reachesPlus_to_reachesStar h1) (reachesStar_trans h2 (reachesStar_trans
    h3 (reachesStar_trans h4 (reachesStar_trans h5 h6))))
theorem reachesPlus_of_macroStep (x y : Nat) (h : TrajectoryGraph.MacroStep x y) :
    (S' x) [target_tm]⊢⁺ (S' y) := by
  cases h with
  | R1 i _ hn hp =>
    exact step_S'_R1 i x hn hp
  | R2 i _ hn hp =>
    have h1 := step_S'_R2 i x hn hp
    have heq : 3 ^ i * 12 - 1 = TrajectoryGraph.A (i + 1) := by
      unfold TrajectoryGraph.A
      rw [Nat.pow_succ]
      omega
    rw [heq] at h1
    exact h1
theorem reachesPlus_of_macroReaches (x y : Nat) (h : TrajectoryGraph.MacroReaches x y) :
    (S' x) [target_tm]⊢⁺ (S' y) := by
  induction h with
  | one x y hs => exact reachesPlus_of_macroStep x y hs
  | cons x y z hs _ ih => exact reachesPlus_trans (reachesPlus_of_macroStep x y hs) ih
theorem multiStep_isSome_of_add {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [multiStep_add_bind] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
theorem init_reaches_A_7 : (init []) [target_tm]⊢* (S' (TrajectoryGraph.A 7)) := by
  have h0 := init_reaches_S'_18
  have h1 := reachesPlus_to_reachesStar (step_S'_R1 2 18 ⟨by decide, by decide⟩ (by decide))
  have h2 := reachesPlus_to_reachesStar (step_S'_R2 2 39 ⟨by decide, by decide⟩ (by decide))
  have h3 := reachesPlus_to_reachesStar (step_S'_R1 3 107 ⟨by decide, by decide⟩ (by decide))
  have h4 := reachesPlus_to_reachesStar (step_S'_R2 3 138 ⟨by decide, by decide⟩ (by decide))
  have h5 := reachesPlus_to_reachesStar (step_S'_R2 4 323 ⟨by decide, by decide⟩ (by decide))
  have h6 := reachesPlus_to_reachesStar (step_S'_R1 5 971 ⟨by decide, by decide⟩ (by decide))
  have h7 := reachesPlus_to_reachesStar (step_S'_R1 5 1219 ⟨by decide, by decide⟩ (by decide))
  have h8 := reachesPlus_to_reachesStar (step_S'_R1 5 1343 ⟨by decide, by decide⟩ (by decide))
  have h9 := reachesPlus_to_reachesStar (step_S'_R1 5 1405 ⟨by decide, by decide⟩ (by decide))
  have h10 := reachesPlus_to_reachesStar (step_S'_R2 5 1436 ⟨by decide, by decide⟩ (by decide))
  have h11 := reachesPlus_to_reachesStar (step_S'_R2 6 2915 ⟨by decide, by decide⟩ (by decide))
  exact reachesStar_trans h0 (reachesStar_trans h1 (reachesStar_trans h2 (reachesStar_trans h3
    (reachesStar_trans h4 (reachesStar_trans h5 (reachesStar_trans h6 (reachesStar_trans h7
    (reachesStar_trans h8 (reachesStar_trans h9 (reachesStar_trans h10 h11))))))))))
theorem exists_unbounded_steps (hc : TrajectoryGraph.core) (m : Nat) :
    ∃ N ≥ m, ∃ k, multiStep target_tm (init []) N = some (S' (TrajectoryGraph.A (7 + k))) := by
  induction m with
  | zero =>
    obtain ⟨n0, hn0⟩ := init_reaches_A_7
    exact ⟨n0, Nat.zero_le n0, 0, hn0⟩
  | succ m ih =>
    obtain ⟨N, hN, k, h_ms⟩ := ih
    have hlayer := reachesPlus_of_macroReaches (TrajectoryGraph.A (7 + k)) (TrajectoryGraph.A (7 + k
      + 1)) (TrajectoryGraph.macroReaches_next_layer (7 + k) hc (by omega))
    obtain ⟨d, hd_pos, hd⟩ := hlayer
    refine ⟨N + d, by omega, k + 1, ?_⟩
    have heq : 7 + (k + 1) = 7 + k + 1 := by omega
    rw [heq]
    exact multiStep_trans_explicit target_tm _ _ _ N d h_ms hd
theorem nonhalt_of_core (hc : TrajectoryGraph.core) : IsDoesNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases exists_unbounded_steps hc (n + 1) with ⟨N, hN, k, h_N⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := multiStep_isSome_of_add h_N
  rw [multiStep_succ_bind, hn] at h_some
  exact h_some


end Solution

public section

/-- Main non-halting theorem for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
theorem is_not_halt : IsNotHalt target :=
  Solution.nonhalt_of_core (Solution.CoreBridge.core Solution.LargeExclusion.exclusion)

end

end BusyBeaver.Pomme.NonHalt
