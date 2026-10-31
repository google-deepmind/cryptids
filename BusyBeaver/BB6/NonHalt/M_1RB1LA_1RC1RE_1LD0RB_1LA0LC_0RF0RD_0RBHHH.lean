/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

namespace Solution

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

lemma dvd_add {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b + c := Int.dvd_add h1 h2
lemma dvd_sub {a b c : Int} (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ b - c := Int.dvd_sub h1 h2
lemma abs_mul (a b : Int) : |a * b| = |a| * |b| := by
  rcases le_or_gt 0 a with ha | ha <;> rcases le_or_gt 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_neg hb, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hb))]; ring
  · rw [abs_of_neg ha, abs_of_nonneg hb, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_lt ha) hb)]; ring
  · rw [abs_of_neg ha, abs_of_neg hb, abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos (le_of_lt ha) (le_of_lt hb))]; ring
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
namespace M4
def z0 : Nat -> (Nat -> Int) -> Nat -> Int
  | 0, f, x => f x
  | d + 1, f, x => z0 d f (x + 1) - z0 d f x
theorem z1 (d : Nat) (f g : Nat -> Int) (h : ∀ x, f x = g x) (x : Nat) :
    z0 d f x = z0 d g x := by
  induction d generalizing x with
  | zero => exact h x
  | succ d ih => simp [z0, ih]
theorem z2 (d : Nat) (f g : Nat -> Int) (x : Nat) :
    z0 d (fun x => f x + g x) x = z0 d f x + z0 d g x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [z0, ih]; ring
theorem z3 (d : Nat) (c : Int) (f : Nat -> Int) (x : Nat) :
    z0 d (fun x => c * f x) x = c * z0 d f x := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [z0, ih]; ring
theorem z4 (d : Nat) (f : Nat -> Int) (x : Nat) :
    z0 d (fun x => f (x + 1)) x = z0 d f (x + 1) := by
  induction d generalizing x with
  | zero => rfl
  | succ d ih => simp only [z0, ih]
theorem z5 (d : Nat) (f : Nat -> Int) (x : Nat) :
    z0 (d + 1) (fun x => (x : Int) * f x) x =
      (x : Int) * z0 (d + 1) f x + ((d + 1 : Nat) : Int) * z0 d f (x + 1) := by
  induction d generalizing x with
  | zero =>
    simp only [z0, Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    ring
  | succ d ih =>
    have h1 := ih (x + 1)
    have h2 := ih x
    have h3 : z0 (d + 1 + 1) (fun x => (x : Int) * f x) x =
        z0 (d + 1) (fun x => (x : Int) * f x) (x + 1) -
        z0 (d + 1) (fun x => (x : Int) * f x) x := rfl
    have h4 : z0 (d + 1 + 1) f x = z0 (d + 1) f (x + 1) - z0 (d + 1) f x := rfl
    have h5 : z0 (d + 1) f (x + 1) = z0 d f (x + 1 + 1) - z0 d f (x + 1) := rfl
    rw [h3, h1, h2, h4, h5]
    push_cast
    ring
theorem z6 (d : Nat) (q : Int) (x : Nat) :
    z0 d (fun x => q ^ x) x = (q - 1) ^ d * q ^ x := by
  induction d generalizing x with
  | zero => simp [z0]
  | succ d ih =>
    simp only [z0, ih, pow_succ]
    ring
theorem z7 (a b : Nat) (h : a ≤ b) : ((4 : Int) ^ a) ∣ ((4 : Int) ^ b) := by
  refine ⟨(4 : Int) ^ (b - a), ?_⟩
  rw [<- pow_add, Nat.add_sub_of_le h]
theorem z8 (q : Int) (hq : (4 : Int) ∣ (q - 1)) (k d x : Nat) :
    ((4 : Int) ^ (d - k)) ∣ z0 d (fun x => (x : Int) ^ k * q ^ x) x := by
  rcases hq with ⟨t, ht⟩
  induction k generalizing d x with
  | zero =>
    rw [Nat.sub_zero]
    have hext : (fun x : Nat => (x : Int) ^ 0 * q ^ x) = (fun x : Nat => q ^ x) := by
      funext y; ring
    rw [hext, z6, ht, mul_pow]
    refine ⟨t ^ d * q ^ x, ?_⟩
    ring
  | succ k ih =>
    cases d with
    | zero =>
      simp [z0]
    | succ d =>
      have hext : (fun x : Nat => (x : Int) ^ (k + 1) * q ^ x) =
          (fun x : Nat => (x : Int) * ((x : Int) ^ k * q ^ x)) := by
        funext y; rw [pow_succ]; ring
      rw [hext, z5, Nat.succ_sub_succ_eq_sub]
      apply dvd_add
      · apply dvd_mul_of_dvd_right
        exact dvd_trans (z7 (d - k) (d + 1 - k) (by omega)) (ih (d + 1) x)
      · apply dvd_mul_of_dvd_right
        exact ih d (x + 1)
def sum : Nat -> (Nat -> Int) -> Int
  | 0, _ => 0
  | n + 1, f => sum n f + f n
theorem z9 (n : Nat) (f g : Nat -> Int) (h : ∀ k, k < n -> f k = g k) :
    sum n f = sum n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [sum]
    rw [ih (fun k hk => h k (by omega)), h n (by omega)]
theorem z10 (n : Nat) (f g : Nat -> Int) :
    sum n (fun k => f k + g k) = sum n f + sum n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [sum, ih]; ring
theorem z11 (n : Nat) (f : Nat -> Int) :
    sum (n + 1) f = f 0 + sum n (fun k => f (k + 1)) := by
  induction n with
  | zero => simp [sum]
  | succ n ih =>
    calc sum (n + 1 + 1) f = sum (n + 1) f + f (n + 1) := rfl
      _ = f 0 + sum n (fun k => f (k + 1)) + f (n + 1) := by rw [ih]
      _ = f 0 + sum (n + 1) (fun k => f (k + 1)) := by simp only [sum]; ring
def z12 : Nat -> Nat -> Int
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, d + 1 => z12 n d + z12 n (d + 1)
theorem z13 (n d : Nat) (h : n < d) : z12 n d = 0 := by
  induction n generalizing d with
  | zero =>
    cases d with
    | zero => omega
    | succ d => rfl
  | succ n ih =>
    cases d with
    | zero => omega
    | succ d =>
      simp only [z12]
      rw [ih d (by omega), ih (d + 1) (by omega)]
      ring
theorem z14 (n : Nat) : z12 n 0 = 1 := by
  cases n <;> rfl
theorem z15 (n : Nat) (f : Nat -> Int) :
    sum (n + 2) (fun k => z12 (n + 1) k * f k) =
      sum (n + 1) (fun k => z12 n k * f k) + sum (n + 1) (fun k => z12 n k * f (k + 1)) := by
  rw [z11 (n + 1) (fun k => z12 (n + 1) k * f k)]
  have hext : sum (n + 1) (fun k => z12 (n + 1) (k + 1) * f (k + 1)) =
      sum (n + 1) (fun k => z12 n k * f (k + 1) + z12 n (k + 1) * f (k + 1)) := by
    apply z9
    intro k _
    simp only [z12]
    ring
  rw [hext, z10]
  rw [z11 n (fun k => z12 n k * f k), z14, z14]
  have htail : sum (n + 1) (fun k => z12 n (k + 1) * f (k + 1)) =
      sum n (fun k => z12 n (k + 1) * f (k + 1)) + z12 n (n + 1) * f (n + 1) := rfl
  rw [htail, z13 n (n + 1) (by omega)]
  ring
theorem z16 (f : Nat -> Int) (n x : Nat) :
    f (x + n) = sum (n + 1) (fun d => z12 n d * z0 d f x) := by
  induction n generalizing x with
  | zero =>
    simp [sum, z12, z0]
  | succ n ih =>
    have h1 : x + (n + 1) = (x + 1) + n := by omega
    rw [h1, ih (x + 1), z15, <- z10]
    apply z9
    intro k _
    simp only [z0]
    ring
end M4
namespace M3
def lap {I : Type} : List I -> (I -> List I -> Int) -> Int
  | [], _ => 0
  | c :: cs, f => f c cs - lap cs (fun x xs => f x (c :: xs))
theorem z17 {I : Type} (z143 : List I) (f g : I -> List I -> Int)
    (h : ∀ c cs, f c cs = g c cs) : lap z143 f = lap z143 g := by
  induction z143 generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    simp only [lap, h]
theorem z18 {I : Type} (z143 : List I) : lap z143 (fun _ _ => 0) = 0 := by
  induction z143 with
  | nil => rfl
  | cons c cs ih => simp [lap, ih]
theorem z19 {I : Type} (z143 : List I) (f g : I -> List I -> Int) :
    lap z143 (fun c cs => f c cs + g c cs) = lap z143 f + lap z143 g := by
  induction z143 generalizing f g with
  | nil => rfl
  | cons c cs ih => simp only [lap, ih]; ring
theorem z20 {I : Type} (z143 : List I) (f g : I -> List I -> Int) :
    lap z143 (fun c cs => f c cs - g c cs) = lap z143 f - lap z143 g := by
  induction z143 generalizing f g with
  | nil => rfl
  | cons c cs ih => simp only [lap, ih]; ring
theorem z21 {I : Type} (z143 : List I) (a : Int) (f : I -> List I -> Int) :
    lap z143 (fun c cs => a * f c cs) = a * lap z143 f := by
  induction z143 generalizing f with
  | nil => simp [lap]
  | cons c cs ih => simp only [lap, ih]; ring
theorem z22 {I : Type} (z143 : List I) (F : I -> I -> List I -> Int) :
    lap z143 (fun c cs => lap cs (fun d ds => F c d ds)) =
      -lap z143 (fun d ds => lap ds (fun c cs => F c d cs)) := by
  induction z143 generalizing F with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap, z20]
    rw [ih (fun x y ys => F x y (c :: ys))]
    ring
theorem z23 {I : Type} (c x : I) (cs xs : List I) (h : (x :: xs).Perm cs) :
    (x :: c :: xs).Perm (c :: cs) :=
  (List.Perm.swap c x xs).trans (h.cons c)
theorem z24 {I : Type} (z143 : List I) (f g : I -> List I -> Int)
    (h : ∀ c cs, (c :: cs).Perm z143 -> f c cs = g c cs) : lap z143 f = lap z143 g := by
  induction z143 generalizing f g with
  | nil => rfl
  | cons c cs ih =>
    simp only [lap]
    rw [h c cs (List.Perm.refl _)]
    congr 1
    exact ih _ _ (fun x xs hxs => h x (c :: xs) (z23 c x cs xs hxs))
theorem z25 {I : Type} (z143 : List I) (f : I -> List I -> Int) (m : Int)
    (h : ∀ c cs, (c :: cs).Perm z143 -> m ∣ f c cs) : m ∣ lap z143 f := by
  induction z143 generalizing f with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap]
    apply dvd_sub
    · exact h c cs (List.Perm.refl _)
    · exact ih _ (fun x xs hxs => h x (c :: xs) (z23 c x cs xs hxs))
theorem z26 {I : Type} (z143 : List I) (f : I -> List I -> Int) (b : Int) (_hb : 0 ≤ b)
    (h : ∀ c cs, (c :: cs).Perm z143 -> |f c cs| ≤ b) :
    |lap z143 f| ≤ (z143.length : Int) * b := by
  induction z143 generalizing f with
  | nil => simp [lap]
  | cons c cs ih =>
    simp only [lap, List.length_cons]
    have hhead : |f c cs| ≤ b := h c cs (List.Perm.refl _)
    have htail : |lap cs (fun x xs => f x (c :: xs))| ≤ (cs.length : Int) * b :=
      ih _ (fun x xs hxs => h x (c :: xs) (z23 c x cs xs hxs))
    have habs : |f c cs - lap cs (fun x xs => f x (c :: xs))| ≤
        |f c cs| + |lap cs (fun x xs => f x (c :: xs))| := abs_sub _ _
    push_cast
    linarith
def det {I : Type} : List (I -> Int) -> List I -> Int
  | [], _ => 1
  | r :: rs, z143 => lap z143 (fun c cs => r c * det rs cs)
theorem z27 {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    det (pre ++ (fun c => r c + s c) :: post) z143 =
      det (pre ++ r :: post) z143 + det (pre ++ s :: post) z143 := by
  induction pre generalizing z143 with
  | nil =>
    simp only [List.nil_append, det, <- z19]
    apply z17; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, det, <- z19]
    apply z17; intro c cs; rw [ih]; ring
theorem z28 {I : Type} (pre : List (I -> Int)) (a : Int) (r : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    det (pre ++ (fun c => a * r c) :: post) z143 = a * det (pre ++ r :: post) z143 := by
  induction pre generalizing z143 with
  | nil =>
    simp only [List.nil_append, det, <- z21]
    apply z17; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, det, <- z21]
    apply z17; intro c cs; rw [ih]; ring
theorem z29 {I : Type} (pre post : List (I -> Int)) (z143 : List I) :
    det (pre ++ (fun _ => 0) :: post) z143 = 0 := by
  have h : (fun _ : I => (0 : Int)) = (fun _ : I => 0 * (0 : Int)) := by funext _; ring
  rw [h, z28]; ring
theorem z30 {I : Type} (r s : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    det (r :: s :: post) z143 = -det (s :: r :: post) z143 := by
  simp only [det]
  rw [z17 z143 (fun c cs => r c * lap cs (fun d ds => s d * det post ds))
    (fun c cs => lap cs (fun d ds => r c * (s d * det post ds)))
    (fun c cs => (z21 cs (r c) _).symm)]
  rw [z22]
  congr 1
  apply z17; intro c cs
  rw [<- z21]
  apply z17; intro d ds; ring
theorem z31 {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    det (pre ++ r :: s :: post) z143 = -det (pre ++ s :: r :: post) z143 := by
  induction pre generalizing z143 with
  | nil => exact z30 r s post z143
  | cons t pre ih =>
    simp only [List.cons_append, det]
    have h : -lap z143 (fun c cs => t c * det (pre ++ s :: r :: post) cs) =
        (-1) * lap z143 (fun c cs => t c * det (pre ++ s :: r :: post) cs) := by ring
    rw [h, <- z21]
    apply z17; intro c cs; rw [ih]; ring
theorem z32 {I : Type} (pre mid : List (I -> Int)) (r : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    det (pre ++ r :: mid ++ r :: post) z143 = 0 := by
  have hbase : ∀ (ms : List (I -> Int)) (cs : List I), det (r :: ms ++ r :: post) cs = 0 := by
    intro ms
    induction ms with
    | nil =>
      intro cs
      have h := z30 r r post cs
      change det (r :: r :: post) cs = 0
      linarith
    | cons s ms ih =>
      intro cs
      change det (r :: s :: (ms ++ r :: post)) cs = 0
      rw [z30]
      change -lap cs (fun c xs => s c * det (r :: ms ++ r :: post) xs) = 0
      rw [z17 cs (fun c xs => s c * det (r :: ms ++ r :: post) xs) (fun _ _ => 0)
        (fun c xs => by dsimp -failIfUnchanged only; rw [ih xs]; ring)]
      rw [z18]; ring
  induction pre generalizing z143 with
  | nil =>
    simp only [List.nil_append]
    exact hbase mid z143
  | cons s pre ih =>
    simp only [List.cons_append, det]
    rw [z17 z143 (fun c xs => s c * det (pre ++ r :: mid ++ r :: post) xs) (fun _ _ => 0)
      (fun c xs => by dsimp -failIfUnchanged only; rw [ih xs]; ring)]
    exact z18 z143
theorem z33 {I : Type} (c : I) (cs z143 : List I) (h : (c :: cs).Perm z143) :
    c ∈ z143 /\ ∀ x ∈ cs, x ∈ z143 :=
  ⟨h.subset (by simp), fun x hx => h.subset (by simp [hx])⟩
theorem z34 {I : Type} (m : Int) (z142 z142' : List (I -> Int)) (z143 : List I)
    (h : List.Forall₂ (fun r s => ∀ c ∈ z143, m ∣ (r c - s c)) z142 z142') :
    m ∣ (det z142 z143 - det z142' z143) := by
  induction z142 generalizing z142' z143 with
  | nil =>
    cases h
    simp [det]
  | cons r rs ih =>
    cases h with
    | @cons _ s _ ss hr hrs =>
      simp only [det, <- z20]
      apply z25
      intro c cs hp
      obtain ⟨hc, hcs⟩ := z33 c cs z143 hp
      rcases hr c hc with ⟨a, ha⟩
      have htail : m ∣ (det rs cs - det ss cs) :=
        ih ss cs (hrs.imp (fun _ _ huv d hd => huv d (hcs d hd)))
      rcases htail with ⟨b, hb⟩
      refine ⟨r c * b + a * det ss cs, ?_⟩
      have h1 : s c = r c - m * a := by linarith
      have h2 : det ss cs = det rs cs - m * b := by linarith
      rw [h1, h2]; ring
theorem z35 {I : Type} (z142 z142' : List (I -> Int)) (z143 : List I)
    (h : List.Forall₂ (fun r s => ∀ c ∈ z143, r c = s c) z142 z142') :
    det z142 z143 = det z142' z143 := by
  have hz : (0 : Int) ∣ (det z142 z143 - det z142' z143) := by
    apply z34
    exact h.imp (fun r s hrs c hc => by rw [hrs c hc]; simp)
  rcases hz with ⟨k, hk⟩
  linarith
def z36 : List Int -> Int
  | [] => 1
  | x :: xs => x * z36 xs
theorem z37 (xs : List Int) (h : ∀ x ∈ xs, 0 ≤ x) : 0 ≤ z36 xs := by
  induction xs with
  | nil => simp [z36]
  | cons x xs ih =>
    simp only [z36]
    exact mul_nonneg (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
def z38 {I : Type} (z143 : List I) (z142 : List (I -> Int)) (bounds : List Int) : Prop :=
  List.Forall₂ (fun r b => 0 ≤ b /\ ∀ c ∈ z143, |r c| ≤ b) z142 bounds
theorem z39 {I : Type} (z143 : List I) (z142 : List (I -> Int)) (bounds : List Int)
    (h : z38 z143 z142 bounds) : ∀ b ∈ bounds, 0 ≤ b := by
  induction h with
  | nil => intro b hb; cases hb
  | @cons r b rs bs hrb _ ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hmem
    · exact hrb.1
    · exact ih x hmem
theorem z40 {I : Type} (z143 cs : List I) (z142 : List (I -> Int)) (bounds : List Int)
    (hcs : ∀ x ∈ cs, x ∈ z143) (h : z38 z143 z142 bounds) : z38 cs z142 bounds :=
  h.imp (fun _ _ hrb => ⟨hrb.1, fun c hc => hrb.2 c (hcs c hc)⟩)
theorem z41 {I : Type} (z142 : List (I -> Int)) (z143 : List I) (bounds : List Int)
    (hlen : z142.length = z143.length) (hbounds : z38 z143 z142 bounds) :
    |det z142 z143| ≤ (z142.length.factorial : Int) * z36 bounds := by
  induction z142 generalizing z143 bounds with
  | nil =>
    cases hbounds
    simp [det, z36]; decide
  | cons r rs ih =>
    cases hbounds with
    | @cons _ b _ bs hrb hrs =>
      simp only [det, List.length_cons, Nat.factorial_succ, z36]
      have hprod : 0 ≤ z36 bs := z37 bs (z39 z143 rs bs hrs)
      have hfact : (0 : Int) ≤ (rs.length.factorial : Int) := Nat.cast_nonneg _
      have hstep1 : |lap z143 (fun c cs => r c * det rs cs)| ≤
          (z143.length : Int) * (b * ((rs.length.factorial : Int) * z36 bs)) := by
        apply z26
        · exact mul_nonneg hrb.1 (mul_nonneg hfact hprod)
        · intro c cs hp
          obtain ⟨hc, hcs⟩ := z33 c cs z143 hp
          have hcslen : rs.length = cs.length := by
            have hp_len := hp.length_eq
            simp only [List.length_cons] at hp_len hlen
            omega
          have hd := ih cs bs hcslen (z40 z143 cs rs bs hcs hrs)
          rw [abs_mul]
          exact mul_le_mul (hrb.2 c hc) hd (abs_nonneg _) hrb.1
      have hstep2 : (z143.length : Int) * (b * ((rs.length.factorial : Int) * z36 bs)) =
          (((rs.length + 1) * rs.length.factorial : Nat) : Int) * (b * z36 bs) := by
        rw [<- hlen]
        simp only [List.length_cons]
        push_cast
        ring
      linarith
theorem z42 (n : Nat) (a : Int) (f : Nat -> Int) :
    M4.sum n (fun d => a * f d) = a * M4.sum n f := by
  induction n with
  | zero => simp [M4.sum]
  | succ n ih => simp only [M4.sum, ih]; ring
theorem z43 (n : Nat) (m : Int) (f : Nat -> Int)
    (h : ∀ d, d < n -> m ∣ f d) : m ∣ M4.sum n f := by
  induction n with
  | zero => simp [M4.sum]
  | succ n ih =>
    simp only [M4.sum]
    exact dvd_add (ih (fun d hd => h d (by omega))) (h n (by omega))
theorem z44 {I : Type} (pre : List (I -> Int)) (n : Nat) (f : Nat -> I -> Int)
    (post : List (I -> Int)) (z143 : List I) :
    det (pre ++ (fun c => M4.sum n (fun d => f d c)) :: post) z143 =
      M4.sum n (fun d => det (pre ++ f d :: post) z143) := by
  induction n with
  | zero => exact z29 pre post z143
  | succ n ih =>
    simp only [M4.sum]
    rw [z27, ih]
def z45 {J : Type} (coef : J -> Nat -> Int) : List J -> List Nat -> Int
  | [], [] => 1
  | r :: rs, d :: ds => coef r d * z45 coef rs ds
  | _, _ => 0
theorem z46 {I J : Type} (coef : J -> Nat -> Int) (basis : Nat -> I -> Int)
    (D : Nat) (m : Int) (z142 : List J) (pre : List (I -> Int)) (z143 : List I) (a : Int)
    (h : ∀ ds : List Nat, ds.length = z142.length -> (∀ d ∈ ds, d < D) ->
      m ∣ (a * z45 coef z142 ds * det (pre ++ ds.map basis) z143)) :
    m ∣ (a * det (pre ++ z142.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143) := by
  induction z142 generalizing pre a with
  | nil =>
    have h0 := h [] rfl (by intro d hd; cases hd)
    simp only [List.map_nil, z45, mul_one] at h0 ⊢
    exact h0
  | cons r rs ih =>
    simp only [List.map_cons]
    rw [z44, <- z42]
    apply z43
    intro d hd
    rw [z28]
    have heq : a * (coef r d * det (pre ++ basis d :: rs.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143) =
        (a * coef r d) * det ((pre ++ [basis d]) ++ rs.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143 := by
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
    simp only [z45, List.map_cons, List.append_assoc, List.singleton_append] at hstep ⊢
    have hmul : a * coef r d * z45 coef rs ds * det (pre ++ basis d :: ds.map basis) z143 =
        a * (coef r d * z45 coef rs ds) * det (pre ++ basis d :: ds.map basis) z143 := by ring
    rw [hmul]
    exact hstep
theorem z47 {α : Type} {x : α} {l : List α} (h : x ∈ l) :
    ∃ pre post : List α, l = pre ++ x :: post := by
  induction l with
  | nil => cases h
  | cons y ys ih =>
    rcases List.mem_cons.mp h with rfl | hmem
    · exact ⟨[], ys, rfl⟩
    · obtain ⟨pre, post, rfl⟩ := ih hmem
      exact ⟨y :: pre, post, rfl⟩
theorem z48 {I : Type} (basis : Nat -> I -> Int) (ds : List Nat) (z143 : List I)
    (h : ¬ ds.Nodup) : det (ds.map basis) z143 = 0 := by
  induction ds generalizing z143 with
  | nil => exact absurd (by simp) h
  | cons d ds ih =>
    by_cases hin : d ∈ ds
    · obtain ⟨pre, post, rfl⟩ := z47 hin
      have hmap : (d :: (pre ++ d :: post)).map basis =
          [] ++ basis d :: pre.map basis ++ basis d :: post.map basis := by simp
      rw [hmap]
      exact z32 [] (pre.map basis) (basis d) (post.map basis) z143
    · have hds : ¬ ds.Nodup := fun hnd => h (List.Nodup.cons hin hnd)
      simp only [List.map_cons, det]
      rw [z17 z143 _ (fun _ _ => 0) (fun c cs => by dsimp -failIfUnchanged only; rw [ih cs hds, mul_zero])]
      exact z18 z143
end M3
namespace M10
def z49 : List Nat -> Nat
  | [] => 0
  | d :: ds => d + z49 ds
def z50 (ds : List Nat) : Int := (z49 ds : Int)
@[simp] theorem z51 : z50 [] = 0 := rfl
@[simp] theorem z52 (d : Nat) (ds : List Nat) :
    z50 (d :: ds) = (d : Int) + z50 ds := by
  simp [z50, z49, Nat.cast_add]
theorem z53 (ds es : List Nat) (h : ds.Perm es) : z50 ds = z50 es := by
  induction h with
  | nil => rfl
  | cons x _ ih => simp only [z52, ih]
  | swap x y l => simp only [z52]; ring
  | trans _ _ ih1 ih2 => rw [ih1, ih2]
theorem z54 (ds : List Nat) : 0 ≤ z50 ds := Nat.cast_nonneg _
theorem z55 (ds : List Nat) (h : ds ≠ []) :
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
theorem z56 (ds : List Nat) (hnd : ds.Nodup) (hpos : ∀ d ∈ ds, 0 < d) :
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
theorem z57 (ds : List Nat) (hpos : ∀ d ∈ ds, 0 < d) :
    z50 ds = z50 (ds.map Nat.pred) + (ds.length : Int) := by
  induction ds with
  | nil => simp
  | cons x xs ih =>
    simp only [z52, List.map_cons, List.length_cons]
    have hx : 0 < x := hpos x (by simp)
    have hih := ih (fun d hd => hpos d (by simp [hd]))
    have hpred : (x : Int) = (x.pred : Int) + 1 := by
      simp only [Nat.pred_eq_sub_one]
      omega
    push_cast
    linarith
theorem z58 (ds : List Nat) (hdup : ds.Nodup) :
    (ds.length : Int) * ((ds.length : Int) - 1) ≤ 2 * z50 ds := by
  generalize hlen : ds.length = n
  induction n generalizing ds with
  | zero =>
    cases ds with
    | nil => simp
    | cons _ _ => simp at hlen
  | succ n ih =>
    have hne : ds ≠ [] := by
      intro h; subst h; simp at hlen
    obtain ⟨d, es, hp, hmin⟩ := z55 ds hne
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
    have hlow := ih (es.map Nat.pred) (z56 es hdup' hpos) (by simp [hlen'])
    rw [z53 ds (d :: es) hp, z52, z57 es hpos, hlen']
    have hd0 : (0 : Int) ≤ (d : Int) := Nat.cast_nonneg _
    push_cast
    linarith
theorem z59 (ds : List Nat) (K : Nat) :
    z50 ds - (ds.length : Int) * (K : Int) ≤ z50 (ds.map (fun d => d - K)) := by
  induction ds with
  | nil => simp
  | cons a ds ih =>
    simp only [z52, List.map_cons, List.length_cons]
    have ha : (a : Int) - (K : Int) ≤ ((a - K : Nat) : Int) := by omega
    push_cast
    linarith
end M10
namespace M2
theorem z60 (a b : Nat) (h : a ≤ b) : ((2 : Int) ^ a) ∣ ((2 : Int) ^ b) := by
  refine ⟨(2 : Int) ^ (b - a), ?_⟩
  rw [<- pow_add, Nat.add_sub_of_le h]
theorem z61 {J : Type} (coef : J -> Nat -> Int) (K : Nat) (z142 : List J) (ds : List Nat)
    (hlen : ds.length = z142.length)
    (hcoef : ∀ r ∈ z142, ∀ d, ((4 : Int) ^ (d - K)) ∣ coef r d) :
    ((4 : Int) ^ (M10.z49 (ds.map (fun d => d - K)))) ∣ M3.z45 coef z142 ds := by
  induction z142 generalizing ds with
  | nil =>
    cases ds with
    | nil => simp [M3.z45, M10.z49]
    | cons _ _ => simp at hlen
  | cons r rs ih =>
    cases ds with
    | nil => simp at hlen
    | cons d ds =>
      simp only [List.map_cons, M10.z49, M3.z45, pow_add]
      rcases hcoef r (by simp) d with ⟨a, ha⟩
      have hih := ih ds (by simp at hlen; exact hlen) (fun s hs => hcoef s (by simp [hs]))
      rcases hih with ⟨b, hb⟩
      refine ⟨a * b, ?_⟩
      rw [ha, hb]; ring
theorem z62 {I J : Type} (coef : J -> Nat -> Int) (basis : Nat -> I -> Int)
    (K D e : Nat) (z142 : List J) (z143 : List I)
    (he : (e : Int) ≤ (z142.length : Int) * ((z142.length : Int) - 1 - 2 * (K : Int)))
    (hcoef : ∀ r ∈ z142, ∀ d, ((4 : Int) ^ (d - K)) ∣ coef r d) :
    ((2 : Int) ^ e) ∣ M3.det (z142.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143 := by
  have h1 : M3.det (z142.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143 =
      1 * M3.det ([] ++ z142.map (fun r c => M4.sum D (fun d => coef r d * basis d c))) z143 := by
    simp
  rw [h1]
  apply M3.z46
  intro ds hlen _
  simp only [List.nil_append, one_mul]
  by_cases hnd : ds.Nodup
  · have hsum := M10.z58 ds hnd
    have hcost := M10.z59 ds K
    have hexp : e ≤ 2 * M10.z49 (ds.map (fun d => d - K)) := by
      rw [hlen] at hsum hcost
      unfold M10.z50 at hsum hcost
      have hlin : (z142.length : Int) * ((z142.length : Int) - 1 - 2 * (K : Int)) =
          (z142.length : Int) * ((z142.length : Int) - 1) - 2 * ((z142.length : Int) * (K : Int)) := by ring
      have hexp_int : (e : Int) ≤ 2 * (M10.z49 (ds.map (fun d => d - K)) : Int) := by linarith
      omega
    have hweight : ((2 : Int) ^ e) ∣ M3.z45 coef z142 ds := by
      apply dvd_trans (z60 e (2 * M10.z49 (ds.map (fun d => d - K))) hexp)
      have h4 : ((2 : Int) ^ (2 * M10.z49 (ds.map (fun d => d - K)))) =
          ((4 : Int) ^ (M10.z49 (ds.map (fun d => d - K)))) := by
        rw [pow_mul]
        rfl
      rw [h4]
      exact z61 coef K z142 ds hlen hcoef
    exact dvd_mul_of_dvd_left hweight _
  · rw [M3.z48 basis ds z143 hnd, mul_zero]
    exact dvd_zero _
theorem z63 (n m : Nat) (f : Nat -> Int) (hnm : n ≤ m)
    (hz : ∀ d, n ≤ d /\ d < m -> f d = 0) :
    M4.sum m f = M4.sum n f := by
  induction m with
  | zero =>
    have : n = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hne : n = m + 1
    · subst hne; rfl
    · simp only [M4.sum]
      rw [hz m ⟨by omega, by omega⟩, ih (by omega) (fun d hd => hz d ⟨hd.1, by omega⟩), add_zero]
theorem z64 (f : Nat -> Int) (D x : Nat) (hx : x < D) :
    f x = M4.sum D (fun d => M4.z0 d f 0 * M4.z12 x d) := by
  have h := M4.z16 f x 0
  rw [Nat.zero_add] at h
  rw [h, z63 (x + 1) D (fun d => M4.z0 d f 0 * M4.z12 x d) (by omega)]
  · apply M4.z9
    intro k _; ring
  · intro d hd
    rw [M4.z13 x d (by omega), mul_zero]
theorem z65 (K e : Nat) (z142 : List (Nat × Int)) (z143 : List Nat)
    (he : (e : Int) ≤ (z142.length : Int) * ((z142.length : Int) - 1 - 2 * (K : Int)))
    (hrows : ∀ k q, (k, q) ∈ z142 -> k ≤ K /\ ((4 : Int) ∣ (q - 1))) :
    ((2 : Int) ^ e) ∣ M3.det (z142.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) z143 := by
  let D := z143.foldr Nat.max 0 + 1
  have hcols : ∀ x ∈ z143, x < D := by
    change ∀ x ∈ z143, x < z143.foldr Nat.max 0 + 1
    induction z143 with
    | nil => intro x hx; cases hx
    | cons y ys ih =>
      intro x hx
      simp only [List.foldr_cons]
      have h1 : y ≤ Nat.max y (ys.foldr Nat.max 0) := Nat.le_max_left y _
      have h2 : ys.foldr Nat.max 0 ≤ Nat.max y (ys.foldr Nat.max 0) := Nat.le_max_right y _
      rcases List.mem_cons.mp hx with rfl | hmem
      · omega
      · have := ih x hmem; omega
  have hext : M3.det (z142.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) z143 =
      M3.det (z142.map (fun p (x : Nat) => M4.sum D (fun d =>
        M4.z0 d (fun (y : Nat) => (y : Int) ^ p.1 * p.2 ^ y) 0 * M4.z12 x d))) z143 := by
    apply M3.z35
    rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact List.forall₂_same.mpr (fun p _ x hx => z64 (fun (y : Nat) => (y : Int) ^ p.1 * p.2 ^ y) D x (hcols x hx))
  rw [hext]
  apply z62 _ (fun d x => M4.z12 x d) K D e z142 z143 he
  intro ⟨k, q⟩ hp d
  obtain ⟨hk, hq⟩ := hrows k q hp
  exact dvd_trans (M4.z7 (d - K) (d - k) (by omega))
    (M4.z8 q hq k d 0)
end M2
namespace M14
theorem z66 {I : Type} (pre : List (I -> Int)) (r s : I -> Int) (post : List (I -> Int)) (z143 : List I) :
    M3.det (pre ++ (fun c => r c - s c) :: post) z143 =
      M3.det (pre ++ r :: post) z143 - M3.det (pre ++ s :: post) z143 := by
  induction pre generalizing z143 with
  | nil =>
    simp only [List.nil_append, M3.det, <- M3.z20]
    apply M3.z17; intro c cs; ring
  | cons t pre ih =>
    simp only [List.cons_append, M3.det, <- M3.z20]
    apply M3.z17; intro c cs; rw [ih]; ring
theorem z67 {I : Type} (z142 : List (I -> Int)) (c : I) (z143 : List I)
    (hlen : z142.length = z143.length + 1) (hz : ∀ r ∈ z142, r c = 0) :
    M3.det z142 (c :: z143) = 0 := by
  induction z142 generalizing c z143 with
  | nil => simp at hlen
  | cons r rs ih =>
    simp only [M3.det, M3.lap]
    rw [hz r (by simp), zero_mul, zero_sub, neg_eq_zero]
    rw [M3.z24 z143 (fun d ds => r d * M3.det rs (c :: ds)) (fun _ _ => 0)]
    · exact M3.z18 z143
    · intro d ds hp
      have hp_len := hp.length_eq
      simp only [List.length_cons] at hlen hp_len
      rw [ih c ds (by omega) (fun s hs => hz s (by simp [hs])), mul_zero]
theorem z68 {I : Type} (r : I -> Int) (rs : List (I -> Int)) (c : I) (z143 : List I)
    (hlen : rs.length = z143.length) (hz : ∀ s ∈ rs, s c = 0) :
    M3.det (r :: rs) (c :: z143) = r c * M3.det rs z143 := by
  simp only [M3.det, M3.lap]
  rw [M3.z24 z143 (fun d ds => r d * M3.det rs (c :: ds)) (fun _ _ => 0)]
  · rw [M3.z18]; ring
  · intro d ds hp
    have hp_len := hp.length_eq
    simp only [List.length_cons] at hp_len
    rw [z67 rs c ds (by omega) hz, mul_zero]
theorem z69 {I : Type} (r s : I -> Int) (a b : Int) (pre post : List (I -> Int)) (z143 : List I) :
    M3.det (r :: (pre ++ (fun x => a * s x - b * r x) :: post)) z143 =
      a * M3.det (r :: (pre ++ s :: post)) z143 := by
  change M3.det ((r :: pre) ++ (fun x => a * s x - b * r x) :: post) z143 =
    a * M3.det ((r :: pre) ++ s :: post) z143
  rw [z66, M3.z28, M3.z28]
  have hzero := M3.z32 [] pre r post z143
  simp only [List.nil_append] at hzero
  change M3.det ((r :: pre) ++ r :: post) z143 = 0 at hzero
  rw [hzero]; ring
theorem z70 {I : Type} (r : I -> Int) (c : I) (a : Int) (rs pre : List (I -> Int)) (z143 : List I) :
    M3.det (r :: (pre ++ rs.map (fun s x => a * s x - s c * r x))) z143 =
      a ^ rs.length * M3.det (r :: (pre ++ rs)) z143 := by
  induction rs generalizing pre z143 with
  | nil => simp
  | cons s rs ih =>
    simp only [List.map_cons, List.length_cons]
    rw [z69]
    have h1 : pre ++ s :: rs.map (fun s x => a * s x - s c * r x) =
        (pre ++ [s]) ++ rs.map (fun s x => a * s x - s c * r x) := by simp
    have h2 : pre ++ s :: rs = (pre ++ [s]) ++ rs := by simp
    rw [h1, ih (pre ++ [s]) z143, h2, pow_succ]
    ring
def z71 {I : Type} : List (I -> Int) -> List Int -> I -> Int
  | r :: rs, w :: ws, c => w * r c + z71 rs ws c
  | _, _, _ => 0
theorem z72 {I : Type} (z142 : List (I -> Int)) (c : I) :
    z71 z142 (List.replicate z142.length 0) c = 0 := by
  induction z142 with
  | nil => rfl
  | cons r rs ih => simp [List.replicate_succ, z71, ih]
theorem z73 {I : Type} (z142 : List (I -> Int)) (ws : List Int) (a : Int) (c : I) :
    z71 z142 (ws.map (fun w => a * w)) c = a * z71 z142 ws c := by
  induction z142 generalizing ws with
  | nil => simp [z71]
  | cons r rs ih =>
    cases ws with
    | nil => simp [z71]
    | cons w ws => simp only [List.map_cons, z71, ih]; ring
theorem z74 {I : Type} (z142 : List (I -> Int)) (ws : List Int)
    (r : I -> Int) (c : I) (a : Int) (x : I) :
    z71 (z142.map (fun s x => a * s x - s c * r x)) ws x =
      a * z71 z142 ws x - r x * z71 z142 ws c := by
  induction z142 generalizing ws with
  | nil => simp [z71]
  | cons s rs ih =>
    cases ws with
    | nil => simp [z71]
    | cons w ws => simp only [List.map_cons, z71, ih]; ring
def z75 {I : Type} (z142 : List (I -> Int)) (z143 : List I) : Prop :=
  ∀ ws : List Int, ws.length = z142.length ->
    (∀ c ∈ z143, z71 z142 ws c = 0) ->
    ∀ w ∈ ws, w = 0
theorem z76 {I : Type} (r : I -> Int) (rs : List (I -> Int)) (z143 : List I)
    (hind : z75 (r :: rs) z143) : ∃ c ∈ z143, r c ≠ 0 := by
  by_contra h
  push Not at h
  have hbad := hind (1 :: List.replicate rs.length 0) (by simp) (by
    intro c hc
    simp only [z71, z72, h c hc]
    ring)
  have h1 : (1 : Int) = 0 := hbad 1 (by simp)
  omega
theorem z77 {I : Type} (r : I -> Int) (rs : List (I -> Int)) (z143 : List I) (c : I)
    (hind : z75 (r :: rs) z143) (hc : r c ≠ 0) :
    z75 (rs.map (fun s x => r c * s x - s c * r x)) z143 := by
  intro ws hlen hz
  rw [List.length_map] at hlen
  have hrel := hind (-z71 rs ws c :: ws.map (fun w => r c * w))
    (by simp [hlen])
    (by
      intro x hx
      have hzx := hz x hx
      rw [z74] at hzx
      simp only [z71, z73]
      linarith)
  intro w hw
  have hmem : r c * w ∈ -z71 rs ws c :: ws.map (fun w => r c * w) :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, hw, rfl⟩)
  have hmul : r c * w = 0 := hrel (r c * w) hmem
  rcases mul_eq_zero.mp hmul with hrc | hw0
  · exact absurd hrc hc
  · exact hw0
theorem z78 {I : Type} (z142 : List (I -> Int)) (z143 : List I)
    (hind : z75 z142 z143) :
    ∃ cs : List I, cs.length = z142.length /\ (∀ x ∈ cs, x ∈ z143) /\ M3.det z142 cs ≠ 0 := by
  generalize hlen : z142.length = n
  induction n generalizing z142 with
  | zero =>
    cases z142 with
    | nil =>
      refine ⟨[], rfl, ?_, by simp [M3.det]⟩
      intro x hx; cases hx
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases z142 with
    | nil => simp at hlen
    | cons r rs =>
      obtain ⟨c, hc, hr⟩ := z76 r rs z143 hind
      obtain ⟨cs, hcs, hin, hdet⟩ := ih (rs.map (fun s x => r c * s x - s c * r x))
        (z77 r rs z143 c hind hr)
        (by simp only [List.length_cons] at hlen; rw [List.length_map]; omega)
      refine ⟨c :: cs, by simp [hcs], ?_, ?_⟩
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact hc
        · exact hin x hmem
      · intro hzero
        have heq := z70 r c (r c) rs [] (c :: cs)
        simp only [List.nil_append] at heq
        rw [hzero, mul_zero] at heq
        rw [z68 r (rs.map (fun s x => r c * s x - s c * r x)) c cs
          (by simp only [List.length_cons] at hlen; simp [hcs]; omega)
          (by
            intro s hs
            rcases List.mem_map.mp hs with ⟨t, _, rfl⟩
            ring)] at heq
        rcases mul_eq_zero.mp heq with hrc | hdet0
        · exact hr hrc
        · exact hdet hdet0
theorem z79 {I : Type} (z142 : List (I -> Int)) (ws : List Int)
    (pre : List (I -> Int)) (z143 : List I) :
    M3.det (z71 z142 ws :: (pre ++ z142)) z143 = 0 := by
  induction z142 generalizing ws pre z143 with
  | nil =>
    have : z71 ([] : List (I -> Int)) ws = (fun _ => 0) := by funext _; rfl
    rw [this]
    exact M3.z29 [] (pre ++ []) z143
  | cons r rs ih =>
    cases ws with
    | nil =>
      have : z71 (r :: rs) [] = (fun _ => 0) := by funext _; rfl
      rw [this]
      exact M3.z29 [] (pre ++ r :: rs) z143
    | cons w ws =>
      change M3.det ([] ++ (fun c => w * r c + z71 rs ws c) :: (pre ++ r :: rs)) z143 = 0
      rw [M3.z27, M3.z28]
      have hr := M3.z32 [] pre r rs z143
      simp only [List.nil_append, List.cons_append] at hr ⊢
      rw [hr]
      have h1 : pre ++ r :: rs = (pre ++ [r]) ++ rs := by simp
      rw [h1, ih ws (pre ++ [r]) z143]
      ring
theorem z80 {I : Type} (r : I -> Int) (rs : List (I -> Int))
    (a : Int) (ws : List Int) (z143 : List I) (ha : a ≠ 0)
    (hrel : ∀ c ∈ z143, a * r c + z71 rs ws c = 0) :
    M3.det (r :: rs) z143 = 0 := by
  have hdet : M3.det ((fun c => a * r c + z71 rs ws c) :: rs) z143 = 0 := by
    rw [M3.z35 _ ((fun _ => 0) :: rs) z143]
    · exact M3.z29 [] rs z143
    · refine List.Forall₂.cons hrel ?_
      exact List.forall₂_same.mpr (fun _ _ _ _ => rfl)
  change M3.det ([] ++ (fun c => a * r c + z71 rs ws c) :: rs) z143 = 0 at hdet
  rw [M3.z27, M3.z28] at hdet
  have hzero := z79 rs ws [] z143
  simp only [List.nil_append] at hdet hzero
  rw [hzero, add_zero] at hdet
  rcases mul_eq_zero.mp hdet with ha0 | hr0
  · exact absurd ha0 ha
  · exact hr0
end M14
namespace M12
theorem z81 (a : Int) (n : Nat) :
    M3.z36 (List.replicate n a) = a ^ n := by
  induction n with
  | zero => simp [M3.z36]
  | succ n ih =>
    simp only [List.replicate_succ, M3.z36, ih]; ring
theorem z82 (n : Nat) (b : Int) (hb : 0 ≤ b) (hn : (n : Int) ≤ b) :
    (n.factorial : Int) ≤ b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.factorial_succ, Nat.cast_mul]
    calc ((n + 1 : Nat) : Int) * (n.factorial : Int)
      _ ≤ b * b ^ n := mul_le_mul hn (ih (by push_cast at hn; linarith)) (Nat.cast_nonneg _) hb
      _ = b ^ (n + 1) := by ring
theorem z83 {I : Type} (z142 : List (I -> Int)) (z143 : List I) (m b : Nat)
    (hlen : z142.length = z143.length)
    (hsize : z142.length ≤ 2 ^ m)
    (hrows : ∀ r ∈ z142, ∀ c ∈ z143, |r c| ≤ (2 : Int) ^ b) :
    |M3.det z142 z143| ≤ (2 : Int) ^ (z142.length * (m + b)) := by
  have hbounds : M3.z38 z143 z142 (List.replicate z142.length ((2 : Int) ^ b)) := by
    clear hlen hsize
    induction z142 with
    | nil => exact List.Forall₂.nil
    | cons r rs ih =>
      simp only [List.length_cons, List.replicate_succ]
      refine List.Forall₂.cons ⟨by positivity, hrows r (by simp)⟩ ?_
      exact ih (fun s hs => hrows s (by simp [hs]))
  have hdet := M3.z41 z142 z143 _ hlen hbounds
  rw [z81] at hdet
  have hsize' : (z142.length : Int) ≤ (2 : Int) ^ m := by exact_mod_cast hsize
  have hfact := z82 z142.length ((2 : Int) ^ m) (by positivity) hsize'
  have hp : (0 : Int) ≤ ((2 : Int) ^ b) ^ z142.length := by positivity
  have hmul := mul_le_mul_of_nonneg_right hfact hp
  have hpow : ((2 : Int) ^ m) ^ z142.length * ((2 : Int) ^ b) ^ z142.length =
      (2 : Int) ^ (z142.length * (m + b)) := by
    rw [<- pow_mul, <- pow_mul, <- pow_add]
    congr 1
    ring
  linarith
theorem z84 (D : Int) (U T : Nat)
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
theorem z85 {I J : Type} (f : I -> J) (cs : List I) (g : J -> List J -> Int) :
    M3.lap (cs.map f) g = M3.lap cs (fun c cs => g (f c) (cs.map f)) := by
  induction cs generalizing g with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.map_cons, M3.lap, ih]
theorem z86 {I J : Type} (f : I -> J) (z142 : List (J -> Int)) (cs : List I) :
    M3.det z142 (cs.map f) = M3.det (z142.map (fun r c => r (f c))) cs := by
  induction z142 generalizing cs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.map_cons, M3.det, z85]
    apply M3.z17
    intro c ds
    rw [ih]
end M12
namespace M18
def eval : List Int -> Int -> Int
  | [], _ => 0
  | a :: p, x => a + x * M18.eval p x
def z87 : List Int -> Int -> List Int
  | [], _ => []
  | _ :: [], _ => []
  | _ :: d :: ps, a => M18.eval (d :: ps) a :: z87 (d :: ps) a
theorem z88 (p : List Int) (a : Int) :
    (z87 p a).length = p.length - 1 := by
  induction p with
  | nil => rfl
  | cons c p ih =>
    cases p with
    | nil => rfl
    | cons d ps =>
      simp only [z87, List.length_cons, ih]
      omega
theorem z89 (p : List Int) (a x : Int) :
    M18.eval p x - M18.eval p a = (x - a) * M18.eval (z87 p a) x := by
  induction p with
  | nil => simp [M18.eval, z87]
  | cons c p ih =>
    cases p with
    | nil => simp [M18.eval, z87]
    | cons d ps =>
      simp only [M18.eval, z87] at ih ⊢
      have h1 : d + x * M18.eval ps x = d + a * M18.eval ps a + (x - a) * M18.eval (z87 (d :: ps) a) x := by linarith
      rw [h1]; ring
theorem z90 (p : List Int) (x : Int) (h : ∀ a ∈ p, a = 0) : M18.eval p x = 0 := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    simp only [M18.eval, h a (by simp), ih (fun b hb => h b (by simp [hb])), mul_zero, add_zero]
theorem z91 (p : List Int) (a : Int) (h : ∀ c ∈ z87 p a, c = 0) :
    ∀ c ∈ p.tail, c = 0 := by
  induction p with
  | nil => intro c hc; cases hc
  | cons c p ih =>
    cases p with
    | nil => intro x hx; cases hx
    | cons d ps =>
      simp only [z87] at h
      have hd : M18.eval (d :: ps) a = 0 := h (M18.eval (d :: ps) a) (by simp)
      have hps : ∀ x ∈ ps, x = 0 := ih (fun x hx => h x (by simp [hx]))
      simp only [M18.eval, z90 ps a hps, mul_zero, add_zero] at hd
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact hd
      · exact hps x hmem
theorem z92 (p roots : List Int) (hnd : roots.Nodup)
    (hz : ∀ x ∈ roots, M18.eval p x = 0) (hsize : p.length ≤ roots.length) :
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
        have ha : M18.eval (c :: p) a = 0 := hz a (by simp)
        have hquot : ∀ x ∈ z87 (c :: p) a, x = 0 := by
          apply ih (z87 (c :: p) a) rs hnd'
          · intro x hx
            have hq := z89 (c :: p) a x
            have hzx : M18.eval (c :: p) x = 0 := hz x (by simp [hx])
            rw [hzx, ha, sub_zero] at hq
            have hxa : x - a ≠ 0 := sub_ne_zero.mpr (fun h => hnot (h ▸ hx))
            rcases mul_eq_zero.mp hq.symm with h1 | h2
            · exact absurd h1 hxa
            · exact h2
          · rw [z88]
            simp only [List.length_cons] at hsize ⊢
            omega
          · rw [z88]
            simp only [List.length_cons] at hlen ⊢
            omega
        have hp : ∀ x ∈ p, x = 0 := z91 (c :: p) a hquot
        simp only [M18.eval, z90 p a hp, mul_zero, add_zero] at ha
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hmem
        · exact ha
        · exact hp x hmem
def add : List Int -> List Int -> List Int
  | [], q => q
  | p, [] => p
  | a :: ps, b :: qs => (a + b) :: add ps qs
def z93 (a : Int) (p : List Int) : List Int := p.map (a * ·)
def mul : List Int -> List Int -> List Int
  | [], _ => []
  | _, [] => []
  | a :: ps, q => add (z93 a q) (0 :: mul ps q)
theorem z94 (p q : List Int) (x : Int) : M18.eval (add p q) x = M18.eval p x + M18.eval q x := by
  induction p generalizing q with
  | nil => simp [add, M18.eval]
  | cons a p ih =>
    cases q with
    | nil => simp [add, M18.eval]
    | cons b q => simp only [add, M18.eval, ih]; ring
theorem z95 (a : Int) (p : List Int) (x : Int) : M18.eval (z93 a p) x = a * M18.eval p x := by
  induction p with
  | nil => simp [z93, M18.eval]
  | cons b p ih =>
    simp only [z93, List.map_cons, M18.eval]
    rw [ <- z93, ih]
    ring
theorem z96 (p q : List Int) (x : Int) : M18.eval (mul p q) x = M18.eval p x * M18.eval q x := by
  induction p generalizing q with
  | nil => simp [mul, M18.eval]
  | cons a p ih =>
    cases q with
    | nil => simp [mul, M18.eval]
    | cons b q =>
      simp only [mul, z94, z95, M18.eval, ih]
      ring
def z97 : List Int -> Int -> List Int
  | [], _ => []
  | c :: ps, a => add [c] (mul [a, 1] (z97 ps a))
theorem z98 (p : List Int) (a x : Int) : M18.eval (z97 p a) x = M18.eval p (x + a) := by
  induction p with
  | nil => rfl
  | cons c ps ih =>
    simp only [z97, z94, z96, ih, M18.eval]
    ring
def z99 (p : List Int) (n : Nat) : Int := p.getD n 0
@[simp] theorem z100 (n : Nat) : z99 [] n = 0 := by
  simp [z99]
@[simp] theorem z101 (a : Int) (p : List Int) : z99 (a :: p) 0 = a := by
  simp [z99]
@[simp] theorem z102 (a : Int) (p : List Int) (n : Nat) :
    z99 (a :: p) (n + 1) = z99 p n := by
  simp [z99]
theorem z103 (p : List Int) (n : Nat) (h : p.length ≤ n) : z99 p n = 0 := by
  induction p generalizing n with
  | nil => exact z100 n
  | cons a p ih =>
    cases n with
    | zero => simp at h
    | succ n =>
      rw [z102]
      exact ih n (by simp at h; omega)
theorem z104 (p : List Int) (n : Nat) (h : ∀ a ∈ p, a = 0) :
    z99 p n = 0 := by
  induction p generalizing n with
  | nil => exact z100 n
  | cons a p ih =>
    cases n with
    | zero => exact h a (by simp)
    | succ n => exact ih n (fun b hb => h b (by simp [hb]))
theorem z105 (p q : List Int) (n : Nat) :
    z99 (add p q) n = z99 p n + z99 q n := by
  induction p generalizing q n with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      cases n with
      | zero => simp [add]
      | succ n => simp only [add, z102, ih]
theorem z106 (a : Int) (p : List Int) (n : Nat) :
    z99 (z93 a p) n = a * z99 p n := by
  induction p generalizing n with
  | nil => simp [z93]
  | cons b p ih =>
    cases n with
    | zero => simp [z93]
    | succ n =>
      simp only [z93, List.map_cons, z102]
      exact ih n
theorem z107 (p q : List Int) : (add p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q =>
      simp only [add, List.length_cons, ih]
      omega
theorem z108 (a : Int) (p : List Int) : (z93 a p).length = p.length := by
  simp [z93]
theorem z109 (p q : List Int) : (mul p q).length ≤ p.length + q.length - 1 := by
  induction p generalizing q with
  | nil => simp [mul]
  | cons a p ih =>
    cases q with
    | nil => simp [mul]
    | cons b q =>
      simp only [mul, z107, z108, List.length_cons]
      have := ih (b :: q)
      simp only [List.length_cons] at this
      omega
theorem z110 (p : List Int) (a : Int) : (z97 p a).length ≤ p.length := by
  induction p with
  | nil => simp [z97]
  | cons c p ih =>
    simp only [z97, z107, List.length_cons, List.length_nil]
    have hmul := z109 [a, 1] (z97 p a)
    simp only [List.length_cons, List.length_nil] at hmul
    omega
theorem z111 (p q : List Int) (d e : Nat)
    (hp : p.length ≤ d + 1) (hq : q.length ≤ e + 1) :
    z99 (mul p q) (d + e) = z99 p d * z99 q e := by
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
          simp only [mul, z105, z106, Nat.zero_add, z101]
          have hz : z99 [0] e = 0 := by
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
        simp only [mul, z105, z106, z102]
        rw [z103 q (d + e) (by simp at hq; omega), mul_zero, zero_add]
        exact ih p (b :: q) (by simp at hp; omega) hq
theorem z112 (p : List Int) (a : Int) (d : Nat) (hp : p.length ≤ d + 1) :
    z99 (z97 p a) d = z99 p d := by
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
      simp only [z97, z105, z102, z100, zero_add]
      have h1 : d + 1 = 1 + d := by omega
      rw [h1, z111 [a, 1] (z97 p a) 1 d (by simp)
        (Nat.le_trans (z110 p a) (by simp at hp; omega))]
      have h2 : z99 [a, 1] 1 = 1 := rfl
      rw [h2, one_mul]
      exact ih p (by simp at hp; omega)
end M18
namespace M17
def z113 {I : Type} : List I -> (I -> List I -> List Int) -> List Int
  | [], _ => []
  | c :: cs, f => M18.add (f c cs) (M18.z93 (-1) (z113 cs (fun d ds => f d (c :: ds))))
theorem z114 {I : Type} (z143 : List I) (f : I -> List I -> List Int) (x : Int) :
    M18.eval (z113 z143 f) x = M3.lap z143 (fun c cs => M18.eval (f c cs) x) := by
  induction z143 generalizing f with
  | nil => rfl
  | cons c cs ih =>
    simp only [z113, M3.lap, M18.z94, M18.z95, ih]
    ring
theorem z115 {I : Type} (z143 : List I) (f : I -> List I -> List Int) (n : Nat) :
    M18.z99 (z113 z143 f) n = M3.lap z143 (fun c cs => M18.z99 (f c cs) n) := by
  induction z143 generalizing f with
  | nil => simp [z113, M3.lap]
  | cons c cs ih =>
    simp only [z113, M3.lap, M18.z105, M18.z106, ih]
    ring
theorem z116 {I : Type} (z143 : List I) (f : I -> List I -> List Int) (n : Nat)
    (h : ∀ c cs, (f c cs).length ≤ n) : (z113 z143 f).length ≤ n := by
  induction z143 generalizing f with
  | nil => simp [z113]
  | cons c cs ih =>
    simp only [z113, M18.z107, M18.z108]
    have h1 := h c cs
    have h2 := ih (fun d ds => f d (c :: ds)) (fun d ds => h d (c :: ds))
    omega
def z117 {I : Type} : List (Nat × (I -> List Int)) -> Nat
  | [] => 0
  | (d, _) :: rs => d + z117 rs
def z118 {I : Type} : List (Nat × (I -> List Int)) -> List I -> List Int
  | [], _ => [1]
  | (_, r) :: rs, z143 => z113 z143 (fun c cs => M18.mul (r c) (z118 rs cs))
def z119 {I : Type} (z142 : List (Nat × (I -> List Int))) : Prop :=
  ∀ p ∈ z142, ∀ c, (p.2 c).length ≤ p.1 + 1
theorem z120 {I : Type} (z142 : List (Nat × (I -> List Int))) (z143 : List I) (x : Int) :
    M18.eval (z118 z142 z143) x =
      M3.det (z142.map (fun p c => M18.eval (p.2 c) x)) z143 := by
  induction z142 generalizing z143 with
  | nil => simp [z118, M3.det, M18.eval]
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [z118, List.map_cons, M3.det, z114]
    apply M3.z17
    intro c cs
    rw [M18.z96, ih]
theorem z121 {I : Type} (z142 : List (Nat × (I -> List Int))) (h : z119 z142) (z143 : List I) :
    (z118 z142 z143).length ≤ z117 z142 + 1 := by
  induction z142 generalizing z143 with
  | nil => simp [z118, z117]
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [z118, z117]
    apply z116
    intro c cs
    have hmul := M18.z109 (r c) (z118 rs cs)
    have hr := h (d, r) (by simp) c
    simp only at hr
    have hrs := ih (fun q hq => h q (by simp [hq])) cs
    omega
theorem z122 {I : Type} (z142 : List (Nat × (I -> List Int))) (h : z119 z142) (z143 : List I) :
    M18.z99 (z118 z142 z143) (z117 z142) =
      M3.det (z142.map (fun p c => M18.z99 (p.2 c) p.1)) z143 := by
  induction z142 generalizing z143 with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨d, r⟩
    simp only [z118, z117, List.map_cons, M3.det, z115]
    apply M3.z17
    intro c cs
    have hvalid_rs : z119 rs := fun q hq => h q (by simp [hq])
    rw [M18.z111 (r c) (z118 rs cs) d (z117 rs)
      (h (d, r) (by simp) c) (z121 rs hvalid_rs cs)]
    rw [ih hvalid_rs cs]
end M17
namespace M20
theorem z123 {I J : Type} (xs : List I) (ys : List J) (F : I -> List I -> J -> List J -> Int) :
    M3.lap xs (fun x xs => M3.lap ys (fun y ys => F x xs y ys)) =
      M3.lap ys (fun y ys => M3.lap xs (fun x xs => F x xs y ys)) := by
  induction xs generalizing F with
  | nil =>
    simp only [M3.lap]
    exact (M3.z18 ys).symm
  | cons x xs ih =>
    simp only [M3.lap, ih, M3.z20]
theorem z124 {I J : Type} (M : J -> I -> Int) (xs : List J) (y : I) (ys : List I)
    (hlen : xs.length = ys.length + 1) :
    M3.det (xs.map M) (y :: ys) =
      M3.lap xs (fun x xs => M x y * M3.det (xs.map M) ys) := by
  induction xs generalizing y ys with
  | nil => simp at hlen
  | cons x xs ih =>
    simp only [List.map_cons, M3.det, M3.lap]
    congr 1
    rw [M3.z24 ys
      (fun z zs => M x z * M3.det (xs.map M) (y :: zs))
      (fun z zs => M3.lap xs (fun t ts => M x z * (M t y * M3.det (ts.map M) zs)))]
    · rw [z123]
      apply M3.z17
      intro t ts
      rw [<- M3.z21]
      apply M3.z17
      intro z zs; ring
    · intro z zs hp
      have hp_len := hp.length_eq
      simp only [List.length_cons] at hlen hp_len
      rw [ih y zs (by omega), M3.z21]
theorem z125 {I J : Type} (M : J -> I -> Int) (xs : List J) (ys : List I)
    (hlen : xs.length = ys.length) :
    M3.det (xs.map M) ys = M3.det (ys.map (fun y x => M x y)) xs := by
  induction ys generalizing xs with
  | nil =>
    cases xs with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons y ys ih =>
    rw [z124 M xs y ys hlen]
    simp only [List.map_cons, M3.det]
    apply M3.z24
    intro x xs' hp
    have hp_len := hp.length_eq
    simp only [List.length_cons] at hlen hp_len
    rw [ih xs' (by omega)]
theorem z126 {I : Type} (z142 z142' : List (I -> Int)) (h : z142.Perm z142')
    (pre : List (I -> Int)) (z143 : List I) :
    M3.det (pre ++ z142) z143 = 0 <-> M3.det (pre ++ z142') z143 = 0 := by
  induction h generalizing pre z143 with
  | nil => rfl
  | @cons x l₁ l₂ _ ih =>
    have h1 : pre ++ x :: l₁ = (pre ++ [x]) ++ l₁ := by simp
    have h2 : pre ++ x :: l₂ = (pre ++ [x]) ++ l₂ := by simp
    rw [h1, h2]
    exact ih (pre ++ [x]) z143
  | swap x y l =>
    rw [M3.z31]
    exact neg_eq_zero
  | trans _ _ ih1 ih2 =>
    exact (ih1 pre z143).trans (ih2 pre z143)
theorem z127 {I J : Type} (M : J -> I -> Int) (xs : List J) (ys zs : List I)
    (hlen : xs.length = ys.length) (hp : ys.Perm zs) :
    M3.det (xs.map M) ys = 0 <-> M3.det (xs.map M) zs = 0 := by
  have hlen' : xs.length = zs.length := hlen.trans hp.length_eq
  rw [z125 M xs ys hlen, z125 M xs zs hlen']
  exact z126 _ _ (hp.map (fun y x => M x y)) [] xs
theorem z128 {I J : Type} [DecidableEq J] (basis : J -> I -> Int) (xs : List J) (z143 : List I)
    (h : ¬ xs.Nodup) : M3.det (xs.map basis) z143 = 0 := by
  induction xs generalizing z143 with
  | nil => exact absurd (by simp) h
  | cons x xs ih =>
    by_cases hin : x ∈ xs
    · obtain ⟨pre, post, rfl⟩ := M3.z47 hin
      have hmap : (x :: (pre ++ x :: post)).map basis =
          [] ++ basis x :: pre.map basis ++ basis x :: post.map basis := by simp
      rw [hmap]
      exact M3.z32 [] (pre.map basis) (basis x) (post.map basis) z143
    · have hxs : ¬ xs.Nodup := fun hnd => h (List.Nodup.cons hin hnd)
      simp only [List.map_cons, M3.det]
      rw [M3.z17 z143 _ (fun _ _ => 0) (fun c cs => by dsimp -failIfUnchanged only; rw [ih cs hxs, mul_zero])]
      exact M3.z18 z143
theorem z129 {α : Type} (c : α) (pre post : List α) :
    (c :: (pre ++ post)).Perm (pre ++ c :: post) := by
  induction pre with
  | nil => exact List.Perm.refl _
  | cons x pre ih =>
    simp only [List.cons_append]
    exact (List.Perm.swap x c (pre ++ post)).trans (ih.cons x)
theorem z130 {I : Type} [DecidableEq I] {cs z143 : List I}
    (hnd : cs.Nodup) (hlen : cs.length = z143.length) (hsub : ∀ x ∈ cs, x ∈ z143) :
    cs.Perm z143 := by
  induction cs generalizing z143 with
  | nil =>
    cases z143 with
    | nil => exact List.Perm.refl _
    | cons _ _ => simp at hlen
  | cons c cs ih =>
    obtain ⟨hnot, hnd'⟩ := List.nodup_cons.mp hnd
    obtain ⟨pre, post, rfl⟩ := M3.z47 (hsub c (by simp))
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
    exact ((ih hnd' hlen' hsub').cons c).trans (z129 c pre post)
theorem z131 {I : Type} [DecidableEq I] (z142 : List (I -> Int)) (z143 : List I)
    (hlen : z142.length = z143.length) (hind : M14.z75 z142 z143) :
    M3.det z142 z143 ≠ 0 := by
  intro hzero
  obtain ⟨cs, hcs, hincl, hdet⟩ := M14.z78 z142 z143 hind
  have hnd : cs.Nodup := by
    by_contra h
    apply hdet
    have ht := z125 (fun (r : I -> Int) c => r c) z142 cs hcs.symm
    simp only [List.map_id'] at ht
    rw [ht]
    exact z128 (fun c (r : I -> Int) => r c) cs z142 h
  have hp : cs.Perm z143 := z130 hnd (hcs.trans hlen) hincl
  have hperm := z127 (fun (r : I -> Int) c => r c) z142 cs z143 hcs.symm hp
  simp only [List.map_id'] at hperm
  exact hdet (hperm.mpr hzero)
end M20
namespace M21
def seq : Nat -> Nat -> List Nat
  | _, 0 => []
  | a, n + 1 => a :: seq (a + 1) n
@[simp] theorem z132 (a n : Nat) : (seq a n).length = n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih => simp [seq, ih]
theorem z133 (a n : Nat) : seq a (n + 1) = seq a n ++ [a + n] := by
  induction n generalizing a with
  | zero => simp [seq]
  | succ n ih =>
    rw [seq, ih (a + 1), seq, List.cons_append]
    have : a + 1 + n = a + (n + 1) := by omega
    rw [this]
theorem z134 (n : Nat) : seq 0 n = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [z133, ih, List.range_succ, Nat.zero_add]
theorem z135 (n : Nat) (ws : List Int) (a : Nat) (x : Int) (hlen : ws.length = n) :
    M14.z71 ((seq a n).map (fun k x => x ^ k)) ws x =
      x ^ a * M18.eval ws x := by
  induction n generalizing ws a with
  | zero =>
    cases ws with
    | nil => simp [seq, M14.z71, M18.eval]
    | cons _ _ => simp at hlen
  | succ n ih =>
    cases ws with
    | nil => simp at hlen
    | cons w ws =>
      simp only [seq, List.map_cons, M14.z71, M18.eval]
      rw [ih ws (a + 1) (by simp at hlen; exact hlen), pow_succ]
      ring
theorem z136 (qs : List Int) (hnd : qs.Nodup) :
    M3.det ((List.range qs.length).map (fun k x => x ^ k)) qs ≠ 0 := by
  apply M20.z131
  · simp
  · intro ws hlen hz
    simp only [List.length_map, List.length_range] at hlen
    apply M18.z92 ws qs hnd
    · intro x hx
      have hzx := hz x hx
      rw [<- z134, z135 qs.length ws 0 x hlen] at hzx
      simpa using hzx
    · omega
theorem z137 (qs : List Int) (hnd : qs.Nodup) :
    M3.det (qs.map (fun q a => q ^ a)) (List.range qs.length) ≠ 0 := by
  rw [M20.z125 (fun q a => q ^ a) qs (List.range qs.length) (by simp)]
  exact z136 qs hnd
end M21
namespace M1
theorem z138 {I J : Type} (f : J -> I -> Int) (a : J -> Int) (rs : List J) (z143 : List I) :
    M3.det (rs.map (fun r c => a r * f r c)) z143 =
      M3.z36 (rs.map a) * M3.det (rs.map f) z143 := by
  induction rs generalizing z143 with
  | nil => simp [M3.det, M3.z36]
  | cons r rs ih =>
    simp only [List.map_cons, M3.z36, M3.det, <- M3.z21]
    apply M3.z17
    intro c cs
    rw [ih]; ring
theorem z139 (xs : List Int) (h : ∀ x ∈ xs, x ≠ 0) : M3.z36 xs ≠ 0 := by
  induction xs with
  | nil => simp [M3.z36]
  | cons x xs ih =>
    simp only [M3.z36]
    exact mul_ne_zero (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))
structure z140 where
  base : Int
  order : Nat
  polynomial : List Int
def lc (t : z140) : Int := M18.z99 t.polynomial t.order
def z141 (t : z140) : Prop := t.polynomial.length ≤ t.order + 1 /\ lc t ≠ 0
def z142 (ts : List z140) : List (Nat × (Nat -> List Int)) :=
  ts.map (fun t => (t.order, fun a => M18.z93 (t.base ^ a) (M18.z97 t.polynomial (a : Int))))
def z143 (ts : List z140) : List Nat := List.range ts.length
def H (ts : List z140) : List Int := M17.z118 (z142 ts) (z143 ts)
def z117 (ts : List z140) : Nat := M17.z117 (z142 ts)
theorem z144 (ts : List z140) (hg : ∀ t ∈ ts, z141 t) :
    M17.z119 (z142 ts) := by
  intro p hp a
  rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
  obtain ⟨hlen, _⟩ := hg t ht
  simp only [M18.z108]
  exact Nat.le_trans (M18.z110 t.polynomial (a : Int)) hlen
theorem z145 (ts : List z140) (hnd : (ts.map z140.base).Nodup) (hg : ∀ t ∈ ts, z141 t) :
    M18.z99 (H ts) (z117 ts) ≠ 0 := by
  unfold H z117
  rw [M17.z122 (z142 ts) (z144 ts hg) (z143 ts)]
  unfold z142
  rw [List.map_map]
  rw [M3.z35 _ (ts.map (fun t a => lc t * t.base ^ a)) (z143 ts)]
  · rw [z138 (fun t a => t.base ^ a) lc ts (z143 ts)]
    intro heq
    rcases mul_eq_zero.mp heq with h1 | h2
    · apply z139 (ts.map lc) _ h1
      intro x hx
      rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
      exact (hg t ht).2
    · have hv := M21.z137 (ts.map z140.base) hnd
      simp only [List.map_map, List.length_map] at hv
      exact hv h2
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    refine List.forall₂_same.mpr ?_
    intro t ht a _
    obtain ⟨hlen, _⟩ := hg t ht
    simp only [Function.comp_apply, M18.z106, M18.z112 _ _ _ hlen]
    unfold lc; ring
theorem z146 (ts : List z140) (roots : List Int)
    (hnd : (ts.map z140.base).Nodup)
    (hg : ∀ t ∈ ts, z141 t)
    (hr : roots.Nodup)
    (hz : ∀ x ∈ roots, M18.eval (H ts) x = 0) :
    roots.length ≤ z117 ts := by
  by_contra hgt
  push Not at hgt
  apply z145 ts hnd hg
  have hp : ∀ a ∈ H ts, a = 0 := by
    apply M18.z92 (H ts) roots hr hz
    have hlen := M17.z121 (z142 ts) (z144 ts hg) (z143 ts)
    unfold H z117 at *
    omega
  exact M18.z104 (H ts) (z117 ts) hp
end M1
namespace M16
lemma z147 (a b p c : Nat) (hb : 0 < b) (hba : b ≤ a)
    (hbase : (b + 1) ^ p ≤ c * b ^ p) :
    (a + 1) ^ p ≤ c * a ^ p := by
  have h1 : b * (a + 1) ≤ (b + 1) * a := by nlinarith
  have h2 : (b * (a + 1)) ^ p ≤ ((b + 1) * a) ^ p := Nat.pow_le_pow_left h1 p
  rw [Nat.mul_pow, Nat.mul_pow] at h2
  have h3 : (b + 1) ^ p * a ^ p ≤ (c * b ^ p) * a ^ p := Nat.mul_le_mul_right (a ^ p) hbase
  have h4 : b ^ p * (a + 1) ^ p ≤ b ^ p * (c * a ^ p) := by linarith
  have hbp : 0 < b ^ p := by positivity
  exact Nat.le_of_mul_le_mul_left h4 hbp
lemma z148 (m : Nat) (hm : 59 ≤ m) : 2 ^ 22 * m ^ 6 < 2 ^ (m - 1) := by
  have h : ∀ i : Nat, 2 ^ 22 * (59 + i) ^ 6 < 2 ^ (58 + i) := by
    intro i
    induction i with
    | zero => decide
    | succ i ih =>
      have hr : (59 + i + 1) ^ 6 ≤ 2 * (59 + i) ^ 6 :=
        z147 (59 + i) 16 6 2 (by omega) (by omega) (by decide)
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
theorem z149 (m n : Nat) (hm : 59 ≤ m) (hn : 2 ^ (m - 1) ≤ n) :
    (2048 * m ^ 3) ^ 2 < n := by
  have h1 := z148 m hm
  have h2 : (2048 * m ^ 3) ^ 2 = 2 ^ 22 * m ^ 6 := by ring
  omega
theorem z150 (m : Nat) (hm : 2 ≤ m) :
    (2048 * m ^ 3) * (1664 * m ^ 3 + m) <
      (2048 * m ^ 3) * (2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2)) := by
  have hpos : 0 < 2048 * m ^ 3 := by positivity
  apply Nat.mul_lt_mul_of_pos_left _ hpos
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
  have h1 : 1664 * (k + 2) ^ 3 + (k + 2) + 1 + 2 * (256 * (k + 2) ^ 2) < 2048 * (k + 2) ^ 3 := by
    nlinarith
  omega
end M16
namespace M13
def F (n : Nat) : Int := 2 * (3 : Int) ^ n + (n : Int) + 5
theorem z151 (a : Nat) : (0 : Int) < (2 : Int) ^ a := by positivity
theorem z152 (m x y : Int) (hm : 0 < m) : (m ∣ (x - y)) <-> x % m = y % m := by
  constructor
  · rintro ⟨q, hq⟩
    have hx : x = y + m * q := by linarith
    rw [hx, Int.add_mul_emod_self_left]
  · intro h
    refine ⟨x / m - y / m, ?_⟩
    have h1 := Int.mul_ediv_add_emod x m
    have h2 := Int.mul_ediv_add_emod y m
    linarith
theorem z7 (a b : Nat) (h : a ≤ b) : ((2 : Int) ^ a) ∣ ((2 : Int) ^ b) := by
  refine ⟨(2 : Int) ^ (b - a), ?_⟩
  have hb : b = a + (b - a) := (Nat.add_sub_of_le h).symm
  conv_lhs => rw [hb]
  rw [pow_add]
lemma z153 (a : Nat) : ∃ t : Int, (3 : Int) ^ (2 ^ a) = 1 + (2 : Int) ^ (a + 1) * t := by
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
lemma z154 (A : Int) (w : Nat) : (A - 1) ∣ (A ^ w - 1) := by
  induction w with
  | zero => exact ⟨0, by ring⟩
  | succ w ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨A * k + 1, ?_⟩
    calc A ^ (w + 1) - 1
        = A * (A ^ w - 1) + (A - 1) := by ring
      _ = A * ((A - 1) * k) + (A - 1) := by rw [hk]
      _ = (A - 1) * (A * k + 1) := by ring
lemma z155 (a x y : Nat) (hxy : y ≤ x)
    (hdvd : ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int))) :
    ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ x - (3 : Int) ^ y) := by
  have hdvd_nat : 2 ^ a ∣ (x - y) := by
    have h1 : ((x - y : Nat) : Int) = (x : Int) - (y : Int) := Int.ofNat_sub hxy
    rw [<- h1] at hdvd
    exact Int.ofNat_dvd.mp hdvd
  rcases hdvd_nat with ⟨w, hw⟩
  have hx : x = y + 2 ^ a * w := by omega
  rcases z153 a with ⟨t, ht⟩
  have hd1 : ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ (2 ^ a) - 1) := ⟨t, by linarith⟩
  have hd2 : ((3 : Int) ^ (2 ^ a) - 1) ∣ (((3 : Int) ^ (2 ^ a)) ^ w - 1) :=
    z154 ((3 : Int) ^ (2 ^ a)) w
  have hd3 : ((2 : Int) ^ (a + 1)) ∣ (((3 : Int) ^ (2 ^ a)) ^ w - 1) := dvd_trans hd1 hd2
  rcases hd3 with ⟨u, hu⟩
  refine ⟨(3 : Int) ^ y * u, ?_⟩
  calc (3 : Int) ^ x - (3 : Int) ^ y
      = (3 : Int) ^ (y + 2 ^ a * w) - (3 : Int) ^ y := by rw [hx]
    _ = (3 : Int) ^ y * (((3 : Int) ^ (2 ^ a)) ^ w - 1) := by rw [pow_add, pow_mul]; ring
    _ = (3 : Int) ^ y * ((2 : Int) ^ (a + 1) * u) := by rw [hu]
    _ = (2 : Int) ^ (a + 1) * ((3 : Int) ^ y * u) := by ring
lemma z156 (a x y : Nat)
    (hdvd : ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int))) :
    ((2 : Int) ^ (a + 1)) ∣ ((3 : Int) ^ x - (3 : Int) ^ y) := by
  by_cases hxy : y ≤ x
  · exact z155 a x y hxy hdvd
  · push Not at hxy
    have hdvd' : ((2 : Int) ^ a) ∣ ((y : Int) - (x : Int)) := by
      rcases hdvd with ⟨w, hw⟩
      exact ⟨-w, by linarith⟩
    rcases z155 a y x (by omega) hdvd' with ⟨v, hv⟩
    exact ⟨-v, by linarith⟩
lemma z157 (a x y : Nat)
    (h : ((2 : Int) ^ a) ∣ (F x - F y)) :
    ((2 : Int) ^ a) ∣ ((x : Int) - (y : Int)) := by
  induction a with
  | zero => exact ⟨(x : Int) - (y : Int), by ring⟩
  | succ a ih =>
    have hlow : ((2 : Int) ^ a) ∣ (F x - F y) := by
      rcases h with ⟨w, hw⟩
      exact ⟨2 * w, by rw [pow_succ] at hw; linarith⟩
    rcases z156 a x y (ih hlow) with ⟨v, hv⟩
    rcases h with ⟨w, hw⟩
    refine ⟨w - 2 * v, ?_⟩
    have hp2 : (2 : Int) ^ (a + 1) = (2 : Int) ^ a * 2 := by rw [pow_succ]
    unfold F at hw
    linarith
def z158 : Nat -> Nat -> Nat -> Nat -> Nat
  | 0, _, _, m => 1 % m
  | k + 1, b, e, m =>
    if e = 0 then 1 % m
    else
      if e % 2 = 0 then ((z158 k b (e / 2) m) * (z158 k b (e / 2) m)) % m
      else (b * (((z158 k b (e / 2) m) * (z158 k b (e / 2) m)) % m)) % m
lemma z159 (k b e m : Nat) (he : e < 2 ^ k) :
    z158 k b e m = (b ^ e) % m := by
  induction k generalizing e with
  | zero =>
    have he0 : e = 0 := by omega
    subst he0
    simp [z158]
  | succ k ih =>
    unfold z158
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
lemma z160 (r q a k : Nat)
    (he : r < 2 ^ k)
    (hpow : z158 k 3 r (2 ^ a) = q)
    (hroot : 2 * q + r + 5 = 2 * 2 ^ a) :
    ((2 : Int) ^ a) ∣ F r := by
  have h1 : (3 ^ r) % (2 ^ a) = q := by
    rw [<- z159 k 3 r (2 ^ a) he]
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
lemma z161 : ((2 : Int) ^ 8) ∣ F 149 :=
  z160 149 179 8 8 (by decide) (by decide) (by decide)
set_option maxRecDepth 200000 in
lemma z162 : ((2 : Int) ^ 64) ∣ F 767351889479380629 :=
  z160 767351889479380629 18063068128969861299 64 60 (by decide) (by decide) (by decide)
lemma z163 (a n r : Nat) (hroot : ((2 : Int) ^ a) ∣ F r)
    (hn : ((2 : Int) ^ a) ∣ F n) :
    n % (2 ^ a) = r % (2 ^ a) := by
  have hsub : ((2 : Int) ^ a) ∣ (F n - F r) := Int.dvd_sub hn hroot
  have hinj : ((2 : Int) ^ a) ∣ ((n : Int) - (r : Int)) := z157 a n r hsub
  have hmod := (z152 ((2 : Int) ^ a) (n : Int) (r : Int) (z151 a)).mp hinj
  exact_mod_cast hmod
theorem z164 (n : Nat) (hn1 : 7 ≤ n) (hn2 : n < 2 ^ 58) :
    ¬ (((2 : Int) ^ (n + 1)) ∣ F n) := by
  intro hbad
  by_cases hsmall : n < 64
  · have h8 : ((2 : Int) ^ 8) ∣ F n :=
      dvd_trans (z7 8 (n + 1) (by omega)) hbad
    have hu := z163 8 n 149 z161 h8
    have h1 : n % (2 ^ 8) = n := Nat.mod_eq_of_lt (by omega)
    have h2 : 149 % (2 ^ 8) = 149 := by decide
    omega
  · have h64 : ((2 : Int) ^ 64) ∣ F n :=
      dvd_trans (z7 64 (n + 1) (by omega)) hbad
    have hu := z163 64 n 767351889479380629 z162 h64
    have hcut1 : 2 ^ 58 < 767351889479380629 := by decide
    have hcut2 : 767351889479380629 < 2 ^ 64 := by decide
    have h1 : n % (2 ^ 64) = n := Nat.mod_eq_of_lt (by omega)
    have h2 : 767351889479380629 % (2 ^ 64) = 767351889479380629 := Nat.mod_eq_of_lt hcut2
    omega
def large_exclusion : Prop :=
  ∀ n u : Nat, 2 ^ 58 ≤ n -> 1 ≤ u /\ u ≤ n -> ¬ (((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - (u : Int)))
theorem z165 (hlarge : large_exclusion) (n : Nat) (hn : 7 ≤ n) :
    ¬ (((2 : Int) ^ (n + 1)) ∣ F n) := by
  intro hbad
  by_cases hsmall : n < 2 ^ 58
  · exact z164 n hn hsmall hbad
  · push Not at hsmall
    have htwo : (2 : Int) ∣ F n := by
      have h1 : ((2 : Int) ^ 1) ∣ F n := dvd_trans (z7 1 (n + 1) (by omega)) hbad
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
end M13
namespace M6
open M18
def z166 : List Int -> List Int
  | [] => []
  | a :: p =>
    match z166 p with
    | [] => if a = 0 then [] else [a]
    | q => a :: q
theorem z167 (p : List Int) :
    (z166 p).length ≤ p.length /\
    (∀ x, M18.eval (z166 p) x = M18.eval p x) /\
    (z166 p = [] \/ z99 (z166 p) ((z166 p).length - 1) ≠ 0) := by
  induction p with
  | nil =>
    simp [z166, M18.eval]
  | cons a p ih =>
    rcases ih with ⟨hlen, he, hlc⟩
    simp only [z166]
    cases hp : z166 p with
    | nil =>
      by_cases ha : a = 0
      · refine ⟨by simp [ha], ?_, Or.inl (by simp [ha])⟩
        intro x
        have hpx := he x
        rw [hp] at hpx
        simp [M18.eval, ha, <- hpx]
      · refine ⟨by simp [ha], ?_, Or.inr (by simp [z99, ha])⟩
        intro x
        have hpx := he x
        rw [hp] at hpx
        simp [M18.eval, ha, <- hpx]
    | cons b q =>
      rw [hp] at hlen hlc
      simp only [List.length_cons] at hlen ⊢
      refine ⟨by omega, ?_, Or.inr ?_⟩
      · intro x
        have hpx := he x
        rw [hp] at hpx
        change a + x * M18.eval (b :: q) x = a + x * M18.eval p x
        rw [hpx]
      · rcases hlc with hnil | hlc
        · nomatch hnil
        · simpa [z99] using hlc
theorem z168 (p : List Int) (h : z166 p = []) : ∀ a ∈ p, a = 0 := by
  induction p with
  | nil => intro a ha; nomatch ha
  | cons a p ih =>
    simp only [z166] at h
    cases hp : z166 p with
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
def z169 (n : Nat) (rs : Nat × Nat) : Int :=
  (rs.1 : Int) + (n : Int) * (rs.2 : Int)
def z170 (R : Nat) : Nat -> List (Nat × Nat)
  | 0 => []
  | s + 1 => z170 R s ++ (List.range R).map (fun r => (r, s))
theorem z171 (R S : Nat) : (z170 R S).length = R * S := by
  induction S with
  | zero => simp [z170]
  | succ s ih =>
    simp [z170, ih, Nat.mul_succ]
theorem z172 (R S r s : Nat) : (r, s) ∈ z170 R S <-> r < R /\ s < S := by
  induction S with
  | zero => simp [z170]
  | succ S ih =>
    simp only [z170, List.mem_append, ih, List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro (⟨hr, hs⟩ | ⟨r', hr', rfl, rfl⟩)
      · exact ⟨hr, by omega⟩
      · exact ⟨hr', by omega⟩
    · rintro ⟨hr, hs⟩
      by_cases h : s = S
      · subst h
        exact Or.inr ⟨r, hr, rfl, rfl⟩
      · exact Or.inl ⟨hr, by omega⟩
theorem z173 {A B : Type} (f : A -> B) (xs : List A) (hnd : xs.Nodup)
    (hinj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y -> x = y) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hnot, hnd'⟩
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hnd' (fun u hu v hv h => hinj u (List.mem_cons_of_mem _ hu) v (List.mem_cons_of_mem _ hv) h)⟩
    intro hmem
    rcases List.mem_map.mp hmem with ⟨y, hy, hfy⟩
    have hyx : y = x := hinj y (List.mem_cons_of_mem _ hy) x List.mem_cons_self hfy
    subst hyx
    exact hnot hy
theorem z174 {A : Type} (xs ys : List A) (hx : xs.Nodup) (hy : ys.Nodup)
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
theorem z175 (n R r s r' s' : Nat) (hn : R ≤ n) (hr : r < R) (hr' : r' < R)
    (he : z169 n (r, s) = z169 n (r', s')) : r = r' /\ s = s' := by
  unfold z169 at he
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
theorem z176 (n R S : Nat) (hn : R ≤ n) : ((z170 R S).map (z169 n)).Nodup := by
  induction S with
  | zero => simp [z170]
  | succ S ih =>
    simp only [z170, List.map_append, List.map_map]
    apply z174 _ _ ih
    · apply z173 _ _ List.nodup_range
      intro r hr r' hr' he
      simp only [Function.comp_apply, z169] at he
      omega
    · intro x hx hy
      rcases List.mem_map.mp hx with ⟨⟨r, s⟩, hrs, rfl⟩
      rcases List.mem_map.mp hy with ⟨r', hr', he⟩
      simp only [Function.comp_apply] at he
      rw [z172] at hrs
      rw [List.mem_range] at hr'
      have ⟨_, hss⟩ := z175 n R r s r' S hn hrs.1 hr' he.symm
      omega
end M6
namespace M9
open M18 M6
abbrev z177 := Nat × List Int
def z178 (l : Nat) : Int := (-3 : Int) ^ l
def z179 : List z177 -> Int -> Int -> Int
  | [], _, _ => 0
  | (l, p) :: ts, x, y => M18.eval p x * y ^ l + z179 ts x y
def z180 : List z177 -> List z177
  | [] => []
  | (l, p) :: ts =>
    match z166 p with
    | [] => z180 ts
    | q => (l, q) :: z180 ts
def z181 (t : z177) : M1.z140 :=
  ⟨z178 t.1, t.2.length - 1, t.2⟩
theorem z182 (ts : List z177) (x y : Int) : z179 (z180 ts) x y = z179 ts x y := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    rcases z167 p with ⟨_, he, _⟩
    simp only [z180]
    cases hp : z166 p with
    | nil =>
      simp only [z179, ih]
      have hpx := he x
      rw [hp] at hpx
      simp [M18.eval, <- hpx]
    | cons a q =>
      simp only [z179, ih]
      have hpx := he x
      rw [hp] at hpx
      rw [hpx]
theorem z183 (ts : List z177) : (z180 ts).length ≤ ts.length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    simp only [z180]
    cases z166 p <;> simp <;> omega
theorem z184 (ts : List z177) (h : z180 ts = []) :
    ∀ t ∈ ts, ∀ a ∈ t.2, a = 0 := by
  induction ts with
  | nil => intro t ht; nomatch ht
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    simp only [z180] at h
    cases hp : z166 p with
    | nil =>
      rw [hp] at h
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact z168 p hp
      · exact ih h u hu
    | cons a q =>
      rw [hp] at h
      nomatch h
theorem z185 (ts : List z177) (l : Nat) (p : List Int) (h : (l, p) ∈ z180 ts) :
    ∃ q, (l, q) ∈ ts /\ p = z166 q /\ p ≠ [] := by
  induction ts with
  | nil => nomatch h
  | cons t ts ih =>
    rcases t with ⟨a, q⟩
    simp only [z180] at h
    cases hq : z166 q with
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
theorem z186 (ts : List z177) : ∀ t ∈ (z180 ts).map z181, M1.z141 t := by
  intro t ht
  rcases List.mem_map.mp ht with ⟨⟨l, p⟩, hp, rfl⟩
  rcases z185 ts l p hp with ⟨q, _, rfl, hne⟩
  rcases z167 q with ⟨_, _, hlc⟩
  unfold M1.z141 M1.lc z181
  dsimp -failIfUnchanged
  refine ⟨by omega, ?_⟩
  rcases hlc with hnil | hlc
  · exact absurd hnil hne
  · exact hlc
theorem z187 (ts : List z177) (K : Nat) (h : ∀ t ∈ ts, t.2.length ≤ K) :
    ∀ t ∈ z180 ts, t.2.length ≤ K := by
  rintro ⟨l, p⟩ hp
  rcases z185 ts l p hp with ⟨q, hq, rfl, _⟩
  have h1 := h (l, q) hq
  have h2 := (z167 q).1
  dsimp -failIfUnchanged at h1 ⊢
  omega
theorem z188 (ts : List z177) :
    ∀ l ∈ (z180 ts).map Prod.fst, l ∈ ts.map Prod.fst := by
  intro l hl
  rcases List.mem_map.mp hl with ⟨⟨l', p⟩, hp, rfl⟩
  rcases z185 ts l' p hp with ⟨q, hq, _⟩
  exact List.mem_map.mpr ⟨(l', q), hq, rfl⟩
theorem z189 (ts : List z177) (h : (ts.map Prod.fst).Nodup) :
    ((z180 ts).map Prod.fst).Nodup := by
  induction ts with
  | nil => simp [z180]
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    rw [List.map_cons, List.nodup_cons] at h
    rcases h with ⟨hnot, hnd⟩
    simp only [z180]
    cases z166 p with
    | nil => exact ih hnd
    | cons a q =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hi => hnot (z188 ts l hi), ih hnd⟩
theorem z190 (l k : Nat) (he : z178 l = z178 k) : l = k := by
  unfold z178 at he
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
theorem z191 (ts : List z177) (h : (ts.map Prod.fst).Nodup) :
    ((ts.map z181).map M1.z140.base).Nodup := by
  have hmap : (ts.map z181).map M1.z140.base = (ts.map Prod.fst).map z178 := by
    induction ts <;> simp [z181, *]
  rw [hmap]
  exact z173 z178 (ts.map Prod.fst) h (fun x _ y _ he => z190 x y he)
theorem z192 (ts : List z177) (K : Nat) (h : ∀ t ∈ ts, t.2.length ≤ K) :
    M1.z117 (ts.map z181) ≤ (K - 1) * ts.length := by
  induction ts with
  | nil => simp [M1.z117, M1.z142, M17.z117]
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    have hp : p.length ≤ K := h (l, p) List.mem_cons_self
    have hts : ∀ u ∈ ts, u.2.length ≤ K := fun u hu => h u (List.mem_cons_of_mem _ hu)
    have ih' := ih hts
    unfold M1.z117 M1.z142 at ih' ⊢
    simp only [List.map_cons, M17.z117, z181, List.length_cons]
    rw [Nat.mul_succ]
    omega
def z193 (u : Int) (rs : Nat × Nat) : Int :=
  (-3 : Int) ^ rs.1 * u ^ rs.2
def z194 (ts : List z177) (x : Int) : List (Nat -> Int) :=
  ts.map (fun t a => (z178 t.1) ^ a * M18.eval t.2 (x + (a : Int)))
def z195 (ts : List z177) (y : Int) : List Int :=
  ts.map (fun t => y ^ t.1)
theorem z196 (u : Int) (rs : Nat × Nat) (hu : u ≠ 0) : z193 u rs ≠ 0 := by
  unfold z193
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ hu)
theorem z197 (l a : Nat) : (z178 l) ^ a = ((-3 : Int) ^ a) ^ l := by
  unfold z178
  rw [<- pow_mul, <- pow_mul, Nat.mul_comm]
theorem z198 (ts : List z177) (x y : Int) (a : Nat) :
    M14.z71 (z194 ts x) (z195 ts y) a =
      z179 ts (x + (a : Int)) ((-3 : Int) ^ a * y) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    unfold z194 z195
    rw [List.map_cons, List.map_cons]
    simp only [M14.z71, z179]
    change y ^ l * (z178 l ^ a * M18.eval p (x + ↑a)) +
      M14.z71 (z194 ts x) (z195 ts y) a = _
    rw [ih, mul_pow, z197]
    ring
theorem z199 (ts : List z177) (x : Int) :
    M18.eval (M1.H (ts.map z181)) x =
      M3.det (z194 ts x) (List.range ts.length) := by
  unfold M1.H M1.z143
  rw [List.length_map, M17.z120]
  unfold M1.z142 z194
  rw [List.map_map, List.map_map]
  generalize List.range ts.length = cs
  apply M3.z35
  induction ts with
  | nil => exact List.Forall₂.nil
  | cons t ts ih =>
    rcases t with ⟨l, p⟩
    refine List.Forall₂.cons ?_ ih
    intro a _
    simp [z181, z95, z98]
theorem z200 (ts : List z177) (x y : Int) (hts : ts ≠ []) (hy : y ≠ 0)
    (hrel : ∀ a, a < ts.length -> z179 ts (x + (a : Int)) ((-3 : Int) ^ a * y) = 0) :
    M18.eval (M1.H (ts.map z181)) x = 0 := by
  rw [z199]
  cases ts with
  | nil => contradiction
  | cons t ts =>
    rcases t with ⟨l, p⟩
    unfold z194
    rw [List.map_cons]
    apply M14.z80 _ _ (y ^ l) (z195 ts y)
    · exact pow_ne_zero _ hy
    · intro a ha
      change M14.z71 (z194 ((l, p) :: ts) x) (z195 ((l, p) :: ts) y) a = 0
      rw [z198]
      apply hrel
      exact List.mem_range.mp ha
theorem z201 (n r s a : Nat) : z169 n (r + a, s) = z169 n (r, s) + (a : Int) := by
  unfold z169
  dsimp -failIfUnchanged
  omega
theorem z202 (u : Int) (r s a : Nat) :
    z193 u (r + a, s) = (-3 : Int) ^ a * z193 u (r, s) := by
  unfold z193
  dsimp -failIfUnchanged
  rw [pow_add]
  ring
theorem z203 (K L n : Nat) (u : Int) (R0 S : Nat) (ts : List z177)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hlength : ts.length ≤ L) (hu : u ≠ 0)
    (hnd : (ts.map Prod.fst).Nodup) (hbound : ∀ t ∈ ts, t.2.length ≤ K)
    (hz : ∀ r s, r < R0 + L - 1 -> s < S -> z179 ts (z169 n (r, s)) (z193 u (r, s)) = 0) :
    ∀ t ∈ ts, ∀ a ∈ t.2, a = 0 := by
  cases hprep : z180 ts with
  | nil => exact z184 ts hprep
  | cons t pts =>
    exfalso
    have hne : z180 ts ≠ [] := by rw [hprep]; simp
    have hroots : ∀ x ∈ (z170 R0 S).map (z169 n),
        M18.eval (M1.H ((z180 ts).map z181)) x = 0 := by
      intro x hx
      rcases List.mem_map.mp hx with ⟨⟨r, s⟩, hrs, rfl⟩
      rw [z172] at hrs
      apply z200 _ _ (z193 u (r, s)) hne (z196 u (r, s) hu)
      intro a ha
      rw [<- z201, <- z202, z182]
      have hplen := z183 ts
      exact hz (r + a) s (by omega) hrs.2
    have hcount := M1.z146 ((z180 ts).map z181) ((z170 R0 S).map (z169 n))
      (z191 _ (z189 ts hnd)) (z186 ts)
      (z176 n R0 S hn) hroots
    have hdegree := z192 (z180 ts) K (z187 ts K hbound)
    have hplen := z183 ts
    rw [List.length_map, z171] at hcount
    have hmul : (K - 1) * (z180 ts).length ≤ (K - 1) * L :=
      Nat.mul_le_mul_left (K - 1) (Nat.le_trans hplen hlength)
    omega
end M9
namespace M8
open M18 M14 M6 M9
def z204 (K : Nat) : Nat -> Nat -> List (Nat × Nat)
  | _, 0 => []
  | a, len + 1 => (List.range K).map (fun k => (k, a)) ++ z204 K (a + 1) len
def entry (n : Nat) (u : Int) (kl rs : Nat × Nat) : Int :=
  (z169 n rs) ^ kl.1 * (z193 u rs) ^ kl.2
def z205 (K : Nat) : Nat -> Nat -> List Int -> List z177
  | _, 0, _ => []
  | a, len + 1, ws => (a, ws.take K) :: z205 K (a + 1) len (ws.drop K)
theorem z206 (K a L : Nat) : (z204 K a L).length = K * L := by
  induction L generalizing a with
  | zero => simp [z204]
  | succ L ih =>
    simp [z204, ih (a + 1), Nat.mul_succ, Nat.add_comm]
theorem z207 (K L a k l : Nat) :
    (k, l) ∈ z204 K a L <-> k < K /\ a ≤ l /\ l < a + L := by
  induction L generalizing a with
  | zero => simp [z204]
  | succ L ih =>
    simp only [z204, List.mem_append, List.mem_map, List.mem_range, Prod.mk.injEq, ih (a + 1)]
    constructor
    · rintro (⟨k', hk', rfl, rfl⟩ | ⟨hk, hl1, hl2⟩)
      · exact ⟨hk', by omega, by omega⟩
      · exact ⟨hk, by omega, by omega⟩
    · rintro ⟨hk, hl1, hl2⟩
      by_cases h : l = a
      · subst h
        exact Or.inl ⟨k, hk, rfl, rfl⟩
      · exact Or.inr ⟨hk, by omega, by omega⟩
theorem z208 (K a L : Nat) (ws : List Int) :
    (z205 K a L ws).map Prod.fst = List.range' a L := by
  induction L generalizing a ws with
  | zero => rfl
  | succ L ih =>
    simp [z205, List.range', ih (a + 1) (ws.drop K)]
theorem z209 (K a L : Nat) (ws : List Int) : (z205 K a L ws).length = L := by
  have h := congrArg List.length (z208 K a L ws)
  simpa using h
theorem z210 (K a L : Nat) (ws : List Int) :
    ∀ t ∈ z205 K a L ws, t.2.length ≤ K := by
  induction L generalizing a ws with
  | zero => intro t ht; nomatch ht
  | succ L ih =>
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · simp [List.length_take]
    · exact ih (a + 1) (ws.drop K) t ht
theorem z211 (K a L : Nat) (ws : List Int) (hlen : ws.length = K * L)
    (hz : ∀ t ∈ z205 K a L ws, ∀ x ∈ t.2, x = 0) :
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
theorem z212 {I : Type} (rs ss : List (I -> Int)) (ws : List Int) (c : I) :
    z71 (rs ++ ss) ws c =
      z71 rs (ws.take rs.length) c + z71 ss (ws.drop rs.length) c := by
  have hnil : ∀ qs : List (I -> Int), z71 qs [] c = 0 := by
    intro qs; cases qs <;> rfl
  induction rs generalizing ws with
  | nil => simp [z71]
  | cons r rs ih =>
    cases ws with
    | nil => simp [hnil]
    | cons w ws =>
      simp only [List.cons_append, List.length_cons, List.take_succ_cons, List.drop_succ_cons,
        z71]
      rw [ih]
      ring
theorem z213 (n : Nat) (u : Int) (l K : Nat) (ws : List Int) (a : Nat) (rs : Nat × Nat)
    (hlen : ws.length = K) :
    z71 ((List.range' a K).map (fun k => entry n u (k, l))) ws rs =
      (z169 n rs) ^ a * M18.eval ws (z169 n rs) * (z193 u rs) ^ l := by
  induction K generalizing ws a with
  | zero =>
    cases ws with
    | nil => simp [List.range', z71, M18.eval]
    | cons _ _ => nomatch hlen
  | succ K ih =>
    cases ws with
    | nil => nomatch hlen
    | cons w ws =>
      simp only [List.length_cons, Nat.succ.injEq] at hlen
      simp only [List.range', List.map_cons, z71, M18.eval]
      rw [ih ws (a + 1) hlen]
      unfold entry
      dsimp -failIfUnchanged
      rw [pow_succ]
      ring
theorem z214 (n : Nat) (u : Int) (K a L : Nat) (ws : List Int) (rs : Nat × Nat)
    (hlen : ws.length = K * L) :
    z71 ((z204 K a L).map (entry n u)) ws rs =
      z179 (z205 K a L ws) (z169 n rs) (z193 u rs) := by
  induction L generalizing a ws with
  | zero =>
    cases ws with
    | nil => rfl
    | cons _ _ => nomatch hlen
  | succ L ih =>
    simp only [z204, z205, z179, List.map_append, z212, List.map_map,
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
    rw [hr, z213 n u a K (ws.take K) 0 rs htake, ih (a + 1) (ws.drop K) hdrop]
    ring
theorem z215 (K L n : Nat) (u : Int) (R0 S : Nat)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hu : u ≠ 0) :
    z75 ((z204 K 0 L).map (entry n u)) (z170 (R0 + L - 1) S) := by
  intro ws hlen hz
  rw [List.length_map, z206] at hlen
  apply z211 K 0 L ws hlen
  apply z203 K L n u R0 S (z205 K 0 L ws) hn hsize
  · rw [z209]
  · exact hu
  · rw [z208]
    exact List.nodup_range'
  · exact z210 K 0 L ws
  · intro r s hr hs
    rw [<- z214 n u K 0 L ws (r, s) hlen]
    exact hz (r, s) ((z172 (R0 + L - 1) S r s).mpr ⟨hr, hs⟩)
theorem z216 (K L n : Nat) (u : Int) (R0 S : Nat)
    (hn : R0 ≤ n) (hsize : (K - 1) * L < R0 * S) (hu : u ≠ 0) :
    ∃ cs, cs.length = K * L /\ (∀ x ∈ cs, x ∈ z170 (R0 + L - 1) S) /\
      M3.det ((z204 K 0 L).map (entry n u)) cs ≠ 0 := by
  rcases z78 _ _ (z215 K L n u R0 S hn hsize hu) with ⟨cs, hcs, hrest⟩
  rw [List.length_map, z206] at hcs
  exact ⟨cs, hcs, hrest⟩
end M8
namespace M5
open M3 M6 M9 M8
theorem z217 {I J : Type} (xs : List J) (f g : J -> I -> Int) (z143 : List I)
    (h : ∀ x ∈ xs, ∀ c ∈ z143, f x c = g x c) :
    det (xs.map f) z143 = det (xs.map g) z143 := by
  apply z35
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    refine List.Forall₂.cons ?_ (ih (fun y hy c hc => h y (List.mem_cons_of_mem _ hy) c hc))
    intro c hc
    exact h x List.mem_cons_self c hc
theorem z218 {I J : Type} (xs : List J) (f g : J -> I -> Int) (z143 : List I) (M : Int)
    (h : ∀ x ∈ xs, ∀ c ∈ z143, M ∣ (f x c - g x c)) :
    M ∣ (det (xs.map f) z143 - det (xs.map g) z143) := by
  apply z34
  induction xs with
  | nil => exact List.Forall₂.nil
  | cons x xs ih =>
    refine List.Forall₂.cons ?_ (ih (fun y hy c hc => h y (List.mem_cons_of_mem _ hy) c hc))
    intro c hc
    exact h x List.mem_cons_self c hc
theorem z219 (M a b : Int) (e : Nat) (h : a % M = b % M) :
    (a ^ e) % M = (b ^ e) % M := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [pow_succ, pow_succ, Int.mul_emod, ih, h, <- Int.mul_emod]
theorem z220 (l : Nat) : (4 : Int) ∣ (z178 l - 1) := by
  rw [M13.z152 4 (z178 l) 1 (by decide)]
  unfold z178
  have h := z219 4 (-3) 1 l (by decide)
  simpa using h
def z221 (n : Nat) (rs : Nat × Nat) : Nat :=
  rs.1 + n * rs.2
theorem z222 (n : Nat) (rs : Nat × Nat) :
    (z221 n rs : Int) = z169 n rs := by
  unfold z221 z169
  push_cast
  rfl
def z223 (n : Nat) (kl rs : Nat × Nat) : Int :=
  (z169 n rs) ^ kl.1 * (z178 kl.2) ^ (z221 n rs)
theorem z224 (n : Nat) (u : Int) (kl rs : Nat × Nat)
    (hbad : ((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - u)) :
    ((2 : Int) ^ n) ∣ (entry n u kl rs - z223 n kl rs) := by
  set M : Int := (2 : Int) ^ n
  have hM : 0 < M := M13.z151 n
  have hb : ((-3 : Int) ^ n) % M = u % M := (M13.z152 M _ _ hM).mp hbad
  rcases kl with ⟨k, l⟩
  rcases rs with ⟨r, s⟩
  have hy : (z193 u (r, s)) % M = ((-3 : Int) ^ (z221 n (r, s))) % M := by
    unfold z193 z221
    dsimp -failIfUnchanged
    rw [pow_add, pow_mul, Int.mul_emod, Int.mul_emod ((-3 : Int) ^ r)]
    rw [z219 M u ((-3 : Int) ^ n) s hb.symm]
  have he : ((z193 u (r, s)) ^ l) % M = ((z178 l) ^ (z221 n (r, s))) % M := by
    unfold z178
    rw [<- pow_mul, Nat.mul_comm l, pow_mul]
    exact z219 M _ _ l hy
  rw [M13.z152 M _ _ hM]
  unfold entry z223
  dsimp -failIfUnchanged
  rw [Int.mul_emod, he, <- Int.mul_emod]
theorem z225 (K L n : Nat) (cs : List (Nat × Nat)) (E : Nat)
    (hbound : (E : Int) ≤ (K * L : Int) * ((K * L : Int) - 1 - 2 * (K : Int))) :
    ((2 : Int) ^ E) ∣ det ((z204 K 0 L).map (z223 n)) cs := by
  set rs := (z204 K 0 L).map (fun kl => (kl.1, z178 kl.2))
  have hdiv : ((2 : Int) ^ E) ∣
      det (rs.map (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x)) (cs.map (z221 n)) := by
    apply M2.z65 K E
    · simp only [rs, List.length_map, z206, Nat.cast_mul] at hbound ⊢
      exact hbound
    · intro k q hkq
      rcases List.mem_map.mp hkq with ⟨⟨k', l⟩, hin, heq⟩
      injection heq with hk hq
      subst hk hq
      rw [z207] at hin
      exact ⟨by omega, z220 l⟩
  rw [M12.z86] at hdiv
  simp only [rs, List.map_map] at hdiv
  have hext : det ((z204 K 0 L).map
      ((fun r c => r (z221 n c)) ∘ (fun p (x : Nat) => (x : Int) ^ p.1 * p.2 ^ x) ∘
        (fun kl => (kl.1, z178 kl.2)))) cs =
      det ((z204 K 0 L).map (z223 n)) cs := by
    apply z217
    intro ⟨k, l⟩ _ c _
    simp [Function.comp_apply, z223, z222]
  rwa [hext] at hdiv
theorem z226 (K L n : Nat) (u : Int) (cs : List (Nat × Nat)) (E : Nat)
    (hE : E ≤ n)
    (hbound : (E : Int) ≤ (K * L : Int) * ((K * L : Int) - 1 - 2 * (K : Int)))
    (hbad : ((2 : Int) ^ n) ∣ ((-3 : Int) ^ n - u)) :
    ((2 : Int) ^ E) ∣ det ((z204 K 0 L).map (entry n u)) cs := by
  have hcongr : ((2 : Int) ^ n) ∣
      (det ((z204 K 0 L).map (entry n u)) cs -
        det ((z204 K 0 L).map (z223 n)) cs) := by
    apply z218
    intro kl _ rs _
    exact z224 n u kl rs hbad
  have hd : ((2 : Int) ^ E) ∣
      (det ((z204 K 0 L).map (entry n u)) cs -
        det ((z204 K 0 L).map (z223 n)) cs) :=
     dvd_trans (M13.z7 E n hE) hcongr
  have hcomp := z225 K L n cs E hbound
  rcases hd with ⟨a, ha⟩
  rcases hcomp with ⟨b, hb⟩
  refine ⟨a + b, by linarith⟩
end M5
namespace M7
open M3 M6 M9 M8
private theorem z227 {a b : Int} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ n : Nat, a ^ n ≤ b ^ n
  | 0 => by simp
  | n + 1 => by
    rw [pow_succ, pow_succ]
    have hb : 0 ≤ b := le_trans ha hab
    exact mul_le_mul (z227 ha hab n) hab ha (pow_nonneg hb n)
private theorem z228 {a : Int} (ha : 1 ≤ a) : ∀ k : Nat, 1 ≤ a ^ k
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ]
    have hk := z228 ha k
    nlinarith
private theorem z229 {a : Int} (ha : 1 ≤ a) {n m : Nat} (hnm : n ≤ m) :
    a ^ n ≤ a ^ m := by
  rcases Nat.le.dest hnm with ⟨k, rfl⟩
  rw [pow_add]
  have hk : 1 ≤ a ^ k := z228 ha k
  have hn : 0 ≤ a ^ n := pow_nonneg (by linarith) n
  nlinarith
private theorem z230 (a b : Int) : |a * b| = |a| * |b| := by
  rcases le_total 0 a with ha | ha <;> rcases le_total 0 b with hb | hb
  · rw [abs_of_nonneg ha, abs_of_nonneg hb, abs_of_nonneg (mul_nonneg ha hb)]
  · rw [abs_of_nonneg ha, abs_of_nonpos hb, abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonneg hb, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha hb)]
    ring
  · rw [abs_of_nonpos ha, abs_of_nonpos hb, abs_of_nonneg (mul_nonneg_of_nonpos_of_nonpos ha hb)]
    ring
private theorem z231 (a : Int) : ∀ n : Nat, |a ^ n| = |a| ^ n
  | 0 => by simp
  | n + 1 => by rw [pow_succ, pow_succ, z230, z231 a n]
theorem z232 (n m R S r s : Nat)
    (hR : R ≤ n) (hn : n ≤ 2 ^ m) (hS : S ≤ 2 ^ m) (hr : r < R) (hs : s < S) :
    0 ≤ z169 n (r, s) /\ z169 n (r, s) ≤ (2 : Int) ^ (2 * m) := by
  unfold z169
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
theorem z233 (n : Nat) (u : Int) (k l r s m : Nat)
    (hu0 : 0 ≤ u) (hu : u ≤ (2 : Int) ^ m)
    (hp0 : 0 ≤ z169 n (r, s)) (hp : z169 n (r, s) ≤ (2 : Int) ^ (2 * m)) :
    |entry n u (k, l) (r, s)| ≤ (2 : Int) ^ (2 * m * k + (2 * r + m * s) * l) := by
  have h3r : (3 : Int) ^ r ≤ (2 : Int) ^ (2 * r) := by
    rw [pow_mul]
    exact z227 (by decide) (by decide) r
  have hus : u ^ s ≤ (2 : Int) ^ (m * s) := by
    rw [pow_mul]
    exact z227 hu0 hu s
  have hheight : (3 : Int) ^ r * u ^ s ≤ (2 : Int) ^ (2 * r + m * s) := by
    rw [pow_add]
    exact mul_le_mul h3r hus (pow_nonneg hu0 s) (by positivity)
  have hpoint : (z169 n (r, s)) ^ k ≤ ((2 : Int) ^ (2 * m)) ^ k :=
    z227 hp0 hp k
  have hpower : ((3 : Int) ^ r * u ^ s) ^ l ≤ ((2 : Int) ^ (2 * r + m * s)) ^ l :=
    z227 (mul_nonneg (by positivity) (pow_nonneg hu0 s)) hheight l
  unfold entry z193
  dsimp -failIfUnchanged
  rw [z230, z231, z231, z230, z231, z231]
  rw [abs_of_nonneg hp0, abs_of_nonneg hu0]
  have habs3 : |(-3 : Int)| = 3 := by decide
  rw [habs3]
  calc (z169 n (r, s)) ^ k * ((3 : Int) ^ r * u ^ s) ^ l
    _ ≤ ((2 : Int) ^ (2 * m)) ^ k * ((2 : Int) ^ (2 * r + m * s)) ^ l :=
      mul_le_mul hpoint hpower (by positivity) (by positivity)
    _ = (2 : Int) ^ (2 * m * k + (2 * r + m * s) * l) := by
      rw [<- pow_mul, <- pow_mul, <- pow_add]
theorem z234 (K L n : Nat) (u : Int) (R S : Nat) (cs : List (Nat × Nat)) (m B : Nat)
    (hlen : cs.length = K * L) (hcols : ∀ c ∈ cs, c ∈ z170 R S)
    (hu0 : 0 ≤ u) (hu : u ≤ (2 : Int) ^ m)
    (hR : R ≤ n) (hn : n ≤ 2 ^ m) (hS : S ≤ 2 ^ m)
    (hN : K * L ≤ 2 ^ m)
    (hex : 2 * m * K + (2 * R + m * S) * L ≤ B) :
    |det ((z204 K 0 L).map (entry n u)) cs| ≤ (2 : Int) ^ ((K * L) * (m + B)) := by
  have hlen_rows : ((z204 K 0 L).map (entry n u)).length = K * L := by
    rw [List.length_map, z206]
  have hbound := M12.z83 ((z204 K 0 L).map (entry n u)) cs m B
    (by rw [hlen_rows, hlen]) (by rw [hlen_rows]; exact hN)
  rw [hlen_rows] at hbound
  apply hbound
  intro row hrow ⟨r, s⟩ hrs
  rcases List.mem_map.mp hrow with ⟨⟨k, l⟩, hkl, rfl⟩
  rw [z207] at hkl
  have hrs_grid := (z172 R S r s).mp (hcols (r, s) hrs)
  have hpb := z232 n m R S r s hR hn hS hrs_grid.1 hrs_grid.2
  have heb := z233 n u k l r s m hu0 hu hpb.1 hpb.2
  refine le_trans heb ?_
  apply z229 (by decide : (1 : Int) ≤ 2)
  have h1 : 2 * m * k ≤ 2 * m * K := Nat.mul_le_mul_left (2 * m) (by omega)
  have h2 : 2 * r + m * s ≤ 2 * R + m * S := by
    have : m * s ≤ m * S := Nat.mul_le_mul_left m (by omega)
    omega
  have h3 : (2 * r + m * s) * l ≤ (2 * R + m * S) * L :=
    Nat.mul_le_mul h2 (by omega)
  omega
end M7
namespace M11
open M3 M6 M9 M8 M5 M7
theorem exclusion : M13.large_exclusion := by
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
  have hdim := M16.z149 m n hm hbits1
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
  rcases z216 K L n (u : Int) R0 S hR0_le_n hroot (by omega) with ⟨cs, hlen, hcols, hnz⟩
  set T := (2048 * m ^ 3) * (2048 * m ^ 3 - 1 - 2 * (256 * m ^ 2))
  set B := 1664 * m ^ 3
  set U := (2048 * m ^ 3) * (m + B)
  have hgap := M16.z150 m (by omega)
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
  have hdiv : ((2 : Int) ^ T) ∣ det ((z204 K 0 L).map (entry n (u : Int))) cs := by
    apply z226 K L n (u : Int) cs T hT_le_n _ hbad
    have hT_eq : T = (K * L) * (K * L - 1 - 2 * K) := by rw [hKL]
    have hsub1 : 1 ≤ K * L := by rw [hKL]; omega
    have hsub2 : 2 * K ≤ K * L - 1 := by rw [hKL]; dsimp -failIfUnchanged [K]; omega
    rw [hT_eq]
    push_cast [hsub1, hsub2]
    rfl
  have hupper : |det ((z204 K 0 L).map (entry n (u : Int))) cs| ≤ (2 : Int) ^ U := by
    have hU : U = (K * L) * (m + B) := by rw [hKL]
    rw [hU]
    apply z234 K L n (u : Int) R S cs m B hlen hcols (by omega)
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
  exact M12.z84 _ U T hUT hnz hdiv hupper
end M11
namespace M15
def A (i : Nat) : Nat := 3 ^ i * 4 - 1
def B (i : Nat) : Nat := 3 ^ i * 6 + i + 4
def F (i : Nat) : Nat := 3 ^ i * 2 + i + 5
def core : Prop := ∀ i : Nat, 7 ≤ i -> ¬ (2 ^ (i + 1) ∣ F i)
inductive z235 : Nat -> Nat -> Prop where
  | R1 (i n : Nat) : 3 ^ i * 2 - i - 2 ≤ n /\ n ≤ 3 ^ i * 6 - i - 6 -> n % 2 = i % 2 ->
      z235 n ((n + B i) / 2)
  | R2 (i n : Nat) : 3 ^ i * 2 - i ≤ n /\ n ≤ 3 ^ i * 6 - i - 10 -> n % 2 = (i + 1) % 2 ->
      z235 n (A (i + 1))
inductive z236 : Nat -> Nat -> Prop where
  | one (x y : Nat) : z235 x y -> z236 x y
  | cons (x y z : Nat) : z235 x y -> z236 y z -> z236 x z
lemma z237 (i : Nat) : i + 1 ≤ 3 ^ i := by
  induction i with
  | zero => decide
  | succ i ih =>
    rw [Nat.pow_succ]
    omega
lemma z238 (i : Nat) (hi : 7 ≤ i) : 2 ^ i * (2 * i + 13) < 3 ^ i * 2 := by
  induction i, hi using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    have hpos : 0 < 2 ^ m := by positivity
    rw [Nat.pow_succ, Nat.pow_succ]
    nlinarith
lemma z239 (n : Nat) (hn : 0 < n) : ∃ v q : Nat, n = 2 ^ v * q /\ q % 2 = 1 /\ 0 < q := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases heven : n % 2 = 0
    · obtain ⟨v, q, he, ho, hq⟩ := ih (n / 2) (by omega) (by omega)
      refine ⟨v + 1, q, ?_, ho, hq⟩
      have hn2 : n = 2 * (n / 2) := by omega
      rw [hn2, he, Nat.pow_succ]
      ring
    · exact ⟨0, n, by simp, by omega, hn⟩
lemma z240 (i : Nat) (hc : core) (hi : 7 ≤ i) :
    ∃ v q : Nat, F i = 2 ^ v * q /\ q % 2 = 1 /\ 2 * i + 15 ≤ q := by
  obtain ⟨v, q, hf, ho, hq⟩ := z239 (F i) (by unfold F; omega)
  have hv : v ≤ i := by
    by_contra hgt
    push Not at hgt
    apply hc i hi
    refine ⟨2 ^ (v - (i + 1)) * q, ?_⟩
    have hv_eq : v = (i + 1) + (v - (i + 1)) := by omega
    conv_lhs => rw [hf, hv_eq, Nat.pow_add]
    ring
  have hp : 2 ^ v ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hv
  have hlarge := z238 i hi
  have hqbound : 2 * i + 13 < q := by
    by_contra hle
    push Not at hle
    have hmul : 2 ^ v * q ≤ 2 ^ i * (2 * i + 13) := Nat.mul_le_mul hp hle
    unfold F at hf
    omega
  exact ⟨v, q, hf, ho, by omega⟩
lemma z241 (i v q : Nat) (hi : 7 ≤ i) (ho : q % 2 = 1)
    (hq : 2 * i + 15 ≤ q) (hd : 2 ^ v * q ≤ F i) :
    z236 (B i - 2 ^ v * q) (A (i + 1)) := by
  induction v with
  | zero =>
    apply z236.one
    apply z235.R2 i
    · have hp3 := z237 i
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
    have hp3 := z237 i
    have hdiv : (B i - 2 ^ v * 2 * q + B i) / 2 = B i - 2 ^ v * q := by
      unfold B F at *
      omega
    have hstep : z235 (B i - 2 ^ v * 2 * q) (B i - 2 ^ v * q) := by
      rw [<- hdiv]
      apply z235.R1 i
      · have hq_pos : 1 * (2 * i + 15) ≤ 2 ^ v * q := Nat.mul_le_mul hp hq
        unfold B F at *
        omega
      · unfold B F at *
        omega
    exact z236.cons _ _ _ hstep (ih (by omega))
theorem z242 (i : Nat) (hc : core) (hi : 7 ≤ i) : z236 (A i) (A (i + 1)) := by
  obtain ⟨v, q, hf, ho, hq⟩ := z240 i hc hi
  have h := z241 i v q hi ho hq (by omega)
  rw [<- hf] at h
  have hba : B i - F i = A i := by
    have hp3 := z237 i
    unfold A B F
    omega
  rw [hba] at h
  exact h
end M15
namespace M0
theorem core (hlarge : M13.large_exclusion) : M15.core := by
  intro i hi ⟨q, hq⟩
  apply M13.z165 hlarge i hi
  refine ⟨(q : Int), ?_⟩
  have hq_int : (M15.F i : Int) = ((2 ^ (i + 1) * q : Nat) : Int) := by exact_mod_cast hq
  unfold M15.F at hq_int
  unfold M13.F
  push_cast at hq_int
  linarith
end M0


variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 8000000
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma z243 (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma z244 (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma append_assoc (l1 l2 : zF) (s : zB) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, z244, ih]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c1 c2 : Cfg zG_ zL_) (h : c1 [tm]⊢ c2) :
    c1 [tm]⊢^{1} c2 := by simp [h]
lemma z01 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c1 c2 : Cfg zG_ zL_) (h : c1 [tm]⊢ c2) :
    c1 [tm]⊢⁺ c2 := ⟨1, by decide, zSm tm c1 c2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep tm c1 (n + m) = (multiStep tm c1 n).bind (fun c2 => multiStep tm c2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c1 c2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h₁ : c1 [tm]⊢^{n} c2) (h₂ : c2 [tm]⊢^{m} c_3) :
    c1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 c_3 : Cfg zG_ zL_}
    (h₁ : c1 [tm]⊢* c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c1 c2 c_3 n m hn hm⟩
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 : Cfg zG_ zL_} (h : c1 [tm]⊢⁺ c2) :
    c1 [tm]⊢* c2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 c_3 : Cfg zG_ zL_}
    (h₁ : c1 [tm]⊢⁺ c2) (h₂ : c2 [tm]⊢⁺ c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c1 c2 c_3 n m hn hm⟩
lemma z02 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 c_3 : Cfg zG_ zL_}
    (h₁ : c1 [tm]⊢⁺ c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c1 c2 c_3 n m hn hm⟩
lemma z03 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 c_3 : Cfg zG_ zL_}
    (h₁ : c1 [tm]⊢* c2) (h₂ : c2 [tm]⊢⁺ c_3) : c1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c1 c2 c_3 n m hn hm⟩
lemma z04 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c1 c2 c_3 : Cfg zG_ zL_}
    (h₁ : c1 [tm]⊢ c2) (h₂ : c2 [tm]⊢* c_3) : c1 [tm]⊢⁺ c_3 :=
  z02 (z01 tm c1 c2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> rfl)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z04 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, z00, zDh, zDt])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
def z245 : Nat -> zB -> zB
  | 0, r => r
  | b + 1, r => (0 : Fin 2) >> (1 : Fin 2) >> z245 b r
def z246 : Nat -> zB -> zB
  | 0, r => r
  | a + 1, r => (1 : Fin 2) >> (1 : Fin 2) >> z246 a r
@[simp] lemma z247 (r : zB) : z245 0 r = r := rfl
@[simp] lemma z248 (b : Nat) (r : zB) : z245 (b + 1) r = (0 : Fin 2) >> (1 : Fin 2) >> z245 b r := rfl
lemma z249 (b : Nat) (r : zB) :
    z245 (b + 1) r = z245 b ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  induction b with
  | zero => rfl
  | succ b ih => rw [z248 (b + 1), ih, <- z248 b]
lemma z250 (b1 b2 : Nat) (r : zB) : z245 (b1 + b2) r = z245 b1 (z245 b2 r) := by
  induction b1 with
  | zero => simp
  | succ b1 ih => rw [Nat.succ_add, z248, z248, ih]
@[simp] lemma z251 (r : zB) : z246 0 r = r := rfl
@[simp] lemma z252 (a : Nat) (r : zB) : z246 (a + 1) r = (1 : Fin 2) >> (1 : Fin 2) >> z246 a r := rfl
lemma z253 (a : Nat) (r : zB) :
    z246 (a + 1) r = z246 a ((1 : Fin 2) >> (1 : Fin 2) >> r) := by
  induction a with
  | zero => rfl
  | succ a ih => rw [z252 (a + 1), ih, <- z252 a]
lemma z254 (a1 a2 : Nat) (r : zB) : z246 (a1 + a2) r = z246 a1 (z246 a2 r) := by
  induction a1 with
  | zero => simp
  | succ a1 ih => rw [Nat.succ_add, z252, z252, ih]
lemma z255 (b : Nat) (l r : zB) :
    (l {{B}}> z245 b r) [target_tm]⊢* (z245 b l {{B}}> r) := by
  induction b generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [z248, z249]
    have h1 : (l {{B}}> ((0 : Fin 2) >> (1 : Fin 2) >> z245 b r)) [target_tm]⊢⁺
        (((0 : Fin 2) >> (1 : Fin 2) >> l) {{B}}> z245 b r) := by execute
    exact zSt (zPs h1) (ih _)
lemma z256 (b : Nat) (l r : zB) :
    (z245 b l <{{C}} r) [target_tm]⊢* (l <{{C}} z245 b r) := by
  induction b generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [z248, z249]
    have h1 : (((0 : Fin 2) >> (1 : Fin 2) >> z245 b l) <{{C}} r) [target_tm]⊢⁺
        (z245 b l <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by execute
    exact zSt (zPs h1) (ih _)
lemma z257 (b : Nat) (l r : zB) :
    (l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 b r)) [target_tm]⊢*
    (z246 b l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r)) := by
  induction b generalizing l with
  | zero => exact ⟨0, rfl⟩
  | succ b ih =>
    rw [z248, z253]
    have h1 : (l {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> z245 b r))
        [target_tm]⊢⁺
        (((1 : Fin 2) >> (1 : Fin 2) >> l) {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 b r)) := by execute
    exact zSt (zPs h1) (ih _)
lemma z258 (a : Nat) (l r : zB) :
    (z246 a l <{{A}} r) [target_tm]⊢* (l <{{A}} z246 a r) := by
  induction a generalizing r with
  | zero => exact ⟨0, rfl⟩
  | succ a ih =>
    rw [z252, z253]
    have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> z246 a l) <{{A}} r) [target_tm]⊢⁺
        (z246 a l <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> r)) := by execute
    exact zSt (zPs h1) (ih _)
abbrev d0 : zB := default
def S1 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> z246 a d0) <{{C}} z245 b (z246 c ((0 : Fin 2) >> (1 : Fin 2) >> d0))
def S2 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> z246 a d0) <{{C}} z245 b ((1 : Fin 2) >> d0)
def S3 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((1 : Fin 2) >> z246 a d0) <{{C}} z245 b d0
lemma z259 (a b c : Nat) :
    (S1 (1 + a) b (2 + c)) [target_tm]⊢* (S1 a (3 + b) c) := by
  unfold S1
  rw [Nat.add_comm 1 a, Nat.add_comm 2 c, Nat.add_comm 3 b]
  simp only [z252]
  set l0 := (1 : Fin 2) >> z246 a d0
  set r0 := z246 c ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)) := by execute
  have h2 := z255 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)
  rw [<- z249 b l0] at h2
  have h3 : (z245 (b + 1) l0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (z245 (b + 2) l0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> r0)) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 2) l0 ((0 : Fin 2) >> (1 : Fin 2) >> r0)
  rw [<- z249 (b + 2) r0] at h4
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) h4))
lemma z260 (n a b c : Nat) :
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
    exact zSt (z259 (n + a) b (n * 2 + c)) (ih a (3 + b) c)
lemma z261 (b c : Nat) :
    (S1 0 b (3 + c)) [target_tm]⊢* (S1 (2 + b) 2 c) := by
  unfold S1
  rw [Nat.add_comm 3 c, Nat.add_comm 2 b]
  simp only [z251, z252]
  set r0 := z246 c ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h1 : (((1 : Fin 2) >> d0) <{{C}} z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (d0 {{B}}> z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)) := by execute
  have h2 := z255 b d0 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)
  have h3 : (z245 b d0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (z245 (b + 1) d0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 1) d0 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0)
  have h5 : (d0 <{{C}} z245 (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 2) ((1 : Fin 2) >> (1 : Fin 2) >> r0))) := by
    rw [z249 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> r0)]
    execute
  have h6 := z257 (b + 2) d0 ((1 : Fin 2) >> (1 : Fin 2) >> r0)
  have h7 : (z246 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> r0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> z246 (b + 2) d0) <{{C}} z245 2 r0) := by
    simp only [z248, z247]
    execute
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) (zSt h4 (zSt (zPs h5) (zSt h6 (zPs h7))))))
lemma z262 (a b : Nat) :
    (S2 (1 + a) b) [target_tm]⊢* (S2 a (3 + b)) := by
  unfold S2
  rw [Nat.add_comm 1 a, Nat.add_comm 3 b]
  simp only [z252]
  set l0 := (1 : Fin 2) >> z246 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} z245 b ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> z245 b ((1 : Fin 2) >> d0)) := by execute
  have h2 := z255 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) ((1 : Fin 2) >> d0)
  rw [<- z249 b l0] at h2
  have h3 : (z245 (b + 1) l0 {{B}}> ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (z245 (b + 3) l0 <{{C}} ((1 : Fin 2) >> d0)) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 3) l0 ((1 : Fin 2) >> d0)
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) h4))
lemma z263 (a b : Nat) :
    (S2 a b) [target_tm]⊢* (S2 0 (a * 3 + b)) := by
  induction a generalizing b with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add]
    exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : a + 1 = 1 + a := by omega
    have h2 : (a + 1) * 3 + b = a * 3 + (3 + b) := by omega
    rw [h2, h1]
    exact zSt (z262 a b) (ih (3 + b))
lemma Ov2 (b : Nat) :
    (S2 0 b) [target_tm]⊢* (S3 (2 + b) 1) := by
  unfold S2 S3
  rw [Nat.add_comm 2 b]
  simp only [z251]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} z245 b ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{B}}> z245 b ((1 : Fin 2) >> d0)) := by execute
  have h2 := z255 b d0 ((1 : Fin 2) >> d0)
  have h3 : (z245 b d0 {{B}}> ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (z245 (b + 2) d0 <{{C}} ((1 : Fin 2) >> d0)) := by
    cases b with
    | zero =>
      simp only [Nat.zero_add, z248, z247]
      execute
    | succ b =>
      simp only [Nat.succ_add, z248]
      execute
  have h4 := z256 (b + 2) d0 ((1 : Fin 2) >> d0)
  have h5 : (d0 <{{C}} z245 (b + 2) ((1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 2) ((1 : Fin 2) >> d0))) := by execute
  have h6 := z257 (b + 2) d0 ((1 : Fin 2) >> d0)
  have h7 : (z246 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> z246 (b + 2) d0) <{{C}} z245 1 d0) := by
    simp only [z248, z247]
    execute
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) (zSt h4 (zSt (zPs h5) (zSt h6 (zPs h7))))))
lemma z264 (a b : Nat) :
    (S3 (1 + a) b) [target_tm]⊢* (S3 a (2 + b)) := by
  unfold S3
  rw [Nat.add_comm 1 a, Nat.add_comm 2 b]
  simp only [z252]
  set l0 := (1 : Fin 2) >> z246 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}} z245 b d0)
      [target_tm]⊢⁺ (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}> z245 b d0) := by execute
  have h2 := z255 b ((0 : Fin 2) >> (1 : Fin 2) >> l0) d0
  rw [<- z249 b l0] at h2
  have h3 : (z245 (b + 1) l0 {{B}}> d0)
      [target_tm]⊢⁺ (z245 (b + 2) l0 <{{C}} d0) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 2) l0 d0
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) h4))
lemma z265 (a b : Nat) :
    (S3 a b) [target_tm]⊢* (S3 0 (a * 2 + b)) := by
  induction a generalizing b with
  | zero =>
    simp only [Nat.zero_mul, Nat.zero_add]
    exact ⟨0, rfl⟩
  | succ a ih =>
    have h1 : a + 1 = 1 + a := by omega
    have h2 : (a + 1) * 2 + b = a * 2 + (2 + b) := by omega
    rw [h2, h1]
    exact zSt (z264 a b) (ih (2 + b))
lemma Ov3 (b : Nat) :
    (S3 0 b) [target_tm]⊢⁺ (S1 0 2 (2 + b)) := by
  unfold S3 S1
  rw [Nat.add_comm 2 b]
  simp only [z251]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} z245 b d0)
      [target_tm]⊢⁺ (d0 {{B}}> z245 b d0) := by execute
  have h2 := z255 b d0 d0
  have h3 : (z245 b d0 {{B}}> d0)
      [target_tm]⊢⁺ (z245 (b + 1) d0 <{{C}} d0) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 1) d0 d0
  have h5 : (d0 <{{C}} z245 (b + 1) d0)
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 1) d0)) := by execute
  have h6 := z257 (b + 1) d0 d0
  have h7 : (z246 (b + 1) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (z246 (b + 3) d0 <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [z252]
    execute
  have h8 := z258 (b + 3) d0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h9 : (d0 <{{A}} z246 (b + 3) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> d0) <{{C}} z245 2 (z246 (b + 2) ((0 : Fin 2) >> (1 : Fin 2) >> d0))) := by
    rw [<- z253 (b + 3) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    simp only [z252, z248, z247]
    execute
  exact z02 h1 (zSt h2 (zSt (zPs h3) (zSt h4 (zSt (zPs h5) (zSt h6 (zSt (zPs h7) (zSt h8 (zPs h9))))))))
lemma z266 (a b : Nat) :
    (S3 a b) [target_tm]⊢⁺ (S1 0 2 (2 + a * 2 + b)) := by
  have h1 := z265 a b
  have h2 := Ov3 (a * 2 + b)
  have heq : 2 + (a * 2 + b) = 2 + a * 2 + b := by omega
  rw [heq] at h2
  exact z03 h1 h2
lemma z267 (a b : Nat) :
    (S2 a b) [target_tm]⊢* (S1 0 2 (7 + a * 6 + b * 2)) := by
  have h1 := z263 a b
  have h2 := Ov2 (a * 3 + b)
  have h3 := zPs (z266 (2 + (a * 3 + b)) 1)
  have heq : 2 + (2 + (a * 3 + b)) * 2 + 1 = 7 + a * 6 + b * 2 := by omega
  rw [heq] at h3
  exact zSt h1 (zSt h2 h3)
lemma z268 (a b : Nat) :
    (S1 (2 + a) b 1) [target_tm]⊢⁺ (S2 a (6 + b)) := by
  unfold S1 S2
  rw [Nat.add_comm 2 a, Nat.add_comm 6 b]
  simp only [z252, z251]
  set l0 := (1 : Fin 2) >> z246 a d0
  have h1 : (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h2 := z255 b ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> l0)
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  rw [<- z249 b ((1 : Fin 2) >> (1 : Fin 2) >> l0)] at h2
  have h3 : (z245 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> l0)) <{{A}}
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [z248]
    execute
  have h4 : (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 1) ((1 : Fin 2) >> (1 : Fin 2) >> l0)) <{{A}}
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (z245 (b + 4) ((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [z248]
    execute
  have h5 := z256 (b + 4) ((1 : Fin 2) >> (1 : Fin 2) >> l0)
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h6 : (((1 : Fin 2) >> (1 : Fin 2) >> l0) <{{C}}
      z245 (b + 4) ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> l0) {{B}}>
      z245 (b + 4) ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h7 := z255 (b + 4) ((0 : Fin 2) >> (1 : Fin 2) >> l0)
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  rw [<- z249 (b + 4) l0] at h7
  have h8 : (z245 (b + 5) l0 {{B}}> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺
      (z245 (b + 6) l0 <{{C}} ((1 : Fin 2) >> d0)) := by
    simp only [z248]
    execute
  have h9 := z256 (b + 6) l0 ((1 : Fin 2) >> d0)
  exact z02 h1 (zSt h2 (zSt (zPs h3) (zSt (zPs h4) (zSt h5 (zSt (zPs h6) (zSt h7 (zSt (zPs h8) h9)))))))
lemma z269 (a b : Nat) :
    (S1 (2 + a) b 1) [target_tm]⊢⁺ (S1 0 2 (19 + a * 6 + b * 2)) := by
  have h1 := z268 a b
  have h2 := z267 a (6 + b)
  have heq : 7 + a * 6 + (6 + b) * 2 = 19 + a * 6 + b * 2 := by omega
  rw [heq] at h2
  exact z02 h1 h2
lemma z270 (a b : Nat) :
    (S1 a b 0) [target_tm]⊢⁺ (S1 0 2 (3 + a * 2 + b)) := by
  have heq1 : S1 a b 0 = S3 a (1 + b) := by
    rw [Nat.add_comm 1 b]
    unfold S1 S3
    simp only [z251, <- z249]
  rw [heq1]
  have h := z266 a (1 + b)
  have heq2 : 2 + a * 2 + (1 + b) = 3 + a * 2 + b := by omega
  rw [heq2] at h
  exact h
def P (n1 n2 : Nat) : Prop :=
  ∀ c : Nat, (S1 0 2 (n1 + c)) [target_tm]⊢* (S1 n2 2 c)
lemma P_O : P 0 0 := by
  intro c
  simp only [Nat.zero_add]
  exact ⟨0, rfl⟩
lemma P_S (n1 n2 : Nat) (hp : P n1 n2) :
    P (n1 + n2 * 2 + 3) (4 + n2 * 3) := by
  intro c
  have h1 := hp (n2 * 2 + (3 + c))
  have heq1 : n1 + (n2 * 2 + (3 + c)) = n1 + n2 * 2 + 3 + c := by omega
  rw [heq1] at h1
  have h2 := z260 n2 0 2 (3 + c)
  simp only [Nat.add_zero] at h2
  have h3 := z261 (n2 * 3 + 2) c
  have heq2 : 2 + (n2 * 3 + 2) = 4 + n2 * 3 := by omega
  rw [heq2] at h3
  exact zSt h1 (zSt h2 h3)
lemma P_n (i : Nat) : P (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 2) := by
  induction i with
  | zero => exact P_O
  | succ i ih =>
    have hps := P_S _ _ ih
    have hp3 := M15.z237 i
    have heq1 : 3 ^ i * 2 - i - 2 + (3 ^ i * 2 - 2) * 2 + 3 = 3 ^ (i + 1) * 2 - (i + 1) - 2 := by
      rw [Nat.pow_succ]
      omega
    have heq2 : 4 + (3 ^ i * 2 - 2) * 3 = 3 ^ (i + 1) * 2 - 2 := by
      rw [Nat.pow_succ]
      omega
    rw [heq1, heq2] at hps
    exact hps
def S' (n : Nat) : Cfg (Fin 2) (Fin 6) := S1 0 2 n
lemma z271 (n1 n2 c : Nat) (hp : P n1 (c + (2 + n2))) :
    (S' (n1 + c * 2 + 1)) [target_tm]⊢⁺ (S' (23 + n2 * 6 + c * 6)) := by
  unfold S'
  have h1 := hp (c * 2 + 1)
  have heq1 : n1 + (c * 2 + 1) = n1 + c * 2 + 1 := by omega
  rw [heq1] at h1
  have h2 := z260 c (2 + n2) 2 1
  have h3 := z269 n2 (c * 3 + 2)
  have heq2 : 19 + n2 * 6 + (c * 3 + 2) * 2 = 23 + n2 * 6 + c * 6 := by omega
  rw [heq2] at h3
  exact z03 h1 (z03 h2 h3)
lemma z272 (n1 n2 c : Nat) (hp : P n1 (c + n2)) :
    (S' (n1 + c * 2 + 0)) [target_tm]⊢⁺ (S' (5 + n2 * 2 + c * 3)) := by
  unfold S'
  have h1 := hp (c * 2 + 0)
  have heq1 : n1 + (c * 2 + 0) = n1 + c * 2 + 0 := by omega
  rw [heq1] at h1
  have h2 := z260 c n2 2 0
  have h3 := z270 n2 (c * 3 + 2)
  have heq2 : 3 + n2 * 2 + (c * 3 + 2) = 5 + n2 * 2 + c * 3 := by omega
  rw [heq2] at h3
  exact z03 h1 (z03 h2 h3)
lemma z272' (i n : Nat) (hn : 3 ^ i * 2 - i - 2 ≤ n /\ n ≤ 3 ^ i * 6 - i - 6)
    (hp : n % 2 = i % 2) :
    (S' n) [target_tm]⊢⁺ (S' ((n + (3 ^ i * 6 + i + 4)) / 2)) := by
  have hp3 := M15.z237 i
  have hpn := P_n i
  set c := (n - (3 ^ i * 2 - i - 2)) / 2
  have hc_eq : c + (3 ^ i * 2 - 2 - c) = 3 ^ i * 2 - 2 := by omega
  rw [<- hc_eq] at hpn
  have hbs := z272 (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 2 - c) c hpn
  have heq1 : 3 ^ i * 2 - i - 2 + c * 2 + 0 = n := by omega
  have heq2 : 5 + (3 ^ i * 2 - 2 - c) * 2 + c * 3 = (n + (3 ^ i * 6 + i + 4)) / 2 := by omega
  rw [heq1, heq2] at hbs
  exact hbs
lemma z271' (i n : Nat) (hn : 3 ^ i * 2 - i ≤ n /\ n ≤ 3 ^ i * 6 - i - 10)
    (hp : n % 2 = (i + 1) % 2) :
    (S' n) [target_tm]⊢⁺ (S' (3 ^ i * 12 - 1)) := by
  have hp3 := M15.z237 i
  have hpn := P_n i
  set c := (n - (3 ^ i * 2 - i - 2)) / 2
  have hc_eq : c + (2 + (3 ^ i * 2 - 4 - c)) = 3 ^ i * 2 - 2 := by omega
  rw [<- hc_eq] at hpn
  have hbs := z271 (3 ^ i * 2 - i - 2) (3 ^ i * 2 - 4 - c) c hpn
  have heq1 : 3 ^ i * 2 - i - 2 + c * 2 + 1 = n := by omega
  have heq2 : 23 + (3 ^ i * 2 - 4 - c) * 6 + c * 6 = 3 ^ i * 12 - 1 := by omega
  rw [heq1, heq2] at hbs
  exact hbs
lemma z273 (b : Nat) :
    (S1 0 b 2) [target_tm]⊢* (S1 0 2 (b + 4)) := by
  unfold S1
  simp only [z251, z252]
  have h1 : (((1 : Fin 2) >> d0) <{{C}} z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{B}}> z245 b ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by execute
  have h2 := z255 b d0 ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h3 : (z245 b d0 {{B}}> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (z245 (b + 1) d0 <{{C}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [z248]
    execute
  have h4 := z256 (b + 1) d0 ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h5 : (d0 <{{C}} z245 (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> z245 (b + 2) ((0 : Fin 2) >> (1 : Fin 2) >> d0))) := by
    rw [z249 (b + 1) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    execute
  have h6 := z257 (b + 2) d0 ((0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h7 : (z246 (b + 2) d0 {{A}}> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (z246 (b + 5) d0 <{{A}} ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)) := by
    simp only [z252]
    execute
  have h8 := z258 (b + 5) d0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0)
  have h9 : (d0 <{{A}} z246 (b + 5) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> d0))
      [target_tm]⊢⁺ (((1 : Fin 2) >> d0) <{{C}} z245 2 (z246 (b + 4) ((0 : Fin 2) >> (1 : Fin 2) >> d0))) := by
    rw [<- z253 (b + 5) ((0 : Fin 2) >> (1 : Fin 2) >> d0)]
    simp only [z252, z248, z247]
    execute
  exact zSt (zPs h1) (zSt h2 (zSt (zPs h3) (zSt h4 (zSt (zPs h5) (zSt h6 (zSt (zPs h7) (zSt h8 (zPs h9))))))))
lemma z274 : (init []) [target_tm]⊢* (S' 18) := by
  have h1 : (init []) [target_tm]⊢⁺ (S3 0 1) := by
    change (d0 {{A}}> d0) [target_tm]⊢⁺ (S3 0 1)
    unfold S3
    simp only [z251, z248, z247]
    execute
  have h2 := zPs (Ov3 1)
  have h3 := zPs (z272' 1 3 ⟨by decide, by decide⟩ (by decide))
  have h4 := z261 2 10
  have h5 := z260 4 0 2 2
  have h6 := z273 14
  exact zSt (zPs h1) (zSt h2 (zSt h3 (zSt h4 (zSt h5 h6))))
lemma z275 (x y : Nat) (h : M15.z235 x y) :
    (S' x) [target_tm]⊢⁺ (S' y) := by
  cases h with
  | R1 i _ hn hp =>
    exact z272' i x hn hp
  | R2 i _ hn hp =>
    have h1 := z271' i x hn hp
    have heq : 3 ^ i * 12 - 1 = M15.A (i + 1) := by
      unfold M15.A
      rw [Nat.pow_succ]
      omega
    rw [heq] at h1
    exact h1
lemma z276 (x y : Nat) (h : M15.z236 x y) :
    (S' x) [target_tm]⊢⁺ (S' y) := by
  induction h with
  | one x y hs => exact z275 x y hs
  | cons x y z hs _ ih => exact zPt (z275 x y hs) ih
lemma zIm {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep target_tm c (j + d) = some c') :
    (multiStep target_tm c j).isSome := by
  rw [zMa] at h
  cases h_j : multiStep target_tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma z277 : (init []) [target_tm]⊢* (S' (M15.A 7)) := by
  have h0 := z274
  have h1 := zPs (z272' 2 18 ⟨by decide, by decide⟩ (by decide))
  have h2 := zPs (z271' 2 39 ⟨by decide, by decide⟩ (by decide))
  have h3 := zPs (z272' 3 107 ⟨by decide, by decide⟩ (by decide))
  have h4 := zPs (z271' 3 138 ⟨by decide, by decide⟩ (by decide))
  have h5 := zPs (z271' 4 323 ⟨by decide, by decide⟩ (by decide))
  have h6 := zPs (z272' 5 971 ⟨by decide, by decide⟩ (by decide))
  have h7 := zPs (z272' 5 1219 ⟨by decide, by decide⟩ (by decide))
  have h8 := zPs (z272' 5 1343 ⟨by decide, by decide⟩ (by decide))
  have h9 := zPs (z272' 5 1405 ⟨by decide, by decide⟩ (by decide))
  have h10 := zPs (z271' 5 1436 ⟨by decide, by decide⟩ (by decide))
  have h11 := zPs (z271' 6 2915 ⟨by decide, by decide⟩ (by decide))
  exact zSt h0 (zSt h1 (zSt h2 (zSt h3 (zSt h4 (zSt h5 (zSt h6 (zSt h7 (zSt h8 (zSt h9 (zSt h10 h11))))))))))
lemma z278 (hc : M15.core) (m : Nat) :
    ∃ N ≥ m, ∃ k, multiStep target_tm (init []) N = some (S' (M15.A (7 + k))) := by
  induction m with
  | zero =>
    obtain ⟨n0, hn0⟩ := z277
    exact ⟨n0, Nat.zero_le n0, 0, hn0⟩
  | succ m ih =>
    obtain ⟨N, hN, k, h_ms⟩ := ih
    have hlayer := z276 (M15.A (7 + k)) (M15.A (7 + k + 1)) (M15.z242 (7 + k) hc (by omega))
    obtain ⟨d, hd_pos, hd⟩ := hlayer
    refine ⟨N + d, by omega, k + 1, ?_⟩
    have heq : 7 + (k + 1) = 7 + k + 1 := by omega
    rw [heq]
    exact zMt target_tm _ _ _ N d h_ms hd
theorem nonhalt_of_core (hc : M15.core) : IsDoesNotHalt target_tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases z278 hc (n + 1) with ⟨N, hN, k, h_N⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := zIm h_N
  rw [zMs, hn] at h_some
  exact h_some

end Solution

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := nonhalt_of_core (M0.core M11.exclusion)

end BusyBeaver.M_1RB1LA_1RC1RE_1LD0RB_1LA0LC_0RF0RD_0RBHHH
