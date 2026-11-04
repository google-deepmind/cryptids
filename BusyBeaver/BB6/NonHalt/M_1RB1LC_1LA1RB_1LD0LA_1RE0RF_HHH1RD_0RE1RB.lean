/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB

end

namespace BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

abbrev target_tm : Machine (Fin 2) (Fin 6) := target
namespace Solution


variable {Γ' Λ' α β γ : Type*} [Inhabited Γ'] [Inhabited Λ']
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
local notation "TapeBlank" => ListBlank (Fin 2)
local notation "FinWord" => List (Fin 2)
theorem lem_00 (m r : Nat) (hr : r <= m) :
    ((m - r) * (m - r)) % m = (r * r) % m := by
  set b := m - r
  have h1 : b * b + m * r = r * r + m * b := by
    have hm : r + b = m := by omega
    calc b * b + m * r = b * b + (r + b) * r := by rw [hm]
      _ = r * r + (r + b) * b := by ring
      _ = r * r + m * b := by rw [hm]
  have h2 := congrArg (· % m) h1
  simpa [Nat.add_mul_mod_self_left] using h2
theorem lem_01 (m y : Nat) (hm : 0 < m) :
    ∃ r ≤ m / 2, (r * r) % m = (y * y) % m := by
  have hmod : (y * y) % m = ((y % m) * (y % m)) % m := by rw [<- Nat.mul_mod]
  have hlt : y % m < m := Nat.mod_lt y hm
  rcases (by omega : y % m <= m / 2 \/ m - y % m <= m / 2) with hle | hle
  · exact ⟨y % m, hle, hmod.symm⟩
  · refine ⟨m - y % m, hle, ?_⟩
    rw [lem_00 m (y % m) (by omega), hmod]
def sNat (n : Nat) (f : Nat -> α) : α :=
  Nat.casesOn n (f 0) (fun m => f (m + 1))
@[simp] theorem sNat_eq (n : Nat) (f : Nat -> α) : sNat n f = f n := by
  cases n <;> rfl
inductive BitTrie where
  | leaf (b : Bool)
  | node (l r : BitTrie)
def lem_02 : BitTrie -> Nat -> Bool
  | .leaf b, _ => b
  | .node l r, n => if n % 2 == 0 then sNat (n / 2) (lem_02 l) else sNat (n / 2) (lem_02 r)
def lem_03 (l r : BitTrie) : BitTrie :=
  match l with
  | .leaf false =>
    match r with
    | .leaf false => .leaf false
    | .leaf true => .node (.leaf false) (.leaf true)
    | .node l2 r2 => .node (.leaf false) (.node l2 r2)
  | .leaf true =>
    match r with
    | .leaf b2 => .node (.leaf true) (.leaf b2)
    | .node l2 r2 => .node (.leaf true) (.node l2 r2)
  | .node l1 r1 =>
    match r with
    | .leaf b2 => .node (.node l1 r1) (.leaf b2)
    | .node l2 r2 => .node (.node l1 r1) (.node l2 r2)
theorem lem_04 (l r : BitTrie) (n : Nat) :
    lem_02 (lem_03 l r) n = (if n % 2 == 0 then lem_02 l (n / 2) else lem_02 r (n / 2)) := by
  cases l with
  | leaf b1 =>
    cases b1 <;> cases r with
    | leaf b2 => cases b2 <;> simp [lem_03, lem_02]
    | node l2 r2 => simp [lem_03, lem_02]
  | node l1 r1 =>
    cases r with
    | leaf b2 => simp [lem_03, lem_02]
    | node l2 r2 => simp [lem_03, lem_02]
def lem_05 : Nat -> Nat -> BitTrie
  | 0, _ => .leaf true
  | d + 1, n =>
    if n % 2 == 0 then sNat (n / 2) (fun n2 => lem_03 (lem_05 d n2) (.leaf false))
    else sNat (n / 2) (fun n2 => lem_03 (.leaf false) (lem_05 d n2))
theorem lem_06 (d n : Nat) :
    lem_02 (lem_05 d n) n = true := by
  induction d generalizing n with
  | zero => rfl
  | succ d ih =>
    simp only [lem_05, sNat_eq]
    split_ifs with h <;> simp only [lem_04, h, ↓reduceIte, Bool.false_eq_true, ih]
def lem_07 : BitTrie -> BitTrie -> BitTrie
  | .leaf true, _ => .leaf true
  | _, .leaf true => .leaf true
  | .leaf false, t => t
  | t, .leaf false => t
  | .node l1 r1, .node l2 r2 => lem_03 (lem_07 l1 l2) (lem_07 r1 r2)
theorem lem_08 (t1 t2 : BitTrie) (n : Nat) :
    lem_02 (lem_07 t1 t2) n = (lem_02 t1 n || lem_02 t2 n) := by
  induction t1 generalizing t2 n with
  | leaf b1 =>
    cases b1 <;> cases t2 with
    | leaf b2 => cases b2 <;> rfl
    | node l2 r2 => rfl
  | node l1 r1 ih1 ih2 =>
    cases t2 with
    | leaf b2 =>
      cases b2
      · simp [lem_07, lem_02, Bool.or_false]
      · simp [lem_07, lem_02]
    | node l2 r2 =>
      simp only [lem_07, lem_04, lem_02, sNat_eq]
      split_ifs with h
      · exact ih1 l2 (n / 2)
      · exact ih2 r2 (n / 2)
def lem_09 : Nat -> Nat -> Nat -> BitTrie
  | 0, m, x => sNat ((x * x) % m) (lem_05 11)
  | k + 1, m, x => sNat (2 * x) (fun x0 => sNat (2 * x + 1) (fun x1 =>
      lem_07 (lem_09 k m x0) (lem_09 k m x1)))
theorem lem_0a (k m x y : Nat) (hy : y < 2 ^ k) :
    lem_02 (lem_09 k m x) (((x * 2 ^ k + y) * (x * 2 ^ k + y)) % m) = true := by
  induction k generalizing x y with
  | zero =>
    have hy0 : y = 0 := by omega
    subst hy0
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero, lem_09, sNat_eq]
    exact lem_06 11 _
  | succ k ih =>
    simp only [lem_09, sNat_eq, lem_08, Bool.or_eq_true]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ']; ring
    rcases (by omega : y < 2 ^ k \/ 2 ^ k <= y) with hlt | hge
    · left
      have hmul : (2 * x) * 2 ^ k = x * 2 ^ (k + 1) := by rw [Nat.pow_succ']; ring
      have heq : x * 2 ^ (k + 1) + y = (2 * x) * 2 ^ k + y := by omega
      rw [heq]
      exact ih (2 * x) y hlt
    · right
      have hmul : (2 * x + 1) * 2 ^ k = x * 2 ^ (k + 1) + 2 ^ k := by rw [Nat.pow_succ']; ring
      have heq : x * 2 ^ (k + 1) + y = (2 * x + 1) * 2 ^ k + (y - 2 ^ k) := by omega
      rw [heq]
      exact ih (2 * x + 1) (y - 2 ^ k) (by omega)
def lem_0b (m : Nat) : Nat :=
  if m <= 31 then 4 else if m <= 127 then 6 else if m <= 511 then 8 else 10
def lem_0c (m : Nat) : BitTrie := lem_09 (lem_0b m) m 0
theorem lem_0d (m y : Nat) (hm : 0 < m) (hm_ub : m <= 2047) :
    lem_02 (lem_0c m) ((y * y) % m) = true := by
  rcases lem_01 m y hm with ⟨r, hr, hsq⟩
  rw [<- hsq]
  unfold lem_0c
  have hlt : r < 2 ^ (lem_0b m) := by
    unfold lem_0b
    split_ifs <;> omega
  have h := lem_0a (lem_0b m) m 0 r hlt
  simpa using h
def lem_0e : Nat -> Nat -> (Nat -> Bool) -> Nat -> Bool
  | 0, m, p, x => p ((x * x) % m)
  | k + 1, m, p, x => lem_0e k m p (2 * x) || lem_0e k m p (2 * x + 1)
theorem lem_0f (k m : Nat) (p : Nat -> Bool) (x y : Nat) (hy : y < 2 ^ k)
    (hp : p (((x * 2 ^ k + y) * (x * 2 ^ k + y)) % m) = true) :
    lem_0e k m p x = true := by
  induction k generalizing x y with
  | zero =>
    have hy0 : y = 0 := by omega
    subst hy0
    simp only [Nat.pow_zero, Nat.mul_one, Nat.add_zero] at hp
    simpa [lem_0e, sNat_eq] using hp
  | succ k ih =>
    simp only [lem_0e, Bool.or_eq_true]
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ']; ring
    rcases (by omega : y < 2 ^ k \/ 2 ^ k <= y) with hlt | hge
    · left
      apply ih (2 * x) y hlt
      have hmul : (2 * x) * 2 ^ k = x * 2 ^ (k + 1) := by rw [Nat.pow_succ']; ring
      have heq : (2 * x) * 2 ^ k + y = x * 2 ^ (k + 1) + y := by omega
      rw [heq]; exact hp
    · right
      apply ih (2 * x + 1) (y - 2 ^ k) (by omega)
      have hmul : (2 * x + 1) * 2 ^ k = x * 2 ^ (k + 1) + 2 ^ k := by rw [Nat.pow_succ']; ring
      have heq : (2 * x + 1) * 2 ^ k + (y - 2 ^ k) = x * 2 ^ (k + 1) + y := by omega
      rw [heq]; exact hp
theorem lem_0g (k m : Nat) (p : Nat -> Bool) (y : Nat)
    (hm : 0 < m) (hub : m / 2 <= 2 ^ k)
    (hcert : (p (((2 ^ k) * (2 ^ k)) % m) || lem_0e k m p 0) = false) :
    p ((y * y) % m) = false := by
  rcases lem_01 m y hm with ⟨r, hr, hsq⟩
  rw [<- hsq]
  simp only [Bool.or_eq_false_iff] at hcert
  rcases (by omega : r = 2 ^ k \/ r < 2 ^ k) with rfl | hlt
  · exact hcert.1
  · cases hpr : p ((r * r) % m) with
    | false => rfl
    | true =>
      have hbad := lem_0f k m p 0 r hlt (by simpa using hpr)
      rw [hcert.2] at hbad
      contradiction
def lem_0h : Nat -> Nat -> Nat -> Nat
  | 0, e, m => (2 ^ e) % m
  | fuel + 1, e, m =>
    if e == 0 then 1 % m
    else
      sNat (lem_0h fuel (e / 2) m) (fun half =>
        sNat ((half * half) % m) (fun sq =>
          if e % 2 == 1 then (2 * sq) % m else sq))
theorem lem_0i (fuel e m : Nat) : lem_0h fuel e m = (2 ^ e) % m := by
  induction fuel generalizing e with
  | zero => rfl
  | succ fuel ih =>
    simp only [lem_0h, sNat_eq]
    split_ifs with h0 h1
    · have he : e = 0 := beq_iff_eq.mp h0
      subst he; rfl
    · have he1 : e % 2 = 1 := beq_iff_eq.mp h1
      rw [ih]
      have hdiv : e = (e / 2) + (e / 2) + 1 := by omega
      conv_rhs =>
          rw [hdiv, Nat.pow_add, Nat.pow_add, Nat.pow_one, Nat.mul_comm _ 2, Nat.mul_mod 2,
              Nat.mul_mod (2
          ^ (e / 2))]
      rw [Nat.mul_mod 2, Nat.mod_mod]
    · have he0 : e % 2 = 0 := by
        have : e % 2 ≠ 1 := fun h => h1 (beq_iff_eq.mpr h)
        omega
      rw [ih]
      have hdiv : e = (e / 2) + (e / 2) := by omega
      conv_rhs => rw [hdiv, Nat.pow_add, Nat.mul_mod]
theorem lem_0j (m p e : Nat) (_hp : 0 < p) (hper : 2 ^ p % m = 1) :
    2 ^ e % m = 2 ^ (e % p) % m := by
  have hdiv : e = p * (e / p) + e % p := (Nat.div_add_mod e p).symm
  conv_lhs => rw [hdiv, Nat.pow_add, Nat.pow_mul]
  have h1 : ∀ k, (2 ^ p) ^ k % m = 1 % m := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.pow_succ, Nat.mul_mod, ih, hper, Nat.mul_one, Nat.mod_mod]
  rw [Nat.mul_mod, h1 (e / p), <- Nat.mul_mod, Nat.one_mul]
theorem lem_0k {a m : Nat} (_hm : 0 < m) (ha : a < 2 * m) :
    a % m = if a < m then a else a - m := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
theorem lem_0l {L Y R m : Nat} (hm : 0 < m) (h : L = Y + R) :
    (L % m + m - R % m) % m = Y % m := by
  have hL : L % m = (Y % m + R % m) % m := by rw [h, Nat.add_mod]
  have hYlt : Y % m < m := Nat.mod_lt Y hm
  have hRlt : R % m < m := Nat.mod_lt R hm
  rw [lem_0k (a := Y % m + R % m) hm (by omega)] at hL
  generalize Y % m = ym at hL hYlt
  generalize R % m = rm at hL hRlt
  split_ifs at hL with hsum
  · have h1 : L % m + m - rm = ym + m := by omega
    rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt hYlt]
  · have h1 : L % m + m - rm = ym := by omega
    rw [h1, Nat.mod_eq_of_lt hYlt]
abbrev Row := Nat × Nat × Nat × Nat
def lem_0m (p : Nat) (s : Row) : Row :=
  let (l, n, a, r) := s
  (l % p, n % p, a % p, r)
def lem_0n (n a r : Nat) : Nat :=
  if r == 1 then 2 * n * (n + 1) + a + 1 else 2 * (n + 1) * (n + 1) + a + 1
def lem_0o (x : Nat) : Bool :=
  (x % 32 == 11) || (x % 32 == 15) || (x % 32 == 31)
def lem_0p (l x : Nat) : Bool :=
  (x % 96 == 15) || ((x % 96 == 11) && (l % 2 == 1))
def lem_0q (s : Row) : Bool :=
  let (l, n, a, r) := s
  sNat (lem_0n n a r) (fun x => lem_0o x && !lem_0p l x)
def lem_0r (p m : Nat) (s : Row) : Nat :=
  let (l, n, _, r) := s
  sNat ((l + 2 * n + r + 3) % p) (fun e => (lem_0h 12 e m + 1) % m)
def lem_0s (p m : Nat) (s : Row) : Nat :=
  let (_, n, a, r) := s
  sNat ((2 * n + 2) % p) (fun e1 =>
    sNat ((a + 1) % p) (fun e2 =>
      ((2 * r - 1) * lem_0h 12 e1 m + 5 * lem_0h 12 e2 m) % m))
def lem_0t (p m : Nat) (s : Row) : Nat :=
  sNat (lem_0r p m s) (fun r1 => sNat (lem_0s p m s) (fun s1 => (r1 + m - s1) % m))
theorem lem_0u (p m : Nat) (s : Row) :
    lem_0t p m (lem_0m p s) = lem_0t p m s := by
  rcases s with ⟨l, n, a, r⟩
  simp only [lem_0t, lem_0r, lem_0s, lem_0m, sNat_eq]
  have h1 : (l % p + 2 * (n % p) + r + 3) % p = (l + 2 * n + r + 3) % p := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  have h2 : (2 * (n % p) + 2) % p = (2 * n + 2) % p := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  have h3 : (a % p + 1) % p = (a + 1) % p := by
    simp only [Nat.add_mod, Nat.mod_mod]
  rw [h1, h2, h3]
theorem lem_0v (p m : Nat) (s : Row) (y : Nat)
    (hp : 0 < p) (hm : 0 < m) (hper : lem_0h 12 p m = 1)
    (hsq : 2 ^ (s.1 + 2 * s.2.1 + s.2.2.2 + 3) + 1 =
      y * y + ((2 * s.2.2.2 - 1) * 2 ^ (2 * s.2.1 + 2) + 5 * 2 ^ (s.2.2.1 + 1))) :
    lem_0t p m s = (y * y) % m := by
  rcases s with ⟨l, n, a, r⟩
  rw [lem_0i] at hper
  simp only [lem_0t, lem_0r, lem_0s, lem_0i, sNat_eq]
  rw [<- lem_0j m p (l + 2 * n + r + 3) hp hper,
      <- lem_0j m p (2 * n + 2) hp hper,
      <- lem_0j m p (a + 1) hp hper]
  have hlhs : (2 ^ (l + 2 * n + r + 3) % m + 1) % m = (2 ^ (l + 2 * n + r + 3) + 1) % m := by
    simp only [Nat.add_mod, Nat.mod_mod]
  have hrhs : ((2 * r - 1) * (2 ^ (2 * n + 2) % m) + 5 * (2 ^ (a + 1) % m)) % m =
      ((2 * r - 1) * 2 ^ (2 * n + 2) + 5 * 2 ^ (a + 1)) % m := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rw [hlhs, hrhs]
  exact lem_0l hm hsq
def lem_0w (p m : Nat) : Bool :=
  (0 < m) && (m <= 2047) && (lem_0h 12 p m == 1)
def lem_0x (p m : Nat) (qr : BitTrie) (xs : List Row) : List Row :=
  match qr with
  | .leaf false => []
  | .leaf true => xs
  | .node l r =>
    xs.filter (fun s => sNat (lem_0t p m s) (lem_02 (.node l r)))
theorem lem_0y (p m : Nat) (qr : BitTrie) (xs : List Row) :
    lem_0x p m qr xs = xs.filter (fun s => lem_02 qr (lem_0t p m s)) := by
  cases qr with
  | leaf b =>
    cases b <;> simp [lem_0x, lem_02]
  | node l r => simp [lem_0x, sNat_eq]
def lem_0z (p : Nat) (ms : List Nat) (xs : List Row) : List Row :=
  match ms with
  | [] => xs
  | m :: ms =>
    lem_0z p ms (lem_0x p m (lem_0c m) xs)
theorem lem_0A (p : Nat) (ms : List Nat) (xs : List Row) (s : Row) (y : Nat)
    (hp : 0 < p) (hms : ms.all (lem_0w p) = true)
    (hsq : 2 ^ (s.1 + 2 * s.2.1 + s.2.2.2 + 3) + 1 =
      y * y + ((2 * s.2.2.2 - 1) * 2 ^ (2 * s.2.1 + 2) + 5 * 2 ^ (s.2.2.1 + 1)))
    (hin : lem_0m p s ∈ xs) :
    lem_0m p s ∈ lem_0z p ms xs := by
  induction ms generalizing xs with
  | nil => exact hin
  | cons m ms ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hms
    rcases hms with ⟨hm_val, hms_rest⟩
    simp only [lem_0w, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm_val
    rcases hm_val with ⟨⟨hm, hm_ub⟩, hper⟩
    apply ih _ hms_rest
    rw [lem_0y, List.mem_filter]
    refine ⟨hin, ?_⟩
    rw [lem_0u, lem_0v p m s y hp hm hper hsq]
    exact lem_0d m y hm hm_ub
def box (ls ns as_ rs : List Nat) : List Row :=
  ls.flatMap (fun l => ns.flatMap (fun n => as_.flatMap (fun a => rs.map (fun r => (l, n, a, r)))))
def lem_0B (p k : Nat) (xs : List Row) : List Row :=
  xs.flatMap (fun (l, n, a, r) =>
    box ((List.range k).map (fun i => sNat (l + p * i) (fun x => x)))
        ((List.range k).map (fun i => sNat (n + p * i) (fun x => x)))
        ((List.range k).map (fun i => sNat (a + p * i) (fun x => x)))
        [r])
theorem lem_0C {ls ns as_ rs : List Nat} {l n a r : Nat}
    (hl : l ∈ ls) (hn : n ∈ ns) (ha : a ∈ as_) (hr : r ∈ rs) :
    (l, n, a, r) ∈ box ls ns as_ rs := by
  unfold box
  rw [List.mem_flatMap]; refine ⟨l, hl, ?_⟩
  rw [List.mem_flatMap]; refine ⟨n, hn, ?_⟩
  rw [List.mem_flatMap]; refine ⟨a, ha, ?_⟩
  rw [List.mem_map]; exact ⟨r, hr, rfl⟩
theorem lem_0D (x p k : Nat) (hp : 0 < p) (hk : 0 < k) :
    ∃ i < k, x % (p * k) = x % p + p * i := by
  refine ⟨(x % (p * k)) / p, ?_, ?_⟩
  · rw [Nat.div_lt_iff_lt_mul hp, Nat.mul_comm]
    exact Nat.mod_lt x (Nat.mul_pos hk hp)
  · have h1 : (x % (p * k)) % p = x % p := Nat.mod_mod_of_dvd x ⟨k, rfl⟩
    have h2 := (Nat.div_add_mod (x % (p * k)) p).symm
    omega
theorem lem_0E (p k : Nat) (xs : List Row) (s : Row)
    (hp : 0 < p) (hk : 0 < k) (hin : lem_0m p s ∈ xs) :
    lem_0m (p * k) s ∈ lem_0B p k xs := by
  rcases s with ⟨l, n, a, r⟩
  unfold lem_0B
  rw [List.mem_flatMap]
  refine ⟨lem_0m p (l, n, a, r), hin, ?_⟩
  simp only [lem_0m, sNat_eq]
  rcases lem_0D l p k hp hk with ⟨il, hil, hl⟩
  rcases lem_0D n p k hp hk with ⟨in_, hin_, hn⟩
  rcases lem_0D a p k hp hk with ⟨ia, hia, ha⟩
  rw [hl, hn, ha]
  apply lem_0C
  · rw [List.mem_map]; exact ⟨il, List.mem_range.mpr hil, rfl⟩
  · rw [List.mem_map]; exact ⟨in_, List.mem_range.mpr hin_, rfl⟩
  · rw [List.mem_map]; exact ⟨ia, List.mem_range.mpr hia, rfl⟩
  · simp
def lem_0F (s t : Row) : Bool :=
  (s.1 == t.1) && (s.2.1 == t.2.1) && (s.2.2.1 == t.2.2.1) && (s.2.2.2 == t.2.2.2)
def lem_0G (xs ys : List Row) : Bool :=
  xs.all (fun x => ys.any (lem_0F x))
theorem lem_0H {xs ys : List Row} (h : lem_0G xs ys = true) {s : Row} (hs : s ∈ xs) :
    s ∈ ys := by
  unfold lem_0G at h
  rw [List.all_eq_true] at h
  have h1 := h s hs
  rw [List.any_eq_true] at h1
  rcases h1 with ⟨t, ht, heq⟩
  rcases s with ⟨l1, n1, a1, r1⟩
  rcases t with ⟨l2, n2, a2, r2⟩
  simp only [lem_0F, Bool.and_eq_true, beq_iff_eq] at heq
  rcases heq with ⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  exact ht
def lem_0I_raw : List Row :=
  lem_0z 6 [3, 7, 9] (box (List.range 6) (List.range 6) [0, 2, 4] [1, 2])
def lem_0I : List Row := [
   (0, 0, 2, 1), (0, 1, 2, 1), (0, 3, 2, 1), (0, 4, 2, 1), (1, 0, 0, 2), (1, 0, 4, 1),
   (1, 1, 2, 2), (1, 1, 4, 1), (1, 1, 4, 2), (1, 2, 0, 2), (1, 2, 2, 2), (1, 2, 4, 1),
   (1, 2, 4, 2), (1, 3, 0, 2), (1, 3, 4, 1), (1, 4, 2, 2), (1, 4, 4, 1), (1, 4, 4, 2),
   (1, 5, 0, 2), (1, 5, 2, 2), (1, 5, 4, 1), (1, 5, 4, 2), (2, 1, 4, 1), (2, 4, 4, 1),
   (3, 0, 0, 2), (3, 0, 2, 1), (3, 0, 2, 2), (3, 0, 4, 1), (3, 0, 4, 2), (3, 1, 0, 1),
   (3, 1, 0, 2), (3, 1, 2, 1), (3, 1, 4, 1), (3, 2, 0, 1), (3, 2, 2, 2), (3, 2, 4, 2),
   (3, 3, 0, 2), (3, 3, 2, 1), (3, 3, 2, 2), (3, 3, 4, 1), (3, 3, 4, 2), (3, 4, 0, 1),
   (3, 4, 0, 2), (3, 4, 2, 1), (3, 4, 4, 1), (3, 5, 0, 1), (3, 5, 2, 2), (3, 5, 4, 2),
   (5, 0, 0, 1), (5, 0, 0, 2), (5, 0, 2, 1), (5, 0, 2, 2), (5, 1, 0, 1), (5, 1, 0, 2),
   (5, 1, 4, 1), (5, 1, 4, 2), (5, 2, 2, 1), (5, 2, 2, 2), (5, 3, 0, 1), (5, 3, 0, 2),
   (5, 3, 2, 1), (5, 3, 2, 2), (5, 4, 0, 1), (5, 4, 0, 2), (5, 4, 4, 1), (5, 4, 4, 2),
   (5, 5, 2, 1), (5, 5, 2, 2)]
def lem_0J_raw : List Row :=
  lem_0z 12 [5, 13] (lem_0B 6 2 lem_0I)
def lem_0J : List Row := [
   (0, 1, 2, 1), (0, 3, 2, 1), (0, 3, 8, 1), (0, 7, 2, 1), (0, 9, 2, 1), (0, 9, 8, 1),
   (1, 0, 4, 1), (1, 1, 2, 2), (1, 1, 4, 2), (1, 2, 4, 1), (1, 3, 0, 2), (1, 4, 10, 1),
   (1, 5, 0, 2), (1, 5, 2, 2), (1, 5, 4, 2), (1, 6, 4, 1), (1, 7, 2, 2), (1, 7, 4, 2),
   (1, 8, 4, 1), (1, 9, 0, 2), (1, 10, 10, 1), (1, 11, 0, 2), (1, 11, 2, 2), (1, 11, 4, 2),
   (2, 1, 4, 1), (2, 4, 4, 1), (2, 4, 10, 1), (2, 7, 4, 1), (2, 10, 4, 1), (2, 10, 10, 1),
   (3, 0, 0, 2), (3, 0, 2, 2), (3, 0, 4, 1), (3, 0, 8, 1), (3, 0, 8, 2), (3, 0, 10, 1),
   (3, 2, 0, 1), (3, 2, 2, 2), (3, 2, 4, 2), (3, 2, 10, 2), (3, 4, 0, 2), (3, 4, 6, 1),
   (3, 4, 6, 2), (3, 4, 8, 1), (3, 4, 10, 1), (3, 6, 0, 2), (3, 6, 2, 2), (3, 6, 4, 1),
   (3, 6, 8, 1), (3, 6, 8, 2), (3, 6, 10, 1), (3, 8, 0, 1), (3, 8, 2, 2), (3, 8, 4, 2),
   (3, 8, 10, 2), (3, 10, 0, 2), (3, 10, 6, 1), (3, 10, 6, 2), (3, 10, 8, 1), (3, 10, 10, 1),
   (5, 0, 2, 1), (5, 0, 6, 1), (5, 0, 8, 1), (5, 1, 0, 2), (5, 1, 6, 2), (5, 1, 10, 2),
   (5, 2, 2, 1), (5, 3, 6, 2), (5, 3, 8, 2), (5, 4, 0, 1), (5, 4, 10, 1), (5, 6, 2, 1),
   (5, 6, 6, 1), (5, 6, 8, 1), (5, 7, 0, 2), (5, 7, 6, 2), (5, 7, 10, 2), (5, 8, 2, 1),
   (5, 9, 6, 2), (5, 9, 8, 2), (5, 10, 0, 1), (5, 10, 10, 1), (6, 1, 8, 1), (6, 3, 8, 1),
   (6, 4, 8, 1), (6, 7, 8, 1), (6, 9, 8, 1), (6, 10, 8, 1), (7, 0, 4, 1), (7, 0, 6, 2),
   (7, 2, 0, 2), (7, 2, 4, 2), (7, 2, 6, 2), (7, 2, 10, 1), (7, 4, 10, 2), (7, 6, 4, 1),
   (7, 6, 6, 2), (7, 8, 0, 2), (7, 8, 4, 2), (7, 8, 6, 2), (7, 8, 10, 1), (7, 10, 10, 2),
   (9, 0, 8, 1), (9, 0, 10, 1), (9, 3, 0, 2), (9, 3, 8, 2), (9, 3, 10, 2), (9, 4, 0, 1),
   (9, 4, 8, 1), (9, 4, 10, 1), (9, 5, 8, 2), (9, 5, 10, 2), (9, 6, 8, 1), (9, 6, 10, 1),
   (9, 9, 0, 2), (9, 9, 8, 2), (9, 9, 10, 2), (9, 10, 0, 1), (9, 10, 8, 1), (9, 10, 10, 1),
   (9, 11, 8, 2), (9, 11, 10, 2), (11, 0, 2, 1), (11, 0, 2, 2), (11, 2, 2, 1), (11, 2, 2, 2),
   (11, 2, 8, 1), (11, 2, 8, 2), (11, 4, 0, 1), (11, 4, 0, 2), (11, 6, 2, 1), (11, 6, 2, 2),
   (11, 8, 2, 1), (11, 8, 2, 2), (11, 8, 8, 1), (11, 8, 8, 2), (11, 10, 0, 1), (11, 10, 0, 2)]
def lem_0K_raw : List Row :=
  lem_0z 24 [17, 241] (lem_0B 12 2 lem_0J)
def lem_0K : List Row := [
   (0, 1, 2, 1), (0, 3, 2, 1), (0, 7, 2, 1), (0, 9, 14, 1), (0, 9, 20, 1), (0, 13, 2, 1),
   (0, 15, 2, 1), (0, 19, 2, 1), (0, 21, 14, 1), (0, 21, 20, 1), (1, 1, 2, 2), (1, 1, 4, 2),
   (1, 2, 4, 1), (1, 5, 12, 2), (1, 6, 4, 1), (1, 7, 2, 2), (1, 7, 16, 2), (1, 10, 22, 1),
   (1, 11, 0, 2), (1, 11, 16, 2), (1, 13, 2, 2), (1, 13, 4, 2), (1, 14, 4, 1), (1, 17, 12, 2),
   (1, 18, 4, 1), (1, 19, 2, 2), (1, 19, 16, 2), (1, 22, 22, 1), (1, 23, 0, 2), (1, 23, 16, 2),
   (2, 1, 4, 1), (2, 4, 10, 1), (2, 4, 16, 1), (2, 7, 4, 1), (2, 10, 16, 1), (2, 10, 22, 1),
   (2, 13, 4, 1), (2, 16, 10, 1), (2, 16, 16, 1), (2, 19, 4, 1), (2, 22, 16, 1), (2, 22, 22, 1),
   (3, 0, 2, 2), (3, 0, 8, 1), (3, 0, 20, 2), (3, 2, 16, 2), (3, 4, 8, 1), (3, 4, 18, 1),
   (3, 4, 20, 1), (3, 6, 0, 2), (3, 6, 22, 1), (3, 8, 2, 2), (3, 8, 12, 1), (3, 10, 0, 2),
   (3, 10, 22, 1), (3, 12, 2, 2), (3, 12, 8, 1), (3, 12, 20, 2), (3, 14, 16, 2), (3, 16, 8, 1),
   (3, 16, 18, 1), (3, 16, 20, 1), (3, 18, 0, 2), (3, 18, 22, 1), (3, 20, 2, 2), (3, 20, 12, 1),
   (3, 22, 0, 2), (3, 22, 22, 1), (5, 0, 20, 1), (5, 2, 14, 1), (5, 3, 20, 2), (5, 4, 12, 1),
   (5, 6, 6, 1), (5, 6, 14, 1), (5, 6, 20, 1), (5, 7, 12, 2), (5, 9, 6, 2), (5, 9, 20, 2),
   (5, 10, 22, 1), (5, 12, 20, 1), (5, 14, 14, 1), (5, 15, 20, 2), (5, 16, 12, 1), (5, 18, 6, 1),
   (5, 18, 14, 1), (5, 18, 20, 1), (5, 19, 12, 2), (5, 21, 6, 2), (5, 21, 20, 2), (5, 22, 22, 1),
   (6, 1, 8, 1), (6, 3, 8, 1), (6, 4, 8, 1), (6, 9, 8, 1), (6, 10, 8, 1), (6, 13, 8, 1),
   (6, 15, 8, 1), (6, 16, 8, 1), (6, 21, 8, 1), (6, 22, 8, 1), (7, 2, 0, 2), (7, 2, 16, 2),
   (7, 2, 18, 2), (7, 6, 16, 1), (7, 8, 4, 2), (7, 8, 10, 1), (7, 14, 0, 2), (7, 14, 16, 2),
   (7, 14, 18, 2), (7, 18, 16, 1), (7, 20, 4, 2), (7, 20, 10, 1), (9, 0, 22, 1), (9, 3, 8, 2),
   (9, 3, 10, 2), (9, 4, 8, 1), (9, 4, 22, 1), (9, 5, 10, 2), (9, 6, 22, 1), (9, 9, 20, 2),
   (9, 10, 10, 1), (9, 10, 20, 1), (9, 10, 22, 1), (9, 11, 10, 2), (9, 12, 22, 1), (9, 15, 8, 2),
   (9, 15, 10, 2), (9, 16, 8, 1), (9, 16, 22, 1), (9, 17, 10, 2), (9, 18, 22, 1), (9, 21, 20, 2),
   (9, 22, 10, 1), (9, 22, 20, 1), (9, 22, 22, 1), (9, 23, 10, 2), (11, 0, 2, 2), (11, 2, 14, 1),
   (11, 2, 14, 2), (11, 4, 12, 1), (11, 6, 14, 1), (11, 12, 2, 2), (11, 14, 14, 1), (11, 14, 14, 2),
   (11, 16, 12, 1), (11, 18, 14, 1), (12, 1, 2, 1), (12, 7, 14, 1), (12, 9, 2, 1), (12, 9, 20, 1),
   (12, 13, 2, 1), (12, 19, 14, 1), (12, 21, 2, 1), (12, 21, 20, 1), (13, 2, 4, 1), (13, 5, 12, 2),
   (13, 5, 14, 2), (13, 6, 4, 1), (13, 7, 4, 2), (13, 10, 22, 1), (13, 11, 12, 2), (13, 14, 4, 1),
   (13, 17, 12, 2), (13, 17, 14, 2), (13, 18, 4, 1), (13, 19, 4, 2), (13, 22, 22, 1), (13, 23, 12,
       2),
   (14, 7, 16, 1), (14, 10, 16, 1), (14, 19, 16, 1), (14, 22, 16, 1), (15, 0, 4, 1), (15, 0, 10, 1),
   (15, 0, 12, 2), (15, 2, 0, 1), (15, 2, 10, 2), (15, 2, 16, 2), (15, 4, 10, 1), (15, 4, 18, 1),
   (15, 4, 18, 2), (15, 6, 0, 2), (15, 6, 2, 2), (15, 6, 8, 2), (15, 6, 10, 1), (15, 8, 4, 2),
   (15, 10, 8, 1), (15, 10, 18, 1), (15, 10, 18, 2), (15, 12, 4, 1), (15, 12, 10, 1), (15, 12, 12,
       2),
   (15, 14, 0, 1), (15, 14, 10, 2), (15, 14, 16, 2), (15, 16, 10, 1), (15, 16, 18, 1), (15, 16, 18,
       2),
   (15, 18, 0, 2), (15, 18, 2, 2), (15, 18, 8, 2), (15, 18, 10, 1), (15, 20, 4, 2), (15, 22, 8, 1),
   (15, 22, 18, 1), (15, 22, 18, 2), (17, 0, 6, 1), (17, 0, 8, 1), (17, 1, 10, 2), (17, 1, 12, 2),
   (17, 4, 22, 1), (17, 6, 2, 1), (17, 6, 6, 1), (17, 6, 14, 1), (17, 6, 18, 1), (17, 9, 18, 2),
   (17, 9, 20, 2), (17, 10, 22, 1), (17, 12, 6, 1), (17, 12, 8, 1), (17, 13, 10, 2), (17, 13, 12,
       2),
   (17, 16, 22, 1), (17, 18, 2, 1), (17, 18, 6, 1), (17, 18, 14, 1), (17, 18, 18, 1), (17, 21, 18,
       2),
   (17, 21, 20, 2), (17, 22, 22, 1), (18, 4, 8, 1), (18, 7, 20, 1), (18, 9, 20, 1), (18, 10, 20, 1),
   (18, 16, 8, 1), (18, 19, 20, 1), (18, 21, 20, 1), (18, 22, 20, 1), (19, 2, 16, 2), (19, 4, 10,
       2),
   (19, 8, 10, 1), (19, 8, 12, 2), (19, 8, 18, 2), (19, 14, 16, 2), (19, 16, 10, 2), (19, 20, 10,
       1),
   (19, 20, 12, 2), (19, 20, 18, 2), (21, 3, 20, 2), (21, 4, 20, 1), (21, 5, 22, 2), (21, 6, 22, 1),
   (21, 9, 12, 2), (21, 9, 20, 2), (21, 10, 12, 1), (21, 10, 20, 1), (21, 15, 20, 2), (21, 16, 20,
       1),
   (21, 17, 22, 2), (21, 18, 22, 1), (21, 21, 12, 2), (21, 21, 20, 2), (21, 22, 12, 1), (21, 22, 20,
       1),
   (23, 2, 2, 1), (23, 2, 2, 2), (23, 8, 20, 1), (23, 8, 20, 2), (23, 14, 2, 1), (23, 14, 2, 2),
   (23, 20, 20, 1), (23, 20, 20, 2)]
def lem_0L_raw : List Row :=
  lem_0z 48 [97, 257, 673] (lem_0B 24 2 lem_0K)
def lem_0L : List Row := [
   (0, 1, 2, 1), (0, 1, 26, 1), (0, 3, 2, 1), (0, 7, 2, 1), (0, 15, 26, 1), (0, 21, 44, 1),
   (0, 25, 2, 1), (0, 25, 26, 1), (0, 27, 2, 1), (0, 31, 2, 1), (0, 39, 26, 1), (0, 45, 44, 1),
   (1, 1, 2, 2), (1, 1, 4, 2), (1, 2, 4, 1), (1, 2, 28, 1), (1, 6, 28, 1), (1, 7, 2, 2),
   (1, 11, 24, 2), (1, 19, 40, 2), (1, 22, 46, 1), (1, 23, 0, 2), (1, 25, 2, 2), (1, 25, 4, 2),
   (1, 26, 4, 1), (1, 26, 28, 1), (1, 30, 28, 1), (1, 31, 2, 2), (1, 35, 24, 2), (1, 43, 40, 2),
   (1, 46, 46, 1), (1, 47, 0, 2), (2, 1, 4, 1), (2, 7, 28, 1), (2, 10, 22, 1), (2, 19, 28, 1),
   (2, 22, 46, 1), (2, 25, 4, 1), (2, 31, 28, 1), (2, 34, 22, 1), (2, 43, 28, 1), (2, 46, 46, 1),
   (3, 0, 2, 2), (3, 4, 32, 1), (3, 8, 36, 1), (3, 12, 8, 1), (3, 12, 32, 1), (3, 16, 42, 1),
   (3, 18, 24, 2), (3, 22, 0, 2), (3, 22, 46, 1), (3, 24, 2, 2), (3, 28, 32, 1), (3, 32, 36, 1),
   (3, 36, 8, 1), (3, 36, 32, 1), (3, 40, 42, 1), (3, 42, 24, 2), (3, 46, 0, 2), (3, 46, 46, 1),
   (5, 0, 20, 1), (5, 3, 44, 2), (5, 9, 6, 2), (5, 9, 20, 2), (5, 15, 44, 2), (5, 19, 12, 2),
   (5, 21, 44, 2), (5, 22, 46, 1), (5, 24, 20, 1), (5, 27, 44, 2), (5, 33, 6, 2), (5, 33, 20, 2),
   (5, 39, 44, 2), (5, 43, 12, 2), (5, 45, 44, 2), (5, 46, 46, 1), (6, 1, 8, 1), (6, 10, 32, 1),
   (6, 16, 32, 1), (6, 21, 32, 1), (6, 25, 8, 1), (6, 34, 32, 1), (6, 40, 32, 1), (6, 45, 32, 1),
   (7, 2, 0, 2), (7, 2, 16, 2), (7, 20, 28, 2), (7, 26, 0, 2), (7, 26, 16, 2), (7, 44, 28, 2),
   (9, 5, 34, 2), (9, 10, 10, 1), (9, 10, 22, 1), (9, 23, 10, 2), (9, 29, 34, 2), (9, 34, 10, 1),
   (9, 34, 22, 1), (9, 47, 10, 2), (11, 2, 14, 2), (11, 26, 14, 2), (12, 19, 38, 1), (12, 43, 38,
       1),
   (13, 10, 22, 1), (13, 19, 4, 2), (13, 22, 46, 1), (13, 34, 22, 1), (13, 43, 4, 2), (13, 46, 46,
       1),
   (14, 7, 16, 1), (14, 7, 40, 1), (14, 22, 40, 1), (14, 31, 16, 1), (14, 31, 40, 1), (14, 46, 40,
       1),
   (15, 6, 0, 2), (15, 6, 32, 2), (15, 10, 18, 2), (15, 12, 28, 1), (15, 16, 18, 1), (15, 30, 0, 2),
   (15, 30, 32, 2), (15, 34, 18, 2), (15, 36, 28, 1), (15, 40, 18, 1), (17, 6, 6, 1), (17, 6, 14,
       1),
   (17, 10, 46, 1), (17, 12, 6, 1), (17, 18, 14, 1), (17, 22, 46, 1), (17, 30, 6, 1), (17, 30, 14,
       1),
   (17, 34, 46, 1), (17, 36, 6, 1), (17, 42, 14, 1), (17, 46, 46, 1), (18, 7, 44, 1), (18, 10, 20,
       1),
   (18, 31, 44, 1), (18, 34, 20, 1), (19, 8, 18, 2), (19, 32, 18, 2), (21, 4, 20, 1), (21, 5, 22,
       2),
   (21, 6, 46, 1), (21, 10, 20, 1), (21, 16, 20, 1), (21, 21, 44, 2), (21, 22, 44, 1), (21, 28, 20,
       1),
   (21, 29, 22, 2), (21, 30, 46, 1), (21, 34, 20, 1), (21, 40, 20, 1), (21, 45, 44, 2), (21, 46, 44,
       1),
   (23, 14, 26, 2), (23, 38, 26, 2), (24, 7, 2, 1), (24, 7, 26, 1), (24, 9, 38, 1), (24, 13, 26, 1),
   (24, 19, 2, 1), (24, 21, 44, 1), (24, 31, 2, 1), (24, 31, 26, 1), (24, 33, 38, 1), (24, 37, 26,
       1),
   (24, 43, 2, 1), (24, 45, 44, 1), (25, 6, 28, 1), (25, 19, 26, 2), (25, 19, 40, 2), (25, 23, 24,
       2),
   (25, 30, 28, 1), (25, 43, 26, 2), (25, 43, 40, 2), (25, 47, 24, 2), (26, 4, 16, 1), (26, 10, 40,
       1),
   (26, 28, 16, 1), (26, 34, 40, 1), (27, 0, 8, 1), (27, 0, 26, 2), (27, 0, 32, 1), (27, 4, 8, 1),
   (27, 4, 32, 1), (27, 6, 24, 2), (27, 8, 2, 2), (27, 8, 26, 2), (27, 12, 26, 2), (27, 16, 44, 1),
   (27, 20, 12, 1), (27, 24, 8, 1), (27, 24, 26, 2), (27, 24, 32, 1), (27, 28, 8, 1), (27, 28, 32,
       1),
   (27, 30, 24, 2), (27, 32, 2, 2), (27, 32, 26, 2), (27, 36, 26, 2), (27, 40, 44, 1), (27, 44, 12,
       1),
   (29, 18, 6, 1), (29, 18, 14, 1), (29, 18, 38, 1), (29, 18, 44, 1), (29, 21, 30, 2), (29, 42, 6,
       1),
   (29, 42, 14, 1), (29, 42, 38, 1), (29, 42, 44, 1), (29, 45, 30, 2), (30, 1, 32, 1), (30, 4, 8,
       1),
   (30, 4, 32, 1), (30, 10, 8, 1), (30, 10, 32, 1), (30, 13, 8, 1), (30, 15, 8, 1), (30, 15, 32, 1),
   (30, 21, 8, 1), (30, 22, 32, 1), (30, 25, 32, 1), (30, 28, 8, 1), (30, 28, 32, 1), (30, 34, 8,
       1),
   (30, 34, 32, 1), (30, 37, 8, 1), (30, 39, 8, 1), (30, 39, 32, 1), (30, 45, 8, 1), (30, 46, 32,
       1),
   (31, 8, 28, 2), (31, 14, 0, 2), (31, 14, 16, 2), (31, 32, 28, 2), (31, 38, 0, 2), (31, 38, 16,
       2),
   (33, 3, 8, 2), (33, 4, 8, 1), (33, 10, 44, 1), (33, 10, 46, 1), (33, 11, 34, 2), (33, 17, 10, 2),
   (33, 18, 46, 1), (33, 22, 22, 1), (33, 22, 46, 1), (33, 23, 34, 2), (33, 27, 8, 2), (33, 28, 8,
       1),
   (33, 34, 44, 1), (33, 34, 46, 1), (33, 35, 34, 2), (33, 41, 10, 2), (33, 42, 46, 1), (33, 46, 22,
       1),
   (33, 46, 46, 1), (33, 47, 34, 2), (35, 4, 36, 1), (35, 14, 14, 1), (35, 16, 36, 1), (35, 18, 38,
       1),
   (35, 28, 36, 1), (35, 38, 14, 1), (35, 40, 36, 1), (35, 42, 38, 1), (36, 1, 26, 1), (36, 7, 14,
       1),
   (36, 7, 38, 1), (36, 9, 26, 1), (36, 25, 26, 1), (36, 31, 14, 1), (36, 31, 38, 1), (36, 33, 26,
       1),
   (37, 5, 12, 2), (37, 6, 28, 1), (37, 10, 22, 1), (37, 14, 28, 1), (37, 19, 28, 2), (37, 22, 22,
       1),
   (37, 29, 12, 2), (37, 30, 28, 1), (37, 34, 22, 1), (37, 38, 28, 1), (37, 43, 28, 2), (37, 46, 22,
       1),
   (38, 22, 40, 1), (38, 46, 40, 1), (39, 0, 10, 1), (39, 0, 36, 2), (39, 2, 16, 2), (39, 6, 34, 1),
   (39, 16, 42, 1), (39, 16, 42, 2), (39, 18, 0, 2), (39, 18, 32, 2), (39, 22, 42, 2), (39, 24, 10,
       1),
   (39, 24, 36, 2), (39, 26, 16, 2), (39, 30, 34, 1), (39, 40, 42, 1), (39, 40, 42, 2), (39, 42, 0,
       2),
   (39, 42, 32, 2), (39, 46, 42, 2), (41, 6, 2, 1), (41, 10, 22, 1), (41, 21, 42, 2), (41, 21, 44,
       2),
   (41, 30, 2, 1), (41, 34, 22, 1), (41, 45, 42, 2), (41, 45, 44, 2), (42, 4, 32, 1), (42, 7, 44,
       1),
   (42, 19, 44, 1), (42, 21, 44, 1), (42, 22, 20, 1), (42, 22, 44, 1), (42, 28, 32, 1), (42, 31, 44,
       1),
   (42, 43, 44, 1), (42, 45, 44, 1), (42, 46, 20, 1), (42, 46, 44, 1), (43, 2, 40, 2), (43, 8, 42,
       2),
   (43, 20, 42, 2), (43, 26, 40, 2), (43, 32, 42, 2), (43, 44, 42, 2), (45, 5, 46, 2), (45, 6, 46,
       1),
   (45, 9, 44, 2), (45, 10, 44, 1), (45, 17, 46, 2), (45, 18, 46, 1), (45, 21, 44, 2), (45, 22, 44,
       1),
   (45, 29, 46, 2), (45, 30, 46, 1), (45, 33, 44, 2), (45, 34, 44, 1), (45, 41, 46, 2), (45, 42, 46,
       1),
   (45, 45, 44, 2), (45, 46, 44, 1), (47, 2, 2, 1), (47, 2, 2, 2), (47, 20, 44, 1), (47, 20, 44, 2),
   (47, 26, 2, 1), (47, 26, 2, 2), (47, 44, 44, 1), (47, 44, 44, 2)]
def lem_0M : List Row :=
  lem_0z 96 [193] ((lem_0B 48 2 lem_0L).filter lem_0q)
theorem lem_0I_sub : lem_0G lem_0I_raw lem_0I = true := by decide +kernel
theorem lem_0J_sub : lem_0G lem_0J_raw lem_0J = true := by decide +kernel
theorem lem_0K_sub : lem_0G lem_0K_raw lem_0K = true := by decide +kernel
theorem lem_0L_sub : lem_0G lem_0L_raw lem_0L = true := by decide +kernel
def lem_0N : List Row :=
  [(0, 1, 26, 1), (0, 49, 26, 1), (0, 25, 74, 1), (0, 73, 74, 1), (84, 1, 26, 1), (84, 1, 74, 1),
   (84, 49, 26, 1), (84, 49, 74, 1), (36, 25, 26, 1), (36, 25, 74, 1), (36, 73, 26, 1), (36, 73, 74,
       1),
   (84, 25, 26, 1), (84, 73, 26, 1), (72, 19, 50, 1), (72, 67, 50, 1), (36, 7, 62, 1), (36, 55, 62,
       1),
   (84, 7, 14, 1), (84, 55, 14, 1), (36, 31, 14, 1), (36, 31, 62, 1), (36, 79, 14, 1), (36, 79, 62,
       1),
   (84, 31, 14, 1), (84, 79, 14, 1), (12, 19, 38, 1), (12, 19, 86, 1), (12, 67, 38, 1), (12, 67, 86,
       1),
   (60, 19, 86, 1), (60, 67, 86, 1), (60, 43, 86, 1), (60, 91, 86, 1), (48, 3, 50, 1), (48, 51, 50,
       1),
   (48, 27, 2, 1), (48, 75, 2, 1), (48, 15, 74, 1), (48, 63, 74, 1), (72, 9, 86, 1), (72, 57, 86,
       1),
   (36, 9, 74, 1), (36, 57, 74, 1), (84, 33, 26, 1), (84, 81, 26, 1), (31, 8, 76, 2), (31, 56, 76,
       2),
   (79, 8, 76, 2), (79, 56, 76, 2), (31, 32, 28, 2), (31, 32, 76, 2), (31, 80, 28, 2), (31, 80, 76,
       2),
   (55, 20, 76, 2), (55, 68, 76, 2), (7, 44, 28, 2), (7, 44, 76, 2), (7, 92, 28, 2), (7, 92, 76, 2),
   (55, 44, 28, 2), (55, 92, 28, 2), (37, 46, 70, 1), (37, 94, 70, 1), (75, 6, 72, 2), (75, 54, 72,
       2),
   (27, 30, 72, 2), (27, 78, 72, 2), (3, 42, 24, 2), (3, 90, 24, 2), (33, 10, 46, 1), (33, 58, 46,
       1),
   (33, 34, 94, 1), (33, 82, 94, 1), (81, 34, 94, 1), (81, 82, 94, 1), (33, 22, 22, 1), (33, 70, 22,
       1),
   (21, 5, 22, 2), (21, 5, 70, 2), (21, 53, 22, 2), (21, 53, 70, 2), (69, 5, 70, 2), (69, 53, 70,
       2),
   (17, 12, 6, 1), (17, 12, 54, 1), (17, 60, 6, 1), (17, 60, 54, 1), (65, 12, 54, 1), (65, 60, 54,
       1),
   (17, 36, 54, 1), (17, 84, 54, 1), (29, 18, 62, 1), (29, 66, 62, 1), (29, 42, 14, 1), (29, 90, 14,
       1),
   (77, 42, 14, 1), (77, 90, 14, 1), (17, 42, 14, 1), (17, 90, 14, 1), (65, 42, 14, 1), (65, 90, 14,
       1),
   (47, 2, 50, 1), (47, 50, 50, 1), (47, 44, 44, 2), (47, 92, 44, 2), (5, 9, 54, 2), (5, 57, 54, 2),
   (53, 9, 54, 2), (53, 57, 54, 2), (5, 33, 54, 2), (5, 81, 54, 2), (53, 33, 54, 2), (53, 81, 54,
       2),
   (17, 10, 46, 1), (17, 58, 46, 1), (17, 34, 94, 1), (17, 82, 94, 1), (65, 34, 94, 1), (65, 82, 94,
       1)]
def lem_0O : List Row :=
  lem_0z 288 [19, 27, 37, 73, 109, 433, 577, 1153] (lem_0B 96 3 lem_0N)
def lem_0P : List Row :=
  [(276, 1, 26, 1), (276, 1, 170, 1), (276, 145, 26, 1), (276, 145, 170, 1),
   (132, 217, 170, 1), (132, 73, 170, 1), (12, 115, 230, 1), (12, 115, 86, 1),
   (12, 259, 230, 1), (12, 259, 86, 1), (144, 3, 146, 1), (144, 147, 146, 1),
   (144, 219, 2, 1), (144, 75, 2, 1), (257, 204, 150, 1), (257, 60, 150, 1),
   (29, 114, 254, 1), (29, 258, 254, 1), (173, 42, 110, 1), (173, 186, 110, 1),
   (143, 140, 140, 2), (143, 284, 140, 2), (53, 105, 54, 2), (53, 249, 54, 2),
   (53, 33, 54, 2), (53, 177, 54, 2)]
def lem_0Q : List Row :=
  lem_0z 1440 [11, 25, 31, 41, 61, 151, 181, 331, 631, 1321] (lem_0B 288 5 lem_0P)
def lem_0R : List Row :=
  [(300, 691, 1382, 1), (1164, 403, 806, 1), (300, 691, 662, 1), (1164, 403, 86, 1),
   (300, 1411, 1382, 1), (1164, 1123, 806, 1), (300, 1411, 662, 1), (1164, 1123, 86, 1),
   (720, 3, 722, 1), (720, 723, 722, 1), (720, 1083, 2, 1), (720, 363, 2, 1),
   (719, 716, 716, 2), (719, 1436, 716, 2), (341, 1257, 342, 2), (341, 537, 342, 2),
   (341, 897, 342, 2), (341, 177, 342, 2)]
def lem_0S (d : Nat) : Bool := d == 5098 || d == 1241 || d == 3447
def lem_0T (d : Nat) : Bool := d == 20198 || d == 2609 || d == 11162
def lem_0U (d : Nat) : Bool := d == 24525 || d == 19976
def lem_0V (d : Nat) : Bool := d == 321
def lem_0W (s : Row) : Bool :=
  !lem_0S (lem_0t 1440 6337 s) &&
  !lem_0T (lem_0t 1440 23041 s) &&
  !lem_0U (lem_0t 1440 37441 s) &&
  !lem_0V (lem_0t 1440 65537 s)
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_0X :
    ([3, 7, 9].all (lem_0w 6) &&
     [5, 13].all (lem_0w 12) &&
     [17, 241].all (lem_0w 24) &&
     [97, 257, 673].all (lem_0w 48) &&
     [193].all (lem_0w 96) &&
     [19, 27, 37, 73, 109, 433, 577, 1153].all (lem_0w 288) &&
     [11, 25, 31, 41, 61, 151, 181, 331, 631, 1321].all (lem_0w 1440)) = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_0Y : lem_0G lem_0M lem_0N = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_0Z : lem_0G lem_0O lem_0P = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_10 : lem_0G lem_0Q lem_0R = true := by decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_11 : (lem_0S (((2 ^ 12) * (2 ^ 12)) % 6337) || lem_0e 12 6337 lem_0S 0) = false := by
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_12 : (lem_0T (((2 ^ 14) * (2 ^ 14)) % 23041) || lem_0e 14 23041 lem_0T 0) = false := by
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_13 : (lem_0U (((2 ^ 15) * (2 ^ 15)) % 37441) || lem_0e 15 37441 lem_0U 0) = false := by
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_14 : (lem_0V (((2 ^ 15) * (2 ^ 15)) % 65537) || lem_0e 15 65537 lem_0V 0) = false := by
  decide +kernel
set_option maxHeartbeats 8000000 in
-- Needed for large symbolic execution or decision procedure
theorem lem_15 : lem_0R.filter lem_0W = [] := by decide +kernel
theorem lem_16 (p n a r : Nat) :
    lem_0n (n % p) (a % p) r % p = lem_0n n a r % p := by
  unfold lem_0n
  split_ifs <;> simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
theorem lem_17 (s : Row) : lem_0q (lem_0m 96 s) = lem_0q s := by
  rcases s with ⟨l, n, a, r⟩
  simp only [lem_0q, lem_0m, lem_0o, lem_0p, sNat_eq]
  have h32 : lem_0n (n % 96) (a % 96) r % 32 = lem_0n n a r % 32 := by
    rw [<- Nat.mod_mod_of_dvd (lem_0n (n % 96) (a % 96) r) (⟨3, rfl⟩ : 32 ∣ 96),
        lem_16 96 n a r,
        Nat.mod_mod_of_dvd (lem_0n n a r) (⟨3, rfl⟩ : 32 ∣ 96)]
  have h96 : lem_0n (n % 96) (a % 96) r % 96 = lem_0n n a r % 96 := lem_16 96 n a r
  have hl2 : (l % 96) % 2 = l % 2 := Nat.mod_mod_of_dvd l ⟨48, rfl⟩
  rw [h32, h96, hl2]
theorem lem_18 (l n a r y : Nat)
    (ha_even : a % 2 = 0) (hr : r = 1 \/ r = 2)
    (hok : lem_0q (l, n, a, r) = true) :
    2 ^ (l + 2 * n + r + 3) + 1 ≠
      y * y + ((2 * r - 1) * 2 ^ (2 * n + 2) + 5 * 2 ^ (a + 1)) := by
  intro hsq
  have hmv := lem_0X
  simp only [Bool.and_eq_true] at hmv
  rcases hmv with ⟨⟨⟨⟨⟨⟨hm6, hm12⟩, hm24⟩, hm48⟩, hm96⟩, hm288⟩, hm1440⟩
  have h_in6 : lem_0m 6 (l, n, a, r) ∈ lem_0I := by
    apply lem_0H lem_0I_sub
    apply lem_0A 6 [3, 7, 9] _ (l, n, a, r) y (by decide) hm6 hsq
    apply lem_0C
    · exact List.mem_range.mpr (Nat.mod_lt l (by decide))
    · exact List.mem_range.mpr (Nat.mod_lt n (by decide))
    · have ha6 : a % 6 < 6 := Nat.mod_lt a (by decide)
      have ha2 : (a % 6) % 2 = a % 2 := Nat.mod_mod_of_dvd a ⟨3, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      omega
    · simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hr
  have h_in12 : lem_0m 12 (l, n, a, r) ∈ lem_0J :=
    lem_0H lem_0J_sub
      (lem_0A 12 [5, 13] _ (l, n, a, r) y (by decide +kernel) hm12 hsq
        (lem_0E 6 2 lem_0I (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in6))
  have h_in24 : lem_0m 24 (l, n, a, r) ∈ lem_0K :=
    lem_0H lem_0K_sub
      (lem_0A 24 [17, 241] _ (l, n, a, r) y (by decide +kernel) hm24 hsq
        (lem_0E 12 2 lem_0J (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in12))
  have h_in48 : lem_0m 48 (l, n, a, r) ∈ lem_0L :=
    lem_0H lem_0L_sub
      (lem_0A 48 [97, 257, 673] _ (l, n, a, r) y (by decide +kernel) hm48 hsq
        (lem_0E 24 2 lem_0K (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in24))
  have h_in96 : lem_0m 96 (l, n, a, r) ∈ lem_0N := by
    apply lem_0H lem_0Y
    apply lem_0A 96 [193] _ (l, n, a, r) y (by decide +kernel) hm96 hsq
    rw [List.mem_filter]
    refine ⟨lem_0E 48 2 lem_0L (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in48, ?_⟩
    rw [lem_17]; exact hok
  have h_in288 : lem_0m 288 (l, n, a, r) ∈ lem_0P :=
    lem_0H lem_0Z
      (lem_0A 288 _ _ (l, n, a, r) y (by decide +kernel) hm288 hsq
        (lem_0E 96 3 lem_0N (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in96))
  have h_in1440 : lem_0m 1440 (l, n, a, r) ∈ lem_0R :=
    lem_0H lem_10
      (lem_0A 1440 _ _ (l, n, a, r) y (by decide +kernel) hm1440 hsq
        (lem_0E 288 5 lem_0P (l, n, a, r) (by decide +kernel) (by decide +kernel) h_in288))
  have h_final : lem_0m 1440 (l, n, a, r) ∈ lem_0R.filter lem_0W := by
    rw [List.mem_filter]
    refine ⟨h_in1440, ?_⟩
    unfold lem_0W
    rw [lem_0u 1440 6337, lem_0v 1440 6337 (l, n, a,
        r) y (by decide +kernel) (by decide +kernel) (by
        decide +kernel) hsq,
        lem_0u 1440 23041, lem_0v 1440 23041 (l, n, a,
            r) y (by decide +kernel) (by decide +kernel) (by
            decide +kernel) hsq,
        lem_0u 1440 37441, lem_0v 1440 37441 (l, n, a,
            r) y (by decide +kernel) (by decide +kernel) (by
            decide +kernel) hsq,
        lem_0u 1440 65537, lem_0v 1440 65537 (l, n, a,
            r) y (by decide +kernel) (by decide +kernel) (by
            decide +kernel) hsq,
        lem_0g 12 6337 lem_0S y (by decide +kernel) (by decide +kernel) lem_11,
        lem_0g 14 23041 lem_0T y (by decide +kernel) (by decide +kernel) lem_12,
        lem_0g 15 37441 lem_0U y (by decide +kernel) (by decide +kernel) lem_13,
        lem_0g 15 65537 lem_0V y (by decide +kernel) (by decide +kernel) lem_14]
    rfl
  rw [lem_15] at h_final
  nomatch h_final
def lem_19 (x : Nat) : Prop :=
  x % 128 = 47 \/ x % 128 = 63 \/ x % 128 = 107 \/ x % 128 = 127
structure Weak (l x : Nat) : Prop where
  weak_length : 18 <= l
  weak_pos : 0 < x
  weak_bound : x < 2 ^ l
  weak_low : lem_19 x
  weak_exc : lem_0p l x = false
structure Inv (l x : Nat) : Prop where
  inv_weak : Weak l x
  inv_half : ∀ q, x + 1 ≠ 2 * q * q
  inv_disc : ∀ q, 2 * x + 3 ≠ q * q
def lem_1a (l n r : Nat) : Nat := l + 2 * n + r + 2
def lem_1b (l n a r : Nat) : Nat :=
  2 ^ (lem_1a l n r) - (2 * r - 1) * 2 ^ (2 * n + 1) - 5 * 2 ^ a - 1
theorem lem_1c {q : Nat} (h : (q * q) % 2 = 0) : q % 2 = 0 := by
  have hdiv : q = 2 * (q / 2) + q % 2 := (Nat.div_add_mod q 2).symm
  rcases (by omega : q % 2 = 0 \/ q % 2 = 1) with h0 | h1
  · exact h0
  · exfalso
    have hsq : q * q = 2 * (2 * (q / 2) * (q / 2) + 2 * (q / 2)) + 1 := by
      conv_lhs => rw [hdiv, h1]
      ring
    omega
theorem lem_1d (k u : Nat) (hu : u % 2 = 1) :
    ∀ q, 4 ^ k * u ≠ 2 * q * q := by
  induction k with
  | zero =>
    intro q h
    simp only [Nat.pow_zero, Nat.one_mul, Nat.mul_assoc] at h
    omega
  | succ k ih =>
    intro q h
    have h5 : 4 ^ (k + 1) * u = 4 * (4 ^ k * u) := by rw [Nat.pow_succ]; ring
    have hq_even : (q * q) % 2 = 0 := by
      rw [Nat.mul_assoc 2 q q] at h
      omega
    have hq2 : q % 2 = 0 := lem_1c hq_even
    have hq_eq : q = 2 * (q / 2) := by omega
    apply ih (q / 2)
    have h4 : 2 * q * q = 4 * (2 * (q / 2) * (q / 2)) := by
      conv_lhs => rw [hq_eq]
      ring
    omega
theorem lem_1e {x : Nat} (h : lem_19 x) : x % 4 = 3 := by
  unfold lem_19 at h
  omega
theorem lem_1f (l x : Nat) (hinv : Inv l x) :
    ∃ n a r, 1 <= n /\ a <= 2 * n - 2 /\ (r = 1 \/ r = 2) /\ x = lem_0n n a r := by
  rcases hinv with ⟨⟨_, _, _, hlow, _⟩, hhalf, hdisc⟩
  have hx4 : x % 4 = 3 := lem_1e hlow
  set y := x / 2 + 1
  have hy : 1 <= y /\ x + 1 = 2 * y := by omega
  set q := Nat.sqrt y
  have hq_le : q * q <= y := Nat.sqrt_le y
  have hq_lt : y < (q + 1) * (q + 1) := Nat.lt_succ_sqrt y
  have hq_ne : q * q ≠ y := by
    intro heq
    apply hhalf q
    rw [Nat.mul_assoc, heq]
    omega
  have hq_strict : q * q < y := by omega
  have hq_pos : 1 <= q := by
    by_contra h
    have h0 : q = 0 := by omega
    rw [h0] at hq_strict hq_lt
    omega
  have hadj : y ≠ q * (q + 1) := by
    intro heq
    apply hdisc (2 * q + 1)
    calc 2 * x + 3 = 4 * y + 1 := by omega
      _ = 4 * (q * (q + 1)) + 1 := by rw [heq]
      _ = (2 * q + 1) * (2 * q + 1) := by ring
  rcases (by omega : y < q * (q + 1) \/ q * (q + 1) < y) with hlt | hgt
  · have hq2 : 2 <= q := by nlinarith
    have hqq : 2 * q * q = 2 * (q * q) := Nat.mul_assoc 2 q q
    refine ⟨q - 1, x - 2 * (q * q) - 1, 2, by omega, ?_, Or.inr rfl, ?_⟩
    · have h1 : q * (q + 1) = q * q + q := by ring
      omega
    · unfold lem_0n
      have hne : (2 == 1) = false := rfl
      have hq_sub : q - 1 + 1 = q := by omega
      rw [hne]
      simp only [Bool.false_eq_true, ↓reduceIte, hq_sub, hqq]
      omega
  · have hqq1 : 2 * q * (q + 1) = 2 * (q * (q + 1)) := Nat.mul_assoc 2 q (q + 1)
    refine ⟨q, x - 2 * (q * (q + 1)) - 1, 1, hq_pos, ?_, Or.inl rfl, ?_⟩
    · have h1 : (q + 1) * (q + 1) = q * (q + 1) + q + 1 := by ring
      omega
    · unfold lem_0n
      have heq1 : (1 == 1) = true := rfl
      rw [heq1]
      simp only [↓reduceIte, hqq1]
      omega
theorem lem_1g (n a r : Nat) (hn : 1 <= n) (ha : a <= 2 * n - 2)
    (hr : r = 1 \/ r = 2) (hlow : lem_19 (lem_0n n a r)) :
    3 <= n /\ 2 <= a /\ a % 2 = 0 /\ (r = 1 -> a % 4 = 2) /\ (r = 2 -> 4 <= a) := by
  have hx4 : lem_0n n a r % 4 = 3 := lem_1e hlow
  have ha_even : a % 2 = 0 := by
    rcases hr with rfl | rfl
    · unfold lem_0n at hx4
      have heq1 : (1 == 1) = true := rfl
      rw [heq1, ite_eq_left rfl, Nat.mul_assoc 2 n (n + 1)] at hx4
      omega
    · unfold lem_0n at hx4
      have hne : (2 == 1) = false := rfl
      rw [hne, ite_eq_right Bool.noConfusion, Nat.mul_assoc 2 (n + 1) (n + 1)] at hx4
      omega
  have hr1 : r = 1 -> a % 4 = 2 := by
    intro h1; subst h1
    unfold lem_0n at hx4
    have heq1 : (1 == 1) = true := rfl
    rw [heq1, ite_eq_left rfl] at hx4
    have hn_div : 2 * n * (n + 1) =
        4 * (2 * (n / 2) * (n / 2) + 2 * (n / 2) * (n % 2) + n / 2) + 2 * (n % 2) * (n % 2 + 1) :=
            by
      have hdiv : n = 2 * (n / 2) + n % 2 := (Nat.div_add_mod n 2).symm
      conv_lhs => rw [hdiv]
      ring
    have hrem : 2 * (n % 2) * (n % 2 + 1) % 4 = 0 := by
      rcases (by omega : n % 2 = 0 \/ n % 2 = 1) with h0 | h1
      · rw [h0]
      · rw [h1]
    rw [hn_div] at hx4
    omega
  have hr2 : r = 2 -> 4 <= a := by
    intro h2; subst h2
    by_contra hlt4
    have ha02 : a = 0 \/ a = 2 := by omega
    unfold lem_19 lem_0n at hlow
    have hne : (2 == 1) = false := rfl
    rw [hne, ite_eq_right Bool.noConfusion] at hlow
    set m := n + 1
    have hm16 : 2 * m * m + a + 1 =
        64 * (8 * (m / 16) * (m / 16) + (m / 16) * (m % 16)) + (2 * (m % 16) * (m % 16) + a +
            1) := by
      have hdiv : m = 16 * (m / 16) + m % 16 := (Nat.div_add_mod m 16).symm
      conv_lhs => rw [hdiv]
      ring
    have hlow64 : (2 * m * m + a + 1) % 64 = 47 \/ (2 * m * m + a + 1) % 64 = 63 \/
        (2 * m * m + a + 1) % 64 = 43 := by omega
    rw [hm16] at hlow64
    have hmod64 : (64 * (8 * (m / 16) * (m / 16) + (m / 16) * (m % 16)) + (2 * (m % 16) * (m % 16) +
        a + 1)) % 64 =
        (2 * (m % 16) * (m % 16) + a + 1) % 64 := Nat.mul_add_mod _ _ _
    rw [hmod64] at hlow64
    have hlt16 : m % 16 < 16 := Nat.mod_lt m (by decide)
    generalize m % 16 = k at hlt16 hlow64
    rcases ha02 with rfl | rfl <;> (revert k; decide +kernel)
  have ha2 : 2 <= a := by
    rcases hr with rfl | rfl
    · have := hr1 rfl; omega
    · have := hr2 rfl; omega
  have hbig : 47 <= lem_0n n a r := by
    unfold lem_19 at hlow; omega
  have ha' : a + 2 <= 2 * n := by omega
  have hn3 : 3 <= n := by
    rcases hr with rfl | rfl
    · unfold lem_0n at hbig
      have heq1 : (1 == 1) = true := rfl
      rw [heq1, ite_eq_left rfl] at hbig
      nlinarith
    · unfold lem_0n at hbig
      have hne : (2 == 1) = false := rfl
      rw [hne, ite_eq_right Bool.noConfusion] at hbig
      nlinarith
  exact ⟨hn3, ha2, ha_even, hr1, hr2⟩
def lem_1h (l n a r : Nat) : Nat :=
  2 ^ (2 * n + 1 - a) * (2 ^ (l + r + 1) - (2 * r - 1)) - 5
theorem lem_1i (l n a r : Nat) (hl : 18 <= l) (ha2 : 2 <= a) (ha : a <= 2 * n - 2)
    (ha_even : a % 2 = 0) (hr : r = 1 \/ r = 2) :
    18 <= lem_1a l n r /\
    (2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1 < 2 ^ (lem_1a l n r) /\
    0 < lem_1b l n a r /\
    lem_1b l n a r < 2 ^ (lem_1a l n r) /\
    (∀ q, lem_1b l n a r + 1 ≠ 2 * q * q) := by
  have he1 : l + 2 * n + r + 2 = a + (2 * n + 1 - a) + (l + r + 1) := by omega
  have he2 : 2 * n + 1 = a + (2 * n + 1 - a) := by omega
  have hA : 4 <= 2 ^ a := by
    obtain ⟨k, rfl⟩ : ∃ k, a = k + 2 := ⟨a - 2, by omega⟩
    rw [Nat.pow_add]
    have := Nat.one_le_pow k 2 (by decide)
    omega
  have hB : 8 <= 2 ^ (2 * n + 1 - a) := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * n + 1 - a = k + 3 := ⟨2 * n - 2 - a, by omega⟩
    rw [hk, Nat.pow_add]
    have := Nat.one_le_pow k 2 (by decide)
    omega
  have hC : 16 <= 2 ^ (l + r + 1) := by
    obtain ⟨k, hk⟩ : ∃ k, l + r + 1 = k + 4 := ⟨l + r - 3, by omega⟩
    rw [hk, Nat.pow_add]
    have := Nat.one_le_pow k 2 (by decide)
    omega
  have hR : 1 <= 2 * r - 1 /\ 2 * r - 1 <= 3 := by omega
  have hpow1 : 2 ^ (lem_1a l n r) = 2 ^ a * (2 ^ (2 * n + 1 - a) * 2 ^ (l + r + 1)) := by
    unfold lem_1a
    rw [he1, Nat.pow_add, Nat.pow_add, Nat.mul_assoc]
  have hpow2 : (2 * r - 1) * 2 ^ (2 * n + 1) = 2 ^ a * (2 ^ (2 * n + 1 - a) * (2 * r - 1)) := by
    conv_lhs => rw [he2, Nat.pow_add]
    ring
  have hB_even : (2 ^ (2 * n + 1 - a)) % 2 = 0 := by
    obtain ⟨k, hk⟩ : ∃ k, 2 * n + 1 - a = k + 1 := ⟨2 * n - a, by omega⟩
    rw [hk, Nat.pow_succ]
    omega
  have ha_pow4 : 2 ^ a = 4 ^ (a / 2) := by
    have ha_div : a = 2 * (a / 2) := by omega
    conv_lhs => rw [ha_div, Nat.pow_mul]
  have hBC : 2 ^ (2 * n + 1 - a) * (2 * r - 1) + 6 <= 2 ^ (2 * n + 1 - a) * 2 ^ (l + r + 1) := by
    nlinarith
  have h_ineq : (2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1 < 2 ^ (lem_1a l n r) := by
    rw [hpow1, hpow2]
    nlinarith
  refine ⟨by unfold lem_1a; omega, h_ineq, by unfold lem_1b; omega, by unfold lem_1b; omega, ?_⟩
  set A := 2 ^ a
  set B := 2 ^ (2 * n + 1 - a)
  set C := 2 ^ (l + r + 1)
  set R := 2 * r - 1
  intro q hq
  have hfactor : lem_1b l n a r + 1 = A * lem_1h l n a r := by
    have h_odd_mul : A * lem_1h l n a r = A * (B * C) - A * (B * R) - 5 * A := by
      unfold lem_1h
      rw [Nat.mul_sub_left_distrib A, Nat.mul_sub_left_distrib B, Nat.mul_sub_left_distrib
          A, Nat.mul_comm A 5]
    unfold lem_1b
    rw [h_odd_mul, hpow1, hpow2]
    omega
  have hodd : lem_1h l n a r % 2 = 1 := by
    change (B * (C - R) - 5) % 2 = 1
    have hB_div : B = 2 * (B / 2) := by omega
    have hCR : 13 <= C - R := by omega
    have hB2 : 4 <= B / 2 := by omega
    have hprod : B * (C - R) = 2 * ((B / 2) * (C - R)) := by
      conv_lhs => rw [hB_div]
      ring
    have hge : 52 <= (B / 2) * (C - R) := by nlinarith
    rw [hprod]
    omega
  rw [hfactor, ha_pow4] at hq
  exact lem_1d (a / 2) (lem_1h l n a r) hodd q hq
theorem lem_1j (e : Nat) (he : 7 <= e) : 2 ^ e % 128 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 7 := ⟨e - 7, by omega⟩
  rw [Nat.pow_add]
  omega
theorem lem_1k (e : Nat) (he : 5 <= e) :
    2 ^ e % 96 = if e % 2 == 0 then 64 else 32 := by
  obtain ⟨k, rfl⟩ : ∃ k, e = k + 5 := ⟨e - 5, by omega⟩
  clear he
  induction k with
  | zero => decide
  | succ k ih =>
    have h1 : 2 ^ (k + 1 + 5) % 96 = (2 * (2 ^ (k + 5) % 96)) % 96 := by
      rw [show k + 1 + 5 = (k + 5) + 1 by omega, Nat.pow_succ', Nat.mul_mod]
    rcases (by omega : (k + 5) % 2 = 0 \/ (k + 5) % 2 = 1) with h0 | h0
    · have h2 : (k + 1 + 5) % 2 = 1 := by omega
      have h10 : (1 == 0) = false := rfl
      rw [h0, beq_self_eq_true, ite_eq_left rfl] at ih
      rw [h2, h10, ite_eq_right Bool.noConfusion, h1, ih]
    · have h2 : (k + 1 + 5) % 2 = 0 := by omega
      have h10 : (1 == 0) = false := rfl
      rw [h0, h10, ite_eq_right Bool.noConfusion] at ih
      rw [h2, beq_self_eq_true, ite_eq_left rfl, h1, ih]
theorem lem_1l (m l n a r : Nat) (hm : 0 < m)
    (hle : (2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1 < 2 ^ (lem_1a l n r)) :
    lem_1b l n a r % m =
      (2 ^ (lem_1a l n r) % m + m -
        ((2 * r - 1) * (2 ^ (2 * n + 1) % m) + 5 * (2 ^ a % m) + 1) % m) % m := by
  have heq : 2 ^ (lem_1a l n r) =
      lem_1b l n a r + ((2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1) := by
    unfold lem_1b; omega
  have h1 := lem_0l hm heq
  have h2 : ((2 * r - 1) * (2 ^ (2 * n + 1) % m) + 5 * (2 ^ a % m) + 1) % m =
      ((2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1) % m := by
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]
  rw [h2, h1]
theorem lem_1m (l n a r : Nat) (hl : 18 <= l) (hn : 3 <= n) (ha2 : 2 <= a)
    (ha_even : a % 2 = 0) (hr : r = 1 \/ r = 2)
    (hr1 : r = 1 -> a % 4 = 2) (hr2 : r = 2 -> 4 <= a)
    (hle : (2 * r - 1) * 2 ^ (2 * n + 1) + 5 * 2 ^ a + 1 < 2 ^ (lem_1a l n r)) :
    lem_19 (lem_1b l n a r) /\ lem_0p (lem_1a l n r) (lem_1b l n a r) = false := by
  have hL7 : 7 <= lem_1a l n r := by unfold lem_1a; omega
  have hN7 : 7 <= 2 * n + 1 := by omega
  have h128 : lem_1b l n a r % 128 = (128 - (5 * (2 ^ a % 128) + 1) % 128) % 128 := by
    rw [lem_1l 128 l n a r (by decide) hle,
        lem_1j _ hL7, lem_1j _ hN7]
    simp
  have hgood : lem_19 (lem_1b l n a r) := by
    unfold lem_19
    rw [h128]
    rcases (by omega : a = 2 \/ a = 4 \/ a = 6 \/ 8 <= a) with rfl | rfl | rfl | ha8
    · decide
    · decide
    · decide
    · rw [lem_1j a (by omega)]; decide
  refine ⟨hgood, ?_⟩
  unfold lem_0p
  rw [lem_1l 96 l n a r (by decide) hle,
      lem_1k (lem_1a l n r) (by omega),
      lem_1k (2 * n + 1) (by omega)]
  have hn_odd : (2 * n + 1) % 2 = 1 := by omega
  rw [hn_odd]
  rcases hr with rfl | rfl
  · have ha4 := hr1 rfl
    rcases (by omega : a = 2 \/ 6 <= a) with rfl | ha6
    · rcases (by omega : lem_1a l n 1 % 2 = 0 \/ lem_1a l n 1 % 2 = 1) with h0 | h1
      · simp [h0]
      · simp [h1]
    · rw [lem_1k a (by omega), ha_even]
      rcases (by omega : lem_1a l n 1 % 2 = 0 \/ lem_1a l n 1 % 2 = 1) with h0 | h1
      · simp [h0]
      · simp [h1]
  · have ha4 := hr2 rfl
    rcases (by omega : a = 4 \/ 6 <= a) with rfl | ha6
    · rcases (by omega : lem_1a l n 2 % 2 = 0 \/ lem_1a l n 2 % 2 = 1) with h0 | h1
      · simp [h0]
      · simp [h1]
    · rw [lem_1k a (by omega), ha_even]
      rcases (by omega : lem_1a l n 2 % 2 = 0 \/ lem_1a l n 2 % 2 = 1) with h0 | h1
      · simp [h0]
      · simp [h1]
theorem lem_1n (l n a r : Nat) (hw : Weak l (lem_0n n a r))
    (hn : 1 <= n) (ha : a <= 2 * n - 2) (hr : r = 1 \/ r = 2) :
    Inv (lem_1a l n r) (lem_1b l n a r) := by
  rcases hw with ⟨hl, _, _, hlow, hexc⟩
  rcases lem_1g n a r hn ha hr hlow with ⟨hn3, ha2, ha_even, hr1, hr2⟩
  rcases lem_1i l n a r hl ha2 ha ha_even hr with ⟨hL, hle, hpos, hbound, hhalf⟩
  rcases lem_1m l n a r hl hn3 ha2 ha_even hr hr1 hr2 hle with ⟨hlow', hexc'⟩
  refine ⟨⟨hL, hpos, hbound, hlow', hexc'⟩, hhalf, ?_⟩
  intro q hq
  have hok : lem_0q (l, n, a, r) = true := by
    unfold lem_0q
    have hinp : lem_0o (lem_0n n a r) = true := by
      unfold lem_0o; unfold lem_19 at hlow
      simp only [Bool.or_eq_true, beq_iff_eq]
      omega
    simp [hinp, hexc]
  apply lem_18 l n a r q ha_even hr hok
  have h1 : 2 ^ (l + 2 * n + r + 3) = 2 * 2 ^ (lem_1a l n r) := by
    unfold lem_1a
    rw [show l + 2 * n + r + 3 = (l + 2 * n + r + 2) + 1 by omega, Nat.pow_succ']
  have h2 : (2 * r - 1) * 2 ^ (2 * n + 2) = 2 * ((2 * r - 1) * 2 ^ (2 * n + 1)) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 by omega, Nat.pow_succ']
    ring
  have h3 : 5 * 2 ^ (a + 1) = 2 * (5 * 2 ^ a) := by
    rw [Nat.pow_succ']
    ring
  unfold lem_1b at hq
  omega
theorem lem_1o : Inv 18 260799 := by
  refine ⟨⟨by decide, by decide, by decide, Or.inr (Or.inl (by decide)), by decide⟩, ?_, ?_⟩
  · intro q hq
    rw [Nat.mul_assoc] at hq
    have h0 : q * q = 130400 := by omega
    have h2 : lem_02 (lem_0c 3) ((q * q) % 3) = true := lem_0d 3 q (by decide) (by decide)
    rw [h0] at h2
    revert h2; decide
  · intro q hq
    have h2 : lem_02 (lem_0c 9) ((q * q) % 9) = true := lem_0d 9 q (by decide) (by decide)
    rw [<- hq] at h2
    revert h2; decide
@[simp] theorem lem_Mz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config :=
    rfl
@[simp] theorem lem_Mo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M
    config := rfl
@[simp] theorem lem_Ms (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] theorem lem_1q : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem lem_Dh : (default : TapeBlank).head = 0 := rfl
@[simp] theorem lem_Dt : (default : TapeBlank).tail = default := rfl
@[simp] theorem append_nil (s : TapeBlank) : ([] : FinWord) +> s = s := rfl
@[simp] theorem append_cons (a : Fin 2) (l : FinWord) (s : TapeBlank) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] theorem append_assoc (l1 l2 : FinWord) (s : TapeBlank) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]
theorem lem_Sm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂ := by simp [h]
theorem lem_1r {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢⁺ c₂ := ⟨1, by decide, lem_Sm tm c₁ c₂ h⟩
theorem lem_Ma {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, lem_Ms, ih, Option.bind_assoc]
    simp_rw [lem_Ms]
theorem lem_Mt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c3) :
    c₁ [tm]⊢^{n+m} c3 := by
  rw [lem_Ma, h₁]; simp [h₂]
theorem lem_St {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢* c3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lem_Mt tm c₁ c₂ c3 n m hn hm⟩
theorem lem_Ps {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
theorem lem_Pt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢⁺ c3) : c₁ [tm]⊢⁺ c3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, lem_Mt tm c₁ c₂ c3 n m hn hm⟩
theorem lem_1s {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), lem_Mt tm c₁ c₂ c3 n m hn hm⟩
theorem lem_1t {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c3) : c₁ [tm]⊢⁺ c3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, lem_Mt tm c₁ c₂ c3 n m hn hm⟩
theorem lem_1u {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  lem_1s (lem_1r tm c₁ c₂ h₁) h₂
macro "finish" : tactic =>
  `(tactic| exact ⟨0, rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine lem_Ps ?_) <;>
    refine lem_1u (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
        Turing.ListBlank.head_cons, lem_Dh]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
        Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
            lem_1q, lem_Dh, lem_Dt, append_cons, append_nil])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
@[simp] theorem lem_1v {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem lem_Lp {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem lem_1w {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
theorem lem_1x {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, lem_Lp, lem_Lp, ih, List.append_assoc]
theorem lem_1y {α : Type*} (l : List α) (n : Nat) : l ^ n ++ l = l ++ l ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [lem_Lp, List.append_assoc, ih]
theorem lem_1y' {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ^ n ++ l := by
  rw [lem_Lp]; exact (lem_1y l n).symm
abbrev P11 : FinWord := [1, 1]
abbrev P01 : FinWord := [0, 1]
abbrev P00 : FinWord := [0, 0]
theorem lem_1z (k : Nat) (s : TapeBlank) :
    ([1] : FinWord) +> (P11 ^ k +> s) = P11 ^ k +> ([1] +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [lem_Lp, append_assoc, <- ih]
    rfl
theorem lem_1A (k : Nat) (l r : TapeBlank) :
    ((P11 ^ k +> l) <{{A}} r) [target_tm]⊢* (l <{{A}} (P01 ^ k +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [lem_Lp P11 k, append_assoc, lem_1y' P01 k, append_assoc]
    have h1 : ((P11 +> (P11 ^ k +> l)) <{{A}} r) [target_tm]⊢⁺
        ((P11 ^ k +> l) <{{A}} (P01 +> r)) := by
      simp only [append_cons, append_nil]; execute
    exact lem_Ps (lem_1s h1 (ih l (P01 +> r)))
theorem lem_1B (k : Nat) (l r : TapeBlank) :
    (l {{B}}> (P11 ^ k +> r)) [target_tm]⊢* ((P11 ^ k +> l) {{B}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_lhs : (l {{B}}> (P11 ^ (k + 1) +> r)) = (l {{B}}> (P11 +> (P11 ^ k +> r))) := by
      rw [lem_Lp P11 k, append_assoc]
    have h_rhs : ((P11 ^ (k + 1) +> l) {{B}}> r) = ((P11 ^ k +> (P11 +> l)) {{B}}> r) := by
      rw [lem_1y' P11 k, append_assoc]
    rw [h_lhs, h_rhs]
    have h1 : (l {{B}}> (P11 +> (P11 ^ k +> r))) [target_tm]⊢⁺
        ((P11 +> l) {{B}}> (P11 ^ k +> r)) := by
      simp only [append_cons, append_nil]; execute
    exact lem_Ps (lem_1s h1 (ih (P11 +> l) r))
theorem lem_1C (k : Nat) (l r : TapeBlank) :
    (l {{D}}> (P01 ^ k +> r)) [target_tm]⊢* ((P11 ^ k +> l) {{D}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    rw [lem_Lp P01 k, append_assoc, lem_1y' P11 k, append_assoc]
    have h1 : (l {{D}}> (P01 +> (P01 ^ k +> r))) [target_tm]⊢⁺
        ((P11 +> l) {{D}}> (P01 ^ k +> r)) := by
      simp only [append_cons, append_nil]; execute
    exact lem_Ps (lem_1s h1 (ih (P11 +> l) r))
def lem_1D (b : Bool) : FinWord :=
  if b then P01 else P11
def lem_1E : Nat -> Nat -> FinWord
  | 0, _ => []
  | len + 1, n => lem_1D (n % 2 == 1) ++ lem_1E len (n / 2)
def RC (len n : Nat) : TapeBlank :=
  lem_1E len n +> ([1] +> default)
theorem lem_1F (len : Nat) : lem_1E len 0 = P11 ^ len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have h0 : (0 % 2 == 1) = false := rfl
    simp only [lem_1E, h0, lem_1D, Bool.false_eq_true, ↓reduceIte,
      Nat.zero_div, ih, lem_Lp]
theorem lem_1G (len : Nat) : lem_1E len (2 ^ len - 1) = P01 ^ len := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hpos : 1 <= 2 ^ len := Nat.one_le_pow len 2 (by decide)
    have hmod : (2 ^ (len + 1) - 1) % 2 = 1 := by
      rw [Nat.pow_succ']; omega
    have hdiv : (2 ^ (len + 1) - 1) / 2 = 2 ^ len - 1 := by
      rw [Nat.pow_succ']; omega
    simp only [lem_1E, hmod, beq_self_eq_true, lem_1D, ↓reduceIte, hdiv, ih, lem_Lp]
theorem lem_1H (len1 len2 a b : Nat) (ha : a < 2 ^ len1) :
    lem_1E (len1 + len2) (b * 2 ^ len1 + a) = lem_1E len1 a ++ lem_1E len2 b := by
  induction len1 generalizing a with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0
    simp [lem_1E]
  | succ len1 ih =>
    have hpow : b * 2 ^ (len1 + 1) = 2 * (b * 2 ^ len1) := by rw [Nat.pow_succ']; ring
    have h1 : (b * 2 ^ (len1 + 1) + a) % 2 = a % 2 := by omega
    have h2 : (b * 2 ^ (len1 + 1) + a) / 2 = b * 2 ^ len1 + a / 2 := by omega
    have ha2 : a / 2 < 2 ^ len1 := by
      rw [Nat.pow_succ'] at ha
      omega
    rw [Nat.succ_add, lem_1E, lem_1E, h1, h2, ih (a / 2) ha2, List.append_assoc]
theorem lem_1I (len b : Nat) :
    lem_1E (1 + len) (b * 2) = P11 ++ lem_1E len b := by
  have h := lem_1H 1 len 0 b (by decide)
  simpa [lem_1E, lem_1D] using h
theorem lem_1J (len b : Nat) :
    lem_1E (1 + len) (b * 2 + 1) = P01 ++ lem_1E len b := by
  have h := lem_1H 1 len 1 b (by decide)
  simpa [lem_1E, lem_1D] using h
theorem lem_1K (k len b : Nat) :
    lem_1E (k + len) (b * 2 ^ k + (2 ^ k - 1)) = P01 ^ k ++ lem_1E len b := by
  have hpos : 1 <= 2 ^ k := Nat.one_le_pow k 2 (by decide)
  rw [lem_1H k len (2 ^ k - 1) b (by omega), lem_1G]
theorem lem_1L (len n : Nat) (hn : n + 1 < 2 ^ len) (l r : TapeBlank) :
    (l {{B}}> (lem_1E len (n + 1) +> r)) [target_tm]⊢⁺
    (l <{{A}} (lem_1E len n +> r)) := by
  induction len generalizing n l with
  | zero => omega
  | succ len ih =>
    rcases (by omega : n % 2 = 0 \/ n % 2 = 1) with h0 | h1
    · have hm1 : ((n + 1) % 2 == 1) = true := by rw [beq_iff_eq]; omega
      have hm0 : (n % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
      have hd1 : (n + 1) / 2 = n / 2 := by omega
      simp only [lem_1E, hm1, hm0, lem_1D, ↓reduceIte, Bool.false_eq_true, hd1,
        append_assoc, append_cons, append_nil]
      execute
    · have hm1 : ((n + 1) % 2 == 1) = false := by rw [beq_eq_false_iff_ne]; omega
      have hm0 : (n % 2 == 1) = true := by rw [beq_iff_eq]; omega
      have hd1 : (n + 1) / 2 = n / 2 + 1 := by omega
      have hlt : n / 2 + 1 < 2 ^ len := by
        rw [Nat.pow_succ'] at hn; omega
      simp only [lem_1E, hm1, hm0, lem_1D, ↓reduceIte, Bool.false_eq_true, hd1, append_assoc]
      have hs1 : (l {{B}}> (P11 +> (lem_1E len (n / 2 + 1) +> r))) [target_tm]⊢⁺
          ((P11 +> l) {{B}}> (lem_1E len (n / 2 + 1) +> r)) := by
        simp only [append_cons, append_nil]; execute
      have hs2 := ih (n / 2) hlt (P11 +> l)
      have hs3 : ((P11 +> l) <{{A}} (lem_1E len (n / 2) +> r)) [target_tm]⊢⁺
          (l <{{A}} (P01 +> (lem_1E len (n / 2) +> r))) := by
        simp only [append_cons, append_nil]; execute
      exact lem_Pt hs1 (lem_Pt hs2 hs3)
theorem lem_1M (len n : Nat) (hn : n + 1 < 2 ^ len) (l : TapeBlank) :
    (l {{B}}> RC len (n + 1)) [target_tm]⊢⁺ (l <{{A}} RC len n) :=
  lem_1L len n hn l ([1] +> default)
def LC0 (a b : Nat) : TapeBlank :=
  [1, 1, 1, 0, 1] +> (P11 ^ b +> (P00 +> (P11 ^ a +> default)))
def LC1 (a b : Nat) : TapeBlank :=
  [1, 1, 1, 1, 0] +> (P11 ^ b +> (P00 +> (P11 ^ a +> default)))
theorem lem_1N (k : Nat) (s r : TapeBlank) :
    (([1, 1, 1] +> (P11 ^ k +> (P00 +> s))) <{{A}} r) [target_tm]⊢⁺
    (([1] +> (P11 ^ k +> (P00 +> (P11 +> s)))) {{D}}> r) := by
  have heq1 : ([1, 1, 1] : FinWord) +> (P11 ^ k +> (P00 +> s)) =
      P11 ^ (k + 1) +> ([1] +> (P00 +> s)) := by
    change P11 +> ([1] +> (P11 ^ k +> (P00 +> s))) = P11 ^ (k + 1) +> ([1] +> (P00 +> s))
    rw [lem_1z, <- append_assoc, <- lem_Lp]
  rw [heq1]
  have h1 := lem_1A (k + 1) ([1] +> (P00 +> s)) r
  rw [lem_Lp P01 k, append_assoc] at h1
  have h2 : (([1] +> (P00 +> s)) <{{A}} (P01 +> (P01 ^ k +> r))) [target_tm]⊢⁺
      (([1] +> (P00 +> (P11 +> s))) {{D}}> (P01 ^ k +> r)) := by
    simp only [append_cons, append_nil]; execute
  have h3 := lem_1C k ([1] +> (P00 +> (P11 +> s))) r
  rw [<- lem_1z] at h3
  exact lem_1t h1 (lem_1s h2 h3)
theorem lem_1O (a b : Nat) (r : TapeBlank) :
    (LC0 a (b + 1) <{{A}} r) [target_tm]⊢⁺ (LC0 (a + 1) b {{B}}> r) := by
  unfold LC0
  rw [lem_Lp P11 b, append_assoc, lem_Lp P11 a, append_assoc]
  have h1 : (([1, 1, 1, 0, 1] +> (P11 +> (P11 ^ b +> (P00 +> (P11 ^ a +> default))))) <{{A}} r)
      [target_tm]⊢⁺
      (([1, 1, 1] +> (P11 ^ b +> (P00 +> (P11 ^ a +> default)))) <{{A}} ([1, 1, 1, 1] +> r)) := by
    simp only [append_cons, append_nil]; execute
  have h2 := lem_1N b (P11 ^ a +> default) ([1, 1, 1, 1] +> r)
  have h3 : (([1] +> (P11 ^ b +> (P00 +> (P11 +> (P11 ^ a +> default))))) {{D}}> ([1, 1, 1,
      1] +> r))
      [target_tm]⊢⁺
      (([1, 1, 1, 0, 1] +> (P11 ^ b +> (P00 +> (P11 +> (P11 ^ a +> default))))) {{B}}> r) := by
    simp only [append_cons, append_nil]; execute
  exact lem_Pt h1 (lem_Pt h2 h3)
theorem lem_1P (a b : Nat) (r : TapeBlank) :
    (LC1 a (b + 1) <{{A}} r) [target_tm]⊢⁺ (LC1 (a + 1) b {{B}}> r) := by
  unfold LC1
  rw [lem_Lp P11 b, append_assoc, lem_Lp P11 a, append_assoc]
  have h1 : (([1, 1, 1, 1, 0] +> (P11 +> (P11 ^ b +> (P00 +> (P11 ^ a +> default))))) <{{A}} r)
      [target_tm]⊢⁺
      (([1, 1, 1] +> (P11 ^ b +> (P00 +> (P11 ^ a +> default)))) <{{A}} ([1, 1, 0, 1] +> r)) := by
    simp only [append_cons, append_nil]; execute
  have h2 := lem_1N b (P11 ^ a +> default) ([1, 1, 0, 1] +> r)
  have h3 : (([1] +> (P11 ^ b +> (P00 +> (P11 +> (P11 ^ a +> default))))) {{D}}> ([1, 1, 0,
      1] +> r))
      [target_tm]⊢⁺
      (([1, 1, 1, 1, 0] +> (P11 ^ b +> (P00 +> (P11 +> (P11 ^ a +> default))))) {{B}}> r) := by
    simp only [append_cons, append_nil]; execute
  exact lem_Pt h1 (lem_Pt h2 h3)
theorem lem_1Q (a : Nat) (r : TapeBlank) :
    (LC0 (a + 1) 0 <{{A}} r) [target_tm]⊢⁺ (LC1 0 (a + 2) {{B}}> r) := by
  unfold LC0 LC1
  have hd : (P00 +> (P11 ^ 0 +> default) : TapeBlank) = default := by
    simp only [lem_1v, append_nil, append_cons, lem_1q]
  rw [hd, lem_1v, append_nil, lem_Lp P11 (a + 1), append_assoc, lem_Lp P11 a, append_assoc]
  simp only [append_cons, append_nil]
  execute
theorem lem_1R (a : Nat) (r : TapeBlank) :
    (LC1 a 0 <{{A}} r) [target_tm]⊢⁺ (LC0 1 a {{B}}> r) := by
  unfold LC1 LC0
  have hd : (P00 +> default : TapeBlank) = default := by
    simp only [append_cons, append_nil, lem_1q]
  rw [lem_1v, append_nil, lem_1w]
  have h1 : (([1, 1, 1, 1, 0] +> (P00 +> (P11 ^ a +> default))) <{{A}} r)
      [target_tm]⊢⁺
      (([1, 1, 1] +> (P11 ^ a +> (P00 +> default))) <{{A}} ([1, 1, 1, 1] +> r)) := by
    rw [hd]; simp only [append_cons, append_nil]; execute
  have h2 := lem_1N a default ([1, 1, 1, 1] +> r)
  have h3 : (([1] +> (P11 ^ a +> (P00 +> (P11 +> default)))) {{D}}> ([1, 1, 1, 1] +> r))
      [target_tm]⊢⁺
      (([1, 1, 1, 0, 1] +> (P11 ^ a +> (P00 +> (P11 +> default)))) {{B}}> r) := by
    simp only [append_cons, append_nil]; execute
  exact lem_Pt h1 (lem_Pt h2 h3)
inductive LRun : Nat -> TapeBlank -> TapeBlank -> Prop where
  | zero (l : TapeBlank) : LRun 0 l l
  | step {k : Nat} {l1 l2 l3 : TapeBlank} :
      (∀ r, (l1 <{{A}} r) [target_tm]⊢⁺ (l2 {{B}}> r)) ->
      LRun k l2 l3 -> LRun (k + 1) l1 l3
theorem lem_1S {k1 k2 : Nat} {l1 l2 l3 : TapeBlank}
    (h1 : LRun k1 l1 l2) (h2 : LRun k2 l2 l3) : LRun (k1 + k2) l1 l3 := by
  induction h1 with
  | zero _ => rw [Nat.zero_add]; exact h2
  | step hs _ ih => rw [Nat.succ_add]; exact LRun.step hs (ih h2)
theorem lem_1T {l1 l2 : TapeBlank}
    (hs : ∀ r, (l1 <{{A}} r) [target_tm]⊢⁺ (l2 {{B}}> r)) : LRun 1 l1 l2 :=
  LRun.step hs (LRun.zero l2)
theorem lem_1U {k : Nat} {l1 l2 : TapeBlank} (h : LRun k l1 l2)
    (len m : Nat) (hlt : m + k < 2 ^ len) :
    (l1 {{B}}> RC len (m + k)) [target_tm]⊢* (l2 {{B}}> RC len m) := by
  induction h generalizing m with
  | zero l => exact ⟨0, rfl⟩
  | @step k l1 l_mid l2 hs hrest ih =>
    rw [show m + (k + 1) = (m + k) + 1 by omega]
    have hdec := lem_1M len (m + k) (by omega) l1
    have hbounce := hs (RC len (m + k))
    have htail := ih m (by omega)
    exact lem_Ps (lem_1s (lem_Pt hdec hbounce) htail)
theorem lem_1V (n a : Nat) : LRun n (LC0 1 (n + a)) (LC0 (n + 1) a) := by
  induction n generalizing a with
  | zero =>
    rw [Nat.zero_add]
    exact LRun.zero _
  | succ n ih =>
    have h1 := ih (a + 1)
    rw [show n + (a + 1) = n + 1 + a by omega] at h1
    exact lem_1S h1 (lem_1T (lem_1O (n + 1) a))
theorem lem_1W (n a : Nat) : LRun n (LC1 0 (n + a)) (LC1 n a) := by
  induction n generalizing a with
  | zero =>
    rw [Nat.zero_add]
    exact LRun.zero _
  | succ n ih =>
    have h1 := ih (a + 1)
    rw [show n + (a + 1) = n + 1 + a by omega] at h1
    exact lem_1S h1 (lem_1T (lem_1P n a))
theorem lem_1X (a : Nat) : LRun (a + 1) (LC0 1 a) (LC1 0 (a + 2)) := by
  have h1 := lem_1V a 0
  rw [Nat.add_zero] at h1
  exact lem_1S h1 (lem_1T (lem_1Q a))
theorem lem_1Y (a : Nat) : LRun (a + 1) (LC1 0 a) (LC0 1 a) := by
  have h1 := lem_1W a 0
  rw [Nat.add_zero] at h1
  exact lem_1S h1 (lem_1T (lem_1R a))
theorem lem_1Z (a : Nat) : LRun (2 * a + 4) (LC0 1 a) (LC0 1 (a + 2)) := by
  have h := lem_1S (lem_1X a) (lem_1Y (a + 2))
  rw [show (a + 1) + (a + 2 + 1) = 2 * a + 4 by omega] at h
  exact h
theorem lem_20 (a : Nat) : LRun (a * (a + 1) * 2) (LC0 1 0) (LC0 1 (2 * a)) := by
  induction a with
  | zero => exact LRun.zero _
  | succ a ih =>
    have h := lem_1S ih (lem_1Z (2 * a))
    rw [show a * (a + 1) * 2 + (2 * (2 * a) + 4) = (a + 1) * (a + 1 + 1) * 2 by ring] at h
    exact h
theorem lem_21 (a b : Nat) (r : TapeBlank) :
    ((P11 ^ (b + 2) +> (P00 +> (P11 ^ (a + 2) +> default))) <{{A}} r) [target_tm]⊢⁺
    (LC0 1 0 {{B}}> (P01 ^ a +> (P11 +> (P01 +> (P11 +> (P01 ^ b +> r)))))) := by
  have h1 := lem_1A (b + 2) (P00 +> (P11 ^ (a + 2) +> default)) r
  have h2 : ((P00 +> (P11 ^ (a + 2) +> default)) <{{A}} (P01 ^ (b + 2) +> r)) [target_tm]⊢⁺
      ((P11 ^ (a + 2) +> default) <{{A}} (P11 +> (P01 +> (P11 +> (P01 ^ b +> r))))) := by
    rw [show b + 2 = 2 + b by omega, lem_1x P01 2 b, append_assoc,
        show a + 2 = 1 + (a + 1) by omega, lem_1x P11 1 (a + 1), append_assoc]
    simp only [lem_Lp, lem_1v, append_assoc, append_cons, append_nil]; execute
  have h3 := lem_1A (a + 2) default (P11 +> (P01 +> (P11 +> (P01 ^ b +> r))))
  have h4 : (default <{{A}} (P01 ^ (a + 2) +> (P11 +> (P01 +> (P11 +> (P01 ^ b +> r))))))
      [target_tm]⊢⁺
      (LC0 1 0 {{B}}> (P01 ^ a +> (P11 +> (P01 +> (P11 +> (P01 ^ b +> r)))))) := by
    unfold LC0
    rw [show a + 2 = 2 + a by omega, lem_1x P01 2 a, append_assoc]
    simp only [lem_Lp, lem_1v, append_assoc, append_cons, append_nil]
    execute
  exact lem_1t h1 (lem_Pt (lem_1s h2 h3) h4)
theorem lem_22 (a b len : Nat) :
    (LC0 (a + 2) (b + 1) {{B}}> RC len 0) [target_tm]⊢⁺
    (LC0 1 0 {{B}}> RC (len + a + b + 5) (2 ^ (len + a + b) * 32 - 2 ^ (a + b) * 8 - 2 ^ a * 5 -
        1)) := by
  unfold RC
  rw [lem_1F]
  set s := P00 +> (P11 ^ (a + 2) +> default)
  have h1 : (LC0 (a + 2) (b + 1) {{B}}> (P11 ^ len +> ([1] +> default))) [target_tm]⊢*
      ((P11 ^ len +> ([1, 1, 1, 0, 1] +> (P11 ^ (b + 1) +> s))) {{B}}> ([1] +> default)) :=
    lem_1B len ([1, 1, 1, 0, 1] +> (P11 ^ (b + 1) +> s)) ([1] +> default)
  have h2 : ((P11 ^ len +> ([1, 1, 1, 0, 1] +> (P11 ^ (b + 1) +> s))) {{B}}> ([1] +> default))
      [target_tm]⊢⁺
      (([1] +> (P11 ^ len +> ([1, 1, 1, 0, 1] +> (P11 ^ (b + 1) +> s)))) <{{A}} ([1] +> default)) :=
          by
    simp only [append_cons, append_nil]; execute
  have h2_eq : ([1] : FinWord) +> (P11 ^ len +> ([1, 1, 1, 0, 1] +> (P11 ^ (b + 1) +> s))) =
      P11 ^ (len + 1) +> ([1, 1, 0, 1] +> (P11 ^ (b + 1) +> s)) := by
    rw [lem_1z, lem_1y' P11 len, append_assoc]
    simp only [append_cons, append_nil]
  rw [h2_eq] at h2
  have h3 := lem_1A (len + 1) ([1, 1, 0, 1] +> (P11 ^ (b + 1) +> s)) ([1] +> default)
  have h4 : (([1, 1, 0, 1] +> (P11 ^ (b + 1) +> s)) <{{A}} (P01 ^ (len + 1) +> ([1] +> default)))
      [target_tm]⊢⁺
      ((P11 ^ (b + 2) +> s) <{{A}} (P11 +> (P01 ^ (len + 1) +> ([1] +> default)))) := by
    rw [lem_Lp P11 (b + 1), append_assoc]
    simp only [append_cons, append_nil]; execute
  have h5 := lem_21 a b (P11 +> (P01 ^ (len + 1) +> ([1] +> default)))
  have h_all := lem_1t h1
    (lem_Pt (lem_1s h2 h3) (lem_Pt h4 h5))
  have h_word : lem_1E (len + a + b + 5) (2 ^ (len + a + b) * 32 - 2 ^ (a + b) * 8 - 2 ^ a * 5 - 1)
      +>
      ([1] +> default) =
      (P01 ^ a +> (P11 +> (P01 +> (P11 +> (P01 ^ b +> (P11 +> (P01 ^ (len + 1) +> ([1] +>
          default)))))))) := by
    have hlen : len + a + b + 5 = a + (1 + (1 + (1 + (b + (1 + (1 + len)))))) := by omega
    have hval : 2 ^ (len + a + b) * 32 - 2 ^ (a + b) * 8 - 2 ^ a * 5 - 1 =
        ((((((2 ^ len - 1) * 2 + 1) * 2) * 2 ^ b + (2 ^ b - 1)) * 2 * 2 + 1) * 2) * 2 ^ a + (2 ^ a -
            1) := by
      obtain ⟨L, hL⟩ : ∃ L, 2 ^ len = L + 1 :=
        ⟨2 ^ len - 1, by have := Nat.one_le_pow len 2 (by decide); omega⟩
      obtain ⟨A, hA⟩ : ∃ A, 2 ^ a = A + 1 :=
        ⟨2 ^ a - 1, by have := Nat.one_le_pow a 2 (by decide); omega⟩
      obtain ⟨B, hB⟩ : ∃ B, 2 ^ b = B + 1 :=
        ⟨2 ^ b - 1, by have := Nat.one_le_pow b 2 (by decide); omega⟩
      rw [show len + a + b = len + (a + b) by omega, Nat.pow_add 2 len (a + b), Nat.pow_add 2 a
          b, hL, hA, hB]
      simp only [Nat.add_sub_cancel]
      have hring : (L + 1) * ((A + 1) * (B + 1)) * 32 =
          ((((((L * 2 + 1) * 2) * (B + 1) + B) * 2 * 2 + 1) * 2) * (A + 1) + A) +
          ((A + 1) * (B + 1) * 8 + (A + 1) * 5 + 1) := by ring
      omega
    rw [hlen, hval,
        lem_1K a,
        lem_1I,
        lem_1J,
        lem_1I,
        lem_1K b,
        lem_1I,
        lem_1J,
        lem_1G,
        lem_Lp P01 len]
    simp only [append_assoc]
  rw [h_word]
  exact h_all
theorem lem_23 (a b len : Nat) :
    (LC1 (a + 2) (b + 2) {{B}}> RC len 0) [target_tm]⊢⁺
    (LC0 1 0 {{B}}> RC (len + a + b + 6) (2 ^ (len + a + b) * 64 - 2 ^ (a + b) * 24 - 2 ^ a * 5 -
        1)) := by
  unfold RC
  rw [lem_1F]
  set s := P00 +> (P11 ^ (a + 2) +> default)
  have h1 : (LC1 (a + 2) (b + 2) {{B}}> (P11 ^ len +> ([1] +> default))) [target_tm]⊢*
      ((P11 ^ len +> ([1, 1, 1, 1, 0] +> (P11 ^ (b + 2) +> s))) {{B}}> ([1] +> default)) :=
    lem_1B len ([1, 1, 1, 1, 0] +> (P11 ^ (b + 2) +> s)) ([1] +> default)
  have h2 : ((P11 ^ len +> ([1, 1, 1, 1, 0] +> (P11 ^ (b + 2) +> s))) {{B}}> ([1] +> default))
      [target_tm]⊢⁺
      (([1] +> (P11 ^ len +> ([1, 1, 1, 1, 0] +> (P11 ^ (b + 2) +> s)))) <{{A}} ([1] +> default)) :=
          by
    simp only [append_cons, append_nil]; execute
  have h2_eq : ([1] : FinWord) +> (P11 ^ len +> ([1, 1, 1, 1, 0] +> (P11 ^ (b + 2) +> s))) =
      P11 ^ (len + 1) +> ([1, 1, 1, 0] +> (P11 ^ (b + 2) +> s)) := by
    rw [lem_1z, lem_1y' P11 len, append_assoc]
    simp only [append_cons, append_nil]
  rw [h2_eq] at h2
  have h3 := lem_1A (len + 1) ([1, 1, 1, 0] +> (P11 ^ (b + 2) +> s)) ([1] +> default)
  have h4 : (([1, 1, 1, 0] +> (P11 ^ (b + 2) +> s)) <{{A}} (P01 ^ (len + 1) +> ([1] +> default)))
      [target_tm]⊢⁺
      ((P11 ^ (b + 2) +> s) <{{A}} (P11 +> (P11 +> (P01 ^ (len + 1) +> ([1] +> default))))) := by
    rw [lem_Lp P11 (b + 1), append_assoc]
    simp only [append_cons, append_nil]; execute
  have h5 := lem_21 a b (P11 +> (P11 +> (P01 ^ (len + 1) +> ([1] +> default))))
  have h_all := lem_1t h1
    (lem_Pt (lem_1s h2 h3) (lem_Pt h4 h5))
  have h_word : lem_1E (len + a + b + 6) (2 ^ (len + a + b) * 64 - 2 ^ (a + b) * 24 - 2 ^ a * 5 - 1)
      +>
      ([1] +> default) =
      (P01 ^ a +> (P11 +> (P01 +> (P11 +> (P01 ^ b +> (P11 +> (P11 +> (P01 ^ (len + 1) +> ([1] +>
          default))))))))) := by
    have hlen : len + a + b + 6 = a + (1 + (1 + (1 + (b + (1 + (1 + (1 + len))))))) := by omega
    have hval : 2 ^ (len + a + b) * 64 - 2 ^ (a + b) * 24 - 2 ^ a * 5 - 1 =
        ((((((2 ^ len - 1) * 2 + 1) * 2 * 2) * 2 ^ b + (2 ^ b - 1)) * 2 * 2 + 1) * 2) * 2 ^ a + (2 ^
            a - 1) := by
      obtain ⟨L, hL⟩ : ∃ L, 2 ^ len = L + 1 :=
        ⟨2 ^ len - 1, by have := Nat.one_le_pow len 2 (by decide); omega⟩
      obtain ⟨A, hA⟩ : ∃ A, 2 ^ a = A + 1 :=
        ⟨2 ^ a - 1, by have := Nat.one_le_pow a 2 (by decide); omega⟩
      obtain ⟨B, hB⟩ : ∃ B, 2 ^ b = B + 1 :=
        ⟨2 ^ b - 1, by have := Nat.one_le_pow b 2 (by decide); omega⟩
      rw [show len + a + b = len + (a + b) by omega, Nat.pow_add 2 len (a + b), Nat.pow_add 2 a
          b, hL, hA, hB]
      simp only [Nat.add_sub_cancel]
      have hring : (L + 1) * ((A + 1) * (B + 1)) * 64 =
          ((((((L * 2 + 1) * 2 * 2) * (B + 1) + B) * 2 * 2 + 1) * 2) * (A + 1) + A) +
          ((A + 1) * (B + 1) * 24 + (A + 1) * 5 + 1) := by ring
      omega
    rw [hlen, hval,
        lem_1K a,
        lem_1I,
        lem_1J,
        lem_1I,
        lem_1K b,
        lem_1I,
        lem_1I,
        lem_1J,
        lem_1G,
        lem_Lp P01 len]
    simp only [append_assoc]
  rw [h_word]
  exact h_all
def S' (len x : Nat) : Cfg (Fin 2) (Fin 6) :=
  LC0 1 0 {{B}}> RC len x
theorem lem_24 (n a b len : Nat) (hab : a + b + 2 = 2 * n)
    (hlt : n * (n + 1) * 2 + (a + 1) < 2 ^ len) :
    (S' len (n * (n + 1) * 2 + (a + 1))) [target_tm]⊢⁺
    (S' (len + a + b + 5) (2 ^ (len + a + b) * 32 - 2 ^ (a + b) * 8 - 2 ^ a * 5 - 1)) := by
  unfold S'
  have hrun : LRun (n * (n + 1) * 2 + (a + 1)) (LC0 1 0) (LC0 (a + 2) (b + 1)) := by
    have h1 := lem_20 n
    have h2 := lem_1V (a + 1) (b + 1)
    rw [show (a + 1) + (b + 1) = 2 * n by omega] at h2
    exact lem_1S h1 h2
  have hinc := lem_1U hrun len 0 (by rw [Nat.zero_add]; exact hlt)
  rw [Nat.zero_add] at hinc
  exact lem_1t hinc (lem_22 a b len)
theorem lem_25 (n a b len : Nat) (hab : a + b + 2 = 2 * n)
    (hlt : n * (n + 1) * 2 + ((n * 2 + 1) + (a + 2)) < 2 ^ len) :
    (S' len (n * (n + 1) * 2 + ((n * 2 + 1) + (a + 2)))) [target_tm]⊢⁺
    (S' (len + a + b + 6) (2 ^ (len + a + b) * 64 - 2 ^ (a + b) * 24 - 2 ^ a * 5 - 1)) := by
  unfold S'
  have hrun : LRun (n * (n + 1) * 2 + ((n * 2 + 1) + (a + 2))) (LC0 1 0) (LC1 (a + 2) (b + 2)) := by
    have h1 := lem_20 n
    have h2 := lem_1X (2 * n)
    have h3 := lem_1W (a + 2) (b + 2)
    rw [show (a + 2) + (b + 2) = 2 * n + 2 by omega] at h3
    rw [show 2 * n = n * 2 by ring] at h1 h2 h3
    exact lem_1S h1 (lem_1S h2 h3)
  have hinc := lem_1U hrun len 0 (by rw [Nat.zero_add]; exact hlt)
  rw [Nat.zero_add] at hinc
  exact lem_1t hinc (lem_23 a b len)
theorem lem_26 (l n a r : Nat) (hw : Weak l (lem_0n n a r))
    (hn : 1 <= n) (ha : a <= 2 * n - 2) (hr : r = 1 \/ r = 2) :
    (S' l (lem_0n n a r)) [target_tm]⊢⁺ (S' (lem_1a l n r) (lem_1b l n a r)) := by
  rcases hw with ⟨_, _, hbound, _, _⟩
  set b := 2 * n - 2 - a
  have hab : a + b + 2 = 2 * n := by omega
  rcases hr with rfl | rfl
  · have hinp : lem_0n n a 1 = n * (n + 1) * 2 + (a + 1) := by
      unfold lem_0n
      change (if true then 2 * n * (n + 1) + a + 1 else 2 * (n + 1) * (n + 1) + a + 1) = _
      simp only [↓reduceIte]
      ring
    have hlen : lem_1a l n 1 = l + a + b + 5 := by unfold lem_1a; omega
    have hval : lem_1b l n a 1 = 2 ^ (l + a + b) * 32 - 2 ^ (a + b) * 8 - 2 ^ a * 5 - 1 := by
      unfold lem_1b lem_1a
      have he1 : l + 2 * n + 1 + 2 = (l + a + b) + 5 := by omega
      have he2 : 2 * n + 1 = (a + b) + 3 := by omega
      rw [he1, he2, Nat.pow_add 2 (l + a + b) 5, Nat.pow_add 2 (a + b) 3]
      change 2 ^ (l + a + b) * 32 - 1 * (2 ^ (a + b) * 8) - 5 * 2 ^ a - 1 = _
      omega
    rw [hinp] at hbound ⊢
    rw [hlen, hval]
    exact lem_24 n a b l hab hbound
  · have hinp : lem_0n n a 2 = n * (n + 1) * 2 + ((n * 2 + 1) + (a + 2)) := by
      unfold lem_0n
      change (if false then 2 * n * (n + 1) + a + 1 else 2 * (n + 1) * (n + 1) + a + 1) = _
      simp only [Bool.false_eq_true, ↓reduceIte]
      ring
    have hlen : lem_1a l n 2 = l + a + b + 6 := by unfold lem_1a; omega
    have hval : lem_1b l n a 2 = 2 ^ (l + a + b) * 64 - 2 ^ (a + b) * 24 - 2 ^ a * 5 - 1 := by
      unfold lem_1b lem_1a
      have he1 : l + 2 * n + 2 + 2 = (l + a + b) + 6 := by omega
      have he2 : 2 * n + 1 = (a + b) + 3 := by omega
      rw [he1, he2, Nat.pow_add 2 (l + a + b) 6, Nat.pow_add 2 (a + b) 3]
      change 2 ^ (l + a + b) * 64 - 3 * (2 ^ (a + b) * 8) - 5 * 2 ^ a - 1 = _
      omega
    rw [hinp] at hbound ⊢
    rw [hlen, hval]
    exact lem_25 n a b l hab hbound
theorem lem_27 :
    (init [] : Cfg (Fin 2) (Fin 6)) [target_tm]⊢* S' 18 260799 := by
  have h1 : (init [] : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺ (LC1 0 1 {{B}}> RC 6 57) := by
    have hinit : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
    have hbw : lem_1E 6 57 = [0, 1, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1] := rfl
    rw [hinit]
    unfold LC1 RC
    rw [hbw]
    simp only [lem_1v, lem_1w, append_cons, append_nil, lem_1q,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, lem_Dh, lem_Dt]
    execute
  have hrun : LRun 57 (LC1 0 1) (LC0 8 2) := by
    have r1 := lem_1Y 1
    have r2 := lem_1Z 1
    have r3 := lem_1Z 3
    have r4 := lem_1Z 5
    have r5 := lem_1Z 7
    have r6 := lem_1V 7 2
    exact lem_1S r1 (lem_1S r2 (lem_1S r3 (lem_1S r4 (lem_1S r5 r6))))
  have h2 := lem_1U hrun 6 0 (by decide)
  rw [Nat.zero_add] at h2
  have h3 := lem_22 6 1 6
  exact lem_Ps (lem_Pt (lem_1s h1 h2) h3)
theorem lem_1p : Weak 31 2144731135 :=
  ⟨by decide, by decide, by decide, Or.inr (Or.inr (Or.inr (by decide))), by decide⟩
theorem lem_28 :
    ((default : TapeBlank) {{B}}> default) [target_tm]⊢* S' 31 2144731135 := by
  have h1 : ((default : TapeBlank) {{B}}> default) [target_tm]⊢⁺
      (LC1 0 1 {{B}}> RC 3 6) := by
    have hbw : lem_1E 3 6 = [1, 1, 0, 1, 0, 1] := rfl
    unfold LC1 RC
    rw [hbw]
    simp only [lem_1v, lem_1w, append_cons, append_nil, lem_1q,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, lem_Dh, lem_Dt]
    execute
  have hrun : LRun 6 (LC1 0 1) (LC1 2 1) := by
    have r1 := lem_1Y 1
    have r2 := lem_1X 1
    have r3 := lem_1W 2 1
    exact lem_1S r1 (lem_1S r2 r3)
  have h2 := lem_1U hrun 3 0 (by decide)
  rw [Nat.zero_add] at h2
  have h3 : (LC1 2 1 {{B}}> RC 3 0) [target_tm]⊢⁺ S' 8 238 := by
    have hbw0 : lem_1E 3 0 = [1, 1, 1, 1, 1, 1] := rfl
    have hbw8 : lem_1E 8 238 = [1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1] := rfl
    unfold LC1 S' LC0 RC
    rw [hbw0, hbw8]
    simp only [lem_Lp, lem_1v, append_assoc, append_cons, append_nil,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    execute
  have h4 := lem_24 10 17 1 8 (by decide) (by decide)
  exact lem_Ps
    (lem_Pt (lem_Pt (lem_1s h1 h2) h3) h4)
theorem lem_29 {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ}
    (h : c₁ [M]⊢⁺ c₂) : (step M c₁).isSome := by
  rcases h with ⟨n, hn, hms⟩
  cases n with
  | zero => omega
  | succ n =>
    rw [Nat.add_comm n 1, lem_Ma, lem_Mo] at hms
    cases hstep : step M c₁ with
    | none => rw [hstep] at hms; simp at hms
    | some c' => rfl
theorem lem_2a (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : Nat) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  rw [Nat.add_comm n 1, lem_Ma, lem_Mo]
theorem lem_2b {M : Machine Γ Λ} {c0 c₁ c : Cfg Γ Λ}
    {n m : Nat} (h1 : c0 [M]⊢^{n} c₁) (h2 : c0 [M]⊢^{m} c) :
    (m <= n /\ c [M]⊢^{n - m} c₁) \/ (n < m /\ c₁ [M]⊢^{m - n} c) := by
  induction n generalizing c0 m with
  | zero =>
    simp only [lem_Mz, Option.some.injEq] at h1
    subst h1
    rcases m with _ | m
    · simp only [lem_Mz, Option.some.injEq] at h2
      subst h2
      left; exact ⟨by omega, rfl⟩
    · right; exact ⟨by omega, h2⟩
  | succ n ih =>
    rcases m with _ | m
    · simp only [lem_Mz, Option.some.injEq] at h2
      subst h2
      left; exact ⟨by omega, h1⟩
    · rw [lem_2a] at h1 h2
      cases hs : step M c0 with
      | none => rw [hs] at h1; simp at h1
      | some c0' =>
        simp only [hs, Option.bind] at h1 h2
        rcases ih h1 h2 with ⟨hle, h⟩ | ⟨hlt, h⟩
        · left; refine ⟨by omega, ?_⟩; simpa only [Nat.succ_sub_succ_eq_sub] using h
        · right; refine ⟨by omega, ?_⟩; simpa only [Nat.succ_sub_succ_eq_sub] using h
theorem lem_2c {M : Machine Γ Λ} {c c' : Cfg Γ Λ}
    (h : c [M]⊢* c') (h' : (step M c').isSome) : (step M c).isSome := by
  rcases h with ⟨k, hk⟩
  cases k with
  | zero =>
    simp only [lem_Mz, Option.some.injEq] at hk
    subst hk; exact h'
  | succ k =>
    exact lem_29 ⟨k + 1, by omega, hk⟩
theorem lem_2d (l x : Nat) (hinv : Inv l x) :
    ∃ l' x', Inv l' x' /\ (S' l x) [target_tm]⊢⁺ (S' l' x') := by
  rcases lem_1f l x hinv with ⟨n, a, r, hn, ha, hr, hxeq⟩
  have hw : Weak l (lem_0n n a r) := hxeq ▸ hinv.inv_weak
  refine ⟨lem_1a l n r, lem_1b l n a r, lem_1n l n a r hw hn ha hr, ?_⟩
  rw [hxeq]; exact lem_26 l n a r hw hn ha hr
theorem lem_2e (l x : Nat) (hinv : Inv l x) :
    (step target_tm (S' l x)).isSome := by
  rcases lem_2d l x hinv with ⟨_, _, _, hstep⟩
  exact lem_29 hstep
theorem lem_2f (k : Nat) :
    ∀ c l x, Inv l x -> ((S' l x) [target_tm]⊢^{k} c) -> (step target_tm c).isSome := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro c l x hinv hreach
    rcases lem_2d l x hinv with ⟨l', x', hinv', m, hm_pos, hm⟩
    rcases lem_2b hm hreach with ⟨_, hd⟩ | ⟨hlt, hd⟩
    · exact lem_2c ⟨m - k, hd⟩ (lem_2e l' x' hinv')
    · exact ih (k - m) (by omega) c l' x' hinv' hd
theorem lem_2g {c0 : Cfg (Fin 2) (Fin 6)} {l x : Nat}
    (h0 : c0 [target_tm]⊢* S' l x) (hinv : Inv l x) :
    ∀ cfg, (c0 [target_tm]⊢* cfg) -> (step target_tm cfg).isSome := by
  intro cfg ⟨k, hk⟩
  rcases h0 with ⟨m, hm⟩
  rcases lem_2b hm hk with ⟨_, hd⟩ | ⟨_, hd⟩
  · exact lem_2c ⟨m - k, hd⟩ (lem_2e l x hinv)
  · exact lem_2f (k - m) cfg l x hinv hd

theorem is_not_halt_from_0831_tm :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{1}}> default) [target_tm]⊢* cfg) →
      (step target_tm cfg).isSome := by
  have h1 : ((default : ListBlank (Fin 2)) {{1}}> default) [target_tm]⊢*
      S' 31 (lem_0n 32746 64610 1) := lem_28
  have h2 : (S' 31 (lem_0n 32746 64610 1)) [target_tm]⊢⁺
      (S' (lem_1a 31 32746 1) (lem_1b 31 32746 64610 1)) :=
    lem_26 31 32746 64610 1 lem_1p (by decide) (by decide) (Or.inl rfl)
  have hinv : Inv (lem_1a 31 32746 1) (lem_1b 31 32746 64610 1) :=
    lem_1n 31 32746 64610 1 lem_1p (by decide) (by decide) (Or.inl rfl)
  exact lem_2g (lem_St h1 (lem_Ps h2)) hinv

theorem is_does_not_halt : IsNotHalt target_tm := lem_2g lem_27 lem_1o

end Solution

public section

theorem is_not_halt_from_0831 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{1}}> default) [target]⊢* cfg) →
      (step target cfg).isSome :=
  Solution.is_not_halt_from_0831_tm

theorem is_not_halt : IsNotHalt target := Solution.is_does_not_halt

end

end BusyBeaver.M_1RB1LC_1LA1RB_1LD0LA_1RE0RF_HHH1RD_0RE1RB
