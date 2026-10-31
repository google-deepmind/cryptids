/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 1, Stmt.write 1 Dir.right)
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
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
local notation "zB" => ListBlank (Fin 2)
local notation "zF" => List (Fin 2)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
namespace Sparse
abbrev num := List (Nat × Int)
def pow2 (n : Nat) : Int := (2 : Int) ^ n
def value : num -> Int
  | [] => 0
  | (e,c) :: xs => c * pow2 e + value xs
lemma zPp (n : Nat) : 0 < pow2 n := by
  unfold pow2; positivity
lemma pow2_add (a b : Nat) : pow2 (a + b) = pow2 a * pow2 b := by
  unfold pow2; exact pow_add 2 a b
lemma z00 {a b : Nat} (h : a <= b) : pow2 b = pow2 a * pow2 (b - a) := by
  rw [<- pow2_add,Nat.add_sub_of_le h]
def z01 (n : Nat) (c : Int) : Option (Int × Bool) :=
  if n <= 16 then some (c / pow2 n,decide (c % pow2 n = 0))
  else if c.natAbs < 65536 then
    some (if c < 0 then -1 else 0,decide (c = 0))
  else none
lemma z02 {n : Nat} (h : 16 < n) : (65536 : Int) <= pow2 n := by
  unfold pow2
  have h1 : (65536 : Int) = (2 : Int) ^ 16 := by norm_num
  rw [h1]
  exact pow_le_pow_right₀ (by norm_num) (by omega)
lemma z03 {n : Nat} {c q : Int} {bz : Bool} (h : z01 n c = some (q,bz)) :
    ∃ r,c = pow2 n * q + r /\ 0 <= r /\ r < pow2 n /\ (bz = true <-> r = 0) := by
  unfold z01 at h
  have hp := zPp n
  split_ifs at h with hn hc hneg
  · injection h with hpair
    injection hpair with hq hz
    subst hq hz
    refine ⟨c % pow2 n,(Int.mul_ediv_add_emod c (pow2 n)).symm,Int.emod_nonneg c (by linarith),
      Int.emod_lt_of_pos c hp,decide_eq_true_iff⟩
  · injection h with hpair
    injection hpair with hq hz
    subst hq hz
    have hp16 : (65536 : Int) <= pow2 n := z02 (by omega)
    have h_abs : -65536 < c := by omega
    refine ⟨c + pow2 n,by ring,by linarith,by linarith,?_⟩
    rw [decide_eq_true_iff]
    (try omega)
  · injection h with hpair
    injection hpair with hq hz
    subst hq hz
    have hp16 : (65536 : Int) <= pow2 n := z02 (by omega)
    have h_abs : c < 65536 := by omega
    refine ⟨c,by ring,by omega,by linarith,decide_eq_true_iff⟩
def cmp0 (x : Int) : Int :=
  if x < 0 then -1 else if x = 0 then 0 else 1
def z04 (bz : Bool) (s : Int) : Int :=
  if s = 0 then (if bz then 0 else 1) else s
lemma z05 {p q r : Int} {bz : Bool}
    (hp : 0 < p) (hr0 : 0 <= r) (hr1 : r < p) (hz : bz = true <-> r = 0) :
    cmp0 (p * q + r) = z04 bz (cmp0 q) := by
  unfold cmp0 z04
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have hq1 : q <= -1 := by omega
    have hpq : p * q <= -p := by nlinarith
    have hsum : p * q + r < 0 := by linarith
    simp [hq,hsum]
  · simp only [mul_zero,zero_add,lt_irrefl,↓reduceIte]
    cases bz
    · have hr_ne : r ≠ 0 := by intro h; exact Bool.false_ne_true (hz.mpr h)
      have hr_pos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr_ne)
      have h_not_lt : ¬(r < 0) := by omega
      simp [h_not_lt,hr_ne]
    · have hr_eq : r = 0 := hz.mp rfl
      simp [hr_eq]
  · have hq1 : 1 <= q := by omega
    have hpq : p <= p * q := by nlinarith
    have hsum : 0 < p * q + r := by linarith
    have h_not_lt : ¬(p * q + r < 0) := by omega
    have h_ne : p * q + r ≠ 0 := by omega
    have hq_not_lt : ¬(q < 0) := by omega
    have hq_ne : q ≠ 0 := by omega
    simp [hq_not_lt,hq_ne,h_not_lt,h_ne]
def z06 : num -> Nat -> Int -> Option Int
  | [],_,carry => some (cmp0 carry)
  | (e,c) :: xs,base,carry =>
    if base <= e then
      match z01 (e - base) carry with
      | some (q,bz) =>
        match z06 xs e (c + q) with
        | some s => some (z04 bz s)
        | none => none
      | none => none
    else none
lemma z07 {xs : num} {base : Nat} {carry s : Int}
    (h : z06 xs base carry = some s) :
    ∃ v,value xs = pow2 base * v /\ cmp0 (carry + v) = s := by
  induction xs generalizing base carry s with
  | nil =>
    simp only [z06] at h
    injection h with hs
    exact ⟨0,by simp [value],by simp [hs]⟩
  | cons ec xs ih =>
    rcases ec with ⟨e,c⟩
    simp only [z06] at h
    split_ifs at h with hbe
    cases hd : z01 (e - base) carry with
    | none => rw [hd] at h; contradiction
    | some qz =>
      rcases qz with ⟨q,bz⟩
      rw [hd] at h
      dsimp only at h
      cases hs : z06 xs e (c + q) with
      | none => rw [hs] at h; contradiction
      | some t =>
        rw [hs] at h
        injection h with ht
        subst ht
        rcases z03 hd with ⟨r,hcarry,hr0,hr1,hzero⟩
        rcases ih hs with ⟨v,hv,hcmp⟩
        refine ⟨pow2 (e - base) * (c + v),?_,?_⟩
        · simp only [value,hv,z00 hbe]
          ring
        · have heq : carry + pow2 (e - base) * (c + v) = pow2 (e - base) * (c + q + v) + r := by
            linarith
          rw [heq,z05 (zPp (e - base)) hr0 hr1 hzero,<- hcmp]
def z08 (xs : num) : Option Int := z06 xs 0 0
lemma z09 {xs : num} {s : Int} (h : z08 xs = some s) :
    cmp0 (value xs) = s := by
  rcases z07 h with ⟨v,hv,hs⟩
  have hv1 : value xs = v := by simp [pow2] at hv; exact hv
  simpa [hv1] using hs
def z0a (e : Nat) (c : Int) : num -> num
  | [] => [(e,c)]
  | (f,d) :: xs =>
    if e < f then (e,c) :: (f,d) :: xs
    else if e = f then (e,c + d) :: xs
    else (f,d) :: z0a e c xs
lemma z0b (xs : num) (e : Nat) (c : Int) :
    value (z0a e c xs) = c * pow2 e + value xs := by
  induction xs with
  | nil => simp [z0a,value]
  | cons fd xs ih =>
    rcases fd with ⟨f,d⟩
    simp only [z0a]
    split_ifs with hlt heq
    · simp [value]
    · subst heq; simp [value]; ring
    · simp [value,ih]; ring
def add (xs ys : num) : num :=
  xs.foldr (fun ec zs => z0a ec.1 ec.2 zs) ys
def neg (xs : num) : num :=
  xs.map (fun ec => (ec.1,-ec.2))
def sub (xs ys : num) : num := add xs (neg ys)
def shift (n : Nat) (xs : num) : num :=
  xs.map (fun ec => (n + ec.1,ec.2))
def power (n : Nat) : num := [(n,1)]
def small (c : Int) : num := [(0,c)]
lemma add_spec (xs ys : num) : value (add xs ys) = value xs + value ys := by
  induction xs with
  | nil => simp [add,value]
  | cons ec xs ih =>
    rcases ec with ⟨e,c⟩
    change value (z0a e c (add xs ys)) = (c * pow2 e + value xs) + value ys
    rw [z0b,ih]; ring
lemma z0c (xs : num) : value (neg xs) = -value xs := by
  induction xs with
  | nil => simp [neg,value]
  | cons ec xs ih =>
    rcases ec with ⟨e,c⟩
    change -c * pow2 e + value (neg xs) = -(c * pow2 e + value xs)
    rw [ih]; ring
lemma sub_spec (xs ys : num) : value (sub xs ys) = value xs - value ys := by
  unfold sub; rw [add_spec,z0c]; ring
lemma shift_spec (n : Nat) (xs : num) : value (shift n xs) = pow2 n * value xs := by
  induction xs with
  | nil => simp [shift,value]
  | cons ec xs ih =>
    rcases ec with ⟨e,c⟩
    change c * pow2 (n + e) + value (shift n xs) = pow2 n * (c * pow2 e + value xs)
    rw [pow2_add,ih]; ring
lemma power_spec (n : Nat) : value (power n) = pow2 n := by
  simp [power,value]
lemma small_spec (c : Int) : value (small c) = c := by
  simp [small,value,pow2]
def z0d (xs ys : num) : Option Int := z08 (sub xs ys)
lemma compare_spec {xs ys : num} {s : Int} (h : z0d xs ys = some s) :
    cmp0 (value xs - value ys) = s := by
  have hs := z09 h
  rwa [sub_spec] at hs
def z0e : Nat -> num -> num
  | 0,xs => xs
  | _ + 1,[] => []
  | fuel + 1,(e,c) :: xs =>
    if c = 0 then z0e fuel xs
    else if c = 1 then (e,c) :: z0e fuel xs
    else if c = -1 then (e,c) :: z0e fuel xs
    else
      let q := c / 2
      let r := c - q * 2
      let ys := z0e fuel (z0a (e + 1) q xs)
      if r = 0 then ys else (e,r) :: ys
lemma z0f (fuel : Nat) (xs : num) : value (z0e fuel xs) = value xs := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    cases xs with
    | nil => rfl
    | cons ec xs =>
      rcases ec with ⟨e,c⟩
      simp only [z0e]
      split_ifs with hc0 hc1 hcm1 hr0
      · simp [value,hc0,ih]
      · simp [value,ih]
      · simp [value,ih]
      · rw [ih,z0b]
        have hp : pow2 (e + 1) = pow2 e * 2 := by rw [pow2_add]; rfl
        simp only [value,hp]
        have hq : (c / 2) * 2 = c := by omega
        calc (c / 2) * (pow2 e * 2) + value xs
          _ = ((c / 2) * 2) * pow2 e + value xs := by ring
          _ = c * pow2 e + value xs := by rw [hq]
      · simp only [value,ih,z0b]
        have hp : pow2 (e + 1) = pow2 e * 2 := by rw [pow2_add]; rfl
        rw [hp]; ring
def pack (xs : num) : num := z0e 128 xs
lemma pack_spec (xs : num) : value (pack xs) = value xs := z0f 128 xs
def eqb (xs ys : num) : Bool := z0d xs ys == some 0
def leb (xs ys : num) : Bool := (z0d xs ys == some (-1)) || (z0d xs ys == some 0)
lemma eqb_spec {xs ys : num} (h : eqb xs ys = true) : value xs = value ys := by
  unfold eqb at h
  rw [beq_iff_eq] at h
  have hcmp := compare_spec h
  unfold cmp0 at hcmp
  split_ifs at hcmp <;> omega
lemma leb_spec {xs ys : num} (h : leb xs ys = true) : value xs <= value ys := by
  unfold leb at h
  rw [Bool.or_eq_true,beq_iff_eq,beq_iff_eq] at h
  rcases h with h | h
  · have hcmp := compare_spec h
    unfold cmp0 at hcmp
    split_ifs at hcmp <;> omega
  · have hcmp := compare_spec h
    unfold cmp0 at hcmp
    split_ifs at hcmp <;> omega
def z0g (n : Nat) : num -> Bool -> num
  | [],negative => if negative then small (-1) else []
  | (e,c) :: xs,negative =>
    if e < n then z0g n xs (decide (c < 0))
    else add (if negative then small (-1) else [])
      (((e,c) :: xs).map (fun ec => (ec.1 - n,ec.2)))
def z0h (n : Nat) (xs : num) : num := pack (z0g n (pack xs) false)
def nonnegative (xs : num) : Bool := leb [] xs
def split (xs : num) : Option (Nat × num) :=
  let ys := pack xs
  match ys with
  | [] => none
  | (e,_) :: _ =>
    let u := z0h (e + 1) ys
    if nonnegative u then
      if eqb xs (shift e (add (shift 1 u) (small 1))) then some (e,u) else none
    else none
lemma split_spec {xs : num} {e : Nat} {u : num} (h : split xs = some (e,u)) :
    0 <= value u /\ value xs = pow2 e * (value u * 2 + 1) := by
  unfold split nonnegative at h
  cases hp : pack xs with
  | nil => rw [hp] at h; contradiction
  | cons ec ys =>
    rcases ec with ⟨i,c⟩
    rw [hp] at h
    dsimp only at h
    split_ifs at h with hn heq
    injection h with hpair
    injection hpair with hi hu
    subst hi hu
    have hnu := leb_spec hn
    have hval := eqb_spec heq
    rw [shift_spec,add_spec,shift_spec,small_spec] at hval
    have hp1 : pow2 1 = 2 := rfl
    rw [hp1] at hval
    simp only [value] at hnu
    exact ⟨hnu,by linarith⟩
def half (xs : num) : Option (Bool × num) :=
  let u := z0h 1 xs
  if nonnegative u then
    if eqb xs (shift 1 u) then some (false,u)
    else if eqb xs (add (shift 1 u) (small 1)) then some (true,u)
    else none
  else none
lemma half_spec {xs : num} {odd : Bool} {u : num} (h : half xs = some (odd,u)) :
    0 <= value u /\ value xs = value u * 2 + (if odd then 1 else 0) := by
  unfold half nonnegative at h
  dsimp only at h
  split_ifs at h with hn he0 he1
  · injection h with hpair
    injection hpair with hodd hu
    cases hodd
    cases hu
    have hnu := leb_spec hn
    have hval := eqb_spec he0
    rw [shift_spec] at hval
    have hp1 : pow2 1 = 2 := rfl
    rw [hp1] at hval
    simp only [value] at hnu
    refine ⟨hnu,?_⟩
    simp only [Bool.false_eq_true,↓reduceIte]
    linarith
  · injection h with hpair
    injection hpair with hodd hu
    cases hodd
    cases hu
    have hnu := leb_spec hn
    have hval := eqb_spec he1
    rw [add_spec,shift_spec,small_spec] at hval
    have hp1 : pow2 1 = 2 := rfl
    rw [hp1] at hval
    simp only [value] at hnu
    refine ⟨hnu,?_⟩
    simp only [↓reduceIte]
    linarith
end Sparse
namespace Forward13
open Sparse
inductive Phase where
  | L | R | T1 | T2 | A
deriving DecidableEq
structure State where
  tag : Phase
  width : Nat
  budget : num
  mark : Nat
  low : num
  high : num
def ordinary (p : Phase) (w : Nat) (k m : num) : State :=
  ⟨p,w,k,0,[],m⟩
def plus (x y : num) : num := pack (add x y)
def minus (x y : num) : num := pack (sub x y)
def one : num := small 1
def twice (x : num) : num := shift 1 x
def full (w : Nat) : num := minus (power w) one
def iszero (x : num) : Bool := eqb x []
def lt (x y : num) : Bool := z0d x y == some (-1)
def good (x : State) : Bool :=
  if 0 < x.width then
  if nonnegative x.budget then
  if lt x.budget (power x.width) then
  if nonnegative x.high then
    match x.tag with
    | .L => lt (plus x.budget x.high) (power (x.width + 1))
    | .R => lt (plus (plus x.budget x.high) one) (power (x.width + 1))
    | .A => leb x.high x.budget
    | .T1 | .T2 =>
      if nonnegative x.low then
      if lt x.low (power (x.mark + 1)) then
        leb (plus x.low x.high) x.budget
      else false else false
  else false else false else false else false
inductive Result where
  | next (x : State)
  | halted
  | stuck
def prefix_step (p : Phase) (w : Nat) (k m : num) (whole : Nat) (bit : Int) : Result :=
  if iszero m then .next (ordinary .R w k (small bit))
  else match split m with
  | some (i,u) =>
    let h := i + whole
    .next ⟨p,w,k,h,minus (full (h + 1)) (small bit),u⟩
  | none => .stuck
def step_state (x : State) : Result :=
  let w := x.width
  let k := x.budget
  let m := x.high
  match x.tag with
  | .R => .next (ordinary .L w [] (plus (plus k m) one))
  | .L =>
    let m := plus k m
    if eqb m (power w) then
      let a := (w - 1) / 4
      let e := (w - 1) % 4
      if e = 0 then
        let j := w + 3 * a + 2
        .next (ordinary .L j [] (plus (power j) one))
      else if e = 1 then
        .next (ordinary .L (w + 3 * a + 3) [] (shift (3 * a + 1) (plus (power (w + 1)) one)))
      else if e = 2 then
        let j := w + 3 * a + 4
        .next (ordinary .L j [] (power j))
      else
        .next (ordinary .L (w + 3 * a + 4) [] (plus (shift (3 * a + 2) (plus (power (w + 1)) one)) one))
    else match half m with
    | some (true,u) => prefix_step .T1 (w + 1) (full (w + 1)) u 0 0
    | some (false,u) => prefix_step .T2 w (full w) u 1 1
    | none => .stuck
  | .A =>
    match half m with
    | some (true,_) => .halted
    | some (false,u) => prefix_step .T2 w k u 0 0
    | none => .stuck
  | .T1 =>
    let a := x.mark / 4
    let e := x.mark % 4
    let b := minus k x.low
    if x.mark = 0 then
      match half m with
      | some (true,_) =>
        match split (plus m one) with
        | some (t,u) =>
          if 0 < t then .next ⟨.T1,w + t,full (w + t),0,one,twice u⟩
          else .stuck
        | none => .stuck
      | some (false,_) => prefix_step .T1 (w + 1) (full (w + 1)) m 0 0
      | none => .stuck
    else
      if e = 0 then prefix_step .T1 (w + 3 * a + 1) (full (w + 3 * a + 1)) m 0 0
      else if e = 1 then
        .next (ordinary .R (w + 3 * a + 1) (minus (shift (3 * a) (plus (twice b) one)) one) (plus (twice m) one))
      else if e = 2 then
        .next (ordinary .R (w + 3 * a + 2) (full (w + 3 * a + 2)) (plus (twice m) one))
      else
        prefix_step .T1 (w + 3 * a + 3) (minus (shift (3 * a + 2) (plus (twice b) one)) one) m 0 0
  | .T2 =>
    let a := x.mark / 4
    let e := x.mark % 4
    let b := minus k x.low
    if e = 0 then prefix_step .T1 (w + 3 * a + 1) (shift (3 * a) (plus (twice b) one)) m 0 0
    else if e = 1 then prefix_step .T1 (w + 3 * a + 2) (full (w + 3 * a + 2)) m 0 1
    else if e = 2 then .next (ordinary .A (w + 3 * a + 3) (minus (shift (3 * a + 2) (plus (twice b) one)) one) m)
    else .next (ordinary .A (w + 3 * a + 4) (full (w + 3 * a + 4)) m)
def check : Nat -> State -> Bool
  | 0,_ => false
  | fuel + 1,x =>
    if good x then
      match step_state x with
      | .next y => check fuel y
      | .halted => true
      | .stuck => false
    else false
def seed : State := ordinary .L 3 [] (pack (small 9))
theorem numerical_halt : check 175 seed = true := by decide
end Forward13
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] lemma z0i : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : zB).head = 0 := rfl
@[simp] lemma zDt : (default : zB).tail = default := rfl
@[simp] lemma append_nil (s : zB) : ([] : zF) +> s = s := rfl
@[simp] lemma append_cons (a : Fin 2) (l : zF) (s : zB) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] lemma append_assoc (l₁ l₂ : zF) (s : zB) :
    (l₁ ++ l₂) +> s = l₁ +> (l₂ +> s) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [ih]
@[simp] lemma zPz (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma z0j (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
lemma z0k (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [z0j,Nat.succ_add,ih,List.append_assoc]
lemma z0l (l : List α) (n : Nat) : l ^ n ++ l = l ^ (n + 1) := by
  induction n with
  | zero => simp [z0j]
  | succ n ih => simp [z0j,List.append_assoc,ih]
lemma z0m (a b : List α) (n : Nat) : (a ++ b) ^ n ++ a = a ++ (b ++ a) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [z0j,List.append_assoc,ih,z0j]
    simp only [List.append_assoc]
lemma z0n (a b : zF) (i : Nat) (s : zB) :
    a +> ((b ++ a) ^ i) +> (b +> s) = ((a ++ b) ^ (i + 1)) +> s := by
  rw [<- append_assoc,<- append_assoc,<- z0m,List.append_assoc,z0l]
def z0o (d0 d1 : zF) : Nat -> Nat -> zB -> zB
  | 0,_,r => r
  | len + 1,n,r => (if n % 2 = 0 then d1 else d0) +> z0o d0 d1 len (n / 2) r
def z0p (d0 d1 dw : zF) (len n : Nat) (r : zB) : zB :=
  (if n % 2 = 0 then d1 else d0) +> z0o (dw ++ d0) (dw ++ d1) len (n / 2) r
def z0q (d0 d1 : zF) : Nat -> zB
  | 0 => default
  | n + 1 =>
    let m := n + 1
    (if m % 2 = 0 then d0 else d1) +> z0q d0 d1 (m / 2)
lemma z0r (d0 d1 : zF) (n : Nat) (r : zB) :
    z0o d0 d1 0 n r = r := rfl
lemma z0s (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0o d0 d1 (len + 1) (n * 2) r = d1 +> z0o d0 d1 len n r := by
  simp only [z0o]
  have h1 : (n * 2) % 2 = 0 := by omega
  have h2 : (n * 2) / 2 = n := by omega
  simp [h1,h2]
lemma z0t (d0 d1 : zF) (len n : Nat) (r : zB) :
    z0o d0 d1 (len + 1) (n * 2 + 1) r = d0 +> z0o d0 d1 len n r := by
  simp only [z0o]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1,h2]
lemma z0u (d0 d1 : zF) (len : Nat) (r : zB) :
    z0o d0 d1 len 0 r = (d1 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have h := z0s d0 d1 len 0 r
    simp only [Nat.zero_mul] at h
    rw [h,ih,z0j,append_assoc]
lemma z0v (n : Nat) : 0 < 2 ^ n := Nat.two_pow_pos n
lemma z0w (d0 d1 : zF) (len : Nat) (r : zB) :
    z0o d0 d1 len (2 ^ len - 1) r = (d0 ^ len) +> r := by
  induction len with
  | zero => rfl
  | succ len ih =>
    have hp := z0v len
    have h1 : 2 ^ (len + 1) - 1 = (2 ^ len - 1) * 2 + 1 := by
      rw [Nat.pow_succ]; omega
    rw [h1,z0t,ih,z0j,append_assoc]
lemma z0x (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0o d0 d1 (len + i) (n * 2 ^ i) r = (d1 ^ i) +> z0o d0 d1 len n r := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : len + (i + 1) = (len + i) + 1 := by omega
    have h2 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ]; ring
    rw [h1,h2,z0s,ih,z0j,append_assoc]
lemma z0y (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0o d0 d1 (len + 1 + i) ((n * 2 + 1) * 2 ^ i - 1) r =
    (d0 ^ i) +> d1 +> z0o d0 d1 len n r := by
  induction i with
  | zero =>
    have h1 : (n * 2 + 1) * 2 ^ 0 - 1 = n * 2 := by simp
    simp [h1,z0s]
  | succ i ih =>
    have hp := z0v i
    have hpos : 1 <= (n * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : len + 1 + (i + 1) = (len + 1 + i) + 1 := by omega
    have h2 : (n * 2 + 1) * 2 ^ (i + 1) - 1 = ((n * 2 + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ]
      have : (n * 2 + 1) * (2 ^ i * 2) = ((n * 2 + 1) * 2 ^ i) * 2 := by ring
      (try omega)
    rw [h1,h2,z0t,ih,z0j,append_assoc]
lemma z0y' (d0 d1 : zF) (len n i : Nat) (r : zB) :
    z0o d0 d1 (len + i) ((n + 1) * 2 ^ i - 1) r =
    (d0 ^ i) +> z0o d0 d1 len n r := by
  induction i with
  | zero =>
    have h1 : (n + 1) * 2 ^ 0 - 1 = n := by omega
    simp [h1]
  | succ i ih =>
    have hp := z0v i
    have hpos : 1 <= (n + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : len + (i + 1) = (len + i) + 1 := by omega
    have h2 : (n + 1) * 2 ^ (i + 1) - 1 = ((n + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ]
      have : (n + 1) * (2 ^ i * 2) = ((n + 1) * 2 ^ i) * 2 := by ring
      (try omega)
    rw [h1,h2,z0t,ih,z0j,append_assoc]
lemma z0z (d0 d1 dw : zF) (len n : Nat) (r : zB) :
    z0p d0 d1 dw len (n * 2) r = d1 +> z0o (dw ++ d0) (dw ++ d1) len n r := by
  unfold z0p
  have h1 : (n * 2) % 2 = 0 := by omega
  have h2 : (n * 2) / 2 = n := by omega
  simp [h1,h2]
lemma z0A (d0 d1 dw : zF) (len n : Nat) (r : zB) :
    z0p d0 d1 dw len (n * 2 + 1) r = d0 +> z0o (dw ++ d0) (dw ++ d1) len n r := by
  unfold z0p
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1,h2]
lemma z0B (d0 d1 dw : zF) (len : Nat) (r : zB) :
    z0p d0 d1 dw len 0 r = ((d1 ++ dw) ^ len) +> d1 +> r := by
  have h := z0z d0 d1 dw len 0 r
  simp only [Nat.zero_mul] at h
  rw [h,z0u,<- append_assoc,<- z0m,append_assoc]
lemma z0C (d0 d1 dw : zF) (len : Nat) (r : zB) :
    z0p d0 d1 dw len (2 ^ (len + 1) - 1) r = ((d0 ++ dw) ^ len) +> d0 +> r := by
  have hp := z0v len
  have h1 : 2 ^ (len + 1) - 1 = (2 ^ len - 1) * 2 + 1 := by rw [Nat.pow_succ]; omega
  rw [h1,z0A,z0w,<- append_assoc,<- z0m,append_assoc]
lemma z0D (d0 d1 dw : zF) (len n i : Nat) (r : zB) :
    z0p d0 d1 dw (len + i) ((n * 2 + 1) * 2 ^ i - 1) r =
    ((d0 ++ dw) ^ i) +> d1 +> z0o (dw ++ d0) (dw ++ d1) len n r := by
  cases i with
  | zero =>
    have h1 : (n * 2 + 1) * 2 ^ 0 - 1 = n * 2 := by simp
    simp [h1,z0z]
  | succ i =>
    have hp := z0v i
    have hpos : 1 <= (n * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : len + (i + 1) = len + 1 + i := by omega
    have h2 : (n * 2 + 1) * 2 ^ (i + 1) - 1 = ((n * 2 + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ]
      have : (n * 2 + 1) * (2 ^ i * 2) = ((n * 2 + 1) * 2 ^ i) * 2 := by ring
      (try omega)
    rw [h2,z0A,h1,z0y]
    rw [append_assoc dw d1,z0n]
lemma z0E (d0 d1 dw : zF) (len n i : Nat) (r : zB) :
    z0p d0 d1 dw (len + i) ((n * 2 + 1) * 2 ^ i) r =
    ((d1 ++ dw) ^ i) +> d0 +> z0o (dw ++ d0) (dw ++ d1) len n r := by
  cases i with
  | zero =>
    simp [z0A]
  | succ i =>
    have h1 : len + (i + 1) = (len + 1) + i := by omega
    have h2 : (n * 2 + 1) * 2 ^ (i + 1) = ((n * 2 + 1) * 2 ^ i) * 2 := by rw [Nat.pow_succ]; ring
    rw [h2,z0z,h1,z0x,z0t]
    rw [append_assoc dw d0,z0n]
lemma z0F (d0 d1 : zF) : z0q d0 d1 0 = default := by simp [z0q]
lemma z0G (d0 d1 : zF) : z0q d0 d1 1 = d1 +> default := by simp [z0q]
lemma z0H {d0 d1 : zF} (hd0 : d0 +> default = default) (n : Nat) :
    z0q d0 d1 (n * 2) = d0 +> z0q d0 d1 n := by
  cases n with
  | zero => simp [z0q,hd0]
  | succ k =>
    conv_lhs =>
      rw [show (k + 1) * 2 = (k * 2 + 1) + 1 by omega]
      unfold z0q
    simp only [show (k * 2 + 1 + 1) % 2 = 0 by omega,show (k * 2 + 1 + 1) / 2 = k + 1 by omega,↓reduceIte]
lemma z0I (d0 d1 : zF) (n : Nat) :
    z0q d0 d1 (n * 2 + 1) = d1 +> z0q d0 d1 n := by
  simp only [z0q]
  have h1 : (n * 2 + 1) % 2 = 1 := by omega
  have h2 : (n * 2 + 1) / 2 = n := by omega
  simp [h1,h2]
lemma z0J {d0 d1 : zF} (hd0 : d0 +> default = default) (n i : Nat) :
    z0q d0 d1 (n * 2 ^ i) = (d0 ^ i) +> z0q d0 d1 n := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 : n * 2 ^ (i + 1) = (n * 2 ^ i) * 2 := by rw [Nat.pow_succ]; ring
    rw [h1,z0H hd0,ih,z0j,append_assoc]
lemma z0K {d0 d1 : zF} (hd0 : d0 +> default = default) (i : Nat) :
    z0q d0 d1 (2 ^ i) = (d0 ^ i) +> d1 +> default := by
  have h1 : 2 ^ i = 1 * 2 ^ i := by omega
  rw [h1,z0J hd0,z0G]
lemma z0L {d0 d1 : zF} (hd0 : d0 +> default = default) (n i : Nat) :
    z0q d0 d1 ((n * 2 + 1) * 2 ^ i - 1) = (d1 ^ i) +> d0 +> z0q d0 d1 n := by
  induction i with
  | zero =>
    have h1 : (n * 2 + 1) * 2 ^ 0 - 1 = n * 2 := by simp
    simp [h1,z0H hd0]
  | succ i ih =>
    have hp := z0v i
    have hpos : 1 <= (n * 2 + 1) * 2 ^ i := Nat.mul_pos (by omega) hp
    have h1 : (n * 2 + 1) * 2 ^ (i + 1) - 1 = ((n * 2 + 1) * 2 ^ i - 1) * 2 + 1 := by
      rw [Nat.pow_succ]
      have : (n * 2 + 1) * (2 ^ i * 2) = ((n * 2 + 1) * 2 ^ i) * 2 := by ring
      (try omega)
    rw [h1,z0I,ih,z0j,append_assoc]
lemma z0M (d0 d1 : zF) (len n : Nat) (r : zB)
    (h : 1 + n < 2 ^ len) :
    ∃ (i : Nat) (s : zB),
      z0o d0 d1 len (1 + n) r = (d1 ^ i) +> d0 +> s /\
      z0o d0 d1 len n r = (d0 ^ i) +> d1 +> s := by
  induction len generalizing n with
  | zero => simp at h
  | succ len ih =>
    have hp : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0,z0o d0 d1 len k r,?_,?_⟩
      · rw [h_odd,z0t]; rfl
      · rw [h_even,z0s]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : 1 + k < 2 ^ len := by omega
      rcases ih k h_lt with ⟨i,s,hi1,hi0⟩
      refine ⟨i + 1,s,?_,?_⟩
      · rw [h_even,z0s,hi1,z0j,append_assoc]
      · rw [h_odd,z0t,hi0,z0j,append_assoc]
lemma z0N (d0 d1 dw : zF) (len n : Nat) (r : zB)
    (h : 1 + n < 2 ^ (len + 1)) :
    ∃ (i : Nat) (s : zB),
      z0p d0 d1 dw len (1 + n) r = ((d1 ++ dw) ^ i) +> d0 +> s /\
      z0p d0 d1 dw len n r = ((d0 ++ dw) ^ i) +> d1 +> s := by
  have hp : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
  let k := n / 2
  rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
  · have h_even : n = k * 2 := by omega
    have h_odd : 1 + n = k * 2 + 1 := by omega
    refine ⟨0,z0o (dw ++ d0) (dw ++ d1) len k r,?_,?_⟩
    · rw [h_odd,z0A]; rfl
    · rw [h_even,z0z]; rfl
  · have h_odd : n = k * 2 + 1 := by omega
    have h_even : 1 + n = (1 + k) * 2 := by omega
    have h_lt : 1 + k < 2 ^ len := by omega
    rcases z0M (dw ++ d0) (dw ++ d1) len k r h_lt with ⟨i,s,hi1,hi0⟩
    refine ⟨i + 1,s,?_,?_⟩
    · rw [h_even,z0z,hi1,append_assoc dw d0,z0n]
    · rw [h_odd,z0A,hi0,append_assoc dw d1,z0n]
lemma z0O {d0 d1 : zF} (hd0 : d0 +> default = default) (n : Nat) :
    ∃ (i : Nat) (s : zB),
      z0q d0 d1 n = (d1 ^ i) +> d0 +> s /\
      z0q d0 d1 (1 + n) = (d0 ^ i) +> d1 +> s := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    let k := n / 2
    rcases Nat.mod_two_eq_zero_or_one n with hn0 | hn1
    · have h_even : n = k * 2 := by omega
      have h_odd : 1 + n = k * 2 + 1 := by omega
      refine ⟨0,z0q d0 d1 k,?_,?_⟩
      · rw [h_even,z0H hd0]; rfl
      · rw [h_odd,z0I]; rfl
    · have h_odd : n = k * 2 + 1 := by omega
      have h_even : 1 + n = (1 + k) * 2 := by omega
      have h_lt : k < n := by omega
      rcases ih k h_lt with ⟨i,s,hi0,hi1⟩
      refine ⟨i + 1,s,?_,?_⟩
      · rw [h_odd,z0I,hi0,z0j,append_assoc]
      · rw [h_even,z0H hd0,hi1,z0j,append_assoc]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma z0P {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1,zSm tm c_1 c_2 h⟩
lemma z0Q {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1,by decide,zSm tm c_1 c_2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,zMs,ih,Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa,h₁]; simp [h₂]
lemma zSt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,_,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n,_,hn⟩ := h; exact ⟨n,hn⟩
lemma z0R {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,n_pos,hn⟩ := h₁; obtain ⟨m,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z0S {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n,hn⟩ := h₁; obtain ⟨m,m_pos,hm⟩ := h₂
  exact ⟨n + m,lt_of_lt_of_le m_pos (Nat.le_add_left m n),zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma z0T {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  z0R (z0Q tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step_tm" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z0T (by (try simp only [Turing.ListBlank.head_cons,zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,z0i,zDh,zDt])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
abbrev ld0 : zF := [0,1,1,1]
abbrev ld1 : zF := [1,1,1,1]
abbrev ldh : zB := [1] +> default
abbrev rd0 : zF := [0,0,0]
abbrev rd1 : zF := [1,0,0]
def z0U (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  l <{{E}} ([0,1,0,1,0] +> r)
def z0V (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  ([1,0,1,1,1] +> l) {{B}}> r
def z0W (l r : zB) : Cfg (Fin 2) (Fin 6) :=
  (ld0 +> l) {{F}}> r
lemma z0X (n : Nat) (r : zB) :
    [1,0] +> (([1,0,1,0] ^ n) +> r) = ([1,0,1,0] ^ n) +> ([1,0] +> r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [z0j,append_assoc,append_assoc,<- ih]
    rfl
lemma z0Y (n : Nat) (r : zB) :
    (rd0 ^ n) +> ([0] +> r) = [0] +> ((rd0 ^ n) +> r) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [z0j,append_assoc,append_assoc,ih]
    rfl
lemma z0Z (n : Nat) (l r : zB) :
    (l {{B}}> ((rd1 ^ n) +> r)) [target_tm]⊢* ((([1,1,1] ^ n) +> l) {{B}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z0j,append_assoc]
    have h1 : (l {{B}}> (rd1 +> (rd1 ^ n) +> r)) [target_tm]⊢*
        (([1,1,1] +> l) {{B}}> ((rd1 ^ n) +> r)) := by
      dsimp [rd1,ListBlank.append]; execute
    have h2 := ih ([1,1,1] +> l) r
    rw [<- append_assoc ([1,1,1] ^ n) [1,1,1] l,z0l] at h2
    exact zSt h1 h2
lemma z10 (n : Nat) (l r : zB) :
    ((([1,1,1] ^ n) +> l) <{{C}} r) [target_tm]⊢* (l <{{C}} ((rd0 ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z0j,append_assoc]
    have h1 : (([1,1,1] +> ([1,1,1] ^ n) +> l) <{{C}} r) [target_tm]⊢*
        ((([1,1,1] ^ n) +> l) <{{C}} (rd0 +> r)) := by
      dsimp [rd0,ListBlank.append]; execute
    have h2 := ih l (rd0 +> r)
    rw [<- append_assoc (rd0 ^ n) rd0 r,z0l] at h2
    exact zSt h1 h2
lemma z11 (n : Nat) (l r : zB) :
    (((ld1 ^ n) +> l) <{{E}} ([0,1,0,1,0] +> r)) [target_tm]⊢*
    (l <{{E}} ([0,1,0,1,0] +> ([1,0,1,0] ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z0j,append_assoc]
    have h1 : ((ld1 +> (ld1 ^ n) +> l) <{{E}} ([0,1,0,1,0] +> r)) [target_tm]⊢*
        (((ld1 ^ n) +> l) <{{E}} ([0,1,0,1,0] +> [1,0,1,0] +> r)) := by
      dsimp [ld1,ListBlank.append]; execute
    have h2 := ih l ([1,0,1,0] +> r)
    rw [<- append_assoc ([1,0,1,0] ^ n) [1,0,1,0] r,z0l] at h2
    exact zSt h1 h2
lemma z12 (n : Nat) (l r : zB) :
    (((ld1 ^ n) +> l) <{{D}} ([1,0] +> r)) [target_tm]⊢*
    (l <{{D}} ([1,0] +> ([1,0,1,0] ^ n) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z0j,append_assoc]
    have h1 : ((ld1 +> (ld1 ^ n) +> l) <{{D}} ([1,0] +> r)) [target_tm]⊢*
        (((ld1 ^ n) +> l) <{{D}} ([1,0] +> [1,0,1,0] +> r)) := by
      dsimp [ld1,ListBlank.append]; execute
    have h2 := ih l ([1,0,1,0] +> r)
    rw [<- append_assoc ([1,0,1,0] ^ n) [1,0,1,0] r,z0l] at h2
    exact zSt h1 h2
lemma z13 (n : Nat) (l r : zB) :
    (([1,0,1,1,1] +> l) {{B}}> (([1,0,1,0] ^ n) +> r)) [target_tm]⊢*
    (([1,0,1,1,1] +> (ld0 ^ n) +> l) {{B}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [z0j,append_assoc]
    have h1 : (([1,0,1,1,1] +> l) {{B}}> ([1,0,1,0] +> ([1,0,1,0] ^ n) +> r)) [target_tm]⊢*
        (([1,0,1,1,1] +> ld0 +> l) {{B}}> (([1,0,1,0] ^ n) +> r)) := by
      dsimp [ld0,ListBlank.append]; execute
    have h2 := ih (ld0 +> l) r
    rw [<- append_assoc (ld0 ^ n) ld0 l,z0l] at h2
    exact zSt h1 h2
lemma z14 (n : Nat) (l r : zB) :
    (([1] +> l) {{B}}> ((rd1 ^ (n * 4)) +> r)) [target_tm]⊢*
    (([1] +> (ld1 ^ (n * 3)) +> l) {{B}}> r) := by
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h_mul4 : (n + 1) * 4 = 4 + n * 4 := by omega
    have h_mul3 : n * 3 + 3 = (n + 1) * 3 := by omega
    rw [h_mul4,z0k,append_assoc]
    have h1 : (([1] +> l) {{B}}> ((rd1 ^ 4) +> (rd1 ^ (n * 4)) +> r)) [target_tm]⊢*
        (([1] +> (ld1 ^ 3) +> l) {{B}}> ((rd1 ^ (n * 4)) +> r)) := by
      dsimp [rd1,ld1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
    have h2 := ih ((ld1 ^ 3) +> l) r
    rw [<- append_assoc (ld1 ^ (n * 3)) (ld1 ^ 3) l,<- z0k,h_mul3] at h2
    exact zSt h1 h2
lemma z15 (l r : zB) (n : Nat) :
    (z0U ((ld1 ^ n) +> ld0 +> l) r) [target_tm]⊢⁺
    (z0V ((ld0 ^ n) +> ld1 +> l) r) := by
  unfold z0U z0V
  have h1 := z11 n (ld0 +> l) r
  have h2 : ((ld0 +> l) <{{E}} ([0,1,0,1,0] +> ([1,0,1,0] ^ n) +> r)) [target_tm]⊢⁺
      (([1,0,1,1,1] +> ld1 +> l) {{B}}> (([1,0,1,0] ^ n) +> r)) := by
    dsimp [ld0,ld1,ListBlank.append]; execute
  have h3 := z13 n (ld1 +> l) r
  exact z0R (z0S h1 h2) h3
lemma z16 (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ n) +> [0] +> r)) [target_tm]⊢⁺
    (z0U l ((rd0 ^ n) +> [1] +> r)) := by
  unfold z0V z0U
  have h1 := z0Z n ([1,0,1,1,1] +> l) ([0] +> r)
  have h2 : ((([1,1,1] ^ n) +> [1,0,1,1,1] +> l) {{B}}> ([0] +> r)) [target_tm]⊢⁺
      ((([1,1,1] ^ n) +> [1,0,1,1,1] +> l) <{{C}} ([1] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h3 := z10 n ([1,0,1,1,1] +> l) ([1] +> r)
  have h4 : (([1,0,1,1,1] +> l) <{{C}} ((rd0 ^ n) +> [1] +> r)) [target_tm]⊢*
      (l <{{E}} ([0,1,0,1,0] +> (rd0 ^ n) +> [1] +> r)) := by
    dsimp [ListBlank.append]; execute
  exact z0R (z0R (z0S h1 h2) h3) h4
lemma z17 (r : zB) (n : Nat) :
    (z0U ((ld1 ^ n) +> ldh) (rd0 +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ n) +> ldh) (rd1 +> [0,0] +> r)) := by
  unfold z0U z0V
  have h1 := z11 n ldh (rd0 +> r)
  have h2 : (ldh <{{E}} ([0,1,0,1,0] +> ([1,0,1,0] ^ n) +> rd0 +> r)) [target_tm]⊢⁺
      (([1,0,1,1,1] +> ldh) {{B}}> ([1,0] +> ([1,0,1,0] ^ n) +> rd0 +> r)) := by
    dsimp [ldh,ListBlank.append]; execute
  rw [z0X] at h2
  have h3 := z13 n ldh ([1,0] +> rd0 +> r)
  exact z0R (z0S h1 h2) h3
lemma z18 (r : zB) (n : Nat) :
    (z0U ((ld1 ^ n) +> ldh) (rd1 +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (1 + n)) +> ldh) ([0] +> r)) := by
  unfold z0U z0V
  have h1 := z11 n ldh (rd1 +> r)
  have h2 : (ldh <{{E}} ([0,1,0,1,0] +> ([1,0,1,0] ^ n) +> rd1 +> r)) [target_tm]⊢⁺
      (([1,0,1,1,1] +> ldh) {{B}}> ([1,0] +> ([1,0,1,0] ^ n) +> rd1 +> r)) := by
    dsimp [ldh,ListBlank.append]; execute
  rw [z0X] at h2
  have h3 := z13 n ldh ([1,0] +> rd1 +> r)
  have h4 : (([1,0,1,1,1] +> (ld0 ^ n) +> ldh) {{B}}> ([1,0] +> rd1 +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> ld0 +> (ld0 ^ n) +> ldh) {{B}}> ([0] +> r)) := by
    dsimp [rd1,ld0,ListBlank.append]; execute
  rw [<- append_assoc ld0 (ld0 ^ n) ldh,<- z0j,Nat.add_comm] at h4
  exact z0R (z0R (z0S h1 h2) h3) h4
def z19 (l l' : zB) : Prop :=
  ∀ r,(l <{{D}} ([1,0,1,0,1,0] +> r)) [target_tm]⊢* (z0V l' ([1,0] +> r))
lemma z1a : z19 ldh ldh := by
  intro r
  unfold z0V
  dsimp [ldh,ListBlank.append]
  execute
lemma z1b {l l' : zB} (h : z19 l l') : z19 (ld0 +> l) (ld0 +> l') := by
  intro r
  have h1 : ((ld0 +> l) <{{D}} ([1,0,1,0,1,0] +> r)) [target_tm]⊢*
      (l <{{D}} ([1,0,1,0,1,0] +> [1,0,1,0] +> r)) := by
    dsimp [ld0,ListBlank.append]; execute
  have h2 := h ([1,0,1,0] +> r)
  unfold z0V at h2 ⊢
  have h3 : (([1,0,1,1,1] +> l') {{B}}> ([1,0] +> [1,0,1,0] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> ld0 +> l') {{B}}> ([1,0] +> r)) := by
    dsimp [ld0,ListBlank.append]; execute
  exact zSt (zSt h1 h2) h3
lemma z1c {l l' : zB} (h : z19 l l') : z19 (ld1 +> l) (ld0 +> l') := by
  intro r
  have h1 : ((ld1 +> l) <{{D}} ([1,0,1,0,1,0] +> r)) [target_tm]⊢*
      (l <{{D}} ([1,0,1,0,1,0] +> [1,0,1,0] +> r)) := by
    dsimp [ld1,ListBlank.append]; execute
  have h2 := h ([1,0,1,0] +> r)
  unfold z0V at h2 ⊢
  have h3 : (([1,0,1,1,1] +> l') {{B}}> ([1,0] +> [1,0,1,0] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> ld0 +> l') {{B}}> ([1,0] +> r)) := by
    dsimp [ld0,ListBlank.append]; execute
  exact zSt (zSt h1 h2) h3
lemma z1d {l l' : zB} (h : z19 l l') (k : Nat) (s : zB) :
    (((ld1 ^ k) +> ld0 +> l) <{{D}} ([1,0] +> s)) [target_tm]⊢*
    (z0V ((ld0 ^ k) +> l') ([1,0] +> s)) := by
  have h1 := z12 k (ld0 +> l) s
  have h2 : ((ld0 +> l) <{{D}} ([1,0] +> ([1,0,1,0] ^ k) +> s)) [target_tm]⊢*
      (l <{{D}} ([1,0,1,0,1,0] +> ([1,0,1,0] ^ k) +> s)) := by
    dsimp [ld0,ListBlank.append]; execute
  have h3 := h (([1,0,1,0] ^ k) +> s)
  unfold z0V at h3 ⊢
  rw [z0X] at h3
  have h4 := z13 k l' ([1,0] +> s)
  exact zSt (zSt (zSt h1 h2) h3) h4
lemma z1e (l r : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4)) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (n * 3 + 1)) +> l') ([0] +> r)) := by
  have h1 := z14 n (ld0 +> l) ([1,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ([1,1,0,0] +> r)) [target_tm]⊢⁺
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,0] +> r)) := by
    dsimp [ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,0] +> r)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,0] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> ld0 +> (ld0 ^ (n * 3)) +> l') {{B}}> ([0] +> r)) := by
    dsimp [ld0,ListBlank.append]; execute
  rw [<- append_assoc ld0 (ld0 ^ (n * 3)) l',<- z0j] at h4
  exact z0R (z0R (z0S h1 h2) h3) h4
lemma z1f (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4 + 1)) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (n * 3)) +> ld1 +> l) (rd1 +> r)) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 1) +> [1,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 1) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
      (z0U ((ld1 ^ (n * 3)) +> ld0 +> l) (rd1 +> r)) := by
    unfold z0U; dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z15 l (rd1 +> r) (n * 3)
  exact zPt (z0S h1 h2) h3
lemma z1g (l r : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4 + 2)) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (n * 3 + 2)) +> l') (rd1 +> r)) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 2) +> [1,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 2) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,1,0,1,0,1,0,0] +> r)) := by
    dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,1,0,1,0,1,0,0] +> r)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,1,0,1,0,1,0,0] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> (ld0 ^ 2) +> (ld0 ^ (n * 3)) +> l') {{B}}> (rd1 +> r)) := by
    dsimp [ld0,rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 2) (ld0 ^ (n * 3)) l',<- z0k,show 2 + n * 3 = n * 3 + 2 by omega] at h4
  exact z0R (z0R (z0S h1 h2) h3) h4
lemma z1h (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4 + 3)) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (n * 3 + 2)) +> ld1 +> l) ([0] +> r)) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 3) +> [1,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 3) +> [1,1,0,0] +> r)) [target_tm]⊢⁺
      (z0U ((ld1 ^ (n * 3)) +> ld0 +> l) ([1,0,1,0,1,0,1,0,0] +> r)) := by
    unfold z0U; dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z15 l ([1,0,1,0,1,0,1,0,0] +> r) (n * 3)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> ld1 +> l) {{B}}> ([1,0,1,0,1,0,1,0,0] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> (ld0 ^ 2) +> (ld0 ^ (n * 3)) +> ld1 +> l) {{B}}> ([0] +> r)) := by
    dsimp [ld0,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 2) (ld0 ^ (n * 3)) (ld1 +> l),<- z0k,show 2 + n * 3 = n * 3 + 2 by omega] at h4
  exact z0R (zPt (z0S h1 h2) h3) h4
lemma z1i (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4)) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld1 ^ (n * 3)) +> ld0 +> l) ([0] +> r)) := by
  have h1 := z14 n (ld0 +> l) ([1,0,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ([1,0,1,0,0] +> r)) [target_tm]⊢⁺
      (z0V ((ld1 ^ (n * 3)) +> ld0 +> l) ([0] +> r)) := by
    unfold z0V; dsimp [ListBlank.append]; execute
  exact z0S h1 h2
lemma z1j (l r : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4 + 1)) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
    (z0V ((ld0 ^ (n * 3 + 2)) +> l') ([1] +> r)) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 1) +> [1,0,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 1) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,1,0,1,0,1] +> r)) := by
    dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,1,0,1,0,1] +> r)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,1,0,1,0,1] +> r)) [target_tm]⊢*
      (([1,0,1,1,1] +> (ld0 ^ 2) +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1] +> r)) := by
    dsimp [ld0,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 2) (ld0 ^ (n * 3)) l',<- z0k,show 2 + n * 3 = n * 3 + 2 by omega] at h4
  exact z0R (z0R (z0S h1 h2) h3) h4
lemma z1k (l r : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4 + 2)) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
    (z0W ((ld0 ^ (n * 3 + 2)) +> ld1 +> l) r) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 2) +> [1,0,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 2) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
      (z0U ((ld1 ^ (n * 3)) +> ld0 +> l) ([1,0,1,0,1,0,1] +> r)) := by
    unfold z0U; dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z15 l ([1,0,1,0,1,0,1] +> r) (n * 3)
  unfold z0V at h3
  unfold z0W
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> ld1 +> l) {{B}}> ([1,0,1,0,1,0,1] +> r)) [target_tm]⊢*
      ((ld0 +> (ld0 ^ 2) +> (ld0 ^ (n * 3)) +> ld1 +> l) {{F}}> r) := by
    dsimp [ld0,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 2) (ld0 ^ (n * 3)) (ld1 +> l),<- z0k,show 2 + n * 3 = n * 3 + 2 by omega] at h4
  exact z0R (zPt (z0S h1 h2) h3) h4
lemma z1l (l r : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4 + 3)) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
    (z0W ((ld0 ^ (n * 3 + 4)) +> l') r) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 3) +> [1,0,1,0,0] +> r)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 3) +> [1,0,1,0,0] +> r)) [target_tm]⊢⁺
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,1,0,1,0,1,0,1,0,1,0,1] +> r)) := by
    dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,1,0,1,0,1,0,1,0,1,0,1] +> r)
  unfold z0V at h3
  unfold z0W
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,1,0,1,0,1,0,1,0,1,0,1] +> r)) [target_tm]⊢*
      ((ld0 +> (ld0 ^ 4) +> (ld0 ^ (n * 3)) +> l') {{F}}> r) := by
    dsimp [ld0,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 4) (ld0 ^ (n * 3)) l',<- z0k,show 4 + n * 3 = n * 3 + 4 by omega] at h4
  exact z0R (z0R (z0S h1 h2) h3) h4
lemma z1m (l r : zB) :
    (z0W l (rd0 +> r)) [target_tm]⊢⁺ (z0V l ([0,0] +> r)) := by
  unfold z0W z0V
  dsimp [ld0,rd0,ListBlank.append]
  execute
lemma z1n (l : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4)) +> [1,1,0,1] +> default)) [target_tm]⊢*
    (z0V ((ld0 ^ (n * 3 + 1)) +> l') (rd1 +> default)) := by
  have h1 := z14 n (ld0 +> l) ([1,1,0,1] +> default)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ([1,1,0,1] +> default)) [target_tm]⊢*
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,1,0] +> default)) := by
    dsimp [ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,1,0] +> default)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,1,0] +> default)) [target_tm]⊢*
      (([1,0,1,1,1] +> ld0 +> (ld0 ^ (n * 3)) +> l') {{B}}> (rd1 +> default)) := by
    dsimp [ld0,rd1,ListBlank.append]; execute
  rw [<- append_assoc ld0 (ld0 ^ (n * 3)) l',<- z0j] at h4
  exact zSt (zSt (zSt h1 h2) h3) h4
lemma z1o (l : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4 + 1)) +> [1,1,0,1] +> default)) [target_tm]⊢*
    (z0U ((ld1 ^ (n * 3 + 1)) +> ld0 +> l) default) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 1) +> [1,1,0,1] +> default)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 1) +> [1,1,0,1] +> default)) [target_tm]⊢*
      (z0U (ld1 +> (ld1 ^ (n * 3)) +> ld0 +> l) default) := by
    unfold z0U; dsimp [rd1,ld1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc ld1 (ld1 ^ (n * 3)) (ld0 +> l),<- z0j] at h2
  exact zSt h1 h2
lemma z1p (l : zB) (n : Nat) {l' : zB} (h : z19 l l') :
    (z0V l ((rd1 ^ (n * 4 + 2)) +> [1,1,0,1] +> default)) [target_tm]⊢*
    (z0V ((ld0 ^ (n * 3 + 3)) +> l') default) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 2) +> [1,1,0,1] +> default)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 2) +> [1,1,0,1] +> default)) [target_tm]⊢*
      (((ld1 ^ (n * 3)) +> ld0 +> l) <{{D}} ([1,0] +> [1,0,1,0,1,0,1,0,1,0] +> default)) := by
    dsimp [rd1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  have h3 := z1d h (n * 3) ([1,0,1,0,1,0,1,0,1,0] +> default)
  unfold z0V at h3 ⊢
  have h4 : (([1,0,1,1,1] +> (ld0 ^ (n * 3)) +> l') {{B}}> ([1,0] +> [1,0,1,0,1,0,1,0,1,0] +> default)) [target_tm]⊢*
      (([1,0,1,1,1] +> (ld0 ^ 3) +> (ld0 ^ (n * 3)) +> l') {{B}}> default) := by
    dsimp [ld0,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld0 ^ 3) (ld0 ^ (n * 3)) l',<- z0k,show 3 + n * 3 = n * 3 + 3 by omega] at h4
  exact zSt (zSt (zSt h1 h2) h3) h4
lemma z1q (l : zB) (n : Nat) :
    (z0V l ((rd1 ^ (n * 4 + 3)) +> [1,1,0,1] +> default)) [target_tm]⊢*
    (z0U ((ld1 ^ (n * 3 + 2)) +> ld0 +> l) (rd1 +> default)) := by
  rw [z0k,append_assoc]
  have h1 := z14 n (ld0 +> l) ((rd1 ^ 3) +> [1,1,0,1] +> default)
  have h2 : (([1] +> (ld1 ^ (n * 3)) +> ld0 +> l) {{B}}> ((rd1 ^ 3) +> [1,1,0,1] +> default)) [target_tm]⊢*
      (z0U ((ld1 ^ 2) +> (ld1 ^ (n * 3)) +> ld0 +> l) (rd1 +> default)) := by
    unfold z0U; dsimp [rd1,ld1,HPow.hPow,list_nat_repeat,ListBlank.append]; execute
  rw [<- append_assoc (ld1 ^ 2) (ld1 ^ (n * 3)) (ld0 +> l),<- z0k,show 2 + n * 3 = n * 3 + 2 by omega] at h2
  exact zSt h1 h2
lemma z1r : ((default) {{A}}> (default)) [target_tm]⊢* (([0,0,1,1,1,1] +> default) <{{D}} ([1,0,1,0,1] +> default)) := by execute
lemma z1s : (([0,0,1,1,1,1] +> default) <{{D}} ([1,0,1,0,1] +> default)) [target_tm]⊢* (([0,1,1,1,0,1,1,1,1] +> default) {{F}}> ([0,1,0,0,0,0,1] +> default)) := by execute
lemma z1t : (([0,1,1,1,0,1,1,1,1] +> default) {{F}}> ([0,1,0,0,0,0,1] +> default)) [target_tm]⊢* ((default) <{{D}} ([1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1] +> default)) := by execute
lemma z1u : ((default) <{{D}} ([1,0,1,0,1,0,1,0,1,0,1,0,0,1,0,1] +> default)) [target_tm]⊢* (([1,1,1,1,1,0,1,1,1,1] +> default) <{{E}} ([0,1,0,1,0,1,0,1] +> default)) := by execute
lemma z1v : (([1,1,1,1,1,0,1,1,1,1] +> default) <{{E}} ([0,1,0,1,0,1,0,1] +> default)) [target_tm]⊢* (([1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1] +> default) <{{C}} ([0,0,1] +> default)) := by execute
lemma z1w : (([1,1,0,1,1,1,0,1,1,1,0,1,1,1,0,1,1,1,1] +> default) <{{C}} ([0,0,1] +> default)) [target_tm]⊢* (([1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1] +> default) {{A}}> ([1,0,1,0,0,1] +> default)) := by execute
lemma z1x : (([1,1,1,0,1,1,1,1,1,1,1,0,1,1,1,1] +> default) {{A}}> ([1,0,1,0,0,1] +> default)) [target_tm]⊢* (([0,1,1,1,1,1,1,0,1,1,1,1] +> default) {{E}}> ([1,0,1,0,1,0,1,0,0,0,0,0,1] +> default)) := by execute
lemma z1y : (([0,1,1,1,1,1,1,0,1,1,1,1] +> default) {{E}}> ([1,0,1,0,1,0,1,0,0,0,0,0,1] +> default)) [target_tm]⊢* (([0,0,1,1,1,0,1,1,1,1,1,1,1,1] +> default) {{E}}> ([1,0,1,0,0,0,0,1,0,0,1] +> default)) := by execute
lemma z1z : (([0,0,1,1,1,0,1,1,1,1,1,1,1,1] +> default) {{E}}> ([1,0,1,0,0,0,0,1,0,0,1] +> default)) [target_tm]⊢* (([1,1,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1] +> default) {{B}}> ([1] +> default)) := by execute
lemma z1A : (([1,1,1,1,1,1,1,0,1,1,1,0,1,1,1,1,1,1,1,1,1,1,1,1] +> default) {{B}}> ([1] +> default)) [target_tm]⊢* (([1,1,1,1,1,1,1,1,1,1,1,1,1] +> default) <{{E}} ([0,1,0,1,0,1,0,0,0,0,0,0,0,0,1] +> default)) := by execute
lemma init_tm : (init []) [target_tm]⊢*
    (z0U ((ld1 ^ 3) +> ldh) ([1,0,0,0,0,0,0,0,0,1,0,0] +> default)) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = ((default) {{A}}> (default)) := rfl
  rw [h0]
  have h := zSt z1r (zSt z1s (zSt z1t
    (zSt z1u (zSt z1v (zSt z1w
    (zSt z1x (zSt z1y (zSt z1z z1A))))))))
  have hr : (([1,1,1,1,1,1,1,1,1,1,1,1,1] +> default) <{{E}} ([0,1,0,1,0,1,0,0,0,0,0,0,0,0,1] +> default)) =
      (z0U ((ld1 ^ 3) +> ldh) ([1,0,0,0,0,0,0,0,0,1,0,0] +> default)) := by
    unfold z0U ldh
    simp [ld1,HPow.hPow,list_nat_repeat]
  rwa [hr] at h
def LC (len k : Nat) : zB := z0o ld0 ld1 len k ldh
def RC (m : Nat) : zB := z0q rd0 rd1 m
def MC (h n : Nat) (r : zB) : zB := z0p [0] [1] [0,0] h n r
def RC1 (h n m : Nat) : zB := MC h n (rd1 +> RC m)
def RC2 (h n m : Nat) : zB := MC h n ([0] +> rd1 +> RC m)
def RC' (h n : Nat) : zB := MC h n ([1,0,1] +> default)
lemma z1B : rd0 +> default = default := by simp [rd0]
lemma z1C : [1] +> RC 0 = RC 1 := by
  simp [RC,z0F,z0G,rd1]
lemma z1D : [0,0] +> RC 0 = RC 0 := by
  simp [RC,z0F]
lemma z1E : [0] +> RC 0 = RC 0 := by
  simp [RC,z0F]
lemma z1F : [1,0,0,0,0] +> RC 0 = RC 1 := by
  simp [RC,z0F,z0G,rd1]
lemma z1G (len k : Nat) (h : k < 2 ^ len) : z19 (LC len k) (LC len (2 ^ len - 1)) := by
  unfold LC
  rw [z0w]
  induction len generalizing k with
  | zero =>
    have hk : k = 0 := by simp at h; omega
    subst hk
    rw [z0u]
    exact z1a
  | succ len ih =>
    have hp : 2 ^ (len + 1) = 2 ^ len * 2 := Nat.pow_succ 2 len
    rw [z0j,append_assoc]
    let q := k / 2
    rcases Nat.mod_two_eq_zero_or_one k with hk0 | hk1
    · have hk : k = q * 2 := by omega
      have hq : q < 2 ^ len := by omega
      rw [hk,z0s]
      exact z1c (ih q hq)
    · have hk : k = q * 2 + 1 := by omega
      have hq : q < 2 ^ len := by omega
      rw [hk,z0t]
      exact z1b (ih q hq)
lemma z1H (len k : Nat) (r : zB) (h : 1 + k < 2 ^ len) :
    (z0U (LC len (1 + k)) r) [target_tm]⊢⁺ (z0V (LC len k) r) := by
  unfold LC
  rcases z0M ld0 ld1 len k ldh h with ⟨i,s,hi1,hi0⟩
  rw [hi1,hi0]
  exact z15 s r i
lemma z1I (m : Nat) (l : zB) :
    (z0V l (RC m)) [target_tm]⊢⁺ (z0U l (RC (1 + m))) := by
  unfold RC
  rcases z0O z1B m with ⟨i,s,hi0,hi1⟩
  rw [hi0,hi1]
  have h1 : (rd1 ^ i) +> rd0 +> s = (rd1 ^ i) +> [0] +> ([0,0] +> s) := rfl
  have h2 : (rd0 ^ i) +> rd1 +> s = (rd0 ^ i) +> [1] +> ([0,0] +> s) := rfl
  rw [h1,h2]
  exact z16 l ([0,0] +> s) i
lemma z1J (h n : Nat) (l r : zB) (hn : 1 + n < 2 ^ (h + 1)) :
    (z0V l (MC h (1 + n) r)) [target_tm]⊢⁺ (z0U l (MC h n r)) := by
  unfold MC
  rcases z0N [0] [1] [0,0] h n r hn with ⟨i,s,hi1,hi0⟩
  rw [hi1,hi0]
  exact z16 l s i
lemma z1K (len m : Nat) :
    (z0U (LC len 0) (RC (m * 2 + 1))) [target_tm]⊢⁺
    (z0V (LC (len + 1) (2 ^ (len + 1) - 1)) ([0] +> RC m)) := by
  unfold LC RC
  rw [z0u,z0I,z0w,Nat.add_comm len 1]
  exact z18 (z0q rd0 rd1 m) len
lemma z1L (len m i : Nat) :
    (z0U (LC len 0) (RC ((m * 2 + 1) * 2 ^ (i + 1)))) [target_tm]⊢⁺
    (z0V (LC len (2 ^ len - 1)) (RC2 (i + 1) ((2 ^ (i + 1) - 1) * 2) m)) := by
  unfold LC RC2 MC RC
  rw [z0u,z0J z1B,z0I,z0w,z0z,z0w]
  rw [z0j rd0 i,append_assoc]
  have hr : [1] +> (rd0 ^ (i + 1)) +> [0] +> rd1 +> z0q rd0 rd1 m =
      rd1 +> [0,0] +> (rd0 ^ i) +> rd1 +> z0q rd0 rd1 m := by
    rw [z0Y (i + 1),z0j rd0 i,append_assoc]
    rfl
  change (z0U ((ld1 ^ len) +> ldh) (rd0 +> (rd0 ^ i) +> rd1 +> z0q rd0 rd1 m)) [target_tm]⊢⁺
    (z0V ((ld0 ^ len) +> ldh) ([1] +> (rd0 ^ (i + 1)) +> [0] +> rd1 +> z0q rd0 rd1 m))
  rw [hr]
  exact z17 ((rd0 ^ i) +> rd1 +> z0q rd0 rd1 m) len
lemma z1M (h m : Nat) : RC1 h 0 m = (rd1 ^ h) +> [1,1,0,0] +> RC m := by
  unfold RC1 MC; rw [z0B]; rfl
lemma z1N (h m : Nat) : RC2 h 0 m = (rd1 ^ h) +> [1,0,1,0,0] +> RC m := by
  unfold RC2 MC; rw [z0B]; rfl
lemma z1O (h : Nat) : RC' h 0 = (rd1 ^ h) +> [1,1,0,1] +> default := by
  unfold RC' MC; rw [z0B]; rfl
lemma z1P (len d : Nat) :
    LC (len + d) (2 ^ (len + d) - 1) = (ld0 ^ d) +> LC len (2 ^ len - 1) := by
  unfold LC
  rw [z0w,z0w,Nat.add_comm len d,z0k,append_assoc]
lemma z1Q (len k d : Nat) :
    LC (len + 1 + d) ((k * 2 + 1) * 2 ^ d - 1) = (ld0 ^ d) +> ld1 +> LC len k := by
  unfold LC; rw [z0y]
lemma z1R (len k d : Nat) :
    LC (len + 1 + d) ((k * 2 + 1) * 2 ^ d) = (ld1 ^ d) +> ld0 +> LC len k := by
  unfold LC; rw [z0x,z0t]
lemma z1S (len k a m : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC1 (a * 4) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + (a * 3 + 1)) (2 ^ (len + (a * 3 + 1)) - 1)) ([0] +> RC m)) := by
  rw [z1M,z1P]
  exact z1e (LC len k) (RC m) a (z1G len k hk)
lemma z1T (len k a m : Nat) :
    (z0V (LC len k) (RC1 (a * 4 + 1) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + 1 + a * 3) ((k * 2 + 1) * 2 ^ (a * 3) - 1)) (RC (m * 2 + 1))) := by
  have hr : RC (m * 2 + 1) = rd1 +> RC m := by unfold RC; rw [z0I]
  rw [z1M,z1Q,hr]
  exact z1f (LC len k) (RC m) a
lemma z1U (len k a m : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC1 (a * 4 + 2) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + (a * 3 + 2)) (2 ^ (len + (a * 3 + 2)) - 1)) (RC (m * 2 + 1))) := by
  have hr : RC (m * 2 + 1) = rd1 +> RC m := by unfold RC; rw [z0I]
  rw [z1M,z1P,hr]
  exact z1g (LC len k) (RC m) a (z1G len k hk)
lemma z1V (len k a m : Nat) :
    (z0V (LC len k) (RC1 (a * 4 + 3) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + 1 + (a * 3 + 2)) ((k * 2 + 1) * 2 ^ (a * 3 + 2) - 1)) ([0] +> RC m)) := by
  rw [z1M,z1Q]
  exact z1h (LC len k) (RC m) a
lemma z1W (len k a m : Nat) :
    (z0V (LC len k) (RC2 (a * 4) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + 1 + a * 3) ((k * 2 + 1) * 2 ^ (a * 3))) ([0] +> RC m)) := by
  rw [z1N,z1R]
  exact z1i (LC len k) (RC m) a
lemma z1X (len k a m : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC2 (a * 4 + 1) 0 m)) [target_tm]⊢⁺
    (z0V (LC (len + (a * 3 + 2)) (2 ^ (len + (a * 3 + 2)) - 1)) ([1] +> RC m)) := by
  rw [z1N,z1P]
  exact z1j (LC len k) (RC m) a (z1G len k hk)
lemma z1Y (len k a m : Nat) :
    (z0V (LC len k) (RC2 (a * 4 + 2) 0 m)) [target_tm]⊢⁺
    (z0W (LC (len + 1 + (a * 3 + 2)) ((k * 2 + 1) * 2 ^ (a * 3 + 2) - 1)) (RC m)) := by
  rw [z1N,z1Q]
  exact z1k (LC len k) (RC m) a
lemma z1Z (len k a m : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC2 (a * 4 + 3) 0 m)) [target_tm]⊢⁺
    (z0W (LC (len + (a * 3 + 4)) (2 ^ (len + (a * 3 + 4)) - 1)) (RC m)) := by
  rw [z1N,z1P]
  exact z1l (LC len k) (RC m) a (z1G len k hk)
lemma z20 (len k m : Nat) :
    (z0W (LC len k) (RC (m * 2))) [target_tm]⊢⁺
    (z0V (LC len k) ([0,0] +> RC m)) := by
  rw [RC,z0H z1B,<- RC]
  exact z1m (LC len k) (RC m)
lemma z21 (len k h n : Nat) (r : zB)
    (hk : k < 2 ^ len) (hn : n + k + 1 < 2 ^ (h + 1)) :
    (z0V (LC len k) (MC h (n + k + 1) r)) [target_tm]⊢*
    (z0U (LC len 0) (MC h n r)) := by
  induction k with
  | zero =>
    have h1 : n + 0 + 1 = 1 + n := by omega
    rw [h1]
    exact zPs (z1J h n (LC len 0) r (by omega))
  | succ k ih =>
    have h1 : n + (k + 1) + 1 = 1 + (n + k + 1) := by omega
    have h2 : k + 1 = 1 + k := by omega
    rw [h1,h2]
    have s1 := zPs (z1J h (n + k + 1) (LC len (1 + k)) r (by omega))
    have s2 := zPs (z1H len k (MC h (n + k + 1) r) (by omega))
    have s3 := ih (by omega) (by omega)
    exact zSt (zSt s1 s2) s3
lemma z22 (len k h n : Nat) (r : zB)
    (hk : k + n < 2 ^ len) (hn : n < 2 ^ (h + 1)) :
    (z0V (LC len (k + n)) (MC h n r)) [target_tm]⊢*
    (z0V (LC len k) (MC h 0 r)) := by
  induction n with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    have h1 : n + 1 = 1 + n := by omega
    have h2 : k + (n + 1) = 1 + (k + n) := by omega
    rw [h2,h1]
    have s1 := zPs (z1J h n (LC len (1 + (k + n))) r (by omega))
    have s2 := zPs (z1H len (k + n) (MC h n r) (by omega))
    have s3 := ih (by omega) (by omega)
    exact zSt (zSt s1 s2) s3
lemma z23' (len h : Nat) :
    (z0U (LC len 0) (RC2 (h + 1) ((2 ^ h - 1) * 2) 0)) [target_tm]⊢⁺
    (z0V (LC (len + 1) (2 ^ (len + 1) - 1)) (RC' h (2 ^ (h + 1) - 1))) := by
  unfold LC RC2 RC' MC RC
  rw [z0u,z0w,z0z,z0C,z0F]
  dsimp only [List.append_assoc,List.cons_append,List.nil_append]
  have h1 : h + 1 = 1 + h := by omega
  have h2 : 2 ^ h - 1 = (0 + 1) * 2 ^ h - 1 := by omega
  rw [h1,h2,z0y' [0,0,0] [0,0,1] 1 0 h]
  have h3 : z0o [0,0,0] [0,0,1] 1 0 ([0] +> rd1 +> default) =
      [0] +> [0] +> [1,0,1] +> default := by
    simp [z0u,rd1]
  rw [h3,Nat.add_comm len 1]
  change (z0U ((ld1 ^ len) +> ldh) ([1] +> (rd0 ^ h) +> ([0] +> ([0] +> [1,0,1] +> default)))) [target_tm]⊢⁺
    (z0V ((ld0 ^ (1 + len)) +> ldh) ((rd0 ^ h) +> ([0] +> [1,0,1] +> default)))
  rw [z0Y h ([0] +> [1,0,1] +> default),z0Y h ([1,0,1] +> default)]
  exact z18 ((rd0 ^ h) +> [1,0,1] +> default) len
lemma z24 (h : Nat) :
    (z0U (LC (h + 1) 0) (RC (2 ^ (h + 1)))) [target_tm]⊢⁺
    (z0V (LC (h + 1 + 1) (2 ^ (h + 1))) (RC' h 0)) := by
  have hp := z0v h
  have hp1 : 2 ^ (h + 1) = 2 ^ h * 2 := Nat.pow_succ 2 h
  have hp2 : 2 ^ (h + 1 + 1) = 2 ^ (h + 1) * 2 := Nat.pow_succ 2 (h + 1)
  have h1 : 2 ^ (h + 1) = (0 * 2 + 1) * 2 ^ (h + 1) := by omega
  have s1 := z1L (h + 1) 0 h
  rw [<- h1] at s1
  have h2 : (2 ^ (h + 1) - 1) * 2 = (2 ^ h - 1) * 2 + (2 ^ (h + 1) - 1) + 1 := by omega
  rw [h2] at s1
  have s2 := z21 (h + 1) (2 ^ (h + 1) - 1) (h + 1) ((2 ^ h - 1) * 2) ([0] +> rd1 +> RC 0)
    (by omega) (by omega)
  have s3 := z23' (h + 1) h
  have h3 : 2 ^ (h + 1 + 1) - 1 = 2 ^ (h + 1) + (2 ^ (h + 1) - 1) := by omega
  rw [h3] at s3
  have s4 := z22 (h + 1 + 1) (2 ^ (h + 1)) h (2 ^ (h + 1) - 1) ([1,0,1] +> default)
    (by omega) (by omega)
  exact z0R (zPt (z0R s1 s2) s3) s4
lemma z25 (len k a : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC' (a * 4) 0)) [target_tm]⊢*
    (z0V (LC (len + (a * 3 + 1)) (2 ^ (len + (a * 3 + 1)) - 1)) (RC 1)) := by
  rw [z1O,z1P,RC,z0G]
  exact z1n (LC len k) a (z1G len k hk)
lemma z26 (len k a : Nat) :
    (z0V (LC len k) (RC' (a * 4 + 1) 0)) [target_tm]⊢*
    (z0U (LC (len + 1 + (a * 3 + 1)) ((k * 2 + 1) * 2 ^ (a * 3 + 1))) (RC 0)) := by
  rw [z1O,z1R,RC,z0F]
  exact z1o (LC len k) a
lemma z27 (len k a : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC' (a * 4 + 2) 0)) [target_tm]⊢*
    (z0V (LC (len + (a * 3 + 3)) (2 ^ (len + (a * 3 + 3)) - 1)) (RC 0)) := by
  rw [z1O,z1P,RC,z0F]
  exact z1p (LC len k) a (z1G len k hk)
lemma z28 (len k a : Nat) :
    (z0V (LC len k) (RC' (a * 4 + 3) 0)) [target_tm]⊢*
    (z0U (LC (len + 1 + (a * 3 + 2)) ((k * 2 + 1) * 2 ^ (a * 3 + 2))) (RC 1)) := by
  rw [z1O,z1R,RC,z0G]
  exact z1q (LC len k) a
lemma z29 (m : Nat) : RC1 0 1 m = [0] +> RC (m * 2 + 1) := by
  unfold RC1 MC RC
  rw [z0A [0] [1] [0,0] 0 0 (rd1 +> z0q rd0 rd1 m),z0r,z0I]
lemma z2a (len k n m : Nat) (hk : k < 2 ^ len) (hn : n <= k) (hsmall : n < 2) :
    (z0V (LC len k) (RC1 0 n (m * 2 + 1))) [target_tm]⊢*
    (z0V (LC (len + 1) (2 ^ (len + 1) - 1)) (RC1 0 1 m)) := by
  rw [z29]
  have hk_eq : k = (k - n) + n := by omega
  rw [hk_eq]
  have s1 := z22 len (k - n) 0 n (rd1 +> RC (m * 2 + 1)) (by omega) (by omega)
  have s2 := zPs (z1S len (k - n) 0 (m * 2 + 1) (by omega))
  exact zSt s1 s2
lemma z2b (t len k n m : Nat) (hk : k < 2 ^ len) (hn : n <= k) (hsmall : n < 2) :
    (z0V (LC len k) (RC1 0 n ((m + 1) * 2 ^ (1 + t) - 1))) [target_tm]⊢*
    (z0V (LC (len + (1 + t)) (2 ^ (len + (1 + t)) - 1)) (RC1 0 1 m)) := by
  induction t generalizing len k n with
  | zero =>
    have h1 : (m + 1) * 2 ^ (1 + 0) - 1 = m * 2 + 1 := by simp; omega
    rw [h1]
    exact z2a len k n m hk hn hsmall
  | succ t ih =>
    have hp := z0v (1 + t)
    have hpos : 1 <= (m + 1) * 2 ^ (1 + t) := Nat.mul_pos (by omega) hp
    have h1 : (m + 1) * 2 ^ (1 + (t + 1)) - 1 = ((m + 1) * 2 ^ (1 + t) - 1) * 2 + 1 := by
      have : 1 + (t + 1) = (1 + t) + 1 := by omega
      rw [this,Nat.pow_succ]
      have : (m + 1) * (2 ^ (1 + t) * 2) = ((m + 1) * 2 ^ (1 + t)) * 2 := by ring
      (try omega)
    rw [h1]
    have s1 := z2a len k n ((m + 1) * 2 ^ (1 + t) - 1) hk hn hsmall
    have hp_len : 2 <= 2 ^ (len + 1) := by
      rw [Nat.pow_succ]; have := z0v len; omega
    have s2 := ih (len + 1) (2 ^ (len + 1) - 1) 1 (by omega) (by omega) (by omega)
    have h2 : len + 1 + (1 + t) = len + (1 + (t + 1)) := by omega
    rw [h2] at s2
    exact zSt s1 s2
lemma z2c (t len k m : Nat) (ht : 0 < t) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC1 0 0 ((m + 1) * 2 ^ t - 1))) [target_tm]⊢*
    (z0V (LC (len + t) (2 ^ (len + t) - 1)) (RC1 0 1 m)) := by
  cases t with
  | zero => omega
  | succ t =>
    have h1 : t + 1 = 1 + t := by omega
    rw [h1]
    exact z2b t len k 0 m hk (by omega) (by omega)
lemma z2d (len k m : Nat) (hk : k < 2 ^ len) :
    (z0U (LC len k) (RC m)) [target_tm]⊢* (z0U (LC len 0) (RC (k + m))) := by
  induction k generalizing m with
  | zero =>
    simp only [Nat.zero_add]
    exact ⟨0,rfl⟩
  | succ k ih =>
    have h1 : k + 1 = 1 + k := by omega
    rw [h1]
    have s1 := zPs (z1H len k (RC m) (by omega))
    have s2 := zPs (z1I m (LC len k))
    have s3 := ih (1 + m) (by omega)
    have h2 : k + (1 + m) = 1 + k + m := by omega
    rw [h2] at s3
    exact zSt (zSt s1 s2) s3
lemma z2e (len k m : Nat) (hk : k < 2 ^ len) :
    (z0V (LC len k) (RC m)) [target_tm]⊢* (z0U (LC len 0) (RC (k + m + 1))) := by
  have s1 := zPs (z1I m (LC len k))
  have s2 := z2d len k (1 + m) hk
  have h1 : k + (1 + m) = k + m + 1 := by omega
  rw [h1] at s2
  exact zSt s1 s2
lemma z2f (i m : Nat) : [0] +> RC ((m * 2 + 1) * 2 ^ i) = RC1 i (2 ^ (i + 1) - 1) m := by
  unfold RC RC1 MC
  rw [z0J z1B,z0I,z0C]
  exact (z0Y i (rd1 +> z0q rd0 rd1 m)).symm
lemma z2g (i m : Nat) : [1] +> RC ((m * 2 + 1) * 2 ^ i) = RC1 i (2 ^ (i + 1) - 1 - 1) m := by
  unfold RC RC1 MC
  have hp := z0v i
  have h1 : 2 ^ (i + 1) - 1 - 1 = (2 ^ i - 1) * 2 := by rw [Nat.pow_succ]; omega
  rw [h1,z0J z1B,z0I,z0z,z0w]
  rfl
lemma z2h (i m : Nat) : [0,0] +> RC ((m * 2 + 1) * 2 ^ i) = RC2 i (2 ^ (i + 1) - 1) m := by
  unfold RC RC2 MC
  rw [z0J z1B,z0I,z0C]
  change [0] +> ([0] +> ((rd0 ^ i) +> (rd1 +> z0q rd0 rd1 m))) =
    (rd0 ^ i) +> ([0] +> ([0] +> rd1 +> z0q rd0 rd1 m))
  rw [z0Y i ([0] +> rd1 +> z0q rd0 rd1 m),z0Y i (rd1 +> z0q rd0 rd1 m)]
lemma z2i (i m : Nat) :
    [1,0,0,0,0] +> RC ((m * 2 + 1) * 2 ^ i) = RC2 (i + 1) (2 ^ (i + 1 + 1) - 1 - 1) m := by
  unfold RC RC2 MC
  have hp := z0v (i + 1)
  have h1 : 2 ^ (i + 1 + 1) - 1 - 1 = (2 ^ (i + 1) - 1) * 2 := by rw [Nat.pow_succ]; omega
  rw [h1,z0J z1B,z0I,z0z,z0w]
  change [1] +> (rd0 +> ([0] +> ((rd0 ^ i) +> (rd1 +> z0q rd0 rd1 m)))) =
    [1] +> ((([0,0,0] : zF) ^ (i + 1)) +> ([0] +> rd1 +> z0q rd0 rd1 m))
  rw [z0j rd0 i,append_assoc,z0Y i (rd1 +> z0q rd0 rd1 m)]
lemma z2j (len m : Nat) :
    (z0U (LC len 0) (RC (m * 2))) [target_tm]⊢⁺
    (z0V (LC len (2 ^ len - 1)) ([1,0,0,0,0] +> RC m)) := by
  unfold LC RC
  rw [z0u,z0H z1B,z0w]
  exact z17 (z0q rd0 rd1 m) len
lemma z2k (len a : Nat) (hlen : len = a * 4 + 1) :
    (z0U (LC len 0) (RC (2 ^ len))) [target_tm]⊢*
    (z0U (LC (len + a * 3 + 2) 0) (RC (2 ^ (len + a * 3 + 2) + 1))) := by
  subst hlen
  have hp := z0v (a * 4 + 1 + 1)
  have hp2 := z0v (a * 4 + 1 + a * 3 + 2)
  have s1 := zPs (z24 (a * 4))
  have s2 := z25 (a * 4 + 1 + 1) (2 ^ (a * 4 + 1)) a (by rw [Nat.pow_succ]; omega)
  have h1 : a * 4 + 1 + 1 + (a * 3 + 1) = a * 4 + 1 + a * 3 + 2 := by omega
  rw [h1] at s2
  have s3 := z2e (a * 4 + 1 + a * 3 + 2) (2 ^ (a * 4 + 1 + a * 3 + 2) - 1) 1 (by omega)
  have h2 : 2 ^ (a * 4 + 1 + a * 3 + 2) - 1 + 1 + 1 = 2 ^ (a * 4 + 1 + a * 3 + 2) + 1 := by omega
  rw [h2] at s3
  exact zSt (zSt s1 s2) s3
lemma z2l (len a : Nat) (hlen : len = a * 4 + 2) :
    (z0U (LC len 0) (RC (2 ^ len))) [target_tm]⊢*
    (z0U (LC (len + a * 3 + 3) 0) (RC ((2 ^ len * 2 + 1) * 2 ^ (a * 3 + 1)))) := by
  have hlen' : len = (a * 4 + 1) + 1 := by omega
  rw [hlen']
  have s1 := zPs (z24 (a * 4 + 1))
  have s2 := z26 (a * 4 + 1 + 1 + 1) (2 ^ (a * 4 + 1 + 1)) a
  have h1 : a * 4 + 1 + 1 + 1 + 1 + (a * 3 + 1) = (a * 4 + 1 + 1) + a * 3 + 3 := by omega
  rw [h1] at s2
  have hk_lt : (2 ^ (a * 4 + 1 + 1) * 2 + 1) * 2 ^ (a * 3 + 1) < 2 ^ ((a * 4 + 1 + 1) + a * 3 + 3) := by
    have h_rhs : 2 ^ ((a * 4 + 1 + 1) + a * 3 + 3) = 2 ^ (a * 4 + 1 + 1) * 4 * 2 ^ (a * 3 + 1) := by
      have : (a * 4 + 1 + 1) + a * 3 + 3 = (a * 4 + 1 + 1) + 2 + (a * 3 + 1) := by omega
      rw [this,Nat.pow_add 2 (a * 4 + 1 + 1 + 2),Nat.pow_add 2 (a * 4 + 1 + 1) 2]
    rw [h_rhs]
    have hp := z0v (a * 3 + 1)
    have hp0 := z0v (a * 4 + 1 + 1)
    nlinarith
  have s3 := z2d ((a * 4 + 1 + 1) + a * 3 + 3) ((2 ^ (a * 4 + 1 + 1) * 2 + 1) * 2 ^ (a * 3 + 1)) 0 hk_lt
  rw [Nat.add_zero] at s3
  exact zSt (zSt s1 s2) s3
lemma z2m (len a : Nat) (hlen : len = a * 4 + 3) :
    (z0U (LC len 0) (RC (2 ^ len))) [target_tm]⊢*
    (z0U (LC (len + a * 3 + 4) 0) (RC (2 ^ (len + a * 3 + 4)))) := by
  have hlen' : len = (a * 4 + 2) + 1 := by omega
  rw [hlen']
  have hp2 := z0v ((a * 4 + 2 + 1) + a * 3 + 4)
  have s1 := zPs (z24 (a * 4 + 2))
  have s2 := z27 (a * 4 + 2 + 1 + 1) (2 ^ (a * 4 + 2 + 1)) a (by rw [Nat.pow_succ]; have := z0v (a * 4 + 2 + 1); omega)
  have h1 : a * 4 + 2 + 1 + 1 + (a * 3 + 3) = (a * 4 + 2 + 1) + a * 3 + 4 := by omega
  rw [h1] at s2
  have s3 := z2e ((a * 4 + 2 + 1) + a * 3 + 4) (2 ^ ((a * 4 + 2 + 1) + a * 3 + 4) - 1) 0 (by omega)
  have h2 : 2 ^ ((a * 4 + 2 + 1) + a * 3 + 4) - 1 + 0 + 1 = 2 ^ ((a * 4 + 2 + 1) + a * 3 + 4) := by omega
  rw [h2] at s3
  exact zSt (zSt s1 s2) s3
lemma z2n (len a : Nat) (hlen : len = a * 4 + 4) :
    (z0U (LC len 0) (RC (2 ^ len))) [target_tm]⊢*
    (z0U (LC (len + a * 3 + 4) 0) (RC ((2 ^ len * 2 + 1) * 2 ^ (a * 3 + 2) + 1))) := by
  have hlen' : len = (a * 4 + 3) + 1 := by omega
  rw [hlen']
  have s1 := zPs (z24 (a * 4 + 3))
  have s2 := z28 (a * 4 + 3 + 1 + 1) (2 ^ (a * 4 + 3 + 1)) a
  have h1 : a * 4 + 3 + 1 + 1 + 1 + (a * 3 + 2) = (a * 4 + 3 + 1) + a * 3 + 4 := by omega
  rw [h1] at s2
  have hk_lt : (2 ^ (a * 4 + 3 + 1) * 2 + 1) * 2 ^ (a * 3 + 2) < 2 ^ ((a * 4 + 3 + 1) + a * 3 + 4) := by
    have h_rhs : 2 ^ ((a * 4 + 3 + 1) + a * 3 + 4) = 2 ^ (a * 4 + 3 + 1) * 4 * 2 ^ (a * 3 + 2) := by
      have : (a * 4 + 3 + 1) + a * 3 + 4 = (a * 4 + 3 + 1) + 2 + (a * 3 + 2) := by omega
      rw [this,Nat.pow_add 2 (a * 4 + 3 + 1 + 2),Nat.pow_add 2 (a * 4 + 3 + 1) 2]
    rw [h_rhs]
    have hp := z0v (a * 3 + 2)
    have hp0 := z0v (a * 4 + 3 + 1)
    nlinarith
  have s3 := z2d ((a * 4 + 3 + 1) + a * 3 + 4) ((2 ^ (a * 4 + 3 + 1) * 2 + 1) * 2 ^ (a * 3 + 2)) 1 hk_lt
  exact zSt (zSt s1 s2) s3
def z2o (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ (cfg : Cfg (Fin 2) (Fin 6)),(c [target_tm]⊢* cfg) /\ (step target_tm cfg).isNone
lemma z2p {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target_tm]⊢* c_2) (h₂ : z2o c_2) : z2o c_1 := by
  rcases h₂ with ⟨cfg,h₂,hnone⟩
  exact ⟨cfg,zSt h₁ h₂,hnone⟩
lemma z2q (l r : zB) : z2o (z0W l (rd1 +> r)) := by
  refine ⟨z0W l (rd1 +> r),⟨0,rfl⟩,?_⟩
  unfold z0W step target_tm F
  simp only [rd1,append_cons,Turing.ListBlank.head_cons]
  rfl
lemma auxiliary_halt (len k m : Nat) : z2o (z0W (LC len k) (RC (m * 2 + 1))) := by
  unfold RC
  rw [z0I]
  exact z2q (LC len k) (z0q rd0 rd1 m)
def z2r (x : Sparse.num) : Nat := (Sparse.value x).toNat
lemma z2s (x : Sparse.num) (h : 0 <= Sparse.value x) :
    (z2r x : Int) = Sparse.value x := Int.toNat_of_nonneg h
lemma z2t (w : Nat) : Sparse.pow2 w = ((2 ^ w : Nat) : Int) := by
  unfold Sparse.pow2; norm_cast
lemma z2u (x y : Sparse.num) :
    Sparse.value (Forward13.plus x y) = Sparse.value x + Sparse.value y := by
  unfold Forward13.plus; rw [Sparse.pack_spec,Sparse.add_spec]
lemma z2v (x y : Sparse.num) :
    Sparse.value (Forward13.minus x y) = Sparse.value x - Sparse.value y := by
  unfold Forward13.minus; rw [Sparse.pack_spec,Sparse.sub_spec]
lemma z2w (x : Sparse.num) :
    Sparse.value (Forward13.twice x) = 2 * Sparse.value x := by
  unfold Forward13.twice; rw [Sparse.shift_spec]; rfl
lemma z2x (w : Nat) :
    Sparse.value (Forward13.full w) = Sparse.pow2 w - 1 := by
  unfold Forward13.full Forward13.one
  rw [z2v,Sparse.power_spec,Sparse.small_spec]
lemma z2y (x y : Sparse.num) (hx : 0 <= Sparse.value x) (hy : 0 <= Sparse.value y) :
    z2r (Forward13.plus x y) = z2r x + z2r y := by
  unfold z2r; rw [z2u]; omega
lemma z2z (x y : Sparse.num) (hy : 0 <= Sparse.value y) (hxy : Sparse.value y <= Sparse.value x) :
    z2r (Forward13.minus x y) = z2r x - z2r y := by
  unfold z2r; rw [z2v]; omega
lemma z2A (w : Nat) (x : Sparse.num) (hx : 0 <= Sparse.value x) :
    z2r (Sparse.shift w x) = 2 ^ w * z2r x := by
  unfold z2r
  have hp : 0 <= Sparse.pow2 w := le_of_lt (Sparse.zPp w)
  rw [Sparse.shift_spec,Int.toNat_mul hp hx,z2t,Int.toNat_natCast]
lemma z2B (x : Sparse.num) (hx : 0 <= Sparse.value x) :
    z2r (Forward13.twice x) = 2 * z2r x := by
  unfold Forward13.twice; rw [z2A 1 x hx]; rfl
lemma z2C (w : Nat) : z2r (Forward13.full w) = 2 ^ w - 1 := by
  unfold z2r
  have hp := Sparse.zPp w
  have h1 : (Sparse.pow2 w - 1).toNat = (Sparse.pow2 w).toNat - 1 := by omega
  rw [z2x,h1,z2t,Int.toNat_natCast]
lemma z2D (w : Nat) : z2r (Sparse.power w) = 2 ^ w := by
  unfold z2r; rw [Sparse.power_spec,z2t,Int.toNat_natCast]
lemma z2E {x y : Sparse.num} (h : Forward13.lt x y = true) :
    Sparse.value x < Sparse.value y := by
  unfold Forward13.lt at h
  rw [beq_iff_eq] at h
  have hcmp := Sparse.compare_spec h
  unfold Sparse.cmp0 at hcmp
  split_ifs at hcmp <;> omega
lemma z2F {x : Sparse.num} (h : Sparse.nonnegative x = true) :
    0 <= Sparse.value x := by
  have h1 := Sparse.leb_spec h
  simpa [Sparse.value] using h1
lemma z2G (w : Nat) : 0 <= Sparse.value (Forward13.full w) := by
  rw [z2x]; have := Sparse.zPp w; omega
lemma z2H {m : Sparse.num} {i : Nat} {u : Sparse.num} (h : Sparse.split m = some (i,u)) :
    0 <= Sparse.value u /\ z2r m = (z2r u * 2 + 1) * 2 ^ i := by
  rcases Sparse.split_spec h with ⟨hu,hm⟩
  refine ⟨hu,?_⟩
  have hp := Sparse.zPp i
  have hm_nonneg : 0 <= Sparse.value m := by rw [hm]; nlinarith
  have h_eq : (z2r m : Int) = (((z2r u * 2 + 1) * 2 ^ i : Nat) : Int) := by
    push_cast
    rw [z2s m hm_nonneg,z2s u hu]
    unfold Sparse.pow2 at hm
    linarith
  exact Int.ofNat.inj h_eq
lemma z2I {m : Sparse.num} {b : Bool} {u : Sparse.num} (h : Sparse.half m = some (b,u)) :
    0 <= Sparse.value u /\ z2r m = z2r u * 2 + (if b then 1 else 0) := by
  rcases Sparse.half_spec h with ⟨hu,hm⟩
  refine ⟨hu,?_⟩
  cases b
  · simp only [Bool.false_eq_true,↓reduceIte,add_zero] at hm ⊢
    have hm_nonneg : 0 <= Sparse.value m := by omega
    have h_eq : (z2r m : Int) = ((z2r u * 2 : Nat) : Int) := by
      push_cast; rw [z2s m hm_nonneg,z2s u hu]; omega
    exact Int.ofNat.inj h_eq
  · simp only [↓reduceIte] at hm ⊢
    have hm_nonneg : 0 <= Sparse.value m := by omega
    have h_eq : (z2r m : Int) = ((z2r u * 2 + 1 : Nat) : Int) := by
      push_cast; rw [z2s m hm_nonneg,z2s u hu]; omega
    exact Int.ofNat.inj h_eq
lemma z2J {x y : Sparse.num} (h : Sparse.eqb x y = true) : z2r x = z2r y := by
  unfold z2r; rw [Sparse.eqb_spec h]
lemma z2K (s p : Nat) :
    z2r (Sparse.shift s (Forward13.plus (Sparse.power p) Forward13.one)) = (2 ^ p + 1) * 2 ^ s := by
  have hp : 0 <= Sparse.value (Sparse.power p) := by rw [Sparse.power_spec]; exact le_of_lt (Sparse.zPp p)
  have h1 : 0 <= Sparse.value Forward13.one := by decide
  have hplus : 0 <= Sparse.value (Forward13.plus (Sparse.power p) Forward13.one) := by rw [z2u]; omega
  rw [z2A s _ hplus,z2y _ _ hp h1,z2D]
  change 2 ^ s * (2 ^ p + 1) = (2 ^ p + 1) * 2 ^ s
  ring
lemma z2L (s p : Nat) :
    z2r (Forward13.plus (Sparse.shift s (Forward13.plus (Sparse.power p) Forward13.one)) Forward13.one) =
    (2 ^ p + 1) * 2 ^ s + 1 := by
  have hp : 0 <= Sparse.value (Sparse.power p) := by rw [Sparse.power_spec]; exact le_of_lt (Sparse.zPp p)
  have h1 : 0 <= Sparse.value Forward13.one := by decide
  have hplus : 0 <= Sparse.value (Forward13.plus (Sparse.power p) Forward13.one) := by rw [z2u]; omega
  have hshift : 0 <= Sparse.value (Sparse.shift s (Forward13.plus (Sparse.power p) Forward13.one)) := by
    rw [Sparse.shift_spec]; exact mul_nonneg (le_of_lt (Sparse.zPp s)) hplus
  rw [z2y _ _ hshift h1,z2K]
  rfl
lemma z2M (s : Nat) (b : Sparse.num) (hb : 0 <= Sparse.value b) :
    z2r (Sparse.shift s (Forward13.plus (Forward13.twice b) Forward13.one)) =
    (z2r b * 2 + 1) * 2 ^ s := by
  have h1 : 0 <= Sparse.value Forward13.one := by decide
  have h2 : 0 <= Sparse.value (Forward13.twice b) := by rw [z2w]; omega
  have hplus : 0 <= Sparse.value (Forward13.plus (Forward13.twice b) Forward13.one) := by rw [z2u]; omega
  rw [z2A s _ hplus,z2y _ _ h2 h1,z2B b hb]
  change 2 ^ s * (2 * z2r b + 1) = (z2r b * 2 + 1) * 2 ^ s
  ring
lemma z2N (s : Nat) (b : Sparse.num) (hb : 0 <= Sparse.value b) :
    z2r (Forward13.minus (Sparse.shift s (Forward13.plus (Forward13.twice b) Forward13.one)) Forward13.one) =
    (z2r b * 2 + 1) * 2 ^ s - 1 := by
  have h1 : 0 <= Sparse.value Forward13.one := by decide
  have h2 : 0 <= Sparse.value (Forward13.twice b) := by rw [z2w]; omega
  have hplus : 1 <= Sparse.value (Forward13.plus (Forward13.twice b) Forward13.one) := by
    rw [z2u,Forward13.one,Sparse.small_spec]; omega
  have hshift : 1 <= Sparse.value (Sparse.shift s (Forward13.plus (Forward13.twice b) Forward13.one)) := by
    rw [Sparse.shift_spec]; have := Sparse.zPp s; nlinarith
  have hle : Sparse.value Forward13.one <= Sparse.value (Sparse.shift s (Forward13.plus (Forward13.twice b) Forward13.one)) := by
    have : Sparse.value Forward13.one = 1 := rfl
    linarith
  rw [z2z _ _ h1 hle,z2M s b hb]
  rfl
lemma z2O (m : Sparse.num) (hm : 0 <= Sparse.value m) :
    z2r (Forward13.plus (Forward13.twice m) Forward13.one) = z2r m * 2 + 1 := by
  have h1 : 0 <= Sparse.value Forward13.one := by decide
  have h2 : 0 <= Sparse.value (Forward13.twice m) := by rw [z2w]; omega
  rw [z2y _ _ h2 h1,z2B m hm]
  change 2 * z2r m + 1 = z2r m * 2 + 1
  ring
def z2P (x : Forward13.State) : Cfg (Fin 2) (Fin 6) :=
  let w := x.width
  let k := z2r x.budget
  let m := z2r x.high
  match x.tag with
  | .L => z0U (LC w k) (RC m)
  | .R => z0V (LC w k) (RC m)
  | .A => z0W (LC w k) (RC m)
  | .T1 => z0V (LC w k) (RC1 x.mark (z2r x.low) m)
  | .T2 => z0V (LC w k) (RC2 x.mark (z2r x.low) m)
def z2Q (x : Forward13.State) : Prop :=
  let w := x.width
  let k := z2r x.budget
  let m := z2r x.high
  let h := x.mark
  let n := z2r x.low
  match x.tag with
  | .L => 1 <= w /\ k < 2 ^ w /\ k + m < 2 ^ w * 2
  | .R => 1 <= w /\ k < 2 ^ w /\ k + m + 1 < 2 ^ w * 2
  | .A => 1 <= w /\ m <= k /\ k < 2 ^ w
  | .T1 | .T2 => 1 <= w /\ n + m <= k /\ k < 2 ^ w /\ n < 2 ^ (h + 1)
lemma z2R {x : Forward13.State} (h : Forward13.good x = true) :
    0 < x.width /\ 0 <= Sparse.value x.budget /\ Sparse.value x.budget < Sparse.pow2 x.width /\
    0 <= Sparse.value x.high := by
  unfold Forward13.good at h
  split_ifs at h with hw hk hcap hm <;>
    exact ⟨hw,z2F hk,by have := z2E hcap; rwa [Sparse.power_spec] at this,z2F hm⟩
lemma z2S {p : Forward13.Phase} {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num}
    (hp : p = .T1 \/ p = .T2) (hg : Forward13.good ⟨p,w,k,h,n,m⟩ = true) :
    0 <= Sparse.value n := by
  unfold Forward13.good at hg
  rcases hp with rfl | rfl <;> (
    dsimp only at hg
    split_ifs at hg with hw hk hcap hm hn hlow
    exact z2F hn
  )
lemma z2T {x : Forward13.State} (hg : Forward13.good x = true) : z2Q x := by
  rcases z2R hg with ⟨hw,hk,hcap,hm⟩
  rcases x with ⟨p,w,k,h,n,m⟩
  dsimp only at hw hk hcap hm
  have h_k_nat : (z2r k : Int) = Sparse.value k := z2s k hk
  have h_m_nat : (z2r m : Int) = Sparse.value m := z2s m hm
  have h_pow_w : Sparse.pow2 w = ((2 ^ w : Nat) : Int) := z2t w
  cases p <;> (
    unfold Forward13.good at hg
    dsimp only [z2Q] at hg ⊢
    split_ifs at hg
  )
  · have hlt := z2E hg
    rw [z2u,Sparse.power_spec,Sparse.pow2_add,show Sparse.pow2 1 = 2 from rfl,h_pow_w] at hlt
    (try omega)
  · have hlt := z2E hg
    rw [z2u,z2u,Forward13.one,Sparse.small_spec,Sparse.power_spec,
      Sparse.pow2_add,show Sparse.pow2 1 = 2 from rfl,h_pow_w] at hlt
    (try omega)
  · rename_i hn hlow
    have hn' := z2F hn
    have h_n_nat : (z2r n : Int) = Sparse.value n := z2s n hn'
    have hlt := z2E hlow
    rw [Sparse.power_spec,z2t] at hlt
    have hle := Sparse.leb_spec hg
    rw [z2u] at hle
    (try omega)
  · rename_i hn hlow
    have hn' := z2F hn
    have h_n_nat : (z2r n : Int) = Sparse.value n := z2s n hn'
    have hlt := z2E hlow
    rw [Sparse.power_spec,z2t] at hlt
    have hle := Sparse.leb_spec hg
    rw [z2u] at hle
    (try omega)
  · have hle := Sparse.leb_spec hg
    (try omega)
lemma z2U {w : Nat} {k m : Sparse.num} {y : Forward13.State}
    (h : Forward13.prefix_step .T1 w k m 0 0 = .next y) :
    z2P y = z0V (LC w (z2r k)) ([0] +> RC (z2r m)) := by
  unfold Forward13.prefix_step Forward13.iszero at h
  split_ifs at h with hz
  · injection h with hy; subst hy
    have hm0 : z2r m = 0 := by unfold z2r; rw [Sparse.eqb_spec hz]; rfl
    have hs0 : z2r (Sparse.small 0) = 0 := rfl
    simp only [z2P,Forward13.ordinary,hm0,hs0,z1E]
  · cases hs : Sparse.split m with
    | none => rw [hs] at h; contradiction
    | some iu =>
      rcases iu with ⟨i,u⟩
      rw [hs] at h
      injection h with hy; subst hy
      rcases z2H hs with ⟨hu,hm⟩
      simp only [z2P,Nat.add_zero]
      have h_sub : z2r (Forward13.minus (Forward13.full (i + 1)) (Sparse.small 0)) = 2 ^ (i + 1) - 1 := by
        rw [z2z _ _ (by simp [Sparse.small_spec]) (by rw [Sparse.small_spec]; exact z2G (i + 1)),z2C]
        rfl
      rw [h_sub,hm,z2f]
lemma z2V {w : Nat} {k m : Sparse.num} {y : Forward13.State}
    (h : Forward13.prefix_step .T1 w k m 0 1 = .next y) :
    z2P y = z0V (LC w (z2r k)) ([1] +> RC (z2r m)) := by
  unfold Forward13.prefix_step Forward13.iszero at h
  split_ifs at h with hz
  · injection h with hy; subst hy
    have hm0 : z2r m = 0 := by unfold z2r; rw [Sparse.eqb_spec hz]; rfl
    have hs1 : z2r (Sparse.small 1) = 1 := rfl
    simp only [z2P,Forward13.ordinary,hm0,hs1,z1C]
  · cases hs : Sparse.split m with
    | none => rw [hs] at h; contradiction
    | some iu =>
      rcases iu with ⟨i,u⟩
      rw [hs] at h
      injection h with hy; subst hy
      rcases z2H hs with ⟨hu,hm⟩
      simp only [z2P,Nat.add_zero]
      have hp : 2 <= Sparse.pow2 (i + 1) := by
        rw [Sparse.pow2_add,show Sparse.pow2 1 = 2 from rfl]; have := Sparse.zPp i; omega
      have h_sub : z2r (Forward13.minus (Forward13.full (i + 1)) (Sparse.small 1)) = 2 ^ (i + 1) - 1 - 1 := by
        rw [z2z _ _ (by simp [Sparse.small_spec]) (by rw [Sparse.small_spec,z2x]; omega),z2C]
        rfl
      rw [h_sub,hm,z2g]
lemma z2W {w : Nat} {k m : Sparse.num} {y : Forward13.State}
    (h : Forward13.prefix_step .T2 w k m 0 0 = .next y) :
    z2P y = z0V (LC w (z2r k)) ([0,0] +> RC (z2r m)) := by
  unfold Forward13.prefix_step Forward13.iszero at h
  split_ifs at h with hz
  · injection h with hy; subst hy
    have hm0 : z2r m = 0 := by unfold z2r; rw [Sparse.eqb_spec hz]; rfl
    have hs0 : z2r (Sparse.small 0) = 0 := rfl
    simp only [z2P,Forward13.ordinary,hm0,hs0,z1D]
  · cases hs : Sparse.split m with
    | none => rw [hs] at h; contradiction
    | some iu =>
      rcases iu with ⟨i,u⟩
      rw [hs] at h
      injection h with hy; subst hy
      rcases z2H hs with ⟨hu,hm⟩
      simp only [z2P,Nat.add_zero]
      have h_sub : z2r (Forward13.minus (Forward13.full (i + 1)) (Sparse.small 0)) = 2 ^ (i + 1) - 1 := by
        rw [z2z _ _ (by simp [Sparse.small_spec]) (by rw [Sparse.small_spec]; exact z2G (i + 1)),z2C]
        rfl
      rw [h_sub,hm,z2h]
lemma z2X {w : Nat} {k m : Sparse.num} {y : Forward13.State}
    (h : Forward13.prefix_step .T2 w k m 1 1 = .next y) :
    z2P y = z0V (LC w (z2r k)) ([1,0,0,0,0] +> RC (z2r m)) := by
  unfold Forward13.prefix_step Forward13.iszero at h
  split_ifs at h with hz
  · injection h with hy; subst hy
    have hm0 : z2r m = 0 := by unfold z2r; rw [Sparse.eqb_spec hz]; rfl
    have hs1 : z2r (Sparse.small 1) = 1 := rfl
    simp only [z2P,Forward13.ordinary,hm0,hs1,z1F]
  · cases hs : Sparse.split m with
    | none => rw [hs] at h; contradiction
    | some iu =>
      rcases iu with ⟨i,u⟩
      rw [hs] at h
      injection h with hy; subst hy
      rcases z2H hs with ⟨hu,hm⟩
      simp only [z2P]
      have hp : 2 <= Sparse.pow2 (i + 1 + 1) := by
        rw [Sparse.pow2_add,show Sparse.pow2 1 = 2 from rfl]; have := Sparse.zPp (i + 1); omega
      have h_sub : z2r (Forward13.minus (Forward13.full (i + 1 + 1)) (Sparse.small 1)) = 2 ^ (i + 1 + 1) - 1 - 1 := by
        rw [z2z _ _ (by simp [Sparse.small_spec]) (by rw [Sparse.small_spec,z2x]; omega),z2C]
        rfl
      rw [h_sub,hm,z2i]
lemma z2Y {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num} {y : Forward13.State}
    (hg : Forward13.good ⟨.R,w,k,h,n,m⟩ = true)
    (hs : Forward13.step_state ⟨.R,w,k,h,n,m⟩ = .next y) :
    (z2P ⟨.R,w,k,h,n,m⟩) [target_tm]⊢* (z2P y) := by
  rcases z2R hg with ⟨hw,hk,hcap,hm⟩
  dsimp only at hw hk hcap hm
  have hP := z2T hg
  dsimp only [z2Q] at hP
  rcases hP with ⟨_,hk_lt,_⟩
  dsimp only [Forward13.step_state] at hs
  injection hs with hy; subst hy
  dsimp only [z2P,Forward13.ordinary]
  have h0 : z2r [] = 0 := rfl
  have h1 : z2r (Forward13.plus (Forward13.plus k m) Forward13.one) = z2r k + z2r m + 1 := by
    rw [z2y _ _ (by rw [z2u]; omega) (by decide),z2y _ _ hk hm]
    rfl
  rw [h0,h1]
  exact z2e w (z2r k) (z2r m) hk_lt
lemma z2Z {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num} {y : Forward13.State}
    (_hg : Forward13.good ⟨.A,w,k,h,n,m⟩ = true)
    (hs : Forward13.step_state ⟨.A,w,k,h,n,m⟩ = .next y) :
    (z2P ⟨.A,w,k,h,n,m⟩) [target_tm]⊢* (z2P y) := by
  dsimp only [Forward13.step_state] at hs
  cases hhalf : Sparse.half m with
  | none => rw [hhalf] at hs; contradiction
  | some bu =>
    rcases bu with ⟨b,u⟩
    rw [hhalf] at hs
    cases b
    · rw [z2W hs]
      rcases z2I hhalf with ⟨_,hm⟩
      simp only [z2P,hm,Bool.false_eq_true,↓reduceIte,Nat.add_zero]
      exact zPs (z20 w (z2r k) (z2r u))
    · contradiction
lemma z30 {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num} {y : Forward13.State}
    (hg : Forward13.good ⟨.L,w,k,h,n,m⟩ = true)
    (hs : Forward13.step_state ⟨.L,w,k,h,n,m⟩ = .next y) :
    (z2P ⟨.L,w,k,h,n,m⟩) [target_tm]⊢* (z2P y) := by
  rcases z2R hg with ⟨hw,hk,hcap,hm⟩
  dsimp only at hw hk hcap hm
  have hP := z2T hg
  dsimp only [z2Q] at hP
  rcases hP with ⟨hw1,hk_lt,_⟩
  let v := Forward13.plus k m
  have hv : z2r v = z2r k + z2r m := z2y k m hk hm
  have s1 : (z2P ⟨.L,w,k,h,n,m⟩) [target_tm]⊢* (z0U (LC w 0) (RC (z2r v))) := by
    dsimp only [z2P]
    rw [hv]
    exact z2d w (z2r k) (z2r m) hk_lt
  refine zSt s1 ?_
  unfold Forward13.step_state at hs
  dsimp only at hs
  change (if Sparse.eqb v (Sparse.power w) then _ else _) = Forward13.Result.next y at hs
  by_cases heq : Sparse.eqb v (Sparse.power w) = true
  · rw [if_pos heq] at hs
    have hv_pow : z2r v = 2 ^ w := by rw [z2J heq,z2D]
    rw [hv_pow]
    let a := (w - 1) / 4
    let e := (w - 1) % 4
    have h_div : w - 1 = a * 4 + e := by omega
    have h_mod : e < 4 := Nat.mod_lt (w - 1) (by decide)
    have h3a : 3 * a = a * 3 := by ring
    have h0 : z2r [] = 0 := rfl
    split_ifs at hs with he0 he1 he2
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      have h_num : z2r (Forward13.plus (Sparse.power (w + 3 * a + 2)) Forward13.one) =
          2 ^ (w + a * 3 + 2) + 1 := by
        rw [z2y _ _ (by rw [Sparse.power_spec]; exact le_of_lt (Sparse.zPp _)) (by decide),
          z2D,h3a]
        rfl
      rw [h0,h_num,h3a]
      exact z2k w a (by omega)
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      rw [h0,z2K,h3a,Nat.pow_succ]
      exact z2l w a (by omega)
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      rw [h0,z2D,h3a]
      exact z2m w a (by omega)
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      rw [h0,z2L,h3a,Nat.pow_succ]
      exact z2n w a (by omega)
  · rw [if_neg heq] at hs
    cases hhalf : Sparse.half v with
    | none => rw [hhalf] at hs; contradiction
    | some bu =>
      rcases bu with ⟨b,u⟩
      rw [hhalf] at hs
      rcases z2I hhalf with ⟨_,hv_half⟩
      cases b
      · rw [z2X hs,z2C,hv_half]
        simp only [Bool.false_eq_true,↓reduceIte,Nat.add_zero]
        exact zPs (z2j w (z2r u))
      · rw [z2U hs,z2C,hv_half]
        simp only [↓reduceIte]
        exact zPs (z1K w (z2r u))
lemma z31 {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num} {y : Forward13.State}
    (hg : Forward13.good ⟨.T2,w,k,h,n,m⟩ = true)
    (hs : Forward13.step_state ⟨.T2,w,k,h,n,m⟩ = .next y) :
    (z2P ⟨.T2,w,k,h,n,m⟩) [target_tm]⊢* (z2P y) := by
  rcases z2R hg with ⟨hw,hk,hcap,hm⟩
  dsimp only at hw hk hcap hm
  have hP := z2T hg
  dsimp only [z2Q] at hP
  rcases hP with ⟨hw1,hnm_le,hk_lt,hn_lt⟩
  have hn := z2S (Or.inr rfl) hg
  have h_k_nat : (z2r k : Int) = Sparse.value k := z2s k hk
  have h_n_nat : (z2r n : Int) = Sparse.value n := z2s n hn
  let b := Forward13.minus k n
  have hb_nonneg : 0 <= Sparse.value b := by rw [z2v]; omega
  have hb_num : z2r b = z2r k - z2r n := z2z k n hn (by omega)
  have s1 : (z2P ⟨.T2,w,k,h,n,m⟩) [target_tm]⊢*
      (z0V (LC w (z2r b)) (RC2 h 0 (z2r m))) := by
    dsimp only [z2P]
    have hk_eq : z2r k = z2r b + z2r n := by omega
    rw [hk_eq]
    exact z22 w (z2r b) h (z2r n) ([0] +> rd1 +> RC (z2r m)) (by omega) hn_lt
  refine zSt s1 ?_
  unfold Forward13.step_state at hs
  dsimp only at hs
  let a := h / 4
  let e := h % 4
  have h_div : h = a * 4 + e := by omega
  have h_mod : e < 4 := Nat.mod_lt h (by decide)
  have h3a : 3 * a = a * 3 := by ring
  split_ifs at hs with he0 he1 he2
  · rw [z2U hs,z2M (3 * a) b hb_nonneg,h3a]
    have hh : h = a * 4 := by omega
    have hw_eq : w + a * 3 + 1 = w + 1 + a * 3 := by omega
    rw [hh,hw_eq]
    exact zPs (z1W w (z2r b) a (z2r m))
  · rw [z2V hs,z2C,h3a]
    have hh : h = a * 4 + 1 := by omega
    have hw_eq : w + a * 3 + 2 = w + (a * 3 + 2) := by omega
    rw [hh,hw_eq]
    exact zPs (z1X w (z2r b) a (z2r m) (by omega))
  · injection hs with hy; subst hy
    dsimp only [z2P,Forward13.ordinary]
    rw [z2N (3 * a + 2) b hb_nonneg,h3a]
    have hh : h = a * 4 + 2 := by omega
    have hw_eq : w + a * 3 + 3 = w + 1 + (a * 3 + 2) := by omega
    rw [hh,hw_eq]
    exact zPs (z1Y w (z2r b) a (z2r m))
  · injection hs with hy; subst hy
    dsimp only [z2P,Forward13.ordinary]
    rw [z2C,h3a]
    have hh : h = a * 4 + 3 := by omega
    have hw_eq : w + a * 3 + 4 = w + (a * 3 + 4) := by omega
    rw [hh,hw_eq]
    exact zPs (z1Z w (z2r b) a (z2r m) (by omega))
lemma z32 {w : Nat} {k : Sparse.num} {h : Nat} {n m : Sparse.num} {y : Forward13.State}
    (hg : Forward13.good ⟨.T1,w,k,h,n,m⟩ = true)
    (hs : Forward13.step_state ⟨.T1,w,k,h,n,m⟩ = .next y) :
    (z2P ⟨.T1,w,k,h,n,m⟩) [target_tm]⊢* (z2P y) := by
  rcases z2R hg with ⟨hw,hk,hcap,hm⟩
  dsimp only at hw hk hcap hm
  have hP := z2T hg
  dsimp only [z2Q] at hP
  rcases hP with ⟨hw1,hnm_le,hk_lt,hn_lt⟩
  have hn := z2S (Or.inl rfl) hg
  have h_k_nat : (z2r k : Int) = Sparse.value k := z2s k hk
  have h_n_nat : (z2r n : Int) = Sparse.value n := z2s n hn
  let b := Forward13.minus k n
  have hb_nonneg : 0 <= Sparse.value b := by rw [z2v]; omega
  have hb_num : z2r b = z2r k - z2r n := z2z k n hn (by omega)
  have s1 : (z2P ⟨.T1,w,k,h,n,m⟩) [target_tm]⊢*
      (z0V (LC w (z2r b)) (RC1 h 0 (z2r m))) := by
    dsimp only [z2P]
    have hk_eq : z2r k = z2r b + z2r n := by omega
    rw [hk_eq]
    exact z22 w (z2r b) h (z2r n) (rd1 +> RC (z2r m)) (by omega) hn_lt
  refine zSt s1 ?_
  unfold Forward13.step_state at hs
  dsimp only at hs
  by_cases hh0 : h = 0
  · subst hh0
    rw [if_pos rfl] at hs
    cases hhalf : Sparse.half m with
    | none => rw [hhalf] at hs; contradiction
    | some bv =>
      rcases bv with ⟨bit,v⟩
      rw [hhalf] at hs
      cases bit
      · rw [z2U hs,z2C]
        have h0 : 0 = 0 * 4 := rfl
        have hw_eq : w + 1 = w + (0 * 3 + 1) := by omega
        rw [h0,hw_eq]
        exact zPs (z1S w (z2r b) 0 (z2r m) (by omega))
      · cases hsplit : Sparse.split (Forward13.plus m Forward13.one) with
        | none => rw [hsplit] at hs; contradiction
        | some tu =>
          rcases tu with ⟨t,u⟩
          rw [hsplit] at hs
          dsimp only at hs
          split_ifs at hs with ht
          injection hs with hy; subst hy
          rcases z2H hsplit with ⟨hu,hm1⟩
          rw [z2y m Forward13.one hm (by decide)] at hm1
          have hone : z2r Forward13.one = 1 := rfl
          rw [hone] at hm1
          dsimp only [z2P]
          rw [z2C,hone,z2B u hu]
          have hm_eq : z2r m = (2 * z2r u + 1) * 2 ^ t - 1 := by
            have h_comm : z2r u * 2 + 1 = 2 * z2r u + 1 := by ring
            rw [h_comm] at hm1
            (try omega)
          rw [hm_eq]
          exact z2c t w (z2r b) (2 * z2r u) ht (by omega)
  · rw [if_neg hh0] at hs
    let a := h / 4
    let e := h % 4
    have h_div : h = a * 4 + e := by omega
    have h_mod : e < 4 := Nat.mod_lt h (by decide)
    have h3a : 3 * a = a * 3 := by ring
    split_ifs at hs with he0 he1 he2
    · rw [z2U hs,z2C,h3a]
      have hh : h = a * 4 := by omega
      have hw_eq : w + a * 3 + 1 = w + (a * 3 + 1) := by omega
      rw [hh,hw_eq]
      exact zPs (z1S w (z2r b) a (z2r m) (by omega))
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      rw [z2N (3 * a) b hb_nonneg,z2O m hm,h3a]
      have hh : h = a * 4 + 1 := by omega
      have hw_eq : w + a * 3 + 1 = w + 1 + a * 3 := by omega
      rw [hh,hw_eq]
      exact zPs (z1T w (z2r b) a (z2r m))
    · injection hs with hy; subst hy
      dsimp only [z2P,Forward13.ordinary]
      rw [z2C,z2O m hm,h3a]
      have hh : h = a * 4 + 2 := by omega
      have hw_eq : w + a * 3 + 2 = w + (a * 3 + 2) := by omega
      rw [hh,hw_eq]
      exact zPs (z1U w (z2r b) a (z2r m) (by omega))
    · rw [z2U hs,z2N (3 * a + 2) b hb_nonneg,h3a]
      have hh : h = a * 4 + 3 := by omega
      have hw_eq : w + a * 3 + 3 = w + 1 + (a * 3 + 2) := by omega
      rw [hh,hw_eq]
      exact zPs (z1V w (z2r b) a (z2r m))
lemma z33 {x y : Forward13.State} (hg : Forward13.good x = true)
    (hs : Forward13.step_state x = .next y) :
    (z2P x) [target_tm]⊢* (z2P y) := by
  rcases x with ⟨p,w,k,h,n,m⟩
  cases p
  · exact z30 hg hs
  · exact z2Y hg hs
  · exact z32 hg hs
  · exact z31 hg hs
  · exact z2Z hg hs
lemma z34 (p : Forward13.Phase) (w : Nat) (k m : Sparse.num) (a : Nat) (b : Int) :
    Forward13.prefix_step p w k m a b ≠ .halted := by
  unfold Forward13.prefix_step
  split_ifs
  · intro h; contradiction
  · cases Sparse.split m <;> (intro h; contradiction)
lemma z35 {x : Forward13.State} (_hg : Forward13.good x = true)
    (hs : Forward13.step_state x = .halted) :
    z2o (z2P x) := by
  rcases x with ⟨p,w,k,h,n,m⟩
  unfold Forward13.step_state at hs
  cases p <;> dsimp only at hs
  · by_cases heq : Sparse.eqb (Forward13.plus k m) (Sparse.power w) = true
    · rw [if_pos heq] at hs
      split_ifs at hs
    · rw [if_neg heq] at hs
      cases hhalf : Sparse.half (Forward13.plus k m) with
      | none => rw [hhalf] at hs; contradiction
      | some bu =>
        rcases bu with ⟨b,u⟩
        rw [hhalf] at hs
        cases b <;> exact False.elim (z34 _ _ _ _ _ _ hs)
  · contradiction
  · by_cases hh0 : h = 0
    · rw [if_pos hh0] at hs
      cases hhalf : Sparse.half m with
      | none => rw [hhalf] at hs; contradiction
      | some bv =>
        rcases bv with ⟨bit,v⟩
        rw [hhalf] at hs
        cases bit
        · exact False.elim (z34 _ _ _ _ _ _ hs)
        · cases hsplit : Sparse.split (Forward13.plus m Forward13.one) with
          | none => rw [hsplit] at hs; contradiction
          | some tu =>
            rcases tu with ⟨t,u⟩
            rw [hsplit] at hs
            dsimp only at hs
            split_ifs at hs
    · rw [if_neg hh0] at hs
      split_ifs at hs <;> exact False.elim (z34 _ _ _ _ _ _ hs)
  · split_ifs at hs <;> exact False.elim (z34 _ _ _ _ _ _ hs)
  · cases hhalf : Sparse.half m with
    | none => rw [hhalf] at hs; contradiction
    | some bu =>
      rcases bu with ⟨b,u⟩
      rw [hhalf] at hs
      cases b
      · exact False.elim (z34 _ _ _ _ _ _ hs)
      · rcases z2I hhalf with ⟨_,hm⟩
        simp only [z2P,hm,↓reduceIte]
        exact auxiliary_halt w (z2r k) (z2r u)
lemma z36 (fuel : Nat) (x : Forward13.State) (h : Forward13.check fuel x = true) :
    z2o (z2P x) := by
  induction fuel generalizing x with
  | zero => contradiction
  | succ fuel ih =>
    unfold Forward13.check at h
    split_ifs at h with hg
    cases hs : Forward13.step_state x with
    | next y =>
      rw [hs] at h
      exact z2p (z33 hg hs) (ih y h)
    | halted =>
      exact z35 hg hs
    | stuck =>
      rw [hs] at h
      contradiction
lemma z37 : (init []) [target_tm]⊢* (z2P Forward13.seed) := by
  have h_meaning : z2P Forward13.seed =
      z0U ((ld1 ^ 3) +> ldh) ([1,0,0,0,0,0,0,0,0,1,0,0] +> default) := by
    dsimp only [Forward13.seed,Forward13.ordinary,z2P,LC,RC]
    have h0 : z2r [] = 0 := rfl
    have h9 : z2r (Sparse.pack (Sparse.small 9)) = 9 := by
      unfold z2r; rw [Sparse.pack_spec,Sparse.small_spec]; rfl
    have h_rc9 : z0q rd0 rd1 9 = [1,0,0,0,0,0,0,0,0,1,0,0] +> default := by
      have : (9 : Nat) = (((0 * 2 + 1) * 2) * 2) * 2 + 1 := rfl
      rw [this,z0I,z0H z1B,z0H z1B,z0I,z0F]
      rfl
    rw [h0,h9,z0u,h_rc9]
  rw [h_meaning]
  exact init_tm

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
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
open Solution in
theorem is_halt : IsHalt target_tm := by
  exact z2p z37 (z36 175 Forward13.seed Forward13.numerical_halt)

end BusyBeaver.M_1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RBHHH
