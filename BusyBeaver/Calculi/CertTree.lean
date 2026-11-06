/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter

/-!
# Certified Search Tree Calculus (`BusyBeaver.Calculi.CertTree`)

Compact tree-structured inductive certificates for finite reachability
and halting/non-halting state exploration in complex Busy Beaver machines.
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.CertTreeEngine

private theorem if_pos {c : Prop} [Decidable c] (hc : c) {α : Sort*} {t e : α} :
    (if c then t else e) = t := by
  simp [hc]

private theorem if_neg {c : Prop} [Decidable c] (hnc : ¬c) {α : Sort*} {t e : α} :
    (if c then t else e) = e := by
  simp [hnc]

theorem pow_one_add (u : List (Fin 2)) (n : Nat) : u ^ (1 + n) = u ++ u ^ n := by
  rw [Nat.add_comm 1 n, pow_succ_list]

def D_word (n : Nat) : List (Fin 2) := [1] ++ ([1, 1] : List (Fin 2)) ^ n ++ [0, 0]
def S_word (n : Nat) : List (Fin 2) := [1] ++ ([0, 1] : List (Fin 2)) ^ (1 + n)
def PL_word (n : Nat) : List (Fin 2) :=
  ([1, 0] : List (Fin 2)) ^ (n + 4) ++ ([1, 1] : List (Fin 2)) ^ n ++ S_word 0 ++ S_word 0

def CfgR (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A l ([0, 1, 0, 0] +> r)

def CfgL (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft B l ([1] +> r)

def CfgJ (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C l ([1, 0, 0] +> r)
theorem rot_pow_cons (a : Fin 2) (w : List (Fin 2)) (k : Nat) (s : ListBlank (Fin 2)) :
    ((a :: w) ^ k) +> (a >> s) = a >> (((w ++ [a]) ^ k) +> s) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ_list, pow_succ_list, listblank_append_right_assoc, ih]
    simp only [List.cons_append, List.nil_append, List.append_assoc,
      listblank_append_right_assoc, listblank_append_cons]

theorem rot_01 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> s) =
      (0 : Fin 2) >> ((([1, 0] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 0 [1] k s

theorem rot_10 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([0, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [0] k s

theorem rot_11 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [1] k s

theorem rot_0101 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1, 0, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> s) =
      (0 : Fin 2) >> ((([1, 0, 1, 0] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 0 [1, 0, 1] k s

theorem rot_1010 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0, 1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([0, 1, 0, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [0, 1, 0] k s

theorem rot_1101 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 1, 0, 1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([1, 0, 1, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [1, 0, 1] k s

theorem rot_1011 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0, 1, 1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([0, 1, 1, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [0, 1, 1] k s

theorem rot_0111 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1, 1, 1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> s) =
      (0 : Fin 2) >> ((([1, 1, 1, 0] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 0 [1, 1, 1] k s

theorem rot_1110 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 1, 1, 0] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> s) =
      (1 : Fin 2) >> ((([1, 1, 0, 1] : List (Fin 2)) ^ k) +> s) :=
  rot_pow_cons 1 [1, 1, 0] k s

theorem pow_two_add (u : List (Fin 2)) (n : Nat) : u ^ (2 + n) = u ++ (u ++ u ^ n) := by
  have h : 2 + n = 1 + (1 + n) := by omega
  rw [h, pow_one_add, pow_one_add]

theorem pow_add_two (u : List (Fin 2)) (n : Nat) : u ^ (n + 2) = u ++ (u ++ u ^ n) := by
  rw [Nat.add_comm n 2, pow_two_add]

theorem pow_add_four (u : List (Fin 2)) (n : Nat) : u ^ (n + 4) = u ++ (u ++ (u ++ (u ++ u ^ n))) :=
  by
  have h : n + 4 = (n + 2) + 2 := by omega
  rw [h, pow_add_two, pow_add_two]

theorem pow_mul_two (u : List (Fin 2)) (k : Nat) : u ^ (k * 2) = (u ++ u) ^ k := by
  rw [Nat.mul_comm k 2, list_pow_mul]
  simp only [pow_succ_list, pow_zero_list, List.append_nil]

macro "norm_cb" : tactic =>
  `(tactic| try simp only [CfgR, CfgL, CfgJ, D_word, S_word, PL_word,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil,
    listblank_append_right_assoc, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, default_head, default_tail,
    zero_cons_default, pow_zero_list, pow_succ_list, pow_one_add, pow_two_add, pow_add_two,
      pow_add_four, pow_mul_two,
    ones_append_cons_one, zeros_append_cons_zero, pow_append_pow, zeros_append_default,
    rot_01, rot_10, rot_11, rot_0101, rot_1010, rot_1101, rot_1011, rot_0111, rot_1110,
    Nat.zero_add, Nat.add_zero])

macro "follow" t:term : tactic =>
  `(tactic| (norm_cb; refine ReachesStar.trans $t ?_; norm_cb))

macro "nsteps" n:num : tactic =>
  `(tactic| (norm_cb; iterate $n bb_step))

macro "fsteps" : tactic =>
  `(tactic| (norm_cb; bb_steps))

def withNat {α : Type} (x : Nat) (k : Nat → α) : α :=
  match x + 1 with
  | 0 => k 0
  | v + 1 => k v

@[simp] theorem withNat_apply {α : Type} (x : Nat) (k : Nat → α) : withNat x k = k x := by
  cases x <;> rfl

-- ============================================================================
-- Section 1: Runs (Certified Symbolic RLE Half-Tapes)
-- ============================================================================


def beqFin2 (a b : Fin 2) : Bool := Nat.beq a.val b.val

theorem beqFin2_eq (a b : Fin 2) (h : beqFin2 a b = true) : a = b :=
  Fin.ext (Nat.eq_of_beq_eq_true h)

def beqFin6 (a b : Fin 6) : Bool := Nat.beq a.val b.val

theorem beqFin6_eq (a b : Fin 6) (h : beqFin6 a b = true) : a = b :=
  Fin.ext (Nat.eq_of_beq_eq_true h)

def beqListFin2 : List (Fin 2) → List (Fin 2) → Bool
  | [], [] => true
  | a :: as, b :: bs => if beqFin2 a b then beqListFin2 as bs else false
  | _, _ => false

theorem beqListFin2_eq (xs ys : List (Fin 2)) (h : beqListFin2 xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> first | rfl | contradiction
  | cons a as ih =>
    cases ys with
    | nil => contradiction
    | cons b bs =>
      dsimp [beqListFin2] at h
      cases hab : beqFin2 a b
      · rw [hab] at h; contradiction
      · rw [hab] at h; simp only [↓reduceIte] at h
        rw [beqFin2_eq a b hab, ih bs h]

inductive SymWord where
  | raw (w : List (Fin 2))
  | D (n : Nat)
  | S (n : Nat)
  | PL (n : Nat)
  deriving DecidableEq

def SymWord.toList : SymWord → List (Fin 2)
  | .raw w => w
  | .D n => D_word n
  | .S n => S_word n
  | .PL n => PL_word n

def SymWord.isEmpty : SymWord → Bool
  | .raw [] => true
  | _ => false

theorem SymWord.isEmpty_spec (w : SymWord) (h : w.isEmpty = true) : w.toList = [] := by
  cases w with
  | raw l => cases l <;> first | rfl | contradiction
  | D _ => contradiction
  | S _ => contradiction
  | PL _ => contradiction

def SymWord.beq : SymWord → SymWord → Bool
  | .raw w, .raw v => beqListFin2 w v
  | .D n, .D m => Nat.beq n m
  | .S n, .S m => Nat.beq n m
  | .PL n, .PL m => Nat.beq n m
  | _, _ => false

theorem SymWord.beq_eq (w v : SymWord) (h : SymWord.beq w v = true) : w.toList = v.toList := by
  cases w <;> cases v <;> try contradiction
  · exact beqListFin2_eq _ _ h
  · rw [Nat.eq_of_beq_eq_true h]
  · rw [Nat.eq_of_beq_eq_true h]
  · rw [Nat.eq_of_beq_eq_true h]

abbrev Runs := List (SymWord × Nat)

def Runs.denote : Runs → ListBlank (Fin 2)
  | [] => default
  | (w, n) :: xs => (w.toList ^ n) +> denote xs


def Runs.push (w : SymWord) (n : Nat) (xs : Runs) : Runs :=
  if w.isEmpty || Nat.beq n 0 then xs
  else
    match xs with
    | (v, m) :: ys =>
      if SymWord.beq w v then
        withNat (n + m) fun nm => (w, nm) :: ys
      else (w, n) :: (v, m) :: ys
    | [] => [(w, n)]

theorem Runs.push_spec (w : SymWord) (n : Nat) (xs : Runs) :
    denote (push w n xs) = (w.toList ^ n) +> denote xs := by
  dsimp only [push]
  cases he : w.isEmpty
  · cases hn : Nat.beq n 0
    · simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      cases xs with
      | nil => rfl
      | cons vm ys =>
        rcases vm with ⟨v, m⟩
        dsimp only [withNat]
        cases h : SymWord.beq w v
        · simp [denote]
        · simp [denote, ← SymWord.beq_eq w v h, pow_append_pow]
    · simp [Nat.eq_of_beq_eq_true hn]
  · simp [SymWord.isEmpty_spec w he, nil_pow]

def Runs.pop : Runs → Fin 2 × Runs
  | [] => (0, [])
  | (_, 0) :: xs => pop xs
  | (.raw [], _ + 1) :: xs => pop xs
  | (.raw (b :: rest), n + 1) :: xs =>
    (b, push (.raw rest) 1 (push (.raw (b :: rest)) n xs))
  | (.D k, n + 1) :: xs =>
    (1, push (.raw [1, 1]) k (push (.raw [0, 0]) 1 (push (.D k) n xs)))
  | (.S k, n + 1) :: xs =>
    withNat (1 + k) fun k1 =>
    (1, push (.raw [0, 1]) k1 (push (.S k) n xs))
  | (.PL k, n + 1) :: xs =>
    withNat (k + 3) fun k3 =>
    (1, push (.raw [0]) 1 (push (.raw [1, 0]) k3 (push (.raw [1,
      1]) k (push (.S 0) 2 (push (.PL k) n xs)))))

theorem Runs.pop_spec (xs : Runs) :
    denote xs = (pop xs).1 >> denote (pop xs).2 := by
  induction xs with
  | nil =>
    dsimp [pop, denote]
    exact zero_cons_default.symm
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    cases n with
    | zero =>
      dsimp [pop, denote]
      exact ih
    | succ n =>
      cases w with
      | raw l =>
        cases l with
        | nil =>
          dsimp only [pop, denote, SymWord.toList]
          rw [nil_pow, listblank_append_nil]
          exact ih
        | cons b rest =>
          dsimp only [pop, denote, SymWord.toList]
          rw [push_spec, push_spec]
          simp only [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil,
            List.cons_append, listblank_append_right_assoc, listblank_append_cons]
      | D k =>
        dsimp only [pop, denote, SymWord.toList]
        rw [push_spec, push_spec, push_spec]
        simp only [D_word, SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil,
          List.cons_append, List.nil_append, List.append_assoc,
          listblank_append_right_assoc, listblank_append_cons, listblank_append_nil]
      | S k =>
        dsimp only [pop, denote, SymWord.toList, withNat]
        rw [push_spec, push_spec]
        simp only [S_word, SymWord.toList, pow_succ_list,
          List.cons_append, List.nil_append,
          listblank_append_right_assoc, listblank_append_cons]
      | PL k =>
        dsimp only [pop, denote, SymWord.toList, withNat]
        rw [push_spec, push_spec, push_spec, push_spec, push_spec]
        dsimp only [PL_word, SymWord.toList]
        have hk4 : k + 4 = 1 + (k + 3) := by omega
        rw [hk4, pow_one_add]
        simp only [pow_succ_list, pow_zero_list, List.append_nil,
          List.cons_append, List.nil_append, List.append_assoc,
          listblank_append_right_assoc, listblank_append_cons, listblank_append_nil]

def Runs.remove : List (Fin 2) → Runs → Option Runs
  | [], xs => some xs
  | b :: w, xs =>
    let (c, ys) := pop xs
    if beqFin2 b c then remove w ys else none

theorem Runs.remove_spec (w : List (Fin 2)) (xs ys : Runs)
    (h : remove w xs = some ys) : denote xs = w +> denote ys := by
  induction w generalizing xs with
  | nil =>
    simp only [remove, Option.some.injEq] at h
    subst h; rfl
  | cons b w ih =>
    dsimp only [remove] at h
    have hp := pop_spec xs
    rcases hpop : pop xs with ⟨c, zs⟩
    rw [hpop] at h hp
    dsimp only at h hp
    cases hbc : beqFin2 b c
    · rw [hbc] at h; simp at h
    · rw [hbc] at h; simp only [↓reduceIte] at h
      rw [beqFin2_eq b c hbc, hp, ih zs h, listblank_append_cons]


def strip_prefix : List (Fin 2) → List (Fin 2) → Option (List (Fin 2))
  | [], ys => some ys
  | x :: xs, y :: ys => if beqFin2 x y then strip_prefix xs ys else none
  | _ :: _, [] => none

theorem strip_prefix_spec (xs ys zs : List (Fin 2)) (h : strip_prefix xs ys = some zs) :
    ys = xs ++ zs := by
  induction xs generalizing ys with
  | nil =>
    dsimp [strip_prefix] at h
    injection h with h
  | cons x xs ih =>
    cases ys with
    | nil => simp [strip_prefix] at h
    | cons y ys =>
      dsimp [strip_prefix] at h
      cases hxy : beqFin2 x y
      · rw [hxy] at h; simp at h
      · rw [hxy] at h; simp only [↓reduceIte] at h
        rw [beqFin2_eq x y hxy, ih ys h, List.cons_append]

def strip_many : Nat → List (Fin 2) → List (Fin 2) → Nat × List (Fin 2)
  | 0, _, v => (0, v)
  | limit + 1, u, v =>
    match strip_prefix u v with
    | some v' =>
      let (k, r) := strip_many limit u v'
      withNat (1 + k) fun k' => (k', r)
    | none => (0, v)

theorem strip_many_spec (limit : Nat) (u v : List (Fin 2)) :
    let (k, r) := strip_many limit u v
    k ≤ limit ∧ v = (u ^ k) ++ r := by
  induction limit generalizing v with
  | zero => simp [strip_many]
  | succ limit ih =>
    dsimp only [strip_many]
    cases hsp : strip_prefix u v with
    | none => simp 
    | some v' =>
      dsimp only
      have hv := strip_prefix_spec u v v' hsp
      have ih' := ih v'
      rcases hsm : strip_many limit u v' with ⟨k, r⟩
      rw [hsm] at ih'
      dsimp only [withNat] at ih' ⊢
      refine ⟨by omega, ?_⟩
      rw [hv, ih'.2, pow_one_add, List.append_assoc]

theorem commute_power (x v w : List (Fin 2)) (a b k : Nat)
    (h : x ++ (v ^ a) = (w ^ b) ++ x) :
    x ++ (v ^ (k * a)) = (w ^ (k * b)) ++ x := by
  induction k with
  | zero => simp 
  | succ k ih =>
    have hka : (k + 1) * a = a + k * a := by ring
    have hkb : (k + 1) * b = b + k * b := by ring
    rw [hka, hkb, list_pow_add, list_pow_add, ← List.append_assoc, h, List.append_assoc, ih,
      List.append_assoc]

def first_bit_eq : List (Fin 2) → List (Fin 2) → List (Fin 2) → Bool
  | x :: _, _, w :: _ => beqFin2 x w
  | [], v :: _, w :: _ => beqFin2 v w
  | _, _, _ => false

def Runs.skip_block (w : List (Fin 2)) (limit : Nat) (x v : List (Fin 2)) (m : Nat) (ys : Runs) :
    Option (Nat × Runs) :=
  if first_bit_eq x v w then
    let a := w.length
    if Nat.ble a m && Nat.ble a 4 then
      let b := v.length
      if Nat.ble b 4 then
        if beqListFin2 (x ++ (v ^ a)) ((w ^ b) ++ x) then
          withNat (Nat.min (limit / b) (m / a)) fun k =>
          if Nat.blt 0 k then
            withNat (k * b) fun kb =>
            withNat (k * a) fun ka =>
            if Nat.ble kb limit then
              if Nat.ble ka m then
                withNat (m - ka) fun rem =>
                some (kb, push (.raw x) 1 (push (.raw v) rem ys))
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem Runs.skip_block_spec (w : List (Fin 2)) (limit : Nat) (x v : List (Fin 2)) (m : Nat)
    (ys : Runs) (n : Nat) (zs : Runs)
    (h : skip_block w limit x v m ys = some (n, zs)) :
    n ≤ limit ∧ (x +> ((v ^ m) +> denote ys)) = ((w ^ n) +> denote zs) := by
  dsimp only [skip_block] at h
  simp only [withNat] at h
  generalize hk : Nat.min (limit / v.length) (m / w.length) = k at h
  cases hfb : first_bit_eq x v w <;> rw [hfb] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases ham : Nat.ble w.length m && Nat.ble w.length 4 <;> rw [ham] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases hb4 : Nat.ble v.length 4 <;> rw [hb4] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases heq : beqListFin2 (x ++ (v ^ w.length)) ((w ^ v.length) ++ x) <;> rw [heq] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases hk0 : Nat.blt 0 k <;> rw [hk0] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases hkb : Nat.ble (k * v.length) limit <;> rw [hkb] at h
  · contradiction
  simp only [↓reduceIte] at h
  cases hka : Nat.ble (k * w.length) m <;> rw [hka] at h
  · contradiction
  simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩
  have hkb' : k * v.length ≤ limit := Nat.le_of_ble_eq_true hkb
  have hka' : k * w.length ≤ m := Nat.le_of_ble_eq_true hka
  refine ⟨hkb', ?_⟩
  rw [push_spec, push_spec]
  dsimp only [SymWord.toList]
  have hm : m = k * w.length + (m - k * w.length) := by omega
  conv_lhs => rw [hm, list_pow_add, listblank_append_right_assoc]
  rw [← listblank_append_right_assoc x (v ^ (k * w.length))]
  rw [commute_power x v w w.length v.length k (beqListFin2_eq _ _ heq)]
  simp only [pow_succ_list, pow_zero_list, List.append_nil, listblank_append_right_assoc]

def Runs.skip_periodic (w : List (Fin 2)) (n : Nat) : Runs → Option (Nat × Runs)
  | (.raw x, 1) :: (.raw v, m) :: ys => skip_block w n x v m ys
  | (.raw v, m) :: ys => skip_block w n [] v m ys
  | _ => none

theorem Runs.skip_periodic_spec (w : List (Fin 2)) (n : Nat) (xs : Runs) (k : Nat) (ys : Runs)
    (h : skip_periodic w n xs = some (k, ys)) :
    k ≤ n ∧ denote xs = (w ^ k) +> denote ys := by
  cases xs with
  | nil => simp [skip_periodic] at h
  | cons xm rest =>
    rcases xm with ⟨xw, m1⟩
    cases xw with
    | D _ => simp [skip_periodic] at h
    | S _ => simp [skip_periodic] at h
    | PL _ => simp [skip_periodic] at h
    | raw x =>
      cases m1 with
      | zero =>
        dsimp [skip_periodic] at h
        have hs := skip_block_spec w n [] x 0 rest k ys h
        simpa [denote, SymWord.toList] using hs
      | succ m1' =>
        cases m1' with
        | zero =>
          cases rest with
          | nil =>
            dsimp [skip_periodic] at h
            have hs := skip_block_spec w n [] x 1 [] k ys h
            simpa [denote, SymWord.toList] using hs
          | cons vm ys' =>
            rcases vm with ⟨vw, m⟩
            cases vw with
            | D _ =>
              dsimp [skip_periodic] at h
              have hs := skip_block_spec w n [] x 1 ((.D _, m) :: ys') k ys h
              simpa [denote, SymWord.toList] using hs
            | S _ =>
              dsimp [skip_periodic] at h
              have hs := skip_block_spec w n [] x 1 ((.S _, m) :: ys') k ys h
              simpa [denote, SymWord.toList] using hs
            | PL _ =>
              dsimp [skip_periodic] at h
              have hs := skip_block_spec w n [] x 1 ((.PL _, m) :: ys') k ys h
              simpa [denote, SymWord.toList] using hs
            | raw v =>
              dsimp [skip_periodic] at h
              have hs := skip_block_spec w n x v m ys' k ys h
              simpa [denote, SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil] using hs
        | succ m1'' =>
          dsimp [skip_periodic] at h
          have hs := skip_block_spec w n [] x (m1'' + 2) rest k ys h
          simpa [denote, SymWord.toList] using hs

def Runs.skip (w : SymWord) (n : Nat) (xs : Runs) : Option (Nat × Runs) :=
  match xs with
  | (v, m) :: ys =>
    if SymWord.beq w v then
      withNat (Nat.min n m) fun k =>
      withNat (m - k) fun rem =>
      some (k, push v rem ys)
    else
      match w, v with
      | .raw wl, .raw vl =>
        match skip_periodic wl n xs with
        | some res => some res
        | none =>
          if Nat.blt 0 m then
            let (k, v_rest) := strip_many (Nat.min n 512) wl vl
            if Nat.blt 0 k then
              withNat (m - 1) fun m' =>
              some (k, push (.raw v_rest) 1 (push (.raw vl) m' ys))
            else none
          else none
      | _, _ => none
  | [] => none

theorem Runs.skip_spec (w : SymWord) (n : Nat) (xs : Runs) (k : Nat) (ys : Runs)
    (h : skip w n xs = some (k, ys)) :
    k ≤ n ∧ denote xs = (w.toList ^ k) +> denote ys := by
  cases xs with
  | nil => simp [skip] at h
  | cons vm rest =>
    rcases vm with ⟨v, m⟩
    dsimp only [skip, withNat] at h
    cases hwv : SymWord.beq w v
    · rw [hwv] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases w <;> cases v <;> try contradiction
      rename_i wl vl
      dsimp only [SymWord.toList] at h ⊢
      cases hsp : skip_periodic wl n ((.raw vl, m) :: rest) with
      | some res =>
        rw [hsp] at h; simp only [Option.some.injEq] at h; subst h
        exact skip_periodic_spec wl n ((.raw vl, m) :: rest) k ys hsp
      | none =>
        rw [hsp] at h; dsimp only at h
        cases hm0 : Nat.blt 0 m <;> rw [hm0] at h
        · contradiction
        simp only [↓reduceIte] at h
        have hm0' : 0 < m := Nat.le_of_ble_eq_true hm0
        have hsm := strip_many_spec (Nat.min n 512) wl vl
        rcases hstrip : strip_many (Nat.min n 512) wl vl with ⟨k', v_rest⟩
        rw [hstrip] at h hsm
        dsimp only at h hsm
        cases hk0 : Nat.blt 0 k' <;> rw [hk0] at h
        · contradiction
        simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        have hmin : Nat.min n 512 ≤ n := Nat.min_le_left n 512
        refine ⟨by omega, ?_⟩
        dsimp only [denote]
        rw [push_spec, push_spec]
        dsimp only [SymWord.toList]
        have hm1 : m = 1 + (m - 1) := by omega
        conv_lhs => rw [hm1, pow_one_add, listblank_append_right_assoc]
        simp only [pow_succ_list, pow_zero_list, List.append_nil,
          ← listblank_append_right_assoc (wl ^ k') v_rest, ← hsm.2]
    · rw [hwv] at h; simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rw [SymWord.beq_eq w v hwv]
      refine ⟨Nat.min_le_left n m, ?_⟩
      dsimp only [denote]
      rw [push_spec, pow_append_pow]
      have hmin : Nat.min n m ≤ m := Nat.min_le_right n m
      have hm : Nat.min n m + (m - Nat.min n m) = m := by omega
      rw [hm]

def Runs.remove_one : Nat → List (Fin 2) → Runs → Option Runs
  | _, [], xs => some xs
  | 0, b :: w, xs => remove (b :: w) xs
  | fuel + 1, b :: w, xs =>
    match xs with
    | (.raw v, m) :: ys =>
      if Nat.beq m 1 then
        match strip_prefix v (b :: w) with
        | some w_rest => remove_one fuel w_rest ys
        | none =>
          let (c, zs) := pop xs
          if beqFin2 b c then remove_one fuel w zs else none
      else if Nat.blt 0 m then
        let (k, w_rest) := strip_many (Nat.min m 512) v (b :: w)
        if Nat.blt 0 k then
          withNat (m - k) fun rem =>
          remove_one fuel w_rest (push (.raw v) rem ys)
        else
          let (c, zs) := pop xs
          if beqFin2 b c then remove_one fuel w zs else none
      else remove (b :: w) xs
    | _ :: _ =>
      let (c, zs) := pop xs
      if beqFin2 b c then remove_one fuel w zs else none
    | [] => remove (b :: w) []

theorem Runs.remove_one_spec (fuel : Nat) (w : List (Fin 2)) (xs ys : Runs)
    (h : remove_one fuel w xs = some ys) : denote xs = w +> denote ys := by
  induction fuel generalizing w xs with
  | zero =>
    cases w with
    | nil => simp only [remove_one, Option.some.injEq] at h; subst h; rfl
    | cons b w' => exact remove_spec (b :: w') xs ys h
  | succ fuel ih =>
    cases w with
    | nil => simp only [remove_one, Option.some.injEq] at h; subst h; rfl
    | cons b w' =>
      cases xs with
      | nil => exact remove_spec (b :: w') [] ys h
      | cons vm rest =>
        rcases vm with ⟨v, m⟩
        cases v with
        | raw vl =>
          dsimp only [remove_one, withNat] at h
          cases hm1 : Nat.beq m 1 <;> rw [hm1] at h
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            cases hm : Nat.blt 0 m <;> rw [hm] at h
            · simp only [Bool.false_eq_true, ↓reduceIte] at h
              exact remove_spec (b :: w') ((.raw vl, m) :: rest) ys h
            · simp only [↓reduceIte] at h
              have hm' : 0 < m := Nat.le_of_ble_eq_true hm
              have hsm := strip_many_spec (Nat.min m 512) vl (b :: w')
              rcases hstrip : strip_many (Nat.min m 512) vl (b :: w') with ⟨k, w_rest⟩
              rw [hstrip] at h hsm
              dsimp only at h hsm
              cases hk : Nat.blt 0 k <;> rw [hk] at h
              · simp only [Bool.false_eq_true, ↓reduceIte] at h
                have hp := pop_spec ((.raw vl, m) :: rest)
                rcases hpop : pop ((.raw vl, m) :: rest) with ⟨c, zs⟩
                rw [hpop] at h hp
                dsimp only at h hp
                cases hbc : beqFin2 b c <;> rw [hbc] at h
                · contradiction
                · simp only [↓reduceIte] at h
                  rw [beqFin2_eq b c hbc, hp, ih w' zs h, listblank_append_cons]
              · simp only [↓reduceIte] at h
                have ih' := ih w_rest (push (.raw vl) (m - k) rest) h
                rw [push_spec] at ih'
                dsimp only [denote, SymWord.toList] at ih' ⊢
                have hmin : Nat.min m 512 ≤ m := Nat.min_le_left m 512
                have hmk : m = k + (m - k) := by omega
                rw [hmk, list_pow_add, listblank_append_right_assoc, ih',
                  ← listblank_append_right_assoc, ← hsm.2]
          · simp only [↓reduceIte] at h
            cases hsp : strip_prefix vl (b :: w') with
            | none =>
              rw [hsp] at h; dsimp only at h
              have hp := pop_spec ((.raw vl, m) :: rest)
              rcases hpop : pop ((.raw vl, m) :: rest) with ⟨c, zs⟩
              rw [hpop] at h hp
              dsimp only at h hp
              cases hbc : beqFin2 b c <;> rw [hbc] at h
              · contradiction
              · simp only [↓reduceIte] at h
                rw [beqFin2_eq b c hbc, hp, ih w' zs h, listblank_append_cons]
            | some w_rest =>
              rw [hsp] at h; dsimp only at h
              have ih' := ih w_rest rest h
              dsimp only [denote, SymWord.toList]
              rw [Nat.eq_of_beq_eq_true hm1, pow_succ_list, pow_zero_list, List.append_nil,
                strip_prefix_spec vl (b :: w') w_rest hsp, listblank_append_right_assoc, ih']
        | D d =>
          dsimp only [remove_one] at h
          have hp := pop_spec ((.D d, m) :: rest)
          rcases hpop : pop ((.D d, m) :: rest) with ⟨c, zs⟩
          rw [hpop] at h hp; dsimp only at h hp
          cases hbc : beqFin2 b c <;> rw [hbc] at h
          · contradiction
          · simp only [↓reduceIte] at h
            rw [beqFin2_eq b c hbc, hp, ih w' zs h, listblank_append_cons]
        | S d =>
          dsimp only [remove_one] at h
          have hp := pop_spec ((.S d, m) :: rest)
          rcases hpop : pop ((.S d, m) :: rest) with ⟨c, zs⟩
          rw [hpop] at h hp; dsimp only at h hp
          cases hbc : beqFin2 b c <;> rw [hbc] at h
          · contradiction
          · simp only [↓reduceIte] at h
            rw [beqFin2_eq b c hbc, hp, ih w' zs h, listblank_append_cons]
        | PL d =>
          dsimp only [remove_one] at h
          have hp := pop_spec ((.PL d, m) :: rest)
          rcases hpop : pop ((.PL d, m) :: rest) with ⟨c, zs⟩
          rw [hpop] at h hp; dsimp only at h hp
          cases hbc : beqFin2 b c <;> rw [hbc] at h
          · contradiction
          · simp only [↓reduceIte] at h
            rw [beqFin2_eq b c hbc, hp, ih w' zs h, listblank_append_cons]


def remove_prefix (w : List (Fin 2)) (xs : Runs) : Option Runs :=
  match w, xs with
  | [], _ => some xs
  | b :: _, (.raw (b' :: v_rest), m) :: ys =>
    if beqFin2 b b' then
      if Nat.beq m 1 && beqListFin2 w (b' :: v_rest) then
        some ys
      else Runs.remove_one 16 w xs
    else none
  | b :: _, (.D _, _ + 1) :: _ =>
    if beqFin2 b 1 then Runs.remove_one 16 w xs else none
  | b :: _, (.S _, _ + 1) :: _ =>
    if beqFin2 b 1 then Runs.remove_one 16 w xs else none
  | b :: _, (.PL _, _ + 1) :: _ =>
    if beqFin2 b 1 then Runs.remove_one 16 w xs else none
  | _, _ => Runs.remove_one 16 w xs

theorem remove_prefix_spec (w : List (Fin 2)) (xs ys : Runs)
    (h : remove_prefix w xs = some ys) : Runs.denote xs = w +> Runs.denote ys := by
  unfold remove_prefix at h
  rcases w with _ | ⟨b, w_rest⟩
  · simp only [Option.some.injEq] at h; subst h; rfl
  rcases xs with _ | ⟨⟨v, m⟩, rest⟩
  · exact Runs.remove_one_spec 16 (b :: w_rest) [] ys h
  cases v with
  | raw vl =>
    rcases vl with _ | ⟨b', v_rest⟩
    · exact Runs.remove_one_spec 16 (b :: w_rest) ((.raw [], m) :: rest) ys h
    dsimp only at h
    cases hbb : beqFin2 b b' <;> rw [hbb] at h
    · contradiction
    simp only [↓reduceIte] at h
    cases hm1 : Nat.beq m 1 && beqListFin2 (b :: w_rest) (b' :: v_rest) <;> rw [hm1] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      exact Runs.remove_one_spec 16 (b :: w_rest) ((.raw (b' :: v_rest), m) :: rest) ys h
    · simp only [↓reduceIte, Option.some.injEq] at h; subst h
      rcases Bool.and_eq_true_iff.mp hm1 with ⟨hm, hwv⟩
      rw [Nat.eq_of_beq_eq_true hm, ← beqListFin2_eq _ _ hwv]
      simp [Runs.denote, SymWord.toList, pow_succ_list]
  | D d =>
    cases m with
    | zero => exact Runs.remove_one_spec 16 (b :: w_rest) ((.D d, 0) :: rest) ys h
    | succ m' =>
      dsimp only at h
      split_ifs at h
      exact Runs.remove_one_spec 16 (b :: w_rest) ((.D d, m' + 1) :: rest) ys h
  | S d =>
    cases m with
    | zero => exact Runs.remove_one_spec 16 (b :: w_rest) ((.S d, 0) :: rest) ys h
    | succ m' =>
      dsimp only at h
      split_ifs at h
      exact Runs.remove_one_spec 16 (b :: w_rest) ((.S d, m' + 1) :: rest) ys h
  | PL d =>
    cases m with
    | zero => exact Runs.remove_one_spec 16 (b :: w_rest) ((.PL d, 0) :: rest) ys h
    | succ m' =>
      dsimp only at h
      split_ifs at h
      exact Runs.remove_one_spec 16 (b :: w_rest) ((.PL d, m' + 1) :: rest) ys h

def Runs.remove_fast_raw : Nat → List (Fin 2) → Nat → Runs → Option Runs
  | _, _, 0, xs => some xs
  | 0, _, _ + 1, _ => none
  | _fuel + 1, [], _ + 1, xs => some xs
  | fuel + 1, b :: wl, n + 1, xs =>
    match skip (.raw (b :: wl)) (n + 1) xs with
    | some (k, ys) =>
      withNat (n + 1 - k) fun rem =>
      remove_fast_raw fuel (b :: wl) rem ys
    | none =>
      match remove_one 16 (b :: wl) xs with
      | some ys => remove_fast_raw fuel (b :: wl) n ys
      | none => none

theorem Runs.remove_fast_raw_spec (fuel : Nat) (wl : List (Fin 2)) (n : Nat) (xs ys : Runs)
    (h : remove_fast_raw fuel wl n xs = some ys) : denote xs = (wl ^ n) +> denote ys := by
  induction fuel generalizing n xs with
  | zero =>
    cases n with
    | zero => simp only [remove_fast_raw, Option.some.injEq] at h; subst h; rfl
    | succ n => simp [remove_fast_raw] at h
  | succ fuel ih =>
    cases n with
    | zero => simp only [remove_fast_raw, Option.some.injEq] at h; subst h; rfl
    | succ n =>
      cases wl with
      | nil =>
        simp only [remove_fast_raw, Option.some.injEq] at h; subst h
        simp [nil_pow]
      | cons b wl' =>
        dsimp only [remove_fast_raw, withNat] at h
        cases hsk : skip (.raw (b :: wl')) (n + 1) xs with
        | some kys =>
          rcases kys with ⟨k, zs⟩
          rw [hsk] at h; dsimp only at h
          rcases skip_spec (.raw (b :: wl')) (n + 1) xs k zs hsk with ⟨hk, hden⟩
          dsimp only [SymWord.toList] at hden
          rw [hden, ih (n + 1 - k) zs h, pow_append_pow]
          have hnk : k + (n + 1 - k) = n + 1 := by omega
          rw [hnk]
        | none =>
          rw [hsk] at h; dsimp only at h
          cases hro : remove_one 16 (b :: wl') xs with
          | none => rw [hro] at h; contradiction
          | some zs =>
            rw [hro] at h; dsimp only at h
            rw [remove_one_spec 16 (b :: wl') xs zs hro, ih n zs h,
              pow_succ_list, listblank_append_right_assoc]

def Runs.exact_head (w : SymWord) (n : Nat) : Runs → Option Runs
  | (v, m) :: ys =>
    if SymWord.beq w v then
      if Nat.beq n m then some ys
      else if Nat.blt n m then
        withNat (m - n) fun rem => some ((v, rem) :: ys)
      else none
    else none
  | [] => none

theorem Runs.exact_head_spec (w : SymWord) (n : Nat) (xs ys : Runs)
    (h : exact_head w n xs = some ys) : denote xs = (w.toList ^ n) +> denote ys := by
  cases xs with
  | nil => contradiction
  | cons vm rest =>
    rcases vm with ⟨v, m⟩
    dsimp only [exact_head, withNat] at h
    cases hwv : SymWord.beq w v <;> rw [hwv] at h
    · contradiction
    simp only [↓reduceIte] at h
    cases hnm : Nat.beq n m <;> rw [hnm] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hlt : Nat.blt n m <;> rw [hlt] at h
      · contradiction
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      dsimp only [denote]
      rw [SymWord.beq_eq w v hwv, pow_append_pow]
      have hlt' : n < m := Nat.le_of_ble_eq_true hlt
      have hm : n + (m - n) = m := by omega
      rw [hm]
    · simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      dsimp only [denote]
      rw [SymWord.beq_eq w v hwv, Nat.eq_of_beq_eq_true hnm]

theorem pow_11_eq_pow_1 (m : Nat) :
    (([1, 1] : List (Fin 2)) ^ m) = ([1] : List (Fin 2)) ^ (m * 2) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm : (m + 1) * 2 = 2 + m * 2 := by omega
    rw [pow_succ_list, ih, hm, list_pow_add]
    rfl

theorem pow_111_eq_pow_1 (m : Nat) :
    (([1, 1, 1] : List (Fin 2)) ^ m) = ([1] : List (Fin 2)) ^ (m * 3) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hm : (m + 1) * 3 = 3 + m * 3 := by omega
    rw [pow_succ_list, ih, hm, list_pow_add]
    rfl

def Runs.remove_ones : Nat → Nat → Runs → Option Runs
  | _, 0, xs => some xs
  | 0, _ + 1, _ => none
  | _ + 1, _ + 1, [] => none
  | fuel + 1, k + 1, (v, m) :: ys =>
    if SymWord.beq v (.raw [1]) && Nat.blt 0 m then
      withNat (Nat.min (k + 1) m) fun tk =>
      withNat (m - tk) fun rem_m =>
      withNat (k + 1 - tk) fun rem_k =>
      remove_ones fuel rem_k (push (.raw [1]) rem_m ys)
    else if SymWord.beq v (.raw [1, 1]) && Nat.blt 0 m then
      withNat (m * 2) fun m2 =>
      if Nat.ble m2 (k + 1) then
        withNat (k + 1 - m2) fun rem_k =>
        remove_ones fuel rem_k ys
      else
        withNat (m2 - (k + 1)) fun diff =>
        withNat (diff / 2) fun q =>
        if Nat.beq (diff % 2) 0 then
          some (push (.raw [1, 1]) q ys)
        else
          some (push (.raw [1]) 1 (push (.raw [1, 1]) q ys))
    else
      let (b, zs) := pop ((v, m) :: ys)
      if beqFin2 1 b then remove_ones fuel k zs else none

theorem Runs.remove_ones_spec (fuel k : Nat) (xs ys : Runs)
    (h : remove_ones fuel k xs = some ys) : denote xs = (([1] : List (Fin 2)) ^ k) +> denote ys :=
      by
  induction fuel generalizing k xs with
  | zero =>
    cases k with
    | zero => simp only [remove_ones, Option.some.injEq] at h; subst h; rfl
    | succ k => simp [remove_ones] at h
  | succ fuel ih =>
    cases k with
    | zero => simp only [remove_ones, Option.some.injEq] at h; subst h; rfl
    | succ k =>
      cases xs with
      | nil => simp [remove_ones] at h
      | cons vm rest =>
        rcases vm with ⟨v, m⟩
        dsimp only [remove_ones, withNat] at h
        cases hc1 : SymWord.beq v (.raw [1]) && Nat.blt 0 m <;> rw [hc1] at h
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hc2 : SymWord.beq v (.raw [1, 1]) && Nat.blt 0 m <;> rw [hc2] at h
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            have hp := pop_spec ((v, m) :: rest)
            rcases hpop : pop ((v, m) :: rest) with ⟨b, zs⟩
            rw [hpop] at h hp
            dsimp only at h hp
            cases hb : beqFin2 1 b <;> rw [hb] at h
            · contradiction
            · simp only [↓reduceIte] at h
              rw [hp, ← beqFin2_eq 1 b hb, ih k zs h, pow_succ_list]
              simp only [List.cons_append, List.nil_append, listblank_append_cons]
          · simp only [↓reduceIte] at h
            rcases Bool.and_eq_true_iff.mp hc2 with ⟨hv, hm⟩
            have hv' : v.toList = [1, 1] := SymWord.beq_eq v (.raw [1, 1]) hv
            dsimp only [denote]
            rw [hv', pow_11_eq_pow_1 m]
            cases hle : Nat.ble (m * 2) (k + 1) <;> rw [hle] at h
            · simp only [Bool.false_eq_true, ↓reduceIte] at h
              have hlt : k + 1 < m * 2 := Nat.gt_of_not_le (fun hle' => by
                rw [Nat.ble_eq.mpr hle'] at hle; contradiction)
              cases hmod : Nat.beq ((m * 2 - (k + 1)) % 2) 0 <;> rw [hmod] at h
              · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at h
                subst h
                rw [push_spec, push_spec]
                dsimp only [SymWord.toList]
                rw [pow_11_eq_pow_1, pow_append_pow, pow_append_pow]
                have hmod' : (m * 2 - (k + 1)) % 2 ≠ 0 := fun h0 => by
                  rw [Nat.beq_eq.mpr h0] at hmod; contradiction
                have hm2 : m * 2 = k + 1 + 1 + (m * 2 - (k + 1)) / 2 * 2 := by omega
                conv_lhs => rw [hm2]
              · simp only [↓reduceIte, Option.some.injEq] at h
                subst h
                rw [push_spec]
                dsimp only [SymWord.toList]
                rw [pow_11_eq_pow_1, pow_append_pow]
                have hmod' := Nat.eq_of_beq_eq_true hmod
                have hm2 : m * 2 = k + 1 + (m * 2 - (k + 1)) / 2 * 2 := by omega
                conv_lhs => rw [hm2]
            · simp only [↓reduceIte] at h
              have hle' : m * 2 ≤ k + 1 := Nat.le_of_ble_eq_true hle
              rw [ih (k + 1 - m * 2) rest h, pow_append_pow]
              have hk : m * 2 + (k + 1 - m * 2) = k + 1 := by omega
              rw [hk]
        · simp only [↓reduceIte] at h
          rcases Bool.and_eq_true_iff.mp hc1 with ⟨hv, hm⟩
          have hv' : v.toList = [1] := SymWord.beq_eq v (.raw [1]) hv
          have ih' :=
            ih (k + 1 - Nat.min (k + 1) m) (push (.raw [1]) (m - Nat.min (k + 1) m) rest) h
          rw [push_spec] at ih'
          dsimp only [SymWord.toList] at ih'
          dsimp only [denote]
          have hmin1 : Nat.min (k + 1) m ≤ m := Nat.min_le_right (k + 1) m
          have hmin2 : Nat.min (k + 1) m ≤ k + 1 := Nat.min_le_left (k + 1) m
          have hm_eq : m = Nat.min (k + 1) m + (m - Nat.min (k + 1) m) := by omega
          have hk_eq : Nat.min (k + 1) m + (k + 1 - Nat.min (k + 1) m) = k + 1 := by omega
          rw [hv', hm_eq, list_pow_add, listblank_append_right_assoc, ih', pow_append_pow, hk_eq]

def Runs.remove_sym_one (w : SymWord) (xs : Runs) : Option Runs :=
  match w with
  | .raw wl => remove_one 16 wl xs
  | .D n =>
    withNat (1 + n * 2) fun n2_1 =>
    match remove_ones 16 n2_1 xs with
    | some xs2 => remove_one 16 [0, 0] xs2
    | none => none
  | .S n =>
    withNat (1 + n) fun n1 =>
    match exact_head (.raw [1, 0]) n1 xs with
    | some xs1 => remove_ones 16 1 xs1
    | none =>
      match remove_ones 16 1 xs with
      | some xs1 => remove_fast_raw 16 [0, 1] n1 xs1
      | none => none
  | .PL n =>
    withNat (n + 4) fun n4 =>
    match remove_fast_raw 16 [1, 0] n4 xs with
    | some xs1 =>
      match remove_fast_raw 16 [1, 1] n xs1 with
      | some xs2 => remove_one 16 [1, 0, 1, 1, 0, 1] xs2
      | none => none
    | none => none

theorem Runs.remove_sym_one_spec (w : SymWord) (xs ys : Runs)
    (h : remove_sym_one w xs = some ys) : denote xs = w.toList +> denote ys := by
  cases w with
  | raw wl => exact remove_one_spec 16 wl xs ys h
  | D n =>
    dsimp only [remove_sym_one, SymWord.toList, D_word, withNat] at h ⊢
    cases h1 : remove_ones 16 (1 + n * 2) xs <;> rw [h1] at h
    · contradiction
    rename_i xs2; dsimp only at h
    rw [remove_ones_spec 16 (1 + n * 2) xs xs2 h1,
        remove_one_spec 16 [0, 0] xs2 ys h,
        pow_one_add, ← pow_11_eq_pow_1 n]
    simp only [List.append_assoc, listblank_append_right_assoc]
  | S n =>
    dsimp only [remove_sym_one, SymWord.toList, S_word, withNat] at h ⊢
    cases hex : exact_head (.raw [1, 0]) (1 + n) xs with
    | some xs1 =>
      rw [hex] at h; dsimp only at h
      have h1 := exact_head_spec (.raw [1, 0]) (1 + n) xs xs1 hex
      have h2 := remove_ones_spec 16 1 xs1 ys h
      dsimp only [SymWord.toList] at h1
      rw [pow_succ_list, pow_zero_list, List.append_nil,
        listblank_append_cons, listblank_append_nil] at h2
      rw [h1, h2, rot_10 (1 + n) (denote ys)]
      simp only [List.cons_append, List.nil_append, listblank_append_cons]
    | none =>
      rw [hex] at h; dsimp only at h
      cases h1 : remove_ones 16 1 xs <;> rw [h1] at h
      · contradiction
      rename_i xs1; dsimp only at h
      rw [remove_ones_spec 16 1 xs xs1 h1,
          remove_fast_raw_spec 16 [0, 1] (1 + n) xs1 ys h]
      simp only [pow_succ_list, pow_zero_list, List.append_nil, listblank_append_right_assoc]
  | PL n =>
    dsimp only [remove_sym_one, SymWord.toList, PL_word, S_word, withNat] at h ⊢
    cases h1 : remove_fast_raw 16 [1, 0] (n + 4) xs <;> rw [h1] at h
    · contradiction
    rename_i xs1; dsimp only at h
    cases h2 : remove_fast_raw 16 [1, 1] n xs1 <;> rw [h2] at h
    · contradiction
    rename_i xs2; dsimp only at h
    rw [remove_fast_raw_spec 16 [1, 0] (n + 4) xs xs1 h1,
        remove_fast_raw_spec 16 [1, 1] n xs1 xs2 h2,
        remove_one_spec 16 [1, 0, 1, 1, 0, 1] xs2 ys h]
    simp only [pow_succ_list, pow_zero_list, List.append_nil, List.cons_append, List.nil_append,
      List.append_assoc, listblank_append_right_assoc, listblank_append_cons]

def Runs.remove_fast : Nat → SymWord → Nat → Runs → Option Runs
  | _, _, 0, xs => some xs
  | 0, _, _ + 1, _ => none
  | fuel + 1, w, n + 1, xs =>
    match exact_head w (n + 1) xs with
    | some ys => some ys
    | none =>
      if w.isEmpty then some xs
      else
        match skip w (n + 1) xs with
        | some (k, ys) =>
          withNat (n + 1 - k) fun rem =>
          remove_fast fuel w rem ys
        | none =>
          match remove_sym_one w xs with
          | some ys => remove_fast fuel w n ys
          | none => none

theorem Runs.remove_fast_spec (fuel : Nat) (w : SymWord) (n : Nat) (xs ys : Runs)
    (h : remove_fast fuel w n xs = some ys) : denote xs = (w.toList ^ n) +> denote ys := by
  induction fuel generalizing n xs with
  | zero =>
    cases n with
    | zero =>
      simp only [remove_fast, Option.some.injEq] at h; subst h; rfl
    | succ n => simp [remove_fast] at h
  | succ fuel ih =>
    cases n with
    | zero =>
      simp only [remove_fast, Option.some.injEq] at h; subst h; rfl
    | succ n =>
      dsimp only [remove_fast, withNat] at h
      cases hex : exact_head w (n + 1) xs with
      | some zs =>
        rw [hex] at h; simp only [Option.some.injEq] at h; subst h
        exact exact_head_spec w (n + 1) xs zs hex
      | none =>
        rw [hex] at h; dsimp only at h
        cases he : w.isEmpty
        · rw [he] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hsk : skip w (n + 1) xs with
          | some kys =>
            rcases kys with ⟨k, zs⟩
            rw [hsk] at h; dsimp only at h
            rcases skip_spec w (n + 1) xs k zs hsk with ⟨hk, hden⟩
            rw [hden, ih (n + 1 - k) zs h, pow_append_pow]
            have hnk : k + (n + 1 - k) = n + 1 := by omega
            rw [hnk]
          | none =>
            rw [hsk] at h; dsimp only at h
            cases hro : remove_sym_one w xs with
            | none => rw [hro] at h; simp at h
            | some zs =>
              rw [hro] at h; dsimp only at h
              rw [remove_sym_one_spec w xs zs hro, ih n zs h,
                pow_succ_list, listblank_append_right_assoc]
        · rw [he] at h; simp only [↓reduceIte, Option.some.injEq] at h; subst h
          simp [SymWord.isEmpty_spec w he, nil_pow]

-- ============================================================================
-- Section 2: RunMachine & CBExec
-- ============================================================================

structure RMConfig where
  left : Runs
  right : Runs
  state : Fin 6
  dir : Dir

def RMConfig.denote (c : RMConfig) : Cfg (Fin 2) (Fin 6) :=
  match c.dir with
  | Dir.left => Cfg.headLeft c.state (Runs.denote c.left) (Runs.denote c.right)
  | Dir.right => Cfg.headRight c.state (Runs.denote c.left) (Runs.denote c.right)


class HasCertRules (target_tm : Machine (Fin 2) (Fin 6)) : Prop where
  no_some_none : ∀ (q : Fin 6) (b : Fin 2), (target_tm q b).map Prod.fst ≠ some none
  scanR : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      ⟨some A, ⟨0, l, (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ n) +> r)⟩⟩
      ⟨some A, ⟨0, (([1, 0] : List (Fin 2)) ^ n) +> l, (1 : Fin 2) >> r⟩⟩
  scanB : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (Cfg.headLeft B ((([0, 1] : List (Fin 2)) ^ n) +> l) r)
      (Cfg.headLeft B l ((([1, 1] : List (Fin 2)) ^ n) +> r))
  scanC : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (Cfg.headLeft C ((([1, 0] : List (Fin 2)) ^ n) +> l) r)
      (Cfg.headLeft C l ((([1, 1] : List (Fin 2)) ^ n) +> r))
  scanPair : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      ⟨some A, ⟨0, l, (1 : Fin 2) >> ((([0, 1, 0, 1] : List (Fin 2)) ^ n) +> r)⟩⟩
      ⟨some A, ⟨0, (([1, 1, 0, 1] : List (Fin 2)) ^ n) +> l, (1 : Fin 2) >> r⟩⟩
  ones : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (Cfg.headRight A l ((([1] : List (Fin 2)) ^ n) +> r))
      (Cfg.headRight A ((([1] : List (Fin 2)) ^ n) +> l) r)
  rule_right : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm (CfgR l (D_word n +> r)) (CfgR (S_word n +> l) r)
  rule_left : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm (CfgL (S_word n +> l) r) (CfgL l (D_word n +> r))
  rule_blank : ∀ (l r : ListBlank (Fin 2)),
    ReachesStar target_tm (CfgR l ([0, 0, 0] +> r)) (CfgL l (D_word 0 +> (D_word 0 +> r)))
  rule_even : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (CfgR l ((([1, 1] : List (Fin 2)) ^ (1 + n)) +> ([0, 0] +> r)))
      (CfgL l (D_word (1 + n) +> ([1, 0] +> r)))
  rule_restart : ∀ (l r : ListBlank (Fin 2)) (b : Nat),
    ReachesStar target_tm
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1, 1, 1] +> l)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) r)
  rule_overflow2 : ∀ (r : ListBlank (Fin 2)) (b : Nat),
    ReachesStar target_tm
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1, 1] +> default)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ 2) +> ((([1, 1] : List (Fin 2)) ^ (1 + b)) +> default))
        ([1] +> r))
  rule_overflow1 : ∀ (r : ListBlank (Fin 2)) (b n : Nat),
    ReachesStar target_tm
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1] +> default)) (D_word n +> r))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (n + 2)) +> ((([1, 1] : List (Fin 2)) ^ b) +> default))
        ([1, 0] +> r))
  rule_collision : ∀ (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      (CfgL ([0, 0, 1, 1, 0, 1] +> l) r)
      (CfgJ l ([1, 1, 1, 1] +> r))
  rule_leftJ : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (CfgJ (S_word n +> l) r)
      (CfgL l (D_word (1 + n) +> r))
  rule_turnB : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (CfgL ([1, 1] +> l) (D_word n +> r))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + n)) +> l) r)
  rule_turnJ : ∀ (l r : ListBlank (Fin 2)) (b : Nat),
    ReachesStar target_tm
      (CfgJ ((([1, 0] : List (Fin 2)) ^ b) +> ([1, 1, 1] +> l)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) r)
  rule_finishP : ∀ (l r : ListBlank (Fin 2)) (b : Nat),
    ReachesStar target_tm
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([0, 1] +> (S_word 0 +> l))) r)
      (CfgJ l (D_word (1 + b) +> r))
  rule_defect0 : ∀ (l r : ListBlank (Fin 2)) (m : Nat),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 0 +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgJ l ([1, 1, 1, 1] +> (D_word m +> ([1] +> r))))
  rule_defect1 : ∀ (l r : ListBlank (Fin 2)) (m : Nat),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 1 +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgL l (D_word 0 +> (D_word 0 +> (D_word (1 + m) +> ([1] +> r)))))
  rule_defect2 : ∀ (l r : ListBlank (Fin 2)) (n m : Nat),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word (2 +
        n) +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (2 + m)) +>
        ((([1, 1] : List (Fin 2)) ^ n) +> (S_word 0 +> (S_word 0 +> l)))) ([1] +> r))
  rule_defect_blank0 : ∀ (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 0 +> ([0, 0] +> r))))
      (CfgR ([1, 0, 0, 1] +> (S_word 0 +> l)) r)
  rule_defect_blankS : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word (1 + n) +> ([0, 0] +> r))))
      (CfgR ([1, 0] +> ((([1, 1] : List (Fin 2)) ^ n) +> ([1] +> (S_word 0 +> (S_word 0 +> l))))) r)
  rule_paired : ∀ (l r : ListBlank (Fin 2)) (k n : Nat),
    ReachesStar target_tm
      (CfgR l ((([1, 0] : List (Fin 2)) ^ (k * 2)) +> (D_word n +> r)))
      (CfgR ((([1, 0] : List (Fin 2)) ^ n) +>
        ((([1, 1, 0, 1] : List (Fin 2)) ^ k) +> (S_word 0 +> l))) r)
  rule_emptyR : ∀ (l : ListBlank (Fin 2)),
    ReachesStar target_tm (CfgR l default) (CfgL l (D_word 0 +> (D_word 0 +> default)))
  rule_collide : ∀ (l r : ListBlank (Fin 2)),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 0 +> (D_word 0 +> r))))
      (CfgJ l (D_word 2 +> ([1, 0] +> r)))
  rule_pairR : ∀ (l r : ListBlank (Fin 2)) (n : Nat),
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word (2 + n) +> (D_word (2 + n) +> r))))
      (CfgR (PL_word n +> l) ([1, 0] +> r))

inductive CertTree where
  | nil : CertTree
  | leaf : Nat → CertTree
  | leaf8 : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → CertTree
  | bin : CertTree → CertTree → CertTree

def h240 (a b : Nat) : Nat := (a <<< 240) + b

section Engine

variable {target_tm : Machine (Fin 2) (Fin 6)} [rules : HasCertRules target_tm]

def raw_step (target_tm : Machine (Fin 2) (Fin 6)) (c : RMConfig) : Option RMConfig :=
  let (b, l, r) := match c.dir with
    | Dir.left =>
      let (b, l) := Runs.pop c.left
      (b, l, c.right)
    | Dir.right =>
      let (b, r) := Runs.pop c.right
      (b, c.left, r)
  match target_tm c.state b with
  | some (some q', Stmt.write b' Dir.left) =>
    some ⟨l, Runs.push (.raw [b']) 1 r, q', Dir.left⟩
  | some (some q', Stmt.write b' Dir.right) =>
    some ⟨Runs.push (.raw [b']) 1 l, r, q', Dir.right⟩
  | _ => none


theorem raw_step_spec (c : RMConfig) :
    match raw_step target_tm c with
    | some c' => ReachesStar target_tm c.denote c'.denote
    | none => HaltsFrom target_tm c.denote := by
  rcases c with ⟨l, r, q, d⟩
  cases d
  · dsimp only [raw_step, RMConfig.denote]
    have hp := Runs.pop_spec l
    rcases hpop : Runs.pop l with ⟨b, l'⟩
    rw [hpop] at hp
    dsimp only at hp ⊢
    rw [hp]
    rcases htm : target_tm q b with _ | ⟨_ | q', ⟨b', d'⟩⟩
    · exact ⟨_, ReachesStar.refl _ _, by simp [step_headLeft_none htm]⟩
    · exact False.elim (rules.no_some_none q b (congrArg (Option.map Prod.fst) htm))
    · cases d' <;> dsimp only [RMConfig.denote] <;> rw [Runs.push_spec] <;>
        simp only [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil,
          listblank_append_cons, listblank_append_nil]
      · exact ReachesStar.single (step_headLeft_left htm (Runs.denote l') (Runs.denote r))
      · exact ReachesStar.single (step_headLeft_right htm (Runs.denote l') (Runs.denote r))
  · dsimp only [raw_step, RMConfig.denote]
    have hp := Runs.pop_spec r
    rcases hpop : Runs.pop r with ⟨b, r'⟩
    rw [hpop] at hp
    dsimp only at hp ⊢
    rw [hp]
    rcases htm : target_tm q b with _ | ⟨_ | q', ⟨b', d'⟩⟩
    · exact ⟨_, ReachesStar.refl _ _, by simp [step_headRight_none htm]⟩
    · exact False.elim (rules.no_some_none q b (congrArg (Option.map Prod.fst) htm))
    · cases d' <;> dsimp only [RMConfig.denote] <;> rw [Runs.push_spec] <;>
        simp only [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil,
          listblank_append_cons, listblank_append_nil]
      · exact ReachesStar.single (step_headRight_left htm (Runs.denote l) (Runs.denote r'))
      · exact ReachesStar.single (step_headRight_right htm (Runs.denote l) (Runs.denote r'))

def orient (d : Dir) (c : RMConfig) : RMConfig :=
  match d, c.dir with
  | Dir.left, Dir.right =>
    let (b, r) := Runs.pop c.right
    ⟨Runs.push (.raw [b]) 1 c.left, r, c.state, Dir.left⟩
  | Dir.right, Dir.left =>
    let (b, l) := Runs.pop c.left
    ⟨l, Runs.push (.raw [b]) 1 c.right, c.state, Dir.right⟩
  | _, _ => c

theorem orient_spec (d : Dir) (c : RMConfig) : (orient d c).denote = c.denote := by
  rcases c with ⟨l, r, q, cd⟩
  cases d <;> cases cd <;> try rfl
  · dsimp only [orient, RMConfig.denote]
    have hp := Runs.pop_spec r
    rcases hpop : Runs.pop r with ⟨b, r'⟩
    rw [hpop] at hp; dsimp only at hp ⊢
    rw [Runs.push_spec, hp]
    simp [SymWord.toList, pow_succ_list, Cfg.headRight_cons]
  · dsimp only [orient, RMConfig.denote]
    have hp := Runs.pop_spec l
    rcases hpop : Runs.pop l with ⟨b, l'⟩
    rw [hpop] at hp; dsimp only at hp ⊢
    rw [Runs.push_spec, hp]
    simp [SymWord.toList, pow_succ_list, Cfg.headLeft_cons]

theorem orient_dir (d : Dir) (c : RMConfig) : (orient d c).dir = d := by
  rcases c with ⟨l, r, q, cd⟩
  cases d <;> cases cd <;> rfl

theorem orient_state (d : Dir) (c : RMConfig) : (orient d c).state = c.state := by
  rcases c with ⟨l, r, q, cd⟩
  cases d <;> cases cd <;> rfl

def all_zero_word : List (Fin 2) → Bool
  | [] => true
  | b :: w => if beqFin2 b 0 then all_zero_word w else false

theorem all_zero_word_spec (w : List (Fin 2)) (h : all_zero_word w = true) :
    w +> (default : ListBlank (Fin 2)) = default := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    dsimp [all_zero_word] at h
    cases hb : beqFin2 b 0
    · rw [hb] at h; simp at h
    · rw [hb] at h; simp only [↓reduceIte] at h
      rw [beqFin2_eq b 0 hb, listblank_append_cons, ih h, zero_cons_default]

def SymWord.all_zero : SymWord → Bool
  | .raw w => all_zero_word w
  | _ => false

theorem SymWord.all_zero_spec (w : SymWord) (h : w.all_zero = true) :
    w.toList +> (default : ListBlank (Fin 2)) = default := by
  cases w with
  | raw l => exact all_zero_word_spec l h
  | D _ => contradiction
  | S _ => contradiction
  | PL _ => contradiction

theorem all_zero_pow_spec (w : SymWord) (n : Nat) (h : w.all_zero = true) :
    (w.toList ^ n) +> (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list, listblank_append_right_assoc, ih, SymWord.all_zero_spec w h]

def zeros : Runs → Bool
  | [] => true
  | (w, _) :: xs => if w.all_zero then zeros xs else false

theorem zeros_spec (xs : Runs) (h : zeros xs = true) : Runs.denote xs = default := by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    dsimp [zeros, Runs.denote] at h ⊢
    cases hw : w.all_zero
    · rw [hw] at h; simp at h
    · rw [hw] at h; simp only [↓reduceIte] at h
      rw [ih h, all_zero_pow_spec w n hw]

def plug : Runs → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | (w, n) :: xs, r => (w.toList ^ n) +> plug xs r

def put : Runs → Runs → Runs
  | [], ys => ys
  | (w, n) :: xs, ys => Runs.push w n (put xs ys)


def Runs.take_one (w : SymWord) (n : Nat) (ys : Runs) : Option Runs :=
  match exact_head w n ys with
  | some zs => some zs
  | none =>
    if SymWord.beq w (.raw [1]) then
      remove_ones 16 n ys
    else if SymWord.beq w (.raw [1, 1]) then
      withNat (n * 2) fun n2 => remove_ones 16 n2 ys
    else if SymWord.beq w (.raw [1, 1, 1]) then
      withNat (n * 3) fun n3 => remove_ones 16 n3 ys
    else if Nat.beq n 1 then
      remove_sym_one w ys
    else
      remove_fast 512 w n ys

theorem Runs.take_one_spec (w : SymWord) (n : Nat) (ys zs : Runs)
    (h : take_one w n ys = some zs) : denote ys = (w.toList ^ n) +> denote zs := by
  dsimp only [take_one, withNat] at h
  cases hex : exact_head w n ys with
  | some ts =>
    rw [hex] at h; simp only [Option.some.injEq] at h; subst h
    exact exact_head_spec w n ys ts hex
  | none =>
    rw [hex] at h; dsimp only at h
    cases h1 : SymWord.beq w (.raw [1]) <;> rw [h1] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases h2 : SymWord.beq w (.raw [1, 1]) <;> rw [h2] at h
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        cases h3 : SymWord.beq w (.raw [1, 1, 1]) <;> rw [h3] at h
        · simp only [Bool.false_eq_true, ↓reduceIte] at h
          cases hn1 : Nat.beq n 1 <;> rw [hn1] at h
          · simp only [Bool.false_eq_true, ↓reduceIte] at h
            exact remove_fast_spec 512 w n ys zs h
          · simp only [↓reduceIte] at h
            rw [Nat.eq_of_beq_eq_true hn1, pow_succ_list, pow_zero_list, List.append_nil]
            exact remove_sym_one_spec w ys zs h
        · simp only [↓reduceIte] at h
          rw [SymWord.beq_eq w (.raw [1, 1, 1]) h3]
          dsimp only [SymWord.toList]
          rw [pow_111_eq_pow_1 n]
          exact remove_ones_spec 16 (n * 3) ys zs h
      · simp only [↓reduceIte] at h
        rw [SymWord.beq_eq w (.raw [1, 1]) h2]
        dsimp only [SymWord.toList]
        rw [pow_11_eq_pow_1 n]
        exact remove_ones_spec 16 (n * 2) ys zs h
    · simp only [↓reduceIte] at h
      rw [SymWord.beq_eq w (.raw [1]) h1]
      exact remove_ones_spec 16 n ys zs h

def take : Runs → Runs → Option Runs
  | [], ys => some ys
  | (w, n) :: xs, ys =>
    match Runs.take_one w n ys with
    | some zs => take xs zs
    | none => none

theorem put_spec (xs ys : Runs) : Runs.denote (put xs ys) = plug xs (Runs.denote ys) := by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    dsimp [put, plug]
    rw [Runs.push_spec, ih]

theorem take_spec (xs ys zs : Runs) (h : take xs ys = some zs) :
    Runs.denote ys = plug xs (Runs.denote zs) := by
  induction xs generalizing ys with
  | nil => simp only [take, Option.some.injEq] at h; subst h; rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    dsimp only [take, plug] at h ⊢
    cases hto : Runs.take_one w n ys with
    | none => rw [hto] at h; contradiction
    | some ts =>
      rw [hto] at h; dsimp only at h
      rw [Runs.take_one_spec w n ys ts hto, ih ts h]

theorem plug_app (xs ys : Runs) (r : ListBlank (Fin 2)) :
    plug (xs ++ ys) r = plug xs (plug ys r) := by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    dsimp [plug]
    rw [ih]

-- ============================================================================
-- Section 3: Symbolic Rules & Higher-Order Macros for CB1
-- ============================================================================

abbrev Digits := List (Nat × Nat)

def ds (v : Digits) : Runs := v.map (fun (n, k) => (.D n, k))
def ss (v : Digits) : Runs := (v.map (fun (n, k) => (.S n, k))).reverse

theorem ds_cons (n k : Nat) (v : Digits) : ds ((n, k) :: v) = (.D n, k) :: ds v := rfl

theorem ss_cons (n k : Nat) (v : Digits) : ss ((n, k) :: v) = ss v ++ [(.S n, k)] := by
  simp [ss]

theorem ds_app (u v : Digits) : ds (u ++ v) = ds u ++ ds v := List.map_append

inductive Mode where
  | MR | ML | MJ | MA | MB | MC
  deriving DecidableEq

def Mode.mq : Mode → Fin 6
  | .MR | .MA => A
  | .ML | .MB => B
  | .MJ | .MC => C

def Mode.md : Mode → Dir
  | .MR | .MA => Dir.right
  | _ => Dir.left

def Mode.payload : Mode → List (Fin 2)
  | .MR => [0, 1, 0, 0]
  | .ML => [1]
  | .MJ => [1, 0, 0]
  | _ => []

def Mode.hat : Mode → ListBlank (Fin 2) → ListBlank (Fin 2) → Cfg (Fin 2) (Fin 6)
  | .MR, l, r => CfgR l r
  | .ML, l, r => CfgL l r
  | .MJ, l, r => CfgJ l r
  | .MA, l, r => Cfg.headRight A l r
  | .MB, l, r => Cfg.headLeft B l r
  | .MC, l, r => Cfg.headLeft C l r

structure Recipe where
  hi : Mode
  li : Runs
  ri : Runs
  ho : Mode
  lo : Runs
  ro_pre : Runs
  ro : Runs
  keep_d : Nat
  zl : Bool
  zr : Bool

def valid (target_tm : Machine (Fin 2) (Fin 6)) (p : Recipe) : Prop :=
  ∀ (v : Digits) (l r : ListBlank (Fin 2)),
    (p.keep_d = 0 → v = []) →
    (p.zl = true → l = default) →
    (p.zr = true → r = default) →
    ReachesStar target_tm
      (p.hi.hat (plug p.li l) (plug (ds v) (plug p.ri r)))
      (p.ho.hat (plug p.lo l) (plug p.ro_pre (plug (ds v) (plug p.ro r))))

def check_zero (z : Bool) (xs : Runs) : Bool :=
  if z then zeros xs else true

theorem check_zero_spec (z : Bool) (xs : Runs) (h : check_zero z xs = true) :
    z = true → Runs.denote xs = default := by
  intro hz; rw [hz] at h; exact zeros_spec xs h

def take_keep_put : Nat → Runs → Runs → Bool → Runs → Option Runs
  | 0, ri, ro, zr, rs =>
    match take ri rs with
    | some r => if check_zero zr r then some (put ro r) else none
    | none => none
  | 1, ri, ro, zr, (.D n, k) :: rs =>
    match take ri rs with
    | some r =>
      if check_zero zr r then
        some (Runs.push (.D n) k (put ro r))
      else none
    | none => none
  | m + 2, ri, ro, zr, (.D n, k) :: rs =>
    match take_keep_put (m + 1) ri ro zr rs with
    | some rs' => some ((.D n, k) :: rs')
    | none => none
  | _ + 1, _, _, _, _ => none

theorem take_keep_put_spec (m : Nat) (ri ro : Runs) (zr : Bool) (rs rs' : Runs)
    (h : take_keep_put m ri ro zr rs = some rs') :
    ∃ (v : Digits) (r : ListBlank (Fin 2)),
      (m = 0 → v = []) ∧
      (zr = true → r = default) ∧
      Runs.denote rs = plug (ds v) (plug ri r) ∧
      Runs.denote rs' = plug (ds v) (plug ro r) := by
  induction m generalizing rs rs' with
  | zero =>
    dsimp only [take_keep_put] at h
    cases htr : take ri rs with
    | none => rw [htr] at h; contradiction
    | some r =>
      rw [htr] at h; dsimp only at h
      split_ifs at h with hzr
      injection h with h; subst h
      exact ⟨[], Runs.denote r, fun _ => rfl, check_zero_spec zr r hzr,
        take_spec ri rs r htr, put_spec ro r⟩
  | succ m ih =>
    cases m with
    | zero =>
      rcases rs with _ | ⟨⟨w, k⟩, rest⟩; · contradiction
      cases w <;> try contradiction
      rename_i n
      dsimp only [take_keep_put] at h
      cases htr : take ri rest with
      | none => rw [htr] at h; contradiction
      | some r =>
        rw [htr] at h; dsimp only at h
        split_ifs at h with hzr
        injection h with h; subst h
        refine ⟨[(n, k)], Runs.denote r, by intro hc; contradiction, check_zero_spec zr r hzr, ?_,
          ?_⟩
        · dsimp only [Runs.denote, ds, List.map, plug, SymWord.toList]
          rw [take_spec ri rest r htr]
        · rw [Runs.push_spec, put_spec]
          rfl
    | succ m' =>
      rcases rs with _ | ⟨⟨w, k⟩, rest⟩; · contradiction
      cases w <;> try contradiction
      rename_i n
      dsimp only [take_keep_put] at h
      cases htk : take_keep_put (m' + 1) ri ro zr rest with
      | none => rw [htk] at h; contradiction
      | some rest' =>
        rw [htk] at h; injection h with h; subst h
        obtain ⟨v, r, _, hzr, hrs, hrs'⟩ := ih rest rest' htk
        refine ⟨(n, k) :: v, r, by intro hc; contradiction, hzr, ?_, ?_⟩
        · dsimp only [Runs.denote, ds_cons, plug, SymWord.toList]
          rw [hrs]
        · dsimp only [Runs.denote, ds_cons, plug, SymWord.toList]
          rw [hrs']

def use (p : Recipe) (c : RMConfig) : Option RMConfig :=
  if beqFin6 c.state p.hi.mq then
    let c := orient p.hi.md c
    match take p.li c.left, remove_prefix p.hi.payload c.right with
    | some l, some rs =>
      if check_zero p.zl l then
        match take_keep_put p.keep_d p.ri p.ro p.zr rs with
        | some r_out =>
          some ⟨put p.lo l, Runs.push (.raw p.ho.payload) 1 (put p.ro_pre r_out), p.ho.mq, p.ho.md⟩
        | none => none
      else none
    | _, _ => none
  else none

omit rules in
theorem use_spec (p : Recipe) (c c' : RMConfig) (hv : valid target_tm p) (hu : use p c = some c') :
    ReachesStar target_tm c.denote c'.denote := by
  rcases p with ⟨hi, li, ri, ho, lo, ro_pre, ro, keep_d, zl, zr⟩
  dsimp only [use] at hu
  cases hst : beqFin6 c.state hi.mq
  · rw [hst] at hu; simp at hu
  · rw [hst] at hu; simp only [↓reduceIte] at hu
    have h_or_den := orient_spec hi.md c
    have h_or_dir := orient_dir hi.md c
    have h_or_st := orient_state hi.md c
    rw [← h_or_den]
    generalize hz : orient hi.md c = z at hu h_or_dir h_or_st
    rcases z with ⟨ls, rs, q, d⟩
    dsimp only at hu h_or_dir h_or_st
    have hq : q = hi.mq := by rw [h_or_st, beqFin6_eq _ _ hst]
    subst hq h_or_dir
    cases htl : take li ls with
    | none => rw [htl] at hu; simp at hu
    | some l =>
      rw [htl] at hu
      cases hrp : remove_prefix hi.payload rs with
      | none => rw [hrp] at hu; simp at hu
      | some rs0 =>
        rw [hrp] at hu; dsimp only at hu
        split_ifs at hu with hzl
        cases htk : take_keep_put keep_d ri ro zr rs0 with
        | none => rw [htk] at hu; simp at hu
        | some r_out =>
          rw [htk] at hu; simp only [Option.some.injEq] at hu
          subst hu
          have hl0 := check_zero_spec zl l hzl
          obtain ⟨v, r, hv0, hr0, hrs1, hrs2⟩ := take_keep_put_spec keep_d ri ro zr rs0 r_out htk
          have hmain := hv v (Runs.denote l) r hv0 hl0 hr0
          have hls := take_spec li ls l htl
          have hrs0 := remove_prefix_spec hi.payload rs rs0 hrp
          cases hi <;> cases ho <;> (
            dsimp only [RMConfig.denote, Mode.md, Mode.mq, Mode.hat, Mode.payload] at hmain hrs0 ⊢
            rw [hls, hrs0, hrs1, Runs.push_spec, put_spec, put_spec, hrs2]
            simpa [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil,
              listblank_append_nil,
              CfgR, CfgL, CfgJ] using hmain)


theorem rule_right_pow (l r : ListBlank (Fin 2)) (n k : Nat) :
    ReachesStar target_tm (CfgR l (((D_word n) ^ k) +> r)) (CfgR (((S_word n) ^ k) +> l) r) := by
  induction k generalizing l with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | succ k ih =>
    rw [pow_succ_list, listblank_append_right_assoc]
    refine (rules.rule_right l _ n).trans ((ih (S_word n +> l)).trans ?_)
    rw [ListBlank.append_pow_comm, ← listblank_append_right_assoc, ← pow_succ_list]
    try exact ReachesStar.refl _ _

theorem rule_left_pow (l r : ListBlank (Fin 2)) (n k : Nat) :
    ReachesStar target_tm (CfgL (((S_word n) ^ k) +> l) r) (CfgL l (((D_word n) ^ k) +> r)) := by
  induction k generalizing r with
  | zero =>
    simp only [pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | succ k ih =>
    rw [pow_succ_list, listblank_append_right_assoc]
    refine (rules.rule_left _ r n).trans ((ih (D_word n +> r)).trans ?_)
    rw [ListBlank.append_pow_comm, ← listblank_append_right_assoc, ← pow_succ_list]
    try exact ReachesStar.refl _ _

theorem right_list (v : Digits) (l r : ListBlank (Fin 2)) :
    ReachesStar target_tm (CfgR l (plug (ds v) r)) (CfgR (plug (ss v) l) r) := by
  induction v generalizing l with
  | nil => try exact ReachesStar.refl _ _
  | cons nk v ih =>
    rcases nk with ⟨n, k⟩
    rw [ds_cons, ss_cons, plug_app]
    dsimp only [plug, SymWord.toList]
    exact (rule_right_pow l (plug (ds v) r) n k).trans (ih (((S_word n) ^ k) +> l))

theorem left_list (v : Digits) (l r : ListBlank (Fin 2)) :
    ReachesStar target_tm (CfgL (plug (ss v) l) r) (CfgL l (plug (ds v) r)) := by
  induction v generalizing l r with
  | nil => try exact ReachesStar.refl _ _
  | cons nk v ih =>
    rcases nk with ⟨n, k⟩
    rw [ds_cons, ss_cons, plug_app]
    dsimp only [plug, SymWord.toList]
    exact (ih (((S_word n) ^ k) +> l) r).trans (rule_left_pow l (plug (ds v) r) n k)

def call (target_tm : Machine (Fin 2) (Fin 6)) (r s : ListBlank (Fin 2)) : Prop :=
  ∀ l : ListBlank (Fin 2), ReachesStar target_tm (CfgR l r) (CfgL l s)

inductive calls (target_tm : Machine (Fin 2) (Fin 6)) : Nat → ListBlank (Fin 2) →
  ListBlank (Fin 2) → Prop where
  | zero (r : ListBlank (Fin 2)) : calls target_tm 0 r r
  | succ {n : Nat} {r s t : ListBlank (Fin 2)} : call target_tm r s → calls target_tm n s t →
      calls target_tm (n + 1) r t

theorem call_prefix (v : Digits) {r s : ListBlank (Fin 2)} (h : call target_tm r s) :
    call target_tm (plug (ds v) r) (plug (ds v) s) := by
  intro l
  exact (right_list v l r).trans ((h (plug (ss v) l)).trans (left_list v l s))

theorem call_blank (v : Digits) :
    call target_tm (plug (ds v) default) (plug (ds v) (((D_word 0) ^ 2) +> default)) := by
  apply call_prefix
  intro l
  simpa [pow_succ_list, pow_zero_list, listblank_append_right_assoc] using rules.rule_emptyR l

theorem calls_blank (k : Nat) (v : Digits) :
    calls target_tm k (plug (ds v) default) (plug (ds v) (((D_word 0) ^ (k * 2)) +> default)) := by
  induction k generalizing v with
  | zero =>
    simpa [pow_zero_list, listblank_append_nil] using calls.zero (plug (ds v) default)
  | succ k ih =>
    refine calls.succ (call_blank v) ?_
    have ih' := ih (v ++ [(0, 2)])
    have hds0 : ds [(0, 2)] = [(.D 0, 2)] := rfl
    simp only [ds_app, plug_app, hds0, plug, SymWord.toList] at ih'
    have hmul : (k + 1) * 2 = 2 + k * 2 := by omega
    rw [hmul, list_pow_add, listblank_append_right_assoc]
    exact ih'

theorem call_collision (v : Digits) (j : Nat) (r : ListBlank (Fin 2)) :
    call target_tm (plug (ds v) (D_word j +> ([1, 0] +> (D_word 0 +> (D_word 0 +> r)))))
      (plug (ds v) (D_word (1 + j) +> (D_word 2 +> ([1, 0] +> r)))) := by
  apply call_prefix
  intro l
  exact (rules.rule_right l _ j).trans ((rules.rule_collide _ r).trans (rules.rule_leftJ l _ j))

theorem calls_collision (k : Nat) (v : Digits) (j : Nat) (r : ListBlank (Fin 2)) :
    calls target_tm (k + 1)
      (plug (ds v) (D_word j +> ([1, 0] +> (((D_word 0) ^ ((k + 1) * 2)) +> r))))
      (plug (ds v) (D_word (1 + j) +> (((D_word 3) ^ k) +> (D_word 2 +> ([1, 0] +> r))))) := by
  induction k generalizing v j with
  | zero =>
    have h1 : (0 + 1) * 2 = 2 := rfl
    rw [h1]
    simp only [pow_succ_list, pow_zero_list, List.append_nil, listblank_append_right_assoc,
      listblank_append_nil]
    exact calls.succ (call_collision v j r) (calls.zero _)
  | succ k ih =>
    have hmul : (k + 1 + 1) * 2 = 2 + (k + 1) * 2 := by omega
    rw [hmul, pow_two_add, listblank_append_right_assoc, listblank_append_right_assoc]
    refine calls.succ (call_collision v j (((D_word 0) ^ ((k + 1) * 2)) +> r)) ?_
    have ih' := ih (v ++ [(1 + j, 1)]) 2
    have hds1 : ds [(1 + j, 1)] = [(.D (1 + j), 1)] := rfl
    simp only [ds_app, plug_app, hds1, plug, SymWord.toList] at ih'
    simpa [pow_succ_list, pow_zero_list, List.append_nil, listblank_append_right_assoc] using ih'

theorem pairsR (k n : Nat) (l r : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (((D_word (2 + n)) ^ (k * 2)) +> r)))
      (CfgR (((PL_word n) ^ k) +> l) ([1, 0] +> r)) := by
  induction k generalizing l with
  | zero =>
    simp only [Nat.zero_mul, pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | succ k ih =>
    have hmul : (k + 1) * 2 = 2 + k * 2 := by omega
    rw [hmul, pow_two_add, listblank_append_right_assoc, listblank_append_right_assoc]
    refine (rules.rule_pairR l _ n).trans ((ih (PL_word n +> l)).trans ?_)
    rw [ListBlank.append_pow_comm, ← listblank_append_right_assoc, ← pow_succ_list]
    try exact ReachesStar.refl _ _

theorem loopL {k : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm k r s) (l : ListBlank (Fin
  2)) (b : Nat) :
    ReachesStar target_tm
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ((([1, 1, 1] : List (Fin 2)) ^ k) +> l)) r)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) s) := by
  induction h generalizing l with
  | zero r =>
    simp only [pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | @succ n r0 u t hcall htail ih =>
    rw [pow_succ_list [1, 1, 1] n, listblank_append_right_assoc]
    exact (rules.rule_restart _ r0 b).trans ((hcall _).trans (ih l))

theorem loopR {k : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm k r s) (l : ListBlank (Fin
  2)) (b : Nat) :
    ReachesStar target_tm
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ((([1, 1, 1] : List (Fin 2)) ^ k) +> l)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) s) := by
  induction h generalizing l with
  | zero r =>
    simp only [pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | @succ n r0 u t hcall htail ih =>
    rw [pow_succ_list [1, 1, 1] n, listblank_append_right_assoc]
    exact (hcall _).trans ((rules.rule_restart _ u b).trans (ih l))

theorem pl_inner_eq (n : Nat) :
    (([1, 1] : List (Fin 2)) ^ (1 + n * 3)) ++ S_word 0 =
      (([1, 1, 1] : List (Fin 2)) ^ (1 + n * 2)) ++ [0, 1] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h1 : 1 + (n + 1) * 3 = 3 + (1 + n * 3) := by omega
    have h2 : 1 + (n + 1) * 2 = 2 + (1 + n * 2) := by omega
    rw [h1, h2, list_pow_add [1, 1] 3 (1 + n * 3), list_pow_add [1, 1, 1] 2 (1 + n * 2),
      List.append_assoc, ih, ← List.append_assoc]
    rfl

theorem pl_decomp (n : Nat) (l : ListBlank (Fin 2)) :
    PL_word (1 + n * 3) +> l =
      (([1, 0] : List (Fin 2)) ^ (5 + n * 3)) +>
        ((([1, 1, 1] : List (Fin 2)) ^ (1 + n * 2)) +>
          ([0, 1] +> (S_word 0 +> l))) := by
  dsimp only [PL_word]
  have h5 : 1 + n * 3 + 4 = 5 + n * 3 := by omega
  rw [h5, List.append_assoc (([1, 0] : List (Fin 2)) ^ (5 + n * 3)), pl_inner_eq n]
  simp only [List.append_assoc, listblank_append_right_assoc]

theorem returnP_L {n : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm (1 +
  n * 2) r s) (l : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (CfgL (PL_word (1 + n * 3) +> l) r)
      (CfgJ l (D_word (5 + n * 3) +> s)) := by
  rw [pl_decomp n l]
  have h5 : 5 + n * 3 = 1 + (4 + n * 3) := by omega
  rw [h5]
  exact (loopL h ([0, 1] +> (S_word 0 +> l)) (4 + n * 3)).trans (rules.rule_finishP l s (4 + n * 3))

theorem loopJ {k : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm (k +
  1) r s) (l : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar target_tm
      (CfgJ ((([1, 0] : List (Fin 2)) ^ b) +> ((([1, 1, 1] : List (Fin 2)) ^ (k + 1)) +> l)) r)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) s) := by
  cases h with
  | @succ _ _ u _ hcall htail =>
    rw [pow_succ_list [1, 1, 1] k, listblank_append_right_assoc]
    exact (rules.rule_turnJ _ r b).trans ((hcall _).trans (loopL htail l b))

theorem returnP_J {n : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm (1 +
  n * 2) r s) (l : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (CfgJ (PL_word (1 + n * 3) +> l) r)
      (CfgJ l (D_word (6 + n * 3) +> s)) := by
  rw [pl_decomp n l]
  rw [Nat.add_comm 1 (n * 2)] at h ⊢
  refine (loopJ h ([0, 1] +> (S_word 0 +> l)) (5 + n * 3)).trans ?_
  have h6 : 6 + n * 3 = 1 + (5 + n * 3) := by omega
  rw [h6]
  exact rules.rule_finishP l s (5 + n * 3)

theorem calls_prefix (v : Digits) {k : Nat} {r s : ListBlank (Fin 2)} (h : calls target_tm k r s) :
    calls target_tm k (plug (ds v) r) (plug (ds v) s) := by
  induction h with
  | zero r => exact calls.zero _
  | succ hcall _ ih => exact calls.succ (call_prefix v hcall) ih

omit rules in
theorem calls_split (a b : Nat) {r s : ListBlank (Fin 2)} (h : calls target_tm (a + b) r s) :
    ∃ t, calls target_tm a r t ∧ calls target_tm b t s := by
  induction a generalizing r with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨r, calls.zero r, h⟩
  | succ a ih =>
    have hab : a + 1 + b = (a + b) + 1 := by omega
    rw [hab] at h
    cases h with
    | @succ _ _ u _ hcall htail =>
      obtain ⟨t, ht1, ht2⟩ := ih htail
      exact ⟨t, calls.succ hcall ht1, ht2⟩

theorem returnsP_J (k n : Nat) {r s : ListBlank (Fin 2)} (h : calls target_tm (k * (1 +
  n * 2)) r s) (l : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (CfgJ (((PL_word (1 + n * 3)) ^ k) +> l) r)
      (CfgJ l (((D_word (6 + n * 3)) ^ k) +> s)) := by
  induction k generalizing r s with
  | zero =>
    have hz : 0 * (1 + n * 2) = 0 := Nat.zero_mul _
    rw [hz] at h
    cases h
    simp only [pow_zero_list, listblank_append_nil]
    try exact ReachesStar.refl _ _
  | succ k ih =>
    have hmul : (k + 1) * (1 + n * 2) = (1 + n * 2) + k * (1 + n * 2) := by ring
    rw [hmul] at h
    obtain ⟨u, hu, hv⟩ := calls_split (1 + n * 2) (k * (1 + n * 2)) h
    rw [pow_succ_list, listblank_append_right_assoc]
    refine (returnP_J hu _).trans ?_
    have hv' := calls_prefix [(6 + n * 3, 1)] hv
    dsimp only [ds, List.map, plug, SymWord.toList] at hv'
    simp only [pow_succ_list, pow_zero_list, List.append_nil] at hv'
    refine (ih hv').trans ?_
    rw [ListBlank.append_pow_comm, ← listblank_append_right_assoc, ← pow_succ_list]
    try exact ReachesStar.refl _ _

theorem returnsP_L (k n : Nat) {r s : ListBlank (Fin 2)} (h : calls target_tm ((1 + k) * (1 +
  n * 2)) r s) (l : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (CfgL (((PL_word (1 + n * 3)) ^ (1 + k)) +> l) r)
      (CfgJ l (((D_word (6 + n * 3)) ^ k) +> (D_word (5 + n * 3) +> s))) := by
  have hmul : (1 + k) * (1 + n * 2) = (1 + n * 2) + k * (1 + n * 2) := by ring
  rw [hmul] at h
  obtain ⟨u, hu, hv⟩ := calls_split (1 + n * 2) (k * (1 + n * 2)) h
  rw [pow_one_add, listblank_append_right_assoc]
  refine (returnP_L hu _).trans ?_
  have hv' := calls_prefix [(5 + n * 3, 1)] hv
  dsimp only [ds, List.map, plug, SymWord.toList] at hv'
  simp only [pow_succ_list, pow_zero_list, List.append_nil] at hv'
  exact returnsP_J k n hv' l



theorem rule_collisionD (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar target_tm
      (CfgL ([0, 0, 1, 1, 0, 1] +> l) (D_word n +> r))
      (CfgJ l (D_word (2 + n) +> r)) := by
  have h : D_word (2 + n) +> r = [1, 1, 1, 1] +> (D_word n +> r) := by
    dsimp [D_word]
    rw [pow_two_add]
    simp only [List.cons_append, List.nil_append, listblank_append_cons,
      listblank_append_right_assoc]
  rw [h]
  exact rules.rule_collision l (D_word n +> r)

theorem rule_defect0D (l r : ListBlank (Fin 2)) (m : Nat) :
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 0 +> (D_word m +> r))))
      (CfgJ l (D_word (2 + m) +> ([1, 0] +> r))) := by
  have h1 : D_word m +> r = [1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> ([0] +> r))) := by
    dsimp [D_word]
    simp only [
      listblank_append_cons, listblank_append_right_assoc, listblank_append_nil]
  have h2 : D_word (2 + m) +> ([1, 0] +> r) = [1, 1, 1, 1] +> (D_word m +> ([1] +> ([0] +> r))) :=
    by
    dsimp [D_word]
    rw [pow_two_add]
    simp only [List.cons_append, List.nil_append,
      listblank_append_cons, listblank_append_right_assoc, listblank_append_nil]
  rw [h1, h2]
  exact rules.rule_defect0 l ([0] +> r) m

theorem rule_defect1D (l r : ListBlank (Fin 2)) (m : Nat) :
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word 1 +> (D_word m +> r))))
      (CfgL l (D_word 0 +> (D_word 0 +> (D_word (1 + m) +> ([1, 0] +> r))))) := by
  have h1 : D_word m +> r = [1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> ([0] +> r))) := by
    dsimp [D_word]
    simp only [
      listblank_append_cons, listblank_append_right_assoc, listblank_append_nil]
  have h2 : ([1, 0] : List (Fin 2)) +> r = [1] +> ([0] +> r) := rfl
  rw [h1, h2]
  exact rules.rule_defect1 l ([0] +> r) m

theorem rule_defect2D (l r : ListBlank (Fin 2)) (n m : Nat) :
    ReachesStar target_tm
      (CfgR l ([1, 0] +> (D_word (2 + n) +> (D_word m +> r))))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (2 +
        m)) +> ((([1, 1] : List (Fin 2)) ^ n) +> (S_word 0 +> (S_word 0 +> l)))) ([1, 0] +> r)) :=
        by
  have h1 : D_word m +> r = [1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> ([0] +> r))) := by
    dsimp [D_word]
    simp only [
      listblank_append_cons, listblank_append_right_assoc, listblank_append_nil]
  have h2 : ([1, 0] : List (Fin 2)) +> r = [1] +> ([0] +> r) := rfl
  rw [h1, h2]
  exact rules.rule_defect2 l ([0] +> r) n m

theorem call_defect0 (v : Digits) (j m : Nat) (r : ListBlank (Fin 2)) :
    call target_tm (plug (ds v) (D_word j +> ([1, 0] +> (D_word 0 +> (D_word m +> r)))))
      (plug (ds v) (D_word (1 + j) +> (D_word (2 + m) +> ([1, 0] +> r)))) := by
  apply call_prefix
  intro l
  exact (rules.rule_right l _ j).trans ((rule_defect0D _ r m).trans (rules.rule_leftJ l _ j))

theorem call_defect1 (v : Digits) (m : Nat) (r : ListBlank (Fin 2)) :
    call target_tm (plug (ds v) ([1, 0] +> (D_word 1 +> (D_word m +> r))))
      (plug (ds v) (D_word 0 +> (D_word 0 +> (D_word (1 + m) +> ([1, 0] +> r))))) := by
  apply call_prefix
  intro l
  exact rule_defect1D l r m

theorem loopR_to_L {k : Nat} {r t : ListBlank (Fin 2)} (h : calls target_tm (k +
  1) r t) (l : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar target_tm
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ((([1, 1, 1] : List (Fin 2)) ^ k) +> l)) r)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) t) := by
  obtain ⟨s, hs1, hs2⟩ := calls_split k 1 h
  cases hs2 with
  | @succ _ _ u _ hcall hzero =>
    cases hzero
    exact (loopR hs1 l b).trans (hcall _)

theorem loopR_to_L' {h : Nat} {r t : ListBlank (Fin 2)} (hh : 0 < h) (hc : calls target_tm h r t) (l
  : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar target_tm
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 +
        b)) +> ((([1, 1, 1] : List (Fin 2)) ^ (h - 1)) +> l)) r)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) t) := by
  have h1 : (h - 1) + 1 = h := by omega
  rw [← h1] at hc
  exact loopR_to_L hc l b

theorem loopJ' {h : Nat} {r s : ListBlank (Fin 2)} (hh : 0 < h) (hc : calls target_tm h r s) (l :
  ListBlank (Fin 2)) (b : Nat) :
    ReachesStar target_tm
      (CfgJ ((([1, 0] : List (Fin 2)) ^ b) +> ((([1, 1, 1] : List (Fin 2)) ^ h) +> l)) r)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) s) := by
  have h1 : (h - 1) + 1 = h := by omega
  rw [← h1] at hc ⊢
  exact loopJ hc l b



-- ============================================================================
-- Section 5: CBMacros (Basic & High Recipes)
-- ============================================================================

def word (w : List (Fin 2)) : Runs := [(.raw w, 1)]
def power (w : List (Fin 2)) (n : Nat) : Runs := [(.raw w, n)]
def dn (n : Nat) : Runs := [(.D n, 1)]
def sn (n : Nat) : Runs := [(.S n, 1)]
def imm : Runs := word [1, 0]
def mk_rule (h : Mode) (l r : Runs) (h' : Mode) (l' r' : Runs) : Recipe :=
  ⟨h, l, r, h', l', [], r', 0, false, false⟩
def mk_leftzero (h : Mode) (l r : Runs) (h' : Mode) (l' r' : Runs) : Recipe :=
  ⟨h, l, r, h', l', [], r', 0, true, false⟩

@[simp] theorem plug_word (w : List (Fin 2)) (r : ListBlank (Fin 2)) :
    plug (word w) r = w +> r := by
  simp [word, plug, SymWord.toList, pow_succ_list]

@[simp] theorem plug_power (w : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    plug (power w n) r = (w ^ n) +> r := rfl

@[simp] theorem plug_dn (n : Nat) (r : ListBlank (Fin 2)) :
    plug (dn n) r = D_word n +> r := by
  simp [dn, plug, SymWord.toList, pow_succ_list]

@[simp] theorem plug_sn (n : Nat) (r : ListBlank (Fin 2)) :
    plug (sn n) r = S_word n +> r := by
  simp [sn, plug, SymWord.toList, pow_succ_list]

@[simp] theorem plug_run (w : SymWord) (n : Nat) (r : ListBlank (Fin 2)) :
    plug [(w, n)] r = (w.toList ^ n) +> r := rfl

inductive Basic where
  | ScanR (k : Nat) | ScanB (k : Nat) | ScanC (k : Nat) | ScanPair (k : Nat) | Ones (k : Nat)
  | Blank | Even (n : Nat) | Restart (b : Nat) | Over2 (b : Nat) | Over1 (b n : Nat)
  | Collision | CollisionD (n : Nat) | LeftJ (n : Nat) | TurnB (n : Nat) | TurnJ (b : Nat)
  | Defect0 (m : Nat) | Defect1 (m : Nat) | Defect2 (n m : Nat)
  | Defect0D (m : Nat) | Defect1D (m : Nat) | Defect2D (n m : Nat)
  | DefectBlank0 | DefectBlankS (n : Nat) | Paired (k n : Nat)

def basic_rule : Basic → Recipe
  | .ScanR k => mk_rule .MA [] (word [0, 1] ++ [(.raw [1, 1], k)]) .MA [(.raw [1, 0], k)] (word [0,
      1])
  | .ScanB k => mk_rule .MB [(.raw [0, 1], k)] [] .MB [] [(.raw [1, 1], k)]
  | .ScanC k => mk_rule .MC [(.raw [1, 0], k)] [] .MC [] [(.raw [1, 1], k)]
  | .ScanPair k => mk_rule .MA [] (word [0, 1] ++ [(.raw [0, 1, 0, 1], k)]) .MA [(.raw [1, 1, 0, 1],
      k)] (word [0, 1])
  | .Ones k => mk_rule .MA [] [(.raw [1], k)] .MA [(.raw [1], k)] []
  | .Blank => mk_rule .MR [] (word [0, 0, 0]) .ML [] (dn 0 ++ dn 0)
  | .Even n => mk_rule .MR [] (power [1, 1] (1 + n) ++ word [0, 0]) .ML [] (dn (1 + n) ++ imm)
  | .Restart b => mk_rule .ML (power [1, 0] (1 + b) ++ word [1, 1, 1]) [] .MR (power [1, 0] (1 +
      b)) []
  | .Over2 b => mk_leftzero .ML (power [1, 0] (1 +
      b) ++ word [1, 1]) [] .MR (power [1, 0] 2 ++ power [1, 1] (1 + b)) (word [1])
  | .Over1 b n => mk_leftzero .ML (power [1, 0] (1 + b) ++ word [1]) (dn n) .MR (power [1, 0] (n +
      2) ++ power [1, 1] b) imm
  | .Collision => mk_rule .ML (word [0, 0, 1, 1, 0, 1]) [] .MJ [] (word [1, 1, 1, 1])
  | .CollisionD n =>
    withNat (2 + n) fun n2 =>
    mk_rule .ML (word [0, 0, 1, 1, 0, 1]) (dn n) .MJ [] (dn n2)
  | .LeftJ n => mk_rule .MJ (sn n) [] .ML [] (dn (1 + n))
  | .TurnB n => mk_rule .ML (word [1, 1]) (dn n) .MR (power [1, 0] (1 + n)) []
  | .TurnJ b => mk_rule .MJ (power [1, 0] b ++ word [1, 1, 1]) [] .MR (power [1, 0] (1 + b)) []
  | .Defect0 m => mk_rule .MR [] (imm ++ dn 0 ++ word [1] ++ power [1,
      1] m ++ word [0]) .MJ [] (word [1, 1, 1, 1] ++ dn m ++ word [1])
  | .Defect1 m => mk_rule .MR [] (imm ++ dn 1 ++ word [1] ++ power [1,
      1] m ++ word [0]) .ML [] (dn 0 ++ dn 0 ++ dn (1 + m) ++ word [1])
  | .Defect2 n m => mk_rule .MR [] (imm ++ dn (2 +
      n) ++ word [1] ++ power [1, 1] m ++ word [0]) .MR (power [1, 0] (2 +
      m) ++ power [1, 1] n ++ sn 0 ++ sn 0) (word [1])
  | .Defect0D m =>
    withNat (2 + m) fun m2 =>
    mk_rule .MR [] (imm ++ dn 0 ++ dn m) .MJ [] (dn m2 ++ imm)
  | .Defect1D m =>
    withNat (1 + m) fun m1 =>
    mk_rule .MR [] (imm ++ dn 1 ++ dn m) .ML [] (dn 0 ++ dn 0 ++ dn m1 ++ imm)
  | .Defect2D n m =>
    withNat (2 + n) fun n2 =>
    withNat (2 + m) fun m2 =>
    mk_rule .MR [] (imm ++ dn n2 ++ dn m) .MR (power [1, 0] m2 ++ power [1,
      1] n ++ sn 0 ++ sn 0) imm
  | .DefectBlank0 => mk_rule .MR [] (imm ++ dn 0 ++ word [0, 0]) .MR (word [1, 0, 0, 1] ++ sn 0) []
  | .DefectBlankS n => mk_rule .MR [] (imm ++ dn (1 +
      n) ++ word [0, 0]) .MR (word [1, 0] ++ power [1, 1] n ++ word [1] ++ sn 0 ++ sn 0) []
  | .Paired k n =>
    withNat (k * 2) fun k2 =>
    mk_rule .MR [] ([(.raw [1, 0], k2)] ++ dn n) .MR (power [1, 0] n ++ [(.raw [1, 1, 0, 1],
      k)] ++ sn 0) []

theorem basic_valid (t : Basic) : valid target_tm (basic_rule t) := by
  cases t with
  | ScanR k =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simpa [ds, plug_app, plug_word, plug, SymWord.toList, Cfg.headRight] using
      rules.scanR l r k
  | ScanB k =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug, SymWord.toList]; exact rules.scanB l r k
  | ScanC k =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug, SymWord.toList]; exact rules.scanC l r k
  | ScanPair k =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simpa [ds, plug_app, plug_word, plug, SymWord.toList, Cfg.headRight] using
      rules.scanPair l r k
  | Ones k =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug, SymWord.toList]; exact rules.ones l r k
  | Blank =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_dn, plug]; exact rules.rule_blank l r
  | Even n =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_dn, plug_power, plug]; exact rules.rule_even l r n
  | Restart b =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_power, plug]; exact rules.rule_restart l r b
  | Over2 b =>
    intro v l r hv hl _; rw [hv rfl, hl rfl]; dsimp only [basic_rule, mk_leftzero, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_power, plug]; exact rules.rule_overflow2 r b
  | Over1 b n =>
    intro v l r hv hl _; rw [hv rfl, hl rfl]; dsimp only [basic_rule, mk_leftzero, imm, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_dn, plug_power, plug]; exact rules.rule_overflow1 r b n
  | Collision =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_word, plug]; exact rules.rule_collision l r
  | CollisionD n =>
    intro v l r hv _ _; dsimp only [basic_rule, mk_rule, withNat, Mode.hat] at hv ⊢
    rw [hv rfl]; simp only [ds, plug_word, plug_dn, plug]; exact rule_collisionD l r n
  | LeftJ n =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_sn, plug_dn, plug]; exact rules.rule_leftJ l r n
  | TurnB n =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_word, plug_dn, plug_power, plug]; exact rules.rule_turnB l r n
  | TurnJ b =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, Mode.hat]
    simp only [ds, plug_app, plug_word, plug_power, plug]; exact rules.rule_turnJ l r b
  | Defect0 m =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_power,
      plug]; exact rules.rule_defect0 l r m
  | Defect1 m =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_power,
      plug]; exact rules.rule_defect1 l r m
  | Defect2 n m =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_sn, plug_power,
      plug]; exact rules.rule_defect2 l r n m
  | Defect0D m =>
    intro v l r hv _ _; dsimp only [basic_rule, mk_rule, imm, withNat, Mode.hat] at hv ⊢
    rw [hv rfl]; simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn,
      plug]; exact rule_defect0D l r m
  | Defect1D m =>
    intro v l r hv _ _; dsimp only [basic_rule, mk_rule, imm, withNat, Mode.hat] at hv ⊢
    rw [hv rfl]; simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn,
      plug]; exact rule_defect1D l r m
  | Defect2D n m =>
    intro v l r hv _ _; dsimp only [basic_rule, mk_rule, imm, withNat, Mode.hat] at hv ⊢
    rw [hv rfl]; simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_sn,
      plug_power, plug]; exact rule_defect2D l r n m
  | DefectBlank0 =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_sn,
      plug]; exact rules.rule_defect_blank0 l r
  | DefectBlankS n =>
    intro v l r hv _ _; rw [hv rfl]; dsimp only [basic_rule, mk_rule, imm, Mode.hat]
    simp only [ds, List.append_assoc, plug_app, plug_word, plug_dn, plug_sn, plug_power,
      plug]; exact rules.rule_defect_blankS l r n
  | Paired k n =>
    intro v l r hv _ _; dsimp only [basic_rule, mk_rule, withNat, Mode.hat] at hv ⊢
    rw [hv rfl]
    simp only [ds, List.append_assoc, plug_app, plug_dn, plug_sn, plug_power,
      plug, SymWord.toList]
    exact rules.rule_paired l r k n

inductive Tail where
  | TBlank (m : Nat) (v : Digits)
  | TCollision (m : Nat) (v : Digits) (j : Nat)
  | TDefect0 (m : Nat) (v : Digits) (j d : Nat)
  | TDefect1 (m : Nat) (v : Digits) (d : Nat)

def Tail.keep_d : Tail → Nat
  | .TBlank m _ => m
  | .TCollision m _ _ => m
  | .TDefect0 m _ _ _ => m
  | .TDefect1 m _ _ => m

def Tail.is_zero : Tail → Bool
  | .TBlank _ _ => true
  | _ => false

def before (h : Nat) : Tail → Runs
  | .TBlank _ v => ds v
  | .TCollision _ v j =>
    withNat (h * 2) fun h2 =>
    ds v ++ dn j ++ imm ++ [(.D 0, h2)]
  | .TDefect0 _ v j d =>
    ds v ++ dn j ++ imm ++ dn 0 ++ dn d
  | .TDefect1 _ v d =>
    ds v ++ imm ++ dn 1 ++ dn d

def after (h : Nat) : Tail → Runs
  | .TBlank _ v =>
    withNat (h * 2) fun h2 =>
    ds v ++ [(.D 0, h2)]
  | .TCollision _ v j =>
    withNat (1 + j) fun j1 =>
    withNat (h - 1) fun hm1 =>
    ds v ++ dn j1 ++ [(.D 3, hm1)] ++ dn 2 ++ imm
  | .TDefect0 _ v j d =>
    withNat (1 + j) fun j1 =>
    withNat (2 + d) fun d2 =>
    ds v ++ dn j1 ++ dn d2 ++ imm
  | .TDefect1 _ v d =>
    withNat (1 + d) fun d1 =>
    ds v ++ [(.D 0, 2)] ++ dn d1 ++ imm

def Tail.valid_h (h : Nat) : Tail → Bool
  | .TBlank _ _ => Nat.blt 0 h
  | .TCollision _ _ _ => Nat.blt 0 h
  | .TDefect0 _ _ _ _ => Nat.beq h 1
  | .TDefect1 _ _ _ => Nat.beq h 1

theorem tail_spec (u : Digits) (h : Nat) (t : Tail) (r : ListBlank (Fin 2))
    (hh : 0 < h) (hr : t.is_zero = true → r = default) :
    calls target_tm (if match t with | .TDefect0 _ _ _ _ | .TDefect1 _ _ _ => true | _ => false then
      1 else h)
      (plug (ds u) (plug (before h t) r))
      (plug (ds u) (plug (after h t) r)) := by
  apply calls_prefix u
  cases t with
  | TBlank m v =>
    rw [hr rfl]
    dsimp only [before, after, withNat, ↓reduceIte]
    rw [plug_app, plug_run]
    exact calls_blank h v
  | TCollision m v j =>
    dsimp only [before, after, imm, withNat, ↓reduceIte]
    simp only [List.append_assoc, plug_app, plug_word, plug_dn, plug_run, SymWord.toList]
    have hh1 : (h - 1) + 1 = h := by omega
    have hc := calls_collision (target_tm := target_tm) (h - 1) v j r
    rwa [hh1] at hc
  | TDefect0 m v j d =>
    dsimp only [before, after, imm, withNat, ↓reduceIte]
    simp only [List.append_assoc, plug_app, plug_word, plug_dn]
    exact calls.succ (call_defect0 v j d r) (calls.zero _)
  | TDefect1 m v d =>
    dsimp only [before, after, imm, withNat, ↓reduceIte]
    simp only [List.append_assoc, plug_app, plug_word, plug_dn, plug_run, SymWord.toList,
      pow_succ_list, pow_zero_list, List.append_nil, listblank_append_right_assoc]
    exact calls.succ (call_defect1 v d r) (calls.zero _)

inductive High where
  | RightList (v : Digits)
  | LeftList (v : Digits)
  | Call (t : Tail)
  | Pairs (n k : Nat)
  | Loops (fromR : Bool) (k b : Nat) (t : Tail)
  | LoopsJ (k b : Nat) (t : Tail)
  | Returns (fromJ : Bool) (n k : Nat) (t : Tail)

def tail_calls (h : Nat) (t : Tail) : Nat :=
  match t with
  | .TDefect0 _ _ _ _ | .TDefect1 _ _ _ => 1
  | _ => h

def high_rule : High → Recipe
  | .RightList v => mk_rule .MR [] (ds v) .MR (ss v) []
  | .LeftList v => mk_rule .ML (ss v) [] .ML [] (ds v)
  | .Call t => ⟨.MR, [], before 1 t, .ML, [], [], after 1 t, t.keep_d, false, t.is_zero⟩
  | .Pairs n k =>
    withNat (2 + n) fun n2 =>
    withNat (k * 2) fun k2 =>
    mk_rule .MR [] (imm ++ [(.D n2, k2)]) .MR [(.PL n, k)] imm
  | .Loops fromR k b t =>
    withNat (if fromR then 2 + k else 1 + k) fun h0 =>
    let h := tail_calls h0 t
    withNat (1 + b) fun b1 =>
    let head_in := if fromR then Mode.MR else Mode.ML
    let shares := if fromR then h - 1 else h
    ⟨head_in, power [1, 0] b1 ++ [(.raw [1, 1, 1], shares)], before h t,
      .ML, power [1, 0] b1, [], after h t, t.keep_d, false, t.is_zero⟩
  | .LoopsJ k b t =>
    withNat (1 + k) fun h0 =>
    let h := tail_calls h0 t
    withNat (1 + b) fun b1 =>
    ⟨.MJ, power [1, 0] b ++ [(.raw [1, 1, 1], h)], before h t,
      .ML, power [1, 0] b1, [], after h t, t.keep_d, false, t.is_zero⟩
  | .Returns fromJ n k t =>
    withNat (1 + k) fun count =>
    withNat (1 + n * 2) fun step =>
    withNat (count * step) fun h =>
    withNat (1 + n * 3) fun n3_1 =>
    withNat (6 + n * 3) fun n3_6 =>
    withNat (5 + n * 3) fun n3_5 =>
    let t_clean := match t with
      | .TBlank m v => Tail.TBlank m v
      | .TCollision m v j => Tail.TCollision m v j
      | .TDefect0 m v _ _ => Tail.TBlank m v
      | .TDefect1 m v _ => Tail.TBlank m v
    ⟨if fromJ then .MJ else .ML, [(.PL n3_1, count)], before h t_clean,
      .MJ, [], (if fromJ then [(.D n3_6, count)] else [(.D n3_6, k)] ++ dn n3_5), after h t_clean,
      t_clean.keep_d, false, t_clean.is_zero⟩

theorem high_valid (x : High) : valid target_tm (high_rule x) := by
  cases x with
  | RightList v =>
    intro u l r hu _ _; rw [hu rfl]
    dsimp [high_rule, mk_rule, Mode.hat, ds, plug]
    exact right_list v l r
  | LeftList v =>
    intro u l r hu _ _; rw [hu rfl]
    dsimp [high_rule, mk_rule, Mode.hat, ds, plug]
    exact left_list v l r
  | Call t =>
    intro u l r _ _ hr
    dsimp only [high_rule, Mode.hat, plug]
    have ht := tail_spec (target_tm := target_tm) u 1 t r (by omega) hr
    revert ht
    cases t
    all_goals
      intro ht
      cases ht with
      | @succ _ _ s _ hcall hzero =>
        cases hzero
        exact hcall l
  | Pairs n k =>
    intro u l r hu _ _; dsimp only [high_rule, mk_rule, imm, Mode.hat, withNat] at hu ⊢
    rw [hu rfl]
    simp only [ds, plug_app, plug_word, plug, SymWord.toList]
    exact pairsR k n l r
  | Loops fromR k b t =>
    intro u l r _ _ hr
    dsimp only [high_rule, withNat, plug]
    let h0 := if fromR then 2 + k else 1 + k
    let h := tail_calls h0 t
    have hh : 0 < h := by
      cases t <;> cases fromR <;> dsimp [h, h0, tail_calls] <;> omega
    have ht := tail_spec (target_tm := target_tm) u h t r hh hr
    revert ht
    cases t
    all_goals
      intro ht
      rw [plug_app, plug_power, plug_run, plug_power]
      cases fromR <;> dsimp [Mode.hat, SymWord.toList]
      · exact loopL ht l b
      · exact loopR_to_L' hh ht l b
  | LoopsJ k b t =>
    intro u l r _ _ hr
    dsimp only [high_rule, withNat, Mode.hat, SymWord.toList, plug]
    let h := tail_calls (1 + k) t
    have hh : 0 < h := by
      cases t <;> dsimp [h, tail_calls] <;> omega
    have ht := tail_spec (target_tm := target_tm) u h t r hh hr
    revert ht
    cases t
    all_goals
      intro ht
      rw [plug_app, plug_power, plug_run, plug_power]
      exact loopJ' hh ht l b
  | Returns fromJ n k t =>
    intro u l r _ _ hr
    dsimp only [high_rule, withNat]
    let t_clean := match t with
      | .TBlank m v => Tail.TBlank m v
      | .TCollision m v j => Tail.TCollision m v j
      | .TDefect0 m v _ _ => Tail.TBlank m v
      | .TDefect1 m v _ => Tail.TBlank m v
    have hpos : 0 < (1 + k) * (1 + n * 2) := by positivity
    have ht := tail_spec (target_tm := target_tm) u ((1 + k) * (1 + n * 2)) t_clean r hpos hr
    revert ht
    cases t
    all_goals
      intro ht
      cases fromJ <;> (
        simp only [Bool.false_eq_true, ↓reduceIte, Mode.hat, plug_app,
          plug_dn, plug_run, plug, SymWord.toList])
      · exact returnsP_L k n ht l
      · exact returnsP_J (1 + k) n ht l


-- ============================================================================
-- Section 6: CBSim (Untrusted Oracle & Verified Checker)
-- ============================================================================

abbrev Instruction := Sum Basic High

def bi (b : Basic) : Option Instruction := some (.inl b)
def hi (h : High) : Option Instruction := some (.inr h)

def recipe_of : Instruction → Recipe
  | .inl b => basic_rule b
  | .inr h => high_rule h

theorem certified (i : Instruction) : valid target_tm (recipe_of i) := by
  cases i with
  | inl b => exact basic_valid b
  | inr h => exact high_valid h


def align (c : RMConfig) : RMConfig :=
  if beqFin6 c.state A then orient Dir.right c
  else if beqFin6 c.state B || beqFin6 c.state C then orient Dir.left c
  else c

theorem align_spec (c : RMConfig) : (align c).denote = c.denote := by
  dsimp [align]
  split_ifs <;> try exact orient_spec _ c
  rfl


def initial : RMConfig := ⟨[], [], A, Dir.right⟩

def Runs.move_right_sym : Nat → Runs → Runs → Option (Runs × Runs)
  | 0, l, r => some (l, r)
  | m + 1, l, (.D n, k) :: r => move_right_sym m (Runs.push (.S n) k l) r
  | _ + 1, _, _ => none

theorem Runs.move_right_sym_spec (m : Nat) (l r l' r' : Runs)
    (h : move_right_sym m l r = some (l', r')) :
    ReachesStar target_tm (CfgR (Runs.denote l) (Runs.denote r)) (CfgR (Runs.denote l') (Runs.denote
      r')) := by
  induction m generalizing l r with
  | zero =>
    simp only [move_right_sym, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    try exact ReachesStar.refl _ _
  | succ m ih =>
    rcases r with _ | ⟨⟨w, k⟩, r_rest⟩; · contradiction
    cases w <;> try contradiction
    rename_i n
    dsimp only [move_right_sym] at h
    have ih' := ih (Runs.push (.S n) k l) r_rest h
    rw [Runs.push_spec] at ih'
    dsimp only [Runs.denote, SymWord.toList] at ih' ⊢
    exact (rule_right_pow (Runs.denote l) (Runs.denote r_rest) n k).trans ih'

def Runs.move_left_sym : Nat → Runs → Runs → Option (Runs × Runs)
  | 0, l, r => some (l, r)
  | m + 1, (.S n, k) :: l, r => move_left_sym m l (Runs.push (.D n) k r)
  | _ + 1, _, _ => none

theorem Runs.move_left_sym_spec (m : Nat) (l r l' r' : Runs)
    (h : move_left_sym m l r = some (l', r')) :
    ReachesStar target_tm (CfgL (Runs.denote l) (Runs.denote r)) (CfgL (Runs.denote l') (Runs.denote
      r')) := by
  induction m generalizing l r with
  | zero =>
    simp only [move_left_sym, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    try exact ReachesStar.refl _ _
  | succ m ih =>
    rcases l with _ | ⟨⟨w, k⟩, l_rest⟩; · contradiction
    cases w <;> try contradiction
    rename_i n
    dsimp only [move_left_sym] at h
    have ih' := ih l_rest (Runs.push (.D n) k r) h
    rw [Runs.push_spec] at ih'
    dsimp only [Runs.denote, SymWord.toList] at ih' ⊢
    exact (rule_left_pow (Runs.denote l_rest) (Runs.denote r) n k).trans ih'


def raw_steps (target_tm : Machine (Fin 2) (Fin 6)) : Nat → RMConfig → Sum RMConfig Bool
  | 0, c => .inl c
  | k + 1, c =>
    let d := if Nat.ble 3 c.state.val then c else align c
    match raw_step target_tm d with
    | some c' => raw_steps target_tm k c'
    | none => .inr true

theorem raw_steps_spec (k : Nat) (c : RMConfig) :
    match raw_steps target_tm k c with
    | .inl c' => ReachesStar target_tm c.denote c'.denote
    | .inr b => b = true → HaltsFrom target_tm c.denote := by
  induction k generalizing c with
  | zero => try exact ReachesStar.refl _ _
  | succ k ih =>
    dsimp only [raw_steps]
    have hd_eq : (if Nat.ble 3 c.state.val then c else align c).denote = c.denote := by
      split_ifs
      · rfl
      · exact align_spec c
    rw [← hd_eq]
    generalize (if Nat.ble 3 c.state.val then c else align c) = d
    have hr := raw_step_spec (target_tm := target_tm) d
    cases hraw : raw_step target_tm d with
    | none =>
      rw [hraw] at hr; dsimp only at hr ⊢
      intro _; exact hr
    | some c' =>
      rw [hraw] at hr; dsimp only at hr ⊢
      have ih' := ih c'
      cases hrs : raw_steps target_tm k c' with
      | inl c'' => rw [hrs] at ih'; exact hr.trans ih'
      | inr b => rw [hrs] at ih'; intro hb; exact HaltsFrom.of_reachesStar hr (ih' hb)


theorem denote_eq_plug_default (r : Runs) : Runs.denote r = plug r default := by
  induction r with
  | nil => rfl
  | cons wn xs ih => rcases wn with ⟨w, n⟩; dsimp only [Runs.denote, plug]; rw [ih]

theorem push_plug (w : SymWord) (n : Nat) (xs : Runs) (t : ListBlank (Fin 2)) :
    plug (Runs.push w n xs) t = (w.toList ^ n) +> plug xs t := by
  dsimp only [Runs.push]
  cases he : w.isEmpty
  · cases hn : Nat.beq n 0
    · simp only [Bool.or_self, Bool.false_eq_true, ↓reduceIte]
      cases xs with
      | nil => rfl
      | cons vm ys =>
        rcases vm with ⟨v, m⟩
        dsimp only [withNat]
        cases h : SymWord.beq w v
        · simp [plug]
        · simp [plug, ← SymWord.beq_eq w v h, pow_append_pow]
    · simp [Nat.eq_of_beq_eq_true hn]
  · simp [SymWord.isEmpty_spec w he, nil_pow]

theorem put_plug (xs ys : Runs) (t : ListBlank (Fin 2)) :
    plug (put xs ys) t = plug xs (plug ys t) := by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    dsimp [put, plug]
    rw [push_plug, ih]

theorem exact_head_plug (w : SymWord) (n : Nat) (xs ys : Runs) (t : ListBlank (Fin 2))
    (h : Runs.exact_head w n xs = some ys) : plug xs t = (w.toList ^ n) +> plug ys t := by
  cases xs with
  | nil => contradiction
  | cons vm rest =>
    rcases vm with ⟨v, m⟩
    dsimp only [Runs.exact_head, withNat] at h
    cases hwv : SymWord.beq w v <;> rw [hwv] at h
    · contradiction
    simp only [↓reduceIte] at h
    cases hnm : Nat.beq n m <;> rw [hnm] at h
    · simp only [Bool.false_eq_true, ↓reduceIte] at h
      cases hlt : Nat.blt n m <;> rw [hlt] at h
      · contradiction
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      dsimp only [plug]
      rw [SymWord.beq_eq w v hwv, pow_append_pow]
      have hlt' : n < m := Nat.le_of_ble_eq_true hlt
      have hm : n + (m - n) = m := by omega
      rw [hm]
    · simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      dsimp only [plug]
      rw [SymWord.beq_eq w v hwv, Nat.eq_of_beq_eq_true hnm]

def Mode.beq : Mode → Mode → Bool
  | .MR, .MR => true
  | .ML, .ML => true
  | .MJ, .MJ => true
  | .MA, .MA => true
  | .MB, .MB => true
  | .MC, .MC => true
  | _, _ => false

theorem Mode.beq_eq (a b : Mode) (h : Mode.beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

def append_d0 (z : Nat) : Runs → Runs
  | [] => if Nat.beq z 0 then [] else [(.D 0, z)]
  | [(w, k)] => Runs.push w k (if Nat.beq z 0 then [] else [(.D 0, z)])
  | x :: xs => x :: append_d0 z xs

theorem denote_d0_ite (z : Nat) :
    Runs.denote (if Nat.beq z 0 then [] else [(.D 0, z)]) = ((D_word 0) ^ z) +> default := by
  by_cases hz : Nat.beq z 0 = true
  · rw [if_pos hz]
    have hz0 : z = 0 := Nat.eq_of_beq_eq_true hz
    subst hz0
    rfl
  · rw [if_neg hz]
    rfl

theorem append_d0_spec (z : Nat) (r : Runs) :
    Runs.denote (append_d0 z r) = plug r (((D_word 0) ^ z) +> default) := by
  induction r with
  | nil =>
    dsimp only [append_d0, plug]
    exact denote_d0_ite z
  | cons x xs ih =>
    rcases x with ⟨w, k⟩
    cases xs with
    | nil =>
      dsimp only [append_d0, plug]
      rw [Runs.push_spec, denote_d0_ite]
    | cons y ys =>
      dsimp only [append_d0, Runs.denote, plug]
      rw [ih]
      rfl

def is_all_d : Runs → Bool
  | [] => true
  | (.D _, _) :: xs => is_all_d xs
  | _ => false

def to_digits : Runs → Digits
  | [] => []
  | (.D n, k) :: xs => (n, k) :: to_digits xs
  | _ :: xs => to_digits xs

theorem ds_to_digits (r : Runs) (h : is_all_d r = true) : ds (to_digits r) = r := by
  induction r with
  | nil => rfl
  | cons x xs ih =>
    rcases x with ⟨w, k⟩
    cases w <;> try contradiction
    dsimp only [is_all_d] at h
    dsimp only [to_digits, ds_cons]
    rw [ih h]

theorem is_all_d_push (n k : Nat) (r : Runs) (hr : is_all_d r = true) :
    is_all_d (Runs.push (.D n) k r) = true := by
  unfold Runs.push
  split_ifs
  · exact hr
  · cases r with
    | nil => rfl
    | cons x xs =>
      rcases x with ⟨v, m⟩
      cases v <;> try contradiction
      dsimp only [is_all_d] at hr
      dsimp only [withNat]
      split_ifs <;> exact hr

theorem is_all_d_put (xs r : Runs) (hxs : is_all_d xs = true) (hr : is_all_d r = true) :
    is_all_d (put xs r) = true := by
  induction xs with
  | nil => exact hr
  | cons x xs ih =>
    rcases x with ⟨w, k⟩
    cases w <;> try contradiction
    dsimp only [is_all_d] at hxs
    dsimp only [put]
    exact is_all_d_push _ k (put xs r) (ih hxs)

theorem is_all_d_append_d0 (z : Nat) (r : Runs) (hr : is_all_d r = true) :
    is_all_d (append_d0 z r) = true := by
  have hd0 : is_all_d (if Nat.beq z 0 then [] else [(.D 0, z)]) = true := by
    split_ifs <;> rfl
  induction r with
  | nil => exact hd0
  | cons x xs ih =>
    rcases x with ⟨w, k⟩
    cases w <;> try contradiction
    dsimp only [is_all_d] at hr
    cases xs with
    | nil => exact is_all_d_push _ k _ hd0
    | cons y ys => dsimp only [append_d0, is_all_d]; exact ih hr

def take_d : Runs → Runs → Option Runs
  | [], ys => some ys
  | [(.D n, k)], ys => Runs.exact_head (.D n) k ys
  | _, _ => none

theorem take_d_plug (ri ys zs : Runs) (t : ListBlank (Fin 2)) (h : take_d ri ys = some zs) :
    plug ys t = plug ri (plug zs t) := by
  rcases ri with _ | ⟨⟨w, k⟩, rest⟩
  · injection h with h; subst h; rfl
  · cases w <;> try contradiction
    cases rest <;> try contradiction
    dsimp only [take_d] at h
    dsimp only [plug]
    exact exact_head_plug _ k ys zs t h

theorem is_all_d_take_d (ri ys zs : Runs) (hys : is_all_d ys = true) (h : take_d ri ys = some zs) :
    is_all_d zs = true := by
  rcases ri with _ | ⟨⟨w, k⟩, rest⟩
  · injection h with h; subst h; exact hys
  · cases w <;> try contradiction
    cases rest <;> try contradiction
    dsimp only [take_d] at h
    rcases ys with _ | ⟨⟨v, m⟩, ys_rest⟩; · contradiction
    cases v <;> try contradiction
    dsimp only [is_all_d] at hys
    dsimp only [Runs.exact_head, withNat] at h
    split_ifs at h <;> (injection h with h; subst h; exact hys)

theorem is_all_d_move_right (m : Nat) (l r l' r' : Runs) (hr : is_all_d r = true)
    (h : Runs.move_right_sym m l r = some (l', r')) : is_all_d r' = true := by
  induction m generalizing l r with
  | zero => simp only [Runs.move_right_sym, Option.some.injEq, Prod.mk.injEq] at h; rcases h with
    ⟨_, rfl⟩; exact hr
  | succ m ih =>
    rcases r with _ | ⟨⟨w, k⟩, r_rest⟩; · contradiction
    cases w <;> try contradiction
    dsimp only [is_all_d] at hr
    exact ih _ r_rest hr h

theorem is_all_d_move_left (m : Nat) (l r l' r' : Runs) (hr : is_all_d r = true)
    (h : Runs.move_left_sym m l r = some (l', r')) : is_all_d r' = true := by
  induction m generalizing l r with
  | zero => simp only [Runs.move_left_sym, Option.some.injEq, Prod.mk.injEq] at h; rcases h with
    ⟨_, rfl⟩; exact hr
  | succ m ih =>
    rcases l with _ | ⟨⟨w, k⟩, l_rest⟩; · contradiction
    cases w <;> try contradiction
    exact ih l_rest _ (is_all_d_push _ k r hr) h

theorem move_right_sym_plug (m : Nat) (l r l' r' : Runs) (t : ListBlank (Fin 2))
    (h : Runs.move_right_sym m l r = some (l', r')) :
    ReachesStar target_tm (CfgR (Runs.denote l) (plug r t)) (CfgR (Runs.denote l') (plug r' t)) :=
      by
  induction m generalizing l r with
  | zero =>
    simp only [Runs.move_right_sym, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    try exact ReachesStar.refl _ _
  | succ m ih =>
    rcases r with _ | ⟨⟨w, k⟩, r_rest⟩; · contradiction
    cases w <;> try contradiction
    rename_i n
    dsimp only [Runs.move_right_sym] at h
    have ih' := ih (Runs.push (.S n) k l) r_rest h
    rw [Runs.push_spec] at ih'
    dsimp only [plug, SymWord.toList] at ih' ⊢
    exact (rule_right_pow (Runs.denote l) (plug r_rest t) n k).trans ih'

theorem move_left_sym_plug (m : Nat) (l r l' r' : Runs) (t : ListBlank (Fin 2))
    (h : Runs.move_left_sym m l r = some (l', r')) :
    ReachesStar target_tm (CfgL (Runs.denote l) (plug r t)) (CfgL (Runs.denote l') (plug r' t)) :=
      by
  induction m generalizing l r with
  | zero =>
    simp only [Runs.move_left_sym, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    try exact ReachesStar.refl _ _
  | succ m ih =>
    rcases l with _ | ⟨⟨w, k⟩, l_rest⟩; · contradiction
    cases w <;> try contradiction
    rename_i n
    dsimp only [Runs.move_left_sym] at h
    have ih' := ih l_rest (Runs.push (.D n) k r) h
    rw [push_plug] at ih'
    dsimp only [Runs.denote, SymWord.toList] at ih' ⊢
    exact (rule_left_pow (Runs.denote l_rest) (plug r t) n k).trans ih'

structure FastConfig where
  left : Runs
  right : Runs
  mode : Mode
  d_tail : Option Nat
  deriving DecidableEq

def FastConfig.WF (fc : FastConfig) : Prop :=
  match fc.d_tail with
  | none => True
  | some _ => is_all_d fc.right = true

def tail_denote : Option Nat → ListBlank (Fin 2)
  | none => default
  | some z => ((D_word 0) ^ z) +> default

def flush_d_runs (dt : Option Nat) (r : Runs) : Runs :=
  match dt with
  | none => r
  | some z => if Nat.beq z 0 then r else append_d0 z r

theorem flush_d_runs_spec (dt : Option Nat) (r : Runs) :
    Runs.denote (flush_d_runs dt r) = plug r (tail_denote dt) := by
  cases dt with
  | none => exact denote_eq_plug_default r
  | some z =>
    dsimp only [flush_d_runs, tail_denote]
    by_cases hz : Nat.beq z 0 = true
    · rw [if_pos hz]
      have hz0 : z = 0 := Nat.eq_of_beq_eq_true hz
      subst hz0
      rw [denote_eq_plug_default]
      rfl
    · rw [if_neg hz]
      exact append_d0_spec z r

def flush_fc (fc : FastConfig) : RMConfig :=
  let r1 := flush_d_runs fc.d_tail fc.right
  ⟨fc.left, Runs.push (.raw fc.mode.payload) 1 r1, fc.mode.mq, fc.mode.md⟩

theorem mode_push_denote (m : Mode) (l r : Runs) :
    (RMConfig.mk l (Runs.push (.raw m.payload) 1 r) m.mq m.md).denote =
    m.hat (Runs.denote l) (Runs.denote r) := by
  cases m <;> (
    dsimp only [RMConfig.denote, Mode.md, Mode.mq, Mode.hat, Mode.payload]
    rw [Runs.push_spec]
    simp [SymWord.toList, pow_succ_list, List.append_nil, CfgR, CfgL, CfgJ])

theorem flush_fc_denote (fc : FastConfig) :
    (flush_fc fc).denote =
      fc.mode.hat (Runs.denote fc.left) (plug fc.right (tail_denote fc.d_tail)) := by
  dsimp only [flush_fc]
  rw [mode_push_denote, flush_d_runs_spec]

def of_rm (c : RMConfig) : Option FastConfig :=
  if beqFin6 c.state A then
    let d := orient Dir.right c
    some ⟨d.left, d.right, .MA, none⟩
  else if beqFin6 c.state B then
    let d := orient Dir.left c
    some ⟨d.left, d.right, .MB, none⟩
  else if beqFin6 c.state C then
    let d := orient Dir.left c
    some ⟨d.left, d.right, .MC, none⟩
  else none

theorem of_rm_spec (c : RMConfig) (fc : FastConfig) (h : of_rm c = some fc) :
    (flush_fc fc).denote = c.denote ∧ fc.WF := by
  dsimp only [of_rm] at h
  split_ifs at h with hA hB hC
  · injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [flush_fc_denote, ← orient_spec Dir.right c]
    have hd_dir := orient_dir Dir.right c
    have hd_st := orient_state Dir.right c
    generalize orient Dir.right c = d at hd_dir hd_st
    rcases d with ⟨dl, dr, dq, ddir⟩
    dsimp only at hd_dir hd_st ⊢
    have hq : dq = A := by rw [hd_st, beqFin6_eq _ _ hA]
    subst hq hd_dir
    dsimp only [Mode.hat, tail_denote, RMConfig.denote]
    rw [← denote_eq_plug_default]
  · injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [flush_fc_denote, ← orient_spec Dir.left c]
    have hd_dir := orient_dir Dir.left c
    have hd_st := orient_state Dir.left c
    generalize orient Dir.left c = d at hd_dir hd_st
    rcases d with ⟨dl, dr, dq, ddir⟩
    dsimp only at hd_dir hd_st ⊢
    have hq : dq = B := by rw [hd_st, beqFin6_eq _ _ hB]
    subst hq hd_dir
    dsimp only [Mode.hat, tail_denote, RMConfig.denote]
    rw [← denote_eq_plug_default]
  · injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [flush_fc_denote, ← orient_spec Dir.left c]
    have hd_dir := orient_dir Dir.left c
    have hd_st := orient_state Dir.left c
    generalize orient Dir.left c = d at hd_dir hd_st
    rcases d with ⟨dl, dr, dq, ddir⟩
    dsimp only at hd_dir hd_st ⊢
    have hq : dq = C := by rw [hd_st, beqFin6_eq _ _ hC]
    subst hq hd_dir
    dsimp only [Mode.hat, tail_denote, RMConfig.denote]
    rw [← denote_eq_plug_default]

def enter_mode (hi : Mode) (l r : Runs) (m : Mode) : Option (Runs × Runs) :=
  if Mode.beq m hi then
    some (l, r)
  else
    let c : RMConfig := ⟨l, Runs.push (.raw m.payload) 1 r, m.mq, m.md⟩
    if beqFin6 c.state hi.mq then
      let d := orient hi.md c
      match remove_prefix hi.payload d.right with
      | some rs => some (d.left, rs)
      | none => none
    else none

theorem enter_mode_spec (hi : Mode) (l r : Runs) (m : Mode) (ls rs : Runs)
    (h : enter_mode hi l r m = some (ls, rs)) :
    (flush_fc ⟨l, r, m, none⟩).denote = hi.hat (Runs.denote ls) (Runs.denote rs) := by
  dsimp only [enter_mode] at h
  by_cases hm : Mode.beq m hi = true
  · rw [if_pos hm] at h
    injection h with h; rcases h with ⟨rfl, rfl⟩
    rw [Mode.beq_eq m hi hm, flush_fc_denote]
    dsimp only [tail_denote]
    rw [← denote_eq_plug_default]
  · rw [if_neg hm] at h
    let c : RMConfig := ⟨l, Runs.push (.raw m.payload) 1 r, m.mq, m.md⟩
    change (if beqFin6 c.state hi.mq then _ else none) = some (ls, rs) at h
    cases hst : beqFin6 c.state hi.mq <;> rw [hst] at h; · contradiction
    simp only [↓reduceIte] at h
    have hc_eq : (flush_fc ⟨l, r, m, none⟩).denote = c.denote := rfl
    rw [hc_eq, ← orient_spec hi.md c]
    have hd_dir := orient_dir hi.md c
    have hd_st := orient_state hi.md c
    generalize orient hi.md c = d at h hd_dir hd_st
    rcases d with ⟨dl, dr, dq, ddir⟩
    dsimp only at h hd_dir hd_st
    have hq : dq = hi.mq := by rw [hd_st, beqFin6_eq _ _ hst]
    subst hq hd_dir
    cases hrp : remove_prefix hi.payload dr <;> rw [hrp] at h; · contradiction
    injection h with h; rcases h with ⟨rfl, rfl⟩
    have hrs := remove_prefix_spec hi.payload dr rs hrp
    cases hi <;> (
      dsimp only [RMConfig.denote, Mode.md, Mode.mq, Mode.hat, Mode.payload] at hrs ⊢
      rw [hrs]
      simp [CfgR, CfgL, CfgJ])

def mk_fc_out (check_all_d : Bool) (l r : Runs) (m : Mode) : FastConfig :=
  let dt := if check_all_d then (if is_all_d r then some 0 else none) else none
  ⟨l, r, m, dt⟩

theorem mk_fc_out_spec (check_all_d : Bool) (l r : Runs) (m : Mode) :
    (flush_fc (mk_fc_out check_all_d l r m)).denote = m.hat (Runs.denote l) (Runs.denote r) ∧
    (mk_fc_out check_all_d l r m).WF := by
  dsimp only [mk_fc_out]
  split_ifs with h1 h2
  · refine ⟨?_, h2⟩
    dsimp only [flush_fc, flush_d_runs]
    rw [mode_push_denote]
    rfl
  · refine ⟨?_, trivial⟩
    dsimp only [flush_fc, flush_d_runs]
    rw [mode_push_denote]
  · refine ⟨?_, trivial⟩
    dsimp only [flush_fc, flush_d_runs]
    rw [mode_push_denote]

def use_fast_none (p : Recipe) (check_all_d : Bool) (fc : FastConfig) : Option FastConfig :=
  let r0 := flush_d_runs fc.d_tail fc.right
  match enter_mode p.hi fc.left r0 fc.mode with
  | some (ls, rs) =>
    match take p.li ls with
    | some l =>
      if check_zero p.zl l then
        match take_keep_put p.keep_d p.ri p.ro p.zr rs with
        | some r_out =>
          some (mk_fc_out check_all_d (put p.lo l) (put p.ro_pre r_out) p.ho)
        | none => none
      else none
    | none => none
  | none => none

omit rules in
theorem use_fast_none_spec (p : Recipe) (check_all_d : Bool) (fc fc' : FastConfig)
    (hv : valid target_tm p) (hu : use_fast_none p check_all_d fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  dsimp only [use_fast_none] at hu
  cases hem : enter_mode p.hi fc.left (flush_d_runs fc.d_tail fc.right) fc.mode with
  | none => rw [hem] at hu; contradiction
  | some lr =>
    rcases lr with ⟨ls, rs⟩
    rw [hem] at hu; dsimp only at hu
    cases htl : take p.li ls with
    | none => rw [htl] at hu; contradiction
    | some l =>
      rw [htl] at hu; dsimp only at hu
      split_ifs at hu with hzl
      cases htk : take_keep_put p.keep_d p.ri p.ro p.zr rs with
      | none => rw [htk] at hu; contradiction
      | some r_out =>
        rw [htk] at hu; injection hu with hu; subst hu
        rcases mk_fc_out_spec check_all_d (put p.lo l) (put p.ro_pre r_out) p.ho with ⟨hden_out,
          hwf_out⟩
        refine ⟨?_, hwf_out⟩
        have hem_den :=
          enter_mode_spec p.hi fc.left (flush_d_runs fc.d_tail fc.right) fc.mode ls rs hem
        change (flush_fc fc).denote = _ at hem_den
        rw [hem_den, hden_out, take_spec p.li ls l htl, put_spec p.lo l, put_spec p.ro_pre r_out]
        obtain ⟨v, r, hkd, hzr, hrs, hrout⟩ :=
          take_keep_put_spec p.keep_d p.ri p.ro p.zr rs r_out htk
        rw [hrs, hrout]
        exact hv v (Runs.denote l) r hkd (check_zero_spec p.zl l hzl) hzr

def use_pres_d_step (p : Recipe) (l r : Runs) (m : Mode) (z : Nat) : Option FastConfig :=
  if Mode.beq m p.hi && Nat.beq p.keep_d 0 && !p.zl && !p.zr && p.ro_pre.isEmpty && is_all_d p.ro
    then
    match take p.li l, take_d p.ri r with
    | some l', some r1 =>
      some ⟨put p.lo l', put p.ro r1, p.ho, some z⟩
    | _, _ => none
  else none

omit rules in
theorem use_pres_d_step_spec (p : Recipe) (l r : Runs) (m : Mode) (z : Nat) (fc' : FastConfig)
    (hr : is_all_d r = true) (hv : valid target_tm p)
    (hu : use_pres_d_step p l r m z = some fc') :
    ReachesStar target_tm (flush_fc ⟨l, r, m, some z⟩).denote (flush_fc fc').denote ∧ fc'.WF := by
  dsimp only [use_pres_d_step] at hu
  split_ifs at hu with hcond
  rcases Bool.and_eq_true_iff.mp hcond with ⟨hcond1, hro⟩
  rcases Bool.and_eq_true_iff.mp hcond1 with ⟨hcond2, hro_pre⟩
  rcases Bool.and_eq_true_iff.mp hcond2 with ⟨hcond3, hzr⟩
  rcases Bool.and_eq_true_iff.mp hcond3 with ⟨hcond4, hzl⟩
  rcases Bool.and_eq_true_iff.mp hcond4 with ⟨hm, hkd⟩
  cases htl : take p.li l <;> rw [htl] at hu; · contradiction
  rename_i l'
  cases htr : take_d p.ri r <;> rw [htr] at hu; · contradiction
  rename_i r1
  injection hu with hu; subst hu
  have hwf' : is_all_d (put p.ro r1) = true :=
    is_all_d_put p.ro r1 hro (is_all_d_take_d p.ri r r1 hr htr)
  refine ⟨?_, hwf'⟩
  rw [flush_fc_denote, flush_fc_denote]
  dsimp only
  rw [Mode.beq_eq m p.hi hm, take_spec p.li l l' htl, put_spec p.lo l',
      take_d_plug p.ri r r1 (tail_denote (some z)) htr,
      put_plug p.ro r1 (tail_denote (some z))]
  have hv' := hv [] (Runs.denote l') (plug r1 (tail_denote (some z)))
    (fun _ => rfl)
    (by intro h; rw [h] at hzl; contradiction)
    (by intro h; rw [h] at hzr; contradiction)
  rw [List.isEmpty_iff.mp hro_pre] at hv'
  exact hv'

def use_pres_all_d (p : Recipe) (fc : FastConfig) : Option FastConfig :=
  match fc.d_tail with
  | none => use_fast_none p false fc
  | some z =>
    match use_pres_d_step p fc.left fc.right fc.mode z with
    | some fc' => some fc'
    | none =>
      if Nat.beq z 0 then none
      else use_pres_d_step p fc.left (append_d0 z fc.right) fc.mode 0

theorem flush_append_d0_eq (l r : Runs) (m : Mode) (z : Nat) :
    (flush_fc ⟨l, append_d0 z r, m, some 0⟩).denote = (flush_fc ⟨l, r, m, some z⟩).denote := by
  rw [flush_fc_denote, flush_fc_denote]
  dsimp only [tail_denote]
  rw [pow_zero_list, listblank_append_nil, ← denote_eq_plug_default, append_d0_spec]

omit rules in
theorem use_pres_all_d_spec (p : Recipe) (fc fc' : FastConfig)
    (hwf : fc.WF) (hv : valid target_tm p) (hu : use_pres_all_d p fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  rcases fc with ⟨l, r, m, dt⟩
  cases dt with
  | none => exact use_fast_none_spec p false ⟨l, r, m, none⟩ fc' hv hu
  | some z =>
    dsimp only [use_pres_all_d] at hu
    dsimp only [FastConfig.WF] at hwf
    cases hstep : use_pres_d_step p l r m z <;> rw [hstep] at hu
    · dsimp only at hu
      split_ifs at hu with hz0
      rw [← flush_append_d0_eq l r m z]
      exact use_pres_d_step_spec p l (append_d0 z r) m 0 fc' (is_all_d_append_d0 z r hwf) hv hu
    · injection hu with hu; subst fc'
      exact use_pres_d_step_spec p l r m z _ hwf hv hstep

def exec_tblank1_step (p : Recipe) (l r : Runs) (m : Mode) (z : Nat) : Option FastConfig :=
  if Mode.beq m p.hi && Nat.beq p.keep_d 1 && !p.zl && p.ri.isEmpty && is_all_d p.ro_pre then
    match p.ro, take p.li l with
    | [(.D 0, h2)], some l' =>
      withNat (z + h2) fun z' =>
      some ⟨put p.lo l', put p.ro_pre r, p.ho, some z'⟩
    | _, _ => none
  else none

omit rules in
theorem exec_tblank1_step_spec (p : Recipe) (l r : Runs) (m : Mode) (z : Nat) (fc' : FastConfig)
    (hr : is_all_d r = true) (hv : valid target_tm p)
    (hu : exec_tblank1_step p l r m z = some fc') :
    ReachesStar target_tm (flush_fc ⟨l, r, m, some z⟩).denote (flush_fc fc').denote ∧ fc'.WF := by
  dsimp only [exec_tblank1_step, withNat] at hu
  split_ifs at hu with hcond
  rcases Bool.and_eq_true_iff.mp hcond with ⟨hcond1, hro_pre⟩
  rcases Bool.and_eq_true_iff.mp hcond1 with ⟨hcond2, hri⟩
  rcases Bool.and_eq_true_iff.mp hcond2 with ⟨hcond3, hzl⟩
  rcases Bool.and_eq_true_iff.mp hcond3 with ⟨hm, hkd⟩
  rcases hro : p.ro with _ | ⟨⟨w, h2⟩, ro_rest⟩ <;> rw [hro] at hu; · contradiction
  cases w <;> try contradiction
  rename_i d
  cases d <;> try contradiction
  cases ro_rest <;> try contradiction
  cases htl : take p.li l <;> rw [htl] at hu; · contradiction
  rename_i l'
  injection hu with hu; subst hu
  refine ⟨?_, is_all_d_put p.ro_pre r hro_pre hr⟩
  rw [flush_fc_denote, flush_fc_denote]
  dsimp only
  rw [Mode.beq_eq m p.hi hm, take_spec p.li l l' htl, put_spec p.lo l',
      put_plug p.ro_pre r (tail_denote (some (z + h2)))]
  let u : Digits := to_digits r ++ [(0, z)]
  have hdu : ds u = r ++ [(.D 0, z)] := by
    dsimp only [u]
    rw [ds_app, ds_to_digits r hr]
    rfl
  have hin : plug r (tail_denote (some z)) = plug (ds u) (plug p.ri default) := by
    rw [hdu, List.isEmpty_iff.mp hri, plug_app]
    rfl
  have hout : plug r (tail_denote (some (z + h2))) = plug (ds u) (plug p.ro default) := by
    rw [hdu, hro, plug_app]
    dsimp only [plug, tail_denote, SymWord.toList]
    rw [pow_append_pow]
  rw [hin, hout]
  have hkd1 : p.keep_d = 1 := Nat.eq_of_beq_eq_true hkd
  exact hv u (Runs.denote l') default
    (by intro hc; rw [hkd1] at hc; contradiction)
    (by intro h; rw [h] at hzl; contradiction)
    (fun _ => rfl)

def step_right_d_step (m : Nat) (l r : Runs) (mode : Mode) (z : Nat) : Option FastConfig :=
  if Mode.beq mode .MR then
    match Runs.move_right_sym m l r with
    | some (l', r') => some ⟨l', r', .MR, some z⟩
    | none => none
  else none

theorem step_right_d_step_spec (m : Nat) (l r : Runs) (mode : Mode) (z : Nat) (fc' : FastConfig)
    (hr : is_all_d r = true) (h : step_right_d_step m l r mode z = some fc') :
    ReachesStar target_tm (flush_fc ⟨l, r, mode, some z⟩).denote (flush_fc fc').denote ∧ fc'.WF :=
      by
  dsimp only [step_right_d_step] at h
  split_ifs at h with hm
  cases hmr : Runs.move_right_sym m l r <;> rw [hmr] at h; · contradiction
  rename_i lr'; rcases lr' with ⟨l', r'⟩
  injection h with h; subst h
  refine ⟨?_, is_all_d_move_right m l r l' r' hr hmr⟩
  rw [flush_fc_denote, flush_fc_denote, Mode.beq_eq mode .MR hm]
  exact move_right_sym_plug m l r l' r' (tail_denote (some z)) hmr

def step_right_sym_fast (m : Nat) (fc : FastConfig) : Option FastConfig :=
  match fc.d_tail with
  | none =>
    match enter_mode .MR fc.left fc.right fc.mode with
    | some (ls, rs) =>
      match Runs.move_right_sym m ls rs with
      | some (l', r') => some ⟨l', r', .MR, none⟩
      | none => none
    | none => none
  | some z =>
    match step_right_d_step m fc.left fc.right fc.mode z with
    | some fc' => some fc'
    | none =>
      if Nat.beq z 0 then none
      else step_right_d_step m fc.left (append_d0 z fc.right) fc.mode 0

theorem step_right_sym_fast_spec (m : Nat) (fc fc' : FastConfig)
    (hwf : fc.WF) (h : step_right_sym_fast m fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  rcases fc with ⟨l, r, mode, dt⟩
  cases dt with
  | none =>
    dsimp only [step_right_sym_fast] at h
    cases hem : enter_mode .MR l r mode <;> rw [hem] at h; · contradiction
    rename_i lrs; rcases lrs with ⟨ls, rs⟩
    dsimp only at h
    cases hmr : Runs.move_right_sym m ls rs <;> rw [hmr] at h; · contradiction
    rename_i lr'; rcases lr' with ⟨l', r'⟩
    injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [enter_mode_spec .MR l r mode ls rs hem, flush_fc_denote]
    dsimp only [Mode.hat, tail_denote]
    rw [denote_eq_plug_default rs]
    exact move_right_sym_plug m ls rs l' r' default hmr
  | some z =>
    dsimp only [step_right_sym_fast] at h
    dsimp only [FastConfig.WF] at hwf
    cases hstep : step_right_d_step m l r mode z <;> rw [hstep] at h
    · dsimp only at h
      split_ifs at h with hz0
      rw [← flush_append_d0_eq l r mode z]
      exact step_right_d_step_spec m l (append_d0 z r) mode 0 fc' (is_all_d_append_d0 z r hwf) h
    · injection h with h; subst fc'
      exact step_right_d_step_spec m l r mode z _ hwf hstep

def step_left_sym_fast (m : Nat) (fc : FastConfig) : Option FastConfig :=
  match fc.d_tail with
  | none =>
    match enter_mode .ML fc.left fc.right fc.mode with
    | some (ls, rs) =>
      match Runs.move_left_sym m ls rs with
      | some (l', r') => some ⟨l', r', .ML, none⟩
      | none => none
    | none => none
  | some z =>
    if Mode.beq fc.mode .ML then
      match Runs.move_left_sym m fc.left fc.right with
      | some (l', r') => some ⟨l', r', .ML, some z⟩
      | none => none
    else none

theorem step_left_sym_fast_spec (m : Nat) (fc fc' : FastConfig)
    (hwf : fc.WF) (h : step_left_sym_fast m fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  rcases fc with ⟨l, r, mode, dt⟩
  cases dt with
  | none =>
    dsimp only [step_left_sym_fast] at h
    cases hem : enter_mode .ML l r mode <;> rw [hem] at h; · contradiction
    rename_i lrs; rcases lrs with ⟨ls, rs⟩
    dsimp only at h
    cases hml : Runs.move_left_sym m ls rs <;> rw [hml] at h; · contradiction
    rename_i lr'; rcases lr' with ⟨l', r'⟩
    injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [enter_mode_spec .ML l r mode ls rs hem, flush_fc_denote]
    dsimp only [Mode.hat, tail_denote]
    rw [denote_eq_plug_default rs]
    exact move_left_sym_plug m ls rs l' r' default hml
  | some z =>
    dsimp only [step_left_sym_fast] at h
    dsimp only [FastConfig.WF] at hwf
    split_ifs at h with hm
    cases hml : Runs.move_left_sym m l r <;> rw [hml] at h; · contradiction
    rename_i lr'; rcases lr' with ⟨l', r'⟩
    injection h with h; subst h
    refine ⟨?_, is_all_d_move_left m l r l' r' hwf hml⟩
    rw [flush_fc_denote, flush_fc_denote, Mode.beq_eq mode .ML hm]
    exact move_left_sym_plug m l r l' r' (tail_denote (some z)) hml

def step_left_raw_sym_fast (n0 m : Nat) (fc : FastConfig) : Option FastConfig :=
  match fc.d_tail with
  | none =>
    match enter_mode .ML fc.left fc.right fc.mode with
    | some (ls, rs) =>
      match Runs.remove_sym_one (.S n0) ls with
      | some l1 =>
        match Runs.move_left_sym m l1 (Runs.push (.D n0) 1 rs) with
        | some (l', r') => some ⟨l', r', .ML, none⟩
        | none => none
      | none => none
    | none => none
  | some z =>
    if Mode.beq fc.mode .ML then
      match Runs.remove_sym_one (.S n0) fc.left with
      | some l1 =>
        match Runs.move_left_sym m l1 (Runs.push (.D n0) 1 fc.right) with
        | some (l', r') => some ⟨l', r', .ML, some z⟩
        | none => none
      | none => none
    else none

theorem step_left_raw_sym_fast_spec (n0 m : Nat) (fc fc' : FastConfig)
    (hwf : fc.WF) (h : step_left_raw_sym_fast n0 m fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  rcases fc with ⟨l, r, mode, dt⟩
  cases dt with
  | none =>
    dsimp only [step_left_raw_sym_fast] at h
    cases hem : enter_mode .ML l r mode <;> rw [hem] at h; · contradiction
    rename_i lrs; rcases lrs with ⟨ls, rs⟩
    dsimp only at h
    cases hro : Runs.remove_sym_one (.S n0) ls <;> rw [hro] at h; · contradiction
    rename_i l1
    dsimp only at h
    cases hml : Runs.move_left_sym m l1 (Runs.push (.D n0) 1 rs) <;> rw [hml] at h; · contradiction
    rename_i lr'; rcases lr' with ⟨l', r'⟩
    injection h with h; subst h
    refine ⟨?_, trivial⟩
    rw [enter_mode_spec .ML l r mode ls rs hem, flush_fc_denote,
        Runs.remove_sym_one_spec (.S n0) ls l1 hro]
    dsimp only [Mode.hat, tail_denote, SymWord.toList]
    rw [denote_eq_plug_default rs]
    have h1 : ReachesStar target_tm (CfgL (S_word n0 +> Runs.denote l1) (plug rs default))
        (CfgL (Runs.denote l1) (plug (Runs.push (.D n0) 1 rs) default)) := by
      rw [push_plug]
      simpa [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil] using
        rules.rule_left (Runs.denote l1) (plug rs default) n0
    exact h1.trans (move_left_sym_plug m l1 (Runs.push (.D n0) 1 rs) l' r' default hml)
  | some z =>
    dsimp only [step_left_raw_sym_fast] at h
    dsimp only [FastConfig.WF] at hwf
    split_ifs at h with hm
    cases hro : Runs.remove_sym_one (.S n0) l <;> rw [hro] at h; · contradiction
    rename_i l1
    dsimp only at h
    cases hml : Runs.move_left_sym m l1 (Runs.push (.D n0) 1 r) <;> rw [hml] at h; · contradiction
    rename_i lr'; rcases lr' with ⟨l', r'⟩
    injection h with h; subst h
    refine ⟨?_,
      is_all_d_move_left m l1 (Runs.push (.D n0) 1 r) l' r' (is_all_d_push n0 1 r hwf) hml⟩
    rw [flush_fc_denote, flush_fc_denote, Mode.beq_eq mode .ML hm,
        Runs.remove_sym_one_spec (.S n0) l l1 hro]
    dsimp only [Mode.hat, SymWord.toList]
    have h1 : ReachesStar target_tm (CfgL (S_word n0 +>
      Runs.denote l1) (plug r (tail_denote (some z))))
        (CfgL (Runs.denote l1) (plug (Runs.push (.D n0) 1 r) (tail_denote (some z)))) := by
      rw [push_plug]
      simpa [SymWord.toList, pow_succ_list, pow_zero_list, List.append_nil] using
        rules.rule_left (Runs.denote l1) (plug r (tail_denote (some z))) n0
    exact h1.trans (move_left_sym_plug m l1 (Runs.push (.D n0) 1 r) l' r' (tail_denote (some z))
      hml)

def is_pres_d_inst : Instruction → Bool
  | .inl (.Restart _) | .inl (.CollisionD _) | .inl (.LeftJ _) | .inl (.TurnB _) | .inl (.TurnJ _)
      => true
  | .inr (.LeftList _) => true
  | _ => false

def to_tblank1_inst : Instruction → Option Instruction
  | .inr (.Call (.TBlank _ [])) => some (.inr (.Call (.TBlank 1 [])))
  | .inr (.Loops fromR k b (.TBlank _ [])) => some (.inr (.Loops fromR k b (.TBlank 1 [])))
  | .inr (.LoopsJ k b (.TBlank _ [])) => some (.inr (.LoopsJ k b (.TBlank 1 [])))
  | .inr (.Returns fromJ n k (.TBlank _ [])) => some (.inr (.Returns fromJ n k (.TBlank 1 [])))
  | _ => none

def is_tblank_inst : Instruction → Bool
  | .inr (.Call (.TBlank _ _)) => true
  | .inr (.Loops _ _ _ (.TBlank _ _)) => true
  | .inr (.LoopsJ _ _ (.TBlank _ _)) => true
  | .inr (.Returns _ _ _ (.TBlank _ _)) => true
  | _ => false

def exec_inst_fast (i : Instruction) (fc : FastConfig) : Option FastConfig :=
  if is_pres_d_inst i then
    use_pres_all_d (recipe_of i) fc
  else
    match fc.d_tail, to_tblank1_inst i with
    | some z, some i1 =>
      match exec_tblank1_step (recipe_of i1) fc.left fc.right fc.mode z with
      | some fc' => some fc'
      | none => use_fast_none (recipe_of i) (is_tblank_inst i) fc
    | _, _ =>
      use_fast_none (recipe_of i) (is_tblank_inst i) fc

theorem exec_inst_fast_spec (i : Instruction) (fc fc' : FastConfig)
    (hwf : fc.WF) (h : exec_inst_fast i fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  rcases fc with ⟨l, r, mode, dt⟩
  dsimp only [exec_inst_fast] at h
  have hcert := certified (target_tm := target_tm) i
  split_ifs at h with hpres
  · exact use_pres_all_d_spec (recipe_of i) ⟨l, r, mode, dt⟩ fc' hwf hcert h
  · cases dt with
    | none =>
      exact use_fast_none_spec (recipe_of i) (is_tblank_inst i) ⟨l, r, mode, none⟩ fc' hcert h
    | some z =>
      cases ht1 : to_tblank1_inst i <;> rw [ht1] at h
      · exact use_fast_none_spec (recipe_of i) (is_tblank_inst i) ⟨l, r, mode, some z⟩ fc' hcert h
      · rename_i i1
        dsimp only at h
        cases hex : exec_tblank1_step (recipe_of i1) l r mode z <;> rw [hex] at h
        · exact use_fast_none_spec (recipe_of i) (is_tblank_inst i) ⟨l, r, mode, some z⟩ fc' hcert h
        · injection h with h; subst fc'
          have hcert1 := certified (target_tm := target_tm) i1
          exact exec_tblank1_step_spec (recipe_of i1) l r mode z _ hwf hcert1 hex

def mask6 : Nat := 63
def mask10 : Nat := 1023
def mask40 : Nat := 1099511627775

def pop40 {α : Type} (w : Nat) (k : Nat → Nat → α) : α :=
  withNat (Nat.land w mask40) fun x =>
  withNat (Nat.shiftRight w 40) fun w' =>
  k x w'

def decode_digits : Nat → Nat → Digits
  | 0, _ => []
  | len + 1, w =>
    pop40 w fun n w1 =>
    pop40 w1 fun m w2 =>
    (n, m) :: decode_digits len w2

def decode_tail (w : Nat) : Tail :=
  pop40 w fun tag w1 =>
  pop40 w1 fun m w2 =>
  if Nat.beq tag 0 then
    pop40 w2 fun len w3 =>
    .TBlank m (decode_digits len w3)
  else if Nat.beq tag 1 then
    pop40 w2 fun j w3 =>
    pop40 w3 fun len w4 =>
    .TCollision m (decode_digits len w4) j
  else if Nat.beq tag 2 then
    pop40 w2 fun j w3 =>
    pop40 w3 fun d w4 =>
    pop40 w4 fun len w5 =>
    .TDefect0 m (decode_digits len w5) j d
  else
    pop40 w2 fun d w3 =>
    pop40 w3 fun len w4 =>
    .TDefect1 m (decode_digits len w4) d

def decode_inst (tag : Nat) (w1 : Nat) : Instruction :=
  if Nat.ble tag 16 then
    if Nat.ble tag 8 then
      if Nat.beq tag 2 then .inl (.ScanR w1)
      else if Nat.beq tag 3 then .inl (.ScanB w1)
      else if Nat.beq tag 4 then .inl (.ScanC w1)
      else if Nat.beq tag 5 then .inl (.ScanPair w1)
      else if Nat.beq tag 6 then .inl (.Ones w1)
      else if Nat.beq tag 7 then .inl .Blank
      else .inl (.Even w1)
    else
      if Nat.beq tag 9 then .inl (.Restart w1)
      else if Nat.beq tag 10 then .inl (.Over2 w1)
      else if Nat.beq tag 11 then
        pop40 w1 fun a b => .inl (.Over1 a b)
      else if Nat.beq tag 12 then .inl .Collision
      else if Nat.beq tag 13 then .inl (.CollisionD w1)
      else if Nat.beq tag 14 then .inl (.LeftJ w1)
      else if Nat.beq tag 15 then .inl (.TurnB w1)
      else .inl (.TurnJ w1)
  else
    if Nat.ble tag 25 then
      if Nat.beq tag 17 then .inl (.Defect0 w1)
      else if Nat.beq tag 18 then .inl (.Defect1 w1)
      else if Nat.beq tag 19 then
        pop40 w1 fun a b => .inl (.Defect2 a b)
      else if Nat.beq tag 20 then .inl (.Defect0D w1)
      else if Nat.beq tag 21 then .inl (.Defect1D w1)
      else if Nat.beq tag 22 then
        pop40 w1 fun a b => .inl (.Defect2D a b)
      else if Nat.beq tag 23 then .inl .DefectBlank0
      else if Nat.beq tag 24 then .inl (.DefectBlankS w1)
      else
        pop40 w1 fun a b => .inl (.Paired a b)
    else
      if Nat.beq tag 26 then
        pop40 w1 fun a b => .inr (.Pairs a b)
      else if Nat.beq tag 27 then
        pop40 w1 fun len w2 => .inr (.RightList (decode_digits len w2))
      else if Nat.beq tag 28 then
        pop40 w1 fun len w2 => .inr (.LeftList (decode_digits len w2))
      else if Nat.beq tag 29 then
        .inr (.Call (decode_tail w1))
      else if Nat.beq tag 30 then
        pop40 w1 fun a w2 =>
        pop40 w2 fun k w3 =>
        pop40 w3 fun b w4 =>
        .inr (.Loops (Nat.beq a 1) k b (decode_tail w4))
      else if Nat.beq tag 31 then
        pop40 w1 fun a w2 =>
        pop40 w2 fun b w3 =>
        .inr (.LoopsJ a b (decode_tail w3))
      else
        pop40 w1 fun a w2 =>
        pop40 w2 fun n w3 =>
        pop40 w3 fun k w4 =>
        .inr (.Returns (Nat.beq a 1) n k (decode_tail w4))

def exec_macro_fast (tag : Nat) (w1 : Nat) (fc : FastConfig) : Option FastConfig :=
  if Nat.beq tag 33 then
    step_right_sym_fast w1 fc
  else if Nat.beq tag 34 then
    step_left_sym_fast w1 fc
  else if Nat.beq tag 35 then
    pop40 w1 fun n0 m =>
    step_left_raw_sym_fast n0 m fc
  else
    exec_inst_fast (decode_inst tag w1) fc

theorem exec_macro_fast_spec (tag : Nat) (w1 : Nat) (fc fc' : FastConfig)
    (hwf : fc.WF) (h : exec_macro_fast tag w1 fc = some fc') :
    ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF := by
  dsimp only [exec_macro_fast, pop40, withNat] at h
  split_ifs at h with h33 h34 h35
  · exact step_right_sym_fast_spec w1 fc fc' hwf h
  · exact step_left_sym_fast_spec w1 fc fc' hwf h
  · exact step_left_raw_sym_fast_spec _ _ fc fc' hwf h
  · exact exec_inst_fast_spec (decode_inst tag w1) fc fc' hwf h


def run_word_fast_base (target_tm : Machine (Fin 2) (Fin 6)) (w : Nat) (fc : FastConfig) :
    Sum FastConfig Bool :=
  withNat (Nat.land w mask6) fun tag =>
  withNat (Nat.land (Nat.shiftRight w 6) mask10) fun r =>
  withNat (Nat.shiftRight w 16) fun w1 =>
  if Nat.beq tag 1 then
    match raw_steps target_tm r (flush_fc fc) with
    | .inl c' =>
      match of_rm c' with
      | some fc' => .inl fc'
      | none => .inr false
    | .inr b => .inr b
  else if Nat.beq r 0 then
    match exec_macro_fast tag w1 fc with
    | some fc' => .inl fc'
    | none => .inr false
  else
    match raw_steps target_tm r (flush_fc fc) with
    | .inl c1 =>
      match of_rm c1 with
      | some fc1 =>
        match exec_macro_fast tag w1 fc1 with
        | some fc' => .inl fc'
        | none => .inr false
      | none => .inr false
    | .inr b => .inr b

def run_word_fast (target_tm : Machine (Fin 2) (Fin 6)) (oldW newW w : Nat) (fc : FastConfig) :
    Sum FastConfig Bool :=
  run_word_fast_base target_tm (if Nat.beq w oldW then newW else w) fc

theorem run_word_fast_base_spec (w : Nat) (fc : FastConfig) (hwf : fc.WF) :
    match run_word_fast_base target_tm w fc with
    | .inl fc' => ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF
    | .inr b => b = true → HaltsFrom target_tm (flush_fc fc).denote := by
  dsimp only [run_word_fast_base, withNat]
  split_ifs with htag1 hr0
  · have hrs := raw_steps_spec (target_tm := target_tm)
      (Nat.land (Nat.shiftRight w 6) mask10) (flush_fc fc)
    cases hraw : raw_steps target_tm (Nat.land (Nat.shiftRight w 6) mask10) (flush_fc fc) <;>
      rw [hraw] at hrs
    · rename_i c'
      dsimp only at hrs ⊢
      cases hof : of_rm c'
      · intro hc; contradiction
      · rename_i fc'
        rcases of_rm_spec c' fc' hof with ⟨hden, hwf'⟩
        rw [← hden] at hrs
        exact ⟨hrs, hwf'⟩
    · exact hrs
  · cases hex : exec_macro_fast (Nat.land w mask6) (Nat.shiftRight w 16) fc
    · intro hc; contradiction
    · rename_i fc'
      exact exec_macro_fast_spec _ _ fc fc' hwf hex
  · have hrs := raw_steps_spec (target_tm := target_tm)
      (Nat.land (Nat.shiftRight w 6) mask10) (flush_fc fc)
    cases hraw : raw_steps target_tm (Nat.land (Nat.shiftRight w 6) mask10) (flush_fc fc) <;>
      rw [hraw] at hrs
    · rename_i c1
      dsimp only at hrs ⊢
      cases hof : of_rm c1
      · intro hc; contradiction
      · rename_i fc1
        rcases of_rm_spec c1 fc1 hof with ⟨hden1, hwf1⟩
        dsimp only
        cases hex : exec_macro_fast (Nat.land w mask6) (Nat.shiftRight w 16) fc1
        · intro hc; contradiction
        · rename_i fc'
          rcases exec_macro_fast_spec (target_tm := target_tm) _ _ fc1 fc' hwf1 hex with
            ⟨hstep, hwf'⟩
          rw [hden1] at hstep
          exact ⟨hrs.trans hstep, hwf'⟩
    · exact hrs

theorem run_word_fast_spec (oldW newW w : Nat) (fc : FastConfig) (hwf : fc.WF) :
    match run_word_fast target_tm oldW newW w fc with
    | .inl fc' => ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF
    | .inr b => b = true → HaltsFrom target_tm (flush_fc fc).denote :=
  run_word_fast_base_spec (if Nat.beq w oldW then newW else w) fc hwf

def seq_word (target_tm : Machine (Fin 2) (Fin 6)) (oldW newW w : Nat) :
    Sum FastConfig Bool → Sum FastConfig Bool
  | .inl fc => run_word_fast target_tm oldW newW w fc
  | .inr b => .inr b

theorem seq_word_spec (oldW newW w : Nat) (fc0 : FastConfig) (res : Sum FastConfig Bool)
    (h : match res with
      | .inl fc => ReachesStar target_tm (flush_fc fc0).denote (flush_fc fc).denote ∧ fc.WF
      | .inr b => b = true → HaltsFrom target_tm (flush_fc fc0).denote) :
    match seq_word target_tm oldW newW w res with
    | .inl fc' => ReachesStar target_tm (flush_fc fc0).denote (flush_fc fc').denote ∧ fc'.WF
    | .inr b => b = true → HaltsFrom target_tm (flush_fc fc0).denote := by
  cases res with
  | inr b =>
    exact h
  | inl fc =>
    dsimp only [seq_word]
    have hw := run_word_fast_spec (target_tm := target_tm) oldW newW w fc h.2
    cases hr : run_word_fast target_tm oldW newW w fc <;> rw [hr] at hw
    · exact ⟨h.1.trans hw.1, hw.2⟩
    · intro hb
      exact HaltsFrom.of_reachesStar h.1 (hw hb)

def run_tree (target_tm : Machine (Fin 2) (Fin 6)) (oldW newW : Nat) :
    CertTree → FastConfig → Sum FastConfig Bool
  | .nil, c => .inl c
  | .leaf w, c => run_word_fast target_tm oldW newW w c
  | .leaf8 w1 w2 w3 w4 w5 w6 w7 w8, c =>
    seq_word target_tm oldW newW w8
      (seq_word target_tm oldW newW w7
        (seq_word target_tm oldW newW w6
          (seq_word target_tm oldW newW w5
            (seq_word target_tm oldW newW w4
              (seq_word target_tm oldW newW w3
                (seq_word target_tm oldW newW w2
                  (run_word_fast target_tm oldW newW w1 c)))))))
  | .bin t1 t2, c =>
    match run_tree target_tm oldW newW t1 c with
    | .inl c' => run_tree target_tm oldW newW t2 c'
    | .inr b => .inr b

theorem run_tree_spec (oldW newW : Nat) (t : CertTree) (fc : FastConfig) (hwf : fc.WF) :
    match run_tree target_tm oldW newW t fc with
    | .inl fc' => ReachesStar target_tm (flush_fc fc).denote (flush_fc fc').denote ∧ fc'.WF
    | .inr b => b = true → HaltsFrom target_tm (flush_fc fc).denote := by
  induction t generalizing fc with
  | nil =>
    exact ⟨ReachesStar.refl _ _, hwf⟩
  | leaf w =>
    exact run_word_fast_spec oldW newW w fc hwf
  | leaf8 w1 w2 w3 w4 w5 w6 w7 w8 =>
    dsimp only [run_tree]
    apply seq_word_spec; apply seq_word_spec; apply seq_word_spec; apply seq_word_spec
    apply seq_word_spec; apply seq_word_spec; apply seq_word_spec
    exact run_word_fast_spec oldW newW w1 fc hwf
  | bin t1 t2 ih1 ih2 =>
    dsimp only [run_tree]
    have h1 := ih1 fc hwf
    cases hr1 : run_tree target_tm oldW newW t1 fc <;> rw [hr1] at h1
    · rename_i fc1
      dsimp only
      have h2 := ih2 fc1 h1.2
      cases hr2 : run_tree target_tm oldW newW t2 fc1 <;> rw [hr2] at h2
      · exact ⟨h1.1.trans h2.1, h2.2⟩
      · intro hb
        exact HaltsFrom.of_reachesStar h1.1 (h2 hb)
    · exact h1

theorem chain_tree (target_tm : Machine (Fin 2) (Fin 6)) [HasCertRules target_tm]
    (oldW newW : Nat) {t : CertTree} {fc fc' : FastConfig}
    (hwf : fc.WF) (h : run_tree target_tm oldW newW t fc = .inl fc')
    (hrest : fc'.WF → HaltsFrom target_tm (flush_fc fc').denote) :
    HaltsFrom target_tm (flush_fc fc).denote := by
  have hs := run_tree_spec (target_tm := target_tm) oldW newW t fc hwf
  rw [h] at hs
  exact HaltsFrom.of_reachesStar hs.1 (hrest hs.2)

theorem done_tree (target_tm : Machine (Fin 2) (Fin 6)) [HasCertRules target_tm]
    (oldW newW : Nat) {t : CertTree} {fc : FastConfig}
    (hwf : fc.WF) (h : run_tree target_tm oldW newW t fc = .inr true) :
    HaltsFrom target_tm (flush_fc fc).denote := by
  have hs := run_tree_spec (target_tm := target_tm) oldW newW t fc hwf
  rw [h] at hs
  exact hs rfl

end Engine

def cert_tm : Bool → Machine (Fin 2) (Fin 6)
  | false, 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | false, 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | false, 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | false, 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | false, 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | false, 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | false, 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | false, 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | false, 4, 0 => some (some 1, Stmt.write 0 Dir.left)
  | false, 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | false, 5, 0 => some (some 2, Stmt.write 1 Dir.right)
  | false, 5, 1 => none
  | true, 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | true, 0, 1 => some (some 0, Stmt.write 1 Dir.right)
  | true, 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | true, 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | true, 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | true, 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | true, 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | true, 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | true, 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | true, 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | true, 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | true, 5, 1 => none

section CertTmRules

variable (var : Bool)

theorem scanR (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      ⟨some A, ⟨0, l, (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ n) +> r)⟩⟩
      ⟨some A, ⟨0, (([1, 0] : List (Fin 2)) ^ n) +> l, (1 : Fin 2) >> r⟩⟩ := by
  induction n generalizing l with
  | zero => norm_cb; bb_refl
  | succ n ih =>
    cases var <;> (
      nsteps 6
      refine (ih ((1 : Fin 2) >> (0 : Fin 2) >> l)).trans ?_
      norm_cb; bb_refl)

theorem scanR1 (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      ⟨some A, ⟨0, l, (1 : Fin 2) >> (1 : Fin 2) >> ((([1, 1] : List (Fin 2)) ^ n) +> r)⟩⟩
      ⟨some A, ⟨0, (([1, 0] : List (Fin 2)) ^ n) +> l, (1 : Fin 2) >> (1 : Fin 2) >> r⟩⟩ := by
  rw [← rot_11 n r]
  exact scanR var l ((1 : Fin 2) >> r) n

theorem scanB (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (Cfg.headLeft B ((([0, 1] : List (Fin 2)) ^ n) +> l) r)
      (Cfg.headLeft B l ((([1, 1] : List (Fin 2)) ^ n) +> r)) := by
  induction n generalizing r with
  | zero => norm_cb; bb_refl
  | succ n ih =>
    cases var <;> (
      nsteps 2
      refine (ih ([1, 1] +> r)).trans ?_
      norm_cb; bb_refl)

theorem scanC (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (Cfg.headLeft C ((([1, 0] : List (Fin 2)) ^ n) +> l) r)
      (Cfg.headLeft C l ((([1, 1] : List (Fin 2)) ^ n) +> r)) := by
  induction n generalizing r with
  | zero => norm_cb; bb_refl
  | succ n ih =>
    cases var <;> (
      nsteps 2
      refine (ih ([1, 1] +> r)).trans ?_
      norm_cb; bb_refl)

theorem scanPair (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      ⟨some A, ⟨0, l, (1 : Fin 2) >> ((([0, 1, 0, 1] : List (Fin 2)) ^ n) +> r)⟩⟩
      ⟨some A, ⟨0, (([1, 1, 0, 1] : List (Fin 2)) ^ n) +> l, (1 : Fin 2) >> r⟩⟩ := by
  induction n generalizing l with
  | zero => norm_cb; bb_refl
  | succ n ih =>
    cases var <;> (
      nsteps 4
      refine (ih ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> l)).trans ?_
      norm_cb; bb_refl)

theorem ones (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (Cfg.headRight A l ((([1] : List (Fin 2)) ^ n) +> r))
      (Cfg.headRight A ((([1] : List (Fin 2)) ^ n) +> l) r) := by
  induction n generalizing l with
  | zero => norm_cb; bb_refl
  | succ n ih =>
    cases var <;> (
      nsteps 1
      refine (ih ([1] +> l)).trans ?_
      norm_cb; bb_refl)

theorem ones2 (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (Cfg.headRight A l ((([1, 1] : List (Fin 2)) ^ n) +> r))
      (Cfg.headRight A ((([1, 1] : List (Fin 2)) ^ n) +> l) r) := by
  rw [one_pow_two_mul]
  exact ones var l r (2 * n)

theorem rule_right (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var) (CfgR l (D_word n +> r)) (CfgR (S_word n +> l) r) := by
  cases var <;> (nsteps 3; follow (scanR _ _ _ n); bb_refl)

theorem rule_left (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var) (CfgL (S_word n +> l) r) (CfgL l (D_word n +> r)) := by
  cases var <;> (nsteps 5; follow (scanB _ _ _ n); bb_refl)

theorem rule_blank (l r : ListBlank (Fin 2)) :
    ReachesStar (cert_tm var) (CfgR l ([0, 0, 0] +> r)) (CfgL l (D_word 0 +> (D_word 0 +> r))) := by
  cases var <;> fsteps

theorem rule_even (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ((([1, 1] : List (Fin 2)) ^ (1 + n)) +> ([0, 0] +> r)))
      (CfgL l (D_word (1 + n) +> ([1, 0] +> r))) := by
  cases var <;> (nsteps 3; follow (scanR1 _ _ _ n); nsteps 16; follow (scanB _ _ _ n); bb_refl)

theorem rule_restart (l r : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar (cert_tm var)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1, 1, 1] +> l)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) r) := by
  have h : ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1, 1, 1] +> l)) =
      S_word b +> ([1, 1] +> l) := by
    norm_cb
  rw [h]
  refine (rule_left var ([1, 1] +> l) r b).trans ?_
  cases var <;> (nsteps 5; follow (scanR _ _ _ b); bb_refl)

theorem rule_overflow2 (r : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar (cert_tm var)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1, 1] +> default)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ 2) +> ((([1, 1] : List (Fin 2)) ^ (1 +
        b)) +> default)) ([1] +> r)) := by
  cases var <;> (
    nsteps 5; follow (scanB _ _ _ b); nsteps 16; follow (scanR1 _ _ _ b)
    nsteps 16; follow (scanB _ _ _ b); nsteps 9; follow (ones2 _ _ _ b); fsteps)

theorem rule_overflow1 (r : ListBlank (Fin 2)) (b n : Nat) :
    ReachesStar (cert_tm var)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([1] +> default)) (D_word n +> r))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (n +
        2)) +> ((([1, 1] : List (Fin 2)) ^ b) +> default)) ([1, 0] +> r)) := by
  cases var <;> (
    nsteps 5; follow (scanB _ _ _ b); nsteps 7; follow (ones2 _ _ _ b)
    nsteps 8; follow (scanR1 _ _ _ n); nsteps 16; follow (scanB _ _ _ n)
    nsteps 11; follow (scanR _ _ _ n); bb_refl)

theorem rule_collision (l r : ListBlank (Fin 2)) :
    ReachesStar (cert_tm var)
      (CfgL ([0, 0, 1, 1, 0, 1] +> l) r)
      (CfgJ l ([1, 1, 1, 1] +> r)) := by
  cases var <;> fsteps

theorem rule_leftJ (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (CfgJ (S_word n +> l) r)
      (CfgL l (D_word (1 + n) +> r)) := by
  cases var <;> (nsteps 3; follow (scanB _ _ _ n); bb_refl)

theorem rule_turnB (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (CfgL ([1, 1] +> l) (D_word n +> r))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + n)) +> l) r) := by
  cases var <;> (nsteps 5; follow (scanR _ _ _ n); bb_refl)

theorem rule_turnJ (l r : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar (cert_tm var)
      (CfgJ ((([1, 0] : List (Fin 2)) ^ b) +> ([1, 1, 1] +> l)) r)
      (CfgR ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> l) r) := by
  cases var <;> (nsteps 1; follow (scanB _ _ _ b); nsteps 5; follow (scanR _ _ _ b); bb_refl)

theorem rule_finishP (l r : ListBlank (Fin 2)) (b : Nat) :
    ReachesStar (cert_tm var)
      (CfgL ((([1, 0] : List (Fin 2)) ^ (1 + b)) +> ([0, 1] +> (S_word 0 +> l))) r)
      (CfgJ l (D_word (1 + b) +> r)) := by
  cases var <;> (nsteps 4; follow (scanC _ _ _ b); fsteps)

theorem rule_defect0 (l r : ListBlank (Fin 2)) (m : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word 0 +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgJ l ([1, 1, 1, 1] +> (D_word m +> ([1] +> r)))) := by
  cases var <;> (nsteps 15; follow (scanR1 _ _ _ m); nsteps 15; follow (scanC _ _ _ m); fsteps)

theorem rule_defect1 (l r : ListBlank (Fin 2)) (m : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word 1 +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgL l (D_word 0 +> (D_word 0 +> (D_word (1 + m) +> ([1] +> r))))) := by
  cases var <;> (nsteps 17; follow (scanR1 _ _ _ m); nsteps 16; follow (scanB _ _ _ m); fsteps)

theorem rule_defect2 (l r : ListBlank (Fin 2)) (n m : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word (2 +
        n) +> ([1] +> ((([1, 1] : List (Fin 2)) ^ m) +> ([0] +> r))))))
      (CfgR ((([1, 0] : List (Fin 2)) ^ (2 +
        m)) +> ((([1, 1] : List (Fin 2)) ^ n) +> (S_word 0 +> (S_word 0 +> l)))) ([1] +> r)) := by
  cases var <;> (
    nsteps 11; follow (ones2 _ _ _ n); nsteps 8; follow (scanR1 _ _ _ m)
    nsteps 16; follow (scanB _ _ _ m); nsteps 11; follow (scanR _ _ _ m); bb_refl)

theorem rule_defect_blank0 (l r : ListBlank (Fin 2)) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word 0 +> ([0, 0] +> r))))
      (CfgR ([1, 0, 0, 1] +> (S_word 0 +> l)) r) := by
  cases var <;> fsteps

theorem rule_defect_blankS (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word (1 + n) +> ([0, 0] +> r))))
      (CfgR ([1, 0] +> ((([1,
        1] : List (Fin 2)) ^ n) +> ([1] +> (S_word 0 +> (S_word 0 +> l))))) r) := by
  cases var <;> (nsteps 9; follow (ones2 _ _ _ n); fsteps)

theorem rule_paired (l r : ListBlank (Fin 2)) (k n : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ((([1, 0] : List (Fin 2)) ^ (k * 2)) +> (D_word n +> r)))
      (CfgR ((([1, 0] : List (Fin 2)) ^ n) +> ((([1, 1, 0,
        1] : List (Fin 2)) ^ k) +> (S_word 0 +> l))) r) := by
  cases var <;> (nsteps 3; follow (scanPair _ _ _ k); follow (scanR _ _ _ n); bb_refl)

theorem rule_emptyR (l : ListBlank (Fin 2)) :
    ReachesStar (cert_tm var) (CfgR l default) (CfgL l (D_word 0 +> (D_word 0 +> default))) := by
  cases var <;> fsteps

theorem rule_collide (l r : ListBlank (Fin 2)) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word 0 +> (D_word 0 +> r))))
      (CfgJ l (D_word 2 +> ([1, 0] +> r))) := by
  cases var <;> fsteps

theorem rule_pairR (l r : ListBlank (Fin 2)) (n : Nat) :
    ReachesStar (cert_tm var)
      (CfgR l ([1, 0] +> (D_word (2 + n) +> (D_word (2 + n) +> r))))
      (CfgR (PL_word n +> l) ([1, 0] +> r)) := by
  cases var <;> (
    nsteps 11; follow (ones2 _ _ _ n); nsteps 20; follow (scanR1 _ _ _ n)
    nsteps 20; follow (scanB _ _ _ n); nsteps 23; follow (scanR _ _ _ n); bb_refl)

theorem cert_tm_no_some_none :
    ∀ (q : Fin 6) (b : Fin 2), (cert_tm var q b).map Prod.fst ≠ some none := by
  cases var <;> decide

instance : HasCertRules (cert_tm var) where
  no_some_none := cert_tm_no_some_none var
  scanR := scanR var
  scanB := scanB var
  scanC := scanC var
  scanPair := scanPair var
  ones := ones var
  rule_right := rule_right var
  rule_left := rule_left var
  rule_blank := rule_blank var
  rule_even := rule_even var
  rule_restart := rule_restart var
  rule_overflow2 := rule_overflow2 var
  rule_overflow1 := rule_overflow1 var
  rule_collision := rule_collision var
  rule_leftJ := rule_leftJ var
  rule_turnB := rule_turnB var
  rule_turnJ := rule_turnJ var
  rule_finishP := rule_finishP var
  rule_defect0 := rule_defect0 var
  rule_defect1 := rule_defect1 var
  rule_defect2 := rule_defect2 var
  rule_defect_blank0 := rule_defect_blank0 var
  rule_defect_blankS := rule_defect_blankS var
  rule_paired := rule_paired var
  rule_emptyR := rule_emptyR var
  rule_collide := rule_collide var
  rule_pairR := rule_pairR var

end CertTmRules

end BusyBeaver.CertTreeEngine
