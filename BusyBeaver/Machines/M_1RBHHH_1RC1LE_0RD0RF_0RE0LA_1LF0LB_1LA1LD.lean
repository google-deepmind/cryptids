/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

@[expose] public section

namespace BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

open Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

local notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
local notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
local notation3 c₁ " [" M "]⊢* " c₂ => ReachesStar M c₁ c₂
local notation3 c₁ " [" M "]⊢⁺ " c₂ => ReachesPlus M c₁ c₂


-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

open SixState

-- ============================================================================
-- Section 6: Reflective Symbolic Execution & Certificate Checker
-- ============================================================================

namespace Cert


macro "nlin" : tactic => `(tactic| ((try simp only [Nat.add_mul, Nat.mul_add,
  Nat.mul_assoc]) <;> omega))

abbrev Sym := Fin 2
abbrev St := Fin 6
abbrev TM := Machine Sym St

-- ---------------------------------------------------------------------------
-- 6.1 Multi-step infrastructure
-- ---------------------------------------------------------------------------

theorem ms_zero (M : TM) (c : Cfg Sym St) : multiStep M c 0 = some c := rfl

theorem ms_succ (M : TM) (c : Cfg Sym St) (n : ℕ) :
    multiStep M c (n + 1) = Option.bind (multiStep M c n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

theorem ms_add (M : TM) (c : Cfg Sym St) (n m : ℕ) :
    multiStep M c (n + m) = (multiStep M c n).bind (fun c' => multiStep M c' m) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← Nat.add_assoc, ms_succ, ih, Option.bind_assoc]
    congr 1; funext c'; rw [ms_succ]

theorem ms_one (M : TM) (c c' : Cfg Sym St) (h : step M c = some c') :
    multiStep M c 1 = some c' := by
  rw [ms_succ, ms_zero]; simpa using h

def RStar (M : TM) (c c' : Cfg Sym St) : Prop := ∃ n, multiStep M c n = some c'
def RPlus (M : TM) (c c' : Cfg Sym St) : Prop := ∃ n > 0, multiStep M c n = some c'

theorem rstar_refl (M : TM) (c : Cfg Sym St) : RStar M c c := ⟨0, rfl⟩

theorem rstar_trans {M : TM} {a b c : Cfg Sym St} (h1 : RStar M a b) (h2 : RStar M b c) :
    RStar M a c := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by rw [ms_add, hn]; simpa using hm⟩

theorem rplus_rstar {M : TM} {a b : Cfg Sym St} (h : RPlus M a b) : RStar M a b := by
  obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

theorem rplus_trans_star {M : TM} {a b c : Cfg Sym St} (h1 : RPlus M a b) (h2 : RStar M b c) :
    RPlus M a c := by
  obtain ⟨n, hn0, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [ms_add, hn]; simpa using hm⟩

theorem rstar_trans_plus {M : TM} {a b c : Cfg Sym St} (h1 : RStar M a b) (h2 : RPlus M b c) :
    RPlus M a c := by
  obtain ⟨n, hn⟩ := h1; obtain ⟨m, hm0, hm⟩ := h2
  exact ⟨n + m, by omega, by rw [ms_add, hn]; simpa using hm⟩

theorem step_rplus {M : TM} {a b : Cfg Sym St} (h : step M a = some b) : RPlus M a b :=
  ⟨1, by omega, ms_one M a b h⟩

-- ---------------------------------------------------------------------------
-- 6.2 List powers and ListBlank lemmas
-- ---------------------------------------------------------------------------

theorem lpow_zero (l : List Sym) : l ^ (0 : ℕ) = [] := rfl
theorem lpow_succ (l : List Sym) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := rfl

theorem lpow_add (l : List Sym) (n m : ℕ) : l ^ (n + m) = l ^ n ++ l ^ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_right_comm, lpow_succ, lpow_succ, ih, List.append_assoc]

theorem lpow_succ' (l : List Sym) (n : ℕ) : l ^ (n + 1) = l ^ n ++ l := by
  rw [lpow_add]; simp
theorem lpow_one (l : List Sym) : l ^ (1 : ℕ) = l := by
  simp

theorem lpow_mul (l : List Sym) (k n : ℕ) : (l ^ k) ^ n = l ^ (k * n) := by
  induction n with
  | zero => simp
  | succ n ih => rw [lpow_succ, ih, Nat.mul_succ, Nat.add_comm, lpow_add]

theorem lpow_rot (u w : List Sym) (n : ℕ) : (u ++ w) ^ n ++ u = u ++ (w ++ u) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [lpow_succ, lpow_succ, List.append_assoc, ih]; simp [List.append_assoc]

theorem lb_app_nil (t : ListBlank Sym) : ListBlank.append [] t = t := rfl
theorem lb_app_cons (x : Sym) (l : List Sym) (t : ListBlank Sym) :
    ListBlank.append (x :: l) t = ListBlank.cons x (ListBlank.append l t) := rfl
theorem lb_app_app (l1 l2 : List Sym) (t : ListBlank Sym) :
    ListBlank.append (l1 ++ l2) t = ListBlank.append l1 (ListBlank.append l2 t) :=
  ListBlank.append_assoc l1 l2 t

theorem lb_cons_zero_default : ListBlank.cons (0 : Sym) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl

theorem lb_zeros_default1 (z : List Sym) (hz : ∀ x ∈ z, x = 0) :
    ListBlank.append z default = default := by
  induction z with
  | nil => rfl
  | cons x z ihz =>
    rw [lb_app_cons, ihz (fun y hy => hz y (List.mem_cons_of_mem _ hy)),
      hz x List.mem_cons_self, lb_cons_zero_default]

theorem lb_zeros_default (z : List Sym) (hz : ∀ x ∈ z, x = 0) (n : ℕ) :
    ListBlank.append (z ^ n) default = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [lpow_succ, lb_app_app, ih, lb_zeros_default1 z hz]

-- ---------------------------------------------------------------------------
-- 6.3 Linear expressions over variables
-- ---------------------------------------------------------------------------

structure Lin where
  c : ℕ
  cs : List ℕ
deriving DecidableEq

def dotv (v : ℕ → ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, i => a * v i + dotv v as (i + 1)

def Lin.eval (v : ℕ → ℕ) (e : Lin) : ℕ := e.c + dotv v e.cs 0

-- all coefficients zero (structural recursion, so the kernel can evaluate it)
def zall : List ℕ → Bool
  | [] => true
  | a :: as => a == 0 && zall as

def csEq : List ℕ → List ℕ → Bool
  | [], bs => zall bs
  | a :: as, [] => zall (a :: as)
  | a :: as, b :: bs => a == b && csEq as bs

def Lin.beq (a b : Lin) : Bool := a.c == b.c && csEq a.cs b.cs

theorem zall_dotv : ∀ (bs : List ℕ), zall bs = true → ∀ v i, dotv v bs i = 0
  | [], _, _, _ => rfl
  | b :: bs, h, v, i => by
    simp only [zall, Bool.and_eq_true, beq_iff_eq] at h
    simp [dotv, h.1, zall_dotv bs h.2 v (i + 1)]

theorem csEq_nil_left (bs : List ℕ) (h : csEq [] bs = true) (v : ℕ → ℕ) (i : ℕ) :
    dotv v bs i = 0 := zall_dotv bs h v i

theorem csEq_sound : ∀ (as bs : List ℕ), csEq as bs = true → ∀ v i, dotv v as i = dotv v bs i
  | [], bs, h, v, i => by rw [csEq_nil_left bs h]; rfl
  | a :: as, [], h, v, i => by
    rw [zall_dotv (a :: as) h v i]; rfl
  | a :: as, b :: bs, h, v, i => by
    simp only [csEq, Bool.and_eq_true, beq_iff_eq] at h
    simp [dotv, h.1, csEq_sound as bs h.2 v (i + 1)]

theorem Lin.beq_sound (a b : Lin) (h : a.beq b = true) (v : ℕ → ℕ) : a.eval v = b.eval v := by
  simp only [Lin.beq, Bool.and_eq_true, beq_iff_eq] at h
  simp [Lin.eval, h.1, csEq_sound _ _ h.2 v 0]

def Lin.const (k : ℕ) : Lin := ⟨k, []⟩
def Lin.var (i : ℕ) : Lin := ⟨0, List.replicate i 0 ++ [1]⟩

theorem Lin.eval_const (k : ℕ) (v : ℕ → ℕ) : (Lin.const k).eval v = k := by
  simp [Lin.const, Lin.eval, dotv]

theorem dotv_var (v : ℕ → ℕ) : ∀ (i j : ℕ), dotv v (List.replicate i 0 ++ [1]) j = v (j + i)
  | 0, j => by simp [dotv]
  | i + 1, j => by
    simp only [List.replicate_succ, List.cons_append, dotv, Nat.zero_mul, Nat.zero_add]
    rw [dotv_var v i (j + 1)]; congr 1; omega

theorem Lin.eval_var (i : ℕ) (v : ℕ → ℕ) : (Lin.var i).eval v = v i := by
  simp [Lin.var, Lin.eval, dotv_var]

def allZero : List ℕ → Bool
  | [] => true
  | a :: as => a == 0 && allZero as

theorem allZero_dotv : ∀ (as : List ℕ), allZero as = true → ∀ v i, dotv v as i = 0
  | [], _, _, _ => rfl
  | a :: as, h, v, i => by
    simp only [allZero, Bool.and_eq_true, beq_iff_eq] at h
    simp [dotv, h.1, allZero_dotv as h.2 v (i + 1)]

def Lin.isConst (e : Lin) (k : ℕ) : Bool := e.c == k && allZero e.cs

theorem Lin.isConst_eval (e : Lin) (k : ℕ) (h : e.isConst k = true) (v : ℕ → ℕ) :
    e.eval v = k := by
  simp only [Lin.isConst, Bool.and_eq_true, beq_iff_eq] at h
  simp [Lin.eval, h.1, allZero_dotv _ h.2 v 0]

def addCs : List ℕ → List ℕ → List ℕ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addCs as bs

theorem dotv_addCs (v : ℕ → ℕ) : ∀ (as bs : List ℕ) (i : ℕ),
    dotv v (addCs as bs) i = dotv v as i + dotv v bs i
  | [], bs, i => by simp [addCs, dotv]
  | a :: as, [], i => by simp [addCs, dotv]
  | a :: as, b :: bs, i => by
    simp only [addCs, dotv, dotv_addCs v as bs (i + 1)]; nlin

def Lin.add (a b : Lin) : Lin := ⟨a.c + b.c, addCs a.cs b.cs⟩

theorem Lin.eval_add (a b : Lin) (v : ℕ → ℕ) : (a.add b).eval v = a.eval v + b.eval v := by
  simp only [Lin.add, Lin.eval, dotv_addCs]; nlin

def Lin.scale (k : ℕ) (a : Lin) : Lin := ⟨k * a.c, a.cs.map (k * ·)⟩

theorem dotv_scale (v : ℕ → ℕ) (k : ℕ) : ∀ (as : List ℕ) (i : ℕ),
    dotv v (as.map (k * ·)) i = k * dotv v as i
  | [], i => by simp [dotv]
  | a :: as, i => by
    simp only [List.map_cons, dotv, dotv_scale v k as (i + 1)]; nlin

theorem Lin.eval_scale (k : ℕ) (a : Lin) (v : ℕ → ℕ) : (a.scale k).eval v = k * a.eval v := by
  simp only [Lin.scale, Lin.eval, dotv_scale]; nlin

def Lin.dec (a : Lin) : Lin := ⟨a.c - 1, a.cs⟩

theorem Lin.eval_dec (a : Lin) (h : 1 ≤ a.c) (v : ℕ → ℕ) : a.eval v = a.dec.eval v + 1 := by
  simp only [Lin.dec, Lin.eval]; omega

def divCs (k : ℕ) : List ℕ → Option (List ℕ)
  | [] => some []
  | a :: as => if a % k == 0 then (divCs k as).map (fun r => (a / k) :: r) else none

theorem divCs_sound (v : ℕ → ℕ) (k : ℕ) : ∀ (as rs : List ℕ), divCs k as = some rs →
    ∀ i, dotv v as i = k * dotv v rs i
  | [], rs, h, i => by
    simp only [divCs, Option.some.injEq] at h; subst h; simp [dotv]
  | a :: as, rs, h, i => by
    simp only [divCs] at h
    split at h
    · rename_i hk
      simp only [beq_iff_eq] at hk
      cases hd : divCs k as with
      | none => simp [hd] at h
      | some r =>
        simp only [hd, Option.map_some, Option.some.injEq] at h
        subst h
        simp only [dotv, divCs_sound v k as r hd (i + 1)]
        have : a = k * (a / k) := by
          have := Nat.div_add_mod a k; omega
        conv_lhs => rw [this]
        nlin
    · simp at h

def Lin.div (k : ℕ) (a : Lin) : Option Lin :=
  if a.c % k == 0 then (divCs k a.cs).map (fun r => ⟨a.c / k, r⟩) else none

theorem Lin.div_sound (k : ℕ) (a b : Lin) (h : a.div k = some b) (v : ℕ → ℕ) :
    a.eval v = k * b.eval v := by
  simp only [Lin.div] at h
  split at h
  · rename_i hk
    simp only [beq_iff_eq] at hk
    cases hd : divCs k a.cs with
    | none => simp [hd] at h
    | some r =>
      simp only [hd, Option.map_some, Option.some.injEq] at h
      subst h
      simp only [Lin.eval, divCs_sound v k a.cs r hd 0]
      have : a.c = k * (a.c / k) := by
        have := Nat.div_add_mod a.c k; omega
      conv_lhs => rw [this]
      nlin
  · simp at h

-- single-variable substitution x_i := f
def setZero : List ℕ → ℕ → List ℕ
  | [], _ => []
  | _ :: as, 0 => 0 :: as
  | a :: as, i + 1 => a :: setZero as i

def getC : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, i + 1 => getC as i

theorem dotv_setZero (v : ℕ → ℕ) : ∀ (as : List ℕ) (j i : ℕ),
    dotv v as i = dotv v (setZero as j) i + getC as j * v (i + j)
  | [], j, i => by simp [setZero, getC, dotv]
  | a :: as, 0, i => by
    simp only [setZero, getC, dotv, Nat.add_zero, Nat.zero_mul, Nat.zero_add]; nlin
  | a :: as, j + 1, i => by
    simp only [setZero, getC, dotv]
    rw [dotv_setZero v as j (i + 1)]
    have : i + 1 + j = i + (j + 1) := by omega
    rw [this]; nlin

theorem getC_setZero : ∀ (as : List ℕ) (j : ℕ), getC (setZero as j) j = 0
  | [], j => by simp [setZero, getC]
  | a :: as, 0 => by simp [setZero, getC]
  | a :: as, j + 1 => by simp [setZero, getC, getC_setZero as j]

theorem dotv_update_lt (v : ℕ → ℕ) (p x : ℕ) : ∀ (as : List ℕ) (i : ℕ), p < i →
    dotv (Function.update v p x) as i = dotv v as i
  | [], i, _ => rfl
  | a :: as, i, h => by
    simp only [dotv]
    rw [dotv_update_lt v p x as (i + 1) (by omega)]
    have : Function.update v p x i = v i := Function.update_of_ne (by omega) _ _
    rw [this]

theorem dotv_update (v : ℕ → ℕ) (x : ℕ) : ∀ (as : List ℕ) (j i : ℕ),
    dotv (Function.update v (i + j) x) as i + getC as j * v (i + j) =
      dotv v as i + getC as j * x
  | [], j, i => by simp [dotv, getC]
  | a :: as, 0, i => by
    simp only [dotv, getC, Nat.add_zero]
    rw [dotv_update_lt v i x as (i + 1) (by omega)]
    simp only [Function.update_self]; nlin
  | a :: as, j + 1, i => by
    simp only [dotv, getC]
    have h2 : i + (j + 1) = (i + 1) + j := by omega
    have h1 : Function.update v (i + 1 + j) x i = v i :=
      Function.update_of_ne (by omega) _ _
    rw [h2, h1]
    have := dotv_update v x as j (i + 1)
    omega

def Lin.subst (a : Lin) (i : ℕ) (f : Lin) : Lin :=
  (⟨a.c, setZero a.cs i⟩ : Lin).add (f.scale (getC a.cs i))


theorem Lin.eval_subst (a : Lin) (i : ℕ) (f : Lin) (v : ℕ → ℕ) :
    (a.subst i f).eval v = a.eval (Function.update v i (f.eval v)) := by
  have h1 := dotv_setZero (Function.update v i (f.eval v)) a.cs i 0
  have h2 := dotv_update v (f.eval v) (setZero a.cs i) i 0
  rw [getC_setZero, Nat.zero_add] at h2
  rw [Nat.zero_add, Function.update_self] at h1
  rw [Lin.subst, Lin.eval_add, Lin.eval_scale]
  change a.c + dotv v (setZero a.cs i) 0 + getC a.cs i * f.eval v = a.c + dotv _ a.cs 0
  omega

-- simultaneous substitution x_j := σ[j] (variables beyond σ are kept)
def substCs : List ℕ → List Lin → ℕ → Lin
  | [], _, _ => Lin.const 0
  | a :: as, σ, i => ((σ.headD (Lin.var i)).scale a).add (substCs as σ.tail (i + 1))

def sem (σ : List Lin) (v : ℕ → ℕ) (j : ℕ) : ℕ := (σ.getD j (Lin.var j)).eval v

theorem getD_zero (x : Lin) (σ : List Lin) (d : Lin) : (x :: σ).getD 0 d = x := rfl

theorem getD_succ (x : Lin) (σ : List Lin) (j : ℕ) (d : Lin) :
    (x :: σ).getD (j + 1) d = σ.getD j d := rfl

theorem headD_drop : ∀ (σ : List Lin) (i : ℕ) (d : Lin), (σ.drop i).headD d = σ.getD i d
  | [], i, d => by cases i <;> simp
  | x :: σ, 0, d => by simp
  | x :: σ, i + 1, d => by
    simp only [List.drop_succ_cons, List.getD_cons_succ]; exact headD_drop σ i d

theorem tail_drop' : ∀ (σ : List Lin) (i : ℕ), (σ.drop i).tail = σ.drop (i + 1)
  | [], i => by cases i <;> simp
  | x :: σ, 0 => by simp
  | x :: σ, i + 1 => by simp only [List.drop_succ_cons]; exact tail_drop' σ i

theorem substCs_eval (v : ℕ → ℕ) : ∀ (as : List ℕ) (σ : List Lin) (i : ℕ),
    (substCs as (σ.drop i) i).eval v = dotv (sem σ v) as i
  | [], σ, i => by simp [substCs, dotv, Lin.eval_const]
  | a :: as, σ, i => by
    simp only [substCs, dotv, Lin.eval_add, Lin.eval_scale]
    rw [tail_drop', substCs_eval v as σ (i + 1), headD_drop]
    rfl

def Lin.substAll (σ : List Lin) (a : Lin) : Lin := (Lin.const a.c).add (substCs a.cs σ 0)

theorem Lin.eval_substAll (σ : List Lin) (a : Lin) (v : ℕ → ℕ) :
    (a.substAll σ).eval v = a.eval (sem σ v) := by
  have := substCs_eval v a.cs σ 0
  simp only [List.drop_zero] at this
  simp only [Lin.substAll, Lin.eval_add, Lin.eval_const, this]; rfl

-- recognising a bare variable
def varIdx : List ℕ → ℕ → Option ℕ
  | [], _ => none
  | a :: as,
    i => if a == 1 && allZero as then some i else if a == 0 then varIdx as (i + 1) else none

theorem varIdx_sound (v : ℕ → ℕ) : ∀ (as : List ℕ) (i k : ℕ), varIdx as i = some k →
    dotv v as i = v k
  | [], i, k, h => by simp [varIdx] at h
  | a :: as, i, k, h => by
    simp only [varIdx] at h
    split at h
    · rename_i h1
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      simp only [Option.some.injEq] at h
      subst h
      simp [dotv, h1.1, allZero_dotv as h1.2 v (i + 1)]
    · split at h
      · rename_i h2
        simp only [beq_iff_eq] at h2
        simp [dotv, h2, varIdx_sound v as (i + 1) k h]
      · simp at h

def Lin.asVar (e : Lin) : Option ℕ := if e.c == 0 then varIdx e.cs 0 else none

theorem Lin.asVar_sound (e : Lin) (k : ℕ) (h : e.asVar = some k) (v : ℕ → ℕ) : e.eval v = v k := by
  simp only [Lin.asVar] at h
  split at h
  · rename_i h0
    simp only [beq_iff_eq] at h0
    simp [Lin.eval, h0, varIdx_sound v e.cs 0 k h]
  · simp at h

-- ---------------------------------------------------------------------------
-- 6.4 Symbolic tapes
-- ---------------------------------------------------------------------------

structure Seg where
  b : List Sym
  e : Lin

/-- Denotation of a half-tape (listed from the head outwards) on top of a tail `t`. -/
def hden (v : ℕ → ℕ) : List Seg → ListBlank Sym → ListBlank Sym
  | [], t => t
  | s :: r, t => ListBlank.append (s.b ^ s.e.eval v) (hden v r t)

theorem den_append (v : ℕ → ℕ) : ∀ (A B : List Seg) (t : ListBlank Sym),
    hden v (A ++ B) t = hden v A (hden v B t)
  | [], B, t => rfl
  | s :: A, B, t => by simp only [List.cons_append, hden, den_append v A B t]

theorem den_single (v : ℕ → ℕ) (w : Sym) (r : List Seg) (t : ListBlank Sym) :
    hden v (⟨[w], Lin.const 1⟩ :: r) t = ListBlank.cons w (hden v r t) := by
  simp only [hden, Lin.eval_const, lpow_one]; rfl

def sideSubst (i : ℕ) (f : Lin) : List Seg → List Seg
  | [] => []
  | s :: A => ⟨s.b, s.e.subst i f⟩ :: sideSubst i f A

theorem den_subst (v : ℕ → ℕ) (i : ℕ) (f : Lin) : ∀ (A : List Seg) (t : ListBlank Sym),
    hden v (sideSubst i f A) t = hden (Function.update v i (f.eval v)) A t
  | [], t => rfl
  | s :: A, t => by simp only [sideSubst, hden, Lin.eval_subst, den_subst v i f A t]

def sideSubstAll (σ : List Lin) : List Seg → List Seg
  | [] => []
  | s :: A => ⟨s.b, s.e.substAll σ⟩ :: sideSubstAll σ A

theorem den_substAll (v : ℕ → ℕ) (σ : List Lin) : ∀ (A : List Seg) (t : ListBlank Sym),
    hden v (sideSubstAll σ A) t = hden (sem σ v) A t
  | [], t => rfl
  | s :: A, t => by simp only [sideSubstAll, hden, Lin.eval_substAll, den_substAll v σ A t]

def sideEq : List Seg → List Seg → Bool
  | [], [] => true
  | a :: as, b :: bs => (a.b == b.b && a.e.beq b.e) && sideEq as bs
  | _, _ => false

theorem sideEq_sound : ∀ (A B : List Seg), sideEq A B = true → ∀ v t, hden v A t = hden v B t
  | [], [], _, v, t => rfl
  | a :: as, b :: bs, h, v, t => by
    simp only [sideEq, Bool.and_eq_true, beq_iff_eq] at h
    simp only [hden, h.1.1, Lin.beq_sound _ _ h.1.2 v, sideEq_sound as bs h.2 v t]
  | [], _ :: _, h, _, _ => by simp [sideEq] at h
  | _ :: _, [], h, _, _ => by simp [sideEq] at h

def singles : List Sym → List Seg
  | [] => []
  | x :: xs => ⟨[x], Lin.const 1⟩ :: singles xs

theorem den_singles (v : ℕ → ℕ) : ∀ (b : List Sym) (r : List Seg) (t : ListBlank Sym),
    hden v (singles b ++ r) t = ListBlank.append b (hden v r t)
  | [], r, t => rfl
  | x :: xs, r, t => by
    simp only [singles, List.cons_append, den_single, den_singles v xs r t, lb_app_cons]

def takeSingles : ℕ → List Seg → Option (List Sym × List Seg)
  | 0, A => some ([], A)
  | k + 1, s :: A =>
    match s.b with
    | [x] => if s.e.isConst 1 then (takeSingles k A).map (fun p => (x :: p.1, p.2)) else none
    | _ => none
  | _ + 1, [] => none

theorem takeSingles_sound (v : ℕ → ℕ) : ∀ (k : ℕ) (A : List Seg) (xs : List Sym) (r : List Seg),
    takeSingles k A = some (xs, r) → ∀ t, hden v A t = ListBlank.append xs (hden v r t)
  | 0, A, xs, r, h, t => by
    simp only [takeSingles, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1, ← h.2]; rfl
  | k + 1, [], xs, r, h, t => by simp [takeSingles] at h
  | k + 1, ⟨b, e⟩ :: A, xs, r, h, t => by
    rcases b with _ | ⟨x, _ | ⟨y, b⟩⟩
    · simp [takeSingles] at h
    · simp only [takeSingles] at h
      split at h
      · rename_i he
        cases hk : takeSingles k A with
        | none => simp [hk] at h
        | some p =>
          simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rcases p with ⟨p1, p2⟩
          rw [← h.1, ← h.2]
          simp only [hden, Lin.isConst_eval e 1 he v, lpow_one, lb_app_cons, lb_app_nil]
          rw [takeSingles_sound v k A p1 p2 hk t]
      · simp at h
    · simp [takeSingles] at h

-- ---------------------------------------------------------------------------
-- 6.5 Local rewrites of half-tapes (denotation preserving for every tail)
-- ---------------------------------------------------------------------------

inductive RW
  | splitF
  | splitB
  | merge
  | unpack
  | pack (k : ℕ)
  | zdrop
  | group (k : ℕ)
  | ungroup (k : ℕ) (b0 : List Sym)
  | rot (j : ℕ)
  | rotB (j : ℕ)
  | zins (b : List Sym)

def rwLocal : RW → List Seg → Option (List Seg)
  | .splitF, s :: r =>
    if 1 ≤ s.e.c then some (⟨s.b, Lin.const 1⟩ :: ⟨s.b, s.e.dec⟩ :: r) else none
  | .splitB, s :: r =>
    if 1 ≤ s.e.c then some (⟨s.b, s.e.dec⟩ :: ⟨s.b, Lin.const 1⟩ :: r) else none
  | .merge, s1 :: s2 :: r =>
    if s1.b == s2.b then some (⟨s1.b, s1.e.add s2.e⟩ :: r) else none
  | .unpack, s :: r => if s.e.isConst 1 then some (singles s.b ++ r) else none
  | .pack k, A => (takeSingles k A).map (fun p => ⟨p.1, Lin.const 1⟩ :: p.2)
  | .zdrop, s :: r => if s.e.isConst 0 then some r else none
  | .group k, s :: r => (s.e.div k).map (fun e' => ⟨s.b ^ k, e'⟩ :: r)
  | .ungroup k b0, s :: r => if s.b == b0 ^ k then some (⟨b0, s.e.scale k⟩ :: r) else none
  | .rot j, s1 :: s2 :: r =>
    if s2.b == s1.b.take j && s2.e.isConst 1 then
      some (s2 :: ⟨s1.b.drop j ++ s1.b.take j, s1.e⟩ :: r) else none
  | .rotB j, s1 :: s2 :: r =>
    if s1.e.isConst 1 && s1.b.length == j && s2.b.drop (s2.b.length - j) == s1.b then
      some (⟨s1.b ++ s2.b.take (s2.b.length - j), s2.e⟩ :: s1 :: r) else none
  | .zins b, A => some (⟨b, Lin.const 0⟩ :: A)
  | _, _ => none

theorem rwLocal_sound (v : ℕ → ℕ) (rw : RW) (A A' : List Seg) (h : rwLocal rw A = some A')
    (t : ListBlank Sym) : hden v A t = hden v A' t := by
  cases rw with
  | splitF =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.eval_const, lpow_one]
        rw [Lin.eval_dec s.e hc v, lpow_succ, lb_app_app]
      · simp at h
  | splitB =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.eval_const, lpow_one]
        rw [Lin.eval_dec s.e hc v, lpow_succ', lb_app_app]
      · simp at h
  | merge =>
    rcases A with _ | ⟨s1, _ | ⟨s2, r⟩⟩
    · simp [rwLocal] at h
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hb
        simp only [beq_iff_eq] at hb
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.eval_add, lpow_add, lb_app_app, hb]
      · simp at h
  | unpack =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        rw [den_singles]
        simp only [hden, Lin.isConst_eval s.e 1 hc v, lpow_one]
      · simp at h
  | pack k =>
    simp only [rwLocal] at h
    cases hk : takeSingles k A with
    | none => simp [hk] at h
    | some p =>
      simp only [hk, Option.map_some, Option.some.injEq] at h; subst h
      rw [takeSingles_sound v k A p.1 p.2 hk t]
      simp only [hden, Lin.eval_const, lpow_one]
  | zdrop =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.isConst_eval s.e 0 hc v, lpow_zero, lb_app_nil]
      · simp at h
  | group k =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      cases hd : s.e.div k with
      | none => simp [hd] at h
      | some e' =>
        simp only [hd, Option.map_some, Option.some.injEq] at h; subst h
        simp only [hden, Lin.div_sound k s.e e' hd v, lpow_mul]
  | ungroup k b0 =>
    rcases A with _ | ⟨s, r⟩
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hb
        simp only [beq_iff_eq] at hb
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, hb, lpow_mul, Lin.eval_scale]
      · simp at h
  | rot j =>
    rcases A with _ | ⟨s1, _ | ⟨s2, r⟩⟩
    · simp [rwLocal] at h
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.isConst_eval s2.e 1 hc.2 v, lpow_one, hc.1]
        rw [← lb_app_app, ← lb_app_app]
        have key := lpow_rot (List.take j s1.b) (List.drop j s1.b) (s1.e.eval v)
        rw [List.take_append_drop] at key
        rw [key]
      · simp at h
  | rotB j =>
    rcases A with _ | ⟨s1, _ | ⟨s2, r⟩⟩
    · simp [rwLocal] at h
    · simp [rwLocal] at h
    · simp only [rwLocal] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        simp only [Option.some.injEq] at h; subst h
        simp only [hden, Lin.isConst_eval s1.e 1 hc.1.1 v, lpow_one]
        rw [← lb_app_app, ← lb_app_app]
        have hb : s2.b = s2.b.take (s2.b.length - j) ++ s1.b := by
          conv_lhs => rw [← List.take_append_drop (s2.b.length - j) s2.b]
          rw [hc.2]
        rw [lpow_rot, ← hb]
      · simp at h
  | zins b =>
    simp only [rwLocal, Option.some.injEq] at h; subst h
    simp only [hden, Lin.eval_const, lpow_zero, lb_app_nil]

def rwAt (rw : RW) : ℕ → List Seg → Option (List Seg)
  | 0, A => rwLocal rw A
  | p + 1, s :: A => (rwAt rw p A).map (s :: ·)
  | _ + 1, [] => none

theorem rwAt_sound (v : ℕ → ℕ) (rw : RW) : ∀ (p : ℕ) (A A' : List Seg), rwAt rw p A = some A' →
    ∀ t, hden v A t = hden v A' t
  | 0, A, A', h, t => rwLocal_sound v rw A A' h t
  | p + 1, [], A', h, t => by simp [rwAt] at h
  | p + 1, s :: A, A', h, t => by
    simp only [rwAt] at h
    cases hp : rwAt rw p A with
    | none => simp [hp] at h
    | some B =>
      simp only [hp, Option.map_some, Option.some.injEq] at h; subst h
      simp only [hden, rwAt_sound v rw p A B hp t]

def dropTail (A : List Seg) : Option (List Seg) :=
  match A.getLast? with
  | some s => if s.b.all (· == 0) then some A.dropLast else none
  | none => none

theorem dropTail_sound (v : ℕ → ℕ) (A A' : List Seg) (h : dropTail A = some A') :
    hden v A default = hden v A' default := by
  unfold dropTail at h
  cases hl : A.getLast? with
  | none => simp [hl] at h
  | some s =>
    simp only [hl] at h
    split at h
    · rename_i hz
      simp only [Option.some.injEq] at h; subst h
      have hA : A = A.dropLast ++ [s] := by
        rw [List.getLast?_eq_some_iff] at hl
        obtain ⟨ys, hys⟩ := hl
        subst hys; simp
      conv_lhs => rw [hA]
      rw [den_append]
      congr 1
      simp only [hden]
      apply lb_zeros_default
      intro x hx
      have := List.all_eq_true.mp hz x hx
      simpa using this
    · simp at h

-- ---------------------------------------------------------------------------
-- 6.6 Symbolic configurations, concrete steps and block shifts
-- ---------------------------------------------------------------------------

structure SC where
  q : St
  dr : Bool
  L : List Seg
  R : List Seg

/-- `dr = true`: head reads the first cell of `R` (`L q> R`);
    `dr = false`: head reads the first cell of `L` (`L <q R`). -/
def cfgOf (q : St) (dr : Bool) (Lt Rt : ListBlank Sym) : Cfg Sym St :=
  if dr then ⟨some q, ⟨Rt.head, Lt, Rt.tail⟩⟩ else ⟨some q, ⟨Lt.head, Lt.tail, Rt⟩⟩

def SC.den (c : SC) (v : ℕ → ℕ) (tl tr : ListBlank Sym) : Cfg Sym St :=
  cfgOf c.q c.dr (hden v c.L tl) (hden v c.R tr)

def SC.subst (i : ℕ) (f : Lin) (c : SC) : SC :=
  ⟨c.q, c.dr, sideSubst i f c.L, sideSubst i f c.R⟩

def SC.substAll (σ : List Lin) (c : SC) : SC :=
  ⟨c.q, c.dr, sideSubstAll σ c.L, sideSubstAll σ c.R⟩

theorem SC.den_subst (c : SC) (i : ℕ) (f : Lin) (v : ℕ → ℕ) (tl tr : ListBlank Sym) :
    (c.subst i f).den v tl tr = c.den (Function.update v i (f.eval v)) tl tr := by
  simp only [SC.subst, SC.den, Cert.den_subst]

theorem SC.den_substAll (c : SC) (σ : List Lin) (v : ℕ → ℕ) (tl tr : ListBlank Sym) :
    (c.substAll σ).den v tl tr = c.den (sem σ v) tl tr := by
  simp only [SC.substAll, SC.den, Cert.den_substAll]

def SC.beq (a b : SC) : Bool := a.q == b.q && a.dr == b.dr && sideEq a.L b.L && sideEq a.R b.R

theorem SC.beq_sound (a b : SC) (h : a.beq b = true) (v : ℕ → ℕ) (tl tr : ListBlank Sym) :
    a.den v tl tr = b.den v tl tr := by
  simp only [SC.beq, Bool.and_eq_true, beq_iff_eq] at h
  simp only [SC.den, h.1.1.1, h.1.1.2, sideEq_sound _ _ h.1.2 v tl, sideEq_sound _ _ h.2 v tr]

def popHead (dflt : Bool) : List Seg → Option (Sym × List Seg)
  | [] => if dflt then some (0, []) else none
  | s :: r =>
    match s.b with
    | [x] => if s.e.isConst 1 then some (x, r) else none
    | _ => none

theorem popHead_sound (dflt : Bool) (A : List Seg) (x : Sym) (r : List Seg)
    (h : popHead dflt A = some (x, r)) (v : ℕ → ℕ) (t : ListBlank Sym)
    (ht : dflt = true → t = default) : hden v A t = ListBlank.cons x (hden v r t) := by
  rcases A with _ | ⟨⟨b, e⟩, A⟩
  · simp only [popHead] at h
    split at h
    · rename_i hd
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      simp only [hden, ht hd, lb_cons_zero_default]
    · simp at h
  · rcases b with _ | ⟨y, _ | ⟨z, b⟩⟩
    · simp [popHead] at h
    · simp only [popHead] at h
      split at h
      · rename_i he
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, ← h.2]
        simp only [hden, Lin.isConst_eval e 1 he v, lpow_one, lb_app_cons, lb_app_nil]
      · simp at h
    · simp [popHead] at h

def symStep (M : TM) (dflt : Bool) (c : SC) : Option SC :=
  if c.dr then
    match popHead dflt c.R with
    | some (x, r) =>
      match M c.q x with
      | some (some q', Stmt.write w Dir.right) => some ⟨q', true, ⟨[w], Lin.const 1⟩ :: c.L, r⟩
      | some (some q', Stmt.write w Dir.left) => some ⟨q', false, c.L, ⟨[w], Lin.const 1⟩ :: r⟩
      | _ => none
    | none => none
  else
    match popHead dflt c.L with
    | some (x, l) =>
      match M c.q x with
      | some (some q', Stmt.write w Dir.right) => some ⟨q', true, ⟨[w], Lin.const 1⟩ :: l, c.R⟩
      | some (some q', Stmt.write w Dir.left) => some ⟨q', false, l, ⟨[w], Lin.const 1⟩ :: c.R⟩
      | _ => none
    | none => none

theorem symStep_sound (M : TM) (dflt : Bool) (c c' : SC) (h : symStep M dflt c = some c')
    (v : ℕ → ℕ) (tl tr : ListBlank Sym) (ht : dflt = true → tl = default ∧ tr = default) :
    step M (c.den v tl tr) = some (c'.den v tl tr) := by
  rcases c with ⟨q, dr, L, R⟩
  cases dr with
  | true =>
    simp only [symStep, ite_true] at h
    cases hp : popHead dflt R with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨x, r⟩
      have hd := popHead_sound dflt R x r hp v tr (fun hd => (ht hd).2)
      simp only [hp] at h
      cases hM : M q x with
      | none => simp [hM] at h
      | some o =>
        rcases o with ⟨_ | q', ⟨w, d⟩⟩
        · simp [hM] at h
        · cases d <;> simp only [hM, Option.some.injEq] at h <;> subst h <;>
            simp [SC.den, cfgOf, step, hd, hM, den_single, Tape.write, Tape.move]
  | false =>
    simp only [symStep, Bool.false_eq_true, ite_false] at h
    cases hp : popHead dflt L with
    | none => simp [hp] at h
    | some p =>
      rcases p with ⟨x, l⟩
      have hd := popHead_sound dflt L x l hp v tl (fun hd => (ht hd).1)
      simp only [hp] at h
      cases hM : M q x with
      | none => simp [hM] at h
      | some o =>
        rcases o with ⟨_ | q', ⟨w, d⟩⟩
        · simp [hM] at h
        · cases d <;> simp only [hM, Option.some.injEq] at h <;> subst h <;>
            simp [SC.den, cfgOf, step, hd, hM, den_single, Tape.write, Tape.move]

def isHalt (M : TM) (dflt : Bool) (c : SC) : Bool :=
  match popHead dflt (if c.dr then c.R else c.L) with
  | some (x, _) => (M c.q x).isNone
  | none => false

theorem isHalt_sound (M : TM) (dflt : Bool) (c : SC) (h : isHalt M dflt c = true)
    (v : ℕ → ℕ) (tl tr : ListBlank Sym) (ht : dflt = true → tl = default ∧ tr = default) :
    (step M (c.den v tl tr)).isNone = true := by
  rcases c with ⟨q, dr, L, R⟩
  unfold isHalt at h
  cases hp : popHead dflt (if dr then R else L) with
  | none => simp [hp] at h
  | some p =>
    rcases p with ⟨x, r⟩
    simp only [hp, Option.isNone_iff_eq_none] at h
    cases dr with
    | true =>
      have hd := popHead_sound dflt R x r (by simpa using hp) v tr (fun hd => (ht hd).2)
      simp [SC.den, cfgOf, step, hd, h]
    | false =>
      have hd := popHead_sound dflt L x r (by simpa using hp) v tl (fun hd => (ht hd).1)
      simp [SC.den, cfgOf, step, hd, h]

-- local simulation inside one block, head entering from the left (moving right)
def runR (M : TM) : ℕ → St → List Sym → List Sym → Option (St × List Sym)
  | _, q, lw, [] => some (q, lw)
  | 0, _, _, _ :: _ => none
  | f + 1, q, lw, s :: rw =>
    match M q s with
    | some (some q', Stmt.write w Dir.right) => runR M f q' (w :: lw) rw
    | some (some q', Stmt.write w Dir.left) =>
      match lw with
      | [] => none
      | x :: lw' => runR M f q' lw' (x :: w :: rw)
    | _ => none

theorem runR_sound (M : TM) : ∀ (f : ℕ) (q : St) (lw rw : List Sym) (q' : St) (lw' : List Sym),
    runR M f q lw rw = some (q', lw') → ∀ (L R : ListBlank Sym),
    RStar M (cfgOf q true (ListBlank.append lw L) (ListBlank.append rw R))
      (cfgOf q' true (ListBlank.append lw' L) R)
  | f, q, lw, [], q', lw', h, L, R => by
    have h' : q = q' ∧ lw = lw' := by cases f <;> simpa [runR] using h
    rw [← h'.1, ← h'.2]; exact rstar_refl M _
  | 0, q, lw, s :: rw, q', lw', h, L, R => by simp [runR] at h
  | f + 1, q, lw, s :: rw, q', lw', h, L, R => by
    simp only [runR] at h
    cases hM : M q s with
    | none => simp [hM] at h
    | some o =>
      rcases o with ⟨_ | q2, ⟨w, d⟩⟩
      · simp [hM] at h
      · cases d with
        | right =>
          simp only [hM] at h
          refine rstar_trans ⟨1, ms_one M _ _ ?_⟩ (runR_sound M f q2 (w :: lw) rw q' lw' h L R)
          simp [cfgOf, step, hM, Tape.write, Tape.move]
        | left =>
          simp only [hM] at h
          rcases lw with _ | ⟨x, lw2⟩
          · simp at h
          · simp only at h
            refine rstar_trans ⟨1,
              ms_one M _ _ ?_⟩ (runR_sound M f q2 lw2 (x :: w :: rw) q' lw' h L R)
            simp [cfgOf, step, hM, Tape.write, Tape.move]

-- local simulation inside one block, head entering from the right (moving left)
def runL (M : TM) : ℕ → St → List Sym → List Sym → Option (St × List Sym)
  | _, q, rw, [] => some (q, rw)
  | 0, _, _, _ :: _ => none
  | f + 1, q, rw, s :: lw =>
    match M q s with
    | some (some q', Stmt.write w Dir.left) => runL M f q' (w :: rw) lw
    | some (some q', Stmt.write w Dir.right) =>
      match rw with
      | [] => none
      | x :: rw' => runL M f q' rw' (x :: w :: lw)
    | _ => none

theorem runL_sound (M : TM) : ∀ (f : ℕ) (q : St) (rw lw : List Sym) (q' : St) (rw' : List Sym),
    runL M f q rw lw = some (q', rw') → ∀ (L R : ListBlank Sym),
    RStar M (cfgOf q false (ListBlank.append lw L) (ListBlank.append rw R))
      (cfgOf q' false L (ListBlank.append rw' R))
  | f, q, rw, [], q', rw', h, L, R => by
    have h' : q = q' ∧ rw = rw' := by cases f <;> simpa [runL] using h
    rw [← h'.1, ← h'.2]; exact rstar_refl M _
  | 0, q, rw, s :: lw, q', rw', h, L, R => by simp [runL] at h
  | f + 1, q, rw, s :: lw, q', rw', h, L, R => by
    simp only [runL] at h
    cases hM : M q s with
    | none => simp [hM] at h
    | some o =>
      rcases o with ⟨_ | q2, ⟨w, d⟩⟩
      · simp [hM] at h
      · cases d with
        | left =>
          simp only [hM] at h
          refine rstar_trans ⟨1, ms_one M _ _ ?_⟩ (runL_sound M f q2 (w :: rw) lw q' rw' h L R)
          simp [cfgOf, step, hM, Tape.write, Tape.move]
        | right =>
          simp only [hM] at h
          rcases rw with _ | ⟨x, rw2⟩
          · simp at h
          · simp only at h
            refine rstar_trans ⟨1,
              ms_one M _ _ ?_⟩ (runL_sound M f q2 rw2 (x :: w :: lw) q' rw' h L R)
            simp [cfgOf, step, hM, Tape.write, Tape.move]

theorem shiftR_sound (M : TM) (f : ℕ) (q : St) (b lw' : List Sym)
    (h : runR M f q [] b = some (q, lw')) :
    ∀ (n : ℕ) (L R : ListBlank Sym),
    RStar M (cfgOf q true L (ListBlank.append (b ^ n) R)) (cfgOf q true (ListBlank.append (lw' ^ n)
      L) R)
  | 0, L, R => rstar_refl M _
  | n + 1, L, R => by
    have h1 := runR_sound M f q [] b q lw' h L (ListBlank.append (b ^ n) R)
    have h2 := shiftR_sound M f q b lw' h n (ListBlank.append lw' L) R
    rw [lpow_succ, lb_app_app]
    rw [lpow_succ', lb_app_app]
    exact rstar_trans h1 h2

theorem shiftL_sound (M : TM) (f : ℕ) (q : St) (b rw' : List Sym)
    (h : runL M f q [] b = some (q, rw')) :
    ∀ (n : ℕ) (L R : ListBlank Sym),
    RStar M (cfgOf q false (ListBlank.append (b ^ n) L) R) (cfgOf q false L (ListBlank.append (rw'
      ^ n) R))
  | 0, L, R => rstar_refl M _
  | n + 1, L, R => by
    have h1 := runL_sound M f q [] b q rw' h (ListBlank.append (b ^ n) L) R
    have h2 := shiftL_sound M f q b rw' h n L (ListBlank.append rw' R)
    rw [lpow_succ, lb_app_app]
    rw [lpow_succ', lb_app_app]
    exact rstar_trans h1 h2

def shiftFuel : ℕ := 512

def shiftOp (M : TM) (c : SC) : Option SC :=
  if c.dr then
    match c.R with
    | s :: r =>
      match runR M shiftFuel c.q [] s.b with
      | some (q', lw') => if q' == c.q then some ⟨c.q, true, ⟨lw', s.e⟩ :: c.L, r⟩ else none
      | none => none
    | [] => none
  else
    match c.L with
    | s :: l =>
      match runL M shiftFuel c.q [] s.b with
      | some (q', rw') => if q' == c.q then some ⟨c.q, false, l, ⟨rw', s.e⟩ :: c.R⟩ else none
      | none => none
    | [] => none

theorem shiftOp_sound (M : TM) (c c' : SC) (h : shiftOp M c = some c') (v : ℕ → ℕ)
    (tl tr : ListBlank Sym) : RStar M (c.den v tl tr) (c'.den v tl tr) := by
  rcases c with ⟨q, dr, L, R⟩
  cases dr with
  | true =>
    simp only [shiftOp, ite_true] at h
    rcases R with _ | ⟨s, r⟩
    · simp at h
    · simp only at h
      cases hr : runR M shiftFuel q [] s.b with
      | none => simp [hr] at h
      | some p =>
        rcases p with ⟨q', lw'⟩
        simp only [hr] at h
        split at h
        · rename_i hq
          simp only [beq_iff_eq] at hq
          subst hq
          simp only [Option.some.injEq] at h; subst h
          exact shiftR_sound M shiftFuel q' s.b lw' hr (s.e.eval v) (hden v L tl) (hden v r tr)
        · simp at h
  | false =>
    simp only [shiftOp, Bool.false_eq_true, ite_false] at h
    rcases L with _ | ⟨s, l⟩
    · simp at h
    · simp only at h
      cases hr : runL M shiftFuel q [] s.b with
      | none => simp [hr] at h
      | some p =>
        rcases p with ⟨q', rw'⟩
        simp only [hr] at h
        split at h
        · rename_i hq
          simp only [beq_iff_eq] at hq
          subst hq
          simp only [Option.some.injEq] at h; subst h
          exact shiftL_sound M shiftFuel q' s.b rw' hr (s.e.eval v) (hden v l tl) (hden v R tr)
        · simp at h

-- ---------------------------------------------------------------------------
-- 6.7 Macro rules (proved by sub-certificates) and their application
-- ---------------------------------------------------------------------------

structure Rule where
  lhs : SC
  rhs : SC
  plus : Bool
  dflt : Bool

/-- A rule is valid if, for all parameter values and all (arbitrary) tape tails,
    the left-hand side reaches the right-hand side (in `≥ 1` steps if `plus`). -/
def RuleOK (M : TM) (r : Rule) : Prop :=
  ∀ v tl tr,
    (r.dflt = true → tl = default
    ∧ tr = default) → RStar M (r.lhs.den v tl tr) (r.rhs.den v tl tr) ∧
    (r.plus = true → RPlus M (r.lhs.den v tl tr) (r.rhs.den v tl tr))

def matchPre (σ : List Lin) : List Seg → List Seg → Option (List Seg)
  | [], A => some A
  | p :: P, a :: A => if p.b == a.b && (p.e.substAll σ).beq a.e then matchPre σ P A else none
  | _ :: _, [] => none

theorem matchPre_sound (σ : List Lin) : ∀ (P A Rst : List Seg), matchPre σ P A = some Rst →
    ∀ v t, hden v A t = hden (sem σ v) P (hden v Rst t)
  | [], A, Rst, h, v, t => by simp only [matchPre, Option.some.injEq] at h; subst h; rfl
  | p :: P, [], Rst, h, v, t => by simp [matchPre] at h
  | p :: P, a :: A, Rst, h, v, t => by
    simp only [matchPre] at h
    split at h
    · rename_i hc
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      have he := Lin.beq_sound _ _ hc.2 v
      rw [Lin.eval_substAll] at he
      simp only [hden, hc.1, he, matchPre_sound σ P A Rst h v t]
    · simp at h

def applyRule (r : Rule) (σ : List Lin) (c : SC) : Option SC :=
  if r.lhs.q == c.q && r.lhs.dr == c.dr then
    match matchPre σ r.lhs.L c.L, matchPre σ r.lhs.R c.R with
    | some rl, some rr =>
      if !r.dflt || (rl.isEmpty && rr.isEmpty) then
        some ⟨r.rhs.q, r.rhs.dr, sideSubstAll σ r.rhs.L ++ rl, sideSubstAll σ r.rhs.R ++ rr⟩
      else none
    | _, _ => none
  else none

theorem applyRule_sound (M : TM) (r : Rule) (hr : RuleOK M r) (σ : List Lin) (c c' : SC)
    (h : applyRule r σ c = some c') (v : ℕ → ℕ) (tl tr : ListBlank Sym)
    (ht : r.dflt = true → tl = default ∧ tr = default) :
    RStar M (c.den v tl tr) (c'.den v tl tr) ∧
      (r.plus = true → RPlus M (c.den v tl tr) (c'.den v tl tr)) := by
  simp only [applyRule] at h
  split at h
  · rename_i hq
    simp only [Bool.and_eq_true, beq_iff_eq] at hq
    cases hl : matchPre σ r.lhs.L c.L with
    | none => simp [hl] at h
    | some rl =>
      cases hrr : matchPre σ r.lhs.R c.R with
      | none => simp [hl, hrr] at h
      | some rr =>
        simp only [hl, hrr] at h
        split at h
        · rename_i hdf
          simp only [Option.some.injEq] at h
          subst h
          have hrest : r.dflt = true → hden v rl tl = default ∧ hden v rr tr = default := by
            intro hd
            simp only [hd, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.isEmpty_iff] at hdf
            rw [hdf.1, hdf.2]; exact ht hd
          have e1 : c.den v tl tr = r.lhs.den (sem σ v) (hden v rl tl) (hden v rr tr) := by
            simp only [SC.den, ← hq.1, ← hq.2, matchPre_sound σ _ _ _ hl v tl,
              matchPre_sound σ _ _ _ hrr v tr]
          have e2 : (⟨r.rhs.q, r.rhs.dr, sideSubstAll σ r.rhs.L ++ rl,
            sideSubstAll σ r.rhs.R ++ rr⟩ : SC).den
              v tl tr = r.rhs.den (sem σ v) (hden v rl tl) (hden v rr tr) := by
            simp only [SC.den, den_append, den_substAll]
          rw [e1, e2]
          exact hr _ _ _ hrest
        · simp at h
  · simp at h

-- ---------------------------------------------------------------------------
-- 6.8 Hub patterns
-- ---------------------------------------------------------------------------

def segsExpr : List Seg → TapeExpr Sym
  | [] => .default
  | s :: r =>
    match s.e.asVar with
    | some k => .rep s.b k (segsExpr r)
    | none => s.b.foldr TapeExpr.sym (segsExpr r)

def segsOK : List Seg → Bool
  | [] => true
  | s :: r => (s.e.asVar.isSome || s.e.isConst 1) && segsOK r

theorem evalTapeExpr_foldr (b : List Sym) (rest : TapeExpr Sym) (v : ℕ → ℕ) :
    evalTapeExpr (b.foldr TapeExpr.sym rest) v = ListBlank.append b (evalTapeExpr rest v) := by
  induction b with
  | nil => rfl
  | cons x b ih => simp only [List.foldr_cons, evalTapeExpr, ih, lb_app_cons]

theorem segsExpr_eval : ∀ (A : List Seg), segsOK A = true → ∀ v,
    evalTapeExpr (segsExpr A) v = hden v A default
  | [], _, v => rfl
  | s :: A, h, v => by
    simp only [segsOK, Bool.and_eq_true, Bool.or_eq_true] at h
    simp only [segsExpr]
    cases hv : s.e.asVar with
    | some k =>
      simp only [evalTapeExpr, hden, Lin.asVar_sound s.e k hv v, segsExpr_eval A h.2 v]
    | none =>
      have hc : s.e.isConst 1 = true := by
        rcases h.1 with h1 | h1
        · simp [hv] at h1
        · exact h1
      simp only [evalTapeExpr_foldr, hden, Lin.isConst_eval s.e 1 hc v, lpow_one,
        segsExpr_eval A h.2 v]

def hubOK (h : SC) : Bool := h.dr && segsOK h.L && segsOK h.R

def toPat (h : SC) : TapePattern Sym St := ⟨segsExpr h.L, some h.q, segsExpr h.R⟩

def hubsPS (hubs : List SC) : TapePatternSet Sym St := hubs.map (fun h => (toPat h, VarCond.true))

theorem toPat_eval (h : SC) (hok : hubOK h = true) (v : ℕ → ℕ) :
    evalTapePattern (toPat h) v = h.den v default default := by
  simp only [hubOK, Bool.and_eq_true] at hok
  rcases h with ⟨q, dr, L, R⟩
  simp only at hok
  rw [hok.1.1]
  simp only [evalTapePattern, toPat, SC.den, cfgOf, ite_true, segsExpr_eval L hok.1.2 v,
    segsExpr_eval R hok.2 v]

theorem in_hubsPS (hubs : List SC) (hh : ∀ h ∈ hubs, hubOK h = true) (h : SC) (hm : h ∈ hubs)
    (v : ℕ → ℕ) : IsInPatternSet (hubsPS hubs) (h.den v default default) :=
  ⟨(toPat h, VarCond.true), List.mem_map.mpr ⟨h, hm, rfl⟩, v, (toPat_eval h (hh h hm) v).symm,
    trivial⟩

-- ---------------------------------------------------------------------------
-- 6.9 Goals, instructions and the checker
-- ---------------------------------------------------------------------------

inductive Tgt
  | hubs
  | ps
  | cfg (c : SC)

def Tgt.subst (i : ℕ) (f : Lin) : Tgt → Tgt
  | .cfg c => .cfg (c.subst i f)
  | t => t

def Tgt.isHub : Tgt → Bool
  | .cfg _ => false
  | _ => true

structure Goal where
  cur : SC
  np : Bool
  tgt : Tgt

inductive Ins
  | step
  | shift
  | rw (left : Bool) (p : ℕ) (r : RW)
  | dropTail (left : Bool)
  | app (j : ℕ) (σ : List Lin)
  | splitZ (i : ℕ)
  | splitM (i m : ℕ)
  | hub (j : ℕ) (σ : List Lin)
  | halt
  | done

def Goal.subst (i : ℕ) (f : Lin) (g : Goal) : Goal := ⟨g.cur.subst i f, g.np, g.tgt.subst i f⟩

def modBranch (i m r : ℕ) : Lin := (Lin.const r).add ((Lin.var i).scale m)

def exec (M : TM) (hubs : List SC) (rules : List Rule) (dflt : Bool) (g : Goal) :
    Ins → Option (List Goal)
  | .step => (symStep M dflt g.cur).map (fun c' => [⟨c', false, g.tgt⟩])
  | .shift => (shiftOp M g.cur).map (fun c' => [⟨c', g.np, g.tgt⟩])
  | .rw left p r =>
    if left then (rwAt r p g.cur.L).map (fun L' => [⟨⟨g.cur.q, g.cur.dr, L', g.cur.R⟩, g.np,
      g.tgt⟩])
    else (rwAt r p g.cur.R).map (fun R' => [⟨⟨g.cur.q, g.cur.dr, g.cur.L, R'⟩, g.np, g.tgt⟩])
  | .dropTail left =>
    if dflt then
      if left then (dropTail g.cur.L).map (fun L' => [⟨⟨g.cur.q, g.cur.dr, L', g.cur.R⟩, g.np,
        g.tgt⟩])
      else (dropTail g.cur.R).map (fun R' => [⟨⟨g.cur.q, g.cur.dr, g.cur.L, R'⟩, g.np, g.tgt⟩])
    else none
  | .app j σ =>
    match rules[j]? with
    | some r => if !r.dflt || dflt then
        (applyRule r σ g.cur).map (fun c' => [⟨c', g.np && !r.plus, g.tgt⟩]) else none
    | none => none
  | .splitZ i => some [g.subst i (Lin.const 0), g.subst i ((Lin.var i).add (Lin.const 1))]
  | .splitM i m => if 1 ≤ m then some ((List.range m).map (fun r => g.subst i (modBranch i m r)))
    else none
  | .hub j σ =>
    match hubs[j]? with
    | some h => if dflt && !g.np && g.tgt.isHub && (h.substAll σ).beq g.cur then some [] else none
    | none => none
  | .halt =>
    match g.tgt with
    | .hubs => if !g.np && isHalt M dflt g.cur then some [] else none
    | _ => none
  | .done =>
    match g.tgt with
    | .cfg d => if !g.np && g.cur.beq d then some [] else none
    | _ => none

def run (M : TM) (hubs : List SC) (rules : List Rule) (dflt : Bool) :
    List Ins → List Goal → Bool
  | [], gs => gs.isEmpty
  | _ :: _, [] => false
  | i :: is, g :: gs =>
    match exec M hubs rules dflt g i with
    | some new => run M hubs rules dflt is (new ++ gs)
    | none => false

def Final (M : TM) (ps : TapePatternSet Sym St) (t : Tgt) (v : ℕ → ℕ) (tl tr : ListBlank Sym)
    (c' : Cfg Sym St) : Prop :=
  match t with
  | .hubs => IsInPatternSet ps c' ∨ (step M c').isNone
  | .ps => IsInPatternSet ps c'
  | .cfg d => c' = d.den v tl tr

def Good (M : TM) (ps : TapePatternSet Sym St) (dflt : Bool) (g : Goal) : Prop :=
  ∀ v tl tr, (dflt = true → tl = default ∧ tr = default) →
    ∃ c', RStar M (g.cur.den v tl tr) c' ∧ (g.np = true → RPlus M (g.cur.den v tl tr) c') ∧
      Final M ps g.tgt v tl tr c'

theorem Final_subst (M : TM) (ps : TapePatternSet Sym St) (t : Tgt) (i : ℕ) (f : Lin)
    (v : ℕ → ℕ) (tl tr : ListBlank Sym) (c' : Cfg Sym St) :
    Final M ps (t.subst i f) v tl tr c' ↔ Final M ps t (Function.update v i (f.eval v)) tl tr c' :=
      by
  cases t with
  | hubs => exact Iff.rfl
  | ps => exact Iff.rfl
  | cfg d => simp only [Tgt.subst, Final, SC.den_subst]

/-- Instantiating a split branch: if the substituted goal is good, the original goal holds at
    every valuation `v` with `v i = f.eval v'` for `v' = update v i k`. -/
theorem Good_subst_at (M : TM) (ps : TapePatternSet Sym St) (dflt : Bool) (g : Goal) (i : ℕ)
    (f : Lin) (hg : Good M ps dflt (g.subst i f)) (v : ℕ → ℕ) (k : ℕ)
    (hk : f.eval (Function.update v i k) = v i) (tl tr : ListBlank Sym)
    (ht : dflt = true → tl = default ∧ tr = default) :
    ∃ c', RStar M (g.cur.den v tl tr) c' ∧ (g.np = true → RPlus M (g.cur.den v tl tr) c') ∧
      Final M ps g.tgt v tl tr c' := by
  obtain ⟨c', h1, h2, h3⟩ := hg (Function.update v i k) tl tr ht
  have hv : Function.update (Function.update v i k) i (f.eval (Function.update v i k)) = v := by
    rw [hk, Function.update_idem, Function.update_eq_self]
  simp only [Goal.subst, SC.den_subst, hv] at h1 h2 h3
  rw [Final_subst, hv] at h3
  exact ⟨c', h1, h2, h3⟩

theorem Good_of_star (M : TM) (ps : TapePatternSet Sym St) (dflt : Bool) (g g' : Goal)
    (htg : g'.tgt = g.tgt) (hnp : g'.np = g.np)
    (hs : ∀ v tl tr, (dflt = true → tl = default ∧ tr = default) →
      RStar M (g.cur.den v tl tr) (g'.cur.den v tl tr))
    (hg : Good M ps dflt g') : Good M ps dflt g := by
  intro v tl tr ht
  obtain ⟨c', h1, h2, h3⟩ := hg v tl tr ht
  refine ⟨c', rstar_trans (hs v tl tr ht) h1, fun hn => ?_, htg ▸ h3⟩
  exact rstar_trans_plus (hs v tl tr ht) (h2 (hnp ▸ hn))

theorem Good_of_plus (M : TM) (ps : TapePatternSet Sym St) (dflt : Bool) (g g' : Goal)
    (htg : g'.tgt = g.tgt)
    (hs : ∀ v tl tr, (dflt = true → tl = default ∧ tr = default) →
      RPlus M (g.cur.den v tl tr) (g'.cur.den v tl tr))
    (hg : Good M ps dflt g') : Good M ps dflt g := by
  intro v tl tr ht
  obtain ⟨c', h1, h2, h3⟩ := hg v tl tr ht
  have hp := rplus_trans_star (hs v tl tr ht) h1
  exact ⟨c', rplus_rstar hp, fun _ => hp, htg ▸ h3⟩

theorem exec_sound (M : TM) (hubs : List SC) (hh : ∀ h ∈ hubs, hubOK h = true)
    (rules : List Rule) (hr : ∀ r ∈ rules, RuleOK M r) (dflt : Bool) (g : Goal) (i : Ins)
    (new : List Goal) (he : exec M hubs rules dflt g i = some new)
    (hn : ∀ g' ∈ new, Good M (hubsPS hubs) dflt g') : Good M (hubsPS hubs) dflt g := by
  cases i with
  | step =>
    simp only [exec] at he
    cases hs : symStep M dflt g.cur with
    | none => simp [hs] at he
    | some c' =>
      simp only [hs, Option.map_some, Option.some.injEq] at he
      subst he
      refine Good_of_plus M _ dflt g ⟨c', false, g.tgt⟩ rfl (fun v tl tr ht => ?_) (hn _ (by simp))
      exact step_rplus (symStep_sound M dflt g.cur c' hs v tl tr ht)
  | shift =>
    simp only [exec] at he
    cases hs : shiftOp M g.cur with
    | none => simp [hs] at he
    | some c' =>
      simp only [hs, Option.map_some, Option.some.injEq] at he
      subst he
      exact Good_of_star M _ dflt g ⟨c', g.np, g.tgt⟩ rfl rfl
        (fun v tl tr _ => shiftOp_sound M g.cur c' hs v tl tr) (hn _ (by simp))
  | rw left p r =>
    simp only [exec] at he
    cases left with
    | true =>
      simp only [ite_true] at he
      cases hs : rwAt r p g.cur.L with
      | none => simp [hs] at he
      | some L' =>
        simp only [hs, Option.map_some, Option.some.injEq] at he
        subst he
        refine Good_of_star M _ dflt g ⟨⟨g.cur.q, g.cur.dr, L', g.cur.R⟩, g.np, g.tgt⟩ rfl rfl
          (fun v tl tr _ => ?_) (hn _ (by simp))
        simp only [SC.den, rwAt_sound v r p g.cur.L L' hs tl]
        exact rstar_refl M _
    | false =>
      simp only [Bool.false_eq_true, ite_false] at he
      cases hs : rwAt r p g.cur.R with
      | none => simp [hs] at he
      | some R' =>
        simp only [hs, Option.map_some, Option.some.injEq] at he
        subst he
        refine Good_of_star M _ dflt g ⟨⟨g.cur.q, g.cur.dr, g.cur.L, R'⟩, g.np, g.tgt⟩ rfl rfl
          (fun v tl tr _ => ?_) (hn _ (by simp))
        simp only [SC.den, rwAt_sound v r p g.cur.R R' hs tr]
        exact rstar_refl M _
  | dropTail left =>
    simp only [exec] at he
    cases hd : dflt with
    | false => simp [hd] at he
    | true =>
      simp only [hd, ite_true] at he
      cases left with
      | true =>
        simp only [ite_true] at he
        cases hs : dropTail g.cur.L with
        | none => simp [hs] at he
        | some L' =>
          simp only [hs, Option.map_some, Option.some.injEq] at he
          subst he
          refine Good_of_star M _ true g ⟨⟨g.cur.q, g.cur.dr, L', g.cur.R⟩, g.np, g.tgt⟩ rfl rfl
            (fun v tl tr ht => ?_) (hd ▸ hn _ (by simp))
          obtain ⟨h1, h2⟩ := ht rfl
          subst h1; subst h2
          simp only [SC.den, dropTail_sound v g.cur.L L' hs]
          exact rstar_refl M _
      | false =>
        simp only [Bool.false_eq_true, ite_false] at he
        cases hs : dropTail g.cur.R with
        | none => simp [hs] at he
        | some R' =>
          simp only [hs, Option.map_some, Option.some.injEq] at he
          subst he
          refine Good_of_star M _ true g ⟨⟨g.cur.q, g.cur.dr, g.cur.L, R'⟩, g.np, g.tgt⟩ rfl rfl
            (fun v tl tr ht => ?_) (hd ▸ hn _ (by simp))
          obtain ⟨h1, h2⟩ := ht rfl
          subst h1; subst h2
          simp only [SC.den, dropTail_sound v g.cur.R R' hs]
          exact rstar_refl M _
  | app j σ =>
    simp only [exec] at he
    cases hj : rules[j]? with
    | none => simp [hj] at he
    | some r =>
      simp only [hj] at he
      have hrok : RuleOK M r := hr r (List.mem_of_getElem? hj)
      split at he
      swap
      · simp at he
      rename_i hdf
      have htl : ∀ tl tr : ListBlank Sym, (dflt = true → tl = default ∧ tr = default) →
          (r.dflt = true → tl = default ∧ tr = default) := by
        intro tl tr ht hd
        simp only [hd, Bool.not_true, Bool.false_or] at hdf
        exact ht hdf
      cases ha : applyRule r σ g.cur with
      | none => simp [ha] at he
      | some c' =>
        simp only [ha, Option.map_some, Option.some.injEq] at he
        subst he
        have hg' := hn ⟨c', g.np && !r.plus, g.tgt⟩ (by simp)
        cases hp : r.plus with
        | true =>
          refine Good_of_plus M _ dflt g ⟨c', g.np && !r.plus, g.tgt⟩ rfl (fun v tl tr ht => ?_) hg'
          exact (applyRule_sound M r hrok σ g.cur c' ha v tl tr (htl tl tr ht)).2 hp
        | false =>
          refine Good_of_star M _ dflt g ⟨c', g.np && !r.plus, g.tgt⟩ rfl (by simp [hp])
            (fun v tl tr ht => ?_) hg'
          exact (applyRule_sound M r hrok σ g.cur c' ha v tl tr (htl tl tr ht)).1
  | splitZ i =>
    simp only [exec, Option.some.injEq] at he
    subst he
    intro v tl tr ht
    cases hvi : v i with
    | zero =>
      refine Good_subst_at M _ dflt g i (Lin.const 0) (hn _ (by simp)) v 0 ?_ tl tr ht
      rw [Lin.eval_const, hvi]
    | succ k =>
      refine Good_subst_at M _ dflt g i ((Lin.var i).add (Lin.const 1)) (hn _ (by simp)) v k ?_ tl
        tr ht
      rw [Lin.eval_add, Lin.eval_var, Lin.eval_const, Function.update_self, hvi]
  | splitM i m =>
    simp only [exec] at he
    split at he
    · rename_i hm
      simp only [Option.some.injEq] at he
      subst he
      intro v tl tr ht
      have hmem : g.subst i (modBranch i m (v i % m)) ∈
          (List.range m).map (fun r => g.subst i (modBranch i m r)) :=
        List.mem_map.mpr ⟨v i % m, List.mem_range.mpr (Nat.mod_lt _ (by omega)), rfl⟩
      refine Good_subst_at M _ dflt g i _ (hn _ hmem) v (v i / m) ?_ tl tr ht
      simp only [modBranch, Lin.eval_add, Lin.eval_const, Lin.eval_scale, Lin.eval_var,
        Function.update_self]
      exact Nat.mod_add_div (v i) m
    · simp at he
  | hub j σ =>
    simp only [exec] at he
    cases hj : hubs[j]? with
    | none => simp [hj] at he
    | some h =>
      simp only [hj] at he
      split at he
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        obtain ⟨⟨⟨hd, hnp⟩, ht⟩, hb⟩ := hc
        intro v tl tr htl
        obtain ⟨h1, h2⟩ := htl hd
        subst h1; subst h2
        refine ⟨g.cur.den v default default, rstar_refl M _, fun h => by simp [hnp] at h, ?_⟩
        have hin := in_hubsPS hubs hh h (List.mem_of_getElem? hj) (sem σ v)
        rw [← SC.den_substAll, SC.beq_sound _ _ hb] at hin
        cases htg : g.tgt with
        | hubs => exact Or.inl hin
        | ps => exact hin
        | cfg d => simp [htg, Tgt.isHub] at ht
      · simp at he
  | halt =>
    simp only [exec] at he
    cases htg : g.tgt with
    | hubs =>
      simp only [htg] at he
      split at he
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        intro v tl tr ht
        refine ⟨g.cur.den v tl tr, rstar_refl M _, fun h => by simp [hc.1] at h, ?_⟩
        rw [htg]
        exact Or.inr (isHalt_sound M dflt g.cur hc.2 v tl tr ht)
      · simp at he
    | ps => simp [htg] at he
    | cfg d => simp [htg] at he
  | done =>
    simp only [exec] at he
    cases htg : g.tgt with
    | cfg d =>
      simp only [htg] at he
      split at he
      · rename_i hc
        simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
        intro v tl tr ht
        refine ⟨g.cur.den v tl tr, rstar_refl M _, fun h => by simp [hc.1] at h, ?_⟩
        rw [htg]
        exact SC.beq_sound _ _ hc.2 v tl tr
      · simp at he
    | hubs => simp [htg] at he
    | ps => simp [htg] at he

theorem run_sound (M : TM) (hubs : List SC) (hh : ∀ h ∈ hubs, hubOK h = true)
    (rules : List Rule) (hr : ∀ r ∈ rules, RuleOK M r) (dflt : Bool) :
    ∀ (is : List Ins) (gs : List Goal), run M hubs rules dflt is gs = true →
      ∀ g ∈ gs, Good M (hubsPS hubs) dflt g
  | [], gs, h, g, hg => by
    simp only [run, List.isEmpty_iff] at h; subst h; simp at hg
  | i :: is, [], h, g, hg => by simp at hg
  | i :: is, g0 :: gs, h, g, hg => by
    simp only [run] at h
    cases he : exec M hubs rules dflt g0 i with
    | none => simp [he] at h
    | some new =>
      simp only [he] at h
      have ih := run_sound M hubs hh rules hr dflt is (new ++ gs) h
      rcases List.mem_cons.mp hg with rfl | hg'
      · exact exec_sound M hubs hh rules hr dflt g i new he (fun g' hg' => ih g' (by simp [hg']))
      · exact ih g (by simp [hg'])

-- ---------------------------------------------------------------------------
-- 6.10 Rule definitions: proved rules and iterated (inductive) rules
-- ---------------------------------------------------------------------------

inductive RDef
  | prove (r : Rule) (pf : List Ins)
  | iter (j : ℕ) (S : SC) (k : ℕ) (ds : List ℕ)

/-- `x_i ↦ x_i + d_i` for `i ≠ k`, `x_k ↦ x_k`. -/
def iterL (k : ℕ) (ds : List ℕ) : List Lin :=
  (List.range ds.length).map (fun i => if i == k then Lin.var i else (Lin.var i).add (Lin.const
    (ds.getD i 0)))

/-- `x_i ↦ x_i + d_i * x_k` for `i ≠ k`, `x_k ↦ 0`. -/
def iterR (k : ℕ) (ds : List ℕ) : List Lin :=
  (List.range ds.length).map (fun i => if i == k then Lin.const 0 else (Lin.var i).add ((Lin.var
    k).scale (ds.getD i 0)))

theorem getD_map_range (n : ℕ) (f : ℕ → Lin) (i : ℕ) (d : Lin) :
    ((List.range n).map f).getD i d = if i < n then f i else d := by
  by_cases h : i < n
  · simp [h, List.getD_eq_getElem?_getD]
  · simp [h, List.getD_eq_getElem?_getD]

theorem sem_iterL (k : ℕ) (ds : List ℕ) (v : ℕ → ℕ) (i : ℕ) :
    sem (iterL k ds) v i = if i < ds.length ∧ i ≠ k then v i + ds.getD i 0 else v i := by
  simp only [sem, iterL, getD_map_range]
  by_cases h1 : i < ds.length
  · by_cases h2 : i = k
    · subst h2; simp [h1, Lin.eval_var]
    · simp [h1, h2, Lin.eval_add, Lin.eval_var, Lin.eval_const]
  · simp [h1, Lin.eval_var]

theorem sem_iterR (k : ℕ) (ds : List ℕ) (v : ℕ → ℕ) (i : ℕ) :
    sem (iterR k ds) v i =
      if i < ds.length then (if i = k then 0 else v i + v k * ds.getD i 0) else v i := by
  simp only [sem, iterR, getD_map_range]
  by_cases h1 : i < ds.length
  · by_cases h2 : i = k
    · subst h2; simp [h1, Lin.eval_const]
    · simp [h1, h2, Lin.eval_add, Lin.eval_var, Lin.eval_scale, Nat.mul_comm]
  · simp [h1, Lin.eval_var]

theorem iter_sound (M : TM) (S : SC) (k : ℕ) (ds : List ℕ) (hk : k < ds.length) (r : Rule)
    (hr : RuleOK M r) (hl : r.lhs.beq (S.subst k ((Lin.var k).add (Lin.const 1))) = true)
    (hrr : r.rhs.beq (S.substAll (iterL k ds)) = true) :
    RuleOK M ⟨S, S.substAll (iterR k ds), false, r.dflt⟩ := by
  intro v tl tr htd
  refine ⟨?_, fun h => by simp at h⟩
  simp only [SC.den_substAll]
  -- induction on the counter value
  suffices H : ∀ n (v : ℕ → ℕ), v k = n →
      RStar M (S.den v tl tr) (S.den (sem (iterR k ds) v) tl tr) from H (v k) v rfl
  intro n
  induction n with
  | zero =>
    intro v hv
    have : sem (iterR k ds) v = v := by
      funext i
      rw [sem_iterR]
      by_cases h1 : i < ds.length
      · by_cases h2 : i = k
        · simp [h2, hv]
        · simp [h1, h2, hv]
      · simp [h1]
    rw [this]; exact rstar_refl M _
  | succ n ih =>
    intro v hv
    let u := Function.update v k n
    have e1 : S.den v tl tr = r.lhs.den u tl tr := by
      rw [SC.beq_sound _ _ hl, SC.den_subst]
      congr 1
      funext i
      simp only [u, Lin.eval_add, Lin.eval_var, Lin.eval_const, Function.update_self]
      by_cases h : i = k
      · subst h; simp [hv]
      · simp [Function.update_of_ne h]
    have e2 : r.rhs.den u tl tr = S.den (sem (iterL k ds) u) tl tr := by
      rw [SC.beq_sound _ _ hrr, SC.den_substAll]
    let w := sem (iterL k ds) u
    have hw : w k = n := by
      simp only [w, sem_iterL, u]; simp
    have e3 : sem (iterR k ds) w = sem (iterR k ds) v := by
      funext i
      by_cases h1 : i < ds.length
      · by_cases h2 : i = k
        · rw [sem_iterR, sem_iterR, ite_eq_left h1, ite_eq_left h1, ite_eq_left h2, ite_eq_left h2]
        · have hwi : w i = v i + ds.getD i 0 := by
            simp only [w, sem_iterL, u, Function.update_of_ne h2]; simp [h1, h2]
          rw [sem_iterR, sem_iterR, ite_eq_left h1, ite_eq_left h1, ite_eq_right h2,
            ite_eq_right h2, hwi, hw, hv,
            Nat.add_mul, Nat.one_mul]
          omega
      · have : i ≠ k := by omega
        have hwi : w i = v i := by
          simp only [w, sem_iterL, u, Function.update_of_ne this]; simp [h1]
        rw [sem_iterR, sem_iterR, ite_eq_right h1, ite_eq_right h1, hwi]
    have h1 := (hr u tl tr htd).1
    rw [← e1, e2] at h1
    have h2 := ih w hw
    rw [e3] at h2
    exact rstar_trans h1 h2

def buildRules (M : TM) : List Rule → List RDef → Option (List Rule)
  | done, [] => some done
  | done, .prove r pf :: ds =>
    if run M [] done r.dflt pf [⟨r.lhs, r.plus, .cfg r.rhs⟩] then buildRules M (done ++ [r]) ds
    else none
  | done, .iter j S k dl :: ds =>
    match done[j]? with
    | some r =>
      if decide (k < dl.length) && r.lhs.beq (S.subst k ((Lin.var k).add (Lin.const 1))) &&
          r.rhs.beq (S.substAll (iterL k dl)) then
        buildRules M (done ++ [⟨S, S.substAll (iterR k dl), false, r.dflt⟩]) ds
      else none
    | none => none

theorem buildRules_sound (M : TM) : ∀ (ds : List RDef) (done rs : List Rule),
    (∀ r ∈ done, RuleOK M r) → buildRules M done ds = some rs → ∀ r ∈ rs, RuleOK M r
  | [], done, rs, hd, h => by simp only [buildRules, Option.some.injEq] at h; subst h; exact hd
  | .prove r pf :: ds, done, rs, hd, h => by
    simp only [buildRules] at h
    split at h
    · rename_i hrun
      refine buildRules_sound M ds (done ++ [r]) rs ?_ h
      intro r' hr'
      rcases List.mem_append.mp hr' with hr' | hr'
      · exact hd r' hr'
      · simp only [List.mem_singleton] at hr'; subst hr'
        have hg := run_sound M [] (by simp) done hd r'.dflt pf _ hrun ⟨r'.lhs, r'.plus, .cfg r'.rhs⟩
          (by simp)
        intro v tl tr htd
        obtain ⟨c', h1, h2, h3⟩ := hg v tl tr htd
        simp only [Final] at h3
        subst h3
        exact ⟨h1, h2⟩
    · simp at h
  | .iter j S k dl :: ds, done, rs, hd, h => by
    simp only [buildRules] at h
    cases hj : done[j]? with
    | none => simp [hj] at h
    | some r =>
      simp only [hj] at h
      split at h
      · rename_i hc
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        refine buildRules_sound M ds _ rs ?_ h
        intro r' hr'
        rcases List.mem_append.mp hr' with hr' | hr'
        · exact hd r' hr'
        · simp only [List.mem_singleton] at hr'; subst hr'
          exact iter_sound M S k dl hc.1.1 r (hd r (List.mem_of_getElem? hj)) hc.1.2 hc.2
      · simp at h

-- ---------------------------------------------------------------------------
-- 6.11 Certificates and the main soundness theorem
-- ---------------------------------------------------------------------------

structure Certificate where
  hubs : List SC
  rules : List RDef
  pf : List Ins

def initSC : SC := ⟨0, true, [], []⟩

def checkCert (M : TM) (c : Certificate) : Bool :=
  c.hubs.all hubOK &&
  match buildRules M [] c.rules with
  | some rs => run M c.hubs rs true c.pf (⟨initSC, false, .ps⟩ :: c.hubs.map (fun h => ⟨h, true,
    .hubs⟩))
  | none => false

theorem checkCert_sound (M : TM) (c : Certificate) (h : checkCert M c
  = true) : HasCollatzReduction M := by
  simp only [checkCert, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hh, hb⟩ := h
  cases hrs : buildRules M [] c.rules with
  | none => simp [hrs] at hb
  | some rs =>
    simp only [hrs] at hb
    have hr := buildRules_sound M c.rules [] rs (by simp) hrs
    have hg := run_sound M c.hubs hh rs hr true c.pf _ hb
    refine ⟨hubsPS c.hubs, ?_, ?_⟩
    · obtain ⟨c', h1, _, h3⟩ := hg ⟨initSC, false, .ps⟩ (by simp) (fun _ => 0) default default
        (fun _ => ⟨rfl, rfl⟩)
      exact ⟨c', h1, h3⟩
    · intro cfg hcfg
      obtain ⟨entry, hmem, vars, hcv, _⟩ := hcfg
      obtain ⟨hub, hhub, rfl⟩ := List.mem_map.mp hmem
      rw [toPat_eval hub (hh hub hhub) vars] at hcv
      subst hcv
      obtain ⟨c', _, h2, h3⟩ := hg ⟨hub, true, .hubs⟩ (by simp [hhub]) vars default default
        (fun _ => ⟨rfl, rfl⟩)
      exact ⟨c', h2 rfl, h3⟩

theorem step_isSome_of_ms_pos {M : TM} {a b : Cfg Sym St} {n : ℕ} (hn : n > 0)
    (h : multiStep M a n = some b) : (step M a).isSome = true := by
  have hk : n = 1 + (n - 1) := by omega
  rw [hk, ms_add, ms_succ, ms_zero] at h
  cases hs : step M a with
  | none => simp [hs] at h
  | some c => rfl

theorem step_isSome_of_ms_lt {M : TM} {c₀ a b : Cfg Sym St} {n k : ℕ} (hlt : n < k)
    (hn : multiStep M c₀ n = some a) (hk : multiStep M c₀ k = some b) :
    (step M a).isSome = true := by
  have h1 : k = n + (k - n) := by omega
  rw [h1, ms_add, hn] at hk
  exact step_isSome_of_ms_pos (by omega) hk

theorem closed_ps_arb_long {M : TM} {ps : TapePatternSet Sym St}
    (h0 : ∃ cfg₀, RStar M (init []) cfg₀ ∧ IsInPatternSet ps cfg₀)
    (hstep : ∀ cfg, IsInPatternSet ps cfg → ∃ cfg', RPlus M cfg cfg' ∧ IsInPatternSet ps cfg') :
    ∀ m : ℕ, ∃ k ≥ m, ∃ cfg', multiStep M (init []) k = some cfg' ∧ IsInPatternSet ps cfg'
  | 0 => by
    obtain ⟨cfg₀, ⟨n, hn⟩, hin⟩ := h0
    exact ⟨n, by omega, cfg₀, hn, hin⟩
  | m + 1 => by
    obtain ⟨k, hkm, cfg₁, hk, hin₁⟩ := closed_ps_arb_long h0 hstep m
    obtain ⟨cfg₂, ⟨d, hd0, hd⟩, hin₂⟩ := hstep cfg₁ hin₁
    refine ⟨k + d, by omega, cfg₂, ?_, hin₂⟩
    rw [ms_add, hk]; simpa using hd

def checkNonHalt (M : TM) (c : Certificate) : Bool :=
  c.hubs.all hubOK &&
  match buildRules M [] c.rules with
  | some rs => run M c.hubs rs true c.pf (⟨initSC, false, .ps⟩ :: c.hubs.map (fun h => ⟨h, true,
    .ps⟩))
  | none => false

theorem checkNonHalt_sound (M : TM) (c : Certificate) (h : checkNonHalt M c = true) :
    (∀ (cfg : Cfg (Fin 2) (Fin 6)), ((init []) [M]⊢* cfg) → (step M cfg).isSome) := by
  simp only [checkNonHalt, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hh, hb⟩ := h
  cases hrs : buildRules M [] c.rules with
  | none => simp [hrs] at hb
  | some rs =>
    simp only [hrs] at hb
    have hr := buildRules_sound M c.rules [] rs (by simp) hrs
    have hg := run_sound M c.hubs hh rs hr true c.pf _ hb
    have h0 : ∃ cfg₀, RStar M (init []) cfg₀ ∧ IsInPatternSet (hubsPS c.hubs) cfg₀ := by
      obtain ⟨c', h1, _, h3⟩ := hg ⟨initSC, false, .ps⟩ (by simp) (fun _ => 0) default default
        (fun _ => ⟨rfl, rfl⟩)
      exact ⟨c', h1, h3⟩
    have hstep : ∀ cfg, IsInPatternSet (hubsPS c.hubs) cfg →
        ∃ cfg', RPlus M cfg cfg' ∧ IsInPatternSet (hubsPS c.hubs) cfg' := by
      intro cfg hcfg
      obtain ⟨entry, hmem, vars, hcv, _⟩ := hcfg
      obtain ⟨hub, hhub, rfl⟩ := List.mem_map.mp hmem
      rw [toPat_eval hub (hh hub hhub) vars] at hcv
      subst hcv
      obtain ⟨c', _, h2, h3⟩ := hg ⟨hub, true, .ps⟩ (by simp [hhub]) vars default default
        (fun _ => ⟨rfl, rfl⟩)
      exact ⟨c', h2 rfl, h3⟩
    intro cfg ⟨n, hn⟩
    obtain ⟨k, hkn, c', hk, _⟩ := closed_ps_arb_long h0 hstep (n + 1)
    exact step_isSome_of_ms_lt (by omega) hn hk

def checkTrans (M : TM) (rules : List RDef) (lhs rhs : SC) (pf : List Ins) : Bool :=
  match buildRules M [] rules with
  | some rs => run M [] rs true pf [⟨lhs, true, .cfg rhs⟩]
  | none => false

theorem checkTrans_sound (M : TM) (rules : List RDef) (lhs rhs : SC) (pf : List Ins)
    (h : checkTrans M rules lhs rhs pf = true) (v : ℕ → ℕ) :
    (lhs.den v default default) [M]⊢⁺ (rhs.den v default default) := by
  unfold checkTrans at h
  cases hrs : buildRules M [] rules with
  | none => simp [hrs] at h
  | some rs =>
    simp only [hrs] at h
    have hr := buildRules_sound M rules [] rs (by simp) hrs
    have hg := run_sound M [] (by simp) rs hr true pf _ h ⟨lhs, true, .cfg rhs⟩ (by simp)
    obtain ⟨c', _, h2, h3⟩ := hg v default default (fun _ => ⟨rfl, rfl⟩)
    simp only [Final] at h3; subst h3
    exact h2 rfl

def checkHaltTrans (M : TM) (rules : List RDef) (lhs rhs : SC) (pf : List Ins) : Bool :=
  isHalt M true rhs &&
  match buildRules M [] rules with
  | some rs => run M [] rs true pf [⟨lhs, true, .cfg rhs⟩]
  | none => false

theorem checkHaltTrans_sound (M : TM) (rules : List RDef) (lhs rhs : SC) (pf : List Ins)
    (h : checkHaltTrans M rules lhs rhs pf = true) (v : ℕ → ℕ) :
    ((lhs.den v default default) [M]⊢⁺ (rhs.den v default default)) ∧
      (step M (rhs.den v default default)).isNone := by
  simp only [checkHaltTrans, Bool.and_eq_true] at h
  refine ⟨checkTrans_sound M rules lhs rhs pf h.2 v, ?_⟩
  exact isHalt_sound M true rhs h.1 v default default (fun _ => ⟨rfl, rfl⟩)

def checkHub (M : TM) (hubs : List SC) (rules : List RDef) (hub : SC) (pf : List Ins) : Bool :=
  hubs.all hubOK &&
  match buildRules M [] rules with
  | some rs => run M hubs rs true pf [⟨hub, true, .hubs⟩]
  | none => false

theorem checkHub_sound (M : TM) (hubs : List SC) (rules : List RDef) (hub : SC) (pf : List Ins)
    (h : checkHub M hubs rules hub pf = true) (v : ℕ → ℕ) :
    ∃ cfg', ((hub.den v default default) [M]⊢⁺ cfg') ∧
      (IsInPatternSet (hubsPS hubs) cfg' ∨ (step M cfg').isNone) := by
  simp only [checkHub, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hh, hb⟩ := h
  cases hrs : buildRules M [] rules with
  | none => simp [hrs] at hb
  | some rs =>
    simp only [hrs] at hb
    have hr := buildRules_sound M rules [] rs (by simp) hrs
    have hg := run_sound M hubs hh rs hr true pf _ hb ⟨hub, true, .hubs⟩ (by simp)
    obtain ⟨c', _, h2, h3⟩ := hg v default default (fun _ => ⟨rfl, rfl⟩)
    exact ⟨c', h2 rfl, h3⟩

def checkInit (M : TM) (rules : List RDef) (rhs : SC) (pf : List Ins) : Bool :=
  match buildRules M [] rules with
  | some rs => run M [] rs true pf [⟨initSC, false, .cfg rhs⟩]
  | none => false

theorem checkInit_sound (M : TM) (rules : List RDef) (rhs : SC) (pf : List Ins)
    (h : checkInit M rules rhs pf = true) (v : ℕ → ℕ) :
    (init []) [M]⊢* (rhs.den v default default) := by
  unfold checkInit at h
  cases hrs : buildRules M [] rules with
  | none => simp [hrs] at h
  | some rs =>
    simp only [hrs] at h
    have hr := buildRules_sound M rules [] rs (by simp) hrs
    have hg := run_sound M [] (by simp) rs hr true pf _ h ⟨initSC, false, .cfg rhs⟩ (by simp)
    obtain ⟨c', h1, _, h3⟩ := hg v default default (fun _ => ⟨rfl, rfl⟩)
    simp only [Final] at h3; subst h3
    exact h1

end Cert


-- ============================================================================
-- Section 7: Canonical Configuration Families & Macro-Transition Rules (`ps_100`)
-- ============================================================================


def env6 (a b c d e f : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | _ => 0

theorem env6_0 (a b c d e f : Nat) : env6 a b c d e f 0 = a := rfl
theorem env6_1 (a b c d e f : Nat) : env6 a b c d e f 1 = b := rfl
theorem env6_2 (a b c d e f : Nat) : env6 a b c d e f 2 = c := rfl
theorem env6_3 (a b c d e f : Nat) : env6 a b c d e f 3 = d := rfl
theorem env6_4 (a b c d e f : Nat) : env6 a b c d e f 4 = e := rfl
theorem env6_5 (a b c d e f : Nat) : env6 a b c d e f 5 = f := rfl

lemma congr_cfg1 (f : Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 : Nat} (ha : a1 = a2) :
    f a1 = f a2 := by
  subst ha; rfl

lemma congr_cfg2 (f : Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 : Nat} (ha : a1 = a2) (hb : b1 = b2) :
    f a1 b1 = f a2 b2 := by
  subst ha hb; rfl

lemma congr_cfg3 (f : Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) :
    f a1 b1 c1 = f a2 b2 c2 := by
  subst ha hb hc; rfl

lemma congr_cfg4 (f : Nat → Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 d1 d2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    f a1 b1 c1 d1 = f a2 b2 c2 d2 := by
  subst ha hb hc hd; rfl

lemma congr_cfg5 (f : Nat → Nat → Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1
      = c2) (hd : d1 = d2) (he : e1 = e2) :
    f a1 b1 c1 d1 e1 = f a2 b2 c2 d2 e2 := by
  subst ha hb hc hd he; rfl

lemma congr_cfg6 (f : Nat → Nat → Nat → Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 d1 d2 e1 e2 f1 f2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1
      = c2) (hd : d1 = d2) (he : e1 = e2) (hf : f1 = f2) :
    f a1 b1 c1 d1 e1 f1 = f a2 b2 c2 d2 e2 f2 := by
  subst ha hb hc hd he hf; rfl

def hub_1 : Cert.SC := ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [0, 0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

def hub_2 : Cert.SC := ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

def hub_3 : Cert.SC := ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩]⟩

def hub_4 : Cert.SC := ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [0, 0, 0, 1]⟩⟩]⟩

def hubs : List Cert.SC := [hub_1, hub_2, hub_3, hub_4]

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 (.sym 1 .default))) }

def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 .default) }

def pat_P3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 .default }

def pat_P4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true), (pat_P3, .true), (pat_P4, .true)]

abbrev ps_100 : TapePatternSet (Fin 2) (Fin 6) := ps

def cfg_P1 (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_1.den (env6 a b c d 0 0) default default

lemma eval_pat_P1 (vars : Nat → Nat) :
    evalTapePattern pat_P1 vars = cfg_P1 (vars 0) (vars 1) (vars 2) (vars 3) :=
  Cert.toPat_eval hub_1 rfl vars

lemma in_ps_P1 (a b c d : Nat) : IsInPatternSet ps_100 (cfg_P1 a b c d) :=
  Cert.in_hubsPS hubs (by decide) hub_1 (by simp [hubs]) (env6 a b c d 0 0)

def cfg_P2 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_2.den (env6 a b c 0 0 0) default default

lemma eval_pat_P2 (vars : Nat → Nat) :
    evalTapePattern pat_P2 vars = cfg_P2 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_2 rfl vars

lemma in_ps_P2 (a b c : Nat) : IsInPatternSet ps_100 (cfg_P2 a b c) :=
  Cert.in_hubsPS hubs (by decide) hub_2 (by simp [hubs]) (env6 a b c 0 0 0)

def cfg_P3 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_3.den (env6 a b c 0 0 0) default default

lemma eval_pat_P3 (vars : Nat → Nat) :
    evalTapePattern pat_P3 vars = cfg_P3 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_3 rfl vars

lemma in_ps_P3 (a b c : Nat) : IsInPatternSet ps_100 (cfg_P3 a b c) :=
  Cert.in_hubsPS hubs (by decide) hub_3 (by simp [hubs]) (env6 a b c 0 0 0)

def cfg_P4 (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_4.den (env6 a b c d 0 0) default default

lemma eval_pat_P4 (vars : Nat → Nat) :
    evalTapePattern pat_P4 vars = cfg_P4 (vars 0) (vars 1) (vars 2) (vars 3) :=
  Cert.toPat_eval hub_4 rfl vars

lemma in_ps_P4 (a b c d : Nat) : IsInPatternSet ps_100 (cfg_P4 a b c d) :=
  Cert.in_hubsPS hubs (by decide) hub_4 (by simp [hubs]) (env6 a b c d 0 0)

def rdefs : List Cert.RDef := [
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0]
]

def rule_1_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 2 .splitF, .rw false 2 .unpack, .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 1: `P_1(0, 2b, c, 0) -> P_2(0, 0, b + c + 2)`. -/
theorem rule_1 (b c : Nat) :
    (cfg_P1 0 (2 * b) c 0) [target]⊢⁺ (cfg_P2 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_2.substAll [⟨0, []⟩,
      ⟨0, []⟩, ⟨2, [0, 1, 1]⟩])
    rule_1_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 0 (2 * b) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_2_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1),
  .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2),
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 2: `P_1(0, 2b + 1, c, 0) -> P_1(b + c, 4, 1, 2)`. -/
theorem rule_2 (b c : Nat) :
    (cfg_P1 0 (2 * b + 1) c 0) [target]⊢⁺ (cfg_P1 (b + c) 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 1,
      1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_2_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 0 (2 * b + 1) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_3_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw false 0 (.pack 2), .rw false 0 .merge, .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩,
  ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 3: `P_1(1, 0, c, 0) -> P_1(c, 4, 1, 2)`. -/
theorem rule_3 (c : Nat) :
    (cfg_P1 1 0 c 0) [target]⊢⁺ (cfg_P1 c 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩,
      ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_3_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 0 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_4_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .zdrop, .step, .step, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1),
  .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1),
  .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .done]

set_option maxRecDepth 200000 in
/-- Rule 4: `P_1(1, 1, c, 0) -> P_1(0, 0, 1, c + 2)`. -/
theorem rule_4 (c : Nat) :
    (cfg_P1 1 1 c 0) [target]⊢⁺ (cfg_P1 0 0 1 (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, []⟩, ⟨0,
      []⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩])
    rule_4_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 1 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 0 0 1 (c + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_5_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .splitF, .step, .rw true 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .rw true 1 .merge, .rw true 1 (.zins [1, 0]), .rw false 3 .splitF,
  .rw false 3 .unpack, .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 4 (.pack 2), .rw false 4 .merge, .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 5: `P_1(1, 2, c, 0) -> P_2(0, 2, c + 3)`. -/
theorem rule_5 (c : Nat) :
    (cfg_P1 1 2 c 0) [target]⊢⁺ (cfg_P2 0 2 (c + 3)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_2.substAll [⟨0, []⟩, ⟨2,
      []⟩, ⟨3, [0, 0, 1]⟩])
    rule_5_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 2 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P2 0 2 (c + 3) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_6_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0], ⟨1, []⟩⟩,
  ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
def rule_6_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .splitF, .step, .rw true 0 .splitF, .done]

/-- Rule 6 (Halting): `P_1(1, b + 3, c, 0) -> Halt`. -/
theorem rule_6_halt (b c : Nat) :
    ∃ cfg', ((cfg_P1 1 (b + 3) c 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) rule_6_rhs
    rule_6_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 1 (b + 3) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_6_rhs.den (env6 0 b c 0 0 0) default default, h_tr.1, h_tr.2⟩

def rule_7_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .step, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 7: `P_1(a + 2, b, c, 0) -> P_1(a, b, 1, c + 2)`. -/
theorem rule_7 (a b c : Nat) :
    (cfg_P1 (a + 2) b c 0) [target]⊢⁺ (cfg_P1 a b 1 (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [1]⟩,
      ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩])
    rule_7_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 a b c 0 0 0) default default = cfg_P1 (a + 2) b c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P1 a b 1 (c + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_8_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩]⟩
def rule_8_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 8 (Halting): `P_1(0, 0, 0, d + 1) -> Halt`. -/
theorem rule_8_halt (d : Nat) :
    ∃ cfg', ((cfg_P1 0 0 0 (d + 1)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0, 1]⟩]) rule_8_rhs
    rule_8_pf rfl (env6 0 0 0 d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 0 d 0 0) default default = cfg_P1 0 0 0 (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 0 d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rw [hL] at h_tr
  exact ⟨rule_8_rhs.den (env6 0 0 0 d 0 0) default default, h_tr.1, h_tr.2⟩

def rule_9_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 9: `P_1(0, 0, c + 1, d + 1) -> P_4(c, 4, 1, d + 2)`. -/
theorem rule_9 (c d : Nat) :
    (cfg_P1 0 0 (c + 1) (d + 1)) [target]⊢⁺ (cfg_P4 c 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩]) (hub_4.substAll [⟨0,
      [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_9_pf rfl (env6 0 0 c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P1 0 0 (c + 1) (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P4 c 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_4 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_10_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .rw false 0 (.pack 2), .rw false 0 .merge, .shift, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 10: `P_1(0, 2b + 2, c, d + 1) -> P_4(b + c, 4, 1, d + 2)`. -/
theorem rule_10 (b c d : Nat) :
    (cfg_P1 0 (2 * b + 2) c (d + 1)) [target]⊢⁺ (cfg_P4 (b + c) 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_10_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 (2 * b + 2) c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 (b + c) 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_4 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_11_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

set_option maxRecDepth 200000 in
/-- Rule 11: `P_1(0, 2b + 1, c, d + 1) -> P_1(0, 0, b + c + 2, d)`. -/
theorem rule_11 (b c d : Nat) :
    (cfg_P1 0 (2 * b + 1) c (d + 1)) [target]⊢⁺ (cfg_P1 0 0 (b + c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_11_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 (2 * b + 1) c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 0 (b + c + 2) d :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_12_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 12: `P_1(a + 1, b, c, d + 1) -> P_1(a, b, c + 2, d)`. -/
theorem rule_12 (a b c d : Nat) :
    (cfg_P1 (a + 1) b c (d + 1)) [target]⊢⁺ (cfg_P1 a b (c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_12_pf rfl (env6 a b c d 0 0)
  have hL : (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P1 (a + 1) b c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P1 a b (c + 2) d :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_13_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
def rule_13_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, []⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, []⟩, ⟨1, []⟩],
  .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 13 (Halting): `P_2(0, 0, 0) -> Halt`. -/
theorem rule_13_halt :
    ∃ cfg', ((cfg_P2 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_13_rhs
    rule_13_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P2 0 0 0 :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_13_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

def rule_14_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, []⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, []⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .done]

/-- Rule 14: `P_2(0, 0, c + 1) -> P_1(c, 4, 1, 1)`. -/
theorem rule_14 (c : Nat) :
    (cfg_P2 0 0 (c + 1)) [target]⊢⁺ (cfg_P1 c 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩,
      ⟨1, []⟩, ⟨1, []⟩])
    rule_14_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P2 0 0 (c + 1) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_15_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .done]

set_option maxRecDepth 200000 in
/-- Rule 15: `P_2(0, 2b + 2, c) -> P_1(b + c, 4, 1, 1)`. -/
theorem rule_15 (b c : Nat) :
    (cfg_P2 0 (2 * b + 2) c) [target]⊢⁺ (cfg_P1 (b + c) 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4,
      []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_15_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 (2 * b + 2) c :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_16_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step, .rw true 0 (.group 2),
  .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 16: `P_2(0, 2b + 1, c) -> P_3(0, 0, b + c + 2)`. -/
theorem rule_16 (b c : Nat) :
    (cfg_P2 0 (2 * b + 1) c) [target]⊢⁺ (cfg_P3 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩,
      ⟨2, [0, 1, 1]⟩])
    rule_16_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 (2 * b + 1) c :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_17_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 17: `P_2(a + 1, b, c) -> P_3(a, b, c + 2)`. -/
theorem rule_17 (a b c : Nat) :
    (cfg_P2 (a + 1) b c) [target]⊢⁺ (cfg_P3 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩]) (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0,
      1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_17_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_2.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P2 (a + 1) b c :=
    (Cert.SC.den_substAll hub_2 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 a b (c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_18_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
def rule_18_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 18 (Halting): `P_3(0, 0, 0) -> Halt`. -/
theorem rule_18_halt :
    ∃ cfg', ((cfg_P3 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_18_rhs
    rule_18_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P3 0 0 0 :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_18_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

def rule_19_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 19: `P_3(0, 0, c + 1) -> P_1(c, 4, 1, 2)`. -/
theorem rule_19 (c : Nat) :
    (cfg_P3 0 0 (c + 1)) [target]⊢⁺ (cfg_P1 c 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩,
      ⟨1, []⟩, ⟨2, []⟩])
    rule_19_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P3 0 0 (c + 1) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_20_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .done]

/-- Rule 20: `P_3(0, 2b + 2, c) -> P_1(b + c, 4, 1, 2)`. -/
theorem rule_20 (b c : Nat) :
    (cfg_P3 0 (2 * b + 2) c) [target]⊢⁺ (cfg_P1 (b + c) 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4,
      []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_20_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 (2 * b + 2) c :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_21_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 21: `P_3(0, 2b + 1, c) -> P_2(0, 0, b + c + 2)`. -/
theorem rule_21 (b c : Nat) :
    (cfg_P3 0 (2 * b + 1) c) [target]⊢⁺ (cfg_P2 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩,
      ⟨2, [0, 1, 1]⟩])
    rule_21_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 (2 * b + 1) c :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_22_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 22: `P_3(a + 1, b, c) -> P_2(a, b, c + 2)`. -/
theorem rule_22 (a b c : Nat) :
    (cfg_P3 (a + 1) b c) [target]⊢⁺ (cfg_P2 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩]) (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0,
      1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_22_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_3.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 (a + 1) b c :=
    (Cert.SC.den_substAll hub_3 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P2 a b (c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_23_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
def rule_23_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .step, .done]

/-- Rule 23 (Halting): `P_4(0, 0, 0, 0) -> Halt`. -/
theorem rule_23_halt :
    ∃ cfg', ((cfg_P4 0 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_23_rhs
    rule_23_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P4 0 0 0 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0,
      []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_23_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

def rule_24_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2),
  .rw false 0 (.pack 2), .done]

/-- Rule 24: `P_4(0, 0, c + 1, 0) -> P_1(c, 4, 1, 1)`. -/
theorem rule_24 (c : Nat) :
    (cfg_P4 0 0 (c + 1) 0) [target]⊢⁺ (cfg_P1 c 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩,
      ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_24_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P4 0 0 (c + 1) 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_25_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2),
  .rw false 0 (.pack 2), .done]

/-- Rule 25: `P_4(0, 2b + 2, c, 0) -> P_1(b + c, 4, 1, 1)`. -/
theorem rule_25 (b c : Nat) :
    (cfg_P4 0 (2 * b + 2) c 0) [target]⊢⁺ (cfg_P1 (b + c) 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 1,
      1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_25_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P4 0 (2 * b + 2) c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

def rule_26_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 26: `P_4(0, 2b + 1, c, 0) -> P_3(0, 0, b + c + 2)`. -/
theorem rule_26 (b c : Nat) :
    (cfg_P4 0 (2 * b + 1) c 0) [target]⊢⁺ (cfg_P3 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_3.substAll [⟨0, []⟩,
      ⟨0, []⟩, ⟨2, [0, 1, 1]⟩])
    rule_26_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P4 0 (2 * b + 1) c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_27_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 27: `P_4(a + 1, b, c, 0) -> P_3(a, b, c + 2)`. -/
theorem rule_27 (a b c : Nat) :
    (cfg_P4 (a + 1) b c 0) [target]⊢⁺ (cfg_P3 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_3.substAll [⟨0, [1]⟩,
      ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_27_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 a b c 0 0 0) default default = cfg_P4 (a + 1) b c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 a b (c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_28_rhs : Cert.SC := ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
def rule_28_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .step, .done]

/-- Rule 28 (Halting): `P_4(0, 0, 0, d + 1) -> Halt`. -/
theorem rule_28_halt (d : Nat) :
    ∃ cfg', ((cfg_P4 0 0 0 (d + 1)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0, 1]⟩]) rule_28_rhs
    rule_28_pf rfl (env6 0 0 0 d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 0 d 0 0) default default = cfg_P4 0 0 0 (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 0 d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rw [hL] at h_tr
  exact ⟨rule_28_rhs.den (env6 0 0 0 d 0 0) default default, h_tr.1, h_tr.2⟩

def rule_29_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 29: `P_4(0, 0, c + 1, d + 1) -> P_1(c, 4, 1, d + 2)`. -/
theorem rule_29 (c d : Nat) :
    (cfg_P4 0 0 (c + 1) (d + 1)) [target]⊢⁺ (cfg_P1 c 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩]) (hub_1.substAll [⟨0,
      [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_29_pf rfl (env6 0 0 c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P4 0 0 (c + 1) (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P1 c 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_30_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .rw false 0 (.pack 2), .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 30: `P_4(0, 2b + 2, c, d + 1) -> P_1(b + c, 4, 1, d + 2)`. -/
theorem rule_30 (b c d : Nat) :
    (cfg_P4 0 (2 * b + 2) c (d + 1)) [target]⊢⁺ (cfg_P1 (b + c) 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_30_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 (2 * b + 2) c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 (b + c) 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_31_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 31: `P_4(0, 2b + 1, c, d + 1) -> P_4(0, 0, b + c + 2, d)`. -/
theorem rule_31 (b c d : Nat) :
    (cfg_P4 0 (2 * b + 1) c (d + 1)) [target]⊢⁺ (cfg_P4 0 0 (b + c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_31_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 (2 * b + 1) c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 0 (b + c + 2) d :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

def rule_32_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 32: `P_4(a + 1, b, c, d + 1) -> P_4(a, b, c + 2, d)`. -/
theorem rule_32 (a b c d : Nat) :
    (cfg_P4 (a + 1) b c (d + 1)) [target]⊢⁺ (cfg_P4 a b (c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_32_pf rfl (env6 a b c d 0 0)
  have hL : (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P4 (a + 1) b c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P4 a b (c + 2) d :=
    (Cert.SC.den_substAll hub_4 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

-- ============================================================================
-- Section 8: Blank-Tape Entry & Complete Closure Proof (`IsCryptid`)
-- ============================================================================

def init_pf : List Cert.Ins := [.step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 2 (.pack 2),
  .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Blank initial tape `init []` reaches `cfg_P2 0 0 2` in 12 concrete steps. -/
theorem init_reaches_P2 : (init []) [target]⊢* (cfg_P2 0 0 2) :=
  Cert.checkInit_sound target rdefs ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, []⟩⟩, ⟨[1], ⟨0,
    []⟩⟩], [⟨[0, 1], ⟨2, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩ init_pf rfl (env6 0 0 0 0 0 0)

theorem audit_ps_nonempty : ∃ cfg, IsInPatternSet ps_100 cfg :=
  ⟨cfg_P2 0 0 2, in_ps_P2 0 0 2⟩

theorem audit_init_neq_cfg0 :
    (init [] : Cfg (Fin 2) (Fin 6)) ≠ cfg_P2 0 0 2 := by
  intro h
  have h_neq := congr_arg (fun c => c.q) h
  revert h_neq
  decide

def hub_1_pf : List Cert.Ins := [.shift, .step, .splitZ 3, .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2),
  .rw true 0 .merge, .shift, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 2 .splitF, .rw false 2 .unpack, .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩],
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2),
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 0,
  .rw true 0 .zdrop, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge,
  .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩],
  .rw true 0 .splitF, .step, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step,
  .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩],
  .rw true 0 .splitF, .step, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .rw true 1 .merge, .rw true 1 (.zins [1, 0]), .rw false 3 .splitF,
  .rw false 3 .unpack, .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 4 (.pack 2), .rw false 4 .merge, .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 1 [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0, 1]⟩],
  .rw true 0 .splitF, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .step,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .shift,
  .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .hub 3 [⟨0, [0, 0, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 3 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 0 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0,
  0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 0 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 1 (`cfg_P1 a b c d`) across all `(a b c d) ∈ ℕ^4`. -/
theorem step_P1_all (a b c d : Nat) :
    ∃ cfg', ((cfg_P1 a b c d) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps_100 cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_1 hub_1_pf rfl (env6 a b c d 0 0)

def hub_2_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨1, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
  []⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 2 (`cfg_P2 a b c`) across all `(a b c) ∈ ℕ^3`. -/
theorem step_P2_all (a b c : Nat) :
    ∃ cfg', ((cfg_P2 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps_100 cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_2 hub_2_pf rfl (env6 a b c 0 0 0)

def hub_3_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2,
  .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF,
  .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 3 (`cfg_P3 a b c`) across all `(a b c) ∈ ℕ^3`. -/
theorem step_P3_all (a b c : Nat) :
    ∃ cfg', ((cfg_P3 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps_100 cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_3 hub_3_pf rfl (env6 a b c 0 0 0)

def hub_4_pf : List Cert.Ins := [.shift, .step, .splitZ 3, .rw false 0 .zdrop, .step, .step,
  .step, .rw true 0 (.rotB 1), .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0,
  [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
  []⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .shift,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop,
  .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
  0, 1]⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step,
  .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 5 (.rotB 1),
  .rw false 5 (.rot 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩],
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 4 (`cfg_P4 a b c d`) across all `(a b c d) ∈ ℕ^4`. -/
theorem step_P4_all (a b c d : Nat) :
    ∃ cfg', ((cfg_P4 a b c d) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps_100 cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_4 hub_4_pf rfl (env6 a b c d 0 0)

theorem step_all (cfg : Cfg (Fin 2) (Fin 6)) (h_in : IsInPatternSet ps cfg) :
    ∃ cfg', ((cfg) [target]⊢⁺ cfg') ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl | rfl | rfl
  · rw [eval_pat_P1 vars]
    exact step_P1_all (vars 0) (vars 1) (vars 2) (vars 3)
  · rw [eval_pat_P2 vars]
    exact step_P2_all (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_P3 vars]
    exact step_P3_all (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_P4 vars]
    exact step_P4_all (vars 0) (vars 1) (vars 2) (vars 3)

theorem is_closed_pattern_set : IsClosedPatternSet target ps :=
  ⟨⟨cfg_P2 0 0 2, init_reaches_P2, in_ps_P2 0 0 2⟩, step_all⟩

theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

inductive State where
  | P_1 (a b c d : ℕ)
  | P_2 (a b c : ℕ)
  | P_3 (a b c : ℕ)
  | P_4 (a b c d : ℕ)
  deriving DecidableEq, Repr

def start : State := .P_2 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a b c d => evalTapePattern pat_P1 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)
  | .P_2 a b c => evalTapePattern pat_P2 (fun | 0 => a | 1 => b | 2 => c | _ => 0)
  | .P_3 a b c => evalTapePattern pat_P3 (fun | 0 => a | 1 => b | 2 => c | _ => 0)
  | .P_4 a b c d => evalTapePattern pat_P4 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)

private lemma encode_P1 (a b c d : ℕ) : encode (.P_1 a b c d) = cfg_P1 a b c d :=
  eval_pat_P1 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)

private lemma encode_P2 (a b c : ℕ) : encode (.P_2 a b c) = cfg_P2 a b c :=
  eval_pat_P2 (fun | 0 => a | 1 => b | 2 => c | _ => 0)

private lemma encode_P3 (a b c : ℕ) : encode (.P_3 a b c) = cfg_P3 a b c :=
  eval_pat_P3 (fun | 0 => a | 1 => b | 2 => c | _ => 0)

private lemma encode_P4 (a b c d : ℕ) : encode (.P_4 a b c d) = cfg_P4 a b c d :=
  eval_pat_P4 (fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0)

def next : State → Option State
  | .P_1 0 b c 0 =>
    if b % 2 = 0 then some (.P_2 0 0 (b / 2 + c + 2))
    else some (.P_1 (b / 2 + c) 4 1 2)
  | .P_1 1 0 c 0 => some (.P_1 c 4 1 2)
  | .P_1 1 1 c 0 => some (.P_1 0 0 1 (c + 2))
  | .P_1 1 2 c 0 => some (.P_2 0 2 (c + 3))
  | .P_1 1 (_ + 3) _ 0 => none
  | .P_1 (a + 2) b c 0 => some (.P_1 a b 1 (c + 2))
  | .P_1 0 0 0 (_ + 1) => none
  | .P_1 0 0 (c + 1) (d + 1) => some (.P_4 c 4 1 (d + 2))
  | .P_1 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_4 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_1 0 0 (b' / 2 + c + 2) d)
  | .P_1 (a + 1) b c (d + 1) => some (.P_1 a b (c + 2) d)
  | .P_2 0 0 0 => none
  | .P_2 0 0 (c + 1) => some (.P_1 c 4 1 1)
  | .P_2 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_2 (a + 1) b c => some (.P_3 a b (c + 2))
  | .P_3 0 0 0 => none
  | .P_3 0 0 (c + 1) => some (.P_1 c 4 1 2)
  | .P_3 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 2)
    else some (.P_2 0 0 (b' / 2 + c + 2))
  | .P_3 (a + 1) b c => some (.P_2 a b (c + 2))
  | .P_4 0 0 0 0 => none
  | .P_4 0 0 (c + 1) 0 => some (.P_1 c 4 1 1)
  | .P_4 0 (b' + 1) c 0 =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_4 (a + 1) b c 0 => some (.P_3 a b (c + 2))
  | .P_4 0 0 0 (_ + 1) => none
  | .P_4 0 0 (c + 1) (d + 1) => some (.P_1 c 4 1 (d + 2))
  | .P_4 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_4 0 0 (b' / 2 + c + 2) d)
  | .P_4 (a + 1) b c (d + 1) => some (.P_4 a b (c + 2) d)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone = true
  | .P_1 0 b c 0 => by
    simp only [next]
    split_ifs with h
    · have h_r := rule_1 (b / 2) c
      have hb : 2 * (b / 2) = b := by omega
      rw [hb] at h_r
      simp only [encode_P1, encode_P2]
      exact h_r
    · have h_r := rule_2 (b / 2) c
      have hb : 2 * (b / 2) + 1 = b := by omega
      rw [hb] at h_r
      simp only [encode_P1]
      exact h_r
  | .P_1 1 0 c 0 => by simp only [next, encode_P1]; exact rule_3 c
  | .P_1 1 1 c 0 => by simp only [next, encode_P1]; exact rule_4 c
  | .P_1 1 2 c 0 => by simp only [next, encode_P1, encode_P2]; exact rule_5 c
  | .P_1 1 (b + 3) c 0 => by
    simp only [next, encode_P1]
    rcases rule_6_halt b c with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_1 (a + 2) b c 0 => by simp only [next, encode_P1]; exact rule_7 a b c
  | .P_1 0 0 0 (d + 1) => by
    simp only [next, encode_P1]
    rcases rule_8_halt d with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_1 0 0 (c + 1) (d + 1) => by simp only [next, encode_P1, encode_P4]; exact rule_9 c d
  | .P_1 0 (b' + 1) c (d + 1) => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P1, encode_P4, hb]
      exact rule_10 (b' / 2) c d
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P1, hb]
      exact rule_11 (b' / 2) c d
  | .P_1 (a + 1) b c (d + 1) => by simp only [next, encode_P1]; exact rule_12 a b c d
  | .P_2 0 0 0 => by
    simp only [next, encode_P2]
    rcases rule_13_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_2 0 0 (c + 1) => by simp only [next, encode_P2, encode_P1]; exact rule_14 c
  | .P_2 0 (b' + 1) c => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P2, encode_P1, hb]
      exact rule_15 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P2, encode_P3, hb]
      exact rule_16 (b' / 2) c
  | .P_2 (a + 1) b c => by simp only [next, encode_P2, encode_P3]; exact rule_17 a b c
  | .P_3 0 0 0 => by
    simp only [next, encode_P3]
    rcases rule_18_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_3 0 0 (c + 1) => by simp only [next, encode_P3, encode_P1]; exact rule_19 c
  | .P_3 0 (b' + 1) c => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P3, encode_P1, hb]
      exact rule_20 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P3, encode_P2, hb]
      exact rule_21 (b' / 2) c
  | .P_3 (a + 1) b c => by simp only [next, encode_P3, encode_P2]; exact rule_22 a b c
  | .P_4 0 0 0 0 => by
    simp only [next, encode_P4]
    rcases rule_23_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_4 0 0 (c + 1) 0 => by simp only [next, encode_P4, encode_P1]; exact rule_24 c
  | .P_4 0 (b' + 1) c 0 => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P4, encode_P1, hb]
      exact rule_25 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P4, encode_P3, hb]
      exact rule_26 (b' / 2) c
  | .P_4 (a + 1) b c 0 => by simp only [next, encode_P4, encode_P3]; exact rule_27 a b c
  | .P_4 0 0 0 (d + 1) => by
    simp only [next, encode_P4]
    rcases rule_28_halt d with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_4 0 0 (c + 1) (d + 1) => by simp only [next, encode_P4, encode_P1]; exact rule_29 c d
  | .P_4 0 (b' + 1) c (d + 1) => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P4, encode_P1, hb]
      exact rule_30 (b' / 2) c d
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P4, hb]
      exact rule_31 (b' / 2) c d
  | .P_4 (a + 1) b c (d + 1) => by simp only [next, encode_P4]; exact rule_32 a b c d

theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := by
    dsimp [start]
    rw [encode_P2]
    exact init_reaches_P2
  step_some s s' hnext := by
    have h := step_state s
    rw [hnext] at h
    exact h
  step_none s hnext := by
    have h := step_state s
    rw [hnext] at h
    exact h

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD
