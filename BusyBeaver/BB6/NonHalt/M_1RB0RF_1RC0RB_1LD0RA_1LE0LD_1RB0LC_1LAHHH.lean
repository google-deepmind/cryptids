/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Counter
import BusyBeaver.Calculi.Longitudinal

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LAHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LAHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

section

set_option maxRecDepth 2000000

open BusyBeaver.Longitudinal

local notation "A" => (0 : Fin 6)
local notation "B" => (1 : Fin 6)
local notation "C" => (2 : Fin 6)
local notation "D" => (3 : Fin 6)
local notation "E" => (4 : Fin 6)
local notation "F" => (5 : Fin 6)

abbrev Cfg6 := Cfg (Fin 2) (Fin 6)
abbrev Side6 := ListBlank (Fin 2)
abbrev Sym2 := Fin 2

-- ============================================================================
-- 1. Machine Definitions (`Sk1Class2_v3.v:TM6, TM5, TM7` / #372, #557, #638)
-- ============================================================================

def tm372 : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 .right)
  | 0, 1 => some (some 5, Stmt.write 0 .right)
  | 1, 0 => some (some 2, Stmt.write 1 .right)
  | 1, 1 => some (some 1, Stmt.write 0 .right)
  | 2, 0 => some (some 3, Stmt.write 1 .left)
  | 2, 1 => some (some 0, Stmt.write 0 .right)
  | 3, 0 => some (some 4, Stmt.write 1 .left)
  | 3, 1 => some (some 3, Stmt.write 0 .left)
  | 4, 0 => some (some 1, Stmt.write 1 .right)
  | 4, 1 => some (some 2, Stmt.write 0 .left)
  | 5, 0 => some (some 0, Stmt.write 1 .left)
  | 5, 1 => none

theorem target_eq_tm372 : target = tm372 := by
  funext q a; fin_cases q <;> fin_cases a <;> rfl

-- ============================================================================
-- 2. Symbolic Run-Length Simulator (`Sk1Class2_v3.v:29-208, 539-656`)
-- ============================================================================

def sneg (s : Sym2) : Sym2 := if s = 0 then 1 else 0
def seqb (a b : Sym2) : Bool := a == b

structure lf where
  lc : Nat
  lv : List Nat
  deriving DecidableEq

def dot : List Nat → List Nat → Nat
  | v :: vs', x :: nu' => v * x + dot vs' nu'
  | _, _ => 0

def ev (nu : List Nat) (a : lf) : Nat := a.lc + dot a.lv nu

def zadd : List Nat → List Nat → List Nat
  | x :: a', y :: b' => (x + y) :: zadd a' b'
  | [], b => b
  | a, [] => a

def lf_add (a b : lf) : lf := ⟨a.lc + b.lc, zadd a.lv b.lv⟩
def lf_S (a : lf) : lf := ⟨a.lc + 1, a.lv⟩
def lf_one : lf := ⟨1, []⟩
def cn (n : Nat) : lf := ⟨n, []⟩

def allz (vs : List Nat) : Bool := vs.all (fun v => v == 0)
def all4 (vs : List Nat) : Bool := vs.all (fun v => v % 4 == 0)
def is_zero (a : lf) : Bool := (a.lc == 0) && allz a.lv
def is_one (a : lf) : Bool := (a.lc == 1) && allz a.lv
def posb (a : lf) : Bool := !(a.lc == 0)

inductive tl_ where
  | T0
  | TV (k : Nat)
  deriving DecidableEq

abbrev run := Sym2 × lf
abbrev sd := List run × tl_

def alt (b : Sym2) : Nat → List Sym2
  | 0 => []
  | n + 1 => b :: alt (sneg b) n

def ev_tl (sg : Nat → Side6) : tl_ → Side6
  | .T0 => default
  | .TV k => sg k

def ev_runs (nu : List Nat) : List run → Side6 → Side6
  | [], s => s
  | (b, n) :: rs', s => alt b (ev nu n) +> ev_runs nu rs' s

def ev_sd (nu : List Nat) (sg : Nat → Side6) (s : sd) : Side6 :=
  ev_runs nu s.1 (ev_tl sg s.2)

def pop_runs : List run → tl_ → Option (Sym2 × sd)
  | (b, n) :: rs', t =>
      if is_zero n then pop_runs rs' t
      else if posb n then
        some (b, ((if is_one n then rs' else (sneg b, ⟨n.lc - 1, n.lv⟩) :: rs'), t))
      else none
  | [], .T0 => some (0, ([], .T0))
  | [], .TV _ => none

def pop (s : sd) : Option (Sym2 × sd) := pop_runs s.1 s.2

def push (w : Sym2) : sd → sd
  | ((b0, n0) :: rs, t) =>
      if seqb w b0 then ((w, lf_one) :: (b0, n0) :: rs, t)
      else ((w, lf_S n0) :: rs, t)
  | ([], t) => ([(w, lf_one)], t)

def afterb (c : Sym2) (n : lf) : Sym2 :=
  if n.lc % 2 == 0 then c else sneg c

def push_run (c : Sym2) (n : lf) : sd → sd
  | ((b0, n0) :: rs, t) =>
      if seqb (afterb c n) b0 then ((c, lf_add n n0) :: rs, t)
      else ((c, n) :: (b0, n0) :: rs, t)
  | ([], t) => ([(c, n)], t)

def cR_st (i : Nat) : Fin 6 :=
  match i % 4 with
  | 0 => B | 1 => C | 2 => A | _ => B

def cR_bt (i : Nat) : Sym2 :=
  match i % 4 with
  | 0 => 0 | 1 => 1 | 2 => 0 | _ => 1

def cR_idx (q : Fin 6) (b : Sym2) : Option Nat :=
  match q, b with
  | 1, 0 => some 0 | 2, 1 => some 1 | 0, 0 => some 2 | 1, 1 => some 3
  | _, _ => none

def cL_st (i : Nat) : Fin 6 :=
  match i % 4 with
  | 0 => D | 1 => D | 2 => E | _ => C

def cL_bt (i : Nat) : Sym2 :=
  match i % 4 with
  | 0 => 1 | 1 => 0 | 2 => 1 | _ => 0

def cL_idx (q : Fin 6) (b : Sym2) : Option Nat :=
  match q, b with
  | 3, 1 => some 0 | 3, 0 => some 1 | 4, 1 => some 2 | 2, 0 => some 3
  | _, _ => none

def lastb (c : Sym2) (n : lf) : Sym2 :=
  if n.lc % 2 == 0 then sneg c else c

inductive cfg where
  | Rc (q : Fin 6) (l r : sd)
  | Lc (q : Fin 6) (l r : sd)
  deriving DecidableEq

def ev_cfg (nu : List Nat) (sg : Nat → Side6) : cfg → Cfg6
  | .Rc q l r => (ev_sd nu sg l) {{q}}> (ev_sd nu sg r)
  | .Lc q l r => (ev_sd nu sg l) <{{q}} (ev_sd nu sg r)

def single : cfg → Option cfg
  | .Rc q l r =>
    match pop r with
    | some (s, r') =>
      match tm372 q s with
      | some (some q', ⟨w, .right⟩) => some (.Rc q' (push w l) r')
      | some (some q', ⟨w, .left⟩) => some (.Lc q' l (push w r'))
      | _ => none
    | none => none
  | .Lc q l r =>
    match pop l with
    | some (s, l') =>
      match tm372 q s with
      | some (some q', ⟨w, .right⟩) => some (.Rc q' (push w l') r)
      | some (some q', ⟨w, .left⟩) => some (.Lc q' l' (push w r))
      | _ => none
    | none => none

def tag (o : Option cfg) : Option (cfg × Bool) :=
  o.map (fun c => (c, true))

def sstep (c : cfg) : Option (cfg × Bool) :=
  match c with
  | .Rc q l ((b, n) :: rs, t) =>
      if is_zero n then some (.Rc q l (rs, t), false)
      else match cR_idx q b with
      | some i =>
          if all4 n.lv then
            some (.Rc (cR_st (i + n.lc % 4)) (push_run (sneg (lastb b n)) n l) (rs, t), posb n)
          else tag (single c)
      | none => tag (single c)
  | .Lc q ((b, n) :: ls, t) r =>
      if is_zero n then some (.Lc q (ls, t) r, false)
      else match cL_idx q b with
      | some i =>
          if all4 n.lv then
            some (.Lc (cL_st (i + n.lc % 4)) (ls, t) (push_run (sneg (lastb b n)) n r), posb n)
          else tag (single c)
      | none => tag (single c)
  | _ => tag (single c)

def strip0 : List Nat → List Nat
  | [] => []
  | v :: vs' =>
    match strip0 vs' with
    | [] => if v == 0 then [] else [v]
    | w => v :: w

def listN_eqb : List Nat → List Nat → Bool
  | [], [] => true
  | x :: a', y :: b' => (x == y) && listN_eqb a' b'
  | _, _ => false

def lf_eqb (a b : lf) : Bool :=
  (a.lc == b.lc) && listN_eqb (strip0 a.lv) (strip0 b.lv)

def runs_eqb : List run → List run → Bool
  | [], [] => true
  | (x, n) :: a', (y, m) :: b' => (seqb x y && lf_eqb n m) && runs_eqb a' b'
  | _, _ => false

def tl_eqb : tl_ → tl_ → Bool
  | .T0, .T0 => true
  | .TV i, .TV j => i == j
  | _, _ => false

def sd_eqb (a b : sd) : Bool :=
  runs_eqb a.1 b.1 && tl_eqb a.2 b.2

def cfg_eqb : cfg → cfg → Bool
  | .Rc q l r, .Rc q' l' r' => (q == q') && sd_eqb l l' && sd_eqb r r'
  | .Lc q l r, .Lc q' l' r' => (q == q') && sd_eqb l l' && sd_eqb r r'
  | _, _ => false

def reachAux (tgt : cfg) : Nat → cfg → Bool → Bool
  | 0, _, _ => false
  | fuel + 1, c, pr =>
    match sstep c with
    | some (c', b) =>
      let pr' := pr || b
      if cfg_eqb c' tgt then pr'
      else reachAux tgt fuel c' pr'
    | none => false

def reach (fuel : Nat) (c tgt : cfg) : Bool :=
  reachAux tgt fuel c false

def urun : Nat → cfg → cfg
  | 0, c => c
  | k + 1, c =>
    match sstep c with
    | some (c', _) => urun k c'
    | none => c

-- ============================================================================
-- 3. Layer 1 Soundness (`Sk1Class2_v3.v:213-654, 1380-1398`)
-- ============================================================================

theorem default_unfold : (default : Side6) = 0 >> default :=
  (ListBlank.cons_head_tail (default : Side6)).symm

theorem step_right_R {q q' : Fin 6} {s w : Sym2} (l r : Side6)
    (h : tm372 q s = some (some q', ⟨w, .right⟩)) :
    (l {{q}}> (s >> r)) [tm372]⊢ ((w >> l) {{q'}}> r) := by
  simp [step, h, Tape.write, Tape.move]

theorem step_left_R {q q' : Fin 6} {s w : Sym2} (l r : Side6)
    (h : tm372 q s = some (some q', ⟨w, .left⟩)) :
    (l {{q}}> (s >> r)) [tm372]⊢ (l <{{q'}} (w >> r)) := by
  simp [step, h, Tape.write, Tape.move]

theorem step_right_L {q q' : Fin 6} {s w : Sym2} (l r : Side6)
    (h : tm372 q s = some (some q', ⟨w, .right⟩)) :
    ((s >> l) <{{q}} r) [tm372]⊢ ((w >> l) {{q'}}> r) := by
  simp [step, h, Tape.write, Tape.move]

theorem step_left_L {q q' : Fin 6} {s w : Sym2} (l r : Side6)
    (h : tm372 q s = some (some q', ⟨w, .left⟩)) :
    ((s >> l) <{{q}} r) [tm372]⊢ (l <{{q'}} (w >> r)) := by
  simp [step, h, Tape.write, Tape.move]

theorem step_to_stepPlus {c₁ c₂ : Cfg6} (h : c₁ [tm372]⊢ c₂) : c₁ [tm372]⊢⁺ c₂ :=
  ⟨1, Nat.one_pos, h⟩

theorem step_stepStar_to_stepPlus {c₁ c₂ c₃ : Cfg6}
    (h₁ : c₁ [tm372]⊢ c₂) (h₂ : c₂ [tm372]⊢* c₃) : c₁ [tm372]⊢⁺ c₃ :=
  stepPlus_stepStar_trans (step_to_stepPlus h₁) h₂

theorem step_stepStar_to_stepStar {c₁ c₂ c₃ : Cfg6}
    (h₁ : c₁ [tm372]⊢ c₂) (h₂ : c₂ [tm372]⊢* c₃) : c₁ [tm372]⊢* c₃ :=
  stepPlus_to_stepStar (step_stepStar_to_stepPlus h₁ h₂)

theorem sneg_neq (a b : Sym2) (h : seqb a b = false) : b = sneg a := by
  rcases a with ⟨_ | _ | a, ha⟩ <;> rcases b with ⟨_ | _ | b, hb⟩ <;>
    first | omega | rfl | contradiction

theorem seqb_eq (a b : Sym2) (h : seqb a b = true) : a = b :=
  beq_iff_eq.mp h

theorem sneg_sneg (a : Sym2) : sneg (sneg a) = a := by
  rcases a with ⟨_ | _ | a, ha⟩ <;> first | rfl | omega

theorem dot_zadd (a b nu : List Nat) : dot (zadd a b) nu = dot a nu + dot b nu := by
  induction a generalizing b nu with
  | nil => simp [zadd, dot]
  | cons x a ih =>
    cases b with
    | nil => simp [zadd, dot]
    | cons y b =>
      cases nu with
      | nil => simp [zadd, dot]
      | cons z nu =>
        simp only [zadd, dot, ih, Nat.add_mul]
        omega

theorem ev_add (nu : List Nat) (a b : lf) : ev nu (lf_add a b) = ev nu a + ev nu b := by
  simp only [ev, lf_add, dot_zadd]
  omega

theorem ev_S (nu : List Nat) (a : lf) : ev nu (lf_S a) = ev nu a + 1 := by
  simp only [ev, lf_S]
  omega

theorem allz_dot (vs nu : List Nat) (h : allz vs = true) : dot vs nu = 0 := by
  induction vs generalizing nu with
  | nil => cases nu <;> rfl
  | cons v vs ih =>
    simp only [allz, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨rfl, h2⟩
    cases nu with
    | nil => rfl
    | cons x nu => simp [dot, ih nu h2]

theorem all4_dot (vs nu : List Nat) (h : all4 vs = true) : ∃ k, dot vs nu = 4 * k := by
  induction vs generalizing nu with
  | nil =>
    refine ⟨0, ?_⟩
    cases nu <;> rfl
  | cons v vs ih =>
    simp only [all4, List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨h1, h2⟩
    cases nu with
    | nil => exact ⟨0, rfl⟩
    | cons x nu =>
      rcases ih nu h2 with ⟨k, hk⟩
      refine ⟨(v / 4) * x + k, ?_⟩
      simp only [dot, hk]
      have hv : v = 4 * (v / 4) := by omega
      calc v * x + 4 * k = 4 * (v / 4) * x + 4 * k := by rw [← hv]
        _ = 4 * (v / 4 * x + k) := by ring

theorem ev_zero (nu : List Nat) (a : lf) (h : is_zero a = true) : ev nu a = 0 := by
  simp only [is_zero, Bool.and_eq_true, beq_iff_eq] at h
  simp [ev, h.1, allz_dot a.lv nu h.2]

theorem ev_one (nu : List Nat) (a : lf) (h : is_one a = true) : ev nu a = 1 := by
  simp only [is_one, Bool.and_eq_true, beq_iff_eq] at h
  simp [ev, h.1, allz_dot a.lv nu h.2]

theorem ev_pos (nu : List Nat) (a : lf) (h : posb a = true) :
    ev nu a = ev nu ⟨a.lc - 1, a.lv⟩ + 1 := by
  simp only [posb, Bool.not_eq_true', beq_eq_false_iff_ne] at h
  simp only [ev]
  omega

theorem ev_mod4 (nu : List Nat) (a : lf) (h : all4 a.lv = true) :
    ∃ k, ev nu a = a.lc + 4 * k := by
  rcases all4_dot a.lv nu h with ⟨k, hk⟩
  exact ⟨k, by simp [ev, hk]⟩

theorem ev_runs_app (nu : List Nat) (rs1 rs2 : List run) (s : Side6) :
    ev_runs nu (rs1 ++ rs2) s = ev_runs nu rs1 (ev_runs nu rs2 s) := by
  induction rs1 with
  | nil => rfl
  | cons r rs1 ih =>
    rcases r with ⟨b, n⟩
    simp [ev_runs, ih]

theorem pop_runs_spec (nu : List Nat) (sg : Nat →
    Side6) (rs : List run) (t : tl_) (b : Sym2) (s' : sd)
    (h : pop_runs rs t = some (b, s')) :
    ev_runs nu rs (ev_tl sg t) = b >> ev_sd nu sg s' := by
  induction rs generalizing b s' with
  | nil =>
    cases t with
    | T0 =>
      simp only [pop_runs, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact default_unfold
    | TV k => simp [pop_runs] at h
  | cons r rs ih =>
    rcases r with ⟨b0, n⟩
    simp only [pop_runs] at h
    rcases hz : is_zero n
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
      rcases hp : posb n
      · simp [hp] at h
      · simp only [hp, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rcases ho : is_one n
        · simp [ev_sd, ev_runs, ev_pos nu n hp, alt]
        · simp [ev_sd, ev_runs, ev_one nu n ho, alt]
    · simp only [hz, ↓reduceIte] at h
      simp only [ev_runs, ev_zero nu n hz, alt, append_nil]
      exact ih b s' h

theorem pop_spec (nu : List Nat) (sg : Nat → Side6) (s : sd) (b : Sym2) (s' : sd)
    (h : pop s = some (b, s')) : ev_sd nu sg s = b >> ev_sd nu sg s' :=
  pop_runs_spec nu sg s.1 s.2 b s' h

theorem push_spec (nu : List Nat) (sg : Nat → Side6) (w : Sym2) (s : sd) :
    ev_sd nu sg (push w s) = w >> ev_sd nu sg s := by
  rcases s with ⟨_ | ⟨⟨b0, n0⟩, rs⟩, t⟩
  · rfl
  · simp only [push]
    rcases h : seqb w b0
    · simp only [Bool.false_eq_true, ↓reduceIte, ev_sd, ev_runs, ev_S, alt, append_cons,
        ← sneg_neq w b0 h]
    · rfl

def afterb_nat (c : Sym2) (n : Nat) : Sym2 :=
  if n % 2 == 0 then c else sneg c

theorem afterb_nat_S (c : Sym2) (m : Nat) :
    afterb_nat c (m + 1) = afterb_nat (sneg c) m := by
  simp only [afterb_nat]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hm1 : (m + 1) % 2 = 1 := by omega
    simp [hm, hm1]
  · have hm1 : (m + 1) % 2 = 0 := by omega
    simp [hm, hm1, sneg_sneg]

theorem alt_add (c : Sym2) (m k : Nat) :
    alt c (m + k) = alt c m ++ alt (afterb_nat c m) k := by
  induction m generalizing c with
  | zero => simp [alt, afterb_nat]
  | succ m ih =>
    rw [Nat.succ_add, alt, alt, List.cons_append, ih, afterb_nat_S]

theorem afterb_ev (nu : List Nat) (c : Sym2) (n : lf) (h : all4 n.lv = true) :
    afterb c n = afterb_nat c (ev nu n) := by
  rcases ev_mod4 nu n h with ⟨k, hk⟩
  simp only [afterb, afterb_nat, hk]
  have hmod : (n.lc + 4 * k) % 2 = n.lc % 2 := by omega
  rw [hmod]

theorem push_run_spec (nu : List Nat) (sg : Nat → Side6) (c : Sym2) (n : lf) (s : sd)
    (h4 : all4 n.lv = true) :
    ev_sd nu sg (push_run c n s) = alt c (ev nu n) +> ev_sd nu sg s := by
  rcases s with ⟨_ | ⟨⟨b0, n0⟩, rs⟩, t⟩
  · rfl
  · simp only [push_run]
    rcases h : seqb (afterb c n) b0
    · rfl
    · simp only [↓reduceIte, ev_sd, ev_runs, ev_add, alt_add, append_assoc]
      rw [← afterb_ev nu c n h4, seqb_eq _ _ h]

def lastb_nat (c : Sym2) (m : Nat) : Sym2 :=
  if m % 2 == 0 then sneg c else c

theorem lastb_ev (nu : List Nat) (c : Sym2) (n : lf) (h : all4 n.lv = true) :
    lastb c n = lastb_nat c (ev nu n) := by
  rcases ev_mod4 nu n h with ⟨k, hk⟩
  simp only [lastb, lastb_nat, hk]
  have hmod : (n.lc + 4 * k) % 2 = n.lc % 2 := by omega
  rw [hmod]

theorem rev_alt (b : Sym2) (m : Nat) (l : Side6) :
    alt (sneg (lastb_nat b (m + 1))) (m + 1) +> l =
      alt (sneg (lastb_nat (sneg b) m)) m +> (sneg b >> l) := by
  rw [alt_add, append_assoc]
  simp only [alt, append_cons, append_nil, lastb_nat, afterb_nat]
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · have hm1 : (m + 1) % 2 = 1 := by omega
    simp [hm, hm1, sneg_sneg]
  · have hm1 : (m + 1) % 2 = 0 := by omega
    simp [hm, hm1, sneg_sneg]

theorem cR_cases (i : Nat) :
    (i % 4 = 0 ∧ (i + 1) % 4 = 1) ∨
    (i % 4 = 1 ∧ (i + 1) % 4 = 2) ∨
    (i % 4 = 2 ∧ (i + 1) % 4 = 3) ∨
    (i % 4 = 3 ∧ (i + 1) % 4 = 0) := by
  omega

theorem cR_tm (i : Nat) :
    tm372 (cR_st i) (cR_bt i) = some (some (cR_st (i + 1)), ⟨sneg (cR_bt i), .right⟩) := by
  unfold cR_st cR_bt
  rcases cR_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl

theorem cR_bt_S (i : Nat) : cR_bt (i + 1) = sneg (cR_bt i) := by
  unfold cR_bt
  rcases cR_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl

theorem cL_tm (i : Nat) :
    tm372 (cL_st i) (cL_bt i) = some (some (cL_st (i + 1)), ⟨sneg (cL_bt i), .left⟩) := by
  unfold cL_st cL_bt
  rcases cR_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl

theorem cL_bt_S (i : Nat) : cL_bt (i + 1) = sneg (cL_bt i) := by
  unfold cL_bt
  rcases cR_cases i with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> rfl

theorem accR_step (i : Nat) (l X : Side6) :
    (l {{cR_st i}}> (cR_bt i >> X)) [tm372]⊢ ((sneg (cR_bt i) >> l) {{cR_st (i + 1)}}> X) :=
  step_right_R l X (cR_tm i)

theorem accL_step (i : Nat) (r X : Side6) :
    ((cL_bt i >> X) <{{cL_st i}} r) [tm372]⊢ (X <{{cL_st (i + 1)}} (sneg (cL_bt i) >> r)) :=
  step_left_L X r (cL_tm i)

theorem accR (m : Nat) (i : Nat) (l r : Side6) :
    (l {{cR_st i}}> (alt (cR_bt i) m +> r)) [tm372]⊢*
      ((alt (sneg (lastb_nat (cR_bt i) m)) m +> l) {{cR_st (i + m)}}> r) := by
  induction m generalizing i l r with
  | zero =>
    rw [Nat.add_zero]
    exact stepStar_refl tm372 _
  | succ m ih =>
    have hadd : i + (m + 1) = i + 1 + m := by omega
    rw [rev_alt, hadd]
    refine step_stepStar_to_stepStar (accR_step i l (alt (sneg (cR_bt i)) m +> r)) ?_
    have h := ih (i + 1) (sneg (cR_bt i) >> l) r
    rwa [cR_bt_S] at h

theorem accR_S (m i : Nat) (l r : Side6) :
    (l {{cR_st i}}> (alt (cR_bt i) (m + 1) +> r)) [tm372]⊢⁺
      ((alt (sneg (lastb_nat (cR_bt i) (m + 1))) (m + 1) +> l) {{cR_st (i + (m + 1))}}> r) := by
  have hadd : i + (m + 1) = i + 1 + m := by omega
  rw [rev_alt, hadd]
  refine step_stepStar_to_stepPlus (accR_step i l (alt (sneg (cR_bt i)) m +> r)) ?_
  have h := accR m (i + 1) (sneg (cR_bt i) >> l) r
  rwa [cR_bt_S] at h

theorem accL (m : Nat) (i : Nat) (l r : Side6) :
    ((alt (cL_bt i) m +> l) <{{cL_st i}} r) [tm372]⊢*
      (l <{{cL_st (i + m)}} (alt (sneg (lastb_nat (cL_bt i) m)) m +> r)) := by
  induction m generalizing i l r with
  | zero =>
    rw [Nat.add_zero]
    exact stepStar_refl tm372 _
  | succ m ih =>
    have hadd : i + (m + 1) = i + 1 + m := by omega
    rw [rev_alt, hadd]
    refine step_stepStar_to_stepStar (accL_step i r (alt (sneg (cL_bt i)) m +> l)) ?_
    have h := ih (i + 1) l (sneg (cL_bt i) >> r)
    rwa [cL_bt_S] at h

theorem accL_S (m i : Nat) (l r : Side6) :
    ((alt (cL_bt i) (m + 1) +> l) <{{cL_st i}} r) [tm372]⊢⁺
      (l <{{cL_st (i + (m + 1))}} (alt (sneg (lastb_nat (cL_bt i) (m + 1))) (m + 1) +> r)) := by
  have hadd : i + (m + 1) = i + 1 + m := by omega
  rw [rev_alt, hadd]
  refine step_stepStar_to_stepPlus (accL_step i r (alt (sneg (cL_bt i)) m +> l)) ?_
  have h := accL m (i + 1) l (sneg (cL_bt i) >> r)
  rwa [cL_bt_S] at h

theorem single_spec (nu : List Nat) (sg : Nat → Side6) {c c' : cfg}
    (h : single c = some c') : (ev_cfg nu sg c) [tm372]⊢ (ev_cfg nu sg c') := by
  cases c with
  | Rc q l r =>
    simp only [single] at h
    rcases hp : pop r with _ | ⟨s, r'⟩
    · simp [hp] at h
    · simp only [hp] at h
      have hr := pop_spec nu sg r s r' hp
      rcases ht : tm372 q s with _ | ⟨_ | q', ⟨w, _ | _⟩⟩ <;> simp only [ht] at h
      · contradiction
      · contradiction
      · contradiction
      · simp only [Option.some.injEq] at h
        subst h
        simp only [ev_cfg, hr, push_spec]
        exact step_left_R _ _ ht
      · simp only [Option.some.injEq] at h
        subst h
        simp only [ev_cfg, hr, push_spec]
        exact step_right_R _ _ ht
  | Lc q l r =>
    simp only [single] at h
    rcases hp : pop l with _ | ⟨s, l'⟩
    · simp [hp] at h
    · simp only [hp] at h
      have hl := pop_spec nu sg l s l' hp
      rcases ht : tm372 q s with _ | ⟨_ | q', ⟨w, _ | _⟩⟩ <;> simp only [ht] at h
      · contradiction
      · contradiction
      · contradiction
      · simp only [Option.some.injEq] at h
        subst h
        simp only [ev_cfg, hl, push_spec]
        exact step_left_L _ _ ht
      · simp only [Option.some.injEq] at h
        subst h
        simp only [ev_cfg, hl, push_spec]
        exact step_right_L _ _ ht

def Rel (b : Bool) (c c' : Cfg6) : Prop :=
  if b then (c [tm372]⊢⁺ c') else (c [tm372]⊢* c')

theorem Rel_trans (b1 b2 : Bool) {c c' c'' : Cfg6}
    (h1 : Rel b1 c c') (h2 : Rel b2 c' c'') : Rel (b1 || b2) c c'' := by
  cases b1 <;> cases b2 <;> simp only [Rel, Bool.or_false, Bool.or_true, ↓reduceIte,
      Bool.false_eq_true] at *
  · exact stepStar_trans h1 h2
  · exact stepStar_stepPlus_trans h1 h2
  · exact stepPlus_stepStar_trans h1 h2
  · exact stepPlus_trans h1 h2

theorem tag_spec (nu : List Nat) (sg : Nat → Side6) {c c' : cfg} {b : Bool}
    (h : tag (single c) = some (c', b)) : Rel b (ev_cfg nu sg c) (ev_cfg nu sg c') := by
  simp only [tag, Option.map_eq_some_iff, Prod.mk.injEq] at h
  rcases h with ⟨c1, hs, rfl, rfl⟩
  exact step_to_stepPlus (single_spec nu sg hs)

theorem cR_idx_spec (q : Fin 6) (b : Sym2) (i : Nat) (h : cR_idx q b = some i) :
    q = cR_st i ∧ b = cR_bt i := by
  rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases b with ⟨_ | _ | b, hb⟩ <;>
    (try omega) <;>
    dsimp [cR_idx] at h <;>
    (try contradiction) <;>
    (injection h with h; subst h; exact ⟨rfl, rfl⟩)

theorem cL_idx_spec (q : Fin 6) (b : Sym2) (i : Nat) (h : cL_idx q b = some i) :
    q = cL_st i ∧ b = cL_bt i := by
  rcases q with ⟨_ | _ | _ | _ | _ | _ | q, hq⟩ <;>
    rcases b with ⟨_ | _ | b, hb⟩ <;>
    (try omega) <;>
    dsimp [cL_idx] at h <;>
    (try contradiction) <;>
    (injection h with h; subst h; exact ⟨rfl, rfl⟩)

theorem cR_st_mod (i k : Nat) : cR_st (i + k % 4) = cR_st (i + k) := by
  unfold cR_st
  have h : (i + k % 4) % 4 = (i + k) % 4 := by omega
  rw [h]

theorem cL_st_mod (i k : Nat) : cL_st (i + k % 4) = cL_st (i + k) := by
  unfold cL_st
  have h : (i + k % 4) % 4 = (i + k) % 4 := by omega
  rw [h]

theorem cR_st_add4 (i a k : Nat) : cR_st (i + (a + 4 * k)) = cR_st (i + a) := by
  unfold cR_st
  have h : (i + (a + 4 * k)) % 4 = (i + a) % 4 := by omega
  rw [h]

theorem cL_st_add4 (i a k : Nat) : cL_st (i + (a + 4 * k)) = cL_st (i + a) := by
  unfold cL_st
  have h : (i + (a + 4 * k)) % 4 = (i + a) % 4 := by omega
  rw [h]

theorem sstep_spec (nu : List Nat) (sg : Nat → Side6) {c c' : cfg} {b : Bool}
    (h : sstep c = some (c', b)) : Rel b (ev_cfg nu sg c) (ev_cfg nu sg c') := by
  rcases c with ⟨q, l, ⟨_ | ⟨⟨b0, n⟩, rs⟩, t⟩⟩ | ⟨q, ⟨_ | ⟨⟨b0, n⟩, ls⟩, t⟩, r⟩
  · exact tag_spec nu sg h
  · simp only [sstep] at h
    rcases hz : is_zero n
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
      rcases hi : cR_idx q b0 with _ | i
      · simp only [hi] at h
        exact tag_spec nu sg h
      · simp only [hi] at h
        rcases h4 : all4 n.lv
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          exact tag_spec nu sg h
        · simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rcases cR_idx_spec q b0 i hi with ⟨rfl, rfl⟩
          simp only [ev_cfg, push_run_spec nu sg _ n l h4, lastb_ev nu _ n h4, cR_st_mod]
          change Rel (posb n) (ev_sd nu sg l {{cR_st i}}> (alt (cR_bt i) (ev nu n) +>
              ev_sd nu sg (rs, t))) _
          rcases ev_mod4 nu n h4 with ⟨k, hk⟩
          have hst : cR_st (i + n.lc) = cR_st (i + ev nu n) := by
            rw [hk, cR_st_add4]
          rw [hst]
          rcases hpos : posb n
          · simp only [Rel, Bool.false_eq_true, ↓reduceIte]
            exact accR (ev nu n) i _ _
          · simp only [Rel, ↓reduceIte]
            simp only [posb, Bool.not_eq_true', beq_eq_false_iff_ne] at hpos
            have hev : ∃ m, ev nu n = m + 1 := ⟨ev nu n - 1, by omega⟩
            rcases hev with ⟨m, hm⟩
            rw [hm]
            exact accR_S m i _ _
    · simp only [hz, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [Rel, Bool.false_eq_true, ↓reduceIte, ev_cfg, ev_sd, ev_runs, ev_zero nu n hz, alt,
          append_nil]
      exact stepStar_refl tm372 _
  · exact tag_spec nu sg h
  · simp only [sstep] at h
    rcases hz : is_zero n
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at h
      rcases hi : cL_idx q b0 with _ | i
      · simp only [hi] at h
        exact tag_spec nu sg h
      · simp only [hi] at h
        rcases h4 : all4 n.lv
        · simp only [h4, Bool.false_eq_true, ↓reduceIte] at h
          exact tag_spec nu sg h
        · simp only [h4, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          rcases cL_idx_spec q b0 i hi with ⟨rfl, rfl⟩
          simp only [ev_cfg, push_run_spec nu sg _ n r h4, lastb_ev nu _ n h4, cL_st_mod]
          change Rel (posb n) ((alt (cL_bt i) (ev nu n) +> ev_sd nu sg (ls,
              t)) <{{cL_st i}} ev_sd nu sg r) _
          rcases ev_mod4 nu n h4 with ⟨k, hk⟩
          have hst : cL_st (i + n.lc) = cL_st (i + ev nu n) := by
            rw [hk, cL_st_add4]
          rw [hst]
          rcases hpos : posb n
          · simp only [Rel, Bool.false_eq_true, ↓reduceIte]
            exact accL (ev nu n) i _ _
          · simp only [Rel, ↓reduceIte]
            simp only [posb, Bool.not_eq_true', beq_eq_false_iff_ne] at hpos
            have hev : ∃ m, ev nu n = m + 1 := ⟨ev nu n - 1, by omega⟩
            rcases hev with ⟨m, hm⟩
            rw [hm]
            exact accL_S m i _ _
    · simp only [hz, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      simp only [Rel, Bool.false_eq_true, ↓reduceIte, ev_cfg, ev_sd, ev_runs, ev_zero nu n hz, alt,
          append_nil]
      exact stepStar_refl tm372 _

theorem dot_strip0 (vs nu : List Nat) : dot (strip0 vs) nu = dot vs nu := by
  induction vs generalizing nu with
  | nil => rfl
  | cons v vs ih =>
    simp only [strip0]
    rcases hs : strip0 vs with _ | ⟨w, ws⟩
    · split_ifs with hv
      · simp only [beq_iff_eq] at hv
        subst hv
        cases nu with
        | nil => rfl
        | cons x nu =>
          simp only [dot, Nat.zero_mul, Nat.zero_add, ← ih nu, hs]
      · cases nu with
        | nil => rfl
        | cons x nu =>
          simp only [dot, ← ih nu, hs]
    · cases nu with
      | nil => rfl
      | cons x nu =>
        simp only [dot, ← ih nu, hs]

theorem listN_eqb_eq {a b : List Nat} (h : listN_eqb a b = true) : a = b := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons y b => contradiction
  | cons x a ih =>
    cases b with
    | nil => contradiction
    | cons y b =>
      simp only [listN_eqb, Bool.and_eq_true, beq_iff_eq] at h
      rw [h.1, ih h.2]

theorem lf_eqb_ev (nu : List Nat) {a b : lf} (h : lf_eqb a b = true) : ev nu a = ev nu b := by
  simp only [lf_eqb, Bool.and_eq_true, beq_iff_eq] at h
  have h2 := listN_eqb_eq h.2
  simp only [ev, h.1, ← dot_strip0 a.lv nu, ← dot_strip0 b.lv nu, h2]

theorem runs_eqb_ev (nu : List Nat) {a b : List run} (s : Side6) (h : runs_eqb a b = true) :
    ev_runs nu a s = ev_runs nu b s := by
  induction a generalizing b with
  | nil =>
    cases b with
    | nil => rfl
    | cons r b => contradiction
  | cons r a ih =>
    rcases r with ⟨x, n⟩
    cases b with
    | nil => contradiction
    | cons r' b =>
      rcases r' with ⟨y, m⟩
      simp only [runs_eqb, Bool.and_eq_true] at h
      rcases h with ⟨⟨h1, h2⟩, h3⟩
      rw [seqb_eq x y h1]
      simp only [ev_runs, lf_eqb_ev nu h2, ih h3]

theorem sd_eqb_ev (nu : List Nat) (sg : Nat → Side6) {a b : sd} (h : sd_eqb a b = true) :
    ev_sd nu sg a = ev_sd nu sg b := by
  rcases a with ⟨ra, ta⟩
  rcases b with ⟨rb, tb⟩
  simp only [sd_eqb, Bool.and_eq_true] at h
  have htb : ta = tb := by
    cases ta <;> cases tb <;> simp only [tl_eqb, beq_iff_eq] at h
    · rfl
    · exact absurd h.2 Bool.false_ne_true
    · exact absurd h.2 Bool.false_ne_true
    · rw [h.2]
  subst htb
  exact runs_eqb_ev nu _ h.1

theorem cfg_eqb_ev (nu : List Nat) (sg : Nat → Side6) {a b : cfg} (h : cfg_eqb a b = true) :
    ev_cfg nu sg a = ev_cfg nu sg b := by
  cases a <;> cases b <;> simp only [cfg_eqb, Bool.and_eq_true,
      beq_iff_eq] at h <;> try contradiction
  · rcases h with ⟨⟨rfl, h2⟩, h3⟩
    simp only [ev_cfg, sd_eqb_ev nu sg h2, sd_eqb_ev nu sg h3]
  · rcases h with ⟨⟨rfl, h2⟩, h3⟩
    simp only [ev_cfg, sd_eqb_ev nu sg h2, sd_eqb_ev nu sg h3]

theorem reachAux_spec (tgt : cfg) (fuel : Nat) (c : cfg) (pr : Bool) (nu : List Nat) (sg : Nat →
    Side6)
    {c0 : Cfg6} (hRel : Rel pr c0 (ev_cfg nu sg c))
    (h : reachAux tgt fuel c pr = true) : c0 [tm372]⊢⁺ (ev_cfg nu sg tgt) := by
  induction fuel generalizing c pr with
  | zero => contradiction
  | succ fuel ih =>
    simp only [reachAux] at h
    rcases hs : sstep c with _ | ⟨c', b⟩
    · simp [hs] at h
    · simp only [hs] at h
      have hStep := sstep_spec nu sg hs
      have hRel' := Rel_trans pr b hRel hStep
      split_ifs at h with heq
      · rw [← cfg_eqb_ev nu sg heq]
        rw [h] at hRel'
        exact hRel'
      · exact ih c' (pr || b) hRel' h

theorem reach_spec {fuel : Nat} {c tgt : cfg} (h : reach fuel c tgt = true)
    (nu : List Nat) (sg : Nat → Side6) : (ev_cfg nu sg c) [tm372]⊢⁺ (ev_cfg nu sg tgt) :=
  reachAux_spec tgt fuel c false nu sg (stepStar_refl tm372 _) h

theorem sstep_ev (nu : List Nat) (sg : Nat → Side6) {c c' : cfg} {b : Bool}
    (h : sstep c = some (c', b)) : (ev_cfg nu sg c) [tm372]⊢* (ev_cfg nu sg c') := by
  have h1 := sstep_spec nu sg h
  cases b
  · exact h1
  · exact stepPlus_to_stepStar h1

theorem urun_spec (k : Nat) (c : cfg) (nu : List Nat) (sg : Nat → Side6) :
    (ev_cfg nu sg c) [tm372]⊢* (ev_cfg nu sg (urun k c)) := by
  induction k generalizing c with
  | zero => exact stepStar_refl tm372 _
  | succ k ih =>
    simp only [urun]
    rcases hs : sstep c with _ | ⟨c', b⟩
    · exact stepStar_refl tm372 _
    · exact stepStar_trans (sstep_ev nu sg hs) (ih c')

abbrev rep {α : Type*} (x : α) (n : Nat) : List α := List.replicate n x

theorem rep_add {α : Type*} (x : α) (n m : Nat) : rep x (n + m) = rep x n ++ rep x m :=
  List.replicate_add n m x

theorem rep_app {α : Type*} (x : α) (n m : Nat) : rep x n ++ rep x m = rep x (n + m) :=
  (List.replicate_add n m x).symm

theorem rep_snoc {α : Type*} (x : α) (n : Nat) (l : List α) :
    rep x n ++ x :: l = rep x (n + 1) ++ l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change x :: (rep x n ++ x :: l) = x :: (rep x (n + 1) ++ l)
    rw [ih]

theorem rep_app_cons {α : Type*} (x : α) (a b : Nat) (l : List α) :
    rep x a ++ (rep x b ++ l) = rep x (a + b) ++ l := by
  rw [← List.append_assoc, rep_app]

-- ============================================================================
-- 4. Chain Blocks & Left-Word Counter (`Sk1Class2_v3.v:662-812`)
-- ============================================================================

def mkruns (b : Sym2) : List lf → List run
  | [] => []
  | n :: ns' => (b, n) :: mkruns (lastb b n) ns'

def vt (c : Nat) : lf := ⟨c, [4, 0, 0, 0]⟩
def vs (c : Nat) : lf := ⟨c, [0, 4, 0, 0]⟩
def va (c : Nat) : lf := ⟨c, [0, 0, 4, 0]⟩
def vl (c : Nat) : lf := ⟨c, [0, 0, 0, 4]⟩

inductive lab where
  | U0 | U1 | U2 | W0 | W1 | D0 | D1 | D2
  deriving DecidableEq

def lens : lab → List lf
  | .U0 => [cn 3, vt 4, vs 4, va 1, vl 2]
  | .U1 => [cn 3, vt 4, vs 4, va 2, vl 1]
  | .U2 => [cn 3, vt 4, vs 4, va 3, vl 0]
  | .W0 => [cn 3, vt 1, vs 6, va 4, vl 0]
  | .W1 => [cn 3, vt 2, vs 5, va 4, vl 0]
  | .D0 => [cn 3, vt 3, vs 4, va 4, vl 0]
  | .D1 => [cn 2, vt 4, vs 4, va 4, vl 0]
  | .D2 => [cn 1, vt 5, vs 4, va 4, vl 0]

def blk (s : lab) : List run := mkruns 0 (lens s)

def rlens : lab → List lf
  | .D0 => [vl 0, va 4, vs 4, vt 3, cn 3]
  | _   => [vl 0, va 3, vs 4, vt 4, cn 3]

def rblk (s : lab) : List run := mkruns 0 (rlens s)

inductive lab1 where
  | P0 | P1 | PD0 | PD1 | PD2
  deriving DecidableEq

def lens1 : lab1 → List lf
  | .P0 => [cn 3, cn 1, cn 3]
  | .P1 => [cn 3, cn 2, cn 2]
  | .PD0 => [cn 3, cn 3, cn 1]
  | .PD1 => [cn 2, cn 4, cn 1]
  | .PD2 => [cn 1, cn 5, cn 1]

def blk1 (s : lab1) : List run := mkruns 0 (lens1 s)
def rblk1 : List run := mkruns 1 [cn 1, cn 3, cn 3]

def stp (p : Bool) : Fin 6 := if p then A else B

def turn : lab → Option (lab × Bool)
  | .U0 => some (.U1, true)
  | .U1 => some (.U2, true)
  | .W0 => some (.W1, true)
  | .W1 => some (.D0, true)
  | .D1 => some (.D0, false)
  | .D2 => some (.D1, false)
  | _ => none

def reset : lab → Bool → Option (lab × Bool)
  | .U2, true => some (.U0, true)
  | .U2, false => some (.W0, true)
  | .D0, false => some (.D2, false)
  | _, _ => none

def turn1 : lab1 → Option (lab1 × Bool)
  | .P0 => some (.P1, true)
  | .P1 => some (.PD0, true)
  | .PD1 => some (.PD0, false)
  | .PD2 => some (.PD1, false)
  | .PD0 => none

def sg2 (L R : Side6) : Nat → Side6
  | 0 => L
  | _ => R

theorem reach_LR (fuel : Nat) (q q' : Fin 6) (l l' : List run) (nu : List Nat) (L R : Side6)
    (h : reach fuel (.Lc q (l, .TV 0) ([], .TV 1)) (.Rc q' (l', .TV 0) ([], .TV 1)) = true) :
    ((ev_runs nu l L) <{{q}} R) [tm372]⊢⁺ ((ev_runs nu l' L) {{q'}}> R) :=
  reach_spec h nu (sg2 L R)

theorem reach_LL (fuel : Nat) (q q' : Fin 6) (l r' : List run) (nu : List Nat) (L R : Side6)
    (h : reach fuel (.Lc q (l, .TV 0) ([], .TV 1)) (.Lc q' ([], .TV 0) (r', .TV 1)) = true) :
    ((ev_runs nu l L) <{{q}} R) [tm372]⊢⁺ (L <{{q'}} (ev_runs nu r' R)) :=
  reach_spec h nu (sg2 L R)

theorem reach_RR (fuel : Nat) (q q' : Fin 6) (r l' : List run) (nu : List Nat) (L R : Side6)
    (h : reach fuel (.Rc q ([], .TV 0) (r, .TV 1)) (.Rc q' (l', .TV 0) ([], .TV 1)) = true) :
    (L {{q}}> (ev_runs nu r R)) [tm372]⊢⁺ ((ev_runs nu l' L) {{q'}}> R) :=
  reach_spec h nu (sg2 L R)

theorem blk_turn_U0 : reach 100 (.Lc D (blk .U0, .TV 0) ([], .TV 1)) (.Rc A (blk .U1, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk_turn_U1 : reach 100 (.Lc D (blk .U1, .TV 0) ([], .TV 1)) (.Rc A (blk .U2, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk_turn_W0 : reach 100 (.Lc D (blk .W0, .TV 0) ([], .TV 1)) (.Rc A (blk .W1, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk_turn_W1 : reach 100 (.Lc D (blk .W1, .TV 0) ([], .TV 1)) (.Rc A (blk .D0, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk_turn_D1 : reach 100 (.Lc D (blk .D1, .TV 0) ([], .TV 1)) (.Rc B (blk .D0, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk_turn_D2 : reach 100 (.Lc D (blk .D2, .TV 0) ([], .TV 1)) (.Rc B (blk .D1, .TV 0) ([],
    .TV 1)) = true := by decide +kernel

theorem blk_turn {s s' : lab} {p : Bool} (nu : List Nat) (L R : Side6)
    (h : turn s = some (s', p)) :
    ((ev_runs nu (blk s) L) <{{D}} R) [tm372]⊢⁺ ((ev_runs nu (blk s') L) {{stp p}}> R) := by
  cases s <;> simp only [turn, Option.some.injEq, Prod.mk.injEq] at h <;> try contradiction
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ nu L R blk_turn_U0
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ nu L R blk_turn_U1
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ nu L R blk_turn_W0
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ nu L R blk_turn_W1
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D B _ _ nu L R blk_turn_D1
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D B _ _ nu L R blk_turn_D2

theorem blk_pass_U2 : reach 100 (.Lc D (blk .U2, .TV 0) ([], .TV 1)) (.Lc D ([], .TV 0) (rblk .U2,
    .TV 1)) = true := by decide +kernel
theorem blk_pass_D0 : reach 100 (.Lc D (blk .D0, .TV 0) ([], .TV 1)) (.Lc D ([], .TV 0) (rblk .D0,
    .TV 1)) = true := by decide +kernel

theorem blk_pass {s : lab} (nu : List Nat) (L R : Side6) (h : turn s = none) :
    ((ev_runs nu (blk s) L) <{{D}} R) [tm372]⊢⁺ (L <{{D}} (ev_runs nu (rblk s) R)) := by
  cases s <;> simp only [turn] at h <;> try contradiction
  · exact reach_LL 100 D D _ _ nu L R blk_pass_U2
  · exact reach_LL 100 D D _ _ nu L R blk_pass_D0

theorem blk_reset_U2_t : reach 100 (.Rc A ([], .TV 0) (rblk .U2, .TV 1)) (.Rc A (blk .U0,
    .TV 0) ([], .TV 1)) = true := by decide +kernel
theorem blk_reset_U2_f : reach 100 (.Rc B ([], .TV 0) (rblk .U2, .TV 1)) (.Rc A (blk .W0,
    .TV 0) ([], .TV 1)) = true := by decide +kernel
theorem blk_reset_D0_f : reach 100 (.Rc B ([], .TV 0) (rblk .D0, .TV 1)) (.Rc B (blk .D2,
    .TV 0) ([], .TV 1)) = true := by decide +kernel

theorem blk_reset {s s' : lab} {p p' : Bool} (nu : List Nat) (L R : Side6)
    (h : reset s p = some (s', p')) :
    (L {{stp p}}> (ev_runs nu (rblk s) R)) [tm372]⊢⁺ ((ev_runs nu (blk s') L) {{stp p'}}> R) := by
  cases s <;> cases p <;> simp only [reset, Option.some.injEq,
      Prod.mk.injEq] at h <;> try contradiction
  · rcases h with ⟨rfl, rfl⟩; exact reach_RR 100 B A _ _ nu L R blk_reset_U2_f
  · rcases h with ⟨rfl, rfl⟩; exact reach_RR 100 A A _ _ nu L R blk_reset_U2_t
  · rcases h with ⟨rfl, rfl⟩; exact reach_RR 100 B B _ _ nu L R blk_reset_D0_f

theorem blk1_turn_P0 : reach 100 (.Lc D (blk1 .P0, .TV 0) ([], .TV 1)) (.Rc A (blk1 .P1, .TV 0) ([],
    .TV 1)) = true := by decide +kernel
theorem blk1_turn_P1 : reach 100 (.Lc D (blk1 .P1, .TV 0) ([], .TV 1)) (.Rc A (blk1 .PD0,
    .TV 0) ([], .TV 1)) = true := by decide +kernel
theorem blk1_turn_PD1 : reach 100 (.Lc D (blk1 .PD1, .TV 0) ([], .TV 1)) (.Rc B (blk1 .PD0,
    .TV 0) ([], .TV 1)) = true := by decide +kernel
theorem blk1_turn_PD2 : reach 100 (.Lc D (blk1 .PD2, .TV 0) ([], .TV 1)) (.Rc B (blk1 .PD1,
    .TV 0) ([], .TV 1)) = true := by decide +kernel

theorem blk1_turn {s s' : lab1} {p : Bool} (L R : Side6) (h : turn1 s = some (s', p)) :
    ((ev_runs [] (blk1 s) L) <{{D}} R) [tm372]⊢⁺ ((ev_runs [] (blk1 s') L) {{stp p}}> R) := by
  cases s <;> simp only [turn1, Option.some.injEq, Prod.mk.injEq] at h <;> try contradiction
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ [] L R blk1_turn_P0
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D A _ _ [] L R blk1_turn_P1
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D B _ _ [] L R blk1_turn_PD1
  · rcases h with ⟨rfl, rfl⟩; exact reach_LR 100 D B _ _ [] L R blk1_turn_PD2

theorem blk1_pass_ok :
    reach 100 (.Lc D (blk1 .PD0, .TV 0) ([], .TV 1)) (.Lc E ([], .TV 0) (rblk1, .TV 1)) = true := by
  decide +kernel

theorem blk1_pass (L R : Side6) :
    ((ev_runs [] (blk1 .PD0) L) <{{D}} R) [tm372]⊢⁺ (L <{{E}} (ev_runs [] rblk1 R)) :=
  reach_LL 100 D E _ _ [] L R blk1_pass_ok

theorem blk1_back_ok :
    reach 100 (.Rc B ([], .TV 0) (rblk1, .TV 1)) (.Rc B (blk1 .PD2, .TV 0) ([], .TV 1)) = true := by
  decide +kernel

theorem blk1_back (L R : Side6) :
    (L {{B}}> (ev_runs [] rblk1 R)) [tm372]⊢⁺ ((ev_runs [] (blk1 .PD2) L) {{B}}> R) :=
  reach_RR 100 B B _ _ [] L R blk1_back_ok

def dgr : Nat → List run
  | 0 => [(0, cn 1), (0, cn 5)]
  | 1 => [(0, cn 2), (1, cn 4)]
  | _ => [(0, cn 3), (0, cn 3)]

def lw (i : Nat) : List run :=
  if i < 81 then
    [(1, cn 3), (1,
        cn 4)] ++ dgr (i % 3) ++ dgr (i / 3 % 3) ++ dgr (i / 9 % 3) ++ dgr (i / 27 % 3) ++ [(0,
        cn 2)]
  else
    [(0, cn 6), (1, cn 4)] ++ dgr 0 ++ dgr 0 ++ dgr 0 ++ dgr 0 ++ [(0, cn 2)]

def LWs (i : Nat) : Side6 := ev_runs [] (lw i) default

theorem reach_T0 (fuel : Nat) (q q' : Fin 6) (l l' : List run) (Y : Side6)
    (h : reach fuel (.Lc q (l, .T0) ([], .TV 0)) (.Rc q' (l', .T0) ([], .TV 0)) = true) :
    ((ev_runs [] l default) <{{q}} Y) [tm372]⊢⁺ ((ev_runs [] l' default) {{q'}}> Y) :=
  reach_spec h [] (fun _ => Y)

def lw_ok (i : Nat) : Bool :=
  reach 300 (.Lc E (lw i, .T0) ([], .TV 0)) (.Rc B (lw (i + 1), .T0) ([], .TV 0))

theorem lw_all : (List.range 81).all lw_ok = true := by
  decide +kernel

theorem lw_ok_lt {i : Nat} (hi : i < 81) : lw_ok i = true := by
  have h := List.all_eq_true.mp lw_all i (List.mem_range.mpr hi)
  exact h

theorem lw_ep {i : Nat} (Y : Side6) (hi : i < 81) :
    (LWs i <{{E}} Y) [tm372]⊢⁺ (LWs (i + 1) {{B}}> Y) :=
  reach_T0 300 E B (lw i) (lw (i + 1)) Y (lw_ok_lt hi)

-- ============================================================================
-- 5. Chain Visits & Lemma T (`Sk1Class2_v3.v:818-1362`)
-- ============================================================================

def chs : List lab → List (List Nat) → Side6 → Side6
  | s :: ls', nu :: nus', L => ev_runs nu (blk s) (chs ls' nus' L)
  | _, _, L => L

def rchs : List lab → List (List Nat) → Side6 → Side6
  | s :: ls', nu :: nus', R => rchs ls' nus' (ev_runs nu (rblk s) R)
  | _, _, R => R

def visit3 : List lab → Option (List lab × Bool)
  | [] => none
  | s :: ls' =>
    match turn s with
    | some (s', p) => some (s' :: ls', p)
    | none =>
      match visit3 ls' with
      | some (ls'', p') =>
        match reset s p' with
        | some (s'', p'') => some (s'' :: ls'', p'')
        | none => none
      | none => none

def cb : List lab → Bool → Option (List lab × Bool)
  | [], p => some ([], p)
  | s :: ls', p =>
    match cb ls' p with
    | some (ls'', p') =>
      match reset s p' with
      | some (s'', p'') => some (s'' :: ls'', p'')
      | none => none
    | none => none

def fullb (s : lab) : Bool := (turn s).isNone

theorem visit3_spec (ls : List lab) : ∀ (ls' : List lab) (p : Bool) (nus : List (List Nat)) (L R :
    Side6),
    visit3 ls = some (ls', p) → ls.length = nus.length →
    ((chs ls nus L) <{{D}} R) [tm372]⊢⁺ ((chs ls' nus L) {{stp p}}> R) := by
  induction ls with
  | nil => intros; contradiction
  | cons s ls ih =>
    intro ls' p nus L R h hl
    cases nus with
    | nil => contradiction
    | cons nu nus =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [visit3] at h
      rcases ht : turn s with _ | ⟨s1, p1⟩
      · simp only [ht] at h
        rcases hv : visit3 ls with _ | ⟨ls1, p1⟩
        · simp [hv] at h
        · simp only [hv] at h
          rcases hr : reset s p1 with _ | ⟨s2, p2⟩
          · simp [hr] at h
          · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp only [chs]
            exact stepPlus_trans (blk_pass nu _ R ht)
              (stepPlus_trans (ih ls1 p1 nus L _ hv hl) (blk_reset nu _ R hr))
      · simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        exact blk_turn nu _ R ht

theorem pass_spec (ls : List lab) : ∀ (nus : List (List Nat)) (L R : Side6),
    ls.all fullb = true → ls.length = nus.length →
    ((chs ls nus L) <{{D}} R) [tm372]⊢* (L <{{D}} (rchs ls nus R)) := by
  induction ls with
  | nil =>
    intro nus L R _ hl
    cases nus with
    | nil => exact stepStar_refl tm372 _
    | cons _ _ => contradiction
  | cons s ls ih =>
    intro nus L R h hl
    cases nus with
    | nil => contradiction
    | cons nu nus =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [List.all_cons, Bool.and_eq_true] at h
      rcases h with ⟨h1, h2⟩
      have ht : turn s = none := Option.isNone_iff_eq_none.mp h1
      exact stepStar_trans (stepPlus_to_stepStar (blk_pass nu _ R ht)) (ih nus L _ h2 hl)

theorem cb_spec (ls : List lab) : ∀ (p : Bool) (ls' : List lab) (p' : Bool) (nus : List (List Nat))
    (L R : Side6),
    cb ls p = some (ls', p') → ls.length = nus.length →
    (L {{stp p}}> (rchs ls nus R)) [tm372]⊢* ((chs ls' nus L) {{stp p'}}> R) := by
  induction ls with
  | nil =>
    intro p ls' p' nus L R h hl
    cases nus with
    | nil =>
      simp only [cb, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact stepStar_refl tm372 _
    | cons _ _ => contradiction
  | cons s ls ih =>
    intro p ls' p' nus L R h hl
    cases nus with
    | nil => contradiction
    | cons nu nus =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [cb] at h
      rcases hc : cb ls p with _ | ⟨ls1, p1⟩
      · simp [hc] at h
      · simp only [hc] at h
        rcases hr : reset s p1 with _ | ⟨s2, p2⟩
        · simp [hr] at h
        · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact stepStar_trans (ih p ls1 p1 nus L _ hc hl)
            (stepPlus_to_stepStar (blk_reset nu _ R hr))

theorem visit3_len (ls : List lab) : ∀ (ls' : List lab) (p : Bool),
    visit3 ls = some (ls', p) → ls'.length = ls.length := by
  induction ls with
  | nil => intros; contradiction
  | cons s ls ih =>
    intro ls' p h
    simp only [visit3] at h
    rcases ht : turn s with _ | ⟨s1, p1⟩
    · simp only [ht] at h
      rcases hv : visit3 ls with _ | ⟨ls1, p1⟩
      · simp [hv] at h
      · simp only [hv] at h
        rcases hr : reset s p1 with _ | ⟨s2, p2⟩
        · simp [hr] at h
        · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [ih ls1 p1 hv]
    · simp only [ht, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

theorem cb_len (ls : List lab) : ∀ (p : Bool) (ls' : List lab) (p' : Bool),
    cb ls p = some (ls', p') → ls'.length = ls.length := by
  induction ls with
  | nil =>
    intro p ls' p' h
    simp only [cb, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | cons s ls ih =>
    intro p ls' p' h
    simp only [cb] at h
    rcases hc : cb ls p with _ | ⟨ls1, p1⟩
    · simp [hc] at h
    · simp only [hc] at h
      rcases hr : reset s p1 with _ | ⟨s2, p2⟩
      · simp [hr] at h
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp [ih p ls1 p1 hc]

abbrev vst := List lab × lab1 × Nat

def vis : vst → Option (vst × Bool)
  | (ls, b, i) =>
    match visit3 ls with
    | some (ls', p) => some ((ls', b, i), p)
    | none =>
      if ls.all fullb then
        match turn1 b with
        | some (b', p1) =>
          match cb ls p1 with
          | some (ls', p) => some ((ls', b', i), p)
          | none => none
        | none =>
          if b == .PD0 && i < 80 then
            match cb ls false with
            | some (ls', p) => some ((ls', .PD2, i + 1), p)
            | none => none
          else none
      else none

def b1s (b : lab1) (X : Side6) : Side6 := ev_runs [] (blk1 b) X

def Gc (st : vst) (nus : List (List Nat)) (R : Side6) : Cfg6 :=
  let (ls, b, i) := st
  (chs ls nus (b1s b (LWs i))) <{{D}} R

def Gx (st : vst) (nus : List (List Nat)) (p : Bool) (R : Side6) : Cfg6 :=
  let (ls, b, i) := st
  (chs ls nus (b1s b (LWs i))) {{stp p}}> R

def vlen (st : vst) : Nat := st.1.length

theorem vis_spec {st st' : vst} {p : Bool} (nus : List (List Nat)) (R : Side6)
    (h : vis st = some (st', p)) (hl : vlen st = nus.length) :
    ((Gc st nus R) [tm372]⊢⁺ (Gx st' nus p R)) ∧ vlen st' = vlen st := by
  rcases st with ⟨ls, b, i⟩
  simp only [vis, vlen] at h hl ⊢
  rcases hv : visit3 ls with _ | ⟨ls1, p1⟩
  · simp only [hv] at h
    rcases hf : ls.all fullb
    · simp [hf] at h
    · simp only [hf, ↓reduceIte] at h
      rcases ht : turn1 b with _ | ⟨b1, p1⟩
      · simp only [ht] at h
        rcases hb : (b == .PD0 && decide (i < 80))
        · simp [hb] at h
        · simp only [hb, ↓reduceIte] at h
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hb
          rcases hb with ⟨rfl, hi⟩
          rcases hc : cb ls false with _ | ⟨ls1, p2⟩
          · simp [hc] at h
          · simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            refine ⟨?_, cb_len ls false ls1 _ hc⟩
            have hpass := pass_spec ls nus (b1s .PD0 (LWs i)) R hf hl
            have h1 := blk1_pass (LWs i) (rchs ls nus R)
            have h2 := lw_ep (ev_runs [] rblk1 (rchs ls nus R)) (by omega : i < 81)
            have h3 := blk1_back (LWs (i + 1)) (rchs ls nus R)
            have h4 := cb_spec ls false ls1 _ nus (b1s .PD2 (LWs (i + 1))) R hc hl
            exact stepStar_stepPlus_trans hpass
              (stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_stepStar_trans h3 h4)))
      · simp only [ht] at h
        rcases hc : cb ls p1 with _ | ⟨ls1, p2⟩
        · simp [hc] at h
        · simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          refine ⟨?_, cb_len ls p1 ls1 _ hc⟩
          have hpass := pass_spec ls nus (b1s b (LWs i)) R hf hl
          have h1 := blk1_turn (LWs i) (rchs ls nus R) ht
          have h2 := cb_spec ls p1 ls1 _ nus (b1s b1 (LWs i)) R hc hl
          exact stepStar_stepPlus_trans hpass (stepPlus_stepStar_trans h1 h2)
  · simp only [hv, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨visit3_spec ls ls1 _ nus _ R hv hl, visit3_len ls ls1 _ hv⟩

def Ep (p : Bool) (R R' : Side6) : Prop :=
  ∀ l, (l {{stp p}}> R) [tm372]⊢* (l <{{D}} R')

def EpSeq : List Bool → Side6 → Side6 → Prop
  | [], R, R' => R = R'
  | p :: ps', R, R' => ∃ R1, Ep p R R1 ∧ EpSeq ps' R1 R'

def runv : Nat → vst → Option (vst × List Bool)
  | 0, st => some (st, [])
  | n' + 1, st =>
    match vis st with
    | some (st1, p) =>
      match runv n' st1 with
      | some (st2, ps) => some (st2, p :: ps)
      | none => none
    | none => none

theorem runv_spec (n : Nat) : ∀ (st st' : vst) (ps : List Bool) (nus : List (List Nat)) (R R' :
    Side6),
    runv n st = some (st', ps) → vlen st = nus.length → EpSeq ps R R' →
    (Gc st nus R) [tm372]⊢* (Gc st' nus R') := by
  induction n with
  | zero =>
    intro st st' ps nus R R' h _ he
    simp only [runv, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    simp only [EpSeq] at he
    subst he
    exact stepStar_refl tm372 _
  | succ n ih =>
    intro st st' ps nus R R' h hl he
    simp only [runv] at h
    rcases hv : vis st with _ | ⟨st1, p⟩
    · simp [hv] at h
    · simp only [hv] at h
      rcases hr : runv n st1 with _ | ⟨st2, ps2⟩
      · simp [hr] at h
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        rcases he with ⟨R1, he1, he2⟩
        rcases vis_spec nus R hv hl with ⟨h1, h2⟩
        have hGx : (Gx st1 nus p R) [tm372]⊢* (Gc st1 nus R1) := by
          rcases st1 with ⟨ls1, b1, i1⟩
          exact he1 _
        exact stepStar_trans (stepPlus_to_stepStar h1)
          (stepStar_trans hGx (ih st1 _ ps2 nus R1 R' hr (h2.trans hl) he2))

theorem runv_add (a : Nat) : ∀ (b : Nat) (st st1 : vst) (ps1 : List Bool) (st2 : vst) (ps2 : List
    Bool),
    runv a st = some (st1, ps1) → runv b st1 = some (st2, ps2) →
    runv (a + b) st = some (st2, ps1 ++ ps2) := by
  induction a with
  | zero =>
    intro b st st1 ps1 st2 ps2 h1 h2
    simp only [runv, Option.some.injEq, Prod.mk.injEq] at h1
    rcases h1 with ⟨rfl, rfl⟩
    simpa using h2
  | succ a ih =>
    intro b st st1 ps1 st2 ps2 h1 h2
    rw [Nat.succ_add]
    simp only [runv] at h1 ⊢
    rcases hv : vis st with _ | ⟨st0, p⟩
    · simp [hv] at h1
    · simp only [hv] at h1 ⊢
      rcases hr : runv a st0 with _ | ⟨st3, ps3⟩
      · simp [hr] at h1
      · simp only [hr, Option.some.injEq, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        rw [ih b st0 _ ps3 st2 ps2 hr h2]
        rfl

theorem runv_one {st st' : vst} {p : Bool} (h : vis st = some (st', p)) :
    runv 1 st = some (st', [p]) := by
  simp [runv, h]

theorem vis3 {ls ls' : List lab} {p : Bool} (b : lab1) (i : Nat) (h : visit3 ls = some (ls', p)) :
    vis (ls, b, i) = some ((ls', b, i), p) := by
  simp [vis, h]

theorem pow3_pos (j : Nat) : 1 ≤ 3 ^ j :=
  Nat.one_le_pow j 3 (by omega)

theorem visit3_U2 (j : Nat) {X X' : List lab} (h : visit3 X = some (X', true)) :
    visit3 (rep .U2 j ++ X) = some (rep .U0 j ++ X', true) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    change visit3 (.U2 :: (rep .U2 j ++ X)) = some (.U0 :: (rep .U0 j ++ X'), true)
    simp [visit3, turn, ih, reset]

theorem cb_U2 (j : Nat) {X : List lab} {p : Bool} {X' : List lab} (h : cb X p = some (X', true)) :
    cb (rep .U2 j ++ X) p = some (rep .U0 j ++ X', true) := by
  induction j with
  | zero => exact h
  | succ j ih =>
    change cb (.U2 :: (rep .U2 j ++ X)) p = some (.U0 :: (rep .U0 j ++ X'), true)
    simp [cb, ih, reset]

theorem visit3_full (ls : List lab) (h : ls.all fullb = true) : visit3 ls = none := by
  induction ls with
  | nil => rfl
  | cons s ls ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ht : turn s = none := Option.isNone_iff_eq_none.mp h.1
    simp [visit3, ht, ih h.2]

theorem fullb_U2 (j : Nat) : (rep .U2 j).all fullb = true := by
  induction j with
  | zero => rfl
  | succ j ih => simp [rep, List.replicate_succ, fullb, turn, ih]

theorem fullb_D0 (j : Nat) : (rep .D0 j).all fullb = true := by
  induction j with
  | zero => rfl
  | succ j ih => simp [rep, List.replicate_succ, fullb, turn, ih]

theorem fullb_app {a b : List lab} (ha : a.all fullb = true) (hb : b.all fullb = true) :
    (a ++ b).all fullb = true := by
  simp [List.all_append, ha, hb]

theorem CU (j : Nat) : ∀ (rest : List lab) (b : lab1) (i : Nat),
    runv (3 ^ j - 1) (rep .U0 j ++ rest, b, i) =
      some ((rep .U2 j ++ rest, b, i), rep true (3 ^ j - 1)) := by
  induction j with
  | zero => intros; rfl
  | succ j ih =>
    intro rest b i
    have hp := pow3_pos j
    rw [← rep_snoc .U0 j rest, ← rep_snoc .U2 j rest]
    have h1 := ih (.U0 :: rest) b i
    have h2 : runv 1 (rep .U2 j ++ .U0 :: rest, b, i) = some ((rep .U0 j ++ .U1 :: rest, b, i),
        rep true 1) :=
      runv_one (vis3 b i (visit3_U2 j rfl))
    have h3 := ih (.U1 :: rest) b i
    have h4 : runv 1 (rep .U2 j ++ .U1 :: rest, b, i) = some ((rep .U0 j ++ .U2 :: rest, b, i),
        rep true 1) :=
      runv_one (vis3 b i (visit3_U2 j rfl))
    have h5 := ih (.U2 :: rest) b i
    have h45 := runv_add _ _ _ _ _ _ _ h4 h5
    have h35 := runv_add _ _ _ _ _ _ _ h3 h45
    have h25 := runv_add _ _ _ _ _ _ _ h2 h35
    have h := runv_add _ _ _ _ _ _ _ h1 h25
    rw [rep_app, rep_app, rep_app, rep_app] at h
    have heq : 3 ^ (j + 1) - 1 = (3 ^ j - 1) + (1 + ((3 ^ j - 1) + (1 + (3 ^ j - 1)))) := by
      rw [Nat.pow_succ]; omega
    rwa [heq]

theorem CW (j : Nat) (rest : List lab) (b : lab1) (i : Nat) :
    runv (3 ^ (j + 1) - 1) (rep .U0 j ++ .W0 :: rest, b, i) =
      some ((rep .U2 j ++ .D0 :: rest, b, i), rep true (3 ^ (j + 1) - 1)) := by
  have hp := pow3_pos j
  have h1 := CU j (.W0 :: rest) b i
  have h2 : runv 1 (rep .U2 j ++ .W0 :: rest, b, i) = some ((rep .U0 j ++ .W1 :: rest, b, i),
      rep true 1) :=
    runv_one (vis3 b i (visit3_U2 j rfl))
  have h3 := CU j (.W1 :: rest) b i
  have h4 : runv 1 (rep .U2 j ++ .W1 :: rest, b, i) = some ((rep .U0 j ++ .D0 :: rest, b, i),
      rep true 1) :=
    runv_one (vis3 b i (visit3_U2 j rfl))
  have h5 := CU j (.D0 :: rest) b i
  have h45 := runv_add _ _ _ _ _ _ _ h4 h5
  have h35 := runv_add _ _ _ _ _ _ _ h3 h45
  have h25 := runv_add _ _ _ _ _ _ _ h2 h35
  have h := runv_add _ _ _ _ _ _ _ h1 h25
  rw [rep_app, rep_app, rep_app, rep_app] at h
  have heq : 3 ^ (j + 1) - 1 = (3 ^ j - 1) + (1 + ((3 ^ j - 1) + (1 + (3 ^ j - 1)))) := by
    rw [Nat.pow_succ]; omega
  rwa [heq]

def tc : Nat → Nat
  | 0 => 0
  | 1 => 2
  | j' + 2 => 3 ^ (j' + 2) + tc (j' + 1)

theorem tc_closed (j : Nat) : 2 * tc (j + 1) + 5 = 3 ^ (j + 2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change 2 * (3 ^ (j + 2) + tc (j + 1)) + 5 = 3 ^ (j + 2) * 3
    omega

theorem S3 (j : Nat) : ∀ (d d' : lab) (rest : List lab) (b : lab1) (i : Nat),
    turn d = some (d', false) →
    runv (tc (j + 1) + 1) (rep .U0 j ++ .W0 :: d :: rest, b, i) =
      some ((.D2 :: (rep .D1 j ++ d' :: rest), b, i), rep true (tc (j + 1)) ++ [false]) := by
  induction j with
  | zero =>
    intro d d' rest b i hd
    have h1 := CW 0 (d :: rest) b i
    have h2 : runv 1 (rep .U2 0 ++ .D0 :: d :: rest, b, i) = some ((.D2 :: d' :: rest, b, i),
        [false]) := by
      apply runv_one
      apply vis3
      have ht0 : turn .D0 = none := rfl
      simp only [rep, List.replicate_zero, List.nil_append, visit3, ht0, hd, reset]
    exact runv_add _ _ _ _ _ _ _ h1 h2
  | succ j ih =>
    intro d d' rest b i hd
    have hp := pow3_pos (j + 2)
    have h1 := CW (j + 1) (d :: rest) b i
    have h2 : runv 1 (rep .U2 (j + 1) ++ .D0 :: d :: rest, b, i) =
        some ((rep .U0 j ++ .W0 :: .D2 :: d' :: rest, b, i), rep true 1) := by
      apply runv_one
      apply vis3
      rw [← rep_snoc]
      refine visit3_U2 j ?_
      have ht0 : turn .D0 = none := rfl
      have htu2 : turn .U2 = none := rfl
      simp only [visit3, ht0, htu2, hd, reset]
    have h3 := ih .D2 .D1 (d' :: rest) b i rfl
    have h23 := runv_add _ _ _ _ _ _ _ h2 h3
    have h := runv_add _ _ _ _ _ _ _ h1 h23
    rw [rep_snoc, ← List.append_assoc, rep_app, ← List.append_assoc, rep_app] at h
    change runv (3 ^ (j + 2) + tc (j + 1) + 1) _ =
      some ((.D2 :: (rep .D1 (j + 1) ++ d' :: rest), b, i),
          rep true (3 ^ (j + 2) + tc (j + 1)) ++ [false])
    have heq1 : 3 ^ (j + 2) + tc (j + 1) + 1 = (3 ^ (j + 2) - 1) + (1 + (tc (j + 1) + 1)) := by
      omega
    have heq2 : 3 ^ (j + 2) + tc (j + 1) = 3 ^ (j + 2) - 1 + 1 + tc (j + 1) := by omega
    rw [heq1, heq2]
    exact h

def isD : lab → Bool
  | .D0 | .D1 | .D2 => true
  | _ => false

def dv : lab → Nat
  | .D1 => 1
  | .D0 => 2
  | _ => 0

def dval : List lab → Nat
  | [] => 0
  | s :: ls' => dv s + 3 * dval ls'

def dv1 : lab1 → Nat
  | .PD1 => 1
  | .PD0 => 2
  | _ => 0

def isD1 : lab1 → Bool
  | .PD0 | .PD1 | .PD2 => true
  | _ => false

theorem dval_lt (ls : List lab) (h : ls.all isD = true) : dval ls < 3 ^ ls.length := by
  induction ls with
  | nil => decide
  | cons s ls ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hlt := ih h.2
    cases s <;> simp only [isD, dval, dv, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
        false_and, true_and] at h ⊢ <;> try contradiction
    all_goals omega

theorem dval_max (ls : List lab) (h : ls.all isD = true) (he : dval ls + 1 = 3 ^ ls.length) :
    ls = rep .D0 ls.length := by
  induction ls with
  | nil => rfl
  | cons s ls ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hlt := dval_lt ls h.2
    cases s <;> simp only [isD, dval, dv, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
        false_and, true_and] at h he ⊢ <;> try contradiction
    · change .D0 :: ls = .D0 :: rep .D0 ls.length
      congr 1
      exact ih h (by omega)
    · omega
    · omega

theorem visit3_D (ls : List lab) (h : ls.all isD = true) (he : dval ls + 1 < 3 ^ ls.length) :
    ∃ ls', visit3 ls = some (ls', false) ∧ ls'.all isD = true ∧ dval ls' = dval ls + 1 ∧
      ls'.length = ls.length := by
  induction ls with
  | nil => simp [dval] at he
  | cons s ls ih =>
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hlt := dval_lt ls h.2
    cases s <;> simp only [isD, dval, dv, List.length_cons, Nat.pow_succ, Bool.false_eq_true,
        false_and, true_and] at h he ⊢ <;> try contradiction
    · rcases ih h (by omega) with ⟨ls', e1, e2, e3, e4⟩
      refine ⟨.D2 :: ls', ?_, ?_, ?_, ?_⟩
      · have ht0 : turn .D0 = none := rfl
        simp [visit3, ht0, e1, reset]
      · simp [isD, e2]
      · simp only [dval, dv, e3]; omega
      · simp [e4]
    · refine ⟨.D0 :: ls, rfl, ?_, ?_, rfl⟩
      · simp [isD, h]
      · simp only [dval, dv]; omega
    · refine ⟨.D1 :: ls, rfl, ?_, ?_, rfl⟩
      · simp [isD, h]
      · simp only [dval, dv]; omega

theorem cb_D0 (j : Nat) : cb (rep .D0 j) false = some (rep .D2 j, false) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change cb (.D0 :: rep .D0 j) false = some (.D2 :: rep .D2 j, false)
    simp [cb, ih, reset]

theorem isD_D2 (j : Nat) : (rep .D2 j).all isD = true := by
  induction j with
  | zero => rfl
  | succ j ih => simp [rep, List.replicate_succ, isD, ih]

theorem dval_D2 (j : Nat) : dval (rep .D2 j) = 0 := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change dv .D2 + 3 * dval (rep .D2 j) = 0
    simp [dv, ih]

theorem dval_D1 (j : Nat) : 2 * dval (rep .D1 j) + 1 = 3 ^ j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    change 2 * (dv .D1 + 3 * dval (rep .D1 j)) + 1 = 3 ^ (j + 1)
    rw [Nat.pow_succ]
    simp only [dv]
    omega

theorem vis_b1 {ls : List lab} {b b' : lab1} {p1 : Bool} {ls' : List lab} {p : Bool} (i : Nat)
    (h1 : ls.all fullb = true) (h2 : turn1 b = some (b', p1)) (h3 : cb ls p1 = some (ls', p)) :
    vis (ls, b, i) = some ((ls', b', i), p) := by
  simp [vis, visit3_full ls h1, h1, h2, h3]

theorem vis_co {ls ls' : List lab} {p : Bool} {i : Nat}
    (h1 : ls.all fullb = true) (h2 : i < 80) (h3 : cb ls false = some (ls', p)) :
    vis (ls, .PD0, i) = some ((ls', .PD2, i + 1), p) := by
  simp [vis, visit3_full ls h1, h1, turn1, h2, h3]

theorem allD (n : Nat) : ∀ (ls : List lab) (b : lab1) (i : Nat),
    ls.all isD = true → isD1 b = true →
    dval ls + 3 ^ ls.length * dv1 b + n + 1 = 3 ^ (ls.length + 1) →
    runv n (ls, b, i) = some ((rep .D0 ls.length, .PD0, i), rep false n) := by
  induction n with
  | zero =>
    intro ls b i h1 h2 he
    have hl := dval_lt ls h1
    rw [Nat.pow_succ] at he
    cases b <;> simp only [isD1, dv1] at h2 he <;> try contradiction
    · rw [← dval_max ls h1 (by omega)]
      rfl
    · omega
    · omega
  | succ n ih =>
    intro ls b i h1 h2 he
    have hl := dval_lt ls h1
    rw [Nat.pow_succ] at he
    by_cases hlt : dval ls + 1 < 3 ^ ls.length
    · rcases visit3_D ls h1 hlt with ⟨ls', e1, e2, e3, e4⟩
      simp only [runv, vis3 b i e1]
      have hih := ih ls' b i e2 h2 (by rw [e3, e4, Nat.pow_succ]; omega)
      rw [hih, e4]
      rfl
    · have hd : dval ls + 1 = 3 ^ ls.length := by omega
      have hmax := dval_max ls h1 hd
      set m := ls.length
      cases b <;> simp only [isD1, dv1] at h2 he <;> try contradiction
      · omega
      · have hv : vis (ls, .PD1, i) = some ((rep .D2 m, .PD0, i), false) := by
          rw [hmax]
          exact vis_b1 i (fullb_D0 m) rfl (cb_D0 m)
        simp only [runv, hv]
        have hih := ih (rep .D2 m) .PD0 i (isD_D2 m) rfl
          (by rw [dval_D2, List.length_replicate, Nat.pow_succ]; simp [dv1]; omega)
        rw [hih, List.length_replicate]
        rfl
      · have hv : vis (ls, .PD2, i) = some ((rep .D2 m, .PD1, i), false) := by
          rw [hmax]
          exact vis_b1 i (fullb_D0 m) rfl (cb_D0 m)
        simp only [runv, hv]
        have hih := ih (rep .D2 m) .PD1 i (isD_D2 m) rfl
          (by rw [dval_D2, List.length_replicate, Nat.pow_succ]; simp [dv1]; omega)
        rw [hih, List.length_replicate]
        rfl

theorem cyc (m i : Nat) (hi : i < 80) :
    runv (3 ^ (m + 1)) (rep .D0 m, .PD0, i) =
      some ((rep .D0 m, .PD0, i + 1), rep false (3 ^ (m + 1))) := by
  have hp := pow3_pos (m + 1)
  have heq : 3 ^ (m + 1) = 1 + (3 ^ (m + 1) - 1) := by omega
  rw [heq, rep_add]
  have h1 := runv_one (vis_co (fullb_D0 m) hi (cb_D0 m))
  have hA := allD (3 ^ (m + 1) - 1) (rep .D2 m) .PD2 (i + 1) (isD_D2 m) rfl
  rw [dval_D2, List.length_replicate] at hA
  have h2 := hA (by simp [dv1]; omega)
  exact runv_add _ _ _ _ _ _ _ h1 h2

theorem cycs (c : Nat) : ∀ (m i : Nat), i + c ≤ 80 →
    runv (c * 3 ^ (m + 1)) (rep .D0 m, .PD0, i) =
      some ((rep .D0 m, .PD0, i + c), rep false (c * 3 ^ (m + 1))) := by
  induction c with
  | zero =>
    intro m i _
    simp [runv]
  | succ c ih =>
    intro m i hi
    have hmul : (c + 1) * 3 ^ (m + 1) = 3 ^ (m + 1) + c * 3 ^ (m + 1) := by ring
    rw [hmul, rep_add]
    refine runv_add _ _ _ _ _ _ _ (cyc m i (by omega)) ?_
    have hadd : i + (c + 1) = (i + 1) + c := by omega
    rw [hadd]
    exact ih m (i + 1) (by omega)

theorem odd_pow3 (j : Nat) : ∃ k, 3 ^ j = 2 * k + 1 := by
  induction j with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    rcases ih with ⟨k, hk⟩
    refine ⟨3 * k + 1, ?_⟩
    rw [Nat.pow_succ, hk]
    ring

theorem half9 (j : Nat) : 2 * ((9 * 3 ^ j + 1) / 2) = 9 * 3 ^ j + 1 := by
  rcases odd_pow3 j with ⟨k, hk⟩
  rw [hk]
  omega

theorem interval (m : Nat) (hm : 2 ≤ m) :
    ∃ T, 2 * T + 5 = 3 ^ (m + 2) ∧
      runv (81 * 3 ^ (m + 1) - 1) (rep .U0 m, .P0, 0) =
        some ((rep .D0 m, .PD0, 80), rep true T ++ rep false (81 * 3 ^ (m + 1) - 1 - T)) := by
  rcases m with _ | _ | m
  · omega
  · omega
  · have hh := half9 (m + 1)
    set y := 3 ^ (m + 1)
    have hy : 1 ≤ y := pow3_pos (m + 1)
    have e3 : 3 ^ (m + 2) = 3 * y := by change 3 ^ (m + 1) * 3 = 3 * y; ring
    have e9 : 3 ^ (m + 3) = 9 * y := by change 3 ^ (m + 1) * 3 * 3 = 9 * y; ring
    have etc := tc_closed m
    rw [e3] at etc
    have h1 : runv (3 ^ (m + 3) - 1) (rep .U0 (m + 2), .P0, 0) =
        some ((rep .U2 (m + 2), .PD0, 0), rep true (3 ^ (m + 3) - 1)) := by
      have a1 := CU (m + 2) [] .P0 0
      rw [List.append_nil, List.append_nil] at a1
      have a2 : runv 1 (rep .U2 (m + 2), .P0, 0) = some ((rep .U0 (m + 2), .P1, 0), rep true 1) :=
          by
        refine runv_one (vis_b1 0 (fullb_U2 (m + 2)) rfl ?_)
        have c := cb_U2 (m + 2) (X := []) (p := true) (X' := []) rfl
        rwa [List.append_nil, List.append_nil] at c
      have a3 := CU (m + 2) [] .P1 0
      rw [List.append_nil, List.append_nil] at a3
      have a4 : runv 1 (rep .U2 (m + 2), .P1, 0) = some ((rep .U0 (m + 2), .PD0, 0), rep true 1) :=
          by
        refine runv_one (vis_b1 0 (fullb_U2 (m + 2)) rfl ?_)
        have c := cb_U2 (m + 2) (X := []) (p := true) (X' := []) rfl
        rwa [List.append_nil, List.append_nil] at c
      have a5 := CU (m + 2) [] .PD0 0
      rw [List.append_nil, List.append_nil] at a5
      have a45 := runv_add _ _ _ _ _ _ _ a4 a5
      have a35 := runv_add _ _ _ _ _ _ _ a3 a45
      have a25 := runv_add _ _ _ _ _ _ _ a2 a35
      have a := runv_add _ _ _ _ _ _ _ a1 a25
      rw [rep_app, rep_app, rep_app, rep_app, e3] at a
      rw [e9]
      have heq : 9 * y - 1 = 3 * y - 1 + (1 + (3 * y - 1 + (1 + (3 * y - 1)))) := by omega
      rwa [heq]
    have h2 : runv 1 (rep .U2 (m + 2), .PD0, 0) =
        some ((rep .U0 (m + 1) ++ [.W0], .PD2, 1), rep true 1) := by
      refine runv_one (vis_co (fullb_U2 (m + 2)) (by omega) ?_)
      have hrep : rep lab.U2 (m + 2) = rep lab.U2 (m + 1) ++ [lab.U2] := by
        have h0 := (rep_snoc lab.U2 (m + 1) []).symm
        rwa [List.append_nil] at h0
      rw [hrep]
      exact cb_U2 (m + 1) rfl
    have h3 := CW (m + 1) [] .PD2 1
    have h4 : runv 1 (rep .U2 (m + 1) ++ [.D0], .PD2, 1) =
        some ((rep .U0 m ++ [.W0, .D2], .PD1, 1), rep true 1) := by
      refine runv_one (vis_b1 1 (fullb_app (fullb_U2 (m + 1)) rfl) rfl ?_)
      have hrep : rep lab.U2 (m + 1) ++ [lab.D0] = rep lab.U2 m ++ [lab.U2, lab.D0] := by
        exact (rep_snoc lab.U2 m [lab.D0]).symm
      rw [hrep]
      exact cb_U2 m rfl
    have h5 := S3 m .D2 .D1 [] .PD1 1 rfl
    rw [rep_snoc, List.append_nil] at h5
    have h6 : runv ((9 * y + 1) / 2) (.D2 :: rep .D1 (m + 1), .PD1, 1) =
        some ((rep .D0 (m + 2), .PD0, 1), rep false ((9 * y + 1) / 2)) := by
      have ed := dval_D1 (m + 1)
      have ha := allD ((9 * y + 1) / 2) (.D2 :: rep .D1 (m + 1)) .PD1 1
        (by simp [isD]) rfl
      simp only [List.length_cons, List.length_replicate, dval, dv, dv1] at ha
      apply ha
      rw [e3, e9]
      omega
    have h7 := cycs 79 (m + 2) 1 (by omega)
    rw [e9] at h7
    have h67 := runv_add _ _ _ _ _ _ _ h6 h7
    have h57 := runv_add _ _ _ _ _ _ _ h5 h67
    have h47 := runv_add _ _ _ _ _ _ _ h4 h57
    have h37 := runv_add _ _ _ _ _ _ _ h3 h47
    have h27 := runv_add _ _ _ _ _ _ _ h2 h37
    have h := runv_add _ _ _ _ _ _ _ h1 h27
    change _ = some (_,
        rep true _ ++ (rep true 1 ++ (rep true _ ++ (rep true 1 ++ ((rep true (tc (m + 1)) ++
        rep false 1) ++ (rep false ((9 * y + 1) / 2) ++ rep false (79 * (9 * y)))))))) at h
    rw [rep_app, List.append_assoc, rep_app_cons, rep_app_cons, rep_app_cons, rep_app_cons,
        rep_app] at h
    rw [e3, e9] at h
    have e27 : 3 ^ (m + 4) = 27 * y := by change 3 ^ (m + 1) * 3 * 3 * 3 = 27 * y; ring
    refine ⟨9 * y - 1 + 1 + (3 * y - 1) + 1 + tc (m + 1), ?_, ?_⟩
    · rw [e27]; omega
    · rw [e9]
      have heq1 : 81 * (9 * y) - 1 =
          9 * y - 1 + (1 + (3 * y - 1 + (1 + (tc (m + 1) + 1 + ((9 * y + 1) / 2 + 79 * (9 *
              y)))))) := by omega
      have heq2 : 81 * (9 * y) - 1 - (9 * y - 1 + 1 + (3 * y - 1) + 1 + tc (m + 1)) =
          1 + ((9 * y + 1) / 2 + 79 * (9 * y)) := by omega
      rw [heq2, heq1]
      exact h

theorem interval_tm (m : Nat) (nus : List (List Nat)) (R R' : Side6)
    (hm : 2 ≤ m) (hl : nus.length = m)
    (he : ∀ T, 2 * T + 5 = 3 ^ (m + 2) →
      EpSeq (rep true T ++ rep false (81 * 3 ^ (m + 1) - 1 - T)) R R') :
    (Gc (rep .U0 m, .P0, 0) nus R) [tm372]⊢* (Gc (rep .D0 m, .PD0, 80) nus R') := by
  rcases interval m hm with ⟨T, hT, hr⟩
  exact runv_spec _ _ _ _ nus R R' hr (by simp [vlen, hl]) (he T hT)

theorem record_visit (m : Nat) (nus : List (List Nat)) (R : Side6) (hl : nus.length = m) :
    (Gc (rep .D0 m, .PD0, 80) nus R) [tm372]⊢⁺
      ((chs (rep .D2 m) nus (b1s .PD2 (LWs 81))) {{B}}> R) := by
  have hpass := pass_spec (rep .D0 m) nus (b1s .PD0 (LWs 80)) R (fullb_D0 m) (by simp [hl])
  have h1 := blk1_pass (LWs 80) (rchs (rep .D0 m) nus R)
  have h2 := lw_ep (ev_runs [] rblk1 (rchs (rep .D0 m) nus R)) (by omega : 80 < 81)
  have h3 := blk1_back (LWs 81) (rchs (rep .D0 m) nus R)
  have h4 :=
      cb_spec (rep .D0 m) false (rep .D2 m) false nus (b1s .PD2 (LWs 81)) R (cb_D0 m) (by simp [hl])
  exact stepStar_stepPlus_trans hpass
    (stepPlus_trans h1 (stepPlus_trans h2 (stepPlus_stepStar_trans h3 h4)))

-- ============================================================================
-- 6. Right-Region Executor & Regrouping (`Sk1Class2_v3.v:1400-1832`)
-- ============================================================================

def tgtD : cfg → Option (List run)
  | .Lc 3 ([], .TV 0) (rr, .T0) => some rr
  | _ => none

theorem tgtD_spec {c : cfg} {rr : List run} (h : tgtD c = some rr) :
    c = .Lc D ([], .TV 0) (rr, .T0) := by
  unfold tgtD at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    rfl
  · contradiction

def evR (nu : List Nat) (rr : List run) : Side6 := ev_runs nu rr default

def ep_run (p : Bool) (rr : List run) : Option (List run) :=
  tgtD (urun 500 (.Rc (stp p) ([], .TV 0) (rr, .T0)))

theorem ep_run_spec {p : Bool} {rr rr' : List run} (h : ep_run p rr = some rr') (nu : List Nat) :
    Ep p (evR nu rr) (evR nu rr') := by
  intro l
  have u := urun_spec 500 (.Rc (stp p) ([], .TV 0) (rr, .T0)) nu (fun _ => l)
  rw [tgtD_spec h] at u
  exact u

def eps : List Bool → List run → Option (List run)
  | [], rr => some rr
  | p :: ps', rr =>
    match ep_run p rr with
    | some rr' => eps ps' rr'
    | none => none

theorem eps_spec (ps : List Bool) : ∀ {rr rr' : List run},
    eps ps rr = some rr' → ∀ (nu : List Nat), EpSeq ps (evR nu rr) (evR nu rr') := by
  induction ps with
  | nil =>
    intro rr rr' h nu
    simp only [eps, Option.some.injEq] at h
    subst h; rfl
  | cons p ps ih =>
    intro rr rr' h nu
    simp only [eps] at h
    rcases he : ep_run p rr with _ | r1
    · simp [he] at h
    · simp only [he] at h
      exact ⟨evR nu r1, ep_run_spec he nu, ih h nu⟩

theorem EpSeq_app (a : List Bool) : ∀ (b : List Bool) (R R1 R2 : Side6),
    EpSeq a R R1 → EpSeq b R1 R2 → EpSeq (a ++ b) R R2 := by
  induction a with
  | nil =>
    intro b R R1 R2 h1 h2
    simp only [EpSeq] at h1
    subst h1; exact h2
  | cons p a ih =>
    intro b R R1 R2 h1 h2
    rcases h1 with ⟨R3, h3, h4⟩
    exact ⟨R3, h3, ih b R3 R1 R2 h4 h2⟩

def evN (nu : List Nat) (a : lf) : Nat := a.lc + dot a.lv nu

theorem dot_zadd2 (v : List Nat) : ∀ (a b : List Nat), dot v (zadd a b) = dot v a + dot v b := by
  induction v with
  | nil => intros; rfl
  | cons x v ih =>
    intro a b
    cases a with
    | nil => simp [zadd, dot]
    | cons y a =>
      cases b with
      | nil => simp [zadd, dot]
      | cons z b =>
        simp only [zadd, dot, ih, Nat.mul_add]
        omega

def vscale (k : Nat) (w : List Nat) : List Nat := w.map (k * ·)

theorem dot_vscale (v : List Nat) : ∀ (k : Nat) (w : List Nat), dot v (vscale k w) = k * dot v w :=
    by
  induction v with
  | nil => intros; simp [dot]
  | cons x v ih =>
    intro k w
    cases w with
    | nil => simp [vscale, dot]
    | cons y w =>
      rw [vscale, List.map_cons, dot, dot, ← vscale, ih k w]
      ring

theorem ev_runs_dot (nu nu' : List Nat) (T : List run) (X : Side6)
    (h : ∀ v, dot v nu = dot v nu') : ev_runs nu T X = ev_runs nu' T X := by
  induction T with
  | nil => rfl
  | cons r T ih =>
    rcases r with ⟨b, a⟩
    simp only [ev_runs, ev, h, ih]

def subst_lf (w : List Nat) (a : lf) : lf := ⟨a.lc + dot a.lv w, a.lv⟩
def subst_runs (w : List Nat) (T : List run) : List run := T.map (fun r => (r.1, subst_lf w r.2))

theorem ev_runs_subst (nu w : List Nat) (T : List run) (X : Side6) :
    ev_runs nu (subst_runs w T) X = ev_runs (zadd nu w) T X := by
  induction T with
  | nil => rfl
  | cons r T ih =>
    rcases r with ⟨b, a⟩
    rw [subst_runs, List.map_cons, ← subst_runs, ev_runs, ev_runs, ih]
    congr 1
    simp only [ev, subst_lf, dot_zadd2]
    congr 1
    omega

def lf_scale (k : Nat) (a : lf) : lf := ⟨k * a.lc, a.lv.map (k * ·)⟩

theorem dot_scale_l (vs : List Nat) : ∀ (k : Nat) (nu : List Nat),
    dot (vs.map (k * ·)) nu = k * dot vs nu := by
  induction vs with
  | nil => intros; simp [dot]
  | cons x vs ih =>
    intro k nu
    cases nu with
    | nil => simp [dot]
    | cons y nu =>
      simp only [List.map_cons, dot, ih]
      ring

theorem evN_add (nu : List Nat) (a b : lf) : evN nu (lf_add a b) = evN nu a + evN nu b :=
  ev_add nu a b

theorem evN_scale (nu : List Nat) (k : Nat) (a : lf) : evN nu (lf_scale k a) = k * evN nu a := by
  simp only [evN, lf_scale, dot_scale_l]
  ring

def comp_aux : List Nat → List lf → lf
  | v :: vs', s :: sg' => lf_add (lf_scale v s) (comp_aux vs' sg')
  | _, _ => ⟨0, []⟩

def compose_lf (sg : List lf) (a : lf) : lf := lf_add ⟨a.lc, []⟩ (comp_aux a.lv sg)
def comp_runs (sg : List lf) (T : List run) : List run := T.map (fun r => (r.1, compose_lf sg r.2))

theorem evN_comp_aux (nu : List Nat) (vs : List Nat) : ∀ (sg : List lf),
    evN nu (comp_aux vs sg) = dot vs (sg.map (evN nu)) := by
  induction vs with
  | nil => intro sg; cases sg <;> rfl
  | cons v vs ih =>
    intro sg
    cases sg with
    | nil => rfl
    | cons s sg =>
      simp only [comp_aux, List.map_cons, dot, evN_add, evN_scale, ih]

theorem evN_compose (nu : List Nat) (sg : List lf) (a : lf) :
    evN nu (compose_lf sg a) = evN (sg.map (evN nu)) a := by
  rw [compose_lf, evN_add, evN_comp_aux]
  simp [evN, dot]

theorem ev_runs_comp (nu : List Nat) (sg : List lf) (T : List run) (X : Side6) :
    ev_runs nu (comp_runs sg T) X = ev_runs (sg.map (evN nu)) T X := by
  induction T with
  | nil => rfl
  | cons r T ih =>
    rcases r with ⟨b, a⟩
    rw [comp_runs, List.map_cons, ← comp_runs, ev_runs, ev_runs, ih]
    congr 1
    exact congrArg (alt b) (evN_compose nu sg a)

theorem jump_lemma (T : List run) (p : Bool) (dec inc : List Nat)
    (hc : ∀ nu, EpSeq [p, p, p, p] (evR nu (subst_runs dec T)) (evR nu (subst_runs inc T)))
    (k : Nat) : ∀ (nu : List Nat),
    EpSeq (rep p (4 * k)) (evR (zadd nu (vscale k dec)) T) (evR (zadd nu (vscale k inc)) T) := by
  induction k with
  | zero =>
    intro nu
    simp only [Nat.mul_zero, rep, List.replicate_zero, EpSeq, evR]
    apply ev_runs_dot
    intro v
    simp [dot_zadd2, dot_vscale]
  | succ k ih =>
    intro nu
    have hmul : 4 * (k + 1) = 4 + 4 * k := by omega
    rw [hmul, rep_add]
    refine EpSeq_app (rep p 4) (rep p (4 * k)) _ (evR (zadd (zadd nu inc) (vscale k dec)) T) _ ?_ ?_
    · have h1 := hc (zadd nu (vscale k dec))
      simp only [evR, ev_runs_subst] at h1 ⊢
      have he1 : ev_runs (zadd nu (vscale (k + 1) dec)) T default =
          ev_runs (zadd (zadd nu (vscale k dec)) dec) T default := by
        apply ev_runs_dot; intro v; simp only [dot_zadd2, dot_vscale]; ring
      have he2 : ev_runs (zadd (zadd nu inc) (vscale k dec)) T default =
          ev_runs (zadd (zadd nu (vscale k dec)) inc) T default := by
        apply ev_runs_dot; intro v; simp only [dot_zadd2]; omega
      rw [he1, he2]
      exact h1
    · have h2 := ih (zadd nu inc)
      simp only [evR] at h2 ⊢
      have he3 : ev_runs (zadd nu (vscale (k + 1) inc)) T default =
          ev_runs (zadd (zadd nu inc) (vscale k inc)) T default := by
        apply ev_runs_dot; intro v; simp only [dot_zadd2, dot_vscale]; ring
      rw [he3]
      exact h2

def uvar (i : Nat) (c : Nat) : lf := ⟨c, List.replicate i 0 ++ [4]⟩

def zsub : List Nat → List Nat → List Nat
  | x :: a', y :: b' => (x - y) :: zsub a' b'
  | a, [] => a
  | [], _ => []

def mk_jump (i : Nat) : List run → List run → lf → Option (List run × List Nat × List Nat × List lf)
  | [], [], _ => some ([], [], [], [])
  | (b, a) :: rr', (b4, a4) :: rr4', c =>
    if !seqb b b4 then none
    else if !listN_eqb (strip0 a.lv) (strip0 a4.lv) then none
    else match mk_jump (i + 1) rr' rr4' c with
    | none => none
    | some (T, dec, inc, sg) =>
      if a4.lc < a.lc then
        let diff := a.lc - a4.lc
        if diff % 4 != 0 then none
        else
          let dn := diff / 4
          let M := a.lc - 4 * dn * c.lc
          let s : lf := ⟨0, (zsub a.lv (c.lv.map ((4 * dn) * ·))).map (· / 4)⟩
          some ((b, uvar i M) :: T, dn :: dec, 0 :: inc, s :: sg)
      else
        let diff := a4.lc - a.lc
        if diff % 4 != 0 then none
        else
          let q := diff / 4
          if allz a.lv && q == 0 then
            some ((b, a) :: T, 0 :: dec, 0 :: inc, ⟨0, []⟩ :: sg)
          else
            let s : lf := ⟨0, a.lv.map (· / 4)⟩
            some ((b, uvar i a.lc) :: T, 0 :: dec, q :: inc, s :: sg)
  | _, _, _ => none

def mapadd (c : lf) : List lf → List Nat → List lf
  | s :: sg', x :: w' => lf_add s (lf_scale x c) :: mapadd c sg' w'
  | _, _ => []

theorem mapadd_ev (nu : List Nat) (c : lf) (sg : List lf) : ∀ (w : List Nat),
    sg.length = w.length →
    (mapadd c sg w).map (evN nu) = zadd (sg.map (evN nu)) (vscale (evN nu c) w) := by
  induction sg with
  | nil =>
    intro w hl
    cases w with
    | nil => rfl
    | cons _ _ => contradiction
  | cons s sg ih =>
    intro w hl
    cases w with
    | nil => contradiction
    | cons x w =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      simp only [mapadd, List.map_cons, vscale, zadd, ih w hl, evN_add, evN_scale]
      congr 1
      ring

def cyc4 (p : Bool) : List Bool := [p, p, p, p]

def jump_run (p : Bool) (c : lf) (rr : List run) : Option (List run) :=
  match eps (cyc4 p) rr with
  | none => none
  | some rr4 =>
    match mk_jump 0 rr rr4 c with
    | none => none
    | some (T, dec, inc, sg) =>
      if sg.length == dec.length && sg.length == inc.length then
        match eps (cyc4 p) (subst_runs dec T) with
        | none => none
        | some X =>
          if runs_eqb X (subst_runs inc T) && runs_eqb rr (comp_runs (mapadd c sg dec) T) then
            some (comp_runs (mapadd c sg inc) T)
          else none
      else none

theorem jump_run_spec {p : Bool} {c : lf} {rr rr' : List run}
    (h : jump_run p c rr = some rr') (nu : List Nat) :
    EpSeq (rep p (4 * ev nu c)) (evR nu rr) (evR nu rr') := by
  simp only [jump_run] at h
  rcases h1 : eps (cyc4 p) rr with _ | rr4
  · simp [h1] at h
  · simp only [h1] at h
    rcases h2 : mk_jump 0 rr rr4 c with _ | ⟨T, dec, inc, sg⟩
    · simp [h2] at h
    · simp only [h2] at h
      rcases hl : (sg.length == dec.length && sg.length == inc.length)
      · simp [hl] at h
      · simp only [hl, ↓reduceIte] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at hl
        rcases hl with ⟨hl1, hl2⟩
        rcases hx : eps (cyc4 p) (subst_runs dec T) with _ | X
        · simp [hx] at h
        · simp only [hx] at h
          rcases hc : (runs_eqb X (subst_runs inc T) && runs_eqb rr (comp_runs (mapadd c sg dec) T))
          · simp [hc] at h
          · simp only [hc, ↓reduceIte, Option.some.injEq] at h
            subst h
            simp only [Bool.and_eq_true] at hc
            rcases hc with ⟨hc1, hc2⟩
            have hcyc : ∀ nu', EpSeq [p, p, p,
                p] (evR nu' (subst_runs dec T)) (evR nu' (subst_runs inc T)) := by
              intro nu'
              have hx' := eps_spec (cyc4 p) hx nu'
              simp only [evR, ← runs_eqb_ev nu' default hc1]
              exact hx'
            have hj := jump_lemma T p dec inc hcyc (ev nu c) (sg.map (evN nu))
            simp only [evR, runs_eqb_ev nu default hc2, ev_runs_comp, mapadd_ev nu c sg dec hl1,
              mapadd_ev nu c sg inc hl2]
            exact hj

inductive instr where
  | ISingle (p : Bool)
  | IJump (p : Bool) (c : lf)
  deriving DecidableEq

abbrev seg := Bool × lf

def segs_ev (nu : List Nat) : List seg → List Bool
  | [] => []
  | (p, n) :: ss' => rep p (ev nu n) ++ segs_ev nu ss'

def exec : List instr → List run → Option (List run × List seg)
  | [], rr => some (rr, [])
  | .ISingle p :: prog', rr =>
    match ep_run p rr with
    | some rr1 =>
      match exec prog' rr1 with
      | some (rr2, ss) => some (rr2, (p, cn 1) :: ss)
      | none => none
    | none => none
  | .IJump p c :: prog', rr =>
    match jump_run p c rr with
    | some rr1 =>
      match exec prog' rr1 with
      | some (rr2, ss) => some (rr2, (p, lf_scale 4 c) :: ss)
      | none => none
    | none => none

theorem ev_scale4 (nu : List Nat) (c : lf) : ev nu (lf_scale 4 c) = 4 * ev nu c :=
  evN_scale nu 4 c

theorem exec_spec (prog : List instr) : ∀ {rr rr' : List run} {ss : List seg},
    exec prog rr = some (rr', ss) → ∀ (nu : List Nat),
    EpSeq (segs_ev nu ss) (evR nu rr) (evR nu rr') := by
  induction prog with
  | nil =>
    intro rr rr' ss h nu
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | cons ins prog ih =>
    intro rr rr' ss h nu
    cases ins with
    | ISingle p =>
      simp only [exec] at h
      rcases e1 : ep_run p rr with _ | rr1
      · simp [e1] at h
      · simp only [e1] at h
        rcases e2 : exec prog rr1 with _ | ⟨rr2, ss2⟩
        · simp [e2] at h
        · simp only [e2, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨evR nu rr1, ep_run_spec e1 nu, ih e2 nu⟩
    | IJump p c =>
      simp only [exec] at h
      rcases e1 : jump_run p c rr with _ | rr1
      · simp [e1] at h
      · simp only [e1] at h
        rcases e2 : exec prog rr1 with _ | ⟨rr2, ss2⟩
        · simp [e2] at h
        · simp only [e2, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp only [segs_ev, ev_scale4]
          exact EpSeq_app _ _ _ (evR nu rr1) _ (jump_run_spec e1 nu) (ih e2 nu)

def sum_ph (p : Bool) : List seg → lf
  | [] => ⟨0, []⟩
  | (q, n) :: ss' => if p == q then lf_add n (sum_ph p ss') else sum_ph p ss'

def split_ok : Bool → List seg → Bool
  | _, [] => true
  | seen_false, (true, _) :: ss' => (!seen_false) && split_ok false ss'
  | _, (false, _) :: ss' => split_ok true ss'

theorem split_false (ss : List seg) (nu : List Nat) (h : split_ok true ss = true) :
    segs_ev nu ss = rep false (ev nu (sum_ph false ss)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨_ | _, n⟩
    · simp only [split_ok] at h
      simp only [segs_ev, sum_ph, beq_self_eq_true, ↓reduceIte, ev_add, rep_add, ih h]
    · contradiction

theorem sum_true_of_split_true (ss : List seg) (nu : List Nat) (h : split_ok true ss = true) :
    ev nu (sum_ph true ss) = 0 := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨_ | _, n⟩
    · simp only [split_ok] at h
      exact ih h
    · contradiction

theorem split_spec (ss : List seg) (nu : List Nat) (h : split_ok false ss = true) :
    segs_ev nu ss = rep true (ev nu (sum_ph true ss)) ++ rep false (ev nu (sum_ph false ss)) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    rcases s with ⟨_ | _, n⟩
    · simp only [split_ok] at h
      have htf : (true == false) = false := rfl
      simp only [segs_ev, sum_ph, htf, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, ev_add,
          rep_add,
        split_false ss nu h, sum_true_of_split_true ss nu h, rep, List.replicate_zero,
            List.nil_append]
    · simp only [split_ok, Bool.not_false, Bool.true_and] at h
      have hft : (false == true) = false := rfl
      simp only [segs_ev, sum_ph, hft, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte, ev_add,
          rep_add, ih h, List.append_assoc]

def prog_check (prog : List instr) (rs re : List run) (t_lf f_lf : lf) : Bool :=
  match exec prog rs with
  | some (re', ss) =>
    (runs_eqb re' re && split_ok false ss) && (lf_eqb (sum_ph true ss) t_lf && lf_eqb (sum_ph false
        ss) f_lf)
  | none => false

theorem prog_check_spec {prog : List instr} {rs re : List run} {t_lf f_lf : lf}
    (h : prog_check prog rs re t_lf f_lf = true) (nu : List Nat) :
    EpSeq (rep true (ev nu t_lf) ++ rep false (ev nu f_lf)) (evR nu rs) (evR nu re) := by
  simp only [prog_check] at h
  rcases he : exec prog rs with _ | ⟨re', ss⟩
  · simp [he] at h
  · simp only [he, Bool.and_eq_true] at h
    rcases h with ⟨⟨h1, h3⟩, ⟨h2, h4⟩⟩
    have hex := exec_spec prog he nu
    rw [split_spec ss nu h3, lf_eqb_ev nu h2, lf_eqb_ev nu h4] at hex
    simp only [evR, ← runs_eqb_ev nu default h1]
    exact hex

def rtop (qs : List (List Nat)) (z : Nat) : Nat :=
  match qs with
  | [] => z
  | q :: _ => q.getD 0 0

def rshift : List (List Nat) → Nat → List (List Nat)
  | [], _ => []
  | q :: qs', z => [q.getD 1 0, q.getD 2 0, q.getD 3 0, rtop qs' z] :: rshift qs' z

theorem shift_len (qs : List (List Nat)) (z : Nat) : (rshift qs z).length = qs.length := by
  induction qs with
  | nil => rfl
  | cons q qs ih => simp [rshift, ih]

theorem dot4 (a b c d : Nat) (q : List Nat) :
    dot [a, b, c, d] q = a * q.getD 0 0 + b * q.getD 1 0 + c * q.getD 2 0 + d * q.getD 3 0 := by
  rcases q with _ | ⟨x0, _ | ⟨x1, _ | ⟨x2, _ | ⟨x3, q⟩⟩⟩⟩ <;> simp [dot, List.getD] <;> ring

theorem alt_split (b : Sym2) (m k : Nat) (h : m % 2 = 0) :
    alt b (m + k) = alt b m ++ alt b k := by
  rw [alt_add]
  simp [afterb_nat, h]

theorem regroup (qs : List (List Nat)) : ∀ (z : Nat) (X X' : Side6),
    X = alt 0 1 +> (alt 0 (2 + 4 * z) +> X') →
    chs (rep .D2 qs.length) qs X =
      alt 0 1 +> (alt 0 (2 + 4 * rtop qs z) +> chs (rep .U0 qs.length) (rshift qs z) X') := by
  induction qs with
  | nil =>
    intro z X X' hx
    exact hx
  | cons q qs ih =>
    intro z X X' hx
    simp only [List.length_cons, rep, List.replicate_succ, chs, rshift, rtop]
    rw [ih z X X' hx]
    set Y := chs (List.replicate qs.length .U0) (rshift qs z) X'
    change ev_runs q [(0, cn 1), (0, vt 5), (0, vs 4), (1, va 4), (0, vl 0)]
        (alt 0 1 +> (alt 0 (2 + 4 * rtop qs z) +> Y)) =
      alt 0 1 +> (alt 0 (2 + 4 * q.getD 0 0) +>
        ev_runs [q.getD 1 0, q.getD 2 0, q.getD 3 0, rtop qs z]
          [(0, cn 3), (0, vt 4), (1, vs 4), (0, va 1), (0, vl 2)] Y)
    simp only [ev_runs, ev, vt, vs, va, vl, cn, dot4, dot, List.getD,
      List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    set xt := q[0]?.getD 0
    set xs := q[1]?.getD 0
    set xa := q[2]?.getD 0
    set xI := q[3]?.getD 0
    set tz := rtop qs z
    have e1 : alt 0 (5 + (4 * xt + 0 * xs + 0 * xa + 0 * xI)) = alt 0 (2 + 4 * xt) ++ alt 0 3 := by
      have hadd : 5 + (4 * xt + 0 * xs + 0 * xa + 0 * xI) = (2 + 4 * xt) + 3 := by omega
      rw [hadd]
      exact alt_split 0 (2 + 4 * xt) 3 (by omega)
    have e2 : alt 0 (1 + (0 * xs + 0 * xa + 4 * xI + 0 * tz)) =
        alt 0 (0 + (0 * xt + 0 * xs + 0 * xa + 4 * xI)) ++ alt 0 1 := by
      have hadd : 1 + (0 * xs + 0 * xa + 4 * xI + 0 * tz) =
          (0 + (0 * xt + 0 * xs + 0 * xa + 4 * xI)) + 1 := by omega
      rw [hadd]
      exact alt_split 0 _ 1 (by omega)
    have e3 : 2 + (0 * xs + 0 * xa + 0 * xI + 4 * tz) = 2 + 4 * tz := by omega
    have e4 : 4 + (4 * xs + 0 * xa + 0 * xI + 0 * tz) = 4 + (0 * xt + 4 * xs + 0 * xa + 0 * xI) :=
        by omega
    have e5 : 4 + (0 * xs + 4 * xa + 0 * xI + 0 * tz) = 4 + (0 * xt + 0 * xs + 4 * xa + 0 * xI) :=
        by omega
    have e0 : 3 + 0 = 3 := rfl
    rw [e1, e2, e3, e4, e5, append_assoc, append_assoc]

theorem regroup_b1 : b1s .PD2 (LWs 81) = alt 0 1 +> (alt 0 (2 + 4 * 0) +> b1s .P0 (LWs 0)) := rfl

@[simp] theorem dot_nil (nu : List Nat) : dot [] nu = 0 := by cases nu <;> rfl
@[simp] theorem ev_cn (nu : List Nat) (c : Nat) : ev nu (cn c) = c := by simp [ev, cn]

theorem drop_step (L Re Rs : List run) (nu : List Nat) (X' : Side6)
    (h : reach 500 (.Rc B (L, .TV 0) (Re, .T0)) (.Lc D ([], .TV 0) (Rs, .T0)) = true) :
    ((ev_runs nu L X') {{B}}> (evR nu Re)) [tm372]⊢⁺ (X' <{{D}} (evR nu Rs)) :=
  reach_spec h nu (fun _ => X')

def tl1 (c a : Nat) : lf := ⟨c, [a]⟩

def Rs_r5 : List run :=
    mkruns 0 [tl1 224492 1796256, tl1 673559 5388768, cn 8, tl1 9836 78732, tl1 1942069 15536448]
def prog_r5 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 817 6561)] ++
    List.replicate 6 (.ISingle true) ++ List.replicate 13 (.ISingle false) ++
    [.IJump false (tl1 43462 347733)] ++ List.replicate 7 (.ISingle false)
def Rs_r0 : List run :=
    mkruns 0 [tl1 74804 598752, tl1 224495 1796256, tl1 673560 5388768, tl1 2020752 16166304, cn 4,
    tl1 521610 4172796, cn 1]
def prog_r0 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 817 6561)] ++
    List.replicate 6 (.ISingle true) ++ List.replicate 9 (.ISingle false) ++
    [.IJump false (tl1 43463 347733)] ++ List.replicate 7 (.ISingle false)
def Rs_r1 : List run :=
    mkruns 0 [tl1 2020748 16166304, cn 7, tl1 551120 4408992, tl1 1564809 12518388, cn 2]
def prog_r1 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 2457 19683)] ++
    List.replicate 7 (.ISingle true) ++ List.replicate 5 (.ISingle false) ++
    [.IJump false (tl1 130398 1043199)] ++ List.replicate 4 (.ISingle false)
def Rs_r2 : List run :=
    mkruns 0 [tl1 8276 66528, tl1 24911 199584, tl1 74808 598752, tl1 224496 1796256,
    tl1 673559 5388768, tl1 2020751 16166304, cn 8, tl1 29514 236196, tl1 5826224 46609344, cn 2]
def prog_r2 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 817 6561)] ++
    List.replicate 6 (.ISingle true) ++ List.replicate 8 (.ISingle false) ++
    [.IJump false (tl1 43464 347733)] ++ List.replicate 4 (.ISingle false)
def Rs_r3 : List run :=
    mkruns 0 [tl1 224492 1796256, tl1 673559 5388768, tl1 2020752 16166304, tl1 6062328 48498912,
    cn 4, tl1 1564810 12518388]
def prog_r3 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 2457 19683)] ++
    List.replicate 7 (.ISingle true) ++ List.replicate 9 (.ISingle false) ++
    [.IJump false (tl1 130397 1043199)] ++ List.replicate 4 (.ISingle false)
def Rs_r4 : List run :=
    mkruns 0 [tl1 74804 598752, tl1 224495 1796256, tl1 673560 5388768, tl1 2020752 16166304,
    tl1 6062327 48498912, cn 7, tl1 1653368 13226976, tl1 4694422 37555164, cn 1]
def prog_r4 : List instr :=
    List.replicate 4 (.ISingle true) ++ [.IJump true (tl1 2457 19683)] ++
    List.replicate 7 (.ISingle true) ++ List.replicate 6 (.ISingle false) ++
    [.IJump false (tl1 130397 1043199)] ++ List.replicate 7 (.ISingle false)

def Re_r5 : List run :=
    [(0, tl1 224492 1796256), (1, tl1 673560 5388768), (0, tl1 2020752 16166304), (1, cn 4), (0,
    tl1 521602 4172796)]
def Re_r0 : List run :=
    [(0, tl1 74804 598752), (1, tl1 224496 1796256), (0, tl1 673560 5388768), (1,
    tl1 2020751 16166304), (1, cn 7), (1, tl1 551120 4408992), (0, tl1 1564798 12518388), (1, cn 1)]
def Re_r1 : List run :=
    [(0, tl1 2020748 16166304), (1, cn 8), (0, tl1 29521 236196), (0, tl1 5826161 46609344), (0,
    cn 2)]
def Re_r2 : List run :=
    [(0, tl1 8276 66528), (1, tl1 24912 199584), (0, tl1 74808 598752), (1, tl1 224495 1796256), (1,
    tl1 673559 5388768), (1, tl1 2020752 16166304), (0, tl1 6062328 48498912), (1, cn 3), (1,
    tl1 1564801 12518388), (1, cn 1)]
def Re_r3 : List run :=
    [(0, tl1 224492 1796256), (1, tl1 673560 5388768), (0, tl1 2020752 16166304), (1,
    tl1 6062327 48498912), (1, cn 7), (1, tl1 1653368 13226976), (0, tl1 4694397 37555164), (0,
    cn 2)]
def Re_r4 : List run :=
    [(0, tl1 74804 598752), (1, tl1 224496 1796256), (0, tl1 673560 5388768), (1,
    tl1 2020751 16166304), (1, tl1 6062327 48498912), (1, cn 7), (1, tl1 88573 708588), (1,
    tl1 17478488 139828032), (0, cn 2)]

theorem int_r5 : prog_check prog_r5 Rs_r5 Re_r5 (tl1 3278 26244) (tl1 173868 1390932) = true := by
  decide +kernel
theorem int_r0 : prog_check prog_r0 Rs_r0 Re_r0 (tl1 3278 26244) (tl1 173868 1390932) = true := by
  decide +kernel
theorem int_r1 : prog_check prog_r1 Rs_r1 Re_r1 (tl1 9839 78732) (tl1 521601 4172796) = true := by
  decide +kernel
theorem int_r2 : prog_check prog_r2 Rs_r2 Re_r2 (tl1 3278 26244) (tl1 173868 1390932) = true := by
  decide +kernel
theorem int_r3 : prog_check prog_r3 Rs_r3 Re_r3 (tl1 9839 78732) (tl1 521601 4172796) = true := by
  decide +kernel
theorem int_r4 : prog_check prog_r4 Rs_r4 Re_r4 (tl1 9839 78732) (tl1 521601 4172796) = true := by
  decide +kernel

def W5t (t : Nat) : Nat := 18701 + 149688 * t
def W5s (t : Nat) : Nat := 6227 + 49896 * t
def W5a (t : Nat) : Nat := 2069 + 16632 * t
def wv (c a t : Nat) : Nat := c + a * t
def W0t := wv 6227 49896
def W0s := wv 2069 16632
def W1t := wv 168389 1347192
def W1s := wv 56123 449064
def W1a := wv 18701 149688
def W1I := wv 6227 49896
def W1u := wv 2069 16632
def W3t := wv 18701 149688

def sig01 : List lf := [tl1 168389 1347192, tl1 56123 449064, tl1 18701 149688, tl1 6227 49896]
def f4_r0 : List run :=
    [(0, tl1 74804 598752), (1, tl1 224496 1796256), (0, tl1 673560 5388768), (1, cn 3)]
def Rp_r0 : List run :=
    [(0, tl1 2020748 16166304), (1, cn 7), (1, tl1 551120 4408992), (0, tl1 1564798 12518388), (1,
    cn 1)]
def sig12 : List lf := [tl1 56123 449064, tl1 18701 149688, tl1 6227 49896, tl1 2069 16632]
def xv : lf := ⟨2, [0, 4]⟩
def sig23 : List lf := [tl1 18701 149688, tl1 6227 49896, tl1 2069 16632, ⟨0, [0, 1]⟩]
def f4_r2 : List run :=
    [(0, tl1 8276 66528), (1, tl1 24912 199584), (0, tl1 74808 598752), (1, cn 3)]
def Rp_r2 : List run :=
    [(0, tl1 224492 1796256), (1, tl1 673559 5388768), (1, tl1 2020752 16166304), (0,
    tl1 6062328 48498912), (1, cn 3), (1, tl1 1564801 12518388), (1, cn 1)]

def sub9_lf (l : lf) : lf :=
  match l.lv with
  | [a] => ⟨l.lc + a, [9 * a]⟩
  | _ => l
def sub9 (rs : List run) : List run := rs.map (fun r => (r.1, sub9_lf r.2))

def sig45 : List lf := [tl1 168389 1347192, tl1 56123 449064, tl1 18701 149688, ⟨0, [0, 1]⟩]
def f4_r4 : List run :=
    [(0, tl1 74804 598752), (1, tl1 224496 1796256), (0, tl1 673560 5388768), (1, cn 3)]
def Rp_r4 : List run :=
    [(0, tl1 2020748 16166304), (1, tl1 6062327 48498912), (1, cn 7), (1, tl1 88573 708588), (1,
    tl1 17478488 139828032), (0, cn 2)]

theorem rec_r5_ok :
    reach 500 (.Rc B ([(0, cn 1), (0, tl1 74806 598752)], .TV 0) (Re_r5, .T0)) (.Lc D ([],
        .TV 0) (Rs_r0, .T0)) = true := by
  decide +kernel

theorem rec_r0a :
    reach 500 (.Rc B ([(0, cn 1), (0, tl1 24910 199584)], .TV 0) (f4_r0, .TV 1))
      (.Rc A (comp_runs sig01 (blk .U0), .TV 0) ([], .TV 1)) = true := by
  decide +kernel

theorem rec_r0b : ep_run true Rp_r0 = some Rs_r1 := by decide +kernel

theorem rec_r3_ok :
    reach 500 (.Rc B ([(0, cn 1), (0, tl1 74806 598752)], .TV 0) (Re_r3, .T0)) (.Lc D ([],
        .TV 0) (Rs_r4, .T0)) = true := by
  decide +kernel

theorem rec_r1_ok :
    reach 500 (.Rc B ([(0, cn 1), (0, tl1 673558 5388768)] ++ comp_runs sig12 (blk .U0),
        .TV 0) (Re_r1, .T0))
      (.Lc D ([], .TV 0) (Rs_r2, .T0)) = true := by
  decide +kernel

theorem rec_r2a :
    reach 500 (.Rc B ([(0, cn 1), (0, xv)], .TV 0) (f4_r2, .TV 1))
      (.Rc A (comp_runs sig23 (blk .U0), .TV 0) ([], .TV 1)) = true := by
  decide +kernel

theorem rec_r2b : ep_run true Rp_r2 = some Rs_r3 := by decide +kernel

theorem rec_r4a :
    reach 500 (.Rc B ([(0, cn 1), (0, xv)], .TV 0) (f4_r4, .TV 1))
      (.Rc A (comp_runs sig45 (blk .U0), .TV 0) ([], .TV 1)) = true := by
  decide +kernel

theorem rec_r4b : ep_run true Rp_r4 = some (sub9 Rs_r5) := by decide +kernel

theorem step_r5 (t f1 : Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 1)) ([W5t t, W5s t, W5a t,
        f1] :: deep) (b1s .PD2 (LWs 81))) {{B}}> (evR [t] Re_r5)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([W5s t, W5a t, f1,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r0) := by
  have hreg :=
      regroup ([W5t t, W5s t, W5a t, f1] :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  simp only [List.length_cons, rtop, rshift, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hreg
  rw [hreg]
  set X' :=
      chs (rep .U0 (deep.length + 1)) ([W5s t, W5a t, f1,
      rtop deep 0] :: rshift deep 0) (b1s .P0 (LWs 0))
  have hev : 2 + 4 * W5t t = ev [t] (tl1 74806 598752) := by
    simp only [ev, W5t, tl1, dot]
    omega
  rw [hev]
  exact drop_step [(0, cn 1), (0, tl1 74806 598752)] Re_r5 Rs_r0 [t] X' rec_r5_ok

theorem pow_K0 (k0 e : Nat) (he : 2 ≤ e) : 3 ^ (k0 + 2 * e) = 3 ^ (k0 + 4) * 9 ^ (e - 2) := by
  have h1 : k0 + 2 * e = (k0 + 4) + 2 * (e - 2) := by omega
  have h2 : (3 : Nat) ^ (2 * (e - 2)) = 9 ^ (e - 2) := by
    rw [Nat.pow_mul]
  rw [h1, Nat.pow_add, h2]

theorem S_r5 (e t f1 : Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 1 + 2 * e) :
    (Gc (rep .U0 (deep.length + 1), .P0, 0) ([W5t t, W5s t, W5a t,
        f1] :: deep) (evR [t] Rs_r5)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([W5s t, W5a t, f1,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r0) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 1) ([W5t t, W5s t, W5a t, f1] :: deep)
    (evR [t] Rs_r5) (evR [t] Re_r5) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r5 [t]
    have e3 : 3 ^ (deep.length + 1 + 2) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 2 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]
      rfl
    have e2 : 3 ^ (deep.length + 1 + 1) = 27 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 1 = 3 + 2 * e := by omega
      rw [hk, pow_K0 3 e he]
      rfl
    rw [e3] at eT
    rw [e2]
    have hT : T = ev [t] (tl1 3278 26244) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (27 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 3278 26244) =
        ev [t] (tl1 173868 1390932) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]
    exact hp
  · exact stepPlus_trans (record_visit (deep.length + 1) ([W5t t, W5s t, W5a t,
      f1] :: deep) (evR [t] Re_r5) rfl)
      (step_r5 t f1 deep)

theorem evN_tl1 (c a t : Nat) : evN [t] (tl1 c a) = wv c a t := by
  simp only [evN, tl1, wv, dot]
  omega

theorem take_step (L first4 Re' Rs : List run) (nu : List Nat) (sg : List lf) (X' : Side6)
    (h1 : reach 500 (.Rc B (L, .TV 0) (first4, .TV 1)) (.Rc A (comp_runs sg (blk .U0), .TV 0) ([],
        .TV 1)) = true)
    (h2 : ep_run true Re' = some Rs) :
    ((ev_runs nu L X') {{B}}> (ev_runs nu first4 (evR nu Re'))) [tm372]⊢⁺
      ((ev_runs (sg.map (evN nu)) (blk .U0) X') <{{D}} (evR nu Rs)) := by
  refine stepPlus_stepStar_trans (reach_spec h1 nu (sg2 X' (evR nu Re'))) ?_
  change ((ev_runs nu (comp_runs sg (blk .U0)) X') {{A}}> (evR nu Re')) [tm372]⊢*
    ((ev_runs (sg.map (evN nu)) (blk .U0) X') <{{D}} (evR nu Rs))
  rw [ev_runs_comp]
  exact ep_run_spec h2 nu _

theorem split4 (nu : List Nat) (r1 r2 r3 : run) (b : Sym2) (c : Nat) (v : List Nat) (rest : List
    run) (X : Side6) :
    ev_runs nu (r1 :: r2 :: r3 :: (b, ⟨3 + c, v⟩) :: rest) X =
      ev_runs nu [r1, r2, r3, (b, cn 3)] (ev_runs nu ((sneg b, ⟨c, v⟩) :: rest) X) := by
  rcases r1 with ⟨b1, n1⟩
  rcases r2 with ⟨b2, n2⟩
  rcases r3 with ⟨b3, n3⟩
  simp only [ev_runs, ev_cn]
  have hreg : alt b (ev nu ⟨3 + c, v⟩) = alt b 3 ++ alt (sneg b) (ev nu ⟨c, v⟩) := by
    simp only [ev]
    have hadd : 3 + c + dot v nu = 3 + (c + dot v nu) := by omega
    rw [hadd, alt_add]
    rfl
  rw [hreg, append_assoc]

theorem split_r0 (t : Nat) : evR [t] Re_r0 = ev_runs [t] f4_r0 (evR [t] Rp_r0) := by
  unfold evR Re_r0 f4_r0 Rp_r0 tl1
  change ev_runs [t] ((0, ⟨74804, [598752]⟩) :: (1, ⟨224496, [1796256]⟩) :: (0, ⟨673560,
      [5388768]⟩) ::
      (1, ⟨3 + 2020748, [16166304]⟩) :: _) default = _
  exact split4 [t] _ _ _ 1 2020748 [16166304] _ default

theorem step_r0 (t f1 f2 : Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 1)) ([W0t t, W0s t, f1,
        f2] :: deep) (b1s .PD2 (LWs 81))) {{B}}> (evR [t] Re_r0)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W1t t, W1s t, W1a t, W1I t] :: [W0s t, f1, f2,
            rtop deep 0] :: rshift deep 0) (evR [t] Rs_r1) := by
  have hreg :=
      regroup ([W0t t, W0s t, f1, f2] :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  have hrtop : rtop ([W0t t, W0s t, f1, f2] :: deep) 0 = W0t t := rfl
  have hrshift : rshift ([W0t t, W0s t, f1, f2] :: deep) 0 = [W0s t, f1, f2,
      rtop deep 0] :: rshift deep 0 := rfl
  rw [List.length_cons, hrtop, hrshift] at hreg
  rw [hreg]
  set X' :=
      chs (rep .U0 (deep.length + 1)) ([W0s t, f1, f2,
      rtop deep 0] :: rshift deep 0) (b1s .P0 (LWs 0))
  have hev : 2 + 4 * W0t t = ev [t] (tl1 24910 199584) := by
    simp only [ev, W0t, wv, tl1, dot]; omega
  rw [hev, split_r0]
  have hsig : [W1t t, W1s t, W1a t, W1I t] = sig01.map (evN [t]) := by
    simp only [sig01, List.map, evN_tl1, W1t, W1s, W1a, W1I]
  rw [hsig]
  exact take_step [(0, cn 1), (0, tl1 24910 199584)] f4_r0 Rp_r0 Rs_r1 [t] sig01 X' rec_r0a rec_r0b

theorem step_r3 (t f1 f2 f3 : Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 1)) ([W3t t, f1, f2,
        f3] :: deep) (b1s .PD2 (LWs 81))) {{B}}> (evR [t] Re_r3)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([f1, f2, f3,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r4) := by
  have hreg :=
      regroup ([W3t t, f1, f2, f3] :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  simp only [List.length_cons, rtop, rshift, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hreg
  rw [hreg]
  set X' :=
      chs (rep .U0 (deep.length + 1)) ([f1, f2, f3, rtop deep 0] :: rshift deep 0) (b1s .P0 (LWs 0))
  have hev : 2 + 4 * W3t t = ev [t] (tl1 74806 598752) := by
    simp only [ev, W3t, wv, tl1, dot]; omega
  rw [hev]
  exact drop_step [(0, cn 1), (0, tl1 74806 598752)] Re_r3 Rs_r4 [t] X' rec_r3_ok

theorem step_r1 (t f1 f2 f3 : Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 2)) ([W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2,
        f3] :: deep) (b1s .PD2 (LWs 81)))
      {{B}}> (evR [t] Re_r1)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([f1, f2, f3,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r2) := by
  have hreg :=
      regroup ([W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2,
      f3] :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  simp only [List.length_cons, rtop, rshift, List.getD, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.getD_some] at hreg
  rw [hreg]
  set X' :=
      chs (rep .U0 (deep.length + 1)) ([f1, f2, f3, rtop deep 0] :: rshift deep 0) (b1s .P0 (LWs 0))
  change ((alt 0 1 +> (alt 0 (2 + 4 * W1t t) +> ev_runs [W1s t, W1a t, W1I t,
      W1u t] (blk .U0) X')) {{B}}> (evR [t] Re_r1)) [tm372]⊢⁺ _
  have hsig : [W1s t, W1a t, W1I t, W1u t] = sig12.map (evN [t]) := by
    simp only [sig12, List.map, evN_tl1, W1s, W1a, W1I, W1u]
  rw [hsig, ← ev_runs_comp]
  have hev : 2 + 4 * W1t t = ev [t] (tl1 673558 5388768) := by
    simp only [ev, W1t, wv, tl1, dot]; omega
  rw [hev]
  exact drop_step ([(0, cn 1), (0,
      tl1 673558 5388768)] ++ comp_runs sig12 (blk .U0)) Re_r1 Rs_r2 [t] X' rec_r1_ok

theorem split_r2 (nu : List Nat) : evR nu Re_r2 = ev_runs nu f4_r2 (evR nu Rp_r2) := by
  unfold evR Re_r2 f4_r2 Rp_r2 tl1
  change ev_runs nu ((0, ⟨8276, [66528]⟩) :: (1, ⟨24912, [199584]⟩) :: (0, ⟨74808, [598752]⟩) ::
      (1, ⟨3 + 224492, [1796256]⟩) :: _) default = _
  exact split4 nu _ _ _ 1 224492 [1796256] _ default

theorem step_r2 (t : Nat) (q : List Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 1)) (q :: deep) (b1s .PD2 (LWs 81))) {{B}}> (evR [t] Re_r2))
        [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W3t t, wv 6227 49896 t, wv 2069 16632 t,
            q.getD 0 0] :: rshift (q :: deep) 0) (evR [t] Rs_r3) := by
  have hreg := regroup (q :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  simp only [List.length_cons, rtop] at hreg
  rw [hreg]
  set xK := q.getD 0 0
  set X' := chs (rep .U0 (deep.length + 1)) (rshift (q :: deep) 0) (b1s .P0 (LWs 0))
  have hr1 : evR [t] Re_r2 = evR [t, xK] Re_r2 := rfl
  have hr2 : evR [t] Rs_r3 = evR [t, xK] Rs_r3 := rfl
  have hev : 2 + 4 * xK = ev [t, xK] xv := by
    simp only [ev, xv, dot]; omega
  have hsig : [W3t t, wv 6227 49896 t, wv 2069 16632 t, xK] = sig23.map (evN [t, xK]) := by
    simp only [sig23, W3t, wv, tl1, evN, List.map, dot]
    refine congrArg₂ List.cons (by omega) (congrArg₂ List.cons (by omega) (congrArg₂ List.cons (by
        omega) (congrArg₂ List.cons (by omega) rfl)))
  rw [hr1, hr2, hev, hsig, split_r2]
  exact take_step [(0, cn 1), (0, xv)] f4_r2 Rp_r2 Rs_r3 [t, xK] sig23 X' rec_r2a rec_r2b

theorem ev_runs_sub9 (t : Nat) (rs : List run) (X : Side6)
    (h : rs.all (fun r => decide (r.2.lv.length ≤ 1)) = true) :
    ev_runs [t] (sub9 rs) X = ev_runs [1 + 9 * t] rs X := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨b, c, _ | ⟨a, _ | ⟨a', v⟩⟩⟩
    · simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      change alt b (ev [t] (sub9_lf ⟨c, []⟩)) +> ev_runs [t] (sub9 rs) X =
        alt b (ev [1 + 9 * t] ⟨c, []⟩) +> ev_runs [1 + 9 * t] rs X
      rw [ih h.2]
      rfl
    · simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      change alt b (ev [t] (sub9_lf ⟨c, [a]⟩)) +> ev_runs [t] (sub9 rs) X =
        alt b (ev [1 + 9 * t] ⟨c, [a]⟩) +> ev_runs [1 + 9 * t] rs X
      rw [ih h.2]
      congr 2
      simp only [sub9_lf, ev, dot]
      ring
    · simp [List.all_cons] at h

theorem evR_sub9_r5 (t : Nat) : evR [t] (sub9 Rs_r5) = evR [1 + 9 * t] Rs_r5 :=
  ev_runs_sub9 t Rs_r5 default rfl

theorem split_r4 (nu : List Nat) : evR nu Re_r4 = ev_runs nu f4_r4 (evR nu Rp_r4) := by
  unfold evR Re_r4 f4_r4 Rp_r4 tl1
  change ev_runs nu ((0, ⟨74804, [598752]⟩) :: (1, ⟨224496, [1796256]⟩) :: (0, ⟨673560,
      [5388768]⟩) ::
      (1, ⟨3 + 2020748, [16166304]⟩) :: _) default = _
  exact split4 nu _ _ _ 1 2020748 [16166304] _ default

theorem step_r4 (t : Nat) (q : List Nat) (deep : List (List Nat)) :
    ((chs (rep .D2 (deep.length + 1)) (q :: deep) (b1s .PD2 (LWs 81))) {{B}}> (evR [t] Re_r4))
        [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W5t (1 + 9 * t), W5s (1 + 9 * t), W5a (1 + 9 * t), q.getD 0 0] :: rshift (q :: deep) 0)
        (evR [1 + 9 * t] Rs_r5) := by
  have hreg := regroup (q :: deep) 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  simp only [List.length_cons, rtop] at hreg
  rw [hreg]
  set xK := q.getD 0 0
  set X' := chs (rep .U0 (deep.length + 1)) (rshift (q :: deep) 0) (b1s .P0 (LWs 0))
  have hr1 : evR [t] Re_r4 = evR [t, xK] Re_r4 := rfl
  rw [← evR_sub9_r5]
  have hr2 : evR [t] (sub9 Rs_r5) = evR [t, xK] (sub9 Rs_r5) := rfl
  have hev : 2 + 4 * xK = ev [t, xK] xv := by
    simp only [ev, xv, dot]; omega
  have hsig : [W5t (1 + 9 * t), W5s (1 + 9 * t), W5a (1 + 9 * t), xK] = sig45.map (evN [t, xK]) :=
      by
    simp only [sig45, W5t, W5s, W5a, tl1, evN, List.map, dot]
    refine congrArg₂ List.cons (by omega) (congrArg₂ List.cons (by omega) (congrArg₂ List.cons (by
        omega) (congrArg₂ List.cons (by omega) rfl)))
  rw [hr1, hr2, hev, hsig, split_r4]
  exact take_step [(0, cn 1), (0, xv)] f4_r4 Rp_r4 (sub9 Rs_r5) [t, xK] sig45 X' rec_r4a rec_r4b

theorem S_r0 (e t f1 f2 : Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 1 + 2 * e) :
    (Gc (rep .U0 (deep.length + 1), .P0, 0) ([W0t t, W0s t, f1,
        f2] :: deep) (evR [t] Rs_r0)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W1t t, W1s t, W1a t, W1I t] :: [W0s t, f1, f2,
            rtop deep 0] :: rshift deep 0) (evR [t] Rs_r1) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 1) ([W0t t, W0s t, f1, f2] :: deep)
    (evR [t] Rs_r0) (evR [t] Re_r0) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r0 [t]
    have e3 : 3 ^ (deep.length + 1 + 2) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 2 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]; rfl
    have e2 : 3 ^ (deep.length + 1 + 1) = 27 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 1 = 3 + 2 * e := by omega
      rw [hk, pow_K0 3 e he]; rfl
    rw [e3] at eT; rw [e2]
    have hT : T = ev [t] (tl1 3278 26244) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (27 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 3278 26244) =
        ev [t] (tl1 173868 1390932) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]; exact hp
  · exact stepPlus_trans (record_visit (deep.length + 1) ([W0t t, W0s t, f1,
      f2] :: deep) (evR [t] Re_r0) rfl)
      (step_r0 t f1 f2 deep)

theorem S_r1 (e t f1 f2 f3 : Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 1 + 2 * e) :
    (Gc (rep .U0 (deep.length + 2), .P0, 0)
      ([W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2, f3] :: deep) (evR [t] Rs_r1)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([f1, f2, f3,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r2) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 2)
    ([W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2, f3] :: deep)
    (evR [t] Rs_r1) (evR [t] Re_r1) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r1 [t]
    have e3 : 3 ^ (deep.length + 2 + 2) = 243 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 2 + 2 = 5 + 2 * e := by omega
      rw [hk, pow_K0 5 e he]; rfl
    have e2 : 3 ^ (deep.length + 2 + 1) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 2 + 1 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]; rfl
    rw [e3] at eT; rw [e2]
    have hT : T = ev [t] (tl1 9839 78732) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (81 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 9839 78732) =
        ev [t] (tl1 521601 4172796) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]; exact hp
  · exact stepPlus_trans (record_visit (deep.length + 2)
      ([W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2, f3] :: deep) (evR [t] Re_r1) rfl)
      (step_r1 t f1 f2 f3 deep)

theorem S_r2 (e t : Nat) (q : List Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 1 + 2 * e) :
    (Gc (rep .U0 (deep.length + 1), .P0, 0) (q :: deep) (evR [t] Rs_r2)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W3t t, wv 6227 49896 t, wv 2069 16632 t,
            q.getD 0 0] :: rshift (q :: deep) 0) (evR [t] Rs_r3) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 1) (q :: deep)
    (evR [t] Rs_r2) (evR [t] Re_r2) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r2 [t]
    have e3 : 3 ^ (deep.length + 1 + 2) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 2 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]; rfl
    have e2 : 3 ^ (deep.length + 1 + 1) = 27 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 1 + 2 * e + 1 + 1 = 3 + 2 * e := by omega
      rw [hk, pow_K0 3 e he]; rfl
    rw [e3] at eT; rw [e2]
    have hT : T = ev [t] (tl1 3278 26244) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (27 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 3278 26244) =
        ev [t] (tl1 173868 1390932) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]; exact hp
  · exact stepPlus_trans (record_visit (deep.length + 1) (q :: deep) (evR [t] Re_r2) rfl)
      (step_r2 t q deep)

theorem S_r3 (e t f1 f2 f3 : Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 2 + 2 * e) :
    (Gc (rep .U0 (deep.length + 1), .P0, 0) ([W3t t, f1, f2, f3] :: deep) (evR [t] Rs_r3)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 1), .P0, 0) ([f1, f2, f3,
          rtop deep 0] :: rshift deep 0) (evR [t] Rs_r4) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 1) ([W3t t, f1, f2, f3] :: deep)
    (evR [t] Rs_r3) (evR [t] Re_r3) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r3 [t]
    have e3 : 3 ^ (deep.length + 1 + 2) = 243 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 2 + 2 * e + 1 + 2 = 5 + 2 * e := by omega
      rw [hk, pow_K0 5 e he]; rfl
    have e2 : 3 ^ (deep.length + 1 + 1) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 2 + 2 * e + 1 + 1 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]; rfl
    rw [e3] at eT; rw [e2]
    have hT : T = ev [t] (tl1 9839 78732) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (81 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 9839 78732) =
        ev [t] (tl1 521601 4172796) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]; exact hp
  · exact stepPlus_trans (record_visit (deep.length + 1) ([W3t t, f1, f2,
      f3] :: deep) (evR [t] Re_r3) rfl)
      (step_r3 t f1 f2 f3 deep)

theorem S_r4 (e t : Nat) (q : List Nat) (deep : List (List Nat))
    (he : 2 ≤ e) (ht : 1 + 8 * t = 9 ^ (e - 2)) (hl : deep.length = 2 + 2 * e) :
    (Gc (rep .U0 (deep.length + 1), .P0, 0) (q :: deep) (evR [t] Rs_r4)) [tm372]⊢⁺
      Gc (rep .U0 (deep.length + 2), .P0, 0)
        ([W5t (1 + 9 * t), W5s (1 + 9 * t), W5a (1 + 9 * t), q.getD 0 0] :: rshift (q :: deep) 0)
        (evR [1 + 9 * t] Rs_r5) := by
  refine stepStar_stepPlus_trans (interval_tm (deep.length + 1) (q :: deep)
    (evR [t] Rs_r4) (evR [t] Re_r4) (by omega) rfl ?_) ?_
  · intro T eT
    have hp := prog_check_spec int_r4 [t]
    have e3 : 3 ^ (deep.length + 1 + 2) = 243 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 2 + 2 * e + 1 + 2 = 5 + 2 * e := by omega
      rw [hk, pow_K0 5 e he]; rfl
    have e2 : 3 ^ (deep.length + 1 + 1) = 81 * 81 * (1 + 8 * t) := by
      rw [hl, ht]
      have hk : 2 + 2 * e + 1 + 1 = 4 + 2 * e := by omega
      rw [hk, pow_K0 4 e he]; rfl
    rw [e3] at eT; rw [e2]
    have hT : T = ev [t] (tl1 9839 78732) := by simp only [ev, tl1, dot]; omega
    have hF : 81 * (81 * 81 * (1 + 8 * t)) - 1 - ev [t] (tl1 9839 78732) =
        ev [t] (tl1 521601 4172796) := by
      simp only [ev, tl1, dot]; omega
    rw [hT, hF]; exact hp
  · exact stepPlus_trans (record_visit (deep.length + 1) (q :: deep) (evR [t] Re_r4) rfl)
      (step_r4 t q deep)

inductive cls where
  | C5 | C0 | C1 | C2 | C3 | C4
  deriving DecidableEq

def Rs : cls → List run
  | .C5 => Rs_r5
  | .C0 => Rs_r0
  | .C1 => Rs_r1
  | .C2 => Rs_r2
  | .C3 => Rs_r3
  | .C4 => Rs_r4

abbrev ist := cls × Nat × Nat × List (List Nat)

def cfgI : ist → Cfg6
  | (r, _, t, nus) => Gc (rep .U0 nus.length, .P0, 0) nus (evR [t] (Rs r))

def win : cls → Nat → Nat → List (List Nat) → Prop
  | .C5, e, t, nus => ∃ f1 deep, nus = [W5t t, W5s t, W5a t, f1] :: deep ∧ deep.length = 1 + 2 * e
  | .C0, e, t, nus => ∃ f1 f2 deep, nus = [W0t t, W0s t, f1, f2] :: deep ∧ deep.length = 1 + 2 * e
  | .C1, e, t, nus =>
      ∃ f1 f2 f3 deep, nus = [W1t t, W1s t, W1a t, W1I t] :: [W1u t, f1, f2,
      f3] :: deep ∧ deep.length = 1 + 2 * e
  | .C2, e, _, nus => ∃ q deep, nus = q :: deep ∧ deep.length = 1 + 2 * e
  | .C3, e, t, nus => ∃ f1 f2 f3 deep, nus = [W3t t, f1, f2, f3] :: deep ∧ deep.length = 2 + 2 * e
  | .C4, e, _, nus => ∃ q deep, nus = q :: deep ∧ deep.length = 2 + 2 * e

def Inv : ist → Prop
  | (r, e, t, nus) => 2 ≤ e ∧ 1 + 8 * t = 9 ^ (e - 2) ∧ win r e t nus

theorem inv_step (s : ist) (h : Inv s) : ∃ s', ((cfgI s) [tm372]⊢⁺ (cfgI s')) ∧ Inv s' := by
  rcases s with ⟨r, e, t, nus⟩
  rcases h with ⟨he, ht, hw⟩
  cases r
  · rcases hw with ⟨f1, deep, rfl, hl⟩
    refine ⟨(.C0, e, t, [W5s t, W5a t, f1, rtop deep 0] :: rshift deep 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r5 e t f1 deep he ht hl
    · refine ⟨he, ht, f1, rtop deep 0, rshift deep 0, rfl, ?_⟩
      rw [shift_len, hl]
  · rcases hw with ⟨f1, f2, deep, rfl, hl⟩
    refine ⟨(.C1, e, t, [W1t t, W1s t, W1a t, W1I t] :: [W0s t, f1, f2,
        rtop deep 0] :: rshift deep 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r0 e t f1 f2 deep he ht hl
    · refine ⟨he, ht, f1, f2, rtop deep 0, rshift deep 0, rfl, ?_⟩
      rw [shift_len, hl]
  · rcases hw with ⟨f1, f2, f3, deep, rfl, hl⟩
    refine ⟨(.C2, e, t, [f1, f2, f3, rtop deep 0] :: rshift deep 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r1 e t f1 f2 f3 deep he ht hl
    · refine ⟨he, ht, [f1, f2, f3, rtop deep 0], rshift deep 0, rfl, ?_⟩
      rw [shift_len, hl]
  · rcases hw with ⟨q, deep, rfl, hl⟩
    refine ⟨(.C3, e, t, [W3t t, wv 6227 49896 t, wv 2069 16632 t,
        q.getD 0 0] :: rshift (q :: deep) 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r2 e t q deep he ht hl
    · refine ⟨he, ht, wv 6227 49896 t, wv 2069 16632 t, q.getD 0 0, rshift (q :: deep) 0, rfl, ?_⟩
      rw [shift_len, List.length_cons, hl]; omega
  · rcases hw with ⟨f1, f2, f3, deep, rfl, hl⟩
    refine ⟨(.C4, e, t, [f1, f2, f3, rtop deep 0] :: rshift deep 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r3 e t f1 f2 f3 deep he ht hl
    · refine ⟨he, ht, [f1, f2, f3, rtop deep 0], rshift deep 0, rfl, ?_⟩
      rw [shift_len, hl]
  · rcases hw with ⟨q, deep, rfl, hl⟩
    refine ⟨(.C5, e + 1, 1 + 9 * t, [W5t (1 + 9 * t), W5s (1 + 9 * t), W5a (1 + 9 * t),
        q.getD 0 0] :: rshift (q :: deep) 0), ?_, ?_⟩
    · simp only [cfgI, List.length_cons, shift_len, Rs]
      exact S_r4 e t q deep he ht hl
    · refine ⟨by omega, ?_, q.getD 0 0, rshift (q :: deep) 0, rfl, ?_⟩
      · have hsub : e + 1 - 2 = (e - 2) + 1 := by omega
        rw [hsub, Nat.pow_succ, ← ht]
        ring
      · rw [shift_len, List.length_cons, hl]; omega

def nus28_372 : List (List Nat) :=
  [[18701, 6227, 2069, 683], [242, 8, 9, 8], [10, 5, 3, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0,
      0]]

def nus28_557 : List (List Nat) :=
  [[18701, 6227, 2069, 683], [242, 8, 9, 8], [10, 5, 4, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0,
      0]]

def nus28_638 : List (List Nat) :=
  [[18701, 6227, 2069, 683], [233, 8, 9, 8], [12, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0,
      0]]

def eval_runs (nu : List Nat) (rs : List run) : List run :=
  rs.map (fun r => (r.1, cn (evN nu r.2)))

theorem eval_runs_spec (nu : List Nat) (rs : List run) (X : Side6) :
    ev_runs [] (eval_runs nu rs) X = ev_runs nu rs X := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨b, n⟩
    change alt b (ev [] (cn (evN nu n))) +> ev_runs [] (eval_runs nu rs) X =
      alt b (ev nu n) +> ev_runs nu rs X
    rw [ih, ev_cn]
    rfl

def chs_runs : List lab → List (List Nat) → List run → List run
  | s :: ls', nu :: nus', rest => eval_runs nu (blk s) ++ chs_runs ls' nus' rest
  | _, _, rest => rest

theorem chs_runs_spec (ls : List lab) (nus : List (List Nat)) (rest : List run) (X : Side6) :
    ev_runs [] (chs_runs ls nus rest) X = chs ls nus (ev_runs [] rest X) := by
  induction ls generalizing nus with
  | nil => cases nus <;> rfl
  | cons s ls ih =>
    cases nus with
    | nil => rfl
    | cons nu nus =>
      simp only [chs_runs, chs, ev_runs_app, ih, eval_runs_spec]

def norm_sd : List run → sd
  | [] => ([], .T0)
  | (b, n) :: rs => push_run b (cn (ev [] n)) (norm_sd rs)

theorem norm_sd_spec (rs : List run) :
    ev_sd [] (fun _ => default) (norm_sd rs) = ev_runs [] rs default := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨b, n⟩
    simp only [norm_sd]
    rw [push_run_spec [] (fun _ => default) b (cn (ev [] n)) (norm_sd rs) rfl, ih]
    rfl

theorem norm_runs_eq {rs1 rs2 : List run} (h : sd_eqb (norm_sd rs1) (norm_sd rs2) = true) :
    ev_runs [] rs1 default = ev_runs [] rs2 default := by
  rw [← norm_sd_spec rs1, ← norm_sd_spec rs2]
  exact sd_eqb_ev [] (fun _ => default) h

theorem inv28_372 : Inv (.C5, 2, 0, nus28_372) :=
  ⟨by decide, rfl, 683, nus28_372.tail, rfl, rfl⟩

theorem inv28_557 : Inv (.C5, 2, 0, nus28_557) :=
  ⟨by decide, rfl, 683, nus28_557.tail, rfl, rfl⟩

theorem inv28_638 : Inv (.C5, 2, 0, nus28_638) :=
  ⟨by decide, rfl, 683, nus28_638.tail, rfl, rfl⟩

theorem b1s_lws_eq (p : lab1) (i : Nat) : b1s p (LWs i) = ev_runs [] (blk1 p ++ lw i) default := by
  simp [b1s, LWs, ev_runs_app]

theorem b28_right : evR [] (Rs_r5.map (fun r => (r.1, cn (evN [0] r.2)))) = evR [0] Rs_r5 :=
  eval_runs_spec [0] Rs_r5 default

inductive Bit where
  | b0 | b1
  deriving DecidableEq

inductive St6 where
  | A | B | C | D | E | F
  deriving DecidableEq

inductive CRun where
  | mk (b : Bit) (n : Nat)
  deriving DecidableEq

inductive CState where
  | mk (dir : Bool) (q : St6) (l r : List CRun)
  deriving DecidableEq

def consB0 (n : Nat) (rest : List CRun) : List CRun :=
  match Nat.add n 1 with
  | 0 => rest
  | .succ m => .mk .b0 m :: rest

def consB1 (n : Nat) (rest : List CRun) : List CRun :=
  match Nat.add n 1 with
  | 0 => rest
  | .succ m => .mk .b1 m :: rest

def cpush0 : List CRun → List CRun
  | [] => [.mk .b0 1]
  | .mk .b0 n0 :: rest => .mk .b0 1 :: .mk .b0 n0 :: rest
  | .mk .b1 n0 :: rest => consB0 (Nat.add n0 1) rest

def cpush1 : List CRun → List CRun
  | [] => [.mk .b1 1]
  | .mk .b1 n0 :: rest => .mk .b1 1 :: .mk .b1 n0 :: rest
  | .mk .b0 n0 :: rest => consB1 (Nat.add n0 1) rest

def cpushRun00 (n : Nat) : List CRun → List CRun
  | [] => [.mk .b0 n]
  | .mk .b0 n0 :: rest => consB0 (Nat.add n n0) rest
  | .mk .b1 n0 :: rest => .mk .b0 n :: .mk .b1 n0 :: rest

def cpushRun01 (n : Nat) : List CRun → List CRun
  | [] => [.mk .b0 n]
  | .mk .b1 n0 :: rest => consB0 (Nat.add n n0) rest
  | .mk .b0 n0 :: rest => .mk .b0 n :: .mk .b0 n0 :: rest

def cpushRun10 (n : Nat) : List CRun → List CRun
  | [] => [.mk .b1 n]
  | .mk .b0 n0 :: rest => consB1 (Nat.add n n0) rest
  | .mk .b1 n0 :: rest => .mk .b1 n :: .mk .b1 n0 :: rest

def cpushRun11 (n : Nat) : List CRun → List CRun
  | [] => [.mk .b1 n]
  | .mk .b1 n0 :: rest => consB1 (Nat.add n n0) rest
  | .mk .b0 n0 :: rest => .mk .b1 n :: .mk .b0 n0 :: rest

def mkStR (q : St6) (l r : List CRun) : CState :=
  match l with
  | [] => .mk true q [] r
  | l0 :: ls => .mk true q (l0 :: ls) r

def mkStL' (q : St6) (l r : List CRun) : CState :=
  match r with
  | [] => .mk false q l []
  | r0 :: rs => .mk false q l (r0 :: rs)

def stepSingleR (q : St6) (s : Bit) (l r' : List CRun) : CState :=
  match q, s with
  | .A, .b0 => mkStR .B (cpush1 l) r'
  | .A, .b1 => mkStR .F (cpush0 l) r'
  | .B, .b0 => mkStR .C (cpush1 l) r'
  | .B, .b1 => mkStR .B (cpush0 l) r'
  | .C, .b0 => mkStL' .D l (cpush1 r')
  | .C, .b1 => mkStR .A (cpush0 l) r'
  | .D, .b0 => mkStL' .E l (cpush1 r')
  | .D, .b1 => mkStL' .D l (cpush0 r')
  | .E, .b0 => mkStR .B (cpush1 l) r'
  | .E, .b1 => mkStL' .C l (cpush0 r')
  | .F, .b0 => mkStL' .A l (cpush1 r')
  | .F, .b1 => .mk true q l r'

def stepSingleL (q : St6) (s : Bit) (l' r : List CRun) : CState :=
  match q, s with
  | .A, .b0 => mkStR .B (cpush1 l') r
  | .A, .b1 => mkStR .F (cpush0 l') r
  | .B, .b0 => mkStR .C (cpush1 l') r
  | .B, .b1 => mkStR .B (cpush0 l') r
  | .C, .b0 => mkStL' .D l' (cpush1 r)
  | .C, .b1 => mkStR .A (cpush0 l') r
  | .D, .b0 => mkStL' .E l' (cpush1 r)
  | .D, .b1 => mkStL' .D l' (cpush0 r)
  | .E, .b0 => mkStR .B (cpush1 l') r
  | .E, .b1 => mkStL' .C l' (cpush0 r)
  | .F, .b0 => mkStL' .A l' (cpush1 r)
  | .F, .b1 => .mk false q l' r

def popAndStepR (q : St6) (b : Bit) (n : Nat) (l r' : List CRun) : CState :=
  match Nat.beq n 1, b with
  | true,  .b0 => stepSingleR q .b0 l r'
  | true,  .b1 => stepSingleR q .b1 l r'
  | false, .b0 => stepSingleR q .b0 l (consB1 (Nat.sub n 1) r')
  | false, .b1 => stepSingleR q .b1 l (consB0 (Nat.sub n 1) r')

def popAndStepL (q : St6) (b : Bit) (n : Nat) (l' r : List CRun) : CState :=
  match Nat.beq n 1, b with
  | true,  .b0 => stepSingleL q .b0 l' r
  | true,  .b1 => stepSingleL q .b1 l' r
  | false, .b0 => stepSingleL q .b0 (consB1 (Nat.sub n 1) l') r
  | false, .b1 => stepSingleL q .b1 (consB0 (Nat.sub n 1) l') r

def csstep : CState → CState
  | .mk true q l [] => stepSingleR q .b0 l []
  | .mk true q l (.mk b n :: r') =>
    match Nat.beq n 0 with
    | true => .mk true q l r'
    | false =>
      match q, b with
      | .B, .b0 =>
        match Nat.mod n 4 with
        | 0 => mkStR .B (cpushRun00 n l) r'
        | 1 => mkStR .C (cpushRun10 n l) r'
        | 2 => mkStR .A (cpushRun00 n l) r'
        | _ => mkStR .B (cpushRun10 n l) r'
      | .C, .b1 =>
        match Nat.mod n 4 with
        | 0 => mkStR .C (cpushRun11 n l) r'
        | 1 => mkStR .A (cpushRun01 n l) r'
        | 2 => mkStR .B (cpushRun11 n l) r'
        | _ => mkStR .B (cpushRun01 n l) r'
      | .A, .b0 =>
        match Nat.mod n 4 with
        | 0 => mkStR .A (cpushRun00 n l) r'
        | 1 => mkStR .B (cpushRun10 n l) r'
        | 2 => mkStR .B (cpushRun00 n l) r'
        | _ => mkStR .C (cpushRun10 n l) r'
      | .B, .b1 =>
        match Nat.mod n 4 with
        | 0 => mkStR .B (cpushRun11 n l) r'
        | 1 => mkStR .B (cpushRun01 n l) r'
        | 2 => mkStR .C (cpushRun11 n l) r'
        | _ => mkStR .A (cpushRun01 n l) r'
      | .F, .b1 => .mk true .F l (.mk .b1 n :: r')
      | _, _ => popAndStepR q b n l r'
  | .mk false q [] r => stepSingleL q .b0 [] r
  | .mk false q (.mk b n :: l') r =>
    match Nat.beq n 0 with
    | true => .mk false q l' r
    | false =>
      match q, b with
      | .D, .b1 =>
        match Nat.mod n 4 with
        | 0 => mkStL' .D l' (cpushRun11 n r)
        | 1 => mkStL' .D l' (cpushRun01 n r)
        | 2 => mkStL' .E l' (cpushRun11 n r)
        | _ => mkStL' .C l' (cpushRun01 n r)
      | .D, .b0 =>
        match Nat.mod n 4 with
        | 0 => mkStL' .D l' (cpushRun00 n r)
        | 1 => mkStL' .E l' (cpushRun10 n r)
        | 2 => mkStL' .C l' (cpushRun00 n r)
        | _ => mkStL' .D l' (cpushRun10 n r)
      | .E, .b1 =>
        match Nat.mod n 4 with
        | 0 => mkStL' .E l' (cpushRun11 n r)
        | 1 => mkStL' .C l' (cpushRun01 n r)
        | 2 => mkStL' .D l' (cpushRun11 n r)
        | _ => mkStL' .D l' (cpushRun01 n r)
      | .C, .b0 =>
        match Nat.mod n 4 with
        | 0 => mkStL' .C l' (cpushRun00 n r)
        | 1 => mkStL' .D l' (cpushRun10 n r)
        | 2 => mkStL' .D l' (cpushRun00 n r)
        | _ => mkStL' .E l' (cpushRun10 n r)
      | .F, .b1 => .mk false .F (.mk .b1 n :: l') r
      | _, _ => popAndStepL q b n l' r

def cstep2n : Nat → CState → CState
  | 0, st => csstep st
  | k + 1, st =>
    match cstep2n k st with
    | .mk d q l r => cstep2n k (.mk d q l r)

def evBit : Bit → Sym2
  | .b0 => 0
  | .b1 => 1

def evSt6 : St6 → Fin 6
  | .A => A | .B => B | .C => C | .D => D | .E => E | .F => F

def toRun : CRun → run
  | .mk b n => (evBit b, cn n)

def toSd (rs : List CRun) : sd :=
  (rs.map toRun, .T0)

def toCfg : CState → cfg
  | .mk true q l r => .Rc (evSt6 q) (toSd l) (toSd r)
  | .mk false q l r => .Lc (evSt6 q) (toSd l) (toSd r)

theorem consB0_eq (n : Nat) (rest : List CRun) : consB0 n rest = .mk .b0 n :: rest := rfl
theorem consB1_eq (n : Nat) (rest : List CRun) : consB1 n rest = .mk .b1 n :: rest := rfl

theorem mkStR_eq (q : St6) (l r : List CRun) : mkStR q l r = .mk true q l r := by
  cases l <;> rfl

theorem mkStL'_eq (q : St6) (l r : List CRun) : mkStL' q l r = .mk false q l r := by
  cases r <;> rfl

theorem toSd_cpush0 (l : List CRun) : toSd (cpush0 l) = push 0 (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;> rfl

theorem toSd_cpush1 (l : List CRun) : toSd (cpush1 l) = push 1 (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;> rfl

theorem lf_add_cn (n n0 : Nat) : lf_add (cn n) (cn n0) = cn (n + n0) := rfl

theorem toSd_cpushRun00 (n : Nat) (l : List CRun) (h : afterb 0 (cn n) = 0) :
    toSd (cpushRun00 n l) = push_run 0 (cn n) (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;>
    simp [cpushRun00, consB0_eq, toSd, toRun, evBit, push_run, h, seqb, lf_add_cn]

theorem toSd_cpushRun01 (n : Nat) (l : List CRun) (h : afterb 0 (cn n) = 1) :
    toSd (cpushRun01 n l) = push_run 0 (cn n) (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;>
    simp [cpushRun01, consB0_eq, toSd, toRun, evBit, push_run, h, seqb, lf_add_cn]

theorem toSd_cpushRun10 (n : Nat) (l : List CRun) (h : afterb 1 (cn n) = 0) :
    toSd (cpushRun10 n l) = push_run 1 (cn n) (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;>
    simp [cpushRun10, consB1_eq, toSd, toRun, evBit, push_run, h, seqb, lf_add_cn]

theorem toSd_cpushRun11 (n : Nat) (l : List CRun) (h : afterb 1 (cn n) = 1) :
    toSd (cpushRun11 n l) = push_run 1 (cn n) (toSd l) := by
  rcases l with _ | ⟨⟨_ | _, n0⟩, rest⟩ <;>
    simp [cpushRun11, consB1_eq, toSd, toRun, evBit, push_run, h, seqb, lf_add_cn]

def cpopRest (b : Bit) (n : Nat) (r' : List CRun) : List CRun :=
  match Nat.beq n 1, b with
  | true,  .b0 => r'
  | true,  .b1 => r'
  | false, .b0 => consB1 (Nat.sub n 1) r'
  | false, .b1 => consB0 (Nat.sub n 1) r'

theorem popAndStepR_eq (q : St6) (b : Bit) (n : Nat) (l r' : List CRun) :
    popAndStepR q b n l r' = stepSingleR q b l (cpopRest b n r') := by
  unfold popAndStepR cpopRest
  cases Nat.beq n 1 <;> cases b <;> rfl

theorem popAndStepL_eq (q : St6) (b : Bit) (n : Nat) (l' r : List CRun) :
    popAndStepL q b n l' r = stepSingleL q b (cpopRest b n l') r := by
  unfold popAndStepL cpopRest
  cases Nat.beq n 1 <;> cases b <;> rfl

theorem beq_eq_nat_beq (n k : Nat) : (n == k) = Nat.beq n k := by
  rw [Bool.eq_iff_iff, beq_iff_eq, Nat.beq_eq]

theorem is_zero_cn (n : Nat) : is_zero (cn n) = Nat.beq n 0 := by
  simp [is_zero, cn, allz, beq_eq_nat_beq]

theorem is_one_cn (n : Nat) : is_one (cn n) = Nat.beq n 1 := by
  simp [is_one, cn, allz, beq_eq_nat_beq]

theorem posb_cn (n : Nat) : posb (cn n) = !(Nat.beq n 0) := by
  simp [posb, cn, beq_eq_nat_beq]

theorem toSd_nil : toSd [] = ([], .T0) := rfl

theorem toSd_cons (b : Bit) (n : Nat) (rs : List CRun) :
    toSd (.mk b n :: rs) = ((evBit b, cn n) :: (toSd rs).1, .T0) := rfl

theorem pop_toSd_b0 (n : Nat) (r' : List CRun) (hz : Nat.beq n 0 = false) :
    pop ((0, cn n) :: (toSd r').1, .T0) = some (0, toSd (cpopRest .b0 n r')) := by
  unfold pop pop_runs cpopRest
  rw [is_zero_cn, posb_cn, is_one_cn, hz]
  cases Nat.beq n 1 <;> rfl

theorem pop_toSd_b1 (n : Nat) (r' : List CRun) (hz : Nat.beq n 0 = false) :
    pop ((1, cn n) :: (toSd r').1, .T0) = some (1, toSd (cpopRest .b1 n r')) := by
  unfold pop pop_runs cpopRest
  rw [is_zero_cn, posb_cn, is_one_cn, hz]
  cases Nat.beq n 1 <;> rfl

theorem mod4_cases (n : Nat) :
    n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega

theorem mod2_of_mod4 (n : Nat) : n % 2 = (n % 4) % 2 := by omega

theorem cn_lc (n : Nat) : (cn n).lc = n := rfl
theorem cn_lv (n : Nat) : (cn n).lv = [] := rfl

theorem lastb_cn (b : Sym2) (n : Nat) :
    lastb b (cn n) = if (n % 4) % 2 == 0 then sneg b else b := by
  unfold lastb cn
  dsimp
  rw [mod2_of_mod4]

theorem afterb_cn (c : Sym2) (n : Nat) :
    afterb c (cn n) = if (n % 4) % 2 == 0 then c else sneg c := by
  unfold afterb cn
  dsimp
  rw [mod2_of_mod4]

theorem toCfg_csstep (st : CState) : toCfg (csstep st) = urun 1 (toCfg st) := by
  rcases st with ⟨_ | _, q, l, r⟩
  · -- dir = false (Lc)
    rcases l with _ | ⟨⟨b, n⟩, l'⟩
    · -- l = []
      cases q <;>
        simp [csstep, stepSingleL, mkStR_eq, mkStL'_eq, toCfg, toSd_nil, toSd_cpush1,
          urun, sstep, tag, single, pop, pop_runs, evSt6, tm372]
    · -- l = .mk b n :: l'
      simp only [csstep]
      rcases hz : Nat.beq n 0
      · -- Nat.beq n 0 = false
        have hzne : is_zero (cn n) = false := by rw [is_zero_cn, hz]
        have hpop0 := pop_toSd_b0 n l' hz
        have hpop1 := pop_toSd_b1 n l' hz
        cases q <;> cases b
        · -- A, b0
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- A, b1
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- B, b0
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- B, b1
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- C, b0 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n r (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- C, b1
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- D, b0 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n r (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- D, b1 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n r (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- E, b0
          simp [popAndStepL_eq, stepSingleL, mkStR_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- E, b1 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n r (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStL'_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cL_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n r (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- F, b0
          simp [popAndStepL_eq, stepSingleL, mkStL'_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- F, b1 (halting)
          simp [toCfg, toSd_cons, urun, sstep, hzne, cL_idx, evSt6, evBit, tag, single, hpop1,
              tm372]
      · -- Nat.beq n 0 = true
        have hzeq : is_zero (cn n) = true := by rw [is_zero_cn, hz]
        simp [toCfg, toSd, toRun, urun, sstep, hzeq]
  · -- dir = true (Rc)
    rcases r with _ | ⟨⟨b, n⟩, r'⟩
    · -- r = []
      cases q <;>
        simp [csstep, stepSingleR, mkStR_eq, mkStL'_eq, toCfg, toSd_nil, toSd_cpush1,
          urun, sstep, tag, single, pop, pop_runs, evSt6, tm372]
    · -- r = .mk b n :: r'
      simp only [csstep]
      rcases hz : Nat.beq n 0
      · -- Nat.beq n 0 = false
        have hzne : is_zero (cn n) = false := by rw [is_zero_cn, hz]
        have hpop0 := pop_toSd_b0 n r' hz
        have hpop1 := pop_toSd_b1 n r' hz
        cases q <;> cases b
        · -- A, b0 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n l (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- A, b1
          simp [popAndStepR_eq, stepSingleR, mkStR_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- B, b0 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun00 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun10 n l (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- B, b1 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n l (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- C, b0
          simp [popAndStepR_eq, stepSingleR, mkStL'_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- C, b1 (accelerated)
          change toCfg (match n % 4 with | 0 => _ | 1 => _ | 2 => _ | _ => _) = _
          rcases mod4_cases n with h4 | h4 | h4 | h4
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun11 n l (by rw [afterb_cn, h4]; rfl)]; rfl
          · simp only [cn_lc, cn_lv, h4, mkStR_eq, toCfg, toSd_cons, urun, sstep, evSt6, evBit,
              hzne, Bool.false_eq_true, ↓reduceIte, cR_idx, all4, List.all_nil, lastb_cn]
            rw [toSd_cpushRun01 n l (by rw [afterb_cn, h4]; rfl)]; rfl
        · -- D, b0
          simp [popAndStepR_eq, stepSingleR, mkStL'_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- D, b1
          simp [popAndStepR_eq, stepSingleR, mkStL'_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- E, b0
          simp [popAndStepR_eq, stepSingleR, mkStR_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- E, b1
          simp [popAndStepR_eq, stepSingleR, mkStL'_eq, toCfg, toSd_cons, toSd_cpush0,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop1, tm372]
        · -- F, b0
          simp [popAndStepR_eq, stepSingleR, mkStL'_eq, toCfg, toSd_cons,
              toSd_cpush1,
            urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop0, tm372]
        · -- F, b1 (halting)
          simp [toCfg, toSd_cons, urun, sstep, hzne, cR_idx, evSt6, evBit, tag, single, hpop1,
              tm372]
      · -- Nat.beq n 0 = true
        have hzeq : is_zero (cn n) = true := by rw [is_zero_cn, hz]
        simp [toCfg, toSd, toRun, urun, sstep, hzeq]

theorem csstep_spec (st : CState) :
    (ev_cfg [] (fun _ => default) (toCfg st)) [tm372]⊢* (ev_cfg [] (fun _ =>
        default) (toCfg (csstep st))) := by
  rw [toCfg_csstep]
  exact urun_spec 1 (toCfg st) [] (fun _ => default)

theorem cstep2n_spec (k : Nat) (st : CState) :
    (ev_cfg [] (fun _ => default) (toCfg st)) [tm372]⊢* (ev_cfg [] (fun _ =>
        default) (toCfg (cstep2n k st))) := by
  induction k generalizing st with
  | zero => exact csstep_spec st
  | succ k ih =>
    simp only [cstep2n]
    have h1 := ih st
    rcases hst : cstep2n k st with ⟨d, q, l, r⟩
    rw [hst] at h1
    exact stepStar_trans h1 (ih (.mk d q l r))

def csstepN : Nat → CState → CState
  | 0, st => st
  | k + 1, st => csstepN k (csstep st)

theorem csstepN_spec (k : Nat) (st : CState) :
    (ev_cfg [] (fun _ => default) (toCfg st)) [tm372]⊢*
      (ev_cfg [] (fun _ => default) (toCfg (csstepN k st))) := by
  induction k generalizing st with
  | zero => exact ⟨0, rfl⟩
  | succ k ih => exact stepStar_trans (csstep_spec st) (ih (csstep st))

theorem chain_cstep2n (k : Nat) (s1 s2 s3 : CState)
    (h1 : cstep2n k s1 = s2)
    (h2 : (ev_cfg [] (fun _ => default) (toCfg s2)) [tm372]⊢* (ev_cfg [] (fun _ =>
        default) (toCfg s3))) :
    (ev_cfg [] (fun _ => default) (toCfg s1)) [tm372]⊢* (ev_cfg [] (fun _ => default) (toCfg s3)) :=
        by
  have hc := cstep2n_spec k s1
  rw [h1] at hc
  exact stepStar_trans hc h2

theorem step_to_Gc (extra m : Nat) (rem r Rs : List run) (nus : List (List Nat))
    (h1 : sd_eqb (norm_sd ((0, cn (extra + 3)) :: rem)) (norm_sd ((0, cn extra) :: (0,
        cn 3) :: rem)) = true)
    (h2 : urun 1 (.Lc D ([(0, cn extra)], .TV 0) (r, .T0)) = .Lc D ([], .TV 0) (Rs, .T0))
    (h3 : sd_eqb (norm_sd ((0,
        cn 3) :: rem)) (norm_sd (chs_runs (rep .U0 m) nus (blk1 .P0 ++ lw 0))) = true) :
    ((ev_runs [] ((0, cn (extra + 3)) :: rem) default) <{{D}} (evR [] r)) [tm372]⊢*
      Gc (rep .U0 m, .P0, 0) nus (evR [] Rs) := by
  have heq1 : ev_runs [] ((0, cn (extra + 3)) :: rem) default =
      ev_runs [] [(0, cn extra)] (ev_runs [] ((0, cn 3) :: rem) default) := by
    rw [← ev_runs_app]
    exact norm_runs_eq h1
  have heq2 : ev_runs [] ((0, cn 3) :: rem) default = chs (rep .U0 m) nus (b1s .P0 (LWs 0)) := by
    rw [b1s_lws_eq, ← chs_runs_spec]
    exact norm_runs_eq h3
  rw [heq1, heq2]
  have hu := urun_spec 1 (.Lc D ([(0, cn extra)], .TV 0) (r, .T0)) []
    (fun _ => chs (rep .U0 m) nus (b1s .P0 (LWs 0)))
  rw [h2] at hu
  exact hu

theorem run_concrete_interval (m : Nat) (nus : List (List Nat)) (prog : List instr) (Rs Re : List
    run) (T F_cnt : Nat)
    (hm : 2 ≤ m) (hlen : nus.length = m)
    (heT : 2 * T + 5 = 3 ^ (m + 2))
    (heF : F_cnt = 81 * 3 ^ (m + 1) - 1 - T)
    (hp : prog_check prog Rs Re (cn T) (cn F_cnt) = true) :
    (Gc (rep .U0 m, .P0, 0) nus (evR [] Rs)) [tm372]⊢⁺
      ((ev_runs [] [(0, cn 1), (0, cn (2 + 4 * rtop nus 0))]
        (chs (rep .U0 m) (rshift nus 0) (b1s .P0 (LWs 0)))) {{B}}> (evR [] Re)) := by
  have hint : (Gc (rep .U0 m, .P0, 0) nus (evR [] Rs)) [tm372]⊢*
      (Gc (rep .D0 m, .PD0, 80) nus (evR [] Re)) := by
    refine interval_tm m nus (evR [] Rs) (evR [] Re) hm hlen ?_
    intro T' hT'
    have hTeq : T' = T := by omega
    subst hTeq
    rw [← heF]
    exact prog_check_spec hp []
  have hrec : (Gc (rep .D0 m, .PD0, 80) nus (evR [] Re)) [tm372]⊢⁺
      ((chs (rep .D2 m) nus (b1s .PD2 (LWs 81))) {{B}}> (evR [] Re)) :=
    record_visit m nus (evR [] Re) hlen
  have htot := stepStar_stepPlus_trans hint hrec
  have hreg := regroup nus 0 (b1s .PD2 (LWs 81)) (b1s .P0 (LWs 0)) regroup_b1
  rw [hlen] at hreg
  rw [hreg] at htot
  exact htot

theorem Gc_to_after (m : Nat) (nus : List (List Nat)) (prog : List instr) (Rs Re : List run) (T
    F_cnt : Nat)
    (l_after r_after : List CRun)
    (hm : 2 ≤ m) (hlen : nus.length = m)
    (heT : 2 * T + 5 = 3 ^ (m + 2))
    (heF : F_cnt = 81 * 3 ^ (m + 1) - 1 - T)
    (hp : prog_check prog Rs Re (cn T) (cn F_cnt) = true)
    (h_out_L : sd_eqb (norm_sd ([(0, cn 1), (0, cn (2 + 4 * rtop nus 0))] ++
            chs_runs (rep .U0 m) (rshift nus 0) (blk1 .P0 ++ lw 0)))
          (norm_sd (l_after.map toRun)) = true)
    (h_out_R : r_after.map toRun = Re) :
    (Gc (rep .U0 m, .P0, 0) nus (evR [] Rs)) [tm372]⊢⁺
      ev_cfg [] (fun _ => default) (toCfg (.mk true .B l_after r_after)) := by
  have h1 := run_concrete_interval m nus prog Rs Re T F_cnt hm hlen heT heF hp
  have heqL : ev_runs [] [(0, cn 1), (0, cn (2 + 4 * rtop nus 0))]
      (chs (rep .U0 m) (rshift nus 0) (b1s .P0 (LWs 0))) =
      ev_runs [] (l_after.map toRun) default := by
    rw [b1s_lws_eq, ← chs_runs_spec, ← ev_runs_app]
    exact norm_runs_eq h_out_L
  change _ [tm372]⊢⁺ ((ev_runs [] (l_after.map toRun) default) {{B}}> (evR [] (r_after.map toRun)))
  rw [← heqL, h_out_R]
  exact h1

theorem interval_step_zero (m T F_cnt k : Nat) (l r l_after r_after : List CRun)
    (nus : List (List Nat)) (prog : List instr) (Rs Re : List run) (st_next : CState)
    (h_in_L : sd_eqb (norm_sd (l.map toRun)) (norm_sd (chs_runs (rep .U0 m) nus (blk1 .P0 ++
        lw 0))) = true)
    (h_in_R : r.map toRun = Rs)
    (hm : 2 ≤ m) (hlen : nus.length = m)
    (heT : 2 * T + 5 = 3 ^ (m + 2))
    (heF : F_cnt = 81 * 3 ^ (m + 1) - 1 - T)
    (hp : prog_check prog Rs Re (cn T) (cn F_cnt) = true)
    (h_out_L : sd_eqb (norm_sd ([(0, cn 1), (0, cn (2 + 4 * rtop nus 0))] ++
            chs_runs (rep .U0 m) (rshift nus 0) (blk1 .P0 ++ lw 0)))
          (norm_sd (l_after.map toRun)) = true)
    (h_out_R : r_after.map toRun = Re)
    (hk : csstepN k (.mk true .B l_after r_after) = st_next) :
    (ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r))) [tm372]⊢⁺
      (ev_cfg [] (fun _ => default) (toCfg st_next)) := by
  have heqL : ev_runs [] (l.map toRun) default = chs (rep .U0 m) nus (b1s .P0 (LWs 0)) := by
    rw [b1s_lws_eq, ← chs_runs_spec]
    exact norm_runs_eq h_in_L
  have hin : ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r)) =
      Gc (rep .U0 m, .P0, 0) nus (evR [] Rs) := by
    change ((ev_runs [] (l.map toRun) default) <{{D}} (evR [] (r.map toRun))) = _
    rw [heqL, h_in_R]
    rfl
  rw [hin]
  have hmid :=
      Gc_to_after m nus prog Rs Re T F_cnt l_after r_after hm hlen heT heF hp h_out_L h_out_R
  have hout := csstepN_spec k (.mk true .B l_after r_after)
  rw [hk] at hout
  exact stepPlus_stepStar_trans hmid hout

theorem interval_step_pos (extra m T F_cnt k : Nat) (l r l_after r_after : List CRun)
    (nus : List (List Nat)) (prog : List instr) (Rs Re : List run) (st_next : CState)
    (h_l : l.map toRun = (0, cn (extra + 3)) :: (l.tail.map toRun))
    (h1 : sd_eqb (norm_sd ((0, cn (extra + 3)) :: (l.tail.map toRun)))
          (norm_sd ((0, cn extra) :: (0, cn 3) :: (l.tail.map toRun))) = true)
    (h2 : urun 1 (.Lc D ([(0, cn extra)], .TV 0) (r.map toRun, .T0)) = .Lc D ([], .TV 0) (Rs, .T0))
    (h3 : sd_eqb (norm_sd ((0, cn 3) :: (l.tail.map toRun)))
          (norm_sd (chs_runs (rep .U0 m) nus (blk1 .P0 ++ lw 0))) = true)
    (hm : 2 ≤ m) (hlen : nus.length = m)
    (heT : 2 * T + 5 = 3 ^ (m + 2))
    (heF : F_cnt = 81 * 3 ^ (m + 1) - 1 - T)
    (hp : prog_check prog Rs Re (cn T) (cn F_cnt) = true)
    (h_out_L : sd_eqb (norm_sd ([(0, cn 1), (0, cn (2 + 4 * rtop nus 0))] ++
            chs_runs (rep .U0 m) (rshift nus 0) (blk1 .P0 ++ lw 0)))
          (norm_sd (l_after.map toRun)) = true)
    (h_out_R : r_after.map toRun = Re)
    (hk : csstepN k (.mk true .B l_after r_after) = st_next) :
    (ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r))) [tm372]⊢⁺
      (ev_cfg [] (fun _ => default) (toCfg st_next)) := by
  have hin : ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r)) =
      ((ev_runs [] ((0,
          cn (extra + 3)) :: (l.tail.map toRun)) default) <{{D}} (evR [] (r.map toRun))) := by
    change ((ev_runs [] (l.map toRun) default) <{{D}} (evR [] (r.map toRun))) = _
    rw [h_l]
  rw [hin]
  have hpre := step_to_Gc extra m (l.tail.map toRun) (r.map toRun) Rs nus h1 h2 h3
  have hmid :=
      Gc_to_after m nus prog Rs Re T F_cnt l_after r_after hm hlen heT heF hp h_out_L h_out_R
  have hout := csstepN_spec k (.mk true .B l_after r_after)
  rw [hk] at hout
  exact stepPlus_stepStar_trans (stepStar_stepPlus_trans hpre hmid) hout

theorem final_to_cfgI (extra : Nat) (l r : List CRun) (nus28 : List (List Nat))
    (h_l : l.map toRun = (0, cn (extra + 3)) :: (l.tail.map toRun))
    (h1 : sd_eqb (norm_sd ((0, cn (extra + 3)) :: (l.tail.map toRun)))
          (norm_sd ((0, cn extra) :: (0, cn 3) :: (l.tail.map toRun))) = true)
    (h2 : urun 1 (.Lc D ([(0, cn extra)], .TV 0) (r.map toRun, .T0)) =
          .Lc D ([], .TV 0) (Rs_r5.map (fun x => (x.1, cn (evN [0] x.2))), .T0))
    (h3 : sd_eqb (norm_sd ((0, cn 3) :: (l.tail.map toRun)))
          (norm_sd (chs_runs (rep .U0 6) nus28 (blk1 .P0 ++ lw 0))) = true)
    (hlen : nus28.length = 6) :
    (ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r))) [tm372]⊢*
      cfgI (.C5, 2, 0, nus28) := by
  have hin : ev_cfg [] (fun _ => default) (toCfg (.mk false .D l r)) =
      ((ev_runs [] ((0,
          cn (extra + 3)) :: (l.tail.map toRun)) default) <{{D}} (evR [] (r.map toRun))) := by
    change ((ev_runs [] (l.map toRun) default) <{{D}} (evR [] (r.map toRun))) = _
    rw [h_l]
  rw [hin]
  have hpre := step_to_Gc extra 6 (l.tail.map toRun) (r.map toRun)
    (Rs_r5.map (fun x => (x.1, cn (evN [0] x.2)))) nus28 h1 h2 h3
  rw [b28_right] at hpre
  rw [cfgI, Gc, Rs, hlen]
  exact hpre

theorem isNotHalt_of_reach_cfgI (s : ist) (hinit : (init []) [tm372]⊢* (cfgI s)) (hs : Inv s) :
    IsNotHalt tm372 := by
  refine IsNotHalt.of_reachesPlus_invariant (M := tm372) (P :=
      fun x => ∃ s', x = cfgI s' ∧ Inv s') hinit ⟨s, rfl, hs⟩ ?_
  rintro x ⟨s', rfl, hs'⟩
  rcases inv_step s' hs' with ⟨s'', hstep, hinv''⟩
  exact ⟨cfgI s'', hstep, s'', rfl, hinv''⟩


def Rs_c1 : List run := [(1, cn 6445), (1, cn 1)]
def Re_c1 : List run := [(0, cn 4), (1, cn 6800), (0, cn 19318), (1, cn 1)]
def r_after_c1 : List CRun := [.mk .b0 4, .mk .b1 6800, .mk .b0 19318, .mk .b1 1]
def prog_c1 : List instr :=
    [.IJump true (cn 29), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 1609), .ISingle false, .ISingle false, .ISingle false]
theorem int_c1 : prog_check prog_c1 Rs_c1 Re_c1 (cn 119) (cn 6441) = true := by decide +kernel

def Rs_c2 : List run := [(0, cn 24908), (1, cn 7), (1, cn 6800), (0, cn 19329), (0, cn 2)]
def Re_c2 : List run := [(0, cn 24908), (1, cn 8), (0, cn 361), (0, cn 71921), (0, cn 2)]
def r_after_c2 : List CRun := [.mk .b0 24908, .mk .b1 8, .mk .b0 361, .mk .b0 71921, .mk .b0 2]
def prog_c2 : List instr :=
    [.IJump true (cn 29), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .IJump false (cn 1610)]
theorem int_c2 : prog_check prog_c2 Rs_c2 Re_c2 (cn 119) (cn 6441) = true := by decide +kernel

def Rs_c3 : List run :=
    [(0, cn 8276), (1, cn 24911), (1, cn 7), (1, cn 361), (1, cn 71936), (0, cn 2)]
def Re_c3 : List run :=
    [(0, cn 8276), (1, cn 24912), (0, cn 74808), (1, cn 3), (1, cn 19321), (1, cn 1)]
def r_after_c3 : List CRun :=
    [.mk .b0 8276, .mk .b1 24912, .mk .b0 74808, .mk .b1 3, .mk .b1 19321, .mk .b1 1]
def prog_c3 : List instr :=
    [.IJump true (cn 29), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 1609), .ISingle false, .ISingle false, .ISingle false]
theorem int_c3 : prog_check prog_c3 Rs_c3 Re_c3 (cn 119) (cn 6441) = true := by decide +kernel

def Rs_c4 : List run :=
    [(0, cn 2732), (1, cn 8279), (1, cn 24912), (0, cn 74808), (1, cn 4), (0, cn 19330)]
def Re_c4 : List run :=
    [(0, cn 2732), (1, cn 8280), (0, cn 24912), (1, cn 74807), (1, cn 7), (1, cn 20408), (0,
    cn 57957), (0, cn 2)]
def r_after_c4 : List CRun :=
    [.mk .b0 2732, .mk .b1 8280, .mk .b0 24912, .mk .b1 74807, .mk .b1 7, .mk .b1 20408,
    .mk .b0 57957, .mk .b0 2]
def prog_c4 : List instr :=
    [.IJump true (cn 29), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 1609), .ISingle false, .ISingle false, .ISingle false]
theorem int_c4 : prog_check prog_c4 Rs_c4 Re_c4 (cn 119) (cn 6441) = true := by decide +kernel

def Rs_c5 : List run := [(0, cn 74804), (1, cn 7), (1, cn 20407), (1, cn 57965), (1, cn 1)]
def Re_c5 : List run := [(0, cn 74804), (1, cn 7), (1, cn 1093), (1, cn 215768), (0, cn 2)]
def r_after_c5 : List CRun := [.mk .b0 74804, .mk .b1 7, .mk .b1 1093, .mk .b1 215768, .mk .b0 2]
def prog_c5 : List instr :=
    [.IJump true (cn 90), .ISingle true, .ISingle true, .ISingle false, .IJump false (cn 4829),
    .ISingle false, .ISingle false, .ISingle false]
theorem int_c5 : prog_check prog_c5 Rs_c5 Re_c5 (cn 362) (cn 19320) = true := by decide +kernel

def Rs_c6 : List run := [(0, cn 24908), (1, cn 74807), (1, cn 8), (0, cn 1088), (1, cn 215797)]
def Re_c6 : List run := [(0, cn 24908), (1, cn 74808), (0, cn 224496), (1, cn 4), (0, cn 57958)]
def r_after_c6 : List CRun :=
    [.mk .b0 24908, .mk .b1 74808, .mk .b0 224496, .mk .b1 4, .mk .b0 57958]
def prog_c6 : List instr :=
    [.IJump true (cn 90), .ISingle true, .ISingle true, .ISingle false, .ISingle false,
    .IJump false (cn 4829), .ISingle false, .ISingle false]
theorem int_c6 : prog_check prog_c6 Rs_c6 Re_c6 (cn 362) (cn 19320) = true := by decide +kernel

def Rs_c7 : List run := [(1, cn 57961), (1, cn 1)]
def Re_c7 : List run := [(0, cn 4), (1, cn 61232), (0, cn 173866), (1, cn 1)]
def r_after_c7 : List CRun := [.mk .b0 4, .mk .b1 61232, .mk .b0 173866, .mk .b1 1]
def prog_c7 : List instr :=
    [.IJump true (cn 272), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 14488), .ISingle false, .ISingle false, .ISingle false]
theorem int_c7 : prog_check prog_c7 Rs_c7 Re_c7 (cn 1091) (cn 57957) = true := by decide +kernel

def Rs_c8 : List run := [(0, cn 224492), (1, cn 7), (1, cn 61232), (0, cn 173877), (0, cn 2)]
def Re_c8 : List run := [(0, cn 224492), (1, cn 8), (0, cn 3277), (0, cn 647345), (0, cn 2)]
def r_after_c8 : List CRun := [.mk .b0 224492, .mk .b1 8, .mk .b0 3277, .mk .b0 647345, .mk .b0 2]
def prog_c8 : List instr :=
    [.IJump true (cn 272), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .IJump false (cn 14489)]
theorem int_c8 : prog_check prog_c8 Rs_c8 Re_c8 (cn 1091) (cn 57957) = true := by decide +kernel

def Rs_c9 : List run :=
    [(0, cn 74804), (1, cn 224495), (1, cn 7), (1, cn 3277), (1, cn 647360), (0, cn 2)]
def Re_c9 : List run :=
    [(0, cn 74804), (1, cn 224496), (0, cn 673560), (1, cn 3), (1, cn 173869), (1, cn 1)]
def r_after_c9 : List CRun :=
    [.mk .b0 74804, .mk .b1 224496, .mk .b0 673560, .mk .b1 3, .mk .b1 173869, .mk .b1 1]
def prog_c9 : List instr :=
    [.IJump true (cn 272), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 14488), .ISingle false, .ISingle false, .ISingle false]
theorem int_c9 : prog_check prog_c9 Rs_c9 Re_c9 (cn 1091) (cn 57957) = true := by decide +kernel

def Rs_c10 : List run :=
    [(0, cn 24908), (1, cn 74807), (1, cn 224496), (0, cn 673560), (1, cn 4), (0, cn 173878)]
def Re_c10 : List run :=
    [(0, cn 24908), (1, cn 74808), (0, cn 224496), (1, cn 673559), (1, cn 7), (1, cn 183704), (0,
    cn 521601), (0, cn 2)]
def r_after_c10 : List CRun :=
    [.mk .b0 24908, .mk .b1 74808, .mk .b0 224496, .mk .b1 673559, .mk .b1 7, .mk .b1 183704,
    .mk .b0 521601, .mk .b0 2]
def prog_c10 : List instr :=
    [.IJump true (cn 272), .ISingle true, .ISingle true, .ISingle true, .ISingle false,
    .ISingle false, .IJump false (cn 14488), .ISingle false, .ISingle false, .ISingle false]
theorem int_c10 : prog_check prog_c10 Rs_c10 Re_c10 (cn 1091) (cn 57957) = true := by decide +kernel

def Rs_c11 : List run := [(0, cn 673556), (1, cn 7), (1, cn 183703), (1, cn 521609), (1, cn 1)]
def Re_c11 : List run := [(0, cn 673556), (1, cn 7), (1, cn 9841), (1, cn 1942040), (0, cn 2)]
def r_after_c11 : List CRun := [.mk .b0 673556, .mk .b1 7, .mk .b1 9841, .mk .b1 1942040, .mk .b0 2]
def prog_c11 : List instr :=
    [.IJump true (cn 819), .ISingle true, .ISingle true, .ISingle false, .IJump false (cn 43466),
    .ISingle false, .ISingle false, .ISingle false]
theorem int_c11 : prog_check prog_c11 Rs_c11 Re_c11 (cn 3278) (cn 173868) = true := by
  decide +kernel

def st372_init : CState := .mk true .A [] []
def st372_0 : CState := .mk true .A [] []
def st372_1 : CState :=
    .mk false .A [.mk .b0 1, .mk .b0 502, .mk .b1 752, .mk .b0 6, .mk .b1 2736, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 15, .mk .b0 7, .mk .b0 1,
    .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1]
def st372_2 : CState :=
    .mk true .B [.mk .b1 1, .mk .b1 229, .mk .b1 8, .mk .b0 2734, .mk .b1 972, .mk .b0 36,
    .mk .b1 40, .mk .b0 35, .mk .b0 43, .mk .b0 24, .mk .b1 16, .mk .b0 7, .mk .b0 3, .mk .b0 2,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b1 6454, .mk .b0 2]
def st372_3 : CState :=
    .mk true .A [.mk .b0 1, .mk .b0 39, .mk .b0 36, .mk .b1 44, .mk .b0 22, .mk .b1 16, .mk .b0 8,
    .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 2, .mk .b1 4, .mk .b0 1,
    .mk .b0 5, .mk .b0 2] [.mk .b0 34, .mk .b1 972, .mk .b0 2736, .mk .b1 8279, .mk .b1 7,
    .mk .b1 2264, .mk .b0 734]
def st372_4 : CState :=
    .mk true .F [.mk .b0 1, .mk .b0 8279, .mk .b0 2736, .mk .b1 972, .mk .b0 35, .mk .b0 39,
    .mk .b0 36, .mk .b1 44, .mk .b0 22, .mk .b1 16, .mk .b0 8, .mk .b1 4, .mk .b0 3, .mk .b0 3,
    .mk .b0 2, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b0 6,
    .mk .b1 2264, .mk .b0 5433, .mk .b0 2]
def st372_5 : CState :=
    .mk false .D [.mk .b1 11510, .mk .b0 1676, .mk .b1 8, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 14, .mk .b1 8, .mk .b0 4,
    .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 1,
    .mk .b0 5, .mk .b0 2] [.mk .b1 1]
def st372_6 : CState :=
    .mk false .D [.mk .b1 18150, .mk .b0 848, .mk .b1 8, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 38, .mk .b1 36, .mk .b0 44, .mk .b1 24, .mk .b0 13, .mk .b0 9, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 3,
    .mk .b0 3, .mk .b0 2] [.mk .b1 1, .mk .b1 1]
def st372_7 : CState :=
    .mk true .B [.mk .b0 2737, .mk .b0 972, .mk .b1 36, .mk .b0 39, .mk .b0 35, .mk .b0 43,
    .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 8277,
    .mk .b1 8, .mk .b0 13, .mk .b0 24809, .mk .b0 2]
def st372_8 : CState :=
    .mk false .D [.mk .b1 3888, .mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973,
    .mk .b0 36, .mk .b1 40, .mk .b0 34, .mk .b1 44, .mk .b0 24, .mk .b1 16, .mk .b0 6, .mk .b1 4,
    .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3,
    .mk .b0 2, .mk .b1 4, .mk .b0 2] [.mk .b1 1, .mk .b1 1]
def st372_9 : CState :=
    .mk false .D [.mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 34, .mk .b1 44,
    .mk .b0 24, .mk .b1 16, .mk .b0 7, .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b1 8280,
    .mk .b0 24912, .mk .b1 4, .mk .b0 5861, .mk .b0 2]
def st372_10 : CState :=
    .mk true .B [.mk .b1 8280, .mk .b0 2734, .mk .b1 972, .mk .b0 36, .mk .b1 40, .mk .b0 35,
    .mk .b0 43, .mk .b0 24, .mk .b1 16, .mk .b0 7, .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 2,
    .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b0 24912, .mk .b1 4, .mk .b0 6354, .mk .b1 1]
def st372_11 : CState :=
    .mk true .B [.mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 33,
    .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 7, .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 3,
    .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b0 24912, .mk .b1 4, .mk .b0 6414, .mk .b1 1]
def st372_12 : CState :=
    .mk false .A [.mk .b0 1, .mk .b0 3, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1,
    .mk .b1 5, .mk .b1 16, .mk .b0 24, .mk .b1 43, .mk .b1 35, .mk .b1 40, .mk .b0 36, .mk .b1 971,
    .mk .b1 2735, .mk .b1 8280, .mk .b0 24912, .mk .b1 4, .mk .b0 6442]
def st372_13 : CState :=
    .mk false .D [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 6445, .mk .b1 1]

theorem step372_0 : cstep2n 15 st372_0 = st372_1 := by decide +kernel
theorem step372_1 : cstep2n 15 st372_1 = st372_2 := by decide +kernel
theorem step372_2 : cstep2n 15 st372_2 = st372_3 := by decide +kernel
theorem step372_3 : cstep2n 15 st372_3 = st372_4 := by decide +kernel
theorem step372_4 : cstep2n 15 st372_4 = st372_5 := by decide +kernel
theorem step372_5 : cstep2n 15 st372_5 = st372_6 := by decide +kernel
theorem step372_6 : cstep2n 15 st372_6 = st372_7 := by decide +kernel
theorem step372_7 : cstep2n 15 st372_7 = st372_8 := by decide +kernel
theorem step372_8 : cstep2n 14 st372_8 = st372_9 := by decide +kernel
theorem step372_9 : cstep2n 12 st372_9 = st372_10 := by decide +kernel
theorem step372_10 : cstep2n 9 st372_10 = st372_11 := by decide +kernel
theorem step372_11 : cstep2n 8 st372_11 = st372_12 := by decide +kernel
theorem step372_12 : cstep2n 5 st372_12 = st372_13 := by decide +kernel

theorem stem_372 : (ev_cfg [] (fun _ => default) (toCfg st372_init)) [tm372]⊢*
    (ev_cfg [] (fun _ => default) (toCfg st372_13)) := by
  have h13 : (ev_cfg [] (fun _ => default) (toCfg st372_13)) [tm372]⊢*
      (ev_cfg [] (fun _ => default) (toCfg st372_13)) := ⟨0, rfl⟩
  have h12 := chain_cstep2n 5 st372_12 st372_13 st372_13 step372_12 h13
  have h11 := chain_cstep2n 8 st372_11 st372_12 st372_13 step372_11 h12
  have h10 := chain_cstep2n 9 st372_10 st372_11 st372_13 step372_10 h11
  have h9 := chain_cstep2n 12 st372_9 st372_10 st372_13 step372_9 h10
  have h8 := chain_cstep2n 14 st372_8 st372_9 st372_13 step372_8 h9
  have h7 := chain_cstep2n 15 st372_7 st372_8 st372_13 step372_7 h8
  have h6 := chain_cstep2n 15 st372_6 st372_7 st372_13 step372_6 h7
  have h5 := chain_cstep2n 15 st372_5 st372_6 st372_13 step372_5 h6
  have h4 := chain_cstep2n 15 st372_4 st372_5 st372_13 step372_4 h5
  have h3 := chain_cstep2n 15 st372_3 st372_4 st372_13 step372_3 h4
  have h2 := chain_cstep2n 15 st372_2 st372_3 st372_13 step372_2 h3
  have h1 := chain_cstep2n 15 st372_1 st372_2 st372_13 step372_1 h2
  have h0 := chain_cstep2n 15 st372_0 st372_1 st372_13 step372_0 h1
  exact h0

def l372_in1 : List CRun :=
    [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in1 : List CRun := [.mk .b1 6445, .mk .b1 1]
def nus372_1 : List (List Nat) := [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 3, 1, 0]]
def l372_after1 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int1 : CState := .mk false .D l372_in1 r372_in1
def l372_in2 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in2 : List CRun := [.mk .b1 7, .mk .b1 6800, .mk .b0 19329, .mk .b0 2]
def nus372_2 : List (List Nat) := [[2069, 683, 242, 8], [9, 8, 10, 5], [3, 1, 0, 0]]
def l372_after2 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 17, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int2 : CState := .mk false .D l372_in2 r372_in2
def l372_in3 : List CRun :=
    [.mk .b0 8279, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44,
    .mk .b0 21, .mk .b0 17, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in3 : List CRun := [.mk .b1 24911, .mk .b1 7, .mk .b1 361, .mk .b1 71936, .mk .b0 2]
def nus372_3 : List (List Nat) := [[683, 242, 8, 9], [8, 10, 5, 3], [1, 0, 0, 0]]
def l372_after3 : List CRun :=
    [.mk .b0 1, .mk .b0 2737, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44,
    .mk .b1 24, .mk .b0 13, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int3 : CState := .mk false .D l372_in3 r372_in3
def l372_in4 : List CRun :=
    [.mk .b0 2735, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24,
    .mk .b0 13, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in4 : List CRun := [.mk .b1 8279, .mk .b1 24912, .mk .b0 74808, .mk .b1 4, .mk .b0 19330]
def nus372_4 : List (List Nat) := [[242, 8, 9, 8], [10, 5, 3, 1], [0, 0, 0, 0]]
def l372_after4 : List CRun :=
    [.mk .b0 1, .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16,
    .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def st372_int4 : CState := .mk false .D l372_in4 r372_in4
def l372_in5 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in5 : List CRun := [.mk .b1 7, .mk .b1 20407, .mk .b1 57965, .mk .b1 1]
def nus372_5 : List (List Nat) :=
    [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 3, 1, 0], [0, 0, 0, 0]]
def l372_after5 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int5 : CState := .mk false .D l372_in5 r372_in5
def l372_in6 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in6 : List CRun := [.mk .b1 74807, .mk .b1 8, .mk .b0 1088, .mk .b1 215797]
def nus372_6 : List (List Nat) := [[2069, 683, 242, 8], [9, 8, 10, 5], [3, 1, 0, 0], [0, 0, 0, 0]]
def l372_after6 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 17, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int6 : CState := .mk false .D l372_in6 r372_in6
def l372_in7 : List CRun :=
    [.mk .b0 3, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44, .mk .b0 21, .mk .b0 17, .mk .b0 8,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in7 : List CRun := [.mk .b1 57961, .mk .b1 1]
def nus372_7 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 242, 8, 9], [8, 10, 5, 3], [1, 0, 0, 0], [0, 0, 0, 0]]
def l372_after7 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 13, .mk .b0 9,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int7 : CState := .mk false .D l372_in7 r372_in7
def l372_in8 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 13, .mk .b0 9, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in8 : List CRun := [.mk .b1 7, .mk .b1 61232, .mk .b0 173877, .mk .b0 2]
def nus372_8 : List (List Nat) :=
    [[18701, 6227, 2069, 683], [242, 8, 9, 8], [10, 5, 3, 1], [0, 0, 0, 0], [0, 0, 0, 0]]
def l372_after8 : List CRun :=
    [.mk .b0 1, .mk .b0 74809, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int8 : CState := .mk false .D l372_in8 r372_in8
def l372_in9 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 16, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in9 : List CRun := [.mk .b1 224495, .mk .b1 7, .mk .b1 3277, .mk .b1 647360, .mk .b0 2]
def nus372_9 : List (List Nat) :=
    [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 3, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l372_after9 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int9 : CState := .mk false .D l372_in9 r372_in9
def l372_in10 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 16, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r372_in10 : List CRun :=
    [.mk .b1 74807, .mk .b1 224496, .mk .b0 673560, .mk .b1 4, .mk .b0 173878]
def nus372_10 : List (List Nat) :=
    [[2069, 683, 242, 8], [9, 8, 10, 5], [3, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l372_after10 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 17, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int10 : CState := .mk false .D l372_in10 r372_in10
def l372_in11 : List CRun :=
    [.mk .b0 673559, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44, .mk .b0 21, .mk .b0 17, .mk .b0 8,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in11 : List CRun := [.mk .b1 7, .mk .b1 183703, .mk .b1 521609, .mk .b1 1]
def nus372_11 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 242, 8, 9], [8, 10, 5, 3], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0,
    0, 0]]
def l372_after11 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 13, .mk .b0 9,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st372_int11 : CState := .mk false .D l372_in11 r372_in11
def l372_in12 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 13, .mk .b0 9, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r372_in12 : List CRun := [.mk .b1 673559, .mk .b1 8, .mk .b0 9836, .mk .b1 1942069]
def st372_int12 : CState := .mk false .D l372_in12 r372_in12

theorem istep372_1 : (ev_cfg [] (fun _ => default) (toCfg st372_int1)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int2)) := by
  exact interval_step_zero 3 119 6441 51 l372_in1 r372_in1
    l372_after1 r_after_c1 nus372_1 prog_c1 Rs_c1 Re_c1 st372_int2
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_2 : (ev_cfg [] (fun _ => default) (toCfg st372_int2)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int3)) := by
  exact interval_step_pos 24908 3 119 6441 72 l372_in2 r372_in2
    l372_after2 r_after_c2 nus372_2 prog_c2 Rs_c2 Re_c2 st372_int3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_3 : (ev_cfg [] (fun _ => default) (toCfg st372_int3)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int4)) := by
  exact interval_step_pos 8276 3 119 6441 56 l372_in3 r372_in3
    l372_after3 r_after_c3 nus372_3 prog_c3 Rs_c3 Re_c3 st372_int4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_4 : (ev_cfg [] (fun _ => default) (toCfg st372_int4)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int5)) := by
  exact interval_step_pos 2732 3 119 6441 43 l372_in4 r372_in4
    l372_after4 r_after_c4 nus372_4 prog_c4 Rs_c4 Re_c4 st372_int5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_5 : (ev_cfg [] (fun _ => default) (toCfg st372_int5)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int6)) := by
  exact interval_step_pos 74804 4 362 19320 111 l372_in5 r372_in5
    l372_after5 r_after_c5 nus372_5 prog_c5 Rs_c5 Re_c5 st372_int6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_6 : (ev_cfg [] (fun _ => default) (toCfg st372_int6)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int7)) := by
  exact interval_step_pos 24908 4 362 19320 14 l372_in6 r372_in6
    l372_after6 r_after_c6 nus372_6 prog_c6 Rs_c6 Re_c6 st372_int7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_7 : (ev_cfg [] (fun _ => default) (toCfg st372_int7)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int8)) := by
  exact interval_step_zero 5 1091 57957 51 l372_in7 r372_in7
    l372_after7 r_after_c7 nus372_7 prog_c7 Rs_c7 Re_c7 st372_int8
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c7 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_8 : (ev_cfg [] (fun _ => default) (toCfg st372_int8)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int9)) := by
  exact interval_step_pos 224492 5 1091 57957 72 l372_in8 r372_in8
    l372_after8 r_after_c8 nus372_8 prog_c8 Rs_c8 Re_c8 st372_int9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_9 : (ev_cfg [] (fun _ => default) (toCfg st372_int9)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int10)) := by
  exact interval_step_pos 74804 5 1091 57957 56 l372_in9 r372_in9
    l372_after9 r_after_c9 nus372_9 prog_c9 Rs_c9 Re_c9 st372_int10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c9
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_10 : (ev_cfg [] (fun _ => default) (toCfg st372_int10)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int11)) := by
  exact interval_step_pos 24908 5 1091 57957 43 l372_in10 r372_in10
    l372_after10 r_after_c10 nus372_10 prog_c10 Rs_c10 Re_c10 st372_int11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c10
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_11 : (ev_cfg [] (fun _ => default) (toCfg st372_int11)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st372_int12)) := by
  exact interval_step_pos 673556 6 3278 173868 111 l372_in11 r372_in11
    l372_after11 r_after_c11 nus372_11 prog_c11 Rs_c11 Re_c11 st372_int12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c11
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep372_12 : (ev_cfg [] (fun _ => default) (toCfg st372_int12)) [tm372]⊢*
    cfgI (.C5, 2, 0, nus28_372) := by
  exact final_to_cfgI 224492 l372_in12 r372_in12 nus28_372
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

theorem reach_cfgI_372 : (ev_cfg [] (fun _ => default) (toCfg st372_init)) [tm372]⊢⁺
    cfgI (.C5, 2, 0, nus28_372) := by
  have h0 : st372_13 = st372_int1 := rfl
  have hs := stem_372
  rw [h0] at hs
  have p1 := stepStar_stepPlus_trans hs istep372_1
  have p2 := stepPlus_trans p1 istep372_2
  have p3 := stepPlus_trans p2 istep372_3
  have p4 := stepPlus_trans p3 istep372_4
  have p5 := stepPlus_trans p4 istep372_5
  have p6 := stepPlus_trans p5 istep372_6
  have p7 := stepPlus_trans p6 istep372_7
  have p8 := stepPlus_trans p7 istep372_8
  have p9 := stepPlus_trans p8 istep372_9
  have p10 := stepPlus_trans p9 istep372_10
  have p11 := stepPlus_trans p10 istep372_11
  exact stepPlus_stepStar_trans p11 istep372_12

def st557_init : CState := .mk true .B [] []
def st557_0 : CState := .mk true .B [] []
def st557_1 : CState :=
    .mk false .E [.mk .b0 2737, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44,
    .mk .b1 24, .mk .b0 19, .mk .b0 7, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 1,
    .mk .b0 5, .mk .b0 2] [.mk .b1 5, .mk .b1 752, .mk .b0 502, .mk .b1 1]
def st557_2 : CState :=
    .mk true .A [.mk .b0 6453, .mk .b0 230, .mk .b1 8, .mk .b0 2734, .mk .b1 972, .mk .b0 36,
    .mk .b1 40, .mk .b0 35, .mk .b0 43, .mk .b0 24, .mk .b1 20, .mk .b0 7, .mk .b0 3, .mk .b0 2,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 2] []
def st557_3 : CState :=
    .mk false .D [.mk .b0 7, .mk .b0 8279, .mk .b0 2736, .mk .b1 972, .mk .b0 34, .mk .b1 40,
    .mk .b0 36, .mk .b1 44, .mk .b0 22, .mk .b1 20, .mk .b0 8, .mk .b1 4, .mk .b0 2, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 2264,
    .mk .b0 734]
def st557_4 : CState :=
    .mk false .C [.mk .b1 40, .mk .b0 36, .mk .b1 44, .mk .b0 22, .mk .b1 20, .mk .b0 8, .mk .b1 4,
    .mk .b0 3, .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b0 34, .mk .b1 972, .mk .b0 2736, .mk .b1 8279, .mk .b1 7, .mk .b1 2264,
    .mk .b0 5433, .mk .b0 2]
def st557_5 : CState :=
    .mk true .B [.mk .b0 2737, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44,
    .mk .b1 24, .mk .b0 18, .mk .b1 8, .mk .b0 4, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 2,
    .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 8277, .mk .b1 8,
    .mk .b0 1676, .mk .b1 11509]
def st557_6 : CState :=
    .mk true .A [.mk .b0 846, .mk .b1 8, .mk .b0 8277, .mk .b0 2737, .mk .b0 972, .mk .b1 36,
    .mk .b0 38, .mk .b1 36, .mk .b0 44, .mk .b1 24, .mk .b0 17, .mk .b0 9, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b1 18152, .mk .b0 2]
def st557_7 : CState :=
    .mk true .B [.mk .b1 36, .mk .b0 39, .mk .b0 35, .mk .b0 43, .mk .b0 24, .mk .b1 20, .mk .b0 5,
    .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b0 972, .mk .b1 2735, .mk .b1 8279, .mk .b1 8,
    .mk .b0 13, .mk .b0 24809, .mk .b0 2]
def st557_8 : CState :=
    .mk true .C [.mk .b1 1, .mk .b1 3887, .mk .b1 4, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733,
    .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 34, .mk .b1 44, .mk .b0 24, .mk .b1 20, .mk .b0 6,
    .mk .b1 4, .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 3,
    .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 2] []
def st557_9 : CState :=
    .mk true .C [.mk .b1 1, .mk .b1 5861, .mk .b1 4, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733,
    .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 34, .mk .b1 44, .mk .b0 24, .mk .b1 20, .mk .b0 7,
    .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 3,
    .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 2] []
def st557_10 : CState :=
    .mk false .D [.mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 35, .mk .b0 43, .mk .b0 24, .mk .b1 20, .mk .b0 7, .mk .b0 3, .mk .b0 4, .mk .b1 4,
    .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b1 4, .mk .b0 6354, .mk .b1 1]
def st557_11 : CState :=
    .mk true .A [.mk .b0 971, .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24,
    .mk .b1 20, .mk .b0 7, .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b1 2735, .mk .b1 8280,
    .mk .b0 24912, .mk .b1 4, .mk .b0 6414, .mk .b1 1]
def st557_12 : CState :=
    .mk false .A [.mk .b0 1, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1, .mk .b1 1, .mk .b1 3,
    .mk .b1 7, .mk .b1 20, .mk .b0 24, .mk .b1 43, .mk .b1 35, .mk .b1 40, .mk .b0 36, .mk .b1 971,
    .mk .b1 2735, .mk .b1 8280, .mk .b0 24912, .mk .b1 4, .mk .b0 6442]
def st557_13 : CState :=
    .mk false .D [.mk .b1 1, .mk .b1 6443, .mk .b1 4, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733,
    .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5,
    .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1]
def st557_14 : CState :=
    .mk true .C [.mk .b1 6444, .mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973,
    .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5,
    .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b0 2]
def st557_15 : CState :=
    .mk false .D [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 6445, .mk .b1 1]

theorem step557_0 : cstep2n 15 st557_0 = st557_1 := by decide +kernel
theorem step557_1 : cstep2n 15 st557_1 = st557_2 := by decide +kernel
theorem step557_2 : cstep2n 15 st557_2 = st557_3 := by decide +kernel
theorem step557_3 : cstep2n 15 st557_3 = st557_4 := by decide +kernel
theorem step557_4 : cstep2n 15 st557_4 = st557_5 := by decide +kernel
theorem step557_5 : cstep2n 15 st557_5 = st557_6 := by decide +kernel
theorem step557_6 : cstep2n 15 st557_6 = st557_7 := by decide +kernel
theorem step557_7 : cstep2n 15 st557_7 = st557_8 := by decide +kernel
theorem step557_8 : cstep2n 14 st557_8 = st557_9 := by decide +kernel
theorem step557_9 : cstep2n 12 st557_9 = st557_10 := by decide +kernel
theorem step557_10 : cstep2n 9 st557_10 = st557_11 := by decide +kernel
theorem step557_11 : cstep2n 8 st557_11 = st557_12 := by decide +kernel
theorem step557_12 : cstep2n 5 st557_12 = st557_13 := by decide +kernel
theorem step557_13 : cstep2n 2 st557_13 = st557_14 := by decide +kernel
theorem step557_14 : cstep2n 1 st557_14 = st557_15 := by decide +kernel

theorem stem_557 : (ev_cfg [] (fun _ => default) (toCfg st557_init)) [tm372]⊢*
    (ev_cfg [] (fun _ => default) (toCfg st557_15)) := by
  have h15 : (ev_cfg [] (fun _ => default) (toCfg st557_15)) [tm372]⊢*
      (ev_cfg [] (fun _ => default) (toCfg st557_15)) := ⟨0, rfl⟩
  have h14 := chain_cstep2n 1 st557_14 st557_15 st557_15 step557_14 h15
  have h13 := chain_cstep2n 2 st557_13 st557_14 st557_15 step557_13 h14
  have h12 := chain_cstep2n 5 st557_12 st557_13 st557_15 step557_12 h13
  have h11 := chain_cstep2n 8 st557_11 st557_12 st557_15 step557_11 h12
  have h10 := chain_cstep2n 9 st557_10 st557_11 st557_15 step557_10 h11
  have h9 := chain_cstep2n 12 st557_9 st557_10 st557_15 step557_9 h10
  have h8 := chain_cstep2n 14 st557_8 st557_9 st557_15 step557_8 h9
  have h7 := chain_cstep2n 15 st557_7 st557_8 st557_15 step557_7 h8
  have h6 := chain_cstep2n 15 st557_6 st557_7 st557_15 step557_6 h7
  have h5 := chain_cstep2n 15 st557_5 st557_6 st557_15 step557_5 h6
  have h4 := chain_cstep2n 15 st557_4 st557_5 st557_15 step557_4 h5
  have h3 := chain_cstep2n 15 st557_3 st557_4 st557_15 step557_3 h4
  have h2 := chain_cstep2n 15 st557_2 st557_3 st557_15 step557_2 h3
  have h1 := chain_cstep2n 15 st557_1 st557_2 st557_15 step557_1 h2
  have h0 := chain_cstep2n 15 st557_0 st557_1 st557_15 step557_0 h1
  exact h0

def l557_in1 : List CRun :=
    [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in1 : List CRun := [.mk .b1 6445, .mk .b1 1]
def nus557_1 : List (List Nat) := [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 4, 1, 0]]
def l557_after1 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int1 : CState := .mk false .D l557_in1 r557_in1
def l557_in2 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in2 : List CRun := [.mk .b1 7, .mk .b1 6800, .mk .b0 19329, .mk .b0 2]
def nus557_2 : List (List Nat) := [[2069, 683, 242, 8], [9, 8, 10, 5], [4, 1, 0, 0]]
def l557_after2 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 21, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int2 : CState := .mk false .D l557_in2 r557_in2
def l557_in3 : List CRun :=
    [.mk .b0 8279, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44,
    .mk .b0 21, .mk .b0 21, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in3 : List CRun := [.mk .b1 24911, .mk .b1 7, .mk .b1 361, .mk .b1 71936, .mk .b0 2]
def nus557_3 : List (List Nat) := [[683, 242, 8, 9], [8, 10, 5, 4], [1, 0, 0, 0]]
def l557_after3 : List CRun :=
    [.mk .b0 1, .mk .b0 2737, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44,
    .mk .b1 24, .mk .b0 17, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int3 : CState := .mk false .D l557_in3 r557_in3
def l557_in4 : List CRun :=
    [.mk .b0 2735, .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24,
    .mk .b0 17, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in4 : List CRun := [.mk .b1 8279, .mk .b1 24912, .mk .b0 74808, .mk .b1 4, .mk .b0 19330]
def nus557_4 : List (List Nat) := [[242, 8, 9, 8], [10, 5, 4, 1], [0, 0, 0, 0]]
def l557_after4 : List CRun :=
    [.mk .b0 1, .mk .b0 973, .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20,
    .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def st557_int4 : CState := .mk false .D l557_in4 r557_in4
def l557_in5 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in5 : List CRun := [.mk .b1 7, .mk .b1 20407, .mk .b1 57965, .mk .b1 1]
def nus557_5 : List (List Nat) :=
    [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 4, 1, 0], [0, 0, 0, 0]]
def l557_after5 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int5 : CState := .mk false .D l557_in5 r557_in5
def l557_in6 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in6 : List CRun := [.mk .b1 74807, .mk .b1 8, .mk .b0 1088, .mk .b1 215797]
def nus557_6 : List (List Nat) := [[2069, 683, 242, 8], [9, 8, 10, 5], [4, 1, 0, 0], [0, 0, 0, 0]]
def l557_after6 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 21, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int6 : CState := .mk false .D l557_in6 r557_in6
def l557_in7 : List CRun :=
    [.mk .b0 3, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44, .mk .b0 21, .mk .b0 21, .mk .b0 8,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in7 : List CRun := [.mk .b1 57961, .mk .b1 1]
def nus557_7 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 242, 8, 9], [8, 10, 5, 4], [1, 0, 0, 0], [0, 0, 0, 0]]
def l557_after7 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 17, .mk .b0 9,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int7 : CState := .mk false .D l557_in7 r557_in7
def l557_in8 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 17, .mk .b0 9, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in8 : List CRun := [.mk .b1 7, .mk .b1 61232, .mk .b0 173877, .mk .b0 2]
def nus557_8 : List (List Nat) :=
    [[18701, 6227, 2069, 683], [242, 8, 9, 8], [10, 5, 4, 1], [0, 0, 0, 0], [0, 0, 0, 0]]
def l557_after8 : List CRun :=
    [.mk .b0 1, .mk .b0 74809, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int8 : CState := .mk false .D l557_in8 r557_in8
def l557_in9 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 973, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 45, .mk .b0 24, .mk .b1 20, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in9 : List CRun := [.mk .b1 224495, .mk .b1 7, .mk .b1 3277, .mk .b1 647360, .mk .b0 2]
def nus557_9 : List (List Nat) :=
    [[6227, 2069, 683, 242], [8, 9, 8, 10], [5, 4, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l557_after9 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int9 : CState := .mk false .D l557_in9 r557_in9
def l557_in10 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 969, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 41, .mk .b0 25, .mk .b0 20, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r557_in10 : List CRun :=
    [.mk .b1 74807, .mk .b1 224496, .mk .b0 673560, .mk .b1 4, .mk .b0 173878]
def nus557_10 : List (List Nat) :=
    [[2069, 683, 242, 8], [9, 8, 10, 5], [4, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l557_after10 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 44, .mk .b0 21, .mk .b0 21, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int10 : CState := .mk false .D l557_in10 r557_in10
def l557_in11 : List CRun :=
    [.mk .b0 673559, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 972, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 44, .mk .b0 21, .mk .b0 21, .mk .b0 8,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in11 : List CRun := [.mk .b1 7, .mk .b1 183703, .mk .b1 521609, .mk .b1 1]
def nus557_11 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 242, 8, 9], [8, 10, 5, 4], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0,
    0, 0]]
def l557_after11 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 972, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 17, .mk .b0 9,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st557_int11 : CState := .mk false .D l557_in11 r557_in11
def l557_in12 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 972,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 44, .mk .b1 24, .mk .b0 17, .mk .b0 9, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r557_in12 : List CRun := [.mk .b1 673559, .mk .b1 8, .mk .b0 9836, .mk .b1 1942069]
def st557_int12 : CState := .mk false .D l557_in12 r557_in12

theorem istep557_1 : (ev_cfg [] (fun _ => default) (toCfg st557_int1)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int2)) := by
  exact interval_step_zero 3 119 6441 51 l557_in1 r557_in1
    l557_after1 r_after_c1 nus557_1 prog_c1 Rs_c1 Re_c1 st557_int2
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_2 : (ev_cfg [] (fun _ => default) (toCfg st557_int2)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int3)) := by
  exact interval_step_pos 24908 3 119 6441 72 l557_in2 r557_in2
    l557_after2 r_after_c2 nus557_2 prog_c2 Rs_c2 Re_c2 st557_int3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_3 : (ev_cfg [] (fun _ => default) (toCfg st557_int3)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int4)) := by
  exact interval_step_pos 8276 3 119 6441 56 l557_in3 r557_in3
    l557_after3 r_after_c3 nus557_3 prog_c3 Rs_c3 Re_c3 st557_int4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_4 : (ev_cfg [] (fun _ => default) (toCfg st557_int4)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int5)) := by
  exact interval_step_pos 2732 3 119 6441 43 l557_in4 r557_in4
    l557_after4 r_after_c4 nus557_4 prog_c4 Rs_c4 Re_c4 st557_int5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_5 : (ev_cfg [] (fun _ => default) (toCfg st557_int5)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int6)) := by
  exact interval_step_pos 74804 4 362 19320 111 l557_in5 r557_in5
    l557_after5 r_after_c5 nus557_5 prog_c5 Rs_c5 Re_c5 st557_int6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_6 : (ev_cfg [] (fun _ => default) (toCfg st557_int6)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int7)) := by
  exact interval_step_pos 24908 4 362 19320 14 l557_in6 r557_in6
    l557_after6 r_after_c6 nus557_6 prog_c6 Rs_c6 Re_c6 st557_int7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_7 : (ev_cfg [] (fun _ => default) (toCfg st557_int7)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int8)) := by
  exact interval_step_zero 5 1091 57957 51 l557_in7 r557_in7
    l557_after7 r_after_c7 nus557_7 prog_c7 Rs_c7 Re_c7 st557_int8
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c7 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_8 : (ev_cfg [] (fun _ => default) (toCfg st557_int8)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int9)) := by
  exact interval_step_pos 224492 5 1091 57957 72 l557_in8 r557_in8
    l557_after8 r_after_c8 nus557_8 prog_c8 Rs_c8 Re_c8 st557_int9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_9 : (ev_cfg [] (fun _ => default) (toCfg st557_int9)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int10)) := by
  exact interval_step_pos 74804 5 1091 57957 56 l557_in9 r557_in9
    l557_after9 r_after_c9 nus557_9 prog_c9 Rs_c9 Re_c9 st557_int10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c9
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_10 : (ev_cfg [] (fun _ => default) (toCfg st557_int10)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int11)) := by
  exact interval_step_pos 24908 5 1091 57957 43 l557_in10 r557_in10
    l557_after10 r_after_c10 nus557_10 prog_c10 Rs_c10 Re_c10 st557_int11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c10
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_11 : (ev_cfg [] (fun _ => default) (toCfg st557_int11)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st557_int12)) := by
  exact interval_step_pos 673556 6 3278 173868 111 l557_in11 r557_in11
    l557_after11 r_after_c11 nus557_11 prog_c11 Rs_c11 Re_c11 st557_int12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c11
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep557_12 : (ev_cfg [] (fun _ => default) (toCfg st557_int12)) [tm372]⊢*
    cfgI (.C5, 2, 0, nus28_557) := by
  exact final_to_cfgI 224492 l557_in12 r557_in12 nus28_557
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

theorem reach_cfgI_557 : (ev_cfg [] (fun _ => default) (toCfg st557_init)) [tm372]⊢⁺
    cfgI (.C5, 2, 0, nus28_557) := by
  have h0 : st557_15 = st557_int1 := rfl
  have hs := stem_557
  rw [h0] at hs
  have p1 := stepStar_stepPlus_trans hs istep557_1
  have p2 := stepPlus_trans p1 istep557_2
  have p3 := stepPlus_trans p2 istep557_3
  have p4 := stepPlus_trans p3 istep557_4
  have p5 := stepPlus_trans p4 istep557_5
  have p6 := stepPlus_trans p5 istep557_6
  have p7 := stepPlus_trans p6 istep557_7
  have p8 := stepPlus_trans p7 istep557_8
  have p9 := stepPlus_trans p8 istep557_9
  have p10 := stepPlus_trans p9 istep557_10
  have p11 := stepPlus_trans p10 istep557_11
  exact stepPlus_stepStar_trans p11 istep557_12


def st638_init : CState := .mk true .F [] []
def st638_0 : CState := .mk true .F [] []
def st638_1 : CState :=
    .mk false .A [.mk .b0 1, .mk .b0 35, .mk .b0 52, .mk .b1 8, .mk .b0 2, .mk .b1 4, .mk .b0 2,
    .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1, .mk .b1 37,
    .mk .b1 36, .mk .b0 936, .mk .b1 2735, .mk .b1 7, .mk .b1 752, .mk .b0 554]
def st638_2 : CState :=
    .mk true .B [.mk .b1 8, .mk .b0 2734, .mk .b1 936, .mk .b0 36, .mk .b1 40, .mk .b0 35,
    .mk .b0 51, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 1,
    .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b0 220, .mk .b1 6525]
def st638_3 : CState :=
    .mk false .D [.mk .b0 5, .mk .b0 8281, .mk .b0 2736, .mk .b1 936, .mk .b0 34, .mk .b1 40,
    .mk .b0 36, .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 3, .mk .b0 3,
    .mk .b0 1, .mk .b0 5, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 2264,
    .mk .b0 782]
def st638_4 : CState :=
    .mk false .D [.mk .b1 1, .mk .b1 5481, .mk .b1 2264, .mk .b0 5, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 936, .mk .b0 34, .mk .b1 40, .mk .b0 36, .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 3,
    .mk .b0 3, .mk .b0 2] [.mk .b1 1]
def st638_5 : CState :=
    .mk true .B [.mk .b1 1668, .mk .b0 9, .mk .b0 8277, .mk .b0 2737, .mk .b0 936, .mk .b1 36,
    .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8, .mk .b0 3, .mk .b0 3, .mk .b0 4, .mk .b1 4,
    .mk .b0 3, .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 1, .mk .b0 5,
    .mk .b0 2] [.mk .b1 1, .mk .b1 11574, .mk .b0 2]
def st638_6 : CState :=
    .mk true .B [.mk .b1 1, .mk .b1 36, .mk .b0 52, .mk .b1 8, .mk .b0 2, .mk .b1 4, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 3,
    .mk .b0 3, .mk .b0 2] [.mk .b1 37, .mk .b1 36, .mk .b0 936, .mk .b1 2735, .mk .b1 8279,
    .mk .b1 8, .mk .b0 836, .mk .b1 18229]
def st638_7 : CState :=
    .mk true .A [.mk .b0 24872, .mk .b1 7, .mk .b1 8, .mk .b0 8277, .mk .b0 2737, .mk .b0 935,
    .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 2, .mk .b1 4,
    .mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 1]
def st638_8 : CState :=
    .mk false .D [.mk .b0 4, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 3,
    .mk .b0 3, .mk .b0 2, .mk .b1 4, .mk .b0 2] [.mk .b1 3, .mk .b1 3, .mk .b1 4, .mk .b0 8,
    .mk .b1 51, .mk .b1 35, .mk .b1 40, .mk .b0 36, .mk .b1 935, .mk .b1 2735, .mk .b1 8280,
    .mk .b0 24912, .mk .b1 4, .mk .b0 3930, .mk .b1 1]
def st638_9 : CState :=
    .mk true .B [.mk .b0 8, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 4, .mk .b1 4, .mk .b0 3,
    .mk .b0 3, .mk .b0 1, .mk .b0 5, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b1 51, .mk .b1 35, .mk .b1 40, .mk .b0 36, .mk .b1 935, .mk .b1 2735,
    .mk .b1 8280, .mk .b0 24912, .mk .b1 4, .mk .b0 5902]
def st638_10 : CState :=
    .mk false .D [.mk .b0 24912, .mk .b1 8280, .mk .b0 2735, .mk .b0 935, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 2, .mk .b1 4, .mk .b0 4, .mk .b1 4,
    .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 2] [.mk .b1 3, .mk .b1 6397, .mk .b1 1]
def st638_11 : CState :=
    .mk true .B [.mk .b1 1, .mk .b1 936, .mk .b0 36, .mk .b1 40, .mk .b0 34, .mk .b1 52, .mk .b0 8,
    .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 4, .mk .b1 4, .mk .b0 3, .mk .b0 3, .mk .b0 3,
    .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 3, .mk .b0 2] [.mk .b1 2733, .mk .b1 8280,
    .mk .b0 24912, .mk .b1 4, .mk .b0 6426, .mk .b1 1]
def st638_12 : CState :=
    .mk true .B [.mk .b0 2] [.mk .b1 3, .mk .b1 3, .mk .b1 3, .mk .b1 3, .mk .b1 3, .mk .b1 3,
    .mk .b1 3, .mk .b1 3, .mk .b1 3, .mk .b1 4, .mk .b0 4, .mk .b1 3, .mk .b1 3, .mk .b1 4,
    .mk .b0 8, .mk .b1 51, .mk .b1 35, .mk .b1 40, .mk .b0 36, .mk .b1 935, .mk .b1 2735,
    .mk .b1 8280, .mk .b0 24912, .mk .b1 4, .mk .b0 6442]
def st638_13 : CState :=
    .mk true .B [.mk .b1 4, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b0 6442]
def st638_14 : CState :=
    .mk true .C [.mk .b1 6444, .mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937,
    .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b0 2]
def st638_15 : CState :=
    .mk false .D [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2] [.mk .b1 6445, .mk .b1 1]

theorem step638_0 : cstep2n 15 st638_0 = st638_1 := by decide +kernel
theorem step638_1 : cstep2n 15 st638_1 = st638_2 := by decide +kernel
theorem step638_2 : cstep2n 15 st638_2 = st638_3 := by decide +kernel
theorem step638_3 : cstep2n 15 st638_3 = st638_4 := by decide +kernel
theorem step638_4 : cstep2n 15 st638_4 = st638_5 := by decide +kernel
theorem step638_5 : cstep2n 15 st638_5 = st638_6 := by decide +kernel
theorem step638_6 : cstep2n 15 st638_6 = st638_7 := by decide +kernel
theorem step638_7 : cstep2n 15 st638_7 = st638_8 := by decide +kernel
theorem step638_8 : cstep2n 14 st638_8 = st638_9 := by decide +kernel
theorem step638_9 : cstep2n 12 st638_9 = st638_10 := by decide +kernel
theorem step638_10 : cstep2n 8 st638_10 = st638_11 := by decide +kernel
theorem step638_11 : cstep2n 7 st638_11 = st638_12 := by decide +kernel
theorem step638_12 : cstep2n 6 st638_12 = st638_13 := by decide +kernel
theorem step638_13 : cstep2n 3 st638_13 = st638_14 := by decide +kernel
theorem step638_14 : cstep2n 1 st638_14 = st638_15 := by decide +kernel

theorem stem_638 : (ev_cfg [] (fun _ => default) (toCfg st638_init)) [tm372]⊢*
    (ev_cfg [] (fun _ => default) (toCfg st638_15)) := by
  have h15 : (ev_cfg [] (fun _ => default) (toCfg st638_15)) [tm372]⊢*
      (ev_cfg [] (fun _ => default) (toCfg st638_15)) := ⟨0, rfl⟩
  have h14 := chain_cstep2n 1 st638_14 st638_15 st638_15 step638_14 h15
  have h13 := chain_cstep2n 3 st638_13 st638_14 st638_15 step638_13 h14
  have h12 := chain_cstep2n 6 st638_12 st638_13 st638_15 step638_12 h13
  have h11 := chain_cstep2n 7 st638_11 st638_12 st638_15 step638_11 h12
  have h10 := chain_cstep2n 8 st638_10 st638_11 st638_15 step638_10 h11
  have h9 := chain_cstep2n 12 st638_9 st638_10 st638_15 step638_9 h10
  have h8 := chain_cstep2n 14 st638_8 st638_9 st638_15 step638_8 h9
  have h7 := chain_cstep2n 15 st638_7 st638_8 st638_15 step638_7 h8
  have h6 := chain_cstep2n 15 st638_6 st638_7 st638_15 step638_6 h7
  have h5 := chain_cstep2n 15 st638_5 st638_6 st638_15 step638_5 h6
  have h4 := chain_cstep2n 15 st638_4 st638_5 st638_15 step638_4 h5
  have h3 := chain_cstep2n 15 st638_3 st638_4 st638_15 step638_3 h4
  have h2 := chain_cstep2n 15 st638_2 st638_3 st638_15 step638_2 h3
  have h1 := chain_cstep2n 15 st638_1 st638_2 st638_15 step638_1 h2
  have h0 := chain_cstep2n 15 st638_0 st638_1 st638_15 step638_0 h1
  exact h0

def l638_in1 : List CRun :=
    [.mk .b0 3, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in1 : List CRun := [.mk .b1 6445, .mk .b1 1]
def nus638_1 : List (List Nat) := [[6227, 2069, 683, 233], [8, 9, 8, 12], [1, 0, 0, 0]]
def l638_after1 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int1 : CState := .mk false .D l638_in1 r638_in1
def l638_in2 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in2 : List CRun := [.mk .b1 7, .mk .b1 6800, .mk .b0 19329, .mk .b0 2]
def nus638_2 : List (List Nat) := [[2069, 683, 233, 8], [9, 8, 12, 1], [0, 0, 0, 0]]
def l638_after2 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int2 : CState := .mk false .D l638_in2 r638_in2
def l638_in3 : List CRun :=
    [.mk .b0 8279, .mk .b0 2736, .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 52,
    .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in3 : List CRun := [.mk .b1 24911, .mk .b1 7, .mk .b1 361, .mk .b1 71936, .mk .b0 2]
def nus638_3 : List (List Nat) := [[683, 233, 8, 9], [8, 12, 1, 0], [0, 0, 0, 0]]
def l638_after3 : List CRun :=
    [.mk .b0 1, .mk .b0 2737, .mk .b0 936, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52,
    .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int3 : CState := .mk false .D l638_in3 r638_in3
def l638_in4 : List CRun :=
    [.mk .b0 2735, .mk .b0 936, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in4 : List CRun := [.mk .b1 8279, .mk .b1 24912, .mk .b0 74808, .mk .b1 4, .mk .b0 19330]
def nus638_4 : List (List Nat) := [[233, 8, 9, 8], [12, 1, 0, 0], [0, 0, 0, 0]]
def l638_after4 : List CRun :=
    [.mk .b0 1, .mk .b0 937, .mk .b0 36, .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def st638_int4 : CState := .mk false .D l638_in4 r638_in4
def l638_in5 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in5 : List CRun := [.mk .b1 7, .mk .b1 20407, .mk .b1 57965, .mk .b1 1]
def nus638_5 : List (List Nat) :=
    [[6227, 2069, 683, 233], [8, 9, 8, 12], [1, 0, 0, 0], [0, 0, 0, 0]]
def l638_after5 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int5 : CState := .mk false .D l638_in5 r638_in5
def l638_in6 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in6 : List CRun := [.mk .b1 74807, .mk .b1 8, .mk .b0 1088, .mk .b1 215797]
def nus638_6 : List (List Nat) := [[2069, 683, 233, 8], [9, 8, 12, 1], [0, 0, 0, 0], [0, 0, 0, 0]]
def l638_after6 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int6 : CState := .mk false .D l638_in6 r638_in6
def l638_in7 : List CRun :=
    [.mk .b0 3, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in7 : List CRun := [.mk .b1 57961, .mk .b1 1]
def nus638_7 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 233, 8, 9], [8, 12, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l638_after7 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 936, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8, .mk .b0 1, .mk .b0 5,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int7 : CState := .mk false .D l638_in7 r638_in7
def l638_in8 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 936,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in8 : List CRun := [.mk .b1 7, .mk .b1 61232, .mk .b0 173877, .mk .b0 2]
def nus638_8 : List (List Nat) :=
    [[18701, 6227, 2069, 683], [233, 8, 9, 8], [12, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l638_after8 : List CRun :=
    [.mk .b0 1, .mk .b0 74809, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36,
    .mk .b1 40, .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int8 : CState := .mk false .D l638_in8 r638_in8
def l638_in9 : List CRun :=
    [.mk .b0 74807, .mk .b0 24912, .mk .b1 8280, .mk .b0 2733, .mk .b0 937, .mk .b0 36, .mk .b1 40,
    .mk .b0 33, .mk .b0 53, .mk .b0 8, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in9 : List CRun := [.mk .b1 224495, .mk .b1 7, .mk .b1 3277, .mk .b1 647360, .mk .b0 2]
def nus638_9 : List (List Nat) :=
    [[6227, 2069, 683, 233], [8, 9, 8, 12], [1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l638_after9 : List CRun :=
    [.mk .b0 1, .mk .b0 24913, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40,
    .mk .b1 36, .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int9 : CState := .mk false .D l638_in9 r638_in9
def l638_in10 : List CRun :=
    [.mk .b0 24911, .mk .b0 8280, .mk .b1 2736, .mk .b0 933, .mk .b0 37, .mk .b0 40, .mk .b1 36,
    .mk .b0 49, .mk .b0 9, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4,
    .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 5, .mk .b0 2]
def r638_in10 : List CRun :=
    [.mk .b1 74807, .mk .b1 224496, .mk .b0 673560, .mk .b1 4, .mk .b0 173878]
def nus638_10 : List (List Nat) :=
    [[2069, 683, 233, 8], [9, 8, 12, 1], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]
def l638_after10 : List CRun :=
    [.mk .b0 1, .mk .b0 8281, .mk .b0 2736, .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36,
    .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1,
    .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int10 : CState := .mk false .D l638_in10 r638_in10
def l638_in11 : List CRun :=
    [.mk .b0 673559, .mk .b0 224496, .mk .b1 74808, .mk .b0 24909, .mk .b0 8281, .mk .b0 2736,
    .mk .b1 936, .mk .b0 33, .mk .b0 41, .mk .b0 36, .mk .b1 52, .mk .b0 5, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in11 : List CRun := [.mk .b1 7, .mk .b1 183703, .mk .b1 521609, .mk .b1 1]
def nus638_11 : List (List Nat) :=
    [[56123, 18701, 6227, 2069], [683, 233, 8, 9], [8, 12, 1, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0,
    0, 0]]
def l638_after11 : List CRun :=
    [.mk .b0 1, .mk .b0 224497, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737,
    .mk .b0 936, .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8, .mk .b0 1, .mk .b0 5,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1,
    .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def st638_int11 : CState := .mk false .D l638_in11 r638_in11
def l638_in12 : List CRun :=
    [.mk .b0 224495, .mk .b0 74808, .mk .b1 24912, .mk .b0 8277, .mk .b0 2737, .mk .b0 936,
    .mk .b1 36, .mk .b0 37, .mk .b0 37, .mk .b0 52, .mk .b1 8, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4, .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 4,
    .mk .b1 4, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 6, .mk .b1 4, .mk .b0 1, .mk .b0 5,
    .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 1, .mk .b0 5, .mk .b0 2]
def r638_in12 : List CRun := [.mk .b1 673559, .mk .b1 8, .mk .b0 9836, .mk .b1 1942069]
def st638_int12 : CState := .mk false .D l638_in12 r638_in12

theorem istep638_1 : (ev_cfg [] (fun _ => default) (toCfg st638_int1)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int2)) := by
  exact interval_step_zero 3 119 6441 51 l638_in1 r638_in1
    l638_after1 r_after_c1 nus638_1 prog_c1 Rs_c1 Re_c1 st638_int2
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c1 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_2 : (ev_cfg [] (fun _ => default) (toCfg st638_int2)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int3)) := by
  exact interval_step_pos 24908 3 119 6441 72 l638_in2 r638_in2
    l638_after2 r_after_c2 nus638_2 prog_c2 Rs_c2 Re_c2 st638_int3
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c2
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_3 : (ev_cfg [] (fun _ => default) (toCfg st638_int3)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int4)) := by
  exact interval_step_pos 8276 3 119 6441 56 l638_in3 r638_in3
    l638_after3 r_after_c3 nus638_3 prog_c3 Rs_c3 Re_c3 st638_int4
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c3
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_4 : (ev_cfg [] (fun _ => default) (toCfg st638_int4)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int5)) := by
  exact interval_step_pos 2732 3 119 6441 43 l638_in4 r638_in4
    l638_after4 r_after_c4 nus638_4 prog_c4 Rs_c4 Re_c4 st638_int5
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c4
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_5 : (ev_cfg [] (fun _ => default) (toCfg st638_int5)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int6)) := by
  exact interval_step_pos 74804 4 362 19320 111 l638_in5 r638_in5
    l638_after5 r_after_c5 nus638_5 prog_c5 Rs_c5 Re_c5 st638_int6
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c5
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_6 : (ev_cfg [] (fun _ => default) (toCfg st638_int6)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int7)) := by
  exact interval_step_pos 24908 4 362 19320 14 l638_in6 r638_in6
    l638_after6 r_after_c6 nus638_6 prog_c6 Rs_c6 Re_c6 st638_int7
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c6
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_7 : (ev_cfg [] (fun _ => default) (toCfg st638_int7)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int8)) := by
  exact interval_step_zero 5 1091 57957 51 l638_in7 r638_in7
    l638_after7 r_after_c7 nus638_7 prog_c7 Rs_c7 Re_c7 st638_int8
    (by decide +kernel) (by decide +kernel) (by decide) (by decide)
    (by decide) (by decide) int_c7 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_8 : (ev_cfg [] (fun _ => default) (toCfg st638_int8)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int9)) := by
  exact interval_step_pos 224492 5 1091 57957 72 l638_in8 r638_in8
    l638_after8 r_after_c8 nus638_8 prog_c8 Rs_c8 Re_c8 st638_int9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c8
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_9 : (ev_cfg [] (fun _ => default) (toCfg st638_int9)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int10)) := by
  exact interval_step_pos 74804 5 1091 57957 56 l638_in9 r638_in9
    l638_after9 r_after_c9 nus638_9 prog_c9 Rs_c9 Re_c9 st638_int10
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c9
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_10 : (ev_cfg [] (fun _ => default) (toCfg st638_int10)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int11)) := by
  exact interval_step_pos 24908 5 1091 57957 43 l638_in10 r638_in10
    l638_after10 r_after_c10 nus638_10 prog_c10 Rs_c10 Re_c10 st638_int11
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c10
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_11 : (ev_cfg [] (fun _ => default) (toCfg st638_int11)) [tm372]⊢⁺
    (ev_cfg [] (fun _ => default) (toCfg st638_int12)) := by
  exact interval_step_pos 673556 6 3278 173868 111 l638_in11 r638_in11
    l638_after11 r_after_c11 nus638_11 prog_c11 Rs_c11 Re_c11 st638_int12
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide) (by decide) (by decide) (by decide) int_c11
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem istep638_12 : (ev_cfg [] (fun _ => default) (toCfg st638_int12)) [tm372]⊢*
    cfgI (.C5, 2, 0, nus28_638) := by
  exact final_to_cfgI 224492 l638_in12 r638_in12 nus28_638
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide)

theorem reach_cfgI_638 : (ev_cfg [] (fun _ => default) (toCfg st638_init)) [tm372]⊢⁺
    cfgI (.C5, 2, 0, nus28_638) := by
  have h0 : st638_15 = st638_int1 := rfl
  have hs := stem_638
  rw [h0] at hs
  have p1 := stepStar_stepPlus_trans hs istep638_1
  have p2 := stepPlus_trans p1 istep638_2
  have p3 := stepPlus_trans p2 istep638_3
  have p4 := stepPlus_trans p3 istep638_4
  have p5 := stepPlus_trans p4 istep638_5
  have p6 := stepPlus_trans p5 istep638_6
  have p7 := stepPlus_trans p6 istep638_7
  have p8 := stepPlus_trans p7 istep638_8
  have p9 := stepPlus_trans p8 istep638_9
  have p10 := stepPlus_trans p9 istep638_10
  have p11 := stepPlus_trans p10 istep638_11
  exact stepPlus_stepStar_trans p11 istep638_12


theorem neverHaltsFrom_of_reach_cfgI {c₀ : Cfg6} (s : ist)
    (hinit : c₀ [tm372]⊢* (cfgI s)) (hs : Inv s) :
    ∀ cfg : Cfg6, (c₀ [tm372]⊢* cfg) → (step tm372 cfg).isSome := by
  refine Counter.does_not_halt_of_invariant
    (Inv := fun x => ∃ s', x = cfgI s' ∧ Inv s')
    ⟨cfgI s, hinit, s, rfl, hs⟩ ?_
  rintro x ⟨s', rfl, hs'⟩
  rcases inv_step s' hs' with ⟨s'', hstep, hinv''⟩
  exact ⟨cfgI s'', hstep, s'', rfl, hinv''⟩

end

public section

theorem is_not_halt_from_0557 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{1}}> default) [target]⊢* cfg) →
      (step target cfg).isSome := by
  rw [target_eq_tm372]
  have hinit : ReachesStar tm372 ((default : ListBlank (Fin 2)) {{1}}> default)
      (cfgI (.C5, 2, 0, nus28_557)) := by
    have h0 : ((default : ListBlank (Fin 2)) {{1}}> default) =
        ev_cfg [] (fun _ => default) (toCfg st557_init) := rfl
    rw [h0]
    exact stepPlus_to_stepStar reach_cfgI_557
  exact neverHaltsFrom_of_reach_cfgI (.C5, 2, 0, nus28_557) hinit inv28_557

theorem is_not_halt_from_0638 :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      (((default : ListBlank (Fin 2)) {{5}}> default) [target]⊢* cfg) →
      (step target cfg).isSome := by
  rw [target_eq_tm372]
  have hinit : ReachesStar tm372 ((default : ListBlank (Fin 2)) {{5}}> default)
      (cfgI (.C5, 2, 0, nus28_638)) := by
    have h0 : ((default : ListBlank (Fin 2)) {{5}}> default) =
        ev_cfg [] (fun _ => default) (toCfg st638_init) := rfl
    rw [h0]
    exact stepPlus_to_stepStar reach_cfgI_638
  exact neverHaltsFrom_of_reach_cfgI (.C5, 2, 0, nus28_638) hinit inv28_638

theorem is_not_halt : IsNotHalt target := by
  rw [target_eq_tm372]
  have hinit : ReachesStar tm372 (init []) (cfgI (.C5, 2, 0, nus28_372)) := by
    have h0 : init [] = ev_cfg [] (fun _ => default) (toCfg st372_init) := rfl
    rw [h0]
    exact stepPlus_to_stepStar reach_cfgI_372
  exact isNotHalt_of_reach_cfgI (.C5, 2, 0, nus28_372) hinit inv28_372

end

end BusyBeaver.M_1RB0RF_1RC0RB_1LD0RA_1LE0LD_1RB0LC_1LAHHH
