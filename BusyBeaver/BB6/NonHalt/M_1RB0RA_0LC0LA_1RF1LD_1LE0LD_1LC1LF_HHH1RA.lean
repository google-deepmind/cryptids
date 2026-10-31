/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_HHH1RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 5, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

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

namespace M8
inductive St | A | B | C | D | E | F | H
  deriving DecidableEq, Repr
structure Cfg where
  st : St
  L : List Bool
  h : Bool
  R : List Bool
  deriving DecidableEq, Repr
def mR (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, w :: c.L, c.R.headD false, c.R.tail⟩
def mL (s : St) (w : Bool) (c : Cfg) : Cfg := ⟨s, c.L.tail, c.L.headD false, w :: c.R⟩
def step (c : Cfg) : Cfg :=
  match c.st, c.h with
  | .A, false => mR .B true c
  | .A, true  => mR .A false c
  | .B, false => mL .C false c
  | .B, true  => mL .A false c
  | .C, false => mR .F true c
  | .C, true  => mL .D true c
  | .D, false => mL .E true c
  | .D, true  => mL .D false c
  | .E, false => mL .C true c
  | .E, true  => mL .F true c
  | .F, false => { c with st := .H }
  | .F, true  => mR .A true c
  | .H, _     => c
def run : Nat -> Cfg -> Cfg
  | 0, c => c
  | n + 1, c => run n (step c)
theorem run_add (m n : Nat) (c : Cfg) : run (m + n) c = run n (run m c) := by
  induction m generalizing c with
  | zero => simp [run]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [run]
    exact ih (step c)
def halted (c : Cfg) : Prop := c.st = .H
def init : Cfg := ⟨.A, [], false, []⟩
theorem run_H (n : Nat) (c : Cfg) (h : c.st = .H) : run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [run]
    have : step c = c := by
      obtain ⟨s, L, x, R⟩ := c
      simp at h; subst h; cases x <;> rfl
    rw [this, ih]
end M8
namespace M8
def mvDir : St -> Bool -> Option Bool
  | .A, _ => some true
  | .B, _ => some false
  | .C, false => some true
  | .C, true => some false
  | .D, _ => some false
  | .E, _ => some false
  | .F, false => none
  | .F, true => some true
  | .H, _ => none
def stepB (c : Cfg) : Option Cfg :=
  match mvDir c.st c.h with
  | some true => if c.R.isEmpty then none else some (step c)
  | some false => if c.L.isEmpty then none else some (step c)
  | none => some (step c)
def runB : Nat -> Cfg -> Option Cfg
  | 0, c => some c
  | n + 1, c => (stepB c).bind (runB n)
def ext (c : Cfg) (Lt Rt : List Bool) : Cfg := ⟨c.st, c.L ++ Lt, c.h, c.R ++ Rt⟩
theorem stepB_frame {c c' : Cfg} (Lt Rt : List Bool) (h : stepB c = some c') :
    step (ext c Lt Rt) = ext c' Lt Rt := by
  obtain ⟨s, L, x, R⟩ := c
  cases s <;> cases x <;> simp only [stepB, mvDir] at h <;>
    first
    | (cases R with
        | nil => simp at h
        | cons r rs => simp at h; subst h; simp [ext, step, mR])
    | (cases L with
        | nil => simp at h
        | cons l ls => simp at h; subst h; simp [ext, step, mL])
    | (simp at h; subst h; simp [ext, step])
theorem runB_frame (n : Nat) (Lt Rt : List Bool) :
    ∀ {c c' : Cfg}, runB n c = some c' -> run n (ext c Lt Rt) = ext c' Lt Rt := by
  induction n with
  | zero => intro c c' h; simp [runB] at h; subst h; rfl
  | succ n ih =>
    intro c c' h
    simp only [runB, Option.bind_eq_some_iff] at h
    obtain ⟨c1, h1, h2⟩ := h
    show run n (step (ext c Lt Rt)) = _
    rw [stepB_frame Lt Rt h1]
    exact ih h2
theorem frame {n : Nat} {s s' : St} {L h R L' h' R'} (Lt Rt : List Bool)
    (hb : runB n ⟨s, L, h, R⟩ = some ⟨s', L', h', R'⟩) :
    run n ⟨s, L ++ Lt, h, R ++ Rt⟩ = ⟨s', L' ++ Lt, h', R' ++ Rt⟩ :=
  runB_frame n Lt Rt hb
end M8
namespace M8
def cons' : Bool -> List Bool -> List Bool
  | false, [] => []
  | x, t => x :: t
def trim : List Bool -> List Bool
  | [] => []
  | x :: xs => cons' x (trim xs)
@[simp] theorem trim_nil : trim [] = [] := rfl
@[simp] theorem trim_cons (x : Bool) (xs : List Bool) : trim (x :: xs) = cons' x (trim xs) := rfl
theorem trim_headD (l : List Bool) : (trim l).headD false = l.headD false := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [trim_cons, List.headD_cons]
    cases x <;> cases trim xs <;> rfl
theorem trim_tail (l : List Bool) : trim l.tail = (trim l).tail := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [trim_cons, List.tail_cons]
    cases x <;> cases trim xs <;> simp [cons']
def PE (c d : Cfg) : Prop := c.st = d.st /\ c.h = d.h /\ trim c.L = trim d.L /\ trim c.R = trim d.R
theorem PE.refl (c : Cfg) : PE c c := ⟨rfl, rfl, rfl, rfl⟩
theorem PE.symm {c d : Cfg} (h : PE c d) : PE d c := ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem PE.trans {c d e : Cfg} (h : PE c d) (h' : PE d e) : PE c e :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩
theorem PE_step {c d : Cfg} (h : PE c d) : PE (step c) (step d) := by
  obtain ⟨s, L, x, R⟩ := c
  obtain ⟨s', L', x', R'⟩ := d
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2
  have hL0 : L.headD false = L'.headD false := by rw [<- trim_headD, h3, trim_headD]
  have hR0 : R.headD false = R'.headD false := by rw [<- trim_headD, h4, trim_headD]
  have hL1 : trim L.tail = trim L'.tail := by rw [trim_tail, h3, trim_tail]
  have hR1 : trim R.tail = trim R'.tail := by rw [trim_tail, h4, trim_tail]
  cases s <;> cases x <;>
    simp only [step, mR, mL, PE, trim_cons, hL0, hR0, hL1, hR1, h3, h4, and_self]
theorem PE_run (n : Nat) {c d : Cfg} (h : PE c d) : PE (run n c) (run n d) := by
  induction n generalizing c d with
  | zero => exact h
  | succ n ih => exact ih (PE_step h)
theorem trim_blank (l : List Bool) (hl : ∀ x ∈ l, x = false) : trim l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := hl x (by simp)
    subst hx
    rw [trim_cons, ih (fun y hy => hl y (by simp [hy]))]; rfl
theorem trim_append_blank (l p : List Bool) (hp : ∀ x ∈ p, x = false) : trim (l ++ p) = trim l := by
  induction l with
  | nil => exact trim_blank p hp
  | cons x xs ih => simp [ih]
theorem trim_append_repl (l : List Bool) (n : Nat) : trim (l ++ List.replicate n false) = trim l :=
  trim_append_blank l _ (fun x hx => (List.mem_replicate.1 hx).2)
theorem PE_pad (s : St) (L R : List Bool) (h : Bool) (a b : Nat) :
    PE ⟨s, L ++ List.replicate a false, h, R ++ List.replicate b false⟩ ⟨s, L, h, R⟩ :=
  ⟨rfl, rfl, trim_append_repl L a, trim_append_repl R b⟩
theorem PE_halted {c d : Cfg} (h : PE c d) : halted c <-> halted d := by
  unfold halted; rw [h.1]
theorem trim_append_congr (p : List Bool) {l l' : List Bool} (h : trim l = trim l') :
    trim (p ++ l) = trim (p ++ l') := by
  induction p with
  | nil => exact h
  | cons x xs ih => simp [ih]
end M8
namespace M8
open List
def Lu : List Bool := [false, true, true, true]
def Rr : List Bool := [false, false, true, true]
def Mr : List Bool := [false, false, true, true, true, true]
def pw (l : List Bool) : Nat -> List Bool
  | 0 => []
  | n + 1 => l ++ pw l n
@[simp] theorem pw_zero (l : List Bool) : pw l 0 = [] := rfl
@[simp] theorem pw_succ (l : List Bool) (n : Nat) : pw l (n + 1) = l ++ pw l n := rfl
theorem pw_add (l : List Bool) (m n : Nat) : pw l (m + n) = pw l m ++ pw l n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, pw_succ, pw_succ, ih, List.append_assoc]
theorem pw_succ' (l : List Bool) (n : Nat) : pw l (n + 1) = pw l n ++ l := by
  rw [pw_add]; simp
def hc (P R : List Bool) : Cfg := ⟨.B, true :: P, true, [true, true] ++ R⟩
def dc (L R : List Bool) : Cfg := ⟨.D, L.tail, L.headD false, R⟩
def ac (L R : List Bool) : Cfg := ⟨.A, L, R.headD false, R.tail⟩
theorem dstep (L R : List Bool) : run 1 ⟨.D, L, true, R⟩ = dc L (false :: R) := rfl
theorem cstep (L R : List Bool) : run 1 ⟨.C, L, true, R⟩ = dc L (true :: R) := rfl
theorem astep (L R : List Bool) : run 1 ⟨.A, L, true, R⟩ = ac (false :: L) R := rfl
theorem restart (L R : List Bool) : run 1 (ac L (Lu ++ R)) = hc L R := rfl
theorem unit (P R : List Bool) : run 18 (hc P (Lu ++ R)) = hc (Rr ++ P) R := by
  have h := frame (n := 18) (s := .B) (s' := .B) (L := [true]) (h := true)
    (R := [true, true, false, true, true, true]) (L' := [true, false, false, true, true]) (h' := true)
    (R' := [true, true]) P R (by decide)
  simpa [hc, Lu, Rr] using h
theorem pass (P R : List Bool) :
    run 36 (hc (Rr ++ P) ([true, false] ++ false :: R)) = hc (Mr ++ P) (false :: R) := by
  have h := frame (n := 36) (s := .B) (s' := .B) (L := [true, false, false, true, true]) (h := true)
    (R := [true, true, true, false, false]) (L' := [true, false, false, true, true, true, true]) (h' := true)
    (R' := [true, true, false]) P R (by decide)
  simpa [hc, Mr, Rr] using h
theorem turn (P X : List Bool) :
    run 24 (hc P ([false, false] ++ X)) = dc P (Lu ++ [true, false] ++ X) := by
  have h := frame (n := 23) (s := .B) (s' := .D) (L := [true]) (h := true)
    (R := [true, true, false, false]) (L' := []) (h' := true)
    (R' := [true, true, true, true, false]) P X (by decide)
  rw [show 24 = 23 + 1 from rfl, run_add]
  simp only [hc, List.cons_append, List.nil_append] at h ⊢
  rw [h, dstep]; rfl
theorem lunit (L R : List Bool) : run 4 (dc (Rr ++ L) R) = dc L (Lu ++ R) := by
  have h := frame (n := 3) (s := .D) (s' := .D) (L := [false, true, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [true, true, true]) L R (by decide)
  rw [show 4 = 3 + 1 from rfl, run_add]
  simp only [dc, Rr, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, dstep]; rfl
theorem lmark (L R : List Bool) : run 6 (dc (Mr ++ L) R) = dc L ([false, false] ++ Lu ++ R) := by
  have h := frame (n := 5) (s := .D) (s' := .D) (L := [false, true, true, true, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [false, false, true, true, true]) L R (by decide)
  rw [show 6 = 5 + 1 from rfl, run_add]
  simp only [dc, Mr, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, dstep]; rfl
theorem rsweep (n : Nat) (P R : List Bool) :
    run (18 * n) (hc P (pw Lu n ++ R)) = hc (pw Rr n ++ P) R := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, run_add, pw_succ, List.append_assoc, unit, ih,
      pw_succ', List.append_assoc]
theorem lsweep (n : Nat) (L R : List Bool) :
    run (4 * n) (dc (pw Rr n ++ L) R) = dc L (pw Lu n ++ R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, run_add, pw_succ, List.append_assoc, lunit, ih, pw_succ', List.append_assoc]
end M8
namespace M8
open List
inductive Dg | z | o | t
  deriving DecidableEq, Repr
def rdig : Dg -> List Bool
  | .z => [false, false, false]
  | .o => [false, true, true]
  | .t => [false, false, true]
def Sr (ds : List Dg) : List Bool := ds.flatMap rdig
@[simp] theorem Sr_nil : Sr [] = [] := rfl
@[simp] theorem Sr_cons (d : Dg) (ds : List Dg) : Sr (d :: ds) = rdig d ++ Sr ds := by
  simp [Sr]
def inc : List Dg -> List Dg
  | [] => [.o]
  | .z :: r => .o :: r
  | .o :: r => .t :: r
  | .t :: r => .z :: inc r
def tz : List Dg -> Nat
  | .t :: r => tz r + 1
  | _ => 0
def lowOk : List Dg -> Bool
  | [] => false
  | .t :: r => lowOk r
  | _ => true
def val : List Dg -> Nat
  | [] => 0
  | d :: r => (match d with | .z => 0 | .o => 1 | .t => 2) + 3 * val r
theorem val_inc (ds : List Dg) : val (inc ds) = val ds + 1 := by
  induction ds with
  | nil => rfl
  | cons d r ih => cases d <;> simp [inc, val, ih] <;> omega
theorem cdig2 (L R : List Bool) : run 3 (dc (rdig .t ++ L) R) = dc L ([true, true, true] ++ R) := by
  have h := frame (n := 2) (s := .D) (s' := .C) (L := [false, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [true, true]) L R (by decide)
  rw [show 3 = 2 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, cstep]; rfl
theorem cdig0 (L R : List Bool) : run 5 (dc (rdig .z ++ L) R) = ac (rdig .o ++ L) R := by
  have h := frame (n := 4) (s := .D) (s' := .A) (L := [false, false]) (h := false)
    (R := []) (L' := [true, true]) (h' := true) (R' := []) L R (by decide)
  rw [show 5 = 4 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, astep]
theorem cdig1 (L R : List Bool) : run 5 (dc (rdig .o ++ L) R) = ac (rdig .t ++ L) R := by
  have h := frame (n := 4) (s := .D) (s' := .A) (L := [true, true]) (h := false)
    (R := []) (L' := [false, true]) (h' := true) (R' := []) L R (by decide)
  rw [show 5 = 4 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, astep]
theorem erase (L R : List Bool) : run 3 (ac L ([true, true, true] ++ R)) = ac ([false, false, false] ++ L) R := by
  show run 1 (run 1 (run 1 ⟨.A, L, true, [true, true] ++ R⟩)) = _
  rfl
theorem cnt (ds : List Dg) (hok : lowOk ds = true) (L R : List Bool) :
    run (6 * tz ds + 5) (dc (Sr ds ++ L) R) = ac (Sr (inc ds) ++ L) R := by
  induction ds generalizing R with
  | nil => simp [lowOk] at hok
  | cons d r ih =>
    cases d with
    | z => simpa [tz, inc, List.append_assoc] using cdig0 (Sr r ++ L) R
    | o => simpa [tz, inc, List.append_assoc] using cdig1 (Sr r ++ L) R
    | t =>
      simp only [lowOk] at hok
      simp only [tz, inc, Sr_cons, List.append_assoc]
      rw [show 6 * (tz r + 1) + 5 = 3 + (6 * tz r + 5) + 3 by omega, run_add, run_add, cdig2,
        ih hok, erase]
      rfl
theorem cnt_top (n : Nat) (L R : List Bool) :
    run (6 * n + 5) (dc (Sr (List.replicate n .t) ++ [false, false, false] ++ L) R)
      = ac (Sr (inc (List.replicate n .t)) ++ L) R := by
  have key : ∀ n, Sr (List.replicate n .t) ++ [false, false, false] = Sr (List.replicate n .t ++ [.z])
      /\ tz (List.replicate n .t ++ [.z]) = n /\ lowOk (List.replicate n .t ++ [.z]) = true
      /\ inc (List.replicate n .t ++ [.z]) = inc (List.replicate n .t) := by
    intro n
    induction n with
    | zero => simp [Sr, rdig, tz, lowOk, inc]
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.replicate_succ, List.cons_append, Sr_cons, List.append_assoc] at h1 ⊢
        rw [h1]
      · simp [List.replicate_succ, tz, h2]
      · simp [List.replicate_succ, lowOk, h3]
      · simp [List.replicate_succ, inc, h4]
  obtain ⟨h1, h2, h3, h4⟩ := key n
  rw [h1, <- h4, <- cnt _ h3, h2]
end M8
namespace M8
open List
def rtt : List Nat -> List Bool -> List Bool
  | [], R => R
  | b :: bs, R => [true, false] ++ pw Lu b ++ rtt bs R
def Q : List Nat -> List Bool -> List Bool
  | [], P => P
  | b :: bs, P => Q bs (pw Rr (b - 1) ++ Mr ++ P)
def E : List Nat -> List Bool
  | [] => []
  | b :: bs => [false, false] ++ pw Lu b ++ E bs
def swT : List Nat -> Nat
  | [] => 0
  | b :: bs => 36 + 18 * b + swT bs
def lqT : List Nat -> Nat
  | [] => 0
  | b :: bs => lqT bs + 4 * (b - 1) + 6
theorem swT_eq (bs : List Nat) : swT bs = 36 * bs.length + 18 * bs.sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [swT, ih]; omega
theorem lqT_eq (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) : lqT bs = 4 * bs.sum + 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have h1 := hb b (by simp)
    have := ih (fun x hx => hb x (by simp [hx]))
    simp [lqT, this]; omega
theorem swp (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (P R : List Bool) :
    run (swT bs) (hc (Rr ++ P) (rtt bs R)) = hc (Rr ++ Q bs P) R := by
  induction bs generalizing P with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := hb b (by simp); omega⟩
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    simp only [swT, rtt, Q, Nat.add_sub_cancel]
    rw [run_add, run_add]
    have e : [true, false] ++ pw Lu (b' + 1) ++ rtt bs R
        = [true, false] ++ false :: ([true, true, true] ++ pw Lu b' ++ rtt bs R) := by
      simp [Lu]
    rw [e, pass]
    have e2 : false :: ([true, true, true] ++ pw Lu b' ++ rtt bs R) = pw Lu (b' + 1) ++ rtt bs R := by
      simp [Lu]
    rw [e2, rsweep, pw_succ, List.append_assoc, ih']
    simp [List.append_assoc]
theorem lqp (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (P R : List Bool) :
    run (lqT bs) (dc (Q bs P) R) = dc P (E bs ++ R) := by
  induction bs generalizing P R with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := hb b (by simp); omega⟩
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    simp only [lqT, Q, E, Nat.add_sub_cancel]
    rw [run_add, run_add, ih', List.append_assoc, lsweep, lmark]
    simp [pw_succ, List.append_assoc]
theorem start (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (k m n : Nat) (hn : m + k = n + 1)
    (S R : List Bool) :
    run (18 * m + swT bs) (hc (pw Rr k ++ S) (pw Lu m ++ rtt bs R))
      = hc (Rr ++ Q bs (pw Rr n ++ S)) R := by
  rw [run_add, rsweep, <- List.append_assoc, <- pw_add, hn, pw_succ, List.append_assoc, swp bs hb]
theorem finish (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (ds : List Dg) (hok : lowOk ds = true)
    (k' m' : Nat) (Lt R : List Bool) :
    run (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k')
        (dc (Q bs (pw Rr (k' + 1 + m') ++ (Sr ds ++ Lt))) R)
      = hc (pw Rr k' ++ (Sr (inc ds) ++ Lt)) (pw Lu m' ++ (E bs ++ R)) := by
  rw [run_add _ (18 * k'), run_add _ 1, run_add _ (6 * tz ds + 5), run_add (lqT bs), lqp bs hb,
    lsweep, cnt ds hok]
  rw [show k' + 1 + m' = (k' + m') + 1 by omega, pw_succ, List.append_assoc, restart, pw_add,
    List.append_assoc, rsweep]
theorem incr (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (k m k' m' : Nat) (hkm : k + m = k' + m' + 2) (Lt X : List Bool) :
    run (22 * m + 22 * bs.sum + 38 * bs.length + 4 * k + 30 + 6 * tz ds + 18 * k')
        (hc (pw Rr k ++ Sr ds ++ Lt) (pw Lu m ++ rtt bs ([false, false] ++ X)))
      = hc (pw Rr k' ++ Sr (inc ds) ++ Lt)
          (pw Lu m' ++ E bs ++ pw Lu 2 ++ [true, false] ++ X) := by
  have e : 22 * m + 22 * bs.sum + 38 * bs.length + 4 * k + 30 + 6 * tz ds + 18 * k'
      = (18 * m + swT bs) + (24 + (4 + (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k'))) := by
    rw [swT_eq, lqT_eq bs hb]; omega
  rw [e, run_add, List.append_assoc, start bs hb k m (k' + 1 + m') (by omega), run_add, turn,
    run_add, lunit, finish bs hb ds hok k' m' Lt]
  simp [List.append_assoc, Lu]
theorem ovf (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (k m k' m' : Nat) (hkm : k + m = k' + m' + 2) (Lt X : List Bool) :
    run (22 * m + 22 * bs.sum + 38 * (bs.length + 1) + 4 * k + 30 + 6 * tz ds + 18 * k')
        (hc (pw Rr k ++ Sr ds ++ Lt) (pw Lu m ++ rtt bs ([true, false] ++ [false, false] ++ X)))
      = hc (pw Rr k' ++ Sr (inc ds) ++ Lt)
          (pw Lu m' ++ E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X) := by
  have e : 22 * m + 22 * bs.sum + 38 * (bs.length + 1) + 4 * k + 30 + 6 * tz ds + 18 * k'
      = (18 * m + swT bs) + (36 + (24 + (6 + (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k')))) := by
    rw [swT_eq, lqT_eq bs hb]; omega
  rw [e, run_add, List.append_assoc, start bs hb k m (k' + 1 + m') (by omega), run_add]
  rw [show [true, false] ++ [false, false] ++ X = [true, false] ++ false :: (false :: X) by rfl, pass,
    run_add, show false :: false :: X = [false, false] ++ X by rfl, turn, run_add, lmark,
    finish bs hb ds hok k' m' Lt]
  simp [List.append_assoc, Lu]
def zz : List Dg -> Nat
  | .z :: r => zz r + 1
  | _ => 0
def kc (ds : List Dg) : Nat := 3 - min (zz ds) 3
def ck (ds : List Dg) (B1 : Nat) (T : List Bool) : Cfg :=
  hc (pw Rr (kc ds) ++ Sr ds ++ []) (pw Lu (B1 - kc ds - 1) ++ T)
theorem kc_inc (ds : List Dg) (hok : lowOk ds = true) : kc (inc ds) = 3 - min (tz ds) 3 := by
  unfold kc; congr 2
  induction ds with
  | nil => simp [lowOk] at hok
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at hok; simp [inc, tz, zz, ih hok]
theorem incr_canon (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (B1 : Nat) (hB : 6 ≤ B1) (X : List Bool) :
    run (22 * (B1 + bs.sum) + 38 * bs.length + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds)
        (ck ds B1 (rtt bs ([false, false] ++ X)))
      = ck (inc ds) (if bs = [] then B1 else B1 - 2)
          (E bs ++ (if bs = [] then [] else pw Lu 2) ++ [true, false] ++ X) := by
  have hk := kc_inc ds hok
  have h1 : kc ds ≤ 3 := by unfold kc; omega
  have h2 : kc (inc ds) ≤ 3 := by rw [hk]; omega
  have h := incr ds hok bs hb (kc ds) (B1 - kc ds - 1) (kc (inc ds)) (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2)
    (by omega) [] X
  have et : 22 * (B1 + bs.sum) + 38 * bs.length + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds
      = 22 * (B1 - kc ds - 1) + 22 * bs.sum + 38 * bs.length + 4 * kc ds + 30 + 6 * tz ds + 18 * kc (inc ds) := by
    rw [hk]; unfold kc; omega
  unfold ck; rw [et, h]
  by_cases hbs : bs = []
  · subst hbs
    simp only [if_true, E, List.nil_append, List.append_nil]
    rw [show B1 - kc (inc ds) - 1 = (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2) + 2 by omega, pw_add]
    simp [List.append_assoc]
  · simp only [hbs, if_false, List.append_nil]
    rw [show B1 - 2 - kc (inc ds) - 1 = B1 - kc ds - 1 + kc ds - kc (inc ds) - 2 by omega]
    simp [List.append_assoc]
theorem ovf_canon (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (B1 : Nat) (hB : 6 ≤ B1) (X : List Bool) :
    run (22 * (B1 + bs.sum) + 38 * (bs.length + 1) + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds)
        (ck ds B1 (rtt bs ([true, false] ++ [false, false] ++ X)))
      = ck (inc ds) (B1 - 2) (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X) := by
  have hk := kc_inc ds hok
  have h1 : kc ds ≤ 3 := by unfold kc; omega
  have h2 : kc (inc ds) ≤ 3 := by rw [hk]; omega
  have h := ovf ds hok bs hb (kc ds) (B1 - kc ds - 1) (kc (inc ds)) (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2)
    (by omega) [] X
  have et : 22 * (B1 + bs.sum) + 38 * (bs.length + 1) + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds
      = 22 * (B1 - kc ds - 1) + 22 * bs.sum + 38 * (bs.length + 1) + 4 * kc ds + 30 + 6 * tz ds
        + 18 * kc (inc ds) := by
    rw [hk]; unfold kc; omega
  unfold ck; rw [et, h]
  rw [show B1 - 2 - kc (inc ds) - 1 = B1 - kc ds - 1 + kc ds - kc (inc ds) - 2 by omega]
  simp [List.append_assoc]
end M8
namespace M8
open List
theorem run_trans {a b : Nat} {c c' c'' : Cfg} (h1 : run a c = c') (h2 : run b c' = c'') :
    run (a + b) c = c'' := by rw [run_add, h1, h2]
theorem rep_add {α} (a : α) (m n : Nat) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a :=
  List.replicate_append_replicate.symm
def T3 : List Bool := [true, true, true]
def F3 : List Bool := [false, false, false]
theorem carry2 (n : Nat) (L R : List Bool) :
    run (3 * n) (dc (Sr (List.replicate n Dg.t) ++ L) R) = dc L (pw T3 n ++ R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_add, List.replicate_succ, Sr_cons,
      List.append_assoc, cdig2, ih, pw_succ', List.append_assoc]
    rfl
theorem zip1 (L R : List Bool) :
    run 3 ⟨.A, L, false, true :: R⟩ = ⟨.A, false :: L, false, R⟩ := rfl
theorem zip (n : Nat) (L R : List Bool) :
    run (3 * n) ⟨.A, L, false, List.replicate n true ++ R⟩
      = ⟨.A, List.replicate n false ++ L, false, R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_add, List.replicate_succ, List.cons_append, zip1, ih,
      List.replicate_succ', List.append_assoc]
    rfl
theorem pw_T3 (n : Nat) : pw T3 n = List.replicate (3 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pw_succ, ih, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; rfl
theorem Sr_zeros (n : Nat) : Sr (List.replicate n Dg.z) = List.replicate (3 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Sr_cons, ih, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; rfl
theorem realign_end (L R : List Bool) :
    run 10 ⟨.A, F3 ++ L, false, Lu ++ R⟩ = hc (Rr ++ L) R := by
  have h := frame (n := 10) (s := .A) (s' := .B) (L := [false, false, false]) (h := false)
    (R := [false, true, true, true]) (L' := [true, false, false, true, true]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, F3, Lu, Rr] using h
theorem realign (n : Nat) (hi : List Dg) (hok : lowOk hi = true) (L R : List Bool) :
    run (3 * (n + 1) + (1 + ((6 * tz hi + 5) + (3 * (3 * (n + 1)) + 10))))
        (dc (Sr (List.replicate (n + 1) Dg.t) ++ [true] ++ Sr hi ++ L) (Lu ++ R))
      = hc (Rr ++ Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) R := by
  have s0 := carry2 (n + 1) ([true] ++ Sr hi ++ L) (Lu ++ R)
  have s1 : run 1 (dc ([true] ++ Sr hi ++ L) (pw T3 (n + 1) ++ (Lu ++ R)))
      = dc (Sr hi ++ L) (false :: (pw T3 (n + 1) ++ (Lu ++ R))) := rfl
  have s2 := cnt hi hok L (false :: (pw T3 (n + 1) ++ (Lu ++ R)))
  have e2 : ac (Sr (inc hi) ++ L) (false :: (pw T3 (n + 1) ++ (Lu ++ R)))
      = ⟨.A, Sr (inc hi) ++ L, false, List.replicate (3 * (n + 1)) true ++ (Lu ++ R)⟩ := by
    simp only [ac, List.headD_cons, List.tail_cons, pw_T3]
  have s3 := zip (3 * (n + 1)) (Sr (inc hi) ++ L) (Lu ++ R)
  have e3 : List.replicate (3 * (n + 1)) false ++ (Sr (inc hi) ++ L)
      = F3 ++ (Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) := by
    rw [Sr_zeros, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; simp [F3]
  have s4 := realign_end (Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) R
  refine run_trans (by simpa [List.append_assoc] using s0) (run_trans s1 (run_trans s2 ?_))
  rw [e2]; refine run_trans s3 ?_
  rw [e3]; simpa [List.append_assoc] using s4
theorem realign0 (hi : List Dg) (hok : lowOk hi = true) (hok' : lowOk (inc hi) = true)
    (L R : List Bool) :
    run (1 + ((6 * tz hi + 5) + (3 + ((6 * tz (inc hi) + 5) + (1 + 1)))))
        (dc ([true] ++ Sr hi ++ L) (Lu ++ R))
      = hc ([false] ++ Sr (inc (inc hi)) ++ L) R := by
  have s1 : run 1 (dc ([true] ++ Sr hi ++ L) (Lu ++ R)) = dc (Sr hi ++ L) (false :: (Lu ++ R)) := rfl
  have s2 := cnt hi hok L (false :: (Lu ++ R))
  have s3 : run 3 (ac (Sr (inc hi) ++ L) (false :: (Lu ++ R)))
      = dc (Sr (inc hi) ++ L) ([true] ++ (Lu ++ R)) := rfl
  have s4 := cnt (inc hi) hok' L ([true] ++ (Lu ++ R))
  have s5 : run 1 (ac (Sr (inc (inc hi)) ++ L) ([true] ++ (Lu ++ R)))
      = ac ([false] ++ Sr (inc (inc hi)) ++ L) (Lu ++ R) := rfl
  have s6 := restart ([false] ++ Sr (inc (inc hi)) ++ L) R
  exact run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5 s6))))
theorem absHead (L X : List Bool) :
    run 3 (ac L ([false, false] ++ X)) = dc L ([true, false] ++ X) := rfl
theorem absTailZ (L R : List Bool) :
    run 11 ⟨.A, rdig .z ++ L, true, [false] ++ Lu ++ R⟩ = hc (Rr ++ [false] ++ L) R := by
  have h := frame (n := 11) (s := .A) (s' := .B) (L := [false, false, false]) (h := true)
    (R := [false, false, true, true, true]) (L' := [true, false, false, true, true, false]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, rdig, Lu, Rr] using h
theorem absTailT (L R : List Bool) :
    run 11 ⟨.A, rdig .t ++ L, true, [false] ++ Lu ++ R⟩ = hc (Rr ++ [true] ++ L) R := by
  have h := frame (n := 11) (s := .A) (s' := .B) (L := [false, false, true]) (h := true)
    (R := [false, false, true, true, true]) (L' := [true, false, false, true, true, true]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, rdig, Lu, Rr] using h
theorem absTailO1 (L R : List Bool) :
    run 8 ⟨.A, rdig .o ++ L, true, [false] ++ Lu ++ R⟩
      = dc L ([false, true, true, true, true] ++ Lu ++ R) := by
  have h := frame (n := 7) (s := .A) (s' := .D) (L := [false, true, true]) (h := true)
    (R := [false, false]) (L' := []) (h' := true)
    (R' := [true, true, true, true, false]) L ([true, true, true] ++ R) (by decide)
  rw [show 8 = 7 + 1 from rfl, run_add]
  simp only [rdig, Lu, List.cons_append, List.nil_append] at h ⊢
  rw [h, dstep]
theorem absTailO2 (L R : List Bool) :
    run 4 (ac L ([false, true, true, true, true] ++ R)) = hc ([false] ++ L) R := rfl
end M8
namespace M8
open List
def Reach1 (c c' : Cfg) : Prop := ∃ n, 0 < n /\ run n c = c'
theorem Reach1.trans {c c' c'' : Cfg} (h : Reach1 c c') (h' : Reach1 c' c'') : Reach1 c c'' := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a + b, by omega, by rw [run_add, e, e']⟩
theorem absFirst (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    ∃ n, 0 < n /\ run n (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      = ac (Sr (inc (inc ds)) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X) := by
  have s1 := start (b :: bs) hb 0 1 0 rfl (Sr ds ++ L) ([false, false] ++ X)
  have s2 := turn (Rr ++ Q (b :: bs) (pw Rr 0 ++ (Sr ds ++ L))) X
  have s3 := lunit (Q (b :: bs) (pw Rr 0 ++ (Sr ds ++ L))) (Lu ++ [true, false] ++ X)
  have s4 := lqp (b :: bs) hb (pw Rr 0 ++ (Sr ds ++ L)) (Lu ++ (Lu ++ [true, false] ++ X))
  have s5 := cnt ds h1 L (E (b :: bs) ++ (Lu ++ (Lu ++ [true, false] ++ X)))
  have s6 := absHead (Sr (inc ds) ++ L) (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X)))
  have s7 := cnt (inc ds) h2 L ([true, false] ++ (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X))))
  simp only [pw_zero, List.nil_append, pw_succ, List.append_nil] at s1 s2 s3 s4
  have e5 : E (b :: bs) ++ (Lu ++ (Lu ++ [true, false] ++ X))
      = [false, false] ++ (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X))) := by
    simp [E, List.append_assoc]
  rw [e5] at s5
  refine ⟨_, ?_, run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5
    (run_trans s6 (s7.trans (by simp [List.append_assoc, pw_succ])))))))⟩
  omega
theorem pw_pos (l : List Bool) (b : Nat) (hb : 1 ≤ b) (R : List Bool) :
    pw l b ++ R = l ++ (pw l (b - 1) ++ R) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp [List.append_assoc]
theorem absorbZ (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .z :: r)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc (Rr ++ [false] ++ Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t := absTailZ (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .z ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .z ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]
theorem absorbT (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .t :: r)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc (Rr ++ [true] ++ Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t := absTailT (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .t ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .t ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]
theorem absorbO (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .o :: r) (h3 : lowOk r = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc ([false] ++ Sr (inc r) ++ L) (pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t1 := absTailO1 (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  have t2 := cnt r h3 L ([false, true, true, true, true] ++ Lu ++
    (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X))
  have t3 := absTailO2 (Sr (inc r) ++ L) (Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X))
  refine ⟨n + (8 + ((6 * tz r + 5) + 4)), by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .o ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .o ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this]
  refine run_trans t1 (run_trans t2 ?_)
  rw [List.append_assoc _ Lu, t3]
  have := pw_pos Lu b hb1 (E bs ++ pw Lu 2 ++ [true, false] ++ X)
  simp only [List.append_assoc] at this ⊢
  rw [this]
end M8
namespace M8
open List
theorem absGenZ (r : List Dg) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run 11 (ac (Sr (.z :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc (Rr ++ [false] ++ Sr r ++ L) (pw Lu (b - 1) ++ Y) := by
  have t := absTailZ (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have : ac (Sr (.z :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .z ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]
theorem absGenT (r : List Dg) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run 11 (ac (Sr (.t :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc (Rr ++ [true] ++ Sr r ++ L) (pw Lu (b - 1) ++ Y) := by
  have t := absTailT (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have : ac (Sr (.t :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .t ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]
theorem absGenO (r : List Dg) (h3 : lowOk r = true) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run (8 + ((6 * tz r + 5) + 4)) (ac (Sr (.o :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc ([false] ++ Sr (inc r) ++ L) (pw Lu b ++ Y) := by
  have t1 := absTailO1 (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have t2 := cnt r h3 L ([false, true, true, true, true] ++ Lu ++ (pw Lu (b - 1) ++ Y))
  have t3 := absTailO2 (Sr (inc r) ++ L) (Lu ++ (pw Lu (b - 1) ++ Y))
  have : ac (Sr (.o :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .o ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this]
  refine run_trans t1 (run_trans t2 ?_)
  rw [List.append_assoc _ Lu, t3]
  have := pw_pos Lu b hb1 Y
  simp only [List.append_assoc] at this ⊢
  rw [this]
theorem absFirstOvf (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    ∃ n, 0 < n /\ run n (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      = ac (Sr (inc (inc ds)) ++ L)
          ([true, false] ++ pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)) := by
  have s1 := start (b :: bs) hb 0 1 0 rfl (Sr ds ++ L) ([true, false] ++ [false, false] ++ X)
  simp only [pw_zero, List.nil_append, pw_succ, List.append_nil] at s1
  have s2 := pass (Q (b :: bs) (Sr ds ++ L)) (false :: X)
  have s3 := turn (Mr ++ Q (b :: bs) (Sr ds ++ L)) X
  have s4 := lmark (Q (b :: bs) (Sr ds ++ L)) (Lu ++ [true, false] ++ X)
  have s3' : run 24 (hc (Mr ++ Q (b :: bs) (Sr ds ++ L)) (false :: false :: X))
      = dc (Mr ++ Q (b :: bs) (Sr ds ++ L)) (Lu ++ [true, false] ++ X) := s3
  have s5 := lqp (b :: bs) hb (Sr ds ++ L) ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X))
  have s6 := cnt ds h1 L (E (b :: bs) ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X)))
  have e6 : E (b :: bs) ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X))
      = [false, false] ++ (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)) := by
    simp [E, List.append_assoc, pw_succ]
  rw [e6] at s6 s5
  have s7 := absHead (Sr (inc ds) ++ L) (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))
  have s8 := cnt (inc ds) h2 L ([true, false] ++ (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)))
  have e1 : [true, false] ++ [false, false] ++ X = [true, false] ++ false :: (false :: X) := rfl
  rw [e1] at s1
  refine ⟨_, ?_, run_trans s1 (run_trans s2 (run_trans s3' (run_trans s4 (run_trans s5
    (run_trans s6 (run_trans s7 (s8.trans ?_)))))))⟩
  · omega
  · simp [List.append_assoc]
theorem absorbZo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .z :: r) (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc (Rr ++ [false] ++ Sr r ++ L)
        (pw Lu (b - 1) ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, absGenZ r b (hb b (by simp))]
theorem absorbTo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .t :: r) (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc (Rr ++ [true] ++ Sr r ++ L)
        (pw Lu (b - 1) ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, absGenT r b (hb b (by simp))]
theorem absorbOo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .o :: r) (h3 : lowOk r = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc ([false] ++ Sr (inc r) ++ L)
        (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + (8 + ((6 * tz r + 5) + 4)), by omega, ?_⟩
  rw [run_add, e, hr, absGenO r h3 b (hb b (by simp))]
end M8
namespace M8.R3
open List
def dv : Dg -> Nat
  | .z => 0
  | .o => 1
  | .t => 2
def dg : Nat -> Dg
  | 0 => .z
  | 1 => .o
  | _ => .t
theorem val_cons (d : Dg) (r : List Dg) : val (d :: r) = dv d + 3 * val r := by
  cases d <;> rfl
def dig (n : Nat) : List Dg :=
  if h : n = 0 then [] else dg (n % 3) :: dig (n / 3)
decreasing_by omega
theorem dv_dg (n : Nat) (h : n < 3) : dv (dg n) = n := by
  match n, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl
theorem val_dig (n : Nat) : val (dig n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold dig
    split
    · subst_vars; rfl
    · rw [val_cons, ih (n / 3) (by omega), dv_dg _ (Nat.mod_lt _ (by omega))]; omega
theorem dig_zero : dig 0 = [] := by unfold dig; simp
theorem dig_pos (n : Nat) (h : n ≠ 0) : dig n = dg (n % 3) :: dig (n / 3) := by
  rw [dig]; simp [h]
theorem trim_Sr_dig (ds : List Dg) : trim (Sr ds) = trim (Sr (dig (val ds))) := by
  induction ds with
  | nil => show trim (Sr []) = trim (Sr (dig 0)); rw [dig_zero]
  | cons d r ih =>
    rw [val_cons]
    by_cases h0 : dv d + 3 * val r = 0
    · have hd : d = .z := by cases d <;> simp [dv] at h0 ⊢
      have hr : val r = 0 := by omega
      subst hd
      rw [h0, dig_zero, Sr_cons]
      rw [hr, dig_zero] at ih
      simp [rdig, ih, cons']
    · rw [dig_pos _ h0, Sr_cons, Sr_cons]
      have e1 : dg ((dv d + 3 * val r) % 3) = d := by
        cases d <;> simp [dv, dg] <;> omega
      have e2 : (dv d + 3 * val r) / 3 = val r := by cases d <;> simp [dv] <;> omega
      rw [e1, e2]
      exact trim_append_congr _ ih
theorem trim_Sr_val {ds ds' : List Dg} (h : val ds = val ds') : trim (Sr ds) = trim (Sr ds') := by
  rw [trim_Sr_dig ds, trim_Sr_dig ds', h]
theorem Sr_append (a b : List Dg) : Sr (a ++ b) = Sr a ++ Sr b := by
  simp [Sr]
theorem val_append (a b : List Dg) : val (a ++ b) = val a + 3 ^ a.length * val b := by
  induction a with
  | nil => simp [val]
  | cons d r ih =>
    rw [List.cons_append, val_cons, val_cons, ih, List.length_cons, Nat.pow_succ]
    have e : 3 * (3 ^ r.length * val b) = 3 ^ r.length * 3 * val b := by
      rw [Nat.mul_comm (3 ^ r.length) 3, Nat.mul_assoc]
    rw [Nat.mul_add, e, Nat.add_assoc]
inductive CF
  | cl (v : Nat)
  | lone (lo : List Dg) (hv : Nat)
def shl (n : Nat) : List Dg × Nat :=
  if h : n = 0 then ([], 0)
  else if n % 3 = 0 then (.z :: (shl (n / 3)).1, (shl (n / 3)).2)
  else if n % 3 = 1 then ([.t], n / 3) else ([.z], n / 3)
decreasing_by omega
def shv (n : Nat) : CF := if n = 0 then .cl 0 else .lone (shl n).1 (shl n).2
def ctape : CF -> List Bool
  | .cl v => Sr (dig v)
  | .lone lo hv => Sr lo ++ [true] ++ Sr (dig hv)
def lad : List (Bool × Nat) -> List Bool
  | [] => [true, false]
  | (s, b) :: r => (if s then [true, false] else [false, false]) ++ pw Lu b ++ lad r
def linc : Nat -> List (Bool × Nat) -> Nat × List (Bool × Nat)
  | B, [] => (B - 2, [(false, 2)])
  | B, (false, c) :: r => (B, (true, c) :: r)
  | B, (true, c) :: r => (B - 2, (false, (linc c r).1 + 2) :: (linc c r).2)
def cph : CF -> Nat × CF
  | .cl v => (0, .cl (v + 1))
  | .lone lo hv =>
    if lowOk lo then (0, .lone (inc lo) hv)
    else if lo = [] then (0, shv (hv + 2))
    else (1, .cl (3 ^ (lo.length - 1) * (hv + 1)))
structure AS where
  k : Nat
  C : CF
  m : Nat
  L : List (Bool × Nat)
def absStep : CF -> List (Bool × Nat) -> AS
  | .cl v, (_, b) :: rest =>
    if (v + 2) % 3 = 0 then ⟨1, shv ((v + 2) / 3), b - 1, rest⟩
    else if (v + 2) % 3 = 2 then ⟨1, .lone [] ((v + 2) / 3), b - 1, rest⟩
    else ⟨0, shv ((v + 2) / 3 + 1), b, rest⟩
  | C, L => ⟨0, C, 0, L⟩
def mstep (S : AS) : AS :=
  match linc (S.k + 1 + S.m) S.L with
  | (0, L') => absStep S.C L'
  | (p + 1, L') => ⟨(cph S.C).1, (cph S.C).2, p, L'⟩
def tape (S : AS) : Cfg := hc (pw Rr S.k ++ ctape S.C) (pw Lu S.m ++ lad S.L)
theorem shl_eq (n : Nat) (hn : n ≠ 0) :
    [false] ++ Sr (dig n) = Sr (shl n).1 ++ [true] ++ Sr (dig (shl n).2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [dig_pos n hn, shl]
    simp only [hn, dite_false]
    by_cases h0 : n % 3 = 0
    · simp only [h0, if_true]
      have hn3 : n / 3 ≠ 0 := by omega
      have := ih (n / 3) (by omega) hn3
      simp only [Sr_cons, dg, rdig] at this ⊢
      simp only [List.cons_append, List.nil_append] at this ⊢
      rw [<- this]
    · by_cases h1 : n % 3 = 1
      · simp [h0, h1, dg, rdig, Sr_cons]
      · have h2 : n % 3 = 2 := by omega
        simp [h0, h1, h2, dg, rdig, Sr_cons]
theorem sh_tape (n : Nat) : trim ([false] ++ Sr (dig n)) = trim (ctape (shv n)) := by
  by_cases hn : n = 0
  · subst hn; simp [shv, ctape, dig_zero, cons']
  · simp only [shv, hn, if_false, ctape]; rw [shl_eq n hn]
end M8.R3
namespace M8.R3
open List
def Adv (c d : Cfg) : Prop := ∃ n, 0 < n /\ PE (run n c) d
theorem Adv.trans {c d e : Cfg} (h1 : Adv c d) (h2 : Adv d e) : Adv c e := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, by omega, by rw [run_add]; exact (PE_run b e1).trans e2⟩
theorem Adv_run {n : Nat} {c d : Cfg} (h : run n c = d) (hn : 0 < n) : Adv c d :=
  ⟨n, hn, h ▸ PE.refl _⟩
theorem Adv.pe_left {c c' d : Cfg} (h : PE c c') (h2 : Adv c' d) : Adv c d := by
  obtain ⟨n, hn, e⟩ := h2
  exact ⟨n, hn, (PE_run n h).trans e⟩
theorem Adv.pe_right {c d d' : Cfg} (h2 : Adv c d) (h : PE d d') : Adv c d' := by
  obtain ⟨n, hn, e⟩ := h2
  exact ⟨n, hn, e.trans h⟩
theorem PE_dc {L L' : List Bool} (h : trim L = trim L') (R : List Bool) : PE (dc L R) (dc L' R) := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show L.headD false = L'.headD false
    rw [<- trim_headD, h, trim_headD]
  · show trim L.tail = trim L'.tail
    rw [trim_tail, h, trim_tail]
theorem PE_hc {P P' : List Bool} (h : trim P = trim P') (R : List Bool) : PE (hc P R) (hc P' R) := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  show trim (true :: P) = trim (true :: P')
  simp [h]
theorem PE_hcR (P : List Bool) {R R' : List Bool} (h : trim R = trim R') : PE (hc P R) (hc P R') := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show trim ([true, true] ++ R) = trim ([true, true] ++ R')
  exact trim_append_congr _ h
theorem PE_dc_R {S R R' : List Bool} (h : R = R') : PE (dc S R) (dc S R') := h ▸ PE.refl _
theorem trim_zpad (l : List Bool) (ds : List Dg) (n : Nat) :
    trim (l ++ Sr (ds ++ List.replicate n .z)) = trim (l ++ Sr ds) := by
  rw [Sr_append, <- List.append_assoc, trim_append_blank]
  intro x hx
  simp [Sr, rdig, List.mem_flatMap, List.mem_replicate] at hx
  exact hx.2
def tl (bs : List Nat) : List (Bool × Nat) := bs.map (fun b => (true, b))
theorem lad_tl (bs : List Nat) (M : List (Bool × Nat)) : lad (tl bs ++ M) = rtt bs (lad M) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [tl, lad, rtt] at ih ⊢; rw [ih]
theorem rtt_app (bs : List Nat) (R Y : List Bool) : rtt bs R ++ Y = rtt bs (R ++ Y) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [rtt, ih]
def lincT : List Nat -> List (Bool × Nat)
  | [] => []
  | [b] => [(false, b + 2)]
  | b :: b' :: bs => (false, b) :: lincT (b' :: bs)
theorem linc_split (bs : List Nat) (hb : ∀ b ∈ bs, 2 ≤ b) (c : Nat) (r : List (Bool × Nat)) (B : Nat) :
    linc B (tl bs ++ (false, c) :: r) = (if bs = [] then B else B - 2, lincT bs ++ (true, c) :: r) := by
  induction bs generalizing B with
  | nil => rfl
  | cons b bs ih =>
    have ih' := ih (fun x hx => hb x (by simp [hx])) b
    have hb0 := hb b (by simp)
    simp only [tl, List.map_cons, List.cons_append] at ih' ⊢
    rw [linc, ih']
    cases bs with
    | nil => simp [lincT]
    | cons b' bs => simp [lincT]; omega
theorem lad_lincT (bs : List Nat) (hbs : bs ≠ []) (M : List (Bool × Nat)) :
    lad (lincT bs ++ M) = E bs ++ pw Lu 2 ++ lad M := by
  induction bs with
  | nil => exact absurd rfl hbs
  | cons b bs ih =>
    cases bs with
    | nil =>
      simp only [lincT, List.cons_append, List.nil_append, lad, E, if_false]
      rw [pw_add]; simp [List.append_assoc]
    | cons b' bs =>
      have := ih (by simp)
      simp only [lincT, List.cons_append, lad, if_false] at this ⊢
      rw [this]; simp [E, List.append_assoc]
theorem linc_tl (bs : List Nat) (hb : ∀ b ∈ bs, 2 ≤ b) (B : Nat) :
    linc B (tl bs) = (B - 2, bs.map (fun b => (false, b)) ++ [(false, 2)]) := by
  induction bs generalizing B with
  | nil => rfl
  | cons b bs ih =>
    have ih' := ih (fun x hx => hb x (by simp [hx])) b
    have hb0 := hb b (by simp)
    simp only [tl, List.map_cons] at ih' ⊢
    rw [linc, ih']
    simp; omega
theorem lad_fl (bs : List Nat) (M : List (Bool × Nat)) :
    lad (bs.map (fun b => (false, b)) ++ M) = E bs ++ lad M := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [lad, E, ih, List.append_assoc]
theorem lad_decomp (L : List (Bool × Nat)) :
    (∃ bs c r, L = tl bs ++ (false, c) :: r) \/ ∃ bs, L = tl bs := by
  induction L with
  | nil => exact Or.inr ⟨[], rfl⟩
  | cons x r ih =>
    obtain ⟨s, b⟩ := x
    cases s with
    | false => exact Or.inl ⟨[], b, r, rfl⟩
    | true =>
      rcases ih with ⟨bs, c, r', rfl⟩ | ⟨bs, rfl⟩
      · exact Or.inl ⟨b :: bs, c, r', rfl⟩
      · exact Or.inr ⟨b :: bs, rfl⟩
theorem lphase (k m : Nat) (hkm : 1 ≤ k + m) (S : List Bool) (L : List (Bool × Nat))
    (hL : ∀ x ∈ L, 2 ≤ x.2) :
    Adv (hc (pw Rr k ++ S) (pw Lu m ++ lad L))
      (dc S (pw Lu (linc (k + 1 + m) L).1 ++ lad (linc (k + 1 + m) L).2)) := by
  obtain ⟨n, hn⟩ : ∃ n, m + k = n + 1 := ⟨k + m - 1, by omega⟩
  rcases lad_decomp L with ⟨bs, c, r, rfl⟩ | ⟨bs, rfl⟩
  · have hb2 : ∀ b ∈ bs, 2 ≤ b := fun b hb => hL (true, b) (by simp [tl, hb])
    have hb1 : ∀ b ∈ bs, 1 ≤ b := fun b hb => by have := hb2 b hb; omega
    have eL : lad (tl bs ++ (false, c) :: r) = rtt bs ([false, false] ++ (pw Lu c ++ lad r)) := by
      rw [lad_tl]; simp [lad]
    rw [eL, linc_split bs hb2]
    have s1 := start bs hb1 k m n hn S ([false, false] ++ (pw Lu c ++ lad r))
    have s2 := turn (Rr ++ Q bs (pw Rr n ++ S)) (pw Lu c ++ lad r)
    have s3 := lunit (Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ (pw Lu c ++ lad r))
    have s4 := lqp bs hb1 (pw Rr n ++ S) (Lu ++ (Lu ++ [true, false] ++ (pw Lu c ++ lad r)))
    have s5 := lsweep n S (E bs ++ (Lu ++ (Lu ++ [true, false] ++ (pw Lu c ++ lad r))))
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 s5)))) (by omega) |>.pe_right ?_
    refine PE_dc_R ?_
    by_cases hbs : bs = []
    · subst hbs
      simp only [if_true, E, List.nil_append, lincT]
      rw [show k + 1 + m = n + 2 by omega, pw_add]
      simp [lad, List.append_assoc]
    · simp only [hbs, if_false, lad_lincT bs hbs]
      rw [show k + 1 + m - 2 = n by omega]
      simp [lad, List.append_assoc]
  · have hb2 : ∀ b ∈ bs, 2 ≤ b := fun b hb => hL (true, b) (by simp [tl, hb])
    have hb1 : ∀ b ∈ bs, 1 ≤ b := fun b hb => by have := hb2 b hb; omega
    rw [linc_tl bs hb2, lad_fl]
    have ep : PE (hc (pw Rr k ++ S) (pw Lu m ++ lad (tl bs)))
        (hc (pw Rr k ++ S) (pw Lu m ++ rtt bs ([true, false] ++ false :: [false]))) := by
      apply PE_hcR
      rw [show lad (tl bs) = rtt bs [true, false] by simpa [lad] using lad_tl bs []]
      rw [show [true, false] ++ false :: [false] = [true, false] ++ [false, false] from rfl, <- rtt_app,
        <- List.append_assoc]
      exact (trim_append_blank _ [false, false] (by simp)).symm
    refine Adv.pe_left ep ?_
    have s1 := start bs hb1 k m n hn S ([true, false] ++ false :: [false])
    have s2 := pass (Q bs (pw Rr n ++ S)) [false]
    have s3 : run 24 (hc (Mr ++ Q bs (pw Rr n ++ S)) (false :: [false]))
        = dc (Mr ++ Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ []) := turn _ []
    have s4 := lmark (Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ [])
    have s5 := lqp bs hb1 (pw Rr n ++ S) ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ []))
    have s6 := lsweep n S (E bs ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ [])))
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5 s6)))))
      (by omega) |>.pe_right ?_
    rw [show k + 1 + m - 2 = n by omega]
    apply PE_dc_R
    simp [lad, pw_add, List.append_assoc]
theorem lowOk_app_z (l : List Dg) : lowOk (l ++ [.z]) = true := by
  induction l with
  | nil => rfl
  | cons d r ih => cases d <;> simp [lowOk, ih]
theorem inc_app (l X : List Dg) (h : lowOk l = true) : inc (l ++ X) = inc l ++ X := by
  induction l with
  | nil => simp [lowOk] at h
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at h; simp [inc, ih h]
theorem inc_ne_nil (l : List Dg) : inc l ≠ [] := by
  cases l with
  | nil => simp [inc]
  | cons d r => cases d <;> simp [inc]
theorem val_rep_z (n : Nat) : val (List.replicate n Dg.z) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, val_cons, ih]; rfl
theorem lowOk_false_rep (lo : List Dg) (h : lowOk lo = false) : lo = List.replicate lo.length .t := by
  induction lo with
  | nil => rfl
  | cons d r ih =>
    cases d with
    | z => simp [lowOk] at h
    | o => simp [lowOk] at h
    | t => simp only [lowOk] at h; simp [List.replicate_succ]; exact ih h
theorem val_inc2pad (v : Nat) :
    ∃ d0 r, inc (inc (dig v ++ [.z, .z, .z])) = d0 :: r /\ lowOk r = true /\ dv d0 + 3 * val r = v + 2 /\
      lowOk (dig v ++ [.z, .z, .z]) = true /\ lowOk (inc (dig v ++ [.z, .z, .z])) = true := by
  have e1 : inc (dig v ++ [.z, .z, .z]) = inc (dig v ++ [.z]) ++ [.z, .z] := by
    rw [show dig v ++ [.z, .z, .z] = (dig v ++ [.z]) ++ [.z, .z] by simp, inc_app _ _ (lowOk_app_z _)]
  have e2 : inc (inc (dig v ++ [.z]) ++ [.z, .z]) = inc (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] := by
    rw [show inc (dig v ++ [.z]) ++ [.z, .z] = (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] by simp,
      inc_app _ _ (lowOk_app_z _)]
  obtain ⟨d0, l2, hl2⟩ : ∃ d0 l2, inc (inc (dig v ++ [.z]) ++ [.z]) = d0 :: l2 := by
    cases h : inc (inc (dig v ++ [.z]) ++ [.z]) with
    | nil => exact absurd h (inc_ne_nil _)
    | cons d l => exact ⟨d, l, rfl⟩
  refine ⟨d0, l2 ++ [.z], ?_, lowOk_app_z _, ?_, ?_, ?_⟩
  · rw [e1, e2, hl2]; rfl
  · have hv : val (inc (inc (dig v ++ [.z, .z, .z]))) = v + 2 := by
      rw [val_inc, val_inc, val_append, val_dig]; simp [val]
    rw [e1, e2, hl2] at hv
    rw [<- val_cons]; simpa [val_append, val] using hv
  · rw [show dig v ++ [.z, .z, .z] = (dig v ++ [.z, .z]) ++ [.z] by simp]; exact lowOk_app_z _
  · rw [e1, show inc (dig v ++ [.z]) ++ [.z, .z] = (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] by simp]
    exact lowOk_app_z _
theorem cphase (C : CF) (p : Nat) (R : List Bool) :
    Adv (dc (ctape C) (pw Lu (p + 1) ++ R)) (hc (pw Rr (cph C).1 ++ ctape (cph C).2) (pw Lu p ++ R)) := by
  have eR : pw Lu (p + 1) ++ R = Lu ++ (pw Lu p ++ R) := by simp [List.append_assoc]
  rw [eR]
  cases C with
  | cl v =>
    have hok := lowOk_app_z (dig v)
    have e0 : PE (dc (Sr (dig v)) (Lu ++ (pw Lu p ++ R))) (dc (Sr (dig v ++ [.z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
      apply PE_dc; simpa using (trim_zpad [] (dig v) 1).symm
    refine Adv.pe_left e0 ?_
    have s1 := cnt _ hok [] (Lu ++ (pw Lu p ++ R))
    have s2 := restart (Sr (inc (dig v ++ [.z])) ++ []) (pw Lu p ++ R)
    refine Adv_run (run_trans s1 s2) (by omega) |>.pe_right ?_
    apply PE_hc
    simp only [cph, ctape, pw_zero, List.nil_append, List.append_nil]
    apply trim_Sr_val
    rw [val_inc, val_append, val_dig, val_dig]; simp [val]
  | lone lo hv =>
    by_cases hok : lowOk lo = true
    · have s1 := cnt lo hok ([true] ++ Sr (dig hv)) (Lu ++ (pw Lu p ++ R))
      have s2 := restart (Sr (inc lo) ++ ([true] ++ Sr (dig hv))) (pw Lu p ++ R)
      refine Adv_run ?_ (show 0 < (6 * tz lo + 5) + 1 by omega)
      simp only [cph, hok, if_true, ctape, pw_zero, List.nil_append, List.append_assoc]
      exact run_trans s1 s2
    · have hok' : lowOk lo = false := by simpa using hok
      by_cases hlo : lo = []
      · subst hlo
        have h1 : lowOk (dig hv ++ [.z, .z]) = true := by
          rw [show dig hv ++ [.z, .z] = (dig hv ++ [.z]) ++ [.z] by simp]; exact lowOk_app_z _
        have h2 : lowOk (inc (dig hv ++ [.z, .z])) = true := by
          rw [show dig hv ++ [.z, .z] = (dig hv ++ [.z]) ++ [.z] by simp, inc_app _ _ (lowOk_app_z _)]
          exact lowOk_app_z _
        have e0 : PE (dc (ctape (.lone [] hv)) (Lu ++ (pw Lu p ++ R)))
            (dc ([true] ++ Sr (dig hv ++ [.z, .z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
          apply PE_dc; simp only [ctape, Sr_nil, List.nil_append, List.append_nil]
          exact (trim_zpad [true] (dig hv) 2).symm
        refine Adv.pe_left e0 ?_
        have s := realign0 _ h1 h2 [] (pw Lu p ++ R)
        refine Adv_run s (by omega) |>.pe_right ?_
        apply PE_hc
        have hc : cph (.lone [] hv) = (0, shv (hv + 2)) := by simp [cph, lowOk]
        rw [hc]; simp only [pw_zero, List.nil_append, List.append_nil]
        rw [<- sh_tape]
        apply trim_append_congr
        apply trim_Sr_val
        rw [val_inc, val_inc, val_append, val_dig, val_dig]; simp [val]
      · obtain ⟨n, hn⟩ : ∃ n, lo.length = n + 1 := ⟨lo.length - 1, by
          cases lo with
          | nil => exact absurd rfl hlo
          | cons _ _ => simp⟩
        have hrep := lowOk_false_rep lo hok'
        rw [hn] at hrep
        have h1 := lowOk_app_z (dig hv)
        have e0 : PE (dc (ctape (.lone lo hv)) (Lu ++ (pw Lu p ++ R)))
            (dc (Sr (List.replicate (n + 1) Dg.t) ++ [true] ++ Sr (dig hv ++ [.z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
          apply PE_dc; simp only [ctape, List.append_nil]; rw [<- hrep]
          have := trim_zpad (Sr lo ++ [true]) (dig hv) 1
          simp only [List.replicate] at this; exact this.symm
        refine Adv.pe_left e0 ?_
        have s := realign n _ h1 [] (pw Lu p ++ R)
        refine Adv_run s (by omega) |>.pe_right ?_
        apply PE_hc
        have hc : cph (.lone lo hv) = (1, .cl (3 ^ n * (hv + 1))) := by simp [cph, hok', hlo, hn]
        rw [hc]; simp only [pw_succ, pw_zero, List.append_nil, ctape]
        rw [List.append_assoc]
        apply trim_append_congr
        rw [<- Sr_append]
        apply trim_Sr_val
        rw [val_append, val_rep_z, val_inc, val_append, val_dig, val_dig, List.length_replicate]
        simp [val]
theorem aphase (v b : Nat) (hb : 1 ≤ b) (rest : List (Bool × Nat)) :
    Adv (dc (ctape (.cl v)) (pw Lu 0 ++ lad ((false, b) :: rest)))
      (tape (absStep (.cl v) ((false, b) :: rest))) := by
  obtain ⟨d0, r, hr, hok, hval, h1, h2⟩ := val_inc2pad v
  have eY : pw Lu 0 ++ lad ((false, b) :: rest) = [false, false] ++ (pw Lu b ++ lad rest) := by
    simp [lad]
  rw [eY]
  have e0 : PE (dc (ctape (.cl v)) ([false, false] ++ (pw Lu b ++ lad rest)))
      (dc (Sr (dig v ++ [.z, .z, .z]) ++ []) ([false, false] ++ (pw Lu b ++ lad rest))) := by
    apply PE_dc; simpa [ctape] using (trim_zpad [] (dig v) 3).symm
  refine Adv.pe_left e0 ?_
  have s1 := cnt _ h1 [] ([false, false] ++ (pw Lu b ++ lad rest))
  have s2 := absHead (Sr (inc (dig v ++ [.z, .z, .z])) ++ []) (pw Lu b ++ lad rest)
  have s3 := cnt _ h2 [] ([true, false] ++ (pw Lu b ++ lad rest))
  rw [hr] at s3
  have hd : dv d0 ≤ 2 := by cases d0 <;> simp [dv]
  have hq : (v + 2) / 3 = val r := by omega
  cases d0 with
  | z =>
    have s4 := absGenZ r b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 0 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, if_true, tape, pw_succ, pw_zero, List.append_nil]
    apply PE_hc
    rw [hq, List.append_assoc]
    apply trim_append_congr
    rw [<- sh_tape]; exact trim_append_congr _ (trim_Sr_dig r)
  | t =>
    have s4 := absGenT r b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 2 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, show (2:Nat) ≠ 0 by omega, if_false, if_true, tape, pw_succ, pw_zero,
      List.append_nil, ctape]
    apply PE_hc
    rw [hq, List.append_assoc]
    apply trim_append_congr
    exact trim_append_congr _ (trim_Sr_dig r)
  | o =>
    have s4 := absGenO r hok b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 1 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, show (1:Nat) ≠ 0 by omega, show (1:Nat) ≠ 2 by omega, if_false, tape, pw_zero,
      List.nil_append, List.append_nil]
    apply PE_hc
    rw [hq, <- sh_tape]
    apply trim_append_congr
    apply trim_Sr_val
    rw [val_inc, val_dig]
def okS (S : AS) : Prop :=
  1 ≤ S.k + S.m /\ (∀ x ∈ S.L, 2 ≤ x.2) /\
  ((linc (S.k + 1 + S.m) S.L).1 = 0 -> (∃ v, S.C = .cl v) /\
    ∃ b rest, (linc (S.k + 1 + S.m) S.L).2 = (false, b) :: rest /\ 1 ≤ b)
theorem sim (S : AS) (h : okS S) : Adv (tape S) (tape (mstep S)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have a1 := lphase S.k S.m h1 (ctape S.C) S.L h2
  show Adv (hc (pw Rr S.k ++ ctape S.C) (pw Lu S.m ++ lad S.L)) _
  unfold mstep
  revert h3 a1
  generalize linc (S.k + 1 + S.m) S.L = q
  obtain ⟨p, L'⟩ := q
  intro h3 a1
  cases p with
  | zero =>
    obtain ⟨⟨v, hv⟩, b, rest, hL, hb⟩ := h3 rfl
    simp only at hL; subst hL
    rw [hv] at a1 ⊢
    exact a1.trans (aphase v b hb rest)
  | succ p =>
    exact a1.trans (cphase S.C p (lad L'))
end M8.R3
namespace M8.R3
open List
def Lam : Nat -> Nat -> List (Bool × Nat)
  | 0, N => [(decide (N % 2 = 1), 2)]
  | l + 1, N => (decide (N % 2 = 1), 2 ^ (l + 1) + 2 * ((N + 2) / 4)) :: Lam l (N / 2)
def Ol : Nat -> List (Bool × Nat)
  | 0 => []
  | l + 1 => (true, 2 ^ (l + 1)) :: Ol l
theorem two_le_pow (l : Nat) : 2 ≤ 2 ^ (l + 1) := by
  rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := l); omega
theorem linc_Lam (l N B : Nat) (hN : N + 1 < 2 ^ (l + 1)) (hB : 2 ≤ B) :
    linc B (Lam l N) = (if N % 2 = 1 then B - 2 else B, Lam l (N + 1)) := by
  induction l generalizing N B with
  | zero =>
    have : N = 0 := by simp at hN; omega
    subst this; rfl
  | succ l ih =>
    have hP := two_le_pow l
    have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
    by_cases hp : N % 2 = 1
    · have ih' := ih (N / 2) (2 ^ (l + 1) + 2 * ((N + 2) / 4)) (by omega) (by omega)
      simp only [Lam, hp, decide_true, linc, ih', if_true]
      have e1 : (N + 1) / 2 = N / 2 + 1 := by omega
      have e2 : decide ((N + 1) % 2 = 1) = false := by simp; omega
      rw [e1, e2]
      congr 3
      split <;> omega
    · simp only [Lam, hp, decide_false, linc, if_false]
      have e1 : (N + 1) / 2 = N / 2 := by omega
      have e2 : decide ((N + 1) % 2 = 1) = true := by simp; omega
      rw [e1, e2]
      congr 3
      omega
theorem linc_Ol (l B : Nat) (hB : 2 ≤ B) : linc B (Ol l) = (B - 2, Lam l 0) := by
  induction l generalizing B with
  | zero => rfl
  | succ l ih =>
    have hP := two_le_pow l
    simp only [Ol, linc, ih (2 ^ (l + 1)) hP, Lam]
    simp; omega
theorem Lam_top (l : Nat) : Lam l (2 ^ (l + 1) - 1) = Ol (l + 1) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have hP := two_le_pow l
    have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
    have e1 : (2 ^ (l + 1 + 1) - 1) / 2 = 2 ^ (l + 1) - 1 := by omega
    rw [Lam, e1, ih, Ol]
    have e2 : decide ((2 ^ (l + 1 + 1) - 1) % 2 = 1) = true := by simp only [decide_eq_true_eq]; omega
    rw [e2]
    congr 2
    omega
theorem Lam_even (l a : Nat) :
    Lam (l + 1) (2 * a) = (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a := by
  simp only [Lam]
  have e1 : 2 * a / 2 = a := by omega
  have e2 : (2 * a + 2) / 4 = (a + 1) / 2 := by omega
  rw [e1, e2]; simp
theorem Lam_blocks (l N : Nat) : ∀ x ∈ Lam l N, 2 ≤ x.2 := by
  induction l generalizing N with
  | zero => intro x hx; simp [Lam] at hx; subst hx; simp
  | succ l ih =>
    intro x hx
    simp only [Lam, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := two_le_pow l; simp; omega
    · exact ih _ x hx
theorem Ol_blocks (l : Nat) : ∀ x ∈ Ol l, 2 ≤ x.2 := by
  induction l with
  | zero => intro x hx; simp [Ol] at hx
  | succ l ih =>
    intro x hx
    simp only [Ol, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact two_le_pow l
    · exact ih x hx
def epL (l a i : Nat) : List (Bool × Nat) :=
  if a + i < 2 ^ (l + 1) then Lam l (a + i) else Lam (l + 1) (a + i - 2 ^ (l + 1))
theorem epL_blocks (l a i : Nat) : ∀ x ∈ epL l a i, 2 ≤ x.2 := by
  unfold epL; split
  · exact Lam_blocks _ _
  · exact Lam_blocks _ _
theorem linc_epL (l a i B : Nat) (ha : a < 2 ^ (l + 1)) (hi : i < 2 ^ (l + 1) + a + 1) (hB : 2 ≤ B) :
    linc B (epL l a i) = (if (a + i) % 2 = 1 then B - 2 else B, epL l a (i + 1)) := by
  have hP := two_le_pow l
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  unfold epL
  by_cases h1 : a + i + 1 < 2 ^ (l + 1)
  · have c1 : a + i < 2 ^ (l + 1) := by omega
    have c2 : a + (i + 1) < 2 ^ (l + 1) := by omega
    rw [if_pos c1, if_pos c2, linc_Lam l _ B h1 hB, Nat.add_assoc]
  · by_cases h2 : a + i < 2 ^ (l + 1)
    · have e : a + i = 2 ^ (l + 1) - 1 := by omega
      have c2 : ¬ a + (i + 1) < 2 ^ (l + 1) := by omega
      have c3 : (a + i) % 2 = 1 := by omega
      rw [if_pos h2, if_neg c2, e, Lam_top, linc_Ol _ B hB, <- e, if_pos c3]
      have e4 : a + (i + 1) - 2 ^ (l + 1) = 0 := by omega
      rw [e4]
    · have c2 : ¬ a + (i + 1) < 2 ^ (l + 1) := by omega
      have c3 : a + i - 2 ^ (l + 1) + 1 < 2 ^ (l + 1 + 1) := by omega
      rw [if_neg h2, if_neg c2, linc_Lam (l + 1) _ B c3 hB]
      have e : (a + i - 2 ^ (l + 1)) % 2 = (a + i) % 2 := by omega
      have e4 : a + (i + 1) - 2 ^ (l + 1) = a + i - 2 ^ (l + 1) + 1 := by omega
      rw [e, e4]
end M8.R3
namespace M8.R3
open List
theorem val_lt (ds : List Dg) : val ds < 3 ^ ds.length := by
  induction ds with
  | nil => simp [val]
  | cons d r ih =>
    rw [val_cons, List.length_cons, Nat.pow_succ]
    have : dv d ≤ 2 := by cases d <;> simp [dv]
    omega
theorem lowOk_iff (ds : List Dg) : lowOk ds = true <-> val ds + 1 < 3 ^ ds.length := by
  induction ds with
  | nil => simp [lowOk, val]
  | cons d r ih =>
    have hl := val_lt r
    rw [val_cons, List.length_cons, Nat.pow_succ]
    cases d with
    | z => simp [lowOk, dv]; omega
    | o => simp [lowOk, dv]; omega
    | t => simp only [lowOk, dv]; rw [ih]; omega
theorem length_inc (ds : List Dg) (h : lowOk ds = true) : (inc ds).length = ds.length := by
  induction ds with
  | nil => simp [lowOk] at h
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at h; simp [inc, ih h]
def Pend (C : CF) (j Vr : Nat) : Prop :=
  ∃ lo hv, C = .lone lo hv /\ lo ≠ [] /\ val lo + j = 3 ^ lo.length /\ Vr = 3 ^ (lo.length - 1) * (hv + 1)
def PendX (C : CF) (j Vr : Nat) : Prop :=
  Pend C j Vr \/ ∃ q j', C = .lone [] q /\ j = j' + 1 /\ Pend (shv (q + 2)) j' Vr
theorem Pend_pos {C : CF} {j Vr : Nat} (h : Pend C j Vr) : 1 ≤ j := by
  obtain ⟨lo, hv, _, _, h1, _⟩ := h
  have := val_lt lo; omega
theorem cph_pend2 {C : CF} {j Vr : Nat} (h : PendX C (j + 2) Vr) :
    ∃ C', cph C = (0, C') /\ Pend C' (j + 1) Vr := by
  rcases h with ⟨lo, hv, rfl, hne, h1, h2⟩ | ⟨q, j', rfl, hj, hp⟩
  · have hok : lowOk lo = true := by rw [lowOk_iff]; omega
    refine ⟨.lone (inc lo) hv, by simp [cph, hok], inc lo, hv, rfl, inc_ne_nil lo, ?_, ?_⟩
    · rw [val_inc, length_inc lo hok]; omega
    · rw [length_inc lo hok]; exact h2
  · have hj' : j' = j + 1 := by omega
    subst hj'
    exact ⟨shv (q + 2), by simp [cph, lowOk], hp⟩
theorem cph_pend1 {C : CF} {Vr : Nat} (h : PendX C 1 Vr) : cph C = (1, .cl Vr) := by
  rcases h with ⟨lo, hv, rfl, hne, h1, h2⟩ | ⟨q, j', rfl, hj, hp⟩
  · have hok : lowOk lo = false := by
      cases h : lowOk lo with
      | false => rfl
      | true => rw [lowOk_iff] at h; omega
    simp [cph, hok, hne, h2]
  · have : j' = 0 := by omega
    subst this
    have := Pend_pos hp; omega
theorem cph_k (C : CF) : (cph C).1 ≤ 1 := by
  cases C with
  | cl v => simp [cph]
  | lone lo hv =>
    simp only [cph]
    by_cases h1 : lowOk lo = true
    · simp [h1]
    · by_cases h2 : lo = []
      · subst h2; simp [lowOk]
      · simp [h1, h2]
theorem shv_ne (n : Nat) (hn : n ≠ 0) : shv n = .lone (shl n).1 (shl n).2 := by simp [shv, hn]
theorem shl_pos (n : Nat) (hn : n ≠ 0) :
    shl n = if n % 3 = 0 then (.z :: (shl (n / 3)).1, (shl (n / 3)).2)
      else if n % 3 = 1 then ([.t], n / 3) else ([.z], n / 3) := by
  rw [shl]; simp [hn]
theorem shv_pend (n : Nat) (hn : 1 ≤ n) :
    ∃ j Vr, Pend (shv n) j Vr /\ 2 * j ≤ 3 * n /\ 3 * Vr ≤ 3 * j + n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [shv_ne n (by omega), shl_pos n (by omega)]
    by_cases h0 : n % 3 = 0
    · rw [if_pos h0]
      obtain ⟨j', Vr', ⟨lo', hv', hc, hne, h1, h2⟩, b1, b2⟩ := ih (n / 3) (by omega) (by omega)
      rw [shv_ne _ (by omega)] at hc
      injection hc with e1 e2
      rw [e1, e2]
      obtain ⟨t, ht⟩ : ∃ t, lo'.length = t + 1 := ⟨lo'.length - 1, by
        cases lo' with
        | nil => exact absurd rfl hne
        | cons _ _ => simp⟩
      refine ⟨3 * j', 3 * Vr', ⟨.z :: lo', hv', rfl, by simp, ?_, ?_⟩, by omega, by omega⟩
      · rw [val_cons, List.length_cons, Nat.pow_succ]; simp [dv]; omega
      · rw [h2, List.length_cons, ht, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ,
          Nat.mul_comm (3 ^ t) 3, Nat.mul_assoc]
    · rw [if_neg h0]
      by_cases h1 : n % 3 = 1
      · rw [if_pos h1]
        refine ⟨1, n / 3 + 1, ⟨[.t], n / 3, rfl, by simp, by simp [val], by simp⟩, by omega, by omega⟩
      · rw [if_neg h1]
        refine ⟨3, n / 3 + 1, ⟨[.z], n / 3, rfl, by simp, by simp [val], by simp⟩, by omega, by omega⟩
def preL (l a : Nat) : List (Bool × Nat) := if a = 0 then Ol (l + 1) else Lam (l + 1) (2 * a - 1)
def EE (l a : Nat) : Nat := 2 ^ (l + 1) + a + 1
def PreInv (S : AS) : Prop :=
  ∃ l a v, a < 2 ^ (l + 1) /\ S.C = .cl v /\ S.k + S.m = 1 /\ S.k ≤ 1 /\ S.L = preL l a /\
    1 ≤ v /\ 5 * v ≤ 6 * EE l a /\ 15 ≤ EE l a
def EpInv (l a R Vr i : Nat) (S : AS) : Prop :=
  S.L = epL l a i /\ S.k ≤ 1 /\
  ((i < R /\ S.k + 1 + S.m = EE l a - i + (a + i) % 2 /\ PendX S.C (R - i) Vr) \/
   (R ≤ i /\ S.k + 1 + S.m = EE l a - i + 1 + (a + i) % 2 /\ S.C = .cl (Vr + i - R)))
theorem epoch_step (l a R Vr i : Nat) (S : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (hi : i < EE l a) (h : EpInv l a R Vr i S) :
    okS S /\ EpInv l a R Vr (i + 1) (mstep S) := by
  obtain ⟨hL, hk, hc⟩ := h
  have hP := two_le_pow l
  unfold EE at hR hi
  have hB : 2 ≤ S.k + 1 + S.m := by rcases hc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> unfold EE at h2 <;> omega
  have hlinc := linc_epL l a i (S.k + 1 + S.m) ha (by omega) hB
  rw [<- hL] at hlinc
  have hp : 1 ≤ (if (a + i) % 2 = 1 then S.k + 1 + S.m - 2 else S.k + 1 + S.m) := by
    rcases hc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> unfold EE at h2 <;> split <;> omega
  refine ⟨⟨by omega, hL ▸ epL_blocks l a i, fun h0 => by rw [hlinc] at h0; simp only at h0; omega⟩, ?_⟩
  obtain ⟨p, hpe⟩ : ∃ p, (if (a + i) % 2 = 1 then S.k + 1 + S.m - 2 else S.k + 1 + S.m) = p + 1 :=
    ⟨_, (Nat.sub_add_cancel hp).symm⟩
  have hms : mstep S = ⟨(cph S.C).1, (cph S.C).2, p, epL l a (i + 1)⟩ := by
    unfold mstep; rw [hlinc, hpe]
  rw [hms]
  refine ⟨rfl, cph_k _, ?_⟩
  simp only
  have hpar : (a + (i + 1)) % 2 = 1 - (a + i) % 2 := by omega
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · by_cases hlast : i + 1 < R
    · obtain ⟨C', e, hC'⟩ := cph_pend2 (j := R - i - 2) (by rw [show R - i - 2 + 2 = R - i by omega]; exact h3)
      rw [e]
      refine Or.inl ⟨hlast, ?_, Or.inl (by rw [show R - (i + 1) = R - i - 2 + 1 by omega]; exact hC')⟩
      simp only; unfold EE at h2 ⊢; split at hpe <;> omega
    · have hR1 : R - i = 1 := by omega
      rw [hR1] at h3
      rw [cph_pend1 h3]
      refine Or.inr ⟨by omega, ?_, by simp only; congr 1; omega⟩
      simp only; unfold EE at h2 ⊢; split at hpe <;> omega
  · rw [h3]
    refine Or.inr ⟨by omega, ?_, by simp only [cph]; congr 1; omega⟩
    simp only [cph]; unfold EE at h2 ⊢; split at hpe <;> omega
end M8.R3
namespace M8.R3
open List
theorem epL_zero (l a : Nat) (ha : a < 2 ^ (l + 1)) : epL l a 0 = Lam l a := by
  unfold epL; rw [if_pos (by omega), Nat.add_zero]
theorem preL_blocks (l a : Nat) : ∀ x ∈ preL l a, 2 ≤ x.2 := by
  unfold preL; split
  · exact Ol_blocks _
  · exact Lam_blocks _ _
theorem linc_preL (l a : Nat) (ha : a < 2 ^ (l + 1)) :
    linc 2 (preL l a) = (0, (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  rw [<- Lam_even]
  unfold preL
  split
  · subst_vars; rw [linc_Ol _ 2 (by omega)]
  · rw [linc_Lam (l + 1) (2 * a - 1) 2 (by omega) (by omega), if_pos (by omega)]
    congr 2; omega
theorem epoch_start (S : AS) (h : PreInv S) :
    ∃ l a R Vr, a < 2 ^ (l + 1) /\ okS S /\ EpInv l a R Vr 0 (mstep S) /\ R + 1 ≤ EE l a /\
      5 * (Vr + EE l a - R) ≤ 6 * (EE l a + 1) /\ 15 ≤ EE l a := by
  obtain ⟨l, a, v, ha, hC, hkm, hk, hL, hv1, hv2, hE⟩ := h
  have hP := two_le_pow l
  have hB : S.k + 1 + S.m = 2 := by omega
  have hl : linc (S.k + 1 + S.m) S.L = (0, (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
    rw [hB, hL]; exact linc_preL l a ha
  have hok : okS S := ⟨by omega, hL ▸ preL_blocks l a, fun _ => ⟨⟨v, hC⟩, _, _, by rw [hl], by omega⟩⟩
  have hms : mstep S = absStep (.cl v) ((false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
    unfold mstep; rw [hl, hC]
  rw [hms]
  unfold EE at hv2 hE ⊢
  have hb : 2 ^ (l + 1) + 2 * ((a + 1) / 2) + 1 = 2 ^ (l + 1) + a + 1 + a % 2 := by omega
  by_cases h0 : (v + 2) % 3 = 0
  · obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3) (by omega)
    refine ⟨l, a, j, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨Pend_pos hp, ?_, Or.inl ?_⟩⟩, ?_, ?_, hE⟩
    · simp only [absStep, h0, if_true]; exact (epL_zero l a ha).symm
    · simp only [absStep, h0, if_true]; omega
    · simp only [absStep, h0, if_true]; (try unfold EE); omega
    · simp only [absStep, h0, if_true, Nat.sub_zero]; exact hp
    · (try unfold EE); omega
    · (try unfold EE); omega
  · by_cases h2 : (v + 2) % 3 = 2
    · obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3 + 2) (by omega)
      have hne : (v + 2) % 3 ≠ 0 := h0
      have h20 : ¬ ((2 : Nat) = 0) := by decide
      refine ⟨l, a, j + 1, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨by omega, ?_, Or.inr ?_⟩⟩, ?_, ?_, hE⟩
      · simp only [absStep, hne, h2, h20, if_false, if_true]; exact (epL_zero l a ha).symm
      · simp only [absStep, hne, h2, h20, if_false, if_true]; omega
      · simp only [absStep, hne, h2, h20, if_false, if_true]; (try unfold EE); omega
      · simp only [absStep, hne, h2, h20, if_false, if_true, Nat.sub_zero]
        exact ⟨_, j, rfl, rfl, hp⟩
      · (try unfold EE); omega
      · (try unfold EE); omega
    · have h1 : (v + 2) % 3 = 1 := by omega
      obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3 + 1) (by omega)
      have hne : (v + 2) % 3 ≠ 0 := h0
      refine ⟨l, a, j, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨Pend_pos hp, ?_, Or.inl ?_⟩⟩, ?_, ?_, hE⟩
      · simp only [absStep, hne, h2, if_false]; exact (epL_zero l a ha).symm
      · simp only [absStep, hne, h2, if_false]; omega
      · simp only [absStep, hne, h2, if_false]; (try unfold EE); omega
      · simp only [absStep, hne, h2, if_false, Nat.sub_zero]; exact hp
      · (try unfold EE); omega
      · (try unfold EE); omega
def itr : Nat -> AS -> AS
  | 0, S => S
  | n + 1, S => mstep (itr n S)
theorem epoch_iter (l a R Vr : Nat) (S0 : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (h0 : EpInv l a R Vr 0 S0) :
    ∀ i, i ≤ EE l a -> EpInv l a R Vr i (itr i S0) /\
      (i = 0 \/ Adv (tape S0) (tape (itr i S0))) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨h0, Or.inl rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨hok, h3⟩ := epoch_step l a R Vr i _ ha hR (by omega) h1
    show EpInv l a R Vr (i + 1) (mstep (itr i S0)) /\ (i + 1 = 0 \/ Adv (tape S0) (tape (mstep (itr i S0))))
    refine ⟨h3, Or.inr ?_⟩
    rcases h2 with h2 | h2
    · subst h2; exact sim _ hok
    · exact h2.trans (sim _ hok)
theorem epoch_end (l a R Vr : Nat) (S : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (hV : 5 * (Vr + EE l a - R) ≤ 6 * (EE l a + 1)) (hE : 15 ≤ EE l a)
    (h : EpInv l a R Vr (EE l a) S) : PreInv S := by
  obtain ⟨hL, hk, hc⟩ := h
  have hP := two_le_pow l
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  rcases hc with ⟨h1, _, _⟩ | ⟨h1, h2, h3⟩
  · omega
  unfold EE at *
  have hL' : S.L = Lam (l + 1) (2 * a + 1) := by
    rw [hL]; unfold epL; rw [if_neg (by omega)]; congr 1; omega
  by_cases hlast : a + 1 < 2 ^ (l + 1)
  · refine ⟨l, a + 1, Vr + (2 ^ (l + 1) + a + 1) - R, hlast, h3, by omega, hk, ?_, by omega, ?_, ?_⟩
    · rw [hL']; unfold preL; rw [if_neg (by omega)]; congr 1
    · (try unfold EE); omega
    · (try unfold EE); omega
  · refine ⟨l + 1, 0, Vr + (2 ^ (l + 1) + a + 1) - R, by omega, h3, by omega, hk, ?_, by omega, ?_, ?_⟩
    · rw [hL']; unfold preL; rw [if_pos rfl, <- Lam_top]; congr 1; omega
    · (try unfold EE); omega
    · (try unfold EE); omega
theorem epoch (S : AS) (h : PreInv S) : ∃ S', PreInv S' /\ Adv (tape S) (tape S') := by
  obtain ⟨l, a, R, Vr, ha, hok, h0, hR, hV, hE⟩ := epoch_start S h
  obtain ⟨hEnd, hAdv⟩ := epoch_iter l a R Vr _ ha hR h0 (EE l a) (Nat.le_refl _)
  refine ⟨_, epoch_end l a R Vr _ ha hR hV hE hEnd, ?_⟩
  have a0 := sim S hok
  rcases hAdv with h1 | h1
  · unfold EE at h1; omega
  · exact a0.trans h1
theorem tape_st (S : AS) : (tape S).st = .B := rfl
theorem nonhalt_from (c : Cfg) (S : AS) (hS : PreInv S) (hc : PE c (tape S)) :
    ∀ n, ¬ halted (run n c) := by
  have key : ∀ t, ∃ n, t ≤ n /\ ∃ S, PreInv S /\ PE (run n c) (tape S) := by
    intro t
    induction t with
    | zero => exact ⟨0, (Nat.le_refl _), S, hS, hc⟩
    | succ t ih =>
      obtain ⟨n, hn, S1, h1, h2⟩ := ih
      obtain ⟨S2, h3, d, hd, h4⟩ := epoch S1 h1
      refine ⟨n + d, by omega, S2, h3, ?_⟩
      rw [run_add]
      exact (PE_run d h2).trans h4
  intro n hn
  obtain ⟨N, hN, S1, _, h2⟩ := key n
  have e : run N c = run n c := by
    rw [show N = n + (N - n) by omega, run_add]
    exact run_H _ _ hn
  have := h2.1
  rw [e, hn] at this
  exact absurd this (by rw [tape_st]; decide)
end M8.R3
namespace M8.R3
set_option maxRecDepth 1000000
def c0 : Cfg := ⟨.B, [true, false, false, true, false, false, true, false, true, true], true, [true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
theorem run_zero (c : Cfg) : run 0 c = c := rfl
def ck_0 : Cfg := init
def ck_1 : Cfg := ⟨.D, [false, false, false, false, false, false, true, true], false, [true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_2 : Cfg := ⟨.A, [false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, false, true, true], true, [false, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_3 : Cfg := ⟨.A, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false, true, true], true, [false, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_4 : Cfg := ⟨.D, [false, false, false, false, true, true, false, false, false, false, false, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_5 : Cfg := ⟨.E, [true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, true], false, [true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_6 : Cfg := ⟨.A, [false, false, false, false, true, true, false, false, true, true, false, false, false, false, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_7 : Cfg := ⟨.D, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, false, false, true], false, [false, true, true, true, true, false, true, true, true, false, true, true, true, true, false]⟩
def ck_8 : Cfg := ⟨.B, [true, false, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, true, true], true, [true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_9 : Cfg := ⟨.F, [true], true, [true, true, true, true, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_10 : Cfg := ⟨.A, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, true, false, true, true], false, [false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_11 : Cfg := ⟨.D, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true], true, [false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_12 : Cfg := ⟨.C, [false, false, true, true, false, true, true], false, [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_13 : Cfg := ⟨.A, [true, true, false, false, true, false, true, true], true, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_14 : Cfg := ⟨.A, [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, false, false, false, true, true], true, [true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_15 : Cfg := ⟨.E, [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true, false, true, true, false, true, true], false, [true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_16 : Cfg := ⟨.A, [false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], false, [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_17 : Cfg := ⟨.B, [true, false, false, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, false, true], false, [true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_18 : Cfg := ⟨.E, [true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false, false, false, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_19 : Cfg := ⟨.D, [false, true, true, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, false, false, false, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_20 : Cfg := ⟨.A, [false, false, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_21 : Cfg := ⟨.C, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, true, true], false, [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_22 : Cfg := ⟨.D, [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, true, true, false, false, true], true, [true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_23 : Cfg := ⟨.E, [true, true, false, false, true, false, false, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_24 : Cfg := ⟨.D, [false, false, false, false, false, false, false, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_25 : Cfg := ⟨.A, [false, false, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, false, false, false, true, true], true, [false, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_26 : Cfg := ⟨.B, [true, false, false, false, false, false, false, false, false, true, false, true, true], false, [true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_27 : Cfg := ⟨.A, [false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true], true, [false, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_28 : Cfg := ⟨.D, [false, false, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, false, true, true], false, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_29 : Cfg := ⟨.A, [true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, false, false, false, false, false, true, true], true, [true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_30 : Cfg := ⟨.A, [false, false, false, false, true, true, false, false, true, true, false, false, true, true, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, false, true, true, false, true, true, false, true, true, false, true, true], true, [false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
def ck_31 : Cfg := ⟨.B, [true, false, false, true, false, false, true, false, true, true], true, [true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩
theorem run_ck_0 : run 1500 ck_0 = ck_1 := by decide +kernel
theorem run_ck_1 : run 1500 ck_1 = ck_2 := by decide +kernel
theorem run_ck_2 : run 1500 ck_2 = ck_3 := by decide +kernel
theorem run_ck_3 : run 1500 ck_3 = ck_4 := by decide +kernel
theorem run_ck_4 : run 1500 ck_4 = ck_5 := by decide +kernel
theorem run_ck_5 : run 1500 ck_5 = ck_6 := by decide +kernel
theorem run_ck_6 : run 1500 ck_6 = ck_7 := by decide +kernel
theorem run_ck_7 : run 1500 ck_7 = ck_8 := by decide +kernel
theorem run_ck_8 : run 1500 ck_8 = ck_9 := by decide +kernel
theorem run_ck_9 : run 1500 ck_9 = ck_10 := by decide +kernel
theorem run_ck_10 : run 1500 ck_10 = ck_11 := by decide +kernel
theorem run_ck_11 : run 1500 ck_11 = ck_12 := by decide +kernel
theorem run_ck_12 : run 1500 ck_12 = ck_13 := by decide +kernel
theorem run_ck_13 : run 1500 ck_13 = ck_14 := by decide +kernel
theorem run_ck_14 : run 1500 ck_14 = ck_15 := by decide +kernel
theorem run_ck_15 : run 1500 ck_15 = ck_16 := by decide +kernel
theorem run_ck_16 : run 1500 ck_16 = ck_17 := by decide +kernel
theorem run_ck_17 : run 1500 ck_17 = ck_18 := by decide +kernel
theorem run_ck_18 : run 1500 ck_18 = ck_19 := by decide +kernel
theorem run_ck_19 : run 1500 ck_19 = ck_20 := by decide +kernel
theorem run_ck_20 : run 1500 ck_20 = ck_21 := by decide +kernel
theorem run_ck_21 : run 1500 ck_21 = ck_22 := by decide +kernel
theorem run_ck_22 : run 1500 ck_22 = ck_23 := by decide +kernel
theorem run_ck_23 : run 1500 ck_23 = ck_24 := by decide +kernel
theorem run_ck_24 : run 1500 ck_24 = ck_25 := by decide +kernel
theorem run_ck_25 : run 1500 ck_25 = ck_26 := by decide +kernel
theorem run_ck_26 : run 1500 ck_26 = ck_27 := by decide +kernel
theorem run_ck_27 : run 1500 ck_27 = ck_28 := by decide +kernel
theorem run_ck_28 : run 1500 ck_28 = ck_29 := by decide +kernel
theorem run_ck_29 : run 1500 ck_29 = ck_30 := by decide +kernel
theorem run_ck_30 : run 1083 ck_30 = ck_31 := by decide +kernel
theorem base_run : run 46083 init = c0 := by
  change run 46083 ck_0 = ck_31
  rw [show 46083 = 1500 + 44583 from rfl, run_add, run_ck_0]
  rw [show 44583 = 1500 + 43083 from rfl, run_add, run_ck_1]
  rw [show 43083 = 1500 + 41583 from rfl, run_add, run_ck_2]
  rw [show 41583 = 1500 + 40083 from rfl, run_add, run_ck_3]
  rw [show 40083 = 1500 + 38583 from rfl, run_add, run_ck_4]
  rw [show 38583 = 1500 + 37083 from rfl, run_add, run_ck_5]
  rw [show 37083 = 1500 + 35583 from rfl, run_add, run_ck_6]
  rw [show 35583 = 1500 + 34083 from rfl, run_add, run_ck_7]
  rw [show 34083 = 1500 + 32583 from rfl, run_add, run_ck_8]
  rw [show 32583 = 1500 + 31083 from rfl, run_add, run_ck_9]
  rw [show 31083 = 1500 + 29583 from rfl, run_add, run_ck_10]
  rw [show 29583 = 1500 + 28083 from rfl, run_add, run_ck_11]
  rw [show 28083 = 1500 + 26583 from rfl, run_add, run_ck_12]
  rw [show 26583 = 1500 + 25083 from rfl, run_add, run_ck_13]
  rw [show 25083 = 1500 + 23583 from rfl, run_add, run_ck_14]
  rw [show 23583 = 1500 + 22083 from rfl, run_add, run_ck_15]
  rw [show 22083 = 1500 + 20583 from rfl, run_add, run_ck_16]
  rw [show 20583 = 1500 + 19083 from rfl, run_add, run_ck_17]
  rw [show 19083 = 1500 + 17583 from rfl, run_add, run_ck_18]
  rw [show 17583 = 1500 + 16083 from rfl, run_add, run_ck_19]
  rw [show 16083 = 1500 + 14583 from rfl, run_add, run_ck_20]
  rw [show 14583 = 1500 + 13083 from rfl, run_add, run_ck_21]
  rw [show 13083 = 1500 + 11583 from rfl, run_add, run_ck_22]
  rw [show 11583 = 1500 + 10083 from rfl, run_add, run_ck_23]
  rw [show 10083 = 1500 + 8583 from rfl, run_add, run_ck_24]
  rw [show 8583 = 1500 + 7083 from rfl, run_add, run_ck_25]
  rw [show 7083 = 1500 + 5583 from rfl, run_add, run_ck_26]
  rw [show 5583 = 1500 + 4083 from rfl, run_add, run_ck_27]
  rw [show 4083 = 1500 + 2583 from rfl, run_add, run_ck_28]
  rw [show 2583 = 1500 + 1083 from rfl, run_add, run_ck_29]
  exact run_ck_30
def S0 : AS := ⟨0, .cl 17, 1, Ol 4⟩
theorem dig17 : dig 17 = [.t, .t, .o] := by
  rw [dig_pos 17 (by decide)]
  rw [show 17 / 3 = 5 from rfl, dig_pos 5 (by decide), show 5 / 3 = 1 from rfl, dig_pos 1 (by decide),
    show 1 / 3 = 0 from rfl, dig_zero]
  rfl
theorem base_pe : PE c0 (tape S0) := by
  unfold tape S0 ctape
  simp only [dig17]
  unfold PE
  decide +kernel
theorem base_inv : PreInv S0 :=
  ⟨3, 0, 17, by decide, rfl, rfl, by decide, rfl, by decide, by decide, by decide⟩
theorem nonhalt : ∀ n, ¬ halted (run n init) := by
  intro n
  have h := nonhalt_from (run 46083 init) S0 base_inv (base_run ▸ base_pe)
  by_cases hn : 46083 ≤ n
  · rw [show n = 46083 + (n - 46083) by omega, run_add]; exact h _
  · intro hh
    have e : run 46083 init = run n init := by
      rw [show 46083 = n + (46083 - n) by omega, run_add]; exact run_H _ _ hh
    have h0 := h 0
    rw [run_zero, e] at h0
    exact h0 hh
end M8.R3
variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
def b2fin (b : Bool) : Fin 2 := if b then 1 else 0
def toSt : M8.St -> Option (Fin 6)
  | .A => some 0 | .B => some 1 | .C => some 2
  | .D => some 3 | .E => some 4 | .F => some 5
  | .H => none
def toCfg (c : M8.Cfg) : Cfg (Fin 2) (Fin 6) :=
  ⟨toSt c.st, ⟨b2fin c.h, ListBlank.mk (c.L.map b2fin), ListBlank.mk (c.R.map b2fin)⟩⟩
lemma step_toCfg (c : M8.Cfg) (hne : (M8.step c).st ≠ .H) :
    step target_tm (toCfg c) = some (toCfg (M8.step c)) := by
  rcases c with ⟨st, L, h, R⟩
  cases st <;> cases h
  · cases R <;> rfl
  · cases R <;> rfl
  · cases L <;> rfl
  · cases L <;> rfl
  · cases R <;> rfl
  · cases L <;> rfl
  · cases L <;> rfl
  · cases L <;> rfl
  · cases L <;> rfl
  · cases L <;> rfl
  · exfalso; apply hne; rfl
  · cases R <;> rfl
  · exfalso; apply hne; rfl
  · exfalso; apply hne; rfl
lemma multiStep_toCfg (n : Nat) :
    multiStep target_tm (init []) n = some (toCfg (M8.run n M8.init)) := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [multiStep, Function.iterate_succ', Function.comp_apply, <- multiStep, ih, Option.bind_some]
    have hrun : M8.run (n + 1) M8.init = M8.step (M8.run n M8.init) := M8.run_add n 1 M8.init
    have hne : (M8.step (M8.run n M8.init)).st ≠ .H := by
      rw [<- hrun]; exact M8.R3.nonhalt (n + 1)
    rw [hrun]
    exact step_toCfg (M8.run n M8.init) hne

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
theorem is_does_not_halt : IsNotHalt target_tm := by
  intro cfg ⟨n, hn⟩
  rw [multiStep_toCfg n, Option.some.injEq] at hn
  subst hn
  have hrun : M8.run (n + 1) M8.init = M8.step (M8.run n M8.init) := M8.run_add n 1 M8.init
  have hne : (M8.step (M8.run n M8.init)).st ≠ .H := by
    rw [<- hrun]; exact M8.R3.nonhalt (n + 1)
  rw [step_toCfg (M8.run n M8.init) hne]
  rfl

end BusyBeaver.M_1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_HHH1RA
