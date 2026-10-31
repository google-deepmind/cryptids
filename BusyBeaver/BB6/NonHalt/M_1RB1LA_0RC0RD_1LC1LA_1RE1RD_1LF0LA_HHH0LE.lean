/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_HHH0LE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_---0LE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 0 Dir.left)

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
def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
namespace Prefix
def mass (xs : List ℕ) : ℕ:=xs.foldr (· + ·) 0
@[simp] lemma mass_nil : mass []=0:=rfl
@[simp] lemma mass_cons (x : ℕ) (xs : List ℕ) : mass (x :: xs)=x + mass xs:=rfl
lemma mass_append (xs ys : List ℕ) : mass (xs ++ ys)=mass xs + mass ys:= by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_assoc]
inductive Step : ℕ → List ℕ → List ℕ → Prop where
  | E (n v w : ℕ) (r : List ℕ) : Step 1 ((2 * n) :: v :: w :: r) ((2 * n + v + w + 3) :: r)
  | O (n v w : ℕ) (r : List ℕ) : 1 ≤ n + v →
      Step 0 ((2 * n + 1) :: v :: w :: r) ((n + v - 1) :: 0 :: 1 :: (w + n + 1) :: r)
inductive Run : ℕ → List ℕ → List ℕ → Prop where
  | refl (xs : List ℕ) : Run 0 xs xs
  | cons {e f : ℕ} {xs ys zs : List ℕ} : Step e xs ys → Run f ys zs → Run (e + f) xs zs
lemma one {e : ℕ} {xs ys : List ℕ} (h : Step e xs ys) : Run e xs ys:= by
  simpa using! Run.cons h (Run.refl ys)
lemma trans {e f : ℕ} {xs ys zs : List ℕ} (h1 : Run e xs ys) (h2 : Run f ys zs) :
    Run (e + f) xs zs:= by
  induction h1 with
  | refl _ => simpa using! h2
  | cons hs _ ih =>
    rw [Nat.add_assoc]
    exact Run.cons hs (ih h2)
lemma step_app {e : ℕ} {xs ys : List ℕ} (r : List ℕ) (h : Step e xs ys) :
    Step e (xs ++ r) (ys ++ r):= by
  cases h with
  | E n v w r0 => exact Step.E n v w (r0 ++ r)
  | O n v w r0 hle => exact Step.O n v w (r0 ++ r) hle
lemma app {e : ℕ} {xs ys : List ℕ} (r : List ℕ) (h : Run e xs ys) :
    Run e (xs ++ r) (ys ++ r):= by
  induction h with
  | refl _ => exact Run.refl _
  | cons hs _ ih => exact Run.cons (step_app r hs) ih
lemma step_mass {e : ℕ} {xs ys : List ℕ} (h : Step e xs ys) :
    mass ys=mass xs + 3 * e:= by
  cases h <;> simp [mass] <;> omega
lemma step_length {e : ℕ} {xs ys : List ℕ} (h : Step e xs ys) :
    xs.length ≤ ys.length + 2 * e:= by
  cases h <;> simp <;> omega
lemma run_length {e : ℕ} {xs ys : List ℕ} (h : Run e xs ys) :
    xs.length ≤ ys.length + 2 * e:= by
  induction h with
  | refl _ => omega
  | cons hs _ ih =>
    have hl:=step_length hs
    omega
lemma qaS {α : Type*} : ∀ (l : List α),l ≠ [] → ∃ p z,l=p ++ [z]
  | [],h => absurd rfl h
  | [x],_ => ⟨[],x,rfl⟩
  | x :: y :: r,_ => by
    rcases qaS (y :: r) (by simp) with ⟨p,z,hp⟩
    exact ⟨x :: p,z,by simp [hp]⟩
lemma qN {α : Type*} {p1 p2 : List α} {z1 z2 : α}
    (h : p1 ++ [z1]=p2 ++ [z2]) : p1=p2 ∧ z1=z2:= by
  have h1:=List.append_inj_left' h rfl
  have h2:=List.append_inj_right' h rfl
  exact ⟨h1,by simpa using! h2⟩
lemma step_last {e : ℕ} {xs ys : List ℕ} (h : Step e xs ys) :
    ∀ p z,xs=p ++ [z] →
      ∃ q d,ys=q ++ [z + d] ∧ ∀ z',Step e (p ++ [z']) (q ++ [z' + d]):= by
  cases h with
  | E n v w r =>
    intro p z hx
    cases r with
    | nil =>
      have hx' : [2 * n,v] ++ [w]=p ++ [z]:=hx
      rcases qN hx' with ⟨rfl,rfl⟩
      refine ⟨[],2 * n + v + 3,?_,?_⟩
      · simp; omega
      · intro z'
        have hstep:=Step.E n v z' []
        have heq : 2 * n + v + z' + 3=z' + (2 * n + v + 3):= by omega
        simpa [heq] using! hstep
    | cons h0 r0 =>
      rcases qaS (h0 :: r0) (by simp) with ⟨p0,z0,hr0⟩
      rw [hr0] at hx ⊢
      have hx' : (2 * n :: v :: w :: p0) ++ [z0]=p ++ [z]:=hx
      rcases qN hx' with ⟨rfl,rfl⟩
      refine ⟨(2 * n + v + w + 3) :: p0,0,?_,?_⟩
      · simp
      · intro z'
        simpa using! Step.E n v w (p0 ++ [z'])
  | O n v w r hsafe =>
    intro p z hx
    cases r with
    | nil =>
      have hx' : [2 * n + 1,v] ++ [w]=p ++ [z]:=hx
      rcases qN hx' with ⟨rfl,rfl⟩
      refine ⟨[n + v - 1,0,1],n + 1,?_,?_⟩
      · simp; omega
      · intro z'
        have hstep:=Step.O n v z' [] hsafe
        have heq : z' + n + 1=z' + (n + 1):= by omega
        simpa [heq] using! hstep
    | cons h0 r0 =>
      rcases qaS (h0 :: r0) (by simp) with ⟨p0,z0,hr0⟩
      rw [hr0] at hx ⊢
      have hx' : ((2 * n + 1) :: v :: w :: p0) ++ [z0]=p ++ [z]:=hx
      rcases qN hx' with ⟨rfl,rfl⟩
      refine ⟨(n + v - 1) :: 0 :: 1 :: (w + n + 1) :: p0,0,?_,?_⟩
      · simp
      · intro z'
        simpa using! Step.O n v w (p0 ++ [z']) hsafe
lemma run_last {e : ℕ} {xs ys : List ℕ} (h : Run e xs ys) :
    ∀ p z,xs=p ++ [z] →
      ∃ q d,ys=q ++ [z + d] ∧ ∀ z',Run e (p ++ [z']) (q ++ [z' + d]):= by
  induction h with
  | refl xs =>
    intro p z hx
    refine ⟨p,0,by simpa using! hx,fun z' => by simpa using! Run.refl (p ++ [z'])⟩
  | cons hs hr ih =>
    intro p z hx
    rcases step_last hs p z hx with ⟨p1,d1,hy,hstep⟩
    rcases ih p1 (z + d1) hy with ⟨p2,d2,hz,hrun⟩
    refine ⟨p2,d1 + d2,by simpa [Nat.add_assoc] using! hz,fun z' => ?_⟩
    rw [← Nat.add_assoc]
    exact Run.cons (hstep z') (hrun (z' + d1))
def geometric : ℕ → ℕ → List ℕ
  | 0,_ => []
  | k + 1,q => q :: geometric k (2 * q)
def F (k q : ℕ) : List ℕ:=(q + 1) :: geometric k q
def G (k q : ℕ) : List ℕ :=
  match k with
  | 0 => [q]
  | k + 1 => F k q ++ [2 ^ k * q - 1]
lemma qY (k q : ℕ) : geometric (k + 1) q=geometric k q ++ [2 ^ k * q]:= by
  induction k generalizing q with
  | zero => simp [geometric]
  | succ k ih =>
    conv_lhs => rw [geometric]; rw [ih (2 * q)]
    conv_rhs => rw [geometric]
    simp only [List.cons_append,List.cons.injEq,true_and]
    congr 2
    rw [Nat.pow_succ]
    ring
lemma qY' (k q : ℕ) : geometric (1 + k) q=geometric k q ++ [2 ^ k * q]:= by
  rw [Nat.add_comm 1 k,qY]
lemma geometric_length (k q : ℕ) : (geometric k q).length=k:= by
  induction k generalizing q with
  | zero => rfl
  | succ k ih => simp [geometric,ih]
lemma F_snoc (k q : ℕ) : F (1 + k) q=F k q ++ [2 ^ k * q]:= by
  simp [F,qY']
lemma F_to_G {e k q : ℕ} {ys : List ℕ} {a : ℕ} (hq : 0 < q)
    (h : Run e (F (1 + k) q) (ys ++ [1 + a])) :
    Run e (G (1 + k) q) (ys ++ [a]):= by
  rcases run_last h (F k q) (2 ^ k * q) (F_snoc k q) with ⟨p,d,he,hr⟩
  rcases qN he with ⟨rfl,ha⟩
  have hpow : 0 < 2 ^ k:=Nat.pos_of_ne_zero (by positivity)
  have hpos : 1 ≤ 2 ^ k * q:=Nat.mul_pos hpow hq
  have h1:=hr (2 ^ k * q - 1)
  have heq : 2 ^ k * q - 1 + d=a:= by omega
  have hg : G (1 + k) q=F k q ++ [2 ^ k * q - 1]:= by
    rw [Nat.add_comm 1 k]; rfl
  rw [hg,← heq]
  exact h1
lemma odd_descent (k t w : ℕ) (r : List ℕ) :
    Run 1 ((2 ^ k * (3 + 2 * t) - 3) :: 0 :: 1 :: w :: r)
      ((4 + 2 * t) :: geometric k (3 + 2 * t) ++ w :: r):= by
  induction k generalizing w r with
  | zero =>
    simp only [Nat.pow_zero,Nat.one_mul,Nat.add_sub_cancel_left,geometric,List.nil_append]
    have hstep:=Step.E t 0 1 (w :: r)
    have h1 : 2 * t + 0 + 1 + 3=4 + 2 * t:= by omega
    simpa [h1] using! one hstep
  | succ k ih =>
    have hpow : 1 ≤ 2 ^ k:=Nat.one_le_pow k 2 (by decide)
    have hp : 3 ≤ 2 ^ k * (3 + 2 * t):= by nlinarith
    simp only [qY,List.append_assoc,List.cons_append,List.nil_append]
    have h0 : Step 0 ((2 ^ (k + 1) * (3 + 2 * t) - 3) :: 0 :: 1 :: w :: r)
        ((2 ^ k * (3 + 2 * t) - 3) :: 0 :: 1 :: (2 ^ k * (3 + 2 * t)) :: w :: r):= by
      have ho:=Step.O (2 ^ k * (3 + 2 * t) - 2) 0 1 (w :: r) (by omega)
      have hmul : 2 ^ (k + 1) * (3 + 2 * t)=2 * (2 ^ k * (3 + 2 * t)):= by
        rw [Nat.pow_succ]; ring
      have ha : 2 * (2 ^ k * (3 + 2 * t) - 2) + 1=2 ^ (k + 1) * (3 + 2 * t) - 3:= by
        omega
      have hb : 2 ^ k * (3 + 2 * t) - 2 + 0 - 1=2 ^ k * (3 + 2 * t) - 3:= by omega
      have hc : 1 + (2 ^ k * (3 + 2 * t) - 2) + 1=2 ^ k * (3 + 2 * t):= by omega
      rw [ha,hb,hc] at ho
      exact ho
    have h1:=ih (2 ^ k * (3 + 2 * t)) (w :: r)
    simpa [List.append_assoc] using! Run.cons h0 h1
lemma qcn {k t n v : ℕ} (w : ℕ) (r : List ℕ) (h : n + v + 2=2 ^ k * (3 + 2 * t)) :
    Run 1 ((2 * n + 1) :: v :: w :: r)
      ((4 + 2 * t) :: geometric k (3 + 2 * t) ++ (w + n + 1) :: r):= by
  have hpow : 1 ≤ 2 ^ k:=Nat.one_le_pow k 2 (by decide)
  have hp : 3 ≤ 2 ^ k * (3 + 2 * t):= by nlinarith
  have h0 : Step 0 ((2 * n + 1) :: v :: w :: r)
      ((2 ^ k * (3 + 2 * t) - 3) :: 0 :: 1 :: (w + n + 1) :: r):= by
    have ho:=Step.O n v w r (by omega)
    have ha : n + v - 1=2 ^ k * (3 + 2 * t) - 3:= by omega
    rw [ha] at ho
    exact ho
  exact Run.cons h0 (odd_descent k t (w + n + 1) r)
lemma odd_lookup {k t n v : ℕ} (w : ℕ) (r : List ℕ) {e : ℕ} {ys : List ℕ} {a : ℕ}
    (hn : n + v + 2=2 ^ k * (3 + 2 * t))
    (hr : Run e (F (1 + k) (3 + 2 * t)) (ys ++ [a])) :
    Run (1 + e) ((2 * n + 1) :: v :: w :: r) ((ys ++ [a + w - v - 1]) ++ r):= by
  have hf : F (1 + k) (3 + 2 * t)=F k (3 + 2 * t) ++ [2 ^ k * (3 + 2 * t)]:=F_snoc k (3 + 2 * t)
  rcases run_last hr (F k (3 + 2 * t)) (2 ^ k * (3 + 2 * t)) hf with ⟨p,d,hlast,hrun⟩
  rcases qN hlast with ⟨rfl,ha⟩
  have h1 : Run 1 ((2 * n + 1) :: v :: w :: r) ((F k (3 + 2 * t) ++ [w + n + 1]) ++ r):= by
    have he:=qcn w r hn
    have hfeq : (4 + 2 * t) :: geometric k (3 + 2 * t) ++ (w + n + 1) :: r =
        (F k (3 + 2 * t) ++ [w + n + 1]) ++ r:= by
      simp only [F,List.cons_append,List.nil_append,List.append_assoc,List.cons.injEq,and_true]
      omega
    rwa [← hfeq]
  have h2 : Run e ((F k (3 + 2 * t) ++ [w + n + 1]) ++ r) ((ys ++ [a + w - v - 1]) ++ r):= by
    have hr':=app r (hrun (w + n + 1))
    have haeq : w + n + 1 + d=a + w - v - 1:= by omega
    rwa [haeq] at hr'
  exact trans h1 h2
inductive Exec : ℕ → List ℕ → List ℕ → Prop where
  | stop (xs : List ℕ) : Exec 0 xs xs
  | take {e f : ℕ} {xs ys zs : List ℕ} : Step e xs ys → Exec f ys zs → Exec (e + f) xs zs
  | zero {e : ℕ} {xs ys : List ℕ} : Exec e (xs ++ [0]) ys → Exec e xs ys
lemma run_exec {e : ℕ} {xs ys : List ℕ} (h : Run e xs ys) : Exec e xs ys:= by
  induction h with
  | refl _ => exact Exec.stop _
  | cons hs _ ih => exact Exec.take hs ih
lemma exec_trans {e f : ℕ} {xs ys zs : List ℕ} (h1 : Exec e xs ys) (h2 : Exec f ys zs) :
    Exec (e + f) xs zs:= by
  induction h1 with
  | stop _ => simpa using! h2
  | take hs _ ih =>
    rw [Nat.add_assoc]
    exact Exec.take hs (ih h2)
  | zero _ ih => exact Exec.zero (ih h2)
lemma mass_zero (xs : List ℕ) : mass (xs ++ [0])=mass xs:= by
  simp [mass_append]
lemma exec_mass {e : ℕ} {xs ys : List ℕ} (h : Exec e xs ys) :
    mass ys=mass xs + 3 * e:= by
  induction h with
  | stop _ => omega
  | take hs _ ih =>
    have hm:=step_mass hs
    omega
  | zero _ ih =>
    rw [mass_zero] at ih
    exact ih
lemma split2 (n : ℕ) (hn : 0 < n) : ∃ k t,n=2 ^ k * (1 + 2 * t):= by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases Nat.even_or_odd' n with ⟨a,rfl | rfl⟩
    · have ha : 0 < a:= by omega
      have hlt : a < 2 * a:= by omega
      rcases ih a hlt ha with ⟨k,t,hk⟩
      refine ⟨k + 1,t,?_⟩
      rw [Nat.pow_succ]
      linarith
    · exact ⟨0,a,by simp [Nat.add_comm]⟩
lemma pow2_mod3 (n : ℕ) : 2 ^ n % 3=1 ∨ 2 ^ n % 3=2:= by
  induction n with
  | zero => left; rfl
  | succ n ih =>
    rw [Nat.pow_succ,Nat.mul_mod]
    rcases ih with h | h <;> rw [h] <;> decide
lemma single_returns
    (hG : ∀ k t,∃ e m,Exec e (G (1 + k) (1 + 2 * t)) [m])
    (j : ℕ) : ∃ e m,Exec (1 + e) [3 * j] [m]:= by
  rcases Nat.even_or_odd' (3 * j) with ⟨n,hn | hn⟩
  · refine ⟨0,2 * n + 3,?_⟩
    rw [hn]
    apply Exec.zero
    apply Exec.zero
    apply run_exec
    simpa using! one (Step.E n 0 0 [])
  · rcases split2 (n + 2) (by omega) with ⟨k,t,hk⟩
    have ht : 1 ≤ t:= by
      by_contra hlt
      have ht0 : t=0:= by omega
      subst ht0
      have hp : 2 ^ (k + 1)=(j + 1) * 3:= by
        rw [Nat.pow_succ]
        omega
      have hmod:=pow2_mod3 (k + 1)
      rw [hp,Nat.mul_mod_left] at hmod
      rcases hmod with h | h <;> contradiction
    rcases hG k t with ⟨e,m,hr⟩
    refine ⟨e,m,?_⟩
    apply Exec.zero
    apply Exec.zero
    change Exec (1 + e) [3 * j,0,0] [m]
    rw [hn]
    have ht1 : 3 + 2 * (t - 1)=1 + 2 * t:= by omega
    have ht2 : 4 + 2 * (t - 1)=1 + 2 * t + 1:= by omega
    have ht3 : n + 1=2 ^ k * (1 + 2 * t) - 1:= by omega
    have hn_eq : n + 0 + 2=2 ^ k * (3 + 2 * (t - 1)):= by
      rw [ht1]; omega
    have hexp:=qcn (k:=k) (t:=t - 1) (n:=n) (v:=0) 0 [] hn_eq
    have hge : (4 + 2 * (t - 1)) :: geometric k (3 + 2 * (t - 1)) ++ (0 + n + 1) :: [] =
        G (1 + k) (1 + 2 * t):= by
      rw [Nat.add_comm 1 k]
      simp only [G,F,ht1,ht2,Nat.zero_add,ht3]
    rw [hge] at hexp
    exact exec_trans (run_exec hexp) hr
end Prefix
def q0 (k : ℤ) : ℤ :=
  match k with
  | Int.ofNat n => Int.ofNat (Nat.pow 2 n)
  | Int.negSucc _ => 0
def ZEven (x : ℤ) : Prop:=∃ k : ℤ,x=2 * k
def qW (x : ℤ) : Prop:=∃ k : ℤ,x=2 * k + 1
def qb6 (x : ℤ) : Bool:=decide (x % 2=0)
def zodd (x : ℤ) : Bool:=decide (x % 2=1)
lemma qe {k : ℤ} (hk : 0 ≤ k) : q0 k=(2 : ℤ) ^ k.toNat:= by
  cases k with
  | ofNat n =>
    change ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n
    exact Nat.cast_pow 2 n
  | negSucc n => omega
@[simp] lemma pow2_zero : q0 0=1:=rfl
@[simp] lemma pow2_one : q0 1=2:=rfl
lemma qc {k : ℤ} (hk : 0 ≤ k) : 0 < q0 k:= by
  rw [qe hk]; positivity
lemma qs (k : ℤ) : 0 ≤ q0 k:= by
  cases k with
  | ofNat n => exact Int.natCast_nonneg (2 ^ n)
  | negSucc n => exact le_refl 0
lemma q5 {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    q0 (a + b)=q0 a * q0 b:= by
  rw [qe (by omega),qe ha,qe hb,
    Int.toNat_add ha hb,pow_add]
lemma qcl {k d : ℤ} (hd : 0 ≤ d) (hdk : d ≤ k) :
    q0 k=q0 d * q0 (k - d):= by
  have h:=q5 hd (sub_nonneg.mpr hdk)
  rwa [add_sub_cancel] at h
lemma qd {a b : ℤ} (ha : 0 ≤ a) (hab : a ≤ b) :
    q0 a ≤ q0 b:= by
  rw [qcl ha hab]
  have hpos : 1 ≤ q0 (b - a):= by
    have:=qc (sub_nonneg.mpr hab)
    omega
  have ha_pos:=qc ha
  nlinarith
lemma qbm {a b : ℤ} (ha : 0 ≤ a) (hab : a < b) :
    q0 a < q0 b:= by
  have hle : a + 1 ≤ b:= by omega
  have h1 : q0 (a + 1) ≤ q0 b:=qd (by omega) hle
  rw [q5 ha (by omega),pow2_one] at h1
  have ha_pos:=qc ha
  omega
lemma qv {a b : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    q0 a < q0 b ↔ a < b:= by
  constructor
  · intro hlt
    by_contra hge
    have hle : q0 b ≤ q0 a:=qd hb (by omega)
    omega
  · exact qbm ha
lemma qah (x : ℤ) : qb6 x=true ↔ ZEven x:= by
  simp only [qb6,decide_eq_true_iff,ZEven]
  constructor
  · intro h; exact ⟨x / 2,by omega⟩
  · rintro ⟨k,rfl⟩; omega
lemma zodd_iff (x : ℤ) : zodd x=true ↔ qW x:= by
  simp only [zodd,decide_eq_true_iff,qW]
  constructor
  · intro h; exact ⟨x / 2,by omega⟩
  · rintro ⟨k,rfl⟩; omega
lemma qa9 (x : ℤ) : qb6 x=false ↔ qW x:= by
  simp only [qb6,decide_eq_false_iff_not,qW]
  constructor
  · intro h; exact ⟨x / 2,by omega⟩
  · rintro ⟨k,rfl⟩; omega
def qS : ℕ → ℕ → ℕ
  | 0,_ => 0
  | fuel + 1,n => if n < 2 then 0 else qS fuel (n / 2) + 1
lemma qcb {fuel n : ℕ} (hn : 0 < n) (hle : n ≤ fuel) :
    2 ^ qS fuel n ≤ n ∧ n < 2 ^ (qS fuel n + 1):= by
  induction fuel generalizing n with
  | zero => omega
  | succ fuel ih =>
    unfold qS
    split_ifs with hlt
    · simp only [Nat.pow_zero,Nat.zero_add,Nat.pow_one]
      omega
    · rcases ih (n:=n / 2) (by omega) (by omega) with ⟨hlo,hhi⟩
      rw [Nat.pow_succ,Nat.pow_succ]
      omega
def qH (x : ℤ) : ℤ :=
  if x ≤ 0 then 0 else (qS x.toNat x.toNat : ℤ)
lemma qM (x : ℤ) : 0 ≤ qH x:= by
  unfold qH; split_ifs <;> positivity
lemma qag {x : ℤ} (hx : 0 < x) :
    q0 (qH x) ≤ x ∧ x < q0 (qH x + 1):= by
  have hle : ¬ x ≤ 0:= by omega
  unfold qH
  rw [if_neg hle]
  rcases qcb (fuel:=x.toNat) (n:=x.toNat) (by omega) (le_refl _) with ⟨hlo,hhi⟩
  rw [qe (by positivity),qe (by positivity)]
  have h1 : ((qS x.toNat x.toNat : ℤ) + 1).toNat=qS x.toNat x.toNat + 1:= by omega
  rw [Int.toNat_natCast,h1]
  have hlo' : ((2 ^ qS x.toNat x.toNat : ℕ) : ℤ) ≤ (x.toNat : ℤ):=Int.ofNat_le.mpr hlo
  have hhi' : (x.toNat : ℤ) < ((2 ^ (qS x.toNat x.toNat + 1) : ℕ) : ℤ):=Int.ofNat_lt.mpr hhi
  push_cast at hlo' hhi'
  rw [Int.toNat_of_nonneg (by omega)] at hlo' hhi'
  exact ⟨hlo',hhi'⟩
lemma qas {x y : ℤ} (hxy : x ≤ y) : qH x ≤ qH y:= by
  by_cases hx : x ≤ 0
  · have : qH x=0:= by unfold qH; rw [if_pos hx]
    have:=qM y
    omega
  · push Not at hx
    have hy : 0 < y:= by omega
    rcases qag hx with ⟨hx1,_⟩
    rcases qag hy with ⟨_,hy2⟩
    have hlt : q0 (qH x) < q0 (qH y + 1):= by omega
    have hlt':=(qv (qM x) (by have:=qM y; omega)).mp hlt
    omega
lemma qck {a : ℤ} (ha : 0 ≤ a) : qH (q0 a)=a:= by
  have hp : 0 < q0 a:=qc ha
  rcases qag hp with ⟨h1,h2⟩
  have hlt1:=(qv ha (by have:=qM (q0 a); omega)).mp h2
  by_contra hne
  have hgt : a < qH (q0 a):= by omega
  have hle:=qd (by omega : 0 ≤ a + 1) (by omega : a + 1 ≤ qH (q0 a))
  rw [q5 ha (by omega),pow2_one] at hle
  omega
def q1 (x : ℤ) : ℤ :=
  if x ≤ 1 then 0 else qH (x - 1) + 1
lemma qh (x : ℤ) : 0 ≤ q1 x:= by
  unfold q1
  split_ifs
  · omega
  · have:=qM (x - 1); omega
lemma qy {x : ℤ} (hx : 1 < x) :
    q0 (q1 x - 1) < x ∧ x ≤ q0 (q1 x):= by
  unfold q1
  rw [if_neg (by omega)]
  have hsub : qH (x - 1) + 1 - 1=qH (x - 1):= by ring
  rw [hsub]
  rcases qag (by omega : 0 < x - 1) with ⟨h1,h2⟩
  omega
lemma qt {x y : ℤ} (hxy : x ≤ y) : q1 x ≤ q1 y:= by
  unfold q1
  split_ifs with hx hy
  · omega
  · have:=qM (y - 1); omega
  · omega
  · have:=qas (by omega : x - 1 ≤ y - 1); omega
lemma qar {a : ℤ} (ha : 0 ≤ a) : q1 (q0 a)=a:= by
  by_cases ha0 : a=0
  · subst ha0; simp [q1,q0]
  · have ha1 : 1 ≤ a:= by omega
    have hp : 1 < q0 a:= by
      have:=qd (by omega : (0 : ℤ) ≤ 1) ha1
      rw [pow2_one] at this; omega
    rcases qy hp with ⟨h1,h2⟩
    have hzu:=qh (q0 a)
    have hzu1 : 1 ≤ q1 (q0 a):= by
      by_contra h
      have h0 : q1 (q0 a)=0:= by omega
      rw [h0,pow2_zero] at h2
      omega
    have hlt:=(qv (by omega : 0 ≤ q1 (q0 a) - 1) ha).mp h1
    by_contra hne
    have hgt : q1 (q0 a) < a:= by omega
    have hle:=qd (by omega : 0 ≤ q1 (q0 a) + 1) (by omega : q1 (q0 a) + 1 ≤ a)
    rw [q5 hzu (by omega),pow2_one] at hle
    have hp0:=qc hzu
    omega
lemma qm {x a : ℤ} (hx : 0 < x) (ha : 0 ≤ a) :
    x ≤ q0 a ↔ q1 x ≤ a:= by
  constructor
  · intro hle
    have:=qt hle
    rwa [qar ha] at this
  · intro hle
    by_cases hx1 : x ≤ 1
    · have:=qc ha; omega
    · push Not at hx1
      rcases qy hx1 with ⟨_,h2⟩
      have hmono:=qd (qh x) hle
      omega
def sNat {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn n (f 0) (fun m => f (Nat.succ m))
@[simp] lemma sNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) : sNat n f = f n := by
  cases n <;> rfl
def q2 {α : Type*} (x : ℤ) (f : ℤ → α) : α :=
  Int.casesOn x (fun n => sNat n (fun n' => f (Int.ofNat n'))) (fun n => sNat n (fun n' => f (Int.negSucc n')))
@[simp] lemma strictInt_eq {α : Type*} (x : ℤ) (f : ℤ → α) : q2 x f=f x:= by
  cases x with
  | ofNat n => cases n <;> rfl
  | negSucc n => cases n <;> rfl
def q4 : ℕ → ℤ → ℤ × ℤ
  | 0,x => (0,x)
  | fuel + 1,x =>
    if x % 2=0 then
      let p:=q4 fuel (x / 2)
      (p.1 + 1,p.2)
    else
      (0,x)
lemma qaw (fuel : ℕ) (x : ℤ) :
    0 ≤ (q4 fuel x).1 ∧
    (q4 fuel x).1 ≤ (fuel : ℤ) ∧
    x=q0 (q4 fuel x).1 * (q4 fuel x).2 ∧
    ((q4 fuel x).1 < (fuel : ℤ) → qW (q4 fuel x).2):= by
  induction fuel generalizing x with
  | zero =>
    simp only [q4,Nat.cast_zero,le_refl,pow2_zero,one_mul,lt_self_iff_false,
      IsEmpty.forall_iff,and_self]
  | succ fuel ih =>
    unfold q4
    split_ifs with hmod
    · rcases ih (x / 2) with ⟨hs0,hsf,heq,hodd⟩
      dsimp -failIfUnchanged
      refine ⟨by omega,by omega,?_,?_⟩
      · rw [q5 hs0 (by omega),pow2_one]
        have hx : x=2 * (x / 2):= by omega
        linarith
      · intro hlt
        exact hodd (by omega)
    · dsimp -failIfUnchanged
      refine ⟨by omega,by omega,by simp [pow2_zero],?_⟩
      intro _
      exact ⟨x / 2,by omega⟩
lemma qbP (n : ℕ) : (n : ℤ) < q0 (n : ℤ):= by
  induction n with
  | zero => simp [q0]
  | succ n ih =>
    push_cast
    rw [q5 (by positivity) (by omega),pow2_one]
    have hp:=qc (k:=(n : ℤ)) (by positivity)
    omega
lemma qbH {x : ℤ} (hx : 0 < x) :
    0 ≤ (q4 x.toNat x).1 ∧
    x=q0 (q4 x.toNat x).1 * (q4 x.toNat x).2 ∧
    qW (q4 x.toNat x).2:= by
  rcases qaw x.toNat x with ⟨hs0,hsf,heq,hodd⟩
  refine ⟨hs0,heq,hodd ?_⟩
  by_contra hge
  have hs : (q4 x.toNat x).1=(x.toNat : ℤ):= by omega
  rw [hs,Int.toNat_of_nonneg (by omega)] at heq
  have hp:=qc (by omega : 0 ≤ x)
  have hr : 1 ≤ (q4 x.toNat x).2:= by nlinarith
  have hlt:=qbP x.toNat
  rw [Int.toNat_of_nonneg (by omega)] at hlt
  nlinarith
namespace Block
structure kernel where
  den : ℤ
  num : ℤ
  bias : ℤ
  gain : ℤ
  deriving DecidableEq,Repr
def good (k : kernel) : Prop :=
  0 < k.den ∧ 0 < k.num ∧ 2 * k.num ≤ k.den ∧ 1 ≤ k.bias ∧ k.bias + 2 ≤ k.gain
def call (k : kernel) (S H S' H' : ℤ) : Prop :=
  S'=S + k.gain ∧
  k.den * H'=2 * k.den * S - k.num * H + k.den * (2 * k.gain + 3 - k.bias)
structure summary where
  scale : ℤ
  sc : ℤ
  hc : ℤ
  offset : ℤ
  added : ℤ
  deriving DecidableEq,Repr
def identity : summary:=⟨1,0,1,0,0⟩
def push (k : kernel) (z : summary) : summary :=
  ⟨k.den * z.scale,
   2 * k.den * z.scale - k.num * z.sc,
   -k.num * z.hc,
   k.den * z.scale * (2 * z.added + 2 * k.gain + 3 - k.bias) - k.num * z.offset,
   z.added + k.gain⟩
def denotes (z : summary) (S H S' H' : ℤ) : Prop :=
  S'=S + z.added ∧ z.scale * H'=z.sc * S + z.hc * H + z.offset
def bounded (z : summary) : Prop :=
  0 < z.scale ∧ 0 ≤ z.sc ∧ z.sc ≤ 2 * z.scale ∧
  0 ≤ z.added ∧ 0 ≤ z.offset ∧ z.offset ≤ z.scale * (2 * z.added + 2)
lemma identity_bounded : bounded identity:= by
  unfold bounded identity; simp
lemma push_bounded (k : kernel) (z : summary) (hk : good k) (hz : bounded z) :
    bounded (push k z) ∧ (push k z).scale ≤ (push k z).sc ∧ 0 < (push k z).offset:= by
  rcases k with ⟨q,p,b,lam⟩
  rcases z with ⟨Q,A,B,C,M⟩
  rcases hk with ⟨hq,hp,hqp,hb,hl⟩
  rcases hz with ⟨hQ,hA0,hA1,hM,hC0,hC1⟩
  simp only [bounded,push] at *
  have hqQ : 0 < q * Q:=mul_pos hq hQ
  have hpA1 : p * A ≤ q * Q:= by nlinarith
  have hpC0 : 0 ≤ p * C:= by positivity
  have hpC1 : p * C ≤ (q * Q) * (M + 1):= by
    have : p * C ≤ p * (Q * (2 * M + 2)):= by nlinarith
    have : (2 * p) * (Q * (M + 1)) ≤ q * (Q * (M + 1)):= by nlinarith
    linarith
  have hbl : (q * Q) * (b + 2) ≤ (q * Q) * lam:= by nlinarith
  have hb1 : (q * Q) * 1 ≤ (q * Q) * b:= by nlinarith
  have hM0 : 0 ≤ (q * Q) * M:= by nlinarith
  refine ⟨⟨by nlinarith,by nlinarith,by nlinarith,by linarith,by linarith,by linarith⟩,
    by nlinarith,by linarith⟩
lemma push_sound (k : kernel) (z : summary) (S H S1 H1 S2 H2 : ℤ)
    (hz : denotes z S H S1 H1) (hk : call k S1 H1 S2 H2) :
    denotes (push k z) S H S2 H2:= by
  rcases k with ⟨q,p,b,lam⟩
  rcases z with ⟨Q,A,B,C,M⟩
  unfold denotes call push at *
  dsimp -failIfUnchanged at *
  rcases hz with ⟨rfl,hH1⟩
  rcases hk with ⟨rfl,hH2⟩
  refine ⟨by ring,?_⟩
  calc q * Q * H2 = Q * (q * H2) := by ring
    _ = Q * (2 * q * (S + M) - p * H1 + q * (2 * lam + 3 - b)) := by rw [hH2]
    _ = Q * (2 * q * (S + M) + q * (2 * lam + 3 - b)) - p * (Q * H1) := by ring
    _ = Q * (2 * q * (S + M) + q * (2 * lam + 3 - b)) - p * (A * S + B * H + C) := by rw [hH1]
    _ = (2 * q * Q - p * A) * S + -p * B * H + (q * Q * (2 * M + 2 * lam + 3 - b) - p * C) := by ring
inductive calls : List kernel → ℤ → ℤ → ℤ → ℤ → Prop where
  | no_calls (S H : ℤ) : calls [] S H S H
  | more_calls {k : kernel} {ks : List kernel} {S H S1 H1 S2 H2 : ℤ} :
      call k S H S1 H1 → calls ks S1 H1 S2 H2 → calls (k :: ks) S H S2 H2
lemma fold_sound {ks : List kernel} {S H S' H' : ℤ} (hrun : calls ks S H S' H') :
    ∀ z S0 H0,denotes z S0 H0 S H →
      denotes (ks.foldl (fun z k => push k z) z) S0 H0 S' H':= by
  induction hrun with
  | no_calls _ _ => intro z S0 H0 hz; exact hz
  | more_calls hstep _ ih =>
    intro z S0 H0 hz
    exact ih (push _ z) S0 H0 (push_sound _ _ _ _ _ _ _ _ hz hstep)
def low_push (k : kernel) (z : summary) : summary :=
  ⟨k.den * z.scale,
   k.num * (2 * z.scale - z.sc),
   -k.num * z.hc,
   k.num * z.scale * (2 * z.added + 3) - k.num * z.offset + k.den * z.scale * k.bias,
   z.added + k.gain⟩
def qA (z : summary) : Prop :=
  0 < z.scale ∧ 0 ≤ z.sc ∧ z.sc ≤ z.scale ∧
  -z.scale ≤ z.hc ∧ z.hc ≤ z.scale ∧
  0 ≤ z.added ∧ 0 ≤ z.offset ∧ z.offset ≤ z.scale * z.added
lemma qa5 : qA identity:= by
  unfold qA identity; simp
lemma qax (k : kernel) (z : summary) (hk : good k) (hz : qA z) :
    qA (low_push k z) ∧
    -(low_push k z).scale ≤ 2 * (low_push k z).hc ∧
    2 * (low_push k z).hc ≤ (low_push k z).scale:= by
  rcases k with ⟨q,p,b,lam⟩
  rcases z with ⟨Q,E,T,V,K⟩
  rcases hk with ⟨hq,hp,hqp,hb,hl⟩
  rcases hz with ⟨hQ,hE0,hE1,hT0,hT1,hK,hV0,hV1⟩
  simp only [qA,low_push] at *
  have hqQ : 0 < q * Q:=mul_pos hq hQ
  have hpQ : 0 < p * Q:=mul_pos hp hQ
  have hqpQ : 2 * (p * Q) ≤ q * Q:= by nlinarith
  have hpV0 : 0 ≤ p * V:= by positivity
  have hpQK : 0 ≤ (p * Q) * K:= by positivity
  have hpV : p * V ≤ (p * Q) * K:= by
    have : p * V ≤ p * (Q * K):= by nlinarith
    linarith
  have h2K : 2 * ((p * Q) * K) ≤ (q * Q) * K:= by nlinarith
  have hb1 : (q * Q) * 1 ≤ (q * Q) * b:= by nlinarith
  have hbl : (q * Q) * (b + 2) ≤ (q * Q) * lam:= by nlinarith
  have hbias : 3 * (p * Q) + (q * Q) * b ≤ (q * Q) * lam:= by linarith
  refine ⟨⟨by nlinarith,by nlinarith,by nlinarith,by nlinarith,by nlinarith,
    by linarith,by linarith,by linarith⟩,by nlinarith,by nlinarith⟩
lemma qbx (ks : List kernel) (z : summary)
    (hks : ∀ k ∈ ks,good k) (hz : qA z) :
    qA (ks.foldl (fun z k => low_push k z) z):= by
  induction ks generalizing z with
  | nil => exact hz
  | cons k ks ih =>
    exact ih (low_push k z) (fun x hx => hks x (List.mem_cons_of_mem k hx))
      (qax k z (hks k List.mem_cons_self) hz).1
def qX (k : kernel) (z : summary) : summary :=
  ⟨k.den * z.scale,
   k.den * (2 * z.scale - z.sc),
   -k.num * z.hc,
   k.den * ((2 * z.scale - z.sc) * k.gain + 2 * z.scale * z.added - z.offset + 3 * z.scale - z.hc * k.bias),
   k.gain + z.added⟩
lemma qbe (k : kernel) : qX k identity=push k identity:= by
  cases k; unfold qX push identity; dsimp -failIfUnchanged; congr 1 <;> ring
lemma high_low_push (h k : kernel) (z : summary) :
    push k (qX h z)=qX h (low_push k z):= by
  cases h; cases k; cases z
  unfold qX push low_push; dsimp -failIfUnchanged; congr 1 <;> ring
lemma high_low_fold (h : kernel) (ks : List kernel) (z : summary) :
    ks.foldl (fun z k => push k z) (qX h z) =
    qX h (ks.foldl (fun z k => low_push k z) z):= by
  induction ks generalizing z with
  | nil => rfl
  | cons k ks ih =>
    simp only [List.foldl_cons,high_low_push,ih]
lemma high_low_word (h : kernel) (ks : List kernel) :
    (h :: ks).foldl (fun z k => push k z) identity =
    qX h (ks.foldl (fun z k => low_push k z) identity):= by
  simp only [List.foldl_cons,← qbe,high_low_fold]
lemma low_fold_half (ks : List kernel) (z : summary)
    (hks : ∀ k ∈ ks,good k) (hz : qA z) (hne : ks ≠ []) :
    -(ks.foldl (fun z k => low_push k z) z).scale ≤ 2 * (ks.foldl (fun z k => low_push k z) z).hc ∧
    2 * (ks.foldl (fun z k => low_push k z) z).hc ≤ (ks.foldl (fun z k => low_push k z) z).scale:= by
  induction ks generalizing z with
  | nil => contradiction
  | cons k ks ih =>
    have hk:=hks k List.mem_cons_self
    have hstep:=qax k z hk hz
    cases ks with
    | nil => exact hstep.2
    | cons k2 ks2 =>
      exact ih (low_push k z) (fun x hx => hks x (List.mem_cons_of_mem k hx)) hstep.1 (by simp)
lemma qbT {m z : ℤ} (hm : 0 < m) (hdvd : m ∣ z) (hlt : |z| < m) : z=0:= by
  rcases hdvd with ⟨k,rfl⟩
  rw [abs_lt] at hlt
  have hk : k=0:= by nlinarith
  subst hk; ring
lemma exact_descent (m S H0 H1 H2 Q0 Q1 A0 A1 B0 B1 C0 C1 mass : ℤ)
    (hm : 0 < m) (hd0 : m ∣ H0) (hd1 : m ∣ H1) (hd2 : m ∣ H2)
    (E0 : Q0 * H1=A0 * S + B0 * H0 + C0)
    (E1 : Q1 * H2=A1 * (S + mass) + B1 * H1 + C1)
    (hbound : |A0 * A1 * mass + A0 * C1 - A1 * C0| < m) :
    A0 * C1=A1 * (C0 - A0 * mass):= by
  have E : A0 * A1 * mass + A0 * C1 - A1 * C0 =
      A0 * Q1 * H2 - (A1 * Q0 + A0 * B1) * H1 + A1 * B0 * H0:= by
    calc A0 * A1 * mass + A0 * C1 - A1 * C0
        = A0 * (A1 * (S + mass) + B1 * H1 + C1) - A1 * (A0 * S + B0 * H0 + C0) - A0 * B1 * H1 + A1 * B0 * H0 := by ring
      _ = A0 * (Q1 * H2) - A1 * (Q0 * H1) - A0 * B1 * H1 + A1 * B0 * H0 := by rw [← E1, ← E0]
      _ = A0 * Q1 * H2 - (A1 * Q0 + A0 * B1) * H1 + A1 * B0 * H0 := by ring
  have hd : m ∣ A0 * A1 * mass + A0 * C1 - A1 * C0:= by
    rw [E]
    rcases hd0 with ⟨k0,rfl⟩
    rcases hd1 with ⟨k1,rfl⟩
    rcases hd2 with ⟨k2,rfl⟩
    exact ⟨A0 * Q1 * k2 - (A1 * Q0 + A0 * B1) * k1 + A1 * B0 * k0,by ring⟩
  have hz:=qbT hm hd hbound
  linarith
lemma cross_bound (Q0 Q1 A0 A1 C0 C1 mass M : ℤ)
    (hQ0 : 0 < Q0) (hQ1 : 0 < Q1) (hm0 : 0 ≤ mass) (hm1 : mass ≤ M)
    (hA00 : 0 ≤ A0) (hA01 : A0 ≤ 2 * Q0)
    (hA10 : 0 ≤ A1) (hA11 : A1 ≤ 2 * Q1)
    (hC00 : 0 ≤ C0) (hC01 : C0 ≤ Q0 * (2 * M + 2))
    (hC10 : 0 ≤ C1) (hC11 : C1 ≤ Q1 * (2 * M + 2)) :
    |A0 * A1 * mass + A0 * C1 - A1 * C0| ≤ Q0 * Q1 * (12 * M + 8):= by
  rw [abs_le]
  have hQ01 : 0 < Q0 * Q1:=mul_pos hQ0 hQ1
  have h1 : A0 * A1 ≤ 4 * (Q0 * Q1):= by nlinarith
  have h2 : (A0 * A1) * mass ≤ 4 * (Q0 * Q1) * M:= by
    have : (A0 * A1) * mass ≤ 4 * (Q0 * Q1) * mass:= by nlinarith
    have : (Q0 * Q1) * mass ≤ (Q0 * Q1) * M:= by nlinarith
    linarith
  have h3 : A0 * C1 ≤ 2 * (Q0 * Q1) * (2 * M + 2):= by
    have : A0 * C1 ≤ (2 * Q0) * (Q1 * (2 * M + 2)):= by nlinarith
    linarith
  have h4 : A1 * C0 ≤ 2 * (Q0 * Q1) * (2 * M + 2):= by
    have : A1 * C0 ≤ (2 * Q1) * (Q0 * (2 * M + 2)):= by nlinarith
    linarith
  have h5 : 0 ≤ (A0 * A1) * mass:= by positivity
  have h6 : 0 ≤ A0 * C1:= by positivity
  have h7 : 0 ≤ A1 * C0:= by positivity
  constructor <;> linarith
lemma qci (m D d0 d1 S H0 H1 H2 A0 A1 B0 B1 C0 C1 mass M : ℤ)
    (hm : 0 ≤ m) (hd00 : 0 ≤ d0) (hd01 : d0 ≤ D) (hd10 : 0 ≤ d1) (hd11 : d1 ≤ D)
    (hm0 : 0 ≤ mass) (hm1 : mass ≤ M)
    (hA00 : 0 ≤ A0) (hA01 : A0 ≤ 2 * q0 d0)
    (hA10 : 0 ≤ A1) (hA11 : A1 ≤ 2 * q0 d1)
    (hC00 : 0 ≤ C0) (hC01 : C0 ≤ q0 d0 * (2 * M + 2))
    (hC10 : 0 ≤ C1) (hC11 : C1 ≤ q0 d1 * (2 * M + 2))
    (hH0 : q0 (m + 1) ∣ H0) (hH1 : q0 (m + 1) ∣ H1) (hH2 : q0 (m + 1) ∣ H2)
    (E0 : q0 d0 * H1=A0 * S + B0 * H0 + C0)
    (E1 : q0 d1 * H2=A1 * (S + mass) + B1 * H1 + C1)
    (hbound : q0 (2 * D) * (12 * M + 8) < q0 (m + 1)) :
    A0 * C1=A1 * (C0 - A0 * mass):= by
  have hQ0 : 0 < q0 d0:=qc hd00
  have hQ1 : 0 < q0 d1:=qc hd10
  have hQ : q0 d0 * q0 d1 ≤ q0 (2 * D):= by
    rw [← q5 hd00 hd10]
    exact qd (by omega) (by omega)
  have hcb:=cross_bound (q0 d0) (q0 d1) A0 A1 C0 C1 mass M
    hQ0 hQ1 hm0 hm1 hA00 hA01 hA10 hA11 hC00 hC01 hC10 hC11
  apply exact_descent (q0 (m + 1)) S H0 H1 H2 (q0 d0) (q0 d1)
    A0 A1 B0 B1 C0 C1 mass (qc (by omega)) hH0 hH1 hH2 E0 E1
  have hle : q0 d0 * q0 d1 * (12 * M + 8) ≤ q0 (2 * D) * (12 * M + 8):= by nlinarith
  linarith
lemma qaN (Q A T V K b lam C : ℤ)
    (hQ0 : 0 < Q) (hQA : Q ≤ A) (hT0 : -Q ≤ 2 * T) (hT1 : 2 * T ≤ Q)
    (hV : 0 ≤ V) (hK : 0 ≤ K) (hb0 : 0 ≤ b) (hbl : b ≤ lam)
    (hC : C=A * lam + 2 * Q * K - V + 3 * Q - T * b) :
    2 * C ≤ A * (3 * (lam + K) + 2 * K + 6):= by
  have h1 : -2 * T * b ≤ Q * b:= by nlinarith
  have h2 : Q * b ≤ A * lam:= by nlinarith
  have h3 : Q * K ≤ A * K:= by nlinarith
  have hAK : 0 ≤ A * K:= by nlinarith
  linarith
lemma word_contraction (h : kernel) (ks : List kernel)
    (hh : good h) (hks : ∀ k ∈ ks,good k) :
    let z:=ks.foldl (fun z k => low_push k z) identity
    let r:=(h :: ks).foldl (fun z k => push k z) identity
    2 * r.offset ≤ r.sc * (3 * r.added + 2 * z.added + 6):= by
  intro z r
  have hr : r=qX h z:=high_low_word h ks
  have hz : qA z:=qbx ks identity hks qa5
  cases ks with
  | nil =>
    rcases h with ⟨q,p,b,lam⟩
    rcases hh with ⟨hq,hp,hqp,hb,hl⟩
    simp only [r,z,List.foldl_nil,List.foldl_cons,push,identity]
    nlinarith
  | cons k ks =>
    have hhalf:=low_fold_half (k :: ks) identity hks qa5 (by simp)
    change -z.scale ≤ 2 * z.hc ∧ 2 * z.hc ≤ z.scale at hhalf
    rcases h with ⟨q,p,b,lam⟩
    rcases z with ⟨Q,E,T,V,K⟩
    rcases hh with ⟨hq,hp,hqp,hb,hl⟩
    rcases hz with ⟨hQ,hE0,hE1,hT0,hT1,hK,hV0,hV1⟩
    have hc:=qaN Q (2 * Q - E) T V K b lam
      ((2 * Q - E) * lam + 2 * Q * K - V + 3 * Q - T * b)
      hQ (by linarith) hhalf.1 hhalf.2 hV0 hK (by linarith) (by linarith) rfl
    rw [hr]
    simp only [qX]
    nlinarith
lemma qc6 (A C A0 C0 A1 C1 T mass : ℤ)
    (hA0 : 0 < A0) (h0 : A * C0=A0 * (C - A * T))
    (h1 : A0 * C1=A1 * (C0 - A0 * mass)) :
    A * C1=A1 * (C - A * (T + mass)):= by
  have h : A0 * (A * C1 - A1 * (C - A * (T + mass)))=0:= by
    have h1' := congr_arg (fun z => A * z) h1
    have h0' := congr_arg (fun z => A1 * z) h0
    dsimp -failIfUnchanged only at h1' h0'
    linarith
  rcases mul_eq_zero.mp h with hzero | hzero
  · omega
  · linarith
lemma shrink_bound (f : ℕ → ℤ) (C : ℤ) (n : ℕ)
    (h : ∀ i < n,3 * f (i + 1) ≤ f i + 2 * C) :
    (3 : ℤ) ^ n * f n ≤ f 0 + ((3 : ℤ) ^ n - 1) * C:= by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih':=ih (fun i hi => h i (by omega))
    have hstep:=h n (by omega)
    have hp : 0 < (3 : ℤ) ^ n:= by positivity
    have hpow : (3 : ℤ) ^ (n + 1)=3 * (3 : ℤ) ^ n:= by ring
    rw [hpow]
    nlinarith
lemma qcd (f : ℕ → ℤ) (gap : ℤ) (n : ℕ)
    (h : ∀ i < n,f (i + 1) < f i - gap) :
    f n ≤ f 0 - (n : ℤ) * (gap + 1):= by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih':=ih (fun i hi => h i (by omega))
    have hstep:=h n (by omega)
    push_cast
    linarith
lemma high_count (f : ℕ → ℤ) (A B V m : ℤ) (t q n : ℕ)
    (hA : 0 < A) (hB : 0 ≤ B) (hm : 0 < m) (hV : 0 ≤ V)
    (hpow : V ≤ (3 : ℤ) ^ t) (hq : B + 4 ≤ (q : ℤ) * m)
    (hstart : f 0 ≤ A * V) (hend : 0 < f n)
    (hshrink : ∀ i < n,3 * f (i + 1) ≤ f i + 2 * A * (B + 3))
    (hdrop : ∀ i < n,f (i + 1) < f i - A * m) :
    n < t + q:= by
  by_contra hge
  have hnt : t ≤ n:= by omega
  have ht:=shrink_bound f (A * (B + 3)) t (fun i hi => by
    have:=hshrink i (by omega); linarith)
  have hp : 0 < (3 : ℤ) ^ t:= by positivity
  have hmid : f t ≤ A * (B + 4):= by
    have hinit : f 0 ≤ A * (3 : ℤ) ^ t:= by nlinarith
    nlinarith
  have htail:=qcd (fun i => f (t + i)) (A * m) (n - t) (fun i hi => by
    have h1:=hdrop (t + i) (by omega)
    simpa [Nat.add_assoc] using! h1)
  have hsub : t + (n - t)=n:= by omega
  simp only [Nat.add_zero,hsub] at htail
  have hcount : (q : ℤ) ≤ ((n - t : ℕ) : ℤ):= by omega
  have hbound : A * (B + 4) ≤ A * ((q : ℤ) * m):= by nlinarith
  have hqm : (q : ℤ) * m ≤ ((n - t : ℕ) : ℤ) * m:= by nlinarith
  have hlast : A * ((q : ℤ) * m) ≤ A * (((n - t : ℕ) : ℤ) * m):= by nlinarith
  have hlast' : A * (((n - t : ℕ) : ℤ) * m)=((n - t : ℕ) : ℤ) * (A * m):= by ring
  linarith
end Block
namespace Table
def qbn (xs : List ℤ) : List ℕ:=xs.map Int.toNat
def F (k q : ℤ) : List ℕ:=Prefix.F k.toNat q.toNat
def G (k q : ℤ) : List ℕ:=Prefix.G k.toNat q.toNat
def run (e : ℕ) (xs ys : List ℤ) : Prop:=Prefix.Run e (qbn xs) (qbn ys)
def exec (e : ℕ) (xs ys : List ℤ) : Prop:=Prefix.Exec e (qbn xs) (qbn ys)
lemma pow_split {k d : ℤ} (hd : 0 ≤ d) (hdk : d ≤ k) :
    q0 k=q0 d * q0 (k - d):=qcl hd hdk
lemma pow_pos {k : ℤ} (hk : 0 ≤ k) : 0 < q0 k:=qc hk
lemma run_even {u v w : ℤ} (r : List ℤ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (heven : ZEven u) :
    run 1 (u :: v :: w :: r) ((u + v + w + 3) :: r):= by
  rcases heven with ⟨n,rfl⟩
  have hn : 0 ≤ n:= by omega
  unfold run qbn
  simp only [List.map_cons]
  have hstep:=Prefix.one (Prefix.Step.E n.toNat v.toNat w.toNat (qbn r))
  have h1 : (2 * n).toNat=2 * n.toNat:= by omega
  have h2 : (2 * n + v + w + 3).toNat=2 * n.toNat + v.toNat + w.toNat + 3:= by omega
  rwa [h1,h2]
lemma odd_lookup {u v w s q : ℤ} (r : List ℤ) {e : ℕ} {ys : List ℤ} {z : ℤ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (hodd : qW u)
    (hs : 1 ≤ s) (hq : 3 ≤ q) (hqo : qW q)
    (hH : u + 2 * v + 3=q0 s * q)
    (hr : Prefix.Run e (F s q) (qbn ys ++ [z.toNat]))
    (hzn : 0 ≤ z) (hz : 0 ≤ z + w - v - 1) :
    run (1 + e) (u :: v :: w :: r) ((ys ++ [z + w - v - 1]) ++ r):= by
  rcases hodd with ⟨n,rfl⟩
  rcases hqo with ⟨t,rfl⟩
  have hn0 : 0 ≤ n:= by omega
  have ht0 : 0 ≤ t - 1:= by omega
  have hhalf : n + v + 2=q0 (s - 1) * (3 + 2 * (t - 1)):= by
    have hsp:=pow_split (k:=s) (d:=1) (by omega) hs
    rw [pow2_one] at hsp
    rw [hsp] at hH
    linarith
  have hnat : n.toNat + v.toNat + 2=2 ^ (s - 1).toNat * (3 + 2 * (t - 1).toNat):= by
    rw [qe (by omega)] at hhalf
    have hcast : ((n.toNat + v.toNat + 2 : ℕ) : ℤ) =
        ((2 ^ (s - 1).toNat * (3 + 2 * (t - 1).toNat) : ℕ) : ℤ):= by
      push_cast
      rw [Int.toNat_of_nonneg hn0,Int.toNat_of_nonneg hv,Int.toNat_of_nonneg ht0]
      exact hhalf
    exact Int.ofNat_inj.mp hcast
  have hF : F s (2 * t + 1)=Prefix.F (1 + (s - 1).toNat) (3 + 2 * (t - 1).toNat):= by
    unfold F
    congr 1 <;> omega
  rw [hF] at hr
  have h:=Prefix.odd_lookup w.toNat (qbn r) hnat hr
  unfold run qbn
  simp only [List.map_append,List.map_cons,List.map_nil]
  have h1 : (2 * n + 1).toNat=2 * n.toNat + 1:= by omega
  have h2 : (z + w - v - 1).toNat=z.toNat + w.toNat - v.toNat - 1:= by omega
  rw [← h1,← h2] at h
  simpa only [List.append_assoc] using! h
structure pair where
  p : ℤ
  d : ℤ
  b : ℤ
  c : ℤ
  deriving DecidableEq,Repr
def ql (k : ℤ) (x : pair) : ℤ:=x.p * q0 (k - x.d)
def left (k q : ℤ) (x : pair) : ℤ:=ql k x * q + x.b
def right (k q : ℤ) (x : pair) : ℤ:=(q0 k - ql k x) * q + x.c
def qai (k q : ℤ) (x : pair) : List ℤ:=[left k q x,right k q x]
def h (x : pair) : ℤ:=x.b + 2 * x.c + 3
def qaB (k : ℤ) (x : pair) : Prop :=
  0 ≤ x.d ∧ x.d ≤ k ∧ 0 < x.p ∧ x.p < q0 x.d ∧ qW x.p ∧ 1 ≤ x.b ∧ -1 ≤ x.c
def qo (k : ℤ) (x : pair) : Prop :=
  qaB k x ∧ 2 * x.p ≤ q0 x.d ∧ 0 ≤ x.c
lemma qac {k : ℤ} {x : pair} (hx : qaB k x) :
    0 < ql k x ∧ ql k x < q0 k:= by
  rcases hx with ⟨hd0,hdk,hp0,hpd,_,_,_⟩
  unfold ql
  rw [pow_split hd0 hdk]
  have hp : 0 < q0 (k - x.d):=pow_pos (by omega)
  exact ⟨by nlinarith,by nlinarith⟩
lemma qn {k q : ℤ} {x : pair} (hx : qaB k x) (hq : 1 ≤ q) :
    1 ≤ left k q x ∧ 0 ≤ right k q x:= by
  have hc:=qac hx
  rcases hx with ⟨_,_,_,_,_,hb,hc0⟩
  unfold left right
  exact ⟨by nlinarith,by nlinarith⟩
def qa (k : ℤ) (x : pair) (s r : ℤ) : Prop :=
  1 ≤ s ∧ s < k - x.d ∧ h x=q0 s * r ∧ qW r
def qg (k q : ℤ) (x : pair) (s r : ℤ) : ℤ :=
  (q0 (x.d + 1) - x.p) * q0 (k - x.d - s) * q + r
lemma qz {k q : ℤ} {x : pair} {s r : ℤ}
    (hx : qaB k x) (hq : 1 ≤ q) (hqo : qW q) (hs : qa k x s r) :
    3 ≤ qg k q x s r ∧ qW (qg k q x s r) ∧
    left k q x + 2 * right k q x + 3=q0 s * qg k q x s r:= by
  rcases hx with ⟨hd0,hdk,hp0,hpd,hpo,hb,hc⟩
  rcases hs with ⟨hs1,hsk,hh,hr⟩
  have hsp : 0 < q0 s:=pow_pos (by omega)
  have h_pos : 2 ≤ h x:= by unfold h; omega
  have hr0 : 1 ≤ r:= by nlinarith
  have hpos : 0 < q0 (k - x.d - s - 1):=pow_pos (by omega)
  have hE : q0 (k - x.d - s)=2 * q0 (k - x.d - s - 1):= by
    have:=pow_split (k:=k - x.d - s) (d:=1) (by omega) (by omega)
    simpa [pow2_one] using! this
  have hD : q0 (x.d + 1)=2 * q0 x.d:= by
    rw [q5 hd0 (by omega),pow2_one]; ring
  unfold qg
  have hq1 : 1 ≤ 2 * q0 x.d - x.p:= by omega
  have hq2 : 2 ≤ 2 * q0 (k - x.d - s - 1):= by omega
  have hq3 : 2 ≤ (2 * q0 x.d - x.p) * (2 * q0 (k - x.d - s - 1)):= by nlinarith
  have hq4 : 2 ≤ (2 * q0 x.d - x.p) * (2 * q0 (k - x.d - s - 1)) * q:= by nlinarith
  refine ⟨by rw [hE,hD]; linarith,?_,?_⟩
  · rcases hr with ⟨v,rfl⟩
    refine ⟨(q0 (x.d + 1) - x.p) * q0 (k - x.d - s - 1) * q + v,?_⟩
    rw [hE]; ring
  · unfold left right ql
    have h1:=pow_split hd0 hdk
    have h2:=pow_split (k:=k - x.d) (d:=s) (by omega) (by omega)
    unfold h at hh
    rw [h1,h2,hD]
    nlinarith
lemma qu (k q : ℤ) (x : pair) :
    left k q x + right k q x=q0 k * q + x.b + x.c:= by
  unfold left right; ring
lemma left_odd {k q : ℤ} {x : pair} (hx : qaB k x) (hd : x.d < k) (hb : qW x.b) :
    qW (left k q x):= by
  rcases hb with ⟨t,hb⟩
  unfold left ql
  refine ⟨x.p * q0 (k - x.d - 1) * q + t,?_⟩
  have h1:=pow_split (k:=k - x.d) (d:=1) (by omega) (by omega)
  rw [pow2_one] at h1
  rw [h1,hb]; ring
def delta (s r : ℤ) (y : pair) : ℤ:=y.p * q0 (s - y.d) * r
def qQ (x : pair) (s r : ℤ) (y : pair) : pair :=
  ⟨y.p * (q0 (x.d + 1) - x.p),
   x.d + y.d,
   delta s r y + y.b,
   h x - delta s r y + y.c - x.c - 1⟩
def qbu (x : pair) : pair:=⟨x.p,x.d + 1,x.b,x.c⟩
lemma qI (x : pair) (s r : ℤ) (y : pair) :
    (qQ x s r y).b + (qQ x s r y).c=x.b + x.c + y.b + y.c + 2:= by
  unfold qQ h; dsimp -failIfUnchanged; ring
lemma qbU {k : ℤ} {x : pair} {s r : ℤ} {y : pair}
    (hs : qa k x s r) (hy : qo s y) :
    q0 y.d * delta s r y=y.p * h x:= by
  rcases hs with ⟨_,_,hh,_⟩
  rcases hy with ⟨⟨hyd0,hyds,_⟩,_⟩
  unfold delta
  rw [hh,pow_split hyd0 hyds]
  ring
lemma qan {k : ℤ} {x : pair} {s r : ℤ} {y : pair}
    (hx : qaB k x) (hs : qa k x s r) (hy : qo s y) :
    qaB k (qQ x s r y) ∧ 1 ≤ (qQ x s r y).c:= by
  have he:=qbU hs hy
  rcases hx with ⟨hdx0,hdxk,hpx0,hpxd,hox,hbx,hcx⟩
  rcases hs with ⟨hs1,hsk,hh,hr⟩
  rcases hy with ⟨⟨hdy0,hdys,hpy0,hpyd,hoy,hby,hcy⟩,hhalf,hcy0⟩
  have hD : q0 (x.d + 1)=2 * q0 x.d:= by
    rw [q5 hdx0 (by omega),pow2_one]; ring
  have hDs : q0 (x.d + y.d)=q0 x.d * q0 y.d:=q5 hdx0 hdy0
  have hxpos : 0 < q0 x.d:=pow_pos hdx0
  have hypos : 0 < q0 y.d:=pow_pos hdy0
  have h_pos : 2 ≤ h x:= by unfold h; omega
  have hsp : 0 < q0 s:=pow_pos (by omega)
  have hr0 : 1 ≤ r:= by nlinarith
  have hds_pos : 0 < q0 (s - y.d):=pow_pos (by omega)
  have hz_pos : 0 < delta s r y:= by unfold delta; positivity
  have hnewc : 1 ≤ (qQ x s r y).c:= by
    unfold qQ h at *
    dsimp -failIfUnchanged
    have h1 : 0 ≤ (q0 y.d - y.p) * (x.b - 1):= by nlinarith
    have h2 : 0 ≤ (q0 y.d - 2 * y.p) * (x.c + 2):= by nlinarith
    nlinarith
  refine ⟨?_,hnewc⟩
  unfold qaB qQ
  dsimp -failIfUnchanged
  change 1 ≤ h x - delta s r y + y.c - x.c - 1 at hnewc
  refine ⟨by omega,by omega,by rw [hD]; nlinarith,by rw [hD,hDs]; nlinarith,?_,by linarith,by omega⟩
  rcases hox with ⟨a,ha⟩
  rcases hoy with ⟨v,hv⟩
  refine ⟨(2 * v + 1) * (q0 x.d - a) - v - 1,?_⟩
  rw [hD,ha,hv]; ring
lemma widen_table {k : ℤ} {x : pair} (hx : qaB k x) (hc : 0 ≤ x.c) :
    qo (k + 1) (qbu x):= by
  rcases hx with ⟨hd0,hdk,hp0,hpd,ho,hb,hc0⟩
  unfold qo qaB qbu
  dsimp -failIfUnchanged
  have hD : q0 (x.d + 1)=2 * q0 x.d:= by
    rw [q5 hd0 (by omega),pow2_one]; ring
  refine ⟨⟨by omega,by omega,hp0,by rw [hD]; omega,ho,hb,hc0⟩,by rw [hD]; omega,hc⟩
lemma widen_values {k : ℤ} (q : ℤ) (x : pair) (hk : 0 ≤ k) :
    qai (k + 1) q (qbu x)=[left k q x,right k q x + q0 k * q]:= by
  unfold qai qbu left right ql
  dsimp -failIfUnchanged
  have hsub : k + 1 - (x.d + 1)=k - x.d:= by omega
  have hD : q0 (k + 1)=2 * q0 k:= by
    rw [q5 hk (by omega),pow2_one]; ring
  rw [hsub,hD]
  congr 1; congr 1; ring
lemma qaF {k : ℤ} (q : ℤ) {x : pair} {s r : ℤ} {y : pair}
    (hx : qaB k x) (hs : qa k x s r) (hy : qo s y) :
    left s (qg k q x s r) y=left k q (qQ x s r y):= by
  rcases hx with ⟨hdx0,hdxk,_⟩
  rcases hs with ⟨hs1,hsk,_⟩
  rcases hy with ⟨⟨hdy0,hdys,_⟩,_⟩
  unfold left ql qg qQ delta
  dsimp -failIfUnchanged
  have hP : q0 (s - y.d) * q0 (k - x.d - s)=q0 (k - (x.d + y.d)):= by
    rw [← q5 (by omega) (by omega)]
    congr 1; omega
  have hP' := congr_arg (fun z => y.p * (q0 (x.d + 1) - x.p) * q * z) hP
  dsimp -failIfUnchanged only at hP'
  linarith
lemma next_right {k q : ℤ} {x : pair} {s r : ℤ} {y : pair}
    (hx : qaB k x) (hq : 1 ≤ q) (ho : qW q)
    (hs : qa k x s r) (hy : qo s y) :
    right s (qg k q x s r) y - right k q x - 1=right k q (qQ x s r y):= by
  have hQ:=(qz hx hq ho hs).2.2
  have hL:=qaF q hx hs hy
  have hS0:=qu k q x
  have hS1:=qu s (qg k q x s r) y
  have hS2:=qu k q (qQ x s r y)
  have hC:=qI x s r y
  linarith
def qk (k : ℤ) (x : pair) : ℤ :=
  if x.d < k then x.b else x.p + x.b
def q3 (k : ℤ) (x : pair) : Bool :=
  qb6 (qk k x)
lemma qbS {k q : ℤ} {x : pair} (hx : qaB k x) (hq : qW q) :
    ∃ a,left k q x=qk k x + 2 * a:= by
  rcases hq with ⟨t,rfl⟩
  unfold qk
  split_ifs with hdk
  · refine ⟨x.p * q0 (k - x.d - 1) * (2 * t + 1),?_⟩
    unfold left ql
    have h1:=pow_split (k:=k - x.d) (d:=1) (by omega) (by omega)
    rw [pow2_one] at h1
    rw [h1]; ring
  · have hd : x.d=k:= by rcases hx with ⟨_,hdk',_⟩; omega
    refine ⟨x.p * t,?_⟩
    unfold left ql
    rw [hd,sub_self,pow2_zero]; ring
lemma qaO {k q : ℤ} {x : pair}
    (hx : qaB k x) (hq : qW q) (he : q3 k x=true) :
    ZEven (left k q x):= by
  rcases qbS hx hq with ⟨a,ha⟩
  rcases (qah _).mp he with ⟨v,hv⟩
  exact ⟨v + a,by linarith⟩
lemma qb0 {k : ℤ} {x : pair} {s r : ℤ}
    (hs : qa k x s r) (he : q3 k x=false) :
    qW x.b:= by
  rcases hs with ⟨hs1,hsk,_⟩
  unfold q3 qk at he
  have hdk : x.d < k:= by omega
  rw [if_pos hdk] at he
  exact (qa9 x.b).mp he
inductive entry where
  | One (const_val count : ℤ)
  | Two (state : pair) (count : ℤ)
  deriving DecidableEq,Repr
def qad : entry → ℤ
  | .One _ e => e
  | .Two _ e => e
def eval (k q : ℤ) : entry → List ℤ
  | .One v _ => [q0 k * q + v]
  | .Two x _ => qai k q x
def qU (k : ℤ) (f : entry) : Prop :=
  0 ≤ k ∧ 0 ≤ qad f ∧
  match f with
  | .One v e => v=1 + 3 * e
  | .Two x e => qo k x ∧ x.b + x.c=1 + 3 * e
def realizes (k : ℤ) (f : entry) : Prop :=
  ∀ q,1 ≤ q → qW q → Prefix.Run (qad f).toNat (F k q) (qbn (eval k q f))
def qZ (k : ℤ) (f : entry) : Prop :=
  qU k f ∧ realizes k f
lemma qcp {k q : ℤ} {x : pair} {s r : ℤ} {y : pair} {e w : ℤ}
    (hx : qaB k x) (hq : 1 ≤ q) (ho : qW q)
    (hs : qa k x s r) (he : q3 k x=false)
    (hval : qZ s (.Two y e)) (hw : 0 ≤ w) :
    run (1 + e.toNat)
      [left k q x,right k q x,w]
      [left k q (qQ x s r y),right k q (qQ x s r y) + w]:= by
  rcases hval with ⟨⟨hs0,he0,hy,hmass⟩,hreal⟩
  rcases qz hx hq ho hs with ⟨hQ,hQo,hH⟩
  rcases qn hx hq with ⟨hu,hv⟩
  rcases qan hx hs hy with ⟨hnext,hc⟩
  rcases qn hnext hq with ⟨hu',hv'⟩
  rcases qn hy.1 (by omega : 1 ≤ qg k q x s r) with ⟨hU,hV⟩
  have hreal':=hreal (qg k q x s r) (by omega) hQo
  change Prefix.Run e.toNat (F s (qg k q x s r))
    (qbn [left s (qg k q x s r) y] ++ [(right s (qg k q x s r) y).toNat]) at hreal'
  have hR:=next_right hx hq ho hs hy
  have hdk : x.d < k:= by rcases hs with ⟨_,hsk,_⟩; omega
  have hrun:=odd_lookup [] (by omega : 0 ≤ left k q x) hv hw
    (left_odd hx hdk (qb0 hs he)) (by rcases hs with ⟨hs1,_⟩; omega)
    hQ hQo hH hreal' hV (by omega)
  rw [qaF q hx hs hy] at hrun
  have heq : right s (qg k q x s r) y + w - right k q x - 1 =
      right k q (qQ x s r y) + w:= by linarith
  rwa [heq] at hrun
lemma qcq {k q : ℤ} {x : pair} {s r v e w : ℤ}
    (hx : qaB k x) (hq : 1 ≤ q) (ho : qW q)
    (hs : qa k x s r) (he : q3 k x=false)
    (hval : qZ s (.One v e)) (hw : 0 ≤ w) :
    run (1 + e.toNat) [left k q x,right k q x,w]
      [q0 k * q + x.b + x.c + v + 2 + w]:= by
  rcases hval with ⟨⟨hs0,he0,hv_eq⟩,hreal⟩
  change 0 ≤ e at he0
  change v=1 + 3 * e at hv_eq
  rcases qz hx hq ho hs with ⟨hQ,hQo,hH⟩
  rcases qn hx hq with ⟨hu,hright⟩
  have hsum:=qu k q x
  have hreal':=hreal (qg k q x s r) (by omega) hQo
  change Prefix.Run e.toNat (F s (qg k q x s r))
    (qbn [] ++ [(q0 s * qg k q x s r + v).toNat]) at hreal'
  have hdk : x.d < k:= by rcases hs with ⟨_,hsk,_⟩; omega
  have hsp : 0 < q0 s:=pow_pos hs0
  have hrun:=odd_lookup [] (by omega : 0 ≤ left k q x) hright hw
    (left_odd hx hdk (qb0 hs he)) (by rcases hs with ⟨hs1,_⟩; omega)
    hQ hQo hH hreal' (by nlinarith) (by linarith)
  have heq : q0 s * qg k q x s r + v + w - right k q x - 1 =
      q0 k * q + x.b + x.c + v + 2 + w:= by linarith
  simpa [heq] using! hrun
lemma snoc {k q : ℤ} (hk : 0 ≤ k) (hq : 0 ≤ q) :
    F (k + 1) q=F k q ++ qbn [q0 k * q]:= by
  unfold F qbn
  have h1 : (k + 1).toNat=1 + k.toNat:= by omega
  rw [h1,Prefix.F_snoc]
  simp only [List.map_cons,List.map_nil]
  rw [qe hk]
  have h2 : ((2 : ℤ) ^ k.toNat * q).toNat=2 ^ k.toNat * q.toNat:= by
    have hcast : (((2 ^ k.toNat * q.toNat : ℕ) : ℤ)).toNat=2 ^ k.toNat * q.toNat :=
      Int.toNat_natCast _
    have heq : ((2 ^ k.toNat * q.toNat : ℕ) : ℤ)=(2 : ℤ) ^ k.toNat * q:= by
      push_cast
      rw [Int.toNat_of_nonneg hq]
    rwa [heq] at hcast
  rw [h2]
lemma qP {k : ℤ} {f : entry} {q : ℤ}
    (hr : realizes k f) (hk : 0 ≤ k) (hq : 1 ≤ q) (ho : qW q) :
    Prefix.Run (qad f).toNat (F (k + 1) q) (qbn (eval k q f ++ [q0 k * q])):= by
  rw [snoc hk (by omega)]
  unfold qbn
  rw [List.map_append]
  exact Prefix.app _ (hr q hq ho)
lemma valid_root : qZ 0 (.One 1 0):= by
  unfold qZ qU qad
  dsimp -failIfUnchanged
  refine ⟨⟨by omega,by omega,rfl⟩,?_⟩
  intro q hq ho
  unfold F Prefix.F eval qad qbn
  simp only [Int.toNat_zero,Prefix.geometric,List.map_cons,List.map_nil,pow2_zero,one_mul]
  have h1 : q.toNat + 1=(q + 1).toNat:= by omega
  rw [h1]
  exact Prefix.Run.refl _
lemma valid_add_one {k v e : ℤ} (h : qZ k (.One v e)) :
    qZ (k + 1) (.Two ⟨1,1,v,0⟩ e):= by
  rcases h with ⟨⟨hk,he,hv⟩,hreal⟩
  change 0 ≤ e at he
  change v=1 + 3 * e at hv
  unfold qZ qU qad qo qaB
  dsimp -failIfUnchanged
  refine ⟨⟨by omega,he,⟨⟨by omega,by omega,by omega,by simp [q0],⟨0,rfl⟩,by omega,by omega⟩,
    by simp [q0],by omega⟩,by omega⟩,?_⟩
  intro q hq ho
  have h:=qP hreal hk hq ho
  change Prefix.Run e.toNat (F (k + 1) q) (qbn [q0 k * q + v,q0 k * q]) at h
  change Prefix.Run e.toNat (F (k + 1) q) (qbn (qai (k + 1) q ⟨1,1,v,0⟩))
  have heq : qai (k + 1) q ⟨1,1,v,0⟩=[q0 k * q + v,q0 k * q]:= by
    unfold qai left right ql
    dsimp -failIfUnchanged
    have hsub : k + 1 - 1=k:= by omega
    have hD : q0 (k + 1)=2 * q0 k:= by
      rw [q5 hk (by omega),pow2_one]; ring
    rw [hsub,hD]
    congr 1; · ring
    congr 1; ring
  rwa [heq]
lemma qc1 {k : ℤ} {x : pair} {e : ℤ}
    (h : qZ k (.Two x e)) (heven : q3 k x=true) :
    qZ (k + 1) (.One (x.b + x.c + 3) (e + 1)):= by
  rcases h with ⟨⟨hk,he,hx,hmass⟩,hreal⟩
  change 0 ≤ e at he
  unfold qZ qU qad
  dsimp -failIfUnchanged
  refine ⟨⟨by omega,by omega,by omega⟩,?_⟩
  intro q hq ho
  have h1:=qP hreal hk hq ho
  rcases qn hx.1 hq with ⟨hu,hv⟩
  have hP:=pow_pos hk
  have hr:=run_even (w:=q0 k * q) [] (by omega) hv (by nlinarith) (qaO hx.1 ho heven)
  have hrun:=Prefix.trans h1 hr
  unfold eval qad
  dsimp -failIfUnchanged
  have hadd : (e + 1).toNat=e.toNat + 1:= by omega
  rw [hadd]
  have heq : q0 (k + 1) * q + (x.b + x.c + 3) =
      left k q x + right k q x + q0 k * q + 3:= by
    have hsum:=qu k q x
    have hD : q0 (k + 1)=2 * q0 k:= by
      rw [q5 hk (by omega),pow2_one]; ring
    rw [hD]; linarith
  rwa [heq]
lemma qaM {k : ℤ} {x : pair} {e s r v f : ℤ}
    (h : qZ k (.Two x e)) (hs : qa k x s r)
    (ho : q3 k x=false) (hsmall : qZ s (.One v f)) :
    qZ (k + 1) (.One (x.b + x.c + v + 2) (e + 1 + f)):= by
  rcases h with ⟨⟨hk,he,hx,hmass⟩,hreal⟩
  rcases hsmall.1 with ⟨hs0,hf,hv⟩
  change 0 ≤ e at he
  change 0 ≤ f at hf
  change v=1 + 3 * f at hv
  unfold qZ qU qad
  dsimp -failIfUnchanged
  refine ⟨⟨by omega,by omega,by omega⟩,?_⟩
  intro q hq hqo
  have h1:=qP hreal hk hq hqo
  have hP:=pow_pos hk
  have hr:=qcq hx.1 hq hqo hs ho hsmall (w:=q0 k * q) (by nlinarith)
  have hrun:=Prefix.trans h1 hr
  unfold eval qad
  dsimp -failIfUnchanged
  have hadd : (e + 1 + f).toNat=e.toNat + (1 + f.toNat):= by omega
  rw [hadd]
  have heq : q0 (k + 1) * q + (x.b + x.c + v + 2) =
      q0 k * q + x.b + x.c + v + 2 + q0 k * q:= by
    have hD : q0 (k + 1)=2 * q0 k:= by
      rw [q5 hk (by omega),pow2_one]; ring
    rw [hD]; ring
  rwa [heq]
lemma qaL {k : ℤ} {x : pair} {e s r : ℤ} {y : pair} {f : ℤ}
    (h : qZ k (.Two x e)) (hs : qa k x s r)
    (ho : q3 k x=false) (hsmall : qZ s (.Two y f)) :
    qZ (k + 1) (.Two (qbu (qQ x s r y)) (e + 1 + f)):= by
  rcases h with ⟨⟨hk,he,hx,hmass⟩,hreal⟩
  rcases hsmall.1 with ⟨hs0,hf,hy,hmass'⟩
  change 0 ≤ e at he
  change 0 ≤ f at hf
  rcases qan hx.1 hs hy with ⟨hnext,hc⟩
  unfold qZ qU qad
  dsimp -failIfUnchanged
  refine ⟨⟨by omega,by omega,widen_table hnext (by omega),?_⟩,?_⟩
  · change (qQ x s r y).b + (qQ x s r y).c=1 + 3 * (e + 1 + f)
    have hnm:=qI x s r y
    linarith
  · intro q hq hqo
    have h1:=qP hreal hk hq hqo
    have hP:=pow_pos hk
    have hr:=qcp hx.1 hq hqo hs ho hsmall (w:=q0 k * q) (by nlinarith)
    have hrun:=Prefix.trans h1 hr
    unfold eval qad
    dsimp -failIfUnchanged
    rw [widen_values q _ hk]
    have hadd : (e + 1 + f).toNat=e.toNat + (1 + f.toNat):= by omega
    rwa [hadd]
inductive Built : ℤ → entry → Prop where
  | built_root : Built 0 (.One 1 0)
  | built_one {k v e : ℤ} : Built k (.One v e) → Built (k + 1) (.Two ⟨1,1,v,0⟩ e)
  | built_even {k : ℤ} {x : pair} {e : ℤ} :
      Built k (.Two x e) → q3 k x=true → Built (k + 1) (.One (x.b + x.c + 3) (e + 1))
  | built_lookup_one {k : ℤ} {x : pair} {e s r v f : ℤ} :
      Built k (.Two x e) → qa k x s r → q3 k x=false →
      Built s (.One v f) → Built (k + 1) (.One (x.b + x.c + v + 2) (e + 1 + f))
  | built_lookup_two {k : ℤ} {x : pair} {e s r : ℤ} {y : pair} {f : ℤ} :
      Built k (.Two x e) → qa k x s r → q3 k x=false →
      Built s (.Two y f) → Built (k + 1) (.Two (qbu (qQ x s r y)) (e + 1 + f))
theorem built_valid {k : ℤ} {f : entry} (h : Built k f) : qZ k f:= by
  induction h with
  | built_root => exact valid_root
  | built_one _ ih => exact valid_add_one ih
  | built_even _ he ih => exact qc1 ih he
  | built_lookup_one _ hs ho _ ih1 ih2 => exact qaM ih1 hs ho ih2
  | built_lookup_two _ hs ho _ ih1 ih2 => exact qaL ih1 hs ho ih2
inductive Boundary (lib : ℤ → entry → Prop) (k : ℤ) : pair → ℤ → ℕ → Prop where
  | boundary_even (x : pair) : q3 k x=true → Boundary lib k x 1 1
  | boundary_one (x : pair) (s r v e : ℤ) :
      qa k x s r → q3 k x=false → lib s (.One v e) →
      Boundary lib k x (1 + e) 1
  | boundary_two (x : pair) (s r : ℤ) (y : pair) (e f : ℤ) (n : ℕ) :
      qa k x s r → q3 k x=false → lib s (.Two y e) →
      Boundary lib k (qQ x s r y) f n → Boundary lib k x (1 + e + f) (1 + n)
lemma qcm {k : ℤ} {x : pair} (hx : qaB k x) : 1 ≤ x.d:= by
  rcases hx with ⟨hd0,_,hp0,hpd,_⟩
  by_contra hlt
  have hd : x.d=0:= by omega
  rw [hd,pow2_zero] at hpd
  omega
lemma run_zero {e : ℕ} {xs ys : List ℤ} (h : run e (xs ++ [0]) ys) : exec e xs ys:= by
  unfold run exec qbn at *
  rw [List.map_append] at h
  exact Prefix.Exec.zero (Prefix.run_exec h)
lemma qb5 {lib : ℤ → entry → Prop} {k : ℤ} {x : pair} {e : ℤ} {n : ℕ}
    (hlib : ∀ s f,lib s f → qZ s f)
    (hb : Boundary lib k x e n) (hx : qaB k x) :
    0 ≤ e ∧ (n : ℤ) + x.d ≤ k + 1 ∧
    ∀ q,1 ≤ q → qW q → exec e.toNat (qai k q x) [q0 k * q + x.b + x.c + 3 * e]:= by
  induction hb with
  | boundary_even x he =>
    refine ⟨by omega,by rcases hx with ⟨_,hdk,_⟩; omega,?_⟩
    intro q hq hqo
    rcases qn hx hq with ⟨hu,hv⟩
    have hr:=run_even [] (by omega) hv (by omega : 0 ≤ (0 : ℤ)) (qaO hx hqo he)
    apply run_zero
    unfold qai
    have heq : q0 k * q + x.b + x.c + 3 * 1=left k q x + right k q x + 0 + 3:= by
      have:=qu k q x; linarith
    rw [heq]
    exact hr
  | boundary_one x s r v e hs ho hsmall =>
    have hval:=hlib s (.One v e) hsmall
    rcases hval.1 with ⟨hs0,he0,hv⟩
    change 0 ≤ e at he0
    change v=1 + 3 * e at hv
    refine ⟨by omega,by rcases hx with ⟨_,hdk,_⟩; omega,?_⟩
    intro q hq hqo
    have hr:=qcq hx hq hqo hs ho hval (w:=0) (by omega)
    have heq : q0 k * q + x.b + x.c + 3 * (1 + e)=q0 k * q + x.b + x.c + v + 2 + 0:= by
      linarith
    have hadd : (1 + e).toNat=1 + e.toNat:= by omega
    rw [heq,hadd]
    exact run_zero hr
  | boundary_two x s r y e f n hs ho hsmall htail ih =>
    have hval:=hlib s (.Two y e) hsmall
    rcases hval.1 with ⟨hs0,he0,hy,hmass⟩
    change 0 ≤ e at he0
    rcases qan hx hs hy with ⟨hnext,hc⟩
    rcases ih hnext with ⟨hf,hdepth,hexec⟩
    have hyd : 1 ≤ y.d:=qcm hy.1
    refine ⟨by omega,?_,?_⟩
    · change (n : ℤ) + (x.d + y.d) ≤ k + 1 at hdepth
      push_cast; omega
    · intro q hq hqo
      have hr:=qcp hx hq hqo hs ho hval (w:=0) (by omega)
      rw [add_zero] at hr
      have hr0:=run_zero (xs:=qai k q x) hr
      have hrun:=Prefix.exec_trans hr0 (hexec q hq hqo)
      unfold exec at *
      have hadd : (1 + e + f).toNat=1 + e.toNat + f.toNat:= by omega
      have heq : q0 k * q + x.b + x.c + 3 * (1 + e + f) =
          q0 k * q + (qQ x s r y).b + (qQ x s r y).c + 3 * f:= by
        have:=qI x s r y; linarith
      rw [hadd,heq]
      exact hrun
def qba (x : pair) : pair:=⟨x.p,x.d,x.b,x.c - 1⟩
lemma qb9 {k : ℤ} {x : pair} (hx : qo k x) : qaB k (qba x):= by
  rcases hx with ⟨⟨hd0,hdk,hp0,hpd,ho,hb,hc⟩,hhalf,hc0⟩
  exact ⟨hd0,hdk,hp0,hpd,ho,hb,by unfold qba; dsimp -failIfUnchanged; omega⟩
lemma lower_values (k q : ℤ) (x : pair) :
    qai k q (qba x)=[left k q x,right k q x - 1]:= by
  unfold qai qba left right ql
  dsimp -failIfUnchanged; congr 1; congr 1; ring
lemma qcs {e : ℕ} {k q : ℤ} (ys : List ℤ) {z : ℤ}
    (hk : 1 ≤ k) (hq : 1 ≤ q) (hz : 1 ≤ z)
    (h : Prefix.Run e (F k q) (qbn (ys ++ [z]))) :
    Prefix.Run e (G k q) (qbn (ys ++ [z - 1])):= by
  unfold F G qbn at *
  rw [List.map_append] at *
  simp only [List.map_cons,List.map_nil] at *
  have hk1 : k.toNat=1 + (k - 1).toNat:= by omega
  have hz1 : z.toNat=1 + (z - 1).toNat:= by omega
  rw [hk1,hz1] at h
  have hres:=Prefix.F_to_G (k:=(k - 1).toNat) (q:=q.toNat) (by omega) h
  rw [hk1]
  exact hres
lemma G_single {k v e : ℤ} (h : qZ k (.One v e)) (hk1 : 1 ≤ k) :
    ∀ q,1 ≤ q → qW q → Prefix.Run e.toNat (G k q) (qbn [q0 k * q + v - 1]):= by
  rcases h with ⟨⟨hk,he,hv⟩,hr⟩
  change 0 ≤ e at he
  change v=1 + 3 * e at hv
  have hP:=pow_pos hk
  intro q hq ho
  exact qcs [] hk1 hq (by nlinarith) (hr q hq ho)
lemma G_pair {k : ℤ} {x : pair} {e : ℤ} (h : qZ k (.Two x e)) (hk1 : 1 ≤ k) :
    ∀ q,1 ≤ q → qW q → Prefix.Run e.toNat (G k q) (qbn (qai k q (qba x))):= by
  rcases h with ⟨⟨hk,he,hx,hmass⟩,hr⟩
  intro q hq ho
  rw [lower_values]
  have hcoeff:=qac hx.1
  have hright : 1 ≤ right k q x:= by
    unfold right
    rcases hx with ⟨_,_,hc0⟩
    nlinarith
  exact qcs [left k q x] hk1 hq hright (hr q hq ho)
def qaf (lib : ℤ → entry → Prop) (k : ℤ) (f : entry) : Prop :=
  match f with
  | .One _ _ => True
  | .Two x _ => ∃ e n,Boundary lib k (qba x) e n
lemma G_returns {lib : ℤ → entry → Prop} {k : ℤ} {f : entry}
    (hlib : ∀ s g,lib s g → qZ s g)
    (hvalid : qZ k f) (hr : qaf lib k f) (hk : 1 ≤ k) :
    ∀ q,1 ≤ q → qW q → ∃ e m,Prefix.Exec e (G k q) [m]:= by
  intro q hq ho
  cases f with
  | One v e =>
    exact ⟨e.toNat,(q0 k * q + v - 1).toNat,Prefix.run_exec (G_single hvalid hk q hq ho)⟩
  | Two x e =>
    rcases hr with ⟨f,n,hb⟩
    rcases qb5 hlib hb (qb9 hvalid.1.2.2.1) with ⟨hf,hn,hexec⟩
    exact ⟨e.toNat + f.toNat,(q0 k * q + (qba x).b + (qba x).c + 3 * f).toNat,
      Prefix.exec_trans (Prefix.run_exec (G_pair hvalid hk q hq ho)) (hexec q hq ho)⟩
end Table
namespace UniqueTable
open Table
lemma qaR {s r t u : ℤ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hr : qW r) (hu : qW u)
    (he : q0 s * r=q0 t * u) : s=t ∧ r=u:= by
  have hlt : ∀ a b x y,0 ≤ a → a < b → qW x → q0 a * x=q0 b * y → False:= by
    intro a b x y ha hab ⟨z,hz⟩ heq
    have hsp:=pow_split (k:=b) (d:=a) ha (by omega)
    have hba:=pow_split (k:=b - a) (d:=1) (by omega) (by omega)
    rw [pow2_one] at hba
    have hp:=pow_pos ha
    have hmul : q0 a * x=q0 a * (2 * (q0 (b - a - 1) * y)):= by
      calc q0 a * x=q0 b * y:=heq
        _ = q0 a * q0 (b - a) * y:= by rw [hsp]
        _ = q0 a * (2 * q0 (b - a - 1)) * y:= by rw [hba]
        _ = q0 a * (2 * (q0 (b - a - 1) * y)):= by ring
    have hx : x=2 * (q0 (b - a - 1) * y):=mul_left_cancel₀ (by omega) hmul
    omega
  have hst : s=t:= by
    rcases lt_trichotomy s t with h | h | h
    · exfalso; exact hlt s t r u hs h hr he
    · exact h
    · exfalso; exact hlt t s u r ht h hu he.symm
  subst hst
  have hp:=pow_pos hs
  exact ⟨rfl,mul_left_cancel₀ (by omega) he⟩
lemma qK {k : ℤ} {x : pair} {s r t u : ℤ}
    (h1 : qa k x s r) (h2 : qa k x t u) : s=t ∧ r=u:= by
  rcases h1 with ⟨hs1,_,he1,hr⟩
  rcases h2 with ⟨ht1,_,he2,hu⟩
  exact qaR (by omega) (by omega) hr hu (by linarith)
lemma built_nonnegative {k : ℤ} {f : entry} (h : Built k f) : 0 ≤ k :=
  (built_valid h).1.1
theorem qbC {k1 : ℤ} {f : entry} (h : Built k1 f) :
    ∀ k2 g,k1=k2 → Built k2 g → f=g:= by
  induction h with
  | built_root =>
    intro k2 g hk hg
    cases hg with
    | built_root => rfl
    | @built_one k2' _ _ hb => have:=built_nonnegative hb; omega
    | @built_even k2' _ _ hb _ => have:=built_nonnegative hb; omega
    | @built_lookup_one k2' _ _ _ _ _ _ hb _ _ _ => have:=built_nonnegative hb; omega
    | @built_lookup_two k2' _ _ _ _ _ _ hb _ _ _ => have:=built_nonnegative hb; omega
  | @built_one k1 v1 e1 hb ih =>
    intro k2 g hk hg
    cases hg with
    | built_root => have:=built_nonnegative hb; omega
    | @built_one k2' v2 e2 hb2 =>
      have heq:=ih k2' _ (by omega) hb2
      injection heq with h1 h2
      subst h1 h2; rfl
    | @built_even k2' _ _ hb2 _ =>
      have heq:=ih k2' _ (by omega) hb2
      contradiction
    | @built_lookup_one k2' _ _ _ _ _ _ hb2 _ _ _ =>
      have heq:=ih k2' _ (by omega) hb2
      contradiction
    | @built_lookup_two k2' _ _ _ _ _ _ hb2 _ _ _ =>
      have heq:=ih k2' _ (by omega) hb2
      contradiction
  | @built_even k1 x1 e1 hb heven ih =>
    intro k2 g hk hg
    cases hg with
    | built_root => have:=built_nonnegative hb; omega
    | @built_one k2' _ _ hb2 =>
      have heq:=ih k2' _ (by omega) hb2
      contradiction
    | @built_even k2' x2 e2 hb2 heven2 =>
      have heq:=ih k2' _ (by omega) hb2
      injection heq with h1 h2
      subst h1 h2; rfl
    | @built_lookup_one k2' x2 e2 _ _ _ _ hb2 _ hodd2 _ =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ih k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rw [heven] at hodd2; contradiction
    | @built_lookup_two k2' x2 e2 _ _ _ _ hb2 _ hodd2 _ =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ih k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rw [heven] at hodd2; contradiction
  | @built_lookup_one k1 x1 e1 s1 r1 v1 f1 hb hsep hodd hsmall ihprev ihsmall =>
    intro k2 g hk hg
    cases hg with
    | built_root => have:=built_nonnegative hb; omega
    | @built_one k2' _ _ hb2 =>
      have heq:=ihprev k2' _ (by omega) hb2
      contradiction
    | @built_even k2' x2 e2 hb2 heven2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rw [hodd] at heven2; contradiction
    | @built_lookup_one k2' x2 e2 s2 r2 v2 f2 hb2 hsep2 _ hsmall2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rcases qK hsep hsep2 with ⟨rfl,rfl⟩
      have heq2:=ihsmall s1 _ rfl hsmall2
      injection heq2 with h3 h4
      subst h3 h4; rfl
    | @built_lookup_two k2' x2 e2 s2 r2 y2 f2 hb2 hsep2 _ hsmall2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rcases qK hsep hsep2 with ⟨rfl,rfl⟩
      have heq2:=ihsmall s1 _ rfl hsmall2
      contradiction
  | @built_lookup_two k1 x1 e1 s1 r1 y1 f1 hb hsep hodd hsmall ihprev ihsmall =>
    intro k2 g hk hg
    cases hg with
    | built_root => have:=built_nonnegative hb; omega
    | @built_one k2' _ _ hb2 =>
      have heq:=ihprev k2' _ (by omega) hb2
      contradiction
    | @built_even k2' x2 e2 hb2 heven2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rw [hodd] at heven2; contradiction
    | @built_lookup_one k2' x2 e2 s2 r2 v2 f2 hb2 hsep2 _ hsmall2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rcases qK hsep hsep2 with ⟨rfl,rfl⟩
      have heq2:=ihsmall s1 _ rfl hsmall2
      contradiction
    | @built_lookup_two k2' x2 e2 s2 r2 y2 f2 hb2 hsep2 _ hsmall2 =>
      have hk' : k1=k2':= by omega
      subst hk'
      have heq:=ihprev k1 _ rfl hb2
      injection heq with h1 h2
      subst h1 h2
      rcases qK hsep hsep2 with ⟨rfl,rfl⟩
      have heq2:=ihsmall s1 _ rfl hsmall2
      injection heq2 with h3 h4
      subst h3 h4; rfl
theorem built_unique {k : ℤ} {f : entry} (h : Built k f) :
    ∀ g,Built k g → f=g :=
  fun g hg => qbC h k g rfl hg
end UniqueTable
namespace CheckTable
open Table
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000
def qb7 (p : pair) (f : pair → Option entry) : Option entry :=
  q2 p.d fun d =>
  q2 p.p fun pp =>
  q2 p.b fun b =>
  q2 p.c fun c =>
  f ⟨pp,d,b,c⟩
@[simp] lemma strictPair_eq (p : pair) (f : pair → Option entry) :
    qb7 p f=f p:= by
  cases p; simp [qb7]
def qaK (k : ℤ) (x : pair) : Option (ℤ × ℤ) :=
  q2 (h x) fun hx =>
  if 0 < hx then
    let p:=q4 18 hx
    q2 p.1 fun s =>
    q2 p.2 fun r =>
    if decide (1 ≤ s ∧ s < k - x.d ∧ hx=q0 s * r) && zodd r then
      some (s,r)
    else
      none
  else
    none
lemma qaY {k : ℤ} {x : pair} {s r : ℤ} (hsep : qaK k x=some (s,r)) :
    qa k x s r:= by
  unfold qaK at hsep
  simp only [strictInt_eq] at hsep
  try dsimp -failIfUnchanged only at hsep
  split_ifs at hsep with hpos hcond
  injection hsep with hpair
  injection hpair with hs hr
  subst hs hr
  rcases Bool.and_eq_true_iff.mp hcond with ⟨hdec,hodd⟩
  rcases of_decide_eq_true hdec with ⟨h1,h2,h3⟩
  exact ⟨h1,h2,h3,(zodd_iff _).mp hodd⟩
def advance (lookup : ℤ → Option entry) (k : ℤ) (f : entry) : Option entry :=
  match f with
  | .One v e =>
    q2 v fun v =>
    q2 e fun e =>
    some (.Two ⟨1,1,v,0⟩ e)
  | .Two x e =>
    if q3 k x then
      q2 (x.b + x.c + 3) fun v' =>
      q2 (e + 1) fun e' =>
      some (.One v' e')
    else
      match qaK k x with
      | some (s,r) =>
        match lookup s with
        | some (.One v f) =>
          q2 (x.b + x.c + v + 2) fun v' =>
          q2 (e + 1 + f) fun e' =>
          some (.One v' e')
        | some (.Two y f) =>
          q2 (e + 1 + f) fun e' =>
          qb7 (qbu (qQ x s r y)) fun p' =>
          some (.Two p' e')
        | none => none
      | none => none
lemma advance_spec {lookup : ℤ → Option entry} {k : ℤ} {f g : entry}
    (hlib : ∀ s x,lookup s=some x → Built s x)
    (hf : Built k f) (hadv : advance lookup k f=some g) :
    Built (k + 1) g:= by
  cases f with
  | One v e =>
    unfold advance at hadv
    simp only [strictInt_eq] at hadv
    try dsimp -failIfUnchanged only at hadv
    injection hadv with h; subst h
    exact Built.built_one hf
  | Two x e =>
    unfold advance at hadv
    simp only [strictInt_eq,strictPair_eq] at hadv
    try dsimp -failIfUnchanged only at hadv
    split_ifs at hadv with he
    · injection hadv with h; subst h
      exact Built.built_even hf he
    · have he' : q3 k x=false:=Bool.eq_false_iff.mpr he
      cases hsep : qaK k x with
      | none => rw [hsep] at hadv; contradiction
      | some sr =>
        rcases sr with ⟨s,r⟩
        rw [hsep] at hadv
        try dsimp -failIfUnchanged only at hadv
        have hs:=qaY hsep
        cases hsmall : lookup s with
        | none => rw [hsmall] at hadv; contradiction
        | some entry_s =>
          rw [hsmall] at hadv
          cases entry_s with
          | One v f =>
            try dsimp -failIfUnchanged only at hadv
            injection hadv with h; subst h
            exact Built.built_lookup_one hf hs he' (hlib s _ hsmall)
          | Two y f =>
            try dsimp -failIfUnchanged only at hadv
            injection hadv with h; subst h
            exact Built.built_lookup_two hf hs he' (hlib s _ hsmall)
def qbq : ℕ → (ℤ → Option entry) → ℤ → pair → Option (ℤ × ℕ)
  | 0,_,_,_ => none
  | fuel + 1,lookup,k,x =>
    if q3 k x then some (1,1)
    else
      match qaK k x with
      | some (s,r) =>
        match lookup s with
        | some (.One _ e) => some (1 + e,1)
        | some (.Two y e) =>
          match qbq fuel lookup k (qQ x s r y) with
          | some (f,n) => some (1 + e + f,1 + n)
          | none => none
        | none => none
      | none => none
def nth_entry : List entry → ℕ → Option entry
  | [],_ => none
  | x :: _,0 => some x
  | _ :: xs,n + 1 => nth_entry xs n
lemma qc7 (xs : List entry) (f : entry) (i : ℕ) :
    nth_entry (xs ++ [f]) i =
      if i < xs.length then nth_entry xs i
      else if i=xs.length then some f
      else none:= by
  induction xs generalizing i with
  | nil =>
    cases i <;> simp [nth_entry]
  | cons x xs ih =>
    cases i with
    | zero => simp [nth_entry]
    | succ i =>
      simp only [List.cons_append,nth_entry,List.length_cons,ih i]
      split_ifs <;> first | rfl | omega
def lookup (bank : List entry) (s : ℤ) : Option entry :=
  if 0 ≤ s then nth_entry bank s.toNat else none
def bank_ok (bank : List entry) : Prop :=
  ∀ (i : ℕ) (f : entry),nth_entry bank i=some f → Built (i : ℤ) f
lemma lookup_spec {bank : List entry} (hb : bank_ok bank) :
    ∀ s f,lookup bank s=some f → Built s f:= by
  intro s f hl
  unfold lookup at hl
  split_ifs at hl with hs
  have h:=hb s.toNat f hl
  rwa [Int.toNat_of_nonneg hs] at h
lemma bank_snoc {bank : List entry} {f : entry} (hbank : bank_ok bank)
    (hf : Built (bank.length : ℤ) f) :
    bank_ok (bank ++ [f]):= by
  intro i g hget
  rw [qc7] at hget
  split_ifs at hget with hlt heq
  · exact hbank i g hget
  · injection hget with h; subst h; subst heq; exact hf
def qa8 : ℕ → Option (List entry)
  | 0 => some [.One 1 0]
  | n + 1 =>
    match qa8 n with
    | some bank =>
      match nth_entry bank n with
      | some f =>
        match advance (lookup bank) (n : ℤ) f with
        | some g => some (bank ++ [g])
        | none => none
      | none => none
    | none => none
lemma qc0 (n : ℕ) (bank : List entry) (hb : qa8 n=some bank) :
    bank.length=1 + n ∧ bank_ok bank:= by
  induction n generalizing bank with
  | zero =>
    unfold qa8 at hb
    injection hb with h; subst h
    refine ⟨rfl,?_⟩
    intro i f hget
    cases i with
    | zero =>
      unfold nth_entry at hget
      injection hget with h; subst h
      exact Built.built_root
    | succ i =>
      cases i <;> contradiction
  | succ n ih =>
    unfold qa8 at hb
    cases hxs : qa8 n with
    | none => rw [hxs] at hb; contradiction
    | some xs =>
      rw [hxs] at hb
      try dsimp -failIfUnchanged only at hb
      rcases ih xs hxs with ⟨hlen,hbank⟩
      cases hf : nth_entry xs n with
      | none => rw [hf] at hb; contradiction
      | some f =>
        rw [hf] at hb
        try dsimp -failIfUnchanged only at hb
        cases hg : advance (lookup xs) (n : ℤ) f with
        | none => rw [hg] at hb; contradiction
        | some g =>
          rw [hg] at hb
          try dsimp -failIfUnchanged only at hb
          injection hb with h; subst h
          refine ⟨by simp [hlen]; omega,?_⟩
          apply bank_snoc hbank
          rw [hlen]
          have hcast : ((1 + n : ℕ) : ℤ)=(n : ℤ) + 1:= by omega
          rw [hcast]
          exact advance_spec (lookup_spec hbank) (hbank n f hf) hg
def depth : entry → ℤ
  | .One _ _ => 0
  | .Two x _ => x.d
def bounded (k : ℤ) (f : entry) : Prop :=
  qad f ≤ 4 * k ^ 3 ∧ depth f ≤ 6 * q1 k + 9
def bank : List entry:=[
  .One 1 0,
  .Two ⟨1,1,1,0⟩ 0,
  .One 4 1,
  .Two ⟨1,1,4,0⟩ 1,
  .One 7 2,
  .Two ⟨1,1,7,0⟩ 2,
  .Two ⟨3,3,6,4⟩ 3,
  .One 13 4,
  .Two ⟨1,1,13,0⟩ 4,
  .One 22 7,
  .Two ⟨1,1,22,0⟩ 7,
  .One 25 8,
  .Two ⟨1,1,25,0⟩ 8,
  .One 31 10,
  .Two ⟨1,1,31,0⟩ 10,
  .Two ⟨3,3,18,16⟩ 11,
  .One 37 12,
  .Two ⟨1,1,37,0⟩ 12
]
lemma qaJ : qa8 17=some bank:= by decide +kernel
lemma checked_bank : bank_ok bank:=(qc0 17 bank qaJ).2
lemma first : Built 1 (.Two ⟨1,1,1,0⟩ 0) :=
  Built.built_one Built.built_root
lemma pair.ext {x y : pair} (hp : x.p = y.p) (hd : x.d = y.d) (hb : x.b = y.b) (hc : x.c = y.c) : x = y := by
  cases x; cases y; dsimp -failIfUnchanged at *; subst hp hd hb hc; rfl

lemma nat_add_eq (a b : ℕ) : Nat.add a b = a + b := rfl
lemma nat_sub_eq (a b : ℕ) : Nat.sub a b = a - b := rfl
lemma nat_mul_eq (a b : ℕ) : Nat.mul a b = a * b := rfl
lemma nat_pow_eq (a b : ℕ) : Nat.pow a b = a ^ b := rfl
lemma nat_mod_eq (a b : ℕ) : Nat.mod a b = a % b := rfl

inductive entry_nat where
  | One (v e : ℕ)
  | Two (p d b c e : ℕ)
  deriving DecidableEq, Repr

def to_pair (p d b c : ℕ) : pair :=
  ⟨(p : ℤ), (d : ℤ), (b : ℤ), (c : ℤ)⟩

def to_pair_c1 (p d b c1 : ℕ) : pair :=
  ⟨(p : ℤ), (d : ℤ), (b : ℤ), (c1 : ℤ) - 1⟩

def to_entry : entry_nat → entry
  | .One v e => .One (v : ℤ) (e : ℤ)
  | .Two p d b c e => .Two (to_pair p d b c) (e : ℤ)

def ctz18 (m : ℕ) : ℕ × ℕ :=
  sNat (Nat.mod m 16) fun r4 =>
  if Nat.beq r4 0 then
    sNat (Nat.div m 16) fun q4 =>
    sNat (Nat.mod q4 16) fun r8 =>
    if Nat.beq r8 0 then
      sNat (Nat.div q4 16) fun q8 =>
      sNat (Nat.mod q8 16) fun r12 =>
      if Nat.beq r12 0 then
        sNat (Nat.div q8 16) fun q12 =>
        sNat (Nat.mod q12 16) fun r16 =>
        if Nat.beq r16 0 then
          sNat (Nat.div q12 16) fun q16 =>
          if Nat.beq (Nat.mod q16 4) 0 then (18, Nat.div q16 4)
          else if Nat.beq (Nat.mod q16 2) 0 then (17, Nat.div q16 2)
          else (16, q16)
        else
          if Nat.beq (Nat.mod r16 4) 0 then
            if Nat.beq (Nat.mod r16 8) 0 then (15, Nat.div q12 8) else (14, Nat.div q12 4)
          else if Nat.beq (Nat.mod r16 2) 0 then (13, Nat.div q12 2) else (12, q12)
      else
        if Nat.beq (Nat.mod r12 4) 0 then
          if Nat.beq (Nat.mod r12 8) 0 then (11, Nat.div q8 8) else (10, Nat.div q8 4)
        else if Nat.beq (Nat.mod r12 2) 0 then (9, Nat.div q8 2) else (8, q8)
    else
      if Nat.beq (Nat.mod r8 4) 0 then
        if Nat.beq (Nat.mod r8 8) 0 then (7, Nat.div q4 8) else (6, Nat.div q4 4)
      else if Nat.beq (Nat.mod r8 2) 0 then (5, Nat.div q4 2) else (4, q4)
  else
    if Nat.beq (Nat.mod r4 4) 0 then
      if Nat.beq (Nat.mod r4 8) 0 then (3, Nat.div m 8) else (2, Nat.div m 4)
    else if Nat.beq (Nat.mod r4 2) 0 then (1, Nat.div m 2) else (0, m)

def bank_nat (s : ℕ) : Option entry_nat :=
  if Nat.ble s 8 then
    if Nat.ble s 4 then
      if Nat.ble s 2 then
        if Nat.beq s 0 then some (.One 1 0)
        else if Nat.beq s 1 then some (.Two 1 1 1 0 0)
        else if Nat.beq s 2 then some (.One 4 1)
        else none
      else
        if Nat.beq s 3 then some (.Two 1 1 4 0 1)
        else if Nat.beq s 4 then some (.One 7 2)
        else none
    else
      if Nat.ble s 6 then
        if Nat.beq s 5 then some (.Two 1 1 7 0 2)
        else if Nat.beq s 6 then some (.Two 3 3 6 4 3)
        else none
      else
        if Nat.beq s 7 then some (.One 13 4)
        else if Nat.beq s 8 then some (.Two 1 1 13 0 4)
        else none
  else
    if Nat.ble s 13 then
      if Nat.ble s 10 then
        if Nat.beq s 9 then some (.One 22 7)
        else if Nat.beq s 10 then some (.Two 1 1 22 0 7)
        else none
      else
        if Nat.beq s 11 then some (.One 25 8)
        else if Nat.beq s 12 then some (.Two 1 1 25 0 8)
        else if Nat.beq s 13 then some (.One 31 10)
        else none
    else
      if Nat.ble s 15 then
        if Nat.beq s 14 then some (.Two 1 1 31 0 10)
        else if Nat.beq s 15 then some (.Two 3 3 18 16 11)
        else none
      else
        if Nat.beq s 16 then some (.One 37 12)
        else if Nat.beq s 17 then some (.Two 1 1 37 0 12)
        else none

lemma bank_nat_lt18 (s : ℕ) (f : entry_nat) (h : bank_nat s = some f) : s < 18 := by
  by_contra hge
  have h1 : Nat.ble s 8 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega
  have h2 : Nat.ble s 13 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega
  have h3 : Nat.ble s 15 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; omega
  have h4 : Nat.beq s 16 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; omega
  have h5 : Nat.beq s 17 = false := by rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; omega
  unfold bank_nat at h
  rw [h1, h2, h3, h4, h5] at h
  contradiction

lemma bank_nat_spec (s : ℕ) (f : entry_nat) (h : bank_nat s = some f) :
    Built (s : ℤ) (to_entry f) := by
  apply lookup_spec checked_bank (s : ℤ) (to_entry f)
  have hs : s < 18 := bank_nat_lt18 s f h
  rcases (by omega : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 ∨ s = 4 ∨ s = 5 ∨ s = 6 ∨ s = 7 ∨ s = 8 ∨
      s = 9 ∨ s = 10 ∨ s = 11 ∨ s = 12 ∨ s = 13 ∨ s = 14 ∨ s = 15 ∨ s = 16 ∨ s = 17) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> {
    dsimp -failIfUnchanged [bank_nat] at h
    injection h with h
    subst h
    decide
  }

def q3_nat (k p d b : ℕ) : Bool :=
  let qk := if Nat.ble (Nat.add d 1) k then b else Nat.add p b
  Nat.beq (Nat.mod qk 2) 0

lemma q3_nat_eq (k p d b : ℕ) (c : ℤ) :
    q3_nat k p d b = q3 (k : ℤ) ⟨(p : ℤ), (d : ℤ), (b : ℤ), c⟩ := by
  unfold q3_nat q3 qk qb6
  dsimp -failIfUnchanged only
  by_cases hlt : (d : ℤ) < (k : ℤ)
  · have hble : Nat.ble (Nat.add d 1) k = true := by
      rw [Nat.ble_eq, nat_add_eq]; omega
    rw [if_pos hble, if_pos hlt]
    by_cases hev : (b : ℤ) % 2 = 0
    · have hbeq : Nat.beq (Nat.mod b 2) 0 = true := by
        rw [Nat.beq_eq, nat_mod_eq]; omega
      rw [hbeq, decide_eq_true hev]
    · have hbeq : Nat.beq (Nat.mod b 2) 0 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq, nat_mod_eq]; omega
      rw [hbeq, decide_eq_false hev]
  · have hble : ¬ Nat.ble (Nat.add d 1) k = true := by
      rw [Nat.ble_eq, nat_add_eq]; omega
    rw [if_neg hble, if_neg hlt]
    by_cases hev : ((p : ℤ) + (b : ℤ)) % 2 = 0
    · have hbeq : Nat.beq (Nat.mod (Nat.add p b) 2) 0 = true := by
        rw [Nat.beq_eq, nat_mod_eq, nat_add_eq]; omega
      rw [hbeq, decide_eq_true hev]
    · have hbeq : Nat.beq (Nat.mod (Nat.add p b) 2) 0 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq, nat_mod_eq, nat_add_eq]; omega
      rw [hbeq, decide_eq_false hev]

def qaK_nat (k d hx : ℕ) : Option (ℕ × ℕ) :=
  if Nat.beq (Nat.mod hx 2) 0 then
    match ctz18 hx with
    | (sn, rn) =>
      sNat rn fun r =>
      if Nat.ble 1 sn && Nat.ble (Nat.add (Nat.add sn d) 1) k &&
         Nat.beq hx (Nat.mul (Nat.pow 2 sn) r) && Nat.beq (Nat.mod r 2) 1 then
        some (sn, r)
      else none
  else none

lemma qaK_nat_spec {k p d b : ℕ} {c : ℤ} {hx s r : ℕ}
    (hhx : (hx : ℤ) = h ⟨(p : ℤ), (d : ℤ), (b : ℤ), c⟩)
    (hsep : qaK_nat k d hx = some (s, r)) :
    qa (k : ℤ) ⟨(p : ℤ), (d : ℤ), (b : ℤ), c⟩ (s : ℤ) (r : ℤ) := by
  unfold qaK_nat at hsep
  split_ifs at hsep with hmod
  rcases hctz : ctz18 hx with ⟨sn, rn⟩
  rw [hctz] at hsep
  simp only [sNat_eq] at hsep
  split_ifs at hsep with hcond
  injection hsep with hpair
  injection hpair with hs hr
  subst hs
  subst hr
  rcases Bool.and_eq_true_iff.mp hcond with ⟨hcond1, hodd⟩
  rcases Bool.and_eq_true_iff.mp hcond1 with ⟨hcond2, hmul⟩
  rcases Bool.and_eq_true_iff.mp hcond2 with ⟨hs1, hsk⟩
  rw [Nat.ble_eq] at hs1 hsk
  rw [Nat.beq_eq] at hmul hodd
  simp only [nat_add_eq, nat_mul_eq, nat_pow_eq, nat_mod_eq] at hsk hmul hodd
  have hq0 : q0 (sn : ℤ) = ((2 ^ sn : ℕ) : ℤ) := rfl
  refine ⟨by omega, by dsimp -failIfUnchanged; omega, ?_, ?_⟩
  · rw [← hhx, hq0]
    exact_mod_cast hmul
  · refine ⟨(rn / 2 : ℕ), ?_⟩
    omega

def qbq_nat : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _, _ => false
  | fuel + 1, k, p, d, b, c1 =>
    if q3_nat k p d b then true
    else
      sNat (Nat.add (Nat.add b (Nat.mul 2 c1)) 1) fun hx =>
      match qaK_nat k d hx with
      | some (s, r) =>
        match bank_nat s with
        | some (.One _ _) => true
        | some (.Two yp yd yb yc _) =>
          if Nat.ble yd s && Nat.ble p (Nat.pow 2 (Nat.add d 1)) then
            sNat (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) fun dlt =>
            sNat (Nat.add (Nat.add hx yc) 1) fun num1 =>
            sNat (Nat.add dlt c1) fun den =>
            if Nat.ble den num1 then
              sNat (Nat.mul yp (Nat.sub (Nat.pow 2 (Nat.add d 1)) p)) fun pp =>
              sNat (Nat.add d yd) fun dd =>
              sNat (Nat.add dlt yb) fun bb =>
              sNat (Nat.sub num1 den) fun cc1 =>
              qbq_nat fuel k pp dd bb cc1
            else false
          else false
        | none => false
      | none => false

lemma qbq_nat_spec {fuel k p d b c1 : ℕ}
    (hfin : qbq_nat fuel k p d b c1 = true) :
    ∃ e n, Boundary Built (k : ℤ) (to_pair_c1 p d b c1) e n := by
  induction fuel generalizing p d b c1 with
  | zero => contradiction
  | succ fuel ih =>
    unfold qbq_nat at hfin
    split_ifs at hfin with he
    · rw [q3_nat_eq k p d b ((c1 : ℤ) - 1)] at he
      exact ⟨1, 1, Boundary.boundary_even (to_pair_c1 p d b c1) he⟩
    · simp only [sNat_eq] at hfin
      have he' : q3 (k : ℤ) (to_pair_c1 p d b c1) = false := by
        unfold to_pair_c1
        rw [← q3_nat_eq k p d b ((c1 : ℤ) - 1)]
        exact Bool.eq_false_iff.mpr he
      set hx := Nat.add (Nat.add b (Nat.mul 2 c1)) 1
      have hhx_val : (hx : ℤ) = (b : ℤ) + 2 * (c1 : ℤ) + 1 := by
        change ((b + 2 * c1 + 1 : ℕ) : ℤ) = (b : ℤ) + 2 * (c1 : ℤ) + 1
        omega
      have hhx : (hx : ℤ) = h (to_pair_c1 p d b c1) := by
        unfold to_pair_c1 h; dsimp -failIfUnchanged only; rw [hhx_val]; ring
      cases hsep : qaK_nat k d hx with
      | none => rw [hsep] at hfin; contradiction
      | some sr =>
        rcases sr with ⟨s, r⟩
        rw [hsep] at hfin
        dsimp -failIfUnchanged only at hfin
        have hs := qaK_nat_spec hhx hsep
        cases hsmall : bank_nat s with
        | none => rw [hsmall] at hfin; contradiction
        | some entry_s =>
          rw [hsmall] at hfin
          have hbuilt_s := bank_nat_spec s entry_s hsmall
          cases entry_s with
          | One v f_cnt =>
            exact ⟨1 + (f_cnt : ℤ), 1, Boundary.boundary_one _ (s : ℤ) (r : ℤ) (v : ℤ) (f_cnt : ℤ) hs he' hbuilt_s⟩
          | Two yp yd yb yc f_cnt =>
            dsimp -failIfUnchanged only at hfin
            split_ifs at hfin with hbounds hble
            rcases Bool.and_eq_true_iff.mp hbounds with ⟨hyd_le, hp_le⟩
            rw [Nat.ble_eq] at hyd_le hp_le hble
            simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq] at hyd_le hp_le hble
            rcases ih hfin with ⟨g_cnt, m_cnt, htail⟩
            have hqQ_eq : to_pair_c1
                (Nat.mul yp (Nat.sub (Nat.pow 2 (Nat.add d 1)) p))
                (Nat.add d yd)
                (Nat.add (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) yb)
                (Nat.sub (Nat.add (Nat.add hx yc) 1) (Nat.add (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) c1)) =
                qQ (to_pair_c1 p d b c1) (s : ℤ) (r : ℤ) (to_pair yp yd yb yc) := by
              have hq0_d1 : q0 ((d : ℤ) + 1) = ((2 ^ (d + 1) : ℕ) : ℤ) := rfl
              have hq0_s : q0 ((s : ℤ) - (yd : ℤ)) = ((2 ^ (s - yd) : ℕ) : ℤ) := by
                have hsub : (s : ℤ) - (yd : ℤ) = ((s - yd : ℕ) : ℤ) := by omega
                rw [hsub]; rfl
              apply pair.ext
              · dsimp -failIfUnchanged only [to_pair_c1, to_pair, qQ]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_d1]
                rw [Nat.cast_mul, Nat.cast_sub hp_le]
              · dsimp -failIfUnchanged only [to_pair_c1, to_pair, qQ]
                simp only [nat_add_eq]
                push_cast; rfl
              · dsimp -failIfUnchanged only [to_pair_c1, to_pair, qQ, delta]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_s]
                push_cast; ring
              · dsimp -failIfUnchanged only [to_pair_c1, to_pair, qQ, delta, h]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_s]
                rw [Nat.cast_sub hble]
                push_cast
                rw [hhx_val]
                ring
            rw [hqQ_eq] at htail
            exact ⟨1 + (f_cnt : ℤ) + g_cnt, 1 + m_cnt,
              Boundary.boundary_two _ (s : ℤ) (r : ℤ) _ (f_cnt : ℤ) g_cnt m_cnt hs he' hbuilt_s htail⟩

def step1_nat (k : ℕ) (f : entry_nat) : Option entry_nat :=
  match f with
  | .One v e =>
    if Nat.ble e (Nat.mul 4 (Nat.mul k (Nat.mul k k))) then
      some (.Two 1 1 v 0 e)
    else none
  | .Two p d b c e =>
    if Nat.ble d 9 && Nat.ble e (Nat.mul 4 (Nat.mul k (Nat.mul k k))) then
      if q3_nat k p d b then
        sNat (Nat.add (Nat.add b c) 3) fun v' =>
        sNat (Nat.add e 1) fun e' =>
        some (.One v' e')
      else if qbq_nat 4 k p d b c then
        sNat (Nat.add (Nat.add b (Nat.mul 2 c)) 3) fun hx =>
        match qaK_nat k d hx with
        | some (s, r) =>
          match bank_nat s with
          | some (.One v f_cnt) =>
            sNat (Nat.add (Nat.add (Nat.add b c) v) 2) fun v' =>
            sNat (Nat.add (Nat.add e 1) f_cnt) fun e' =>
            some (.One v' e')
          | some (.Two yp yd yb yc f_cnt) =>
            if Nat.ble yd s && Nat.ble p (Nat.pow 2 (Nat.add d 1)) then
              sNat (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) fun dlt =>
              sNat (Nat.add hx yc) fun num =>
              sNat (Nat.add (Nat.add dlt c) 1) fun den =>
              if Nat.ble den num then
                sNat (Nat.mul yp (Nat.sub (Nat.pow 2 (Nat.add d 1)) p)) fun pp =>
                sNat (Nat.add (Nat.add d yd) 1) fun dd1 =>
                sNat (Nat.add dlt yb) fun bb =>
                sNat (Nat.sub num den) fun cc =>
                sNat (Nat.add (Nat.add e 1) f_cnt) fun e' =>
                some (.Two pp dd1 bb cc e')
              else none
            else none
          | none => none
        | none => none
      else none
    else none

lemma step1_nat_spec {k : ℕ} {f g : entry_nat}
    (hf : Built (k : ℤ) (to_entry f))
    (hstep : step1_nat k f = some g) :
    Built ((k : ℤ) + 1) (to_entry g) ∧
    bounded (k : ℤ) (to_entry f) ∧
    qaf Built (k : ℤ) (to_entry f) := by
  cases f with
  | One v e =>
    unfold step1_nat at hstep
    dsimp -failIfUnchanged only at hstep
    split_ifs at hstep with hble
    injection hstep with h; subst h
    rw [Nat.ble_eq] at hble
    simp only [nat_mul_eq] at hble
    have hlog := qh (k : ℤ)
    have hpow3 : ((4 * (k * (k * k)) : ℕ) : ℤ) = 4 * (k : ℤ) ^ 3 := by
      push_cast; ring
    refine ⟨Built.built_one hf, ⟨?_, ?_⟩, trivial⟩
    · dsimp -failIfUnchanged only [to_entry, qad]; rw [← hpow3]; exact_mod_cast hble
    · dsimp -failIfUnchanged only [to_entry, depth]; omega
  | Two p d b c e =>
    unfold step1_nat at hstep
    dsimp -failIfUnchanged only at hstep
    split_ifs at hstep with hbd hq3 hqbq
    · simp only [sNat_eq] at hstep
      injection hstep with h; subst h
      rcases Bool.and_eq_true_iff.mp hbd with ⟨hd9, he_le⟩
      rw [Nat.ble_eq] at hd9 he_le
      simp only [nat_mul_eq] at he_le
      have hlog := qh (k : ℤ)
      have hpow3 : ((4 * (k * (k * k)) : ℕ) : ℤ) = 4 * (k : ℤ) ^ 3 := by
        push_cast; ring
      have hq3_int : q3 (k : ℤ) (to_pair p d b c) = true := by
        unfold to_pair; rw [← q3_nat_eq]; exact hq3
      have hq3_qba : q3 (k : ℤ) (qba (to_pair p d b c)) = true := by
        unfold qba to_pair; dsimp -failIfUnchanged only; rw [← q3_nat_eq]; exact hq3
      refine ⟨?_, ⟨?_, ?_⟩, ⟨1, 1, Boundary.boundary_even _ hq3_qba⟩⟩
      · dsimp -failIfUnchanged only [to_entry, to_pair]
        simp only [nat_add_eq]
        push_cast
        exact Built.built_even hf hq3_int
      · dsimp -failIfUnchanged only [to_entry, qad]; rw [← hpow3]; exact_mod_cast he_le
      · dsimp -failIfUnchanged only [to_entry, depth, to_pair]; omega
    · simp only [sNat_eq] at hstep
      rcases Bool.and_eq_true_iff.mp hbd with ⟨hd9, he_le⟩
      rw [Nat.ble_eq] at hd9 he_le
      simp only [nat_mul_eq] at he_le
      have hlog := qh (k : ℤ)
      have hpow3 : ((4 * (k * (k * k)) : ℕ) : ℤ) = 4 * (k : ℤ) ^ 3 := by
        push_cast; ring
      have hbounded : bounded (k : ℤ) (to_entry (.Two p d b c e)) := by
        refine ⟨?_, ?_⟩
        · dsimp -failIfUnchanged only [to_entry, qad]; rw [← hpow3]; exact_mod_cast he_le
        · dsimp -failIfUnchanged only [to_entry, depth, to_pair]; omega
      have hqaf : qaf Built (k : ℤ) (to_entry (.Two p d b c e)) := by
        dsimp -failIfUnchanged only [qaf, to_entry]
        have hqba_eq : qba (to_pair p d b c) = to_pair_c1 p d b c := rfl
        rw [hqba_eq]
        exact qbq_nat_spec hqbq
      have he' : q3 (k : ℤ) (to_pair p d b c) = false := by
        unfold to_pair; rw [← q3_nat_eq]; exact Bool.eq_false_iff.mpr hq3
      set hx := Nat.add (Nat.add b (Nat.mul 2 c)) 3
      have hhx_val : (hx : ℤ) = (b : ℤ) + 2 * (c : ℤ) + 3 := by
        change ((b + 2 * c + 3 : ℕ) : ℤ) = (b : ℤ) + 2 * (c : ℤ) + 3
        omega
      have hhx : (hx : ℤ) = h (to_pair p d b c) := by
        unfold to_pair h; dsimp -failIfUnchanged only; exact hhx_val
      cases hsep : qaK_nat k d hx with
      | none => rw [hsep] at hstep; contradiction
      | some sr =>
        rcases sr with ⟨s, r⟩
        rw [hsep] at hstep
        dsimp -failIfUnchanged only at hstep
        have hs := qaK_nat_spec hhx hsep
        cases hsmall : bank_nat s with
        | none => rw [hsmall] at hstep; contradiction
        | some entry_s =>
          rw [hsmall] at hstep
          have hbuilt_s := bank_nat_spec s entry_s hsmall
          cases entry_s with
          | One v f_cnt =>
            simp only [sNat_eq] at hstep
            injection hstep with h; subst h
            refine ⟨?_, hbounded, hqaf⟩
            dsimp -failIfUnchanged only [to_entry]
            simp only [nat_add_eq]
            push_cast
            exact Built.built_lookup_one hf hs he' hbuilt_s
          | Two yp yd yb yc f_cnt =>
            dsimp -failIfUnchanged only at hstep
            split_ifs at hstep with hbounds hble
            injection hstep with h; subst h
            rcases Bool.and_eq_true_iff.mp hbounds with ⟨hyd_le, hp_le⟩
            rw [Nat.ble_eq] at hyd_le hp_le hble
            simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq] at hyd_le hp_le hble
            refine ⟨?_, hbounded, hqaf⟩
            dsimp -failIfUnchanged only [to_entry]
            have hqbu_eq : to_pair
                (Nat.mul yp (Nat.sub (Nat.pow 2 (Nat.add d 1)) p))
                (Nat.add (Nat.add d yd) 1)
                (Nat.add (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) yb)
                (Nat.sub (Nat.add hx yc) (Nat.add (Nat.add (Nat.mul (Nat.mul yp (Nat.pow 2 (Nat.sub s yd))) r) c) 1)) =
                qbu (qQ (to_pair p d b c) (s : ℤ) (r : ℤ) (to_pair yp yd yb yc)) := by
              have hq0_d1 : q0 ((d : ℤ) + 1) = ((2 ^ (d + 1) : ℕ) : ℤ) := rfl
              have hq0_s : q0 ((s : ℤ) - (yd : ℤ)) = ((2 ^ (s - yd) : ℕ) : ℤ) := by
                have hsub : (s : ℤ) - (yd : ℤ) = ((s - yd : ℕ) : ℤ) := by omega
                rw [hsub]; rfl
              apply pair.ext
              · dsimp -failIfUnchanged only [to_pair, qbu, qQ]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_d1]
                rw [Nat.cast_mul, Nat.cast_sub hp_le]
              · dsimp -failIfUnchanged only [to_pair, qbu, qQ]
                simp only [nat_add_eq]
                push_cast; ring
              · dsimp -failIfUnchanged only [to_pair, qbu, qQ, delta]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_s]
                push_cast; ring
              · dsimp -failIfUnchanged only [to_pair, qbu, qQ, delta, h]
                simp only [nat_add_eq, nat_sub_eq, nat_mul_eq, nat_pow_eq, hq0_s]
                rw [Nat.cast_sub hble]
                push_cast
                rw [hhx_val]
                ring
            rw [hqbu_eq]
            simp only [nat_add_eq]
            push_cast
            exact Built.built_lookup_two hf hs he' hbuilt_s

def qb_nat : ℕ → ℕ → entry_nat → Option entry_nat
  | 0, k, f => step1_nat k f
  | n + 1, k, f =>
    match qb_nat n k f with
    | some g => sNat (Nat.add k (Nat.pow 2 n)) fun k' => qb_nat n k' g
    | none => none

lemma qc2_nat {n k : ℕ} {f f_end : entry_nat}
    (hf : Built (k : ℤ) (to_entry f))
    (hcheck : qb_nat n k f = some f_end) :
    Built (((k + 2 ^ n : ℕ) : ℤ)) (to_entry f_end) ∧
    ∀ j : ℤ, (k : ℤ) ≤ j ∧ j < ((k + 2 ^ n : ℕ) : ℤ) →
      ∃ g, Built j g ∧ bounded j g ∧ qaf Built j g := by
  induction n generalizing k f f_end with
  | zero =>
    unfold qb_nat at hcheck
    rcases step1_nat_spec hf hcheck with ⟨hb_end, hbd, hqaf⟩
    have hpow : k + 2 ^ 0 = k + 1 := rfl
    rw [hpow]
    refine ⟨by push_cast; exact hb_end, fun j hj => ?_⟩
    have hjk : j = (k : ℤ) := by omega
    subst hjk
    exact ⟨to_entry f, hf, hbd, hqaf⟩
  | succ n ih =>
    unfold qb_nat at hcheck
    cases hmid : qb_nat n k f with
    | none => rw [hmid] at hcheck; contradiction
    | some g =>
      rw [hmid] at hcheck
      simp only [sNat_eq] at hcheck
      have hk' : Nat.add k (Nat.pow 2 n) = k + 2 ^ n := rfl
      rw [hk'] at hcheck
      rcases ih hf hmid with ⟨hg, hrange1⟩
      rcases ih hg hcheck with ⟨hend, hrange2⟩
      have hpow : k + 2 ^ (n + 1) = (k + 2 ^ n) + 2 ^ n := by
        rw [Nat.pow_succ]; ring
      rw [hpow]
      refine ⟨hend, fun j hj => ?_⟩
      by_cases hjlt : j < ((k + 2 ^ n : ℕ) : ℤ)
      · exact hrange1 j ⟨hj.1, hjlt⟩
      · exact hrange2 j ⟨by omega, by omega⟩

lemma chunk_0 : qb_nat 12 1 (.Two 1 1 1 0 0) = some (.Two 1 1 10951 0 3650) := by decide +kernel
lemma chunk_1 : qb_nat 12 4097 (.Two 1 1 10951 0 3650) = some (.Two 1 1 21925 0 7308) := by decide +kernel
lemma chunk_2 : qb_nat 12 8193 (.Two 1 1 21925 0 7308) = some (.One 32881 10960) := by decide +kernel
lemma chunk_3 : qb_nat 12 12289 (.One 32881 10960) = some (.One 43852 14617) := by decide +kernel
lemma chunk_4 : qb_nat 12 16385 (.One 43852 14617) = some (.One 54817 18272) := by decide +kernel
lemma chunk_5 : qb_nat 12 20481 (.One 54817 18272) = some (.Two 1 1 65782 0 21927) := by decide +kernel
lemma chunk_6 : qb_nat 12 24577 (.Two 1 1 65782 0 21927) = some (.Two 1 1 76735 0 25578) := by decide +kernel
lemma chunk_7 : qb_nat 12 28673 (.Two 1 1 76735 0 25578) = some (.Two 3 3 43848 43843 29230) := by decide +kernel
lemma chunk_8 : qb_nat 12 32769 (.Two 3 3 43848 43843 29230) = some (.Two 1 1 98653 0 32884) := by decide +kernel
lemma chunk_9 : qb_nat 12 36865 (.Two 1 1 98653 0 32884) = some (.Two 1 1 109615 0 36538) := by decide +kernel
lemma chunk_10 : qb_nat 12 40961 (.Two 1 1 109615 0 36538) = some (.Two 3 3 60294 60292 40195) := by decide +kernel
lemma chunk_11 : qb_nat 12 45057 (.Two 3 3 60294 60292 40195) = some (.Two 1 1 131542 0 43847) := by decide +kernel
lemma chunk_12 : qb_nat 12 49153 (.Two 1 1 131542 0 43847) = some (.Two 1 1 142513 0 47504) := by decide +kernel
lemma chunk_13 : qb_nat 12 53249 (.Two 1 1 142513 0 47504) = some (.Two 1 1 153469 0 51156) := by decide +kernel
lemma chunk_14 : qb_nat 12 57345 (.Two 1 1 153469 0 51156) = some (.Two 1 1 164437 0 54812) := by decide +kernel
lemma chunk_15 : qb_nat 12 61441 (.Two 1 1 164437 0 54812) = some (.Two 1 1 175393 0 58464) := by decide +kernel

lemma q8_nat {n k k' : ℕ} {f g h : entry_nat}
    (h1 : qb_nat n k f = some g) (h2 : qb_nat n k' g = some h)
    (hk : Nat.add k (Nat.pow 2 n) = k' := by decide) :
    qb_nat (n + 1) k f = some h := by
  unfold qb_nat
  rw [h1]
  simp only [sNat_eq, hk]
  exact h2

lemma qaH_nat : qb_nat 16 1 (.Two 1 1 1 0 0) = some (.Two 1 1 175393 0 58464) := by
  have h13_0 := q8_nat chunk_0 chunk_1
  have h13_1 := q8_nat chunk_2 chunk_3
  have h13_2 := q8_nat chunk_4 chunk_5
  have h13_3 := q8_nat chunk_6 chunk_7
  have h13_4 := q8_nat chunk_8 chunk_9
  have h13_5 := q8_nat chunk_10 chunk_11
  have h13_6 := q8_nat chunk_12 chunk_13
  have h13_7 := q8_nat chunk_14 chunk_15
  have h14_0 := q8_nat h13_0 h13_1
  have h14_1 := q8_nat h13_2 h13_3
  have h14_2 := q8_nat h13_4 h13_5
  have h14_3 := q8_nat h13_6 h13_7
  have h15_0 := q8_nat h14_0 h14_1
  have h15_1 := q8_nat h14_2 h14_3
  exact q8_nat h15_0 h15_1

theorem base_structured (k : ℤ) (hk : 1 ≤ k ∧ k ≤ 65536) :
    ∃ f, Built k f ∧ bounded k f ∧ qaf Built k f := by
  exact (qc2_nat first qaH_nat).2 k (by omega)
lemma bank16 : lookup bank 16=some (.One 37 12):= by decide +kernel
theorem P16 : Built 16 (.One 37 12) :=
  lookup_spec checked_bank 16 (.One 37 12) bank16
end CheckTable
namespace Bridge
open Table
def kernel (x : pair) : Block.kernel :=
  ⟨q0 x.d,x.p,x.b,x.b + x.c + 2⟩
lemma kernel_good {s : ℤ} {x : pair} (hx : qo s x) : Block.good (kernel x):= by
  rcases hx with ⟨⟨hd0,hdk,hp0,hpd,ho,hb,hc⟩,hhalf,hc0⟩
  unfold Block.good kernel
  dsimp -failIfUnchanged
  have hP:=pow_pos hd0
  refine ⟨hP,hp0,hhalf,hb,by omega⟩
lemma gain_large {k : ℤ} {f : entry} (h : qZ k f) : k < 3 * (qad f + 1):= by
  rcases h with ⟨⟨hk,he,hwf⟩,hr⟩
  have hr1:=hr 1 (by omega) ⟨0,rfl⟩
  have hl:=Prefix.run_length hr1
  unfold Table.F Prefix.F qbn at hl
  rw [List.length_map,List.length_cons,Prefix.geometric_length] at hl
  have hlen : (Table.eval k 1 f).length ≤ 2:= by
    cases f <;> simp [Table.eval,qai]
  omega
lemma kernel_gain {s : ℤ} {x : pair} {e : ℤ} (h : qZ s (.Two x e)) :
    s < (kernel x).gain:= by
  have hg:=gain_large h
  rcases h.1 with ⟨hs,he,hx,hmass⟩
  unfold kernel qad at *
  dsimp -failIfUnchanged at *
  omega
lemma head_value {k q : ℤ} {x : pair} (hx : qaB k x) (hq : qW q) :
    qb6 (left k q x)=q3 k x:= by
  rcases qbS hx hq with ⟨a,ha⟩
  unfold q3
  rw [ha]
  cases h1 : qb6 (qk k x + 2 * a) <;> cases h2 : qb6 (qk k x)
  · rfl
  · exfalso
    rcases (qah _).mp h2 with ⟨b,hb⟩
    have hev : ZEven (qk k x + 2 * a):=⟨b + a,by linarith⟩
    have:=(qah _).mpr hev
    rw [h1] at this; contradiction
  · exfalso
    rcases (qah _).mp h1 with ⟨b,hb⟩
    have hev : ZEven (qk k x):=⟨b - a,by linarith⟩
    have:=(qah _).mpr hev
    rw [h2] at this; contradiction
  · rfl
lemma lookup_parity {k : ℤ} {x : pair} {s r : ℤ} {y : pair}
    (hx : qaB k x) (hs : qa k x s r) (hy : qo s y) :
    q3 k (qQ x s r y)=q3 s y:= by
  rcases qan hx hs hy with ⟨hnext,_⟩
  have hodd : qW 1:=⟨0,rfl⟩
  rw [← head_value hnext hodd,← qaF 1 hx hs hy]
  exact head_value hy.1 (qz hx (by omega) hodd hs).2.1
end Bridge
namespace Finite
open Table
lemma all_base {k : ℤ} {f : entry} (hk : 1 ≤ k ∧ k ≤ 65536) (hf : Built k f) :
    CheckTable.bounded k f ∧ qaf Built k f:= by
  rcases CheckTable.base_structured k hk with ⟨g,hg,hb,hr⟩
  have heq:=UniqueTable.built_unique hf g hg
  subst heq
  exact ⟨hb,hr⟩
end Finite
namespace WordArith
def qa3 (n x : ℤ) : Prop:=∃ q : ℤ,x=q0 n * q
lemma div2_zero (n : ℤ) : qa3 n 0:=⟨0,by ring⟩
lemma div2_refl (x : ℤ) : qa3 0 x:=⟨x,by simp [pow2_zero]⟩
lemma div2_add {n x y : ℤ} (hx : qa3 n x) (hy : qa3 n y) : qa3 n (x + y):= by
  rcases hx with ⟨a,rfl⟩
  rcases hy with ⟨b,rfl⟩
  exact ⟨a + b,by ring⟩
lemma qb4 {n x y : ℤ} (hx : qa3 n x) (hy : qa3 n y) : qa3 n (x - y):= by
  rcases hx with ⟨a,rfl⟩
  rcases hy with ⟨b,rfl⟩
  exact ⟨a - b,by ring⟩
lemma qa7 {n x : ℤ} (a : ℤ) (hx : qa3 n x) : qa3 n (a * x):= by
  rcases hx with ⟨b,rfl⟩
  exact ⟨a * b,by ring⟩
lemma qp {n m x : ℤ} (hm : 0 ≤ m) (hmn : m ≤ n) (hx : qa3 n x) : qa3 m x:= by
  rcases hx with ⟨a,rfl⟩
  refine ⟨q0 (n - m) * a,?_⟩
  rw [Table.pow_split hm hmn]
  ring
lemma div2_product {n m x y : ℤ} (hn : 0 ≤ n) (hm : 0 ≤ m)
    (hx : qa3 n x) (hy : qa3 m y) : qa3 (n + m) (x * y):= by
  rcases hx with ⟨a,rfl⟩
  rcases hy with ⟨b,rfl⟩
  refine ⟨a * b,?_⟩
  rw [q5 hn hm]
  ring
lemma qaa {n m x : ℤ} (hm : 0 ≤ m) (hmn : m ≤ n)
    (h : qa3 n (q0 m * x)) : qa3 (n - m) x:= by
  rcases h with ⟨a,ha⟩
  refine ⟨a,?_⟩
  rw [Table.pow_split hm hmn] at ha
  have hp:=Table.pow_pos hm
  nlinarith
def qab (x n : ℤ) : ℤ:=x / q0 n
lemma qbh {n x : ℤ} (hn : 0 ≤ n) (hx : qa3 n x) : x=q0 n * qab x n:= by
  rcases hx with ⟨a,rfl⟩
  unfold qab
  have hp:=Table.pow_pos hn
  rw [Int.mul_ediv_cancel_left _ (by omega)]
lemma qat {n x : ℤ} (hn : 1 ≤ n) (ho : qW x) : ¬ qa3 n x:= by
  intro hd
  rcases ho with ⟨a,ha⟩
  rcases qp (by omega : 0 ≤ (1 : ℤ)) hn hd with ⟨b,hb⟩
  rw [pow2_one] at hb
  omega
def ctz_nat : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    if x % 2 = 0 then ctz_nat fuel (x / 2) + 1 else 0
lemma ctz_nat_eq_q4 (fuel : ℕ) (x : ℤ) :
    ((ctz_nat fuel x.natAbs : ℕ) : ℤ) = (q4 fuel x).1 := by
  induction fuel generalizing x with
  | zero => rfl
  | succ fuel ih =>
    unfold ctz_nat q4
    by_cases hmod : x % 2 = 0
    · have hnat : x.natAbs % 2 = 0 := by omega
      have hdiv : (x / 2).natAbs = x.natAbs / 2 := by omega
      rw [if_pos hmod, if_pos hnat, ← hdiv]
      push_cast
      rw [ih (x / 2)]
    · have hnat : x.natAbs % 2 ≠ 0 := by omega
      rw [if_neg hmod, if_neg hnat]
      rfl
lemma mod_two_mul_mod_two (x m : ℕ) : (x % (2 * m)) % 2 = x % 2 := by
  have h := Nat.div_add_mod x (2 * m)
  have h2 : 2 * m * (x / (2 * m)) = 2 * (m * (x / (2 * m))) := by ring
  omega
lemma mod_two_mul_div_two (x m : ℕ) : (x % (2 * m)) / 2 = (x / 2) % m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 := Nat.div_add_mod x (2 * m)
    have h2 := Nat.mod_lt x (by omega : 0 < 2 * m)
    have h3 : x / 2 = m * (x / (2 * m)) + (x % (2 * m)) / 2 := by
      have : 2 * m * (x / (2 * m)) = 2 * (m * (x / (2 * m))) := by ring
      omega
    have hlt : (x % (2 * m)) / 2 < m := by omega
    rw [h3, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt]
lemma div_two_mod_eq_zero (x m : ℕ) (hx : x % 2 = 0) :
    (x / 2) % m = 0 ↔ x % (2 * m) = 0 := by
  have hm2 := mod_two_mul_mod_two x m
  rw [← mod_two_mul_div_two]
  omega
lemma ctz_nat_step_k (k : ℕ) :
    ∀ (fuel x : ℕ),
      ctz_nat (k + fuel) x =
        if x % (2 ^ k) = 0 then ctz_nat fuel (x / (2 ^ k)) + k
        else ctz_nat k (x % (2 ^ k)) := by
  induction k with
  | zero =>
    intro fuel x
    simp [Nat.mod_one]
  | succ k ih =>
    intro fuel x
    conv_lhs => rw [Nat.succ_add, ctz_nat]
    have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hx2 : x % 2 = 0
    · rw [if_pos hx2, ih fuel (x / 2)]
      have hdiv_mod : (x / 2) % (2 ^ k) = 0 ↔ x % (2 ^ (k + 1)) = 0 := by
        rw [hpow]; exact div_two_mod_eq_zero x (2 ^ k) hx2
      by_cases hxk : (x / 2) % (2 ^ k) = 0
      · have hxk' : x % (2 ^ (k + 1)) = 0 := hdiv_mod.mp hxk
        rw [if_pos hxk, if_pos hxk']
        have hdiv2 : (x / 2) / (2 ^ k) = x / (2 ^ (k + 1)) := by
          rw [hpow, Nat.div_div_eq_div_mul]
        rw [hdiv2]
        omega
      · have hxk' : x % (2 ^ (k + 1)) ≠ 0 := fun h => hxk (hdiv_mod.mpr h)
        rw [if_neg hxk, if_neg hxk']
        conv_rhs => unfold ctz_nat
        have hmod2 : (x % (2 ^ (k + 1))) % 2 = 0 := by
          rw [hpow, mod_two_mul_mod_two, hx2]
        have hmod_div : (x % (2 ^ (k + 1))) / 2 = (x / 2) % (2 ^ k) := by
          rw [hpow, mod_two_mul_div_two]
        rw [if_pos hmod2, hmod_div]
    · have hmod2 : (x % (2 ^ (k + 1))) % 2 ≠ 0 := by
        rw [hpow, mod_two_mul_mod_two]; exact hx2
      have hxk' : x % (2 ^ (k + 1)) ≠ 0 := by omega
      rw [if_neg hx2, if_neg hxk']
      conv_rhs => unfold ctz_nat
      rw [if_neg hmod2]
def ctz_0 : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x =>
    if Nat.beq (Nat.mod x 2) 0 then Nat.add (ctz_0 fuel (Nat.div x 2)) 1 else 0
lemma ctz_0_eq : ∀ fuel x, ctz_0 fuel x = ctz_nat fuel x
  | 0, _ => rfl
  | fuel + 1, x => by
    unfold ctz_0 ctz_nat
    by_cases h : x % 2 = 0
    · have hb : Nat.beq (Nat.mod x 2) 0 = true := Nat.beq_eq.mpr h
      rw [hb, if_pos rfl, if_pos h, ctz_0_eq fuel (Nat.div x 2)]
      rfl
    · have hb : Nat.beq (Nat.mod x 2) 0 = false := by
        rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq]; exact h
      rw [hb, if_neg Bool.false_ne_true, if_neg h]
def ctz_split (k pk : ℕ) (f_low f_high : ℕ → ℕ → ℕ) (fuel x : ℕ) : ℕ :=
  match Nat.ble fuel k with
  | true => f_low fuel x
  | false =>
    sNat (Nat.mod x pk) fun r =>
    match Nat.beq r 0 with
    | true => Nat.add (f_high (Nat.sub fuel k) (Nat.div x pk)) k
    | false => f_low k r
lemma ctz_split_eq (k pk : ℕ) (f_low f_high : ℕ → ℕ → ℕ) (hpk : pk = 2 ^ k)
    (hlow : ∀ fuel x, f_low fuel x = ctz_nat fuel x)
    (hhigh : ∀ fuel x, f_high fuel x = ctz_nat fuel x) (fuel x : ℕ) :
    ctz_split k pk f_low f_high fuel x = ctz_nat fuel x := by
  unfold ctz_split
  rw [hpk]
  simp only [sNat_eq]
  cases hle : Nat.ble fuel k
  · have hle' : ¬ fuel ≤ k := by
      intro h; have := Nat.ble_eq.mpr h; rw [hle] at this; contradiction
    have hfuel : fuel = k + (fuel - k) := by omega
    try dsimp -failIfUnchanged only
    cases hmod : Nat.beq (Nat.mod x (2 ^ k)) 0
    · have hmod' : ¬ x % 2 ^ k = 0 := by
        intro h
        have h1 : Nat.beq (Nat.mod x (2 ^ k)) 0 = true := Nat.beq_eq.mpr h
        rw [hmod] at h1; contradiction
      try dsimp -failIfUnchanged only
      rw [hlow]
      conv_rhs => rw [hfuel, ctz_nat_step_k k (fuel - k) x, if_neg hmod']
      rfl
    · have hmod' : x % 2 ^ k = 0 := Nat.beq_eq.mp hmod
      try dsimp -failIfUnchanged only
      rw [hhigh]
      conv_rhs => rw [hfuel, ctz_nat_step_k k (fuel - k) x, if_pos hmod']
      rfl
  · try dsimp -failIfUnchanged only
    rw [hlow]
def ctz_1 : ℕ → ℕ → ℕ := ctz_split 1 2 ctz_0 ctz_0
lemma ctz_1_eq : ∀ fuel x, ctz_1 fuel x = ctz_nat fuel x :=
  ctz_split_eq 1 2 ctz_0 ctz_0 rfl ctz_0_eq ctz_0_eq
def ctz_2 : ℕ → ℕ → ℕ := ctz_split 2 4 ctz_1 ctz_1
lemma ctz_2_eq : ∀ fuel x, ctz_2 fuel x = ctz_nat fuel x :=
  ctz_split_eq 2 4 ctz_1 ctz_1 rfl ctz_1_eq ctz_1_eq
def ctz_4 : ℕ → ℕ → ℕ := ctz_split 4 16 ctz_2 ctz_2
lemma ctz_4_eq : ∀ fuel x, ctz_4 fuel x = ctz_nat fuel x :=
  ctz_split_eq 4 16 ctz_2 ctz_2 rfl ctz_2_eq ctz_2_eq
def ctz_8 : ℕ → ℕ → ℕ := ctz_split 8 256 ctz_4 ctz_4
lemma ctz_8_eq : ∀ fuel x, ctz_8 fuel x = ctz_nat fuel x :=
  ctz_split_eq 8 256 ctz_4 ctz_4 rfl ctz_4_eq ctz_4_eq
def ctz_16 : ℕ → ℕ → ℕ := ctz_split 16 65536 ctz_8 ctz_8
lemma ctz_16_eq : ∀ fuel x, ctz_16 fuel x = ctz_nat fuel x :=
  ctz_split_eq 16 65536 ctz_8 ctz_8 rfl ctz_8_eq ctz_8_eq
def ctz_top_256 : ℕ → ℕ → ℕ := ctz_split 256 (Nat.pow 2 256) ctz_16 ctz_16
lemma ctz_top_256_eq : ∀ fuel x, ctz_top_256 fuel x = ctz_nat fuel x :=
  ctz_split_eq 256 (Nat.pow 2 256) ctz_16 ctz_16 rfl ctz_16_eq ctz_16_eq
def ctz_top_64 : ℕ → ℕ → ℕ := ctz_split 64 (Nat.pow 2 64) ctz_16 ctz_top_256
lemma ctz_top_64_eq : ∀ fuel x, ctz_top_64 fuel x = ctz_nat fuel x :=
  ctz_split_eq 64 (Nat.pow 2 64) ctz_16 ctz_top_256 rfl ctz_16_eq ctz_top_256_eq
def ctz_top_12 : ℕ → ℕ → ℕ := ctz_split 12 4096 ctz_4 ctz_top_64
lemma ctz_top_12_eq : ∀ fuel x, ctz_top_12 fuel x = ctz_nat fuel x :=
  ctz_split_eq 12 4096 ctz_4 ctz_top_64 rfl ctz_4_eq ctz_top_64_eq
def ctz_fast : ℕ → ℕ → ℕ := ctz_split 4 16 ctz_2 ctz_top_12
lemma ctz_fast_eq (fuel x : ℕ) : ctz_fast fuel x = ctz_nat fuel x :=
  ctz_split_eq 4 16 ctz_2 ctz_top_12 rfl ctz_2_eq ctz_top_12_eq fuel x
def qq (n x : ℤ) : ℤ :=
  if Nat.beq x.natAbs 0 then n else Int.ofNat (ctz_fast n.toNat x.natAbs)
lemma qq_eq_orig (n x : ℤ) :
    qq n x = (if x = 0 then n else (q4 n.toNat x).1) := by
  unfold qq
  by_cases hx : x = 0
  · subst hx; simp
  · have hna : Nat.beq x.natAbs 0 = false := by
      rw [Bool.eq_false_iff, ne_eq, Nat.beq_eq, Int.natAbs_eq_zero]; exact hx
    rw [hna, if_neg Bool.false_ne_true, if_neg hx]
    change ((ctz_fast n.toNat x.natAbs : ℕ) : ℤ) = (q4 n.toNat x).1
    rw [ctz_fast_eq, ctz_nat_eq_q4]
lemma qal {n : ℤ} (x : ℤ) (hn : 0 ≤ n) :
    (0 ≤ qq n x ∧ qq n x ≤ n) ∧
    ∃ q,x=q0 (qq n x) * q ∧ (qq n x < n → qW q):= by
  rw [qq_eq_orig]
  split_ifs with hx
  · subst hx
    exact ⟨⟨hn,le_refl n⟩,0,by ring,fun h => by omega⟩
  · rcases qaw n.toNat x with ⟨h0,h1,heq,hodd⟩
    rw [Int.toNat_of_nonneg hn] at h1 hodd
    exact ⟨⟨h0,h1⟩,(q4 n.toNat x).2,heq,hodd⟩
lemma qam {n : ℤ} (x : ℤ) (hn : 0 ≤ n) : qa3 (qq n x) x:= by
  rcases (qal x hn).2 with ⟨q,hq,_⟩
  exact ⟨q,hq⟩
lemma qL {n : ℤ} (x : ℤ) (hn : 0 ≤ n) : 0 ≤ qq n x ∧ qq n x ≤ n :=
  (qal x hn).1
lemma qbO {n x : ℤ} (hn : 0 ≤ n) (hlt : qq n x < n) :
    qW (qab x (qq n x)):= by
  rcases qal x hn with ⟨⟨h0,_⟩,q,hx,hodd⟩
  have he:=qbh h0 (qam x hn)
  have hp:=Table.pow_pos h0
  have hq : qab x (qq n x)=q:= by nlinarith
  rw [hq]
  exact hodd hlt
lemma div2_order {n x : ℤ} (hn : 0 ≤ n) : qa3 n x ↔ qq n x=n:= by
  rcases qal x hn with ⟨⟨h0,h1⟩,q,hx,hodd⟩
  constructor
  · intro h
    by_contra hne
    have hlt : qq n x < n:= by omega
    rw [hx] at h
    have hdiv:=qaa h0 h1 h
    exact qat (by omega : 1 ≤ n - qq n x) (hodd hlt) hdiv
  · intro h
    rw [← h]
    exact qam x hn
def qbg (n x : ℤ) : Bool :=
  match n with
  | Int.ofNat 0 => true
  | Int.ofNat (m + 1) => Nat.beq (x.natAbs % (2 ^ (m + 1))) 0
  | Int.negSucc _ => false
lemma qbs {n x : ℤ} (hn : 0 ≤ n) : qbg n x=true ↔ qa3 n x:= by
  cases n with
  | negSucc m => omega
  | ofNat m =>
    have hq0 : q0 (Int.ofNat m) = Int.ofNat (2 ^ m) := rfl
    have heq : qbg (Int.ofNat m) x = true ↔ (2 ^ m) ∣ x.natAbs := by
      cases m with
      | zero => simp [qbg]
      | succ m =>
        simp only [qbg, Nat.beq_eq, Nat.dvd_iff_mod_eq_zero]
    rw [heq, ← Int.ofNat_dvd_left]
    unfold qa3
    rw [hq0]
    rfl
lemma qbw {n x m q : ℤ} (hn : 0 ≤ n) (hm : 0 ≤ m) (hq : qW q)
    (h : qa3 n (x - q0 m * q)) :
    (qq n x < n → m=qq n x) ∧ (qq n x=n → n ≤ m):= by
  rcases qal x hn with ⟨⟨hv0,hvn⟩,a,ha,ho⟩
  have hsame : qq n x < n → m=qq n x:= by
    intro hvlt
    rcases lt_trichotomy m (qq n x) with hlt | heq | hgt
    · have h1 : qa3 (m + 1) x:=qp (by omega) (by omega) (qam x hn)
      have h2 : qa3 (m + 1) (x - q0 m * q):=qp (by omega) (by omega) h
      have h3 : qa3 (m + 1) (q0 m * q):= by
        have hsub:=qb4 h1 h2
        have heq_sub : x - (x - q0 m * q)=q0 m * q:= by ring
        rwa [heq_sub] at hsub
      have h4:=qaa hm (by omega) h3
      exfalso
      exact qat (by omega : 1 ≤ m + 1 - m) hq h4
    · exact heq
    · have h1 : qa3 (qq n x + 1) (q0 m * q) :=
        qp (by omega) (by omega) ⟨q,rfl⟩
      have h2 : qa3 (qq n x + 1) (x - q0 m * q) :=
        qp (by omega) (by omega) h
      have h3 : qa3 (qq n x + 1) (q0 (qq n x) * a):= by
        have hsum:=div2_add h2 h1
        have heq_sum : x - q0 m * q + q0 m * q=q0 (qq n x) * a:= by linarith
        rwa [heq_sum] at hsum
      have h4:=qaa hv0 (by omega) h3
      exfalso
      exact qat (by omega : 1 ≤ qq n x + 1 - qq n x) (ho hvlt) h4
  refine ⟨hsame,?_⟩
  intro hv0
  by_contra hlt
  have h1 : qa3 n x:=(div2_order hn).mpr hv0
  have h2 : qa3 n (q0 m * q):= by
    have hsub:=qb4 h1 h
    have heq_sub : x - (x - q0 m * q)=q0 m * q:= by ring
    rwa [heq_sub] at hsub
  have h3:=qaa hm (by omega) h2
  exact qat (by omega : 1 ≤ n - m) hq h3
end WordArith
namespace WordRelation
open WordArith
structure relation where
  a : ℤ
  q : ℤ
  c : ℤ
  n : ℤ
  sa : ℤ
  sb : ℤ
  sn : ℤ
  deriving DecidableEq,Repr
def qbd (z : relation) (S U : ℤ) : Prop :=
  0 ≤ z.n ∧ 0 ≤ z.sn ∧ qW z.q ∧ qW z.sa ∧
  qa3 z.n (z.q * U - z.a * S - z.c) ∧ qa3 z.sn (z.sa * S - z.sb)
def choose (z : relation) (A Q C N a0 b0 p0 : ℤ) : relation :=
  if decide (z.n < N) then ⟨A,Q,C,N,a0,b0,p0⟩
  else ⟨z.a,z.q,z.c,z.n,a0,b0,p0⟩
lemma qaU (z : relation) (A Q C N a0 b0 p0 S U : ℤ)
    (hz : qbd z S U) (hN : 0 ≤ N) (hQ : qW Q)
    (hR : qa3 N (Q * U - A * S - C)) (hp0 : 0 ≤ p0) (ha0 : qW a0)
    (hS : qa3 p0 (a0 * S - b0)) :
    qbd (choose z A Q C N a0 b0 p0) S U:= by
  rcases hz with ⟨hn,hp,hq,ha,hr,hs⟩
  unfold choose
  split_ifs <;> exact ⟨by assumption,hp0,by assumption,ha0,by assumption,hS⟩
lemma eliminate (z : relation) (A Q C N S U : ℤ)
    (hz : qbd z S U) (hN : 0 ≤ N) (hnew : qa3 N (Q * U - A * S - C)) :
    qa3 (min N z.n) ((Q * z.a - z.q * A) * S - (z.q * C - Q * z.c)):= by
  rcases hz with ⟨hn,hp,hq,ha,hr,hs⟩
  have hr' : qa3 (min N z.n) (z.q * U - z.a * S - z.c) :=
    qp (by omega) (by omega) hr
  have hnew' : qa3 (min N z.n) (Q * U - A * S - C) :=
    qp (by omega) (by omega) hnew
  have h:=qb4 (qa7 z.q hnew') (qa7 Q hr')
  have heq : z.q * (Q * U - A * S - C) - Q * (z.q * U - z.a * S - z.c) =
      (Q * z.a - z.q * A) * S - (z.q * C - Q * z.c):= by ring
  rwa [heq] at h
lemma qaP (m A B S : ℤ) (hm : 0 ≤ m) (h : qa3 m (A * S - B)) :
    qa3 (qq m A) B:= by
  have hv:=qL A hm
  have hA:=qa7 S (qam A hm)
  have hB:=qp hv.1 hv.2 h
  have hsub:=qb4 hA hB
  have heq : S * A - (A * S - B)=B:= by ring
  rwa [heq] at hsub
lemma qb3 (m A B S : ℤ) (hm : 0 ≤ m) (h : qa3 m (A * S - B)) :
    qa3 (m - qq m A) (qab A (qq m A) * S - qab B (qq m A)):= by
  have hv:=qL A hm
  have hA:=qbh hv.1 (qam A hm)
  have hB:=qbh hv.1 (qaP m A B S hm h)
  apply qaa hv.1 hv.2
  have heq : q0 (qq m A) * (qab A (qq m A) * S - qab B (qq m A))=A * S - B:= by
    have hA' := congr_arg (fun z => S * z) hA.symm
    dsimp -failIfUnchanged only at hA'
    linarith
  rwa [heq]
lemma compatible (m a0 b0 p0 a1 b1 S : ℤ) (hm : 0 ≤ m) (hp : 0 ≤ p0)
    (h0 : qa3 m (a0 * S - b0)) (h1 : qa3 p0 (a1 * S - b1)) :
    qa3 (min m p0) (a0 * b1 - a1 * b0):= by
  have h0':=qp (by omega) (by omega : min m p0 ≤ m) h0
  have h1':=qp (by omega) (by omega : min m p0 ≤ p0) h1
  have h:=qb4 (qa7 a1 h0') (qa7 a0 h1')
  have heq : a1 * (a0 * S - b0) - a0 * (a1 * S - b1)=a0 * b1 - a1 * b0:= by ring
  rwa [heq] at h
def qaC (r : relation) (f : relation → Option relation) : Option relation :=
  q2 r.a fun a =>
  q2 r.q fun q =>
  q2 r.c fun c =>
  q2 r.n fun n =>
  q2 r.sa fun sa =>
  q2 r.sb fun sb =>
  q2 r.sn fun sn =>
  f ⟨a,q,c,n,sa,sb,sn⟩
@[simp] lemma strictRel_eq (r : relation) (f : relation → Option relation) :
    qaC r f=f r:= by
  cases r; simp [qaC]
def qbR (z : relation) (A Q C N : ℤ) : Option relation :=
  q2 (min N z.n) fun m =>
  q2 (Q * z.a - z.q * A) fun aa =>
  q2 (z.q * C - Q * z.c) fun bb =>
  q2 (qq m aa) fun v =>
  if qbg v bb then
    if decide (v < m) then
      q2 (qab aa v) fun ca =>
      q2 (qab bb v) fun cb =>
      q2 (m - v) fun cp =>
      if qbg (min cp z.sn) (ca * z.sb - z.sa * cb) then
        if decide (z.sn < cp) then qaC (choose z A Q C N ca cb cp) some
        else qaC (choose z A Q C N z.sa z.sb z.sn) some
      else none
    else qaC (choose z A Q C N z.sa z.sb z.sn) some
  else none
lemma qce (z : relation) (A Q C N S U : ℤ)
    (hz : qbd z S U) (hN : 0 ≤ N) (hQ : qW Q)
    (hnew : qa3 N (Q * U - A * S - C)) :
    ∃ z',qbR z A Q C N=some z' ∧ qbd z' S U:= by
  have helim:=eliminate z A Q C N S U hz hN hnew
  rcases hz with ⟨hn,hp,hq,ha,hU,hS⟩
  have hwhole : qbd z S U:=⟨hn,hp,hq,ha,hU,hS⟩
  have hm : 0 ≤ min N z.n:= by omega
  have hv:=qL (Q * z.a - z.q * A) hm
  have hB:=qaP (min N z.n) (Q * z.a - z.q * A) (z.q * C - Q * z.c) S hm helim
  have hdiv:=qb3 (min N z.n) (Q * z.a - z.q * A) (z.q * C - Q * z.c) S hm helim
  unfold qbR
  simp only [strictInt_eq,strictRel_eq]
  try dsimp -failIfUnchanged only
  have htest : qbg (qq (min N z.n) (Q * z.a - z.q * A)) (z.q * C - Q * z.c)=true :=
    (qbs hv.1).mpr hB
  rw [htest,if_pos rfl]
  split_ifs with hlt hctest hsn
  · have hlt' : qq (min N z.n) (Q * z.a - z.q * A) < min N z.n:=of_decide_eq_true hlt
    have hO:=qbO hm hlt'
    refine ⟨_,rfl,qaU z A Q C N _ _ _ S U hwhole hN hQ hnew (by omega) hO hdiv⟩
  · refine ⟨_,rfl,qaU z A Q C N _ _ _ S U hwhole hN hQ hnew hp ha hS⟩
  · exfalso
    have hlt' : qq (min N z.n) (Q * z.a - z.q * A) < min N z.n:=of_decide_eq_true hlt
    have hC:=compatible (min N z.n - qq (min N z.n) (Q * z.a - z.q * A))
      (qab (Q * z.a - z.q * A) (qq (min N z.n) (Q * z.a - z.q * A)))
      (qab (z.q * C - Q * z.c) (qq (min N z.n) (Q * z.a - z.q * A)))
      z.sn z.sa z.sb S (by omega) hp hdiv hS
    have hC_true : qbg (min (min N z.n - qq (min N z.n) (Q * z.a - z.q * A)) z.sn)
      (qab (Q * z.a - z.q * A) (qq (min N z.n) (Q * z.a - z.q * A)) * z.sb -
       z.sa * qab (z.q * C - Q * z.c) (qq (min N z.n) (Q * z.a - z.q * A)))=true :=
      (qbs (by omega)).mpr hC
    exact hctest hC_true
  · refine ⟨_,rfl,qaU z A Q C N _ _ _ S U hwhole hN hQ hnew hp ha hS⟩
def optional (z : Option relation) (S U : ℤ) : Prop :=
  match z with
  | none => True
  | some z => qbd z S U
def add (z : Option relation) (A Q C N : ℤ) : Option relation :=
  match z with
  | none => some ⟨A,Q,C,N,1,0,0⟩
  | some z => qbR z A Q C N
lemma add_spec (z : Option relation) (A Q C N S U : ℤ)
    (hz : optional z S U) (hN : 0 ≤ N) (hQ : qW Q)
    (hnew : qa3 N (Q * U - A * S - C)) :
    ∃ z',add z A Q C N=some z' ∧ qbd z' S U:= by
  cases z with
  | none =>
    refine ⟨⟨A,Q,C,N,1,0,0⟩,rfl,?_⟩
    unfold qbd
    try dsimp -failIfUnchanged only
    refine ⟨hN,by omega,hQ,⟨0,rfl⟩,hnew,?_⟩
    simpa using! div2_refl S
  | some z =>
    exact qce z A Q C N S U hz hN hQ hnew
def qb2 (z : relation) (A Q : ℤ) : ℤ:=Q * z.a - z.q * A
def elim_b (z : relation) (B Q : ℤ) : ℤ:=z.q * B - Q * z.c
def qa2 (z : relation) (A Q : ℤ) : ℤ:=min z.n (z.sn + qq z.n (qb2 z A Q))
def qa6 (z : relation) (A B Q : ℤ) : ℤ:=z.sa * elim_b z B Q - qb2 z A Q * z.sb
lemma qaZ (z : relation) (A B Q S U H : ℤ)
    (hz : qbd z S U) (hH : H=A * S - Q * U + B) :
    qa3 (qa2 z A Q) (qa6 z A B Q - z.sa * z.q * H):= by
  rcases hz with ⟨hn,hp,hq,ha,hU,hS⟩
  have hv:=qL (qb2 z A Q) hn
  have hmul:=div2_product hp hv.1 hS (qam (qb2 z A Q) hn)
  have hcut0 : 0 ≤ qa2 z A Q:= by unfold qa2; omega
  have hmul':=qp hcut0 (by unfold qa2; omega) hmul
  have hscaled:=qa7 (z.sa * Q) hU
  have hscaled':=qp hcut0 (by unfold qa2; omega) hscaled
  have hsum:=div2_add hmul' hscaled'
  unfold qa6
  have heq : (z.sa * S - z.sb) * qb2 z A Q + z.sa * Q * (z.q * U - z.a * S - z.c) =
      z.sa * elim_b z B Q - qb2 z A Q * z.sb - z.sa * z.q * H:= by
    unfold qb2 elim_b
    rw [hH]
    ring
  rwa [heq] at hsum
lemma pruning_spec (z : relation) (A B Q S U D s t : ℤ)
    (hz : qbd z S U) (hD : 0 ≤ D) (hs : 0 ≤ s)
    (hH : A * S - Q * U + B=q0 (D + s) * (2 * t + 1)) :
    let bound:=qa2 z A Q
    let v:=qq bound (qa6 z A B Q)
    (v < bound → s=v - D) ∧ (v=bound → bound - D ≤ s):= by
  have hdiv:=qaZ z A B Q S U (q0 (D + s) * (2 * t + 1)) hz hH.symm
  rcases hz with ⟨hn,hp,hQ,ha,hU,hS⟩
  have horder:=qL (qb2 z A Q) hn
  have hbound : 0 ≤ qa2 z A Q:= by unfold qa2; omega
  have hodd : qW (z.sa * z.q * (2 * t + 1)):= by
    rcases hQ with ⟨u,hu⟩
    rcases ha with ⟨v,hv⟩
    refine ⟨2 * v * u * (2 * t + 1) + (v + u) * (2 * t + 1) + t,?_⟩
    rw [hu,hv]; ring
  have heq : qa6 z A B Q - z.sa * z.q * (q0 (D + s) * (2 * t + 1)) =
      qa6 z A B Q - q0 (D + s) * (z.sa * z.q * (2 * t + 1)):= by ring
  rw [heq] at hdiv
  rcases qbw hbound (by omega : 0 ≤ D + s) hodd hdiv with ⟨he,hle⟩
  try dsimp -failIfUnchanged only
  refine ⟨fun h => by have:=he h; omega,fun h => by have:=hle h; omega⟩
end WordRelation
namespace WordLibrary
open Table
structure kernel where
  index : ℤ
  pair : Table.pair
  deriving DecidableEq,Repr
def gain (k : kernel) : ℤ:=k.pair.b + k.pair.c + 2
def continuing (k : kernel) : Prop :=
  ∃ e,Built k.index (.Two k.pair e) ∧ 1 ≤ k.index ∧ q3 k.index k.pair=false
def qV : ℕ → ℤ → entry → Option (List entry)
  | 0,_,f => some [f]
  | n + 1,k,f =>
    match CheckTable.advance (CheckTable.lookup CheckTable.bank) k f with
    | some g =>
      match qV n (k + 1) g with
      | some xs => some (f :: xs)
      | none => none
    | none => none
lemma qbY (n : ℕ) (k : ℤ) (f : entry) (xs : List entry)
    (hf : Built k f) (hb : qV n k f=some xs) :
    xs.length=n + 1 ∧
    ∀ (i : ℕ) (g : entry),CheckTable.nth_entry xs i=some g → Built (k + (i : ℤ)) g:= by
  induction n generalizing k f xs with
  | zero =>
    unfold qV at hb
    injection hb with h; subst h
    refine ⟨rfl,?_⟩
    intro i g hget
    cases i with
    | zero =>
      unfold CheckTable.nth_entry at hget
      injection hget with h; subst h
      simpa using! hf
    | succ i =>
      cases i <;> contradiction
  | succ n ih =>
    unfold qV at hb
    cases hadv : CheckTable.advance (CheckTable.lookup CheckTable.bank) k f with
    | none => rw [hadv] at hb; contradiction
    | some g =>
      rw [hadv] at hb
      try dsimp -failIfUnchanged only at hb
      cases hrest : qV n (k + 1) g with
      | none => rw [hrest] at hb; contradiction
      | some rest =>
        rw [hrest] at hb
        try dsimp -failIfUnchanged only at hb
        injection hb with h; subst h
        have hg : Built (k + 1) g :=
          CheckTable.advance_spec (CheckTable.lookup_spec CheckTable.checked_bank) hf hadv
        rcases ih (k + 1) g rest hg hrest with ⟨hlen,hok⟩
        refine ⟨by simp [hlen],?_⟩
        intro i h hget
        cases i with
        | zero =>
          unfold CheckTable.nth_entry at hget
          injection hget with heq; subst heq
          simpa using! hf
        | succ i =>
          unfold CheckTable.nth_entry at hget
          have hi:=hok i h hget
          have heq : k + 1 + (i : ℤ)=k + ((i + 1 : ℕ) : ℤ):= by push_cast; ring
          rwa [heq] at hi
def bank_opt : Option (List entry):=qV 2048 0 (.One 1 0)
def bank : List entry:=bank_opt.getD []
lemma bank_opt_some : bank_opt.isSome=true:= by decide +kernel
lemma qaA {α : Type*} {o : Option α} (d : α) (h : o.isSome=true) :
    o=some (o.getD d):= by
  cases o with
  | none => contradiction
  | some xs => rfl
lemma qaJ : bank_opt=some bank :=
  qaA [] bank_opt_some
lemma qaq (xs : List entry)
    (hb : qV 2048 0 (.One 1 0)=some xs) :
    xs.length=2049 ∧ CheckTable.bank_ok xs:= by
  rcases qbY 2048 0 (.One 1 0) xs Built.built_root hb with ⟨hlen,hok⟩
  refine ⟨hlen,fun i f hget => ?_⟩
  simpa using! hok i f hget
lemma bank_valid : bank.length=2049 ∧ CheckTable.bank_ok bank :=
  qaq bank qaJ
lemma qc8 {xs : List entry} {i : ℕ} (h : CheckTable.nth_entry xs i=none) :
    xs.length ≤ i:= by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
    cases i with
    | zero => contradiction
    | succ i =>
      simp only [List.length_cons]
      have:=ih h
      omega
def qaI (k : ℤ) : List entry → List kernel
  | [] => []
  | f :: r =>
    let rest:=qaI (k + 1) r
    match f with
    | .One _ _ => rest
    | .Two x _ =>
      if decide (1 ≤ k) then
        if q3 k x then rest else ⟨k,x⟩ :: rest
      else rest
lemma collect_tail (k : ℤ) (f : entry) (xs : List entry) (z : kernel)
    (hz : z ∈ qaI (k + 1) xs) : z ∈ qaI k (f :: xs):= by
  cases f with
  | One _ _ => exact hz
  | Two x _ =>
    unfold qaI
    try dsimp -failIfUnchanged only
    split_ifs <;> simp [hz]
lemma qbB (k : ℤ) (xs : List entry) (i : ℕ) (x : Table.pair) (e : ℤ)
    (hget : CheckTable.nth_entry xs i=some (.Two x e))
    (hk : 1 ≤ k + (i : ℤ))
    (he : q3 (k + (i : ℤ)) x=false) :
    ⟨k + (i : ℤ),x⟩ ∈ qaI k xs:= by
  induction xs generalizing k i with
  | nil => contradiction
  | cons f xs ih =>
    cases i with
    | zero =>
      unfold CheckTable.nth_entry at hget
      injection hget with hf; subst hf
      simp only [Nat.cast_zero,add_zero] at hk he ⊢
      unfold qaI
      try dsimp -failIfUnchanged only
      rw [if_pos (decide_eq_true hk),he]
      simp
    | succ i =>
      unfold CheckTable.nth_entry at hget
      apply collect_tail
      have heq : k + ((i + 1 : ℕ) : ℤ)=(k + 1) + (i : ℤ):= by push_cast; ring
      rw [heq] at hk he ⊢
      exact ih (k + 1) i hget hk he
lemma qap (xs : List entry)
    (hlen : xs.length=2049) (hbank : CheckTable.bank_ok xs)
    (k : kernel) (hk : continuing k) (hmax : k.index ≤ 2048) :
    k ∈ qaI 0 xs:= by
  rcases k with ⟨s,x⟩
  rcases hk with ⟨e,hb,hs,he⟩
  dsimp -failIfUnchanged at hb hs he hmax
  have hs0 : 0 ≤ s:= by omega
  cases hg : CheckTable.nth_entry xs s.toNat with
  | none =>
    have hle:=qc8 hg
    omega
  | some g =>
    have hbuilt:=hbank s.toNat g hg
    rw [Int.toNat_of_nonneg hs0] at hbuilt
    have heq:=UniqueTable.built_unique hb g hbuilt
    subst heq
    have hs_eq : s=0 + (s.toNat : ℤ):= by omega
    rw [hs_eq]
    apply qbB 0 xs s.toNat x e hg (by omega)
    rwa [← hs_eq]
def library : List kernel:=qaI 0 bank
theorem qby (k : kernel) (hk : continuing k) (hmax : k.index ≤ 2048) :
    k ∈ library :=
  qap bank bank_valid.1 bank_valid.2 k hk hmax
def lib_0a : List kernel:=[
  ⟨5,⟨1,1,7,0⟩⟩,⟨8,⟨1,1,13,0⟩⟩,⟨12,⟨1,1,25,0⟩⟩,⟨14,⟨1,1,31,0⟩⟩,⟨17,⟨1,1,37,0⟩⟩,⟨22,⟨1,1,49,0⟩⟩,
  ⟨24,⟨1,1,55,0⟩⟩,⟨27,⟨1,1,61,0⟩⟩,⟨32,⟨1,1,79,0⟩⟩,⟨35,⟨1,1,85,0⟩⟩,⟨40,⟨1,1,97,0⟩⟩,⟨42,⟨1,1,103,0⟩⟩,
  ⟨45,⟨1,1,109,0⟩⟩,⟨49,⟨1,1,121,0⟩⟩,⟨51,⟨1,1,127,0⟩⟩,⟨54,⟨1,1,133,0⟩⟩,⟨59,⟨1,1,145,0⟩⟩,⟨61,⟨1,1,151,0⟩⟩,
  ⟨64,⟨1,1,157,0⟩⟩
]
def lib_0b : List kernel:=[
  ⟨65,⟨3,3,87,79⟩⟩
]
def lib_0c : List kernel:=[
  ⟨68,⟨1,1,175,0⟩⟩,⟨71,⟨1,1,181,0⟩⟩,⟨76,⟨1,1,193,0⟩⟩,⟨78,⟨1,1,199,0⟩⟩,
  ⟨81,⟨1,1,205,0⟩⟩,⟨85,⟨1,1,217,0⟩⟩,⟨87,⟨1,1,223,0⟩⟩,⟨90,⟨1,1,229,0⟩⟩,⟨95,⟨1,1,241,0⟩⟩,⟨97,⟨1,1,247,0⟩⟩,
  ⟨100,⟨1,1,253,0⟩⟩,⟨101,⟨3,3,141,127⟩⟩,⟨106,⟨1,1,277,0⟩⟩,⟨111,⟨1,1,289,0⟩⟩,⟨113,⟨1,1,295,0⟩⟩,⟨116,⟨1,1,301,0⟩⟩,
  ⟨120,⟨1,1,313,0⟩⟩,⟨122,⟨1,1,319,0⟩⟩,⟨125,⟨1,1,325,0⟩⟩,⟨130,⟨1,1,337,0⟩⟩,⟨132,⟨1,1,343,0⟩⟩
]
def lib_0 : List kernel:=lib_0a ++ lib_0b ++ lib_0c
def lib_1 : List kernel:=[
  ⟨135,⟨1,1,349,0⟩⟩,⟨136,⟨3,3,183,175⟩⟩,⟨139,⟨1,1,367,0⟩⟩,⟨142,⟨1,1,373,0⟩⟩,⟨147,⟨1,1,385,0⟩⟩,⟨149,⟨1,1,391,0⟩⟩,
  ⟨152,⟨1,1,397,0⟩⟩,⟨156,⟨1,1,409,0⟩⟩,⟨158,⟨1,1,415,0⟩⟩,⟨161,⟨1,1,421,0⟩⟩,⟨166,⟨1,1,433,0⟩⟩,⟨168,⟨1,1,439,0⟩⟩,
  ⟨171,⟨1,1,445,0⟩⟩,⟨176,⟨1,1,463,0⟩⟩,⟨179,⟨1,1,469,0⟩⟩,⟨184,⟨1,1,481,0⟩⟩,⟨186,⟨1,1,487,0⟩⟩,⟨189,⟨1,1,493,0⟩⟩,
  ⟨193,⟨1,1,505,0⟩⟩,⟨195,⟨1,1,511,0⟩⟩,⟨198,⟨1,1,517,0⟩⟩,⟨203,⟨1,1,529,0⟩⟩,⟨205,⟨1,1,535,0⟩⟩,⟨208,⟨1,1,541,0⟩⟩,
  ⟨209,⟨3,3,279,271⟩⟩,⟨212,⟨1,1,559,0⟩⟩,⟨215,⟨1,1,565,0⟩⟩,⟨220,⟨1,1,577,0⟩⟩,⟨222,⟨1,1,583,0⟩⟩,⟨225,⟨1,1,589,0⟩⟩,
  ⟨229,⟨1,1,601,0⟩⟩,⟨231,⟨1,1,607,0⟩⟩,⟨234,⟨1,1,613,0⟩⟩,⟨239,⟨1,1,625,0⟩⟩,⟨241,⟨1,1,631,0⟩⟩,⟨244,⟨1,1,637,0⟩⟩,
  ⟨248,⟨1,1,655,0⟩⟩,⟨251,⟨1,1,661,0⟩⟩,⟨256,⟨1,1,673,0⟩⟩,⟨258,⟨1,1,679,0⟩⟩,⟨261,⟨1,1,685,0⟩⟩
]
def lib_2 : List kernel:=[
  ⟨265,⟨1,1,697,0⟩⟩,⟨267,⟨1,1,703,0⟩⟩,⟨270,⟨1,1,709,0⟩⟩,⟨275,⟨1,1,721,0⟩⟩,⟨277,⟨1,1,727,0⟩⟩,⟨280,⟨1,1,733,0⟩⟩,
  ⟨281,⟨3,3,375,367⟩⟩,⟨284,⟨1,1,751,0⟩⟩,⟨287,⟨1,1,757,0⟩⟩,⟨292,⟨1,1,769,0⟩⟩,⟨294,⟨1,1,775,0⟩⟩,⟨297,⟨1,1,781,0⟩⟩,
  ⟨301,⟨1,1,793,0⟩⟩,⟨303,⟨1,1,799,0⟩⟩,⟨306,⟨1,1,805,0⟩⟩,⟨311,⟨1,1,817,0⟩⟩,⟨313,⟨1,1,823,0⟩⟩,⟨316,⟨1,1,829,0⟩⟩,
  ⟨321,⟨1,1,847,0⟩⟩,⟨324,⟨1,1,853,0⟩⟩,⟨329,⟨1,1,865,0⟩⟩,⟨331,⟨1,1,871,0⟩⟩,⟨334,⟨1,1,877,0⟩⟩,⟨338,⟨1,1,889,0⟩⟩,
  ⟨340,⟨1,1,895,0⟩⟩,⟨343,⟨1,1,901,0⟩⟩,⟨348,⟨1,1,913,0⟩⟩,⟨350,⟨1,1,919,0⟩⟩,⟨353,⟨1,1,925,0⟩⟩,⟨354,⟨3,3,471,463⟩⟩,
  ⟨357,⟨1,1,943,0⟩⟩,⟨360,⟨1,1,949,0⟩⟩,⟨365,⟨1,1,961,0⟩⟩,⟨367,⟨1,1,967,0⟩⟩,⟨370,⟨1,1,973,0⟩⟩,⟨374,⟨1,1,985,0⟩⟩,
  ⟨376,⟨1,1,991,0⟩⟩,⟨379,⟨1,1,997,0⟩⟩,⟨384,⟨1,1,1009,0⟩⟩,⟨386,⟨1,1,1015,0⟩⟩,⟨389,⟨1,1,1021,0⟩⟩
]
def lib_3 : List kernel:=[
  ⟨394,⟨1,1,1051,0⟩⟩,⟨397,⟨1,1,1057,0⟩⟩,⟨399,⟨1,1,1063,0⟩⟩,⟨402,⟨1,1,1069,0⟩⟩,⟨406,⟨1,1,1081,0⟩⟩,⟨408,⟨1,1,1087,0⟩⟩,
  ⟨411,⟨1,1,1093,0⟩⟩,⟨416,⟨1,1,1105,0⟩⟩,⟨418,⟨1,1,1111,0⟩⟩,⟨421,⟨1,1,1117,0⟩⟩,⟨422,⟨3,3,567,559⟩⟩,⟨425,⟨1,1,1135,0⟩⟩,
  ⟨428,⟨1,1,1141,0⟩⟩,⟨433,⟨1,1,1153,0⟩⟩,⟨435,⟨1,1,1159,0⟩⟩,⟨438,⟨1,1,1165,0⟩⟩,⟨442,⟨1,1,1177,0⟩⟩,⟨444,⟨1,1,1183,0⟩⟩,
  ⟨447,⟨1,1,1189,0⟩⟩,⟨452,⟨1,1,1201,0⟩⟩,⟨454,⟨1,1,1207,0⟩⟩,⟨457,⟨1,1,1213,0⟩⟩,⟨462,⟨1,1,1231,0⟩⟩,⟨465,⟨1,1,1237,0⟩⟩,
  ⟨470,⟨1,1,1249,0⟩⟩,⟨472,⟨1,1,1255,0⟩⟩,⟨475,⟨1,1,1261,0⟩⟩,⟨479,⟨1,1,1273,0⟩⟩,⟨481,⟨1,1,1279,0⟩⟩,⟨484,⟨1,1,1285,0⟩⟩,
  ⟨489,⟨1,1,1297,0⟩⟩,⟨491,⟨1,1,1303,0⟩⟩,⟨494,⟨1,1,1309,0⟩⟩,⟨495,⟨3,3,663,655⟩⟩,⟨498,⟨1,1,1327,0⟩⟩,⟨501,⟨1,1,1333,0⟩⟩,
  ⟨506,⟨1,1,1345,0⟩⟩,⟨508,⟨1,1,1351,0⟩⟩,⟨511,⟨1,1,1357,0⟩⟩,⟨515,⟨1,1,1369,0⟩⟩,⟨517,⟨1,1,1375,0⟩⟩
]
def lib_4 : List kernel:=[
  ⟨520,⟨1,1,1381,0⟩⟩,⟨525,⟨1,1,1393,0⟩⟩,⟨527,⟨1,1,1399,0⟩⟩,⟨530,⟨1,1,1405,0⟩⟩,⟨534,⟨1,1,1423,0⟩⟩,⟨537,⟨1,1,1429,0⟩⟩,
  ⟨542,⟨1,1,1441,0⟩⟩,⟨544,⟨1,1,1447,0⟩⟩,⟨547,⟨1,1,1453,0⟩⟩,⟨551,⟨1,1,1465,0⟩⟩,⟨553,⟨1,1,1471,0⟩⟩,⟨556,⟨1,1,1477,0⟩⟩,
  ⟨561,⟨1,1,1489,0⟩⟩,⟨563,⟨1,1,1495,0⟩⟩,⟨566,⟨1,1,1501,0⟩⟩,⟨567,⟨3,3,759,751⟩⟩,⟨570,⟨1,1,1519,0⟩⟩,⟨573,⟨1,1,1525,0⟩⟩,
  ⟨578,⟨1,1,1537,0⟩⟩,⟨580,⟨1,1,1543,0⟩⟩,⟨583,⟨1,1,1549,0⟩⟩,⟨587,⟨1,1,1561,0⟩⟩,⟨589,⟨1,1,1567,0⟩⟩,⟨592,⟨1,1,1573,0⟩⟩,
  ⟨597,⟨1,1,1585,0⟩⟩,⟨599,⟨1,1,1591,0⟩⟩,⟨602,⟨1,1,1597,0⟩⟩,⟨607,⟨1,1,1615,0⟩⟩,⟨610,⟨1,1,1621,0⟩⟩,⟨615,⟨1,1,1633,0⟩⟩,
  ⟨617,⟨1,1,1639,0⟩⟩,⟨620,⟨1,1,1645,0⟩⟩,⟨624,⟨1,1,1657,0⟩⟩,⟨626,⟨1,1,1663,0⟩⟩,⟨629,⟨1,1,1669,0⟩⟩,⟨634,⟨1,1,1681,0⟩⟩,
  ⟨636,⟨1,1,1687,0⟩⟩,⟨639,⟨1,1,1693,0⟩⟩,⟨640,⟨3,3,855,847⟩⟩,⟨643,⟨1,1,1711,0⟩⟩,⟨646,⟨1,1,1717,0⟩⟩
]
def lib_5 : List kernel:=[
  ⟨651,⟨1,1,1729,0⟩⟩,⟨653,⟨1,1,1735,0⟩⟩,⟨656,⟨1,1,1741,0⟩⟩,⟨660,⟨1,1,1753,0⟩⟩,⟨662,⟨1,1,1759,0⟩⟩,⟨665,⟨1,1,1765,0⟩⟩,
  ⟨670,⟨1,1,1777,0⟩⟩,⟨672,⟨1,1,1783,0⟩⟩,⟨675,⟨1,1,1789,0⟩⟩,⟨676,⟨3,3,909,895⟩⟩,⟨681,⟨1,1,1813,0⟩⟩,⟨686,⟨1,1,1825,0⟩⟩,
  ⟨688,⟨1,1,1831,0⟩⟩,⟨691,⟨1,1,1837,0⟩⟩,⟨695,⟨1,1,1849,0⟩⟩,⟨697,⟨1,1,1855,0⟩⟩,⟨700,⟨1,1,1861,0⟩⟩,⟨705,⟨1,1,1873,0⟩⟩,
  ⟨707,⟨1,1,1879,0⟩⟩,⟨710,⟨1,1,1885,0⟩⟩,⟨711,⟨3,3,951,943⟩⟩,⟨714,⟨1,1,1903,0⟩⟩,⟨717,⟨1,1,1909,0⟩⟩,⟨722,⟨1,1,1921,0⟩⟩,
  ⟨724,⟨1,1,1927,0⟩⟩,⟨727,⟨1,1,1933,0⟩⟩,⟨731,⟨1,1,1945,0⟩⟩,⟨733,⟨1,1,1951,0⟩⟩,⟨736,⟨1,1,1957,0⟩⟩,⟨741,⟨1,1,1969,0⟩⟩,
  ⟨743,⟨1,1,1975,0⟩⟩,⟨746,⟨1,1,1981,0⟩⟩,⟨751,⟨1,1,1999,0⟩⟩,⟨754,⟨1,1,2005,0⟩⟩,⟨759,⟨1,1,2017,0⟩⟩,⟨761,⟨1,1,2023,0⟩⟩,
  ⟨764,⟨1,1,2029,0⟩⟩,⟨768,⟨1,1,2041,0⟩⟩,⟨770,⟨1,1,2047,0⟩⟩,⟨773,⟨1,1,2053,0⟩⟩,⟨778,⟨1,1,2065,0⟩⟩
]
def lib_6 : List kernel:=[
  ⟨780,⟨1,1,2071,0⟩⟩,⟨783,⟨1,1,2077,0⟩⟩,⟨784,⟨3,3,1047,1039⟩⟩,⟨787,⟨1,1,2095,0⟩⟩,⟨790,⟨1,1,2101,0⟩⟩,⟨795,⟨1,1,2113,0⟩⟩,
  ⟨797,⟨1,1,2119,0⟩⟩,⟨800,⟨1,1,2125,0⟩⟩,⟨804,⟨1,1,2137,0⟩⟩,⟨806,⟨1,1,2143,0⟩⟩,⟨809,⟨1,1,2149,0⟩⟩,⟨814,⟨1,1,2161,0⟩⟩,
  ⟨816,⟨1,1,2167,0⟩⟩,⟨819,⟨1,1,2173,0⟩⟩,⟨823,⟨1,1,2191,0⟩⟩,⟨826,⟨1,1,2197,0⟩⟩,⟨831,⟨1,1,2209,0⟩⟩,⟨833,⟨1,1,2215,0⟩⟩,
  ⟨836,⟨1,1,2221,0⟩⟩,⟨840,⟨1,1,2233,0⟩⟩,⟨842,⟨1,1,2239,0⟩⟩,⟨845,⟨1,1,2245,0⟩⟩,⟨850,⟨1,1,2257,0⟩⟩,⟨852,⟨1,1,2263,0⟩⟩,
  ⟨855,⟨1,1,2269,0⟩⟩,⟨856,⟨3,3,1143,1135⟩⟩,⟨859,⟨1,1,2287,0⟩⟩,⟨862,⟨1,1,2293,0⟩⟩,⟨867,⟨1,1,2305,0⟩⟩,⟨869,⟨1,1,2311,0⟩⟩,
  ⟨872,⟨1,1,2317,0⟩⟩,⟨876,⟨1,1,2329,0⟩⟩,⟨878,⟨1,1,2335,0⟩⟩,⟨881,⟨1,1,2341,0⟩⟩,⟨886,⟨1,1,2353,0⟩⟩,⟨888,⟨1,1,2359,0⟩⟩,
  ⟨891,⟨1,1,2365,0⟩⟩,⟨896,⟨1,1,2383,0⟩⟩,⟨899,⟨1,1,2389,0⟩⟩,⟨904,⟨1,1,2401,0⟩⟩,⟨906,⟨1,1,2407,0⟩⟩
]
def lib_7 : List kernel:=[
  ⟨909,⟨1,1,2413,0⟩⟩,⟨913,⟨1,1,2425,0⟩⟩,⟨915,⟨1,1,2431,0⟩⟩,⟨918,⟨1,1,2437,0⟩⟩,⟨923,⟨1,1,2449,0⟩⟩,⟨925,⟨1,1,2455,0⟩⟩,
  ⟨928,⟨1,1,2461,0⟩⟩,⟨929,⟨3,3,1239,1231⟩⟩,⟨932,⟨1,1,2479,0⟩⟩,⟨935,⟨1,1,2485,0⟩⟩,⟨940,⟨1,1,2497,0⟩⟩,⟨942,⟨1,1,2503,0⟩⟩,
  ⟨945,⟨1,1,2509,0⟩⟩,⟨949,⟨1,1,2521,0⟩⟩,⟨951,⟨1,1,2527,0⟩⟩,⟨954,⟨1,1,2533,0⟩⟩,⟨959,⟨1,1,2545,0⟩⟩,⟨961,⟨1,1,2551,0⟩⟩,
  ⟨964,⟨1,1,2557,0⟩⟩,⟨966,⟨1,1,2581,0⟩⟩,⟨971,⟨1,1,2593,0⟩⟩,⟨973,⟨1,1,2599,0⟩⟩,⟨976,⟨1,1,2605,0⟩⟩,⟨980,⟨1,1,2617,0⟩⟩,
  ⟨982,⟨1,1,2623,0⟩⟩,⟨985,⟨1,1,2629,0⟩⟩,⟨990,⟨1,1,2641,0⟩⟩,⟨992,⟨1,1,2647,0⟩⟩,⟨995,⟨1,1,2653,0⟩⟩,⟨996,⟨3,3,1335,1327⟩⟩,
  ⟨999,⟨1,1,2671,0⟩⟩,⟨1002,⟨1,1,2677,0⟩⟩,⟨1007,⟨1,1,2689,0⟩⟩,⟨1009,⟨1,1,2695,0⟩⟩,⟨1012,⟨1,1,2701,0⟩⟩,⟨1016,⟨1,1,2713,0⟩⟩,
  ⟨1018,⟨1,1,2719,0⟩⟩,⟨1021,⟨1,1,2725,0⟩⟩,⟨1026,⟨1,1,2737,0⟩⟩,⟨1028,⟨1,1,2743,0⟩⟩,⟨1031,⟨1,1,2749,0⟩⟩
]
def lib_8 : List kernel:=[
  ⟨1036,⟨1,1,2767,0⟩⟩,⟨1039,⟨1,1,2773,0⟩⟩,⟨1044,⟨1,1,2785,0⟩⟩,⟨1046,⟨1,1,2791,0⟩⟩,⟨1049,⟨1,1,2797,0⟩⟩,⟨1053,⟨1,1,2809,0⟩⟩,
  ⟨1055,⟨1,1,2815,0⟩⟩,⟨1058,⟨1,1,2821,0⟩⟩,⟨1063,⟨1,1,2833,0⟩⟩,⟨1065,⟨1,1,2839,0⟩⟩,⟨1068,⟨1,1,2845,0⟩⟩,⟨1069,⟨3,3,1431,1423⟩⟩,
  ⟨1072,⟨1,1,2863,0⟩⟩,⟨1075,⟨1,1,2869,0⟩⟩,⟨1080,⟨1,1,2881,0⟩⟩,⟨1082,⟨1,1,2887,0⟩⟩,⟨1085,⟨1,1,2893,0⟩⟩,⟨1089,⟨1,1,2905,0⟩⟩,
  ⟨1091,⟨1,1,2911,0⟩⟩,⟨1094,⟨1,1,2917,0⟩⟩,⟨1099,⟨1,1,2929,0⟩⟩,⟨1101,⟨1,1,2935,0⟩⟩,⟨1104,⟨1,1,2941,0⟩⟩,⟨1108,⟨1,1,2959,0⟩⟩,
  ⟨1111,⟨1,1,2965,0⟩⟩,⟨1116,⟨1,1,2977,0⟩⟩,⟨1118,⟨1,1,2983,0⟩⟩,⟨1121,⟨1,1,2989,0⟩⟩,⟨1125,⟨1,1,3001,0⟩⟩,⟨1127,⟨1,1,3007,0⟩⟩,
  ⟨1130,⟨1,1,3013,0⟩⟩,⟨1135,⟨1,1,3025,0⟩⟩,⟨1137,⟨1,1,3031,0⟩⟩,⟨1140,⟨1,1,3037,0⟩⟩,⟨1141,⟨3,3,1527,1519⟩⟩,⟨1144,⟨1,1,3055,0⟩⟩,
  ⟨1147,⟨1,1,3061,0⟩⟩,⟨1152,⟨1,1,3073,0⟩⟩,⟨1154,⟨1,1,3079,0⟩⟩,⟨1157,⟨1,1,3085,0⟩⟩,⟨1161,⟨1,1,3097,0⟩⟩
]
def lib_9 : List kernel:=[
  ⟨1163,⟨1,1,3103,0⟩⟩,⟨1166,⟨1,1,3109,0⟩⟩,⟨1171,⟨1,1,3121,0⟩⟩,⟨1173,⟨1,1,3127,0⟩⟩,⟨1176,⟨1,1,3133,0⟩⟩,⟨1181,⟨1,1,3151,0⟩⟩,
  ⟨1184,⟨1,1,3157,0⟩⟩,⟨1189,⟨1,1,3169,0⟩⟩,⟨1191,⟨1,1,3175,0⟩⟩,⟨1194,⟨1,1,3181,0⟩⟩,⟨1198,⟨1,1,3193,0⟩⟩,⟨1200,⟨1,1,3199,0⟩⟩,
  ⟨1203,⟨1,1,3205,0⟩⟩,⟨1208,⟨1,1,3217,0⟩⟩,⟨1210,⟨1,1,3223,0⟩⟩,⟨1213,⟨1,1,3229,0⟩⟩,⟨1214,⟨3,3,1623,1615⟩⟩,⟨1217,⟨1,1,3247,0⟩⟩,
  ⟨1220,⟨1,1,3253,0⟩⟩,⟨1225,⟨1,1,3265,0⟩⟩,⟨1227,⟨1,1,3271,0⟩⟩,⟨1230,⟨1,1,3277,0⟩⟩,⟨1234,⟨1,1,3289,0⟩⟩,⟨1236,⟨1,1,3295,0⟩⟩,
  ⟨1239,⟨1,1,3301,0⟩⟩,⟨1244,⟨1,1,3313,0⟩⟩,⟨1246,⟨1,1,3319,0⟩⟩,⟨1249,⟨1,1,3325,0⟩⟩,⟨1250,⟨3,3,1677,1663⟩⟩,⟨1255,⟨1,1,3349,0⟩⟩,
  ⟨1260,⟨1,1,3361,0⟩⟩,⟨1262,⟨1,1,3367,0⟩⟩,⟨1265,⟨1,1,3373,0⟩⟩,⟨1269,⟨1,1,3385,0⟩⟩,⟨1271,⟨1,1,3391,0⟩⟩,⟨1274,⟨1,1,3397,0⟩⟩,
  ⟨1279,⟨1,1,3409,0⟩⟩,⟨1281,⟨1,1,3415,0⟩⟩,⟨1284,⟨1,1,3421,0⟩⟩,⟨1285,⟨3,3,1719,1711⟩⟩,⟨1288,⟨1,1,3439,0⟩⟩
]
def lib_10 : List kernel:=[
  ⟨1291,⟨1,1,3445,0⟩⟩,⟨1296,⟨1,1,3457,0⟩⟩,⟨1298,⟨1,1,3463,0⟩⟩,⟨1301,⟨1,1,3469,0⟩⟩,⟨1305,⟨1,1,3481,0⟩⟩,⟨1307,⟨1,1,3487,0⟩⟩,
  ⟨1310,⟨1,1,3493,0⟩⟩,⟨1315,⟨1,1,3505,0⟩⟩,⟨1317,⟨1,1,3511,0⟩⟩,⟨1320,⟨1,1,3517,0⟩⟩,⟨1325,⟨1,1,3535,0⟩⟩,⟨1328,⟨1,1,3541,0⟩⟩,
  ⟨1333,⟨1,1,3553,0⟩⟩,⟨1335,⟨1,1,3559,0⟩⟩,⟨1338,⟨1,1,3565,0⟩⟩,⟨1342,⟨1,1,3577,0⟩⟩,⟨1344,⟨1,1,3583,0⟩⟩,⟨1347,⟨1,1,3589,0⟩⟩,
  ⟨1352,⟨1,1,3601,0⟩⟩,⟨1354,⟨1,1,3607,0⟩⟩,⟨1357,⟨1,1,3613,0⟩⟩,⟨1358,⟨3,3,1815,1807⟩⟩,⟨1361,⟨1,1,3631,0⟩⟩,⟨1364,⟨1,1,3637,0⟩⟩,
  ⟨1369,⟨1,1,3649,0⟩⟩,⟨1371,⟨1,1,3655,0⟩⟩,⟨1374,⟨1,1,3661,0⟩⟩,⟨1378,⟨1,1,3673,0⟩⟩,⟨1380,⟨1,1,3679,0⟩⟩,⟨1383,⟨1,1,3685,0⟩⟩,
  ⟨1388,⟨1,1,3697,0⟩⟩,⟨1390,⟨1,1,3703,0⟩⟩,⟨1393,⟨1,1,3709,0⟩⟩,⟨1397,⟨1,1,3727,0⟩⟩,⟨1400,⟨1,1,3733,0⟩⟩,⟨1405,⟨1,1,3745,0⟩⟩,
  ⟨1407,⟨1,1,3751,0⟩⟩,⟨1410,⟨1,1,3757,0⟩⟩,⟨1414,⟨1,1,3769,0⟩⟩,⟨1416,⟨1,1,3775,0⟩⟩,⟨1419,⟨1,1,3781,0⟩⟩
]
def lib_11 : List kernel:=[
  ⟨1424,⟨1,1,3793,0⟩⟩,⟨1426,⟨1,1,3799,0⟩⟩,⟨1429,⟨1,1,3805,0⟩⟩,⟨1430,⟨3,3,1911,1903⟩⟩,⟨1433,⟨1,1,3823,0⟩⟩,⟨1436,⟨1,1,3829,0⟩⟩,
  ⟨1441,⟨1,1,3841,0⟩⟩,⟨1443,⟨1,1,3847,0⟩⟩,⟨1446,⟨1,1,3853,0⟩⟩,⟨1450,⟨1,1,3865,0⟩⟩,⟨1452,⟨1,1,3871,0⟩⟩,⟨1455,⟨1,1,3877,0⟩⟩,
  ⟨1460,⟨1,1,3889,0⟩⟩,⟨1462,⟨1,1,3895,0⟩⟩,⟨1465,⟨1,1,3901,0⟩⟩,⟨1470,⟨1,1,3919,0⟩⟩,⟨1473,⟨1,1,3925,0⟩⟩,⟨1478,⟨1,1,3937,0⟩⟩,
  ⟨1480,⟨1,1,3943,0⟩⟩,⟨1483,⟨1,1,3949,0⟩⟩,⟨1487,⟨1,1,3961,0⟩⟩,⟨1489,⟨1,1,3967,0⟩⟩,⟨1492,⟨1,1,3973,0⟩⟩,⟨1497,⟨1,1,3985,0⟩⟩,
  ⟨1499,⟨1,1,3991,0⟩⟩,⟨1502,⟨1,1,3997,0⟩⟩,⟨1503,⟨3,3,2007,1999⟩⟩,⟨1506,⟨1,1,4015,0⟩⟩,⟨1509,⟨1,1,4021,0⟩⟩,⟨1514,⟨1,1,4033,0⟩⟩,
  ⟨1516,⟨1,1,4039,0⟩⟩,⟨1519,⟨1,1,4045,0⟩⟩,⟨1523,⟨1,1,4057,0⟩⟩,⟨1525,⟨1,1,4063,0⟩⟩,⟨1528,⟨1,1,4069,0⟩⟩,⟨1533,⟨1,1,4081,0⟩⟩,
  ⟨1535,⟨1,1,4087,0⟩⟩,⟨1538,⟨1,1,4093,0⟩⟩,⟨1539,⟨3,3,2073,2047⟩⟩,⟨1544,⟨1,1,4129,0⟩⟩,⟨1546,⟨1,1,4135,0⟩⟩
]
def lib_12 : List kernel:=[
  ⟨1549,⟨1,1,4141,0⟩⟩,⟨1553,⟨1,1,4153,0⟩⟩,⟨1555,⟨1,1,4159,0⟩⟩,⟨1558,⟨1,1,4165,0⟩⟩,⟨1563,⟨1,1,4177,0⟩⟩,⟨1565,⟨1,1,4183,0⟩⟩,
  ⟨1568,⟨1,1,4189,0⟩⟩,⟨1569,⟨3,3,2103,2095⟩⟩,⟨1572,⟨1,1,4207,0⟩⟩,⟨1575,⟨1,1,4213,0⟩⟩,⟨1580,⟨1,1,4225,0⟩⟩,⟨1582,⟨1,1,4231,0⟩⟩,
  ⟨1585,⟨1,1,4237,0⟩⟩,⟨1589,⟨1,1,4249,0⟩⟩,⟨1591,⟨1,1,4255,0⟩⟩,⟨1594,⟨1,1,4261,0⟩⟩,⟨1599,⟨1,1,4273,0⟩⟩,⟨1601,⟨1,1,4279,0⟩⟩,
  ⟨1604,⟨1,1,4285,0⟩⟩,⟨1609,⟨1,1,4303,0⟩⟩,⟨1612,⟨1,1,4309,0⟩⟩,⟨1617,⟨1,1,4321,0⟩⟩,⟨1619,⟨1,1,4327,0⟩⟩,⟨1622,⟨1,1,4333,0⟩⟩,
  ⟨1626,⟨1,1,4345,0⟩⟩,⟨1628,⟨1,1,4351,0⟩⟩,⟨1631,⟨1,1,4357,0⟩⟩,⟨1636,⟨1,1,4369,0⟩⟩,⟨1638,⟨1,1,4375,0⟩⟩,⟨1641,⟨1,1,4381,0⟩⟩,
  ⟨1642,⟨3,3,2199,2191⟩⟩,⟨1645,⟨1,1,4399,0⟩⟩,⟨1648,⟨1,1,4405,0⟩⟩,⟨1653,⟨1,1,4417,0⟩⟩,⟨1655,⟨1,1,4423,0⟩⟩,⟨1658,⟨1,1,4429,0⟩⟩,
  ⟨1662,⟨1,1,4441,0⟩⟩,⟨1664,⟨1,1,4447,0⟩⟩,⟨1667,⟨1,1,4453,0⟩⟩,⟨1672,⟨1,1,4465,0⟩⟩,⟨1674,⟨1,1,4471,0⟩⟩
]
def lib_13 : List kernel:=[
  ⟨1677,⟨1,1,4477,0⟩⟩,⟨1681,⟨1,1,4495,0⟩⟩,⟨1684,⟨1,1,4501,0⟩⟩,⟨1689,⟨1,1,4513,0⟩⟩,⟨1691,⟨1,1,4519,0⟩⟩,⟨1694,⟨1,1,4525,0⟩⟩,
  ⟨1698,⟨1,1,4537,0⟩⟩,⟨1700,⟨1,1,4543,0⟩⟩,⟨1703,⟨1,1,4549,0⟩⟩,⟨1708,⟨1,1,4561,0⟩⟩,⟨1710,⟨1,1,4567,0⟩⟩,⟨1713,⟨1,1,4573,0⟩⟩,
  ⟨1714,⟨3,3,2295,2287⟩⟩,⟨1717,⟨1,1,4591,0⟩⟩,⟨1720,⟨1,1,4597,0⟩⟩,⟨1725,⟨1,1,4609,0⟩⟩,⟨1727,⟨1,1,4615,0⟩⟩,⟨1730,⟨1,1,4621,0⟩⟩,
  ⟨1734,⟨1,1,4633,0⟩⟩,⟨1736,⟨1,1,4639,0⟩⟩,⟨1739,⟨1,1,4645,0⟩⟩,⟨1744,⟨1,1,4657,0⟩⟩,⟨1746,⟨1,1,4663,0⟩⟩,⟨1749,⟨1,1,4669,0⟩⟩,
  ⟨1754,⟨1,1,4687,0⟩⟩,⟨1757,⟨1,1,4693,0⟩⟩,⟨1762,⟨1,1,4705,0⟩⟩,⟨1764,⟨1,1,4711,0⟩⟩,⟨1767,⟨1,1,4717,0⟩⟩,⟨1771,⟨1,1,4729,0⟩⟩,
  ⟨1773,⟨1,1,4735,0⟩⟩,⟨1776,⟨1,1,4741,0⟩⟩,⟨1781,⟨1,1,4753,0⟩⟩,⟨1783,⟨1,1,4759,0⟩⟩,⟨1786,⟨1,1,4765,0⟩⟩,⟨1787,⟨3,3,2391,2383⟩⟩,
  ⟨1790,⟨1,1,4783,0⟩⟩,⟨1793,⟨1,1,4789,0⟩⟩,⟨1798,⟨1,1,4801,0⟩⟩,⟨1800,⟨1,1,4807,0⟩⟩,⟨1803,⟨1,1,4813,0⟩⟩
]
def lib_14 : List kernel:=[
  ⟨1807,⟨1,1,4825,0⟩⟩,⟨1809,⟨1,1,4831,0⟩⟩,⟨1812,⟨1,1,4837,0⟩⟩,⟨1817,⟨1,1,4849,0⟩⟩,⟨1819,⟨1,1,4855,0⟩⟩,⟨1822,⟨1,1,4861,0⟩⟩,
  ⟨1823,⟨3,3,2445,2431⟩⟩,⟨1828,⟨1,1,4885,0⟩⟩,⟨1833,⟨1,1,4897,0⟩⟩,⟨1835,⟨1,1,4903,0⟩⟩,⟨1838,⟨1,1,4909,0⟩⟩,⟨1842,⟨1,1,4921,0⟩⟩,
  ⟨1844,⟨1,1,4927,0⟩⟩,⟨1847,⟨1,1,4933,0⟩⟩,⟨1852,⟨1,1,4945,0⟩⟩,⟨1854,⟨1,1,4951,0⟩⟩,⟨1857,⟨1,1,4957,0⟩⟩,⟨1858,⟨3,3,2487,2479⟩⟩,
  ⟨1861,⟨1,1,4975,0⟩⟩,⟨1864,⟨1,1,4981,0⟩⟩,⟨1869,⟨1,1,4993,0⟩⟩,⟨1871,⟨1,1,4999,0⟩⟩,⟨1874,⟨1,1,5005,0⟩⟩,⟨1878,⟨1,1,5017,0⟩⟩,
  ⟨1880,⟨1,1,5023,0⟩⟩,⟨1883,⟨1,1,5029,0⟩⟩,⟨1888,⟨1,1,5041,0⟩⟩,⟨1890,⟨1,1,5047,0⟩⟩,⟨1893,⟨1,1,5053,0⟩⟩,⟨1898,⟨1,1,5071,0⟩⟩,
  ⟨1901,⟨1,1,5077,0⟩⟩,⟨1906,⟨1,1,5089,0⟩⟩,⟨1908,⟨1,1,5095,0⟩⟩,⟨1911,⟨1,1,5101,0⟩⟩,⟨1915,⟨1,1,5113,0⟩⟩,⟨1917,⟨1,1,5119,0⟩⟩,
  ⟨1920,⟨1,1,5125,0⟩⟩,⟨1925,⟨1,1,5137,0⟩⟩,⟨1927,⟨1,1,5143,0⟩⟩,⟨1930,⟨1,1,5149,0⟩⟩,⟨1931,⟨3,3,2583,2575⟩⟩
]
def lib_15 : List kernel:=[
  ⟨1934,⟨1,1,5167,0⟩⟩,⟨1937,⟨1,1,5173,0⟩⟩,⟨1942,⟨1,1,5185,0⟩⟩,⟨1944,⟨1,1,5191,0⟩⟩,⟨1947,⟨1,1,5197,0⟩⟩,⟨1951,⟨1,1,5209,0⟩⟩,
  ⟨1953,⟨1,1,5215,0⟩⟩,⟨1956,⟨1,1,5221,0⟩⟩,⟨1961,⟨1,1,5233,0⟩⟩,⟨1963,⟨1,1,5239,0⟩⟩,⟨1966,⟨1,1,5245,0⟩⟩,⟨1970,⟨1,1,5263,0⟩⟩,
  ⟨1973,⟨1,1,5269,0⟩⟩,⟨1978,⟨1,1,5281,0⟩⟩,⟨1980,⟨1,1,5287,0⟩⟩,⟨1983,⟨1,1,5293,0⟩⟩,⟨1987,⟨1,1,5305,0⟩⟩,⟨1989,⟨1,1,5311,0⟩⟩,
  ⟨1992,⟨1,1,5317,0⟩⟩,⟨1997,⟨1,1,5329,0⟩⟩,⟨1999,⟨1,1,5335,0⟩⟩,⟨2002,⟨1,1,5341,0⟩⟩,⟨2003,⟨3,3,2679,2671⟩⟩,⟨2006,⟨1,1,5359,0⟩⟩,
  ⟨2009,⟨1,1,5365,0⟩⟩,⟨2014,⟨1,1,5377,0⟩⟩,⟨2016,⟨1,1,5383,0⟩⟩,⟨2019,⟨1,1,5389,0⟩⟩,⟨2023,⟨1,1,5401,0⟩⟩,⟨2025,⟨1,1,5407,0⟩⟩,
  ⟨2028,⟨1,1,5413,0⟩⟩,⟨2033,⟨1,1,5425,0⟩⟩,⟨2035,⟨1,1,5431,0⟩⟩,⟨2038,⟨1,1,5437,0⟩⟩,⟨2043,⟨1,1,5455,0⟩⟩,⟨2046,⟨1,1,5461,0⟩⟩
]
def library_val : List kernel :=
  lib_0 ++ lib_1 ++ lib_2 ++ lib_3 ++ lib_4 ++ lib_5 ++ lib_6 ++ lib_7 ++ lib_8 ++ lib_9 ++ lib_10 ++ lib_11 ++ lib_12 ++ lib_13 ++ lib_14 ++ lib_15
lemma library_eq : library=library_val:= by decide +kernel
def action (k : kernel) (S U S' U' : ℤ) : Prop :=
  S'=S + gain k ∧
  q0 k.pair.d * U'=k.pair.p * (2 * S - U + 3) + q0 k.pair.d * k.pair.b ∧
  ∃ t,2 * S - U + 3=q0 k.index * (2 * t + 1)
inductive trace : List kernel → ℤ → ℤ → Prop where
  | trace_nil (S U : ℤ) : trace [] S U
  | trace_cons {k : kernel} {r : List kernel} {S U S' U' : ℤ} :
      action k S U S' U' → trace r S' U' → trace (k :: r) S U
end WordLibrary
namespace WordCheck
open Table WordArith WordRelation WordLibrary
structure state where
  rel : Option relation
  P : ℤ
  Q : ℤ
  C : ℤ
  D : ℤ
  mass : ℤ
  deriving DecidableEq,Repr
def qE (z : state) (S0 U0 S U : ℤ) : Prop :=
  0 ≤ z.D ∧ qW z.Q ∧
  q0 z.D * U=z.P * S0 + z.Q * U0 + z.C ∧ S=S0 + z.mass ∧ optional z.rel S0 U0
def A (z : state) : ℤ:=q0 (z.D + 1) - z.P
def B (z : state) : ℤ:=(2 * z.mass + 3) * q0 z.D - z.C
lemma qav (z : state) (S0 U0 S U : ℤ) (hz : qE z S0 U0 S U) :
    q0 z.D * (2 * S - U + 3)=A z * S0 - z.Q * U0 + B z:= by
  rcases hz with ⟨hD,hQ,hU,hS,hR⟩
  unfold A B
  rw [q5 hD (by omega),pow2_one,hS]
  linarith
lemma qcj (z : state) (k : kernel) (S0 U0 S U S' U' : ℤ)
    (hz : qE z S0 U0 S U) (hk : 0 ≤ k.index) (hact : action k S U S' U') :
    qa3 (z.D + k.index + 1) (z.Q * U0 - A z * S0 - (B z - q0 (z.D + k.index))):= by
  rcases hact with ⟨hS,hU,t,ht⟩
  have hH:=qav z S0 U0 S U hz
  rcases hz with ⟨hD,_⟩
  refine ⟨-t,?_⟩
  rw [ht] at hH
  rw [q5 (by omega : 0 ≤ z.D + k.index) (by omega : 0 ≤ (1 : ℤ)),pow2_one]
  rw [q5 hD hk]
  linarith
def push (z : state) (k : kernel) (r : relation) : state :=
  ⟨some r,
   k.pair.p * A z,
   -k.pair.p * z.Q,
   k.pair.p * B z + k.pair.b * q0 (z.D + k.pair.d),
   z.D + k.pair.d,
   z.mass + gain k⟩
lemma push_spec (z : state) (k : kernel) (r : relation) (S0 U0 S U S' U' : ℤ)
    (hz : qE z S0 U0 S U) (hd : 0 ≤ k.pair.d) (hp : qW k.pair.p)
    (hact : action k S U S' U') (hr : qbd r S0 U0) :
    qE (push z k r) S0 U0 S' U':= by
  rcases hact with ⟨hS,hU,_⟩
  have hH:=qav z S0 U0 S U hz
  rcases hz with ⟨hD,hQ,hU0,hS0,hR0⟩
  unfold qE push WordRelation.optional
  try dsimp -failIfUnchanged only
  refine ⟨by omega,?_,?_,by omega,hr⟩
  · rcases hp with ⟨a,ha⟩
    rcases hQ with ⟨b,hb⟩
    refine ⟨-2 * a * b - a - b - 1,?_⟩
    rw [ha,hb]; ring
  · rw [q5 hD hd]
    have h1 := congr_arg (fun t => q0 z.D * t) hU
    have h2 := congr_arg (fun t => k.pair.p * t) hH
    linarith
def qJ {T : Type*} (f : T → Bool) : List T → Bool
  | [] => true
  | x :: r => if f x then qJ f r else false
lemma qbf {T : Type*} (f : T → Bool) (xs : List T) (h : qJ f xs=true) :
    ∀ x ∈ xs,f x=true:= by
  induction xs with
  | nil => intro x hx; contradiction
  | cons a xs ih =>
    unfold qJ at h
    split_ifs at h with ha
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha
    · exact ih h x hx'
lemma qbr {T : Type*} (f : T → Bool) (xs ys : List T) :
    qJ f (xs ++ ys)=(qJ f xs && qJ f ys):= by
  induction xs with
  | nil => simp [qJ]
  | cons a xs ih =>
    simp only [List.cons_append,qJ,ih]
    cases f a <;> rfl
def int_le (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => Nat.ble m n
  | Int.negSucc _, Int.ofNat _ => true
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc m, Int.negSucc n => Nat.ble n m
def int_lt (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => Nat.ble (Nat.add m 1) n
  | Int.negSucc _, Int.ofNat _ => true
  | Int.ofNat _, Int.negSucc _ => false
  | Int.negSucc m, Int.negSucc n => Nat.ble (Nat.add n 1) m
def int_eq (a b : ℤ) : Bool :=
  match a, b with
  | Int.ofNat m, Int.ofNat n => Nat.beq m n
  | Int.negSucc m, Int.negSucc n => Nat.beq m n
  | _, _ => false
def find_kernel (s : ℤ) : List kernel → List kernel
  | [] => []
  | k :: ks =>
    if int_eq k.index s then [k]
    else if int_lt s k.index then []
    else find_kernel s ks
def single (s : ℤ) : List kernel :=
  if int_lt s 5 then []
  else if int_eq s 5 then [⟨5,⟨1,1,7,0⟩⟩]
  else if int_lt s 8 then []
  else if int_eq s 8 then [⟨8,⟨1,1,13,0⟩⟩]
  else if int_lt s 12 then []
  else if int_eq s 12 then [⟨12,⟨1,1,25,0⟩⟩]
  else if int_lt s 14 then []
  else if int_lt s 1036 then
    if int_lt s 520 then
      if int_lt s 265 then
        if int_lt s 135 then find_kernel s lib_0
        else find_kernel s lib_1
      else
        if int_lt s 394 then find_kernel s lib_2
        else find_kernel s lib_3
    else
      if int_lt s 780 then
        if int_lt s 651 then find_kernel s lib_4
        else find_kernel s lib_5
      else
        if int_lt s 909 then find_kernel s lib_6
        else find_kernel s lib_7
  else
    if int_lt s 1549 then
      if int_lt s 1291 then
        if int_lt s 1163 then find_kernel s lib_8
        else find_kernel s lib_9
      else
        if int_lt s 1424 then find_kernel s lib_10
        else find_kernel s lib_11
    else
      if int_lt s 1807 then
        if int_lt s 1677 then find_kernel s lib_12
        else find_kernel s lib_13
      else
        if int_lt s 1934 then find_kernel s lib_14
        else if int_le s 2046 then find_kernel s lib_15
        else []
lemma single_all :
    qJ (fun k => decide (k ∈ single k.index)) library_val=true:= by
  decide +kernel
lemma qx (k : kernel) (hk : continuing k) (hmax : k.index ≤ 2048) :
    k ∈ library_val:= by
  rw [← library_eq]
  exact qby k hk hmax
lemma qbL (k : kernel) (hk : continuing k) (hmax : k.index ≤ 2048) :
    k ∈ single k.index:= by
  have hmem : k ∈ library_val:=qx k hk hmax
  exact of_decide_eq_true (qbf _ library_val single_all k hmem)
def qaQ (z : state) (f : state → Option state) : Option state :=
  q2 z.P fun P =>
  q2 z.Q fun Q =>
  q2 z.C fun C =>
  q2 z.D fun D =>
  q2 z.mass fun mass =>
  f ⟨z.rel,P,Q,C,D,mass⟩
@[simp] lemma strictState_eq (z : state) (f : state → Option state) :
    qaQ z f=f z:= by
  cases z; simp [qaQ]
def qbj (z : state) : List kernel :=
  match z.rel with
  | none => library_val
  | some r =>
    q2 (A z) fun az =>
    q2 (B z) fun bz =>
    q2 (qa2 r az z.Q) fun bound =>
    q2 (qq bound (qa6 r az bz z.Q)) fun v =>
    if decide (v < bound) then
      q2 (v - z.D) fun s => single s
    else
      q2 (bound - z.D) fun min_idx =>
      library_val.filter (fun k => decide (min_idx ≤ k.index))
lemma choices_spec (z : state) (k : kernel) (S0 U0 S U S' U' : ℤ)
    (hz : qE z S0 U0 S U) (hk : continuing k) (hmax : k.index ≤ 2048)
    (hstep : action k S U S' U') :
    k ∈ qbj z:= by
  rcases hstep with ⟨hS,hU,t,ht⟩
  have hH:=qav z S0 U0 S U hz
  rcases hz with ⟨hD,hQ,hU0,hS0,hR⟩
  rcases hk with ⟨e,hbuilt,hindex,hodd⟩
  have hkeep : continuing k:=⟨e,hbuilt,hindex,hodd⟩
  have hH' : A z * S0 - z.Q * U0 + B z=q0 (z.D + k.index) * (2 * t + 1):= by
    rw [← hH,ht,q5 hD (by omega)]
    ring
  unfold qbj
  simp only [strictInt_eq]
  cases hr : z.rel with
  | none => exact qx k hkeep hmax
  | some r =>
    rw [hr] at hR
    change qbd r S0 U0 at hR
    rcases pruning_spec r (A z) (B z) z.Q S0 U0 z.D k.index t hR hD (by omega) hH' with ⟨he,hl⟩
    try dsimp -failIfUnchanged only at he hl ⊢
    have hb : 0 ≤ qa2 r (A z) z.Q:= by
      rcases hR with ⟨hn,hp,_⟩
      unfold qa2
      have:=qL (qb2 r (A z) z.Q) hn
      omega
    have hv:=qL (qa6 r (A z) (B z) z.Q) hb
    split_ifs with hvb
    · have hvb' : qq (qa2 r (A z) z.Q) (qa6 r (A z) (B z) z.Q) < qa2 r (A z) z.Q :=
        of_decide_eq_true hvb
      have hs_eq : k.index=qq (qa2 r (A z) z.Q) (qa6 r (A z) (B z) z.Q) - z.D:=he hvb'
      rw [← hs_eq]
      exact qbL k hkeep hmax
    · rw [decide_eq_true_iff] at hvb
      exact List.mem_filter.mpr ⟨qx k hkeep hmax,decide_eq_true (hl (by omega))⟩
def advance (z : state) (k : kernel) : Option state :=
  q2 (A z) fun az =>
  q2 (B z) fun bz =>
  q2 (z.D + k.index) fun dki =>
  q2 (bz - q0 dki) fun c_arg =>
  q2 (dki + 1) fun n_arg =>
  match add z.rel az z.Q c_arg n_arg with
  | some r => qaQ (push z k r) some
  | none => none
lemma advance_spec (z : state) (k : kernel) (S0 U0 S U S' U' : ℤ)
    (hz : qE z S0 U0 S U) (hk : continuing k) (hstep : action k S U S' U') :
    ∃ z',advance z k=some z' ∧ qE z' S0 U0 S' U':= by
  rcases hk with ⟨e,hbuilt,hindex,hodd⟩
  rcases (Table.built_valid hbuilt).1 with ⟨hk0,he0,⟨⟨hd,_,hp,_,hpo,_⟩,_⟩,_⟩
  have hcond:=qcj z k S0 U0 S U S' U' hz (by omega) hstep
  have hkeep:=hz
  rcases hz with ⟨hD,hQ,hU,hS,hR⟩
  rcases add_spec z.rel (A z) z.Q (B z - q0 (z.D + k.index)) (z.D + k.index + 1)
    S0 U0 hR (by omega) hQ hcond with ⟨r,hadd,hholds⟩
  refine ⟨push z k r,?_,?_⟩
  · unfold advance
    simp only [strictInt_eq,strictState_eq]
    rw [hadd]
  · exact push_spec z k r S0 U0 S U S' U' hkeep hd hpo hstep hholds
def qB (f : state → Bool) (z : state) (k : kernel) : Bool :=
  match advance z k with
  | none => true
  | some z' => f z'
def bkt_1 : List kernel := [⟨27,⟨1,1,61,0⟩⟩,⟨64,⟨1,1,157,0⟩⟩,⟨100,⟨1,1,253,0⟩⟩,⟨135,⟨1,1,349,0⟩⟩,⟨171,⟨1,1,445,0⟩⟩,⟨208,⟨1,1,541,0⟩⟩,⟨244,⟨1,1,637,0⟩⟩,⟨280,⟨1,1,733,0⟩⟩,⟨316,⟨1,1,829,0⟩⟩,⟨353,⟨1,1,925,0⟩⟩,⟨389,⟨1,1,1021,0⟩⟩,⟨421,⟨1,1,1117,0⟩⟩,⟨457,⟨1,1,1213,0⟩⟩,⟨494,⟨1,1,1309,0⟩⟩,⟨530,⟨1,1,1405,0⟩⟩,⟨566,⟨1,1,1501,0⟩⟩,⟨602,⟨1,1,1597,0⟩⟩,⟨639,⟨1,1,1693,0⟩⟩,⟨675,⟨1,1,1789,0⟩⟩,⟨710,⟨1,1,1885,0⟩⟩,⟨746,⟨1,1,1981,0⟩⟩,⟨783,⟨1,1,2077,0⟩⟩,⟨819,⟨1,1,2173,0⟩⟩,⟨855,⟨1,1,2269,0⟩⟩,⟨891,⟨1,1,2365,0⟩⟩,⟨928,⟨1,1,2461,0⟩⟩,⟨964,⟨1,1,2557,0⟩⟩,⟨995,⟨1,1,2653,0⟩⟩,⟨1031,⟨1,1,2749,0⟩⟩,⟨1068,⟨1,1,2845,0⟩⟩,⟨1104,⟨1,1,2941,0⟩⟩,⟨1140,⟨1,1,3037,0⟩⟩,⟨1176,⟨1,1,3133,0⟩⟩,⟨1213,⟨1,1,3229,0⟩⟩,⟨1249,⟨1,1,3325,0⟩⟩,⟨1284,⟨1,1,3421,0⟩⟩,⟨1320,⟨1,1,3517,0⟩⟩,⟨1357,⟨1,1,3613,0⟩⟩,⟨1393,⟨1,1,3709,0⟩⟩,⟨1429,⟨1,1,3805,0⟩⟩,⟨1465,⟨1,1,3901,0⟩⟩,⟨1502,⟨1,1,3997,0⟩⟩,⟨1538,⟨1,1,4093,0⟩⟩,⟨1568,⟨1,1,4189,0⟩⟩,⟨1604,⟨1,1,4285,0⟩⟩,⟨1641,⟨1,1,4381,0⟩⟩,⟨1677,⟨1,1,4477,0⟩⟩,⟨1713,⟨1,1,4573,0⟩⟩,⟨1749,⟨1,1,4669,0⟩⟩,⟨1786,⟨1,1,4765,0⟩⟩,⟨1822,⟨1,1,4861,0⟩⟩,⟨1857,⟨1,1,4957,0⟩⟩,⟨1893,⟨1,1,5053,0⟩⟩,⟨1930,⟨1,1,5149,0⟩⟩,⟨1966,⟨1,1,5245,0⟩⟩,⟨2002,⟨1,1,5341,0⟩⟩,⟨2038,⟨1,1,5437,0⟩⟩]
def bkt_3 : List kernel := [⟨14,⟨1,1,31,0⟩⟩,⟨51,⟨1,1,127,0⟩⟩,⟨87,⟨1,1,223,0⟩⟩,⟨122,⟨1,1,319,0⟩⟩,⟨158,⟨1,1,415,0⟩⟩,⟨195,⟨1,1,511,0⟩⟩,⟨231,⟨1,1,607,0⟩⟩,⟨267,⟨1,1,703,0⟩⟩,⟨303,⟨1,1,799,0⟩⟩,⟨340,⟨1,1,895,0⟩⟩,⟨376,⟨1,1,991,0⟩⟩,⟨408,⟨1,1,1087,0⟩⟩,⟨444,⟨1,1,1183,0⟩⟩,⟨481,⟨1,1,1279,0⟩⟩,⟨517,⟨1,1,1375,0⟩⟩,⟨553,⟨1,1,1471,0⟩⟩,⟨589,⟨1,1,1567,0⟩⟩,⟨626,⟨1,1,1663,0⟩⟩,⟨662,⟨1,1,1759,0⟩⟩,⟨697,⟨1,1,1855,0⟩⟩,⟨733,⟨1,1,1951,0⟩⟩,⟨770,⟨1,1,2047,0⟩⟩,⟨806,⟨1,1,2143,0⟩⟩,⟨842,⟨1,1,2239,0⟩⟩,⟨878,⟨1,1,2335,0⟩⟩,⟨915,⟨1,1,2431,0⟩⟩,⟨951,⟨1,1,2527,0⟩⟩,⟨982,⟨1,1,2623,0⟩⟩,⟨1018,⟨1,1,2719,0⟩⟩,⟨1055,⟨1,1,2815,0⟩⟩,⟨1091,⟨1,1,2911,0⟩⟩,⟨1127,⟨1,1,3007,0⟩⟩,⟨1163,⟨1,1,3103,0⟩⟩,⟨1200,⟨1,1,3199,0⟩⟩,⟨1236,⟨1,1,3295,0⟩⟩,⟨1271,⟨1,1,3391,0⟩⟩,⟨1307,⟨1,1,3487,0⟩⟩,⟨1344,⟨1,1,3583,0⟩⟩,⟨1380,⟨1,1,3679,0⟩⟩,⟨1416,⟨1,1,3775,0⟩⟩,⟨1452,⟨1,1,3871,0⟩⟩,⟨1489,⟨1,1,3967,0⟩⟩,⟨1525,⟨1,1,4063,0⟩⟩,⟨1555,⟨1,1,4159,0⟩⟩,⟨1591,⟨1,1,4255,0⟩⟩,⟨1628,⟨1,1,4351,0⟩⟩,⟨1664,⟨1,1,4447,0⟩⟩,⟨1700,⟨1,1,4543,0⟩⟩,⟨1736,⟨1,1,4639,0⟩⟩,⟨1773,⟨1,1,4735,0⟩⟩,⟨1809,⟨1,1,4831,0⟩⟩,⟨1844,⟨1,1,4927,0⟩⟩,⟨1880,⟨1,1,5023,0⟩⟩,⟨1917,⟨1,1,5119,0⟩⟩,⟨1953,⟨1,1,5215,0⟩⟩,⟨1989,⟨1,1,5311,0⟩⟩,⟨2025,⟨1,1,5407,0⟩⟩]
def bkt_5 : List kernel := [⟨40,⟨1,1,97,0⟩⟩,⟨76,⟨1,1,193,0⟩⟩,⟨111,⟨1,1,289,0⟩⟩,⟨147,⟨1,1,385,0⟩⟩,⟨184,⟨1,1,481,0⟩⟩,⟨220,⟨1,1,577,0⟩⟩,⟨256,⟨1,1,673,0⟩⟩,⟨292,⟨1,1,769,0⟩⟩,⟨329,⟨1,1,865,0⟩⟩,⟨365,⟨1,1,961,0⟩⟩,⟨397,⟨1,1,1057,0⟩⟩,⟨433,⟨1,1,1153,0⟩⟩,⟨470,⟨1,1,1249,0⟩⟩,⟨506,⟨1,1,1345,0⟩⟩,⟨542,⟨1,1,1441,0⟩⟩,⟨578,⟨1,1,1537,0⟩⟩,⟨615,⟨1,1,1633,0⟩⟩,⟨651,⟨1,1,1729,0⟩⟩,⟨686,⟨1,1,1825,0⟩⟩,⟨722,⟨1,1,1921,0⟩⟩,⟨759,⟨1,1,2017,0⟩⟩,⟨795,⟨1,1,2113,0⟩⟩,⟨831,⟨1,1,2209,0⟩⟩,⟨867,⟨1,1,2305,0⟩⟩,⟨904,⟨1,1,2401,0⟩⟩,⟨940,⟨1,1,2497,0⟩⟩,⟨971,⟨1,1,2593,0⟩⟩,⟨1007,⟨1,1,2689,0⟩⟩,⟨1044,⟨1,1,2785,0⟩⟩,⟨1080,⟨1,1,2881,0⟩⟩,⟨1116,⟨1,1,2977,0⟩⟩,⟨1152,⟨1,1,3073,0⟩⟩,⟨1189,⟨1,1,3169,0⟩⟩,⟨1225,⟨1,1,3265,0⟩⟩,⟨1260,⟨1,1,3361,0⟩⟩,⟨1296,⟨1,1,3457,0⟩⟩,⟨1333,⟨1,1,3553,0⟩⟩,⟨1369,⟨1,1,3649,0⟩⟩,⟨1405,⟨1,1,3745,0⟩⟩,⟨1441,⟨1,1,3841,0⟩⟩,⟨1478,⟨1,1,3937,0⟩⟩,⟨1514,⟨1,1,4033,0⟩⟩,⟨1544,⟨1,1,4129,0⟩⟩,⟨1580,⟨1,1,4225,0⟩⟩,⟨1617,⟨1,1,4321,0⟩⟩,⟨1653,⟨1,1,4417,0⟩⟩,⟨1689,⟨1,1,4513,0⟩⟩,⟨1725,⟨1,1,4609,0⟩⟩,⟨1762,⟨1,1,4705,0⟩⟩,⟨1798,⟨1,1,4801,0⟩⟩,⟨1833,⟨1,1,4897,0⟩⟩,⟨1869,⟨1,1,4993,0⟩⟩,⟨1906,⟨1,1,5089,0⟩⟩,⟨1942,⟨1,1,5185,0⟩⟩,⟨1978,⟨1,1,5281,0⟩⟩,⟨2014,⟨1,1,5377,0⟩⟩]
def bkt_7 : List kernel := []
def bkt_9 : List kernel := [⟨17,⟨1,1,37,0⟩⟩,⟨54,⟨1,1,133,0⟩⟩,⟨90,⟨1,1,229,0⟩⟩,⟨125,⟨1,1,325,0⟩⟩,⟨161,⟨1,1,421,0⟩⟩,⟨198,⟨1,1,517,0⟩⟩,⟨234,⟨1,1,613,0⟩⟩,⟨270,⟨1,1,709,0⟩⟩,⟨306,⟨1,1,805,0⟩⟩,⟨343,⟨1,1,901,0⟩⟩,⟨379,⟨1,1,997,0⟩⟩,⟨411,⟨1,1,1093,0⟩⟩,⟨447,⟨1,1,1189,0⟩⟩,⟨484,⟨1,1,1285,0⟩⟩,⟨520,⟨1,1,1381,0⟩⟩,⟨556,⟨1,1,1477,0⟩⟩,⟨592,⟨1,1,1573,0⟩⟩,⟨629,⟨1,1,1669,0⟩⟩,⟨665,⟨1,1,1765,0⟩⟩,⟨700,⟨1,1,1861,0⟩⟩,⟨736,⟨1,1,1957,0⟩⟩,⟨773,⟨1,1,2053,0⟩⟩,⟨809,⟨1,1,2149,0⟩⟩,⟨845,⟨1,1,2245,0⟩⟩,⟨881,⟨1,1,2341,0⟩⟩,⟨918,⟨1,1,2437,0⟩⟩,⟨954,⟨1,1,2533,0⟩⟩,⟨985,⟨1,1,2629,0⟩⟩,⟨1021,⟨1,1,2725,0⟩⟩,⟨1058,⟨1,1,2821,0⟩⟩,⟨1094,⟨1,1,2917,0⟩⟩,⟨1130,⟨1,1,3013,0⟩⟩,⟨1166,⟨1,1,3109,0⟩⟩,⟨1203,⟨1,1,3205,0⟩⟩,⟨1239,⟨1,1,3301,0⟩⟩,⟨1274,⟨1,1,3397,0⟩⟩,⟨1310,⟨1,1,3493,0⟩⟩,⟨1347,⟨1,1,3589,0⟩⟩,⟨1383,⟨1,1,3685,0⟩⟩,⟨1419,⟨1,1,3781,0⟩⟩,⟨1455,⟨1,1,3877,0⟩⟩,⟨1492,⟨1,1,3973,0⟩⟩,⟨1528,⟨1,1,4069,0⟩⟩,⟨1558,⟨1,1,4165,0⟩⟩,⟨1594,⟨1,1,4261,0⟩⟩,⟨1631,⟨1,1,4357,0⟩⟩,⟨1667,⟨1,1,4453,0⟩⟩,⟨1703,⟨1,1,4549,0⟩⟩,⟨1739,⟨1,1,4645,0⟩⟩,⟨1776,⟨1,1,4741,0⟩⟩,⟨1812,⟨1,1,4837,0⟩⟩,⟨1847,⟨1,1,4933,0⟩⟩,⟨1883,⟨1,1,5029,0⟩⟩,⟨1920,⟨1,1,5125,0⟩⟩,⟨1956,⟨1,1,5221,0⟩⟩,⟨1992,⟨1,1,5317,0⟩⟩,⟨2028,⟨1,1,5413,0⟩⟩]
def bkt_11 : List kernel := [⟨42,⟨1,1,103,0⟩⟩,⟨78,⟨1,1,199,0⟩⟩,⟨113,⟨1,1,295,0⟩⟩,⟨149,⟨1,1,391,0⟩⟩,⟨186,⟨1,1,487,0⟩⟩,⟨222,⟨1,1,583,0⟩⟩,⟨258,⟨1,1,679,0⟩⟩,⟨294,⟨1,1,775,0⟩⟩,⟨331,⟨1,1,871,0⟩⟩,⟨367,⟨1,1,967,0⟩⟩,⟨399,⟨1,1,1063,0⟩⟩,⟨435,⟨1,1,1159,0⟩⟩,⟨472,⟨1,1,1255,0⟩⟩,⟨508,⟨1,1,1351,0⟩⟩,⟨544,⟨1,1,1447,0⟩⟩,⟨580,⟨1,1,1543,0⟩⟩,⟨617,⟨1,1,1639,0⟩⟩,⟨653,⟨1,1,1735,0⟩⟩,⟨688,⟨1,1,1831,0⟩⟩,⟨724,⟨1,1,1927,0⟩⟩,⟨761,⟨1,1,2023,0⟩⟩,⟨797,⟨1,1,2119,0⟩⟩,⟨833,⟨1,1,2215,0⟩⟩,⟨869,⟨1,1,2311,0⟩⟩,⟨906,⟨1,1,2407,0⟩⟩,⟨942,⟨1,1,2503,0⟩⟩,⟨973,⟨1,1,2599,0⟩⟩,⟨1009,⟨1,1,2695,0⟩⟩,⟨1046,⟨1,1,2791,0⟩⟩,⟨1082,⟨1,1,2887,0⟩⟩,⟨1118,⟨1,1,2983,0⟩⟩,⟨1154,⟨1,1,3079,0⟩⟩,⟨1191,⟨1,1,3175,0⟩⟩,⟨1227,⟨1,1,3271,0⟩⟩,⟨1262,⟨1,1,3367,0⟩⟩,⟨1298,⟨1,1,3463,0⟩⟩,⟨1335,⟨1,1,3559,0⟩⟩,⟨1371,⟨1,1,3655,0⟩⟩,⟨1407,⟨1,1,3751,0⟩⟩,⟨1443,⟨1,1,3847,0⟩⟩,⟨1480,⟨1,1,3943,0⟩⟩,⟨1516,⟨1,1,4039,0⟩⟩,⟨1546,⟨1,1,4135,0⟩⟩,⟨1582,⟨1,1,4231,0⟩⟩,⟨1619,⟨1,1,4327,0⟩⟩,⟨1655,⟨1,1,4423,0⟩⟩,⟨1691,⟨1,1,4519,0⟩⟩,⟨1727,⟨1,1,4615,0⟩⟩,⟨1764,⟨1,1,4711,0⟩⟩,⟨1800,⟨1,1,4807,0⟩⟩,⟨1835,⟨1,1,4903,0⟩⟩,⟨1871,⟨1,1,4999,0⟩⟩,⟨1908,⟨1,1,5095,0⟩⟩,⟨1944,⟨1,1,5191,0⟩⟩,⟨1980,⟨1,1,5287,0⟩⟩,⟨2016,⟨1,1,5383,0⟩⟩]
def bkt_13 : List kernel := []
def bkt_15 : List kernel := [⟨101,⟨3,3,141,127⟩⟩,⟨676,⟨3,3,909,895⟩⟩,⟨1250,⟨3,3,1677,1663⟩⟩,⟨1823,⟨3,3,2445,2431⟩⟩]
def bkt_17 : List kernel := [⟨8,⟨1,1,13,0⟩⟩,⟨45,⟨1,1,109,0⟩⟩,⟨81,⟨1,1,205,0⟩⟩,⟨116,⟨1,1,301,0⟩⟩,⟨152,⟨1,1,397,0⟩⟩,⟨189,⟨1,1,493,0⟩⟩,⟨225,⟨1,1,589,0⟩⟩,⟨261,⟨1,1,685,0⟩⟩,⟨297,⟨1,1,781,0⟩⟩,⟨334,⟨1,1,877,0⟩⟩,⟨370,⟨1,1,973,0⟩⟩,⟨402,⟨1,1,1069,0⟩⟩,⟨438,⟨1,1,1165,0⟩⟩,⟨475,⟨1,1,1261,0⟩⟩,⟨511,⟨1,1,1357,0⟩⟩,⟨547,⟨1,1,1453,0⟩⟩,⟨583,⟨1,1,1549,0⟩⟩,⟨620,⟨1,1,1645,0⟩⟩,⟨656,⟨1,1,1741,0⟩⟩,⟨691,⟨1,1,1837,0⟩⟩,⟨727,⟨1,1,1933,0⟩⟩,⟨764,⟨1,1,2029,0⟩⟩,⟨800,⟨1,1,2125,0⟩⟩,⟨836,⟨1,1,2221,0⟩⟩,⟨872,⟨1,1,2317,0⟩⟩,⟨909,⟨1,1,2413,0⟩⟩,⟨945,⟨1,1,2509,0⟩⟩,⟨976,⟨1,1,2605,0⟩⟩,⟨1012,⟨1,1,2701,0⟩⟩,⟨1049,⟨1,1,2797,0⟩⟩,⟨1085,⟨1,1,2893,0⟩⟩,⟨1121,⟨1,1,2989,0⟩⟩,⟨1157,⟨1,1,3085,0⟩⟩,⟨1194,⟨1,1,3181,0⟩⟩,⟨1230,⟨1,1,3277,0⟩⟩,⟨1265,⟨1,1,3373,0⟩⟩,⟨1301,⟨1,1,3469,0⟩⟩,⟨1338,⟨1,1,3565,0⟩⟩,⟨1374,⟨1,1,3661,0⟩⟩,⟨1410,⟨1,1,3757,0⟩⟩,⟨1446,⟨1,1,3853,0⟩⟩,⟨1483,⟨1,1,3949,0⟩⟩,⟨1519,⟨1,1,4045,0⟩⟩,⟨1549,⟨1,1,4141,0⟩⟩,⟨1585,⟨1,1,4237,0⟩⟩,⟨1622,⟨1,1,4333,0⟩⟩,⟨1658,⟨1,1,4429,0⟩⟩,⟨1694,⟨1,1,4525,0⟩⟩,⟨1730,⟨1,1,4621,0⟩⟩,⟨1767,⟨1,1,4717,0⟩⟩,⟨1803,⟨1,1,4813,0⟩⟩,⟨1838,⟨1,1,4909,0⟩⟩,⟨1874,⟨1,1,5005,0⟩⟩,⟨1911,⟨1,1,5101,0⟩⟩,⟨1947,⟨1,1,5197,0⟩⟩,⟨1983,⟨1,1,5293,0⟩⟩,⟨2019,⟨1,1,5389,0⟩⟩]
def bkt_19 : List kernel := [⟨32,⟨1,1,79,0⟩⟩,⟨68,⟨1,1,175,0⟩⟩,⟨139,⟨1,1,367,0⟩⟩,⟨176,⟨1,1,463,0⟩⟩,⟨212,⟨1,1,559,0⟩⟩,⟨248,⟨1,1,655,0⟩⟩,⟨284,⟨1,1,751,0⟩⟩,⟨321,⟨1,1,847,0⟩⟩,⟨357,⟨1,1,943,0⟩⟩,⟨425,⟨1,1,1135,0⟩⟩,⟨462,⟨1,1,1231,0⟩⟩,⟨498,⟨1,1,1327,0⟩⟩,⟨534,⟨1,1,1423,0⟩⟩,⟨570,⟨1,1,1519,0⟩⟩,⟨607,⟨1,1,1615,0⟩⟩,⟨643,⟨1,1,1711,0⟩⟩,⟨714,⟨1,1,1903,0⟩⟩,⟨751,⟨1,1,1999,0⟩⟩,⟨787,⟨1,1,2095,0⟩⟩,⟨823,⟨1,1,2191,0⟩⟩,⟨859,⟨1,1,2287,0⟩⟩,⟨896,⟨1,1,2383,0⟩⟩,⟨932,⟨1,1,2479,0⟩⟩,⟨999,⟨1,1,2671,0⟩⟩,⟨1036,⟨1,1,2767,0⟩⟩,⟨1072,⟨1,1,2863,0⟩⟩,⟨1108,⟨1,1,2959,0⟩⟩,⟨1144,⟨1,1,3055,0⟩⟩,⟨1181,⟨1,1,3151,0⟩⟩,⟨1217,⟨1,1,3247,0⟩⟩,⟨1288,⟨1,1,3439,0⟩⟩,⟨1325,⟨1,1,3535,0⟩⟩,⟨1361,⟨1,1,3631,0⟩⟩,⟨1397,⟨1,1,3727,0⟩⟩,⟨1433,⟨1,1,3823,0⟩⟩,⟨1470,⟨1,1,3919,0⟩⟩,⟨1506,⟨1,1,4015,0⟩⟩,⟨1572,⟨1,1,4207,0⟩⟩,⟨1609,⟨1,1,4303,0⟩⟩,⟨1645,⟨1,1,4399,0⟩⟩,⟨1681,⟨1,1,4495,0⟩⟩,⟨1717,⟨1,1,4591,0⟩⟩,⟨1754,⟨1,1,4687,0⟩⟩,⟨1790,⟨1,1,4783,0⟩⟩,⟨1861,⟨1,1,4975,0⟩⟩,⟨1898,⟨1,1,5071,0⟩⟩,⟨1934,⟨1,1,5167,0⟩⟩,⟨1970,⟨1,1,5263,0⟩⟩,⟨2006,⟨1,1,5359,0⟩⟩,⟨2043,⟨1,1,5455,0⟩⟩]
def bkt_21 : List kernel := [⟨22,⟨1,1,49,0⟩⟩,⟨59,⟨1,1,145,0⟩⟩,⟨95,⟨1,1,241,0⟩⟩,⟨130,⟨1,1,337,0⟩⟩,⟨166,⟨1,1,433,0⟩⟩,⟨203,⟨1,1,529,0⟩⟩,⟨239,⟨1,1,625,0⟩⟩,⟨275,⟨1,1,721,0⟩⟩,⟨311,⟨1,1,817,0⟩⟩,⟨348,⟨1,1,913,0⟩⟩,⟨384,⟨1,1,1009,0⟩⟩,⟨416,⟨1,1,1105,0⟩⟩,⟨452,⟨1,1,1201,0⟩⟩,⟨489,⟨1,1,1297,0⟩⟩,⟨525,⟨1,1,1393,0⟩⟩,⟨561,⟨1,1,1489,0⟩⟩,⟨597,⟨1,1,1585,0⟩⟩,⟨634,⟨1,1,1681,0⟩⟩,⟨670,⟨1,1,1777,0⟩⟩,⟨705,⟨1,1,1873,0⟩⟩,⟨741,⟨1,1,1969,0⟩⟩,⟨778,⟨1,1,2065,0⟩⟩,⟨814,⟨1,1,2161,0⟩⟩,⟨850,⟨1,1,2257,0⟩⟩,⟨886,⟨1,1,2353,0⟩⟩,⟨923,⟨1,1,2449,0⟩⟩,⟨959,⟨1,1,2545,0⟩⟩,⟨990,⟨1,1,2641,0⟩⟩,⟨1026,⟨1,1,2737,0⟩⟩,⟨1063,⟨1,1,2833,0⟩⟩,⟨1099,⟨1,1,2929,0⟩⟩,⟨1135,⟨1,1,3025,0⟩⟩,⟨1171,⟨1,1,3121,0⟩⟩,⟨1208,⟨1,1,3217,0⟩⟩,⟨1244,⟨1,1,3313,0⟩⟩,⟨1279,⟨1,1,3409,0⟩⟩,⟨1315,⟨1,1,3505,0⟩⟩,⟨1352,⟨1,1,3601,0⟩⟩,⟨1388,⟨1,1,3697,0⟩⟩,⟨1424,⟨1,1,3793,0⟩⟩,⟨1460,⟨1,1,3889,0⟩⟩,⟨1497,⟨1,1,3985,0⟩⟩,⟨1533,⟨1,1,4081,0⟩⟩,⟨1563,⟨1,1,4177,0⟩⟩,⟨1599,⟨1,1,4273,0⟩⟩,⟨1636,⟨1,1,4369,0⟩⟩,⟨1672,⟨1,1,4465,0⟩⟩,⟨1708,⟨1,1,4561,0⟩⟩,⟨1744,⟨1,1,4657,0⟩⟩,⟨1781,⟨1,1,4753,0⟩⟩,⟨1817,⟨1,1,4849,0⟩⟩,⟨1852,⟨1,1,4945,0⟩⟩,⟨1888,⟨1,1,5041,0⟩⟩,⟨1925,⟨1,1,5137,0⟩⟩,⟨1961,⟨1,1,5233,0⟩⟩,⟨1997,⟨1,1,5329,0⟩⟩,⟨2033,⟨1,1,5425,0⟩⟩]
def bkt_23 : List kernel := []
def bkt_25 : List kernel := [⟨35,⟨1,1,85,0⟩⟩,⟨65,⟨3,3,87,79⟩⟩,⟨71,⟨1,1,181,0⟩⟩,⟨106,⟨1,1,277,0⟩⟩,⟨136,⟨3,3,183,175⟩⟩,⟨142,⟨1,1,373,0⟩⟩,⟨179,⟨1,1,469,0⟩⟩,⟨209,⟨3,3,279,271⟩⟩,⟨215,⟨1,1,565,0⟩⟩,⟨251,⟨1,1,661,0⟩⟩,⟨281,⟨3,3,375,367⟩⟩,⟨287,⟨1,1,757,0⟩⟩,⟨324,⟨1,1,853,0⟩⟩,⟨354,⟨3,3,471,463⟩⟩,⟨360,⟨1,1,949,0⟩⟩,⟨422,⟨3,3,567,559⟩⟩,⟨428,⟨1,1,1141,0⟩⟩,⟨465,⟨1,1,1237,0⟩⟩,⟨495,⟨3,3,663,655⟩⟩,⟨501,⟨1,1,1333,0⟩⟩,⟨537,⟨1,1,1429,0⟩⟩,⟨567,⟨3,3,759,751⟩⟩,⟨573,⟨1,1,1525,0⟩⟩,⟨610,⟨1,1,1621,0⟩⟩,⟨640,⟨3,3,855,847⟩⟩,⟨646,⟨1,1,1717,0⟩⟩,⟨681,⟨1,1,1813,0⟩⟩,⟨711,⟨3,3,951,943⟩⟩,⟨717,⟨1,1,1909,0⟩⟩,⟨754,⟨1,1,2005,0⟩⟩,⟨784,⟨3,3,1047,1039⟩⟩,⟨790,⟨1,1,2101,0⟩⟩,⟨826,⟨1,1,2197,0⟩⟩,⟨856,⟨3,3,1143,1135⟩⟩,⟨862,⟨1,1,2293,0⟩⟩,⟨899,⟨1,1,2389,0⟩⟩,⟨929,⟨3,3,1239,1231⟩⟩,⟨935,⟨1,1,2485,0⟩⟩,⟨966,⟨1,1,2581,0⟩⟩,⟨996,⟨3,3,1335,1327⟩⟩,⟨1002,⟨1,1,2677,0⟩⟩,⟨1039,⟨1,1,2773,0⟩⟩,⟨1069,⟨3,3,1431,1423⟩⟩,⟨1075,⟨1,1,2869,0⟩⟩,⟨1111,⟨1,1,2965,0⟩⟩,⟨1141,⟨3,3,1527,1519⟩⟩,⟨1147,⟨1,1,3061,0⟩⟩,⟨1184,⟨1,1,3157,0⟩⟩,⟨1214,⟨3,3,1623,1615⟩⟩,⟨1220,⟨1,1,3253,0⟩⟩,⟨1255,⟨1,1,3349,0⟩⟩,⟨1285,⟨3,3,1719,1711⟩⟩,⟨1291,⟨1,1,3445,0⟩⟩,⟨1328,⟨1,1,3541,0⟩⟩,⟨1358,⟨3,3,1815,1807⟩⟩,⟨1364,⟨1,1,3637,0⟩⟩,⟨1400,⟨1,1,3733,0⟩⟩,⟨1430,⟨3,3,1911,1903⟩⟩,⟨1436,⟨1,1,3829,0⟩⟩,⟨1473,⟨1,1,3925,0⟩⟩,⟨1503,⟨3,3,2007,1999⟩⟩,⟨1509,⟨1,1,4021,0⟩⟩,⟨1569,⟨3,3,2103,2095⟩⟩,⟨1575,⟨1,1,4213,0⟩⟩,⟨1612,⟨1,1,4309,0⟩⟩,⟨1642,⟨3,3,2199,2191⟩⟩,⟨1648,⟨1,1,4405,0⟩⟩,⟨1684,⟨1,1,4501,0⟩⟩,⟨1714,⟨3,3,2295,2287⟩⟩,⟨1720,⟨1,1,4597,0⟩⟩,⟨1757,⟨1,1,4693,0⟩⟩,⟨1787,⟨3,3,2391,2383⟩⟩,⟨1793,⟨1,1,4789,0⟩⟩,⟨1828,⟨1,1,4885,0⟩⟩,⟨1858,⟨3,3,2487,2479⟩⟩,⟨1864,⟨1,1,4981,0⟩⟩,⟨1901,⟨1,1,5077,0⟩⟩,⟨1931,⟨3,3,2583,2575⟩⟩,⟨1937,⟨1,1,5173,0⟩⟩,⟨1973,⟨1,1,5269,0⟩⟩,⟨2003,⟨3,3,2679,2671⟩⟩,⟨2009,⟨1,1,5365,0⟩⟩,⟨2046,⟨1,1,5461,0⟩⟩]
def bkt_27 : List kernel := [⟨5,⟨1,1,7,0⟩⟩,⟨24,⟨1,1,55,0⟩⟩,⟨61,⟨1,1,151,0⟩⟩,⟨97,⟨1,1,247,0⟩⟩,⟨132,⟨1,1,343,0⟩⟩,⟨168,⟨1,1,439,0⟩⟩,⟨205,⟨1,1,535,0⟩⟩,⟨241,⟨1,1,631,0⟩⟩,⟨277,⟨1,1,727,0⟩⟩,⟨313,⟨1,1,823,0⟩⟩,⟨350,⟨1,1,919,0⟩⟩,⟨386,⟨1,1,1015,0⟩⟩,⟨418,⟨1,1,1111,0⟩⟩,⟨454,⟨1,1,1207,0⟩⟩,⟨491,⟨1,1,1303,0⟩⟩,⟨527,⟨1,1,1399,0⟩⟩,⟨563,⟨1,1,1495,0⟩⟩,⟨599,⟨1,1,1591,0⟩⟩,⟨636,⟨1,1,1687,0⟩⟩,⟨672,⟨1,1,1783,0⟩⟩,⟨707,⟨1,1,1879,0⟩⟩,⟨743,⟨1,1,1975,0⟩⟩,⟨780,⟨1,1,2071,0⟩⟩,⟨816,⟨1,1,2167,0⟩⟩,⟨852,⟨1,1,2263,0⟩⟩,⟨888,⟨1,1,2359,0⟩⟩,⟨925,⟨1,1,2455,0⟩⟩,⟨961,⟨1,1,2551,0⟩⟩,⟨992,⟨1,1,2647,0⟩⟩,⟨1028,⟨1,1,2743,0⟩⟩,⟨1065,⟨1,1,2839,0⟩⟩,⟨1101,⟨1,1,2935,0⟩⟩,⟨1137,⟨1,1,3031,0⟩⟩,⟨1173,⟨1,1,3127,0⟩⟩,⟨1210,⟨1,1,3223,0⟩⟩,⟨1246,⟨1,1,3319,0⟩⟩,⟨1281,⟨1,1,3415,0⟩⟩,⟨1317,⟨1,1,3511,0⟩⟩,⟨1354,⟨1,1,3607,0⟩⟩,⟨1390,⟨1,1,3703,0⟩⟩,⟨1426,⟨1,1,3799,0⟩⟩,⟨1462,⟨1,1,3895,0⟩⟩,⟨1499,⟨1,1,3991,0⟩⟩,⟨1535,⟨1,1,4087,0⟩⟩,⟨1539,⟨3,3,2073,2047⟩⟩,⟨1565,⟨1,1,4183,0⟩⟩,⟨1601,⟨1,1,4279,0⟩⟩,⟨1638,⟨1,1,4375,0⟩⟩,⟨1674,⟨1,1,4471,0⟩⟩,⟨1710,⟨1,1,4567,0⟩⟩,⟨1746,⟨1,1,4663,0⟩⟩,⟨1783,⟨1,1,4759,0⟩⟩,⟨1819,⟨1,1,4855,0⟩⟩,⟨1854,⟨1,1,4951,0⟩⟩,⟨1890,⟨1,1,5047,0⟩⟩,⟨1927,⟨1,1,5143,0⟩⟩,⟨1963,⟨1,1,5239,0⟩⟩,⟨1999,⟨1,1,5335,0⟩⟩,⟨2035,⟨1,1,5431,0⟩⟩]
def bkt_29 : List kernel := [⟨12,⟨1,1,25,0⟩⟩,⟨49,⟨1,1,121,0⟩⟩,⟨85,⟨1,1,217,0⟩⟩,⟨120,⟨1,1,313,0⟩⟩,⟨156,⟨1,1,409,0⟩⟩,⟨193,⟨1,1,505,0⟩⟩,⟨229,⟨1,1,601,0⟩⟩,⟨265,⟨1,1,697,0⟩⟩,⟨301,⟨1,1,793,0⟩⟩,⟨338,⟨1,1,889,0⟩⟩,⟨374,⟨1,1,985,0⟩⟩,⟨406,⟨1,1,1081,0⟩⟩,⟨442,⟨1,1,1177,0⟩⟩,⟨479,⟨1,1,1273,0⟩⟩,⟨515,⟨1,1,1369,0⟩⟩,⟨551,⟨1,1,1465,0⟩⟩,⟨587,⟨1,1,1561,0⟩⟩,⟨624,⟨1,1,1657,0⟩⟩,⟨660,⟨1,1,1753,0⟩⟩,⟨695,⟨1,1,1849,0⟩⟩,⟨731,⟨1,1,1945,0⟩⟩,⟨768,⟨1,1,2041,0⟩⟩,⟨804,⟨1,1,2137,0⟩⟩,⟨840,⟨1,1,2233,0⟩⟩,⟨876,⟨1,1,2329,0⟩⟩,⟨913,⟨1,1,2425,0⟩⟩,⟨949,⟨1,1,2521,0⟩⟩,⟨980,⟨1,1,2617,0⟩⟩,⟨1016,⟨1,1,2713,0⟩⟩,⟨1053,⟨1,1,2809,0⟩⟩,⟨1089,⟨1,1,2905,0⟩⟩,⟨1125,⟨1,1,3001,0⟩⟩,⟨1161,⟨1,1,3097,0⟩⟩,⟨1198,⟨1,1,3193,0⟩⟩,⟨1234,⟨1,1,3289,0⟩⟩,⟨1269,⟨1,1,3385,0⟩⟩,⟨1305,⟨1,1,3481,0⟩⟩,⟨1342,⟨1,1,3577,0⟩⟩,⟨1378,⟨1,1,3673,0⟩⟩,⟨1414,⟨1,1,3769,0⟩⟩,⟨1450,⟨1,1,3865,0⟩⟩,⟨1487,⟨1,1,3961,0⟩⟩,⟨1523,⟨1,1,4057,0⟩⟩,⟨1553,⟨1,1,4153,0⟩⟩,⟨1589,⟨1,1,4249,0⟩⟩,⟨1626,⟨1,1,4345,0⟩⟩,⟨1662,⟨1,1,4441,0⟩⟩,⟨1698,⟨1,1,4537,0⟩⟩,⟨1734,⟨1,1,4633,0⟩⟩,⟨1771,⟨1,1,4729,0⟩⟩,⟨1807,⟨1,1,4825,0⟩⟩,⟨1842,⟨1,1,4921,0⟩⟩,⟨1878,⟨1,1,5017,0⟩⟩,⟨1915,⟨1,1,5113,0⟩⟩,⟨1951,⟨1,1,5209,0⟩⟩,⟨1987,⟨1,1,5305,0⟩⟩,⟨2023,⟨1,1,5401,0⟩⟩]
def bkt_31 : List kernel := [⟨394,⟨1,1,1051,0⟩⟩]
def cands_5 : List kernel := [⟨17,⟨1,1,37,0⟩⟩,⟨54,⟨1,1,133,0⟩⟩,⟨90,⟨1,1,229,0⟩⟩,⟨125,⟨1,1,325,0⟩⟩,⟨161,⟨1,1,421,0⟩⟩,⟨198,⟨1,1,517,0⟩⟩,⟨234,⟨1,1,613,0⟩⟩,⟨270,⟨1,1,709,0⟩⟩,⟨306,⟨1,1,805,0⟩⟩,⟨343,⟨1,1,901,0⟩⟩,⟨379,⟨1,1,997,0⟩⟩,⟨411,⟨1,1,1093,0⟩⟩,⟨447,⟨1,1,1189,0⟩⟩,⟨484,⟨1,1,1285,0⟩⟩,⟨520,⟨1,1,1381,0⟩⟩,⟨556,⟨1,1,1477,0⟩⟩,⟨592,⟨1,1,1573,0⟩⟩,⟨629,⟨1,1,1669,0⟩⟩,⟨665,⟨1,1,1765,0⟩⟩,⟨700,⟨1,1,1861,0⟩⟩,⟨736,⟨1,1,1957,0⟩⟩,⟨773,⟨1,1,2053,0⟩⟩,⟨809,⟨1,1,2149,0⟩⟩,⟨845,⟨1,1,2245,0⟩⟩,⟨881,⟨1,1,2341,0⟩⟩,⟨918,⟨1,1,2437,0⟩⟩,⟨954,⟨1,1,2533,0⟩⟩,⟨985,⟨1,1,2629,0⟩⟩,⟨1021,⟨1,1,2725,0⟩⟩,⟨1058,⟨1,1,2821,0⟩⟩,⟨1094,⟨1,1,2917,0⟩⟩,⟨1130,⟨1,1,3013,0⟩⟩,⟨1166,⟨1,1,3109,0⟩⟩,⟨1203,⟨1,1,3205,0⟩⟩,⟨1239,⟨1,1,3301,0⟩⟩,⟨1274,⟨1,1,3397,0⟩⟩,⟨1310,⟨1,1,3493,0⟩⟩,⟨1347,⟨1,1,3589,0⟩⟩,⟨1383,⟨1,1,3685,0⟩⟩,⟨1419,⟨1,1,3781,0⟩⟩,⟨1455,⟨1,1,3877,0⟩⟩,⟨1492,⟨1,1,3973,0⟩⟩,⟨1528,⟨1,1,4069,0⟩⟩,⟨1558,⟨1,1,4165,0⟩⟩,⟨1594,⟨1,1,4261,0⟩⟩,⟨1631,⟨1,1,4357,0⟩⟩,⟨1667,⟨1,1,4453,0⟩⟩,⟨1703,⟨1,1,4549,0⟩⟩,⟨1739,⟨1,1,4645,0⟩⟩,⟨1776,⟨1,1,4741,0⟩⟩,⟨1812,⟨1,1,4837,0⟩⟩,⟨1847,⟨1,1,4933,0⟩⟩,⟨1883,⟨1,1,5029,0⟩⟩,⟨1920,⟨1,1,5125,0⟩⟩,⟨1956,⟨1,1,5221,0⟩⟩,⟨1992,⟨1,1,5317,0⟩⟩,⟨2028,⟨1,1,5413,0⟩⟩]
def cands_8 : List kernel := [⟨139,⟨1,1,367,0⟩⟩,⟨425,⟨1,1,1135,0⟩⟩,⟨714,⟨1,1,1903,0⟩⟩,⟨999,⟨1,1,2671,0⟩⟩,⟨1288,⟨1,1,3439,0⟩⟩,⟨1572,⟨1,1,4207,0⟩⟩,⟨1861,⟨1,1,4975,0⟩⟩]

def qaG : state:=⟨none,0,1,0,0,0⟩
lemma initial_spec (S U : ℤ) : qE qaG S U S U:= by
  unfold qE qaG WordRelation.optional
  try dsimp -failIfUnchanged only
  refine ⟨by omega,⟨0,rfl⟩,by simp,by omega,trivial⟩

def get_bkt (r : ℤ) : List kernel :=
  if int_lt r 16 then
    if int_lt r 8 then
      if int_lt r 4 then
        if int_eq r 1 then bkt_1 else if int_eq r 3 then bkt_3 else []
      else
        if int_eq r 5 then bkt_5 else if int_eq r 7 then bkt_7 else []
    else
      if int_lt r 12 then
        if int_eq r 9 then bkt_9 else if int_eq r 11 then bkt_11 else []
      else
        if int_eq r 13 then bkt_13 else if int_eq r 15 then bkt_15 else []
  else
    if int_lt r 24 then
      if int_lt r 20 then
        if int_eq r 17 then bkt_17 else if int_eq r 19 then bkt_19 else []
      else
        if int_eq r 21 then bkt_21 else if int_eq r 23 then bkt_23 else []
    else
      if int_lt r 28 then
        if int_eq r 25 then bkt_25 else if int_eq r 27 then bkt_27 else []
      else
        if int_eq r 29 then bkt_29 else if int_eq r 31 then bkt_31 else []

def k_tag (k : kernel) : ℤ :=
  (2 * gain k - k.pair.b + (if int_eq k.index 5 then 16 else 0)) % 32

def k_req (kp : kernel) : ℤ :=
  (32 - ((kp.pair.b + (if int_eq kp.index 5 then 16 else 0)) % 32)) % 32

def get_cands_3 (kp : kernel) : List kernel :=
  if int_eq kp.index 5 then cands_5
  else if int_eq kp.index 8 then cands_8
  else
    q2 (k_req kp) fun r =>
    if int_eq r 27 then [⟨5,⟨1,1,7,0⟩⟩]
    else if int_eq r 17 then [⟨8,⟨1,1,13,0⟩⟩]
    else []

def get_cands (fuel : ℕ) (kp : kernel) : List kernel :=
  match fuel with
  | 0 => library_val
  | _ + 1 =>
    match Nat.ble 3 fuel with
    | true => get_cands_3 kp
    | false => get_bkt (k_req kp)

def qq16 (n x : ℤ) : ℤ :=
  if Nat.beq x.natAbs 0 then n else Int.ofNat (ctz_16 n.toNat x.natAbs)

def qbg5 (x : ℤ) : Bool :=
  Nat.beq (Nat.mod x.natAbs 32) 0

def single_small (v : ℤ) : Option kernel :=
  if int_eq v 5 then some ⟨5,⟨1,1,7,0⟩⟩
  else if int_eq v 8 then some ⟨8,⟨1,1,13,0⟩⟩
  else if int_eq v 12 then some ⟨12,⟨1,1,25,0⟩⟩
  else if int_eq v 14 then some ⟨14,⟨1,1,31,0⟩⟩
  else none

def int_min (a b : ℤ) : ℤ :=
  if int_le a b then a else b

def step_base (base m1 m2 : ℤ) : Bool × Option kernel :=
  q2 (int_min m1 m2) fun m_raw =>
  if int_lt m_raw 4 then (true, none)
  else
    q2 (int_min 15 (m_raw + 1)) fun m =>
    q2 (if int_eq m1 m2 then 0 else if int_le m_raw 14 then q0 m_raw else 0) fun adj =>
    q2 (base + adj) fun diff =>
    if !(qbg5 diff) then (false, none)
    else
      q2 (qq16 m diff) fun v =>
      if int_lt v m then
        match single_small v with
        | none => (false, none)
        | some k3 => (true, some k3)
      else (true, none)

def chain_simple : ℕ → kernel → kernel → Bool
  | 0, _, _ => true
  | fuel + 1, k1, k2 =>
    q2 (k1.index - k1.pair.d) fun m1 =>
    q2 (k2.index - k2.pair.d) fun m2 =>
    q2 (2 * gain k2 + k1.pair.b - k2.pair.b) fun base =>
    match step_base base m1 m2 with
    | (false, _) => false
    | (true, none) => true
    | (true, some k3) =>
      if !(chain_simple fuel k2 k3) then false
      else
        match fuel with
        | 0 => true
        | fuel2 + 1 =>
          if int_le k3.index (int_min m1 m2) then
            q2 (2 * gain k3 + k2.pair.b - k3.pair.b + base / 2) fun base_div =>
            match step_base base_div (m1 - 1) (m2 - 1) with
            | (false, _) => false
            | (true, none) => true
            | (true, some k4) => chain_simple fuel2 k3 k4
          else true

def eval_step_rel (fuel1 : ℕ) (base m1 : ℤ) (k_last : kernel) : Bool :=
  q2 (k_last.index - k_last.pair.d) fun m2 =>
  match step_base base m1 m2 with
  | (false, _) => false
  | (true, none) => true
  | (true, some k_next) =>
    if !(chain_simple fuel1 k_last k_next) then false
    else
      match fuel1 with
      | 0 => true
      | fuel2 + 1 =>
        if int_le k_next.index (int_min m1 m2) then
          q2 (2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2) fun base_div =>
          match step_base base_div (m1 - 1) (m2 - 1) with
          | (false, _) => false
          | (true, none) => true
          | (true, some k_next2) => chain_simple fuel2 k_next k_next2
        else true

def check_4k_simple (fuel : ℕ) (kp2 : Option kernel) (kp k : kernel) : Bool :=
  let ok4 :=
    match kp2, fuel with
    | none, _ => true
    | _, 0 => true
    | some k0, fuel1 + 1 =>
      if !(int_eq kp.pair.d 1) then true
      else
        q2 (k0.index - k0.pair.d) fun m1 =>
        q2 (2 * gain k - k.pair.b - k0.pair.b - 4) fun base =>
        eval_step_rel fuel1 base m1 k
  if !ok4 then false else chain_simple fuel kp k

def qJ_cands (fuel : ℕ) (min_idx : ℤ) (kp2 : Option kernel) (kp : kernel)
    (step : kernel → Bool) : List kernel → Bool
  | [] => true
  | k :: ks =>
    if int_le min_idx k.index then
      if check_4k_simple fuel kp2 kp k then
        if step k then qJ_cands fuel min_idx kp2 kp step ks else false
      else
        qJ_cands fuel min_idx kp2 kp step ks
    else
      qJ_cands fuel min_idx kp2 kp step ks

def qbN_c : ℕ → state → Option kernel → kernel → Bool
  | 0, _, _, _ => false
  | fuel + 1, z, kp2, kp =>
    match z.rel with
    | none => qJ_cands fuel 0 kp2 kp (fun k => qB (fun z' => qbN_c fuel z' (some kp) k) z k) (get_cands fuel kp)
    | some r =>
      q2 (A z) fun az =>
      q2 (B z) fun bz =>
      q2 (qa2 r az z.Q) fun bound =>
      q2 (qq bound (qa6 r az bz z.Q)) fun v =>
      if int_lt v bound then
        q2 (v - z.D) fun s =>
        qJ_cands fuel 0 kp2 kp (fun k => qB (fun z' => qbN_c fuel z' (some kp) k) z k) (single s)
      else
        q2 (bound - z.D) fun min_idx =>
        qJ_cands fuel min_idx kp2 kp (fun k => qB (fun z' => qbN_c fuel z' (some kp) k) z k) (get_cands fuel kp)

lemma int_le_iff (a b : ℤ) : int_le a b = true ↔ a ≤ b := by
  cases a <;> cases b <;> simp [int_le, Nat.ble_eq] <;> omega

lemma int_lt_iff (a b : ℤ) : int_lt a b = true ↔ a < b := by
  cases a <;> cases b <;> simp [int_lt, Nat.ble_eq] <;> omega

lemma int_eq_iff (a b : ℤ) : int_eq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [int_eq, Nat.beq_eq] <;> omega

lemma int_min_eq (a b : ℤ) : int_min a b = min a b := by
  unfold int_min
  split_ifs with h
  · rw [int_le_iff] at h; exact (min_eq_left h).symm
  · have h' : ¬ a ≤ b := fun hab => h ((int_le_iff a b).mpr hab)
    omega

lemma qq16_eq (n x : ℤ) : qq16 n x = qq n x := by
  unfold qq16 qq
  split_ifs with h
  · rfl
  · rw [ctz_16_eq, ctz_fast_eq]

lemma qbg5_iff (x : ℤ) : qbg5 x = true ↔ qa3 5 x := by
  have h5 : (0 : ℤ) ≤ 5 := by omega
  rw [← qbs h5]
  rfl

def lib_kernel_ok (k : kernel) : Bool :=
  decide (5 ≤ k.index) &&
  decide (1 ≤ k.pair.d) &&
  decide (4 ≤ k.index - k.pair.d) &&
  decide (k.index - k.pair.d = 4 ↔ k.index = 5) &&
  zodd k.pair.p &&
  zodd (q0 k.pair.d - k.pair.p) &&
  zodd (q0 (k.pair.d + 1) - k.pair.p) &&
  decide (k.pair.d = 1 → k.pair.p = 1 ∧ gain k = k.pair.b + 2) &&
  decide (k.index < 15 → single_small k.index = some k) &&
  decide (k ∈ get_bkt (k_tag k))

lemma lib_kernel_ok_all : qJ lib_kernel_ok library_val = true := by decide +kernel

lemma lib_kernel_props {k : kernel} (hk : k ∈ library_val) :
    5 ≤ k.index ∧
    1 ≤ k.pair.d ∧
    4 ≤ k.index - k.pair.d ∧
    (k.index - k.pair.d = 4 ↔ k.index = 5) ∧
    qW k.pair.p ∧
    qW (q0 k.pair.d - k.pair.p) ∧
    qW (q0 (k.pair.d + 1) - k.pair.p) ∧
    (k.pair.d = 1 → k.pair.p = 1 ∧ gain k = k.pair.b + 2) ∧
    (k.index < 15 → single_small k.index = some k) ∧
    k ∈ get_bkt (k_tag k) := by
  have h := qbf lib_kernel_ok library_val lib_kernel_ok_all k hk
  unfold lib_kernel_ok at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, zodd_iff] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2,
    h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

lemma single_small_props (v : ℤ) (k3 : kernel) (h : single_small v = some k3) :
    k3 ∈ library_val ∧ k3.index = v ∧ k3.pair.d = 1 ∧ k3.pair.p = 1 := by
  unfold single_small at h
  split_ifs at h with h5 h8 h12 h14
  · injection h with h; subst h; rw [int_eq_iff] at h5; subst h5
    exact ⟨by decide, rfl, rfl, rfl⟩
  · injection h with h; subst h; rw [int_eq_iff] at h8; subst h8
    exact ⟨by decide, rfl, rfl, rfl⟩
  · injection h with h; subst h; rw [int_eq_iff] at h12; subst h12
    exact ⟨by decide, rfl, rfl, rfl⟩
  · injection h with h; subst h; rw [int_eq_iff] at h14; subst h14
    exact ⟨by decide, rfl, rfl, rfl⟩

lemma odd_mul {x y : ℤ} (hx : qW x) (hy : qW y) : qW (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨2 * a * b + a + b, ?_⟩
  ring

lemma odd_neg {x : ℤ} (hx : qW x) : qW (-x) := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨-a - 1, ?_⟩
  ring

lemma odd_add_two_mul {x : ℤ} (y : ℤ) (hx : qW x) : qW (2 * y + x) := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨y + a, ?_⟩
  ring

lemma odd_pair_adj_dvd {m1 m2 u1 u2 : ℤ}
    (hm1 : 0 ≤ m1) (hm2 : 0 ≤ m2) (hu1 : qW u1) (hu2 : qW u2) :
    qa3 (min 15 (min m1 m2 + 1))
      (q0 m1 * u1 + q0 m2 * u2 -
        (if m1 = m2 then 0 else if min m1 m2 ≤ 14 then q0 (min m1 m2) else 0)) := by
  rcases hu1 with ⟨a, rfl⟩
  rcases hu2 with ⟨b, rfl⟩
  have hm_raw : 0 ≤ min m1 m2 := by omega
  have hm : 0 ≤ min 15 (min m1 m2 + 1) := by omega
  split_ifs with heq hle14
  · subst heq
    have hmin : min m1 m1 = m1 := min_self m1
    rw [hmin]
    apply qp (by omega) (by omega : min 15 (m1 + 1) ≤ m1 + 1)
    refine ⟨a + b + 1, ?_⟩
    rw [q5 hm1 (by omega : (0 : ℤ) ≤ 1), pow2_one]
    ring
  · apply qp hm (by omega : min 15 (min m1 m2 + 1) ≤ min m1 m2 + 1)
    rcases lt_trichotomy m1 m2 with hlt | h_eq | hgt
    · have hmin : min m1 m2 = m1 := min_eq_left (by omega)
      rw [hmin]
      have h1 : qa3 (m1 + 1) (q0 m1 * (2 * a + 1) - q0 m1) := by
        refine ⟨a, ?_⟩
        rw [q5 hm1 (by omega : (0 : ℤ) ≤ 1), pow2_one]
        ring
      have h2 : qa3 (m1 + 1) (q0 m2 * (2 * b + 1)) :=
        qp (by omega) (by omega : m1 + 1 ≤ m2) ⟨2 * b + 1, rfl⟩
      have hsum := div2_add h1 h2
      have heq_sum : q0 m1 * (2 * a + 1) - q0 m1 + q0 m2 * (2 * b + 1) =
          q0 m1 * (2 * a + 1) + q0 m2 * (2 * b + 1) - q0 m1 := by ring
      rwa [heq_sum] at hsum
    · exact absurd h_eq heq
    · have hmin : min m1 m2 = m2 := min_eq_right (by omega)
      rw [hmin]
      have h1 : qa3 (m2 + 1) (q0 m2 * (2 * b + 1) - q0 m2) := by
        refine ⟨b, ?_⟩
        rw [q5 hm2 (by omega : (0 : ℤ) ≤ 1), pow2_one]
        ring
      have h2 : qa3 (m2 + 1) (q0 m1 * (2 * a + 1)) :=
        qp (by omega) (by omega : m2 + 1 ≤ m1) ⟨2 * a + 1, rfl⟩
      have hsum := div2_add h2 h1
      have heq_sum : q0 m1 * (2 * a + 1) + (q0 m2 * (2 * b + 1) - q0 m2) =
          q0 m1 * (2 * a + 1) + q0 m2 * (2 * b + 1) - q0 m2 := by ring
      rwa [heq_sum] at hsum
  · have hm15 : min 15 (min m1 m2 + 1) = 15 := by omega
    rw [hm15]
    have h1 : qa3 15 (q0 m1 * (2 * a + 1)) :=
      qp (by omega) (by omega : 15 ≤ m1) ⟨2 * a + 1, rfl⟩
    have h2 : qa3 15 (q0 m2 * (2 * b + 1)) :=
      qp (by omega) (by omega : 15 ≤ m2) ⟨2 * b + 1, rfl⟩
    have hsum := div2_add h1 h2
    simpa using! hsum

def H_rel (base m1 m2 S U : ℤ) : Prop :=
  4 ≤ m1 ∧ 4 ≤ m2 ∧
  ∃ u1 u2 : ℤ, qW u1 ∧ qW u2 ∧ 2 * S - U + 3 = base + q0 m1 * u1 + q0 m2 * u2

lemma step_base_sound {base m1 m2 S U S' U' : ℤ} {k_next : kernel}
    (hrel : H_rel base m1 m2 S U)
    (hk : k_next ∈ library_val)
    (hact : action k_next S U S' U') :
    (step_base base m1 m2).1 = true ∧
    ∀ k3, (step_base base m1 m2).2 = some k3 →
      k3 = k_next ∧ k_next.pair.d = 1 ∧ k_next.pair.p = 1 := by
  rcases hrel with ⟨hm1, hm2, u1, u2, hu1, hu2, hH⟩
  rcases hact with ⟨_, _, t, ht⟩
  have hkp := lib_kernel_props hk
  have hi_ge5 : 5 ≤ k_next.index := hkp.1
  have h_if_lt : int_lt (int_min m1 m2) 4 = false := by
    rw [Bool.eq_false_iff, Ne, int_lt_iff, int_min_eq]; omega
  unfold step_base
  simp only [strictInt_eq]
  rw [h_if_lt]
  try dsimp -failIfUnchanged only
  have hm_eq : int_min 15 (int_min m1 m2 + 1) = min 15 (min m1 m2 + 1) := by
    rw [int_min_eq, int_min_eq]
  have hadj_eq : (if int_eq m1 m2 = true then 0 else if int_le (int_min m1 m2) 14 = true then q0 (int_min m1 m2) else 0) =
      (if m1 = m2 then 0 else if min m1 m2 ≤ 14 then q0 (min m1 m2) else 0) := by
    rw [int_min_eq]
    by_cases h12 : m1 = m2
    · have h12' : int_eq m1 m2 = true := (int_eq_iff m1 m2).mpr h12
      rw [if_pos h12', if_pos h12]
    · have h12' : ¬ int_eq m1 m2 = true := fun h => h12 ((int_eq_iff m1 m2).mp h)
      rw [if_neg h12', if_neg h12]
      by_cases hle : min m1 m2 ≤ 14
      · have hle' : int_le (min m1 m2) 14 = true := (int_le_iff _ _).mpr hle
        rw [if_pos hle', if_pos hle]
      · have hle' : ¬ int_le (min m1 m2) 14 = true := fun h => hle ((int_le_iff _ _).mp h)
        rw [if_neg hle', if_neg hle]
  rw [hm_eq, hadj_eq]
  set m := min 15 (min m1 m2 + 1)
  set adj := if m1 = m2 then 0 else if min m1 m2 ≤ 14 then q0 (min m1 m2) else 0
  set diff := base + adj
  have hm_ge5 : 5 ≤ m := by omega
  have hm_le15 : m ≤ 15 := by omega
  have hdvd_m : qa3 m (diff - q0 k_next.index * (2 * t + 1)) := by
    have h1 := odd_pair_adj_dvd (by omega : 0 ≤ m1) (by omega : 0 ≤ m2) hu1 hu2
    have hneg := qb4 (div2_zero m) h1
    have heq_diff : 0 - (q0 m1 * u1 + q0 m2 * u2 - adj) = diff - q0 k_next.index * (2 * t + 1) := by
      change 0 - (q0 m1 * u1 + q0 m2 * u2 - adj) = (base + adj) - q0 k_next.index * (2 * t + 1)
      linarith
    rwa [heq_diff] at hneg
  have hdvd5 : qa3 5 diff := by
    have h1 : qa3 5 (diff - q0 k_next.index * (2 * t + 1)) := qp (by omega) hm_ge5 hdvd_m
    have h2 : qa3 5 (q0 k_next.index * (2 * t + 1)) := qp (by omega) hi_ge5 ⟨2 * t + 1, rfl⟩
    have hsum := div2_add h1 h2
    have heq : diff - q0 k_next.index * (2 * t + 1) + q0 k_next.index * (2 * t + 1) = diff := by ring
    rwa [heq] at hsum
  have hqbg5 : qbg5 diff = true := (qbg5_iff diff).mpr hdvd5
  rw [hqbg5]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, qq16_eq]
  rcases qbw (by omega : 0 ≤ m) (by omega : 0 ≤ k_next.index) ⟨t, rfl⟩ hdvd_m with ⟨hv_lt, _⟩
  split_ifs with hlt
  · have hlt' : qq m diff < m := (int_lt_iff _ _).mp hlt
    have hi_eq : k_next.index = qq m diff := hv_lt hlt'
    have hi_lt15 : k_next.index < 15 := by omega
    have hss : single_small (qq m diff) = some k_next := by
      rw [← hi_eq]
      exact hkp.2.2.2.2.2.2.2.2.1 hi_lt15
    rw [hss]
    rcases single_small_props _ _ hss with ⟨_, _, hd, hp⟩
    exact ⟨rfl, fun k3 hk3 => by injection hk3 with hk3; exact ⟨hk3.symm, hd, hp⟩⟩
  · exact ⟨rfl, fun k3 hk3 => by contradiction⟩

lemma action_step_eq {k : kernel} {S U S' U' : ℤ}
    (hk : k ∈ library_val) (hact : action k S U S' U') :
    ∃ t : ℤ,
      2 * S - U + 3 = q0 k.index * (2 * t + 1) ∧
      U' = k.pair.b + q0 (k.index - k.pair.d) * (k.pair.p * (2 * t + 1)) ∧
      2 * S' - U' + 3 = U + 2 * gain k - k.pair.b +
        q0 (k.index - k.pair.d) * ((q0 k.pair.d - k.pair.p) * (2 * t + 1)) := by
  rcases hact with ⟨hS, hU, t, ht⟩
  have hkp := lib_kernel_props hk
  have hd_ge1 : 1 ≤ k.pair.d := hkp.2.1
  have h_sub : 4 ≤ k.index - k.pair.d := hkp.2.2.1
  have hsplit : q0 k.index = q0 k.pair.d * q0 (k.index - k.pair.d) :=
    pow_split (by omega) (by omega)
  have hd_pos : 0 < q0 k.pair.d := pow_pos (by omega)
  have hU' : U' = k.pair.b + q0 (k.index - k.pair.d) * (k.pair.p * (2 * t + 1)) := by
    apply mul_left_cancel₀ (ne_of_gt hd_pos)
    calc q0 k.pair.d * U'
      _ = k.pair.p * (2 * S - U + 3) + q0 k.pair.d * k.pair.b := hU
      _ = k.pair.p * (q0 k.pair.d * q0 (k.index - k.pair.d) * (2 * t + 1)) + q0 k.pair.d * k.pair.b := by
          rw [ht, hsplit]
      _ = q0 k.pair.d * (k.pair.b + q0 (k.index - k.pair.d) * (k.pair.p * (2 * t + 1))) := by ring
  refine ⟨t, ht, hU', ?_⟩
  have ht' : 2 * S - U + 3 = q0 k.pair.d * q0 (k.index - k.pair.d) * (2 * t + 1) := by
    rw [← hsplit]; exact ht
  linarith

def H_rel_full (base m1 : ℤ) (k_last : kernel) (S_cur U_cur : ℤ) : Prop :=
  H_rel base m1 (k_last.index - k_last.pair.d) S_cur U_cur ∧
  ∃ v2 : ℤ, U_cur = k_last.pair.b + q0 (k_last.index - k_last.pair.d) * v2

lemma two_step_rel {k1 k2 : kernel} {S0 U0 S1 U1 S2 U2 : ℤ}
    (hk1 : k1 ∈ library_val) (hk2 : k2 ∈ library_val)
    (hact1 : action k1 S0 U0 S1 U1) (hact2 : action k2 S1 U1 S2 U2) :
    H_rel_full (2 * gain k2 + k1.pair.b - k2.pair.b) (k1.index - k1.pair.d) k2 S2 U2 := by
  rcases action_step_eq hk1 hact1 with ⟨t1, _, hU1, _⟩
  rcases action_step_eq hk2 hact2 with ⟨t2, _, hU2, hH2⟩
  have hkp1 := lib_kernel_props hk1
  have hkp2 := lib_kernel_props hk2
  refine ⟨⟨hkp1.2.2.1, hkp2.2.2.1,
    k1.pair.p * (2 * t1 + 1), (q0 k2.pair.d - k2.pair.p) * (2 * t2 + 1),
    odd_mul hkp1.2.2.2.2.1 ⟨t1, rfl⟩,
    odd_mul hkp2.2.2.2.2.2.1 ⟨t2, rfl⟩, ?_⟩,
    ⟨k2.pair.p * (2 * t2 + 1), hU2⟩⟩
  linarith

lemma three_step_4k_rel {k0 kp k : kernel} {S0 U0 S1 U1 S2 U2 S3 U3 : ℤ}
    (hk0 : k0 ∈ library_val) (hkp : kp ∈ library_val) (hk : k ∈ library_val)
    (hd1 : kp.pair.d = 1)
    (hact0 : action k0 S0 U0 S1 U1)
    (hact1 : action kp S1 U1 S2 U2)
    (hact2 : action k S2 U2 S3 U3) :
    H_rel_full (2 * gain k - k.pair.b - k0.pair.b - 4) (k0.index - k0.pair.d) k S3 U3 := by
  rcases action_step_eq hk0 hact0 with ⟨t0, _, hU1, _⟩
  rcases action_step_eq hk hact2 with ⟨t2, ht2, hU3, hH3⟩
  rcases hact1 with ⟨hS2, hU2_raw, _⟩
  have hkp0 := lib_kernel_props hk0
  have hkpp := lib_kernel_props hkp
  have hkpk := lib_kernel_props hk
  rcases hkpp.2.2.2.2.2.2.2.1 hd1 with ⟨hp1, hgain1⟩
  have hU2_eq : 2 * U2 = (2 * S1 - U1 + 3) + 2 * kp.pair.b := by
    have h := hU2_raw
    rw [hd1, hp1, pow2_one] at h
    linarith
  have hU2_rel : U2 = (2 * S2 - U2 + 3) - U1 - 4 := by linarith
  have hsplit_k : q0 k.index = q0 k.pair.d * q0 (k.index - k.pair.d) :=
    pow_split (by omega : 0 ≤ k.pair.d) (by omega : k.pair.d ≤ k.index)
  have hpow_d1 : q0 (k.pair.d + 1) = 2 * q0 k.pair.d := by
    rw [q5 (by omega : 0 ≤ k.pair.d) (by omega : 0 ≤ (1 : ℤ)), pow2_one]
    ring
  refine ⟨⟨hkp0.2.2.1, hkpk.2.2.1,
    -(k0.pair.p * (2 * t0 + 1)), (q0 (k.pair.d + 1) - k.pair.p) * (2 * t2 + 1),
    odd_neg (odd_mul hkp0.2.2.2.2.1 ⟨t0, rfl⟩),
    odd_mul hkpk.2.2.2.2.2.2.1 ⟨t2, rfl⟩, ?_⟩,
    ⟨k.pair.p * (2 * t2 + 1), hU3⟩⟩
  have ht2' : 2 * S2 - U2 + 3 = q0 k.pair.d * q0 (k.index - k.pair.d) * (2 * t2 + 1) := by
    rw [← hsplit_k]; exact ht2
  have hpow' := congr_arg (fun z => q0 (k.index - k.pair.d) * (2 * t2 + 1) * z) hpow_d1
  dsimp -failIfUnchanged only at hpow'
  linarith

lemma step_rel_div {base m1 : ℤ} {k_last k_next : kernel} {S_cur U_cur S_next U_next : ℤ}
    (hrel : H_rel_full base m1 k_last S_cur U_cur)
    (hk_next : k_next ∈ library_val)
    (hd1 : k_next.pair.d = 1) (hp1 : k_next.pair.p = 1)
    (hact : action k_next S_cur U_cur S_next U_next)
    (hle : k_next.index ≤ min m1 (k_last.index - k_last.pair.d)) :
    H_rel (2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2)
      (m1 - 1) (k_last.index - k_last.pair.d - 1) S_next U_next := by
  rcases hrel with ⟨⟨hm1, hm2, u1, u2, hu1, hu2, hH_cur⟩, v2, hU_cur⟩
  rcases hact with ⟨hS_next, hU_next_raw, t_next, ht_next⟩
  have hkp_next := lib_kernel_props hk_next
  have hi_ge5 : 5 ≤ k_next.index := hkp_next.1
  have hm1_ge5 : 5 ≤ m1 := by omega
  have hm2_ge5 : 5 ≤ k_last.index - k_last.pair.d := by omega
  have hU_next : 2 * U_next = (2 * S_cur - U_cur + 3) + 2 * k_next.pair.b := by
    have h := hU_next_raw
    rw [hd1, hp1, pow2_one] at h
    linarith
  have hpow_i : q0 k_next.index = 2 * q0 (k_next.index - 1) := by
    rw [pow_split (by omega : 0 ≤ (1 : ℤ)) (by omega : 1 ≤ k_next.index), pow2_one]
  have hpow_m1 : q0 m1 = 2 * q0 (m1 - 1) := by
    rw [pow_split (by omega : 0 ≤ (1 : ℤ)) (by omega : 1 ≤ m1), pow2_one]
  have hpow_m2 : q0 (k_last.index - k_last.pair.d) = 2 * q0 (k_last.index - k_last.pair.d - 1) := by
    rw [pow_split (by omega : 0 ≤ (1 : ℤ)) (by omega : 1 ≤ k_last.index - k_last.pair.d), pow2_one]
  refine ⟨by omega, by omega, u1, 2 * v2 + u2, hu1, odd_add_two_mul v2 hu2, ?_⟩
  set Q_next := q0 (k_next.index - 1) * (2 * t_next + 1)
  set Q1 := q0 (m1 - 1) * u1
  set Q2 := q0 (k_last.index - k_last.pair.d - 1) * u2
  set V2 := q0 (k_last.index - k_last.pair.d - 1) * v2
  have h1 : 2 * S_cur - U_cur + 3 = 2 * Q_next := by
    calc 2 * S_cur - U_cur + 3 = q0 k_next.index * (2 * t_next + 1) := ht_next
    _ = 2 * Q_next := by rw [hpow_i]; ring
  have h2 : 2 * S_cur - U_cur + 3 = base + 2 * Q1 + 2 * Q2 := by
    calc 2 * S_cur - U_cur + 3 = base + q0 m1 * u1 + q0 (k_last.index - k_last.pair.d) * u2 := hH_cur
    _ = base + 2 * Q1 + 2 * Q2 := by rw [hpow_m1, hpow_m2]; ring
  have h3 : U_cur = k_last.pair.b + 2 * V2 := by
    calc U_cur = k_last.pair.b + q0 (k_last.index - k_last.pair.d) * v2 := hU_cur
    _ = k_last.pair.b + 2 * V2 := by rw [hpow_m2]; ring
  have h4 : 2 * S_next - U_next + 3 =
      (2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2) + Q1 + (2 * V2 + Q2) := by
    omega
  calc 2 * S_next - U_next + 3
    _ = (2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2) + Q1 + (2 * V2 + Q2) := h4
    _ = 2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2 +
        q0 (m1 - 1) * u1 + q0 (k_last.index - k_last.pair.d - 1) * (2 * v2 + u2) := by
        dsimp -failIfUnchanged [Q1, Q2, V2]; ring

lemma chain_simple_succ (fuel1 : ℕ) (k1 k2 : kernel) :
    chain_simple (fuel1 + 1) k1 k2 =
      eval_step_rel fuel1 (2 * gain k2 + k1.pair.b - k2.pair.b) (k1.index - k1.pair.d) k2 := by
  unfold chain_simple eval_step_rel
  simp only [strictInt_eq]

lemma eval_step_rel_sound {fuel1 : ℕ} {base m1 : ℤ} {k_last : kernel}
    {S_prev U_prev S_cur U_cur : ℤ} {rest : List kernel}
    (ih1 : ∀ (k_a k_b : kernel) (S_a U_a S_b U_b S_c U_c : ℤ) (rest_c : List kernel),
      k_a ∈ library_val → k_b ∈ library_val →
      action k_a S_a U_a S_b U_b → action k_b S_b U_b S_c U_c →
      (∀ x ∈ rest_c, x ∈ library_val) → trace rest_c S_c U_c →
      fuel1 ≤ rest_c.length → chain_simple fuel1 k_a k_b = true)
    (ih2 : ∀ (fuel2 : ℕ), fuel1 = fuel2 + 1 →
      ∀ (k_a k_b : kernel) (S_a U_a S_b U_b S_c U_c : ℤ) (rest_c : List kernel),
      k_a ∈ library_val → k_b ∈ library_val →
      action k_a S_a U_a S_b U_b → action k_b S_b U_b S_c U_c →
      (∀ x ∈ rest_c, x ∈ library_val) → trace rest_c S_c U_c →
      fuel2 ≤ rest_c.length → chain_simple fuel2 k_a k_b = true)
    (hk_last : k_last ∈ library_val)
    (hrel : H_rel_full base m1 k_last S_cur U_cur)
    (hact_last : action k_last S_prev U_prev S_cur U_cur)
    (hall : ∀ x ∈ rest, x ∈ library_val)
    (htrace : trace rest S_cur U_cur)
    (hlen : fuel1 + 1 ≤ rest.length) :
    eval_step_rel fuel1 base m1 k_last = true := by
  cases htrace with
  | trace_nil => simp at hlen
  | @trace_cons k_next rest1 _ _ S_next U_next hstep_next htail1 =>
    have hk_next : k_next ∈ library_val := hall k_next List.mem_cons_self
    have hall1 : ∀ x ∈ rest1, x ∈ library_val :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have hlen1 : fuel1 ≤ rest1.length := by simp at hlen; omega
    rcases step_base_sound hrel.1 hk_next hstep_next with ⟨hsb1, hsb2⟩
    unfold eval_step_rel
    simp only [strictInt_eq]
    generalize h_sb : step_base base m1 (k_last.index - k_last.pair.d) = sb
    rcases sb with ⟨b, opt_k⟩
    have hb : b = true := by rw [← hsb1, h_sb]
    subst hb
    cases opt_k with
    | none => rfl
    | some k3 =>
      rcases hsb2 k3 (by rw [h_sb]) with ⟨hk3_eq, hd1, hp1⟩
      subst k3
      dsimp -failIfUnchanged only
      have hcs1 : chain_simple fuel1 k_last k_next = true :=
        ih1 k_last k_next S_prev U_prev S_cur U_cur S_next U_next rest1
          hk_last hk_next hact_last hstep_next hall1 htail1 hlen1
      rw [hcs1]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases fuel1 with
      | zero => rfl
      | succ fuel2 =>
        dsimp -failIfUnchanged only
        split_ifs with hle_idx
        · have hle' : k_next.index ≤ min m1 (k_last.index - k_last.pair.d) := by
            rw [int_le_iff, int_min_eq] at hle_idx
            exact hle_idx
          cases htail1 with
          | trace_nil => simp at hlen1
          | @trace_cons k_next2 rest2 _ _ S_next2 U_next2 hstep_next2 htail2 =>
            have hk_next2 : k_next2 ∈ library_val := hall1 k_next2 List.mem_cons_self
            have hall2 : ∀ x ∈ rest2, x ∈ library_val :=
              fun x hx => hall1 x (List.mem_cons_of_mem _ hx)
            have hlen2 : fuel2 ≤ rest2.length := by simp at hlen1; omega
            have hrel_div := step_rel_div hrel hk_next hd1 hp1 hstep_next hle'
            rcases step_base_sound hrel_div hk_next2 hstep_next2 with ⟨hsb_d1, hsb_d2⟩
            generalize h_sbd : step_base (2 * gain k_next + k_last.pair.b - k_next.pair.b + base / 2)
                (m1 - 1) (k_last.index - k_last.pair.d - 1) = sbd
            rcases sbd with ⟨bd, opt_kd⟩
            have hbd : bd = true := by rw [← hsb_d1, h_sbd]
            subst hbd
            cases opt_kd with
            | none => rfl
            | some k4 =>
              rcases hsb_d2 k4 (by rw [h_sbd]) with ⟨hk4_eq, _, _⟩
              subst k4
              dsimp -failIfUnchanged only
              exact ih2 fuel2 rfl k_next k_next2 S_cur U_cur S_next U_next S_next2 U_next2 rest2
                hk_next hk_next2 hstep_next hstep_next2 hall2 htail2 hlen2
        · rfl

lemma chain_simple_sound (fuel : ℕ) :
    ∀ (k1 k2 : kernel) (S0 U0 S1 U1 S2 U2 : ℤ) (rest : List kernel),
      k1 ∈ library_val → k2 ∈ library_val →
      action k1 S0 U0 S1 U1 → action k2 S1 U1 S2 U2 →
      (∀ x ∈ rest, x ∈ library_val) → trace rest S2 U2 →
      fuel ≤ rest.length → chain_simple fuel k1 k2 = true := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro k1 k2 S0 U0 S1 U1 S2 U2 rest hk1 hk2 hact1 hact2 hall htrace hlen
    cases fuel with
    | zero => rfl
    | succ fuel1 =>
      rw [chain_simple_succ]
      have hrel := two_step_rel hk1 hk2 hact1 hact2
      exact eval_step_rel_sound
        (ih fuel1 (by omega))
        (fun fuel2 h_eq => ih fuel2 (by omega))
        hk2 hrel hact2 hall htrace hlen

def prev_ok (kp2 : Option kernel) (kp : kernel) (S U : ℤ) : Prop :=
  kp ∈ library_val ∧
  ∃ S_prev U_prev : ℤ, action kp S_prev U_prev S U ∧
    match kp2 with
    | none => True
    | some k0 => k0 ∈ library_val ∧ ∃ S_prev2 U_prev2 : ℤ, action k0 S_prev2 U_prev2 S_prev U_prev

lemma check_4k_simple_sound (fuel : ℕ) (kp2 : Option kernel) (kp k : kernel)
    (S U S' U' : ℤ) (rest : List kernel)
    (hp_ok : prev_ok kp2 kp S U)
    (hk : k ∈ library_val)
    (hact_k : action k S U S' U')
    (hall : ∀ x ∈ rest, x ∈ library_val)
    (htrace : trace rest S' U')
    (hlen : fuel ≤ rest.length) :
    check_4k_simple fuel kp2 kp k = true := by
  rcases hp_ok with ⟨hkp, S_prev, U_prev, hact_kp, hkp2⟩
  have hcs : chain_simple fuel kp k = true :=
    chain_simple_sound fuel kp k S_prev U_prev S U S' U' rest hkp hk hact_kp hact_k hall htrace hlen
  unfold check_4k_simple
  dsimp -failIfUnchanged only
  cases kp2 with
  | none =>
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs]
  | some k0 =>
    cases fuel with
    | zero =>
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hcs]
    | succ fuel1 =>
      dsimp -failIfUnchanged only
      cases hd1_b : int_eq kp.pair.d 1
      · simp only [Bool.not_false, ↓reduceIte, Bool.not_true, Bool.false_eq_true, hcs]
      · have hd1 : kp.pair.d = 1 := (int_eq_iff _ _).mp hd1_b
        rcases hkp2 with ⟨hk0, S_prev2, U_prev2, hact_k0⟩
        have hrel := three_step_4k_rel hk0 hkp hk hd1 hact_k0 hact_kp hact_k
        have heval : eval_step_rel fuel1 (2 * gain k - k.pair.b - k0.pair.b - 4)
            (k0.index - k0.pair.d) k = true :=
          eval_step_rel_sound
            (chain_simple_sound fuel1)
            (fun fuel2 _ => chain_simple_sound fuel2)
            hk hrel hact_k hall htrace hlen
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, strictInt_eq, heval, hcs]

lemma kernel_term_mod32 {k0 : kernel} {u : ℤ}
    (hk0 : k0 ∈ library_val) (hu : qW u) :
    ∃ c : ℤ, q0 (k0.index - k0.pair.d) * u =
      32 * c + (if int_eq k0.index 5 then 16 else 0) := by
  rcases hu with ⟨a, rfl⟩
  have hkp0 := lib_kernel_props hk0
  have hm_ge4 : 4 ≤ k0.index - k0.pair.d := hkp0.2.2.1
  have hm_iff : k0.index - k0.pair.d = 4 ↔ k0.index = 5 := hkp0.2.2.2.1
  by_cases h5 : k0.index = 5
  · have hm4 : k0.index - k0.pair.d = 4 := hm_iff.mpr h5
    have h5' : int_eq k0.index 5 = true := (int_eq_iff _ _).mpr h5
    have hq0_4 : q0 4 = 16 := by decide
    rw [hm4, h5', if_pos rfl, hq0_4]
    exact ⟨a, by ring⟩
  · have hm5 : 5 ≤ k0.index - k0.pair.d := by omega
    have h5' : ¬ int_eq k0.index 5 = true := fun h => h5 ((int_eq_iff _ _).mp h)
    have hsplit : q0 (k0.index - k0.pair.d) = 32 * q0 (k0.index - k0.pair.d - 5) := by
      rw [pow_split (by omega : 0 ≤ (5 : ℤ)) hm5]
      have hq0_5 : q0 5 = 32 := by decide
      rw [hq0_5]
    rw [if_neg h5', hsplit]
    exact ⟨q0 (k0.index - k0.pair.d - 5) * (2 * a + 1), by ring⟩

lemma two_step_bkt {kp k k_next : kernel} {S_prev U_prev S U S' U' S'' U'' : ℤ}
    (hkp : kp ∈ library_val) (hk : k ∈ library_val) (hk_next : k_next ∈ library_val)
    (hact_kp : action kp S_prev U_prev S U)
    (hact_k : action k S U S' U')
    (hact_next : action k_next S' U' S'' U'') :
    k ∈ get_bkt (k_req kp) := by
  rcases (two_step_rel hkp hk hact_kp hact_k).1 with ⟨_, _, u1, u2, hu1, hu2, hH⟩
  rcases hact_next with ⟨_, _, t, ht⟩
  rcases kernel_term_mod32 hkp hu1 with ⟨c1, hc1⟩
  rcases kernel_term_mod32 hk hu2 with ⟨c2, hc2⟩
  have hi_ge5 : 5 ≤ k_next.index := (lib_kernel_props hk_next).1
  have hsplit_next : q0 k_next.index = 32 * q0 (k_next.index - 5) := by
    rw [pow_split (by omega : 0 ≤ (5 : ℤ)) hi_ge5]
    have hq0_5 : q0 5 = 32 := by decide
    rw [hq0_5]
  have ht_32 : 2 * S' - U' + 3 = 32 * (q0 (k_next.index - 5) * (2 * t + 1)) := by
    rw [ht, hsplit_next]; ring
  have htag_eq : k_tag k = k_req kp := by
    unfold k_tag k_req
    omega
  rw [← htag_eq]
  exact (lib_kernel_props hk).2.2.2.2.2.2.2.2.2

def eq_kernel (k1 k2 : kernel) : Bool :=
  int_eq k1.index k2.index &&
  int_eq k1.pair.p k2.pair.p &&
  int_eq k1.pair.d k2.pair.d &&
  int_eq k1.pair.b k2.pair.b &&
  int_eq k1.pair.c k2.pair.c

lemma eq_kernel_iff (k1 k2 : kernel) : eq_kernel k1 k2 = true ↔ k1 = k2 := by
  rcases k1 with ⟨i1, p1, d1, b1, c1⟩
  rcases k2 with ⟨i2, p2, d2, b2, c2⟩
  simp only [eq_kernel, Bool.and_eq_true, int_eq_iff, kernel.mk.injEq, Table.pair.mk.injEq]
  tauto

def mem_kernel (k : kernel) : List kernel → Bool
  | [] => false
  | x :: xs => if eq_kernel k x then true else mem_kernel k xs

lemma mem_kernel_iff (k : kernel) (xs : List kernel) :
    mem_kernel k xs = true ↔ k ∈ xs := by
  induction xs with
  | nil => simp [mem_kernel]
  | cons x xs ih =>
    unfold mem_kernel
    by_cases h : k = x
    · subst h
      have heq : eq_kernel k k = true := (eq_kernel_iff k k).mpr rfl
      rw [heq, if_pos rfl]
      simp
    · have heq : eq_kernel k x = false := by
        rw [Bool.eq_false_iff, ne_eq, eq_kernel_iff]; exact h
      rw [heq, if_neg Bool.false_ne_true, ih]
      simp [h]

def cs2_small (k k3 : kernel) : Bool :=
  if int_eq k3.index 5 then int_eq (k_tag k) 9
  else if int_eq k3.index 8 then mem_kernel k cands_8
  else false

def bool_beq (a b : Bool) : Bool :=
  match a, b with
  | true, true => true
  | false, false => true
  | _, _ => false

def check_cs2_small (k : kernel) : Bool :=
  bool_beq (chain_simple 2 k ⟨5, ⟨1, 1, 7, 0⟩⟩) (cs2_small k ⟨5, ⟨1, 1, 7, 0⟩⟩) &&
  bool_beq (chain_simple 2 k ⟨8, ⟨1, 1, 13, 0⟩⟩) (cs2_small k ⟨8, ⟨1, 1, 13, 0⟩⟩) &&
  bool_beq (chain_simple 2 k ⟨12, ⟨1, 1, 25, 0⟩⟩) (cs2_small k ⟨12, ⟨1, 1, 25, 0⟩⟩) &&
  bool_beq (chain_simple 2 k ⟨14, ⟨1, 1, 31, 0⟩⟩) (cs2_small k ⟨14, ⟨1, 1, 31, 0⟩⟩)

lemma check_cs2_small_all : qJ check_cs2_small library_val = true := by decide +kernel

lemma bool_beq_eq {a b : Bool} (h : bool_beq a b = true) : a = b := by
  cases a <;> cases b <;> first | rfl | contradiction

lemma cs2_small_eq {k k3 : kernel} {v : ℤ} (hk : k ∈ library_val)
    (hss : single_small v = some k3) :
    chain_simple 2 k k3 = cs2_small k k3 := by
  have h := qbf check_cs2_small library_val check_cs2_small_all k hk
  unfold check_cs2_small at h
  simp only [Bool.and_eq_true] at h
  unfold single_small at hss
  split_ifs at hss with h5 h8 h12 h14
  · injection hss with hss; subst hss; exact bool_beq_eq h.1.1.1
  · injection hss with hss; subst hss; exact bool_beq_eq h.1.1.2
  · injection hss with hss; subst hss; exact bool_beq_eq h.1.2
  · injection hss with hss; subst hss; exact bool_beq_eq h.2

lemma step_base_some_small {base m1 m2 : ℤ} {k3 : kernel}
    (h : (step_base base m1 m2).2 = some k3) :
    ∃ v, single_small v = some k3 := by
  unfold step_base at h
  simp only [strictInt_eq] at h
  generalize hv : qq16 (int_min 15 (int_min m1 m2 + 1))
    (base + if int_eq m1 m2 = true then 0 else if int_le (int_min m1 m2) 14 = true then q0 (int_min m1 m2) else 0) = v at h
  generalize hadj : (if int_eq m1 m2 = true then 0 else if int_le (int_min m1 m2) 14 = true then q0 (int_min m1 m2) else 0) = adj at h
  split_ifs at h with h1 h2 h3
  cases hss : single_small v with
  | none => rw [hss] at h; contradiction
  | some k3' =>
    rw [hss] at h
    injection h with h; subst h
    exact ⟨v, hss⟩

def chain_simple_3_fast (kp k : kernel) : Bool :=
  q2 (kp.index - kp.pair.d) fun m1 =>
  q2 (k.index - k.pair.d) fun m2 =>
  q2 (2 * gain k + kp.pair.b - k.pair.b) fun base =>
  match step_base base m1 m2 with
  | (false, _) => false
  | (true, none) => true
  | (true, some k3) =>
    if !(cs2_small k k3) then false
    else
      if int_le k3.index (int_min m1 m2) then
        q2 (2 * gain k3 + k.pair.b - k3.pair.b + base / 2) fun base_div =>
        match step_base base_div (m1 - 1) (m2 - 1) with
        | (false, _) => false
        | (true, none) => true
        | (true, some k4) => chain_simple 1 k3 k4
      else true

lemma chain_simple_3_fast_eq (kp : kernel) {k : kernel} (hk : k ∈ library_val) :
    chain_simple_3_fast kp k = chain_simple 3 kp k := by
  unfold chain_simple_3_fast
  conv_rhs => unfold chain_simple
  simp only [strictInt_eq]
  generalize hsb : step_base (2 * gain k + kp.pair.b - k.pair.b)
    (kp.index - kp.pair.d) (k.index - k.pair.d) = sb
  rcases sb with ⟨b, opt_k3⟩
  cases b with
  | false => rfl
  | true =>
    cases opt_k3 with
    | none => rfl
    | some k3 =>
      have h2 : (step_base (2 * gain k + kp.pair.b - k.pair.b)
          (kp.index - kp.pair.d) (k.index - k.pair.d)).2 = some k3 := by
        rw [hsb]
      rcases step_base_some_small h2 with ⟨v, hss⟩
      dsimp -failIfUnchanged only
      rw [cs2_small_eq hk hss]

def check_cands_3 (kp : kernel) : Bool :=
  let cands := get_cands_3 kp
  qJ (fun k => if mem_kernel k cands then true else !(chain_simple_3_fast kp k))
    (get_bkt (k_req kp))

lemma cands_3_0 : qJ check_cands_3 lib_0 = true := by decide +kernel
lemma cands_3_1 : qJ check_cands_3 lib_1 = true := by decide +kernel
lemma cands_3_2 : qJ check_cands_3 lib_2 = true := by decide +kernel
lemma cands_3_3 : qJ check_cands_3 lib_3 = true := by decide +kernel
lemma cands_3_4 : qJ check_cands_3 lib_4 = true := by decide +kernel
lemma cands_3_5 : qJ check_cands_3 lib_5 = true := by decide +kernel
lemma cands_3_6 : qJ check_cands_3 lib_6 = true := by decide +kernel
lemma cands_3_7 : qJ check_cands_3 lib_7 = true := by decide +kernel
lemma cands_3_8 : qJ check_cands_3 lib_8 = true := by decide +kernel
lemma cands_3_9 : qJ check_cands_3 lib_9 = true := by decide +kernel
lemma cands_3_10 : qJ check_cands_3 lib_10 = true := by decide +kernel
lemma cands_3_11 : qJ check_cands_3 lib_11 = true := by decide +kernel
lemma cands_3_12 : qJ check_cands_3 lib_12 = true := by decide +kernel
lemma cands_3_13 : qJ check_cands_3 lib_13 = true := by decide +kernel
lemma cands_3_14 : qJ check_cands_3 lib_14 = true := by decide +kernel
lemma cands_3_15 : qJ check_cands_3 lib_15 = true := by decide +kernel

lemma cands_3_sub_bkt : qJ check_cands_3 library_val = true := by
  unfold library_val
  simp only [qbr, cands_3_0, cands_3_1, cands_3_2, cands_3_3, cands_3_4, cands_3_5,
    cands_3_6, cands_3_7, cands_3_8, cands_3_9, cands_3_10, cands_3_11,
    cands_3_12, cands_3_13, cands_3_14, cands_3_15, Bool.and_self]

lemma get_cands_sound (fuel : ℕ) (kp k : kernel)
    (S_prev U_prev S U S' U' : ℤ) (rest : List kernel)
    (hkp : kp ∈ library_val) (hk : k ∈ library_val)
    (hact_kp : action kp S_prev U_prev S U)
    (hact_k : action k S U S' U')
    (hall : ∀ x ∈ rest, x ∈ library_val)
    (htrace : trace rest S' U')
    (hlen : fuel ≤ rest.length) :
    k ∈ get_cands fuel kp := by
  unfold get_cands
  cases fuel with
  | zero => exact hk
  | succ fuel1 =>
    have hbkt : k ∈ get_bkt (k_req kp) := by
      cases htrace with
      | trace_nil => simp at hlen
      | @trace_cons k_next rest1 _ _ S'' U'' hstep_next _ =>
        have hk_next : k_next ∈ library_val := hall k_next List.mem_cons_self
        exact two_step_bkt hkp hk hk_next hact_kp hact_k hstep_next
    cases hble : Nat.ble 3 (fuel1 + 1)
    · exact hbkt
    · have hge3 : 3 ≤ fuel1 + 1 := Nat.le_of_ble_eq_true hble
      have hcs3 : chain_simple 3 kp k = true :=
        chain_simple_sound 3 kp k S_prev U_prev S U S' U' rest hkp hk hact_kp hact_k hall htrace (by omega)
      have h3 := qbf check_cands_3 library_val cands_3_sub_bkt kp hkp
      unfold check_cands_3 at h3
      have h4 := qbf _ (get_bkt (k_req kp)) h3 k hbkt
      try dsimp -failIfUnchanged only at h4
      by_cases hmem : k ∈ get_cands_3 kp
      · exact hmem
      · have hmem_f : mem_kernel k (get_cands_3 kp) = false := by
          rw [Bool.eq_false_iff, ne_eq, mem_kernel_iff]; exact hmem
        rw [hmem_f, if_neg Bool.false_ne_true, chain_simple_3_fast_eq kp hk, hcs3] at h4
        contradiction

lemma qJ_cands_sound (fuel : ℕ) (min_idx : ℤ) (kp2 : Option kernel) (kp : kernel)
    (step : kernel → Bool) (ks : List kernel)
    (h : qJ_cands fuel min_idx kp2 kp step ks = true) :
    ∀ k ∈ ks, min_idx ≤ k.index → check_4k_simple fuel kp2 kp k = true → step k = true := by
  induction ks with
  | nil => intro k hk; contradiction
  | cons a ks ih =>
    intro k hk hle hchk
    unfold qJ_cands at h
    rcases List.mem_cons.mp hk with rfl | hk'
    · have hle' : int_le min_idx k.index = true := (int_le_iff _ _).mpr hle
      rw [hle', hchk] at h
      simp only [↓reduceIte] at h
      split_ifs at h with hstep
      exact hstep
    · split_ifs at h <;> exact ih h k hk' hle hchk

theorem refute_spec_c (fuel : ℕ) (z : state) (kp2 : Option kernel) (kp : kernel)
    (S0 U0 S U : ℤ)
    (hz : qE z S0 U0 S U)
    (hp_ok : prev_ok kp2 kp S U)
    (hcheck : qbN_c fuel z kp2 kp = true) :
    ∀ word, (∀ k ∈ word, continuing k ∧ k.index ≤ 2048) →
      trace word S U → word.length < fuel := by
  induction fuel generalizing z kp2 kp S U with
  | zero => contradiction
  | succ fuel ih =>
    intro word hall htrace
    cases htrace with
    | trace_nil => simp
    | @trace_cons k rest _ _ S' U' hstep htail =>
      by_contra hnot
      have hlen : fuel ≤ rest.length := by simp only [List.length_cons] at hnot; omega
      rcases hall k List.mem_cons_self with ⟨hk_cont, hmax⟩
      have hk_lib : k ∈ library_val := qx k hk_cont hmax
      have hrest_all : ∀ x ∈ rest, continuing x ∧ x.index ≤ 2048 :=
        fun x hx => hall x (List.mem_cons_of_mem k hx)
      have hrest_lib : ∀ x ∈ rest, x ∈ library_val :=
        fun x hx => qx x (hrest_all x hx).1 (hrest_all x hx).2
      have hchk : check_4k_simple fuel kp2 kp k = true :=
        check_4k_simple_sound fuel kp2 kp k S U S' U' rest hp_ok hk_lib hstep hrest_lib htail hlen
      rcases hp_ok with ⟨hkp_lib, S_prev, U_prev, hact_kp, hkp2_rest⟩
      have hcands : k ∈ get_cands fuel kp :=
        get_cands_sound fuel kp k S_prev U_prev S U S' U' rest hkp_lib hk_lib hact_kp hstep hrest_lib htail hlen
      have hi_ge0 : 0 ≤ k.index := by
        have := (lib_kernel_props hk_lib).1
        omega
      have hnext : qB (fun z' => qbN_c fuel z' (some kp) k) z k = true := by
        unfold qbN_c at hcheck
        simp only [strictInt_eq] at hcheck
        cases hr : z.rel with
        | none =>
          rw [hr] at hcheck
          exact qJ_cands_sound fuel 0 kp2 kp _ (get_cands fuel kp) hcheck k hcands hi_ge0 hchk
        | some r =>
          rw [hr] at hcheck
          dsimp -failIfUnchanged only at hcheck
          have hin : k ∈ qbj z := choices_spec z k S0 U0 S U S' U' hz hk_cont hmax hstep
          unfold qbj at hin
          simp only [strictInt_eq, hr] at hin
          try dsimp -failIfUnchanged only at hin
          cases hvb : int_lt (qq (qa2 r (A z) z.Q) (qa6 r (A z) (B z) z.Q)) (qa2 r (A z) z.Q)
          · rw [hvb] at hcheck
            simp only [Bool.false_eq_true, ↓reduceIte] at hcheck
            have hvb' : ¬ (decide (qq (qa2 r (A z) z.Q) (qa6 r (A z) (B z) z.Q) < qa2 r (A z) z.Q) = true) := by
              rw [decide_eq_true_iff, ← int_lt_iff, hvb]
              decide
            rw [if_neg hvb'] at hin
            rcases List.mem_filter.mp hin with ⟨_, hmin⟩
            rw [decide_eq_true_iff] at hmin
            exact qJ_cands_sound fuel (qa2 r (A z) z.Q - z.D) kp2 kp _ (get_cands fuel kp) hcheck k hcands hmin hchk
          · rw [hvb, if_pos rfl] at hcheck
            have hvb' : decide (qq (qa2 r (A z) z.Q) (qa6 r (A z) (B z) z.Q) < qa2 r (A z) z.Q) = true := by
              rw [decide_eq_true_iff]
              exact (int_lt_iff _ _).mp hvb
            rw [if_pos hvb'] at hin
            exact qJ_cands_sound fuel 0 kp2 kp _ _ hcheck k hin hi_ge0 hchk
      rcases advance_spec z k S0 U0 S U S' U' hz hk_cont hstep with ⟨z', hadvance, hz'⟩
      unfold qB at hnext
      rw [hadvance] at hnext
      have hp_ok' : prev_ok (some kp) k S' U' :=
        ⟨hk_lib, S, U, hstep, hkp_lib, S_prev, U_prev, hact_kp⟩
      have ih_res := ih z' (some kp) k S' U' hz' hp_ok' hnext rest hrest_all htail
      omega

def q9_c (k : kernel) : Bool :=
  qB (fun z' => qbN_c 6 z' none k) qaG k
lemma ref_0a : qJ q9_c lib_0a=true:= by decide +kernel
lemma ref_0b : qJ q9_c lib_0b=true:= by decide +kernel
lemma ref_0c : qJ q9_c lib_0c=true:= by decide +kernel
lemma ref_0 : qJ q9_c lib_0=true:= by
  unfold lib_0
  simp only [qbr,ref_0a,ref_0b,ref_0c,Bool.and_self]
lemma ref_1 : qJ q9_c lib_1=true:= by decide +kernel
lemma ref_2 : qJ q9_c lib_2=true:= by decide +kernel
lemma ref_3 : qJ q9_c lib_3=true:= by decide +kernel
lemma ref_4 : qJ q9_c lib_4=true:= by decide +kernel
lemma ref_5 : qJ q9_c lib_5=true:= by decide +kernel
lemma ref_6 : qJ q9_c lib_6=true:= by decide +kernel
lemma ref_7 : qJ q9_c lib_7=true:= by decide +kernel
lemma ref_8 : qJ q9_c lib_8=true:= by decide +kernel
lemma ref_9 : qJ q9_c lib_9=true:= by decide +kernel
lemma ref_10 : qJ q9_c lib_10=true:= by decide +kernel
lemma ref_11 : qJ q9_c lib_11=true:= by decide +kernel
lemma ref_12 : qJ q9_c lib_12=true:= by decide +kernel
lemma ref_13 : qJ q9_c lib_13=true:= by decide +kernel
lemma ref_14 : qJ q9_c lib_14=true:= by decide +kernel
lemma ref_15 : qJ q9_c lib_15=true:= by decide +kernel
lemma qbA : qJ q9_c library_val=true:= by
  unfold library_val
  simp only [qbr,ref_0,ref_1,ref_2,ref_3,ref_4,ref_5,ref_6,ref_7,
    ref_8,ref_9,ref_10,ref_11,ref_12,ref_13,ref_14,ref_15,Bool.and_self]
theorem F2 (word : List kernel) (S U : ℤ)
    (hall : ∀ k ∈ word,continuing k ∧ k.index ≤ 2048)
    (htrace : trace word S U) :
    word.length ≤ 6:= by
  cases htrace with
  | trace_nil => simp
  | @trace_cons k rest _ _ S' U' hstep htail =>
    rcases hall k List.mem_cons_self with ⟨hk_cont, hmax⟩
    have hk_lib : k ∈ library_val := qx k hk_cont hmax
    have hrest_all : ∀ x ∈ rest, continuing x ∧ x.index ≤ 2048 :=
      fun x hx => hall x (List.mem_cons_of_mem k hx)
    have hq9 : q9_c k = true := qbf q9_c library_val qbA k hk_lib
    rcases advance_spec qaG k S U S U S' U' (initial_spec S U) hk_cont hstep with ⟨z', hadvance, hz'⟩
    unfold q9_c qB at hq9
    rw [hadvance] at hq9
    have hp_ok : prev_ok none k S' U' := ⟨hk_lib, S, U, hstep, trivial⟩
    have hlen := refute_spec_c 6 z' none k S U S' U' hz' hp_ok hq9 rest hrest_all htail
    simp only [List.length_cons]
    omega
lemma finite_bounds :
    qJ (fun k => decide (k.pair.d ≤ 5) && decide (gain k ≤ 5472)) library_val=true:= by decide +kernel
lemma kernel_bounds (k : WordLibrary.kernel) (hk : WordLibrary.continuing k) (hmax : k.index ≤ 2048) :
    k.pair.d ≤ 5 ∧ WordLibrary.gain k ≤ 5472:= by
  have hmem : k ∈ library_val:=qx k hk hmax
  have h:=qbf _ library_val finite_bounds k hmem
  rcases Bool.and_eq_true_iff.mp h with ⟨hd,hg⟩
  exact ⟨of_decide_eq_true hd,of_decide_eq_true hg⟩
end WordCheck
namespace WordLink
open Table WordLibrary
lemma continuing_good (k : WordLibrary.kernel) (hk : WordLibrary.continuing k) :
    Block.good (Bridge.kernel k.pair):= by
  rcases hk with ⟨e,hb,hs,he⟩
  rcases (built_valid hb).1 with ⟨_,_,hx,_⟩
  exact Bridge.kernel_good hx
lemma continuing_gain (k : WordLibrary.kernel) (hk : WordLibrary.continuing k) :
    k.index < WordLibrary.gain k:= by
  rcases hk with ⟨e,hb,_⟩
  exact Bridge.kernel_gain (built_valid hb)
lemma action_block {k : WordLibrary.kernel} {S U S' U' : ℤ}
    (h : WordLibrary.action k S U S' U') :
    Block.call (Bridge.kernel k.pair) S (2 * S - U + 3) S' (2 * S' - U' + 3):= by
  rcases h with ⟨hS,hU,_⟩
  unfold Block.call Bridge.kernel gain at *
  try dsimp -failIfUnchanged only at *
  refine ⟨hS,?_⟩
  rw [hS]
  linarith
lemma trace_suffix (pref suf : List WordLibrary.kernel) (S U : ℤ)
    (h : WordLibrary.trace (pref ++ suf) S U) :
    ∃ S' U',WordLibrary.trace suf S' U':= by
  induction pref generalizing S U with
  | nil => exact ⟨S,U,h⟩
  | cons k pref ih =>
    cases h with
    | trace_cons _ htail => exact ih _ _ htail
def bound (L r : ℤ) : Prop :=
  ∀ word S U,(∀ k ∈ word,WordLibrary.continuing k ∧ k.index ≤ L) →
    WordLibrary.trace word S U → (word.length : ℤ) ≤ r
lemma bound_mono (L L' r r' : ℤ) (hL : L' ≤ L) (hr : r ≤ r') (hb : bound L r) : bound L' r':= by
  intro word S U hall htrace
  have hall' : ∀ k ∈ word,WordLibrary.continuing k ∧ k.index ≤ L:= by
    intro k hk
    rcases hall k hk with ⟨hc,hi⟩
    exact ⟨hc,by omega⟩
  have h1:=hb word S U hall' htrace
  omega
lemma base_bound : bound 2048 6:= by
  intro word S U hall htrace
  have h:=WordCheck.F2 word S U hall htrace
  omega
end WordLink
namespace Phase
open Table
def qct (s r gap : ℤ) (x : pair) (K : ℤ) (y : pair) : Prop :=
  y.b=left s r x ∧ y.c=right s r x ∧ K - y.d=s - x.d + gap
lemma qaT (s r gap : ℤ) (x : pair) (K : ℤ) (y : pair)
    (hx : qaB s x) (hr : qW r) (hg : 1 ≤ gap) (hc : qct s r gap x K y) :
    q3 K y=q3 s x:= by
  rcases hc with ⟨hb,hcy,hd⟩
  rcases hx with ⟨hdx0,hdxs,hpx0,hpxd,hpodd,hbx,hcx⟩
  have hlt : y.d < K:= by omega
  unfold q3 qk
  rw [if_pos hlt,hb]
  exact Bridge.head_value ⟨hdx0,hdxs,hpx0,hpxd,hpodd,hbx,hcx⟩ hr
lemma qay (s r gap : ℤ) (x : pair) (K : ℤ) (y : pair) (t u : ℤ)
    (hx : qaB s x) (hr : 1 ≤ r) (ho : qW r) (hg : 1 ≤ gap)
    (hc : qct s r gap x K y) (hsep : qa s x t u) :
    qa K y t (qg s r x t u):= by
  rcases hc with ⟨hb,hcy,hd⟩
  rcases qz hx hr ho hsep with ⟨hQ,hQo,hH⟩
  rcases hsep with ⟨ht1,hts,_,_⟩
  refine ⟨ht1,by omega,?_,hQo⟩
  unfold h
  rw [hb,hcy]
  exact hH
lemma copies_next (s r gap : ℤ) (x : pair) (K : ℤ) (y : pair) (t u : ℤ) (z : pair)
    (hx : qaB s x) (hc : qct s r gap x K y)
    (hsep : qa s x t u) (hz : qo t z) :
    qct s r gap (qQ x t u z) (K + 1) (qbu (qQ y t (qg s r x t u) z)):= by
  rcases hc with ⟨hb,hcy,hd⟩
  have hL:=qaF r hx hsep hz
  have hB : (qbu (qQ y t (qg s r x t u) z)).b=left s r (qQ x t u z):= by
    rw [← hL]
    rfl
  have hm:=qI x t u z
  have hn:=qI y t (qg s r x t u) z
  have hs:=qu s r x
  have ht:=qu s r (qQ x t u z)
  refine ⟨hB,?_,?_⟩
  · change (qQ y t (qg s r x t u) z).c=right s r (qQ x t u z)
    change (qQ y t (qg s r x t u) z).b=left s r (qQ x t u z) at hB
    linarith
  · change K + 1 - (y.d + z.d + 1)=s - (x.d + z.d) + gap
    omega
def span (K : ℤ) (n : ℕ) (D : ℤ) : Prop :=
  ∀ i,0 ≤ i ∧ i ≤ (n : ℤ) → ∃ f,Built (K + i) f ∧ CheckTable.depth f ≤ D
lemma span_one (K : ℤ) (y : pair) (e v f D : ℤ)
    (h0 : Built K (.Two y e)) (h1 : Built (K + 1) (.One v f))
    (hD : y.d ≤ D) (hD0 : 0 ≤ D) :
    span K 1 D:= by
  intro i hi
  have hi' : i=0 ∨ i=1:= by omega
  rcases hi' with rfl | rfl
  · refine ⟨.Two y e,?_,hD⟩
    simpa using! h0
  · exact ⟨.One v f,h1,hD0⟩
lemma qa0 (K : ℤ) (f : entry) (n : ℕ) (D : ℤ)
    (h0 : Built K f) (hD : CheckTable.depth f ≤ D) (htail : span (K + 1) n D) :
    span K (1 + n) D:= by
  intro i hi
  by_cases hiz : i=0
  · subst hiz
    refine ⟨f,?_,hD⟩
    simpa using! h0
  · rcases htail (i - 1) (by omega) with ⟨g,hg,hdepth⟩
    refine ⟨g,?_,hdepth⟩
    have heq : K + i=K + 1 + (i - 1):= by omega
    rwa [heq]
theorem boundary_copy (s : ℤ) (x : pair) (f : ℤ) (n : ℕ)
    (hb : Boundary Built s x f n) (hx : qaB s x) :
    ∀ r gap K y e,1 ≤ r → qW r → 1 ≤ gap →
      qct s r gap x K y → Built K (.Two y e) →
      Built (K + (n : ℤ)) (.One (y.b + y.c + 3 * f) (e + f)) ∧
      span K n (K - s - gap + s + (n : ℤ) - 1):= by
  induction hb with
  | boundary_even x he =>
    intro r gap K y e hr hro hg hcopy hlarge
    have hy : qaB K y:=(built_valid hlarge).1.2.2.1.1
    have hp:=qaT s r gap x K y hx hro hg hcopy
    have hB : Built (K + 1) (.One (y.b + y.c + 3) (e + 1)) :=
      Built.built_even hlarge (by rw [hp,he])
    refine ⟨?_,?_⟩
    · simpa using! hB
    · apply span_one K y e (y.b + y.c + 3) (e + 1) _ hlarge hB
      · rcases hcopy with ⟨_,_,hD⟩; rcases hx with ⟨hdx0,_⟩; omega
      · rcases hcopy with ⟨_,_,hD⟩; rcases hx with ⟨hdx0,_⟩; rcases hy with ⟨hdy0,_⟩; omega
  | boundary_one x t u v f hsep ho hsmall =>
    intro r gap K y e hr hro hg hcopy hlarge
    have hy : qaB K y:=(built_valid hlarge).1.2.2.1.1
    have hp:=qaT s r gap x K y hx hro hg hcopy
    have hs:=qay s r gap x K y t u hx hr hro hg hcopy hsep
    have hB:=Built.built_lookup_one hlarge hs (by rw [hp,ho]) hsmall
    have hv : v=1 + 3 * f:=(built_valid hsmall).1.2.2
    have hB' : Built (K + 1) (.One (y.b + y.c + 3 * (1 + f)) (e + (1 + f))):= by
      have h1 : y.b + y.c + 3 * (1 + f)=y.b + y.c + v + 2:= by omega
      have h2 : e + (1 + f)=e + 1 + f:= by omega
      rwa [h1,h2]
    refine ⟨?_,?_⟩
    · simpa using! hB'
    · apply span_one K y e (y.b + y.c + 3 * (1 + f)) (e + (1 + f)) _ hlarge hB'
      · rcases hcopy with ⟨_,_,hD⟩; rcases hx with ⟨hdx0,_⟩; omega
      · rcases hcopy with ⟨_,_,hD⟩; rcases hx with ⟨hdx0,_⟩; rcases hy with ⟨hdy0,_⟩; omega
  | boundary_two x t u z f g n hsep ho hsmall htail ih =>
    intro r gap K y e hr hro hg hcopy hlarge
    have hy : qaB K y:=(built_valid hlarge).1.2.2.1.1
    rcases (built_valid hsmall).1 with ⟨ht0,hf,hz,hmass⟩
    have hp:=qaT s r gap x K y hx hro hg hcopy
    have hs:=qay s r gap x K y t u hx hr hro hg hcopy hsep
    have hB:=Built.built_lookup_two hlarge hs (by rw [hp,ho]) hsmall
    have hC:=copies_next s r gap x K y t u z hx hcopy hsep hz
    rcases ih (qan hx hsep hz).1 r gap (K + 1)
      (qbu (qQ y t (qg s r x t u) z)) (e + 1 + f) hr hro hg hC hB with ⟨hend,hspan⟩
    refine ⟨?_,?_⟩
    · have hk_eq : K + ((1 + n : ℕ) : ℤ)=K + 1 + (n : ℤ):= by push_cast; omega
      rw [hk_eq]
      change Built (K + 1 + (n : ℤ))
        (.One ((qQ y t (qg s r x t u) z).b + (qQ y t (qg s r x t u) z).c + 3 * g)
          (e + 1 + f + g)) at hend
      rw [qI] at hend
      have h1 : y.b + y.c + 3 * (1 + f + g)=y.b + y.c + z.b + z.c + 2 + 3 * g:= by omega
      have h2 : e + (1 + f + g)=e + 1 + f + g:= by omega
      rwa [h1,h2]
    · apply qa0 K (.Two y e) n _ hlarge
      · change y.d ≤ K - s - gap + s + ((1 + n : ℕ) : ℤ) - 1
        rcases hcopy with ⟨_,_,hD⟩
        rcases hx with ⟨hdx0,_⟩
        omega
      · have h_eq : K - s - gap + s + ((1 + n : ℕ) : ℤ) - 1 =
            K + 1 - s - gap + s + (n : ℤ) - 1:= by omega
        rwa [h_eq]
lemma qbI (K : ℤ) (n : ℕ) (D D' : ℤ) (hD : D ≤ D') (hspan : span K n D) :
    span K n D':= by
  intro i hi
  rcases hspan i hi with ⟨f,hf,hd⟩
  exact ⟨f,hf,by omega⟩
lemma span_zero (K : ℤ) (f : entry) (D : ℤ) (hf : Built K f) (hd : CheckTable.depth f ≤ D) :
    span K 0 D:= by
  intro i hi
  have hi0 : i=0:= by omega
  subst hi0
  refine ⟨f,?_,hd⟩
  simpa using! hf
lemma qbp (l B : ℤ) (hl : 1 ≤ l) :
    q3 (l + 1) ⟨1,1,B,0⟩=qb6 B:= by
  unfold q3 qk
  dsimp -failIfUnchanged
  rw [if_pos (by omega)]
lemma qbc (l B s r : ℤ) (hs : 1 ≤ s ∧ s < l)
    (hB : B + 3=q0 s * r) (hr : qW r) :
    qa (l + 1) ⟨1,1,B,0⟩ s r:= by
  refine ⟨hs.1,by dsimp -failIfUnchanged; omega,?_,hr⟩
  unfold h
  dsimp -failIfUnchanged
  linarith
lemma qcf (l B s r : ℤ) (x : pair) (hB : B + 3=q0 s * r) :
    qct s r (l - s) (qba x) (l + 2) (qbu (qQ ⟨1,1,B,0⟩ s r x)):= by
  refine ⟨rfl,?_,?_⟩
  · change B + 2 * 0 + 3 - (x.p * q0 (s - x.d) * r) + x.c - 0 - 1 =
      (q0 s - x.p * q0 (s - x.d)) * r + (x.c - 1)
    nlinarith
  · change l + 2 - (1 + x.d + 1)=s - x.d + (l - s)
    omega
lemma odd_factor (B s r : ℤ) (hs : 1 ≤ s) (hB : B + 3=q0 s * r) :
    qb6 B=false:= by
  rw [qa9]
  refine ⟨q0 (s - 1) * r - 2,?_⟩
  have hsp:=pow_split (k:=s) (d:=1) (by omega) hs
  rw [pow2_one] at hsp
  rw [hsp] at hB
  linarith
theorem stage_even (l B e : ℤ) (hl : 1 ≤ l) (hB : Built l (.One B e)) (he : qb6 B=true) :
    Built (l + 2) (.One (B + 3) (e + 1)) ∧ span l 2 1:= by
  have h1:=Built.built_one hB
  have h2 : Built (l + 1 + 1) (.One (B + 3) (e + 1)):= by
    have hB3 : B + 3=(⟨1,1,B,0⟩ : pair).b + (⟨1,1,B,0⟩ : pair).c + 3:= by dsimp -failIfUnchanged; omega
    rw [hB3]
    apply Built.built_even h1
    rw [qbp l B hl]
    exact he
  have h2' : Built (l + 2) (.One (B + 3) (e + 1)):= by
    have heq : l + 2=l + 1 + 1:= by omega
    rwa [heq]
  refine ⟨h2',?_⟩
  change span l (1 + (1 + 0)) 1
  apply qa0 l (.One B e) (1 + 0) 1 hB (by simp [CheckTable.depth])
  apply qa0 (l + 1) (.Two ⟨1,1,B,0⟩ e) 0 1 h1 (by simp [CheckTable.depth])
  exact span_zero (l + 1 + 1) (.One (B + 3) (e + 1)) 1 h2 (by simp [CheckTable.depth])
theorem stage_odd (l B e s r : ℤ) (g : entry)
    (hB : Built l (.One B e)) (hs : 1 ≤ s ∧ s < l)
    (hfactor : B + 3=q0 s * r) (hr : qW r)
    (hg : Built s g) (hreturn : qaf Built s g) :
    ∃ (n : ℕ) (v f : ℤ),(n : ℤ) ≤ s ∧ Built (l + 2 + (n : ℤ)) (.One v f) ∧ span l (2 + n) (2 * s + 1):= by
  rcases (built_valid hB).1 with ⟨hl,he,hBmass⟩
  change 0 ≤ e at he
  change B=1 + 3 * e at hBmass
  have hsp : 0 < q0 s:=pow_pos (by omega)
  have hr0 : 1 ≤ r:= by nlinarith
  have h1:=Built.built_one hB
  have hS:=qbc l B s r hs hfactor hr
  have hO : q3 (l + 1) ⟨1,1,B,0⟩=false:= by
    rw [qbp l B (by omega)]
    exact odd_factor B s r hs.1 hfactor
  have hprefix : ∀ n : ℕ,span (l + 2) n (2 * s + 1) → span l (2 + n) (2 * s + 1):= by
    intro n hspan
    have h2n : 2 + n=1 + (1 + n):= by omega
    rw [h2n]
    apply qa0 l (.One B e) (1 + n) (2 * s + 1) hB (by simp [CheckTable.depth]; omega)
    apply qa0 (l + 1) (.Two ⟨1,1,B,0⟩ e) n (2 * s + 1) h1 (by simp [CheckTable.depth]; omega)
    have heq : l + 1 + 1=l + 2:= by omega
    rwa [heq]
  cases g with
  | One v f =>
    have h2:=Built.built_lookup_one h1 hS hO hg
    have heq : l + 1 + 1=l + 2:= by omega
    rw [heq] at h2
    refine ⟨0,B + 0 + v + 2,e + 1 + f,by omega,?_,?_⟩
    · simpa using! h2
    · apply hprefix
      exact span_zero (l + 2) (.One (B + 0 + v + 2) (e + 1 + f)) (2 * s + 1) h2
        (by simp [CheckTable.depth]; omega)
  | Two x f =>
    have h2:=Built.built_lookup_two h1 hS hO hg
    have heq : l + 1 + 1=l + 2:= by omega
    rw [heq] at h2
    rcases (built_valid hg).1 with ⟨hs0,hf,hx,hmass⟩
    rcases hreturn with ⟨j,n,hbound⟩
    have hlow:=qb9 hx
    rcases qb5 (fun _ _ h => built_valid h) hbound hlow with ⟨hj,hn,hexec⟩
    have hd:=qcm hlow
    have hns : (n : ℤ) ≤ s:= by omega
    rcases boundary_copy s (qba x) j n hbound hlow r (l - s) (l + 2)
      (qbu (qQ ⟨1,1,B,0⟩ s r x)) (e + 1 + f) hr0 hr (by omega)
      (qcf l B s r x hfactor) h2 with ⟨hend,hspan⟩
    refine ⟨n,_,_,hns,hend,?_⟩
    apply hprefix
    exact qbI (l + 2) n _ (2 * s + 1) (by omega) hspan
end Phase
namespace Cubic
open Table
lemma cubic_exp (k : ℤ) (hk : 16 ≤ k) : 12 * k ^ 3 + 4 < q0 k:= by
  have h : ∀ n : ℕ,12 * (16 + (n : ℤ)) ^ 3 + 4 < q0 (16 + (n : ℤ)):= by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hcast : (16 + ((n + 1 : ℕ) : ℤ))=(16 + (n : ℤ)) + 1:= by push_cast; ring
      rw [hcast,q5 (by omega) (by omega),pow2_one]
      have hdiff : 2 * (12 * (16 + (n : ℤ)) ^ 3 + 4) - (12 * ((16 + (n : ℤ)) + 1) ^ 3 + 4) =
          12 * (n : ℤ) ^ 3 + 540 * (n : ℤ) ^ 2 + 8028 * (n : ℤ) + 39352:= by ring
      have hpos : 0 ≤ 12 * (n : ℤ) ^ 3 + 540 * (n : ℤ) ^ 2 + 8028 * (n : ℤ) + 39352:= by positivity
      linarith
  have hk_eq : k=16 + ((k - 16).toNat : ℤ):= by omega
  rw [hk_eq]
  exact h (k - 16).toNat
lemma cubic_exp2 (x : ℤ) (hx : 16 ≤ x) : 2048 * x ^ 3 ≤ 12 * q0 (2 * x - 2):= by
  have h : ∀ n : ℕ,2048 * (16 + (n : ℤ)) ^ 3 ≤ 12 * q0 (2 * (16 + (n : ℤ)) - 2):= by
    intro n
    induction n with
    | zero => decide
    | succ n ih =>
      have hcast1 : (16 + ((n + 1 : ℕ) : ℤ))=(16 + (n : ℤ)) + 1:= by push_cast; ring
      have hcast2 : 2 * ((16 + (n : ℤ)) + 1) - 2=(2 * (16 + (n : ℤ)) - 2) + 2:= by ring
      rw [hcast1,hcast2,q5 (by omega) (by omega)]
      have hp2 : q0 2=4:= by decide
      rw [hp2]
      have hdiff : 4 * (2048 * (16 + (n : ℤ)) ^ 3) - 2048 * ((16 + (n : ℤ)) + 1) ^ 3 =
          6144 * (n : ℤ) ^ 3 + 288768 * (n : ℤ) ^ 2 + 4515840 * (n : ℤ) + 23492608:= by ring
      have hpos : 0 ≤ 6144 * (n : ℤ) ^ 3 + 288768 * (n : ℤ) ^ 2 + 4515840 * (n : ℤ) + 23492608:= by positivity
      linarith
  have hx_eq : x=16 + ((x - 16).toNat : ℤ):= by omega
  rw [hx_eq]
  exact h (x - 16).toNat
lemma qbo (k s : ℤ) (hk : 2 ≤ k) (hs : 1 ≤ s) (hp : q0 s ≤ 24 * k ^ 3 + 4) :
    s ≤ 3 * q1 k + 4:= by
  set x:=q1 k
  have hx : 0 ≤ x:=qh k
  rcases qy (by omega : 1 < k) with ⟨hlo,hhi⟩
  have hE : q0 (3 * x + 5)=32 * q0 x ^ 3:= by
    have heq : 3 * x + 5=x + (x + (x + 5)):= by ring
    rw [heq,q5 hx (by omega),q5 hx (by omega),q5 hx (by omega)]
    have hp5 : q0 5=32:= by decide
    rw [hp5]
    ring
  have hcube : k ^ 3 ≤ q0 x ^ 3:=pow_le_pow_left₀ (by omega) hhi 3
  have hpow : 0 < q0 x:=pow_pos hx
  have hpow3 : 1 ≤ q0 x ^ 3:= by
    have : 1 ^ 3 ≤ q0 x ^ 3:=pow_le_pow_left₀ (by omega) (by omega : 1 ≤ q0 x) 3
    linarith
  have hL : q0 s < q0 (3 * x + 5):= by linarith
  have hlt:=(qv (by omega) (by omega)).mp hL
  omega
lemma growth (k s : ℤ) (hk : 65536 ≤ k) (hs : 1 ≤ s) (hp : q0 s ≤ 24 * k ^ 3 + 4) :
    1 + 4 * s ^ 3 ≤ 12 * k ^ 2:= by
  have hsbound:=qbo k s (by omega) hs hp
  set x:=q1 k
  have hx : 16 ≤ x:= by
    have hp16 : (65536 : ℤ)=q0 16:= by decide
    have hmono:=qt hk
    rw [hp16,qar (by omega)] at hmono
    exact hmono
  have hE:=cubic_exp2 x hx
  have hsmall : 1 + 4 * s ^ 3 ≤ 2048 * x ^ 3:= by
    have hcube : s ^ 3 ≤ (4 * x) ^ 3:=pow_le_pow_left₀ (by omega) (by omega : s ≤ 4 * x) 3
    have hx3 : 1 ≤ x ^ 3:= by
      have : 1 ^ 3 ≤ x ^ 3:=pow_le_pow_left₀ (by omega) (by omega : 1 ≤ x) 3
      linarith
    have h64 : (4 * x) ^ 3=64 * x ^ 3:= by ring
    linarith
  rcases qy (by omega : 1 < k) with ⟨hlo,hhi⟩
  have hP : q0 (2 * x - 2)=q0 (x - 1) * q0 (x - 1):= by
    have heq : 2 * x - 2=(x - 1) + (x - 1):= by ring
    rw [heq,q5 (by omega) (by omega)]
  rw [hP] at hE
  have hp_pos:=pow_pos (by omega : 0 ≤ x - 1)
  nlinarith
lemma lookup_h (k : ℤ) (x : pair) (e s r : ℤ)
    (hb : Built k (.Two x e)) (hsep : qa k x s r) (he : e ≤ 4 * k ^ 3) :
    q0 s ≤ 24 * k ^ 3 + 4:= by
  rcases hsep with ⟨hs1,hsk,hh,hr⟩
  rcases (built_valid hb).1 with ⟨hk,he0,hx,hmass⟩
  rcases hx with ⟨⟨hd0,hdk,hp,hpd,ho,hb0,hc⟩,hhalf,hc0⟩
  unfold h at hh
  have hp_pos:=pow_pos (by omega : 0 ≤ s)
  have hr1 : 1 ≤ r:= by nlinarith
  nlinarith
theorem qaV (k : ℤ) (f : entry) (h : Built k f) : qad f ≤ 4 * k ^ 3:= by
  induction h with
  | built_root => simp [qad]
  | @built_one k v e hb ih =>
    by_cases hbase : k + 1 ≤ 65536
    · have hk0:=UniqueTable.built_nonnegative hb
      exact (Finite.all_base ⟨by omega,hbase⟩ (Built.built_one hb)).1.1
    · change e ≤ 4 * k ^ 3 at ih
      change e ≤ 4 * (k + 1) ^ 3
      have hk0 : 0 ≤ k:= by omega
      have hdiff : 4 * (k + 1) ^ 3 - 4 * k ^ 3=12 * k ^ 2 + 12 * k + 4:= by ring
      have hpos : 0 ≤ 12 * k ^ 2 + 12 * k + 4:= by positivity
      linarith
  | @built_even k x e hb he ih =>
    by_cases hbase : k + 1 ≤ 65536
    · have hk0:=UniqueTable.built_nonnegative hb
      exact (Finite.all_base ⟨by omega,hbase⟩ (Built.built_even hb he)).1.1
    · change e ≤ 4 * k ^ 3 at ih
      change e + 1 ≤ 4 * (k + 1) ^ 3
      have hk0 : 0 ≤ k:= by omega
      have hdiff : 4 * (k + 1) ^ 3 - (4 * k ^ 3 + 1)=12 * k ^ 2 + 12 * k + 3:= by ring
      have hpos : 0 ≤ 12 * k ^ 2 + 12 * k + 3:= by positivity
      linarith
  | @built_lookup_one k x e s r v f hb hs ho hsmall ih ihsmall =>
    by_cases hbase : k + 1 ≤ 65536
    · have hk0:=UniqueTable.built_nonnegative hb
      exact (Finite.all_base ⟨by omega,hbase⟩ (Built.built_lookup_one hb hs ho hsmall)).1.1
    · change e ≤ 4 * k ^ 3 at ih
      change f ≤ 4 * s ^ 3 at ihsmall
      change e + 1 + f ≤ 4 * (k + 1) ^ 3
      have hgrow:=growth k s (by omega) hs.1 (lookup_h k x e s r hb hs ih)
      have hk0 : 0 ≤ k:= by omega
      have hdiff : 4 * (k + 1) ^ 3 - (4 * k ^ 3 + 12 * k ^ 2)=12 * k + 4:= by ring
      linarith
  | @built_lookup_two k x e s r y f hb hs ho hsmall ih ihsmall =>
    by_cases hbase : k + 1 ≤ 65536
    · have hk0:=UniqueTable.built_nonnegative hb
      exact (Finite.all_base ⟨by omega,hbase⟩ (Built.built_lookup_two hb hs ho hsmall)).1.1
    · change e ≤ 4 * k ^ 3 at ih
      change f ≤ 4 * s ^ 3 at ihsmall
      change e + 1 + f ≤ 4 * (k + 1) ^ 3
      have hgrow:=growth k s (by omega) hs.1 (lookup_h k x e s r hb hs ih)
      have hk0 : 0 ≤ k:= by omega
      have hdiff : 4 * (k + 1) ^ 3 - (4 * k ^ 3 + 12 * k ^ 2)=12 * k + 4:= by ring
      linarith
end Cubic
namespace Stages
open Table Phase Cubic
lemma split2_spec (x : ℤ) (hx : 0 < x) :
    let s:=(q4 x.toNat x).1
    let r:=(q4 x.toNat x).2
    0 ≤ s ∧ 1 ≤ r ∧ qW r ∧ x=q0 s * r:= by
  rcases qbH hx with ⟨hs0,heq,hodd⟩
  have hp:=qc hs0
  exact ⟨hs0,by nlinarith,hodd,heq⟩
lemma qbv (l B e : ℤ) (hl : 16 ≤ l) (hB : Built l (.One B e)) (ho : qb6 B=false) :
    ∃ s r,(1 ≤ s ∧ s < l) ∧ B + 3=q0 s * r ∧ qW r ∧ s ≤ 3 * q1 l + 4:= by
  rcases (built_valid hB).1 with ⟨hl0,he0,hmass⟩
  change 0 ≤ e at he0
  change B=1 + 3 * e at hmass
  have hE : e ≤ 4 * l ^ 3:=qaV l (.One B e) hB
  have hpos : 0 < B + 3:= by omega
  rcases split2_spec (B + 3) hpos with ⟨hs,hr,hro,hfactor⟩
  set s:=(q4 (B + 3).toNat (B + 3)).1
  set r:=(q4 (B + 3).toNat (B + 3)).2
  have hs1 : 1 ≤ s:= by
    by_contra hlt
    have hs0 : s=0:= by omega
    rw [hs0,pow2_zero,one_mul] at hfactor
    rcases hro with ⟨t,ht⟩
    have hBeven : ZEven B:=⟨t - 1,by omega⟩
    have htr:=(qah B).mpr hBeven
    rw [ho] at htr
    contradiction
  have hp:=pow_pos hs
  have hbound : q0 s ≤ 12 * l ^ 3 + 4:= by nlinarith
  have hlt : q0 s < q0 l:= by
    have:=cubic_exp l hl
    omega
  have hsl : s < l:=(qv hs (by omega)).mp hlt
  have hl3 : 0 ≤ l ^ 3:= by positivity
  exact ⟨s,r,⟨hs1,hsl⟩,hfactor,hro,qbo l s (by omega) hs1 (by linarith)⟩
theorem next_stage (l B e : ℤ) (hl : 16 ≤ l) (hB : Built l (.One B e))
    (hsmall : ∀ s,1 ≤ s ∧ s < l → ∃ g,Built s g ∧ qaf Built s g) :
    ∃ (n : ℕ) (v f : ℤ),2 ≤ (n : ℤ) ∧ Built (l + (n : ℤ)) (.One v f) ∧ span l n (6 * q1 l + 9):= by
  cases he : qb6 B
  · rcases qbv l B e hl hB he with ⟨s,r,hs,hfactor,hr,hbound⟩
    rcases hsmall s hs with ⟨g,hg,hreturn⟩
    rcases stage_odd l B e s r g hB hs hfactor hr hg hreturn with ⟨n,v,f,hn,hend,hspan⟩
    refine ⟨2 + n,v,f,by omega,?_,?_⟩
    · have heq : l + ((2 + n : ℕ) : ℤ)=l + 2 + (n : ℤ):= by omega
      rwa [heq]
    · exact qbI l (2 + n) (2 * s + 1) (6 * q1 l + 9) (by omega) hspan
  · rcases stage_even l B e (by omega) hB he with ⟨hend,hspan⟩
    refine ⟨2,B + 3,e + 1,by omega,?_,?_⟩
    · simpa using! hend
    · have hlog:=qh l
      exact qbI l 2 1 (6 * q1 l + 9) (by omega) hspan
theorem through (target : ℤ) (htarget : 0 ≤ target)
    (hreturns : ∀ s,1 ≤ s ∧ s < target → ∃ g,Built s g ∧ qaf Built s g) :
    ∃ f,Built target f ∧ CheckTable.bounded target f:= by
  by_cases hbase : target ≤ 16
  · by_cases htz : target=0
    · subst htz
      exact ⟨.One 1 0,Built.built_root,by simp [CheckTable.bounded,qad,CheckTable.depth,q1]⟩
    · rcases CheckTable.base_structured target ⟨by omega,by omega⟩ with ⟨f,hf,hbounds,_⟩
      exact ⟨f,hf,hbounds⟩
  · have hgo : ∀ (n : ℕ) (l B e : ℤ),(16 ≤ l ∧ l ≤ target) → target - l ≤ (n : ℤ) →
        Built l (.One B e) → ∃ f,Built target f ∧ CheckTable.bounded target f:= by
      intro n
      induction n with
      | zero =>
        intro l B e hl hfuel hB
        have htl : target=l:= by omega
        subst htl
        refine ⟨.One B e,hB,qaV target (.One B e) hB,?_⟩
        simp only [CheckTable.depth]
        have:=qh target
        omega
      | succ n ih =>
        intro l B e hl hfuel hB
        rcases next_stage l B e hl.1 hB (fun s hs => hreturns s ⟨hs.1,by omega⟩) with
          ⟨m,v,f,hm,hend,hspan⟩
        by_cases hstop : target ≤ l + (m : ℤ)
        · rcases hspan (target - l) ⟨by omega,by omega⟩ with ⟨g,hg,hD⟩
          have heq : l + (target - l)=target:= by omega
          rw [heq] at hg
          have hlog:=qt hl.2
          exact ⟨g,hg,qaV target g hg,by omega⟩
        · exact ih (l + (m : ℤ)) v f ⟨by omega,by omega⟩ (by omega) hend
    exact hgo (target - 16).toNat 16 37 12 ⟨by omega,by omega⟩ (by omega) CheckTable.P16
end Stages
namespace BoundaryBound
open Table WordLibrary
lemma qbV (k : ℤ) (x : pair) (s r : ℤ) (y : pair) (e : ℤ)
    (hsep : qa k x s r) (hb : Built s (.Two y e)) :
    action ⟨s,y⟩ (x.b + x.c) x.b ((qQ x s r y).b + (qQ x s r y).c) (qQ x s r y).b:= by
  rcases (built_valid hb).1 with ⟨hs,he,hy,hmass⟩
  refine ⟨by rw [qI]; unfold gain; dsimp -failIfUnchanged; ring,?_,?_⟩
  · have hdelta:=qbU hsep hy
    unfold qQ h at *
    dsimp -failIfUnchanged at *
    linarith
  · rcases hsep with ⟨_,_,hh,t,rfl⟩
    refine ⟨t,?_⟩
    unfold h at hh
    dsimp -failIfUnchanged
    linarith
lemma qbJ (k : ℤ) (x : pair) (L : ℤ)
    (hx : qaB k x) (hL : 1 ≤ L) (hdepth : x.d + L < k) (hbound : h x < q0 L)
    (he : q3 k x=false) :
    ∃ s r,qa k x s r ∧ s < L:= by
  rcases hx with ⟨hd,hdk,hp,hpd,ho,hb,hc⟩
  have hpos : 0 < h x:= by unfold h; omega
  have hbodd : qW x.b:= by
    unfold q3 qk at he
    rw [if_pos (by omega : x.d < k)] at he
    exact (qa9 x.b).mp he
  rcases Stages.split2_spec (h x) hpos with ⟨hs,hr,hro,hfactor⟩
  set s:=(q4 (h x).toNat (h x)).1
  set r:=(q4 (h x).toNat (h x)).2
  have hs1 : 1 ≤ s:= by
    by_contra hlt
    have hs0 : s=0:= by omega
    rw [hs0,pow2_zero,one_mul] at hfactor
    unfold h at hfactor
    rcases hbodd with ⟨a,ha⟩
    rcases hro with ⟨v,hv⟩
    omega
  have hsL : s < L:= by
    apply (qv hs (by omega)).mp
    have hp2:=pow_pos hs
    nlinarith
  exact ⟨s,r,⟨hs1,by omega,hfactor,hro⟩,hsL⟩
lemma qbD (k L D M : ℤ)
    (hL : 1 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (hlib : ∀ s,1 ≤ s ∧ s ≤ L → ∃ f,Built s f)
    (hparams : ∀ s y e,1 ≤ s ∧ s ≤ L → Built s (.Two y e) → y.d ≤ D ∧ y.b + y.c + 2 ≤ M)
    (n : ℕ) :
    ∀ x,qaB k x → x.d + (n : ℤ) * D + L < k →
      2 * (x.b + x.c + (n : ℤ) * M) + 3 < q0 L →
      (∃ e m,Boundary Built k x e m) ∨
      (∃ word : List kernel,word.length=n ∧
        (∀ z ∈ word,continuing z ∧ z.index ≤ L) ∧
        trace word (x.b + x.c) x.b):= by
  induction n with
  | zero =>
    intro x hx hdepth hmass
    right
    exact ⟨[],rfl,by simp,trace.trace_nil _ _⟩
  | succ n ih =>
    intro x hx hdepth hmass
    cases he : q3 k x
    · have hxdepth : x.d + L < k:= by nlinarith
      have hxbound : h x < q0 L:= by
        rcases hx with ⟨_,_,_,_,_,hb,hc⟩
        unfold h
        nlinarith
      rcases qbJ k x L hx hL hxdepth hxbound he with ⟨s,r,hsep,hsL⟩
      have hs : 1 ≤ s ∧ s ≤ L:=⟨hsep.1,by omega⟩
      rcases hlib s hs with ⟨f_s,hb⟩
      cases f_s with
      | One v e =>
        left
        exact ⟨1 + e,1,Boundary.boundary_one x s r v e hsep he hb⟩
      | Two y e =>
        rcases (built_valid hb).1 with ⟨hs0,he0,hy,hysum⟩
        rcases qan hx hsep hy with ⟨hnext,hc⟩
        have hP:=Bridge.lookup_parity hx hsep hy
        cases hparity : q3 s y
        · rcases hparams s y e hs hb with ⟨hDy,hMy⟩
          have hdepth' : (qQ x s r y).d + (n : ℤ) * D + L < k:= by
            change x.d + y.d + (n : ℤ) * D + L < k
            push_cast at hdepth
            linarith
          have hmass' : 2 * ((qQ x s r y).b + (qQ x s r y).c + (n : ℤ) * M) + 3 < q0 L:= by
            rw [qI]
            push_cast at hmass
            linarith
          rcases ih (qQ x s r y) hnext hdepth' hmass' with
            ⟨f,m,hreturn⟩ | ⟨word,hlen,hall,htrace⟩
          · left
            exact ⟨1 + e + f,1 + m,Boundary.boundary_two x s r y e f m hsep he hb hreturn⟩
          · right
            refine ⟨⟨s,y⟩ :: word,by simp [hlen],?_,?_⟩
            · intro z hz
              rcases List.mem_cons.mp hz with rfl | hz'
              · exact ⟨⟨e,hb,hs.1,hparity⟩,hs.2⟩
              · exact hall z hz'
            · exact trace.trace_cons (qbV k x s r y e hsep hb) htrace
        · left
          refine ⟨1 + e + 1,2,Boundary.boundary_two x s r y e 1 1 hsep he hb ?_⟩
          exact Boundary.boundary_even (qQ x s r y) (by rw [hP,hparity])
    · left
      exact ⟨1,1,Boundary.boundary_even x he⟩
theorem returns_of_bound (k : ℤ) (x : pair) (L D M : ℤ) (n : ℕ)
    (hL : 1 ≤ L) (hD : 0 ≤ D) (hM : 0 ≤ M) (hx : qaB k x)
    (hlib : ∀ s,1 ≤ s ∧ s ≤ L → ∃ f,Built s f)
    (hparams : ∀ s y e,1 ≤ s ∧ s ≤ L → Built s (.Two y e) → y.d ≤ D ∧ y.b + y.c + 2 ≤ M)
    (hwords : WordLink.bound L ((n : ℤ) - 1))
    (hdepth : x.d + (n : ℤ) * D + L < k)
    (hmass : 2 * (x.b + x.c + (n : ℤ) * M) + 3 < q0 L) :
    ∃ e m,Boundary Built k x e m:= by
  rcases qbD k L D M hL hD hM hlib hparams n x hx hdepth hmass with
    hreturn | ⟨word,hlen,hall,htrace⟩
  · exact hreturn
  · have hbw:=hwords word (x.b + x.c) x.b hall htrace
    rw [hlen] at hbw
    omega
end BoundaryBound
namespace Closure
open Table
def good (k : ℤ) : Prop :=
  ∃ f,Built k f ∧ CheckTable.bounded k f ∧ qaf Built k f
def earlier (k : ℤ) : Prop :=
  ∀ s,1 ≤ s ∧ s < k → good s
def budget (k : ℤ) : Prop :=
  ∃ L : ℤ,∃ n : ℕ,(1 ≤ L ∧ L < k) ∧ WordLink.bound L ((n : ℤ) - 1) ∧
    6 * q1 k + 9 + (n : ℤ) * (6 * q1 L + 9) + L < k ∧
    2 * (12 * k ^ 3 + (n : ℤ) * (12 * L ^ 3 + 3)) + 3 < q0 L
lemma qch (k : ℤ) (h : earlier k) :
    ∀ s f,1 ≤ s ∧ s < k → Built s f → CheckTable.bounded s f:= by
  intro s f hs hf
  rcases h s hs with ⟨g,hg,hbounds,_⟩
  have heq:=UniqueTable.built_unique hf g hg
  subst heq
  exact hbounds
lemma kernel_bounds (k L : ℤ) (hL : 1 ≤ L ∧ L < k) (hprev : earlier k) :
    ∀ s y e,(1 ≤ s ∧ s ≤ L) → Built s (.Two y e) →
      y.d ≤ 6 * q1 L + 9 ∧ y.b + y.c + 2 ≤ 12 * L ^ 3 + 3:= by
  intro s y e hs hb
  rcases qch k hprev s (.Two y e) ⟨hs.1,by omega⟩ hb with ⟨hE,hD⟩
  change e ≤ 4 * s ^ 3 at hE
  change y.d ≤ 6 * q1 s + 9 at hD
  have hlog:=qt hs.2
  have hpow : s ^ 3 ≤ L ^ 3:=pow_le_pow_left₀ (by omega) hs.2 3
  rcases (built_valid hb).1 with ⟨hs0,he,hy,hmass⟩
  exact ⟨by omega,by omega⟩
theorem close (k : ℤ) (hk : 1 ≤ k) (hprevious : earlier k) (hbudget : budget k) :
    good k:= by
  rcases hbudget with ⟨L,n,hL,hword,hdepth,hmass⟩
  have hentries : ∀ s,1 ≤ s ∧ s < k → ∃ f,Built s f ∧ qaf Built s f:= by
    intro s hs
    rcases hprevious s hs with ⟨f,hf,_,hreturn⟩
    exact ⟨f,hf,hreturn⟩
  rcases Stages.through k (by omega) hentries with ⟨f,hf,hbounds⟩
  refine ⟨f,hf,hbounds,?_⟩
  cases f with
  | One v e => trivial
  | Two x e =>
    rcases hbounds with ⟨hE,hD⟩
    change e ≤ 4 * k ^ 3 at hE
    change x.d ≤ 6 * q1 k + 9 at hD
    rcases (built_valid hf).1 with ⟨hk0,he,hx,hsum⟩
    have hL0 : 0 ≤ L:= by omega
    have hL3 : 0 ≤ L ^ 3:= by positivity
    apply BoundaryBound.returns_of_bound k (qba x) L
      (6 * q1 L + 9) (12 * L ^ 3 + 3) n
    · omega
    · have:=qh L; omega
    · omega
    · exact qb9 hx
    · intro s hs
      rcases hentries s ⟨hs.1,by omega⟩ with ⟨g,hg,_⟩
      exact ⟨g,hg⟩
    · exact kernel_bounds k L hL hprevious
    · exact hword
    · change x.d + (n : ℤ) * (6 * q1 L + 9) + L < k
      omega
    · change 2 * (x.b + (x.c - 1) + (n : ℤ) * (12 * L ^ 3 + 3)) + 3 < q0 L
      omega
theorem qae (k : ℤ) (hk : 1 ≤ k) (hprevious : earlier k)
    (hbudget : 65536 < k → budget k) : good k:= by
  by_cases hsmall : k ≤ 65536
  · exact CheckTable.base_structured k ⟨hk,hsmall⟩
  · exact close k hk hprevious (hbudget (by omega))
theorem all_good (hbudget : ∀ k,65536 < k → earlier k → budget k) :
    ∀ k,1 ≤ k → good k:= by
  have hnat : ∀ n : ℕ,1 ≤ n → good (n : ℤ):= by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro hn
      have hprevious : earlier (n : ℤ):= by
        intro s hs
        have hs_eq : s=(s.toNat : ℤ):= by omega
        rw [hs_eq]
        exact ih s.toNat (by omega) (by omega)
      exact qae (n : ℤ) (by omega) hprevious (fun hlarge => hbudget (n : ℤ) hlarge hprevious)
  intro k hk
  have hk_eq : k=(k.toNat : ℤ):= by omega
  rw [hk_eq]
  exact hnat k.toNat (by omega)
theorem G_returns (hbudget : ∀ k,65536 < k → earlier k → budget k) :
    ∀ k t : ℕ,∃ e m,Prefix.Exec e (Prefix.G (1 + k) (1 + 2 * t)) [m]:= by
  intro k t
  rcases all_good hbudget ((1 + k : ℕ) : ℤ) (by omega) with ⟨f,hf,hbounds,hreturn⟩
  have h:=Table.G_returns (fun s g hsg => built_valid hsg)
    (built_valid hf) hreturn (by omega) ((1 + 2 * t : ℕ) : ℤ) (by omega)
    ⟨(t : ℤ),by push_cast; ring⟩
  unfold Table.G at h
  simpa only [Int.toNat_natCast] using! h
end Closure
namespace HighPath
open Block
def certified (m D M B : ℤ) (z : summary) : Prop :=
  ∃ d,(0 ≤ d ∧ d ≤ D) ∧ z.scale=q0 d ∧ (z.scale ≤ z.sc ∧ z.sc ≤ 2 * z.scale) ∧
    (0 < z.offset ∧ z.offset ≤ z.scale * (2 * M + 2)) ∧ (m < z.added ∧ z.added ≤ M) ∧
    2 * z.offset ≤ z.sc * (3 * z.added + 2 * B + 6)
inductive path (m D M B : ℤ) : List summary → ℤ → ℤ → Prop where
  | path_stop (S H : ℤ) : q0 (m + 1) ∣ H → path m D M B [] S H
  | path_step (z : summary) (zs : List summary) (S H H' : ℤ) :
      q0 (m + 1) ∣ H → certified m D M B z →
      denotes z S H (S + z.added) H' → path m D M B zs (S + z.added) H' →
      path m D M B (z :: zs) S H
lemma path_div (m D M B : ℤ) (zs : List summary) (S H : ℤ)
    (hp : path m D M B zs S H) : q0 (m + 1) ∣ H:= by
  cases hp with
  | path_stop _ _ h => exact h
  | path_step _ _ _ _ _ h _ _ _ => exact h
inductive chain (m D M B : ℤ) : List summary → Prop where
  | chain_one (z : summary) : certified m D M B z → chain m D M B [z]
  | chain_more (z z' : summary) (zs : List summary) :
      certified m D M B z →
      z.sc * z'.offset=z'.sc * (z.offset - z.sc * z.added) →
      chain m D M B (z' :: zs) →
      chain m D M B (z :: z' :: zs)
lemma adjacent (m D M B : ℤ) (z z' : summary) (S H0 H1 H2 : ℤ)
    (hm : 0 ≤ m)
    (hz : certified m D M B z) (hz' : certified m D M B z')
    (hH0 : q0 (m + 1) ∣ H0) (hH1 : q0 (m + 1) ∣ H1) (hH2 : q0 (m + 1) ∣ H2)
    (hden0 : denotes z S H0 (S + z.added) H1)
    (hden1 : denotes z' (S + z.added) H1 (S + z.added + z'.added) H2)
    (hbudget : q0 (2 * D) * (12 * M + 8) < q0 (m + 1)) :
    z.sc * z'.offset=z'.sc * (z.offset - z.sc * z.added):= by
  rcases hz with ⟨d0,⟨hd00,hd01⟩,hQ0,⟨hA00,hA01⟩,⟨hC00,hC01⟩,⟨hM00,hM01⟩,_⟩
  rcases hz' with ⟨d1,⟨hd10,hd11⟩,hQ1,⟨hA10,hA11⟩,⟨hC10,hC11⟩,_,_⟩
  rcases hden0 with ⟨_,hE0⟩
  rcases hden1 with ⟨_,hE1⟩
  rw [hQ0] at hA00 hA01 hC01 hE0
  rw [hQ1] at hA10 hA11 hC11 hE1
  have hp0:=qc hd00
  have hp1:=qc hd10
  exact qci m D d0 d1 S H0 H1 H2 z.sc z'.sc z.hc z'.hc z.offset z'.offset z.added M
    hm hd00 hd01 hd10 hd11 (by omega) hM01
    (by omega) hA01 (by omega) hA11
    (by omega) hC01 (by omega) hC11
    hH0 hH1 hH2 hE0 hE1 hbudget
lemma path_chain (m D M B : ℤ) (zs : List summary) (S H : ℤ)
    (hm : 0 ≤ m) (hbudget : q0 (2 * D) * (12 * M + 8) < q0 (m + 1))
    (hp : path m D M B zs S H) (hne : zs ≠ []) : chain m D M B zs:= by
  induction hp with
  | path_stop _ _ _ => contradiction
  | path_step z zs S H H' hH hz hstep htail ih =>
    cases zs with
    | nil => exact chain.chain_one z hz
    | cons z' zs' =>
      cases htail with
      | path_step _ _ _ _ H2 hH1 hz' hstep' htail' =>
        have hH2 : q0 (m + 1) ∣ H2:=path_div m D M B zs' (S + z.added + z'.added) H2 htail'
        have hadj:=adjacent m D M B z z' S H H' H2 hm hz hz' hH hH1 hH2 hstep hstep' hbudget
        exact chain.chain_more z z' zs' hz hadj (ih (by simp))
inductive roots (A B m : ℤ) : ℤ → ℕ → Prop where
  | roots_one (f : ℤ) : 0 < f → roots A B m f 0
  | roots_more (f g : ℤ) (n : ℕ) :
      3 * g ≤ f + 2 * A * (B + 3) →
      g < f - A * m →
      roots A B m g n →
      roots A B m f (n + 1)
lemma qc4 (A B m f : ℤ) (n : ℕ) (hr : roots A B m f n) :
    ∃ v : ℕ → ℤ,v 0=f ∧ 0 < v n ∧
      ∀ i < n,3 * v (i + 1) ≤ v i + 2 * A * (B + 3) ∧ v (i + 1) < v i - A * m:= by
  induction hr with
  | roots_one f hf =>
    refine ⟨fun _ => f,rfl,hf,fun i hi => by omega⟩
  | roots_more f g n hshrink hdrop _ ih =>
    rcases ih with ⟨v,hv0,hvn,hsteps⟩
    refine ⟨fun i => match i with | 0 => f | j + 1 => v j,rfl,hvn,?_⟩
    intro i hi
    cases i with
    | zero =>
      dsimp -failIfUnchanged
      rw [hv0]
      exact ⟨hshrink,hdrop⟩
    | succ j =>
      exact hsteps j (by omega)
lemma roots_count (A B m f : ℤ) (n t q : ℕ) (V : ℤ)
    (hA : 0 < A) (hB : 0 ≤ B) (hm : 0 < m) (hV : 0 ≤ V)
    (hpow : V ≤ (3 : ℤ) ^ t) (hq : B + 4 ≤ (q : ℤ) * m) (hf : f ≤ A * V)
    (hr : roots A B m f n) : n < t + q:= by
  rcases qc4 A B m f n hr with ⟨v,hv0,hlast,hsteps⟩
  apply high_count v A B V m t q n hA hB hm hV hpow hq
  · rw [hv0]; exact hf
  · exact hlast
  · intro i hi; exact (hsteps i hi).1
  · intro i hi; exact (hsteps i hi).2
lemma chain_roots (m D M B : ℤ) (zs : List summary) (hch : chain m D M B zs) :
    ∀ z rest,zs=z :: rest → ∀ A f,0 < A → A * z.offset=z.sc * f →
      roots A B m f rest.length:= by
  induction hch with
  | chain_one z hz =>
    intro z0 rest heq A f hA hroot
    injection heq with hz0 hrest
    subst hz0 hrest
    rcases hz with ⟨d,⟨hd0,_⟩,hQ,⟨hsc1,_⟩,⟨hc1,_⟩,_,_⟩
    have hp:=qc hd0
    have hsc_pos : 0 < z.sc:= by linarith
    have hAf_pos : 0 < z.sc * f:= by nlinarith
    have hf_pos : 0 < f:= by nlinarith
    exact roots.roots_one f hf_pos
  | chain_more z z' zs hz hdescent _ ih =>
    intro z0 rest heq A f hA hroot
    injection heq with hz0 hrest
    subst hz0 hrest
    rcases hz with ⟨d,⟨hd0,_⟩,hQ,⟨hsc1,_⟩,⟨hc1,_⟩,⟨hm1,_⟩,hcontract⟩
    have hp:=qc hd0
    have hsc_pos : 0 < z.sc:= by linarith
    have hnext : A * z'.offset=z'.sc * (f - A * z.added):= by
      have hroot0 : A * z.offset=z.sc * (f - A * 0):= by
        simpa using! hroot
      have hprop:=qc6 A f z.sc z.offset z'.sc z'.offset 0 z.added hsc_pos hroot0 hdescent
      simpa using! hprop
    apply roots.roots_more f (f - A * z.added) zs.length
    · have hmul : A * (2 * z.offset) ≤ A * (z.sc * (3 * z.added + 2 * B + 6)) :=
        mul_le_mul_of_nonneg_left hcontract (by omega)
      nlinarith
    · nlinarith
    · exact ih z' zs rfl A (f - A * z.added) hA hnext
theorem path_count (m D M B : ℤ) (zs : List summary) (S H : ℤ) (t q : ℕ)
    (hm : 0 < m) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hpow : 2 * M + 2 ≤ (3 : ℤ) ^ t) (hq : B + 4 ≤ (q : ℤ) * m)
    (hbudget : q0 (2 * D) * (12 * M + 8) < q0 (m + 1))
    (hp : path m D M B zs S H) : zs.length < t + q + 1:= by
  cases zs with
  | nil => simp
  | cons z rest =>
    have hch : chain m D M B (z :: rest) :=
      path_chain m D M B (z :: rest) S H (by omega) hbudget hp (by simp)
    cases hp with
    | path_step _ _ _ _ _ _ hz _ _ =>
      rcases hz with ⟨d,⟨hd0,_⟩,hQ,⟨hA1,_⟩,⟨hC1,hC2⟩,_,_⟩
      have hp_pos:=qc hd0
      have hsc_pos : 0 < z.sc:= by linarith
      have hr : roots z.sc B m z.offset rest.length :=
        chain_roots m D M B (z :: rest) hch z rest rfl z.sc z.offset hsc_pos rfl
      have hrc : rest.length < t + q :=
        roots_count z.sc B m z.offset rest.length t q (2 * M + 2)
          hsc_pos hB hm (by omega) hpow hq (by nlinarith) hr
      simp; omega
end HighPath
namespace WordBlocks
open WordLibrary
def qD (f : kernel → ℤ) (word : List kernel) : ℤ :=
  word.foldr (fun k z => f k + z) 0
def depth (k : kernel) : ℤ:=k.pair.d
def qw (word : List kernel) : List Block.kernel :=
  word.map (fun k => Bridge.kernel k.pair)
def summary (word : List kernel) : Block.summary :=
  (qw word).foldl (fun z k => Block.push k z) Block.identity
lemma qaj (f : kernel → ℤ) (word : List kernel)
    (h : ∀ k ∈ word,0 ≤ f k) : 0 ≤ qD f word:= by
  induction word with
  | nil => simp [qD]
  | cons k word ih =>
    have hk:=h k (by simp)
    have hrest:=ih (fun x hx => h x (by simp [hx]))
    rw [qD,List.foldr_cons,← qD]
    omega
lemma qbF (f : kernel → ℤ) (word : List kernel) (C : ℤ)
    (h : ∀ k ∈ word,0 ≤ f k ∧ f k ≤ C) :
    0 ≤ qD f word ∧ qD f word ≤ (word.length : ℤ) * C:= by
  induction word with
  | nil => simp [qD]
  | cons k word ih =>
    have hk:=h k (by simp)
    have hrest:=ih (fun x hx => h x (by simp [hx]))
    rw [qD,List.foldr_cons,← qD]
    simp only [List.length_cons]
    push_cast
    constructor
    · omega
    · nlinarith
lemma fold_added (word : List kernel) (z : Block.summary) :
    ((qw word).foldl (fun z k => Block.push k z) z).added=z.added + qD gain word:= by
  induction word generalizing z with
  | nil => simp [qw,qD]
  | cons k word ih =>
    rw [qw,List.map_cons,List.foldl_cons,← qw,qD,List.foldr_cons,← qD]
    rw [ih]
    dsimp -failIfUnchanged [Block.push,Bridge.kernel,gain]
    ring
lemma qca (word : List kernel) (z : Block.summary) :
    ((qw word).foldl (fun z k => Block.low_push k z) z).added=z.added + qD gain word:= by
  induction word generalizing z with
  | nil => simp [qw,qD]
  | cons k word ih =>
    rw [qw,List.map_cons,List.foldl_cons,← qw,qD,List.foldr_cons,← qD]
    rw [ih]
    dsimp -failIfUnchanged [Block.low_push,Bridge.kernel,gain]
    ring
lemma fold_scale (word : List kernel) (z : Block.summary)
    (h : ∀ k ∈ word,0 ≤ depth k) :
    ((qw word).foldl (fun z k => Block.push k z) z).scale=z.scale * q0 (qD depth word):= by
  induction word generalizing z with
  | nil => simp [qw,qD,pow2_zero]
  | cons k word ih =>
    have hk : 0 ≤ depth k:=h k (by simp)
    have hrest : ∀ x ∈ word,0 ≤ depth x:=fun x hx => h x (by simp [hx])
    have htot : 0 ≤ qD depth word:=qaj depth word hrest
    rw [qw,List.map_cons,List.foldl_cons,← qw,qD,List.foldr_cons,← qD]
    rw [ih (Block.push (Bridge.kernel k.pair) z) hrest]
    rw [q5 hk htot]
    dsimp -failIfUnchanged [Block.push,Bridge.kernel,depth]
    ring
lemma fold_strong (ks : List Block.kernel) (z : Block.summary)
    (hgood : ∀ k ∈ ks,Block.good k) (hz : Block.bounded z) (hne : ks ≠ []) :
    let r:=ks.foldl (fun z k => Block.push k z) z
    Block.bounded r ∧ r.scale ≤ r.sc ∧ 0 < r.offset:= by
  induction ks generalizing z with
  | nil => contradiction
  | cons k ks ih =>
    have hk : Block.good k:=hgood k (by simp)
    cases ks with
    | nil =>
      simp only [List.foldl_cons,List.foldl_nil]
      exact Block.push_bounded k z hk hz
    | cons a ks' =>
      simp only [List.foldl_cons]
      have hpush:=(Block.push_bounded k z hk hz).1
      exact ih (Block.push k z) (fun x hx => hgood x (by simp [hx])) hpush (by simp)
lemma summary_data (word : List kernel)
    (hall : ∀ k ∈ word,continuing k) (hne : word ≠ []) :
    0 ≤ qD depth word ∧
    (summary word).scale=q0 (qD depth word) ∧
    Block.bounded (summary word) ∧
    (summary word).scale ≤ (summary word).sc ∧
    0 < (summary word).offset ∧
    (summary word).added=qD gain word:= by
  have hgood : ∀ k ∈ qw word,Block.good k:= by
    intro bk hbk
    rcases List.mem_map.mp hbk with ⟨k,hk_mem,rfl⟩
    exact WordLink.continuing_good k (hall k hk_mem)
  have hdepth : ∀ k ∈ word,0 ≤ depth k:= by
    intro k hk_mem
    rcases hall k hk_mem with ⟨e,hb,_,_⟩
    have hval:=Table.built_valid hb
    rcases hval with ⟨⟨_,_,⟨hx,_⟩,_⟩,_⟩
    exact hx.1
  refine ⟨qaj depth word hdepth,?_,?_⟩
  · unfold summary
    rw [fold_scale word Block.identity hdepth]
    dsimp -failIfUnchanged [Block.identity]
    ring
  · have hkne : qw word ≠ []:= by
      cases word with
      | nil => contradiction
      | cons _ _ => simp [qw]
    rcases fold_strong (qw word) Block.identity hgood Block.identity_bounded hkne with
      ⟨hb,hA,hC⟩
    refine ⟨hb,hA,hC,?_⟩
    unfold summary
    rw [fold_added]
    dsimp -failIfUnchanged [Block.identity]
    ring
lemma qbl (xs ys : List kernel) (S U : ℤ)
    (h : trace (xs ++ ys) S U) : trace xs S U:= by
  induction xs generalizing S U with
  | nil => exact trace.trace_nil S U
  | cons k xs ih =>
    cases h with
    | trace_cons hact htr =>
      exact trace.trace_cons hact (ih _ _ htr)
lemma trace_split (xs ys : List kernel) (S U : ℤ)
    (h : trace (xs ++ ys) S U) :
    ∃ S' U',Block.calls (qw xs) S (2 * S - U + 3) S' (2 * S' - U' + 3) ∧ trace ys S' U':= by
  induction xs generalizing S U with
  | nil =>
    exact ⟨S,U,Block.calls.no_calls S (2 * S - U + 3),h⟩
  | cons k xs ih =>
    cases h with
    | trace_cons hact htr =>
      rcases ih _ _ htr with ⟨S2,U2,hcalls,hrest⟩
      refine ⟨S2,U2,?_,hrest⟩
      exact Block.calls.more_calls (WordLink.action_block hact) hcalls
lemma summary_sound (word : List kernel) (S U S' U' : ℤ)
    (h : Block.calls (qw word) S (2 * S - U + 3) S' (2 * S' - U' + 3)) :
    Block.denotes (summary word) S (2 * S - U + 3) S' (2 * S' - U' + 3):= by
  apply Block.fold_sound h Block.identity S (2 * S - U + 3)
  dsimp -failIfUnchanged [Block.denotes,Block.identity]
  exact ⟨by ring,by ring⟩
lemma high_div (m : ℤ) (k : kernel) (word : List kernel) (S U : ℤ)
    (hm : 0 ≤ m) (hhigh : m < k.index) (htrace : trace (k :: word) S U) :
    q0 (m + 1) ∣ (2 * S - U + 3):= by
  cases htrace with
  | trace_cons hact _ =>
    rcases hact with ⟨_,_,t,ht⟩
    rw [ht,Table.pow_split (by omega : 0 ≤ m + 1) (by omega : m + 1 ≤ k.index)]
    exact ⟨q0 (k.index - (m + 1)) * (2 * t + 1),by ring⟩
lemma qbX (m r dL dm gL gm : ℤ) (k : kernel) (lows : List kernel) (S U : ℤ)
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hdm : 0 ≤ dm) (hgm : 0 ≤ gm)
    (hhigh : m < k.index) (hk : continuing k) (hdk : depth k ≤ dL) (hgk : gain k ≤ gL)
    (hlow : ∀ z ∈ lows,continuing z ∧ z.index ≤ m ∧ depth z ≤ dm ∧ gain z ≤ gm)
    (htrace : trace lows S U) (hbound : WordLink.bound m r) :
    HighPath.certified m (dL + r * dm) (gL + r * gm) (r * gm) (summary (k :: lows)):= by
  have hall : ∀ z ∈ (k :: lows),continuing z:= by
    intro z hz
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact hk
    · exact (hlow z hz').1
  have hlen : (lows.length : ℤ) ≤ r :=
    hbound lows S U (fun z hz => ⟨(hlow z hz).1,(hlow z hz).2.1⟩) htrace
  have hD : 0 ≤ qD depth lows ∧ qD depth lows ≤ r * dm:= by
    have h1 : ∀ z ∈ lows,0 ≤ depth z ∧ depth z ≤ dm:= by
      intro z hz
      rcases hlow z hz with ⟨⟨e,hb,_,_⟩,_,hd,_⟩
      rcases Table.built_valid hb with ⟨⟨_,_,⟨hx,_⟩,_⟩,_⟩
      exact ⟨hx.1,hd⟩
    have htb:=qbF depth lows dm h1
    exact ⟨htb.1,by nlinarith⟩
  have hG : 0 ≤ qD gain lows ∧ qD gain lows ≤ r * gm:= by
    have h1 : ∀ z ∈ lows,0 ≤ gain z ∧ gain z ≤ gm:= by
      intro z hz
      rcases hlow z hz with ⟨hz_cont,_,_,hg⟩
      have hgood:=WordLink.continuing_good z hz_cont
      dsimp -failIfUnchanged [Block.good,Bridge.kernel] at hgood
      have hgain_eq : gain z=z.pair.b + z.pair.c + 2:=rfl
      exact ⟨by omega,hg⟩
    have htb:=qbF gain lows gm h1
    exact ⟨htb.1,by nlinarith⟩
  rcases summary_data (k :: lows) hall (by simp) with ⟨hd0,hQ,hz,hA,hC,hM⟩
  have hMbound : m < (summary (k :: lows)).added ∧ (summary (k :: lows)).added ≤ gL + r * gm:= by
    rw [hM,qD,List.foldr_cons,← qD]
    have hcg:=WordLink.continuing_gain k hk
    exact ⟨by omega,by omega⟩
  have hDfull : qD depth (k :: lows) ≤ dL + r * dm:= by
    rw [qD,List.foldr_cons,← qD]
    omega
  rcases hz with ⟨hQpos,hA0,hAs,hMpos,hC0,hCs⟩
  have hcontract : 2 * (summary (k :: lows)).offset ≤
      (summary (k :: lows)).sc * (3 * (summary (k :: lows)).added + 2 * (r * gm) + 6):= by
    have hgood_lows : ∀ bk ∈ qw lows,Block.good bk:= by
      intro bk hbk
      rcases List.mem_map.mp hbk with ⟨z,hz_mem,rfl⟩
      exact WordLink.continuing_good z (hlow z hz_mem).1
    have hwc:=Block.word_contraction (Bridge.kernel k.pair) (qw lows)
      (WordLink.continuing_good k hk) hgood_lows
    try dsimp -failIfUnchanged only at hwc
    rw [qca] at hwc
    change 2 * (summary (k :: lows)).offset ≤
      (summary (k :: lows)).sc * (3 * (summary (k :: lows)).added +
        2 * (Block.identity.added + qD gain lows) + 6) at hwc
    dsimp -failIfUnchanged [Block.identity] at hwc
    nlinarith
  refine ⟨qD depth (k :: lows),⟨hd0,hDfull⟩,hQ,⟨hA,hAs⟩,⟨hC,?_⟩,hMbound,hcontract⟩
  nlinarith
end WordBlocks
namespace Multiscale
open WordLibrary WordBlocks
def qC (L d g : ℤ) : Prop :=
  ∀ k,continuing k → k.index ≤ L → depth k ≤ d ∧ gain k ≤ g
lemma low_split (m : ℤ) (word : List kernel) :
    ∃ lows tail,word=lows ++ tail ∧
      (∀ k ∈ lows,k.index ≤ m) ∧
      (tail=[] ∨ ∃ k rest,tail=k :: rest ∧ m < k.index):= by
  induction word with
  | nil =>
    exact ⟨[],[],rfl,by simp,Or.inl rfl⟩
  | cons k word ih =>
    by_cases hlow : k.index ≤ m
    · rcases ih with ⟨lows,tail,heq,hall,htail⟩
      refine ⟨k :: lows,tail,by simp [heq],?_,htail⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact hlow
      · exact hall x hx'
    · refine ⟨[],k :: word,rfl,by simp,Or.inr ⟨k,word,rfl,by omega⟩⟩
lemma qc9 (m L dm gm : ℤ) (lows : List kernel)
    (hparams : qC m dm gm)
    (hall : ∀ k ∈ lows,continuing k ∧ k.index ≤ L)
    (hlow : ∀ k ∈ lows,k.index ≤ m) :
    ∀ k ∈ lows,continuing k ∧ k.index ≤ m ∧ depth k ≤ dm ∧ gain k ≤ gm:= by
  intro k hk
  have h1:=hall k hk
  have h2:=hlow k hk
  have h3:=hparams k h1.1 h2
  exact ⟨h1.1,h2,h3.1,h3.2⟩
lemma qco (m L r : ℤ) (lows : List kernel) (S U : ℤ)
    (hb : WordLink.bound m r)
    (hall : ∀ k ∈ lows,continuing k ∧ k.index ≤ L)
    (hlow : ∀ k ∈ lows,k.index ≤ m)
    (htrace : trace lows S U) :
    (lows.length : ℤ) ≤ r:= by
  exact hb lows S U (fun k hk => ⟨(hall k hk).1,hlow k hk⟩) htrace
lemma qcg (m L r dL dm gL gm : ℤ)
    (hm : 0 ≤ m) (hr : 0 ≤ r) (hdm : 0 ≤ dm) (hgm : 0 ≤ gm)
    (hglobal : qC L dL gL) (hlow : qC m dm gm) (hbound : WordLink.bound m r) :
    ∀ (fuel : ℕ) (k : kernel) (rest : List kernel) (S U : ℤ),
      (k :: rest).length ≤ fuel → m < k.index →
      (∀ z ∈ (k :: rest),continuing z ∧ z.index ≤ L) →
      trace (k :: rest) S U →
      ∃ zs,HighPath.path m (dL + r * dm) (gL + r * gm) (r * gm) zs S (2 * S - U + 3) ∧
        ((k :: rest).length : ℤ) ≤ (r + 1) * ((zs.length : ℤ) + 1):= by
  intro fuel
  induction fuel with
  | zero =>
    intro k rest S U hfuel
    simp at hfuel
  | succ fuel ih =>
    intro k rest Sa Ua hfuel hhigh hall htrace
    rcases low_split m rest with ⟨lows,tail,hsplit,hindices,htail⟩
    subst hsplit
    have hk : continuing k ∧ k.index ≤ L:=hall k (by simp)
    have hlows : ∀ z ∈ lows,continuing z ∧ z.index ≤ L :=
      fun z hz => hall z (by simp [hz])
    have htailall : ∀ z ∈ tail,continuing z ∧ z.index ≤ L :=
      fun z hz => hall z (by simp [hz])
    cases htrace with
    | trace_cons hfirst hafter =>
      rename_i S1 U1
      have hlowtrace : trace lows S1 U1:=qbl lows tail S1 U1 hafter
      have hlen : (lows.length : ℤ) ≤ r :=
        qco m L r lows S1 U1 hbound hlows hindices hlowtrace
      have hdiv : q0 (m + 1) ∣ (2 * Sa - Ua + 3) :=
        high_div m k (lows ++ tail) Sa Ua hm hhigh (trace.trace_cons hfirst hafter)
      rcases htail with rfl | ⟨k',rest',rfl,hhigh'⟩
      · refine ⟨[],HighPath.path.path_stop Sa (2 * Sa - Ua + 3) hdiv,?_⟩
        simp only [List.append_nil,List.length_cons,List.length_nil]
        push_cast
        omega
      · have htr_full : trace ((k :: lows) ++ (k' :: rest')) Sa Ua:= by
          simpa using! trace.trace_cons hfirst hafter
        rcases trace_split (k :: lows) (k' :: rest') Sa Ua htr_full with
          ⟨Sb,Ub,hcalls,hresttrace⟩
        have hfuel' : (k' :: rest').length ≤ fuel:= by
          simp only [List.length_cons,List.length_append] at hfuel ⊢
          omega
        rcases ih k' rest' Sb Ub hfuel' hhigh' htailall hresttrace with
          ⟨zs,hpath,hcount⟩
        refine ⟨summary (k :: lows) :: zs,?_,?_⟩
        · rcases summary_sound (k :: lows) Sa Ua Sb Ub hcalls with ⟨hS,hH⟩
          subst hS
          rcases hglobal k hk.1 hk.2 with ⟨hd,hg⟩
          have hcert:=qbX m r dL dm gL gm k lows S1 U1
            hm hr hdm hgm hhigh hk.1 hd hg
            (qc9 m L dm gm lows hlow hlows hindices) hlowtrace hbound
          exact HighPath.path.path_step (summary (k :: lows)) zs Sa
            (2 * Sa - Ua + 3) (2 * (Sa + (summary (k :: lows)).added) - Ub + 3)
            hdiv hcert ⟨rfl,hH⟩ hpath
        · simp only [List.length_cons,List.length_append] at hcount ⊢
          push_cast at hcount ⊢
          linarith
theorem qcr (m L r dL dm gL gm : ℤ) (t q : ℕ)
    (hm : 0 < m) (hr : 0 ≤ r) (hdm : 0 ≤ dm) (hgm : 0 ≤ gm) (hgL : 0 ≤ gL)
    (hglobal : qC L dL gL) (hlow : qC m dm gm) (hbound : WordLink.bound m r)
    (hbudget : q0 (2 * (dL + r * dm)) * (12 * (gL + r * gm) + 8) < q0 (m + 1))
    (hpow : 2 * (gL + r * gm) + 2 ≤ (3 : ℤ) ^ t)
    (hq : r * gm + 4 ≤ (q : ℤ) * m) :
    WordLink.bound L ((r + 1) * ((t : ℤ) + (q : ℤ) + 2) + r):= by
  intro word S U hall htrace
  rcases low_split m word with ⟨lows,tail,rfl,hindices,htail⟩
  have hlows : ∀ z ∈ lows,continuing z ∧ z.index ≤ L :=
    fun z hz => hall z (by simp [hz])
  have htailall : ∀ z ∈ tail,continuing z ∧ z.index ≤ L :=
    fun z hz => hall z (by simp [hz])
  have hlowtrace : trace lows S U:=qbl lows tail S U htrace
  have hlen : (lows.length : ℤ) ≤ r :=
    qco m L r lows S U hbound hlows hindices hlowtrace
  rcases htail with rfl | ⟨k,rest,rfl,hhigh⟩
  · simp only [List.append_nil]
    have : 0 ≤ (r + 1) * ((t : ℤ) + (q : ℤ) + 2):= by positivity
    linarith
  · rcases WordLink.trace_suffix lows (k :: rest) S U htrace with ⟨S',U',hsuffix⟩
    rcases qcg m L r dL dm gL gm (by omega) hr hdm hgm hglobal hlow hbound
        (k :: rest).length k rest S' U' (le_refl _) hhigh htailall hsuffix with
      ⟨zs,hpath,hcount⟩
    have hhighcount : zs.length < t + q + 1 :=
      HighPath.path_count m (dL + r * dm) (gL + r * gm) (r * gm) zs S' (2 * S' - U' + 3)
        t q hm (by positivity) (by positivity) hpow hq hbudget hpath
    simp only [List.length_append]
    push_cast
    have hzs : (zs.length : ℤ) + 1 ≤ (t : ℤ) + (q : ℤ) + 1:= by omega
    have hmul : (r + 1) * ((zs.length : ℤ) + 1) ≤ (r + 1) * ((t : ℤ) + (q : ℤ) + 1) :=
      mul_le_mul_of_nonneg_left hzs (by omega)
    linarith
end Multiscale
namespace SmallScale
open WordLibrary WordBlocks Multiscale
lemma qbZ : qC 2048 5 5472:= by
  intro k hk hL
  exact WordCheck.kernel_bounds k hk hL
lemma earlier_parameters (k L : ℤ) (hL : 1 ≤ L ∧ L < k) (hprev : Closure.earlier k) :
    qC L (6 * q1 L + 9) (12 * L ^ 3 + 3):= by
  intro z hcont hindex
  rcases hcont with ⟨e,hb,hs,_⟩
  exact Closure.kernel_bounds k L hL hprev z.index z.pair e ⟨hs,hindex⟩ hb
lemma exp3 (x : ℤ) (hx : 0 ≤ x) : q0 (3 * x)=(q0 x) ^ 3:= by
  have h1 : 3 * x=x + (x + x):= by ring
  rw [h1,q5 hx (by omega),q5 hx hx]
  ring
lemma qao (L x : ℤ) (hL : 2048 < L) (hx : 12 ≤ x) (hpow : L ≤ q0 x) :
    12 * L ^ 3 + 3 + 6 * 5472 ≤ 13 * q0 (3 * x):= by
  have hL3 : L ^ 3 ≤ (q0 x) ^ 3:=pow_le_pow_left₀ (by omega) hpow 3
  have hsmall : 65536 ≤ q0 (3 * x):= by
    have h16 : (65536 : ℤ)=q0 16:= by decide
    rw [h16]
    exact qd (by omega) (by omega)
  rw [exp3 x (by omega)] at hsmall ⊢
  linarith
lemma budget120 (x M : ℤ) (hx : 12 ≤ x ∧ x ≤ 120) (hM : 0 ≤ M ∧ M ≤ 13 * q0 (3 * x)) :
    q0 (2 * (6 * x + 39)) * (12 * M + 8) < q0 2049:= by
  have hp : 0 < q0 (3 * x):=qc (by omega)
  have hB : 12 * M + 8 < q0 (3 * x + 8):= by
    rw [q5 (by omega) (by omega)]
    have h8 : q0 8=256:= by decide
    rw [h8]
    linarith
  have hbig : q0 (2 * (6 * x + 39)) * (12 * M + 8) < q0 (15 * x + 86):= by
    have heq : 15 * x + 86=2 * (6 * x + 39) + (3 * x + 8):= by ring
    rw [heq,q5 (by omega) (by omega)]
    exact mul_lt_mul_of_pos_left hB (qc (by omega))
  exact lt_trans hbig (qbm (by omega) (by omega))
lemma qa4 (x M : ℤ) (hx : 0 ≤ x) (hM : 0 ≤ M ∧ M ≤ 13 * q0 (3 * x)) :
    2 * M + 2 ≤ (3 : ℤ) ^ (2 * x + 4).toNat:= by
  let n : ℕ:=x.toNat
  have hxn : x=(n : ℤ):=(Int.toNat_of_nonneg hx).symm
  have h2x4 : (2 * x + 4).toNat=2 * n + 4:= by omega
  rw [h2x4]
  have hpow8 : q0 (3 * x)=(8 : ℤ) ^ n:= by
    rw [hxn,qe (by omega)]
    have h3n : (3 * (n : ℤ)).toNat=3 * n:= by omega
    rw [h3n,pow_mul]
    norm_num
  have hpow9 : (3 : ℤ) ^ (2 * n + 4)=81 * (9 : ℤ) ^ n:= by
    rw [pow_add,pow_mul]
    norm_num
    ring
  have h89 : (8 : ℤ) ^ n ≤ (9 : ℤ) ^ n:= by
    gcongr
    norm_num
  have h8pos : 1 ≤ (8 : ℤ) ^ n:=one_le_pow₀ (by norm_num)
  rw [hpow8] at hM
  rw [hpow9]
  linarith
theorem range120 (L : ℤ) (hL : 2 ≤ L ∧ L ≤ q0 120)
    (hparams : qC L (6 * q1 L + 9) (12 * L ^ 3 + 3)) :
    WordLink.bound L (30 * q1 L):= by
  by_cases hsmall : L ≤ 2048
  · apply WordLink.bound_mono 2048 L 6 (30 * q1 L) hsmall _ WordLink.base_bound
    have hlog : 1 ≤ q1 L:= by
      have h1 : q1 2 ≤ q1 L:=qt hL.1
      have h2 : q1 2=1:= by decide
      omega
    omega
  · push Not at hsmall
    set x:=q1 L
    have hx : 12 ≤ x ∧ x ≤ 120:= by
      constructor
      · have hp11 : (2048 : ℤ)=q0 11:= by decide
        by_contra hlt
        have hle:=(qm (by omega : 0 < L) (by omega : 0 ≤ (11 : ℤ))).mpr (by omega : x ≤ 11)
        omega
      · exact (qm (by omega) (by omega)).mp hL.2
    have hLpow : L ≤ q0 x:=(qy (by omega)).2
    have hL0 : 0 ≤ L:= by omega
    have hL3_nonneg : 0 ≤ L ^ 3:= by positivity
    have hM : 0 ≤ 12 * L ^ 3 + 3 + 6 * 5472 ∧ 12 * L ^ 3 + 3 + 6 * 5472 ≤ 13 * q0 (3 * x) :=
      ⟨by linarith,qao L x hsmall hx.1 hLpow⟩
    have hbudget : q0 (2 * (6 * x + 9 + 6 * 5)) * (12 * (12 * L ^ 3 + 3 + 6 * 5472) + 8) < q0 (2048 + 1):= by
      have heq : 6 * x + 9 + 6 * 5=6 * x + 39:= by ring
      rw [heq]
      exact budget120 x (12 * L ^ 3 + 3 + 6 * 5472) hx hM
    have htime : 2 * (12 * L ^ 3 + 3 + 6 * 5472) + 2 ≤ (3 : ℤ) ^ (2 * x + 4).toNat :=
      qa4 x (12 * L ^ 3 + 3 + 6 * 5472) (by omega) hM
    have hlift:=qcr 2048 L 6 (6 * x + 9) 5 (12 * L ^ 3 + 3) 5472
      (2 * x + 4).toNat 17 (by omega) (by omega) (by omega) (by omega) (by linarith)
      hparams qbZ WordLink.base_bound hbudget htime (by omega)
    apply WordLink.bound_mono L L ((6 + 1) * (((2 * x + 4).toNat : ℤ) + (17 : ℕ) + 2) + 6) (30 * x)
      (le_refl L) _ hlift
    have htoNat : ((2 * x + 4).toNat : ℤ)=2 * x + 4:=Int.toNat_of_nonneg (by omega)
    rw [htoNat]
    push_cast
    omega
end SmallScale
namespace Exponential
lemma power_ratio (a b : ℤ) (p : ℕ) (c : ℤ)
    (hab : 0 < b ∧ b ≤ a) (hc : 0 ≤ c) (hbase : (b + 1) ^ p ≤ c * b ^ p) :
    (a + 1) ^ p ≤ c * a ^ p:= by
  have hb0 : 0 ≤ b:= by omega
  have ha0 : 0 ≤ a:= by omega
  have h1 : b * (a + 1) ≤ (b + 1) * a:= by nlinarith
  have h2 : (b * (a + 1)) ^ p ≤ ((b + 1) * a) ^ p :=
    pow_le_pow_left₀ (by positivity) h1 p
  rw [mul_pow,mul_pow] at h2
  have ha_nonneg : 0 ≤ a ^ p:= by positivity
  have hb_pos : 0 < b ^ p:= by have : 0 < b:=hab.1; positivity
  have h3 : (b + 1) ^ p * a ^ p ≤ (c * b ^ p) * a ^ p :=
    mul_le_mul_of_nonneg_right hbase ha_nonneg
  nlinarith
lemma qO (K c : ℤ) (p : ℕ) (start slope : ℤ)
    (hK : 0 ≤ K) (hstart0 : 0 ≤ start) (hstart : 0 < start + c) (hslope : 0 ≤ slope)
    (hratio : (start + c + 1) ^ p ≤ q0 slope * (start + c) ^ p)
    (hbase : K * (start + c) ^ p < q0 (slope * start)) :
    ∀ n,start ≤ n → K * (n + c) ^ p < q0 (slope * n):= by
  have hall : ∀ i : ℕ,K * (start + (i : ℤ) + c) ^ p < q0 (slope * (start + (i : ℤ))):= by
    intro i
    induction i with
    | zero =>
      simpa using! hbase
    | succ i ih =>
      push_cast
      have heq1 : start + ((i : ℤ) + 1) + c=(start + (i : ℤ) + c) + 1:= by ring
      have heq2 : slope * (start + ((i : ℤ) + 1))=slope * (start + (i : ℤ)) + slope:= by ring
      rw [heq1,heq2,q5 (by nlinarith) hslope]
      have hstep : (start + (i : ℤ) + c + 1) ^ p ≤ q0 slope * (start + (i : ℤ) + c) ^ p :=
        power_ratio (start + (i : ℤ) + c) (start + c) p (q0 slope)
          ⟨hstart,by omega⟩ (qs slope) hratio
      have hscaled : K * (start + (i : ℤ) + c + 1) ^ p ≤ K * (q0 slope * (start + (i : ℤ) + c) ^ p) :=
        mul_le_mul_of_nonneg_left hstep hK
      have hpos : 0 < q0 slope:=qc hslope
      nlinarith
  intro n hn
  have hdecomp : n=start + ((n - start).toNat : ℤ):= by omega
  rw [hdecomp]
  exact hall (n - start).toNat
lemma square_tail (n : ℤ) (hn : 20 ≤ n) : 1024 * (n + 8) ^ 2 < q0 n:= by
  have h:=qO 1024 8 2 20 1 (by omega) (by omega) (by omega) (by omega)
    (by decide) (by decide) n hn
  simpa using! h
lemma fifth_tail (n : ℤ) (hn : 114 ≤ n) : q0 70 * (n + 8) ^ 5 < q0 n:= by
  have h:=qO (q0 70) 8 5 114 1 (qs 70) (by omega) (by omega) (by omega)
    (by decide) (by decide) n hn
  simpa using! h
lemma eighth_tail (n : ℤ) (hn : 114 ≤ n) : q0 84 * (n + 8) ^ 8 < q0 (2 * n):= by
  exact qO (q0 84) 8 8 114 2 (qs 84) (by omega) (by omega) (by omega)
    (by decide) (by decide) n hn
set_option exponentiation.threshold 2048 in
lemma final_tail (n : ℤ) (hn : 1024 ≤ n) : q0 70 * (n + 1) ^ 5 < q0 (n - 1):= by
  have h:=qO (q0 71) 1 5 1024 1 (qs 71) (by omega) (by omega) (by omega)
    (by decide) (by decide) n hn
  rw [one_mul,Table.pow_split (by omega : (0 : ℤ) ≤ 1) (by omega : 1 ≤ n)] at h
  have h1 : q0 1=2:= by decide
  have h71 : q0 71=2 * q0 70:= by decide
  rw [h1,h71] at h
  linarith
lemma final_square (n : ℤ) (hn : 17 ≤ n) : 200 * n ^ 2 < q0 (n - 1):= by
  have h:=qO 400 0 2 17 1 (by omega) (by omega) (by omega) (by omega)
    (by decide) (by decide) n hn
  rw [add_zero,one_mul,Table.pow_split (by omega : (0 : ℤ) ≤ 1) (by omega : 1 ≤ n)] at h
  have h1 : q0 1=2:= by decide
  rw [h1] at h
  linarith
end Exponential
namespace LargeStep
open WordLibrary WordBlocks Multiscale
lemma lin_lt_pow2 (n : ℤ) (hn : 0 ≤ n) : n < q0 n:= by
  have h:=qbP n.toNat
  rwa [Int.toNat_of_nonneg hn] at h
lemma qao (L m x r : ℤ)
    (hx : 3 ≤ x) (hm : 2 ≤ m ∧ m ≤ L) (hL : L ≤ q0 x) (hr : 0 ≤ r) :
    0 ≤ 12 * L ^ 3 + 3 + r * (12 * m ^ 3 + 3) ∧
    12 * L ^ 3 + 3 + r * (12 * m ^ 3 + 3) ≤ 13 * (r + 1) * q0 (3 * x):= by
  have hmL : m ^ 3 ≤ L ^ 3:=pow_le_pow_left₀ (by omega) hm.2 3
  have hLP : L ^ 3 ≤ (q0 x) ^ 3:=pow_le_pow_left₀ (by omega) hL 3
  have hm0 : 0 ≤ m:= by omega
  have hm3 : 0 ≤ m ^ 3:= by positivity
  have hP : 8 ≤ q0 (3 * x):= by
    have h8 : (8 : ℤ)=q0 3:= by decide
    rw [h8]
    exact qd (by omega) (by omega)
  rw [SmallScale.exp3 x (by omega)] at hP ⊢
  constructor
  · nlinarith
  · nlinarith
lemma budget (m x y r M : ℤ)
    (hx : 3 ≤ x) (hy : 0 ≤ y) (hr : 1 ≤ r)
    (hM : 0 ≤ M ∧ M ≤ 13 * (r + 1) * q0 (3 * x))
    (hbudget : 15 * x + 27 + 2 * r * (6 * y + 9) + r ≤ m + 1) :
    q0 (2 * (6 * x + 9 + r * (6 * y + 9))) * (12 * M + 8) < q0 (m + 1):= by
  have hrpow : r + 1 < q0 (r + 1):=lin_lt_pow2 (r + 1) (by omega)
  have hP : 0 < q0 (3 * x):=qc (by omega)
  have hE : q0 (3 * x + 8 + (r + 1))=256 * q0 (3 * x) * q0 (r + 1):= by
    rw [q5 (by omega) (by omega),q5 (by omega) (by omega)]
    have h8 : q0 8=256:= by decide
    rw [h8]
    ring
  have hMpow : 12 * M + 8 < q0 (3 * x + 8 + (r + 1)):= by
    rw [hE]
    nlinarith
  have hstep : q0 (2 * (6 * x + 9 + r * (6 * y + 9))) * (12 * M + 8) <
      q0 (15 * x + 27 + 2 * r * (6 * y + 9) + r):= by
    have heq : 15 * x + 27 + 2 * r * (6 * y + 9) + r =
        2 * (6 * x + 9 + r * (6 * y + 9)) + (3 * x + 8 + (r + 1)):= by ring
    rw [heq,q5 (by nlinarith) (by omega)]
    exact mul_lt_mul_of_pos_left hMpow (qc (by nlinarith))
  exact lt_of_lt_of_le hstep (qd (by nlinarith) hbudget)
lemma qa4 (x r M : ℤ)
    (hx : 3 ≤ x) (hr : 1 ≤ r) (hrpow : r + 1 ≤ q0 x)
    (hM : 0 ≤ M ∧ M ≤ 13 * (r + 1) * q0 (3 * x)) :
    2 * M + 2 ≤ (3 : ℤ) ^ (4 * x).toNat:= by
  have hE : q0 (4 * x)=q0 x * q0 (3 * x):= by
    have heq : 4 * x=x + 3 * x:= by ring
    rw [heq,q5 (by omega) (by omega)]
  have hMpow : 2 * M + 2 ≤ 28 * q0 (4 * x):= by
    rw [hE]
    have hpx : 0 < q0 x:=qc (by omega)
    have hp3x : 0 < q0 (3 * x):=qc (by omega)
    nlinarith
  let n : ℕ:=x.toNat
  have hxn : x=(n : ℤ):=(Int.toNat_of_nonneg (by omega)).symm
  have hn3 : 3 ≤ n:= by omega
  have h4x : (4 * x).toNat=4 * n:= by omega
  rw [h4x]
  have hpow16 : q0 (4 * x)=(16 : ℤ) ^ n:= by
    rw [hxn,qe (by omega)]
    have h4n : (4 * (n : ℤ)).toNat=4 * n:= by omega
    rw [h4n,pow_mul]
    norm_num
  have hpow81 : (3 : ℤ) ^ (4 * n)=(81 : ℤ) ^ n:= by
    rw [pow_mul]
    norm_num
  have h4_ge : (64 : ℤ) ≤ (4 : ℤ) ^ n:= by
    have h64 : (64 : ℤ)=(4 : ℤ) ^ 3:= by norm_num
    rw [h64]
    exact pow_le_pow_right₀ (by norm_num) hn3
  have h64_81 : (64 : ℤ) ^ n ≤ (81 : ℤ) ^ n:= by
    gcongr
    norm_num
  have hmul64 : (4 : ℤ) ^ n * (16 : ℤ) ^ n=(64 : ℤ) ^ n:= by
    rw [← mul_pow]
    norm_num
  have h16_pos : 0 < (16 : ℤ) ^ n:= by positivity
  rw [hpow16] at hMpow
  rw [hpow81]
  nlinarith
lemma qbQ (r x m : ℤ) (hr : 1 ≤ r) (hm : 2 ≤ m) (hx : x ≤ m ^ 2) :
    (r + 1) * (4 * x + 13 * r * m ^ 2 + 2) + r ≤ 64 * (r + 1) ^ 2 * m ^ 2:= by
  have h1 : (r + 1) * (4 * x + 13 * r * m ^ 2 + 2) ≤ (r + 1) * (4 * m ^ 2 + 13 * r * m ^ 2 + 2) :=
    mul_le_mul_of_nonneg_left (by linarith) (by omega)
  have hm2 : 1 ≤ m ^ 2:= by nlinarith
  nlinarith
theorem lift (m L x y r : ℤ)
    (hx : 3 ≤ x) (hy : 0 ≤ y) (hm : 2 ≤ m ∧ m ≤ L) (hr : 1 ≤ r)
    (hL : L ≤ q0 x) (hsquare : x ≤ m ^ 2)
    (hparams : qC L (6 * x + 9) (12 * L ^ 3 + 3))
    (hlow : qC m (6 * y + 9) (12 * m ^ 3 + 3))
    (hbound : WordLink.bound m r)
    (hbudget : 15 * x + 27 + 2 * r * (6 * y + 9) + r ≤ m + 1) :
    WordLink.bound L (64 * (r + 1) ^ 2 * m ^ 2):= by
  have hM:=qao L m x r hx hm hL (by omega)
  have hexp:=budget m x y r (12 * L ^ 3 + 3 + r * (12 * m ^ 3 + 3)) hx hy hr hM hbudget
  have hrpow : r + 1 ≤ q0 x:= by
    have hnonneg : 0 ≤ 2 * r * (6 * y + 9):= by positivity
    omega
  have htime:=qa4 x r (12 * L ^ 3 + 3 + r * (12 * m ^ 3 + 3)) hx hr hrpow hM
  have hq : r * (12 * m ^ 3 + 3) + 4 ≤ (13 * r * m ^ 2) * m:= by
    have hm2 : 2 * m ^ 2 ≤ m ^ 3:= by nlinarith [sq_nonneg m]
    nlinarith
  have hm0 : 0 ≤ m:= by omega
  have hL0 : 0 ≤ L:= by omega
  have hq0 : 0 ≤ 13 * r * m ^ 2:= by positivity
  have h4x_eq : ((4 * x).toNat : ℤ)=4 * x:=Int.toNat_of_nonneg (by omega)
  have hq_eq : ((13 * r * m ^ 2).toNat : ℤ)=13 * r * m ^ 2:=Int.toNat_of_nonneg hq0
  have hq' : r * (12 * m ^ 3 + 3) + 4 ≤ ((13 * r * m ^ 2).toNat : ℤ) * m:= by
    rw [hq_eq]; exact hq
  have hm3 : 0 ≤ m ^ 3:= by positivity
  have hL3 : 0 ≤ L ^ 3:= by positivity
  have hlift:=qcr m L r (6 * x + 9) (6 * y + 9) (12 * L ^ 3 + 3) (12 * m ^ 3 + 3)
    (4 * x).toNat (13 * r * m ^ 2).toNat (by omega) (by omega) (by omega)
    (by linarith) (by linarith) hparams hlow hbound hexp htime hq'
  apply WordLink.bound_mono L L
    ((r + 1) * (((4 * x).toNat : ℤ) + ((13 * r * m ^ 2).toNat : ℤ) + 2) + r)
    (64 * (r + 1) ^ 2 * m ^ 2) (le_refl L) _ hlift
  rw [h4x_eq,hq_eq]
  exact qbQ r x m hr hm.1 hsquare
end LargeStep
namespace ScaleNumbers
lemma threshold (x : ℤ) (hx : 121 ≤ x) : q0 20 + 32 * x < q0 (x - 1):= by
  have h:=Exponential.final_square x (by omega)
  have h20 : q0 20=1048576:= by decide
  nlinarith
lemma subscale (x : ℤ) (hx : 121 ≤ x) :
    (20 ≤ q1 (q0 20 + 32 * x) ∧ q1 (q0 20 + 32 * x) ≤ x) ∧
    q0 20 + 32 * x ≤ q0 14 * x ∧ x ≤ (q0 20 + 32 * x) ^ 2:= by
  have ht:=threshold x hx
  have h20 : q0 20=1048576:= by decide
  have h14 : q0 14=16384:= by decide
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · have h:=qt (by omega : q0 20 ≤ q0 20 + 32 * x)
    rw [qar (by omega)] at h
    exact h
  · apply (qm (by omega) (by omega)).mp
    have hmono:=qd (by omega : 0 ≤ x - 1) (by omega : x - 1 ≤ x)
    linarith
  · rw [h20,h14]; omega
  · nlinarith
lemma small_window (x : ℤ) (hx : 121 ≤ x ∧ x ≤ q0 20) :
    q1 (q0 20 + 32 * x) ≤ 26:= by
  have h20 : q0 20=1048576:= by decide
  have h26 : q0 26=67108864:= by decide
  apply (qm (by omega) (by omega)).mp
  omega
lemma large_window (x : ℤ) (hx : q0 20 < x) :
    20 ≤ qH x ∧
    (q0 (qH x) ≤ x ∧ x < q0 (qH x + 1)) ∧
    q1 (q0 20 + 32 * x) ≤ qH x + 7 ∧
    q0 20 + 32 * x ≤ 64 * x:= by
  have h20 : q0 20=1048576:= by decide
  have hpow:=qag (by omega : 0 < x)
  have hn : 20 ≤ qH x:= by
    have h:=qas (le_of_lt hx)
    rw [qck (by omega)] at h
    exact h
  refine ⟨hn,hpow,?_,by omega⟩
  apply (qm (by omega) (by omega)).mp
  rw [Table.pow_split (by omega : (0 : ℤ) ≤ 6) (by omega : 6 ≤ qH x + 7)]
  have h6 : q0 6=64:= by decide
  have heq : qH x + 7 - 6=qH x + 1:= by ring
  rw [h6,heq]
  omega
lemma huge_window (x : ℤ) (hm : q0 120 < q0 20 + 32 * x) :
    q0 114 < x ∧ 114 ≤ qH x:= by
  have hfixed : q0 20 + 32 * q0 114 < q0 120:= by decide
  have hx : q0 114 < x:= by linarith
  refine ⟨hx,?_⟩
  have h:=qas (le_of_lt hx)
  rw [qck (by omega)] at h
  exact h
lemma qak (y n : ℤ) (hy : 0 ≤ y ∧ y ≤ n + 7) (hn : 0 ≤ n) :
    27 + 2 * (30 * y) * (6 * y + 9) + 30 * y ≤ 1024 * (n + 8) ^ 2:= by
  nlinarith
lemma small_budget (x : ℤ) (hx : 121 ≤ x) :
    let y:=q1 (q0 20 + 32 * x)
    15 * x + 27 + 2 * (30 * y) * (6 * y + 9) + 30 * y ≤ q0 20 + 32 * x + 1:= by
  rcases subscale x hx with ⟨hy,_⟩
  try dsimp -failIfUnchanged only
  have h20 : q0 20=1048576:= by decide
  by_cases hsmall : x ≤ q0 20
  · have hsw:=small_window x ⟨hx,hsmall⟩
    have hpoly:=qak (q1 (q0 20 + 32 * x)) 19 ⟨by omega,by omega⟩ (by omega)
    omega
  · push Not at hsmall
    rcases large_window x hsmall with ⟨hn,⟨hpow1,hpow2⟩,hyn,hm⟩
    have hpoly:=qak (q1 (q0 20 + 32 * x)) (qH x) ⟨by omega,hyn⟩ (by omega)
    have htail:=Exponential.square_tail (qH x) hn
    linarith
lemma qbb (y : ℤ) (hy : 0 ≤ y) :
    27 + 2 * (q0 64 * (y + 1) ^ 4) * (6 * y + 9) + q0 64 * (y + 1) ^ 4 ≤
      q0 70 * (y + 1) ^ 5:= by
  have hP : 1 ≤ (y + 1) ^ 4:=one_le_pow₀ (by omega)
  have hy4y : 0 ≤ (y + 1) ^ 4 * y:= by positivity
  have h64_ge : (27 : ℤ) ≤ q0 64:= by decide
  have heq : q0 70 * (y + 1) ^ 5=64 * q0 64 * ((y + 1) ^ 4 * y) + 64 * q0 64 * (y + 1) ^ 4:= by
    have h70 : q0 70=64 * q0 64:= by decide
    rw [h70]
    ring
  have heq2 : 27 + 2 * (q0 64 * (y + 1) ^ 4) * (6 * y + 9) + q0 64 * (y + 1) ^ 4 =
      27 + 12 * q0 64 * ((y + 1) ^ 4 * y) + 19 * q0 64 * (y + 1) ^ 4:= by ring
  rw [heq,heq2]
  have hp64 : 0 < q0 64:=qc (by omega)
  nlinarith
lemma large_budget (x : ℤ) (hx : 121 ≤ x) (hm : q0 120 < q0 20 + 32 * x) :
    let y:=q1 (q0 20 + 32 * x)
    15 * x + 27 + 2 * (q0 64 * (y + 1) ^ 4) * (6 * y + 9) + q0 64 * (y + 1) ^ 4 ≤
      q0 20 + 32 * x + 1:= by
  try dsimp -failIfUnchanged only
  have hp20 : 0 ≤ q0 20:=qs 20
  rcases huge_window x hm with ⟨hxlarge,hn⟩
  have h20 : q0 20 < x:= by
    have hmono : q0 20 ≤ q0 114:=qd (by omega) (by omega)
    omega
  rcases large_window x h20 with ⟨_,⟨hpow1,hpow2⟩,hy,_⟩
  have hy0:=qh (q0 20 + 32 * x)
  have hpoly:=qbb (q1 (q0 20 + 32 * x)) hy0
  have hmono : (q1 (q0 20 + 32 * x) + 1) ^ 5 ≤ (qH x + 8) ^ 5 :=
    pow_le_pow_left₀ (by omega) (by omega) 5
  have htail:=Exponential.fifth_tail (qH x) hn
  have hpow70_mono : q0 70 * (q1 (q0 20 + 32 * x) + 1) ^ 5 ≤ q0 70 * (qH x + 8) ^ 5 :=
    mul_le_mul_of_nonneg_left hmono (qs 70)
  linarith
lemma qaE (a A b B : ℤ) (ha : 0 ≤ a ∧ a ≤ A) (hb : 0 ≤ b ∧ b ≤ B) :
    64 * a ^ 2 * b ^ 2 ≤ 64 * A ^ 2 * B ^ 2:= by
  have ha2 : a ^ 2 ≤ A ^ 2:=pow_le_pow_left₀ ha.1 ha.2 2
  have hb2 : b ^ 2 ≤ B ^ 2:=pow_le_pow_left₀ hb.1 hb.2 2
  have ha0 : 0 ≤ a ^ 2:=sq_nonneg a
  have hA0 : 0 ≤ A ^ 2:=sq_nonneg A
  have hmul : a ^ 2 * b ^ 2 ≤ A ^ 2 * B ^ 2:=mul_le_mul ha2 hb2 (sq_nonneg b) hA0
  linarith
lemma small_output (x y m : ℤ)
    (hx : 121 ≤ x) (hy : 0 ≤ y ∧ y ≤ x) (hm : 0 ≤ m ∧ m ≤ q0 14 * x) :
    64 * (30 * y + 1) ^ 2 * m ^ 2 ≤ q0 64 * (x + 1) ^ 4:= by
  have h:=qaE (30 * y + 1) (32 * x) m (q0 14 * x) ⟨by omega,by omega⟩ hm
  have h14 : q0 14=16384:= by decide
  have h44 : (64 : ℤ) * (32 * x) ^ 2 * (q0 14 * x) ^ 2=q0 44 * x ^ 4:= by
    rw [h14]
    have hp44 : q0 44=17592186044416:= by decide
    rw [hp44]
    ring
  rw [h44] at h
  have hx4 : x ^ 4 ≤ (x + 1) ^ 4:=pow_le_pow_left₀ (by omega) (by omega) 4
  have hx4_0 : 0 ≤ x ^ 4:= by positivity
  have h44_64 : q0 44 ≤ q0 64:=qd (by omega) (by omega)
  have hp64 : 0 ≤ q0 64:=qs 64
  nlinarith
lemma large_output (x y m n : ℤ)
    (hx : 1 ≤ x) (hy : 0 ≤ y ∧ y ≤ n + 7) (hn : 114 ≤ n)
    (hnx : q0 n ≤ x) (hm : 0 ≤ m ∧ m ≤ 64 * x) :
    64 * (q0 64 * (y + 1) ^ 4 + 1) ^ 2 * m ^ 2 ≤ q0 64 * (x + 1) ^ 4:= by
  have hP : 1 ≤ (y + 1) ^ 4:=one_le_pow₀ (by omega)
  have hp64_pos : 0 < q0 64:=qc (by omega)
  have h65_eq : q0 65=2 * q0 64:= by decide
  have h:=qaE (q0 64 * (y + 1) ^ 4 + 1) (q0 65 * (y + 1) ^ 4) m (64 * x)
    ⟨by positivity,by rw [h65_eq]; nlinarith⟩ hm
  have h148 : 64 * (q0 65 * (y + 1) ^ 4) ^ 2 * (64 * x) ^ 2=q0 148 * (y + 1) ^ 8 * x ^ 2:= by
    have hp65 : q0 65=36893488147419103232:= by decide
    have hp148 : q0 148=356811923176489970264571492362373784095686656:= by decide
    rw [hp65,hp148]
    ring
  rw [h148] at h
  have hy8 : (y + 1) ^ 8 ≤ (n + 8) ^ 8:=pow_le_pow_left₀ (by omega) (by omega) 8
  have htail:=Exponential.eighth_tail n hn
  have hn2 : q0 (2 * n) ≤ x ^ 2:= by
    have heq : 2 * n=n + n:= by ring
    rw [heq,q5 (by omega) (by omega)]
    have hpn:=qs n
    nlinarith
  have hp84 : 0 < q0 84:=qc (by omega)
  have h8 : q0 84 * (y + 1) ^ 8 ≤ x ^ 2:= by nlinarith
  have hstep : q0 148 * (y + 1) ^ 8 * x ^ 2 ≤ q0 64 * x ^ 4:= by
    have hp148_split : q0 148=q0 64 * q0 84:= by decide
    rw [hp148_split]
    have hx2_0 : 0 ≤ x ^ 2:=sq_nonneg x
    have h1 : q0 84 * (y + 1) ^ 8 * x ^ 2 ≤ x ^ 2 * x ^ 2 :=
      mul_le_mul_of_nonneg_right h8 hx2_0
    have h2 : q0 64 * (q0 84 * (y + 1) ^ 8 * x ^ 2) ≤ q0 64 * (x ^ 2 * x ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (qs 64)
    linarith [show q0 64 * (x ^ 2 * x ^ 2)=q0 64 * x ^ 4 by ring,
              show q0 64 * (q0 84 * (y + 1) ^ 8 * x ^ 2)=q0 64 * q0 84 * (y + 1) ^ 8 * x ^ 2 by ring]
  have hx4 : x ^ 4 ≤ (x + 1) ^ 4:=pow_le_pow_left₀ (by omega) (by omega) 4
  nlinarith
end ScaleNumbers
namespace GlobalBounds
lemma qcc (x : ℤ) (hx : 0 ≤ x) : 30 * x ≤ q0 64 * (x + 1) ^ 4:= by
  have hpow : x + 1 ≤ (x + 1) ^ 4:= by
    have h1 : 1 ≤ (x + 1) ^ 3:=one_le_pow₀ (by omega)
    have h2 : (x + 1) * 1 ≤ (x + 1) * (x + 1) ^ 3:=mul_le_mul_of_nonneg_left h1 (by omega)
    linarith [show (x + 1) * (x + 1) ^ 3=(x + 1) ^ 4 by ring]
  have h64 : (30 : ℤ) ≤ q0 64:= by decide
  nlinarith
lemma qae (k L : ℤ) (hprev : Closure.earlier k) (hL : 2 ≤ L ∧ L < k)
    (ih : ∀ m,2 ≤ m ∧ m < L → WordLink.bound m (q0 64 * (q1 m + 1) ^ 4)) :
    WordLink.bound L (q0 64 * (q1 L + 1) ^ 4):= by
  have hparams:=SmallScale.earlier_parameters k L ⟨by omega,hL.2⟩ hprev
  by_cases hsmall : L ≤ q0 120
  · exact WordLink.bound_mono L L (30 * q1 L) (q0 64 * (q1 L + 1) ^ 4)
      (le_refl L) (qcc (q1 L) (qh L))
      (SmallScale.range120 L ⟨hL.1,hsmall⟩ hparams)
  · push Not at hsmall
    have hpow:=qy (by omega : 1 < L)
    set x:=q1 L with hx_def
    have hx : 121 ≤ x:= by
      by_contra hle
      push Not at hle
      have:=(qm (by omega : 0 < L) (by omega : 0 ≤ (120 : ℤ))).mpr (by omega : x ≤ 120)
      omega
    have hth:=ScaleNumbers.threshold x hx
    have hsub:=ScaleNumbers.subscale x hx
    set m:=q0 20 + 32 * x with hm_def
    have h20_val : q0 20=1048576:= by decide
    have hm : 2 ≤ m ∧ m < L:=⟨by omega,by omega⟩
    have hmparams:=SmallScale.earlier_parameters k m ⟨by omega,by omega⟩ hprev
    set y:=q1 m with hy_def
    rcases hsub with ⟨hy,hm14,hxm⟩
    by_cases hmsmall : m ≤ q0 120
    · have hword:=SmallScale.range120 m ⟨hm.1,hmsmall⟩ hmparams
      rw [← hy_def] at hword
      have hsb:=ScaleNumbers.small_budget x hx
      try dsimp -failIfUnchanged only at hsb
      rw [← hm_def,← hy_def] at hsb
      have hlift:=LargeStep.lift m L x y (30 * y) (by omega) (by omega)
        ⟨hm.1,by omega⟩ (by omega) hpow.2 hxm hparams hmparams hword hsb
      exact WordLink.bound_mono L L (64 * (30 * y + 1) ^ 2 * m ^ 2) (q0 64 * (x + 1) ^ 4)
        (le_refl L) (ScaleNumbers.small_output x y m hx ⟨by omega,hy.2⟩ ⟨by omega,hm14⟩) hlift
    · push Not at hmsmall
      have hword:=ih m hm
      rw [← hy_def] at hword
      have hP : 1 ≤ (y + 1) ^ 4:=one_le_pow₀ (by omega)
      have hp64_pos : 0 < q0 64:=qc (by omega)
      have hr : 1 ≤ q0 64 * (y + 1) ^ 4:= by nlinarith
      have hlb:=ScaleNumbers.large_budget x hx (by rwa [← hm_def])
      try dsimp -failIfUnchanged only at hlb
      rw [← hm_def,← hy_def] at hlb
      have hlift:=LargeStep.lift m L x y (q0 64 * (y + 1) ^ 4) (by omega) (by omega)
        ⟨hm.1,by omega⟩ hr hpow.2 hxm hparams hmparams hword hlb
      rcases ScaleNumbers.huge_window x (by rwa [← hm_def]) with ⟨hx114,hn⟩
      have hx20 : q0 20 < x:= by
        have hmono : q0 20 ≤ q0 114:=qd (by omega) (by omega)
        omega
      have hlw:=ScaleNumbers.large_window x hx20
      rw [← hm_def,← hy_def] at hlw
      rcases hlw with ⟨_,hnx,hyn,hm64⟩
      exact WordLink.bound_mono L L (64 * (q0 64 * (y + 1) ^ 4 + 1) ^ 2 * m ^ 2)
        (q0 64 * (x + 1) ^ 4) (le_refl L)
        (ScaleNumbers.large_output x y m (qH x) (by omega) ⟨by omega,hyn⟩ hn hnx.1 ⟨by omega,hm64⟩)
        hlift
theorem quartic (k : ℤ) (hprev : Closure.earlier k) :
    ∀ L,2 ≤ L ∧ L < k → WordLink.bound L (q0 64 * (q1 L + 1) ^ 4):= by
  have hnat : ∀ n : ℕ,2 ≤ (n : ℤ) ∧ (n : ℤ) < k →
      WordLink.bound (n : ℤ) (q0 64 * (q1 (n : ℤ) + 1) ^ 4):= by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      apply qae k (n : ℤ) hprev hn
      intro m hm
      have hm_eq : m=(m.toNat : ℤ):=(Int.toNat_of_nonneg (by omega)).symm
      rw [hm_eq]
      exact ih m.toNat (by omega) ⟨by omega,by omega⟩
  intro L hL
  have hL_eq : L=(L.toNat : ℤ):=(Int.toNat_of_nonneg (by omega)).symm
  rw [hL_eq]
  exact hnat L.toNat ⟨by omega,by omega⟩
end GlobalBounds
namespace FinalBudget
lemma qa2 (k : ℤ) (hk : 65536 < k) :
    let x:=q1 k
    17 ≤ x ∧ (q0 (x - 1) < k ∧ k ≤ q0 x) ∧
    (2 ≤ 8 * x ∧ 8 * x < k) ∧ (0 ≤ q1 (8 * x) ∧ q1 (8 * x) ≤ x):= by
  try dsimp -failIfUnchanged only
  set x:=q1 k
  have hx : 17 ≤ x:= by
    have hp16 : (65536 : ℤ)=q0 16:= by decide
    by_contra hlt
    have hle:=(qm (by omega : 0 < k) (by omega : 0 ≤ (16 : ℤ))).mpr (by omega : x ≤ 16)
    omega
  have hpow:=qy (by omega : 1 < k)
  have hsquare:=Exponential.final_square x hx
  have hL : 2 ≤ 8 * x ∧ 8 * x < k:=⟨by omega,by nlinarith⟩
  refine ⟨hx,hpow,hL,qh (8 * x),?_⟩
  apply (qm (by omega) (by omega)).mp
  have hmono:=qd (by omega : 0 ≤ x - 1) (by omega : x - 1 ≤ x)
  nlinarith
lemma small_depth (x y : ℤ) (hx : 17 ≤ x) (hy : 0 ≤ y ∧ y ≤ x) :
    6 * x + 9 + (30 * y + 1) * (6 * y + 9) + 8 * x ≤ 200 * x ^ 2:= by
  nlinarith
lemma qbz (x : ℤ) (hx : 0 ≤ x) :
    6 * x + 9 + (q0 64 * (x + 1) ^ 4 + 1) * (6 * x + 9) + 8 * x ≤ q0 70 * (x + 1) ^ 5:= by
  have hP : 1 ≤ (x + 1) ^ 4:=one_le_pow₀ (by omega)
  have hx4x : 0 ≤ (x + 1) ^ 4 * x:=mul_nonneg (pow_nonneg (by omega) 4) (by omega)
  have h64_ge : (27 : ℤ) ≤ q0 64:= by decide
  have heq : q0 70 * (x + 1) ^ 5=64 * q0 64 * ((x + 1) ^ 4 * x) + 64 * q0 64 * (x + 1) ^ 4:= by
    have h70 : q0 70=64 * q0 64:= by decide
    rw [h70]
    ring
  have heq2 : 6 * x + 9 + (q0 64 * (x + 1) ^ 4 + 1) * (6 * x + 9) + 8 * x =
      18 + 20 * x + 6 * q0 64 * ((x + 1) ^ 4 * x) + 9 * q0 64 * (x + 1) ^ 4:= by ring
  rw [heq,heq2]
  have hp64 : 0 < q0 64:=qc (by omega)
  have hx_le : x ≤ (x + 1) ^ 4 * x:= by nlinarith
  nlinarith
lemma large_depth (x y : ℤ) (hy : 0 ≤ y ∧ y ≤ x) :
    6 * x + 9 + (q0 64 * (y + 1) ^ 4 + 1) * (6 * y + 9) + 8 * x ≤ q0 70 * (x + 1) ^ 5:= by
  have hP : (y + 1) ^ 4 ≤ (x + 1) ^ 4:=pow_le_pow_left₀ (by omega) (by omega) 4
  have hP0 : 0 ≤ (y + 1) ^ 4:=pow_nonneg (by omega) 4
  have hx0 : 0 ≤ (x + 1) ^ 4:=pow_nonneg (by omega) 4
  have hp64:=qs 64
  have hprod : (q0 64 * (y + 1) ^ 4 + 1) * (6 * y + 9) ≤ (q0 64 * (x + 1) ^ 4 + 1) * (6 * x + 9) :=
    mul_le_mul (by nlinarith) (by omega) (by omega) (by nlinarith)
  have hpoly:=qbz x (by omega)
  linarith
lemma mass_poly (k : ℤ) (hk : 3 ≤ k) :
    2 * (12 * k ^ 3 + k * (12 * k ^ 3 + 3)) + 3 < k ^ 8:= by
  have hsmall : 2 * (12 * k ^ 3 + k * (12 * k ^ 3 + 3)) + 3 ≤ 40 * k ^ 4:= by
    have hk0 : 0 ≤ k:= by omega
    have hk3_0 : 0 ≤ k ^ 3:=pow_nonneg (by omega) 3
    have hk1 : 1 ≤ k ^ 3:=one_le_pow₀ (by omega)
    have hkk3 : k ≤ k ^ 3:= by nlinarith [sq_nonneg k]
    have hk34 : 3 * k ^ 3 ≤ k ^ 4:= by
      have h1:=mul_le_mul_of_nonneg_right hk hk3_0
      linarith [show k * k ^ 3=k ^ 4 by ring]
    linarith [show 2 * (12 * k ^ 3 + k * (12 * k ^ 3 + 3)) + 3=24 * k ^ 3 + 24 * k ^ 4 + 6 * k + 3 by ring]
  have hpow : 81 ≤ k ^ 4:= by
    have h81 : (81 : ℤ)=3 ^ 4:= by norm_num
    rw [h81]
    exact pow_le_pow_left₀ (by omega) hk 4
  have hbig : 40 * k ^ 4 < k ^ 8:= by
    have heq : k ^ 8=k ^ 4 * k ^ 4:= by ring
    rw [heq]
    nlinarith
  linarith
lemma qao (k L n : ℤ) (hk : 3 ≤ k) (hL : 0 ≤ L ∧ L ≤ k) (hn : 0 ≤ n ∧ n ≤ k) :
    2 * (12 * k ^ 3 + n * (12 * L ^ 3 + 3)) + 3 < k ^ 8:= by
  have hLk3 : L ^ 3 ≤ k ^ 3:=pow_le_pow_left₀ hL.1 hL.2 3
  have hL3_0 : 0 ≤ L ^ 3:=pow_nonneg hL.1 3
  have hk3_0 : 0 ≤ k ^ 3:=pow_nonneg (by omega) 3
  have hmul : n * (12 * L ^ 3 + 3) ≤ k * (12 * k ^ 3 + 3) :=
    mul_le_mul hn.2 (by linarith) (by linarith) (by omega)
  have hmp:=mass_poly k hk
  linarith
lemma assemble (k x y r : ℤ)
    (hk : 65536 < k) (hx : x=q1 k) (hy : y=q1 (8 * x))
    (hr : 0 ≤ r) (hword : WordLink.bound (8 * x) r)
    (hD : 6 * x + 9 + (r + 1) * (6 * y + 9) + 8 * x < k) :
    Closure.budget k:= by
  rcases qa2 k hk with ⟨hx17,hpow,hL,hys⟩
  rw [← hx] at hx17 hpow hL hys
  rw [← hy] at hys
  have hn : r + 1 < k:= by nlinarith
  refine ⟨8 * x,(r + 1).toNat,⟨by omega,hL.2⟩,?_,?_,?_⟩
  · have htoNat : (((r + 1).toNat : ℤ) - 1)=r:= by omega
    rw [htoNat]
    exact hword
  · have htoNat : ((r + 1).toNat : ℤ)=r + 1:=Int.toNat_of_nonneg (by omega)
    rw [htoNat,← hx,← hy]
    exact hD
  · have htoNat : ((r + 1).toNat : ℤ)=r + 1:=Int.toNat_of_nonneg (by omega)
    rw [htoNat]
    have hmb:=qao k (8 * x) (r + 1) (by omega) ⟨by omega,by omega⟩ ⟨by omega,by omega⟩
    have hk8 : k ^ 8 ≤ q0 (8 * x):= by
      have heq : 8 * x=x + (x + (x + (x + (x + (x + (x + x)))))):= by ring
      have hx0 : 0 ≤ x:= by omega
      have hpow8 : q0 (8 * x)=(q0 x) ^ 8:= by
        rw [qe (by omega),qe hx0]
        have h8t : (8 * x).toNat=x.toNat * 8:= by omega
        rw [h8t,pow_mul]
      rw [hpow8]
      exact pow_le_pow_left₀ (by omega) hpow.2 8
    exact lt_of_lt_of_le hmb hk8
theorem budget (k : ℤ) (hk : 65536 < k) (hprev : Closure.earlier k) :
    Closure.budget k:= by
  rcases qa2 k hk with ⟨hx,hpow,hL,hy⟩
  set x:=q1 k
  set y:=q1 (8 * x)
  by_cases hsmall : 8 * x ≤ q0 120
  · apply assemble k x y (30 * y) hk rfl rfl (by omega)
    · exact SmallScale.range120 (8 * x) ⟨hL.1,hsmall⟩
        (SmallScale.earlier_parameters k (8 * x) ⟨by omega,hL.2⟩ hprev)
    · have hsd:=small_depth x y hx hy
      have hfs:=Exponential.final_square x hx
      linarith
  · push Not at hsmall
    have hy4 : 0 ≤ (y + 1) ^ 4:=pow_nonneg (by omega) 4
    have hp64:=qs 64
    apply assemble k x y (q0 64 * (y + 1) ^ 4) hk rfl rfl (mul_nonneg hp64 hy4)
    · exact GlobalBounds.quartic k hprev (8 * x) hL
    · have hx1024 : 1024 ≤ x:= by
        have hfixed : 8 * 1024 < q0 120:= by decide
        omega
      have hld:=large_depth x y hy
      have hft:=Exponential.final_tail x hx1024
      linarith
end FinalBudget
namespace TM1
abbrev M:=target_tm
@[simp] lemma multiStep_zero (config : Cfg (Fin 2) (Fin 6)) : multiStep M config 0=some config:=rfl
@[simp] lemma multiStep_one (config : Cfg (Fin 2) (Fin 6)) : multiStep M config 1=step M config:=rfl
@[simp] lemma multiStep_succ (config : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep M config (n + 1)=Option.bind (multiStep M config n) (step M):= by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] lemma zero_cons_default : (0 : Fin 2) >> (default : ListBlank (Fin 2))=default:= by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head=0:=rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail=default:=rfl
lemma qc3 {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [M]⊢ c₂) :
    c₁ [M]⊢^{1} c₂:= by simp [h]
lemma step_stepPlus {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [M]⊢ c₂) :
    c₁ [M]⊢⁺ c₂:=⟨1,by decide,qc3 h⟩
lemma qb1 (c₁ : Cfg (Fin 2) (Fin 6)) (n m : ℕ) :
    multiStep M c₁ (n + m)=(multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m):= by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,multiStep_succ,ih,Option.bind_assoc]
    simp_rw [multiStep_succ]
lemma qR {c₁ c₂ c3 : Cfg (Fin 2) (Fin 6)} {n m : ℕ}
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c3) :
    c₁ [M]⊢^{n+m} c3:= by
  rw [qb1,h₁]; simp [h₂]
lemma qF (c : Cfg (Fin 2) (Fin 6)) : c [M]⊢* c:=⟨0,rfl⟩
lemma qi {c₁ c₂ c3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c3) : c₁ [M]⊢* c3:= by
  rcases h₁ with ⟨n,hn⟩; rcases h₂ with ⟨m,hm⟩
  exact ⟨n + m,qR hn hm⟩
lemma qf {c₁ c₂ : Cfg (Fin 2) (Fin 6)} (h : c₁ [M]⊢⁺ c₂) :
    c₁ [M]⊢* c₂:= by rcases h with ⟨n,_,hn⟩; exact ⟨n,hn⟩
lemma q7 {c₁ c₂ c3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢* c3) : c₁ [M]⊢⁺ c3:= by
  rcases h₁ with ⟨n,hn0,hn⟩; rcases h₂ with ⟨m,hm⟩
  exact ⟨n + m,by omega,qR hn hm⟩
lemma qG {c₁ c₂ c3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢⁺ c3) : c₁ [M]⊢⁺ c3:= by
  rcases h₁ with ⟨n,hn⟩; rcases h₂ with ⟨m,hm0,hm⟩
  exact ⟨n + m,by omega,qR hn hm⟩
lemma qaz {c₁ c₂ c3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c₁ [M]⊢ c₂) (h₂ : c₂ [M]⊢* c3) : c₁ [M]⊢⁺ c3 :=
  q7 (step_stepPlus h₁) h₂
macro "qbq" : tactic =>
  `(tactic| exact qF _)
macro "step" : tactic =>
  `(tactic| (try refine qf ?_) <;>
    refine qaz (by (try simp only [Turing.ListBlank.head_cons,default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,zero_cons_default,default_head,default_tail])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | qbq | step)))
abbrev o1 : List (Fin 2):=[1]
@[simp] lemma o1_pow_zero (s : ListBlank (Fin 2)) : (o1 ^ (0 : ℕ)) +> s=s:=rfl
lemma q6 (n : ℕ) (s : ListBlank (Fin 2)) :
    (o1 ^ (n + 1)) +> s=(1 : Fin 2) >> ((o1 ^ n) +> s):=rfl
lemma qj (n : ℕ) (s : ListBlank (Fin 2)) :
    (o1 ^ n) +> ((1 : Fin 2) >> s)=(1 : Fin 2) >> ((o1 ^ n) +> s):= by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [q6,ih,← q6]
lemma o1_pow_add (m n : ℕ) (s : ListBlank (Fin 2)) :
    (o1 ^ (m + n)) +> s=(o1 ^ m) +> ((o1 ^ n) +> s):= by
  induction m with
  | zero => simp [o1_pow_zero]
  | succ m ih =>
    rw [Nat.succ_add,q6,q6,ih]
lemma qa1 (n : ℕ) (l r : ListBlank (Fin 2)) :
    (((o1 ^ n) +> l) <{{A}} r) [M]⊢* (l <{{A}} ((o1 ^ n) +> r)):= by
  induction n generalizing l r with
  | zero => exact qF _
  | succ n ih =>
    rw [q6]
    have h1 : (((1 : Fin 2) >> ((o1 ^ n) +> l)) <{{A}} r) [M]⊢⁺
        (((o1 ^ n) +> l) <{{A}} ((1 : Fin 2) >> r)):= by execute
    exact qi (qf h1) (by rw [q6,← qj]; exact ih l ((1 : Fin 2) >> r))
lemma qaX (n : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ((o1 ^ n) +> r)) [M]⊢* (((o1 ^ n) +> l) {{D}}> r):= by
  induction n generalizing l r with
  | zero => exact qF _
  | succ n ih =>
    rw [q6]
    have h1 : (l {{D}}> ((1 : Fin 2) >> ((o1 ^ n) +> r))) [M]⊢⁺
        (((1 : Fin 2) >> l) {{D}}> ((o1 ^ n) +> r)):= by execute
    exact qi (qf h1) (by rw [q6,← qj]; exact ih ((1 : Fin 2) >> l) r)
def S1 (a b c : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
    ((o1 ^ b) +> ((0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r)))
def S2 (a b c : ℕ) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
    ((o1 ^ b) +> ((1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r)))
lemma Inc1 (a b c : ℕ) (r : ListBlank (Fin 2)) :
    (S1 a (2 + b) c r) [M]⊢* (S1 (1 + a) b (1 + c) r):= by
  unfold S1
  rw [show 2 + b=b + 1 + 1 by omega,q6 (b + 1),q6 b]
  have h1 : (((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
      ((1 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ b) +> ((0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))))) [M]⊢⁺
      (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default)) {{D}}>
      ((o1 ^ b) +> ((0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r)))):= by execute
  have h2:=qaX b ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))
    ((0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))
  rw [qj] at h2
  have h3 : (((1 : Fin 2) >> ((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default)))) {{D}}>
      ((0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))) [M]⊢⁺
      (((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))) <{{A}}
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))):= by execute
  have h4:=qa1 b ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))
    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))
  rw [show 1 + a=a + 1 by omega,show 1 + c=c + 1 by omega,q6 a,q6 c]
  exact qi (qf h1) (qi h2 (qi (qf h3) h4))
lemma Incs1 (n a b c : ℕ) (r : ListBlank (Fin 2)) :
    (S1 a (n * 2 + b) c r) [M]⊢* (S1 (n + a) b (n + c) r):= by
  induction n generalizing a b c with
  | zero => simp [qF]
  | succ n ih =>
    rw [show (n + 1) * 2 + b=n * 2 + (2 + b) by omega]
    have h1:=ih a (2 + b) c
    have h2:=Inc1 (n + a) b (n + c) r
    rw [show 1 + (n + a)=n + 1 + a by omega,show 1 + (n + c)=n + 1 + c by omega] at h2
    exact qi h1 h2
lemma Inc2 (a b c : ℕ) (r : ListBlank (Fin 2)) :
    (S2 a b (1 + c) r) [M]⊢* (S2 (1 + a) b c r):= by
  unfold S2
  rw [show 1 + c=c + 1 by omega,q6 c,qj b]
  have h1 : (((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
      ((1 : Fin 2) >> ((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))))) [M]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default)) {{D}}>
      ((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r)))):= by execute
  have h2:=qaX b ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))
    ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))
  have h3 : ((((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))) {{D}}>
      ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r)))) [M]⊢⁺
      (((o1 ^ b) +> ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))) <{{A}}
      ((1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))):= by execute
  have h4:=qa1 b ((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default))
    ((1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))
  rw [show 1 + a=a + 1 by omega,q6 a]
  exact qi (qf h1) (qi h2 (qi (qf h3) h4))
lemma Incs2 (a b c : ℕ) (r : ListBlank (Fin 2)) :
    (S2 a b c r) [M]⊢* (S2 (c + a) b 0 r):= by
  induction c generalizing a b with
  | zero => simp [qF]
  | succ c ih =>
    rw [show c + 1=1 + c by omega]
    have h1:=Inc2 a b c r
    have h2:=ih (1 + a) b
    rw [show c + (1 + a)=(1 + c) + a by omega] at h2
    exact qi h1 h2
lemma Ov0_start (a c d : ℕ) (r' : ListBlank (Fin 2)) :
    (S1 a 0 c ((0 : Fin 2) >> ((o1 ^ d) +> r'))) [M]⊢⁺ (S2 0 (2 + a + c) d r'):= by
  unfold S1 S2
  simp only [o1_pow_zero,zero_add]
  cases c with
  | zero =>
    simp only [o1_pow_zero,Nat.add_zero]
    have h1 : (((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r'))) [M]⊢⁺
        (((o1 ^ a) +> default) <{{A}}
        ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r'))):= by execute
    have h2:=qa1 a default
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r'))
    have h_eq : ((default : ListBlank (Fin 2)) <{{A}}
        ((o1 ^ a) +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r')))) =
        (((0 : Fin 2) >> default) <{{A}}
        ((o1 ^ (2 + a)) +> ((1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r')))):= by
      rw [zero_cons_default,show 2 + a=a + 1 + 1 by omega,
          q6 (a + 1),q6 a,← qj a,← qj a]
    rw [h_eq] at h2
    exact q7 h1 h2
  | succ c =>
    rw [q6 c]
    have h1 : (((0 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
        ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> ((0 : Fin 2) >> ((o1 ^ d) +> r'))))) [M]⊢⁺
        (((o1 ^ a) +> default) <{{A}}
        ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> ((0 : Fin 2) >> ((o1 ^ d) +> r'))))):= by execute
    have h2:=qa1 a default
      ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> ((0 : Fin 2) >> ((o1 ^ d) +> r'))))
    have h_eq : ((default : ListBlank (Fin 2)) <{{A}}
        ((o1 ^ a) +> ((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> ((0 : Fin 2) >> ((o1 ^ d) +> r')))))) =
        (((0 : Fin 2) >> default) <{{A}}
        ((o1 ^ (2 + a + (c + 1))) +> ((1 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ d) +> r')))):= by
      rw [zero_cons_default,show 2 + a + (c + 1)=a + (1 + 1 + 1 + c) by omega,
          o1_pow_add a (1 + 1 + 1 + c)]
      congr 2
      rw [show 1 + 1 + 1 + c=c + 1 + 1 + 1 by omega,
          q6 (c + 1 + 1),q6 (c + 1),q6 c,qj c]
    rw [h_eq] at h2
    exact q7 h1 h2
lemma Ov0 (a c d e : ℕ) (r : ListBlank (Fin 2)) :
    (S1 a 0 c ((0 : Fin 2) >> ((o1 ^ d) +> ((0 : Fin 2) >> ((o1 ^ e) +> r))))) [M]⊢⁺
    (S1 d (3 + a + c) e r):= by
  have h1:=Ov0_start a c d ((0 : Fin 2) >> ((o1 ^ e) +> r))
  have h2:=Incs2 0 (2 + a + c) d ((0 : Fin 2) >> ((o1 ^ e) +> r))
  rw [Nat.add_zero] at h2
  have h_eq : S2 d (2 + a + c) 0 ((0 : Fin 2) >> ((o1 ^ e) +> r))=S1 d (3 + a + c) e r:= by
    unfold S2 S1
    simp only [o1_pow_zero]
    rw [show 3 + a + c=(2 + a + c) + 1 by omega,q6 (2 + a + c),qj (2 + a + c)]
  rw [h_eq] at h2
  exact q7 h1 h2
lemma Ov1 (a c : ℕ) (r : ListBlank (Fin 2)) :
    (S1 (1 + a) 1 c r) [M]⊢⁺ (S1 0 a 1 ((0 : Fin 2) >> ((o1 ^ (1 + c)) +> r))):= by
  unfold S1
  rw [show 1 + a=a + 1 by omega,show 1 + c=c + 1 by omega,
      q6 a,q6 0,o1_pow_zero,q6 c]
  have h1 : (((0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ a) +> default)) <{{A}}
      ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((o1 ^ c) +> r))) [M]⊢⁺
      (((o1 ^ a) +> default) <{{A}}
      ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))):= by execute
  have h2:=qa1 a default
    ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r))
  have h_eq : ((default : ListBlank (Fin 2)) <{{A}}
      ((o1 ^ a) +> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r)))) =
      (((0 : Fin 2) >> default) <{{A}}
      ((o1 ^ a) +> ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((o1 ^ c) +> r)))):= by
    rw [zero_cons_default]
  rw [h_eq] at h2
  exact q7 h1 h2
lemma MacroE (n v w d e : ℕ) (r : ListBlank (Fin 2)) :
    (S1 v (2 * n) w ((0 : Fin 2) >> ((o1 ^ d) +> ((0 : Fin 2) >> ((o1 ^ e) +> r))))) [M]⊢⁺
    (S1 d (2 * n + v + w + 3) e r):= by
  have h1:=Incs1 n v 0 w ((0 : Fin 2) >> ((o1 ^ d) +> ((0 : Fin 2) >> ((o1 ^ e) +> r))))
  rw [show n * 2 + 0=2 * n by omega] at h1
  have h2:=Ov0 (n + v) (n + w) d e r
  rw [show 3 + (n + v) + (n + w)=2 * n + v + w + 3 by omega] at h2
  exact qG h1 h2
lemma MacroO (n v w : ℕ) (r : ListBlank (Fin 2)) (h : 1 ≤ n + v) :
    (S1 v (2 * n + 1) w r) [M]⊢⁺
    (S1 0 (n + v - 1) 1 ((0 : Fin 2) >> ((o1 ^ (w + n + 1)) +> r))):= by
  have h1:=Incs1 n v 1 w r
  rw [show n * 2 + 1=2 * n + 1 by omega] at h1
  have h2:=Ov1 (n + v - 1) (n + w) r
  rw [show 1 + (n + v - 1)=n + v by omega,show 1 + (n + w)=w + n + 1 by omega] at h2
  exact qG h1 h2
def qr : List ℕ → ListBlank (Fin 2)
  | [] => default
  | n :: xs => (0 : Fin 2) >> ((o1 ^ n) +> qr xs)
def qT : List ℕ → Cfg (Fin 2) (Fin 6)
  | [] => S1 0 0 0 default
  | [u] => S1 0 u 0 default
  | [u,v] => S1 v u 0 default
  | u :: v :: w :: r => S1 v u w (qr r)
lemma step_spec {e : ℕ} {xs ys : List ℕ} (h : Prefix.Step e xs ys) :
    (qT xs) [M]⊢⁺ (qT ys):= by
  cases h with
  | E n v w r =>
    rcases r with _ | ⟨d,_ | ⟨e',r⟩⟩
    · dsimp -failIfUnchanged [qT,qr]
      have hM:=MacroE n v w 0 0 default
      simpa [o1_pow_zero,zero_cons_default] using! hM
    · dsimp -failIfUnchanged [qT,qr]
      have hM:=MacroE n v w d 0 default
      simpa [o1_pow_zero,zero_cons_default] using! hM
    · dsimp -failIfUnchanged [qT,qr]
      exact MacroE n v w d e' (qr r)
  | O n v w r hnv =>
    dsimp -failIfUnchanged [qT,qr]
    exact MacroO n v w (qr r) hnv
lemma qbG (xs : List ℕ) : qr (xs ++ [0])=qr xs:= by
  induction xs with
  | nil => simp [qr,o1_pow_zero,zero_cons_default]
  | cons x xs ih => simp [qr,ih]
lemma qaW (xs : List ℕ) : qT (xs ++ [0])=qT xs:= by
  rcases xs with _ | ⟨u,_ | ⟨v,_ | ⟨w,xs⟩⟩⟩
  · simp [qT,S1,o1_pow_zero,zero_cons_default]
  · simp [qT,S1,o1_pow_zero,zero_cons_default]
  · simp [qT,S1,qr,o1_pow_zero,zero_cons_default]
  · simp [qT,qbG]
lemma init_eq : init []=qT []:= by
  unfold init qT S1
  simp [Tape.mk₁,o1_pow_zero,zero_cons_default,A]
  rfl
lemma exec_spec {e : ℕ} {xs ys : List ℕ} (h : Prefix.Exec e xs ys) :
    (qT xs) [M]⊢* (qT ys):= by
  induction h with
  | stop xs => exact qF _
  | take hs _ ih => exact qi (qf (step_spec hs)) ih
  | zero _ ih => rw [← qaW]; exact ih
lemma exec_progress {e : ℕ} {xs ys : List ℕ} (h : Prefix.Exec e xs ys) (he : 0 < e) :
    (qT xs) [M]⊢⁺ (qT ys):= by
  induction h with
  | stop xs => omega
  | take hs hex ih =>
    exact q7 (step_spec hs) (exec_spec hex)
  | zero _ ih =>
    rw [← qaW]
    exact ih he
lemma qau {c c' : Cfg (Fin 2) (Fin 6)} {j d : ℕ}
    (h : multiStep M c (j + d)=some c') :
    (multiStep M c j).isSome:= by
  rw [qb1] at h
  cases h_j : multiStep M c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl
lemma nonhalt_of_returns (hreturn : ∀ k : ℕ,∃ e m : ℕ,Prefix.Exec (1 + e) [3 * k] [m]) :
    IsDoesNotHalt M:= by
  have h_chain : ∀ m : ℕ,∃ N ≥ m,∃ k : ℕ,multiStep M (init []) N=some (qT [3 * k]):= by
    intro m
    induction m with
    | zero =>
      refine ⟨0,Nat.le_refl 0,0,?_⟩
      rw [init_eq,← qaW []]
      rfl
    | succ m ih =>
      rcases ih with ⟨N,hN,k,h_ms⟩
      rcases hreturn k with ⟨e,m_out,hex⟩
      have hmass:=Prefix.exec_mass hex
      simp [Prefix.mass] at hmass
      have hm_eq : m_out=3 * (k + 1 + e):= by omega
      rw [hm_eq] at hex
      rcases exec_progress hex (by omega) with ⟨qad,hsteps_pos,hsteps⟩
      exact ⟨N + qad,by omega,k + 1 + e,qR h_ms hsteps⟩
  intro cfg h_reach
  rcases h_reach with ⟨n,hn⟩
  rcases h_chain (n + 1) with ⟨N,hN,k,h_N⟩
  have h_eq : (n + 1) + (N - (n + 1))=N:=Nat.add_sub_of_le hN
  rw [← h_eq] at h_N
  have h_some:=qau h_N
  rw [multiStep_succ,hn] at h_some
  exact h_some
end TM1

end Solution
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.dupNamespace false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option quotPrecheck false
set_option maxRecDepth 4000000
set_option maxHeartbeats 8000000

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm := TM1.nonhalt_of_returns (Prefix.single_returns (Closure.G_returns FinalBudget.budget))

end BusyBeaver.M_1RB1LA_0RC0RD_1LC1LA_1RE1RD_1LF0LA_HHH0LE
