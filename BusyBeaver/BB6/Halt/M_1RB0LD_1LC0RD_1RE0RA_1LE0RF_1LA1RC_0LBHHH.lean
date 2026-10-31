/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LB---` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LB---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LBHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LB---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
@[reducible] def holdout_0491_tm : Machine (Fin 2) (Fin 6) := target_tm
abbrev qc : Machine (Fin 2) (Fin 6)
  | 0,0 => some (some 1,Stmt.write 1 Dir.left)
  | 0,1 => some (some 3,Stmt.write 0 Dir.right)
  | 1,0 => some (some 2,Stmt.write 1 Dir.right)
  | 1,1 => some (some 3,Stmt.write 0 Dir.left)
  | 2,0 => some (some 4,Stmt.write 1 Dir.left)
  | 2,1 => some (some 0,Stmt.write 0 Dir.left)
  | 3,0 => some (some 4,Stmt.write 1 Dir.right)
  | 3,1 => some (some 5,Stmt.write 0 Dir.left)
  | 4,0 => some (some 0,Stmt.write 1 Dir.right)
  | 4,1 => some (some 2,Stmt.write 1 Dir.left)
  | 5,0 => some (some 1,Stmt.write 0 Dir.right)
  | 5,1 => none
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000
@[simp] lemma multiStep_zero (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0=some config:=rfl
@[simp] lemma multiStep_one (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1=step M config:=rfl
@[simp] lemma multiStep_succ (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1)=Option.bind (multiStep M config n) (step M):= by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default=default:= by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head=0:=rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail=default:=rfl
@[simp] lemma append_nil (s : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> s=s:=rfl
@[simp] lemma append_cons (a : Fin 2) (l : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (a :: l) +> s=a >> (l +> s):=rfl
@[simp] lemma append_assoc (l1 l2 : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (l1 ++ l2) +> s=l1 +> (l2 +> s):= by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp [ih]
@[simp] lemma pow_zero_list {α : Type*} (l : List α) : l ^ (0 : ℕ)=[]:=rfl
@[simp] lemma pow_succ_list {α : Type*} (l : List α) (n : ℕ) : l ^ (n + 1)=l ++ l ^ n:=rfl
lemma qb {α : Type*} (l : List α) (m n : ℕ) : l ^ (m + n)=l ^ m ++ l ^ n:= by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [pow_succ_list,Nat.succ_add,ih,List.append_assoc]
lemma pow_shift {α : Type*} (l : List α) (n : ℕ) : l ^ n ++ l=l ^ (n + 1):= by
  induction n with
  | zero => simp [pow_succ_list]
  | succ n ih => simp [pow_succ_list,List.append_assoc,ih]
@[simp] lemma nil_pow_list {α : Type*} (n : ℕ) : ([] : List α) ^ n=[]:= by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
lemma commute_power {x v w : List (Fin 2)} {a b : ℕ}
    (h : x ++ v ^ a=w ^ b ++ x) (k : ℕ) :
    x ++ v ^ (k * a)=w ^ (k * b) ++ x:=
  BusyBeaver.Excursion.commute_pow_left h k
lemma qD {w : List (Fin 2)} (h : BusyBeaver.Longitudinal.BoundedConfig.all0 w=true) :
    w +> default=default:=
  BusyBeaver.Longitudinal.BoundedConfig.all0_spec h
lemma qM {w : List (Fin 2)} (h : BusyBeaver.Longitudinal.BoundedConfig.all0 w=true) (n : ℕ) :
    (w ^ n) +> default=default:= by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list,append_assoc,ih,qD h]
lemma qA {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂:= by simp [h]
lemma qm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢* c₂:=⟨1,qA tm c₁ c₂ h⟩
lemma multiStep_add {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m)=(multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m):= by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,multiStep_succ,ih,Option.bind_assoc]
    simp_rw [multiStep_succ]
lemma qu {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c3) :
    c₁ [tm]⊢^{n+m} c3:= by
  rw [multiStep_add,h₁]; simp [h₂]
lemma q0 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢* c3:= by
  obtain ⟨n,hn⟩:=h₁; obtain ⟨m,hm⟩:=h₂
  exact ⟨n + m,qu tm c₁ c₂ c3 n m hn hm⟩
lemma qE {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂:= by obtain ⟨n,_,hn⟩:=h; exact ⟨n,hn⟩
lemma qn {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3:= by
  obtain ⟨n,n_pos,hn⟩:=h₁; obtain ⟨m,hm⟩:=h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),qu tm c₁ c₂ c3 n m hn hm⟩
lemma qt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  qn (step_stepPlus tm c₁ c₂ h₁) h₂
local macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
local macro "step_tm" : tactic =>
  `(tactic| (try refine qE ?_) <;>
    refine qt (by (try simp only [Turing.ListBlank.head_cons,default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,zero_cons_default,default_head,default_tail])
local macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)))
local macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
local macro "execute90" : tactic =>
  `(tactic| execute <;> execute)
def q4 {α : Type*} (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn n (f Nat.zero) (fun m => f (Nat.succ m))
@[simp] lemma strictNat_eq {α : Type*} (n : ℕ) (f : ℕ → α) : q4 n f=f n:= by
  cases n <;> rfl
def W : List (Fin 2):=[1,1,1,1,0,1,1,1,1,1]
inductive Digit where
  | D0 | D1 | D2 | D3 | D4 | D5
deriving DecidableEq
def qS {α : Type*} (d : Digit) (f : Digit → α) : α :=
  match d with
  | .D0 => f .D0
  | .D1 => f .D1
  | .D2 => f .D2
  | .D3 => f .D3
  | .D4 => f .D4
  | .D5 => f .D5
@[simp] lemma strictDigit_eq {α : Type*} (d : Digit) (f : Digit → α) : qS d f=f d:= by
  cases d <;> rfl
def Digit.index : Digit → ℕ
  | .D0 => 0 | .D1 => 1 | .D2 => 2 | .D3 => 3 | .D4 => 4 | .D5 => 5
def qo : Digit → List (Fin 2)
  | .D0 => [0,1]
  | .D1 => [1,1,1,1]
  | .D2 => [0,1,1,1,1,1]
  | .D3 => [1,1,1,1,1,1,1,1]
  | .D4 => [0,1,1,1,1,1,1,1,1,1]
  | .D5 => [1,1,1,1,1,1,1,1,1,1,1,1]
def next : Digit → Digit
  | .D0 => .D1 | .D1 => .D2 | .D2 => .D3 | .D3 => .D4 | .D4 => .D5 | .D5 => .D0
def take : Digit → ℕ
  | .D1 | .D3 => 1
  | _ => 0
def give : Digit → ℕ
  | .D1 | .D3 | .D5 => 1
  | _ => 0
def qO : Digit → ℕ
  | .D5 => 1
  | _ => 0
def qd (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2) → Prop
  | 0,r,r' => r=r'
  | t + 1,r,r' =>
    ∃ r1,(∀ l,(([1,0,1] +> l) {{q}}> r) [tm]⊢* (l <{{q}} ([1] +> r1))) ∧
          qd tm q t r1 r'
lemma sideCalls_add {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t u : ℕ} {r1 r2 r3 : ListBlank (Fin 2)}
    (h₁ : qd tm q t r1 r2) (h₂ : qd tm q u r2 r3) :
    qd tm q (t + u) r1 r3:= by
  induction t generalizing r1 with
  | zero =>
    rw [Nat.zero_add]
    change r1=r2 at h₁
    subst h₁
    exact h₂
  | succ t ih =>
    rcases h₁ with ⟨rm,hstep,hrest⟩
    rw [Nat.succ_add]
    exact ⟨rm,hstep,ih hrest⟩
lemma qT {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t u : ℕ} {r1 r3 : ListBlank (Fin 2)}
    (h : qd tm q (t + u) r1 r3) :
    ∃ r2,qd tm q t r1 r2 ∧ qd tm q u r2 r3:= by
  induction t generalizing r1 with
  | zero =>
    rw [Nat.zero_add] at h
    exact ⟨r1,rfl,h⟩
  | succ t ih =>
    rw [Nat.succ_add] at h
    rcases h with ⟨rm,hstep,hrest⟩
    rcases ih hrest with ⟨r2,h₁,h₂⟩
    exact ⟨r2,⟨rm,hstep,h₁⟩,h₂⟩
def q2 (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (t u : ℕ) (w1 w2 : List (Fin 2)) : Prop :=
  ∀ r1 r2,qd tm q u r1 r2 → qd tm q t (w1 +> r1) (w2 +> r2)
lemma qh (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (w : List (Fin 2)) :
    q2 tm q 0 0 w w:= by
  intro r1 r2 h
  change r1=r2 at h
  subst h
  rfl
lemma segCalls_nil (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (t : ℕ) :
    q2 tm q t t [] []:= by
  intro r1 r2 h
  exact h
lemma q5 {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t u v : ℕ}
    {w1 w2 v1 v2 : List (Fin 2)}
    (h₁ : q2 tm q t u w1 w2) (h₂ : q2 tm q u v v1 v2) :
    q2 tm q t v (w1 ++ v1) (w2 ++ v2):= by
  intro r1 r2 hr
  rw [append_assoc,append_assoc]
  exact h₁ (v1 +> r1) (v2 +> r2) (h₂ r1 r2 hr)
lemma qB {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t1 u1 t2 u2 : ℕ}
    {w1 w2 w3 : List (Fin 2)}
    (h₁ : q2 tm q t1 u1 w1 w2) (h₂ : q2 tm q t2 u2 w2 w3) :
    q2 tm q (t1 + t2) (u1 + u2) w1 w3:= by
  intro r1 r3 hr
  rcases qT hr with ⟨r2,hr₁,hr₂⟩
  exact sideCalls_add (h₁ r1 r2 hr₁) (h₂ r2 r3 hr₂)
lemma qk {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {w1 w2 : List (Fin 2)}
    (h : ∀ l r,(([1,0,1] +> l) {{q}}> (w1 +> r)) [tm]⊢* (l <{{q}} ([1] +> w2 +> r))) :
    q2 tm q 1 0 w1 w2:= by
  intro r1 r2 hr
  change r1=r2 at hr
  subst hr
  exact ⟨w2 +> r1,fun l => h l r1,rfl⟩
lemma qJ {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {w1 w_mid w2 : List (Fin 2)}
    (hR : ∀ l r,(([1,0,1] +> l) {{q}}> (w1 +> r)) [tm]⊢* (([1,0,1] +> w_mid +> l) {{q}}> r))
    (hL : ∀ l r,((w_mid +> l) <{{q}} ([1] +> r)) [tm]⊢* (l <{{q}} ([1] +> w2 +> r))) :
    q2 tm q 1 1 w1 w2:= by
  intro r1 r2 hr
  rcases hr with ⟨r',hcall,rfl⟩
  refine ⟨w2 +> r',fun l => ?_,rfl⟩
  exact q0 (hR l r1) (q0 (hcall (w_mid +> l)) (hL l r'))
lemma wall_n {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W) (n : ℕ) :
    q2 tm q 1 1 (W ^ n) (W ^ n):= by
  induction n with
  | zero => exact segCalls_nil tm q 1
  | succ n ih =>
    rw [pow_succ_list]
    exact q5 hwall1 ih
lemma walls {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W) (t n : ℕ) :
    q2 tm q t t (W ^ n) (W ^ n):= by
  induction t with
  | zero => exact qh tm q (W ^ n)
  | succ t ih =>
    have h1:=qB (wall_n hwall1 n) ih
    rwa [Nat.add_comm 1 t] at h1
lemma prefix_rule {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    {t u a b c : ℕ} {p p' : Digit}
    (h : q2 tm q t u (qo p ++ W ^ b) (W ^ a ++ qo p' ++ W ^ c)) (k : ℕ) :
    q2 tm q t u (W ^ k ++ (qo p ++ W ^ b)) (W ^ (k + a) ++ qo p' ++ W ^ c):= by
  have hw:=walls hwall1 t k
  have hc:=q5 hw h
  simpa only [qb,List.append_assoc] using hc
structure Effect where
  phase : Digit
  used : ℕ
  given : ℕ
  sent : ℕ
deriving DecidableEq
def qx : Digit → ℕ → Effect
  | p,0 => ⟨p,0,0,0⟩
  | p,t + 1 =>
    let a:=qx (next p) t
    ⟨a.phase,take p + a.used,give p + a.given,qO p + a.sent⟩
lemma total_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qO p) (qo p ++ W ^ (take p + n)) (W ^ (give p) ++ qo (next p) ++ W ^ n))
    (t : ℕ) (p : Digit) (n : ℕ) :
    let a:=qx p t
    q2 tm q t a.sent (qo p ++ W ^ (a.used + n)) (W ^ a.given ++ qo a.phase ++ W ^ n):= by
  induction t generalizing p n with
  | zero =>
    dsimp -failIfUnchanged [qx]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using qh tm q (qo p ++ W ^ n)
  | succ t ih =>
    dsimp -failIfUnchanged [qx]
    have h1:=hone p ((qx (next p) t).used + n)
    have h2:=prefix_rule hwall1 (ih (next p) n) (give p)
    rw [← List.append_assoc] at h2
    have h3:=qB h1 h2
    rw [Nat.add_comm 1 t,← Nat.add_assoc] at h3
    exact h3
lemma total_add (p : Digit) (t u : ℕ) :
    qx p (t + u) =
      let a:=qx p t
      let b:=qx a.phase u
      ⟨b.phase,a.used + b.used,a.given + b.given,a.sent + b.sent⟩:= by
  induction t generalizing p with
  | zero =>
    rw [Nat.zero_add]
    dsimp -failIfUnchanged only [qx]
    rcases qx p u with ⟨ph,us,gv,sn⟩
    simp only [Nat.zero_add]
  | succ t ih =>
    rw [Nat.succ_add]
    dsimp -failIfUnchanged only [qx]
    rw [ih (next p)]
    dsimp -failIfUnchanged only
    congr 1 <;> omega
lemma total_six (p : Digit) : qx p 6=⟨p,2,3,1⟩:= by
  cases p <;> rfl
lemma total_period (p : Digit) (k r : ℕ) :
    qx p (k * 6 + r) =
      let a:=qx p r
      ⟨a.phase,k * 2 + a.used,k * 3 + a.given,k + a.sent⟩:= by
  induction k with
  | zero =>
    simp only [Nat.zero_mul,Nat.zero_add]
  | succ k ih =>
    have h_eq : (k + 1) * 6 + r=6 + (k * 6 + r):= by omega
    rw [h_eq,total_add,total_six]
    dsimp -failIfUnchanged only
    rw [ih]
    dsimp -failIfUnchanged only
    congr 1 <;> omega
def qy (p : Digit) (t : ℕ) : Effect :=
  q4 (t / 6) (fun k =>
    q4 (t % 6) (fun r =>
      match qx p r with
      | ⟨ph,u,g,s⟩ =>
        qS ph (fun ph' =>
          q4 (k * 2 + u) (fun u' =>
            q4 (k * 3 + g) (fun g' =>
              q4 (k + s) (fun s' =>
                ⟨ph',u',g',s'⟩))))))
lemma totalN_spec (p : Digit) (t : ℕ) : qy p t=qx p t:= by
  unfold qy
  simp only [strictNat_eq,strictDigit_eq]
  have h_div : t=(t / 6) * 6 + t % 6:=(Nat.div_add_mod' t 6).symm
  conv_rhs => rw [h_div,total_period]
lemma totalN_rule {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qO p) (qo p ++ W ^ (take p + n)) (W ^ (give p) ++ qo (next p) ++ W ^ n))
    (p : Digit) (t n : ℕ) (h : (qy p t).used ≤ n) :
    let a:=qy p t
    q2 tm q t a.sent (qo p ++ W ^ n) (W ^ a.given ++ qo a.phase ++ W ^ (n - a.used)):= by
  dsimp -failIfUnchanged only
  have h_spec:=total_spec hwall1 hone t p (n - (qy p t).used)
  rw [← totalN_spec p t] at h_spec
  dsimp -failIfUnchanged only at h_spec
  have h_add : (qy p t).used + (n - (qy p t).used)=n:=Nat.add_sub_of_le h
  rwa [h_add] at h_spec
abbrev qv:=List (Digit × ℕ)
def q8 : qv → List (Fin 2)
  | [] => []
  | (p,n) :: xs => qo p ++ W ^ n ++ q8 xs
def qZ : ℕ → qv → Option (ℕ × qv)
  | t,[] => if t == 0 then some (0,[]) else none
  | t,(p,n) :: xs =>
    match qy p t with
    | ⟨ph,u,g,s⟩ =>
      if u ≤ n then
        match qZ s xs with
        | some (e,ys) =>
          q4 (n - u + e) (fun m =>
            some (g,(ph,m) :: ys))
        | none => none
      else none
lemma batch_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qO p) (qo p ++ W ^ (take p + n)) (W ^ (give p) ++ qo (next p) ++ W ^ n))
    (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (h : qZ t xs=some (e,ys)) :
    q2 tm q t 0 (q8 xs) (W ^ e ++ q8 ys):= by
  induction xs generalizing t e ys with
  | nil =>
    unfold qZ at h
    split_ifs at h with ht
    injection h with hpair
    injection hpair with he hys
    subst he hys
    have ht0 : t=0:=beq_iff_eq.mp ht
    subst ht0
    exact qh tm q []
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qZ at h
    dsimp -failIfUnchanged only at h
    split_ifs at h with hle
    cases hb : qZ (qy p t).sent xs with
    | none => rw [hb] at h; contradiction
    | some eys =>
      rcases eys with ⟨e',ys'⟩
      rw [hb] at h
      simp only [strictNat_eq] at h
      injection h with hpair
      injection hpair with he hys
      subst he hys
      have h1:=totalN_rule hwall1 hone p t n hle
      have h2:=ih (qy p t).sent e' ys' hb
      have h3:=q5 h1 h2
      simpa only [q8,qb,List.append_assoc] using h3
lemma calls_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hemit : ∀ r,(default <{{q}} ([1] +> r)) [tm]⊢* (([1,0,1] +> default) {{q}}> r))
    (t : ℕ) (r r' : ListBlank (Fin 2)) (h : qd tm q t r r') :
    (([1,0,1] +> default) {{q}}> r) [tm]⊢* (([1,0,1] +> default) {{q}}> r'):= by
  induction t generalizing r with
  | zero =>
    change r=r' at h
    subst h
    exact ⟨0,rfl⟩
  | succ t ih =>
    rcases h with ⟨r1,hstep,hrest⟩
    exact q0 (hstep default) (q0 (hemit r1) (ih r1 hrest))
lemma batch_root {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hemit : ∀ r,(default <{{q}} ([1] +> r)) [tm]⊢* (([1,0,1] +> default) {{q}}> r))
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qO p) (qo p ++ W ^ (take p + n)) (W ^ (give p) ++ qo (next p) ++ W ^ n))
    (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (k : ℕ) (r : ListBlank (Fin 2))
    (h : qZ t xs=some (e,ys)) :
    (([1,0,1] +> default) {{q}}> ((W ^ k) +> (q8 xs) +> r)) [tm]⊢*
    (([1,0,1] +> default) {{q}}> ((W ^ (k + e)) +> (q8 ys) +> r)):= by
  apply calls_spec hemit t
  have hw:=walls hwall1 t k
  have hb:=batch_spec hwall1 hone t xs e ys h
  have hc:=q5 hw hb r r rfl
  simpa only [qb,List.append_assoc,append_assoc] using hc
abbrev Runs:=List (List (Fin 2) × ℕ)
def q3 {α : Type*} (r : Runs) (f : Runs → α) : α :=
  match r with
  | [] => f []
  | head :: tail => f (head :: tail)
@[simp] lemma strictRuns_eq {α : Type*} (r : Runs) (f : Runs → α) : q3 r f=f r:= by
  cases r <;> rfl
def Runs.denote : Runs → ListBlank (Fin 2)
  | [] => default
  | (w,n) :: xs => (w ^ n) +> Runs.denote xs
def Runs.push (w : List (Fin 2)) (n : ℕ) (xs : Runs) : Runs :=
  match w with
  | [] => xs
  | b :: w' =>
    if n == 0 then xs
    else match xs with
      | [] => q4 n (fun n' => [(b :: w',n')])
      | (v,m) :: ys =>
        if (b :: w') == v then
          q4 (n + m) (fun nm => (b :: w',nm) :: ys)
        else
          q4 n (fun n' => (b :: w',n') :: (v,m) :: ys)
lemma Runs.push_spec (w : List (Fin 2)) (n : ℕ) (xs : Runs) :
    Runs.denote (Runs.push w n xs)=(w ^ n) +> Runs.denote xs:= by
  cases w with
  | nil => simp [Runs.push,nil_pow_list]
  | cons b w' =>
    unfold Runs.push
    simp only [strictNat_eq]
    by_cases hn : (n == 0)=true
    · have hn0 : n=0:=beq_iff_eq.mp hn
      subst hn0
      simp
    · rw [if_neg hn]
      cases xs with
      | nil => rfl
      | cons vm ys =>
        rcases vm with ⟨v,m⟩
        dsimp -failIfUnchanged only
        by_cases hv : ((b :: w') == v)=true
        · have hv_eq : b :: w'=v:=beq_iff_eq.mp hv
          subst hv_eq
          rw [if_pos hv,Runs.denote,Runs.denote,qb,append_assoc]
        · rw [if_neg hv]; rfl
def Runs.pop : Runs → Fin 2 × Runs
  | [] => (0,[])
  | ([],_) :: xs => Runs.pop xs
  | (b :: w,n) :: xs =>
    if n == 0 then Runs.pop xs
    else if n == 1 then
      match w with
      | [] => (b, xs)
      | b2 :: w' => q3 (Runs.push (b2 :: w') 1 xs) (fun xs2 => (b, xs2))
    else
      q4 (n - 1) (fun n' =>
        q3 (Runs.push (b :: w) n' xs) (fun xs1 =>
          q3 (Runs.push w 1 xs1) (fun xs2 =>
            (b,xs2))))
lemma Runs.pop_spec (xs : Runs) :
    Runs.denote xs=(Runs.pop xs).1 >> Runs.denote (Runs.pop xs).2:= by
  induction xs with
  | nil =>
    simp only [Runs.pop,Runs.denote,zero_cons_default]
  | cons wn xs ih =>
    rcases wn with ⟨w,n⟩
    cases w with
    | nil =>
      simpa [Runs.pop,Runs.denote,nil_pow_list] using ih
    | cons b w =>
      unfold Runs.pop
      by_cases hn : (n == 0)=true
      · have hn0 : n=0:=beq_iff_eq.mp hn
        subst hn0
        simpa [Runs.denote] using ih
      · rw [if_neg hn]
        by_cases hn1 : (n == 1)=true
        · rw [if_pos hn1]
          have hn1_eq : n=1:=beq_iff_eq.mp hn1
          subst hn1_eq
          cases w with
          | nil => simp [Runs.denote,pow_succ_list]
          | cons b2 w' =>
            simp [strictRuns_eq,Runs.push_spec,Runs.denote,pow_succ_list]
        · rw [if_neg hn1]
          simp only [strictNat_eq,strictRuns_eq]
          rw [Runs.push_spec,Runs.push_spec,Runs.denote]
          have hn_pos : 0 < n:=Nat.pos_of_ne_zero (by intro h0; subst h0; exact hn rfl)
          have hn_eq : n=(n - 1) + 1:=(Nat.sub_add_cancel hn_pos).symm
          conv_lhs => rw [hn_eq,pow_succ_list]
          simp [pow_succ_list,append_assoc]
def Runs.remove : List (Fin 2) → Runs → Option Runs
  | [],xs => q3 xs (fun xs' => some xs')
  | b :: w,xs =>
    match Runs.pop xs with
    | (b',xs') => if b == b' then Runs.remove w xs' else none
lemma Runs.remove_spec {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove w xs=some ys) :
    Runs.denote xs=w +> Runs.denote ys:= by
  induction w generalizing xs with
  | nil =>
    unfold Runs.remove at h
    simp only [strictRuns_eq] at h
    injection h with hys; subst hys; rfl
  | cons b w ih =>
    unfold Runs.remove at h
    dsimp -failIfUnchanged only at h
    split_ifs at h with hb
    have hb_eq : b=(Runs.pop xs).1:=beq_iff_eq.mp hb
    rw [Runs.pop_spec xs,← hb_eq,ih h]
    rfl
def strip_prefix : List (Fin 2) → List (Fin 2) → Option (List (Fin 2) × List (Fin 2))
  | [], v => some ([], v)
  | w, [] => some (w, [])
  | b1 :: w', b2 :: v' => if b1 == b2 then strip_prefix w' v' else none

lemma strip_prefix_spec {w v w_rem v_rem : List (Fin 2)}
    (h : strip_prefix w v = some (w_rem, v_rem)) :
    (w_rem = [] → v = w ++ v_rem) ∧ (v_rem = [] → w = v ++ w_rem) := by
  induction w generalizing v with
  | nil =>
    unfold strip_prefix at h
    injection h with hp; injection hp with hw hv
    subst hw hv
    refine ⟨fun _ => rfl, fun hv0 => ?_⟩
    subst hv0; rfl
  | cons b1 w' ih =>
    cases v with
    | nil =>
      unfold strip_prefix at h
      injection h with hp; injection hp with hw hv
      subst hw hv
      refine ⟨fun hw0 => by contradiction, fun _ => rfl⟩
    | cons b2 v' =>
      unfold strip_prefix at h
      split_ifs at h with hb
      have hb_eq : b1 = b2 := beq_iff_eq.mp hb
      subst hb_eq
      rcases ih h with ⟨ih1, ih2⟩
      refine ⟨fun hw0 => congrArg (b1 :: ·) (ih1 hw0), fun hv0 => congrArg (b1 :: ·) (ih2 hv0)⟩

def Runs.remove_word : ℕ → List (Fin 2) → Runs → Option Runs
  | 0, w, xs => Runs.remove w xs
  | _ + 1, [], xs => q3 xs (fun xs' => some xs')
  | _ + 1, w, [] => Runs.remove w []
  | fuel + 1, w, (v, nv) :: ys =>
    if nv == 0 then Runs.remove_word fuel w ys
    else
      match strip_prefix w v with
      | some ([], v_rem) =>
        q4 (nv - 1) (fun nv' =>
          q3 (Runs.push v nv' ys) (fun ys1 =>
            q3 (Runs.push v_rem 1 ys1) (fun ys2 => some ys2)))
      | some (w_rem, []) =>
        q4 (nv - 1) (fun nv' =>
          q3 (Runs.push v nv' ys) (fun ys1 =>
            Runs.remove_word fuel w_rem ys1))
      | _ => none

lemma Runs.remove_word_spec {fuel : ℕ} {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove_word fuel w xs = some ys) :
    Runs.denote xs = w +> Runs.denote ys := by
  induction fuel generalizing w xs ys with
  | zero => exact Runs.remove_spec h
  | succ fuel ih =>
    cases w with
    | nil =>
      unfold Runs.remove_word at h
      simp only [strictRuns_eq] at h
      injection h with hys; subst hys; rfl
    | cons b1 w' =>
      cases xs with
      | nil =>
        unfold Runs.remove_word at h
        exact Runs.remove_spec h
      | cons vn ys0 =>
        rcases vn with ⟨v, nv⟩
        unfold Runs.remove_word at h
        by_cases hnv : (nv == 0) = true
        · rw [if_pos hnv] at h
          have hnv0 : nv = 0 := beq_iff_eq.mp hnv
          subst hnv0
          simpa [Runs.denote] using ih h
        · rw [if_neg hnv] at h
          have hnv_pos : 0 < nv := Nat.pos_of_ne_zero (by intro h0; subst h0; exact hnv rfl)
          have hnv_eq : nv = 1 + (nv - 1) := (Nat.add_sub_of_le hnv_pos).symm
          have h_v_pow : v ^ nv = v ++ v ^ (nv - 1) := by
            conv_lhs => rw [hnv_eq, qb, pow_succ_list, pow_zero_list, List.append_nil]
          cases hsp : strip_prefix (b1 :: w') v with
          | none => rw [hsp] at h; contradiction
          | some wv =>
            rcases wv with ⟨w_rem, v_rem⟩
            rw [hsp] at h
            rcases strip_prefix_spec hsp with ⟨hsp1, hsp2⟩
            cases w_rem with
            | nil =>
              dsimp -failIfUnchanged only at h
              simp only [strictNat_eq, strictRuns_eq] at h
              injection h with hys; subst hys
              have hv_eq := hsp1 rfl
              have h_v_pow2 : v ^ nv = (b1 :: w' ++ v_rem) ++ v ^ (nv - 1) :=
                h_v_pow.trans (congrArg (· ++ v ^ (nv - 1)) hv_eq)
              rw [Runs.denote, h_v_pow2, Runs.push_spec, Runs.push_spec]
              simp [pow_succ_list, append_assoc]
            | cons bw w_tail =>
              cases v_rem with
              | nil =>
                dsimp -failIfUnchanged only at h
                simp only [strictNat_eq, strictRuns_eq] at h
                have hw_eq := hsp2 rfl
                have h_ih := ih h
                rw [Runs.push_spec] at h_ih
                rw [Runs.denote, h_v_pow, append_assoc, h_ih, hw_eq, append_assoc]
              | cons bv v_tail =>
                dsimp -failIfUnchanged only at h
                contradiction
def qGcd : ℕ → ℕ → ℕ → ℕ
  | 0, m, _ => m
  | fuel + 1, m, n => if n == 0 then m else qGcd fuel n (m % n)
def Runs.skip_block (w : List (Fin 2)) (limit : ℕ) (x v : List (Fin 2)) (m : ℕ) (ys : Runs) : Option (ℕ × Runs) :=
  if w.length == v.length then
    if (x ++ v) == (w ++ x) then
      if m ≤ limit then
        if 0 < m then
          q3 (Runs.push x 1 ys) (fun zs => some (m, zs))
        else none
      else
        if 0 < limit then
          q4 (m - limit) (fun m' =>
            q3 (Runs.push v m' ys) (fun ys1 =>
              q3 (Runs.push x 1 ys1) (fun zs =>
                some (limit, zs))))
        else none
    else none
  else
  q4 (qGcd 8 w.length v.length) (fun g =>
    q4 (w.length / g) (fun a =>
      q4 (v.length / g) (fun b =>
        q4 (min (limit / b) (m / a)) (fun k =>
          if 0 < k then
            if k * b ≤ limit then
              if k * a ≤ m then
                if (x ++ v ^ a) == (w ^ b ++ x) then
                  q4 (k * b) (fun kb =>
                    q4 (m - k * a) (fun m' =>
                      q3 (Runs.push v m' ys) (fun ys1 =>
                        q3 (Runs.push x 1 ys1) (fun zs =>
                          some (kb,zs)))))
                else none
              else none
            else none
          else none))))
lemma Runs.skip_block_spec {w : List (Fin 2)} {limit : ℕ} {x v : List (Fin 2)} {m : ℕ} {ys : Runs} {n : ℕ} {zs : Runs}
    (h : Runs.skip_block w limit x v m ys=some (n,zs)) :
    n ≤ limit ∧ x +> (v ^ m) +> Runs.denote ys=(w ^ n) +> Runs.denote zs:= by
  unfold Runs.skip_block at h
  simp only [strictNat_eq,strictRuns_eq] at h
  by_cases hlen : (w.length == v.length) = true
  · rw [if_pos hlen] at h
    split_ifs at h with heq hm_lim hm_pos hlim_pos
    · injection h with hpair; injection hpair with hn hzs; subst hn hzs
      refine ⟨hm_lim, ?_⟩
      rw [Runs.push_spec]
      have hx1 : x ^ (1 : ℕ) = x := by simp [pow_succ_list]
      rw [hx1]
      have heq1 : x ++ v ^ 1 = w ^ 1 ++ x := by simpa [pow_succ_list] using beq_iff_eq.mp heq
      have hk_comm := commute_power heq1 m
      simp only [Nat.mul_one] at hk_comm
      rw [← append_assoc, hk_comm, append_assoc]
    · injection h with hpair; injection hpair with hn hzs; subst hn hzs
      refine ⟨le_rfl, ?_⟩
      rw [Runs.push_spec, Runs.push_spec]
      have hx1 : x ^ (1 : ℕ) = x := by simp [pow_succ_list]
      rw [hx1]
      have hlim_le : limit ≤ m := Nat.le_of_not_le hm_lim
      have hm_eq : m = limit + (m - limit) := (Nat.add_sub_of_le hlim_le).symm
      have heq1 : x ++ v ^ 1 = w ^ 1 ++ x := by simpa [pow_succ_list] using beq_iff_eq.mp heq
      have hk_comm := commute_power heq1 limit
      simp only [Nat.mul_one] at hk_comm
      conv_lhs => rw [hm_eq, qb]
      rw [append_assoc (v ^ limit), ← append_assoc x, hk_comm, append_assoc]
  · rw [if_neg hlen] at h
    split_ifs at h with hk hkb hka heq
    injection h with hpair
    injection hpair with hn hzs
    subst hn hzs
    refine ⟨hkb,?_⟩
    rw [Runs.push_spec,Runs.push_spec]
    have hx1 : x ^ (1 : ℕ)=x:= by simp [pow_succ_list]
    rw [hx1]
    have hm_eq:=(Nat.add_sub_of_le hka).symm
    have hk_comm:=commute_power (beq_iff_eq.mp heq) (min (limit / (v.length / qGcd 8 w.length v.length)) (m / (w.length / qGcd 8 w.length v.length)))
    have h_lhs : x +> (v ^ m) +> Runs.denote ys =
        (x ++ v ^ (min (limit / (v.length / qGcd 8 w.length v.length)) (m / (w.length / qGcd 8 w.length v.length)) * (w.length / qGcd 8 w.length v.length))) +>
        (v ^ (m - min (limit / (v.length / qGcd 8 w.length v.length)) (m / (w.length / qGcd 8 w.length v.length)) * (w.length / qGcd 8 w.length v.length))) +> Runs.denote ys:= by
      conv_lhs => rw [hm_eq,qb]
      rw [append_assoc (v ^ _),← append_assoc x]
    rw [h_lhs,hk_comm,append_assoc]
def Runs.skip_periodic (w : List (Fin 2)) (n : ℕ) (xs : Runs) : Option (ℕ × Runs) :=
  match xs with
  | (x,nx) :: (v,m) :: ys =>
    if nx == 1 then Runs.skip_block w n x v m ys
    else Runs.skip_block w n [] x nx ((v,m) :: ys)
  | [(v,m)] => Runs.skip_block w n [] v m []
  | [] => none
lemma Runs.skip_periodic_spec {w : List (Fin 2)} {n : ℕ} {xs : Runs} {k : ℕ} {ys : Runs}
    (h : Runs.skip_periodic w n xs=some (k,ys)) :
    k ≤ n ∧ Runs.denote xs=(w ^ k) +> Runs.denote ys:= by
  unfold Runs.skip_periodic at h
  rcases xs with _ | ⟨⟨x,nx⟩,_ | ⟨⟨v,m⟩,ys'⟩⟩
  · contradiction
  · simpa [Runs.denote] using Runs.skip_block_spec h
  · simp only [] at h
    split_ifs at h with hnx
    · have hnx1 : nx=1:=beq_iff_eq.mp hnx
      subst hnx1
      have hx1 : x ^ (1 : ℕ)=x:= by simp [pow_succ_list]
      simpa [Runs.denote,hx1] using Runs.skip_block_spec h
    · simpa [Runs.denote] using Runs.skip_block_spec h
def Runs.skip (w : List (Fin 2)) (n : ℕ) (xs : Runs) : Option (ℕ × Runs) :=
  match xs with
  | [] => none
  | (v,m) :: ys =>
    if w == v then
      q4 (min n m) (fun k =>
        q4 (m - k) (fun m' =>
          q3 (Runs.push v m' ys) (fun zs =>
            some (k,zs))))
    else Runs.skip_periodic w n ((v,m) :: ys)
lemma Runs.skip_spec {w : List (Fin 2)} {n : ℕ} {xs : Runs} {k : ℕ} {ys : Runs}
    (h : Runs.skip w n xs=some (k,ys)) :
    k ≤ n ∧ Runs.denote xs=(w ^ k) +> Runs.denote ys:= by
  rcases xs with _ | ⟨⟨v,m⟩,ys'⟩
  · contradiction
  · unfold Runs.skip at h
    simp only [strictNat_eq,strictRuns_eq] at h
    split_ifs at h with hwv
    · injection h with hpair
      injection hpair with hk hys
      subst hk hys
      have hwv_eq : w=v:=beq_iff_eq.mp hwv
      subst hwv_eq
      refine ⟨Nat.min_le_left n m,?_⟩
      rw [Runs.denote,Runs.push_spec,← append_assoc,← qb]
      have hm_eq : m=min n m + (m - min n m):=(Nat.add_sub_of_le (Nat.min_le_right n m)).symm
      rw [← hm_eq]
    · exact Runs.skip_periodic_spec h
def Runs.remove_fast_step (fuel : ℕ) (w : List (Fin 2)) (n : ℕ) (xs : Runs) (rec : ℕ → Runs → Option Runs) : Option Runs :=
  match Runs.skip w n xs with
  | some (k,ys) => q4 (n - k) (fun n' => rec n' ys)
  | none =>
    match Runs.remove_word 16 w xs with
    | some ys => q4 (n - 1) (fun n' => rec n' ys)
    | none => none

def Runs.remove_fast : ℕ → List (Fin 2) → ℕ → Runs → Option Runs
  | 0,_,n,xs => if n == 0 then q3 xs (fun xs' => some xs') else none
  | fuel + 1,w,n,xs =>
    if n == 0 then q3 xs (fun xs' => some xs')
    else if n ≤ 5 then Runs.remove_word 16 (w ^ n) xs
    else match xs with
      | (x, nx) :: (v, m) :: ys =>
        if nx == 1 && w.length == v.length && m + 1 == n && (x ++ v) == (w ++ x) then
          Runs.remove_word 16 w ((x, 1) :: ys)
        else Runs.remove_fast_step fuel w n xs (Runs.remove_fast fuel w)
      | _ => Runs.remove_fast_step fuel w n xs (Runs.remove_fast fuel w)

lemma Runs.remove_fast_step_spec {fuel : ℕ} {w : List (Fin 2)} {n : ℕ} {xs ys : Runs}
    (hn_pos : 0 < n)
    (ih : ∀ {n' : ℕ} {xs' ys' : Runs}, Runs.remove_fast fuel w n' xs' = some ys' → Runs.denote xs' = (w ^ n') +> Runs.denote ys')
    (h : Runs.remove_fast_step fuel w n xs (Runs.remove_fast fuel w) = some ys) :
    Runs.denote xs = (w ^ n) +> Runs.denote ys := by
  unfold Runs.remove_fast_step at h
  cases hskip : Runs.skip w n xs with
  | some kys =>
    rcases kys with ⟨k,zs⟩
    rw [hskip] at h
    simp only [strictNat_eq] at h
    rcases Runs.skip_spec hskip with ⟨hkn,hden⟩
    rw [hden,ih h,← append_assoc,← qb,Nat.add_sub_of_le hkn]
  | none =>
    rw [hskip] at h
    cases hrem : Runs.remove_word 16 w xs with
    | none => rw [hrem] at h; contradiction
    | some zs =>
      rw [hrem] at h
      simp only [strictNat_eq] at h
      rw [Runs.remove_word_spec hrem,ih h]
      have hn_eq : n=(n - 1) + 1:=(Nat.sub_add_cancel hn_pos).symm
      conv_rhs => rw [hn_eq,pow_succ_list,append_assoc]

lemma Runs.remove_fast_spec {fuel : ℕ} {w : List (Fin 2)} {n : ℕ} {xs ys : Runs}
    (h : Runs.remove_fast fuel w n xs=some ys) :
    Runs.denote xs=(w ^ n) +> Runs.denote ys:= by
  induction fuel generalizing n xs ys with
  | zero =>
    unfold Runs.remove_fast at h
    simp only [strictRuns_eq] at h
    split_ifs at h with hn
    injection h with hys; subst hys
    have hn0 : n=0:=beq_iff_eq.mp hn; subst hn0
    simp
  | succ fuel ih =>
    unfold Runs.remove_fast at h
    simp only [strictRuns_eq] at h
    split_ifs at h with hn hn5
    · injection h with hys; subst hys
      have hn0 : n=0:=beq_iff_eq.mp hn; subst hn0
      simp
    · exact Runs.remove_word_spec h
    · have hn_pos : 0 < n:=Nat.pos_of_ne_zero (by intro h0; subst h0; exact hn rfl)
      rcases xs with _ | ⟨⟨x, nx⟩, _ | ⟨⟨v, m⟩, ys'⟩⟩
      · exact Runs.remove_fast_step_spec hn_pos ih h
      · exact Runs.remove_fast_step_spec hn_pos ih h
      · dsimp -failIfUnchanged only at h
        split_ifs at h with hfast
        · simp only [Bool.and_eq_true, beq_iff_eq] at hfast
          rcases hfast with ⟨⟨⟨hnx1, _⟩, hmn⟩, hxveq⟩
          subst hnx1 hmn
          have hx1 : x ^ (1 : ℕ) = x := by simp [pow_succ_list]
          have heq1 : x ++ v ^ 1 = w ^ 1 ++ x := by simpa [pow_succ_list] using hxveq
          have hk_comm := commute_power heq1 m
          simp only [Nat.mul_one] at hk_comm
          have hrem := Runs.remove_word_spec h
          simp only [Runs.denote, hx1] at hrem
          rw [Runs.denote, Runs.denote, hx1, ← append_assoc, hk_comm, append_assoc, hrem, ← append_assoc, pow_shift]
        · exact Runs.remove_fast_step_spec hn_pos ih h
def Runs.size : Runs → ℕ
  | [] => 0
  | (w,n) :: xs => w.length * n + Runs.size xs
def Runs.zeros : Runs → Bool
  | [] => true
  | (w,_) :: xs => if BusyBeaver.Longitudinal.BoundedConfig.all0 w then Runs.zeros xs else false
lemma Runs.zeros_spec {xs : Runs} (h : Runs.zeros xs=true) : Runs.denote xs=default:= by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w,n⟩
    unfold Runs.zeros at h
    split_ifs at h with hw
    rw [Runs.denote,ih h,qM hw n]
structure RMConfig where
  left : Runs
  right : Runs
  state : Fin 6
  dir : Dir
deriving DecidableEq
def RMConfig.denote (c : RMConfig) : Cfg (Fin 2) (Fin 6) :=
  match c.dir with
  | .left => Runs.denote c.left <{{c.state}} Runs.denote c.right
  | .right => Runs.denote c.left {{c.state}}> Runs.denote c.right
def RM.raw (tm : Machine (Fin 2) (Fin 6)) (c : RMConfig) : Option RMConfig :=
  match c.dir with
  | .left =>
    match Runs.pop c.left with
    | (b,l) =>
      match tm c.state b with
      | none => none
      | some (none,_) => none
      | some (some q',Stmt.write b' .left) =>
        q3 (Runs.push [b'] 1 c.right) (fun r' =>
          some ⟨l,r',q',.left⟩)
      | some (some q',Stmt.write b' .right) =>
        q3 (Runs.push [b'] 1 l) (fun l' =>
          some ⟨l',c.right,q',.right⟩)
  | .right =>
    match Runs.pop c.right with
    | (b,r) =>
      match tm c.state b with
      | none => none
      | some (none,_) => none
      | some (some q',Stmt.write b' .left) =>
        q3 (Runs.push [b'] 1 r) (fun r' =>
          some ⟨c.left,r',q',.left⟩)
      | some (some q',Stmt.write b' .right) =>
        q3 (Runs.push [b'] 1 c.left) (fun l' =>
          some ⟨l',r,q',.right⟩)
lemma RM.raw_spec {tm : Machine (Fin 2) (Fin 6)} {c c' : RMConfig}
    (h : RM.raw tm c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  rcases c with ⟨l,r,q,d⟩
  unfold RM.raw at h
  cases d
  · dsimp -failIfUnchanged only at h
    have hpop:=Runs.pop_spec l
    cases htm : tm q (Runs.pop l).1 with
    | none => rw [htm] at h; contradiction
    | some qa =>
      rcases qa with ⟨ _ | q',⟨b',_ | _⟩⟩
      · rw [htm] at h; contradiction
      · rw [htm] at h; contradiction
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply qm
        unfold RMConfig.denote step
        dsimp -failIfUnchanged only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply qm
        unfold RMConfig.denote step
        dsimp -failIfUnchanged only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
  · dsimp -failIfUnchanged only at h
    have hpop:=Runs.pop_spec r
    cases htm : tm q (Runs.pop r).1 with
    | none => rw [htm] at h; contradiction
    | some qa =>
      rcases qa with ⟨ _ | q',⟨b',_ | _⟩⟩
      · rw [htm] at h; contradiction
      · rw [htm] at h; contradiction
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply qm
        unfold RMConfig.denote step
        dsimp -failIfUnchanged only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply qm
        unfold RMConfig.denote step
        dsimp -failIfUnchanged only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
def ql (d : Dir) (c : RMConfig) : RMConfig :=
  match d,c.dir with
  | .left,.right =>
    match Runs.pop c.right with
    | (b,r') =>
      q3 (Runs.push [b] 1 c.left) (fun l' =>
        ⟨l',r',c.state,.left⟩)
  | .right,.left =>
    match Runs.pop c.left with
    | (b,l') =>
      q3 (Runs.push [b] 1 c.right) (fun r' =>
        ⟨l',r',c.state,.right⟩)
  | _,_ => c
lemma qV (d : Dir) (c : RMConfig) : (ql d c).denote=c.denote:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> try rfl
  · unfold ql RMConfig.denote
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.pop_spec r]
    simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil,
               Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  · unfold ql RMConfig.denote
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.pop_spec l]
    simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil,
               Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
lemma qa1 (d : Dir) (c : RMConfig) : (ql d c).dir=d:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> simp [ql]
lemma qL (d : Dir) (c : RMConfig) : (ql d c).state=c.state:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> simp [ql]
structure Scan where
  q : Fin 6
  dir : Dir
  scan_in : List (Fin 2)
  scan_out : List (Fin 2)
  context : List (Fin 2)
def q7 (tm : Machine (Fin 2) (Fin 6)) (s : Scan) : Prop :=
  ∀ (n : ℕ) (l r : ListBlank (Fin 2)),
    match s.dir with
    | .right =>
      ((s.context.reverse +> l) {{s.q}}> ((s.scan_in ^ n) +> r)) [tm]⊢*
      ((s.context.reverse +> (s.scan_out.reverse ^ n) +> l) {{s.q}}> r)
    | .left =>
      (((s.scan_in.reverse ^ n) +> l) <{{s.q}} (s.context +> r)) [tm]⊢*
      (l <{{s.q}} (s.context +> (s.scan_out ^ n) +> r))
lemma qI {tm : Machine (Fin 2) (Fin 6)} {s : Scan} (hd : s.dir=.right)
    (hbase : ∀ l r,((s.context.reverse +> l) {{s.q}}> (s.scan_in +> r)) [tm]⊢*
                    ((s.context.reverse +> s.scan_out.reverse +> l) {{s.q}}> r)) :
    q7 tm s:= by
  unfold q7
  intro n l r
  rw [hd]
  dsimp -failIfUnchanged only
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [pow_succ_list,append_assoc]
    have h1:=hbase l ((s.scan_in ^ n) +> r)
    have h2:=ih (s.scan_out.reverse +> l) r
    rw [← append_assoc (s.scan_out.reverse ^ n) s.scan_out.reverse l,pow_shift] at h2
    exact q0 h1 h2
lemma qg {tm : Machine (Fin 2) (Fin 6)} {s : Scan} (hd : s.dir=.left)
    (hbase : ∀ l r,((s.scan_in.reverse +> l) <{{s.q}} (s.context +> r)) [tm]⊢*
                    (l <{{s.q}} (s.context +> s.scan_out +> r))) :
    q7 tm s:= by
  unfold q7
  intro n l r
  rw [hd]
  dsimp -failIfUnchanged only
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [pow_succ_list,append_assoc]
    have h1:=hbase ((s.scan_in.reverse ^ n) +> l) r
    have h2:=ih l (s.scan_out +> r)
    rw [← append_assoc (s.scan_out ^ n) s.scan_out r,pow_shift] at h2
    exact q0 h1 h2
def qj:=Runs.remove_fast 32
def qr (s : Scan) (n : ℕ) (l r : Runs) : Option (Runs × Runs) :=
  match s.dir with
  | .left =>
    match Runs.remove_word 16 s.context r,qj s.scan_in.reverse n l with
    | some r',some l' =>
      q3 (Runs.push s.scan_out n r') (fun r1 =>
        q3 (Runs.push s.context 1 r1) (fun r2 =>
          some (l',r2)))
    | _,_ => none
  | .right =>
    match Runs.remove_word 16 s.context.reverse l,qj s.scan_in n r with
    | some l',some r' =>
      q3 (Runs.push s.scan_out.reverse n l') (fun l1 =>
        q3 (Runs.push s.context.reverse 1 l1) (fun l2 =>
          some (l2,r')))
    | _,_ => none
lemma qN {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {n : ℕ} {l r l' r' : Runs}
    (hv : q7 tm s) (h : qr s n l r=some (l',r')) :
    (RMConfig.denote ⟨l,r,s.q,s.dir⟩) [tm]⊢* (RMConfig.denote ⟨l',r',s.q,s.dir⟩):= by
  unfold q7 at hv
  rcases s with ⟨q,d,sin,sout,ctx⟩
  have hv_n:=hv n
  unfold qr qj at h
  cases d
  · dsimp -failIfUnchanged only at h hv_n
    cases hr : Runs.remove_word 16 ctx r with
    | none => rw [hr] at h; contradiction
    | some r0 =>
      rw [hr] at h
      cases hl : Runs.remove_fast 32 sin.reverse n l with
      | none => rw [hl] at h; contradiction
      | some l0 =>
        rw [hl] at h
        simp only [strictRuns_eq] at h
        injection h with hpair
        injection hpair with hl' hr'
        subst hl' hr'
        unfold RMConfig.denote
        dsimp -failIfUnchanged only
        rw [Runs.push_spec,Runs.push_spec,Runs.remove_word_spec hr,Runs.remove_fast_spec hl]
        have hc1 : ctx ^ (1 : ℕ)=ctx:= by simp [pow_succ_list]
        rw [hc1]
        exact hv_n (Runs.denote l0) (Runs.denote r0)
  · dsimp -failIfUnchanged only at h hv_n
    cases hl : Runs.remove_word 16 ctx.reverse l with
    | none => rw [hl] at h; contradiction
    | some l0 =>
      rw [hl] at h
      cases hr : Runs.remove_fast 32 sin n r with
      | none => rw [hr] at h; contradiction
      | some r0 =>
        rw [hr] at h
        simp only [strictRuns_eq] at h
        injection h with hpair
        injection hpair with hl' hr'
        subst hl' hr'
        unfold RMConfig.denote
        dsimp -failIfUnchanged only
        rw [Runs.push_spec,Runs.push_spec,Runs.remove_word_spec hl,Runs.remove_fast_spec hr]
        have hc1 : ctx.reverse ^ (1 : ℕ)=ctx.reverse:= by simp [pow_succ_list]
        rw [hc1]
        exact hv_n (Runs.denote l0) (Runs.denote r0)
def use_scan (s : Scan) (n : ℕ) (c : RMConfig) : Option RMConfig :=
  if c.state == s.q then
    let z:=ql s.dir c
    match qr s n z.left z.right with
    | some (l,r) => some ⟨l,r,s.q,s.dir⟩
    | none => none
  else none
lemma use_scan_spec {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {n : ℕ} {c c' : RMConfig}
    (hv : q7 tm s) (h : use_scan s n c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold use_scan at h
  split_ifs at h with hq
  have hq_eq : c.state=s.q:=beq_iff_eq.mp hq
  rw [← qV s.dir c]
  have hd_z : (ql s.dir c).dir=s.dir:=qa1 s.dir c
  have hq_z : (ql s.dir c).state=s.q:= by rw [qL,hq_eq]
  rcases hz : ql s.dir c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp -failIfUnchanged only at hd_z hq_z h
  subst hd_z hq_z
  cases hs : qr s n l r with
  | none => rw [hs] at h; contradiction
  | some lr =>
    rcases lr with ⟨l',r'⟩
    rw [hs] at h
    injection h with hc'; subst hc'
    exact qN hv hs
def Runs.remove_one (w : List (Fin 2)) (xs : Runs) : Option Runs :=
  match xs with
  | (v, 1) :: ys =>
    if w == v then q3 ys (fun ys' => some ys')
    else Runs.remove_word 16 w xs
  | _ => Runs.remove_word 16 w xs
lemma Runs.remove_one_spec {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove_one w xs = some ys) :
    Runs.denote xs = w +> Runs.denote ys := by
  unfold Runs.remove_one at h
  rcases xs with _ | ⟨⟨v, _ | _ | m⟩, rest⟩
  · exact Runs.remove_word_spec h
  · exact Runs.remove_word_spec h
  · simp only [Nat.zero_add] at h ⊢
    split_ifs at h with hwv
    · simp only [strictRuns_eq] at h
      injection h with hys; subst hys
      have hwv_eq : w = v := beq_iff_eq.mp hwv
      subst hwv_eq
      simp [Runs.denote, pow_succ_list]
    · exact Runs.remove_word_spec h
  · exact Runs.remove_word_spec h
def Runs.remove_exact (w : List (Fin 2)) (n : ℕ) (xs : Runs) : Option Runs :=
  if n == 0 then q3 xs (fun xs' => some xs')
  else match xs with
    | (v, m) :: ys =>
      if w == v then
        if n == m then q3 ys (fun ys' => some ys')
        else qj w n xs
      else qj w n xs
    | [] => none
lemma Runs.remove_exact_spec {w : List (Fin 2)} {n : ℕ} {xs ys : Runs}
    (h : Runs.remove_exact w n xs = some ys) :
    Runs.denote xs = (w ^ n) +> Runs.denote ys := by
  unfold Runs.remove_exact at h
  split_ifs at h with hn0
  · simp only [strictRuns_eq] at h
    injection h with hys; subst hys
    have hn : n = 0 := beq_iff_eq.mp hn0; subst hn
    simp
  · rcases xs with _ | ⟨⟨v, m⟩, rest⟩
    · contradiction
    · dsimp -failIfUnchanged only at h
      split_ifs at h with hwv hnm
      · simp only [strictRuns_eq] at h
        injection h with hys; subst hys
        have hwv_eq : w = v := beq_iff_eq.mp hwv
        have hnm_eq : n = m := beq_iff_eq.mp hnm
        subst hwv_eq hnm_eq
        rfl
      · exact Runs.remove_fast_spec h
      · exact Runs.remove_fast_spec h
def qi : qv → Runs → Option Runs
  | [],r => q3 r (fun r' => some r')
  | (p,n) :: xs,r =>
    match Runs.remove_one (qo p) r with
    | none => none
    | some r1 =>
      match Runs.remove_exact W n r1 with
      | none => none
      | some r2 => qi xs r2
lemma qF {xs : qv} {r r' : Runs}
    (h : qi xs r=some r') :
    Runs.denote r=(q8 xs) +> Runs.denote r':= by
  induction xs generalizing r with
  | nil =>
    unfold qi at h
    simp only [strictRuns_eq] at h
    injection h with hr'; subst hr'; rfl
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qi at h
    cases hr1 : Runs.remove_one (qo p) r with
    | none => rw [hr1] at h; contradiction
    | some r1 =>
      rw [hr1] at h
      dsimp -failIfUnchanged only at h
      cases hr2 : Runs.remove_exact W n r1 with
      | none => rw [hr2] at h; contradiction
      | some r2 =>
        rw [hr2] at h
        dsimp -failIfUnchanged only at h
        rw [Runs.remove_one_spec hr1,Runs.remove_exact_spec hr2,ih h,q8,append_assoc,append_assoc]
def qw : qv → Runs → Runs
  | [],r => r
  | (p,n) :: xs,r =>
    q3 (qw xs r) (fun r1 =>
      q3 (Runs.push W n r1) (fun r2 =>
        Runs.push (qo p) 1 r2))
lemma qU (xs : qv) (r : Runs) :
  Runs.denote (qw xs r)=(q8 xs) +> Runs.denote r:= by
  induction xs with
  | nil => rfl
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qw q8
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.push_spec,ih]
    have hw1 : (qo p) ^ (1 : ℕ)=qo p:= by simp [pow_succ_list]
    rw [hw1,append_assoc,append_assoc]
def qC (q : Fin 6) (u : List (Fin 2)) (t k : ℕ) (xs : qv) (c : RMConfig) : Option RMConfig :=
  if c.state == q then
    let z:=ql .right c
    match Runs.remove_word 16 u.reverse z.left,Runs.remove_exact W k z.right,qZ t xs with
    | some l0,some r0,some (e,ys) =>
      if Runs.zeros l0 then
        match qi xs r0 with
        | some r1 =>
          q4 (k + e) (fun ke =>
            q3 (qw ys r1) (fun r2 =>
              q3 (Runs.push W ke r2) (fun r3 =>
                some ⟨z.left,r3,q,.right⟩)))
        | none => none
      else none
    | _,_,_ => none
  else none
lemma qP {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hrule : ∀ t xs e ys k r,qZ t xs=some (e,ys) →
      (([1,0,1] +> default) {{q}}> ((W ^ k) +> (q8 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{q}}> ((W ^ (k + e)) +> (q8 ys) +> r)))
    {t k : ℕ} {xs : qv} {c c' : RMConfig}
    (h : qC q [1,0,1] t k xs c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qC at h
  split_ifs at h with hq
  have hq_eq : c.state=q:=beq_iff_eq.mp hq
  rw [← qV .right c]
  have hd_z : (ql .right c).dir=.right:=qa1 .right c
  have hq_z : (ql .right c).state=q:= by rw [qL,hq_eq]
  rcases hz : ql .right c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp -failIfUnchanged only at hd_z hq_z h
  subst hd_z hq_z
  cases hl0 : Runs.remove_word 16 ([1,0,1] : List (Fin 2)).reverse l with
  | none => rw [hl0] at h; contradiction
  | some l0 =>
    rw [hl0] at h
    cases hr0 : Runs.remove_exact W k r with
    | none => rw [hr0] at h; contradiction
    | some r0 =>
      rw [hr0] at h
      cases hb : qZ t xs with
      | none => rw [hb] at h; contradiction
      | some eys =>
        rcases eys with ⟨e,ys⟩
        rw [hb] at h
        dsimp -failIfUnchanged only at h
        split_ifs at h with hz0
        cases hrc : qi xs r0 with
        | none => rw [hrc] at h; contradiction
        | some r1 =>
          rw [hrc] at h
          simp only [strictNat_eq,strictRuns_eq] at h
          injection h with hc'; subst hc'
          unfold RMConfig.denote
          dsimp -failIfUnchanged only
          have hl_den : Runs.denote l=[1,0,1] +> default:= by
            rw [Runs.remove_word_spec hl0,Runs.zeros_spec hz0]
            rfl
          rw [hl_den,Runs.push_spec,qU,Runs.remove_exact_spec hr0,qF hrc]
          exact hrule t xs e ys k (Runs.denote r1) hb
def periodic (w : List (Fin 2)) (r : Runs) : Bool :=
  match (match r with
    | (x,nx) :: (v,_) :: _ => if nx == 1 then (x,v) else ([],x)
    | (v,_) :: _ => ([],v)
    | [] => ([],[])) with
  | (x, v) =>
    q4 (qGcd 8 w.length v.length) (fun g =>
      q4 (w.length / g) (fun a =>
        q4 (v.length / g) (fun b =>
          (x ++ v ^ a) == (w ^ b ++ x))))
def match_digit (v : List (Fin 2)) : Option Digit :=
  if v == [0,1] then some .D0
  else if v == [1,1,1,1] then some .D1
  else if v == [0,1,1,1,1,1] then some .D2
  else if v == [1,1,1,1,1,1,1,1] then some .D3
  else if v == [0,1,1,1,1,1,1,1,1,1] then some .D4
  else if v == [1,1,1,1,1,1,1,1,1,1,1,1] then some .D5
  else none
def cannot_start_W (r : Runs) : Bool :=
  match r with
  | [] => true
  | (v, _) :: rest =>
    if v == [0,1] || v == [0,1,1,1,1,1] || v == [0,1,1,1,1,1,1,1,1,1] ||
       v == [1,1,1,1,1,1,1,1] || v == [1,1,1,1,1,1,1,1,1,1,1,1] then true
    else if v == [1] then rest.isEmpty
    else if v == [1,1,1,1] then
      match rest with
      | (w2, n2) :: _ => w2 == W && 0 < n2
      | [] => true
    else false
def qf : ℕ → List (Fin 2) → Runs → ℕ × Runs
  | 0,_,r => (0,r)
  | fuel + 1,w,r =>
    match r with
    | [] => (0,[])
    | (v,m) :: ys =>
      if w == v then
        if w == W && cannot_start_W ys then (m,ys)
        else
          match qf fuel w ys with
          | (n,s') => q4 (m + n) (fun kn => (kn,s'))
      else if w == W && cannot_start_W r then (0,r)
      else
        match (if periodic w r then q4 (Runs.size (r.take 2)) (fun sz => Runs.skip w sz r) else none) with
        | some (k,s) =>
          match qf fuel w s with
          | (n,s') => q4 (k + n) (fun kn => (kn,s'))
        | none =>
          match Runs.remove_word 16 w r with
          | some s =>
            match qf fuel w s with
            | (n,s') => q4 (1 + n) (fun n1 => (n1,s'))
          | none => (0,r)
def first_bad : ℕ → Digit → ℕ → ℕ
  | 0,_,_ => 1
  | fuel + 1,p,n =>
    if take p ≤ n then 1 + first_bad fuel (next p) (n - take p) else 1
def unsafe_bound (p : Digit) (n : ℕ) : ℕ :=
  q4 (n / 2) (fun q =>
    q4 (n % 2) (fun r =>
      q4 (first_bad 6 p r) (fun fb =>
        6 * q + fb)))
def choose_opt_slow (r : Runs) : Option (Digit × ℕ × Runs) :=
  match Runs.pop r with
  | (b,r1) =>
    if b == 0 then
      match Runs.remove_word 16 [1] r1 with
      | none => none
      | some r_d0 =>
        match qf 32 W r_d0 with
        | (n0,rt0) =>
          if 0 < n0 then some (.D0,n0,rt0)
          else match Runs.remove_word 16 [1,1,1,1] r_d0 with
            | none => some (.D0,0,r_d0)
            | some r_d2 =>
              match qf 32 W r_d2 with
              | (n2,rt2) =>
                if 0 < n2 then some (.D2,n2,rt2)
                else match Runs.remove_word 16 [1,1,1,1] r_d2 with
                  | none => some (.D2,0,r_d2)
                  | some r_d4 =>
                    match qf 32 W r_d4 with
                    | (n4,rt4) => some (.D4,n4,rt4)
    else
      match Runs.remove_word 16 [1,1,1] r1 with
      | none => none
      | some r_d1 =>
        match qf 32 W r_d1 with
        | (n1,rt1) =>
          if 0 < n1 then some (.D1,n1,rt1)
          else match Runs.remove_word 16 [1,1,1,1] r_d1 with
            | none => some (.D1,0,r_d1)
            | some r_d3 =>
              match qf 32 W r_d3 with
              | (n3,rt3) =>
                if 0 < n3 then some (.D3,n3,rt3)
                else match Runs.remove_word 16 [1,1,1,1] r_d3 with
                  | none => some (.D3,0,r_d3)
                  | some r_d5 =>
                    match qf 32 W r_d5 with
                    | (n5,rt5) => some (.D5,n5,rt5)
def choose_opt (r : Runs) : Option (Digit × ℕ × Runs) :=
  match r with
  | (v, 1) :: (w, n) :: rest =>
    if w == W && 0 < n && cannot_start_W rest then
      match match_digit v with
      | some d => some (d, n, rest)
      | none => choose_opt_slow r
    else choose_opt_slow r
  | _ => choose_opt_slow r
def qq : ℕ → Runs → Option ℕ → ℕ × qv
  | 0,_,_ => (0,[])
  | fuel + 1,r,cap =>
    match choose_opt r with
    | none => (0,[])
    | some (p,n,r2) =>
      q4 (unsafe_bound p n - 1) (fun t0 =>
        q4 (match cap with | none => t0 | some u => min t0 u) (fun t =>
          q4 ((t + p.index) / 6) (fun child =>
            if child == 0 then (t,[(p,n)])
            else
              match qq fuel r2 (some child) with
              | (u,xs) =>
                q4 (min t (6 * u + 5 - p.index)) (fun t' =>
                  (t',(p,n) :: xs)))))
def qK (c : RMConfig) : Option (ℕ × ℕ × qv) :=
  let z:=ql .right c
  match qf 32 W z.right with
  | (k,r2) =>
    match qq 32 r2 none with
    | (t,xs) => if t == 0 then none else some (t,k,xs)
def qY (q : Fin 6) (c : RMConfig) : Option RMConfig :=
  match qK c with
  | some (t,k,xs) => qC q [1,0,1] t k xs c
  | none => none
lemma qa0 {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hrule : ∀ t xs e ys k r,qZ t xs=some (e,ys) →
      (([1,0,1] +> default) {{q}}> ((W ^ k) +> (q8 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{q}}> ((W ^ (k + e)) +> (q8 ys) +> r)))
    {c c' : RMConfig} (h : qY q c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qY at h
  cases hp : qK c with
  | none => rw [hp] at h; contradiction
  | some tkx =>
    rcases tkx with ⟨t,k,xs⟩
    rw [hp] at h
    exact qP hrule h
def qe (s : Scan) (keep : ℕ) (c : RMConfig) : Option RMConfig :=
  let z:=ql s.dir c
  let w:=match s.dir with | .left => s.scan_in.reverse | .right => s.scan_in
  let src:=match s.dir with | .left => z.left | .right => z.right
  q4 ((qf 32 w src).1 - keep) (fun n => use_scan s n c)
lemma q9 {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {keep : ℕ} {c c' : RMConfig}
    (hv : q7 tm s) (h : qe s keep c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qe at h
  simp only [strictNat_eq] at h
  exact use_scan_spec hv h
def qX (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q,⟨c.tape.1,c.tape.right,c.tape.left⟩⟩
lemma qH (c : Cfg (Fin 2) (Fin 6)) :
    step holdout_0491_tm (qX c)=(step qc c).map qX:= by
  rcases c with ⟨_ | ⟨q,hq⟩,⟨⟨b,hb⟩,l,r⟩⟩
  · rfl
  · rcases q with _ | _ | _ | _ | _ | _ | q <;> try omega
    all_goals (rcases b with _ | _ | b <;> first | omega | rfl)
lemma qG (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep holdout_0491_tm (qX c) n=(multiStep qc c n).map qX:= by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiStep_succ,multiStep_succ,ih]
    cases multiStep qc c n with
    | none => rfl
    | some c' => simp [qH]
lemma qW (h : IsHalt qc) : IsHalt holdout_0491_tm:= by
  rcases h with ⟨cfg,⟨n,hn⟩,hnone⟩
  refine ⟨qX cfg,⟨n,?_⟩,?_⟩
  · have h1:=qG (init []) n
    rw [hn] at h1
    exact h1
  · rw [qH,Option.isNone_map]
    exact hnone
lemma wall_1 : q2 qc C 1 1 W W:= by
  apply qJ (w_mid:=[1,0,1,1,0,0,1,1,0,1])
  · intro l r; dsimp -failIfUnchanged [W,ListBlank.append]; execute90
  · intro l r; dsimp -failIfUnchanged [W,ListBlank.append]; execute90
lemma inc0 : q2 qc C 1 0 (qo .D0) (qo .D1):= by
  apply qk
  intro l r; dsimp -failIfUnchanged [qo,ListBlank.append]; execute90
lemma inc1 : q2 qc C 1 0 (qo .D1 ++ W) (W ++ qo .D2):= by
  apply qk
  intro l r; dsimp -failIfUnchanged [qo,W,ListBlank.append]; execute90
lemma inc2 : q2 qc C 1 0 (qo .D2) (qo .D3):= by
  apply qk
  intro l r; dsimp -failIfUnchanged [qo,ListBlank.append]; execute90
lemma inc3 : q2 qc C 1 0 (qo .D3 ++ W) (W ++ qo .D4):= by
  apply qk
  intro l r; dsimp -failIfUnchanged [qo,W,ListBlank.append]; execute90
lemma inc4 : q2 qc C 1 0 (qo .D4) (qo .D5):= by
  apply qk
  intro l r; dsimp -failIfUnchanged [qo,ListBlank.append]; execute90
lemma inc5 : q2 qc C 1 1 (qo .D5) (W ++ qo .D0):= by
  apply qJ (w_mid:=[1,0,1,1,0,1,1,0,1,1,0,1])
  · intro l r; dsimp -failIfUnchanged [qo,W,ListBlank.append]; execute90
  · intro l r; dsimp -failIfUnchanged [qo,W,ListBlank.append]; execute90
lemma one (p : Digit) (n : ℕ) :
    q2 qc C 1 (qO p)
      (qo p ++ W ^ (take p + n))
      (W ^ (give p) ++ qo (next p) ++ W ^ n):= by
  cases p
  · dsimp -failIfUnchanged only [take,give,qO,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q5 inc0 (qh qc C (W ^ n))
  · dsimp -failIfUnchanged only [take,give,qO,next]
    have h:=q5 inc1 (qh qc C (W ^ n))
    have h1 : 1 + n=n + 1:= by omega
    rw [h1,pow_succ_list,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
  · dsimp -failIfUnchanged only [take,give,qO,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q5 inc2 (qh qc C (W ^ n))
  · dsimp -failIfUnchanged only [take,give,qO,next]
    have h:=q5 inc3 (qh qc C (W ^ n))
    have h1 : 1 + n=n + 1:= by omega
    rw [h1,pow_succ_list,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
  · dsimp -failIfUnchanged only [take,give,qO,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q5 inc4 (qh qc C (W ^ n))
  · dsimp -failIfUnchanged only [take,give,qO,next]
    have h:=q5 inc5 (wall_n wall_1 n)
    rw [Nat.zero_add,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
lemma emit (r : ListBlank (Fin 2)) :
    (default <{{C}} ([1] +> r)) [qc]⊢* (([1,0,1] +> default) {{C}}> r):= by
  dsimp -failIfUnchanged [ListBlank.append]; execute90
lemma batch_step (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (k : ℕ) (r : ListBlank (Fin 2))
    (h : qZ t xs=some (e,ys)) :
    (([1,0,1] +> default) {{C}}> ((W ^ k) +> (q8 xs) +> r)) [qc]⊢*
    (([1,0,1] +> default) {{C}}> ((W ^ (k + e)) +> (q8 ys) +> r)) :=
  batch_root emit wall_1 one t xs e ys k r h
def scan_0 : Scan:=⟨E,.left,[0,1,1,0,0,1,1,0,1,1],[1,1,1,1,0,1,1,1,1,1],[]⟩
lemma scan_0_valid : q7 qc scan_0:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_0,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_1 : Scan:=⟨D,.left,[1,0,1,1,0,0,1,1,0,1],[1,1,1,1,1,0,1,1,1,1],[0,1,0]⟩
lemma scan_1_valid : q7 qc scan_1:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_1,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_2 : Scan:=⟨A,.left,[1,1,0,1,1,0,0,1,1,0],[1,1,1,1,0,1,1,1,1,1],[0,1]⟩
lemma scan_2_valid : q7 qc scan_2:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_2,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_3 : Scan:=⟨D,.right,[1,1,0,1,1,1,1,1,1,1],[0,0,1,1,0,1,1,0,1,1],[0]⟩
lemma scan_3_valid : q7 qc scan_3:= by
  apply qI rfl
  intro l r; dsimp -failIfUnchanged [scan_3,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_4 : Scan:=⟨E,.left,[0,1,1,0,1,1],[1,1,1,1,0,1],[]⟩
lemma scan_4_valid : q7 qc scan_4:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_4,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_5 : Scan:=⟨D,.left,[1,0,1,1,0,1],[1,0,1,1,1,1],[0]⟩
lemma scan_5_valid : q7 qc scan_5:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_5,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_6 : Scan:=⟨A,.left,[1,1,0,1,1,0],[0,1,1,1,1,1],[]⟩
lemma scan_6_valid : q7 qc scan_6:= by
  apply qg rfl
  intro l r; dsimp -failIfUnchanged [scan_6,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_7 : Scan:=⟨D,.right,[1,1,1],[0,1,1],[0]⟩
lemma scan_7_valid : q7 qc scan_7:= by
  apply qI rfl
  intro l r; dsimp -failIfUnchanged [scan_7,List.reverse,List.reverseAux,ListBlank.append]; execute90
def run_raw (tm : Machine (Fin 2) (Fin 6)) : ℕ → RMConfig → Option RMConfig
  | 0,c => some c
  | n + 1,c =>
    match RM.raw tm c with
    | some c' => run_raw tm n c'
    | none => none
lemma run_raw_spec {n : ℕ} {c c' : RMConfig}
    (h : run_raw qc n c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold run_raw at h
    cases hr : RM.raw qc c with
    | none => rw [hr] at h; contradiction
    | some c₁ =>
      rw [hr] at h
      exact q0 (RM.raw_spec hr) (ih h)
def qs (op arg : ℕ) (c : RMConfig) : Option RMConfig :=
  match op with
  | 0 => run_raw qc arg c
  | 1 => qY C c
  | 2 => qe scan_0 arg c
  | 3 => qe scan_1 arg c
  | 4 => qe scan_2 arg c
  | 5 => qe scan_3 arg c
  | 6 => qe scan_4 arg c
  | 7 => qe scan_5 arg c
  | 8 => qe scan_6 arg c
  | 9 => qe scan_7 arg c
  | _ => none
lemma qp {op arg : ℕ} {c c' : RMConfig}
    (h : qs op arg c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  unfold qs at h
  rcases op with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | op
  · exact run_raw_spec h
  · exact qa0 batch_step h
  · exact q9 scan_0_valid h
  · exact q9 scan_1_valid h
  · exact q9 scan_2_valid h
  · exact q9 scan_3_valid h
  · exact q9 scan_4_valid h
  · exact q9 scan_5_valid h
  · exact q9 scan_6_valid h
  · exact q9 scan_7_valid h
  · contradiction
def qR : ℕ → ℕ → ℕ → RMConfig → Option RMConfig
  | 0,_,_,c => some c
  | n + 1,op,arg,c =>
    match qs op arg c with
    | some c' => qR n op arg c'
    | none => none
lemma run_rep1_spec {n op arg : ℕ} {c c' : RMConfig}
    (h : qR n op arg c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold qR at h
    cases ho : qs op arg c with
    | none => rw [ho] at h; contradiction
    | some c₁ =>
      rw [ho] at h
      exact q0 (qp ho) (ih h)
def qQ : ℕ → ℕ → ℕ → ℕ → ℕ → RMConfig → Option RMConfig
  | 0,_,_,_,_,c => some c
  | n + 1,op1,arg1,op2,arg2,c =>
    match qs op1 arg1 c with
    | some c₁ =>
      match qs op2 arg2 c₁ with
      | some c₂ => qQ n op1 arg1 op2 arg2 c₂
      | none => none
    | none => none
lemma run_rep2_spec {n op1 arg1 op2 arg2 : ℕ} {c c' : RMConfig}
    (h : qQ n op1 arg1 op2 arg2 c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold qQ at h
    cases ho1 : qs op1 arg1 c with
    | none => rw [ho1] at h; contradiction
    | some c₁ =>
      rw [ho1] at h; dsimp -failIfUnchanged only at h
      cases ho2 : qs op2 arg2 c₁ with
      | none => rw [ho2] at h; contradiction
      | some c₂ =>
        rw [ho2] at h; dsimp -failIfUnchanged only at h
        exact q0 (qp ho1) (q0 (qp ho2) (ih h))

def norm_qv : qv → qv
  | [] => []
  | (p, n) :: rest =>
    let rest' := norm_qv rest
    if n == 0 then
      match p, rest' with
      | .D1, (.D1, n2) :: tail => (.D3, n2) :: tail
      | .D1, (.D3, n2) :: tail => (.D5, n2) :: tail
      | .D3, (.D1, n2) :: tail => (.D5, n2) :: tail
      | .D1, (.D5, n2) :: tail => (.D5, 0) :: (.D1, n2) :: tail
      | .D3, (.D3, n2) :: tail => (.D5, 0) :: (.D1, n2) :: tail
      | .D3, (.D5, n2) :: tail => (.D5, 0) :: (.D3, n2) :: tail
      | _, _ => (p, 0) :: rest'
    else (p, n) :: rest'

lemma norm_qv_spec (xs : qv) : q8 (norm_qv xs) = q8 xs := by
  induction xs with
  | nil => rfl
  | cons pn rest ih =>
    rcases pn with ⟨p, n⟩
    unfold norm_qv
    dsimp -failIfUnchanged only
    split_ifs with hn0
    · have hn : n = 0 := beq_iff_eq.mp hn0
      subst hn
      rcases hrest : norm_qv rest with _ | ⟨⟨p2, n2⟩, tail⟩
      · simp [q8, ← ih, hrest]
      · cases p <;> cases p2 <;>
        simp [q8, qo, pow_zero_list, List.append_assoc, ← ih, hrest]
    · simp [q8, ih]

def qZ_fast : ℕ → qv → Option (ℕ × qv)
  | t, [] => if t == 0 then some (0, []) else none
  | t, (p, n) :: xs =>
    if t == 0 then some (0, (p, n) :: xs)
    else
      match qy p t with
      | ⟨ph, u, g, s⟩ =>
        if u ≤ n then
          match qZ_fast s xs with
          | some (e, ys) =>
            q4 (n - u + e) (fun m =>
              some (g, (ph, m) :: ys))
          | none => none
        else none

lemma qZ_fast_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n, q2 tm q 1 (qO p) (qo p ++ W ^ (take p + n)) (W ^ (give p) ++ qo (next p) ++ W ^ n))
    (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (h : qZ_fast t xs = some (e, ys)) :
    q2 tm q t 0 (q8 xs) (W ^ e ++ q8 ys) := by
  induction xs generalizing t e ys with
  | nil =>
    unfold qZ_fast at h
    split_ifs at h with ht
    injection h with hpair; injection hpair with he hys; subst he hys
    have ht0 : t = 0 := beq_iff_eq.mp ht; subst ht0
    exact qh tm q []
  | cons pn xs ih =>
    rcases pn with ⟨p, n⟩
    unfold qZ_fast at h
    dsimp -failIfUnchanged only at h
    split_ifs at h with ht hle
    · injection h with hpair; injection hpair with he hys; subst he hys
      have ht0 : t = 0 := beq_iff_eq.mp ht; subst ht0
      simpa using qh tm q (q8 ((p, n) :: xs))
    · cases hb : qZ_fast (qy p t).sent xs with
      | none => rw [hb] at h; contradiction
      | some eys =>
        rcases eys with ⟨e', ys'⟩
        rw [hb] at h
        simp only [strictNat_eq] at h
        injection h with hpair; injection hpair with he hys; subst he hys
        have h1 := totalN_rule hwall1 hone p t n hle
        have h2 := ih (qy p t).sent e' ys' hb
        have h3 := q5 h1 h2
        simpa only [q8, qb, List.append_assoc] using h3

lemma batch_fast_step (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (k : ℕ) (r : ListBlank (Fin 2))
    (h : qZ_fast t xs = some (e, ys)) :
    (([1,0,1] +> default) {{C}}> ((W ^ k) +> (q8 xs) +> r)) [qc]⊢*
    (([1,0,1] +> default) {{C}}> ((W ^ (k + e)) +> (q8 ys) +> r)) := by
  apply calls_spec emit t
  have hw := walls wall_1 t k
  have hb := qZ_fast_spec wall_1 one t xs e ys h
  have hc := q5 hw hb r r rfl
  simpa only [qb, List.append_assoc, append_assoc] using hc

def qZ_many : List ℕ → ℕ → qv → Option (ℕ × qv)
  | [], k, xs => some (k, xs)
  | t :: ts, k, xs =>
    match qZ_fast t xs with
    | some (e, ys) => q4 (k + e) (fun k' => qZ_many ts k' (norm_qv ys))
    | none => none

lemma qZ_many_spec (ts : List ℕ) (k : ℕ) (xs : qv) (ke : ℕ) (ys : qv) (r : ListBlank (Fin 2))
    (h : qZ_many ts k xs = some (ke, ys)) :
    (([1,0,1] +> default) {{C}}> ((W ^ k) +> (q8 xs) +> r)) [qc]⊢*
    (([1,0,1] +> default) {{C}}> ((W ^ ke) +> (q8 ys) +> r)) := by
  induction ts generalizing k xs with
  | nil =>
    unfold qZ_many at h
    injection h with hpair; injection hpair with hke hys; subst hke hys
    exact ⟨0, rfl⟩
  | cons t ts ih =>
    unfold qZ_many at h
    cases hb : qZ_fast t xs with
    | none => rw [hb] at h; contradiction
    | some eys =>
      rcases eys with ⟨e, ys1⟩
      rw [hb] at h
      simp only [strictNat_eq] at h
      have h1 := batch_fast_step t xs e ys1 k r hb
      have h2 := ih (k + e) (norm_qv ys1) h
      rw [norm_qv_spec] at h2
      exact q0 h1 h2

def qC_many (q : Fin 6) (u : List (Fin 2)) (ts : List ℕ) (k : ℕ) (xs : qv) (c : RMConfig) : Option RMConfig :=
  if c.state == q then
    let z := ql .right c
    match Runs.remove_word 16 u.reverse z.left, Runs.remove_exact W k z.right, qZ_many ts k xs with
    | some l0, some r0, some (ke, ys) =>
      if Runs.zeros l0 then
        match qi xs r0 with
        | some r1 =>
          q3 (qw ys r1) (fun r2 =>
            q3 (Runs.push W ke r2) (fun r3 =>
              some ⟨z.left, r3, q, .right⟩))
        | none => none
      else none
    | _, _, _ => none
  else none

lemma qP_many {ts : List ℕ} {k : ℕ} {xs : qv} {c c' : RMConfig}
    (h : qC_many C [1,0,1] ts k xs c = some c') :
    (c.denote) [qc]⊢* (c'.denote) := by
  unfold qC_many at h
  split_ifs at h with hq
  have hq_eq : c.state = C := beq_iff_eq.mp hq
  rw [← qV .right c]
  have hd_z : (ql .right c).dir = .right := qa1 .right c
  have hq_z : (ql .right c).state = C := by rw [qL, hq_eq]
  rcases hz : ql .right c with ⟨l, r, qz, dz⟩
  rw [hz] at hd_z hq_z h
  dsimp -failIfUnchanged only at hd_z hq_z h
  subst hd_z hq_z
  cases hl0 : Runs.remove_word 16 ([1,0,1] : List (Fin 2)).reverse l with
  | none => rw [hl0] at h; contradiction
  | some l0 =>
    rw [hl0] at h
    cases hr0 : Runs.remove_exact W k r with
    | none => rw [hr0] at h; contradiction
    | some r0 =>
      rw [hr0] at h
      cases hb : qZ_many ts k xs with
      | none => rw [hb] at h; contradiction
      | some keys =>
        rcases keys with ⟨ke, ys⟩
        rw [hb] at h
        dsimp -failIfUnchanged only at h
        split_ifs at h with hz0
        cases hrc : qi xs r0 with
        | none => rw [hrc] at h; contradiction
        | some r1 =>
          rw [hrc] at h
          simp only [strictNat_eq, strictRuns_eq] at h
          injection h with hc'; subst hc'
          unfold RMConfig.denote
          dsimp -failIfUnchanged only
          have hl_den : Runs.denote l = [1,0,1] +> default := by
            rw [Runs.remove_word_spec hl0, Runs.zeros_spec hz0]
            rfl
          rw [hl_den, Runs.push_spec, qU, Runs.remove_exact_spec hr0, qF hrc]
          exact qZ_many_spec ts k xs ke ys (Runs.denote r1) hb

def Runs.toList : Runs → List (Fin 2)
  | [] => []
  | (w, n) :: xs => w ^ n ++ Runs.toList xs

def Runs.push_runs : Runs → Runs → Runs
  | [], ys => ys
  | (w, n) :: xs, ys => q3 (Runs.push_runs xs ys) (fun zs => Runs.push w n zs)

lemma Runs.push_runs_spec (xs ys : Runs) :
    Runs.denote (Runs.push_runs xs ys) = Runs.toList xs +> Runs.denote ys := by
  induction xs with
  | nil => rfl
  | cons wn xs ih =>
    rcases wn with ⟨w, n⟩
    simp only [Runs.push_runs, Runs.toList, strictRuns_eq, Runs.push_spec, ih, append_assoc]

structure MacroRule where
  q1 : Fin 6
  d1 : Dir
  l_in : List (Fin 2)
  r_in : List (Fin 2)
  q2 : Fin 6
  d2 : Dir
  l_out : Runs
  r_out : Runs

abbrev cfg_of := @Counter.cfg_of (Fin 2) (Fin 6)

def MacroRule.Valid (tm : Machine (Fin 2) (Fin 6)) (m : MacroRule) : Prop :=
  ∀ (l r : ListBlank (Fin 2)),
    (cfg_of m.q1 m.d1 (m.l_in +> l) (m.r_in +> r)) [tm]⊢*
    (cfg_of m.q2 m.d2 (Runs.toList m.l_out +> l) (Runs.toList m.r_out +> r))

abbrev LocalState := Counter.LocalState (Fin 2) (Fin 6)
abbrev step_local := @Counter.step_local (Fin 2) (Fin 6)
abbrev step_local_spec := @Counter.step_local_spec (Fin 2) (Fin 6) _ _
abbrev run_local := @Counter.run_local (Fin 2) (Fin 6)
abbrev run_local_spec := @Counter.run_local_spec (Fin 2) (Fin 6) _ _

lemma check_macro_spec {tm : Machine (Fin 2) (Fin 6)} {n : ℕ} {m : MacroRule}
    (h : run_local tm n ⟨m.l_in, m.r_in, m.q1, m.d1⟩ = some ⟨Runs.toList m.l_out, Runs.toList m.r_out, m.q2, m.d2⟩) :
    MacroRule.Valid tm m := by
  intro L R
  exact run_local_spec h L R

def apply_macro (m : MacroRule) (c : RMConfig) : Option RMConfig :=
  if c.state == m.q1 then
    let z := ql m.d1 c
    match Runs.remove_word 16 m.l_in z.left, Runs.remove_word 16 m.r_in z.right with
    | some l', some r' =>
      q3 (Runs.push_runs m.l_out l') (fun l1 =>
        q3 (Runs.push_runs m.r_out r') (fun r1 =>
          some ⟨l1, r1, m.q2, m.d2⟩))
    | _, _ => none
  else none

lemma apply_macro_spec {tm : Machine (Fin 2) (Fin 6)} {m : MacroRule} {c c' : RMConfig}
    (hv : MacroRule.Valid tm m) (h : apply_macro m c = some c') :
    (c.denote) [tm]⊢* (c'.denote) := by
  unfold apply_macro at h
  split_ifs at h with hq
  have hq_eq : c.state = m.q1 := beq_iff_eq.mp hq
  rw [← qV m.d1 c]
  have hd_z : (ql m.d1 c).dir = m.d1 := qa1 m.d1 c
  have hq_z : (ql m.d1 c).state = m.q1 := by rw [qL, hq_eq]
  rcases hz : ql m.d1 c with ⟨l, r, qz, dz⟩
  rw [hz] at hd_z hq_z h
  dsimp -failIfUnchanged only at hd_z hq_z h
  subst hd_z hq_z
  cases hl : Runs.remove_word 16 m.l_in l with
  | none => rw [hl] at h; contradiction
  | some l' =>
    rw [hl] at h
    cases hr : Runs.remove_word 16 m.r_in r with
    | none => rw [hr] at h; contradiction
    | some r' =>
      rw [hr] at h
      simp only [strictRuns_eq] at h
      injection h with hc'; subst hc'
      have h_lhs : (RMConfig.mk l r m.q1 m.d1).denote = cfg_of m.q1 m.d1 (m.l_in +> Runs.denote l') (m.r_in +> Runs.denote r') := by
        cases m.d1 <;> simp [RMConfig.denote, cfg_of, Counter.cfg_of, Runs.remove_word_spec hl, Runs.remove_word_spec hr]
      have h_rhs : (RMConfig.mk (Runs.push_runs m.l_out l') (Runs.push_runs m.r_out r') m.q2 m.d2).denote =
          cfg_of m.q2 m.d2 (Runs.toList m.l_out +> Runs.denote l') (Runs.toList m.r_out +> Runs.denote r') := by
        cases m.d2 <;> simp [RMConfig.denote, cfg_of, Counter.cfg_of, Runs.push_runs_spec]
      rw [h_lhs, h_rhs]
      exact hv (Runs.denote l') (Runs.denote r')

def macro_10 : MacroRule := ⟨D, .right, [0,1,1,0,1], [1,0], D, .left, [], [([0,1,0],1),([1],4)]⟩
lemma macro_10_valid : MacroRule.Valid qc macro_10 := check_macro_spec (n := 10) (by decide +kernel)

def macro_20 : MacroRule := ⟨D, .left, [1,0,1,1,0,1,1,0,1,1,0,1], [0], D, .left, [], [([0,1,0],1),([1,1,1,1,1,0,1,1,1,1],1)]⟩
lemma macro_20_valid : MacroRule.Valid qc macro_20 := check_macro_spec (n := 20) (by decide +kernel)

def macro_50 : MacroRule := ⟨C, .right, [1,0], [1,1,1,1,0,1,1,1,1,1,1,1], D, .right, [([0],1),([1,1,0,1,1,0,1,1,0,0],1),([1,1,0],1)], []⟩
lemma macro_50_valid : MacroRule.Valid qc macro_50 := check_macro_spec (n := 50) (by decide +kernel)

def macro_339 : MacroRule := ⟨D, .left, [1,0,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,0,1,1,0,1,1,0,0,1,1,0,1,0,0,0], [0,1,0], C, .right, [([1],1),([0],1),([1],1)], [([0,1],1),([0,1,1,1,1,1],2),(W,4),([1,1,1,1,0,1,1,1,1],1)]⟩
lemma macro_339_valid : MacroRule.Valid qc macro_339 := check_macro_spec (n := 339) (by decide +kernel)

def run_raw_fast (n : ℕ) (c : RMConfig) : Option RMConfig :=
  if n == 20 then apply_macro macro_20 c
  else if n == 50 then apply_macro macro_50 c
  else if n == 339 then apply_macro macro_339 c
  else if n == 10 then apply_macro macro_10 c
  else run_raw qc n c

lemma run_raw_fast_spec {n : ℕ} {c c' : RMConfig}
    (h : run_raw_fast n c = some c') :
    (c.denote) [qc]⊢* (c'.denote) := by
  unfold run_raw_fast at h
  split_ifs at h
  · exact apply_macro_spec macro_20_valid h
  · exact apply_macro_spec macro_50_valid h
  · exact apply_macro_spec macro_339_valid h
  · exact apply_macro_spec macro_10_valid h
  · exact run_raw_spec h

def qs_direct (op n : ℕ) (c : RMConfig) : Option RMConfig :=
  match op with
  | 0 => run_raw_fast n c
  | 2 => use_scan scan_0 n c
  | 3 => use_scan scan_1 n c
  | 4 => use_scan scan_2 n c
  | 5 => use_scan scan_3 n c
  | 6 => use_scan scan_4 n c
  | 7 => use_scan scan_5 n c
  | 8 => use_scan scan_6 n c
  | 9 => use_scan scan_7 n c
  | _ => none

lemma qs_direct_spec {op n : ℕ} {c c' : RMConfig}
    (h : qs_direct op n c = some c') :
    (c.denote) [qc]⊢* (c'.denote) := by
  unfold qs_direct at h
  rcases op with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | op
  · exact run_raw_fast_spec h
  · contradiction
  · exact use_scan_spec scan_0_valid h
  · exact use_scan_spec scan_1_valid h
  · exact use_scan_spec scan_2_valid h
  · exact use_scan_spec scan_3_valid h
  · exact use_scan_spec scan_4_valid h
  · exact use_scan_spec scan_5_valid h
  · exact use_scan_spec scan_6_valid h
  · exact use_scan_spec scan_7_valid h
  · contradiction

def qQ_direct (op1 op2 : ℕ) : List (ℕ × ℕ) → RMConfig → Option RMConfig
  | [], c => some c
  | (n1, n2) :: rest, c =>
    match qs_direct op1 n1 c with
    | some c1 =>
      match qs_direct op2 n2 c1 with
      | some c2 => qQ_direct op1 op2 rest c2
      | none => none
    | none => none

lemma qQ_direct_spec {op1 op2 : ℕ} {ns : List (ℕ × ℕ)} {c c' : RMConfig}
    (h : qQ_direct op1 op2 ns c = some c') :
    (c.denote) [qc]⊢* (c'.denote) := by
  induction ns generalizing c with
  | nil =>
    injection h with heq; subst heq; exact ⟨0, rfl⟩
  | cons p rest ih =>
    rcases p with ⟨n1, n2⟩
    unfold qQ_direct at h
    cases ho1 : qs_direct op1 n1 c with
    | none => rw [ho1] at h; contradiction
    | some c1 =>
      rw [ho1] at h; dsimp -failIfUnchanged only at h
      cases ho2 : qs_direct op2 n2 c1 with
      | none => rw [ho2] at h; contradiction
      | some c2 =>
        rw [ho2] at h; dsimp -failIfUnchanged only at h
        exact q0 (qs_direct_spec ho1) (q0 (qs_direct_spec ho2) (ih h))

inductive Cmd where
  | one (op arg : ℕ)
  | rep1 (cnt op arg : ℕ)
  | rep2 (cnt op1 arg1 op2 arg2 : ℕ)
  | batch (ts : List ℕ) (k : ℕ) (xs : qv)
  | scan (op n : ℕ)
  | scan2 (op1 op2 : ℕ) (ns : List (ℕ × ℕ))
def exec_cmd (cmd : Cmd) (c : RMConfig) : Option RMConfig :=
  match cmd with
  | .one op arg => qs op arg c
  | .rep1 cnt op arg => qR cnt op arg c
  | .rep2 cnt op1 arg1 op2 arg2 => qQ cnt op1 arg1 op2 arg2 c
  | .batch ts k xs => qC_many C [1,0,1] ts k xs c
  | .scan op n => qs_direct op n c
  | .scan2 op1 op2 ns => qQ_direct op1 op2 ns c
lemma exec_cmd_spec {cmd : Cmd} {c c' : RMConfig}
    (h : exec_cmd cmd c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  cases cmd with
  | one op arg => exact qp h
  | rep1 cnt op arg => exact run_rep1_spec h
  | rep2 cnt op1 arg1 op2 arg2 => exact run_rep2_spec h
  | batch ts k xs => exact qP_many h
  | scan op n => exact qs_direct_spec h
  | scan2 op1 op2 ns => exact qQ_direct_spec h
def q6 : List Cmd → RMConfig → Option RMConfig
  | [],c => some c
  | cmd :: rest,c =>
    match exec_cmd cmd c with
    | some c' => q6 rest c'
    | none => none
lemma q1 {cs : List Cmd} {c c' : RMConfig}
    (h : q6 cs c=some c') :
    (c.denote) [qc]⊢* (c'.denote):= by
  induction cs generalizing c with
  | nil =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | cons cmd rest ih =>
    unfold q6 at h
    cases hc : exec_cmd cmd c with
    | none => rw [hc] at h; contradiction
    | some c₁ =>
      rw [hc] at h; dsimp -failIfUnchanged only at h
      exact q0 (exec_cmd_spec hc) (ih h)
def isHalted (tm : Machine (Fin 2) (Fin 6)) (c : RMConfig) : Bool :=
  let b:=match c.dir with
    | .left => (Runs.pop c.left).1
    | .right => (Runs.pop c.right).1
  (tm c.state b).isNone
lemma isHalted_spec {c : RMConfig} (h : isHalted qc c=true) :
    (step qc c.denote).isNone:= by
  rcases c with ⟨l,r,q,d⟩
  unfold isHalted at h
  cases d
  · dsimp -failIfUnchanged only at h
    unfold RMConfig.denote step
    dsimp -failIfUnchanged only
    rw [Runs.pop_spec l,Turing.ListBlank.head_cons]
    cases htm : qc q (Runs.pop l).1 with
    | none => rfl
    | some _ => rw [htm] at h; contradiction
  · dsimp -failIfUnchanged only at h
    unfold RMConfig.denote step
    dsimp -failIfUnchanged only
    rw [Runs.pop_spec r,Turing.ListBlank.head_cons]
    cases htm : qc q (Runs.pop r).1 with
    | none => rfl
    | some _ => rw [htm] at h; contradiction
set_option maxHeartbeats 4000000
def cfg_0 : RMConfig:=⟨[],[],A,.right⟩
def cfg_1 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],14),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8),([1],3)],C,.right⟩
def cfg_2 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],241),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],53),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5),([1],3)],C,.right⟩
def cfg_3 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],647),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1107),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],264),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],25),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15),([1],3)],C,.right⟩
def cfg_4 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],2447),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9145),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5808),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],632),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],57),([1],3)],C,.right⟩
def cfg_5 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],139729),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15624),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],40628),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5261),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5160),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],524),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],33),([1],3)],C,.right⟩
def cfg_6 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],839807),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1811737),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1103222),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],232638),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],17301),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1373),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4512),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],416),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9),([1],3)],C,.right⟩
def cfg_7 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],279935),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1492283),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11819877),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],793479),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],181014),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8697),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4223),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],368),([1],3)],C,.right⟩
def cfg_8 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],13436929),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7775802),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5381133),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],652474),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11679909),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],770151),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],177126),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8049),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4115),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],344),([1],3)],C,.right⟩
def cfg_9 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],451477011),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],21742666),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],16636277),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],57393613),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1208971),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11528278),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],744879),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],172914),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7347),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3998),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],318),([1],3)],C,.right⟩
def cfg_10 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],2734414851),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1842187633),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],126986568),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],229349196),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],52354765),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],369163),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11388310),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],721551),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],169026),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6699),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3890),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],294),([1],3)],C,.right⟩
def cfg_11 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],2902376449),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1988686442),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15670412907),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1277209393),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],32823528),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],213655356),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],49739125),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11260007),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],700167),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],165462),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6105),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3791),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],272),([1],3)],C,.right⟩
def cfg_12 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],11913785351),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],98528659453),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],43845250986),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9080552433),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14474075415),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1077819811),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],207776700),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],48759349),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11096711),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],672951),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],160926),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5349),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3665),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],244),([1],3)],C,.right⟩
def cfg_13 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],626913312769),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],243867188622),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13026910521),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],65876924410),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],38403295146),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8173559793),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14322909975),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1052625571),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],203577660),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],48059509),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10980071),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],653511),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],157686),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4809),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3575),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],224),([1],3)],C,.right⟩
def cfg_14 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],17145729646246),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],505981945839),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1037065005185),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2777645236624),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],23429668859),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],31328752554),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6994469361),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14126394903),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1019873059),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],198118908),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],47149717),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10828439),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],628239),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],153474),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4107),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3458),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],198),([1],3)],C,.right⟩
def cfg_15 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],90752743557389),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],110070725690864),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],37325785004977),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5644560578121),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9105470814445),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],118673488085),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2624579983774),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],25342601129),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5996777457),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13960112919),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],992159395),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],193499964),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],46379893),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10700135),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],606855),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],149910),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3513),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3359),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],176),([1],3)],C,.right⟩
def cfg_16 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],4592766929338371),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],123825256253571),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],306313064936501),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],364891287778978),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6795949950050),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],556254735633),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8257419840697),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2582132728221),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],18268058537),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4817687025),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13763597847),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],959406883),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],188041212),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],45470101),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10548503),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],581583),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],145698),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2811),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3242),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],150),([1],3)],C,.right⟩
def cfg_17 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],4874877920083969),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],25556429845487524),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1709142197372564),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3068205663580327),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],155407234188137),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],339740315987584),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2604121318151),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8022327348409),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2542950646173),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11737711529),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3729295857),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13582199319),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],929173795),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],183002364),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],44630293),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10408535),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],558255),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],141810),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2163),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3134),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],126),([1],3)],C,.right⟩
def cfg_18 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],22993523763921719),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],51981972515675869),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],146293703117781586),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15182639638593206),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2763525793575078),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],104627255853929),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],331276986265216),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1193566364423),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7787234856121),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2503768564125),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5207364521),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2640904689),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13400800791),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],898940707),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],177963516),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],43790485),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10268567),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],534927),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],137922),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1515),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3026),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],102),([1],3)],C,.right⟩
def cfg_19 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],29249267520503809),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],813965834913967086),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],604654236871710051),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],137176979921917522),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13663185772615862),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2510283482578854),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],62420204021225),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],324242477626432),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],21148257959),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7591831838377),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2471201394501),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1552513520),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13219402263),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],868707619),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],172924668),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],42950677),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10128599),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],511599),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],134034),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],867),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2918),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],78),([1],3)],C,.right⟩
def cfg_20 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],227527202966565959),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],878274055253804511),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],22084482590786306),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],798063893976589425),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],602003913382147107),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136735259340323698),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13589565675683558),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2498013466423470),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],60375201328661),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],323901643844338),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7552649756328),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2464671047493),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],464122352),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13038003735),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],838474531),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],167885820),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],42110869),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9988631),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],488271),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],130146),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],219),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2810),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],54),([1],3)],C,.right⟩
def cfg_21 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],5768519355599781893),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],327824879050489010),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1568295479115420465),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],21594293168954344),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],739226421390733018),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],793293023825066099),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],601208768356893219),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136602735169448050),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13567478313870950),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2494332239454702),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],59761663500533),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],323799387539650),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7535607038880),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2461830594585),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],12951363545),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],824034499),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],165479148),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],41709757),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9921779),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],477129),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],128289),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2684),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],26),([1],3)],C,.right⟩
def cfg_22 : RMConfig:=⟨[([1],1),([0],1),([1,1,0,1,1,0,1,1,0,0],2564),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],127569),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],472809),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],9895859),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],41554237),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],164546028),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],818435779),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],12917771225),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],2461629040665),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],7534397715360),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],323792131598530),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],59718127853813),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],2494071025574382),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],13565911030589030),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],136593331469756530),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],601152346158744099),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],792954490636171379),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],737195222257364698),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],9407098368744424),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],1495172310314160944),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],3690655947539779712),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],34650830869133740991),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],575691254228742226),([1,1,0],4),([1,1,0,1,1,0,1,1,0,0],4738381338321616897),([1,1,0],1),([1],1)],[([0],2),([1],1),([0],1),([1],5)],F,.left⟩
def cmds_0 : List Cmd:=[
  .scan 0 84,
  .batch [1] 0 [(.D0,0)],
  .scan 0 120,
  .batch [1] 0 [(.D0,0)],
  .scan 0 149,
  .batch [1] 0 [(.D0,0)],
  .batch [1] 1 [(.D2,0)],
  .scan 0 35,
  .scan 9 4,
  .scan 0 109,
  .batch [1] 0 [(.D0,0)],
  .batch [1] 2 [(.D2,0)],
  .scan 0 58,
  .scan 9 4,
  .scan 0 2,
  .scan 8 3,
  .scan 0 131,
  .batch [1] 0 [(.D0,0)],
  .batch [3] 1 [(.D2,2)],
  .scan 0 58,
  .scan 9 6,
  .scan 0 95,
  .scan 7 4,
  .scan 0 157,
  .batch [1] 0 [(.D0,0)],
  .batch [3] 3 [(.D0,1)],
  .scan 0 50,
  .scan 5 3,
  .scan 9 3,
  .scan 0 2,
  .scan 8 3,
  .scan 0 323,
  .batch [1] 0 [(.D0,0)],
  .batch [1] 5 [(.D2,0)],
  .scan 0 50,
  .scan 5 4,
  .scan 0 32,
  .scan 8 3,
  .scan 0 281,
  .batch [1] 0 [(.D0,0)],
  .batch [3] 1 [(.D2,5)],
  .scan 0 58,
  .scan 9 6,
  .scan 5 3,
  .scan 0 29,
  .scan 2 4,
  .scan 6 3,
  .scan 0 151,
  .batch [1] 0 [(.D0,0)],
  .batch [5] 3 [(.D0,4)],
  .scan 0 50,
  .scan 5 4,
  .scan 9 4,
  .scan 0 166,
  .scan 7 4,
  .scan 0 289,
  .batch [1] 0 [(.D0,0)],
  .batch [17,2,2,2] 1 [(.D2,5),(.D0,2)],
  .batch [2] 12 [(.D1,1)],
  .scan 0 50,
  .scan 5 12,
  .scan 9 3,
  .scan 0 2,
  .scan 8 3,
  .scan 4 6,
  .scan 0 569,
  .batch [1] 0 [(.D0,0)],
  .batch [1] 14 [(.D2,0)],
  .scan 0 50,
  .scan 5 13,
  .scan 0 32,
  .scan 8 3,
  .scan 0 42,
  .scan 3 7,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3] 1 [(.D2,14)],
  .scan 0 58,
  .scan 9 6,
  .scan 5 12,
  .scan 0 29,
  .scan 2 13,
  .scan 6 3,
  .scan 0 151,
  .batch [1] 0 [(.D0,0)],
  .batch [5] 3 [(.D0,13)],
  .scan 0 50,
  .scan 5 4,
  .scan 9 4,
  .scan 5 11,
  .scan 0 10,
  .scan 3 11,
  .scan 0 309,
  .batch [1] 0 [(.D0,0)],
  .batch [17,2,2,2] 1 [(.D2,5),(.D0,11)],
  .batch [4] 12 [(.D1,10)]
]
lemma chunk_0_ok : q6 cmds_0 cfg_0=some cfg_1:= by decide +kernel
def cmds_1 : List Cmd:=[
  .scan 0 50,
  .scan 5 13,
  .scan 9 4,
  .scan 5 8,
  .scan 0 10,
  .scan 3 8,
  .scan 0 20,
  .scan 3 8,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [33] 1 [(.D2,14),(.D0,8)],
  .scan 0 50,
  .scan2 5 9 [(16,4),(5,4)],
  .scan 5 6,
  .scan 0 10,
  .scan2 3 0 [(6,20),(5,20)],
  .scan 3 11,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [53,12,2,2,2] 1 [(.D2,17),(.D0,6),(.D0,6)],
  .batch [2] 36 [(.D1,1)],
  .batch [4,4] 37 [(.D5,1),(.D1,6)],
  .scan 0 50,
  .scan 5 40,
  .scan 9 4,
  .scan 5 5,
  .scan 0 10,
  .scan 3 5,
  .scan 0 20,
  .scan 3 35,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [33] 1 [(.D2,41),(.D0,5)],
  .scan 0 50,
  .scan2 5 9 [(16,4),(32,4)],
  .scan 5 3,
  .scan 0 10,
  .scan2 3 0 [(3,20),(32,20)],
  .scan 3 11,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [53,12,2,2,2] 1 [(.D2,17),(.D0,33),(.D0,3)],
  .batch [2] 36 [(.D1,1)],
  .batch [24] 37 [(.D5,28),(.D1,3)],
  .scan 0 50,
  .scan2 5 9 [(48,4),(22,4)],
  .scan 0 78,
  .scan 7 4,
  .scan 3 22,
  .scan 0 20,
  .scan 3 43,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [141] 1 [(.D2,49),(.D0,23),(.D0,1)],
  .scan 0 50,
  .scan2 5 9 [(70,4),(13,4),(16,3)],
  .scan 0 2,
  .scan 8 3,
  .scan 4 16,
  .scan 0 18,
  .scan 2 13,
  .scan 6 3,
  .scan 0 72,
  .scan 2 64,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [43,8,4] 72 [(.D0,14),(.D0,17),(.D2,0)],
  .scan 0 50,
  .scan 5 98,
  .scan 9 4,
  .scan 5 14,
  .scan 0 32,
  .scan 8 3,
  .scan 0 42,
  .scan 3 13,
  .scan 0 20,
  .scan 3 93,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [33] 1 [(.D2,99),(.D0,15)],
  .scan 0 50,
  .scan2 5 9 [(16,4),(90,4)],
  .scan 5 12,
  .scan 0 29,
  .scan 2 13,
  .scan 6 3,
  .scan 0 72,
  .scan 2 89,
  .scan 6 3,
  .scan 0 72,
  .scan 2 10,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [35] 18 [(.D0,91),(.D0,13)],
  .scan 0 50,
  .scan2 5 9 [(34,4),(81,4)],
  .scan 5 11,
  .scan 0 10,
  .scan2 3 0 [(11,20),(81,20)],
  .scan 3 29,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [107,26,6,2,2] 1 [(.D2,35),(.D0,82),(.D0,11)],
  .batch [2] 72 [(.D1,1)],
  .batch [12] 73 [(.D5,74),(.D3,10)],
  .scan 0 50,
  .scan2 5 9 [(78,4),(71,4)],
  .scan 5 9,
  .scan 0 10,
  .scan2 3 0 [(9,20),(71,20)],
  .scan 3 73,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [213] 1 [(.D2,79),(.D0,72),(.D0,9)],
  .scan 0 50,
  .scan2 5 9 [(106,4),(25,4),(62,4)],
  .scan 5 7,
  .scan 0 10,
  .scan2 3 0 [(7,20),(62,20),(25,20)],
  .scan 3 101,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [323,80,18,6,2,2] 1 [(.D2,107),(.D0,26),(.D0,63),(.D0,7)],
  .batch [2] 216 [(.D1,1)],
  .batch [20,6,2] 217 [(.D5,6),(.D5,59),(.D1,7)],
  .batch [2] 231 [(.D1,1)],
  .batch [18] 232 [(.D5,58),(.D2,6)]
]
lemma chunk_1_ok : q6 cmds_1 cfg_1=some cfg_2:= by decide +kernel
def cmds_2 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(240,4),(53,4)],
  .scan 5 5,
  .scan 0 10,
  .scan2 3 0 [(5,20),(53,20)],
  .scan 3 235,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [213] 1 [(.D2,241),(.D0,54),(.D0,5)],
  .scan 0 50,
  .scan2 5 9 [(106,4),(187,4),(44,4)],
  .scan 5 3,
  .scan 0 10,
  .scan2 3 0 [(3,20),(44,20),(187,20)],
  .scan 3 101,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [323,80,18,6,2,2] 1 [(.D2,107),(.D0,188),(.D0,45),(.D0,3)],
  .batch [2] 216 [(.D1,1)],
  .batch [144] 217 [(.D5,168),(.D5,41),(.D1,3)],
  .scan 0 50,
  .scan2 5 9 [(288,4),(132,4),(35,4)],
  .scan 0 78,
  .scan 7 4,
  .scan2 3 0 [(35,20),(132,20)],
  .scan 3 283,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [861] 1 [(.D2,289),(.D0,133),(.D0,36),(.D0,1)],
  .scan 0 50,
  .scan2 5 9 [(430,4),(73,4),(96,4),(29,3)],
  .scan 0 2,
  .scan 8 3,
  .scan 4 29,
  .scan 0 18,
  .scan 2 96,
  .scan 6 3,
  .scan 0 72,
  .scan 2 72,
  .scan 6 3,
  .scan 0 72,
  .scan 2 424,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [223,54,14,4,20] 432 [(.D0,74),(.D0,97),(.D0,30),(.D2,0)],
  .scan 0 50,
  .scan2 5 9 [(588,4),(79,4)],
  .scan 5 26,
  .scan 0 32,
  .scan 8 3,
  .scan 0 42,
  .scan2 3 0 [(25,20),(79,20)],
  .scan 3 583,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [213] 1 [(.D2,589),(.D0,80),(.D0,27)],
  .scan 0 50,
  .scan2 5 9 [(106,4),(535,4),(70,4)],
  .scan 5 24,
  .scan 0 29,
  .scan 2 25,
  .scan 6 3,
  .scan 0 72,
  .scan 2 69,
  .scan 6 3,
  .scan 0 72,
  .scan 2 534,
  .scan 6 3,
  .scan 0 72,
  .scan 2 100,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [215] 108 [(.D0,536),(.D0,71),(.D0,25)],
  .scan 0 50,
  .scan2 5 9 [(214,4),(481,4),(61,4)],
  .scan 5 23,
  .scan 0 10,
  .scan2 3 0 [(23,20),(61,20),(481,20)],
  .scan 3 209,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [647,162,38,10,2,2,2] 1 [(.D2,215),(.D0,482),(.D0,62),(.D0,23)],
  .batch [2] 432 [(.D1,1)],
  .batch [72] 433 [(.D5,444),(.D5,55),(.D3,22)],
  .scan 0 50,
  .scan2 5 9 [(468,4),(426,4),(52,4)],
  .scan 5 21,
  .scan 0 10,
  .scan2 3 0 [(21,20),(52,20),(426,20)],
  .scan 3 463,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1293] 1 [(.D2,469),(.D0,427),(.D0,53),(.D0,21)],
  .scan 0 50,
  .scan2 5 9 [(646,4),(145,4),(372,4),(43,4)],
  .scan 5 19,
  .scan 0 10,
  .scan2 3 0 [(19,20),(43,20),(372,20),(145,20)],
  .scan 3 641,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1943,486,120,30,8,2,2] 1 [(.D2,647),(.D0,146),(.D0,373),(.D0,44),(.D0,19)],
  .batch [2] 1296 [(.D1,1)],
  .batch [110,30,6,2] 1297 [(.D5,36),(.D5,354),(.D5,40),(.D1,19)],
  .batch [2] 1371 [(.D1,1)],
  .batch [118] 1372 [(.D1,349),(.D4,39),(.D2,18)],
  .scan 0 50,
  .scan2 5 9 [(1430,4),(318,4),(34,4)],
  .scan 5 17,
  .scan 0 10,
  .scan2 3 0 [(17,20),(34,20),(318,20)],
  .scan 3 1425,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1293] 1 [(.D2,1431),(.D0,319),(.D0,35),(.D0,17)]
]
lemma chunk_2_ok : q6 cmds_2 cfg_2=some cfg_3:= by decide +kernel
def cmds_3 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(646,4),(1107,4),(264,4),(25,4)],
  .scan 5 15,
  .scan 0 10,
  .scan2 3 0 [(15,20),(25,20),(264,20),(1107,20)],
  .scan 3 641,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1943,486,120,30,8,2,2] 1 [(.D2,647),(.D0,1108),(.D0,265),(.D0,26),(.D0,15)],
  .batch [2] 1296 [(.D1,1)],
  .batch [864] 1297 [(.D5,998),(.D5,246),(.D5,22),(.D1,15)],
  .scan 0 50,
  .scan2 5 9 [(1728,4),(782,4),(210,4),(16,4)],
  .scan 5 13,
  .scan 0 10,
  .scan2 3 0 [(13,20),(16,20),(210,20),(782,20)],
  .scan 3 1723,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5189,1296,324,80,22,6,140] 1 [(.D2,1729),(.D0,783),(.D0,211),(.D0,17),(.D0,13)],
  .scan 0 50,
  .scan2 5 9 [(3528,4),(459,4),(156,4),(7,4)],
  .scan 5 11,
  .scan 0 10,
  .scan2 3 0 [(11,20),(7,20),(156,20),(459,20)],
  .scan 3 3523,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5613,1296,432,432] 1 [(.D2,3529),(.D0,460),(.D0,157),(.D0,8),(.D0,11)],
  .batch [864] 3887 [(.D5,1585),(.D5,135),(.D5,102),(.D1,9)],
  .scan 0 50,
  .scan2 5 9 [(4318,4),(1369,4),(99,4),(96,4)],
  .scan 5 7,
  .scan 0 10,
  .scan2 3 0 [(7,20),(96,20),(99,20),(1369,20)],
  .scan 3 4313,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7773] 1 [(.D2,4319),(.D0,1370),(.D0,100),(.D0,97),(.D0,7)],
  .scan 0 50,
  .scan2 5 9 [(3886,4),(2375,4),(1045,4),(45,4),(87,4)],
  .scan 5 5,
  .scan 0 10,
  .scan2 3 0 [(5,20),(87,20),(45,20),(1045,20),(2375,20)],
  .scan 3 3881,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [11663,2916,728,180,46,12,2,2,2] 1 [(.D2,3887),(.D0,2376),(.D0,1046),(.D0,46),(.D0,88),(.D0,5)],
  .batch [2] 7776 [(.D1,1)],
  .batch [2952,792,216,72] 7777 [(.D5,1726),(.D5,937),(.D5,27),(.D5,84),(.D1,5)],
  .batch [72] 9793 [(.D5,718),(.D5,769),(.D1,1)],
  .batch [144] 9829 [(.D5,700),(.D5,766),(.D1,80),(.D5,3)],
  .scan 0 50,
  .scan2 5 9 [(9900,4),(664,4),(760,4),(78,4)],
  .scan 5 3,
  .scan 0 10,
  .scan2 3 0 [(3,20),(78,20),(760,20),(664,20)],
  .scan 3 9895,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7773] 1 [(.D2,9901),(.D0,665),(.D0,761),(.D0,79),(.D0,3)],
  .scan 0 50,
  .scan2 5 9 [(3886,4),(7957,4),(340,4),(706,4),(69,4)],
  .scan 0 78,
  .scan 7 4,
  .scan2 3 0 [(69,20),(706,20),(340,20),(7957,20)],
  .scan 3 3881,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [11663,2916,728,180,46,12,2,2,2] 1 [(.D2,3887),(.D0,7958),(.D0,341),(.D0,707),(.D0,70),(.D0,1)],
  .batch [2] 7776 [(.D1,1)],
  .batch [2592] 7777 [(.D5,7308),(.D5,232),(.D5,688),(.D5,66),(.D1,1)],
  .scan 0 50,
  .scan2 5 9 [(9072,4),(6660,4),(124,4),(670,4),(63,3)],
  .scan 0 2,
  .scan 8 3,
  .scan 4 63,
  .scan 0 18,
  .scan 2 670,
  .scan 6 3,
  .scan 0 72,
  .scan 2 123,
  .scan 6 3,
  .scan 0 72,
  .scan 2 6659,
  .scan 6 3,
  .scan 0 72,
  .scan 2 9066,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [2255,336] 9074 [(.D0,6661),(.D0,125),(.D0,671),(.D0,64),(.D2,0)],
  .scan 0 50,
  .scan2 5 9 [(10368,4),(6012,4),(16,4),(652,4)],
  .scan 5 60,
  .scan 0 32,
  .scan 8 3,
  .scan 0 42,
  .scan2 3 0 [(59,20),(652,20),(16,20),(6012,20)],
  .scan 3 10363,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1869,432,144,72,72] 1 [(.D2,10369),(.D0,6013),(.D0,17),(.D0,653),(.D0,61)],
  .batch [1008] 1295 [(.D5,9721),(.D5,5904),(.D1,649),(.D1,61)],
  .scan 0 50,
  .scan2 5 9 [(1798,4),(9469,4),(5862,4),(641,4)],
  .scan 5 58,
  .scan 0 29,
  .scan 2 59,
  .scan 6 3,
  .scan 0 72,
  .scan 2 640,
  .scan 6 3,
  .scan 0 72,
  .scan 2 5861,
  .scan 6 3,
  .scan 0 72,
  .scan 2 9468,
  .scan 6 3,
  .scan 0 72,
  .scan 2 1792,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [1295] 1800 [(.D0,9470),(.D0,5863),(.D0,642),(.D0,59)]
]
lemma chunk_3_ok : q6 cmds_3 cfg_3=some cfg_4:= by decide +kernel
def cmds_4 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(2446,4),(9145,4),(5808,4),(632,4)],
  .scan 5 57,
  .scan 0 10,
  .scan2 3 0 [(57,20),(632,20),(5808,20),(9145,20)],
  .scan 3 2441,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7343,430] 1 [(.D2,2447),(.D0,9146),(.D0,5809),(.D0,633),(.D0,57)],
  .scan 0 50,
  .scan2 5 9 [(3886,4),(503,4),(8821,4),(5754,4),(623,4)],
  .scan 5 55,
  .scan 0 10,
  .scan2 3 0 [(55,20),(623,20),(5754,20),(8821,20),(503,20)],
  .scan 3 3881,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [9081,2268,552,144,36,12,12] 1 [(.D2,3887),(.D0,504),(.D0,8822),(.D0,5755),(.D0,624),(.D0,55)],
  .batch [12] 6053 [(.D5,860),(.D1,1)],
  .batch [2572,646,162,38,10,2,384] 6059 [(.D5,857),(.D5,8736),(.D1,5741),(.D3,621),(.D1,55)],
  .scan 0 50,
  .scan2 5 9 [(7965,4),(8498,4),(5700,4),(614,4)],
  .scan 5 53,
  .scan 0 10,
  .scan2 3 0 [(53,20),(614,20),(5700,20),(8498,20)],
  .scan 3 7960,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7773] 1 [(.D2,7966),(.D0,8499),(.D0,5701),(.D0,615),(.D0,53)],
  .scan 0 50,
  .scan2 5 9 [(3886,4),(6022,4),(8174,4),(5646,4),(605,4)],
  .scan 5 51,
  .scan 0 10,
  .scan2 3 0 [(51,20),(605,20),(5646,20),(8174,20),(6022,20)],
  .scan 3 3881,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [11663,2916,728,180,46,12,2,2,2] 1 [(.D2,3887),(.D0,6023),(.D0,8175),(.D0,5647),(.D0,606),(.D0,51)],
  .batch [2] 7776 [(.D1,1)],
  .batch [5184] 7777 [(.D5,5373),(.D5,8066),(.D5,5628),(.D5,602),(.D1,51)],
  .scan 0 50,
  .scan2 5 9 [(10368,4),(4077,4),(7850,4),(5592,4),(596,4)],
  .scan 5 49,
  .scan 0 10,
  .scan2 3 0 [(49,20),(596,20),(5592,20),(7850,20),(4077,20)],
  .scan 3 10363,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [31109,7776,1944,486,122,30,6,4,860] 1 [(.D2,10369),(.D0,4078),(.D0,7851),(.D0,5593),(.D0,597),(.D0,49)],
  .scan 0 50,
  .scan2 5 9 [(21168,4),(2134,4),(7526,4),(5538,4),(587,4)],
  .scan 5 47,
  .scan 0 10,
  .scan2 3 0 [(47,20),(587,20),(5538,20),(7526,20),(2134,20)],
  .scan 3 21163,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [38433,8220] 1 [(.D2,21169),(.D0,2135),(.D0,7527),(.D0,5539),(.D0,588),(.D0,47)],
  .scan 0 50,
  .scan2 5 9 [(23326,4),(9505,4),(190,4),(7202,4),(5484,4),(578,4)],
  .scan 5 45,
  .scan 0 10,
  .scan2 3 0 [(45,20),(578,20),(5484,20),(7202,20),(190,20),(9505,20)],
  .scan 3 23321,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [20661,5112,1296,288,144] 1 [(.D2,23327),(.D0,9506),(.D0,191),(.D0,7203),(.D0,5485),(.D0,579)],
  .batch [41976] 13751 [(.D5,16451),(.D5,8359),(.D3,7171),(.D3,5479),(.D3,578),(.D0,45)],
  .scan 0 50,
  .scan2 5 9 [(34738,4),(5957,4),(6610,4),(6879,4),(5430,4),(569,4)],
  .scan 5 43,
  .scan 0 10,
  .scan2 3 0 [(43,20),(569,20),(5430,20),(6879,20),(6610,20),(5957,20)],
  .scan 3 34733,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [104219,26054,6514,1628,406,102,26,6,2,2] 1 [(.D2,34739),(.D0,5958),(.D0,6611),(.D0,6880),(.D0,5431),(.D0,570),(.D0,43)],
  .batch [2] 69480 [(.D1,1)],
  .batch [500,126,32,6,4,2,2] 69481 [(.D5,166),(.D1,5646),(.D1,6719),(.D5,5403),(.D5,565),(.D2,42)],
  .batch [3808] 69817 [(.D1,5617),(.D1,6715),(.D2,5403),(.D0,565),(.D3,42)],
  .scan 0 50,
  .scan2 5 9 [(71720,4),(4664,4),(6555,4),(5376,4),(560,4)],
  .scan 5 41,
  .scan 0 10,
  .scan2 3 0 [(41,20),(560,20),(5376,20),(6555,20),(4664,20)],
  .scan 3 71715,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [46653] 1 [(.D2,71721),(.D0,4665),(.D0,6556),(.D0,5377),(.D0,561),(.D0,41)],
  .scan 0 50,
  .scan2 5 9 [(23326,4),(60057,4),(2720,4),(6231,4),(5322,4),(551,4)],
  .scan 5 39,
  .scan 0 10,
  .scan2 3 0 [(39,20),(551,20),(5322,20),(6231,20),(2720,20),(60057,20)],
  .scan 3 23321,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [69983,17496,4374,1092,272,70,18,2,2,2] 1 [(.D2,23327),(.D0,60058),(.D0,2721),(.D0,6232),(.D0,5323),(.D0,552),(.D0,39)],
  .batch [2] 46656 [(.D1,1)],
  .batch [31104] 46657 [(.D5,56168),(.D5,2072),(.D5,6123),(.D5,5304),(.D5,548),(.D1,39)],
  .scan 0 50,
  .scan2 5 9 [(62208,4),(48392,4),(776,4),(5907,4),(5268,4),(542,4)],
  .scan 5 37,
  .scan 0 10,
  .scan2 3 0 [(37,20),(542,20),(5268,20),(5907,20),(776,20),(48392,20)],
  .scan 3 62203,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [83949,20952,5184,1296,360,72,27864] 1 [(.D2,62209),(.D0,48393),(.D0,777),(.D0,5908),(.D0,5269),(.D0,543),(.D0,37)],
  .scan 0 50,
  .scan2 5 9 [(69838,4),(27289,4),(42572,4),(5585,4),(5214,4),(533,4)],
  .scan 5 35,
  .scan 0 10,
  .scan2 3 0 [(35,20),(533,20),(5214,20),(5585,20),(42572,20),(27289,20)],
  .scan 3 69833,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [209519,52380,13094,3274,818,204,52,12,2,2,2] 1 [(.D2,69839),(.D0,27290),(.D0,42573),(.D0,5586),(.D0,5215),(.D0,534),(.D0,35)],
  .batch [2] 139680 [(.D1,1)],
  .batch [96] 139681 [(.D5,15648),(.D1,40633),(.D3,5262),(.D5,5160),(.D5,524),(.D5,33)]
]
lemma chunk_4_ok : q6 cmds_4 cfg_4=some cfg_5:= by decide +kernel
def cmds_5 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(139728,4),(15624,4),(40628,4),(5261,4),(5160,4),(524,4)],
  .scan 5 33,
  .scan 0 10,
  .scan2 3 0 [(33,20),(524,20),(5160,20),(5261,20),(40628,20),(15624,20)],
  .scan 3 139723,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [279933] 1 [(.D2,139729),(.D0,15625),(.D0,40629),(.D0,5262),(.D0,5161),(.D0,525),(.D0,33)],
  .scan 0 50,
  .scan2 5 9 [(139966,4),(69745,4),(3960,4),(38684,4),(4937,4),(5106,4),(515,4)],
  .scan 5 31,
  .scan 0 10,
  .scan2 3 0 [(31,20),(515,20),(5106,20),(4937,20),(38684,20),(3960,20),(69745,20)],
  .scan 3 139961,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [419903,104976,26244,6560,1638,412,102,26,6,2,2] 1 [(.D2,139967),(.D0,69746),(.D0,3961),(.D0,38685),(.D0,4938),(.D0,5107),(.D0,516),(.D0,31)],
  .batch [2] 279936 [(.D1,1)],
  .batch [1308,336,72,24,12] 279937 [(.D5,46416),(.D5,72),(.D5,38036),(.D5,4829),(.D5,5088),(.D5,512),(.D1,31)],
  .batch [12] 280813 [(.D5,45978),(.D1,1)],
  .batch [30804] 280819 [(.D5,45975),(.D1,38025),(.D2,4827),(.D1,5089),(.D0,513),(.D2,30)],
  .scan 0 50,
  .scan2 5 9 [(296220,4),(38274,4),(36740,4),(4613,4),(5052,4),(506,4)],
  .scan 5 29,
  .scan 0 10,
  .scan2 3 0 [(29,20),(506,20),(5052,20),(4613,20),(36740,20),(38274,20)],
  .scan 3 296215,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [279933] 1 [(.D2,296221),(.D0,38275),(.D0,36741),(.D0,4614),(.D0,5053),(.D0,507),(.D0,29)],
  .scan 0 50,
  .scan2 5 9 [(139966,4),(226237,4),(26610,4),(34796,4),(4289,4),(4998,4),(497,4)],
  .scan 5 27,
  .scan 0 10,
  .scan2 3 0 [(27,20),(497,20),(4998,20),(4289,20),(34796,20),(26610,20),(226237,20)],
  .scan 3 139961,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [419903,104976,26244,6560,1638,412,102,26,6,2,2] 1 [(.D2,139967),(.D0,226238),(.D0,26611),(.D0,34797),(.D0,4290),(.D0,4999),(.D0,498),(.D0,27)],
  .batch [2] 279936 [(.D1,1)],
  .batch [186624] 279937 [(.D5,202908),(.D5,22722),(.D5,34148),(.D5,4181),(.D5,4980),(.D5,494),(.D1,27)],
  .scan 0 50,
  .scan2 5 9 [(373248,4),(156252,4),(14946,4),(32852,4),(3965,4),(4944,4),(488,4)],
  .scan 5 25,
  .scan 0 10,
  .scan2 3 0 [(25,20),(488,20),(4944,20),(3965,20),(32852,20),(14946,20),(156252,20)],
  .scan 3 373243,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1119749,279936,69984,17496,4374,1094,274,68,16,6,31100] 1 [(.D2,373249),(.D0,156253),(.D0,14947),(.D0,32853),(.D0,3966),(.D0,4945),(.D0,489),(.D0,25)],
  .scan 0 50,
  .scan2 5 9 [(762048,4),(86269,4),(3282,4),(30908,4),(3641,4),(4890,4),(479,4)],
  .scan 5 23,
  .scan 0 10,
  .scan2 3 0 [(23,20),(479,20),(4890,20),(3641,20),(30908,20),(3282,20),(86269,20)],
  .scan 3 762043,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [354597,88560,22176,5616,1368,360,72] 1 [(.D2,762049),(.D0,86270),(.D0,3283),(.D0,30909),(.D0,3642),(.D0,4891),(.D0,480),(.D0,23)],
  .batch [72] 236375 [(.D5,643861),(.D5,66571),(.D1,1)],
  .batch [201096] 236411 [(.D5,643843),(.D5,66568),(.D5,30361),(.D4,3550),(.D0,4876),(.D4,476),(.D1,23)],
  .scan 0 50,
  .scan2 5 9 [(336958,4),(593569,4),(58189,4),(28964,4),(3317,4),(4836,4),(470,4)],
  .scan 5 21,
  .scan 0 10,
  .scan2 3 0 [(21,20),(470,20),(4836,20),(3317,20),(28964,20),(58189,20),(593569,20)],
  .scan 3 336953,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1010879,252720,63180,15794,3948,988,246,62,16,2,2,2] 1 [(.D2,336959),(.D0,593570),(.D0,58190),(.D0,28965),(.D0,3318),(.D0,4837),(.D0,471),(.D0,21)],
  .batch [2] 673920 [(.D1,1)],
  .batch [55296] 673921 [(.D5,537408),(.D5,48829),(.D5,27404),(.D1,3058),(.D5,4793),(.D4,463),(.D4,19)],
  .scan 0 50,
  .scan2 5 9 [(701568,4),(523584,4),(46525,4),(27020,4),(2993,4),(4782,4),(461,4)],
  .scan 5 19,
  .scan 0 10,
  .scan2 3 0 [(19,20),(461,20),(4782,20),(2993,20),(27020,20),(46525,20),(523584,20)],
  .scan 3 701563,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1679613] 1 [(.D2,701569),(.D0,523585),(.D0,46526),(.D0,27021),(.D0,2994),(.D0,4783),(.D0,462),(.D0,19)],
  .scan 0 50,
  .scan2 5 9 [(839806,4),(281665,4),(453600,4),(34861,4),(25076,4),(2669,4),(4728,4),(452,4)],
  .scan 5 17,
  .scan 0 10,
  .scan2 3 0 [(17,20),(452,20),(4728,20),(2669,20),(25076,20),(34861,20),(453600,20),(281665,20)],
  .scan 3 839801,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2519423,629856,157464,39366,9840,2460,614,154,38,10,2,2,2] 1 [(.D2,839807),(.D0,281666),(.D0,453601),(.D0,34862),(.D0,25077),(.D0,2670),(.D0,4729),(.D0,453),(.D0,17)],
  .batch [2] 1679616 [(.D1,1)],
  .batch [425090,106274,26568,6642,1660,416,102,28,6,2] 1679617 [(.D5,141696),(.D5,430272),(.D5,30973),(.D5,24428),(.D5,2561),(.D5,4710),(.D5,449),(.D1,17)],
  .batch [2] 1963011 [(.D1,1)],
  .batch [92158] 1963012 [(.D1,406657),(.D0,27038),(.D2,23772),(.D5,2452),(.D0,4693),(.D0,447),(.D4,15)],
  .scan 0 50,
  .scan2 5 9 [(2009090,4),(383616,4),(23197,4),(23132,4),(2345,4),(4674,4),(443,4)],
  .scan 5 15,
  .scan 0 10,
  .scan2 3 0 [(15,20),(443,20),(4674,20),(2345,20),(23132,20),(23197,20),(383616,20)],
  .scan 3 2009085,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1679613] 1 [(.D2,2009091),(.D0,383617),(.D0,23198),(.D0,23133),(.D0,2346),(.D0,4675),(.D0,444),(.D0,15)],
  .scan 0 50,
  .scan2 5 9 [(839806,4),(1589187,4),(313632,4),(11533,4),(21188,4),(2021,4),(4620,4),(434,4)],
  .scan 5 13,
  .scan 0 10,
  .scan2 3 0 [(13,20),(434,20),(4620,20),(2021,20),(21188,20),(11533,20),(313632,20),(1589187,20)],
  .scan 3 839801,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2519423,629856,157464,39366,9840,2460,614,154,38,10,2,2,2] 1 [(.D2,839807),(.D0,1589188),(.D0,313633),(.D0,11534),(.D0,21189),(.D0,2022),(.D0,4621),(.D0,435),(.D0,13)],
  .batch [2] 1679616 [(.D1,1)],
  .batch [825696,206496,51624,12888,3240,864,216,3024] 1679617 [(.D5,1449218),(.D5,290304),(.D5,7645),(.D5,20540),(.D5,1913),(.D5,4602),(.D5,431),(.D1,13)],
  .scan 0 50,
  .scan2 5 9 [(2231640,4),(1173206,4),(244302,4),(19245,4),(1697,4),(4566,4),(425,4)],
  .scan 5 11,
  .scan 0 10,
  .scan2 3 0 [(11,20),(425,20),(4566,20),(1697,20),(19245,20),(244302,20),(1173206,20)],
  .scan 3 2231635,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1679613] 1 [(.D2,2231641),(.D0,1173207),(.D0,244303),(.D0,19246),(.D0,1698),(.D0,4567),(.D0,426),(.D0,11)]
]
lemma chunk_5_ok : q6 cmds_5 cfg_5=some cfg_6:= by decide +kernel
def cmds_6 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(839806,4),(1811737,4),(1103222,4),(232638,4),(17301,4),(1373,4),(4512,4),(416,4)],
  .scan 5 9,
  .scan 0 10,
  .scan2 3 0 [(9,20),(416,20),(4512,20),(1373,20),(17301,20),(232638,20),(1103222,20),(1811737,20)],
  .scan 3 839801,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2519423,629856,157464,39366,9840,2460,614,154,38,10,2,2,2] 1 [(.D2,839807),(.D0,1811738),(.D0,1103223),(.D0,232639),(.D0,17302),(.D0,1374),(.D0,4513),(.D0,417),(.D0,9)],
  .batch [2] 1679616 [(.D1,1)],
  .batch [1119744] 1679617 [(.D5,1671768),(.D5,1079894),(.D5,228750),(.D5,16653),(.D5,1265),(.D5,4494),(.D5,413),(.D1,9)],
  .scan 0 50,
  .scan2 5 9 [(2239488,4),(1391832,4),(1033238,4),(220974,4),(15357,4),(1049,4),(4458,4),(407,4)],
  .scan 5 7,
  .scan 0 10,
  .scan2 3 0 [(7,20),(407,20),(4458,20),(1049,20),(15357,20),(220974,20),(1033238,20),(1391832,20)],
  .scan 3 2239483,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [6718469,1679616,419904,104976,26244,6560,1642,410,102,24,6,4,186620] 1 [(.D2,2239489),(.D0,1391833),(.D0,1033239),(.D0,220975),(.D0,15358),(.D0,1050),(.D0,4459),(.D0,408),(.D0,7)],
  .scan 0 50,
  .scan2 5 9 [(4572288,4),(971929,4),(963254,4),(209310,4),(13413,4),(725,4),(4404,4),(398,4)],
  .scan 5 5,
  .scan 0 10,
  .scan2 3 0 [(5,20),(398,20),(4404,20),(725,20),(13413,20),(209310,20),(963254,20),(971929,20)],
  .scan 3 4572283,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [10077693] 1 [(.D2,4572289),(.D0,971930),(.D0,963255),(.D0,209311),(.D0,13414),(.D0,726),(.D0,4405),(.D0,399),(.D0,5)],
  .scan 0 50,
  .scan2 5 9 [(5038846,4),(2052865,4),(552025,4),(893270,4),(197646,4),(11469,4),(401,4),(4350,4),(389,4)],
  .scan 5 3,
  .scan 0 10,
  .scan2 3 0 [(3,20),(389,20),(4350,20),(401,20),(11469,20),(197646,20),(893270,20),(552025,20),(2052865,20)],
  .scan 3 5038841,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [15116543,3779136,944784,236196,59048,14760,3690,924,232,56,16,2,2,2] 1 [(.D2,5038847),(.D0,2052866),(.D0,552026),(.D0,893271),(.D0,197647),(.D0,11470),(.D0,402),(.D0,4351),(.D0,390),(.D0,3)],
  .batch [2] 10077696 [(.D1,1)],
  .batch [3639170,909794,227448,56862,14214,3556,888,222,56,12,4,2] 10077697 [(.D5,1213056),(.D5,412057),(.D5,869942),(.D5,193758),(.D5,10821),(.D5,293),(.D5,4332),(.D5,386),(.D1,3)],
  .batch [2] 12503811 [(.D1,1)],
  .batch [311038] 12503812 [(.D1,209882),(.D0,836247),(.D0,188143),(.D0,9886),(.D0,138),(.D2,4306),(.D5,382),(.D4,1)],
  .scan 0 50,
  .scan2 5 9 [(12659330,4),(132121,4),(823286,4),(185982,4),(9525,4),(77,4),(4296,4),(380,4)],
  .scan 0 78,
  .scan 7 4,
  .scan2 3 0 [(380,20),(4296,20),(77,20),(9525,20),(185982,20),(823286,20),(132121,20)],
  .scan 3 12659325,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1835133,435456,124416,15552,15552,15552] 1 [(.D2,12659331),(.D0,132122),(.D0,823287),(.D0,185983),(.D0,9526),(.D0,78),(.D0,4297),(.D0,381),(.D0,1)],
  .batch [546936,136752,34176,8556,2136,528,144,36,264] 1220831 [(.D5,12048915),(.D5,30385),(.D5,806330),(.D5,183156),(.D5,9054),(.D1,4284),(.D2,378),(.D1,1)],
  .scan 0 50,
  .scan2 5 9 [(1585594,4),(11866533,4),(801255,4),(182310,4),(8913,4),(4259,4),(374,3)],
  .scan 0 2,
  .scan 8 3,
  .scan 4 374,
  .scan 0 18,
  .scan 2 4259,
  .scan 6 3,
  .scan 0 72,
  .scan 2 8912,
  .scan 6 3,
  .scan 0 72,
  .scan 2 182309,
  .scan 6 3,
  .scan 0 72,
  .scan 2 801254,
  .scan 6 3,
  .scan 0 72,
  .scan 2 11866532,
  .scan 6 3,
  .scan 0 72,
  .scan 2 1585588,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [93311] 1585596 [(.D0,11866534),(.D0,801256),(.D0,182311),(.D0,8914),(.D0,4260),(.D0,375),(.D2,0)],
  .scan 0 50,
  .scan2 5 9 [(1632250,4),(11843205,4),(797367,4),(181662,4),(8805,4),(4241,4)],
  .scan 5 371,
  .scan 0 32,
  .scan 8 3,
  .scan 0 42,
  .scan2 3 0 [(370,20),(4241,20),(8805,20),(181662,20),(797367,20),(11843205,20)],
  .scan 3 1632245,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [279933] 1 [(.D2,1632251),(.D0,11843206),(.D0,797368),(.D0,181663),(.D0,8806),(.D0,4242),(.D0,372)],
  .scan 0 50,
  .scan2 5 9 [(139966,4),(1562267,4),(11831541,4),(795423,4),(181338,4),(8751,4),(4232,4)],
  .scan 5 369,
  .scan 0 29,
  .scan 2 370,
  .scan 6 3,
  .scan 0 72,
  .scan 2 4231,
  .scan 6 3,
  .scan 0 72,
  .scan 2 8750,
  .scan 6 3,
  .scan 0 72,
  .scan 2 181337,
  .scan 6 3,
  .scan 0 72,
  .scan 2 795422,
  .scan 6 3,
  .scan 0 72,
  .scan 2 11831540,
  .scan 6 3,
  .scan 0 72,
  .scan 2 1562266,
  .scan 6 3,
  .scan 0 72,
  .scan 2 139960,
  .scan 0 489,
  .batch [1] 0 [(.D0,0)],
  .batch [279935] 139968 [(.D0,1562268),(.D0,11831542),(.D0,795424),(.D0,181339),(.D0,8752),(.D0,4233),(.D0,370)]
]
lemma chunk_6_ok : q6 cmds_6 cfg_6=some cfg_7:= by decide +kernel
def cmds_7 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(279934,4),(1492283,4),(11819877,4),(793479,4),(181014,4),(8697,4),(4223,4)],
  .scan 5 368,
  .scan 0 10,
  .scan2 3 0 [(368,20),(4223,20),(8697,20),(181014,20),(793479,20),(11819877,20),(1492283,20)],
  .scan 3 279929,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [839807,209952,52488,13122,3278,820,206,52,12,2,2,2] 1 [(.D2,279935),(.D0,1492284),(.D0,11819878),(.D0,793480),(.D0,181015),(.D0,8698),(.D0,4224),(.D0,368)],
  .batch [2] 559872 [(.D1,1)],
  .batch [93312] 559873 [(.D5,1445626),(.D5,11812101),(.D5,792183),(.D5,180798),(.D5,8661),(.D5,4217),(.D3,367)],
  .scan 0 50,
  .scan2 5 9 [(606528,4),(1422298,4),(11808213,4),(791535,4),(180690,4),(8643,4),(4214,4)],
  .scan 5 366,
  .scan 0 10,
  .scan2 3 0 [(366,20),(4214,20),(8643,20),(180690,20),(791535,20),(11808213,20),(1422298,20)],
  .scan 3 606523,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1679613] 1 [(.D2,606529),(.D0,1422299),(.D0,11808214),(.D0,791536),(.D0,180691),(.D0,8644),(.D0,4215),(.D0,366)],
  .scan 0 50,
  .scan2 5 9 [(839806,4),(186625,4),(1352314,4),(11796549,4),(789591,4),(180366,4),(8589,4),(4205,4)],
  .scan 5 364,
  .scan 0 10,
  .scan2 3 0 [(364,20),(4205,20),(8589,20),(180366,20),(789591,20),(11796549,20),(1352314,20),(186625,20)],
  .scan 3 839801,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2519423,629856,157464,39366,9840,2460,614,154,38,10,2,2,2] 1 [(.D2,839807),(.D0,186626),(.D0,1352315),(.D0,11796550),(.D0,789592),(.D0,180367),(.D0,8590),(.D0,4206),(.D0,364)],
  .batch [2] 1679616 [(.D1,1)],
  .batch [139970,34994,8748,2188,546,138,32,10,2] 1679617 [(.D5,46656),(.D5,1328986),(.D5,11792661),(.D5,788943),(.D5,180258),(.D5,8571),(.D5,4202),(.D1,364)],
  .batch [2] 1772931 [(.D1,1)],
  .batch [155518] 1772932 [(.D1,1321211),(.D0,11791366),(.D0,788728),(.D0,180223),(.D0,8566),(.D4,4201),(.D2,363)],
  .scan 0 50,
  .scan2 5 9 [(1850690,4),(1282330,4),(11784885,4),(787647,4),(180042,4),(8535,4),(4196,4)],
  .scan 5 362,
  .scan 0 10,
  .scan2 3 0 [(362,20),(4196,20),(8535,20),(180042,20),(787647,20),(11784885,20),(1282330,20)],
  .scan 3 1850685,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1679613] 1 [(.D2,1850691),(.D0,1282331),(.D0,11784886),(.D0,787648),(.D0,180043),(.D0,8536),(.D0,4197),(.D0,362)],
  .scan 0 50,
  .scan2 5 9 [(839806,4),(1430787,4),(1212346,4),(11773221,4),(785703,4),(179718,4),(8481,4),(4187,4)],
  .scan 5 360,
  .scan 0 10,
  .scan2 3 0 [(360,20),(4187,20),(8481,20),(179718,20),(785703,20),(11773221,20),(1212346,20),(1430787,20)],
  .scan 3 839801,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2519423,629856,157464,39366,9840,2460,614,154,38,10,2,2,2] 1 [(.D2,839807),(.D0,1430788),(.D0,1212347),(.D0,11773222),(.D0,785704),(.D0,179719),(.D0,8482),(.D0,4188),(.D0,360)],
  .batch [2] 1679616 [(.D1,1)],
  .batch [1119744] 1679617 [(.D5,1290818),(.D5,1189018),(.D5,11769333),(.D5,785055),(.D5,179610),(.D5,8463),(.D5,4184),(.D1,360)],
  .scan 0 50,
  .scan2 5 9 [(2239488,4),(1010882,4),(1142362,4),(11761557,4),(783759,4),(179394,4),(8427,4),(4178,4)],
  .scan 5 358,
  .scan 0 10,
  .scan2 3 0 [(358,20),(4178,20),(8427,20),(179394,20),(783759,20),(11761557,20),(1142362,20),(1010882,20)],
  .scan 3 2239483,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [6718469,1679616,419904,104976,26244,6560,1642,410,102,24,6,4,186620] 1 [(.D2,2239489),(.D0,1010883),(.D0,1142363),(.D0,11761558),(.D0,783760),(.D0,179395),(.D0,8428),(.D0,4179),(.D0,358)],
  .scan 0 50,
  .scan2 5 9 [(4572288,4),(590979,4),(1072378,4),(11749893,4),(781815,4),(179070,4),(8373,4),(4169,4)],
  .scan 5 356,
  .scan 0 10,
  .scan2 3 0 [(356,20),(4169,20),(8373,20),(179070,20),(781815,20),(11749893,20),(1072378,20),(590979,20)],
  .scan 3 4572283,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [10077693] 1 [(.D2,4572289),(.D0,590980),(.D0,1072379),(.D0,11749894),(.D0,781816),(.D0,179071),(.D0,8374),(.D0,4170),(.D0,356)],
  .scan 0 50,
  .scan2 5 9 [(5038846,4),(2052865,4),(171075,4),(1002394,4),(11738229,4),(779871,4),(178746,4),(8319,4),(4160,4)],
  .scan 5 354,
  .scan 0 10,
  .scan2 3 0 [(354,20),(4160,20),(8319,20),(178746,20),(779871,20),(11738229,20),(1002394,20),(171075,20),(2052865,20)],
  .scan 3 5038841,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [15116543,3779136,944784,236196,59048,14760,3690,924,232,56,16,2,2,2] 1 [(.D2,5038847),(.D0,2052866),(.D0,171076),(.D0,1002395),(.D0,11738230),(.D0,779872),(.D0,178747),(.D0,8320),(.D0,4161),(.D0,354)],
  .batch [2] 10077696 [(.D1,1)],
  .batch [559932,139992,35004,8748,2184,552,132,36,12] 10077697 [(.D5,1213056),(.D5,31107),(.D5,979066),(.D5,11734341),(.D5,779223),(.D5,178638),(.D5,8301),(.D5,4157),(.D1,354)],
  .batch [995316] 10450993 [(.D5,1026408),(.D1,973883),(.D0,11733478),(.D0,779080),(.D0,178615),(.D4,8297),(.D2,4157),(.D2,353)],
  .scan 0 50,
  .scan2 5 9 [(10948650,4),(777579,4),(932410,4),(11726565,4),(777927,4),(178422,4),(8265,4),(4151,4)],
  .scan 5 352,
  .scan 0 10,
  .scan2 3 0 [(352,20),(4151,20),(8265,20),(178422,20),(777927,20),(11726565,20),(932410,20),(777579,20)],
  .scan 3 10948645,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [10077693] 1 [(.D2,10948651),(.D0,777580),(.D0,932411),(.D0,11726566),(.D0,777928),(.D0,178423),(.D0,8266),(.D0,4152),(.D0,352)],
  .scan 0 50,
  .scan2 5 9 [(5038846,4),(8429227,4),(357675,4),(862426,4),(11714901,4),(775983,4),(178098,4),(8211,4),(4142,4)],
  .scan 5 350,
  .scan 0 10,
  .scan2 3 0 [(350,20),(4142,20),(8211,20),(178098,20),(775983,20),(11714901,20),(862426,20),(357675,20),(8429227,20)],
  .scan 3 5038841,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [15116543,3779136,944784,236196,59048,14760,3690,924,232,56,16,2,2,2] 1 [(.D2,5038847),(.D0,8429228),(.D0,357676),(.D0,862427),(.D0,11714902),(.D0,775984),(.D0,178099),(.D0,8212),(.D0,4143),(.D0,350)],
  .batch [2] 10077696 [(.D1,1)],
  .batch [3918732,979692,244920,61236,15300,3840,948,240,72,12] 10077697 [(.D5,7589418),(.D5,217707),(.D5,839098),(.D5,11711013),(.D5,775335),(.D5,177990),(.D5,8193),(.D5,4139),(.D1,350)],
  .batch [12] 12690193 [(.D5,6283170),(.D1,1)],
  .batch [248904] 12690199 [(.D5,6283167),(.D5,802813),(.D3,11704966),(.D5,774327),(.D5,177822),(.D3,8166),(.D0,4135),(.D5,348)],
  .scan 0 50,
  .scan2 5 9 [(12814650,4),(6220941,4),(792442,4),(11703237,4),(774039,4),(177774,4),(8157,4),(4133,4)],
  .scan 5 348,
  .scan 0 10,
  .scan2 3 0 [(348,20),(4133,20),(8157,20),(177774,20),(774039,20),(11703237,20),(792442,20),(6220941,20)],
  .scan 3 12814645,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [10077693] 1 [(.D2,12814651),(.D0,6220942),(.D0,792443),(.D0,11703238),(.D0,774040),(.D0,177775),(.D0,8158),(.D0,4134),(.D0,348)],
  .scan 0 50,
  .scan2 5 9 [(5038846,4),(10295227,4),(5801037,4),(722458,4),(11691573,4),(772095,4),(177450,4),(8103,4),(4124,4)],
  .scan 5 346,
  .scan 0 10,
  .scan2 3 0 [(346,20),(4124,20),(8103,20),(177450,20),(772095,20),(11691573,20),(722458,20),(5801037,20),(10295227,20)],
  .scan 3 5038841,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [15116543,3779136,944784,236196,59048,14760,3690,924,232,56,16,2,2,2] 1 [(.D2,5038847),(.D0,10295228),(.D0,5801038),(.D0,722459),(.D0,11691574),(.D0,772096),(.D0,177451),(.D0,8104),(.D0,4125),(.D0,346)],
  .batch [2] 10077696 [(.D1,1)],
  .batch [6718464] 10077697 [(.D5,9455418),(.D5,5661069),(.D5,699130),(.D5,11687685),(.D5,771447),(.D5,177342),(.D5,8085),(.D5,4121),(.D1,346)]
]
lemma chunk_7_ok : q6 cmds_7 cfg_7=some cfg_8:= by decide +kernel
def cmds_8 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(13436928,4),(7775802,4),(5381133,4),(652474,4),(11679909,4),(770151,4),(177126,4),(8049,4),(4115,4)],
  .scan 5 344,
  .scan 0 10,
  .scan2 3 0 [(344,20),(4115,20),(8049,20),(177126,20),(770151,20),(11679909,20),(652474,20),(5381133,20),(7775802,20)],
  .scan 3 13436923,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [40310789,10077696,2519424,629856,157464,39366,9842,2460,616,152,40,8,4,1119740] 1 [(.D2,13436929),(.D0,7775803),(.D0,5381134),(.D0,652475),(.D0,11679910),(.D0,770152),(.D0,177127),(.D0,8050),(.D0,4116),(.D0,344)],
  .scan 0 50,
  .scan2 5 9 [(27433728,4),(5256379,4),(4961229,4),(582490,4),(11668245,4),(768207,4),(176802,4),(7995,4),(4106,4)],
  .scan 5 342,
  .scan 0 10,
  .scan2 3 0 [(342,20),(4106,20),(7995,20),(176802,20),(768207,20),(11668245,20),(582490,20),(4961229,20),(5256379,20)],
  .scan 3 27433723,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [60466173] 1 [(.D2,27433729),(.D0,5256380),(.D0,4961230),(.D0,582491),(.D0,11668246),(.D0,768208),(.D0,176803),(.D0,7996),(.D0,4107),(.D0,342)],
  .scan 0 50,
  .scan2 5 9 [(30233086,4),(12317185,4),(2736955,4),(4541325,4),(512506,4),(11656581,4),(766263,4),(176478,4),(7941,4),(4097,4)],
  .scan 5 340,
  .scan 0 10,
  .scan2 3 0 [(340,20),(4097,20),(7941,20),(176478,20),(766263,20),(11656581,20),(512506,20),(4541325,20),(2736955,20),(12317185,20)],
  .scan 3 30233081,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [90699263,22674816,5668704,1417176,354294,88572,22142,5536,1386,344,88,20,6,2,2] 1 [(.D2,30233087),(.D0,12317186),(.D0,2736956),(.D0,4541326),(.D0,512507),(.D0,11656582),(.D0,766264),(.D0,176479),(.D0,7942),(.D0,4098),(.D0,340)],
  .batch [2] 60466176 [(.D1,1)],
  .batch [21835010,5458754,1364688,341172,85294,21324,5330,1332,334,84,20,4,2] 60466177 [(.D5,7278336),(.D5,1897147),(.D5,4401357),(.D5,489178),(.D5,11652693),(.D5,765615),(.D5,176370),(.D5,7923),(.D5,4094),(.D1,340)],
  .batch [2] 75022851 [(.D1,1)],
  .batch [1866238] 75022852 [(.D1,684092),(.D0,4199182),(.D0,455483),(.D0,11647078),(.D0,764680),(.D0,176215),(.D2,7897),(.D5,4090),(.D4,338)],
  .scan 0 50,
  .scan2 5 9 [(75955970,4),(217531,4),(4121421,4),(442522,4),(11644917,4),(764319,4),(176154,4),(7887,4),(4088,4)],
  .scan 5 338,
  .scan 0 10,
  .scan2 3 0 [(338,20),(4088,20),(7887,20),(176154,20),(764319,20),(11644917,20),(442522,20),(4121421,20),(217531,20)],
  .scan 3 75955965,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3915585,978888,244716,61176,15300,3816,960,252,48,24] 1 [(.D2,75955971),(.D0,217532),(.D0,4121422),(.D0,442523),(.D0,11644918),(.D0,764320),(.D0,176155),(.D0,7888),(.D0,4089)],
  .batch [9207552] 2610383 [(.D5,74650779),(.D3,4085167),(.D2,436480),(.D2,11643910),(.D5,764151),(.D3,176127),(.D0,7883),(.D3,4088),(.D0,338)],
  .scan 0 50,
  .scan2 5 9 [(7214158,4),(72348891,4),(3701518,4),(372538,4),(11633253,4),(762375,4),(175830,4),(7833,4),(4079,4)],
  .scan 5 336,
  .scan 0 10,
  .scan2 3 0 [(336,20),(4079,20),(7833,20),(175830,20),(762375,20),(11633253,20),(372538,20),(3701518,20),(72348891,20)],
  .scan 3 7214153,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21642479,5410620,1352654,338164,84540,21134,5284,1322,330,82,20,6,5268252] 1 [(.D2,7214159),(.D0,72348892),(.D0,3701519),(.D0,372539),(.D0,11633254),(.D0,762376),(.D0,175831),(.D0,7834),(.D0,4080),(.D0,336)],
  .scan 0 50,
  .scan2 5 9 [(17062443,4),(69829469,4),(3281614,4),(302554,4),(11621589,4),(760431,4),(175506,4),(7779,4),(4070,4)],
  .scan 5 334,
  .scan 0 10,
  .scan2 3 0 [(334,20),(4070,20),(7779,20),(175506,20),(760431,20),(11621589,20),(302554,20),(3281614,20),(69829469,20)],
  .scan 3 17062438,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [51187333,9278840] 1 [(.D2,17062444),(.D0,69829470),(.D0,3281615),(.D0,302555),(.D0,11621590),(.D0,760432),(.D0,175507),(.D0,7780),(.D0,4071),(.D0,334)],
  .scan 0 50,
  .scan2 5 9 [(30233086,4),(1945900,4),(67310045,4),(2861710,4),(232570,4),(11609925,4),(758487,4),(175182,4),(7725,4),(4061,4)],
  .scan 5 332,
  .scan 0 10,
  .scan2 3 0 [(332,20),(4061,20),(7725,20),(175182,20),(758487,20),(11609925,20),(232570,20),(2861710,20),(67310045,20),(1945900,20)],
  .scan 3 30233081,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [35026221,8756556,2189136,547272,136824,34212,8556,2136,528,144,36] 1 [(.D2,30233087),(.D0,1945901),(.D0,67310046),(.D0,2861711),(.D0,232571),(.D0,11609926),(.D0,758488),(.D0,175183),(.D0,7726),(.D0,4062)],
  .batch [52682556] 23350811 [(.D5,18557681),(.D3,66985729),(.D1,2807658),(.D5,223561),(.D5,11608424),(.D4,758237),(.D4,175140),(.D3,7719),(.D4,4060),(.D0,332)],
  .scan 0 50,
  .scan2 5 9 [(49692088,4),(5387042,4),(64790622,4),(2441806,4),(162586,4),(11598261,4),(756543,4),(174858,4),(7671,4),(4052,4)],
  .scan 5 330,
  .scan 0 10,
  .scan2 3 0 [(330,20),(4052,20),(7671,20),(174858,20),(756543,20),(11598261,20),(162586,20),(2441806,20),(64790622,20),(5387042,20)],
  .scan 3 49692083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [96966777,24241680,6060420,1515120,378768,94704,23664,5928,1476,372,96,12,38917980] 1 [(.D2,49692089),(.D0,5387043),(.D0,64790623),(.D0,2441807),(.D0,162587),(.D0,11598262),(.D0,756544),(.D0,174859),(.D0,7672),(.D0,4053),(.D0,330)],
  .scan 0 50,
  .scan2 5 9 [(84103498,4),(7640339,4),(62271200,4),(2021902,4),(92602,4),(11586597,4),(754599,4),(174534,4),(7617,4),(4043,4)],
  .scan 5 328,
  .scan 0 10,
  .scan2 3 0 [(328,20),(4043,20),(7617,20),(174534,20),(754599,20),(11586597,20),(92602,20),(2021902,20),(62271200,20),(7640339,20)],
  .scan 3 84103493,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [137526129,34381524,8595384,2148840,537204,134304,33588,8388,2100,528,120,36,12,12] 1 [(.D2,84103499),(.D0,7640340),(.D0,62271201),(.D0,2021903),(.D0,92603),(.D0,11586598),(.D0,754600),(.D0,174535),(.D0,7618),(.D0,4044),(.D0,328)],
  .batch [29904828] 91684085 [(.D5,38261456),(.D1,60997811),(.D4,1809670),(.D1,57231),(.D1,11580703),(.D0,753617),(.D1,174371),(.D1,7591),(.D0,4039),(.D3,327)],
  .scan 0 50,
  .scan2 5 9 [(106636498,4),(30785249,4),(59751775,4),(1601998,4),(22618,4),(11574933,4),(752655,4),(174210,4),(7563,4),(4034,4)],
  .scan 5 326,
  .scan 0 10,
  .scan2 3 0 [(326,20),(4034,20),(7563,20),(174210,20),(752655,20),(11574933,20),(22618,20),(1601998,20),(59751775,20),(30785249,20)],
  .scan 3 106636493,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [87943965,21982752,5497632,1373760,344736,85536,20736,7776,40919904] 1 [(.D2,106636499),(.D0,30785250),(.D0,59751776),(.D0,1601999),(.D0,22619),(.D0,11574934),(.D0,752656),(.D0,174211),(.D0,7564),(.D0,4035),(.D0,326)],
  .scan 0 50,
  .scan2 5 9 [(79088398,4),(67092299,4),(24194549,4),(58653325,4),(1418923,4),(11563270,4),(750711,4),(173886,4),(7509,4),(4025,4)],
  .scan 5 324,
  .scan 0 10,
  .scan2 3 0 [(324,20),(4025,20),(7509,20),(173886,20),(750711,20),(11563270,20),(1418923,20),(58653325,20),(24194549,20),(67092299,20)],
  .scan 3 79088393,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [237265199,59316300,14829074,3707268,926818,231704,57924,14482,3620,906,226,56,16,2,2,2] 1 [(.D2,79088399),(.D0,67092300),(.D0,24194550),(.D0,58653326),(.D0,1418924),(.D0,11563271),(.D0,750712),(.D0,173887),(.D0,7510),(.D0,4026),(.D0,324)],
  .batch [2] 158176800 [(.D1,1)],
  .batch [7740576] 158176801 [(.D5,53910898),(.D5,21997649),(.D5,58287175),(.D1,1357899),(.D3,11553100),(.D0,749017),(.D2,173604),(.D2,7462),(.D1,4018),(.D5,322)],
  .scan 0 50,
  .scan2 5 9 [(162047088,4),(51975754,4),(21675125,4),(58233421,4),(1348939,4),(11551606,4),(748767,4),(173562,4),(7455,4),(4016,4)],
  .scan 5 322,
  .scan 0 10,
  .scan2 3 0 [(322,20),(4016,20),(7455,20),(173562,20),(748767,20),(11551606,20),(1348939,20),(58233421,20),(21675125,20),(51975754,20)],
  .scan 3 162047083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [362797053] 1 [(.D2,162047089),(.D0,51975755),(.D0,21675126),(.D0,58233422),(.D0,1348940),(.D0,11551607),(.D0,748768),(.D0,173563),(.D0,7456),(.D0,4017),(.D0,322)],
  .scan 0 50,
  .scan2 5 9 [(181398526,4),(71347825,4),(36859210,4),(19155701,4),(57813517,4),(1278955,4),(11539942,4),(746823,4),(173238,4),(7401,4),(4007,4)],
  .scan 5 320,
  .scan 0 10,
  .scan2 3 0 [(320,20),(4007,20),(7401,20),(173238,20),(746823,20),(11539942,20),(1278955,20),(57813517,20),(19155701,20),(36859210,20),(71347825,20)],
  .scan 3 181398521,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [544195583,136048896,34012224,8503056,2125764,531440,132858,33216,8304,2076,520,128,34,8,2,2] 1 [(.D2,181398527),(.D0,71347826),(.D0,36859211),(.D0,19155702),(.D0,57813518),(.D0,1278956),(.D0,11539943),(.D0,746824),(.D0,173239),(.D0,7402),(.D0,4008),(.D0,320)],
  .batch [2] 362797056 [(.D1,1)],
  .batch [123344210,30836054,7709014,1927254,481812,120452,30114,7528,1884,470,118,30,6,2] 362797057 [(.D5,41114736),(.D5,31820362),(.D5,18315893),(.D5,57673549),(.D5,1255627),(.D5,11536054),(.D5,746175),(.D5,173130),(.D5,7383),(.D5,4004),(.D1,320)],
  .batch [2] 445026531 [(.D1,1)],
  .batch [12900958] 445026532 [(.D1,24967907),(.D0,17173818),(.D2,57483203),(.D3,1223903),(.D5,11530767),(.D2,745294),(.D5,172983),(.D1,7360),(.D4,4000),(.D4,318)]
]
lemma chunk_8_ok : q6 cmds_8 cfg_8=some cfg_9:= by decide +kernel
def cmds_9 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(451477010,4),(21742666,4),(16636277,4),(57393613,4),(1208971,4),(11528278,4),(744879,4),(172914,4),(7347,4),(3998,4)],
  .scan 5 318,
  .scan 0 10,
  .scan2 3 0 [(318,20),(3998,20),(7347,20),(172914,20),(744879,20),(11528278,20),(1208971,20),(57393613,20),(16636277,20),(21742666,20)],
  .scan 3 451477005,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [362797053] 1 [(.D2,451477011),(.D0,21742667),(.D0,16636278),(.D0,57393614),(.D0,1208972),(.D0,11528279),(.D0,744880),(.D0,172915),(.D0,7348),(.D0,3999),(.D0,318)],
  .scan 0 50,
  .scan2 5 9 [(181398526,4),(360777747,4),(6626122,4),(14116853,4),(56973709,4),(1138987,4),(11516614,4),(742935,4),(172590,4),(7293,4),(3989,4)],
  .scan 5 316,
  .scan 0 10,
  .scan2 3 0 [(316,20),(3989,20),(7293,20),(172590,20),(742935,20),(11516614,20),(1138987,20),(56973709,20),(14116853,20),(6626122,20),(360777747,20)],
  .scan 3 181398521,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [544195583,136048896,34012224,8503056,2125764,531440,132858,33216,8304,2076,520,128,34,8,2,2] 1 [(.D2,181398527),(.D0,360777748),(.D0,6626123),(.D0,14116854),(.D0,56973710),(.D0,1138988),(.D0,11516615),(.D0,742936),(.D0,172591),(.D0,7294),(.D0,3990),(.D0,316)],
  .batch [2] 362797056 [(.D1,1)],
  .batch [28570944,7142736,1785696,446412,111600,27900,6984,1752,432,108,36,12,12] 362797057 [(.D5,330544658),(.D5,1587274),(.D5,13277045),(.D5,56833741),(.D5,1115659),(.D5,11512726),(.D5,742287),(.D5,172482),(.D5,7275),(.D5,3986),(.D1,316)],
  .batch [33961704] 381844369 [(.D5,321021002),(.D1,13012499),(.D5,56789650),(.D5,1108311),(.D2,11511502),(.D0,742084),(.D4,172448),(.D4,7269),(.D3,3986),(.D2,315)],
  .scan 0 50,
  .scan2 5 9 [(398825220,4),(312530576,4),(11597427,4),(56553805,4),(1069003,4),(11504950,4),(740991,4),(172266,4),(7239,4),(3980,4)],
  .scan 5 314,
  .scan 0 10,
  .scan2 3 0 [(314,20),(3980,20),(7239,20),(172266,20),(740991,20),(11504950,20),(1069003,20),(56553805,20),(11597427,20),(312530576,20)],
  .scan 3 398825215,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [362797053] 1 [(.D2,398825221),(.D0,312530577),(.D0,11597428),(.D0,56553806),(.D0,1069004),(.D0,11504951),(.D0,740992),(.D0,172267),(.D0,7240),(.D0,3981),(.D0,314)],
  .scan 0 50,
  .scan2 5 9 [(181398526,4),(308125957,4),(297414032,4),(9078003,4),(56133901,4),(999019,4),(11493286,4),(739047,4),(171942,4),(7185,4),(3971,4)],
  .scan 5 312,
  .scan 0 10,
  .scan2 3 0 [(312,20),(3971,20),(7185,20),(171942,20),(739047,20),(11493286,20),(999019,20),(56133901,20),(9078003,20),(297414032,20),(308125957,20)],
  .scan 3 181398521,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [544195583,136048896,34012224,8503056,2125764,531440,132858,33216,8304,2076,520,128,34,8,2,2] 1 [(.D2,181398527),(.D0,308125958),(.D0,297414033),(.D0,9078004),(.D0,56133902),(.D0,999020),(.D0,11493287),(.D0,739048),(.D0,171943),(.D0,7186),(.D0,3972),(.D0,312)],
  .batch [2] 362797056 [(.D1,1)],
  .batch [241864704] 362797057 [(.D5,277892868),(.D5,292375184),(.D5,8238195),(.D5,55993933),(.D5,975691),(.D5,11489398),(.D5,738399),(.D5,171834),(.D5,7167),(.D5,3968),(.D1,312)],
  .scan 0 50,
  .scan2 5 9 [(483729408,4),(217426692,4),(282297488,4),(6558579,4),(55713997,4),(929035,4),(11481622,4),(737103,4),(171618,4),(7131,4),(3962,4)],
  .scan 5 310,
  .scan 0 10,
  .scan2 3 0 [(310,20),(3962,20),(7131,20),(171618,20),(737103,20),(11481622,20),(929035,20),(55713997,20),(6558579,20),(282297488,20),(217426692,20)],
  .scan 3 483729403,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1451188229,362797056,90699264,22674816,5668704,1417176,354294,88574,22144,5534,1384,348,86,22,6,40310780] 1 [(.D2,483729409),(.D0,217426693),(.D0,282297489),(.D0,6558580),(.D0,55713998),(.D0,929036),(.D0,11481623),(.D0,737104),(.D0,171619),(.D0,7132),(.D0,3963),(.D0,310)],
  .scan 0 50,
  .scan2 5 9 [(987614208,4),(126727429,4),(267180944,4),(4039155,4),(55294093,4),(859051,4),(11469958,4),(735159,4),(171294,4),(7077,4),(3953,4)],
  .scan 5 308,
  .scan 0 10,
  .scan2 3 0 [(308,20),(3953,20),(7077,20),(171294,20),(735159,20),(11469958,20),(859051,20),(55294093,20),(4039155,20),(267180944,20),(126727429,20)],
  .scan 3 987614203,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2176782333] 1 [(.D2,987614209),(.D0,126727430),(.D0,267180945),(.D0,4039156),(.D0,55294094),(.D0,859052),(.D0,11469959),(.D0,735160),(.D0,171295),(.D0,7078),(.D0,3954),(.D0,308)],
  .scan 0 50,
  .scan2 5 9 [(1088391166,4),(443418625,4),(36028165,4),(252064400,4),(1519731,4),(54874189,4),(789067,4),(11458294,4),(733215,4),(170970,4),(7023,4),(3944,4)],
  .scan 5 306,
  .scan 0 10,
  .scan2 3 0 [(306,20),(3944,20),(7023,20),(170970,20),(733215,20),(11458294,20),(789067,20),(54874189,20),(1519731,20),(252064400,20),(36028165,20),(443418625,20)],
  .scan 3 1088391161,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3265173503,816293376,204073344,51018336,12754584,3188646,797160,199290,49824,12456,3114,776,196,48,12,2,2,2] 1 [(.D2,1088391167),(.D0,443418626),(.D0,36028166),(.D0,252064401),(.D0,1519732),(.D0,54874190),(.D0,789068),(.D0,11458295),(.D0,733216),(.D0,170971),(.D0,7024),(.D0,3945),(.D0,306)],
  .batch [2] 2176782336 [(.D1,1)],
  .batch [104311392,26077860,6519456,1629864,407472,101880,25464,6360,1596,396,96,36,56046600,14011560,3502872,875808,218880,54792,13680,3384,864,216,72] 2176782337 [(.D5,262020096),(.D5,5795077),(.D5,247025552),(.D5,679923),(.D5,54734221),(.D5,765739),(.D5,11454406),(.D5,732567),(.D5,170862),(.D5,7005),(.D5,3941),(.D1,306)],
  .batch [72] 2283687637 [(.D5,208567446),(.D5,242946009),(.D1,1)],
  .batch [23992560] 2283687673 [(.D5,208567428),(.D5,242946006),(.D1,54620901),(.D1,746853),(.D3,11451259),(.D4,732042),(.D1,170776),(.D4,6990),(.D3,3939),(.D3,305)],
  .scan 0 50,
  .scan2 5 9 [(2295683952,4),(202569288,4),(241946316,4),(54454285,4),(719083,4),(11446630,4),(731271,4),(170646,4),(6969,4),(3935,4)],
  .scan 5 304,
  .scan 0 10,
  .scan2 3 0 [(304,20),(3935,20),(6969,20),(170646,20),(731271,20),(11446630,20),(719083,20),(54454285,20),(241946316,20),(202569288,20)],
  .scan 3 2295683947,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [362797053] 1 [(.D2,2295683953),(.D0,202569289),(.D0,241946317),(.D0,54454286),(.D0,719084),(.D0,11446631),(.D0,731272),(.D0,170647),(.D0,6970),(.D0,3936),(.D0,304)],
  .scan 0 50,
  .scan2 5 9 [(181398526,4),(2204984689,4),(187452744,4),(239426892,4),(54034381,4),(649099,4),(11434966,4),(729327,4),(170322,4),(6915,4),(3926,4)],
  .scan 5 302,
  .scan 0 10,
  .scan2 3 0 [(302,20),(3926,20),(6915,20),(170322,20),(729327,20),(11434966,20),(649099,20),(54034381,20),(239426892,20),(187452744,20),(2204984689,20)],
  .scan 3 181398521,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [544195583,136048896,34012224,8503056,2125764,531440,132858,33216,8304,2076,520,128,34,8,2,2] 1 [(.D2,181398527),(.D0,2204984690),(.D0,187452745),(.D0,239426893),(.D0,54034382),(.D0,649100),(.D0,11434967),(.D0,729328),(.D0,170323),(.D0,6916),(.D0,3927),(.D0,302)],
  .batch [2] 362797056 [(.D1,1)],
  .batch [241864704] 362797057 [(.D5,2174751600),(.D5,182413896),(.D5,238587084),(.D5,53894413),(.D5,625771),(.D5,11431078),(.D5,728679),(.D5,170214),(.D5,6897),(.D5,3923),(.D1,302)],
  .scan 0 50,
  .scan2 5 9 [(483729408,4),(2114285424,4),(172336200,4),(236907468,4),(53614477,4),(579115,4),(11423302,4),(727383,4),(169998,4),(6861,4),(3917,4)],
  .scan 5 300,
  .scan 0 10,
  .scan2 3 0 [(300,20),(3917,20),(6861,20),(169998,20),(727383,20),(11423302,20),(579115,20),(53614477,20),(236907468,20),(172336200,20),(2114285424,20)],
  .scan 3 483729403,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1451188229,362797056,90699264,22674816,5668704,1417176,354294,88574,22144,5534,1384,348,86,22,6,40310780] 1 [(.D2,483729409),(.D0,2114285425),(.D0,172336201),(.D0,236907469),(.D0,53614478),(.D0,579116),(.D0,11423303),(.D0,727384),(.D0,169999),(.D0,6862),(.D0,3918),(.D0,300)],
  .scan 0 50,
  .scan2 5 9 [(987614208,4),(2023586161,4),(157219656,4),(234388044,4),(53194573,4),(509131,4),(11411638,4),(725439,4),(169674,4),(6807,4),(3908,4)],
  .scan 5 298,
  .scan 0 10,
  .scan2 3 0 [(298,20),(3908,20),(6807,20),(169674,20),(725439,20),(11411638,20),(509131,20),(53194573,20),(234388044,20),(157219656,20),(2023586161,20)],
  .scan 3 987614203,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2176782333] 1 [(.D2,987614209),(.D0,2023586162),(.D0,157219657),(.D0,234388045),(.D0,53194574),(.D0,509132),(.D0,11411639),(.D0,725440),(.D0,169675),(.D0,6808),(.D0,3909),(.D0,298)],
  .scan 0 50,
  .scan2 5 9 [(1088391166,4),(443418625,4),(1932886897,4),(142103112,4),(231868620,4),(52774669,4),(439147,4),(11399974,4),(723495,4),(169350,4),(6753,4),(3899,4)],
  .scan 5 296,
  .scan 0 10,
  .scan2 3 0 [(296,20),(3899,20),(6753,20),(169350,20),(723495,20),(11399974,20),(439147,20),(52774669,20),(231868620,20),(142103112,20),(1932886897,20),(443418625,20)],
  .scan 3 1088391161,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3265173503,816293376,204073344,51018336,12754584,3188646,797160,199290,49824,12456,3114,776,196,48,12,2,2,2] 1 [(.D2,1088391167),(.D0,443418626),(.D0,1932886898),(.D0,142103113),(.D0,231868621),(.D0,52774670),(.D0,439148),(.D0,11399975),(.D0,723496),(.D0,169351),(.D0,6754),(.D0,3900),(.D0,296)],
  .batch [2] 2176782336 [(.D1,1)],
  .batch [786060290,196515074,49128768,12282192,3070548,767638,191910,47976,11994,3000,750,186,48,12,2] 2176782337 [(.D5,262020096),(.D5,1902653809),(.D5,137064264),(.D5,231028812),(.D5,52634701),(.D5,415819),(.D5,11396086),(.D5,722847),(.D5,169242),(.D5,6735),(.D5,3896),(.D1,296)],
  .batch [2] 2700822531 [(.D1,1)],
  .batch [67184638] 2700822532 [(.D1,1858983794),(.D0,129785929),(.D0,229815757),(.D0,52432526),(.D0,382124),(.D0,11390471),(.D0,721912),(.D0,169087),(.D2,6709),(.D5,3892),(.D4,294)]
]
lemma chunk_9_ok : q6 cmds_9 cfg_9=some cfg_10:= by decide +kernel
def cmds_10 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(2734414850,4),(1842187633,4),(126986568,4),(229349196,4),(52354765,4),(369163,4),(11388310,4),(721551,4),(169026,4),(6699,4),(3890,4)],
  .scan 5 294,
  .scan 0 10,
  .scan2 3 0 [(294,20),(3890,20),(6699,20),(169026,20),(721551,20),(11388310,20),(369163,20),(52354765,20),(229349196,20),(126986568,20),(1842187633,20)],
  .scan 3 2734414845,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2176782333] 1 [(.D2,2734414851),(.D0,1842187634),(.D0,126986569),(.D0,229349197),(.D0,52354766),(.D0,369164),(.D0,11388311),(.D0,721552),(.D0,169027),(.D0,6700),(.D0,3891),(.D0,294)],
  .scan 0 50,
  .scan2 5 9 [(1088391166,4),(2190219267,4),(1751488369,4),(111870024,4),(226829772,4),(51934861,4),(299179,4),(11376646,4),(719607,4),(168702,4),(6645,4),(3881,4)],
  .scan 5 292,
  .scan 0 10,
  .scan2 3 0 [(292,20),(3881,20),(6645,20),(168702,20),(719607,20),(11376646,20),(299179,20),(51934861,20),(226829772,20),(111870024,20),(1751488369,20),(2190219267,20)],
  .scan 3 1088391161,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3265173503,816293376,204073344,51018336,12754584,3188646,797160,199290,49824,12456,3114,776,196,48,12,2,2,2] 1 [(.D2,1088391167),(.D0,2190219268),(.D0,1751488370),(.D0,111870025),(.D0,226829773),(.D0,51934862),(.D0,299180),(.D0,11376647),(.D0,719608),(.D0,168703),(.D0,6646),(.D0,3882),(.D0,292)],
  .batch [2] 2176782336 [(.D1,1)],
  .batch [1451188224] 2176782337 [(.D5,2008820738),(.D5,1721255281),(.D5,106831176),(.D5,225989964),(.D5,51794893),(.D5,275851),(.D5,11372758),(.D5,718959),(.D5,168594),(.D5,6627),(.D5,3878),(.D1,292)],
  .scan 0 50,
  .scan2 5 9 [(2902376448,4),(1646023682,4),(1660789105,4),(96753480,4),(224310348,4),(51514957,4),(229195,4),(11364982,4),(717663,4),(168378,4),(6591,4),(3872,4)],
  .scan 5 290,
  .scan 0 10,
  .scan2 3 0 [(290,20),(3872,20),(6591,20),(168378,20),(717663,20),(11364982,20),(229195,20),(51514957,20),(224310348,20),(96753480,20),(1660789105,20),(1646023682,20)],
  .scan 3 2902376443,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [8707129349,2176782336,544195584,136048896,34012224,8503056,2125764,531440,132862,33216,8304,2076,518,130,32,6,4,241864700] 1 [(.D2,2902376449),(.D0,1646023683),(.D0,1660789106),(.D0,96753481),(.D0,224310349),(.D0,51514958),(.D0,229196),(.D0,11364983),(.D0,717664),(.D0,168379),(.D0,6592),(.D0,3873),(.D0,290)],
  .scan 0 50,
  .scan2 5 9 [(5925685248,4),(1101828099,4),(1570089841,4),(81636936,4),(221790924,4),(51095053,4),(159211,4),(11353318,4),(715719,4),(168054,4),(6537,4),(3863,4)],
  .scan 5 288,
  .scan 0 10,
  .scan2 3 0 [(288,20),(3863,20),(6537,20),(168054,20),(715719,20),(11353318,20),(159211,20),(51095053,20),(221790924,20),(81636936,20),(1570089841,20),(1101828099,20)],
  .scan 3 5925685243,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [13060694013] 1 [(.D2,5925685249),(.D0,1101828100),(.D0,1570089842),(.D0,81636937),(.D0,221790925),(.D0,51095054),(.D0,159212),(.D0,11353319),(.D0,715720),(.D0,168055),(.D0,6538),(.D0,3864),(.D0,288)],
  .scan 0 50,
  .scan2 5 9 [(6530347006,4),(2660511745,4),(557632515,4),(1479390577,4),(66520392,4),(219271500,4),(50675149,4),(89227,4),(11341654,4),(713775,4),(167730,4),(6483,4),(3854,4)],
  .scan 5 286,
  .scan 0 10,
  .scan2 3 0 [(286,20),(3854,20),(6483,20),(167730,20),(713775,20),(11341654,20),(89227,20),(50675149,20),(219271500,20),(66520392,20),(1479390577,20),(557632515,20),(2660511745,20)],
  .scan 3 6530347001,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [19591041023,4897760256,1224440064,306110016,76527504,19131876,4782968,1195740,298936,74736,18684,4670,1168,290,72,18,6,2,2] 1 [(.D2,6530347007),(.D0,2660511746),(.D0,557632516),(.D0,1479390578),(.D0,66520393),(.D0,219271501),(.D0,50675150),(.D0,89228),(.D0,11341655),(.D0,713776),(.D0,167731),(.D0,6484),(.D0,3855),(.D0,286)],
  .batch [2] 13060694016 [(.D1,1)],
  .batch [4716361730,1179090434,294772608,73693152,18423288,4605822,1151454,287866,71966,17992,4496,1126,282,68,18,4,2] 13060694017 [(.D5,1572120576),(.D5,376233987),(.D5,1449157489),(.D5,61481544),(.D5,218431692),(.D5,50535181),(.D5,65899),(.D5,11337766),(.D5,713127),(.D5,167622),(.D5,6465),(.D5,3851),(.D1,286)],
  .batch [2] 16204935171 [(.D1,1)],
  .batch [342641676,60466162] 16204935172 [(.D1,114213892),(.D0,1405487474),(.D0,54203209),(.D0,217218637),(.D0,50333006),(.D0,32204),(.D0,11332151),(.D0,712192),(.D0,167467),(.D2,6439),(.D5,3847),(.D4,284)],
  .scan 0 50,
  .scan2 5 9 [(16406489090,4),(13436931,4),(1388691313,4),(51403848,4),(216752076,4),(50255245,4),(19243,4),(11329990,4),(711831,4),(167406,4),(6429,4),(3845,4)],
  .scan 5 284,
  .scan 0 10,
  .scan2 3 0 [(284,20),(3845,20),(6429,20),(167406,20),(711831,20),(11329990,20),(19243,20),(50255245,20),(216752076,20),(51403848,20),(1388691313,20),(13436931,20)],
  .scan 3 16406489085,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [241864785,60466188,15116544,3779136,944784,236196,59040,14760,3696,936,228,60,12] 1 [(.D2,16406489091),(.D0,13436932),(.D0,1388691314),(.D0,51403849),(.D0,216752077),(.D0,50255246),(.D0,19244),(.D0,11329991),(.D0,711832),(.D0,167407),(.D0,6430)],
  .batch [408628788,102145536,25520832,6391872,1586304,404352,108864,31104,263015424] 161243183 [(.D5,16325867499),(.D1,1386451826),(.D0,51030601),(.D0,216689869),(.D0,50244878),(.D0,17516),(.D0,11329703),(.D0,711784),(.D2,167398),(.D5,6428),(.D0,3846),(.D0,284)],
  .scan 0 50,
  .scan2 5 9 [(565159720,4),(16123909230,4),(1352792113,4),(45420648,4),(215754876,4),(50089045,4),(11318327,4),(709887,4),(167082,4),(6375,4),(3836,4)],
  .scan 5 282,
  .scan 0 10,
  .scan2 3 0 [(282,20),(3836,20),(6375,20),(167082,20),(709887,20),(11318327,20),(50089045,20),(215754876,20),(45420648,20),(1352792113,20),(16123909230,20)],
  .scan 3 565159715,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1695479165,423869790,57433378] 1 [(.D2,565159721),(.D0,16123909231),(.D0,1352792114),(.D0,45420649),(.D0,215754877),(.D0,50089046),(.D0,11318328),(.D0,709888),(.D0,167083),(.D0,6376),(.D0,3837),(.D0,282)],
  .scan 0 50,
  .scan2 5 9 [(1088391166,4),(20964137,4),(16033209966,4),(1337675569,4),(42901224,4),(215334972,4),(50019061,4),(11306663,4),(707943,4),(166758,4),(6321,4),(3827,4)],
  .scan 5 280,
  .scan 0 10,
  .scan2 3 0 [(280,20),(3827,20),(6321,20),(166758,20),(707943,20),(11306663,20),(50019061,20),(215334972,20),(42901224,20),(1337675569,20),(16033209966,20),(20964137,20)],
  .scan 3 1088391161,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [377354493,94338612,23584656,5896152,1474044,368508,92124,23040,5760,1440,360,96,12,12,12] 1 [(.D2,1088391167),(.D0,20964138),(.D0,16033209967),(.D0,1337675570),(.D0,42901225),(.D0,215334973),(.D0,50019062),(.D0,11306664),(.D0,707944),(.D0,166759),(.D0,6322),(.D0,3828)],
  .batch [2092925796] 251569661 [(.D5,962606336),(.D1,16029715944),(.D4,1337093232),(.D0,42804169),(.D0,215318797),(.D2,50016365),(.D3,11306214),(.D5,707868),(.D1,166747),(.D2,6319),(.D1,3828),(.D0,280)],
  .scan 0 50,
  .scan2 5 9 [(1298032558,4),(439374887,4),(15942510701,4),(1322559025,4),(40381800,4),(214915068,4),(49949077,4),(11294999,4),(705999,4),(166434,4),(6267,4),(3818,4)],
  .scan 5 278,
  .scan 0 10,
  .scan2 3 0 [(278,20),(3818,20),(6267,20),(166434,20),(705999,20),(11294999,20),(49949077,20),(214915068,20),(40381800,20),(1322559025,20),(15942510701,20),(439374887,20)],
  .scan 3 1298032553,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3894097679,973524420,243381104,60845274,15211320,3802830,950706,237678,59418,14856,3714,928,234,56,16,2,2,2] 1 [(.D2,1298032559),(.D0,439374888),(.D0,15942510702),(.D0,1322559026),(.D0,40381801),(.D0,214915069),(.D0,49949078),(.D0,11295000),(.D0,706000),(.D0,166435),(.D0,6268),(.D0,3819),(.D0,278)],
  .batch [2] 2596065120 [(.D1,1)],
  .batch [669108380,167277096,41819274,10454820,2613704,653424,163356,40840,10212,2552,636,160,42,8,4,2,2] 2596065121 [(.D5,223036126),(.D5,15906454241),(.D1,1316549616),(.D1,39380233),(.D2,214748140),(.D3,49921256),(.D1,11290363),(.D1,705227),(.D5,166305),(.D1,6247),(.D2,3815),(.D2,277)],
  .batch [69880468] 3042137377 [(.D1,15869281553),(.D5,1310354167),(.D1,38347658),(.D5,214576044),(.D1,49892574),(.D1,11285583),(.D2,704430),(.D2,166173),(.D0,6224),(.D5,3811),(.D4,276)],
  .scan 0 50,
  .scan2 5 9 [(3077077610,4),(15851811435,4),(1307442481,4),(37862376,4),(214495164,4),(49879093,4),(11283335,4),(704055,4),(166110,4),(6213,4),(3809,4)],
  .scan 5 276,
  .scan 0 10,
  .scan2 3 0 [(276,20),(3809,20),(6213,20),(166110,20),(704055,20),(11283335,20),(49879093,20),(214495164,20),(37862376,20),(1307442481,20),(15851811435,20)],
  .scan 3 3077077605,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2176782333] 1 [(.D2,3077077611),(.D0,15851811436),(.D0,1307442482),(.D0,37862377),(.D0,214495165),(.D0,49879094),(.D0,11283336),(.D0,704056),(.D0,166111),(.D0,6214),(.D0,3810),(.D0,276)],
  .scan 0 50,
  .scan2 5 9 [(1088391166,4),(2532882027,4),(15761112171,4),(1292325937,4),(35342952,4),(214075260,4),(49809109,4),(11271671,4),(702111,4),(165786,4),(6159,4),(3800,4)],
  .scan 5 274,
  .scan 0 10,
  .scan2 3 0 [(274,20),(3800,20),(6159,20),(165786,20),(702111,20),(11271671,20),(49809109,20),(214075260,20),(35342952,20),(1292325937,20),(15761112171,20),(2532882027,20)],
  .scan 3 1088391161,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3265173503,816293376,204073344,51018336,12754584,3188646,797160,199290,49824,12456,3114,776,196,48,12,2,2,2] 1 [(.D2,1088391167),(.D0,2532882028),(.D0,15761112172),(.D0,1292325938),(.D0,35342953),(.D0,214075261),(.D0,49809110),(.D0,11271672),(.D0,702112),(.D0,165787),(.D0,6160),(.D0,3801),(.D0,274)],
  .batch [2] 2176782336 [(.D1,1)],
  .batch [1451188224] 2176782337 [(.D5,2351483498),(.D5,15730879083),(.D5,1287287089),(.D5,34503144),(.D5,213935292),(.D5,49785781),(.D5,11267783),(.D5,701463),(.D5,165678),(.D5,6141),(.D5,3797),(.D1,274)]
]
lemma chunk_10_ok : q6 cmds_10 cfg_10=some cfg_11:= by decide +kernel
def cmds_11 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(2902376448,4),(1988686442,4),(15670412907,4),(1277209393,4),(32823528,4),(213655356,4),(49739125,4),(11260007,4),(700167,4),(165462,4),(6105,4),(3791,4)],
  .scan 5 272,
  .scan 0 10,
  .scan2 3 0 [(272,20),(3791,20),(6105,20),(165462,20),(700167,20),(11260007,20),(49739125,20),(213655356,20),(32823528,20),(1277209393,20),(15670412907,20),(1988686442,20)],
  .scan 3 2902376443,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [8707129349,2176782336,544195584,136048896,34012224,8503056,2125764,531440,132862,33216,8304,2076,518,130,32,6,4,241864700] 1 [(.D2,2902376449),(.D0,1988686443),(.D0,15670412908),(.D0,1277209394),(.D0,32823529),(.D0,213655357),(.D0,49739126),(.D0,11260008),(.D0,700168),(.D0,165463),(.D0,6106),(.D0,3792),(.D0,272)],
  .scan 0 50,
  .scan2 5 9 [(5925685248,4),(1444490859,4),(15579713643,4),(1262092849,4),(30304104,4),(213235452,4),(49669141,4),(11248343,4),(698223,4),(165138,4),(6051,4),(3782,4)],
  .scan 5 270,
  .scan 0 10,
  .scan2 3 0 [(270,20),(3782,20),(6051,20),(165138,20),(698223,20),(11248343,20),(49669141,20),(213235452,20),(30304104,20),(1262092849,20),(15579713643,20),(1444490859,20)],
  .scan 3 5925685243,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [13060694013] 1 [(.D2,5925685249),(.D0,1444490860),(.D0,15579713644),(.D0,1262092850),(.D0,30304105),(.D0,213235453),(.D0,49669142),(.D0,11248344),(.D0,698224),(.D0,165139),(.D0,6052),(.D0,3783),(.D0,270)],
  .scan 0 50,
  .scan2 5 9 [(6530347006,4),(2660511745,4),(900295275,4),(15489014379,4),(1246976305,4),(27784680,4),(212815548,4),(49599157,4),(11236679,4),(696279,4),(164814,4),(5997,4),(3773,4)],
  .scan 5 268,
  .scan 0 10,
  .scan2 3 0 [(268,20),(3773,20),(5997,20),(164814,20),(696279,20),(11236679,20),(49599157,20),(212815548,20),(27784680,20),(1246976305,20),(15489014379,20),(900295275,20),(2660511745,20)],
  .scan 3 6530347001,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [19591041023,4897760256,1224440064,306110016,76527504,19131876,4782968,1195740,298936,74736,18684,4670,1168,290,72,18,6,2,2] 1 [(.D2,6530347007),(.D0,2660511746),(.D0,900295276),(.D0,15489014380),(.D0,1246976306),(.D0,27784681),(.D0,212815549),(.D0,49599158),(.D0,11236680),(.D0,696280),(.D0,164815),(.D0,5998),(.D0,3774),(.D0,268)],
  .batch [2] 13060694016 [(.D1,1)],
  .batch [4716361730,1179090434,294772608,73693152,18423288,4605822,1151454,287866,71966,17992,4496,1126,282,68,18,4,2] 13060694017 [(.D5,1572120576),(.D5,718896747),(.D5,15458781291),(.D5,1241937457),(.D5,26944872),(.D5,212675580),(.D5,49575829),(.D5,11232791),(.D5,695631),(.D5,164706),(.D5,5979),(.D5,3770),(.D1,268)],
  .batch [2] 16204935171 [(.D1,1)],
  .batch [403107838] 16204935172 [(.D1,456876652),(.D0,15415111276),(.D0,1234659122),(.D0,25731817),(.D0,212473405),(.D0,49542134),(.D0,11227176),(.D0,694696),(.D0,164551),(.D2,5953),(.D5,3766),(.D4,266)],
  .scan 0 50,
  .scan2 5 9 [(16406489090,4),(356099691,4),(15398315115,4),(1231859761,4),(25265256,4),(212395644,4),(49529173,4),(11225015,4),(694335,4),(164490,4),(5943,4),(3764,4)],
  .scan 5 266,
  .scan 0 10,
  .scan2 3 0 [(266,20),(3764,20),(5943,20),(164490,20),(694335,20),(11225015,20),(49529173,20),(212395644,20),(25265256,20),(1231859761,20),(15398315115,20),(356099691,20)],
  .scan 3 16406489085,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [6409794465,1602448608,400612140,100153044,25038252,6259572,1564884,391236,97812,24444,6120,1524,384,84,24,12] 1 [(.D2,16406489091),(.D0,356099692),(.D0,15398315116),(.D0,1231859762),(.D0,25265257),(.D0,212395645),(.D0,49529174),(.D0,11225016),(.D0,694336),(.D0,164491),(.D0,5944),(.D0,3765),(.D0,266)],
  .batch [752383572] 4273196303 [(.D5,14269890939),(.D1,15338965168),(.D4,1221968103),(.D0,23616647),(.D5,212120876),(.D4,49483378),(.D1,11217384),(.D0,693064),(.D2,164278),(.D3,5908),(.D5,3758),(.D3,265)],
  .scan 0 50,
  .scan2 5 9 [(4649388088,4),(14081795046,4),(15307615851,4),(1216743217,4),(22745832,4),(211975740,4),(49459189,4),(11213351,4),(692391,4),(164166,4),(5889,4),(3755,4)],
  .scan 5 264,
  .scan 0 10,
  .scan2 3 0 [(264,20),(3755,20),(5889,20),(164166,20),(692391,20),(11213351,20),(49459189,20),(211975740,20),(22745832,20),(1216743217,20),(15307615851,20),(14081795046,20)],
  .scan 3 4649388083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [13060694013] 1 [(.D2,4649388089),(.D0,14081795047),(.D0,15307615852),(.D0,1216743218),(.D0,22745833),(.D0,211975741),(.D0,49459190),(.D0,11213352),(.D0,692392),(.D0,164167),(.D0,5890),(.D0,3756),(.D0,264)],
  .scan 0 50,
  .scan2 5 9 [(6530347006,4),(1384214585,4),(13537599462,4),(15216916587,4),(1201626673,4),(20226408,4),(211555836,4),(49389205,4),(11201687,4),(690447,4),(163842,4),(5835,4),(3746,4)],
  .scan 5 262,
  .scan 0 10,
  .scan2 3 0 [(262,20),(3746,20),(5835,20),(163842,20),(690447,20),(11201687,20),(49389205,20),(211555836,20),(20226408,20),(1201626673,20),(15216916587,20),(13537599462,20),(1384214585,20)],
  .scan 3 6530347001,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [19591041023,4897760256,1224440064,306110016,76527504,19131876,4782968,1195740,298936,74736,18684,4670,1168,290,72,18,6,2,2] 1 [(.D2,6530347007),(.D0,1384214586),(.D0,13537599463),(.D0,15216916588),(.D0,1201626674),(.D0,20226409),(.D0,211555837),(.D0,49389206),(.D0,11201688),(.D0,690448),(.D0,163843),(.D0,5836),(.D0,3747),(.D0,262)],
  .batch [2] 13060694016 [(.D1,1)],
  .batch [887470250,221867564,55466890,13866722,3466680,866670,216670,54168,13542,3384,846,212,52,14,4,1253972610] 13060694017 [(.D5,295823416),(.D5,13356200934),(.D5,15186683499),(.D5,1196587825),(.D5,19386600),(.D5,211415868),(.D5,49365877),(.D5,11197799),(.D5,689799),(.D5,163734),(.D5,5817),(.D5,3743),(.D1,262)],
  .scan 0 50,
  .scan2 5 9 [(14279327155,4),(12993403879,4),(15126217323,4),(1186510129,4),(17706984,4),(211135932,4),(49319221,4),(11190023,4),(688503,4),(163518,4),(5781,4),(3737,4)],
  .scan 5 260,
  .scan 0 10,
  .scan2 3 0 [(260,20),(3737,20),(5781,20),(163518,20),(688503,20),(11190023,20),(49319221,20),(211135932,20),(17706984,20),(1186510129,20),(15126217323,20),(12993403879,20)],
  .scan 3 14279327150,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [13060694013] 1 [(.D2,14279327156),(.D0,12993403880),(.D0,15126217324),(.D0,1186510130),(.D0,17706985),(.D0,211135933),(.D0,49319222),(.D0,11190024),(.D0,688504),(.D0,163519),(.D0,5782),(.D0,3738),(.D0,260)],
  .scan 0 50,
  .scan2 5 9 [(6530347006,4),(11014153652,4),(12449208295,4),(15035518059,4),(1171393585,4),(15187560,4),(210716028,4),(49249237,4),(11178359,4),(686559,4),(163194,4),(5727,4),(3728,4)],
  .scan 5 258,
  .scan 0 10,
  .scan2 3 0 [(258,20),(3728,20),(5727,20),(163194,20),(686559,20),(11178359,20),(49249237,20),(210716028,20),(15187560,20),(1171393585,20),(15035518059,20),(12449208295,20),(11014153652,20)],
  .scan 3 6530347001,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [19591041023,4897760256,1224440064,306110016,76527504,19131876,4782968,1195740,298936,74736,18684,4670,1168,290,72,18,6,2,2] 1 [(.D2,6530347007),(.D0,11014153653),(.D0,12449208296),(.D0,15035518060),(.D0,1171393586),(.D0,15187561),(.D0,210716029),(.D0,49249238),(.D0,11178360),(.D0,686560),(.D0,163195),(.D0,5728),(.D0,3729),(.D0,258)],
  .batch [2] 13060694016 [(.D1,1)],
  .batch [8707129344] 13060694017 [(.D5,9925762483),(.D5,12267809767),(.D5,15005284971),(.D5,1166354737),(.D5,14347752),(.D5,210576060),(.D5,49225909),(.D5,11174471),(.D5,685911),(.D5,163086),(.D5,5709),(.D5,3725),(.D1,258)],
  .scan 0 50,
  .scan2 5 9 [(17414258688,4),(7748980147,4),(11905012711,4),(14944818795,4),(1156277041,4),(12668136,4),(210296124,4),(49179253,4),(11166695,4),(684615,4),(162870,4),(5673,4),(3719,4)],
  .scan 5 256,
  .scan 0 10,
  .scan2 3 0 [(256,20),(3719,20),(5673,20),(162870,20),(684615,20),(11166695,20),(49179253,20),(210296124,20),(12668136,20),(1156277041,20),(14944818795,20),(11905012711,20),(7748980147,20)],
  .scan 3 17414258683,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [52242776069,13060694016,3265173504,816293376,204073344,51018336,12754584,3188646,797162,199290,49822,12456,3114,780,194,48,12,4,1451188220] 1 [(.D2,17414258689),(.D0,7748980148),(.D0,11905012712),(.D0,14944818796),(.D0,1156277042),(.D0,12668137),(.D0,210296125),(.D0,49179254),(.D0,11166696),(.D0,684616),(.D0,162871),(.D0,5674),(.D0,3720),(.D0,256)],
  .scan 0 50,
  .scan2 5 9 [(35554111488,4),(4483806644,4),(11360817127,4),(14854119531,4),(1141160497,4),(10148712,4),(209876220,4),(49109269,4),(11155031,4),(682671,4),(162546,4),(5619,4),(3710,4)],
  .scan 5 254,
  .scan 0 10,
  .scan2 3 0 [(254,20),(3710,20),(5619,20),(162546,20),(682671,20),(11155031,20),(49109269,20),(209876220,20),(10148712,20),(1141160497,20),(14854119531,20),(11360817127,20),(4483806644,20)],
  .scan 3 35554111483,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [78364164093] 1 [(.D2,35554111489),(.D0,4483806645),(.D0,11360817128),(.D0,14854119532),(.D0,1141160498),(.D0,10148713),(.D0,209876221),(.D0,49109270),(.D0,11155032),(.D0,682672),(.D0,162547),(.D0,5620),(.D0,3711),(.D0,254)],
  .scan 0 50,
  .scan2 5 9 [(39182082046,4),(15963070465,4),(1218633140,4),(10816621543,4),(14763420267,4),(1126043953,4),(7629288,4),(209456316,4),(49039285,4),(11143367,4),(680727,4),(162222,4),(5565,4),(3701,4)],
  .scan 5 252,
  .scan 0 10,
  .scan2 3 0 [(252,20),(3701,20),(5565,20),(162222,20),(680727,20),(11143367,20),(49039285,20),(209456316,20),(7629288,20),(1126043953,20),(14763420267,20),(10816621543,20),(1218633140,20),(15963070465,20)],
  .scan 3 39182082041,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [117546246143,29386561536,7346640384,1836660096,459165024,114791256,28697814,7174452,1793612,448404,112102,28026,7004,1752,438,108,28,8,2,2] 1 [(.D2,39182082047),(.D0,15963070466),(.D0,1218633141),(.D0,10816621544),(.D0,14763420268),(.D0,1126043954),(.D0,7629289),(.D0,209456317),(.D0,49039286),(.D0,11143368),(.D0,680728),(.D0,162223),(.D0,5566),(.D0,3702),(.D0,252)],
  .batch [2] 78364164096 [(.D1,1)],
  .batch [2344355508,586088892,146522208,36630564,9157644,2289396,572352,143100,35760,8952,2232,552,144,36,8186161428] 78364164097 [(.D5,9432723456),(.D5,130241972),(.D5,10635223015),(.D5,14733187179),(.D5,1121005105),(.D5,6789480),(.D5,209316348),(.D5,49015957),(.D5,11139479),(.D5,680079),(.D5,162114),(.D5,5547),(.D5,3698),(.D1,252)],
  .scan 0 50,
  .scan2 5 9 [(84020148480,4),(6604731264,4),(10272425961,4),(14672721003,4),(1110927409,4),(5109864,4),(209036412,4),(48969301,4),(11131703,4),(678783,4),(161898,4),(5511,4),(3692,4)],
  .scan 5 250,
  .scan 0 10,
  .scan2 3 0 [(250,20),(3692,20),(5511,20),(161898,20),(678783,20),(11131703,20),(48969301,20),(209036412,20),(5109864,20),(1110927409,20),(14672721003,20),(10272425961,20),(6604731264,20)],
  .scan 3 84020148475,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [78364164093] 1 [(.D2,84020148481),(.D0,6604731265),(.D0,10272425962),(.D0,14672721004),(.D0,1110927410),(.D0,5109865),(.D0,209036413),(.D0,48969302),(.D0,11131704),(.D0,678784),(.D0,161899),(.D0,5512),(.D0,3693),(.D0,250)],
  .scan 0 50,
  .scan2 5 9 [(39182082046,4),(64429107457,4),(3339557760,4),(9728230377,4),(14582021739,4),(1095810865,4),(2590440,4),(208616508,4),(48899317,4),(11120039,4),(676839,4),(161574,4),(5457,4),(3683,4)],
  .scan 5 248,
  .scan 0 10,
  .scan2 3 0 [(248,20),(3683,20),(5457,20),(161574,20),(676839,20),(11120039,20),(48899317,20),(208616508,20),(2590440,20),(1095810865,20),(14582021739,20),(9728230377,20),(3339557760,20),(64429107457,20)],
  .scan 3 39182082041,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [117546246143,29386561536,7346640384,1836660096,459165024,114791256,28697814,7174452,1793612,448404,112102,28026,7004,1752,438,108,28,8,2,2] 1 [(.D2,39182082047),(.D0,64429107458),(.D0,3339557761),(.D0,9728230378),(.D0,14582021740),(.D0,1095810866),(.D0,2590441),(.D0,208616509),(.D0,48899318),(.D0,11120040),(.D0,676840),(.D0,161575),(.D0,5458),(.D0,3684),(.D0,248)],
  .batch [2] 78364164096 [(.D1,1)],
  .batch [40520998668,10130249676,1591527720] 78364164097 [(.D5,57898760448),(.D5,2251166592),(.D5,9546831849),(.D5,14551788651),(.D5,1090772017),(.D5,1750632),(.D5,208476540),(.D5,48875989),(.D5,11116151),(.D5,676191),(.D5,161466),(.D5,5439),(.D5,3680),(.D1,248)],
  .scan 0 50,
  .scan2 5 9 [(104485552128,4),(44838066432,4),(74384256,4),(9184034793,4),(14491322475,4),(1080694321,4),(71016,4),(208196604,4),(48829333,4),(11108375,4),(674895,4),(161250,4),(5403,4),(3674,4)],
  .scan 5 246,
  .scan 0 10,
  .scan2 3 0 [(246,20),(3674,20),(5403,20),(161250,20),(674895,20),(11108375,20),(48829333,20),(208196604,20),(71016,20),(1080694321,20),(14491322475,20),(9184034793,20),(74384256,20),(44838066432,20)],
  .scan 3 104485552123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [8033499789,2008374912,502093728,125523432,31380840,7845192,1961280,490320,122616,30672,7632,1944,432,144,72] 1 [(.D2,104485552129),(.D0,44838066433),(.D0,74384257),(.D0,9184034794),(.D0,14491322476),(.D0,1080694322),(.D0,71017),(.D0,208196605),(.D0,48829334),(.D0,11108376),(.D0,674896),(.D0,161251),(.D0,5404)],
  .batch [317765952] 5355666503 [(.D5,101807718877),(.D5,44391760890),(.D1,9171637418),(.D1,14489256247),(.D0,1080349950),(.D3,13621),(.D1,208187039),(.D5,48827739),(.D0,11108110),(.D3,674851),(.D5,161243),(.D4,5402)],
  .batch [79455168,19844352,4976640,1228608,311040,93312,15552] 5514549479 [(.D5,101728277389),(.D5,44378520642),(.D5,9169430709),(.D5,14488888461),(.D5,1080288652),(.D1,3406),(.D2,208185336),(.D0,48827456),(.D4,11108062),(.D4,674843),(.D4,161241),(.D5,5402),(.D0,3675)],
  .batch [15552] 5567511815 [(.D5,101701796221),(.D5,44374107114),(.D5,9168695121),(.D5,14488765863),(.D5,1080268219),(.D1,1)],
  .batch [12692531520] 5567519591 [(.D5,101701792333),(.D5,44374106466),(.D5,9168695013),(.D5,14488765845),(.D5,1080268216),(.D5,208184768),(.D0,48827361),(.D1,11108047),(.D3,674841),(.D0,161242),(.D0,5402),(.D1,3675),(.D0,246)]
]
lemma chunk_11_ok : q6 cmds_11 cfg_11=some cfg_12:= by decide +kernel
def cmds_12 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(11913785350,4),(98528659453,4),(43845250986,4),(9080552433,4),(14474075415,4),(1077819811,4),(207776700,4),(48759349,4),(11096711,4),(672951,4),(160926,4),(5349,4),(3665,4)],
  .scan 5 244,
  .scan 0 10,
  .scan2 3 0 [(244,20),(3665,20),(5349,20),(160926,20),(672951,20),(11096711,20),(48759349,20),(207776700,20),(1077819811,20),(14474075415,20),(9080552433,20),(43845250986,20),(98528659453,20)],
  .scan 3 11913785345,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [35741356055,8935339014,2233834752,558458688,139614672,34903668,8725916,2181480,545370,136342,34086,8522,2130,532,134,34,8,2,2] 1 [(.D2,11913785351),(.D0,98528659454),(.D0,43845250987),(.D0,9080552434),(.D0,14474075416),(.D0,1077819812),(.D0,207776701),(.D0,48759350),(.D0,11096712),(.D0,672952),(.D0,160927),(.D0,5350),(.D0,3666),(.D0,244)],
  .batch [2] 23827570704 [(.D1,1)],
  .batch [5118170448] 23827570705 [(.D5,96543028560),(.D3,43514312505),(.D2,9025396020),(.D2,14464882680),(.D0,1076287689),(.D5,207521346),(.D3,48716791),(.D4,11089618),(.D0,671770),(.D2,160729),(.D5,5316),(.D3,3660),(.D3,243)],
  .scan 0 50,
  .scan2 5 9 [(26386655928,4),(95263485948,4),(43301055402,4),(8989853169,4),(14458958871,4),(1075300387,4),(207356796,4),(48689365,4),(11085047,4),(671007,4),(160602,4),(5295,4),(3656,4)],
  .scan 5 242,
  .scan 0 10,
  .scan2 3 0 [(242,20),(3656,20),(5295,20),(160602,20),(671007,20),(11085047,20),(48689365,20),(207356796,20),(1075300387,20),(14458958871,20),(8989853169,20),(43301055402,20),(95263485948,20)],
  .scan 3 26386655923,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [78364164093] 1 [(.D2,26386655929),(.D0,95263485949),(.D0,43301055403),(.D0,8989853170),(.D0,14458958872),(.D0,1075300388),(.D0,207356797),(.D0,48689366),(.D0,11085048),(.D0,671008),(.D0,160603),(.D0,5296),(.D0,3657),(.D0,242)],
  .scan 0 50,
  .scan2 5 9 [(39182082046,4),(6795614905,4),(91998312444,4),(42756859818,4),(8899153905,4),(14443842327,4),(1072780963,4),(206936892,4),(48619381,4),(11073383,4),(669063,4),(160278,4),(5241,4),(3647,4)],
  .scan 5 240,
  .scan 0 10,
  .scan2 3 0 [(240,20),(3647,20),(5241,20),(160278,20),(669063,20),(11073383,20),(48619381,20),(206936892,20),(1072780963,20),(14443842327,20),(8899153905,20),(42756859818,20),(91998312444,20),(6795614905,20)],
  .scan 3 39182082041,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [117546246143,29386561536,7346640384,1836660096,459165024,114791256,28697814,7174452,1793612,448404,112102,28026,7004,1752,438,108,28,8,2,2] 1 [(.D2,39182082047),(.D0,6795614906),(.D0,91998312445),(.D0,42756859819),(.D0,8899153906),(.D0,14443842328),(.D0,1072780964),(.D0,206936893),(.D0,48619382),(.D0,11073384),(.D0,669064),(.D0,160279),(.D0,5242),(.D0,3648),(.D0,240)],
  .batch [2] 78364164096 [(.D1,1)],
  .batch [795803690,198950924,49737730,12434432,3108610,777152,194286,48574,12144,3036,758,190,48,12,2] 78364164097 [(.D5,265267896),(.D5,90909921276),(.D5,42575461290),(.D5,8868920817),(.D5,14438803479),(.D5,1071941155),(.D5,206796924),(.D5,48596053),(.D5,11069495),(.D5,668415),(.D5,160170),(.D5,5223),(.D5,3644),(.D1,240)],
  .batch [2] 78894699891 [(.D1,1)],
  .batch [8530284078] 78894699892 [(.D5,90865709960),(.D2,42568092738),(.D0,8867692726),(.D4,14438598797),(.D2,1071907042),(.D2,206791239),(.D4,48595105),(.D1,11069338),(.D3,668389),(.D5,160166),(.D2,5223),(.D0,3645),(.D2,239)],
  .scan 0 50,
  .scan2 5 9 [(83159841930,4),(88733138940,4),(42212664234,4),(8808454641,4),(14428725783,4),(1070261539,4),(206516988,4),(48549397,4),(11061719,4),(667119,4),(159954,4),(5187,4),(3638,4)],
  .scan 5 238,
  .scan 0 10,
  .scan2 3 0 [(238,20),(3638,20),(5187,20),(159954,20),(667119,20),(11061719,20),(48549397,20),(206516988,20),(1070261539,20),(14428725783,20),(8808454641,20),(42212664234,20),(88733138940,20)],
  .scan 3 83159841925,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [78364164093] 1 [(.D2,83159841931),(.D0,88733138941),(.D0,42212664235),(.D0,8808454642),(.D0,14428725784),(.D0,1070261540),(.D0,206516989),(.D0,48549398),(.D0,11061720),(.D0,667120),(.D0,159955),(.D0,5188),(.D0,3639),(.D0,238)],
  .scan 0 50,
  .scan2 5 9 [(39182082046,4),(63568800907,4),(85467965436,4),(41668468650,4),(8717755377,4),(14413609239,4),(1067742115,4),(206097084,4),(48479413,4),(11050055,4),(665175,4),(159630,4),(5133,4),(3629,4)],
  .scan 5 236,
  .scan 0 10,
  .scan2 3 0 [(236,20),(3629,20),(5133,20),(159630,20),(665175,20),(11050055,20),(48479413,20),(206097084,20),(1067742115,20),(14413609239,20),(8717755377,20),(41668468650,20),(85467965436,20),(63568800907,20)],
  .scan 3 39182082041,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [117546246143,29386561536,7346640384,1836660096,459165024,114791256,28697814,7174452,1793612,448404,112102,28026,7004,1752,438,108,28,8,2,2] 1 [(.D2,39182082047),(.D0,63568800908),(.D0,85467965437),(.D0,41668468651),(.D0,8717755378),(.D0,14413609240),(.D0,1067742116),(.D0,206097085),(.D0,48479414),(.D0,11050056),(.D0,665176),(.D0,159631),(.D0,5134),(.D0,3630),(.D0,236)],
  .batch [2] 78364164096 [(.D1,1)],
  .batch [52242776064] 78364164097 [(.D5,57038453898),(.D5,84379574268),(.D5,41487070122),(.D5,8687522289),(.D5,14408570391),(.D5,1066902307),(.D5,205957116),(.D5,48456085),(.D5,11046167),(.D5,664527),(.D5,159522),(.D5,5115),(.D5,3626),(.D1,236)],
  .scan 0 50,
  .scan2 5 9 [(104485552128,4),(43977759882,4),(82202791932,4),(41124273066,4),(8627056113,4),(14398492695,4),(1065222691,4),(205677180,4),(48409429,4),(11038391,4),(663231,4),(159306,4),(5079,4),(3620,4)],
  .scan 5 234,
  .scan 0 10,
  .scan2 3 0 [(234,20),(3620,20),(5079,20),(159306,20),(663231,20),(11038391,20),(48409429,20),(205677180,20),(1065222691,20),(14398492695,20),(8627056113,20),(41124273066,20),(82202791932,20),(43977759882,20)],
  .scan 3 104485552123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [313456656389,78364164096,19591041024,4897760256,1224440064,306110016,76527504,19131876,4782968,1195744,298934,74734,18684,4670,1168,294,72,18,6,8707129340] 1 [(.D2,104485552129),(.D0,43977759883),(.D0,82202791933),(.D0,41124273067),(.D0,8627056114),(.D0,14398492696),(.D0,1065222692),(.D0,205677181),(.D0,48409430),(.D0,11038392),(.D0,663232),(.D0,159307),(.D0,5080),(.D0,3621),(.D0,234)],
  .scan 0 50,
  .scan2 5 9 [(213324668928,4),(24386718859,4),(78937618428,4),(40580077482,4),(8536356849,4),(14383376151,4),(1062703267,4),(205257276,4),(48339445,4),(11026727,4),(661287,4),(158982,4),(5025,4),(3611,4)],
  .scan 5 232,
  .scan 0 10,
  .scan2 3 0 [(232,20),(3611,20),(5025,20),(158982,20),(661287,20),(11026727,20),(48339445,20),(205257276,20),(1062703267,20),(14383376151,20),(8536356849,20),(40580077482,20),(78937618428,20),(24386718859,20)],
  .scan 3 213324668923,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [438960939489,31224045084] 1 [(.D2,213324668929),(.D0,24386718860),(.D0,78937618429),(.D0,40580077483),(.D0,8536356850),(.D0,14383376152),(.D0,1062703268),(.D0,205257277),(.D0,48339446),(.D0,11026728),(.D0,661288),(.D0,158983),(.D0,5026),(.D0,3612),(.D0,232)],
  .scan 0 50,
  .scan2 5 9 [(235092492286,4),(95778422785,4),(4795677835,4),(75672444924,4),(40035881898,4),(8445657585,4),(14368259607,4),(1060183843,4),(204837372,4),(48269461,4),(11015063,4),(659343,4),(158658,4),(4971,4),(3602,4)],
  .scan 5 230,
  .scan 0 10,
  .scan2 3 0 [(230,20),(3602,20),(4971,20),(158658,20),(659343,20),(11015063,20),(48269461,20),(204837372,20),(1060183843,20),(14368259607,20),(8445657585,20),(40035881898,20),(75672444924,20),(4795677835,20),(95778422785,20)],
  .scan 3 235092492281,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [517933206357,129483301536,32370825312,8092706328,2023176672,505794096,126448560,31612176,7903008,1975752,493992,123408,30888,7704,1944,504,144,72,72] 1 [(.D2,235092492287),(.D0,95778422786),(.D0,4795677836),(.D0,75672444925),(.D0,40035881899),(.D0,8445657586),(.D0,14368259608),(.D0,1060183844),(.D0,204837373),(.D0,48269462),(.D0,11015064),(.D0,659344),(.D0,158659),(.D0,4972),(.D0,3603),(.D0,230)],
  .batch [187344270466,46836067618,11709016904,2927254228,731813556,182953388,45738348,11434588,2858646,714662,178666,44666,11166,2790,700,174,44,10,2,2,2] 345288804263 [(.D5,62448090155),(.D5,67004355763),(.D1,74873165285),(.D4,39902668625),(.D4,8423455373),(.D2,14364559239),(.D0,1059567116),(.D2,204734584),(.D5,48252330),(.D2,11012208),(.D1,658868),(.D5,158579),(.D4,4958),(.D2,3600),(.D1,230)],
  .batch [2] 470184984576 [(.D1,1)],
  .batch [17549392668] 470184984577 [(.D5,56596340736),(.D1,73138496114),(.D4,39613557096),(.D5,8375270118),(.D3,14356528363),(.D3,1058228636),(.D1,204511505),(.D3,48215150),(.D3,11006012),(.D4,657834),(.D3,158407),(.D5,4929),(.D3,3596),(.D4,228)],
  .scan 0 50,
  .scan2 5 9 [(478959680910,4),(52208992569,4),(72407271418,4),(39491686314,4),(8354958321,4),(14353143063,4),(1057664419,4),(204417468,4),(48199477,4),(11003399,4),(657399,4),(158334,4),(4917,4),(3593,4)],
  .scan 5 228,
  .scan 0 10,
  .scan2 3 0 [(228,20),(3593,20),(4917,20),(158334,20),(657399,20),(11003399,20),(48199477,20),(204417468,20),(1057664419,20),(14353143063,20),(8354958321,20),(39491686314,20),(72407271418,20),(52208992569,20)],
  .scan 3 478959680905,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [470184984573] 1 [(.D2,478959680911),(.D0,52208992570),(.D0,72407271419),(.D0,39491686315),(.D0,8354958322),(.D0,14353143064),(.D0,1057664420),(.D0,204417469),(.D0,48199478),(.D0,11003400),(.D0,657400),(.D0,158335),(.D0,4918),(.D0,3594),(.D0,228)],
  .scan 0 50,
  .scan2 5 9 [(235092492286,4),(361413434767,4),(32617951545,4),(69142097914,4),(38947490730,4),(8264259057,4),(14338026519,4),(1055144995,4),(203997564,4),(48129493,4),(10991735,4),(655455,4),(158010,4),(4863,4),(3584,4)],
  .scan 5 226,
  .scan 0 10,
  .scan2 3 0 [(226,20),(3584,20),(4863,20),(158010,20),(655455,20),(10991735,20),(48129493,20),(203997564,20),(1055144995,20),(14338026519,20),(8264259057,20),(38947490730,20),(69142097914,20),(32617951545,20),(361413434767,20)],
  .scan 3 235092492281,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [705277476863,176319369216,44079842304,11019960576,2754990144,688747536,172186884,43046720,10761678,2690422,672606,168150,42038,10510,2628,656,162,42,10,2,2,2] 1 [(.D2,235092492287),(.D0,361413434768),(.D0,32617951546),(.D0,69142097915),(.D0,38947490731),(.D0,8264259058),(.D0,14338026520),(.D0,1055144996),(.D0,203997565),(.D0,48129494),(.D0,10991736),(.D0,655456),(.D0,158011),(.D0,4864),(.D0,3585),(.D0,226)],
  .batch [2] 470184984576 [(.D1,1)],
  .batch [313456656384] 470184984577 [(.D5,322231352718),(.D5,26087604537),(.D5,68053706746),(.D5,38766092202),(.D5,8234025969),(.D5,14332987671),(.D5,1054305187),(.D5,203857596),(.D5,48106165),(.D5,10987847),(.D5,654807),(.D5,157902),(.D5,4845),(.D5,3581),(.D1,226)]
]
lemma chunk_12_ok : q6 cmds_12 cfg_12=some cfg_13:= by decide +kernel
def cmds_13 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(626913312768,4),(243867188622,4),(13026910521,4),(65876924410,4),(38403295146,4),(8173559793,4),(14322909975,4),(1052625571,4),(203577660,4),(48059509,4),(10980071,4),(653511,4),(157686,4),(4809,4),(3575,4)],
  .scan 5 224,
  .scan 0 10,
  .scan2 3 0 [(224,20),(3575,20),(4809,20),(157686,20),(653511,20),(10980071,20),(48059509,20),(203577660,20),(1052625571,20),(14322909975,20),(8173559793,20),(38403295146,20),(65876924410,20),(13026910521,20),(243867188622,20)],
  .scan 3 626913312763,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1406906336445,351726584040,87931646064,21982911480,5495727888,1373931936,343482984,85870800,21467664,5366880,1341792,335448,83808,20952,5256,1296,360,72] 1 [(.D2,626913312769),(.D0,243867188623),(.D0,13026910522),(.D0,65876924411),(.D0,38403295147),(.D0,8173559794),(.D0,14322909976),(.D0,1052625572),(.D0,203577661),(.D0,48059510),(.D0,10980072),(.D0,653512),(.D0,157687),(.D0,4810),(.D0,3576),(.D0,224)],
  .batch [157539132072] 937937557583 [(.D5,157944533977),(.D5,165705725490),(.D1,63705772658),(.D4,38041436520),(.D5,8113250022),(.D3,14312858347),(.D3,1050950300),(.D1,203298449),(.D3,48012974),(.D3,10972316),(.D4,652218),(.D3,157471),(.D5,4773),(.D5,3569),(.D3,223)],
  .scan 0 50,
  .scan2 5 9 [(1016707123618,4),(118559750959,4),(159141594987,4),(62611750906,4),(37859099562,4),(8082860529,4),(14307793431,4),(1050106147,4),(203157756,4),(47989525,4),(10968407,4),(651567,4),(157362,4),(4755,4),(3566,4)],
  .scan 5 222,
  .scan 0 10,
  .scan2 3 0 [(222,20),(3566,20),(4755,20),(157362,20),(651567,20),(10968407,20),(47989525,20),(203157756,20),(1050106147,20),(14307793431,20),(8082860529,20),(37859099562,20),(62611750906,20),(159141594987,20),(118559750959,20)],
  .scan 3 1016707123613,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2134075517289,533518879320,133379719824,20135791020] 1 [(.D2,1016707123619),(.D0,118559750960),(.D0,159141594988),(.D0,62611750907),(.D0,37859099563),(.D0,8082860530),(.D0,14307793432),(.D0,1050106148),(.D0,203157757),(.D0,47989526),(.D0,10968408),(.D0,651568),(.D0,157363),(.D0,4756),(.D0,3567),(.D0,222)],
  .scan 0 50,
  .scan2 5 9 [(1410554953726,4),(311429646755,4),(1013504815,4),(139550553963,4),(59346577402,4),(37314903978,4),(7992161265,4),(14292676887,4),(1047586723,4),(202737852,4),(47919541,4),(10956743,4),(649623,4),(157038,4),(4701,4),(3557,4)],
  .scan 5 220,
  .scan 0 10,
  .scan2 3 0 [(220,20),(3557,20),(4701,20),(157038,20),(649623,20),(10956743,20),(47919541,20),(202737852,20),(1047586723,20),(14292676887,20),(7992161265,20),(37314903978,20),(59346577402,20),(139550553963,20),(1013504815,20),(311429646755,20)],
  .scan 3 1410554953721,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [109458520197,27364630032,6841157472,1710289296,427572360,106893072,26723304,6680808,1670184,417528,104472,26136,6480,1584,432,144] 1 [(.D2,1410554953727),(.D0,311429646756),(.D0,1013504816),(.D0,139550553964),(.D0,59346577403),(.D0,37314903979),(.D0,7992161266),(.D0,14292676888),(.D0,1047586724),(.D0,202737853),(.D0,47919542),(.D0,10956744),(.D0,649624),(.D0,157039),(.D0,4702)],
  .batch [2796785791776] 72972346751 [(.D5,1374068780351),(.D5,305348617859),(.D3,139381636495),(.D4,59318424490),(.D1,37310211827),(.D1,7991379241),(.D4,14292546549),(.D5,1047565000),(.D3,202734232),(.D1,47918939),(.D0,10956643),(.D1,649607),(.D5,157035),(.D1,4702),(.D0,3558),(.D0,220)],
  .scan 0 50,
  .scan2 5 9 [(1471365242638,4),(674872332407,4),(188815876535,4),(119959512940,4),(56081403898,4),(36770708394,4),(7901462001,4),(14277560343,4),(1045067299,4),(202317948,4),(47849557,4),(10945079,4),(647679,4),(156714,4),(4647,4),(3548,4)],
  .scan 5 218,
  .scan 0 10,
  .scan2 3 0 [(218,20),(3548,20),(4647,20),(156714,20),(647679,20),(10945079,20),(47849557,20),(202317948,20),(1045067299,20),(14277560343,20),(7901462001,20),(36770708394,20),(56081403898,20),(119959512940,20),(188815876535,20),(674872332407,20)],
  .scan 3 1471365242633,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4414095727919,1103523931980,275880982994,68970245748,17242561438,4310640360,1077660090,269415020,67353756,16838440,4209608,1052404,263100,65774,16444,4112,1026,258,64,18,2,2,2] 1 [(.D2,1471365242639),(.D0,674872332408),(.D0,188815876536),(.D0,119959512941),(.D0,56081403899),(.D0,36770708395),(.D0,7901462002),(.D0,14277560344),(.D0,1045067300),(.D0,202317949),(.D0,47849558),(.D0,10945080),(.D0,647680),(.D0,156715),(.D0,4648),(.D0,3549),(.D0,218)],
  .batch [2] 2942730485280 [(.D1,1)],
  .batch [1288934375900,322233593976,80558398494,20139599624,5034899904,1258724976,314681244,78670312,19667580,4916894,1229224,307304,76828,19206,4802,1200,300,76,18,6,2,2] 2942730485281 [(.D5,429644791966),(.D1,147944619796),(.D5,113147636817),(.D4,54946091211),(.D0,36581489614),(.D0,7869925538),(.D3,14272304266),(.D3,1044191287),(.D4,202171946),(.D2,47825224),(.D4,10941023),(.D3,647004),(.D0,156602),(.D3,4629),(.D0,3546),(.D2,217)],
  .batch [20270096308] 3802020069217 [(.D1,76337154467),(.D1,101213059263),(.D3,52956994952),(.D3,36249973570),(.D5,7814672864),(.D2,14263095487),(.D1,1042656491),(.D4,201916146),(.D3,47782591),(.D4,10933918),(.D0,645820),(.D4,156404),(.D2,4596),(.D4,3539),(.D5,216)],
  .scan 0 50,
  .scan2 5 9 [(3812155117370,4),(71269630389,4),(100368471916,4),(52816230394,4),(36226512810,4),(7810762737,4),(14262443799,4),(1042547875,4),(201898044,4),(47779573,4),(10933415,4),(645735,4),(156390,4),(4593,4),(3539,4)],
  .scan 5 216,
  .scan 0 10,
  .scan2 3 0 [(216,20),(3539,20),(4593,20),(156390,20),(645735,20),(10933415,20),(47779573,20),(201898044,20),(1042547875,20),(14262443799,20),(7810762737,20),(36226512810,20),(52816230394,20),(100368471916,20),(71269630389,20)],
  .scan 3 3812155117365,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1282853347029,320713336740,80178334188,20044583544,5011145892,1252786464,313196616,78299160,19574796,4893696,1223424,305856,76464,19116,4776,1200,288,72,24,12] 1 [(.D2,3812155117371),(.D0,71269630390),(.D0,100368471917),(.D0,52816230395),(.D0,36226512811),(.D0,7810762738),(.D0,14262443800),(.D0,1042547876),(.D0,201898045),(.D0,47779574),(.D0,10933416),(.D0,645736),(.D0,156391),(.D0,4594),(.D0,3540),(.D0,216)],
  .batch [12] 855235564679 [(.D5,3384537335031),(.D1,1)],
  .batch [185106463008] 855235564685 [(.D5,3384537335028),(.D1,88490200185),(.D1,50836518440),(.D0,35896560818),(.D3,7755770739),(.D0,14253278467),(.D2,1041020320),(.D2,201643452),(.D0,47737142),(.D4,10926343),(.D4,644556),(.D5,156194),(.D4,4560),(.D3,3534),(.D3,215)],
  .scan 0 50,
  .scan2 5 9 [(947788796188,4),(3338260719276,4),(80777430892,4),(49551056890,4),(35682317226,4),(7720063473,4),(14247327255,4),(1040028451,4),(201478140,4),(47709589,4),(10921751,4),(643791,4),(156066,4),(4539,4),(3530,4)],
  .scan 5 214,
  .scan 0 10,
  .scan2 3 0 [(214,20),(3530,20),(4539,20),(156066,20),(643791,20),(10921751,20),(47709589,20),(201478140,20),(1040028451,20),(14247327255,20),(7720063473,20),(35682317226,20),(49551056890,20),(80777430892,20),(3338260719276,20)],
  .scan 3 947788796183,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2821109907453] 1 [(.D2,947788796189),(.D0,3338260719277),(.D0,80777430893),(.D0,49551056891),(.D0,35682317227),(.D0,7720063474),(.D0,14247327256),(.D0,1040028452),(.D0,201478141),(.D0,47709590),(.D0,10921752),(.D0,643792),(.D0,156067),(.D0,4540),(.D0,3531),(.D0,214)],
  .scan 0 50,
  .scan2 5 9 [(1410554953726,4),(242511319325,4),(3220714473132,4),(61186389868,4),(46285883386,4),(35138121642,4),(7629364209,4),(14232210711,4),(1037509027,4),(201058236,4),(47639605,4),(10910087,4),(641847,4),(155742,4),(4485,4),(3521,4)],
  .scan 5 212,
  .scan 0 10,
  .scan2 3 0 [(212,20),(3521,20),(4485,20),(155742,20),(641847,20),(10910087,20),(47639605,20),(201058236,20),(1037509027,20),(14232210711,20),(7629364209,20),(35138121642,20),(46285883386,20),(61186389868,20),(3220714473132,20),(242511319325,20)],
  .scan 3 1410554953721,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4231664861183,1057916215296,264479053824,66119763456,16529940864,4132485216,1033121304,258280326,64570080,16142520,4035630,1008908,252226,63056,15766,3942,984,246,62,16,2,2,2] 1 [(.D2,1410554953727),(.D0,242511319326),(.D0,3220714473133),(.D0,61186389869),(.D0,46285883387),(.D0,35138121643),(.D0,7629364210),(.D0,14232210712),(.D0,1037509028),(.D0,201058237),(.D0,47639606),(.D0,10910088),(.D0,641848),(.D0,155743),(.D0,4486),(.D0,3522),(.D0,212)],
  .batch [2] 2821109907456 [(.D1,1)],
  .batch [22256481110,5564120280,1391030070,347757516,86939378,21734844,5433712,1358430,339606,84902,21226,5306,1326,330,84,22,6,308510771690] 2821109907457 [(.D5,7418827036),(.D5,3181532391084),(.D5,54656042860),(.D5,45197492218),(.D5,34956723114),(.D5,7599131121),(.D5,14227171863),(.D5,1036669219),(.D5,200918268),(.D5,47616277),(.D5,10906199),(.D5,641199),(.D5,155634),(.D5,4467),(.D5,3518),(.D1,212)],
  .scan 0 50,
  .scan2 5 9 [(2990202947375,4),(3103168226989,4),(41595348844,4),(43020709882,4),(34593926058,4),(7538664945,4),(14217094167,4),(1034989603,4),(200638332,4),(47569621,4),(10898423,4),(639903,4),(155418,4),(4431,4),(3512,4)],
  .scan 5 210,
  .scan 0 10,
  .scan2 3 0 [(210,20),(3512,20),(4431,20),(155418,20),(639903,20),(10898423,20),(47569621,20),(200638332,20),(1034989603,20),(14217094167,20),(7538664945,20),(34593926058,20),(43020709882,20),(41595348844,20),(3103168226989,20)],
  .scan 3 2990202947370,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2821109907453] 1 [(.D2,2990202947376),(.D0,3103168226990),(.D0,41595348845),(.D0,43020709883),(.D0,34593926059),(.D0,7538664946),(.D0,14217094168),(.D0,1034989604),(.D0,200638333),(.D0,47569622),(.D0,10898424),(.D0,639904),(.D0,155419),(.D0,4432),(.D0,3513),(.D0,210)],
  .scan 0 50,
  .scan2 5 9 [(1410554953726,4),(2284925470512,4),(2985621980845,4),(22004307820,4),(39755536378,4),(34049730474,4),(7447965681,4),(14201977623,4),(1032470179,4),(200218428,4),(47499637,4),(10886759,4),(637959,4),(155094,4),(4377,4),(3503,4)],
  .scan 5 208,
  .scan 0 10,
  .scan2 3 0 [(208,20),(3503,20),(4377,20),(155094,20),(637959,20),(10886759,20),(47499637,20),(200218428,20),(1032470179,20),(14201977623,20),(7447965681,20),(34049730474,20),(39755536378,20),(22004307820,20),(2985621980845,20),(2284925470512,20)],
  .scan 3 1410554953721,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4231664861183,1057916215296,264479053824,66119763456,16529940864,4132485216,1033121304,258280326,64570080,16142520,4035630,1008908,252226,63056,15766,3942,984,246,62,16,2,2,2] 1 [(.D2,1410554953727),(.D0,2284925470513),(.D0,2985621980846),(.D0,22004307821),(.D0,39755536379),(.D0,34049730475),(.D0,7447965682),(.D0,14201977624),(.D0,1032470180),(.D0,200218429),(.D0,47499638),(.D0,10886760),(.D0,637960),(.D0,155095),(.D0,4378),(.D0,3504),(.D0,208)],
  .batch [2] 2821109907456 [(.D1,1)],
  .batch [1671187767768,209552170536] 2821109907457 [(.D5,2049832978223),(.D5,2946439898797),(.D5,15473960812),(.D5,38667145210),(.D5,33868331946),(.D5,7417732593),(.D5,14196938775),(.D5,1031630371),(.D5,200078460),(.D5,47476309),(.D5,10882871),(.D5,637311),(.D5,154986),(.D5,4359),(.D5,3500),(.D1,208)],
  .scan 0 50,
  .scan2 5 9 [(3761479876608,4),(1579647993647,4),(2868075734701,4),(2413266796,4),(36490362874,4),(33505534890,4),(7357266417,4),(14186861079,4),(1029950755,4),(199798524,4),(47429653,4),(10875095,4),(636015,4),(154770,4),(4323,4),(3494,4)],
  .scan 5 206,
  .scan 0 10,
  .scan2 3 0 [(206,20),(3494,20),(4323,20),(154770,20),(636015,20),(10875095,20),(47429653,20),(199798524,20),(1029950755,20),(14186861079,20),(7357266417,20),(33505534890,20),(36490362874,20),(2413266796,20),(2868075734701,20),(1579647993647,20)],
  .scan 3 3761479876603,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1563796884669,390949221168,97737305184,24434326080,6108581952,1527145488,381786048,95446512,23861952,5965488,1490832,372816,93312,23328,5616,1296,864] 1 [(.D2,3761479876609),(.D0,1579647993648),(.D0,2868075734702),(.D0,2413266797),(.D0,36490362875),(.D0,33505534891),(.D0,7357266418),(.D0,14186861080),(.D0,1029950756),(.D0,199798525),(.D0,47429654),(.D0,10875096),(.D0,636016),(.D0,154771),(.D0,4324),(.D0,3495)],
  .batch [2473599488112] 1042531256303 [(.D5,3240214248457),(.D5,1492770388955),(.D5,2853596133919),(.D3,36088151742),(.D5,33438499701),(.D1,7346093887),(.D2,14184998991),(.D4,1029640407),(.D0,199746800),(.D1,47421033),(.D5,10873658),(.D3,635776),(.D3,154731),(.D2,4317),(.D4,3493),(.D0,206)],
  .scan 0 50,
  .scan2 5 9 [(2279331000358,4),(2621814376429,4),(1389703743617,4),(2836418359696,4),(33225189371,4),(32961339306,4),(7266567153,4),(14171744535,4),(1027431331,4),(199378620,4),(47359669,4),(10863431,4),(634071,4),(154446,4),(4269,4),(3485,4)],
  .scan 5 204,
  .scan 0 10,
  .scan2 3 0 [(204,20),(3485,20),(4269,20),(154446,20),(634071,20),(10863431,20),(47359669,20),(199378620,20),(1027431331,20),(14171744535,20),(7266567153,20),(32961339306,20),(33225189371,20),(2836418359696,20),(1389703743617,20),(2621814376429,20)],
  .scan 3 2279331000353,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [6837993001079,1709498250270,427374562566,106843640642,26710910160,6677727540,1669431886,417357972,104339492,26084872,6521220,1630304,407574,101896,25472,6370,1592,396,100,26,6,2,2] 1 [(.D2,2279331000359),(.D0,2621814376430),(.D0,1389703743618),(.D0,2836418359697),(.D0,33225189372),(.D0,32961339307),(.D0,7266567154),(.D0,14171744536),(.D0,1027431332),(.D0,199378621),(.D0,47359670),(.D0,10863432),(.D0,634072),(.D0,154447),(.D0,4270),(.D0,3486),(.D0,204)],
  .batch [2] 4558662000720 [(.D1,1)],
  .batch [1301555907216] 4558662000721 [(.D5,2241925876368),(.D5,1326388993607),(.D1,2825865901362),(.D3,31466446316),(.D0,32668215464),(.D5,7217713179),(.D1,14163602207),(.D1,1026074277),(.D5,199152444),(.D3,47321974),(.D2,10857149),(.D0,633025),(.D2,154272),(.D2,4240),(.D1,3481),(.D3,203)],
  .scan 0 50,
  .scan2 5 9 [(5209439954328,4),(1916536899564,4),(1272157497473,4),(2816827318672,4),(29960015867,4),(32417143722,4),(7175867889,4),(14156627991,4),(1024911907,4),(198958716,4),(47289685,4),(10851767,4),(632127,4),(154122,4),(4215,4),(3476,4)],
  .scan 5 202,
  .scan 0 10,
  .scan2 3 0 [(202,20),(3476,20),(4215,20),(154122,20),(632127,20),(10851767,20),(47289685,20),(198958716,20),(1024911907,20),(14156627991,20),(7175867889,20),(32417143722,20),(29960015867,20),(2816827318672,20),(1272157497473,20),(1916536899564,20)],
  .scan 3 5209439954323,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [15628319862989,1298339581744] 1 [(.D2,5209439954329),(.D0,1916536899565),(.D0,1272157497474),(.D0,2816827318673),(.D0,29960015868),(.D0,32417143723),(.D0,7175867890),(.D0,14156627992),(.D0,1024911908),(.D0,198958717),(.D0,47289686),(.D0,10851768),(.D0,632128),(.D0,154123),(.D0,4216),(.D0,3477),(.D0,202)],
  .scan 0 50,
  .scan2 5 9 [(8463329722366,4),(977775093145,4),(1211259422700,4),(1154611251329,4),(2797236277648,4),(26694842363,4),(31872948138,4),(7085168625,4),(14141511447,4),(1022392483,4),(198538812,4),(47219701,4),(10840103,4),(630183,4),(153798,4),(4161,4),(3467,4)],
  .scan 5 200,
  .scan 0 10,
  .scan2 3 0 [(200,20),(3467,20),(4161,20),(153798,20),(630183,20),(10840103,20),(47219701,20),(198538812,20),(1022392483,20),(14141511447,20),(7085168625,20),(31872948138,20),(26694842363,20),(2797236277648,20),(1154611251329,20),(1211259422700,20),(977775093145,20)],
  .scan 3 8463329722361,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [17599951676637,4399987919148,1099996979796,274999244940,68749811244,17187452796,4296863196,1074215808,268553952,67138488,16784628,4196160,1049040,262260,65556,16392,4092,1020,252,72,24,7790037490474,1947509372620,486877343156,121719335788,30429833948,7607458486,1901864622,475466156,118866538,29716634,7429158,1857292,464322,116082,29018,7254,1816,452,114,28,8,438140403024] 1 [(.D2,8463329722367),(.D0,977775093146),(.D0,1211259422701),(.D0,1154611251330),(.D0,2797236277649),(.D0,26694842364),(.D0,31872948139),(.D0,7085168626),(.D0,14141511448),(.D0,1022392484),(.D0,198538813),(.D0,47219702),(.D0,10840104),(.D0,630184),(.D0,153799),(.D0,4162),(.D0,3468),(.D0,200)]
]
lemma chunk_13_ok : q6 cmds_13 cfg_13=some cfg_14:= by decide +kernel
def cmds_14 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(17145729646245,4),(505981945839,4),(1037065005185,4),(2777645236624,4),(23429668859,4),(31328752554,4),(6994469361,4),(14126394903,4),(1019873059,4),(198118908,4),(47149717,4),(10828439,4),(628239,4),(153474,4),(4107,4),(3458,4)],
  .scan 5 198,
  .scan 0 10,
  .scan2 3 0 [(198,20),(3458,20),(4107,20),(153474,20),(628239,20),(10828439,20),(47149717,20),(198118908,20),(1019873059,20),(14126394903,20),(6994469361,20),(31328752554,20),(23429668859,20),(2777645236624,20),(1037065005185,20),(505981945839,20)],
  .scan 3 17145729646240,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [9107675025129,2276918756280,569229689064,142307422260,35576855568,8894213892,2223553476,555888372,138972096,34743024,8685756,2171424,542868,135720,33924,8484,2124,516,132,36,12] 1 [(.D2,17145729646246),(.D0,505981945840),(.D0,1037065005186),(.D0,2777645236625),(.D0,23429668860),(.D0,31328752555),(.D0,6994469362),(.D0,14126394904),(.D0,1019873060),(.D0,198118909),(.D0,47149718),(.D0,10828440),(.D0,628240),(.D0,153475),(.D0,4108),(.D0,3459),(.D0,198)],
  .batch [797182124100] 6071783350079 [(.D5,14109837971206),(.D1,952734680880),(.D0,2763590182574),(.D2,21087159851),(.D4,30938334386),(.D2,6929399667),(.D0,14115549955),(.D2,1018065568),(.D2,197817660),(.D0,47099510),(.D4,10820071),(.D4,626844),(.D5,153242),(.D4,4068),(.D1,3453),(.D4,196)],
  .scan 0 50,
  .scan2 5 9 [(6470374412128,4),(13910542440181,4),(919518759041,4),(2758054195600,4),(20164495355,4),(30784556970,4),(6903770097,4),(14111278359,4),(1017353635,4),(197699004,4),(47079733,4),(10816775,4),(626295,4),(153150,4),(4053,4),(3449,4)],
  .scan 5 196,
  .scan 0 10,
  .scan2 3 0 [(196,20),(3449,20),(4053,20),(153150,20),(626295,20),(10816775,20),(47079733,20),(197699004,20),(1017353635,20),(14111278359,20),(6903770097,20),(30784556970,20),(20164495355,20),(2758054195600,20),(919518759041,20),(13910542440181,20)],
  .scan 3 6470374412123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [16926659444733] 1 [(.D2,6470374412129),(.D0,13910542440182),(.D0,919518759042),(.D0,2758054195601),(.D0,20164495356),(.D0,30784556971),(.D0,6903770098),(.D0,14111278360),(.D0,1017353636),(.D0,197699005),(.D0,47079734),(.D0,10816776),(.D0,626296),(.D0,153151),(.D0,4054),(.D0,3450),(.D0,196)],
  .scan 0 50,
  .scan2 5 9 [(8463329722366,4),(2238709550945,4),(13205264963317,4),(801972512897,4),(2738463154576,4),(16899321851,4),(30240361386,4),(6813070833,4),(14096161815,4),(1014834211,4),(197279100,4),(47009749,4),(10805111,4),(624351,4),(152826,4),(3999,4),(3440,4)],
  .scan 5 194,
  .scan 0 10,
  .scan2 3 0 [(194,20),(3440,20),(3999,20),(152826,20),(624351,20),(10805111,20),(47009749,20),(197279100,20),(1014834211,20),(14096161815,20),(6813070833,20),(30240361386,20),(16899321851,20),(2738463154576,20),(801972512897,20),(13205264963317,20),(2238709550945,20)],
  .scan 3 8463329722361,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [25389989167103,6347497291776,1586874322944,396718580736,99179645184,24794911296,6198727824,1549681956,387420488,96855120,24213780,6053446,1513362,378342,94584,23646,5912,1476,370,92,24,6,2,2] 1 [(.D2,8463329722367),(.D0,2238709550946),(.D0,13205264963318),(.D0,801972512898),(.D0,2738463154577),(.D0,16899321852),(.D0,30240361387),(.D0,6813070834),(.D0,14096161816),(.D0,1014834212),(.D0,197279101),(.D0,47009750),(.D0,10805112),(.D0,624352),(.D0,152827),(.D0,4000),(.D0,3441),(.D0,194)],
  .batch [2] 16926659444736 [(.D1,1)],
  .batch [2484463791650,621115947914,155278986978,38819746744,9704936688,2426234172,606558542,151639636,37909908,9477476,2369370,592342,148086,37022,9256,2312,580,144,36,8,4,1328636873490] 16926659444737 [(.D5,828154597216),(.D5,12970172471029),(.D5,762790430849),(.D5,2731932807568),(.D5,15810930683),(.D5,30058962858),(.D5,6782837745),(.D5,14091122967),(.D5,1013994403),(.D5,197139132),(.D5,46986421),(.D5,10801223),(.D5,623703),(.D5,152718),(.D5,3981),(.D5,3437),(.D1,194)],
  .scan 0 50,
  .scan2 5 9 [(19247287075915,4),(12499987486454,4),(684426266753,4),(2718872113552,4),(13634148347,4),(29696165802,4),(6722371569,4),(14081045271,4),(1012314787,4),(196859196,4),(46939765,4),(10793447,4),(622407,4),(152502,4),(3945,4),(3431,4)],
  .scan 5 192,
  .scan 0 10,
  .scan2 3 0 [(192,20),(3431,20),(3945,20),(152502,20),(622407,20),(10793447,20),(46939765,20),(196859196,20),(1012314787,20),(14081045271,20),(6722371569,20),(29696165802,20),(13634148347,20),(2718872113552,20),(684426266753,20),(12499987486454,20)],
  .scan 3 19247287075910,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [16926659444733] 1 [(.D2,19247287075916),(.D0,12499987486455),(.D0,684426266754),(.D0,2718872113553),(.D0,13634148348),(.D0,29696165803),(.D0,6722371570),(.D0,14081045272),(.D0,1012314788),(.D0,196859197),(.D0,46939766),(.D0,10793448),(.D0,622408),(.D0,152503),(.D0,3946),(.D0,3432),(.D0,192)],
  .scan 0 50,
  .scan2 5 9 [(8463329722366,4),(15015622214732,4),(11794710009590,4),(566880020609,4),(2699281072528,4),(10368974843,4),(29151970218,4),(6631672305,4),(14065928727,4),(1009795363,4),(196439292,4),(46869781,4),(10781783,4),(620463,4),(152178,4),(3891,4),(3422,4)],
  .scan 5 190,
  .scan 0 10,
  .scan2 3 0 [(190,20),(3422,20),(3891,20),(152178,20),(620463,20),(10781783,20),(46869781,20),(196439292,20),(1009795363,20),(14065928727,20),(6631672305,20),(29151970218,20),(10368974843,20),(2699281072528,20),(566880020609,20),(11794710009590,20),(15015622214732,20)],
  .scan 3 8463329722361,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [25389989167103,6347497291776,1586874322944,396718580736,99179645184,24794911296,6198727824,1549681956,387420488,96855120,24213780,6053446,1513362,378342,94584,23646,5912,1476,370,92,24,6,2,2] 1 [(.D2,8463329722367),(.D0,15015622214733),(.D0,11794710009591),(.D0,566880020610),(.D0,2699281072529),(.D0,10368974844),(.D0,29151970219),(.D0,6631672306),(.D0,14065928728),(.D0,1009795364),(.D0,196439293),(.D0,46869782),(.D0,10781784),(.D0,620464),(.D0,152179),(.D0,3892),(.D0,3423),(.D0,190)],
  .batch [2] 16926659444736 [(.D1,1)],
  .batch [11284439629824] 16926659444737 [(.D5,13605067261003),(.D5,11559617517302),(.D5,527697938561),(.D5,2692750725520),(.D5,9280583675),(.D5,28970571690),(.D5,6601439217),(.D5,14060889879),(.D5,1008955555),(.D5,196299324),(.D5,46846453),(.D5,10777895),(.D5,619815),(.D5,152070),(.D5,3873),(.D5,3419),(.D1,190)],
  .scan 0 50,
  .scan2 5 9 [(22568879259648,4),(10783957353547,4),(11089432532726,4),(449333774465,4),(2679690031504,4),(7103801339,4),(28607774634,4),(6540973041,4),(14050812183,4),(1007275939,4),(196019388,4),(46799797,4),(10770119,4),(618519,4),(151854,4),(3837,4),(3413,4)],
  .scan 5 188,
  .scan 0 10,
  .scan2 3 0 [(188,20),(3413,20),(3837,20),(151854,20),(618519,20),(10770119,20),(46799797,20),(196019388,20),(1007275939,20),(14050812183,20),(6540973041,20),(28607774634,20),(7103801339,20),(2679690031504,20),(449333774465,20),(11089432532726,20),(10783957353547,20)],
  .scan 3 22568879259643,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [67706637778949,16926659444736,4231664861184,1057916215296,264479053824,66119763456,16529940864,4132485216,1033121304,258280326,64570082,16142520,4035630,1008906,252228,63058,15764,3940,986,246,60,16,6,1880739938300] 1 [(.D2,22568879259649),(.D0,10783957353548),(.D0,11089432532727),(.D0,449333774466),(.D0,2679690031505),(.D0,7103801340),(.D0,28607774635),(.D0,6540973042),(.D0,14050812184),(.D0,1007275940),(.D0,196019389),(.D0,46799798),(.D0,10770120),(.D0,618520),(.D0,151855),(.D0,3838),(.D0,3414),(.D0,188)],
  .scan 0 50,
  .scan2 5 9 [(46078128488448,4),(6552292492364,4),(10384155055862,4),(331787528321,4),(2660098990480,4),(3838627835,4),(28063579050,4),(6450273777,4),(14035695639,4),(1004756515,4),(195599484,4),(46729813,4),(10758455,4),(616575,4),(151530,4),(3783,4),(3404,4)],
  .scan 5 186,
  .scan 0 10,
  .scan2 3 0 [(186,20),(3404,20),(3783,20),(151530,20),(616575,20),(10758455,20),(46729813,20),(195599484,20),(1004756515,20),(14035695639,20),(6450273777,20),(28063579050,20),(3838627835,20),(2660098990480,20),(331787528321,20),(10384155055862,20),(6552292492364,20)],
  .scan 3 46078128488443,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [89547510173757,12012446494656] 1 [(.D2,46078128488449),(.D0,6552292492365),(.D0,10384155055863),(.D0,331787528322),(.D0,2660098990481),(.D0,3838627836),(.D0,28063579051),(.D0,6450273778),(.D0,14035695640),(.D0,1004756516),(.D0,195599485),(.D0,46729814),(.D0,10758456),(.D0,616576),(.D0,151531),(.D0,3784),(.D0,3405),(.D0,186)],
  .scan 0 50,
  .scan2 5 9 [(50779978334206,4),(20688139321345,4),(2320627631180,4),(9678877578998,4),(214241282177,4),(2640507949456,4),(573454331,4),(27519383466,4),(6359574513,4),(14020579095,4),(1002237091,4),(195179580,4),(46659829,4),(10746791,4),(614631,4),(151206,4),(3729,4),(3395,4)],
  .scan 5 184,
  .scan 0 10,
  .scan2 3 0 [(184,20),(3395,20),(3729,20),(151206,20),(614631,20),(10746791,20),(46659829,20),(195179580,20),(1002237091,20),(14020579095,20),(6359574513,20),(27519383466,20),(573454331,20),(2640507949456,20),(214241282177,20),(9678877578998,20),(2320627631180,20),(20688139321345,20)],
  .scan 3 50779978334201,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [80265256034685,20066313938688] 1 [(.D2,50779978334207),(.D0,20688139321346),(.D0,2320627631181),(.D0,9678877578999),(.D0,214241282178),(.D0,2640507949457),(.D0,573454332),(.D0,27519383467),(.D0,6359574514),(.D0,14020579096),(.D0,1002237092),(.D0,195179581),(.D0,46659830),(.D0,10746792),(.D0,614632),(.D0,151207),(.D0,3730),(.D0,3396)],
  .batch [5016578438016,1254144632832,313536158208,78384039552,19596079872,4898973312,1224720000,306156672,76515840,19222272,4758912,1213056,279936,93312,93312] 50165784986687 [(.D5,25697085840863),(.D5,16507657239121),(.D5,1623880617476),(.D5,9562753076714),(.D5,194887198463),(.D5,2637282268837),(.D3,35840895),(.D1,27429781228),(.D2,6344640807),(.D4,14018090144),(.D0,1001822267),(.D4,195110442),(.D5,46648306),(.D1,10744872),(.D2,614311),(.D3,151153),(.D5,3720),(.D5,3394),(.D0,184)],
  .batch [93312] 53510170674239 [(.D5,24024892997087),(.D5,16228958431825),(.D5,1577430816260),(.D5,9555011443178),(.D5,193596926207),(.D5,2637067223461),(.D1,1)],
  .batch [72074678921278,11648554204610] 53510170720895 [(.D5,24024892973759),(.D5,16228958427937),(.D5,1577430815612),(.D5,9555011443070),(.D5,193596926189),(.D5,2637067223458),(.D5,27423807743),(.D3,6343645227),(.D4,14017924214),(.D4,1001794611),(.D2,195105834),(.D0,46647539),(.D4,10744742),(.D3,614290),(.D5,151149),(.D1,3721),(.D0,3394),(.D1,184)],
  .scan 0 50,
  .scan2 5 9 [(95371787283838,4),(3094084692287,4),(12740490381025,4),(996019474460,4),(9458109552878,4),(177446611157,4),(2634375504286,4),(26975187881,4),(6268875249,4),(14005462551,4),(999717667,4),(194759676,4),(46589845,4),(10735127,4),(612687,4),(150882,4),(3675,4),(3386,4)],
  .scan 5 182,
  .scan 0 10,
  .scan2 3 0 [(182,20),(3386,20),(3675,20),(150882,20),(612687,20),(10735127,20),(46589845,20),(194759676,20),(999717667,20),(14005462551,20),(6268875249,20),(26975187881,20),(2634375504286,20),(177446611157,20),(9458109552878,20),(996019474460,20),(12740490381025,20),(3094084692287,20)],
  .scan 3 95371787283833,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [55693524461193,13923381115296,3480845278824,870211319700,217552829928,54388207476,13597051872,3399262956,849815748,212453928,53113488,13278384,3319596,829884,207468,51876,12960,3240,816,216,48,12,12] 1 [(.D2,95371787283839),(.D0,3094084692288),(.D0,12740490381026),(.D0,996019474461),(.D0,9458109552879),(.D0,177446611158),(.D0,2634375504287),(.D0,26975187882),(.D0,6268875250),(.D0,14005462552),(.D0,999717668),(.D0,194759677),(.D0,46589846),(.D0,10735128),(.D0,612688),(.D0,150883),(.D0,3676),(.D0,3387)],
  .batch [12] 37129016307461 [(.D5,76807279130108),(.D1,1)],
  .batch [89183617899264] 37129016307467 [(.D5,76807279130105),(.D5,12224809598976),(.D5,910072677452),(.D5,9443785086710),(.D5,175059200129),(.D5,2633977602448),(.D1,26908870909),(.D3,6257822421),(.D0,14003620414),(.D0,999410645),(.D4,194708505),(.D3,46581317),(.D3,10733706),(.D5,612450),(.D1,150844),(.D2,3669),(.D4,3385),(.D0,182)],
  .scan 0 50,
  .scan2 5 9 [(81720825257098,4),(54511374655289,4),(8508825519840,4),(290741997596,4),(9340563306734,4),(157855570133,4),(2631110330782,4),(26430992297,4),(6178175985,4),(13990346007,4),(997198243,4),(194339772,4),(46519861,4),(10723463,4),(610743,4),(150558,4),(3621,4),(3377,4)],
  .scan 5 180,
  .scan 0 10,
  .scan2 3 0 [(180,20),(3377,20),(3621,20),(150558,20),(610743,20),(10723463,20),(46519861,20),(194339772,20),(997198243,20),(13990346007,20),(6178175985,20),(26430992297,20),(2631110330782,20),(157855570133,20),(9340563306734,20),(290741997596,20),(8508825519840,20),(54511374655289,20)],
  .scan 3 81720825257093,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [188400814443069,47100203610768,11775050902800,2943762725376,735940681344,183985170336,45996292368,11499073200,2874768192,718692480,179672688,44918064,11229840,2807136,702000,175392,44064,11232,2592,432,432,432] 1 [(.D2,81720825257099),(.D0,54511374655290),(.D0,8508825519841),(.D0,290741997597),(.D0,9340563306735),(.D0,157855570134),(.D0,2631110330783),(.D0,26430992298),(.D0,6178175986),(.D0,13990346008),(.D0,997198244),(.D0,194339773),(.D0,46519862),(.D0,10723464),(.D0,610744),(.D0,150559),(.D0,3622),(.D0,3378),(.D0,180)],
  .batch [56761661328118,2931447686762] 125600542962119 [(.D5,18920553776039),(.D5,44044662741779),(.D5,6764373534255),(.D1,9292106307135),(.D3,149779403534),(.D2,2629764303016),(.D4,26206654336),(.D0,6140786326),(.D4,13984114397),(.D0,996159642),(.D1,194166673),(.D2,46491011),(.D3,10718655),(.D1,609943),(.D0,150425),(.D5,3599),(.D2,3374),(.D2,179)],
  .scan 0 50,
  .scan2 5 9 [(155447097469558,4),(3997276522319,4),(41557449866159,4),(6349838054985,4),(9223017060589,4),(138264529109,4),(2627845157278,4),(25886796713,4),(6087476721,4),(13975229463,4),(994678819,4),(193919868,4),(46449877,4),(10711799,4),(608799,4),(150234,4),(3567,4),(3368,4)],
  .scan 5 178,
  .scan 0 10,
  .scan2 3 0 [(178,20),(3368,20),(3567,20),(150234,20),(608799,20),(10711799,20),(46449877,20),(193919868,20),(994678819,20),(13975229463,20),(6087476721,20),(25886796713,20),(2627845157278,20),(138264529109,20),(9223017060589,20),(6349838054985,20),(41557449866159,20),(3997276522319,20)],
  .scan 3 155447097469553,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [71950977401769,17987744350440,4496936087604,1124234021904,281058505464,70264626372,17566156584,4391539152,1097884800,274471200,68617800,17154444,4288608,1072152,268044,67008,16740,4200,1044,264,60,12] 1 [(.D2,155447097469559),(.D0,3997276522320),(.D0,41557449866160),(.D0,6349838054986),(.D0,9223017060590),(.D0,138264529110),(.D0,2627845157279),(.D0,25886796714),(.D0,6087476722),(.D0,13975229464),(.D0,994678820),(.D0,193919869),(.D0,46449878),(.D0,10711800),(.D0,608800),(.D0,150235),(.D0,3568),(.D0,3369)],
  .batch [85570850579112] 47967318267833 [(.D5,131463438335642),(.D5,40891237112440),(.D1,6238802596033),(.D0,9204511150764),(.D5,135180210805),(.D4,2627331104227),(.D3,25801121205),(.D5,6073197470),(.D2,13972849588),(.D3,994282174),(.D4,193853760),(.D1,46438860),(.D1,10709964),(.D0,608494),(.D0,150184),(.D4,3558),(.D5,3367),(.D0,178)]
]
lemma chunk_14_ok : q6 cmds_14 cfg_14=some cfg_15:= by decide +kernel
def cmds_15 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(90752743557388,4),(110070725690864,4),(37325785004977,4),(5644560578121,4),(9105470814445,4),(118673488085,4),(2624579983774,4),(25342601129,4),(5996777457,4),(13960112919,4),(992159395,4),(193499964,4),(46379893,4),(10700135,4),(606855,4),(149910,4),(3513,4),(3359,4)],
  .scan 5 176,
  .scan 0 10,
  .scan2 3 0 [(176,20),(3359,20),(3513,20),(149910,20),(606855,20),(10700135,20),(46379893,20),(193499964,20),(992159395,20),(13960112919,20),(5996777457,20),(25342601129,20),(2624579983774,20),(118673488085,20),(9105470814445,20),(5644560578121,20),(37325785004977,20),(110070725690864,20)],
  .scan 3 90752743557383,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [272258230672169,68064557668040,17016139417012,4254034854252,1063508713562,265877178390,66469294600,16617323648,4154330914,1038582728,259645680,64911420,16227856,4056966,1014240,253560,63390,15848,3960,990,250,62,16,2,41058127630152] 1 [(.D2,90752743557389),(.D0,110070725690865),(.D0,37325785004978),(.D0,5644560578122),(.D0,9105470814446),(.D0,118673488086),(.D0,2624579983775),(.D0,25342601130),(.D0,5996777458),(.D0,13960112920),(.D0,992159396),(.D0,193499965),(.D0,46379894),(.D0,10700136),(.D0,606856),(.D0,149911),(.D0,3514),(.D0,3360),(.D0,176)],
  .scan 0 50,
  .scan2 5 9 [(202034550929853,4),(84680736523762,4),(33094120143793,4),(4939283101257,4),(8987924568301,4),(99082447061,4),(2621314810270,4),(24798405545,4),(5906078193,4),(13944996375,4),(989639971,4),(193080060,4),(46309909,4),(10688471,4),(604911,4),(149586,4),(3459,4),(3350,4)],
  .scan 5 174,
  .scan 0 10,
  .scan2 3 0 [(174,20),(3350,20),(3459,20),(149586,20),(604911,20),(10688471,20),(46309909,20),(193080060,20),(989639971,20),(13944996375,20),(5906078193,20),(24798405545,20),(2621314810270,20),(99082447061,20),(8987924568301,20),(4939283101257,20),(33094120143793,20),(84680736523762,20)],
  .scan 3 202034550929848,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [606103652789563,3256087220930] 1 [(.D2,202034550929854),(.D0,84680736523763),(.D0,33094120143794),(.D0,4939283101258),(.D0,8987924568302),(.D0,99082447062),(.D0,2621314810271),(.D0,24798405546),(.D0,5906078194),(.D0,13944996376),(.D0,989639972),(.D0,193080061),(.D0,46309910),(.D0,10688472),(.D0,604912),(.D0,149587),(.D0,3460),(.D0,3351),(.D0,174)],
  .scan 0 50,
  .scan2 5 9 [(304679870005246,4),(49694615927230,4),(59290747356658,4),(28862455282609,4),(4234005624393,4),(8870378322157,4),(79491406037,4),(2618049636766,4),(24254209961,4),(5815378929,4),(13929879831,4),(987120547,4),(192660156,4),(46239925,4),(10676807,4),(602967,4),(149262,4),(3405,4),(3341,4)],
  .scan 5 172,
  .scan 0 10,
  .scan2 3 0 [(172,20),(3341,20),(3405,20),(149262,20),(602967,20),(10676807,20),(46239925,20),(192660156,20),(987120547,20),(13929879831,20),(5815378929,20),(24254209961,20),(2618049636766,20),(79491406037,20),(8870378322157,20),(4234005624393,20),(28862455282609,20),(59290747356658,20),(49694615927230,20)],
  .scan 3 304679870005241,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [894503086690161,223625771672532,55906442918136,13976610729528,3494152682388,873538170588,218384542656,54596135664,13649033916,3412258476,853064616,213266160,53316540,13329132,3332280,833076,208260,52080,13008,3264,804,204,48,24,19536523325584,4884130831398,1221032707848,305258176962,76314544242,19078636060,4769659016,1192414752,298103688,74525922,18631482,4657870,1164468,291116,72780,18196,4548,1136,286,72,18,2,2,2] 1 [(.D2,304679870005247),(.D0,49694615927231),(.D0,59290747356659),(.D0,28862455282610),(.D0,4234005624394),(.D0,8870378322158),(.D0,79491406038),(.D0,2618049636767),(.D0,24254209962),(.D0,5815378930),(.D0,13929879832),(.D0,987120548),(.D0,192660157),(.D0,46239926),(.D0,10676808),(.D0,602968),(.D0,149263),(.D0,3406),(.D0,3342),(.D0,172)],
  .batch [64088763089020] 609359740010496 [(.D1,49922948961810),(.D3,27301155550135),(.D4,3973789002314),(.D4,8827008885144),(.D4,72263166535),(.D2,2616844930183),(.D0,24053425531),(.D1,5781914858),(.D1,13924302487),(.D0,986190990),(.D1,192505231),(.D0,46214105),(.D0,10672504),(.D1,602251),(.D4,149142),(.D1,3386),(.D1,3339),(.D2,171)],
  .scan 0 50,
  .scan2 5 9 [(641404121555005,4),(33900758189554,4),(24630790421425,4),(3528728147529,4),(8752832076013,4),(59900365013,4),(2614784463262,4),(23710014377,4),(5724679665,4),(13914763287,4),(984601123,4),(192240252,4),(46169941,4),(10665143,4),(601023,4),(148938,4),(3351,4),(3332,4)],
  .scan 5 170,
  .scan 0 10,
  .scan2 3 0 [(170,20),(3332,20),(3351,20),(148938,20),(601023,20),(10665143,20),(46169941,20),(192240252,20),(984601123,20),(13914763287,20),(5724679665,20),(23710014377,20),(2614784463262,20),(59900365013,20),(8752832076013,20),(3528728147529,20),(24630790421425,20),(33900758189554,20)],
  .scan 3 641404121555000,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [609359740010493] 1 [(.D2,641404121555006),(.D0,33900758189555),(.D0,24630790421426),(.D0,3528728147530),(.D0,8752832076014),(.D0,59900365014),(.D0,2614784463263),(.D0,23710014378),(.D0,5724679666),(.D0,13914763288),(.D0,984601124),(.D0,192240253),(.D0,46169942),(.D0,10665144),(.D0,601024),(.D0,148939),(.D0,3352),(.D0,3333),(.D0,170)],
  .scan 0 50,
  .scan2 5 9 [(304679870005246,4),(489064186552382,4),(8510769022450,4),(20399125560241,4),(2823450670665,4),(8635285829869,4),(40309323989,4),(2611519289758,4),(23165818793,4),(5633980401,4),(13899646743,4),(982081699,4),(191820348,4),(46099957,4),(10653479,4),(599079,4),(148614,4),(3297,4),(3323,4)],
  .scan 5 168,
  .scan 0 10,
  .scan2 3 0 [(168,20),(3323,20),(3297,20),(148614,20),(599079,20),(10653479,20),(46099957,20),(191820348,20),(982081699,20),(13899646743,20),(5633980401,20),(23165818793,20),(2611519289758,20),(40309323989,20),(8635285829869,20),(2823450670665,20),(20399125560241,20),(8510769022450,20),(489064186552382,20)],
  .scan 3 304679870005241,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [914039610015743,228509902503936,57127475625984,14281868906496,3570467226624,892616806656,223154201664,55788550416,13947137604,3486784400,871696098,217924026,54481006,13620252,3405062,851266,212816,53206,13302,3324,830,208,54,12,2,2,2] 1 [(.D2,304679870005247),(.D0,489064186552383),(.D0,8510769022451),(.D0,20399125560242),(.D0,2823450670666),(.D0,8635285829870),(.D0,40309323990),(.D0,2611519289759),(.D0,23165818794),(.D0,5633980402),(.D0,13899646744),(.D0,982081700),(.D0,191820349),(.D0,46099958),(.D0,10653480),(.D0,599080),(.D0,148615),(.D0,3298),(.D0,3324),(.D0,168)],
  .batch [2] 609359740010496 [(.D1,1)],
  .batch [853907401488,213476850372,53369212596,13342303152,3335575788,833893956,208473480,52118364,13029588,3257412,814356,203580,50904,12720,3168,792,204,48,24,67516880578596] 609359740010497 [(.D5,438284208218173),(.D5,47439300082),(.D5,18988570606513),(.D5,2588358178377),(.D5,8596103747821),(.D5,33778976981),(.D5,2610430898590),(.D5,22984420265),(.D5,5603747313),(.D5,13894607895),(.D5,981241891),(.D5,191680380),(.D5,46076629),(.D5,10649591),(.D5,598431),(.D5,148506),(.D5,3279),(.D5,3320),(.D1,168)],
  .scan 0 50,
  .scan2 5 9 [(643687451900790,4),(421120352273026,4),(16167460699058,4),(2118173193801,4),(8517739583725,4),(20718282965,4),(2608254116254,4),(22621623209,4),(5543281137,4),(13884530199,4),(979562275,4),(191400444,4),(46029973,4),(10641815,4),(597135,4),(148290,4),(3243,4),(3314,4)],
  .scan 5 166,
  .scan 0 10,
  .scan2 3 0 [(166,20),(3314,20),(3243,20),(148290,20),(597135,20),(10641815,20),(46029973,20),(191400444,20),(979562275,20),(13884530199,20),(5543281137,20),(22621623209,20),(2608254116254,20),(20718282965,20),(8517739583725,20),(2118173193801,20),(16167460699058,20),(421120352273026,20)],
  .scan 3 643687451900785,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [483316105046397,120829026238272,5214608725824] 1 [(.D2,643687451900791),(.D0,421120352273027),(.D0,16167460699059),(.D0,2118173193802),(.D0,8517739583726),(.D0,20718282966),(.D0,2608254116255),(.D0,22621623210),(.D0,5543281138),(.D0,13884530200),(.D0,979562276),(.D0,191400445),(.D0,46029974),(.D0,10641816),(.D0,597136),(.D0,148291),(.D0,3244),(.D0,3315),(.D0,166)],
  .scan 0 50,
  .scan2 5 9 [(304679870005246,4),(491347516898167,4),(395730363105922,4),(11935795837874,4),(1412895716937,4),(8400193337581,4),(1127241941,4),(2604988942750,4),(22077427625,4),(5452581873,4),(13869413655,4),(977042851,4),(190980540,4),(45959989,4),(10630151,4),(595191,4),(147966,4),(3189,4),(3305,4)],
  .scan 5 164,
  .scan 0 10,
  .scan2 3 0 [(164,20),(3305,20),(3189,20),(147966,20),(595191,20),(10630151,20),(45959989,20),(190980540,20),(977042851,20),(13869413655,20),(5452581873,20),(22077427625,20),(2604988942750,20),(1127241941,20),(8400193337581,20),(1412895716937,20),(11935795837874,20),(395730363105922,20),(491347516898167,20)],
  .scan 3 304679870005241,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [157777800231165,39444449917824,9861112502784,2465278219008,616319508096,154079853696,38519940096,9630078336,2407449600,601862400,150418944,37698048,9331200,2426112,559872,93312,93312,93312] 1 [(.D2,304679870005247),(.D0,491347516898168),(.D0,395730363105923),(.D0,11935795837875),(.D0,1412895716938),(.D0,8400193337582),(.D0,1127241942),(.D0,2604988942751),(.D0,22077427626),(.D0,5452581874),(.D0,13869413656),(.D0,977042852),(.D0,190980541),(.D0,45959990),(.D0,10630152),(.D0,595192),(.D0,147967),(.D0,3190),(.D0,3306)],
  .batch [574298006739840] 105185200138559 [(.D5,252087269935967),(.D5,482582083553287),(.D5,394269457548442),(.D5,11692311578294),(.D5,1372315007007),(.D5,8393429885926),(.D1,2604801069094),(.D4,22046115349),(.D4,5447363160),(.D5,13868543870),(.D4,976897887),(.D0,190956380),(.D3,45955963),(.D2,10629480),(.D3,595080),(.D2,147948),(.D0,3187),(.D2,3305),(.D0,164)],
  .scan 0 50,
  .scan2 5 9 [(392334203508478,4),(108512768251007,4),(458652999939127,4),(390281276946082,4),(11027614811234,4),(1261532212497,4),(8374966086841,4),(2601723769245,4),(21533232041,4),(5361882609,4),(13854297111,4),(974523427,4),(190560636,4),(45890005,4),(10618487,4),(593247,4),(147642,4),(3135,4),(3296,4)],
  .scan 5 162,
  .scan 0 10,
  .scan2 3 0 [(162,20),(3296,20),(3135,20),(147642,20),(593247,20),(10618487,20),(45890005,20),(190560636,20),(974523427,20),(13854297111,20),(5361882609,20),(21533232041,20),(2601723769245,20),(8374966086841,20),(1261532212497,20),(11027614811234,20),(390281276946082,20),(458652999939127,20),(108512768251007,20)],
  .scan 3 392334203508473,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1177002610525439,294250652631360,73562663157840,18390665789460,4597666447364,1149416611840,287354152962,71838538238,17959634560,4489908642,1122477158,280619290,70154822,17538706,4384676,1096170,274042,68510,17128,4284,1070,268,66,18,2,2,2] 1 [(.D2,392334203508479),(.D0,108512768251008),(.D0,458652999939128),(.D0,390281276946083),(.D0,11027614811235),(.D0,1261532212498),(.D0,8374966086842),(.D0,2601723769246),(.D0,21533232042),(.D0,5361882610),(.D0,13854297112),(.D0,974523428),(.D0,190560637),(.D0,45890006),(.D0,10618488),(.D0,593248),(.D0,147643),(.D0,3136),(.D0,3297),(.D0,162)],
  .batch [2] 784668407016960 [(.D1,1)],
  .batch [129371202998780,32342800749696,8085700187424,2021425046856,505356261714,126339065430,31584766356,7896191588,1974047898,493511974,123377994,30844500,7711124,1927780,481946,120486,30120,7530,1884,472,116,30,6,4,2,2] 784668407016961 [(.D5,43123734332926),(.D5,447754827619447),(.D5,388464914892802),(.D5,10724887802354),(.D5,1211077711017),(.D5,8366557003261),(.D5,2600322255315),(.D5,21299646386),(.D3,5322951667),(.D1,13847808622),(.D2,973442012),(.D1,190380401),(.D1,45859967),(.D4,10613480),(.D1,592414),(.D4,147503),(.D2,3112),(.D3,3293),(.D2,161)],
  .batch [29218111167748] 870915875682817 [(.D1,440567538563959),(.D5,387267033383554),(.D5,10525240884146),(.D5,1177803224649),(.D5,8361011255533),(.D5,2599397964027),(.D5,21145597838),(.D5,5297276909),(.D0,13843529495),(.D5,972728824),(.D1,190261537),(.D2,45840155),(.D5,10610179),(.D0,591863),(.D5,147411),(.D3,3097),(.D1,3291),(.D4,160)],
  .scan 0 50,
  .scan2 5 9 [(885524931266690,4),(433263010772021,4),(386049612084898,4),(10322337334370,4),(1143985966353,4),(8355375045817,4),(2598458595741,4),(20989036457,4),(5271183345,4),(13839180567,4),(972004003,4),(190140732,4),(45820021,4),(10606823,4),(591303,4),(147318,4),(3081,4),(3287,4)],
  .scan 5 160,
  .scan 0 10,
  .scan2 3 0 [(160,20),(3287,20),(3081,20),(147318,20),(591303,20),(10606823,20),(45820021,20),(190140732,20),(972004003,20),(13839180567,20),(5271183345,20),(20989036457,20),(2598458595741,20),(8355375045817,20),(1143985966353,20),(10322337334370,20),(386049612084898,20),(433263010772021,20)],
  .scan 3 885524931266685,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [609359740010493] 1 [(.D2,885524931266691),(.D0,433263010772022),(.D0,386049612084899),(.D0,10322337334371),(.D0,1143985966354),(.D0,8355375045818),(.D0,2598458595742),(.D0,20989036458),(.D0,5271183346),(.D0,13839180568),(.D0,972004004),(.D0,190140733),(.D0,45820022),(.D0,10606824),(.D0,591304),(.D0,147319),(.D0,3082),(.D0,3288),(.D0,160)],
  .scan 0 50,
  .scan2 5 9 [(304679870005246,4),(733184996264067,4),(407873021604917,4),(381817947223714,4),(9617059857506,4),(1026439720209,4),(8335784004793,4),(2595193422237,4),(20444840873,4),(5180484081,4),(13824064023,4),(969484579,4),(189720828,4),(45750037,4),(10595159,4),(589359,4),(146994,4),(3027,4),(3278,4)],
  .scan 5 158,
  .scan 0 10,
  .scan2 3 0 [(158,20),(3278,20),(3027,20),(146994,20),(589359,20),(10595159,20),(45750037,20),(189720828,20),(969484579,20),(13824064023,20),(5180484081,20),(20444840873,20),(2595193422237,20),(8335784004793,20),(1026439720209,20),(9617059857506,20),(381817947223714,20),(407873021604917,20),(733184996264067,20)],
  .scan 3 304679870005241,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [914039610015743,228509902503936,57127475625984,14281868906496,3570467226624,892616806656,223154201664,55788550416,13947137604,3486784400,871696098,217924026,54481006,13620252,3405062,851266,212816,53206,13302,3324,830,208,54,12,2,2,2] 1 [(.D2,304679870005247),(.D0,733184996264068),(.D0,407873021604918),(.D0,381817947223715),(.D0,9617059857507),(.D0,1026439720210),(.D0,8335784004794),(.D0,2595193422238),(.D0,20444840874),(.D0,5180484082),(.D0,13824064024),(.D0,969484580),(.D0,189720829),(.D0,45750038),(.D0,10595160),(.D0,589360),(.D0,146995),(.D0,3028),(.D0,3279),(.D0,158)],
  .batch [2] 609359740010496 [(.D1,1)],
  .batch [406239826673664] 609359740010497 [(.D5,682405017929858),(.D5,399409691882549),(.D5,380407392269986),(.D5,9381967365218),(.D5,987257638161),(.D5,8329253657785),(.D5,2594105031069),(.D5,20263442345),(.D5,5150250993),(.D5,13819025175),(.D5,968644771),(.D5,189580860),(.D5,45726709),(.D5,10591271),(.D5,588711),(.D5,146886),(.D5,3009),(.D5,3275),(.D1,158)],
  .scan 0 50,
  .scan2 5 9 [(812479653347328,4),(580845061261442,4),(382483032437813,4),(377586282362530,4),(8911782380642,4),(908893474065,4),(8316192963769,4),(2591928248733,4),(19900645289,4),(5089784817,4),(13808947479,4),(966965155,4),(189300924,4),(45680053,4),(10583495,4),(587415,4),(146670,4),(2973,4),(3269,4)],
  .scan 5 156,
  .scan 0 10,
  .scan2 3 0 [(156,20),(3269,20),(2973,20),(146670,20),(587415,20),(10583495,20),(45680053,20),(189300924,20),(966965155,20),(13808947479,20),(5089784817,20),(19900645289,20),(2591928248733,20),(8316192963769,20),(908893474065,20),(8911782380642,20),(377586282362530,20),(382483032437813,20),(580845061261442,20)],
  .scan 3 812479653347323,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2437438960041989,609359740010496,152339935002624,38084983750656,9521245937664,2380311484416,595077871104,148769467776,37192366944,9298091736,2324522934,581130734,145282684,36320670,9080168,2270040,567510,141880,35468,8868,2218,554,138,34,8,4,67706637778940] 1 [(.D2,812479653347329),(.D0,580845061261443),(.D0,382483032437814),(.D0,377586282362531),(.D0,8911782380643),(.D0,908893474066),(.D0,8316192963770),(.D0,2591928248734),(.D0,19900645290),(.D0,5089784818),(.D0,13808947480),(.D0,966965156),(.D0,189300925),(.D0,45680054),(.D0,10583496),(.D0,587416),(.D0,146671),(.D0,2974),(.D0,3270),(.D0,156)],
  .scan 0 50,
  .scan2 5 9 [(1658812625584128,4),(428505126258819,4),(357093043270709,4),(373354617501346,4),(8206504903778,4),(791347227921,4),(8296601922745,4),(2588663075229,4),(19356449705,4),(4999085553,4),(13793830935,4),(964445731,4),(188881020,4),(45610069,4),(10571831,4),(585471,4),(146346,4),(2919,4),(3260,4)],
  .scan 5 154,
  .scan 0 10,
  .scan2 3 0 [(154,20),(3260,20),(2919,20),(146346,20),(585471,20),(10571831,20),(45610069,20),(188881020,20),(964445731,20),(13793830935,20),(4999085553,20),(19356449705,20),(2588663075229,20),(8296601922745,20),(791347227921,20),(8206504903778,20),(373354617501346,20),(357093043270709,20),(428505126258819,20)],
  .scan 3 1658812625584123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3656158440062973] 1 [(.D2,1658812625584129),(.D0,428505126258820),(.D0,357093043270710),(.D0,373354617501347),(.D0,8206504903779),(.D0,791347227922),(.D0,8296601922746),(.D0,2588663075230),(.D0,19356449706),(.D0,4999085554),(.D0,13793830936),(.D0,964445732),(.D0,188881021),(.D0,45610070),(.D0,10571832),(.D0,585472),(.D0,146347),(.D0,2920),(.D0,3261),(.D0,154)],
  .scan 0 50,
  .scan2 5 9 [(1828079220031486,4),(744773015568385,4),(276165191256195,4),(331703054103605,4),(369122952640162,4),(7501227426914,4),(673800981777,4),(8277010881721,4),(2585397901725,4),(18812254121,4),(4908386289,4),(13778714391,4),(961926307,4),(188461116,4),(45540085,4),(10560167,4),(583527,4),(146022,4),(2865,4),(3251,4)],
  .scan 5 152,
  .scan 0 10,
  .scan2 3 0 [(152,20),(3251,20),(2865,20),(146022,20),(583527,20),(10560167,20),(45540085,20),(188461116,20),(961926307,20),(13778714391,20),(4908386289,20),(18812254121,20),(2585397901725,20),(8277010881721,20),(673800981777,20),(7501227426914,20),(369122952640162,20),(331703054103605,20),(276165191256195,20),(744773015568385,20)],
  .scan 3 1828079220031481,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5484237660094463,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176600,1307544150,326886038,81721510,20430378,5107592,1276900,319224,79806,19952,4986,1248,312,78,18,6,2,2] 1 [(.D2,1828079220031487),(.D0,744773015568386),(.D0,276165191256196),(.D0,331703054103606),(.D0,369122952640163),(.D0,7501227426915),(.D0,673800981778),(.D0,8277010881722),(.D0,2585397901726),(.D0,18812254122),(.D0,4908386290),(.D0,13778714392),(.D0,961926308),(.D0,188461117),(.D0,45540086),(.D0,10560168),(.D0,583528),(.D0,146023),(.D0,2866),(.D0,3252),(.D0,152)],
  .batch [2] 3656158440062976 [(.D1,1)],
  .batch [1320279436689410,330069859172354,82517464793088,20629366198272,5157341549568,1289335387392,322333846848,80583461712,20145865428,5036466358,1259116590,314779146,78694788,19673696,4918422,1229608,307400,76852,19212,4802,1200,300,76,20,4,2] 3656158440062977 [(.D5,440093145563136),(.D5,225385212921987),(.D5,323239724381237),(.D5,367712397686434),(.D5,7266134934626),(.D5,634618899729),(.D5,8270480534713),(.D5,2584309510557),(.D5,18630855593),(.D5,4878153201),(.D5,13773675543),(.D5,961086499),(.D5,188321148),(.D5,45516757),(.D5,10556279),(.D5,582879),(.D5,145914),(.D5,2847),(.D5,3248),(.D1,152)],
  .batch [2] 4536344731189251 [(.D1,1)],
  .batch [112844396298238] 4536344731189252 [(.D1,152036355328132),(.D0,311014914782262),(.D0,365674929419939),(.D0,6926556890211),(.D0,578022558994),(.D0,8261047811258),(.D0,2582737389982),(.D0,18368835498),(.D0,4834483186),(.D0,13766397208),(.D0,959873444),(.D0,188118973),(.D0,45483062),(.D0,10550664),(.D0,581944),(.D0,145759),(.D2,2821),(.D5,3244),(.D4,150)]
]
lemma chunk_15_ok : q6 cmds_15 cfg_15=some cfg_16:= by decide +kernel
def cmds_16 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(4592766929338370,4),(123825256253571,4),(306313064936501,4),(364891287778978,4),(6795949950050,4),(556254735633,4),(8257419840697,4),(2582132728221,4),(18268058537,4),(4817687025,4),(13763597847,4),(959406883,4),(188041212,4),(45470101,4),(10548503,4),(581583,4),(145698,4),(2811,4),(3242,4)],
  .scan 5 150,
  .scan 0 10,
  .scan2 3 0 [(150,20),(3242,20),(2811,20),(145698,20),(581583,20),(10548503,20),(45470101,20),(188041212,20),(959406883,20),(13763597847,20),(4817687025,20),(18268058537,20),(2582132728221,20),(8257419840697,20),(556254735633,20),(6795949950050,20),(364891287778978,20),(306313064936501,20),(123825256253571,20)],
  .scan 3 4592766929338365,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2228854612564305,557213653141068,139303413285264,34825853321316,8706463330320,2176615832580,544153958160,136038489528,34009622388,8502405588,2125601412,531400356,132850080,33212520,8303124,2075784,518952,129732,32436,8112,2016,504,132,36,12] 1 [(.D2,4592766929338371),(.D0,123825256253572),(.D0,306313064936502),(.D0,364891287778979),(.D0,6795949950051),(.D0,556254735634),(.D0,8257419840698),(.D0,2582132728222),(.D0,18268058538),(.D0,4817687026),(.D0,13763597848),(.D0,959406884),(.D0,188041213),(.D0,45470102),(.D0,10548504),(.D0,581584),(.D0,145699),(.D0,2812),(.D0,3243),(.D0,150)],
  .batch [114058714996212] 1485903075042863 [(.D5,3849815391816939),(.D1,285675522227574),(.D0,361451697327491),(.D0,6222684874803),(.D0,460710556426),(.D0,8241495810830),(.D0,2579478723244),(.D0,17825724375),(.D2,4743964665),(.D2,13751310787),(.D5,957359040),(.D0,187699906),(.D0,45413217),(.D3,10539023),(.D2,580003),(.D3,145435),(.D1,2768),(.D5,3235),(.D4,148)],
  .scan 0 50,
  .scan2 5 9 [(1542932432540968,4),(3821300713067886,4),(280923075769397,4),(360659622917794,4),(6090672473186,4),(438708489489,4),(8237828799673,4),(2578867554717,4),(17723862953,4),(4726987761,4),(13748481303,4),(956887459,4),(187621308,4),(45400117,4),(10536839,4),(579639,4),(145374,4),(2757,4),(3233,4)],
  .scan 5 148,
  .scan 0 10,
  .scan2 3 0 [(148,20),(3233,20),(2757,20),(145374,20),(579639,20),(10536839,20),(45400117,20),(187621308,20),(956887459,20),(13748481303,20),(4726987761,20),(17723862953,20),(2578867554717,20),(8237828799673,20),(438708489489,20),(6090672473186,20),(360659622917794,20),(280923075769397,20),(3821300713067886,20)],
  .scan 3 1542932432540963,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3656158440062973] 1 [(.D2,1542932432540969),(.D0,3821300713067887),(.D0,280923075769398),(.D0,360659622917795),(.D0,6090672473187),(.D0,438708489490),(.D0,8237828799674),(.D0,2578867554718),(.D0,17723862954),(.D0,4726987762),(.D0,13748481304),(.D0,956887460),(.D0,187621309),(.D0,45400118),(.D0,10536840),(.D0,579640),(.D0,145375),(.D0,2758),(.D0,3234),(.D0,148)],
  .scan 0 50,
  .scan2 5 9 [(1828079220031486,4),(628892822525225,4),(3668960778065262,4),(255533086602293,4),(356427958056610,4),(5385394996322,4),(321162243345,4),(8218237758649,4),(2575602381213,4),(17179667369,4),(4636288497,4),(13733364759,4),(954368035,4),(187201404,4),(45330133,4),(10525175,4),(577695,4),(145050,4),(2703,4),(3224,4)],
  .scan 5 146,
  .scan 0 10,
  .scan2 3 0 [(146,20),(3224,20),(2703,20),(145050,20),(577695,20),(10525175,20),(45330133,20),(187201404,20),(954368035,20),(13733364759,20),(4636288497,20),(17179667369,20),(2575602381213,20),(8218237758649,20),(321162243345,20),(5385394996322,20),(356427958056610,20),(255533086602293,20),(3668960778065262,20),(628892822525225,20)],
  .scan 3 1828079220031481,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5484237660094463,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176600,1307544150,326886038,81721510,20430378,5107592,1276900,319224,79806,19952,4986,1248,312,78,18,6,2,2] 1 [(.D2,1828079220031487),(.D0,628892822525226),(.D0,3668960778065263),(.D0,255533086602294),(.D0,356427958056611),(.D0,5385394996323),(.D0,321162243346),(.D0,8218237758650),(.D0,2575602381214),(.D0,17179667370),(.D0,4636288498),(.D0,13733364760),(.D0,954368036),(.D0,187201405),(.D0,45330134),(.D0,10525176),(.D0,577696),(.D0,145051),(.D0,2704),(.D0,3225),(.D0,146)],
  .batch [2] 3656158440062976 [(.D1,1)],
  .batch [972638857559930,243159714389984,60789928597494,15197482149376,3799370537342,949842634336,237460658586,59365164644,14841291162,3710322790,927580698,231895176,57973794,14493446,3623362,905840,226462,56616,14154,3536,886,222,54,14,4,190097858327010] 3656158440062977 [(.D5,324212952519976),(.D5,3618180799731054),(.D5,247069756879925),(.D5,355017403102882),(.D5,5150302504034),(.D5,281980161297),(.D5,8211707411641),(.D5,2574513990045),(.D5,16998268841),(.D5,4606055409),(.D5,13728325911),(.D5,953528227),(.D5,187061436),(.D5,45306805),(.D5,10521287),(.D5,577047),(.D5,144942),(.D5,2685),(.D5,3221),(.D1,146)],
  .scan 0 50,
  .scan2 5 9 [(4399633274266435,4),(3516620843062639,4),(230143097435189,4),(352196293195426,4),(4680117519458,4),(203615997201,4),(8198646717625,4),(2572337207709,4),(16635471785,4),(4545589233,4),(13718248215,4),(951848611,4),(186781500,4),(45260149,4),(10513511,4),(575751,4),(144726,4),(2649,4),(3215,4)],
  .scan 5 144,
  .scan 0 10,
  .scan2 3 0 [(144,20),(3215,20),(2649,20),(144726,20),(575751,20),(10513511,20),(45260149,20),(186781500,20),(951848611,20),(13718248215,20),(4545589233,20),(16635471785,20),(2572337207709,20),(8198646717625,20),(203615997201,20),(4680117519458,20),(352196293195426,20),(230143097435189,20),(3516620843062639,20)],
  .scan 3 4399633274266430,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3656158440062973] 1 [(.D2,4399633274266436),(.D0,3516620843062640),(.D0,230143097435190),(.D0,352196293195427),(.D0,4680117519459),(.D0,203615997202),(.D0,8198646717626),(.D0,2572337207710),(.D0,16635471786),(.D0,4545589234),(.D0,13718248216),(.D0,951848612),(.D0,186781501),(.D0,45260150),(.D0,10513512),(.D0,575752),(.D0,144727),(.D0,2650),(.D0,3216),(.D0,144)],
  .scan 0 50,
  .scan2 5 9 [(1828079220031486,4),(3485593664250692,4),(3364280908060015,4),(204753108268085,4),(347964628334242,4),(3974840042594,4),(86069751057,4),(8179055676601,4),(2569072034205,4),(16091276201,4),(4454889969,4),(13703131671,4),(949329187,4),(186361596,4),(45190165,4),(10501847,4),(573807,4),(144402,4),(2595,4),(3206,4)],
  .scan 5 142,
  .scan 0 10,
  .scan2 3 0 [(142,20),(3206,20),(2595,20),(144402,20),(573807,20),(10501847,20),(45190165,20),(186361596,20),(949329187,20),(13703131671,20),(4454889969,20),(16091276201,20),(2569072034205,20),(8179055676601,20),(86069751057,20),(3974840042594,20),(347964628334242,20),(204753108268085,20),(3364280908060015,20),(3485593664250692,20)],
  .scan 3 1828079220031481,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5484237660094463,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176600,1307544150,326886038,81721510,20430378,5107592,1276900,319224,79806,19952,4986,1248,312,78,18,6,2,2] 1 [(.D2,1828079220031487),(.D0,3485593664250693),(.D0,3364280908060016),(.D0,204753108268086),(.D0,347964628334243),(.D0,3974840042595),(.D0,86069751058),(.D0,8179055676602),(.D0,2569072034206),(.D0,16091276202),(.D0,4454889970),(.D0,13703131672),(.D0,949329188),(.D0,186361597),(.D0,45190166),(.D0,10501848),(.D0,573808),(.D0,144403),(.D0,2596),(.D0,3207),(.D0,142)],
  .batch [2] 3656158440062976 [(.D1,1)],
  .batch [1093795542649728,273448885685760,68362221405888,17090555347584,4272638844672,1068159726720,267039923904,66759977088,16690002048,4172492736,1043134848,260775936,65178432,16314048,4074624,1010880,248832,77760,15552] 3656158440062977 [(.D5,3180913794245443),(.D5,3313500929725807),(.D5,196289778545717),(.D5,346554073380514),(.D5,3739747550306),(.D5,46887669009),(.D5,8172525329593),(.D5,2567983643037),(.D5,15909877673),(.D5,4424656881),(.D5,13698092823),(.D5,948489379),(.D5,186221628),(.D5,45166837),(.D5,10497959),(.D5,573159),(.D5,144294),(.D5,2577),(.D5,3203),(.D1,142)],
  .batch [15552] 4385355468506497 [(.D5,2816315280023683),(.D5,3252734510688847),(.D5,186162042039557),(.D5,344866117296154),(.D5,3458421536246),(.D1,1)],
  .batch [163174150515456] 4385355468514273 [(.D5,2816315280019795),(.D5,3252734510688199),(.D5,186162042039449),(.D5,344866117296136),(.D5,3458421536243),(.D1,8164710718092),(.D5,2566681207787),(.D4,15692805131),(.D1,4388478125),(.D5,13692063030),(.D5,947484414),(.D4,186054134),(.D2,45138922),(.D4,10493306),(.D5,572384),(.D0,144166),(.D2,2556),(.D2,3200),(.D4,140)],
  .scan 0 50,
  .scan2 5 9 [(4466942543772000,4),(2775521742390931,4),(3245935587750055,4),(185028888216425,4),(344677258325632,4),(3426945041159,4),(8159464635577,4),(2565806860701,4),(15547080617,4),(4364190705,4),(13688015127,4),(946809763,4),(185941692,4),(45120181,4),(10490183,4),(571863,4),(144078,4),(2541,4),(3197,4)],
  .scan 5 140,
  .scan 0 10,
  .scan2 3 0 [(140,20),(3197,20),(2541,20),(144078,20),(571863,20),(10490183,20),(45120181,20),(185941692,20),(946809763,20),(13688015127,20),(4364190705,20),(15547080617,20),(2565806860701,20),(8159464635577,20),(3426945041159,20),(344677258325632,20),(185028888216425,20),(3245935587750055,20),(2775521742390931,20)],
  .scan 3 4466942543771995,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3656158440062973] 1 [(.D2,4466942543772001),(.D0,2775521742390932),(.D0,3245935587750056),(.D0,185028888216426),(.D0,344677258325633),(.D0,3426945041160),(.D0,8159464635578),(.D0,2565806860702),(.D0,15547080618),(.D0,4364190706),(.D0,13688015128),(.D0,946809764),(.D0,185941693),(.D0,45120182),(.D0,10490184),(.D0,571864),(.D0,144079),(.D0,2542),(.D0,3198),(.D0,140)],
  .scan 0 50,
  .scan2 5 9 [(1828079220031486,4),(3552902933756257,4),(2623181807388307,4),(3220545598582951,4),(180797223355241,4),(343971980848768,4),(3309398795015,4),(8139873594553,4),(2562541687197,4),(15002885033,4),(4273491441,4),(13672898583,4),(944290339,4),(185521788,4),(45050197,4),(10478519,4),(569919,4),(143754,4),(2487,4),(3188,4)],
  .scan 5 138,
  .scan 0 10,
  .scan2 3 0 [(138,20),(3188,20),(2487,20),(143754,20),(569919,20),(10478519,20),(45050197,20),(185521788,20),(944290339,20),(13672898583,20),(4273491441,20),(15002885033,20),(2562541687197,20),(8139873594553,20),(3309398795015,20),(343971980848768,20),(180797223355241,20),(3220545598582951,20),(2623181807388307,20),(3552902933756257,20)],
  .scan 3 1828079220031481,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5484237660094463,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176600,1307544150,326886038,81721510,20430378,5107592,1276900,319224,79806,19952,4986,1248,312,78,18,6,2,2] 1 [(.D2,1828079220031487),(.D0,3552902933756258),(.D0,2623181807388308),(.D0,3220545598582952),(.D0,180797223355242),(.D0,343971980848769),(.D0,3309398795016),(.D0,8139873594554),(.D0,2562541687198),(.D0,15002885034),(.D0,4273491442),(.D0,13672898584),(.D0,944290340),(.D0,185521789),(.D0,45050198),(.D0,10478520),(.D0,569920),(.D0,143755),(.D0,2488),(.D0,3189),(.D0,138)],
  .batch [2] 3656158440062976 [(.D1,1)],
  .batch [2437438960041984] 3656158440062977 [(.D5,3248223063751008),(.D5,2572401829054099),(.D5,3212082268860583),(.D5,179386668401513),(.D5,343736888356480),(.D5,3270216712967),(.D5,8133343247545),(.D5,2561453296029),(.D5,14821486505),(.D5,4243258353),(.D5,13667859735),(.D5,943450531),(.D5,185381820),(.D5,45026869),(.D5,10474631),(.D5,569271),(.D5,143646),(.D5,2469),(.D5,3185),(.D1,138)],
  .scan 0 50,
  .scan2 5 9 [(4874877920083968,4),(2638863323740512,4),(2470841872385683,4),(3195155609415847,4),(176565558494057,4),(343266703371904,4),(3191852548871,4),(8120282553529,4),(2559276513693,4),(14458689449,4),(4182792177,4),(13657782039,4),(941770915,4),(185101884,4),(44980213,4),(10466855,4),(567975,4),(143430,4),(2433,4),(3179,4)],
  .scan 5 136,
  .scan 0 10,
  .scan2 3 0 [(136,20),(3179,20),(2433,20),(143430,20),(567975,20),(10466855,20),(44980213,20),(185101884,20),(941770915,20),(13657782039,20),(4182792177,20),(14458689449,20),(2559276513693,20),(8120282553529,20),(3191852548871,20),(343266703371904,20),(176565558494057,20),(3195155609415847,20),(2470841872385683,20),(2638863323740512,20)],
  .scan 3 4874877920083963,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [14624633760251909,3656158440062976,914039610015744,228509902503936,57127475625984,14281868906496,3570467226624,892616806656,223154201664,55788550416,13947137604,3486784400,871696102,217924026,54481004,13620252,3405064,851264,212818,53204,13300,3326,832,206,52,14,4,406239826673660] 1 [(.D2,4874877920083969),(.D0,2638863323740513),(.D0,2470841872385684),(.D0,3195155609415848),(.D0,176565558494058),(.D0,343266703371905),(.D0,3191852548872),(.D0,8120282553530),(.D0,2559276513694),(.D0,14458689450),(.D0,4182792178),(.D0,13657782040),(.D0,941770916),(.D0,185101885),(.D0,44980214),(.D0,10466856),(.D0,567976),(.D0,143431),(.D0,2434),(.D0,3180),(.D0,136)],
  .scan 0 50,
  .scan2 5 9 [(9952875753504768,4),(1724823713724769,4),(2318501937383059,4),(3169765620248743,4),(172333893632873,4),(342561425895040,4),(3074306302727,4),(8100691512505,4),(2556011340189,4),(13914493865,4),(4092092913,4),(13642665495,4),(939251491,4),(184681980,4),(44910229,4),(10455191,4),(566031,4),(143106,4),(2379,4),(3170,4)],
  .scan 5 134,
  .scan 0 10,
  .scan2 3 0 [(134,20),(3170,20),(2379,20),(143106,20),(566031,20),(10455191,20),(44910229,20),(184681980,20),(939251491,20),(13642665495,20),(4092092913,20),(13914493865,20),(2556011340189,20),(8100691512505,20),(3074306302727,20),(342561425895040,20),(172333893632873,20),(3169765620248743,20),(2318501937383059,20),(1724823713724769,20)],
  .scan 3 9952875753504763,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21936950640377853] 1 [(.D2,9952875753504769),(.D0,1724823713724770),(.D0,2318501937383060),(.D0,3169765620248744),(.D0,172333893632874),(.D0,342561425895041),(.D0,3074306302728),(.D0,8100691512506),(.D0,2556011340190),(.D0,13914493866),(.D0,4092092914),(.D0,13642665496),(.D0,939251492),(.D0,184681981),(.D0,44910230),(.D0,10455192),(.D0,566032),(.D0,143107),(.D0,2380),(.D0,3171),(.D0,134)],
  .scan 0 50,
  .scan2 5 9 [(10968475320188926,4),(4468638093410305,4),(810784103709025,4),(2166162002380435,4),(3144375631081639,4),(168102228771689,4),(341856148418176,4),(2956760056583,4),(8081100471481,4),(2552746166685,4),(13370298281,4),(4001393649,4),(13627548951,4),(936732067,4),(184262076,4),(44840245,4),(10443527,4),(564087,4),(142782,4),(2325,4),(3161,4)],
  .scan 5 132,
  .scan 0 10,
  .scan2 3 0 [(132,20),(3161,20),(2325,20),(142782,20),(564087,20),(10443527,20),(44840245,20),(184262076,20),(936732067,20),(13627548951,20),(4001393649,20),(13370298281,20),(2552746166685,20),(8081100471481,20),(2956760056583,20),(341856148418176,20),(168102228771689,20),(3144375631081639,20),(2166162002380435,20),(810784103709025,20),(4468638093410305,20)],
  .scan 3 10968475320188921,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [32905425960566783,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264900,1961316226,490329056,122582266,30645566,7661392,1915346,478836,119710,29928,7482,1872,468,116,28,8,2,2] 1 [(.D2,10968475320188927),(.D0,4468638093410306),(.D0,810784103709026),(.D0,2166162002380436),(.D0,3144375631081640),(.D0,168102228771690),(.D0,341856148418177),(.D0,2956760056584),(.D0,8081100471482),(.D0,2552746166686),(.D0,13370298282),(.D0,4001393650),(.D0,13627548952),(.D0,936732068),(.D0,184262077),(.D0,44840246),(.D0,10443528),(.D0,564088),(.D0,142783),(.D0,2326),(.D0,3162),(.D0,132)],
  .batch [2] 21936950640377856 [(.D1,1)],
  .batch [7921676620136450,1980419155034114,495104788758528,123776197189632,30944049297408,7736012324352,1934003081088,483500770272,120875192568,30218798142,7554699534,1888674886,472168722,118042178,29510544,7377636,1844410,461102,115276,28820,7204,1802,450,112,30,6,2] 21936950640377857 [(.D5,2640558873378816),(.D5,506104233703777),(.D5,2115382024046227),(.D5,3135912301359271),(.D5,166691673817961),(.D5,341621055925888),(.D5,2917577974535),(.D5,8074570124473),(.D5,2551657775517),(.D5,13188899753),(.D5,3971160561),(.D5,13622510103),(.D5,935892259),(.D5,184122108),(.D5,44816917),(.D5,10439639),(.D5,563439),(.D5,142674),(.D5,2307),(.D5,3158),(.D1,132)],
  .batch [2] 27218068387135491 [(.D1,1)],
  .batch [198033264421926,49508316105480,12377079026370,3094269756594,773567439146,193391859786,48347964948,12086991238,3021747810,755436950,188859238,47214810,11803704,2950926,737730,184434,46106,11526,2884,720,180,44,12,4,68837004204476] 27218068387135492 [(.D1,66011088140642),(.D0,2042033166452372),(.D0,3123687491760296),(.D0,164654205551466),(.D0,341281477881473),(.D0,2860981633800),(.D0,8065137401018),(.D0,2550085654942),(.D0,12926879658),(.D0,3927490546),(.D0,13615231768),(.D0,934679204),(.D0,183919933),(.D0,44783222),(.D0,10434024),(.D0,562504),(.D0,142519),(.D2,2281),(.D5,3154),(.D4,130)],
  .scan 0 50,
  .scan2 5 9 [(27384509065519012,4),(2013822067377812,4),(3118985641914535,4),(163870563910505,4),(341150870941312,4),(2839213810439,4),(8061509430457,4),(2549480993181,4),(12826102697,4),(3910694385,4),(13612432407,4),(934212643,4),(183842172,4),(44770261,4),(10431863,4),(562143,4),(142458,4),(2271,4),(3152,4)],
  .scan 5 130,
  .scan 0 10,
  .scan2 3 0 [(130,20),(3152,20),(2271,20),(142458,20),(562143,20),(10431863,20),(44770261,20),(183842172,20),(934212643,20),(13612432407,20),(3910694385,20),(12826102697,20),(2549480993181,20),(8061509430457,20),(2839213810439,20),(341150870941312,20),(163870563910505,20),(3118985641914535,20),(2013822067377812,20)],
  .scan 3 27384509065519007,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3656158440062973] 1 [(.D2,27384509065519013),(.D0,2013822067377813),(.D0,3118985641914536),(.D0,163870563910506),(.D0,341150870941313),(.D0,2839213810440),(.D0,8061509430458),(.D0,2549480993182),(.D0,12826102698),(.D0,3910694386),(.D0,13612432408),(.D0,934212644),(.D0,183842173),(.D0,44770262),(.D0,10431864),(.D0,562144),(.D0,142459),(.D0,2272),(.D0,3153),(.D0,130)],
  .scan 0 50,
  .scan2 5 9 [(1828079220031486,4),(26470469455503269,4),(1861482132375188,4),(3093595652747431,4),(159638899049321,4),(340445593464448,4),(2721667564295,4),(8041918389433,4),(2546215819677,4),(12281907113,4),(3819995121,4),(13597315863,4),(931693219,4),(183422268,4),(44700277,4),(10420199,4),(560199,4),(142134,4),(2217,4),(3143,4)],
  .scan 5 128,
  .scan 0 10,
  .scan2 3 0 [(128,20),(3143,20),(2217,20),(142134,20),(560199,20),(10420199,20),(44700277,20),(183422268,20),(931693219,20),(13597315863,20),(3819995121,20),(12281907113,20),(2546215819677,20),(8041918389433,20),(2721667564295,20),(340445593464448,20),(159638899049321,20),(3093595652747431,20),(1861482132375188,20),(26470469455503269,20)],
  .scan 3 1828079220031481,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [5484237660094463,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176600,1307544150,326886038,81721510,20430378,5107592,1276900,319224,79806,19952,4986,1248,312,78,18,6,2,2] 1 [(.D2,1828079220031487),(.D0,26470469455503270),(.D0,1861482132375189),(.D0,3093595652747432),(.D0,159638899049322),(.D0,340445593464449),(.D0,2721667564296),(.D0,8041918389434),(.D0,2546215819678),(.D0,12281907114),(.D0,3819995122),(.D0,13597315864),(.D0,931693220),(.D0,183422269),(.D0,44700278),(.D0,10420200),(.D0,560200),(.D0,142135),(.D0,2218),(.D0,3144),(.D0,128)],
  .batch [2] 3656158440062976 [(.D1,1)],
  .batch [2437438960041984] 3656158440062977 [(.D5,26165789585498020),(.D5,1810702154040980),(.D5,3085132323025063),(.D5,158228344095593),(.D5,340210500972160),(.D5,2682485482247),(.D5,8035388042425),(.D5,2545127428509),(.D5,12100508585),(.D5,3789762033),(.D5,13592277015),(.D5,930853411),(.D5,183282300),(.D5,44676949),(.D5,10416311),(.D5,559551),(.D5,142026),(.D5,2199),(.D5,3140),(.D1,128)]
]
lemma chunk_16_ok : q6 cmds_16 cfg_16=some cfg_17:= by decide +kernel
def cmds_17 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(4874877920083968,4),(25556429845487524,4),(1709142197372564,4),(3068205663580327,4),(155407234188137,4),(339740315987584,4),(2604121318151,4),(8022327348409,4),(2542950646173,4),(11737711529,4),(3729295857,4),(13582199319,4),(929173795,4),(183002364,4),(44630293,4),(10408535,4),(558255,4),(141810,4),(2163,4),(3134,4)],
  .scan 5 126,
  .scan 0 10,
  .scan2 3 0 [(126,20),(3134,20),(2163,20),(141810,20),(558255,20),(10408535,20),(44630293,20),(183002364,20),(929173795,20),(13582199319,20),(3729295857,20),(11737711529,20),(2542950646173,20),(8022327348409,20),(2604121318151,20),(339740315987584,20),(155407234188137,20),(3068205663580327,20),(1709142197372564,20),(25556429845487524,20)],
  .scan 3 4874877920083963,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [14624633760251909,3656158440062976,914039610015744,228509902503936,57127475625984,14281868906496,3570467226624,892616806656,223154201664,55788550416,13947137604,3486784400,871696102,217924026,54481004,13620252,3405064,851264,212818,53204,13300,3326,832,206,52,14,4,406239826673660] 1 [(.D2,4874877920083969),(.D0,25556429845487525),(.D0,1709142197372565),(.D0,3068205663580328),(.D0,155407234188138),(.D0,339740315987585),(.D0,2604121318152),(.D0,8022327348410),(.D0,2542950646174),(.D0,11737711530),(.D0,3729295858),(.D0,13582199320),(.D0,929173796),(.D0,183002365),(.D0,44630294),(.D0,10408536),(.D0,558256),(.D0,141811),(.D0,2164),(.D0,3135),(.D0,126)],
  .scan 0 50,
  .scan2 5 9 [(9952875753504768,4),(24642390235471781,4),(1556802262369940,4),(3042815674413223,4),(151175569326953,4),(339035038510720,4),(2486575072007,4),(8002736307385,4),(2539685472669,4),(11193515945,4),(3638596593,4),(13567082775,4),(926654371,4),(182582460,4),(44560309,4),(10396871,4),(556311,4),(141486,4),(2109,4),(3125,4)],
  .scan 5 124,
  .scan 0 10,
  .scan2 3 0 [(124,20),(3125,20),(2109,20),(141486,20),(556311,20),(10396871,20),(44560309,20),(182582460,20),(926654371,20),(13567082775,20),(3638596593,20),(11193515945,20),(2539685472669,20),(8002736307385,20),(2486575072007,20),(339035038510720,20),(151175569326953,20),(3042815674413223,20),(1556802262369940,20),(24642390235471781,20)],
  .scan 3 9952875753504763,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21936950640377853] 1 [(.D2,9952875753504769),(.D0,24642390235471782),(.D0,1556802262369941),(.D0,3042815674413224),(.D0,151175569326954),(.D0,339035038510721),(.D0,2486575072008),(.D0,8002736307386),(.D0,2539685472670),(.D0,11193515946),(.D0,3638596594),(.D0,13567082776),(.D0,926654372),(.D0,182582461),(.D0,44560310),(.D0,10396872),(.D0,556312),(.D0,141487),(.D0,2110),(.D0,3126),(.D0,124)],
  .scan 0 50,
  .scan2 5 9 [(10968475320188926,4),(4468638093410305,4),(23728350625456037,4),(1404462327367316,4),(3017425685246119,4),(146943904465769,4),(338329761033856,4),(2369028825863,4),(7983145266361,4),(2536420299165,4),(10649320361,4),(3547897329,4),(13551966231,4),(924134947,4),(182162556,4),(44490325,4),(10385207,4),(554367,4),(141162,4),(2055,4),(3116,4)],
  .scan 5 122,
  .scan 0 10,
  .scan2 3 0 [(122,20),(3116,20),(2055,20),(141162,20),(554367,20),(10385207,20),(44490325,20),(182162556,20),(924134947,20),(13551966231,20),(3547897329,20),(10649320361,20),(2536420299165,20),(7983145266361,20),(2369028825863,20),(338329761033856,20),(146943904465769,20),(3017425685246119,20),(1404462327367316,20),(23728350625456037,20),(4468638093410305,20)],
  .scan 3 10968475320188921,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [32905425960566783,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264900,1961316226,490329056,122582266,30645566,7661392,1915346,478836,119710,29928,7482,1872,468,116,28,8,2,2] 1 [(.D2,10968475320188927),(.D0,4468638093410306),(.D0,23728350625456038),(.D0,1404462327367317),(.D0,3017425685246120),(.D0,146943904465770),(.D0,338329761033857),(.D0,2369028825864),(.D0,7983145266362),(.D0,2536420299166),(.D0,10649320362),(.D0,3547897330),(.D0,13551966232),(.D0,924134948),(.D0,182162557),(.D0,44490326),(.D0,10385208),(.D0,554368),(.D0,141163),(.D0,2056),(.D0,3117),(.D0,122)],
  .batch [2] 21936950640377856 [(.D1,1)],
  .batch [7921676620136450,1980419155034114,495104788758528,123776197189632,30944049297408,7736012324352,1934003081088,483500770272,120875192568,30218798142,7554699534,1888674886,472168722,118042178,29510544,7377636,1844410,461102,115276,28820,7204,1802,450,112,30,6,2] 21936950640377857 [(.D5,2640558873378816),(.D5,23423670755450789),(.D5,1353682349033108),(.D5,3008962355523751),(.D5,145533349512041),(.D5,338094668541568),(.D5,2329846743815),(.D5,7976614919353),(.D5,2535331907997),(.D5,10467921833),(.D5,3517664241),(.D5,13546927383),(.D5,923295139),(.D5,182022588),(.D5,44466997),(.D5,10381319),(.D5,553719),(.D5,141054),(.D5,2037),(.D5,3113),(.D1,122)],
  .batch [2] 27218068387135491 [(.D1,1)],
  .batch [677066377789438] 27218068387135492 [(.D1,22983577609887654),(.D0,1280333491439253),(.D0,2996737545924776),(.D0,143495881245546),(.D0,337755090497153),(.D0,2273250403080),(.D0,7967182195898),(.D0,2533759787422),(.D0,10205901738),(.D0,3473994226),(.D0,13539649048),(.D0,922082084),(.D0,181820413),(.D0,44433302),(.D0,10375704),(.D0,552784),(.D0,140899),(.D2,2011),(.D5,3109),(.D4,120)],
  .scan 0 50,
  .scan2 5 9 [(27556601576030210,4),(22814311015440293,4),(1252122392364692,4),(2992035696079015,4),(142712239604585,4),(337624483556992,4),(2251482579719,4),(7963554225337,4),(2533155125661,4),(10105124777,4),(3457198065,4),(13536849687,4),(921615523,4),(181742652,4),(44420341,4),(10373543,4),(552423,4),(140838,4),(2001,4),(3107,4)],
  .scan 5 120,
  .scan 0 10,
  .scan2 3 0 [(120,20),(3107,20),(2001,20),(140838,20),(552423,20),(10373543,20),(44420341,20),(181742652,20),(921615523,20),(13536849687,20),(3457198065,20),(10105124777,20),(2533155125661,20),(7963554225337,20),(2251482579719,20),(337624483556992,20),(142712239604585,20),(2992035696079015,20),(1252122392364692,20),(22814311015440293,20)],
  .scan 3 27556601576030205,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21936950640377853] 1 [(.D2,27556601576030211),(.D0,22814311015440294),(.D0,1252122392364693),(.D0,2992035696079016),(.D0,142712239604586),(.D0,337624483556993),(.D0,2251482579720),(.D0,7963554225338),(.D0,2533155125662),(.D0,10105124778),(.D0,3457198066),(.D0,13536849688),(.D0,921615524),(.D0,181742653),(.D0,44420342),(.D0,10373544),(.D0,552424),(.D0,140839),(.D0,2002),(.D0,3108),(.D0,120)],
  .scan 0 50,
  .scan2 5 9 [(10968475320188926,4),(22072363915935747,4),(21900271405424549,4),(1099782457362068,4),(2966645706911911,4),(138480574743401,4),(336919206080128,4),(2133936333575,4),(7943963184313,4),(2529889952157,4),(9560929193,4),(3366498801,4),(13521733143,4),(919096099,4),(181322748,4),(44350357,4),(10361879,4),(550479,4),(140514,4),(1947,4),(3098,4)],
  .scan 5 118,
  .scan 0 10,
  .scan2 3 0 [(118,20),(3098,20),(1947,20),(140514,20),(550479,20),(10361879,20),(44350357,20),(181322748,20),(919096099,20),(13521733143,20),(3366498801,20),(9560929193,20),(2529889952157,20),(7943963184313,20),(2133936333575,20),(336919206080128,20),(138480574743401,20),(2966645706911911,20),(1099782457362068,20),(21900271405424549,20),(22072363915935747,20)],
  .scan 3 10968475320188921,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [32905425960566783,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264900,1961316226,490329056,122582266,30645566,7661392,1915346,478836,119710,29928,7482,1872,468,116,28,8,2,2] 1 [(.D2,10968475320188927),(.D0,22072363915935748),(.D0,21900271405424550),(.D0,1099782457362069),(.D0,2966645706911912),(.D0,138480574743402),(.D0,336919206080129),(.D0,2133936333576),(.D0,7943963184314),(.D0,2529889952158),(.D0,9560929194),(.D0,3366498802),(.D0,13521733144),(.D0,919096100),(.D0,181322749),(.D0,44350358),(.D0,10361880),(.D0,550480),(.D0,140515),(.D0,1948),(.D0,3099),(.D0,118)],
  .batch [2] 21936950640377856 [(.D1,1)],
  .batch [14624633760251904] 21936950640377857 [(.D5,20244284695904258),(.D5,21595591535419301),(.D5,1049002479027860),(.D5,2958182377189543),(.D5,137070019789673),(.D5,336684113587840),(.D5,2094754251527),(.D5,7937432837305),(.D5,2528801560989),(.D5,9379530665),(.D5,3336265713),(.D5,13516694295),(.D5,918256291),(.D5,181182780),(.D5,44327029),(.D5,10357991),(.D5,549831),(.D5,140406),(.D5,1929),(.D5,3095),(.D1,118)],
  .scan 0 50,
  .scan2 5 9 [(29249267520503808,4),(16588126255841282,4),(20986231795408805,4),(947442522359444,4),(2941255717744807,4),(134248909882217,4),(336213928603264,4),(2016390087431,4),(7924372143289,4),(2526624778653,4),(9016733609,4),(3275799537,4),(13506616599,4),(916576675,4),(180902844,4),(44280373,4),(10350215,4),(548535,4),(140190,4),(1893,4),(3089,4)],
  .scan 5 116,
  .scan 0 10,
  .scan2 3 0 [(116,20),(3089,20),(1893,20),(140190,20),(548535,20),(10350215,20),(44280373,20),(180902844,20),(916576675,20),(13506616599,20),(3275799537,20),(9016733609,20),(2526624778653,20),(7924372143289,20),(2016390087431,20),(336213928603264,20),(134248909882217,20),(2941255717744807,20),(947442522359444,20),(20986231795408805,20),(16588126255841282,20)],
  .scan 3 29249267520503803,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [87747802561511429,21936950640377856,5484237660094464,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176602,1307544150,326886036,81721510,20430378,5107596,1276898,319224,79806,19950,4990,1248,312,78,18,6,2437438960041980] 1 [(.D2,29249267520503809),(.D0,16588126255841283),(.D0,20986231795408806),(.D0,947442522359445),(.D0,2941255717744808),(.D0,134248909882218),(.D0,336213928603265),(.D0,2016390087432),(.D0,7924372143290),(.D0,2526624778654),(.D0,9016733610),(.D0,3275799538),(.D0,13506616600),(.D0,916576676),(.D0,180902845),(.D0,44280374),(.D0,10350216),(.D0,548536),(.D0,140191),(.D0,1894),(.D0,3090),(.D0,116)],
  .scan 0 50,
  .scan2 5 9 [(59717254521028608,4),(11103888595746819,4),(20072192185393061,4),(795102587356820,4),(2915865728577703,4),(130017245021033,4),(335508651126400,4),(1898843841287,4),(7904781102265,4),(2523359605149,4),(8472538025,4),(3185100273,4),(13491500055,4),(914057251,4),(180482940,4),(44210389,4),(10338551,4),(546591,4),(139866,4),(1839,4),(3080,4)],
  .scan 5 114,
  .scan 0 10,
  .scan2 3 0 [(114,20),(3080,20),(1839,20),(139866,20),(546591,20),(10338551,20),(44210389,20),(180482940,20),(914057251,20),(13491500055,20),(3185100273,20),(8472538025,20),(2523359605149,20),(7904781102265,20),(1898843841287,20),(335508651126400,20),(130017245021033,20),(2915865728577703,20),(795102587356820,20),(20072192185393061,20),(11103888595746819,20)],
  .scan 3 59717254521028603,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [131621703842267133] 1 [(.D2,59717254521028609),(.D0,11103888595746820),(.D0,20072192185393062),(.D0,795102587356821),(.D0,2915865728577704),(.D0,130017245021034),(.D0,335508651126401),(.D0,1898843841288),(.D0,7904781102266),(.D0,2523359605150),(.D0,8472538026),(.D0,3185100274),(.D0,13491500056),(.D0,914057252),(.D0,180482941),(.D0,44210390),(.D0,10338552),(.D0,546592),(.D0,139867),(.D0,1840),(.D0,3081),(.D0,114)],
  .scan 0 50,
  .scan2 5 9 [(65810851921133566,4),(26811828560461825,4),(5619650935652355,4),(19158152575377317,4),(642762652354196,4),(2890475739410599,4),(125785580159849,4),(334803373649536,4),(1781297595143,4),(7885190061241,4),(2520094431645,4),(7928342441,4),(3094401009,4),(13476383511,4),(911537827,4),(180063036,4),(44140405,4),(10326887,4),(544647,4),(139542,4),(1785,4),(3071,4)],
  .scan 5 112,
  .scan 0 10,
  .scan2 3 0 [(112,20),(3071,20),(1785,20),(139542,20),(544647,20),(10326887,20),(44140405,20),(180063036,20),(911537827,20),(13476383511,20),(3094401009,20),(7928342441,20),(2520094431645,20),(7885190061241,20),(1781297595143,20),(334803373649536,20),(125785580159849,20),(2890475739410599,20),(642762652354196,20),(19158152575377317,20),(5619650935652355,20),(26811828560461825,20)],
  .scan 3 65810851921133561,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [197432555763400703,49358138940850176,12339534735212544,3084883683803136,771220920950784,192805230237696,48201307559424,12050326889856,3012581722464,753145430616,188286357654,47071589412,11767897352,2941974340,735493584,183873396,45968348,11492088,2873022,718254,179566,44892,11222,2806,702,174,44,10,2,2,2] 1 [(.D2,65810851921133567),(.D0,26811828560461826),(.D0,5619650935652356),(.D0,19158152575377318),(.D0,642762652354197),(.D0,2890475739410600),(.D0,125785580159850),(.D0,334803373649537),(.D0,1781297595144),(.D0,7885190061242),(.D0,2520094431646),(.D0,7928342442),(.D0,3094401010),(.D0,13476383512),(.D0,911537828),(.D0,180063037),(.D0,44140406),(.D0,10326888),(.D0,544648),(.D0,139543),(.D0,1786),(.D0,3072),(.D0,112)],
  .batch [2] 131621703842267136 [(.D1,1)],
  .batch [47530059720818690,11882514930204674,2970628732551168,742657183137792,185664295784448,46416073946112,11604018486528,2901004621632,725251155408,181312788852,45328197214,11332049304,2833012326,708253080,177063270,44265818,11066454,2766612,691654,172914,43230,10806,2702,676,168,42,12,2] 131621703842267137 [(.D5,15843353240272896),(.D5,3791571715620867),(.D5,18853472705372069),(.D5,591982674019988),(.D5,2882012409688231),(.D5,124375025206121),(.D5,334568281157248),(.D5,1742115513095),(.D5,7878659714233),(.D5,2519006040477),(.D5,7746943913),(.D5,3064167921),(.D5,13471344663),(.D5,910698019),(.D5,179923068),(.D5,44117077),(.D5,10322999),(.D5,543999),(.D5,139434),(.D5,1767),(.D5,3068),(.D1,112)],
  .batch [2] 163308410322812931 [(.D1,1)],
  .batch [3453038526726156,609359740010482] 163308410322812932 [(.D1,1151012842242052),(.D0,18413379559808934),(.D0,518633816426133),(.D0,2869787600089256),(.D0,122337556939626),(.D0,334228703112833),(.D0,1685519172360),(.D0,7869226990778),(.D0,2517433919902),(.D0,7484923818),(.D0,3020497906),(.D0,13464066328),(.D0,909484964),(.D0,179720893),(.D0,44083382),(.D0,10317384),(.D0,543064),(.D0,139279),(.D2,1741),(.D5,3064),(.D4,110)],
  .scan 0 50,
  .scan2 5 9 [(165339609456181250,4),(135413275557891,4),(18244112965361573,4),(490422717351572,4),(2865085750243495,4),(121553915298665,4),(334098096172672,4),(1663751348999,4),(7865599020217,4),(2516829258141,4),(7384146857,4),(3003701745,4),(13461266967,4),(909018403,4),(179643132,4),(44070421,4),(10315223,4),(542703,4),(139218,4),(1731,4),(3062,4)],
  .scan 5 110,
  .scan 0 10,
  .scan2 3 0 [(110,20),(3062,20),(1731,20),(139218,20),(542703,20),(10315223,20),(44070421,20),(179643132,20),(909018403,20),(13461266967,20),(3003701745,20),(7384146857,20),(2516829258141,20),(7865599020217,20),(1663751348999,20),(334098096172672,20),(121553915298665,20),(2865085750243495,20),(490422717351572,20),(18244112965361573,20),(135413275557891,20)],
  .scan 3 165339609456181245,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2437438960042065,609359740010508,152339935002624,38084983750656,9521245937664,2380311484416,595077871104,148769467776,37192366944,9298091736,2324522940,581130732,145282680,36320676,9080172,2270028,567504,141876,35484,8868,2220,552,132,36,12] 1 [(.D2,165339609456181251),(.D0,135413275557892),(.D0,18244112965361574),(.D0,490422717351573),(.D0,2865085750243496),(.D0,121553915298666),(.D0,334098096172673),(.D0,1663751349000),(.D0,7865599020218),(.D0,2516829258142),(.D0,7384146858),(.D0,3003701746),(.D0,13461266968),(.D0,909018404),(.D0,179643133),(.D0,44070422),(.D0,10315224),(.D0,542704),(.D0,139219),(.D0,1732)],
  .batch [21395297538146292] 1624959306694703 [(.D5,164527129802833899),(.D1,18221544086101926),(.D0,486661237474965),(.D0,2864458836930728),(.D0,121449429746538),(.D0,334080681913985),(.D0,1660848972552),(.D0,7865115290810),(.D0,2516748636574),(.D0,7370709930),(.D0,3001462258),(.D0,13460893720),(.D0,908956196),(.D0,179632765),(.D0,44068694),(.D0,10314936),(.D0,542656),(.D2,139210),(.D5,1730),(.D0,3063),(.D0,110)],
  .scan 0 50,
  .scan2 5 9 [(12322608075767848,4),(159178305418297326,4),(17330073355345829,4),(338082782348948,4),(2839695761076391,4),(117322250437481,4),(333392818695808,4),(1546205102855,4),(7846007979193,4),(2513564084637,4),(6839951273,4),(2913002481,4),(13446150423,4),(906498979,4),(179223228,4),(44000437,4),(10303559,4),(540759,4),(138894,4),(1677,4),(3053,4)],
  .scan 5 108,
  .scan 0 10,
  .scan2 3 0 [(108,20),(3053,20),(1677,20),(138894,20),(540759,20),(10303559,20),(44000437,20),(179223228,20),(906498979,20),(13446150423,20),(2913002481,20),(6839951273,20),(2513564084637,20),(7846007979193,20),(1546205102855,20),(333392818695808,20),(117322250437481,20),(2839695761076391,20),(338082782348948,20),(17330073355345829,20),(159178305418297326,20)],
  .scan 3 12322608075767843,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [36967824227303549,9241956056825886,2310489014206472,577622253551616,144405563387904,36101390846976,9025347711744,2256336927936,564084231984,141021057996,35255264500,8813816126,2203454032,550863506,137715876,34428970,8607242,2151810,537954,134488,33624,8406,2100,524,132,34,8,2,2] 1 [(.D2,12322608075767849),(.D0,159178305418297327),(.D0,17330073355345830),(.D0,338082782348949),(.D0,2839695761076392),(.D0,117322250437482),(.D0,333392818695809),(.D0,1546205102856),(.D0,7846007979194),(.D0,2513564084638),(.D0,6839951274),(.D0,2913002482),(.D0,13446150424),(.D0,906498980),(.D0,179223229),(.D0,44000438),(.D0,10303560),(.D0,540760),(.D0,138895),(.D0,1678),(.D0,3054),(.D0,108)],
  .batch [13721878589865958] 24645216151535700 [(.D1,157124537405669352),(.D4,16987778686574500),(.D0,281033670887061),(.D0,2830187575832744),(.D0,115737552896874),(.D0,333128702439041),(.D0,1502185726728),(.D0,7838671416506),(.D0,2512341324190),(.D0,6636157866),(.D0,2879036914),(.D0,13440489496),(.D0,905555492),(.D0,179065981),(.D0,43974230),(.D0,10299192),(.D2,540031),(.D5,138773),(.D2,1657),(.D1,3051),(.D2,107)],
  .scan 0 50,
  .scan2 5 9 [(31506155446468678,4),(153694067758202861,4),(16416033745330085,4),(185742847346324,4),(2814305771909287,4),(113090585576297,4),(332687541218944,4),(1428658856711,4),(7826416938169,4),(2510298911133,4),(6295755689,4),(2822303217,4),(13431033879,4),(903979555,4),(178803324,4),(43930453,4),(10291895,4),(538815,4),(138570,4),(1623,4),(3044,4)],
  .scan 5 106,
  .scan 0 10,
  .scan2 3 0 [(106,20),(3044,20),(1623,20),(138570,20),(538815,20),(10291895,20),(43930453,20),(178803324,20),(903979555,20),(13431033879,20),(2822303217,20),(6295755689,20),(2510298911133,20),(7826416938169,20),(1428658856711,20),(332687541218944,20),(113090585576297,20),(2814305771909287,20),(185742847346324,20),(16416033745330085,20),(153694067758202861,20)],
  .scan 3 31506155446468673,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [94518466339406039,23629616584851510,5907404146212876,1476851036553218,369212759138304,92303189784576,23075797446144,5768949361536,1442237340384,360559335096,90139833774,22534958446,5633739612,1408434902,352108726,88027182,22006794,5501700,1375424,343854,85966,21492,5372,1342,336,84,20,6,2,2] 1 [(.D2,31506155446468679),(.D0,153694067758202862),(.D0,16416033745330086),(.D0,185742847346325),(.D0,2814305771909288),(.D0,113090585576298),(.D0,332687541218945),(.D0,1428658856712),(.D0,7826416938170),(.D0,2510298911134),(.D0,6295755690),(.D0,2822303218),(.D0,13431033880),(.D0,903979556),(.D0,178803325),(.D0,43930454),(.D0,10291896),(.D0,538816),(.D0,138571),(.D0,1624),(.D0,3045),(.D0,106)],
  .batch [2] 63012310892937360 [(.D1,1)],
  .batch [932847009398736] 63012310892937361 [(.D5,148443041850458080),(.D1,15540862760705956),(.D1,39881016575637),(.D0,2789995466780840),(.D0,109038868054890),(.D0,332012254965377),(.D0,1316111147784),(.D0,7807658986682),(.D0,2507172585886),(.D0,5774701482),(.D0,2735460850),(.D0,13416560152),(.D0,901567268),(.D0,178401277),(.D0,43863446),(.D2,10280727),(.D5,536954),(.D4,138260),(.D2,1572),(.D4,3035),(.D5,104)],
  .scan 0 50,
  .scan2 5 9 [(63478734397636728,4),(148209830098108396,4),(15501994135314341,4),(33402912343700,4),(2788915782742183,4),(108858920715113,4),(331982263742080,4),(1311112610567,4),(7806825897145,4),(2507033737629,4),(5751560105,4),(2731603953,4),(13415917335,4),(901460131,4),(178383420,4),(43860469,4),(10280231,4),(536871,4),(138246,4),(1569,4),(3035,4)],
  .scan 5 104,
  .scan 0 10,
  .scan2 3 0 [(104,20),(3035,20),(1569,20),(138246,20),(536871,20),(10280231,20),(43860469,20),(178383420,20),(901460131,20),(13415917335,20),(2731603953,20),(5751560105,20),(2507033737629,20),(7806825897145,20),(1311112610567,20),(331982263742080,20),(108858920715113,20),(2788915782742183,20),(33402912343700,20),(15501994135314341,20),(148209830098108396,20)],
  .scan 3 63478734397636723,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21645087198718461] 1 [(.D2,63478734397636729),(.D0,148209830098108397),(.D0,15501994135314342),(.D0,33402912343701),(.D0,2788915782742184),(.D0,108858920715114),(.D0,331982263742081),(.D0,1311112610568),(.D0,7806825897146),(.D0,2507033737630),(.D0,5751560106),(.D0,2731603954),(.D0,13415917336),(.D0,901460132),(.D0,178383421),(.D0,43860470),(.D0,10280232),(.D0,536872),(.D0,138247),(.D0,1570),(.D0,3036)],
  .batch [5411271799679616,1352817949919472,338204487479760,84551121870480,21137780467728,5284445116608,1321111279152,330277820112,82569454704,20642364000,5160590784,1290147264,322536816,80634528,20158848,5039280,1259712,314928,79056,19440,5184,1296,432,432] 10822543599359231 [(.D5,58067462597957113),(.D5,147307951464828460),(.D5,15351681029767685),(.D3,8350728085925),(.D4,2784740418699220),(.D5,108163026707953),(.D0,331866281407554),(.D3,1291782221480),(.D4,7803604165630),(.D1,2506496782378),(.D4,5662067563),(.D4,2716688529),(.D1,13413431432),(.D3,901045814),(.D1,178314368),(.D3,43848961),(.D4,10278313),(.D0,536552),(.D3,138193),(.D5,1560),(.D5,3034),(.D0,104)],
  .batch [17126931262885344] 14430058132479047 [(.D5,56263705331397205),(.D5,147007325253735142),(.D5,15301576661252132),(.D1,2783348630684900),(.D1,107931062038900),(.D1,331827620629379),(.D0,1285338758451),(.D2,7802530255126),(.D4,2506317797292),(.D1,5632236717),(.D2,2711716722),(.D2,13412602797),(.D0,900907709),(.D2,178291350),(.D0,43845125),(.D0,10277674),(.D1,536446),(.D2,138175),(.D5,1557),(.D1,3034),(.D1,104)]
]
lemma chunk_17_ok : q6 cmds_17 cfg_17=some cfg_18:= by decide +kernel
def cmds_18 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(22993523763921718,4),(51981972515675869,4),(146293703117781586,4),(15182639638593206,4),(2763525793575078,4),(104627255853929,4),(331276986265216,4),(1193566364423,4),(7787234856121,4),(2503768564125,4),(5207364521,4),(2640904689,4),(13400800791,4),(898940707,4),(177963516,4),(43790485,4),(10268567,4),(534927,4),(137922,4),(1515,4),(3026,4)],
  .scan 5 102,
  .scan 0 10,
  .scan2 3 0 [(102,20),(3026,20),(1515,20),(137922,20),(534927,20),(10268567,20),(43790485,20),(177963516,20),(898940707,20),(13400800791,20),(2640904689,20),(5207364521,20),(2503768564125,20),(7787234856121,20),(1193566364423,20),(331276986265216,20),(104627255853929,20),(2763525793575078,20),(15182639638593206,20),(146293703117781586,20),(51981972515675869,20)],
  .scan 3 22993523763921713,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [68980571291765159,17245142822941290,4311285705735320,1077821426433832,269455356608456,67363839152116,16840959788028,4210239947006,1052559986752,263139996690,65784999170,16446249792,4111562448,1027890612,256972654,64243164,16060790,4015198,1003800,250950,62738,15684,3922,980,244,62,16,2,2,2] 1 [(.D2,22993523763921719),(.D0,51981972515675870),(.D0,146293703117781587),(.D0,15182639638593207),(.D0,2763525793575079),(.D0,104627255853930),(.D0,331276986265217),(.D0,1193566364424),(.D0,7787234856122),(.D0,2503768564126),(.D0,5207364522),(.D0,2640904690),(.D0,13400800792),(.D0,898940708),(.D0,177963517),(.D0,43790486),(.D0,10268568),(.D0,534928),(.D0,137923),(.D0,1516),(.D0,3027),(.D0,102)],
  .batch [2] 45987047527843440 [(.D1,1)],
  .batch [6607934797763376] 45987047527843441 [(.D5,48149718555022248),(.D5,145654994124339316),(.D5,15076188139686161),(.D5,2745783877090571),(.D0,101670269773179),(.D2,330784155251758),(.D2,1111427862180),(.D1,7773545105748),(.D5,2501486939063),(.D4,4827093677),(.D5,2577526215),(.D3,13390237713),(.D2,897180194),(.D3,177670098),(.D0,43741583),(.D4,10260416),(.D3,533569),(.D5,137696),(.D0,1478),(.D1,3021),(.D4,100)],
  .scan 0 50,
  .scan2 5 9 [(49291014926725128,4),(46497734855581404,4),(145379663507765842,4),(15030299703590582,4),(2738135804407974,4),(100395590992745,4),(330571708788352,4),(1076020118279,4),(7767643815097,4),(2500503390621,4),(4663168937,4),(2550205425,4),(13385684247,4),(896421283,4),(177543612,4),(43720501,4),(10256903,4),(532983,4),(137598,4),(1461,4),(3017,4)],
  .scan 5 100,
  .scan 0 10,
  .scan2 3 0 [(100,20),(3017,20),(1461,20),(137598,20),(532983,20),(10256903,20),(43720501,20),(177543612,20),(896421283,20),(13385684247,20),(2550205425,20),(4663168937,20),(2500503390621,20),(7767643815097,20),(1076020118279,20),(330571708788352,20),(100395590992745,20),(2738135804407974,20),(15030299703590582,20),(145379663507765842,20),(46497734855581404,20)],
  .scan 3 49291014926725123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [131621703842267133] 1 [(.D2,49291014926725129),(.D0,46497734855581405),(.D0,145379663507765843),(.D0,15030299703590583),(.D0,2738135804407975),(.D0,100395590992746),(.D0,330571708788353),(.D0,1076020118280),(.D0,7767643815098),(.D0,2500503390622),(.D0,4663168938),(.D0,2550205426),(.D0,13385684248),(.D0,896421284),(.D0,177543613),(.D0,43720502),(.D0,10256904),(.D0,532984),(.D0,137599),(.D0,1462),(.D0,3018),(.D0,100)],
  .scan 0 50,
  .scan2 5 9 [(65810851921133566,4),(16385588966158345,4),(41013497195486940,4),(144465623897750098,4),(14877959768587958,4),(2712745815240870,4),(96163926131561,4),(329866431311488,4),(958473872135,4),(7748052774073,4),(2497238217117,4),(4118973353,4),(2459506161,4),(13370567703,4),(893901859,4),(177123708,4),(43650517,4),(10245239,4),(531039,4),(137274,4),(1407,4),(3008,4)],
  .scan 5 98,
  .scan 0 10,
  .scan2 3 0 [(98,20),(3008,20),(1407,20),(137274,20),(531039,20),(10245239,20),(43650517,20),(177123708,20),(893901859,20),(13370567703,20),(2459506161,20),(4118973353,20),(2497238217117,20),(7748052774073,20),(958473872135,20),(329866431311488,20),(96163926131561,20),(2712745815240870,20),(14877959768587958,20),(144465623897750098,20),(41013497195486940,20),(16385588966158345,20)],
  .scan 3 65810851921133561,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [197432555763400703,49358138940850176,12339534735212544,3084883683803136,771220920950784,192805230237696,48201307559424,12050326889856,3012581722464,753145430616,188286357654,47071589412,11767897352,2941974340,735493584,183873396,45968348,11492088,2873022,718254,179566,44892,11222,2806,702,174,44,10,2,2,2] 1 [(.D2,65810851921133567),(.D0,16385588966158346),(.D0,41013497195486941),(.D0,144465623897750099),(.D0,14877959768587959),(.D0,2712745815240871),(.D0,96163926131562),(.D0,329866431311489),(.D0,958473872136),(.D0,7748052774074),(.D0,2497238217118),(.D0,4118973354),(.D0,2459506162),(.D0,13370567704),(.D0,893901860),(.D0,177123709),(.D0,43650518),(.D0,10245240),(.D0,531040),(.D0,137275),(.D0,1408),(.D0,3009),(.D0,98)],
  .batch [2] 131621703842267136 [(.D1,1)],
  .batch [16251340937908250,4062835234477064,1015708808619264,253927202154816,63481800538704,15870450134676,3967612533670,991903133418,247975783356,61993945838,15498486460,3874621614,968655404,242163850,60540962,15135240,3783810,945954,236488,59124,14780,3694,924,230,58,14,4,2] 131621703842267137 [(.D5,5417113645969416),(.D5,39185417975455452),(.D5,144160944027744850),(.D5,14827179790253750),(.D5,2704282485518502),(.D5,94753371177833),(.D5,329631338819200),(.D5,919291790087),(.D5,7741522427065),(.D5,2496149825949),(.D5,3937574825),(.D5,2429273073),(.D5,13365528855),(.D5,893062051),(.D5,176983740),(.D5,43627189),(.D5,10241351),(.D5,530391),(.D5,137166),(.D5,1389),(.D5,3005),(.D1,98)],
  .batch [2] 142455931134205971 [(.D1,1)],
  .batch [11013224662938958] 142455931134205972 [(.D1,38282565701127217),(.D0,144010468648690145),(.D0,14802100560411300),(.D4,2700102613878093),(.D3,94056725904432),(.D5,329515231273633),(.D1,899940532494),(.D4,7738297217466),(.D0,2495612291017),(.D4,3847985669),(.D3,2414341548),(.D2,13363040268),(.D4,892647286),(.D5,176914613),(.D4,43615668),(.D0,10239432),(.D2,530071),(.D3,137113),(.D5,1380),(.D5,3004),(.D2,97)],
  .scan 0 50,
  .scan2 5 9 [(147962543465675450,4),(35529259535392476,4),(143551584287734354,4),(14725619833585334,4),(2687355826073766,4),(91932261270377,4),(329161153834624,4),(840927625991,4),(7728461733049,4),(2493973043613,4),(3574777769,4),(2368806897,4),(13355451159,4),(891382435,4),(176703804,4),(43580533,4),(10233575,4),(529095,4),(136950,4),(1353,4),(2999,4)],
  .scan 5 96,
  .scan 0 10,
  .scan2 3 0 [(96,20),(2999,20),(1353,20),(136950,20),(529095,20),(10233575,20),(43580533,20),(176703804,20),(891382435,20),(13355451159,20),(2368806897,20),(3574777769,20),(2493973043613,20),(7728461733049,20),(840927625991,20),(329161153834624,20),(91932261270377,20),(2687355826073766,20),(14725619833585334,20),(143551584287734354,20),(35529259535392476,20)],
  .scan 3 147962543465675445,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [131621703842267133] 1 [(.D2,147962543465675451),(.D0,35529259535392477),(.D0,143551584287734355),(.D0,14725619833585335),(.D0,2687355826073767),(.D0,91932261270378),(.D0,329161153834625),(.D0,840927625992),(.D0,7728461733050),(.D0,2493973043614),(.D0,3574777770),(.D0,2368806898),(.D0,13355451160),(.D0,891382436),(.D0,176703805),(.D0,43580534),(.D0,10233576),(.D0,529096),(.D0,136951),(.D0,1354),(.D0,3000),(.D0,96)],
  .scan 0 50,
  .scan2 5 9 [(65810851921133566,4),(115057117505108667,4),(30045021875298012,4),(142637544677718610,4),(14573279898582710,4),(2661965836906662,4),(87700596409193,4),(328455876357760,4),(723381379847,4),(7708870692025,4),(2490707870109,4),(3030582185,4),(2278107633,4),(13340334615,4),(888863011,4),(176283900,4),(43510549,4),(10221911,4),(527151,4),(136626,4),(1299,4),(2990,4)],
  .scan 5 94,
  .scan 0 10,
  .scan2 3 0 [(94,20),(2990,20),(1299,20),(136626,20),(527151,20),(10221911,20),(43510549,20),(176283900,20),(888863011,20),(13340334615,20),(2278107633,20),(3030582185,20),(2490707870109,20),(7708870692025,20),(723381379847,20),(328455876357760,20),(87700596409193,20),(2661965836906662,20),(14573279898582710,20),(142637544677718610,20),(30045021875298012,20),(115057117505108667,20)],
  .scan 3 65810851921133561,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [197432555763400703,49358138940850176,12339534735212544,3084883683803136,771220920950784,192805230237696,48201307559424,12050326889856,3012581722464,753145430616,188286357654,47071589412,11767897352,2941974340,735493584,183873396,45968348,11492088,2873022,718254,179566,44892,11222,2806,702,174,44,10,2,2,2] 1 [(.D2,65810851921133567),(.D0,115057117505108668),(.D0,30045021875298013),(.D0,142637544677718611),(.D0,14573279898582711),(.D0,2661965836906663),(.D0,87700596409194),(.D0,328455876357761),(.D0,723381379848),(.D0,7708870692026),(.D0,2490707870110),(.D0,3030582186),(.D0,2278107634),(.D0,13340334616),(.D0,888863012),(.D0,176283901),(.D0,43510550),(.D0,10221912),(.D0,527152),(.D0,136627),(.D0,1300),(.D0,2991),(.D0,94)],
  .batch [2] 131621703842267136 [(.D1,1)],
  .batch [87747802561511424] 131621703842267137 [(.D5,104088642184919738),(.D5,28216942655266524),(.D5,142332864807713362),(.D5,14522499920248502),(.D5,2653502507184294),(.D5,86290041455465),(.D5,328220783865472),(.D5,684199297799),(.D5,7702340345017),(.D5,2489619478941),(.D5,2849183657),(.D5,2247874545),(.D5,13335295767),(.D5,888023203),(.D5,176143932),(.D5,43487221),(.D5,10218023),(.D5,526503),(.D5,136518),(.D5,1281),(.D5,2987),(.D1,94)],
  .scan 0 50,
  .scan2 5 9 [(175495605123022848,4),(82151691544541882,4),(24560784215203548,4),(141723505067702866,4),(14420939963580086,4),(2636575847739558,4),(83468931548009,4),(327750598880896,4),(605835133703,4),(7689279651001,4),(2487442696605,4),(2486386601,4),(2187408369,4),(13325218071,4),(886343587,4),(175863996,4),(43440565,4),(10210247,4),(525207,4),(136302,4),(1245,4),(2981,4)],
  .scan 5 92,
  .scan 0 10,
  .scan2 3 0 [(92,20),(2981,20),(1245,20),(136302,20),(525207,20),(10210247,20),(43440565,20),(175863996,20),(886343587,20),(13325218071,20),(2187408369,20),(2486386601,20),(2487442696605,20),(7689279651001,20),(605835133703,20),(327750598880896,20),(83468931548009,20),(2636575847739558,20),(14420939963580086,20),(141723505067702866,20),(24560784215203548,20),(82151691544541882,20)],
  .scan 3 175495605123022843,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [526486815369068549,131621703842267136,32905425960566784,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264904,1961316224,490329058,122582264,30645564,7661392,1915350,478836,119708,29928,7482,1870,468,116,30,6,4,14624633760251900] 1 [(.D2,175495605123022849),(.D0,82151691544541883),(.D0,24560784215203549),(.D0,141723505067702867),(.D0,14420939963580087),(.D0,2636575847739559),(.D0,83468931548010),(.D0,327750598880897),(.D0,605835133704),(.D0,7689279651002),(.D0,2487442696606),(.D0,2486386602),(.D0,2187408370),(.D0,13325218072),(.D0,886343588),(.D0,175863997),(.D0,43440566),(.D0,10210248),(.D0,525208),(.D0,136303),(.D0,1246),(.D0,2982),(.D0,92)],
  .scan 0 50,
  .scan2 5 9 [(358303527126171648,4),(49246265583975099,4),(19076546555109084,4),(140809465457687122,4),(14268600028577462,4),(2611185858572454,4),(79237266686825,4),(327045321404032,4),(488288887559,4),(7669688609977,4),(2484177523101,4),(1942191017,4),(2096709105,4),(13310101527,4),(883824163,4),(175444092,4),(43370581,4),(10198583,4),(523263,4),(135978,4),(1191,4),(2972,4)],
  .scan 5 90,
  .scan 0 10,
  .scan2 3 0 [(90,20),(2972,20),(1191,20),(135978,20),(523263,20),(10198583,20),(43370581,20),(175444092,20),(883824163,20),(13310101527,20),(2096709105,20),(1942191017,20),(2484177523101,20),(7669688609977,20),(488288887559,20),(327045321404032,20),(79237266686825,20),(2611185858572454,20),(14268600028577462,20),(140809465457687122,20),(19076546555109084,20),(49246265583975099,20)],
  .scan 3 358303527126171643,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,358303527126171649),(.D0,49246265583975100),(.D0,19076546555109085),(.D0,140809465457687123),(.D0,14268600028577463),(.D0,2611185858572455),(.D0,79237266686826),(.D0,327045321404033),(.D0,488288887560),(.D0,7669688609978),(.D0,2484177523102),(.D0,1942191018),(.D0,2096709106),(.D0,13310101528),(.D0,883824164),(.D0,175444093),(.D0,43370582),(.D0,10198584),(.D0,523264),(.D0,135979),(.D0,1192),(.D0,2973),(.D0,90)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(160870971362770945,4),(16340839623408315,4),(13592308895014620,4),(139895425847671378,4),(14116260093574838,4),(2585795869405350,4),(75005601825641,4),(326340043927168,4),(370742641415,4),(7650097568953,4),(2480912349597,4),(1397995433,4),(2006009841,4),(13294984983,4),(881304739,4),(175024188,4),(43300597,4),(10186919,4),(521319,4),(135654,4),(1137,4),(2963,4)],
  .scan 5 88,
  .scan 0 10,
  .scan2 3 0 [(88,20),(2963,20),(1137,20),(135654,20),(521319,20),(10186919,20),(43300597,20),(175024188,20),(881304739,20),(13294984983,20),(2006009841,20),(1397995433,20),(2480912349597,20),(7650097568953,20),(370742641415,20),(326340043927168,20),(75005601825641,20),(2585795869405350,20),(14116260093574838,20),(139895425847671378,20),(13592308895014620,20),(16340839623408315,20),(160870971362770945,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,160870971362770946),(.D0,16340839623408316),(.D0,13592308895014621),(.D0,139895425847671379),(.D0,14116260093574839),(.D0,2585795869405351),(.D0,75005601825642),(.D0,326340043927169),(.D0,370742641416),(.D0,7650097568954),(.D0,2480912349598),(.D0,1397995434),(.D0,2006009842),(.D0,13294984984),(.D0,881304740),(.D0,175024189),(.D0,43300598),(.D0,10186920),(.D0,521320),(.D0,135655),(.D0,1138),(.D0,2964),(.D0,88)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [96702557457948972,24175639364487252,6043909841121816,1510977460280448,377744365070124,94436091267528,23609022816876,5902255704216,1475563926060,368890981512,92222745384,23055686340,5763921588,1440980400,360245088,90061272,22515324,5628828,1407204,351816,87948,21996,5484,1368,348,84,24,12] 789730223053602817 [(.D5,95060119441637376),(.D5,5372364303219387),(.D5,11764229674983132),(.D5,139590745977666130),(.D5,14065480115240630),(.D5,2577332539682982),(.D5,73595046871913),(.D5,326104951434880),(.D5,331560559367),(.D5,7643567221945),(.D5,2479823958429),(.D5,1216596905),(.D5,1975776753),(.D5,13289946135),(.D5,880464931),(.D5,174884220),(.D5,43277269),(.D5,10183031),(.D5,520671),(.D5,135546),(.D5,1119),(.D5,2960),(.D1,88)],
  .batch [66258345348633876] 854198594692235473 [(.D5,62825933622321048),(.D1,10868835624446569),(.D0,139441513635910037),(.D4,14040608058281281),(.D0,2573187196856425),(.D2,72904156400820),(.D1,325989803023032),(.D1,312369157393),(.D1,7640368654950),(.D5,2479290863930),(.D0,1127747823),(.D2,1960968573),(.D2,13287478105),(.D3,880053593),(.D1,174815665),(.D2,43265843),(.D3,10181127),(.D3,520354),(.D1,135494),(.D5,1110),(.D5,2959),(.D2,87)],
  .scan 0 50,
  .scan2 5 9 [(887327767366552410,4),(46261347285162579,4),(8108071234920156,4),(138981386237655634,4),(13963920158572214,4),(2560405880238246,4),(70773936964457,4),(325634766450304,4),(253196395271,4),(7630506527929,4),(2477647176093,4),(853799849,4),(1915310577,4),(13279868439,4),(878785315,4),(174604284,4),(43230613,4),(10175255,4),(519375,4),(135330,4),(1083,4),(2954,4)],
  .scan 5 86,
  .scan 0 10,
  .scan2 3 0 [(86,20),(2954,20),(1083,20),(135330,20),(519375,20),(10175255,20),(43230613,20),(174604284,20),(878785315,20),(13279868439,20),(1915310577,20),(853799849,20),(2477647176093,20),(7630506527929,20),(253196395271,20),(325634766450304,20),(70773936964457,20),(2560405880238246,20),(13963920158572214,20),(138981386237655634,20),(8108071234920156,20),(46261347285162579,20)],
  .scan 3 887327767366552405,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,887327767366552411),(.D0,46261347285162580),(.D0,8108071234920157),(.D0,138981386237655635),(.D0,13963920158572215),(.D0,2560405880238247),(.D0,70773936964458),(.D0,325634766450305),(.D0,253196395272),(.D0,7630506527930),(.D0,2477647176094),(.D0,853799850),(.D0,1915310578),(.D0,13279868440),(.D0,878785316),(.D0,174604285),(.D0,43230614),(.D0,10175256),(.D0,519376),(.D0,135331),(.D0,1084),(.D0,2955),(.D0,86)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(689895211603151707,4),(13355921324595795,4),(2623833574825692,4),(138067346627639890,4),(13811580223569590,4),(2535015891071142,4),(66542272103273,4),(324929488973440,4),(135650149127,4),(7610915486905,4),(2474382002589,4),(309604265,4),(1824611313,4),(13264751895,4),(876265891,4),(174184380,4),(43160629,4),(10163591,4),(517431,4),(135006,4),(1029,4),(2945,4)],
  .scan 5 84,
  .scan 0 10,
  .scan2 3 0 [(84,20),(2945,20),(1029,20),(135006,20),(517431,20),(10163591,20),(43160629,20),(174184380,20),(876265891,20),(13264751895,20),(1824611313,20),(309604265,20),(2474382002589,20),(7610915486905,20),(135650149127,20),(324929488973440,20),(66542272103273,20),(2535015891071142,20),(13811580223569590,20),(138067346627639890,20),(2623833574825692,20),(13355921324595795,20),(689895211603151707,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,689895211603151708),(.D0,13355921324595796),(.D0,2623833574825693),(.D0,138067346627639891),(.D0,13811580223569591),(.D0,2535015891071143),(.D0,66542272103274),(.D0,324929488973441),(.D0,135650149128),(.D0,7610915486906),(.D0,2474382002590),(.D0,309604266),(.D0,1824611314),(.D0,13264751896),(.D0,876265892),(.D0,174184381),(.D0,43160630),(.D0,10163592),(.D0,517432),(.D0,135007),(.D0,1030),(.D0,2946),(.D0,84)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [42974028079323612,10743507019830912,2685876754957740,671469188739420,167867297184852,41966824296228,10491706074060,2622926518500,655731629628,163932907404,40983226848,10245806712,2561451684,640362924,160090740,40022676,10005672,2501412,625356,156348,39072,9780,2448,612,144,36,12] 789730223053602817 [(.D5,624084359682018138),(.D5,2387446004406867),(.D5,795754354794204),(.D5,137762666757634642),(.D5,13760800245235382),(.D5,2526552561348774),(.D5,65131717149545),(.D5,324694396481152),(.D5,96468067079),(.D5,7604385139897),(.D5,2473293611421),(.D5,128205737),(.D5,1794378225),(.D5,13259713047),(.D5,875426083),(.D5,174044412),(.D5,43137301),(.D5,10159703),(.D5,516783),(.D5,134898),(.D5,1011),(.D5,2942),(.D1,84)],
  .batch [12] 818379575106485233 [(.D5,609759683655576930),(.D1,1)],
  .batch [7161240373075068,1790310093268776,447577523317200,111894380829288,27973595207328,6993398801844,1748349700452,437087425116,109271856276,27317964060,6829491024,1707372756,426843180,106710804,26677692,6669432,1667364,416844,104196,26052,6516,1632,396,108,24,12] 818379575106485239 [(.D5,609759683655576927),(.D5,397846687393059),(.D3,137696348813067785),(.D3,13749747254474240),(.D2,2524710396221917),(.D1,64824689628403),(.D5,324643225227628),(.D5,87939524825),(.D5,7602963716188),(.D3,2473056707470),(.D1,88721746),(.D1,1787797561),(.D0,13258616270),(.D1,875243288),(.D4,174013946),(.D0,43132224),(.D1,10158858),(.D0,516643),(.D4,134874),(.D3,1008),(.D2,2942)],
  .batch [1488792306306192,372198054868992,93049523794944,23262365832192,5815616652288,1453909201920,363462183936,90880662528,22694971392,5683820544,1431032832,362797056,80621568,20155392,20155392] 823153735355201959 [(.D5,607372603531218567),(.D1,137630041031835609),(.D1,13738695957602211),(.D2,2522868513409912),(.D3,64517709159735),(.D5,324592061816184),(.D4,79412289584),(.D1,7601542510316),(.D2,2472819839824),(.D3,49243805),(.D0,1781217904),(.D0,13257519661),(.D4,875060518),(.D1,173983486),(.D4,43127146),(.D1,10158012),(.D0,516502),(.D2,134851),(.D1,1004),(.D5,2941),(.D2,83)],
  .batch [20155392] 824146263561730543 [(.D5,606876339427954275),(.D5,137547330347958226),(.D5,13724910843622646),(.D5,2520570994413318),(.D5,64134789326969),(.D5,324528241844056),(.D5,68775627563),(.D5,7599769733311),(.D5,2472524376990),(.D1,1)],
  .batch [1576093324695552] 824146263571808239 [(.D5,606876339422915427),(.D5,137547330347118418),(.D5,13724910843482678),(.D5,2520570994389990),(.D5,64134789323081),(.D5,324528241843408),(.D5,68775627455),(.D5,7599769733293),(.D5,2472524376987),(.D5,1773010601),(.D1,13256151778),(.D4,874832538),(.D2,173945488),(.D3,43120814),(.D5,10156955),(.D1,516326),(.D5,134822),(.D2,999),(.D2,2940),(.D3,83)],
  .scan 0 50,
  .scan2 5 9 [(824934310234156014,4),(606482316091741539,4),(137481659791922770,4),(13713965750950070,4),(2518746812301222,4),(63830758974953,4),(324477570118720,4),(60330340007,4),(7598362185385,4),(2472289785669,4),(1733912048,4),(13249635351,4),(873746467,4),(173764476,4),(43090645,4),(10151927,4),(515487,4),(134682,4),(975,4),(2936,4)],
  .scan 5 82,
  .scan 0 10,
  .scan2 3 0 [(82,20),(2936,20),(975,20),(134682,20),(515487,20),(10151927,20),(43090645,20),(173764476,20),(873746467,20),(13249635351,20),(1733912048,20),(2472289785669,20),(7598362185385,20),(60330340007,20),(324477570118720,20),(63830758974953,20),(2518746812301222,20),(13713965750950070,20),(137481659791922770,20),(606482316091741539,20)],
  .scan 3 824934310234156009,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [21936950640377853] 1 [(.D2,824934310234156015),(.D0,606482316091741540),(.D0,137481659791922771),(.D0,13713965750950071),(.D0,2518746812301223),(.D0,63830758974954),(.D0,324477570118721),(.D0,60330340008),(.D0,7598362185386),(.D0,2472289785670),(.D0,1733912049),(.D0,13249635352),(.D0,873746468),(.D0,173764477),(.D0,43090646),(.D0,10151928),(.D0,515488),(.D0,134683),(.D0,976),(.D0,2937),(.D0,82)],
  .scan 0 50,
  .scan2 5 9 [(10968475320188926,4),(819450072574061551,4),(605568276481725795,4),(137329319856920146,4),(13688575761782966,4),(2514515147440038,4),(63125481498089,4),(324360023872576,4),(40739298983,4),(7595097011881,4),(2471745590085,4),(1643212784,4),(13234518807,4),(871227043,4),(173344572,4),(43020661,4),(10140263,4),(513543,4),(134358,4),(921,4),(2927,4)],
  .scan 5 80,
  .scan 0 10,
  .scan2 3 0 [(80,20),(2927,20),(921,20),(134358,20),(513543,20),(10140263,20),(43020661,20),(173344572,20),(871227043,20),(13234518807,20),(1643212784,20),(2471745590085,20),(7595097011881,20),(40739298983,20),(324360023872576,20),(63125481498089,20),(2514515147440038,20),(13688575761782966,20),(137329319856920146,20),(605568276481725795,20),(819450072574061551,20)],
  .scan 3 10968475320188921,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [32905425960566783,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264900,1961316226,490329056,122582266,30645566,7661392,1915346,478836,119710,29928,7482,1872,468,116,28,8,2,2] 1 [(.D2,10968475320188927),(.D0,819450072574061552),(.D0,605568276481725796),(.D0,137329319856920147),(.D0,13688575761782967),(.D0,2514515147440039),(.D0,63125481498090),(.D0,324360023872577),(.D0,40739298984),(.D0,7595097011882),(.D0,2471745590086),(.D0,1643212785),(.D0,13234518808),(.D0,871227044),(.D0,173344573),(.D0,43020662),(.D0,10140264),(.D0,513544),(.D0,134359),(.D0,922),(.D0,2928),(.D0,80)],
  .batch [2] 21936950640377856 [(.D1,1)],
  .batch [14624633760251904] 21936950640377857 [(.D5,817621993354030062),(.D5,605263596611720547),(.D5,137278539878585938),(.D5,13680112432060598),(.D5,2513104592486310),(.D5,62890389005801),(.D5,324320841790528),(.D5,34208951975),(.D5,7594008620713),(.D5,2471564191557),(.D5,1612979696),(.D5,13229479959),(.D5,870387235),(.D5,173204604),(.D5,42997333),(.D5,10136375),(.D5,512895),(.D5,134250),(.D5,903),(.D5,2924),(.D1,80)]
]
lemma chunk_18_ok : q6 cmds_18 cfg_18=some cfg_19:= by decide +kernel
def cmds_19 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(29249267520503808,4),(813965834913967086,4),(604654236871710051,4),(137176979921917522,4),(13663185772615862,4),(2510283482578854,4),(62420204021225,4),(324242477626432,4),(21148257959,4),(7591831838377,4),(2471201394501,4),(1552513520,4),(13219402263,4),(868707619,4),(172924668,4),(42950677,4),(10128599,4),(511599,4),(134034,4),(867,4),(2918,4)],
  .scan 5 78,
  .scan 0 10,
  .scan2 3 0 [(78,20),(2918,20),(867,20),(134034,20),(511599,20),(10128599,20),(42950677,20),(172924668,20),(868707619,20),(13219402263,20),(1552513520,20),(2471201394501,20),(7591831838377,20),(21148257959,20),(324242477626432,20),(62420204021225,20),(2510283482578854,20),(13663185772615862,20),(137176979921917522,20),(604654236871710051,20),(813965834913967086,20)],
  .scan 3 29249267520503803,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [87747802561511429,21936950640377856,5484237660094464,1371059415023616,342764853755904,85691213438976,21422803359744,5355700839936,1338925209984,334731302496,83682825624,20920706406,5230176602,1307544150,326886036,81721510,20430378,5107596,1276898,319224,79806,19950,4990,1248,312,78,18,6,2437438960041980] 1 [(.D2,29249267520503809),(.D0,813965834913967087),(.D0,604654236871710052),(.D0,137176979921917523),(.D0,13663185772615863),(.D0,2510283482578855),(.D0,62420204021226),(.D0,324242477626433),(.D0,21148257960),(.D0,7591831838378),(.D0,2471201394502),(.D0,1552513521),(.D0,13219402264),(.D0,868707620),(.D0,172924669),(.D0,42950678),(.D0,10128600),(.D0,511600),(.D0,134035),(.D0,868),(.D0,2919),(.D0,78)],
  .scan 0 50,
  .scan2 5 9 [(59717254521028608,4),(808481597253872623,4),(603740197261694307,4),(137024639986914898,4),(13637795783448758,4),(2506051817717670,4),(61714926544361,4),(324124931380288,4),(1557216935,4),(7588566664873,4),(2470657198917,4),(1461814256,4),(13204285719,4),(866188195,4),(172504764,4),(42880693,4),(10116935,4),(509655,4),(133710,4),(813,4),(2909,4)],
  .scan 5 76,
  .scan 0 10,
  .scan2 3 0 [(76,20),(2909,20),(813,20),(133710,20),(509655,20),(10116935,20),(42880693,20),(172504764,20),(866188195,20),(13204285719,20),(1461814256,20),(2470657198917,20),(7588566664873,20),(1557216935,20),(324124931380288,20),(61714926544361,20),(2506051817717670,20),(13637795783448758,20),(137024639986914898,20),(603740197261694307,20),(808481597253872623,20)],
  .scan 3 59717254521028603,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7846579446888957,1961644860882432,490411212701184,122602804015104,30650697644544,7662676930560,1915669232640,478918987776,119726387712,29930757120,7484368896,1874451456,466933248,117573120,30233088,3359232,3359232,3359232] 1 [(.D2,59717254521028609),(.D0,808481597253872624),(.D0,603740197261694308),(.D0,137024639986914899),(.D0,13637795783448759),(.D0,2506051817717671),(.D0,61714926544362),(.D0,324124931380289),(.D0,1557216936),(.D0,7588566664874),(.D0,2470657198918),(.D0,1461814257),(.D0,13204285720),(.D0,866188196),(.D0,172504765),(.D0,42880694),(.D0,10116936),(.D0,509656),(.D0,133711),(.D0,814),(.D0,2910)],
  .batch [3359232] 5231052964032767 [(.D5,57101728039012225),(.D5,808045676173536559),(.D5,603667543748304963),(.D5,137012531068016674),(.D5,13635777630299054),(.D5,2505715458859386),(.D5,61658866734647),(.D5,324115588078669),(.D1,1)],
  .batch [20193266319593472] 5231052965712383 [(.D5,57101728038172417),(.D5,808045676173396591),(.D5,603667543748281635),(.D5,137012531068012786),(.D5,13635777630298406),(.D5,2505715458859278),(.D5,61658866734629),(.D5,324115588078666),(.D5,7588307128716),(.D3,2470613942892),(.D0,1454604919),(.D3,13203084163),(.D1,865987937),(.D0,172471388),(.D3,42875131),(.D0,10116009),(.D0,509501),(.D1,133685),(.D5,809),(.D2,2909),(.D0,76)],
  .scan 0 50,
  .scan2 5 9 [(15327686125509118,4),(52053411458274049,4),(807204290076746863,4),(603527312732173347,4),(136989159231994738,4),(13631882324295398,4),(2505066241192110,4),(61550663790101,4),(324097554254578,4),(7585301491368,4),(2470113003333,4),(1371114992,4),(13189169175,4),(863668771,4),(172084860,4),(42810709,4),(10105271,4),(507711,4),(133386,4),(759,4),(2900,4)],
  .scan 5 74,
  .scan 0 10,
  .scan2 3 0 [(74,20),(2900,20),(759,20),(133386,20),(507711,20),(10105271,20),(42810709,20),(172084860,20),(863668771,20),(13189169175,20),(1371114992,20),(2470113003333,20),(7585301491368,20),(324097554254578,20),(61550663790101,20),(2505066241192110,20),(13631882324295398,20),(136989159231994738,20),(603527312732173347,20),(807204290076746863,20),(52053411458274049,20)],
  .scan 3 15327686125509113,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [45983058376527359,11495764594131840,2873941148532960,718485287133240,179621321783310,44905330445826,11226332611458,2806583152862,701645788216,175411447056,43852861764,10963215440,2740803858,685200966,171300240,42825060,10706266,2676566,669142,167286,41822,10456,2612,654,162,42,10,2,2,2] 1 [(.D2,15327686125509119),(.D0,52053411458274050),(.D0,807204290076746864),(.D0,603527312732173348),(.D0,136989159231994739),(.D0,13631882324295399),(.D0,2505066241192111),(.D0,61550663790102),(.D0,324097554254579),(.D0,7585301491369),(.D0,2470113003334),(.D0,1371114993),(.D0,13189169176),(.D0,863668772),(.D0,172084861),(.D0,42810710),(.D0,10105272),(.D0,507712),(.D0,133387),(.D0,760),(.D0,2901),(.D0,74)],
  .batch [2] 30655372251018240 [(.D1,1)],
  .batch [11718493223371776] 30655372251018241 [(.D5,49498797104022528),(.D5,806778521017704943),(.D5,603456351222333027),(.D5,136977332313688018),(.D5,13629911171244278),(.D5,2504737715683590),(.D5,61495909538681),(.D1,324088428546009),(.D5,7583780539940),(.D0,2469859511429),(.D1,1328866342),(.D3,13182127734),(.D2,862495198),(.D0,171889265),(.D5,42778110),(.D0,10099839),(.D4,506805),(.D3,133236),(.D4,734),(.D4,2896),(.D2,73)],
  .scan 0 50,
  .scan2 5 9 [(36514618862704128,4),(46569173798179584,4),(806290250466731119,4),(603374972797170723,4),(136963769242827634,4),(13627650659434214,4),(2504360963715246,4),(61433117543957,4),(324077963213554,4),(7582036317864,4),(2469568807749,4),(1280415728,4),(13174052631,4),(861149347,4),(171664956,4),(42740725,4),(10093607,4),(505767,4),(133062,4),(705,4),(2891,4)],
  .scan 5 72,
  .scan 0 10,
  .scan2 3 0 [(72,20),(2891,20),(705,20),(133062,20),(505767,20),(10093607,20),(42740725,20),(171664956,20),(861149347,20),(13174052631,20),(1280415728,20),(2469568807749,20),(7582036317864,20),(324077963213554,20),(61433117543957,20),(2504360963715246,20),(13627650659434214,20),(136963769242827634,20),(603374972797170723,20),(806290250466731119,20),(46569173798179584,20)],
  .scan 3 36514618862704123,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [109543856588112389,22077847254154744] 1 [(.D2,36514618862704129),(.D0,46569173798179585),(.D0,806290250466731120),(.D0,603374972797170724),(.D0,136963769242827635),(.D0,13627650659434215),(.D0,2504360963715247),(.D0,61433117543958),(.D0,324077963213555),(.D0,7582036317865),(.D0,2469568807750),(.D0,1280415729),(.D0,13174052632),(.D0,861149348),(.D0,171664957),(.D0,42740726),(.D0,10093608),(.D0,505768),(.D0,133063),(.D0,706),(.D0,2892),(.D0,72)],
  .scan 0 50,
  .scan2 5 9 [(65810851921133566,4),(3609192902137345,4),(41084936138085120,4),(805376210856715375,4),(603222632862168099,4),(136938379253660530,4),(13623418994573030,4),(2503655686238382,4),(61315571297813,4),(324058372172530,4),(7578771144360,4),(2469024612165,4),(1189716464,4),(13158936087,4),(858629923,4),(171245052,4),(42670741,4),(10081943,4),(503823,4),(132738,4),(651,4),(2882,4)],
  .scan 5 70,
  .scan 0 10,
  .scan2 3 0 [(70,20),(2882,20),(651,20),(132738,20),(503823,20),(10081943,20),(42670741,20),(171245052,20),(858629923,20),(13158936087,20),(1189716464,20),(2469024612165,20),(7578771144360,20),(324058372172530,20),(61315571297813,20),(2503655686238382,20),(13623418994573030,20),(136938379253660530,20),(603222632862168099,20),(805376210856715375,20),(41084936138085120,20),(3609192902137345,20)],
  .scan 3 65810851921133561,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [64965472238472237,16241368059618048,4060342014904512,1015085503726128,253771375931532,63442843982892,15860710995708,3965177748924,991294437240,247823609316,61955902332,15488975568,3872243904,968060964,242015244,60503808,15125964,3781488,945360,236340,59100,14772,3696,912,240,48,24] 1 [(.D2,65810851921133567),(.D0,3609192902137346),(.D0,41084936138085121),(.D0,805376210856715376),(.D0,603222632862168100),(.D0,136938379253660531),(.D0,13623418994573031),(.D0,2503655686238383),(.D0,61315571297814),(.D0,324058372172531),(.D0,7578771144361),(.D0,2469024612166),(.D0,1189716465),(.D0,13158936088),(.D0,858629924),(.D0,171245053),(.D0,42670742),(.D0,10081944),(.D0,503824),(.D0,132739),(.D0,652),(.D0,2883)],
  .batch [117184932233717736] 43310314825648151 [(.D5,44155694508309491),(.D3,40483403987728897),(.D0,805275955498322672),(.D0,603205923635769316),(.D0,136935594382594067),(.D0,13622954849395287),(.D0,2503578328708759),(.D2,61302678376209),(.D5,324056223352263),(.D2,7578413007649),(.D5,2468964922713),(.D1,1179768223),(.D1,13157278048),(.D4,858353583),(.D2,171198996),(.D2,42663065),(.D5,10080664),(.D0,503611),(.D4,132702),(.D5,645),(.D3,2882),(.D0,70)],
  .scan 0 50,
  .scan2 5 9 [(101902780942507018,4),(14859461449880057,4),(35600698477990657,4),(804462171246699631,4),(603070292927165475,4),(136912989264493426,4),(13619187329711846,4),(2502950408761518,4),(61198025051669,4),(324038781131506,4),(7575505970856,4),(2468480416581,4),(1099017200,4),(13143819543,4),(856110499,4),(170825148,4),(42600757,4),(10070279,4),(501879,4),(132414,4),(597,4),(2873,4)],
  .scan 5 68,
  .scan 0 10,
  .scan2 3 0 [(68,20),(2873,20),(597,20),(132414,20),(501879,20),(10070279,20),(42600757,20),(170825148,20),(856110499,20),(13143819543,20),(1099017200,20),(2468480416581,20),(7575505970856,20),(324038781131506,20),(61198025051669,20),(2502950408761518,20),(13619187329711846,20),(136912989264493426,20),(603070292927165475,20),(804462171246699631,20),(35600698477990657,20),(14859461449880057,20)],
  .scan 3 101902780942507013,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [267470306097841053,66867576524460252,16716894131115072,4179223532778768,1044805883194692,261201470798664,65300367699660,16325091924912,4081272981228,1020318245316,255079561320,63769890336,15942472596,3985618140,996404544,249101136,62275284,15568812,3892212,973044,243264,60804,15216,3792,960,228,60,12,38238036729680024,9559509182420006,2389877295605002,597469323901250,149367330975312,37341832743828,9335458185958,2333864546490,583466136624,145866534156,36466633538,9116658384,2279164596,569791150,142447788,35611946,8902986,2225746,556436,139110,34776,8694,2176,542,136,36,8,2,2] 1 [(.D2,101902780942507019),(.D0,14859461449880058),(.D0,35600698477990658),(.D0,804462171246699632),(.D0,603070292927165476),(.D0,136912989264493427),(.D0,13619187329711847),(.D0,2502950408761519),(.D0,61198025051670),(.D0,324038781131507),(.D0,7575505970857),(.D0,2468480416582),(.D0,1099017201),(.D0,13143819544),(.D0,856110500),(.D0,170825149),(.D0,42600758),(.D0,10070280),(.D0,501880),(.D0,132415),(.D0,598),(.D0,2874),(.D0,68)],
  .batch [3533301511640032] 203805561885014040 [(.D1,30999786195806203),(.D5,803695352533002222),(.D0,602942489808215908),(.D0,136891688744668499),(.D0,13615637243074359),(.D0,2502358727655271),(.D4,61099411533961),(.D0,324022345545222),(.D5,7572766706475),(.D5,2468023872518),(.D0,1022926524),(.D4,13131137763),(.D3,853996870),(.D4,170472876),(.D1,42542046),(.D3,10060494),(.D1,500249),(.D1,132143),(.D1,553),(.D0,2866),(.D5,66)],
  .scan 0 50,
  .scan2 5 9 [(205572212640834055,4),(30116460817896194,4),(803548131636683887,4),(602917952992162851,4),(136887599275326322,4),(13614955664850662,4),(2502245131284654,4),(61080478805525,4),(324019190090482,4),(7572240797352,4),(2467936220997,4),(1008317936,4),(13128702999,4),(853591075,4),(170405244,4),(42530773,4),(10058615,4),(499935,4),(132090,4),(543,4),(2864,4)],
  .scan 5 66,
  .scan 0 10,
  .scan2 3 0 [(66,20),(2864,20),(543,20),(132090,20),(499935,20),(10058615,20),(42530773,20),(170405244,20),(853591075,20),(13128702999,20),(1008317936,20),(2467936220997,20),(7572240797352,20),(324019190090482,20),(61080478805525,20),(2502245131284654,20),(13614955664850662,20),(136887599275326322,20),(602917952992162851,20),(803548131636683887,20),(30116460817896194,20)],
  .scan 3 205572212640834050,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [131621703842267133] 1 [(.D2,205572212640834056),(.D0,30116460817896195),(.D0,803548131636683888),(.D0,602917952992162852),(.D0,136887599275326323),(.D0,13614955664850663),(.D0,2502245131284655),(.D0,61080478805526),(.D0,324019190090483),(.D0,7572240797353),(.D0,2467936220998),(.D0,1008317937),(.D0,13128703000),(.D0,853591076),(.D0,170405245),(.D0,42530774),(.D0,10058616),(.D0,499936),(.D0,132091),(.D0,544),(.D0,2865),(.D0,66)],
  .scan 0 50,
  .scan2 5 9 [(65810851921133566,4),(172666786680267272,4),(24632223157801730,4),(802634092026668143,4),(602765613057160227,4),(136862209286159218,4),(13610723999989478,4),(2501539853807790,4),(60962932559381,4),(323999599049458,4),(7568975623848,4),(2467392025413,4),(917618672,4),(13113586455,4),(851071651,4),(169985340,4),(42460789,4),(10046951,4),(497991,4),(131766,4),(489,4),(2855,4)],
  .scan 5 64,
  .scan 0 10,
  .scan2 3 0 [(64,20),(2855,20),(489,20),(131766,20),(497991,20),(10046951,20),(42460789,20),(169985340,20),(851071651,20),(13113586455,20),(917618672,20),(2467392025413,20),(7568975623848,20),(323999599049458,20),(60962932559381,20),(2501539853807790,20),(13610723999989478,20),(136862209286159218,20),(602765613057160227,20),(802634092026668143,20),(24632223157801730,20),(172666786680267272,20)],
  .scan 3 65810851921133561,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [197432555763400703,49358138940850176,12339534735212544,3084883683803136,771220920950784,192805230237696,48201307559424,12050326889856,3012581722464,753145430616,188286357654,47071589412,11767897352,2941974340,735493584,183873396,45968348,11492088,2873022,718254,179566,44892,11222,2806,702,174,44,10,2,2,2] 1 [(.D2,65810851921133567),(.D0,172666786680267273),(.D0,24632223157801731),(.D0,802634092026668144),(.D0,602765613057160228),(.D0,136862209286159219),(.D0,13610723999989479),(.D0,2501539853807791),(.D0,60962932559382),(.D0,323999599049459),(.D0,7568975623849),(.D0,2467392025414),(.D0,917618673),(.D0,13113586456),(.D0,851071652),(.D0,169985341),(.D0,42460790),(.D0,10046952),(.D0,497992),(.D0,131767),(.D0,490),(.D0,2856),(.D0,64)],
  .batch [2] 131621703842267136 [(.D1,1)],
  .batch [87747802561511424] 131621703842267137 [(.D5,161698311360078343),(.D5,22804143937770242),(.D5,802329412156662895),(.D5,602714833078826019),(.D5,136853745956436850),(.D5,13609313445035750),(.D5,2501304761315502),(.D5,60923750477333),(.D5,323993068702450),(.D5,7567887232680),(.D5,2467210626885),(.D5,887385584),(.D5,13108547607),(.D5,850231843),(.D5,169845372),(.D5,42437461),(.D5,10043063),(.D5,497343),(.D5,131658),(.D5,471),(.D5,2852),(.D1,64)],
  .scan 0 50,
  .scan2 5 9 [(175495605123022848,4),(139761360719700487,4),(19147985497707266,4),(801720052416652399,4),(602613273122157603,4),(136836819296992114,4),(13606492335128294,4),(2500834576330926,4),(60845386313237,4),(323980008008434,4),(7565710450344,4),(2466847829829,4),(826919408,4),(13098469911,4),(848552227,4),(169565436,4),(42390805,4),(10035287,4),(496047,4),(131442,4),(435,4),(2846,4)],
  .scan 5 62,
  .scan 0 10,
  .scan2 3 0 [(62,20),(2846,20),(435,20),(131442,20),(496047,20),(10035287,20),(42390805,20),(169565436,20),(848552227,20),(13098469911,20),(826919408,20),(2466847829829,20),(7565710450344,20),(323980008008434,20),(60845386313237,20),(2500834576330926,20),(13606492335128294,20),(136836819296992114,20),(602613273122157603,20),(801720052416652399,20),(19147985497707266,20),(139761360719700487,20)],
  .scan 3 175495605123022843,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [526486815369068549,131621703842267136,32905425960566784,8226356490141696,2056589122535424,514147280633856,128536820158464,32134205039616,8033551259904,2008387814976,502096953744,125524238436,31381059608,7845264904,1961316224,490329058,122582264,30645564,7661392,1915350,478836,119708,29928,7482,1870,468,116,30,6,4,14624633760251900] 1 [(.D2,175495605123022849),(.D0,139761360719700488),(.D0,19147985497707267),(.D0,801720052416652400),(.D0,602613273122157604),(.D0,136836819296992115),(.D0,13606492335128295),(.D0,2500834576330927),(.D0,60845386313238),(.D0,323980008008435),(.D0,7565710450345),(.D0,2466847829830),(.D0,826919409),(.D0,13098469912),(.D0,848552228),(.D0,169565437),(.D0,42390806),(.D0,10035288),(.D0,496048),(.D0,131443),(.D0,436),(.D0,2847),(.D0,62)],
  .scan 0 50,
  .scan2 5 9 [(358303527126171648,4),(106855934759133704,4),(13663747837612802,4),(800806012806636655,4),(602460933187154979,4),(136811429307825010,4),(13602260670267110,4),(2500129298854062,4),(60727840067093,4),(323960416967410,4),(7562445276840,4),(2466303634245,4),(736220144,4),(13083353367,4),(846032803,4),(169145532,4),(42320821,4),(10023623,4),(494103,4),(131118,4),(381,4),(2837,4)],
  .scan 5 60,
  .scan 0 10,
  .scan2 3 0 [(60,20),(2837,20),(381,20),(131118,20),(494103,20),(10023623,20),(42320821,20),(169145532,20),(846032803,20),(13083353367,20),(736220144,20),(2466303634245,20),(7562445276840,20),(323960416967410,20),(60727840067093,20),(2500129298854062,20),(13602260670267110,20),(136811429307825010,20),(602460933187154979,20),(800806012806636655,20),(13663747837612802,20),(106855934759133704,20)],
  .scan 3 358303527126171643,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,358303527126171649),(.D0,106855934759133705),(.D0,13663747837612803),(.D0,800806012806636656),(.D0,602460933187154980),(.D0,136811429307825011),(.D0,13602260670267111),(.D0,2500129298854063),(.D0,60727840067094),(.D0,323960416967411),(.D0,7562445276841),(.D0,2466303634246),(.D0,736220145),(.D0,13083353368),(.D0,846032804),(.D0,169145533),(.D0,42320822),(.D0,10023624),(.D0,494104),(.D0,131119),(.D0,382),(.D0,2838),(.D0,60)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(160870971362770945,4),(73950508798566920,4),(8179510177518338,4),(799891973196620911,4),(602308593252152355,4),(136786039318657906,4),(13598029005405926,4),(2499424021377198,4),(60610293820949,4),(323940825926386,4),(7559180103336,4),(2465759438661,4),(645520880,4),(13068236823,4),(843513379,4),(168725628,4),(42250837,4),(10011959,4),(492159,4),(130794,4),(327,4),(2828,4)],
  .scan 5 58,
  .scan 0 10,
  .scan2 3 0 [(58,20),(2828,20),(327,20),(130794,20),(492159,20),(10011959,20),(42250837,20),(168725628,20),(843513379,20),(13068236823,20),(645520880,20),(2465759438661,20),(7559180103336,20),(323940825926386,20),(60610293820949,20),(2499424021377198,20),(13598029005405926,20),(136786039318657906,20),(602308593252152355,20),(799891973196620911,20),(8179510177518338,20),(73950508798566920,20),(160870971362770945,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,160870971362770946),(.D0,73950508798566921),(.D0,8179510177518339),(.D0,799891973196620912),(.D0,602308593252152356),(.D0,136786039318657907),(.D0,13598029005405927),(.D0,2499424021377199),(.D0,60610293820950),(.D0,323940825926387),(.D0,7559180103337),(.D0,2465759438662),(.D0,645520881),(.D0,13068236824),(.D0,843513380),(.D0,168725629),(.D0,42250838),(.D0,10011960),(.D0,492160),(.D0,130795),(.D0,328),(.D0,2829),(.D0,58)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [285180358324912130,71295089581228034,17823772395307008,4455943098826752,1113985774706688,278496443676672,69624110919168,17406027729792,4351506932448,1087876733112,271969183278,67992295818,16998073956,4249518490,1062379622,265594906,66398726,16599682,4149920,1037478,259372,64842,16212,4052,1012,254,64,14,4,2] 789730223053602817 [(.D5,95060119441637376),(.D5,62982033478377992),(.D5,6351430957486850),(.D5,799587293326615663),(.D5,602257813273818147),(.D5,136777575988935538),(.D5,13596618450452198),(.D5,2499188928884910),(.D5,60571111738901),(.D5,323934295579378),(.D5,7558091712168),(.D5,2465578040133),(.D5,615287792),(.D5,13063197975),(.D5,842673571),(.D5,168585660),(.D5,42227509),(.D5,10008071),(.D5,491511),(.D5,130686),(.D5,309),(.D5,2825),(.D1,58)],
  .batch [2] 979850461936877571 [(.D1,1)],
  .batch [24374389600419838] 979850461936877572 [(.D1,47138680238105097),(.D0,3710872084108035),(.D0,799147200181052528),(.D0,602184464416224292),(.D0,136765351179336563),(.D0,13594580982185703),(.D0,2498849350840495),(.D0,60514515398166),(.D0,323924862855923),(.D0,7556519591593),(.D0,2465316020038),(.D0,571617777),(.D0,13055919640),(.D0,841460516),(.D0,168383485),(.D0,42193814),(.D0,10002456),(.D0,490576),(.D0,130531),(.D2,283),(.D5,2821),(.D4,56)],
  .scan 0 50,
  .scan2 5 9 [(992037656737087490,4),(41045082838000136,4),(2695272517423874,4),(798977933586605167,4),(602156253317149731,4),(136760649329490802,4),(13593797340544742,4),(2498718743900334,4),(60492747574805,4),(323921234885362,4),(7555914929832,4),(2465215243077,4),(554821616,4),(13053120279,4),(840993955,4),(168305724,4),(42180853,4),(10000295,4),(490215,4),(130470,4),(273,4),(2819,4)],
  .scan 5 56,
  .scan 0 10,
  .scan2 3 0 [(56,20),(2819,20),(273,20),(130470,20),(490215,20),(10000295,20),(42180853,20),(168305724,20),(840993955,20),(13053120279,20),(554821616,20),(2465215243077,20),(7555914929832,20),(323921234885362,20),(60492747574805,20),(2498718743900334,20),(13593797340544742,20),(136760649329490802,20),(602156253317149731,20),(798977933586605167,20),(2695272517423874,20),(41045082838000136,20)],
  .scan 3 992037656737087485,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [291089431881778533,72772357970444544,18193089492611136,4548272373152784,1137068093288232,284267023322040,71066755830528,17766688957704,4441672239336,1110418059816,277604515008,69401128752,17350282224,4337570520,1084392648,271098144,67774536,16943616,4235976,1058904,264744,66168,16560,4176,1008,288,66935163424093992] 1 [(.D2,992037656737087491),(.D0,41045082838000137),(.D0,2695272517423875),(.D0,798977933586605168),(.D0,602156253317149732),(.D0,136760649329490803),(.D0,13593797340544743),(.D0,2498718743900335),(.D0,60492747574806),(.D0,323921234885363),(.D0,7555914929833),(.D0,2465215243078),(.D0,554821617),(.D0,13053120280),(.D0,840993956),(.D0,168305725),(.D0,42180854),(.D0,10000296),(.D0,490216),(.D0,130471),(.D0,274),(.D0,2820),(.D0,56)]
]
lemma chunk_19_ok : q6 cmds_19 cfg_19=some cfg_20:= by decide +kernel
def cmds_20 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(227527202966565958,4),(878274055253804511,4),(22084482590786306,4),(798063893976589425,4),(602003913382147107,4),(136735259340323698,4),(13589565675683558,4),(2498013466423470,4),(60375201328661,4),(323901643844338,4),(7552649756328,4),(2464671047493,4),(464122352,4),(13038003735,4),(838474531,4),(167885820,4),(42110869,4),(9988631,4),(488271,4),(130146,4),(219,4),(2810,4)],
  .scan 5 54,
  .scan 0 10,
  .scan2 3 0 [(54,20),(2810,20),(219,20),(130146,20),(488271,20),(9988631,20),(42110869,20),(167885820,20),(838474531,20),(13038003735,20),(464122352,20),(2464671047493,20),(7552649756328,20),(323901643844338,20),(60375201328661,20),(2498013466423470,20),(13589565675683558,20),(136735259340323698,20),(602003913382147107,20),(798063893976589425,20),(22084482590786306,20),(878274055253804511,20)],
  .scan 3 227527202966565953,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [682581608899697879,107148614153904934] 1 [(.D2,227527202966565959),(.D0,878274055253804512),(.D0,22084482590786307),(.D0,798063893976589426),(.D0,602003913382147108),(.D0,136735259340323699),(.D0,13589565675683559),(.D0,2498013466423471),(.D0,60375201328662),(.D0,323901643844339),(.D0,7552649756329),(.D0,2464671047494),(.D0,464122353),(.D0,13038003736),(.D0,838474532),(.D0,167885821),(.D0,42110870),(.D0,9988632),(.D0,488272),(.D0,130147),(.D0,220),(.D0,2811),(.D0,54)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(30094647203165255,4),(845368629293237727,4),(16600244930691842,4),(797149854366573681,4),(601851573447144483,4),(136709869351156594,4),(13585334010822374,4),(2497308188946606,4),(60257655082517,4),(323882052803314,4),(7549384582824,4),(2464126851909,4),(373423088,4),(13022887191,4),(835955107,4),(167465916,4),(42040885,4),(9976967,4),(486327,4),(129822,4),(165,4),(2801,4)],
  .scan 5 52,
  .scan 0 10,
  .scan2 3 0 [(52,20),(2801,20),(165,20),(129822,20),(486327,20),(9976967,20),(42040885,20),(167465916,20),(835955107,20),(13022887191,20),(373423088,20),(2464126851909,20),(7549384582824,20),(323882052803314,20),(60257655082517,20),(2497308188946606,20),(13585334010822374,20),(136709869351156594,20),(601851573447144483,20),(797149854366573681,20),(16600244930691842,20),(845368629293237727,20),(30094647203165255,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [541703649656974617,135425912414243652,33856478103560904,8464119525890220,2116029881472552,529007470368144,132251867592048,33062966898012,8265741724488,2066435431128,516608857788,129152214444,32288053608,8072013408,2018003340,504500832,126125208,31531308,7882824,1970712,492684,123168,30780,7704,1932,480,108,36,12,12] 1 [(.D2,394865111526801407),(.D0,30094647203165256),(.D0,845368629293237728),(.D0,16600244930691843),(.D0,797149854366573682),(.D0,601851573447144484),(.D0,136709869351156595),(.D0,13585334010822375),(.D0,2497308188946607),(.D0,60257655082518),(.D0,323882052803315),(.D0,7549384582825),(.D0,2464126851910),(.D0,373423089),(.D0,13022887192),(.D0,835955108),(.D0,167465917),(.D0,42040886),(.D0,9976968),(.D0,486328),(.D0,129823),(.D0,166),(.D0,2802)],
  .batch [12] 361135766437983077 [(.D5,214297228307809868),(.D1,1)],
  .batch [642891684923429596,26459949317512196] 361135766437983083 [(.D5,214297228307809865),(.D5,840352854759376850),(.D1,15764282508381697),(.D1,797010527296188658),(.D0,601828352268746980),(.D0,136705999154757011),(.D0,13584688978089111),(.D0,2497200683491063),(.D0,60239737506594),(.D2,323879066540660),(.D3,7548886872382),(.D1,2464043900170),(.D0,359597799),(.D2,13020582976),(.D5,835571071),(.D3,167401911),(.D4,42030217),(.D1,9975190),(.D3,486031),(.D5,129773),(.D2,157),(.D5,2800),(.D0,52)],
  .scan 0 50,
  .scan2 5 9 [(695811583558453978,4),(46959319747574417,4),(812463203332670942,4),(11116007270597378,4),(796235814756557937,4),(601699233512141859,4),(136684479361989490,4),(13581102345961190,4),(2496602911469742,4),(60140108836373,4),(323862461762290,4),(7546119409320,4),(2463582656325,4),(282723824,4),(13007770647,4),(833435683,4),(167046012,4),(41970901,4),(9965303,4),(484383,4),(129498,4),(111,4),(2792,4)],
  .scan 5 50,
  .scan 0 10,
  .scan2 3 0 [(50,20),(2792,20),(111,20),(129498,20),(484383,20),(9965303,20),(41970901,20),(167046012,20),(833435683,20),(13007770647,20),(282723824,20),(2463582656325,20),(7546119409320,20),(323862461762290,20),(60140108836373,20),(2496602911469742,20),(13581102345961190,20),(136684479361989490,20),(601699233512141859,20),(796235814756557937,20),(11116007270597378,20),(812463203332670942,20),(46959319747574417,20)],
  .scan 3 695811583558453973,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [845267755456339533,211316938864084872,52829234716021212,13207308679005300,3301827169751340,825456792437832,206364198109452,51591049527360,12897762381852,3224440595460,806110148868,201527537220,50381884296,12595471068,3148867764,787216956,196804236,49201056,12300264,3075072,768756,192192,48060,12000,3012,756,180,48,601892944063305120] 1 [(.D2,695811583558453979),(.D0,46959319747574418),(.D0,812463203332670943),(.D0,11116007270597379),(.D0,796235814756557938),(.D0,601699233512141860),(.D0,136684479361989491),(.D0,13581102345961191),(.D0,2496602911469743),(.D0,60140108836374),(.D0,323862461762291),(.D0,7546119409321),(.D0,2463582656326),(.D0,282723825),(.D0,13007770648),(.D0,833435684),(.D0,167046013),(.D0,41970902),(.D0,9965304),(.D0,484384),(.D0,129499),(.D0,112),(.D0,2793),(.D0,50)],
  .scan 0 50,
  .scan2 5 9 [(864458309002545568,4),(263582429057181194,4),(779557777372104160,4),(5631769610502914,4),(795321775146542193,4),(601546893577139235,4),(136659089372822386,4),(13576870681100006,4),(2495897633992878,4),(60022562590229,4),(323842870721266,4),(7542854235816,4),(2463038460741,4),(192024560,4),(12992654103,4),(830916259,4),(166626108,4),(41900917,4),(9953639,4),(482439,4),(129174,4),(57,4),(2783,4)],
  .scan 5 48,
  .scan 0 10,
  .scan2 3 0 [(48,20),(2783,20),(57,20),(129174,20),(482439,20),(9953639,20),(41900917,20),(166626108,20),(830916259,20),(12992654103,20),(192024560,20),(2463038460741,20),(7542854235816,20),(323842870721266,20),(60022562590229,20),(2495897633992878,20),(13576870681100006,20),(136659089372822386,20),(601546893577139235,20),(795321775146542193,20),(5631769610502914,20),(779557777372104160,20),(263582429057181194,20)],
  .scan 3 864458309002545563,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [2593374927007636709,648343731751909176,162085932937977294,40521483234494324,10130370808623580,2532592702155896,633148175538972,158287043884744,39571760971188,9892940242796,2473235060698,618308765174,154577191294,38644297824,9661074456,2415268614,603817154,150954288,37738572,9434644,2358660,589664,147418,36854,9214,2304,576,144,36,8,176001963433042032,37422720285530400] 1 [(.D2,864458309002545569),(.D0,263582429057181195),(.D0,779557777372104161),(.D0,5631769610502915),(.D0,795321775146542194),(.D0,601546893577139236),(.D0,136659089372822387),(.D0,13576870681100007),(.D0,2495897633992879),(.D0,60022562590230),(.D0,323842870721267),(.D0,7542854235817),(.D0,2463038460742),(.D0,192024561),(.D0,12992654104),(.D0,830916260),(.D0,166626109),(.D0,41900918),(.D0,9953640),(.D0,482440),(.D0,129175),(.D0,58),(.D0,2784),(.D0,48)],
  .scan 0 50,
  .scan2 5 9 [(1835628959864377353,4),(66149873293780492,4),(746652351411537376,4),(147531950408450,4),(794407735536526449,4),(601394553642136611,4),(136633699383655282,4),(13572639016238822,4),(2495192356516014,4),(59905016344085,4),(323823279680242,4),(7539589062312,4),(2462494265157,4),(101325296,4),(12977537559,4),(828396835,4),(166206204,4),(41830933,4),(9941975,4),(480495,4),(128850,4),(3,4),(2774,4)],
  .scan 5 46,
  .scan 0 10,
  .scan2 3 0 [(46,20),(2774,20),(3,20),(128850,20),(480495,20),(9941975,20),(41830933,20),(166206204,20),(828396835,20),(12977537559,20),(101325296,20),(2462494265157,20),(7539589062312,20),(323823279680242,20),(59905016344085,20),(2495192356516014,20),(13572639016238822,20),(136633699383655282,20),(601394553642136611,20),(794407735536526449,20),(147531950408450,20),(746652351411537376,20),(66149873293780492,20)],
  .scan 3 1835628959864377348,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [95600703864676461,23900175966168576,5975043991542144,1493760997885536,373440249471600,93360062367792,23340015591840,5835003898176,1458750974976,364687743744,91171935936,22792983984,5698245456,1424561472,356140800,89035200,22258800,5564160,1391472,347760,86832,21600,5616,1296] 1 [(.D2,1835628959864377354),(.D0,66149873293780493),(.D0,746652351411537377),(.D0,147531950408451),(.D0,794407735536526450),(.D0,601394553642136612),(.D0,136633699383655283),(.D0,13572639016238823),(.D0,2495192356516015),(.D0,59905016344086),(.D0,323823279680243),(.D0,7539589062313),(.D0,2462494265158),(.D0,101325297),(.D0,12977537560),(.D0,828396836),(.D0,166206205),(.D0,41830934),(.D0,9941976),(.D0,480496),(.D0,128851),(.D0,4)],
  .batch [29941617302063856,7312316880125952] 63733802576450615 [(.D5,1803762058576152046),(.D5,60838723079076274),(.D5,745767159709086673),(.D5,794383146878125042),(.D0,601390455532403044),(.D0,136633016365366355),(.D0,13572525179857335),(.D0,2495173383785767),(.D4,59901854222377),(.D2,323822752659958),(.D2,7539501225598),(.D5,2462479625705),(.D4,98885387),(.D5,12977130908),(.D2,828329060),(.D3,166194909),(.D0,41829051),(.D1,9941662),(.D5,480443),(.D4,128841),(.D5,2),(.D0,2775)],
  .batch [124309386962141184] 82360769667545519 [(.D5,1794448575030604594),(.D5,59286475821485032),(.D5,745508451832821466),(.D5,794340028898747507),(.D5,601383269202506787),(.D5,136631818643716978),(.D5,13572325559582438),(.D5,2495140113739950),(.D5,59896309214741),(.D5,323821828492018),(.D5,7539347197608),(.D5,2462453954373),(.D5,94606832),(.D5,12976417815),(.D5,828210211),(.D5,166175100),(.D5,41825749),(.D5,9941111),(.D5,480351),(.D5,128826),(.D1,2775),(.D0,46)],
  .scan 0 50,
  .scan2 5 9 [(144515463148616110,4),(1763371228290069298,4),(54106918031395816,4),(744645192201139930,4),(794196152293467251,4),(601359289768293411,4),(136627822071348082,4),(13571659464187622,4),(2495029097840814,4),(59877806564885,4),(323818744717042,4),(7538833235112,4),(2462368293957,4),(80330096,4),(12974038359,4),(827813635,4),(166109004,4),(41814733,4),(9939275,4),(480045,4),(128775,4),(2765,4)],
  .scan 5 44,
  .scan 0 10,
  .scan2 3 0 [(44,20),(2765,20),(128775,20),(480045,20),(9939275,20),(41814733,20),(166109004,20),(827813635,20),(12974038359,20),(80330096,20),(2462368293957,20),(7538833235112,20),(323818744717042,20),(59877806564885,20),(2495029097840814,20),(13571659464187622,20),(136627822071348082,20),(601359289768293411,20),(794196152293467251,20),(744645192201139930,20),(54106918031395816,20),(1763371228290069298,20)],
  .scan 3 144515463148616105,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [433546389445848335,108386597361462084,27096649340365520,6774162335091378,1693540583772846,423385145943210,105846286485804,26461571621452,6615392905362,1653848226342,413462056584,103365514146,25841378538,6460344632,1615086160,403771538,100942884,25235722,6308930,1577232,394308,98578,24644,6162,1540,386,96,24,6,2,2] 1 [(.D2,144515463148616111),(.D0,1763371228290069299),(.D0,54106918031395817),(.D0,744645192201139931),(.D0,794196152293467252),(.D0,601359289768293412),(.D0,136627822071348083),(.D0,13571659464187623),(.D0,2495029097840815),(.D0,59877806564886),(.D0,323818744717043),(.D0,7538833235113),(.D0,2462368293958),(.D0,80330097),(.D0,12974038360),(.D0,827813636),(.D0,166109005),(.D0,41814734),(.D0,9939276),(.D0,480046),(.D0,128776),(.D0,2766),(.D0,44)],
  .batch [2] 289030926297232224 [(.D1,1)],
  .batch [35278061743189728] 289030926297232225 [(.D5,1739285317765299945),(.D5,50092599610600924),(.D1,743976139131007449),(.D1,794084643448445172),(.D0,601340704960789732),(.D0,136624724603430803),(.D0,13571143219534743),(.D4,2494943057065334),(.D2,59863466435639),(.D0,323816354695502),(.D0,7538434898189),(.D1,2462301904471),(.D4,69265181),(.D5,12972194207),(.D4,827506276),(.D5,166057778),(.D4,41806195),(.D3,9937853),(.D0,479809),(.D2,128736),(.D2,2759),(.D4,42)],
  .scan 0 50,
  .scan2 5 9 [(306669957168827088,4),(1730465802329502513,4),(48622680371301352,4),(743731152591124186,4),(794043812358464627,4),(601333899779126307,4),(136623590406486898,4),(13570954186710758,4),(2494911551594670,4),(59858215523861,4),(323815479543538,4),(7538289039528,4),(2462277594693,4),(65213552,4),(12971518935,4),(827393731,4),(166039020,4),(41803069,4),(9937331,4),(479721,4),(128721,4),(2756,4)],
  .scan 5 42,
  .scan 0 10,
  .scan2 3 0 [(42,20),(2756,20),(128721,20),(479721,20),(9937331,20),(41803069,20),(166039020,20),(827393731,20),(12971518935,20),(65213552,20),(2462277594693,20),(7538289039528,20),(323815479543538,20),(59858215523861,20),(2494911551594670,20),(13570954186710758,20),(136623590406486898,20),(601333899779126307,20),(794043812358464627,20),(743731152591124186,20),(48622680371301352,20),(1730465802329502513,20)],
  .scan 3 306669957168827083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,306669957168827089),(.D0,1730465802329502514),(.D0,48622680371301353),(.D0,743731152591124187),(.D0,794043812358464628),(.D0,601333899779126308),(.D0,136623590406486899),(.D0,13570954186710759),(.D0,2494911551594671),(.D0,59858215523862),(.D0,323815479543539),(.D0,7538289039529),(.D0,2462277594694),(.D0,65213553),(.D0,12971518936),(.D0,827393732),(.D0,166039021),(.D0,41803070),(.D0,9937332),(.D0,479722),(.D0,128722),(.D0,2757),(.D0,42)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(109237401405426385,4),(1697560376368935729,4),(43138442711206888,4),(742817112981108442,4),(793891472423462003,4),(601308509789959203,4),(136619358741625714,4),(13570248909233894,4),(2494794005348526,4),(59838624482837,4),(323812214370034,4),(7537744843944,4),(2462186895429,4),(50097008,4),(12968999511,4),(826973827,4),(165969036,4),(41791405,4),(9935387,4),(479397,4),(128667,4),(2747,4)],
  .scan 5 40,
  .scan 0 10,
  .scan2 3 0 [(40,20),(2747,20),(128667,20),(479397,20),(9935387,20),(41791405,20),(165969036,20),(826973827,20),(12968999511,20),(50097008,20),(2462186895429,20),(7537744843944,20),(323812214370034,20),(59838624482837,20),(2494794005348526,20),(13570248909233894,20),(136619358741625714,20),(601308509789959203,20),(793891472423462003,20),(742817112981108442,20),(43138442711206888,20),(1697560376368935729,20),(109237401405426385,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,109237401405426386),(.D0,1697560376368935730),(.D0,43138442711206889),(.D0,742817112981108443),(.D0,793891472423462004),(.D0,601308509789959204),(.D0,136619358741625715),(.D0,13570248909233895),(.D0,2494794005348527),(.D0,59838624482838),(.D0,323812214370035),(.D0,7537744843945),(.D0,2462186895430),(.D0,50097009),(.D0,12968999512),(.D0,826973828),(.D0,165969037),(.D0,41791406),(.D0,9935388),(.D0,479398),(.D0,128668),(.D0,2748),(.D0,40)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [130279648452878450,32569912113219614,8142478028304904,2035619507076224,508904876769058,127226219192264,31806554798064,7951638699516,1987909674880,496977418722,124244354678,31061088670,7765272168,1941318042,485329512,121332378,30333092,7583274,1895818,473954,118488,29622,7408,1850,462,118,30,6,2] 789730223053602817 [(.D5,43426549484292816),(.D5,1686591901048746801),(.D5,41310363491175400),(.D5,742512433111103194),(.D5,793840692445127795),(.D5,601300046460236835),(.D5,136617948186671986),(.D5,13570013816741606),(.D5,2494754823266478),(.D5,59832094135829),(.D5,323811125978866),(.D5,7537563445416),(.D5,2462156662341),(.D5,45058160),(.D5,12968159703),(.D5,826833859),(.D5,165945708),(.D5,41787517),(.D5,9934739),(.D5,479289),(.D5,128649),(.D5,2744),(.D1,40)],
  .batch [2] 876583322022188451 [(.D1,1)],
  .batch [58796769571982878] 876583322022188452 [(.D1,1679354142801364666),(.D2,40104070449945044),(.D1,742311384270898136),(.D2,793807184305093619),(.D0,601294461770231140),(.D0,136617017405004371),(.D4,13569858686463670),(.D2,2494728968220156),(.D4,59827784961442),(.D0,323810407783136),(.D4,7537443746127),(.D5,2462136712460),(.D2,41733180),(.D1,12967605541),(.D4,826741498),(.D1,165930316),(.D2,41784952),(.D0,9934312),(.D3,479218),(.D5,128637),(.D1,2743),(.D3,39)],
  .scan 0 50,
  .scan2 5 9 [(905981706808179890,4),(1664654950408368945,4),(37654205051112424,4),(741903073371092698,4),(793739132488459379,4),(601283119800792099,4),(136615127076764530,4),(13569543631757030,4),(2494676459102382,4),(59819033441813,4),(323808949196530,4),(7537200648360,4),(2462096196165,4),(34980464,4),(12966480087,4),(826553923,4),(165899052,4),(41779741,4),(9933443,4),(479073,4),(128613,4),(2738,4)],
  .scan 5 38,
  .scan 0 10,
  .scan2 3 0 [(38,20),(2738,20),(128613,20),(479073,20),(9933443,20),(41779741,20),(165899052,20),(826553923,20),(12966480087,20),(34980464,20),(2462096196165,20),(7537200648360,20),(323808949196530,20),(59819033441813,20),(2494676459102382,20),(13569543631757030,20),(136615127076764530,20),(601283119800792099,20),(793739132488459379,20),(741903073371092698,20),(37654205051112424,20),(1664654950408368945,20)],
  .scan 3 905981706808179885,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,905981706808179891),(.D0,1664654950408368946),(.D0,37654205051112425),(.D0,741903073371092699),(.D0,793739132488459380),(.D0,601283119800792100),(.D0,136615127076764531),(.D0,13569543631757031),(.D0,2494676459102383),(.D0,59819033441814),(.D0,323808949196531),(.D0,7537200648361),(.D0,2462096196166),(.D0,34980465),(.D0,12966480088),(.D0,826553924),(.D0,165899053),(.D0,41779742),(.D0,9933444),(.D0,479074),(.D0,128614),(.D0,2739),(.D0,38)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(708549151044779187,4),(1631749524447802161,4),(32169967391017960,4),(740989033761076954,4),(793586792553456755,4),(601257729811624995,4),(136610895411903346,4),(13568838354280166,4),(2494558912856238,4),(59799442400789,4),(323805684023026,4),(7536656452776,4),(2462005496901,4),(19863920,4),(12963960663,4),(826134019,4),(165829068,4),(41768077,4),(9931499,4),(478749,4),(128559,4),(2729,4)],
  .scan 5 36,
  .scan 0 10,
  .scan2 3 0 [(36,20),(2729,20),(128559,20),(478749,20),(9931499,20),(41768077,20),(165829068,20),(826134019,20),(12963960663,20),(19863920,20),(2462005496901,20),(7536656452776,20),(323805684023026,20),(59799442400789,20),(2494558912856238,20),(13568838354280166,20),(136610895411903346,20),(601257729811624995,20),(793586792553456755,20),(740989033761076954,20),(32169967391017960,20),(1631749524447802161,20),(708549151044779187,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,708549151044779188),(.D0,1631749524447802162),(.D0,32169967391017961),(.D0,740989033761076955),(.D0,793586792553456756),(.D0,601257729811624996),(.D0,136610895411903347),(.D0,13568838354280167),(.D0,2494558912856239),(.D0,59799442400790),(.D0,323805684023027),(.D0,7536656452777),(.D0,2462005496902),(.D0,19863921),(.D0,12963960664),(.D0,826134020),(.D0,165829069),(.D0,41768078),(.D0,9931500),(.D0,478750),(.D0,128560),(.D0,2730),(.D0,36)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [526486815369068544] 789730223053602817 [(.D5,642738299123645618),(.D5,1620781049127613233),(.D5,30341888170986472),(.D5,740684353891071706),(.D5,793536012575122547),(.D5,601249266481902627),(.D5,136609484856949618),(.D5,13568603261787878),(.D5,2494519730774190),(.D5,59792912053781),(.D5,323804595631858),(.D5,7536475054248),(.D5,2461975263813),(.D5,14825072),(.D5,12963120855),(.D5,825994051),(.D5,165805740),(.D5,41764189),(.D5,9930851),(.D5,478641),(.D5,128541),(.D5,2726),(.D1,36)],
  .scan 0 50,
  .scan2 5 9 [(1052973630738137088,4),(511116595281378482,4),(1598844098487235377,4),(26685729730923496,4),(740074994151061210,4),(793434452618454131,4),(601232339822457891,4),(136606663747042162,4),(13568133076803302,4),(2494441366610094,4),(59779851359765,4),(323802418849522,4),(7536112257192,4),(2461914797637,4),(4747376,4),(12961441239,4),(825714115,4),(165759084,4),(41756413,4),(9929555,4),(478425,4),(128505,4),(2720,4)],
  .scan 5 34,
  .scan 0 10,
  .scan2 3 0 [(34,20),(2720,20),(128505,20),(478425,20),(9929555,20),(41756413,20),(165759084,20),(825714115,20),(12961441239,20),(4747376,20),(2461914797637,20),(7536112257192,20),(323802418849522,20),(59779851359765,20),(2494441366610094,20),(13568133076803302,20),(136606663747042162,20),(601232339822457891,20),(793434452618454131,20),(740074994151061210,20),(26685729730923496,20),(1598844098487235377,20),(511116595281378482,20)],
  .scan 3 1052973630738137083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1116072769124892669,279018113917059072,69754606843428864,17438690892939264,4359555176988672,1089888794247168,272393834397696,68176822763520,16926659444736,4231664861184,1253826625536,156728328192,541713756094562304] 1 [(.D2,1052973630738137089),(.D0,511116595281378483),(.D0,1598844098487235378),(.D0,26685729730923497),(.D0,740074994151061211),(.D0,793434452618454132),(.D0,601232339822457892),(.D0,136606663747042163),(.D0,13568133076803303),(.D0,2494441366610095),(.D0,59779851359766),(.D0,323802418849523),(.D0,7536112257193),(.D0,2461914797638),(.D0,4747377),(.D0,12961441240),(.D0,825714116),(.D0,165759085),(.D0,41756414),(.D0,9929556),(.D0,478426),(.D0,128506),(.D0,2721),(.D0,34)],
  .scan 0 50,
  .scan2 5 9 [(1014905260190269438,4),(545521000643002369,4),(426541156932189362,4),(1584748192095703857,4),(24336411999001576,4),(739683441195740890,4),(793369193792567411,4),(601221463351476771,4),(136604851001878642,4),(13567830952609382,4),(2494391012577774,4),(59771459021045,4),(323801020126402,4),(7535879136672,4),(2461875944217,4),(12958921817,4),(825294211,4),(165689100,4),(41744749,4),(9927611,4),(478101,4),(128451,4),(2711,4)],
  .scan 5 32,
  .scan 0 10,
  .scan2 3 0 [(32,20),(2711,20),(128451,20),(478101,20),(9927611,20),(41744749,20),(165689100,20),(825294211,20),(12958921817,20),(2461875944217,20),(7535879136672,20),(323801020126402,20),(59771459021045,20),(2494391012577774,20),(13567830952609382,20),(136604851001878642,20),(601221463351476771,20),(793369193792567411,20),(739683441195740890,20),(24336411999001576,20),(1584748192095703857,20),(426541156932189362,20),(545521000643002369,20)],
  .scan 3 1014905260190269433,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3044715780570808319,761178945142702080,190294736285675520,47573684071418880,11893421017854720,2973355254463680,743338813615920,185834703403980,46458675850994,11614668962748,2903667240688,725916810170,181479202542,45369800638,11342450160,2835612540,708903134,177225784,44306444,11076612,2769154,692288,173070,43270,10818,2702,676,170,42,10,2,2,2] 1 [(.D2,1014905260190269439),(.D0,545521000643002370),(.D0,426541156932189363),(.D0,1584748192095703858),(.D0,24336411999001577),(.D0,739683441195740891),(.D0,793369193792567412),(.D0,601221463351476772),(.D0,136604851001878643),(.D0,13567830952609383),(.D0,2494391012577775),(.D0,59771459021046),(.D0,323801020126403),(.D0,7535879136673),(.D0,2461875944218),(.D0,12958921818),(.D0,825294212),(.D0,165689101),(.D0,41744750),(.D0,9927612),(.D0,478102),(.D0,128452),(.D0,2712),(.D0,32)],
  .batch [2] 2029810520380538880 [(.D1,1)],
  .batch [113126716260089856] 2029810520380538881 [(.D5,376370123944624128),(.D5,398349344149126322),(.D5,1580049556631860017),(.D5,23553306088360936),(.D5,739552923543967450),(.D5,793347440850605171),(.D5,601217837861149731),(.D5,136604246753490802),(.D5,13567730244544742),(.D5,2494374227900334),(.D5,59768661574805),(.D5,323800553885362),(.D5,7535801429832),(.D1,2461862993078),(.D3,12956763294),(.D5,824934457),(.D3,165629142),(.D0,41734757),(.D2,9925946),(.D0,477824),(.D5,128405),(.D0,2704),(.D5,30)],
  .scan 0 50,
  .scan2 5 9 [(2086373878510583808,4),(348088444879601664,4),(393635730971622578,4),(1579263954435609393,4),(23422372388985832,4),(739531101260738266,4),(793343803803400307,4),(601217231686615587,4),(136604145724401778,4),(13567713406363238,4),(2494371421536750,4),(59768193847541,4),(323800475930818,4),(7535788437408,4),(2461860827673,4),(12956402393,4),(824874307,4),(165619116,4),(41733085,4),(9925667,4),(477777,4),(128397,4),(2702,4)],
  .scan 5 30,
  .scan 0 10,
  .scan2 3 0 [(30,20),(2702,20),(128397,20),(477777,20),(9925667,20),(41733085,20),(165619116,20),(824874307,20),(12956402393,20),(2461860827673,20),(7535788437408,20),(323800475930818,20),(59768193847541,20),(2494371421536750,20),(13567713406363238,20),(136604145724401778,20),(601217231686615587,20),(793343803803400307,20),(739531101260738266,20),(23422372388985832,20),(1579263954435609393,20),(393635730971622578,20),(348088444879601664,20)],
  .scan 3 2086373878510583803,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4738381338321616893] 1 [(.D2,2086373878510583809),(.D0,348088444879601665),(.D0,393635730971622579),(.D0,1579263954435609394),(.D0,23422372388985833),(.D0,739531101260738267),(.D0,793343803803400308),(.D0,601217231686615588),(.D0,136604145724401779),(.D0,13567713406363239),(.D0,2494371421536751),(.D0,59768193847542),(.D0,323800475930819),(.D0,7535788437409),(.D0,2461860827674),(.D0,12956402394),(.D0,824874308),(.D0,165619117),(.D0,41733086),(.D0,9925668),(.D0,477778),(.D0,128398),(.D0,2703),(.D0,30)],
  .scan 0 50,
  .scan2 5 9 [(2369190669160808446,4),(901778543930179585,4),(150655889116200960,4),(360730305011055794,4),(1573779716775514929,4),(22508332778970088,4),(739378761325735642,4),(793318413814233203,4),(601213000021754403,4),(136603440446924914,4),(13567595860117094,4),(2494351830495726,4),(59764928674037,4),(323799931735234,4),(7535697738144,4),(2461845711129,4),(12953882969,4),(824454403,4),(165549132,4),(41721421,4),(9923723,4),(477453,4),(128343,4),(2693,4)],
  .scan 5 28,
  .scan 0 10,
  .scan2 3 0 [(28,20),(2693,20),(128343,20),(477453,20),(9923723,20),(41721421,20),(165549132,20),(824454403,20),(12953882969,20),(2461845711129,20),(7535697738144,20),(323799931735234,20),(59764928674037,20),(2494351830495726,20),(13567595860117094,20),(136603440446924914,20),(601213000021754403,20),(793318413814233203,20),(739378761325735642,20),(22508332778970088,20),(1573779716775514929,20),(360730305011055794,20),(150655889116200960,20),(901778543930179585,20)],
  .scan 3 2369190669160808441,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7107572007482425343,1776893001870606336,444223250467651584,111055812616912896,27763953154228224,6940988288557056,1735247072139264,433811768034816,108452942008704,27113235502176,6778308875544,1694577218886,423644304720,105911076180,26477769044,6619442262,1654860564,413715142,103428786,25857198,6464298,1616076,404018,101004,25252,6312,1578,396,98,24,6,2,2] 1 [(.D2,2369190669160808447),(.D0,901778543930179586),(.D0,150655889116200961),(.D0,360730305011055795),(.D0,1573779716775514930),(.D0,22508332778970089),(.D0,739378761325735643),(.D0,793318413814233204),(.D0,601213000021754404),(.D0,136603440446924915),(.D0,13567595860117095),(.D0,2494351830495727),(.D0,59764928674038),(.D0,323799931735235),(.D0,7535697738145),(.D0,2461845711130),(.D0,12953882970),(.D0,824454404),(.D0,165549133),(.D0,41721422),(.D0,9923724),(.D0,477454),(.D0,128344),(.D0,2694),(.D0,28)],
  .batch [2] 4738381338321616896 [(.D1,1)],
  .batch [1520740297210134530,380185074302533634,95046268575633408,23761567143908352,5940391785977088,1485097946494272,371274486623568,92818621655892,23204655413974,5801163853494,1450290963372,362572740842,90643185210,22660796304,5665199076,1416299770,354074942,88518736,22129682,5532420,1383106,345776,86446,21612,5402,1350,336,84,22,6,2] 4738381338321616897 [(.D5,506913432403378176),(.D5,84845037195067392),(.D5,349761829690866866),(.D5,1571951637555483441),(.D5,22203652908964840),(.D5,739327981347401434),(.D5,793309950484510835),(.D5,601211589466800675),(.D5,136603205354432626),(.D5,13567556678035046),(.D5,2494345300148718),(.D5,59763840282869),(.D5,323799750336706),(.D5,7535667505056),(.D5,2461840672281),(.D5,12953043161),(.D5,824314435),(.D5,165525804),(.D5,41717533),(.D5,9923075),(.D5,477345),(.D5,128325),(.D5,2690),(.D1,28)],
  .batch [2] 5752208203128373251 [(.D1,1)],
  .batch [1078395383513090,269598845878272,67399711469568,16849927867392,4212481966848,1053120491712,263280122928,65820030732,16455007684,4113751920,1028437980,257109494,64277374,16069344,4017336,1004334,251084,62770,15692,3924,982,246,60,14,4,2] 5752208203128373252 [(.D1,359465127837697),(.D0,335680901012995251),(.D0,1569604816109171506),(.D0,21812516001246185),(.D0,739262791862781659),(.D0,793299085570407540),(.D0,601209778647783460),(.D0,136602903551263091),(.D0,13567506377506791),(.D0,2494336916727343),(.D0,59762443045974),(.D0,323799517463891),(.D2,7535628692920),(.D3,2461834203592),(.D1,12951965047),(.D3,824134750),(.D0,165495857),(.D3,41712542),(.D3,9922244),(.D2,477207)],
  .batch [2] 5752927133384048645 [(.D1,1)],
  .batch [31184444431466494] 5752927133384048646 [(.D1,335620990158355635),(.D0,1569594830966731570),(.D0,21810851810839529),(.D0,739262514497713883),(.D0,793299039342896244),(.D0,601209770943198244),(.D0,136602902267165555),(.D0,13567506163490535),(.D0,2494336881057967),(.D0,59762437101078),(.D0,323799516473075),(.D0,7535628527785),(.D0,2461834176070),(.D2,12951960459),(.D1,824133986),(.D0,165495730),(.D4,41712520),(.D5,9922240),(.D4,477206),(.D2,128302),(.D3,2687),(.D4,26)]
]
lemma chunk_20_ok : q6 cmds_20 cfg_20=some cfg_21:= by decide +kernel
def cmds_21 : List Cmd:=[
  .scan 0 50,
  .scan2 5 9 [(5768519355599781892,4),(327824879050489010,4),(1568295479115420465,4),(21594293168954344,4),(739226421390733018,4),(793293023825066099,4),(601208768356893219,4),(136602735169448050,4),(13567478313870950,4),(2494332239454702,4),(59761663500533,4),(323799387539650,4),(7535607038880,4),(2461830594585,4),(12951363545,4),(824034499,4),(165479148,4),(41709757,4),(9921779,4),(477129,4),(128289,4),(2684,4)],
  .scan 5 26,
  .scan 0 10,
  .scan2 3 0 [(26,20),(2684,20),(128289,20),(477129,20),(9921779,20),(41709757,20),(165479148,20),(824034499,20),(12951363545,20),(2461830594585,20),(7535607038880,20),(323799387539650,20),(59761663500533,20),(2494332239454702,20),(13567478313870950,20),(136602735169448050,20),(601208768356893219,20),(793293023825066099,20),(739226421390733018,20),(21594293168954344,20),(1568295479115420465,20),(327824879050489010,20)],
  .scan 3 5768519355599781887,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [789730223053602813] 1 [(.D2,5768519355599781893),(.D0,327824879050489011),(.D0,1568295479115420466),(.D0,21594293168954345),(.D0,739226421390733019),(.D0,793293023825066100),(.D0,601208768356893220),(.D0,136602735169448051),(.D0,13567478313870951),(.D0,2494332239454703),(.D0,59761663500534),(.D0,323799387539651),(.D0,7535607038881),(.D0,2461830594586),(.D0,12951363546),(.D0,824034500),(.D0,165479149),(.D0,41709758),(.D0,9921780),(.D0,477130),(.D0,128290),(.D0,2685),(.D0,26)],
  .scan 0 50,
  .scan2 5 9 [(394865111526801406,4),(5571086799836381189,4),(294919453089922226,4),(1562811241455326001,4),(20680253558938600,4),(739074081455730394,4),(793267633835898995,4),(601204536692032035,4),(136602029891971186,4),(13567360767624806,4),(2494312648413678,4),(59758398327029,4),(323798843344066,4),(7535516339616,4),(2461815478041,4),(12948844121,4),(823614595,4),(165409164,4),(41698093,4),(9919835,4),(476805,4),(128235,4),(2675,4)],
  .scan 5 24,
  .scan 0 10,
  .scan2 3 0 [(24,20),(2675,20),(128235,20),(476805,20),(9919835,20),(41698093,20),(165409164,20),(823614595,20),(12948844121,20),(2461815478041,20),(7535516339616,20),(323798843344066,20),(59758398327029,20),(2494312648413678,20),(13567360767624806,20),(136602029891971186,20),(601204536692032035,20),(793267633835898995,20),(739074081455730394,20),(20680253558938600,20),(1562811241455326001,20),(294919453089922226,20),(5571086799836381189,20)],
  .scan 3 394865111526801401,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1184595334580404223,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384118,17651846032,4412961506,1103240376,275810094,68952526,17238132,4309532,1077382,269346,67338,16832,4210,1052,262,66,18,2,2,2] 1 [(.D2,394865111526801407),(.D0,5571086799836381190),(.D0,294919453089922227),(.D0,1562811241455326002),(.D0,20680253558938601),(.D0,739074081455730395),(.D0,793267633835898996),(.D0,601204536692032036),(.D0,136602029891971187),(.D0,13567360767624807),(.D0,2494312648413679),(.D0,59758398327030),(.D0,323798843344067),(.D0,7535516339617),(.D0,2461815478042),(.D0,12948844122),(.D0,823614596),(.D0,165409165),(.D0,41698094),(.D0,9919836),(.D0,476806),(.D0,128236),(.D0,2676),(.D0,24)],
  .batch [2] 789730223053602816 [(.D1,1)],
  .batch [526486815369068544] 789730223053602817 [(.D5,5505275947915247620),(.D5,283950977769733298),(.D5,1560983162235294513),(.D5,20375573688933352),(.D5,739023301477396186),(.D5,793259170506176627),(.D5,601203126137078307),(.D5,136601794799478898),(.D5,13567321585542758),(.D5,2494306118066670),(.D5,59757309935861),(.D5,323798661945538),(.D5,7535486106528),(.D5,2461810439193),(.D5,12948004313),(.D5,823474627),(.D5,165385836),(.D5,41694205),(.D5,9919187),(.D5,476697),(.D5,128217),(.D5,2672),(.D1,24)],
  .scan 0 50,
  .scan2 5 9 [(1052973630738137088,4),(5373654244072980484,4),(262014027129355442,4),(1557327003795231537,4),(19766213948922856,4),(738921741520727770,4),(793242243846731891,4),(601200305027170851,4),(136601324614494322,4),(13567243221378662,4),(2494293057372654,4),(59755133153525,4),(323798299148482,4),(7535425640352,4),(2461800361497,4),(12946324697,4),(823194691,4),(165339180,4),(41686429,4),(9917891,4),(476481,4),(128181,4),(2666,4)],
  .scan 5 22,
  .scan 0 10,
  .scan2 3 0 [(22,20),(2666,20),(128181,20),(476481,20),(9917891,20),(41686429,20),(165339180,20),(823194691,20),(12946324697,20),(2461800361497,20),(7535425640352,20),(323798299148482,20),(59755133153525,20),(2494293057372654,20),(13567243221378662,20),(136601324614494322,20),(601200305027170851,20),(793242243846731891,20),(738921741520727770,20),(19766213948922856,20),(1557327003795231537,20),(262014027129355442,20),(5373654244072980484,20)],
  .scan 3 1052973630738137083,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3158920892214411269,789730223053602816,197432555763400704,49358138940850176,12339534735212544,3084883683803136,771220920950784,192805230237696,48201307559424,12050326889856,3012581722464,753145430616,188286357654,47071589414,11767897354,2941974338,735493584,183873396,45968350,11492088,2873022,718254,179564,44890,11222,2806,702,176,42,12,4,87747802561511420] 1 [(.D2,1052973630738137089),(.D0,5373654244072980485),(.D0,262014027129355443),(.D0,1557327003795231538),(.D0,19766213948922857),(.D0,738921741520727771),(.D0,793242243846731892),(.D0,601200305027170852),(.D0,136601324614494323),(.D0,13567243221378663),(.D0,2494293057372655),(.D0,59755133153526),(.D0,323798299148483),(.D0,7535425640353),(.D0,2461800361498),(.D0,12946324698),(.D0,823194692),(.D0,165339181),(.D0,41686430),(.D0,9917892),(.D0,476482),(.D0,128182),(.D0,2667),(.D0,22)],
  .scan 0 50,
  .scan2 5 9 [(2149821162757029888,4),(5176221688309579781,4),(229108601168788658,4),(1551842766135137073,4),(18852174338907112,4),(738769401585725146,4),(793216853857564787,4),(601196073362309667,4),(136600619337017458,4),(13567125675132518,4),(2494273466331630,4),(59751867980021,4),(323797754952898,4),(7535334941088,4),(2461785244953,4),(12943805273,4),(822774787,4),(165269196,4),(41674765,4),(9915947,4),(476157,4),(128127,4),(2657,4)],
  .scan 5 20,
  .scan 0 10,
  .scan2 3 0 [(20,20),(2657,20),(128127,20),(476157,20),(9915947,20),(41674765,20),(165269196,20),(822774787,20),(12943805273,20),(2461785244953,20),(7535334941088,20),(323797754952898,20),(59751867980021,20),(2494273466331630,20),(13567125675132518,20),(136600619337017458,20),(601196073362309667,20),(793216853857564787,20),(738769401585725146,20),(18852174338907112,20),(1551842766135137073,20),(229108601168788658,20),(5176221688309579781,20)],
  .scan 3 2149821162757029883,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4738381338321616893] 1 [(.D2,2149821162757029889),(.D0,5176221688309579782),(.D0,229108601168788659),(.D0,1551842766135137074),(.D0,18852174338907113),(.D0,738769401585725147),(.D0,793216853857564788),(.D0,601196073362309668),(.D0,136600619337017459),(.D0,13567125675132519),(.D0,2494273466331631),(.D0,59751867980022),(.D0,323797754952899),(.D0,7535334941089),(.D0,2461785244954),(.D0,12943805274),(.D0,822774788),(.D0,165269197),(.D0,41674766),(.D0,9915948),(.D0,476158),(.D0,128128),(.D0,2658),(.D0,20)],
  .scan 0 50,
  .scan2 5 9 [(2369190669160808446,4),(965225828176625665,4),(4978789132546179077,4),(196203175208221874,4),(1546358528475042609,4),(17938134728891368,4),(738617061650722522,4),(793191463868397683,4),(601191841697448483,4),(136599914059540594,4),(13567008128886374,4),(2494253875290606,4),(59748602806517,4),(323797210757314,4),(7535244241824,4),(2461770128409,4),(12941285849,4),(822354883,4),(165199212,4),(41663101,4),(9914003,4),(475833,4),(128073,4),(2648,4)],
  .scan 5 18,
  .scan 0 10,
  .scan2 3 0 [(18,20),(2648,20),(128073,20),(475833,20),(9914003,20),(41663101,20),(165199212,20),(822354883,20),(12941285849,20),(2461770128409,20),(7535244241824,20),(323797210757314,20),(59748602806517,20),(2494253875290606,20),(13567008128886374,20),(136599914059540594,20),(601191841697448483,20),(793191463868397683,20),(738617061650722522,20),(17938134728891368,20),(1546358528475042609,20),(196203175208221874,20),(4978789132546179077,20),(965225828176625665,20)],
  .scan 3 2369190669160808441,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7107572007482425343,1776893001870606336,444223250467651584,111055812616912896,27763953154228224,6940988288557056,1735247072139264,433811768034816,108452942008704,27113235502176,6778308875544,1694577218886,423644304720,105911076180,26477769044,6619442262,1654860564,413715142,103428786,25857198,6464298,1616076,404018,101004,25252,6312,1578,396,98,24,6,2,2] 1 [(.D2,2369190669160808447),(.D0,965225828176625666),(.D0,4978789132546179078),(.D0,196203175208221875),(.D0,1546358528475042610),(.D0,17938134728891369),(.D0,738617061650722523),(.D0,793191463868397684),(.D0,601191841697448484),(.D0,136599914059540595),(.D0,13567008128886375),(.D0,2494253875290607),(.D0,59748602806518),(.D0,323797210757315),(.D0,7535244241825),(.D0,2461770128410),(.D0,12941285850),(.D0,822354884),(.D0,165199213),(.D0,41663102),(.D0,9914004),(.D0,475834),(.D0,128074),(.D0,2649),(.D0,18)],
  .batch [2] 4738381338321616896 [(.D1,1)],
  .batch [1711082149949472770,427770537487368194,106942634371842048,26735658592960512,6683914648240128,1670978662060032,417744665515008,104436166378752,26109041594688,6527260398672,1631815099668,407953774918,101988443730,25497110930,6374277732,1593569434,398392358,99598090,24899522,6224880,1556220,389056,97266,24314,6078,1522,380,94,24,6,2] 4738381338321616897 [(.D5,570360716649824256),(.D5,4912978280625045509),(.D5,185234699888032946),(.D5,1544530449255011121),(.D5,17633454858886120),(.D5,738566281672388314),(.D5,793183000538675315),(.D5,601190431142494755),(.D5,136599678967048306),(.D5,13566968946804326),(.D5,2494247344943598),(.D5,59747514415349),(.D5,323797029358786),(.D5,7535214008736),(.D5,2461765089561),(.D5,12940446041),(.D5,822214915),(.D5,165175884),(.D5,41659213),(.D5,9913355),(.D5,475725),(.D5,128055),(.D5,2645),(.D1,18)],
  .batch [2] 5879102771621265411 [(.D1,1)],
  .batch [146246337602519038] 5879102771621265412 [(.D1,4817918161183408134),(.D0,169391346647760051),(.D0,1541889890381632306),(.D0,17193361713322985),(.D0,738492932814794459),(.D0,793170775729076340),(.D0,601188393674228260),(.D0,136599339389003891),(.D0,13566912350463591),(.D0,2494237912220143),(.D0,59745942294774),(.D0,323796767338691),(.D0,7535170338721),(.D0,2461757811226),(.D0,12939232986),(.D0,822012740),(.D0,165142189),(.D0,41653598),(.D0,9912420),(.D0,475570),(.D2,128029),(.D5,2641),(.D4,16)],
  .scan 0 50,
  .scan2 5 9 [(5952225940422524930,4),(4781356576782778373,4),(163297749247655090,4),(1540874290814948145,4),(17024095118875624,4),(738464721715719898,4),(793166073879230579,4),(601187610032587299,4),(136599208782063730,4),(13566890582640230,4),(2494234284249582,4),(59745337633013,4),(323796666561730,4),(7535153542560,4),(2461755011865,4),(12938766425,4),(821934979,4),(165129228,4),(41651437,4),(9912059,4),(475509,4),(128019,4),(2639,4)],
  .scan 5 16,
  .scan 0 10,
  .scan2 3 0 [(16,20),(2639,20),(128019,20),(475509,20),(9912059,20),(41651437,20),(165129228,20),(821934979,20),(12938766425,20),(2461755011865,20),(7535153542560,20),(323796666561730,20),(59745337633013,20),(2494234284249582,20),(13566890582640230,20),(136599208782063730,20),(601187610032587299,20),(793166073879230579,20),(738464721715719898,20),(17024095118875624,20),(1540874290814948145,20),(163297749247655090,20),(4781356576782778373,20)],
  .scan 3 5952225940422524925,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4738381338321616893] 1 [(.D2,5952225940422524931),(.D0,4781356576782778374),(.D0,163297749247655091),(.D0,1540874290814948146),(.D0,17024095118875625),(.D0,738464721715719899),(.D0,793166073879230580),(.D0,601187610032587300),(.D0,136599208782063731),(.D0,13566890582640231),(.D0,2494234284249583),(.D0,59745337633014),(.D0,323796666561731),(.D0,7535153542561),(.D0,2461755011866),(.D0,12938766426),(.D0,821934980),(.D0,165129229),(.D0,41651438),(.D0,9912060),(.D0,475510),(.D0,128020),(.D0,2640),(.D0,16)],
  .scan 0 50,
  .scan2 5 9 [(2369190669160808446,4),(4767630605842120707,4),(4583924021019377669,4),(130392323287088306,4),(1535390053154853681,4),(16110055508859880,4),(738312381780717274,4),(793140683890063475,4),(601183378367726115,4),(136598503504586866,4),(13566773036394086,4),(2494214693208558,4),(59742072459509,4),(323796122366146,4),(7535062843296,4),(2461739895321,4),(12936247001,4),(821515075,4),(165059244,4),(41639773,4),(9910115,4),(475185,4),(127965,4),(2630,4)],
  .scan 5 14,
  .scan 0 10,
  .scan2 3 0 [(14,20),(2630,20),(127965,20),(475185,20),(9910115,20),(41639773,20),(165059244,20),(821515075,20),(12936247001,20),(2461739895321,20),(7535062843296,20),(323796122366146,20),(59742072459509,20),(2494214693208558,20),(13566773036394086,20),(136598503504586866,20),(601183378367726115,20),(793140683890063475,20),(738312381780717274,20),(16110055508859880,20),(1535390053154853681,20),(130392323287088306,20),(4583924021019377669,20),(4767630605842120707,20)],
  .scan 3 2369190669160808441,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7107572007482425343,1776893001870606336,444223250467651584,111055812616912896,27763953154228224,6940988288557056,1735247072139264,433811768034816,108452942008704,27113235502176,6778308875544,1694577218886,423644304720,105911076180,26477769044,6619442262,1654860564,413715142,103428786,25857198,6464298,1616076,404018,101004,25252,6312,1578,396,98,24,6,2,2] 1 [(.D2,2369190669160808447),(.D0,4767630605842120708),(.D0,4583924021019377670),(.D0,130392323287088307),(.D0,1535390053154853682),(.D0,16110055508859881),(.D0,738312381780717275),(.D0,793140683890063476),(.D0,601183378367726116),(.D0,136598503504586867),(.D0,13566773036394087),(.D0,2494214693208559),(.D0,59742072459510),(.D0,323796122366147),(.D0,7535062843297),(.D0,2461739895322),(.D0,12936247002),(.D0,821515076),(.D0,165059245),(.D0,41639774),(.D0,9910116),(.D0,475186),(.D0,127966),(.D0,2631),(.D0,14)],
  .batch [2] 4738381338321616896 [(.D1,1)],
  .batch [3158920892214411264] 4738381338321616897 [(.D5,4372765494315319298),(.D5,4518113169098244101),(.D5,119423847966899378),(.D5,1533561973934822193),(.D5,15805375638854632),(.D5,738261601802383066),(.D5,793132220560341107),(.D5,601181967812772387),(.D5,136598268412094578),(.D5,13566733854312038),(.D5,2494208162861550),(.D5,59740984068341),(.D5,323795940967618),(.D5,7535032610208),(.D5,2461734856473),(.D5,12935407193),(.D5,821375107),(.D5,165035916),(.D5,41635885),(.D5,9909467),(.D5,475077),(.D5,127947),(.D5,2627),(.D1,14)],
  .scan 0 50,
  .scan2 5 9 [(6317841784428822528,4),(3583035271261716482,4),(4386491465255976965,4),(97486897326521522,4),(1529905815494759217,4),(15196015898844136,4),(738160041845714650,4),(793115293900896371,4),(601179146702864931,4),(136597798227110002,4),(13566655490147942,4),(2494195102167534,4),(59738807286005,4),(323795578170562,4),(7534972144032,4),(2461724778777,4),(12933727577,4),(821095171,4),(164989260,4),(41628109,4),(9908171,4),(474861,4),(127911,4),(2621,4)],
  .scan 5 12,
  .scan 0 10,
  .scan2 3 0 [(12,20),(2621,20),(127911,20),(474861,20),(9908171,20),(41628109,20),(164989260,20),(821095171,20),(12933727577,20),(2461724778777,20),(7534972144032,20),(323795578170562,20),(59738807286005,20),(2494195102167534,20),(13566655490147942,20),(136597798227110002,20),(601179146702864931,20),(793115293900896371,20),(738160041845714650,20),(15196015898844136,20),(1529905815494759217,20),(97486897326521522,20),(4386491465255976965,20),(3583035271261716482,20)],
  .scan 3 6317841784428822523,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [18953525353286467589,4738381338321616896,1184595334580404224,296148833645101056,74037208411275264,18509302102818816,4627325525704704,1156831381426176,289207845356544,72301961339136,18075490334784,4518872583696,1129718145924,282429536480,70607384122,17651846030,4412961508,1103240376,275810094,68952524,17238130,4309532,1077384,269346,67336,16836,4208,1050,264,66,16,6,526486815369068540] 1 [(.D2,6317841784428822529),(.D0,3583035271261716483),(.D0,4386491465255976966),(.D0,97486897326521523),(.D0,1529905815494759218),(.D0,15196015898844137),(.D0,738160041845714651),(.D0,793115293900896372),(.D0,601179146702864932),(.D0,136597798227110003),(.D0,13566655490147943),(.D0,2494195102167535),(.D0,59738807286006),(.D0,323795578170563),(.D0,7534972144033),(.D0,2461724778778),(.D0,12933727578),(.D0,821095172),(.D0,164989261),(.D0,41628110),(.D0,9908172),(.D0,474862),(.D0,127912),(.D0,2622),(.D0,12)],
  .scan 0 50,
  .scan2 5 9 [(12898926976542179328,4),(2398439936681312259,4),(4189058909492576261,4),(64581471365954738,4),(1524421577834664753,4),(14281976288828392,4),(738007701910712026,4),(793089903911729267,4),(601174915038003747,4),(136597092949633138,4),(13566537943901798,4),(2494175511126510,4),(59735542112501,4),(323795033974978,4),(7534881444768,4),(2461709662233,4),(12931208153,4),(820675267,4),(164919276,4),(41616445,4),(9906227,4),(474537,4),(127857,4),(2612,4)],
  .scan 5 10,
  .scan 0 10,
  .scan2 3 0 [(10,20),(2612,20),(127857,20),(474537,20),(9906227,20),(41616445,20),(164919276,20),(820675267,20),(12931208153,20),(2461709662233,20),(7534881444768,20),(323795033974978,20),(59735542112501,20),(2494175511126510,20),(13566537943901798,20),(136597092949633138,20),(601174915038003747,20),(793089903911729267,20),(738007701910712026,20),(14281976288828392,20),(1524421577834664753,20),(64581471365954738,20),(4189058909492576261,20),(2398439936681312259,20)],
  .scan 3 12898926976542179323,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [28430288029929701373] 1 [(.D2,12898926976542179329),(.D0,2398439936681312260),(.D0,4189058909492576262),(.D0,64581471365954739),(.D0,1524421577834664754),(.D0,14281976288828393),(.D0,738007701910712027),(.D0,793089903911729268),(.D0,601174915038003748),(.D0,136597092949633139),(.D0,13566537943901799),(.D0,2494175511126511),(.D0,59735542112502),(.D0,323795033974979),(.D0,7534881444769),(.D0,2461709662234),(.D0,12931208154),(.D0,820675268),(.D0,164919277),(.D0,41616446),(.D0,9906228),(.D0,474538),(.D0,127858),(.D0,2613),(.D0,10)],
  .scan 0 50,
  .scan2 5 9 [(14215144014964850686,4),(5791354969059753985,4),(1213844602100908035,4),(3991626353729175557,4),(31676045405387954,4),(1518937340174570289,4),(13367936678812648,4),(737855361975709402,4),(793064513922562163,4),(601170683373142563,4),(136596387672156274,4),(13566420397655654,4),(2494155920085486,4),(59732276938997,4),(323794489779394,4),(7534790745504,4),(2461694545689,4),(12928688729,4),(820255363,4),(164849292,4),(41604781,4),(9904283,4),(474213,4),(127803,4),(2603,4)],
  .scan 5 8,
  .scan 0 10,
  .scan2 3 0 [(8,20),(2603,20),(127803,20),(474213,20),(9904283,20),(41604781,20),(164849292,20),(820255363,20),(12928688729,20),(2461694545689,20),(7534790745504,20),(323794489779394,20),(59732276938997,20),(2494155920085486,20),(13566420397655654,20),(136596387672156274,20),(601170683373142563,20),(793064513922562163,20),(737855361975709402,20),(13367936678812648,20),(1518937340174570289,20),(31676045405387954,20),(3991626353729175557,20),(1213844602100908035,20),(5791354969059753985,20)],
  .scan 3 14215144014964850681,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [42645432044894552063,10661358011223638016,2665339502805909504,666334875701477376,166583718925369344,41645929731342336,10411482432835584,2602870608208896,650717652052224,162679413013056,40669853253264,10167463313316,2541865828328,635466457080,158866614270,39716653570,9929163392,2482290846,620572714,155143178,38785794,9696448,2424114,606026,151506,37878,9468,2368,594,146,36,10,2,2,2] 1 [(.D2,14215144014964850687),(.D0,5791354969059753986),(.D0,1213844602100908036),(.D0,3991626353729175558),(.D0,31676045405387955),(.D0,1518937340174570290),(.D0,13367936678812649),(.D0,737855361975709403),(.D0,793064513922562164),(.D0,601170683373142564),(.D0,136596387672156275),(.D0,13566420397655655),(.D0,2494155920085487),(.D0,59732276938998),(.D0,323794489779395),(.D0,7534790745505),(.D0,2461694545690),(.D0,12928688730),(.D0,820255364),(.D0,164849293),(.D0,41604782),(.D0,9904284),(.D0,474214),(.D0,127804),(.D0,2604),(.D0,8)],
  .batch [2] 28430288029929701376 [(.D1,1)],
  .batch [10266492899696836610,2566623224924209154,641655806231052288,160413951557763072,40103487889440768,10025871972360192,2506467993090048,626616998272512,156654249568128,39163562392032,9790890598008,2447722649502,611930662374,152982665596,38245666398,9561416600,2390354148,597588538,149397134,37349284,9337322,2334330,583582,145896,36474,9120,2280,570,140,36,10,2] 28430288029929701377 [(.D5,3422164299898945536),(.D5,818979490574106627),(.D5,3925815501808041989),(.D5,20707570085199026),(.D5,1517109260954538801),(.D5,13063256808807400),(.D5,737804581997375194),(.D5,793056050592839795),(.D5,601169272818188835),(.D5,136596152579663986),(.D5,13566381215573606),(.D5,2494149389738478),(.D5,59731188547829),(.D5,323794308380866),(.D5,7534760512416),(.D5,2461689506841),(.D5,12927848921),(.D5,820115395),(.D5,164825964),(.D5,41600893),(.D5,9903635),(.D5,474105),(.D5,127785),(.D5,2600),(.D1,8)],
  .batch [2] 35274616629727592451 [(.D1,1)],
  .batch [525335419252022182,131333854813005456,32833463703251400,8208365925812832,2052091481453280,513022870363248,128255717590848,32063929397712,8015982349464,2003995587384,500998896792,125249724216,31312431072,7828107696,1957026960,489256776,122314176,30578472,7644672,1911168,477792,119448,29808,7488,1944,432,72,72,72] 35274616629727592452 [(.D1,248618773924282372),(.D0,3830755382366404614),(.D0,4864216844926131),(.D0,1514468702081159986),(.D0,12623163663244265),(.D0,737731233139781339),(.D0,793043825783240820),(.D0,601167235349922340),(.D0,136595813001619571),(.D0,13566324619232871),(.D0,2494139957015023),(.D0,59729616427254),(.D0,323794046360771),(.D0,7534716842401),(.D0,2461682228506),(.D0,12926635866),(.D0,819913220),(.D0,164792269),(.D0,41595278),(.D0,9902700),(.D0,473950),(.D2,127759),(.D5,2596),(.D4,6)],
  .batch [29505133324291968] 35624840242562273919 [(.D5,73506967506941637),(.D5,3801570081296847824),(.D1,1513657999273672297),(.D1,12488046528662984),(.D4,737708713617351124),(.D3,793040072529502451),(.D0,601166609807632612),(.D4,136595708744571282),(.D2,13566307243058156),(.D2,2494137060985903),(.D1,59729133755734),(.D5,323793965915517),(.D2,7534703434858),(.D5,2461679993915),(.D4,12926263433),(.D1,819851148),(.D5,164781923),(.D2,41593553),(.D3,9902412),(.D5,473901),(.D3,127752),(.D4,2594),(.D5,6)],
  .scan 0 50,
  .scan2 5 9 [(35639592809224419902,4),(66130684175868645,4),(3800340700741668992,4),(1513453102514475824,4),(12453897068796904,4),(737703022040706778,4),(793039123933395059,4),(601166451708281379,4),(136595682394679410,4),(13566302851409510,4),(2494136329044462,4),(59729011765493,4),(323793945583810,4),(7534700046240,4),(2461679429145,4),(12926169305,4),(819835459,4),(164779308,4),(41593117,4),(9902339,4),(473889,4),(127749,4),(2594,4)],
  .scan 5 6,
  .scan 0 10,
  .scan2 3 0 [(6,20),(2594,20),(127749,20),(473889,20),(9902339,20),(41593117,20),(164779308,20),(819835459,20),(12926169305,20),(2461679429145,20),(7534700046240,20),(323793945583810,20),(59729011765493,20),(2494136329044462,20),(13566302851409510,20),(136595682394679410,20),(601166451708281379,20),(793039123933395059,20),(737703022040706778,20),(12453897068796904,20),(1513453102514475824,20),(3800340700741668992,20),(66130684175868645,20)],
  .scan 3 35639592809224419897,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [1190352315165635637,297588078791408892,74397019697852220,18599254924463064,4649813731115772,1162453432778940,290613358194732,72653339548680,18163334887176,4540833721788,1135208430444,283802107608,70950526908,17737631724,4434407928,1108601988,277150500,69287628,17321904,4330476,1082616,270660,67668,16920,4224,1044,276,72,12] 1 [(.D2,35639592809224419903),(.D0,66130684175868646),(.D0,3800340700741668993),(.D0,1513453102514475825),(.D0,12453897068796905),(.D0,737703022040706779),(.D0,793039123933395060),(.D0,601166451708281380),(.D0,136595682394679411),(.D0,13566302851409511),(.D0,2494136329044463),(.D0,59729011765494),(.D0,323793945583811),(.D0,7534700046241),(.D0,2461679429146),(.D0,12926169306),(.D0,819835460),(.D0,164779309),(.D0,41593118),(.D0,9902340),(.D0,473890),(.D0,127750),(.D0,2595),(.D0,6)],
  .batch [525207486350128236] 793568210110423751 [(.D5,35242808704169208027),(.D1,3789318920045690886),(.D0,1511616139065146140),(.D3,12147736493908624),(.D2,737651995278225398),(.D5,793030619472981496),(.D2,601165034298212452),(.D3,136595446159667923),(.D4,13566263478907595),(.D5,2494129766960810),(.D4,59727918084884),(.D3,323793763303709),(.D3,7534669666224),(.D2,2461674365809),(.D5,12925325416),(.D2,819694811),(.D3,164755867),(.D3,41589211),(.D0,9901689),(.D2,473781),(.D0,127732),(.D0,2592),(.D2,5)],
  .scan 0 50,
  .scan2 5 9 [(1056171953285487868,4),(35111506832581675968,4),(3767435274781102208,4),(1507968864854381360,4),(11539857458781160,4),(737550682105704154,4),(793013733944227955,4),(601162220043420195,4),(136594977117202546,4),(13566185305163366,4),(2494116738003438,4),(59725746591989,4),(323793401388226,4),(7534609346976,4),(2461664312601,4),(12923649881,4),(819415555,4),(164709324,4),(41581453,4),(9900395,4),(473565,4),(127695,4),(2585,4)],
  .scan 5 4,
  .scan 0 10,
  .scan2 3 0 [(4,20),(2585,20),(127695,20),(473565,20),(9900395,20),(41581453,20),(164709324,20),(819415555,20),(12923649881,20),(2461664312601,20),(7534609346976,20),(323793401388226,20),(59725746591989,20),(2494116738003438,20),(13566185305163366,20),(136594977117202546,20),(601162220043420195,20),(793013733944227955,20),(737550682105704154,20),(11539857458781160,20),(1507968864854381360,20),(3767435274781102208,20),(35111506832581675968,20)],
  .scan 3 1056171953285487863,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [3168515859856463609,792128964964115900,198032241241028976,49508060310257244,12377015077564312,3094253769391076,773563442347770,193390860586942,48347715146736,12086928786684,3021732196670,755433049168,188858262294,47214565572,11803641392,2950910350,737727588,184431896,46107972,11526994,2881748,720438,180108,45028,11258,2814,702,178,44,10,2,2,2] 1 [(.D2,1056171953285487869),(.D0,35111506832581675969),(.D0,3767435274781102209),(.D0,1507968864854381361),(.D0,11539857458781161),(.D0,737550682105704155),(.D0,793013733944227956),(.D0,601162220043420196),(.D0,136594977117202547),(.D0,13566185305163367),(.D0,2494116738003439),(.D0,59725746591990),(.D0,323793401388227),(.D0,7534609346977),(.D0,2461664312602),(.D0,12923649882),(.D0,819415556),(.D0,164709325),(.D0,41581454),(.D0,9900396),(.D0,473566),(.D0,127696),(.D0,2586),(.D0,4)],
  .batch [85615587529944238] 2112343906570975740 [(.D1,34935478173700761324),(.D4,3738097164967616434),(.D0,1503079179885467065),(.D1,10724909963962112),(.D0,737414857523234313),(.D5,792991096513816315),(.D4,601158447138351588),(.D3,136594348299691112),(.D3,13566080502244794),(.D1,2494099270850344),(.D2,59722835399807),(.D0,323792916189530),(.D2,7534528480527),(.D0,2461650834860),(.D5,12921403591),(.D4,819041173),(.D5,164646927),(.D5,41571054),(.D2,9898662),(.D3,473277),(.D0,127648),(.D2,2577),(.D5,2)],
  .scan 0 50,
  .scan2 5 9 [(2155151700335947858,4),(34914074276818275263,4),(3734529848820535424,4),(1502484627194286896,4),(10625817848765416,4),(737398342170701530,4),(792988343955060851,4),(601157988378559011,4),(136594271839725682,4),(13566067758917222,4),(2494097146962414,4),(59722481418485,4),(323792857192642,4),(7534518647712,4),(2461649196057,4),(12921130457,4),(818995651,4),(164639340,4),(41569789,4),(9898451,4),(473241,4),(127641,4),(2576,4)],
  .scan 0 166,
  .scan 7 4,
  .scan2 3 0 [(2576,20),(127641,20),(473241,20),(9898451,20),(41569789,20),(164639340,20),(818995651,20),(12921130457,20),(2461649196057,20),(7534518647712,20),(323792857192642,20),(59722481418485,20),(2494097146962414,20),(13566067758917222,20),(136594271839725682,20),(601157988378559011,20),(792988343955060851,20),(737398342170701530,20),(10625817848765416,20),(1502484627194286896,20),(3734529848820535424,20),(34914074276818275263,20)],
  .scan 3 2155151700335947853,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [4738381338321616893] 1 [(.D2,2155151700335947859),(.D0,34914074276818275264),(.D0,3734529848820535425),(.D0,1502484627194286897),(.D0,10625817848765417),(.D0,737398342170701531),(.D0,792988343955060852),(.D0,601157988378559012),(.D0,136594271839725683),(.D0,13566067758917223),(.D0,2494097146962415),(.D0,59722481418486),(.D0,323792857192643),(.D0,7534518647713),(.D0,2461649196058),(.D0,12921130458),(.D0,818995652),(.D0,164639341),(.D0,41569790),(.D0,9898452),(.D0,473242),(.D0,127642),(.D0,2577),(.D0,2)],
  .scan 0 50,
  .scan2 5 9 [(2369190669160808446,4),(970556365755543635,4),(34716641721054874559,4),(3701624422859968640,4),(1497000389534192432,4),(9711778238749672,4),(737246002235698906,4),(792962953965893747,4),(601153756713697827,4),(136593566562248818,4),(13565950212671078,4),(2494077555921390,4),(59719216244981,4),(323792312997058,4),(7534427948448,4),(2461634079513,4),(12918611033,4),(818575747,4),(164569356,4),(41558125,4),(9896507,4),(472917,4),(127587,4),(2567,4)],
  .scan 7 3,
  .scan2 3 0 [(2567,20),(127587,20),(472917,20),(9896507,20),(41558125,20),(164569356,20),(818575747,20),(12918611033,20),(2461634079513,20),(7534427948448,20),(323792312997058,20),(59719216244981,20),(2494077555921390,20),(13565950212671078,20),(136593566562248818,20),(601153756713697827,20),(792962953965893747,20),(737246002235698906,20),(9711778238749672,20),(1497000389534192432,20),(3701624422859968640,20),(34716641721054874559,20),(970556365755543635,20)],
  .scan 3 2369190669160808441,
  .scan 0 339,
  .batch [1] 0 [(.D0,0)],
  .batch [7107572007482425343,1776893001870606336,444223250467651584,111055812616912896,27763953154228224,6940988288557056,1735247072139264,433811768034816,108452942008704,27113235502176,6778308875544,1694577218886,423644304720,105911076180,26477769044,6619442262,1654860564,413715142,103428786,25857198,6464298,1616076,404018,101004,25252,6312,1578,396,98,24,6,2,2] 1 [(.D2,2369190669160808447),(.D0,970556365755543636),(.D0,34716641721054874560),(.D0,3701624422859968641),(.D0,1497000389534192433),(.D0,9711778238749673),(.D0,737246002235698907),(.D0,792962953965893748),(.D0,601153756713697828),(.D0,136593566562248819),(.D0,13565950212671079),(.D0,2494077555921391),(.D0,59719216244982),(.D0,323792312997059),(.D0,7534427948449),(.D0,2461634079514),(.D0,12918611034),(.D0,818575748),(.D0,164569357),(.D0,41558126),(.D0,9896508),(.D0,472918),(.D0,127588),(.D0,2568),(.D0,0)],
  .batch [2] 4738381338321616896 [(.D1,1)],
  .scan 0 50,
  .scan2 5 9 [(4738381338321616896,4),(575691254228742226,4),(34650830869133740991,4),(3690655947539779712,4),(1495172310314160944,4),(9407098368744424,4),(737195222257364698,4),(792954490636171379,4),(601152346158744099,4),(136593331469756530,4),(13565911030589030,4),(2494071025574382,4),(59718127853813,4),(323792131598530,4),(7534397715360,4),(2461629040665,4),(12917771225,4),(818435779,4),(164546028,4),(41554237,4),(9895859,4),(472809,4),(127569,4)],
  .scan 5 2564,
  .scan 0 62
]
lemma chunk_21_ok : q6 cmds_21 cfg_21=some cfg_22:= by decide +kernel
lemma halted_final : isHalted qc cfg_22=true:= by decide +kernel
lemma init_eq_cfg_0 : cfg_0.denote=init []:=rfl
lemma tm104_halt : IsHalt qc:= by
  refine ⟨cfg_22.denote,?_,isHalted_spec halted_final⟩
  rw [← init_eq_cfg_0]
  refine q0 (q1 chunk_0_ok) ?_
  refine q0 (q1 chunk_1_ok) ?_
  refine q0 (q1 chunk_2_ok) ?_
  refine q0 (q1 chunk_3_ok) ?_
  refine q0 (q1 chunk_4_ok) ?_
  refine q0 (q1 chunk_5_ok) ?_
  refine q0 (q1 chunk_6_ok) ?_
  refine q0 (q1 chunk_7_ok) ?_
  refine q0 (q1 chunk_8_ok) ?_
  refine q0 (q1 chunk_9_ok) ?_
  refine q0 (q1 chunk_10_ok) ?_
  refine q0 (q1 chunk_11_ok) ?_
  refine q0 (q1 chunk_12_ok) ?_
  refine q0 (q1 chunk_13_ok) ?_
  refine q0 (q1 chunk_14_ok) ?_
  refine q0 (q1 chunk_15_ok) ?_
  refine q0 (q1 chunk_16_ok) ?_
  refine q0 (q1 chunk_17_ok) ?_
  refine q0 (q1 chunk_18_ok) ?_
  refine q0 (q1 chunk_19_ok) ?_
  refine q0 (q1 chunk_20_ok) ?_
  refine q0 (q1 chunk_21_ok) ?_
  exact ⟨0,rfl⟩
lemma holdout_0491_halt :
    IsHalt holdout_0491_tm :=
  qW tm104_halt

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := holdout_0491_halt

end BusyBeaver.M_1RB0LD_1LC0RD_1RE0RA_1LE0RF_1LA1RC_0LBHHH
