/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_---1RA` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_---1RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_HHH1RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_---1RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 2, Stmt.write 0 Dir.left)
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

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000000
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
@[simp] lemma pow_zero_list (l : List α) : l ^ (0 : ℕ)=[]:=rfl
@[simp] lemma pow_succ_list (l : List α) (n : ℕ) : l ^ (n + 1)=l ++ l ^ n:=rfl
lemma qb (l : List α) (m n : ℕ) : l ^ (m + n)=l ^ m ++ l ^ n:= by
  induction m with
  | zero => simp [Nat.zero_add]
  | succ m ih => simp [pow_succ_list,Nat.succ_add,ih,List.append_assoc]
lemma pow_shift (l : List α) (n : ℕ) : l ^ n ++ l=l ^ (n + 1):= by
  induction n with
  | zero => simp [pow_succ_list]
  | succ n ih => simp [pow_succ_list,List.append_assoc,ih]
@[simp] lemma nil_pow_list (n : ℕ) : ([] : List α) ^ n=[]:= by
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
lemma qJ {w : List (Fin 2)} (h : BusyBeaver.Longitudinal.BoundedConfig.all0 w=true) (n : ℕ) :
    (w ^ n) +> default=default:= by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ_list,append_assoc,ih,qD h]
lemma qA {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) :
    c₁ [tm]⊢^{1} c₂:= by simp [h]
lemma ql {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
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
lemma qm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3:= by
  obtain ⟨n,n_pos,hn⟩:=h₁; obtain ⟨m,hm⟩:=h₂
  exact ⟨n + m,lt_of_lt_of_le n_pos (Nat.le_add_right n m),qu tm c₁ c₂ c3 n m hn hm⟩
lemma qt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢ c₂) (h₂ : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  qm (step_stepPlus tm c₁ c₂ h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step_tm" : tactic =>
  `(tactic| (try refine qE ?_) <;>
    refine qt (by (try simp only [Turing.ListBlank.head_cons,default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,Tape.write,zero_cons_default,default_head,default_tail])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)) <;> (any_goals (first | finish | step_tm)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
macro "execute90" : tactic =>
  `(tactic| execute <;> execute)
def q4 (n : ℕ) (f : ℕ → α) : α :=
  Nat.casesOn n (f Nat.zero) (fun m => f (Nat.succ m))
@[simp] lemma strictNat_eq (n : ℕ) (f : ℕ → α) : q4 n f=f n:= by
  cases n <;> rfl
def W : List (Fin 2):=[1,1,1,1,0,1,1,1,1,1]
inductive Digit where
  | D0 | D1 | D2 | D3 | D4 | D5
deriving DecidableEq
def qP (d : Digit) (f : Digit → α) : α :=
  match d with
  | .D0 => f .D0
  | .D1 => f .D1
  | .D2 => f .D2
  | .D3 => f .D3
  | .D4 => f .D4
  | .D5 => f .D5
@[simp] lemma strictDigit_eq (d : Digit) (f : Digit → α) : qP d f=f d:= by
  cases d <;> rfl
def Digit.index : Digit → ℕ
  | .D0 => 0 | .D1 => 1 | .D2 => 2 | .D3 => 3 | .D4 => 4 | .D5 => 5
def qn : Digit → List (Fin 2)
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
def qL : Digit → ℕ
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
lemma qQ {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t u : ℕ} {r1 r3 : ListBlank (Fin 2)}
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
lemma qg (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (w : List (Fin 2)) :
    q2 tm q 0 0 w w:= by
  intro r1 r2 h
  change r1=r2 at h
  subst h
  rfl
lemma segCalls_nil (tm : Machine (Fin 2) (Fin 6)) (q : Fin 6) (t : ℕ) :
    q2 tm q t t [] []:= by
  intro r1 r2 h
  exact h
lemma q6 {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {t u v : ℕ}
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
  rcases qQ hr with ⟨r2,hr₁,hr₂⟩
  exact sideCalls_add (h₁ r1 r2 hr₁) (h₂ r2 r3 hr₂)
lemma qj {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {w1 w2 : List (Fin 2)}
    (h : ∀ l r,(([1,0,1] +> l) {{q}}> (w1 +> r)) [tm]⊢* (l <{{q}} ([1] +> w2 +> r))) :
    q2 tm q 1 0 w1 w2:= by
  intro r1 r2 hr
  change r1=r2 at hr
  subst hr
  exact ⟨w2 +> r1,fun l => h l r1,rfl⟩
lemma qG {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6} {w1 w_mid w2 : List (Fin 2)}
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
    exact q6 hwall1 ih
lemma walls {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W) (t n : ℕ) :
    q2 tm q t t (W ^ n) (W ^ n):= by
  induction t with
  | zero => exact qg tm q (W ^ n)
  | succ t ih =>
    have h1:=qB (wall_n hwall1 n) ih
    rwa [Nat.add_comm 1 t] at h1
lemma prefix_rule {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    {t u a b c : ℕ} {p p' : Digit}
    (h : q2 tm q t u (qn p ++ W ^ b) (W ^ a ++ qn p' ++ W ^ c)) (k : ℕ) :
    q2 tm q t u (W ^ k ++ (qn p ++ W ^ b)) (W ^ (k + a) ++ qn p' ++ W ^ c):= by
  have hw:=walls hwall1 t k
  have hc:=q6 hw h
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
    ⟨a.phase,take p + a.used,give p + a.given,qL p + a.sent⟩
lemma total_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qL p) (qn p ++ W ^ (take p + n)) (W ^ (give p) ++ qn (next p) ++ W ^ n))
    (t : ℕ) (p : Digit) (n : ℕ) :
    let a:=qx p t
    q2 tm q t a.sent (qn p ++ W ^ (a.used + n)) (W ^ a.given ++ qn a.phase ++ W ^ n):= by
  induction t generalizing p n with
  | zero =>
    dsimp [qx]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using qg tm q (qn p ++ W ^ n)
  | succ t ih =>
    dsimp [qx]
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
    dsimp only [qx]
    rcases qx p u with ⟨ph,us,gv,sn⟩
    simp only [Nat.zero_add]
  | succ t ih =>
    rw [Nat.succ_add]
    dsimp only [qx]
    rw [ih (next p)]
    dsimp only
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
    dsimp only
    rw [ih]
    dsimp only
    congr 1 <;> omega
def qx_fast : Digit → ℕ → Effect
  | .D0,0 => ⟨.D0,0,0,0⟩ | .D0,1 => ⟨.D1,0,0,0⟩ | .D0,2 => ⟨.D2,1,1,0⟩ | .D0,3 => ⟨.D3,1,1,0⟩ | .D0,4 => ⟨.D4,2,2,0⟩ | .D0,5 => ⟨.D5,2,2,0⟩
  | .D1,0 => ⟨.D1,0,0,0⟩ | .D1,1 => ⟨.D2,1,1,0⟩ | .D1,2 => ⟨.D3,1,1,0⟩ | .D1,3 => ⟨.D4,2,2,0⟩ | .D1,4 => ⟨.D5,2,2,0⟩ | .D1,5 => ⟨.D0,2,3,1⟩
  | .D2,0 => ⟨.D2,0,0,0⟩ | .D2,1 => ⟨.D3,0,0,0⟩ | .D2,2 => ⟨.D4,1,1,0⟩ | .D2,3 => ⟨.D5,1,1,0⟩ | .D2,4 => ⟨.D0,1,2,1⟩ | .D2,5 => ⟨.D1,1,2,1⟩
  | .D3,0 => ⟨.D3,0,0,0⟩ | .D3,1 => ⟨.D4,1,1,0⟩ | .D3,2 => ⟨.D5,1,1,0⟩ | .D3,3 => ⟨.D0,1,2,1⟩ | .D3,4 => ⟨.D1,1,2,1⟩ | .D3,5 => ⟨.D2,2,3,1⟩
  | .D4,0 => ⟨.D4,0,0,0⟩ | .D4,1 => ⟨.D5,0,0,0⟩ | .D4,2 => ⟨.D0,0,1,1⟩ | .D4,3 => ⟨.D1,0,1,1⟩ | .D4,4 => ⟨.D2,1,2,1⟩ | .D4,5 => ⟨.D3,1,2,1⟩
  | .D5,0 => ⟨.D5,0,0,0⟩ | .D5,1 => ⟨.D0,0,1,1⟩ | .D5,2 => ⟨.D1,0,1,1⟩ | .D5,3 => ⟨.D2,1,2,1⟩ | .D5,4 => ⟨.D3,1,2,1⟩ | .D5,5 => ⟨.D4,2,3,1⟩
  | p,n + 6 => qx p (n + 6)
lemma qx_fast_eq (p : Digit) (r : ℕ) : qx_fast p r=qx p r:= by
  cases p <;> rcases r with _ | _ | _ | _ | _ | _ | r <;> rfl
def qy (p : Digit) (t : ℕ) : Effect :=
  q4 (t / 6) (fun k =>
    q4 (t % 6) (fun r =>
      match qx_fast p r with
      | ⟨ph,u,g,s⟩ =>
        q4 (k * 2 + u) (fun u' =>
          q4 (k * 3 + g) (fun g' =>
            q4 (k + s) (fun s' =>
              ⟨ph,u',g',s'⟩)))))
lemma totalN_spec (p : Digit) (t : ℕ) : qy p t=qx p t:= by
  unfold qy
  simp only [strictNat_eq,qx_fast_eq]
  have h_div : t=(t / 6) * 6 + t % 6:=(Nat.div_add_mod' t 6).symm
  conv_rhs => rw [h_div,total_period]
lemma totalN_rule {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qL p) (qn p ++ W ^ (take p + n)) (W ^ (give p) ++ qn (next p) ++ W ^ n))
    (p : Digit) (t n : ℕ) (h : (qy p t).used ≤ n) :
    let a:=qy p t
    q2 tm q t a.sent (qn p ++ W ^ n) (W ^ a.given ++ qn a.phase ++ W ^ (n - a.used)):= by
  dsimp only
  have h_spec:=total_spec hwall1 hone t p (n - (qy p t).used)
  rw [← totalN_spec p t] at h_spec
  dsimp only at h_spec
  have h_add : (qy p t).used + (n - (qy p t).used)=n:=Nat.add_sub_of_le h
  rwa [h_add] at h_spec
abbrev qv:=List (Digit × ℕ)
def q9 : qv → List (Fin 2)
  | [] => []
  | (p,n) :: xs => qn p ++ W ^ n ++ q9 xs
def qU : ℕ → qv → Option (ℕ × qv)
  | t,[] => if Nat.beq t 0 then some (0,[]) else none
  | t,(p,n) :: xs =>
    if Nat.beq t 0 then some (0,(p,n) :: xs)
    else
      match qy p t with
      | ⟨ph,u,g,s⟩ =>
        if Nat.ble u n then
          match qU s xs with
          | some (e,ys) =>
            q4 (n - u + e) (fun m =>
              some (g,(ph,m) :: ys))
          | none => none
        else none
lemma batch_spec {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hwall1 : q2 tm q 1 1 W W)
    (hone : ∀ p n,q2 tm q 1 (qL p) (qn p ++ W ^ (take p + n)) (W ^ (give p) ++ qn (next p) ++ W ^ n))
    (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (h : qU t xs=some (e,ys)) :
    q2 tm q t 0 (q9 xs) (W ^ e ++ q9 ys):= by
  induction xs generalizing t e ys with
  | nil =>
    unfold qU at h
    split_ifs at h with ht
    injection h with hpair
    injection hpair with he hys
    subst he hys
    have ht0 : t=0:=Nat.beq_eq.mp ht
    subst ht0
    exact qg tm q []
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qU at h
    split_ifs at h with ht0
    · injection h with hpair
      injection hpair with he hys
      subst he hys
      have ht_eq : t=0:=Nat.beq_eq.mp ht0
      subst ht_eq
      simpa only [pow_zero_list,List.nil_append] using qg tm q (q9 ((p,n) :: xs))
    · dsimp only at h
      split_ifs at h with hle
      cases hb : qU (qy p t).sent xs with
      | none => rw [hb] at h; contradiction
      | some eys =>
        rcases eys with ⟨e',ys'⟩
        rw [hb] at h
        simp only [strictNat_eq] at h
        injection h with hpair
        injection hpair with he hys
        subst he hys
        have h1:=totalN_rule hwall1 hone p t n (Nat.ble_eq.mp hle)
        have h2:=ih (qy p t).sent e' ys' hb
        have h3:=q6 h1 h2
        simpa only [q9,qb,List.append_assoc] using h3
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
    (hone : ∀ p n,q2 tm q 1 (qL p) (qn p ++ W ^ (take p + n)) (W ^ (give p) ++ qn (next p) ++ W ^ n))
    (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (k : ℕ) (r : ListBlank (Fin 2))
    (h : qU t xs=some (e,ys)) :
    (([1,0,1] +> default) {{q}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
    (([1,0,1] +> default) {{q}}> ((W ^ (k + e)) +> (q9 ys) +> r)):= by
  apply calls_spec hemit t
  have hw:=walls hwall1 t k
  have hb:=batch_spec hwall1 hone t xs e ys h
  have hc:=q6 hw hb r r rfl
  simpa only [qb,List.append_assoc,append_assoc] using hc
abbrev Runs:=List (List (Fin 2) × ℕ)
def q3 (r : Runs) (f : Runs → α) : α :=
  match r with
  | [] => f []
  | head :: tail => f (head :: tail)
@[simp] lemma strictRuns_eq (r : Runs) (f : Runs → α) : q3 r f=f r:= by
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
        dsimp only
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
      q3 (Runs.push w 1 xs) (fun xs2 => (b,xs2))
    else match w with
      | [] => q4 (n - 1) (fun n' => (b,([b],n') :: xs))
      | u :: v =>
        q4 (n - 1) (fun n' =>
          q3 (Runs.push (b :: u :: v) n' xs) (fun xs1 =>
            q3 (Runs.push (u :: v) 1 xs1) (fun xs2 =>
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
      by_cases hn0 : (n == 0)=true
      · have hn_eq : n=0:=beq_iff_eq.mp hn0
        subst hn_eq
        simpa [Runs.denote] using ih
      · rw [if_neg hn0]
        by_cases hn1 : (n == 1)=true
        · rw [if_pos hn1]
          have hn_eq : n=1:=beq_iff_eq.mp hn1
          subst hn_eq
          simp only [strictRuns_eq,Runs.push_spec,Runs.denote,pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_assoc]
        · rw [if_neg hn1]
          have hn_pos : 0 < n:=Nat.pos_of_ne_zero (by intro h0; subst h0; exact hn0 rfl)
          have hn_eq : n=(n - 1) + 1:=(Nat.sub_add_cancel hn_pos).symm
          cases w with
          | nil =>
            simp only [strictNat_eq,Runs.denote]
            conv_lhs => rw [hn_eq,pow_succ_list]
            simp [append_assoc]
          | cons u v =>
            simp only [strictNat_eq,strictRuns_eq]
            rw [Runs.push_spec,Runs.push_spec,Runs.denote]
            conv_lhs => rw [hn_eq,pow_succ_list]
            simp [pow_succ_list,append_assoc]
inductive StripResult
  | done (v_rem : List (Fin 2))
  | more (w_rem : List (Fin 2))
def strip_step : List (Fin 2) → List (Fin 2) → Option StripResult
  | [],v => some (.done v)
  | b :: w,[] => some (.more (b :: w))
  | b :: w,c :: v => if b == c then strip_step w v else none
lemma strip_step_done {w v v' : List (Fin 2)} (h : strip_step w v=some (.done v')) :
    v=w ++ v':= by
  induction w generalizing v with
  | nil =>
    unfold strip_step at h
    injection h with hv; injection hv
  | cons b w ih =>
    cases v with
    | nil =>
      unfold strip_step at h
      nomatch h
    | cons c v =>
      unfold strip_step at h
      split_ifs at h with hbc
      have hbc_eq : b=c:=beq_iff_eq.mp hbc
      subst hbc_eq
      simp [ih h]
lemma strip_step_more {w v w' : List (Fin 2)} (h : strip_step w v=some (.more w')) :
    w=v ++ w':= by
  induction w generalizing v with
  | nil =>
    unfold strip_step at h
    nomatch h
  | cons b w ih =>
    cases v with
    | nil =>
      unfold strip_step at h
      injection h with hm; injection hm
    | cons c v =>
      unfold strip_step at h
      split_ifs at h with hbc
      have hbc_eq : b=c:=beq_iff_eq.mp hbc
      subst hbc_eq
      simp [ih h]
def Runs.remove_slow : List (Fin 2) → Runs → Option Runs
  | [],xs => q3 xs (fun xs' => some xs')
  | b :: w,xs =>
    match Runs.pop xs with
    | (b',xs') => if b == b' then Runs.remove_slow w xs' else none
lemma Runs.remove_slow_spec {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove_slow w xs=some ys) :
    Runs.denote xs=w +> Runs.denote ys:= by
  induction w generalizing xs with
  | nil =>
    unfold Runs.remove_slow at h
    simp only [strictRuns_eq] at h
    injection h with hys; subst hys; rfl
  | cons b w ih =>
    unfold Runs.remove_slow at h
    dsimp only at h
    split_ifs at h with hb
    have hb_eq : b=(Runs.pop xs).1:=beq_iff_eq.mp hb
    rw [Runs.pop_spec xs,← hb_eq,ih h]
    rfl
def Runs.remove_aux : ℕ → List (Fin 2) → Runs → Option Runs
  | 0,w,xs => Runs.remove_slow w xs
  | _ + 1,[],xs => q3 xs (fun xs' => some xs')
  | _ + 1,w,[] => Runs.remove_slow w []
  | fuel + 1,w,([],_) :: ys => Runs.remove_aux fuel w ys
  | fuel + 1,w,(c :: v,m) :: ys =>
    if m == 0 then Runs.remove_aux fuel w ys
    else match strip_step w (c :: v) with
      | none => none
      | some (.done v') =>
        if m == 1 then
          q3 (Runs.push v' 1 ys) (fun zs => some zs)
        else
          q4 (m - 1) (fun m' =>
            q3 (Runs.push v' 1 ((c :: v,m') :: ys)) (fun zs => some zs))
      | some (.more w') =>
        if m == 1 then Runs.remove_aux fuel w' ys
        else
          q4 (m - 1) (fun m' => Runs.remove_aux fuel w' ((c :: v,m') :: ys))
lemma Runs.remove_aux_spec {fuel : ℕ} {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove_aux fuel w xs=some ys) :
    Runs.denote xs=w +> Runs.denote ys:= by
  induction fuel generalizing w xs ys with
  | zero => exact Runs.remove_slow_spec h
  | succ fuel ih =>
    cases w with
    | nil =>
      unfold Runs.remove_aux at h
      simp only [strictRuns_eq] at h
      injection h with hys; subst hys; rfl
    | cons b w0 =>
      rcases xs with _ | ⟨⟨_ | ⟨c,v⟩,m⟩,ys'⟩
      · exact Runs.remove_slow_spec h
      · unfold Runs.remove_aux at h
        simpa [Runs.denote,nil_pow_list] using ih h
      · unfold Runs.remove_aux at h
        by_cases hm0 : (m == 0)=true
        · rw [if_pos hm0] at h
          have hm_eq : m=0:=beq_iff_eq.mp hm0
          subst hm_eq
          simpa [Runs.denote] using ih h
        · rw [if_neg hm0] at h
          have hm_pos : 0 < m:=Nat.pos_of_ne_zero (by intro h0; subst h0; exact hm0 rfl)
          have hm_eq : m=(m - 1) + 1:=(Nat.sub_add_cancel hm_pos).symm
          cases hs : strip_step (b :: w0) (c :: v) with
          | none => rw [hs] at h; contradiction
          | some res =>
            rw [hs] at h
            cases res with
            | done v' =>
              dsimp only at h
              have hv_eq:=strip_step_done hs
              by_cases hm1 : (m == 1)=true
              · rw [if_pos hm1] at h
                have hm1_eq : m=1:=beq_iff_eq.mp hm1
                subst hm1_eq
                simp only [strictRuns_eq] at h
                injection h with hys; subst hys
                simp [Runs.denote,Runs.push_spec,pow_succ_list,hv_eq,append_assoc]
              · rw [if_neg hm1] at h
                simp only [strictNat_eq,strictRuns_eq] at h
                injection h with hys; subst hys
                rw [Runs.push_spec,Runs.denote,Runs.denote]
                conv_lhs => rw [hm_eq,pow_succ_list]
                simp [pow_succ_list,hv_eq,append_assoc]
            | more w' =>
              dsimp only at h
              have hw_eq:=strip_step_more hs
              by_cases hm1 : (m == 1)=true
              · rw [if_pos hm1] at h
                have hm1_eq : m=1:=beq_iff_eq.mp hm1
                subst hm1_eq
                rw [Runs.denote,pow_succ_list,pow_zero_list,List.append_nil,ih h,hw_eq,append_assoc]
              · rw [if_neg hm1] at h
                simp only [strictNat_eq] at h
                have h_ih:=ih h
                rw [Runs.denote] at h_ih ⊢
                conv_lhs => rw [hm_eq,pow_succ_list]
                rw [append_assoc,h_ih,hw_eq,append_assoc]
def Runs.remove_fast1 (w : List (Fin 2)) (xs : Runs) : Option Runs :=
  match xs with
  | (v,1) :: rest =>
    if v == w then some rest
    else if w == [0] && v == [0,1,0] then
      some (([1,0],1) :: rest)
    else
      match rest with
      | (v2,1) :: rest2 =>
        if v == [1] && w == [1,0,1] && v2 == [0,1,1,0,1,1,0,1,1,0] then
          some (([1,0,1,1,0,1,1,0],1) :: rest2)
        else none
      | (v2,m2 + 2) :: rest2 =>
        if v == [1] && w == [1,0,1] && v2 == [0,1,1,0,1,1,0,1,1,0] then
          some (([1,0,1,1,0,1,1,0],1) :: ([0,1,1,0,1,1,0,1,1,0],m2 + 1) :: rest2)
        else if m2 == 0 && v == [0] && w == [0,1,0] && v2 == [1,0,1,1,1,1] then
          some (([1,1,1,1],1) :: ([1,0,1,1,1,1],1) :: rest2)
        else none
      | _ => none
  | (v,m + 2) :: rest =>
    if w == [1] && v == [1,0,1] then
      some (([0,1],1) :: ([1,0,1],m + 1) :: rest)
    else none
  | _ => none
lemma Runs.remove_fast1_spec {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove_fast1 w xs=some ys) :
    Runs.denote xs=w +> Runs.denote ys:= by
  rcases xs with _ | ⟨⟨v,_ | _ | m⟩,rest⟩
  · contradiction
  · contradiction
  · unfold Runs.remove_fast1 at h
    dsimp only at h
    by_cases hvw : (v == w)=true
    · rw [if_pos hvw] at h
      injection h with hys; subst hys
      have hvw_eq : v=w:=beq_iff_eq.mp hvw
      subst hvw_eq
      simp [Runs.denote,pow_succ_list]
    · rw [if_neg hvw] at h
      by_cases h1 : (w == [0] && v == [0,1,0])=true
      · rw [if_pos h1] at h
        injection h with hys; subst hys
        simp only [Bool.and_eq_true,beq_iff_eq] at h1
        rcases h1 with ⟨hw,hv⟩; subst hw hv; rfl
      · rw [if_neg h1] at h
        rcases rest with _ | ⟨⟨v2,_ | _ | m2⟩,rest2⟩
        · contradiction
        · contradiction
        · dsimp only at h
          split_ifs at h with h2
          injection h with hys; subst hys
          simp only [Bool.and_eq_true,beq_iff_eq] at h2
          rcases h2 with ⟨⟨hv,hw⟩,hv2⟩; subst hv hw hv2; rfl
        · dsimp only at h
          by_cases h3 : (v == [1] && w == [1,0,1] && v2 == [0,1,1,0,1,1,0,1,1,0])=true
          · rw [if_pos h3] at h
            injection h with hys; subst hys
            simp only [Bool.and_eq_true,beq_iff_eq] at h3
            rcases h3 with ⟨⟨hv,hw⟩,hv2⟩; subst hv hw hv2; rfl
          · rw [if_neg h3] at h
            split_ifs at h with h4
            injection h with hys; subst hys
            simp only [Bool.and_eq_true,beq_iff_eq] at h4
            rcases h4 with ⟨⟨⟨hm2,hv⟩,hw⟩,hv2⟩; subst hm2 hv hw hv2; rfl
  · unfold Runs.remove_fast1 at h
    dsimp only at h
    split_ifs at h with h5
    injection h with hys; subst hys
    simp only [Bool.and_eq_true,beq_iff_eq] at h5
    rcases h5 with ⟨hw,hv⟩; subst hw hv; rfl
def Runs.remove (w : List (Fin 2)) (xs : Runs) : Option Runs :=
  match Runs.remove_fast1 w xs with
  | some ys => some ys
  | none => Runs.remove_aux 16 w xs
lemma Runs.remove_spec {w : List (Fin 2)} {xs ys : Runs}
    (h : Runs.remove w xs=some ys) :
    Runs.denote xs=w +> Runs.denote ys:= by
  unfold Runs.remove at h
  cases hf : Runs.remove_fast1 w xs with
  | some zs =>
    rw [hf] at h
    injection h with hys; subst hys
    exact Runs.remove_fast1_spec hf
  | none =>
    rw [hf] at h
    exact Runs.remove_aux_spec h
def Runs.skip_block (w : List (Fin 2)) (limit : ℕ) (x v : List (Fin 2)) (m : ℕ) (ys : Runs) : Option (ℕ × Runs) :=
  if w.length % v.length == 0 || v.length % w.length == 0 then
    q4 (min w.length v.length) (fun g =>
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
  else none
lemma Runs.skip_block_spec {w : List (Fin 2)} {limit : ℕ} {x v : List (Fin 2)} {m : ℕ} {ys : Runs} {n : ℕ} {zs : Runs}
    (h : Runs.skip_block w limit x v m ys=some (n,zs)) :
    n ≤ limit ∧ x +> (v ^ m) +> Runs.denote ys=(w ^ n) +> Runs.denote zs:= by
  unfold Runs.skip_block at h
  simp only [strictNat_eq,strictRuns_eq] at h
  split_ifs at h with hdiv hk hkb hka heq
  injection h with hpair
  injection hpair with hn hzs
  subst hn hzs
  refine ⟨hkb,?_⟩
  rw [Runs.push_spec,Runs.push_spec]
  have hx1 : x ^ (1 : ℕ)=x:= by simp [pow_succ_list]
  rw [hx1]
  have hm_eq:=(Nat.add_sub_of_le hka).symm
  have hk_comm:=commute_power (beq_iff_eq.mp heq) (min (limit / (v.length / min w.length v.length)) (m / (w.length / min w.length v.length)))
  have h_lhs : x +> (v ^ m) +> Runs.denote ys =
      (x ++ v ^ (min (limit / (v.length / min w.length v.length)) (m / (w.length / min w.length v.length)) * (w.length / min w.length v.length))) +>
      (v ^ (m - min (limit / (v.length / min w.length v.length)) (m / (w.length / min w.length v.length)) * (w.length / min w.length v.length))) +> Runs.denote ys:= by
    conv_lhs => rw [hm_eq,qb]
    rw [append_assoc (v ^ _),← append_assoc x]
  rw [h_lhs,hk_comm,append_assoc]
def Runs.skip_periodic (w : List (Fin 2)) (n : ℕ) (xs : Runs) : Option (ℕ × Runs) :=
  match xs with
  | (x,nx) :: (v,m) :: ys =>
    if nx == 1 then
      if w.length ≤ x.length && x.length % w.length == 0 then
        Runs.skip_block w n [] x 1 ((v,m) :: ys)
      else Runs.skip_block w n x v m ys
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
  · dsimp only at h
    split_ifs at h with hnx hxl
    · have hnx1 : nx=1:=beq_iff_eq.mp hnx
      subst hnx1
      simpa [Runs.denote] using Runs.skip_block_spec h
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
      if m ≤ n then some (m,ys)
      else q4 (m - n) (fun m' => some (n,(v,m') :: ys))
    else Runs.skip_periodic w n ((v,m) :: ys)
lemma Runs.skip_spec {w : List (Fin 2)} {n : ℕ} {xs : Runs} {k : ℕ} {ys : Runs}
    (h : Runs.skip w n xs=some (k,ys)) :
    k ≤ n ∧ Runs.denote xs=(w ^ k) +> Runs.denote ys:= by
  rcases xs with _ | ⟨⟨v,m⟩,ys'⟩
  · contradiction
  · unfold Runs.skip at h
    simp only [strictNat_eq] at h
    split_ifs at h with hwv hmn
    · injection h with hpair
      injection hpair with hk hys
      subst hk hys
      have hwv_eq : w=v:=beq_iff_eq.mp hwv
      subst hwv_eq
      exact ⟨hmn,rfl⟩
    · injection h with hpair
      injection hpair with hk hys
      subst hk hys
      have hwv_eq : w=v:=beq_iff_eq.mp hwv
      subst hwv_eq
      have hle : n ≤ m:=Nat.le_of_not_le hmn
      refine ⟨le_rfl,?_⟩
      rw [Runs.denote,Runs.denote,← append_assoc,← qb,Nat.add_sub_of_le hle]
    · exact Runs.skip_periodic_spec h
def Runs.remove_fast : ℕ → List (Fin 2) → ℕ → Runs → Option Runs
  | 0,_,n,xs => if n == 0 then q3 xs (fun xs' => some xs') else none
  | fuel + 1,w,n,xs =>
    if n == 0 then q3 xs (fun xs' => some xs')
    else match Runs.skip w n xs with
      | some (k,ys) =>
        q4 (n - k) (fun n' => Runs.remove_fast fuel w n' ys)
      | none =>
        match Runs.remove w xs with
        | some ys =>
          q4 (n - 1) (fun n' => Runs.remove_fast fuel w n' ys)
        | none => none
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
    split_ifs at h with hn
    · injection h with hys; subst hys
      have hn0 : n=0:=beq_iff_eq.mp hn; subst hn0
      simp
    · have hn_pos : 0 < n:=Nat.pos_of_ne_zero (by intro h0; subst h0; exact hn rfl)
      cases hskip : Runs.skip w n xs with
      | some kys =>
        rcases kys with ⟨k,zs⟩
        rw [hskip] at h
        simp only [strictNat_eq] at h
        rcases Runs.skip_spec hskip with ⟨hkn,hden⟩
        rw [hden,ih h,← append_assoc,← qb,Nat.add_sub_of_le hkn]
      | none =>
        rw [hskip] at h
        cases hrem : Runs.remove w xs with
        | none => rw [hrem] at h; contradiction
        | some zs =>
          rw [hrem] at h
          simp only [strictNat_eq] at h
          rw [Runs.remove_spec hrem,ih h]
          have hn_eq : n=(n - 1) + 1:=(Nat.sub_add_cancel hn_pos).symm
          conv_rhs => rw [hn_eq,pow_succ_list,append_assoc]
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
    rw [Runs.denote,ih h,qJ hw n]
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
  · dsimp only at h
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
        apply ql
        unfold RMConfig.denote step
        dsimp only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply ql
        unfold RMConfig.denote step
        dsimp only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
  · dsimp only at h
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
        apply ql
        unfold RMConfig.denote step
        dsimp only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
      · rw [htm] at h
        simp only [strictRuns_eq] at h
        injection h with hc'; subst hc'
        apply ql
        unfold RMConfig.denote step
        dsimp only
        rw [hpop,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Runs.push_spec]
        simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil]
        rfl
def qk (d : Dir) (c : RMConfig) : RMConfig :=
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
lemma qS (d : Dir) (c : RMConfig) : (qk d c).denote=c.denote:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> try rfl
  · unfold qk RMConfig.denote
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.pop_spec r]
    simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil,
               Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
  · unfold qk RMConfig.denote
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.pop_spec l]
    simp only [pow_succ_list,pow_zero_list,List.append_nil,append_cons,append_nil,
               Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons]
lemma qW (d : Dir) (c : RMConfig) : (qk d c).dir=d:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> simp [qk]
lemma qI (d : Dir) (c : RMConfig) : (qk d c).state=c.state:= by
  rcases c with ⟨l,r,q,cd⟩
  cases d <;> cases cd <;> simp [qk]
structure Scan where
  q : Fin 6
  dir : Dir
  scan_in : List (Fin 2)
  scan_out : List (Fin 2)
  context : List (Fin 2)
def q5 (tm : Machine (Fin 2) (Fin 6)) (s : Scan) : Prop :=
  ∀ (n : ℕ) (l r : ListBlank (Fin 2)),
    match s.dir with
    | .right =>
      ((s.context.reverse +> l) {{s.q}}> ((s.scan_in ^ n) +> r)) [tm]⊢*
      ((s.context.reverse +> (s.scan_out.reverse ^ n) +> l) {{s.q}}> r)
    | .left =>
      (((s.scan_in.reverse ^ n) +> l) <{{s.q}} (s.context +> r)) [tm]⊢*
      (l <{{s.q}} (s.context +> (s.scan_out ^ n) +> r))
lemma qo {tm : Machine (Fin 2) (Fin 6)} {s : Scan} (hd : s.dir=.right)
    (hbase : ∀ l r,((s.context.reverse +> l) {{s.q}}> (s.scan_in +> r)) [tm]⊢*
                    ((s.context.reverse +> s.scan_out.reverse +> l) {{s.q}}> r)) :
    q5 tm s:= by
  unfold q5
  intro n l r
  rw [hd]
  dsimp only
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [pow_succ_list,append_assoc]
    have h1:=hbase l ((s.scan_in ^ n) +> r)
    have h2:=ih (s.scan_out.reverse +> l) r
    rw [← append_assoc (s.scan_out.reverse ^ n) s.scan_out.reverse l,pow_shift] at h2
    exact q0 h1 h2
lemma qf {tm : Machine (Fin 2) (Fin 6)} {s : Scan} (hd : s.dir=.left)
    (hbase : ∀ l r,((s.scan_in.reverse +> l) <{{s.q}} (s.context +> r)) [tm]⊢*
                    (l <{{s.q}} (s.context +> s.scan_out +> r))) :
    q5 tm s:= by
  unfold q5
  intro n l r
  rw [hd]
  dsimp only
  induction n generalizing l r with
  | zero => exact ⟨0,rfl⟩
  | succ n ih =>
    rw [pow_succ_list,append_assoc]
    have h1:=hbase ((s.scan_in.reverse ^ n) +> l) r
    have h2:=ih l (s.scan_out +> r)
    rw [← append_assoc (s.scan_out ^ n) s.scan_out r,pow_shift] at h2
    exact q0 h1 h2
def qi:=Runs.remove_fast 32
def qr (s : Scan) (n : ℕ) (l r : Runs) : Option (Runs × Runs) :=
  match s.dir with
  | .left =>
    match Runs.remove s.context r,qi s.scan_in.reverse n l with
    | some r',some l' =>
      q3 (Runs.push s.scan_out n r') (fun r1 =>
        q3 (Runs.push s.context 1 r1) (fun r2 =>
          some (l',r2)))
    | _,_ => none
  | .right =>
    match Runs.remove s.context.reverse l,qi s.scan_in n r with
    | some l',some r' =>
      q3 (Runs.push s.scan_out.reverse n l') (fun l1 =>
        q3 (Runs.push s.context.reverse 1 l1) (fun l2 =>
          some (l2,r')))
    | _,_ => none
lemma qK {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {n : ℕ} {l r l' r' : Runs}
    (hv : q5 tm s) (h : qr s n l r=some (l',r')) :
    (RMConfig.denote ⟨l,r,s.q,s.dir⟩) [tm]⊢* (RMConfig.denote ⟨l',r',s.q,s.dir⟩):= by
  unfold q5 at hv
  rcases s with ⟨q,d,sin,sout,ctx⟩
  have hv_n:=hv n
  unfold qr qi at h
  cases d
  · dsimp only at h hv_n
    cases hr : Runs.remove ctx r with
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
        dsimp only
        rw [Runs.push_spec,Runs.push_spec,Runs.remove_spec hr,Runs.remove_fast_spec hl]
        have hc1 : ctx ^ (1 : ℕ)=ctx:= by simp [pow_succ_list]
        rw [hc1]
        exact hv_n (Runs.denote l0) (Runs.denote r0)
  · dsimp only at h hv_n
    cases hl : Runs.remove ctx.reverse l with
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
        dsimp only
        rw [Runs.push_spec,Runs.push_spec,Runs.remove_spec hl,Runs.remove_fast_spec hr]
        have hc1 : ctx.reverse ^ (1 : ℕ)=ctx.reverse:= by simp [pow_succ_list]
        rw [hc1]
        exact hv_n (Runs.denote l0) (Runs.denote r0)
def use_scan (s : Scan) (n : ℕ) (c : RMConfig) : Option RMConfig :=
  if c.state == s.q then
    let z:=qk s.dir c
    match qr s n z.left z.right with
    | some (l,r) => some ⟨l,r,s.q,s.dir⟩
    | none => none
  else none
lemma use_scan_spec {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {n : ℕ} {c c' : RMConfig}
    (hv : q5 tm s) (h : use_scan s n c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold use_scan at h
  split_ifs at h with hq
  have hq_eq : c.state=s.q:=beq_iff_eq.mp hq
  rw [← qS s.dir c]
  have hd_z : (qk s.dir c).dir=s.dir:=qW s.dir c
  have hq_z : (qk s.dir c).state=s.q:= by rw [qI,hq_eq]
  rcases hz : qk s.dir c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp only at hd_z hq_z h
  subst hd_z hq_z
  cases hs : qr s n l r with
  | none => rw [hs] at h; contradiction
  | some lr =>
    rcases lr with ⟨l',r'⟩
    rw [hs] at h
    injection h with hc'; subst hc'
    exact qK hv hs
def qh_slow (p : Digit) (n : ℕ) (r : Runs) : Option Runs :=
  match Runs.remove (qn p) r with
  | none => none
  | some r1 => qi W n r1
lemma qh_slow_spec {p : Digit} {n : ℕ} {r r2 : Runs} (h : qh_slow p n r=some r2) :
    Runs.denote r=(qn p) +> (W ^ n) +> Runs.denote r2:= by
  unfold qh_slow at h
  cases hr1 : Runs.remove (qn p) r with
  | none => rw [hr1] at h; contradiction
  | some r1 =>
    rw [hr1] at h
    rw [Runs.remove_spec hr1,Runs.remove_fast_spec h]
def W_rot : List (Fin 2):=[1,1,1,1,1,0,1,1,1,1]
lemma w_rot_step : W_rot ++ [1]=[1] ++ W:=rfl
lemma w_rot_comm (m : ℕ) : W_rot ^ m ++ [1]=[1] ++ W ^ m:= by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_list,List.append_assoc,ih,← List.append_assoc,w_rot_step,List.append_assoc,← pow_succ_list]
lemma w_rot_append (m : ℕ) (s : ListBlank (Fin 2)) :
    (W_rot ^ m) +> ([1] +> s)=[1] +> (W ^ m) +> s:= by
  rw [← append_assoc,w_rot_comm,append_assoc]
lemma w_rot_tail_eq (s : ListBlank (Fin 2)) :
    ([1,1,1,1] ^ (1 : ℕ)) +> ([1,0,1,1,1,1] ^ (1 : ℕ)) +> ([1,0] ^ (1 : ℕ)) +> s =
    [1] +> W +> ([0] ^ (1 : ℕ)) +> s:=rfl
lemma w_rot_mid_eq (m : ℕ) (s : ListBlank (Fin 2)) :
    (W_rot ^ m) +> ([1,1,1,1] ^ (1 : ℕ)) +> ([1,0,1,1,1,1] ^ (1 : ℕ)) +> ([1,0] ^ (1 : ℕ)) +> s =
    [1] +> (W ^ (m + 1)) +> ([0] ^ (1 : ℕ)) +> s:= by
  rw [w_rot_tail_eq,w_rot_append,← append_assoc (W ^ m) W,pow_shift]
lemma w_rot_d0_eq (m : ℕ) (rest : Runs) :
    Runs.denote (([0],1) :: (W_rot,m) :: ([1,1,1,1],1) :: ([1,0,1,1,1,1],1) :: ([1,0],1) :: rest) =
    (qn .D0) +> (W ^ (m + 1)) +> Runs.denote (([0],1) :: rest):= by
  simp only [Runs.denote,w_rot_mid_eq]
  rfl
lemma w_rot_d2_eq (m : ℕ) (rest : Runs) :
    Runs.denote (([0,1,1,1,1],1) :: (W_rot,m) :: ([1,1,1,1],1) :: ([1,0,1,1,1,1],1) :: ([1,0],1) :: rest) =
    (qn .D2) +> (W ^ (m + 1)) +> Runs.denote (([0],1) :: rest):= by
  simp only [Runs.denote,w_rot_mid_eq]
  rfl
lemma w_rot_end_tail (s : ListBlank (Fin 2)) :
    ([1] ^ (4 : ℕ)) +> s=[1] +> ([1] ^ (3 : ℕ)) +> s:=rfl
lemma w_rot_end_eq (m : ℕ) (rest : Runs) :
    Runs.denote (([0],1) :: (W_rot,m) :: ([1],4) :: rest) =
    (qn .D0) +> (W ^ m) +> Runs.denote (([1],3) :: rest):= by
  simp only [Runs.denote,w_rot_end_tail,w_rot_append]
  rfl
def qh_one (p : Digit) (n : ℕ) (r : Runs) : Option Runs :=
  match r with
  | (v,mv) :: (w,m) :: rest =>
    if mv == 1 && w == W && qn p == v && n == m then
      some rest
    else if mv == 1 && w == W_rot then
      match rest with
      | (u1,m1) :: tail1 =>
        if p == .D0 && v == [0] && u1 == [1] && m1 == 4 && n == m then
          some (([1],3) :: tail1)
        else
          match tail1 with
          | (u2,m2) :: (u3,m3) :: tail3 =>
            if u1 == [1,1,1,1] && m1 == 1 && u2 == [1,0,1,1,1,1] && m2 == 1 && u3 == [1,0] && m3 == 1 && n == m + 1 then
              if p == .D0 && v == [0] then
                some (([0],1) :: tail3)
              else if p == .D2 && v == [0,1,1,1,1] then
                some (([0],1) :: tail3)
              else qh_slow p n r
            else qh_slow p n r
          | _ => qh_slow p n r
      | _ => qh_slow p n r
    else qh_slow p n r
  | _ => qh_slow p n r
lemma qh_one_spec {p : Digit} {n : ℕ} {r r2 : Runs} (h : qh_one p n r=some r2) :
    Runs.denote r=(qn p) +> (W ^ n) +> Runs.denote r2:= by
  rcases r with _ | ⟨⟨v,mv⟩,_ | ⟨⟨w,m⟩,rest⟩⟩
  · exact qh_slow_spec h
  · exact qh_slow_spec h
  · unfold qh_one at h
    dsimp only at h
    by_cases h1 : (mv == 1 && w == W && qn p == v && n == m)=true
    · rw [if_pos h1] at h
      injection h with hr2; subst hr2
      simp only [Bool.and_eq_true,beq_iff_eq] at h1
      rcases h1 with ⟨⟨⟨hmv,hw⟩,hp⟩,hn⟩
      subst hmv hw hp hn
      simp [Runs.denote,pow_succ_list]
    · rw [if_neg h1] at h
      by_cases h2 : (mv == 1 && w == W_rot)=true
      · rw [if_pos h2] at h
        simp only [Bool.and_eq_true,beq_iff_eq] at h2
        rcases h2 with ⟨hmv,hw⟩
        subst hmv hw
        rcases rest with _ | ⟨⟨u1,m1⟩,tail1⟩
        · exact qh_slow_spec h
        · dsimp only at h
          by_cases h3 : (p == .D0 && v == [0] && u1 == [1] && m1 == 4 && n == m)=true
          · rw [if_pos h3] at h
            injection h with hr2; subst hr2
            simp only [Bool.and_eq_true,beq_iff_eq] at h3
            rcases h3 with ⟨⟨⟨⟨hp,hv⟩,hu1⟩,hm1⟩,hn⟩
            subst hp hv hu1 hm1
            rw [hn]
            exact w_rot_end_eq m tail1
          · rw [if_neg h3] at h
            rcases tail1 with _ | ⟨⟨u2,m2⟩,_ | ⟨⟨u3,m3⟩,tail3⟩⟩
            · exact qh_slow_spec h
            · exact qh_slow_spec h
            · dsimp only at h
              by_cases h4 : (u1 == [1,1,1,1] && m1 == 1 && u2 == [1,0,1,1,1,1] && m2 == 1 && u3 == [1,0] && m3 == 1 && n == m + 1)=true
              · rw [if_pos h4] at h
                simp only [Bool.and_eq_true,beq_iff_eq] at h4
                rcases h4 with ⟨⟨⟨⟨⟨⟨hu1,hm1⟩,hu2⟩,hm2⟩,hu3⟩,hm3⟩,hn⟩
                subst hu1 hm1 hu2 hm2 hu3 hm3 hn
                by_cases h5 : (p == .D0 && v == [0])=true
                · rw [if_pos h5] at h
                  injection h with hr2; subst hr2
                  simp only [Bool.and_eq_true,beq_iff_eq] at h5
                  rcases h5 with ⟨hp,hv⟩
                  subst hp hv
                  exact w_rot_d0_eq m tail3
                · rw [if_neg h5] at h
                  by_cases h6 : (p == .D2 && v == [0,1,1,1,1])=true
                  · rw [if_pos h6] at h
                    injection h with hr2; subst hr2
                    simp only [Bool.and_eq_true,beq_iff_eq] at h6
                    rcases h6 with ⟨hp,hv⟩
                    subst hp hv
                    exact w_rot_d2_eq m tail3
                  · rw [if_neg h6] at h
                    exact qh_slow_spec h
              · rw [if_neg h4] at h
                exact qh_slow_spec h
      · rw [if_neg h2] at h
        exact qh_slow_spec h
def qh : qv → Runs → Option Runs
  | [],r => q3 r (fun r' => some r')
  | (p,n) :: xs,r =>
    match qh_one p n r with
    | none => none
    | some r2 => qh xs r2
lemma qF {xs : qv} {r r' : Runs}
    (h : qh xs r=some r') :
    Runs.denote r=(q9 xs) +> Runs.denote r':= by
  induction xs generalizing r with
  | nil =>
    unfold qh at h
    simp only [strictRuns_eq] at h
    injection h with hr'; subst hr'; rfl
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qh at h
    cases hr2 : qh_one p n r with
    | none => rw [hr2] at h; contradiction
    | some r2 =>
      rw [hr2] at h
      dsimp only at h
      rw [qh_one_spec hr2,ih h,q9,append_assoc,append_assoc]
def qw : qv → Runs → Runs
  | [],r => r
  | (p,n) :: xs,r =>
    q3 (qw xs r) (fun r1 =>
      q3 (Runs.push W n r1) (fun r2 =>
        Runs.push (qn p) 1 r2))
lemma qR (xs : qv) (r : Runs) :
    Runs.denote (qw xs r)=(q9 xs) +> Runs.denote r:= by
  induction xs with
  | nil => rfl
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qw q9
    simp only [strictRuns_eq]
    rw [Runs.push_spec,Runs.push_spec,ih]
    have hw1 : (qn p) ^ (1 : ℕ)=qn p:= by simp [pow_succ_list]
    rw [hw1,append_assoc,append_assoc]
def W_s0 : List (Fin 2):=[1,0,1,1,0,0,1,1,0,1]
def W_s1 : List (Fin 2):=[0,1,1,0,1,1,0,1,1,0]
lemma w_s0_step : W_s1 ++ [0,1,1,0,1]=[0,1,1,0,1] ++ W_s0:=rfl
lemma w_s0_comm (m : ℕ) : W_s1 ^ m ++ [0,1,1,0,1]=[0,1,1,0,1] ++ W_s0 ^ m:= by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_list,List.append_assoc,ih,← List.append_assoc,w_s0_step,List.append_assoc,← pow_succ_list]
lemma w_s0_append (m : ℕ) (s : ListBlank (Fin 2)) :
    (W_s1 ^ m) +> ([0,1,1,0,1] +> s)=[0,1,1,0,1] +> (W_s0 ^ m) +> s:= by
  rw [← append_assoc,w_s0_comm,append_assoc]
lemma w_s0_tail_eq (k : ℕ) (s : ListBlank (Fin 2)) :
    ([0,1] ^ (1 : ℕ)) +> ([1,0,1] ^ (k + 1)) +> s =
    [0,1,1,0,1] +> ([1,0,1] ^ k) +> s:=rfl
lemma w_s0_head_eq (m : ℕ) (s : ListBlank (Fin 2)) :
    ([1,0,1,1,0] ^ (1 : ℕ)) +> [0,1,1,0,1] +> (W_s0 ^ m) +> s =
    (W_s0 ^ (m + 1)) +> s:=rfl
lemma w_s0_eq (m k : ℕ) (rest : Runs) :
    Runs.denote (([1,0,1,1,0],1) :: (W_s1,m) :: ([0,1],1) :: ([1,0,1],k + 1) :: rest) =
    (W_s0 ^ (m + 1)) +> Runs.denote (([1,0,1],k) :: rest):= by
  simp only [Runs.denote,w_s0_tail_eq,w_s0_append,w_s0_head_eq]
def W_s5 : List (Fin 2):=[1,0,1,1,0,1]
lemma w_s5_eq (rest : Runs) :
    Runs.denote (([1,0,1],3) :: ([1,0,1,1,0,1,1,0],1) :: rest) =
    (W_s5 ^ (2 : ℕ)) +> Runs.denote (([1,0,1,1,0],1) :: rest):=rfl
def W_s9 : List (Fin 2):=[1,1,1]
lemma w_s9_4_eq1 (rest : Runs) :
    Runs.denote (([1,1,1,1,1,1,1,1,1],1) :: (W,1) :: rest) =
    (W_s9 ^ (4 : ℕ)) +> Runs.denote (([1,0,1,1,1,1,1],1) :: rest):=rfl
lemma w_s9_4_eq2 (m : ℕ) (rest : Runs) :
    Runs.denote (([1,1,1,1,1,1,1,1,1],1) :: (W,m + 1) :: rest) =
    (W_s9 ^ (4 : ℕ)) +> Runs.denote (([1,0,1,1,1,1,1],1) :: (W,m) :: rest):=rfl
lemma w_s9_5_eq1 (rest : Runs) :
    Runs.denote (([1,1,1,1,1,1,1,1,1,1,1,1],1) :: (W,1) :: rest) =
    (W_s9 ^ (5 : ℕ)) +> Runs.denote (([1,0,1,1,1,1,1],1) :: rest):=rfl
lemma w_s9_5_eq2 (m : ℕ) (rest : Runs) :
    Runs.denote (([1,1,1,1,1,1,1,1,1,1,1,1],1) :: (W,m + 1) :: rest) =
    (W_s9 ^ (5 : ℕ)) +> Runs.denote (([1,0,1,1,1,1,1],1) :: (W,m) :: rest):=rfl
def W_s1_in : List (Fin 2):=[1,0,1,1,1,1,1,1,1,1]
lemma w_s1_in_step : W ++ [1,1,1]=[1,1,1] ++ W_s1_in:=rfl
lemma w_s1_in_comm (m : ℕ) : W ^ m ++ [1,1,1]=[1,1,1] ++ W_s1_in ^ m:= by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ_list,List.append_assoc,ih,← List.append_assoc,w_s1_in_step,List.append_assoc,← pow_succ_list]
lemma w_s1_in_append (m : ℕ) (s : ListBlank (Fin 2)) :
    (W ^ m) +> ([1,1,1] +> s)=[1,1,1] +> (W_s1_in ^ m) +> s:= by
  rw [← append_assoc,w_s1_in_comm,append_assoc]
lemma w_s1_in_head_eq (m : ℕ) (s : ListBlank (Fin 2)) :
    ([1,0,1,1,1,1,1] ^ (1 : ℕ)) +> [1,1,1] +> (W_s1_in ^ m) +> s =
    (W_s1_in ^ (m + 1)) +> s:=rfl
lemma w_s1_in_tail1 (s : ListBlank (Fin 2)) :
    ([1,1,1,1,1,1,1,1,1,1,1,1] ^ (1 : ℕ)) +> s =
    [1,1,1] +> ([1,1,1,1,1,1,1,1,1] ^ (1 : ℕ)) +> s:=rfl
lemma w_s1_in_eq1 (m : ℕ) (rest : Runs) :
    Runs.denote (([1,0,1,1,1,1,1],1) :: (W,m) :: ([1,1,1,1,1,1,1,1,1,1,1,1],1) :: rest) =
    (W_s1_in ^ (m + 1)) +> Runs.denote (([1,1,1,1,1,1,1,1,1],1) :: rest):= by
  simp only [Runs.denote,w_s1_in_tail1,w_s1_in_append,w_s1_in_head_eq]
lemma w_s1_in_tail2 (s : ListBlank (Fin 2)) :
    ([1] ^ (3 : ℕ)) +> s=[1,1,1] +> s:=rfl
lemma w_s1_in_eq2 (m : ℕ) (rest : Runs) :
    Runs.denote (([1,0,1,1,1,1,1],1) :: (W,m) :: ([1],3) :: rest) =
    (W_s1_in ^ (m + 1)) +> Runs.denote rest:= by
  simp only [Runs.denote,w_s1_in_tail2,w_s1_in_append,w_s1_in_head_eq]
def qe_fast (w : List (Fin 2)) (r : Runs) : Option (ℕ × Runs) :=
  match r with
  | (v1,m1) :: (v2,m2) :: rest2 =>
    if w == W_s5 && v1 == [1,0,1] && m1 == 3 && v2 == [1,0,1,1,0,1,1,0] && m2 == 1 then
      some (2,([1,0,1,1,0],1) :: rest2)
    else if w == W_s9 && m1 == 1 && v2 == W then
      match m2 with
      | 0 => none
      | 1 =>
        if v1 == [1,1,1,1,1,1,1,1,1] then
          some (4,([1,0,1,1,1,1,1],1) :: rest2)
        else if v1 == [1,1,1,1,1,1,1,1,1,1,1,1] then
          some (5,([1,0,1,1,1,1,1],1) :: rest2)
        else none
      | m + 2 =>
        if v1 == [1,1,1,1,1,1,1,1,1] then
          some (4,([1,0,1,1,1,1,1],1) :: (W,m + 1) :: rest2)
        else if v1 == [1,1,1,1,1,1,1,1,1,1,1,1] then
          some (5,([1,0,1,1,1,1,1],1) :: (W,m + 1) :: rest2)
        else none
    else
      match rest2 with
      | (v3,m3) :: rest3 =>
        if w == W_s1_in && v1 == [1,0,1,1,1,1,1] && m1 == 1 && v2 == W then
          if v3 == [1,1,1,1,1,1,1,1,1,1,1,1] && m3 == 1 then
            q4 (m2 + 1) (fun n => some (n,([1,1,1,1,1,1,1,1,1],1) :: rest3))
          else if v3 == [1] && m3 == 3 then
            q4 (m2 + 1) (fun n => some (n,rest3))
          else none
        else
          match rest3 with
          | (v4,k + 2) :: rest4 =>
            if w == W_s0 && v1 == [1,0,1,1,0] && m1 == 1 && v2 == W_s1 && v3 == [0,1] && m3 == 1 && v4 == [1,0,1] then
              q4 (m2 + 1) (fun n => some (n,([1,0,1],k + 1) :: rest4))
            else none
          | _ => none
      | _ => none
  | _ => none
lemma qe_fast_spec {w : List (Fin 2)} {r s : Runs} {n : ℕ}
    (h : qe_fast w r=some (n,s)) :
    Runs.denote r=(w ^ n) +> Runs.denote s:= by
  rcases r with _ | ⟨⟨v1,m1⟩,_ | ⟨⟨v2,m2⟩,rest2⟩⟩
  · contradiction
  · contradiction
  · unfold qe_fast at h
    dsimp only at h
    by_cases h1 : (w == W_s5 && v1 == [1,0,1] && m1 == 3 && v2 == [1,0,1,1,0,1,1,0] && m2 == 1)=true
    · rw [if_pos h1] at h
      injection h with hpair
      injection hpair with hn hs
      subst hn hs
      simp only [Bool.and_eq_true,beq_iff_eq] at h1
      rcases h1 with ⟨⟨⟨⟨hw,hv1⟩,hm1⟩,hv2⟩,hm2⟩
      subst hw hv1 hm1 hv2 hm2
      exact w_s5_eq rest2
    · rw [if_neg h1] at h
      by_cases h2 : (w == W_s9 && m1 == 1 && v2 == W)=true
      · rw [if_pos h2] at h
        simp only [Bool.and_eq_true,beq_iff_eq] at h2
        rcases h2 with ⟨⟨hw,hm1⟩,hv2⟩
        subst hw hm1 hv2
        rcases m2 with _ | _ | m
        · contradiction
        · dsimp only at h
          by_cases h3 : (v1 == [1,1,1,1,1,1,1,1,1])=true
          · rw [if_pos h3] at h
            injection h with hpair; injection hpair with hn hs; subst hn hs
            have hv1 : v1=[1,1,1,1,1,1,1,1,1]:=beq_iff_eq.mp h3
            subst hv1
            exact w_s9_4_eq1 rest2
          · rw [if_neg h3] at h
            by_cases h4 : (v1 == [1,1,1,1,1,1,1,1,1,1,1,1])=true
            · rw [if_pos h4] at h
              injection h with hpair; injection hpair with hn hs; subst hn hs
              have hv1 : v1=[1,1,1,1,1,1,1,1,1,1,1,1]:=beq_iff_eq.mp h4
              subst hv1
              exact w_s9_5_eq1 rest2
            · rw [if_neg h4] at h; contradiction
        · dsimp only at h
          by_cases h3 : (v1 == [1,1,1,1,1,1,1,1,1])=true
          · rw [if_pos h3] at h
            injection h with hpair; injection hpair with hn hs; subst hn hs
            have hv1 : v1=[1,1,1,1,1,1,1,1,1]:=beq_iff_eq.mp h3
            subst hv1
            exact w_s9_4_eq2 (m + 1) rest2
          · rw [if_neg h3] at h
            by_cases h4 : (v1 == [1,1,1,1,1,1,1,1,1,1,1,1])=true
            · rw [if_pos h4] at h
              injection h with hpair; injection hpair with hn hs; subst hn hs
              have hv1 : v1=[1,1,1,1,1,1,1,1,1,1,1,1]:=beq_iff_eq.mp h4
              subst hv1
              exact w_s9_5_eq2 (m + 1) rest2
            · rw [if_neg h4] at h; contradiction
      · rw [if_neg h2] at h
        rcases rest2 with _ | ⟨⟨v3,m3⟩,rest3⟩
        · contradiction
        · dsimp only at h
          by_cases h5 : (w == W_s1_in && v1 == [1,0,1,1,1,1,1] && m1 == 1 && v2 == W)=true
          · rw [if_pos h5] at h
            simp only [Bool.and_eq_true,beq_iff_eq] at h5
            rcases h5 with ⟨⟨⟨hw,hv1⟩,hm1⟩,hv2⟩
            subst hw hm1 hv2 hv1
            by_cases h6 : (v3 == [1,1,1,1,1,1,1,1,1,1,1,1] && m3 == 1)=true
            · rw [if_pos h6] at h
              simp only [strictNat_eq] at h
              injection h with hpair; injection hpair with hn hs; subst hn hs
              simp only [Bool.and_eq_true,beq_iff_eq] at h6
              rcases h6 with ⟨hv3,hm3⟩
              subst hv3 hm3
              exact w_s1_in_eq1 m2 rest3
            · rw [if_neg h6] at h
              by_cases h7 : (v3 == [1] && m3 == 3)=true
              · rw [if_pos h7] at h
                simp only [strictNat_eq] at h
                injection h with hpair; injection hpair with hn hs; subst hn hs
                simp only [Bool.and_eq_true,beq_iff_eq] at h7
                rcases h7 with ⟨hv3,hm3⟩
                subst hv3 hm3
                exact w_s1_in_eq2 m2 rest3
              · rw [if_neg h7] at h; contradiction
          · rw [if_neg h5] at h
            rcases rest3 with _ | ⟨⟨v4,_ | _ | k⟩,rest4⟩
            · contradiction
            · contradiction
            · contradiction
            · dsimp only at h
              by_cases h8 : (w == W_s0 && v1 == [1,0,1,1,0] && m1 == 1 && v2 == W_s1 && v3 == [0,1] && m3 == 1 && v4 == [1,0,1])=true
              · rw [if_pos h8] at h
                simp only [strictNat_eq] at h
                injection h with hpair; injection hpair with hn hs; subst hn hs
                simp only [Bool.and_eq_true,beq_iff_eq] at h8
                rcases h8 with ⟨⟨⟨⟨⟨⟨hw,hv1⟩,hm1⟩,hv2⟩,hv3⟩,hm3⟩,hv4⟩
                subst hw hv1 hm1 hv2 hv3 hm3 hv4
                exact w_s0_eq m2 (k + 1) rest4
              · rw [if_neg h8] at h; contradiction
def qe : ℕ → List (Fin 2) → Runs → ℕ × Runs
  | 0,_,r => (0,r)
  | fuel + 1,w,r =>
    match qe_fast w r with
    | some res => res
    | none =>
      match r with
      | [] => (0,[])
      | (v,m) :: ys =>
        if w == v then
          match qe fuel w ys with
          | (n,s') => q4 (m + n) (fun mn => (mn,s'))
        else if (strip_step w v).isNone then (0,r)
        else
          match q4 (Runs.size (r.take 2)) (fun sz => Runs.skip w sz r) with
          | some (k,s) =>
            match qe fuel w s with
            | (n,s') => q4 (k + n) (fun kn => (kn,s'))
          | none =>
            match Runs.remove w r with
            | some s =>
              match qe fuel w s with
              | (n,s') => q4 (1 + n) (fun n1 => (n1,s'))
            | none => (0,r)
lemma qe_spec (fuel : ℕ) (w : List (Fin 2)) (r : Runs) :
    Runs.denote r=(w ^ (qe fuel w r).1) +> Runs.denote (qe fuel w r).2:= by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    unfold qe
    cases hfast : qe_fast w r with
    | some res =>
      rcases res with ⟨n,s⟩
      exact qe_fast_spec hfast
    | none =>
      rcases r with _ | ⟨⟨v,m⟩,ys⟩
      · rfl
      · dsimp only
        split_ifs with hwv hst
        · have hwv_eq : w=v:=beq_iff_eq.mp hwv
          subst hwv_eq
          have h_ih:=ih ys
          rcases hqe : qe fuel w ys with ⟨n,s'⟩
          rw [hqe] at h_ih
          simp only [strictNat_eq,Runs.denote,h_ih,qb,append_assoc]
        · rfl
        · simp only [strictNat_eq]
          cases hskip : Runs.skip w (Runs.size (((v,m) :: ys).take 2)) ((v,m) :: ys) with
          | some ks =>
            rcases ks with ⟨k,s⟩
            dsimp only
            have h_ih:=ih s
            rcases hqe : qe fuel w s with ⟨n,s'⟩
            rw [hqe] at h_ih
            dsimp only
            rw [(Runs.skip_spec hskip).2,h_ih,qb,append_assoc]
          | none =>
            dsimp only
            cases hrem : Runs.remove w ((v,m) :: ys) with
            | none => rfl
            | some s =>
              dsimp only
              have h_ih:=ih s
              rcases hqe : qe fuel w s with ⟨n,s'⟩
              rw [hqe] at h_ih
              dsimp only
              have h1n : 1 + n=n + 1:=Nat.add_comm 1 n
              rw [Runs.remove_spec hrem,h_ih,h1n,pow_succ_list,append_assoc]
def first_bad : ℕ → Digit → ℕ → ℕ
  | 0,_,_ => 1
  | fuel + 1,p,n =>
    if take p ≤ n then 1 + first_bad fuel (next p) (n - take p) else 1
def unsafe_bound (p : Digit) (n : ℕ) : ℕ :=
  6 * (n / 2) + first_bad 6 p (n % 2)
def match_digit (v : List (Fin 2)) : Option Digit :=
  if v == [0,1] then some .D0
  else if v == [1,1,1,1] then some .D1
  else if v == [0,1,1,1,1,1] then some .D2
  else if v == [1,1,1,1,1,1,1,1] then some .D3
  else if v == [0,1,1,1,1,1,1,1,1,1] then some .D4
  else if v == [1,1,1,1,1,1,1,1,1,1,1,1] then some .D5
  else none
lemma match_digit_spec {v : List (Fin 2)} {p : Digit} (h : match_digit v=some p) :
    v=qn p:= by
  unfold match_digit at h
  split_ifs at h with h0 h1 h2 h3 h4 h5
  · injection h with hp; subst hp; exact beq_iff_eq.mp h0
  · injection h with hp; subst hp; exact beq_iff_eq.mp h1
  · injection h with hp; subst hp; exact beq_iff_eq.mp h2
  · injection h with hp; subst hp; exact beq_iff_eq.mp h3
  · injection h with hp; subst hp; exact beq_iff_eq.mp h4
  · injection h with hp; subst hp; exact beq_iff_eq.mp h5
def choose_opt_slow (r : Runs) : Option (Digit × ℕ × Runs) :=
  match Runs.pop r with
  | (b,r1) =>
    if b == 0 then
      match Runs.remove [1] r1 with
      | none => none
      | some r_d0 =>
        match qe 32 W r_d0 with
        | (n0,rt0) =>
          if 0 < n0 then some (.D0,n0,rt0)
          else match Runs.remove [1,1,1,1] r_d0 with
            | none => some (.D0,0,r_d0)
            | some r_d2 =>
              match qe 32 W r_d2 with
              | (n2,rt2) =>
                if 0 < n2 then some (.D2,n2,rt2)
                else match Runs.remove [1,1,1,1] r_d2 with
                  | none => some (.D2,0,r_d2)
                  | some r_d4 =>
                    match qe 32 W r_d4 with
                    | (n4,rt4) => some (.D4,n4,rt4)
    else
      match Runs.remove [1,1,1] r1 with
      | none => none
      | some r_d1 =>
        match qe 32 W r_d1 with
        | (n1,rt1) =>
          if 0 < n1 then some (.D1,n1,rt1)
          else match Runs.remove [1,1,1,1] r_d1 with
            | none => some (.D1,0,r_d1)
            | some r_d3 =>
              match qe 32 W r_d3 with
              | (n3,rt3) =>
                if 0 < n3 then some (.D3,n3,rt3)
                else match Runs.remove [1,1,1,1] r_d3 with
                  | none => some (.D3,0,r_d3)
                  | some r_d5 =>
                    match qe 32 W r_d5 with
                    | (n5,rt5) => some (.D5,n5,rt5)
def choose_opt (r : Runs) : Option (Digit × ℕ × Runs) :=
  match r with
  | (v,1) :: (w,m) :: rest =>
    if w == W && 0 < m then
      match match_digit v with
      | some p =>
        match rest with
        | [([1],3)] => some (p,m,rest)
        | (v2,1) :: (w2,m2) :: _ =>
          if w2 == W && 0 < m2 && (match_digit v2).isSome then some (p,m,rest)
          else
            match qe 32 W ((w,m) :: rest) with
            | (n,rt) => some (p,n,rt)
        | _ =>
          match qe 32 W ((w,m) :: rest) with
          | (n,rt) => some (p,n,rt)
      | none => choose_opt_slow r
    else choose_opt_slow r
  | _ => choose_opt_slow r
def parse_cells_rem : ℕ → Runs → qv × Runs
  | 0,r => ([],r)
  | fuel + 1,r =>
    match r with
    | (v,mv) :: (w,m) :: rest =>
      if mv == 1 && w == W && 0 < m then
        match match_digit v with
        | some p =>
          match parse_cells_rem fuel rest with
          | (xs,rem) => ((p,m) :: xs,rem)
        | none => ([],r)
      else if mv == 1 && w == W_rot then
        match rest with
        | (u1,m1) :: tail1 =>
          if v == [0] && u1 == [1] && m1 == 4 then
            ([(.D0,m)],([1],3) :: tail1)
          else
            match tail1 with
            | (u2,m2) :: (u3,m3) :: tail3 =>
              if u1 == [1,1,1,1] && m1 == 1 && u2 == [1,0,1,1,1,1] && m2 == 1 && u3 == [1,0] && m3 == 1 then
                if v == [0] then
                  q4 (m + 1) (fun m1 =>
                    match parse_cells_rem fuel (([0],1) :: tail3) with
                    | (xs,rem) => ((.D0,m1) :: xs,rem))
                else if v == [0,1,1,1,1] then
                  q4 (m + 1) (fun m1 =>
                    match parse_cells_rem fuel (([0],1) :: tail3) with
                    | (xs,rem) => ((.D2,m1) :: xs,rem))
                else ([],r)
              else ([],r)
            | _ => ([],r)
        | _ => ([],r)
      else ([],r)
    | _ => ([],r)
lemma parse_cells_rem_spec (fuel : ℕ) (r : Runs) :
    Runs.denote r=(q9 (parse_cells_rem fuel r).1) +> Runs.denote (parse_cells_rem fuel r).2:= by
  induction fuel generalizing r with
  | zero => rfl
  | succ fuel ih =>
    rcases r with _ | ⟨⟨v,mv⟩,_ | ⟨⟨w,m⟩,rest⟩⟩
    · rfl
    · rfl
    · unfold parse_cells_rem
      dsimp only
      by_cases h1 : (mv == 1 && w == W && 0 < m)=true
      · rw [if_pos h1]
        cases hmd : match_digit v with
        | none => rfl
        | some p =>
          dsimp only
          have h_ih:=ih rest
          rcases hpcr : parse_cells_rem fuel rest with ⟨xs,rem⟩
          rw [hpcr] at h_ih
          dsimp only at h_ih ⊢
          simp only [Bool.and_eq_true,beq_iff_eq] at h1
          rcases h1 with ⟨⟨hmv,hw⟩,_⟩
          have hv:=match_digit_spec hmd
          subst hmv hw hv
          simp [Runs.denote,pow_succ_list,h_ih,q9,append_assoc]
      · rw [if_neg h1]
        by_cases h2 : (mv == 1 && w == W_rot)=true
        · rw [if_pos h2]
          simp only [Bool.and_eq_true,beq_iff_eq] at h2
          rcases h2 with ⟨hmv,hw⟩
          subst hmv hw
          rcases rest with _ | ⟨⟨u1,m1⟩,tail1⟩
          · rfl
          · dsimp only
            by_cases h3 : (v == [0] && u1 == [1] && m1 == 4)=true
            · rw [if_pos h3]
              dsimp only
              simp only [Bool.and_eq_true,beq_iff_eq] at h3
              rcases h3 with ⟨⟨hv,hu1⟩,hm1⟩
              subst hv hu1 hm1
              simpa [q9,append_assoc] using w_rot_end_eq m tail1
            · rw [if_neg h3]
              rcases tail1 with _ | ⟨⟨u2,m2⟩,_ | ⟨⟨u3,m3⟩,tail3⟩⟩
              · rfl
              · rfl
              · dsimp only
                by_cases h4 : (u1 == [1,1,1,1] && m1 == 1 && u2 == [1,0,1,1,1,1] && m2 == 1 && u3 == [1,0] && m3 == 1)=true
                · rw [if_pos h4]
                  simp only [Bool.and_eq_true,beq_iff_eq] at h4
                  rcases h4 with ⟨⟨⟨⟨⟨hu1,hm1⟩,hu2⟩,hm2⟩,hu3⟩,hm3⟩
                  subst hu1 hm1 hu2 hm2 hu3 hm3
                  by_cases h5 : (v == [0])=true
                  · rw [if_pos h5]
                    simp only [strictNat_eq]
                    have hv : v=[0]:=beq_iff_eq.mp h5
                    subst hv
                    have h_ih:=ih (([0],1) :: tail3)
                    rcases hpcr : parse_cells_rem fuel (([0],1) :: tail3) with ⟨xs,rem⟩
                    rw [hpcr] at h_ih
                    dsimp only at h_ih ⊢
                    rw [w_rot_d0_eq m tail3,h_ih,q9,append_assoc,append_assoc]
                  · rw [if_neg h5]
                    by_cases h6 : (v == [0,1,1,1,1])=true
                    · rw [if_pos h6]
                      simp only [strictNat_eq]
                      have hv : v=[0,1,1,1,1]:=beq_iff_eq.mp h6
                      subst hv
                      have h_ih:=ih (([0],1) :: tail3)
                      rcases hpcr : parse_cells_rem fuel (([0],1) :: tail3) with ⟨xs,rem⟩
                      rw [hpcr] at h_ih
                      dsimp only at h_ih ⊢
                      rw [w_rot_d2_eq m tail3,h_ih,q9,append_assoc,append_assoc]
                    · rw [if_neg h6]; rfl
                · rw [if_neg h4]; rfl
        · rw [if_neg h2]; rfl
def push_qv : Digit → ℕ → qv → qv
  | p,0,[] => [(p,0)]
  | p,n + 1,xs => (p,n + 1) :: xs
  | p,0,(p2,m) :: xs =>
    match p2 with
    | .D1 =>
      match p with
      | .D0 => push_qv .D2 m xs
      | .D1 => push_qv .D3 m xs
      | .D2 => push_qv .D4 m xs
      | .D3 => push_qv .D5 m xs
      | _ => (p,0) :: (.D1,m) :: xs
    | .D3 =>
      match p with
      | .D0 => push_qv .D4 m xs
      | .D1 => push_qv .D5 m xs
      | .D2 => (.D4,0) :: push_qv .D1 m xs
      | .D3 => (.D5,0) :: push_qv .D1 m xs
      | _ => (p,0) :: (.D3,m) :: xs
    | .D5 =>
      match p with
      | .D0 => (.D4,0) :: push_qv .D1 m xs
      | .D1 => (.D5,0) :: push_qv .D1 m xs
      | .D2 => (.D4,0) :: push_qv .D3 m xs
      | .D3 => (.D5,0) :: push_qv .D3 m xs
      | _ => (p,0) :: (.D5,m) :: xs
    | .D2 =>
      match p with
      | .D2 => q4 (m + 1) (fun m1 => (.D0,m1) :: xs)
      | .D3 => q4 (m + 1) (fun m1 => (.D1,m1) :: xs)
      | .D4 => q4 (m + 1) (fun m1 => (.D2,m1) :: xs)
      | .D5 => q4 (m + 1) (fun m1 => (.D3,m1) :: xs)
      | _ => (p,0) :: (.D2,m) :: xs
    | .D4 =>
      match p with
      | .D2 => (.D0,1) :: push_qv .D1 m xs
      | .D3 => (.D1,1) :: push_qv .D1 m xs
      | .D4 => (.D2,1) :: push_qv .D1 m xs
      | .D5 => (.D3,1) :: push_qv .D1 m xs
      | _ => (p,0) :: (.D4,m) :: xs
    | .D0 =>
      match m with
      | 0 => (p,0) :: (.D0,0) :: xs
      | m' + 1 =>
        match p with
        | .D2 => (.D0,1) :: push_qv .D2 m' xs
        | .D3 => (.D1,1) :: push_qv .D2 m' xs
        | .D4 => (.D2,1) :: push_qv .D2 m' xs
        | .D5 => (.D3,1) :: push_qv .D2 m' xs
        | _ => (p,0) :: (.D0,m' + 1) :: xs
lemma push_qv_spec (p : Digit) (n : ℕ) (xs : qv) :
    q9 (push_qv p n xs)=qn p ++ W ^ n ++ q9 xs:= by
  induction xs generalizing p n with
  | nil =>
    cases n <;> rfl
  | cons pm xs ih =>
    rcases pm with ⟨p2,m⟩
    cases n with
    | succ n => rfl
    | zero =>
      cases p2 <;> cases p
      all_goals try rfl
      all_goals (try cases m <;> try rfl)
      all_goals (
        unfold push_qv
        simp only [strictNat_eq,q9,ih,pow_succ_list,pow_zero_list,List.nil_append,List.append_nil,← List.append_assoc]
        rfl)
def qU_norm : ℕ → qv → Option (ℕ × qv)
  | t,[] => if Nat.beq t 0 then some (0,[]) else none
  | t,(p,n) :: xs =>
    if Nat.beq t 0 then some (0,(p,n) :: xs)
    else
      match qy p t with
      | ⟨ph,u,g,s⟩ =>
        if Nat.ble u n then
          match qU_norm s xs with
          | some (e,ys) =>
            q4 (n - u + e) (fun m =>
              some (g,push_qv ph m ys))
          | none => none
        else none
lemma qU_norm_spec {t : ℕ} {xs : qv} {e : ℕ} {ys : qv}
    (h : qU_norm t xs=some (e,ys)) :
    ∃ ys0,qU t xs=some (e,ys0) ∧ q9 ys=q9 ys0:= by
  induction xs generalizing t e ys with
  | nil =>
    unfold qU_norm at h
    split_ifs at h with ht
    injection h with hpair; injection hpair with he hys; subst he hys
    exact ⟨[],by simp [qU,ht],rfl⟩
  | cons pn xs ih =>
    rcases pn with ⟨p,n⟩
    unfold qU_norm at h
    split_ifs at h with ht0
    · injection h with hpair; injection hpair with he hys; subst he hys
      exact ⟨(p,n) :: xs,by simp [qU,ht0],rfl⟩
    · dsimp only at h
      split_ifs at h with hle
      cases hb : qU_norm (qy p t).sent xs with
      | none => rw [hb] at h; contradiction
      | some eys =>
        rcases eys with ⟨e',ys'⟩
        rw [hb] at h
        simp only [strictNat_eq] at h
        injection h with hpair; injection hpair with he hys; subst he hys
        rcases ih hb with ⟨ys0,hqU,hq9⟩
        refine ⟨((qy p t).phase,n - (qy p t).used + e') :: ys0,by simp [qU,ht0,hle,hqU],?_⟩
        rw [push_qv_spec,q9,hq9]
def ub_rem : Digit → ℕ → ℕ
  | .D0,0 => 1 | .D0,_ => 3
  | .D1,0 => 0 | .D1,_ => 2
  | .D2,0 => 1 | .D2,_ => 5
  | .D3,0 => 0 | .D3,_ => 4
  | .D4,0 => 3 | .D4,_ => 5
  | .D5,0 => 2 | .D5,_ => 4
def unsafe_bound_m1 (p : Digit) (n : ℕ) : ℕ :=
  6 * (n / 2) + ub_rem p (n % 2)
def min_nat (a b : ℕ) : ℕ :=
  if Nat.ble a b then a else b
def qe_xs_cap : qv → ℕ → ℕ
  | [],_ => 0
  | (p,n) :: xs,cap =>
    q4 (if Nat.ble cap n && Nat.ble 2 n then cap else min_nat (unsafe_bound_m1 p n) cap) (fun t =>
      q4 ((t + p.index) / 6) (fun child =>
        if Nat.beq child 0 then t
        else
          q4 (qe_xs_cap xs child) (fun u =>
            if Nat.beq u child then t else min_nat t (6 * u + 5 - p.index))))
def qe_xs : qv → ℕ
  | [] => 0
  | (p,n) :: xs =>
    q4 (unsafe_bound_m1 p n) (fun t =>
      q4 ((t + p.index) / 6) (fun child =>
        if Nat.beq child 0 then t
        else
          q4 (qe_xs_cap xs child) (fun u =>
            if Nat.beq u child then t else min_nat t (6 * u + 5 - p.index))))
def qv_loop : ℕ → ℕ → qv → ℕ × qv
  | 0,k,xs => (k,xs)
  | fuel + 1,k,xs =>
    q4 (qe_xs xs) (fun t =>
      if Nat.beq t 0 then (k,xs)
      else
        match qU_norm t xs with
        | some (e,ys) =>
          q4 (k + e) (fun k' => qv_loop fuel k' ys)
        | none => (k,xs))
lemma qa1 {tm : Machine (Fin 2) (Fin 6)}
    (hrule : ∀ t xs e ys k r,qU t xs=some (e,ys) →
      (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{E}}> ((W ^ (k + e)) +> (q9 ys) +> r)))
    (fuel k : ℕ) (xs : qv) (r : ListBlank (Fin 2)) :
    let res:=qv_loop fuel k xs
    (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
    (([1,0,1] +> default) {{E}}> ((W ^ res.1) +> (q9 res.2) +> r)):= by
  induction fuel generalizing k xs with
  | zero => exact ⟨0,rfl⟩
  | succ fuel ih =>
    unfold qv_loop
    simp only [strictNat_eq]
    split_ifs with ht
    · exact ⟨0,rfl⟩
    · cases hb : qU_norm (qe_xs xs) xs with
      | none => exact ⟨0,rfl⟩
      | some eys =>
        rcases eys with ⟨e,ys⟩
        dsimp only
        rcases qU_norm_spec hb with ⟨ys0,hqU,hq9⟩
        have hstep:=hrule (qe_xs xs) xs e ys0 k r hqU
        rw [← hq9] at hstep
        exact q0 hstep (ih (k + e) ys)
lemma step7_pre (rest : Runs) :
    Runs.denote (([0],1) :: ([1],1) :: ([0],1) :: ([1],1) :: ([1,1,1,1,0,1,1,1,1],1) :: rest) =
    (W ^ 0) +> (q9 [(.D0,0)]) +> Runs.denote (([0],1) :: ([1],1) :: ([1,1,1,1,0,1,1,1,1],1) :: rest):=rfl
lemma step7_post (rest : Runs) :
    (W ^ 0) +> (q9 [(.D1,0)]) +> Runs.denote (([0],1) :: ([1],1) :: ([1,1,1,1,0,1,1,1,1],1) :: rest) =
    (W ^ 1) +> Runs.denote (([0,1,1,1,1],1) :: rest):=rfl
lemma step7_qU : qU 1 [(.D0,0)]=some (0,[(.D1,0)]):=rfl
lemma step7_rule {tm : Machine (Fin 2) (Fin 6)}
    (hrule : ∀ t xs e ys k r,qU t xs=some (e,ys) →
      (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{E}}> ((W ^ (k + e)) +> (q9 ys) +> r)))
    (rest : Runs) :
    (([1,0,1] +> default) {{E}}> Runs.denote (([0],1) :: ([1],1) :: ([0],1) :: ([1],1) :: ([1,1,1,1,0,1,1,1,1],1) :: rest)) [tm]⊢*
    (([1,0,1] +> default) {{E}}> ((W ^ 1) +> Runs.denote (([0,1,1,1,1],1) :: rest))):= by
  rw [step7_pre,← step7_post]
  exact hrule 1 [(.D0,0)] 0 [(.D1,0)] 0 _ step7_qU
def qa0_wk (cnt k : ℕ) (l r_cells : Runs) : RMConfig :=
  match parse_cells_rem 32 r_cells with
  | (xs,r1) =>
    match qv_loop cnt k xs with
    | (k_new,ys) =>
      q3 (qw ys r1) (fun r2 =>
        q3 (Runs.push W k_new r2) (fun r3 =>
          ⟨l,r3,E,.right⟩))
lemma qa0_wk_spec {tm : Machine (Fin 2) (Fin 6)}
    (hrule : ∀ t xs e ys k r,qU t xs=some (e,ys) →
      (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{E}}> ((W ^ (k + e)) +> (q9 ys) +> r)))
    (cnt k : ℕ) (l r_cells : Runs) (hl : Runs.denote l=[1,0,1] +> default) :
    (([1,0,1] +> default) {{E}}> ((W ^ k) +> Runs.denote r_cells)) [tm]⊢*
    (qa0_wk cnt k l r_cells).denote:= by
  unfold qa0_wk
  have hpcr:=parse_cells_rem_spec 32 r_cells
  rcases h1 : parse_cells_rem 32 r_cells with ⟨xs,r1⟩
  rw [h1] at hpcr; dsimp only at hpcr ⊢
  have hbl:=qa1 hrule cnt k xs (Runs.denote r1)
  rcases h2 : qv_loop cnt k xs with ⟨k_new,ys⟩
  rw [h2] at hbl; dsimp only at hbl ⊢
  simp only [strictRuns_eq,RMConfig.denote,hl,Runs.push_spec,qR,hpcr]
  exact hbl
def qa0 (cnt : ℕ) (c : RMConfig) : Option RMConfig :=
  if c.state == E then
    let z:=qk .right c
    match Runs.remove [1,0,1] z.left with
    | some l0 =>
      if Runs.zeros l0 then
        match z.right with
        | (w,k) :: rest =>
          if w == W then
            some (qa0_wk cnt k z.left rest)
          else
            match cnt,rest with
            | cnt' + 1,(u1,m1) :: (u2,m2) :: (u3,m3) :: (u4,m4) :: rest4 =>
              if w == [0] && k == 1 && u1 == [1] && m1 == 1 && u2 == [0] && m2 == 1 && u3 == [1] && m3 == 1 && u4 == [1,1,1,1,0,1,1,1,1] && m4 == 1 then
                some (qa0_wk cnt' 1 z.left (([0,1,1,1,1],1) :: rest4))
              else none
            | _,_ => none
        | [] => none
      else none
    | none => none
  else none
lemma qa3 {tm : Machine (Fin 2) (Fin 6)}
    (hrule : ∀ t xs e ys k r,qU t xs=some (e,ys) →
      (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{E}}> ((W ^ (k + e)) +> (q9 ys) +> r)))
    {cnt : ℕ} {c c' : RMConfig} (h : qa0 cnt c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qa0 at h
  split_ifs at h with hq
  have hq_eq : c.state=E:=beq_iff_eq.mp hq
  rw [← qS .right c]
  have hd_z : (qk .right c).dir=.right:=qW .right c
  have hq_z : (qk .right c).state=E:= by rw [qI,hq_eq]
  rcases hz : qk .right c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp only at hd_z hq_z h
  subst hd_z hq_z
  cases hl0 : Runs.remove [1,0,1] l with
  | none => rw [hl0] at h; contradiction
  | some l0 =>
    rw [hl0] at h
    dsimp only at h
    split_ifs at h with hz0
    have hl_den : Runs.denote l=[1,0,1] +> default:= by
      rw [Runs.remove_spec hl0,Runs.zeros_spec hz0]
    rcases r with _ | ⟨⟨w,k⟩,rest⟩
    · contradiction
    · dsimp only at h
      by_cases hw : (w == W)=true
      · rw [if_pos hw] at h
        injection h with hc'; subst hc'
        have hw_eq : w=W:=beq_iff_eq.mp hw
        subst hw_eq
        unfold RMConfig.denote
        dsimp only
        rw [hl_den,Runs.denote]
        exact qa0_wk_spec hrule cnt k l rest hl_den
      · rw [if_neg hw] at h
        rcases cnt with _ | cnt'
        · contradiction
        · rcases rest with _ | ⟨⟨u1,m1⟩,_ | ⟨⟨u2,m2⟩,_ | ⟨⟨u3,m3⟩,_ | ⟨⟨u4,m4⟩,rest4⟩⟩⟩⟩
          · contradiction
          · contradiction
          · contradiction
          · contradiction
          · dsimp only at h
            split_ifs at h with hstep7
            injection h with hc'; subst hc'
            simp only [Bool.and_eq_true,beq_iff_eq] at hstep7
            rcases hstep7 with ⟨⟨⟨⟨⟨⟨⟨⟨⟨hw0,hk⟩,hu1⟩,hm1⟩,hu2⟩,hm2⟩,hu3⟩,hm3⟩,hu4⟩,hm4⟩
            subst hw0 hk hu1 hm1 hu2 hm2 hu3 hm3 hu4 hm4
            unfold RMConfig.denote
            dsimp only
            rw [hl_den]
            exact q0 (step7_rule hrule rest4) (qa0_wk_spec hrule cnt' 1 l (([0,1,1,1,1],1) :: rest4) hl_den)
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
def qT (q : Fin 6) (c : RMConfig) : Option RMConfig :=
  if c.state == q then
    let z:=qk .right c
    match qe 32 W z.right with
    | (k,r0) =>
      match qq 32 r0 none with
      | (t,xs) =>
        if t == 0 then none
        else
          match Runs.remove [1,0,1] z.left,qU t xs with
          | some l0,some (e,ys) =>
            if Runs.zeros l0 then
              match qh xs r0 with
              | some r1 =>
                q4 (k + e) (fun ke =>
                  q3 (qw ys r1) (fun r2 =>
                    q3 (Runs.push W ke r2) (fun r3 =>
                      some ⟨z.left,r3,q,.right⟩)))
              | none => none
            else none
          | _,_ => none
  else none
lemma qV {tm : Machine (Fin 2) (Fin 6)} {q : Fin 6}
    (hrule : ∀ t xs e ys k r,qU t xs=some (e,ys) →
      (([1,0,1] +> default) {{q}}> ((W ^ k) +> (q9 xs) +> r)) [tm]⊢*
      (([1,0,1] +> default) {{q}}> ((W ^ (k + e)) +> (q9 ys) +> r)))
    {c c' : RMConfig} (h : qT q c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qT at h
  split_ifs at h with hq
  have hq_eq : c.state=q:=beq_iff_eq.mp hq
  rw [← qS .right c]
  have hd_z : (qk .right c).dir=.right:=qW .right c
  have hq_z : (qk .right c).state=q:= by rw [qI,hq_eq]
  rcases hz : qk .right c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp only at hd_z hq_z h
  subst hd_z hq_z
  have hqe_spec:=qe_spec 32 W r
  rcases hqe : qe 32 W r with ⟨k,r0⟩
  rw [hqe] at h hqe_spec
  dsimp only at h hqe_spec
  rcases hqq : qq 32 r0 none with ⟨t,xs⟩
  rw [hqq] at h
  dsimp only at h
  split_ifs at h with ht0
  cases hl0 : Runs.remove [1,0,1] l with
  | none => rw [hl0] at h; contradiction
  | some l0 =>
    rw [hl0] at h
    cases hb : qU t xs with
    | none => rw [hb] at h; contradiction
    | some eys =>
      rcases eys with ⟨e,ys⟩
      rw [hb] at h
      dsimp only at h
      split_ifs at h with hz0
      cases hrc : qh xs r0 with
      | none => rw [hrc] at h; contradiction
      | some r1 =>
        rw [hrc] at h
        simp only [strictNat_eq,strictRuns_eq] at h
        injection h with hc'; subst hc'
        unfold RMConfig.denote
        dsimp only
        have hl_den : Runs.denote l=[1,0,1] +> default:= by
          rw [Runs.remove_spec hl0,Runs.zeros_spec hz0]
        rw [hl_den,Runs.push_spec,qR,hqe_spec,qF hrc]
        exact hrule t xs e ys k (Runs.denote r1) hb
def qc_zero (s : Scan) (c : RMConfig) : Option RMConfig :=
  if c.state == s.q then
    let z:=qk s.dir c
    match s.dir with
    | .left =>
      match Runs.remove s.context z.right with
      | some r' =>
        match qe 32 s.scan_in.reverse z.left with
        | (n,l') =>
          q3 (Runs.push s.scan_out n r') (fun r1 =>
            q3 (Runs.push s.context 1 r1) (fun r2 =>
              some ⟨l',r2,s.q,.left⟩))
      | none => none
    | .right =>
      match Runs.remove s.context.reverse z.left with
      | some l' =>
        match qe 32 s.scan_in z.right with
        | (n,r') =>
          q3 (Runs.push s.scan_out.reverse n l') (fun l1 =>
            q3 (Runs.push s.context.reverse 1 l1) (fun l2 =>
              some ⟨l2,r',s.q,.right⟩))
      | none => none
  else none
lemma qc_zero_spec {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {c c' : RMConfig}
    (hv : q5 tm s) (h : qc_zero s c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qc_zero at h
  split_ifs at h with hq
  have hq_eq : c.state=s.q:=beq_iff_eq.mp hq
  rw [← qS s.dir c]
  have hd_z : (qk s.dir c).dir=s.dir:=qW s.dir c
  have hq_z : (qk s.dir c).state=s.q:= by rw [qI,hq_eq]
  rcases hz : qk s.dir c with ⟨l,r,qz,dz⟩
  rw [hz] at hd_z hq_z h
  dsimp only at hd_z hq_z h
  subst hd_z hq_z
  unfold q5 at hv
  rcases s with ⟨sq,d,sin,sout,ctx⟩
  cases d
  · dsimp only at h hv
    cases hr : Runs.remove ctx r with
    | none => rw [hr] at h; contradiction
    | some r0 =>
      rw [hr] at h
      have hqe_spec:=qe_spec 32 sin.reverse l
      rcases hqe : qe 32 sin.reverse l with ⟨n,l0⟩
      rw [hqe] at h hqe_spec
      simp only [strictRuns_eq] at h
      injection h with hc'; subst hc'
      unfold RMConfig.denote
      dsimp only
      rw [Runs.push_spec,Runs.push_spec,Runs.remove_spec hr,hqe_spec]
      have hc1 : ctx ^ (1 : ℕ)=ctx:= by simp [pow_succ_list]
      rw [hc1]
      exact hv n (Runs.denote l0) (Runs.denote r0)
  · dsimp only at h hv
    cases hl : Runs.remove ctx.reverse l with
    | none => rw [hl] at h; contradiction
    | some l0 =>
      rw [hl] at h
      have hqe_spec:=qe_spec 32 sin r
      rcases hqe : qe 32 sin r with ⟨n,r0⟩
      rw [hqe] at h hqe_spec
      simp only [strictRuns_eq] at h
      injection h with hc'; subst hc'
      unfold RMConfig.denote
      dsimp only
      rw [Runs.push_spec,Runs.push_spec,Runs.remove_spec hl,hqe_spec]
      have hc1 : ctx.reverse ^ (1 : ℕ)=ctx.reverse:= by simp [pow_succ_list]
      rw [hc1]
      exact hv n (Runs.denote l0) (Runs.denote r0)
def qc (s : Scan) (keep : ℕ) (c : RMConfig) : Option RMConfig :=
  if keep == 0 then qc_zero s c
  else
    let z:=qk s.dir c
    let w:=match s.dir with | .left => s.scan_in.reverse | .right => s.scan_in
    let src:=match s.dir with | .left => z.left | .right => z.right
    q4 ((qe 32 w src).1 - keep) (fun n => use_scan s n c)
lemma q8 {tm : Machine (Fin 2) (Fin 6)} {s : Scan} {keep : ℕ} {c c' : RMConfig}
    (hv : q5 tm s) (h : qc s keep c=some c') :
    (c.denote) [tm]⊢* (c'.denote):= by
  unfold qc at h
  split_ifs at h with hk0
  · exact qc_zero_spec hv h
  · simp only [strictNat_eq] at h
    exact use_scan_spec hv h
lemma wall_1 : q2 target_tm E 1 1 W W:= by
  apply qG (w_mid:=[1,0,1,1,0,0,1,1,0,1])
  · intro l r; dsimp [W,ListBlank.append]; execute90
  · intro l r; dsimp [W,ListBlank.append]; execute90
lemma inc0 : q2 target_tm E 1 0 (qn .D0) (qn .D1):= by
  apply qj
  intro l r; dsimp [qn,ListBlank.append]; execute90
lemma inc1 : q2 target_tm E 1 0 (qn .D1 ++ W) (W ++ qn .D2):= by
  apply qj
  intro l r; dsimp [qn,W,ListBlank.append]; execute90
lemma inc2 : q2 target_tm E 1 0 (qn .D2) (qn .D3):= by
  apply qj
  intro l r; dsimp [qn,ListBlank.append]; execute90
lemma inc3 : q2 target_tm E 1 0 (qn .D3 ++ W) (W ++ qn .D4):= by
  apply qj
  intro l r; dsimp [qn,W,ListBlank.append]; execute90
lemma inc4 : q2 target_tm E 1 0 (qn .D4) (qn .D5):= by
  apply qj
  intro l r; dsimp [qn,ListBlank.append]; execute90
lemma inc5 : q2 target_tm E 1 1 (qn .D5) (W ++ qn .D0):= by
  apply qG (w_mid:=[1,0,1,1,0,1,1,0,1,1,0,1])
  · intro l r; dsimp [qn,W,ListBlank.append]; execute90
  · intro l r; dsimp [qn,W,ListBlank.append]; execute90
lemma one (p : Digit) (n : ℕ) :
    q2 target_tm E 1 (qL p)
      (qn p ++ W ^ (take p + n))
      (W ^ (give p) ++ qn (next p) ++ W ^ n):= by
  cases p
  · dsimp only [take,give,qL,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q6 inc0 (qg target_tm E (W ^ n))
  · dsimp only [take,give,qL,next]
    have h:=q6 inc1 (qg target_tm E (W ^ n))
    have h1 : 1 + n=n + 1:= by omega
    rw [h1,pow_succ_list,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
  · dsimp only [take,give,qL,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q6 inc2 (qg target_tm E (W ^ n))
  · dsimp only [take,give,qL,next]
    have h:=q6 inc3 (qg target_tm E (W ^ n))
    have h1 : 1 + n=n + 1:= by omega
    rw [h1,pow_succ_list,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
  · dsimp only [take,give,qL,next]
    simpa only [Nat.zero_add,pow_zero_list,List.nil_append] using
      q6 inc4 (qg target_tm E (W ^ n))
  · dsimp only [take,give,qL,next]
    have h:=q6 inc5 (wall_n wall_1 n)
    rw [Nat.zero_add,pow_succ_list,pow_zero_list,List.append_nil]
    simpa only [List.append_assoc] using h
lemma emit (r : ListBlank (Fin 2)) :
    (default <{{E}} ([1] +> r)) [target_tm]⊢* (([1,0,1] +> default) {{E}}> r):= by
  dsimp [ListBlank.append]; execute90
lemma batch_step (t : ℕ) (xs : qv) (e : ℕ) (ys : qv) (k : ℕ) (r : ListBlank (Fin 2))
    (h : qU t xs=some (e,ys)) :
    (([1,0,1] +> default) {{E}}> ((W ^ k) +> (q9 xs) +> r)) [target_tm]⊢*
    (([1,0,1] +> default) {{E}}> ((W ^ (k + e)) +> (q9 ys) +> r)) :=
  batch_root emit wall_1 one t xs e ys k r h
def scan_0 : Scan:=⟨A,.left,[1,0,1,1,0,0,1,1,0,1],[1,1,1,1,1,0,1,1,1,1],[0,1,0]⟩
lemma scan_0_valid : q5 target_tm scan_0:= by
  apply qf rfl
  intro l r; dsimp [scan_0,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_1 : Scan:=⟨E,.right,[1,0,1,1,1,1,1,1,1,1],[0,1,1,0,1,1,0,1,1,0],[1]⟩
lemma scan_1_valid : q5 target_tm scan_1:= by
  apply qo rfl
  intro l r; dsimp [scan_1,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_2 : Scan:=⟨C,.left,[1,1,0,1,1,0,0,1,1,0],[1,1,1,1,0,1,1,1,1,1],[0,1]⟩
lemma scan_2_valid : q5 target_tm scan_2:= by
  apply qf rfl
  intro l r; dsimp [scan_2,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_3 : Scan:=⟨E,.right,[1,1,1,1,0,1,1,1,1,1],[1,0,1,1,0,0,1,1,0,1],[1,0,1]⟩
lemma scan_3_valid : q5 target_tm scan_3:= by
  apply qo rfl
  intro l r; dsimp [scan_3,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_4 : Scan:=⟨E,.left,[1,1,0,1,1,0,0,1,1,0],[1,1,1,1,1,0,1,1,1,1],[1,1,1,0]⟩
lemma scan_4_valid : q5 target_tm scan_4:= by
  apply qf rfl
  intro l r; dsimp [scan_4,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_5 : Scan:=⟨A,.left,[1,0,1,1,0,1],[1,0,1,1,1,1],[0]⟩
lemma scan_5_valid : q5 target_tm scan_5:= by
  apply qf rfl
  intro l r; dsimp [scan_5,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_6 : Scan:=⟨C,.left,[1,1,0,1,1,0],[0,1,1,1,1,1],[]⟩
lemma scan_6_valid : q5 target_tm scan_6:= by
  apply qf rfl
  intro l r; dsimp [scan_6,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_7 : Scan:=⟨E,.left,[1,1,0,1,1,0],[1,1,1,0,1,1],[]⟩
lemma scan_7_valid : q5 target_tm scan_7:= by
  apply qf rfl
  intro l r; dsimp [scan_7,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_8 : Scan:=⟨A,.right,[1,1,1],[1,0,1],[1,0]⟩
lemma scan_8_valid : q5 target_tm scan_8:= by
  apply qo rfl
  intro l r; dsimp [scan_8,List.reverse,List.reverseAux,ListBlank.append]; execute90
def scan_9 : Scan:=⟨E,.right,[1,1,1],[1,0,1],[1,0,1]⟩
lemma scan_9_valid : q5 target_tm scan_9:= by
  apply qo rfl
  intro l r; dsimp [scan_9,List.reverse,List.reverseAux,ListBlank.append]; execute90
def run_raw (tm : Machine (Fin 2) (Fin 6)) : ℕ → RMConfig → Option RMConfig
  | 0,c => some c
  | n + 1,c =>
    match RM.raw tm c with
    | some c' => run_raw tm n c'
    | none => none
lemma run_raw_spec {n : ℕ} {c c' : RMConfig}
    (h : run_raw target_tm n c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold run_raw at h
    cases hr : RM.raw target_tm c with
    | none => rw [hr] at h; contradiction
    | some c₁ =>
      rw [hr] at h
      exact q0 (RM.raw_spec hr) (ih h)
def qs (op arg : ℕ) (c : RMConfig) : Option RMConfig :=
  match op with
  | 0 => run_raw target_tm arg c
  | 1 => qT E c
  | 2 => qc scan_0 arg c
  | 3 => qc scan_1 arg c
  | 4 => qc scan_2 arg c
  | 5 => qc scan_3 arg c
  | 6 => qc scan_4 arg c
  | 7 => qc scan_5 arg c
  | 8 => qc scan_6 arg c
  | 9 => qc scan_7 arg c
  | 10 => qc scan_8 arg c
  | 11 => qc scan_9 arg c
  | 12 => qa0 arg c
  | _ => none
lemma qp {op arg : ℕ} {c c' : RMConfig}
    (h : qs op arg c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  unfold qs at h
  rcases op with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | op
  · exact run_raw_spec h
  · exact qV batch_step h
  · exact q8 scan_0_valid h
  · exact q8 scan_1_valid h
  · exact q8 scan_2_valid h
  · exact q8 scan_3_valid h
  · exact q8 scan_4_valid h
  · exact q8 scan_5_valid h
  · exact q8 scan_6_valid h
  · exact q8 scan_7_valid h
  · exact q8 scan_8_valid h
  · exact q8 scan_9_valid h
  · exact qa3 batch_step h
  · contradiction
def qO : ℕ → ℕ → ℕ → RMConfig → Option RMConfig
  | 0,_,_,c => some c
  | n + 1,op,arg,c =>
    match qs op arg c with
    | some c' => qO n op arg c'
    | none => none
lemma run_rep1_spec {n op arg : ℕ} {c c' : RMConfig}
    (h : qO n op arg c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold qO at h
    cases ho : qs op arg c with
    | none => rw [ho] at h; contradiction
    | some c₁ =>
      rw [ho] at h
      exact q0 (qp ho) (ih h)
def qN : ℕ → ℕ → ℕ → ℕ → ℕ → RMConfig → Option RMConfig
  | 0,_,_,_,_,c => some c
  | n + 1,op1,arg1,op2,arg2,c =>
    match qs op1 arg1 c with
    | some c₁ =>
      match qs op2 arg2 c₁ with
      | some c₂ => qN n op1 arg1 op2 arg2 c₂
      | none => none
    | none => none
lemma run_rep2_spec {n op1 arg1 op2 arg2 : ℕ} {c c' : RMConfig}
    (h : qN n op1 arg1 op2 arg2 c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  induction n generalizing c with
  | zero =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | succ n ih =>
    unfold qN at h
    cases ho1 : qs op1 arg1 c with
    | none => rw [ho1] at h; contradiction
    | some c₁ =>
      rw [ho1] at h; dsimp only at h
      cases ho2 : qs op2 arg2 c₁ with
      | none => rw [ho2] at h; contradiction
      | some c₂ =>
        rw [ho2] at h; dsimp only at h
        exact q0 (qp ho1) (q0 (qp ho2) (ih h))
inductive Cmd where
  | one (op arg : ℕ)
  | rep1 (cnt op arg : ℕ)
  | rep2 (cnt op1 arg1 op2 arg2 : ℕ)
def exec_cmd (cmd : Cmd) (c : RMConfig) : Option RMConfig :=
  match cmd with
  | .one op arg => qs op arg c
  | .rep1 cnt op arg => qO cnt op arg c
  | .rep2 cnt op1 arg1 op2 arg2 => qN cnt op1 arg1 op2 arg2 c
lemma exec_cmd_spec {cmd : Cmd} {c c' : RMConfig}
    (h : exec_cmd cmd c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  cases cmd with
  | one op arg => exact qp h
  | rep1 cnt op arg => exact run_rep1_spec h
  | rep2 cnt op1 arg1 op2 arg2 => exact run_rep2_spec h
def q7 : List Cmd → RMConfig → Option RMConfig
  | [],c => some c
  | cmd :: rest,c =>
    match exec_cmd cmd c with
    | some c' => q7 rest c'
    | none => none
lemma q1 {cs : List Cmd} {c c' : RMConfig}
    (h : q7 cs c=some c') :
    (c.denote) [target_tm]⊢* (c'.denote):= by
  induction cs generalizing c with
  | nil =>
    injection h with heq; subst heq; exact ⟨0,rfl⟩
  | cons cmd rest ih =>
    unfold q7 at h
    cases hc : exec_cmd cmd c with
    | none => rw [hc] at h; contradiction
    | some c₁ =>
      rw [hc] at h; dsimp only at h
      exact q0 (exec_cmd_spec hc) (ih h)
def isHalted (tm : Machine (Fin 2) (Fin 6)) (c : RMConfig) : Bool :=
  let b:=match c.dir with
    | .left => (Runs.pop c.left).1
    | .right => (Runs.pop c.right).1
  (tm c.state b).isNone
lemma isHalted_spec {c : RMConfig} (h : isHalted target_tm c=true) :
    (step target_tm c.denote).isNone:= by
  rcases c with ⟨l,r,q,d⟩
  unfold isHalted at h
  cases d
  · dsimp only at h
    unfold RMConfig.denote step
    dsimp only
    rw [Runs.pop_spec l,Turing.ListBlank.head_cons]
    cases htm : target_tm q (Runs.pop l).1 with
    | none => rfl
    | some _ => rw [htm] at h; contradiction
  · dsimp only at h
    unfold RMConfig.denote step
    dsimp only
    rw [Runs.pop_spec r,Turing.ListBlank.head_cons]
    cases htm : target_tm q (Runs.pop r).1 with
    | none => rfl
    | some _ => rw [htm] at h; contradiction
def cfg_0 : RMConfig:=⟨[],[],A,.right⟩
def cfg_1 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],14),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8),([1],3)],E,.right⟩
def cfg_2 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],241),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],53),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5),([1],3)],E,.right⟩
def cfg_3 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],1729),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],782),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],210),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],16),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13),([1],3)],E,.right⟩
def cfg_4 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],3887),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6022),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8174),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5646),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],605),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],51),([1],3)],E,.right⟩
def cfg_5 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],139967),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],226237),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],26610),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],34796),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4289),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4998),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],497),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],27),([1],3)],E,.right⟩
def cfg_6 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],1632251),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11843205),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],797367),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],181662),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8805),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4241),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],371),([1,1,1,1,1,1,1,1],1)],E,.right⟩
def cfg_7 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],4572289),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],590979),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1072378),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11749893),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],781815),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],179070),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8373),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4169),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],356),([1],3)],E,.right⟩
def cfg_8 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],30233087),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1945900),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],67310045),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2861710),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],232570),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11609925),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],758487),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],175182),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7725),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4061),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],332),([1],3)],E,.right⟩
def cfg_9 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],2295683953),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],202569288),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],241946316),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],54454285),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],719083),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11446630),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],731271),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],170646),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6969),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3935),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],304),([1],3)],E,.right⟩
def cfg_10 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],433652009),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],16189663086),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1363751089),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],47247144),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],216059292),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],50139781),([1,1,1,1],2),([1,1,1,1,0,1,1,1,1,1],11326784),([0,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],711297),([0,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],167317),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6414),([1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3843),([1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],284),([1],3)],E,.right⟩
def cfg_11 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],14279327156),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],12993403879),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15126217323),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1186510129),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],17706984),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],211135932),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],49319221),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11190023),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],688503),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],163518),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5781),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3737),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],260),([1],3)],E,.right⟩
def cfg_12 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],39182082047),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],63568800907),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],85467965436),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],41668468650),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8717755377),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14413609239),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1067742115),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],206097084),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],48479413),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11050055),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],665175),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],159630),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5133),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3629),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],236),([1],3)],E,.right⟩
def cfg_13 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],947788796189),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3338260719276),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],80777430892),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],49551056890),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],35682317226),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7720063473),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14247327255),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1040028451),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],201478140),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],47709589),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10921751),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],643791),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],156066),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4539),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3530),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],214),([1],3)],E,.right⟩
def cfg_14 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],8463329722367),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15015622214732),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],11794710009590),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],566880020609),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2699281072528),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10368974843),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],29151970218),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],6631672305),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14065928727),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1009795363),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],196439292),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],46869781),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10781783),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],620463),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],152178),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3891),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3422),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],190),([1],3)],E,.right⟩
def cfg_15 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],643687451900791),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],421120352273026),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],16167460699058),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2118173193801),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8517739583725),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],20718282965),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2608254116254),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],22621623209),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5543281137),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13884530199),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],979562275),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],191400444),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],46029973),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10641815),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],597135),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],148290),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3243),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3314),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],166),([1],3)],E,.right⟩
def cfg_16 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],4466942543772001),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2775521742390931),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3245935587750055),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],185028888216425),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],344677258325632),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3426945041159),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],8159464635577),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2565806860701),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],15547080617),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],4364190705),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13688015127),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],946809763),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],185941692),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],45120181),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10490183),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],571863),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],144078),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2541),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3197),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],140),([1],3)],E,.right⟩
def cfg_17 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],10968475320188927),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],22072363915935747),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],21900271405424549),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1099782457362068),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2966645706911911),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],138480574743401),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],336919206080128),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2133936333575),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7943963184313),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2529889952157),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9560929193),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3366498801),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13521733143),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],919096099),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],181322748),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],44350357),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10361879),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],550479),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],140514),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1947),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3098),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],118),([1],3)],E,.right⟩
def cfg_18 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],147962543465675451),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],35529259535392476),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],143551584287734354),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],14725619833585334),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2687355826073766),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],91932261270377),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],329161153834624),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],840927625991),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7728461733049),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2493973043613),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],3574777769),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2368806897),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13355451159),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],891382435),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],176703804),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],43580533),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10233575),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],529095),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136950),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1353),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2999),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],96),([1],3)],E,.right⟩
def cfg_19 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],36514618862704129),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],46569173798179584),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],806290250466731119),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],603374972797170723),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136963769242827634),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13627650659434214),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2504360963715246),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],61433117543957),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],324077963213554),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7582036317864),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2469568807749),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1280415728),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13174052631),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],861149347),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],171664956),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],42740725),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],10093607),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],505767),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],133062),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],705),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2891),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],72),([1],3)],E,.right⟩
def cfg_20 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],144515463148616111),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1763371228290069298),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],54106918031395816),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],744645192201139930),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],794196152293467251),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],601359289768293411),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136627822071348082),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13571659464187622),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2495029097840814),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],59877806564885),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],323818744717042),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7538833235112),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2462368293957),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],80330096),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],12974038359),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],827813635),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],166109004),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],41814733),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9939275),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],480045),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],128775),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2765),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],44),([1],3)],E,.right⟩
def cfg_21 : RMConfig:=⟨[([1],1),([0],1),([1],1)],[([1,1,1,1,0,1,1,1,1,1],394865111526801407),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],5571086799836381189),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],294919453089922226),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],1562811241455326001),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],20680253558938600),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],739074081455730394),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],793267633835898995),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],601204536692032035),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],136602029891971186),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],13567360767624806),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2494312648413678),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],59758398327029),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],323798843344066),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],7535516339616),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2461815478041),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],12948844121),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],823614595),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],165409164),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],41698093),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],9919835),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],476805),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],128235),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],2675),([1,1,1,1,1,1,1,1,1,1,1,1],1),([1,1,1,1,0,1,1,1,1,1],24),([1],3)],E,.right⟩
def cfg_22 : RMConfig:=⟨[([0,1,1,0,1,1,0,1,1,0],2562),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],127559),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],472754),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],9895534),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],41552292),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],164534363),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],818365794),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],12917351320),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],2461626521240),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],7534382598815),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],323792040899265),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],59717583658228),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],2494067760400877),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],13565891439548005),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],136593213923510385),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],601151640881267234),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],792950258971310194),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],737169832268197593),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],9254758433741799),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],1494258270704145199),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],3685171709879685247),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],34617925443173174206),([0,1],1),([1,0,1],4),([1,0,1,1,0,1,1,0],1),([0,1,1,0,1,1,0,1,1,0],378258698465341521),([0,1],1),([1,0,1],5),([1,0,1,1,0,0,1,1,0,1],5133246449848418304),([1],1),([0],1),([1],2),([0],2),([1],2),([0],1),([1],1)],[([1],2),([0],1),([1],5),([0],1),([1],4)],F,.left⟩
def cmds_0 : List Cmd:=[.one 0 72,.one 1 0,.one 0 112,.one 1 0,.one 0 139,.one 1 0,.one 1 0,.one 0 35,.one 10 0,.one 0 97,.one 1 0,.one 1 0,.one 0 56,.one 10 0,.one 0 2,.one 8 0,.one 0 121,.one 1 0,.one 1 0,.one 0 56,.one 10 0,.one 0 89,.one 7 0,.one 0 145,.one 1 0,.one 1 0,.one 5 0,.one 11 0,.one 0 16,.one 8 0,.one 0 299,.one 1 0,.one 1 0,.one 5 0,.one 0 46,.one 8 0,.one 0 259,.one 1 0,.one 1 0,.one 0 56,.one 10 0,.one 0 1,.one 3 0,.one 0 26,.one 4 0,.one 0 163,.one 1 0,.one 1 0,.one 5 0,.one 11 0,.one 0 155,.one 7 0,.one 0 265,.one 1 0,.one 1 0,.one 12 4,.one 5 0,.one 11 0,.one 0 16,.one 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 5 0,.one 0 46,.one 8 0,.one 0 40,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 0 56,.one 10 0,.one 0 1,.one 3 0,.one 0 26,.one 4 0,.one 0 163,.one 1 0,.one 1 0,.one 5 0,.one 11 0,.one 3 0,.one 0 7,.one 2 0,.one 0 281,.one 1 0,.one 1 0,.one 12 4]
set_option maxHeartbeats 8000000 in
lemma chunk_0_ok : q7 cmds_0 cfg_0=some cfg_1:= by decide +kernel
def cmds_1 : List Cmd:=[.one 5 0,.one 11 0,.one 3 0,.one 0 7,.one 2 0,.one 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 2 11 0 3 0,.one 0 7,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 12 8,.one 1 0,.one 5 0,.one 11 0,.one 3 0,.one 0 7,.one 2 0,.one 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 2 11 0 3 0,.one 0 7,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 12 8,.one 5 0,.one 11 0,.one 3 0,.one 11 0,.one 0 73,.one 7 0,.one 2 0,.one 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 2 11 0 3 0,.one 0 46,.one 8 0,.rep2 2 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 12 1,.one 1 0,.one 5 0,.one 11 0,.one 3 0,.one 0 31,.one 8 0,.one 0 40,.one 2 0,.one 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 2 11 0 3 0,.one 0 26,.rep2 2 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 5 0,.rep2 2 11 0 3 0,.one 0 7,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 12 8,.one 5 0,.rep2 2 11 0 3 0,.one 0 7,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 3 11 0 3 0,.one 0 7,.rep2 3 2 0 7 0,.one 2 0,.one 0 35,.one 12 13]
set_option maxHeartbeats 8000000 in
lemma chunk_1_ok : q7 cmds_1 cfg_1=some cfg_2:= by decide +kernel
def cmds_2 : List Cmd:=[.one 5 0,.rep2 2 11 0 3 0,.one 0 7,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 3 11 0 3 0,.one 0 7,.rep2 3 2 0 7 0,.one 2 0,.one 0 35,.one 12 9,.one 5 0,.rep2 2 11 0 3 0,.one 11 0,.one 0 73,.one 7 0,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 3 11 0 3 0,.one 0 46,.one 8 0,.rep2 3 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 12 4,.one 5 0,.rep2 2 11 0 3 0,.one 0 31,.one 8 0,.one 0 40,.rep2 2 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 3 11 0 3 0,.one 0 26,.rep2 3 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 5 0,.rep2 3 11 0 3 0,.one 0 7,.rep2 3 2 0 7 0,.one 2 0,.one 0 35,.one 12 10,.one 5 0,.rep2 3 11 0 3 0,.one 0 7,.rep2 3 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 15,.one 5 0,.rep2 3 11 0 3 0,.one 0 7,.rep2 3 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 10]
set_option maxHeartbeats 8000000 in
lemma chunk_2_ok : q7 cmds_2 cfg_2=some cfg_3:= by decide +kernel
def cmds_3 : List Cmd:=[.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 8,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 6,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 17,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 4 11 0 3 0,.one 11 0,.one 0 73,.one 7 0,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 12 10,.one 5 0,.rep2 4 11 0 3 0,.one 0 46,.one 8 0,.rep2 4 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 12 1,.one 5 0,.rep2 4 11 0 3 0,.one 0 31,.one 8 0,.one 0 40,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 12 5,.one 5 0,.rep2 4 11 0 3 0,.one 0 26,.rep2 4 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 16,.one 5 0,.rep2 4 11 0 3 0,.one 0 7,.rep2 4 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_3_ok : q7 cmds_3 cfg_3=some cfg_4:= by decide +kernel
def cmds_4 : List Cmd:=[.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 12,.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 10,.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 7,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 20,.one 5 0,.rep2 5 11 0 3 0,.one 0 7,.rep2 5 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 13,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 8,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 20,.one 5 0,.rep2 6 11 0 3 0,.one 0 7,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_4_ok : q7 cmds_4 cfg_4=some cfg_5:= by decide +kernel
def cmds_5 : List Cmd:=[.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 12,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 10,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 15,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 23,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 16,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 30,.one 5 0,.rep2 7 11 0 3 0,.one 11 0,.one 0 73,.one 7 0,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 12 14,.one 5 0,.rep2 6 11 0 3 0,.one 0 46,.one 8 0,.rep2 6 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0]
set_option maxHeartbeats 8000000 in
lemma chunk_5_ok : q7 cmds_5 cfg_5=some cfg_6:= by decide +kernel
def cmds_6 : List Cmd:=[.one 5 0,.rep2 6 11 0 3 0,.one 0 31,.one 8 0,.one 0 40,.rep2 6 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 7 11 0 3 0,.one 0 26,.rep2 7 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 15,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 7 11 0 3 0,.one 0 7,.rep2 7 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 16,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 14]
set_option maxHeartbeats 8000000 in
lemma chunk_6_ok : q7 cmds_6 cfg_6=some cfg_7:= by decide +kernel
def cmds_7 : List Cmd:=[.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 28,.one 5 0,.rep2 8 11 0 3 0,.one 0 7,.rep2 8 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 17,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 15,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 12,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 9 11 0 3 0,.one 0 7,.rep2 9 2 0 7 0,.one 2 0,.one 0 35,.one 12 3]
set_option maxHeartbeats 8000000 in
lemma chunk_7_ok : q7 cmds_7 cfg_7=some cfg_8:= by decide +kernel
def cmds_8 : List Cmd:=[.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 13,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 16,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 10,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 17,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 45]
set_option maxHeartbeats 8000000 in
lemma chunk_8_ok : q7 cmds_8 cfg_8=some cfg_9:= by decide +kernel
def cmds_9 : List Cmd:=[.one 5 0,.rep2 10 11 0 3 0,.one 0 7,.rep2 10 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 17,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 37,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 41,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 1 0]
set_option maxHeartbeats 8000000 in
lemma chunk_9_ok : q7 cmds_9 cfg_9=some cfg_10:= by decide +kernel
def cmds_10 : List Cmd:=[.one 1 0,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 4,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 17,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 38,.one 5 0,.rep2 11 11 0 3 0,.one 0 7,.rep2 11 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 40,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 18,.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 37]
set_option maxHeartbeats 8000000 in
lemma chunk_10_ok : q7 cmds_10 cfg_10=some cfg_11:= by decide +kernel
def cmds_11 : List Cmd:=[.one 5 0,.rep2 12 11 0 3 0,.one 0 7,.rep2 12 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 22,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 20,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 37,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 25,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 22,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 39,.one 5 0,.rep2 13 11 0 3 0,.one 0 7,.rep2 13 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_11_ok : q7 cmds_11 cfg_11=some cfg_12:= by decide +kernel
def cmds_12 : List Cmd:=[.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 23,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 43,.one 5 0,.rep2 14 11 0 3 0,.one 0 7,.rep2 14 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 25,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 20,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 5,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 18,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 48,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 23]
set_option maxHeartbeats 8000000 in
lemma chunk_12_ok : q7 cmds_12 cfg_12=some cfg_13:= by decide +kernel
def cmds_13 : List Cmd:=[.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 43,.one 5 0,.rep2 15 11 0 3 0,.one 0 7,.rep2 15 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 19,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 17 11 0 3 0,.one 0 7,.rep2 17 2 0 7 0,.one 2 0,.one 0 35,.one 12 44,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 23,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 17 11 0 3 0,.one 0 7,.rep2 17 2 0 7 0,.one 2 0,.one 0 35,.one 12 48,.one 5 0,.rep2 16 11 0 3 0,.one 0 7,.rep2 16 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_13_ok : q7 cmds_13 cfg_13=some cfg_14:= by decide +kernel
def cmds_14 : List Cmd:=[.one 5 0,.rep2 17 11 0 3 0,.one 0 7,.rep2 17 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 17 11 0 3 0,.one 0 7,.rep2 17 2 0 7 0,.one 2 0,.one 0 35,.one 12 25,.one 5 0,.rep2 17 11 0 3 0,.one 0 7,.rep2 17 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 25,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 24,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 26,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 50,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 49]
set_option maxHeartbeats 8000000 in
lemma chunk_14_ok : q7 cmds_14 cfg_14=some cfg_15:= by decide +kernel
def cmds_15 : List Cmd:=[.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 4,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 20,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 56,.one 5 0,.rep2 18 11 0 3 0,.one 0 7,.rep2 18 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 30,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 28,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 58,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 56,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 51]
set_option maxHeartbeats 8000000 in
lemma chunk_15_ok : q7 cmds_15 cfg_15=some cfg_16:= by decide +kernel
def cmds_16 : List Cmd:=[.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 31,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 29,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 84,.one 5 0,.rep2 19 11 0 3 0,.one 0 7,.rep2 19 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 31,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 29,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 60,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_16_ok : q7 cmds_16 cfg_16=some cfg_17:= by decide +kernel
def cmds_17 : List Cmd:=[.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 30,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 64,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 31,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 33,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 27,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 33,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 63]
set_option maxHeartbeats 8000000 in
lemma chunk_17_ok : q7 cmds_17 cfg_17=some cfg_18:= by decide +kernel
def cmds_18 : List Cmd:=[.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 63,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 105,.one 5 0,.rep2 20 11 0 3 0,.one 0 7,.rep2 20 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 30,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 21,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 33]
set_option maxHeartbeats 8000000 in
lemma chunk_18_ok : q7 cmds_18 cfg_18=some cfg_19:= by decide +kernel
def cmds_19 : List Cmd:=[.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 29,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 59,.one 5 0,.rep2 21 11 0 3 0,.one 0 7,.rep2 21 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 32,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 66,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 28,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 3,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 30,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 33,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 28]
set_option maxHeartbeats 8000000 in
lemma chunk_19_ok : q7 cmds_19 cfg_19=some cfg_20:= by decide +kernel
def cmds_20 : List Cmd:=[.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 65,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 35,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 14,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 36,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 24 11 0 3 0,.one 0 7,.rep2 24 2 0 7 0,.one 2 0,.one 0 35,.one 12 95,.one 5 0,.rep2 22 11 0 3 0,.one 0 7,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 12 2]
set_option maxHeartbeats 8000000 in
lemma chunk_20_ok : q7 cmds_20 cfg_20=some cfg_21:= by decide +kernel
def cmds_21 : List Cmd:=[.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 35,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 33,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 24 11 0 3 0,.one 0 7,.rep2 24 2 0 7 0,.one 2 0,.one 0 35,.one 12 68,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 24 11 0 3 0,.one 0 7,.rep2 24 2 0 7 0,.one 2 0,.one 0 35,.one 12 36,.one 5 0,.rep2 24 11 0 3 0,.one 0 7,.rep2 24 2 0 7 0,.one 2 0,.one 0 35,.one 12 34,.one 5 0,.rep2 24 11 0 3 0,.one 0 7,.rep2 24 2 0 7 0,.one 2 0,.one 0 35,.one 12 2,.one 5 0,.rep2 25 11 0 3 0,.one 0 7,.rep2 25 2 0 7 0,.one 2 0,.one 0 35,.one 12 100,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 31,.one 5 0,.rep2 23 11 0 3 0,.one 0 7,.rep2 23 2 0 7 0,.one 2 0,.one 0 35,.one 12 35,.one 5 0,.rep2 22 11 0 3 0,.one 11 0,.one 0 155,.one 7 0,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 5 0,.rep2 23 11 0 3 0,.one 11 0,.one 0 2,.one 9 0,.one 6 0,.one 0 13,.rep2 22 2 0 7 0,.one 2 0,.one 0 35,.one 1 0,.one 1 0,.one 12 31,.one 1 0,.one 1 0,.one 5 0,.rep2 23 11 0 3 0,.one 0 66,.rep2 23 4 0 8 0,.one 4 0,.one 0 71,.one 1 0,.one 1 0,.one 0 36,.one 5 0,.rep2 23 11 0 3 0,.one 0 72]
set_option maxHeartbeats 8000000 in
lemma chunk_21_ok : q7 cmds_21 cfg_21=some cfg_22:= by decide +kernel
lemma halted_final : isHalted target_tm cfg_22=true:= by decide +kernel
lemma init_eq_cfg_0 : cfg_0.denote=init []:=rfl

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

end BusyBeaver.M_1RB1RE_1RC1LE_1LD0RA_1LF0LA_1LB0LC_HHH1RA
