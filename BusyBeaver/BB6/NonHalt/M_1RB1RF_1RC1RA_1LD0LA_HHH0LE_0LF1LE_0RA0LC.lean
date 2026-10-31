/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_1RC1RA_1LD0LA_---0LE_0LF1LE_0RA0LC` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1RC1RA_1LD0LA_---0LE_0LF1LE_0RA0LC`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1RC1RA_1LD0LA_HHH0LE_0LF1LE_0RA0LC

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1RC1RA_1LD0LA_---0LE_0LF1LE_0RA0LC`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option autoImplicit true
set_option linter.unusedSimpArgs false


def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
abbrev gQ:=Fin 2
abbrev ai:=ListBlank (Fin 2)
abbrev aL:=Cfg (Fin 2) (Fin 6)
def sA : Fin 6:=B
def sB : Fin 6:=C
def sC : Fin 6:=D
def sD : Fin 6:=E
def sE : Fin 6:=F
def sF : Fin 6:=A
abbrev tm:=target_tm
@[simp] lemma sr (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config:=rfl
@[simp] lemma n9 (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config:=rfl
@[simp] lemma sn (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep,Function.iterate_succ',Function.comp_apply,multiStep]
lemma qO {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [M]⊢ c₂) :
    c₁ [M]⊢^{1} c₂ := by simp [h]
lemma qC {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m:Nat) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ,sn,ih,Option.bind_assoc]
    simp_rw [sn]
lemma qT {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Cfg Γ Λ) (n:Nat) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  rw [Nat.add_comm n 1,qC,n9]
lemma qH {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m:Nat)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n + m} c₃ := by
  rw [qC,h₁]; simp [h₂]
lemma mm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} (c : Cfg Γ Λ) : c [M]⊢* c:=⟨0,rfl⟩
lemma ss {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢* c₃ := by
  rcases h₁ with ⟨n,hn⟩; rcases h₂ with ⟨m,hm⟩
  exact ⟨n + m,qH M c₁ c₂ c₃ n m hn hm⟩
lemma V {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [M]⊢⁺ c₂) :
    c₁ [M]⊢* c₂ := by rcases h with ⟨n,_,hn⟩; exact ⟨n,hn⟩
lemma ee {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n,hn_pos,hn⟩; rcases h₂ with ⟨m,hm⟩
  exact ⟨n + m,by omega,qH M c₁ c₂ c₃ n m hn hm⟩
lemma kT {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n,hn⟩; rcases h₂ with ⟨m,hm_pos,hm⟩
  exact ⟨n + m,by omega,qH M c₁ c₂ c₃ n m hn hm⟩
lemma sq {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  ee h₁ (V h₂)
@[simp] lemma oR : (0 : Fin 2)>>default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma kX : (default : ListBlank (Fin 2)).head = 0:=rfl
@[simp] lemma k5 : (default : ListBlank (Fin 2)).tail = default:=rfl
@[simp] lemma append_nil (s : ListBlank (Fin 2)) : ([] : List (Fin 2))+>s = s:=rfl
@[simp] lemma append_cons (a : Fin 2) (l : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (a :: l)+>s = a>>(l+>s):=rfl
@[simp] lemma append_assoc (l1 l2 : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (l1++l2)+>s = l1+>(l2+>s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp [ih]
lemma qZ {w : List (Fin 2)} (h : BusyBeaver.Longitudinal.BoundedConfig.all0 w = true) :
    w+>default = default :=
  BusyBeaver.Longitudinal.BoundedConfig.all0_spec h
lemma x3 (b : Fin 2) : b = 0∨b = 1 := by
  rcases b with ⟨_ | ⟨_ | n⟩,hlt⟩
  · left; rfl
  · right; rfl
  · omega
lemma dW (r:ai) : (∃ r',r = [0]+>r')∨(∃ r',r = [1]+>r') := by
  have h : r.head>>r.tail = r:=Turing.ListBlank.cons_head_tail r
  rcases x3 r.head with h0 | h1
  · left; refine ⟨r.tail,?_⟩; rw [append_cons,append_nil,← h0,h]
  · right; refine ⟨r.tail,?_⟩; rw [append_cons,append_nil,← h1,h]
def bf (l:ai) (w : List gQ) : ai:=w.reverse+>l
def FR (l r:ai) : aL:=l {{sF}}> r
def DL (l r:ai) : aL:=l <{{sD}} r
def FL (l r:ai) : aL:=l <{{sF}} r
def BL (l r:ai) : aL:=l <{{sB}} r
def CE (r:ai) : aL:=default {{sE}}> ([0,0]+>r)
def wL : List gQ:=[1,1,0]
def wX : List gQ:=[1,1,0,1,1,0]
def wY : List gQ:=[1,1,1,1]
def wa : List gQ:=[1,1,1,0,1,0]
def wb : List gQ:=[1,0,1,0]
@[simp] lemma Hw (l:ai) : bf l [] = l:=rfl
lemma df (l:ai) (u v : List gQ) : bf l (u++v) = bf (bf l u) v := by
  simp [bf,List.reverse_append,append_assoc]
structure pv where
  past : List gQ
  front : List gQ
  state : Fin 6
  left_head : Bool
deriving DecidableEq
def pv.toBC (x:pv) : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6) :=
  match x.left_head with
  | true => ⟨x.front, x.past, x.state, .left⟩
  | false => ⟨x.past, x.front, x.state, .right⟩
def pv.ofBC (x : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6)) : pv :=
  match x.sgn with
  | .left => ⟨x.r, x.l, x.s, true⟩
  | .right => ⟨x.l, x.r, x.s, false⟩
lemma pv_toBC_ofBC (x : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6)) :
    (pv.ofBC x).toBC = x := by
  rcases x with ⟨l, r, s, _ | _⟩ <;> rfl
def go (x:pv) (l r:ai) : aL :=
  BusyBeaver.Longitudinal.BoundedConfig.toCfg x.toBC l r
def qj (x:pv) : Option pv :=
  (BusyBeaver.Longitudinal.BoundedConfig.step tm x.toBC).map pv.ofBC
lemma yc {x y : pv} (h : qj x = some y) (l r:ai) :
    (go x l r) [tm]⊢ (go y l r) := by
  rcases Option.map_eq_some_iff.mp h with ⟨b, hb, rfl⟩
  simpa only [go, pv_toBC_ofBC] using
    BusyBeaver.Longitudinal.BoundedConfig.step_spec tm x.toBC hb l r
def wd : Nat→pv→Option pv
  | 0,x => some x
  | n + 1,x =>
    match qj x with
    | none => none
    | some z => wd n z
lemma yP {n : Nat} {x y : pv} (h : wd n x = some y) (l r:ai) :
    (go x l r) [tm]⊢^{n} (go y l r) := by
  induction n generalizing x with
  | zero => injection h with hy; subst hy; rfl
  | succ n ih =>
    unfold wd at h
    rcases hs : qj x with _ | z
    · rw [hs] at h; contradiction
    · rw [hs] at h
      rw [Nat.add_comm n 1]
      exact qH tm _ _ _ 1 n (qO tm _ _ (yc hs l r)) (ih h)
lemma U (n:Nat) (x y:pv) (h : wd (n + 1) x = some y) (l r:ai) :
    (go x l r) [tm]⊢⁺ (go y l r) :=
  ⟨n + 1,Nat.succ_pos n,yP h l r⟩
lemma r2 (l r:ai) : (FR l ([0,0,0]+>r)) [tm]⊢⁺ (DL l ([1,0,1]+>r)) :=
  U 4 ⟨[],[0,0,0],sF,false⟩ ⟨[],[1,0,1],sD,true⟩ (by decide) l r
lemma r4 (l r:ai) : (FR l ([0,0,1]+>r)) [tm]⊢⁺ (FR (bf l wL) r) :=
  U 4 ⟨[],[0,0,1],sF,false⟩ ⟨wL.reverse,[],sF,false⟩ (by decide) l r
lemma xH (l r:ai) : (FR l ([0,1]+>r)) [tm]⊢⁺ (FR (bf l [1,1]) r) :=
  U 1 ⟨[],[0,1],sF,false⟩ ⟨[1,1],[],sF,false⟩ (by decide) l r
lemma vf (l r:ai) : (FR l ([1,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) r) :=
  U 1 ⟨[],[1,0],sF,false⟩ ⟨[0,1],[],sF,false⟩ (by decide) l r
lemma vv (l r:ai) : (FR l ([1,1]+>r)) [tm]⊢⁺ (FL l ([0,0]+>r)) :=
  U 2 ⟨[],[1,1],sF,false⟩ ⟨[],[0,0],sF,true⟩ (by decide) l r
lemma Av (l r:ai) : (DL (bf l [1]) r) [tm]⊢⁺ (DL l ([1]+>r)) :=
  U 0 ⟨[1],[],sD,true⟩ ⟨[],[1],sD,true⟩ (by decide) l r
lemma xL (l r:ai) : (DL (bf l [1,0]) r) [tm]⊢⁺ (BL l ([0,0]+>r)) :=
  U 1 ⟨[0,1],[],sD,true⟩ ⟨[],[0,0],sB,true⟩ (by decide) l r
lemma EJ (l r:ai) : (BL (bf l [1]) ([0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>r)) :=
  U 0 ⟨[1],[0,0],sB,true⟩ ⟨[],[0,0,0],sF,true⟩ (by decide) l r
lemma xV (l r:ai) : (BL (bf l [1,0]) ([0,0]+>r)) [tm]⊢⁺ (DL l ([0,1,0,0]+>r)) :=
  U 1 ⟨[0,1],[0,0],sB,true⟩ ⟨[],[0,1,0,0],sD,true⟩ (by decide) l r
lemma E6 (l r:ai) : (FL (bf l [1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) ([0]+>r)) :=
  U 1 ⟨[1],[0,0],sF,true⟩ ⟨[0,1],[0],sF,false⟩ (by decide) l r
lemma xZ (l r:ai) : (FL (bf l [1,0]) ([0,0]+>r)) [tm]⊢⁺ (DL (bf l [1]) ([1,0,1]+>r)) :=
  U 4 ⟨[0,1],[0,0],sF,true⟩ ⟨[1],[1,0,1],sD,true⟩ (by decide) l r
abbrev d7 (c:aL) (n:Nat) : Prop :=
  BusyBeaver.Excursion.HaltsIn tm c n
abbrev cE (c:aL) (P : aL→Prop) : Prop :=
  BusyBeaver.Excursion.Leads tm c P
abbrev fl (c:aL) (P : aL→Prop) : Prop :=
  BusyBeaver.Excursion.Advances tm c P
lemma uM {c d : aL} {n : Nat} (hr : c [tm]⊢* d) (hh : d7 c n) :
    ∃ m ≤ n,d7 d m :=
  BusyBeaver.Excursion.haltsIn_reduce_stepStar hr hh
lemma kz {c d : aL} {n : Nat} (hr : c [tm]⊢⁺ d) (hh : d7 c n) :
    ∃ m < n,d7 d m :=
  BusyBeaver.Excursion.haltsIn_reduce_stepPlus hr hh
lemma dg {c : aL} {P : aL→Prop} (hp : P c) : cE c P :=
  BusyBeaver.Excursion.Leads.here hp
lemma bn {c d : aL} {P : aL→Prop} (hr : c [tm]⊢* d) (hp : P d) : cE c P :=
  BusyBeaver.Excursion.Leads.of_stepStar hr hp
lemma bh {c : aL} {P Q : aL→Prop} (h1 : cE c P) (h2 : ∀ d,P d→cE d Q) :
    cE c Q :=
  BusyBeaver.Excursion.Leads.trans h1 h2
lemma x7 {c : aL} {P Q : aL→Prop} (h : cE c P) (hinc : ∀ d,P d→Q d) :
    cE c Q :=
  BusyBeaver.Excursion.Leads.mono h hinc
lemma yb {c : aL} {P : aL→Prop} (h : fl c P) : cE c P :=
  BusyBeaver.Excursion.Advances.to_leads h
lemma cr {c d : aL} {P : aL→Prop} (hr : c [tm]⊢⁺ d) (h : cE d P) :
    fl c P :=
  BusyBeaver.Excursion.Advances.of_stepPlus_leads hr h
lemma cc {c d : aL} {P : aL→Prop} (hr : c [tm]⊢⁺ d) (h : cE d P) :
    cE c P :=
  BusyBeaver.Excursion.Leads.of_stepPlus_leads hr h
lemma sv {c : aL} {P Q : aL→Prop} (h1 : fl c P) (h2 : ∀ d,P d→cE d Q) :
    fl c Q :=
  BusyBeaver.Excursion.Advances.trans h1 h2
lemma q3 {P : aL→Prop} (h : ∀ c,P c→fl c P) :
    ∀ n c,P c→¬ d7 c n :=
  BusyBeaver.Excursion.not_haltsIn_of_advances h
inductive BA where
  | GoRight | FromD | FromF | FromB
def se (b:Bool) : List gQ:=if b then [1,0] else [1]
def bJ (l:ai) : List Bool→ai
  | [] => l
  | b :: s => bf (bJ l s) (se b)
def aq (l:ai) (s : List Bool) (e:BA) (r:ai) : aL :=
  match e with
  | .GoRight => FR (bJ l s) r
  | .FromD => DL (bJ l s) r
  | .FromF => FL (bJ l s) ([0,0]+>r)
  | .FromB => BL (bJ l s) ([0,0]+>r)
inductive ip (l:ai) : aL→Prop where
  | contact_D (r:ai) : ip l (DL l r)
  | contact_F (r:ai) : ip l (FL l ([0,0]+>r))
  | contact_B (r:ai) : ip l (BL l ([0,0]+>r))
lemma el {c d : aL} {P : aL→Prop} {n : Nat}
    (hr : c [tm]⊢⁺ d)
    (ih : ∀ m < n,d7 d m→∃ k e,k ≤ m∧P e∧d7 e k)
    (hh : d7 c n) : ∃ k e,k ≤ n∧P e∧d7 e k := by
  rcases kz hr hh with ⟨m,hmn,hm⟩
  rcases ih m hmn hm with ⟨k,e,hkm,hp,hk⟩
  exact ⟨k,e,by omega,hp,hk⟩
lemma ux (n:Nat) :
    ∀ (l:ai) (s : List Bool) (e:BA) (r:ai),
    d7 (aq l s e r) n →
    ∃ k c,k ≤ n∧ip l c∧d7 c k := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro l s e r hhalt
    cases e with
    | GoRight =>
      rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
      · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
        · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
          · have hr : (aq l s .GoRight ([0]+>([0]+>([0]+>r)))) [tm]⊢⁺ (aq l s .FromD ([1,0,1]+>r)) := by
              simpa only [aq,← append_assoc] using! r2 (bJ l s) r
            exact el hr (fun m hmn hm => ih m hmn l s .FromD ([1,0,1]+>r) hm) hhalt
          · have hr : (aq l s .GoRight ([0]+>([0]+>([1]+>r)))) [tm]⊢⁺ (aq l (true :: false :: s) .GoRight r) := by
              simpa only [aq,bJ,se,df,← append_assoc] using! r4 (bJ l s) r
            exact el hr (fun m hmn hm => ih m hmn l (true :: false :: s) .GoRight r hm) hhalt
        · have hr : (aq l s .GoRight ([0]+>([1]+>r))) [tm]⊢⁺ (aq l (false :: false :: s) .GoRight r) := by
            simpa only [aq,bJ,se,df,← append_assoc] using! xH (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (false :: false :: s) .GoRight r hm) hhalt
      · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
        · have hr : (aq l s .GoRight ([1]+>([0]+>r))) [tm]⊢⁺ (aq l (true :: s) .GoRight r) := by
            simpa only [aq,bJ,se,df,← append_assoc] using! vf (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (true :: s) .GoRight r hm) hhalt
        · have hr : (aq l s .GoRight ([1]+>([1]+>r))) [tm]⊢⁺ (aq l s .FromF r) := by
            simpa only [aq,← append_assoc] using! vv (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromF r hm) hhalt
    | FromD =>
      cases s with
      | nil => exact ⟨n,DL l r,le_rfl,.contact_D r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromD r) [tm]⊢⁺ (aq l s .FromD ([1]+>r)) :=
            Av (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromD ([1]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromD r) [tm]⊢⁺ (aq l s .FromB r) :=
            xL (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromB r hm) hhalt
    | FromF =>
      cases s with
      | nil => exact ⟨n,FL l ([0,0]+>r),le_rfl,.contact_F r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromF r) [tm]⊢⁺ (aq l (true :: s) .GoRight ([0]+>r)) :=
            E6 (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (true :: s) .GoRight ([0]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromF r) [tm]⊢⁺ (aq l (false :: s) .FromD ([1,0,1]+>r)) :=
            xZ (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (false :: s) .FromD ([1,0,1]+>r) hm) hhalt
    | FromB =>
      cases s with
      | nil => exact ⟨n,BL l ([0,0]+>r),le_rfl,.contact_B r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromB r) [tm]⊢⁺ (aq l s .FromF ([0]+>r)) := by
            simpa only [aq,← append_assoc] using! EJ (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromF ([0]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromB r) [tm]⊢⁺ (aq l s .FromD ([0,1,0,0]+>r)) :=
            xV (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromD ([0,1,0,0]+>r) hm) hhalt
lemma fv (l r:ai) : cE (FR l r) (ip l) :=
  fun n hn => ux n l [] .GoRight r hn
lemma jC (l:ai) (s : List Bool) (e:BA) (r:ai) :
    cE (aq l s e r) (ip l) :=
  fun n hn => ux n l s e r hn
lemma pH (l r:ai) : fl (FR l r) (ip l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
      · refine cr ?_ (dg (.contact_D ([1,0,1]+>r)))
        simpa only [← append_assoc] using! r2 l r
      · refine cr ?_ (jC l [true,false] .GoRight r)
        simpa only [aq,bJ,se,df,← append_assoc] using! r4 l r
    · refine cr ?_ (jC l [false,false] .GoRight r)
      simpa only [aq,bJ,se,df,← append_assoc] using! xH l r
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · refine cr ?_ (jC l [true] .GoRight r)
      simpa only [aq,bJ,se,df,← append_assoc] using! vf l r
    · refine cr ?_ (dg (.contact_F r))
      simpa only [← append_assoc] using! vv l r
inductive gw (l:ai) : aL→Prop where
  | weak_D (r:ai) : gw l (DL l r)
  | weak_F (r:ai) : gw l (FL l ([0,0,0]+>r))
inductive dU (l:ai) : aL→Prop where
  | strong_D (r:ai) : dU l (DL l (wa+>r))
  | strong_F (r:ai) : dU l (FL l ([0,0,0]+>(wa+>r)))
lemma GZ (l r:ai) : (DL (bf l wL) r) [tm]⊢⁺ (FL l ([0,0,0]+>r)) :=
  U 2 ⟨wL.reverse,[],sD,true⟩ ⟨[],[0,0,0],sF,true⟩ (by decide) l r
lemma Ha (l r:ai) : (FL (bf l wL) ([0,0]+>r)) [tm]⊢⁺ (DL l ([1,1,1,0,1]+>r)) :=
  U 6 ⟨wL.reverse,[0,0],sF,true⟩ ⟨[],[1,1,1,0,1],sD,true⟩ (by decide) l r
lemma GX (l r:ai) : (BL (bf l wL) ([0,0]+>r)) [tm]⊢⁺ (DL l ([1,0,1,0,0]+>r)) :=
  U 2 ⟨wL.reverse,[0,0],sB,true⟩ ⟨[],[1,0,1,0,0],sD,true⟩ (by decide) l r
lemma Gn (l r:ai) : (DL (bf l [1,1]) r) [tm]⊢⁺ (DL l ([1,1]+>r)) :=
  U 1 ⟨[1,1],[],sD,true⟩ ⟨[],[1,1],sD,true⟩ (by decide) l r
lemma Gm (l r:ai) : (FL (bf l [1,1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l wL) ([0]+>r)) :=
  U 1 ⟨[1,1],[0,0],sF,true⟩ ⟨wL.reverse,[0],sF,false⟩ (by decide) l r
lemma Hm (l r:ai) : (BL (bf l [1,1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) ([0,0]+>r)) :=
  U 2 ⟨[1,1],[0,0],sB,true⟩ ⟨[0,1],[0,0],sF,false⟩ (by decide) l r
lemma G6 (l r:ai) : (DL (bf l wX) r) [tm]⊢⁺ (DL l (wa+>r)) :=
  U 9 ⟨wX.reverse,[],sD,true⟩ ⟨[],wa,sD,true⟩ (by decide) l r
lemma Dx (l r:ai) : (FL (bf l wX) ([0,0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>r))) := by
  simpa only [append_assoc] using!
    U 9 ⟨wX.reverse,[0,0,0],sF,true⟩ ⟨[],[0,0,0]++wa,sF,true⟩ (by decide) l r
lemma rW (l:ai) (c:aL) (h : ip (bf l wL) c) : cE c (gw l) := by
  cases h with
  | contact_D r => exact bn (V (GZ l r)) (.weak_F r)
  | contact_F r => exact bn (V (Ha l r)) (.weak_D ([1,1,1,0,1]+>r))
  | contact_B r => exact bn (V (GX l r)) (.weak_D ([1,0,1,0,0]+>r))
lemma yY (l r:ai) : cE (FR (bf l wL) r) (gw l) :=
  bh (fv (bf l wL) r) (rW l)
def lu (w : List gQ) : Prop :=
  ∀ l c,gw (bf l w) c→cE c (gw l)
lemma Bn : lu wL := by
  intro l c h
  cases h with
  | weak_D r => exact rW l _ (.contact_D r)
  | weak_F r =>
    have hc : ip (bf l wL) (FL (bf l wL) ([0,0]+>([0]+>r))):=.contact_F ([0]+>r)
    simpa only [← append_assoc] using! rW l _ hc
lemma AS : lu [1,1] := by
  intro l c h
  cases h with
  | weak_D r => exact bn (V (Gn l r)) (.weak_D ([1,1]+>r))
  | weak_F r =>
    have hf : (FL (bf l [1,1]) ([0,0,0]+>r)) [tm]⊢⁺ (FR (bf l wL) ([0]+>([0]+>r))) := by
      simpa only [← append_assoc] using! Gm l ([0]+>r)
    exact cc hf (yY l ([0]+>([0]+>r)))
lemma yX {u v : List gQ} (hu : lu u) (hv : lu v) :
    lu (u++v) := by
  intro l c hc
  rw [df] at hc
  exact bh (hv (bf l u) c hc) (hu l)
inductive b9 where
  | PL | P11
deriving DecidableEq
def x0 : b9→List gQ
  | .PL => wL
  | .P11 => [1,1]
def hE : List b9→List gQ
  | [] => []
  | p :: ps => x0 p++hE ps
lemma xg (ps : List b9) : lu (hE ps) := by
  induction ps with
  | nil => intro l c h; exact dg h
  | cons p ps ih =>
    unfold hE
    refine yX ?_ ih
    cases p
    · exact Bn
    · exact AS
lemma DZ (l:ai) (c:aL) (h : gw (bf l wX) c) :
    cE c (dU l) := by
  cases h with
  | weak_D r => exact bn (V (G6 l r)) (.strong_D r)
  | weak_F r => exact bn (V (Dx l r)) (.strong_F r)
def b5 (ps : List b9) : List gQ :=
  (wX++hE ps)++wL
lemma lI (ps : List b9) (l:ai) (c:aL)
    (h : ip (bf l (b5 ps)) c) : cE c (dU l) := by
  unfold b5 at h
  rw [df,df] at h
  refine bh (rW (bf (bf l wX) (hE ps)) c h) ?_
  intro d hd
  refine bh (xg ps (bf l wX) d hd) ?_
  intro e he
  exact DZ l e he
lemma r8 (ps : List b9) (l r:ai) :
    cE (FR (bf l (b5 ps)) r) (dU l) :=
  bh (fv (bf l (b5 ps)) r) (lI ps l)
inductive dA (l:ai) : aL→Prop where
  | phase_D (r:ai) : dA l (DL l r)
  | phase_F (r:ai) : dA l (FL l ([0,0,0]+>r))
  | phase_B101 (r:ai) : dA l (BL l ([0,0,1,0,1]+>r))
  | phase_B11101 (r:ai) : dA l (BL l ([0,0,1,1,1,0,1]+>r))
lemma x5 (l:ai) (c:aL) (h : gw l c) : dA l c := by
  cases h with
  | weak_D r => exact .phase_D r
  | weak_F r => exact .phase_F r
lemma GL (l r:ai) : (DL (bf l ([1,0]++wL)) r) [tm]⊢⁺ (DL l ([1,1,0,1,0]+>r)) :=
  U 8 ⟨(([1,0] : List gQ)++wL).reverse,[],sD,true⟩ ⟨[],[1,1,0,1,0],sD,true⟩ (by decide) l r
lemma GH (l r:ai) : (FL (bf l ([1,0]++wL)) ([0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,1,1,0,1]+>r)) :=
  U 8 ⟨(([1,0] : List gQ)++wL).reverse,[0,0],sF,true⟩ ⟨[],[0,0,1,1,1,0,1],sB,true⟩ (by decide) l r
lemma Gr (l r:ai) : (BL (bf l ([1,0]++wL)) ([0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,0,1,0,0]+>r)) :=
  U 4 ⟨(([1,0] : List gQ)++wL).reverse,[0,0],sB,true⟩ ⟨[],[0,0,1,0,1,0,0],sB,true⟩ (by decide) l r
lemma CI (l r:ai) : cE (FR (bf l ([1,0]++wL)) r) (dA l) := by
  refine bh (fv (bf l ([1,0]++wL)) r) ?_
  intro c h
  cases h with
  | contact_D r0 => exact bn (V (GL l r0)) (.phase_D ([1,1,0,1,0]+>r0))
  | contact_F r0 => exact bn (V (GH l r0)) (.phase_B11101 r0)
  | contact_B r0 =>
    have hp : dA l (BL l ([0,0,1,0,1,0,0]+>r0)) := by
      simpa only [← append_assoc] using! dA.phase_B101 ([0,0]+>r0)
    exact bn (V (Gr l r0)) hp
lemma A9 (l r:ai) : (FR (bf l [1,0]) ([0,0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,0,1]+>r)) :=
  U 6 ⟨[0,1],[0,0,0],sF,false⟩ ⟨[],[0,0,1,0,1],sB,true⟩ (by decide) l r
lemma AT (l r:ai) : (FR (bf l [1,0]) ([0,0,1]+>r)) [tm]⊢⁺ (FR (bf l ([1,0]++wL)) r) :=
  U 4 ⟨[0,1],[0,0,1],sF,false⟩ ⟨(([1,0] : List gQ)++wL).reverse,[],sF,false⟩ (by decide) l r
lemma Bl (l r:ai) : cE (FR (bf l [1,0]) ([0,0]+>r)) (dA l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR (bf l [1,0]) ([0,0]+>([0]+>r))) [tm]⊢⁺ (BL l ([0,0,1,0,1]+>r)) := by
      simpa only [← append_assoc] using! A9 l r
    exact bn (V hr) (.phase_B101 r)
  · have hr : (FR (bf l [1,0]) ([0,0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l ([1,0]++wL)) r) := by
      simpa only [← append_assoc] using! AT l r
    exact cc hr (CI l r)
lemma x9 (l r:ai) : cE (FR (bf l [1,1]) r) (dA l) := by
  refine bh (fv (bf l [1,1]) r) ?_
  intro c h
  cases h with
  | contact_D r0 => exact bn (V (Gn l r0)) (.phase_D ([1,1]+>r0))
  | contact_F r0 => exact cc (Gm l r0) (x7 (yY l ([0]+>r0)) (x5 l))
  | contact_B r0 => exact cc (Hm l r0) (Bl l r0)
lemma uR (l r:ai) : cE (FR l ([0]+>r)) (dA l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have hr : (FR l ([0]+>([0]+>([0]+>r)))) [tm]⊢⁺ (DL l ([1,0,1]+>r)) := by
        simpa only [← append_assoc] using! r2 l r
      exact bn (V hr) (.phase_D ([1,0,1]+>r))
    · have hr : (FR l ([0]+>([0]+>([1]+>r)))) [tm]⊢⁺ (FR (bf l wL) r) := by
        simpa only [← append_assoc] using! r4 l r
      exact cc hr (x7 (yY l r) (x5 l))
  · have hr : (FR l ([0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l [1,1]) r) := by
      simpa only [← append_assoc] using! xH l r
    exact cc hr (x9 l r)
inductive W where
  | UA | UT
deriving DecidableEq
inductive cm where
  | CD | CF
deriving DecidableEq
def za : W→List gQ
  | .UA => wa
  | .UT => wY++wa
def yT : W→List gQ
  | .UA => wa
  | .UT => wa++wb
def G1 : W→List gQ
  | .UA => wX
  | .UT => wX++wY
def HD : List W→List gQ
  | [] => []
  | u :: us => za u++HD us
def HF : List W→List gQ
  | [] => []
  | u :: us => yT u++HF us
def G : List W→List gQ
  | [] => []
  | u :: us => G1 u++G us
@[simp] lemma Cg (u:W) (us : List W) : HD (u :: us) = za u++HD us:=rfl
@[simp] lemma CB (u:W) (us : List W) : HF (u :: us) = yT u++HF us:=rfl
def lX : cm→List gQ
  | .CD => []
  | .CF => wY
def oa (d:cm) (us : List W) : List gQ :=
  match d with
  | .CD => HD us
  | .CF => wb++HF us
def hF (d:cm) (us : List W) (r:ai) : aL :=
  CE (oa d us+>r)
def lr (c:aL) : Prop :=
  ∃ d us r,3 ≤ us.length∧c = hF d us r
def cn (d:cm) (us : List W) : ai :=
  bf default ([0]++lX d++G us)
lemma F0 (us vs : List W) : HD (us++vs) = HD us++HD vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [HD,ih,List.append_assoc]
lemma F7 (us vs : List W) : HF (us++vs) = HF us++HF vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [HF,ih,List.append_assoc]
lemma Gt (us vs : List W) : G (us++vs) = G us++G vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [G,ih,List.append_assoc]
lemma D4 (u:W) (l r:ai) :
    (FR l ([0]+>(za u+>r))) [tm]⊢⁺ (FR (bf l (G1 u)) ([0]+>r)) := by
  cases u
  · simpa only [za,G1,append_assoc] using!
      U 11 ⟨[],[0]++wa,sF,false⟩ ⟨wX.reverse,[0],sF,false⟩ (by decide) l r
  · simpa only [za,G1,append_assoc] using!
      U 17 ⟨[],[0]++(wY++wa),sF,false⟩ ⟨(wX++wY).reverse,[0],sF,false⟩ (by decide) l r
lemma DW (u:W) (l r:ai) :
    (FR l ([0]+>(yT u+>r))) [tm]⊢⁺ (FR (bf l (G1 u)) ([0]+>r)) := by
  cases u
  · simpa only [yT,G1,append_assoc] using!
      U 11 ⟨[],[0]++wa,sF,false⟩ ⟨wX.reverse,[0],sF,false⟩ (by decide) l r
  · simpa only [yT,G1,append_assoc] using!
      U 15 ⟨[],[0]++(wa++wb),sF,false⟩ ⟨(wX++wY).reverse,[0],sF,false⟩ (by decide) l r
lemma FV (l r:ai) :
    (FR l ([0]+>(wb+>r))) [tm]⊢⁺ (FR (bf l wY) ([0]+>r)) := by
  simpa only [append_assoc] using!
    U 3 ⟨[],[0]++wb,sF,false⟩ ⟨wY.reverse,[0],sF,false⟩ (by decide) l r
lemma EP (us : List W) (l r:ai) :
    (FR l ([0]+>(HD us+>r))) [tm]⊢* (FR (bf l (G us)) ([0]+>r)) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold HD G
    rw [append_assoc,df]
    exact V (ee (D4 u l (HD us+>r)) (ih (bf l (G1 u)) r))
lemma Ff (us : List W) (l r:ai) :
    (FR l ([0]+>(HF us+>r))) [tm]⊢* (FR (bf l (G us)) ([0]+>r)) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold HF G
    rw [append_assoc,df]
    exact V (ee (DW u l (HF us+>r)) (ih (bf l (G1 u)) r))
lemma Fg (r:ai) : (CE r) [tm]⊢⁺ (FR (bf default [0]) ([0]+>r)) := by
  refine ⟨1,by decide,?_⟩
  simp only [CE,FR,bf,List.reverse_singleton,n9,step,append_cons,append_nil,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5,tm,target_tm,sE,sF,F,A,Option.map,Tape.write,Tape.move]
lemma tj (d:cm) (us : List W) (r:ai) :
    (hF d us r) [tm]⊢⁺ (FR (cn d us) ([0]+>r)) := by
  unfold hF
  refine ee (Fg (oa d us+>r)) ?_
  cases d
  · unfold oa cn lX
    simp only [List.append_nil,df]
    exact EP us (bf default [0]) r
  · unfold oa cn lX
    rw [append_assoc,df,df]
    exact V (ee (FV (bf default [0]) (HF us+>r)) (Ff us (bf (bf default [0]) wY) r))
lemma Hh (u:W) (l r:ai) :
    (DL (bf l (G1 u)) (wa+>r)) [tm]⊢⁺ (DL l (wa+>(za u+>r))) := by
  cases u
  · simpa only [G1,za,append_assoc] using!
      U 9 ⟨wX.reverse,wa,sD,true⟩ ⟨[],wa++wa,sD,true⟩ (by decide) l r
  · simpa only [G1,za,append_assoc] using!
      U 13 ⟨(wX++wY).reverse,wa,sD,true⟩ ⟨[],wa++(wY++wa),sD,true⟩ (by decide) l r
lemma Hf (u:W) (l r:ai) :
    (FL (bf l (G1 u)) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>(yT u+>r)))) := by
  cases u
  · simpa only [G1,yT,append_assoc] using!
      U 9 ⟨wX.reverse,[0,0,0]++wa,sF,true⟩ ⟨[],[0,0,0]++wa++wa,sF,true⟩ (by decide) l r
  · simpa only [G1,yT,append_assoc] using!
      U 49 ⟨(wX++wY).reverse,[0,0,0]++wa,sF,true⟩ ⟨[],[0,0,0]++wa++(wa++wb),sF,true⟩ (by decide) l r
lemma Ii (us : List W) (l r:ai) :
    (DL (bf l (G us)) (wa+>r)) [tm]⊢* (DL l (wa+>(HD us+>r))) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold G HD
    rw [df,append_assoc]
    exact ss (ih (bf l (G1 u)) r) (V (Hh u l (HD us+>r)))
lemma HT (us : List W) (l r:ai) :
    (FL (bf l (G us)) ([0,0,0]+>(wa+>r))) [tm]⊢* (FL l ([0,0,0]+>(wa+>(HF us+>r)))) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold G HF
    rw [df,append_assoc]
    exact ss (ih (bf l (G1 u)) r) (V (Hf u l (HF us+>r)))
lemma HO (l r:ai) : (DL (bf l wY) (wa+>r)) [tm]⊢⁺ (DL l (wY+>(wa+>r))) := by
  simpa only [append_assoc] using!
    U 3 ⟨wY.reverse,wa,sD,true⟩ ⟨[],wY++wa,sD,true⟩ (by decide) l r
lemma Ia (l r:ai) :
    (FL (bf l wY) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>(wb+>r)))) := by
  simpa only [append_assoc] using!
    U 39 ⟨wY.reverse,[0,0,0]++wa,sF,true⟩ ⟨[],[0,0,0]++wa++wb,sF,true⟩ (by decide) l r
lemma B3 (r:ai) : (DL (bf default [0]) r) [tm]⊢⁺ (CE r) := by
  refine ⟨1,by decide,?_⟩
  simp only [DL,CE,bf,List.reverse_singleton,n9,step,append_cons,append_nil,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5,tm,target_tm,sD,sE,E,F,Option.map,Tape.write,Tape.move]
structure f3 where
  past : List gQ
  front : List gQ
  state : Fin 6
deriving DecidableEq
def dw (x:f3) (r:ai) : aL :=
  ⟨some x.state,⟨(x.front+>r).head,x.past+>default,(x.front+>r).tail⟩⟩
def mr (x:f3) : Option f3 :=
  match x.front with
  | [] => none
  | b :: bs =>
    match tm x.state b with
    | none => none
    | some (none,_) => none
    | some (some s',Stmt.write v .right) => some ⟨v :: x.past,bs,s'⟩
    | some (some s',Stmt.write v .left) =>
      match x.past with
      | [] => some ⟨[],0 :: v :: bs,s'⟩
      | a :: ls => some ⟨ls,a :: v :: bs,s'⟩
def AL : Nat→f3→Option f3
  | 0,x => some x
  | n + 1,x =>
    match mr x with
    | none => none
    | some y => AL n y
lemma vX {x y : f3} (h : mr x = some y) (r:ai) :
    (dw x r) [tm]⊢ (dw y r) := by
  rcases x with ⟨ls,fs,s⟩
  cases fs with
  | nil => contradiction
  | cons b bs =>
    unfold mr at h; dsimp only at h
    rcases htm : tm s b with _ | ⟨q',st⟩
    · rw [htm] at h; contradiction
    · rw [htm] at h
      rcases q' with _ | s'
      · contradiction
      · rcases st with ⟨v,d⟩
        cases d
        · cases ls with
          | nil =>
            injection h with hy; subst hy
            unfold dw; dsimp only [append_cons,append_nil]
            simp only [step,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5,htm,Option.map,Tape.write,Tape.move]
          | cons a ls =>
            injection h with hy; subst hy
            unfold dw; dsimp only [append_cons]
            simp only [step,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Option.map,Tape.write,Tape.move]
        · injection h with hy; subst hy
          unfold dw; dsimp only [append_cons]
          simp only [step,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,htm,Option.map,Tape.write,Tape.move]
lemma Db {n : Nat} {x y : f3} (h : AL n x = some y) (r:ai) :
    (dw x r) [tm]⊢^{n} (dw y r) := by
  induction n generalizing x with
  | zero => injection h with hy; subst hy; rfl
  | succ n ih =>
    unfold AL at h
    rcases hs : mr x with _ | z
    · rw [hs] at h; contradiction
    · rw [hs] at h
      rw [Nat.add_comm n 1]
      exact qH tm _ _ _ 1 n (qO tm _ _ (vX hs r)) (ih h)
lemma vK {n : Nat} {x y : f3} (h : AL (n + 1) x = some y) (r:ai) :
    (dw x r) [tm]⊢⁺ (dw y r) :=
  ⟨n + 1,Nat.succ_pos n,Db h r⟩
def r3 : List gQ→List gQ
  | [] => []
  | b :: ls =>
    match r3 ls with
    | [] => if b==0 then [] else [b]
    | ys => b :: ys
lemma xx (ls : List gQ) : r3 ls+>default = ls+>default := by
  induction ls with
  | nil => rfl
  | cons b ls ih =>
    unfold r3
    rcases h : r3 ls with _ | ⟨y,ys⟩
    · rw [h,append_nil] at ih
      rcases x3 b with rfl | rfl
      · change []+>default = (0 :: ls)+>default
        rw [append_nil,append_cons,← ih,oR]
      · change [1]+>default = (1 :: ls)+>default
        rw [append_cons,append_nil,append_cons,← ih]
    · change (b :: y :: ys)+>default = (b :: ls)+>default
      rw [append_cons,← h,ih,append_cons]
def kR (x y:f3) : Bool :=
  r3 x.past==r3 y.past&&x.front==y.front&&x.state==y.state
lemma kE {x y : f3} (h : kR x y = true) (r:ai) :
    dw x r = dw y r := by
  unfold kR at h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨⟨hp,hf⟩,hs⟩
  unfold dw
  rw [hf,hs,← xx x.past,← xx y.past,hp]
def vN (n:Nat) (x y:f3) : Bool :=
  match AL n x with
  | some z => kR z y
  | none => false
lemma kC (n:Nat) (x y:f3) (h : vN (n + 1) x y = true) (r:ai) :
    (dw x r) [tm]⊢⁺ (dw y r) := by
  unfold vN at h
  rcases hr : AL (n + 1) x with _ | z
  · rw [hr] at h; contradiction
  · rw [hr] at h
    rw [← kE h r]
    exact vK hr r
lemma Ck (r:ai) : (FL (bf default [0]) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (CE (wb+>(wa+>r))) := by
  have h:=kC 5 ⟨[],0 :: ([0,0,0]++wa),sF⟩ ⟨[],[0,0]++wb++wa,sE⟩ (by decide) r
  simpa only [dw,FL,CE,bf,List.reverse_singleton,append_cons,append_nil,append_assoc,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons] using h
def gJ : cm→W
  | .CD => .UA
  | .CF => .UT
lemma Ek (d:cm) (us : List W) (r:ai) :
    (DL (cn d us) (wa+>r)) [tm]⊢⁺ (hF .CD (gJ d :: us) r) := by
  unfold cn
  rw [df]
  refine kT (Ii us (bf default ([0]++lX d)) r) ?_
  cases d
  · unfold lX gJ hF oa
    simp only [Cg,za,List.append_nil,append_assoc]
    exact B3 (wa+>(HD us+>r))
  · unfold lX gJ hF oa
    rw [df]
    refine sq (HO (bf default [0]) (HD us+>r)) ?_
    simp only [Cg,za,append_assoc]
    exact B3 (wY+>(wa+>(HD us+>r)))
lemma Ea (d:cm) (us : List W) (r:ai) :
    (FL (cn d us) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (hF .CF (gJ d :: us) r) := by
  unfold cn
  rw [df]
  refine kT (HT us (bf default ([0]++lX d)) r) ?_
  cases d
  · unfold lX gJ hF oa
    simp only [CB,yT,List.append_nil,append_assoc]
    exact Ck (HF us+>r)
  · unfold lX gJ hF oa
    rw [df]
    refine sq (Ia (bf default [0]) (HF us+>r)) ?_
    simp only [CB,yT,append_assoc]
    exact Ck (wb+>(HF us+>r))
def Bd (d:cm) (us : List W) (c:aL) : Prop :=
  ∃ d' r,c = hF d' (gJ d :: us) r
lemma hN (d:cm) (us : List W) (c:aL)
    (h : dU (cn d us) c) : cE c (Bd d us) := by
  cases h with
  | strong_D r =>
    exact bn (V (Ek d us r)) ⟨.CD,r,rfl⟩
  | strong_F r =>
    exact bn (V (Ea d us r)) ⟨.CF,r,rfl⟩
lemma i8 (d:cm) (us : List W) (c:aL)
    (hlen : 2 ≤ us.length) (h : Bd d us c) : lr c := by
  rcases h with ⟨d',r,rfl⟩
  exact ⟨d',gJ d :: us,r,by simp; omega,rfl⟩
def Ct : List gQ:=[1,1,1,1,1,1,1,1,1]
def wo : List gQ:=[1,1,1,1,1,1,0,1,0]
lemma CM (l r:ai) :
    (FR l ([0]+>(Ct+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r)) := by
  simpa only [b5,hE,append_assoc] using!
    U 20 ⟨[],[0]++Ct,sF,false⟩ ⟨((wX++[])++wL).reverse,[0],sF,false⟩ (by decide) l r
lemma D2 (l r:ai) :
    (FR l ([0]+>(wo+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r)) := by
  simpa only [b5,hE,append_assoc] using!
    U 18 ⟨[],[0]++wo,sF,false⟩ ⟨((wX++[])++wL).reverse,[0],sF,false⟩ (by decide) l r
lemma y7 (d:cm) (us : List W) (r:ai) (t : List gQ)
    (hlen : 2 ≤ us.length)
    (ht : ∀ l r,(FR l ([0]+>(t+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r))) :
    cE (hF d us (t+>r)) lr := by
  refine cc (tj d us (t+>r)) ?_
  refine cc (ht (cn d us) r) ?_
  refine bh (r8 [] (cn d us) ([0]+>r)) ?_
  intro c hc
  refine bh (hN d us c hc) ?_
  intro e he
  exact dg (i8 d us e hlen he)
lemma ye (d:cm) (us : List W) (r:ai) (hlen : 2 ≤ us.length) :
    cE (hF d us (Ct+>r)) lr :=
  y7 d us r Ct hlen CM
lemma ze (d:cm) (us : List W) (r:ai) (hlen : 2 ≤ us.length) :
    cE (hF d us (wo+>r)) lr :=
  y7 d us r wo hlen D2
lemma xN (r:ai) :
    (hF .CF [.UA,.UT] ((wY++wa++wa)+>r)) [tm]⊢⁺
    (FR (bf (cn .CF [.UA,.UT]) (b5 [.P11,.P11])) ([0,0,1,0]+>r)) := by
  have h:=kC 57
    ⟨[],[0,0]++oa .CF [.UA,.UT]++(wY++wa++wa),sE⟩
    ⟨([0]++lX .CF++G [.UA,.UT]++b5 [.P11,.P11]).reverse,[0,0,1,0],sF⟩
    (by decide) r
  simpa only [dw,hF,CE,FR,cn,df,bf,append_assoc] using! h
lemma Ap (r:ai) :
    cE (hF .CF [.UA,.UT] ((wY++wa++wa)+>r)) lr := by
  refine cc (xN r) ?_
  refine bh (r8 [.P11,.P11] (cn .CF [.UA,.UT]) ([0,0,1,0]+>r)) ?_
  intro c hc
  refine bh (hN .CF [.UA,.UT] c hc) ?_
  intro e he
  exact dg (i8 .CF [.UA,.UT] e (by decide) he)
inductive bR where
  | RD | RF | RB
deriving DecidableEq
def jY (e:bR) (l r:ai) : aL :=
  match e with
  | .RD => DL l r
  | .RF => FL l r
  | .RB => BL l r
def vT : List (bR × List gQ) :=
  [(.RD,[]),(.RF,[0,0]),(.RB,[0,0])]
def pN : List (bR × List gQ) :=
  [(.RD,[1,0,1]),(.RD,[1,1,1,0,1]),(.RD,[1,0,1,0,0]),(.RF,[0,0,0])]
def Ac : List (bR × List gQ) :=
  [(.RD,[1,1,0,1]),(.RD,[0,1,0,0]),(.RF,[0,0]),(.RB,[0,0])]
def xR : List (bR × List gQ):=[(.RD,[]),(.RF,[0,0])]
def Bk : List (bR × List gQ):=[(.RD,[]),(.RB,[0,0])]
def Cu : List (bR × List gQ):=[(.RF,[0,0])]
def ic (l:ai) (es : List (bR × List gQ)) (c:aL) : Prop :=
  ∃ e p r,(e,p) ∈ es∧c = jY e l (p+>r)
lemma we (l:ai) (c:aL) (h : ip l c) : ic l vT c := by
  cases h with
  | contact_D r => exact ⟨.RD,[],r,by decide,rfl⟩
  | contact_F r => exact ⟨.RF,[0,0],r,by decide,rfl⟩
  | contact_B r => exact ⟨.RB,[0,0],r,by decide,rfl⟩
lemma Bv (l r:ai) : fl (FR l r) (ic l vT) :=
  sv (pH l r) (fun c h => dg (we l c h))
lemma CT (l:ai) (c:aL) (h : ip (bf l wL) c) :
    cE c (ic l pN) := by
  cases h with
  | contact_D r =>
    exact bn (V (GZ l r)) ⟨.RF,[0,0,0],r,by decide,rfl⟩
  | contact_F r =>
    exact bn (V (Ha l r)) ⟨.RD,[1,1,1,0,1],r,by decide,rfl⟩
  | contact_B r =>
    exact bn (V (GX l r)) ⟨.RD,[1,0,1,0,0],r,by decide,rfl⟩
lemma x2 (l r:ai) : fl (FR l ([0,0]+>r)) (ic l pN) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR l ([0,0]+>([0]+>r))) [tm]⊢⁺ (DL l ([1,0,1]+>r)) := by
      simpa only [← append_assoc] using! r2 l r
    exact cr hr (dg ⟨.RD,[1,0,1],r,by decide,rfl⟩)
  · have hr : (FR l ([0,0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l wL) r) := by
      simpa only [← append_assoc] using! r4 l r
    exact cr hr (bh (fv (bf l wL) r) (CT l))
lemma Bp (l:ai) (c:aL) (h : ip (bf l [1,0]) c) :
    cE c (ic l Ac) := by
  cases h with
  | contact_D r =>
    exact bn (V (xL l r)) ⟨.RB,[0,0],r,by decide,rfl⟩
  | contact_F r =>
    refine cc (xZ l r) ?_
    refine cc (Av l ([1,0,1]+>r)) ?_
    exact dg ⟨.RD,[1,1,0,1],r,by decide,by simp [jY,← append_assoc]⟩
  | contact_B r =>
    exact bn (V (xV l r)) ⟨.RD,[0,1,0,0],r,by decide,rfl⟩
lemma CX (l r:ai) : fl (FR l ([1]+>r)) (ic l Ac) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR l ([1]+>([0]+>r))) [tm]⊢⁺ (FR (bf l [1,0]) r) := by
      simpa only [← append_assoc] using! vf l r
    exact cr hr (bh (fv (bf l [1,0]) r) (Bp l))
  · have hr : (FR l ([1]+>([1]+>r))) [tm]⊢⁺ (FL l ([0,0]+>r)) := by
      simpa only [← append_assoc] using! vv l r
    exact cr hr (dg ⟨.RF,[0,0],r,by decide,rfl⟩)
lemma x8 (l:ai) (c:aL) (h : ic l pN c) :
    ic l xR c := by
  rcases h with ⟨e,p,r,hin,rfl⟩
  simp only [pN,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hin
  rcases hin with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨.RD,[],[1,0,1]+>r,by decide,rfl⟩
  · exact ⟨.RD,[],[1,1,1,0,1]+>r,by decide,rfl⟩
  · exact ⟨.RD,[],[1,0,1,0,0]+>r,by decide,rfl⟩
  · exact ⟨.RF,[0,0],[0]+>r,by decide,by simp [jY,← append_assoc]⟩
lemma xm (l r:ai) : fl (FR l ([0,0]+>r)) (ic l xR) :=
  sv (x2 l r) (fun c h => dg (x8 l c h))
lemma w5 (l r:ai) : fl (FR l ([1,0]+>r)) (ic l Bk) := by
  refine cr (vf l r) ?_
  refine bh (fv (bf l [1,0]) r) ?_
  intro c h
  cases h with
  | contact_D r0 =>
    exact bn (V (xL l r0)) ⟨.RB,[0,0],r0,by decide,rfl⟩
  | contact_F r0 =>
    refine cc (xZ l r0) ?_
    exact bn (V (Av l ([1,0,1]+>r0)))
      ⟨.RD,[],[1,1,0,1]+>r0,by decide,by simp [jY,← append_assoc]⟩
  | contact_B r0 =>
    exact bn (V (xV l r0))
      ⟨.RD,[],[0,1,0,0]+>r0,by decide,rfl⟩
lemma wv (l r:ai) : fl (FR l ([1,1]+>r)) (ic l Cu) :=
  cr (vv l r) (dg ⟨.RF,[0,0],r,by decide,rfl⟩)
inductive ax where
  | qA | qB | qC | qD | qE | qF
deriving DecidableEq
def yh (b:Bool) : gQ:=if b then 1 else 0
def be (bs : List Bool) : List gQ:=bs.map yh
@[simp] lemma y4 : be [] = []:=rfl
@[simp] lemma m7 (b:Bool) (bs : List Bool) : be (b :: bs) = yh b :: be bs:=rfl
@[simp] lemma jF (xs ys : List Bool) : be (xs++ys) = be xs++be ys := by simp [be]
@[simp] lemma sT (xs : List Bool) : be xs.reverse = (be xs).reverse := by simp [be]
def BJ : ax→Fin 6
  | .qA => sA | .qB => sB | .qC => sC | .qD => sD | .qE => sE | .qF => sF
structure R where
  past : List Bool
  front : List Bool
  state : ax
deriving DecidableEq
def sz (x:R) : f3 :=
  ⟨be x.past,be x.front,BJ x.state⟩
def dC (x:R) (r:ai) : aL:=dw (sz x) r
def v4 (x:R) : Option R :=
  match x.front with
  | [] => none
  | false :: bs =>
    match x.state with
    | .qA => some ⟨true :: x.past,bs,.qB⟩
    | .qB =>
      match x.past with
      | [] => some ⟨[],false :: true :: bs,.qC⟩
      | a :: ls => some ⟨ls,a :: true :: bs,.qC⟩
    | .qC => none
    | .qD =>
      match x.past with
      | [] => some ⟨[],false :: false :: bs,.qE⟩
      | a :: ls => some ⟨ls,a :: false :: bs,.qE⟩
    | .qE => some ⟨false :: x.past,bs,.qF⟩
    | .qF => some ⟨true :: x.past,bs,.qA⟩
  | true :: bs =>
    match x.state with
    | .qA => some ⟨true :: x.past,bs,.qF⟩
    | .qB =>
      match x.past with
      | [] => some ⟨[],false :: false :: bs,.qF⟩
      | a :: ls => some ⟨ls,a :: false :: bs,.qF⟩
    | .qC =>
      match x.past with
      | [] => some ⟨[],false :: false :: bs,.qD⟩
      | a :: ls => some ⟨ls,a :: false :: bs,.qD⟩
    | .qD =>
      match x.past with
      | [] => some ⟨[],false :: true :: bs,.qD⟩
      | a :: ls => some ⟨ls,a :: true :: bs,.qD⟩
    | .qE =>
      match x.past with
      | [] => some ⟨[],false :: false :: bs,.qB⟩
      | a :: ls => some ⟨ls,a :: false :: bs,.qB⟩
    | .qF => some ⟨true :: x.past,bs,.qE⟩
def AV (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih [] (false :: true :: bs) q
def zI (a:Bool) (ls : List Bool) (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih ls (a :: true :: bs) q
noncomputable def sZ (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    AV
    zI
    past q ih bs
def Ak (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih [] (false :: false :: bs) q
def yj (a:Bool) (ls : List Bool) (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih ls (a :: false :: bs) q
noncomputable def ln (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    Ak
    yj
    past q ih bs
def ll (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  ih (true :: past) bs q
def xG (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  ih (false :: past) bs q
def CP (_ : List Bool→List Bool→ax→Option R) (_ _ : List Bool) : Option R :=
  none
noncomputable def xy (state:ax) : (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  ax.rec (motive:=fun _ => (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    (ll .qB)
    (sZ .qC)
    CP
    (ln .qE)
    (xG .qF)
    (ll .qA)
    state
noncomputable def xO (state:ax) : (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  ax.rec (motive:=fun _ => (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    (ll .qF)
    (ln .qF)
    (ln .qD)
    (sZ .qD)
    (ln .qB)
    (ll .qE)
    state
noncomputable def Ca (b:Bool) : ax→(List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  Bool.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    xy
    xO
    b
noncomputable def Au (b:Bool) (bs : List Bool)
    (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (state:ax) (ih : List Bool→List Bool→ax→Option R) (past : List Bool) : Option R :=
  Ca b state ih past bs
def A1 (_:ax) (_ : List Bool→List Bool→ax→Option R) (_ : List Bool) : Option R :=
  none
noncomputable def lN (ih : List Bool→List Bool→ax→Option R)
    (past front : List Bool) (state:ax) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    A1
    Au
    front state ih past
def Aj (past front : List Bool) (state:ax) : Option R :=
  some ⟨past,front,state⟩
noncomputable def zV (_:Nat) (ih : List Bool→List Bool→ax→Option R) : List Bool→List Bool→ax→Option R :=
  lN ih
noncomputable def l7 (n:Nat) : List Bool→List Bool→ax→Option R :=
  Nat.rec (motive:=fun _ => List Bool→List Bool→ax→Option R)
    Aj
    zV
    n
noncomputable def xJ (n:Nat) (x:R) : Option R :=
  R.rec (motive:=fun _ => Option R) (l7 n) x
noncomputable def Ao (n:Nat) (x:R) : Option R :=
  R.rec (motive:=fun _ => Option R) (lN (l7 n)) x
lemma zg (x:R) : (v4 x).map sz = mr (sz x) := by
  rcases x with ⟨_ | ⟨a,ls⟩,_ | ⟨_ | _,bs⟩,_ | _ | _ | _ | _ | _⟩ <;> rfl
lemma wx (ih : List Bool→List Bool→ax→Option R)
    (past front : List Bool) (state:ax) :
    lN ih past front state =
      match v4 ⟨past,front,state⟩ with
      | none => none
      | some y => ih y.past y.front y.state := by
  rcases past with _ | ⟨a,ls⟩ <;> rcases front with _ | ⟨_ | _,bs⟩ <;> cases state <;> rfl
lemma vQ (n:Nat) (past front : List Bool) (state:ax) :
    (l7 n past front state).map sz = AL n (sz ⟨past,front,state⟩) := by
  induction n generalizing past front state with
  | zero => rfl
  | succ n ih =>
    change (lN (l7 n) past front state).map sz = AL (n + 1) (sz ⟨past,front,state⟩)
    rw [wx]
    unfold AL
    rw [← zg ⟨past,front,state⟩]
    rcases v4 ⟨past,front,state⟩ with _ | ⟨p',f',s'⟩ <;> simp [ih]
lemma AX (n:Nat) (x:R) : (xJ n x).map sz = AL n (sz x) :=
  vQ n x.past x.front x.state
def CK : ax→ax→Bool
  | .qA,.qA | .qB,.qB | .qC,.qC | .qD,.qD | .qE,.qE | .qF,.qF => true
  | _,_ => false
lemma zY (x y:ax) : CK x y = true↔x = y := by
  cases x <;> cases y <;> decide
def sx (_:Bool) (_ : List Bool) (_:Bool) : Bool:=false
noncomputable def zS (ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => Bool) true sx ys
noncomputable def zK (b:Bool) (ih : List Bool→Bool) (bs : List Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool) (ih bs) false b
noncomputable def y5 (b:Bool) (ih : List Bool→Bool) (bs : List Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool) false (ih bs) b
noncomputable def rj (b:Bool) (bs : List Bool) (_ : (List Bool→Bool)→Bool→Bool)
    (ih : List Bool→Bool) (a:Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool→(List Bool→Bool)→List Bool→Bool) zK y5 a b ih bs
def sm (_ : List Bool→Bool) (_:Bool) : Bool:=false
noncomputable def pt (a:Bool) (_ : List Bool) (ih : List Bool→Bool) (ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => (List Bool→Bool)→Bool→Bool)
    sm
    rj
    ys ih a
noncomputable def lp (xs ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => List Bool→Bool)
    zS
    pt
    xs ys
lemma oF (xs ys : List Bool) : lp xs ys = true↔xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [lp,zS,sx]
  | cons a as ih =>
    cases ys with
    | nil => simp [lp,pt,sm]
    | cons b bs =>
      change pt a as (lp as) (b :: bs) = true↔a :: as = b :: bs
      cases a <;> cases b <;> simp [pt,rj,zK,y5,ih]
def mz (b:Bool) (_ : List Bool) (ih : List Bool) : List Bool :=
  match ih with
  | [] => if b then [true] else []
  | ys => b :: ys
noncomputable def mO (ls : List Bool) : List Bool :=
  List.rec (motive:=fun _ => List Bool) [] mz ls
lemma sp (ls : List Bool) : be (mO ls) = r3 (be ls) := by
  induction ls with
  | nil => rfl
  | cons b ls ih =>
    change be (mz b ls (mO ls)) = r3 (yh b :: be ls)
    unfold mz r3
    rw [← ih]
    rcases mO ls with _ | ⟨y,ys⟩ <;> cases b <;> rfl
noncomputable def mn (xp xf : List Bool) (xs:ax) (yp yf : List Bool) (ys:ax) : Bool :=
  CK xs ys&&lp xf yf&&(lp xp yp||lp (mO xp) (mO yp))
noncomputable def xt (y:R) (xp xf : List Bool) (xs:ax) : Bool :=
  R.rec (motive:=fun _ => Bool) (mn xp xf xs) y
noncomputable def tX (x y:R) : Bool :=
  R.rec (motive:=fun _ => Bool) (xt y) x
lemma wt {x y : R} (h : tX x y = true) (r:ai) :
    dC x r = dC y r := by
  rcases x with ⟨xp,xf,xs⟩
  rcases y with ⟨yp,yf,ys⟩
  change mn xp xf xs yp yf ys = true at h
  unfold mn at h
  simp only [Bool.and_eq_true,Bool.or_eq_true,zY,oF] at h
  rcases h with ⟨⟨hs,hf⟩,hp | hp⟩
  · apply kE _ r
    unfold kR sz
    dsimp only
    rw [hp,hf,hs]
    simp
  · apply kE _ r
    unfold kR sz
    dsimp only
    rw [← sp xp,← sp yp,hp,hf,hs]
    simp
def Be (_:R) : Bool:=false
noncomputable def Ba (z y:R) : Bool:=tX z y
noncomputable def oh (n:Nat) (x y:R) : Bool :=
  Option.rec (motive:=fun _ => R→Bool) Be Ba (xJ n x) y
noncomputable def eO (n:Nat) (x y:R) : Bool :=
  Option.rec (motive:=fun _ => R→Bool) Be Ba (Ao n x) y
lemma gi (n:Nat) (x y:R)
    (h : oh (n + 1) x y = true) (r:ai) :
    (dC x r) [tm]⊢⁺ (dC y r) := by
  unfold oh at h
  rcases hr : xJ (n + 1) x with _ | z
  · rw [hr] at h; contradiction
  · rw [hr] at h
    change tX z y = true at h
    rw [← wt h r]
    have hrun : AL (n + 1) (sz x) = some (sz z) := by
      rw [← AX (n + 1) x,hr]; rfl
    exact vK hrun r
def bL : List Bool:=[true,true,false]
def bX : List Bool:=[true,true,false,true,true,false]
def bY : List Bool:=[true,true,true,true]
def ba : List Bool:=[true,true,true,false,true,false]
def bb : List Bool:=[true,false,true,false]
def EQ : List Bool:=[true,true,true,true,true,true,true,true,true]
def B8 : List Bool:=[true,true,true,true,true,true,false,true,false]
def Gh : W→List Bool
  | .UA => ba
  | .UT => bY++ba
def Gi : W→List Bool
  | .UA => ba
  | .UT => ba++bb
def Hy : W→List Bool
  | .UA => bX
  | .UT => bX++bY
def FM : List W→List Bool
  | [] => []
  | u :: us => Gh u++FM us
def Gb : List W→List Bool
  | [] => []
  | u :: us => Gi u++Gb us
def bG : List W→List Bool
  | [] => []
  | u :: us => Hy u++bG us
def bW : cm→List Bool
  | .CD => []
  | .CF => bY
def xX (d:cm) (us : List W) : List Bool :=
  match d with
  | .CD => FM us
  | .CF => bb++Gb us
def wj : b9→List Bool
  | .PL => bL
  | .P11 => [true,true]
def mI : List b9→List Bool
  | [] => []
  | p :: ps => wj p++mI ps
def rT (ps : List b9) : List Bool :=
  (bX++mI ps)++bL
def Dw (b:Bool) : List Bool :=
  if b then [true,false] else [true]
def nU : List Bool→List Bool
  | [] => []
  | b :: s => nU s++Dw b
@[simp] lemma GP : be bL = wL:=rfl
@[simp] lemma GS : be bX = wX:=rfl
@[simp] lemma DX : be bY = wY:=rfl
@[simp] lemma Bj : be ba = wa:=rfl
@[simp] lemma GR : be bb = wb:=rfl
@[simp] lemma Bt : be EQ = Ct:=rfl
@[simp] lemma Ae : be B8 = wo:=rfl
@[simp] lemma GC (us : List W) : be (FM us) = HD us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [FM,HD,Gh,za,← ih]
@[simp] lemma Gv (us : List W) : be (Gb us) = HF us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [Gb,HF,Gi,yT,← ih]
@[simp] lemma GQ (us : List W) : be (bG us) = G us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [bG,G,Hy,G1,← ih]
@[simp] lemma FA (d:cm) : be (bW d) = lX d := by
  cases d <;> rfl
@[simp] lemma n0 (d:cm) (us : List W) : be (xX d us) = oa d us := by
  cases d <;> simp [xX,oa]
@[simp] lemma CH (ps : List b9) : be (mI ps) = hE ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [mI,hE,wj,x0,yh,← ih]
@[simp] lemma v3 (ps : List b9) : be (rT ps) = b5 ps := by
  simp [rT,b5]
def lw : List Bool→List gQ
  | [] => []
  | b :: s => lw s++se b
lemma xT (l:ai) (s : List Bool) :
    bJ l s = bf l (lw s) := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    unfold bJ lw
    rw [ih,df]
lemma xQ (base : List gQ) (ps : List b9) (s : List Bool) (r:ai) :
    cE (FR (bf default ((base++b5 ps)++lw s)) r)
      (dU (bf default base)) := by
  rw [df,df,← xT]
  exact bh (jC (bf (bf default base) (b5 ps)) s .GoRight r)
    (lI ps (bf default base))
@[simp] lemma v2 (s : List Bool) : be (nU s) = lw s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp [nU,lw,Dw,se,yh,← ih]
def pD (q w : List Bool) : R:=⟨q.reverse,w,.qF⟩
def hG (q : List Bool) (s:ax) (w : List Bool) : R :=
  match q.reverse with
  | [] => ⟨[],false :: w,s⟩
  | a :: ls => ⟨ls,a :: w,s⟩
def jJ (qr w : List Bool) : R:=⟨qr,w,.qF⟩
def gh (qr : List Bool) (s:ax) (w : List Bool) : R :=
  match qr with
  | [] => ⟨[],false :: w,s⟩
  | a :: ls => ⟨ls,a :: w,s⟩
def xI (w : List Bool) : R:=⟨[],false :: false :: w,.qE⟩
lemma zO (q w : List Bool) (r:ai) :
    dC (pD q w) r = FR (bf default (be q)) (be w+>r) := by
  unfold dC pD sz dw FR bf
  simp [BJ]
lemma pF (q : List Bool) (s:ax) (w : List Bool) (r:ai) :
    dC (hG q s w) r = ((bf default (be q)) <{{BJ s}} (be w+>r)) := by
  unfold dC hG sz bf dw
  dsimp only
  rw [← sT]
  rcases q.reverse with _ | ⟨a,ls⟩ <;>
    simp only [y4,m7,yh,Bool.false_eq_true,↓reduceIte,
      append_cons,append_nil,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5]
lemma vW (qr w : List Bool) (r:ai) :
    dC (jJ qr w) r = FR (bf default (be qr.reverse)) (be w+>r) := by
  unfold dC jJ sz dw FR bf
  simp [BJ]
lemma w8 (qr : List Bool) (s:ax) (w : List Bool) (r:ai) :
    dC (gh qr s w) r = ((bf default (be qr.reverse)) <{{BJ s}} (be w+>r)) := by
  unfold dC gh sz bf dw
  dsimp only
  rw [← sT,List.reverse_reverse]
  rcases qr with _ | ⟨a,ls⟩ <;>
    simp only [y4,m7,yh,Bool.false_eq_true,↓reduceIte,
      append_cons,append_nil,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5]
lemma C9 (w : List Bool) (r:ai) :
    dC (xI w) r = CE (be w+>r):=rfl
inductive fZ where
  | Recovered (d:cm) (us : List W) (tail : List Bool)
  | NineGain (d:cm) (us : List W) (tail : List Bool)
  | SixGain (d:cm) (us : List W) (tail : List Bool)
  | YaaGain (tail : List Bool)
deriving DecidableEq
def j6 : fZ→List Bool
  | .Recovered d us tail => xX d us++tail
  | .NineGain d us tail => xX d us++EQ++tail
  | .SixGain d us tail => xX d us++B8++tail
  | .YaaGain tail => xX .CF [.UA,.UT]++bY++ba++ba++tail
def f0 (t:fZ) : R:=xI (j6 t)
def jj : fZ→Bool
  | .Recovered _ us _ => decide (3 ≤ us.length)
  | .NineGain _ us _ => decide (2 ≤ us.length)
  | .SixGain _ us _ => decide (2 ≤ us.length)
  | .YaaGain _ => true
lemma nP (t:fZ) (h : jj t = true) (r:ai) :
    cE (dC (f0 t) r) lr := by
  unfold f0
  rw [C9]
  cases t with
  | Recovered d us tail =>
    have hlen : 3 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,n0,append_assoc]
    exact dg ⟨d,us,be tail+>r,hlen,rfl⟩
  | NineGain d us tail =>
    have hlen : 2 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,n0,Bt,append_assoc]
    exact ye d us (be tail+>r) hlen
  | SixGain d us tail =>
    have hlen : 2 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,n0,Ae,append_assoc]
    exact ze d us (be tail+>r) hlen
  | YaaGain tail =>
    unfold j6
    simp only [jF,n0,DX,Bj]
    have heq : (oa .CF [.UA,.UT]++wY++wa++wa++be tail)+>r =
        oa .CF [.UA,.UT]+>((wY++wa++wa)+>(be tail+>r)) := by
      simp only [append_assoc]
    rw [heq]
    exact Ap (be tail+>r)
structure mB where
  guard_base : List Bool
  guard_pieces : List b9
  guard_stack : List Bool
  guard_D_steps : Nat
  guard_D_terminal : fZ
  guard_F_steps : Nat
  guard_F_terminal : fZ
deriving DecidableEq
def uz (g:mB) : List Bool :=
  (g.guard_base++rT g.guard_pieces)++nU g.guard_stack
noncomputable def nV (g:mB) : Bool :=
  jj g.guard_D_terminal &&
  jj g.guard_F_terminal &&
  eO g.guard_D_steps (hG g.guard_base .qD ba) (f0 g.guard_D_terminal) &&
  eO g.guard_F_steps (hG g.guard_base .qF ([false,false,false]++ba)) (f0 g.guard_F_terminal)
lemma Bu (g:mB) (h : nV g = true) (r:ai) :
    cE (FR (bf default (be (uz g))) r) lr := by
  unfold nV at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hd,hf⟩,nd⟩,nf⟩
  unfold uz
  simp only [jF,v3,v2]
  refine bh (xQ (be g.guard_base) g.guard_pieces g.guard_stack r) ?_
  intro c hc
  cases hc with
  | strong_D r0 =>
    have hnat:=gi g.guard_D_steps (hG g.guard_base .qD ba) (f0 g.guard_D_terminal) nd r0
    rw [pF] at hnat
    dsimp only [BJ,Bj] at hnat
    exact cc hnat (nP g.guard_D_terminal hd r0)
  | strong_F r0 =>
    have hnat:=gi g.guard_F_steps (hG g.guard_base .qF ([false,false,false]++ba)) (f0 g.guard_F_terminal) nf r0
    rw [pF] at hnat
    have h000 : be ([false,false,false]++ba)+>r0 = [0,0,0]+>(wa+>r0) := by
      simp [append_assoc,yh]
    dsimp only [BJ] at hnat
    rw [h000] at hnat
    exact cc hnat (nP g.guard_F_terminal hf r0)
inductive k1 where
  | AllCases | Cases00 | Cases1 | Coarse00 | Coarse10 | Coarse11
deriving DecidableEq
def iW : k1→List (bR × List gQ)
  | .AllCases => vT
  | .Cases00 => pN
  | .Cases1 => Ac
  | .Coarse00 => xR
  | .Coarse10 => Bk
  | .Coarse11 => Cu
def so : k1→List (bR × List Bool)
  | .AllCases => [(.RD,[]),(.RF,[false,false]),(.RB,[false,false])]
  | .Cases00 => [(.RD,[true,false,true]),(.RD,[true,true,true,false,true]),(.RD,[true,false,true,false,false]),(.RF,[false,false,false])]
  | .Cases1 => [(.RD,[true,true,false,true]),(.RD,[false,true,false,false]),(.RF,[false,false]),(.RB,[false,false])]
  | .Coarse00 => [(.RD,[]),(.RF,[false,false])]
  | .Coarse10 => [(.RD,[]),(.RB,[false,false])]
  | .Coarse11 => [(.RF,[false,false])]
lemma vJ (s:k1) :
    (so s).map (fun e => (e.1,be e.2)) = iW s := by
  cases s <;> rfl
noncomputable def kq (s:k1) (w : List Bool) : Bool :=
  match s with
  | .AllCases => true
  | .Cases00 => lp w [false,false]
  | .Cases1 => lp w [true]
  | .Coarse00 => lp (w.take 2) [false,false]
  | .Coarse10 => lp (w.take 2) [true,false]
  | .Coarse11 => lp (w.take 2) [true,true]
lemma zk (s:k1) (w : List Bool) (h : kq s w = true) (l r:ai) :
    fl (FR l (be w+>r)) (ic l (iW s)) := by
  cases s with
  | AllCases => exact Bv l (be w+>r)
  | Cases00 =>
    unfold kq at h; rw [oF] at h; subst h
    exact x2 l r
  | Cases1 =>
    unfold kq at h; rw [oF] at h; subst h
    exact CX l r
  | Coarse00 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,yh,Bool.false_eq_true,↓reduceIte,← append_assoc] using! xm l (be w'+>r)
  | Coarse10 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,yh,Bool.false_eq_true,↓reduceIte,← append_assoc] using! w5 l (be w'+>r)
  | Coarse11 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,yh,Bool.false_eq_true,↓reduceIte,← append_assoc] using! wv l (be w'+>r)
def nz : bR→ax
  | .RD => .qD
  | .RF => .qF
  | .RB => .qB
def GB : bR→Fin 6
  | .RD => sD
  | .RF => sF
  | .RB => sB
@[simp] lemma yd (s:bR) : BJ (nz s) = GB s := by
  cases s <;> rfl
inductive Pos where
  | Z : Pos
  | O : Pos→Pos
  | E : Pos→Pos
deriving DecidableEq
def Fl : bR→bR→Bool
  | .RD,.RD | .RF,.RF | .RB,.RB => true
  | _,_ => false
lemma CN (x y:bR) : Fl x y = true↔x = y := by
  cases x <;> cases y <;> decide
structure py where
  state : bR
  pref : List Bool
  steps : Nat
  target : Pos
  prep : List Bool
deriving DecidableEq
noncomputable def su (e : bR × List Bool) (b:py) : Bool :=
  Fl e.1 b.state&&lp e.2 b.pref
noncomputable def yq (s:k1) (bs : List py) : Bool :=
  (so s).all (fun e => bs.any (su e))
lemma yi (s:k1) (bs : List py) (e : bR × List gQ)
    (hc : yq s bs = true) (hin : e ∈ iW s) :
    ∃ b ∈ bs,e.1 = b.state∧e.2 = be b.pref := by
  rw [← vJ s,List.mem_map] at hin
  rcases hin with ⟨⟨st,p⟩,hp,rfl⟩
  unfold yq at hc
  have h1:=List.all_eq_true.mp hc (st,p) hp
  rcases List.any_eq_true.mp h1 with ⟨b,hb,hm⟩
  unfold su at hm
  simp only [Bool.and_eq_true,CN,oF] at hm
  exact ⟨b,hb,hm.1,by rw [hm.2]⟩
inductive dp where
  | rEnd (t:fZ)
  | rProt (gc:mB) (w : List Bool)
  | rNat (fin:R) (steps:Nat) (target:Pos) (prep : List Bool)
  | rRet (qr w : List Bool) (s:k1) (bs : List py)
def F4 (t:fZ) : R:=f0 t
def CC (gc:mB) (w : List Bool) : R:=pD (uz gc) w
def F2 (fin:R) (_:Nat) (_:Pos) (_ : List Bool) : R:=fin
def DH (qr w : List Bool) (_:k1) (_ : List py) : R:=jJ qr w
noncomputable def fw (r:dp) : R :=
  dp.rec (motive:=fun _ => R) F4 CC F2 DH r
def Ec (p : List Bool) (xp xf : List Bool) (xs:ax) : R :=
  ⟨xp,xf++p,xs⟩
noncomputable def jE (p : List Bool) (x:R) : R :=
  R.rec (motive:=fun _ => R) (Ec p) x
lemma nR (p : List Bool) (x:R) (r:ai) :
    dC (jE p x) r = dC x (be p+>r) := by
  rcases x with ⟨xp,xf,xs⟩
  change dC ⟨xp,xf++p,xs⟩ r = dC ⟨xp,xf,xs⟩ (be p+>r)
  unfold dC dw sz
  simp only [jF,append_assoc]
inductive ab (α : Type) where
  | empty : ab α
  | node : Option α→ab α→ab α→ab α
def zi (v : Option α) (_ _ : ab α) (_ _ : Option α) : Option α:=v
noncomputable def Ce (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => Option α) none zi t
def vL (_ : ab α→Option α) : Option α:=none
def zs (_ : Option α) (l _ : ab α) (_ _ : (ab α→Option α)→Option α) (ih : ab α→Option α) : Option α:=ih l
def AM (_ : Option α) (_ r : ab α) (_ _ : (ab α→Option α)→Option α) (ih : ab α→Option α) : Option α:=ih r
noncomputable def BS (_:Pos) (ih : ab α→Option α) (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => (ab α→Option α)→Option α) vL zs t ih
noncomputable def B7 (_:Pos) (ih : ab α→Option α) (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => (ab α→Option α)→Option α) vL AM t ih
noncomputable def ig (t : ab α) (p:Pos) : Option α :=
  Pos.rec (motive:=fun _ => ab α→Option α)
    Ce
    BS
    B7
    p t
def n7 (_ : α→Bool) (ihl ihr:Bool) : Bool:=ihl&&ihr
def oA (x : α) (p : α→Bool) (ihl ihr:Bool) : Bool:=p x&&ihl&&ihr
noncomputable def me (p : α→Bool) (v : Option α) (_ _ : ab α) (ihl ihr:Bool) : Bool :=
  Option.rec (motive:=fun _ => (α→Bool)→Bool→Bool→Bool)
    n7
    oA
    v p ihl ihr
noncomputable def ay (p : α→Bool) (t : ab α) : Bool :=
  ab.rec (motive:=fun _ => Bool) true (me p) t
lemma AZ {p : α→Bool} {t : ab α} {i : Pos} {x : α}
    (hall : ay p t = true) (hget : ig t i = some x) : p x = true := by
  induction i generalizing t with
  | Z =>
    cases t with
    | empty => contradiction
    | node v l r =>
      change v = some x at hget
      subst hget
      change (p x&&ay p l&&ay p r) = true at hall
      simp only [Bool.and_eq_true] at hall
      exact hall.1.1
  | O i ih =>
    cases t with
    | empty => contradiction
    | node v l r =>
      change ig l i = some x at hget
      change me p v l r (ay p l) (ay p r) = true at hall
      have hl : ay p l = true := by
        cases v <;> simp only [me,n7,oA,Bool.and_eq_true] at hall <;> tauto
      exact ih hl hget
  | E i ih =>
    cases t with
    | empty => contradiction
    | node v l r =>
      change ig r i = some x at hget
      change me p v l r (ay p l) (ay p r) = true at hall
      have hr : ay p r = true := by
        cases v <;> simp only [me,n7,oA,Bool.and_eq_true] at hall <;> tauto
      exact ih hr hget
def vO (_:Nat) (_:R) (_ : List Bool) : Bool:=false
noncomputable def v0 (y:dp) (steps:Nat) (fin:R) (prep : List Bool) : Bool :=
  eO steps fin (jE prep (fw y))
noncomputable def mN (opt_y : Option dp) (steps:Nat) (fin:R) (prep : List Bool) : Bool :=
  Option.rec (motive:=fun _ => Nat→R→List Bool→Bool)
    vO
    v0
    opt_y steps fin prep
noncomputable def Ee (g : ab dp) (qr : List Bool)
    (state:bR) (pref : List Bool) (steps:Nat) (target:Pos) (prep : List Bool) : Bool :=
  mN (ig g target) steps (gh qr (nz state) pref) prep
noncomputable def pC (g : ab dp) (qr : List Bool) (b:py) : Bool :=
  py.rec (motive:=fun _ => Bool) (Ee g qr) b
def F9 (t:fZ) (_ : ab dp) : Bool:=jj t
noncomputable def EG (gc:mB) (_ : List Bool) (_ : ab dp) : Bool:=nV gc
noncomputable def FN (fin:R) (steps:Nat) (target:Pos) (prep : List Bool) (g : ab dp) : Bool :=
  mN (ig g target) steps fin prep
noncomputable def FS (qr w : List Bool) (s:k1) (bs : List py) (g : ab dp) : Bool :=
  kq s w&&yq s bs&&bs.all (pC g qr)
noncomputable def sg (g : ab dp) (r:dp) : Bool :=
  dp.rec (motive:=fun _ => ab dp→Bool)
    F9 EG FN FS r g
lemma Bm (g : ab dp) (hg : ay (sg g) g = true) :
    ∀ (i:Pos) (x:dp),ig g i = some x→∀ r,cE (dC (fw x) r) lr := by
  intro i x hx r n hn
  induction n using Nat.strong_induction_on generalizing i x r with
  | h n ih =>
    have hchk : sg g x = true:=AZ hg hx
    cases x with
    | rEnd t =>
      change jj t = true at hchk
      exact nP t hchk r n hn
    | rProt gc w =>
      change nV gc = true at hchk
      unfold fw CC at hn
      rw [zO] at hn
      exact Bu gc hchk (be w+>r) n hn
    | rNat fin steps target prep =>
      change mN (ig g target) steps fin prep = true at hchk
      rcases hy : ig g target with _ | y
      · rw [hy] at hchk; contradiction
      · rw [hy] at hchk
        change eO steps fin (jE prep (fw y)) = true at hchk
        have hp:=gi steps fin (jE prep (fw y)) hchk r
        rw [nR] at hp
        rcases kz hp hn with ⟨m,hmn,hm⟩
        rcases ih m hmn target y hy (be prep+>r) hm with ⟨k,d,hkm,hsafe,hk⟩
        exact ⟨k,d,by omega,hsafe,hk⟩
    | rRet qr w s bs =>
      change (kq s w&&yq s bs&&bs.all (pC g qr)) = true at hchk
      simp only [Bool.and_eq_true] at hchk
      rcases hchk with ⟨⟨hs,hc⟩,hbs⟩
      unfold fw DH at hn
      rw [vW] at hn
      rcases zk s w hs (bf default (be qr.reverse)) r n hn with ⟨m,c,hmn,hret,hm⟩
      rcases hret with ⟨e,p,r',hin,rfl⟩
      rcases yi s bs (e,p) hc hin with ⟨b,hb,he,hp⟩
      dsimp only at he hp; subst he hp
      have hbv : pC g qr b = true:=List.all_eq_true.mp hbs b hb
      rcases b with ⟨b_state,b_pref,b_steps,b_target,b_prep⟩
      change mN (ig g b_target) b_steps (gh qr (nz b_state) b_pref) b_prep = true at hbv
      rcases hy : ig g b_target with _ | y
      · rw [hy] at hbv; contradiction
      · rw [hy] at hbv
        change eO b_steps (gh qr (nz b_state) b_pref) (jE b_prep (fw y)) = true at hbv
        have hnat:=gi b_steps (gh qr (nz b_state) b_pref) (jE b_prep (fw y)) hbv r'
        rw [w8,yd,nR] at hnat
        have hret_step : (jY b_state (bf default (be qr.reverse)) (be b_pref+>r')) [tm]⊢⁺ (dC (fw y) (be b_prep+>r')) := by
          revert hnat; cases b_state <;> intro hnat <;> exact hnat
        rcases kz hret_step hm with ⟨a,ham,ha⟩
        rcases ih a (by omega) b_target y hy (be b_prep+>r') ha with ⟨z,d,hza,hsafe,hz⟩
        exact ⟨z,d,by omega,hsafe,hz⟩
def j9 : W→List b9
  | .UA => [.PL]
  | .UT => [.P11,.P11,.PL]
lemma Gx (u:W) : G1 u++wX = b5 (j9 u) := by
  cases u <;> rfl
lemma C2 (u:W) : G [u,.UA] = b5 (j9 u) := by
  cases u <;> rfl
lemma C4 (u:W) : G [u,.UT] = b5 (j9 u)++wY := by
  cases u <;> rfl
lemma A5 (u v:W) (l:ai) (c:aL)
    (h : ip (bf l (G [u,v])) c) : cE c (dU l) := by
  cases v
  · rw [C2] at h
    exact lI (j9 u) l c h
  · rw [C4,df] at h
    have hstack (e:BA) (r0:ai) :
        cE (aq (bf l (b5 (j9 u))) [false,false,false,false] e r0) (dU l) :=
      bh (jC (bf l (b5 (j9 u))) [false,false,false,false] e r0)
        (lI (j9 u) l)
    cases h with
    | contact_D r0 => exact hstack .FromD r0
    | contact_F r0 => exact hstack .FromF r0
    | contact_B r0 => exact hstack .FromB r0
lemma x4 (d:cm) (us vs : List W) :
    cn d (us++vs) = bf (cn d us) (G vs) := by
  unfold cn
  rw [Gt,← List.append_assoc,df]
lemma Bq (d:cm) (us : List W) (u:W) :
    cn d (us++[u]) = bf (cn d us) (G1 u) := by
  rw [x4]
  simp [G]
lemma Cf (d:cm) (a b c e:W) (r:ai) :
    fl (hF d [a,b,c,e] r) lr := by
  refine cr (tj d [a,b,c,e] r) ?_
  have hf : cn d [a,b,c,e] = bf (cn d [a,b]) (G [c,e]) :=
    x4 d [a,b] [c,e]
  rw [hf]
  refine bh (fv (bf (cn d [a,b]) (G [c,e])) ([0]+>r)) ?_
  intro x hx
  refine bh (A5 c e (cn d [a,b]) x hx) ?_
  intro y hy
  refine bh (hN d [a,b] y hy) ?_
  intro z hz
  exact dg (i8 d [a,b] z (by simp) hz)
lemma Ge (u:W) (l r:ai) :
    (DL (bf l (G1 u)) r) [tm]⊢⁺ (DL l (wa+>((match u with | .UA => [] | .UT => wY)+>r))) := by
  cases u
  · simpa only [G1,append_nil] using! G6 l r
  · simpa only [G1,append_assoc] using!
      U 13 ⟨(wX++wY).reverse,[],sD,true⟩ ⟨[],wa++wY,sD,true⟩ (by decide) l r
lemma Ei (l r:ai) :
    (FL (bf l (G1 .UA)) ([0,0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>r))) :=
  Dx l r
lemma D9 (l r:ai) :
    (FL (bf l (G1 .UT)) ([0,0,0]+>r)) [tm]⊢⁺ (FR (bf l (b5 [.P11])) ([0,0]+>r)) :=
  U 1 ⟨(wX++wY).reverse,[0,0,0],sF,true⟩ ⟨(b5 [.P11]).reverse,[0,0],sF,false⟩ (by decide) l r
lemma A8 (d:cm) (us : List W) (u:W) (c:aL)
    (h : dA (bf (cn d us) (G1 u)) c)
    (h1 : ∀ r,cE (BL (bf (cn d us) (G1 u)) ([0,0,1,0,1]+>r)) lr)
    (h2 : ∀ r,cE (BL (bf (cn d us) (G1 u)) ([0,0,1,1,1,0,1]+>r)) lr)
    (hlen : 2 ≤ us.length) : cE c lr := by
  cases h with
  | phase_D r =>
    refine cc (Ge u (cn d us) r) ?_
    refine bh (hN d us _ (.strong_D _)) ?_
    intro e he
    exact dg (i8 d us e hlen he)
  | phase_F r =>
    cases u
    · refine cc (Ei (cn d us) r) ?_
      refine bh (hN d us _ (.strong_F _)) ?_
      intro e he
      exact dg (i8 d us e hlen he)
    · refine cc (D9 (cn d us) r) ?_
      refine bh (r8 [.P11] (cn d us) ([0,0]+>r)) ?_
      intro e he
      refine bh (hN d us e he) ?_
      intro f hf
      exact dg (i8 d us f hlen hf)
  | phase_B101 r => exact h1 r
  | phase_B11101 r => exact h2 r
def r9 : Prop:=∀ d a b c r,
  cE (BL (cn d [a,b,c]) ([0,0,1,0,1]+>r)) lr ∧
  cE (BL (cn d [a,b,c]) ([0,0,1,1,1,0,1]+>r)) lr
lemma Bx (hb:r9) (d:cm) (a b c:W) (r:ai) :
    fl (hF d [a,b,c] r) lr := by
  refine cr (tj d [a,b,c] r) ?_
  refine bh (uR (cn d [a,b,c]) r) ?_
  intro x hx
  have hsnoc : cn d [a,b,c] = bf (cn d [a,b]) (G1 c) :=
    Bq d [a,b] c
  rw [hsnoc] at hx
  refine A8 d [a,b] c x hx ?_ ?_ (by simp)
  · intro r'; rw [← hsnoc]; exact (hb d a b c r').1
  · intro r'; rw [← hsnoc]; exact (hb d a b c r').2
lemma Bz (d:cm) (us vs : List W) (r:ai) :
    hF d (us++vs) r = hF d us ((match d with | .CD => HD vs | .CF => HF vs)+>r) := by
  cases d <;> simp [hF,oa,F0,F7,append_assoc]
lemma zb (hb:r9) (c:aL) (hs : lr c) : fl c lr := by
  rcases hs with ⟨d,us,r,hlen,rfl⟩
  rcases us with _ | ⟨a,_ | ⟨b,_ | ⟨e,_ | ⟨f,us'⟩⟩⟩⟩
  · contradiction
  · contradiction
  · contradiction
  · exact Bx hb d a b e r
  · have h4 : [a,b,e,f]++us' = a :: b :: e :: f :: us':=rfl
    rw [← h4,Bz]
    exact Cf d a b e f _
lemma AU (hb:r9) (c:aL) (hs : lr c) (n:Nat) : ¬ d7 c n :=
  q3 (zb hb) n c hs
lemma CZ :
    (init []) [tm]⊢* (hF .CD [.UA,.UT,.UT] ([1,0,1]+>default)) := by
  have h0 : init [] = dw ⟨[],([0] : List gQ) ^ 19,A⟩ default := by
    have hz : (([0] : List gQ) ^ 19)+>default = default:=qZ (by decide)
    unfold init dw
    rw [append_nil,hz]
    rfl
  have hrun:=kC 405
    ⟨[],([0] : List gQ) ^ 19,A⟩
    ⟨[],[0,0]++oa .CD [.UA,.UT,.UT]++[1,0,1],sE⟩
    (by decide) default
  rw [h0]
  refine V ?_
  simpa only [dw,hF,CE,append_assoc] using! hrun
abbrev Y:=List Bool
abbrev U_:=List W
abbrev M_:=List b9
abbrev T_:=ab dp
def cD : cm:=.CD
def cF : cm:=.CF
def Iu : ab dp:=.empty
def nd (x:dp) (l r : ab dp) : ab dp:=.node (some x) l r
def aZ (x:dp) (l : ab dp) : ab dp:=.node (some x) l .empty
def Iv (x:dp) (r : ab dp) : ab dp:=.node (some x) .empty r
def lf (x:dp) : ab dp:=.node (some x) .empty .empty
def z0:Pos:=.Z
def z1:Pos:=.O z0
def z2:Pos:=.E z0
def z3:Pos:=.O z1
def z4:Pos:=.E z1
def z5:Pos:=.O z2
def z6:Pos:=.E z2
def z7:Pos:=.O z3
def z8:Pos:=.E z3
def z9:Pos:=.O z4
def dn:Pos:=.E z4
def c5:Pos:=.O z5
def cG:Pos:=.E z5
def cM:Pos:=.O z6
def cq:Pos:=.E z6
def cP:Pos:=.O z7
def cy:Pos:=.E z7
def ct:Pos:=.O z8
def cB:Pos:=.E z8
def cV:Pos:=.O z9
def dy:Pos:=.E z9
def c9:Pos:=.O dn
def dj:Pos:=.E dn
def dP:Pos:=.O c5
def di:Pos:=.E c5
def da:Pos:=.O cG
def cA:Pos:=.E cG
def cS:Pos:=.O cM
def cI:Pos:=.E cM
def c8:Pos:=.O cq
def cN:Pos:=.E cq
def c7:Pos:=.O cP
def c0:Pos:=.E cP
def dI:Pos:=.O cy
def dr:Pos:=.E cy
def ds:Pos:=.O ct
def dT:Pos:=.E ct
def c6:Pos:=.O cB
def dl:Pos:=.E cB
def dL:Pos:=.O cV
def cO:Pos:=.E cV
def dM:Pos:=.O dy
def cL:Pos:=.E dy
def cU:Pos:=.O c9
def cT:Pos:=.E c9
def dq:Pos:=.O dj
def dY:Pos:=.E dj
def d9:Pos:=.O dP
def d1:Pos:=.E dP
def FO:Pos:=.O di
def Gs:Pos:=.E di
def GN:Pos:=.O da
def Gw:Pos:=.E da
def Gz:Pos:=.O cA
def GJ:Pos:=.E cA
def Gq:Pos:=.O cS
def GI:Pos:=.E cS
def GG:Pos:=.O cI
def Gc:Pos:=.E cI
def Fz:Pos:=.O c8
def F3:Pos:=.E c8
def FU:Pos:=.O cN
def GD:Pos:=.E cN
def Hz:Pos:=.O c7
def H0:Pos:=.E c7
def HP:Pos:=.O c0
def HY:Pos:=.E c0
def HK:Pos:=.O dI
def HX:Pos:=.E dI
def HQ:Pos:=.O dr
def Ik:Pos:=.E dr
def Ie:Pos:=.O ds
def Id:Pos:=.E ds
def HJ:Pos:=.O dT
def HR:Pos:=.E dT
def H8:Pos:=.O c6
def HL:Pos:=.E c6
def HE:Pos:=.O dl
def Ig:Pos:=.E dl
def HN:Pos:=.O dL
def HS:Pos:=.E dL
def H2:Pos:=.O cO
def HH:Pos:=.E cO
def G2:Pos:=.O dM
def Hu:Pos:=.E dM
def Ho:Pos:=.O cL
def HG:Pos:=.E cL
def HW:Pos:=.O cU
def HI:Pos:=.E cU
def HU:Pos:=.O cT
def Ib:Pos:=.E cT
def HC:Pos:=.O dq
def H6:Pos:=.E dq
def H5:Pos:=.O dY
def H9:Pos:=.E dY
def Ij:Pos:=.O d9
def H3:Pos:=.E d9
def Ic:Pos:=.O d1
def H7:Pos:=.E d1
def HZ:Pos:=.O FO
def Hk:Pos:=.E FO
def G4:Pos:=.O Gs
def Hs:Pos:=.E Gs
def Hv:Pos:=.O GN
def GW:Pos:=.E GN
def Hi:Pos:=.O Gw
def Hj:Pos:=.E Gw
def Hx:Pos:=.O Gz
def Hp:Pos:=.E Gz
def GY:Pos:=.O GJ
def G8:Pos:=.E GJ
def G9:Pos:=.O Gq
def Gl:Pos:=.E Gq
def Hr:Pos:=.O GI
def GV:Pos:=.E GI
def Hg:Pos:=.O GG
def G5:Pos:=.E GG
def He:Pos:=.O Gc
def GU:Pos:=.E Gc
def Ht:Pos:=.O Fz
def Hn:Pos:=.E Fz
def Hq:Pos:=.O F3
def G3:Pos:=.E F3
def G0:Pos:=.O FU
def Hb:Pos:=.E FU
def Go:Pos:=.O GD
def Hl:Pos:=.E GD
def vE(p:Pos):Pos:=.E (.E (.E p))
def vH(p:Pos):Pos:=.O (.E (.E p))
def vB(p:Pos):Pos:=.E (.O (.E p))
def vy(p:Pos):Pos:=.O (.O (.E p))
def vD(p:Pos):Pos:=.E (.E (.O p))
def vx(p:Pos):Pos:=.O (.E (.O p))
def vA(p:Pos):Pos:=.E (.O (.O p))
def vI(p:Pos):Pos:=.O (.O (.O p))
namespace Pos
def p0(p:Pos):Pos:=vE (vE p)
def p1(p:Pos):Pos:=vH (vE p)
def p2(p:Pos):Pos:=vB (vE p)
def p3(p:Pos):Pos:=vy (vE p)
def p4(p:Pos):Pos:=vD (vE p)
def p5(p:Pos):Pos:=vx (vE p)
def p6(p:Pos):Pos:=vA (vE p)
def p7(p:Pos):Pos:=vI (vE p)
def p8(p:Pos):Pos:=vE (vH p)
def p9(p:Pos):Pos:=vH (vH p)
def gL(p:Pos):Pos:=vB (vH p)
def hH(p:Pos):Pos:=vy (vH p)
def f5(p:Pos):Pos:=vD (vH p)
def gj(p:Pos):Pos:=vx (vH p)
def ga(p:Pos):Pos:=vA (vH p)
def f9(p:Pos):Pos:=vI (vH p)
def eA(p:Pos):Pos:=vE (vB p)
def gn(p:Pos):Pos:=vH (vB p)
def fx(p:Pos):Pos:=vB (vB p)
def fM(p:Pos):Pos:=vy (vB p)
def gd(p:Pos):Pos:=vD (vB p)
def gb(p:Pos):Pos:=vx (vB p)
def fq(p:Pos):Pos:=vA (vB p)
def gv(p:Pos):Pos:=vI (vB p)
def fC(p:Pos):Pos:=vE (vy p)
def gm(p:Pos):Pos:=vH (vy p)
def gH(p:Pos):Pos:=vB (vy p)
def fm(p:Pos):Pos:=vy (vy p)
def eS(p:Pos):Pos:=vD (vy p)
def eY(p:Pos):Pos:=vx (vy p)
def gg(p:Pos):Pos:=vA (vy p)
def fL(p:Pos):Pos:=vI (vy p)
def ex(p:Pos):Pos:=vE (vD p)
def fN(p:Pos):Pos:=vH (vD p)
def fK(p:Pos):Pos:=vB (vD p)
def ez(p:Pos):Pos:=vy (vD p)
def eu(p:Pos):Pos:=vD (vD p)
def fA(p:Pos):Pos:=vx (vD p)
def fT(p:Pos):Pos:=vA (vD p)
def eB(p:Pos):Pos:=vI (vD p)
def er(p:Pos):Pos:=vE (vx p)
def gk(p:Pos):Pos:=vH (vx p)
def e1(p:Pos):Pos:=vB (vx p)
def gl(p:Pos):Pos:=vy (vx p)
def fz(p:Pos):Pos:=vD (vx p)
def f8(p:Pos):Pos:=vx (vx p)
def eH(p:Pos):Pos:=vA (vx p)
def eW(p:Pos):Pos:=vI (vx p)
def fi(p:Pos):Pos:=vE (vA p)
def fU(p:Pos):Pos:=vH (vA p)
def fo(p:Pos):Pos:=vB (vA p)
def eZ(p:Pos):Pos:=vy (vA p)
def ev(p:Pos):Pos:=vD (vA p)
def gO(p:Pos):Pos:=vx (vA p)
def fu(p:Pos):Pos:=vA (vA p)
def fD(p:Pos):Pos:=vI (vA p)
def fE(p:Pos):Pos:=vE (vI p)
def f4(p:Pos):Pos:=vH (vI p)
def ft(p:Pos):Pos:=vB (vI p)
def fp(p:Pos):Pos:=vy (vI p)
def gK(p:Pos):Pos:=vD (vI p)
def fP(p:Pos):Pos:=vx (vI p)
def f6(p:Pos):Pos:=vA (vI p)
def e7(p:Pos):Pos:=vI (vI p)
end Pos
def e_:Y:=[]
def bd:Y:=false::e_
def b1:Y:=true::e_
def aP:Y:=false::bd
def aE:Y:=false::b1
def fY:Y:=true::bd
def jN:Y:=true::b1
def Gu:Y:=false::aP
def aw:Y:=false::fY
def jH:Y:=false::jN
def j:Y:=true::aP
def H:Y:=true::aE
def vV:Y:=true::fY
def xP:Y:=true::jN
def F6:Y:=false::aw
def FY:Y:=false::jH
def L:Y:=false::j
def au:Y:=false::H
def xq:Y:=false::vV
def FQ:Y:=false::xP
def F1:Y:=true::Gu
def bt:Y:=true::aw
def px:Y:=true::jH
def h9:Y:=true::j
def K:Y:=true::H
def yr:Y:=true::vV
def pr:Y:=true::xP
def af:Y:=false::L
def aA:Y:=false::au
def k9:Y:=false::bt
def kW:Y:=false::px
def hj:Y:=false::h9
def ak:Y:=false::K
def ok:Y:=false::pr
def EV:Y:=true::F6
def aU:Y:=true::L
def ci:Y:=true::au
def rx:Y:=true::xq
def E5:Y:=true::FQ
def bq:Y:=true::bt
def yR:Y:=true::px
def ah:Y:=true::K
def oG:Y:=true::yr
def yM:Y:=true::pr
def br:Y:=false::af
def bj:Y:=false::ak
def El:Y:=false::ok
def Ef:Y:=false::EV
def ad:Y:=false::aU
def dO:Y:=false::ci
def hO:Y:=false::bq
def X:Y:=false::ah
def vg:Y:=false::oG
def ie:Y:=true::af
def iZ:Y:=true::aA
def mE:Y:=true::k9
def kx:Y:=true::kW
def aH:Y:=true::hj
def dN:Y:=true::ak
def Bb:Y:=true::ok
def eM:Y:=true::aU
def dV:Y:=true::ci
def pK:Y:=true::rx
def Bh:Y:=true::E5
def aN:Y:=true::bq
def D7:Y:=true::yR
def dZ:Y:=true::ah
def xS:Y:=true::oG
def Bg:Y:=true::yM
def dD:Y:=false::ad
def Dq:Y:=false::hO
def aB:Y:=false::X
def b3:Y:=false::ie
def e4:Y:=false::iZ
def vZ:Y:=false::mE
def Dn:Y:=false::kx
def bO:Y:=false::aH
def cg:Y:=false::dN
def zq:Y:=false::Bb
def gN:Y:=false::eM
def vU:Y:=false::dV
def vP:Y:=false::pK
def vR:Y:=false::Bh
def b4:Y:=false::aN
def Da:Y:=false::D7
def lq:Y:=false::dZ
def ao:Y:=true::br
def ar:Y:=true::bj
def CO:Y:=true::El
def C5:Y:=true::Ef
def cC:Y:=true::ad
def e3:Y:=true::dO
def v1:Y:=true::hO
def aV:Y:=true::X
def Dm:Y:=true::vg
def my:Y:=true::mE
def iE:Y:=true::kx
def op:Y:=true::aH
def rS:Y:=true::dN
def ea:Y:=true::eM
def gf:Y:=true::dV
def gS:Y:=true::aN
def bK:Y:=true::dZ
def yx:Y:=true::xS
def Im(t:Y):Y:=false::false::false::false::t
def wp(t:Y):Y:=true::false::false::false::t
def mx(t:Y):Y:=false::true::false::false::t
def wT(t:Y):Y:=true::true::false::false::t
def po(t:Y):Y:=false::false::true::false::t
def js(t:Y):Y:=true::false::true::false::t
def kU(t:Y):Y:=false::true::true::false::t
def lv(t:Y):Y:=true::true::true::false::t
def x1(t:Y):Y:=false::false::false::true::t
def mS(t:Y):Y:=true::false::false::true::t
def kd(t:Y):Y:=false::true::false::true::t
def jM(t:Y):Y:=true::true::false::true::t
def pZ(t:Y):Y:=false::false::true::true::t
def ks(t:Y):Y:=true::false::true::true::t
def nI(t:Y):Y:=false::true::true::true::t
def kI(t:Y):Y:=true::true::true::true::t
def _root_.List.sy(t:Y):Y:=wp (wp t)
def _root_.List.wi(t:Y):Y:=mx (wp t)
def _root_.List.If(t:Y):Y:=po (wp t)
def _root_.List.Hc(t:Y):Y:=js (wp t)
def _root_.List.G7(t:Y):Y:=kU (wp t)
def _root_.List.Do(t:Y):Y:=lv (wp t)
def _root_.List.GO(t:Y):Y:=kd (wp t)
def _root_.List.iG(t:Y):Y:=mx (mx t)
def _root_.List.GK(t:Y):Y:=wT (mx t)
def _root_.List.hU(t:Y):Y:=js (mx t)
def _root_.List.AY(t:Y):Y:=mS (mx t)
def _root_.List.wk(t:Y):Y:=kd (mx t)
def _root_.List.o6(t:Y):Y:=jM (mx t)
def _root_.List.A3(t:Y):Y:=pZ (mx t)
def _root_.List.xE(t:Y):Y:=ks (mx t)
def _root_.List.vS(t:Y):Y:=nI (mx t)
def _root_.List.mu(t:Y):Y:=kI (mx t)
def _root_.List.H4(t:Y):Y:=po (wT t)
def _root_.List.A7(t:Y):Y:=js (wT t)
def _root_.List.yk(t:Y):Y:=lv (wT t)
def _root_.List.zh(t:Y):Y:=po (po t)
def _root_.List.hM(t:Y):Y:=js (po t)
def _root_.List.ya(t:Y):Y:=kU (po t)
def _root_.List.Gd(t:Y):Y:=x1 (po t)
def _root_.List.Eg(t:Y):Y:=mS (po t)
def _root_.List.nj(t:Y):Y:=kd (po t)
def _root_.List.hK(t:Y):Y:=jM (po t)
def _root_.List.jd(t:Y):Y:=mx (js t)
def _root_.List.vz(t:Y):Y:=wT (js t)
def _root_.List.bi(t:Y):Y:=js (js t)
def _root_.List.bg(t:Y):Y:=kU (js t)
def _root_.List.cJ(t:Y):Y:=lv (js t)
def _root_.List.kY(t:Y):Y:=mS (js t)
def _root_.List.aD(t:Y):Y:=kd (js t)
def _root_.List.b8(t:Y):Y:=jM (js t)
def _root_.List.pE(t:Y):Y:=pZ (js t)
def _root_.List.bm(t:Y):Y:=ks (js t)
def _root_.List.ja(t:Y):Y:=nI (js t)
def _root_.List.bu(t:Y):Y:=kI (js t)
def _root_.List.fr(t:Y):Y:=po (kU t)
def _root_.List.xM(t:Y):Y:=js (kU t)
def _root_.List.mX(t:Y):Y:=kU (kU t)
def _root_.List.pU(t:Y):Y:=mS (kU t)
def _root_.List.aX(t:Y):Y:=kd (kU t)
def _root_.List.bH(t:Y):Y:=jM (kU t)
def _root_.List.CR(t:Y):Y:=pZ (kU t)
def _root_.List.cd(t:Y):Y:=ks (kU t)
def _root_.List.aS(t:Y):Y:=nI (kU t)
def _root_.List.b6(t:Y):Y:=kI (kU t)
def _root_.List.bI(t:Y):Y:=mx (lv t)
def _root_.List.Cv(t:Y):Y:=wT (lv t)
def _root_.List.aI(t:Y):Y:=js (lv t)
def _root_.List.iI(t:Y):Y:=kU (lv t)
def _root_.List.wq(t:Y):Y:=lv (lv t)
def _root_.List.F8(t:Y):Y:=mS (lv t)
def _root_.List.bw(t:Y):Y:=kd (lv t)
def _root_.List.dm(t:Y):Y:=jM (lv t)
def _root_.List.EZ(t:Y):Y:=pZ (lv t)
def _root_.List.hL(t:Y):Y:=ks (lv t)
def _root_.List.jr(t:Y):Y:=nI (lv t)
def _root_.List.fy(t:Y):Y:=kI (lv t)
def _root_.List.FH(t:Y):Y:=x1 (x1 t)
def _root_.List.Gy(t:Y):Y:=mS (x1 t)
def _root_.List.xK(t:Y):Y:=kd (x1 t)
def _root_.List.CQ(t:Y):Y:=jM (x1 t)
def _root_.List.FT(t:Y):Y:=ks (x1 t)
def _root_.List.gP(t:Y):Y:=wp (mS t)
def _root_.List.AW(t:Y):Y:=mx (mS t)
def _root_.List.Ev(t:Y):Y:=po (mS t)
def _root_.List.sl(t:Y):Y:=js (mS t)
def _root_.List.n2(t:Y):Y:=kU (mS t)
def _root_.List.eC(t:Y):Y:=lv (mS t)
def _root_.List.vG(t:Y):Y:=kd (mS t)
def _root_.List.ym(t:Y):Y:=po (kd t)
def _root_.List.ib(t:Y):Y:=js (kd t)
def _root_.List.Ej(t:Y):Y:=kU (kd t)
def _root_.List.ae(t:Y):Y:=kd (kd t)
def _root_.List.aF(t:Y):Y:=jM (kd t)
def _root_.List.kB(t:Y):Y:=pZ (kd t)
def _root_.List.e0(t:Y):Y:=ks (kd t)
def _root_.List.aC(t:Y):Y:=nI (kd t)
def _root_.List.bP(t:Y):Y:=kI (kd t)
def _root_.List.cH(t:Y):Y:=mx (jM t)
def _root_.List.vC(t:Y):Y:=wT (jM t)
def _root_.List.cx(t:Y):Y:=js (jM t)
def _root_.List.S(t:Y):Y:=kU (jM t)
def _root_.List.cz(t:Y):Y:=lv (jM t)
def _root_.List.iH(t:Y):Y:=mS (jM t)
def _root_.List.bQ(t:Y):Y:=kd (jM t)
def _root_.List.gR(t:Y):Y:=jM (jM t)
def _root_.List.FX(t:Y):Y:=pZ (jM t)
def _root_.List.fj(t:Y):Y:=ks (jM t)
def _root_.List.ia(t:Y):Y:=nI (jM t)
def _root_.List.eK(t:Y):Y:=kI (jM t)
def _root_.List.r5(t:Y):Y:=x1 (pZ t)
def _root_.List.rG(t:Y):Y:=mS (pZ t)
def _root_.List.ni(t:Y):Y:=kd (pZ t)
def _root_.List.gY(t:Y):Y:=jM (pZ t)
def _root_.List.xY(t:Y):Y:=ks (pZ t)
def _root_.List.Gp(t:Y):Y:=mx (ks t)
def _root_.List.GF(t:Y):Y:=wT (ks t)
def _root_.List.cR(t:Y):Y:=js (ks t)
def _root_.List.bV(t:Y):Y:=kU (ks t)
def _root_.List.aO(t:Y):Y:=lv (ks t)
def _root_.List.mv(t:Y):Y:=mS (ks t)
def _root_.List.aj(t:Y):Y:=kd (ks t)
def _root_.List.ag(t:Y):Y:=jM (ks t)
def _root_.List.GE(t:Y):Y:=pZ (ks t)
def _root_.List.eP(t:Y):Y:=ks (ks t)
def _root_.List.b2(t:Y):Y:=nI (ks t)
def _root_.List.nS(t:Y):Y:=kI (ks t)
def _root_.List.kv(t:Y):Y:=po (nI t)
def _root_.List.pG(t:Y):Y:=js (nI t)
def _root_.List.nT(t:Y):Y:=kU (nI t)
def _root_.List.cQ(t:Y):Y:=kd (nI t)
def _root_.List.bl(t:Y):Y:=jM (nI t)
def _root_.List.eb(t:Y):Y:=ks (nI t)
def _root_.List.iF(t:Y):Y:=nI (nI t)
def _root_.List.q6(t:Y):Y:=kI (nI t)
def _root_.List.fF(t:Y):Y:=mx (kI t)
def _root_.List.pm(t:Y):Y:=wT (kI t)
def _root_.List.eV(t:Y):Y:=js (kI t)
def _root_.List.a0(t:Y):Y:=kU (kI t)
def _root_.List.pl(t:Y):Y:=lv (kI t)
def _root_.List.Ga(t:Y):Y:=mS (kI t)
def _root_.List.eN(t:Y):Y:=kd (kI t)
def _root_.List.dJ(t:Y):Y:=jM (kI t)
def _root_.List.HV(t:Y):Y:=pZ (kI t)
def _root_.List.dK(t:Y):Y:=ks (kI t)
def _root_.List.jq(t:Y):Y:=nI (kI t)
def _root_.List.ec(t:Y):Y:=kI (kI t)
def _root_.List.bo(t:Y):Y:=t.eV.aO
def _root_.List.av(t:Y):Y:=t.aC.bi
def _root_.List.b0(t:Y):Y:=t.aC.aS
def _root_.List.eh(t:Y):Y:=t.kv.hK
def _root_.List.cw(t:Y):Y:=t.bu.aO
def _root_.List.cY(t:Y):Y:=t.pE.aF
def _root_.List.bz(t:Y):Y:=t.bm.aI
def _root_.List.qW(t:Y):Y:=t.bi.aI
def _root_.List.cK(t:Y):Y:=t.bV.ae
def _root_.List.cs(t:Y):Y:=t.S.aj
def _root_.List.eD(t:Y):Y:=t.AY.bi
def _root_.List.gD(t:Y):Y:=t.hU.fr
def _root_.List.cf(t:Y):Y:=t.cd.S
def _root_.List.k7(t:Y):Y:=t.gY.bm
def _root_.List.dv(t:Y):Y:=t.ag.aX
def _root_.List.fQ(t:Y):Y:=t.aO.iG
def _root_.List.bp(t:Y):Y:=t.ae.S
def _root_.List.ET(t:Y):Y:=t.gY.bu
def _root_.List.dB(t:Y):Y:=t.e0.S
def _root_.List.cv(t:Y):Y:=t.bQ.bl
def _root_.List.gC(t:Y):Y:=t.ag.S
def _root_.List.d6(t:Y):Y:=t.bm.bI
def _root_.List.g8(t:Y):Y:=t.e0.bI
def _root_.List.Ft(t:Y):Y:=t.bi.cR
def _root_.List.it(t:Y):Y:=t.eb.S
def _root_.List.EX(t:Y):Y:=t.b8.AY
def _root_.List.dh(t:Y):Y:=t.bm.fy
def _root_.List.EW(t:Y):Y:=t.ni.bi
def _root_.List.fg(t:Y):Y:=t.b8.aX
def _root_.List.gZ(t:Y):Y:=t.cx.S
def _root_.List.fH(t:Y):Y:=t.bV.ag
def _root_.List.iV(t:Y):Y:=t.cx.aC
def _root_.List.Aw(t:Y):Y:=t.bQ.eV
def _root_.List.ik(t:Y):Y:=t.bH.dm
def _root_.List.gE(t:Y):Y:=t.eV.gY
def _root_.List.i9(t:Y):Y:=t.bI.aC
def _root_.List.kk(t:Y):Y:=t.cR.aI
def _root_.List.i0(t:Y):Y:=t.cQ.pG
def _root_.List.ce(t:Y):Y:=t.bl.aC
def _root_.List.i2(t:Y):Y:=t.aI.gP
def _root_.List.g6(t:Y):Y:=t.S.ag
def _root_.List.h8(t:Y):Y:=t.bH.aC
def _root_.List.ho(t:Y):Y:=t.ag.aD
def _root_.List.iv(t:Y):Y:=t.n2.hK
def _root_.List.jQ(t:Y):Y:=t.aI.aO
def _root_.List.g0(t:Y):Y:=t.bH.bw
def _root_.List.kl(t:Y):Y:=t.a0.a0
def _root_.List.db(t:Y):Y:=t.ET.aO
def _root_.List.dx(t:Y):Y:=t.hL.fy
def _root_.List.io(t:Y):Y:=t.eh.gD
def _root_.List.dt(t:Y):Y:=t.EX.qW
def _root_.List.fd(t:Y):Y:=t.EW.aO
def _root_.List.gT(t:Y):Y:=t.Ft.aI
def _root_.List.eF(t:Y):Y:=t.Aw.aO
def _root_.List.hV(t:Y):Y:=t.k7.aI
def _root_.List.gB(t:Y):Y:=t.jd.aC
def DI : List W:=[.UA,.UA]
def kD : List W:=[.UA,.UA,.UA]
def F5 : List W:=[.UA,.UA,.UA,.UA]
def f7 : List W:=[.UA,.UA,.UT]
def FK : List W:=[.UA,.UA,.UT,.UA]
def Bf : List W:=[.UA,.UT]
def nQ : List W:=[.UA,.UT,.UA]
def FZ : List W:=[.UA,.UT,.UA,.UA]
def EE : List W:=[.UA,.UT,.UA,.UA,.UA]
def Bc : List W:=[.UA,.UT,.UA,.UA,.UA,.UA]
def vY : List W:=[.UA,.UT,.UT]
def Gj : List W:=[.UT,.UA]
def dE : List W:=[.UT,.UA,.UA]
def vr : List W:=[.UT,.UA,.UA,.UA]
def FC : List W:=[.UT,.UA,.UA,.UA,.UA]
def hI : List W:=[.UT,.UA,.UT]
def Dy : List W:=[.UT,.UA,.UT,.UA]
def Gf : List W:=[.UT,.UA,.UT,.UT]
def Gk : List W:=[.UT,.UT]
def mD : List W:=[.UT,.UT,.UA]
def FW : List W:=[.UT,.UT,.UA,.UA]
def fB : List W:=[.UT,.UT,.UT]
def Dr : List W:=[.UT,.UT,.UT,.UA]
def wU : List b9:=[]
def iC : List b9:=[.P11]
def sd : List b9:=[.P11,.P11]
def By : List Bool:=[]
def GA : List Bool:=[false,false]
def rU : List Bool:=[false,false,false,false,true,true,true,true]
def BH : List Bool:=[false,false,true,false]
def rh : List Bool:=[false,false,true,false,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false]
def zG : List Bool:=[false,false,true,true,true,true]
def x6 : List Bool:=[true]
def A2 : List Bool:=[true,false,false,false,false,true,true,true,true]
def D1 : List Bool:=[true,false,false,true,false]
def xF : List Bool:=[true,false,false,true,false,false,false,false,true,true,true,true]
def BB : List Bool:=[true,false,false,true,false,false,true,false]
def BI : List Bool:=[true,false,false,true,true,true,true]
def Bs : List Bool:=[true,false,false,true,true,true,true,true]
def yl : List Bool:=[true,false,false,true,true,true,true,true,false,false,false]
def EK : List Bool:=[true,false,true,false]
def yg : List Bool:=[true,false,true,false,false,false,false,true,true,true,true]
def BN : List Bool:=[true,false,true,false,false,true,false]
def r1 : List Bool:=[true,false,true,false,true,true,true,true]
def vw : List Bool:=[true,false,true,false,true,true,true,true,false,false,true,false,false,true,false]
def CV : List Bool:=[true,false,true,true,true,true]
def Cx : List Bool:=[true,false,true,true,true,true,true]
def Ax : List Bool:=[true,false,true,true,true,true,true,false,false,false]
def Dp : List Bool:=[true,true]
def sw : List Bool:=[true,true,false,false,false,false,false,true,true,true,true]
def Bw : List Bool:=[true,true,true]
def tA : List Bool:=[true,true,true,true]
def Cd : List Bool:=[true,true,true,true,false,false,false]
def Bo : List Bool:=[true,true,true,true,true,false,false,false]
def vF : List Bool:=[true,true,true,true,true,true,false,false,false,true,false,false,false,true,false]
def aM (d:cm) (us : List W) (w : List Bool) : fZ:=.Recovered d us w
def t9 (d:cm) (us : List W) (w : List Bool) : fZ:=.NineGain d us w
def t6 (d:cm) (us : List W) (w : List Bool) : fZ:=.SixGain d us w
def tY (w : List Bool) : fZ:=.YaaGain w
def eU (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (aM d us w)
def Du (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (t9 d us w)
def zr (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (t6 d us w)
def kH (w : List Bool) : dp:=.rEnd (tY w)
def DP (w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (xI w) s t p
def In (q w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (jJ q w) s t p
def Gg (q w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (gh q .qB w) s t p
def rP (b : List Bool) (ps : List b9) (st : List Bool) (nd:Nat) (td:fZ) (nf:Nat) (tf:fZ) (w : List Bool) : dp:=.rProt ⟨b,ps,st,nd,td,nf,tf⟩ w
def dH (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) : dp:=.rRet q w .AllCases [⟨.RD,[],s1,t1,p1⟩,⟨.RF,[false,false],s2,t2,p2⟩,⟨.RB,[false,false],s3,t3,p3⟩]
def eX (q : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) (s4:Nat) (t4:Pos) (p4 : List Bool) : dp:=.rRet q [false,false] .Cases00 [⟨.RD,[true,false,true],s1,t1,p1⟩,⟨.RD,[true,true,true,false,true],s2,t2,p2⟩,⟨.RD,[true,false,true,false,false],s3,t3,p3⟩,⟨.RF,[false,false,false],s4,t4,p4⟩]
def jL (q : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) (s4:Nat) (t4:Pos) (p4 : List Bool) : dp:=.rRet q [true] .Cases1 [⟨.RD,[true,true,false,true],s1,t1,p1⟩,⟨.RD,[false,true,false,false],s2,t2,p2⟩,⟨.RF,[false,false],s3,t3,p3⟩,⟨.RB,[false,false],s4,t4,p4⟩]
def FP (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) : dp:=.rRet q w .Coarse00 [⟨.RD,[],s1,t1,p1⟩,⟨.RF,[false,false],s2,t2,p2⟩]
def Br (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) : dp:=.rRet q w .Coarse10 [⟨.RD,[],s1,t1,p1⟩,⟨.RB,[false,false],s2,t2,p2⟩]
noncomputable section
def an:=z6.fu
def ap:=z2.fp
def bv:=dj.f4
def bN:=z3.gm
def b7:=d1.fT
def ca:=z2.ft
def ch:=dj.fE
def c4:=z8.fT
def ey:=c9.fC
def et:=cq.ga
def dX:=z1.p0
def ep:=z1.p1
def fG:=z1.p9
def hB:=cO.p3
def fe:=cM.e1
def hJ:=ct.eS
def hC:=cq.p1
def iq:=z6.fP
def hD:=dy.eZ
def iK:=cq.p0
def kA:=z2.f9
def jK:=dr.hH
def jc:=dM.fU
def iB:=z2.fU
def kw:=z5.p0
def iJ:=d1.fE
def lF:=cM.fD
def lo:=cP.eW
def iz:=dn.e7
def je:=z6.ev
def mF:=z6.f6
def mL:=cP.gm
def mf:=cP.fC
def mG:=ct.fp
def mH:=cO.p1
def l0:=cI.p3
def lJ:=cA.er
def mJ:=dP.gn
def nY:=z5.ez
def mK:=dr.gk
def mc:=z6.ex
def mM:=cy.p5
def lA:=c0.fL
def lm:=cB.fq
def ky:=cP.eY
def pz:=c0.fo
def rQ:=z2.e7
def nX:=z3.fm
def rO:=cy.gO
def nW:=cG.gm
def sf:=z4.fK
def pw:=z7.gv
def sc:=cU.f5
def rV:=dy.eS
def r6:=z7.f5
def nZ:=cy.p2
def pn:=ct.p5
def vn:=ds.fC
def sh:=ct.eY
def pB:=dn.p1
def pq:=cM.p9
def pA:=cM.gL
def rR:=d1.e1
def rZ:=cS.gb
def sa:=d1.eu
def rX:=d1.er
def pu:=c0.fT
def sj:=z2.fP
def vc:=c0.fD
def sb:=cP.gH
def vk:=cU.gj
def sk:=cP.gn
def vq:=cO.p8
def r7:=cP.gg
def pp:=c5.p5
def vu:=cq.eY
def ve:=di.e1
def wA:=z2.eZ
def vm:=dy.gL
def vj:=di.eH
def vi:=ds.gH
def vd:=di.fi
def vl:=dl.eA
def yt:=c9.p6
def rY:=z6.gk
def vt:=cB.gv
def vo:=cI.gH
def xj:=dj.fD
def xr:=cy.gg
def w1:=ds.gv
def yo:=cV.fN
def vh:=da.ez
def vp:=cB.f8
def yu:=cI.p5
def wh:=cG.f8
def xw:=cG.fT
def xn:=cM.gl
def yv:=cP.eS
def yw:=z5.fo
def w2:=cB.gm
def v6:=cI.p4
def u2:=cB.fC
def uG:=cM.gg
def w6:=dL.gv
def Aq:=cM.hH
def xa:=dn.gb
def wu:=c5.eu
def w9:=dr.gd
def xi:=cL.fx
def ts:=cI.gO
def w3:=cI.fi
def wn:=c9.gl
def wK:=cG.gb
def xC:=cG.fM
def w7:=cG.fA
def wz:=dy.fz
def xl:=dy.gl
def xz:=cS.fA
def wF:=cN.fP
def wc:=c8.p1
def wV:=dj.f9
def wC:=dj.f5
def un:=ct.p4
def sM:=cM.ft
def rc:=cG.fC
def wm:=dP.fz
def wB:=cM.gk
def zu:=di.p1
def Cc:=cM.eS
def AI:=z4.fA
def zz:=dy.f6
def wS:=c0.fu
def wl:=c8.eY
def wO:=dj.ft
def zZ:=z8.f4
def zE:=cO.p9
def tO:=cU.eZ
def wg:=cP.p2
def yS:=c6.fP
def Ai:=cS.gj
def yH:=cA.fA
def xD:=cG.gk
def yQ:=c7.p6
def v9:=cI.eA
def uC:=cM.fu
def u7:=z7.fm
def y3:=cB.fA
def CA:=di.fz
def Ah:=cB.eH
def xd:=c6.p5
def wy:=cG.gj
def wN:=z7.gj
def yy:=cU.p6
def zU:=cT.p6
def Am:=cP.eZ
def xA:=cM.fp
def zM:=cV.fC
def zx:=dM.fp
def yW:=c7.eY
def zF:=dr.gb
def AP:=dI.eS
def AA:=c5.fi
def zP:=dY.er
def yB:=dY.gk
def xc:=cP.e7
def y6:=dP.p4
def y0:=dl.gl
def zf:=c6.fm
def yU:=dj.p6
def y8:=c8.ez
def AF:=dL.fU
def Ay:=c5.p4
def w4:=c5.p7
def Az:=da.gm
def As:=cV.eu
def AK:=dn.ex
def wJ:=c9.f9
def zp:=dq.eZ
def xo:=cB.ex
def zX:=dj.fu
def zm:=da.fo
def nD:=bd.ag
def sS:=e_.cd
def lO:=oG.ag
def kV:=vV.a0
def AD:=e_.jr
def yJ:=bd.dK
def i4:=xq.ag
def ql:=fY.dJ
def kt:=yr.eb
def cZ:=vP.ag
def fk:=rx.S
def il:=pK.cd
def lD:=vV.cd
def xv:=fY.S
def o1:=yx.cd
def qt:=xS.S
def B1:=vV.b6
def yD:=rx.eK
def rF:=vP.dK
def aQ:=bd.hM
def aY:=b1.xM
def cj:=e_.bQ
def BR:=xq.nS
def Al:=fY.cz
def tc:=pK.jr
def bF:=aE.ni
def bE:=aP.xK
def rq:=yx.b6
def cl:=e_.iG
def cX:=e_.cH
def ed:=b1.aI
def fI:=b1.bI
def dS:=e_.wk
def dk:=aE.bl
def dz:=e_.hU
def An:=xS.cz
def d8:=bd.hK
def d0:=bd.bi
def d4:=aP.FT
def eQ:=e_.cx
def Cr:=b1.eb
def e6:=aP.aF
def fX:=b1.bH
def gx:=e_.yk
def ox:=aE.eN
def gq:=aE.pG
def g5:=e_.ib
def gX:=aP.eC
def g7:=b3.bl
def g2:=K.aC
def hW:=e_.ia
def hQ:=cg.bl
def h5:=aE.xY
def iD:=bd.jd
def i6:=fY.bI
def iX:=af.bQ
def iY:=e_.iH
def iQ:=ie.aI
def iS:=aV.aI
def iN:=e_.aC
def l6:=e_.bm
def jk:=L.bP
def jv:=e_.aF
def jt:=aE.aO
def jD:=j.Do
def jw:=H.eC
def jl:=H.sl
def ju:=j.Hc
def jy:=ah.bm
def jn:=b1.nj
def jT:=bq.bl
def kn:=b1.bP
def jX:=e4.bl
def kr:=bd.bQ
def kc:=fY.bH
def ke:=ak.bQ
def ki:=e_.pE
def j5:=H.aO
def kg:=L.aC
def jZ:=bd.zh
def jU:=H.Ev
def ka:=j.If
def k6:=aP.ib
def kO:=b1.bw
def ld:=e_.vS
def kJ:=bd.kY
def kS:=L.wk
def rD:=L.bm
def kP:=e_.H4
def k0:=b1.fr
def lk:=K.wk
def lR:=fY.aI
def mq:=bd.iH
def mh:=j.vS
def lT:=bd.aX
def lS:=e_.aD
def lV:=e_.A7
def lM:=aE.cQ
def lG:=j.cJ
def lP:=bd.cx
def nL:=j.GO
def mW:=e_.AY
def nK:=b1.hL
def m3:=aP.bQ
def nl:=H.eV
def nH:=ao.aI
def mY:=dN.aI
def mT:=ah.kY
def m4:=K.bm
def nk:=aE.aC
def nr:=H.aC
def nC:=ar.aI
def nE:=K.bl
def np:=aP.cR
def oS:=aE.gY
def oz:=aP.CQ
def oc:=iZ.aI
def o4:=X.bQ
def oB:=aE.Ev
def oH:=br.aF
def ob:=ak.jd
def oX:=j.bH
def oo:=af.jd
def oD:=aE.sl
def o5:=j.aF
def o7:=H.ni
def oZ:=aP.Gp
def pd:=aw.bl
def oJ:=j.bQ
def oN:=bt.eV
def pY:=L.vS
def pR:=e_.S
def rb:=H.fF
def q9:=ci.aI
def qM:=br.ib
def FG:=ok.ag
def qJ:=bd.bm
def rB:=K.AY
def qI:=bj.aF
def rC:=aU.kY
def rK:=e_.bu
def qR:=aE.eV
def qz:=aP.eP
def rH:=K.vS
def rJ:=br.bQ
def q4:=b1.hK
def qq:=bq.aC
def rE:=ak.bm
def rN:=af.bm
def qc:=aw.kv
def pT:=bj.bQ
def q5:=b1.bm
def ru:=aU.bm
def q7:=H.vG
def rs:=X.bi
def qn:=L.AY
def tg:=j.bI
def u1:=ah.bu
def uP:=aE.bQ
def ul:=K.Ev
def sP:=K.bP
def uj:=j.mu
def uN:=hj.bl
def uO:=H.bl
def tF:=K.sl
def tW:=L.bl
def tk:=ak.bi
def ug:=aE.bV
def vb:=e_.cJ
def ub:=e_.fj
def t5:=cC.aI
def uK:=bd.aC
def ur:=H.gY
def ty:=H.AY
def uS:=aP.Gy
def ut:=br.xK
def Et:=fY.eb
def tP:=h9.aI
def ui:=aP.ae
def t0:=au.bi
def tS:=H.aI
def uB:=bd.ya
def tN:=aP.cx
def tq:=b1.cJ
def ue:=au.jd
def uq:=af.bi
def tE:=bd.aD
def Ez:=bd.nS
def jm:=AD.ag
def iP:=kV.ag
def fc:=ql.cd
def kb:=yJ.S
def fa:=sS.cz
def iA:=nD.a0
def dF:=B1.ag
def ny:=sS.dJ
def hR:=kt.cz
def j0:=nD.b6
def eT:=lO.b6
def iy:=Al.eb
def j7:=xv.nS
def eI:=BR.cz
def h7:=lD.eK
def n3:=kV.dK
def gs:=o1.eK
def kQ:=lO.a0
def rl:=yJ.eK
def gr:=rq.ag
def sV:=il.dK
def zt:=fk.jq
def gF:=qt.nS
def gG:=yD.b6
def BF:=lD.gR
def eE:=nD.jr
def B5:=i4.iI
def B2:=nD.aS
def rv:=i4.fy
def pV:=AD.nS
def mU:=kt.dJ
def uk:=sS.S
def gu:=cj.bl
def BQ:=xv.eP
def zc:=il.bQ
def gU:=yD.cd
def k8:=rF.eK
def ol:=qt.eP
def tr:=fk.eb
def t7:=rF.bQ
def h3:=tc.ag
def t8:=i4.aS
def zC:=fk.eP
def ua:=ql.jr
def Cb:=o1.bQ
def nB:=xv.ag
def pc:=nD.cd
def oe:=tc.eP
def sR:=lO.aS
def BP:=il.ag
def AN:=lD.cz
def AQ:=yD.aS
def BC:=cZ.eN
def m8:=BR.S
def jA:=An.eb
def sX:=cZ.aI
def jV:=ox.bl
def rg:=tc.nS
def kp:=fI.bl
def ko:=i4.jr
def j2:=Cr.S
def kj:=rF.cz
def Er:=cZ.cz
def tH:=cZ.pl
def s5:=qt.b2
def zJ:=kt.S
def wG:=o1.fj
def yO:=o1.S
def Fx:=xv.b2
def FI:=Cr.dJ
def yF:=rq.cd
def Ew:=cZ.eb
def mP:=fk.dK
def BM:=qt.ag
def v7:=il.dJ
def yV:=i4.dm
def y1:=fk.a0
def BX:=il.eb
def BE:=lD.ia
def BG:=lO.cd
def ra:=lO.ec
def Ch:=lO.ag
def qu:=FG.jr
def pS:=An.jq
def E1:=yJ.fj
def Fi:=cZ.S
def E0:=i4.hL
def FD:=AD.b2
def E2:=An.S
def uf:=dS.bl
def sW:=rD.bI
def u8:=lD.fj
def s6:=cX.bl
def tU:=cl.bl
def uU:=ed.aI
def tT:=l6.aI
def Fe:=Et.eb
def s9:=ql.fy
def va:=ed.aO
def ES:=il.a0
def sI:=Ez.S
def uu:=rF.fj
def ou:=jm.aI
def pf:=fc.bV
def d5:=n3.eK
def nh:=iP.e0
def Cl:=fa.eV
def k4:=sV.cd
def uI:=kb.bl
def iT:=jm.jr
def i1:=rl.b6
def jx:=iA.bl
def AC:=j0.bl
def g3:=kb.dK
def jp:=ny.aI
def hY:=kQ.ec
def j8:=h7.e0
def qN:=jm.dm
def oQ:=j7.bV
def ii:=zc.ag
def o9:=zt.S
def iu:=rv.b8
def v8:=uk.bl
def i3:=fc.dJ
def BU:=BF.bw
def lH:=pV.cz
def nn:=zC.cd
def jg:=hR.b8
def BD:=eT.aX
def o3:=BC.ag
def E8:=B2.ag
def BZ:=tr.cQ
def jS:=mU.fy
def EO:=B5.eV
def rI:=kb.a0
def yZ:=AN.b8
def uW:=t8.S
def w0:=Er.ae
def li:=ua.nS
def kZ:=iA.ec
def kK:=ol.cd
def Fh:=fa.cd
def Ag:=fc.eb
def uy:=ny.jr
def mj:=iP.a0
def EN:=BQ.fj
def uX:=Fx.cR
def l8:=Cb.ag
def tM:=dF.a0
def Fy:=B5.aj
def l4:=FI.jr
def AE:=kb.ag
def wZ:=sR.S
def ns:=Ew.bi
def nu:=iy.eK
def nb:=sX.cz
def Fv:=fa.b6
def nx:=ny.b6
def Fp:=BQ.S
def wM:=iy.dJ
def m2:=dF.jr
def Ey:=B2.b2
def wf:=j0.aX
def nM:=iA.nS
def EM:=hR.cx
def zB:=eI.eb
def oj:=pc.bV
def B4:=zJ.nS
def y9:=k8.bH
def n6:=iA.dK
def oO:=oe.cd
def n5:=t7.ag
def pg:=iP.pl
def oy:=j0.eP
def oW:=ny.fy
def E9:=BM.fy
def y2:=jm.cd
def E7:=nB.e0
def ph:=AQ.S
def o0:=dF.e0
def Fu:=BF.cd
def BY:=yO.ec
def oM:=iy.aO
def os:=yF.e0
def Fj:=BP.cR
def EF:=iP.aj
def Cp:=rg.cx
def qX:=hR.iF
def rm:=eI.ec
def Fn:=wG.aF
def Fq:=eT.bV
def rd:=BX.b8
def Cz:=zt.cz
def BT:=BE.cR
def pX:=dF.bP
def qi:=tH.cd
def BV:=BP.aX
def BW:=BG.eK
def B9:=s5.cR
def ri:=fa.iF
def Cq:=E1.S
def ro:=yV.bg
def Cm:=Fi.cR
def rk:=iy.eb
def Fr:=E0.ae
def qg:=hR.eb
def rn:=gr.dJ
def tC:=m8.dK
def uE:=gs.bH
def EA:=FD.ag
def uv:=y1.e0
def uY:=E2.bV
def tv:=ny.dm
def tt:=j7.gR
def uQ:=gG.ec
def Eq:=hR.cd
def tL:=t7.dK
def te:=j0.cx
def Fd:=gs.aD
def Fm:=gF.e0
def sK:=j7.aX
def EH:=iP.eV
def s7:=eT.eP
def uw:=AQ.fj
def uF:=Fe.ae
def tx:=iP.ag
def ta:=Cb.eP
def uV:=v7.S
def uA:=iP.b6
def tz:=Ch.bH
def uh:=ES.ae
def m9:=ou.S
def g9:=pf.ag
def lK:=Cl.S
def i5:=uI.cd
def wr:=BU.e0
def xu:=E8.bi
def uL:=EO.b8
def j3:=BD.ag
def kL:=AC.cd
def yA:=BZ.S
def tw:=Fh.ae
def CG:=qN.bg
def wQ:=EN.bg
def l3:=Fy.ae
def ma:=yZ.dm
def lU:=nh.cz
def u5:=oQ.ag
def B6:=k4.S
def Co:=Fv.bi
def mZ:=o9.ag
def mQ:=Fp.ae
def zR:=Ey.aF
def nF:=Ag.b8
def nG:=EM.cd
def ov:=w0.ag
def n1:=E9.ag
def n8:=v8.b6
def Cj:=AE.jq
def oL:=E7.fj
def oK:=Fu.bi
def Cw:=Fj.cd
def qd:=uW.pl
def re:=B4.a0
def qx:=EF.S
def qV:=Fn.cd
def rA:=Fq.ae
def qK:=rI.e0
def qQ:=BY.S
def rf:=Fr.S
def qy:=wZ.eP
def rt:=uy.bV
def qh:=jx.b6
def FB:=o3.cd
def tb:=zB.aX
def tB:=nh.S
def tl:=nn.cx
def tV:=EA.aD
def tR:=Cz.b8
def sU:=BT.b8
def tp:=Eq.ae
def uD:=Cl.bQ
def sJ:=iT.bV
def s0:=i1.eb
def uH:=Fd.aF
def uo:=Fm.bi
def tu:=tM.cx
def th:=j8.S
def s8:=uX.S
def tD:=BV.aF
def tn:=Cp.ae
def sO:=BW.eb
def u0:=y2.ec
def u3:=lH.a0
def ED:=EH.ae
def tK:=y9.bi
def uc:=Cq.cx
def tG:=v8.cd
def sQ:=wf.ag
def um:=B9.S
def sY:=AC.aI
def ud:=Cm.bg
def u6:=wM.aD
def uJ:=jp.cz
def lW:=wr.S
def l9:=CG.ag
def m1:=xu.b8
def na:=yA.ag
def ot:=B6.bV
def oY:=Co.S
def oV:=uL.cd
def B0:=lK.ag
def qf:=m9.eb
def q8:=Cj.ag
def qa:=wQ.ag
def qY:=Cw.S
def rr:=zR.cd
def qo:=tw.e0
def rL:=FB.e0
def ti:=m9.ag
def sL:=ED.S
def Eu:=u5.cd
def pI:=B0.b8
def tJ:=Eu.cd
def zL a1 a2 a3:=DP a1 a2 a3 e_
def zj a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 e_
def km a1:=Du cD Gk a1
def yK a1:=eU cD kD a1
def zn a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 a8 a9 a7 a10
def og a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 e_
def zd a1:=zr cD DI a1
def At a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 e_
def Ad a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 a9
def zQ a1:=Du cD Bf a1
def Cy a1:=eU cD vY a1
def zH a1 a2 a3 a4 a5 a6 a7 a8:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 e_ a7 a8 e_
def AO a1:=eU cD FZ a1
def yG a1 a2 a3 a4 a5 a6:=eX a1 a2 a3 e_ a2 a4 e_ a2 a3 aP a5 a6 e_
def Ab a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 a4 a5 a6 e_ a7 a8 e_
def Af a1:=eU cF f7 a1
def zl a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a4 a5 e_ a2 a3 aP a6 a7 e_
def zA a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 e_
def wW a1:=eU cD hI a1
def yI a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a8 e_
def zN a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 e_
def zv a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a5 a8
def BO a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a5 e_ a6 a7 e_
def ws a1:=eU cF fB a1
def AH a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a6 a9
def AJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 a10
def zy a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 b1 a2 a3 aP a6 a7 a8
def AG a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 e_ a2 a3 a4 a5 a6 a7 a8 a6 a9
def Cn a1:=eU cF nQ a1
def zD a1:=eU cF dE a1
def pJ a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 bd
def ww a1:=eU cD dE a1
def q1 a1:=Du cD DI a1
def Ci a1:=eU cD F5 a1
def qk a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 e_ a4 a5 a6 a7 a5 a8
def zW a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 a9
def Fa a1 a2 a3 a4:=Gg a1 a2 a3 a4 e_
def zw a1:=zr cD Gj a1
def xb a1:=eU cD fB a1
def m0 a1 a2 a3 a4 a5 a6 a7:=dH a1 b1 a2 a3 e_ a4 a5 e_ a6 a7 e_
def oi a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a9 e_
def xe a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 e_
def uT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 a9 a10 a8 a11
def oP a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 bd
def pP a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a8 bd
def Fo a1:=eU cD mD a1
def lB a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 e_ a7 a8 e_
def BK a1:=eU cD f7 a1
def rp a1:=zr cD Gk a1
def oC a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 a7 a8 a6 a9
def oT a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 e_ a7 a8 a9
def oE a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a5 a8
def nJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 a8 a9 a7 a10
def oI a1 a2 a3 a4 a5:=FP a1 aP a2 a3 e_ a4 a5 e_
def Fk a1:=Du cD Gj a1
def jo a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 a10
def wI a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 e_ a2 a3 aP a6 a7 a8
def jB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 a9 a10 a11 e_
def Cs a1:=eU cF vY a1
def Ar a1:=eU cD nQ a1
def zT a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a4 a5 b1 a2 a3 aP a6 a7 e_
def lz a1:=eU cF kD a1
def lL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 a11
def wP a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 e_
def lZ a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a3 aP a5 a6 a7
def l5 a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 a8
def E3 a1:=eU cD vr a1
def FF a1:=eU cD Dy a1
def EC a1:=zr cD Bf a1
def pe a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 bd
def ow a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a5 a8
def pk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 a11
def ry a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 bd a6 a7 e_
def ER a1:=eU cD EE a1
def qL a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 aP
def rM a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 a4 a5 a6 e_ a7 a3 a8
def qb a1 a2 a3 a4:=rP a1 iC a2 a3 (aM cD dE e_) a4 (aM cF dE e_) b1
def Ex a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 e_ a2 a6 e_ a7 a8 e_
def q2 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a5 a8 a9 a5 a10
def qP a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 aP a4 a5 a6 a7 a5 a8
def qU a1 a2 a3 a4 a5 a6 a7 a8:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 a4 a8 a7 a5
def qG a1:=eU cF hI a1
def pW a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 e_
def qp a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a6 a4
def EB a1:=eU cF FC a1
def pO a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a3 a8
def tQ a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 aP
def tZ a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 e_ a7 a3 a8
def uZ a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a8 aP
def tI a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a3 a6 a7 a3 a8
def sN a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a5 a10
def xB a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a3 a7 a8 a3 a9
def xh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 a8 a9 a10 e_
def wR a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 aP
def wE a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a8 e_
def wH a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 bd
def yL a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 aP
def zo a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a4 a5 bd a6 a7 e_ a8 a9 e_
def yN a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 a6 a2 a7 e_ a8 a9 e_
def yC a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a5 e_ a6 a7 bd
def yz a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 bd a4 a5 e_ a6 a7 e_
def Aa a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a3 a9
def AB a1 a2 a3 a4:=rP a1 iC a2 a3 (aM cD nQ e_) a4 (aM cF nQ e_) e_
def yE a1 a2 a3:=rP a1 iC x6 a2 (aM cD f7 e_) a3 (aM cF f7 e_) b1
def ac a1 a2 a3:=lf (zL a1 a2 a3)
def al a1:=lf (km a1)
def aG a1:=lf (zd a1)
def aK a1:=lf (yK a1)
def aT a1 a2 a3 a4 a5 a6 a7:=lf (zj a1 a2 a3 a4 a5 a6 a7)
def bk a1:=lf (Cy a1)
def bC a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (zn a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def bM a1 a2 a3 a4 a5 a6 a7 a8:=lf (At a1 a2 a3 a4 a5 a6 a7 a8)
def bZ a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (Ad a1 a2 a3 a4 a5 a6 a7 a8 a9)
def co a1:=lf (ww a1)
def cp a1 a2 a3 a4 a5 a6:=lf (yG a1 a2 a3 a4 a5 a6)
def dc a1:=lf (ws a1)
def dd a1 a2 a3 a4:=lf (Fa a1 a2 a3 a4)
def d2 a1:=lf (Cn a1)
def em a1 a2 a3 a4 a5 a6 a7 a8:=lf (zH a1 a2 a3 a4 a5 a6 a7 a8)
def eo a1 a2 a3 a4 a5 a6 a7 a8:=lf (yI a1 a2 a3 a4 a5 a6 a7 a8)
def e8 a1 a2 a3 a4 a5 a6 a7 a8:=lf (pJ a1 a2 a3 a4 a5 a6 a7 a8)
def ff a1 a2 a3 a4 a5 a6 a7:=lf (zl a1 a2 a3 a4 a5 a6 a7)
def fb a1 a2 a3:=lf (eU a1 a2 a3)
def e5 a1 a2 a3 a4 a5 a6 a7 a8:=lf (qk a1 a2 a3 a4 a5 a6 a7 a8)
def fW a1:=lf (Fo a1)
def fJ a1:=lf (zQ a1)
def g4 a1 a2 a3 a4 a5 a6 a7:=lf (og a1 a2 a3 a4 a5 a6 a7)
def g1 a1 a2 a3 a4 a5 a6 a7 a8:=lf (zy a1 a2 a3 a4 a5 a6 a7 a8)
def hZ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13:=lf (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
def hT a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (AH a1 a2 a3 a4 a5 a6 a7 a8 a9)
def h6 a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (oi a1 a2 a3 a4 a5 a6 a7 a8 a9)
def ij a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (AG a1 a2 a3 a4 a5 a6 a7 a8 a9)
def iR a1 a2 a3 a4 a5 a6 a7 a8:=lf (Ab a1 a2 a3 a4 a5 a6 a7 a8)
def i7 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (AJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def iO a1 a2 a3 a4:=lf (DP a1 a2 a3 a4)
def iM a1:=lf (xb a1)
def iL a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zA a1 a2 a3 a4 a5 a6 a7 a8 a9)
def ji a1:=lf (Fk a1)
def kf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=lf (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
def lb a1:=lf (AO a1)
def lc a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zN a1 a2 a3 a4 a5 a6 a7 a8 a9)
def lg a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zW a1 a2 a3 a4 a5 a6 a7 a8 a9)
def la a1 a2 a3 a4 a5 a6 a7:=lf (BO a1 a2 a3 a4 a5 a6 a7)
def ms a1:=lf (BK a1)
def ml a1:=lf (Af a1)
def ly a1:=lf (Ar a1)
def mg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=lf (uT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
def mb a1 a2 a3 a4 a5 a6 a7 a8:=lf (zv a1 a2 a3 a4 a5 a6 a7 a8)
def nA a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (oC a1 a2 a3 a4 a5 a6 a7 a8 a9)
def n4 a1:=lf (EC a1)
def pa a1:=lf (Ci a1)
def q0 a1 a2 a3 a4 a5:=lf (Gg a1 a2 a3 a4 a5)
def pM a1 a2 a3 a4 a5 a6 a7 a8:=lf (pP a1 a2 a3 a4 a5 a6 a7 a8)
def qm a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (nJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def J a1 a2 a3 l:=aZ (zL a1 a2 a3) l
def aW a1 l:=aZ (km a1) l
def bA a1 a2 a3 a4 a5 a6 a7 l:=aZ (zj a1 a2 a3 a4 a5 a6 a7) l
def bD a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l:=aZ (zn a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l
def bT a1 a2 a3 a4 l:=aZ (DP a1 a2 a3 a4) l
def ck a1 l:=aZ (zd a1) l
def de a1 l:=aZ (yK a1) l
def du a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (Ad a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def dG a1 l:=aZ (Af a1) l
def ek a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (Ab a1 a2 a3 a4 a5 a6 a7 a8) l
def en a1 l:=aZ (Cy a1) l
def ej a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zA a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def eG a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (At a1 a2 a3 a4 a5 a6 a7 a8) l
def e9 a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zH a1 a2 a3 a4 a5 a6 a7 a8) l
def fh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l:=aZ (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l
def fS a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zv a1 a2 a3 a4 a5 a6 a7 a8) l
def fO a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (yI a1 a2 a3 a4 a5 a6 a7 a8) l
def fV a1 a2 a3 a4 a5 a6 a7 l:=aZ (og a1 a2 a3 a4 a5 a6 a7) l
def gz a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (AH a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def gy a1 l:=aZ (zQ a1) l
def gV a1 a2 a3 a4 a5 a6 a7 l:=aZ (zl a1 a2 a3 a4 a5 a6 a7) l
def gW a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l:=aZ (AJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l
def hX a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zy a1 a2 a3 a4 a5 a6 a7 a8) l
def iw a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (AG a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def ix a1 l:=aZ (Cn a1) l
def ir a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zN a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def jz a1 l:=aZ (ws a1) l
def jW a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zW a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def j4 a1 l:=aZ (rp a1) l
def kh a1 a2 a3 a4 a5 a6 l:=aZ (yG a1 a2 a3 a4 a5 a6) l
def kN a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (pJ a1 a2 a3 a4 a5 a6 a7 a8) l
def k3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l:=aZ (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l
def md a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (xe a1 a2 a3 a4 a5 a6 a7 a8) l
def mR a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (pP a1 a2 a3 a4 a5 a6 a7 a8) l
def m5 a1 l:=aZ (xb a1) l
def nt a1 a2 a3 a4 a5 a6 a7 l:=aZ (oP a1 a2 a3 a4 a5 a6 a7) l
def ng a1 a2 a3 a4 a5 a6 a7 l:=aZ (zT a1 a2 a3 a4 a5 a6 a7) l
def o8 a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (oT a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def od a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l:=aZ (uT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l
def N a1 a2 a3 l r:=nd (zL a1 a2 a3) l r
def az a1 a2 a3 a4 a5 a6 a7 l r:=nd (og a1 a2 a3 a4 a5 a6 a7) l r
def aJ a1 a2 a3 a4 a5 a6 a7 l r:=nd (zj a1 a2 a3 a4 a5 a6 a7) l r
def aR a1 l r:=nd (wW a1) l r
def bc a1 l r:=nd (AO a1) l r
def bU a1 l r:=nd (zQ a1) l r
def bS a1 l r:=nd (zD a1) l r
def cb a1 a2 a3 a4 a5 a6 a7 l r:=nd (BO a1 a2 a3 a4 a5 a6 a7) l r
def cu a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (At a1 a2 a3 a4 a5 a6 a7 a8) l r
def c3 a1 l r:=nd (q1 a1) l r
def dQ a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zN a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def dR a1 l r:=nd (Ci a1) l r
def d3 a1 l r:=nd (zw a1) l r
def ef a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l r:=nd (zn a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l r
def ei a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zH a1 a2 a3 a4 a5 a6 a7 a8) l r
def eg a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (Ab a1 a2 a3 a4 a5 a6 a7 a8) l r
def eL a1 l r:=nd (Af a1) l r
def eR a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l r:=nd (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l r
def eJ a1 l r:=nd (yK a1) l r
def e2 a1 a2 a3 a4 l r:=nd (DP a1 a2 a3 a4) l r
def fR a1 a2 a3 a4 a5 a6 a7 l r:=nd (zl a1 a2 a3 a4 a5 a6 a7) l r
def gA a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (Ad a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def gp a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zA a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def gI a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zv a1 a2 a3 a4 a5 a6 a7 a8) l r
def hi a1 a2 a3 a4 a5 a6 l r:=nd (yG a1 a2 a3 a4 a5 a6) l r
def hS a1 a2 a3 a4 a5 a6 a7 l r:=nd (m0 a1 a2 a3 a4 a5 a6 a7) l r
def im a1 l r:=nd (km a1) l r
def ku a1 l r:=nd (Cs a1) l r
def lj a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l r:=nd (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l r
def k2 a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (lB a1 a2 a3 a4 a5 a6 a7 a8) l r
def lQ a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (yI a1 a2 a3 a4 a5 a6 a7 a8) l r
def lE a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (wI a1 a2 a3 a4 a5 a6 a7 a8) l r
def mi a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l r:=nd (eX a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l r
def lY a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (xe a1 a2 a3 a4 a5 a6 a7 a8) l r
def lC a1 a2 a3 l r:=nd (eU a1 a2 a3) l r
def m6 a1 l r:=nd (E3 a1) l r
def mV a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l r:=nd (AJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l r
def nm a1 l r:=nd (FF a1) l r
def nw a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (AG a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def oq a1 l r:=nd (BK a1) l r
def o2 a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (AH a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def oU a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (oE a1 a2 a3 a4 a5 a6 a7 a8) l r
def om a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zW a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def pj a1 a2 a3 a4 a5 l r:=nd (oI a1 a2 a3 a4 a5) l r
def qS a1 l r:=nd (ER a1) l r
def pL a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (Ex a1 a2 a3 a4 a5 a6 a7 a8) l r
def qs a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (wP a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def rz a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (qk a1 a2 a3 a4 a5 a6 a7 a8) l r
def qv a1 l r:=nd (EB a1) l r
def qw a1 a2 a3 a4 a5 a6 a7 l r:=nd (oP a1 a2 a3 a4 a5 a6 a7) l r
def qe a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zy a1 a2 a3 a4 a5 a6 a7 a8) l r
def pQ a1 l r:=nd (zd a1) l r
def EI : ab dp:=(oq gx (d3 cl (eL aP.FH.aF (cb i3.b8 49 z3.f4 z3.fE z3.fD 1 z3.fu (az tC.jq 4 z4.eB 87 z6.eA 83 z7.fu (N gS.i0.bo 69 cy.fu (iR m1.b8 87 bN b1.g8 1 dI.fo 2 dI.fU) (ji iD)) (e9 hY.cQ.cQ 60 da.f6 da.fP 49 da.gK 46 da.fp (bM kL.fH.bw 178 ap aE.eC.d6 K.eC.d6 L.eC.d6 19 dL.er))) (bU bO.bu (J aY.iG.hU.gT 83 dy.gd (em nh.cx.fj.cQ 145 ds.fm vi 88 ds.gm 84 vn)) (du rq.dK.cQ.fj.S 171 zu au X ad 92 mG aN (bk jV)))) (bc ed.eV (nd (tQ gs.aI.gZ 156 an cg.iV b3.iV 72 z9.fz 60 z7.p7) (N b1.bg.pU.hK.dh 57 ct.gK (aG jV.fQ) (lb dO.S)) (iw pV.dJ.cR.dm.aX 89 mG L 172 cV.er ar 168 ao (bk jk))) (hi t8.ia.aj 52 Cc cM.fm 95 uG (aW nL.aD (n4 bq.ae.bV.aS)) (J i6.iv.bm.dx 164 c8.eA (lf (pe ns.bV 24 dq.fK 100 cT.p7 H 26 dq.fN 54 dq.f4)))))) (N ed.eV.dK.fy 139 z2.f6 (bU iX (gA tC.it 122 AI jv dk e6 103 sf lR (N iE.yk.hU.bo 189 cV.gk (d2 pY.vC.bm) (dc aV)) (fh na e_ 64 ch jH 1 di.fA e_ 2 cB.gn bd (bC ot.b2.b2.aj 199 ap cX.bP.bP.av cl.bP.bP.av 145 ey cg.bQ.cv 141 b3.bQ.cv))) (bc pR (bD ii.aX.aj 91 fe bF bE 74 zz K 70 L (ij dF.jq.b2.ae.cQ 70 wS aH 176 vc oS 172 oz)) (e9 tb.cs 75 cI.hH cI.gL 184 cI.p9 180 cI.p8 (aT ns.dJ 11 cT.ev 1 cT.eZ 2 cT.fo)))) (az mj 38 mF 115 iq 14 z6.gK (N F1.Hc.iI.cx 282 dn.f6 (mR oj.b2.b2 4 cy.e1 65 ct.p0 H 61 hJ (co j.wi.bl.ec)) (aZ (ry j8.fH.dm 11 c7.p9 1 c7.fE 2 cN.gk) (ms jT))) (ef tB.aj 125 et aY aQ 66 hC ak 62 af (jW tl.aS 11 dP.p6 83 c9.p5 aE 94 fe e_.ja (bM lW.ag.bw 113 bv oc.aO iY.jQ mW.jQ 19 dl.eS)) (de K.cJ.kY.ib.fr (cp jA.eb.ag.iI 113 dY.ev dY.eZ 272 dY.fT)))))) (bc cC (cb uE.bw 54 z1.fq z1.gb z1.gd 19 z1.fM (bS nK.bm (cu nu.dm.bw 93 sf g5 gq k6 19 z7.fx (im e_.e0.mX (aK bt.io) (lf (rP rx.dJ.jr wU By 28 (aM cD mD e_) 105 (aM cF mD e_) aP))) (fS oj.b2.a0.ae 272 c7.f4 136 sh ar 132 ao (bZ o9.eP.cd.ag.bg 186 ap dO.ni.fj.bI cj.ni.fj.bI dS.ni.fj.bI 200 w6 bt))) (ef gs.iI.bV.aj 139 pB cX cl 88 fG jt.aD 84 gX.aD (kN qd.S 86 hJ ci aV cC 111 yo (bM re.eP.aF 180 b7 fI.ja.ae rb.ja.ae tg.ja.ae 1 ds.f5)) (mR tV.bQ.b2 4 cI.fE 148 cS.ex H 144 l0 (ac aN.iG.eD.aI 286 cT.eS)))) (c3 bF.aF (o2 qx.nS.S 110 an vZ.ce 116 c4 u1 112 aU.bu (aZ (yL jg.bp 63 pq 126 pA 122 Aq) (aK kO.io)) (aZ (yL i5.dK.ja 4 da.fN 47 da.fK 44 vh) (nA Cp.S 57 cL.f4 cL.fE 87 mH aV 83 cC))) (aJ uv.bQ 52 cq.fu 17 cq.gO 61 cq.ev (o8 nb.gR.bw 270 dP.fm dP.gH 17 dP.er 218 hC j.ae (aG pY.eK.ce)) (fO ns.cz.S 108 wl 70 c8.ex H 66 cN.f4 (lf (rP eE sd BB 24 (aM cD dE e_) 65 (aM cF dE e_) b1)))))) (c3 m3 (qS ah (eR qX.S.a0 e_ 66 z8.fo e_ 107 an uP.mv 14 z8.eZ aP (fR oj.b2.bl 33 vp 32 cB.fz 1 cB.gl (ac e_.aO.bP.dt 334 dr.fz) (q0 cZ.b6 aB 71 rR au)) (J ci.xM.r5.eF 171 c7.fM (bk kn))) (oU tc.b2.cR.S 95 cG.e7 57 pp X 53 ad (bA k4.cx.dJ 11 dj.fK 1 dj.fN 2 dj.ex (iR oY.ag.ag 110 bv e_.aO.aO 1 dT.p5 2 dT.p4)) (J q9.aO.bP.eV.dK.fy 134 c8.fT (ac e3.eC.bu.bz 223 dq.eY)))) (gp o1.gR.bw 42 kA bj br 17 z6.gm 361 z6.p1 (ei fk.ag.aF.bw 52 dn.fq xa 17 dn.gn 129 dn.p4 (aZ (zo ov 226 dP.p0 54 wO 1 dy.gO 2 dy.ev) (ml nl.aI.cH)) (ek rm.bV.aF.b8 121 lJ kW 1 cN.f9 2 cN.ga (bk jX))) (ef ra.bw.e0.ae 64 sb cX cl 169 cP.p1 K 165 L (aZ (oE m1.jr 4 cA.fq 87 bN H.dK.bI 83 j.hL.bI) (bM lW.fH 117 bv o4.aO hW.bQ.aO ld.bQ.aO 1 dL.fp)) (e9 Ch.aS.cQ.cs 245 dI.eW dI.eH 417 dI.f8 413 dI.fz (lb qM.bg)))))))
def FE : ab dp:=(hS gU.aX 122 d1 89 FO 194 Gs (nd (rP qu sd By 28 (aM cD hI e_) 105 (aM cF hI e_) aP) (cu eT.gC 252 iJ dO cj dS 56 z1.fK (nd (oC hR.cz.S 128 z3.gl z3.e1 55 dX X 51 ad) (aJ nu.dm.dm 11 z7.fN 1 z7.ex 2 z7.fL (nd (lz uP.bl) (bk oz.ae.eh) (ji kr)) (mR jg.aS.aF.aS 4 da.er 501 mJ K.cR 134 c7.fU (ac oc.pE.eP.aI.db 109 dL.gd))) (nd (oT k8.dJ.bw 50 c5.fA wu 17 c5.fK 509 iz kJ.sy) (aW kS.nT (co H.kB.aF.ec)) (ix mE.pm.bm (lc hY.bQ 23 cU.gl 24 cU.e1 17 cU.gk 115 cU.eA)))) (ei rv.iF.aj 124 z5.f8 z5.fz 69 z5.gl 65 z5.e1 (nd (ow qV.aj 23 z9.ex 138 c4 au.eN 112 kc) (J X.cH.hU.gT 172 cV.fo (aK ar.cJ.kY.ib.fr)) (ek ol.aS.ae.ag 65 pq jN 1 cA.p5 2 cA.p4 (aT y9.dm 11 dM.fL 1 dM.gg 2 dM.eY))) (N gN.pU.hK.dh 55 cM.eH (k3 ol.aS.ae.a0 371 ky fX 65 dP.fD e_ 146 pA aE 14 da.eW aP (bZ tV.bQ.ho 75 yu oB ul L.Ev 164 l0 kc)) (en h9.bg.hK (bk nH.gY))))) (eL K (cb rg.it 148 z4.fz z4.gl z4.e1 57 z4.gk (m6 gN.S (N L.bu.dt 334 cV.p7 (pM rg.ec.aI.ja 4 dI.p4 145 c0.fi H 141 c0.er) (lf (q1 eQ.bI))) (k3 Dm.fj.cx.bi.cx.aD 185 cN.ez e_ 587 cN.gg e_ 128 iz dN.fr.iH 62 di.f8 j (aT lH.eb.ag 55 cO.ga 1 cO.gj 2 cO.f5))) (nd (pP mP.aO.b2 4 cG.eS 92 cG.fi H 88 wh) (aZ (qL zt.cx.bp 138 dj.fi 60 dj.eW 56 di.gK) (bM jg.cd.gR.ag 89 iK aV.wq nK.wq qJ.wq 1 dT.fT)) (aZ (lL li.aj.cR.bV 24 c8.fD 207 cI.fU H 26 c8.fu 69 rZ aN) (al ke)))) (d3 lq (eJ sP.gY (J rB.aI.hV 72 cB.fE (eo kZ.dJ.bp 68 dr.f8 286 vc e_.bP 53 ds.p2)) (ck mq.sy.nj (fW g7))) (aJ i5.dJ 11 cP.fp 1 cP.ft 2 cP.f4 (ck ed.gP.nj (al ah.rG.bH.bH)) (bA uY.aF.bi.b8 77 c7.ez 1 c7.fK 2 c7.fN (co aQ.bg.eK)))))) (aR bj.eK (aR gu (bU uj (lQ nu.iI.a0 97 z8.fE 134 zZ aE 14 z8.fD (oq oH.xM (hZ g9.aS.a0 87 iK dN.wq 87 iK ie.wq 158 et dV.bP 14 da.p9 aP) (al e4)) (iw kK.S.cQ 69 iK aH 132 et oS 128 oz (lf (tZ mZ.bH.b6.aX 186 ap uj.av 29 dL.gL 206 uN.av)))) (az tv.bg 34 c5.p6 47 pp 96 cG.fu (bA nb.eK.b8 57 c9.eS 1 c9.fm 2 c9.gH (al kO.kv.aX)) (ir jS.aS.ag.aS 11 cI.fK 214 c8.eB 123 cI.fN 119 cI.ex (aK ci.bp)))) (bS ob.bu (gI rA.ag.aS 4 z9.eS 108 an uO.b0 104 oX.b0 (bA tt.ik 11 ct.f5 1 ct.hH 2 ct.gL (fJ aA.ib.iG.eC)) (J aN.aI.bV.fd 159 c7.gm (e8 BX.S 68 zE au X ad 49 dM.eA))) (nd (jo uI.aI.aD 177 cP.eB 420 cy.fC 143 cP.fT 60 cM.eW j) (J bt.hL.aI.hV 73 dP.f9 (bC oV.cs 87 ch qI.aC oH.aC 122 bv mY.aO 118 iQ.aO)) (e9 n6.e0.cJ.ag.bw 112 c7.fi c7.eW 17 c7.eH 193 c7.f8 (ac iS.bi.hL.dx 156 dY.f6))))) (N sP.dh 53 z2.ga (cb nx.ag.bw 91 z4.p4 z4.p3 z4.p2 19 z4.p1 (ef iy.gR.cd.bi.aD 106 nY ob oo 87 pw fX 83 d8 (dQ Co.bQ 82 cB.eS 220 dj.fz 17 cB.fm 59 cB.gH (hT fc.cz.dK.S.S 178 b7 bt.ni.ae 77 vd X 73 ad) (dd yO aB 71 b7)) (m5 iQ.bu (bM mU.dm.bw 47 rQ aA aB dD 19 dM.e1))) (gI rd.ae 91 cG.er 61 xw K 57 L (bT ki.ym.hM.bu.dK.fy 112 iB ki.Ej.kB (h6 i5.aj.b2.a0 195 jK bq 169 mK gf 14 c6.e1)) (du eT.cd.e0.b8.bg 131 iq H.kY.bg.jd mT.bg.jd rC.bg.jd 80 ep i6.pE.n2 (ff jS.ag.bw 157 dq.fz 314 dq.p9 19 dq.gl)))) (bc H.ec (lE gF.gR.aS 11 dn.p2 144 pB 71 fG fY.bw (gV wQ.bl 84 dy.eB 228 di.eu 1 cy.gL (bM i4.b6.aj.cQ.g6 134 w9 ah bK ea 1 dT.fM)) (gz mQ.cs 73 ca uf 92 bN m4.bI 88 sW (kf kt.cx.bp e_ 51 tO bd 88 xi K 84 xi L))) (az rl.pl.ae.aj 60 sb 165 wg 161 cP.p1 (bT jD.kY.sy.cJ.aO.aO 500 ts cl (bZ kL.bV.b2.aj 178 ap oD.hL.bI tF.hL.bI L.sl.hL.bI 128 vl aw)) (fS uQ.e0.bg.S 64 cN.gj 126 lJ cj 122 dS (lf (rP eE iC x6 24 (aM cD dE e_) 65 (aM cF dE e_) b1))))))))
def Fw : ab dp:=(nd (kH L) (bc d0 (aR j5.bP (aR tW (nd (uT gF.aX.aC 11 z7.gl 77 kA hj.gP 53 mc aE.fF 49 aP.cH) (nd (jB jg.aX.aC 11 cy.eB 383 ap kP.CQ 364 iB lq.bH.kB 122 cy.fT) (hZ tR.cd.iF 11 dI.gn e_ 147 dI.eA e_ 120 hD dN.aO 17 cN.eB bd) (ji m3)) (bT d8.kv.pU.hK.dh 305 ky d8 (lf (xe eI.b8.dm.cJ.ag.bw 135 dL.eW 438 ap iN.eK.av 19 dL.eH)))) (bS gu (bT e_.bi.r5.Gy.bm.bz 146 ep bt.cJ.ja (eo oO.dJ.S.a0 91 ds.gO 282 yS aE 14 c6.gK)) (fO d5.eN.S.a0 74 cS.gO 88 Ai aE 14 cS.f5 (e8 rl.cd.dB 133 sa nk g2 kg 64 cU.f4)))) (nd (kH aQ) (bS h9.EZ.FT (J ok.cH.hU.gT 365 cV.fP (d2 mh.vC.bm)) (ck ed.ec.aC (aT cZ.ik 11 dM.er 1 dM.eB 2 dM.fT))) (N e3.aO.hU.bo 548 c9.fi (aZ (lB sR.cx.aF.ae 123 cq.eA L 535 cS.gn 532 cS.eA) (n4 kx.ae.bV.aS)) (bD jS.bH.bi.ae 179 w3 K L 75 rZ ar 71 ao (i7 sU.bw 58 vk jw jD 17 dq.gb 90 sc bO))))) (dR tk (aJ k8.dv 54 z4.e7 149 z4.eH 145 z4.f8 (hi nu.iI.ag 97 z8.gg z8.eY 1 z8.eS (fR n5.b6 54 ct.p2 133 cV.f5 1 ct.p1 (ac d4.bi.cJ.aO.aO 585 dT.gb) (lf (m0 tp 224 d1.fo 121 d1.fu 200 d1.f8))) (ej k8.dJ.cJ.ae 58 yH K L 226 cA.e1 222 cA.gk (aT ny.cd.ag 47 cO.fA 1 cO.eu 2 cO.ez))) (ei uX.bQ 87 xD cG.er 17 cG.eB 53 xw (bA tL.b6.dm 11 dj.f6 1 dj.fP 2 dj.gK (i7 uD.ag.g0 233 ch bF.bV bE.bV 17 dT.fK 109 hD lT.pG)) (bA ql.dm.cd.aX.bl.b8 150 cI.p2 1 cI.p1 2 cI.p0 (g4 wM.aI.cQ 99 cT.gk 57 cT.er 53 cT.eB)))) (nd (zr cF Bf Da) (N kJ.mu.bo 55 dn.e1 (aW rK.bH (lf (jo kV.a0.aj.cR.cx.aD 199 ds.fM 272 ds.fx 243 ds.gn 74 dr.fu j))) (bA uQ.bQ.bP 140 c0.fi 1 c0.eW 2 c0.eH (bk jT))) (N cj.r5.ib.bo 614 cV.fT (J d0.r5.eF 164 cA.fE (al m4.bH.bH)) (o8 te.bg.eP.S 72 c7.p8 c7.p7 110 yQ 106 v9 j (fW kP.cx.bu)))))) (az j7.dJ.S.ae 71 Go 134 Hl 130 z1.e7 (cb sJ.ag 59 z1.f9 z1.ga z1.gj 1 z1.f5 (bU bd.b6 (N aP.FH.ae.pG.cw 78 z7.p4 (mi oe.dm.bg 36 cy.ga e_ 91 cy.gj e_ 38 cy.f5 e_ 53 mL bd (aG ah.AY.sy.nj) (em i1.a0 44 d1.gK d1.fp 175 d9.gd 14 d9.fM)) (eG nn.bl.bw 116 fe g5 gq k6 19 da.fq (aG aN.bm.fr.gB))) (eJ K.GK.cJ.fr (aZ (lz aU.cY) (ac ah.hU.bP.dt 334 dT.p3)) (aZ (uZ s0.aX.b2 4 cS.ft 202 cS.fC H 198 cS.fz) (al fX)))) (ei pg.eb.aD 131 z5.f9 z5.ga 177 z5.gj 38 z5.f5 (nd (rM g3.aX.bP.aX 96 an af.ia.aS 29 z9.gj 116 op.b0) (fV nn.q6.aj 16 ct.fM 112 ct.fx 268 cV.eY (bC xu.bg.aj 68 ca jl.bI ju.bI 91 bN nr.cH 87 mh.cH)) (eG ii.fH 121 fe ed nl j.aI 1 cN.gd (bM uE.bw 54 mF jX kp iD.bl 19 cL.gm))) (ef oy.fg 124 cq.eH K L 64 wh ak 60 af (aZ (oC mZ.aD 60 dP.gb dP.gd 170 ap ak.cx 166 af.cx) (d2 gq.aI.pm.bm)) (de qR.gY.gD (lg tb.aC 11 dq.p4 182 hB iN.ya 63 dq.gm aw))))) (ei j0.a0 36 z2.fq z2.gl 95 z2.gb 14 z2.gd (cb nx.ag.dm 114 z4.ga z4.gj z4.f5 1 z4.hH (oU j3.jr 4 z8.p9 106 c4 bK 102 ea (mV oe.jr.cx.bw 99 mf cX cl 17 cB.eu 65 vu bO (lf (tZ fc.cz.dK.cz.aX 178 b7 L.ja.ae 29 ds.gg 198 aH.cK)) (q0 dF.b6 aB 111 rX au)) (bA kL.bP.aX 130 di.eY 29 cA.eA 161 cA.f9 (bM qN.bw 43 ep aA aB dD 19 dM.f8))) (aJ rd.b6 95 uC 1 cM.gO 2 cM.ev (fh oe.dm.cJ.aX bd 61 sk L 29 dj.fm e_ 81 mM aH (aT qf.b6.dm 11 dT.eA 1 dT.f9 2 dT.ga)) (j4 bF.bi.bu (aT jS.ag.dm 11 cT.gn 1 cT.eA 2 cT.f9)))) (aJ iP.cz.b8 69 z6.fM 1 z6.fx 2 z6.gn (N nL.iH.ib.bz 64 dn.hH (J aY.gP.cJ.aO.aO 221 dj.e1 (aK ki.eC.gD)) (kN k4.gZ 69 rV au X ad 140 cA.gm (fW kp))) (oq o5.xM (e9 d5.gC.aj 70 di.fx di.gn 122 di.eA 118 di.f9 (dc ju.i2)) (de g5.kY.ib.fr (lf (zD H))))))))
def Fb : ab dp:=(eL aU (aR vU.eK (aJ mj.eb.aX 62 z1.fT 41 z1.fA 138 z1.eu (bS iZ.bm (aJ i3.e0.eK 61 u7 1 z7.gH 2 z7.gm (mV pS.eV.b8.bw 166 y3 ak af 17 cy.gm 77 mG h9 (aK oS.io) (la kQ.ag 40 d9.fK d9.fN d9.ex 1 d9.fL)) (dG op.e0.cH (lf (xB o9.eP.jr.ae.aj 178 ap ar.bg.hM.fF ao.bg.hM.fF 240 ak.aC.fj.bI 236 af.aC.fj.bI)))) (e2 K.A7.bi.cJ.aO.aO 330 iz ak.kY.sy (fV pX.b2.ae 128 dP.f6 165 c9.gO 367 dP.fP (fJ jZ.vz.aI)) (ix qz.Cv.bm (lf (ry iu.b8 51 cU.ez 1 cU.fT 2 cU.fK))))) (nd (zr cF Bf b4) (nd (qb eE xF 24 65) (aW cg.nT (bk fX.ae.eh)) (bT b1.kB.CQ.dt 370 wn ak (eo uk.bV.a0 51 dM.p3 70 rR iN 14 dM.p2))) (dR X.bg (dG jy.cH (i7 lW.ag.bw 113 bv nC.aO nH.aO 17 c6.f9 94 ch o5.aC)) (en aH.wk.bl.bH (e8 te.cJ.S 98 sc dO cj dS 60 dq.gk))))) (eL H (pL nu.jr 11 z4.fT 122 AI z4.eu 85 z4.ez (gA h3.S.cR.bg 106 nY jv dk e6 79 pw aN (lj l8.bi.aD 378 ap jU.CQ 378 ap ka.CQ 371 iB ug.bH.kB 129 cy.fT j (fJ aV.mX.eC) (ji dV)) (fh oW.dK.aX.S e_ 59 cA.eB bd 117 lJ H 53 di.fu e_ (h6 j0.gC 96 vq bt 52 cO.er H 48 cO.p6))) (ei u8.aF.aD 46 cG.fq wK 96 cG.gd 92 xC (J ah.xE.mX.aF.sl.aI 144 di.eB (fb cF vr aE.ia.mv.bm)) (du e_.dm.dm.aX.aF.aX.aj 104 CA aA aB dD 67 ve bq (bk aQ.gY)))) (eg jm.iI.q6 91 nX jH 1 z6.gg 2 z6.eY (N nL.aF.sl.aI 108 dn.gj (fS ii.cK 98 cB.fi 66 Ah K 62 L (aG nK.jQ.iG)) (gy ah.iG.eC (aK kp))) (fR qi.eN 68 cP.f8 145 cy.fm 19 cP.fz (od ov.aS 11 di.fT 101 bv j.ib 70 ch lq 66 gN (iO L.iG.bl.hU.gE.cw 240 ap L.iG.mv.bI)) (fh sV.aS.g6.aX e_ 140 cN.ex aP 103 hD ar.cJ 99 hD ao.cJ (lb ak.pG.bg)))))) (eL iZ.aF (az iA.cK 168 z1.p4 202 z1.p3 198 z1.p2 (ei dF.dK.S 50 z3.p0 z4.e7 145 z4.f6 141 z4.fP (eg uH.b6 94 an xP.b0 1 z8.e1 2 z8.gk (k2 kt.ec.S.bp 168 iB aw.nT.kB 172 ct.eW 243 cV.fU (aG g7.fQ) (al cj)) (gz ti.S 85 iK vb 138 et sP 134 jk (i7 mZ.bH.b6.b6.bw 136 ey cX.bQ.cv cl.bQ.cv 17 cO.e7 206 ap hj.bP.bP.av))) (N bd.cH.bu.cw 54 cG.fE (aW gX.bH (dc aY.bm.fr.vz)) (j4 bO.bi.bu (lf (rp jw))))) (nm bK.A7 (oU uo.S.b2 4 z9.eY 109 an nE.b0 105 tW.b0 (fS nn.q6.b2 4 cV.eA 105 hJ ah 101 aU (co jU.aF.ec)) (du g9.aS.aj 136 et e4.bP fI.bP iD.bP 91 iK bq.cJ (lf (rP fk iC rU 20 (aM cD kD e_) 25 (aM cF kD e_) e_)))) (nd (jB jx.pl.aD 35 cq.fm 84 mf j 82 vu aE 26 cq.gH) (aW bq.iv (eo iy.bV.nS.gR.bp 143 xd 131 c6.p8 H 53 dl.fN)) (kh tu.bu.aD 171 c0.ft c0.f4 65 c0.fE (bM tu.bg 167 hB ci.mX aV.mX cC.mX 62 dq.fq))))) (nd (yN gs.aS 11 z2.p0 90 dX au z3.e7 46 z3.f6) (nd (kH aU) (gA qx.aj 100 r6 H ah aU 66 an kc.aC (mV jp.eb.b8.bw 63 mL rH pY 17 cB.f5 113 cy.gj bO (lg g9.cz.aS 11 ds.f4 184 mK H 140 lA bq) (dd n3.S aB 111 sa)) (aZ (q2 l3.dJ.aj 23 c7.f6 127 ca aH.cR.bI 111 m4.bI 107 sW) (ff y1.ag 44 dM.eA 828 cU.ga 1 dM.f9))) (nd (pk tH.b8.bw 67 cM.fT 122 lF j 17 cM.fA 88 w7 hj) (fS tw.bP.ia 4 dj.p9 103 ca ub.bI 99 e_.xE.bI (i7 oV.gR.bw 114 bv s6.aO tU.aO 17 c6.f8 109 ch h9.bi.ni)) (jz jU.GF (ac cX.gP.eF 68 dq.ex)))) (nd (qP sR.cK 188 z6.fD 139 wA ar 135 ao) (bS ka.aF (fV th.S 121 dy.eY 66 rV 62 dy.fm (aK rJ.io)) (aW e_.vC.bI.aD (e8 pc.dB 53 rR nk g2 kg 56 cL.p9))) (gI s8.S 61 cq.p5 107 wy X 103 ad (aZ (rP l4 iC Bo 32 (aM cD fB e_) 145 (aM cF fB e_) bd) (lf (q2 o9.eP.jr.ae.aC 11 dL.eZ 182 ap bO.zh.hM.fF 226 ah.vG.fj.bI 222 aU.vG.fj.bI))) (ej n1.bw 170 b7 rH.ae pY.ae 17 dI.eZ 73 di.ev (la gF.eN 37 dY.p1 dY.p0 d9.e7 19 d9.f6)))))))
def EY : ab dp:=(az fa.dJ.bg 32 cO 47 dM 43 cL (qs m2.bV 150 HG 230 HW 152 HI 306 HU (cb iT.eP.bQ 55 z1.e1 z1.gk z1.er 19 z1.eB (k2 mj.S 80 dX aw 54 z3.f4 50 z3.gO (nd (oi nx.nS.S 132 kw mE.aI 95 z7.gK H 91 z7.fi) (nd (xh m9.a0 457 cV.p8 122 cy.eW 77 hC aE 14 cy.eH) (lf (lB mQ.ia.S 84 bN i6.fF 85 dI.fq 29 dI.gb)) (fb cD Dy bd)) (ix d4.pm.bm (bZ oV.dB 87 ch q9.ni iS.ni t5.ni 122 bv b4.bQ.aO))) (N mE.bi.cJ.aO.aO 215 c5.fN (nt gr.dK.gR.aS 4 dy.ga 114 dy.gj 110 dj.gn (ac iZ.Gd.eK.dt 334 dl.f4)) (fV s0.cK 96 c9.fU 64 c9.ev 60 c9.eZ (e8 BG.dB 93 b7 nk g2 kg 60 cU.fP)))) (bc nK.aI (gI qK.cz.aS 4 z9.eW 114 c4 uO 110 oX (bT aw.bQ.xY.bu.dK.fy 131 je uK.cH (bM tD.g0 92 bN q4.g8 ur.g8 j.hK.g8 19 ds.fi)) (aZ (wP kQ.jq.eP.bV 24 cV.fT 202 cS.f8 26 cS.fp 38 cS.ft) (fb cF mD aV))) (dR my.a0 (aW K.cR.nT (ac e4.i0.gE.cw 94 c6.fU)) (ir tn.dJ.aj 23 c8.f9 129 c8.ga 113 c8.gj 109 c8.f5 (aG X.bu.iG))))) (N k0.eF 59 z2.f4 (cb gG.a0.ag 52 z4.fo z4.fU z4.fi 1 z4.eW (bc hQ (lQ uI.aD.S 335 cV.er 56 ct.fK H 113 cV.eB (g4 gG.aj.cR.iI.ae 177 dI.fu 201 dI.gO 197 dI.ev) (al b3)) (o8 kZ.eN.cR.aD 92 cA.f8 cA.fz 64 cA.gl 60 di.fE j (hT iu.cd.gZ.b2.ae 107 ey nL.cv 197 ap K.iG.ce.bi 193 L.iG.ce.bi))) (aJ ko.bl.q6 87 cG.fi 1 cG.eW 2 cG.eH (aZ (lZ yZ.cd.aD 63 yt c9.p5 92 fe hO) (co L.A3.aF.ec)) (J jU.Gp.eD.kk 221 cI.p7 (al lS)))) (nd (yC hR.S 98 z6.ft z6.f4 z6.fE 43 ep) (dQ lD.S.bl.iF 11 dn.eZ 54 dn.fo 153 dn.fN 17 dn.fU (du i5.S 60 hC au X ad 127 et aN (al h9.bg.hK)) (ek sO.bQ 169 b7 gN.ae 17 c0.gO 68 c0.ev (ly jT))) (N pr.yk.hU.bo 171 cP.p0 (bT b4.bl.eC.db 166 hD vb (al rB.bH.bH)) (en aY.wk.bl.bH (bk px.fr.hK)))))) (d3 e_.FX.cH (eR eT.aj.b2.aj b1 64 z1.eA e_ 268 iJ ak.aC 264 iJ af.aC (N nE.dh 216 z3.gH (k2 qK.S 60 an qq 102 wN 98 r6 (e2 lT.xY.bu.dK.fy 131 je bO.cH (ac g5.aI.bV.fd 159 c0.fx) (fb cF fB b1)) (dG oS.e0.cH (aG H.aF.aC.S.gB))) (bU dz.aO (dG K.cR.cH (ac ar.aF.bl.dt 342 dl.fU)) (ej li.aj.cR.aX 69 rZ ar ao 181 cI.fU 177 w3 (em gr.eb.cQ 124 cU.p9 cU.p8 54 cU.p7 50 yy)))) (nm tk (lE i3.e0.dB 79 z9.fx 87 z9.gn 163 an kr.iV (dG b1.bi.cH (cp sK.dB.ag 73 dr.er dr.eB 1 dr.fT)) (dG fX.e0.cH (eo zJ.bV.a0 55 cL.eZ 110 b7 iN 14 cL.fo))) (e2 fI.bP.hV 187 cP.fE b1 (fV n8.jr.S 111 c9.gm 85 dP.ex 29 dP.fL (bk jy.bV.hK)) (bA sK.e0.gR.dm 11 cN.fD 1 cN.fu 2 cN.gO (h6 eI.cz.gR.a0 77 jc gS 176 hB q9 14 dq.p8))))) (eL cC (nd (kH fY) (gp qx.ag 62 an uO.aC oX.aC 1 z7.p6 2 z8.p7 (eR nn.iF.S e_ 41 vp bd 95 cB.eW H 29 cB.eB e_ (bM i5.g6 72 hC g2 dZ.aC eM.aC 1 c0.p6) (q0 h7.b6 aB 210 d1.ft au)) (aZ (lB tD.b6 80 bN Bb.bI 1 cA.fq 2 cA.gb) (h6 AE.S 103 b7 aw 52 cO.eS H 48 dM.f6))) (aJ tH.bu.b8 57 cM.f6 1 cM.fP 2 cM.gK (ck cC.h8 (hT Cj.aj.b2.ae 84 pu d4 189 b7 ak.hM.cK 185 af.hM.cK)) (kN jS.eV.cf 71 Ai au X ad 90 cI.eY (g4 AC.bH.ae 52 dq.e7 64 dq.f6 60 dq.fP)))) (eg iP.eN.ag 46 rY jH 1 z6.gb 2 z6.gd (eJ gN.hK (e9 zR.aD 52 dy.f8 wz 271 di.eZ 87 xl (lf (oP hY.bw.aF.aS 4 ds.eA 80 ds.f9 76 c6.fN))) (du u0.cd.a0 176 b7 ci.jr.ae aV.jr.ae cC.jr.ae 103 pu bt (co kp))) (gp eI.ja.cR.eN 55 mf bj br 17 cP.gb 25 cP.gd (gW t7.a0.aF.bw 62 mM aY aQ 17 di.gd 90 nZ aH (d2 uU.pm.bm)) (jz H.cQ.mv (lf (eX fc.eN 33 an b1 33 fG e_ 33 an j 19 dY.gb e_))))))))
def EU : ab dp:=(d3 X (bc lV (aR bt.bP (bS dN.bm (ef kb.dJ.bi.aD 72 kA cX.gP cl.gP 60 mc ak.cH 56 af.cH (im H.cR.nT (d2 aB.aF.pm.bm) (hZ kQ.a0 113 c5.gj b1 40 c5.gb bd 135 d9.er e_ 14 d9.eB e_)) (gV kK.eK.aF 41 vh 40 da.fK 1 da.fN (aG K.o6.aC.S.gB))) (mV gF.gR.g0 79 fG jw.aD jD.aD 17 c5.fL 146 pB hj (ir sS.eb.eb.ae.aC 11 c9.ft 183 dj.p4 55 vm 51 c9.f4 (al ak.iH.bQ)) (fV lH.ag.b2.ae 71 xz 147 cS.eu 143 cS.ez (lc u3.aC 11 cU.gg 79 cU.eY 176 cT.fE 51 cU.eS)))) (c3 eQ.bI (eg sL.ag 102 an iE.b0 1 z9.eY 2 z9.eS (bT au.cH.AY.hK.dh 242 vt au (aT oO.dJ.bQ.bP 111 ds.ev 1 ds.eZ 2 ds.fo)) (bD ii.b2.b2.aj 121 cV.ex bF bE 122 hJ dN.bm 118 ie.bm (aT gr.ik 11 dM.fq 1 dM.gb 2 dM.gd))) (N aE.rG.aI.hV 70 cq.e7 (aW fY.bg.hK (bC kK.e0.q6.bi.aD 95 vn ob oo 164 vi fX 160 d8)) (ej vg.b2.aj.ae.aj.e0.cQ 118 wF K L 73 c8.p2 69 wc (e5 gr.jq.dv 164 dq.ev 66 cT.eS ar 62 ao))))) (c3 b3 (ku jy (lY s7.cd.aj 23 z8.fM 180 an dV.iV 75 z8.fx (nd (l5 jg.b6.aX 126 cy.eW 29 cB.fE 146 et gx) (bC q8.aD 173 b7 ar.nj.ae ao.nj.ae 76 vd ak 72 af) (lf (zw dD.cH))) (J cj.ni.cH.hU.aI.aI 271 cA.ex (hZ u8.S 292 xi e_ 42 cO.gL e_ 65 zE e_ 61 z2.gb aP))) (az uX.cQ 112 cG.ga 195 cM.eZ 192 cM.fo (J j.xE.mX.aF.sl.aI 134 di.fo (bC dF.jq.b2.ae.aj 66 cN.eu bF bE 180 vc jt 176 gX)) (bA d5.cx.aF.b8 204 c8.eZ 1 c8.fo 2 c8.fU (em ns.aX 54 cT.p9 cT.p8 74 cT.p7 70 zU)))) (hi gs.bP 38 z6.ez z6.fK 1 z6.fN (eJ e_.cz.gY (aZ (pe oL.bV 24 dy.gK 88 cB.eW H 26 cB.eB 38 vp) (lf (jo g9.gZ 475 dl.fD 140 ds.p8 170 jK 166 c0.fK j))) (gy fX.iG.eC (iM g7))) (mV wf.nS.S 96 lF ak af 102 Am 98 xA j (nt B4.pl.iF 4 di.fU 99 vd 17 cA.ez (aG bF.S.gB)) (bD na.aD 72 ch ar.nj ao.nj 111 bv cg.aO 107 b3.aO (fW ka.cx.bu)))))) (nd (rP eE iC tA 24 (aM cD dE e_) 65 (aM cF dE e_) e_) (aR g7 (aJ eI.dJ.dm 11 z3.p7 1 z3.p6 2 z3.p5 (lY g3.bV.b2 11 z8.eZ 100 an uP.mv 63 z8.fo (gI ph.ag.aS 4 ct.fE 68 pn dZ 64 eM (bC tr.cx.bi.cs 91 bN aY.d6 aQ.d6 84 ca ke.bl 80 iX.bl) (iM ah)) (bA ti.dm 11 da.gj 1 da.f5 2 da.hH (bZ pI.jr.aj 189 ap jn.eK.av o7.eK.av j.nj.eK.av 135 ey fY.aX.cv))) (fR iA.a0.bP 44 cG.fP 231 cG.fo 1 cG.gK (ek o0.g6 62 pn jN 1 c9.fM 2 ct.fE (bC re.bV.aj 71 pu aY aQ 188 b7 eQ.cK 184 dz.cK)) (aZ (ry kQ.jq.eP.g6 76 vo 1 cI.eY 2 cI.gm) (lf (rp aY.yk))))) (nm lV (nw j3.fg 118 c4 iX 76 an jl.i9 72 ju.i9 (fO h7.iI.bV.a0 80 ct.p9 121 zM aE 14 cV.fq (cp tK.q6.bw 197 c6.fC c6.gv 19 c6.fq)) (eG ti.bw 67 hC H.vS ah.vS aU.vS 19 c0.gH (bZ jA.it 148 zx au X ad 57 rQ b4))) (N au.cH.o6.eD.aI 58 cq.fL (aW j5.bH (mg j8.cz.b8.dm.aS 11 dl.p8 188 ap hj.sl.hL.bI 130 vl K 126 L)) (kh tb.ia.aj 176 c7.fz c7.gl 111 c7.e1 (aK iX.bp))))) (az gs.b6 42 z2.p9 1 z2.p8 2 z2.p7 (cb nM.S.a0 96 z4.p0 z5.e7 z5.f6 119 z5.fP (nd (tI uo.S 61 an lR.gP 97 g2.aS 93 kg.aS) (nd (wR uL.aC 11 cB.gb 71 cB.gH aH 234 dj.er 86 cB.eS) (g4 jg.b6.cQ.S 134 c0.p9 151 ds.fP 49 ds.gK) (dd mj aB 220 iJ)) (aZ (qU xq.b2.b2.aj.ae.cz.ae 67 wV K L 120 wC 116) (aK jk))) (ef wf.eP.aD 60 xw aY aQ 102 xD ak 98 af (eG nD.ag.ag.bi.bm.aF 64 vm aE.kv K.kv L.kv 1 dj.ga (al lM.a0.hK)) (en tk.bV.hK (aG fY.fy.iG)))) (nw jm.hL.bp 55 mc i6 79 kA mT 75 rC (gA pg.cd.a0 76 fG e3.eN ed.eN d0.eN 171 pB aw (ek oO.cQ.bP 179 lm pr 1 dy.fK 2 dy.fN (ac K.aF.bl.dt 342 dT.hH)) (gz uw.ae.b2.ae 96 nZ d4 72 mM ak.hM 68 af.hM (kf kV.aj.cR.ja bd 4 cU.fo e_ 50 cL.f5 H 46 tO aP))) (aJ fa.bl.bi.b8 87 cy.e7 1 cy.f6 2 cy.fP (ej oK.hL.eN 102 ca rE.bI rN.bI 17 di.p7 25 di.p6 (al X.bm.bH.bH)) (de ty.hK.gD (lf (qG j))))))))
def Es : ab dp:=(nd (Br rv.iF.aj fY 124 dq e_ 65 dY e_) (pL nu.aX 149 Hi 316 Hj Hx 31 H2 (k2 eT.gC 252 iJ aw 56 z1.fo 52 z1.ez (bS ci.eP (gp h3.eN.a0 90 kw eQ.fF dz.fF 107 z7.fT 14 z7.fA (dR dk.a0 (qm m9.cQ.cs 355 dl.p7 356 dl.p6 509 mJ eQ.cR 505 dz.cR) (lf (wW gx))) (gW nn.q6.b6.bw 113 hJ ar.bm ao.bm 17 da.gl 128 cV.ex bO (lf (xB lK.bl.eV.bi.aD 177 ap bF.zh.hM.fF bE.zh.hM.fF 233 eQ.vG.fj.bI 229 dz.vG.fj.bI)))) (bU bE.bu (ck uS.h8 (pM n5.pl.aI.ja 4 c6.fA 116 ds.ev H 112 c6.eA)) (mR fk.dJ.bi.cd.jq 4 cS.p6 64 cS.ev H 60 cI.gd (ac aE.eh.dh 139 cU.fT)))) (bc tT (rz B9.cx.ae 162 z9.fD 69 an K.hU.aC 65 L.hU.aC (k3 ra.cd.bi.aD 165 cV.e7 e_ 165 cV.f6 e_ 173 iB dN.mX.kB 56 ct.ev j (bC qQ.aj 66 pz K L 179 b7 nr.ae 175 mh.ae)) (bD wG.S.cx.aD 117 iq bj.ym.jd br.ym.jd 74 ep H.kB.n2 70 j.A3.n2 (aT dF.ik 11 dM.fK 1 dM.fN 2 dM.ex))) (dQ ol.aS.aC 11 cM.f9 177 cq.eu 118 cq.ez 53 cM.eW (J aP.FH.ib.bP.eV.dK.fy 253 dP.fp (ac cj.i0.gE.cw 99 c6.f5)) (J jN.bg.cJ.bi.hL.dx 156 c8.p5 (al iS))))) (N iN.iH.qW 283 z2.fo (ku fY.bm (aJ qX.g6 67 z8.fm 1 z8.gH 2 z8.gm (nd (pJ oy.cz.S 119 lo au X ad 78 rO) (co gu.ec) (lf (kH L))) (e9 gG.jq.cR.cQ 220 cA.e1 cA.gk 60 lJ 56 yH (aT qN.dm 11 cO.gm 1 cO.fC 2 cO.gv))) (dR K.iI (ck aw.mv.nj (lg lW.b2 11 cN.er 92 ch dV.aC 105 bv aN.aO)) (e9 gG.aj.cR.hL.eN 104 c8.fP c8.gK 17 c8.fp 25 c8.ft (eo fa.aj.aF.a0 55 cT.hH 115 sc au 14 cT.gL)))) (lQ gU.bV 22 z6.fi 81 je H 120 z6.gl (ei il.cz.bu.aD 49 dn.fA dn.eu 63 dn.ez 26 dn.fK (aZ (pW rq.dK.cx.ja.aC 11 cV.p2 185 iB oZ.o6.kB 300 c9.p9 179 cV.p1) (g4 kZ.eb.bg.ae 64 ds.gk 84 ds.er 80 ds.eB)) (ek n1.b8 174 b7 e_.cK 1 cA.eH 2 c0.f8 (co jT))) (aJ ri.ag.eN 69 cq.p4 17 cq.p3 25 cq.p2 (J jN.xY.r5.eF 171 cA.eZ (em i1.pl.bp.aj 203 dl.fC dl.gv 88 dl.fq 84 dl.gb)) (ir uc.aD.aF.aj 23 c7.fA 265 dI.eu 249 dI.ez 245 dI.fK (fW cj.eV.bu)))))) (nd (rP qu sd BH 28 (aM cD hI e_) 105 (aM cF hI e_) aP) (rz i3.fg 61 z1.hH 243 iJ bF 239 bE (az dF.ec.aS 4 z3.ga 50 z3.gj 46 z3.f5 (cu m2.a0.ag 98 sf ed nl j.aI 1 z8.e7 (gA oM.bl.bg 53 vu au X ad 99 mf aw (iL u0.cd.ae 172 b7 bj.xK.ae ut.ae 71 dI.p0 67 dr.e7) (la i1.ag 44 d9.hH d9.gL d9.p9 1 d9.p8)) (du iu.cf 165 ap q9 iS t5 67 ey aN (aG g5.bm.fr.gB))) (eR eI.iF.S e_ 41 c5.f5 bd 77 c5.p1 H 29 cN.fz e_ (J aP.fj.bV.fd 159 c9.ex (em lH.dJ.cR.b8.bw 79 dl.gO dl.ev 17 dl.eZ 210 dl.fo)) (od uF.e0.aF.aj 23 cI.er 85 ve gx 131 iz fX.kv.iH 127 d8.kv.iH (ac g5.iG.eD.aI 239 cT.gv)))) (bS jv.bu (aJ j3.dm.dm 11 z9.gL 1 z9.p9 2 z9.p8 (kh ma.ag 106 yo cV.ex 1 cV.fL (i7 qf.b6.bw 190 jK cX cl 17 dr.f5 154 mK aH)) (aZ (lB l8.aD.ae 475 dX d4.bg 498 dr.eY 494 dr.eS) (nA li.gZ 61 cL.fz cL.gl 91 sj cj 87 dS))) (nd (ry qi.dJ 11 cq.er 1 cq.fU 2 cq.eB) (aZ (oE eI.b8.cf 214 un 67 pn ah 63 aU) (em n5.aj.ia.cQ 78 dl.eu dl.ez 29 dl.gd 26 dl.fA)) (jz bd.S.vz (bZ iA.kl.cR.bg 145 hB H.kY.wi mT.wi rC.wi 68 mH qc.hM))))) (oq ah (nd (kH cC) (aJ iT.bl.ik 11 z9.e7 1 z9.f6 2 z9.fP (im ar.mX (e8 tG.fj.S 76 yW au X ad 119 c0.gd) (dd k8.b6 aA 9 cO.gO)) (du t7.a0.bP.bg 62 mL aE.kB K.kB L.kB 238 vt ki (h6 kQ.gC 143 sa aw 56 cO.gd H 52 dM.gK))) (dR L.bg (m5 tP.bu (bZ fk.nS.cx.cR.cf 89 zF au X ad 139 w9 aN)) (ck kn.fQ (hT dF.ag.eP.S 139 hB lR 80 jc cj 76 dS)))) (mV fc.b6.bw 100 wA bj br 17 z6.p9 57 nX bO (nd (oC g3.ho 129 dn.p8 dn.p7 78 fG K.aD 74 L.aD) (aZ (qp w0.cK 93 xl L 62 wz K 58) (ac jH.cx.aI.eC.bu.bz 393 c6.fD)) (fS mQ.cz.ja 4 cA.gH 73 ca aE.Ga.bH 69 aP.iH.bH (e5 jA.dJ.fg 65 cL.gl 95 sj lk 91 kS))) (N j.xM.dt 73 cP.p9 (aW oD.bw (qm j8.cz.b8.dm.aD 35 dl.p1 158 dl.p0 188 ap H.e0.hL.bI 184 j.xE.hL.bI)) (o8 fa.aj.aF.cf 71 dI.gg dI.eY 95 AP 91 wl j (co bK)))))))
def E4 : ab dp:=(hS fc.dv 108 HP 225 HJ 222 HR (m6 pR (aR jk (bS e3.eP (cu nx.bl.ag 92 kw ed.fF nl.fF j.aI.fF 1 z7.gb (nd (uZ oM.iF.b2 4 cq.fN 244 cP.eu H 240 ky) (ac kW.r5.iv.bm.dx 164 dI.gL) (lf (yz i1.aX 44 c5.gb 29 d9.eY 64 d9.eS))) (dG ah.e0.cH (bZ ot.nS.S 129 ey e_.ae.cv lM.cv ui.cv 191 ap b4.eK.av))) (nd (lL kZ.dJ.bg 36 c5.gg 94 c5.fA H 38 c5.eY 56 AA aN) (k3 nb.eK.aS 11 c9.gk e_ 35 c9.er e_ 274 dP.fU e_ 110 ct.fx aP (dc af.pU.sy)) (J jZ.cJ.bi.hL.dx 156 cI.gK (aG kx.aC)))) (N jZ.Aw.bz 154 z5.ex (cu uo.eN 89 an aA.ia.aS aB.ia.aS dD.ia.aS 19 z9.gv (aW aP.sl.nT (aK fX.io)) (fh i5.gC e_ 183 c0.fK e_ 139 lA H 470 dr.eu e_ (cp h7.g0 50 cL.fA cL.eu 19 cL.ez))) (N eQ.aO.hU.bo 548 ct.eu (ng kK.bQ.aC 11 dP.eH 83 da.eu 128 dP.f8 (dc t0.gP)) (j4 oD.aI.bu (pa aN.A7))))) (c3 iD (bc rK (nd (jB nF.aS 11 z8.eH 65 an oZ.aC 103 c4 K 99 z8.eW) (eR sQ.dm e_ 11 cG.fz b1 1 cB.gO e_ 2 cB.ev e_ (al dV.mu.bH) (al dV)) (gz oY.S 67 xj aN 102 bv dk 98 e6 (g1 ny.cd.aj 23 dM.eZ 77 cL.fp 51 cO.fA aw))) (nd (wR rd.aC 11 cG.hH 65 xw aH 95 cG.gL 91 xD) (jW uL.aS 11 dj.fT 77 xj gf 94 bv gS (mb l8.b8.b2.ae 149 vi 92 vn K 88 L)) (J bt.pE.xK.cH.hU.aI.aI 317 cN.gK (lf (oP tM.bl.aS 4 cT.p2 62 cT.p1 58 dq.eu))))) (d3 hW (ei cZ.aS.e0.cQ 71 dn.fC dn.gv 58 dn.fq 54 xa (bT px.aX.rG.bm.bz 122 dX kx.fr (aK cC.fr.hK.gD)) (aZ (rM BW.q6.aX 169 b7 b3.cQ 29 cN.p7 189 bd.aS.ae) (e5 v7.fg 57 dM.p0 87 vq jl 83 ju))) (aJ jx.pl.b6 239 cP.eu 1 cP.ez 2 cP.fK (md BU.bP.bg 58 di.fL 406 b7 ak.ni.ae 254 c7.fx (iO d4.mu.hU.gE.cw 232 ap d4.xE.fF)) (e9 kt.eb.cz.aI.b8.bw 408 cN.gH cN.gm 17 cN.fL 252 cN.fC (bZ n3.fj.gR.bH.bg 70 zP au X ad 122 yB aN)))))) (eL oH (eL h5 (ku H.eP (gI dF.iI.aj.ae 72 pw 103 nY K 99 L (az s9.q6.bi.cQ 69 cP.fm 162 ct.er 241 cV.fz (aG kp.fQ) (al b3)) (gV jp.eN.b2.ag 81 da.p1 168 c7.fD 1 da.p0 (ij kL.S.S.dK.S 194 ap b4.eK.av 136 ey lM.cv 132 ui.cv))) (nd (Ar ah.yk) (iw ro.dv 105 nW L 67 lF bj 63 br (bC iy.ec.b6.bi.aD 61 wS aY aQ 179 vc fX 175 d8)) (ir ql.dm.cd.aX.bl.aS 11 cI.ga 47 cI.gj 238 c8.gv 69 cI.f5 (em i1.a0.aj 183 cT.fU cT.fi 60 cT.eW 56 cT.eH)))) (qv H.bV (cu um.a0.ag 119 c4 va nl.aO j.jQ 1 z9.p0 (bT j.bg.rG.bm.bz 114 dX aU.bg (aT oW.dK.cR.b8 105 dr.fi 1 dr.eW 2 dr.eH)) (md sY.S.b2 11 cN.p2 112 hD ci.aO 131 cN.p1 (aK jT))) (aJ zC.dm.aX 168 cP.ga 113 cP.gj 110 cP.f5 (fO nb.bQ.S 75 c9.p1 139 xn vU 41 dP.gL (h6 lW.bV.a0 117 bv aw.eN.aO 104 ch tS.ni 14 dl.fL)) (en fY.bm.bV.hK (co aH.bg.eK))))) (bc ci (bc iY.aI (gA l9.aD 105 r6 g5 gq k6 75 an v1.h8 (lE oM.cx.aD 73 cB.p8 279 dy.gg 61 mM aw (bZ l3.eP.aD 90 bN e4.vG.jd fI.vG.jd iD.vG.jd 79 ca bq.kY.bH) (dd gr.a0 aB 261 d1.p2)) (gW qN.cd.ag.bw 140 iq nC.bI nH.bI 17 cA.p3 79 ep h9.cJ.ja (d2 aV))) (fR j7.bQ.aj 35 cM.fN 43 cM.ex 53 cM.fL (fS lK.cK 67 cV.eZ 194 bN h5.fF 190 d4.fF (al H.rG.bH.bH)) (J bd.S.jd.eD.kk 221 c8.fM (bk gX.gY)))) (gI o1.ia.cR.ja 4 z7.f4 54 mc rb 50 tg (nd (lZ s7.S 129 c5.fE c5.fD 70 fG kr) (aZ (jB uw.aF.iF 11 dy.fC 64 sk bO 116 nZ K 17 dy.gv) (aK lS.io)) (bD rI.gC.aj 72 ep ar.cJ.ja ao.cJ.ja 149 iq mY.bI 145 iQ.bI (ly gu))) (nd (jo oy.cz.aj 23 cy.gk 171 ct.gv 153 cy.fU 74 cq.p4 j) (gW kt.ec.fj.cJ.S 85 mG K L 168 zu 164 cV.er j (g4 o0.fj.ae.b2.ae 106 dl.fT 82 dl.er 78 dl.eB)) (eG qa.b6 100 bv ah.aO bK.aO ea.aO 1 dT.eZ (lf (qG H))))))))
def Fc : ab dp:=(nd (rP j2 iC Dp 24 (aM cD f7 e_) 65 (aM cF f7 e_) b1) (cb nM.S 84 HQ Ik Ie 89 Id (aR ah.bP (nd (rP eE iC tA 24 (aM cD dE e_) 65 (aM cF dE e_) e_) (aJ kj.eV.dJ 11 z7.eZ 1 z7.fo 2 z7.fU (N e_.eK.i0.bo 77 cy.fo (bZ mQ.ia.aj 84 bN aA.aF.fF aB.aF.fF dD.aF.fF 109 ca aw.cR.bI) (lf (wW ah))) (fh s5.ho.bQ bd 65 ep e_.A3.n2 17 da.eZ e_ 124 iq j.ym.jd (lf (jB th.aj.ag.iF 11 dL.fT 188 ap hj.eC.av 122 ey K.cY 17 dL.fA)))) (bU ci.fy (aZ (eU cF Dr ar) (iL wZ.bV.pl.ae 86 vn K L 151 ds.fm 147 vi)) (bA u3.cx.b6 197 cS.fC 1 cS.gv 2 cS.fq (co gu)))) (nd (kH vb) (cu iT.bl.g0 153 an e4.iV fI.iV iD.iV 19 z9.gk (fS kV.ec.b2.aF.aX 163 cP.p1 66 sb K 62 L (bC tr.cx.bi.gZ 95 bN fX.g8 d8.g8 80 ca ah.cY 76 aU.cY)) (aW nL.hM (bM rI.ag 48 ep X hW ld 1 dM.f5))) (az ri.ia.S 149 xA 85 cM.gv 29 cM.fq (aW j.mX.nT (iO o4.bV.rG.bm.bz 114 dX gu.bg)) (en pT.eh (aG af.pU.vS))))) (N nl.eV.dK.fy 188 z2.gK (ku cC (qw g3.bV.b2 4 z8.eu 61 z8.ez 58 u7 (qe fa.bl.bi.aD 47 ct.ex 650 cS.gO 91 cy.e7 aw (bk lT.eh) (al kr)) (bA sV.bH.bi.b8 139 cA.fo 1 cA.fU 2 cA.fi (ij th.aj.ag.dv 196 ap d8.bP.av 120 ey lk.cv 116 kS.cv))) (N rb.bu.cw 186 cG.eZ (bD tG.aF.aD 68 yt bj br 101 fe ug 97 aP.n2 (ac iZ.nj.vC.Eg.fy.bz 81 dT.er)) (de cX.o6.bp (lf (rP l4 iC GA 32 (aM cD fB e_) 145 (aM cF fB e_) e_))))) (bS H (dQ fa.a0.aC 11 dn.f4 71 dn.fE 148 dn.gl 43 dn.fD (gz h7.iI.nS.S 139 lo aw 80 xc ah 76 aU (al br.iH.bQ)) (fh qQ.b2 bd 4 cA.f4 aP 70 cA.f6 H 66 c0.eZ aP (ly hQ))) (nd (rP j2 wU Cx 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (fO jp.eN.b2.a0 81 dj.fp 175 y6 aE 14 dP.p3 (hZ lK.bl.b6.aD 173 ap bF.d6 173 ap bE.d6 135 y0 aE 26 dl.gk e_)) (J aH.pE.xK.cH.hU.aI.aI 317 dl.gK (aK hW.bQ.bp)))))) (aR aE.ec (e2 j.bm.bu.bu.dh 151 iJ aP.aC (cu wG.fj.S 58 dX nk g2 kg 135 z3.eS (aJ nM.gR.dm 11 z7.eA 1 z7.f9 2 z7.ga (e2 lM.rG.bm.bz 122 dX K.fr (iO aV.hL.aI.hV 231 et H.bH) (lf (rP rx.dJ.jr iC x6 28 (aM cD mD e_) 105 (aM cF mD e_) b1))) (iw oL.cz.ae 113 sh br 86 hJ h5 82 d4 (ac iS.pE.eP.aI.db 114 dL.p3))) (gI gG.jq.b2.ae 184 c5.fT 60 wu K 56 L (dG ie.hL.cH (hT sO.S.S 76 pz aN 189 b7 ed.aC.ae 185 d0.aC.ae)) (J aU.iv.bm.dx 164 cI.fu (lf (rp aH.yk))))) (dQ iT.dK.aC 11 z5.gv 136 z5.fq 162 z5.gb 29 z5.gd (nd (tI hR.bl.bi.cf 71 an tT.gP 107 dk.b0 103 e6.b0) (J H.cR.bV.fd 159 ct.gH (aG iQ.fQ)) (dG jn.bm.cH (cp y9.bw 54 cL.fL cL.gg 19 cL.eY))) (N X.aF.vG.bi.aO 65 cq.fU (J aV.hL.bV.fd 159 dP.fK (d2 eQ.aI.pm.bm)) (J mE.aO.kY.eF 925 dT.p0 (lc ua.cK.cQ 235 dq.p0 236 dY.e7 144 dq.p2 140 dq.p1))))) (eL ci (lC cD Bc bd (bc jV (nd (pJ qi.S 99 lo aE K L 76 xr) (aT lU.eV.b8 65 c0.f5 1 c0.hH 2 c0.gL) (dd cZ.a0 aB 170 d1.ft)) (eG ud.bl 66 ca iY.bH aE.Ga.bH aP.iH.bH 1 cA.gH (g1 zB.aj 23 dM.eW 81 cL.fD 55 cO.fL aw))) (lj t8.ia.ag 91 sM aE 91 uG bd 1 cG.p0 e_ 2 cM.e7 e_ (gz mQ.S 76 bN i6 65 ca dk 61 e6 (al i6.mu.bH)) (fh jA.dK.gR.cf e_ 125 cI.gg e_ 81 vo H 77 cI.fL aP (bk gf.gY)))) (om jm.iI.iF 11 z6.gv 61 z5.gk aE 95 nX hO (k2 gF.gR.b6 67 fG zq 1 dn.eA 2 dn.f9 (gV uD.aj 35 dy.fi 43 dy.eW 99 dy.eH (al ar.iH.bQ)) (gy j.ib.iG.eC (e5 wM.fg 61 cL.fE 91 mH jl 87 ju))) (N cX.eC.db 60 cP.fq (bD jx.aj.e0.cQ 92 nZ h5 d4 68 mM aY 64 aQ (bM oV.g6 118 bv iS.aO nK.jQ qJ.jQ 1 dL.ft)) (J jn.vC.hK.bm.dx 164 cN.gv (lf (zo rI 103 d9 36 an 95 dY.gH 14 dY.gm))))))))
def EL : ab dp:=(hS cZ.ec.bw 115 Gq 17 GI 50 GG (aJ gU.eb.cQ 78 G2 93 Hu 89 Ho (aR dV.bl (cb eT.b6.bw 125 z3.eB z3.fT z3.fA 19 z3.eu (o2 fc.a0.bp 77 kA bq.gP 61 mc X.cH 57 ad.cH (N q4.i0.bo 68 cy.eS (d2 lT.bl.pm.bm) (ji b3)) (bT bd.FX.CQ.dt 362 mJ v1 (bM iu.aS.S.eb.aF 195 w6 H ah aU 1 dL.fL))) (ef iT.eb.e0.cQ 148 pB b1.mX uB 85 fG jw.aD 81 jD.aD (aW cX.nT (al rS.mu.bH)) (e9 u6.bP.aX 174 cS.e1 cS.gk 29 cS.er 194 cS.eB (eo qt.cK.S 86 cU.fL 57 cU.eH H 191 cT.fm)))) (eL qI (eg nF.b6.ag 111 c4 jN.bu 1 z9.fL 2 z9.gg (gW ol.bH.bi.aD 296 lm aY aQ 417 dj.p5 128 ct.fz j (dc cg.cQ.mv)) (kN uI.aI.cJ.S 149 pA dO cj dS 72 da.eH (ij tx.aX 50 ep af 109 iq cX 105 cl))) (gp sX.q6.bw 492 je lk.cH kS.cH 17 cM.p5 221 cq.gv (md ta.bi.eN 62 dP.gO 368 ky ur 19 dP.ev (bC na.iI.aj 102 ch ar.bi.ni ao.bi.ni 123 bv hQ.aO 119 g7.aO)) (ix ao.Cv.bm (aT dF.ag.eP.dJ 11 dq.eS 1 dq.fm 2 dq.gH))))) (az h7.a0 38 z2.er 115 z2.eB 14 z2.fT (ku ju (gp nG.eK 101 c4 e_.eK e_.mu 1 z8.gv 2 z8.fq (fR g9.ag 124 cB.ft 459 c9.gL 1 cB.f4 (lf (lZ n1.aD 61 dI.p2 dI.p1 178 b7 aw.cK)) (lb np)) (bT aU.AW.kv.hM.bu.bu 61 iz j.fr.iH (h6 fk.gC 63 rR aw 48 cO.eH H 44 cO.hH))) (N k9.iH.ib.bo 59 cG.gH (J rB.Gd.eF 166 di.gO (mg na.aS 11 dT.eu 111 bv bd.pU.cJ 80 ch ah.aC 76 aU.aC)) (en kO.eh (aG rB.vS)))) (az gF.bV 22 z6.e1 41 rY 37 z6.er (pQ aY.yk (aZ (qk uW.aj.S 68 zz 93 fe X 89 ad) (fJ b4.ya.eC)) (gy jU.GE.eC (cp pV.S.fH 59 cU.f4 cU.fE 1 cU.fD))) (gI v8.eb.ia 4 cM.fE 99 sM K 95 L (ir rg.ec.aD.aC 11 di.fp 97 di.ft 57 di.f4 53 di.fE (al af.pU.bH.bH)) (de ah.io (bk cC.fr.hK)))))) (hS i3.iI.iF 4 z1.fp 109 z1.ft 17 z1.f4 (aR m3.bl (bU uO (m6 X.S (nd (xh ou.bQ.aC 11 cy.p1 127 ct.f6 369 je b1.aS.cH 114 cy.p0) (bM tB.eP.eN 84 iK iZ.wq iY.wq mW.wq 19 dT.eH) (al iD)) (iw ri.ag.dv 85 rO af 130 lo bF 126 bE (mg tJ.dJ.aD 35 dL.p7 165 ey hj.bQ.cv 199 ap ug.eK.av 195 aP.n2.eK.av))) (aJ n6.aX 28 c5.p2 44 c5.p1 40 c5.p0 (aZ (nJ u5.aS 11 c9.gv 65 c9.fq 163 ap qR 159 tN) (fb cF vr dN.gP.bm)) (aW jy.xM (aG aN.iG)))) (qv vU (nd (Aa fc.eN.cR.b8.bw 97 an oS.b0 oz.b0 17 z9.p5 73 lV.i2) (ek qd.q6 100 hJ jN 1 ct.p7 2 ct.p6 (lf (oT tn.pl.S 200 c6.eY c6.eS 99 zf 95 c8.p3 j))) (bD l8.cf 70 hC nr mh 137 et j5 133 lG (e8 rk.S 108 hB au X ad 53 dM.ga))) (lj sR.cz.bi.aD 228 cP.fm aY 228 cP.fm aQ 382 yv dV 64 cM.f5 j (aZ (wE uV.kl 83 cy.ev 146 lo iN 14 dP.ga) (bZ g9.cx.fj.S 152 mK tq j5 lG 200 jK kr)) (en ke.eh (aK aw.eN.bp))))) (bc H (nd (kH b1.wq) (lQ qX.S.S 53 z9.fu 153 an aE.iV 63 z9.gO (e2 aE.mv.aI.db 232 ap aE.cx (aT lU.ik 11 dr.gl 1 dr.e1 2 dI.fx) (q0 uA aB 111 b7 au)) (m5 L.xY.bu (h6 i1.gC 104 sj k9 60 cO.ga H 56 dM.fE))) (dR ak.S (m5 qR.bu (mg nh.cx.fj.cQ.aC 11 c6.gl 100 vn oZ 157 vi dZ 153 eM)) (nt tz.bi.ae.ia 4 c8.fC 241 cN.f8 72 cN.eH (aG L.bu.iG)))) (nw tp 102 yw L 55 kA k0 51 jZ (hi rm.a0 47 c5.fP c5.gK 203 c5.fp (gy j.kY.aI (bC ud.ho 78 ca aY.wk.bl aQ.wk.bl 101 bN fX.d6 97 d8.d6)) (aZ (ow oK.cd.aj 23 c7.p1 119 bN e_.bP.g8 93 hO.fj.bI) (pa dZ.fr))) (ef ro.ho 101 cM.eu aY aQ 71 cM.ez ak 67 af (bD nD.ag.ag.bi.bg.aj 105 cV.fD ak af 573 ts cg 569 b3 (mb u5.e0.gR.aX 84 dL.ev 183 ap bF.fj.bI 179 bE.fj.bI)) (gy aw.pG.iG.eC (fb cF hI b1)))))))
def Dz : ab dp:=(c3 K.AW (hS h3.ae.aC 4 HS 215 HZ 211 Hk (aR bd.aF.bl (aR e6 (aJ h3.pl.ag 89 z7.e1 1 z7.gk 2 z7.er (lY rd.aj 23 cy.ez 125 uC ci 99 cy.fK (pM pc.dJ.bm.bg.b2 4 dr.fo 131 c7.fu H 127 w9) (ji b3)) (bT q4.kv.pU.hK.dh 305 ky q4 (hZ iu.aS.eK.bi.aD 173 ap bj.ym.hM.fF 173 ap br.ym.hM.fF 247 ap au.ni.fj.bI 58 dL.f8 e_))) (nd (lZ g3.ho 129 c5.gk c5.er 78 fG bq.aD) (aZ (wP iu.cd.bV 24 ct.fi 170 dy.p4 26 dy.p3 63 dy.p2) (ac bq.i0.gE.cw 88 c6.ev)) (bA d5.cz.cd.bQ 70 cS.p9 17 cS.p8 122 cS.p7 (iM jV)))) (nd (kH j5) (k2 j3.ae 60 an aQ.aC 73 z9.eB 70 z9.fT (hX ra.cd.bi.aS 11 cV.gK 70 dy.f9 173 ct.fD aw (d2 ak.aS.vC.bm)) (aZ (jB rI.ag.bQ.aC 11 cS.fU 80 ep bO.ya.n2 169 iq dN.bV.jd 41 cS.fi) (e5 cZ.dv 46 cO.gL 69 z2.gb bj 65 br))) (nd (pP cZ.aj.S.b2 4 cM.gn 100 uC H 96 nW) (ir xq.b2.b2.aj.ae.aj 183 da.gO 184 da.ev 479 cS.p3 476 cS.p2 (lf (eX o3.aI.cz.S 122 dl.gn e_ 122 vl H 122 dl.gn aP 180 ap l6.hL.bI))) (bA tu.bu.b8 57 c8.p9 1 c8.p8 2 c8.p7 (bk dS.gY))))) (nd (rP eE sd D1 24 (aM cD dE e_) 65 (aM cF dE e_) b1) (bU cj.eN (bc kp (e2 dk.i0.bo 204 fe au (nA n1.aD 61 dI.p7 dI.p6 178 b7 ug.ae 174 aP.n2.ae) (lb d0)) (gW BY.eK.bw 98 pz K L 17 cA.fT 179 b7 o5.cQ (aT zB.ag 51 cO.fL 1 cO.gg 2 cO.eY))) (dQ h7.aI.eN 45 cG.ez 46 cG.fK 17 cG.fN 25 cG.ex (fV oY 86 bv 59 ch 55 xj (lg na.jr 11 dT.fL 112 ch jv.aC 107 bv rK.aO)) (J eQ.iv.bm.dx 164 c8.f6 (bk gx.gY)))) (az m8.bl 76 je 1 z6.eZ 2 z6.fo (pQ dN.eC (fh s8.a0 bd 103 uC bt 83 rc aE 14 cP.e1 aP (fJ aN.A3.eC)) (k3 n1.aS 11 c0.gl e_ 178 b7 h9.nj.ae 69 cA.f6 aE 65 vd aP (co hQ))) (lj rd.aD 59 cq.p9 e_ 118 cq.p8 e_ 319 cM.ga H 57 cq.fu j (J nl.r5.eF 171 cA.gO (al pT.kv.aX)) (kh sK.e0.gR.bw 69 c7.p4 c7.p3 19 c7.p2 (bZ gG.b6.wq.S 159 hB e3.aI uU d0.aI 82 jc pd)))))) (nd (rP qu sd BH 28 (aM cD hI e_) 105 (aM cF hI e_) e_) (aR kp (bU L.mu (nd (lL nM.aO.S 114 z7.p2 190 z7.fC H 116 z7.p1 97 kw lR.fF) (nd (uT uw.aF.aj 23 cy.p7 80 mL bd.aS 64 mf ak 60 af) (ff os.b8.bg 121 cA.ex 288 dr.fC 235 dr.gv) (la li.eN 41 d9.f9 d9.ga d9.gj 19 d9.f5)) (ck jU.aF.aC (aG cl.aC.S.gB))) (N C5.eV.dK.fy 51 c5.gd (J au.bm.aX.pG.bo 213 dP.e1 (lf (tQ l8.iI.cx.bw 141 w1 bj br 17 dT.fq 215 ds.fm))) (J eM.hU.bP.eV.dK.fy 92 cI.e1 (ff d5.aj 23 cT.fP 76 cT.gK 50 cT.fp)))) (lC cF vr aE.nS (nd (oi qx.bV.a0 116 c4 aw.eN 92 an q5.i9 14 z9.f5) (aZ (lz jl.cY) (lf (tI oK.iI.ae 85 bN j.wi.fF 109 ak.aS.cH 105 af.aS.cH))) (gz kL.S.S 170 ap b4.bi 76 ey dk 72 e6 (eo pV.S.bV.a0 59 cL.eH 150 sa iN 14 cL.f8))) (aJ uX.eK.dm 11 cq.gl 1 cq.e1 2 cq.gk (fS B6.b2 4 dP.fM 69 ey bK 65 ea (aG nr.eK.ce)) (de e3.gY.gD (bC rf.aj 83 sc bF bE 67 vk jt 63 gX))))) (lC cF f7 b1 (nd (kH ci) (eR l9.a0 e_ 109 c4 rK 107 an dO.ce 14 z8.p1 e_ (aJ eI.bu.gR.b8 246 cB.ez 1 cB.fK 2 cB.fN (ml dz.aI.cH) (dd tM aB 247 d1.gd)) (aZ (lL jx.aj.gR.bg 36 cA.f5 106 mM K.xM 38 cA.hH 68 sk i6) (lf (ow qg.aj 23 dM.fz 81 mF dV.bl 55 bt.bP)))) (e2 qM.hU.bo 546 je lT.cH (aZ (qP eI.ja.cR.cQ 231 vt 59 mL bj 55 br) (aK br.vC.cJ.fr)) (bA uh.ag.ag 65 c8.ex 1 c8.fL 2 c8.gg (eo n6.bQ.S 61 dq.fu 60 cT.fq H 56 dq.gO)))) (gI hR.eV.S 90 z6.gj 51 rY X 47 ad (eJ rJ.gY (bD w0.eP.aD 66 cB.gH aY aQ 97 cB.eS ak 93 af (ac g2.vC.Eg.fy.bz 319 ds.gj)) (jW tD.aS 11 c7.e7 83 ca b1.cY 84 bN bd.fj.bI (iM jX))) (nd (rP j2 wU r1 24 (aM cD f7 e_) 65 (aM cF f7 e_) e_) (ej i1.a0.cx.bw 64 yU ak af 17 di.ga 138 di.gj (al iX.kv.aX)) (jz fY.aX.mv (lf (yz BD 40 an 29 dY.f9 60 dY.ga))))))))
def Ds : ab dp:=(c3 o5 (m6 aw.S (hS qg.b6.bw 107 z1.eY 17 z1.fm 71 z1.gH (bS mW.bm (cu h3.eN.ag 90 kw aV.bI nK.bI qJ.bI 1 z7.fq (N ah.aC.hM.gT 82 cy.fq (em kt.eb.cx.ae.cR.b8.bw 248 dr.p8 dr.p7 17 dI.fA 364 dr.p6) (fb cF mD H)) (bA nn.bl.dm 11 dP.gm 1 dP.fC 2 dP.gv (lf (tZ iu.cd.cx.cz.aX 185 ap gX.av 29 dL.ex 205 tP.av)))) (bU aY.aO (bA ta.bi.dJ 11 c9.eW 1 c9.eH 2 c9.f8 (fJ qM.iG.eC)) (j4 d4.bu (lc hY.aj 23 cU.gm 68 cU.fC 52 cU.gv 48 cU.fq)))) (az gU.a0.ae 89 z5.fK 175 z5.eY 172 z5.eS (lj rA.a0 92 an ak.ia.aS 92 an af.ia.aS 78 an tS.gP 14 z8.fN aP (aW bt.bH (em tz.bi.bp.aj 357 ds.p7 ds.p6 257 ds.p5 253 ds.p4)) (hX i5.cR.aD 68 c7.gn 239 ds.gO 135 da.eB aw (nA j7.gZ 53 dM.p1 dM.p0 83 vq aV 79 cC))) (nd (tQ ri.cs 81 w7 cX cl 73 cq.gK 70 cG.fz) (ej lU.bi.eN 492 mJ rE rN 17 dP.fi 25 dP.eW (lf (wP ph.dK.eP.bg 56 c6.fM 144 c6.fx 58 c6.gn 114 c6.eA))) (bD li.gC.ho 125 y8 bj br 89 vo cg 85 b3 (e5 tn.S 65 dq.fq 174 hB aV.mX 170 cC.mX))))) (c3 e4 (nd (kH H) (gA CG.aj 55 an e4.aC fI.aC iD.aC 101 c4 aw (e2 H.fr.bi.k7.fy 319 ap au.gY (lf (oE fc.cz.dK.S.b2 4 dr.p2 182 b7 dZ.aC.ae 178 eM.aC.ae)) (fb cD fB b1)) (gz qY 96 bv aN 69 ch X 65 ad (ly kn))) (N H.CR.ib.bo 73 cG.gn (k3 sV.aS.cs 87 hD aY 87 hD aQ 119 dj.eB e_ 116 di.fA bd (i7 l8.cd.ag.bw 92 iK jw.cJ jD.cJ 17 dT.p2 153 et o5.bP)) (fh vV.ag.ag.bi.b8.cJ.aX bd 66 vj af 29 c8.gk e_ 148 iz qz.fr.iH (bk jD.gY)))) (d3 hO (eJ ar.hK.gY (J qq.hM.gT 82 dy.fE (al vZ.a0.hK)) (gy af.pE.eC (ms jX))) (gA pc.aO.ho 57 Cc aA aB dD 104 uG bq (du ph.eV.bg 60 w2 au X ad 182 lm aN (lf (sN n5.aj.gR.bg 36 c6.fx 357 ap H.cH.mv.bI 38 dl.p3 311 mq.xE.fF))) (iw oK.cf 78 ca kr.bl 93 bN jy.bI 89 ru.bI (aK ar.CR.xK.S)))))) (eL mW.aF (nd (rP yM.it wU Dp 28 (t9 cD DI bq) 105 (aM cF f7 bt) b1) (cb eI.dJ.bw 47 z4.ft z4.f4 z4.fE 19 z4.fD (c3 bj.xK.aF (nd (pW nh.aX.aC 11 ct.f8 301 lm aH 410 c9.f6 121 ct.fz) (cp sU.iI.ag 74 c0.p0 dI.e7 1 dI.f6) (al m3)) (J bd.nj.bl.eC.db 80 da.p3 (bC kL.S.S.cz.ae 190 ap H.gP.aI.av j.sy.aI.av 104 ey h5.cY 100 d4.cY))) (N fI.bu.cw 95 cG.fD (aW K.eC.bH (aK ke.io)) (bA ns.cz.ag 66 cI.fM 1 cI.fx 2 cI.gn (al pT)))) (cb hR.q6.b6.bg 136 z5.p4 z5.p3 z5.p2 89 z5.p1 (nd (xB sL.aj 66 an jl.i2 ju.i2 106 fX.b0 102 d8.b0) (J tT.db 72 cV.ga (iR qQ.ag 175 b7 b1.aC.ae 1 dr.p2 2 dr.p1)) (du tG.aF.aD 68 yt aA aB dD 101 fe aw.bV (aK hQ))) (nd (oC v8.b2.aj 214 cP.eA cP.f9 501 je H.ae.cH 497 j.wk.cH) (bT iY.Eg.aI.hV 148 hC aE.ia (iO uK.eK.hU.gE.cw 232 ap uK.fj.fF)) (de b1.aF.o6.bp (lf (rM tc.b2.b2.q6.aX 79 jc d8 29 dY.gK 99 oJ)))))) (m6 pR (cb nM.g6 96 z5.gK z5.fp z5.ft 1 z5.f4 (eR qV.bQ e_ 66 an oX.aC 17 z9.fU e_ 112 r6 aH (N b1.kB.eC.db 161 cB.p9 (aT ph.dK.ag.dm 11 ds.fE 1 ds.fD 2 ds.fu) (q0 gr.b6 aB 151 sa au)) (bA xu.bu.b8 57 c7.gK 1 c7.fp 2 c7.ft (ly jk))) (gp uv.aX 94 xC K L 52 cG.fq 48 wK (ck kJ.h8 (hT rr.cz.S 102 ch my.aC 115 bv j5.aO 111 lG.aO)) (J jv.iv.bm.dx 164 c8.gb (lf (oT rg.cz.b8.bw 61 dq.fi dq.eW 17 dq.eH 183 mH gN.hM))))) (nw qt.bV.pl.ae 104 wA br 65 nX q7 61 nL (eJ iX.gY (gW tL.ag.bw 76 r7 jw jD 17 dy.gm 257 ky bO (dc oD.fr.vz)) (aZ (oE ta.bi.S 129 pA 70 pq ah 66 aU) (ms jV))) (N mq.cJ.hU.bo 157 ct.fL (aW dN.mX.nT (hZ o0.fj.aF.cx.aD 339 ap bj.Ej.mv.bI 339 ap br.Ej.mv.bI 319 ap K.kY.xE.fF 82 dl.p4 j)) (aZ (pW tR.cd.aj 23 dT.fD 250 ch bO.bV 141 dT.fu 138 dT.gO) (la eT.ag 40 d9.fP d9.gK d9.fp 1 d9.ft)))))))
def DC : ab dp:=(bc d0 (bc e3 (az mj.eb.aX 62 z1.fT 41 z1.fA 138 z1.eu (aR dk (gA eT.cx.bg 72 kA H.kY mT rC 52 mc i6 (fR i5.eN 119 cy.fz 454 cV.p5 19 cy.gl (ml cl.bm.cH) (ji cj)) (j4 L.xY.bu (lf (jo o0.fj.aF.it 245 dL.eu 138 dL.fo 86 AF 82 xd j)))) (nd (tZ s7.cz.aX 78 fG ie.bw 29 c5.gl 98 gx.aD) (fh vP.kl.cR.cJ.aX bd 62 vm af 29 dy.p9 e_ 583 ts hj (iR qy.gR.b8 143 lA kW 1 ds.gL 2 ds.p9)) (ej bd.kl.cR.bg.cR.eN 122 iz oS.kv.iH oz.kv.iH 17 cS.fM 25 cS.fx (fW gu)))) (cb nu.cf 102 z5.fu z5.gO z5.ev 101 z5.eZ (nd (pO fc.eN.cR.b8.aD 61 an jn.bi.gP o7.bi.gP j.nj.bi.gP 105 lP.b0) (ej rq.dK.cx.bi.aX 58 ct.ev ar ao 171 cV.e7 167 cV.f6 (bk kS.eh)) (bA li.dK.b8.dm 11 cS.fE 1 cS.fD 2 cS.fu (bM kQ.a0.ag 52 rQ X hW ld 1 dM.hH))) (nd (uZ sX.a0.b2 4 cG.p0 98 sM H 94 cM.eY) (J kJ.sy.cJ.aO.aO 405 cA.p1 (bZ kt.eb.cx.aF.dB 75 v6 au X ad 156 l0 aN)) (de bF.bH.bp (aG ur.iG))))) (ei nB.a0.aj 85 z2.fD z2.fu 121 z2.gO 118 z2.ev (bU aB.bQ (N lM.pG.eV.bz 71 z8.fL (az rl.pl.ae.cQ 64 cy.gd 161 cP.fN 157 cP.ex (d2 X.jd.pm.bm) (lf (m0 s9.eb.ae 96 z0 211 z1 219 z2))) (gy dZ.iG.eC (aT yV.dm 11 cO.gl 1 cO.e1 2 cO.gk))) (ef eI.cx.aD 67 Ay bj br 55 w4 K 51 L (aZ (lB tl.b6 90 fe ok 1 c9.p0 2 dj.e7) (mb uY.aC.S.b2 4 c6.f4 158 l0 bK 154 ea)) (jz vR.vz (em k4.aD 49 cT.f8 cT.fz 75 cT.gl 50 cT.e1)))) (bS aV (nd (oT h7.cx.aD 66 dn.f8 dn.fz 163 dn.eS 50 dn.fD j) (kN lU.S 80 hC dO cj dS 129 cB.ft (aK b1.mX.gP.ib.fr)) (ek sO.S 173 b7 b4.ae 68 c0.eZ 64 pz (bk hQ))) (qe mP.aX.aC 11 cq.hH 62 cy.gK 84 cq.fp aw (J l6.mX.aF.sl.aI 199 cA.ft (al ue.mu.bH)) (ck lG.fQ (bZ tK.aD 167 hB jn.ya o7.ya j.nj.ya 70 dY.fp aw)))))) (hS fa.jq.eb.ae 128 G0 73 Hb 69 Go (aR pd (N cl.aF.sl.aI 141 z3.gv (fR i3.e0.ia 11 z7.p8 87 z7.p7 70 z7.p6 (N aB.eC.db 147 cy.f9 (ml aN.aI.cH) (dc j)) (ej uW.eV.S 119 fe eQ dz 68 Az 64 da.fC (mb iu.bH.bi.cf 83 w6 189 ap g2.iH.wi 185 kg.iH.wi))) (o2 qX.aj.b2.ae 152 pB uB 89 fG ar.Do.aD 85 ao.Do.aD (J rD.aX.pG.bo 211 dP.gl (ac K.o6.av.k7.fy 202 dT.gL)) (nt u6.bP.ia 4 cI.eH 105 cI.f8 101 c8.ev (em lH.dJ.bw 51 cU.p5 cU.p4 17 cU.p3 190 cU.p2)))) (bS jt.bu (ef j3.iI.aj 90 an tk.i9 uq.i9 122 c4 hQ 118 g7 (e9 mP.ag.iI.aj 119 ct.gb ct.gd 165 cV.ez 162 cV.fK (aG iY.jQ.iG)) (bT X.iH.aI.hV 124 hC cj (bC gF.gZ 57 mF hQ g7 87 dX cj 83 dS))) (gp tH.bg.aj 58 wh ak af 345 cy.fA 122 cq.eH (J b4.bm.bV.fd 159 dP.eS (cp rt.aF.b2.ag 202 dl.fm dl.gH 1 dl.gm)) (e9 tV.e0.bi.eN 240 c7.eB c7.fT 17 cN.eZ 25 cN.fo (bk b1.eh))))) (N bd.ib.cw 41 z2.fC (aJ nx.ag.dm 11 z4.gn 1 z4.eA 2 z4.f9 (cu qX.cs 85 an H.wk.mv ah.wk.mv aU.wk.mv 75 z8.p5 (ef rq.dK.cQ.cs 70 mG ar ao 175 y3 K 171 L (co H.ae.bl.ec) (dd rF.S aB 71 rX)) (ek m1.bP 68 ca CO.bH 1 cA.fM 2 cA.fx (bC wG.S 46 ep ak af 105 iq K 101 L))) (dR b4.S (bD jp.dJ.cs 250 ky bF bE 85 r7 jt 81 gX (bM na.b6 76 ch dZ.aC e_.eK.aC e_.mu.aC 1 dT.gn)) (aZ (lZ kQ.jq.eP.cs 120 y8 c8.fK 80 vo aw) (aK uB.bp)))) (ef jm.iI.aj 98 yw K L 51 kA ak 47 af (eJ aQ.gY (J H.gP.aI.db 116 dy.gk (aK e_.A3.eC.gD)) (iw qo.S 86 bN l6.bI 75 ca gu 71 uf (ij i3.fg 61 mF g7 91 dX lk 87 kS))) (nd (zT t7.a0.aC 11 cP.fx 88 nZ 54 sk) (m5 nC.bu (e8 n6.e0.cJ.fj.S 102 zf au X ad 207 dl.fm)) (jz cl.cQ.mv (la AE 36 dY.gd dY.fM dY.fx 1 dY.gn)))))))
def Dt : ab dp:=(d3 ld (N nH.eV.bz 142 GY (aR gq.bP (bS bt.eP (lQ kj.q6.S 189 z7.gn 94 z7.e1 H 90 z7.gg (oU u8.aF.cf 66 rc 108 nW ah 104 aU (lf (qU e_.dm.dm.aX.aF.aX.cz.ae 71 wc K L 124 wF 120)) (lf (eX jA.eN 37 c5.gb b1 99 c5.fM e_ 37 c5.gb j 19 d9.ez e_))) (fh g9.eN.S e_ 49 vh bd 136 wm K 132 wm L (iL o3.aI.S.b2.aj 188 ap aY.bu.d6 aQ.bu.d6 138 dL.fm 134 dL.gH))) (bS oB.aF (k3 pf.cx.aD 521 cS.f4 e_ 637 iz op.kv.iH 348 ct.er aE 124 cq.eA j (fJ ao.A3.eC)) (ix L.hU.pm.bm (lc jA.ec.aD 113 cT.fu 160 cT.gO 63 cU.fm 26 cU.gH)))) (N gq.bP.dh 59 z5.er (nd (rM pg.b8.fg 160 an b3.iV 75 z9.gH 164 bd.b6.b0) (aZ (eX s9.q6.bi.S 65 mG b1 197 je g2.cH 65 mG j 166 y3 e_) (d2 lk.bl.pm.bm)) (ej l8.aI.b8.bw 500 mJ aY.cR aQ.cR 17 c7.eZ 411 dl.gj (aT d5.ik 11 dM.fM 1 dM.fx 2 dM.gn))) (N ao.bg.fd 76 cq.fP (od oL.dJ.aD 35 dP.eZ 142 hJ h9.bm 121 ct.fx ak 117 af (ij lU.ik.aX 197 jK b3 153 mK aY 149 aQ)) (e9 yr.cz.S.bp.aF.bw 67 c8.p2 wc 17 cN.f6 116 wF (aG u1.iG))))) (oq gx (bU b4.bQ (nd (ow uH.aS 11 z8.eA 76 an iN.bi.gP 98 aN.b0) (nd (pW ko.eb.gR.bw 159 ct.fq 264 As j 17 ct.gm 126 ct.fC) (iR q8.b8 72 vd jH 1 c0.f9 2 c0.ga) (fb cD hI b1)) (aZ (qP iy.ec.eV.ae.b2 4 di.eB 119 lJ ah 115 aU) (ff yV.bw 39 dM.fu 219 cL.f9 19 dM.gO))) (dR ak.bg (ck ar.aF.aC (e8 qy.dB 173 jK au X ad 147 dT.e1)) (de bO.bH.bp (bk gN.hK)))) (d3 X (pQ ar.Do (aZ (yL qd.ja 4 cB.gl 39 cB.fz 36 vp) (ac oN.bP.dt 334 dT.p8)) (J cl.xY.bi.cJ.aO.aO 585 dT.p1 (cp mU.jr.fH 63 cU.fu cU.gO 1 cU.ev))) (cu uX.eK.bw 93 lF aA aB dD 19 cP.fU (kh vV.ag.ag.bi.b8.bg 99 CA di.gl 58 ve (bM lK.bl.cd.aF 177 ap fI.d6 rb.d6 tg.d6 1 dl.p2)) (md j8.fH.bw 135 cN.er 216 ch dV.aC 19 cN.eB (fW af.cx.bu)))))) (cb qg.ag 51 z1.fo z1.fU z1.fi 1 z1.eW (N X.bu.dh 55 z1.p8 (cb eI.dJ.dm 160 z3.p4 z3.p3 z3.p2 1 z3.p1 (eR nG.bQ bd 101 z8.eW e_ 17 z8.eH e_ 67 an oZ.aC (az kt.ec.S.ae.bQ 51 ct.ev 17 ct.eZ 251 cV.fp (hZ oQ.bl.cf 135 dT.f8 e_ 136 cN.ex aP 99 hD j5 95 hD lG) (fb cD Dr bd)) (J jn.pU.aI.hV 78 da.gL (bC pI.cd.cQ 103 ey q7.cv nL.cv 193 ap s6.av 189 tU.av))) (eR dF.aj.bQ e_ 46 w4 bd 17 cG.f4 e_ 74 Ay j (bA mP.ag.dm.dm 11 c9.ga 1 c9.gj 2 c9.f5 (lg qy.gR.aD 35 dT.gv 229 jK dV 147 lA lS)) (J tN.aO.bP.eV.dK.fy 134 cI.fC (ac h5.bi.hL.dx 156 cT.gH)))) (qv af (nd (oi um.kl 119 c4 aN.aO 117 an au.cQ.ce 14 z9.p3) (J fY.hL.aX.pG.bo 666 c0.e1 (ac jn.zh.jd.eD.kk 221 dr.fK)) (ek g9.aS.ag 87 iK jN.cJ 1 da.p8 2 da.p7 (pa H.fr))) (e2 qc.pU.hK.dh 305 ky aw (aW ah.iv (bZ rr.cs 111 bv t0.aO rs.aO ad.bi.aO 88 ch kc.aC)) (e9 u6.aF.bw 174 c7.p0 c0.e7 17 c0.f6 77 c0.fP (aK aB.bQ.bp))))) (aR pr (bc iQ (nd (uZ qx.b2 4 u7 104 c4 ah 100 wN) (dQ oQ.bl.aj 23 cB.fx 125 cB.gn 119 cB.eA 94 cB.f9 (ac bt.r5.eK.dt 334 dT.eY) (q0 gs.b6 aB 260 iJ au)) (ek tz.cJ.b8.b6 153 l0 pr 1 dT.f4 2 dT.fE (lf (lz aV)))) (nd (qU cZ.aj.cx.ae 50 wK K L 100 xC 96) (e9 sS.eb.eb.ae.aF.bw 63 dj.eA wV 17 dj.gj 112 wC (aG bd.aS.eK.ce)) (ix m4.Cv.bm (aG ak.hK.iG)))) (ef kV.aj.b2.aj 50 nX bF bE 109 wA ak 105 af (gI lD.S.cQ.b2.ae 75 dn.gv 62 xa K 58 L (aZ (qU wQ.aj 57 xj K L 92 bv 88) (e5 kK.gR.fg 144 ds.p8 174 c0.fK ar 170 ao)) (aZ (rP l4 iC Ax 32 (aM cD fB e_) 145 (aM cF fB e_) aP) (aK gu))) (nd (rP fk iC sw 20 (aM cD kD e_) 25 (aM cF kD e_) b1) (jW tD.iF 11 di.p5 94 bN H.bI.fF 101 ca v1.bI (al bK.bm.bH.bH)) (de L.aF.o6.bp (em eT.a0 40 d9.eH d9.f8 135 dY.p6 14 dY.p5)))))))
def DR : ab dp:=(eL e6 (cb kj.S 64 H5 H9 Ij 225 Hg (aR dZ.bP (aR kc (cu kj.eV.eN 87 kw g5.fF gq.fF k6.fF 19 z7.fK (nw uv.dJ.aX 100 lF af 106 xA ar 102 ao (iO bq.pE.CQ.dt 362 mJ aw.cR) (lf (qG aV))) (dG ub.hL.cH (iO g2.eK.hU.gE.cw 232 ap g2.fj.fF))) (cu oW.dK.aF 51 AA ah bK ea 1 c5.ez (fV gr.dK.gR.ae 28 dy.p1 70 dy.p0 66 c9.e7 (bM ud.fH 97 bN dk.g8 nE.g8 tW.g8 1 ds.gd)) (k3 hR.S.eP.cR.aD 75 ep bF.ya.n2 75 ep bE.ya.n2 184 iq b1.kY.bg.jd 50 cS.p4 e_ (aT s9.eb.ae 96 cU.er 211 cU.fA 219 cU.eu)))) (az iy.bQ.ae 207 z5.fi 109 z5.eW 223 z5.eH (ef l9.aD 105 r6 aY aQ 75 an dN.h8 71 ie.h8 (gV rx.fj.fj.cx.bi.a0 60 cV.fE 491 di.p8 137 cV.fD (bZ m1.aD 68 ca oB.aF ul.aF L.Ev.aF 91 bN bt.g8)) (od mU.hL.fj.cQ.aC 11 cS.eH 155 cS.ez aH 79 xz dZ 75 eM (ac K.eC.bu.cw 147 dM.p6))) (nd (jB pf.cQ.aC 11 cM.gj 233 cP.fm aH 367 ky H 57 cM.f5) (J gx.hU.bP.eV.dK.fy 259 dP.fE (lf (ry kL.bV.b2.ag 124 vl 1 c6.f5 2 dl.f9))) (hX d5.cx.aF.aD 66 c8.p4 372 c6.gH 208 c8.eZ aw (ff hY.g6 162 dq.f9 319 dY.fP 1 dq.ga))))) (N b1.ib.cw 41 z2.fi (bU hW.bQ (oU um.b2 4 z7.p6 69 an nE.aC 65 tW.aC (dQ ma.aS 11 ct.gn 141 cV.eS 270 cV.fm 106 ct.eA (lg re.b2 11 dI.p5 81 c0.eZ aE 172 b7 bd.ia.ae) (kf rv.iF.aj fY 124 d1.fi e_ 69 d1.eW e_ 65 d1.eH e_)) (eG fc.cz.dK.eN 162 b7 e4.cQ fI.cQ iD.cQ 19 cA.ez (aT mU.cd.ag 51 cO.gd 1 cO.fM 2 cO.fx))) (eg gG.aX.ag 52 pp jH 1 cG.fL 2 cG.gg (gV zR.b6 56 dj.gO 235 cA.ev 1 dj.ev (lf (lB tR.cf 102 hD bt.aO 150 cN.fN 138 dT.gm))) (J jU.aO.bi.hL.dx 156 c8.f4 (dc jl)))) (ei eT.bl 36 z6.eW z6.eH 1 z6.f8 2 z6.fz (az i4.cd.aO.aX 51 AK 29 dn.fL 71 dn.gg (gW tl.bw 65 zz ak af 17 dy.e7 98 fe bO (aT AN.eb.aI.b8.b8 133 dr.fM 1 dr.fx 2 dr.gn)) (fO BC.cK.S 58 cA.eW 144 cA.fo H 313 dr.gg (bM sJ.ag 59 mF gu jV m3.bl 1 cU.ft))) (eR ri.ag.a0 e_ 73 xc e_ 136 lo aE 14 cP.f6 e_ (hX j8.aX.aC 11 di.fP 68 cA.eW 136 dj.eZ aw (al ak.aX.a0.hK)) (de op.io (aK h9.CR.xK.S)))))) (nd (rP eE iC CV 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (aR dk.bl (bU uN (az iT.bl.b6 54 z8.f6 1 z8.fP 2 z8.gK (N bd.FX.eC.db 487 dy.gH (ac ty.GO.bi.k7.fy 80 c0.p5) (dc H)) (aW e_.bV.hK (bC ot.bV.aj 89 ey aY.cY aQ.cY 195 ap mY.av 191 iQ.av))) (az n6.bV 22 c5.gj 38 c5.f5 26 c5.hH (nt qd.aS 4 c9.gg 271 dP.ez 107 dP.eu (aK H.kB.eC.gD)) (aZ (pW uF.e0.aF.iF 11 cI.fT 69 vj kP 460 cN.e7 17 cI.fA) (mb n3.ia.b2.ae 128 cU.p8 58 yy K 54 L)))) (bS e6.bu (eR uH.cf e_ 110 an pd.b0 78 an jy.i2 74 an ru.i2 (aZ (pk ii.ho 141 c9.fA 627 mJ qz 277 c9.eu 113 ct.eA j) (lf (jB uD.ag.b6.aD 147 c6.eB 254 bv tP.aO 135 hD b1.kY.cJ 26 c6.fT))) (fO sX.S.b2.a0 114 da.f9 93 yW aE 14 c7.eS (cp d5.g0 58 cL.gb cL.gd 19 cL.fM))) (hi uv.S 56 lF rc 98 nW (fO uW.a0.S 98 wJ 72 c9.fx H 157 da.fM (g4 qh.aX.dJ.ae 28 dl.fA 84 dl.eu 80 dl.ez)) (J ue.iv.bm.dx 164 cN.hH (bk iQ.gY))))) (lC cD FK bd (ei kj.it 94 z4.gL z4.p9 99 z4.p8 95 z4.p7 (nd (pO uo.S 61 an q9.gP iS.gP t5.gP 97 qq.aS) (az uD.ag 91 cB.fL 1 cB.gg 2 cB.eY (ml gq.aI.cH) (pa dO.S)) (aW aQ.bm.bw (iL n3.fj.S 50 rQ ak af 145 zx 141 dM.ft))) (dQ t8.fj.ae 137 cM.p2 138 cM.p1 113 cM.p0 273 cq.f9 (fO rl.a0.cR.bg.S 60 dy.f9 181 dy.fx H 277 di.f5 (lg qY.b2 11 c6.eH 126 bv tS.aO 81 ch gS.aC)) (hX ns.cz.aj 23 c8.fm 96 cN.ev 70 cI.fM aw (lf (jo d5.it 317 dq.f5 160 dq.ev 62 zp 58 cT.eS j))))) (lY iP.cz.aD 46 z6.p6 196 kw gf.fF 77 z6.p5 (gp il.cz.bg.aj 62 dn.eH ak af 61 dn.p6 57 dn.p5 (gz yA.aj 91 bv aU 68 ch ak 64 af (lf (wI AN.eb.aI.b8.aD 79 dT.fP 409 dT.eB 137 dr.fM aw))) (gz l3.cK 75 ca uS.bH 86 bN bj.xK.jd 82 ut.jd (lf (eX jm.aD.aF 43 tO e_ 43 cL.f5 H 43 tO aP 1 cU.fo e_)))) (dQ ou.bQ.aj 35 cP.p5 36 cP.p4 181 ct.e1 178 ct.gk (m5 lP.bu (aG au.aC.S.gB)) (kh te.bg.ag.bw 68 dI.gH dI.gm 19 dI.fC (lf (rP eE wU By 24 (aM cD dE e_) 65 (aM cF dE e_) aP))))))))
def DE : ab dp:=(d3 b4 (bc ci (eR gF.gZ b1 57 z1.gm e_ 239 iJ X 235 iJ ad (bS d0.eP (gp nM.fj.S 96 sf eQ dz 119 z4.gd 115 z4.fM (N H.n2.hM.gT 82 cy.fM (lf (wI uY.aF.bi.aD 120 dI.p9 342 dr.fN 81 c7.ez aw)) (fW bK)) (bD nb.cs 71 hJ aY aQ 118 sh ak 114 af (bM ot.eP.aF 187 ap aB.eC.av b1.EZ.eC.av bd.pE.eC.av 1 dL.eA))) (eg uF.ae.ae 111 iz ao.sy 374 c5.gv 370 c5.fq (J jy.bV.fd 159 c9.eB (al ao.fr.aX)) (ej uc.aI.aX 68 cS.eY ar ao 127 cI.fp 123 cI.ft (g4 rf 51 vk 75 sc 131 cT.gg)))) (ei i3.a0.aj 93 z5.fm z5.gH 138 z5.gm 134 z5.fC (gA j3.aD 60 an ue.aC X.gB ad.gB 110 c4 lS (hX ou.e0.aD 118 cV.e1 263 dj.p0 55 ct.fK aw (ac oD.fr.jd.eD.kk 221 dr.p5)) (kN l8.fy.bg 129 wm aE K L 46 vh (eo m8.bV.a0 55 cL.fp 110 rX iN 14 cL.ft))) (aJ mP.aX.bP 80 cq.fp 1 cq.ft 2 cq.f4 (kN ko.eb.dB 104 zM au X ad 85 c9.fK (al lS.kv.aX)) (en K.aD.bl.bH (mb BT.bg.ae 58 cT.p8 78 zU K 74 L))))) (c3 cj (az h3.pl.S 112 z4.fm 93 z4.fL 89 z4.gH (eg rA.ag 92 an b1.b0 1 z8.hH 2 z8.gL (gA ro.dK.S 105 Am au X ad 103 lF b4 (mg qy.gR.aD 35 dI.fM 219 jK hj 147 lA cg 143 b3) (dd lD.S aB 31 rR)) (gz iy.bV.b2.bp 65 u2 aN 191 lm dk 187 e6 (eo iA.kl 48 mH 125 hB aE 14 cO.p0))) (dQ ko.bl.aj 23 cG.p7 79 cG.p6 73 cG.p5 48 cG.p4 (jW oO.cQ.aC 11 dj.eu 75 u2 gf 183 lm gS (lf (q2 rr.cz.aj 23 dT.p7 131 bv uN.aO 115 H.bP.aO 111 uj.aO))) (j4 ub.aI.bu (iR rk.iF.ag 75 jc kW 1 cT.fM 2 cT.fx)))) (mi jm.fy.ja 11 z6.fm e_ 100 z6.gH e_ 11 z6.fm aP 43 z6.ez bd (nd (nJ gF.gR.aS 11 dn.fM 134 dn.fx 71 fG kO 67 tE) (hX eI.bu.gR.aD 35 dy.fD 115 dj.fp 250 cB.ez aw (dc o7.zh.vz)) (e9 yF.gR.ae.cQ 239 dr.f4 dr.fE 53 c7.fq 50 c7.gb (ly kp))) (az jp.dJ.S 69 r7 242 ky 238 yv (fO o3.bH.a0 131 di.fm 106 rV au 14 di.gH (lf (tZ o0.eK.aD.S.ae 353 ap uS.bm.fF 169 dL.eB 337 h9.bg.hM.fF))) (iw ov.cf 82 ch qq 113 bv va 109 d0.aO (aK ie.CR.xK.S)))))) (c3 L.hU.bI (N u1.dh 215 Gc (cb gG.kl 52 z4.fu z4.gO z4.ev 165 z4.eZ (nd (qp gU.dv.ae 101 nY L 78 pw K 74) (N mh.hM.gT 82 ct.fT (aT tD.ik 11 dI.fP 1 dI.gK 2 dI.fp) (iM gx)) (aZ (qk oM.bl.dm.aX 83 dP.p5 159 xo ar 155 ao) (bC rL.cs 94 ey bF.cv bE.cv 196 ap hQ.av 192 g7.av))) (N bF.bu.cw 54 cG.gO (J kJ.aF.hU.gT 116 c9.p8 (fJ jn.ya.eC)) (ix rE.Cv.bm (ff gG.ag.aC 11 cT.fK 73 cT.fN 52 cT.ex)))) (nm aN.A7 (nd (xB g3.aX.dB.aj 76 an aY.bz.gP aQ.bz.gP 116 hQ.b0 112 g7.b0) (aZ (wH jp.S.b2 11 cV.hH 224 un aE 59 ct.p2) (co ul.aF.ec)) (J lM.bl.eC.db 87 c7.fE (ms hQ))) (fR m9.bV 59 cq.fx 308 ct.fi 202 cP.p7 (J b4.pU.aI.hV 79 dP.p7 (bC qa.cf 116 bv mY.aO iQ.aO 89 ch dk.aC 85 e6.aC)) (bT nH.AW.kv.hM.bu.bu 61 iz rN.fr.iH (n4 j.G7.aS))))) (bc cC (aJ m2.dv 98 z4.p9 103 z5.fE 99 z5.fD (cu l9.ag 109 c4 j5 ah.aO aU.aO 1 z9.eH (lj nh.cR.aD 127 cB.p5 e_ 197 r7 gx 252 sb dV 121 cy.p0 j (kf i4.b6.aj.cQ.S.a0 e_ 134 c7.fu bt 106 zF aE 14 dr.f9 e_) (dd d5.b6 aA 9 cO.eW)) (J X.ia.hM.gT 82 cA.p0 (ac rK.bu.cw 178 dM.gL))) (nd (AB sI r1 24 65) (aZ (eX hY.bH.bg 48 cV.fo e_ 241 cV.fP H 50 dj.p7 e_ 64 yU e_) (aK L.A3.vC.cJ.fr)) (fO kV.a0.aj.cR.bV.S 70 c8.e7 155 cI.p2 H 373 cN.f5 (bk qR.gY)))) (k2 eT.bl.aX 48 rY af 41 z7.fD 38 z7.f4 (bS b1.cY (aZ (jB pX.bV.aC 11 dy.fq 58 cq.eS aH 100 mf H 41 dy.gb) (bZ qQ.aj 66 pz H ah aU 179 b7 bt.aC.ae)) (fV uY.aC.bQ 61 cS.eY 17 cS.eS 350 cI.ev (e8 gU.dB 93 rX nk g2 kg 60 cL.p3))) (N iS.k7.fy 72 cy.fE (eG ra.bw.bP.bw 82 mG au X ad 19 da.e7 (lf (oT k4.bQ.ag.b6.bw 129 dL.gl dL.e1 17 dL.gk 195 ap aH.bu.d6))) (fh oV.bQ e_ 102 bv L.aO 17 cN.gl e_ 79 ch h9.nj (ji e4)))))))
def DV : ab dp:=(c3 iD (az nx.aj 16 HX 143 Ig 140 HN (pL qg.aj 23 z1.eH 81 z1.f8 z1.fz 55 z1.gl (aR gS (lE m2.jq 11 z7.gO 137 z7.ev 86 z6.p0 aw (hi ri.ag.ag 73 rO cy.ev 1 cy.eZ (i7 Cm.cJ.ag.bw 110 ca aY.cR.bI aQ.cR.bI 17 dI.fi 101 bN lT.bl.fF) (aT kb.ec.aX 44 d9.gO 29 d9.ev 64 d9.eZ)) (kh oQ.nS.a0 57 da.fE da.fD 138 da.fu (aG rS.aC.S.gB))) (az rg.ec.aX 49 AA 29 c5.eW 69 c5.eH (J aQ.iG.hU.gT 190 dy.fM (ff g9.cx.aF 136 w1 471 dl.eW 1 ds.fq)) (ir s0.eP.aD 167 cI.eZ 265 cI.fo 63 cS.fm 38 cS.gH (e8 n6.dB 90 mH H.bm jy ru 64 cL.p0)))) (bc d0.eV (k2 g3.bV.bV.a0 158 an bq.iV 94 z9.gl 14 z9.e1 (fS eI.bu.gR.aS 4 cB.p4 77 r7 dZ 73 eM (e8 rf.it 113 yQ au X ad 79 c0.p0)) (aW q7.hM (co jk))) (dQ v7.aF.bw 281 cP.fD 117 cM.gH 17 cM.gm 65 cM.fC (aW H.nT.nT (ac b3.i0.gE.cw 92 c6.gO)) (de cg.gY.gD (aG ak.pU.vS))))) (nd (rP sI iC Bw 24 (aM cD nQ e_) 65 (aM cF nQ e_) b1) (ku aV (aJ l9 97 c4 1 u7 2 z8.fA (lQ j0.cK.S 52 cy.gK 92 cy.e7 H 261 c9.fD (em tu.bg.aj 70 dI.ft dI.f4 183 dI.fE 179 dI.fD) (dc cC)) (kh oQ.cx.bg 53 di.gK dj.eW 135 dj.fi (lf (sN pI.dm.bg 36 cO.gK 231 ap H.cH.ce.bi 38 cO.fp 193 mq.mu.av)))) (nd (rP sI iC tA 24 (aM cD nQ e_) 65 (aM cF nQ e_) bd) (bT bt.rG.aI.hV 199 et vb (ff jg.aS.fH 142 dT.e1 477 dl.p9 1 dT.gk)) (en np.bV.hK (ac iY.mu.eV.dK.fy 120 cT.eY)))) (lC cD hI e_ (dQ cZ.jq.cQ 101 dn.fp 102 dn.ft 29 dn.fP 26 dn.gK (hX n8.aS 11 cV.gL 108 wJ 64 ct.p0 aw (al bj.iH.bQ)) (aZ (ww zq.bl.ec) (cp ko.fH 55 cL.p6 cL.p5 1 cL.p4))) (nd (rP j2 wU Bs 24 (aM cD f7 e_) 65 (aM cF f7 e_) b1) (aZ (jo oe.jr.cz.S 159 da.p4 79 dP.p5 155 y6 151 xo j) (lf (lB k4.bQ.dv 175 ap sW 103 y0 99 dl.e1))) (bD oG.b6.cd.bi.cd.bg.aj 109 cI.ez ak af 138 iz m4.fr.iH 134 rD.fr.iH (aK o4.bp)))))) (nd (yN g3.ia 11 G5 262 iJ au He 48 GU) (e2 q5.bu.bu.dh 151 iJ iN (bS qJ.bm (bc jk (N my.eC.db 63 cy.gn (ac dz.aI.bV.fd 159 c0.gb) (lf (yC lH.S 138 d9.fm d9.gH d9.gm 47 rQ))) (J jn.bm.bV.fd 159 da.eY (lf (l5 ot.nS.bQ 19 dL.f9 17 dL.ga 191 ap aH.mu.av)))) (gp dF.ec.cz.ae 54 wu K L 186 c5.eB 182 c5.fT (dG dN.hL.cH (i7 uA.dJ.g0 179 b7 aY.cK aQ.cK 17 ds.hH 78 pu aH)) (hX os.bm.aS 11 cI.fD 80 c8.e7 147 cS.ex aw (hZ d5.cx.aD 74 cU.hH e_ 74 cU.gL e_ 191 cT.er aE 58 cU.eS j)))) (c3 bE.aF (nd (ow nF.b6.aj 23 z9.fM 141 c4 gf.aO 115 bq.bu) (J b1.bi.bV.fd 159 ct.fm (aG mY.fQ)) (ng m9.jq.aC 11 c0.eY 144 c0.p9 46 c0.eS (eo rt.a0 59 cL.fD 107 mH q5 14 cL.fu))) (N hO.aF.vG.bi.aO 59 cq.eZ (md oL.aj 23 dP.fA 143 fe gf 109 dP.eu (iL o3.b6.a0.aj 230 ap aY.qW aQ.qW 82 c6.gb 78 c6.gd)) (hX uh.ag.aj 23 cN.fE 95 cN.eA 69 c8.ex aw (lf (rP eE sd BN 24 (aM cD dE e_) 65 (aM cF dE e_) aP)))))) (cb rv.S 98 z2.eY z2.eS z2.fm 43 z2.gH (qS bK (bc gu (N cj.i0.bo 75 cy.fo (g1 qf.aj 23 c0.gj 164 mK 138 lA aw) (dd cZ.a0 aA 21 cO.f4)) (bD qo.aX 71 ca aE.rG.bH uS.bH 82 bN bF.jd 78 bE.jd (h6 gG.gC 100 mH bt 56 cO.fL H 52 dM.e7))) (lE gG.aX.aj 47 cG.p2 55 cG.p1 56 pp hO (ek qo.eK 82 bN e_.dK.bI 1 dj.fL 2 dj.gg (ij Cw.cx.ae 100 bv qM 81 ch bj.n2 77 br.n2)) (j4 tT.bu (g4 il.eK.bH.ae 40 cT.p0 131 dq.fL 128 dq.gg)))) (gI kb.eb.b2 4 z6.fC 96 nX X 92 ad (eJ oJ.gY (fV sY.S 82 hD 106 dy.fo 94 dy.fU (mb uA.dJ.bH.ae 66 dT.fp 187 b7 ar.ym.ae 183 ao.ym.ae)) (aZ (oC rm.bV.aF.aD 59 ds.fT ds.fA 125 lJ cg 121 b3) (bk kp))) (hi uw.aF 48 mL mf 1 cP.gv (jW qo.ia 11 di.fq 103 ca H.cY 86 bN aw.dK.bI (ij na.fg 119 bv iX.aO 88 ch tk.ni 84 uq.ni)) (jz hj.cQ.mv (aT i3 11 dY.eY 1 dY.eS 2 dY.fm)))))))
def DB : ab dp:=(cb eT.bl 36 GN Gw Gz 1 GJ (cb m8.cQ.ae 225 Ht Hn Hq 213 G3 (aJ uE.dm 11 z1.fN 1 z1.ex 2 z1.fL (lQ s5.b2.a0 130 z3.gk 75 dX iN 14 z3.er (qS b1.bu (fR uV.ag 71 xr 146 cy.fU 1 cy.eY (em u6.bP.cs 186 dI.gk dI.er 121 dI.eB 117 dI.fT) (ji cg)) (bA i5.cR.b8 131 da.eB 1 da.fT 2 da.fA (e5 n5.aj.ia.dv 142 dL.fo 90 xd ar 86 ao))) (bU aH.aO (bD pS.eV.b8.aD 65 sb aY aQ 174 wg ak 170 af (co j.A3.aF.ec)) (bD gr.eb.q6.bi.aD 150 cS.ez aY aQ 86 xz fX 82 d8 (ac px.fr.hK.dh 154 cT.f4)))) (eL o5 (gA qK.cz.S 90 an e_.ae.ce lM.ce ui.ce 114 c4 bt.aO (aW lT.nT (aK ao.cJ.kY.ib.fr)) (bT dk.kv.pU.hK.dh 305 ky dk (aT iP.ik 11 dM.eS 1 dM.fm 2 dM.gH))) (az jp.dJ.bQ 19 cM.p8 17 cM.p7 37 cM.p6 (fO ou.bQ.aF.a0 67 c9.fz 166 pA au 14 dP.fu (iR rr.g6 84 ch iE.aC 1 c6.gL 2 c6.p9)) (ix ar.Cv.bm (lc k8.aS.cs 115 dq.gd 116 dq.fM 70 dq.fx 66 dq.gn))))) (az fk.ec.aX 40 z2.gl 29 z2.e1 60 z2.gk (ku jl (lj j3.aD 60 an ob.aC 60 an oo.aC 110 c4 cg 106 z8.eW j (cu ti 122 et ah bK ea 1 cB.fp (g1 uQ.bQ.aC 11 dI.p3 78 dr.f8 144 c0.fi aw) (lf (q1 dz.bI))) (bT ah.AW.kv.hM.bu.bu 61 iz H.kv.iH (aK kn))) (qe ko.bl.iF 11 cG.fm 159 xA 91 cG.fi aw (fh wr.bQ e_ 58 wO bd 17 dj.eH e_ 93 zX j (lf (rM kK.S.q6.aX 91 iK ie.wq 29 dT.fA 111 gx.cJ))) (ng rt.aF.iF 11 c8.gO 186 c8.p6 103 c8.ev (al iX)))) (d3 gN (N k9.iH.ib.bz 57 dn.eY (bT qn.aI.hV 193 et gx (cp oW.dK.cR.aD 63 ds.p1 ds.p0 113 dT.e7)) (fS qQ.S 66 pu 179 b7 H.cK 175 j.bg.ae (fW jT))) (N dz.bH.hU.bo 161 cy.eu (bD uL.aD 86 zX bj br 67 wO K 63 L (al ak.pU.bH.bH)) (J bq.r5.iv.bm.dx 164 c7.fL (bC tv.dm.cs 144 hB jl.aI ju.aI 89 jc ke 85 iX)))))) (aR br.eK (aR jV (pL kZ.aj 23 z3.hH 74 z3.gL z3.p9 48 z3.p8 (hi nM.gR.bw 92 z8.fu z8.gO 19 z8.ev (nd (rP j2 wU zG 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (h6 jg.cd.gR.a0 89 iK bt.pl 178 et jv.bP 14 dT.eW) (al fI)) (eG uV.a0.ag 83 rO X hW ld 1 da.ga (iL rL.eK.aD 184 ap aY.mu.av aQ.mu.av 63 dL.p9 26 dL.p8))) (hi uu.ae 62 Ay c5.p3 46 w4 (fS kL.S 60 ey 162 ap ed 158 d0 (lf (qb eE vF 24 65))) (aZ (eX d5.cz.cf 74 cI.fL e_ 74 vo H 74 cI.fL aP 122 cI.gg e_) (aK aV.bp)))) (bS oo.bu (nd (pO iT.cx.cJ.S 81 an e3.i2 uU.gP d0.i2 99 b4.ia.aS) (J lP.i0.bo 68 ct.p8 (fJ aB.ib.iG.eC)) (du qi.it 129 lo nk g2 kg 88 rO b4 (ac j5.bu.cw 186 cL.ga))) (N jv.o6.eD.aI 50 cq.fK (bD ko.eb.fj.S 81 rO ak af 126 lo X 122 ad (bZ sY.g6.bg 106 hD H.kY.cJ mT.cJ rC.cJ 269 bv bt.jQ)) (en op.ae.eh (e8 jA.ec.cf 65 zp au X ad 167 dq.f9))))) (aJ h3.a0 133 z2.hH 81 z2.gj 14 z2.f5 (nd (kH gf) (nd (nJ nF.aD 59 z9.fE 158 z9.fD 65 an eQ.aC 61 dz.aC) (ei uJ.ae 51 w2 u2 177 vt 173 lm (bZ q8.aD 173 b7 iZ.nj.ae iY.nj.ae mW.nj.ae 76 vd hO) (dd uA aA 9 cO.ev)) (aZ (nJ li.eb.aX.aj 59 cA.gL 60 cA.p9 73 yU K 69 L) (iM kn))) (nd (lz L.xY) (kh hY.aS.aj 60 dj.fM dj.fx 112 dj.gn (bM qf.b6.bw 190 jK e4 fI iD 19 c6.gk)) (aZ (jo tz.cJ.b8.aD 47 c8.gm 281 cN.fU 245 cN.fi 76 cI.f5 j) (aG K.bu.iG)))) (mi tC.jq 11 z6.p4 e_ 142 z4.gb e_ 11 z6.p4 aP 87 z6.eA bd (dQ uQ.iF 11 dn.p0 52 c5.e7 790 c5.fC 17 c5.f6 (ek uL.b6 90 bv pr 1 dy.eu 2 dy.ez (hT gr.ec.aX.S.ae 90 ds.e1 L 74 wn k0 70 jZ)) (gz l3.gC 93 ca fY.cY 94 bN X.fj.bI 90 ad.fj.bI (pa K.fr))) (N aN.dt 334 ct.fA (aZ (lL Al.cz.S.ae.gR.bg 36 di.hH 107 dj.eA H 38 di.gL 69 vm qc) (lb ah.bg.pG.bg)) (aZ (lZ rm.bV.aF.aD 59 dI.f9 dI.ga 125 lJ lS) (co gx)))))))
def DO : ab dp:=(nd (rP j2 iC x6 24 (aM cD f7 e_) 65 (aM cF f7 e_) fY) (nd (kH e_) (aR lG.bP (cu mj.S 80 dX dO cj dS 54 z3.fi (bc bd.bu (nd (pJ nh.cx.bg 58 cy.fA aE K L 125 cB.fu) (ac e_.eV.aI.eC.bu.bz 393 dT.ft) (la jm.fy.S 138 d9.fo d9.fU d9.fi 47 d9.eW)) (md ou.bQ.aF.ag 67 da.eH 373 ky nE 1 da.f8 (ac oN.pE.eP.aI.db 103 dL.gg))) (gI i3.S.S 134 c5.e1 79 fG ah.aD 75 aU.aD (ir mZ.aC 11 dy.p8 135 dy.p7 64 dy.p6 60 dy.p5 (lf (xe ph.dK.ag.bw 86 c6.fp 363 ap q5.hL.bI 19 c6.ft))) (ng li.dK.b8.bw 75 cS.hH 199 cI.gg 19 cS.gL (iM gu)))) (nd (kH tq) (nd (tI sL 90 an b4.aS 58 ed.gP 54 d0.gP) (aZ (uZ pS.aj.ae.b2 4 cP.p7 174 ct.fD H 170 ct.eW) (d2 j.wi.pm.bm)) (fV rf.ec 59 cS.ev 1 cS.eZ 2 cS.fo (ac oc.bo 171 cL.eA))) (dR ok.S (aW my.nT (qm lK.bl.b6.aS 11 dl.fM 35 dl.fx 181 ap ub.hL.bI 177 e_.xE.hL.bI)) (gz jA.dK.e0.bg.ae 73 rZ ao 185 w3 K 181 L (hT tv.dm.S 73 jc aw 136 hB ed 132 d0))))) (dR uq (bU dO.eN (bc jX (az n8.b6 60 ct.p0 1 cB.e7 2 cB.f6 (fJ j.sy.aI) (lf (m0 h3.a0.aj 89 d1.gO 98 d1.ev 94 d1.eZ))) (fS kZ.eb.ja.ae 224 cA.gk 64 yH K 60 L (aT tv.dm 11 cO.fK 1 cO.fN 2 cO.ex))) (fR oy.dm 88 w7 216 cG.eA 1 cG.eu (ck e_.bi.ce (qm qY.jq 11 dT.fN 23 dT.ex 108 bv e_.eK.aO 104 e_.mu.aO)) (de L.gY.gD (em wM.aI.eN 53 cT.fT cT.fA 17 cT.eu 25 cT.ez)))) (N aw.bu.dh 45 z6.gO (ei j0.cz.ae 44 dn.gk dn.er 201 dn.ga 89 dn.eB (bT ah.iG.dt 237 iB X.bH.kB (ac kJ.vS.hK.bm.dx 164 dr.gm)) (aZ (qL k8.jq.cQ.S 146 c0.er 70 c0.eB 66 dr.ft) (cp rt.ag 59 cL.p0 cU.e7 1 cU.f6))) (N L.aO.hU.bo 308 cy.f4 (J oD.mX.aF.sl.aI 115 cA.fD (al rD.bH.bH)) (fO sU.iI.a0 74 cN.ev 130 yQ aE 14 c7.p5 (g4 lH.cz.cd.aX 115 yB 67 zP 252 dY.fL)))))) (d3 ki.cH (aR jX (bU K.mu (nd (lL kj.eV.S 92 z7.eu 193 z5.eu H 94 z7.p3 95 kw l6.bI) (dQ sY.eN 91 cy.hH 92 cy.gL 17 cy.p9 25 cy.p8 (lc tV.S.aC 11 dr.fD 199 dr.fm 236 dr.gH 67 dr.fu) (g4 d5.a0 46 d9.fx 195 d9.gn 14 d9.eA)) (dG bt.e0.cH (aG cX.aC.S.gB))) (eJ L.GK.cJ.fr (gV h7.iI.fH 80 c9.fK 755 dT.gd 1 c9.fN (lf (pe lU.bH.bg 48 ds.fP 138 ds.gm H 50 dT.ez 141 w1))) (hX u3.cx.aS 11 cI.gl 81 c8.fi 201 cS.fC aw (al d8)))) (bS oZ.bu (ef qK.gZ 114 c4 ke iX 72 an aV.i9 68 cC.i9 (bD n8.jr.aj 111 As bj br 112 hJ eQ 108 dz (bC oK.fg 89 bN ar.vS.cH ao.vS.cH 74 ca jl.bI 70 ju.bI)) (iw n8.fg 123 fe dz 72 da.fC K 68 L (nA jA.gZ 57 cL.fi cL.eW 130 sa X 126 ad))) (az oy.iI.ae 73 cq.fz 505 cB.eZ 502 cB.fo (ck kP.aF.aC (e5 u6.bP.dm.aX 204 c6.eS 103 c8.p3 ar 99 ao)) (de tN.gY.gD (bk qc.hK))))) (c3 cg (qS bq (om nG.ia 11 z8.p2 95 an ci.i9 105 c4 gS (im kO.nT (ml eQ.aI.cH) (dd tM aA 21 cO.fu)) (ek oK.cd.ag 89 bN jH.fj.bI 1 cA.ga 2 cA.gj (hT eT.gC 100 dX k9 56 mF sP 52 jk))) (N bj.ib.hU.bo 60 cM.f8 (k3 oe.jr.cx.aD 53 cq.eS aY 53 cq.eS aQ 115 mL e_.kB 50 dj.gH e_ (qm qf.aX.aj 59 dT.gj 60 dT.f5 150 w1 ak 146 af)) (j4 bE.bi.bu (bk kW.gY)))) (hi m2.ec 82 z6.eA z6.f9 1 z6.ga (eJ pT.gY (J aQ.gP.cJ.aO.aO 222 dj.gk (ac nk.vC.Eg.fy.bz 172 ds.ga)) (fS ud.b2 4 cN.p0 85 bN nK.bI 81 qJ.bI (e5 ua.ag.fg 61 cL.eW 134 sa bF 130 bE))) (nd (rP j2 wU rU 24 (aM cD f7 e_) 65 (aM cF f7 e_) e_) (aW aH.bm.bw (al ke.kv.aX)) (de gq.kY.ib.fr (cp tx 38 ep dX 1 dY.eA)))))))
def DU : ab dp:=(nd (rP yM.it wU x6 28 (t9 cD DI bq) 105 (aM cF f7 bt) b1) (az g3.eK.ae 52 Gl 37 Hr 34 GV (aR dz.bP (bS iY.bm (ei kj.cd.ae 68 z7.fC pw 99 z5.eu 95 nY (lj pX.eP.aX 35 cy.gv e_ 128 mf hj 41 cq.fm e_ 86 mf j (aK oz.io) (fb cD fB e_)) (dG ak.fj.cH (iL ot.nS.aD 183 ap cX.eC.av cl.eC.av 63 dL.fK 26 dL.fN))) (e2 L.A7.bi.cJ.aO.aO 330 iz af.kY.sy (e9 rn.aI.ae 58 c9.ev c9.eZ 41 c9.fo 94 c9.fU (fJ bj.ib.iG.eC)) (de rS.o6.bp (kf o9.S e_ 53 cU.fN e_ 56 cU.ez H 52 cU.ex e_)))) (ei gU.dv 93 z5.eu nY 149 z5.fL 145 z5.gg (nd (rP eE iC yg 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (aW b3.nT (bk d8.ae.eh)) (fO g9.bp 73 da.eu 136 da.eB H 433 dr.ga (cp cZ.g0 46 cL.er cL.eB 19 cL.fT))) (ef s8.aj 61 lF bj br 107 nW K 103 L (dG bK.bm.cH (bM uD.ag.cd.aF 264 bv tS.aO ah.jQ aU.jQ 1 c6.ga)) (en au.cv.bH (aT tb.bP 59 dq.gm 1 dq.fC 2 dq.gv))))) (cb h7.ag 38 z2.fN z2.ex z2.fL 1 z2.gg (aJ gU.dJ.ag 88 sf 1 z4.fN 2 z4.ex (m6 jH.S (e2 eM.iG.dt 237 iB gN.bH.kB (co ki.aF.ec) (ac rs.kk 84 d1.fA)) (bD qa.aD 96 bv bj.ib qM 77 ch ug 73 aP.n2 (g1 fa.eb.aj 23 dM.ev 77 cL.e7 51 cO.er aw))) (N j.ib.hU.bo 55 cG.fx (bD oY.aj 67 ch bF bE 102 bv jt 98 gX (bZ wZ.ag.wq.S 161 et aE.aF.bP K.aF.bP L.aF.bP 94 iK l6.wq)) (ej oG.b6.cd.bi.cd.bu.aD 64 vj jU ka 63 c8.gl 26 c8.e1 (bk jw.gY)))) (eR fc.gC e_ 97 nX k9 53 z4.er b1 49 z6.eS e_ (eJ vb.gY (bD ko.it.aj 104 lo cX cl 85 xr ak 81 af (e8 sU.cf 98 AP au X ad 78 dr.er)) (gW u0.jr.aj 172 b7 qI.cQ oH.cQ 107 c0.gm 103 pz j (e5 nB.fg 53 dM.p4 54 rR bF 50 bE))) (oU nB.bP.S.S 62 cM.fm 105 uG ah 101 aU (ek ov.b8 97 bv iE 1 di.ez 2 di.fK (ac d4.pE.eP.aI.db 97 dL.gK)) (du qY.aj 77 ch e4.aC fI.aC iD.aC 112 bv lP.aO (lb k9.pG.bg)))))) (eL iY.aF (az kb.jq.S 44 FU 85 Fz 29 F3 (az gG.kl 52 z4.gK 165 z3.p4 14 z4.fp (oU nG.S 105 wN 67 an dk.aC 63 e6.aC (nd (oC kt.ec.fj.bg.aj 247 cV.fi cV.eW 203 je nr.cH 199 mh.cH) (ac lM.pG.kY.eF 85 c0.p1) (al ox)) (ek tG.aF.b8 97 fe e_.bV 1 da.p6 2 da.p5 (bM pI.dm.bw 189 ap q4.bP.av ur.bP.av j.hK.bP.av 19 cO.fP))) (nd (AB sI Dp 24 65) (aW aE.eC.bH (dc aQ.bm.fr.vz)) (ng sU.jr 11 cI.gb 118 wl 62 cI.gd (lf (rp jD))))) (nm ea.A7 (nd (Aa iT.cx.bg.ag.bw 107 an s6.b0 tU.b0 17 z9.p1 83 aH.bz.gP) (hX qd.iF 11 cV.f9 121 c9.gm 104 hJ bq (co ka.aF.ec)) (aZ (oE oj.ag.bg.S 73 c9.p5 102 fe H.bV 98 j.bg) (lf (rP fk iC r1 20 (aM cD kD e_) 25 (aM cF kD e_) e_)))) (qw jx.aj.ia 4 cq.gm 56 cq.fC 52 sk (J iZ.Eg.aI.hV 77 dP.hH (g1 qh.eP.cR.aD 67 dl.ex 206 dL.fu 130 c6.p8 aw)) (ix i6.pm.bm (bC gG.b6.cd.bi.aD 145 hB cX.gP.wi cl.gP.wi 76 mH dN.fr.hM 72 ie.fr.hM))))) (nd (qb eE Bw 24 65) (bc oN (nw qV.S 70 an pd.aC 112 wN X 108 ad (lE pX.aX.aj 47 cB.hH 55 cB.gL 62 mL hO (bZ g9.cf 140 et e3.aO va d0.aO 77 hC qq) (dd gr.b6 aA 9 cO.fU)) (fS l3.dJ.aS 4 c7.fP 111 ca K.cR.bI 107 L.cR.bI (ms jk))) (az cZ.aj.cs 96 cM.eu 62 cM.ez 607 ct.ez (ck b1.F8.h8 (lf (ow ov.cd.aj 23 c6.fz 139 bv au.eN.aO 113 kc.aO))) (jz ka.GF (ac cl.gP.eF 651 dY.fU)))) (N aA.ib.bP.dh 58 z7.fP (eJ ke.gY (gy mT.aI (dc aH.bm.fr.vz)) (aW e_.GK.bI.aD (ms gu))) (qe sQ.aD 56 cy.ft 279 c9.fz 106 wy hO (aW i6.aD (lf (pO iu.aS.eK.bi.bg 177 ap ci.fr.hM.fF aV.fr.hM.fF cC.fr.hM.fF 225 bq.vG.fj.bI))) (bD mQ.cx.ae 80 bN bj.xK.jd ut.jd 77 ca aE.rG.bH 73 uS.bH (fb cF hI b1)))))))
def DJ : ab dp:=(pj gU.cR.bg 112 cU 214 cT (qs h3.ag 218 Ib 267 HC 220 H6 1 HE (aR fX.bl (pL i3.aD 35 z3.ev 164 z3.eZ z3.fo 53 z3.fU (lE kj.q6.aj 23 z7.eW 120 z7.eH 94 z7.gK aw (lQ g9.a0 124 cP.fE 97 hC au 14 cy.f8 (bM xu.bu.aD 79 bN ue.fF X.jd.fF ad.jd.fF 65 dI.gd) (lf (rP qu wU By 28 (aM cD hI e_) 105 (aM cF hI e_) aP))) (aZ (nJ s0.aX.aj 59 da.fU 60 da.fi 72 zm K 68 L) (bZ na.cf 92 ch dO.ce gu.aC uf.aC 123 bv tT.aO))) (gp gs.iI.nS.aD 76 fG rB.bw qn.bw 63 c5.f8 26 c5.fz (ej nD.ag.ag.bi.bu.aD 60 vm jU ka 63 dy.f5 26 dy.hH (lf (l5 kK.gR.aI.ae 136 dr.p0 41 ds.gb 172 w1 j))) (fV rn.aD.S 66 zm 200 cS.fz 53 cS.gl (bZ g3.dB 90 dX au.bQ o4 ad.bQ 64 mF kr.bl)))) (bc qJ.aI (nd (tI sL.S 66 an b4.bi.gP 106 ed.b0 102 d0.b0) (gW jp.g6.bw 67 pn jw jD 17 cB.p0 226 un bO (bk lk.eh)) (aW fY.bm.xM (dc j))) (N ok.aF.vG.bi.aO 62 cM.fM (aZ (pk B1.b6.cd.bi.aD 183 di.p3 317 iq tP.bI 491 cS.fN 58 c9.f4 j) (e5 uJ.iF.dv 93 c6.f6 266 c7.eA ar 262 ao)) (nt tn.dJ.aS 4 c8.hH 113 c8.gL 109 c7.e1 (lf (l5 sK.bP.aX 57 cT.gj 29 dq.fD 77 vk gx)))))) (N jZ.eF 138 z2.fE (bU aA.bQ (bc g7 (N ty.cJ.hU.bo 156 cV.fA (d2 ue.pm.bm) (ac gf.bH.bz 199 d1.f4)) (gy kP.GE.eC (aT i4.cd.ag 43 cO.eH 1 cO.f8 2 cO.fz))) (nd (qL v7.bP.S 93 wh 70 cG.fz 58 cG.gv) (bA ii.eP.b8 57 c9.p4 1 c9.p3 2 c9.p2 (n4 xP.ae.bV.aS)) (J ka.Gp.eD.kk 221 cI.p6 (ij ol.S.ae 53 kA jZ 108 yw cX 104 cl)))) (lC cF hI b1 (hi nB.aI.a0 49 dn.fi dn.eW 94 dn.eH (J u1.dt 334 c9.hH (fJ ci.mX.eC)) (bA dF.jq.b2.ae 164 vc 58 cN.eu 54 wS (cp m8.fH 55 cL.p3 cL.p2 1 cL.p1))) (nd (pP il.eN.cR.ja 4 cq.f5 85 cq.fp H 81 cq.fE) (J lP.r5.eF 166 cA.fp (al qn.bH.bH)) (en aQ.wk.bl.bH (h6 rt.bp 172 hB b4.ya 71 dY.fp H 67 dY.f8)))))) (d3 e_.A3.cH (aR o5.bl (ei BV 45 ap ca 171 z3.fC 60 bN (az pg.b8.jr 4 z7.hH 70 z7.gL 61 z7.p9 (e2 dS.xY.bu.dK.fy 131 je ad.cH (e5 oj.ag.dm.aX 116 c7.gg 77 wJ ar 73 ao) (fb cF mD aV)) (dG oz.e0.cH (aG j.o6.aC.S.gB))) (ef i3.S.cz.ae 83 fG ar.Do.aD ao.Do.aD 154 pB b1.mX 150 uB (dG L.cR.cH (ac ao.aF.bl.dt 342 dl.fi)) (eG s0.aX.bl 64 rZ ah bK ea 1 cI.eW (ff jA.dK.aF 49 cT.f6 170 cT.fC 1 cU.e1)))) (nm uq (gp hR.bl.bi.cd.eN 99 an K.mu.b0 L.mu.b0 17 z9.eA 25 z9.f9 (dG H.cR.cH (aG oc.fQ)) (dG d8.e0.cH (cp iP.g0 50 cL.eS cL.fm 19 cL.gH))) (N aQ.bH.hU.bo 164 cP.fu (gV nb.eK.aD 106 dP.gg 266 da.eS 65 dP.eY (d2 aN.aI.pm.bm)) (fV uk.dK.aC.aF.b6 126 c7.fu 1 c7.gO 2 c7.ev (bM dF.ag.eP.eN 72 jc q4 ur j.hK 19 dq.p5))))) (c3 kr (qS aU (eR s7.cf bd 90 an kr.mv 82 z8.p6 e_ 70 z7.gL aP (mV h7.iI.ag.bw 76 xr bj br 17 cB.fT 111 lo hj (ij tB.dv 74 hC mh 141 et ar.cJ 137 ao.cJ) (dd rF.S aA 115 dY.gL)) (eG o3.bH.ag 224 ca e_.e0.bH aE.eb.bH aP.e0.bH 1 cA.gd (g1 y2.aj 23 dM.eH 77 cL.eZ 51 cO.eS aw))) (az zc.dJ.b6 93 sM 1 cM.f4 2 cM.fE (gy bt.kY.aI (bZ lW.aj 101 bv iZ.cJ iY.cJ mW.cJ 78 ch bt.aC)) (J px.jQ.bP.eV.dK.fy 134 c8.eu (aK b1.mX.bp)))) (ef tp 102 yw cX cl 55 kA k0 51 jZ (eJ aY.gY (J bd.pU.Gd.eF 161 dj.gl (aK e_.FX.eC.gD)) (aZ (lL qo.bV 24 cN.p6 108 bN ak.ni.jd 26 cA.gn 71 ca mq.bH) (e5 BM.fg 57 cL.ev 94 b7 bF 90 bE))) (cu jx.eV.aF 94 mf aE K L 1 cP.fM (eG oe.dm.cJ.aF 233 vt aB b1.EZ bd.pE 1 di.fM (d2 nl.aI.pm.bm)) (jz cX.cQ.mv (fb cF dE b1)))))))
def DA : ab dp:=(d3 hW (N nC.eV.bz 141 Hp (aR g5.bP (bS ie.bm (bc kn (eg s8.ag 103 nW jN 1 cP.gk 2 cP.er (bk bt.ae.eh) (g4 gr.a0 42 d9.fT 155 d9.fA 14 d9.eu)) (bA m9.jq.bP 40 da.ex 1 da.fL 2 da.gg (aG L.o6.aC.S.gB))) (bS ki.aF (J ty.o6.eD.aI 58 c9.fE (al af.iH.bQ)) (ix K.hU.pm.bm (lf (pe rn.bg 36 cU.fx 92 cU.p7 H 38 cU.gn 54 cT.f6))))) (c3 dz.bI (cu g3.bV.fH 158 an cj.iV ox.iV m3.iV 1 z9.fm (aZ (wR kV.ec.b2.aF.aS 11 cV.eH 70 sb aH 167 cP.fA 163 wg) (aT uJ.iF.cQ.S 117 c6.eA 151 c6.fx 61 c6.gn)) (iw ma.dv 118 yo af 97 hJ jl 93 ju (ij gr.dv 54 rQ af 149 dM.ft K 145 L))) (N ar.bg.fd 75 cq.f6 (dG ci.hL.cH (bM i5.aj.b2.ag 195 jK cj ox m3 1 c6.gj)) (eG oG.b6.cd.bi.cd.bm.aF 68 vj aE.kv K.kv L.kv 1 c8.p0 (bZ ns.S 78 sc au X ad 58 vk aN))))) (nd (yE j2 24 65) (ku ru (gI iT.cx.bg.b2 4 z8.gn 99 an dZ.b0 95 eM.b0 (hi nb.S 102 ct.gg sh 63 hJ (al bt.eK.bH) (ac gq.bz 76 d1.gk)) (bT bq.AW.kv.hM.bu.bu 61 iz qc.iH (eo y1.a0 44 vq 85 zE aE 14 cO.p7))) (dQ ro.aj 201 cM.fU 202 cM.fi 97 wy 93 cG.f5 (gy K.kY.aI (ac iS.bP.dt 334 dl.fz)) (fV tK.cQ 74 c8.eW 171 c8.eH 167 c8.f8 (cp uh.bl 49 dq.f4 dq.fE 1 dq.e7)))) (nd (l5 gF.aX 41 mc 29 z6.fL 61 kA j) (az nB.aI.cQ 91 dn.fm 49 dn.gH 45 dn.gm (fh yZ.cd.b8 e_ 88 fe jH 1 vp bd 2 dy.fp e_ (eo jg.aS.bV.a0 142 mK 190 jK aE 14 dT.f6)) (J cX.xY.bi.cJ.aO.aO 585 dT.fx (iM jT))) (nd (wE u8.aF.jr.a0 98 rc 122 Am aE 14 cP.fo) (ir yr.cz.S.bp.aC 11 di.eW 185 cA.fK 59 vj 55 di.f8 (aG bE.S.gB)) (bD l3.ho 86 bN cX.sl.bI cl.sl.bI 83 ca K.aD.bl 79 L.aD.bl (bM ua.b2.eP.cx.aF 117 yB ah bK ea 1 dY.ez)))))) (aJ qg.ag 51 z1.ev 1 z1.eZ 2 z1.f6 (aR kr.bl (bU au.eN (eg j3.b6 64 an b1.ce 1 z8.fU 2 z8.fi (aJ ra.cd.bi.b6 169 ct.fD 1 ct.fu 2 ct.gO (lf (tQ th.cs 74 rV bF bE 153 c0.p2 150 cN.fA)) (iM bK)) (gz tG.aF.ae 68 xn br 101 wB h5 97 d4 (i7 ot.ag.bw 187 ap s6.av tU.av 17 dL.p1 101 ey bO.cv))) (N aE.vG.bu.cw 53 cG.fp (bA ma.b8 67 c9.fx 1 c9.gn 2 c9.eA (hT kK.gR.iI.S 174 mK fY 148 lA cj 144 dS)) (aZ (qk hY.cQ.dv 80 cS.ga 72 da.ft ar 68 ao) (lf (rp aQ.yk))))) (qv ak (ef nG.fj.S 117 c4 eQ.aO dz.aO 97 an lM.ce 93 ui.ce (gV tt.g0 75 cV.gb 297 dP.gk 19 cV.gd (aK px.fr.hK.gD)) (bA tB.eP.dJ 11 c7.f9 1 c7.ga 2 c7.gj (pa bd.S))) (e2 X.cH.o6.eD.aI 126 sb rS (aW ah.aO.bH (hT qa.cf 116 bv lR.aO 89 ch dk.aC 85 e6.aC)) (en ah.ae.eh (aK aA.bQ.bp))))) (cb kj.S 64 z2.p3 z2.p2 z2.p1 225 z3.fP (bc mY (nd (pO rA.aj 56 an t0.gP rs.gP ad.bi.gP 96 bt.b0) (nd (pe wr.bV 24 cB.gd 84 dy.f8 H 26 cB.fM 89 dy.eB) (ff lU.eV.aD 129 ds.fp 464 dl.f5 73 ds.ft) (dd gs.b6 aA 9 cO.fo)) (aZ (qp pK.dm.dm.aX.ae.b2.ae 118 wC L 73 wV K 69) (ac iQ.bo 169 cL.gn))) (dR lq.bg (J b1.F8.sy.cJ.aO.aO 410 cA.p2 (lf (oT k4.cz.dJ.bw 73 c6.ex c6.fL 17 c6.gg 237 ap aH.qW))) (en uq.bV.hK (cp fa.aj.aF.ag 55 dq.gk dq.er 1 dq.eB)))) (aJ m2.ec 82 z6.p0 1 z7.e7 2 z7.f6 (gp pc.bQ.cz.ae 56 xa K L 77 dn.fC 73 dn.gv (iw uJ.bp 185 lm aN 67 w2 X 63 ad (ac oc.bP.dt 334 dl.fE)) (aZ (rP l4 iC yl 32 (aM cD fB e_) 145 (aM cF fB e_) b1) (g1 fc.aX.aC 11 cU.fi 96 cU.fL 49 cL.f5 aw))) (N dO.r5.ib.bo 518 dP.e7 (ck K.kY.h8 (n4 d0.ae.bV.aS)) (de ah.AY.hK.gD (aT gF.dJ 11 dY.p9 1 dY.p8 2 dY.p7)))))))
def DM : ab dp:=(d3 aB.cH (az gU.eb.cQ 78 G2 93 Hu 89 Ho (aR sP (cu eT.b6.dm 70 dX iN aE.iF aP.aC 1 z3.fz (k2 nx.bl.a0 92 kw aN.fF 129 z7.eu 14 z7.ez (cu u8.aF.jr.ag 98 lF X hW ld 1 cy.fN (ac t0.vG.bi.k7.fy 75 dI.gl) (lf (qG ci))) (eG n8.dm.bw 111 yo aA aB dD 19 da.e1 (ac iQ.pE.eP.aI.db 107 dL.ez))) (ei kZ.eb.cQ 180 c5.eB c5.fT 56 c5.fA 52 wu (aZ (rP l4 iC Cd 32 (aM cD fB e_) 145 (aM cF fB e_) b1) (g1 oO.dJ.bQ.aC 11 c6.eu 153 xd 115 ds.ev aw)) (hX rf.jq 11 cS.p5 133 v9 63 cS.ev aw (e8 kb.cx.bg 81 xi aE K L 48 tO)))) (N dS.iH.qW 116 z5.fU (eg j3.b8 106 c4 kW 1 z9.fK 2 z9.fN (aZ (jB pK.dm.dm.aX.aF.iF 11 cV.ft 65 vm kP 285 ep K.cJ.ja 17 cV.f4) (hT mQ.S.S 73 ca ki.aF 92 bN K.g8 88 L.g8)) (J aN.hU.bP.eV.dK.fy 259 cS.eW (ac aE.eC.bu.cw 139 dM.p7))) (fR sR.cz.bg 115 cM.ga 436 cP.fL 118 cq.fN (ej u3.cx.bw 63 zm ak af 17 dP.ft 137 dP.f4 (e8 n5.pl.cf 265 yS au X ad 96 c6.eZ)) (fO jS.bH.bg.S 71 c8.fi 209 c8.eZ H 362 cN.p9 (ac oN.bi.hL.dx 156 dq.gj))))) (d3 H.ja (bU o4 (nd (l5 nG.bQ 101 z8.eW 17 z8.eH 67 an oZ.aC) (nd (qL oL.S 66 hJ 109 sh 105 ct.gg) (co uf.ec) (kf gU.cR.bg aP 112 d1.fU e_ 214 d1.fz e_ 210 d1.gl e_)) (kh rm.bV.aF 51 cA.eB cA.eu 1 dj.fz (iR qg.ag 51 mF kn 1 cO.fq 2 cO.gb))) (dR dZ.iI (fh lW e_ 62 ch bd 93 bv ah 89 bv aU (hZ lW.ag 74 ch ah.aC 74 ch aU.aC 1 cN.ex bd 2 dT.gH e_)) (en oJ.eh (cp ns.eN 50 dq.gK dq.fp 19 dq.ft)))) (gA m8.cQ 43 iB aA aB dD 80 je aw (eJ h9.hK.gY (md pS.aj.bP.bg 57 cV.p0 180 iB dk.o6.kB 299 c9.p7 (cp cZ.jr.aO.bi.S 79 dr.fq zF 129 w9)) (J kW.xY.r5.eF 189 c0.eA (cp zJ.fH 55 cU.fP cU.gK 1 cU.fp))) (az kK.S 120 et 57 hC 53 iK (mR rv.aD.cR.ja 4 di.f6 137 dj.eZ H 133 dj.fi (dc lV.i2)) (nt uc.aD.aF.aS 4 c7.eu 249 dI.fL 80 dI.ex (n4 au.bV.aS)))))) (nd (qb eE BI 24 65) (aR jv.bl (nd (rP b1.jq.nS.S iC x6 32 (t9 cD Bf bq) 145 (aM cF vY bt) b1) (nw gU.dJ.dv 100 sf dz 123 z4.gb bj 119 br (aJ oM.cx.b8 57 mM 1 cy.p4 2 cy.p3 (g4 oW.a0.aC.S 63 dr.gO 113 dr.ev 29 dr.eZ) (al bq)) (ek pI 71 ey iE 1 da.gb 2 da.gd (aG gq.bm.fr.gB))) (nd (zo uu.aF 229 c5.p8 42 w4 1 c5.f9 2 c5.ga) (aZ (jo qd.aj 23 c9.fL 287 dP.eB 271 dP.fT 107 cV.fM j) (al oJ.kv.aX)) (fS uF.e0.aF.aS 4 cI.eB 69 ve dZ 65 eM (iL i1.cz.ae 52 yy K L 130 cU.p9 126 cU.p8)))) (bS dk.bu (eR rA.ag.b6 e_ 104 an b1.ce.aS 1 z9.p7 e_ 2 z9.f9 bd (J dN.hL.bV.fd 159 cV.gg (ff lU.g0 137 dr.gL 472 dl.hH 19 dr.p9)) (aZ (jo nn.cz.S 272 c0.fq 112 c7.gg 73 yW 69 wJ j) (eo mU.jr.bV.a0 63 cL.e1 111 sj uP 14 cL.gk))) (eg pc.aO.ag.b8 100 uG jN 1 cq.fT 2 cq.fA (J jH.cx.gE.bz 509 c0.fz (em qh.aX.cz.ae 76 dl.er dl.eB 205 dL.fP 104 dl.fT)) (jz jN.bg.vz (bk mY.gY))))) (oq bK (lC cD Bc e_ (eg l9.eN 105 c4 e_.mu 17 z9.gK 25 z9.fp (im ao.mX (ml g5.aI.cH) (dd k8.b6 aB 287 d1.gn)) (aW aY.bm.bw (g1 mU.cd.aj 23 dM.gl 81 cL.eH 55 cO.gd aw))) (nd (pP t8.fj.iF 4 cM.fz 493 je cg.cH 17 cM.p3) (J e_.bV.cH.hU.gT 140 dj.gb (aK K.A3.vC.cJ.fr)) (fO fa.aj.aF.b6.S 123 v9 71 cI.fM H 67 c8.eS (bZ rk.iF.aj 134 hB t0 rs ad.bi 79 jc lS)))) (eR hR.aS.S bd 51 z5.gk bd 97 z6.p8 e_ 29 z6.p7 e_ (bS kP.aF (aZ (pk tR.bw 113 dy.fT 174 ch bO 17 dy.fA 94 hD aH) (eo i4.b6.aj.cQ.S.S 84 dr.eA 138 dr.fM H 528 dl.gL)) (jW m1.aC 11 c7.f5 105 bN dV.vG.jd 72 ca fY.F8.bH (ac aE.cH.eD.aI 226 cU.eW))) (N aE.e0.aI.k7.fy 68 cP.p8 (aW tF.bw (lf (oP j8.cz.b8.cd.iF 4 dL.e7 130 dL.f6 17 dL.er))) (fO sK.dB.a0 73 cN.eA 115 AP aE 14 dI.fm (fb cD vr bd)))))))
def DQ : ab dp:=(az fc.a0.ae 45 Hz 129 HY 126 HK (nd (rP eE iC tA 24 (aM cD dE e_) 65 (aM cF dE e_) bd) (aR bq.bP (bS ed.eP (nd (rM nu.bP.aX 94 kw dz.fF 29 z7.gd 114 qz.bI) (qe jx.pl.aS 11 cy.gb 190 xo 243 cP.eu aw (eo os.bg.bp 125 c7.ex 82 c7.ez H 243 dr.ez) (fW ah)) (dG aV.hL.cH (bC rL.e0.cQ 98 ey h5.cY d4.cY 192 ap nC.av 188 nH.av))) (gp oW.a0.aj 171 c5.fp ak af 59 c5.eS 55 c5.fm (kN ii.nS.S 106 hJ e3 ed d0 113 c9.eY (al ar.fr.aX)) (bD jg.bp.aj 134 pA bF bE 79 pq jt 75 gX (g1 iu.aD 47 cT.e7 101 cT.hH 55 cU.ez aw)))) (nd (zr cF Bf cl) (o2 um.S 65 an i6.aC 111 c4 cj 107 dS (J iE.AY.hK.dh 213 cV.gl (aK d8.io)) (aZ (nJ g9.cz.aS 11 c0.fN 35 c0.ex 140 lA K 136 L) (nA iy.gZ 53 cL.fP cL.gK 90 rX X 86 ad))) (dR hW.bg (J jy.aX.pG.bo 674 ds.f8 (dc rs.gP)) (j4 tF.aI.bu (iL te.bi.ae 72 zU K L 60 cT.p9 56 cT.p8))))) (aJ fk.ec.aX 40 z2.gl 29 z2.e1 60 z2.gk (qS jN (aJ pg.b8.b8 79 z8.ga 1 z8.gj 2 z8.f5 (dR lS.a0 (ac bd.aF.bl.dt 342 dr.fA) (dd lD.S aA 71 dY.gg)) (du ov.aD 62 xj g5 gq k6 101 bv kc (lc uu.S 233 dM.p9 46 cO.p4 105 hB 101 cO.p2))) (nd (pe uv.bV 24 cG.p9 78 cG.fq H 26 cG.p8 94 cM.eB) (fS n5.cR.ja 4 dj.fA 184 lm bK 180 ea (bC sY.S.bV.aj 102 hD lk.pG kS.pG 242 ch b1.aX.bV 238 bd.nj.bV)) (o8 rn.iI.ho 209 cN.fp cN.ft 130 c8.er 126 cI.ex j (aT uy.eP.b8 55 cT.fq 1 cT.gb 2 cT.gd)))) (d3 aE.jq (cu il.cz.bm.aF 53 AK ah bK ea 1 dn.gd (fh AQ.eK.iI.S bd 180 xo e_ 251 cB.ez H 370 dX d0.fr (dc jn.zh.vz)) (nt Cq.iF.aF.aS 4 cN.fK 409 cN.fm 165 cN.eS (ly jX))) (gp rl.pl.ae.cQ 64 cy.gd K L 161 cP.fN 157 cP.ex (aZ (xh o9.aj.a0 147 di.gg 126 di.eY 86 rV aE 14 di.eS) (hZ kL.aO.cQ.aC 11 dL.gO e_ 178 ap j.ym.hM.fF 232 ap b1.aS.fj.bI 49 dl.gj e_)) (gV yF.gR.ae.aj 70 cN.eY 235 cN.fq 167 cN.eS (aK dN.CR.xK.S)))))) (c3 K.hU.bI (eL d4 (ku j.bm (nd (qU dF.iI.aj.ae 72 pw K L 103 nY 99) (N nr.hM.gT 82 ct.eB (e5 fk.dJ.bi.cd.dv 76 c7.p7 114 v9 ar 110 ao) (lf (rP l4 iC x6 32 (aM cD fB e_) 145 (aM cF fB e_) b1))) (J jn.bl.eC.db 82 cA.e7 (mg tJ.dJ.aS 11 dL.p0 199 ap h9.nj.eK.av 137 ey H.cQ.cv 133 j.aX.cv))) (mi uu.aF 42 pp e_ 42 cG.fP e_ 42 pp aP 1 c5.f9 bd (gW s9.eb.ae.eV.aD 180 iB ob.o6.kB oo.o6.kB 307 dP.f5 186 cV.p1 j (kf iy.ec.aj.S.ae bd 65 dT.fz e_ 65 dT.gl e_ 121 cN.eu bO)) (kN uc.aI.S 149 l0 H ah aU 72 v6 (dc lV)))) (qv j.bg (nw l9.dv 121 c4 dz.aO 101 an bj.ae.ce 97 br.ae.ce (J nK.aI.db 71 cV.gj (co oB.aF.ec)) (ck H.cR.ce (cp uk.fH 51 cL.p9 cL.p8 1 cL.p7))) (dQ i5.aC 11 cq.gd 139 cP.hH 202 cP.gL 119 cq.fM (md ii.eP.aD 70 dP.p9 237 iK ci.pl 65 dP.p8 (bM qa.g0 112 bv aA.bQ.aO aB.bQ.aO dD.bQ.aO 19 dl.gg)) (bT nC.AW.kv.hM.bu.bu 61 iz rE.fr.iH (n4 H.n2.aS))))) (bc aV (bc mW.aI (eg qV.ag 108 c4 iE 1 z9.fi 2 z9.eW (N fY.Cv.aI.db 74 cB.p7 (mg l3.ag.aS 11 dr.gj 83 ca aH.wk.bl 94 bN dZ.d6 90 eM.d6) (lb aE.S)) (du tx.aS.aj 62 ep g5.ja gq.ja k6.ja 139 iq lP.bI (lf (Cs j)))) (nd (AB sI rU 24 65) (ck mq.h8 (bC ti.cs 146 et qI.bP oH.bP 101 iK jt.cJ 97 gX.cJ)) (J jN.bg.jd.eD.kk 221 c8.fx (ff n6.bQ.aj 35 dq.fT 43 dq.fA 60 dq.eu)))) (om gF.aX.aC 11 z7.fE 87 kA dV.gP 53 mc aw.fF (eg g3.ag.b8 74 fG jN.aD 1 c5.fu 2 c5.gO (du eI.ja.cR.a0 59 cq.fC au X ad 115 nZ bt (lf (oE u0.cf 71 c0.eZ 180 b7 g2.ae 176 kg.ae))) (bA os.bm.b6 143 cS.ex 1 cS.fL 2 cS.gg (ly jV))) (qw oy.cz.aS 4 cy.er 152 ct.gj 74 ct.ga (fO pS.eV.ja.a0 87 dj.p0 188 zu aE 14 di.p0 (bZ kL.fH.bg 106 y0 au X ad 182 ap i6.d6)) (bA iu.dB.ag 135 dT.fo 1 dT.fU 2 dT.fi (la gs.ag 42 d9.f4 d9.fE d9.fD 1 d9.fu)))))))
def DG : ab dp:=(c3 b1.AW (hS tC.aC 4 H8 307 HH 29 HL (aR aU.bP (aR iE (bc jN.bu (nd (wH qi.jq 11 cy.fi 149 lo au 72 cP.fP) (i7 tw.aF.bw 82 bN rH.cH pY.cH 17 dI.gv 75 ca lV.bI) (lf (wW bK))) (ix h5.pm.bm (bZ tJ.a0 183 ap H.bu.av u1.av aU.bu.av 121 ey bt.cY))) (bU aV.fy (bA pV.dJ.aX.aF.b8 176 dy.fx 1 dy.gn 2 dy.eA (g4 qy.gR.ae 28 ds.fq 482 dl.eH 478 dl.f8)) (fV rn.aD.bQ 62 rZ 17 cS.gd 339 cI.gk (co jV)))) (bc iS (nd (q2 qK.cz.aj 23 z9.er 130 c4 uN 114 H.bP 110 uj) (ir oM.iF.cQ 43 cB.p3 44 cB.p2 29 cB.p1 26 cP.fM (h6 ud.bV.a0 97 bN gS.g8 100 ca gf.cY 14 ds.fU)) (ir jA.dK.gR.aC 11 cS.f6 167 cS.gm 38 cS.fP 29 cS.gK (fW jk))) (lY tH.bu.aD 57 cM.gb 154 rc aE 65 cM.gd (aW aw.nT.nT (ff oO.dJ.g6 91 c6.eZ 190 c6.hH 1 c6.fo)) (en rJ.eh (aG au.bu.iG))))) (bc pR (bU aw.eN (fR iT.bl.aS 11 z8.fK 65 z8.fN 60 z8.ex (N ki.FH.ib.bo 582 da.ft (iL gG.aj.cR.fg 181 dI.fD K L 76 dI.ft 72 dI.f4) (al cg)) (ck e3.gP.nj (bC tJ.cz.ae 191 ap K.iG.ce.bi L.iG.ce.bi 109 ey q7.cv 105 nL.cv))) (nd (wH rk.ja 11 cG.fU 105 cG.e7 aE 49 cG.fP) (ej uW.eV.ae 60 Ah K L 41 cB.fU 96 cB.fi (lf (rP eE sd vw 24 (aM cD dE e_) 65 (aM cF dE e_) bd))) (de cl.o6.bp (iM b1.bu)))) (hi tx 38 ep dX 1 z6.fp (qs cZ.dJ.bg 36 dn.fu 84 dn.gO 38 dn.ev 147 dn.fT (jW tt.b6.aj 23 cV.p9 105 cy.ev aE 79 xc bq (iL i1.dK.ae.aj 64 wn ak af 88 ds.gl 84 ds.e1)) (jW n1.aS 11 c0.gk 188 b7 ci.ni.ae 69 cA.f6 aw (ly g7))) (nd (wR sQ.aS 11 cq.gj 106 cM.eu aH 613 c9.fp 60 cM.ez) (ng tL.b6.bw 76 dP.p2 292 cN.p1 19 dP.p1 (aK aH.cJ.kY.ib.fr)) (de bt.cJ.kY.ib.fr (i7 uu.fj.ag.bw 80 jc pT rJ 17 dY.eH 151 hB lV.aI)))))) (aR aP.eK (mi sJ.a0 59 z1.fx e_ 59 z1.gn e_ 59 z1.eA e_ 259 iJ uK (bS l6.bm (bc dV.bl (N ui.rG.bm.bz 64 cy.eA (ff sX.S.b2.ag 114 c0.gd 274 dr.fL 1 c0.fM) (fW gx)) (dG b4.bm.cH (e8 oO.eb.bu.cf 89 AF au X ad 145 dL.eY))) (bU eQ.aO (mR m9.cQ.ia 4 c9.ez 493 mJ ub 126 dP.f8 (bZ re.ho 71 pz g5 gq k6 188 b7 lP.aC.ae)) (o8 os.bm.aD 121 cI.fp cI.ft 70 ts 66 cS.eY j (ac kJ.mu.eV.dK.fy 67 cT.fD)))) (cb gs.jr.bV 131 z5.fM z5.fx z5.gn 161 z5.eA (nd (pO sL.aj 66 an oD.i2 tF.i2 L.sl.i2 106 kc.b0) (J lR.gE.bz 552 wn (ac va.kY.eF 925 dl.ga)) (dG o7.bm.cH (nA fc.gZ 53 cL.gO cL.ev 90 b7 X 86 ad))) (N e4.bP.hV 64 cq.eW (gW ii.ag.bw 109 sh bj br 17 dP.fN 78 hJ aH (d2 dz.aI.pm.bm)) (ck jk.fQ (hZ rk.iF.a0 75 jc fX 75 jc d8 156 hB tS 14 cT.fN aP))))) (eL aV (cb h3.pl.S 112 z4.gb z4.gd z4.fM 93 z4.fx (nd (pJ m2.it 117 zZ au X ad 102 z8.gg) (aJ ma.bP 32 cB.e1 1 cB.gk 2 cB.er (lf (lB g9.cz.b6 136 lA jN 1 c0.p8 2 c0.p7)) (dd h7.b6 aA 9 cO.fE)) (gV o9.aj.ag 135 cA.gm 134 cA.fC 1 cA.gv (co kn))) (fR h7.aI.a0 55 cG.gv 63 cG.fz 90 wh (ck aV.h8 (bC qQ.cz.ae 183 b7 ak.hM.cK af.hM.cK 86 pu h5 82 d4)) (od rn.iI.ag.aS 11 c8.fA 130 y8 j 82 vo K 78 L (al bt.aI)))) (N lG.bP.dh 56 z6.fq (eJ H.xM.gY (J K.xE.mX.aF.sl.aI 136 dj.f8 (al ao.iH.bQ)) (aZ (jB q8.iF 11 c0.fC 181 b7 bO.ja.ae 104 pu K 17 c0.gv) (co jX))) (N cl.eC.db 481 cB.gj (eG jp.eb.bm.aF 63 sk fI rb tg 1 di.gb (ij qY.dv 120 bv iQ.aO 93 ch qI.aC 89 oH.aC)) (J fY.aX.bl.eD.kk 239 cN.gb (g4 mj 38 dY.fC 115 dY.gv 14 dY.fq)))))))
def DD : ab dp:=(eL aH (m6 H.S (nd (yN uE.dm 102 z1.gg 254 iJ aE.iF z1.eY 1 z1.eS) (mi s5.b2.a0 130 z3.ez e_ 130 z3.fK e_ 130 z3.fN e_ 75 dX uK (gA kb.dJ.bi.aD 72 kA e4.gP fI.gP iD.gP 60 mc hO.cH (nd (l5 tt.b6.aX 75 cP.fi 29 cy.gH 95 xr j) (d2 aA.aF.pm.bm) (aT jA.dJ 11 d9.gl 1 d9.e1 2 d9.gk)) (J e_.kB.eK.dt 334 c0.ez (iR j8.cx.bp.ag 184 ap b1.aC.iH.wi 1 dL.gm 2 dL.fC))) (cu gs.iI.eP.aF 80 fG H.rG.bw ah.rG.bw aU.rG.bw 1 c5.ex (aW cl.nT (iR re.ag.b8 184 b7 kx.aC.ae 1 ds.eY 2 ds.eS)) (J pR.cJ.bi.hL.dx 156 cS.fT (g1 lO.bH.bi.aD 81 cU.fM 482 dq.fo 56 cU.eH aw)))) (eL oH (eR g3.aX.dB e_ 100 an qq.aS 68 an iS.gP 64 an t5.gP (J aU.gP.o6.eD.aI 284 c9.fP (dc b3.cQ.mv)) (gW nh.cR.b8.bw 70 pq jw jD 17 cS.fK 141 pA bO (aT uE.dm 11 dM.gm 1 dM.fC 2 dM.gv))) (fR nB.bP.bw 89 cM.p4 171 cq.gb 19 cM.p3 (bT gS.kv.pU.hK.dh 305 ky gS (aT qa.ik 11 c6.p4 1 c6.p3 2 c6.p2)) (bD vg.b2.aj.ae.aj.cs 114 di.gl bF bE 77 ve jt 73 gX (ac oc.bi.hL.dx 156 dq.gL))))) (cb j7.eN 33 z2.fA z2.eu z2.ez 19 z2.fK (ku H.bm (eR gF.bQ.gC bd 75 z8.fN bd 82 z8.gb e_ 70 z8.gd e_ (N au.bu.dt 334 cV.p6 (em lH.jq.cR.bw 79 dr.f6 dr.fP 17 dr.gK 71 dr.fp) (lf (zw aB.cH))) (J dO.ni.cH.hU.aI.aI 74 cA.fN (g1 i4.cd.aj 23 dM.fD 73 dM.p3 47 cO.eH aw))) (nd (qL fa.cx.cf 101 nW 63 rc 59 lF) (J qn.Gd.eF 258 di.ev (fJ cl.pE.eC)) (de Bh.o6.bp (aG qn.vS)))) (fR eT.cQ 31 z6.eB 39 z6.fT 40 z6.fA (pQ aQ.yk (od tl.aS 11 dy.fP 73 yt j 94 fe lq 90 gN (al kx.bl.bH)) (gy ka.GE.eC (iM hQ))) (qw fa.cx.b6.aS 4 cP.gO 101 cP.ev 97 cy.fK (aZ (pe uQ.e0.bg 48 di.fD 110 lJ H 50 di.fu 56 cA.eB) (al jy.bH.bH)) (gz gG.cK 80 pp j 48 c5.p0 K 44 L (fW jU.cx.bu)))))) (cb g3.gR.iI 60 z1.fE z1.fD z1.fu 108 z1.gO (cu g3.dB 242 iJ nk g2 kg 64 z1.gL (bU oX (m6 ad.S (lY ta.bg 58 ct.e7 221 vu au 236 mG (iR l3.eP.b8 75 ca jN.kY.bH 1 c0.p4 2 c0.p3) (aT hY.aX 48 d9.p3 29 d9.p2 68 d9.p1)) (aW eQ.iv (pM tJ.eb.iF 4 dL.p6 137 ey H.bQ.cv 17 cO.fP))) (nd (yz dF.aj.S 50 pp 92 cG.e7 41 cG.f6) (ek mZ.b6 64 ey pr 1 c9.gb 2 c9.gd (lf (sN sO.gR.bg 36 dT.eS 223 b7 K.xM.cK 38 dT.fm 185 i6.ja.ae))) (gV d5.eN.g6 85 cI.eY 84 cI.eS 1 cI.fm (ac mT.eF 177 cT.fL)))) (cb pg.cz.aF 84 z5.p8 z5.p7 z5.p6 1 z5.p5 (cu qx.fH 116 c4 o4 hW.bQ ld.bQ 1 z9.p4 (ir oy.gZ 418 wm 78 cV.gm 101 zM 97 cV.gv (eo rt.aF.b2.a0 202 c6.gH 119 zf aE 14 c6.gm)) (aZ (oi i5.S.a0 72 hC bd.ia 157 et ci.aO 14 c0.fm) (bZ Ag.S 108 iq jv dk e6 53 ep b4))) (N j.fr.pU.hK.dh 63 cq.ex (eG mP.ag.dm.bw 78 rO aA aB dD 19 dP.gj (kf u5.e0.fj.S e_ 183 ap l6.hL.bI 129 vl H 125 dl.gn aP)) (en iX.eh (aK ke.bp))))) (qs h3.ag 218 z2.p6 267 z2.p5 220 z2.p4 1 z2.gL (nd (kH bd.cJ) (lY pg.b8.aD 47 z9.ev 140 an au.jq.aS 87 z9.eZ (az iy.bV.b2.ae 175 lm 57 w2 53 u2 (lc g9.cz.aD 467 dl.fp 132 dr.p0 75 ds.e7 26 ds.f6) (dd mj aA 21 cO.eZ)) (fV jS.cz.aD.ae 63 cA.p8 103 cA.p7 99 cA.p6 (g1 lH.eb.aj 23 dM.gk 85 cL.e1 59 cO.ga aw))) (dR af.S (ej Al.cz.S.ae.e0.cQ 114 wC K L 69 dj.eA 65 wV (bZ pf.aj.b2.eV.bg 95 vn jv dk e6 156 vi aN)) (J oX.iv.bm.dx 164 c8.fq (bM uh.ag 53 vk ah bK ea 1 dq.e1)))) (eg gF.aX.bP 49 mc e_.fF 1 z6.p3 2 z6.p2 (nd (jB qX.ag.iF 11 c5.ft 81 fG bd.pU.bw 172 pB H 17 c5.f4) (bD jx.aj.cs 106 cy.gj bF bE 72 mL nr 68 mh (bC i5.aj.b2.aj 147 mK aY aQ 199 jK cg 195 b3)) (bD pX.aX.cz.ae 66 mM ak.hM af.hM 98 nZ h5 94 d4 (ac b1.eh.dh 136 cU.eB))) (hi ko.cx.bg 47 cq.gL cq.fD 83 cq.fE (bT np.r5.Gy.bm.bz 146 ep aH.cJ.ja (al X.jd.mu.bH)) (jz aU.bg.vz (lf (zD aV))))))))
def DK : ab dp:=(c3 L.AW (qs gU.cR.bg 116 G4 248 Hs 118 Hv 214 GW (aR kn (aJ eT.b6.dm 11 z3.eW 1 z3.eH 2 z3.f8 (N e_.ae.pG.eV.bz 63 z7.eB (dR kO.a0 (g1 uk.dK.aC.aF.aS 11 dr.fU 94 dr.eA 130 c7.fu aw) (lf (rP qu iC x6 28 (aM cD hI e_) 105 (aM cF hI e_) b1))) (aZ (l5 pf.cQ.bP.aX 69 dP.fD 29 da.fz 89 pq gx) (g1 lK.cx.bg.b2 11 dL.fz 93 w6 181 ap bd.ia.iH.wi))) (bU bF.bu (ck aE.rG.h8 (iO yR.kB.ib.gE.cw 244 ap yR.xM.fF)) (ck Bg.fQ (e8 kQ.dK.dB 94 sj au.bQ o4 ad.bQ 68 cU.fu)))) (nd (kH lG) (aJ uo.dJ 11 z9.fA 1 z9.eu 2 z9.ez (bT j.fr.hM.bu.dK.fy 112 iB j.mX.kB (d2 af.aS.vC.bm)) (du qN.cd.eP.bg 75 ep ci.mX.n2 aV.mX.n2 cC.mX.n2 168 iq mE.bV.jd (aT h7.ik 11 dM.fA 1 dM.eu 2 dM.ez))) (qe rd.aS 11 cM.eA 71 cq.p5 99 uC aw (J aE.r5.ib.bP.eV.dK.fy 253 dP.gK (lf (l5 o3.aI.cz.bQ 19 dl.f6 17 dl.fP 180 ap bO.d6))) (en lS.eh (ac iQ.bi.hL.dx 156 dq.hH))))) (nd (rP eE sd EK 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (bU dS.eN (rz tC.dv 99 z8.ft 118 z7.ev bj 114 br (e2 nE.i0.bo 204 fe X (co kP.aF.ec) (lf (kH K))) (aZ (ww lT.bl.ec) (aT y2.ag 47 cO.eS 1 cO.fm 2 cO.gH))) (dR j.iI (gV w0.aj 81 zX 205 cA.fu 58 wO (bM j8.fH.aD 92 hD aA.ib aB.ib dD.ib 155 dT.gg)) (jz kP.GF (hZ uh.a0 53 cT.ga e_ 53 cT.gj e_ 95 sc aE 14 cT.f5 e_)))) (N FY.cx.bz 40 z6.fU (az BE.b2.ae 91 dn.eB 50 dn.gk 46 dn.er (eG sQ.bw 98 nW au X ad 19 cV.p3 (fJ pR.vz.aI)) (ek q8.b6 177 b7 xP.aC.ae 1 c0.fA 2 c0.eu (co g7))) (nd (rP fk iC A2 20 (aM cD kD e_) 25 (aM cF kD e_) bd) (aZ (wH wQ.b2 11 di.e7 106 bv gf 61 dj.gO) (al rJ.kv.aX)) (ck jT.fQ (fW dO.eV.bu)))))) (lC cF Gf b1 (aR iD.bl (dQ dF.ec.aj 23 z3.fx 66 z3.gn 50 z3.eA 46 z3.f9 (nd (tQ dF.fy.b8.bw 95 kw rE.bI rN.bI 17 z7.p0 182 z7.fC) (gI uw.aF.aS 4 cy.p6 64 mL lq 60 gN (em d5.b2.ae.cQ 197 ds.eu ds.ez 74 ds.fK 70 ds.fN) (fb cF fB b1)) (ck ka.aF.aC (kf pI.jr.ag e_ 131 ey Dn.cv 1 dL.p3 bd 2 dL.hH e_))) (az uy.bl 23 c5.fx 1 c5.gn 2 c5.eA (aZ (qk mP.ag.fg 82 cV.gm 105 cV.gv K 101 L) (bZ qo.dB 83 ca tq.cY j5.cY lG.cY 102 bN pd.g8)) (k3 u3.cx.aD 175 cI.fU e_ 175 w3 e_ 339 c8.eH aE 67 rZ j (al kO)))) (az g3.eb.cQ 82 z5.hH 133 z5.gL 129 z5.p9 (cu nF.g0 111 c4 aA.bQ aB.bQ dD.bQ 19 z9.hH (aZ (lz ju.cY) (ij l3.cz.ae 86 bN pY.cH 83 ca K.A7.bI 79 L.A7.bI)) (du B0.aD 165 ap jn.bi o7.bi j.nj.bi 75 ey kc (cp gr.g0 54 cL.fC cL.gv 19 cL.fq))) (rz j7.bQ.cz.ae 121 cM.gH 73 cM.fC K 69 L (jW mZ.aS 11 dP.fx 180 ap iN.bi 68 ey gS (aG mh.eK.ce)) (de ed.gY.gD (mg rk.eb.ae.aC 11 dq.p6 150 hB hj.gP.wi 69 mH H.kv.hM 65 j.fr.hM))))) (cb j0.ag 36 z2.fM z2.fx z2.gn 1 z2.eA (nd (kH aV) (cu um.ec 103 c4 b1.fy H.ec j.fy 1 z8.p0 (e2 kP.FT.bu.dK.fy 131 je aH.iG (ac uU.bV.fd 159 dr.ex) (pa aE.S)) (bD jp.eb.bg.aj 83 nZ aY aQ 71 mM eQ 67 dz (fW kn))) (dR K.bg (e9 li.eb.ag.bw 113 dj.gm dj.fC 17 dj.gv 77 dj.fq (al b1.dm.mu.bH)) (ck rK.fQ (lg uy.eP.aD 55 dq.f8 131 jc e_.bP 59 cT.fq aw)))) (lE iP.eN.aj 35 z6.f5 43 z6.hH 50 rY hO (nd (lL cZ.aS.gR.bg 36 dn.gL 96 dn.fq H 38 dn.p9 58 AK aN) (aZ (qU BZ.cx.ae 56 wz K L 95 xl 91) (ac lR.aI.eC.bu.bz 393 c6.e7)) (du lK.aO.S 89 rV dO cj dS 229 ca bd.e0.bH (iM kp))) (nd (pk jg.cd.aD 139 ct.ft 200 pn gx 227 ct.f4 126 cq.fM j) (bT oB.ym.hM.bu.dK.fy 112 iB oB.Ej.kB (hZ uJ.cx.iI.aC 11 dl.p5 e_ 344 ap j.Ej.mv.bI 312 ap b1.F8.xE.fF 75 dl.p4 e_)) (du nb.dB 71 Az au X ad 126 fe lR (co ah)))))))
def DS : ab dp:=(hS jm.hL.ae 119 H0 47 GD 43 Hz (nd (qb eE Bw 24 65) (e2 h9.bm.bu.bu.dh 151 iJ j.aC (rz qN.dm.aX 132 z3.e1 59 dX bF 55 bE (gp iA.eP.S.ae 97 nY K L 74 z7.fC 70 pw (e2 b1.cQ.rG.bm.bz 122 dX xP.fr (ff os.bg.ae.aj 125 dI.fN 347 dr.p4 82 dI.ex) (cp gr.ag 42 rQ sj 1 d9.gg)) (J bt.e0.bV.fd 159 dP.fq (qm rL.eK.aS 11 dL.gj 35 dL.f5 192 ap lq.eK.av 188 gN.eK.av))) (bU aQ.aO (J ci.hL.bV.fd 159 c9.e1 (dc ak.pU.sy)) (J k0.cJ.bi.hL.dx 156 cI.fP (lf (oP hY.aS 4 cU.gb 52 cU.gd 48 cT.fp))))) (N k0.Aw.bz 67 z5.fN (eR uH.a0 bd 94 an aw.jq.aS 98 an q9.gP 14 z9.fC e_ (aW aE.cR.nT (aK oJ.io)) (J mq.GO.bi.k7.fy 327 c7.eA (eo ko.bV.a0 55 cL.e7 103 vq q5 14 cL.f6))) (dR ad.S (dG cg.cR.cH (aT qh.eP.cR.b8 126 c6.p8 1 c6.p7 2 c6.p6)) (en jH.cv.bH (bk lP.gY))))) (c3 fI (cb gU.dJ.ag 88 z4.fL z4.gg z4.eY 1 z4.eS (cu gs.aI.S 80 an dO.mv cj.mv dS.mv 60 u7 (lY pf.aj.aF 120 cB.fu 358 iB hW.bH.kB 1 cP.fu (lg q8.aS 11 ds.fz 86 pz gf 181 b7 aN.aC.ae) (ac gq.gT 92 d1.ez)) (aZ (nJ kZ.eN.cR.aS 11 cA.gg 64 cA.eY 118 lJ K 114 L) (h6 iA.gC 103 rX aw 52 cO.fA H 48 cO.p5))) (mi j7.bQ.a0 46 cM.er b1 165 cG.gd aE 48 cG.f9 e_ 93 w7 bd (aZ (qP yA.b2 4 dy.fo 95 bv bK 91 ea) (bC oY.ho 106 bv rB.cJ qn.cJ 87 ch eQ.aC 83 dz.aC)) (bT H.bu.AW.kv.hM.bu.bu 61 iz tq.kv.iH (lf (xh tM.bl.aj 23 cT.p5 78 cT.p4 62 cT.eY H 58 cT.p3))))) (mi eT.bl 36 rY e_ 36 z6.ez e_ 36 rY aP 1 z6.f8 bd (eJ ao.hK.gY (bD tL.aX.aj 58 vu bF bE 108 mf cg 104 b3 (al d0.bl.bH)) (gy bK.iG.eC (ms kp))) (eR kV.ec.b2.aF.aS bd 4 cq.f9 bd 167 cP.fA e_ 163 wg aP (ek qh.bi.b8 186 lm iE 1 di.fN 2 di.ex (iO h5.mu.hU.gE.cw 232 ap h5.xE.fF)) (gy H.gP.aI (aK ao.CR.xK.S)))))) (d3 Dq.cH (d3 bd.aS (ku q5 (c3 ut.aF (lY pf.cx.bg 53 ct.gl 296 vt X 409 c9.gK (aG jX.fQ) (la jS.S 178 d9.p0 d1.e7 d1.f6 51 d1.fP)) (J aV.cd.aI.db 126 da.p2 (hT th.aj.aj.b2.ae 102 ey d4.cY 196 ap H.gP.aI.av 192 j.sy.aI.av))) (nd (Ar H.yk) (bD kK.cs 65 hC bF bE 136 et jt 132 gX (aK iX.io)) (eG hR.S.bV.e0.aF 75 ep fI.pE.n2 rb.pE.n2 tg.pE.n2 1 cI.f9 (al rJ)))) (qv b1.bg (gA nG.dB 75 an H.d6.aC jy.i9 ru.i9 121 c4 b4.bQ (bT H.bV.rG.bm.bz 114 dX ah.bg (cp rm.eP.bg 63 dr.ft c0.eB 143 c0.er)) (ir oQ.bl.cd.ia 11 cN.p5 23 cN.p4 138 cN.ex 126 cN.p3 (aK g7))) (N au.bg.fd 73 cq.fq (bD tl.aD 86 wB aY aQ 73 xn ak 69 af (bC rr.gZ 115 bv ke.aO iX.aO 84 ch ed.ni 80 d0.ni)) (J aA.ib.hU.bP.eV.dK.fy 104 cN.p8 (aT tK.b8 66 dY.fp 1 dY.ft 2 dY.f4))))) (nd (rP eE iC tA 24 (aM cD dE e_) 65 (aM cF dE e_) bd) (bc oc (o2 qK.S.S 110 r6 aN 76 an aV.h8 72 cC.h8 (lQ pX.aX.S 78 nZ 62 mM H 123 dy.ex (hT tr.cx.bi.bQ.S 95 bN bq.vG.jd 80 ca mT.bH 76 rC.bH) (dd gr.a0 aA 21 cO.fi)) (bD mQ.cs 73 ca lk.bl kS.bl 92 bN m4.bI 88 sW (ac gX.bu.cw 137 dM.p8))) (hi ro.bl 89 cM.eB cM.fK 1 cG.fK (aZ (Aa tw.bP.aX 82 bN K.hU.fF L.hU.fF 29 dj.p8 102 qz.bI) (lf (ow oY.ag.aj 23 c6.er 140 bv ci.bo 114 aw.aO.aO))) (J dk.iv.bm.dx 164 c8.gd (bk tP.gY)))) (aJ kj.q6.ag 90 z7.gK 1 z7.fp 2 z7.ft (gI iT.eb.ia 4 dn.f9 73 fG H.eN 69 j.bw (du oM.iF.aj 240 yv H ah aU 75 r7 bq (dc tF.fr.vz)) (du ol.aS.ae.aj 124 Aq aA aB dD 69 pq bq (e8 mP.dB 86 vq H.bm jy ru 60 cL.p6))) (N ea.i0.bo 70 cy.e1 (fS eT.cd.gR.aS 4 di.p2 141 iq qR.bI 137 tN.bI (iO kJ.mu.hU.gE.cw 232 ap kJ.xE.fF)) (mR tR.cd.aS 4 dT.ev 234 ch ak.bV 153 dT.gg (ji bq)))))))
def DN : ab dp:=(nd (kH K) (bc ed (aR tq.bP (aR nE (eg kb.dJ.bi.b8 56 mc jH.cH 1 z7.f8 2 z7.fz (N fY.fy.dt 334 cB.fD (kf iu.dB.a0 e_ 134 cN.p1 e_ 119 hD ci.aO 14 cN.p2 aP) (ji ox)) (ix lV.pm.bm (eo ph.a0.bP.S.a0 140 dL.fu 106 AF aE 14 dL.fi))) (bS dO.bl (J e3.Ga.sy.cJ.aO.aO 422 di.p9 (lf (jo eI.b8.jr.it 181 c6.fu 89 c6.f6 262 yS 258 c7.eA j))) (aZ (jo i1.jq.dB 75 cS.f9 76 cS.ga 68 Ai 64 da.ft j) (fW jV)))) (nd (kH aY) (nd (qb eE sw 24 65) (du o0.cs 209 ct.p3 H ah aU 66 pn bq (d2 nr.vC.bm)) (ck e3.ec.aC (iM jk))) (om zc.dJ.aS 11 cM.fx 72 cM.fm aE 97 sM aw (bA ra.bw.bP.dm 11 dj.p3 1 dj.p2 2 dj.p1 (iR tV.bQ.ag.b8 160 l0 iE 1 c6.fi 2 c6.eW)) (de bE.bH.bp (aG ah.gY.iG))))) (dR np (bU dD.bQ (bc jT (aJ jx.cf 60 pn 211 un 207 ct.p3 (e5 tn.cz.ae 178 c0.e7 85 c0.fP K 81 L) (ac H.iI.cx.bz 119 d1.fD)) (gy eM.iG.eC (aT fa.eb.ag 47 cO.er 1 cO.eB 2 cO.fT))) (aJ h7.aI.cQ 85 cG.gl 51 cG.e1 295 cM.eW (aW kr.nT (lg tz.cJ.b8.aS 11 c6.fE 90 yu b1.pE 157 l0 gS)) (kh uY.aC.S 65 yu v6 146 l0 (bk e_.cz.gY)))) (nd (qG j) (pQ aH.yk (gW wZ.ag.bw 127 et jw jD 17 cV.p4 72 hC bO (aK uB.gP.ib.fr)) (eG uA.dJ.b6 167 b7 hW.ae aE.jq.ae aP.ia.ae 1 c0.fU (bk g7))) (N aN.yk.hU.bo 174 cy.fp (J ed.r5.eF 172 cA.f4 (al au.bm.bH.bH)) (bA te.bg.ag.dm 11 cN.fM 1 cN.fx 2 cN.gn (hZ ua.b2.eP.cz.aD 113 dY.fz e_ 113 dY.gl e_ 99 zP aE 26 dY.e1 e_)))))) (eL b1.CR.aF (aR jT (ei iy.ec.eN 41 z3.fq z3.gb 17 z3.gd 25 z3.fM (N aE.r5.ae.pG.cw 78 z7.p5 (N b1.EZ.eC.db 487 dy.e1 (aG ty.sy.nj) (aT li.dJ 11 d9.gv 1 d9.fq 2 d9.gb)) (aZ (oi ii.bV.a0 121 fe aN 88 Az aE 14 da.gv) (lf (lZ j8.cx.bp.aj 78 dL.fM dL.fx 188 ap bt.aC.iH.wi)))) (eJ aE.vC.cJ.fr (aZ (lz ah.cY) (ac L.o6.av.k7.fy 269 dT.p9)) (J vR.cJ.bi.hL.dx 156 cI.fz (al oJ)))) (bS gX.bu (cu uH.ag 94 an X.ia.aS hW.ia.aS ld.ia.aS 1 z9.ga (aZ (lz lV.cY) (e5 rf.dv 75 dI.eY 99 wl ar 95 ao)) (bT ad.iH.aI.hV 124 hC dS (h6 sJ.a0 59 mF jT 107 dX uP 14 cL.fU))) (N bO.iH.ib.bo 61 cq.f8 (ck pd.aC (d2 g5.aI.pm.bm)) (ng kV.a0.aj.cR.aX.aC 11 cN.eW 135 c7.ex 74 cN.eH (pM gG.aj.cR.ja 4 dq.p7 64 dq.gm H 60 dq.fq))))) (az j7.dJ 11 z2.gv 1 z2.f8 2 z2.fz (bc ci.eV (eg l9.b8 71 an px.h8 1 z8.p4 2 z8.p3 (im oJ.nT (iL re.nS.aD 176 b7 bF.ja.ae bE.ja.ae 63 ds.ex 26 ds.fL) (dd dF.b6 aA 9 cO.fD)) (fh oK.aS.S e_ 74 ca mq.bH 115 bN ak.ni.jd 29 cA.gn e_ (lf (wE rI.a0 48 dX 125 iq dV 14 dM.fP)))) (N va.hU.bo 548 cP.gl (ej jp.eb.bu.aD 59 sk bF bE 63 dj.eY 26 dj.eS (kf ov.cd.bQ e_ 78 ch aU.aC 17 dT.eu e_ 113 bv bd.pU.cJ)) (en tE.bl.bH (bk b1.wq.gY)))) (mi o1.gR.iI 103 z6.gL e_ 46 z4.er b1 46 z6.eS e_ 94 nX k9 (N q7.iH.ib.bz 63 dn.f5 (J j.sy.aI.db 116 dy.er (al e_.e0.fr.aX)) (od m1.aS 11 cN.e1 91 bN hj.sl.bI 76 ca kO.bl 72 tE.bl (fW jX))) (N aE.HV.eC.db 487 cB.p6 (m5 nH.bu (dc jl.i2)) (de h9.cJ.kY.ib.fr (fb cD hI e_)))))))
def DF : ab dp:=(qs gF.bV 24 Gc 78 Fz 26 F3 41 FU (hS gs.b6.cQ 27 G8 54 G9 50 Gl (aR k6.bP (cb s5.b2.ag 130 z3.ex z3.fL z3.gg 1 z3.eY (lE h3.pl.aj 23 z7.eY 119 z7.eS 93 z7.e1 aw (gA s8.aj 61 lF aA aB dD 107 nW bq (lf (qp uF.e0.ae.b2.ae 122 wF L 77 wc K 73)) (fb cF mD b1)) (ej n8.iI.aj 211 hC bj.ae br.ae 279 da.fm 275 da.gH (iR iu.aS.g6.aX 185 ap gX.d6 113 dL.fq 109 dL.gb))) (bS ul.aF (J aw.ia.hM.gT 82 c9.fu (fJ k0.vz.aI)) (e9 tu.b8.bw 175 cS.p1 cS.p0 17 cI.e7 82 cI.f6 (bM iA.eP.bg 52 iB aE.kB K.kB L.kB 227 cT.ft)))) (aJ m8.jq.S 88 z5.eB 85 z5.fT 29 z5.fA (mV nG.gR.bw 113 c4 s6 tU 17 z9.gm 97 an np.i9 (J rH.hM.gT 82 cV.f8 (d2 kS.bl.pm.bm)) (gV g9.ae.aj 73 c7.fo 157 dI.e1 136 c7.fU (nA il.gZ 49 dM.p5 dM.p4 50 rR X 46 ad))) (aJ ro.cQ 55 xw 93 xD 89 cG.er (mR oL.eb.iF 4 dP.fo 114 hJ aE.eP 17 da.e1 (aT lW.ag.dm 11 c6.p1 1 c6.p0 2 dl.e7)) (j4 H.e0.aI.bu (aG bK.bu.iG))))) (c3 bq (N fY.aO.bP.dh 59 z4.eB (nd (uT kj.cd.ae.aC 11 z8.f9 111 nY oZ 80 pw dZ 76 eM) (nd (zT qi.aj 23 ct.f9 102 ct.p9 76 ct.ga) (fJ k9.mv.aI) (ac rs.bz 84 d1.eB)) (hX kZ.eN.cR.aS 11 cA.fL 74 cN.gj 118 lJ bq (ms kn))) (dR af.bg (ck ao.aF.aC (lf (rP eE sd rh 24 (aM cD dE e_) 65 (aM cF dE e_) e_))) (gW oG.b6.cd.bi.cd.b8.bw 68 ve jw jD 17 c8.fz 121 di.gl bO (bk aY.gY)))) (d3 ad (pQ ao.Do (ng ma.aC 11 dy.ft 85 c9.p1 38 dy.f4 (aG iS.fQ)) (gy ak.pE.eC (aK jX))) (dQ uV.a0 159 cy.ex 71 cP.fi 116 lo 14 cP.eH (ek kZ.eN.cR.b6 114 lJ jN 1 di.gk 2 di.er (iO K.iG.bl.hU.gE.cw 240 ap K.iG.mv.bI)) (fh qY.ag e_ 108 bv kx.aO 1 cN.fN bd 2 cN.fT e_ (ac aY.wk.eV.eV.dK.fy 188 dY.ex)))))) (aR bd.eK (aJ ny.aS.S 135 z1.p6 145 z1.p5 29 z1.p7 (bU kc (aJ s7.cd.ag 67 z8.f8 1 z8.fz 2 z8.gl (dQ o0.S.cQ 135 ct.fo 136 ct.fU 133 cV.fu 130 cV.gO (aG hQ.fQ) (lf (rP l4 wU By 32 (aM cD fB e_) 145 (aM cF fB e_) aP))) (iw oj.ag.bi.ae 90 wB aQ 77 xn k0 73 jZ (bM rL.fj.aF 188 ap iY.mu.av aE.Ga.mu.av aP.iH.mu.av 1 cO.f6))) (dR H.iI (aW jt.bH (ac iQ.bP.dt 334 dl.fu)) (o8 jS.aS.ho 115 cI.gv cI.fq 214 c8.fN 75 cS.p9 j (ac d4.bi.hL.dx 156 cT.gm)))) (nm ah.A7 (cu j3.dm.bw 114 c4 g5.aO gq.aO k6.aO 19 z9.p2 (bA ma.eN 102 cV.fM 17 cV.fx 25 cV.gn (dc b4.zh.vz)) (gz tB.eP.S 141 et bq.bP 92 iK ah.cJ 88 aU.cJ (lf (rP fk iC zG 20 (aM cD kD e_) 25 (aM cF kD e_) aP)))) (az tL.aX 28 cq.gg 50 vu 46 cq.eS (aW aU.iv (ac cX.kB.ib.gE.cw 82 dl.fK)) (fV tb.ia.S 176 c8.p6 85 c0.gK 29 c0.fp (bM eI.cz.gR.ag 77 jc dk nE tW 1 dY.gO))))) (nd (rP qu iC By 28 (aM cD hI e_) 105 (aM cF hI e_) bd) (nd (kH ah) (om nF.aS 11 z9.fo 75 an H.i9 103 c4 bq (qw oQ.bl.aS 4 cB.eY 106 cB.ga 97 dy.eH (lf (qP lU.aS.b2 4 vh 141 lA ah 137 aU)) (dd n3.S aA 159 d9.fC)) (iw os.bm.cf 159 l0 aN 82 v6 X 78 ad (ac oN.bo 305 cU.fU))) (nd (qp wf.cK 98 xC L 56 wK K 52) (aZ (pk lK.eP.aD 135 dj.hH 231 ca qz.bI 71 dj.gL 67 dy.p5 j) (al fY.hL.bH.bH)) (ix rD.Cv.bm (aG af.hK.iG)))) (ef lO.ik.aX 107 wA k0 jZ 56 nX bF 52 bE (bS jU.aF (J au.vz.aI.db 73 dy.fL (aK pT.io)) (aW ut.aD (aK jV))) (nd (lz h9.EZ.FT) (gW m1.bw 83 bN rE.bI rN.bI 17 di.p4 80 ca lT.bl (bC k4.bQ.ag.ho 183 ap cX.sl.hL.bI cl.sl.hL.bI 137 vl cg 133 b3)) (bA tK.q6.dm 11 dI.gj 1 dI.f5 2 dI.hH (g4 gs.a0 42 dY.p4 155 dY.p3 14 dY.p2)))))))
def Dv : ab dp:=(c3 dz.bI (hS mj.jq 4 H3 50 Ic 46 H7 (aR eM.bP (aR pd (bc aU.bu (N d8.i0.bo 66 cy.fL (bk oS.ae.eh) (lf (qG cC))) (aZ (q2 jg.aS.aF.aj 23 da.gk 517 mJ aH.cR 501 m4 497 rD) (ff ph.a0.bP.g6 140 dL.eY 254 dL.p2 1 dL.eS))) (bU L.bu (aW lk.nT (ij m1.fg 99 bN d8.g8 84 ca aY.cY 80 aQ.cY)) (gz Ag.cx.aF.aX 73 ep L.pE.n2 128 iq ar.bg.jd 124 ao.bg.jd (aT lO.bH.bi.b8 52 cU.eH 1 cU.f8 2 cU.fz)))) (d3 aP.cH (o2 l9.S 85 an bt.i9 113 c4 dk 109 e6 (ej k4.cx.ae 188 bN h5.fF d4.fF 69 cV.ev 65 cV.eZ (bC tw.bP.cs 94 bN lk.bl.fF kS.bl.fF 119 ca eQ.cR.bI 115 dz.cR.bI)) (du n3.ia.b2.eV.bg 150 cS.eu au X ad 78 xz aN (e5 dF.dv 50 cO.p4 109 cO.p2 K 105 L))) (hi uI.aI.bg 119 Aq pA 60 pq (aW b1.bi.nT (hT uc.aI.S.S 80 yu ki 165 l0 dk 161 e6)) (J aw.pG.hU.bP.eV.dK.fy 188 c8.p3 (bk nC.gY))))) (dQ j7.dJ 110 z2.eW 15 z2.eH 1 z2.f8 2 z2.fz (bU ld.bQ (om j3.aS 11 z8.fC 120 r6 gf 68 an bt.ce (eg tt.b6.ag 75 xc jN 1 cB.fP 2 cB.gK (fJ jH.mv.aI) (ml e6)) (aZ (ww hQ.ec) (aT mU.dm.dm 11 cO.gn 1 cO.eA 2 cO.f9))) (N jH.iH.ib.bo 57 cG.eY (bA j8.aX.bP 132 dj.eZ 1 dj.fo 2 dj.fU (bM iu.dB.aj 97 hD iZ.cJ iY.cJ mW.cJ 143 dT.fC)) (J ka.aO.bi.hL.dx 156 c8.fE (dc ju)))) (rz gU.aX 122 z6.eu 40 z2.gm ak 36 af (eJ aE.bP.gY (bT aH.rG.aI.hV 199 et aP.aO (mg k8.eb.cQ.aC 11 ds.p3 66 wS aH 172 vc dZ 168 eM)) (aZ (lZ sV.bH.bi.aD 53 c7.fC c7.gv 143 cA.fo aw) (fW hQ))) (fR uV.ec 67 cP.fP 144 cy.fU 1 cP.gK (J bt.xY.r5.eF 174 cA.eH (al af.aX.a0.hK)) (de ak.cx.gY.gD (co aY.bg.eK)))))) (az gF.cz.aS 4 z1.f6 57 z1.fP 53 z1.gK (aR e6.bl (bU H.bP (lj nx.eP.S 95 z8.fp e_ 95 z8.ft e_ 114 zZ e_ 110 z7.ev aP (oq qI.xM (iO aw.bQ.bV.rG.bm.bz 114 dX k9.bl.bg) (la d5.ag 46 d9.p7 d9.p6 d9.p5 1 d9.p4)) (bA ii.b6.dm 11 da.fx 1 da.gn 2 da.eA (lf (sN rL.gR.bg 36 dL.p5 230 ap aE.mv.aI.av 38 dL.p4 192 ki.eC.av)))) (fR uy.cQ 47 c5.gL 109 cG.ft 31 c5.p9 (aZ (lZ ma.a0 106 As c9.eY 103 hJ bt) (cp d5.b2.ae.aj 193 c6.ez c6.fK 78 c6.fN)) (md bd.kl.cR.bg.cR.a0 64 cI.eu 126 iz j5.kv.iH 141 cI.ez (lf (oP k8.aS.ia 4 cU.p1 54 cU.p0 50 cT.ex))))) (lC cF vr fY.bu (nd (q2 rA.ag.aj 23 z9.p6 124 an uN.b0 108 H.bP.b0 104 uj.b0) (J L.cR.bV.fd 159 cV.gH (mb oY.ag.aS 4 cN.fT 114 bv qR.aO 110 tN.aO)) (gV ii.b6.bw 109 c7.fm 269 c0.gn 19 c7.gH (ac iS.bo 783 cU.f9))) (eg sQ.b8 102 wy jH 1 cq.p7 2 cq.p6 (hX ma.aD 35 dP.eA 148 da.f9 71 c9.fx aw (iO my.kB.ib.gE.cw 244 ap my.xM.fF)) (de mq.hK.gD (em nB.a0.cs 197 dY.fi dY.eW 598 dY.fK 594 dY.fN))))) (nd (rP j2 wU By 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (az nM.S.a0 96 z4.p6 119 z4.ga 14 z4.p5 (eg fc.eN.cR.b8.b8 101 an kx.b0 1 z9.ft 2 z9.f4 (o2 tx.aj.ae 78 ep af.aS 62 dX ak.zh 58 af.zh (iL u0.cd.aD 172 b7 bj.ym.ae br.ym.ae 71 ds.eW 67 ds.eH) (dd yO aA 115 d9.fz)) (m5 mY.bu (lf (wE kQ.kl 52 sj 165 zx aE 14 dM.f4)))) (nd (pW ii.aX 58 xn 248 et aH 83 fe 79 wB) (jW pV.dJ.aX.aF.aD 55 dj.gd 168 iB ul.Ej.kB 180 dy.fx aw (bC l8.iI.cz.S 193 jK cg b3 149 mK ah 145 aU)) (J vZ.pG.kY.eF 75 c8.gH (eo hY.S.a0 162 dq.fo 82 zp aE 14 dq.fU)))) (bc b1.fy (gI gs.iI.b2 4 dn.p3 72 fG ox 68 m3 (ej wr.aX 89 xl K L 58 dy.f8 54 wz (ac bt.ni.vC.Eg.fy.bz 82 dT.gK)) (aZ (pk u5.b8.bw 147 c7.hH 232 bN aH.d6 17 c7.gL 81 rV bO) (aT fc.aX.bP 45 cL.f5 1 cL.hH 2 cL.gL))) (N kJ.o6.eD.aI 53 cP.p3 (bT jw.kY.sy.cJ.aO.aO 500 ts cX (aG jH.aC.S.gB)) (ck oN.fQ (lf (yC hR.S 98 dY.gj dY.f5 dY.hH 43 ep))))))))
def DT : ab dp:=(d3 cX (bc aV (az sJ.a0 59 z1.fC 107 z1.gg 14 z1.gv (bS aV.bm (nd (oi m2.kl 98 sf aN 139 AI dV 14 z7.fM) (N j.G7.hM.gT 82 cy.fx (ac b4.zh.jd.eD.kk 221 dI.p8) (fb cD FW bd)) (bD oj.b2.dv 116 sh k0 jZ 77 hJ aY 73 aQ (i7 mZ.bH.g0 186 ap nC.av nH.av 17 dL.gn 96 ey aH.cY))) (nd (sN iT.eb.gR.bg 36 c5.gH 123 fG dN.eC.aD 38 c5.gm 85 bt.rG.bw) (J bK.bm.bV.fd 159 c9.fT (bC sO.e0.cQ 80 pu h5 d4 185 b7 aY.cK 181 aQ.cK)) (J vR.jd.eD.kk 221 cI.f4 (aG d0.aC)))) (nm np (aJ nF.ik 11 z9.fq 1 z9.gb 2 z9.gd (J oB.FH.ib.bo 529 da.f4 (ac lP.r5.iv.bm.dx 164 dr.p3)) (aZ (ry qf.ag 134 lA 1 vh 2 c0.gg) (cp dF.g0 50 cL.fK cL.fN 19 cL.ex))) (nd (qL cZ.eV.bp 86 cq.fE 54 cq.fD 50 cq.gL) (dG aP.fj.cH (aG rH.eK.ce)) (ck e_.aO.fQ (em pc.dJ.b8.bw 589 dY.fA dY.eu 17 dq.eA 204 dq.p3))))) (c3 ox (pL gU.dJ.aj 23 z4.gm 118 z4.fC z4.gv 92 z4.fq (k2 nF.b6 99 c4 jN 1 z8.p9 2 z8.p8 (dQ oL.aX 35 cB.fU 94 cB.fi 62 cB.eW 58 Ah (pM qy.e0.iF 4 dI.fx 191 jK H 17 dr.p9) (dd cZ.b6 aA 9 cO.ft)) (du qh.bi.aD 60 u2 g5 gq k6 190 lm kc (cp tv.bw 43 dM.fo jc 19 dM.fi))) (qw ko.bl.aS 4 cG.p3 60 cG.gv 51 cM.fL (fV Cz.ja.ae 140 dj.ez 323 cA.eS 320 cA.fm (mb rr.cz.aS 4 dT.p6 115 bv uO.aO 111 oX.aO)) (j4 e_.xE.aI.bu (bk bq.gY)))) (d3 L (eJ d8.gY (J bt.cd.aI.db 126 dy.fu (ml uU.cH)) (J aE.kB.aF.eD.kk 66 c7.gd (e5 h3.fg 57 cL.gK 94 rX bF 90 bE))) (nd (qp eI.bu.gR.aX 73 r7 L 246 yv K 242) (gV k4.cx.eN 125 di.gm 133 di.fC 19 di.gv (aT eI.b8.dm.cJ.ag.dm 11 dL.f4 1 dL.fE 2 dL.fD)) (iw oV.S 106 bv bt.aO 79 ch g2 75 kg (lb bj.ib.bg)))))) (eL aE.r5.aF (N bK.bu.dh 269 Fz (bU ke (lj m8.jq.cs 103 z8.er e_ 104 z8.eB e_ 104 kw m4.bI 100 kw sW (aJ ou.e0.b8 51 ct.fK 1 cy.fp 2 ct.fN (d2 rH.vC.bm) (dc ci)) (bA n1.b6 65 cA.f6 1 cA.fP 2 cA.gK (bC mZ.bH.b6.ho 194 ap ar.nj.eK.av ao.nj.eK.av 144 ey dN.aX.cv 140 ie.aX.cv))) (N bE.bu.cw 180 cG.ev (bT jv.vS.hM.bu.dK.fy 122 iB jv.o6.kB (fJ o7.ya.eC)) (ix rN.Cv.bm (bk dZ.gY)))) (N jN.eV.bz 46 z6.e7 (gA qV.it 100 an dO.cQ.ce cj.cQ.ce dS.cQ.ce 124 c4 lR.aO (J e_.eV.gE.bz 552 mJ (co H.AW.bl.ec)) (kN jx.eV.fj.S 158 y6 au X ad 86 da.p1 (ms g7))) (dQ ta.bw 175 cP.p6 416 ct.eH 17 cq.gn 159 cq.eA (aZ (qP ii.aX.b2 4 vp 95 fe hW 91 ld) (h6 oV.S.a0 118 bv oN.aO 109 ch au.ce 14 dl.eY)) (aZ (lL vg.b2.aj.ae.aj.gR.bg 36 c7.gk 111 c8.p2 H 38 c7.er 73 vj qc) (lc gr.gC.iF 11 dY.fE 118 dY.fD 273 dY.eB 17 dY.fu))))) (aJ i3.b8 49 z3.gK 1 z3.fp 2 z3.ft (bc e3.eV (om qV.jq 11 z9.f8 120 an e_.ae.ce 108 c4 fY.fy (N aP.cH.o6.eD.aI 56 ct.fP (aG gu.fQ) (dd d5.b6 aB 301 FO.e7)) (eG pS.eV.ja.ag 87 mG ah bK ea 1 cS.e7 (ff iA.a0.ag 48 dM.ga 235 cL.gj 1 dM.gj))) (az zC.hL.S 123 cq.fo 96 cM.eY 150 cq.fi (aW q7.aD (lb fY.bg.pG.bg)) (aZ (wI ql.dm.cd.aX.bl.aD 65 c8.gn 230 cN.gL 154 cI.p2 aw) (ff i4.b6.b6.bg 56 cT.fL 450 dY.fo 81 dq.ez)))) (bc Bg (ei oW.ec.aD 47 c5.ev c5.eZ 63 c5.fo 26 c5.fU (bD jx.cf.aj 219 un bF bE 76 pn jt 72 gX (ac qM.bP.dt 334 dl.ft)) (aW dk.nT (bk gu))) (N t5.k7.fy 64 cy.fD (bT bq.bQ.xY.bu.dK.fy 131 je aw.iF.cH (aG bd.h8.S.gB)) (du tr.cx.bi.S 68 ca dO.bl gu uf 83 bN l6.bI (ji fI)))))))
def mC : ab dp:=(pj iA.eP.bg 100 z9 225 dn (hS hY.aj 16 z3 52 z4 48 z5 (pj d5.ag 46 c5 1 cG (im kO (pj il.ec.bQ 19 dj 17 dP EI FE) (hS cZ.ec.aD 38 c0 63 dI 26 di Fw Fb)) (im kW (im dS EY EU) (hS h3.a0.aj 89 c6 98 dl 94 dL Es E4))) (im d8 (nd (Br fa.jq.iF fY 4 cP e_ 17 cy e_) (nd (ws fY) Fc EL) (c3 ob Dz Ds)) (pj i1.ag 44 dy 1 c9 (nd (rP l4 wU By 32 (aM cD fB e_) 145 (aM cF fB e_) bd) DC Dt) (c3 b3 DR DE)))) (az hY.aS 4 z6 52 z7 48 z8 (im fX (im tE (az j0.dK.aX 28 di 44 da 40 cA DV DB) (pj cZ.dK.aF 42 dr 1 ds DO DU)) (az jS.S 178 ct 51 cB 47 cV (nd (xb jN) DJ DA) (bc np DM DQ))) (pj d5.aj 16 cM 50 cq (hS tp 224 dT 121 cS 200 cI (im cj DG DD) (c3 oo DK DS)) (im cg (az fk.ec.aX 40 c8 29 cN 60 c7 DN DF) (nd (yE j2 24 65) Dv DT)))))
def bx : dp→Bool:=sg mC
lemma DY : ay bx EI = true := by decide +kernel
lemma Em : ay bx FE = true := by decide +kernel
lemma D6 : ay bx Fw = true := by decide +kernel
lemma Eh : ay bx Fb = true := by decide +kernel
lemma Ed : ay bx EY = true := by decide +kernel
lemma D3 : ay bx EU = true := by decide +kernel
lemma D8 : ay bx Es = true := by decide +kernel
lemma D0 : ay bx E4 = true := by decide +kernel
lemma Eb : ay bx Fc = true := by decide +kernel
lemma D5 : ay bx EL = true := by decide +kernel
lemma Dl : ay bx Dz = true := by decide +kernel
lemma Di : ay bx Ds = true := by decide +kernel
lemma C6 : ay bx DC = true := by decide +kernel
lemma Dh : ay bx Dt = true := by decide +kernel
lemma Dg : ay bx DR = true := by decide +kernel
lemma CW : ay bx DE = true := by decide +kernel
lemma CL : ay bx DV = true := by decide +kernel
lemma Dd : ay bx DB = true := by decide +kernel
lemma C7 : ay bx DO = true := by decide +kernel
lemma Df : ay bx DU = true := by decide +kernel
lemma C8 : ay bx DJ = true := by decide +kernel
lemma De : ay bx DA = true := by decide +kernel
lemma CU : ay bx DM = true := by decide +kernel
lemma CJ : ay bx DQ = true := by decide +kernel
lemma CY : ay bx DG = true := by decide +kernel
lemma C0 : ay bx DD = true := by decide +kernel
lemma Dc : ay bx DK = true := by decide +kernel
lemma C3 : ay bx DS = true := by decide +kernel
lemma C1 : ay bx DN = true := by decide +kernel
lemma Dj : ay bx DF = true := by decide +kernel
lemma CS : ay bx Dv = true := by decide +kernel
lemma Dk : ay bx DT = true := by decide +kernel
lemma ew (x:dp) {l r : ab dp}
    (hx : bx x = true) (hl : ay bx l = true) (hr : ay bx r = true) :
    ay bx (nd x l r) = true := by
  change (bx x&&ay bx l&&ay bx r) = true
  rw [hx,hl,hr]; rfl
lemma A0 : ay (sg mC) mC = true :=
  (ew (oI iA.eP.bg 100 z9 225 dn) (by decide +kernel) (ew (m0 hY.aj 16 z3 52 z4 48 z5) (by decide +kernel) (ew (oI d5.ag 46 c5 1 cG) (by decide +kernel) (ew (km kO) (by decide +kernel) (ew (oI il.ec.bQ 19 dj 17 dP) (by decide +kernel) DY Em) (ew (m0 cZ.ec.aD 38 c0 63 dI 26 di) (by decide +kernel) D6 Eh)) (ew (km kW) (by decide +kernel) (ew (km dS) (by decide +kernel) Ed D3) (ew (m0 h3.a0.aj 89 c6 98 dl 94 dL) (by decide +kernel) D8 D0))) (ew (km d8) (by decide +kernel) (ew (Br fa.jq.iF fY 4 cP e_ 17 cy e_) (by decide +kernel) (ew (ws fY) (by decide +kernel) Eb D5) (ew (q1 ob) (by decide +kernel) Dl Di)) (ew (oI i1.ag 44 dy 1 c9) (by decide +kernel) (ew (rP l4 wU By 32 (aM cD fB e_) 145 (aM cF fB e_) bd) (by decide +kernel) C6 Dh) (ew (q1 b3) (by decide +kernel) Dg CW)))) (ew (og hY.aS 4 z6 52 z7 48 z8) (by decide +kernel) (ew (km fX) (by decide +kernel) (ew (km tE) (by decide +kernel) (ew (og j0.dK.aX 28 di 44 da 40 cA) (by decide +kernel) CL Dd) (ew (oI cZ.dK.aF 42 dr 1 ds) (by decide +kernel) C7 Df)) (ew (og jS.S 178 ct 51 cB 47 cV) (by decide +kernel) (ew (xb jN) (by decide +kernel) C8 De) (ew (AO np) (by decide +kernel) CU CJ))) (ew (oI d5.aj 16 cM 50 cq) (by decide +kernel) (ew (m0 tp 224 dT 121 cS 200 cI) (by decide +kernel) (ew (km cj) (by decide +kernel) CY C0) (ew (q1 oo) (by decide +kernel) Dc C3)) (ew (km cg) (by decide +kernel) (ew (og fk.ec.aX 40 c8 29 cN 60 c7) (by decide +kernel) C1 Dj) (ew (yE j2 24 65) (by decide +kernel) CS Dk)))))
def u4 (idx:Pos) (q w : List Bool) : Bool :=
  match ig mC idx with
  | none => false
  | some x =>
    let y:=fw x
    let z:=hG q .qB w
    CK y.state z.state&&lp y.front z.front&&lp y.past z.past
lemma am (idx:Pos) (q w : List Bool)
    (h : u4 idx q w = true) (r:ai) :
    cE (BL (bf default (be q)) (be w+>r)) lr := by
  unfold u4 at h
  rcases hx : ig mC idx with _ | x
  · rw [hx] at h; contradiction
  · rw [hx] at h
    dsimp only at h
    simp only [Bool.and_eq_true,zY,oF] at h
    rcases h with ⟨⟨hs,hf⟩,hp⟩
    have heq : fw x = hG q .qB w := by
      rcases h1 : fw x with ⟨p1,f1,s1⟩
      rcases h2 : hG q .qB w with ⟨p2,f2,s2⟩
      rw [h1,h2] at hs hf hp
      dsimp only at hs hf hp
      subst hs hf hp
      rfl
    have hs_g:=Bm mC A0 idx x hx r
    rw [heq,pF] at hs_g
    exact hs_g
lemma A4 (d:cm) (us : List W) :
    cn d us = bf default (be ([false]++bW d++bG us)) := by
  unfold cn
  simp [yh]
lemma xW : r9 := by
  intro d a b c r
  rw [A4 d [a,b,c]]
  cases d <;> cases a <;> cases b <;> cases c
  · exact ⟨am d1.fK ([false]++bW cD++bG kD) aA (by decide +kernel) r,am d1.fN ([false]++bW cD++bG kD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.ex ([false]++bW cD++bG f7) aA (by decide +kernel) r,am d1.fL ([false]++bW cD++bG f7) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gg ([false]++bW cD++bG nQ) aA (by decide +kernel) r,am d1.eY ([false]++bW cD++bG nQ) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.eS ([false]++bW cD++bG vY) aA (by decide +kernel) r,am d1.fm ([false]++bW cD++bG vY) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gH ([false]++bW cD++bG dE) aA (by decide +kernel) r,am d1.gm ([false]++bW cD++bG dE) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fC ([false]++bW cD++bG hI) aA (by decide +kernel) r,am d1.gv ([false]++bW cD++bG hI) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fq ([false]++bW cD++bG mD) aA (by decide +kernel) r,am d1.gb ([false]++bW cD++bG mD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fM ([false]++bW cD++bG fB) aA (by decide +kernel) r,am d1.fx ([false]++bW cD++bG fB) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.eA ([false]++bW cF++bG kD) aA (by decide +kernel) r,am d1.f9 ([false]++bW cF++bG kD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.ga ([false]++bW cF++bG f7) aA (by decide +kernel) r,am d1.gj ([false]++bW cF++bG f7) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.f5 ([false]++bW cF++bG nQ) aA (by decide +kernel) r,am d1.hH ([false]++bW cF++bG nQ) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gL ([false]++bW cF++bG vY) aA (by decide +kernel) r,am d1.p9 ([false]++bW cF++bG vY) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p8 ([false]++bW cF++bG dE) aA (by decide +kernel) r,am d1.p7 ([false]++bW cF++bG dE) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p6 ([false]++bW cF++bG hI) aA (by decide +kernel) r,am d1.p5 ([false]++bW cF++bG hI) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p4 ([false]++bW cF++bG mD) aA (by decide +kernel) r,am d1.p3 ([false]++bW cF++bG mD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p1 ([false]++bW cF++bG fB) aA (by decide +kernel) r,am d1.p0 ([false]++bW cF++bG fB) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  BusyBeaver.Excursion.does_not_halt_of_advances CZ
    ⟨.CD, [.UA, .UT, .UT], _, by decide, rfl⟩ (zb xW)

end BusyBeaver.M_1RB1RF_1RC1RA_1LD0LA_HHH0LE_0LF1LE_0RA0LC
