/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB1RF_1LC0LF_---0LD_0LE1LD_0RF0LB_1RA1RE` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB1RF_1LC0LF_---0LD_0LE1LD_0RF0LB_1RA1RE`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RF_1LC0LF_HHH0LD_0LE1LD_0RF0LB_1RA1RE

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB1RF_1LC0LF_---0LD_0LE1LD_0RF0LB_1RA1RE`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 2, 0 => none
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 4, Stmt.write 1 Dir.right)

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
abbrev tm:=target_tm
@[simp] lemma sq (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config:=rfl
@[simp] lemma n8 (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config:=rfl
@[simp] lemma sm (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : ℕ) :
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
    rw [Nat.add_succ,sm,ih,Option.bind_assoc]
    simp_rw [sm]
lemma qT {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c : Cfg Γ Λ) (n:Nat) :
    multiStep M c (n + 1) = (step M c).bind (fun c' => multiStep M c' n) := by
  rw [Nat.add_comm n 1,qC,n8]
lemma qH {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m:Nat)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) :
    c₁ [M]⊢^{n + m} c₃ := by
  rw [qC,h₁]; simp [h₂]
lemma mm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} (c : Cfg Γ Λ) : c [M]⊢* c:=⟨0,rfl⟩
lemma sr {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
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
lemma sp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  ee h₁ (V h₂)
@[simp] lemma oQ : (0 : Fin 2)>>default = default := by
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
lemma xV (b : Fin 2) : b = 0∨b = 1 := by
  rcases b with ⟨_ | ⟨_ | n⟩,hlt⟩
  · left; rfl
  · right; rfl
  · omega
lemma dW (r:ai) : (∃ r',r = [0]+>r')∨(∃ r',r = [1]+>r') := by
  have h : r.head>>r.tail = r:=Turing.ListBlank.cons_head_tail r
  rcases xV r.head with h0 | h1
  · left; refine ⟨r.tail,?_⟩; rw [append_cons,append_nil,← h0,h]
  · right; refine ⟨r.tail,?_⟩; rw [append_cons,append_nil,← h1,h]
def bf (l:ai) (w : List gQ) : ai:=w.reverse+>l
def FR (l r:ai) : aL:=l {{F}}> r
def DL (l r:ai) : aL:=l <{{D}} r
def FL (l r:ai) : aL:=l <{{F}} r
def BL (l r:ai) : aL:=l <{{B}} r
def CE (r:ai) : aL:=default {{E}}> ([0,0]+>r)
def wL : List gQ:=[1,1,0]
def wX : List gQ:=[1,1,0,1,1,0]
def wY : List gQ:=[1,1,1,1]
def wa : List gQ:=[1,1,1,0,1,0]
def wb : List gQ:=[1,0,1,0]
@[simp] lemma Hm (l:ai) : bf l [] = l:=rfl
lemma df (l:ai) (u v : List gQ) : bf l (u++v) = bf (bf l u) v := by
  simp [bf,List.reverse_append,append_assoc]
structure pu where
  past : List gQ
  front : List gQ
  state : Fin 6
  left_head : Bool
deriving DecidableEq
def pu.toBC (x:pu) : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6) :=
  match x.left_head with
  | true => ⟨x.front, x.past, x.state, .left⟩
  | false => ⟨x.past, x.front, x.state, .right⟩
def pu.ofBC (x : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6)) : pu :=
  match x.sgn with
  | .left => ⟨x.r, x.l, x.s, true⟩
  | .right => ⟨x.l, x.r, x.s, false⟩
lemma pu_toBC_ofBC (x : BusyBeaver.Longitudinal.BoundedConfig.BCfg gQ (Fin 6)) :
    (pu.ofBC x).toBC = x := by
  rcases x with ⟨l, r, s, _ | _⟩ <;> rfl
def go (x:pu) (l r:ai) : aL :=
  BusyBeaver.Longitudinal.BoundedConfig.toCfg x.toBC l r
def qi (x:pu) : Option pu :=
  (BusyBeaver.Longitudinal.BoundedConfig.step tm x.toBC).map pu.ofBC
lemma x4 {x y : pu} (h : qi x = some y) (l r:ai) :
    (go x l r) [tm]⊢ (go y l r) := by
  rcases Option.map_eq_some_iff.mp h with ⟨b, hb, rfl⟩
  simpa only [go, pu_toBC_ofBC] using
    BusyBeaver.Longitudinal.BoundedConfig.step_spec tm x.toBC hb l r
def v4 : Nat→pu→Option pu
  | 0,x => some x
  | n + 1,x =>
    match qi x with
    | none => none
    | some z => v4 n z
lemma yH {n : Nat} {x y : pu} (h : v4 n x = some y) (l r:ai) :
    (go x l r) [tm]⊢^{n} (go y l r) := by
  induction n generalizing x with
  | zero => injection h with hy; subst hy; rfl
  | succ n ih =>
    unfold v4 at h
    rcases hs : qi x with _ | z
    · rw [hs] at h; contradiction
    · rw [hs] at h
      rw [Nat.add_comm n 1]
      exact qH tm _ _ _ 1 n (qO tm _ _ (x4 hs l r)) (ih h)
lemma U (n:Nat) (x y:pu) (h : v4 (n + 1) x = some y) (l r:ai) :
    (go x l r) [tm]⊢⁺ (go y l r) :=
  ⟨n + 1,Nat.succ_pos n,yH h l r⟩
lemma r1 (l r:ai) : (FR l ([0,0,0]+>r)) [tm]⊢⁺ (DL l ([1,0,1]+>r)) :=
  U 4 ⟨[],[0,0,0],F,false⟩ ⟨[],[1,0,1],D,true⟩ (by decide) l r
lemma r3 (l r:ai) : (FR l ([0,0,1]+>r)) [tm]⊢⁺ (FR (bf l wL) r) :=
  U 4 ⟨[],[0,0,1],F,false⟩ ⟨wL.reverse,[],F,false⟩ (by decide) l r
lemma xA (l r:ai) : (FR l ([0,1]+>r)) [tm]⊢⁺ (FR (bf l [1,1]) r) :=
  U 1 ⟨[],[0,1],F,false⟩ ⟨[1,1],[],F,false⟩ (by decide) l r
lemma u8 (l r:ai) : (FR l ([1,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) r) :=
  U 1 ⟨[],[1,0],F,false⟩ ⟨[0,1],[],F,false⟩ (by decide) l r
lemma vn (l r:ai) : (FR l ([1,1]+>r)) [tm]⊢⁺ (FL l ([0,0]+>r)) :=
  U 2 ⟨[],[1,1],F,false⟩ ⟨[],[0,0],F,true⟩ (by decide) l r
lemma An (l r:ai) : (DL (bf l [1]) r) [tm]⊢⁺ (DL l ([1]+>r)) :=
  U 0 ⟨[1],[],D,true⟩ ⟨[],[1],D,true⟩ (by decide) l r
lemma xE (l r:ai) : (DL (bf l [1,0]) r) [tm]⊢⁺ (BL l ([0,0]+>r)) :=
  U 1 ⟨[0,1],[],D,true⟩ ⟨[],[0,0],B,true⟩ (by decide) l r
lemma EA (l r:ai) : (BL (bf l [1]) ([0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>r)) :=
  U 0 ⟨[1],[0,0],B,true⟩ ⟨[],[0,0,0],F,true⟩ (by decide) l r
lemma xN (l r:ai) : (BL (bf l [1,0]) ([0,0]+>r)) [tm]⊢⁺ (DL l ([0,1,0,0]+>r)) :=
  U 1 ⟨[0,1],[0,0],B,true⟩ ⟨[],[0,1,0,0],D,true⟩ (by decide) l r
lemma EX (l r:ai) : (FL (bf l [1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) ([0]+>r)) :=
  U 1 ⟨[1],[0,0],F,true⟩ ⟨[0,1],[0],F,false⟩ (by decide) l r
lemma xR (l r:ai) : (FL (bf l [1,0]) ([0,0]+>r)) [tm]⊢⁺ (DL (bf l [1]) ([1,0,1]+>r)) :=
  U 4 ⟨[0,1],[0,0],F,true⟩ ⟨[1],[1,0,1],D,true⟩ (by decide) l r
abbrev d7 (c:aL) (n:Nat) : Prop :=
  BusyBeaver.Excursion.HaltsIn tm c n
abbrev cE (c:aL) (P : aL→Prop) : Prop :=
  BusyBeaver.Excursion.Leads tm c P
abbrev fl (c:aL) (P : aL→Prop) : Prop :=
  BusyBeaver.Excursion.Advances tm c P
lemma uF {c d : aL} {n : Nat} (hr : c [tm]⊢* d) (hh : d7 c n) :
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
lemma xZ {c : aL} {P Q : aL→Prop} (h : cE c P) (hinc : ∀ d,P d→Q d) :
    cE c Q :=
  BusyBeaver.Excursion.Leads.mono h hinc
lemma x3 {c : aL} {P : aL→Prop} (h : fl c P) : cE c P :=
  BusyBeaver.Excursion.Advances.to_leads h
lemma cr {c d : aL} {P : aL→Prop} (hr : c [tm]⊢⁺ d) (h : cE d P) :
    fl c P :=
  BusyBeaver.Excursion.Advances.of_stepPlus_leads hr h
lemma cc {c d : aL} {P : aL→Prop} (hr : c [tm]⊢⁺ d) (h : cE d P) :
    cE c P :=
  BusyBeaver.Excursion.Leads.of_stepPlus_leads hr h
lemma su {c : aL} {P Q : aL→Prop} (h1 : fl c P) (h2 : ∀ d,P d→cE d Q) :
    fl c Q :=
  BusyBeaver.Excursion.Advances.trans h1 h2
lemma q2 {P : aL→Prop} (h : ∀ c,P c→fl c P) :
    ∀ n c,P c→¬ d7 c n :=
  BusyBeaver.Excursion.not_haltsIn_of_advances h
inductive Bs where
  | GoRight | FromD | FromF | FromB
def sd (b:Bool) : List gQ:=if b then [1,0] else [1]
def bJ (l:ai) : List Bool→ai
  | [] => l
  | b :: s => bf (bJ l s) (sd b)
def aq (l:ai) (s : List Bool) (e:Bs) (r:ai) : aL :=
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
lemma uo (n:Nat) :
    ∀ (l:ai) (s : List Bool) (e:Bs) (r:ai),
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
              simpa only [aq,← append_assoc] using! r1 (bJ l s) r
            exact el hr (fun m hmn hm => ih m hmn l s .FromD ([1,0,1]+>r) hm) hhalt
          · have hr : (aq l s .GoRight ([0]+>([0]+>([1]+>r)))) [tm]⊢⁺ (aq l (true :: false :: s) .GoRight r) := by
              simpa only [aq,bJ,sd,df,← append_assoc] using! r3 (bJ l s) r
            exact el hr (fun m hmn hm => ih m hmn l (true :: false :: s) .GoRight r hm) hhalt
        · have hr : (aq l s .GoRight ([0]+>([1]+>r))) [tm]⊢⁺ (aq l (false :: false :: s) .GoRight r) := by
            simpa only [aq,bJ,sd,df,← append_assoc] using! xA (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (false :: false :: s) .GoRight r hm) hhalt
      · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
        · have hr : (aq l s .GoRight ([1]+>([0]+>r))) [tm]⊢⁺ (aq l (true :: s) .GoRight r) := by
            simpa only [aq,bJ,sd,df,← append_assoc] using! u8 (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (true :: s) .GoRight r hm) hhalt
        · have hr : (aq l s .GoRight ([1]+>([1]+>r))) [tm]⊢⁺ (aq l s .FromF r) := by
            simpa only [aq,← append_assoc] using! vn (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromF r hm) hhalt
    | FromD =>
      cases s with
      | nil => exact ⟨n,DL l r,le_rfl,.contact_D r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromD r) [tm]⊢⁺ (aq l s .FromD ([1]+>r)) :=
            An (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromD ([1]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromD r) [tm]⊢⁺ (aq l s .FromB r) :=
            xE (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromB r hm) hhalt
    | FromF =>
      cases s with
      | nil => exact ⟨n,FL l ([0,0]+>r),le_rfl,.contact_F r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromF r) [tm]⊢⁺ (aq l (true :: s) .GoRight ([0]+>r)) :=
            EX (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (true :: s) .GoRight ([0]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromF r) [tm]⊢⁺ (aq l (false :: s) .FromD ([1,0,1]+>r)) :=
            xR (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l (false :: s) .FromD ([1,0,1]+>r) hm) hhalt
    | FromB =>
      cases s with
      | nil => exact ⟨n,BL l ([0,0]+>r),le_rfl,.contact_B r,hhalt⟩
      | cons b s =>
        cases b
        · have hr : (aq l (false :: s) .FromB r) [tm]⊢⁺ (aq l s .FromF ([0]+>r)) := by
            simpa only [aq,← append_assoc] using! EA (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromF ([0]+>r) hm) hhalt
        · have hr : (aq l (true :: s) .FromB r) [tm]⊢⁺ (aq l s .FromD ([0,1,0,0]+>r)) :=
            xN (bJ l s) r
          exact el hr (fun m hmn hm => ih m hmn l s .FromD ([0,1,0,0]+>r) hm) hhalt
lemma fv (l r:ai) : cE (FR l r) (ip l) :=
  fun n hn => uo n l [] .GoRight r hn
lemma jC (l:ai) (s : List Bool) (e:Bs) (r:ai) :
    cE (aq l s e r) (ip l) :=
  fun n hn => uo n l s e r hn
lemma pG (l r:ai) : fl (FR l r) (ip l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
      · refine cr ?_ (dg (.contact_D ([1,0,1]+>r)))
        simpa only [← append_assoc] using! r1 l r
      · refine cr ?_ (jC l [true,false] .GoRight r)
        simpa only [aq,bJ,sd,df,← append_assoc] using! r3 l r
    · refine cr ?_ (jC l [false,false] .GoRight r)
      simpa only [aq,bJ,sd,df,← append_assoc] using! xA l r
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · refine cr ?_ (jC l [true] .GoRight r)
      simpa only [aq,bJ,sd,df,← append_assoc] using! u8 l r
    · refine cr ?_ (dg (.contact_F r))
      simpa only [← append_assoc] using! vn l r
inductive gw (l:ai) : aL→Prop where
  | weak_D (r:ai) : gw l (DL l r)
  | weak_F (r:ai) : gw l (FL l ([0,0,0]+>r))
inductive dU (l:ai) : aL→Prop where
  | strong_D (r:ai) : dU l (DL l (wa+>r))
  | strong_F (r:ai) : dU l (FL l ([0,0,0]+>(wa+>r)))
lemma GP (l r:ai) : (DL (bf l wL) r) [tm]⊢⁺ (FL l ([0,0,0]+>r)) :=
  U 2 ⟨wL.reverse,[],D,true⟩ ⟨[],[0,0,0],F,true⟩ (by decide) l r
lemma GZ (l r:ai) : (FL (bf l wL) ([0,0]+>r)) [tm]⊢⁺ (DL l ([1,1,1,0,1]+>r)) :=
  U 6 ⟨wL.reverse,[0,0],F,true⟩ ⟨[],[1,1,1,0,1],D,true⟩ (by decide) l r
lemma GN (l r:ai) : (BL (bf l wL) ([0,0]+>r)) [tm]⊢⁺ (DL l ([1,0,1,0,0]+>r)) :=
  U 2 ⟨wL.reverse,[0,0],B,true⟩ ⟨[],[1,0,1,0,0],D,true⟩ (by decide) l r
lemma Ge (l r:ai) : (DL (bf l [1,1]) r) [tm]⊢⁺ (DL l ([1,1]+>r)) :=
  U 1 ⟨[1,1],[],D,true⟩ ⟨[],[1,1],D,true⟩ (by decide) l r
lemma Gd (l r:ai) : (FL (bf l [1,1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l wL) ([0]+>r)) :=
  U 1 ⟨[1,1],[0,0],F,true⟩ ⟨wL.reverse,[0],F,false⟩ (by decide) l r
lemma Hc (l r:ai) : (BL (bf l [1,1]) ([0,0]+>r)) [tm]⊢⁺ (FR (bf l [1,0]) ([0,0]+>r)) :=
  U 2 ⟨[1,1],[0,0],B,true⟩ ⟨[0,1],[0,0],F,false⟩ (by decide) l r
lemma GV (l r:ai) : (DL (bf l wX) r) [tm]⊢⁺ (DL l (wa+>r)) :=
  U 9 ⟨wX.reverse,[],D,true⟩ ⟨[],wa,D,true⟩ (by decide) l r
lemma Dp (l r:ai) : (FL (bf l wX) ([0,0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>r))) := by
  simpa only [append_assoc] using!
    U 9 ⟨wX.reverse,[0,0,0],F,true⟩ ⟨[],[0,0,0]++wa,F,true⟩ (by decide) l r
lemma rV (l:ai) (c:aL) (h : ip (bf l wL) c) : cE c (gw l) := by
  cases h with
  | contact_D r => exact bn (V (GP l r)) (.weak_F r)
  | contact_F r => exact bn (V (GZ l r)) (.weak_D ([1,1,1,0,1]+>r))
  | contact_B r => exact bn (V (GN l r)) (.weak_D ([1,0,1,0,0]+>r))
lemma yQ (l r:ai) : cE (FR (bf l wL) r) (gw l) :=
  bh (fv (bf l wL) r) (rV l)
def lu (w : List gQ) : Prop :=
  ∀ l c,gw (bf l w) c→cE c (gw l)
lemma Bf : lu wL := by
  intro l c h
  cases h with
  | weak_D r => exact rV l _ (.contact_D r)
  | weak_F r =>
    have hc : ip (bf l wL) (FL (bf l wL) ([0,0]+>([0]+>r))):=.contact_F ([0]+>r)
    simpa only [← append_assoc] using! rV l _ hc
lemma AK : lu [1,1] := by
  intro l c h
  cases h with
  | weak_D r => exact bn (V (Ge l r)) (.weak_D ([1,1]+>r))
  | weak_F r =>
    have hf : (FL (bf l [1,1]) ([0,0,0]+>r)) [tm]⊢⁺ (FR (bf l wL) ([0]+>([0]+>r))) := by
      simpa only [← append_assoc] using! Gd l ([0]+>r)
    exact cc hf (yQ l ([0]+>([0]+>r)))
lemma yP {u v : List gQ} (hu : lu u) (hv : lu v) :
    lu (u++v) := by
  intro l c hc
  rw [df] at hc
  exact bh (hv (bf l u) c hc) (hu l)
inductive b9 where
  | PL | P11
deriving DecidableEq
def xS : b9→List gQ
  | .PL => wL
  | .P11 => [1,1]
def hE : List b9→List gQ
  | [] => []
  | p :: ps => xS p++hE ps
lemma w8 (ps : List b9) : lu (hE ps) := by
  induction ps with
  | nil => intro l c h; exact dg h
  | cons p ps ih =>
    unfold hE
    refine yP ?_ ih
    cases p
    · exact Bf
    · exact AK
lemma DR (l:ai) (c:aL) (h : gw (bf l wX) c) :
    cE c (dU l) := by
  cases h with
  | weak_D r => exact bn (V (GV l r)) (.strong_D r)
  | weak_F r => exact bn (V (Dp l r)) (.strong_F r)
def b5 (ps : List b9) : List gQ :=
  (wX++hE ps)++wL
lemma lI (ps : List b9) (l:ai) (c:aL)
    (h : ip (bf l (b5 ps)) c) : cE c (dU l) := by
  unfold b5 at h
  rw [df,df] at h
  refine bh (rV (bf (bf l wX) (hE ps)) c h) ?_
  intro d hd
  refine bh (w8 ps (bf l wX) d hd) ?_
  intro e he
  exact DR l e he
lemma r7 (ps : List b9) (l r:ai) :
    cE (FR (bf l (b5 ps)) r) (dU l) :=
  bh (fv (bf l (b5 ps)) r) (lI ps l)
inductive dA (l:ai) : aL→Prop where
  | phase_D (r:ai) : dA l (DL l r)
  | phase_F (r:ai) : dA l (FL l ([0,0,0]+>r))
  | phase_B101 (r:ai) : dA l (BL l ([0,0,1,0,1]+>r))
  | phase_B11101 (r:ai) : dA l (BL l ([0,0,1,1,1,0,1]+>r))
lemma xX (l:ai) (c:aL) (h : gw l c) : dA l c := by
  cases h with
  | weak_D r => exact .phase_D r
  | weak_F r => exact .phase_F r
lemma GC (l r:ai) : (DL (bf l ([1,0]++wL)) r) [tm]⊢⁺ (DL l ([1,1,0,1,0]+>r)) :=
  U 8 ⟨(([1,0] : List gQ)++wL).reverse,[],D,true⟩ ⟨[],[1,1,0,1,0],D,true⟩ (by decide) l r
lemma Gy (l r:ai) : (FL (bf l ([1,0]++wL)) ([0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,1,1,0,1]+>r)) :=
  U 8 ⟨(([1,0] : List gQ)++wL).reverse,[0,0],F,true⟩ ⟨[],[0,0,1,1,1,0,1],B,true⟩ (by decide) l r
lemma Gi (l r:ai) : (BL (bf l ([1,0]++wL)) ([0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,0,1,0,0]+>r)) :=
  U 4 ⟨(([1,0] : List gQ)++wL).reverse,[0,0],B,true⟩ ⟨[],[0,0,1,0,1,0,0],B,true⟩ (by decide) l r
lemma Cx (l r:ai) : cE (FR (bf l ([1,0]++wL)) r) (dA l) := by
  refine bh (fv (bf l ([1,0]++wL)) r) ?_
  intro c h
  cases h with
  | contact_D r0 => exact bn (V (GC l r0)) (.phase_D ([1,1,0,1,0]+>r0))
  | contact_F r0 => exact bn (V (Gy l r0)) (.phase_B11101 r0)
  | contact_B r0 =>
    have hp : dA l (BL l ([0,0,1,0,1,0,0]+>r0)) := by
      simpa only [← append_assoc] using! dA.phase_B101 ([0,0]+>r0)
    exact bn (V (Gi l r0)) hp
lemma A1 (l r:ai) : (FR (bf l [1,0]) ([0,0,0]+>r)) [tm]⊢⁺ (BL l ([0,0,1,0,1]+>r)) :=
  U 6 ⟨[0,1],[0,0,0],F,false⟩ ⟨[],[0,0,1,0,1],B,true⟩ (by decide) l r
lemma AL (l r:ai) : (FR (bf l [1,0]) ([0,0,1]+>r)) [tm]⊢⁺ (FR (bf l ([1,0]++wL)) r) :=
  U 4 ⟨[0,1],[0,0,1],F,false⟩ ⟨(([1,0] : List gQ)++wL).reverse,[],F,false⟩ (by decide) l r
lemma Bd (l r:ai) : cE (FR (bf l [1,0]) ([0,0]+>r)) (dA l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR (bf l [1,0]) ([0,0]+>([0]+>r))) [tm]⊢⁺ (BL l ([0,0,1,0,1]+>r)) := by
      simpa only [← append_assoc] using! A1 l r
    exact bn (V hr) (.phase_B101 r)
  · have hr : (FR (bf l [1,0]) ([0,0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l ([1,0]++wL)) r) := by
      simpa only [← append_assoc] using! AL l r
    exact cc hr (Cx l r)
lemma x1 (l r:ai) : cE (FR (bf l [1,1]) r) (dA l) := by
  refine bh (fv (bf l [1,1]) r) ?_
  intro c h
  cases h with
  | contact_D r0 => exact bn (V (Ge l r0)) (.phase_D ([1,1]+>r0))
  | contact_F r0 => exact cc (Gd l r0) (xZ (yQ l ([0]+>r0)) (xX l))
  | contact_B r0 => exact cc (Hc l r0) (Bd l r0)
lemma uK (l r:ai) : cE (FR l ([0]+>r)) (dA l) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
    · have hr : (FR l ([0]+>([0]+>([0]+>r)))) [tm]⊢⁺ (DL l ([1,0,1]+>r)) := by
        simpa only [← append_assoc] using! r1 l r
      exact bn (V hr) (.phase_D ([1,0,1]+>r))
    · have hr : (FR l ([0]+>([0]+>([1]+>r)))) [tm]⊢⁺ (FR (bf l wL) r) := by
        simpa only [← append_assoc] using! r3 l r
      exact cc hr (xZ (yQ l r) (xX l))
  · have hr : (FR l ([0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l [1,1]) r) := by
      simpa only [← append_assoc] using! xA l r
    exact cc hr (x1 l r)
inductive W where
  | UA | UT
deriving DecidableEq
inductive cm where
  | CD | CF
deriving DecidableEq
def y2 : W→List gQ
  | .UA => wa
  | .UT => wY++wa
def yL : W→List gQ
  | .UA => wa
  | .UT => wa++wb
def G1 : W→List gQ
  | .UA => wX
  | .UT => wX++wY
def HD : List W→List gQ
  | [] => []
  | u :: us => y2 u++HD us
def HF : List W→List gQ
  | [] => []
  | u :: us => yL u++HF us
def G : List W→List gQ
  | [] => []
  | u :: us => G1 u++G us
@[simp] lemma B8 (u:W) (us : List W) : HD (u :: us) = y2 u++HD us:=rfl
@[simp] lemma Ct (u:W) (us : List W) : HF (u :: us) = yL u++HF us:=rfl
def lX : cm→List gQ
  | .CD => []
  | .CF => wY
def n9 (d:cm) (us : List W) : List gQ :=
  match d with
  | .CD => HD us
  | .CF => wb++HF us
def hF (d:cm) (us : List W) (r:ai) : aL :=
  CE (n9 d us+>r)
def lr (c:aL) : Prop :=
  ∃ d us r,3 ≤ us.length∧c = hF d us r
def cn (d:cm) (us : List W) : ai :=
  bf default ([0]++lX d++G us)
lemma FQ (us vs : List W) : HD (us++vs) = HD us++HD vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [HD,ih,List.append_assoc]
lemma FY (us vs : List W) : HF (us++vs) = HF us++HF vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [HF,ih,List.append_assoc]
lemma Gk (us vs : List W) : G (us++vs) = G us++G vs := by
  induction us with
  | nil => rfl
  | cons u us ih => simp [G,ih,List.append_assoc]
lemma DW (u:W) (l r:ai) :
    (FR l ([0]+>(y2 u+>r))) [tm]⊢⁺ (FR (bf l (G1 u)) ([0]+>r)) := by
  cases u
  · simpa only [y2,G1,append_assoc] using!
      U 11 ⟨[],[0]++wa,F,false⟩ ⟨wX.reverse,[0],F,false⟩ (by decide) l r
  · simpa only [y2,G1,append_assoc] using!
      U 17 ⟨[],[0]++(wY++wa),F,false⟩ ⟨(wX++wY).reverse,[0],F,false⟩ (by decide) l r
lemma DO (u:W) (l r:ai) :
    (FR l ([0]+>(yL u+>r))) [tm]⊢⁺ (FR (bf l (G1 u)) ([0]+>r)) := by
  cases u
  · simpa only [yL,G1,append_assoc] using!
      U 11 ⟨[],[0]++wa,F,false⟩ ⟨wX.reverse,[0],F,false⟩ (by decide) l r
  · simpa only [yL,G1,append_assoc] using!
      U 15 ⟨[],[0]++(wa++wb),F,false⟩ ⟨(wX++wY).reverse,[0],F,false⟩ (by decide) l r
lemma FK (l r:ai) :
    (FR l ([0]+>(wb+>r))) [tm]⊢⁺ (FR (bf l wY) ([0]+>r)) := by
  simpa only [append_assoc] using!
    U 3 ⟨[],[0]++wb,F,false⟩ ⟨wY.reverse,[0],F,false⟩ (by decide) l r
lemma EG (us : List W) (l r:ai) :
    (FR l ([0]+>(HD us+>r))) [tm]⊢* (FR (bf l (G us)) ([0]+>r)) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold HD G
    rw [append_assoc,df]
    exact V (ee (DW u l (HD us+>r)) (ih (bf l (G1 u)) r))
lemma E6 (us : List W) (l r:ai) :
    (FR l ([0]+>(HF us+>r))) [tm]⊢* (FR (bf l (G us)) ([0]+>r)) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold HF G
    rw [append_assoc,df]
    exact V (ee (DO u l (HF us+>r)) (ih (bf l (G1 u)) r))
lemma E7 (r:ai) : (CE r) [tm]⊢⁺ (FR (bf default [0]) ([0]+>r)) := by
  refine ⟨1,by decide,?_⟩
  simp only [CE,FR,bf,List.reverse_singleton,n8,step,append_cons,append_nil,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5,tm,target_tm,E,F,Option.map,Tape.write,Tape.move]
lemma ta (d:cm) (us : List W) (r:ai) :
    (hF d us r) [tm]⊢⁺ (FR (cn d us) ([0]+>r)) := by
  unfold hF
  refine ee (E7 (n9 d us+>r)) ?_
  cases d
  · unfold n9 cn lX
    simp only [List.append_nil,df]
    exact EG us (bf default [0]) r
  · unfold n9 cn lX
    rw [append_assoc,df,df]
    exact V (ee (FK (bf default [0]) (HF us+>r)) (E6 us (bf (bf default [0]) wY) r))
lemma G7 (u:W) (l r:ai) :
    (DL (bf l (G1 u)) (wa+>r)) [tm]⊢⁺ (DL l (wa+>(y2 u+>r))) := by
  cases u
  · simpa only [G1,y2,append_assoc] using!
      U 9 ⟨wX.reverse,wa,D,true⟩ ⟨[],wa++wa,D,true⟩ (by decide) l r
  · simpa only [G1,y2,append_assoc] using!
      U 13 ⟨(wX++wY).reverse,wa,D,true⟩ ⟨[],wa++(wY++wa),D,true⟩ (by decide) l r
lemma G5 (u:W) (l r:ai) :
    (FL (bf l (G1 u)) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>(yL u+>r)))) := by
  cases u
  · simpa only [G1,yL,append_assoc] using!
      U 9 ⟨wX.reverse,[0,0,0]++wa,F,true⟩ ⟨[],[0,0,0]++wa++wa,F,true⟩ (by decide) l r
  · simpa only [G1,yL,append_assoc] using!
      U 49 ⟨(wX++wY).reverse,[0,0,0]++wa,F,true⟩ ⟨[],[0,0,0]++wa++(wa++wb),F,true⟩ (by decide) l r
lemma H8 (us : List W) (l r:ai) :
    (DL (bf l (G us)) (wa+>r)) [tm]⊢* (DL l (wa+>(HD us+>r))) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold G HD
    rw [df,append_assoc]
    exact sr (ih (bf l (G1 u)) r) (V (G7 u l (HD us+>r)))
lemma HJ (us : List W) (l r:ai) :
    (FL (bf l (G us)) ([0,0,0]+>(wa+>r))) [tm]⊢* (FL l ([0,0,0]+>(wa+>(HF us+>r)))) := by
  induction us generalizing l r with
  | nil => exact mm _
  | cons u us ih =>
    unfold G HF
    rw [df,append_assoc]
    exact sr (ih (bf l (G1 u)) r) (V (G5 u l (HF us+>r)))
lemma HC (l r:ai) : (DL (bf l wY) (wa+>r)) [tm]⊢⁺ (DL l (wY+>(wa+>r))) := by
  simpa only [append_assoc] using!
    U 3 ⟨wY.reverse,wa,D,true⟩ ⟨[],wY++wa,D,true⟩ (by decide) l r
lemma H0 (l r:ai) :
    (FL (bf l wY) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>(wb+>r)))) := by
  simpa only [append_assoc] using!
    U 39 ⟨wY.reverse,[0,0,0]++wa,F,true⟩ ⟨[],[0,0,0]++wa++wb,F,true⟩ (by decide) l r
lemma BV (r:ai) : (DL (bf default [0]) r) [tm]⊢⁺ (CE r) := by
  refine ⟨1,by decide,?_⟩
  simp only [DL,CE,bf,List.reverse_singleton,n8,step,append_cons,append_nil,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5,tm,target_tm,D,E,Option.map,Tape.write,Tape.move]
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
def AD : Nat→f3→Option f3
  | 0,x => some x
  | n + 1,x =>
    match mr x with
    | none => none
    | some y => AD n y
lemma vQ {x y : f3} (h : mr x = some y) (r:ai) :
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
lemma C3 {n : Nat} {x y : f3} (h : AD n x = some y) (r:ai) :
    (dw x r) [tm]⊢^{n} (dw y r) := by
  induction n generalizing x with
  | zero => injection h with hy; subst hy; rfl
  | succ n ih =>
    unfold AD at h
    rcases hs : mr x with _ | z
    · rw [hs] at h; contradiction
    · rw [hs] at h
      rw [Nat.add_comm n 1]
      exact qH tm _ _ _ 1 n (qO tm _ _ (vQ hs r)) (ih h)
lemma vD {n : Nat} {x y : f3} (h : AD (n + 1) x = some y) (r:ai) :
    (dw x r) [tm]⊢⁺ (dw y r) :=
  ⟨n + 1,Nat.succ_pos n,C3 h r⟩
def r2 : List gQ→List gQ
  | [] => []
  | b :: ls =>
    match r2 ls with
    | [] => if b==0 then [] else [b]
    | ys => b :: ys
lemma xo (ls : List gQ) : r2 ls+>default = ls+>default := by
  induction ls with
  | nil => rfl
  | cons b ls ih =>
    unfold r2
    rcases h : r2 ls with _ | ⟨y,ys⟩
    · rw [h,append_nil] at ih
      rcases xV b with rfl | rfl
      · change []+>default = (0 :: ls)+>default
        rw [append_nil,append_cons,← ih,oQ]
      · change [1]+>default = (1 :: ls)+>default
        rw [append_cons,append_nil,append_cons,← ih]
    · change (b :: y :: ys)+>default = (b :: ls)+>default
      rw [append_cons,← h,ih,append_cons]
def kR (x y:f3) : Bool :=
  r2 x.past==r2 y.past&&x.front==y.front&&x.state==y.state
lemma kE {x y : f3} (h : kR x y = true) (r:ai) :
    dw x r = dw y r := by
  unfold kR at h
  simp only [Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨⟨hp,hf⟩,hs⟩
  unfold dw
  rw [hf,hs,← xo x.past,← xo y.past,hp]
def vG (n:Nat) (x y:f3) : Bool :=
  match AD n x with
  | some z => kR z y
  | none => false
lemma kC (n:Nat) (x y:f3) (h : vG (n + 1) x y = true) (r:ai) :
    (dw x r) [tm]⊢⁺ (dw y r) := by
  unfold vG at h
  rcases hr : AD (n + 1) x with _ | z
  · rw [hr] at h; contradiction
  · rw [hr] at h
    rw [← kE h r]
    exact vD hr r
lemma Cc (r:ai) : (FL (bf default [0]) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (CE (wb+>(wa+>r))) := by
  have h:=kC 5 ⟨[],0 :: ([0,0,0]++wa),F⟩ ⟨[],[0,0]++wb++wa,E⟩ (by decide) r
  simpa only [dw,FL,CE,bf,List.reverse_singleton,append_cons,append_nil,append_assoc,
    Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons] using h
def gJ : cm→W
  | .CD => .UA
  | .CF => .UT
lemma Ec (d:cm) (us : List W) (r:ai) :
    (DL (cn d us) (wa+>r)) [tm]⊢⁺ (hF .CD (gJ d :: us) r) := by
  unfold cn
  rw [df]
  refine kT (H8 us (bf default ([0]++lX d)) r) ?_
  cases d
  · unfold lX gJ hF n9
    simp only [B8,y2,List.append_nil,append_assoc]
    exact BV (wa+>(HD us+>r))
  · unfold lX gJ hF n9
    rw [df]
    refine sp (HC (bf default [0]) (HD us+>r)) ?_
    simp only [B8,y2,append_assoc]
    exact BV (wY+>(wa+>(HD us+>r)))
lemma D2 (d:cm) (us : List W) (r:ai) :
    (FL (cn d us) ([0,0,0]+>(wa+>r))) [tm]⊢⁺ (hF .CF (gJ d :: us) r) := by
  unfold cn
  rw [df]
  refine kT (HJ us (bf default ([0]++lX d)) r) ?_
  cases d
  · unfold lX gJ hF n9
    simp only [Ct,yL,List.append_nil,append_assoc]
    exact Cc (HF us+>r)
  · unfold lX gJ hF n9
    rw [df]
    refine sp (H0 (bf default [0]) (HF us+>r)) ?_
    simp only [Ct,yL,append_assoc]
    exact Cc (wb+>(HF us+>r))
def A5 (d:cm) (us : List W) (c:aL) : Prop :=
  ∃ d' r,c = hF d' (gJ d :: us) r
lemma hN (d:cm) (us : List W) (c:aL)
    (h : dU (cn d us) c) : cE c (A5 d us) := by
  cases h with
  | strong_D r =>
    exact bn (V (Ec d us r)) ⟨.CD,r,rfl⟩
  | strong_F r =>
    exact bn (V (D2 d us r)) ⟨.CF,r,rfl⟩
lemma i8 (d:cm) (us : List W) (c:aL)
    (hlen : 2 ≤ us.length) (h : A5 d us c) : lr c := by
  rcases h with ⟨d',r,rfl⟩
  exact ⟨d',gJ d :: us,r,by simp; omega,rfl⟩
def Cl : List gQ:=[1,1,1,1,1,1,1,1,1]
def wh : List gQ:=[1,1,1,1,1,1,0,1,0]
lemma CB (l r:ai) :
    (FR l ([0]+>(Cl+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r)) := by
  simpa only [b5,hE,append_assoc] using!
    U 20 ⟨[],[0]++Cl,F,false⟩ ⟨((wX++[])++wL).reverse,[0],F,false⟩ (by decide) l r
lemma DU (l r:ai) :
    (FR l ([0]+>(wh+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r)) := by
  simpa only [b5,hE,append_assoc] using!
    U 18 ⟨[],[0]++wh,F,false⟩ ⟨((wX++[])++wL).reverse,[0],F,false⟩ (by decide) l r
lemma yZ (d:cm) (us : List W) (r:ai) (t : List gQ)
    (hlen : 2 ≤ us.length)
    (ht : ∀ l r,(FR l ([0]+>(t+>r))) [tm]⊢⁺ (FR (bf l (b5 [])) ([0]+>r))) :
    cE (hF d us (t+>r)) lr := by
  refine cc (ta d us (t+>r)) ?_
  refine cc (ht (cn d us) r) ?_
  refine bh (r7 [] (cn d us) ([0]+>r)) ?_
  intro c hc
  refine bh (hN d us c hc) ?_
  intro e he
  exact dg (i8 d us e hlen he)
lemma x6 (d:cm) (us : List W) (r:ai) (hlen : 2 ≤ us.length) :
    cE (hF d us (Cl+>r)) lr :=
  yZ d us r Cl hlen CB
lemma y6 (d:cm) (us : List W) (r:ai) (hlen : 2 ≤ us.length) :
    cE (hF d us (wh+>r)) lr :=
  yZ d us r wh hlen DU
lemma xG (r:ai) :
    (hF .CF [.UA,.UT] ((wY++wa++wa)+>r)) [tm]⊢⁺
    (FR (bf (cn .CF [.UA,.UT]) (b5 [.P11,.P11])) ([0,0,1,0]+>r)) := by
  have h:=kC 57
    ⟨[],[0,0]++n9 .CF [.UA,.UT]++(wY++wa++wa),E⟩
    ⟨([0]++lX .CF++G [.UA,.UT]++b5 [.P11,.P11]).reverse,[0,0,1,0],F⟩
    (by decide) r
  simpa only [dw,hF,CE,FR,cn,df,bf,append_assoc] using! h
lemma Ah (r:ai) :
    cE (hF .CF [.UA,.UT] ((wY++wa++wa)+>r)) lr := by
  refine cc (xG r) ?_
  refine bh (r7 [.P11,.P11] (cn .CF [.UA,.UT]) ([0,0,1,0]+>r)) ?_
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
def vM : List (bR × List gQ) :=
  [(.RD,[]),(.RF,[0,0]),(.RB,[0,0])]
def pM : List (bR × List gQ) :=
  [(.RD,[1,0,1]),(.RD,[1,1,1,0,1]),(.RD,[1,0,1,0,0]),(.RF,[0,0,0])]
def zU : List (bR × List gQ) :=
  [(.RD,[1,1,0,1]),(.RD,[0,1,0,0]),(.RF,[0,0]),(.RB,[0,0])]
def xK : List (bR × List gQ):=[(.RD,[]),(.RF,[0,0])]
def Bc : List (bR × List gQ):=[(.RD,[]),(.RB,[0,0])]
def Cm : List (bR × List gQ):=[(.RF,[0,0])]
def ic (l:ai) (es : List (bR × List gQ)) (c:aL) : Prop :=
  ∃ e p r,(e,p) ∈ es∧c = jY e l (p+>r)
lemma v5 (l:ai) (c:aL) (h : ip l c) : ic l vM c := by
  cases h with
  | contact_D r => exact ⟨.RD,[],r,by decide,rfl⟩
  | contact_F r => exact ⟨.RF,[0,0],r,by decide,rfl⟩
  | contact_B r => exact ⟨.RB,[0,0],r,by decide,rfl⟩
lemma Bn (l r:ai) : fl (FR l r) (ic l vM) :=
  su (pG l r) (fun c h => dg (v5 l c h))
lemma CL (l:ai) (c:aL) (h : ip (bf l wL) c) :
    cE c (ic l pM) := by
  cases h with
  | contact_D r =>
    exact bn (V (GP l r)) ⟨.RF,[0,0,0],r,by decide,rfl⟩
  | contact_F r =>
    exact bn (V (GZ l r)) ⟨.RD,[1,1,1,0,1],r,by decide,rfl⟩
  | contact_B r =>
    exact bn (V (GN l r)) ⟨.RD,[1,0,1,0,0],r,by decide,rfl⟩
lemma xU (l r:ai) : fl (FR l ([0,0]+>r)) (ic l pM) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR l ([0,0]+>([0]+>r))) [tm]⊢⁺ (DL l ([1,0,1]+>r)) := by
      simpa only [← append_assoc] using! r1 l r
    exact cr hr (dg ⟨.RD,[1,0,1],r,by decide,rfl⟩)
  · have hr : (FR l ([0,0]+>([1]+>r))) [tm]⊢⁺ (FR (bf l wL) r) := by
      simpa only [← append_assoc] using! r3 l r
    exact cr hr (bh (fv (bf l wL) r) (CL l))
lemma Bh (l:ai) (c:aL) (h : ip (bf l [1,0]) c) :
    cE c (ic l zU) := by
  cases h with
  | contact_D r =>
    exact bn (V (xE l r)) ⟨.RB,[0,0],r,by decide,rfl⟩
  | contact_F r =>
    refine cc (xR l r) ?_
    refine cc (An l ([1,0,1]+>r)) ?_
    exact dg ⟨.RD,[1,1,0,1],r,by decide,by simp [jY,← append_assoc]⟩
  | contact_B r =>
    exact bn (V (xN l r)) ⟨.RD,[0,1,0,0],r,by decide,rfl⟩
lemma CP (l r:ai) : fl (FR l ([1]+>r)) (ic l zU) := by
  rcases dW r with ⟨r,rfl⟩ | ⟨r,rfl⟩
  · have hr : (FR l ([1]+>([0]+>r))) [tm]⊢⁺ (FR (bf l [1,0]) r) := by
      simpa only [← append_assoc] using! u8 l r
    exact cr hr (bh (fv (bf l [1,0]) r) (Bh l))
  · have hr : (FR l ([1]+>([1]+>r))) [tm]⊢⁺ (FL l ([0,0]+>r)) := by
      simpa only [← append_assoc] using! vn l r
    exact cr hr (dg ⟨.RF,[0,0],r,by decide,rfl⟩)
lemma x0 (l:ai) (c:aL) (h : ic l pM c) :
    ic l xK c := by
  rcases h with ⟨e,p,r,hin,rfl⟩
  simp only [pM,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at hin
  rcases hin with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨.RD,[],[1,0,1]+>r,by decide,rfl⟩
  · exact ⟨.RD,[],[1,1,1,0,1]+>r,by decide,rfl⟩
  · exact ⟨.RD,[],[1,0,1,0,0]+>r,by decide,rfl⟩
  · exact ⟨.RF,[0,0],[0]+>r,by decide,by simp [jY,← append_assoc]⟩
lemma xe (l r:ai) : fl (FR l ([0,0]+>r)) (ic l xK) :=
  su (xU l r) (fun c h => dg (x0 l c h))
lemma wW (l r:ai) : fl (FR l ([1,0]+>r)) (ic l Bc) := by
  refine cr (u8 l r) ?_
  refine bh (fv (bf l [1,0]) r) ?_
  intro c h
  cases h with
  | contact_D r0 =>
    exact bn (V (xE l r0)) ⟨.RB,[0,0],r0,by decide,rfl⟩
  | contact_F r0 =>
    refine cc (xR l r0) ?_
    exact bn (V (An l ([1,0,1]+>r0)))
      ⟨.RD,[],[1,1,0,1]+>r0,by decide,by simp [jY,← append_assoc]⟩
  | contact_B r0 =>
    exact bn (V (xN l r0))
      ⟨.RD,[],[0,1,0,0]+>r0,by decide,rfl⟩
lemma wo (l r:ai) : fl (FR l ([1,1]+>r)) (ic l Cm) :=
  cr (vn l r) (dg ⟨.RF,[0,0],r,by decide,rfl⟩)
inductive ax where
  | qA | qB | qC | qD | qE | qF
deriving DecidableEq
def x8 (b:Bool) : gQ:=if b then 1 else 0
def be (bs : List Bool) : List gQ:=bs.map x8
@[simp] lemma yW : be [] = []:=rfl
@[simp] lemma m7 (b:Bool) (bs : List Bool) : be (b :: bs) = x8 b :: be bs:=rfl
@[simp] lemma jF (xs ys : List Bool) : be (xs++ys) = be xs++be ys := by simp [be]
@[simp] lemma sM (xs : List Bool) : be xs.reverse = (be xs).reverse := by simp [be]
def BB : ax→Fin 6
  | .qA => A | .qB => B | .qC => C | .qD => D | .qE => E | .qF => F
structure R where
  past : List Bool
  front : List Bool
  state : ax
deriving DecidableEq
def sy (x:R) : f3 :=
  ⟨be x.past,be x.front,BB x.state⟩
def dC (x:R) (r:ai) : aL:=dw (sy x) r
def vX (x:R) : Option R :=
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
def AN (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih [] (false :: true :: bs) q
def zA (a:Bool) (ls : List Bool) (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih ls (a :: true :: bs) q
noncomputable def sS (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    AN
    zA
    past q ih bs
def Ac (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih [] (false :: false :: bs) q
def ya (a:Bool) (ls : List Bool) (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (q:ax) (ih : List Bool→List Bool→ax→Option R) (bs : List Bool) : Option R :=
  ih ls (a :: false :: bs) q
noncomputable def ln (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    Ac
    ya
    past q ih bs
def ll (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  ih (true :: past) bs q
def xz (q:ax) (ih : List Bool→List Bool→ax→Option R) (past bs : List Bool) : Option R :=
  ih (false :: past) bs q
def CH (_ : List Bool→List Bool→ax→Option R) (_ _ : List Bool) : Option R :=
  none
noncomputable def xq (state:ax) : (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  ax.rec (motive:=fun _ => (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    (ll .qB)
    (sS .qC)
    CH
    (ln .qE)
    (xz .qF)
    (ll .qA)
    state
noncomputable def xH (state:ax) : (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  ax.rec (motive:=fun _ => (List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    (ll .qF)
    (ln .qF)
    (ln .qD)
    (sS .qD)
    (ln .qB)
    (ll .qE)
    state
noncomputable def B2 (b:Bool) : ax→(List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R :=
  Bool.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→List Bool→Option R)
    xq
    xH
    b
noncomputable def Am (b:Bool) (bs : List Bool)
    (_ : ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    (state:ax) (ih : List Bool→List Bool→ax→Option R) (past : List Bool) : Option R :=
  B2 b state ih past bs
def AT (_:ax) (_ : List Bool→List Bool→ax→Option R) (_ : List Bool) : Option R :=
  none
noncomputable def lN (ih : List Bool→List Bool→ax→Option R)
    (past front : List Bool) (state:ax) : Option R :=
  List.rec (motive:=fun _ => ax→(List Bool→List Bool→ax→Option R)→List Bool→Option R)
    AT
    Am
    front state ih past
def Ab (past front : List Bool) (state:ax) : Option R :=
  some ⟨past,front,state⟩
noncomputable def zN (_:Nat) (ih : List Bool→List Bool→ax→Option R) : List Bool→List Bool→ax→Option R :=
  lN ih
noncomputable def l7 (n:Nat) : List Bool→List Bool→ax→Option R :=
  Nat.rec (motive:=fun _ => List Bool→List Bool→ax→Option R)
    Ab
    zN
    n
noncomputable def xC (n:Nat) (x:R) : Option R :=
  R.rec (motive:=fun _ => Option R) (l7 n) x
noncomputable def Ag (n:Nat) (x:R) : Option R :=
  R.rec (motive:=fun _ => Option R) (lN (l7 n)) x
lemma y8 (x:R) : (vX x).map sy = mr (sy x) := by
  rcases x with ⟨_ | ⟨a,ls⟩,_ | ⟨_ | _,bs⟩,_ | _ | _ | _ | _ | _⟩ <;> rfl
lemma wq (ih : List Bool→List Bool→ax→Option R)
    (past front : List Bool) (state:ax) :
    lN ih past front state =
      match vX ⟨past,front,state⟩ with
      | none => none
      | some y => ih y.past y.front y.state := by
  rcases past with _ | ⟨a,ls⟩ <;> rcases front with _ | ⟨_ | _,bs⟩ <;> cases state <;> rfl
lemma vJ (n:Nat) (past front : List Bool) (state:ax) :
    (l7 n past front state).map sy = AD n (sy ⟨past,front,state⟩) := by
  induction n generalizing past front state with
  | zero => rfl
  | succ n ih =>
    change (lN (l7 n) past front state).map sy = AD (n + 1) (sy ⟨past,front,state⟩)
    rw [wq]
    unfold AD
    rw [← y8 ⟨past,front,state⟩]
    rcases vX ⟨past,front,state⟩ with _ | ⟨p',f',s'⟩ <;> simp [ih]
lemma AP (n:Nat) (x:R) : (xC n x).map sy = AD n (sy x) :=
  vJ n x.past x.front x.state
def Cz : ax→ax→Bool
  | .qA,.qA | .qB,.qB | .qC,.qC | .qD,.qD | .qE,.qE | .qF,.qF => true
  | _,_ => false
lemma zQ (x y:ax) : Cz x y = true↔x = y := by
  cases x <;> cases y <;> decide
def sw (_:Bool) (_ : List Bool) (_:Bool) : Bool:=false
noncomputable def zK (ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => Bool) true sw ys
noncomputable def zC (b:Bool) (ih : List Bool→Bool) (bs : List Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool) (ih bs) false b
noncomputable def yX (b:Bool) (ih : List Bool→Bool) (bs : List Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool) false (ih bs) b
noncomputable def ri (b:Bool) (bs : List Bool) (_ : (List Bool→Bool)→Bool→Bool)
    (ih : List Bool→Bool) (a:Bool) : Bool :=
  Bool.rec (motive:=fun _ => Bool→(List Bool→Bool)→List Bool→Bool) zC yX a b ih bs
def sl (_ : List Bool→Bool) (_:Bool) : Bool:=false
noncomputable def pr (a:Bool) (_ : List Bool) (ih : List Bool→Bool) (ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => (List Bool→Bool)→Bool→Bool)
    sl
    ri
    ys ih a
noncomputable def lp (xs ys : List Bool) : Bool :=
  List.rec (motive:=fun _ => List Bool→Bool)
    zK
    pr
    xs ys
lemma oE (xs ys : List Bool) : lp xs ys = true↔xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys <;> simp [lp,zK,sw]
  | cons a as ih =>
    cases ys with
    | nil => simp [lp,pr,sl]
    | cons b bs =>
      change pr a as (lp as) (b :: bs) = true↔a :: as = b :: bs
      cases a <;> cases b <;> simp [pr,ri,zC,yX,ih]
def mz (b:Bool) (_ : List Bool) (ih : List Bool) : List Bool :=
  match ih with
  | [] => if b then [true] else []
  | ys => b :: ys
noncomputable def mO (ls : List Bool) : List Bool :=
  List.rec (motive:=fun _ => List Bool) [] mz ls
lemma so (ls : List Bool) : be (mO ls) = r2 (be ls) := by
  induction ls with
  | nil => rfl
  | cons b ls ih =>
    change be (mz b ls (mO ls)) = r2 (x8 b :: be ls)
    unfold mz r2
    rw [← ih]
    rcases mO ls with _ | ⟨y,ys⟩ <;> cases b <;> rfl
noncomputable def mn (xp xf : List Bool) (xs:ax) (yp yf : List Bool) (ys:ax) : Bool :=
  Cz xs ys&&lp xf yf&&(lp xp yp||lp (mO xp) (mO yp))
noncomputable def xk (y:R) (xp xf : List Bool) (xs:ax) : Bool :=
  R.rec (motive:=fun _ => Bool) (mn xp xf xs) y
noncomputable def tQ (x y:R) : Bool :=
  R.rec (motive:=fun _ => Bool) (xk y) x
lemma wm {x y : R} (h : tQ x y = true) (r:ai) :
    dC x r = dC y r := by
  rcases x with ⟨xp,xf,xs⟩
  rcases y with ⟨yp,yf,ys⟩
  change mn xp xf xs yp yf ys = true at h
  unfold mn at h
  simp only [Bool.and_eq_true,Bool.or_eq_true,zQ,oE] at h
  rcases h with ⟨⟨hs,hf⟩,hp | hp⟩
  · apply kE _ r
    unfold kR sy
    dsimp only
    rw [hp,hf,hs]
    simp
  · apply kE _ r
    unfold kR sy
    dsimp only
    rw [← so xp,← so yp,hp,hf,hs]
    simp
def A6 (_:R) : Bool:=false
noncomputable def A2 (z y:R) : Bool:=tQ z y
noncomputable def og (n:Nat) (x y:R) : Bool :=
  Option.rec (motive:=fun _ => R→Bool) A6 A2 (xC n x) y
noncomputable def eO (n:Nat) (x y:R) : Bool :=
  Option.rec (motive:=fun _ => R→Bool) A6 A2 (Ag n x) y
lemma gi (n:Nat) (x y:R)
    (h : og (n + 1) x y = true) (r:ai) :
    (dC x r) [tm]⊢⁺ (dC y r) := by
  unfold og at h
  rcases hr : xC (n + 1) x with _ | z
  · rw [hr] at h; contradiction
  · rw [hr] at h
    change tQ z y = true at h
    rw [← wm h r]
    have hrun : AD (n + 1) (sy x) = some (sy z) := by
      rw [← AP (n + 1) x,hr]; rfl
    exact vD hrun r
def bL : List Bool:=[true,true,false]
def bX : List Bool:=[true,true,false,true,true,false]
def bY : List Bool:=[true,true,true,true]
def ba : List Bool:=[true,true,true,false,true,false]
def bb : List Bool:=[true,false,true,false]
def EH : List Bool:=[true,true,true,true,true,true,true,true,true]
def B0 : List Bool:=[true,true,true,true,true,true,false,true,false]
def F8 : W→List Bool
  | .UA => ba
  | .UT => bY++ba
def F9 : W→List Bool
  | .UA => ba
  | .UT => ba++bb
def Ho : W→List Bool
  | .UA => bX
  | .UT => bX++bY
def FC : List W→List Bool
  | [] => []
  | u :: us => F8 u++FC us
def F2 : List W→List Bool
  | [] => []
  | u :: us => F9 u++F2 us
def bG : List W→List Bool
  | [] => []
  | u :: us => Ho u++bG us
def bW : cm→List Bool
  | .CD => []
  | .CF => bY
def xP (d:cm) (us : List W) : List Bool :=
  match d with
  | .CD => FC us
  | .CF => bb++F2 us
def wc : b9→List Bool
  | .PL => bL
  | .P11 => [true,true]
def mI : List b9→List Bool
  | [] => []
  | p :: ps => wc p++mI ps
def rS (ps : List b9) : List Bool :=
  (bX++mI ps)++bL
def Do (b:Bool) : List Bool :=
  if b then [true,false] else [true]
def nT : List Bool→List Bool
  | [] => []
  | b :: s => nT s++Do b
@[simp] lemma GF : be bL = wL:=rfl
@[simp] lemma GI : be bX = wX:=rfl
@[simp] lemma DP : be bY = wY:=rfl
@[simp] lemma Bb : be ba = wa:=rfl
@[simp] lemma GH : be bb = wb:=rfl
@[simp] lemma Bl : be EH = Cl:=rfl
@[simp] lemma zW : be B0 = wh:=rfl
@[simp] lemma Gt (us : List W) : be (FC us) = HD us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [FC,HD,F8,y2,← ih]
@[simp] lemma Gm (us : List W) : be (F2 us) = HF us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [F2,HF,F9,yL,← ih]
@[simp] lemma GG (us : List W) : be (bG us) = G us := by
  induction us with
  | nil => rfl
  | cons u us ih => cases u <;> simp [bG,G,Ho,G1,← ih]
@[simp] lemma Fr (d:cm) : be (bW d) = lX d := by
  cases d <;> rfl
@[simp] lemma nZ (d:cm) (us : List W) : be (xP d us) = n9 d us := by
  cases d <;> simp [xP,n9]
@[simp] lemma Cw (ps : List b9) : be (mI ps) = hE ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [mI,hE,wc,xS,x8,← ih]
@[simp] lemma vW (ps : List b9) : be (rS ps) = b5 ps := by
  simp [rS,b5]
def lw : List Bool→List gQ
  | [] => []
  | b :: s => lw s++sd b
lemma xM (l:ai) (s : List Bool) :
    bJ l s = bf l (lw s) := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    unfold bJ lw
    rw [ih,df]
lemma xJ (base : List gQ) (ps : List b9) (s : List Bool) (r:ai) :
    cE (FR (bf default ((base++b5 ps)++lw s)) r)
      (dU (bf default base)) := by
  rw [df,df,← xM]
  exact bh (jC (bf (bf default base) (b5 ps)) s .GoRight r)
    (lI ps (bf default base))
@[simp] lemma vV (s : List Bool) : be (nT s) = lw s := by
  induction s with
  | nil => rfl
  | cons b s ih => cases b <;> simp [nT,lw,Do,sd,x8,← ih]
def pC (q w : List Bool) : R:=⟨q.reverse,w,.qF⟩
def hG (q : List Bool) (s:ax) (w : List Bool) : R :=
  match q.reverse with
  | [] => ⟨[],false :: w,s⟩
  | a :: ls => ⟨ls,a :: w,s⟩
def jJ (qr w : List Bool) : R:=⟨qr,w,.qF⟩
def gh (qr : List Bool) (s:ax) (w : List Bool) : R :=
  match qr with
  | [] => ⟨[],false :: w,s⟩
  | a :: ls => ⟨ls,a :: w,s⟩
def xB (w : List Bool) : R:=⟨[],false :: false :: w,.qE⟩
lemma zG (q w : List Bool) (r:ai) :
    dC (pC q w) r = FR (bf default (be q)) (be w+>r) := by
  unfold dC pC sy dw FR bf
  simp [BB]
lemma pE (q : List Bool) (s:ax) (w : List Bool) (r:ai) :
    dC (hG q s w) r = ((bf default (be q)) <{{BB s}} (be w+>r)) := by
  unfold dC hG sy bf dw
  dsimp only
  rw [← sM]
  rcases q.reverse with _ | ⟨a,ls⟩ <;>
    simp only [yW,m7,x8,Bool.false_eq_true,↓reduceIte,
      append_cons,append_nil,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5]
lemma vP (qr w : List Bool) (r:ai) :
    dC (jJ qr w) r = FR (bf default (be qr.reverse)) (be w+>r) := by
  unfold dC jJ sy dw FR bf
  simp [BB]
lemma w1 (qr : List Bool) (s:ax) (w : List Bool) (r:ai) :
    dC (gh qr s w) r = ((bf default (be qr.reverse)) <{{BB s}} (be w+>r)) := by
  unfold dC gh sy bf dw
  dsimp only
  rw [← sM,List.reverse_reverse]
  rcases qr with _ | ⟨a,ls⟩ <;>
    simp only [yW,m7,x8,Bool.false_eq_true,↓reduceIte,
      append_cons,append_nil,Turing.ListBlank.head_cons,Turing.ListBlank.tail_cons,kX,k5]
lemma C1 (w : List Bool) (r:ai) :
    dC (xB w) r = CE (be w+>r):=rfl
inductive fZ where
  | Recovered (d:cm) (us : List W) (tail : List Bool)
  | NineGain (d:cm) (us : List W) (tail : List Bool)
  | SixGain (d:cm) (us : List W) (tail : List Bool)
  | YaaGain (tail : List Bool)
deriving DecidableEq
def j6 : fZ→List Bool
  | .Recovered d us tail => xP d us++tail
  | .NineGain d us tail => xP d us++EH++tail
  | .SixGain d us tail => xP d us++B0++tail
  | .YaaGain tail => xP .CF [.UA,.UT]++bY++ba++ba++tail
def f0 (t:fZ) : R:=xB (j6 t)
def jj : fZ→Bool
  | .Recovered _ us _ => decide (3 ≤ us.length)
  | .NineGain _ us _ => decide (2 ≤ us.length)
  | .SixGain _ us _ => decide (2 ≤ us.length)
  | .YaaGain _ => true
lemma nO (t:fZ) (h : jj t = true) (r:ai) :
    cE (dC (f0 t) r) lr := by
  unfold f0
  rw [C1]
  cases t with
  | Recovered d us tail =>
    have hlen : 3 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,nZ,append_assoc]
    exact dg ⟨d,us,be tail+>r,hlen,rfl⟩
  | NineGain d us tail =>
    have hlen : 2 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,nZ,Bl,append_assoc]
    exact x6 d us (be tail+>r) hlen
  | SixGain d us tail =>
    have hlen : 2 ≤ us.length:=of_decide_eq_true h
    unfold j6
    simp only [jF,nZ,zW,append_assoc]
    exact y6 d us (be tail+>r) hlen
  | YaaGain tail =>
    unfold j6
    simp only [jF,nZ,DP,Bb]
    have heq : (n9 .CF [.UA,.UT]++wY++wa++wa++be tail)+>r =
        n9 .CF [.UA,.UT]+>((wY++wa++wa)+>(be tail+>r)) := by
      simp only [append_assoc]
    rw [heq]
    exact Ah (be tail+>r)
structure mB where
  guard_base : List Bool
  guard_pieces : List b9
  guard_stack : List Bool
  guard_D_steps : Nat
  guard_D_terminal : fZ
  guard_F_steps : Nat
  guard_F_terminal : fZ
deriving DecidableEq
def ur (g:mB) : List Bool :=
  (g.guard_base++rS g.guard_pieces)++nT g.guard_stack
noncomputable def nU (g:mB) : Bool :=
  jj g.guard_D_terminal &&
  jj g.guard_F_terminal &&
  eO g.guard_D_steps (hG g.guard_base .qD ba) (f0 g.guard_D_terminal) &&
  eO g.guard_F_steps (hG g.guard_base .qF ([false,false,false]++ba)) (f0 g.guard_F_terminal)
lemma Bm (g:mB) (h : nU g = true) (r:ai) :
    cE (FR (bf default (be (ur g))) r) lr := by
  unfold nU at h
  simp only [Bool.and_eq_true] at h
  rcases h with ⟨⟨⟨hd,hf⟩,nd⟩,nf⟩
  unfold ur
  simp only [jF,vW,vV]
  refine bh (xJ (be g.guard_base) g.guard_pieces g.guard_stack r) ?_
  intro c hc
  cases hc with
  | strong_D r0 =>
    have hnat:=gi g.guard_D_steps (hG g.guard_base .qD ba) (f0 g.guard_D_terminal) nd r0
    rw [pE] at hnat
    dsimp only [BB,Bb] at hnat
    exact cc hnat (nO g.guard_D_terminal hd r0)
  | strong_F r0 =>
    have hnat:=gi g.guard_F_steps (hG g.guard_base .qF ([false,false,false]++ba)) (f0 g.guard_F_terminal) nf r0
    rw [pE] at hnat
    have h000 : be ([false,false,false]++ba)+>r0 = [0,0,0]+>(wa+>r0) := by
      simp [append_assoc,x8]
    dsimp only [BB] at hnat
    rw [h000] at hnat
    exact cc hnat (nO g.guard_F_terminal hf r0)
inductive k1 where
  | AllCases | Cases00 | Cases1 | Coarse00 | Coarse10 | Coarse11
deriving DecidableEq
def iW : k1→List (bR × List gQ)
  | .AllCases => vM
  | .Cases00 => pM
  | .Cases1 => zU
  | .Coarse00 => xK
  | .Coarse10 => Bc
  | .Coarse11 => Cm
def sn : k1→List (bR × List Bool)
  | .AllCases => [(.RD,[]),(.RF,[false,false]),(.RB,[false,false])]
  | .Cases00 => [(.RD,[true,false,true]),(.RD,[true,true,true,false,true]),(.RD,[true,false,true,false,false]),(.RF,[false,false,false])]
  | .Cases1 => [(.RD,[true,true,false,true]),(.RD,[false,true,false,false]),(.RF,[false,false]),(.RB,[false,false])]
  | .Coarse00 => [(.RD,[]),(.RF,[false,false])]
  | .Coarse10 => [(.RD,[]),(.RB,[false,false])]
  | .Coarse11 => [(.RF,[false,false])]
lemma vC (s:k1) :
    (sn s).map (fun e => (e.1,be e.2)) = iW s := by
  cases s <;> rfl
noncomputable def kq (s:k1) (w : List Bool) : Bool :=
  match s with
  | .AllCases => true
  | .Cases00 => lp w [false,false]
  | .Cases1 => lp w [true]
  | .Coarse00 => lp (w.take 2) [false,false]
  | .Coarse10 => lp (w.take 2) [true,false]
  | .Coarse11 => lp (w.take 2) [true,true]
lemma zc (s:k1) (w : List Bool) (h : kq s w = true) (l r:ai) :
    fl (FR l (be w+>r)) (ic l (iW s)) := by
  cases s with
  | AllCases => exact Bn l (be w+>r)
  | Cases00 =>
    unfold kq at h; rw [oE] at h; subst h
    exact xU l r
  | Cases1 =>
    unfold kq at h; rw [oE] at h; subst h
    exact CP l r
  | Coarse00 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,x8,Bool.false_eq_true,↓reduceIte,← append_assoc] using! xe l (be w'+>r)
  | Coarse10 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,x8,Bool.false_eq_true,↓reduceIte,← append_assoc] using! wW l (be w'+>r)
  | Coarse11 =>
    rcases w with _ | ⟨_ | _,_ | ⟨_ | _,w'⟩⟩ <;> try contradiction
    simpa only [iW,m7,x8,Bool.false_eq_true,↓reduceIte,← append_assoc] using! wo l (be w'+>r)
def ny : bR→ax
  | .RD => .qD
  | .RF => .qF
  | .RB => .qB
def Gs : bR→Fin 6
  | .RD => D
  | .RF => F
  | .RB => B
@[simp] lemma x5 (s:bR) : BB (ny s) = Gs s := by
  cases s <;> rfl
inductive Pos where
  | Z : Pos
  | O : Pos→Pos
  | E : Pos→Pos
deriving DecidableEq
def Fc : bR→bR→Bool
  | .RD,.RD | .RF,.RF | .RB,.RB => true
  | _,_ => false
lemma CC (x y:bR) : Fc x y = true↔x = y := by
  cases x <;> cases y <;> decide
structure px where
  state : bR
  pref : List Bool
  steps : Nat
  target : Pos
  prep : List Bool
deriving DecidableEq
noncomputable def ss (e : bR × List Bool) (b:px) : Bool :=
  Fc e.1 b.state&&lp e.2 b.pref
noncomputable def yh (s:k1) (bs : List px) : Bool :=
  (sn s).all (fun e => bs.any (ss e))
lemma x9 (s:k1) (bs : List px) (e : bR × List gQ)
    (hc : yh s bs = true) (hin : e ∈ iW s) :
    ∃ b ∈ bs,e.1 = b.state∧e.2 = be b.pref := by
  rw [← vC s,List.mem_map] at hin
  rcases hin with ⟨⟨st,p⟩,hp,rfl⟩
  unfold yh at hc
  have h1:=List.all_eq_true.mp hc (st,p) hp
  rcases List.any_eq_true.mp h1 with ⟨b,hb,hm⟩
  unfold ss at hm
  simp only [Bool.and_eq_true,CC,oE] at hm
  exact ⟨b,hb,hm.1,by rw [hm.2]⟩
inductive dp where
  | rEnd (t:fZ)
  | rProt (gc:mB) (w : List Bool)
  | rNat (fin:R) (steps:Nat) (target:Pos) (prep : List Bool)
  | rRet (qr w : List Bool) (s:k1) (bs : List px)
def FV (t:fZ) : R:=f0 t
def Cu (gc:mB) (w : List Bool) : R:=pC (ur gc) w
def FT (fin:R) (_:Nat) (_:Pos) (_ : List Bool) : R:=fin
def Dz (qr w : List Bool) (_:k1) (_ : List px) : R:=jJ qr w
noncomputable def fw (r:dp) : R :=
  dp.rec (motive:=fun _ => R) FV Cu FT Dz r
def D4 (p : List Bool) (xp xf : List Bool) (xs:ax) : R :=
  ⟨xp,xf++p,xs⟩
noncomputable def jE (p : List Bool) (x:R) : R :=
  R.rec (motive:=fun _ => R) (D4 p) x
lemma nQ (p : List Bool) (x:R) (r:ai) :
    dC (jE p x) r = dC x (be p+>r) := by
  rcases x with ⟨xp,xf,xs⟩
  change dC ⟨xp,xf++p,xs⟩ r = dC ⟨xp,xf,xs⟩ (be p+>r)
  unfold dC dw sy
  simp only [jF,append_assoc]
inductive ab (α : Type) where
  | empty : ab α
  | node : Option α→ab α→ab α→ab α
def za (v : Option α) (_ _ : ab α) (_ _ : Option α) : Option α:=v
noncomputable def B6 (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => Option α) none za t
def vE (_ : ab α→Option α) : Option α:=none
def zk (_ : Option α) (l _ : ab α) (_ _ : (ab α→Option α)→Option α) (ih : ab α→Option α) : Option α:=ih l
def AE (_ : Option α) (_ r : ab α) (_ _ : (ab α→Option α)→Option α) (ih : ab α→Option α) : Option α:=ih r
noncomputable def BJ (_:Pos) (ih : ab α→Option α) (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => (ab α→Option α)→Option α) vE zk t ih
noncomputable def BZ (_:Pos) (ih : ab α→Option α) (t : ab α) : Option α :=
  ab.rec (motive:=fun _ => (ab α→Option α)→Option α) vE AE t ih
noncomputable def ig (t : ab α) (p:Pos) : Option α :=
  Pos.rec (motive:=fun _ => ab α→Option α)
    B6
    BJ
    BZ
    p t
def n6 (_ : α→Bool) (ihl ihr:Bool) : Bool:=ihl&&ihr
def oz (x : α) (p : α→Bool) (ihl ihr:Bool) : Bool:=p x&&ihl&&ihr
noncomputable def me (p : α→Bool) (v : Option α) (_ _ : ab α) (ihl ihr:Bool) : Bool :=
  Option.rec (motive:=fun _ => (α→Bool)→Bool→Bool→Bool)
    n6
    oz
    v p ihl ihr
noncomputable def ay (p : α→Bool) (t : ab α) : Bool :=
  ab.rec (motive:=fun _ => Bool) true (me p) t
lemma AR {p : α→Bool} {t : ab α} {i : Pos} {x : α}
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
        cases v <;> simp only [me,n6,oz,Bool.and_eq_true] at hall <;> tauto
      exact ih hl hget
  | E i ih =>
    cases t with
    | empty => contradiction
    | node v l r =>
      change ig r i = some x at hget
      change me p v l r (ay p l) (ay p r) = true at hall
      have hr : ay p r = true := by
        cases v <;> simp only [me,n6,oz,Bool.and_eq_true] at hall <;> tauto
      exact ih hr hget
def vH (_:Nat) (_:R) (_ : List Bool) : Bool:=false
noncomputable def vT (y:dp) (steps:Nat) (fin:R) (prep : List Bool) : Bool :=
  eO steps fin (jE prep (fw y))
noncomputable def mN (opt_y : Option dp) (steps:Nat) (fin:R) (prep : List Bool) : Bool :=
  Option.rec (motive:=fun _ => Nat→R→List Bool→Bool)
    vH
    vT
    opt_y steps fin prep
noncomputable def D6 (g : ab dp) (qr : List Bool)
    (state:bR) (pref : List Bool) (steps:Nat) (target:Pos) (prep : List Bool) : Bool :=
  mN (ig g target) steps (gh qr (ny state) pref) prep
noncomputable def pB (g : ab dp) (qr : List Bool) (b:px) : Bool :=
  px.rec (motive:=fun _ => Bool) (D6 g qr) b
def F0 (t:fZ) (_ : ab dp) : Bool:=jj t
noncomputable def Ex (gc:mB) (_ : List Bool) (_ : ab dp) : Bool:=nU gc
noncomputable def FD (fin:R) (steps:Nat) (target:Pos) (prep : List Bool) (g : ab dp) : Bool :=
  mN (ig g target) steps fin prep
noncomputable def FH (qr w : List Bool) (s:k1) (bs : List px) (g : ab dp) : Bool :=
  kq s w&&yh s bs&&bs.all (pB g qr)
noncomputable def sf (g : ab dp) (r:dp) : Bool :=
  dp.rec (motive:=fun _ => ab dp→Bool)
    F0 Ex FD FH r g
lemma Be (g : ab dp) (hg : ay (sf g) g = true) :
    ∀ (i:Pos) (x:dp),ig g i = some x→∀ r,cE (dC (fw x) r) lr := by
  intro i x hx r n hn
  induction n using Nat.strong_induction_on generalizing i x r with
  | h n ih =>
    have hchk : sf g x = true:=AR hg hx
    cases x with
    | rEnd t =>
      change jj t = true at hchk
      exact nO t hchk r n hn
    | rProt gc w =>
      change nU gc = true at hchk
      unfold fw Cu at hn
      rw [zG] at hn
      exact Bm gc hchk (be w+>r) n hn
    | rNat fin steps target prep =>
      change mN (ig g target) steps fin prep = true at hchk
      rcases hy : ig g target with _ | y
      · rw [hy] at hchk; contradiction
      · rw [hy] at hchk
        change eO steps fin (jE prep (fw y)) = true at hchk
        have hp:=gi steps fin (jE prep (fw y)) hchk r
        rw [nQ] at hp
        rcases kz hp hn with ⟨m,hmn,hm⟩
        rcases ih m hmn target y hy (be prep+>r) hm with ⟨k,d,hkm,hsafe,hk⟩
        exact ⟨k,d,by omega,hsafe,hk⟩
    | rRet qr w s bs =>
      change (kq s w&&yh s bs&&bs.all (pB g qr)) = true at hchk
      simp only [Bool.and_eq_true] at hchk
      rcases hchk with ⟨⟨hs,hc⟩,hbs⟩
      unfold fw Dz at hn
      rw [vP] at hn
      rcases zc s w hs (bf default (be qr.reverse)) r n hn with ⟨m,c,hmn,hret,hm⟩
      rcases hret with ⟨e,p,r',hin,rfl⟩
      rcases x9 s bs (e,p) hc hin with ⟨b,hb,he,hp⟩
      dsimp only at he hp; subst he hp
      have hbv : pB g qr b = true:=List.all_eq_true.mp hbs b hb
      rcases b with ⟨b_state,b_pref,b_steps,b_target,b_prep⟩
      change mN (ig g b_target) b_steps (gh qr (ny b_state) b_pref) b_prep = true at hbv
      rcases hy : ig g b_target with _ | y
      · rw [hy] at hbv; contradiction
      · rw [hy] at hbv
        change eO b_steps (gh qr (ny b_state) b_pref) (jE b_prep (fw y)) = true at hbv
        have hnat:=gi b_steps (gh qr (ny b_state) b_pref) (jE b_prep (fw y)) hbv r'
        rw [w1,x5,nQ] at hnat
        have hret_step : (jY b_state (bf default (be qr.reverse)) (be b_pref+>r')) [tm]⊢⁺ (dC (fw y) (be b_prep+>r')) := by
          revert hnat; cases b_state <;> intro hnat <;> exact hnat
        rcases kz hret_step hm with ⟨a,ham,ha⟩
        rcases ih a (by omega) b_target y hy (be b_prep+>r') ha with ⟨z,d,hza,hsafe,hz⟩
        exact ⟨z,d,by omega,hsafe,hz⟩
def j9 : W→List b9
  | .UA => [.PL]
  | .UT => [.P11,.P11,.PL]
lemma Go (u:W) : G1 u++wX = b5 (j9 u) := by
  cases u <;> rfl
lemma CU (u:W) : G [u,.UA] = b5 (j9 u) := by
  cases u <;> rfl
lemma CW (u:W) : G [u,.UT] = b5 (j9 u)++wY := by
  cases u <;> rfl
lemma AX (u v:W) (l:ai) (c:aL)
    (h : ip (bf l (G [u,v])) c) : cE c (dU l) := by
  cases v
  · rw [CU] at h
    exact lI (j9 u) l c h
  · rw [CW,df] at h
    have hstack (e:Bs) (r0:ai) :
        cE (aq (bf l (b5 (j9 u))) [false,false,false,false] e r0) (dU l) :=
      bh (jC (bf l (b5 (j9 u))) [false,false,false,false] e r0)
        (lI (j9 u) l)
    cases h with
    | contact_D r0 => exact hstack .FromD r0
    | contact_F r0 => exact hstack .FromF r0
    | contact_B r0 => exact hstack .FromB r0
lemma xW (d:cm) (us vs : List W) :
    cn d (us++vs) = bf (cn d us) (G vs) := by
  unfold cn
  rw [Gk,← List.append_assoc,df]
lemma Bi (d:cm) (us : List W) (u:W) :
    cn d (us++[u]) = bf (cn d us) (G1 u) := by
  rw [xW]
  simp [G]
lemma B7 (d:cm) (a b c e:W) (r:ai) :
    fl (hF d [a,b,c,e] r) lr := by
  refine cr (ta d [a,b,c,e] r) ?_
  have hf : cn d [a,b,c,e] = bf (cn d [a,b]) (G [c,e]) :=
    xW d [a,b] [c,e]
  rw [hf]
  refine bh (fv (bf (cn d [a,b]) (G [c,e])) ([0]+>r)) ?_
  intro x hx
  refine bh (AX c e (cn d [a,b]) x hx) ?_
  intro y hy
  refine bh (hN d [a,b] y hy) ?_
  intro z hz
  exact dg (i8 d [a,b] z (by simp) hz)
lemma F5 (u:W) (l r:ai) :
    (DL (bf l (G1 u)) r) [tm]⊢⁺ (DL l (wa+>((match u with | .UA => [] | .UT => wY)+>r))) := by
  cases u
  · simpa only [G1,append_nil] using! GV l r
  · simpa only [G1,append_assoc] using!
      U 13 ⟨(wX++wY).reverse,[],D,true⟩ ⟨[],wa++wY,D,true⟩ (by decide) l r
lemma Ea (l r:ai) :
    (FL (bf l (G1 .UA)) ([0,0,0]+>r)) [tm]⊢⁺ (FL l ([0,0,0]+>(wa+>r))) :=
  Dp l r
lemma D1 (l r:ai) :
    (FL (bf l (G1 .UT)) ([0,0,0]+>r)) [tm]⊢⁺ (FR (bf l (b5 [.P11])) ([0,0]+>r)) :=
  U 1 ⟨(wX++wY).reverse,[0,0,0],F,true⟩ ⟨(b5 [.P11]).reverse,[0,0],F,false⟩ (by decide) l r
lemma A0 (d:cm) (us : List W) (u:W) (c:aL)
    (h : dA (bf (cn d us) (G1 u)) c)
    (h1 : ∀ r,cE (BL (bf (cn d us) (G1 u)) ([0,0,1,0,1]+>r)) lr)
    (h2 : ∀ r,cE (BL (bf (cn d us) (G1 u)) ([0,0,1,1,1,0,1]+>r)) lr)
    (hlen : 2 ≤ us.length) : cE c lr := by
  cases h with
  | phase_D r =>
    refine cc (F5 u (cn d us) r) ?_
    refine bh (hN d us _ (.strong_D _)) ?_
    intro e he
    exact dg (i8 d us e hlen he)
  | phase_F r =>
    cases u
    · refine cc (Ea (cn d us) r) ?_
      refine bh (hN d us _ (.strong_F _)) ?_
      intro e he
      exact dg (i8 d us e hlen he)
    · refine cc (D1 (cn d us) r) ?_
      refine bh (r7 [.P11] (cn d us) ([0,0]+>r)) ?_
      intro e he
      refine bh (hN d us e he) ?_
      intro f hf
      exact dg (i8 d us f hlen hf)
  | phase_B101 r => exact h1 r
  | phase_B11101 r => exact h2 r
def r8 : Prop:=∀ d a b c r,
  cE (BL (cn d [a,b,c]) ([0,0,1,0,1]+>r)) lr ∧
  cE (BL (cn d [a,b,c]) ([0,0,1,1,1,0,1]+>r)) lr
lemma Bp (hb:r8) (d:cm) (a b c:W) (r:ai) :
    fl (hF d [a,b,c] r) lr := by
  refine cr (ta d [a,b,c] r) ?_
  refine bh (uK (cn d [a,b,c]) r) ?_
  intro x hx
  have hsnoc : cn d [a,b,c] = bf (cn d [a,b]) (G1 c) :=
    Bi d [a,b] c
  rw [hsnoc] at hx
  refine A0 d [a,b] c x hx ?_ ?_ (by simp)
  · intro r'; rw [← hsnoc]; exact (hb d a b c r').1
  · intro r'; rw [← hsnoc]; exact (hb d a b c r').2
lemma Br (d:cm) (us vs : List W) (r:ai) :
    hF d (us++vs) r = hF d us ((match d with | .CD => HD vs | .CF => HF vs)+>r) := by
  cases d <;> simp [hF,n9,FQ,FY,append_assoc]
lemma y3 (hb:r8) (c:aL) (hs : lr c) : fl c lr := by
  rcases hs with ⟨d,us,r,hlen,rfl⟩
  rcases us with _ | ⟨a,_ | ⟨b,_ | ⟨e,_ | ⟨f,us'⟩⟩⟩⟩
  · contradiction
  · contradiction
  · contradiction
  · exact Bp hb d a b e r
  · have h4 : [a,b,e,f]++us' = a :: b :: e :: f :: us':=rfl
    rw [← h4,Br]
    exact B7 d a b e f _
lemma AM (hb:r8) (c:aL) (hs : lr c) (n:Nat) : ¬ d7 c n :=
  q2 (y3 hb) n c hs
lemma CR :
    (init []) [tm]⊢* (hF .CD [.UA,.UT,.UA,.UA] ([1,0,1,0,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1]+>default)) := by
  have h0 : init [] = dw ⟨[],([0] : List gQ) ^ 32,A⟩ default := by
    have hz : (([0] : List gQ) ^ 32)+>default = default:=qZ (by decide)
    unfold init dw
    rw [append_nil,hz]
    rfl
  have hrun:=kC 1044
    ⟨[],([0] : List gQ) ^ 32,A⟩
    ⟨[],[0,0]++n9 .CD [.UA,.UT,.UA,.UA]++[1,0,1,0,0,1,1,0,1,0,1,1,0,1,0,0,1,0,1],E⟩
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
def Ii : ab dp:=.empty
def nd (x:dp) (l r : ab dp) : ab dp:=.node (some x) l r
def aZ (x:dp) (l : ab dp) : ab dp:=.node (some x) l .empty
def Ij (x:dp) (r : ab dp) : ab dp:=.node (some x) .empty r
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
def FE:Pos:=.O di
def Gj:Pos:=.E di
def GD:Pos:=.O da
def Gn:Pos:=.E da
def Gq:Pos:=.O cA
def GA:Pos:=.E cA
def Gh:Pos:=.O cS
def Gz:Pos:=.E cS
def Gx:Pos:=.O cI
def F3:Pos:=.E cI
def Fq:Pos:=.O c8
def FU:Pos:=.E c8
def FJ:Pos:=.O cN
def Gu:Pos:=.E cN
def Hp:Pos:=.O c7
def HQ:Pos:=.E c7
def HE:Pos:=.O c0
def HO:Pos:=.E c0
def Hy:Pos:=.O dI
def HN:Pos:=.E dI
def HG:Pos:=.O dr
def Ia:Pos:=.E dr
def H4:Pos:=.O ds
def H3:Pos:=.E ds
def Hx:Pos:=.O dT
def HH:Pos:=.E dT
def HY:Pos:=.O c6
def Hz:Pos:=.E c6
def Ht:Pos:=.O dl
def H6:Pos:=.E dl
def HB:Pos:=.O dL
def HI:Pos:=.E dL
def HS:Pos:=.O cO
def Hv:Pos:=.E cO
def GR:Pos:=.O dM
def Hk:Pos:=.E dM
def He:Pos:=.O cL
def Hu:Pos:=.E cL
def HM:Pos:=.O cU
def Hw:Pos:=.E cU
def HK:Pos:=.O cT
def H1:Pos:=.E cT
def Hs:Pos:=.O dq
def HW:Pos:=.E dq
def HV:Pos:=.O dY
def HZ:Pos:=.E dY
def H9:Pos:=.O d9
def HT:Pos:=.E d9
def H2:Pos:=.O d1
def HX:Pos:=.E d1
def HP:Pos:=.O FE
def Ha:Pos:=.E FE
def GT:Pos:=.O Gj
def Hi:Pos:=.E Gj
def Hl:Pos:=.O GD
def GM:Pos:=.E GD
def G8:Pos:=.O Gn
def G9:Pos:=.E Gn
def Hn:Pos:=.O Gq
def Hf:Pos:=.E Gq
def GO:Pos:=.O GA
def GX:Pos:=.E GA
def GY:Pos:=.O Gh
def Gc:Pos:=.E Gh
def Hh:Pos:=.O Gz
def GL:Pos:=.E Gz
def G6:Pos:=.O Gx
def GU:Pos:=.E Gx
def G4:Pos:=.O F3
def GK:Pos:=.E F3
def Hj:Pos:=.O Fq
def Hd:Pos:=.E Fq
def Hg:Pos:=.O FU
def GS:Pos:=.E FU
def GQ:Pos:=.O FJ
def G0:Pos:=.E FJ
def Gf:Pos:=.O Gu
def Hb:Pos:=.E Gu
def vx(p:Pos):Pos:=.E (.E (.E p))
def vA(p:Pos):Pos:=.O (.E (.E p))
def vu(p:Pos):Pos:=.E (.O (.E p))
def vq(p:Pos):Pos:=.O (.O (.E p))
def vw(p:Pos):Pos:=.E (.E (.O p))
def vp(p:Pos):Pos:=.O (.E (.O p))
def vt(p:Pos):Pos:=.E (.O (.O p))
def vB(p:Pos):Pos:=.O (.O (.O p))
namespace Pos
def p0(p:Pos):Pos:=vx (vx p)
def p1(p:Pos):Pos:=vA (vx p)
def p2(p:Pos):Pos:=vu (vx p)
def p3(p:Pos):Pos:=vq (vx p)
def p4(p:Pos):Pos:=vw (vx p)
def p5(p:Pos):Pos:=vp (vx p)
def p6(p:Pos):Pos:=vt (vx p)
def p7(p:Pos):Pos:=vB (vx p)
def p8(p:Pos):Pos:=vx (vA p)
def p9(p:Pos):Pos:=vA (vA p)
def gL(p:Pos):Pos:=vu (vA p)
def hH(p:Pos):Pos:=vq (vA p)
def f5(p:Pos):Pos:=vw (vA p)
def gj(p:Pos):Pos:=vp (vA p)
def ga(p:Pos):Pos:=vt (vA p)
def f9(p:Pos):Pos:=vB (vA p)
def eA(p:Pos):Pos:=vx (vu p)
def gn(p:Pos):Pos:=vA (vu p)
def fx(p:Pos):Pos:=vu (vu p)
def fM(p:Pos):Pos:=vq (vu p)
def gd(p:Pos):Pos:=vw (vu p)
def gb(p:Pos):Pos:=vp (vu p)
def fq(p:Pos):Pos:=vt (vu p)
def gv(p:Pos):Pos:=vB (vu p)
def fC(p:Pos):Pos:=vx (vq p)
def gm(p:Pos):Pos:=vA (vq p)
def gH(p:Pos):Pos:=vu (vq p)
def fm(p:Pos):Pos:=vq (vq p)
def eS(p:Pos):Pos:=vw (vq p)
def eY(p:Pos):Pos:=vp (vq p)
def gg(p:Pos):Pos:=vt (vq p)
def fL(p:Pos):Pos:=vB (vq p)
def ex(p:Pos):Pos:=vx (vw p)
def fN(p:Pos):Pos:=vA (vw p)
def fK(p:Pos):Pos:=vu (vw p)
def ez(p:Pos):Pos:=vq (vw p)
def eu(p:Pos):Pos:=vw (vw p)
def fA(p:Pos):Pos:=vp (vw p)
def fT(p:Pos):Pos:=vt (vw p)
def eB(p:Pos):Pos:=vB (vw p)
def er(p:Pos):Pos:=vx (vp p)
def gk(p:Pos):Pos:=vA (vp p)
def e1(p:Pos):Pos:=vu (vp p)
def gl(p:Pos):Pos:=vq (vp p)
def fz(p:Pos):Pos:=vw (vp p)
def f8(p:Pos):Pos:=vp (vp p)
def eH(p:Pos):Pos:=vt (vp p)
def eW(p:Pos):Pos:=vB (vp p)
def fi(p:Pos):Pos:=vx (vt p)
def fU(p:Pos):Pos:=vA (vt p)
def fo(p:Pos):Pos:=vu (vt p)
def eZ(p:Pos):Pos:=vq (vt p)
def ev(p:Pos):Pos:=vw (vt p)
def gO(p:Pos):Pos:=vp (vt p)
def fu(p:Pos):Pos:=vt (vt p)
def fD(p:Pos):Pos:=vB (vt p)
def fE(p:Pos):Pos:=vx (vB p)
def f4(p:Pos):Pos:=vA (vB p)
def ft(p:Pos):Pos:=vu (vB p)
def fp(p:Pos):Pos:=vq (vB p)
def gK(p:Pos):Pos:=vw (vB p)
def fP(p:Pos):Pos:=vp (vB p)
def f6(p:Pos):Pos:=vt (vB p)
def e7(p:Pos):Pos:=vB (vB p)
end Pos
def e_:Y:=[]
def bd:Y:=false::e_
def b1:Y:=true::e_
def aP:Y:=false::bd
def aE:Y:=false::b1
def fY:Y:=true::bd
def jN:Y:=true::b1
def Gl:Y:=false::aP
def aw:Y:=false::fY
def jH:Y:=false::jN
def j:Y:=true::aP
def H:Y:=true::aE
def vO:Y:=true::fY
def xI:Y:=true::jN
def FX:Y:=false::aw
def FO:Y:=false::jH
def L:Y:=false::j
def au:Y:=false::H
def xi:Y:=false::vO
def FG:Y:=false::xI
def FS:Y:=true::Gl
def bt:Y:=true::aw
def pw:Y:=true::jH
def h9:Y:=true::j
def K:Y:=true::H
def yi:Y:=true::vO
def pq:Y:=true::xI
def af:Y:=false::L
def aA:Y:=false::au
def k9:Y:=false::bt
def kW:Y:=false::pw
def hj:Y:=false::h9
def ak:Y:=false::K
def oj:Y:=false::pq
def EM:Y:=true::FX
def aU:Y:=true::L
def ci:Y:=true::au
def rv:Y:=true::xi
def EW:Y:=true::FG
def bq:Y:=true::bt
def yJ:Y:=true::pw
def ah:Y:=true::K
def oF:Y:=true::yi
def yE:Y:=true::pq
def br:Y:=false::af
def bj:Y:=false::ak
def Ed:Y:=false::oj
def D7:Y:=false::EM
def ad:Y:=false::aU
def dO:Y:=false::ci
def hO:Y:=false::bq
def X:Y:=false::ah
def u9:Y:=false::oF
def ie:Y:=true::af
def iZ:Y:=true::aA
def mE:Y:=true::k9
def kx:Y:=true::kW
def aH:Y:=true::hj
def dN:Y:=true::ak
def A3:Y:=true::oj
def eM:Y:=true::aU
def dV:Y:=true::ci
def pJ:Y:=true::rv
def A9:Y:=true::EW
def aN:Y:=true::bq
def DZ:Y:=true::yJ
def dZ:Y:=true::ah
def xL:Y:=true::oF
def A8:Y:=true::yE
def dD:Y:=false::ad
def Di:Y:=false::hO
def aB:Y:=false::X
def b3:Y:=false::ie
def e4:Y:=false::iZ
def vS:Y:=false::mE
def Df:Y:=false::kx
def bO:Y:=false::aH
def cg:Y:=false::dN
def zi:Y:=false::A3
def gN:Y:=false::eM
def vN:Y:=false::dV
def vI:Y:=false::pJ
def vK:Y:=false::A9
def b4:Y:=false::aN
def C2:Y:=false::DZ
def lq:Y:=false::dZ
def ao:Y:=true::br
def ar:Y:=true::bj
def CG:Y:=true::Ed
def CX:Y:=true::D7
def cC:Y:=true::ad
def e3:Y:=true::dO
def vU:Y:=true::hO
def aV:Y:=true::X
def De:Y:=true::u9
def my:Y:=true::mE
def iE:Y:=true::kx
def oo:Y:=true::aH
def rR:Y:=true::dN
def ea:Y:=true::eM
def gf:Y:=true::dV
def gS:Y:=true::aN
def bK:Y:=true::dZ
def yn:Y:=true::xL
def Ic(t:Y):Y:=false::false::false::false::t
def wi(t:Y):Y:=true::false::false::false::t
def mx(t:Y):Y:=false::true::false::false::t
def wM(t:Y):Y:=true::true::false::false::t
def pn(t:Y):Y:=false::false::true::false::t
def js(t:Y):Y:=true::false::true::false::t
def kU(t:Y):Y:=false::true::true::false::t
def lv(t:Y):Y:=true::true::true::false::t
def xT(t:Y):Y:=false::false::false::true::t
def mS(t:Y):Y:=true::false::false::true::t
def kd(t:Y):Y:=false::true::false::true::t
def jM(t:Y):Y:=true::true::false::true::t
def pY(t:Y):Y:=false::false::true::true::t
def ks(t:Y):Y:=true::false::true::true::t
def nH(t:Y):Y:=false::true::true::true::t
def kI(t:Y):Y:=true::true::true::true::t
def _root_.List.sx(t:Y):Y:=wi (wi t)
def _root_.List.v9(t:Y):Y:=mx (wi t)
def _root_.List.H5(t:Y):Y:=pn (wi t)
def _root_.List.G2(t:Y):Y:=js (wi t)
def _root_.List.GW(t:Y):Y:=kU (wi t)
def _root_.List.Dg(t:Y):Y:=lv (wi t)
def _root_.List.GE(t:Y):Y:=kd (wi t)
def _root_.List.iG(t:Y):Y:=mx (mx t)
def _root_.List.GB(t:Y):Y:=wM (mx t)
def _root_.List.hU(t:Y):Y:=js (mx t)
def _root_.List.AQ(t:Y):Y:=mS (mx t)
def _root_.List.wd(t:Y):Y:=kd (mx t)
def _root_.List.o5(t:Y):Y:=jM (mx t)
def _root_.List.AV(t:Y):Y:=pY (mx t)
def _root_.List.xx(t:Y):Y:=ks (mx t)
def _root_.List.vL(t:Y):Y:=nH (mx t)
def _root_.List.mu(t:Y):Y:=kI (mx t)
def _root_.List.HU(t:Y):Y:=pn (wM t)
def _root_.List.AZ(t:Y):Y:=js (wM t)
def _root_.List.yb(t:Y):Y:=lv (wM t)
def _root_.List.y9(t:Y):Y:=pn (pn t)
def _root_.List.hM(t:Y):Y:=js (pn t)
def _root_.List.x2(t:Y):Y:=kU (pn t)
def _root_.List.F4(t:Y):Y:=xT (pn t)
def _root_.List.D8(t:Y):Y:=mS (pn t)
def _root_.List.ni(t:Y):Y:=kd (pn t)
def _root_.List.hK(t:Y):Y:=jM (pn t)
def _root_.List.jd(t:Y):Y:=mx (js t)
def _root_.List.vr(t:Y):Y:=wM (js t)
def _root_.List.bi(t:Y):Y:=js (js t)
def _root_.List.bg(t:Y):Y:=kU (js t)
def _root_.List.cJ(t:Y):Y:=lv (js t)
def _root_.List.kY(t:Y):Y:=mS (js t)
def _root_.List.aD(t:Y):Y:=kd (js t)
def _root_.List.b8(t:Y):Y:=jM (js t)
def _root_.List.pD(t:Y):Y:=pY (js t)
def _root_.List.bm(t:Y):Y:=ks (js t)
def _root_.List.ja(t:Y):Y:=nH (js t)
def _root_.List.bu(t:Y):Y:=kI (js t)
def _root_.List.fr(t:Y):Y:=pn (kU t)
def _root_.List.xF(t:Y):Y:=js (kU t)
def _root_.List.mX(t:Y):Y:=kU (kU t)
def _root_.List.pT(t:Y):Y:=mS (kU t)
def _root_.List.aX(t:Y):Y:=kd (kU t)
def _root_.List.bH(t:Y):Y:=jM (kU t)
def _root_.List.CJ(t:Y):Y:=pY (kU t)
def _root_.List.cd(t:Y):Y:=ks (kU t)
def _root_.List.aS(t:Y):Y:=nH (kU t)
def _root_.List.b6(t:Y):Y:=kI (kU t)
def _root_.List.bI(t:Y):Y:=mx (lv t)
def _root_.List.Cn(t:Y):Y:=wM (lv t)
def _root_.List.aI(t:Y):Y:=js (lv t)
def _root_.List.iI(t:Y):Y:=kU (lv t)
def _root_.List.wj(t:Y):Y:=lv (lv t)
def _root_.List.FZ(t:Y):Y:=mS (lv t)
def _root_.List.bw(t:Y):Y:=kd (lv t)
def _root_.List.dm(t:Y):Y:=jM (lv t)
def _root_.List.EQ(t:Y):Y:=pY (lv t)
def _root_.List.hL(t:Y):Y:=ks (lv t)
def _root_.List.jr(t:Y):Y:=nH (lv t)
def _root_.List.fy(t:Y):Y:=kI (lv t)
def _root_.List.Fy(t:Y):Y:=xT (xT t)
def _root_.List.Gp(t:Y):Y:=mS (xT t)
def _root_.List.xD(t:Y):Y:=kd (xT t)
def _root_.List.CI(t:Y):Y:=jM (xT t)
def _root_.List.FI(t:Y):Y:=ks (xT t)
def _root_.List.gP(t:Y):Y:=wi (mS t)
def _root_.List.AO(t:Y):Y:=mx (mS t)
def _root_.List.Em(t:Y):Y:=pn (mS t)
def _root_.List.sk(t:Y):Y:=js (mS t)
def _root_.List.n1(t:Y):Y:=kU (mS t)
def _root_.List.eC(t:Y):Y:=lv (mS t)
def _root_.List.vz(t:Y):Y:=kd (mS t)
def _root_.List.yd(t:Y):Y:=pn (kd t)
def _root_.List.ib(t:Y):Y:=js (kd t)
def _root_.List.Eb(t:Y):Y:=kU (kd t)
def _root_.List.ae(t:Y):Y:=kd (kd t)
def _root_.List.aF(t:Y):Y:=jM (kd t)
def _root_.List.kB(t:Y):Y:=pY (kd t)
def _root_.List.e0(t:Y):Y:=ks (kd t)
def _root_.List.aC(t:Y):Y:=nH (kd t)
def _root_.List.bP(t:Y):Y:=kI (kd t)
def _root_.List.cH(t:Y):Y:=mx (jM t)
def _root_.List.vv(t:Y):Y:=wM (jM t)
def _root_.List.cx(t:Y):Y:=js (jM t)
def _root_.List.S(t:Y):Y:=kU (jM t)
def _root_.List.cz(t:Y):Y:=lv (jM t)
def _root_.List.iH(t:Y):Y:=mS (jM t)
def _root_.List.bQ(t:Y):Y:=kd (jM t)
def _root_.List.gR(t:Y):Y:=jM (jM t)
def _root_.List.FN(t:Y):Y:=pY (jM t)
def _root_.List.fj(t:Y):Y:=ks (jM t)
def _root_.List.ia(t:Y):Y:=nH (jM t)
def _root_.List.eK(t:Y):Y:=kI (jM t)
def _root_.List.r4(t:Y):Y:=xT (pY t)
def _root_.List.rF(t:Y):Y:=mS (pY t)
def _root_.List.nh(t:Y):Y:=kd (pY t)
def _root_.List.gY(t:Y):Y:=jM (pY t)
def _root_.List.xQ(t:Y):Y:=ks (pY t)
def _root_.List.Gg(t:Y):Y:=mx (ks t)
def _root_.List.Gw(t:Y):Y:=wM (ks t)
def _root_.List.cR(t:Y):Y:=js (ks t)
def _root_.List.bV(t:Y):Y:=kU (ks t)
def _root_.List.aO(t:Y):Y:=lv (ks t)
def _root_.List.mv(t:Y):Y:=mS (ks t)
def _root_.List.aj(t:Y):Y:=kd (ks t)
def _root_.List.ag(t:Y):Y:=jM (ks t)
def _root_.List.Gv(t:Y):Y:=pY (ks t)
def _root_.List.eP(t:Y):Y:=ks (ks t)
def _root_.List.b2(t:Y):Y:=nH (ks t)
def _root_.List.nR(t:Y):Y:=kI (ks t)
def _root_.List.kv(t:Y):Y:=pn (nH t)
def _root_.List.pF(t:Y):Y:=js (nH t)
def _root_.List.nS(t:Y):Y:=kU (nH t)
def _root_.List.cQ(t:Y):Y:=kd (nH t)
def _root_.List.bl(t:Y):Y:=jM (nH t)
def _root_.List.eb(t:Y):Y:=ks (nH t)
def _root_.List.iF(t:Y):Y:=nH (nH t)
def _root_.List.q5(t:Y):Y:=kI (nH t)
def _root_.List.fF(t:Y):Y:=mx (kI t)
def _root_.List.pl(t:Y):Y:=wM (kI t)
def _root_.List.eV(t:Y):Y:=js (kI t)
def _root_.List.a0(t:Y):Y:=kU (kI t)
def _root_.List.pk(t:Y):Y:=lv (kI t)
def _root_.List.F1(t:Y):Y:=mS (kI t)
def _root_.List.eN(t:Y):Y:=kd (kI t)
def _root_.List.dJ(t:Y):Y:=jM (kI t)
def _root_.List.HL(t:Y):Y:=pY (kI t)
def _root_.List.dK(t:Y):Y:=ks (kI t)
def _root_.List.jq(t:Y):Y:=nH (kI t)
def _root_.List.ec(t:Y):Y:=kI (kI t)
def _root_.List.bo(t:Y):Y:=t.eV.aO
def _root_.List.av(t:Y):Y:=t.aC.bi
def _root_.List.b0(t:Y):Y:=t.aC.aS
def _root_.List.eh(t:Y):Y:=t.kv.hK
def _root_.List.cw(t:Y):Y:=t.bu.aO
def _root_.List.cY(t:Y):Y:=t.pD.aF
def _root_.List.bz(t:Y):Y:=t.bm.aI
def _root_.List.qV(t:Y):Y:=t.bi.aI
def _root_.List.cK(t:Y):Y:=t.bV.ae
def _root_.List.cs(t:Y):Y:=t.S.aj
def _root_.List.eD(t:Y):Y:=t.AQ.bi
def _root_.List.gD(t:Y):Y:=t.hU.fr
def _root_.List.cf(t:Y):Y:=t.cd.S
def _root_.List.k7(t:Y):Y:=t.gY.bm
def _root_.List.dv(t:Y):Y:=t.ag.aX
def _root_.List.fQ(t:Y):Y:=t.aO.iG
def _root_.List.bp(t:Y):Y:=t.ae.S
def _root_.List.EK(t:Y):Y:=t.gY.bu
def _root_.List.dB(t:Y):Y:=t.e0.S
def _root_.List.cv(t:Y):Y:=t.bQ.bl
def _root_.List.gC(t:Y):Y:=t.ag.S
def _root_.List.d6(t:Y):Y:=t.bm.bI
def _root_.List.g8(t:Y):Y:=t.e0.bI
def _root_.List.Fk(t:Y):Y:=t.bi.cR
def _root_.List.it(t:Y):Y:=t.eb.S
def _root_.List.EO(t:Y):Y:=t.b8.AQ
def _root_.List.dh(t:Y):Y:=t.bm.fy
def _root_.List.EN(t:Y):Y:=t.nh.bi
def _root_.List.fg(t:Y):Y:=t.b8.aX
def _root_.List.gZ(t:Y):Y:=t.cx.S
def _root_.List.fH(t:Y):Y:=t.bV.ag
def _root_.List.iV(t:Y):Y:=t.cx.aC
def _root_.List.Ao(t:Y):Y:=t.bQ.eV
def _root_.List.ik(t:Y):Y:=t.bH.dm
def _root_.List.gE(t:Y):Y:=t.eV.gY
def _root_.List.i9(t:Y):Y:=t.bI.aC
def _root_.List.kk(t:Y):Y:=t.cR.aI
def _root_.List.i0(t:Y):Y:=t.cQ.pF
def _root_.List.ce(t:Y):Y:=t.bl.aC
def _root_.List.i2(t:Y):Y:=t.aI.gP
def _root_.List.g6(t:Y):Y:=t.S.ag
def _root_.List.h8(t:Y):Y:=t.bH.aC
def _root_.List.ho(t:Y):Y:=t.ag.aD
def _root_.List.iv(t:Y):Y:=t.n1.hK
def _root_.List.jQ(t:Y):Y:=t.aI.aO
def _root_.List.g0(t:Y):Y:=t.bH.bw
def _root_.List.kl(t:Y):Y:=t.a0.a0
def _root_.List.db(t:Y):Y:=t.EK.aO
def _root_.List.dx(t:Y):Y:=t.hL.fy
def _root_.List.io(t:Y):Y:=t.eh.gD
def _root_.List.dt(t:Y):Y:=t.EO.qV
def _root_.List.fd(t:Y):Y:=t.EN.aO
def _root_.List.gT(t:Y):Y:=t.Fk.aI
def _root_.List.eF(t:Y):Y:=t.Ao.aO
def _root_.List.hV(t:Y):Y:=t.k7.aI
def _root_.List.gB(t:Y):Y:=t.jd.aC
def DA : List W:=[.UA,.UA]
def kD : List W:=[.UA,.UA,.UA]
def FW : List W:=[.UA,.UA,.UA,.UA]
def f7 : List W:=[.UA,.UA,.UT]
def FB : List W:=[.UA,.UA,.UT,.UA]
def A7 : List W:=[.UA,.UT]
def nP : List W:=[.UA,.UT,.UA]
def FP : List W:=[.UA,.UT,.UA,.UA]
def Ev : List W:=[.UA,.UT,.UA,.UA,.UA]
def A4 : List W:=[.UA,.UT,.UA,.UA,.UA,.UA]
def vR : List W:=[.UA,.UT,.UT]
def Ga : List W:=[.UT,.UA]
def dE : List W:=[.UT,.UA,.UA]
def vk : List W:=[.UT,.UA,.UA,.UA]
def Ft : List W:=[.UT,.UA,.UA,.UA,.UA]
def hI : List W:=[.UT,.UA,.UT]
def Dq : List W:=[.UT,.UA,.UT,.UA]
def F6 : List W:=[.UT,.UA,.UT,.UT]
def Gb : List W:=[.UT,.UT]
def mD : List W:=[.UT,.UT,.UA]
def FM : List W:=[.UT,.UT,.UA,.UA]
def fB : List W:=[.UT,.UT,.UT]
def Dj : List W:=[.UT,.UT,.UT,.UA]
def wN : List b9:=[]
def iC : List b9:=[.P11]
def sc : List b9:=[.P11,.P11]
def Bq : List Bool:=[]
def Gr : List Bool:=[false,false]
def rT : List Bool:=[false,false,false,false,true,true,true,true]
def Bz : List Bool:=[false,false,true,false]
def rg : List Bool:=[false,false,true,false,false,false,false,false,true,true,true,true,false,false,true,false,false,true,false]
def zy : List Bool:=[false,false,true,true,true,true]
def xY : List Bool:=[true]
def AU : List Bool:=[true,false,false,false,false,true,true,true,true]
def DT : List Bool:=[true,false,false,true,false]
def xy : List Bool:=[true,false,false,true,false,false,false,false,true,true,true,true]
def Bt : List Bool:=[true,false,false,true,false,false,true,false]
def BA : List Bool:=[true,false,false,true,true,true,true]
def Bk : List Bool:=[true,false,false,true,true,true,true,true]
def yc : List Bool:=[true,false,false,true,true,true,true,true,false,false,false]
def EB : List Bool:=[true,false,true,false]
def x7 : List Bool:=[true,false,true,false,false,false,false,true,true,true,true]
def BE : List Bool:=[true,false,true,false,false,true,false]
def rZ : List Bool:=[true,false,true,false,true,true,true,true]
def vo : List Bool:=[true,false,true,false,true,true,true,true,false,false,true,false,false,true,false]
def CN : List Bool:=[true,false,true,true,true,true]
def Cp : List Bool:=[true,false,true,true,true,true,true]
def Ap : List Bool:=[true,false,true,true,true,true,true,false,false,false]
def Dh : List Bool:=[true,true]
def sv : List Bool:=[true,true,false,false,false,false,false,true,true,true,true]
def Bo : List Bool:=[true,true,true]
def tt : List Bool:=[true,true,true,true]
def B5 : List Bool:=[true,true,true,true,false,false,false]
def Bg : List Bool:=[true,true,true,true,true,false,false,false]
def vy : List Bool:=[true,true,true,true,true,true,false,false,false,true,false,false,false,true,false]
def aM (d:cm) (us : List W) (w : List Bool) : fZ:=.Recovered d us w
def t9 (d:cm) (us : List W) (w : List Bool) : fZ:=.NineGain d us w
def t6 (d:cm) (us : List W) (w : List Bool) : fZ:=.SixGain d us w
def tY (w : List Bool) : fZ:=.YaaGain w
def eU (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (aM d us w)
def Dm (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (t9 d us w)
def zj (d:cm) (us : List W) (w : List Bool) : dp:=.rEnd (t6 d us w)
def kH (w : List Bool) : dp:=.rEnd (tY w)
def DG (w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (xB w) s t p
def Id (q w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (jJ q w) s t p
def F7 (q w : List Bool) (s:Nat) (t:Pos) (p : List Bool) : dp:=.rNat (gh q .qB w) s t p
def rP (b : List Bool) (ps : List b9) (st : List Bool) (nd:Nat) (td:fZ) (nf:Nat) (tf:fZ) (w : List Bool) : dp:=.rProt ⟨b,ps,st,nd,td,nf,tf⟩ w
def dH (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) : dp:=.rRet q w .AllCases [⟨.RD,[],s1,t1,p1⟩,⟨.RF,[false,false],s2,t2,p2⟩,⟨.RB,[false,false],s3,t3,p3⟩]
def eX (q : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) (s4:Nat) (t4:Pos) (p4 : List Bool) : dp:=.rRet q [false,false] .Cases00 [⟨.RD,[true,false,true],s1,t1,p1⟩,⟨.RD,[true,true,true,false,true],s2,t2,p2⟩,⟨.RD,[true,false,true,false,false],s3,t3,p3⟩,⟨.RF,[false,false,false],s4,t4,p4⟩]
def jL (q : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) (s3:Nat) (t3:Pos) (p3 : List Bool) (s4:Nat) (t4:Pos) (p4 : List Bool) : dp:=.rRet q [true] .Cases1 [⟨.RD,[true,true,false,true],s1,t1,p1⟩,⟨.RD,[false,true,false,false],s2,t2,p2⟩,⟨.RF,[false,false],s3,t3,p3⟩,⟨.RB,[false,false],s4,t4,p4⟩]
def FF (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) : dp:=.rRet q w .Coarse00 [⟨.RD,[],s1,t1,p1⟩,⟨.RF,[false,false],s2,t2,p2⟩]
def Bj (q w : List Bool) (s1:Nat) (t1:Pos) (p1 : List Bool) (s2:Nat) (t2:Pos) (p2 : List Bool) : dp:=.rRet q w .Coarse10 [⟨.RD,[],s1,t1,p1⟩,⟨.RB,[false,false],s2,t2,p2⟩]
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
def nX:=z5.ez
def mK:=dr.gk
def mc:=z6.ex
def mM:=cy.p5
def lA:=c0.fL
def lm:=cB.fq
def ky:=cP.eY
def py:=c0.fo
def rO:=z2.e7
def nW:=z3.fm
def rN:=cy.gO
def nV:=cG.gm
def se:=z4.fK
def pv:=z7.gv
def sb:=cU.f5
def rU:=dy.eS
def r5:=z7.f5
def nY:=cy.p2
def pm:=ct.p5
def vg:=ds.fC
def sg:=ct.eY
def pA:=dn.p1
def pp:=cM.p9
def pz:=cM.gL
def rQ:=d1.e1
def rY:=cS.gb
def r9:=d1.eu
def rW:=d1.er
def pt:=c0.fT
def si:=z2.fP
def u5:=c0.fD
def sa:=cP.gH
def vd:=cU.gj
def sj:=cP.gn
def vj:=cO.p8
def r6:=cP.gg
def po:=c5.p5
def vm:=cq.eY
def u7:=di.e1
def wt:=z2.eZ
def vf:=dy.gL
def vc:=di.eH
def vb:=ds.gH
def u6:=di.fi
def ve:=dl.eA
def yj:=c9.p6
def rX:=z6.gk
def vl:=cB.gv
def vh:=cI.gH
def xb:=dj.fD
def xj:=cy.gg
def wS:=ds.gv
def yg:=cV.fN
def va:=da.ez
def vi:=cB.f8
def yk:=cI.p5
def v8:=cG.f8
def xn:=cG.fT
def xg:=cM.gl
def yl:=cP.eS
def ym:=z5.fo
def wT:=cB.gm
def vZ:=cI.p4
def uV:=cB.fC
def uz:=cM.gg
def wZ:=dL.gv
def Ai:=cM.hH
def w3:=dn.gb
def wn:=c5.eu
def w2:=dr.gd
def xa:=cL.fx
def tj:=cI.gO
def wU:=cI.fi
def wg:=c9.gl
def wD:=cG.gb
def xv:=cG.fM
def w0:=cG.fA
def ws:=dy.fz
def xd:=dy.gl
def xr:=cS.fA
def wy:=cN.fP
def v3:=c8.p1
def wO:=dj.f9
def wv:=dj.f5
def ug:=ct.p4
def sF:=cM.ft
def rb:=cG.fC
def wf:=dP.fz
def wu:=cM.gk
def zm:=di.p1
def B4:=cM.eS
def AA:=z4.fA
def zr:=dy.f6
def wK:=c0.fu
def we:=c8.eY
def wG:=dj.ft
def zR:=z8.f4
def zw:=cO.p9
def tH:=cU.eZ
def v7:=cP.p2
def yK:=c6.fP
def Aa:=cS.gj
def yz:=cA.fA
def xw:=cG.gk
def yI:=c7.p6
def v2:=cI.eA
def uv:=cM.fu
def u0:=z7.fm
def yV:=cB.fA
def Cs:=di.fz
def zZ:=cB.eH
def w6:=c6.p5
def wr:=cG.gj
def wF:=z7.gj
def yo:=cU.p6
def zM:=cT.p6
def Ae:=cP.eZ
def xt:=cM.fp
def zE:=cV.fC
def zp:=dM.fp
def yO:=c7.eY
def zx:=dr.gb
def AH:=dI.eS
def As:=c5.fi
def zH:=dY.er
def yt:=dY.gk
def w5:=cP.e7
def yY:=dP.p4
def yS:=dl.gl
def y7:=c6.fm
def yM:=dj.p6
def y0:=c8.ez
def Ax:=dL.fU
def Aq:=c5.p4
def wV:=c5.p7
def Ar:=da.gm
def Ak:=cV.eu
def AC:=dn.ex
def wC:=c9.f9
def zh:=dq.eZ
def xh:=cB.ex
def zP:=dj.fu
def ze:=da.fo
def nC:=bd.ag
def sL:=e_.cd
def lO:=oF.ag
def kV:=vO.a0
def Av:=e_.jr
def yB:=bd.dK
def i4:=xi.ag
def qk:=fY.dJ
def kt:=yi.eb
def cZ:=vI.ag
def fk:=rv.S
def il:=pJ.cd
def lD:=vO.cd
def xm:=fY.S
def o0:=yn.cd
def qs:=xL.S
def BT:=vO.b6
def yv:=rv.eK
def rE:=vI.dK
def aQ:=bd.hM
def aY:=b1.xF
def cj:=e_.bQ
def BI:=xi.nR
def Ad:=fY.cz
def s5:=pJ.jr
def bF:=aE.nh
def bE:=aP.xD
def rp:=yn.b6
def cl:=e_.iG
def cX:=e_.cH
def ed:=b1.aI
def fI:=b1.bI
def dS:=e_.wd
def dk:=aE.bl
def dz:=e_.hU
def Af:=xL.cz
def d8:=bd.hK
def d0:=bd.bi
def d4:=aP.FI
def eQ:=e_.cx
def Cj:=b1.eb
def e6:=aP.aF
def fX:=b1.bH
def gx:=e_.yb
def ow:=aE.eN
def gq:=aE.pF
def g5:=e_.ib
def gX:=aP.eC
def g7:=b3.bl
def g2:=K.aC
def hW:=e_.ia
def hQ:=cg.bl
def h5:=aE.xQ
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
def jD:=j.Dg
def jw:=H.eC
def jl:=H.sk
def ju:=j.G2
def jy:=ah.bm
def jn:=b1.ni
def jT:=bq.bl
def kn:=b1.bP
def jX:=e4.bl
def kr:=bd.bQ
def kc:=fY.bH
def ke:=ak.bQ
def ki:=e_.pD
def j5:=H.aO
def kg:=L.aC
def jZ:=bd.y9
def jU:=H.Em
def ka:=j.H5
def k6:=aP.ib
def kO:=b1.bw
def ld:=e_.vL
def kJ:=bd.kY
def kS:=L.wd
def rC:=L.bm
def kP:=e_.HU
def k0:=b1.fr
def lk:=K.wd
def lR:=fY.aI
def mq:=bd.iH
def mh:=j.vL
def lT:=bd.aX
def lS:=e_.aD
def lV:=e_.AZ
def lM:=aE.cQ
def lG:=j.cJ
def lP:=bd.cx
def nK:=j.GE
def mW:=e_.AQ
def nJ:=b1.hL
def m3:=aP.bQ
def nk:=H.eV
def nG:=ao.aI
def mY:=dN.aI
def mT:=ah.kY
def m4:=K.bm
def nj:=aE.aC
def nq:=H.aC
def nB:=ar.aI
def nD:=K.bl
def nn:=aP.cR
def oR:=aE.gY
def oy:=aP.CI
def ob:=iZ.aI
def o3:=X.bQ
def oA:=aE.Em
def oG:=br.aF
def oa:=ak.jd
def oW:=j.bH
def om:=af.jd
def oC:=aE.sk
def o4:=j.aF
def o6:=H.nh
def oY:=aP.Gg
def pc:=aw.bl
def oI:=j.bQ
def oM:=bt.eV
def pX:=L.vL
def pQ:=e_.S
def ra:=H.fF
def q8:=ci.aI
def qL:=br.ib
def Fx:=oj.ag
def qI:=bd.bm
def rA:=K.AQ
def qG:=bj.aF
def rB:=aU.kY
def rJ:=e_.bu
def qQ:=aE.eV
def qy:=aP.eP
def rG:=K.vL
def rI:=br.bQ
def q3:=b1.hK
def qp:=bq.aC
def rD:=ak.bm
def rM:=af.bm
def qb:=aw.kv
def pS:=bj.bQ
def q4:=b1.bm
def rt:=aU.bm
def q6:=H.vz
def rr:=X.bi
def qm:=L.AQ
def s7:=j.bI
def uU:=ah.bu
def uI:=aE.bQ
def ue:=K.Em
def sI:=K.bP
def uc:=j.mu
def uG:=hj.bl
def uH:=H.bl
def ty:=K.sk
def tP:=L.bl
def tb:=ak.bi
def t8:=aE.bV
def u4:=e_.cJ
def tX:=e_.fj
def tT:=cC.aI
def uD:=bd.aC
def uj:=H.gY
def tr:=H.AQ
def uL:=aP.Gp
def uk:=br.xD
def Ek:=fY.eb
def tI:=h9.aI
def ub:=aP.ae
def tS:=au.bi
def tL:=H.aI
def uu:=bd.x2
def tG:=aP.cx
def th:=b1.cJ
def t5:=au.jd
def ui:=af.bi
def tx:=bd.aD
def Eq:=bd.nR
def jm:=Av.ag
def iP:=kV.ag
def fc:=qk.cd
def kb:=yB.S
def fa:=sL.cz
def iA:=nC.a0
def dF:=BT.ag
def nx:=sL.dJ
def hR:=kt.cz
def j0:=nC.b6
def eT:=lO.b6
def iy:=Ad.eb
def j7:=xm.nR
def eI:=BI.cz
def h7:=lD.eK
def n2:=kV.dK
def gs:=o0.eK
def kQ:=lO.a0
def rk:=yB.eK
def gr:=rp.ag
def sO:=il.dK
def zl:=fk.jq
def gF:=qs.nR
def gG:=yv.b6
def Bx:=lD.gR
def eE:=nC.jr
def BX:=i4.iI
def BU:=nC.aS
def ru:=i4.fy
def pU:=Av.nR
def mU:=kt.dJ
def ud:=sL.S
def gu:=cj.bl
def BH:=xm.eP
def y4:=il.bQ
def gU:=yv.cd
def k8:=rE.eK
def ok:=qs.eP
def ti:=fk.eb
def tU:=rE.bQ
def h3:=s5.ag
def tV:=i4.aS
def zu:=fk.eP
def tW:=qk.jr
def B3:=o0.bQ
def nA:=xm.ag
def pb:=nC.cd
def od:=s5.eP
def sK:=lO.aS
def BG:=il.ag
def AF:=lD.cz
def AI:=yv.aS
def Bu:=cZ.eN
def m8:=BI.S
def jA:=Af.eb
def sQ:=cZ.aI
def jV:=ow.bl
def rf:=s5.nR
def kp:=fI.bl
def ko:=i4.jr
def j2:=Cj.S
def kj:=rE.cz
def Ei:=cZ.cz
def tA:=cZ.pk
def sU:=qs.b2
def zB:=kt.S
def wz:=o0.fj
def yG:=o0.S
def Fo:=xm.b2
def Fz:=Cj.dJ
def yx:=rp.cd
def En:=cZ.eb
def mP:=fk.dK
def BD:=qs.ag
def v0:=il.dJ
def yN:=i4.dm
def yT:=fk.a0
def BP:=il.eb
def Bw:=lD.ia
def By:=lO.cd
def q9:=lO.ec
def B9:=lO.ag
def qt:=Fx.jr
def pR:=Af.jq
def ES:=yB.fj
def E9:=cZ.S
def ER:=i4.hL
def Fu:=Av.b2
def ET:=Af.S
def t7:=dS.bl
def sP:=rC.bI
def u1:=lD.fj
def sV:=cX.bl
def tN:=cl.bl
def uN:=ed.aI
def tM:=l6.aI
def E5:=Ek.eb
def sY:=qk.fy
def u3:=ed.aO
def EJ:=il.a0
def sB:=Eq.S
def ul:=rE.fj
def ot:=jm.aI
def pe:=fc.bV
def d5:=n2.eK
def ng:=iP.e0
def Cd:=fa.eV
def k4:=sO.cd
def uB:=kb.bl
def iT:=jm.jr
def i1:=rk.b6
def jx:=iA.bl
def Au:=j0.bl
def g3:=kb.dK
def jp:=nx.aI
def hY:=kQ.ec
def j8:=h7.e0
def qM:=jm.dm
def oP:=j7.bV
def ii:=y4.ag
def o8:=zl.S
def iu:=ru.b8
def v1:=ud.bl
def i3:=fc.dJ
def BM:=Bx.bw
def lH:=pU.cz
def nm:=zu.cd
def jg:=hR.b8
def Bv:=eT.aX
def o2:=Bu.ag
def EZ:=BU.ag
def BR:=ti.cQ
def jS:=mU.fy
def EF:=BX.eV
def rH:=kb.a0
def yR:=AF.b8
def uP:=tV.S
def wR:=Ei.ae
def li:=tW.nR
def kZ:=iA.ec
def kK:=ok.cd
def E8:=fa.cd
def zY:=fc.eb
def uq:=nx.jr
def mj:=iP.a0
def EE:=BH.fj
def uQ:=Fo.cR
def l8:=B3.ag
def tF:=dF.a0
def Fp:=BX.aj
def l4:=Fz.jr
def Aw:=kb.ag
def wQ:=sK.S
def nr:=En.bi
def nt:=iy.eK
def nb:=sQ.cz
def Fm:=fa.b6
def nw:=nx.b6
def Fg:=BH.S
def wE:=iy.dJ
def m2:=dF.jr
def Ep:=BU.b2
def v6:=j0.aX
def nL:=iA.nR
def ED:=hR.cx
def zt:=eI.eb
def oi:=pb.bV
def BW:=zB.nR
def y1:=k8.bH
def n5:=iA.dK
def oN:=od.cd
def n4:=tU.ag
def pf:=iP.pk
def ox:=j0.eP
def oV:=nx.fy
def E0:=BD.fy
def yU:=jm.cd
def EY:=nA.e0
def pg:=AI.S
def oZ:=dF.e0
def Fl:=Bx.cd
def BQ:=yG.ec
def oL:=iy.aO
def oq:=yx.e0
def Fa:=BG.cR
def Ew:=iP.aj
def Ch:=rf.cx
def qW:=hR.iF
def rl:=eI.ec
def Fe:=wz.aF
def Fh:=eT.bV
def rc:=BP.b8
def Cr:=zl.cz
def BK:=Bw.cR
def pW:=dF.bP
def qh:=tA.cd
def BN:=BG.aX
def BO:=By.eK
def B1:=sU.cR
def rh:=fa.iF
def Ci:=ES.S
def rn:=yN.bg
def Ce:=E9.cR
def rj:=iy.eb
def Fi:=ER.ae
def qf:=hR.eb
def rm:=gr.dJ
def tv:=m8.dK
def ux:=gs.bH
def Er:=Fu.ag
def um:=yT.e0
def uR:=ET.bV
def tn:=nx.dm
def tk:=j7.gR
def uJ:=gG.ec
def Eh:=hR.cd
def tE:=tU.dK
def s6:=j0.cx
def E4:=gs.aD
def Fd:=gF.e0
def sD:=j7.aX
def Ey:=iP.eV
def sW:=eT.eP
def un:=AI.fj
def uy:=E5.ae
def tq:=iP.ag
def sZ:=B3.eP
def uO:=v0.S
def ut:=iP.b6
def ts:=B9.bH
def ua:=EJ.ae
def m9:=ot.S
def g9:=pe.ag
def lK:=Cd.S
def i5:=uB.cd
def wk:=BM.e0
def xl:=EZ.bi
def uE:=EF.b8
def j3:=Bv.ag
def kL:=Au.cd
def yr:=BR.S
def tp:=E8.ae
def Cv:=qM.bg
def wI:=EE.bg
def l3:=Fp.ae
def ma:=yR.dm
def lU:=ng.cz
def uY:=oP.ag
def BY:=k4.S
def Cg:=Fm.bi
def mZ:=o8.ag
def mQ:=Fg.ae
def zJ:=Ep.aF
def nE:=zY.b8
def nF:=ED.cd
def ou:=wR.ag
def n0:=E0.ag
def n7:=v1.b6
def Cb:=Aw.jq
def oK:=EY.fj
def oJ:=Fl.bi
def Co:=Fa.cd
def qc:=uP.pk
def rd:=BW.a0
def qw:=Ew.S
def qU:=Fe.cd
def rz:=Fh.ae
def qJ:=rH.e0
def qP:=BQ.S
def re:=Fi.S
def qx:=wQ.eP
def rs:=uq.bV
def qg:=jx.b6
def Fs:=o2.cd
def s0:=zt.aX
def tu:=ng.S
def tc:=nm.cx
def tO:=Er.aD
def tK:=Cr.b8
def sN:=BK.b8
def tg:=Eh.ae
def uw:=Cd.bQ
def sC:=iT.bV
def sT:=i1.eb
def uA:=E4.aF
def uh:=Fd.bi
def tl:=tF.cx
def s8:=j8.S
def sX:=uQ.S
def tw:=BN.aF
def te:=Ch.ae
def sH:=BO.eb
def uT:=yU.ec
def uW:=lH.a0
def Eu:=Ey.ae
def tD:=y1.bi
def tZ:=Ci.cx
def tz:=v1.cd
def sJ:=v6.ag
def uf:=B1.S
def sR:=Au.aI
def t0:=Ce.bg
def uZ:=wE.aD
def uC:=jp.cz
def lW:=wk.S
def l9:=Cv.ag
def m1:=xl.b8
def na:=yr.ag
def os:=BY.bV
def oX:=Cg.S
def oU:=uE.cd
def BS:=lK.ag
def qe:=m9.eb
def q7:=Cb.ag
def pZ:=wI.ag
def qX:=Co.S
def rq:=zJ.cd
def qn:=tp.e0
def rK:=Fs.e0
def s9:=m9.ag
def sE:=Eu.S
def El:=uY.cd
def pH:=BS.b8
def tC:=El.cd
def zD a1 a2 a3:=DG a1 a2 a3 e_
def zb a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 e_
def km a1:=Dm cD Gb a1
def yC a1:=eU cD kD a1
def zf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 a8 a9 a7 a10
def oe a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 e_
def y5 a1:=zj cD DA a1
def Al a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 e_
def zV a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 a9
def zI a1:=Dm cD A7 a1
def Cq a1:=eU cD vR a1
def zz a1 a2 a3 a4 a5 a6 a7 a8:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 e_ a7 a8 e_
def AG a1:=eU cD FP a1
def yy a1 a2 a3 a4 a5 a6:=eX a1 a2 a3 e_ a2 a4 e_ a2 a3 aP a5 a6 e_
def zT a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 a4 a5 a6 e_ a7 a8 e_
def zX a1:=eU cF f7 a1
def zd a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a4 a5 e_ a2 a3 aP a6 a7 e_
def zs a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 e_
def wP a1:=eU cD hI a1
def yA a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a8 e_
def zF a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 e_
def zn a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a5 a8
def BF a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a5 e_ a6 a7 e_
def wl a1:=eU cF fB a1
def Az a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a6 a9
def AB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 a10
def zq a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 b1 a2 a3 aP a6 a7 a8
def Ay a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 e_ a2 a3 a4 a5 a6 a7 a8 a6 a9
def Cf a1:=eU cF nP a1
def zv a1:=eU cF dE a1
def pI a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a8 bd
def wp a1:=eU cD dE a1
def q0 a1:=Dm cD DA a1
def Ca a1:=eU cD FW a1
def qj a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 e_ a4 a5 a6 a7 a5 a8
def zO a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 a9
def E1 a1 a2 a3 a4:=F7 a1 a2 a3 a4 e_
def zo a1:=zj cD Ga a1
def w4 a1:=eU cD fB a1
def m0 a1 a2 a3 a4 a5 a6 a7:=dH a1 b1 a2 a3 e_ a4 a5 e_ a6 a7 e_
def oh a1 a2 a3 a4 a5 a6 a7 a8 a9:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a9 e_
def w7 a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 e_
def uM a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 a9 a10 a8 a11
def oO a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 bd
def pO a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 e_ a4 a5 a6 a7 a8 bd
def Ff a1:=eU cD mD a1
def lB a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 e_ a7 a8 e_
def BC a1:=eU cD f7 a1
def ro a1:=zj cD Gb a1
def oB a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 a7 a8 a6 a9
def oS a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a2 a4 e_ a5 a6 e_ a7 a8 a9
def oD a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a5 a8
def nI a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 a8 a9 a7 a10
def oH a1 a2 a3 a4 a5:=FF a1 aP a2 a3 e_ a4 a5 e_
def Fb a1:=Dm cD Ga a1
def jo a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 a10
def wB a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 e_ a2 a3 aP a6 a7 a8
def jB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 a9 a10 a11 e_
def Ck a1:=eU cF vR a1
def Aj a1:=eU cD nP a1
def zL a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a4 a5 b1 a2 a3 aP a6 a7 e_
def lz a1:=eU cF kD a1
def lL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 a11
def wH a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 e_ a6 a7 e_ a8 a9 e_
def lZ a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a3 aP a5 a6 a7
def l5 a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 a8
def EU a1:=eU cD vk a1
def Fw a1:=eU cD Dq a1
def Et a1:=zj cD A7 a1
def pd a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 bd
def ov a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a5 a8
def pj a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 a11
def rx a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 bd a6 a7 e_
def EI a1:=eU cD Ev a1
def qK a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 e_ a4 a5 e_ a6 a7 aP
def rL a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 e_ a2 a3 a4 a5 a6 e_ a7 a3 a8
def qa a1 a2 a3 a4:=rP a1 iC a2 a3 (aM cD dE e_) a4 (aM cF dE e_) b1
def Eo a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 e_ a2 a6 e_ a7 a8 e_
def q1 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a5 a8 a9 a5 a10
def qN a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 aP a4 a5 a6 a7 a5 a8
def qS a1 a2 a3 a4 a5 a6 a7 a8:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 a4 a8 a7 a5
def qz a1:=eU cF hI a1
def pV a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 e_
def qo a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 a7 a8 a6 a4
def Es a1:=eU cF Ft a1
def pN a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 a4 a2 a3 a5 a2 a3 a6 a7 a3 a8
def tJ a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a9 aP
def tR a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a6 e_ a7 a3 a8
def uS a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a8 aP
def tB a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 a4 a5 a3 a6 a7 a3 a8
def sG a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=eX a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a5 a10
def xu a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a3 a7 a8 a3 a9
def w9 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 e_ a6 a7 a8 a9 a10 e_
def wJ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=jL a1 a2 a3 e_ a4 a5 a6 a7 a8 e_ a9 a10 aP
def wx a1 a2 a3 a4 a5 a6 a7 a8:=dH a1 bd a2 a3 bd a4 a5 a6 a7 a8 e_
def wA a1 a2 a3 a4 a5 a6 a7 a8:=eX a1 a2 a3 e_ a4 a5 a6 a2 a3 aP a7 a8 bd
def yD a1 a2 a3 a4 a5 a6 a7:=dH a1 bd a2 a3 e_ a4 a5 e_ a6 a7 aP
def zg a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 e_ a4 a5 bd a6 a7 e_ a8 a9 e_
def yF a1 a2 a3 a4 a5 a6 a7 a8 a9:=eX a1 a2 a3 e_ a4 a5 a6 a2 a7 e_ a8 a9 e_
def yu a1 a2 a3 a4 a5 a6 a7:=eX a1 a2 a3 e_ a2 a4 e_ a2 a5 e_ a6 a7 bd
def yq a1 a2 a3 a4 a5 a6 a7:=dH a1 e_ a2 a3 bd a4 a5 e_ a6 a7 e_
def zS a1 a2 a3 a4 a5 a6 a7 a8 a9:=jL a1 a2 a3 a4 a2 a3 a5 a6 a7 e_ a8 a3 a9
def At a1 a2 a3 a4:=rP a1 iC a2 a3 (aM cD nP e_) a4 (aM cF nP e_) e_
def yw a1 a2 a3:=rP a1 iC xY a2 (aM cD f7 e_) a3 (aM cF f7 e_) b1
def ac a1 a2 a3:=lf (zD a1 a2 a3)
def al a1:=lf (km a1)
def aG a1:=lf (y5 a1)
def aK a1:=lf (yC a1)
def aT a1 a2 a3 a4 a5 a6 a7:=lf (zb a1 a2 a3 a4 a5 a6 a7)
def bk a1:=lf (Cq a1)
def bC a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (zf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def bM a1 a2 a3 a4 a5 a6 a7 a8:=lf (Al a1 a2 a3 a4 a5 a6 a7 a8)
def bZ a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zV a1 a2 a3 a4 a5 a6 a7 a8 a9)
def co a1:=lf (wp a1)
def cp a1 a2 a3 a4 a5 a6:=lf (yy a1 a2 a3 a4 a5 a6)
def dc a1:=lf (wl a1)
def dd a1 a2 a3 a4:=lf (E1 a1 a2 a3 a4)
def d2 a1:=lf (Cf a1)
def em a1 a2 a3 a4 a5 a6 a7 a8:=lf (zz a1 a2 a3 a4 a5 a6 a7 a8)
def eo a1 a2 a3 a4 a5 a6 a7 a8:=lf (yA a1 a2 a3 a4 a5 a6 a7 a8)
def e8 a1 a2 a3 a4 a5 a6 a7 a8:=lf (pI a1 a2 a3 a4 a5 a6 a7 a8)
def ff a1 a2 a3 a4 a5 a6 a7:=lf (zd a1 a2 a3 a4 a5 a6 a7)
def fb a1 a2 a3:=lf (eU a1 a2 a3)
def e5 a1 a2 a3 a4 a5 a6 a7 a8:=lf (qj a1 a2 a3 a4 a5 a6 a7 a8)
def fW a1:=lf (Ff a1)
def fJ a1:=lf (zI a1)
def g4 a1 a2 a3 a4 a5 a6 a7:=lf (oe a1 a2 a3 a4 a5 a6 a7)
def g1 a1 a2 a3 a4 a5 a6 a7 a8:=lf (zq a1 a2 a3 a4 a5 a6 a7 a8)
def hZ a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13:=lf (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13)
def hT a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (Az a1 a2 a3 a4 a5 a6 a7 a8 a9)
def h6 a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (oh a1 a2 a3 a4 a5 a6 a7 a8 a9)
def ij a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (Ay a1 a2 a3 a4 a5 a6 a7 a8 a9)
def iR a1 a2 a3 a4 a5 a6 a7 a8:=lf (zT a1 a2 a3 a4 a5 a6 a7 a8)
def i7 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (AB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def iO a1 a2 a3 a4:=lf (DG a1 a2 a3 a4)
def iM a1:=lf (w4 a1)
def iL a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zs a1 a2 a3 a4 a5 a6 a7 a8 a9)
def ji a1:=lf (Fb a1)
def kf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=lf (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
def lb a1:=lf (AG a1)
def lc a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zF a1 a2 a3 a4 a5 a6 a7 a8 a9)
def lg a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (zO a1 a2 a3 a4 a5 a6 a7 a8 a9)
def la a1 a2 a3 a4 a5 a6 a7:=lf (BF a1 a2 a3 a4 a5 a6 a7)
def ms a1:=lf (BC a1)
def ml a1:=lf (zX a1)
def ly a1:=lf (Aj a1)
def mg a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11:=lf (uM a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11)
def mb a1 a2 a3 a4 a5 a6 a7 a8:=lf (zn a1 a2 a3 a4 a5 a6 a7 a8)
def nz a1 a2 a3 a4 a5 a6 a7 a8 a9:=lf (oB a1 a2 a3 a4 a5 a6 a7 a8 a9)
def n3 a1:=lf (Et a1)
def o9 a1:=lf (Ca a1)
def qY a1 a2 a3 a4 a5:=lf (F7 a1 a2 a3 a4 a5)
def pL a1 a2 a3 a4 a5 a6 a7 a8:=lf (pO a1 a2 a3 a4 a5 a6 a7 a8)
def ql a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:=lf (nI a1 a2 a3 a4 a5 a6 a7 a8 a9 a10)
def J a1 a2 a3 l:=aZ (zD a1 a2 a3) l
def aW a1 l:=aZ (km a1) l
def bA a1 a2 a3 a4 a5 a6 a7 l:=aZ (zb a1 a2 a3 a4 a5 a6 a7) l
def bD a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l:=aZ (zf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l
def bT a1 a2 a3 a4 l:=aZ (DG a1 a2 a3 a4) l
def ck a1 l:=aZ (y5 a1) l
def de a1 l:=aZ (yC a1) l
def du a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zV a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def dG a1 l:=aZ (zX a1) l
def ek a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zT a1 a2 a3 a4 a5 a6 a7 a8) l
def en a1 l:=aZ (Cq a1) l
def ej a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zs a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def eG a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (Al a1 a2 a3 a4 a5 a6 a7 a8) l
def e9 a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zz a1 a2 a3 a4 a5 a6 a7 a8) l
def fh a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l:=aZ (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l
def fS a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zn a1 a2 a3 a4 a5 a6 a7 a8) l
def fO a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (yA a1 a2 a3 a4 a5 a6 a7 a8) l
def fV a1 a2 a3 a4 a5 a6 a7 l:=aZ (oe a1 a2 a3 a4 a5 a6 a7) l
def gz a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (Az a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def gy a1 l:=aZ (zI a1) l
def gV a1 a2 a3 a4 a5 a6 a7 l:=aZ (zd a1 a2 a3 a4 a5 a6 a7) l
def gW a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l:=aZ (AB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l
def hX a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (zq a1 a2 a3 a4 a5 a6 a7 a8) l
def iw a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (Ay a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def ix a1 l:=aZ (Cf a1) l
def ir a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zF a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def jz a1 l:=aZ (wl a1) l
def jW a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (zO a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def j4 a1 l:=aZ (ro a1) l
def kh a1 a2 a3 a4 a5 a6 l:=aZ (yy a1 a2 a3 a4 a5 a6) l
def kN a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (pI a1 a2 a3 a4 a5 a6 a7 a8) l
def k3 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l:=aZ (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l
def md a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (w7 a1 a2 a3 a4 a5 a6 a7 a8) l
def mR a1 a2 a3 a4 a5 a6 a7 a8 l:=aZ (pO a1 a2 a3 a4 a5 a6 a7 a8) l
def m5 a1 l:=aZ (w4 a1) l
def ns a1 a2 a3 a4 a5 a6 a7 l:=aZ (oO a1 a2 a3 a4 a5 a6 a7) l
def nc a1 a2 a3 a4 a5 a6 a7 l:=aZ (zL a1 a2 a3 a4 a5 a6 a7) l
def o7 a1 a2 a3 a4 a5 a6 a7 a8 a9 l:=aZ (oS a1 a2 a3 a4 a5 a6 a7 a8 a9) l
def oc a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l:=aZ (uM a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l
def N a1 a2 a3 l r:=nd (zD a1 a2 a3) l r
def az a1 a2 a3 a4 a5 a6 a7 l r:=nd (oe a1 a2 a3 a4 a5 a6 a7) l r
def aJ a1 a2 a3 a4 a5 a6 a7 l r:=nd (zb a1 a2 a3 a4 a5 a6 a7) l r
def aR a1 l r:=nd (wP a1) l r
def bc a1 l r:=nd (AG a1) l r
def bU a1 l r:=nd (zI a1) l r
def bS a1 l r:=nd (zv a1) l r
def cb a1 a2 a3 a4 a5 a6 a7 l r:=nd (BF a1 a2 a3 a4 a5 a6 a7) l r
def cu a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (Al a1 a2 a3 a4 a5 a6 a7 a8) l r
def c3 a1 l r:=nd (q0 a1) l r
def dQ a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zF a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def dR a1 l r:=nd (Ca a1) l r
def d3 a1 l r:=nd (zo a1) l r
def ef a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l r:=nd (zf a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l r
def ei a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zz a1 a2 a3 a4 a5 a6 a7 a8) l r
def eg a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zT a1 a2 a3 a4 a5 a6 a7 a8) l r
def eL a1 l r:=nd (zX a1) l r
def eR a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 l r:=nd (dH a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) l r
def eJ a1 l r:=nd (yC a1) l r
def e2 a1 a2 a3 a4 l r:=nd (DG a1 a2 a3 a4) l r
def fR a1 a2 a3 a4 a5 a6 a7 l r:=nd (zd a1 a2 a3 a4 a5 a6 a7) l r
def gA a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zV a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def gp a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zs a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def gI a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zn a1 a2 a3 a4 a5 a6 a7 a8) l r
def hi a1 a2 a3 a4 a5 a6 l r:=nd (yy a1 a2 a3 a4 a5 a6) l r
def hS a1 a2 a3 a4 a5 a6 a7 l r:=nd (m0 a1 a2 a3 a4 a5 a6 a7) l r
def im a1 l r:=nd (km a1) l r
def ku a1 l r:=nd (Ck a1) l r
def lj a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l r:=nd (jL a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l r
def k2 a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (lB a1 a2 a3 a4 a5 a6 a7 a8) l r
def lQ a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (yA a1 a2 a3 a4 a5 a6 a7 a8) l r
def lE a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (wB a1 a2 a3 a4 a5 a6 a7 a8) l r
def mi a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 l r:=nd (eX a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13) l r
def lY a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (w7 a1 a2 a3 a4 a5 a6 a7 a8) l r
def lC a1 a2 a3 l r:=nd (eU a1 a2 a3) l r
def m6 a1 l r:=nd (EU a1) l r
def mV a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 l r:=nd (AB a1 a2 a3 a4 a5 a6 a7 a8 a9 a10) l r
def nl a1 l r:=nd (Fw a1) l r
def nv a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (Ay a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def op a1 l r:=nd (BC a1) l r
def o1 a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (Az a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def oT a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (oD a1 a2 a3 a4 a5 a6 a7 a8) l r
def ol a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (zO a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def ph a1 a2 a3 a4 a5 l r:=nd (oH a1 a2 a3 a4 a5) l r
def qR a1 l r:=nd (EI a1) l r
def pK a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (Eo a1 a2 a3 a4 a5 a6 a7 a8) l r
def qq a1 a2 a3 a4 a5 a6 a7 a8 a9 l r:=nd (wH a1 a2 a3 a4 a5 a6 a7 a8 a9) l r
def ry a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (qj a1 a2 a3 a4 a5 a6 a7 a8) l r
def qu a1 l r:=nd (Es a1) l r
def qv a1 a2 a3 a4 a5 a6 a7 l r:=nd (oO a1 a2 a3 a4 a5 a6 a7) l r
def qd a1 a2 a3 a4 a5 a6 a7 a8 l r:=nd (zq a1 a2 a3 a4 a5 a6 a7 a8) l r
def pP a1 l r:=nd (y5 a1) l r
def Ez : ab dp:=(op gx (d3 cl (eL aP.Fy.aF (cb i3.b8 49 z3.f4 z3.fE z3.fD 1 z3.fu (az tv.jq 4 z4.eB 87 z6.eA 83 z7.fu (N gS.i0.bo 69 cy.fu (iR m1.b8 87 bN b1.g8 1 dI.fo 2 dI.fU) (ji iD)) (e9 hY.cQ.cQ 60 da.f6 da.fP 49 da.gK 46 da.fp (bM kL.fH.bw 178 ap aE.eC.d6 K.eC.d6 L.eC.d6 19 dL.er))) (bU bO.bu (J aY.iG.hU.gT 83 dy.gd (em ng.cx.fj.cQ 145 ds.fm vb 88 ds.gm 84 vg)) (du rp.dK.cQ.fj.S 171 zm au X ad 92 mG aN (bk jV)))) (bc ed.eV (nd (tJ gs.aI.gZ 156 an cg.iV b3.iV 72 z9.fz 60 z7.p7) (N b1.bg.pT.hK.dh 57 ct.gK (aG jV.fQ) (lb dO.S)) (iw pU.dJ.cR.dm.aX 89 mG L 172 cV.er ar 168 ao (bk jk))) (hi tV.ia.aj 52 B4 cM.fm 95 uz (aW nK.aD (n3 bq.ae.bV.aS)) (J i6.iv.bm.dx 164 c8.eA (lf (pd nr.bV 24 dq.fK 100 cT.p7 H 26 dq.fN 54 dq.f4)))))) (N ed.eV.dK.fy 139 z2.f6 (bU iX (gA tv.it 122 AA jv dk e6 103 se lR (N iE.yb.hU.bo 189 cV.gk (d2 pX.vv.bm) (dc aV)) (fh na e_ 64 ch jH 1 di.fA e_ 2 cB.gn bd (bC os.b2.b2.aj 199 ap cX.bP.bP.av cl.bP.bP.av 145 ey cg.bQ.cv 141 b3.bQ.cv))) (bc pQ (bD ii.aX.aj 91 fe bF bE 74 zr K 70 L (ij dF.jq.b2.ae.cQ 70 wK aH 176 u5 oR 172 oy)) (e9 s0.cs 75 cI.hH cI.gL 184 cI.p9 180 cI.p8 (aT nr.dJ 11 cT.ev 1 cT.eZ 2 cT.fo)))) (az mj 38 mF 115 iq 14 z6.gK (N FS.G2.iI.cx 282 dn.f6 (mR oi.b2.b2 4 cy.e1 65 ct.p0 H 61 hJ (co j.v9.bl.ec)) (aZ (rx j8.fH.dm 11 c7.p9 1 c7.fE 2 cN.gk) (ms jT))) (ef tu.aj 125 et aY aQ 66 hC ak 62 af (jW tc.aS 11 dP.p6 83 c9.p5 aE 94 fe e_.ja (bM lW.ag.bw 113 bv ob.aO iY.jQ mW.jQ 19 dl.eS)) (de K.cJ.kY.ib.fr (cp jA.eb.ag.iI 113 dY.ev dY.eZ 272 dY.fT)))))) (bc cC (cb ux.bw 54 z1.fq z1.gb z1.gd 19 z1.fM (bS nJ.bm (cu nt.dm.bw 93 se g5 gq k6 19 z7.fx (im e_.e0.mX (aK bt.io) (lf (rP rv.dJ.jr wN Bq 28 (aM cD mD e_) 105 (aM cF mD e_) aP))) (fS oi.b2.a0.ae 272 c7.f4 136 sg ar 132 ao (bZ o8.eP.cd.ag.bg 186 ap dO.nh.fj.bI cj.nh.fj.bI dS.nh.fj.bI 200 wZ bt))) (ef gs.iI.bV.aj 139 pA cX cl 88 fG jt.aD 84 gX.aD (kN qc.S 86 hJ ci aV cC 111 yg (bM rd.eP.aF 180 b7 fI.ja.ae ra.ja.ae s7.ja.ae 1 ds.f5)) (mR tO.bQ.b2 4 cI.fE 148 cS.ex H 144 l0 (ac aN.iG.eD.aI 286 cT.eS)))) (c3 bF.aF (o1 qw.nR.S 110 an vS.ce 116 c4 uU 112 aU.bu (aZ (yD jg.bp 63 pp 126 pz 122 Ai) (aK kO.io)) (aZ (yD i5.dK.ja 4 da.fN 47 da.fK 44 va) (nz Ch.S 57 cL.f4 cL.fE 87 mH aV 83 cC))) (aJ um.bQ 52 cq.fu 17 cq.gO 61 cq.ev (o7 nb.gR.bw 270 dP.fm dP.gH 17 dP.er 218 hC j.ae (aG pX.eK.ce)) (fO nr.cz.S 108 we 70 c8.ex H 66 cN.f4 (lf (rP eE sc Bt 24 (aM cD dE e_) 65 (aM cF dE e_) b1)))))) (c3 m3 (qR ah (eR qW.S.a0 e_ 66 z8.fo e_ 107 an uI.mv 14 z8.eZ aP (fR oi.b2.bl 33 vi 32 cB.fz 1 cB.gl (ac e_.aO.bP.dt 334 dr.fz) (qY cZ.b6 aB 71 rQ au)) (J ci.xF.r4.eF 171 c7.fM (bk kn))) (oT s5.b2.cR.S 95 cG.e7 57 po X 53 ad (bA k4.cx.dJ 11 dj.fK 1 dj.fN 2 dj.ex (iR oX.ag.ag 110 bv e_.aO.aO 1 dT.p5 2 dT.p4)) (J q8.aO.bP.eV.dK.fy 134 c8.fT (ac e3.eC.bu.bz 223 dq.eY)))) (gp o0.gR.bw 42 kA bj br 17 z6.gm 361 z6.p1 (ei fk.ag.aF.bw 52 dn.fq w3 17 dn.gn 129 dn.p4 (aZ (zg ou 226 dP.p0 54 wG 1 dy.gO 2 dy.ev) (ml nk.aI.cH)) (ek rl.bV.aF.b8 121 lJ kW 1 cN.f9 2 cN.ga (bk jX))) (ef q9.bw.e0.ae 64 sa cX cl 169 cP.p1 K 165 L (aZ (oD m1.jr 4 cA.fq 87 bN H.dK.bI 83 j.hL.bI) (bM lW.fH 117 bv o3.aO hW.bQ.aO ld.bQ.aO 1 dL.fp)) (e9 B9.aS.cQ.cs 245 dI.eW dI.eH 417 dI.f8 413 dI.fz (lb qL.bg)))))))
def Fv : ab dp:=(hS gU.aX 122 d1 89 FE 194 Gj (nd (rP qt sc Bq 28 (aM cD hI e_) 105 (aM cF hI e_) aP) (cu eT.gC 252 iJ dO cj dS 56 z1.fK (nd (oB hR.cz.S 128 z3.gl z3.e1 55 dX X 51 ad) (aJ nt.dm.dm 11 z7.fN 1 z7.ex 2 z7.fL (nd (lz uI.bl) (bk oy.ae.eh) (ji kr)) (mR jg.aS.aF.aS 4 da.er 501 mJ K.cR 134 c7.fU (ac ob.pD.eP.aI.db 109 dL.gd))) (nd (oS k8.dJ.bw 50 c5.fA wn 17 c5.fK 509 iz kJ.sx) (aW kS.nS (co H.kB.aF.ec)) (ix mE.pl.bm (lc hY.bQ 23 cU.gl 24 cU.e1 17 cU.gk 115 cU.eA)))) (ei ru.iF.aj 124 z5.f8 z5.fz 69 z5.gl 65 z5.e1 (nd (ov qU.aj 23 z9.ex 138 c4 au.eN 112 kc) (J X.cH.hU.gT 172 cV.fo (aK ar.cJ.kY.ib.fr)) (ek ok.aS.ae.ag 65 pp jN 1 cA.p5 2 cA.p4 (aT y1.dm 11 dM.fL 1 dM.gg 2 dM.eY))) (N gN.pT.hK.dh 55 cM.eH (k3 ok.aS.ae.a0 371 ky fX 65 dP.fD e_ 146 pz aE 14 da.eW aP (bZ tO.bQ.ho 75 yk oA ue L.Em 164 l0 kc)) (en h9.bg.hK (bk nG.gY))))) (eL K (cb rf.it 148 z4.fz z4.gl z4.e1 57 z4.gk (m6 gN.S (N L.bu.dt 334 cV.p7 (pL rf.ec.aI.ja 4 dI.p4 145 c0.fi H 141 c0.er) (lf (q0 eQ.bI))) (k3 De.fj.cx.bi.cx.aD 185 cN.ez e_ 587 cN.gg e_ 128 iz dN.fr.iH 62 di.f8 j (aT lH.eb.ag 55 cO.ga 1 cO.gj 2 cO.f5))) (nd (pO mP.aO.b2 4 cG.eS 92 cG.fi H 88 v8) (aZ (qK zl.cx.bp 138 dj.fi 60 dj.eW 56 di.gK) (bM jg.cd.gR.ag 89 iK aV.wj nJ.wj qI.wj 1 dT.fT)) (aZ (lL li.aj.cR.bV 24 c8.fD 207 cI.fU H 26 c8.fu 69 rY aN) (al ke)))) (d3 lq (eJ sI.gY (J rA.aI.hV 72 cB.fE (eo kZ.dJ.bp 68 dr.f8 286 u5 e_.bP 53 ds.p2)) (ck mq.sx.ni (fW g7))) (aJ i5.dJ 11 cP.fp 1 cP.ft 2 cP.f4 (ck ed.gP.ni (al ah.rF.bH.bH)) (bA uR.aF.bi.b8 77 c7.ez 1 c7.fK 2 c7.fN (co aQ.bg.eK)))))) (aR bj.eK (aR gu (bU uc (lQ nt.iI.a0 97 z8.fE 134 zR aE 14 z8.fD (op oG.xF (hZ g9.aS.a0 87 iK dN.wj 87 iK ie.wj 158 et dV.bP 14 da.p9 aP) (al e4)) (iw kK.S.cQ 69 iK aH 132 et oR 128 oy (lf (tR mZ.bH.b6.aX 186 ap uc.av 29 dL.gL 206 uG.av)))) (az tn.bg 34 c5.p6 47 po 96 cG.fu (bA nb.eK.b8 57 c9.eS 1 c9.fm 2 c9.gH (al kO.kv.aX)) (ir jS.aS.ag.aS 11 cI.fK 214 c8.eB 123 cI.fN 119 cI.ex (aK ci.bp)))) (bS oa.bu (gI rz.ag.aS 4 z9.eS 108 an uH.b0 104 oW.b0 (bA tk.ik 11 ct.f5 1 ct.hH 2 ct.gL (fJ aA.ib.iG.eC)) (J aN.aI.bV.fd 159 c7.gm (e8 BP.S 68 zw au X ad 49 dM.eA))) (nd (jo uB.aI.aD 177 cP.eB 420 cy.fC 143 cP.fT 60 cM.eW j) (J bt.hL.aI.hV 73 dP.f9 (bC oU.cs 87 ch qG.aC oG.aC 122 bv mY.aO 118 iQ.aO)) (e9 n5.e0.cJ.ag.bw 112 c7.fi c7.eW 17 c7.eH 193 c7.f8 (ac iS.bi.hL.dx 156 dY.f6))))) (N sI.dh 53 z2.ga (cb nw.ag.bw 91 z4.p4 z4.p3 z4.p2 19 z4.p1 (ef iy.gR.cd.bi.aD 106 nX oa om 87 pv fX 83 d8 (dQ Cg.bQ 82 cB.eS 220 dj.fz 17 cB.fm 59 cB.gH (hT fc.cz.dK.S.S 178 b7 bt.nh.ae 77 u6 X 73 ad) (dd yG aB 71 b7)) (m5 iQ.bu (bM mU.dm.bw 47 rO aA aB dD 19 dM.e1))) (gI rc.ae 91 cG.er 61 xn K 57 L (bT ki.yd.hM.bu.dK.fy 112 iB ki.Eb.kB (h6 i5.aj.b2.a0 195 jK bq 169 mK gf 14 c6.e1)) (du eT.cd.e0.b8.bg 131 iq H.kY.bg.jd mT.bg.jd rB.bg.jd 80 ep i6.pD.n1 (ff jS.ag.bw 157 dq.fz 314 dq.p9 19 dq.gl)))) (bc H.ec (lE gF.gR.aS 11 dn.p2 144 pA 71 fG fY.bw (gV wI.bl 84 dy.eB 228 di.eu 1 cy.gL (bM i4.b6.aj.cQ.g6 134 w2 ah bK ea 1 dT.fM)) (gz mQ.cs 73 ca t7 92 bN m4.bI 88 sP (kf kt.cx.bp e_ 51 tH bd 88 xa K 84 xa L))) (az rk.pk.ae.aj 60 sa 165 v7 161 cP.p1 (bT jD.kY.sx.cJ.aO.aO 500 tj cl (bZ kL.bV.b2.aj 178 ap oC.hL.bI ty.hL.bI L.sk.hL.bI 128 ve aw)) (fS uJ.e0.bg.S 64 cN.gj 126 lJ cj 122 dS (lf (rP eE iC xY 24 (aM cD dE e_) 65 (aM cF dE e_) b1))))))))
def Fn : ab dp:=(nd (kH L) (bc d0 (aR j5.bP (aR tP (nd (uM gF.aX.aC 11 z7.gl 77 kA hj.gP 53 mc aE.fF 49 aP.cH) (nd (jB jg.aX.aC 11 cy.eB 383 ap kP.CI 364 iB lq.bH.kB 122 cy.fT) (hZ tK.cd.iF 11 dI.gn e_ 147 dI.eA e_ 120 hD dN.aO 17 cN.eB bd) (ji m3)) (bT d8.kv.pT.hK.dh 305 ky d8 (lf (w7 eI.b8.dm.cJ.ag.bw 135 dL.eW 438 ap iN.eK.av 19 dL.eH)))) (bS gu (bT e_.bi.r4.Gp.bm.bz 146 ep bt.cJ.ja (eo oN.dJ.S.a0 91 ds.gO 282 yK aE 14 c6.gK)) (fO d5.eN.S.a0 74 cS.gO 88 Aa aE 14 cS.f5 (e8 rk.cd.dB 133 r9 nj g2 kg 64 cU.f4)))) (nd (kH aQ) (bS h9.EQ.FI (J oj.cH.hU.gT 365 cV.fP (d2 mh.vv.bm)) (ck ed.ec.aC (aT cZ.ik 11 dM.er 1 dM.eB 2 dM.fT))) (N e3.aO.hU.bo 548 c9.fi (aZ (lB sK.cx.aF.ae 123 cq.eA L 535 cS.gn 532 cS.eA) (n3 kx.ae.bV.aS)) (bD jS.bH.bi.ae 179 wU K L 75 rY ar 71 ao (i7 sN.bw 58 vd jw jD 17 dq.gb 90 sb bO))))) (dR tb (aJ k8.dv 54 z4.e7 149 z4.eH 145 z4.f8 (hi nt.iI.ag 97 z8.gg z8.eY 1 z8.eS (fR n4.b6 54 ct.p2 133 cV.f5 1 ct.p1 (ac d4.bi.cJ.aO.aO 585 dT.gb) (lf (m0 tg 224 d1.fo 121 d1.fu 200 d1.f8))) (ej k8.dJ.cJ.ae 58 yz K L 226 cA.e1 222 cA.gk (aT nx.cd.ag 47 cO.fA 1 cO.eu 2 cO.ez))) (ei uQ.bQ 87 xw cG.er 17 cG.eB 53 xn (bA tE.b6.dm 11 dj.f6 1 dj.fP 2 dj.gK (i7 uw.ag.g0 233 ch bF.bV bE.bV 17 dT.fK 109 hD lT.pF)) (bA qk.dm.cd.aX.bl.b8 150 cI.p2 1 cI.p1 2 cI.p0 (g4 wE.aI.cQ 99 cT.gk 57 cT.er 53 cT.eB)))) (nd (zj cF A7 C2) (N kJ.mu.bo 55 dn.e1 (aW rJ.bH (lf (jo kV.a0.aj.cR.cx.aD 199 ds.fM 272 ds.fx 243 ds.gn 74 dr.fu j))) (bA uJ.bQ.bP 140 c0.fi 1 c0.eW 2 c0.eH (bk jT))) (N cj.r4.ib.bo 614 cV.fT (J d0.r4.eF 164 cA.fE (al m4.bH.bH)) (o7 s6.bg.eP.S 72 c7.p8 c7.p7 110 yI 106 v2 j (fW kP.cx.bu)))))) (az j7.dJ.S.ae 71 Gf 134 Hb 130 z1.e7 (cb sC.ag 59 z1.f9 z1.ga z1.gj 1 z1.f5 (bU bd.b6 (N aP.Fy.ae.pF.cw 78 z7.p4 (mi od.dm.bg 36 cy.ga e_ 91 cy.gj e_ 38 cy.f5 e_ 53 mL bd (aG ah.AQ.sx.ni) (em i1.a0 44 d1.gK d1.fp 175 d9.gd 14 d9.fM)) (eG nm.bl.bw 116 fe g5 gq k6 19 da.fq (aG aN.bm.fr.gB))) (eJ K.GB.cJ.fr (aZ (lz aU.cY) (ac ah.hU.bP.dt 334 dT.p3)) (aZ (uS sT.aX.b2 4 cS.ft 202 cS.fC H 198 cS.fz) (al fX)))) (ei pf.eb.aD 131 z5.f9 z5.ga 177 z5.gj 38 z5.f5 (nd (rL g3.aX.bP.aX 96 an af.ia.aS 29 z9.gj 116 oo.b0) (fV nm.q5.aj 16 ct.fM 112 ct.fx 268 cV.eY (bC xl.bg.aj 68 ca jl.bI ju.bI 91 bN nq.cH 87 mh.cH)) (eG ii.fH 121 fe ed nk j.aI 1 cN.gd (bM ux.bw 54 mF jX kp iD.bl 19 cL.gm))) (ef ox.fg 124 cq.eH K L 64 v8 ak 60 af (aZ (oB mZ.aD 60 dP.gb dP.gd 170 ap ak.cx 166 af.cx) (d2 gq.aI.pl.bm)) (de qQ.gY.gD (lg s0.aC 11 dq.p4 182 hB iN.x2 63 dq.gm aw))))) (ei j0.a0 36 z2.fq z2.gl 95 z2.gb 14 z2.gd (cb nw.ag.dm 114 z4.ga z4.gj z4.f5 1 z4.hH (oT j3.jr 4 z8.p9 106 c4 bK 102 ea (mV od.jr.cx.bw 99 mf cX cl 17 cB.eu 65 vm bO (lf (tR fc.cz.dK.cz.aX 178 b7 L.ja.ae 29 ds.gg 198 aH.cK)) (qY dF.b6 aB 111 rW au)) (bA kL.bP.aX 130 di.eY 29 cA.eA 161 cA.f9 (bM qM.bw 43 ep aA aB dD 19 dM.f8))) (aJ rc.b6 95 uv 1 cM.gO 2 cM.ev (fh od.dm.cJ.aX bd 61 sj L 29 dj.fm e_ 81 mM aH (aT qe.b6.dm 11 dT.eA 1 dT.f9 2 dT.ga)) (j4 bF.bi.bu (aT jS.ag.dm 11 cT.gn 1 cT.eA 2 cT.f9)))) (aJ iP.cz.b8 69 z6.fM 1 z6.fx 2 z6.gn (N nK.iH.ib.bz 64 dn.hH (J aY.gP.cJ.aO.aO 221 dj.e1 (aK ki.eC.gD)) (kN k4.gZ 69 rU au X ad 140 cA.gm (fW kp))) (op o4.xF (e9 d5.gC.aj 70 di.fx di.gn 122 di.eA 118 di.f9 (dc ju.i2)) (de g5.kY.ib.fr (lf (zv H))))))))
def E2 : ab dp:=(eL aU (aR vN.eK (aJ mj.eb.aX 62 z1.fT 41 z1.fA 138 z1.eu (bS iZ.bm (aJ i3.e0.eK 61 u0 1 z7.gH 2 z7.gm (mV pR.eV.b8.bw 166 yV ak af 17 cy.gm 77 mG h9 (aK oR.io) (la kQ.ag 40 d9.fK d9.fN d9.ex 1 d9.fL)) (dG oo.e0.cH (lf (xu o8.eP.jr.ae.aj 178 ap ar.bg.hM.fF ao.bg.hM.fF 240 ak.aC.fj.bI 236 af.aC.fj.bI)))) (e2 K.AZ.bi.cJ.aO.aO 330 iz ak.kY.sx (fV pW.b2.ae 128 dP.f6 165 c9.gO 367 dP.fP (fJ jZ.vr.aI)) (ix qy.Cn.bm (lf (rx iu.b8 51 cU.ez 1 cU.fT 2 cU.fK))))) (nd (zj cF A7 b4) (nd (qa eE xy 24 65) (aW cg.nS (bk fX.ae.eh)) (bT b1.kB.CI.dt 370 wg ak (eo ud.bV.a0 51 dM.p3 70 rQ iN 14 dM.p2))) (dR X.bg (dG jy.cH (i7 lW.ag.bw 113 bv nB.aO nG.aO 17 c6.f9 94 ch o4.aC)) (en aH.wd.bl.bH (e8 s6.cJ.S 98 sb dO cj dS 60 dq.gk))))) (eL H (pK nt.jr 11 z4.fT 122 AA z4.eu 85 z4.ez (gA h3.S.cR.bg 106 nX jv dk e6 79 pv aN (lj l8.bi.aD 378 ap jU.CI 378 ap ka.CI 371 iB t8.bH.kB 129 cy.fT j (fJ aV.mX.eC) (ji dV)) (fh oV.dK.aX.S e_ 59 cA.eB bd 117 lJ H 53 di.fu e_ (h6 j0.gC 96 vj bt 52 cO.er H 48 cO.p6))) (ei u1.aF.aD 46 cG.fq wD 96 cG.gd 92 xv (J ah.xx.mX.aF.sk.aI 144 di.eB (fb cF vk aE.ia.mv.bm)) (du e_.dm.dm.aX.aF.aX.aj 104 Cs aA aB dD 67 u7 bq (bk aQ.gY)))) (eg jm.iI.q5 91 nW jH 1 z6.gg 2 z6.eY (N nK.aF.sk.aI 108 dn.gj (fS ii.cK 98 cB.fi 66 zZ K 62 L (aG nJ.jQ.iG)) (gy ah.iG.eC (aK kp))) (fR qh.eN 68 cP.f8 145 cy.fm 19 cP.fz (oc ou.aS 11 di.fT 101 bv j.ib 70 ch lq 66 gN (iO L.iG.bl.hU.gE.cw 240 ap L.iG.mv.bI)) (fh sO.aS.g6.aX e_ 140 cN.ex aP 103 hD ar.cJ 99 hD ao.cJ (lb ak.pF.bg)))))) (eL iZ.aF (az iA.cK 168 z1.p4 202 z1.p3 198 z1.p2 (ei dF.dK.S 50 z3.p0 z4.e7 145 z4.f6 141 z4.fP (eg uA.b6 94 an xI.b0 1 z8.e1 2 z8.gk (k2 kt.ec.S.bp 168 iB aw.nS.kB 172 ct.eW 243 cV.fU (aG g7.fQ) (al cj)) (gz s9.S 85 iK u4 138 et sI 134 jk (i7 mZ.bH.b6.b6.bw 136 ey cX.bQ.cv cl.bQ.cv 17 cO.e7 206 ap hj.bP.bP.av))) (N bd.cH.bu.cw 54 cG.fE (aW gX.bH (dc aY.bm.fr.vr)) (j4 bO.bi.bu (lf (ro jw))))) (nl bK.AZ (oT uh.S.b2 4 z9.eY 109 an nD.b0 105 tP.b0 (fS nm.q5.b2 4 cV.eA 105 hJ ah 101 aU (co jU.aF.ec)) (du g9.aS.aj 136 et e4.bP fI.bP iD.bP 91 iK bq.cJ (lf (rP fk iC rT 20 (aM cD kD e_) 25 (aM cF kD e_) e_)))) (nd (jB jx.pk.aD 35 cq.fm 84 mf j 82 vm aE 26 cq.gH) (aW bq.iv (eo iy.bV.nR.gR.bp 143 w6 131 c6.p8 H 53 dl.fN)) (kh tl.bu.aD 171 c0.ft c0.f4 65 c0.fE (bM tl.bg 167 hB ci.mX aV.mX cC.mX 62 dq.fq))))) (nd (yF gs.aS 11 z2.p0 90 dX au z3.e7 46 z3.f6) (nd (kH aU) (gA qw.aj 100 r5 H ah aU 66 an kc.aC (mV jp.eb.b8.bw 63 mL rG pX 17 cB.f5 113 cy.gj bO (lg g9.cz.aS 11 ds.f4 184 mK H 140 lA bq) (dd n2.S aB 111 r9)) (aZ (q1 l3.dJ.aj 23 c7.f6 127 ca aH.cR.bI 111 m4.bI 107 sP) (ff yT.ag 44 dM.eA 828 cU.ga 1 dM.f9))) (nd (pj tA.b8.bw 67 cM.fT 122 lF j 17 cM.fA 88 w0 hj) (fS tp.bP.ia 4 dj.p9 103 ca tX.bI 99 e_.xx.bI (i7 oU.gR.bw 114 bv sV.aO tN.aO 17 c6.f8 109 ch h9.bi.nh)) (jz jU.Gw (ac cX.gP.eF 68 dq.ex)))) (nd (qN sK.cK 188 z6.fD 139 wt ar 135 ao) (bS ka.aF (fV s8.S 121 dy.eY 66 rU 62 dy.fm (aK rI.io)) (aW e_.vv.bI.aD (e8 pb.dB 53 rQ nj g2 kg 56 cL.p9))) (gI sX.S 61 cq.p5 107 wr X 103 ad (aZ (rP l4 iC Bg 32 (aM cD fB e_) 145 (aM cF fB e_) bd) (lf (q1 o8.eP.jr.ae.aC 11 dL.eZ 182 ap bO.y9.hM.fF 226 ah.vz.fj.bI 222 aU.vz.fj.bI))) (ej n0.bw 170 b7 rG.ae pX.ae 17 dI.eZ 73 di.ev (la gF.eN 37 dY.p1 dY.p0 d9.e7 19 d9.f6)))))))
def EP : ab dp:=(az fa.dJ.bg 32 cO 47 dM 43 cL (qq m2.bV 150 Hu 230 HM 152 Hw 306 HK (cb iT.eP.bQ 55 z1.e1 z1.gk z1.er 19 z1.eB (k2 mj.S 80 dX aw 54 z3.f4 50 z3.gO (nd (oh nw.nR.S 132 kw mE.aI 95 z7.gK H 91 z7.fi) (nd (w9 m9.a0 457 cV.p8 122 cy.eW 77 hC aE 14 cy.eH) (lf (lB mQ.ia.S 84 bN i6.fF 85 dI.fq 29 dI.gb)) (fb cD Dq bd)) (ix d4.pl.bm (bZ oU.dB 87 ch q8.nh iS.nh tT.nh 122 bv b4.bQ.aO))) (N mE.bi.cJ.aO.aO 215 c5.fN (ns gr.dK.gR.aS 4 dy.ga 114 dy.gj 110 dj.gn (ac iZ.F4.eK.dt 334 dl.f4)) (fV sT.cK 96 c9.fU 64 c9.ev 60 c9.eZ (e8 By.dB 93 b7 nj g2 kg 60 cU.fP)))) (bc nJ.aI (gI qJ.cz.aS 4 z9.eW 114 c4 uH 110 oW (bT aw.bQ.xQ.bu.dK.fy 131 je uD.cH (bM tw.g0 92 bN q3.g8 uj.g8 j.hK.g8 19 ds.fi)) (aZ (wH kQ.jq.eP.bV 24 cV.fT 202 cS.f8 26 cS.fp 38 cS.ft) (fb cF mD aV))) (dR my.a0 (aW K.cR.nS (ac e4.i0.gE.cw 94 c6.fU)) (ir te.dJ.aj 23 c8.f9 129 c8.ga 113 c8.gj 109 c8.f5 (aG X.bu.iG))))) (N k0.eF 59 z2.f4 (cb gG.a0.ag 52 z4.fo z4.fU z4.fi 1 z4.eW (bc hQ (lQ uB.aD.S 335 cV.er 56 ct.fK H 113 cV.eB (g4 gG.aj.cR.iI.ae 177 dI.fu 201 dI.gO 197 dI.ev) (al b3)) (o7 kZ.eN.cR.aD 92 cA.f8 cA.fz 64 cA.gl 60 di.fE j (hT iu.cd.gZ.b2.ae 107 ey nK.cv 197 ap K.iG.ce.bi 193 L.iG.ce.bi))) (aJ ko.bl.q5 87 cG.fi 1 cG.eW 2 cG.eH (aZ (lZ yR.cd.aD 63 yj c9.p5 92 fe hO) (co L.AV.aF.ec)) (J jU.Gg.eD.kk 221 cI.p7 (al lS)))) (nd (yu hR.S 98 z6.ft z6.f4 z6.fE 43 ep) (dQ lD.S.bl.iF 11 dn.eZ 54 dn.fo 153 dn.fN 17 dn.fU (du i5.S 60 hC au X ad 127 et aN (al h9.bg.hK)) (ek sH.bQ 169 b7 gN.ae 17 c0.gO 68 c0.ev (ly jT))) (N pq.yb.hU.bo 171 cP.p0 (bT b4.bl.eC.db 166 hD u4 (al rA.bH.bH)) (en aY.wd.bl.bH (bk pw.fr.hK)))))) (d3 e_.FN.cH (eR eT.aj.b2.aj b1 64 z1.eA e_ 268 iJ ak.aC 264 iJ af.aC (N nD.dh 216 z3.gH (k2 qJ.S 60 an qp 102 wF 98 r5 (e2 lT.xQ.bu.dK.fy 131 je bO.cH (ac g5.aI.bV.fd 159 c0.fx) (fb cF fB b1)) (dG oR.e0.cH (aG H.aF.aC.S.gB))) (bU dz.aO (dG K.cR.cH (ac ar.aF.bl.dt 342 dl.fU)) (ej li.aj.cR.aX 69 rY ar ao 181 cI.fU 177 wU (em gr.eb.cQ 124 cU.p9 cU.p8 54 cU.p7 50 yo)))) (nl tb (lE i3.e0.dB 79 z9.fx 87 z9.gn 163 an kr.iV (dG b1.bi.cH (cp sD.dB.ag 73 dr.er dr.eB 1 dr.fT)) (dG fX.e0.cH (eo zB.bV.a0 55 cL.eZ 110 b7 iN 14 cL.fo))) (e2 fI.bP.hV 187 cP.fE b1 (fV n7.jr.S 111 c9.gm 85 dP.ex 29 dP.fL (bk jy.bV.hK)) (bA sD.e0.gR.dm 11 cN.fD 1 cN.fu 2 cN.gO (h6 eI.cz.gR.a0 77 jc gS 176 hB q8 14 dq.p8))))) (eL cC (nd (kH fY) (gp qw.ag 62 an uH.aC oW.aC 1 z7.p6 2 z8.p7 (eR nm.iF.S e_ 41 vi bd 95 cB.eW H 29 cB.eB e_ (bM i5.g6 72 hC g2 dZ.aC eM.aC 1 c0.p6) (qY h7.b6 aB 210 d1.ft au)) (aZ (lB tw.b6 80 bN A3.bI 1 cA.fq 2 cA.gb) (h6 Aw.S 103 b7 aw 52 cO.eS H 48 dM.f6))) (aJ tA.bu.b8 57 cM.f6 1 cM.fP 2 cM.gK (ck cC.h8 (hT Cb.aj.b2.ae 84 pt d4 189 b7 ak.hM.cK 185 af.hM.cK)) (kN jS.eV.cf 71 Aa au X ad 90 cI.eY (g4 Au.bH.ae 52 dq.e7 64 dq.f6 60 dq.fP)))) (eg iP.eN.ag 46 rX jH 1 z6.gb 2 z6.gd (eJ gN.hK (e9 zJ.aD 52 dy.f8 ws 271 di.eZ 87 xd (lf (oO hY.bw.aF.aS 4 ds.eA 80 ds.f9 76 c6.fN))) (du uT.cd.a0 176 b7 ci.jr.ae aV.jr.ae cC.jr.ae 103 pt bt (co kp))) (gp eI.ja.cR.eN 55 mf bj br 17 cP.gb 25 cP.gd (gW tU.a0.aF.bw 62 mM aY aQ 17 di.gd 90 nY aH (d2 uN.pl.bm)) (jz H.cQ.mv (lf (eX fc.eN 33 an b1 33 fG e_ 33 an j 19 dY.gb e_))))))))
def EL : ab dp:=(d3 X (bc lV (aR bt.bP (bS dN.bm (ef kb.dJ.bi.aD 72 kA cX.gP cl.gP 60 mc ak.cH 56 af.cH (im H.cR.nS (d2 aB.aF.pl.bm) (hZ kQ.a0 113 c5.gj b1 40 c5.gb bd 135 d9.er e_ 14 d9.eB e_)) (gV kK.eK.aF 41 va 40 da.fK 1 da.fN (aG K.o5.aC.S.gB))) (mV gF.gR.g0 79 fG jw.aD jD.aD 17 c5.fL 146 pA hj (ir sL.eb.eb.ae.aC 11 c9.ft 183 dj.p4 55 vf 51 c9.f4 (al ak.iH.bQ)) (fV lH.ag.b2.ae 71 xr 147 cS.eu 143 cS.ez (lc uW.aC 11 cU.gg 79 cU.eY 176 cT.fE 51 cU.eS)))) (c3 eQ.bI (eg sE.ag 102 an iE.b0 1 z9.eY 2 z9.eS (bT au.cH.AQ.hK.dh 242 vl au (aT oN.dJ.bQ.bP 111 ds.ev 1 ds.eZ 2 ds.fo)) (bD ii.b2.b2.aj 121 cV.ex bF bE 122 hJ dN.bm 118 ie.bm (aT gr.ik 11 dM.fq 1 dM.gb 2 dM.gd))) (N aE.rF.aI.hV 70 cq.e7 (aW fY.bg.hK (bC kK.e0.q5.bi.aD 95 vg oa om 164 vb fX 160 d8)) (ej u9.b2.aj.ae.aj.e0.cQ 118 wy K L 73 c8.p2 69 v3 (e5 gr.jq.dv 164 dq.ev 66 cT.eS ar 62 ao))))) (c3 b3 (ku jy (lY sW.cd.aj 23 z8.fM 180 an dV.iV 75 z8.fx (nd (l5 jg.b6.aX 126 cy.eW 29 cB.fE 146 et gx) (bC q7.aD 173 b7 ar.ni.ae ao.ni.ae 76 u6 ak 72 af) (lf (zo dD.cH))) (J cj.nh.cH.hU.aI.aI 271 cA.ex (hZ u1.S 292 xa e_ 42 cO.gL e_ 65 zw e_ 61 z2.gb aP))) (az uQ.cQ 112 cG.ga 195 cM.eZ 192 cM.fo (J j.xx.mX.aF.sk.aI 134 di.fo (bC dF.jq.b2.ae.aj 66 cN.eu bF bE 180 u5 jt 176 gX)) (bA d5.cx.aF.b8 204 c8.eZ 1 c8.fo 2 c8.fU (em nr.aX 54 cT.p9 cT.p8 74 cT.p7 70 zM)))) (hi gs.bP 38 z6.ez z6.fK 1 z6.fN (eJ e_.cz.gY (aZ (pd oK.bV 24 dy.gK 88 cB.eW H 26 cB.eB 38 vi) (lf (jo g9.gZ 475 dl.fD 140 ds.p8 170 jK 166 c0.fK j))) (gy fX.iG.eC (iM g7))) (mV v6.nR.S 96 lF ak af 102 Ae 98 xt j (ns BW.pk.iF 4 di.fU 99 u6 17 cA.ez (aG bF.S.gB)) (bD na.aD 72 ch ar.ni ao.ni 111 bv cg.aO 107 b3.aO (fW ka.cx.bu)))))) (nd (rP eE iC tt 24 (aM cD dE e_) 65 (aM cF dE e_) e_) (aR g7 (aJ eI.dJ.dm 11 z3.p7 1 z3.p6 2 z3.p5 (lY g3.bV.b2 11 z8.eZ 100 an uI.mv 63 z8.fo (gI pg.ag.aS 4 ct.fE 68 pm dZ 64 eM (bC ti.cx.bi.cs 91 bN aY.d6 aQ.d6 84 ca ke.bl 80 iX.bl) (iM ah)) (bA s9.dm 11 da.gj 1 da.f5 2 da.hH (bZ pH.jr.aj 189 ap jn.eK.av o6.eK.av j.ni.eK.av 135 ey fY.aX.cv))) (fR iA.a0.bP 44 cG.fP 231 cG.fo 1 cG.gK (ek oZ.g6 62 pm jN 1 c9.fM 2 ct.fE (bC rd.bV.aj 71 pt aY aQ 188 b7 eQ.cK 184 dz.cK)) (aZ (rx kQ.jq.eP.g6 76 vh 1 cI.eY 2 cI.gm) (lf (ro aY.yb))))) (nl lV (nv j3.fg 118 c4 iX 76 an jl.i9 72 ju.i9 (fO h7.iI.bV.a0 80 ct.p9 121 zE aE 14 cV.fq (cp tD.q5.bw 197 c6.fC c6.gv 19 c6.fq)) (eG s9.bw 67 hC H.vL ah.vL aU.vL 19 c0.gH (bZ jA.it 148 zp au X ad 57 rO b4))) (N au.cH.o5.eD.aI 58 cq.fL (aW j5.bH (mg j8.cz.b8.dm.aS 11 dl.p8 188 ap hj.sk.hL.bI 130 ve K 126 L)) (kh s0.ia.aj 176 c7.fz c7.gl 111 c7.e1 (aK iX.bp))))) (az gs.b6 42 z2.p9 1 z2.p8 2 z2.p7 (cb nL.S.a0 96 z4.p0 z5.e7 z5.f6 119 z5.fP (nd (tB uh.S 61 an lR.gP 97 g2.aS 93 kg.aS) (nd (wJ uE.aC 11 cB.gb 71 cB.gH aH 234 dj.er 86 cB.eS) (g4 jg.b6.cQ.S 134 c0.p9 151 ds.fP 49 ds.gK) (dd mj aB 220 iJ)) (aZ (qS xi.b2.b2.aj.ae.cz.ae 67 wO K L 120 wv 116) (aK jk))) (ef v6.eP.aD 60 xn aY aQ 102 xw ak 98 af (eG nC.ag.ag.bi.bm.aF 64 vf aE.kv K.kv L.kv 1 dj.ga (al lM.a0.hK)) (en tb.bV.hK (aG fY.fy.iG)))) (nv jm.hL.bp 55 mc i6 79 kA mT 75 rB (gA pf.cd.a0 76 fG e3.eN ed.eN d0.eN 171 pA aw (ek oN.cQ.bP 179 lm pq 1 dy.fK 2 dy.fN (ac K.aF.bl.dt 342 dT.hH)) (gz un.ae.b2.ae 96 nY d4 72 mM ak.hM 68 af.hM (kf kV.aj.cR.ja bd 4 cU.fo e_ 50 cL.f5 H 46 tH aP))) (aJ fa.bl.bi.b8 87 cy.e7 1 cy.f6 2 cy.fP (ej oJ.hL.eN 102 ca rD.bI rM.bI 17 di.p7 25 di.p6 (al X.bm.bH.bH)) (de tr.hK.gD (lf (qz j))))))))
def Ej : ab dp:=(nd (Bj ru.iF.aj fY 124 dq e_ 65 dY e_) (pK nt.aX 149 G8 316 G9 Hn 31 HS (k2 eT.gC 252 iJ aw 56 z1.fo 52 z1.ez (bS ci.eP (gp h3.eN.a0 90 kw eQ.fF dz.fF 107 z7.fT 14 z7.fA (dR dk.a0 (ql m9.cQ.cs 355 dl.p7 356 dl.p6 509 mJ eQ.cR 505 dz.cR) (lf (wP gx))) (gW nm.q5.b6.bw 113 hJ ar.bm ao.bm 17 da.gl 128 cV.ex bO (lf (xu lK.bl.eV.bi.aD 177 ap bF.y9.hM.fF bE.y9.hM.fF 233 eQ.vz.fj.bI 229 dz.vz.fj.bI)))) (bU bE.bu (ck uL.h8 (pL n4.pk.aI.ja 4 c6.fA 116 ds.ev H 112 c6.eA)) (mR fk.dJ.bi.cd.jq 4 cS.p6 64 cS.ev H 60 cI.gd (ac aE.eh.dh 139 cU.fT)))) (bc tM (ry B1.cx.ae 162 z9.fD 69 an K.hU.aC 65 L.hU.aC (k3 q9.cd.bi.aD 165 cV.e7 e_ 165 cV.f6 e_ 173 iB dN.mX.kB 56 ct.ev j (bC qP.aj 66 py K L 179 b7 nq.ae 175 mh.ae)) (bD wz.S.cx.aD 117 iq bj.yd.jd br.yd.jd 74 ep H.kB.n1 70 j.AV.n1 (aT dF.ik 11 dM.fK 1 dM.fN 2 dM.ex))) (dQ ok.aS.aC 11 cM.f9 177 cq.eu 118 cq.ez 53 cM.eW (J aP.Fy.ib.bP.eV.dK.fy 253 dP.fp (ac cj.i0.gE.cw 99 c6.f5)) (J jN.bg.cJ.bi.hL.dx 156 c8.p5 (al iS))))) (N iN.iH.qV 283 z2.fo (ku fY.bm (aJ qW.g6 67 z8.fm 1 z8.gH 2 z8.gm (nd (pI ox.cz.S 119 lo au X ad 78 rN) (co gu.ec) (lf (kH L))) (e9 gG.jq.cR.cQ 220 cA.e1 cA.gk 60 lJ 56 yz (aT qM.dm 11 cO.gm 1 cO.fC 2 cO.gv))) (dR K.iI (ck aw.mv.ni (lg lW.b2 11 cN.er 92 ch dV.aC 105 bv aN.aO)) (e9 gG.aj.cR.hL.eN 104 c8.fP c8.gK 17 c8.fp 25 c8.ft (eo fa.aj.aF.a0 55 cT.hH 115 sb au 14 cT.gL)))) (lQ gU.bV 22 z6.fi 81 je H 120 z6.gl (ei il.cz.bu.aD 49 dn.fA dn.eu 63 dn.ez 26 dn.fK (aZ (pV rp.dK.cx.ja.aC 11 cV.p2 185 iB oY.o5.kB 300 c9.p9 179 cV.p1) (g4 kZ.eb.bg.ae 64 ds.gk 84 ds.er 80 ds.eB)) (ek n0.b8 174 b7 e_.cK 1 cA.eH 2 c0.f8 (co jT))) (aJ rh.ag.eN 69 cq.p4 17 cq.p3 25 cq.p2 (J jN.xQ.r4.eF 171 cA.eZ (em i1.pk.bp.aj 203 dl.fC dl.gv 88 dl.fq 84 dl.gb)) (ir tZ.aD.aF.aj 23 c7.fA 265 dI.eu 249 dI.ez 245 dI.fK (fW cj.eV.bu)))))) (nd (rP qt sc Bz 28 (aM cD hI e_) 105 (aM cF hI e_) aP) (ry i3.fg 61 z1.hH 243 iJ bF 239 bE (az dF.ec.aS 4 z3.ga 50 z3.gj 46 z3.f5 (cu m2.a0.ag 98 se ed nk j.aI 1 z8.e7 (gA oL.bl.bg 53 vm au X ad 99 mf aw (iL uT.cd.ae 172 b7 bj.xD.ae uk.ae 71 dI.p0 67 dr.e7) (la i1.ag 44 d9.hH d9.gL d9.p9 1 d9.p8)) (du iu.cf 165 ap q8 iS tT 67 ey aN (aG g5.bm.fr.gB))) (eR eI.iF.S e_ 41 c5.f5 bd 77 c5.p1 H 29 cN.fz e_ (J aP.fj.bV.fd 159 c9.ex (em lH.dJ.cR.b8.bw 79 dl.gO dl.ev 17 dl.eZ 210 dl.fo)) (oc uy.e0.aF.aj 23 cI.er 85 u7 gx 131 iz fX.kv.iH 127 d8.kv.iH (ac g5.iG.eD.aI 239 cT.gv)))) (bS jv.bu (aJ j3.dm.dm 11 z9.gL 1 z9.p9 2 z9.p8 (kh ma.ag 106 yg cV.ex 1 cV.fL (i7 qe.b6.bw 190 jK cX cl 17 dr.f5 154 mK aH)) (aZ (lB l8.aD.ae 475 dX d4.bg 498 dr.eY 494 dr.eS) (nz li.gZ 61 cL.fz cL.gl 91 si cj 87 dS))) (nd (rx qh.dJ 11 cq.er 1 cq.fU 2 cq.eB) (aZ (oD eI.b8.cf 214 ug 67 pm ah 63 aU) (em n4.aj.ia.cQ 78 dl.eu dl.ez 29 dl.gd 26 dl.fA)) (jz bd.S.vr (bZ iA.kl.cR.bg 145 hB H.kY.v9 mT.v9 rB.v9 68 mH qb.hM))))) (op ah (nd (kH cC) (aJ iT.bl.ik 11 z9.e7 1 z9.f6 2 z9.fP (im ar.mX (e8 tz.fj.S 76 yO au X ad 119 c0.gd) (dd k8.b6 aA 9 cO.gO)) (du tU.a0.bP.bg 62 mL aE.kB K.kB L.kB 238 vl ki (h6 kQ.gC 143 r9 aw 56 cO.gd H 52 dM.gK))) (dR L.bg (m5 tI.bu (bZ fk.nR.cx.cR.cf 89 zx au X ad 139 w2 aN)) (ck kn.fQ (hT dF.ag.eP.S 139 hB lR 80 jc cj 76 dS)))) (mV fc.b6.bw 100 wt bj br 17 z6.p9 57 nW bO (nd (oB g3.ho 129 dn.p8 dn.p7 78 fG K.aD 74 L.aD) (aZ (qo wR.cK 93 xd L 62 ws K 58) (ac jH.cx.aI.eC.bu.bz 393 c6.fD)) (fS mQ.cz.ja 4 cA.gH 73 ca aE.F1.bH 69 aP.iH.bH (e5 jA.dJ.fg 65 cL.gl 95 si lk 91 kS))) (N j.xF.dt 73 cP.p9 (aW oC.bw (ql j8.cz.b8.dm.aD 35 dl.p1 158 dl.p0 188 ap H.e0.hL.bI 184 j.xx.hL.bI)) (o7 fa.aj.aF.cf 71 dI.gg dI.eY 95 AH 91 we j (co bK)))))))
def EV : ab dp:=(hS fc.dv 108 HE 225 Hx 222 HH (m6 pQ (aR jk (bS e3.eP (cu nw.bl.ag 92 kw ed.fF nk.fF j.aI.fF 1 z7.gb (nd (uS oL.iF.b2 4 cq.fN 244 cP.eu H 240 ky) (ac kW.r4.iv.bm.dx 164 dI.gL) (lf (yq i1.aX 44 c5.gb 29 d9.eY 64 d9.eS))) (dG ah.e0.cH (bZ os.nR.S 129 ey e_.ae.cv lM.cv ub.cv 191 ap b4.eK.av))) (nd (lL kZ.dJ.bg 36 c5.gg 94 c5.fA H 38 c5.eY 56 As aN) (k3 nb.eK.aS 11 c9.gk e_ 35 c9.er e_ 274 dP.fU e_ 110 ct.fx aP (dc af.pT.sx)) (J jZ.cJ.bi.hL.dx 156 cI.gK (aG kx.aC)))) (N jZ.Ao.bz 154 z5.ex (cu uh.eN 89 an aA.ia.aS aB.ia.aS dD.ia.aS 19 z9.gv (aW aP.sk.nS (aK fX.io)) (fh i5.gC e_ 183 c0.fK e_ 139 lA H 470 dr.eu e_ (cp h7.g0 50 cL.fA cL.eu 19 cL.ez))) (N eQ.aO.hU.bo 548 ct.eu (nc kK.bQ.aC 11 dP.eH 83 da.eu 128 dP.f8 (dc tS.gP)) (j4 oC.aI.bu (o9 aN.AZ))))) (c3 iD (bc rJ (nd (jB nE.aS 11 z8.eH 65 an oY.aC 103 c4 K 99 z8.eW) (eR sJ.dm e_ 11 cG.fz b1 1 cB.gO e_ 2 cB.ev e_ (al dV.mu.bH) (al dV)) (gz oX.S 67 xb aN 102 bv dk 98 e6 (g1 nx.cd.aj 23 dM.eZ 77 cL.fp 51 cO.fA aw))) (nd (wJ rc.aC 11 cG.hH 65 xn aH 95 cG.gL 91 xw) (jW uE.aS 11 dj.fT 77 xb gf 94 bv gS (mb l8.b8.b2.ae 149 vb 92 vg K 88 L)) (J bt.pD.xD.cH.hU.aI.aI 317 cN.gK (lf (oO tF.bl.aS 4 cT.p2 62 cT.p1 58 dq.eu))))) (d3 hW (ei cZ.aS.e0.cQ 71 dn.fC dn.gv 58 dn.fq 54 w3 (bT pw.aX.rF.bm.bz 122 dX kx.fr (aK cC.fr.hK.gD)) (aZ (rL BO.q5.aX 169 b7 b3.cQ 29 cN.p7 189 bd.aS.ae) (e5 v0.fg 57 dM.p0 87 vj jl 83 ju))) (aJ jx.pk.b6 239 cP.eu 1 cP.ez 2 cP.fK (md BM.bP.bg 58 di.fL 406 b7 ak.nh.ae 254 c7.fx (iO d4.mu.hU.gE.cw 232 ap d4.xx.fF)) (e9 kt.eb.cz.aI.b8.bw 408 cN.gH cN.gm 17 cN.fL 252 cN.fC (bZ n2.fj.gR.bH.bg 70 zH au X ad 122 yt aN)))))) (eL oG (eL h5 (ku H.eP (gI dF.iI.aj.ae 72 pv 103 nX K 99 L (az sY.q5.bi.cQ 69 cP.fm 162 ct.er 241 cV.fz (aG kp.fQ) (al b3)) (gV jp.eN.b2.ag 81 da.p1 168 c7.fD 1 da.p0 (ij kL.S.S.dK.S 194 ap b4.eK.av 136 ey lM.cv 132 ub.cv))) (nd (Aj ah.yb) (iw rn.dv 105 nV L 67 lF bj 63 br (bC iy.ec.b6.bi.aD 61 wK aY aQ 179 u5 fX 175 d8)) (ir qk.dm.cd.aX.bl.aS 11 cI.ga 47 cI.gj 238 c8.gv 69 cI.f5 (em i1.a0.aj 183 cT.fU cT.fi 60 cT.eW 56 cT.eH)))) (qu H.bV (cu uf.a0.ag 119 c4 u3 nk.aO j.jQ 1 z9.p0 (bT j.bg.rF.bm.bz 114 dX aU.bg (aT oV.dK.cR.b8 105 dr.fi 1 dr.eW 2 dr.eH)) (md sR.S.b2 11 cN.p2 112 hD ci.aO 131 cN.p1 (aK jT))) (aJ zu.dm.aX 168 cP.ga 113 cP.gj 110 cP.f5 (fO nb.bQ.S 75 c9.p1 139 xg vN 41 dP.gL (h6 lW.bV.a0 117 bv aw.eN.aO 104 ch tL.nh 14 dl.fL)) (en fY.bm.bV.hK (co aH.bg.eK))))) (bc ci (bc iY.aI (gA l9.aD 105 r5 g5 gq k6 75 an vU.h8 (lE oL.cx.aD 73 cB.p8 279 dy.gg 61 mM aw (bZ l3.eP.aD 90 bN e4.vz.jd fI.vz.jd iD.vz.jd 79 ca bq.kY.bH) (dd gr.a0 aB 261 d1.p2)) (gW qM.cd.ag.bw 140 iq nB.bI nG.bI 17 cA.p3 79 ep h9.cJ.ja (d2 aV))) (fR j7.bQ.aj 35 cM.fN 43 cM.ex 53 cM.fL (fS lK.cK 67 cV.eZ 194 bN h5.fF 190 d4.fF (al H.rF.bH.bH)) (J bd.S.jd.eD.kk 221 c8.fM (bk gX.gY)))) (gI o0.ia.cR.ja 4 z7.f4 54 mc ra 50 s7 (nd (lZ sW.S 129 c5.fE c5.fD 70 fG kr) (aZ (jB un.aF.iF 11 dy.fC 64 sj bO 116 nY K 17 dy.gv) (aK lS.io)) (bD rH.gC.aj 72 ep ar.cJ.ja ao.cJ.ja 149 iq mY.bI 145 iQ.bI (ly gu))) (nd (jo ox.cz.aj 23 cy.gk 171 ct.gv 153 cy.fU 74 cq.p4 j) (gW kt.ec.fj.cJ.S 85 mG K L 168 zm 164 cV.er j (g4 oZ.fj.ae.b2.ae 106 dl.fT 82 dl.er 78 dl.eB)) (eG pZ.b6 100 bv ah.aO bK.aO ea.aO 1 dT.eZ (lf (qz H))))))))
def E3 : ab dp:=(nd (rP j2 iC Dh 24 (aM cD f7 e_) 65 (aM cF f7 e_) b1) (cb nL.S 84 HG Ia H4 89 H3 (aR ah.bP (nd (rP eE iC tt 24 (aM cD dE e_) 65 (aM cF dE e_) e_) (aJ kj.eV.dJ 11 z7.eZ 1 z7.fo 2 z7.fU (N e_.eK.i0.bo 77 cy.fo (bZ mQ.ia.aj 84 bN aA.aF.fF aB.aF.fF dD.aF.fF 109 ca aw.cR.bI) (lf (wP ah))) (fh sU.ho.bQ bd 65 ep e_.AV.n1 17 da.eZ e_ 124 iq j.yd.jd (lf (jB s8.aj.ag.iF 11 dL.fT 188 ap hj.eC.av 122 ey K.cY 17 dL.fA)))) (bU ci.fy (aZ (eU cF Dj ar) (iL wQ.bV.pk.ae 86 vg K L 151 ds.fm 147 vb)) (bA uW.cx.b6 197 cS.fC 1 cS.gv 2 cS.fq (co gu)))) (nd (kH u4) (cu iT.bl.g0 153 an e4.iV fI.iV iD.iV 19 z9.gk (fS kV.ec.b2.aF.aX 163 cP.p1 66 sa K 62 L (bC ti.cx.bi.gZ 95 bN fX.g8 d8.g8 80 ca ah.cY 76 aU.cY)) (aW nK.hM (bM rH.ag 48 ep X hW ld 1 dM.f5))) (az rh.ia.S 149 xt 85 cM.gv 29 cM.fq (aW j.mX.nS (iO o3.bV.rF.bm.bz 114 dX gu.bg)) (en pS.eh (aG af.pT.vL))))) (N nk.eV.dK.fy 188 z2.gK (ku cC (qv g3.bV.b2 4 z8.eu 61 z8.ez 58 u0 (qd fa.bl.bi.aD 47 ct.ex 650 cS.gO 91 cy.e7 aw (bk lT.eh) (al kr)) (bA sO.bH.bi.b8 139 cA.fo 1 cA.fU 2 cA.fi (ij s8.aj.ag.dv 196 ap d8.bP.av 120 ey lk.cv 116 kS.cv))) (N ra.bu.cw 186 cG.eZ (bD tz.aF.aD 68 yj bj br 101 fe t8 97 aP.n1 (ac iZ.ni.vv.D8.fy.bz 81 dT.er)) (de cX.o5.bp (lf (rP l4 iC Gr 32 (aM cD fB e_) 145 (aM cF fB e_) e_))))) (bS H (dQ fa.a0.aC 11 dn.f4 71 dn.fE 148 dn.gl 43 dn.fD (gz h7.iI.nR.S 139 lo aw 80 w5 ah 76 aU (al br.iH.bQ)) (fh qP.b2 bd 4 cA.f4 aP 70 cA.f6 H 66 c0.eZ aP (ly hQ))) (nd (rP j2 wN Cp 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (fO jp.eN.b2.a0 81 dj.fp 175 yY aE 14 dP.p3 (hZ lK.bl.b6.aD 173 ap bF.d6 173 ap bE.d6 135 yS aE 26 dl.gk e_)) (J aH.pD.xD.cH.hU.aI.aI 317 dl.gK (aK hW.bQ.bp)))))) (aR aE.ec (e2 j.bm.bu.bu.dh 151 iJ aP.aC (cu wz.fj.S 58 dX nj g2 kg 135 z3.eS (aJ nL.gR.dm 11 z7.eA 1 z7.f9 2 z7.ga (e2 lM.rF.bm.bz 122 dX K.fr (iO aV.hL.aI.hV 231 et H.bH) (lf (rP rv.dJ.jr iC xY 28 (aM cD mD e_) 105 (aM cF mD e_) b1))) (iw oK.cz.ae 113 sg br 86 hJ h5 82 d4 (ac iS.pD.eP.aI.db 114 dL.p3))) (gI gG.jq.b2.ae 184 c5.fT 60 wn K 56 L (dG ie.hL.cH (hT sH.S.S 76 py aN 189 b7 ed.aC.ae 185 d0.aC.ae)) (J aU.iv.bm.dx 164 cI.fu (lf (ro aH.yb))))) (dQ iT.dK.aC 11 z5.gv 136 z5.fq 162 z5.gb 29 z5.gd (nd (tB hR.bl.bi.cf 71 an tM.gP 107 dk.b0 103 e6.b0) (J H.cR.bV.fd 159 ct.gH (aG iQ.fQ)) (dG jn.bm.cH (cp y1.bw 54 cL.fL cL.gg 19 cL.eY))) (N X.aF.vz.bi.aO 65 cq.fU (J aV.hL.bV.fd 159 dP.fK (d2 eQ.aI.pl.bm)) (J mE.aO.kY.eF 925 dT.p0 (lc tW.cK.cQ 235 dq.p0 236 dY.e7 144 dq.p2 140 dq.p1))))) (eL ci (lC cD A4 bd (bc jV (nd (pI qh.S 99 lo aE K L 76 xj) (aT lU.eV.b8 65 c0.f5 1 c0.hH 2 c0.gL) (dd cZ.a0 aB 170 d1.ft)) (eG t0.bl 66 ca iY.bH aE.F1.bH aP.iH.bH 1 cA.gH (g1 zt.aj 23 dM.eW 81 cL.fD 55 cO.fL aw))) (lj tV.ia.ag 91 sF aE 91 uz bd 1 cG.p0 e_ 2 cM.e7 e_ (gz mQ.S 76 bN i6 65 ca dk 61 e6 (al i6.mu.bH)) (fh jA.dK.gR.cf e_ 125 cI.gg e_ 81 vh H 77 cI.fL aP (bk gf.gY)))) (ol jm.iI.iF 11 z6.gv 61 z5.gk aE 95 nW hO (k2 gF.gR.b6 67 fG zi 1 dn.eA 2 dn.f9 (gV uw.aj 35 dy.fi 43 dy.eW 99 dy.eH (al ar.iH.bQ)) (gy j.ib.iG.eC (e5 wE.fg 61 cL.fE 91 mH jl 87 ju))) (N cX.eC.db 60 cP.fq (bD jx.aj.e0.cQ 92 nY h5 d4 68 mM aY 64 aQ (bM oU.g6 118 bv iS.aO nJ.jQ qI.jQ 1 dL.ft)) (J jn.vv.hK.bm.dx 164 cN.gv (lf (zg rH 103 d9 36 an 95 dY.gH 14 dY.gm))))))))
def EC : ab dp:=(hS cZ.ec.bw 115 Gh 17 Gz 50 Gx (aJ gU.eb.cQ 78 GR 93 Hk 89 He (aR dV.bl (cb eT.b6.bw 125 z3.eB z3.fT z3.fA 19 z3.eu (o1 fc.a0.bp 77 kA bq.gP 61 mc X.cH 57 ad.cH (N q3.i0.bo 68 cy.eS (d2 lT.bl.pl.bm) (ji b3)) (bT bd.FN.CI.dt 362 mJ vU (bM iu.aS.S.eb.aF 195 wZ H ah aU 1 dL.fL))) (ef iT.eb.e0.cQ 148 pA b1.mX uu 85 fG jw.aD 81 jD.aD (aW cX.nS (al rR.mu.bH)) (e9 uZ.bP.aX 174 cS.e1 cS.gk 29 cS.er 194 cS.eB (eo qs.cK.S 86 cU.fL 57 cU.eH H 191 cT.fm)))) (eL qG (eg nE.b6.ag 111 c4 jN.bu 1 z9.fL 2 z9.gg (gW ok.bH.bi.aD 296 lm aY aQ 417 dj.p5 128 ct.fz j (dc cg.cQ.mv)) (kN uB.aI.cJ.S 149 pz dO cj dS 72 da.eH (ij tq.aX 50 ep af 109 iq cX 105 cl))) (gp sQ.q5.bw 492 je lk.cH kS.cH 17 cM.p5 221 cq.gv (md sZ.bi.eN 62 dP.gO 368 ky uj 19 dP.ev (bC na.iI.aj 102 ch ar.bi.nh ao.bi.nh 123 bv hQ.aO 119 g7.aO)) (ix ao.Cn.bm (aT dF.ag.eP.dJ 11 dq.eS 1 dq.fm 2 dq.gH))))) (az h7.a0 38 z2.er 115 z2.eB 14 z2.fT (ku ju (gp nF.eK 101 c4 e_.eK e_.mu 1 z8.gv 2 z8.fq (fR g9.ag 124 cB.ft 459 c9.gL 1 cB.f4 (lf (lZ n0.aD 61 dI.p2 dI.p1 178 b7 aw.cK)) (lb nn)) (bT aU.AO.kv.hM.bu.bu 61 iz j.fr.iH (h6 fk.gC 63 rQ aw 48 cO.eH H 44 cO.hH))) (N k9.iH.ib.bo 59 cG.gH (J rA.F4.eF 166 di.gO (mg na.aS 11 dT.eu 111 bv bd.pT.cJ 80 ch ah.aC 76 aU.aC)) (en kO.eh (aG rA.vL)))) (az gF.bV 22 z6.e1 41 rX 37 z6.er (pP aY.yb (aZ (qj uP.aj.S 68 zr 93 fe X 89 ad) (fJ b4.x2.eC)) (gy jU.Gv.eC (cp pU.S.fH 59 cU.f4 cU.fE 1 cU.fD))) (gI v1.eb.ia 4 cM.fE 99 sF K 95 L (ir rf.ec.aD.aC 11 di.fp 97 di.ft 57 di.f4 53 di.fE (al af.pT.bH.bH)) (de ah.io (bk cC.fr.hK)))))) (hS i3.iI.iF 4 z1.fp 109 z1.ft 17 z1.f4 (aR m3.bl (bU uH (m6 X.S (nd (w9 ot.bQ.aC 11 cy.p1 127 ct.f6 369 je b1.aS.cH 114 cy.p0) (bM tu.eP.eN 84 iK iZ.wj iY.wj mW.wj 19 dT.eH) (al iD)) (iw rh.ag.dv 85 rN af 130 lo bF 126 bE (mg tC.dJ.aD 35 dL.p7 165 ey hj.bQ.cv 199 ap t8.eK.av 195 aP.n1.eK.av))) (aJ n5.aX 28 c5.p2 44 c5.p1 40 c5.p0 (aZ (nI uY.aS 11 c9.gv 65 c9.fq 163 ap qQ 159 tG) (fb cF vk dN.gP.bm)) (aW jy.xF (aG aN.iG)))) (qu vN (nd (zS fc.eN.cR.b8.bw 97 an oR.b0 oy.b0 17 z9.p5 73 lV.i2) (ek qc.q5 100 hJ jN 1 ct.p7 2 ct.p6 (lf (oS te.pk.S 200 c6.eY c6.eS 99 y7 95 c8.p3 j))) (bD l8.cf 70 hC nq mh 137 et j5 133 lG (e8 rj.S 108 hB au X ad 53 dM.ga))) (lj sK.cz.bi.aD 228 cP.fm aY 228 cP.fm aQ 382 yl dV 64 cM.f5 j (aZ (wx uO.kl 83 cy.ev 146 lo iN 14 dP.ga) (bZ g9.cx.fj.S 152 mK th j5 lG 200 jK kr)) (en ke.eh (aK aw.eN.bp))))) (bc H (nd (kH b1.wj) (lQ qW.S.S 53 z9.fu 153 an aE.iV 63 z9.gO (e2 aE.mv.aI.db 232 ap aE.cx (aT lU.ik 11 dr.gl 1 dr.e1 2 dI.fx) (qY ut aB 111 b7 au)) (m5 L.xQ.bu (h6 i1.gC 104 si k9 60 cO.ga H 56 dM.fE))) (dR ak.S (m5 qQ.bu (mg ng.cx.fj.cQ.aC 11 c6.gl 100 vg oY 157 vb dZ 153 eM)) (ns ts.bi.ae.ia 4 c8.fC 241 cN.f8 72 cN.eH (aG L.bu.iG)))) (nv tg 102 ym L 55 kA k0 51 jZ (hi rl.a0 47 c5.fP c5.gK 203 c5.fp (gy j.kY.aI (bC t0.ho 78 ca aY.wd.bl aQ.wd.bl 101 bN fX.d6 97 d8.d6)) (aZ (ov oJ.cd.aj 23 c7.p1 119 bN e_.bP.g8 93 hO.fj.bI) (o9 dZ.fr))) (ef rn.ho 101 cM.eu aY aQ 71 cM.ez ak 67 af (bD nC.ag.ag.bi.bg.aj 105 cV.fD ak af 573 tj cg 569 b3 (mb uY.e0.gR.aX 84 dL.ev 183 ap bF.fj.bI 179 bE.fj.bI)) (gy aw.pF.iG.eC (fb cF hI b1)))))))
def Dr : ab dp:=(c3 K.AO (hS h3.ae.aC 4 HI 215 HP 211 Ha (aR bd.aF.bl (aR e6 (aJ h3.pk.ag 89 z7.e1 1 z7.gk 2 z7.er (lY rc.aj 23 cy.ez 125 uv ci 99 cy.fK (pL pb.dJ.bm.bg.b2 4 dr.fo 131 c7.fu H 127 w2) (ji b3)) (bT q3.kv.pT.hK.dh 305 ky q3 (hZ iu.aS.eK.bi.aD 173 ap bj.yd.hM.fF 173 ap br.yd.hM.fF 247 ap au.nh.fj.bI 58 dL.f8 e_))) (nd (lZ g3.ho 129 c5.gk c5.er 78 fG bq.aD) (aZ (wH iu.cd.bV 24 ct.fi 170 dy.p4 26 dy.p3 63 dy.p2) (ac bq.i0.gE.cw 88 c6.ev)) (bA d5.cz.cd.bQ 70 cS.p9 17 cS.p8 122 cS.p7 (iM jV)))) (nd (kH j5) (k2 j3.ae 60 an aQ.aC 73 z9.eB 70 z9.fT (hX q9.cd.bi.aS 11 cV.gK 70 dy.f9 173 ct.fD aw (d2 ak.aS.vv.bm)) (aZ (jB rH.ag.bQ.aC 11 cS.fU 80 ep bO.x2.n1 169 iq dN.bV.jd 41 cS.fi) (e5 cZ.dv 46 cO.gL 69 z2.gb bj 65 br))) (nd (pO cZ.aj.S.b2 4 cM.gn 100 uv H 96 nV) (ir xi.b2.b2.aj.ae.aj 183 da.gO 184 da.ev 479 cS.p3 476 cS.p2 (lf (eX o2.aI.cz.S 122 dl.gn e_ 122 ve H 122 dl.gn aP 180 ap l6.hL.bI))) (bA tl.bu.b8 57 c8.p9 1 c8.p8 2 c8.p7 (bk dS.gY))))) (nd (rP eE sc DT 24 (aM cD dE e_) 65 (aM cF dE e_) b1) (bU cj.eN (bc kp (e2 dk.i0.bo 204 fe au (nz n0.aD 61 dI.p7 dI.p6 178 b7 t8.ae 174 aP.n1.ae) (lb d0)) (gW BQ.eK.bw 98 py K L 17 cA.fT 179 b7 o4.cQ (aT zt.ag 51 cO.fL 1 cO.gg 2 cO.eY))) (dQ h7.aI.eN 45 cG.ez 46 cG.fK 17 cG.fN 25 cG.ex (fV oX 86 bv 59 ch 55 xb (lg na.jr 11 dT.fL 112 ch jv.aC 107 bv rJ.aO)) (J eQ.iv.bm.dx 164 c8.f6 (bk gx.gY)))) (az m8.bl 76 je 1 z6.eZ 2 z6.fo (pP dN.eC (fh sX.a0 bd 103 uv bt 83 rb aE 14 cP.e1 aP (fJ aN.AV.eC)) (k3 n0.aS 11 c0.gl e_ 178 b7 h9.ni.ae 69 cA.f6 aE 65 u6 aP (co hQ))) (lj rc.aD 59 cq.p9 e_ 118 cq.p8 e_ 319 cM.ga H 57 cq.fu j (J nk.r4.eF 171 cA.gO (al pS.kv.aX)) (kh sD.e0.gR.bw 69 c7.p4 c7.p3 19 c7.p2 (bZ gG.b6.wj.S 159 hB e3.aI uN d0.aI 82 jc pc)))))) (nd (rP qt sc Bz 28 (aM cD hI e_) 105 (aM cF hI e_) e_) (aR kp (bU L.mu (nd (lL nL.aO.S 114 z7.p2 190 z7.fC H 116 z7.p1 97 kw lR.fF) (nd (uM un.aF.aj 23 cy.p7 80 mL bd.aS 64 mf ak 60 af) (ff oq.b8.bg 121 cA.ex 288 dr.fC 235 dr.gv) (la li.eN 41 d9.f9 d9.ga d9.gj 19 d9.f5)) (ck jU.aF.aC (aG cl.aC.S.gB))) (N CX.eV.dK.fy 51 c5.gd (J au.bm.aX.pF.bo 213 dP.e1 (lf (tJ l8.iI.cx.bw 141 wS bj br 17 dT.fq 215 ds.fm))) (J eM.hU.bP.eV.dK.fy 92 cI.e1 (ff d5.aj 23 cT.fP 76 cT.gK 50 cT.fp)))) (lC cF vk aE.nR (nd (oh qw.bV.a0 116 c4 aw.eN 92 an q4.i9 14 z9.f5) (aZ (lz jl.cY) (lf (tB oJ.iI.ae 85 bN j.v9.fF 109 ak.aS.cH 105 af.aS.cH))) (gz kL.S.S 170 ap b4.bi 76 ey dk 72 e6 (eo pU.S.bV.a0 59 cL.eH 150 r9 iN 14 cL.f8))) (aJ uQ.eK.dm 11 cq.gl 1 cq.e1 2 cq.gk (fS BY.b2 4 dP.fM 69 ey bK 65 ea (aG nq.eK.ce)) (de e3.gY.gD (bC re.aj 83 sb bF bE 67 vd jt 63 gX))))) (lC cF f7 b1 (nd (kH ci) (eR l9.a0 e_ 109 c4 rJ 107 an dO.ce 14 z8.p1 e_ (aJ eI.bu.gR.b8 246 cB.ez 1 cB.fK 2 cB.fN (ml dz.aI.cH) (dd tF aB 247 d1.gd)) (aZ (lL jx.aj.gR.bg 36 cA.f5 106 mM K.xF 38 cA.hH 68 sj i6) (lf (ov qf.aj 23 dM.fz 81 mF dV.bl 55 bt.bP)))) (e2 qL.hU.bo 546 je lT.cH (aZ (qN eI.ja.cR.cQ 231 vl 59 mL bj 55 br) (aK br.vv.cJ.fr)) (bA ua.ag.ag 65 c8.ex 1 c8.fL 2 c8.gg (eo n5.bQ.S 61 dq.fu 60 cT.fq H 56 dq.gO)))) (gI hR.eV.S 90 z6.gj 51 rX X 47 ad (eJ rI.gY (bD wR.eP.aD 66 cB.gH aY aQ 97 cB.eS ak 93 af (ac g2.vv.D8.fy.bz 319 ds.gj)) (jW tw.aS 11 c7.e7 83 ca b1.cY 84 bN bd.fj.bI (iM jX))) (nd (rP j2 wN rZ 24 (aM cD f7 e_) 65 (aM cF f7 e_) e_) (ej i1.a0.cx.bw 64 yM ak af 17 di.ga 138 di.gj (al iX.kv.aX)) (jz fY.aX.mv (lf (yq Bv 40 an 29 dY.f9 60 dY.ga))))))))
def Dk : ab dp:=(c3 o4 (m6 aw.S (hS qf.b6.bw 107 z1.eY 17 z1.fm 71 z1.gH (bS mW.bm (cu h3.eN.ag 90 kw aV.bI nJ.bI qI.bI 1 z7.fq (N ah.aC.hM.gT 82 cy.fq (em kt.eb.cx.ae.cR.b8.bw 248 dr.p8 dr.p7 17 dI.fA 364 dr.p6) (fb cF mD H)) (bA nm.bl.dm 11 dP.gm 1 dP.fC 2 dP.gv (lf (tR iu.cd.cx.cz.aX 185 ap gX.av 29 dL.ex 205 tI.av)))) (bU aY.aO (bA sZ.bi.dJ 11 c9.eW 1 c9.eH 2 c9.f8 (fJ qL.iG.eC)) (j4 d4.bu (lc hY.aj 23 cU.gm 68 cU.fC 52 cU.gv 48 cU.fq)))) (az gU.a0.ae 89 z5.fK 175 z5.eY 172 z5.eS (lj rz.a0 92 an ak.ia.aS 92 an af.ia.aS 78 an tL.gP 14 z8.fN aP (aW bt.bH (em ts.bi.bp.aj 357 ds.p7 ds.p6 257 ds.p5 253 ds.p4)) (hX i5.cR.aD 68 c7.gn 239 ds.gO 135 da.eB aw (nz j7.gZ 53 dM.p1 dM.p0 83 vj aV 79 cC))) (nd (tJ rh.cs 81 w0 cX cl 73 cq.gK 70 cG.fz) (ej lU.bi.eN 492 mJ rD rM 17 dP.fi 25 dP.eW (lf (wH pg.dK.eP.bg 56 c6.fM 144 c6.fx 58 c6.gn 114 c6.eA))) (bD li.gC.ho 125 y0 bj br 89 vh cg 85 b3 (e5 te.S 65 dq.fq 174 hB aV.mX 170 cC.mX))))) (c3 e4 (nd (kH H) (gA Cv.aj 55 an e4.aC fI.aC iD.aC 101 c4 aw (e2 H.fr.bi.k7.fy 319 ap au.gY (lf (oD fc.cz.dK.S.b2 4 dr.p2 182 b7 dZ.aC.ae 178 eM.aC.ae)) (fb cD fB b1)) (gz qX 96 bv aN 69 ch X 65 ad (ly kn))) (N H.CJ.ib.bo 73 cG.gn (k3 sO.aS.cs 87 hD aY 87 hD aQ 119 dj.eB e_ 116 di.fA bd (i7 l8.cd.ag.bw 92 iK jw.cJ jD.cJ 17 dT.p2 153 et o4.bP)) (fh vO.ag.ag.bi.b8.cJ.aX bd 66 vc af 29 c8.gk e_ 148 iz qy.fr.iH (bk jD.gY)))) (d3 hO (eJ ar.hK.gY (J qp.hM.gT 82 dy.fE (al vS.a0.hK)) (gy af.pD.eC (ms jX))) (gA pb.aO.ho 57 B4 aA aB dD 104 uz bq (du pg.eV.bg 60 wT au X ad 182 lm aN (lf (sG n4.aj.gR.bg 36 c6.fx 357 ap H.cH.mv.bI 38 dl.p3 311 mq.xx.fF))) (iw oJ.cf 78 ca kr.bl 93 bN jy.bI 89 rt.bI (aK ar.CJ.xD.S)))))) (eL mW.aF (nd (rP yE.it wN Dh 28 (t9 cD DA bq) 105 (aM cF f7 bt) b1) (cb eI.dJ.bw 47 z4.ft z4.f4 z4.fE 19 z4.fD (c3 bj.xD.aF (nd (pV ng.aX.aC 11 ct.f8 301 lm aH 410 c9.f6 121 ct.fz) (cp sN.iI.ag 74 c0.p0 dI.e7 1 dI.f6) (al m3)) (J bd.ni.bl.eC.db 80 da.p3 (bC kL.S.S.cz.ae 190 ap H.gP.aI.av j.sx.aI.av 104 ey h5.cY 100 d4.cY))) (N fI.bu.cw 95 cG.fD (aW K.eC.bH (aK ke.io)) (bA nr.cz.ag 66 cI.fM 1 cI.fx 2 cI.gn (al pS)))) (cb hR.q5.b6.bg 136 z5.p4 z5.p3 z5.p2 89 z5.p1 (nd (xu sE.aj 66 an jl.i2 ju.i2 106 fX.b0 102 d8.b0) (J tM.db 72 cV.ga (iR qP.ag 175 b7 b1.aC.ae 1 dr.p2 2 dr.p1)) (du tz.aF.aD 68 yj aA aB dD 101 fe aw.bV (aK hQ))) (nd (oB v1.b2.aj 214 cP.eA cP.f9 501 je H.ae.cH 497 j.wd.cH) (bT iY.D8.aI.hV 148 hC aE.ia (iO uD.eK.hU.gE.cw 232 ap uD.fj.fF)) (de b1.aF.o5.bp (lf (rL s5.b2.b2.q5.aX 79 jc d8 29 dY.gK 99 oI)))))) (m6 pQ (cb nL.g6 96 z5.gK z5.fp z5.ft 1 z5.f4 (eR qU.bQ e_ 66 an oW.aC 17 z9.fU e_ 112 r5 aH (N b1.kB.eC.db 161 cB.p9 (aT pg.dK.ag.dm 11 ds.fE 1 ds.fD 2 ds.fu) (qY gr.b6 aB 151 r9 au)) (bA xl.bu.b8 57 c7.gK 1 c7.fp 2 c7.ft (ly jk))) (gp um.aX 94 xv K L 52 cG.fq 48 wD (ck kJ.h8 (hT rq.cz.S 102 ch my.aC 115 bv j5.aO 111 lG.aO)) (J jv.iv.bm.dx 164 c8.gb (lf (oS rf.cz.b8.bw 61 dq.fi dq.eW 17 dq.eH 183 mH gN.hM))))) (nv qs.bV.pk.ae 104 wt br 65 nW q6 61 nK (eJ iX.gY (gW tE.ag.bw 76 r6 jw jD 17 dy.gm 257 ky bO (dc oC.fr.vr)) (aZ (oD sZ.bi.S 129 pz 70 pp ah 66 aU) (ms jV))) (N mq.cJ.hU.bo 157 ct.fL (aW dN.mX.nS (hZ oZ.fj.aF.cx.aD 339 ap bj.Eb.mv.bI 339 ap br.Eb.mv.bI 319 ap K.kY.xx.fF 82 dl.p4 j)) (aZ (pV tK.cd.aj 23 dT.fD 250 ch bO.bV 141 dT.fu 138 dT.gO) (la eT.ag 40 d9.fP d9.gK d9.fp 1 d9.ft)))))))
def Du : ab dp:=(bc d0 (bc e3 (az mj.eb.aX 62 z1.fT 41 z1.fA 138 z1.eu (aR dk (gA eT.cx.bg 72 kA H.kY mT rB 52 mc i6 (fR i5.eN 119 cy.fz 454 cV.p5 19 cy.gl (ml cl.bm.cH) (ji cj)) (j4 L.xQ.bu (lf (jo oZ.fj.aF.it 245 dL.eu 138 dL.fo 86 Ax 82 w6 j)))) (nd (tR sW.cz.aX 78 fG ie.bw 29 c5.gl 98 gx.aD) (fh vI.kl.cR.cJ.aX bd 62 vf af 29 dy.p9 e_ 583 tj hj (iR qx.gR.b8 143 lA kW 1 ds.gL 2 ds.p9)) (ej bd.kl.cR.bg.cR.eN 122 iz oR.kv.iH oy.kv.iH 17 cS.fM 25 cS.fx (fW gu)))) (cb nt.cf 102 z5.fu z5.gO z5.ev 101 z5.eZ (nd (pN fc.eN.cR.b8.aD 61 an jn.bi.gP o6.bi.gP j.ni.bi.gP 105 lP.b0) (ej rp.dK.cx.bi.aX 58 ct.ev ar ao 171 cV.e7 167 cV.f6 (bk kS.eh)) (bA li.dK.b8.dm 11 cS.fE 1 cS.fD 2 cS.fu (bM kQ.a0.ag 52 rO X hW ld 1 dM.hH))) (nd (uS sQ.a0.b2 4 cG.p0 98 sF H 94 cM.eY) (J kJ.sx.cJ.aO.aO 405 cA.p1 (bZ kt.eb.cx.aF.dB 75 vZ au X ad 156 l0 aN)) (de bF.bH.bp (aG uj.iG))))) (ei nA.a0.aj 85 z2.fD z2.fu 121 z2.gO 118 z2.ev (bU aB.bQ (N lM.pF.eV.bz 71 z8.fL (az rk.pk.ae.cQ 64 cy.gd 161 cP.fN 157 cP.ex (d2 X.jd.pl.bm) (lf (m0 sY.eb.ae 96 z0 211 z1 219 z2))) (gy dZ.iG.eC (aT yN.dm 11 cO.gl 1 cO.e1 2 cO.gk))) (ef eI.cx.aD 67 Aq bj br 55 wV K 51 L (aZ (lB tc.b6 90 fe oj 1 c9.p0 2 dj.e7) (mb uR.aC.S.b2 4 c6.f4 158 l0 bK 154 ea)) (jz vK.vr (em k4.aD 49 cT.f8 cT.fz 75 cT.gl 50 cT.e1)))) (bS aV (nd (oS h7.cx.aD 66 dn.f8 dn.fz 163 dn.eS 50 dn.fD j) (kN lU.S 80 hC dO cj dS 129 cB.ft (aK b1.mX.gP.ib.fr)) (ek sH.S 173 b7 b4.ae 68 c0.eZ 64 py (bk hQ))) (qd mP.aX.aC 11 cq.hH 62 cy.gK 84 cq.fp aw (J l6.mX.aF.sk.aI 199 cA.ft (al t5.mu.bH)) (ck lG.fQ (bZ tD.aD 167 hB jn.x2 o6.x2 j.ni.x2 70 dY.fp aw)))))) (hS fa.jq.eb.ae 128 GQ 73 G0 69 Gf (aR pc (N cl.aF.sk.aI 141 z3.gv (fR i3.e0.ia 11 z7.p8 87 z7.p7 70 z7.p6 (N aB.eC.db 147 cy.f9 (ml aN.aI.cH) (dc j)) (ej uP.eV.S 119 fe eQ dz 68 Ar 64 da.fC (mb iu.bH.bi.cf 83 wZ 189 ap g2.iH.v9 185 kg.iH.v9))) (o1 qW.aj.b2.ae 152 pA uu 89 fG ar.Dg.aD 85 ao.Dg.aD (J rC.aX.pF.bo 211 dP.gl (ac K.o5.av.k7.fy 202 dT.gL)) (ns uZ.bP.ia 4 cI.eH 105 cI.f8 101 c8.ev (em lH.dJ.bw 51 cU.p5 cU.p4 17 cU.p3 190 cU.p2)))) (bS jt.bu (ef j3.iI.aj 90 an tb.i9 ui.i9 122 c4 hQ 118 g7 (e9 mP.ag.iI.aj 119 ct.gb ct.gd 165 cV.ez 162 cV.fK (aG iY.jQ.iG)) (bT X.iH.aI.hV 124 hC cj (bC gF.gZ 57 mF hQ g7 87 dX cj 83 dS))) (gp tA.bg.aj 58 v8 ak af 345 cy.fA 122 cq.eH (J b4.bm.bV.fd 159 dP.eS (cp rs.aF.b2.ag 202 dl.fm dl.gH 1 dl.gm)) (e9 tO.e0.bi.eN 240 c7.eB c7.fT 17 cN.eZ 25 cN.fo (bk b1.eh))))) (N bd.ib.cw 41 z2.fC (aJ nw.ag.dm 11 z4.gn 1 z4.eA 2 z4.f9 (cu qW.cs 85 an H.wd.mv ah.wd.mv aU.wd.mv 75 z8.p5 (ef rp.dK.cQ.cs 70 mG ar ao 175 yV K 171 L (co H.ae.bl.ec) (dd rE.S aB 71 rW)) (ek m1.bP 68 ca CG.bH 1 cA.fM 2 cA.fx (bC wz.S 46 ep ak af 105 iq K 101 L))) (dR b4.S (bD jp.dJ.cs 250 ky bF bE 85 r6 jt 81 gX (bM na.b6 76 ch dZ.aC e_.eK.aC e_.mu.aC 1 dT.gn)) (aZ (lZ kQ.jq.eP.cs 120 y0 c8.fK 80 vh aw) (aK uu.bp)))) (ef jm.iI.aj 98 ym K L 51 kA ak 47 af (eJ aQ.gY (J H.gP.aI.db 116 dy.gk (aK e_.AV.eC.gD)) (iw qn.S 86 bN l6.bI 75 ca gu 71 t7 (ij i3.fg 61 mF g7 91 dX lk 87 kS))) (nd (zL tU.a0.aC 11 cP.fx 88 nY 54 sj) (m5 nB.bu (e8 n5.e0.cJ.fj.S 102 y7 au X ad 207 dl.fm)) (jz cl.cQ.mv (la Aw 36 dY.gd dY.fM dY.fx 1 dY.gn)))))))
def Dl : ab dp:=(d3 ld (N nG.eV.bz 142 GO (aR gq.bP (bS bt.eP (lQ kj.q5.S 189 z7.gn 94 z7.e1 H 90 z7.gg (oT u1.aF.cf 66 rb 108 nV ah 104 aU (lf (qS e_.dm.dm.aX.aF.aX.cz.ae 71 v3 K L 124 wy 120)) (lf (eX jA.eN 37 c5.gb b1 99 c5.fM e_ 37 c5.gb j 19 d9.ez e_))) (fh g9.eN.S e_ 49 va bd 136 wf K 132 wf L (iL o2.aI.S.b2.aj 188 ap aY.bu.d6 aQ.bu.d6 138 dL.fm 134 dL.gH))) (bS oA.aF (k3 pe.cx.aD 521 cS.f4 e_ 637 iz oo.kv.iH 348 ct.er aE 124 cq.eA j (fJ ao.AV.eC)) (ix L.hU.pl.bm (lc jA.ec.aD 113 cT.fu 160 cT.gO 63 cU.fm 26 cU.gH)))) (N gq.bP.dh 59 z5.er (nd (rL pf.b8.fg 160 an b3.iV 75 z9.gH 164 bd.b6.b0) (aZ (eX sY.q5.bi.S 65 mG b1 197 je g2.cH 65 mG j 166 yV e_) (d2 lk.bl.pl.bm)) (ej l8.aI.b8.bw 500 mJ aY.cR aQ.cR 17 c7.eZ 411 dl.gj (aT d5.ik 11 dM.fM 1 dM.fx 2 dM.gn))) (N ao.bg.fd 76 cq.fP (oc oK.dJ.aD 35 dP.eZ 142 hJ h9.bm 121 ct.fx ak 117 af (ij lU.ik.aX 197 jK b3 153 mK aY 149 aQ)) (e9 yi.cz.S.bp.aF.bw 67 c8.p2 v3 17 cN.f6 116 wy (aG uU.iG))))) (op gx (bU b4.bQ (nd (ov uA.aS 11 z8.eA 76 an iN.bi.gP 98 aN.b0) (nd (pV ko.eb.gR.bw 159 ct.fq 264 Ak j 17 ct.gm 126 ct.fC) (iR q7.b8 72 u6 jH 1 c0.f9 2 c0.ga) (fb cD hI b1)) (aZ (qN iy.ec.eV.ae.b2 4 di.eB 119 lJ ah 115 aU) (ff yN.bw 39 dM.fu 219 cL.f9 19 dM.gO))) (dR ak.bg (ck ar.aF.aC (e8 qx.dB 173 jK au X ad 147 dT.e1)) (de bO.bH.bp (bk gN.hK)))) (d3 X (pP ar.Dg (aZ (yD qc.ja 4 cB.gl 39 cB.fz 36 vi) (ac oM.bP.dt 334 dT.p8)) (J cl.xQ.bi.cJ.aO.aO 585 dT.p1 (cp mU.jr.fH 63 cU.fu cU.gO 1 cU.ev))) (cu uQ.eK.bw 93 lF aA aB dD 19 cP.fU (kh vO.ag.ag.bi.b8.bg 99 Cs di.gl 58 u7 (bM lK.bl.cd.aF 177 ap fI.d6 ra.d6 s7.d6 1 dl.p2)) (md j8.fH.bw 135 cN.er 216 ch dV.aC 19 cN.eB (fW af.cx.bu)))))) (cb qf.ag 51 z1.fo z1.fU z1.fi 1 z1.eW (N X.bu.dh 55 z1.p8 (cb eI.dJ.dm 160 z3.p4 z3.p3 z3.p2 1 z3.p1 (eR nF.bQ bd 101 z8.eW e_ 17 z8.eH e_ 67 an oY.aC (az kt.ec.S.ae.bQ 51 ct.ev 17 ct.eZ 251 cV.fp (hZ oP.bl.cf 135 dT.f8 e_ 136 cN.ex aP 99 hD j5 95 hD lG) (fb cD Dj bd)) (J jn.pT.aI.hV 78 da.gL (bC pH.cd.cQ 103 ey q6.cv nK.cv 193 ap sV.av 189 tN.av))) (eR dF.aj.bQ e_ 46 wV bd 17 cG.f4 e_ 74 Aq j (bA mP.ag.dm.dm 11 c9.ga 1 c9.gj 2 c9.f5 (lg qx.gR.aD 35 dT.gv 229 jK dV 147 lA lS)) (J tG.aO.bP.eV.dK.fy 134 cI.fC (ac h5.bi.hL.dx 156 cT.gH)))) (qu af (nd (oh uf.kl 119 c4 aN.aO 117 an au.cQ.ce 14 z9.p3) (J fY.hL.aX.pF.bo 666 c0.e1 (ac jn.y9.jd.eD.kk 221 dr.fK)) (ek g9.aS.ag 87 iK jN.cJ 1 da.p8 2 da.p7 (o9 H.fr))) (e2 qb.pT.hK.dh 305 ky aw (aW ah.iv (bZ rq.cs 111 bv tS.aO rr.aO ad.bi.aO 88 ch kc.aC)) (e9 uZ.aF.bw 174 c7.p0 c0.e7 17 c0.f6 77 c0.fP (aK aB.bQ.bp))))) (aR pq (bc iQ (nd (uS qw.b2 4 u0 104 c4 ah 100 wF) (dQ oP.bl.aj 23 cB.fx 125 cB.gn 119 cB.eA 94 cB.f9 (ac bt.r4.eK.dt 334 dT.eY) (qY gs.b6 aB 260 iJ au)) (ek ts.cJ.b8.b6 153 l0 pq 1 dT.f4 2 dT.fE (lf (lz aV)))) (nd (qS cZ.aj.cx.ae 50 wD K L 100 xv 96) (e9 sL.eb.eb.ae.aF.bw 63 dj.eA wO 17 dj.gj 112 wv (aG bd.aS.eK.ce)) (ix m4.Cn.bm (aG ak.hK.iG)))) (ef kV.aj.b2.aj 50 nW bF bE 109 wt ak 105 af (gI lD.S.cQ.b2.ae 75 dn.gv 62 w3 K 58 L (aZ (qS wI.aj 57 xb K L 92 bv 88) (e5 kK.gR.fg 144 ds.p8 174 c0.fK ar 170 ao)) (aZ (rP l4 iC Ap 32 (aM cD fB e_) 145 (aM cF fB e_) aP) (aK gu))) (nd (rP fk iC sv 20 (aM cD kD e_) 25 (aM cF kD e_) b1) (jW tw.iF 11 di.p5 94 bN H.bI.fF 101 ca vU.bI (al bK.bm.bH.bH)) (de L.aF.o5.bp (em eT.a0 40 d9.eH d9.f8 135 dY.p6 14 dY.p5)))))))
def DI : ab dp:=(eL e6 (cb kj.S 64 HV HZ H9 225 G6 (aR dZ.bP (aR kc (cu kj.eV.eN 87 kw g5.fF gq.fF k6.fF 19 z7.fK (nv um.dJ.aX 100 lF af 106 xt ar 102 ao (iO bq.pD.CI.dt 362 mJ aw.cR) (lf (qz aV))) (dG tX.hL.cH (iO g2.eK.hU.gE.cw 232 ap g2.fj.fF))) (cu oV.dK.aF 51 As ah bK ea 1 c5.ez (fV gr.dK.gR.ae 28 dy.p1 70 dy.p0 66 c9.e7 (bM t0.fH 97 bN dk.g8 nD.g8 tP.g8 1 ds.gd)) (k3 hR.S.eP.cR.aD 75 ep bF.x2.n1 75 ep bE.x2.n1 184 iq b1.kY.bg.jd 50 cS.p4 e_ (aT sY.eb.ae 96 cU.er 211 cU.fA 219 cU.eu)))) (az iy.bQ.ae 207 z5.fi 109 z5.eW 223 z5.eH (ef l9.aD 105 r5 aY aQ 75 an dN.h8 71 ie.h8 (gV rv.fj.fj.cx.bi.a0 60 cV.fE 491 di.p8 137 cV.fD (bZ m1.aD 68 ca oA.aF ue.aF L.Em.aF 91 bN bt.g8)) (oc mU.hL.fj.cQ.aC 11 cS.eH 155 cS.ez aH 79 xr dZ 75 eM (ac K.eC.bu.cw 147 dM.p6))) (nd (jB pe.cQ.aC 11 cM.gj 233 cP.fm aH 367 ky H 57 cM.f5) (J gx.hU.bP.eV.dK.fy 259 dP.fE (lf (rx kL.bV.b2.ag 124 ve 1 c6.f5 2 dl.f9))) (hX d5.cx.aF.aD 66 c8.p4 372 c6.gH 208 c8.eZ aw (ff hY.g6 162 dq.f9 319 dY.fP 1 dq.ga))))) (N b1.ib.cw 41 z2.fi (bU hW.bQ (oT uf.b2 4 z7.p6 69 an nD.aC 65 tP.aC (dQ ma.aS 11 ct.gn 141 cV.eS 270 cV.fm 106 ct.eA (lg rd.b2 11 dI.p5 81 c0.eZ aE 172 b7 bd.ia.ae) (kf ru.iF.aj fY 124 d1.fi e_ 69 d1.eW e_ 65 d1.eH e_)) (eG fc.cz.dK.eN 162 b7 e4.cQ fI.cQ iD.cQ 19 cA.ez (aT mU.cd.ag 51 cO.gd 1 cO.fM 2 cO.fx))) (eg gG.aX.ag 52 po jH 1 cG.fL 2 cG.gg (gV zJ.b6 56 dj.gO 235 cA.ev 1 dj.ev (lf (lB tK.cf 102 hD bt.aO 150 cN.fN 138 dT.gm))) (J jU.aO.bi.hL.dx 156 c8.f4 (dc jl)))) (ei eT.bl 36 z6.eW z6.eH 1 z6.f8 2 z6.fz (az i4.cd.aO.aX 51 AC 29 dn.fL 71 dn.gg (gW tc.bw 65 zr ak af 17 dy.e7 98 fe bO (aT AF.eb.aI.b8.b8 133 dr.fM 1 dr.fx 2 dr.gn)) (fO Bu.cK.S 58 cA.eW 144 cA.fo H 313 dr.gg (bM sC.ag 59 mF gu jV m3.bl 1 cU.ft))) (eR rh.ag.a0 e_ 73 w5 e_ 136 lo aE 14 cP.f6 e_ (hX j8.aX.aC 11 di.fP 68 cA.eW 136 dj.eZ aw (al ak.aX.a0.hK)) (de oo.io (aK h9.CJ.xD.S)))))) (nd (rP eE iC CN 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (aR dk.bl (bU uG (az iT.bl.b6 54 z8.f6 1 z8.fP 2 z8.gK (N bd.FN.eC.db 487 dy.gH (ac tr.GE.bi.k7.fy 80 c0.p5) (dc H)) (aW e_.bV.hK (bC os.bV.aj 89 ey aY.cY aQ.cY 195 ap mY.av 191 iQ.av))) (az n5.bV 22 c5.gj 38 c5.f5 26 c5.hH (ns qc.aS 4 c9.gg 271 dP.ez 107 dP.eu (aK H.kB.eC.gD)) (aZ (pV uy.e0.aF.iF 11 cI.fT 69 vc kP 460 cN.e7 17 cI.fA) (mb n2.ia.b2.ae 128 cU.p8 58 yo K 54 L)))) (bS e6.bu (eR uA.cf e_ 110 an pc.b0 78 an jy.i2 74 an rt.i2 (aZ (pj ii.ho 141 c9.fA 627 mJ qy 277 c9.eu 113 ct.eA j) (lf (jB uw.ag.b6.aD 147 c6.eB 254 bv tI.aO 135 hD b1.kY.cJ 26 c6.fT))) (fO sQ.S.b2.a0 114 da.f9 93 yO aE 14 c7.eS (cp d5.g0 58 cL.gb cL.gd 19 cL.fM))) (hi um.S 56 lF rb 98 nV (fO uP.a0.S 98 wC 72 c9.fx H 157 da.fM (g4 qg.aX.dJ.ae 28 dl.fA 84 dl.eu 80 dl.ez)) (J t5.iv.bm.dx 164 cN.hH (bk iQ.gY))))) (lC cD FB bd (ei kj.it 94 z4.gL z4.p9 99 z4.p8 95 z4.p7 (nd (pN uh.S 61 an q8.gP iS.gP tT.gP 97 qp.aS) (az uw.ag 91 cB.fL 1 cB.gg 2 cB.eY (ml gq.aI.cH) (o9 dO.S)) (aW aQ.bm.bw (iL n2.fj.S 50 rO ak af 145 zp 141 dM.ft))) (dQ tV.fj.ae 137 cM.p2 138 cM.p1 113 cM.p0 273 cq.f9 (fO rk.a0.cR.bg.S 60 dy.f9 181 dy.fx H 277 di.f5 (lg qX.b2 11 c6.eH 126 bv tL.aO 81 ch gS.aC)) (hX nr.cz.aj 23 c8.fm 96 cN.ev 70 cI.fM aw (lf (jo d5.it 317 dq.f5 160 dq.ev 62 zh 58 cT.eS j))))) (lY iP.cz.aD 46 z6.p6 196 kw gf.fF 77 z6.p5 (gp il.cz.bg.aj 62 dn.eH ak af 61 dn.p6 57 dn.p5 (gz yr.aj 91 bv aU 68 ch ak 64 af (lf (wB AF.eb.aI.b8.aD 79 dT.fP 409 dT.eB 137 dr.fM aw))) (gz l3.cK 75 ca uL.bH 86 bN bj.xD.jd 82 uk.jd (lf (eX jm.aD.aF 43 tH e_ 43 cL.f5 H 43 tH aP 1 cU.fo e_)))) (dQ ot.bQ.aj 35 cP.p5 36 cP.p4 181 ct.e1 178 ct.gk (m5 lP.bu (aG au.aC.S.gB)) (kh s6.bg.ag.bw 68 dI.gH dI.gm 19 dI.fC (lf (rP eE wN Bq 24 (aM cD dE e_) 65 (aM cF dE e_) aP))))))))
def Dw : ab dp:=(d3 b4 (bc ci (eR gF.gZ b1 57 z1.gm e_ 239 iJ X 235 iJ ad (bS d0.eP (gp nL.fj.S 96 se eQ dz 119 z4.gd 115 z4.fM (N H.n1.hM.gT 82 cy.fM (lf (wB uR.aF.bi.aD 120 dI.p9 342 dr.fN 81 c7.ez aw)) (fW bK)) (bD nb.cs 71 hJ aY aQ 118 sg ak 114 af (bM os.eP.aF 187 ap aB.eC.av b1.EQ.eC.av bd.pD.eC.av 1 dL.eA))) (eg uy.ae.ae 111 iz ao.sx 374 c5.gv 370 c5.fq (J jy.bV.fd 159 c9.eB (al ao.fr.aX)) (ej tZ.aI.aX 68 cS.eY ar ao 127 cI.fp 123 cI.ft (g4 re 51 vd 75 sb 131 cT.gg)))) (ei i3.a0.aj 93 z5.fm z5.gH 138 z5.gm 134 z5.fC (gA j3.aD 60 an t5.aC X.gB ad.gB 110 c4 lS (hX ot.e0.aD 118 cV.e1 263 dj.p0 55 ct.fK aw (ac oC.fr.jd.eD.kk 221 dr.p5)) (kN l8.fy.bg 129 wf aE K L 46 va (eo m8.bV.a0 55 cL.fp 110 rW iN 14 cL.ft))) (aJ mP.aX.bP 80 cq.fp 1 cq.ft 2 cq.f4 (kN ko.eb.dB 104 zE au X ad 85 c9.fK (al lS.kv.aX)) (en K.aD.bl.bH (mb BK.bg.ae 58 cT.p8 78 zM K 74 L))))) (c3 cj (az h3.pk.S 112 z4.fm 93 z4.fL 89 z4.gH (eg rz.ag 92 an b1.b0 1 z8.hH 2 z8.gL (gA rn.dK.S 105 Ae au X ad 103 lF b4 (mg qx.gR.aD 35 dI.fM 219 jK hj 147 lA cg 143 b3) (dd lD.S aB 31 rQ)) (gz iy.bV.b2.bp 65 uV aN 191 lm dk 187 e6 (eo iA.kl 48 mH 125 hB aE 14 cO.p0))) (dQ ko.bl.aj 23 cG.p7 79 cG.p6 73 cG.p5 48 cG.p4 (jW oN.cQ.aC 11 dj.eu 75 uV gf 183 lm gS (lf (q1 rq.cz.aj 23 dT.p7 131 bv uG.aO 115 H.bP.aO 111 uc.aO))) (j4 tX.aI.bu (iR rj.iF.ag 75 jc kW 1 cT.fM 2 cT.fx)))) (mi jm.fy.ja 11 z6.fm e_ 100 z6.gH e_ 11 z6.fm aP 43 z6.ez bd (nd (nI gF.gR.aS 11 dn.fM 134 dn.fx 71 fG kO 67 tx) (hX eI.bu.gR.aD 35 dy.fD 115 dj.fp 250 cB.ez aw (dc o6.y9.vr)) (e9 yx.gR.ae.cQ 239 dr.f4 dr.fE 53 c7.fq 50 c7.gb (ly kp))) (az jp.dJ.S 69 r6 242 ky 238 yl (fO o2.bH.a0 131 di.fm 106 rU au 14 di.gH (lf (tR oZ.eK.aD.S.ae 353 ap uL.bm.fF 169 dL.eB 337 h9.bg.hM.fF))) (iw ou.cf 82 ch qp 113 bv u3 109 d0.aO (aK ie.CJ.xD.S)))))) (c3 L.hU.bI (N uU.dh 215 F3 (cb gG.kl 52 z4.fu z4.gO z4.ev 165 z4.eZ (nd (qo gU.dv.ae 101 nX L 78 pv K 74) (N mh.hM.gT 82 ct.fT (aT tw.ik 11 dI.fP 1 dI.gK 2 dI.fp) (iM gx)) (aZ (qj oL.bl.dm.aX 83 dP.p5 159 xh ar 155 ao) (bC rK.cs 94 ey bF.cv bE.cv 196 ap hQ.av 192 g7.av))) (N bF.bu.cw 54 cG.gO (J kJ.aF.hU.gT 116 c9.p8 (fJ jn.x2.eC)) (ix rD.Cn.bm (ff gG.ag.aC 11 cT.fK 73 cT.fN 52 cT.ex)))) (nl aN.AZ (nd (xu g3.aX.dB.aj 76 an aY.bz.gP aQ.bz.gP 116 hQ.b0 112 g7.b0) (aZ (wA jp.S.b2 11 cV.hH 224 ug aE 59 ct.p2) (co ue.aF.ec)) (J lM.bl.eC.db 87 c7.fE (ms hQ))) (fR m9.bV 59 cq.fx 308 ct.fi 202 cP.p7 (J b4.pT.aI.hV 79 dP.p7 (bC pZ.cf 116 bv mY.aO iQ.aO 89 ch dk.aC 85 e6.aC)) (bT nG.AO.kv.hM.bu.bu 61 iz rM.fr.iH (n3 j.GW.aS))))) (bc cC (aJ m2.dv 98 z4.p9 103 z5.fE 99 z5.fD (cu l9.ag 109 c4 j5 ah.aO aU.aO 1 z9.eH (lj ng.cR.aD 127 cB.p5 e_ 197 r6 gx 252 sa dV 121 cy.p0 j (kf i4.b6.aj.cQ.S.a0 e_ 134 c7.fu bt 106 zx aE 14 dr.f9 e_) (dd d5.b6 aA 9 cO.eW)) (J X.ia.hM.gT 82 cA.p0 (ac rJ.bu.cw 178 dM.gL))) (nd (At sB rZ 24 65) (aZ (eX hY.bH.bg 48 cV.fo e_ 241 cV.fP H 50 dj.p7 e_ 64 yM e_) (aK L.AV.vv.cJ.fr)) (fO kV.a0.aj.cR.bV.S 70 c8.e7 155 cI.p2 H 373 cN.f5 (bk qQ.gY)))) (k2 eT.bl.aX 48 rX af 41 z7.fD 38 z7.f4 (bS b1.cY (aZ (jB pW.bV.aC 11 dy.fq 58 cq.eS aH 100 mf H 41 dy.gb) (bZ qP.aj 66 py H ah aU 179 b7 bt.aC.ae)) (fV uR.aC.bQ 61 cS.eY 17 cS.eS 350 cI.ev (e8 gU.dB 93 rW nj g2 kg 60 cL.p3))) (N iS.k7.fy 72 cy.fE (eG q9.bw.bP.bw 82 mG au X ad 19 da.e7 (lf (oS k4.bQ.ag.b6.bw 129 dL.gl dL.e1 17 dL.gk 195 ap aH.bu.d6))) (fh oU.bQ e_ 102 bv L.aO 17 cN.gl e_ 79 ch h9.ni (ji e4)))))))
def DN : ab dp:=(c3 iD (az nw.aj 16 HN 143 H6 140 HB (pK qf.aj 23 z1.eH 81 z1.f8 z1.fz 55 z1.gl (aR gS (lE m2.jq 11 z7.gO 137 z7.ev 86 z6.p0 aw (hi rh.ag.ag 73 rN cy.ev 1 cy.eZ (i7 Ce.cJ.ag.bw 110 ca aY.cR.bI aQ.cR.bI 17 dI.fi 101 bN lT.bl.fF) (aT kb.ec.aX 44 d9.gO 29 d9.ev 64 d9.eZ)) (kh oP.nR.a0 57 da.fE da.fD 138 da.fu (aG rR.aC.S.gB))) (az rf.ec.aX 49 As 29 c5.eW 69 c5.eH (J aQ.iG.hU.gT 190 dy.fM (ff g9.cx.aF 136 wS 471 dl.eW 1 ds.fq)) (ir sT.eP.aD 167 cI.eZ 265 cI.fo 63 cS.fm 38 cS.gH (e8 n5.dB 90 mH H.bm jy rt 64 cL.p0)))) (bc d0.eV (k2 g3.bV.bV.a0 158 an bq.iV 94 z9.gl 14 z9.e1 (fS eI.bu.gR.aS 4 cB.p4 77 r6 dZ 73 eM (e8 re.it 113 yI au X ad 79 c0.p0)) (aW q6.hM (co jk))) (dQ v0.aF.bw 281 cP.fD 117 cM.gH 17 cM.gm 65 cM.fC (aW H.nS.nS (ac b3.i0.gE.cw 92 c6.gO)) (de cg.gY.gD (aG ak.pT.vL))))) (nd (rP sB iC Bo 24 (aM cD nP e_) 65 (aM cF nP e_) b1) (ku aV (aJ l9 97 c4 1 u0 2 z8.fA (lQ j0.cK.S 52 cy.gK 92 cy.e7 H 261 c9.fD (em tl.bg.aj 70 dI.ft dI.f4 183 dI.fE 179 dI.fD) (dc cC)) (kh oP.cx.bg 53 di.gK dj.eW 135 dj.fi (lf (sG pH.dm.bg 36 cO.gK 231 ap H.cH.ce.bi 38 cO.fp 193 mq.mu.av)))) (nd (rP sB iC tt 24 (aM cD nP e_) 65 (aM cF nP e_) bd) (bT bt.rF.aI.hV 199 et u4 (ff jg.aS.fH 142 dT.e1 477 dl.p9 1 dT.gk)) (en nn.bV.hK (ac iY.mu.eV.dK.fy 120 cT.eY)))) (lC cD hI e_ (dQ cZ.jq.cQ 101 dn.fp 102 dn.ft 29 dn.fP 26 dn.gK (hX n7.aS 11 cV.gL 108 wC 64 ct.p0 aw (al bj.iH.bQ)) (aZ (wp zi.bl.ec) (cp ko.fH 55 cL.p6 cL.p5 1 cL.p4))) (nd (rP j2 wN Bk 24 (aM cD f7 e_) 65 (aM cF f7 e_) b1) (aZ (jo od.jr.cz.S 159 da.p4 79 dP.p5 155 yY 151 xh j) (lf (lB k4.bQ.dv 175 ap sP 103 yS 99 dl.e1))) (bD oF.b6.cd.bi.cd.bg.aj 109 cI.ez ak af 138 iz m4.fr.iH 134 rC.fr.iH (aK o3.bp)))))) (nd (yF g3.ia 11 GU 262 iJ au G4 48 GK) (e2 q4.bu.bu.dh 151 iJ iN (bS qI.bm (bc jk (N my.eC.db 63 cy.gn (ac dz.aI.bV.fd 159 c0.gb) (lf (yu lH.S 138 d9.fm d9.gH d9.gm 47 rO))) (J jn.bm.bV.fd 159 da.eY (lf (l5 os.nR.bQ 19 dL.f9 17 dL.ga 191 ap aH.mu.av)))) (gp dF.ec.cz.ae 54 wn K L 186 c5.eB 182 c5.fT (dG dN.hL.cH (i7 ut.dJ.g0 179 b7 aY.cK aQ.cK 17 ds.hH 78 pt aH)) (hX oq.bm.aS 11 cI.fD 80 c8.e7 147 cS.ex aw (hZ d5.cx.aD 74 cU.hH e_ 74 cU.gL e_ 191 cT.er aE 58 cU.eS j)))) (c3 bE.aF (nd (ov nE.b6.aj 23 z9.fM 141 c4 gf.aO 115 bq.bu) (J b1.bi.bV.fd 159 ct.fm (aG mY.fQ)) (nc m9.jq.aC 11 c0.eY 144 c0.p9 46 c0.eS (eo rs.a0 59 cL.fD 107 mH q4 14 cL.fu))) (N hO.aF.vz.bi.aO 59 cq.eZ (md oK.aj 23 dP.fA 143 fe gf 109 dP.eu (iL o2.b6.a0.aj 230 ap aY.qV aQ.qV 82 c6.gb 78 c6.gd)) (hX ua.ag.aj 23 cN.fE 95 cN.eA 69 c8.ex aw (lf (rP eE sc BE 24 (aM cD dE e_) 65 (aM cF dE e_) aP)))))) (cb ru.S 98 z2.eY z2.eS z2.fm 43 z2.gH (qR bK (bc gu (N cj.i0.bo 75 cy.fo (g1 qe.aj 23 c0.gj 164 mK 138 lA aw) (dd cZ.a0 aA 21 cO.f4)) (bD qn.aX 71 ca aE.rF.bH uL.bH 82 bN bF.jd 78 bE.jd (h6 gG.gC 100 mH bt 56 cO.fL H 52 dM.e7))) (lE gG.aX.aj 47 cG.p2 55 cG.p1 56 po hO (ek qn.eK 82 bN e_.dK.bI 1 dj.fL 2 dj.gg (ij Co.cx.ae 100 bv qL 81 ch bj.n1 77 br.n1)) (j4 tM.bu (g4 il.eK.bH.ae 40 cT.p0 131 dq.fL 128 dq.gg)))) (gI kb.eb.b2 4 z6.fC 96 nW X 92 ad (eJ oI.gY (fV sR.S 82 hD 106 dy.fo 94 dy.fU (mb ut.dJ.bH.ae 66 dT.fp 187 b7 ar.yd.ae 183 ao.yd.ae)) (aZ (oB rl.bV.aF.aD 59 ds.fT ds.fA 125 lJ cg 121 b3) (bk kp))) (hi un.aF 48 mL mf 1 cP.gv (jW qn.ia 11 di.fq 103 ca H.cY 86 bN aw.dK.bI (ij na.fg 119 bv iX.aO 88 ch tb.nh 84 ui.nh)) (jz hj.cQ.mv (aT i3 11 dY.eY 1 dY.eS 2 dY.fm)))))))
def Dt : ab dp:=(cb eT.bl 36 GD Gn Gq 1 GA (cb m8.cQ.ae 225 Hj Hd Hg 213 GS (aJ ux.dm 11 z1.fN 1 z1.ex 2 z1.fL (lQ sU.b2.a0 130 z3.gk 75 dX iN 14 z3.er (qR b1.bu (fR uO.ag 71 xj 146 cy.fU 1 cy.eY (em uZ.bP.cs 186 dI.gk dI.er 121 dI.eB 117 dI.fT) (ji cg)) (bA i5.cR.b8 131 da.eB 1 da.fT 2 da.fA (e5 n4.aj.ia.dv 142 dL.fo 90 w6 ar 86 ao))) (bU aH.aO (bD pR.eV.b8.aD 65 sa aY aQ 174 v7 ak 170 af (co j.AV.aF.ec)) (bD gr.eb.q5.bi.aD 150 cS.ez aY aQ 86 xr fX 82 d8 (ac pw.fr.hK.dh 154 cT.f4)))) (eL o4 (gA qJ.cz.S 90 an e_.ae.ce lM.ce ub.ce 114 c4 bt.aO (aW lT.nS (aK ao.cJ.kY.ib.fr)) (bT dk.kv.pT.hK.dh 305 ky dk (aT iP.ik 11 dM.eS 1 dM.fm 2 dM.gH))) (az jp.dJ.bQ 19 cM.p8 17 cM.p7 37 cM.p6 (fO ot.bQ.aF.a0 67 c9.fz 166 pz au 14 dP.fu (iR rq.g6 84 ch iE.aC 1 c6.gL 2 c6.p9)) (ix ar.Cn.bm (lc k8.aS.cs 115 dq.gd 116 dq.fM 70 dq.fx 66 dq.gn))))) (az fk.ec.aX 40 z2.gl 29 z2.e1 60 z2.gk (ku jl (lj j3.aD 60 an oa.aC 60 an om.aC 110 c4 cg 106 z8.eW j (cu s9 122 et ah bK ea 1 cB.fp (g1 uJ.bQ.aC 11 dI.p3 78 dr.f8 144 c0.fi aw) (lf (q0 dz.bI))) (bT ah.AO.kv.hM.bu.bu 61 iz H.kv.iH (aK kn))) (qd ko.bl.iF 11 cG.fm 159 xt 91 cG.fi aw (fh wk.bQ e_ 58 wG bd 17 dj.eH e_ 93 zP j (lf (rL kK.S.q5.aX 91 iK ie.wj 29 dT.fA 111 gx.cJ))) (nc rs.aF.iF 11 c8.gO 186 c8.p6 103 c8.ev (al iX)))) (d3 gN (N k9.iH.ib.bz 57 dn.eY (bT qm.aI.hV 193 et gx (cp oV.dK.cR.aD 63 ds.p1 ds.p0 113 dT.e7)) (fS qP.S 66 pt 179 b7 H.cK 175 j.bg.ae (fW jT))) (N dz.bH.hU.bo 161 cy.eu (bD uE.aD 86 zP bj br 67 wG K 63 L (al ak.pT.bH.bH)) (J bq.r4.iv.bm.dx 164 c7.fL (bC tn.dm.cs 144 hB jl.aI ju.aI 89 jc ke 85 iX)))))) (aR br.eK (aR jV (pK kZ.aj 23 z3.hH 74 z3.gL z3.p9 48 z3.p8 (hi nL.gR.bw 92 z8.fu z8.gO 19 z8.ev (nd (rP j2 wN zy 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (h6 jg.cd.gR.a0 89 iK bt.pk 178 et jv.bP 14 dT.eW) (al fI)) (eG uO.a0.ag 83 rN X hW ld 1 da.ga (iL rK.eK.aD 184 ap aY.mu.av aQ.mu.av 63 dL.p9 26 dL.p8))) (hi ul.ae 62 Aq c5.p3 46 wV (fS kL.S 60 ey 162 ap ed 158 d0 (lf (qa eE vy 24 65))) (aZ (eX d5.cz.cf 74 cI.fL e_ 74 vh H 74 cI.fL aP 122 cI.gg e_) (aK aV.bp)))) (bS om.bu (nd (pN iT.cx.cJ.S 81 an e3.i2 uN.gP d0.i2 99 b4.ia.aS) (J lP.i0.bo 68 ct.p8 (fJ aB.ib.iG.eC)) (du qh.it 129 lo nj g2 kg 88 rN b4 (ac j5.bu.cw 186 cL.ga))) (N jv.o5.eD.aI 50 cq.fK (bD ko.eb.fj.S 81 rN ak af 126 lo X 122 ad (bZ sR.g6.bg 106 hD H.kY.cJ mT.cJ rB.cJ 269 bv bt.jQ)) (en oo.ae.eh (e8 jA.ec.cf 65 zh au X ad 167 dq.f9))))) (aJ h3.a0 133 z2.hH 81 z2.gj 14 z2.f5 (nd (kH gf) (nd (nI nE.aD 59 z9.fE 158 z9.fD 65 an eQ.aC 61 dz.aC) (ei uC.ae 51 wT uV 177 vl 173 lm (bZ q7.aD 173 b7 iZ.ni.ae iY.ni.ae mW.ni.ae 76 u6 hO) (dd ut aA 9 cO.ev)) (aZ (nI li.eb.aX.aj 59 cA.gL 60 cA.p9 73 yM K 69 L) (iM kn))) (nd (lz L.xQ) (kh hY.aS.aj 60 dj.fM dj.fx 112 dj.gn (bM qe.b6.bw 190 jK e4 fI iD 19 c6.gk)) (aZ (jo ts.cJ.b8.aD 47 c8.gm 281 cN.fU 245 cN.fi 76 cI.f5 j) (aG K.bu.iG)))) (mi tv.jq 11 z6.p4 e_ 142 z4.gb e_ 11 z6.p4 aP 87 z6.eA bd (dQ uJ.iF 11 dn.p0 52 c5.e7 790 c5.fC 17 c5.f6 (ek uE.b6 90 bv pq 1 dy.eu 2 dy.ez (hT gr.ec.aX.S.ae 90 ds.e1 L 74 wg k0 70 jZ)) (gz l3.gC 93 ca fY.cY 94 bN X.fj.bI 90 ad.fj.bI (o9 K.fr))) (N aN.dt 334 ct.fA (aZ (lL Ad.cz.S.ae.gR.bg 36 di.hH 107 dj.eA H 38 di.gL 69 vf qb) (lb ah.bg.pF.bg)) (aZ (lZ rl.bV.aF.aD 59 dI.f9 dI.ga 125 lJ lS) (co gx)))))))
def DF : ab dp:=(nd (rP j2 iC xY 24 (aM cD f7 e_) 65 (aM cF f7 e_) fY) (nd (kH e_) (aR lG.bP (cu mj.S 80 dX dO cj dS 54 z3.fi (bc bd.bu (nd (pI ng.cx.bg 58 cy.fA aE K L 125 cB.fu) (ac e_.eV.aI.eC.bu.bz 393 dT.ft) (la jm.fy.S 138 d9.fo d9.fU d9.fi 47 d9.eW)) (md ot.bQ.aF.ag 67 da.eH 373 ky nD 1 da.f8 (ac oM.pD.eP.aI.db 103 dL.gg))) (gI i3.S.S 134 c5.e1 79 fG ah.aD 75 aU.aD (ir mZ.aC 11 dy.p8 135 dy.p7 64 dy.p6 60 dy.p5 (lf (w7 pg.dK.ag.bw 86 c6.fp 363 ap q4.hL.bI 19 c6.ft))) (nc li.dK.b8.bw 75 cS.hH 199 cI.gg 19 cS.gL (iM gu)))) (nd (kH th) (nd (tB sE 90 an b4.aS 58 ed.gP 54 d0.gP) (aZ (uS pR.aj.ae.b2 4 cP.p7 174 ct.fD H 170 ct.eW) (d2 j.v9.pl.bm)) (fV re.ec 59 cS.ev 1 cS.eZ 2 cS.fo (ac ob.bo 171 cL.eA))) (dR oj.S (aW my.nS (ql lK.bl.b6.aS 11 dl.fM 35 dl.fx 181 ap tX.hL.bI 177 e_.xx.hL.bI)) (gz jA.dK.e0.bg.ae 73 rY ao 185 wU K 181 L (hT tn.dm.S 73 jc aw 136 hB ed 132 d0))))) (dR ui (bU dO.eN (bc jX (az n7.b6 60 ct.p0 1 cB.e7 2 cB.f6 (fJ j.sx.aI) (lf (m0 h3.a0.aj 89 d1.gO 98 d1.ev 94 d1.eZ))) (fS kZ.eb.ja.ae 224 cA.gk 64 yz K 60 L (aT tn.dm 11 cO.fK 1 cO.fN 2 cO.ex))) (fR ox.dm 88 w0 216 cG.eA 1 cG.eu (ck e_.bi.ce (ql qX.jq 11 dT.fN 23 dT.ex 108 bv e_.eK.aO 104 e_.mu.aO)) (de L.gY.gD (em wE.aI.eN 53 cT.fT cT.fA 17 cT.eu 25 cT.ez)))) (N aw.bu.dh 45 z6.gO (ei j0.cz.ae 44 dn.gk dn.er 201 dn.ga 89 dn.eB (bT ah.iG.dt 237 iB X.bH.kB (ac kJ.vL.hK.bm.dx 164 dr.gm)) (aZ (qK k8.jq.cQ.S 146 c0.er 70 c0.eB 66 dr.ft) (cp rs.ag 59 cL.p0 cU.e7 1 cU.f6))) (N L.aO.hU.bo 308 cy.f4 (J oC.mX.aF.sk.aI 115 cA.fD (al rC.bH.bH)) (fO sN.iI.a0 74 cN.ev 130 yI aE 14 c7.p5 (g4 lH.cz.cd.aX 115 yt 67 zH 252 dY.fL)))))) (d3 ki.cH (aR jX (bU K.mu (nd (lL kj.eV.S 92 z7.eu 193 z5.eu H 94 z7.p3 95 kw l6.bI) (dQ sR.eN 91 cy.hH 92 cy.gL 17 cy.p9 25 cy.p8 (lc tO.S.aC 11 dr.fD 199 dr.fm 236 dr.gH 67 dr.fu) (g4 d5.a0 46 d9.fx 195 d9.gn 14 d9.eA)) (dG bt.e0.cH (aG cX.aC.S.gB))) (eJ L.GB.cJ.fr (gV h7.iI.fH 80 c9.fK 755 dT.gd 1 c9.fN (lf (pd lU.bH.bg 48 ds.fP 138 ds.gm H 50 dT.ez 141 wS))) (hX uW.cx.aS 11 cI.gl 81 c8.fi 201 cS.fC aw (al d8)))) (bS oY.bu (ef qJ.gZ 114 c4 ke iX 72 an aV.i9 68 cC.i9 (bD n7.jr.aj 111 Ak bj br 112 hJ eQ 108 dz (bC oJ.fg 89 bN ar.vL.cH ao.vL.cH 74 ca jl.bI 70 ju.bI)) (iw n7.fg 123 fe dz 72 da.fC K 68 L (nz jA.gZ 57 cL.fi cL.eW 130 r9 X 126 ad))) (az ox.iI.ae 73 cq.fz 505 cB.eZ 502 cB.fo (ck kP.aF.aC (e5 uZ.bP.dm.aX 204 c6.eS 103 c8.p3 ar 99 ao)) (de tG.gY.gD (bk qb.hK))))) (c3 cg (qR bq (ol nF.ia 11 z8.p2 95 an ci.i9 105 c4 gS (im kO.nS (ml eQ.aI.cH) (dd tF aA 21 cO.fu)) (ek oJ.cd.ag 89 bN jH.fj.bI 1 cA.ga 2 cA.gj (hT eT.gC 100 dX k9 56 mF sI 52 jk))) (N bj.ib.hU.bo 60 cM.f8 (k3 od.jr.cx.aD 53 cq.eS aY 53 cq.eS aQ 115 mL e_.kB 50 dj.gH e_ (ql qe.aX.aj 59 dT.gj 60 dT.f5 150 wS ak 146 af)) (j4 bE.bi.bu (bk kW.gY)))) (hi m2.ec 82 z6.eA z6.f9 1 z6.ga (eJ pS.gY (J aQ.gP.cJ.aO.aO 222 dj.gk (ac nj.vv.D8.fy.bz 172 ds.ga)) (fS t0.b2 4 cN.p0 85 bN nJ.bI 81 qI.bI (e5 tW.ag.fg 61 cL.eW 134 r9 bF 130 bE))) (nd (rP j2 wN rT 24 (aM cD f7 e_) 65 (aM cF f7 e_) e_) (aW aH.bm.bw (al ke.kv.aX)) (de gq.kY.ib.fr (cp tq 38 ep dX 1 dY.eA)))))))
def DM : ab dp:=(nd (rP yE.it wN xY 28 (t9 cD DA bq) 105 (aM cF f7 bt) b1) (az g3.eK.ae 52 Gc 37 Hh 34 GL (aR dz.bP (bS iY.bm (ei kj.cd.ae 68 z7.fC pv 99 z5.eu 95 nX (lj pW.eP.aX 35 cy.gv e_ 128 mf hj 41 cq.fm e_ 86 mf j (aK oy.io) (fb cD fB e_)) (dG ak.fj.cH (iL os.nR.aD 183 ap cX.eC.av cl.eC.av 63 dL.fK 26 dL.fN))) (e2 L.AZ.bi.cJ.aO.aO 330 iz af.kY.sx (e9 rm.aI.ae 58 c9.ev c9.eZ 41 c9.fo 94 c9.fU (fJ bj.ib.iG.eC)) (de rR.o5.bp (kf o8.S e_ 53 cU.fN e_ 56 cU.ez H 52 cU.ex e_)))) (ei gU.dv 93 z5.eu nX 149 z5.fL 145 z5.gg (nd (rP eE iC x7 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (aW b3.nS (bk d8.ae.eh)) (fO g9.bp 73 da.eu 136 da.eB H 433 dr.ga (cp cZ.g0 46 cL.er cL.eB 19 cL.fT))) (ef sX.aj 61 lF bj br 107 nV K 103 L (dG bK.bm.cH (bM uw.ag.cd.aF 264 bv tL.aO ah.jQ aU.jQ 1 c6.ga)) (en au.cv.bH (aT s0.bP 59 dq.gm 1 dq.fC 2 dq.gv))))) (cb h7.ag 38 z2.fN z2.ex z2.fL 1 z2.gg (aJ gU.dJ.ag 88 se 1 z4.fN 2 z4.ex (m6 jH.S (e2 eM.iG.dt 237 iB gN.bH.kB (co ki.aF.ec) (ac rr.kk 84 d1.fA)) (bD pZ.aD 96 bv bj.ib qL 77 ch t8 73 aP.n1 (g1 fa.eb.aj 23 dM.ev 77 cL.e7 51 cO.er aw))) (N j.ib.hU.bo 55 cG.fx (bD oX.aj 67 ch bF bE 102 bv jt 98 gX (bZ wQ.ag.wj.S 161 et aE.aF.bP K.aF.bP L.aF.bP 94 iK l6.wj)) (ej oF.b6.cd.bi.cd.bu.aD 64 vc jU ka 63 c8.gl 26 c8.e1 (bk jw.gY)))) (eR fc.gC e_ 97 nW k9 53 z4.er b1 49 z6.eS e_ (eJ u4.gY (bD ko.it.aj 104 lo cX cl 85 xj ak 81 af (e8 sN.cf 98 AH au X ad 78 dr.er)) (gW uT.jr.aj 172 b7 qG.cQ oG.cQ 107 c0.gm 103 py j (e5 nA.fg 53 dM.p4 54 rQ bF 50 bE))) (oT nA.bP.S.S 62 cM.fm 105 uz ah 101 aU (ek ou.b8 97 bv iE 1 di.ez 2 di.fK (ac d4.pD.eP.aI.db 97 dL.gK)) (du qX.aj 77 ch e4.aC fI.aC iD.aC 112 bv lP.aO (lb k9.pF.bg)))))) (eL iY.aF (az kb.jq.S 44 FJ 85 Fq 29 FU (az gG.kl 52 z4.gK 165 z3.p4 14 z4.fp (oT nF.S 105 wF 67 an dk.aC 63 e6.aC (nd (oB kt.ec.fj.bg.aj 247 cV.fi cV.eW 203 je nq.cH 199 mh.cH) (ac lM.pF.kY.eF 85 c0.p1) (al ow)) (ek tz.aF.b8 97 fe e_.bV 1 da.p6 2 da.p5 (bM pH.dm.bw 189 ap q3.bP.av uj.bP.av j.hK.bP.av 19 cO.fP))) (nd (At sB Dh 24 65) (aW aE.eC.bH (dc aQ.bm.fr.vr)) (nc sN.jr 11 cI.gb 118 we 62 cI.gd (lf (ro jD))))) (nl ea.AZ (nd (zS iT.cx.bg.ag.bw 107 an sV.b0 tN.b0 17 z9.p1 83 aH.bz.gP) (hX qc.iF 11 cV.f9 121 c9.gm 104 hJ bq (co ka.aF.ec)) (aZ (oD oi.ag.bg.S 73 c9.p5 102 fe H.bV 98 j.bg) (lf (rP fk iC rZ 20 (aM cD kD e_) 25 (aM cF kD e_) e_)))) (qv jx.aj.ia 4 cq.gm 56 cq.fC 52 sj (J iZ.D8.aI.hV 77 dP.hH (g1 qg.eP.cR.aD 67 dl.ex 206 dL.fu 130 c6.p8 aw)) (ix i6.pl.bm (bC gG.b6.cd.bi.aD 145 hB cX.gP.v9 cl.gP.v9 76 mH dN.fr.hM 72 ie.fr.hM))))) (nd (qa eE Bo 24 65) (bc oM (nv qU.S 70 an pc.aC 112 wF X 108 ad (lE pW.aX.aj 47 cB.hH 55 cB.gL 62 mL hO (bZ g9.cf 140 et e3.aO u3 d0.aO 77 hC qp) (dd gr.b6 aA 9 cO.fU)) (fS l3.dJ.aS 4 c7.fP 111 ca K.cR.bI 107 L.cR.bI (ms jk))) (az cZ.aj.cs 96 cM.eu 62 cM.ez 607 ct.ez (ck b1.FZ.h8 (lf (ov ou.cd.aj 23 c6.fz 139 bv au.eN.aO 113 kc.aO))) (jz ka.Gw (ac cl.gP.eF 651 dY.fU)))) (N aA.ib.bP.dh 58 z7.fP (eJ ke.gY (gy mT.aI (dc aH.bm.fr.vr)) (aW e_.GB.bI.aD (ms gu))) (qd sJ.aD 56 cy.ft 279 c9.fz 106 wr hO (aW i6.aD (lf (pN iu.aS.eK.bi.bg 177 ap ci.fr.hM.fF aV.fr.hM.fF cC.fr.hM.fF 225 bq.vz.fj.bI))) (bD mQ.cx.ae 80 bN bj.xD.jd uk.jd 77 ca aE.rF.bH 73 uL.bH (fb cF hI b1)))))))
def DB : ab dp:=(ph gU.cR.bg 112 cU 214 cT (qq h3.ag 218 H1 267 Hs 220 HW 1 Ht (aR fX.bl (pK i3.aD 35 z3.ev 164 z3.eZ z3.fo 53 z3.fU (lE kj.q5.aj 23 z7.eW 120 z7.eH 94 z7.gK aw (lQ g9.a0 124 cP.fE 97 hC au 14 cy.f8 (bM xl.bu.aD 79 bN t5.fF X.jd.fF ad.jd.fF 65 dI.gd) (lf (rP qt wN Bq 28 (aM cD hI e_) 105 (aM cF hI e_) aP))) (aZ (nI sT.aX.aj 59 da.fU 60 da.fi 72 ze K 68 L) (bZ na.cf 92 ch dO.ce gu.aC t7.aC 123 bv tM.aO))) (gp gs.iI.nR.aD 76 fG rA.bw qm.bw 63 c5.f8 26 c5.fz (ej nC.ag.ag.bi.bu.aD 60 vf jU ka 63 dy.f5 26 dy.hH (lf (l5 kK.gR.aI.ae 136 dr.p0 41 ds.gb 172 wS j))) (fV rm.aD.S 66 ze 200 cS.fz 53 cS.gl (bZ g3.dB 90 dX au.bQ o3 ad.bQ 64 mF kr.bl)))) (bc qI.aI (nd (tB sE.S 66 an b4.bi.gP 106 ed.b0 102 d0.b0) (gW jp.g6.bw 67 pm jw jD 17 cB.p0 226 ug bO (bk lk.eh)) (aW fY.bm.xF (dc j))) (N oj.aF.vz.bi.aO 62 cM.fM (aZ (pj BT.b6.cd.bi.aD 183 di.p3 317 iq tI.bI 491 cS.fN 58 c9.f4 j) (e5 uC.iF.dv 93 c6.f6 266 c7.eA ar 262 ao)) (ns te.dJ.aS 4 c8.hH 113 c8.gL 109 c7.e1 (lf (l5 sD.bP.aX 57 cT.gj 29 dq.fD 77 vd gx)))))) (N jZ.eF 138 z2.fE (bU aA.bQ (bc g7 (N tr.cJ.hU.bo 156 cV.fA (d2 t5.pl.bm) (ac gf.bH.bz 199 d1.f4)) (gy kP.Gv.eC (aT i4.cd.ag 43 cO.eH 1 cO.f8 2 cO.fz))) (nd (qK v0.bP.S 93 v8 70 cG.fz 58 cG.gv) (bA ii.eP.b8 57 c9.p4 1 c9.p3 2 c9.p2 (n3 xI.ae.bV.aS)) (J ka.Gg.eD.kk 221 cI.p6 (ij ok.S.ae 53 kA jZ 108 ym cX 104 cl)))) (lC cF hI b1 (hi nA.aI.a0 49 dn.fi dn.eW 94 dn.eH (J uU.dt 334 c9.hH (fJ ci.mX.eC)) (bA dF.jq.b2.ae 164 u5 58 cN.eu 54 wK (cp m8.fH 55 cL.p3 cL.p2 1 cL.p1))) (nd (pO il.eN.cR.ja 4 cq.f5 85 cq.fp H 81 cq.fE) (J lP.r4.eF 166 cA.fp (al qm.bH.bH)) (en aQ.wd.bl.bH (h6 rs.bp 172 hB b4.x2 71 dY.fp H 67 dY.f8)))))) (d3 e_.AV.cH (aR o4.bl (ei BN 45 ap ca 171 z3.fC 60 bN (az pf.b8.jr 4 z7.hH 70 z7.gL 61 z7.p9 (e2 dS.xQ.bu.dK.fy 131 je ad.cH (e5 oi.ag.dm.aX 116 c7.gg 77 wC ar 73 ao) (fb cF mD aV)) (dG oy.e0.cH (aG j.o5.aC.S.gB))) (ef i3.S.cz.ae 83 fG ar.Dg.aD ao.Dg.aD 154 pA b1.mX 150 uu (dG L.cR.cH (ac ao.aF.bl.dt 342 dl.fi)) (eG sT.aX.bl 64 rY ah bK ea 1 cI.eW (ff jA.dK.aF 49 cT.f6 170 cT.fC 1 cU.e1)))) (nl ui (gp hR.bl.bi.cd.eN 99 an K.mu.b0 L.mu.b0 17 z9.eA 25 z9.f9 (dG H.cR.cH (aG ob.fQ)) (dG d8.e0.cH (cp iP.g0 50 cL.eS cL.fm 19 cL.gH))) (N aQ.bH.hU.bo 164 cP.fu (gV nb.eK.aD 106 dP.gg 266 da.eS 65 dP.eY (d2 aN.aI.pl.bm)) (fV ud.dK.aC.aF.b6 126 c7.fu 1 c7.gO 2 c7.ev (bM dF.ag.eP.eN 72 jc q3 uj j.hK 19 dq.p5))))) (c3 kr (qR aU (eR sW.cf bd 90 an kr.mv 82 z8.p6 e_ 70 z7.gL aP (mV h7.iI.ag.bw 76 xj bj br 17 cB.fT 111 lo hj (ij tu.dv 74 hC mh 141 et ar.cJ 137 ao.cJ) (dd rE.S aA 115 dY.gL)) (eG o2.bH.ag 224 ca e_.e0.bH aE.eb.bH aP.e0.bH 1 cA.gd (g1 yU.aj 23 dM.eH 77 cL.eZ 51 cO.eS aw))) (az y4.dJ.b6 93 sF 1 cM.f4 2 cM.fE (gy bt.kY.aI (bZ lW.aj 101 bv iZ.cJ iY.cJ mW.cJ 78 ch bt.aC)) (J pw.jQ.bP.eV.dK.fy 134 c8.eu (aK b1.mX.bp)))) (ef tg 102 ym cX cl 55 kA k0 51 jZ (eJ aY.gY (J bd.pT.F4.eF 161 dj.gl (aK e_.FN.eC.gD)) (aZ (lL qn.bV 24 cN.p6 108 bN ak.nh.jd 26 cA.gn 71 ca mq.bH) (e5 BD.fg 57 cL.ev 94 b7 bF 90 bE))) (cu jx.eV.aF 94 mf aE K L 1 cP.fM (eG od.dm.cJ.aF 233 vl aB b1.EQ bd.pD 1 di.fM (d2 nk.aI.pl.bm)) (jz cX.cQ.mv (fb cF dE b1)))))))
def Ds : ab dp:=(d3 hW (N nB.eV.bz 141 Hf (aR g5.bP (bS ie.bm (bc kn (eg sX.ag 103 nV jN 1 cP.gk 2 cP.er (bk bt.ae.eh) (g4 gr.a0 42 d9.fT 155 d9.fA 14 d9.eu)) (bA m9.jq.bP 40 da.ex 1 da.fL 2 da.gg (aG L.o5.aC.S.gB))) (bS ki.aF (J tr.o5.eD.aI 58 c9.fE (al af.iH.bQ)) (ix K.hU.pl.bm (lf (pd rm.bg 36 cU.fx 92 cU.p7 H 38 cU.gn 54 cT.f6))))) (c3 dz.bI (cu g3.bV.fH 158 an cj.iV ow.iV m3.iV 1 z9.fm (aZ (wJ kV.ec.b2.aF.aS 11 cV.eH 70 sa aH 167 cP.fA 163 v7) (aT uC.iF.cQ.S 117 c6.eA 151 c6.fx 61 c6.gn)) (iw ma.dv 118 yg af 97 hJ jl 93 ju (ij gr.dv 54 rO af 149 dM.ft K 145 L))) (N ar.bg.fd 75 cq.f6 (dG ci.hL.cH (bM i5.aj.b2.ag 195 jK cj ow m3 1 c6.gj)) (eG oF.b6.cd.bi.cd.bm.aF 68 vc aE.kv K.kv L.kv 1 c8.p0 (bZ nr.S 78 sb au X ad 58 vd aN))))) (nd (yw j2 24 65) (ku rt (gI iT.cx.bg.b2 4 z8.gn 99 an dZ.b0 95 eM.b0 (hi nb.S 102 ct.gg sg 63 hJ (al bt.eK.bH) (ac gq.bz 76 d1.gk)) (bT bq.AO.kv.hM.bu.bu 61 iz qb.iH (eo yT.a0 44 vj 85 zw aE 14 cO.p7))) (dQ rn.aj 201 cM.fU 202 cM.fi 97 wr 93 cG.f5 (gy K.kY.aI (ac iS.bP.dt 334 dl.fz)) (fV tD.cQ 74 c8.eW 171 c8.eH 167 c8.f8 (cp ua.bl 49 dq.f4 dq.fE 1 dq.e7)))) (nd (l5 gF.aX 41 mc 29 z6.fL 61 kA j) (az nA.aI.cQ 91 dn.fm 49 dn.gH 45 dn.gm (fh yR.cd.b8 e_ 88 fe jH 1 vi bd 2 dy.fp e_ (eo jg.aS.bV.a0 142 mK 190 jK aE 14 dT.f6)) (J cX.xQ.bi.cJ.aO.aO 585 dT.fx (iM jT))) (nd (wx u1.aF.jr.a0 98 rb 122 Ae aE 14 cP.fo) (ir yi.cz.S.bp.aC 11 di.eW 185 cA.fK 59 vc 55 di.f8 (aG bE.S.gB)) (bD l3.ho 86 bN cX.sk.bI cl.sk.bI 83 ca K.aD.bl 79 L.aD.bl (bM tW.b2.eP.cx.aF 117 yt ah bK ea 1 dY.ez)))))) (aJ qf.ag 51 z1.ev 1 z1.eZ 2 z1.f6 (aR kr.bl (bU au.eN (eg j3.b6 64 an b1.ce 1 z8.fU 2 z8.fi (aJ q9.cd.bi.b6 169 ct.fD 1 ct.fu 2 ct.gO (lf (tJ s8.cs 74 rU bF bE 153 c0.p2 150 cN.fA)) (iM bK)) (gz tz.aF.ae 68 xg br 101 wu h5 97 d4 (i7 os.ag.bw 187 ap sV.av tN.av 17 dL.p1 101 ey bO.cv))) (N aE.vz.bu.cw 53 cG.fp (bA ma.b8 67 c9.fx 1 c9.gn 2 c9.eA (hT kK.gR.iI.S 174 mK fY 148 lA cj 144 dS)) (aZ (qj hY.cQ.dv 80 cS.ga 72 da.ft ar 68 ao) (lf (ro aQ.yb))))) (qu ak (ef nF.fj.S 117 c4 eQ.aO dz.aO 97 an lM.ce 93 ub.ce (gV tk.g0 75 cV.gb 297 dP.gk 19 cV.gd (aK pw.fr.hK.gD)) (bA tu.eP.dJ 11 c7.f9 1 c7.ga 2 c7.gj (o9 bd.S))) (e2 X.cH.o5.eD.aI 126 sa rR (aW ah.aO.bH (hT pZ.cf 116 bv lR.aO 89 ch dk.aC 85 e6.aC)) (en ah.ae.eh (aK aA.bQ.bp))))) (cb kj.S 64 z2.p3 z2.p2 z2.p1 225 z3.fP (bc mY (nd (pN rz.aj 56 an tS.gP rr.gP ad.bi.gP 96 bt.b0) (nd (pd wk.bV 24 cB.gd 84 dy.f8 H 26 cB.fM 89 dy.eB) (ff lU.eV.aD 129 ds.fp 464 dl.f5 73 ds.ft) (dd gs.b6 aA 9 cO.fo)) (aZ (qo pJ.dm.dm.aX.ae.b2.ae 118 wv L 73 wO K 69) (ac iQ.bo 169 cL.gn))) (dR lq.bg (J b1.FZ.sx.cJ.aO.aO 410 cA.p2 (lf (oS k4.cz.dJ.bw 73 c6.ex c6.fL 17 c6.gg 237 ap aH.qV))) (en ui.bV.hK (cp fa.aj.aF.ag 55 dq.gk dq.er 1 dq.eB)))) (aJ m2.ec 82 z6.p0 1 z7.e7 2 z7.f6 (gp pb.bQ.cz.ae 56 w3 K L 77 dn.fC 73 dn.gv (iw uC.bp 185 lm aN 67 wT X 63 ad (ac ob.bP.dt 334 dl.fE)) (aZ (rP l4 iC yc 32 (aM cD fB e_) 145 (aM cF fB e_) b1) (g1 fc.aX.aC 11 cU.fi 96 cU.fL 49 cL.f5 aw))) (N dO.r4.ib.bo 518 dP.e7 (ck K.kY.h8 (n3 d0.ae.bV.aS)) (de ah.AQ.hK.gD (aT gF.dJ 11 dY.p9 1 dY.p8 2 dY.p7)))))))
def DD : ab dp:=(d3 aB.cH (az gU.eb.cQ 78 GR 93 Hk 89 He (aR sI (cu eT.b6.dm 70 dX iN aE.iF aP.aC 1 z3.fz (k2 nw.bl.a0 92 kw aN.fF 129 z7.eu 14 z7.ez (cu u1.aF.jr.ag 98 lF X hW ld 1 cy.fN (ac tS.vz.bi.k7.fy 75 dI.gl) (lf (qz ci))) (eG n7.dm.bw 111 yg aA aB dD 19 da.e1 (ac iQ.pD.eP.aI.db 107 dL.ez))) (ei kZ.eb.cQ 180 c5.eB c5.fT 56 c5.fA 52 wn (aZ (rP l4 iC B5 32 (aM cD fB e_) 145 (aM cF fB e_) b1) (g1 oN.dJ.bQ.aC 11 c6.eu 153 w6 115 ds.ev aw)) (hX re.jq 11 cS.p5 133 v2 63 cS.ev aw (e8 kb.cx.bg 81 xa aE K L 48 tH)))) (N dS.iH.qV 116 z5.fU (eg j3.b8 106 c4 kW 1 z9.fK 2 z9.fN (aZ (jB pJ.dm.dm.aX.aF.iF 11 cV.ft 65 vf kP 285 ep K.cJ.ja 17 cV.f4) (hT mQ.S.S 73 ca ki.aF 92 bN K.g8 88 L.g8)) (J aN.hU.bP.eV.dK.fy 259 cS.eW (ac aE.eC.bu.cw 139 dM.p7))) (fR sK.cz.bg 115 cM.ga 436 cP.fL 118 cq.fN (ej uW.cx.bw 63 ze ak af 17 dP.ft 137 dP.f4 (e8 n4.pk.cf 265 yK au X ad 96 c6.eZ)) (fO jS.bH.bg.S 71 c8.fi 209 c8.eZ H 362 cN.p9 (ac oM.bi.hL.dx 156 dq.gj))))) (d3 H.ja (bU o3 (nd (l5 nF.bQ 101 z8.eW 17 z8.eH 67 an oY.aC) (nd (qK oK.S 66 hJ 109 sg 105 ct.gg) (co t7.ec) (kf gU.cR.bg aP 112 d1.fU e_ 214 d1.fz e_ 210 d1.gl e_)) (kh rl.bV.aF 51 cA.eB cA.eu 1 dj.fz (iR qf.ag 51 mF kn 1 cO.fq 2 cO.gb))) (dR dZ.iI (fh lW e_ 62 ch bd 93 bv ah 89 bv aU (hZ lW.ag 74 ch ah.aC 74 ch aU.aC 1 cN.ex bd 2 dT.gH e_)) (en oI.eh (cp nr.eN 50 dq.gK dq.fp 19 dq.ft)))) (gA m8.cQ 43 iB aA aB dD 80 je aw (eJ h9.hK.gY (md pR.aj.bP.bg 57 cV.p0 180 iB dk.o5.kB 299 c9.p7 (cp cZ.jr.aO.bi.S 79 dr.fq zx 129 w2)) (J kW.xQ.r4.eF 189 c0.eA (cp zB.fH 55 cU.fP cU.gK 1 cU.fp))) (az kK.S 120 et 57 hC 53 iK (mR ru.aD.cR.ja 4 di.f6 137 dj.eZ H 133 dj.fi (dc lV.i2)) (ns tZ.aD.aF.aS 4 c7.eu 249 dI.fL 80 dI.ex (n3 au.bV.aS)))))) (nd (qa eE BA 24 65) (aR jv.bl (nd (rP b1.jq.nR.S iC xY 32 (t9 cD A7 bq) 145 (aM cF vR bt) b1) (nv gU.dJ.dv 100 se dz 123 z4.gb bj 119 br (aJ oL.cx.b8 57 mM 1 cy.p4 2 cy.p3 (g4 oV.a0.aC.S 63 dr.gO 113 dr.ev 29 dr.eZ) (al bq)) (ek pH 71 ey iE 1 da.gb 2 da.gd (aG gq.bm.fr.gB))) (nd (zg ul.aF 229 c5.p8 42 wV 1 c5.f9 2 c5.ga) (aZ (jo qc.aj 23 c9.fL 287 dP.eB 271 dP.fT 107 cV.fM j) (al oI.kv.aX)) (fS uy.e0.aF.aS 4 cI.eB 69 u7 dZ 65 eM (iL i1.cz.ae 52 yo K L 130 cU.p9 126 cU.p8)))) (bS dk.bu (eR rz.ag.b6 e_ 104 an b1.ce.aS 1 z9.p7 e_ 2 z9.f9 bd (J dN.hL.bV.fd 159 cV.gg (ff lU.g0 137 dr.gL 472 dl.hH 19 dr.p9)) (aZ (jo nm.cz.S 272 c0.fq 112 c7.gg 73 yO 69 wC j) (eo mU.jr.bV.a0 63 cL.e1 111 si uI 14 cL.gk))) (eg pb.aO.ag.b8 100 uz jN 1 cq.fT 2 cq.fA (J jH.cx.gE.bz 509 c0.fz (em qg.aX.cz.ae 76 dl.er dl.eB 205 dL.fP 104 dl.fT)) (jz jN.bg.vr (bk mY.gY))))) (op bK (lC cD A4 e_ (eg l9.eN 105 c4 e_.mu 17 z9.gK 25 z9.fp (im ao.mX (ml g5.aI.cH) (dd k8.b6 aB 287 d1.gn)) (aW aY.bm.bw (g1 mU.cd.aj 23 dM.gl 81 cL.eH 55 cO.gd aw))) (nd (pO tV.fj.iF 4 cM.fz 493 je cg.cH 17 cM.p3) (J e_.bV.cH.hU.gT 140 dj.gb (aK K.AV.vv.cJ.fr)) (fO fa.aj.aF.b6.S 123 v2 71 cI.fM H 67 c8.eS (bZ rj.iF.aj 134 hB tS rr ad.bi 79 jc lS)))) (eR hR.aS.S bd 51 z5.gk bd 97 z6.p8 e_ 29 z6.p7 e_ (bS kP.aF (aZ (pj tK.bw 113 dy.fT 174 ch bO 17 dy.fA 94 hD aH) (eo i4.b6.aj.cQ.S.S 84 dr.eA 138 dr.fM H 528 dl.gL)) (jW m1.aC 11 c7.f5 105 bN dV.vz.jd 72 ca fY.FZ.bH (ac aE.cH.eD.aI 226 cU.eW))) (N aE.e0.aI.k7.fy 68 cP.p8 (aW ty.bw (lf (oO j8.cz.b8.cd.iF 4 dL.e7 130 dL.f6 17 dL.er))) (fO sD.dB.a0 73 cN.eA 115 AH aE 14 dI.fm (fb cD vk bd)))))))
def DH : ab dp:=(az fc.a0.ae 45 Hp 129 HO 126 Hy (nd (rP eE iC tt 24 (aM cD dE e_) 65 (aM cF dE e_) bd) (aR bq.bP (bS ed.eP (nd (rL nt.bP.aX 94 kw dz.fF 29 z7.gd 114 qy.bI) (qd jx.pk.aS 11 cy.gb 190 xh 243 cP.eu aw (eo oq.bg.bp 125 c7.ex 82 c7.ez H 243 dr.ez) (fW ah)) (dG aV.hL.cH (bC rK.e0.cQ 98 ey h5.cY d4.cY 192 ap nB.av 188 nG.av))) (gp oV.a0.aj 171 c5.fp ak af 59 c5.eS 55 c5.fm (kN ii.nR.S 106 hJ e3 ed d0 113 c9.eY (al ar.fr.aX)) (bD jg.bp.aj 134 pz bF bE 79 pp jt 75 gX (g1 iu.aD 47 cT.e7 101 cT.hH 55 cU.ez aw)))) (nd (zj cF A7 cl) (o1 uf.S 65 an i6.aC 111 c4 cj 107 dS (J iE.AQ.hK.dh 213 cV.gl (aK d8.io)) (aZ (nI g9.cz.aS 11 c0.fN 35 c0.ex 140 lA K 136 L) (nz iy.gZ 53 cL.fP cL.gK 90 rW X 86 ad))) (dR hW.bg (J jy.aX.pF.bo 674 ds.f8 (dc rr.gP)) (j4 ty.aI.bu (iL s6.bi.ae 72 zM K L 60 cT.p9 56 cT.p8))))) (aJ fk.ec.aX 40 z2.gl 29 z2.e1 60 z2.gk (qR jN (aJ pf.b8.b8 79 z8.ga 1 z8.gj 2 z8.f5 (dR lS.a0 (ac bd.aF.bl.dt 342 dr.fA) (dd lD.S aA 71 dY.gg)) (du ou.aD 62 xb g5 gq k6 101 bv kc (lc ul.S 233 dM.p9 46 cO.p4 105 hB 101 cO.p2))) (nd (pd um.bV 24 cG.p9 78 cG.fq H 26 cG.p8 94 cM.eB) (fS n4.cR.ja 4 dj.fA 184 lm bK 180 ea (bC sR.S.bV.aj 102 hD lk.pF kS.pF 242 ch b1.aX.bV 238 bd.ni.bV)) (o7 rm.iI.ho 209 cN.fp cN.ft 130 c8.er 126 cI.ex j (aT uq.eP.b8 55 cT.fq 1 cT.gb 2 cT.gd)))) (d3 aE.jq (cu il.cz.bm.aF 53 AC ah bK ea 1 dn.gd (fh AI.eK.iI.S bd 180 xh e_ 251 cB.ez H 370 dX d0.fr (dc jn.y9.vr)) (ns Ci.iF.aF.aS 4 cN.fK 409 cN.fm 165 cN.eS (ly jX))) (gp rk.pk.ae.cQ 64 cy.gd K L 161 cP.fN 157 cP.ex (aZ (w9 o8.aj.a0 147 di.gg 126 di.eY 86 rU aE 14 di.eS) (hZ kL.aO.cQ.aC 11 dL.gO e_ 178 ap j.yd.hM.fF 232 ap b1.aS.fj.bI 49 dl.gj e_)) (gV yx.gR.ae.aj 70 cN.eY 235 cN.fq 167 cN.eS (aK dN.CJ.xD.S)))))) (c3 K.hU.bI (eL d4 (ku j.bm (nd (qS dF.iI.aj.ae 72 pv K L 103 nX 99) (N nq.hM.gT 82 ct.eB (e5 fk.dJ.bi.cd.dv 76 c7.p7 114 v2 ar 110 ao) (lf (rP l4 iC xY 32 (aM cD fB e_) 145 (aM cF fB e_) b1))) (J jn.bl.eC.db 82 cA.e7 (mg tC.dJ.aS 11 dL.p0 199 ap h9.ni.eK.av 137 ey H.cQ.cv 133 j.aX.cv))) (mi ul.aF 42 po e_ 42 cG.fP e_ 42 po aP 1 c5.f9 bd (gW sY.eb.ae.eV.aD 180 iB oa.o5.kB om.o5.kB 307 dP.f5 186 cV.p1 j (kf iy.ec.aj.S.ae bd 65 dT.fz e_ 65 dT.gl e_ 121 cN.eu bO)) (kN tZ.aI.S 149 l0 H ah aU 72 vZ (dc lV)))) (qu j.bg (nv l9.dv 121 c4 dz.aO 101 an bj.ae.ce 97 br.ae.ce (J nJ.aI.db 71 cV.gj (co oA.aF.ec)) (ck H.cR.ce (cp ud.fH 51 cL.p9 cL.p8 1 cL.p7))) (dQ i5.aC 11 cq.gd 139 cP.hH 202 cP.gL 119 cq.fM (md ii.eP.aD 70 dP.p9 237 iK ci.pk 65 dP.p8 (bM pZ.g0 112 bv aA.bQ.aO aB.bQ.aO dD.bQ.aO 19 dl.gg)) (bT nB.AO.kv.hM.bu.bu 61 iz rD.fr.iH (n3 H.n1.aS))))) (bc aV (bc mW.aI (eg qU.ag 108 c4 iE 1 z9.fi 2 z9.eW (N fY.Cn.aI.db 74 cB.p7 (mg l3.ag.aS 11 dr.gj 83 ca aH.wd.bl 94 bN dZ.d6 90 eM.d6) (lb aE.S)) (du tq.aS.aj 62 ep g5.ja gq.ja k6.ja 139 iq lP.bI (lf (Ck j)))) (nd (At sB rT 24 65) (ck mq.h8 (bC s9.cs 146 et qG.bP oG.bP 101 iK jt.cJ 97 gX.cJ)) (J jN.bg.jd.eD.kk 221 c8.fx (ff n5.bQ.aj 35 dq.fT 43 dq.fA 60 dq.eu)))) (ol gF.aX.aC 11 z7.fE 87 kA dV.gP 53 mc aw.fF (eg g3.ag.b8 74 fG jN.aD 1 c5.fu 2 c5.gO (du eI.ja.cR.a0 59 cq.fC au X ad 115 nY bt (lf (oD uT.cf 71 c0.eZ 180 b7 g2.ae 176 kg.ae))) (bA oq.bm.b6 143 cS.ex 1 cS.fL 2 cS.gg (ly jV))) (qv ox.cz.aS 4 cy.er 152 ct.gj 74 ct.ga (fO pR.eV.ja.a0 87 dj.p0 188 zm aE 14 di.p0 (bZ kL.fH.bg 106 yS au X ad 182 ap i6.d6)) (bA iu.dB.ag 135 dT.fo 1 dT.fU 2 dT.fi (la gs.ag 42 d9.f4 d9.fE d9.fD 1 d9.fu)))))))
def Dy : ab dp:=(c3 b1.AO (hS tv.aC 4 HY 307 Hv 29 Hz (aR aU.bP (aR iE (bc jN.bu (nd (wA qh.jq 11 cy.fi 149 lo au 72 cP.fP) (i7 tp.aF.bw 82 bN rG.cH pX.cH 17 dI.gv 75 ca lV.bI) (lf (wP bK))) (ix h5.pl.bm (bZ tC.a0 183 ap H.bu.av uU.av aU.bu.av 121 ey bt.cY))) (bU aV.fy (bA pU.dJ.aX.aF.b8 176 dy.fx 1 dy.gn 2 dy.eA (g4 qx.gR.ae 28 ds.fq 482 dl.eH 478 dl.f8)) (fV rm.aD.bQ 62 rY 17 cS.gd 339 cI.gk (co jV)))) (bc iS (nd (q1 qJ.cz.aj 23 z9.er 130 c4 uG 114 H.bP 110 uc) (ir oL.iF.cQ 43 cB.p3 44 cB.p2 29 cB.p1 26 cP.fM (h6 t0.bV.a0 97 bN gS.g8 100 ca gf.cY 14 ds.fU)) (ir jA.dK.gR.aC 11 cS.f6 167 cS.gm 38 cS.fP 29 cS.gK (fW jk))) (lY tA.bu.aD 57 cM.gb 154 rb aE 65 cM.gd (aW aw.nS.nS (ff oN.dJ.g6 91 c6.eZ 190 c6.hH 1 c6.fo)) (en rI.eh (aG au.bu.iG))))) (bc pQ (bU aw.eN (fR iT.bl.aS 11 z8.fK 65 z8.fN 60 z8.ex (N ki.Fy.ib.bo 582 da.ft (iL gG.aj.cR.fg 181 dI.fD K L 76 dI.ft 72 dI.f4) (al cg)) (ck e3.gP.ni (bC tC.cz.ae 191 ap K.iG.ce.bi L.iG.ce.bi 109 ey q6.cv 105 nK.cv))) (nd (wA rj.ja 11 cG.fU 105 cG.e7 aE 49 cG.fP) (ej uP.eV.ae 60 zZ K L 41 cB.fU 96 cB.fi (lf (rP eE sc vo 24 (aM cD dE e_) 65 (aM cF dE e_) bd))) (de cl.o5.bp (iM b1.bu)))) (hi tq 38 ep dX 1 z6.fp (qq cZ.dJ.bg 36 dn.fu 84 dn.gO 38 dn.ev 147 dn.fT (jW tk.b6.aj 23 cV.p9 105 cy.ev aE 79 w5 bq (iL i1.dK.ae.aj 64 wg ak af 88 ds.gl 84 ds.e1)) (jW n0.aS 11 c0.gk 188 b7 ci.nh.ae 69 cA.f6 aw (ly g7))) (nd (wJ sJ.aS 11 cq.gj 106 cM.eu aH 613 c9.fp 60 cM.ez) (nc tE.b6.bw 76 dP.p2 292 cN.p1 19 dP.p1 (aK aH.cJ.kY.ib.fr)) (de bt.cJ.kY.ib.fr (i7 ul.fj.ag.bw 80 jc pS rI 17 dY.eH 151 hB lV.aI)))))) (aR aP.eK (mi sC.a0 59 z1.fx e_ 59 z1.gn e_ 59 z1.eA e_ 259 iJ uD (bS l6.bm (bc dV.bl (N ub.rF.bm.bz 64 cy.eA (ff sQ.S.b2.ag 114 c0.gd 274 dr.fL 1 c0.fM) (fW gx)) (dG b4.bm.cH (e8 oN.eb.bu.cf 89 Ax au X ad 145 dL.eY))) (bU eQ.aO (mR m9.cQ.ia 4 c9.ez 493 mJ tX 126 dP.f8 (bZ rd.ho 71 py g5 gq k6 188 b7 lP.aC.ae)) (o7 oq.bm.aD 121 cI.fp cI.ft 70 tj 66 cS.eY j (ac kJ.mu.eV.dK.fy 67 cT.fD)))) (cb gs.jr.bV 131 z5.fM z5.fx z5.gn 161 z5.eA (nd (pN sE.aj 66 an oC.i2 ty.i2 L.sk.i2 106 kc.b0) (J lR.gE.bz 552 wg (ac u3.kY.eF 925 dl.ga)) (dG o6.bm.cH (nz fc.gZ 53 cL.gO cL.ev 90 b7 X 86 ad))) (N e4.bP.hV 64 cq.eW (gW ii.ag.bw 109 sg bj br 17 dP.fN 78 hJ aH (d2 dz.aI.pl.bm)) (ck jk.fQ (hZ rj.iF.a0 75 jc fX 75 jc d8 156 hB tL 14 cT.fN aP))))) (eL aV (cb h3.pk.S 112 z4.gb z4.gd z4.fM 93 z4.fx (nd (pI m2.it 117 zR au X ad 102 z8.gg) (aJ ma.bP 32 cB.e1 1 cB.gk 2 cB.er (lf (lB g9.cz.b6 136 lA jN 1 c0.p8 2 c0.p7)) (dd h7.b6 aA 9 cO.fE)) (gV o8.aj.ag 135 cA.gm 134 cA.fC 1 cA.gv (co kn))) (fR h7.aI.a0 55 cG.gv 63 cG.fz 90 v8 (ck aV.h8 (bC qP.cz.ae 183 b7 ak.hM.cK af.hM.cK 86 pt h5 82 d4)) (oc rm.iI.ag.aS 11 c8.fA 130 y0 j 82 vh K 78 L (al bt.aI)))) (N lG.bP.dh 56 z6.fq (eJ H.xF.gY (J K.xx.mX.aF.sk.aI 136 dj.f8 (al ao.iH.bQ)) (aZ (jB q7.iF 11 c0.fC 181 b7 bO.ja.ae 104 pt K 17 c0.gv) (co jX))) (N cl.eC.db 481 cB.gj (eG jp.eb.bm.aF 63 sj fI ra s7 1 di.gb (ij qX.dv 120 bv iQ.aO 93 ch qG.aC 89 oG.aC)) (J fY.aX.bl.eD.kk 239 cN.gb (g4 mj 38 dY.fC 115 dY.gv 14 dY.fq)))))))
def Dv : ab dp:=(eL aH (m6 H.S (nd (yF ux.dm 102 z1.gg 254 iJ aE.iF z1.eY 1 z1.eS) (mi sU.b2.a0 130 z3.ez e_ 130 z3.fK e_ 130 z3.fN e_ 75 dX uD (gA kb.dJ.bi.aD 72 kA e4.gP fI.gP iD.gP 60 mc hO.cH (nd (l5 tk.b6.aX 75 cP.fi 29 cy.gH 95 xj j) (d2 aA.aF.pl.bm) (aT jA.dJ 11 d9.gl 1 d9.e1 2 d9.gk)) (J e_.kB.eK.dt 334 c0.ez (iR j8.cx.bp.ag 184 ap b1.aC.iH.v9 1 dL.gm 2 dL.fC))) (cu gs.iI.eP.aF 80 fG H.rF.bw ah.rF.bw aU.rF.bw 1 c5.ex (aW cl.nS (iR rd.ag.b8 184 b7 kx.aC.ae 1 ds.eY 2 ds.eS)) (J pQ.cJ.bi.hL.dx 156 cS.fT (g1 lO.bH.bi.aD 81 cU.fM 482 dq.fo 56 cU.eH aw)))) (eL oG (eR g3.aX.dB e_ 100 an qp.aS 68 an iS.gP 64 an tT.gP (J aU.gP.o5.eD.aI 284 c9.fP (dc b3.cQ.mv)) (gW ng.cR.b8.bw 70 pp jw jD 17 cS.fK 141 pz bO (aT ux.dm 11 dM.gm 1 dM.fC 2 dM.gv))) (fR nA.bP.bw 89 cM.p4 171 cq.gb 19 cM.p3 (bT gS.kv.pT.hK.dh 305 ky gS (aT pZ.ik 11 c6.p4 1 c6.p3 2 c6.p2)) (bD u9.b2.aj.ae.aj.cs 114 di.gl bF bE 77 u7 jt 73 gX (ac ob.bi.hL.dx 156 dq.gL))))) (cb j7.eN 33 z2.fA z2.eu z2.ez 19 z2.fK (ku H.bm (eR gF.bQ.gC bd 75 z8.fN bd 82 z8.gb e_ 70 z8.gd e_ (N au.bu.dt 334 cV.p6 (em lH.jq.cR.bw 79 dr.f6 dr.fP 17 dr.gK 71 dr.fp) (lf (zo aB.cH))) (J dO.nh.cH.hU.aI.aI 74 cA.fN (g1 i4.cd.aj 23 dM.fD 73 dM.p3 47 cO.eH aw))) (nd (qK fa.cx.cf 101 nV 63 rb 59 lF) (J qm.F4.eF 258 di.ev (fJ cl.pD.eC)) (de A9.o5.bp (aG qm.vL)))) (fR eT.cQ 31 z6.eB 39 z6.fT 40 z6.fA (pP aQ.yb (oc tc.aS 11 dy.fP 73 yj j 94 fe lq 90 gN (al kx.bl.bH)) (gy ka.Gv.eC (iM hQ))) (qv fa.cx.b6.aS 4 cP.gO 101 cP.ev 97 cy.fK (aZ (pd uJ.e0.bg 48 di.fD 110 lJ H 50 di.fu 56 cA.eB) (al jy.bH.bH)) (gz gG.cK 80 po j 48 c5.p0 K 44 L (fW jU.cx.bu)))))) (cb g3.gR.iI 60 z1.fE z1.fD z1.fu 108 z1.gO (cu g3.dB 242 iJ nj g2 kg 64 z1.gL (bU oW (m6 ad.S (lY sZ.bg 58 ct.e7 221 vm au 236 mG (iR l3.eP.b8 75 ca jN.kY.bH 1 c0.p4 2 c0.p3) (aT hY.aX 48 d9.p3 29 d9.p2 68 d9.p1)) (aW eQ.iv (pL tC.eb.iF 4 dL.p6 137 ey H.bQ.cv 17 cO.fP))) (nd (yq dF.aj.S 50 po 92 cG.e7 41 cG.f6) (ek mZ.b6 64 ey pq 1 c9.gb 2 c9.gd (lf (sG sH.gR.bg 36 dT.eS 223 b7 K.xF.cK 38 dT.fm 185 i6.ja.ae))) (gV d5.eN.g6 85 cI.eY 84 cI.eS 1 cI.fm (ac mT.eF 177 cT.fL)))) (cb pf.cz.aF 84 z5.p8 z5.p7 z5.p6 1 z5.p5 (cu qw.fH 116 c4 o3 hW.bQ ld.bQ 1 z9.p4 (ir ox.gZ 418 wf 78 cV.gm 101 zE 97 cV.gv (eo rs.aF.b2.a0 202 c6.gH 119 y7 aE 14 c6.gm)) (aZ (oh i5.S.a0 72 hC bd.ia 157 et ci.aO 14 c0.fm) (bZ zY.S 108 iq jv dk e6 53 ep b4))) (N j.fr.pT.hK.dh 63 cq.ex (eG mP.ag.dm.bw 78 rN aA aB dD 19 dP.gj (kf uY.e0.fj.S e_ 183 ap l6.hL.bI 129 ve H 125 dl.gn aP)) (en iX.eh (aK ke.bp))))) (qq h3.ag 218 z2.p6 267 z2.p5 220 z2.p4 1 z2.gL (nd (kH bd.cJ) (lY pf.b8.aD 47 z9.ev 140 an au.jq.aS 87 z9.eZ (az iy.bV.b2.ae 175 lm 57 wT 53 uV (lc g9.cz.aD 467 dl.fp 132 dr.p0 75 ds.e7 26 ds.f6) (dd mj aA 21 cO.eZ)) (fV jS.cz.aD.ae 63 cA.p8 103 cA.p7 99 cA.p6 (g1 lH.eb.aj 23 dM.gk 85 cL.e1 59 cO.ga aw))) (dR af.S (ej Ad.cz.S.ae.e0.cQ 114 wv K L 69 dj.eA 65 wO (bZ pe.aj.b2.eV.bg 95 vg jv dk e6 156 vb aN)) (J oW.iv.bm.dx 164 c8.fq (bM ua.ag 53 vd ah bK ea 1 dq.e1)))) (eg gF.aX.bP 49 mc e_.fF 1 z6.p3 2 z6.p2 (nd (jB qW.ag.iF 11 c5.ft 81 fG bd.pT.bw 172 pA H 17 c5.f4) (bD jx.aj.cs 106 cy.gj bF bE 72 mL nq 68 mh (bC i5.aj.b2.aj 147 mK aY aQ 199 jK cg 195 b3)) (bD pW.aX.cz.ae 66 mM ak.hM af.hM 98 nY h5 94 d4 (ac b1.eh.dh 136 cU.eB))) (hi ko.cx.bg 47 cq.gL cq.fD 83 cq.fE (bT nn.r4.Gp.bm.bz 146 ep aH.cJ.ja (al X.jd.mu.bH)) (jz aU.bg.vr (lf (zv aV))))))))
def DC : ab dp:=(c3 L.AO (qq gU.cR.bg 116 GT 248 Hi 118 Hl 214 GM (aR kn (aJ eT.b6.dm 11 z3.eW 1 z3.eH 2 z3.f8 (N e_.ae.pF.eV.bz 63 z7.eB (dR kO.a0 (g1 ud.dK.aC.aF.aS 11 dr.fU 94 dr.eA 130 c7.fu aw) (lf (rP qt iC xY 28 (aM cD hI e_) 105 (aM cF hI e_) b1))) (aZ (l5 pe.cQ.bP.aX 69 dP.fD 29 da.fz 89 pp gx) (g1 lK.cx.bg.b2 11 dL.fz 93 wZ 181 ap bd.ia.iH.v9))) (bU bF.bu (ck aE.rF.h8 (iO yJ.kB.ib.gE.cw 244 ap yJ.xF.fF)) (ck A8.fQ (e8 kQ.dK.dB 94 si au.bQ o3 ad.bQ 68 cU.fu)))) (nd (kH lG) (aJ uh.dJ 11 z9.fA 1 z9.eu 2 z9.ez (bT j.fr.hM.bu.dK.fy 112 iB j.mX.kB (d2 af.aS.vv.bm)) (du qM.cd.eP.bg 75 ep ci.mX.n1 aV.mX.n1 cC.mX.n1 168 iq mE.bV.jd (aT h7.ik 11 dM.fA 1 dM.eu 2 dM.ez))) (qd rc.aS 11 cM.eA 71 cq.p5 99 uv aw (J aE.r4.ib.bP.eV.dK.fy 253 dP.gK (lf (l5 o2.aI.cz.bQ 19 dl.f6 17 dl.fP 180 ap bO.d6))) (en lS.eh (ac iQ.bi.hL.dx 156 dq.hH))))) (nd (rP eE sc EB 24 (aM cD dE e_) 65 (aM cF dE e_) aP) (bU dS.eN (ry tv.dv 99 z8.ft 118 z7.ev bj 114 br (e2 nD.i0.bo 204 fe X (co kP.aF.ec) (lf (kH K))) (aZ (wp lT.bl.ec) (aT yU.ag 47 cO.eS 1 cO.fm 2 cO.gH))) (dR j.iI (gV wR.aj 81 zP 205 cA.fu 58 wG (bM j8.fH.aD 92 hD aA.ib aB.ib dD.ib 155 dT.gg)) (jz kP.Gw (hZ ua.a0 53 cT.ga e_ 53 cT.gj e_ 95 sb aE 14 cT.f5 e_)))) (N FO.cx.bz 40 z6.fU (az Bw.b2.ae 91 dn.eB 50 dn.gk 46 dn.er (eG sJ.bw 98 nV au X ad 19 cV.p3 (fJ pQ.vr.aI)) (ek q7.b6 177 b7 xI.aC.ae 1 c0.fA 2 c0.eu (co g7))) (nd (rP fk iC AU 20 (aM cD kD e_) 25 (aM cF kD e_) bd) (aZ (wA wI.b2 11 di.e7 106 bv gf 61 dj.gO) (al rI.kv.aX)) (ck jT.fQ (fW dO.eV.bu)))))) (lC cF F6 b1 (aR iD.bl (dQ dF.ec.aj 23 z3.fx 66 z3.gn 50 z3.eA 46 z3.f9 (nd (tJ dF.fy.b8.bw 95 kw rD.bI rM.bI 17 z7.p0 182 z7.fC) (gI un.aF.aS 4 cy.p6 64 mL lq 60 gN (em d5.b2.ae.cQ 197 ds.eu ds.ez 74 ds.fK 70 ds.fN) (fb cF fB b1)) (ck ka.aF.aC (kf pH.jr.ag e_ 131 ey Df.cv 1 dL.p3 bd 2 dL.hH e_))) (az uq.bl 23 c5.fx 1 c5.gn 2 c5.eA (aZ (qj mP.ag.fg 82 cV.gm 105 cV.gv K 101 L) (bZ qn.dB 83 ca th.cY j5.cY lG.cY 102 bN pc.g8)) (k3 uW.cx.aD 175 cI.fU e_ 175 wU e_ 339 c8.eH aE 67 rY j (al kO)))) (az g3.eb.cQ 82 z5.hH 133 z5.gL 129 z5.p9 (cu nE.g0 111 c4 aA.bQ aB.bQ dD.bQ 19 z9.hH (aZ (lz ju.cY) (ij l3.cz.ae 86 bN pX.cH 83 ca K.AZ.bI 79 L.AZ.bI)) (du BS.aD 165 ap jn.bi o6.bi j.ni.bi 75 ey kc (cp gr.g0 54 cL.fC cL.gv 19 cL.fq))) (ry j7.bQ.cz.ae 121 cM.gH 73 cM.fC K 69 L (jW mZ.aS 11 dP.fx 180 ap iN.bi 68 ey gS (aG mh.eK.ce)) (de ed.gY.gD (mg rj.eb.ae.aC 11 dq.p6 150 hB hj.gP.v9 69 mH H.kv.hM 65 j.fr.hM))))) (cb j0.ag 36 z2.fM z2.fx z2.gn 1 z2.eA (nd (kH aV) (cu uf.ec 103 c4 b1.fy H.ec j.fy 1 z8.p0 (e2 kP.FI.bu.dK.fy 131 je aH.iG (ac uN.bV.fd 159 dr.ex) (o9 aE.S)) (bD jp.eb.bg.aj 83 nY aY aQ 71 mM eQ 67 dz (fW kn))) (dR K.bg (e9 li.eb.ag.bw 113 dj.gm dj.fC 17 dj.gv 77 dj.fq (al b1.dm.mu.bH)) (ck rJ.fQ (lg uq.eP.aD 55 dq.f8 131 jc e_.bP 59 cT.fq aw)))) (lE iP.eN.aj 35 z6.f5 43 z6.hH 50 rX hO (nd (lL cZ.aS.gR.bg 36 dn.gL 96 dn.fq H 38 dn.p9 58 AC aN) (aZ (qS BR.cx.ae 56 ws K L 95 xd 91) (ac lR.aI.eC.bu.bz 393 c6.e7)) (du lK.aO.S 89 rU dO cj dS 229 ca bd.e0.bH (iM kp))) (nd (pj jg.cd.aD 139 ct.ft 200 pm gx 227 ct.f4 126 cq.fM j) (bT oA.yd.hM.bu.dK.fy 112 iB oA.Eb.kB (hZ uC.cx.iI.aC 11 dl.p5 e_ 344 ap j.Eb.mv.bI 312 ap b1.FZ.xx.fF 75 dl.p4 e_)) (du nb.dB 71 Ar au X ad 126 fe lR (co ah)))))))
def DJ : ab dp:=(hS jm.hL.ae 119 HQ 47 Gu 43 Hp (nd (qa eE Bo 24 65) (e2 h9.bm.bu.bu.dh 151 iJ j.aC (ry qM.dm.aX 132 z3.e1 59 dX bF 55 bE (gp iA.eP.S.ae 97 nX K L 74 z7.fC 70 pv (e2 b1.cQ.rF.bm.bz 122 dX xI.fr (ff oq.bg.ae.aj 125 dI.fN 347 dr.p4 82 dI.ex) (cp gr.ag 42 rO si 1 d9.gg)) (J bt.e0.bV.fd 159 dP.fq (ql rK.eK.aS 11 dL.gj 35 dL.f5 192 ap lq.eK.av 188 gN.eK.av))) (bU aQ.aO (J ci.hL.bV.fd 159 c9.e1 (dc ak.pT.sx)) (J k0.cJ.bi.hL.dx 156 cI.fP (lf (oO hY.aS 4 cU.gb 52 cU.gd 48 cT.fp))))) (N k0.Ao.bz 67 z5.fN (eR uA.a0 bd 94 an aw.jq.aS 98 an q8.gP 14 z9.fC e_ (aW aE.cR.nS (aK oI.io)) (J mq.GE.bi.k7.fy 327 c7.eA (eo ko.bV.a0 55 cL.e7 103 vj q4 14 cL.f6))) (dR ad.S (dG cg.cR.cH (aT qg.eP.cR.b8 126 c6.p8 1 c6.p7 2 c6.p6)) (en jH.cv.bH (bk lP.gY))))) (c3 fI (cb gU.dJ.ag 88 z4.fL z4.gg z4.eY 1 z4.eS (cu gs.aI.S 80 an dO.mv cj.mv dS.mv 60 u0 (lY pe.aj.aF 120 cB.fu 358 iB hW.bH.kB 1 cP.fu (lg q7.aS 11 ds.fz 86 py gf 181 b7 aN.aC.ae) (ac gq.gT 92 d1.ez)) (aZ (nI kZ.eN.cR.aS 11 cA.gg 64 cA.eY 118 lJ K 114 L) (h6 iA.gC 103 rW aw 52 cO.fA H 48 cO.p5))) (mi j7.bQ.a0 46 cM.er b1 165 cG.gd aE 48 cG.f9 e_ 93 w0 bd (aZ (qN yr.b2 4 dy.fo 95 bv bK 91 ea) (bC oX.ho 106 bv rA.cJ qm.cJ 87 ch eQ.aC 83 dz.aC)) (bT H.bu.AO.kv.hM.bu.bu 61 iz th.kv.iH (lf (w9 tF.bl.aj 23 cT.p5 78 cT.p4 62 cT.eY H 58 cT.p3))))) (mi eT.bl 36 rX e_ 36 z6.ez e_ 36 rX aP 1 z6.f8 bd (eJ ao.hK.gY (bD tE.aX.aj 58 vm bF bE 108 mf cg 104 b3 (al d0.bl.bH)) (gy bK.iG.eC (ms kp))) (eR kV.ec.b2.aF.aS bd 4 cq.f9 bd 167 cP.fA e_ 163 v7 aP (ek qg.bi.b8 186 lm iE 1 di.fN 2 di.ex (iO h5.mu.hU.gE.cw 232 ap h5.xx.fF)) (gy H.gP.aI (aK ao.CJ.xD.S)))))) (d3 Di.cH (d3 bd.aS (ku q4 (c3 uk.aF (lY pe.cx.bg 53 ct.gl 296 vl X 409 c9.gK (aG jX.fQ) (la jS.S 178 d9.p0 d1.e7 d1.f6 51 d1.fP)) (J aV.cd.aI.db 126 da.p2 (hT s8.aj.aj.b2.ae 102 ey d4.cY 196 ap H.gP.aI.av 192 j.sx.aI.av))) (nd (Aj H.yb) (bD kK.cs 65 hC bF bE 136 et jt 132 gX (aK iX.io)) (eG hR.S.bV.e0.aF 75 ep fI.pD.n1 ra.pD.n1 s7.pD.n1 1 cI.f9 (al rI)))) (qu b1.bg (gA nF.dB 75 an H.d6.aC jy.i9 rt.i9 121 c4 b4.bQ (bT H.bV.rF.bm.bz 114 dX ah.bg (cp rl.eP.bg 63 dr.ft c0.eB 143 c0.er)) (ir oP.bl.cd.ia 11 cN.p5 23 cN.p4 138 cN.ex 126 cN.p3 (aK g7))) (N au.bg.fd 73 cq.fq (bD tc.aD 86 wu aY aQ 73 xg ak 69 af (bC rq.gZ 115 bv ke.aO iX.aO 84 ch ed.nh 80 d0.nh)) (J aA.ib.hU.bP.eV.dK.fy 104 cN.p8 (aT tD.b8 66 dY.fp 1 dY.ft 2 dY.f4))))) (nd (rP eE iC tt 24 (aM cD dE e_) 65 (aM cF dE e_) bd) (bc ob (o1 qJ.S.S 110 r5 aN 76 an aV.h8 72 cC.h8 (lQ pW.aX.S 78 nY 62 mM H 123 dy.ex (hT ti.cx.bi.bQ.S 95 bN bq.vz.jd 80 ca mT.bH 76 rB.bH) (dd gr.a0 aA 21 cO.fi)) (bD mQ.cs 73 ca lk.bl kS.bl 92 bN m4.bI 88 sP (ac gX.bu.cw 137 dM.p8))) (hi rn.bl 89 cM.eB cM.fK 1 cG.fK (aZ (zS tp.bP.aX 82 bN K.hU.fF L.hU.fF 29 dj.p8 102 qy.bI) (lf (ov oX.ag.aj 23 c6.er 140 bv ci.bo 114 aw.aO.aO))) (J dk.iv.bm.dx 164 c8.gd (bk tI.gY)))) (aJ kj.q5.ag 90 z7.gK 1 z7.fp 2 z7.ft (gI iT.eb.ia 4 dn.f9 73 fG H.eN 69 j.bw (du oL.iF.aj 240 yl H ah aU 75 r6 bq (dc ty.fr.vr)) (du ok.aS.ae.aj 124 Ai aA aB dD 69 pp bq (e8 mP.dB 86 vj H.bm jy rt 60 cL.p6))) (N ea.i0.bo 70 cy.e1 (fS eT.cd.gR.aS 4 di.p2 141 iq qQ.bI 137 tG.bI (iO kJ.mu.hU.gE.cw 232 ap kJ.xx.fF)) (mR tK.cd.aS 4 dT.ev 234 ch ak.bV 153 dT.gg (ji bq)))))))
def DE : ab dp:=(nd (kH K) (bc ed (aR th.bP (aR nD (eg kb.dJ.bi.b8 56 mc jH.cH 1 z7.f8 2 z7.fz (N fY.fy.dt 334 cB.fD (kf iu.dB.a0 e_ 134 cN.p1 e_ 119 hD ci.aO 14 cN.p2 aP) (ji ow)) (ix lV.pl.bm (eo pg.a0.bP.S.a0 140 dL.fu 106 Ax aE 14 dL.fi))) (bS dO.bl (J e3.F1.sx.cJ.aO.aO 422 di.p9 (lf (jo eI.b8.jr.it 181 c6.fu 89 c6.f6 262 yK 258 c7.eA j))) (aZ (jo i1.jq.dB 75 cS.f9 76 cS.ga 68 Aa 64 da.ft j) (fW jV)))) (nd (kH aY) (nd (qa eE sv 24 65) (du oZ.cs 209 ct.p3 H ah aU 66 pm bq (d2 nq.vv.bm)) (ck e3.ec.aC (iM jk))) (ol y4.dJ.aS 11 cM.fx 72 cM.fm aE 97 sF aw (bA q9.bw.bP.dm 11 dj.p3 1 dj.p2 2 dj.p1 (iR tO.bQ.ag.b8 160 l0 iE 1 c6.fi 2 c6.eW)) (de bE.bH.bp (aG ah.gY.iG))))) (dR nn (bU dD.bQ (bc jT (aJ jx.cf 60 pm 211 ug 207 ct.p3 (e5 te.cz.ae 178 c0.e7 85 c0.fP K 81 L) (ac H.iI.cx.bz 119 d1.fD)) (gy eM.iG.eC (aT fa.eb.ag 47 cO.er 1 cO.eB 2 cO.fT))) (aJ h7.aI.cQ 85 cG.gl 51 cG.e1 295 cM.eW (aW kr.nS (lg ts.cJ.b8.aS 11 c6.fE 90 yk b1.pD 157 l0 gS)) (kh uR.aC.S 65 yk vZ 146 l0 (bk e_.cz.gY)))) (nd (qz j) (pP aH.yb (gW wQ.ag.bw 127 et jw jD 17 cV.p4 72 hC bO (aK uu.gP.ib.fr)) (eG ut.dJ.b6 167 b7 hW.ae aE.jq.ae aP.ia.ae 1 c0.fU (bk g7))) (N aN.yb.hU.bo 174 cy.fp (J ed.r4.eF 172 cA.f4 (al au.bm.bH.bH)) (bA s6.bg.ag.dm 11 cN.fM 1 cN.fx 2 cN.gn (hZ tW.b2.eP.cz.aD 113 dY.fz e_ 113 dY.gl e_ 99 zH aE 26 dY.e1 e_)))))) (eL b1.CJ.aF (aR jT (ei iy.ec.eN 41 z3.fq z3.gb 17 z3.gd 25 z3.fM (N aE.r4.ae.pF.cw 78 z7.p5 (N b1.EQ.eC.db 487 dy.e1 (aG tr.sx.ni) (aT li.dJ 11 d9.gv 1 d9.fq 2 d9.gb)) (aZ (oh ii.bV.a0 121 fe aN 88 Ar aE 14 da.gv) (lf (lZ j8.cx.bp.aj 78 dL.fM dL.fx 188 ap bt.aC.iH.v9)))) (eJ aE.vv.cJ.fr (aZ (lz ah.cY) (ac L.o5.av.k7.fy 269 dT.p9)) (J vK.cJ.bi.hL.dx 156 cI.fz (al oI)))) (bS gX.bu (cu uA.ag 94 an X.ia.aS hW.ia.aS ld.ia.aS 1 z9.ga (aZ (lz lV.cY) (e5 re.dv 75 dI.eY 99 we ar 95 ao)) (bT ad.iH.aI.hV 124 hC dS (h6 sC.a0 59 mF jT 107 dX uI 14 cL.fU))) (N bO.iH.ib.bo 61 cq.f8 (ck pc.aC (d2 g5.aI.pl.bm)) (nc kV.a0.aj.cR.aX.aC 11 cN.eW 135 c7.ex 74 cN.eH (pL gG.aj.cR.ja 4 dq.p7 64 dq.gm H 60 dq.fq))))) (az j7.dJ 11 z2.gv 1 z2.f8 2 z2.fz (bc ci.eV (eg l9.b8 71 an pw.h8 1 z8.p4 2 z8.p3 (im oI.nS (iL rd.nR.aD 176 b7 bF.ja.ae bE.ja.ae 63 ds.ex 26 ds.fL) (dd dF.b6 aA 9 cO.fD)) (fh oJ.aS.S e_ 74 ca mq.bH 115 bN ak.nh.jd 29 cA.gn e_ (lf (wx rH.a0 48 dX 125 iq dV 14 dM.fP)))) (N u3.hU.bo 548 cP.gl (ej jp.eb.bu.aD 59 sj bF bE 63 dj.eY 26 dj.eS (kf ou.cd.bQ e_ 78 ch aU.aC 17 dT.eu e_ 113 bv bd.pT.cJ)) (en tx.bl.bH (bk b1.wj.gY)))) (mi o0.gR.iI 103 z6.gL e_ 46 z4.er b1 46 z6.eS e_ 94 nW k9 (N q6.iH.ib.bz 63 dn.f5 (J j.sx.aI.db 116 dy.er (al e_.e0.fr.aX)) (oc m1.aS 11 cN.e1 91 bN hj.sk.bI 76 ca kO.bl 72 tx.bl (fW jX))) (N aE.HL.eC.db 487 cB.p6 (m5 nG.bu (dc jl.i2)) (de h9.cJ.kY.ib.fr (fb cD hI e_)))))))
def Dx : ab dp:=(qq gF.bV 24 F3 78 Fq 26 FU 41 FJ (hS gs.b6.cQ 27 GX 54 GY 50 Gc (aR k6.bP (cb sU.b2.ag 130 z3.ex z3.fL z3.gg 1 z3.eY (lE h3.pk.aj 23 z7.eY 119 z7.eS 93 z7.e1 aw (gA sX.aj 61 lF aA aB dD 107 nV bq (lf (qo uy.e0.ae.b2.ae 122 wy L 77 v3 K 73)) (fb cF mD b1)) (ej n7.iI.aj 211 hC bj.ae br.ae 279 da.fm 275 da.gH (iR iu.aS.g6.aX 185 ap gX.d6 113 dL.fq 109 dL.gb))) (bS ue.aF (J aw.ia.hM.gT 82 c9.fu (fJ k0.vr.aI)) (e9 tl.b8.bw 175 cS.p1 cS.p0 17 cI.e7 82 cI.f6 (bM iA.eP.bg 52 iB aE.kB K.kB L.kB 227 cT.ft)))) (aJ m8.jq.S 88 z5.eB 85 z5.fT 29 z5.fA (mV nF.gR.bw 113 c4 sV tN 17 z9.gm 97 an nn.i9 (J rG.hM.gT 82 cV.f8 (d2 kS.bl.pl.bm)) (gV g9.ae.aj 73 c7.fo 157 dI.e1 136 c7.fU (nz il.gZ 49 dM.p5 dM.p4 50 rQ X 46 ad))) (aJ rn.cQ 55 xn 93 xw 89 cG.er (mR oK.eb.iF 4 dP.fo 114 hJ aE.eP 17 da.e1 (aT lW.ag.dm 11 c6.p1 1 c6.p0 2 dl.e7)) (j4 H.e0.aI.bu (aG bK.bu.iG))))) (c3 bq (N fY.aO.bP.dh 59 z4.eB (nd (uM kj.cd.ae.aC 11 z8.f9 111 nX oY 80 pv dZ 76 eM) (nd (zL qh.aj 23 ct.f9 102 ct.p9 76 ct.ga) (fJ k9.mv.aI) (ac rr.bz 84 d1.eB)) (hX kZ.eN.cR.aS 11 cA.fL 74 cN.gj 118 lJ bq (ms kn))) (dR af.bg (ck ao.aF.aC (lf (rP eE sc rg 24 (aM cD dE e_) 65 (aM cF dE e_) e_))) (gW oF.b6.cd.bi.cd.b8.bw 68 u7 jw jD 17 c8.fz 121 di.gl bO (bk aY.gY)))) (d3 ad (pP ao.Dg (nc ma.aC 11 dy.ft 85 c9.p1 38 dy.f4 (aG iS.fQ)) (gy ak.pD.eC (aK jX))) (dQ uO.a0 159 cy.ex 71 cP.fi 116 lo 14 cP.eH (ek kZ.eN.cR.b6 114 lJ jN 1 di.gk 2 di.er (iO K.iG.bl.hU.gE.cw 240 ap K.iG.mv.bI)) (fh qX.ag e_ 108 bv kx.aO 1 cN.fN bd 2 cN.fT e_ (ac aY.wd.eV.eV.dK.fy 188 dY.ex)))))) (aR bd.eK (aJ nx.aS.S 135 z1.p6 145 z1.p5 29 z1.p7 (bU kc (aJ sW.cd.ag 67 z8.f8 1 z8.fz 2 z8.gl (dQ oZ.S.cQ 135 ct.fo 136 ct.fU 133 cV.fu 130 cV.gO (aG hQ.fQ) (lf (rP l4 wN Bq 32 (aM cD fB e_) 145 (aM cF fB e_) aP))) (iw oi.ag.bi.ae 90 wu aQ 77 xg k0 73 jZ (bM rK.fj.aF 188 ap iY.mu.av aE.F1.mu.av aP.iH.mu.av 1 cO.f6))) (dR H.iI (aW jt.bH (ac iQ.bP.dt 334 dl.fu)) (o7 jS.aS.ho 115 cI.gv cI.fq 214 c8.fN 75 cS.p9 j (ac d4.bi.hL.dx 156 cT.gm)))) (nl ah.AZ (cu j3.dm.bw 114 c4 g5.aO gq.aO k6.aO 19 z9.p2 (bA ma.eN 102 cV.fM 17 cV.fx 25 cV.gn (dc b4.y9.vr)) (gz tu.eP.S 141 et bq.bP 92 iK ah.cJ 88 aU.cJ (lf (rP fk iC zy 20 (aM cD kD e_) 25 (aM cF kD e_) aP)))) (az tE.aX 28 cq.gg 50 vm 46 cq.eS (aW aU.iv (ac cX.kB.ib.gE.cw 82 dl.fK)) (fV s0.ia.S 176 c8.p6 85 c0.gK 29 c0.fp (bM eI.cz.gR.ag 77 jc dk nD tP 1 dY.gO))))) (nd (rP qt iC Bq 28 (aM cD hI e_) 105 (aM cF hI e_) bd) (nd (kH ah) (ol nE.aS 11 z9.fo 75 an H.i9 103 c4 bq (qv oP.bl.aS 4 cB.eY 106 cB.ga 97 dy.eH (lf (qN lU.aS.b2 4 va 141 lA ah 137 aU)) (dd n2.S aA 159 d9.fC)) (iw oq.bm.cf 159 l0 aN 82 vZ X 78 ad (ac oM.bo 305 cU.fU))) (nd (qo v6.cK 98 xv L 56 wD K 52) (aZ (pj lK.eP.aD 135 dj.hH 231 ca qy.bI 71 dj.gL 67 dy.p5 j) (al fY.hL.bH.bH)) (ix rC.Cn.bm (aG af.hK.iG)))) (ef lO.ik.aX 107 wt k0 jZ 56 nW bF 52 bE (bS jU.aF (J au.vr.aI.db 73 dy.fL (aK pS.io)) (aW uk.aD (aK jV))) (nd (lz h9.EQ.FI) (gW m1.bw 83 bN rD.bI rM.bI 17 di.p4 80 ca lT.bl (bC k4.bQ.ag.ho 183 ap cX.sk.hL.bI cl.sk.hL.bI 137 ve cg 133 b3)) (bA tD.q5.dm 11 dI.gj 1 dI.f5 2 dI.hH (g4 gs.a0 42 dY.p4 155 dY.p3 14 dY.p2)))))))
def Dn : ab dp:=(c3 dz.bI (hS mj.jq 4 HT 50 H2 46 HX (aR eM.bP (aR pc (bc aU.bu (N d8.i0.bo 66 cy.fL (bk oR.ae.eh) (lf (qz cC))) (aZ (q1 jg.aS.aF.aj 23 da.gk 517 mJ aH.cR 501 m4 497 rC) (ff pg.a0.bP.g6 140 dL.eY 254 dL.p2 1 dL.eS))) (bU L.bu (aW lk.nS (ij m1.fg 99 bN d8.g8 84 ca aY.cY 80 aQ.cY)) (gz zY.cx.aF.aX 73 ep L.pD.n1 128 iq ar.bg.jd 124 ao.bg.jd (aT lO.bH.bi.b8 52 cU.eH 1 cU.f8 2 cU.fz)))) (d3 aP.cH (o1 l9.S 85 an bt.i9 113 c4 dk 109 e6 (ej k4.cx.ae 188 bN h5.fF d4.fF 69 cV.ev 65 cV.eZ (bC tp.bP.cs 94 bN lk.bl.fF kS.bl.fF 119 ca eQ.cR.bI 115 dz.cR.bI)) (du n2.ia.b2.eV.bg 150 cS.eu au X ad 78 xr aN (e5 dF.dv 50 cO.p4 109 cO.p2 K 105 L))) (hi uB.aI.bg 119 Ai pz 60 pp (aW b1.bi.nS (hT tZ.aI.S.S 80 yk ki 165 l0 dk 161 e6)) (J aw.pF.hU.bP.eV.dK.fy 188 c8.p3 (bk nB.gY))))) (dQ j7.dJ 110 z2.eW 15 z2.eH 1 z2.f8 2 z2.fz (bU ld.bQ (ol j3.aS 11 z8.fC 120 r5 gf 68 an bt.ce (eg tk.b6.ag 75 w5 jN 1 cB.fP 2 cB.gK (fJ jH.mv.aI) (ml e6)) (aZ (wp hQ.ec) (aT mU.dm.dm 11 cO.gn 1 cO.eA 2 cO.f9))) (N jH.iH.ib.bo 57 cG.eY (bA j8.aX.bP 132 dj.eZ 1 dj.fo 2 dj.fU (bM iu.dB.aj 97 hD iZ.cJ iY.cJ mW.cJ 143 dT.fC)) (J ka.aO.bi.hL.dx 156 c8.fE (dc ju)))) (ry gU.aX 122 z6.eu 40 z2.gm ak 36 af (eJ aE.bP.gY (bT aH.rF.aI.hV 199 et aP.aO (mg k8.eb.cQ.aC 11 ds.p3 66 wK aH 172 u5 dZ 168 eM)) (aZ (lZ sO.bH.bi.aD 53 c7.fC c7.gv 143 cA.fo aw) (fW hQ))) (fR uO.ec 67 cP.fP 144 cy.fU 1 cP.gK (J bt.xQ.r4.eF 174 cA.eH (al af.aX.a0.hK)) (de ak.cx.gY.gD (co aY.bg.eK)))))) (az gF.cz.aS 4 z1.f6 57 z1.fP 53 z1.gK (aR e6.bl (bU H.bP (lj nw.eP.S 95 z8.fp e_ 95 z8.ft e_ 114 zR e_ 110 z7.ev aP (op qG.xF (iO aw.bQ.bV.rF.bm.bz 114 dX k9.bl.bg) (la d5.ag 46 d9.p7 d9.p6 d9.p5 1 d9.p4)) (bA ii.b6.dm 11 da.fx 1 da.gn 2 da.eA (lf (sG rK.gR.bg 36 dL.p5 230 ap aE.mv.aI.av 38 dL.p4 192 ki.eC.av)))) (fR uq.cQ 47 c5.gL 109 cG.ft 31 c5.p9 (aZ (lZ ma.a0 106 Ak c9.eY 103 hJ bt) (cp d5.b2.ae.aj 193 c6.ez c6.fK 78 c6.fN)) (md bd.kl.cR.bg.cR.a0 64 cI.eu 126 iz j5.kv.iH 141 cI.ez (lf (oO k8.aS.ia 4 cU.p1 54 cU.p0 50 cT.ex))))) (lC cF vk fY.bu (nd (q1 rz.ag.aj 23 z9.p6 124 an uG.b0 108 H.bP.b0 104 uc.b0) (J L.cR.bV.fd 159 cV.gH (mb oX.ag.aS 4 cN.fT 114 bv qQ.aO 110 tG.aO)) (gV ii.b6.bw 109 c7.fm 269 c0.gn 19 c7.gH (ac iS.bo 783 cU.f9))) (eg sJ.b8 102 wr jH 1 cq.p7 2 cq.p6 (hX ma.aD 35 dP.eA 148 da.f9 71 c9.fx aw (iO my.kB.ib.gE.cw 244 ap my.xF.fF)) (de mq.hK.gD (em nA.a0.cs 197 dY.fi dY.eW 598 dY.fK 594 dY.fN))))) (nd (rP j2 wN Bq 24 (aM cD f7 e_) 65 (aM cF f7 e_) aP) (az nL.S.a0 96 z4.p6 119 z4.ga 14 z4.p5 (eg fc.eN.cR.b8.b8 101 an kx.b0 1 z9.ft 2 z9.f4 (o1 tq.aj.ae 78 ep af.aS 62 dX ak.y9 58 af.y9 (iL uT.cd.aD 172 b7 bj.yd.ae br.yd.ae 71 ds.eW 67 ds.eH) (dd yG aA 115 d9.fz)) (m5 mY.bu (lf (wx kQ.kl 52 si 165 zp aE 14 dM.f4)))) (nd (pV ii.aX 58 xg 248 et aH 83 fe 79 wu) (jW pU.dJ.aX.aF.aD 55 dj.gd 168 iB ue.Eb.kB 180 dy.fx aw (bC l8.iI.cz.S 193 jK cg b3 149 mK ah 145 aU)) (J vS.pF.kY.eF 75 c8.gH (eo hY.S.a0 162 dq.fo 82 zh aE 14 dq.fU)))) (bc b1.fy (gI gs.iI.b2 4 dn.p3 72 fG ow 68 m3 (ej wk.aX 89 xd K L 58 dy.f8 54 ws (ac bt.nh.vv.D8.fy.bz 82 dT.gK)) (aZ (pj uY.b8.bw 147 c7.hH 232 bN aH.d6 17 c7.gL 81 rU bO) (aT fc.aX.bP 45 cL.f5 1 cL.hH 2 cL.gL))) (N kJ.o5.eD.aI 53 cP.p3 (bT jw.kY.sx.cJ.aO.aO 500 tj cX (aG jH.aC.S.gB)) (ck oM.fQ (lf (yu hR.S 98 dY.gj dY.f5 dY.hH 43 ep))))))))
def DK : ab dp:=(d3 cX (bc aV (az sC.a0 59 z1.fC 107 z1.gg 14 z1.gv (bS aV.bm (nd (oh m2.kl 98 se aN 139 AA dV 14 z7.fM) (N j.GW.hM.gT 82 cy.fx (ac b4.y9.jd.eD.kk 221 dI.p8) (fb cD FM bd)) (bD oi.b2.dv 116 sg k0 jZ 77 hJ aY 73 aQ (i7 mZ.bH.g0 186 ap nB.av nG.av 17 dL.gn 96 ey aH.cY))) (nd (sG iT.eb.gR.bg 36 c5.gH 123 fG dN.eC.aD 38 c5.gm 85 bt.rF.bw) (J bK.bm.bV.fd 159 c9.fT (bC sH.e0.cQ 80 pt h5 d4 185 b7 aY.cK 181 aQ.cK)) (J vK.jd.eD.kk 221 cI.f4 (aG d0.aC)))) (nl nn (aJ nE.ik 11 z9.fq 1 z9.gb 2 z9.gd (J oA.Fy.ib.bo 529 da.f4 (ac lP.r4.iv.bm.dx 164 dr.p3)) (aZ (rx qe.ag 134 lA 1 va 2 c0.gg) (cp dF.g0 50 cL.fK cL.fN 19 cL.ex))) (nd (qK cZ.eV.bp 86 cq.fE 54 cq.fD 50 cq.gL) (dG aP.fj.cH (aG rG.eK.ce)) (ck e_.aO.fQ (em pb.dJ.b8.bw 589 dY.fA dY.eu 17 dq.eA 204 dq.p3))))) (c3 ow (pK gU.dJ.aj 23 z4.gm 118 z4.fC z4.gv 92 z4.fq (k2 nE.b6 99 c4 jN 1 z8.p9 2 z8.p8 (dQ oK.aX 35 cB.fU 94 cB.fi 62 cB.eW 58 zZ (pL qx.e0.iF 4 dI.fx 191 jK H 17 dr.p9) (dd cZ.b6 aA 9 cO.ft)) (du qg.bi.aD 60 uV g5 gq k6 190 lm kc (cp tn.bw 43 dM.fo jc 19 dM.fi))) (qv ko.bl.aS 4 cG.p3 60 cG.gv 51 cM.fL (fV Cr.ja.ae 140 dj.ez 323 cA.eS 320 cA.fm (mb rq.cz.aS 4 dT.p6 115 bv uH.aO 111 oW.aO)) (j4 e_.xx.aI.bu (bk bq.gY)))) (d3 L (eJ d8.gY (J bt.cd.aI.db 126 dy.fu (ml uN.cH)) (J aE.kB.aF.eD.kk 66 c7.gd (e5 h3.fg 57 cL.gK 94 rW bF 90 bE))) (nd (qo eI.bu.gR.aX 73 r6 L 246 yl K 242) (gV k4.cx.eN 125 di.gm 133 di.fC 19 di.gv (aT eI.b8.dm.cJ.ag.dm 11 dL.f4 1 dL.fE 2 dL.fD)) (iw oU.S 106 bv bt.aO 79 ch g2 75 kg (lb bj.ib.bg)))))) (eL aE.r4.aF (N bK.bu.dh 269 Fq (bU ke (lj m8.jq.cs 103 z8.er e_ 104 z8.eB e_ 104 kw m4.bI 100 kw sP (aJ ot.e0.b8 51 ct.fK 1 cy.fp 2 ct.fN (d2 rG.vv.bm) (dc ci)) (bA n0.b6 65 cA.f6 1 cA.fP 2 cA.gK (bC mZ.bH.b6.ho 194 ap ar.ni.eK.av ao.ni.eK.av 144 ey dN.aX.cv 140 ie.aX.cv))) (N bE.bu.cw 180 cG.ev (bT jv.vL.hM.bu.dK.fy 122 iB jv.o5.kB (fJ o6.x2.eC)) (ix rM.Cn.bm (bk dZ.gY)))) (N jN.eV.bz 46 z6.e7 (gA qU.it 100 an dO.cQ.ce cj.cQ.ce dS.cQ.ce 124 c4 lR.aO (J e_.eV.gE.bz 552 mJ (co H.AO.bl.ec)) (kN jx.eV.fj.S 158 yY au X ad 86 da.p1 (ms g7))) (dQ sZ.bw 175 cP.p6 416 ct.eH 17 cq.gn 159 cq.eA (aZ (qN ii.aX.b2 4 vi 95 fe hW 91 ld) (h6 oU.S.a0 118 bv oM.aO 109 ch au.ce 14 dl.eY)) (aZ (lL u9.b2.aj.ae.aj.gR.bg 36 c7.gk 111 c8.p2 H 38 c7.er 73 vc qb) (lc gr.gC.iF 11 dY.fE 118 dY.fD 273 dY.eB 17 dY.fu))))) (aJ i3.b8 49 z3.gK 1 z3.fp 2 z3.ft (bc e3.eV (ol qU.jq 11 z9.f8 120 an e_.ae.ce 108 c4 fY.fy (N aP.cH.o5.eD.aI 56 ct.fP (aG gu.fQ) (dd d5.b6 aB 301 FE.e7)) (eG pR.eV.ja.ag 87 mG ah bK ea 1 cS.e7 (ff iA.a0.ag 48 dM.ga 235 cL.gj 1 dM.gj))) (az zu.hL.S 123 cq.fo 96 cM.eY 150 cq.fi (aW q6.aD (lb fY.bg.pF.bg)) (aZ (wB qk.dm.cd.aX.bl.aD 65 c8.gn 230 cN.gL 154 cI.p2 aw) (ff i4.b6.b6.bg 56 cT.fL 450 dY.fo 81 dq.ez)))) (bc A8 (ei oV.ec.aD 47 c5.ev c5.eZ 63 c5.fo 26 c5.fU (bD jx.cf.aj 219 ug bF bE 76 pm jt 72 gX (ac qL.bP.dt 334 dl.ft)) (aW dk.nS (bk gu))) (N tT.k7.fy 64 cy.fD (bT bq.bQ.xQ.bu.dK.fy 131 je aw.iF.cH (aG bd.h8.S.gB)) (du ti.cx.bi.S 68 ca dO.bl gu t7 83 bN l6.bI (ji fI)))))))
def mC : ab dp:=(ph iA.eP.bg 100 z9 225 dn (hS hY.aj 16 z3 52 z4 48 z5 (ph d5.ag 46 c5 1 cG (im kO (ph il.ec.bQ 19 dj 17 dP Ez Fv) (hS cZ.ec.aD 38 c0 63 dI 26 di Fn E2)) (im kW (im dS EP EL) (hS h3.a0.aj 89 c6 98 dl 94 dL Ej EV))) (im d8 (nd (Bj fa.jq.iF fY 4 cP e_ 17 cy e_) (nd (wl fY) E3 EC) (c3 oa Dr Dk)) (ph i1.ag 44 dy 1 c9 (nd (rP l4 wN Bq 32 (aM cD fB e_) 145 (aM cF fB e_) bd) Du Dl) (c3 b3 DI Dw)))) (az hY.aS 4 z6 52 z7 48 z8 (im fX (im tx (az j0.dK.aX 28 di 44 da 40 cA DN Dt) (ph cZ.dK.aF 42 dr 1 ds DF DM)) (az jS.S 178 ct 51 cB 47 cV (nd (w4 jN) DB Ds) (bc nn DD DH))) (ph d5.aj 16 cM 50 cq (hS tg 224 dT 121 cS 200 cI (im cj Dy Dv) (c3 om DC DJ)) (im cg (az fk.ec.aX 40 c8 29 cN 60 c7 DE Dx) (nd (yw j2 24 65) Dn DK)))))
def bx : dp→Bool:=sf mC
lemma DQ : ay bx Ez = true := by decide +kernel
lemma Ee : ay bx Fv = true := by decide +kernel
lemma DY : ay bx Fn = true := by decide +kernel
lemma D9 : ay bx E2 = true := by decide +kernel
lemma D5 : ay bx EP = true := by decide +kernel
lemma DV : ay bx EL = true := by decide +kernel
lemma D0 : ay bx Ej = true := by decide +kernel
lemma DS : ay bx EV = true := by decide +kernel
lemma D3 : ay bx E3 = true := by decide +kernel
lemma DX : ay bx EC = true := by decide +kernel
lemma Dd : ay bx Dr = true := by decide +kernel
lemma Da : ay bx Dk = true := by decide +kernel
lemma CY : ay bx Du = true := by decide +kernel
lemma C9 : ay bx Dl = true := by decide +kernel
lemma C8 : ay bx DI = true := by decide +kernel
lemma CO : ay bx Dw = true := by decide +kernel
lemma CA : ay bx DN = true := by decide +kernel
lemma C5 : ay bx Dt = true := by decide +kernel
lemma CZ : ay bx DF = true := by decide +kernel
lemma C7 : ay bx DM = true := by decide +kernel
lemma C0 : ay bx DB = true := by decide +kernel
lemma C6 : ay bx Ds = true := by decide +kernel
lemma CM : ay bx DD = true := by decide +kernel
lemma Cy : ay bx DH = true := by decide +kernel
lemma CQ : ay bx Dy = true := by decide +kernel
lemma CS : ay bx Dv = true := by decide +kernel
lemma C4 : ay bx DC = true := by decide +kernel
lemma CV : ay bx DJ = true := by decide +kernel
lemma CT : ay bx DE = true := by decide +kernel
lemma Db : ay bx Dx = true := by decide +kernel
lemma CK : ay bx Dn = true := by decide +kernel
lemma Dc : ay bx DK = true := by decide +kernel
lemma ew (x:dp) {l r : ab dp}
    (hx : bx x = true) (hl : ay bx l = true) (hr : ay bx r = true) :
    ay bx (nd x l r) = true := by
  change (bx x&&ay bx l&&ay bx r) = true
  rw [hx,hl,hr]; rfl
lemma AS : ay (sf mC) mC = true :=
  (ew (oH iA.eP.bg 100 z9 225 dn) (by decide +kernel) (ew (m0 hY.aj 16 z3 52 z4 48 z5) (by decide +kernel) (ew (oH d5.ag 46 c5 1 cG) (by decide +kernel) (ew (km kO) (by decide +kernel) (ew (oH il.ec.bQ 19 dj 17 dP) (by decide +kernel) DQ Ee) (ew (m0 cZ.ec.aD 38 c0 63 dI 26 di) (by decide +kernel) DY D9)) (ew (km kW) (by decide +kernel) (ew (km dS) (by decide +kernel) D5 DV) (ew (m0 h3.a0.aj 89 c6 98 dl 94 dL) (by decide +kernel) D0 DS))) (ew (km d8) (by decide +kernel) (ew (Bj fa.jq.iF fY 4 cP e_ 17 cy e_) (by decide +kernel) (ew (wl fY) (by decide +kernel) D3 DX) (ew (q0 oa) (by decide +kernel) Dd Da)) (ew (oH i1.ag 44 dy 1 c9) (by decide +kernel) (ew (rP l4 wN Bq 32 (aM cD fB e_) 145 (aM cF fB e_) bd) (by decide +kernel) CY C9) (ew (q0 b3) (by decide +kernel) C8 CO)))) (ew (oe hY.aS 4 z6 52 z7 48 z8) (by decide +kernel) (ew (km fX) (by decide +kernel) (ew (km tx) (by decide +kernel) (ew (oe j0.dK.aX 28 di 44 da 40 cA) (by decide +kernel) CA C5) (ew (oH cZ.dK.aF 42 dr 1 ds) (by decide +kernel) CZ C7)) (ew (oe jS.S 178 ct 51 cB 47 cV) (by decide +kernel) (ew (w4 jN) (by decide +kernel) C0 C6) (ew (AG nn) (by decide +kernel) CM Cy))) (ew (oH d5.aj 16 cM 50 cq) (by decide +kernel) (ew (m0 tg 224 dT 121 cS 200 cI) (by decide +kernel) (ew (km cj) (by decide +kernel) CQ CS) (ew (q0 om) (by decide +kernel) C4 CV)) (ew (km cg) (by decide +kernel) (ew (oe fk.ec.aX 40 c8 29 cN 60 c7) (by decide +kernel) CT Db) (ew (yw j2 24 65) (by decide +kernel) CK Dc)))))
def uX (idx:Pos) (q w : List Bool) : Bool :=
  match ig mC idx with
  | none => false
  | some x =>
    let y:=fw x
    let z:=hG q .qB w
    Cz y.state z.state&&lp y.front z.front&&lp y.past z.past
lemma am (idx:Pos) (q w : List Bool)
    (h : uX idx q w = true) (r:ai) :
    cE (BL (bf default (be q)) (be w+>r)) lr := by
  unfold uX at h
  rcases hx : ig mC idx with _ | x
  · rw [hx] at h; contradiction
  · rw [hx] at h
    dsimp only at h
    simp only [Bool.and_eq_true,zQ,oE] at h
    rcases h with ⟨⟨hs,hf⟩,hp⟩
    have heq : fw x = hG q .qB w := by
      rcases h1 : fw x with ⟨p1,f1,s1⟩
      rcases h2 : hG q .qB w with ⟨p2,f2,s2⟩
      rw [h1,h2] at hs hf hp
      dsimp only at hs hf hp
      subst hs hf hp
      rfl
    have hs_g:=Be mC AS idx x hx r
    rw [heq,pE] at hs_g
    exact hs_g
lemma AW (d:cm) (us : List W) :
    cn d us = bf default (be ([false]++bW d++bG us)) := by
  unfold cn
  simp [x8]
lemma xO : r8 := by
  intro d a b c r
  rw [AW d [a,b,c]]
  cases d <;> cases a <;> cases b <;> cases c
  · exact ⟨am d1.fK ([false]++bW cD++bG kD) aA (by decide +kernel) r,am d1.fN ([false]++bW cD++bG kD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.ex ([false]++bW cD++bG f7) aA (by decide +kernel) r,am d1.fL ([false]++bW cD++bG f7) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gg ([false]++bW cD++bG nP) aA (by decide +kernel) r,am d1.eY ([false]++bW cD++bG nP) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.eS ([false]++bW cD++bG vR) aA (by decide +kernel) r,am d1.fm ([false]++bW cD++bG vR) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gH ([false]++bW cD++bG dE) aA (by decide +kernel) r,am d1.gm ([false]++bW cD++bG dE) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fC ([false]++bW cD++bG hI) aA (by decide +kernel) r,am d1.gv ([false]++bW cD++bG hI) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fq ([false]++bW cD++bG mD) aA (by decide +kernel) r,am d1.gb ([false]++bW cD++bG mD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.fM ([false]++bW cD++bG fB) aA (by decide +kernel) r,am d1.fx ([false]++bW cD++bG fB) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.eA ([false]++bW cF++bG kD) aA (by decide +kernel) r,am d1.f9 ([false]++bW cF++bG kD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.ga ([false]++bW cF++bG f7) aA (by decide +kernel) r,am d1.gj ([false]++bW cF++bG f7) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.f5 ([false]++bW cF++bG nP) aA (by decide +kernel) r,am d1.hH ([false]++bW cF++bG nP) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.gL ([false]++bW cF++bG vR) aA (by decide +kernel) r,am d1.p9 ([false]++bW cF++bG vR) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p8 ([false]++bW cF++bG dE) aA (by decide +kernel) r,am d1.p7 ([false]++bW cF++bG dE) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p6 ([false]++bW cF++bG hI) aA (by decide +kernel) r,am d1.p5 ([false]++bW cF++bG hI) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p4 ([false]++bW cF++bG mD) aA (by decide +kernel) r,am d1.p3 ([false]++bW cF++bG mD) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
  · exact ⟨am d1.p1 ([false]++bW cF++bG fB) aA (by decide +kernel) r,am d1.p0 ([false]++bW cF++bG fB) [false,false,true,true,true,false,true] (by decide +kernel) r⟩
end

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  BusyBeaver.Excursion.does_not_halt_of_advances CR
    ⟨.CD, [.UA, .UT, .UA, .UA], _, by decide, rfl⟩ (y3 xO)

end BusyBeaver.M_1RB1RF_1LC0LF_HHH0LD_0LE1LD_0RF0LB_1RA1RE
