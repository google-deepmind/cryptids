/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`

## Collatz-like Acceleration Rules
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

open SixState Turing


def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

local notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
local notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
local notation3 c₁ " [" M "]⊢* " c₂ => ∃ n, multiStep M c₁ n = some c₂
local notation3 c₁ " [" M "]⊢⁺ " c₂ => ∃ n > 0, multiStep M c₁ n = some c₂

local notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
local notation:67 s:67 " << " a:68 => ListBlank.cons a s
local infixr:67 " >> " => ListBlank.cons
local notation:67 s:67 " <+ " l:68 => ListBlank.append l s
local infixr:67 " +> " => ListBlank.append
local notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
local notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

@[simp]
def listNatRepeat {Γ} (l : List Γ) (n : Nat) : List Γ := match n with
  | 0 => []
  | n + 1 => List.append l (listNatRepeat l n)

local instance instHPowListNatLocal {Γ} : HPow (List Γ) Nat (List Γ) := ⟨listNatRepeat⟩

lemma flatten_replicate_eq_listNatRepeat {Γ} (l : List Γ) (n : Nat) :
    (List.replicate n l).flatten = listNatRepeat l n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change l ++ (List.replicate n l).flatten = l ++ listNatRepeat l n
    rw [ih]

variable {zG_ zL_ α β γ : Type*} [Inhabited zG_] [Inhabited zL_]
variable {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
@[simp] lemma zMz (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 0 = some config
    := rfl
@[simp] lemma zMo (M : Machine zG_ zL_) (config : Cfg zG_ zL_) : multiStep M config 1 = step M
    config := rfl
@[simp] lemma zMs (M : Machine zG_ zL_) (config : Cfg zG_ zL_) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] lemma zPz (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zPsl (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma zCal (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma zAnl (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma zLan (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma zLac (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x >>
    (xs +> b) := rfl
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl
omit [Inhabited zG_] in
@[simp]
theorem zLpa (l : List zG_) (n m : Nat) : l^(n + m) = l^n ++ l^m := match m with
  | 0 => by simp_rw [HPow.hPow, add_zero, listNatRepeat, List.append_nil]
  | m + 1 => by
    rw [add_comm m 1, <- add_assoc, add_comm 1 m, zLpa]
    simp only [HPow.hPow, listNatRepeat, List.append_eq, List.append_assoc]
    rw [<- List.append_assoc, <- List.append_assoc, List.append_cancel_right_eq]
    induction n with
    | zero => simp
    | succ n ih => simpa
omit [Inhabited zG_] in
theorem zLpc (l : List zG_) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [<- zLpa, add_comm, zLpa]
lemma zLaa (s : ListBlank zG_) (l₁ l₂ : List zG_) :
    (s <+ l₁) <+ l₂ = s <+ (l₂ ++ l₁) := by
  unfold ListBlank.append
  split
  · split
    · next h => simp_all
    · simp_all
  · rename_i _ l₂ l₁
    refine (congr_arg _ ?_).symm
    exact ListBlank.append_assoc l₁ _ s
lemma zLp1 (u : List (Fin 2)) (k : Nat) :
    u^k ++ u = u^(k + 1) := by
  have h := zLpc u k 1
  dsimp [HPow.hPow, listNatRepeat] at h ⊢
  rw [List.append_nil] at h
  exact h
lemma zPar (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [zLpa, <- zLaa]
lemma zPsr (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [zPsl, <- zLaa]
lemma zPl (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [zLaa, <- zLpa, add_comm]
lemma zPa1 (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [zLaa, zLp1]
lemma zPal (l : ListBlank (Fin 2)) (u : List (Fin 2)) (k : Nat) :
    (l <+ u) <+ (u ^ k) = l <+ (u ^ (k + 1)) := by
  rw [zLaa, zLp1]
lemma append_zero_pow_01 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ k = (s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [0]) [0, 1] k 1, ih]
    have h1 : ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ [0]) <+ ([0, 1] : List (Fin 2)) ^ 1 =
        ((s <+ ([1, 0] : List (Fin 2)) ^ k) <+ ([1, 0] : List (Fin 2)) ^ 1) <+ [0] := rfl
    rw [h1, <- zPl s [1, 0] k 1]
lemma default_pow_01 (c : Nat) :
    (default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ c =
    (default <+ ([1, 0] : List (Fin 2)) ^ c) <+ [0] := by
  have h0 : (default : ListBlank (Fin 2)) = default <+ [0] := zZcd.symm
  conv_lhs => rw [h0]
  exact append_zero_pow_01 default c
lemma append_one_pow_10 (s : ListBlank (Fin 2)) (k : Nat) :
    (s <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ k = (s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1] := by
  induction k with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPl (s <+ [1]) [1, 0] k 1, ih]
    have h1 : ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ [1]) <+ ([1, 0] : List (Fin 2)) ^ 1 =
        ((s <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2)) ^ 1) <+ [1] := rfl
    rw [h1, <- zPl s [0, 1] k 1]
lemma pow_11_eq_pow_1_mul2 (k : Nat) :
    ([1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (2 * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h2 : 2 * (k + 1) = 2 + 2 * k := by omega
    rw [zPsl, ih, h2, zLpa]
    rfl
lemma pow_01_append_0 (k : Nat) (r : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k) +> ([0] +> r) =
    [0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r) := by
  induction k generalizing r with
  | zero =>
    simp only [zPz, zLan]
  | succ k ih =>
    rw [zPsr, ih]
    have h1 : ([0, 1] : List (Fin 2)) +> ([0] +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) =
        [0] +> (([1, 0] : List (Fin 2)) +> ((([1, 0] : List (Fin 2)) ^ k) +> r)) := rfl
    rw [h1, <- zPsr]
lemma zSm {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma step_stepStar {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1, zSm tm c_1 c_2 h⟩
lemma zSp2 {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 : Cfg zG_ zL_) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 : Cfg zG_ zL_) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    (tm : Machine zG_ zL_) (c_1 c_2 c_3 : Cfg zG_ zL_) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 : Cfg zG_ zL_} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPsp {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSpp {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 :=
  zPsp h₁ (zPs h₂)
lemma zSsp {zG_ zL_ : Type*} [Inhabited zG_] [Inhabited zL_]
    {tm : Machine zG_ zL_} {c_1 c_2 c_3 : Cfg zG_ zL_}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  zPsp (zSp2 tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine zSsp (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
            Tape.write, zZcd, zDh, zDt])
macro "execute5" : tactic =>
  `(tactic| (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
          (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;>
          (any_goals (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
lemma shift_E_ones_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1] : List (Fin 2)) ^ k +> r)) [target]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{E}}> ([1] +> (([1] : List (Fin 2)) ^ k +> r)))
        [target]⊢*
        ((l <+ [1]) {{E}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [1]) r
    rw [zPal] at h2
    exact zSt h1 h2
lemma shift_CB_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [target]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([0, 1] : List (Fin 2)) ^ k) <+ [0, 1]) {{C}}> ([1] +> r))
        [target]⊢*
        ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
lemma shift_D_right_100_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : (l {{D}}> ([1, 0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
        [target]⊢*
        ((l <+ [0, 1]) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih (l <+ [0, 1]) r
    rw [zPal] at h2
    exact zSt h1 h2
lemma shift_FA_left_0082 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> r)) [target]⊢*
    (l {{F}}> ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{F}}> ([0] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> ([0, 1] +> r))) := by
      dsimp [ListBlank.append]
      execute
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [zPa1] at h2
    exact zSt h1 h2
def E_0082 (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ a)
          {{E}}> default
def F_R (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
          {{F}}>
    ([0, 0] +> r)
def cfg_A (b k c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k)
          {{F}}>
    ([0, 0] +> (([1] : List (Fin 2)) ^ c +> default))
lemma cfg_A_eq_F_R (b k c : Nat) :
    cfg_A b k c = F_R b k (([1] : List (Fin 2)) ^ c +> default) := rfl
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 0] 1 (.rep [1] 0 .default)
    head  := some F
    right := .sym 0 (.sym 0 (.rep [1] 2 .default)) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

lemma eval_pat_A (vars : Nat → Nat) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) := by
  dsimp [evalTapePattern, evalTapeExpr, pat_A, cfg_A, F_R, HPow.hPow, instHPowListNat]
  repeat rw [flatten_replicate_eq_listNatRepeat]
  unfold Cfg.headRight
  rfl

lemma in_ps_A (b k c : Nat) : IsInPatternSet ps (cfg_A b k c) := by
  refine ⟨(pat_A, .true), List.Mem.head _, fun i => match i with | 0 => b | 1 => k | _ => c, ?_,
          trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => b | 1 => k | _ => c)).symm
def Closes (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (cfg [target]⊢⁺ cfg') /\
          (IsInPatternSet ps cfg' \/ (step target cfg').isNone)
lemma closes_of_in_ps {cfg cfg' : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg [target]⊢⁺ cfg') (h_in : IsInPatternSet ps cfg') :
    Closes cfg :=
  ⟨cfg', h_step, Or.inl h_in⟩
lemma closes_of_halt {cfg cfg' : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg [target]⊢⁺ cfg') (h_halt : (step target cfg').isNone) :
    Closes cfg :=
  ⟨cfg', h_step, Or.inr h_halt⟩
lemma closes_of_stepPlus {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg₁ [target]⊢⁺ cfg₂) (h_close : Closes cfg₂) :
    Closes cfg₁ := by
  rcases h_close with ⟨cfg', h_step', h_end⟩
  exact ⟨cfg', zPt h_step h_step', h_end⟩
lemma closes_of_stepStar {cfg₁ cfg₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : cfg₁ [target]⊢* cfg₂) (h_close : Closes cfg₂) :
    Closes cfg₁ := by
  rcases h_close with ⟨cfg', h_step', h_end⟩
  exact ⟨cfg', zSpp h_step h_step', h_end⟩
theorem init_to_E_0082 : (init []) [target]⊢⁺ (E_0082 0 4) := by
  unfold init E_0082
  simp only [Tape.mk₁, zPz, zPsl, zCal, zAnl,
    zLan, zLac]
  execute
theorem step_E_b0_0082 (a : Nat) :
    (E_0082 a 0) [target]⊢⁺ (E_0082 0 (2 * a + 4)) := by
  unfold E_0082
  simp only [zPz, zLan]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) {{E}}> default)
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) <+ [0]) {{C}}> ([1] +> ([1]
              +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- default_pow_01 a] at h1
  have h2 := shift_CB_left_0082 a default ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((default : ListBlank (Fin 2)) {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1]
          +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones_0082 (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          3) default
  rw [<- zPl default ([1] : List (Fin 2)) 3 (2 * a + 1)] at h4
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h4
  exact zPsp (zPt (zPsp h1 h2) h3) h4
theorem step_E_b1_0082 (a : Nat) :
    (E_0082 a 1) [target]⊢⁺ (E_0082 0 (2 * a + 6)) := by
  unfold E_0082
  simp only [zPz, zLan]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) a] at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+
          [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones_0082 (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          5) default
  rw [<- zPl default ([1] : List (Fin 2)) 5 (2 * a + 1)] at h4
  have ha : 5 + (2 * a + 1) = 2 * a + 6 := by omega
  rw [ha] at h4
  exact zPsp (zPt (zPsp h1 h2) h3) h4
theorem step_E_b2_to_D_halt_0082 (a : Nat) :
    (E_0082 a 2) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ (2 * a + 4) +>
            default))) := by
  unfold E_0082
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) a] at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+
          [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default,
    <- zPar ([1] : List (Fin 2)) 3 (2 * a + 1) default] at h3
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h3
  exact zPt (zPsp h1 h2) h3
theorem step_E_b3_to_cfg_A (a b : Nat) :
    (E_0082 a (b + 3)) [target]⊢⁺ (cfg_A (b + 1) 0 (2 * a + 3)) := by
  unfold E_0082 cfg_A
  simp only [zPz, zLan]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List
          (Fin 2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List (Fin
              2)) ^ a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) a]
      at h1
  have h2 := shift_CB_left_0082 a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
          3)) <+ [0]) ([1] +> default)
  rw [pow_11_eq_pow_1_mul2 a] at h2
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1 h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
          (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) {{F}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    dsimp [ListBlank.append]
    execute
  rw [<- zPar ([1] : List (Fin 2)) (2 * a) 1 default,
    <- zPar ([1] : List (Fin 2)) 2 (2 * a + 1) default] at h3
  have ha : 2 + (2 * a + 1) = 2 * a + 3 := by omega
  rw [ha] at h3
  exact zPt (zPsp h1 h2) h3
theorem step_F_b2_k0_0082 (c : Nat) :
    (cfg_A 2 0 (c + 1)) [target]⊢⁺ (cfg_A 5 0 c) := by
  unfold cfg_A
  rw [zPsr ([1] : List (Fin 2)) c default]
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
theorem init_reaches_A_502 :
    (init []) [target]⊢* (cfg_A 5 0 2) :=
  zPs
    (zPt init_to_E_0082
      (zPt (step_E_b3_to_cfg_A 0 1) (step_F_b2_k0_0082 2)))
lemma isNone_step_D_00 (l r : ListBlank (Fin 2)) :
    (step target (l {{D}}> ([0, 0] +> r))).isNone = true := by
  simp only [step, D, target, zLac, zLan,
    Turing.ListBlank.head_cons]
  rfl
lemma closes_E (a b : Nat) : Closes (E_0082 a b) := by
  rcases b with _ | _ | _ | b'
  · have h1 := step_E_b0_0082 a
    have hb : 2 * a + 4 = (2 * a + 1) + 3 := by omega
    rw [hb] at h1
    exact closes_of_in_ps (zPt h1 (step_E_b3_to_cfg_A 0 (2 * a + 1)))
      (in_ps_A (2 * a + 2) 0 3)
  · have h1 := step_E_b1_0082 a
    have hb : 2 * a + 6 = (2 * a + 3) + 3 := by omega
    rw [hb] at h1
    exact closes_of_in_ps (zPt h1 (step_E_b3_to_cfg_A 0 (2 * a + 3)))
      (in_ps_A (2 * a + 4) 0 3)
  · exact closes_of_halt (step_E_b2_to_D_halt_0082 a) (isNone_step_D_00 _ _)
  · exact closes_of_in_ps (step_E_b3_to_cfg_A a b') (in_ps_A (b' + 1) 0 (2 * a + 3))
def D100 (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k) <+
          [0]) {{D}}>
    ([1, 0, 0] +> r)
def C_bounce (b : Nat) (s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) {{C}}> ([1] +> s)
lemma step_F0_sweep_right_0082 (k : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
    [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  have h1 : ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    dsimp [ListBlank.append]
    execute
  have h2 := shift_D_right_100_0082 k default r
  exact zPsp h1 h2
lemma F_R_b0_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 0 k r) [target]⊢⁺ (D100 0 k r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k default ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 := step_F0_sweep_right_0082 k r
  rw [default_pow_01 k] at h2
  exact zSpp h1 h2
lemma F_R_b1_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 1 k r) [target]⊢⁺ (D100 0 (k + 1) r) := by
  unfold F_R D100
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) ([0]
          +> r)
  rw [pow_01_append_0 k r] at h1
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{F}}>
        ([0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPsr ([1, 0] : List (Fin 2)) k r] at h2
  have h3 := step_F0_sweep_right_0082 (k + 1) r
  rw [default_pow_01 (k + 1)] at h3
  exact zPt (zSpp h1 h2) h3
lemma F_R_b3_to_D100 (b k : Nat) (r : ListBlank (Fin 2)) :
    (F_R (b + 3) k r) [target]⊢⁺ (D100 (b + 1) k r) := by
  unfold F_R D100
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3))
          ([0] +> r)
  rw [pow_01_append_0 k r] at h1
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2] at h1
  have h2 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List (Fin
          2)) ^ 2) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) {{D}}>
        ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  have h3 := shift_D_right_100_0082 k
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) r
  rw [append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) k] at h3
  exact zPsp (zSpp h1 h2) h3
lemma D100_0_11 (k : Nat) (r : ListBlank (Fin 2)) :
    (D100 0 k ([1, 1] +> r)) [target]⊢⁺ (F_R 1 (k + 1) r) := by
  unfold D100 F_R
  simp only [zPz, zLan]
  rw [<- default_pow_01 k]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2))
              ^ 1) <+ [1]) {{F}}>
        ([0, 0] +> r)) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPl default ([0, 1] : List (Fin 2)) k 1,
    <- append_one_pow_10 default (k + 1)] at h1
  exact h1
lemma D100_succ_11 (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 (b + 1) k ([1, 1] +> r)) [target]⊢⁺ (F_R (b + 1) (k + 2) r) := by
  unfold D100 F_R
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List
          (Fin 2)) ^ k) <+ [0]) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1, 0] : List (Fin
              2)) ^ k) <+
        ([1, 0] : List (Fin 2)) ^ 2) {{F}}>
        ([0, 0] +> r)) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) ([1,
    0] : List (Fin 2)) k 2]
      at h1
  exact h1
lemma D100_nil_to_C_bounce (b k : Nat) :
    (D100 b k default) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 3) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> default))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0,
    1] : List (Fin 2)) k 1]
      at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 1 default] at h2
  have hk : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma D100_one_to_C_bounce (b k : Nat) :
    (D100 b k ([1] +> default)) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 5) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1] +> default)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 2) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0,
    1] : List (Fin 2)) k 2]
      at h1
  have h2 := shift_CB_left_0082 (k + 2) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pow_11_eq_pow_1_mul2 (k + 2),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 2)) 1 default] at h2
  have hk : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma D100_01_to_C_bounce (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 b k ([0, 1] +> r)) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 4) +> r)) := by
  unfold D100 C_bounce
  rw [<- append_zero_pow_01 ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) k]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([0, 1] +> r)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 2 +> r))) := by
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  rw [<- zPl (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) ([0,
    1] : List (Fin 2)) k 1]
      at h1
  have h2 := shift_CB_left_0082 (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 2 +> r)
  rw [pow_11_eq_pow_1_mul2 (k + 1),
    <- zPar ([1] : List (Fin 2)) (2 * (k + 1)) 2 r] at h2
  have hk : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [hk] at h2
  exact zPsp h1 h2
lemma C_bounce_0 (s : ListBlank (Fin 2)) :
    (C_bounce 0 s) [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}> s) := by
  unfold C_bounce
  simp only [zPz, zLan]
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma C_bounce_1 (s : ListBlank (Fin 2)) :
    (C_bounce 1 s) [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}> s) := by
  unfold C_bounce
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma C_bounce_2 (s : ListBlank (Fin 2)) :
    (C_bounce 2 s) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> s))) := by
  unfold C_bounce
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma C_bounce_3 (b : Nat) (s : ListBlank (Fin 2)) :
    (C_bounce (b + 3) s) [target]⊢⁺
    (F_R (b + 1) 0 (([1] : List (Fin 2)) ^ 2 +> s)) := by
  unfold C_bounce F_R
  simp only [zPz, zLan]
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, zPl default ([1] : List (Fin 2)) (b + 1) 2]
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma step_F_ksucc_c0 (b k : Nat) :
    (cfg_A b (k + 1) 0) [target]⊢⁺ (cfg_A b k 1) := by
  unfold cfg_A
  rw [zPl ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) ([1, 0] : List (Fin 2)) k 1]
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma step_F_b2_k0_c0 :
    (cfg_A 2 0 0) [target]⊢⁺ (cfg_A 3 0 3) := by
  unfold cfg_A
  dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
  execute
lemma closes_C_bounce_ones (b n : Nat) :
    Closes (C_bounce b (([1] : List (Fin 2)) ^ n +> default)) := by
  rcases b with _ | _ | _ | b'
  · have h1 := C_bounce_0 (([1] : List (Fin 2)) ^ n +> default)
    have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3)
            default
    rw [<- zPl default ([1] : List (Fin 2)) 3 n] at h2
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (3 + n)) {{E}}> default) =
        E_0082 0 (3 + n) := rfl
    rw [h_eq] at h2
    exact closes_of_stepPlus (zPsp h1 h2) (closes_E 0 (3 + n))
  · have h1 := C_bounce_1 (([1] : List (Fin 2)) ^ n +> default)
    have h2 := shift_E_ones_0082 n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5)
            default
    rw [<- zPl default ([1] : List (Fin 2)) 5 n] at h2
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (5 + n)) {{E}}> default) =
        E_0082 0 (5 + n) := rfl
    rw [h_eq] at h2
    exact closes_of_stepPlus (zPsp h1 h2) (closes_E 0 (5 + n))
  · exact closes_of_halt (C_bounce_2 (([1] : List (Fin 2)) ^ n +> default)) (isNone_step_D_00 _ _)
  · have h1 := C_bounce_3 b' (([1] : List (Fin 2)) ^ n +> default)
    rw [<- zPar ([1] : List (Fin 2)) 2 n default, <- cfg_A_eq_F_R] at h1
    exact closes_of_in_ps h1 (in_ps_A (b' + 1) 0 (2 + n))
lemma closes_A_c0 (b k : Nat) : Closes (cfg_A b k 0) := by
  rcases k with _ | k'
  · rcases b with _ | _ | _ | b'
    · exact closes_of_stepPlus (zPt (F_R_b0_to_D100 0 default) (D100_nil_to_C_bounce 0 0))
        (closes_C_bounce_ones 0 3)
    · exact closes_of_stepPlus (zPt (F_R_b1_to_D100 0 default) (D100_nil_to_C_bounce 0 1))
        (closes_C_bounce_ones 0 5)
    · exact closes_of_in_ps step_F_b2_k0_c0 (in_ps_A 3 0 3)
    · exact closes_of_stepPlus (zPt (F_R_b3_to_D100 b' 0 default) (D100_nil_to_C_bounce (b' + 1) 0))
        (closes_C_bounce_ones (b' + 1) 3)
  · exact closes_of_in_ps (step_F_ksucc_c0 b k') (in_ps_A b k' 1)
lemma closes_A_b0 (k c : Nat) : Closes (cfg_A 0 k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 0 k
  · exact closes_of_stepPlus (zPt (F_R_b0_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 k))
      (closes_C_bounce_ones 0 (2 * k + 5))
  · have hc : (([1] : List (Fin 2)) ^ (c' + 2) +> (default : ListBlank (Fin 2))) =
        [1, 1] +> (([1] : List (Fin 2)) ^ c' +> default) := by
      rw [Nat.add_comm c' 2, zPar ([1] : List (Fin 2)) 2 c' default]
      rfl
    have h1 := F_R_b0_to_D100 k (([1] : List (Fin 2)) ^ (c' + 2) +> default)
    rw [hc] at h1
    have h2 := D100_0_11 k (([1] : List (Fin 2)) ^ c' +> default)
    exact closes_of_in_ps (zPt h1 h2) (in_ps_A 1 (k + 1) c')
lemma closes_A_b1 (k c : Nat) : Closes (cfg_A 1 k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 1 k
  · exact closes_of_stepPlus (zPt (F_R_b1_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 (k +
          1)))
      (closes_C_bounce_ones 0 (2 * (k + 1) + 5))
  · have hc : (([1] : List (Fin 2)) ^ (c' + 2) +> (default : ListBlank (Fin 2))) =
        [1, 1] +> (([1] : List (Fin 2)) ^ c' +> default) := by
      rw [Nat.add_comm c' 2, zPar ([1] : List (Fin 2)) 2 c' default]
      rfl
    have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ (c' + 2) +> default)
    rw [hc] at h1
    have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ c' +> default)
    exact closes_of_in_ps (zPt h1 h2) (in_ps_A 1 (k + 2) c')
lemma closes_A_b3 (b k c : Nat) : Closes (cfg_A (b + 3) k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 (b + 3) k
  · have h1 := F_R_b3_to_D100 b k ([1] +> default)
    have h2 := D100_one_to_C_bounce (b + 1) k
    exact closes_of_stepPlus (zPt h1 h2) (closes_C_bounce_ones (b + 1) (2 * k + 5))
  · have hc : (([1] : List (Fin 2)) ^ (c' + 2) +> (default : ListBlank (Fin 2))) =
        [1, 1] +> (([1] : List (Fin 2)) ^ c' +> default) := by
      rw [Nat.add_comm c' 2, zPar ([1] : List (Fin 2)) 2 c' default]
      rfl
    have h1 := F_R_b3_to_D100 b k (([1] : List (Fin 2)) ^ (c' + 2) +> default)
    rw [hc] at h1
    have h2 := D100_succ_11 b k (([1] : List (Fin 2)) ^ c' +> default)
    exact closes_of_in_ps (zPt h1 h2) (in_ps_A (b + 1) (k + 2) c')
lemma step_F_R_b2_one (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 2 k ([1] +> r)) [target]⊢⁺
    (F_R 5 0 (([0, 1] : List (Fin 2)) ^ k +> r)) := by
  unfold F_R
  simp only [zPz, zLan]
  have h1 := shift_FA_left_0082 k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) ([0,
          1] +> r)
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{F}}>
      ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([0, 1] +> r))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{F}}>
        ([0, 0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
    rw [zPa1 ([0, 1] : List (Fin 2)) k r,
      zPsr ([0, 1] : List (Fin 2)) k r]
    dsimp [HPow.hPow, listNatRepeat, ListBlank.append]
    execute
  exact zSpp h1 h2
lemma step_E_01_to_F_R (b : Nat) (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) {{E}}> ([0, 1] +> r))
    [target]⊢⁺
    (F_R b 0 r) := by
  unfold F_R
  simp only [zPz, zLan]
  dsimp [ListBlank.append]
  execute
lemma closes_E_01_tail (b m c : Nat)
    (ih : ∀ m' < m + 1, ∀ p k, Closes (F_R (2 * p + 1) k (([0, 1] : List (Fin 2)) ^ m' +> (([1] :
            List (Fin 2)) ^ c +> default)))) :
    Closes (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1)) {{E}}>
      (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  rcases m with _ | m'
  · simp only [zPz, zLan]
    have h1 := shift_E_ones_0082 c ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b
            + 1)) default
    rw [<- zPl default ([1] : List (Fin 2)) (2 * b + 1) c] at h1
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1 + c)) {{E}}>
            default) =
        E_0082 0 (2 * b + 1 + c) := rfl
    rw [h_eq] at h1
    exact closes_of_stepStar h1 (closes_E 0 (2 * b + 1 + c))
  · rw [zPsr ([0, 1] : List (Fin 2)) m']
    have h1 := step_E_01_to_F_R (2 * b + 1) (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2))
            ^ c +> default))
    exact closes_of_stepPlus h1 (ih m' (by omega) b 0)
lemma closes_odd_even_ones (n : Nat) (r : ListBlank (Fin 2))
    (h_base : ∀ p k, Closes (F_R (2 * p + 1) k r)) :
    ∀ p k, Closes (F_R (2 * p + 1) k (([1] : List (Fin 2)) ^ (2 * n) +> r)) := by
  induction n with
  | zero =>
    intro p k
    simp only [Nat.mul_zero, zPz, zLan]
    exact h_base p k
  | succ n ih =>
    intro p k
    have hn : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [hn, zPar ([1] : List (Fin 2)) 2 (2 * n) r]
    rcases p with _ | p'
    · have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +>
            r))
      have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact closes_of_stepPlus (zPt h1 h2) (ih 0 (k + 2))
    · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
      rw [hp]
      have h1 := F_R_b3_to_D100 (2 * p') k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2
              * n) +> r))
      have h2 := D100_succ_11 (2 * p') k (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact closes_of_stepPlus (zPt h1 h2) (ih p' (k + 2))
lemma closes_odd_m (m : Nat) (c : Nat) :
    ∀ p k, Closes (F_R (2 * p + 1) k (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +>
            default))) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro p k
    rcases m with _ | m'
    · simp only [zPz, zLan, <- cfg_A_eq_F_R]
      rcases p with _ | p'
      · exact closes_A_b1 k c
      · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
        rw [hp]
        exact closes_A_b3 (2 * p') k c
    · rw [zPsr ([0, 1] : List (Fin 2)) m']
      set r' := (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default))
      rcases p with _ | _ | p''
      · have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 0 (k + 1) r'
        have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
        have h4 := shift_E_ones_0082 (2 * (k + 1) + 4) ((default : ListBlank (Fin 2)) <+ ([1] :
                List (Fin 2)) ^ 3) r'
        rw [<- zPl default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
        have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact closes_of_stepPlus
          (zPsp (zPt (zPt h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 1 k r'
        have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        have h4 := shift_E_ones_0082 (2 * k + 4) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin
                2)) ^ 5) r'
        rw [<- zPl default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
        have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact closes_of_stepPlus
          (zPsp (zPt (zPt h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have hp : 2 * (p'' + 2) + 1 = (2 * p'' + 2) + 3 := by omega
        rw [hp]
        have h1 := F_R_b3_to_D100 (2 * p'' + 2) k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce (2 * p'' + 3) k r'
        have h3 := C_bounce_3 (2 * p'') (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        rw [<- zPar ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
        have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
        rw [hk] at h3
        exact closes_of_stepPlus (zPt (zPt h1 h2) h3)
          (closes_odd_even_ones (k + 3) r' (ih m' (by omega)) p'' 0)
lemma closes_A_b2 (k c : Nat) : Closes (cfg_A 2 k c) := by
  rcases c with _ | c'
  · exact closes_A_c0 2 k
  · rw [cfg_A_eq_F_R, zPsr ([1] : List (Fin 2)) c' default]
    have h1 := step_F_R_b2_one k (([1] : List (Fin 2)) ^ c' +> default)
    exact closes_of_stepPlus h1 (closes_odd_m k c' 2 0)
lemma closes_A_all (b k c : Nat) : Closes (cfg_A b k c) := by
  rcases b with _ | _ | _ | b'
  · exact closes_A_b0 k c
  · exact closes_A_b1 k c
  · exact closes_A_b2 k c
  · exact closes_A_b3 b' k c


lemma closes_A_all_of_in_ps (cfg : Cfg (Fin 2) (Fin 6)) (h_in : IsInPatternSet ps cfg) :
    Closes cfg := by
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_A]
  exact closes_A_all (vars 0) (vars 1) (vars 2)

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 5 0 2, init_reaches_A_502, in_ps_A 5 0 2⟩, ?_⟩
  intro cfg h_in
  exact closes_A_all_of_in_ps cfg h_in

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE
