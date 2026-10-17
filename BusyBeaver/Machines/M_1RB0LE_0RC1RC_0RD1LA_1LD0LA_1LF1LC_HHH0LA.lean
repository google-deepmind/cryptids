/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA`.

## Collatz-like Acceleration Rules
The canonical configuration is D_cfg(a, b, c, d).
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---0LA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

notation:67 s:67 " << " a:68 => ListBlank.cons a s
infixr:67 " >> " => ListBlank.cons
notation:67 s:67 " <+ " l:68 => ListBlank.append l s
infixr:67 " +> " => ListBlank.append
notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

notation3 c₁ " [" M "]⊢ " c₂ => step M c₁ = some c₂
notation3 c₁ " [" M "]⊢^{" n "} " c₂ => multiStep M c₁ n = some c₂
notation3 c₁ " [" M "]⊢* " c₂ => ReachesStar M c₁ c₂
notation3 c₁ " [" M "]⊢⁺ " c₂ => ReachesPlus M c₁ c₂


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[simp] lemma zMz (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 0 = some config := rfl
@[simp] lemma zMo (M : Machine Γ Λ) (config : Cfg Γ Λ) : multiStep M config 1 = step M config := rfl
@[simp] lemma zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  exact multiStep_succ' M config n
@[simp] lemma zPz (l : List (Fin 2)) : l ^ (0 : Nat) = [] := rfl
@[simp] lemma zPsl (l : List (Fin 2)) (n : Nat) : l ^ (n + 1) = l ++ (l ^ n) := rfl
@[simp] lemma zCal (x : Fin 2) (xs ys : List (Fin 2)) : (x :: xs) ++ ys = x :: (xs ++ ys) := rfl
@[simp] lemma zAnl (l : List (Fin 2)) : l ++ [] = l := List.append_nil l
@[simp] lemma zLan (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma zLac (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) : (x :: xs) +> b = x
    >> (xs +> b) := rfl
@[simp] lemma zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma zDh : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma zDt : (default : ListBlank (Fin 2)).tail = default := rfl
omit [Inhabited Γ] in
@[simp]
theorem zLpa (l : List Γ) (n m : Nat) : l^(n + m) = l^n ++ l^m := by
  dsimp [HPow.hPow]
  rw [List.replicate_add, List.flatten_append]

omit [Inhabited Γ] in
theorem zLpc (l : List Γ) (n m : Nat) : l^n ++ l^m = l^m ++ l^n := by
  rw [<- zLpa, add_comm, zLpa]
lemma zLaa (s : ListBlank Γ) (l₁ l₂ : List Γ) :
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
  rw [zLpa]
  have h : u^1 = u := by dsimp [HPow.hPow]; simp
  rw [h]
lemma zPar (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [zLpa, <- zLaa]
lemma zPsr (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [zPsl, <- zLaa]
lemma zPl (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [zLaa, <- zLpa, add_comm]
lemma split_111_succ (b : Nat) (l_0 : ListBlank (Fin 2)) :
    l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1) =
    ((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [zPz, zPsl, zAnl, zLaa]
    rfl
  | succ b ih =>
    have h1 : l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1 + 1) =
        (l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [zPl l_0 ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [h1, ih l_0]
    have h2 : ((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [1, 1, 1]) =
        (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1, 1, 1]) <+ [1] := by
      simp only [zLaa]
      rfl
    rw [h2, <- zPsr ([1, 1, 1] : List (Fin 2)) b]
lemma comm_1_111 (b : Nat) (l_0 : ListBlank (Fin 2)) :
    (l_0 <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b =
    (l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [zPz, zLan]
  | succ b ih =>
    rw [zPl (l_0 <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1, ih l_0]
    have h1 : (((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) =
        ((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [1] := by
      simp only [zPsl, zPz, zAnl, zLaa]
      rfl
    rw [h1, <- zPl l_0 ([1, 1, 1] : List (Fin 2)) b 1]
lemma zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
lemma step_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1, zSm tm c_1 c_2 h⟩
lemma zSp2 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, zSm tm c_1 c_2 h⟩
lemma zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]
lemma zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 c_3 : Cfg Γ Λ) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [zMa, h₁]; simp [h₂]
lemma zSt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 : Cfg Γ Λ} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
lemma zPsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zSpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le m_pos (Nat.le_add_left m n), zMt tm c_1 c_2 c_3 n m hn hm⟩
lemma zPt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 :=
  zPsp h₁ (zPs h₂)
lemma zSsp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c_1 c_2 c_3 : Cfg Γ Λ}
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
      (any_goals (first | finish | step)) <;> (any_goals (first | finish | step)) <;> (any_goals
      (first | finish | step)))
macro "execute" : tactic =>
  `(tactic| execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5 <;> execute5)
macro "execute55" : tactic =>
  `(tactic| execute <;> execute5 <;> execute5 <;> execute5 <;> execute5)
macro "simptape" : tactic =>
  `(tactic| simp only [zPsl, zPz, zCal, List.nil_append, zAnl, zLac, zLan, zZcd,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, zDh, zDt])
lemma shift_A_left_111 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} r) [target]⊢*
    (l <{{A}} (([1, 1, 0] : List (Fin 2))^k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [1, 1, 1]) <{{A}} r)
        [target]⊢⁺
        ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) := by
      simptape; execute
    have h2 := ih l (([1, 1, 0] : List (Fin 2)) +> r)
    have h_comb : (([1, 1, 0] : List (Fin 2))^k +> ([1, 1, 0] +> r)) =
        (([1, 1, 0] : List (Fin 2))^(k + 1) +> r) := by
      rw [zLaa, zLp1]
    rw [h_comb] at h2
    exact zPs (zPsp h1 h2)
lemma shift_D_right_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : ((l <+ [0]) {{D}}> ([1, 0] +> (([1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [0, 1]) <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) := by
      simptape; execute
    have h2 := ih (l <+ [0, 1]) r
    have h_comb : ((l <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^k) =
        (l <+ ([0, 1] : List (Fin 2))^(k + 1)) := by
      rw [zLaa, zLp1]
    rw [h_comb] at h2
    exact zPs (zPsp h1 h2)
lemma shift_D_right_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsr]
    have h1 : ((l <+ [0]) {{D}}> ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [1, 1, 1]) <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) := by
      simptape; execute
    have h2 := ih (l <+ [1, 1, 1]) r
    have h_comb : ((l <+ [1, 1, 1]) <+ ([1, 1, 1] : List (Fin 2))^k) =
        (l <+ ([1, 1, 1] : List (Fin 2))^(k + 1)) := by
      rw [zLaa, zLp1]
    rw [h_comb] at h2
    exact zPs (zPsp h1 h2)
lemma shift_A_left_01_with_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) [target]⊢*
    (l <{{A}} ([1, 1, 0] +> (([1, 0] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [zPz, zLan]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [zPsl, <- zLaa]
    have h1 : (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0, 1]) <{{A}} ([1, 1, 0] +> r))
        [target]⊢⁺
        ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> ([1, 0] +> r))) := by
      simptape; execute
    have h2 := ih l ([1, 0] +> r)
    have h_comb : (([1, 0] : List (Fin 2))^k +> ([1, 0] +> r)) =
        (([1, 0] : List (Fin 2))^(k + 1) +> r) := by
      rw [zLaa, zLp1]
    rw [h_comb] at h2
    exact zPs (zPsp h1 h2)
lemma bounce_A_left_with_110 (r : ListBlank (Fin 2)) :
    (default <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^2 +> r)) := by
  simptape; execute
lemma drain_A_left_01_with_110 (a : Nat) (r : ListBlank (Fin 2)) :
    ((default <+ ([0, 1] : List (Fin 2))^a) <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> r)) := by
  have h1 := shift_A_left_01_with_110 a default r
  have h2 := bounce_A_left_with_110 (([1, 0] : List (Fin 2))^a +> r)
  have h_eq : (([1, 0] : List (Fin 2))^2 +> (([1, 0] : List (Fin 2))^a +> r)) =
      (([1, 0] : List (Fin 2))^(a + 2) +> r) := by
    rw [<- zPar ([1, 0] : List (Fin 2)) 2 a r, Nat.add_comm]
  rw [h_eq] at h2
  exact zSpp h1 h2
lemma drain_A_left_111_01_with_110 (a b : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}} ([1, 1, 0]
        +> r))
    [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> (([1, 1, 0] : List (Fin 2))^b +> r))) := by
  have h1 := shift_A_left_111 b (default <+ ([0, 1] : List (Fin 2))^a) ([1, 1, 0] +> r)
  have h_eq : (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> r)) =
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> r)) := by
    have h_l : (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> r)) =
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> r) := by
      rw [zLaa, zLp1]
    rw [h_l, zPsr]
  rw [h_eq] at h1
  exact zSpp h1 (drain_A_left_01_with_110 a (([1, 1, 0] : List (Fin 2))^b +> r))
lemma roundtrip_D_110_cap0 (b d : Nat) (l_0 : ListBlank (Fin 2)) :
    ((l_0 <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d
        +> default))))
    [target]⊢⁺
    ((l_0 <+ [1, 1]) <{{A}} (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d +
        2) +> default)))) := by
  have h1 := shift_D_right_110 (b + 1) l_0 ([0] +> (([1] : List (Fin 2))^d +> default))
  rw [split_111_succ b l_0] at h1
  have h2 : (((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [0]) {{D}}>
      ([0] +> (([1] : List (Fin 2))^d +> default)))
      [target]⊢⁺
      (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, zPar ([1] : List (Fin 2)) 2 d]
      rfl
    rw [hd]
    simptape; execute
  have h3 := shift_A_left_111 b (l_0 <+ [1, 1]) ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))
  exact zSpp h1 (zPsp h2 h3)
def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left  := .default
    head  := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.rep [0] 2 (.rep [1] 3 .default))) }
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .not (.ge_const 2 2))]
def D_cfg (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default {{D}}>
    (([1, 0] : List (Fin 2))^a +>
      (([1, 1, 0] : List (Fin 2))^b +>
        (([0] : List (Fin 2))^c +>
          (([1] : List (Fin 2))^d +> default))))
lemma eval_pat_D (vars : Nat -> Nat) :
    evalTapePattern pat_D vars = D_cfg (vars 0) (vars 1) (vars 2) (vars 3) := by
  rfl
lemma in_ps_D (a b c d : Nat) (hc : c <= 1) : IsInPatternSet ps (D_cfg a b c d) := by
  refine ⟨(pat_D, .not (.ge_const 2 2)), by simp [ps],
    fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0, rfl, ?_⟩
  simp only [evalVarCond]
  omega
def Closes (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg', (cfg [target]⊢⁺ cfg') /\
          (IsInPatternSet ps cfg' \/ (step target cfg').isNone)
lemma closes_of_stepPlus {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢⁺ c_2) (h₂ : Closes c_2) : Closes c_1 := by
  obtain ⟨c_3, h₂₃, h₃⟩ := h₂
  exact ⟨c_3, zPt h₁ h₂₃, h₃⟩
lemma closes_of_stepStar {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢* c_2) (h₂ : Closes c_2) : Closes c_1 := by
  obtain ⟨c_3, h₂₃, h₃⟩ := h₂
  exact ⟨c_3, zSpp h₁ h₂₃, h₃⟩
lemma closes_of_in_ps {c_1 : Cfg (Fin 2) (Fin 6)} {a b c d : Nat}
    (h₁ : c_1 [target]⊢⁺ D_cfg a b c d) (hc : c <= 1) : Closes c_1 :=
  ⟨D_cfg a b c d, h₁, Or.inl (in_ps_D a b c d hc)⟩
lemma closes_of_halt {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢⁺ c_2) (h₂ : (step target c_2).isNone) : Closes c_1 :=
  ⟨c_2, h₁, Or.inr h₂⟩
def H_mid (a b m : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0]) {{D}}>
    (([1] : List (Fin 2))^m +> default)
lemma closes_H_mid_a0_m1 (b : Nat) : Closes (H_mid 0 (b + 1) 1) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b
      + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      ((((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        ([0] +> (([1] : List (Fin 2))^3 +> default)))) := by
    rw [zPl (default <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1]
    simptape; execute
  have h2 := shift_A_left_111 (b + 1) (default <+ [1]) ([0] +> (([1] : List (Fin 2))^3 +> default))
  have h3 : (((default <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
      [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin
          2))^3 +> default))))) := by
    simptape; execute
  refine closes_of_halt (zPt (zPsp h1 h2) h3) ?_
  rfl
lemma closes_H_mid_asucc_m1 (a b : Nat) : Closes (H_mid (a + 1) (b + 1) 1) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin
      2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
          1)) <{{A}}
        ([0] +> (([1] : List (Fin 2))^3 +> default))) := by
    rw [zPl ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1]
    simptape; execute
  have h2 := shift_A_left_111 (b + 1) ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1])
    ([0] +> (([1] : List (Fin 2))^3 +> default))
  have h12 := zPsp h1 h2
  rcases a with _ | a'
  · have h3 : ((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
        [target]⊢⁺
        ((((default <+ [1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
              := by
      rw [zPsr ([1, 1, 0] : List (Fin 2)) b]
      simptape; execute
    have h4 := roundtrip_D_110_cap0 b 3 (default <+ [1, 1, 1])
    have h5 : ((((default <+ [1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^5 +> default)))))
        [target]⊢⁺ D_cfg 1 (b + 1) 1 5 := by
      unfold D_cfg
      rw [zPsr ([1, 1, 0] : List (Fin 2)) b]
      simptape; execute
    exact closes_of_in_ps (zPt h12 (zPt h3 (zPt h4 h5))) (by decide)
  · have h3 : ((((default <+ ([0, 1] : List (Fin 2))^(a' + 2)) <+ [1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
        [target]⊢⁺
        (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^3 +> default)))))
              := by
      rw [zPl default ([0, 1] : List (Fin 2)) a' 2]
      rw [zPsr ([1, 1, 0] : List (Fin 2)) b]
      simptape; execute
    have h4 := roundtrip_D_110_cap0 b 3 ((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1])
    have h5 : (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^5 +> default)))))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] :
              List (Fin 2))^5 +> default)))))) := by
      rw [zPsr ([1, 1, 0] : List (Fin 2)) b]
      simptape; execute
    have h6 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^5
          +> default))))
    exact closes_of_in_ps (zPt h12 (zPt h3 (zPt h4 (zPt h5 h6)))) (by decide)
lemma closes_H_mid_m2 (a b : Nat) : Closes (H_mid a (b + 1) 2) := by
  unfold H_mid
  rw [comm_1_111 (b + 1) (default <+ ([0, 1] : List (Fin 2))^a)]
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+
      [1]) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^2 +> default))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default)))) := by
    simptape; execute
  have h2 := drain_A_left_111_01_with_110 a (b + 1)
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
  exact closes_of_in_ps (zPt h1 h2) (by decide)
lemma closes_H_mid_a0_m3 (b m : Nat) : Closes (H_mid 0 (b + 1) (m + 3)) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b
      + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default)))
      [target]⊢⁺
      ((((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default))) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, zPar ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : (default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2) =
        ((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [zPl (default <+ [1]) ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [hm, hb, zPsr ([1] : List (Fin 2)) m]
    simptape; execute
  have h2 := shift_A_left_111 (b + 2) (default <+ [1]) (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))))
      [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m
          + 1) +> default)))) := by
    simptape; execute
  refine closes_of_halt (zPt (zPsp h1 h2) h3) ?_
  rfl
lemma step_H_mid_a1_m3_prefix (b m : Nat) :
    (H_mid 1 (b + 1) (m + 3)) [target]⊢⁺
    (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 1) +> default)) := by
  unfold H_mid
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
      1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2))
          <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, zPar ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
        2) =
        (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1))
            <+ [1, 1, 1] := by
      rw [zPl ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      rfl
    rw [hm, hb, zPsr ([1] : List (Fin 2)) m]
    simptape; execute
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0]) {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [zPsr ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simptape; execute
  have h4 := shift_D_right_110 (b + 2) (default <+ ([1, 1, 1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- zPl default ([1, 1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact zPt (zPsp h1 h2) (zPsp h3 h4)
lemma closes_H_mid_a1_m3 (b m : Nat) : Closes (H_mid 1 (b + 1) (m + 3)) := by
  have h_pref := step_H_mid_a1_m3_prefix b m
  rcases m with _ | _ | m'
  · have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^1 +> default))
        [target]⊢⁺
        ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
      rw [zPl default ([1, 1, 1] : List (Fin 2)) (b + 2) 1]
      simptape; execute
    have h2 := drain_A_left_111_01_with_110 0 (b + 2)
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
    exact closes_of_in_ps (zPt h_pref (zPt h1 h2)) (by decide)
  · have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^2 +> default))
        [target]⊢⁺
        (((default <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
          (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))) := by
      rw [split_111_succ (b + 2) default]
      rw [zPl (default <+ [1, 1]) ([1, 1, 1] : List (Fin 2)) (b + 2) 1]
      simptape; execute
    have h2 := shift_A_left_111 (b + 3) (default <+ [1, 1])
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
    have h3 : ((default <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 3) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2
            +> default))))
        [target]⊢⁺ D_cfg 1 (b + 3) 1 2 := by
      unfold D_cfg
      simptape; execute
    exact closes_of_in_ps (zPt h_pref (zPt (zPsp h1 h2) h3)) (by decide)
  · have h1 : (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^(m' + 3) +> default))
        [target]⊢⁺
        ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default))))
              := by
      have hm : (([1] : List (Fin 2))^(m' + 3) +> default) =
          ([1, 1, 1] +> (([1] : List (Fin 2))^m' +> default)) := by
        rw [Nat.add_comm m' 3, zPar ([1] : List (Fin 2)) 3 m']
        rfl
      rw [hm, zPsr ([1] : List (Fin 2)) m']
      simptape; execute
    have h2 := drain_A_left_111_01_with_110 0 (b + 3)
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default))
    exact closes_of_in_ps (zPt h_pref (zPt h1 h2)) (by decide)
lemma step_H_mid_asucc2_m3 (a b m : Nat) :
    (H_mid (a + 2) (b + 1) (m + 3)) [target]⊢⁺ (H_mid a (b + 3) (m + 1)) := by
  unfold H_mid
  have h1 : (((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
      2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
          2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, zPar ([1] : List (Fin 2)) 3 m]
      rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
        2))^(b + 2) =
        (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
            1)) <+ [1, 1, 1] := by
      rw [zPl ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) ([1, 1, 1] : List (Fin 2)) (b
          + 1) 1]
      rfl
    rw [hm, hb, zPsr ([1] : List (Fin 2)) m]
    simptape; execute
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0])
          {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [zPl default ([0, 1] : List (Fin 2)) a 2]
    rw [zPsr ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simptape; execute
  have h4 := shift_D_right_110 (b + 2) (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1,
      1, 1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+
      ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- zPl ((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) ([1, 1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact zPt (zPsp h1 h2) (zPsp h3 h4)
lemma closes_H_mid (a : Nat) : ∀ b m, Closes (H_mid a (b + 1) (m + 1)) := by
  induction a using Nat.strong_induction_on with
  | h a ih =>
    intro b m
    rcases m with _ | _ | m'
    · rcases a with _ | a'
      · exact closes_H_mid_a0_m1 b
      · exact closes_H_mid_asucc_m1 a' b
    · exact closes_H_mid_m2 a b
    · rcases a with _ | _ | a'
      · exact closes_H_mid_a0_m3 b m'
      · exact closes_H_mid_a1_m3 b m'
      · exact closes_of_stepPlus (step_H_mid_asucc2_m3 a' b m') (ih a' (by omega) (b + 2) m')
def B_mid (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^k) {{B}}>
    ([0, 0] +> (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^d +> default)))))
def A_rem (a k q m : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^k) <{{A}}
    (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m +> default))))
lemma step_B_mid_bsucc (a k b d : Nat) :
    (B_mid a (k + 1) (b + 1) d) [target]⊢⁺ (B_mid a (k + 2) b (d + 2)) := by
  unfold B_mid
  have h1 : (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) {{B}}>
      ([0, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d +>
          default)))))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0]) <+ [0])
          {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> ([0] +> (([1] : List (Fin 2))^d +> default)))) := by
    simptape; execute
  have h2 := roundtrip_D_110_cap0 b d
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0])
  have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0])
      <+ [1, 1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 2)) {{B}}>
        ([0, 0] +> (([1, 1, 0] : List (Fin 2))^b +> ([0] +> (([1] : List (Fin 2))^(d + 2) +>
            default))))) := by
    rw [zPl (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2)) (k + 1) 1]
    simptape; execute
  exact zPt h1 (zPt h2 h3)
lemma step_B_mid_bsucc_star (b : Nat) : ∀ a k d,
    (B_mid a (k + 1) b d) [target]⊢* (B_mid a (k + 1 + b) 0 (d + 2 * b)) := by
  induction b with
  | zero =>
    intro a k d
    simp only [Nat.add_zero, Nat.mul_zero]
    exact ⟨0, rfl⟩
  | succ b ih =>
    intro a k d
    have h1 := zPs (step_B_mid_bsucc a k b d)
    have h2 := ih a (k + 1) (d + 2)
    have hk : k + 1 + 1 + b = k + 1 + (b + 1) := by omega
    have hd : d + 2 + 2 * b = d + 2 * (b + 1) := by omega
    rw [hk, hd] at h2
    exact zSt h1 h2
lemma step_B_mid_ksucc2_b0 (a k d : Nat) :
    (B_mid a (k + 2) 0 d) [target]⊢⁺ (A_rem a (k + 1) 0 (d + 3)) := by
  unfold B_mid A_rem
  rw [zPl (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2)) (k + 1) 1]
  have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
      ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 3, zPar ([1] : List (Fin 2)) 3 d]
    rfl
  rw [hd]
  simptape; execute
lemma step_A_rem_ksucc3 (a k q m : Nat) :
    (A_rem a (k + 3) q m) [target]⊢⁺ (A_rem a k (q + 1) m) := by
  unfold A_rem
  rw [zPl (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2)) k 3]
  have hq : (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default))) =
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m +>
          default)))) := by
    rw [zPsr]
  rw [hq]
  simptape; execute
lemma closes_A_rem_k0_qsucc (a q m : Nat) : Closes (A_rem a 0 (q + 1) m) := by
  have h1 := drain_A_left_01_with_110 a
    ((([1, 1, 0] : List (Fin 2))^q +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^m +>
        default))))
  have h_eq : (((default <+ ([0, 1] : List (Fin 2))^a) <{{A}}
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^m +> default)))))) =
      A_rem a 0 (q + 1) m := by
    unfold A_rem
    rw [zPsr ([1, 1, 0] : List (Fin 2)) q]
    simptape
  rw [h_eq] at h1
  exact closes_of_in_ps h1 (by decide)
lemma closes_A_rem_a0_k1 (q m : Nat) : Closes (A_rem 0 1 q m) := by
  have h1 : (A_rem 0 1 q m) [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^m
          +> default))))) := by
    unfold A_rem
    simptape; execute
  refine closes_of_halt h1 ?_
  rfl
lemma closes_A_rem_asucc_k1_q0 (a m : Nat) : Closes (A_rem (a + 1) 1 0 m) := by
  rcases a with _ | a'
  · have h1 : (A_rem 1 1 0 m) [target]⊢⁺ D_cfg 1 0 1 (m + 2) := by
      unfold A_rem D_cfg
      have hm : (([1] : List (Fin 2))^(m + 2) +> default) =
          ([1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
        rw [Nat.add_comm m 2, zPar ([1] : List (Fin 2)) 2 m]
        rfl
      rw [hm]
      simptape; execute
    exact closes_of_in_ps h1 (by decide)
  · have h1 : (A_rem (a' + 2) 1 0 m) [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^1 +> (([1] : List
              (Fin 2))^(m + 2) +> default)))))) := by
      unfold A_rem
      rw [zPl default ([0, 1] : List (Fin 2)) a' 2]
      have hm : (([1] : List (Fin 2))^(m + 2) +> default) =
          ([1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
        rw [Nat.add_comm m 2, zPar ([1] : List (Fin 2)) 2 m]
        rfl
      rw [hm]
      simptape; execute
    have h2 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^(m + 2)
          +> default))))
    exact closes_of_in_ps (zPt h1 h2) (by decide)
lemma closes_A_rem_asucc_k1_qsucc (a q m : Nat) : Closes (A_rem (a + 1) 1 (q + 1) m) := by
  rcases a with _ | a'
  · have h1 : (A_rem 1 1 (q + 1) m) [target]⊢⁺
        ((((default <+ [1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default)))))
              := by
      unfold A_rem
      rw [zPsr ([1, 1, 0] : List (Fin 2)) q]
      simptape; execute
    have h2 := roundtrip_D_110_cap0 q m (default <+ [1, 1, 1])
    have h3 : ((((default <+ [1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^(m + 2) +> default)))))
        [target]⊢⁺ D_cfg 1 (q + 1) 1 (m + 2) := by
      unfold D_cfg
      rw [zPsr ([1, 1, 0] : List (Fin 2)) q]
      simptape; execute
    exact closes_of_in_ps (zPt h1 (zPt h2 h3)) (by decide)
  · have h1 : (A_rem (a' + 2) 1 (q + 1) m) [target]⊢⁺
        (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^(q + 1) +> ([0] +> (([1] : List (Fin 2))^m +> default)))))
              := by
      unfold A_rem
      rw [zPl default ([0, 1] : List (Fin 2)) a' 2]
      rw [zPsr ([1, 1, 0] : List (Fin 2)) q]
      simptape; execute
    have h2 := roundtrip_D_110_cap0 q m ((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1])
    have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1, 1, 1, 1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^q +> ([0] +> (([1] : List (Fin 2))^(m + 2) +> default)))))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a') <{{A}}
          ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^(q + 1) +> (([0] : List (Fin 2))^1 +> (([1] :
              List (Fin 2))^(m + 2) +> default)))))) := by
      rw [zPsr ([1, 1, 0] : List (Fin 2)) q]
      simptape; execute
    have h4 := drain_A_left_01_with_110 a'
      ((([1, 1, 0] : List (Fin 2))^(q + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^(m
          + 2) +> default))))
    exact closes_of_in_ps (zPt h1 (zPt h2 (zPt h3 h4))) (by decide)
lemma closes_A_rem_a0_k2 (q m : Nat) : Closes (A_rem 0 2 q m) := by
  have h1 : (A_rem 0 2 q m) [target]⊢⁺ D_cfg 1 q 1 m := by
    unfold A_rem D_cfg
    simptape; execute
  exact closes_of_in_ps h1 (by decide)
lemma step_A_rem_asucc_k2 (a q m : Nat) :
    (A_rem (a + 1) 2 q m) [target]⊢⁺ (B_mid a 2 q m) := by
  unfold A_rem B_mid
  rw [zPl default ([0, 1] : List (Fin 2)) a 1]
  simptape; execute
lemma step_A_rem_asucc_k2_to_A_rem (a q m : Nat) :
    (A_rem (a + 1) 2 q m) [target]⊢⁺ (A_rem a (q + 1) 0 (m + 2 * q + 3)) := by
  have h1 := step_A_rem_asucc_k2 a q m
  have h2 := step_B_mid_bsucc_star q a 1 m
  have hq : 1 + 1 + q = q + 2 := by omega
  rw [hq] at h2
  have h3 := step_B_mid_ksucc2_b0 a q (m + 2 * q)
  exact zPt (zPsp h1 h2) h3
lemma closes_A_rem (a : Nat) : ∀ k q m, k + q >= 1 -> Closes (A_rem a k q m) := by
  induction a using Nat.strong_induction_on with
  | h a iha =>
    intro k
    induction k using Nat.strong_induction_on with
    | h k ihk =>
      intro q m hkq
      rcases k with _ | _ | _ | k'
      · rcases q with _ | q'
        · omega
        · exact closes_A_rem_k0_qsucc a q' m
      · rcases a with _ | a'
        · exact closes_A_rem_a0_k1 q m
        · rcases q with _ | q'
          · exact closes_A_rem_asucc_k1_q0 a' m
          · exact closes_A_rem_asucc_k1_qsucc a' q' m
      · rcases a with _ | a'
        · exact closes_A_rem_a0_k2 q m
        · exact closes_of_stepPlus (step_A_rem_asucc_k2_to_A_rem a' q m)
            (iha a' (by omega) (q + 1) 0 (m + 2 * q + 3) (by omega))
      · exact closes_of_stepPlus (step_A_rem_ksucc3 a k' q m)
          (ihk k' (by omega) (q + 1) m (by omega))
lemma closes_B_mid_a0_k1_b0 (d : Nat) : Closes (B_mid 0 1 0 d) := by
  have h1 : (B_mid 0 1 0 d) [target]⊢⁺ D_cfg 0 0 0 (d + 4) := by
    unfold B_mid D_cfg
    have hd : (([1] : List (Fin 2))^(d + 4) +> default) =
        ([1, 1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 4, zPar ([1] : List (Fin 2)) 4 d]
      rfl
    rw [hd]
    simptape; execute
  exact closes_of_in_ps h1 (by decide)
lemma closes_B_mid_a1_k1_b0 (d : Nat) : Closes (B_mid 1 1 0 d) := by
  have h1 : (B_mid 1 1 0 d) [target]⊢⁺
      (default <{{F}} ([1, 0, 1, 1, 0] +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    unfold B_mid
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, zPar ([1] : List (Fin 2)) 2 d]
      rfl
    rw [hd]
    simptape; execute
  refine closes_of_halt h1 ?_
  rfl
lemma closes_B_mid_a2_k1_b0 (d : Nat) : Closes (B_mid 2 1 0 d) := by
  rcases d with _ | d'
  · have h1 : (B_mid 2 1 0 0) [target]⊢⁺ D_cfg 1 2 1 2 := by
      unfold B_mid D_cfg
      simptape; execute55
    exact closes_of_in_ps h1 (by decide)
  · have h1 : (B_mid 2 1 0 (d' + 1)) [target]⊢⁺ D_cfg 2 2 0 (d' + 1) := by
      unfold B_mid D_cfg
      rw [zPsr ([1] : List (Fin 2)) d']
      simptape; execute55
    exact closes_of_in_ps h1 (by decide)
lemma step_B_mid_asucc3_k1_b0 (a d : Nat) :
    (B_mid (a + 3) 1 0 d) [target]⊢⁺ (H_mid a 2 (d + 2)) := by
  unfold B_mid H_mid
  rw [zPl default ([0, 1] : List (Fin 2)) a 3]
  have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
      ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 2, zPar ([1] : List (Fin 2)) 2 d]
    rfl
  rw [hd]
  simptape; execute
lemma closes_B_mid_b0 (k : Nat) : ∀ a d, Closes (B_mid a (k + 1) 0 d) := by
  intro a d
  rcases k with _ | k'
  · rcases a with _ | _ | _ | a''
    · exact closes_B_mid_a0_k1_b0 d
    · exact closes_B_mid_a1_k1_b0 d
    · exact closes_B_mid_a2_k1_b0 d
    · exact closes_of_stepPlus (step_B_mid_asucc3_k1_b0 a'' d) (closes_H_mid a'' 1 (d + 1))
  · exact closes_of_stepPlus (step_B_mid_ksucc2_b0 a k' d)
      (closes_A_rem a (k' + 1) 0 (d + 3) (by omega))
lemma closes_B_mid (b : Nat) : ∀ a k d, Closes (B_mid a (k + 1) b d) := by
  induction b with
  | zero =>
    intro a k d
    exact closes_B_mid_b0 k a d
  | succ b ih =>
    intro a k d
    exact closes_of_stepPlus (step_B_mid_bsucc a k b d) (ih a (k + 1) (d + 2))
lemma step_D_cfg_to_D_mid (a : Nat) (r : ListBlank (Fin 2)) :
    (default {{D}}> (([1, 0] : List (Fin 2))^a +> r)) [target]⊢*
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ [0]) {{D}}> r) := by
  have h := shift_D_right_10 a default r
  have h_def : (default <+ ([0] : List (Fin 2))) = default := by
    simptape
  rwa [h_def] at h
lemma closes_D_cfg_c1 (a b d : Nat) : Closes (D_cfg a b 1 d) := by
  rcases a with _ | a'
  · rcases b with _ | b'
    · have h1 : (D_cfg 0 0 1 d) [target]⊢⁺ (D_cfg 0 0 1 (d + 1)) := by
        unfold D_cfg
        rw [zPsr ([1] : List (Fin 2)) d]
        simptape; execute
      exact closes_of_in_ps h1 (by decide)
    · have h1 := roundtrip_D_110_cap0 b' d default
      have h_def : (default <+ ([0] : List (Fin 2))) = default := by simptape
      rw [h_def] at h1
      have h2 : ((default <+ [1, 1]) <{{A}}
          (([1, 1, 0] : List (Fin 2))^b' +> ([0] +> (([1] : List (Fin 2))^(d + 2) +> default))))
          [target]⊢⁺ D_cfg 1 b' 1 (d + 2) := by
        unfold D_cfg
        simptape; execute
      have h_start : ((default {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b' + 1) +> ([0] +> (([1] : List (Fin 2))^d +> default))))) =
          D_cfg 0 (b' + 1) 1 d := by
        unfold D_cfg; rfl
      rw [h_start] at h1
      exact closes_of_in_ps (zPt h1 h2) (by decide)
  · have h1 := step_D_cfg_to_D_mid a'
      ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^d +> default))))
    have h_start : (default {{D}}>
        (([1, 0] : List (Fin 2))^a' +> ([1, 0] +>
          (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^d +>
              default)))))) =
        D_cfg (a' + 1) b 1 d := by
      unfold D_cfg
      rw [zLaa, zLp1]
    rw [h_start] at h1
    have h2 : (((default <+ ([0, 1] : List (Fin 2))^a') <+ [0]) {{D}}>
        ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
            2))^d +> default)))))
        [target]⊢⁺ B_mid a' 1 b d := by
      unfold B_mid
      simptape; execute
    exact closes_of_stepStar h1 (closes_of_stepPlus h2 (closes_B_mid b a' 0 d))
lemma D_cfg_c0_d0_eq (a b : Nat) : D_cfg a b 0 0 = D_cfg a b 1 0 := by
  unfold D_cfg
  simptape
lemma D_cfg_c0_d2_eq (a b : Nat) : D_cfg a b 0 2 = D_cfg a (b + 1) 1 0 := by
  unfold D_cfg
  have h_b : (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
      2))^0 +> default))) =
      (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
          2))^0 +> default)))) := by
    rw [ <- zLp1 ([1, 1, 0] : List (Fin 2)) b, <- zLaa]
  rw [h_b]
  simptape
lemma closes_D_cfg_c0_d1 (a b : Nat) : Closes (D_cfg a b 0 1) := by
  rcases b with _ | b'
  · rcases a with _ | a'
    · have h1 : (D_cfg 0 0 0 1) [target]⊢⁺ (D_cfg 0 0 0 4) := by
        unfold D_cfg
        simptape; execute
      exact closes_of_in_ps h1 (by decide)
    · have h1 := step_D_cfg_to_D_mid (a' + 1)
        (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
            default)))
      have h_start : (default {{D}}>
          (([1, 0] : List (Fin 2))^(a' + 1) +>
            (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1
                +> default))))) =
          D_cfg (a' + 1) 0 0 1 := by
        unfold D_cfg; rfl
      rw [h_start] at h1
      have h2 : (((default <+ ([0, 1] : List (Fin 2))^(a' + 1)) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
              default))))
          [target]⊢⁺ B_mid (a' + 1) 1 0 0 := by
        unfold B_mid
        simptape; execute
      exact closes_of_stepStar h1 (closes_of_stepPlus h2 (closes_B_mid 0 (a' + 1) 0 0))
  · have h1 := step_D_cfg_to_D_mid a
      (([1, 1, 0] : List (Fin 2))^(b' + 1) +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1
          +> default)))
    have h2 := shift_D_right_110 (b' + 1) (default <+ ([0, 1] : List (Fin 2))^a)
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default))
    have h3 : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b' + 1))
        <+ [0]) {{D}}>
        (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default)))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b') <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
      rw [zPl (default <+ ([0, 1] : List (Fin 2))^a) ([1, 1, 1] : List (Fin 2)) b' 1]
      simptape; execute
    have h4 := drain_A_left_111_01_with_110 a b'
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
    exact closes_of_in_ps
      (zSpp (zSt h1 h2) (zPt h3 h4)) (by decide)
lemma closes_D_cfg_c0_d3 (a b d : Nat) : Closes (D_cfg a b 0 (d + 3)) := by
  have h1 := step_D_cfg_to_D_mid a
    (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +>
        default)))
  have h2 := shift_D_right_110 b (default <+ ([0, 1] : List (Fin 2))^a)
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default))
  have h3 : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0])
      {{D}}>
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default)))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default)))) := by
    have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 3, zPar ([1] : List (Fin 2)) 3 d]
      rfl
    rw [hd, zPsr ([1] : List (Fin 2)) d]
    simptape; execute
  have h4 := drain_A_left_111_01_with_110 a b
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default))
  exact closes_of_in_ps
    (zSpp (zSt h1 h2) (zPt h3 h4)) (by decide)
lemma closes_D_cfg (a b c d : Nat) (hc : c <= 1) : Closes (D_cfg a b c d) := by
  have hc_cases : c = 0 \/ c = 1 := by omega
  rcases hc_cases with rfl | rfl
  · rcases d with _ | _ | _ | d'
    · rw [D_cfg_c0_d0_eq]
      exact closes_D_cfg_c1 a b 0
    · exact closes_D_cfg_c0_d1 a b
    · rw [D_cfg_c0_d2_eq]
      exact closes_D_cfg_c1 a (b + 1) 0
    · exact closes_D_cfg_c0_d3 a b d'
  · exact closes_D_cfg_c1 a b d
theorem init_reaches_D :
    (init []) [target]⊢* (D_cfg 0 0 0 4) := by
  have h_init : (init []) [target]⊢⁺ (D_cfg 0 0 0 4) := by
    unfold init D_cfg
    simptape; execute
  exact zPs h_init

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  constructor
  · exact ⟨D_cfg 0 0 0 4, init_reaches_D, in_ps_D 0 0 0 4 (by decide)⟩
  · intro cfg h_in
    rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
    simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
    subst h_mem
    rw [eval_pat_D]
    simp only [evalVarCond] at h_cond
    exact closes_D_cfg (vars 0) (vars 1) (vars 2) (vars 3) (by omega)

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

end BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA

