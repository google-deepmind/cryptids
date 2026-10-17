/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC`

## Collatz-like Acceleration Rules
The canonical configuration is D_cfg(a, b, c, d).
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
    load_rle_machine% "1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_---1LC"

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


lemma multiStep_one_of_step {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
  {tm : Machine Γ Λ} {c_1 c_2 : Cfg Γ Λ} (h : step tm c_1 = some c_2) :
  multiStep tm c_1 1 = some c_2 := by simp [h]

lemma list_blank_append_pow_add (u : List (Fin 2)) (m n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (m + n)) +> r = (u ^ m) +> ((u ^ n) +> r) := by
  rw [list_pow_add, ListBlank.append_assoc]

lemma list_blank_append_pow_succ_left (u : List (Fin 2)) (n : Nat) (r : ListBlank (Fin 2)) :
    (u ^ (n + 1)) +> r = u +> ((u ^ n) +> r) := by
  rw [list_pow_succ, ListBlank.append_assoc]

lemma list_blank_append_pow_assoc_right (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [<- ListBlank.append_assoc, <- list_pow_add, Nat.add_comm m n]

lemma list_blank_append_pow_add_one (u : List (Fin 2)) (k : Nat) (r : ListBlank (Fin 2)) :
    (u ^ k) +> (u +> r) = (u ^ (k + 1)) +> r := by
  rw [<- ListBlank.append_assoc, list_pow_succ']

lemma list_blank_append_pow_add_one_left (l : ListBlank (Fin 2)) (u : List (Fin 2)) (k : Nat) :
    (l <+ u) <+ (u ^ k) = l <+ (u ^ (k + 1)) := by
  rw [<- ListBlank.append_assoc, list_pow_succ']
lemma split_111_succ (b : Nat) (l_0 : ListBlank (Fin 2)) :
    l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1) =
    ((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [list_pow_zero, list_pow_succ, List.append_nil, ListBlank.append]
    try rfl
  | succ b ih =>
    have h1 : l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1 + 1) =
        (l_0 <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [list_blank_append_pow_assoc_right l_0 ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      try rfl
    rw [h1, ih l_0]
    have h2 : ((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [1, 1, 1]) =
        (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1, 1, 1]) <+ [1] := by
      simp only [<- ListBlank.append_assoc]
      try rfl
    rw [h2, <- list_blank_append_pow_succ_left ([1, 1, 1] : List (Fin 2)) b (l_0 <+ [1, 1])]
lemma comm_1_111 (b : Nat) (l_0 : ListBlank (Fin 2)) :
    (l_0 <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b =
    (l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1] := by
  induction b generalizing l_0 with
  | zero =>
    simp only [list_pow_zero, ListBlank.append]
  | succ b ih =>
    rw [list_blank_append_pow_assoc_right (l_0 <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1, ih l_0]
    have h1 : (((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) =
        ((l_0 <+ ([1, 1, 1] : List (Fin 2))^b) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [1] := by
      simp only [list_pow_succ, list_pow_zero, List.append_nil]
      try rfl
    rw [h1, <- list_blank_append_pow_assoc_right l_0 ([1, 1, 1] : List (Fin 2)) b 1]
lemma step_stepStar {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c_1 c_2 : Cfg Γ Λ) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢* c_2 := ⟨1, multiStep_one_of_step h⟩
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)

lemma shift_A_left_111 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} r) [target]⊢*
    (l <{{A}} (([1, 1, 0] : List (Fin 2))^k +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_pow_succ, ListBlank.append_assoc]
    have h1 : (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [1, 1, 1]) <{{A}} r)
        [target]⊢⁺
        ((l <+ ([1, 1, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) := by
      simp only [ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := ih l (([1, 1, 0] : List (Fin 2)) +> r)
    rw [list_blank_append_pow_add_one ([1, 1, 0] : List (Fin 2)) k r] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
lemma shift_D_right_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_blank_append_pow_succ_left]
    have h1 : ((l <+ [0]) {{D}}> ([1, 0] +> (([1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [0, 1]) <+ [0]) {{D}}> (([1, 0] : List (Fin 2))^k +> r)) := by
      simp only [ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := ih (l <+ [0, 1]) r
    rw [list_blank_append_pow_add_one_left l ([0, 1] : List (Fin 2)) k] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
lemma shift_D_right_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) [target]⊢*
    (((l <+ ([1, 1, 1] : List (Fin 2))^k) <+ [0]) {{D}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_blank_append_pow_succ_left]
    have h1 : ((l <+ [0]) {{D}}> ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^k +> r)))
        [target]⊢⁺
        (((l <+ [1, 1, 1]) <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^k +> r)) := by
      simp only [ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := ih (l <+ [1, 1, 1]) r
    rw [list_blank_append_pow_add_one_left l ([1, 1, 1] : List (Fin 2)) k] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
lemma shift_A_left_01_with_110 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> r)) [target]⊢*
    (l <{{A}} ([1, 1, 0] +> (([1, 0] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append]
    exact ⟨0, rfl⟩
  | succ k ih =>
    rw [list_pow_succ, ListBlank.append_assoc]
    have h1 : (((l <+ ([0, 1] : List (Fin 2))^k) <+ [0, 1]) <{{A}} ([1, 1, 0] +> r))
        [target]⊢⁺
        ((l <+ ([0, 1] : List (Fin 2))^k) <{{A}} ([1, 1, 0] +> ([1, 0] +> r))) := by
      simp only [ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := ih l ([1, 0] +> r)
    rw [list_blank_append_pow_add_one ([1, 0] : List (Fin 2)) k r] at h2
    exact ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
lemma bounce_A_left_with_110 (r : ListBlank (Fin 2)) :
    (default <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^2 +> r)) := by
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, ListBlank.head_default,
    ListBlank.tail_default]
  bb_steps
  try rfl
lemma drain_A_left_01_with_110 (a : Nat) (r : ListBlank (Fin 2)) :
    ((default <+ ([0, 1] : List (Fin 2))^a) <{{A}} ([1, 1, 0] +> r)) [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> r)) := by
  have h1 := shift_A_left_01_with_110 a default r
  have h2 := bounce_A_left_with_110 (([1, 0] : List (Fin 2))^a +> r)
  have h_eq : (([1, 0] : List (Fin 2))^2 +> (([1, 0] : List (Fin 2))^a +> r)) =
      (([1, 0] : List (Fin 2))^(a + 2) +> r) := by
    rw [<- list_blank_append_pow_add ([1, 0] : List (Fin 2)) 2 a r, Nat.add_comm]
  rw [h_eq] at h2
  exact ReachesStar.trans_plus h1 h2
lemma drain_A_left_111_01_with_110 (a b : Nat) (r : ListBlank (Fin 2)) :
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}} ([1, 1, 0] +>
    r))
    [target]⊢⁺
    (default {{D}}> (([1, 0] : List (Fin 2))^(a + 2) +> (([1, 1, 0] : List (Fin 2))^b +> r))) := by
  have h1 := shift_A_left_111 b (default <+ ([0, 1] : List (Fin 2))^a) ([1, 1, 0] +> r)
  have h_eq : (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> r)) =
      ([1, 1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> r)) := by
    have h_l : (([1, 1, 0] : List (Fin 2))^b +> ([1, 1, 0] +> r)) =
        (([1, 1, 0] : List (Fin 2))^(b + 1) +> r) := by
      rw [list_blank_append_pow_add_one]
    rw [h_l, list_blank_append_pow_succ_left]
  rw [h_eq] at h1
  exact ReachesStar.trans_plus h1 (drain_A_left_01_with_110 a (([1, 1, 0] : List (Fin 2))^b +> r))
lemma roundtrip_D_110_cap0 (b d : Nat) (l_0 : ListBlank (Fin 2)) :
    ((l_0 <+ [0]) {{D}}> (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2)) +> (([1] :
    List (Fin 2))^d +> default))))
    [target]⊢⁺
    ((l_0 <+ [1, 1]) <{{A}} (([1, 1,
      0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2)
      +> default)))) :=
    by
  have h1 :=
    shift_D_right_110 (b + 1) l_0 (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default))
  rw [split_111_succ b l_0] at h1
  have h2 : (((((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [1]) <+ [0]) {{D}}>
      (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))
      [target]⊢⁺
      (((l_0 <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, list_blank_append_pow_add ([1] : List (Fin 2)) 2 d]
      try rfl
    rw [hd]
    simp only [ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h3 :=
    shift_A_left_111 b (l_0 <+ [1,
      1]) (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2) +> default))
  exact ReachesStar.trans_plus h1 (ReachesPlus.trans_star h2 h3)
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
  try rfl
lemma in_ps_D (a b c d : Nat) (hc : c <= 1) : IsInPatternSet ps (D_cfg a b c d) := by
  refine ⟨(pat_D, .not (.ge_const 2 2)), by simp [ps],
    fun | 0 => a | 1 => b | 2 => c | 3 => d | _ => 0, rfl, ?_⟩
  simp only [evalVarCond]
  omega

lemma closes_of_stepPlus {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢⁺ c_2) (h₂ : StepsToClosed target ps c_2) : StepsToClosed target ps c_1 :=
  StepsToClosed.of_reachesPlus h₁ h₂

lemma closes_of_stepStar {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢* c_2) (h₂ : StepsToClosed target ps c_2) : StepsToClosed target ps c_1 := by
  obtain ⟨c_3, h₂₃, h₃⟩ := h₂
  exact ⟨c_3, ReachesStar.trans_plus h₁ h₂₃, h₃⟩

lemma closes_of_in_ps {c_1 : Cfg (Fin 2) (Fin 6)} {a b c d : Nat}
    (h₁ : c_1 [target]⊢⁺ D_cfg a b c d) (hc : c <= 1) : StepsToClosed target ps c_1 :=
  ⟨D_cfg a b c d, h₁, Or.inl (in_ps_D a b c d hc)⟩

lemma closes_of_halt {c_1 c_2 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [target]⊢⁺ c_2) (h₂ : (step target c_2).isNone) : StepsToClosed target ps c_1 :=
  ⟨c_2, h₁, Or.inr h₂⟩
def A_ones (a k b d : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <{{A}}
    (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +> default)))
lemma closes_A_ones_k2 (a b d : Nat) : StepsToClosed target ps (A_ones a 2 b d) := by
  unfold A_ones
  have h1 : (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^3) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
      [target]⊢⁺
      ((default <+ ([0, 1] : List (Fin 2))^a) <{{A}}
        ([1, 1, 0] +> (([1, 1,
          0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^d
          +> default))))) :=
    by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := drain_A_left_01_with_110 a
    ((([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^d +>
    default))))
  exact closes_of_in_ps (ReachesPlus.trans h1 h2) (by decide)
lemma closes_A_ones_k0 (a b d : Nat) : StepsToClosed target ps (A_ones a 0 b d) := by
  rcases a with _ | _ | a'
  · unfold A_ones
    have h1 : (((default <+ ([0, 1] : List (Fin 2))^0) <+ ([1] : List (Fin 2))^1) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
        [target]⊢⁺
        (default <{{F}} ([1, 0] +> (([1, 1,
          0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d
          +> default))))) :=
    by
      simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, ListBlank.head_default,
    ListBlank.tail_default]
      bb_steps
      try rfl
    exact closes_of_halt h1 rfl
  · unfold A_ones
    have h1 : (((default <+ ([0, 1] : List (Fin 2))^1) <+ ([1] : List (Fin 2))^1) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
        [target]⊢⁺ D_cfg 0 (b + 1) 1 d := by
      unfold D_cfg
      rw [list_blank_append_pow_succ_left ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    exact closes_of_in_ps h1 (by decide)
  · unfold A_ones
    have h1 : (((default <+ ([0, 1] : List (Fin 2))^(a' + 2)) <+ ([1] : List (Fin 2))^1) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
        [target]⊢⁺
        ((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1]) <+ [0]) {{D}}>
          (([1, 1,
            0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d
            +> default)))) :=
    by
      rw [list_blank_append_pow_assoc_right default ([0, 1] : List (Fin 2)) a' 2]
      rw [list_blank_append_pow_succ_left ([1, 1, 0] : List (Fin 2)) b]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := roundtrip_D_110_cap0 b d ((default <+ ([0, 1] : List (Fin 2))^a') <+ [1])
    have h_eq : ((((default <+ ([0, 1] : List (Fin 2))^a') <+ [1]) <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2) +>
    default)))) =
        A_ones a' 2 b (d + 2) := by
      unfold A_ones
      simp only [list_pow_succ, list_pow_zero, List.append_nil]
      try rfl
    rw [h_eq] at h2
    exact closes_of_stepPlus (ReachesPlus.trans h1 h2) (closes_A_ones_k2 a' b (d + 2))
lemma step_A_ones_ksucc3 (a k b d : Nat) :
    (A_ones a (k + 3) b d) [target]⊢⁺ (A_ones a k (b + 1) d) := by
  unfold A_ones
  rw [list_blank_append_pow_assoc_right (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2))
    (k + 1) 3]
  rw [list_blank_append_pow_succ_left ([1, 1, 0] : List (Fin 2)) b]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps
  try rfl
def H_mid (a b m : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0]) {{D}}>
    (([1] : List (Fin 2))^m +> default)
lemma closes_H_mid_a0_m1 (b : Nat) : StepsToClosed target ps (H_mid 0 (b + 1) 1) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
    1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      (((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^3 +> default))) := by
    rw [list_blank_append_pow_assoc_right (default <+ [1]) ([1, 1, 1] : List (Fin 2)) b 1]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 :=
    shift_A_left_111 (b + 1) (default <+ [1]) (([0] : List (Fin 2))
      +> (([1] : List (Fin 2))^3 +> default))
  exact closes_of_stepPlus (ReachesPlus.trans_star h1 h2) (closes_A_ones_k0 0 (b + 1) 3)
lemma closes_H_mid_asucc_m1 (a b : Nat) : StepsToClosed target ps (H_mid (a + 1) (b + 1) 1) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin
    2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^1 +> default)))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
    1)) <{{A}}
        (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^3 +> default))) := by
    rw [list_blank_append_pow_assoc_right ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1])
    ([1, 1, 1] : List (Fin 2)) b 1]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := shift_A_left_111 (b + 1) ((default <+ ([0, 1] : List (Fin 2))^(a + 1)) <+ [1])
    (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^3 +> default))
  exact closes_of_stepPlus (ReachesPlus.trans_star h1 h2) (closes_A_ones_k0 (a + 1) (b + 1) 3)
lemma closes_H_mid_m2 (a b : Nat) : StepsToClosed target ps (H_mid a (b + 1) 2) := by
  unfold H_mid
  rw [comm_1_111 (b + 1) (default <+ ([0, 1] : List (Fin 2))^a)]
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+
    [1]) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^2 +> default)))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default)))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := drain_A_left_111_01_with_110 a (b + 1)
    (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
  exact closes_of_in_ps (ReachesPlus.trans h1 h2) (by decide)
lemma closes_H_mid_a0_m3 (b m : Nat) : StepsToClosed target ps (H_mid 0 (b + 1) (m + 3)) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^0) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
    1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default)))
      [target]⊢⁺
      (((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 m]
      try rfl
    have hb : (default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2) =
        ((default <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] := by
      rw [list_blank_append_pow_assoc_right (default <+ [1]) ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      try rfl
    rw [hm, hb, list_blank_append_pow_succ_left ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, list_pow_zero, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := shift_A_left_111 (b + 2) (default <+ [1]) (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : ((default <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (default <{{F}} ([1, 0] +> (([1, 1,
        0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))) :=
    by
    simp only [list_pow_succ, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, ListBlank.head_default,
    ListBlank.tail_default]
    bb_steps
    try rfl
  exact closes_of_halt (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) rfl
lemma step_H_mid_a1_m3_prefix (b m : Nat) :
    (H_mid 1 (b + 1) (m + 3)) [target]⊢⁺
    (((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 1) +> default)) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
    1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default)))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2))
    <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 m]
      try rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)
    =
        (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <+ ([1, 1,
          1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] :=
    by
      rw [list_blank_append_pow_assoc_right ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) ([1, 1,
    1] : List (Fin 2)) (b + 1) 1]
      try rfl
    rw [hm, hb, list_blank_append_pow_succ_left ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^1) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^1) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0]) {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [list_blank_append_pow_succ_left ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h4 := shift_D_right_110 (b + 2) (default <+ ([1, 1, 1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((default <+ ([1, 1, 1] : List (Fin 2))^1) <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- list_blank_append_pow_assoc_right default ([1, 1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (ReachesPlus.trans_star h3 h4)
lemma closes_H_mid_a1_m3 (b m : Nat) : StepsToClosed target ps (H_mid 1 (b + 1) (m + 3)) := by
  have h_pref := step_H_mid_a1_m3_prefix b m
  rcases m with _ | _ | m'
  · have h1 : ((((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^1 +> default)))
        [target]⊢⁺
        ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 2)) <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
      rw [list_blank_append_pow_assoc_right default ([1, 1, 1] : List (Fin 2)) (b + 2) 1]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := drain_A_left_111_01_with_110 0 (b + 2)
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
    exact closes_of_in_ps (ReachesPlus.trans h_pref (ReachesPlus.trans h1 h2)) (by decide)
  · have h1 : ((((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^2 +> default)))
        [target]⊢⁺
        (((default <+ [1, 1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
          (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))) := by
      rw [split_111_succ (b + 2) default]
      rw [list_blank_append_pow_assoc_right (default <+ [1, 1]) ([1, 1, 1] : List (Fin 2)) (b + 2)
    1]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := shift_A_left_111 (b + 3) (default <+ [1, 1])
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2 +> default))
    have h3 : ((default <+ [1, 1]) <{{A}}
        (([1, 1, 0] : List (Fin 2))^(b + 3) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^2
    +> default))))
        [target]⊢⁺ D_cfg 1 (b + 3) 1 2 := by
      unfold D_cfg
      simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    exact closes_of_in_ps (ReachesPlus.trans h_pref (ReachesPlus.trans (ReachesPlus.trans_star h1
    h2) h3)) (by decide)
  · have h1 : ((((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <+ [0]) {{D}}>
        (([1] : List (Fin 2))^(m' + 3) +> default)))
        [target]⊢⁺
        ((default <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default)))) :=
    by
      have hm : (([1] : List (Fin 2))^(m' + 3) +> default) =
          ([1, 1, 1] +> (([1] : List (Fin 2))^m' +> default)) := by
        rw [Nat.add_comm m' 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 m']
        try rfl
      rw [hm, list_blank_append_pow_succ_left ([1] : List (Fin 2)) m']
      simp only [list_pow_succ, list_pow_zero, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h2 := drain_A_left_111_01_with_110 0 (b + 3)
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(m' + 1) +> default))
    exact closes_of_in_ps (ReachesPlus.trans h_pref (ReachesPlus.trans h1 h2)) (by decide)
lemma step_H_mid_asucc2_m3 (a b m : Nat) :
    (H_mid (a + 2) (b + 1) (m + 3)) [target]⊢⁺ (H_mid a (b + 3) (m + 1)) := by
  unfold H_mid
  have h1 : ((((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
    2))^(b + 1)) <+ [0]) {{D}}>
      (([1] : List (Fin 2))^(m + 3) +> default)))
      [target]⊢⁺
      ((((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b +
    2)) <{{A}}
        (([1] : List (Fin 2))^(m + 1) +> default)) := by
    have hm : (([1] : List (Fin 2))^(m + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^m +> default)) := by
      rw [Nat.add_comm m 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 m]
      try rfl
    have hb : ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1, 1] : List (Fin
    2))^(b + 2) =
        (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <+ ([1, 1,
          1] : List (Fin 2))^(b + 1)) <+ [1, 1, 1] :=
    by
      rw [list_blank_append_pow_assoc_right ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1])
    ([1, 1, 1] : List (Fin 2)) (b + 1) 1]
      try rfl
    rw [hm, hb, list_blank_append_pow_succ_left ([1] : List (Fin 2)) m]
    simp only [list_pow_succ, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := shift_A_left_111 (b + 2) ((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1])
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h3 : (((default <+ ([0, 1] : List (Fin 2))^(a + 2)) <+ [1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default)))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+ [0])
    {{D}}>
        (([1, 1, 0] : List (Fin 2))^(b + 2) +> (([1] : List (Fin 2))^(m + 1) +> default))) := by
    rw [list_blank_append_pow_assoc_right default ([0, 1] : List (Fin 2)) a 2]
    rw [list_blank_append_pow_succ_left ([1, 1, 0] : List (Fin 2)) (b + 1)]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h4 :=
    shift_D_right_110 (b + 2) (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1,
      1] : List (Fin 2))^1)
    (([1] : List (Fin 2))^(m + 1) +> default)
  have h_eq : ((((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^1) <+
      ([1, 1, 1] : List (Fin 2))^(b + 2)) =
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) <+ ([1, 1, 1] : List (Fin 2))^(b + 3)) := by
    rw [<- list_blank_append_pow_assoc_right ((default <+ ([0, 1] : List (Fin 2))^a) <+ [1]) ([1,
    1, 1] : List (Fin 2)) 1 (b + 2)]
    have h_add : 1 + (b + 2) = b + 3 := by omega
    rw [h_add]
  rw [h_eq] at h4
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (ReachesPlus.trans_star h3 h4)
lemma closes_H_mid (a : Nat) : ∀ b m, StepsToClosed target ps (H_mid a (b + 1) (m + 1)) := by
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
  ((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^k) {{B}}>
    ([0, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
lemma closes_B_mid_a0_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 0 1 0 d) := by
  have h1 : (B_mid 0 1 0 d) [target]⊢⁺ D_cfg 0 0 0 (d + 4) := by
    unfold B_mid D_cfg
    have hd : (([1] : List (Fin 2))^(d + 4) +> default) =
        ([1, 1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 4, list_blank_append_pow_add ([1] : List (Fin 2)) 4 d]
      try rfl
    rw [hd]
    simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  exact closes_of_in_ps h1 (by decide)
lemma closes_B_mid_a1_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 1 1 0 d) := by
  have h1 : (B_mid 1 1 0 d) [target]⊢⁺
      (default <{{F}} ([1, 0, 1, 1, 0] +> (([1] : List (Fin 2))^(d + 2) +> default))) := by
    unfold B_mid
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, list_blank_append_pow_add ([1] : List (Fin 2)) 2 d]
      try rfl
    rw [hd]
    simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, ListBlank.head_default,
    ListBlank.tail_default]
    bb_steps
    try rfl
  exact closes_of_halt h1 rfl
lemma closes_B_mid_a2_k1_b0 (d : Nat) : StepsToClosed target ps (B_mid 2 1 0 d) := by
  have h1 : (B_mid 2 1 0 d) [target]⊢⁺ D_cfg 0 2 0 (d + 2) := by
    unfold B_mid D_cfg
    have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
        ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 2, list_blank_append_pow_add ([1] : List (Fin 2)) 2 d]
      try rfl
    rw [hd]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  exact closes_of_in_ps h1 (by decide)
lemma step_B_mid_asucc3_k1_b0 (a d : Nat) :
    (B_mid (a + 3) 1 0 d) [target]⊢⁺ (H_mid a 2 (d + 2)) := by
  unfold B_mid H_mid
  rw [list_blank_append_pow_assoc_right default ([0, 1] : List (Fin 2)) a 3]
  have hd : (([1] : List (Fin 2))^(d + 2) +> default) =
      ([1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 2, list_blank_append_pow_add ([1] : List (Fin 2)) 2 d]
    try rfl
  rw [hd]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps
  try rfl
lemma closes_B_mid_k1_b0 (a d : Nat) : StepsToClosed target ps (B_mid a 1 0 d) := by
  rcases a with _ | _ | _ | a'
  · exact closes_B_mid_a0_k1_b0 d
  · exact closes_B_mid_a1_k1_b0 d
  · exact closes_B_mid_a2_k1_b0 d
  · exact closes_of_stepPlus (step_B_mid_asucc3_k1_b0 a' d) (closes_H_mid a' 1 (d + 1))
lemma step_B_mid_ksucc2_b0 (a k d : Nat) :
    (B_mid a (k + 2) 0 d) [target]⊢⁺ (A_ones a k 0 (d + 3)) := by
  unfold B_mid A_ones
  rw [list_blank_append_pow_assoc_right (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin 2))
    (k + 1) 1]
  have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
      ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
    rw [Nat.add_comm d 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 d]
    try rfl
  rw [hd]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps
  try rfl
lemma step_B_mid_bsucc (a k b d : Nat) :
    (B_mid a (k + 1) (b + 1) d) [target]⊢⁺ (B_mid a (k + 2) b (d + 2)) := by
  unfold B_mid
  have h1 : (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) {{B}}>
      ([0, 0] +> (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2)) +> (([1] : List (Fin
    2))^d +> default)))))
      [target]⊢⁺
      (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0]) <+ [0])
    {{D}}>
        (([1, 1,
          0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d
          +> default)))) :=
    by
    simp only [list_pow_succ, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h2 := roundtrip_D_110_cap0 b d
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0])
  have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 1)) <+ [0]) <+
    [1, 1]) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2) +>
    default))))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1] : List (Fin 2))^(k + 2)) {{B}}>
        ([0, 0] +> (([1, 1,
          0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2)
          +> default))))) :=
    by
    rw [list_blank_append_pow_assoc_right (default <+ ([0, 1] : List (Fin 2))^a) ([1] : List (Fin
    2)) (k + 1) 1]
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  exact ReachesPlus.trans h1 (ReachesPlus.trans h2 h3)
lemma closes_A_ones_a0_k1 (b d : Nat) : StepsToClosed target ps (A_ones 0 1 b d) := by
  unfold A_ones
  have h1 : (((default <+ ([0, 1] : List (Fin 2))^0) <+ ([1] : List (Fin 2))^2) <{{A}}
      (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d +>
    default))))
      [target]⊢⁺ D_cfg 1 b 1 d := by
    unfold D_cfg
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  exact closes_of_in_ps h1 (by decide)
lemma step_A_ones_asucc_k1 (a b d : Nat) :
    (A_ones (a + 1) 1 b d) [target]⊢⁺ (B_mid a 2 b d) := by
  unfold A_ones B_mid
  rw [list_blank_append_pow_assoc_right default ([0, 1] : List (Fin 2)) a 1]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  bb_steps
  try rfl
lemma closes_B_mid_all (a : Nat) : ∀ b k d, StepsToClosed target ps (B_mid a (k + 1) b d) := by
  induction a using Nat.strong_induction_on with
  | h a ih_a =>
    have h_A_ones : ∀ k b d, StepsToClosed target ps (A_ones a k b d) := by
      intro k
      induction k using Nat.strong_induction_on with
      | h k ih_k =>
        intro b d
        rcases k with _ | _ | _ | k'
        · exact closes_A_ones_k0 a b d
        · rcases a with _ | a'
          · exact closes_A_ones_a0_k1 b d
          · exact closes_of_stepPlus (step_A_ones_asucc_k1 a' b d) (ih_a a' (by omega) b 1 d)
        · exact closes_A_ones_k2 a b d
        · exact closes_of_stepPlus (step_A_ones_ksucc3 a k' b d) (ih_k k' (by omega) (b + 1) d)
    have h_b0 : ∀ k d, StepsToClosed target ps (B_mid a (k + 1) 0 d) := by
      intro k d
      rcases k with _ | k'
      · exact closes_B_mid_k1_b0 a d
      · exact closes_of_stepPlus (step_B_mid_ksucc2_b0 a k' d) (h_A_ones k' 0 (d + 3))
    intro b
    induction b with
    | zero =>
      intro k d
      exact h_b0 k d
    | succ b ih_b =>
      intro k d
      exact closes_of_stepPlus (step_B_mid_bsucc a k b d) (ih_b (k + 1) (d + 2))
lemma closes_B_mid (b a k d : Nat) : StepsToClosed target ps (B_mid a (k + 1) b d) :=
  closes_B_mid_all a b k d
lemma step_D_cfg_to_D_mid (a : Nat) (r : ListBlank (Fin 2)) :
    (default {{D}}> (([1, 0] : List (Fin 2))^a +> r)) [target]⊢*
    (((default <+ ([0, 1] : List (Fin 2))^a) <+ [0]) {{D}}> r) := by
  have h := shift_D_right_10 a default r
  have h_def : (default <+ ([0] : List (Fin 2))) = default := by
    simp only [ListBlank.append, ListBlank.cons_zero_default]
  rwa [h_def] at h
lemma closes_D_cfg_c1 (a b d : Nat) : StepsToClosed target ps (D_cfg a b 1 d) := by
  rcases a with _ | a'
  · rcases b with _ | b'
    · have h1 : (D_cfg 0 0 1 d) [target]⊢⁺ (D_cfg 0 0 1 (d + 1)) := by
        unfold D_cfg
        rw [list_blank_append_pow_succ_left ([1] : List (Fin 2)) d]
        simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
        bb_steps
        try rfl
      exact closes_of_in_ps h1 (by decide)
    · have h1 := roundtrip_D_110_cap0 b' d default
      have h_def : (default <+ ([0] : List (Fin 2))) = default :=
    by simp only [ListBlank.append, ListBlank.cons_zero_default]
      rw [h_def] at h1
      have h2 : ((default <+ [1, 1]) <{{A}}
          (([1, 1, 0] : List (Fin 2))^b' +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^(d + 2)
    +> default))))
          [target]⊢⁺ D_cfg 1 b' 1 (d + 2) := by
        unfold D_cfg
        simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
        bb_steps
        try rfl
      have h_start : ((default {{D}}>
          (([1, 1, 0] : List (Fin 2))^(b' + 1) +> (([0] : List (Fin 2)) +> (([1] : List (Fin 2))^d
    +> default))))) =
          D_cfg 0 (b' + 1) 1 d := by
        unfold D_cfg; rfl
      rw [h_start] at h1
      exact closes_of_in_ps (ReachesPlus.trans h1 h2) (by decide)
  · have h1 := step_D_cfg_to_D_mid a'
      ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
    2))^d +> default))))
    have h_start : (default {{D}}>
        (([1, 0] : List (Fin 2))^a' +> ([1, 0] +>
          (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^d +>
    default)))))) =
        D_cfg (a' + 1) b 1 d := by
      unfold D_cfg
      rw [list_blank_append_pow_add_one]
    rw [h_start] at h1
    have h2 : ((((default <+ ([0, 1] : List (Fin 2))^a') <+ [0]) {{D}}>
        ([1, 0] +> (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
    2))^d +> default))))))
        [target]⊢⁺ B_mid a' 1 b d := by
      unfold B_mid
      simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    exact closes_of_stepStar h1 (closes_of_stepPlus h2 (closes_B_mid b a' 0 d))
lemma D_cfg_c0_d0_eq (a b : Nat) : D_cfg a b 0 0 = D_cfg a b 1 0 := by
  unfold D_cfg
  simp only [list_pow_succ, list_pow_zero, List.append_nil,
    ListBlank.append, ListBlank.append_cons, ListBlank.cons_zero_default]
lemma D_cfg_c0_d2_eq (a b : Nat) : D_cfg a b 0 2 = D_cfg a (b + 1) 1 0 := by
  unfold D_cfg
  have h_b : (([1, 1, 0] : List (Fin 2))^(b + 1) +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin
    2))^0 +> default))) =
      (([1, 1, 0] : List (Fin 2))^b +> ([1, 1,
        0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^0 +> default)))) :=
    by
    rw [<- list_blank_append_pow_add_one]
  rw [h_b]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons, ListBlank.cons_zero_default,
      <- ListBlank.append_assoc]
lemma closes_D_cfg_c0_d1 (a b : Nat) : StepsToClosed target ps (D_cfg a b 0 1) := by
  rcases b with _ | b'
  · rcases a with _ | a'
    · have h1 : (D_cfg 0 0 0 1) [target]⊢⁺ (D_cfg 0 0 0 4) := by
        unfold D_cfg
        simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
        bb_steps
        try rfl
      exact closes_of_in_ps h1 (by decide)
    · have h1 := step_D_cfg_to_D_mid (a' + 1)
        (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
    default)))
      have h_start : (default {{D}}>
          (([1, 0] : List (Fin 2))^(a' + 1) +>
            (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
    default))))) =
          D_cfg (a' + 1) 0 0 1 := by
        unfold D_cfg; rfl
      rw [h_start] at h1
      have h2 : ((((default <+ ([0, 1] : List (Fin 2))^(a' + 1)) <+ [0]) {{D}}>
          (([1, 1, 0] : List (Fin 2))^0 +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
    default)))))
          [target]⊢⁺ B_mid (a' + 1) 1 0 0 := by
        unfold B_mid
        simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons, ListBlank.cons_zero_default,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, ListBlank.head_default,
    ListBlank.tail_default]
        bb_steps
        try rfl
      exact closes_of_stepStar h1 (closes_of_stepPlus h2 (closes_B_mid 0 (a' + 1) 0 0))
  · have h1 := step_D_cfg_to_D_mid a
      (([1, 1, 0] : List (Fin 2))^(b' + 1) +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +>
    default)))
    have h2 := shift_D_right_110 (b' + 1) (default <+ ([0, 1] : List (Fin 2))^a)
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default))
    have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^(b' + 1)) <+
    [0]) {{D}}>
        (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^1 +> default))))
        [target]⊢⁺
        (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b') <{{A}}
          ([1, 1, 0] +> (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default)))) := by
      rw [list_blank_append_pow_assoc_right (default <+ ([0, 1] : List (Fin 2))^a) ([1, 1, 1] :
    List (Fin 2)) b' 1]
      simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
      bb_steps
      try rfl
    have h4 := drain_A_left_111_01_with_110 a b'
      (([0] : List (Fin 2))^1 +> (([1] : List (Fin 2))^3 +> default))
    exact closes_of_in_ps
      (ReachesStar.trans_plus (ReachesStar.trans h1 h2) (ReachesPlus.trans h3 h4)) (by decide)
lemma closes_D_cfg_c0_d3 (a b d : Nat) : StepsToClosed target ps (D_cfg a b 0 (d + 3)) := by
  have h1 := step_D_cfg_to_D_mid a
    (([1, 1, 0] : List (Fin 2))^b +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +>
    default)))
  have h2 := shift_D_right_110 b (default <+ ([0, 1] : List (Fin 2))^a)
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default))
  have h3 : (((((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <+ [0])
    {{D}}>
      (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 3) +> default))))
      [target]⊢⁺
      (((default <+ ([0, 1] : List (Fin 2))^a) <+ ([1, 1, 1] : List (Fin 2))^b) <{{A}}
        ([1, 1, 0] +> (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default)))) := by
    have hd : (([1] : List (Fin 2))^(d + 3) +> default) =
        ([1, 1, 1] +> (([1] : List (Fin 2))^d +> default)) := by
      rw [Nat.add_comm d 3, list_blank_append_pow_add ([1] : List (Fin 2)) 3 d]
      try rfl
    rw [hd, list_blank_append_pow_succ_left ([1] : List (Fin 2)) d]
    simp only [list_pow_zero,
    ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  have h4 := drain_A_left_111_01_with_110 a b
    (([0] : List (Fin 2))^0 +> (([1] : List (Fin 2))^(d + 1) +> default))
  exact closes_of_in_ps
    (ReachesStar.trans_plus (ReachesStar.trans h1 h2) (ReachesPlus.trans h3 h4)) (by decide)
lemma closes_D_cfg (a b c d : Nat) (hc : c <= 1) : StepsToClosed target ps (D_cfg a b c d) := by
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
    simp only [list_pow_succ, list_pow_zero, List.append_nil, List.nil_append,
    ListBlank.append, List.cons_append, ListBlank.append_cons,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
    bb_steps
    try rfl
  exact ReachesPlus.to_star h_init

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

end BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH1LC
