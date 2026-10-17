/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC`

## Collatz-like Acceleration Rules
-/


@[expose] public section
namespace BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_---1LC"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

notation3 c1 " [target]⊢⁺ " c2 => ReachesPlus target c1 c2
notation3 c1 " [target]⊢* " c2 => ReachesStar target c1 c2
notation3 c1 " [target]⊢ " c2 => step target c1 = some c2

notation l " {{" s "}} " r => (⟨s, l, r⟩ : Tape _)
notation:67 s:67 " << " a:68 => ListBlank.cons a s
infixr:67 " >> " => ListBlank.cons
notation:67 s:67 " <+ " l:68 => ListBlank.append l s
infixr:67 " +> " => ListBlank.append
notation3 l " {{" q "}}> " r => (⟨some q, ⟨ListBlank.head r, l, ListBlank.tail r⟩⟩ : Cfg _ _)
notation3 l " <{{" q "}} " r => (⟨some q, ⟨ListBlank.head l, ListBlank.tail l, r⟩⟩ : Cfg _ _)

@[simp] lemma nil_append_blank (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
@[simp] lemma cons_append_blank (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
@[simp] lemma zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] lemma default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
@[simp] lemma default_tail : (default : ListBlank (Fin 2)).tail = default := rfl

lemma append_pow_add_flipped (s : ListBlank (Fin 2)) (u : List (Fin 2)) (m n : Nat) :
    s <+ (u ^ (m + n)) = (s <+ (u ^ m)) <+ (u ^ n) := by
  rw [← ListBlank.append_assoc, ← list_pow_add, Nat.add_comm m n]

local macro "exec_step" : tactic =>
  `(tactic| (try refine ReachesPlus.to_star ?_) <;>
    refine ReachesPlus.head (by (try simp only [ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Tape.move, ListBlank.head_cons, ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail, list_pow_zero, list_pow_succ,
      cons_append_blank, nil_append_blank])

local macro "execute" : tactic =>
  `(tactic| repeat (any_goals exec_step))

lemma zero_one_pow_default (m : Nat) :
    (([0, 1] : List (Fin 2))^m +> default) =
    (0 : Fin 2) >> (([1, 0] : List (Fin 2))^m +> default) := by
  induction m with
  | zero => exact zero_cons_default.symm
  | succ m ih =>
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m default, ih]
    rfl
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine ReachesPlus.to_star ?_) <;>
    refine ReachesPlus.head (by (try simp only [ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Tape.move, ListBlank.head_cons, ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))
lemma shift_A_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{A}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 1] : List (Fin 2))^k) {{A}}> r) := by
  induction k generalizing l r with
  | zero => use 0; simp
  | succ k ih =>
    have h1 : (l {{A}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 1] : List (Fin 2))) {{A}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      simp only [cons_append_blank, nil_append_blank]
      execute
    have h2 := ih (l <+ ([1, 1] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([1, 1] : List (Fin 2))) <+ ([1, 1] : List (Fin 2))^k) =
        (l <+ ([1, 1] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3
lemma shift_B_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{B}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([1, 0] : List (Fin 2))^k) {{B}}> r) := by
  induction k generalizing l r with
  | zero => use 0; simp
  | succ k ih =>
    have h1 : (l {{B}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))) {{B}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      simp only [cons_append_blank, nil_append_blank]
      execute
    have h2 := ih (l <+ ([1, 0] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([1, 0] : List (Fin 2))) <+ ([1, 0] : List (Fin 2))^k) =
        (l <+ ([1, 0] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3
lemma shift_E_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1, 1] : List (Fin 2))^k +> r)) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2))^k) {{E}}> r) := by
  induction k generalizing l r with
  | zero => use 0; simp
  | succ k ih =>
    have h1 : (l {{E}}> (([1, 1] : List (Fin 2))^(k + 1) +> r)) [target]⊢⁺
        ((l <+ ([0, 1] : List (Fin 2))) {{E}}> (([1, 1] : List (Fin 2))^k +> r)) := by
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) k r]
      simp only [cons_append_blank, nil_append_blank]
      execute
    have h2 := ih (l <+ ([0, 1] : List (Fin 2))) r
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow : ((l <+ ([0, 1] : List (Fin 2))) <+ ([0, 1] : List (Fin 2))^k) =
        (l <+ ([0, 1] : List (Fin 2))^(k + 1)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow] at h3
lemma shift_C_left_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((0 : Fin 2) >> r)) [target]⊢*
    (l {{C}}> ((0 : Fin 2) >> (([1, 1] : List (Fin 2))^k +> r))) := by
  induction k generalizing l r with
  | zero => use 0; simp
  | succ k ih =>
    have h_pow_l : (l <+ ([1, 0] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1, 0] : List (Fin 2))) := by
      rw [← ListBlank.append_assoc]; rfl
    rw [h_pow_l]
    have h1 : (((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1,
      0] : List (Fin 2))) {{C}}> ((0 : Fin 2) >> r))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((0 : Fin 2) >> (([1,
      1] : List (Fin 2)) +> r))) := by
      simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
      execute
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow_r : (([1, 1] : List (Fin 2))^k +> (([1, 1] : List (Fin 2)) +> r)) =
        (([1, 1] : List (Fin 2))^(k + 1) +> r) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow_r] at h3
lemma shift_C_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> ((1 : Fin 2) >> r)) [target]⊢*
    (l {{C}}> (([1, 0] : List (Fin 2))^k +> ((1 : Fin 2) >> r))) := by
  induction k generalizing l r with
  | zero => use 0; simp
  | succ k ih =>
    have h_pow_l : (l <+ ([1, 0] : List (Fin 2))^(k + 1)) =
        ((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1, 0] : List (Fin 2))) := by
      rw [← ListBlank.append_assoc]; rfl
    rw [h_pow_l]
    have h1 : (((l <+ ([1, 0] : List (Fin 2))^k) <+ ([1,
      0] : List (Fin 2))) {{C}}> ((1 : Fin 2) >> r))
        [target]⊢⁺
        ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r))) := by
      simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
      execute
    have h2 : ((l <+ ([1, 0] : List (Fin 2))^k) {{C}}> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r)))
        [target]⊢*
        (l {{C}}> (([1, 0] : List (Fin 2))^k +> (([1,
      0] : List (Fin 2)) +> ((1 : Fin 2) >> r)))) := by
      simpa [List.cons_append, cons_append_blank, nil_append_blank] using
        ih l ((0 : Fin 2) >> ((1 : Fin 2) >> r))
    have h3 := ReachesPlus.to_star (ReachesPlus.trans_star h1 h2)
    have h_pow_r : (([1, 0] : List (Fin 2))^k +> (([1, 0] : List (Fin 2)) +> ((1 : Fin 2) >> r))) =
        (([1, 0] : List (Fin 2))^(k + 1) +> ((1 : Fin 2) >> r)) := by
      rw [← ListBlank.append_assoc, ← list_pow_succ']
    rwa [h_pow_r] at h3
lemma step_C_11_to_B (d : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [1, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    ((l <+ [1, 1]) {{B}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) := by
  cases d with
  | zero =>
    simp only [list_pow_zero, cons_append_blank, nil_append_blank,
      ListBlank.head_cons, ListBlank.tail_cons]
    execute
  | succ d =>
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
lemma step_C_default_to_E (d : Nat) (r : ListBlank (Fin 2)) :
    (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    ((default <+ [0, 1]) {{E}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) := by
  cases d with
  | zero =>
    simp only [list_pow_zero, cons_append_blank, nil_append_blank,
      ListBlank.head_cons, ListBlank.tail_cons]
    execute
  | succ d =>
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
lemma step_C_01_to_A (d : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
    (l {{A}}> (([1, 1] : List (Fin 2))^d +> ([1, 1] +> ((1 : Fin 2) >> r)))) := by
  have h1 : ((l <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) [target]⊢⁺
      (l {{A}}> ([1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r)))) := by
    cases d with
    | zero =>
      simp only [list_pow_zero, cons_append_blank, nil_append_blank,
      ListBlank.head_cons, ListBlank.tail_cons]
      execute
    | succ d =>
      rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
      simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
      execute
  have h_comm : ([1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> r))) =
      (([1, 1] : List (Fin 2))^d +> ([1, 1] +> ((1 : Fin 2) >> r))) := by
    rw [<- ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) d]
    rw [ListBlank.append_pow_add ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_comm] at h1
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 1] 1 (.rep [0, 1] 0 .default)
    head  := some C
    right := .rep [1, 1] 2 (.rep [1, 0] 3 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default))))) }
def ps : TapePatternSet (Fin 2) (Fin 6) := [(pat_A, .true)]
def cfg_A (a k d c : Nat) : Cfg (Fin 2) (Fin 6) :=
  ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k) {{C}}>
    (([1, 1] : List (Fin 2))^d +> (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default)))
lemma eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) (vars 3) := by
  simp [evalTapePattern, evalTapeExpr, pat_A, cfg_A]
lemma in_ps_A (a k d c : Nat) : IsInPatternSet ps (cfg_A a k d c) := by
  refine ⟨(pat_A, .true), List.Mem.head _,
      (fun i => match i with | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0), ?_, trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0)).symm
theorem one_one_pow_comm_one (n : Nat) (R : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2))^n +> ((1 : Fin 2) >> R)) =
    ((1 : Fin 2) >> (([1, 1] : List (Fin 2))^n +> R)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) n]
    rw [ListBlank.append_pow_succ ([1, 1] : List (Fin 2)) n]
    simp only [cons_append_blank, nil_append_blank]
    rw [ih]
theorem rule_1 (a k d c : Nat) :
    (cfg_A a (k + 1) d (c + 1)) [target]⊢⁺ (cfg_A a k (d + 2) c) := by
  let L := ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k)
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A a (k + 1) d (c + 1) =
      ((L <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^d +> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))) := by
    unfold cfg_A
    rw [append_pow_add_flipped _ ([1, 1] : List (Fin 2)) k 1]
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rw [h_start]
  have h1 := step_C_11_to_B d L ((0 : Fin 2) >> R_tail)
  have h2 := shift_B_11 d (L <+ [1, 1]) ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((L <+ [1, 1]) <+ ([1,
      0] : List (Fin 2))^d) {{B}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))
      [target]⊢⁺
      (((L <+ [1, 1]) <+ ([1,
      0] : List (Fin 2))^d) {{C}}> ((0 : Fin 2) >> ((1 : Fin 2) >> R_tail))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h4 := shift_C_left_01 d (L <+ [1, 1]) ((1 : Fin 2) >> R_tail)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h5 : ((L <+ [1, 1]) {{C}}> ((0 : Fin 2) >> (([1,
      1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail))))
      [target]⊢⁺
      (L {{C}}> ([1, 1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail)))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h12345 := ReachesPlus.trans h1234 h5
  have h_end : (L {{C}}> ([1, 1, 1] +> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> R_tail)))) =
      cfg_A a k (d + 2) c := by
    rw [one_one_pow_comm_one d R_tail]
    unfold cfg_A
    have h_d : d + 2 = 2 + d := by omega
    rw [h_d, ListBlank.append_pow_add ([1, 1] : List (Fin 2)) 2 d]
    rfl
  rwa [h_end] at h12345
theorem rule_2 (a k d : Nat) :
    (cfg_A a (k + 1) d 0) [target]⊢⁺ (cfg_A a (k + 1) 0 (d + 1)) := by
  let L := ((([0, 1] : List (Fin 2))^a +> default) <+ ([1, 1] : List (Fin 2))^k)
  have h_start : cfg_A a (k + 1) d 0 =
      ((L <+ [1, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [append_pow_add_flipped _ ([1, 1] : List (Fin 2)) k 1]
    rfl
  rw [h_start]
  have h1 := step_C_11_to_B d L ([1, 1, 1] +> default)
  have h2 := shift_B_11 d (L <+ [1, 1]) ((1 : Fin 2) >> ([1, 1, 1] +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) {{B}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))
      [target]⊢⁺
      ((((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) <+ [1, 0]) {{C}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_pow : (((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^d) <+ [1, 0]) =
      ((L <+ [1, 1]) <+ ([1, 0] : List (Fin 2))^(d + 1)) := by
    rw [← ListBlank.append_assoc]; rfl
  rw [h_pow] at h123
  have h4 := shift_C_left_10 (d + 1) (L <+ [1, 1]) ([1, 1, 1] +> default)
  have h1234 := ReachesPlus.trans_star h123 h4
  have h_end : ((L <+ [1, 1]) {{C}}> (([1, 0] : List (Fin 2))^(d + 1) +> ((1 : Fin 2) >> ([1,
      1, 1] +> default)))) =
      cfg_A a (k + 1) 0 (d + 1) := by
    unfold cfg_A
    rw [append_pow_add_flipped _ ([1, 1] : List (Fin 2)) k 1]
    rfl
  rwa [h_end] at h1234
theorem rule_3 (d : Nat) :
    ∃ cfg', ((cfg_A 0 0 d 0) [target]⊢⁺ cfg') /\ (step target cfg').isNone := by
  refine ⟨(default {{F}}> ((0 : Fin 2) >> ((1 : Fin 2) >> (([1,
      1] : List (Fin 2))^(d + 3) +> ([1] +> default))))), ?_,
    by simp [step, target, F, ListBlank.head_cons]; rfl⟩
  have h_start : cfg_A 0 0 d 0 =
      (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1, 1] +> default)))) := rfl
  rw [h_start]
  have h1 := step_C_default_to_E d ([1, 1, 1] +> default)
  have h2 := shift_E_11 d (default <+ [0, 1]) ((1 : Fin 2) >> ([1, 1, 1] +> default))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) {{E}}> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))
      [target]⊢⁺
      (((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0,
      1]) {{E}}> default) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons, default_head, default_tail]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_l : ((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0, 1]) =
      ((0 : Fin 2) >> (default <+ ([1, 0] : List (Fin 2))^(d + 3))) := by
    have h_merge : ((((default <+ [0, 1]) <+ ([0, 1] : List (Fin 2))^d) <+ [0, 1]) <+ [0, 1]) =
        ((([0, 1] : List (Fin 2))^(d + 3) +> default)) := by
      have h_d : d + 3 = ((1 + d) + 1) + 1 := by omega
      rw [h_d]
      rw [append_pow_add_flipped default ([0, 1] : List (Fin 2)) ((1 + d) + 1) 1]
      rw [append_pow_add_flipped default ([0, 1] : List (Fin 2)) (1 + d) 1]
      rw [append_pow_add_flipped default ([0, 1] : List (Fin 2)) 1 d]
      rfl
    rw [h_merge, zero_one_pow_default (d + 3)]
  rw [h_l] at h123
  have h4 : (((0 : Fin 2) >> (default <+ ([1, 0] : List (Fin 2))^(d + 3))) {{E}}> default)
      [target]⊢⁺
      ((default <+ ([1, 0] : List (Fin 2))^(d + 3)) {{C}}> ((0 : Fin 2) >> ([1] +> default))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons, default_head, default_tail]
    execute
  have h1234 := ReachesPlus.trans h123 h4
  have h5 := shift_C_left_01 (d + 3) default ([1] +> default)
  have h12345 := ReachesPlus.trans_star h1234 h5
  have h6 : (default {{C}}> ((0 : Fin 2) >> (([1, 1] : List (Fin 2))^(d + 3) +> ([1] +> default))))
      [target]⊢⁺
      (default {{F}}> ((0 : Fin 2) >> ((1 : Fin 2) >> (([1,
      1] : List (Fin 2))^(d + 3) +> ([1] +> default))))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  exact ReachesPlus.trans h12345 h6
theorem rule_4 (d c : Nat) :
    (cfg_A 0 0 d (c + 1)) [target]⊢⁺ (cfg_A (d + 1) 0 0 (c + 1)) := by
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A 0 0 d (c + 1) =
      (default {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rw [h_start]
  have h1 := step_C_default_to_E d ((0 : Fin 2) >> R_tail)
  have h2 := shift_E_11 d (default <+ [0, 1]) ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{E}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail)))
      [target]⊢⁺
      (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{C}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_end : (((default <+ [0, 1]) <+ ([0,
      1] : List (Fin 2))^d) {{C}}> ((1 : Fin 2) >> ((0 : Fin 2) >> R_tail))) =
      cfg_A (d + 1) 0 0 (c + 1) := by
    unfold cfg_A
    have h_d : d + 1 = 1 + d := by omega
    rw [h_d, append_pow_add_flipped default ([0, 1] : List (Fin 2)) 1 d]
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) c]
    rfl
  rwa [h_end] at h123
theorem rule_5 (a d : Nat) :
    (cfg_A (a + 1) 0 d 0) [target]⊢⁺ (cfg_A a (d + 2) 0 0) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  have h_start : cfg_A (a + 1) 0 d 0 =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([1, 1, 1] +> default)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([1, 1, 1] +> default)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([1, 1,
      1] +> default))))
      [target]⊢⁺
      ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> ([1, 1, 1,
      1] +> default)) := by
    simp only [cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_end : ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> ([1, 1, 1,
      1] +> default)) =
      cfg_A a (d + 2) 0 0 := by
    unfold cfg_A
    rw [append_pow_add_flipped L ([1, 1] : List (Fin 2)) (d + 1) 1]
    rw [append_pow_add_flipped L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123
theorem rule_6 (a d : Nat) :
    (cfg_A (a + 1) 0 d 1) [target]⊢⁺ (cfg_A a (d + 2) 0 1) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  have h_start : cfg_A (a + 1) 0 d 1 =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([0, 1, 1, 1,
      1] +> default)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([0, 1, 1, 1, 1] +> default)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 1, 1, 1] +> default)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 1, 1,
      1] +> default))))
      [target]⊢⁺
      ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> (([1,
      0] : List (Fin 2))^1 +> ([1, 1, 1, 1] +> default))) := by
    simp only [list_pow_zero, list_pow_succ,
      List.append_nil, cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_end : ((((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) <+ [1, 1]) {{C}}> (([1,
      0] : List (Fin 2))^1 +> ([1, 1, 1, 1] +> default))) =
      cfg_A a (d + 2) 0 1 := by
    unfold cfg_A
    rw [append_pow_add_flipped L ([1, 1] : List (Fin 2)) (d + 1) 1]
    rw [append_pow_add_flipped L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123
theorem rule_7 (a d c : Nat) :
    (cfg_A (a + 1) 0 d (c + 2)) [target]⊢⁺ (cfg_A a (d + 1) 2 c) := by
  let L := (([0, 1] : List (Fin 2))^a +> default)
  let R_tail := (([1, 0] : List (Fin 2))^c +> ([1, 1, 1, 1] +> default))
  have h_start : cfg_A (a + 1) 0 d (c + 2) =
      ((L <+ [0, 1]) {{C}}> (([1, 1] : List (Fin 2))^d +> ((1 : Fin 2) >> ([0, 1,
      0] +> R_tail)))) := by
    unfold cfg_A
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a]
    have h_c : c + 2 = 2 + c := by omega
    rw [h_c, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) 2 c]
    rfl
  rw [h_start]
  have h1 := step_C_01_to_A d L ([0, 1, 0] +> R_tail)
  have h2 := shift_A_11 d L ([1, 1] +> ((1 : Fin 2) >> ([0, 1, 0] +> R_tail)))
  have h12 := ReachesPlus.trans_star h1 h2
  have h3 : ((L <+ ([1, 1] : List (Fin 2))^d) {{A}}> ([1, 1] +> ((1 : Fin 2) >> ([0, 1,
      0] +> R_tail))))
      [target]⊢⁺
      (((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^2 +> R_tail)) := by
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
      List.append_nil, cons_append_blank, nil_append_blank, ListBlank.head_cons,
      ListBlank.tail_cons]
    execute
  have h123 := ReachesPlus.trans h12 h3
  have h_end : (((L <+ ([1, 1] : List (Fin 2))^d) <+ [1, 1]) {{C}}> (([1,
      1] : List (Fin 2))^2 +> R_tail)) =
      cfg_A a (d + 1) 2 c := by
    unfold cfg_A
    rw [append_pow_add_flipped L ([1, 1] : List (Fin 2)) d 1]
    rfl
  rwa [h_end] at h123
theorem init_reaches_A : (init []) [target]⊢* (cfg_A 0 0 0 1) := by
  refine ReachesPlus.to_star ?_
  unfold init cfg_A
  simp only [Tape.mk₁, list_pow_zero, list_pow_succ,
      List.append_nil, cons_append_blank, nil_append_blank]
  execute
theorem step_A_all (a k d c : Nat) :
    ∃ cfg', ((cfg_A a k d c) [target]⊢⁺ cfg') /\
            (IsInPatternSet ps cfg' \/ (step target cfg').isNone) := by
  rcases k with _ | k'
  · rcases a with _ | a'
    · rcases c with _ | c'
      · obtain ⟨cfg', h_step, h_halt⟩ := rule_3 d
        exact ⟨cfg', h_step, Or.inr h_halt⟩
      · exact ⟨cfg_A (d + 1) 0 0 (c' + 1), rule_4 d c', Or.inl (in_ps_A (d + 1) 0 0 (c' + 1))⟩
    · rcases c with _ | _ | c'
      · exact ⟨cfg_A a' (d + 2) 0 0, rule_5 a' d, Or.inl (in_ps_A a' (d + 2) 0 0)⟩
      · exact ⟨cfg_A a' (d + 2) 0 1, rule_6 a' d, Or.inl (in_ps_A a' (d + 2) 0 1)⟩
      · exact ⟨cfg_A a' (d + 1) 2 c', rule_7 a' d c', Or.inl (in_ps_A a' (d + 1) 2 c')⟩
  · rcases c with _ | c'
    · exact ⟨cfg_A a (k' + 1) 0 (d + 1), rule_2 a k' d, Or.inl (in_ps_A a (k' + 1) 0 (d + 1))⟩
    · exact ⟨cfg_A a k' (d + 2) c', rule_1 a k' d c', Or.inl (in_ps_A a k' (d + 2) c')⟩

theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 0 0 1, init_reaches_A, in_ps_A 0 0 0 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · rw [eval_pat_A]
    generalize h_a : vars 0 = a
    generalize h_k : vars 1 = k
    generalize h_d : vars 2 = d
    generalize h_c : vars 3 = c
    obtain ⟨cfg', h_step, h_halt⟩ := step_A_all a k d c
    exact ⟨cfg', h_step, h_halt⟩
  · nomatch h_mem

theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

inductive State
  | mk (a k d c : ℕ)

def start : State := .mk 0 0 0 1

def encode : State → Cfg (Fin 2) (Fin 6)
  | .mk a k d c => evalTapePattern pat_A (fun | 0 => a | 1 => k | 2 => d | 3 => c | _ => 0)

def next : State → Option State
  | .mk a (k + 1) d (c + 1) => some (.mk a k (d + 2) c)
  | .mk a (k + 1) d 0       => some (.mk a (k + 1) 0 (d + 1))
  | .mk (a + 1) 0 d (c + 2) => some (.mk a (d + 1) 2 c)
  | .mk (a + 1) 0 d 1       => some (.mk a (d + 2) 0 1)
  | .mk (a + 1) 0 d 0       => some (.mk a (d + 2) 0 0)
  | .mk 0 0 d (c + 1)       => some (.mk (d + 1) 0 0 (c + 1))
  | .mk 0 0 _ 0             => none

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine ⟨init_reaches_A, ?_, ?_⟩
  · intro s s' hnext
    match s with
    | .mk 0 0 d (c' + 1) => injection hnext with h; subst h; exact rule_4 d c'
    | .mk (a' + 1) 0 d 0 => injection hnext with h; subst h; exact rule_5 a' d
    | .mk (a' + 1) 0 d 1 => injection hnext with h; subst h; exact rule_6 a' d
    | .mk (a' + 1) 0 d (c' + 2) => injection hnext with h; subst h; exact rule_7 a' d c'
    | .mk a (k' + 1) d 0 => injection hnext with h; subst h; exact rule_2 a k' d
    | .mk a (k' + 1) d (c' + 1) => injection hnext with h; subst h; exact rule_1 a k' d c'
    | .mk 0 0 d 0 => nomatch hnext
  · intro s hnext
    match s with
    | .mk 0 0 d 0             => exact ⟨_, ReachesPlus.to_star (rule_3 d).choose_spec.1,
      (rule_3 d).choose_spec.2⟩
    | .mk a (k + 1) d (c + 1) => nomatch hnext
    | .mk a (k + 1) d 0       => nomatch hnext
    | .mk (a + 1) 0 d (c + 2) => nomatch hnext
    | .mk (a + 1) 0 d 1       => nomatch hnext
    | .mk (a + 1) 0 d 0       => nomatch hnext
    | .mk 0 0 d (c + 1)       => nomatch hnext

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RA_0LC0RE_1LF1LD_1LA0LA_1LC1RB_HHH1LC
