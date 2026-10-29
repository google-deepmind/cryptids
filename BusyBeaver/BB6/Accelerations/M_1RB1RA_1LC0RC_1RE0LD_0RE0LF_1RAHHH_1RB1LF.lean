/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF` (Halving Tower family).

Each half-tape stack encodes unary blocks $1^{a + 1}$ separated by single zeros (`encStack`),
ordered from the tape head outward. The closed 2-mode 2nd-order digit-stack system has the
configurations `A(L, R)` (state `A` reading the `0` separator between `encStack L` and
`encStack R`) and `BR(L, R)` (state `B` reading the `0` separator between `encStack L` and
`(encStack R).tail`). Below, `bumpHead` increments the head digit of a stack (pushing `0` onto an
empty stack) and `tailWeight R` is the head digit of `R` (`0` if `R = []`).

## Accelerated Transition Rules

```text
A(L, [])            -> BR(bumpHead L, [])
A(L, [0])           -> A(1 :: bumpHead L, [])
A(L, 0 :: e :: R)   -> Halt
A(L, (d + 1) :: R)  -> A(d :: bumpHead L, R)

BR([], R)           -> Halt
BR(0 :: L, R)       -> A((tailWeight R + 1) :: L, R.tail)
BR(1 :: L, R)       -> BR(bumpHead L, 0 :: tailWeight R :: R.tail)
BR(2 :: L, R)       -> A((tailWeight R + 2) :: bumpHead L, R.tail)
BR((a + 3) :: L, R) -> BR((a + 1) :: bumpHead L, (tailWeight R + 1) :: R.tail)

Start: A([2, 0], []), reached after 16 raw TM steps
```

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem S4 — trigger **POW**, growth mass-conserving sandpile, shield partial.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* as #660 (same sandpile law); E3 macro twin of #209; busycoq `Eqv_*` merges #96 into this
class

*Simulated horizon:* family-level

*Why it is hard:* see #660

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RAHHH_1RB1LF

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Digit-Stack Encodings and Walk Helpers -/

@[simp]
private theorem encStack_nil : encStack [] = default :=
  rfl

private theorem encStack_cons (a : ℕ) (s : List ℕ) :
    encStack (a :: s) = ((encStack s).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) :=
  rfl

@[simp]
private theorem encStack_cons_one (s : List ℕ) :
    (1 : Fin 2) >> encStack s = encStack (bumpHead s) := by
  cases s with
  | nil => simp [bumpHead, encStack]
  | cons a s' => rfl

/-- Head digit of a right stack under `.tail` (`0` if empty, `d` if `d :: _`). -/
private def tailWeight : List ℕ → ℕ
  | [] => 0
  | d :: _ => d

@[simp]
private theorem encStack_tail_cons_one (R : List ℕ) :
    (1 : Fin 2) >> (encStack R).tail = encStack (tailWeight R :: R.tail) := by
  cases R with
  | nil => simp [tailWeight, encStack]
  | cons d R' => simp [tailWeight, encStack, list_pow_succ]

private theorem encStack_tail_decomp (R : List ℕ) :
    (encStack R).tail = (([1] : List (Fin 2)) ^ (tailWeight R)) +> ((encStack R.tail).cons 0) := by
  cases R with
  | nil => simp [tailWeight, encStack]
  | cons d R' => simp [tailWeight, encStack, list_pow_succ]

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [Cfg.headRight, Cfg.headLeft, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.cons_zero_default, encStack_nil, encStack_cons_one, encStack_tail_cons_one,
    ListBlank.head_cons, ListBlank.tail_cons, multiStep_zero]
  try rfl))

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons,
    ListBlank.head_default_fin, ListBlank.tail_cons, ListBlank.tail_default,
    ListBlank.cons_zero_default]
  apply ReachesPlus.head (by rfl)
  simp only [Cfg.headRight, Cfg.headLeft, Tape.move, Tape.write,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default]))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  try finish))

/-- Right-sweep separator configuration: state `A` reading `0` between `L` and `R`. -/
private def cfg_A (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, encStack L, encStack R⟩⟩

/-- Left-split separator configuration: state `B` reading `0` between `L` and `(encStack R).tail`.
-/
private def cfg_BR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encStack L, (encStack R).tail⟩⟩

/-- Modes of the 2nd-order digit-stack configuration family. -/
private inductive StackMode
  | A
  | BR

private def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .A, L, R => cfg_A L R
  | .BR, L, R => cfg_BR L R

private def IsInStackSystem1 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg1 m L R

/-- State `A` walks right across `1^k` (`A, 1 -> 1RA`). -/
private theorem a_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{A}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{A}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (l {{A}}> (([1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ k +> r))) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ 1)) {{A}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih (l <+ (([1] : List (Fin 2)) ^ 1)) r).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-- State `F` walks left across `1^k` (`F, 1 -> 1LF`). -/
private theorem f_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} r) [target]⊢*
      (l <{{F}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{F}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih l (([1] : List (Fin 2)) ^ 1 +> r)).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-! ## Local Separator Rules -/

private theorem rule_A_nil (L : List ℕ) :
    (cfg_A L []) [target]⊢⁺ (cfg_BR (bumpHead L) []) := by
  unfold cfg_A cfg_BR
  rw [encStack_nil]
  execute 1

private theorem rule_A_zero_nil (L : List ℕ) :
    (cfg_A L [0]) [target]⊢⁺ (cfg_A (1 :: bumpHead L) []) := by
  unfold cfg_A
  rw [encStack_cons 0 [], encStack_nil, encStack_cons 1 (bumpHead L)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private def cfg_Halt_A (L : List ℕ) (e : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨1, (1 : Fin 2) >> (0 : Fin 2) >> encStack (bumpHead L),
    (([1] : List (Fin 2)) ^ e) +> (encStack R).cons 0⟩⟩

private theorem rule_A_zero_cons (L R : List ℕ) (e : ℕ) :
    ((cfg_A L (0 :: e :: R)) [target]⊢⁺ (cfg_Halt_A L e R)) ∧
      (step target (cfg_Halt_A L e R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_A cfg_Halt_A
  rw [encStack_cons 0 (e :: R), encStack_cons e R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 3

private theorem rule_A_succ_cons (L R : List ℕ) (d : ℕ) :
    (cfg_A L ((d + 1) :: R)) [target]⊢⁺ (cfg_A (d :: bumpHead L) R) := by
  unfold cfg_A
  rw [encStack_cons (d + 1) R]
  have h_split : d + 1 + 1 = 2 + d := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some A, ⟨0, encStack L,
        (([1] : List (Fin 2)) ^ 2) +> ((([1] : List (Fin 2)) ^ d) +> (encStack R).cons 0)⟩⟩ :
          Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{A}}>
          ((([1] : List (Fin 2)) ^ d) +> (encStack R).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 5
  refine h_pre.trans_star ?_
  refine (a_walk_right d (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    ((encStack R).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons d (bumpHead L)]
  finish

private def cfg_Halt_BR (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨1, encStack [0], (encStack R).tail⟩⟩

private theorem rule_BR_nil (R : List ℕ) :
    ((cfg_BR [] R) [target]⊢⁺ (cfg_Halt_BR R)) ∧
      (step target (cfg_Halt_BR R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_BR cfg_Halt_BR
  rw [encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 2

private theorem rule_BR_zero (L R : List ℕ) :
    (cfg_BR (0 :: L) R) [target]⊢⁺ (cfg_A ((tailWeight R + 1) :: L) R.tail) := by
  unfold cfg_BR cfg_A
  rw [encStack_cons 0 L, encStack_tail_decomp R]
  have h_pre :
      (⟨some B, ⟨0, ((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1),
        (([1] : List (Fin 2)) ^ (tailWeight R)) +> (encStack R.tail).cons 0⟩⟩ :
          Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 2)) {{A}}>
          ((([1] : List (Fin 2)) ^ (tailWeight R)) +> (encStack R.tail).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 5
  refine h_pre.trans_star ?_
  refine (a_walk_right (tailWeight R) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 2))
    ((encStack R.tail).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons (tailWeight R + 1) L]
  finish

private theorem rule_BR_one (L R : List ℕ) :
    (cfg_BR (1 :: L) R) [target]⊢⁺ (cfg_BR (bumpHead L) (0 :: tailWeight R :: R.tail)) := by
  unfold cfg_BR
  rw [encStack_cons 1 L, encStack_cons 0 (tailWeight R :: R.tail)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_BR_two (L R : List ℕ) :
    (cfg_BR (2 :: L) R) [target]⊢⁺ (cfg_A ((tailWeight R + 2) :: bumpHead L) R.tail) := by
  unfold cfg_BR cfg_A
  rw [encStack_cons 2 L, encStack_tail_decomp R]
  have h_pre :
      (⟨some B, ⟨0, ((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 3),
        (([1] : List (Fin 2)) ^ (tailWeight R)) +> (encStack R.tail).cons 0⟩⟩ :
          Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3)) {{A}}>
          ((([1] : List (Fin 2)) ^ (tailWeight R)) +> (encStack R.tail).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 9
  refine h_pre.trans_star ?_
  refine (a_walk_right (tailWeight R)
    (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 3))
    ((encStack R.tail).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons (tailWeight R + 2) (bumpHead L)]
  finish

private theorem rule_BR_ge3 (L R : List ℕ) (a : ℕ) :
    (cfg_BR ((a + 3) :: L) R) [target]⊢⁺
      (cfg_BR ((a + 1) :: bumpHead L) ((tailWeight R + 1) :: R.tail)) := by
  unfold cfg_BR
  rw [encStack_cons (a + 3) L]
  have h_split : a + 3 + 1 = 2 + (a + 1 + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some B, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <+
        (([1] : List (Fin 2)) ^ 2), (encStack R).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1 + 1))) <{{F}}
          (((encStack (tailWeight R :: R.tail)).cons 0).cons 0)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  rw [list_pow_add, ListBlank.append_assoc]
  refine (f_walk_left (a + 1) (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (tailWeight R :: R.tail)).cons 0).cons 0)).trans ?_
  have h_split3 : a + 1 = 1 + a := by omega
  rw [h_split3, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) <{{F}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ a) +> (((encStack (tailWeight R :: R.tail)).cons 0).cons 0))))
        [target]⊢⁺
        ((((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1)) {{A}}>
          ((([1] : List (Fin 2)) ^ a) +>
            (((encStack (tailWeight R :: R.tail)).cons 0).cons 0))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 6
  refine h_mid.to_star.trans ?_
  refine (a_walk_right a (((encStack (bumpHead L)).cons 0) <+ (([1] : List (Fin 2)) ^ 1))
    (((encStack (tailWeight R :: R.tail)).cons 0).cons 0)).trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← encStack_cons a (bumpHead L)]
  have h_post :
      ((encStack (a :: bumpHead L)) {{A}}> (((encStack (tailWeight R :: R.tail)).cons 0).cons 0))
        [target]⊢⁺
        (⟨some B, ⟨0, encStack ((a + 1) :: bumpHead L),
          (encStack ((tailWeight R + 1) :: R.tail)).tail⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encStack_cons (tailWeight R + 1) R.tail]
    simp only [list_pow_succ, List.cons_append, List.nil_append]
    execute 1
  rw [Nat.add_comm 1 a]
  exact h_post.to_star

/-! ## Initial Reachability and Stack Reduction Closure -/

private theorem init_to_cfg_A :
    (init []) [target]⊢⁺ (cfg_A [2, 0] []) := by
  unfold cfg_A
  rw [encStack_cons 2 [0], encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 16

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg1 .BR [1, 1] [1] :=
  init_to_cfg_A
    |>.trans (rule_A_nil [2, 0])
    |>.trans (rule_BR_ge3 [0] [] 0)

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem1 cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem1 cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | A =>
    cases R with
    | nil =>
      exact ⟨cfg_BR (bumpHead L) [], rule_A_nil L, Or.inl ⟨.BR, bumpHead L, [], rfl⟩⟩
    | cons d R' =>
      rcases d with _ | d
      · cases R' with
        | nil =>
          exact ⟨cfg_A (1 :: bumpHead L) [], rule_A_zero_nil L,
            Or.inl ⟨.A, 1 :: bumpHead L, [], rfl⟩⟩
        | cons e R'' =>
          obtain ⟨hstep, hnone⟩ := rule_A_zero_cons L R'' e
          exact ⟨cfg_Halt_A L e R'', hstep, Or.inr hnone⟩
      · exact ⟨cfg_A (d :: bumpHead L) R', rule_A_succ_cons L R' d,
          Or.inl ⟨.A, d :: bumpHead L, R', rfl⟩⟩
  | BR =>
    cases L with
    | nil =>
      obtain ⟨hstep, hnone⟩ := rule_BR_nil R
      exact ⟨cfg_Halt_BR R, hstep, Or.inr hnone⟩
    | cons a L' =>
      rcases a with _ | _ | _ | a
      · exact ⟨cfg_A ((tailWeight R + 1) :: L') R.tail, rule_BR_zero L' R,
          Or.inl ⟨.A, (tailWeight R + 1) :: L', R.tail, rfl⟩⟩
      · exact ⟨cfg_BR (bumpHead L') (0 :: tailWeight R :: R.tail), rule_BR_one L' R,
          Or.inl ⟨.BR, bumpHead L', 0 :: tailWeight R :: R.tail, rfl⟩⟩
      · exact ⟨cfg_A ((tailWeight R + 2) :: bumpHead L') R.tail, rule_BR_two L' R,
          Or.inl ⟨.A, (tailWeight R + 2) :: bumpHead L', R.tail, rfl⟩⟩
      · exact ⟨cfg_BR ((a + 1) :: bumpHead L') ((tailWeight R + 1) :: R.tail),
          rule_BR_ge3 L' R a,
          Or.inl ⟨.BR, (a + 1) :: bumpHead L', (tailWeight R + 1) :: R.tail, rfl⟩⟩

private theorem encStack_head (a : ℕ) (s : List ℕ) : (encStack (a :: s)).head = 1 := by
  simp [encStack, list_pow_succ]

private theorem encStack_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ s : List ℕ, encStack s ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro s h
  rcases s with _ | ⟨_ | a, rest⟩
  · have h1 := congrArg ListBlank.head h
    simp [encStack] at h1
  · rcases rest with _ | ⟨b, s'⟩
    · have h1 := congrArg (fun x => x.tail.tail.tail.head) h
      simp [encStack, list_pow_succ, list_pow_zero] at h1
    · have h1 := congrArg (fun x => x.tail.tail.head) h
      simp [encStack, list_pow_succ, list_pow_zero] at h1
  · have h1 := congrArg (fun x => x.tail.head) h
    simp [encStack, list_pow_succ] at h1

private theorem block_encoding :
    ∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
      strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
      strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
      (∀ a L, encStack (a :: L) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encStack L))) ∧
      (∀ d R, encStack (d :: R) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encStack R))) := by
  refine ⟨1, 1, 1, 1, 1, 1,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro a L
    simp [encStack]
  · intro d R
    simp [encStack]

private theorem modes_bounded :
    ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes := by
  refine ⟨[.A, .BR], by decide, ?_⟩
  intro m
  cases m <;> simp

private theorem valid_stack_modes : IsValidStackModes encStack encStack evalStackCfg1 := by
  intro m
  cases m with
  | A => exact ⟨A, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | BR => exact ⟨B, .id [], .tail [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

/-- `target` reduces to a closed 2nd-order digit-stack system (`HasStackReduction`). -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack encStack evalStackCfg1 IsInStackSystem1
    ⟨rfl, rfl, encStack_head, encStack_head,
      encStack_not_surjective, encStack_not_surjective,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.BR, [1, 1], [1], init_reaches_nontrivial, by decide, ⟨1, by decide, by decide⟩⟩,
      Or.inl ⟨.BR, .BR, 1, (· + 1), fun R => 0 :: tailWeight R :: R.tail,
        fun s => by cases s <;> simp, fun z L R => rule_BR_one (z :: L) R⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RAHHH_1RB1LF
