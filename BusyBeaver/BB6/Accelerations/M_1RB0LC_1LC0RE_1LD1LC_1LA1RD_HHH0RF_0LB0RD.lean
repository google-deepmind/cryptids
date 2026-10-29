/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD` (Halving Tower family).

The left half-tape stack encodes unary blocks $1^{a + 1}$ separated by double zeros (`encStack2`),
and the right half-tape stack encodes unary blocks $1^{d + 1}$ separated by single zeros
(`encStack`), both ordered from the tape head outward. The closed 2-mode 2nd-order digit-stack
system has the configurations `D(L, R)` (state `D` reading the `0` separator between `encStack2 L`
and `encStack R`) and `AL(L, R)` (state `A` reading the `0` separator between `(encStack2 L).tail`
and `encStack R`). Below, `bumpHead` increments the head digit of a stack (pushing `0` onto an
empty stack) and `tailWeight L` is the head digit of `L` (`0` if `L = []`).

## Accelerated Transition Rules

```text
D([], R)            -> AL([], bumpHead R)
D(a :: L, R)        -> D(L, a :: bumpHead R)

AL(L, [])           -> D(L.tail, [tailWeight L + 2])
AL(L, 0 :: R)       -> Halt
AL(L, 1 :: R)       -> D((tailWeight L + 2) :: L.tail, R)
AL(L, 2 :: R)       -> AL(0 :: tailWeight L :: L.tail, bumpHead R)
AL(L, (d + 3) :: R) -> AL((tailWeight L + 1) :: L.tail, (d + 1) :: bumpHead R)

Start: D([3], [0]), reached after 23 raw TM steps
```

<!-- hardness:begin -->
## Hardness

*Hardness class:* S4 sibling — trigger **POW**, growth mass-conserving sandpile, shield partial
(strict digit positivity blocks the sole $d=0$ halt).

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* as #660/#680

*Simulated horizon:* family-level

*Why it is hard:* E1 pair of #680 (different seed)

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_1LC0RE_1LD1LC_1LA1RD_---0RF_0LB0RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Digit-Stack Encodings and Walk Helpers -/

@[simp]
private theorem encStack2_nil : encStack2 [] = default :=
  rfl

private theorem encStack2_cons (a : ℕ) (L : List ℕ) :
    encStack2 (a :: L) = (((encStack2 L).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)) :=
  rfl

@[simp]
private theorem encStack_nil : encStack [] = default :=
  rfl

private theorem encStack_cons (d : ℕ) (R : List ℕ) :
    encStack (d :: R) = (([1] : List (Fin 2)) ^ (d + 1)) +> ((encStack R).cons 0) :=
  rfl

@[simp]
private theorem encStack2_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encStack2 L = encStack2 (bumpHead L) := by
  cases L with
  | nil => simp [bumpHead, encStack2]
  | cons b L' => rfl

@[simp]
private theorem encStack_cons_one (R : List ℕ) :
    (1 : Fin 2) >> encStack R = encStack (bumpHead R) := by
  cases R with
  | nil => simp [bumpHead, encStack]
  | cons d R' => rfl

/-- Head digit of a left stack under `.tail` (`0` if empty, `a` if `a :: _`). -/
private def tailWeight : List ℕ → ℕ
  | [] => 0
  | a :: _ => a

@[simp]
private theorem encStack2_tail_cons_one (L : List ℕ) :
    (1 : Fin 2) >> (encStack2 L).tail = encStack2 (tailWeight L :: L.tail) := by
  cases L with
  | nil => simp [tailWeight, encStack2]
  | cons a L' => simp [tailWeight, encStack2, list_pow_succ]

private theorem encStack2_tail_decomp (L : List ℕ) :
    (encStack2 L).tail =
      (((encStack2 L.tail).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ (tailWeight L)) := by
  cases L with
  | nil => simp [tailWeight, encStack2]
  | cons a L' => simp [tailWeight, encStack2, list_pow_succ]

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [Cfg.headRight, Cfg.headLeft, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.cons_zero_default, encStack2_nil, encStack_nil, encStack2_cons_one,
    encStack_cons_one, encStack2_tail_cons_one, ListBlank.head_cons, ListBlank.tail_cons,
    multiStep_zero]
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

/-- Right-sweep separator configuration: state `D` reading `0` between `L` and `R`. -/
private def cfg_D (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack2 L, encStack R⟩⟩

/-- Left-split separator configuration: state `A` reading `0` between `(encStack2 L).tail` and `R`.
-/
private def cfg_AL (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some A, ⟨0, (encStack2 L).tail, encStack R⟩⟩

/-- Modes of the 2nd-order digit-stack configuration family. -/
private inductive StackMode
  | D
  | AL

private def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .D, L, R => cfg_D L R
  | .AL, L, R => cfg_AL L R

private def IsInStackSystem1 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg1 m L R

/-- State `C` walks left across `1^k` (`C, 1 -> 1LC`). -/
private theorem c_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{C}} r) [target]⊢*
      (l <{{C}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{C}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{C}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih l (([1] : List (Fin 2)) ^ 1 +> r)).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-- State `D` walks right across `1^k` (`D, 1 -> 1RD`). -/
private theorem d_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{D}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (l {{D}}> (([1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ k +> r))) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ 1)) {{D}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih (l <+ (([1] : List (Fin 2)) ^ 1)) r).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-! ## Local Separator Rules -/

private theorem rule_D_nil (R : List ℕ) :
    (cfg_D [] R) [target]⊢⁺ (cfg_AL [] (bumpHead R)) := by
  unfold cfg_D cfg_AL
  rw [encStack2_nil]
  execute 1

private theorem rule_D_cons (a : ℕ) (L R : List ℕ) :
    (cfg_D (a :: L) R) [target]⊢⁺ (cfg_D L (a :: bumpHead R)) := by
  unfold cfg_D
  rw [encStack2_cons a L]
  have h_pre :
      (⟨some D, ⟨0, (((encStack2 L).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 1)),
        encStack R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (((((encStack2 L).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ a)) <{{C}}
          ((encStack (bumpHead R)).cons 0)) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append]
    execute 2
  refine h_pre.trans_star ?_
  refine (c_walk_left a (((encStack2 L).cons 0).cons 0)
    ((encStack (bumpHead R)).cons 0)).trans ?_
  have h_post :
      ((((encStack2 L).cons 0).cons 0) <{{C}}
        ((([1] : List (Fin 2)) ^ a) +> ((encStack (bumpHead R)).cons 0)))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack2 L, encStack (a :: bumpHead R)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encStack_cons a (bumpHead R)]
    simp only [list_pow_succ, List.cons_append, List.nil_append]
    execute 1
  exact h_post.to_star

private theorem rule_AL_nil (L : List ℕ) :
    (cfg_AL L []) [target]⊢⁺ (cfg_D L.tail [tailWeight L + 2]) := by
  unfold cfg_AL cfg_D
  rw [encStack2_tail_decomp L, encStack_nil]
  have h_pre :
      (⟨some A, ⟨0,
        (((encStack2 L.tail).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ (tailWeight L)),
        default⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (((((encStack2 L.tail).cons 0).cons 0) <+ (([1] : List (Fin 2)) ^ (tailWeight L))) <{{C}}
          (([1] : List (Fin 2)) ^ 2 +> default)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  refine (c_walk_left (tailWeight L) (((encStack2 L.tail).cons 0).cons 0)
    (([1] : List (Fin 2)) ^ 2 +> default)).trans ?_
  have h_post :
      ((((encStack2 L.tail).cons 0).cons 0) <{{C}}
        ((([1] : List (Fin 2)) ^ (tailWeight L)) +> (([1] : List (Fin 2)) ^ 2 +> default)))
        [target]⊢⁺
        (⟨some D, ⟨0, encStack2 L.tail,
          (([1] : List (Fin 2)) ^ 1) +>
            ((([1] : List (Fin 2)) ^ (tailWeight L)) +>
              (([1] : List (Fin 2)) ^ 2 +> default))⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 1
  refine h_post.to_star.trans ?_
  rw [← ListBlank.append_assoc, ← list_pow_add, ← ListBlank.append_assoc, ← list_pow_add]
  have h_eq : 1 + tailWeight L + 2 = tailWeight L + 2 + 1 := by omega
  rw [h_eq, encStack_cons (tailWeight L + 2) [], encStack_nil, ListBlank.cons_zero_default]

private def cfg_Halt_AL (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, (encStack2 (tailWeight L :: L.tail)).cons 0, encStack R⟩⟩

private theorem rule_AL_zero (L R : List ℕ) :
    ((cfg_AL L (0 :: R)) [target]⊢⁺ (cfg_Halt_AL L R)) ∧
      (step target (cfg_Halt_AL L R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_AL cfg_Halt_AL
  rw [encStack_cons 0 R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 2

private theorem rule_AL_one (L R : List ℕ) :
    (cfg_AL L (1 :: R)) [target]⊢⁺ (cfg_D ((tailWeight L + 2) :: L.tail) R) := by
  unfold cfg_AL cfg_D
  rw [encStack_cons 1 R]
  have h_pre :
      (⟨some A, ⟨0, (encStack2 L).tail,
        (([1] : List (Fin 2)) ^ (1 + 1)) +> ((encStack R).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (⟨some C, ⟨0, encStack2 (tailWeight L :: L.tail), encStack (0 :: R)⟩⟩ :
          Cfg (Fin 2) (Fin 6)) := by
    rw [encStack_cons 0 R]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 5
  refine h_pre.trans ?_
  rw [encStack2_cons (tailWeight L) L.tail, encStack_cons 0 R,
    encStack2_cons (tailWeight L + 2) L.tail]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_AL_two (L R : List ℕ) :
    (cfg_AL L (2 :: R)) [target]⊢⁺ (cfg_AL (0 :: tailWeight L :: L.tail) (bumpHead R)) := by
  unfold cfg_AL
  rw [encStack_cons 2 R, encStack2_cons 0 (tailWeight L :: L.tail)]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private theorem rule_AL_ge3 (d : ℕ) (L R : List ℕ) :
    (cfg_AL L ((d + 3) :: R)) [target]⊢⁺
      (cfg_AL ((tailWeight L + 1) :: L.tail) ((d + 1) :: bumpHead R)) := by
  unfold cfg_AL
  rw [encStack_cons (d + 3) R]
  have h_split : d + 3 + 1 = 3 + (d + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some A, ⟨0, (encStack2 L).tail,
        (([1] : List (Fin 2)) ^ 3) +>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> ((encStack R).cons 0))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0) {{D}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> ((encStack R).cons 0))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 4
  refine h_pre.trans_star ?_
  refine (d_walk_right (d + 1)
    ((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0)
    ((encStack R).cons 0)).trans ?_
  have h_mid :
      ((((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0) <+
        (([1] : List (Fin 2)) ^ (d + 1))) {{D}}> ((encStack R).cons 0))
        [target]⊢⁺
        ((((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0) <+
          (([1] : List (Fin 2)) ^ d)) <{{C}} ((encStack (bumpHead R)).cons 0)) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append]
    execute 2
  refine h_mid.to_star.trans ?_
  refine (c_walk_left d ((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0)
    ((encStack (bumpHead R)).cons 0)).trans ?_
  have h_post :
      (((((encStack2 (tailWeight L :: L.tail)).cons 0).cons 0).cons 0) <{{C}}
        ((([1] : List (Fin 2)) ^ d) +> ((encStack (bumpHead R)).cons 0)))
        [target]⊢⁺
        (⟨some A, ⟨0, (encStack2 ((tailWeight L + 1) :: L.tail)).tail,
          encStack ((d + 1) :: bumpHead R)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    rw [encStack2_cons (tailWeight L + 1) L.tail, encStack_cons (d + 1) (bumpHead R)]
    simp only [list_pow_succ, List.cons_append, List.nil_append]
    execute 2
  exact h_post.to_star

/-! ## Initial Reachability and Stack Reduction Closure -/

private theorem init_to_cfg_D :
    (init []) [target]⊢⁺ (cfg_D [3] [0]) := by
  unfold cfg_D
  rw [encStack2_cons, encStack2_nil, encStack_cons, encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 23

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg1 .AL [1] [2, 2] :=
  init_to_cfg_D
    |>.trans (rule_D_cons 3 [] [0])
    |>.trans (rule_D_nil [3, 1])
    |>.trans (rule_AL_ge3 1 [] [1])

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem1 cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem1 cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | D =>
    cases L with
    | nil =>
      exact ⟨cfg_AL [] (bumpHead R), rule_D_nil R, Or.inl ⟨.AL, [], bumpHead R, rfl⟩⟩
    | cons a L' =>
      exact ⟨cfg_D L' (a :: bumpHead R), rule_D_cons a L' R,
        Or.inl ⟨.D, L', a :: bumpHead R, rfl⟩⟩
  | AL =>
    cases R with
    | nil =>
      exact ⟨cfg_D L.tail [tailWeight L + 2], rule_AL_nil L,
        Or.inl ⟨.D, L.tail, [tailWeight L + 2], rfl⟩⟩
    | cons d R' =>
      rcases d with _ | _ | _ | d
      · obtain ⟨hstep, hnone⟩ := rule_AL_zero L R'
        exact ⟨cfg_Halt_AL L R', hstep, Or.inr hnone⟩
      · exact ⟨cfg_D ((tailWeight L + 2) :: L.tail) R', rule_AL_one L R',
          Or.inl ⟨.D, (tailWeight L + 2) :: L.tail, R', rfl⟩⟩
      · exact ⟨cfg_AL (0 :: tailWeight L :: L.tail) (bumpHead R'), rule_AL_two L R',
          Or.inl ⟨.AL, 0 :: tailWeight L :: L.tail, bumpHead R', rfl⟩⟩
      · exact ⟨cfg_AL ((tailWeight L + 1) :: L.tail) ((d + 1) :: bumpHead R'),
          rule_AL_ge3 d L R',
          Or.inl ⟨.AL, (tailWeight L + 1) :: L.tail, (d + 1) :: bumpHead R', rfl⟩⟩

private theorem encStack2_head (a : ℕ) (L : List ℕ) : (encStack2 (a :: L)).head = 1 := by
  simp [encStack2, list_pow_succ]

private theorem encStack_head (d : ℕ) (R : List ℕ) : (encStack (d :: R)).head = 1 := by
  simp [encStack, list_pow_succ]

private theorem encStack2_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ s : List ℕ, encStack2 s ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro s h
  rcases s with _ | ⟨_ | a, rest⟩
  · have h1 := congrArg ListBlank.head h
    simp [encStack2] at h1
  · have h1 := congrArg (fun x => x.tail.tail.head) h
    simp [encStack2, list_pow_succ, list_pow_zero] at h1
  · have h1 := congrArg (fun x => x.tail.head) h
    simp [encStack2, list_pow_succ] at h1

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
      (∀ a L, encStack2 (a :: L) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encStack2 L))) ∧
      (∀ d R, encStack (d :: R) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encStack R))) := by
  refine ⟨1, 1, 2, 1, 1, 1,
    by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · intro a L
    simp [encStack2, list_pow_succ, list_pow_zero]
  · intro d R
    simp [encStack]

private theorem modes_bounded :
    ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes := by
  refine ⟨[.D, .AL], by decide, ?_⟩
  intro m
  cases m <;> simp

private theorem valid_stack_modes : IsValidStackModes encStack2 encStack evalStackCfg1 := by
  intro m
  cases m with
  | D => exact ⟨D, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | AL => exact ⟨A, .tail [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

/-- `target` reduces to a closed 2nd-order digit-stack system (`HasStackReduction`). -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack2 encStack evalStackCfg1 IsInStackSystem1
    ⟨rfl, rfl, encStack2_head, encStack_head,
      encStack2_not_surjective, encStack_not_surjective,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.AL, [1], [2, 2], init_reaches_nontrivial, by decide, ⟨1, by decide, by decide⟩⟩,
      Or.inl ⟨.D, .D, 0, id, fun R => 0 :: bumpHead R,
        fun s => by cases s <;> simp [bumpHead], fun z L R => rule_D_cons 0 (z :: L) R⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RB0LC_1LC0RE_1LD1LC_1LA1RD_HHH0RF_0LB0RD
