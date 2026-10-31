/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Machine `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver machine
`1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`
(https://wiki.bbchallenge.org/wiki/1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF).

Each half-tape stack encodes unary blocks $1^{a + 1}$ separated by single zeros (`encStack`),
ordered from the tape head outward. Starting from `init []`, the machine enters a closed 2-mode
(`D`, `FR`) 2nd-order digit-stack system in 3 raw steps.

<!-- hardness:begin -->
## Hardness

*Hardness class:* Problem S5 — trigger **POW (Mersenne bottom rung $2^k-1$)**, growth —, shield
partial (`ValidStack549` kills the empty-stack halt).

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting, slowly critical.

*Hazard:* 846 exposures in $10^7$ steps ($14\to35\to90\to275$ fresh starts per decade),
$\approx0.05$ expected halts per decade; near-misses $4,13,61,65,252,513,1020,1027$

*Simulated horizon:* $10^7$ macro-steps (exact)

*Why it is hard:* the community's *Sweeper* re-measured; two-mode halving sweeper

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF"

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

/-- Left-scan separator configuration: state `D` reading `0` between `L` and `R`. -/
private def cfg_D (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack L, encStack R⟩⟩

/-- Right-sweep separator configuration: state `F` reading `0` between `L` and `(encStack R).tail`.
-/
private def cfg_FR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨0, encStack L, (encStack R).tail⟩⟩

/-- Modes of the 2nd-order digit-stack configuration family. -/
private inductive StackMode
  | D
  | FR

private def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .D, L, R => cfg_D L R
  | .FR, L, R => cfg_FR L R

private def IsInStackSystem1 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg1 m L R

/-- State `A` walks left across `1^k` (`A, 1 -> 1LA`). -/
private theorem a_walk_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ k)) <{{A}} r) [target]⊢*
      (l <{{A}} ((([1] : List (Fin 2)) ^ k) +> r)) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (((l <+ (([1] : List (Fin 2)) ^ k)) <+ (([1] : List (Fin 2)) ^ 1)) <{{A}} r) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ k)) <{{A}} (([1] : List (Fin 2)) ^ 1 +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih l (([1] : List (Fin 2)) ^ 1 +> r)).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-- State `F` walks right across `1^k` (`F, 1 -> 1RF`). -/
private theorem f_walk_right (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{F}}> ((([1] : List (Fin 2)) ^ k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ k)) {{F}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : k + 1 = 1 + k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    have h1 :
        (l {{F}}> (([1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ k +> r))) [target]⊢⁺
          ((l <+ (([1] : List (Fin 2)) ^ 1)) {{F}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      simp only [list_pow_one]
      execute 1
    refine h1.to_star.trans ?_
    refine (ih (l <+ (([1] : List (Fin 2)) ^ 1)) r).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-! ## Local Separator Rules -/

private def cfg_Halt_D_nil (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, default, (encStack R).cons 0⟩⟩

private theorem rule_D_nil (R : List ℕ) :
    ((cfg_D [] R) [target]⊢⁺ (cfg_Halt_D_nil R)) ∧
      (step target (cfg_Halt_D_nil R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_D cfg_Halt_D_nil
  rw [encStack_nil]
  execute 1

private theorem rule_D_zero_nil (L : List ℕ) :
    (cfg_D (0 :: L) []) [target]⊢⁺ (cfg_D (bumpHead (bumpHead (bumpHead L))) []) := by
  unfold cfg_D
  rw [encStack_cons 0 L, encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private theorem rule_D_zero_zero_nil (L : List ℕ) :
    (cfg_D (0 :: L) [0]) [target]⊢⁺
      (cfg_D (bumpHead (bumpHead (bumpHead (bumpHead (bumpHead (bumpHead L)))))) []) := by
  unfold cfg_D
  rw [encStack_cons 0 L, encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 8

private def cfg_Halt_D_zero (L : List ℕ) (e : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨1, encStack (bumpHead (bumpHead (bumpHead (bumpHead (bumpHead L))))),
    (([1] : List (Fin 2)) ^ e) +> (encStack R).cons 0⟩⟩

private theorem rule_D_zero_zero_cons (L R : List ℕ) (e : ℕ) :
    ((cfg_D (0 :: L) (0 :: e :: R)) [target]⊢⁺ (cfg_Halt_D_zero L e R)) ∧
      (step target (cfg_Halt_D_zero L e R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_D cfg_Halt_D_zero
  rw [encStack_cons 0 L, encStack_cons 0 (e :: R), encStack_cons e R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 7

private theorem rule_D_zero_one (L R : List ℕ) :
    (cfg_D (0 :: L) (1 :: R)) [target]⊢⁺
      (cfg_D (bumpHead (bumpHead (bumpHead (bumpHead L)))) (bumpHead R)) := by
  unfold cfg_D
  rw [encStack_cons 0 L, encStack_cons 1 R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 8

private theorem rule_D_zero_ge2 (L R : List ℕ) (d : ℕ) :
    (cfg_D (0 :: L) ((d + 2) :: R)) [target]⊢⁺
      (cfg_FR (d :: bumpHead (bumpHead (bumpHead (bumpHead L)))) (bumpHead R)) := by
  unfold cfg_D cfg_FR
  rw [encStack_cons (d + 2) R]
  have h_split : d + 2 + 1 = 2 + (d + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, encStack (0 :: L),
        (([1] : List (Fin 2)) ^ 2) +>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (((encStack (bumpHead (bumpHead (bumpHead (bumpHead L))))).cons 0) {{F}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)) := by
    rw [encStack_cons 0 L]
    simp only [Nat.zero_add, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 7
  refine h_pre.trans_star ?_
  refine (f_walk_right (d + 1)
    ((encStack (bumpHead (bumpHead (bumpHead (bumpHead L))))).cons 0) ((encStack R).cons 0)).trans
    ?_
  rw [← encStack_cons d (bumpHead (bumpHead (bumpHead (bumpHead L)))), ← encStack_cons_one R]
  exact ⟨0, by simp only [Cfg.headRight, ListBlank.head_cons, ListBlank.tail_cons, multiStep_zero]⟩

private theorem rule_D_one (L R : List ℕ) :
    (cfg_D (1 :: L) R) [target]⊢⁺ (cfg_D (bumpHead L) (0 :: R)) := by
  unfold cfg_D
  rw [encStack_cons 1 L, encStack_cons 0 R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 6

private theorem rule_D_ge2 (L R : List ℕ) (a : ℕ) :
    (cfg_D ((a + 2) :: L) R) [target]⊢⁺ (cfg_FR (a :: bumpHead L) (0 :: R)) := by
  unfold cfg_D cfg_FR
  rw [encStack_cons (a + 2) L]
  have h_split : a + 2 + 1 = 1 + (a + 2) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some D, ⟨0, (((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 2))) <+
        (([1] : List (Fin 2)) ^ 1), encStack R⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack L).cons 0) <+ (([1] : List (Fin 2)) ^ (a + 2))) <{{A}}
          (((encStack R).cons 0).cons 0)) := by
    simp only [list_pow_one]
    execute 2
  refine h_pre.trans_star ?_
  refine (a_walk_left (a + 2) ((encStack L).cons 0) (((encStack R).cons 0).cons 0)).trans ?_
  have h_split2 : a + 2 = 1 + (a + 1) := by omega
  rw [h_split2, list_pow_add, ListBlank.append_assoc]
  have h_mid :
      (((encStack L).cons 0) <{{A}}
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ (a + 1)) +> (((encStack R).cons 0).cons 0))))
        [target]⊢⁺
        (((encStack (bumpHead L)).cons 0) {{F}}>
          ((([1] : List (Fin 2)) ^ (a + 1)) +> (((encStack R).cons 0).cons 0))) := by
    simp only [list_pow_one]
    execute 2
  refine h_mid.to_star.trans ?_
  refine (f_walk_right (a + 1)
    ((encStack (bumpHead L)).cons 0) (((encStack R).cons 0).cons 0)).trans ?_
  rw [← encStack_cons a (bumpHead L), encStack_cons 0 R]
  simp only [Nat.zero_add, list_pow_one]
  finish

private theorem rule_FR_nil (R : List ℕ) :
    (cfg_FR [] R) [target]⊢⁺ (cfg_D [] (tailWeight R :: R.tail)) := by
  unfold cfg_FR cfg_D
  rw [encStack_nil]
  execute 1

private theorem rule_FR_cons_nil (L : List ℕ) (a : ℕ) :
    (cfg_FR (a :: L) []) [target]⊢⁺ (cfg_D (a :: L) [0]) := by
  unfold cfg_FR cfg_D
  rw [encStack_cons a L, encStack_cons 0 [], encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_FR_cons_zero (L R : List ℕ) (a : ℕ) :
    (cfg_FR (a :: L) (0 :: R)) [target]⊢⁺ (cfg_D (a :: L) (bumpHead R)) := by
  unfold cfg_FR cfg_D
  rw [encStack_cons a L, encStack_cons 0 R]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem rule_FR_cons_succ (L R : List ℕ) (a d : ℕ) :
    (cfg_FR (a :: L) ((d + 1) :: R)) [target]⊢⁺ (cfg_FR (d :: a :: L) (bumpHead R)) := by
  unfold cfg_FR
  rw [encStack_cons (d + 1) R]
  have h_split : d + 1 + 1 = 1 + (d + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some F, ⟨0, encStack (a :: L),
        ((([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)).tail⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        (((encStack (a :: L)).cons 0) {{F}}>
          ((([1] : List (Fin 2)) ^ (d + 1)) +> (encStack R).cons 0)) := by
    rw [encStack_cons a L]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_pre.trans_star ?_
  refine (f_walk_right (d + 1) ((encStack (a :: L)).cons 0) ((encStack R).cons 0)).trans ?_
  rw [← encStack_cons d (a :: L), ← encStack_cons_one R]
  exact ⟨0, by simp only [Cfg.headRight, ListBlank.head_cons, ListBlank.tail_cons, multiStep_zero]⟩

/-! ## Initial Reachability and Stack Reduction Closure -/

private theorem init_to_cfg_D :
    (init []) [target]⊢⁺ (cfg_D [2] []) := by
  unfold cfg_D
  rw [encStack_cons, encStack_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 3

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg1 .FR [4, 0] [0] :=
  init_to_cfg_D
    |>.trans (rule_D_ge2 [] [] 0)
    |>.trans (rule_FR_cons_zero [0] [] 0)
    |>.trans (rule_D_zero_zero_nil [0])
    |>.trans (rule_D_ge2 [] [] 4)

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem1 cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem1 cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | D =>
    cases L with
    | nil =>
      obtain ⟨hstep, hnone⟩ := rule_D_nil R
      exact ⟨cfg_Halt_D_nil R, hstep, Or.inr hnone⟩
    | cons a L' =>
      rcases a with _ | _ | a
      · cases R with
        | nil =>
          exact ⟨cfg_D (bumpHead (bumpHead (bumpHead L'))) [], rule_D_zero_nil L',
            Or.inl ⟨.D, bumpHead (bumpHead (bumpHead L')), [], rfl⟩⟩
        | cons d R' =>
          rcases d with _ | _ | d
          · cases R' with
            | nil =>
              let L6 := bumpHead (bumpHead (bumpHead (bumpHead (bumpHead (bumpHead L')))))
              exact ⟨cfg_D L6 [], rule_D_zero_zero_nil L', Or.inl ⟨.D, L6, [], rfl⟩⟩
            | cons e R'' =>
              obtain ⟨hstep, hnone⟩ := rule_D_zero_zero_cons L' R'' e
              exact ⟨cfg_Halt_D_zero L' e R'', hstep, Or.inr hnone⟩
          · let L4 := bumpHead (bumpHead (bumpHead (bumpHead L')))
            exact ⟨cfg_D L4 (bumpHead R'), rule_D_zero_one L' R',
              Or.inl ⟨.D, L4, bumpHead R', rfl⟩⟩
          · let L4 := bumpHead (bumpHead (bumpHead (bumpHead L')))
            exact ⟨cfg_FR (d :: L4) (bumpHead R'), rule_D_zero_ge2 L' R' d,
              Or.inl ⟨.FR, d :: L4, bumpHead R', rfl⟩⟩
      · exact ⟨cfg_D (bumpHead L') (0 :: R), rule_D_one L' R,
          Or.inl ⟨.D, bumpHead L', 0 :: R, rfl⟩⟩
      · exact ⟨cfg_FR (a :: bumpHead L') (0 :: R), rule_D_ge2 L' R a,
          Or.inl ⟨.FR, a :: bumpHead L', 0 :: R, rfl⟩⟩
  | FR =>
    cases L with
    | nil =>
      exact ⟨cfg_D [] (tailWeight R :: R.tail), rule_FR_nil R,
        Or.inl ⟨.D, [], tailWeight R :: R.tail, rfl⟩⟩
    | cons a L' =>
      cases R with
      | nil =>
        exact ⟨cfg_D (a :: L') [0], rule_FR_cons_nil L' a,
          Or.inl ⟨.D, a :: L', [0], rfl⟩⟩
      | cons d R' =>
        rcases d with _ | d
        · exact ⟨cfg_D (a :: L') (bumpHead R'), rule_FR_cons_zero L' R' a,
            Or.inl ⟨.D, a :: L', bumpHead R', rfl⟩⟩
        · exact ⟨cfg_FR (d :: a :: L') (bumpHead R'), rule_FR_cons_succ L' R' a d,
            Or.inl ⟨.FR, d :: a :: L', bumpHead R', rfl⟩⟩

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
  refine ⟨[.D, .FR], by decide, ?_⟩
  intro m
  cases m <;> simp

private theorem valid_stack_modes : IsValidStackModes encStack encStack evalStackCfg1 := by
  intro m
  cases m with
  | D => exact ⟨D, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | FR => exact ⟨F, .id [], .tail [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

/-- `target` reduces to a closed 2nd-order digit-stack system (`HasStackReduction`). -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack encStack evalStackCfg1 IsInStackSystem1
    ⟨rfl, rfl, encStack_head, encStack_head,
      encStack_not_surjective, encStack_not_surjective,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.FR, [4, 0], [0], init_reaches_nontrivial, by decide, ⟨4, by decide, by decide⟩⟩,
      Or.inl ⟨.D, .D, 1, (· + 1), (0 :: ·),
        fun _ => Nat.le_succ _, fun z L R => rule_D_one (z :: L) R⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RB1LA_1RC0RF_1RDHHH_0LE1RB_HHH0LA_1LD1RF
