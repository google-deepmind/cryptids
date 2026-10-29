/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Machine `1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver machine
`1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB`
(https://wiki.bbchallenge.org/wiki/1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB).

Each half-tape stack encodes unary blocks $1^{3a + 2}$ separated by single zeros, ordered from the
tape head outward. Starting from `init []`, the machine enters a closed 2-mode (`SweepR`, `CarryD`)
2nd-order digit-stack system in 14 raw steps.

<!-- hardness:begin -->
## Hardness

*Hardness class:* Wiki stack — trigger **era-recursive (3-case bottom-extension recurrence)**,
growth doubly-exponential era lengths ($T_0..T_3 = 1, 2, 8, 256$), shield none closed (all-even
$R$ + $L.\mathrm{last}=0$ refuted across eras).

*Verdict (heuristic; community analysis, see the wiki page):* probviously non-halting (wiki
cryptid).

*Hazard:* not quantified; perturbed all-even seeds halt in Era 2/3 (`rec_59_bottom_extension`)

*Simulated horizon:* pumping test: 46 perturbed configurations, 0 halts in $10^5$ steps

*Why it is hard:* exact 3-case composition theorem verified on all 1,024 stacks of weight $\le10$

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Digit-Stack Encodings and Inner Loop Helpers -/

private theorem append_left_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (s <+ (([1] : List (Fin 2)) ^ n)) <+ (([1] : List (Fin 2)) ^ m) =
      s <+ (([1] : List (Fin 2)) ^ (n + m)) := by
  rw [ListBlank.append_append, list_pow_add_comm, ← list_pow_add]

/-- Encode a digit stack `s` as `1^{3a + 2} 0 ...` from the tape head outward. -/
private def encStack1 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s => ListBlank.append (([1] : List (Fin 2)) ^ (3 * a + 2))
      (ListBlank.cons 0 (encStack1 s))

@[simp]
private theorem encStack1_nil : encStack1 [] = default :=
  rfl

private theorem encStack1_cons (a : ℕ) (s : List ℕ) :
    encStack1 (a :: s) = ((encStack1 s).cons 0) <+ (([1] : List (Fin 2)) ^ (3 * a + 2)) :=
  rfl

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [Cfg.headRight, Cfg.headLeft, ListBlank.cons_zero_default, encStack1_nil,
    ListBlank.head_cons, ListBlank.tail_cons, multiStep_zero]
  try rfl))

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.mk_nil, ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons,
    ListBlank.head_default_fin, ListBlank.tail_cons, ListBlank.tail_default,
    ListBlank.cons_zero_default]
  apply ReachesPlus.head (by rfl)
  simp only [Cfg.headRight, Cfg.headLeft, Tape.move, Tape.write,
    ListBlank.mk_nil, ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons,
    ListBlank.tail_cons, ListBlank.cons_zero_default, ListBlank.head_default_fin,
    ListBlank.tail_default]))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  try finish))

/-- Right-sweep separator configuration: state `E` reading `0` between `L` and `R`. -/
private def cfg_SweepR (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some E, ⟨0, encStack1 L, encStack1 R⟩⟩

/-- Left-carry separator configuration: state `D` reading `0` between `L` and `R`. -/
private def cfg_CarryD (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some D, ⟨0, encStack1 L, encStack1 R⟩⟩

/-- Right-shift overflow configuration: `0 1 C>` shifting blocks of `R` by 1 cell right. -/
private def cfg_ShiftC (L R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨(encStack1 R).head, ((encStack1 L).cons 0).cons 1, (encStack1 R).tail⟩⟩

/-- Modes of the 2nd-order digit-stack configuration family. -/
private inductive StackMode
  | SweepR
  | CarryD

private def evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .SweepR, L, R => cfg_SweepR L R
  | .CarryD, L, R => cfg_CarryD L R

private def IsInStackSystem1 (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg1 m L R

private theorem step_C_triple (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([1] : List (Fin 2)) ^ 3 +> r)) [target]⊢⁺
      ((l <+ (([1] : List (Fin 2)) ^ 3)) {{C}}> r) := by
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 5

private theorem loop_C_sweep (k : ℕ) (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([1] : List (Fin 2)) ^ (3 * k) +> r)) [target]⊢*
      ((l <+ (([1] : List (Fin 2)) ^ (3 * k))) {{C}}> r) := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h_split : 3 * (k + 1) = 3 + 3 * k := by omega
    rw [h_split, list_pow_add, ListBlank.append_assoc]
    refine (step_C_triple l _).to_star.trans ?_
    refine (ih (l <+ ([1] : List (Fin 2)) ^ 3) r).trans ?_
    rw [ListBlank.append_append, list_pow_add_comm]

private theorem loop_D_rewind (n : ℕ) (l r : ListBlank (Fin 2)) :
    ((l <+ (([1] : List (Fin 2)) ^ (2 * n))) <{{D}} r) [target]⊢*
      (l <{{D}} ((([1] : List (Fin 2)) ^ (2 * n)) +> r)) := by
  induction n generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    have h_split : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [h_split, list_pow_add, ← ListBlank.append_append]
    have h1 :
        (((l <+ ([1] : List (Fin 2)) ^ (2 * n)) <+ ([1] : List (Fin 2)) ^ 2) <{{D}} r) [target]⊢⁺
          ((l <+ ([1] : List (Fin 2)) ^ (2 * n)) <{{D}} (([1] : List (Fin 2)) ^ 2 +> r)) := by
      simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
      execute 2
    refine h1.to_star.trans ?_
    refine (ih l (([1] : List (Fin 2)) ^ 2 +> r)).trans ?_
    rw [← ListBlank.append_assoc, list_pow_add_comm]

/-! ## Local Separator Rules -/

private theorem rule_sweepR_nil_nil :
    (cfg_SweepR [] []) [target]⊢⁺ (cfg_CarryD [0] [0]) := by
  unfold cfg_SweepR cfg_CarryD
  rw [encStack1_cons, encStack1_nil]
  simp only [Nat.mul_zero, Nat.zero_add, list_pow_succ, list_pow_zero,
    List.cons_append, List.nil_append]
  execute 14

private theorem rule_sweepR_step (L R : List ℕ) (c : ℕ) :
    (cfg_SweepR L (c :: R)) [target]⊢⁺ (cfg_SweepR (c :: L) R) := by
  unfold cfg_SweepR
  rw [encStack1_cons]
  have h_split : 3 * c + 2 = 1 + (3 * c + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some E, ⟨0, encStack1 L, ([1] : List (Fin 2)) ^ 1 +>
        (([1] : List (Fin 2)) ^ (3 * c) +>
          (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
          (([1] : List (Fin 2)) ^ (3 * c) +>
            (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_pre.trans_star ?_
  refine (loop_C_sweep c (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) _).trans ?_
  rw [append_left_pow_add]
  have h_post :
      ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * c)) {{C}}>
        (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0)) [target]⊢⁺
        (⟨some E, ⟨0,
          (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * c)) <+
            ([1] : List (Fin 2)) ^ 1,
          encStack1 R⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    simp only [list_pow_one]
    execute 1
  refine h_post.to_star.trans ?_
  rw [append_left_pow_add, encStack1_cons]
  have h_eq : 1 + 3 * c + 1 = 3 * c + 2 := by omega
  rw [h_eq]

private theorem sweepA_step (L R : List ℕ) (c : ℕ) :
    (⟨some A, ⟨0, encStack1 L, encStack1 (c :: R)⟩⟩ : Cfg (Fin 2) (Fin 6))
      [target]⊢⁺ (cfg_SweepR (c :: L) R) := by
  unfold cfg_SweepR
  rw [encStack1_cons]
  have h_split : 3 * c + 2 = 1 + (3 * c + 1) := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc, list_pow_add, ListBlank.append_assoc]
  have h_pre :
      (⟨some A, ⟨0, encStack1 L, ([1] : List (Fin 2)) ^ 1 +>
        (([1] : List (Fin 2)) ^ (3 * c) +>
          (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0))⟩⟩ : Cfg (Fin 2) (Fin 6))
        [target]⊢⁺
        ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
          (([1] : List (Fin 2)) ^ (3 * c) +>
            (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0))) := by
    simp only [list_pow_one]
    execute 4
  refine h_pre.trans_star ?_
  refine (loop_C_sweep c (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) _).trans ?_
  rw [append_left_pow_add]
  have h_post :
      ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * c)) {{C}}>
        (([1] : List (Fin 2)) ^ 1 +> (encStack1 R).cons 0)) [target]⊢⁺
        (⟨some E, ⟨0,
          (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * c)) <+
            ([1] : List (Fin 2)) ^ 1,
          encStack1 R⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    simp only [list_pow_one]
    execute 1
  refine h_post.to_star.trans ?_
  rw [append_left_pow_add, encStack1_cons]
  have h_eq : 1 + 3 * c + 1 = 3 * c + 2 := by omega
  rw [h_eq]

private def cfg_RewindD (L : List ℕ) (a : ℕ) (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (((encStack1 L).cons 0) <+ (([1] : List (Fin 2)) ^ (3 * a + 3))) <{{D}}
    ((([1] : List (Fin 2)) ^ 2) +> ((encStack1 R).cons 0))

private theorem right_bounce_to_RewindD (L : List ℕ) (a : ℕ) :
    (cfg_SweepR (a :: L) []) [target]⊢⁺ (cfg_RewindD L a []) := by
  unfold cfg_SweepR cfg_RewindD
  rw [encStack1_cons, encStack1_nil]
  have h_eq : 3 * a + 3 = (3 * a + 2) + 1 := by omega
  rw [h_eq, ← append_left_pow_add]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 4

private theorem carry_zero_to_RewindD (L R : List ℕ) (a : ℕ) :
    (cfg_CarryD (0 :: a :: L) R) [target]⊢⁺ (cfg_RewindD L a R) := by
  unfold cfg_CarryD cfg_RewindD
  rw [encStack1_cons, encStack1_cons]
  have h_eq : 3 * a + 3 = (3 * a + 2) + 1 := by omega
  rw [h_eq, ← append_left_pow_add]
  simp only [Nat.mul_zero, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 7

private theorem rewindD_even (L R : List ℕ) (m : ℕ) :
    (cfg_RewindD L (2 * m) R) [target]⊢⁺ (cfg_SweepR ((2 * m + 1) :: L) R) := by
  unfold cfg_RewindD
  have h_split : 3 * (2 * m) + 3 = 1 + 2 * (3 * m + 1) := by omega
  rw [h_split, ← append_left_pow_add]
  refine (loop_D_rewind (3 * m + 1)
    (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) _).trans_plus ?_
  rw [← ListBlank.append_pow_add]
  have h_stepA :
      (((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) <{{D}}
        (([1] : List (Fin 2)) ^ (2 * (3 * m + 1) + 2) +> (encStack1 R).cons 0)))
        [target]⊢⁺
        (⟨some A, ⟨0, encStack1 L, (([1] : List (Fin 2)) ^ 1) +>
          ((([1] : List (Fin 2)) ^ (2 * (3 * m + 1) + 2)) +>
            (encStack1 R).cons 0)⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    simp only [list_pow_one]
    execute 1
  refine h_stepA.trans ?_
  rw [← ListBlank.append_pow_add]
  have h_eq : 1 + (2 * (3 * m + 1) + 2) = 3 * (2 * m + 1) + 2 := by omega
  rw [h_eq, ← encStack1_cons]
  exact sweepA_step L R (2 * m + 1)

private theorem rewindD_odd (L R : List ℕ) (m : ℕ) :
    (cfg_RewindD L (2 * m + 1) R) [target]⊢* (cfg_CarryD L ((2 * m + 2) :: R)) := by
  unfold cfg_RewindD cfg_CarryD
  rw [encStack1_cons]
  have h_split : 3 * (2 * m + 1) + 3 = 2 * (3 * m + 3) := by omega
  rw [h_split]
  refine (loop_D_rewind (3 * m + 3) ((encStack1 L).cons 0) _).trans ?_
  rw [← ListBlank.append_pow_add]
  have h_eq : 2 * (3 * m + 3) + 2 = 3 * (2 * m + 2) + 2 := by omega
  rw [h_eq]
  exact ⟨0, by simp [Cfg.headLeft]⟩

private theorem rule_even_bump (L : List ℕ) (j : ℕ) :
    (cfg_SweepR ((2 * j) :: L) []) [target]⊢⁺ (cfg_SweepR ((2 * j + 1) :: L) []) :=
  (right_bounce_to_RewindD L (2 * j)).trans (rewindD_even L [] j)

private theorem rule_odd_carry_init (L : List ℕ) (j : ℕ) :
    (cfg_SweepR ((2 * j + 1) :: L) []) [target]⊢⁺ (cfg_CarryD L [2 * j + 2]) :=
  (right_bounce_to_RewindD L (2 * j + 1)).trans_star (rewindD_odd L [] j)

private theorem rule_carryD_split_step (L R : List ℕ) (a : ℕ) :
    (cfg_CarryD ((a + 1) :: L) R) [target]⊢⁺ (cfg_CarryD (a :: L) (0 :: R)) := by
  unfold cfg_CarryD
  rw [encStack1_cons, encStack1_cons, encStack1_cons]
  have h_split : 3 * (a + 1) + 2 = (3 * a + 2) + 3 := by omega
  rw [h_split, ← append_left_pow_add]
  simp only [Nat.mul_zero, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
  execute 7

private theorem rule_carryD_absorb_even (L R : List ℕ) (m : ℕ) :
    (cfg_CarryD (0 :: (2 * m) :: L) R) [target]⊢⁺ (cfg_SweepR ((2 * m + 1) :: L) R) :=
  (carry_zero_to_RewindD L R (2 * m)).trans (rewindD_even L R m)

private theorem rule_carryD_prop_odd (L R : List ℕ) (m : ℕ) :
    (cfg_CarryD (0 :: (2 * m + 1) :: L) R) [target]⊢⁺ (cfg_CarryD L ((2 * m + 2) :: R)) :=
  (carry_zero_to_RewindD L R (2 * m + 1)).trans_star (rewindD_odd L R m)

private theorem rule_overflow_start (R : List ℕ) :
    (cfg_CarryD [0] R) [target]⊢⁺ (cfg_ShiftC [0] R) := by
  unfold cfg_CarryD cfg_ShiftC
  rw [encStack1_cons, encStack1_nil]
  simp only [Nat.mul_zero, Nat.zero_add, list_pow_succ, list_pow_zero,
    List.cons_append, List.nil_append]
  execute 15

private theorem rule_shiftC_step (L R : List ℕ) (d : ℕ) :
    (cfg_ShiftC L (d :: R)) [target]⊢⁺ (cfg_ShiftC (d :: L) R) := by
  unfold cfg_ShiftC
  rw [encStack1_cons]
  have h_split : 3 * d + 2 = (3 * d) + 2 := by omega
  rw [h_split, list_pow_add, ListBlank.append_assoc]
  change ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ((([1] : List (Fin 2)) ^ (3 * d)) +> (([1] : List (Fin 2)) ^ 2 +> (encStack1 R).cons 0)))
    [target]⊢⁺ _
  refine (loop_C_sweep d (((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ 1) _).trans_plus ?_
  rw [append_left_pow_add]
  have h_end :
      ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * d)) {{C}}>
        (([1] : List (Fin 2)) ^ 2 +> (encStack1 R).cons 0)) [target]⊢⁺
        (⟨some C, ⟨(encStack1 R).head,
          ((((encStack1 L).cons 0) <+ ([1] : List (Fin 2)) ^ (1 + 3 * d)) <+
            ([1] : List (Fin 2)) ^ 1).cons 0 |>.cons 1,
          (encStack1 R).tail⟩⟩ : Cfg (Fin 2) (Fin 6)) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append]
    execute 3
  refine h_end.trans_star ?_
  rw [append_left_pow_add, encStack1_cons]
  have h_eq : 1 + 3 * d + 1 = 3 * d + 2 := by omega
  rw [h_eq]

private theorem rule_shiftC_end (L : List ℕ) :
    (cfg_ShiftC L []) [target]⊢⁺ (cfg_CarryD L [0]) := by
  unfold cfg_ShiftC cfg_CarryD
  rw [encStack1_cons, encStack1_nil]
  simp only [Nat.mul_zero, Nat.zero_add, list_pow_succ, list_pow_zero,
    List.cons_append, List.nil_append]
  execute 2

private theorem rule_shiftC_all (R L : List ℕ) :
    (cfg_ShiftC L R) [target]⊢* (cfg_ShiftC (R.reverse ++ L) []) := by
  induction R generalizing L with
  | nil => simp
  | cons d R' ih =>
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    exact (rule_shiftC_step L R' d).to_star.trans (ih (d :: L))

private theorem rule_left_shift_overflow (R : List ℕ) :
    (cfg_CarryD [0] R) [target]⊢⁺ (cfg_CarryD (R.reverse ++ [0]) [0]) :=
  (rule_overflow_start R).trans
    ((rule_shiftC_all R [0]).trans_plus (rule_shiftC_end (R.reverse ++ [0])))

private def cfg_Halt (R : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  ⟨some F, ⟨0, default, (encStack1 R).cons 0⟩⟩

private theorem rule_left_halt (R : List ℕ) :
    ((cfg_CarryD [] R) [target]⊢⁺ (cfg_Halt R)) ∧ (step target (cfg_Halt R)).isNone := by
  refine ⟨?_, rfl⟩
  unfold cfg_CarryD cfg_Halt
  rw [encStack1_nil]
  execute 1

/-! ## Initial Reachability and Stack Reduction Closure -/

private theorem init_to_CarryD :
    (init []) [target]⊢⁺ (cfg_CarryD [0] [0]) := by
  unfold cfg_CarryD
  rw [encStack1_cons, encStack1_nil]
  simp only [Nat.mul_zero, Nat.zero_add, list_pow_succ, list_pow_zero,
    List.cons_append, List.nil_append]
  execute 14

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg1 .CarryD [0] [0, 2] :=
  init_to_CarryD
    |>.trans (rule_left_shift_overflow [0])
    |>.trans (rule_carryD_absorb_even [] [0] 0)
    |>.trans (rule_sweepR_step [1] [] 0)
    |>.trans (rule_even_bump [1] 0)
    |>.trans (rule_odd_carry_init [1] 0)
    |>.trans (rule_carryD_split_step [] [2] 0)

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem1 cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem1 cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨mode, L, R, rfl⟩
  cases mode with
  | SweepR =>
    cases R with
    | cons c R' =>
      exact ⟨cfg_SweepR (c :: L) R', rule_sweepR_step L R' c,
        Or.inl ⟨.SweepR, c :: L, R', rfl⟩⟩
    | nil =>
      cases L with
      | nil =>
        exact ⟨cfg_CarryD [0] [0], rule_sweepR_nil_nil, Or.inl ⟨.CarryD, [0], [0], rfl⟩⟩
      | cons a L' =>
        rcases nat_even_or_odd_two_mul a with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · exact ⟨cfg_SweepR ((2 * j + 1) :: L') [], rule_even_bump L' j,
            Or.inl ⟨.SweepR, (2 * j + 1) :: L', [], rfl⟩⟩
        · exact ⟨cfg_CarryD L' [2 * j + 2], rule_odd_carry_init L' j,
            Or.inl ⟨.CarryD, L', [2 * j + 2], rfl⟩⟩
  | CarryD =>
    cases L with
    | nil =>
      exact ⟨cfg_Halt R, (rule_left_halt R).1, Or.inr (rule_left_halt R).2⟩
    | cons a L' =>
      cases a with
      | succ a' =>
        exact ⟨cfg_CarryD (a' :: L') (0 :: R), rule_carryD_split_step L' R a',
          Or.inl ⟨.CarryD, a' :: L', 0 :: R, rfl⟩⟩
      | zero =>
        cases L' with
        | nil =>
          exact ⟨cfg_CarryD (R.reverse ++ [0]) [0], rule_left_shift_overflow R,
            Or.inl ⟨.CarryD, R.reverse ++ [0], [0], rfl⟩⟩
        | cons b L'' =>
          rcases nat_even_or_odd_two_mul b with ⟨m, rfl⟩ | ⟨m, rfl⟩
          · exact ⟨cfg_SweepR ((2 * m + 1) :: L'') R, rule_carryD_absorb_even L'' R m,
              Or.inl ⟨.SweepR, (2 * m + 1) :: L'', R, rfl⟩⟩
          · exact ⟨cfg_CarryD L'' ((2 * m + 2) :: R), rule_carryD_prop_odd L'' R m,
              Or.inl ⟨.CarryD, L'', (2 * m + 2) :: R, rfl⟩⟩

private theorem encStack1_head (a : ℕ) (s : List ℕ) : (encStack1 (a :: s)).head = 1 := by
  simp [encStack1, list_pow_succ]

private theorem encStack1_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ s : List ℕ, encStack1 s ≠ t := by
  refine ⟨(1 : Fin 2) >> default, rfl, ?_⟩
  intro s h
  cases s with
  | nil =>
    have h0 := congrArg ListBlank.head h
    simp [encStack1] at h0
  | cons x s' =>
    have h1 := congrArg (fun u => u.tail.head) h
    simp [encStack1, list_pow_succ] at h1

private theorem block_encoding :
    ∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
      strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
      strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
      (∀ a L, encStack1 (a :: L) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encStack1 L))) ∧
      (∀ d R, encStack1 (d :: R) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encStack1 R))) :=
  ⟨3, 2, 1, 3, 2, 1, by decide, by decide, by decide, by decide, by decide, by decide,
    fun _ _ => rfl, fun _ _ => rfl⟩

private theorem modes_bounded :
    ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes := by
  refine ⟨[.SweepR, .CarryD], by decide, ?_⟩
  intro m
  cases m <;> simp

private theorem valid_stack_modes : IsValidStackModes encStack1 encStack1 evalStackCfg1 := by
  intro m
  cases m with
  | SweepR => exact ⟨E, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩
  | CarryD => exact ⟨D, .id [], .id [], by decide, by decide, Or.inl (fun _ _ => rfl)⟩

/-- `target` reduces to a closed 2nd-order digit-stack system (`HasStackReduction`). -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack1 encStack1 evalStackCfg1 IsInStackSystem1
    ⟨rfl, rfl, encStack1_head, encStack1_head,
      encStack1_not_surjective, encStack1_not_surjective,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.CarryD, [0], [0, 2], init_reaches_nontrivial, by decide, ⟨2, by decide, by decide⟩⟩,
      Or.inr ⟨.SweepR, .SweepR, 0, id, (0 :: ·),
        fun _ => Nat.le_succ _, fun z L R => rule_sweepR_step L (z :: R) 0⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_HHH0LB
