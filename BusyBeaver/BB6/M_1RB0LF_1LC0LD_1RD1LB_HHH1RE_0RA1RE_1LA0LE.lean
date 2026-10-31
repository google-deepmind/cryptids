/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`

We define the configuration for $b, c \ge 0$:

$$
A(b, c) := 0^\infty \ 1^b \ \mathrm{F}{>} \ 00 \ 1^c \ 0^\infty.
$$

Starting from $A(5, 2)$ (reached after 33 steps from the blank tape), the machine follows the
map $T$, where $h = \lfloor c/2 \rfloor$:

$$
T(A(b, c)) = \begin{cases}
  A(2c+4, 3) & \text{if } b = 0, \\
  A(3, 3) & \text{if } b = 2 \text{ and } c = 0, \\
  A(5, c-1) & \text{if } b = 2 \text{ and } c \ge 1, \\
  A(b-2h-4, 2c+5) & \text{if } b \ge 2h+5, \\
  A(2c+6, 3) & \text{if } b \text{ is odd and } b \le 2h+3, \\
  F(b-3, 2, 0, c-b+1) & \text{if } b \ge 4 \text{ is even and } b \le 2h, \\
  F(b-4+(c \bmod 2), 2, 0, 0) & \text{if } b \ge 4 \text{ is even and } b = 2h+2, \\
  \text{Halt} & \text{if } b \ge 4 \text{ is even and } b = 2h+4,
\end{cases}
$$

where $F(m, p, n, c)$ is defined recursively on $m$:

$$
F(m, p, n, c) = \begin{cases}
  A(4n+c+7, 3) & \text{if } m = 0 \text{ and } p \le n+1, \\
  A(2(p-n-2)+1, 4n+c+6) & \text{if } m = 0 \text{ and } p \ge n+2, \\
  A(4n+9, c) & \text{if } m = 1 \text{ and } p \le n+1, \\
  F(0, p-n-2, 2n+3, c) & \text{if } m = 1 \text{ and } p \ge n+2, \\
  F(m-2, 2n+4, 0, c) & \text{if } m \ge 2 \text{ and } p \le n+1, \\
  F(m-1, p-n-2, 2n+3, c) & \text{if } m \ge 2 \text{ and } p \ge n+2.
\end{cases}
$$

<!-- hardness:begin -->
## Hardness

*Hardness class:* Cascade — trigger **EQ**, growth super-exponential (two-stage $2^n$ doubling
tower), shield none.

*Verdict (heuristic, from exact accelerated simulation of the certified rules):* probviously
non-halting.

*Hazard:* $P(\text{halt}) \ll 10^{-600}$

*Simulated horizon:* $> 3.46\times10^{1204}$ TM steps in 12 cascades

*Why it is hard:* coupled outer `D1` and inner `Modd` $2^n$ cascades; halts iff $D_1(2,u,0)$

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

/-! ## Shift Lemmas -/

private theorem shift_E_ones (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([1] : List (Fin 2)) ^ k +> r)) [target]⊢*
    ((l <+ ([1] : List (Fin 2)) ^ k) {{E}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{E}}> ([1] +> (([1] : List (Fin 2)) ^ k +> r)))
        [target]⊢*
        ((l <+ [1]) {{E}}> (([1] : List (Fin 2)) ^ k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [1]) r
    rw [ListBlank.append_pow_succ' ([1] : List (Fin 2)) k l] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_CB_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [target]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([0, 1] : List (Fin 2)) ^ k) <+ [0, 1]) {{C}}> ([1] +> r))
        [target]⊢*
        ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ' ([1, 1] : List (Fin 2)) k r] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_D_right_100 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{D}}> ([1, 0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
        [target]⊢*
        ((l <+ [0, 1]) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k l] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_FA_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> r)) [target]⊢*
    (l {{F}}> ([0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, <- ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{F}}> ([0] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{F}}> ([0] +> ([0, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([0, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k r] at h2
    exact ReachesStar.trans h1 h2

/-! ## Canonical Configurations and Pattern Set -/

private def cfg_E (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
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

private theorem cfg_A_eq_F_R (b k c : Nat) :
    cfg_A b k c = F_R b k (([1] : List (Fin 2)) ^ c +> default) := rfl

/-- Canonical tape pattern
$A(b, k, c) := 0^\infty\,1^b\,(01)^k\,\mathrm{F}{>}\,0\,0\,1^c\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1, 0] 1 (.rep [1] 0 .default)
    head  := some F
    right := .sym 0 (.sym 0 (.rep [1] 2 .default)) }

/-- Closed pattern set for `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

private theorem eval_pat_A (vars : Nat → Nat) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_A (b k c : Nat) : IsInPatternSet ps (cfg_A b k c) := by
  refine ⟨(pat_A, .true), List.Mem.head _, fun i => match i with | 0 => b | 1 => k | _ => c, ?_,
          trivial⟩
  exact (eval_pat_A (fun i => match i with | 0 => b | 1 => k | _ => c)).symm

/-! ## Accelerated Transition Rules -/

private theorem init_to_E : (init []) [target]⊢⁺ (cfg_E 0 4) := by
  unfold init cfg_E
  simp only [Tape.mk₁, list_pow_zero, list_pow_succ, List.cons_append, List.append_nil,
    ListBlank.append_nil, ListBlank.append_cons]
  bb_steps

private theorem step_E_b0 (a : Nat) :
    (cfg_E a 0) [target]⊢⁺ (cfg_E 0 (2 * a + 4)) := by
  unfold cfg_E
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) {{E}}> default)
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ a) <+ [0]) {{C}}> ([1] +> ([1]
              +> default))) := by
    bb_steps
  rw [ListBlank.append_cons, ListBlank.append_nil, <- default_append_01_pow a] at h1
  have h2 := shift_CB_left a default ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((default : ListBlank (Fin 2)) {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1]
          +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          3) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * a + 1)] at h4
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_E_b1 (a : Nat) :
    (cfg_E a 1) [target]⊢⁺ (cfg_E 0 (2 * a + 6)) := by
  unfold cfg_E
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)] at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+
          [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}>
        ((([1] : List (Fin 2)) ^ (2 * a)) +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default] at h3
  have h4 := shift_E_ones (2 * a + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          5) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * a + 1)] at h4
  have ha : 5 + (2 * a + 1) = 2 * a + 6 := by omega
  rw [ha] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_E_b2_to_D_halt (a : Nat) :
    (cfg_E a 2) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ (2 * a + 4) +>
            default))) := by
  unfold cfg_E
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin
          2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ ([1, 0] : List (Fin 2)) ^
              a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2)] at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+
          [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default,
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) 3 (2 * a + 1) default] at h3
  have ha : 3 + (2 * a + 1) = 2 * a + 4 := by omega
  rw [ha] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem step_E_b3_to_cfg_A (a b : Nat) :
    (cfg_E a (b + 3)) [target]⊢⁺ (cfg_A (b + 1) 0 (2 * a + 3)) := by
  unfold cfg_E cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List
          (Fin 2)) ^ a) {{E}}> default)
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3)) <+ ([1, 0] : List (Fin
              2)) ^ a) <+ [0]) {{C}}>
        ([1] +> ([1] +> default))) := by
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- append_01_pow_zero a ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3))]
      at h1
  have h2 := shift_CB_left a (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b +
          3)) <+ [0]) ([1] +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 a] at h2
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2] at h1 h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List
          (Fin 2)) ^ 2) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * a) +> ([1] +> default))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) {{F}}>
        ([0, 0] +> (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * a) +> (([1] : List
                (Fin 2)) ^ 1 +> default))))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * a) 1 default,
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * a + 1) default] at h3
  have ha : 2 + (2 * a + 1) = 2 * a + 3 := by omega
  rw [ha] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem step_F_b2_k0 (c : Nat) :
    (cfg_A 2 0 (c + 1)) [target]⊢⁺ (cfg_A 5 0 c) := by
  unfold cfg_A
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem init_reaches_A_502 :
    (init []) [target]⊢* (cfg_A 5 0 2) :=
  ReachesPlus.to_star
    (ReachesPlus.trans init_to_E
      (ReachesPlus.trans (step_E_b3_to_cfg_A 0 1) (step_F_b2_k0 2)))

private theorem isNone_step_D_00 (l r : ListBlank (Fin 2)) :
    (step target (l {{D}}> ([0, 0] +> r))).isNone = true := by
  bb_halt

private theorem closes_E (a b : Nat) : StepsToClosed target ps (cfg_E a b) := by
  rcases b with _ | _ | _ | b'
  · have h1 := step_E_b0 a
    have hb : 2 * a + 4 = (2 * a + 1) + 3 := by omega
    rw [hb] at h1
    exact StepsToClosed.of_isInPatternSet (ReachesPlus.trans h1 (step_E_b3_to_cfg_A 0 (2 * a + 1)))
      (in_ps_A (2 * a + 2) 0 3)
  · have h1 := step_E_b1 a
    have hb : 2 * a + 6 = (2 * a + 3) + 3 := by omega
    rw [hb] at h1
    exact StepsToClosed.of_isInPatternSet (ReachesPlus.trans h1 (step_E_b3_to_cfg_A 0 (2 * a + 3)))
      (in_ps_A (2 * a + 4) 0 3)
  · exact StepsToClosed.of_halting (step_E_b2_to_D_halt a) (isNone_step_D_00 _ _)
  · exact StepsToClosed.of_isInPatternSet (step_E_b3_to_cfg_A a b') (in_ps_A (b' + 1) 0 (2 * a + 3))

private def D100 (b k : Nat) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ ([1, 0] : List (Fin 2)) ^ k) <+
          [0]) {{D}}>
    ([1, 0, 0] +> r)

private def C_bounce (b : Nat) (s : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) {{C}}> ([1] +> s)

private theorem step_F0_sweep_right (k : Nat) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
    [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}> ([1, 0, 0] +> r)) := by
  have h1 : ((default : ListBlank (Fin 2)) {{F}}> ([0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}> ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    bb_steps
  have h2 := shift_D_right_100 k default r
  exact ReachesPlus.trans_star h1 h2

private theorem F_R_b0_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 0 k r) [target]⊢⁺ (D100 0 k r) := by
  unfold F_R D100
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k default ([0] +> r)
  rw [append_01_pow_zero k r] at h1
  have h2 := step_F0_sweep_right k r
  rw [default_append_01_pow k] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem F_R_b1_to_D100 (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 1 k r) [target]⊢⁺ (D100 0 (k + 1) r) := by
  unfold F_R D100
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) ([0]
          +> r)
  rw [append_01_pow_zero k r] at h1
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{F}}>
        ([0, 0] +> ([1, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r)))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) k r] at h2
  have h3 := step_F0_sweep_right (k + 1) r
  rw [default_append_01_pow (k + 1)] at h3
  exact ReachesPlus.trans (ReachesStar.trans_plus h1 h2) h3

private theorem F_R_b3_to_D100 (b k : Nat) (r : ListBlank (Fin 2)) :
    (F_R (b + 3) k r) [target]⊢⁺ (D100 (b + 1) k r) := by
  unfold F_R D100
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 3))
          ([0] +> r)
  rw [append_01_pow_zero k r] at h1
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2] at h1
  have h2 : ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ ([1] : List (Fin
          2)) ^ 2) {{F}}>
      ([0] +> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) {{D}}>
        ([1, 0, 0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  have h3 := shift_D_right_100 k
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1)) <+ [0]) r
  rw [append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1))] at h3
  exact ReachesPlus.trans_star (ReachesStar.trans_plus h1 h2) h3

private theorem D100_0_11 (k : Nat) (r : ListBlank (Fin 2)) :
    (D100 0 k ([1, 1] +> r)) [target]⊢⁺ (F_R 1 (k + 1) r) := by
  unfold D100 F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_cons, ListBlank.append_nil, <- default_append_01_pow k]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1, 1] +> r)))
      [target]⊢⁺
      (((((default : ListBlank (Fin 2)) <+ ([0, 1] : List (Fin 2)) ^ k) <+ ([0, 1] : List (Fin 2))
              ^ 1) <+ [1]) {{F}}>
        ([0, 0] +> r)) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) k 1,
    <- append_10_pow_one (k + 1) default] at h1
  exact h1

private theorem D100_succ_11 (b k : Nat) (r : ListBlank (Fin 2)) :
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
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (b + 1))
    ([1, 0] : List (Fin 2)) k 2] at h1
  exact h1

private theorem D100_nil_to_C_bounce (b k : Nat) :
    (D100 b k default) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 3) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> default))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
      ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 1] at h1
  have h2 := shift_CB_left (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 1),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 1)) 1 default] at h2
  have hk : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem D100_one_to_C_bounce (b k : Nat) :
    (D100 b k ([1] +> default)) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 5) +> default)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([1] +> default)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 2) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 2] at h1
  have h2 := shift_CB_left (k + 2) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 1 +> default)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 2),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 2)) 1 default] at h2
  have hk : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem D100_01_to_C_bounce (b k : Nat) (r : ListBlank (Fin 2)) :
    (D100 b k ([0, 1] +> r)) [target]⊢⁺
    (C_bounce b (([1] : List (Fin 2)) ^ (2 * k + 4) +> r)) := by
  unfold D100 C_bounce
  rw [<- append_01_pow_zero k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] :
          List (Fin 2)) ^ k) {{D}}>
      ([1, 0, 0] +> ([0, 1] +> r)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0]) <+ ([0, 1] : List
              (Fin 2)) ^ k) <+
        ([0, 1] : List (Fin 2)) ^ 1) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 2 +> r))) := by
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  rw [<- ListBlank.append_pow_add_rev
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) <+ [0])
    ([0, 1] : List (Fin 2)) k 1] at h1
  have h2 := shift_CB_left (k + 1) (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^
          b) <+ [0])
    (([1] : List (Fin 2)) ^ 2 +> r)
  rw [pair_pow_eq_singleton_pow_two_mul 1 (k + 1),
    <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 1)) 2 r] at h2
  have hk : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
  rw [hk] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem C_bounce_0 (s : ListBlank (Fin 2)) :
    (C_bounce 0 s) [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) {{E}}> s) := by
  unfold C_bounce
  simp only [list_pow_zero, ListBlank.append_nil]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_1 (s : ListBlank (Fin 2)) :
    (C_bounce 1 s) [target]⊢⁺
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{E}}> s) := by
  unfold C_bounce
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_2 (s : ListBlank (Fin 2)) :
    (C_bounce 2 s) [target]⊢⁺
    ((default : ListBlank (Fin 2)) {{D}}> ([0, 0] +> (([1] : List (Fin 2)) ^ 3 +> s))) := by
  unfold C_bounce
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_3 (b : Nat) (s : ListBlank (Fin 2)) :
    (C_bounce (b + 3) s) [target]⊢⁺
    (F_R (b + 1) 0 (([1] : List (Fin 2)) ^ 2 +> s)) := by
  unfold C_bounce F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  have hb : b + 3 = (b + 1) + 2 := by omega
  rw [hb, ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (b + 1) 2]
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem step_F_ksucc_c0 (b k : Nat) :
    (cfg_A b (k + 1) 0) [target]⊢⁺ (cfg_A b k 1) := by
  unfold cfg_A
  rw [ListBlank.append_pow_add_rev ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b)
    ([1, 0] : List (Fin 2)) k 1]
  simp only [list_pow_succ, list_pow_zero, List.append_nil, ListBlank.append_cons,
    ListBlank.append_nil]
  bb_steps

private theorem step_F_b2_k0_c0 :
    (cfg_A 2 0 0) [target]⊢⁺ (cfg_A 3 0 3) := by
  unfold cfg_A
  simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
    ListBlank.append_cons, ListBlank.append_nil]
  bb_steps

private theorem C_bounce_0_ones (n : Nat) :
    (C_bounce 0 (([1] : List (Fin 2)) ^ n +> default)) [target]⊢⁺
    (cfg_A (n + 1) 0 3) := by
  have h1 := C_bounce_0 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 n] at h2
  have hn : 3 + n = n + 3 := by omega
  rw [hn] at h2
  have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (n + 3)) {{E}}> default) =
      cfg_E 0 (n + 3) := rfl
  rw [h_eq] at h2
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) (step_E_b3_to_cfg_A 0 n)

private theorem C_bounce_1_ones (n : Nat) :
    (C_bounce 1 (([1] : List (Fin 2)) ^ n +> default)) [target]⊢⁺
    (cfg_A (n + 3) 0 3) := by
  have h1 := C_bounce_1 (([1] : List (Fin 2)) ^ n +> default)
  have h2 := shift_E_ones n ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 n] at h2
  have hn : 5 + n = (n + 2) + 3 := by omega
  rw [hn] at h2
  have h_eq :
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ ((n + 2) + 3)) {{E}}> default) =
      cfg_E 0 ((n + 2) + 3) := rfl
  rw [h_eq] at h2
  have h3 := step_E_b3_to_cfg_A 0 (n + 2)
  have hn2 : (n + 2) + 1 = n + 3 := by omega
  rw [hn2] at h3
  exact ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3

private theorem C_bounce_2_ones_halt (n : Nat) :
    ∃ cfg', ((C_bounce 2 (([1] : List (Fin 2)) ^ n +> default)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone :=
  ⟨_, C_bounce_2 (([1] : List (Fin 2)) ^ n +> default), isNone_step_D_00 _ _⟩

private theorem C_bounce_3_ones (b n : Nat) :
    (C_bounce (b + 3) (([1] : List (Fin 2)) ^ n +> default)) [target]⊢⁺
    (cfg_A (b + 1) 0 (n + 2)) := by
  have h1 := C_bounce_3 b (([1] : List (Fin 2)) ^ n +> default)
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 n default, <- cfg_A_eq_F_R] at h1
  have hn : 2 + n = n + 2 := by omega
  rwa [hn] at h1

private theorem rule_A_ksucc_c0 (b k : Nat) :
    (cfg_A b (k + 1) 0) [target]⊢⁺ (cfg_A b k 1) :=
  step_F_ksucc_c0 b k

private theorem rule_A_b0_k0_c0 :
    (cfg_A 0 0 0) [target]⊢⁺ (cfg_A 4 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b0_to_D100 0 default) (D100_nil_to_C_bounce 0 0))
    (C_bounce_0_ones 3)

private theorem rule_A_b1_k0_c0 :
    (cfg_A 1 0 0) [target]⊢⁺ (cfg_A 6 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b1_to_D100 0 default) (D100_nil_to_C_bounce 0 1))
    (C_bounce_0_ones 5)

private theorem rule_A_b2_k0_c0 :
    (cfg_A 2 0 0) [target]⊢⁺ (cfg_A 3 0 3) :=
  step_F_b2_k0_c0

private theorem rule_A_b3_k0_c0 :
    (cfg_A 3 0 0) [target]⊢⁺ (cfg_A 6 0 3) :=
  ReachesPlus.trans (ReachesPlus.trans (F_R_b3_to_D100 0 0 default) (D100_nil_to_C_bounce 1 0))
    (C_bounce_1_ones 3)

private theorem rule_A_b4_k0_c0_halt :
    ∃ cfg', ((cfg_A 4 0 0) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt 3
  exact ⟨cfg', ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 1 0 default) (D100_nil_to_C_bounce 2 0)) h_step, h_halt⟩

private theorem rule_A_b5_k0_c0 (b : Nat) :
    (cfg_A (b + 5) 0 0) [target]⊢⁺ (cfg_A (b + 1) 0 5) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  exact ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 (b + 2) 0 default) (D100_nil_to_C_bounce (b + 3) 0))
    (C_bounce_3_ones b 3)

private theorem rule_A_b0_c1 (k : Nat) :
    (cfg_A 0 k 1) [target]⊢⁺ (cfg_A (2 * k + 6) 0 3) :=
  ReachesPlus.trans
    (ReachesPlus.trans (F_R_b0_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 k))
    (C_bounce_0_ones (2 * k + 5))

private theorem rule_A_b1_c1 (k : Nat) :
    (cfg_A 1 k 1) [target]⊢⁺ (cfg_A (2 * k + 8) 0 3) := by
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b1_to_D100 k ([1] +> default)) (D100_one_to_C_bounce 0 (k + 1)))
    (C_bounce_0_ones (2 * (k + 1) + 5))
  have hk : (2 * (k + 1) + 5) + 1 = 2 * k + 8 := by omega
  rwa [hk] at h

private theorem rule_A_b2_k0_c1 (c : Nat) :
    (cfg_A 2 0 (c + 1)) [target]⊢⁺ (cfg_A 5 0 c) :=
  step_F_b2_k0 c

private theorem rule_A_b3_c1 (k : Nat) :
    (cfg_A 3 k 1) [target]⊢⁺ (cfg_A (2 * k + 8) 0 3) := by
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 0 k ([1] +> default)) (D100_one_to_C_bounce 1 k))
    (C_bounce_1_ones (2 * k + 5))
  have hk : (2 * k + 5) + 3 = 2 * k + 8 := by omega
  rwa [hk] at h

private theorem rule_A_b4_c1_halt (k : Nat) :
    ∃ cfg', ((cfg_A 4 k 1) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  obtain ⟨cfg', h_step, h_halt⟩ := C_bounce_2_ones_halt (2 * k + 5)
  exact ⟨cfg', ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 1 k ([1] +> default)) (D100_one_to_C_bounce 2 k)) h_step,
    h_halt⟩

private theorem rule_A_b5_c1 (b k : Nat) :
    (cfg_A (b + 5) k 1) [target]⊢⁺ (cfg_A (b + 1) 0 (2 * k + 7)) := by
  have hb : b + 5 = (b + 2) + 3 := by omega
  rw [hb]
  have h := ReachesPlus.trans
    (ReachesPlus.trans (F_R_b3_to_D100 (b + 2) k ([1] +> default)) (D100_one_to_C_bounce (b + 3) k))
    (C_bounce_3_ones b (2 * k + 5))
  have hk : (2 * k + 5) + 2 = 2 * k + 7 := by omega
  rwa [hk] at h

private theorem rule_A_b0_c2 (k c : Nat) :
    (cfg_A 0 k (c + 2)) [target]⊢⁺ (cfg_A 1 (k + 1) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b0_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 k (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

private theorem rule_A_b1_c2 (k c : Nat) :
    (cfg_A 1 k (c + 2)) [target]⊢⁺ (cfg_A 1 (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

private theorem rule_A_b3_c2 (b k c : Nat) :
    (cfg_A (b + 3) k (c + 2)) [target]⊢⁺ (cfg_A (b + 1) (k + 2) c) := by
  have hc : (([1] : List (Fin 2)) ^ (c + 2) +> (default : ListBlank (Fin 2))) =
      [1, 1] +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
    rfl
  have h1 := F_R_b3_to_D100 b k (([1] : List (Fin 2)) ^ (c + 2) +> default)
  rw [hc] at h1
  have h2 := D100_succ_11 b k (([1] : List (Fin 2)) ^ c +> default)
  exact ReachesPlus.trans h1 h2

/-! ## Closure of the Pattern Set -/

private theorem closes_A_c0 (b k : Nat) : StepsToClosed target ps (cfg_A b k 0) := by
  rcases k with _ | k'
  · rcases b with _ | _ | _ | _ | _ | b'
    · exact StepsToClosed.of_isInPatternSet rule_A_b0_k0_c0 (in_ps_A 4 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_A_b1_k0_c0 (in_ps_A 6 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_A_b2_k0_c0 (in_ps_A 3 0 3)
    · exact StepsToClosed.of_isInPatternSet rule_A_b3_k0_c0 (in_ps_A 6 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_A_b4_k0_c0_halt
      exact StepsToClosed.of_halting h_step h_halt
    · exact StepsToClosed.of_isInPatternSet (rule_A_b5_k0_c0 b') (in_ps_A (b' + 1) 0 5)
  · exact StepsToClosed.of_isInPatternSet (rule_A_ksucc_c0 b k') (in_ps_A b k' 1)

private theorem closes_A_b0 (k c : Nat) : StepsToClosed target ps (cfg_A 0 k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 0 k
  · exact StepsToClosed.of_isInPatternSet (rule_A_b0_c1 k) (in_ps_A (2 * k + 6) 0 3)
  · exact StepsToClosed.of_isInPatternSet (rule_A_b0_c2 k c') (in_ps_A 1 (k + 1) c')

private theorem closes_A_b1 (k c : Nat) : StepsToClosed target ps (cfg_A 1 k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 1 k
  · exact StepsToClosed.of_isInPatternSet (rule_A_b1_c1 k) (in_ps_A (2 * k + 8) 0 3)
  · exact StepsToClosed.of_isInPatternSet (rule_A_b1_c2 k c') (in_ps_A 1 (k + 2) c')

private theorem closes_A_b3 (b k c : Nat) : StepsToClosed target ps (cfg_A (b + 3) k c) := by
  rcases c with _ | _ | c'
  · exact closes_A_c0 (b + 3) k
  · rcases b with _ | _ | b'
    · exact StepsToClosed.of_isInPatternSet (rule_A_b3_c1 k) (in_ps_A (2 * k + 8) 0 3)
    · obtain ⟨cfg', h_step, h_halt⟩ := rule_A_b4_c1_halt k
      exact StepsToClosed.of_halting h_step h_halt
    · exact StepsToClosed.of_isInPatternSet (rule_A_b5_c1 b' k) (in_ps_A (b' + 1) 0 (2 * k + 7))
  · exact StepsToClosed.of_isInPatternSet (rule_A_b3_c2 b k c') (in_ps_A (b + 1) (k + 2) c')

private theorem step_F_R_b2_one (k : Nat) (r : ListBlank (Fin 2)) :
    (F_R 2 k ([1] +> r)) [target]⊢⁺
    (F_R 5 0 (([0, 1] : List (Fin 2)) ^ k +> r)) := by
  unfold F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_FA_left k ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) ([0,
          1] +> r)
  have h2 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{F}}>
      ([0] +> (([0, 1] : List (Fin 2)) ^ k +> ([0, 1] +> r))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) {{F}}>
        ([0, 0] +> (([0, 1] : List (Fin 2)) ^ k +> r))) := by
    rw [ListBlank.append_pow_succ' ([0, 1] : List (Fin 2)) k r,
      ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) k r]
    simp only [list_pow_succ, list_pow_zero, List.cons_append, List.nil_append, List.append_nil,
      ListBlank.append_cons, ListBlank.append_nil]
    bb_steps
  exact ReachesStar.trans_plus h1 h2

private theorem step_E_01_to_F_R (b : Nat) (r : ListBlank (Fin 2)) :
    (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ b) {{E}}> ([0, 1] +> r))
    [target]⊢⁺
    (F_R b 0 r) := by
  unfold F_R
  simp only [list_pow_zero, ListBlank.append_nil]
  bb_steps

def Odd_cfg (p k n m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  F_R (2 * p + 1) k
    (([1] : List (Fin 2)) ^ (2 * n) +>
      (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default)))

def ETail_cfg (k m c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) {{E}}>
    (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default)))

private theorem rule_A_b2_ksucc_c1 (k c : Nat) :
    (cfg_A 2 (k + 1) (c + 1)) [target]⊢⁺ (Odd_cfg 2 0 0 k c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [cfg_A_eq_F_R, ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  exact step_F_R_b2_one (k + 1) (([1] : List (Fin 2)) ^ c +> default)

private theorem step_Odd_nsucc_p0 (k n m c : Nat) :
    (Odd_cfg 0 k (n + 1) m c) [target]⊢⁺ (Odd_cfg 0 (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  rw [hn, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +> r))
  have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact ReachesPlus.trans h1 h2

private theorem step_Odd_nsucc_psucc (p k n m c : Nat) :
    (Odd_cfg (p + 1) k (n + 1) m c) [target]⊢⁺ (Odd_cfg p (k + 2) n m c) := by
  unfold Odd_cfg
  set r := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hn : 2 * (n + 1) = 2 + 2 * n := by omega
  have hp : 2 * (p + 1) + 1 = (2 * p) + 3 := by omega
  rw [hn, hp, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
  have h1 :=
    F_R_b3_to_D100 (2 * p) k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +> r))
  have h2 := D100_succ_11 (2 * p) k (([1] : List (Fin 2)) ^ (2 * n) +> r)
  exact ReachesPlus.trans h1 h2

private theorem step_Odd_n0_p0 (k m c : Nat) :
    (Odd_cfg 0 k 0 m c) [target]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 0 (k + 1) r'
  have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
  have h4 := shift_E_ones (2 * (k + 1) + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) r'
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
  have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4

private theorem step_Odd_n0_p1 (k m c : Nat) :
    (Odd_cfg 1 k 0 m c) [target]⊢⁺ (ETail_cfg k m c) := by
  unfold Odd_cfg ETail_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
  set r' := (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))
  have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce 1 k r'
  have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  have h4 := shift_E_ones (2 * k + 4)
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 5) r'
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
  have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
  rw [hk] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4

private theorem step_Odd_n0_p2_m0 (p k c : Nat) :
    (Odd_cfg (p + 2) k 0 0 c) [target]⊢⁺ (cfg_A (2 * p + 1) 0 (2 * (k + 3) + c)) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) 0]
  simp only [list_pow_zero, ListBlank.append_nil]
  set r' := (([1] : List (Fin 2)) ^ c +> default)
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk, <- ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (k + 3)) c default,
    <- cfg_A_eq_F_R] at h3
  exact ReachesPlus.trans (ReachesPlus.trans h1 h2) h3

private theorem step_Odd_n0_p2_msucc (p k m c : Nat) :
    (Odd_cfg (p + 2) k 0 (m + 1) c) [target]⊢⁺ (Odd_cfg p 0 (k + 3) m c) := by
  unfold Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (m + 1)]
  set r' := (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))
  have hp : 2 * (p + 2) + 1 = (2 * p + 2) + 3 := by omega
  rw [hp]
  have h1 := F_R_b3_to_D100 (2 * p + 2) k ([0, 1] +> r')
  have h2 := D100_01_to_C_bounce (2 * p + 3) k r'
  have h3 := C_bounce_3 (2 * p) (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
  rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
  have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
  rw [hk] at h3
  exact ReachesPlus.trans (ReachesPlus.trans h1 h2) h3

private theorem step_ETail_m0 (k c : Nat) :
    (ETail_cfg k 0 c) [target]⊢⁺ (cfg_A (2 * k + c + 7) 0 3) := by
  unfold ETail_cfg
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := shift_E_ones c
    ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * (k + 4) + 1)) default
  rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (2 * (k + 4) + 1) c] at h1
  have hk : 2 * (k + 4) + 1 + c = (2 * k + c + 6) + 3 := by omega
  rw [hk] at h1
  have h2 := step_E_b3_to_cfg_A 0 (2 * k + c + 6)
  have hk2 : (2 * k + c + 6) + 1 = 2 * k + c + 7 := by omega
  rw [hk2] at h2
  exact ReachesStar.trans_plus h1 h2

private theorem step_ETail_m1 (k c : Nat) :
    (ETail_cfg k 1 c) [target]⊢⁺ (cfg_A (2 * (k + 4) + 1) 0 c) := by
  unfold ETail_cfg
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) 0]
  simp only [list_pow_zero, ListBlank.append_nil]
  exact step_E_01_to_F_R (2 * (k + 4) + 1) (([1] : List (Fin 2)) ^ c +> default)

private theorem step_ETail_m2 (k m c : Nat) :
    (ETail_cfg k (m + 2) c) [target]⊢⁺ (Odd_cfg (k + 4) 0 0 m c) := by
  unfold ETail_cfg Odd_cfg
  simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (m + 1)]
  exact step_E_01_to_F_R (2 * (k + 4) + 1)
    (([0, 1] : List (Fin 2)) ^ (m + 1) +> (([1] : List (Fin 2)) ^ c +> default))

private theorem closes_E_01_tail (b m c : Nat)
    (ih : ∀ m' < m + 1, ∀ p k, StepsToClosed target ps (F_R (2 * p + 1) k
      (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default)))) :
    StepsToClosed target ps
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1)) {{E}}>
        (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  rcases m with _ | m'
  · simp only [list_pow_zero, ListBlank.append_nil]
    have h1 := shift_E_ones c ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b
            + 1)) default
    rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) (2 * b + 1) c] at h1
    have h_eq : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ (2 * b + 1 + c)) {{E}}>
            default) =
        cfg_E 0 (2 * b + 1 + c) := rfl
    rw [h_eq] at h1
    exact StepsToClosed.of_reachesStar h1 (closes_E 0 (2 * b + 1 + c))
  · rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m']
    have h1 := step_E_01_to_F_R (2 * b + 1) (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2))
            ^ c +> default))
    exact StepsToClosed.of_reachesPlus h1 (ih m' (by omega) b 0)

private theorem closes_odd_even_ones (n : Nat) (r : ListBlank (Fin 2))
    (h_base : ∀ p k, StepsToClosed target ps (F_R (2 * p + 1) k r)) :
    ∀ p k, StepsToClosed target ps (F_R (2 * p + 1) k (([1] : List (Fin 2)) ^ (2 * n) +> r)) := by
  induction n with
  | zero =>
    intro p k
    simp only [Nat.mul_zero, list_pow_zero, ListBlank.append_nil]
    exact h_base p k
  | succ n ih =>
    intro p k
    have hn : 2 * (n + 1) = 2 + 2 * n := by omega
    rw [hn, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * n) r]
    rcases p with _ | p'
    · have h1 := F_R_b1_to_D100 k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2 * n) +>
            r))
      have h2 := D100_0_11 (k + 1) (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact StepsToClosed.of_reachesPlus (ReachesPlus.trans h1 h2) (ih 0 (k + 2))
    · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
      rw [hp]
      have h1 := F_R_b3_to_D100 (2 * p') k (([1] : List (Fin 2)) ^ 2 +> (([1] : List (Fin 2)) ^ (2
              * n) +> r))
      have h2 := D100_succ_11 (2 * p') k (([1] : List (Fin 2)) ^ (2 * n) +> r)
      exact StepsToClosed.of_reachesPlus (ReachesPlus.trans h1 h2) (ih p' (k + 2))

private theorem closes_odd_m (m : Nat) (c : Nat) :
    ∀ p k, StepsToClosed target ps (F_R (2 * p + 1) k
      (([0, 1] : List (Fin 2)) ^ m +> (([1] : List (Fin 2)) ^ c +> default))) := by
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro p k
    rcases m with _ | m'
    · simp only [list_pow_zero, ListBlank.append_nil, <- cfg_A_eq_F_R]
      rcases p with _ | p'
      · exact closes_A_b1 k c
      · have hp : 2 * (p' + 1) + 1 = (2 * p') + 3 := by omega
        rw [hp]
        exact closes_A_b3 (2 * p') k c
    · rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m']
      set r' := (([0, 1] : List (Fin 2)) ^ m' +> (([1] : List (Fin 2)) ^ c +> default))
      rcases p with _ | _ | p''
      · have h1 := F_R_b1_to_D100 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 0 (k + 1) r'
        have h3 := C_bounce_0 (([1] : List (Fin 2)) ^ (2 * (k + 1) + 4) +> r')
        have h4 := shift_E_ones (2 * (k + 1) + 4) ((default : ListBlank (Fin 2)) <+ ([1] :
                List (Fin 2)) ^ 3) r'
        rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 (2 * (k + 1) + 4)] at h4
        have hk : 3 + (2 * (k + 1) + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact StepsToClosed.of_reachesPlus
          (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have h1 := F_R_b3_to_D100 0 k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce 1 k r'
        have h3 := C_bounce_1 (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        have h4 := shift_E_ones (2 * k + 4) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin
                2)) ^ 5) r'
        rw [<- ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 5 (2 * k + 4)] at h4
        have hk : 5 + (2 * k + 4) = 2 * (k + 4) + 1 := by omega
        rw [hk] at h4
        exact StepsToClosed.of_reachesPlus
          (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3) h4)
          (closes_E_01_tail (k + 4) m' c ih)
      · have hp : 2 * (p'' + 2) + 1 = (2 * p'' + 2) + 3 := by omega
        rw [hp]
        have h1 := F_R_b3_to_D100 (2 * p'' + 2) k ([0, 1] +> r')
        have h2 := D100_01_to_C_bounce (2 * p'' + 3) k r'
        have h3 := C_bounce_3 (2 * p'') (([1] : List (Fin 2)) ^ (2 * k + 4) +> r')
        rw [<- ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * k + 4) r'] at h3
        have hk : 2 + (2 * k + 4) = 2 * (k + 3) := by omega
        rw [hk] at h3
        exact StepsToClosed.of_reachesPlus (ReachesPlus.trans (ReachesPlus.trans h1 h2) h3)
          (closes_odd_even_ones (k + 3) r' (ih m' (by omega)) p'' 0)

private theorem closes_A_b2 (k c : Nat) : StepsToClosed target ps (cfg_A 2 k c) := by
  rcases c with _ | c'
  · exact closes_A_c0 2 k
  · rw [cfg_A_eq_F_R, ListBlank.append_pow_succ ([1] : List (Fin 2)) c' default]
    have h1 := step_F_R_b2_one k (([1] : List (Fin 2)) ^ c' +> default)
    exact StepsToClosed.of_reachesPlus h1 (closes_odd_m k c' 2 0)

private theorem closes_A_all (b k c : Nat) : StepsToClosed target ps (cfg_A b k c) := by
  rcases b with _ | _ | _ | b'
  · exact closes_A_b0 k c
  · exact closes_A_b1 k c
  · exact closes_A_b2 k c
  · exact closes_A_b3 b' k c

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 5 0 2, init_reaches_A_502, in_ps_A 5 0 2⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  rw [eval_pat_A]
  exact closes_A_all (vars 0) (vars 1) (vars 2)

/-- `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target := ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0LF_1LC0LD_1RD1LB_---1RE_0RA1RE_1LA0LE`. -/
inductive State
  /-- $A(b, k, c) := 0^\infty\,1^b\,(01)^k\,\mathrm{F}{>}\,0\,0\,1^c\,0^\infty$. -/
  | A (b k c : ℕ)
  /-- $Odd(p, k, n, m, c) :=
  0^\infty\,1^{2p+1}\,(01)^k\,\mathrm{F}{>}\,0\,0\,1^{2n}\,(01)^{m+1}\,1^c\,0^\infty$. -/
  | Odd (p k n m c : ℕ)
  /-- $ETail(k, m, c) := 0^\infty\,1^{2k+9}\,\mathrm{E}{>}\,(01)^m\,1^c\,0^\infty$. -/
  | ETail (k m c : ℕ)

/-- Initial symbolic state $A(5, 0, 2)$, reached from the blank tape. -/
def start : State := .A 5 0 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A b k c => cfg_A b k c
  | .Odd p k n m c => Odd_cfg p k n m c
  | .ETail k m c => ETail_cfg k m c

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (.Odd 2 0 0 k 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 1) c)) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2) c)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (.Odd 2 0 0 k (c + 1))) fun b =>
    some (.A (b + 1) (k + 2) c)
  | .Odd p k (n + 1) m c =>
    Nat.casesOn p (some (.Odd 0 (k + 2) n m c)) fun p =>
    some (.Odd p (k + 2) n m c)
  | .Odd p k 0 m c =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn p (some (.ETail k m c)) fun p =>
    Nat.casesOn m (some (.A (2 * p + 1) 0 (2 * (k + 3) + c))) fun m =>
    some (.Odd p 0 (k + 3) m c)
  | .ETail k 0 c => some (.A (2 * k + c + 7) 0 3)
  | .ETail k 1 c => some (.A (2 * (k + 4) + 1) 0 c)
  | .ETail k (m + 2) c => some (.Odd (k + 4) 0 0 m c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_A_502 (fun s => ?_)
  match s with
  | .A b (k + 1) 0 => exact rule_A_ksucc_c0 b k
  | .A 0 0 0 => exact rule_A_b0_k0_c0
  | .A 1 0 0 => exact rule_A_b1_k0_c0
  | .A 2 0 0 => exact rule_A_b2_k0_c0
  | .A 3 0 0 => exact rule_A_b3_k0_c0
  | .A 4 0 0 =>
    obtain ⟨cfg', h1, h2⟩ := rule_A_b4_k0_c0_halt
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .A (b + 5) 0 0 => exact rule_A_b5_k0_c0 b
  | .A 0 k 1 => exact rule_A_b0_c1 k
  | .A 1 k 1 => exact rule_A_b1_c1 k
  | .A 2 0 1 => exact rule_A_b2_k0_c1 0
  | .A 2 (k + 1) 1 => exact rule_A_b2_ksucc_c1 k 0
  | .A 3 k 1 => exact rule_A_b3_c1 k
  | .A 4 k 1 =>
    obtain ⟨cfg', h1, h2⟩ := rule_A_b4_c1_halt k
    exact ⟨cfg', ReachesPlus.to_star h1, h2⟩
  | .A (b + 5) k 1 => exact rule_A_b5_c1 b k
  | .A 0 k (c + 2) => exact rule_A_b0_c2 k c
  | .A 1 k (c + 2) => exact rule_A_b1_c2 k c
  | .A 2 0 (c + 2) => exact rule_A_b2_k0_c1 (c + 1)
  | .A 2 (k + 1) (c + 2) => exact rule_A_b2_ksucc_c1 k (c + 1)
  | .A (b + 3) k (c + 2) => exact rule_A_b3_c2 b k c
  | .Odd 0 k (n + 1) m c => exact step_Odd_nsucc_p0 k n m c
  | .Odd (p + 1) k (n + 1) m c => exact step_Odd_nsucc_psucc p k n m c
  | .Odd 0 k 0 m c => exact step_Odd_n0_p0 k m c
  | .Odd 1 k 0 m c => exact step_Odd_n0_p1 k m c
  | .Odd (p + 2) k 0 0 c => exact step_Odd_n0_p2_m0 p k c
  | .Odd (p + 2) k 0 (m + 1) c => exact step_Odd_n0_p2_msucc p k m c
  | .ETail k 0 c => exact step_ETail_m0 k c
  | .ETail k 1 c => exact step_ETail_m1 k c
  | .ETail k (m + 2) c => exact step_ETail_m2 k m c

/-- `target` halts from the blank tape iff `next` halts from `start` (Level B). -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive MidState where
  | A (b k c : ℕ)

private def midStart : MidState := .A 5 0 2

private def midToState : MidState → State
  | .A b k c => .A b k c

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midEvalOdd : ℕ → ℕ → ℕ → ℕ → ℕ → MidState
  | 0, p, k, n, c =>
    Nat.casesOn (p - n) (.A (2 * (k + 2 * n) + c + 7) 0 3) fun d =>
    Nat.casesOn d (.A (2 * (k + 2 * n) + c + 7) 0 3) fun p' =>
    .A (2 * p' + 1) 0 (2 * (k + 2 * n + 3) + c)
  | 1, p, k, n, c =>
    Nat.casesOn (p - n) (.A (2 * (k + 2 * n + 4) + 1) 0 c) fun d =>
    Nat.casesOn d (.A (2 * (k + 2 * n + 4) + 1) 0 c) fun p' =>
    midEvalOdd 0 p' 0 (k + 2 * n + 3) c
  | m + 2, p, k, n, c =>
    Nat.casesOn (p - n) (midEvalOdd m (k + 2 * n + 4) 0 0 c) fun d =>
    Nat.casesOn d (midEvalOdd m (k + 2 * n + 4) 0 0 c) fun p' =>
    midEvalOdd (m + 1) p' 0 (k + 2 * n + 3) c

private def midNext : MidState → Option MidState
  | .A b k 0 =>
    Nat.casesOn k
      (Nat.casesOn b (some (.A 4 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b (some (.A 3 0 3)) fun b =>
       Nat.casesOn b (some (.A 6 0 3)) fun b =>
       Nat.casesOn b none fun b =>
       some (.A (b + 1) 0 5))
      fun k => some (.A b k 1)
  | .A b k 1 =>
    Nat.casesOn b (some (.A (2 * k + 6) 0 3)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 0)) fun k => some (midEvalOdd k 2 0 0 0)) fun b =>
    Nat.casesOn b (some (.A (2 * k + 8) 0 3)) fun b =>
    Nat.casesOn b none fun b =>
    some (.A (b + 1) 0 (2 * k + 7))
  | .A b k (c + 2) =>
    Nat.casesOn b (some (.A 1 (k + 2 * (c / 2) + 1) (c % 2))) fun b =>
    Nat.casesOn b (some (.A 1 (k + 2 * (c / 2 + 1)) (c % 2))) fun b =>
    Nat.casesOn b
      (Nat.casesOn k (some (.A 5 0 (c + 1))) fun k => some (midEvalOdd k 2 0 0 (c + 1))) fun b =>
    let m := min ((b + 2) / 2) ((c + 2) / 2)
    some (.A (b + 3 - 2 * m) (k + 2 * m) (c + 2 - 2 * m))

private theorem reaches_A_b1_diag (m : ℕ) (k c : ℕ) :
    CollatzReachesStar next (.A 1 k (c + 2 * m)) (.A 1 (k + 2 * m) c) := by
  induction m generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h_next : next (.A 1 k (c + 2 * (m + 1))) =
        some (.A 1 (k + 2) (c + 2 * m)) := by
      have hc : c + 2 * (m + 1) = (c + 2 * m) + 2 := by omega
      rw [hc]
      rfl
    have ih' := ih (k + 2)
    have hk : k + 2 + 2 * m = k + 2 * (m + 1) := by omega
    rw [hk] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_A_b0_drain (k c : ℕ) :
    CollatzStepsTo next (.A 0 k (c + 2))
      (some (.A 1 (k + 2 * (c / 2) + 1) (c % 2))) := by
  have h_head : next (.A 0 k (c + 2)) = some (.A 1 (k + 1) c) := rfl
  have h_star := reaches_A_b1_diag (c / 2) (k + 1) (c % 2)
  have hc : c % 2 + 2 * (c / 2) = c := by omega
  have hk : k + 1 + 2 * (c / 2) = k + 2 * (c / 2) + 1 := by omega
  rw [hc, hk] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_A_b1_drain (k c : ℕ) :
    CollatzStepsTo next (.A 1 k (c + 2))
      (some (.A 1 (k + 2 * (c / 2 + 1)) (c % 2))) := by
  have h_head : next (.A 1 k (c + 2)) = some (.A 1 (k + 2) c) := rfl
  have h_star := reaches_A_b1_diag (c / 2) (k + 2) (c % 2)
  have hc : c % 2 + 2 * (c / 2) = c := by omega
  have hk : k + 2 + 2 * (c / 2) = k + 2 * (c / 2 + 1) := by omega
  rw [hc, hk] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_A_b3_diag (m : ℕ) (b k c : ℕ) :
    CollatzReachesStar next (.A (b + 2 * m + 1) k (c + 2 * m))
      (.A (b + 1) (k + 2 * m) c) := by
  induction m generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | succ m ih =>
    have h_next : next (.A (b + 2 * (m + 1) + 1) k (c + 2 * (m + 1))) =
        some (.A (b + 2 * m + 1) (k + 2) (c + 2 * m)) := by
      have hb : b + 2 * (m + 1) + 1 = (b + 2 * m) + 3 := by omega
      have hc : c + 2 * (m + 1) = (c + 2 * m) + 2 := by omega
      rw [hb, hc]
      rfl
    have ih' := ih (k + 2)
    have hk : k + 2 + 2 * m = k + 2 * (m + 1) := by omega
    rw [hk] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_A_b3_drain (b k c : ℕ) :
    CollatzStepsTo next (.A (b + 3) k (c + 2))
      (some (.A (b + 3 - 2 * min ((b + 2) / 2) ((c + 2) / 2))
        (k + 2 * min ((b + 2) / 2) ((c + 2) / 2))
        (c + 2 - 2 * min ((b + 2) / 2) ((c + 2) / 2)))) := by
  let m := min ((b + 2) / 2) ((c + 2) / 2)
  have hm_pos : 0 < m := by omega
  obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm_pos)
  have h_head : next (.A (b + 3) k (c + 2)) = some (.A (b + 1) (k + 2) c) := rfl
  have h_star := reaches_A_b3_diag m' (b + 2 - 2 * m) (k + 2) (c + 2 - 2 * m)
  have hb1 : b + 2 - 2 * m + 2 * m' + 1 = b + 1 := by omega
  have hc1 : c + 2 - 2 * m + 2 * m' = c := by omega
  have hb2 : b + 2 - 2 * m + 1 = b + 3 - 2 * m := by omega
  have hk1 : k + 2 + 2 * m' = k + 2 * m := by omega
  rw [hb1, hc1, hb2, hk1] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_Odd_n : ∀ (n p k m c : ℕ),
    CollatzReachesStar next (.Odd p k n m c) (.Odd (p - n) (k + 2 * n) 0 m c)
  | 0, p, k, m, c => by
    simp only [Nat.sub_zero, Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | n + 1, 0, k, m, c => by
    have ih := reaches_Odd_n n 0 (k + 2) m c
    have hk : k + 2 + 2 * n = k + 2 * (n + 1) := by omega
    rw [Nat.zero_sub, hk] at ih
    rw [Nat.zero_sub]
    exact CollatzReachesStar.head rfl ih
  | n + 1, p + 1, k, m, c => by
    have ih := reaches_Odd_n n p (k + 2) m c
    have hp : p - n = (p + 1) - (n + 1) := by omega
    have hk : k + 2 + 2 * n = k + 2 * (n + 1) := by omega
    rw [hp, hk] at ih
    exact CollatzReachesStar.head rfl ih

private theorem stepsTo_Odd : ∀ (m p k n c : ℕ),
    CollatzStepsTo next (.Odd p k n m c) (some (midToState (midEvalOdd m p k n c)))
  | 0, p, k, n, c => by
    refine CollatzStepsTo.of_reachesStar (reaches_Odd_n n p k 0 c) ?_
    dsimp [midEvalOdd]
    rcases p - n with _ | _ | p'
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.of_eq rfl
  | 1, p, k, n, c => by
    refine CollatzStepsTo.of_reachesStar (reaches_Odd_n n p k 1 c) ?_
    dsimp [midEvalOdd]
    rcases p - n with _ | _ | p'
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
    · exact CollatzStepsTo.head rfl (stepsTo_Odd 0 p' 0 (k + 2 * n + 3) c)
  | m + 2, p, k, n, c => by
    refine CollatzStepsTo.of_reachesStar (reaches_Odd_n n p k (m + 2) c) ?_
    dsimp [midEvalOdd]
    rcases p - n with _ | _ | p'
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (stepsTo_Odd m (k + 2 * n + 4) 0 0 c))
    · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (stepsTo_Odd m (k + 2 * n + 4) 0 0 c))
    · exact CollatzStepsTo.head rfl (stepsTo_Odd (m + 1) p' 0 (k + 2 * n + 3) c)

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  refine is_valid_acceleration.of_collatz (embed := midToState)
    (CollatzReachesStar.refl next start) ?_
  rintro ⟨b, k, c⟩
  rcases c with _ | _ | c
  · rcases k with _ | k
    · rcases b with _ | _ | _ | _ | _ | b <;> exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
  · rcases b with _ | _ | _ | _ | _ | b
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · rcases k with _ | k
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_Odd k 2 0 0 0)
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
  · rcases b with _ | _ | _ | b
    · exact reaches_A_b0_drain k c
    · exact reaches_A_b1_drain k c
    · rcases k with _ | k
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.head rfl (stepsTo_Odd k 2 0 0 (c + 1))
    · have h_eq : Option.map midToState (midNext (.A (b + 3) k (c + 2))) =
          some (.A (b + 3 - 2 * min ((b + 2) / 2) ((c + 2) / 2))
            (k + 2 * min ((b + 2) / 2) ((c + 2) / 2))
            (c + 2 - 2 * min ((b + 2) / 2) ((c + 2) / 2))) := rfl
      rw [h_eq]
      exact reaches_A_b3_drain b k c

/-- Single-family high-level state space
$A(b, c) := 0^\infty\,1^b\,\mathrm{F}{>}\,00\,1^c\,0^\infty$ (the configuration $A(b, 0, c)$)
for the high-level Collatz-like acceleration. -/
inductive HighLevelState where
  /-- $A(b, c) := 0^\infty\,1^b\,\mathrm{F}{>}\,00\,1^c\,0^\infty$. -/
  | A (b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial state $A(5, 2)$ for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .A 5 2

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .A b c => .A b 0 c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

private def toMid : HighLevelState → MidState
  | .A b c => .A b 0 c

/-- Outcome $F(m, p, n, c)$ of the intermediate family `Odd p 0 n m c` when run until it returns to
a configuration $A(b, c)$. -/
def evalOdd (m p n c : ℕ) : HighLevelState :=
  if m = 0 then
    if p ≤ n + 1 then .A (4 * n + c + 7) 3 else .A (2 * (p - n - 2) + 1) (4 * n + c + 6)
  else if m = 1 then
    if p ≤ n + 1 then .A (4 * n + 9) c else evalOdd 0 (p - n - 2) (2 * n + 3) c
  else
    if p ≤ n + 1 then evalOdd (m - 2) (2 * n + 4) 0 c
    else evalOdd (m - 1) (p - n - 2) (2 * n + 3) c
termination_by m
decreasing_by all_goals omega

/-- High-level accelerated Collatz-like transition function on $A(b, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .A b c =>
    if b = 0 then some (.A (2 * c + 4) 3)
    else if b = 2 then (if c = 0 then some (.A 3 3) else some (.A 5 (c - 1)))
    else if 2 * (c / 2) + 5 ≤ b then some (.A (b - 2 * (c / 2) - 4) (2 * c + 5))
    else if b % 2 = 1 then some (.A (2 * c + 6) 3)
    else if b ≤ 2 * (c / 2) then some (evalOdd (b - 3) 2 0 (c - b + 1))
    else if b = 2 * (c / 2) + 2 then some (evalOdd (b - 4 + c % 2) 2 0 0)
    else none

private theorem toMid_evalOdd : ∀ m p n c, toMid (evalOdd m p n c) = midEvalOdd m p 0 n c
  | 0, p, n, c => by
    rw [evalOdd, midEvalOdd]
    simp only [↓reduceIte]
    rcases h : p - n with _ | _ | d
    all_goals
      split_ifs
      all_goals first
        | omega
        | exact congrArg₂ (fun x y => MidState.A x 0 y) (by omega) (by omega)
  | 1, p, n, c => by
    rw [evalOdd, midEvalOdd]
    simp only [one_ne_zero, ↓reduceIte]
    rcases h : p - n with _ | _ | d
    all_goals
      split_ifs
      all_goals first
        | omega
        | exact congrArg₂ (fun x y => MidState.A x 0 y) (by omega) (by omega)
        | (rw [toMid_evalOdd 0]
           exact congrArg₂ (fun x y => midEvalOdd 0 x 0 y c) (by omega) (by omega))
  | m + 2, p, n, c => by
    have hm0 : m + 2 ≠ 0 := by omega
    have hm1 : m + 2 ≠ 1 := by omega
    have hm2 : m + 2 - 2 = m := by omega
    have hm3 : m + 2 - 1 = m + 1 := by omega
    rw [evalOdd, midEvalOdd]
    simp only [hm0, hm1, hm2, hm3, ↓reduceIte]
    rcases h : p - n with _ | _ | d
    all_goals
      split_ifs
      all_goals first
        | omega
        | (rw [toMid_evalOdd m]
           exact congrArg₂ (fun x y => midEvalOdd m x 0 y c) (by omega) (by omega))
        | (rw [toMid_evalOdd (m + 1)]
           exact congrArg₂ (fun x y => midEvalOdd (m + 1) x 0 y c) (by omega) (by omega))

private theorem mid_b0 {k c k' c' : ℕ} (hk : k' = k + 2 * (c / 2) + 1) (hc : c' = c % 2) :
    midNext (.A 0 k (c + 2)) = some (.A 1 k' c') := by
  subst hk hc
  rfl

private theorem mid_b1 {k c k' c' : ℕ} (hk : k' = k + 2 * (c / 2 + 1)) (hc : c' = c % 2) :
    midNext (.A 1 k (c + 2)) = some (.A 1 k' c') := by
  subst hk hc
  rfl

private theorem mid_drain {b k c b' k' c' : ℕ}
    (hb : b' = b + 3 - 2 * min ((b + 2) / 2) ((c + 2) / 2))
    (hk : k' = k + 2 * min ((b + 2) / 2) ((c + 2) / 2))
    (hc : c' = c + 2 - 2 * min ((b + 2) / 2) ((c + 2) / 2)) :
    midNext (.A (b + 3) k (c + 2)) = some (.A b' k' c') := by
  subst hb hk hc
  rfl

private theorem mid_b1_small (k c n : ℕ) (hc : c < 2) (hn : n = 2 * (k + c) + 6) :
    CollatzStepsTo midNext (.A 1 k c) (some (.A n 0 3)) := by
  rcases c with _ | _ | c
  · rcases k with _ | k
    · subst hn
      exact CollatzStepsTo.of_eq rfl
    · obtain rfl : n = 2 * k + 8 := by omega
      exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
  · obtain rfl : n = 2 * k + 8 := by omega
    exact CollatzStepsTo.of_eq rfl
  · omega

private theorem mid_b1_all (k c n : ℕ) (hn : n = 2 * (k + c) + 6) :
    CollatzStepsTo midNext (.A 1 k c) (some (.A n 0 3)) := by
  rcases c with _ | _ | c
  · exact mid_b1_small k 0 n (by omega) hn
  · exact mid_b1_small k 1 n (by omega) hn
  · exact CollatzStepsTo.head (mid_b1 rfl rfl) (mid_b1_small _ _ n (by omega) (by omega))

private theorem mid_b0_all (c n : ℕ) (hn : n = 2 * c + 4) :
    CollatzStepsTo midNext (.A 0 0 c) (some (.A n 0 3)) := by
  rcases c with _ | _ | c
  · subst hn
    exact CollatzStepsTo.of_eq rfl
  · subst hn
    exact CollatzStepsTo.of_eq rfl
  · exact CollatzStepsTo.head (mid_b0 rfl rfl) (mid_b1_small _ _ n (by omega) (by omega))

private theorem mid_big (b c n m : ℕ) (hb : 2 * (c / 2) + 5 ≤ b) (hn : n = b - 2 * (c / 2) - 4)
    (hm : m = 2 * c + 5) : CollatzStepsTo midNext (.A b 0 c) (some (.A n 0 m)) := by
  obtain ⟨x, rfl⟩ : ∃ x, b = x + 5 := ⟨b - 5, by omega⟩
  rcases c with _ | _ | c
  · obtain rfl : n = x + 1 := by omega
    subst hm
    exact CollatzStepsTo.of_eq rfl
  · obtain rfl : n = x + 1 := by omega
    subst hm
    exact CollatzStepsTo.of_eq rfl
  · obtain rfl : n = x - 2 * (c / 2) - 2 + 1 := by omega
    rcases Nat.mod_two_eq_zero_or_one c with hc | hc
    · obtain rfl : m = 2 * (2 * (c / 2) + 1) + 7 := by omega
      exact CollatzStepsTo.head (mid_drain (b := x + 2) (k := 0) (c := c)
        (b' := x - 2 * (c / 2) - 2 + 5) (k' := 2 * (c / 2) + 1 + 1) (c' := 0)
        (by omega) (by omega) (by omega)) (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
    · obtain rfl : m = 2 * (2 * (c / 2) + 2) + 7 := by omega
      exact CollatzStepsTo.head (mid_drain (b := x + 2) (k := 0) (c := c)
        (b' := x - 2 * (c / 2) - 2 + 5) (k' := 2 * (c / 2) + 2) (c' := 1)
        (by omega) (by omega) (by omega)) (CollatzStepsTo.of_eq rfl)

private theorem mid_odd (b c n : ℕ) (hodd : b % 2 = 1) (hb : b ≤ 2 * (c / 2) + 3)
    (hn : n = 2 * c + 6) : CollatzStepsTo midNext (.A b 0 c) (some (.A n 0 3)) := by
  by_cases hb1 : b = 1
  · subst hb1
    exact mid_b1_all 0 c n (by omega)
  obtain ⟨j, rfl⟩ : ∃ j, b = 2 * j + 3 := ⟨(b - 3) / 2, by omega⟩
  by_cases hc : 2 * j + 2 ≤ c
  · obtain ⟨d, rfl⟩ : ∃ d, c = d + 2 * j + 2 := ⟨c - 2 * j - 2, by omega⟩
    exact CollatzStepsTo.head (mid_drain (b := 2 * j) (k := 0) (c := d + 2 * j) (b' := 1)
      (k' := 2 * j + 2) (c' := d) (by omega) (by omega) (by omega)) (mid_b1_all _ _ n (by omega))
  by_cases hj : j = 0
  · subst hj
    rcases c with _ | _ | c
    · subst hn
      exact CollatzStepsTo.of_eq rfl
    · subst hn
      exact CollatzStepsTo.of_eq rfl
    · omega
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 2 := ⟨c - 2, by omega⟩
  rcases Nat.mod_two_eq_zero_or_one c with hc2 | hc2
  · obtain rfl : n = 2 * (2 * j - 1) + 8 := by omega
    exact CollatzStepsTo.head (mid_drain (b := 2 * j) (k := 0) (c := c) (b' := 3)
      (k' := 2 * j - 1 + 1) (c' := 0) (by omega) (by omega) (by omega))
      (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
  · obtain rfl : n = 2 * (2 * j) + 8 := by omega
    exact CollatzStepsTo.head (mid_drain (b := 2 * j) (k := 0) (c := c) (b' := 3)
      (k' := 2 * j) (c' := 1) (by omega) (by omega) (by omega)) (CollatzStepsTo.of_eq rfl)

private theorem mid_even_le (b c m c' : ℕ) (heven : b % 2 = 0) (h4 : 4 ≤ b)
    (hb : b ≤ 2 * (c / 2)) (hm : m = b - 3) (hc : c' = c - b + 1) :
    CollatzStepsTo midNext (.A b 0 c) (some (toMid (evalOdd m 2 0 c'))) := by
  obtain ⟨j, rfl⟩ : ∃ j, b = 2 * j + 4 := ⟨(b - 4) / 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, c = e + 2 * j + 2 + 2 := ⟨c - 2 * j - 4, by omega⟩
  obtain rfl : m = 2 * j + 1 := by omega
  obtain rfl : c' = e + 1 := by omega
  rw [toMid_evalOdd]
  exact CollatzStepsTo.head (mid_drain (b := 2 * j + 1) (k := 0) (c := e + 2 * j + 2) (b' := 2)
    (k' := 2 * j + 1 + 1) (c' := e + 2) (by omega) (by omega) (by omega))
    (CollatzStepsTo.of_eq rfl)

private theorem mid_even_eq (b c m : ℕ) (h4 : 4 ≤ b) (hb : b = 2 * (c / 2) + 2)
    (hm : m = b - 4 + c % 2) :
    CollatzStepsTo midNext (.A b 0 c) (some (toMid (evalOdd m 2 0 0))) := by
  obtain ⟨j, rfl⟩ : ∃ j, b = 2 * j + 4 := ⟨b - 4 - (b - 4) / 2, by omega⟩
  rw [toMid_evalOdd]
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc
  · obtain rfl : c = 2 * j + 2 := by omega
    obtain rfl : m = 2 * j := by omega
    exact CollatzStepsTo.head (mid_drain (b := 2 * j + 1) (k := 0) (c := 2 * j) (b' := 2)
      (k' := 2 * j + 1 + 1) (c' := 0) (by omega) (by omega) (by omega))
      (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
  · obtain rfl : c = 2 * j + 1 + 2 := by omega
    obtain rfl : m = 2 * j + 1 := by omega
    exact CollatzStepsTo.head (mid_drain (b := 2 * j + 1) (k := 0) (c := 2 * j + 1) (b' := 2)
      (k' := 2 * j + 1 + 1) (c' := 1) (by omega) (by omega) (by omega))
      (CollatzStepsTo.of_eq rfl)

private theorem mid_none (b c : ℕ) (hb : b = 2 * (c / 2) + 4) :
    CollatzStepsTo midNext (.A b 0 c) none := by
  by_cases hc : c < 2
  · obtain rfl : b = 4 := by omega
    rcases c with _ | _ | c
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
    · omega
  obtain ⟨i, r, hr, rfl⟩ : ∃ i r, r < 2 ∧ c = 2 * i + r + 2 :=
    ⟨c / 2 - 1, c % 2, by omega, by omega⟩
  obtain rfl : b = 2 * i + 3 + 3 := by omega
  rcases r with _ | _ | r
  · exact CollatzStepsTo.head (mid_drain (b := 2 * i + 3) (k := 0) (c := 2 * i + 0) (b' := 4)
      (k' := 2 * i + 1 + 1) (c' := 0) (by omega) (by omega) (by omega))
      (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
  · exact CollatzStepsTo.head (mid_drain (b := 2 * i + 3) (k := 0) (c := 2 * i + 1) (b' := 4)
      (k' := 2 * i + 2) (c' := 1) (by omega) (by omega) (by omega)) (CollatzStepsTo.of_eq rfl)
  · omega

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_mid_acceleration.of_collatz (embed := toMid)
    (CollatzReachesStar.refl midNext _) ?_
  rintro ⟨b, c⟩
  dsimp only [highLevelNext]
  split_ifs
  · obtain rfl : b = 0 := by omega
    exact mid_b0_all c _ rfl
  · obtain rfl : b = 2 := by omega
    obtain rfl : c = 0 := by omega
    exact CollatzStepsTo.of_eq rfl
  · obtain rfl : b = 2 := by omega
    obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rcases c with _ | c
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq rfl
  · exact mid_big b c _ _ (by omega) rfl rfl
  · exact mid_odd b c _ (by omega) (by omega) rfl
  · exact mid_even_le b c _ _ (by omega) (by omega) (by omega) rfl rfl
  · exact mid_even_eq b c _ (by omega) (by omega) rfl
  · exact mid_none b c (by omega)

/-- `target` halts from the blank tape if and only if the high-level acceleration `highLevelNext`
halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` if and only if the high-level acceleration
`highLevelNext` halts from `highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB0LF_1LC0LD_1RD1LB_HHH1RE_0RA1RE_1LA0LE
