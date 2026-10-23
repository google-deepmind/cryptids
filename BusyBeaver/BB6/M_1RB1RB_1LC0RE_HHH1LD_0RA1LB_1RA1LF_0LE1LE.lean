/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`

We define the configuration for $k \ge 1$, $m \ge 1$, $f \ge 1$:

$$
C(2k, 2m, f) := 0^\infty \ (11)^k \ 0 \ (11)^m \ 0 \ \mathrm{D}{>} \ 1 \ 1^f \ 0^\infty.
$$

At the start of every macro step the last counter is $2$ or $5$, so for $a, b \ge 0$ and
$p \in \lbrace 0, 1 \rbrace$ we set

$$
D_p(a, b) := C(2a+2, 2b+2, 2+3p).
$$

Starting from $D_0(2, 0) = C(6, 2, 2)$ (reached after 76 steps from the blank tape), the machine
follows the map $T$:

$$
T(D_p(a, b)) = \begin{cases}
  D_p(a-b-2, 3b+p+4) & \text{if } a \ge b+2, \\
  D_0(3b+5, 0) & \text{if } a = b+1,\ p = 1, \\
  D_1(3b+2, 2) & \text{if } a = b+1,\ p = 0, \\
  \text{Halt} & \text{if } a \le b \le a+1, \\
  D_1(3a+5, 2) & \text{if } b = a+2,\ p = 1, \\
  D_0(3a+5, 0) & \text{if } b = a+2,\ p = 0, \\
  D_{1-p}(b-a-3, 3a+2p+5) & \text{if } b \ge a+3.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem split_11_pow_add_two (m : ℕ) (s : ListBlank (Fin 2)) :
    ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 2)) s =
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) (ListBlank.append [1] s)) := by
  rw [Nat.add_comm m 2, ListBlank.append_pow_add, swap_1_11_pow]
  rfl

/-- Leftward shift across `(11)^k` in state `E`, preserving `(11)^k`. -/
private theorem shift_E_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headLeft E
            (ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
            r)
          (Cfg.headLeft E
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l)
            (ListBlank.append [1, 1] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] r) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-- Rightward shift across `(11)^k` in state `E` with `[0, 1, 1, 0]` behind the head. -/
private theorem shift_E_0110 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight E
            (ListBlank.append [0, 1, 1, 0] l)
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight E
            (ListBlank.append [0, 1, 1, 0] (ListBlank.append [1, 1] l))
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Rightward shift across `(11)^k` in state `B` with `[1, 1, 0]` behind the head. -/
private theorem shift_B_110 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight B
        (ListBlank.append [1, 1, 0] l)
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight B
        (ListBlank.append [1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l))
        r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight B
            (ListBlank.append [1, 1, 0] l)
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight B
            (ListBlank.append [1, 1, 0] (ListBlank.append [1, 1] l))
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Canonical tape pattern
$A(k, m, f) := 0^\infty\,(11)^k\,0\,(11)^m\,0\,\mathrm{D}{>}\,1\,1^f\,0^\infty$. -/
private abbrev pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

/-- Guard condition $k \ge 1 \land m \ge 1 \land f \ge 1$. -/
private abbrev cond_A : VarCond :=
  .and (.ge_const 0 1) (.and (.ge_const 1 1) (.ge_const 2 1))

/-- Closed pattern set for `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [({ left := .sym 0 (.rep [1, 1] 1 (.sym 0 (.rep [1, 1] 0 .default)))
      head := some SixState.D
      right := .sym 1 (.rep [1] 2 .default) },
    .and (.ge_const 0 1) (.and (.ge_const 1 1) (.ge_const 2 1)))]

/-- Configuration $A(k, m, f)$. -/
private def cfg_A (k m f : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D
    (ListBlank.append [0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default))))
    (ListBlank.append [1]
      (ListBlank.append (([1] : List (Fin 2)) ^ f) default))

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) (vars 2) :=
  rfl

private theorem in_ps_A (k m f : ℕ) (hk : k ≥ 1) (hm : m ≥ 1) (hf : f ≥ 1) :
    IsInPatternSet ps (cfg_A k m f) :=
  ⟨(pat_A, cond_A), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => m | 2 => f | _ => 0, rfl, ⟨hk, hm, hf⟩⟩

private theorem cfg_A_zero (m f : ℕ) :
    cfg_A 0 m f =
      Cfg.headRight D
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ m) default))
        (ListBlank.append [1]
          (ListBlank.append (([1] : List (Fin 2)) ^ f) default)) := by
  unfold cfg_A
  simp

/-! ## Accelerated Transitions from $A(k, m, f)$ -/

/-- Main contraction step: $A(k + 1, m + 2, f) \to^+ A(k, m + 1, f + 6)$. -/
private theorem step_macro (k m f : ℕ) :
    ReachesPlus target (cfg_A (k + 1) (m + 2) f) (cfg_A k (m + 1) (f + 6)) := by
  unfold cfg_A
  set l_k := ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default
  set r_f := ListBlank.append (([1] : List (Fin 2)) ^ f) default
  rw [split_11_pow_add_two m (ListBlank.append [0] l_k)]
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0]
            (ListBlank.append [1, 1, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
                (ListBlank.append [1] (ListBlank.append [0] l_k)))))
          (ListBlank.append [1] r_f))
        (Cfg.headLeft E
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ m)
            (ListBlank.append [1, 0] l_k))
          (ListBlank.append [0, 1, 1, 1, 1] r_f)) := by
    bb_steps
  have h2 := shift_E_11 m (ListBlank.append [1, 0] l_k) (ListBlank.append [0, 1, 1, 1, 1] r_f)
  have h12 := h1.trans_star h2
  set r_m :=
    ListBlank.append (([1, 1] : List (Fin 2)) ^ m) (ListBlank.append [0, 1, 1, 1, 1] r_f)
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E (ListBlank.append [1, 0] l_k) r_m)
        (Cfg.headLeft E l_k (ListBlank.append [0, 1] r_m)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_E_11 (k + 1) default (ListBlank.append [0, 1] r_m)
  have h1234 := h123.trans_star h4
  rw [ListBlank.append_pow_succ] at h1234
  set r_k :=
    ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r_m)
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E default (ListBlank.append [1, 1] r_k))
        (Cfg.headRight E (ListBlank.append [0, 1, 1, 0] default) r_k) := by
    bb_steps
  have h12345 := h1234.trans h5
  have h6 := shift_E_0110 k default (ListBlank.append [0, 1] r_m)
  have h123456 := h12345.trans_star h6
  set l_k' := ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default)
  have h7 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) default))
          (ListBlank.append [0, 1] r_m))
        (Cfg.headRight B
          (ListBlank.append [1, 1, 0] (ListBlank.append [1, 1] l_k'))
          r_m) := by
    bb_steps
  have h1234567 := h123456.trans h7
  have h8 := shift_B_110 m (ListBlank.append [1, 1] l_k') (ListBlank.append [0, 1, 1, 1, 1] r_f)
  have h12345678 := h1234567.trans_star h8
  have h_pow_m :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ m) (ListBlank.append [1, 1] l_k') =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1)) l_k' := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_pow_m] at h12345678
  have h9 :
      ReachesPlus target
        (Cfg.headRight B
          (ListBlank.append [1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1)) l_k'))
          (ListBlank.append [0, 1, 1, 1, 1] r_f))
        (Cfg.headRight D
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1)) l_k'))
          (ListBlank.append [1]
            (ListBlank.append (([1] : List (Fin 2)) ^ (f + 6)) default))) := by
    have h_f :
        ListBlank.append (([1] : List (Fin 2)) ^ (f + 6)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 1, 1, 1, 1, 1] r_f := by
      rw [Nat.add_comm f 6, ListBlank.append_pow_add]
      rfl
    rw [h_f]
    bb_steps
  exact h12345678.trans h9

/-- Boundary step when $m = 1$: $A(k + 1, 1, f) \to^+ A(0, k + 1, f + 3)$. -/
private theorem step_m1 (k f : ℕ) :
    ReachesPlus target (cfg_A (k + 1) 1 f) (cfg_A 0 (k + 1) (f + 3)) := by
  rw [cfg_A_zero]
  unfold cfg_A
  have h_m1 : (([1, 1] : List (Fin 2)) ^ 1) = [1, 1] := rfl
  have h_f :
      ListBlank.append (([1] : List (Fin 2)) ^ (f + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1] : List (Fin 2)) ^ f) default) := by
    rw [Nat.add_comm f 3, ListBlank.append_pow_add]
    rfl
  rw [h_m1, h_f]
  bb_steps

/-- Halting transition from $A(0, 1, d + 1)$. -/
private theorem step_zero_one (d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A 0 1 (d + 1)) cfg' ∧ (step target cfg').isNone := by
  rw [cfg_A_zero]
  have h_m1 : (([1, 1] : List (Fin 2)) ^ 1) = [1, 1] := rfl
  have h_d :
      ListBlank.append (([1] : List (Fin 2)) ^ (d + 1)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1] (ListBlank.append (([1] : List (Fin 2)) ^ d) default) := by
    rw [Nat.add_comm d 1, ListBlank.append_pow_add]
    rfl
  rw [h_m1, h_d]
  set r_d := ListBlank.append (([1] : List (Fin 2)) ^ d) default
  refine ⟨Cfg.headLeft C default (ListBlank.append [1, 1, 1, 1, 1, 1] r_d), ?_, ?_⟩
  · bb_steps
  · bb_halt

/-- Shared 15-step opening for $A(0, 2, f)$. -/
private theorem sweep_zero_two (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 2) default))
        (ListBlank.append [1] r))
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0] (ListBlank.append [1, 1] default))
        (ListBlank.append [1, 1] r)) := by
  have h2 : (([1, 1] : List (Fin 2)) ^ 2) = [1, 1, 1, 1] := rfl
  rw [h2]
  bb_steps

/-- Shared sweep across $0^\infty\,(11)^{v+3}\,0\,\mathrm{D}{>}\,1\,r$. -/
private theorem sweep_D_zero (v : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 3)) default))
        (ListBlank.append [1] r))
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1)) default))
        (ListBlank.append [0, 1, 1, 1, 1] r)) := by
  have h_split :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 3)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 1, 1]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1))
            (ListBlank.append [1] default)) :=
    split_11_pow_add_two (v + 1) default
  rw [h_split]
  set l_v :=
    ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1)) (ListBlank.append [1] default)
  have h1 :
      ReachesPlus target
        (Cfg.headRight D
          (ListBlank.append [0] (ListBlank.append [1, 1, 1] l_v))
          (ListBlank.append [1] r))
        (Cfg.headLeft E l_v (ListBlank.append [0, 1, 1, 1, 1] r)) := by
    bb_steps
  have h2 := shift_E_11 (v + 1) (ListBlank.append [1] default) (ListBlank.append [0, 1, 1, 1, 1] r)
  have h12 := h1.trans_star h2
  set r_v :=
    ListBlank.append (([1, 1] : List (Fin 2)) ^ (v + 1)) (ListBlank.append [0, 1, 1, 1, 1] r)
  have h3 :
      ReachesPlus target
        (Cfg.headLeft E (ListBlank.append [1] default) r_v)
        (Cfg.headRight E (ListBlank.append [0, 1, 1, 0] default) r_v) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_E_0110 (v + 1) default (ListBlank.append [0, 1, 1, 1, 1] r)
  exact h123.trans_star h4

/-- Shared rightward completion across `0\,(11)^{u+1}\,r_{\mathrm{rem}}`. -/
private theorem shift_0110_block (a u : ℕ) (r_rem : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1)) r_rem)))
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1))
            (ListBlank.append [0]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))
        r_rem) := by
  set l_a := ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default
  rw [ListBlank.append_pow_succ (([1, 1] : List (Fin 2))) u r_rem]
  set r_u := ListBlank.append (([1, 1] : List (Fin 2)) ^ u) r_rem
  have h1 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0] l_a)
          (ListBlank.append [0] (ListBlank.append [1, 1] r_u)))
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0] (ListBlank.append [1, 1, 0] l_a))
          r_u) := by
    bb_steps
  have h2 := shift_E_0110 u (ListBlank.append [1, 1, 0] l_a) r_rem
  have h12 := h1.trans_star h2
  have h_pow :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ u) (ListBlank.append [1, 1, 0] l_a) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1)) (ListBlank.append [0] l_a) := by
    change ListBlank.append (([1, 1] : List (Fin 2)) ^ u)
      (ListBlank.append [1, 1] (ListBlank.append [0] l_a)) = _
    rw [ListBlank.append_append, ← list_pow_succ']
  rwa [h_pow] at h12

private theorem finish_0110_even (a u : ℕ) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1)) default)))
      (cfg_A a (u + 1) 5) := by
  have h1 := shift_0110_block a u default
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1))
              (ListBlank.append [0]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))))
          default)
        (cfg_A a (u + 1) 5) := by
    unfold cfg_A
    have h5 : (([1] : List (Fin 2)) ^ 5) = [1, 1, 1, 1, 1] := rfl
    rw [h5]
    bb_steps
  exact h1.trans h2

private theorem finish_0110_odd (a u : ℕ) :
    ReachesPlus target
      (Cfg.headRight E
        (ListBlank.append [0, 1, 1, 0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default))
        (ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1))
            (ListBlank.append [1] default))))
      (cfg_A a (u + 2) 2) := by
  have h1 := shift_0110_block a u (ListBlank.append [1] default)
  set l_a := ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) default)
  have h2 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1)) l_a))
          (ListBlank.append [1] default))
        (cfg_A a (u + 2) 2) := by
    unfold cfg_A
    have h2_pow : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    have h_u2 :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 2)) l_a =
          ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (u + 1)) l_a) := by
      rw [← ListBlank.append_pow_succ]
    rw [h2_pow, h_u2]
    bb_steps
  exact h1.trans h2

/-- Even-exponent transition from $A(0, 2, 2j + 4)$. -/
private theorem step_zero_two_even (j : ℕ) :
    ReachesPlus target (cfg_A 0 2 (2 * j + 4)) (cfg_A (j + 4) 1 2) := by
  rw [cfg_A_zero]
  have h1 := sweep_zero_two (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) default)
  have h_r :
      ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 3)) default := by
    have h_eq : 2 * (j + 3) = 2 + (2 * j + 4) := by omega
    rw [one_pow_two_mul, h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 (2 * j + 4)]
    rfl
  rw [h_r] at h1
  have h2 := shift_E_0110 (j + 3) (ListBlank.append [1, 1] default) default
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 3))
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4)) default := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4)) default))
          default)
        (cfg_A (j + 4) 1 2) := by
    unfold cfg_A
    have h_m1 : (([1, 1] : List (Fin 2)) ^ 1) = [1, 1] := rfl
    have h_f2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_m1, h_f2]
    bb_steps
  exact h12.trans h3

/-- Odd-exponent transition from $A(0, 2, 2j + 5)$. -/
private theorem step_zero_two_odd (j : ℕ) :
    ReachesPlus target (cfg_A 0 2 (2 * j + 5)) (cfg_A (j + 3) 3 5) := by
  rw [cfg_A_zero]
  have h1 := sweep_zero_two (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 5)) default)
  have h_r :
      ListBlank.append [1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 5)) (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 3)) (ListBlank.append [1] default) := by
    have h_eq : 2 * j + 5 = 2 * (j + 2) + 1 := by omega
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 2)) 1,
      ← one_pow_two_mul, list_pow_one, ← ListBlank.append_pow_succ]
  rw [h_r] at h1
  have h2 := shift_E_0110 (j + 3) (ListBlank.append [1, 1] default) (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h_l :
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 3))
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4)) default := by
    rw [ListBlank.append_append, ← list_pow_succ']
  rw [h_l] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight E
          (ListBlank.append [0, 1, 1, 0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4)) default))
          (ListBlank.append [1] default))
        (Cfg.headRight D
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 5)) default))
          (ListBlank.append [1] (ListBlank.append [1, 1] default))) := by
    rw [ListBlank.append_pow_succ (([1, 1] : List (Fin 2))) (j + 4)]
    bb_steps
  have h123 := h12.trans h3
  have h4 := sweep_D_zero (j + 2) (ListBlank.append [1, 1] default)
  have h1234 := h123.trans h4
  have h_r2 :
      ListBlank.append [0, 1, 1, 1, 1] (ListBlank.append [1, 1] (default : ListBlank (Fin 2))) =
        ListBlank.append [0] (ListBlank.append (([1, 1] : List (Fin 2)) ^ 3) default) := rfl
  rw [h_r2] at h1234
  exact h1234.trans (finish_0110_even (j + 3) 2)

/-- Even-exponent transition from $A(0, v + 3, 2j + 4)$. -/
private theorem step_zero_ge3_even (v j : ℕ) :
    ReachesPlus target (cfg_A 0 (v + 3) (2 * j + 4)) (cfg_A (v + 1) (j + 4) 5) := by
  rw [cfg_A_zero]
  have h1 := sweep_D_zero v (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) default)
  have h_r :
      ListBlank.append [0, 1, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4)) default) := by
    have h_eq : 2 * (j + 4) = 4 + (2 * j + 4) := by omega
    change ListBlank.append [0]
      (ListBlank.append [1, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 4)) default)) = _
    rw [one_pow_two_mul, h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) 4 (2 * j + 4)]
    rfl
  rw [h_r] at h1
  exact h1.trans (finish_0110_even (v + 1) (j + 3))

/-- Odd-exponent transition from $A(0, v + 3, 2j + 5)$. -/
private theorem step_zero_ge3_odd (v j : ℕ) :
    ReachesPlus target (cfg_A 0 (v + 3) (2 * j + 5)) (cfg_A (v + 1) (j + 5) 2) := by
  rw [cfg_A_zero]
  have h1 := sweep_D_zero v (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 5)) default)
  have h_r :
      ListBlank.append [0, 1, 1, 1, 1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 5)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0]
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ (j + 4))
            (ListBlank.append [1] default)) := by
    have h_eq : 2 * j + 5 = 2 * (j + 2) + 1 := by omega
    have h_eq2 : (j + 2) + 2 = j + 4 := by omega
    change ListBlank.append [0]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * j + 5)) default)) = _
    rw [h_eq, ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 2)) 1,
      ← one_pow_two_mul, list_pow_one, ← ListBlank.append_pow_add,
      Nat.add_comm 2 (j + 2), h_eq2]
  rw [h_r] at h1
  exact h1.trans (finish_0110_odd (v + 1) (j + 3))

/-! ## Closedness and `HasCollatzReduction` -/

private theorem step_zero_closed (w d : ℕ) :
    StepsToClosed target ps (cfg_A 0 (w + 1) (d + 4)) := by
  rcases w with _ | _ | v
  · obtain ⟨cfg', h_step, h_halt⟩ := step_zero_one (d + 3)
    exact ⟨cfg', h_step, Or.inr h_halt⟩
  · rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨cfg_A (j + 4) 1 2, step_zero_two_even j,
        Or.inl (in_ps_A (j + 4) 1 2 (by omega) (by decide) (by decide))⟩
    · have h_eq : 2 * j + 1 + 4 = 2 * j + 5 := by omega
      rw [h_eq]
      exact ⟨cfg_A (j + 3) 3 5, step_zero_two_odd j,
        Or.inl (in_ps_A (j + 3) 3 5 (by omega) (by decide) (by decide))⟩
  · rcases nat_even_or_odd_two_mul d with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact ⟨cfg_A (v + 1) (j + 4) 5, step_zero_ge3_even v j,
        Or.inl (in_ps_A (v + 1) (j + 4) 5 (by omega) (by omega) (by decide))⟩
    · have h_eq : 2 * j + 1 + 4 = 2 * j + 5 := by omega
      rw [h_eq]
      exact ⟨cfg_A (v + 1) (j + 5) 2, step_zero_ge3_odd v j,
        Or.inl (in_ps_A (v + 1) (j + 5) 2 (by omega) (by omega) (by decide))⟩

private theorem step_A_closed (k m f : ℕ) (hk : k ≥ 1) (hm : m ≥ 1) (hf : f ≥ 1) :
    StepsToClosed target ps (cfg_A k m f) := by
  rcases k with _ | k'
  · omega
  · rcases m with _ | _ | m'
    · omega
    · rcases f with _ | d
      · omega
      · exact StepsToClosed.of_reachesPlus (step_m1 k' (d + 1)) (step_zero_closed k' d)
    · rcases k' with _ | k''
      · rcases f with _ | d
        · omega
        · have h_step := step_macro 0 m' (d + 1)
          have h_eq : d + 1 + 6 = (d + 3) + 4 := by omega
          rw [h_eq] at h_step
          exact StepsToClosed.of_reachesPlus h_step (step_zero_closed m' (d + 3))
      · exact ⟨cfg_A (k'' + 1) (m' + 1) (f + 6), step_macro (k'' + 1) m' f,
          Or.inl (in_ps_A (k'' + 1) (m' + 1) (f + 6) (by omega) (by omega) (by omega))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 3 1 2) := by
  have h_init : ReachesPlus target (init []) (cfg_A 3 1 2) := by
    unfold cfg_A
    have hk3 : (([1, 1] : List (Fin 2)) ^ 3) = [1, 1, 1, 1, 1, 1] := rfl
    have hm1 : (([1, 1] : List (Fin 2)) ^ 1) = [1, 1] := rfl
    have hf2 : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [hk3, hm1, hf2]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 3 1 2, init_reaches_start, in_ps_A 3 1 2 (by decide) (by decide) (by decide)⟩,
    ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  subst h_mem
  exact step_A_closed (vars 0) (vars 1) (vars 2) h_cond.1 h_cond.2.1 h_cond.2.2

/-- `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

private theorem step_macro_iter (n : ℕ) : ∀ k m f,
    ReachesPlus target (cfg_A (k + n + 2) (m + n + 2) f)
      (cfg_A (k + 1) (m + 1) (f + 6 * (n + 1))) := by
  induction n with
  | zero =>
    intro k m f
    simpa using step_macro (k + 1) m f
  | succ n ih =>
    intro k m f
    have hk : k + (n + 1) + 2 = (k + n + 2) + 1 := by omega
    have hm : m + (n + 1) + 2 = (m + n + 1) + 2 := by omega
    rw [hk, hm]
    have h2 := (step_macro (k + n + 2) (m + n + 1) f).trans (ih k m (f + 6))
    have h_f : f + 6 + 6 * (n + 1) = f + 6 * (n + 1 + 1) := by omega
    rwa [h_f] at h2

/-- Symbolic configuration state space for `1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`. -/
inductive State where
  /-- $C(2(k+1), 2(m+1), f+1) :=
    0^\infty\,1^{2(k+1)}\,0\,1^{2(m+1)}\,0\,\mathrm{D}{>}\,1\,1^{f+1}\,0^\infty$. -/
  | C (k m f : ℕ)

/-- Initial symbolic state $C(6, 2, 2)$, reached after 76 raw TM steps. -/
def start : State := .C 2 0 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C k m f =>
    Cfg.headRight SixState.D
      (ListBlank.append [0]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ (m + 1))
          (ListBlank.append [0]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) default))))
      (ListBlank.append [1]
        (ListBlank.append (([1] : List (Fin 2)) ^ (f + 1)) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C 0 0 _ => none
  | .C 0 1 _ => none
  | .C 0 2 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 2 4)
    else some (.C (f / 2 + 5) 0 1)
  | .C 0 (m + 3) f =>
    if f % 2 = 0 then some (.C m (f / 2 + 5) 1)
    else some (.C m (f / 2 + 5) 4)
  | .C 1 0 f =>
    if f % 2 = 0 then some (.C (f / 2 + 3) 0 1)
    else some (.C (f / 2 + 2) 2 4)
  | .C (k + 2) 0 f =>
    if f % 2 = 0 then some (.C k (f / 2 + 3) 4)
    else some (.C k (f / 2 + 4) 1)
  | .C (k + 1) (m + 1) f =>
    if k < m then some (.C 0 (m - k) (f + 6 * (k + 1)))
    else if m < k then some (.C (k - m) 0 (f + 6 * (m + 1)))
    else some (.C 0 0 (f + 6 * (k + 1)))

private theorem encode_C (k m f : ℕ) : encode (.C k m f) = cfg_A (k + 1) (m + 1) (f + 1) := rfl

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨k, m, f⟩ s' hnext
    rcases k with _ | _ | k
    · rcases m with _ | _ | _ | v
      · simp [next] at hnext
      · simp [next] at hnext
      · rcases nat_even_or_odd_two_mul f with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · have hmod : (2 * j) % 2 = 0 := by omega
          have hdiv : (2 * j) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_macro 0 1 (2 * j + 1)
          have h_eq : 2 * j + 1 + 6 = 2 * (j + 1) + 5 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_two_odd (j + 1))
        · have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * j + 1) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_macro 0 1 (2 * j + 1 + 1)
          have h_eq : 2 * j + 1 + 1 + 6 = 2 * (j + 2) + 4 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_two_even (j + 2))
      · rcases nat_even_or_odd_two_mul f with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · have hmod : (2 * j) % 2 = 0 := by omega
          have hdiv : (2 * j) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_macro 0 (v + 2) (2 * j + 1)
          have h_eq : 2 * j + 1 + 6 = 2 * (j + 1) + 5 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_ge3_odd v (j + 1))
        · have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * j + 1) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_macro 0 (v + 2) (2 * j + 1 + 1)
          have h_eq : 2 * j + 1 + 1 + 6 = 2 * (j + 2) + 4 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_ge3_even v (j + 2))
    · rcases m with _ | m
      · rcases nat_even_or_odd_two_mul f with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · have hmod : (2 * j) % 2 = 0 := by omega
          have hdiv : (2 * j) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_m1 1 (2 * j + 1)
          have h_eq : 2 * j + 1 + 3 = 2 * j + 4 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_two_even j)
        · have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * j + 1) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_m1 1 (2 * j + 1 + 1)
          have h_eq : 2 * j + 1 + 1 + 3 = 2 * j + 5 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_two_odd j)
      · rcases m with _ | m'
        · simp only [next, lt_self_iff_false, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_C]
          have h := step_macro 1 0 (f + 1)
          have h_f : f + 1 + 6 = f + 6 + 1 := by omega
          rwa [h_f] at h
        · have hlt : 0 < m' + 1 := by omega
          have hsub : m' + 1 - 0 = m' + 1 := by omega
          simp only [next, hlt, ↓reduceIte, hsub, Option.some.injEq] at hnext
          subst hnext
          rw [encode_C, encode_C]
          have h := step_macro 1 (m' + 1) (f + 1)
          have h_f : f + 1 + 6 = f + 6 + 1 := by omega
          rwa [h_f] at h
    · rcases m with _ | m
      · rcases nat_even_or_odd_two_mul f with ⟨j, rfl⟩ | ⟨j, rfl⟩
        · have hmod : (2 * j) % 2 = 0 := by omega
          have hdiv : (2 * j) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_m1 (k + 2) (2 * j + 1)
          have h_eq : 2 * j + 1 + 3 = 2 * j + 4 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_ge3_even k j)
        · have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
          have hdiv : (2 * j + 1) / 2 = j := by omega
          simp only [next, hmod, ↓reduceIte, hdiv, Option.some.injEq] at hnext
          subst hnext
          have h1 := step_m1 (k + 2) (2 * j + 1 + 1)
          have h_eq : 2 * j + 1 + 1 + 3 = 2 * j + 5 := by omega
          rw [h_eq] at h1
          exact h1.trans (step_zero_ge3_odd k j)
      · by_cases hlt1 : k + 1 < m
        · simp only [next, hlt1, ↓reduceIte, Option.some.injEq] at hnext
          subst hnext
          have h_iter := step_macro_iter (k + 1) 0 (m - (k + 1)) (f + 1)
          have h_k : 0 + (k + 1) + 2 = k + 1 + 1 + 1 := by omega
          have h_m : m - (k + 1) + (k + 1) + 2 = m + 1 + 1 := by omega
          have h_f : f + 1 + 6 * (k + 1 + 1) = f + 6 * (k + 1 + 1) + 1 := by omega
          rw [h_k, h_m, h_f] at h_iter
          exact h_iter
        · by_cases hlt2 : m < k + 1
          · simp only [next, hlt1, ↓reduceIte, hlt2, Option.some.injEq] at hnext
            subst hnext
            have h_iter := step_macro_iter m (k + 1 - m) 0 (f + 1)
            have h_k : k + 1 - m + m + 2 = k + 1 + 1 + 1 := by omega
            have h_m : 0 + m + 2 = m + 1 + 1 := by omega
            have h_f : f + 1 + 6 * (m + 1) = f + 6 * (m + 1) + 1 := by omega
            rw [h_k, h_m, h_f] at h_iter
            exact h_iter
          · have heq : m = k + 1 := by omega
            subst heq
            simp only [next, hlt1, ↓reduceIte, Option.some.injEq] at hnext
            subst hnext
            have h_iter := step_macro_iter (k + 1) 0 0 (f + 1)
            have h_k : 0 + (k + 1) + 2 = k + 1 + 1 + 1 := by omega
            have h_f : f + 1 + 6 * (k + 1 + 1) = f + 6 * (k + 1 + 1) + 1 := by omega
            rw [h_k, h_f] at h_iter
            exact h_iter
  step_none := by
    rintro ⟨k, m, f⟩ hnext
    rcases k with _ | _ | k
    · rcases m with _ | _ | _ | v
      · have h1 := step_m1 0 (f + 1)
        have h_eq : f + 1 + 3 = (f + 3) + 1 := by omega
        rw [h_eq] at h1
        obtain ⟨cfg', h2, hh⟩ := step_zero_one (f + 3)
        exact ⟨cfg', (h1.trans h2).to_star, hh⟩
      · have h1 := step_macro 0 0 (f + 1)
        have h_eq : f + 1 + 6 = (f + 6) + 1 := by omega
        rw [h_eq] at h1
        obtain ⟨cfg', h2, hh⟩ := step_zero_one (f + 6)
        exact ⟨cfg', (h1.trans h2).to_star, hh⟩
      · simp only [next] at hnext
        split_ifs at hnext
      · simp only [next] at hnext
        split_ifs at hnext
    · rcases m with _ | m <;> (simp only [next] at hnext; split_ifs at hnext)
    · rcases m with _ | m <;> (simp only [next] at hnext; split_ifs at hnext)

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

/-- High-level symbolic configuration state space for
`1RB1RB_1LC0RE_---1LD_0RA1LB_1RA1LF_0LE1LE`: at every high-level step the last counter of
`State.C` is $1$ or $4$, so it is replaced by a flag. -/
inductive HighLevelState where
  /-- $D_p(a, b) := C(2(a+1), 2(b+1), 2 + 3p)$, i.e. `.C a b (if p then 4 else 1)`. -/
  | C (a b : ℕ) (p : Bool)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $D_0(2, 0)$, encoding $C(6, 2, 2)$. -/
def highLevelStart : HighLevelState := .C 2 0 false

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .C a b p => .C a b (if p then 4 else 1)

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- High-level accelerated transition function on $D_p(a, b)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .C a b p =>
    let r := if p then 1 else 0
    if a ≥ b + 2 then some (.C (a - b - 2) (3 * b + r + 4) p)
    else if a = b + 1 then
      if p then some (.C (3 * b + 5) 0 false) else some (.C (3 * b + 2) 2 true)
    else if b ≤ a + 1 then none
    else if b = a + 2 then
      if p then some (.C (3 * a + 5) 2 true) else some (.C (3 * a + 5) 0 false)
    else some (.C (b - a - 3) (3 * a + 2 * r + 5) (!p))

private theorem next_C_succ_succ (a b f : ℕ) :
    next (.C (a + 1) (b + 1) f) =
      if a < b then some (.C 0 (b - a) (f + 6 * (a + 1)))
      else if b < a then some (.C (a - b) 0 (f + 6 * (b + 1)))
      else some (.C 0 0 (f + 6 * (a + 1))) := by
  simp [next]

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_acceleration.of_collatz (embed := toState) (CollatzReachesStar.refl next _) ?_
  rintro ⟨a, b, p⟩
  rcases a with _ | a
  · rcases b with _ | _ | _ | b
    · cases p <;> exact CollatzStepsTo.of_eq rfl
    · cases p <;> exact CollatzStepsTo.of_eq rfl
    · cases p <;> exact CollatzStepsTo.of_eq rfl
    · cases p <;> exact CollatzStepsTo.of_eq (by simp [toState, highLevelNext, next])
  · rcases b with _ | b
    · rcases a with _ | a
      · cases p <;> exact CollatzStepsTo.of_eq rfl
      · cases p <;> exact CollatzStepsTo.of_eq (by simp [toState, highLevelNext, next])
    · rcases lt_trichotomy a b with h | rfl | h
      · obtain ⟨t, rfl⟩ : ∃ t, b = a + 1 + t := ⟨b - a - 1, by omega⟩
        have h1 : next (toState (.C (a + 1) (a + 1 + t + 1) p)) =
            some (.C 0 (t + 1) ((if p then 4 else 1) + 6 * (a + 1))) := by
          simp only [toState, next_C_succ_succ]
          split_ifs <;> simp only [Option.some.injEq, State.C.injEq, true_and, and_true] <;> omega
        refine CollatzStepsTo.head h1 (CollatzStepsTo.of_eq ?_)
        rcases t with _ | _ | t <;> cases p
        all_goals
          simp only [next, highLevelNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Bool.not_true]
          split_ifs <;>
            (try simp only [Option.map_some, Option.map_none, toState, Option.some.injEq,
              State.C.injEq, ↓reduceIte, Bool.false_eq_true, and_true, reduceCtorEq]) <;>
            omega
      · have h1 : next (toState (.C (a + 1) (a + 1) p)) =
            some (.C 0 0 ((if p then 4 else 1) + 6 * (a + 1))) := by
          simp [toState, next_C_succ_succ]
        refine CollatzStepsTo.head h1 (CollatzStepsTo.of_eq ?_)
        cases p
        all_goals
          simp only [next, highLevelNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Bool.not_true]
          split_ifs <;> (try simp only [Option.map_some, Option.map_none, toState,
            ↓reduceIte, Bool.false_eq_true, reduceCtorEq]) <;> omega
      · obtain ⟨t, rfl⟩ : ∃ t, a = b + 1 + t := ⟨a - b - 1, by omega⟩
        have h1 : next (toState (.C (b + 1 + t + 1) (b + 1) p)) =
            some (.C (t + 1) 0 ((if p then 4 else 1) + 6 * (b + 1))) := by
          simp only [toState, next_C_succ_succ]
          split_ifs <;> simp only [Option.some.injEq, State.C.injEq, and_true] <;> omega
        refine CollatzStepsTo.head h1 (CollatzStepsTo.of_eq ?_)
        rcases t with _ | t <;> cases p
        all_goals
          simp only [next, highLevelNext, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
            Bool.not_true]
          split_ifs <;>
            (try simp only [Option.map_some, Option.map_none, toState, Option.some.injEq,
              State.C.injEq, ↓reduceIte, Bool.false_eq_true, and_true, reduceCtorEq]) <;>
            omega

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

end BusyBeaver.M_1RB1RB_1LC0RE_HHH1LD_0RA1LB_1RA1LF_0LE1LE
