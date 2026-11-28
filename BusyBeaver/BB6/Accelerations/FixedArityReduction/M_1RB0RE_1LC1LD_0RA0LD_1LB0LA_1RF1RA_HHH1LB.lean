/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`
(see <https://wiki.bbchallenge.org/wiki/1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB>)
(`cryptid_13`, holdout #243, `suspect_84`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$A(n, m) := 0^\infty\,(01)^{3n+2}\,\mathrm{A}{>}\,(01)^m\,0^\infty$$
at $A(0, 0)$ in 22 steps, and every $A(n, m)$ advances in `ReachesPlus` either to another
$A(n', m')$ or to a halting configuration (when $n = 2k$ and $m = 1$).

## Collatz-like Acceleration Rules

```text
Consider:
A(n, m) = 0^inf (01)^(3n+2) A> (01)^m 0^inf

A(n, 0)      -> A(0, 3n+2)
A(2k, 1)     -> Halt
A(2k, m+2)   -> A(3k+1, m)
A(2k+1, m+1) -> A(3k+2, m)

Start: A(0, 0), reached after 22 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward A-E sweep across `1^(2k)`, depositing `(10)^k` on the left. -/
private theorem shift_AE (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A l (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r))
      (Cfg.headRight A (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h_split :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (k + 1))) r =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r) := by
      have h_add : 2 * (k + 1) = 2 + 2 * k := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_split]
    have h1 :
        ReachesPlus target
          (Cfg.headRight A l
            (ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)))
          (Cfg.headRight A (ListBlank.append [1, 0] l)
            (ListBlank.append (([1] : List (Fin 2)) ^ (2 * k)) r)) := by
      bb_steps
    have h2 := ih (ListBlank.append [1, 0] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] l) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward B-D sweep across `(10)^p` followed by the left-boundary turnaround into state `A`. -/
private theorem sweep_D_to_A (p q : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ p) default)
        (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ q) r)))
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * p + q + 2)) r)) := by
  induction p generalizing q with
  | zero =>
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * 0 + q + 2)) r =
          ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ q) r) := by
      have h_add : 2 * 0 + q + 2 = 2 + q := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [list_pow_zero, ListBlank.append_nil, h_r]
    bb_steps
  | succ p ih =>
    rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight D
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ p) default))
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ q) r)))
          (Cfg.headRight D
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ p) default)
            (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (q + 2)) r))) := by
      have h_q :
          ListBlank.append (([1] : List (Fin 2)) ^ (q + 2)) r =
            ListBlank.append [1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ q) r) := by
        have h_add : q + 2 = 2 + q := by omega
        rw [h_add, ListBlank.append_pow_add]
        rfl
      rw [h_q]
      bb_steps
    have h2 := ih (q + 2)
    have h3 := h1.trans h2
    have h_eq : 2 * p + (q + 2) + 2 = 2 * (p + 1) + q + 2 := by omega
    rwa [h_eq] at h3

/-- Leftward 4-step cycle consuming `(10)^k` on the left and depositing `(01)^k` on the right. -/
private theorem shift_A_left (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
        (ListBlank.append [0, 0] r))
      (Cfg.headRight A l
        (ListBlank.append [0, 0] (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))) := by
  induction k generalizing r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight A
            (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l))
            (ListBlank.append [0, 0] r))
          (Cfg.headRight A
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) l)
            (ListBlank.append [0, 0] (ListBlank.append [0, 1] r))) := by
      bb_steps
    have h2 := ih (ListBlank.append [0, 1] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([0, 1] : List (Fin 2)) ^ k) (ListBlank.append [0, 1] r) =
          ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-! ## Inner Loop Lemmas -/

/-- One iteration of the inner loop: decreases the leading `1`-block by 2 and increases the inner
`1`-block by 3. -/
private theorem inner_step (p m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (p + 2)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) r))))
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (p + 1)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r)))) := by
  have h1 := shift_AE (p + 2) default
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) r))
  have h2 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (p + 2)) default)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) r)))
        (Cfg.headRight D
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ p) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r))))) := by
    have h_l :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ (p + 2)) (default : ListBlank (Fin 2)) =
          ListBlank.append [1, 0, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ p) default) := by
      have h_add : p + 2 = 2 + p := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    have h_r :
        ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r =
          ListBlank.append [1, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ m) r) := by
      have h_add : m + 4 = 4 + m := by omega
      rw [h_add, ListBlank.append_pow_add]
      rfl
    rw [h_l, ListBlank.append_pow_succ ([1] : List (Fin 2)) m, list_pow_zero,
      ListBlank.append_nil, h_r]
    bb_steps
  have h12 := h1.trans_plus h2
  have h3 := sweep_D_to_A p 0
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r))
  have h123 := h12.trans h3
  have h_eq : 2 * p + 0 + 2 = 2 * (p + 1) := by omega
  rwa [h_eq] at h123

/-- `j` iterations of `inner_step`, reducing the leading `1`-block from `2 * (j + 1)` to `2` and
increasing the inner `1`-block from `m + 1` to `m + 3 * j + 1`. -/
private theorem inner_loop (j m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (j + 1)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) r))))
      (Cfg.headRight A default
        (ListBlank.append [1, 1]
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ (m + 3 * j + 1)) r)))) := by
  induction j generalizing m with
  | zero => exact ReachesStar.refl _ _
  | succ j ih =>
    have h1 := inner_step j m r
    have h_m1 : m + 4 = (m + 3) + 1 := by omega
    rw [h_m1] at h1
    have h2 := ih (m + 3)
    have h3 := (h1.trans_star h2).to_star
    have h_m2 : (m + 3) + 3 * j + 1 = m + 3 * (j + 1) + 1 := by omega
    rwa [h_m2] at h3

/-- Shared 12-step turnaround after `inner_loop` when the leading `1`-block has size `2`. -/
private theorem post_inner_turnaround (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default
        (ListBlank.append [1, 1]
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ (m + 1)) r))))
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r)) := by
  have h_r :
      ListBlank.append (([1] : List (Fin 2)) ^ (m + 4)) r =
        ListBlank.append [1, 1, 1, 1] (ListBlank.append (([1] : List (Fin 2)) ^ m) r) := by
    have h_add : m + 4 = 4 + m := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) m, h_r]
  bb_steps

/-- Shared prelude for even `n = 2 * k`: from `left = (10)^(6k+2)` and `right = [0, 1, 0] ++ r` to
the inner-loop entry state with `2 * (6k + 1)` leading ones and `4` inner ones. -/
private theorem prelude_even (k : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k + 2)) default)
        (ListBlank.append [0, 1, 0] r))
      (Cfg.headRight A default
        (ListBlank.append (([1] : List (Fin 2)) ^ (2 * (6 * k + 1)))
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4)
            (ListBlank.append [0] r))))) := by
  have h_l :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [1, 0, 1, 0]
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default) := by
    have h_add : 6 * k + 2 = 2 + 6 * k := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_l]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 0, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default))
          (ListBlank.append [0, 1, 0] r))
        (Cfg.headRight D
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 0)
              (ListBlank.append [0]
                (ListBlank.append (([1] : List (Fin 2)) ^ 4)
                  (ListBlank.append [0] r)))))) := by
    have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    rw [list_pow_zero, ListBlank.append_nil, h4]
    bb_steps
  have h2 := sweep_D_to_A (6 * k) 0
    (ListBlank.append [0]
      (ListBlank.append (([1] : List (Fin 2)) ^ 4) (ListBlank.append [0] r)))
  have h12 := h1.trans h2
  have h_eq : 2 * (6 * k) + 0 + 2 = 2 * (6 * k + 1) := by omega
  rwa [h_eq] at h12

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$A(n, m) := 0^\infty\,(01)^{3n+2}\,\mathrm{A}{>}\,(01)^m\,0^\infty$. -/
def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0, 1, 0, 1, 0] 0 .default))))
    head := some A
    right := .rep [0, 1] 1 .default }

/-- Closed pattern set for `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .true)]

/-- Configuration $A(n, m)$. -/
private def cfg_A (n m : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight A
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * n + 2)) default)
    (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default)

private theorem eval_pat_A (vars : ℕ → ℕ) :
    evalTapePattern pat_A vars = cfg_A (vars 0) (vars 1) := by
  simp only [pat_A, evalTapePattern_some, evalTapeExpr_rep, evalTapeExpr_sym, evalTapeExpr_default,
    cfg_A]
  have h_six : ([1, 0, 1, 0, 1, 0] : List (Fin 2)) = ([1, 0] : List (Fin 2)) ^ 3 := rfl
  rw [h_six, ← list_pow_mul]
  change Cfg.headRight A
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 2)
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * vars 0)) default)) _ = _
  rw [← ListBlank.append_pow_add, Nat.add_comm 2 (3 * vars 0)]

private theorem in_ps_A (n m : ℕ) : IsInPatternSet ps (cfg_A n m) :=
  ⟨(pat_A, .true), List.Mem.head _,
    fun i => match i with | 0 => n | 1 => m | _ => 0, by rw [eval_pat_A]; rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem phase2 (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight A default (ListBlank.append [0, 0, 0] r))
      (Cfg.headRight A
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * 0 + 2)) default)
        (ListBlank.append [0] r)) := by
  have h_l : (([1, 0] : List (Fin 2)) ^ (3 * 0 + 2)) = [1, 0, 1, 0] := rfl
  rw [h_l]
  bb_steps

/-- Rule 1 (reset): $A(n, 0) \to^+ A(0, 3n + 2)$. -/
private theorem step_A_reset (n : ℕ) :
    ReachesPlus target (cfg_A n 0) (cfg_A 0 (3 * n + 2)) := by
  unfold cfg_A
  rw [list_pow_zero, ListBlank.append_nil]
  have h_def : (default : ListBlank (Fin 2)) = ListBlank.append [0, 0] default := by simp
  nth_rw 2 [h_def]
  have h1 := shift_A_left (3 * n + 2) default default
  have h_split :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * n + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [0]
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * n + 1)) default)) := by
    have h_add : 3 * n + 2 = 1 + (3 * n + 1) := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  have h_r :
      ListBlank.append [0, 0]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * n + 2)) (default : ListBlank (Fin 2))) =
        ListBlank.append [0, 0, 0]
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * n + 1)) default)) := by
    rw [h_split]
    rfl
  rw [h_r] at h1
  have h2 := phase2
    (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (3 * n + 1)) default))
  rw [← h_split] at h2
  exact h1.trans_plus h2

/-- Rule 2 (even): $A(2k, m + 2) \to^+ A(3k + 1, m)$. -/
private theorem step_A_even (k m : ℕ) :
    ReachesPlus target (cfg_A (2 * k) (m + 2)) (cfg_A (3 * k + 1) m) := by
  unfold cfg_A
  have h_l_init : 3 * (2 * k) + 2 = 6 * k + 2 := by omega
  have h_r_init :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ (m + 2)) (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 1, 0]
          (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default)) := by
    have h_add : m + 2 = 2 + m := by omega
    rw [h_add, ListBlank.append_pow_add]
    rfl
  rw [h_l_init, h_r_init]
  set R := ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default
  have h1 := prelude_even k (ListBlank.append [1] R)
  have h2 := inner_loop (6 * k) 3 (ListBlank.append [0] (ListBlank.append [1] R))
  have h12 := h1.trans_star h2
  have h3 := post_inner_turnaround (3 + 3 * (6 * k))
    (ListBlank.append [0] (ListBlank.append [1] R))
  have h123 := h12.trans h3
  have h_m :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 + 3 * (6 * k) + 4))
        (ListBlank.append [0] (ListBlank.append [1] R)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (9 * k + 3)))
          (ListBlank.append [1, 0, 1] R) := by
    have h_add : 3 + 3 * (6 * k) + 4 = 2 * (9 * k + 3) + 1 := by omega
    rw [h_add, ListBlank.append_pow_add, list_pow_one]
    rfl
  rw [h_m] at h123
  have h4 := shift_AE (9 * k + 3) default (ListBlank.append [1, 0, 1] R)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (9 * k + 3)) default)
          (ListBlank.append [1, 0, 1] R))
        (Cfg.headRight D
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (9 * k + 3)) default)
          (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 2) R))) := by
    have h_two : (([1] : List (Fin 2)) ^ 2) = [1, 1] := rfl
    rw [h_two]
    bb_steps
  have h12345 := h1234.trans h5
  have h6 := sweep_D_to_A (9 * k + 3) 2 R
  have h123456 := h12345.trans h6
  have h_eq : 2 * (9 * k + 3) + 2 + 2 = 2 * (3 * (3 * k + 1) + 2) := by omega
  rw [h_eq] at h123456
  have h7 := shift_AE (3 * (3 * k + 1) + 2) default R
  exact h123456.trans_star h7

/-- Rule 3 (odd): $A(2k + 1, m + 1) \to^+ A(3k + 2, m)$. -/
private theorem step_A_odd (k m : ℕ) :
    ReachesPlus target (cfg_A (2 * k + 1) (m + 1)) (cfg_A (3 * k + 2) m) := by
  unfold cfg_A
  set R := ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default
  have h_l :
      ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * (2 * k + 1) + 2))
        (default : ListBlank (Fin 2)) =
        ListBlank.append (([1, 0] : List (Fin 2)) ^ 5)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default) := by
    have h_add : 3 * (2 * k + 1) + 2 = 5 + 6 * k := by omega
    rw [h_add, ListBlank.append_pow_add]
  rw [h_l, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) m]
  have h1 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ 5)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default))
          (ListBlank.append [0, 1] R))
        (Cfg.headRight D
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (6 * k)) default)
          (ListBlank.append [0]
            (ListBlank.append (([1] : List (Fin 2)) ^ 6)
              (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) R))))) := by
    have h5 : (([1, 0] : List (Fin 2)) ^ 5) = [1, 0, 1, 0, 1, 0, 1, 0, 1, 0] := rfl
    have h6 : (([1] : List (Fin 2)) ^ 6) = [1, 1, 1, 1, 1, 1] := rfl
    have h4 : (([1] : List (Fin 2)) ^ 4) = [1, 1, 1, 1] := rfl
    rw [h5, h6, h4]
    bb_steps
  have h2 := sweep_D_to_A (6 * k) 6
    (ListBlank.append [0] (ListBlank.append (([1] : List (Fin 2)) ^ 4) R))
  have h12 := h1.trans h2
  have h_eq1 : 2 * (6 * k) + 6 + 2 = 2 * ((6 * k + 3) + 1) := by omega
  rw [h_eq1] at h12
  have h3 := inner_loop (6 * k + 3) 3 R
  have h123 := h12.trans_star h3
  have h4 := post_inner_turnaround (3 + 3 * (6 * k + 3)) R
  have h1234 := h123.trans h4
  have h_eq2 : 3 + 3 * (6 * k + 3) + 4 = 2 * (3 * (3 * k + 2) + 2) := by omega
  rw [h_eq2] at h1234
  have h5 := shift_AE (3 * (3 * k + 2) + 2) default R
  exact h1234.trans_star h5

/-- Rule 4 (halt): $A(2k, 1)$ reaches a halting configuration. -/
private theorem step_A_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A (2 * k) 1) cfg' ∧ (step target cfg').isNone := by
  unfold cfg_A
  have h_l : 3 * (2 * k) + 2 = 6 * k + 2 := by omega
  have h_r :
      ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) (default : ListBlank (Fin 2)) =
        ListBlank.append [0, 1, 0] default := by
    simp
  rw [h_l, h_r]
  have h1 := prelude_even k default
  have h_def : ListBlank.append [0] (default : ListBlank (Fin 2)) = default := by simp
  rw [h_def] at h1
  have h2 := inner_loop (6 * k) 3 default
  have h12 := h1.trans_star h2
  have h3 := post_inner_turnaround (3 + 3 * (6 * k)) default
  have h123 := h12.trans h3
  have h_m :
      ListBlank.append (([1] : List (Fin 2)) ^ (3 + 3 * (6 * k) + 4))
        (default : ListBlank (Fin 2)) =
        ListBlank.append (([1] : List (Fin 2)) ^ (2 * (9 * k + 3)))
          (ListBlank.append [1] default) := by
    have h_add : 3 + 3 * (6 * k) + 4 = 2 * (9 * k + 3) + 1 := by omega
    rw [h_add, ListBlank.append_pow_add, list_pow_one]
  rw [h_m] at h123
  have h4 := shift_AE (9 * k + 3) default (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (9 * k + 3)) default)
          (ListBlank.append [1] default))
        (Cfg.headRight F
          (ListBlank.append [1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (9 * k + 3)) default))
          default) := by
    bb_steps
  refine ⟨_, h1234.trans h5, ?_⟩
  bb_halt

private theorem step_A (n m : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_A n m) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases m with _ | _ | m'
  · exact ⟨cfg_A 0 (3 * n + 2), step_A_reset n, Or.inl (in_ps_A 0 (3 * n + 2))⟩
  · rcases nat_even_or_odd_two_mul n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · obtain ⟨cfg', h1, h2⟩ := step_A_halt k
      exact ⟨cfg', h1, Or.inr h2⟩
    · exact ⟨cfg_A (3 * k + 2) 0, step_A_odd k 0, Or.inl (in_ps_A (3 * k + 2) 0)⟩
  · rcases nat_even_or_odd_two_mul n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · exact ⟨cfg_A (3 * k + 1) m', step_A_even k m', Or.inl (in_ps_A (3 * k + 1) m')⟩
    · exact ⟨cfg_A (3 * k + 2) (m' + 1), step_A_odd k (m' + 1),
        Or.inl (in_ps_A (3 * k + 2) (m' + 1))⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_A 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_A 0 0) := by
    unfold cfg_A
    have h2 : (([1, 0] : List (Fin 2)) ^ (3 * 0 + 2)) = [1, 0, 1, 0] := rfl
    rw [h2, list_pow_zero, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A 0 0, init_reaches_start, in_ps_A 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_A]
  exact step_A (vars 0) (vars 1)

/-- `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_---1LB`. -/
inductive State where
  /-- $A(n, m) := 0^\infty\,(01)^{3n+2}\,\mathrm{A}{>}\,(01)^m\,0^\infty$. -/
  | A (n m : ℕ)

/-- Initial symbolic state $A(0, 0)$, reached after 22 raw TM steps. -/
def start : State := .A 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .A n m =>
    Cfg.headRight SixState.A
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * n + 2)) default)
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ m) default)

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .A n 0 => some (.A 0 (3 * n + 2))
  | .A n 1 =>
    if n % 2 = 0 then none
    else some (.A (3 * (n / 2) + 2) 0)
  | .A n (m + 2) =>
    if n % 2 = 0 then some (.A (3 * (n / 2) + 1) m)
    else some (.A (3 * (n / 2) + 2) (m + 1))

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨n, m⟩ s' hnext
    rcases m with _ | _ | m'
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_A_reset n
    · rcases nat_even_or_odd_two_mul n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have h_mod : (2 * k) % 2 = 0 := by omega
        simp [next, h_mod] at hnext
      · have h_mod : (2 * k + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * k + 1) / 2 = k := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_odd k 0
    · rcases nat_even_or_odd_two_mul n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · have h_mod : (2 * k) % 2 = 0 := by omega
        have h_div : (2 * k) / 2 = k := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_even k m'
      · have h_mod : (2 * k + 1) % 2 ≠ 0 := by omega
        have h_div : (2 * k + 1) / 2 = k := by omega
        simp only [next, h_mod, ↓reduceIte, h_div, Option.some.injEq] at hnext
        subst hnext
        exact step_A_odd k (m' + 1)
  step_none := by
    rintro ⟨n, m⟩ hnext
    rcases m with _ | _ | m'
    · simp [next] at hnext
    · rcases nat_even_or_odd_two_mul n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨cfg', hp, hh⟩ := step_A_halt k
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · by_cases h : n % 2 = 0 <;> simp [next, h] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RE_1LC1LD_0RA0LD_1LB0LA_1RF1RA_HHH1LB
