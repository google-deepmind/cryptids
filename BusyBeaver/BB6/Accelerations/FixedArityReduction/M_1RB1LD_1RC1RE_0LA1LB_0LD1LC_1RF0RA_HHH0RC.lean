/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout
`1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`
(see <https://wiki.bbchallenge.org/wiki/1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC>)
(`cryptid_7`, holdout #432, `suspect_90`).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$Q(a, c) := 0^\infty\,\mathrm{D}{>}\,(10)^a\,(110)^c\,11\,0^\infty$$
at $Q(0, 0)$ in 4 steps, and every $Q(a, c)$ advances in `ReachesPlus` either to another
$Q(a', c')$ or to a halting configuration (when $a \equiv 6 \pmod{9}$ and $c = 0$).

## Collatz-like Acceleration Rules

```text
Consider:
Q(a, c) = 0^inf D> (10)^a (110)^c 11 0^inf

Q(3m, c+1)   -> Q(4m+3, c)
Q(3m+1, c)   -> Q(3m, c+2)
Q(3m+2, c)   -> Q(4m+4, c+1)
Q(9k, 0)     -> Q(12k+3, 0)
Q(9k+3, 0)   -> Q(12k+6, 1)
Q(9k+6, 0)   -> Halt

Start: Q(0, 0), reached after 4 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift and Sweep Lemmas -/

/-- Rightward shift across `(10)^(3m)` in state `C`. -/
private theorem shift_C_right (m : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C (ListBlank.append [1, 1] l)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m)) r))
      (Cfg.headRight C
        (ListBlank.append [1, 1]
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) l))
        r) := by
  induction m generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    have h_mul : 3 * (m + 1) = 3 + 3 * m := by omega
    rw [h_mul, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) 3 (3 * m) r]
    have h1 :
        ReachesPlus target
          (Cfg.headRight C (ListBlank.append [1, 1] l)
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m)) r)))
          (Cfg.headRight C
            (ListBlank.append [1, 1]
              (ListBlank.append [1, 1, 1, 0, 1, 1] l))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m)) r)) := by
      have h_pow3 : (([1, 0] : List (Fin 2)) ^ 3) = [1, 0, 1, 0, 1, 0] := rfl
      rw [h_pow3]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1, 1, 0, 1, 1] l) r
    have h12 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m)
          (ListBlank.append [1, 1, 1, 0, 1, 1] l) =
          ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ (m + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h12

/-- Leftward shift across `(110111)^m` in state `D`. -/
private theorem shift_D_left (m : ℕ) (l u : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight D
        (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) l)
        (ListBlank.append [1] u))
      (Cfg.headRight D l
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
          (ListBlank.append [1] u))) := by
  induction m generalizing l u with
  | zero => exact ReachesStar.refl _ _
  | succ m ih =>
    rw [ListBlank.append_pow_succ]
    have h1 :
        ReachesPlus target
          (Cfg.headRight D
            (ListBlank.append [1, 1, 1, 0, 1, 1]
              (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) l))
            (ListBlank.append [1] u))
          (Cfg.headRight D
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) l)
            (ListBlank.append [1]
              (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1] u)))) := by
      bb_steps
    have h2 := ih l (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1] u))
    have h12 := (h1.trans_star h2).to_star
    have h_r1 :
        ListBlank.append [1]
          (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1] u)) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ 3) (ListBlank.append [1] u) :=
      rfl
    rw [h_r1, ← ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * m) 3] at h12
    have h_mul : 3 * m + 3 = 3 * (m + 1) := by omega
    rwa [h_mul] at h12

/-- Right-to-left bounce across `(110)^c 11` from state `B` to state `A`. -/
private theorem bounce_B (c : ℕ) (l : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight B l
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1] default)))
      (Cfg.headRight A l
        (ListBlank.append [1, 0]
          (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append [1, 1] default)))) := by
  induction c generalizing l with
  | zero =>
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  | succ c ih =>
    rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) c]
    have h1 :
        ReachesPlus target
          (Cfg.headRight B l
            (ListBlank.append [1, 1, 0]
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default))))
          (Cfg.headRight B (ListBlank.append [1, 0, 1] l)
            (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1] default))) := by
      bb_steps
    have h2 := ih (ListBlank.append [1, 0, 1] l)
    have h12 := h1.trans h2
    have h3 :
        ReachesPlus target
          (Cfg.headRight A (ListBlank.append [1, 0, 1] l)
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default))))
          (Cfg.headRight A l
            (ListBlank.append [1, 0]
              (ListBlank.append [1, 1, 0]
                (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append [1, 1] default))))) := by
      bb_steps
    exact h12.trans h3

/-- Left-boundary turn from `D` into `C` with `[1, 1]` pushed to the left half-tape. -/
private theorem enter_D_to_C_pow (k : ℕ) (u : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D default
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] u)))
      (Cfg.headRight C (ListBlank.append [1, 1] default)
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1] u))) := by
  rcases k with _ | k
  · rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  · rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) k]
    bb_steps

/-- Single-block prefix reduction converting `(10)^3` before `110` into `(10)^4` after `110`. -/
private theorem step_prefix_succ (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D default
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * (m + 1)))
          (ListBlank.append [1, 1, 0] r)))
      (Cfg.headRight D default
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
          (ListBlank.append [1, 1, 0]
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 4) r)))) := by
  have h_mul : 3 * (m + 1) = 3 * m + 3 := by omega
  rw [h_mul, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * m) 3]
  have h1 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
              (ListBlank.append [1, 1, 0] r))))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
              (ListBlank.append [1, 1, 0] r)))) :=
    enter_D_to_C_pow (3 * m) (ListBlank.append [0, 1, 0, 1, 0, 1, 1, 0] r)
  have h2 := shift_C_right m default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3) (ListBlank.append [1, 1, 0] r))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ 3)
            (ListBlank.append [1, 1, 0] r)))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default)
          (ListBlank.append [1]
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ 4) r)))) := by
    have h_pow3 : (([1, 0] : List (Fin 2)) ^ 3) = [1, 0, 1, 0, 1, 0] := rfl
    have h_pow4 : (([1, 0] : List (Fin 2)) ^ 4) = [1, 0, 1, 0, 1, 0, 1, 0] := rfl
    rw [h_pow3, h_pow4]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_D_left m default
    (ListBlank.append [1, 0] (ListBlank.append (([1, 0] : List (Fin 2)) ^ 4) r))
  exact h123.trans_star h4

/-- Drain `(10)^(3m) 110` into `(10)^(4m+3)`. -/
private theorem drain_prefix (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target
      (Cfg.headRight D default
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
          (ListBlank.append [1, 1, 0] r)))
      (Cfg.headRight D default
        (ListBlank.append (([1, 0] : List (Fin 2)) ^ (4 * m + 3)) r)) := by
  induction m generalizing r with
  | zero =>
    have h_pow3 : (([1, 0] : List (Fin 2)) ^ (4 * 0 + 3)) = [1, 0, 1, 0, 1, 0] := rfl
    rw [Nat.mul_zero, list_pow_zero, ListBlank.append_nil, h_pow3]
    bb_steps
  | succ m ih =>
    have h1 := step_prefix_succ m r
    have h2 := ih (ListBlank.append (([1, 0] : List (Fin 2)) ^ 4) r)
    have h12 := h1.trans h2
    rw [← ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (4 * m + 3) 4 r] at h12
    have h_add : 4 * m + 3 + 4 = 4 * (m + 1) + 3 := by omega
    rwa [h_add] at h12

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$Q(a, c) := 0^\infty\,\mathrm{D}{>}\,(10)^a\,(110)^c\,11\,0^\infty$. -/
def pat_Q : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .rep [1, 0] 0 (.rep [1, 1, 0] 1 (.sym 1 (.sym 1 .default))) }

/-- Closed pattern set for `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_Q, .true)]

/-- Configuration $Q(a, c)$. -/
private def cfg_Q (a c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1] default)))

/-- Auxiliary configuration $R(n) := 0^\infty\,\mathrm{D}{>}\,(10)^n\,1\,0^\infty$. -/
private def cfg_R (n : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headRight D default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ n) (ListBlank.append [1] default))

private theorem eval_pat_Q (vars : ℕ → ℕ) :
    evalTapePattern pat_Q vars = cfg_Q (vars 0) (vars 1) :=
  rfl

private theorem in_ps_Q (a c : ℕ) : IsInPatternSet ps (cfg_Q a c) :=
  ⟨(pat_Q, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => c | _ => 0, rfl, trivial⟩

/-! ## Accelerated Transition Rules -/

private theorem step_Q_mod0_c_succ (m c : ℕ) :
    ReachesPlus target (cfg_Q (3 * m) (c + 1)) (cfg_Q (4 * m + 3) c) := by
  unfold cfg_Q
  rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) c]
  exact drain_prefix m
    (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c) (ListBlank.append [1, 1] default))

private theorem step_Q_mod1 (m c : ℕ) :
    ReachesPlus target (cfg_Q (3 * m + 1) c) (cfg_Q (3 * m) (c + 2)) := by
  unfold cfg_Q
  rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * m) 1]
  have h1 :
      ReachesPlus target
        (Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default)))))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default))))) :=
    enter_D_to_C_pow (3 * m)
      (ListBlank.append [0]
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1] default)))
  have h2 := shift_C_right m default
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1] default)))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
            (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1] default))))
        (Cfg.headRight B
          (ListBlank.append [1, 0, 1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append [1, 1] default))) := by
    rw [list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h4 := bounce_B c
    (ListBlank.append [1, 0, 1, 1]
      (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
  have h1234 := h123.trans h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 0, 1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append [1, 0]
            (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1] default))))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default)
          (ListBlank.append [1]
            (ListBlank.append [1, 0, 1, 1, 0]
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default))))) := by
    bb_steps
  have h12345 := h1234.trans h5
  have h6 := shift_D_left m default
    (ListBlank.append [1, 0, 1, 1, 0]
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1] default)))
  have h123456 := h12345.trans_star h6
  rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) (c + 1),
    ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) c]
  exact h123456

private theorem step_Q_mod2_c0 (m : ℕ) :
    ReachesPlus target (cfg_Q (3 * m + 2) 0) (cfg_Q (4 * m + 4) 1) := by
  have h_cfg :
      cfg_Q (3 * m + 2) 0 =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append [1] (ListBlank.append [0, 1, 0, 1, 1] default))) := by
    unfold cfg_Q
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * m) 2]
    rfl
  have h1 :
      ReachesPlus target (cfg_Q (3 * m + 2) 0)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append [1, 0, 1, 0, 1, 1] default))) := by
    rw [h_cfg]
    exact enter_D_to_C_pow (3 * m) (ListBlank.append [0, 1, 0, 1, 1] default)
  have h2 := shift_C_right m default (ListBlank.append [1, 0, 1, 0, 1, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append [1, 0, 1, 0, 1, 1] default))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default)
          (ListBlank.append [1]
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
                (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
                  (ListBlank.append [1, 1] default)))))) := by
    rw [list_pow_one, list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_D_left m default
    (ListBlank.append [1, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
          (ListBlank.append [1, 1] default))))
  have h1234 := h123.trans_star h4
  have h5 := drain_prefix m
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
        (ListBlank.append [1, 1] default)))
  have h12345 := h1234.trans h5
  unfold cfg_Q
  rw [← ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (4 * m + 3) 1] at h12345
  have h_add : 4 * m + 3 + 1 = 4 * m + 4 := by omega
  rwa [h_add] at h12345

private theorem step_Q_mod2_c_succ (m c : ℕ) :
    ReachesPlus target (cfg_Q (3 * m + 2) (c + 1)) (cfg_Q (4 * m + 4) (c + 2)) := by
  have h_cfg :
      cfg_Q (3 * m + 2) (c + 1) =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append [1]
              (ListBlank.append [0, 1, 0, 1, 1, 0]
                (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                  (ListBlank.append [1, 1] default))))) := by
    unfold cfg_Q
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * m) 2,
      ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) c]
    rfl
  have h1 :
      ReachesPlus target (cfg_Q (3 * m + 2) (c + 1))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append [1, 0, 1, 0, 1, 1, 0]
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
                (ListBlank.append [1, 1] default))))) := by
    rw [h_cfg]
    exact enter_D_to_C_pow (3 * m)
      (ListBlank.append [0, 1, 0, 1, 1, 0]
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1] default)))
  have h2 := shift_C_right m default
    (ListBlank.append [1, 0, 1, 0, 1, 1, 0]
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
        (ListBlank.append [1, 1] default)))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append [1, 0, 1, 0, 1, 1, 0]
            (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1] default))))
        (Cfg.headRight B
          (ListBlank.append [1, 0, 1, 1, 1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
            (ListBlank.append [1, 1] default))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := bounce_B c
    (ListBlank.append [1, 0, 1, 1, 1, 1, 0, 1, 1]
      (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
  have h1234 := h123.trans h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight A
          (ListBlank.append [1, 0, 1, 1, 1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default))
          (ListBlank.append [1, 0]
            (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1] default))))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ m) default)
          (ListBlank.append [1]
            (ListBlank.append [1, 0]
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
                (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ (c + 2))
                  (ListBlank.append [1, 1] default)))))) := by
    rw [ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) (c + 1),
      ListBlank.append_pow_succ ([1, 1, 0] : List (Fin 2)) c, list_pow_one]
    bb_steps
  have h12345 := h1234.trans h5
  have h6 := shift_D_left m default
    (ListBlank.append [1, 0]
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ (c + 2))
          (ListBlank.append [1, 1] default))))
  have h123456 := h12345.trans_star h6
  have h7 := drain_prefix m
    (ListBlank.append (([1, 0] : List (Fin 2)) ^ 1)
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ (c + 2))
        (ListBlank.append [1, 1] default)))
  have h1234567 := h123456.trans h7
  unfold cfg_Q
  rw [← ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (4 * m + 3) 1] at h1234567
  have h_add : 4 * m + 3 + 1 = 4 * m + 4 := by omega
  rwa [h_add] at h1234567

private theorem step_Q_mod2 (m c : ℕ) :
    ReachesPlus target (cfg_Q (3 * m + 2) c) (cfg_Q (4 * m + 4) (c + 1)) := by
  rcases c with _ | c'
  · exact step_Q_mod2_c0 m
  · exact step_Q_mod2_c_succ m c'

private theorem step_Q_mod0_c0_to_R (m : ℕ) :
    ReachesPlus target (cfg_Q (3 * m) 0) (cfg_R (4 * m + 2)) := by
  have h_eq1 :
      cfg_Q (3 * m) 0 =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * m))
            (ListBlank.append [1, 1, 0] default)) := by
    unfold cfg_Q
    simp
  have h_eq2 :
      Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (4 * m + 3)) default) =
        cfg_R (4 * m + 2) := by
    unfold cfg_R
    have h_add : 4 * m + 3 = (4 * m + 2) + 1 := by omega
    rw [h_add, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (4 * m + 2) 1]
    simp
  rw [h_eq1, ← h_eq2]
  exact drain_prefix m default

private theorem step_R_mod1_halt (j : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_R (3 * j + 1)) cfg' ∧ (step target cfg').isNone := by
  have h_cfg :
      cfg_R (3 * j + 1) =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1] (ListBlank.append [0, 1] default))) := by
    unfold cfg_R
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * j) 1]
    rfl
  have h1 :
      ReachesPlus target (cfg_R (3 * j + 1))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1, 0, 1] default))) := by
    rw [h_cfg]
    exact enter_D_to_C_pow (3 * j) (ListBlank.append [0, 1] default)
  have h2 := shift_C_right j default (ListBlank.append [1, 0, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default))
          (ListBlank.append [1, 0, 1] default))
        (Cfg.headRight F
          (ListBlank.append [1, 1, 1, 0, 1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default))
          default) := by
    bb_steps
  refine ⟨_, h12.trans h3, ?_⟩
  bb_halt

private theorem step_R_mod2 (j : ℕ) :
    ReachesPlus target (cfg_R (3 * j + 2)) (cfg_Q (3 * j + 3) 0) := by
  have h_cfg :
      cfg_R (3 * j + 2) =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1] (ListBlank.append [0, 1, 0, 1] default))) := by
    unfold cfg_R
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * j) 2]
    rfl
  have h1 :
      ReachesPlus target (cfg_R (3 * j + 2))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1, 0, 1, 0, 1] default))) := by
    rw [h_cfg]
    exact enter_D_to_C_pow (3 * j) (ListBlank.append [0, 1, 0, 1] default)
  have h2 := shift_C_right j default (ListBlank.append [1, 0, 1, 0, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default))
          (ListBlank.append [1, 0, 1, 0, 1] default))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default)
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1, 1] default)))) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_D_left j default
    (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1, 1] default))
  have h1234 := h123.trans_star h4
  have h_eq :
      Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1]
              (ListBlank.append [0, 1, 0, 1, 0] (ListBlank.append [1, 1] default)))) =
        cfg_Q (3 * j + 3) 0 := by
    unfold cfg_Q
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * j) 3]
    rfl
  rwa [h_eq] at h1234

private theorem step_R_mod0 (j : ℕ) :
    ReachesPlus target (cfg_R (3 * (j + 1))) (cfg_Q (3 * j + 3) 1) := by
  have h_cfg :
      cfg_R (3 * (j + 1)) =
        Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1] (ListBlank.append [0, 1, 0, 1, 0, 1] default))) := by
    unfold cfg_R
    have h_mul : 3 * (j + 1) = 3 * j + 3 := by omega
    rw [h_mul, ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * j) 3]
    rfl
  have h1 :
      ReachesPlus target (cfg_R (3 * (j + 1)))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1, 0, 1, 0, 1, 0, 1] default))) := by
    rw [h_cfg]
    exact enter_D_to_C_pow (3 * j) (ListBlank.append [0, 1, 0, 1, 0, 1] default)
  have h2 := shift_C_right j default (ListBlank.append [1, 0, 1, 0, 1, 0, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default))
          (ListBlank.append [1, 0, 1, 0, 1, 0, 1] default))
        (Cfg.headRight D
          (ListBlank.append (([1, 1, 1, 0, 1, 1] : List (Fin 2)) ^ j) default)
          (ListBlank.append [1]
            (ListBlank.append [0, 1, 0, 1, 0]
              (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
                (ListBlank.append [1, 1] default))))) := by
    rw [list_pow_one]
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_D_left j default
    (ListBlank.append [0, 1, 0, 1, 0]
      (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
        (ListBlank.append [1, 1] default)))
  have h1234 := h123.trans_star h4
  have h_eq :
      Cfg.headRight D default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (3 * j))
            (ListBlank.append [1]
              (ListBlank.append [0, 1, 0, 1, 0]
                (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ 1)
                  (ListBlank.append [1, 1] default))))) =
        cfg_Q (3 * j + 3) 1 := by
    unfold cfg_Q
    rw [ListBlank.append_pow_add ([1, 0] : List (Fin 2)) (3 * j) 3]
    rfl
  rwa [h_eq] at h1234

private theorem step_Q_mod9_0 (k : ℕ) :
    ReachesPlus target (cfg_Q (9 * k) 0) (cfg_Q (12 * k + 3) 0) := by
  have h_a : 9 * k = 3 * (3 * k) := by omega
  have h_r : 4 * (3 * k) + 2 = 3 * (4 * k) + 2 := by omega
  have h_q : 3 * (4 * k) + 3 = 12 * k + 3 := by omega
  have h1 := step_Q_mod0_c0_to_R (3 * k)
  rw [← h_a, h_r] at h1
  have h2 := step_R_mod2 (4 * k)
  rw [h_q] at h2
  exact h1.trans h2

private theorem step_Q_mod9_3 (k : ℕ) :
    ReachesPlus target (cfg_Q (9 * k + 3) 0) (cfg_Q (12 * k + 6) 1) := by
  have h_a : 9 * k + 3 = 3 * (3 * k + 1) := by omega
  have h_r : 4 * (3 * k + 1) + 2 = 3 * (4 * k + 1 + 1) := by omega
  have h_q : 3 * (4 * k + 1) + 3 = 12 * k + 6 := by omega
  have h1 := step_Q_mod0_c0_to_R (3 * k + 1)
  rw [← h_a, h_r] at h1
  have h2 := step_R_mod0 (4 * k + 1)
  rw [h_q] at h2
  exact h1.trans h2

private theorem step_Q_mod9_6 (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Q (9 * k + 6) 0) cfg' ∧ (step target cfg').isNone := by
  have h_a : 9 * k + 6 = 3 * (3 * k + 2) := by omega
  have h_r : 4 * (3 * k + 2) + 2 = 3 * (4 * k + 3) + 1 := by omega
  have h1 := step_Q_mod0_c0_to_R (3 * k + 2)
  rw [← h_a, h_r] at h1
  obtain ⟨cfg', h2, hh⟩ := step_R_mod1_halt (4 * k + 3)
  exact ⟨cfg', h1.trans h2, hh⟩

private theorem step_Q (a c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_Q a c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have ha_mod : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 := ⟨a / 3, by omega⟩
  rcases ha_mod with ⟨m, rfl | rfl | rfl⟩
  · rcases c with _ | c'
    · have hm_mod : ∃ k, m = 3 * k ∨ m = 3 * k + 1 ∨ m = 3 * k + 2 := ⟨m / 3, by omega⟩
      rcases hm_mod with ⟨k, rfl | rfl | rfl⟩
      · have h_eq : 3 * (3 * k) = 9 * k := by omega
        rw [h_eq]
        exact ⟨cfg_Q (12 * k + 3) 0, step_Q_mod9_0 k, Or.inl (in_ps_Q _ _)⟩
      · have h_eq : 3 * (3 * k + 1) = 9 * k + 3 := by omega
        rw [h_eq]
        exact ⟨cfg_Q (12 * k + 6) 1, step_Q_mod9_3 k, Or.inl (in_ps_Q _ _)⟩
      · have h_eq : 3 * (3 * k + 2) = 9 * k + 6 := by omega
        rw [h_eq]
        obtain ⟨cfg', hp, hh⟩ := step_Q_mod9_6 k
        exact ⟨cfg', hp, Or.inr hh⟩
    · exact ⟨cfg_Q (4 * m + 3) c', step_Q_mod0_c_succ m c', Or.inl (in_ps_Q _ _)⟩
  · exact ⟨cfg_Q (3 * m) (c + 2), step_Q_mod1 m c, Or.inl (in_ps_Q _ _)⟩
  · exact ⟨cfg_Q (4 * m + 4) (c + 1), step_Q_mod2 m c, Or.inl (in_ps_Q _ _)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_Q 0 0) := by
  have h_init : ReachesPlus target (init []) (cfg_Q 0 0) := by
    unfold cfg_Q
    rw [list_pow_zero, list_pow_zero, ListBlank.append_nil, ListBlank.append_nil]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_Q 0 0, init_reaches_start, in_ps_Q 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_Q]
  exact step_Q (vars 0) (vars 1)

/-- `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_---0RC`. -/
inductive State where
  /-- $Q(a, c) := 0^\infty\,\mathrm{D}{>}\,(10)^a\,(110)^c\,11\,0^\infty$. -/
  | Q (a c : ℕ)

/-- Initial symbolic state $Q(0, 0)$, reached after 4 raw TM steps. -/
def start : State := .Q 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .Q a c =>
    Cfg.headRight SixState.D default
      (ListBlank.append (([1, 0] : List (Fin 2)) ^ a)
        (ListBlank.append (([1, 1, 0] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1] default)))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .Q a c =>
    if a % 3 = 1 then
      some (.Q (3 * (a / 3)) (c + 2))
    else if a % 3 = 2 then
      some (.Q (4 * (a / 3) + 4) (c + 1))
    else
      match c with
      | c' + 1 => some (.Q (4 * (a / 3) + 3) c')
      | 0 =>
        if a % 9 = 0 then
          some (.Q (12 * (a / 9) + 3) 0)
        else if a % 9 = 3 then
          some (.Q (12 * (a / 9) + 6) 1)
        else
          none

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, c⟩ s' hnext
    have ha_mod : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 := ⟨a / 3, by omega⟩
    rcases ha_mod with ⟨m, rfl | rfl | rfl⟩
    · rcases c with _ | c'
      · have hm_mod : ∃ k, m = 3 * k ∨ m = 3 * k + 1 ∨ m = 3 * k + 2 := ⟨m / 3, by omega⟩
        rcases hm_mod with ⟨k, rfl | rfl | rfl⟩
        · have h_m3 : (3 * (3 * k)) % 3 = 0 := by omega
          have h_m9 : (3 * (3 * k)) % 9 = 0 := by omega
          have h_d9 : (3 * (3 * k)) / 9 = k := by omega
          simp only [next, h_m3, h_m9, h_d9, ↓reduceIte, Nat.reduceEqDiff,
            Option.some.injEq] at hnext
          subst hnext
          have h_eq : 3 * (3 * k) = 9 * k := by omega
          rw [encode, h_eq]
          exact step_Q_mod9_0 k
        · have h_m3 : (3 * (3 * k + 1)) % 3 = 0 := by omega
          have h_m9 : (3 * (3 * k + 1)) % 9 = 3 := by omega
          have h_d9 : (3 * (3 * k + 1)) / 9 = k := by omega
          simp only [next, h_m3, h_m9, h_d9, ↓reduceIte, Nat.reduceEqDiff,
            Option.some.injEq] at hnext
          subst hnext
          have h_eq : 3 * (3 * k + 1) = 9 * k + 3 := by omega
          rw [encode, h_eq]
          exact step_Q_mod9_3 k
        · have h_m3 : (3 * (3 * k + 2)) % 3 = 0 := by omega
          have h_m9 : (3 * (3 * k + 2)) % 9 = 6 := by omega
          simp [next, h_m3, h_m9] at hnext
      · have h_m3 : (3 * m) % 3 = 0 := by omega
        have h_d3 : (3 * m) / 3 = m := by omega
        simp only [next, h_m3, h_d3, ↓reduceIte, Nat.reduceEqDiff, Option.some.injEq] at hnext
        subst hnext
        exact step_Q_mod0_c_succ m c'
    · have h_m3 : (3 * m + 1) % 3 = 1 := by omega
      have h_d3 : (3 * m + 1) / 3 = m := by omega
      simp only [next, h_m3, h_d3, ↓reduceIte, Option.some.injEq] at hnext
      subst hnext
      exact step_Q_mod1 m c
    · have h_m3 : (3 * m + 2) % 3 = 2 := by omega
      have h_d3 : (3 * m + 2) / 3 = m := by omega
      simp only [next, h_m3, h_d3, ↓reduceIte, Nat.reduceEqDiff, Option.some.injEq] at hnext
      subst hnext
      exact step_Q_mod2 m c
  step_none := by
    rintro ⟨a, c⟩ hnext
    have ha_mod : ∃ m, a = 3 * m ∨ a = 3 * m + 1 ∨ a = 3 * m + 2 := ⟨a / 3, by omega⟩
    rcases ha_mod with ⟨m, rfl | rfl | rfl⟩
    · rcases c with _ | c'
      · have hm_mod : ∃ k, m = 3 * k ∨ m = 3 * k + 1 ∨ m = 3 * k + 2 := ⟨m / 3, by omega⟩
        rcases hm_mod with ⟨k, rfl | rfl | rfl⟩
        · have h_m3 : (3 * (3 * k)) % 3 = 0 := by omega
          have h_m9 : (3 * (3 * k)) % 9 = 0 := by omega
          simp [next, h_m3, h_m9] at hnext
        · have h_m3 : (3 * (3 * k + 1)) % 3 = 0 := by omega
          have h_m9 : (3 * (3 * k + 1)) % 9 = 3 := by omega
          simp [next, h_m3, h_m9] at hnext
        · have h_eq : 3 * (3 * k + 2) = 9 * k + 6 := by omega
          rw [encode, h_eq]
          obtain ⟨cfg', hp, hh⟩ := step_Q_mod9_6 k
          exact ⟨cfg', hp.to_star, hh⟩
      · have h_m3 : (3 * m) % 3 = 0 := by omega
        simp [next, h_m3] at hnext
    · have h_m3 : (3 * m + 1) % 3 = 1 := by omega
      simp [next, h_m3] at hnext
    · have h_m3 : (3 * m + 2) % 3 = 2 := by omega
      simp [next, h_m3] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LD_1RC1RE_0LA1LB_0LD1LC_1RF0RA_HHH0RC
