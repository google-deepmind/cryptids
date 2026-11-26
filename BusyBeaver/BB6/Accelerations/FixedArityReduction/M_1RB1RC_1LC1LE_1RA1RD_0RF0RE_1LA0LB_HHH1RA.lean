/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`
(`cryptid_6` (holdout #778, `suspect_89`); see
https://wiki.bbchallenge.org/wiki/1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$C(a, b, c) := 0^\infty\,{<}\mathrm{C}\,1\,(01)^a\,1\,(01)^b\,1\,(01)^c\,0^\infty$$
at $C(1, 3, 1)$ in 48 steps, and every $C(a, b, c)$ advances in `ReachesPlus` either to another
$C(a', b', c')$ or to a halting configuration (when $b = 0$, $c = 0$, and $a = 2k$ is even).

## Collatz-like Acceleration Rules

```text
Consider:
C(a, b, c) = 0^inf <C 1 (01)^a 1 (01)^b 1 (01)^c 0^inf

C(a, b+2, c)  -> C(a+3, b, c)
C(a, 1, c)    -> C(1, a+2, c+2)
C(a, 0, c+1)  -> C(1, a+2, c)
C(2k+1, 0, 0) -> C(1, 3k+6, 1)
C(2k, 0, 0)   -> Halt

Start: C(1, 3, 1), reached after 48 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Helper & Shift Lemmas -/

private theorem append_111_11_pow_1 (s : ListBlank (Fin 2)) (k : ℕ) :
    ListBlank.append [1, 1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1] s)) =
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 2)) s := by
  rw [swap_1_11_pow]
  change ListBlank.append (([1, 1] : List (Fin 2)) ^ 2)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) s) = _
  rw [← ListBlank.append_pow_add, Nat.add_comm]

private theorem append_11_11_pow_11 (k : ℕ) :
    ListBlank.append [1, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
        (ListBlank.append [1, 1] (default : ListBlank (Fin 2)))) =
      ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 2)) default := by
  change ListBlank.append (([1, 1] : List (Fin 2)) ^ 1)
    (ListBlank.append (([1, 1] : List (Fin 2)) ^ k)
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ 1) default)) = _
  rw [← ListBlank.append_pow_add, ← ListBlank.append_pow_add]
  exact congrArg (fun n => ListBlank.append (([1, 1] : List (Fin 2)) ^ n) default) (by omega)

/-- Rightward shift across `(01)^k` in state `C`, writing `(11)^k`. -/
private theorem shift_C_01 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r))
      (Cfg.headRight C (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r) := by
  induction k generalizing l r with
  | zero => exact ReachesStar.refl _ _
  | succ k ih =>
    have h1 :
        ReachesPlus target
          (Cfg.headRight C l (ListBlank.append (([0, 1] : List (Fin 2)) ^ (k + 1)) r))
          (Cfg.headRight C (ListBlank.append [1, 1] l)
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ k) r)) := by
      rw [ListBlank.append_pow_succ]
      bb_steps
    have h2 := ih (ListBlank.append [1, 1] l) r
    have h3 := (h1.trans_star h2).to_star
    have h_pow :
        ListBlank.append (([1, 1] : List (Fin 2)) ^ k) (ListBlank.append [1, 1] l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow] at h3

/-- Leftward shift across `(11)^k` in state `E`, writing `(10)^k`. -/
private theorem shift_E_11 (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target
      (Cfg.headLeft E (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) r)
      (Cfg.headLeft E l (ListBlank.append (([1, 0] : List (Fin 2)) ^ k) r)) := by
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
            (ListBlank.append [1, 0] r)) := by
      bb_steps
    have h2 := ih l (ListBlank.append [1, 0] r)
    have h3 := (h1.trans_star h2).to_star
    have h_pow_l :
        ListBlank.append [1, 1] (ListBlank.append (([1, 1] : List (Fin 2)) ^ k) l) =
          ListBlank.append (([1, 1] : List (Fin 2)) ^ (k + 1)) l := by
      rw [← ListBlank.append_pow_succ]
    have h_pow_r :
        ListBlank.append (([1, 0] : List (Fin 2)) ^ k) (ListBlank.append [1, 0] r) =
          ListBlank.append (([1, 0] : List (Fin 2)) ^ (k + 1)) r := by
      rw [ListBlank.append_append, ← list_pow_succ']
    rwa [h_pow_l, h_pow_r] at h3

/-! ## Canonical Pattern Set -/

/-- Canonical tape pattern
$C(a, b, c) := 0^\infty\,{<}\mathrm{C}\,1\,(01)^a\,1\,(01)^b\,1\,(01)^c\,0^\infty$. -/
def pat_C : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.rep [0, 1] 0
      (.sym 1 (.rep [0, 1] 1 (.sym 1 (.rep [0, 1] 2 .default)))))) }

/-- Closed pattern set for `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_C, .true)]

/-- Configuration $C(a, b, c)$. -/
private def cfg_C (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C default
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
            (ListBlank.append [1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))))

/-- Two-block intermediate configuration
$C_2(d, b) := 0^\infty\,{<}\mathrm{C}\,1\,(01)^d\,1\,(01)^b\,0^\infty$. -/
private def cfg_C2 (d b : ℕ) : Cfg (Fin 2) (Fin 6) :=
  Cfg.headLeft C default
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ d)
        (ListBlank.append [1]
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))))

private theorem eval_pat_C (vars : ℕ → ℕ) :
    evalTapePattern pat_C vars = cfg_C (vars 0) (vars 1) (vars 2) := by
  simp [pat_C, cfg_C, Cfg.headLeft, Cfg.headRight]

private theorem in_ps_C (a b c : ℕ) : IsInPatternSet ps (cfg_C a b c) :=
  ⟨(pat_C, .true), List.Mem.head _,
    fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0,
    (eval_pat_C (fun i => match i with | 0 => a | 1 => b | 2 => c | _ => 0)).symm, trivial⟩

/-! ## Accelerated Transition Rules -/

/-- Rule 1 (`b ≥ 2`): `C(a, b + 2, c) -> C(a + 3, b, c)`. -/
private theorem step_C_b_ge2 (a b c : ℕ) :
    ReachesPlus target (cfg_C a (b + 2) c) (cfg_C (a + 3) b c) := by
  let tail_r :=
    ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
      (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h1 :
      ReachesPlus target (cfg_C a (b + 2) c)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
                (ListBlank.append [1]
                  (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))))) := by
    unfold cfg_C
    bb_steps
  have h2 := shift_C_01 a (ListBlank.append [1, 1] default)
    (ListBlank.append [1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
        (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))
  have h12 := h1.trans_star h2
  have h_split :
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) (default : ListBlank (Fin 2))))) =
        ListBlank.append [1, 0, 1, 0, 1] tail_r := by
    have h_b : b + 2 = 2 + b := by omega
    rw [h_b, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 b]
    rfl
  rw [h_split] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 0, 1, 0, 1] tail_r))
        (Cfg.headLeft E
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1, 1] tail_r)) := by
    bb_steps
  have h123 := h12.trans h3
  have h_l :
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
          (ListBlank.append [1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (a + 2)) (ListBlank.append [1] default) :=
    append_111_11_pow_1 (ListBlank.append [1] default) a
  rw [h_l] at h123
  have h4 := shift_E_11 (a + 2) (ListBlank.append [1] default) (ListBlank.append [1, 1] tail_r)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [1, 1] tail_r)))
        (Cfg.headLeft C default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 3))
            (ListBlank.append [1] (ListBlank.append [1] tail_r)))) := by
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) (a + 2)]
    bb_steps
  have h12345 := h1234.trans h5
  rw [append_10_pow_one (a + 3) (ListBlank.append [1] tail_r)] at h12345
  exact h12345

/-- Rule 2 (`b = 1`): `C(a, 1, c) -> C(1, a + 2, c + 2)`. -/
private theorem step_C_b1 (a c : ℕ) :
    ReachesPlus target (cfg_C a 1 c) (cfg_C 1 (a + 2) (c + 2)) := by
  have h1 :
      ReachesPlus target (cfg_C a 1 c)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [1, 0, 1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_C
    rw [list_pow_one]
    bb_steps
  have h2 := shift_C_01 a (ListBlank.append [1, 1] default)
    (ListBlank.append [1, 0, 1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 0, 1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))
        (Cfg.headRight C
          (ListBlank.append [1, 1, 0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)) := by
    bb_steps
  have h123 := h12.trans h3
  have h4 := shift_C_01 c
    (ListBlank.append [1, 1, 0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
    default
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
            (ListBlank.append [1, 1, 0, 1]
              (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
                (ListBlank.append [1, 1] default))))
          default)
        (Cfg.headLeft E
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
              (ListBlank.append [1, 1, 0, 1]
                (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
                  (ListBlank.append [1, 1] default)))))
          (ListBlank.append [1] default)) := by
    bb_steps
  have h12345 := h1234.trans h5
  have h_l1 :
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ c)
          (ListBlank.append [1, 1, 0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
              (ListBlank.append [1, 1] (default : ListBlank (Fin 2)))))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (c + 2))
          (ListBlank.append [1, 0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a)
              (ListBlank.append [1, 1] default))) :=
    append_111_11_pow_1
      (ListBlank.append [1, 0, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
      c
  rw [h_l1] at h12345
  have h6 := shift_E_11 (c + 2)
    (ListBlank.append [1, 0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
    (ListBlank.append [1] default)
  have h123456 := h12345.trans_star h6
  rw [append_10_pow_one (c + 2) default] at h123456
  have h7 :
      ReachesPlus target
        (Cfg.headLeft E
          (ListBlank.append [1, 0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default)))
        (Cfg.headLeft E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default))) := by
    bb_steps
  have h1234567 := h123456.trans h7
  rw [append_11_11_pow_11 a] at h1234567
  have h8 := shift_E_11 (a + 2) default
    (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default))
  have h12345678 := h1234567.trans_star h8
  have h9 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default))))
        (Cfg.headLeft C default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
                (ListBlank.append [1]
                  (ListBlank.append [1]
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ (c + 2)) default))))))) := by
    rw [list_pow_one]
    bb_steps
  have h123456789 := h12345678.trans h9
  rw [append_10_pow_one (a + 2)] at h123456789
  exact h123456789

/-- Rule 3 (`b = 0, c ≥ 1`): `C(a, 0, c + 1) -> C(1, a + 2, c)`. -/
private theorem step_C_b0_c_ge1 (a c : ℕ) :
    ReachesPlus target (cfg_C a 0 (c + 1)) (cfg_C 1 (a + 2) c) := by
  have h1 :
      ReachesPlus target (cfg_C a 0 (c + 1))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [1, 1, 0, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))) := by
    unfold cfg_C
    rw [list_pow_zero, ListBlank.append_nil, ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) c]
    bb_steps
  have h2 := shift_C_01 a (ListBlank.append [1, 1] default)
    (ListBlank.append [1, 1, 0, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 1, 0, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default)))
        (Cfg.headLeft E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1, 1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))) := by
    bb_steps
  have h123 := h12.trans h3
  rw [append_11_11_pow_11 a] at h123
  have h4 := shift_E_11 (a + 2) default
    (ListBlank.append [1, 1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [1, 1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))
        (Cfg.headLeft C default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
                (ListBlank.append [1]
                  (ListBlank.append [1]
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))))) := by
    rw [list_pow_one]
    bb_steps
  have h12345 := h1234.trans h5
  rw [append_10_pow_one (a + 2)] at h12345
  exact h12345

/-- Entry from `C(a, 0, 0)` into the two-block countdown family `C_2(1, a + 2)`. -/
private theorem step_C_b0_c0_to_C2 (a : ℕ) :
    ReachesPlus target (cfg_C a 0 0) (cfg_C2 1 (a + 2)) := by
  have h1 :
      ReachesPlus target (cfg_C a 0 0)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
            (ListBlank.append [1, 1] default))) := by
    unfold cfg_C
    simp only [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_C_01 a (ListBlank.append [1, 1] default) (ListBlank.append [1, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 1] default))
        (Cfg.headLeft E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ a) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1] default)) := by
    bb_steps
  have h123 := h12.trans h3
  rw [append_11_11_pow_11 a] at h123
  have h4 := shift_E_11 (a + 2) default (ListBlank.append [1] default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
            (ListBlank.append [1] default)))
        (Cfg.headLeft C default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (a + 2))
                (ListBlank.append [1] default))))) := by
    rw [list_pow_one]
    bb_steps
  have h12345 := h1234.trans h5
  rw [append_10_pow_one (a + 2) default] at h12345
  exact h12345

/-- Single step in the two-block countdown family: `C_2(d, b + 2) -> C_2(d + 3, b)`. -/
private theorem step_C2_b_ge2 (d b : ℕ) :
    ReachesPlus target (cfg_C2 d (b + 2)) (cfg_C2 (d + 3) b) := by
  let tail_r := ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default
  have h1 :
      ReachesPlus target (cfg_C2 d (b + 2))
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [1]
              (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default)))) := by
    unfold cfg_C2
    bb_steps
  have h2 := shift_C_01 d (ListBlank.append [1, 1] default)
    (ListBlank.append [1] (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) default))
  have h12 := h1.trans_star h2
  have h_split :
      ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ (b + 2)) (default : ListBlank (Fin 2))) =
        ListBlank.append [1, 0, 1, 0, 1] tail_r := by
    have h_b : b + 2 = 2 + b := by omega
    rw [h_b, ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 b]
    rfl
  rw [h_split] at h12
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 0, 1, 0, 1] tail_r))
        (Cfg.headLeft E
          (ListBlank.append [1, 1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1, 1] tail_r)) := by
    bb_steps
  have h123 := h12.trans h3
  have h_l :
      ListBlank.append [1, 1, 1]
        (ListBlank.append (([1, 1] : List (Fin 2)) ^ d)
          (ListBlank.append [1, 1] (default : ListBlank (Fin 2)))) =
        ListBlank.append (([1, 1] : List (Fin 2)) ^ (d + 2)) (ListBlank.append [1] default) :=
    append_111_11_pow_1 (ListBlank.append [1] default) d
  rw [h_l] at h123
  have h4 := shift_E_11 (d + 2) (ListBlank.append [1] default) (ListBlank.append [1, 1] tail_r)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E (ListBlank.append [1] default)
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 2))
            (ListBlank.append [1, 1] tail_r)))
        (Cfg.headLeft C default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 3))
            (ListBlank.append [1] (ListBlank.append [1] tail_r)))) := by
    rw [ListBlank.append_pow_succ ([1, 0] : List (Fin 2)) (d + 2)]
    bb_steps
  have h12345 := h1234.trans h5
  rw [append_10_pow_one (d + 3) (ListBlank.append [1] tail_r)] at h12345
  exact h12345

/-- Multi-step countdown in `C_2`: `C_2(d, 2k + r) ->* C_2(d + 3k, r)`. -/
private theorem countdown_C2 (k d r : ℕ) :
    ReachesStar target (cfg_C2 d (2 * k + r)) (cfg_C2 (d + 3 * k) r) := by
  induction k generalizing d with
  | zero =>
    have h_z : 2 * 0 + r = r := by omega
    have h_d : d + 3 * 0 = d := by omega
    rw [h_z, h_d]
  | succ k ih =>
    have h_split : 2 * (k + 1) + r = (2 * k + r) + 2 := by omega
    rw [h_split]
    have h1 := (step_C2_b_ge2 d (2 * k + r)).to_star
    have h2 := ih (d + 3)
    have h12 := h1.trans h2
    have h_d : (d + 3) + 3 * k = d + 3 * (k + 1) := by omega
    rwa [h_d] at h12

/-- Exit from `C_2(d, 1)` back into `C(1, d + 2, 1)`. -/
private theorem step_C2_b1 (d : ℕ) :
    ReachesPlus target (cfg_C2 d 1) (cfg_C 1 (d + 2) 1) := by
  have h1 :
      ReachesPlus target (cfg_C2 d 1)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [1, 0, 1] default))) := by
    unfold cfg_C2
    rw [list_pow_one]
    bb_steps
  have h2 := shift_C_01 d (ListBlank.append [1, 1] default) (ListBlank.append [1, 0, 1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default))
          (ListBlank.append [1, 0, 1] default))
        (Cfg.headLeft E
          (ListBlank.append [1, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default)))
          (ListBlank.append [1, 1, 0, 1] default)) := by
    bb_steps
  have h123 := h12.trans h3
  rw [append_11_11_pow_11 d] at h123
  have h4 := shift_E_11 (d + 2) default (ListBlank.append [1, 1, 0, 1] default)
  have h1234 := h123.trans_star h4
  have h5 :
      ReachesPlus target
        (Cfg.headLeft E default
          (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 2))
            (ListBlank.append [1, 1, 0, 1] default)))
        (Cfg.headLeft C default
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1)
              (ListBlank.append (([1, 0] : List (Fin 2)) ^ (d + 2))
                (ListBlank.append [1]
                  (ListBlank.append [1]
                    (ListBlank.append (([0, 1] : List (Fin 2)) ^ 1) default))))))) := by
    rw [list_pow_one]
    bb_steps
  have h12345 := h1234.trans h5
  rw [append_10_pow_one (d + 2)] at h12345
  exact h12345

/-- Halting transition from `C_2(d, 0)`. -/
private theorem step_C2_b0_halt (d : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C2 d 0) cfg' ∧ (step target cfg').isNone := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [0, 1]
      (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default)))
    default, ?_, by bb_halt⟩
  have h1 :
      ReachesPlus target (cfg_C2 d 0)
        (Cfg.headRight C (ListBlank.append [1, 1] default)
          (ListBlank.append (([0, 1] : List (Fin 2)) ^ d)
            (ListBlank.append [1] default))) := by
    unfold cfg_C2
    rw [list_pow_zero, ListBlank.append_nil]
    bb_steps
  have h2 := shift_C_01 d (ListBlank.append [1, 1] default) (ListBlank.append [1] default)
  have h12 := h1.trans_star h2
  have h3 :
      ReachesPlus target
        (Cfg.headRight C
          (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default))
          (ListBlank.append [1] default))
        (Cfg.headRight F
          (ListBlank.append [0, 1]
            (ListBlank.append (([1, 1] : List (Fin 2)) ^ d) (ListBlank.append [1, 1] default)))
          default) := by
    bb_steps
  exact h12.trans h3

/-- Rule 4 (`b = 0, c = 0, a = 2k + 1` odd): `C(2k + 1, 0, 0) -> C(1, 3k + 6, 1)`. -/
private theorem step_C_b0_c0_odd (k : ℕ) :
    ReachesPlus target (cfg_C (2 * k + 1) 0 0) (cfg_C 1 (3 * k + 6) 1) := by
  have h_enter := step_C_b0_c0_to_C2 (2 * k + 1)
  have h_eq : (2 * k + 1) + 2 = 2 * (k + 1) + 1 := by omega
  rw [h_eq] at h_enter
  have h_loop := countdown_C2 (k + 1) 1 1
  have h_exit := step_C2_b1 (1 + 3 * (k + 1))
  have h_tot := (h_enter.trans_star h_loop).trans h_exit
  have h_idx : (1 + 3 * (k + 1)) + 2 = 3 * k + 6 := by omega
  rwa [h_idx] at h_tot

/-- Rule 5 (`b = 0, c = 0, a = 2k` even): `C(2k, 0, 0)` halts. -/
private theorem step_C_b0_c0_even_halt (k : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C (2 * k) 0 0) cfg' ∧ (step target cfg').isNone := by
  have h_enter := step_C_b0_c0_to_C2 (2 * k)
  have h_eq : 2 * k + 2 = 2 * (k + 1) + 0 := by omega
  rw [h_eq] at h_enter
  have h_loop := countdown_C2 (k + 1) 1 0
  obtain ⟨cfg', h_halt_step, h_halt⟩ := step_C2_b0_halt (1 + 3 * (k + 1))
  exact ⟨cfg', (h_enter.trans_star h_loop).trans h_halt_step, h_halt⟩

private theorem step_C (a b c : ℕ) :
    ∃ cfg', ReachesPlus target (cfg_C a b c) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases b with _ | _ | b'
  · rcases c with _ | c'
    · rcases nat_even_or_odd_two_mul a with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · obtain ⟨cfg', h_plus, h_halt⟩ := step_C_b0_c0_even_halt k
        exact ⟨cfg', h_plus, Or.inr h_halt⟩
      · exact ⟨cfg_C 1 (3 * k + 6) 1, step_C_b0_c0_odd k,
          Or.inl (in_ps_C 1 (3 * k + 6) 1)⟩
    · exact ⟨cfg_C 1 (a + 2) c', step_C_b0_c_ge1 a c', Or.inl (in_ps_C 1 (a + 2) c')⟩
  · exact ⟨cfg_C 1 (a + 2) (c + 2), step_C_b1 a c, Or.inl (in_ps_C 1 (a + 2) (c + 2))⟩
  · exact ⟨cfg_C (a + 3) b' c, step_C_b_ge2 a b' c, Or.inl (in_ps_C (a + 3) b' c)⟩

private theorem init_reaches_start : ReachesStar target (init []) (cfg_C 1 3 1) := by
  have h_init : ReachesPlus target (init []) (cfg_C 1 3 1) := by
    unfold cfg_C
    have h3 : (([0, 1] : List (Fin 2)) ^ 3) = [0, 1, 0, 1, 0, 1] := rfl
    rw [list_pow_one, h3]
    bb_steps
  exact h_init.to_star

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_C 1 3 1, init_reaches_start, in_ps_C 1 3 1⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl
  rw [eval_pat_C]
  exact step_C (vars 0) (vars 1) (vars 2)

/-- `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_---1RA`. -/
inductive State where
  /-- $C(a, b, c) := 0^\infty\,{<}\mathrm{C}\,1\,(01)^a\,1\,(01)^b\,1\,(01)^c\,0^\infty$. -/
  | C (a b c : ℕ)

/-- Initial symbolic state $C(1, 3, 1)$, reached after 48 raw TM steps. -/
def start : State := .C 1 3 1

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .C a b c =>
    Cfg.headLeft SixState.C default
      (ListBlank.append [1]
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.append [1]
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b)
              (ListBlank.append [1]
                (ListBlank.append (([0, 1] : List (Fin 2)) ^ c) default))))))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .C a 0 0 => if a % 2 = 1 then some (.C 1 (3 * (a / 2) + 6) 1) else none
  | .C a 0 (c + 1) => some (.C 1 (a + 2) c)
  | .C a 1 c => some (.C 1 (a + 2) (c + 2))
  | .C a (b + 2) c => some (.C (a + 3) b c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_start
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases b with _ | _ | b'
    · rcases c with _ | c'
      · simp only [next] at hnext
        split_ifs at hnext with h_odd
        simp only [Option.some.injEq] at hnext
        subst hnext
        have h := step_C_b0_c0_odd (a / 2)
        have ha : 2 * (a / 2) + 1 = a := by omega
        rwa [ha] at h
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact step_C_b0_c_ge1 a c'
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_C_b1 a c
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact step_C_b_ge2 a b' c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases b with _ | _ | b'
    · rcases c with _ | c'
      · simp only [next] at hnext
        split_ifs at hnext with h_odd
        have ha : 2 * (a / 2) = a := by omega
        obtain ⟨cfg', hp, hh⟩ := step_C_b0_c0_even_halt (a / 2)
        rw [ha] at hp
        exact ⟨cfg', hp.to_star, hh⟩
      · simp [next] at hnext
    · simp [next] at hnext
    · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1RC_1LC1LE_1RA1RD_0RF0RE_1LA0LB_HHH1RA
