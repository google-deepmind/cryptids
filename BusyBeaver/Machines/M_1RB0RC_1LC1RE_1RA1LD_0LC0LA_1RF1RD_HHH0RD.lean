/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD`

## Collatz-like Acceleration Rules

The canonical configuration family is parameterized by left prefix
$l \in \{0^\infty, 0^\infty 1^3 0\}$ and non-negative integers $k, j, c \ge 0$:
$$S(l, k, j, c) \equiv l \, 1^k \; \text{\{\{D\}\}>} \; 1^2 \, (01)^j \, 1^c \, 0^\infty$$
together with the intermediate scan family:
$$C_{001}(l, a, b) \equiv l \; \text{\{\{C\}\}>} \; 001 \, (01)^a \, 1^b \, 0^\infty$$

Starting from the blank tape, the machine reaches $S(0^\infty, 2, 0, 0)$. The accelerated rules are:

```text
S(l, k + 3, j, c + 1) -> S(l, k, j + 2, c)
S(l, k + 2, j, 0)     -> S(l, k, 0, 2j + 5)
S(0^inf, 2, j, c + 1) -> C_001(0^inf, j + 2, c)
S(0^inf, 1, j, c + 1) -> C_001(0^inf, j + 1, c)
S(0^inf, 1, j, 0)     -> S(0^inf, 0, 0, 2j + 3)
S(0^inf, 0, j + 1, c) -> C_001(0^inf 1^3 0, j, c)
S(0^inf, 0, 0, c)     -> C_001(0^inf, 0, c + 2)

C_001(l, 2m, 0)       -> Halt
C_001(l, 2m, 1)       -> S(l, 4m + 2, 0, 0)
C_001(l, 2m, 2)       -> S(l, 4m + 2, 0, 3)
C_001(l, 2m, c + 3)   -> S(l, 4m + 4, 0, c)
C_001(l, 2m + 1, 0)   -> S(l, 4m + 4, 0, 1)
C_001(l, 2m + 1, c+1) -> S(l, 4m + 3, 0, c + 1)
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Shift Lemmas -/

private theorem shift_C_right (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) [target]⊢*
    ((l <+ ([0, 1] : List (Fin 2)) ^ k) {{C}}> r) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ k +> r)))
        [target]⊢*
        ((l <+ [0, 1]) {{C}}> (([0, 1] : List (Fin 2)) ^ k +> r)) := by
      bb_steps
    have h2 := ih (l <+ [0, 1]) r
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_DC_left (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> r)) [target]⊢*
    (l {{D}}> ([0] +> (([1, 0] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, ← ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{D}}> ([0] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{D}}> ([0] +> ([1, 0] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 0] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_C_left_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> r)) [target]⊢*
    (l {{C}}> ([1] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ k ih =>
    rw [list_pow_succ, ← ListBlank.append_append]
    have h1 : (((l <+ ([1, 0] : List (Fin 2)) ^ k) <+ [1, 0]) {{C}}> ([1] +> r))
        [target]⊢*
        ((l <+ ([1, 0] : List (Fin 2)) ^ k) {{C}}> ([1] +> ([1, 1] +> r))) := by
      bb_steps
    have h2 := ih l (([1, 1] : List (Fin 2)) +> r)
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem shift_E_0101 (m : Nat) (l r : ListBlank (Fin 2)) :
    (l {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) [target]⊢*
    ((l <+ ([1, 1, 1, 1] : List (Fin 2)) ^ m) {{E}}> r) := by
  induction m generalizing l r with
  | zero =>
    simp only [list_pow_zero, ListBlank.append_nil]
    exact ReachesStar.refl _ _
  | succ m ih =>
    rw [ListBlank.append_pow_succ]
    have h1 : (l {{E}}> ([0, 1, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
        [target]⊢*
        ((l <+ [1, 1, 1, 1]) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
      bb_steps
    have h2 := ih (l <+ [1, 1, 1, 1]) r
    rw [ListBlank.append_pow_succ'] at h2
    exact ReachesStar.trans h1 h2

private theorem one_pow_four_mul (k : ℕ) :
    ([1, 1, 1, 1] : List (Fin 2)) ^ k = ([1] : List (Fin 2)) ^ (4 * k) :=
  (list_pow_mul [1] 4 k).symm

private theorem zero_one_pow_two_mul (m : ℕ) :
    ([0, 1] : List (Fin 2)) ^ (2 * m) = ([0, 1, 0, 1] : List (Fin 2)) ^ m :=
  list_pow_mul [0, 1] 2 m

/-! ## Canonical Pattern Set -/

private def cfg_D (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  (default : ListBlank (Fin 2)) {{D}}> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +>
      default))

abbrev cfg_A (l : ListBlank (Fin 2)) (k j c : Nat) : Cfg (Fin 2) (Fin 6) :=
  (l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
    ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> (([1] : List (Fin 2)) ^ c +> default)))

abbrev l_hat : ListBlank (Fin 2) :=
  ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]

abbrev l_ones3 : ListBlank (Fin 2) :=
  (default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3

abbrev cfg_C001 (l : ListBlank (Fin 2)) (a b : Nat) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +> default)))

def pat_A : TapePattern (Fin 2) (Fin 6) :=
  { left  := .rep [1] 0 (.rep [0, 1, 1, 1] 1 .default)
    head  := some D
    right := .sym 1 (.sym 1 (.rep [0, 1] 2 (.rep [1] 3 .default))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_A, .not (.ge_const 1 2))]

private theorem eval_pat_A (vars : Nat -> Nat) :
    evalTapePattern pat_A vars =
    cfg_A (default <+ ([0, 1, 1, 1] : List (Fin 2)) ^ (vars 1)) (vars 0) (vars 2) (vars 3) := rfl

private theorem in_ps_S_def (k j c : Nat) : IsInPatternSet ps (cfg_A default k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 0 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]

private theorem in_ps_S_hat (k j c : Nat) : IsInPatternSet ps (cfg_A l_hat k j c) := by
  refine ⟨(pat_A, .not (.ge_const 1 2)), List.Mem.head _,
    fun i => match i with | 0 => k | 1 => 1 | 2 => j | 3 => c | _ => 0, rfl, ?_⟩
  simp [evalVarCond]

private theorem in_ps_S_ones3 (k j c : Nat) :
    IsInPatternSet ps (cfg_A (default <+ ([1] : List (Fin 2)) ^ 3) k j c) := by
  unfold cfg_A
  rw [← ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 k]
  exact in_ps_S_def (3 + k) j c

/-! ## Accelerated Transition Rules -/

private theorem step_C001_even_to_E (l : ListBlank (Fin 2)) (m : Nat) (r : ListBlank (Fin 2)) :
    (l {{C}}> ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (2 * m) +> r))) [target]⊢⁺
    ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> r) := by
  rw [zero_one_pow_two_mul m]
  have h1 : (l {{C}}> ([0, 0, 1] +> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ 3) {{E}}> (([0, 1, 0, 1] : List (Fin 2)) ^ m +> r)) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  have h2 := shift_E_0101 m (l <+ ([1] : List (Fin 2)) ^ 3) r
  rw [one_pow_four_mul m, ← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) 3 (4 * m)] at h2
  have hm : 3 + 4 * m = 4 * m + 3 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans_star h1 h2

private theorem step_C001_even_b0_halt (l : ListBlank (Fin 2)) (m : Nat) :
    ∃ cfg', ((cfg_C001 l (2 * m) 0) [target]⊢⁺ cfg') ∧ (step target cfg').isNone := by
  refine ⟨(((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default), ?_,
    by rfl⟩
  unfold cfg_C001
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m default
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> default)
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ [1]) {{F}}> default) := by
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b1 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 1) [target]⊢⁺ (cfg_A l (4 * m + 2) 0 0) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 1 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 1 +> default))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}> ([1, 1] +> default)) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b2 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m) 2) [target]⊢⁺ (cfg_A l (4 * m + 2) 0 3) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 2 +> default)
  have hm : 4 * m + 3 = (4 * m + 2) + 1 := by omega
  rw [hm, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 2) 1] at h1
  have h2 : (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{E}}>
      (([1] : List (Fin 2)) ^ 2 +> default))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_even_b3 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m) (c + 3)) [target]⊢⁺ (cfg_A l (4 * m + 4) 0 c) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have hc : c + 3 = 3 + c := by omega
  rw [hc, ListBlank.append_pow_add ([1] : List (Fin 2)) 3 c default]
  have h1 := step_C001_even_to_E l m (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +>
      default))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([1] : List (Fin 2)) ^ 3 +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ c +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2

private theorem step_C001_odd_b0 (l : ListBlank (Fin 2)) (m : Nat) :
    (cfg_C001 l (2 * m + 1) 0) [target]⊢⁺ (cfg_A l (4 * m + 4) 0 1) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (2 * m) 1 default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> default)
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}> (([0, 1] : List (Fin 2)) ^ 1 +>
      default))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ 1 +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (4 * m + 3) 1] at h2
  have hm : (4 * m + 3) + 1 = 4 * m + 4 := by omega
  rw [hm] at h2
  exact ReachesPlus.trans h1 h2

private theorem step_C001_odd_b1 (l : ListBlank (Fin 2)) (m c : Nat) :
    (cfg_C001 l (2 * m + 1) (c + 1)) [target]⊢⁺ (cfg_A l (4 * m + 3) 0 (c + 1)) := by
  unfold cfg_C001 cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_add ([0, 1] : List (Fin 2)) (2 * m) 1 (([1] : List (Fin 2)) ^ (c + 1) +>
    default),
    ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 := step_C001_even_to_E l m (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +>
      (([1] : List (Fin 2)) ^ c +> default)))
  have h2 : ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{E}}>
      (([0, 1] : List (Fin 2)) ^ 1 +> ([1] +> (([1] : List (Fin 2)) ^ c +> default))))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ (4 * m + 3)) {{D}}>
        ([1, 1] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans h1 h2

private theorem step_C001_all (l : ListBlank (Fin 2))
    (hl : ∀ k j c, IsInPatternSet ps (cfg_A l k j c)) (a b : Nat) :
    ∃ cfg', ((cfg_C001 l a b) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have ha : ∃ m, a = 2 * m ∨ a = 2 * m + 1 := ⟨a / 2, by omega⟩
  rcases ha with ⟨m, rfl | rfl⟩
  · rcases b with _ | _ | _ | c
    · obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l m
      exact ⟨cfg', h_plus, Or.inr h_halt⟩
    · exact ⟨_, step_C001_even_b1 l m, Or.inl (hl (4 * m + 2) 0 0)⟩
    · exact ⟨_, step_C001_even_b2 l m, Or.inl (hl (4 * m + 2) 0 3)⟩
    · exact ⟨_, step_C001_even_b3 l m c, Or.inl (hl (4 * m + 4) 0 c)⟩
  · rcases b with _ | c
    · exact ⟨_, step_C001_odd_b0 l m, Or.inl (hl (4 * m + 4) 0 1)⟩
    · exact ⟨_, step_C001_odd_b1 l m c, Or.inl (hl (4 * m + 3) 0 (c + 1))⟩

private theorem step_D_succ_to_cfg_C001 (a b : Nat) :
    (cfg_D (a + 1) b) [target]⊢⁺ (cfg_C001 default a b) := by
  unfold cfg_D cfg_C001
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) a (([1] : List (Fin 2)) ^ b +> default)]
  bb_steps

private theorem step_S_def_k0_jsucc_to_cfg_C001 (j c : Nat) :
    (cfg_A default 0 (j + 1) c) [target]⊢⁺ (cfg_C001 l_hat j c) := by
  unfold cfg_A cfg_C001 l_hat
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_S_hat_k0_jsucc (j c : Nat) :
    (cfg_A l_hat 0 (j + 1) c) [target]⊢⁺ (cfg_A default 6 (j + 1) c) := by
  unfold cfg_A l_hat
  simp only [list_pow_zero, ListBlank.append_nil]
  rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j (([1] : List (Fin 2)) ^ c +> default)]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_S_hat_k1_c0 (j : Nat) :
    (cfg_A l_hat 1 j 0) [target]⊢⁺ (cfg_A default 1 1 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      ((l_hat <+ [0]) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0]) default
  rw [append_01_pow_zero (j + 1) l_hat] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      [target]⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 (j + 1) l_hat (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul (j + 1),
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 1)) 3 default] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (l_hat {{C}}> ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 1 +> (([1] : List (Fin 2)) ^ (2 * j + 5) +>
      default)))) := by
    unfold l_hat
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_hat_k1_csucc_to_cfg_C001 (j c : Nat) :
    (cfg_A l_hat 1 j (c + 1)) [target]⊢⁺
    (cfg_C001 (default <+ ([1] : List (Fin 2)) ^ 3) (j + 1) c) := by
  unfold cfg_A cfg_C001
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : ((l_hat <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((l_hat <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) (l_hat <+ [0])
      ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) l_hat] at h2
  have h3 : (((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((l_hat <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) l_hat ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (l_hat {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((default <+ ([1] : List (Fin 2)) ^ 3) {{C}}>
        ([0, 0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))) := by
    unfold l_hat
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_stride3 (l : ListBlank (Fin 2)) (k j c : Nat) :
    (cfg_A l (k + 3) j (c + 1)) [target]⊢⁺ (cfg_A l k (j + 2) c) := by
  unfold cfg_A
  have hk : k + 3 = (k + 2) + 1 := by omega
  rw [hk, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (k + 2) 1,
    ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 2))] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 2))
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default),
    ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) k 2] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_c0_k2 (l : ListBlank (Fin 2)) (k j : Nat) :
    (cfg_A l (k + 2) j 0) [target]⊢⁺ (cfg_A l k 0 (2 * j + 5)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have hk : k + 2 = (k + 1) + 1 := by omega
  rw [hk, ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) (k + 1) 1]
  have h1 : (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) ((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ [0]) default
  rw [append_01_pow_zero (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 1))] at h2
  have h3 : ((((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}> default)
      [target]⊢⁺
      (((l <+ ([1] : List (Fin 2)) ^ (k + 1)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 (j + 1) (l <+ ([1] : List (Fin 2)) ^ (k + 1))
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul (j + 1),
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * (j + 1)) 3 default,
    ListBlank.append_pow_add_rev l ([1] : List (Fin 2)) k 1] at h4
  have hj : 2 * (j + 1) + 3 = 2 * j + 5 := by omega
  rw [hj] at h4
  have h5 : (((l <+ ([1] : List (Fin 2)) ^ k) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default)))
      [target]⊢⁺
      ((l <+ ([1] : List (Fin 2)) ^ k) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 5) +> default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_k1_c0 (j : Nat) :
    (cfg_A default 1 j 0) [target]⊢⁺ (cfg_A default 0 0 (2 * j + 3)) := by
  unfold cfg_A
  simp only [list_pow_zero, ListBlank.append_nil]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}> ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +>
      default))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j default] at h1
  have h2 := shift_C_right (j + 1) default default
  have h12 := ReachesPlus.trans_star h1 h2
  have hj1 : j + 1 = 1 + j := by omega
  rw [hj1, ListBlank.append_pow_add_rev default ([0, 1] : List (Fin 2)) 1 j] at h12
  change (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> default))) [target]⊢⁺
      ((((default <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) <+ ([0,
      1] : List (Fin 2)) ^ j) {{C}}> default) at h12
  rw [append_01_pow_zero j (default <+ ([1] : List (Fin 2)) ^ 1)] at h12
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) <+ [0]) {{C}}> default)
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ j) {{C}}>
        ([1] +> (([1] : List (Fin 2)) ^ 3 +> default))) := by
    bb_steps
  have h4 := shift_C_left_10 j ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
      (([1] : List (Fin 2)) ^ 3 +> default)
  rw [one_pow_two_mul j,
    ← ListBlank.append_pow_add ([1] : List (Fin 2)) (2 * j) 3 default] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default)))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        ([1, 1] +> (([1] : List (Fin 2)) ^ (2 * j + 3) +> default))) := by
    bb_steps
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans h12 h3) h4) h5

private theorem step_S_k1_csucc (j c : Nat) :
    (cfg_A default 1 j (c + 1)) [target]⊢⁺ (cfg_D (j + 2) c) := by
  unfold cfg_A cfg_D
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [default_append_01_pow (j + 1)] at h2
  have h3 : ((((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) default ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : ([0] : List (Fin 2)) +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))) =
      ([0, 1] : List (Fin 2)) ^ (j + 2) +> (([1] : List (Fin 2)) ^ c +> default) := by
    rw [ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) (j + 1)]
    rfl
  rw [h5] at h4
  exact ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star h1 h2) h3) h4

private theorem step_S_k2_csucc (j c : Nat) :
    (cfg_A default 2 j (c + 1)) [target]⊢⁺ (cfg_D (j + 3) c) := by
  unfold cfg_A cfg_D
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)]
    at h2
  have h3 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) <+ ([1,
      0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1) ((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      ((default : ListBlank (Fin 2)) {{D}}>
        (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default)))) := by
    dsimp [ListBlank.append, list_pow_succ]
    bb_steps
  rw [← ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_S_k0_j0 (c : Nat) :
    (cfg_A default 0 0 c) [target]⊢⁺ (cfg_D 1 (c + 2)) := by
  unfold cfg_A cfg_D
  rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

private theorem step_SL_hat_k2_csucc (j c : Nat) :
    (cfg_A l_hat 2 j (c + 1)) [target]⊢⁺ (cfg_A default 1 (j + 3) c) := by
  unfold cfg_A l_hat
  rw [ListBlank.append_pow_succ ([1] : List (Fin 2)) c default]
  have h1 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 2) {{D}}>
      ([1, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+ [0]) {{C}}>
        ([0, 1] +> (([0, 1] : List (Fin 2)) ^ j +> ([1] +> (([1] : List (Fin 2)) ^ c +>
      default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_succ ([0, 1] : List (Fin 2)) j ([1] +> (([1] : List (Fin 2)) ^ c +>
    default))] at h1
  have h2 := shift_C_right (j + 1)
    (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2))
      ^ 1) <+ [0])
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_01_pow_zero (j + 1)
    ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+
      ([1] : List (Fin 2)) ^ 1)] at h2
  have h3 : ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) <+
      ([1, 0] : List (Fin 2)) ^ (j + 1) <+ [0]) {{C}}>
      ([1] +> (([1] : List (Fin 2)) ^ c +> default)))
      [target]⊢⁺
      ((((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin
      2)) ^ 1) <+
        ([1, 0] : List (Fin 2)) ^ (j + 1)) {{D}}>
        ([0] +> ([1] +> (([1] : List (Fin 2)) ^ c +> default)))) := by
    bb_steps
  have h4 := shift_DC_left (j + 1)
    ((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List (Fin 2)) ^
      1)
    ([1] +> (([1] : List (Fin 2)) ^ c +> default))
  rw [append_10_pow_one (j + 1) (([1] : List (Fin 2)) ^ c +> default)] at h4
  have h5 : (((((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 3) <+ [0]) <+ ([1] : List
      (Fin 2)) ^ 1) {{D}}>
      ([0] +> ([1] +> (([0, 1] : List (Fin 2)) ^ (j + 1) +> (([1] : List (Fin 2)) ^ c +>
      default)))))
      [target]⊢⁺
      (((default : ListBlank (Fin 2)) <+ ([1] : List (Fin 2)) ^ 1) {{D}}>
        ([1, 1] +> (([0, 1] : List (Fin 2)) ^ 2 +> (([0, 1] : List (Fin 2)) ^ (j + 1) +>
      (([1] : List (Fin 2)) ^ c +> default))))) := by
    bb_steps
  rw [← ListBlank.append_pow_add ([0, 1] : List (Fin 2)) 2 (j + 1) (([1] : List (Fin 2)) ^ c +>
    default)] at h5
  have hj : 2 + (j + 1) = j + 3 := by omega
  rw [hj] at h5
  exact ReachesPlus.trans (ReachesPlus.trans_star (ReachesPlus.trans (ReachesPlus.trans_star
    h1 h2) h3) h4) h5

private theorem step_SL_hat_k0_j0 (c : Nat) :
    (cfg_A l_hat 0 0 c) [target]⊢⁺ (cfg_A default 2 0 (c + 2)) := by
  unfold cfg_A l_hat
  rw [Nat.add_comm c 2, ListBlank.append_pow_add ([1] : List (Fin 2)) 2 c default]
  dsimp [ListBlank.append, list_pow_succ]
  bb_steps

/-! ## Blank-Tape Entry and Closure -/

private theorem init_to_cfg_D : (init []) [target]⊢⁺ (cfg_D 1 1) := by
  unfold init cfg_D
  simp only [Tape.mk₁]
  bb_steps

private theorem init_reaches_S : (init []) [target]⊢* (cfg_A default 2 0 0) :=
  ReachesPlus.to_star
    (ReachesPlus.trans (ReachesPlus.trans init_to_cfg_D (step_D_succ_to_cfg_C001 0 1))
      (step_C001_even_b1 default 0))

private theorem step_S_def_all (k j c : Nat) :
    ∃ cfg', ((cfg_A default k j c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · have h12 := ReachesPlus.trans (step_S_k0_j0 c) (step_D_succ_to_cfg_C001 0 (c + 2))
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def 0 (c + 2)
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
    · have h1 := step_S_def_k0_jsucc_to_cfg_C001 j' c
      obtain ⟨cfg', h2, h_end⟩ := step_C001_all l_hat in_ps_S_hat j' c
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_k1_c0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 3))⟩
    · have h12 := ReachesPlus.trans (step_S_k1_csucc j c') (step_D_succ_to_cfg_C001 (j + 1) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default 0 j, Or.inl (in_ps_S_def 0 0 (2 * j + 5))⟩
    · have h12 := ReachesPlus.trans (step_S_k2_csucc j c') (step_D_succ_to_cfg_C001 (j + 2) c')
      obtain ⟨cfg', h3, h_end⟩ := step_C001_all default in_ps_S_def (j + 2) c'
      exact ⟨cfg', ReachesPlus.trans h12 h3, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 default (k' + 1) j, Or.inl (in_ps_S_def (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 default k' j c', Or.inl (in_ps_S_def k' (j + 2) c')⟩

private theorem step_S_hat_all (k j c : Nat) :
    ∃ cfg', ((cfg_A l_hat k j c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases k with _ | _ | _ | k'
  · rcases j with _ | j'
    · exact ⟨_, step_SL_hat_k0_j0 c, Or.inl (in_ps_S_def 2 0 (c + 2))⟩
    · exact ⟨_, step_S_hat_k0_jsucc j' c, Or.inl (in_ps_S_def 6 (j' + 1) c)⟩
  · rcases c with _ | c'
    · exact ⟨_, step_S_hat_k1_c0 j, Or.inl (in_ps_S_def 1 1 (2 * j + 5))⟩
    · have h1 := step_S_hat_k1_csucc_to_cfg_C001 j c'
      obtain ⟨cfg', h2,
      h_end⟩ := step_C001_all (default <+ ([1] : List (Fin 2)) ^ 3) in_ps_S_ones3 (j + 1) c'
      exact ⟨cfg', ReachesPlus.trans h1 h2, h_end⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat 0 j, Or.inl (in_ps_S_hat 0 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_hat_k2_csucc j c', Or.inl (in_ps_S_def 1 (j + 3) c')⟩
  · rcases c with _ | c'
    · exact ⟨_, step_SL_c0_k2 l_hat (k' + 1) j, Or.inl (in_ps_S_hat (k' + 1) 0 (2 * j + 5))⟩
    · exact ⟨_, step_SL_stride3 l_hat k' j c', Or.inl (in_ps_S_hat k' (j + 2) c')⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨⟨cfg_A default 2 0 0, init_reaches_S, in_ps_S_def 2 0 0⟩, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, h_cond⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · rw [eval_pat_A]
    change ¬ (vars 1 >= 2) at h_cond
    have hp : vars 1 = 0 ∨ vars 1 = 1 := by omega
    rcases hp with h0 | h1
    · rw [h0]
      exact step_S_def_all (vars 0) (vars 2) (vars 3)
    · rw [h1]
      exact step_S_hat_all (vars 0) (vars 2) (vars 3)
  · nomatch h_mem

/-- `1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_---0RD` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

private theorem cfg_A_ones3_eq (k j c : Nat) :
    cfg_A l_ones3 k j c = cfg_A default (3 + k) j c := by
  unfold cfg_A l_ones3
  rw [← ListBlank.append_pow_add_rev default ([1] : List (Fin 2)) 3 k]

inductive State where
  | S_def (k j c : ℕ)
  | S_hat (k j c : ℕ)
  | C_def (a b : ℕ)
  | C_hat (a b : ℕ)
  | C_ones3 (a b : ℕ)

def start : State := .S_def 2 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .S_def k j c => cfg_A default k j c
  | .S_hat k j c => cfg_A l_hat k j c
  | .C_def a b => cfg_C001 default a b
  | .C_hat a b => cfg_C001 l_hat a b
  | .C_ones3 a b => cfg_C001 l_ones3 a b

def next : State → Option State
  | .S_def 0 0 c => some (.C_def 0 (c + 2))
  | .S_def 0 (j + 1) c => some (.C_hat j c)
  | .S_def 1 j 0 => some (.S_def 0 0 (2 * j + 3))
  | .S_def 1 j (c + 1) => some (.C_def (j + 1) c)
  | .S_def 2 j 0 => some (.S_def 0 0 (2 * j + 5))
  | .S_def 2 j (c + 1) => some (.C_def (j + 2) c)
  | .S_def (k + 3) j 0 => some (.S_def (k + 1) 0 (2 * j + 5))
  | .S_def (k + 3) j (c + 1) => some (.S_def k (j + 2) c)
  | .S_hat 0 0 c => some (.S_def 2 0 (c + 2))
  | .S_hat 0 (j + 1) c => some (.S_def 6 (j + 1) c)
  | .S_hat 1 j 0 => some (.S_def 1 1 (2 * j + 5))
  | .S_hat 1 j (c + 1) => some (.C_ones3 (j + 1) c)
  | .S_hat 2 j 0 => some (.S_hat 0 0 (2 * j + 5))
  | .S_hat 2 j (c + 1) => some (.S_def 1 (j + 3) c)
  | .S_hat (k + 3) j 0 => some (.S_hat (k + 1) 0 (2 * j + 5))
  | .S_hat (k + 3) j (c + 1) => some (.S_hat k (j + 2) c)
  | .C_def a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_def (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_def (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_def (4 * (a / 2) + 3) 0 (c + 1))
  | .C_hat a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 0)) fun b =>
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 2) 0 3)) fun c =>
      some (.S_hat (4 * (a / 2) + 4) 0 c)
    else
      Nat.casesOn b (some (.S_hat (4 * (a / 2) + 4) 0 1)) fun c =>
      some (.S_hat (4 * (a / 2) + 3) 0 (c + 1))
  | .C_ones3 a b =>
    if a % 2 = 0 then
      Nat.casesOn b none fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 0)) fun b =>
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 2)) 0 3)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 4)) 0 c)
    else
      Nat.casesOn b (some (.S_def (3 + (4 * (a / 2) + 4)) 0 1)) fun c =>
      some (.S_def (3 + (4 * (a / 2) + 3)) 0 (c + 1))

theorem is_valid_acceleration : IsValidAcceleration target start encode next := by
  refine IsValidAcceleration.of_step init_reaches_S ?_
  intro s
  cases s with
  | S_def k j c =>
    rcases k with _ | _ | _ | k
    · rcases j with _ | j
      · exact ReachesPlus.trans (step_S_k0_j0 c) (step_D_succ_to_cfg_C001 0 (c + 2))
      · exact step_S_def_k0_jsucc_to_cfg_C001 j c
    · rcases c with _ | c
      · exact step_S_k1_c0 j
      · exact ReachesPlus.trans (step_S_k1_csucc j c) (step_D_succ_to_cfg_C001 (j + 1) c)
    · rcases c with _ | c
      · exact step_SL_c0_k2 default 0 j
      · exact ReachesPlus.trans (step_S_k2_csucc j c) (step_D_succ_to_cfg_C001 (j + 2) c)
    · rcases c with _ | c
      · exact step_SL_c0_k2 default (k + 1) j
      · exact step_SL_stride3 default k j c
  | S_hat k j c =>
    rcases k with _ | _ | _ | k
    · rcases j with _ | j
      · exact step_SL_hat_k0_j0 c
      · exact step_S_hat_k0_jsucc j c
    · rcases c with _ | c
      · exact step_S_hat_k1_c0 j
      · exact step_S_hat_k1_csucc_to_cfg_C001 j c
    · rcases c with _ | c
      · exact step_SL_c0_k2 l_hat 0 j
      · exact step_SL_hat_k2_csucc j c
    · rcases c with _ | c
      · exact step_SL_c0_k2 l_hat (k + 1) j
      · exact step_SL_stride3 l_hat k j c
  | C_def a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt default (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b1 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b2 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b3 default (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b0 default (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b1 default (a / 2) c
        rwa [← ha] at hstep
  | C_hat a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l_hat (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b1 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b2 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_even_b3 l_hat (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b0 l_hat (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode]
        have hstep := step_C001_odd_b1 l_hat (a / 2) c
        rwa [← ha] at hstep
  | C_ones3 a b =>
    by_cases h : a % 2 = 0
    · have ha : a = 2 * (a / 2) := by omega
      rcases b with _ | _ | _ | c
      · simp only [next, h, ↓reduceIte, encode]
        rw [ha]
        obtain ⟨cfg', h_plus, h_halt⟩ := step_C001_even_b0_halt l_ones3 (a / 2)
        exact ⟨cfg', ReachesPlus.to_star h_plus, h_halt⟩
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b1 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b2 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_even_b3 l_ones3 (a / 2) c
        rwa [← ha] at hstep
    · have ha : a = 2 * (a / 2) + 1 := by omega
      rcases b with _ | c
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_odd_b0 l_ones3 (a / 2)
        rwa [← ha] at hstep
      · simp only [next, h, ↓reduceIte, encode, ← cfg_A_ones3_eq]
        have hstep := step_C001_odd_b1 l_ones3 (a / 2) c
        rwa [← ha] at hstep

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB0RC_1LC1RE_1RA1LD_0LC0LA_1RF1RD_HHH0RD
