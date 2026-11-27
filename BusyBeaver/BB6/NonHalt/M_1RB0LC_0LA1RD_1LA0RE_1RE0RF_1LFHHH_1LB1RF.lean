/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.Stack
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => none
  | 5, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.right)


private def A : Fin 6 := 0
private def B : Fin 6 := 1
private def C : Fin 6 := 2
private def F : Fin 6 := 5


private theorem pow_succ_list (u : List (Fin 2)) (n : Nat) : u ^ (n + 1) = u ++ u ^ n := rfl
private theorem listblank_append_nil (b : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> b = b := rfl
private theorem listblank_append_cons (x : Fin 2) (xs : List (Fin 2)) (b : ListBlank (Fin 2)) :
    (x :: xs) +> b = x >> (xs +> b) := rfl
private theorem zero_cons_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
private theorem default_head : (default : ListBlank (Fin 2)).head = 0 := rfl
private theorem default_tail : (default : ListBlank (Fin 2)).tail = default := rfl
private theorem init_nil : (init ([] : List (Fin 2))) = ⟨some A, ⟨0, default, default⟩⟩ := rfl

omit [Inhabited Γ] in
private theorem list_pow_add (l : List Γ) (n m : Nat) : l ^ (n + m) = l ^ n ++ l ^ m :=
  BusyBeaver.list_pow_add l n m

private theorem list_pow_append_one (u : List (Fin 2)) (k : ℕ) : u ^ k ++ u = u ^ (k + 1) :=
  BusyBeaver.list_pow_append_one u k

private theorem listblank_right_pow_add (s : ListBlank (Fin 2)) (n m : ℕ) :
    (([1] : List (Fin 2)) ^ n) +> ((([1] : List (Fin 2)) ^ m) +> s) =
    (([1] : List (Fin 2)) ^ (n + m)) +> s := by
  rw [← BusyBeaver.PairStack.listblank_append_right_assoc, ← list_pow_add]

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  simp only [zero_cons_default, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    default_head, default_tail, multiStep_zero, listblank_append_cons, listblank_append_nil]
  try rfl))
local macro "step" : tactic => `(tactic| (
  try refine stepPlus_stepStar ?_
  try simp only [listblank_append_cons, listblank_append_nil, Turing.ListBlank.head_cons,
      default_head]
  apply step_stepStar_stepPlus (by rfl)
  simp only [Turing.Tape.move, listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
    zero_cons_default, default_head, default_tail]))
local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

/-! ## Step-indexed safety (exact non-halting without halting-or-termination measures) -/

private def Safe (k : ℕ) (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∀ j ≤ k, ∀ c', multiStep target_tm c j = some c' → (step target_tm c').isSome

private theorem multiStep_zero_eq (c : Cfg (Fin 2) (Fin 6)) :
    multiStep target_tm c 0 = some c := rfl

private theorem multiStep_succ_eq (c : Cfg (Fin 2) (Fin 6)) (n : ℕ) :
    multiStep target_tm c (n + 1) = (multiStep target_tm c n).bind (step target_tm) :=
  Function.iterate_succ_apply' (Option.bind · (step target_tm)) n (some c)

private theorem multiStep_add_eq (c c₁ : Cfg (Fin 2) (Fin 6)) (a b : ℕ)
    (h : multiStep target_tm c a = some c₁) :
    multiStep target_tm c (a + b) = multiStep target_tm c₁ b := by
  induction b with
  | zero => exact h
  | succ b ih =>
    rw [← Nat.add_assoc, multiStep_succ_eq, ih, multiStep_succ_eq]

private theorem multiStep_none_succ
    (c : Cfg (Fin 2) (Fin 6)) (hs : step target_tm c = none) (m : ℕ) :
    multiStep target_tm c (m + 1) = none := by
  induction m with
  | zero =>
    rw [multiStep_succ_eq, multiStep_zero_eq]
    exact hs
  | succ m ih =>
    rw [multiStep_succ_eq, ih]
    rfl

private theorem multiStep_prefix_isSome {c c' : Cfg (Fin 2) (Fin 6)} {n j : ℕ}
    (h : multiStep target_tm c n = some c') (hj : j < n)
    {cj : Cfg (Fin 2) (Fin 6)} (hcj : multiStep target_tm c j = some cj) :
    (step target_tm cj).isSome := by
  have hsplit : n = j + (n - j - 1 + 1) := by omega
  rw [hsplit, multiStep_add_eq c cj j (n - j - 1 + 1) hcj] at h
  cases hs : step target_tm cj with
  | none =>
    rw [multiStep_none_succ cj hs (n - j - 1)] at h
    cases h
  | some _ => rfl

private theorem Safe_of_stepPlus {k : ℕ} {c c' : Cfg (Fin 2) (Fin 6)}
    (h : c [target_tm]⊢⁺ c') (hsafe : ∀ k' < k, Safe k' c') :
    Safe k c := by
  rcases h with ⟨n, hn, hreach⟩
  intro j hj cⱼ hcj
  rcases Nat.lt_or_ge j n with hlt | hge
  · exact multiStep_prefix_isSome hreach hlt hcj
  · have hjeq : j = n + (j - n) := by omega
    rw [hjeq, multiStep_add_eq c c' n (j - n) hreach] at hcj
    exact hsafe (k - n) (by omega) (j - n) (by omega) cⱼ hcj

private theorem isNotHalt_of_forall_safe (c₀ : Cfg (Fin 2) (Fin 6))
    (hinit : (init []) [target_tm]⊢⁺ c₀)
    (hsafe : ∀ k, Safe k c₀) : IsNotHalt target_tm := by
  rcases hinit with ⟨n₀, hn₀, hreach⟩
  intro cfg ⟨m, hm⟩
  rcases Nat.lt_or_ge m n₀ with hlt | hge
  · exact multiStep_prefix_isSome hreach hlt hm
  · have hmeq : m = n₀ + (m - n₀) := by omega
    rw [hmeq, multiStep_add_eq (init []) c₀ n₀ (m - n₀) hreach] at hm
    exact hsafe (m - n₀) (m - n₀) (Nat.le_refl _) cfg hm

/-! ## Unary-bitstring left encoding and right-tape buffer encoding -/

/-- Run-length separator bitstring encoding on the left half-tape:
    `false` (`0`) pushes a single `1`, `true` (`1`) pushes `1 0`. -/
private def encBits : List Bool → ListBlank (Fin 2)
  | [] => default
  | false :: w => (1 : Fin 2) >> encBits w
  | true :: w => (1 : Fin 2) >> (0 : Fin 2) >> encBits w

private def zeros : ℕ → List Bool
  | 0 => []
  | n + 1 => false :: zeros n

private def ones : ℕ → List Bool
  | 0 => []
  | n + 1 => true :: ones n

private theorem zeros_succ (n : ℕ) : zeros (n + 1) = false :: zeros n := rfl

private theorem zeros_add (a b : ℕ) : zeros (a + b) = zeros a ++ zeros b := by
  induction a with
  | zero => simp [zeros]
  | succ a ih =>
    have : a + 1 + b = (a + b) + 1 := by omega
    rw [this, zeros_succ, zeros_succ, List.cons_append, ih]

private theorem ones_succ (n : ℕ) : ones (n + 1) = true :: ones n := rfl

private theorem encBits_zeros (d : ℕ) (w : List Bool) :
    encBits (zeros d ++ w) = (([1] : List (Fin 2)) ^ d) +> encBits w := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [zeros_succ, List.cons_append, encBits, ih, pow_succ_list,
        BusyBeaver.PairStack.listblank_append_right_assoc]
    rfl

private theorem encBits_zeros_true (d : ℕ) (w : List Bool) :
    encBits (zeros d ++ true :: w) =
      (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encBits w) := by
  rw [encBits_zeros, encBits]
  have h := listblank_right_pow_add ((0 : Fin 2) >> encBits w) d 1
  change (([1] : List (Fin 2)) ^ d) +> ((1 : Fin 2) >> (0 : Fin 2) >> encBits w) =
    (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encBits w)
  exact h

private theorem encBits_nonempty_head (w : List Bool) (hw : w ≠ []) :
    ∃ t : ListBlank (Fin 2), encBits w = (1 : Fin 2) >> t := by
  cases w with
  | nil => exact False.elim (hw rfl)
  | cons b w' =>
    cases b with
    | false => exact ⟨encBits w', rfl⟩
    | true => exact ⟨(0 : Fin 2) >> encBits w', rfl⟩

private def encBuf : List ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], s => s
  | d :: M, s => (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> encBuf M s)

private theorem one_cons_encBuf (d : ℕ) (M : List ℕ) (s : ListBlank (Fin 2)) :
    (1 : Fin 2) >> encBuf (d :: M) s = encBuf ((d + 1) :: M) s := by
  dsimp [encBuf]
  rw [pow_succ_list ([1] : List (Fin 2)) (d + 1), BusyBeaver.PairStack.listblank_append_right_assoc]
  rfl

private theorem one_default_eq_encBuf :
    (1 : Fin 2) >> (default : ListBlank (Fin 2)) =
      encBuf [0] ((0 : Fin 2) >> (default : ListBlank (Fin 2))) := by
  dsimp [encBuf, HPow.hPow, instHPowListNat, List.replicate, List.flatten]
  simp

private def sweepBits : List ℕ → List Bool → List Bool
  | [], w => w
  | d :: M, w => sweepBits M (zeros d ++ true :: w)

private theorem sweepBits_zeros_rep (r : ℕ) (M : List ℕ) (w : List Bool) :
    sweepBits (List.replicate r 0 ++ M) w = sweepBits M (ones r ++ w) := by
  induction r generalizing w with
  | zero => rfl
  | succ r ih =>
    change sweepBits (List.replicate r 0 ++ M) (true :: w) = sweepBits M (true :: (ones r ++ w))
    rw [ih (true :: w)]
    have hcomm : ones r ++ true :: w = true :: (ones r ++ w) := by
      clear ih
      induction r with
      | zero => rfl
      | succ r' ih' =>
        change true :: (ones r' ++ true :: w) = true :: true :: (ones r' ++ w)
        rw [ih']
    rw [hcomm]

/-! ## Raw TM sweep & primitive `C`/`B` step rules -/

private theorem shift_F_1 (k : ℕ) (l r : ListBlank (Fin 2)) :
    (⟨some F, ⟨1, l, (([1] : List (Fin 2)) ^ k) +> r⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢*
    ⟨some F, ⟨1, (([1] : List (Fin 2)) ^ k) +> l, r⟩⟩ := by
  induction k generalizing l r with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
    have h1 : (⟨some F, ⟨1, l,
        (([1] : List (Fin 2)) ^ (k + 1)) +> r⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
        ⟨some F, ⟨1, (1 : Fin 2) >> l, (([1] : List (Fin 2)) ^ k) +> r⟩⟩ := by
      rw [pow_succ_list, BusyBeaver.PairStack.listblank_append_right_assoc]
      execute 1
    have h2 := ih ((1 : Fin 2) >> l) r
    have h3 := stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)
    have h_pow : (([1] : List (Fin 2)) ^ k) +> ((1 : Fin 2) >> l) =
        (([1] : List (Fin 2)) ^ (k + 1)) +> l := by
      change (([1] : List (Fin 2)) ^ k) +> (([1] : List (Fin 2)) +> l) = _
      rw [← BusyBeaver.PairStack.listblank_append_right_assoc, list_pow_append_one]
    rwa [h_pow] at h3

private theorem shift_F_block (k : ℕ) (l s : ListBlank (Fin 2)) :
    (⟨some F, ⟨1, l,
        (([1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> s)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
    ⟨some F, ⟨0, (([1] : List (Fin 2)) ^ (k + 1)) +> l, s⟩⟩ := by
  have h1 := shift_F_1 k l ((0 : Fin 2) >> s)
  have h2 : (⟨some F, ⟨1, (([1] : List (Fin 2)) ^ k) +> l,
      (0 : Fin 2) >> s⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some F, ⟨0, (([1] : List (Fin 2)) ^ (k + 1)) +> l, s⟩⟩ := by
    rw [pow_succ_list, BusyBeaver.PairStack.listblank_append_right_assoc]
    execute 1
  exact stepStar_stepPlus_stepPlus h1 h2

private theorem f_step_block_raw (t : ListBlank (Fin 2)) (d : ℕ) (s : ListBlank (Fin 2)) :
    (⟨some F, ⟨0, (1 : Fin 2) >> t,
        (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >>
        s)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
    ⟨some F, ⟨0, (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> (1 : Fin 2) >> t), s⟩⟩ := by
  have h1 : (⟨some F, ⟨0, (1 : Fin 2) >> t,
      (([1] : List (Fin 2)) ^ (d + 1)) +> ((0 : Fin 2) >> s)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some F, ⟨1, (0 : Fin 2) >> (1 : Fin 2) >> t,
          (([1] : List (Fin 2)) ^ d) +> ((0 : Fin 2) >> s)⟩⟩ := by
    rw [pow_succ_list ([1] : List (Fin 2)) d, BusyBeaver.PairStack.listblank_append_right_assoc]
    execute 3
  exact stepPlus_trans h1 (shift_F_block d ((0 : Fin 2) >> (1 : Fin 2) >> t) s)

private theorem f_sweep_bits (M : List ℕ) (w : List Bool) (hw : w ≠ []) (u : ListBlank (Fin 2)) :
    (⟨some F, ⟨0, encBits w, encBuf M ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some B, ⟨0, encBits (sweepBits M w), (1 : Fin 2) >> u⟩⟩ := by
  induction M generalizing w with
  | nil =>
    obtain ⟨t, ht⟩ := encBits_nonempty_head w hw
    dsimp [encBuf, sweepBits]
    rw [ht]
    execute 4
  | cons d M ih =>
    obtain ⟨t, ht⟩ := encBits_nonempty_head w hw
    have hstep : (⟨some F, ⟨0, encBits w,
        encBuf (d :: M) ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
        ⟨some F, ⟨0, encBits (zeros d ++ true :: w), encBuf M ((0 : Fin 2) >> u)⟩⟩ := by
      dsimp [encBuf]
      rw [encBits_zeros_true, ht]
      exact f_step_block_raw t d (encBuf M ((0 : Fin 2) >> u))
    have hne : zeros d ++ true :: w ≠ [] := by cases d <;> simp [zeros]
    exact stepPlus_trans hstep (ih (zeros d ++ true :: w) hne)

private def cfgC (w : List Bool) (M : List ℕ) (u : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some C, ⟨0, encBits w, (0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u)⟩⟩

private def cfgB
    (w : List Bool) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encBits w, (1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)⟩⟩

private def retB (w : List Bool) (u : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some B, ⟨0, encBits w, (1 : Fin 2) >> u⟩⟩

private theorem step_C_ff (w : List Bool) (hw : w ≠ []) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgC (false :: false :: w) M u) [target_tm]⊢⁺
      retB (sweepBits M (false :: true :: w)) u := by
  obtain ⟨t, ht⟩ := encBits_nonempty_head w hw
  have h1 : (cfgC (false :: false :: w) M u) [target_tm]⊢⁺
      ⟨some F, ⟨0, encBits (false :: true :: w), encBuf M ((0 : Fin 2) >> u)⟩⟩ := by
    unfold cfgC
    change (⟨some C, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> encBits w,
      (0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some F, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encBits w,
        encBuf M ((0 : Fin 2) >> u)⟩⟩
    rw [ht]
    execute 9
  exact stepPlus_trans h1 (f_sweep_bits M (false :: true :: w) (List.cons_ne_nil _ _) u)

private theorem step_C_ft (w : List Bool) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgC (false :: true :: w) M u) [target_tm]⊢⁺ cfgB w 1 M u := by
  unfold cfgC cfgB
  dsimp [encBits, encBuf, HPow.hPow, instHPowListNat, List.replicate, List.flatten]
  execute 5

private theorem step_C_t (w : List Bool) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgC (true :: w) M u) [target_tm]⊢⁺ cfgC w (0 :: M) u := by
  unfold cfgC
  dsimp [encBits, encBuf, HPow.hPow, instHPowListNat, List.replicate, List.flatten]
  execute 2

private theorem step_C_ones_ff
    (r : ℕ) (w : List Bool) (hw : w ≠ []) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgC (ones r ++ false :: false :: w) M u) [target_tm]⊢⁺
      retB (sweepBits M (ones r ++ false :: true :: w)) u := by
  induction r generalizing M with
  | zero => exact step_C_ff w hw M u
  | succ r ih =>
    have h1 := step_C_t (ones r ++ false :: false :: w) M u
    have h2 := ih (0 :: M)
    have hres : sweepBits (0 :: M) (ones r ++ false :: true :: w) =
        sweepBits M (ones (r + 1) ++ false :: true :: w) := by
      change sweepBits M (true :: (ones r ++ false :: true :: w)) =
        sweepBits M (true :: (ones r ++ false :: true :: w))
      rfl
    rw [hres] at h2
    exact stepPlus_trans h1 h2

private theorem step_C_ones_ft (r : ℕ) (w : List Bool) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgC (ones r ++ false :: true :: w) M u) [target_tm]⊢⁺
      cfgB w 1 (List.replicate r 0 ++ M) u := by
  induction r generalizing M with
  | zero => exact step_C_ft w M u
  | succ r ih =>
    have h1 := step_C_t (ones r ++ false :: true :: w) M u
    have h2 := ih (0 :: M)
    have hrep : List.replicate r 0 ++ (0 :: M) = List.replicate (r + 1) 0 ++ M := by
      clear h1 h2 ih
      induction r with
      | zero => rfl
      | succ r' ih' =>
        change 0 :: (List.replicate r' 0 ++ 0 :: M) = 0 :: (List.replicate (r' + 1) 0 ++ M)
        rw [ih']
    rw [hrep] at h2
    exact stepPlus_trans h1 h2

private theorem step_B_nil (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB [] d M u) [target_tm]⊢⁺
      retB (sweepBits M (zeros (d + 1) ++ [false, false, false, false, true])) u := by
  unfold cfgB
  have h1 : (⟨some B, ⟨0, default,
      (1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some F, ⟨1, (([1] : List (Fin 2)) ^ 2) +> default,
        (([1] : List (Fin 2)) ^ (2 + (d + 1))) +> ((0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u))⟩⟩ :=
            by
    dsimp [encBuf]
    rw [← listblank_right_pow_add ((0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u)) 2 (d + 1)]
    dsimp [HPow.hPow, instHPowListNat, List.replicate, List.flatten]
    execute 9
  have h2 := shift_F_block (2 + (d + 1)) ((([1] : List (Fin 2)) ^ 2) +> default)
    (encBuf M ((0 : Fin 2) >> u))
  have h3 := stepPlus_trans h1 h2
  have h_eq :
      (([1] : List (Fin 2)) ^ (2 + (d + 1) + 1)) +> ((([1] : List (Fin 2)) ^ 2) +> default) =
      encBits (zeros (d + 5) ++ [true]) := by
    rw [encBits_zeros_true (d + 5) [], listblank_right_pow_add]
    have hd : 2 + (d + 1) + 1 + 2 = d + 5 + 1 := by omega
    rw [hd, encBits, zero_cons_default]
  have h_list : zeros (d + 5) ++ [true] = zeros (d + 1) ++ [false, false, false, false, true] := by
    have hd : d + 5 = (d + 1) + 4 := by omega
    rw [hd, zeros_add, List.append_assoc]
    rfl
  rw [h_eq] at h3
  have h4 := f_sweep_bits M (zeros (d + 5) ++ [true]) (by cases d <;> simp [zeros]) u
  have h5 := stepPlus_trans h3 h4
  rwa [h_list] at h5

private theorem step_B_true_nil (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB [true] d M u) [target_tm]⊢⁺
      retB (sweepBits M (zeros (d + 1) ++ [false, false, false, false, true])) u := by
  unfold cfgB
  have h1 : (⟨some B, ⟨0, encBits [true],
      (1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺
      ⟨some F, ⟨1, (([1] : List (Fin 2)) ^ 2) +> default,
        (([1] : List (Fin 2)) ^ (2 + (d + 1))) +> ((0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u))⟩⟩ :=
            by
    dsimp [encBits, encBuf]
    rw [← listblank_right_pow_add ((0 : Fin 2) >> encBuf M ((0 : Fin 2) >> u)) 2 (d + 1)]
    dsimp [HPow.hPow, instHPowListNat, List.replicate, List.flatten]
    execute 7
  have h2 := shift_F_block (2 + (d + 1)) ((([1] : List (Fin 2)) ^ 2) +> default)
    (encBuf M ((0 : Fin 2) >> u))
  have h3 := stepPlus_trans h1 h2
  have h_eq :
      (([1] : List (Fin 2)) ^ (2 + (d + 1) + 1)) +> ((([1] : List (Fin 2)) ^ 2) +> default) =
      encBits (zeros (d + 5) ++ [true]) := by
    rw [encBits_zeros_true (d + 5) [], listblank_right_pow_add]
    have hd : 2 + (d + 1) + 1 + 2 = d + 5 + 1 := by omega
    rw [hd, encBits, zero_cons_default]
  have h_list : zeros (d + 5) ++ [true] = zeros (d + 1) ++ [false, false, false, false, true] := by
    have hd : d + 5 = (d + 1) + 4 := by omega
    rw [hd, zeros_add, List.append_assoc]
    rfl
  rw [h_eq] at h3
  have h4 := f_sweep_bits M (zeros (d + 5) ++ [true]) (by cases d <;> simp [zeros]) u
  have h5 := stepPlus_trans h3 h4
  rwa [h_list] at h5

private theorem step_B_ff
    (w : List Bool) (hw : w ≠ []) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB (false :: false :: w) d M u) [target_tm]⊢⁺
      retB (sweepBits M (zeros (d + 1) ++ true :: true :: w)) u := by
  obtain ⟨t, ht⟩ := encBits_nonempty_head w hw
  have h1 : (cfgB (false :: false :: w) d M u) [target_tm]⊢⁺
      ⟨some F, ⟨0, encBits w, encBuf (0 :: (d + 1) :: M) ((0 : Fin 2) >> u)⟩⟩ := by
    unfold cfgB
    change (⟨some B, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> encBits w,
      (1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺ _
    dsimp [encBuf]
    rw [pow_succ_list ([1] : List (Fin 2)) (d + 1),
        BusyBeaver.PairStack.listblank_append_right_assoc, ht]
    dsimp [HPow.hPow, instHPowListNat, List.replicate, List.flatten]
    execute 4
  exact stepPlus_trans h1 (f_sweep_bits (0 :: (d + 1) :: M) w hw u)

private theorem step_B_ft (w : List Bool) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB (false :: true :: w) d M u) [target_tm]⊢⁺ cfgB w 0 ((d + 1) :: M) u := by
  unfold cfgB
  dsimp [encBits, encBuf]
  rw [pow_succ_list ([1] : List (Fin 2)) (d + 1), BusyBeaver.PairStack.listblank_append_right_assoc]
  dsimp [HPow.hPow, instHPowListNat, List.replicate, List.flatten]
  execute 5

private theorem step_B_t (w : List Bool) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB (true :: w) d M u) [target_tm]⊢⁺
      cfgC w [] ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) := by
  unfold cfgB cfgC
  dsimp [encBits, encBuf]
  execute 2

private theorem retB_of_B_t (w : List Bool) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    retB w ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) =
      cfgB w (d + 1) M u := by
  unfold retB cfgB
  rw [one_cons_encBuf d M ((0 : Fin 2) >> u)]

private theorem step_B_ones_ff
    (r : ℕ) (w : List Bool) (hw : w ≠ []) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB (true :: (ones r ++ false :: false :: w)) d M u) [target_tm]⊢⁺
      cfgB (ones r ++ false :: true :: w) (d + 1) M u := by
  have h1 := step_B_t (ones r ++ false :: false :: w) d M u
  have h2 := step_C_ones_ff r w hw [] ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u))
  have h := stepPlus_trans h1 h2
  dsimp [sweepBits] at h
  rwa [retB_of_B_t] at h

private theorem step_B_ones_ft
    (r : ℕ) (w : List Bool) (d : ℕ) (M : List ℕ) (u : ListBlank (Fin 2)) :
    (cfgB (true :: (ones r ++ false :: true :: w)) d M u) [target_tm]⊢⁺
      cfgB w 1 (List.replicate r 0) ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) := by
  have h1 := step_B_t (ones r ++ false :: true :: w) d M u
  have h2 := step_C_ones_ft r w [] ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u))
  simpa using stepPlus_trans h1 h2

private theorem step_top_ff (w : List Bool) (hw : w ≠ []) :
    (retB (false :: false :: w) default) [target_tm]⊢⁺ retB (true :: true :: w) default := by
  obtain ⟨t, ht⟩ := encBits_nonempty_head w hw
  have h1 : (retB (false :: false :: w) default) [target_tm]⊢⁺
      ⟨some F, ⟨0, encBits w, encBuf [0, 0] ((0 : Fin 2) >> default)⟩⟩ := by
    unfold retB
    change (⟨some B, ⟨0, (1 : Fin 2) >> (1 : Fin 2) >> encBits w,
      (1 : Fin 2) >> default⟩⟩ : Cfg (Fin 2) (Fin 6)) [target_tm]⊢⁺ _
    dsimp [encBuf, HPow.hPow, instHPowListNat, List.replicate, List.flatten]
    rw [ht]
    execute 4
  exact stepPlus_trans h1 (f_sweep_bits [0, 0] w hw default)

private theorem step_top_t (w : List Bool) :
    (retB (true :: w) default) [target_tm]⊢⁺
      cfgC w [] ((1 : Fin 2) >> (default : ListBlank (Fin 2))) := by
  unfold retB cfgC
  dsimp [encBits, encBuf]
  execute 2

private theorem retB_of_top_t (w : List Bool) :
    retB w ((1 : Fin 2) >> (default : ListBlank (Fin 2))) = cfgB w 0 [] default := by
  unfold retB cfgB
  rw [one_default_eq_encBuf]

private theorem init_reaches_start :
    (init ([] : List (Fin 2))) [target_tm]⊢⁺
      retB [false, false, false, true] default := by
  rw [init_nil]
  unfold retB
  dsimp [encBits]
  execute 14

/-! ## The 10-state Mealy pair-DFA `Q10` -/

private inductive Q10 where
  | S0
  | S1
  | Sd
  | D0
  | D1
  | D2
  | Z0a
  | Z0b
  | Z1a
  | Z1b

private def InL : Q10 → List Bool → Prop
  | .S0,  false :: false :: w => InL .S0 w
  | .S0,  true  :: true  :: w => InL .Sd w
  | .S1,  false :: false :: w => InL .Sd w
  | .S1,  true  :: true  :: w => InL .S1 w
  | .Sd,  false :: false :: w => InL .D1 w
  | .Sd,  true  :: true  :: w => InL .D1 w
  | .D0,  false :: true  :: w => InL .Z0a w
  | .D0,  true  :: false :: w => InL .Z0b w
  | .D1,  false :: true  :: w => InL .Z1a w
  | .D1,  true  :: false :: w => InL .Z1b w
  | .D2,  false :: true  :: w => InL .Z0b w
  | .D2,  true  :: false :: w => InL .Z0a w
  | .Z0a, false :: false :: w => w ≠ [] ∧ InL .Z1a w
  | .Z0a, true  :: false :: w => InL .D0 w
  | .Z0b, false :: false :: w => InL .Z0a w
  | .Z0b, true  :: false :: w => InL .S0 w
  | .Z1a, []                  => True
  | .Z1a, [true]              => True
  | .Z1a, false :: true  :: w => InL .S1 w
  | .Z1a, true  :: true  :: w => InL .Z1b w
  | .Z1b, false :: true  :: w => InL .D2 w
  | .Z1b, true  :: true  :: w => InL .Z0a w
  | _,    _                   => False

private def InL0 (q : Q10) (w : List Bool) : Prop :=
  ∃ u, w = false :: u ∧ InL q u

private def InL0p (w : List Bool) : Prop :=
  ∃ u, w = false :: u ∧ u ≠ [] ∧ InL .Z1a u

private def InL1 (q : Q10) (w : List Bool) : Prop :=
  ∃ u, w = true :: u ∧ InL q u

private theorem InL_ne_nil {q : Q10} {w : List Bool} (hq : q ≠ .Z1a) (hw : InL q w) : w ≠ [] := by
  intro hnil
  subst hnil
  cases q with
  | Z1a => exact hq rfl
  | _ => exact hw

private theorem InL0_ne_nil {q : Q10} {w : List Bool} (hw : InL0 q w) : w ≠ [] := by
  rcases hw with ⟨u, rfl, _⟩
  exact List.cons_ne_nil _ _

private theorem InL0p_ne_nil {w : List Bool} (hw : InL0p w) : w ≠ [] := by
  rcases hw with ⟨u, rfl, _, _⟩
  exact List.cons_ne_nil _ _

private theorem InL1_ne_nil {q : Q10} {w : List Bool} (hw : InL1 q w) : w ≠ [] := by
  rcases hw with ⟨u, rfl, _⟩
  exact List.cons_ne_nil _ _

private theorem start_in_Sd : InL .Sd [false, false, false, true] := by
  trivial

private theorem reload_in_Z0b : InL .Z0b [false, false, false, false, true] := by
  exact ⟨List.cons_ne_nil _ _, trivial⟩

private theorem S1_eq_ones_double {w : List Bool} (hw : InL .S1 w) :
    ∃ r u, w = ones (2 * r) ++ false :: false :: u ∧ InL .Sd u := by
  match w with
  | [] => cases hw
  | [b] => cases b <;> cases hw
  | false :: false :: u => exact ⟨0, u, rfl, hw⟩
  | false :: true :: _ => cases hw
  | true :: false :: _ => cases hw
  | true :: true :: w' =>
    obtain ⟨r, u, heq, hu⟩ := S1_eq_ones_double (w := w') hw
    refine ⟨r + 1, u, ?_, hu⟩
    have : 2 * (r + 1) = (2 * r) + 2 := by omega
    rw [this, heq]
    rfl

private theorem ones_double_in_S1 (r : ℕ) {w : List Bool} (hw : InL .Sd w) :
    InL .S1 (ones (2 * r) ++ false :: false :: w) := by
  induction r with
  | zero => exact hw
  | succ m ihm =>
    have hmul : 2 * (m + 1) = 2 * m + 2 := by omega
    rw [hmul]
    exact ihm

/-! ## Step-indexed CPS contracts (`14` `hb` rules + `4` `Fb` rules) -/

private def SafeB (P Q : List Bool → Prop) (k : ℕ) : Prop :=
  ∀ w d M u, P w →
    (∀ k' < k, ∀ w', Q w' → Safe k' (retB (sweepBits M (zeros (d + 1) ++ w')) u)) →
    Safe k (cfgB w d M u)

private def SafeC (P Q : List Bool → Prop) (k : ℕ) : Prop :=
  ∀ w M u, P w →
    (∀ k' < k, ∀ w', Q w' → Safe k' (retB (sweepBits M w') u)) →
    Safe k (cfgC w M u)

private def Inv (k : ℕ) : Prop :=
  -- 6 plain hb rules
  SafeB (InL .Z1a) (InL .Z0b) k ∧
  SafeB (InL .Z0b) (InL .Z1b) k ∧
  SafeB (InL .D1)  (InL .D0)  k ∧
  SafeB (InL .D2)  (InL .D1)  k ∧
  SafeB (InL .Sd)  (InL .Sd)  k ∧
  SafeB (InL .S1)  (InL .S0)  k ∧
  -- 4 shifted `0.` hb rules
  SafeB InL0p       (InL1 .S1)  k ∧
  SafeB (InL0 .Z0b) (InL1 .D2)  k ∧
  SafeB (InL0 .D0)  (InL1 .Z1b) k ∧
  SafeB (InL0 .S0)  (InL1 .Z0b) k ∧
  -- 4 shifted `1.` hb rules
  SafeB (InL1 .Z0a) (InL0 .D0)  k ∧
  SafeB (InL1 .Z1b) (InL0 .Sd)  k ∧
  SafeB (InL1 .Sd)  (InL0 .Z0a) k ∧
  SafeB (InL1 .D2)  InL0p       k ∧
  -- 4 Fb rules
  SafeC (InL .Z1b)  (InL .Sd)   k ∧
  SafeC (InL .Z0a)  (InL .D1)   k ∧
  SafeC (InL0 .D0)  (InL0 .Z1b) k ∧
  SafeC (InL0 .S0)  (InL0 .Z0b) k

private theorem sweep_lift_1 {d : ℕ} {w : List Bool} :
    zeros (d + 1 + 1) ++ w = zeros (d + 1) ++ false :: w := by
  have : d + 1 + 1 = (d + 1) + 1 := rfl
  rw [zeros_add (d + 1) 1, List.append_assoc]
  rfl

private theorem sweep_lift_2 {d : ℕ} {w : List Bool} :
    zeros (d + 2 + 1) ++ w = zeros (d + 1) ++ false :: false :: w := by
  have : d + 2 + 1 = (d + 1) + 2 := by omega
  rw [this, zeros_add (d + 1) 2, List.append_assoc]
  rfl

private theorem sweep_lift_3 {d : ℕ} {w : List Bool} :
    zeros (d + 3 + 1) ++ w = zeros (d + 1) ++ false :: false :: false :: w := by
  have : d + 3 + 1 = (d + 1) + 3 := by omega
  rw [this, zeros_add (d + 1) 3, List.append_assoc]
  rfl

private theorem sweep_lift_4 {d : ℕ} {w : List Bool} :
    zeros (d + 4 + 1) ++ w = zeros (d + 1) ++ false :: false :: false :: false :: w := by
  have : d + 4 + 1 = (d + 1) + 4 := by omega
  rw [this, zeros_add (d + 1) 4, List.append_assoc]
  rfl

private theorem sweep_ones_ret (r : ℕ) (w' : List Bool) :
    sweepBits (List.replicate r 0) (zeros 2 ++ w') =
      ones r ++ false :: false :: w' := by
  have h := sweepBits_zeros_rep r [] (false :: false :: w')
  simpa [sweepBits, zeros] using h

private theorem inv_holds (k : ℕ) : Inv k := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    have hb_Z1a : SafeB (InL .Z1a) (InL .Z0b) k := by
      intro w d M u hw hcont
      match w with
      | [] =>
        exact Safe_of_stepPlus (step_B_nil d M u) fun k' hk' =>
          hcont k' hk' _ reload_in_Z0b
      | [true] =>
        exact Safe_of_stepPlus (step_B_true_nil d M u) fun k' hk' =>
          hcont k' hk' _ reload_in_Z0b
      | [false] => cases hw
      | false :: false :: _ => cases hw
      | true :: false :: _ => cases hw
      | false :: true :: v =>
        refine Safe_of_stepPlus (step_B_ft v d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.1 v 0 ((d + 1) :: M) u hw fun k₂ hk₂ w' hw' =>
          hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: w') hw'
      | true :: true :: v =>
        refine Safe_of_stepPlus (step_B_t (true :: v) d M u) fun k₁ hk₁ => ?_
        refine Safe_of_stepPlus (step_C_t v [] ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
          fun k₂ hk₂ => ?_
        exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v [0]
          ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hw fun k₃ hk₃ w₁ hw₁ => by
            change Safe k₃ (retB (true :: w₁) ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
            rw [retB_of_B_t]
            exact (ih k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))).2.2.2.2.2.2.2.2.2.2.2.2.1
              (true :: w₁) (d + 1) M u ⟨w₁, rfl, hw₁⟩ fun k₄ hk₄ w₂ hw₂ => by
                rcases hw₂ with ⟨y, rfl, hy⟩
                rw [sweep_lift_1]
                exact hcont k₄ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                  (false :: false :: y) hy
    have hb_Z0b : SafeB (InL .Z0b) (InL .Z1b) k := by
      intro w d M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: true :: _ => cases hw
      | true :: true :: _ => cases hw
      | false :: false :: v =>
        exact Safe_of_stepPlus (step_B_ff v (InL_ne_nil (fun h =>
            by cases h) hw) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: v) hw
      | true :: false :: v =>
        refine Safe_of_stepPlus (step_B_t (false :: v) d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2 (false :: v) []
          ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v, rfl, hw⟩ fun k₂ hk₂ w₁ hw₁ => by
            change Safe k₂ (retB w₁ ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
            rw [retB_of_B_t]
            exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.1
              w₁ (d + 1) M u hw₁ fun k₃ hk₃ w₂ hw₂ => by
                rcases hw₂ with ⟨y, rfl, hy⟩
                rw [sweep_lift_1]
                exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                  (false :: true :: y) hy
    have hb_D1 : SafeB (InL .D1) (InL .D0) k := by
      intro w d M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: false :: _ => cases hw
      | true :: true :: _ => cases hw
      | false :: true :: v =>
        refine Safe_of_stepPlus (step_B_ft v d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).1 v 0 ((d + 1) :: M) u hw fun k₂ hk₂ w' hw' =>
          hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: w') hw'
      | true :: false :: v =>
        match v with
        | [] => cases hw
        | [b] => cases b <;> cases hw
        | false :: false :: _ => cases hw
        | true :: false :: _ => cases hw
        | false :: true :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ff 0 (true :: v₂) (List.cons_ne_nil _ _) d M u)
            fun k₁ hk₁ => ?_
          refine Safe_of_stepPlus (step_B_ft (true :: v₂) (d + 1) M u) fun k₂ hk₂ => ?_
          exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v₂) 0
            ((d + 2) :: M) u ⟨v₂, rfl, hw⟩ fun k₃ hk₃ w' hw' => by
              rcases hw' with ⟨y, rfl, hne, hy⟩
              change Safe k₃
                  (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: false :: y)) u)
              rw [sweep_lift_1]
              exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (false :: true :: false :: false :: y) ⟨hne, hy⟩
        | true :: true :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ft 0 (true :: v₂) d M u) fun k₁ hk₁ => ?_
          exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.1 (true :: v₂) 1 []
            ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v₂, rfl,
                hw⟩ fun k₂ hk₂ w' hw' => by
              change Safe k₂
                  (retB (false :: false :: w') ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus (step_B_ff w' (InL0_ne_nil hw') (d + 1) M u) fun k₃ hk₃ => ?_
              rcases hw' with ⟨y, rfl, hy⟩
              rw [sweep_lift_1]
              exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (false :: true :: true :: false :: y) hy
    have hb_D2 : SafeB (InL .D2) (InL .D1) k := by
      intro w d M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: false :: _ => cases hw
      | true :: true :: _ => cases hw
      | false :: true :: v =>
        refine Safe_of_stepPlus (step_B_ft v d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.1 v 0 ((d + 1) :: M) u hw fun k₂ hk₂ w' hw' =>
          hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: w') hw'
      | true :: false :: v =>
        match v with
        | [] => cases hw
        | [b] => cases b <;> cases hw
        | false :: true :: _ => cases hw
        | true :: true :: _ => cases hw
        | false :: false :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ff 0 (false :: v₂) (List.cons_ne_nil _ _) d M u)
            fun k₁ hk₁ => ?_
          refine Safe_of_stepPlus (step_B_ft (false :: v₂) (d + 1) M u) fun k₂ hk₂ => ?_
          exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.1 (false :: v₂) 0
            ((d + 2) :: M) u ⟨v₂, rfl, hw.1, hw.2⟩ fun k₃ hk₃ w' hw' => by
              rcases hw' with ⟨y, rfl, hy⟩
              change Safe k₃
                  (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: true :: y)) u)
              rw [sweep_lift_1]
              exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (false :: true :: false :: true :: y) hy
        | true :: false :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ft 0 (false :: v₂) d M u) fun k₁ hk₁ => ?_
          exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.1 (false :: v₂) 1 []
            ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v₂, rfl,
                hw⟩ fun k₂ hk₂ w' hw' => by
              change Safe k₂
                  (retB (false :: false :: w') ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus (step_B_ff w' (InL1_ne_nil hw') (d + 1) M u) fun k₃ hk₃ => ?_
              rcases hw' with ⟨y, rfl, hy⟩
              rw [sweep_lift_1]
              exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                (false :: true :: true :: true :: y) hy
    have hb_Sd : SafeB (InL .Sd) (InL .Sd) k := by
      intro w d M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: true :: _ => cases hw
      | true :: false :: _ => cases hw
      | false :: false :: v =>
        exact Safe_of_stepPlus (step_B_ff v (InL_ne_nil (fun h =>
            by cases h) hw) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: v) hw
      | true :: true :: v =>
        match v with
        | [] => cases hw
        | [b] => cases b <;> cases hw
        | false :: false :: _ => cases hw
        | true :: true :: _ => cases hw
        | false :: true :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ft 1 v₂ d M u) fun k₁ hk₁ => ?_
          exact (ih k₁ hk₁).1 v₂ 1 [0]
            ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hw fun k₂ hk₂ w₁ hw₁ => by
              change Safe k₂ (retB (true :: false :: false :: w₁)
                ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus
                (step_B_ones_ff 0 w₁ (InL_ne_nil (fun h =>
                    by cases h) hw₁) (d + 1) M u) fun k₃ hk₃ => ?_
              refine Safe_of_stepPlus (step_B_ft w₁ (d + 2) M u) fun k₄ hk₄ => ?_
              exact (ih k₄ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))).2.1
                w₁ 0 ((d + 3) :: M) u hw₁ fun k₅ hk₅ w₂ hw₂ => by
                  change Safe k₅ (retB (sweepBits M (zeros (d + 2 + 1) ++ true :: false :: w₂)) u)
                  rw [sweep_lift_2]
                  exact hcont k₅
                    (Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))))
                    (false :: false :: true :: false :: w₂) hw₂
        | true :: false :: v₂ =>
          match v₂ with
          | [] => cases hw
          | [b] => cases b <;> cases hw
          | false :: false :: _ => cases hw
          | true :: false :: _ => cases hw
          | false :: true :: v₃ =>
            refine Safe_of_stepPlus
              (step_B_ones_ff 2 (true :: v₃) (List.cons_ne_nil _ _) d M u) fun k₁ hk₁ => ?_
            refine Safe_of_stepPlus (step_B_ones_ft 1 (true :: v₃) (d + 1) M u) fun k₂ hk₂ => ?_
            exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0]
              ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)) ⟨v₃, rfl, hw⟩
              fun k₃ hk₃ w₁ hw₁ => by
                change Safe k₃ (retB (true :: false :: false :: w₁)
                  ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)))
                rw [retB_of_B_t]
                refine Safe_of_stepPlus
                  (step_B_ones_ff 0 w₁ (InL0p_ne_nil hw₁) (d + 2) M u) fun k₄ hk₄ => ?_
                refine Safe_of_stepPlus (step_B_ft w₁ (d + 3) M u) fun k₅ hk₅ => ?_
                have hk₅lt : k₅ < k :=
                  Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                exact (ih k₅ hk₅lt).2.2.2.2.2.2.1 w₁ 0 ((d + 4) :: M) u hw₁
                  fun k₆ hk₆ w₂ hw₂ => by
                    rcases hw₂ with ⟨y, rfl, hy⟩
                    change Safe k₆
                        (retB (sweepBits M (zeros (d + 3 + 1) ++ true :: false :: true :: y)) u)
                    rw [sweep_lift_3]
                    exact hcont k₆ (Nat.lt_trans hk₆ hk₅lt)
                      (false :: false :: false :: true :: false :: true :: y) hy
          | true :: true :: v₃ =>
            refine Safe_of_stepPlus (step_B_ones_ft 2 (true :: v₃) d M u) fun k₁ hk₁ => ?_
            exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0, 0]
              ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v₃, rfl, hw⟩
              fun k₂ hk₂ w₁ hw₁ => by
                change Safe k₂ (retB (true :: true :: false :: false :: w₁)
                  ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
                rw [retB_of_B_t]
                refine Safe_of_stepPlus
                  (step_B_ones_ff 1 w₁ (InL0_ne_nil hw₁) (d + 1) M u) fun k₃ hk₃ => ?_
                refine Safe_of_stepPlus (step_B_ones_ft 0 w₁ (d + 2) M u) fun k₄ hk₄ => ?_
                have hk₄lt : k₄ < k :=
                  Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                exact (ih k₄ hk₄lt).2.2.2.2.2.2.2.2.1 w₁ 1 []
                  ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)) hw₁
                  fun k₅ hk₅ w₂ hw₂ => by
                    change Safe k₅ (retB (false :: false :: w₂)
                      ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)))
                    rw [retB_of_B_t]
                    refine Safe_of_stepPlus (step_B_ff w₂ (InL1_ne_nil hw₂) (d + 3) M u)
                      fun k₆ hk₆ => ?_
                    rcases hw₂ with ⟨y, rfl, hy⟩
                    rw [sweep_lift_3]
                    exact hcont k₆ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅ hk₄lt))
                      (false :: false :: false :: true :: true :: true :: y) hy
    have hb_S1 : SafeB (InL .S1) (InL .S0) k := by
      intro w d M u hw hcont
      obtain ⟨r, v, rfl, hv⟩ := S1_eq_ones_double hw
      cases r with
      | zero =>
        exact Safe_of_stepPlus (step_B_ff v (InL_ne_nil (fun h =>
            by cases h) hv) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: v) hv
      | succ r' =>
        have hlen : 2 * (r' + 1) = (2 * r' + 1) + 1 := by omega
        change Safe k (cfgB (ones (2 * (r' + 1)) ++ false :: false :: v) d M u)
        rw [hlen, ones_succ, List.cons_append]
        refine Safe_of_stepPlus
          (step_B_ones_ff (2 * r' + 1) v (InL_ne_nil (fun h =>
              by cases h) hv) d M u) fun k₁ hk₁ => ?_
        rw [ones_succ, List.cons_append]
        refine Safe_of_stepPlus (step_B_ones_ft (2 * r') v (d + 1) M u) fun k₂ hk₂ => ?_
        exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.1 v 1 (List.replicate (2 * r') 0)
          ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)) hv
          fun k₃ hk₃ w₁ hw₁ => by
            rw [sweep_ones_ret (2 * r') w₁, retB_of_B_t]
            exact (ih k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))).2.2.2.2.2.1
              (ones (2 * r') ++ false :: false :: w₁) (d + 2) M u (ones_double_in_S1 r' hw₁)
              fun k₄ hk₄ w₂ hw₂ => by
                rw [sweep_lift_2]
                exact hcont k₄
                  (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                  (false :: false :: w₂) hw₂
    have hb_0Z1a : SafeB InL0p (InL1 .S1) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hne, hv⟩
      match v with
      | [] => exact False.elim (hne rfl)
      | [false] => cases hv
      | [true] =>
        refine Safe_of_stepPlus (step_B_ft [] d M u) fun k₁ hk₁ => ?_
        refine Safe_of_stepPlus (step_B_nil 0 ((d + 1) :: M) u) fun k₂ hk₂ => ?_
        exact hcont k₂ (Nat.lt_trans hk₂ hk₁)
          (true :: false :: false :: false :: false :: false :: [true])
          ⟨[false, false, false, false, false, true], rfl, trivial⟩
      | false :: false :: _ => cases hv
      | true :: false :: _ => cases hv
      | false :: true :: v' =>
        exact Safe_of_stepPlus (step_B_ff (true :: v') (List.cons_ne_nil _ _) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: true :: v') ⟨true :: true :: v', rfl, hv⟩
      | true :: true :: v' =>
        refine Safe_of_stepPlus (step_B_ft (true :: v') d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.1 (true :: v') 0 ((d + 1) :: M) u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: false :: y)
              ⟨false :: false :: y, rfl, hy⟩
    have hb_0Z0b : SafeB (InL0 .Z0b) (InL1 .D2) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: true :: _ => cases hv
      | true :: true :: _ => cases hv
      | false :: false :: v' =>
        exact Safe_of_stepPlus (step_B_ff (false :: v') (List.cons_ne_nil _ _) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: false :: v') ⟨true :: false :: v', rfl, hv⟩
      | true :: false :: v' =>
        refine Safe_of_stepPlus (step_B_ft (false :: v') d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.1 (false :: v') 0 ((d + 1) :: M) u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: true :: y)
              ⟨false :: true :: y, rfl, hy⟩
    have hb_0D0 : SafeB (InL0 .D0) (InL1 .Z1b) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: false :: _ => cases hv
      | true :: true :: _ => cases hv
      | false :: true :: v' =>
        exact Safe_of_stepPlus (step_B_ff (true :: v') (List.cons_ne_nil _ _) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: true :: v') ⟨true :: true :: v', rfl, hv⟩
      | true :: false :: v' =>
        refine Safe_of_stepPlus (step_B_ft (false :: v') d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.1 (false :: v') 0 ((d + 1) :: M) u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: true :: y)
              ⟨false :: true :: y, rfl, hy⟩
    have hb_0S0 : SafeB (InL0 .S0) (InL1 .Z0b) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: true :: _ => cases hv
      | true :: false :: _ => cases hv
      | false :: false :: v' =>
        exact Safe_of_stepPlus (step_B_ff (false :: v') (List.cons_ne_nil _ _) d M u) fun k' hk' =>
          hcont k' hk' (true :: true :: false :: v') ⟨true :: false :: v', rfl, hv⟩
      | true :: true :: v' =>
        refine Safe_of_stepPlus (step_B_ft (true :: v') d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v') 0 ((d + 1) :: M) u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: false :: y)
              ⟨false :: false :: y, rfl, hy⟩
    have hb_1Z0a : SafeB (InL1 .Z0a) (InL0 .D0) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      refine Safe_of_stepPlus (step_B_t v d M u) fun k₁ hk₁ => ?_
      exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v []
        ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hv fun k₂ hk₂ w₁ hw₁ => by
          change Safe k₂ (retB w₁ ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
          rw [retB_of_B_t]
          exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.1 w₁ (d + 1) M u hw₁ fun k₃ hk₃ w₂ hw₂ => by
            rw [sweep_lift_1]
            exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)) (false :: w₂) ⟨w₂, rfl, hw₂⟩
    have hb_1Z1b : SafeB (InL1 .Z1b) (InL0 .Sd) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      refine Safe_of_stepPlus (step_B_t v d M u) fun k₁ hk₁ => ?_
      exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v []
        ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hv fun k₂ hk₂ w₁ hw₁ => by
          change Safe k₂ (retB w₁ ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
          rw [retB_of_B_t]
          exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.1 w₁ (d + 1) M u hw₁ fun k₃ hk₃ w₂ hw₂ => by
            rw [sweep_lift_1]
            exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)) (false :: w₂) ⟨w₂, rfl, hw₂⟩
    have hb_1Sd : SafeB (InL1 .Sd) (InL0 .Z0a) k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: true :: _ => cases hv
      | true :: false :: _ => cases hv
      | false :: false :: v₁ =>
        refine Safe_of_stepPlus
          (step_B_ones_ff 0 v₁ (InL_ne_nil (fun h => by cases h) hv) d M u) fun k₁ hk₁ => ?_
        refine Safe_of_stepPlus (step_B_ft v₁ (d + 1) M u) fun k₂ hk₂ => ?_
        exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.1 v₁ 0 ((d + 2) :: M) u hv
          fun k₃ hk₃ w' hw' => by
            change Safe k₃ (retB (sweepBits M (zeros (d + 1 + 1) ++ true :: false :: w')) u)
            rw [sweep_lift_1]
            exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
              (false :: true :: false :: w') ⟨true :: false :: w', rfl, hw'⟩
      | true :: true :: v₁ =>
        match v₁ with
        | [] => cases hv
        | [b] => cases b <;> cases hv
        | false :: false :: _ => cases hv
        | true :: true :: _ => cases hv
        | false :: true :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ft 2 v₂ d M u) fun k₁ hk₁ => ?_
          exact (ih k₁ hk₁).1 v₂ 1 [0, 0]
            ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hv
            fun k₂ hk₂ w₁ hw₁ => by
              change Safe k₂ (retB (true :: true :: false :: false :: w₁)
                ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus
                (step_B_ones_ff 1 w₁ (InL_ne_nil (fun h =>
                    by cases h) hw₁) (d + 1) M u) fun k₃ hk₃ => ?_
              refine Safe_of_stepPlus (step_B_ones_ft 0 w₁ (d + 2) M u) fun k₄ hk₄ => ?_
              have hk₄lt : k₄ < k :=
                Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
              exact (ih k₄ hk₄lt).2.1 w₁ 1 []
                ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)) hw₁
                fun k₅ hk₅ w₂ hw₂ => by
                  change Safe k₅ (retB (false :: false :: w₂)
                    ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)))
                  rw [retB_of_B_t]
                  refine Safe_of_stepPlus
                    (step_B_ff w₂ (InL_ne_nil (fun h =>
                        by cases h) hw₂) (d + 3) M u) fun k₆ hk₆ => ?_
                  rw [sweep_lift_3]
                  exact hcont k₆ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅ hk₄lt))
                    (false :: false :: false :: true :: true :: w₂)
                    ⟨false :: false :: true :: true :: w₂, rfl, List.cons_ne_nil _ _, hw₂⟩
        | true :: false :: v₂ =>
          match v₂ with
          | [] => cases hv
          | [b] => cases b <;> cases hv
          | false :: false :: _ => cases hv
          | true :: false :: _ => cases hv
          | false :: true :: v₃ =>
            refine Safe_of_stepPlus
              (step_B_ones_ff 3 (true :: v₃) (List.cons_ne_nil _ _) d M u) fun k₁ hk₁ => ?_
            refine Safe_of_stepPlus (step_B_ones_ft 2 (true :: v₃) (d + 1) M u) fun k₂ hk₂ => ?_
            exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0, 0]
              ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)) ⟨v₃, rfl, hv⟩
              fun k₃ hk₃ w₁ hw₁ => by
                change Safe k₃ (retB (true :: true :: false :: false :: w₁)
                  ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)))
                rw [retB_of_B_t]
                refine Safe_of_stepPlus
                  (step_B_ones_ff 1 w₁ (InL0p_ne_nil hw₁) (d + 2) M u) fun k₄ hk₄ => ?_
                refine Safe_of_stepPlus (step_B_ones_ft 0 w₁ (d + 3) M u) fun k₅ hk₅ => ?_
                have hk₅lt : k₅ < k :=
                  Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                exact (ih k₅ hk₅lt).2.2.2.2.2.2.1 w₁ 1 []
                  ((1 : Fin 2) >> encBuf ((d + 3) :: M) ((0 : Fin 2) >> u)) hw₁
                  fun k₆ hk₆ w₂ hw₂ => by
                    change Safe k₆ (retB (false :: false :: w₂)
                      ((1 : Fin 2) >> encBuf ((d + 3) :: M) ((0 : Fin 2) >> u)))
                    rw [retB_of_B_t]
                    refine Safe_of_stepPlus
                      (step_B_ff w₂ (InL1_ne_nil hw₂) (d + 4) M u) fun k₇ hk₇ => ?_
                    rcases hw₂ with ⟨y, rfl, hy⟩
                    rw [sweep_lift_4]
                    exact hcont k₇ (Nat.lt_trans hk₇ (Nat.lt_trans hk₆ hk₅lt))
                      (false :: false :: false :: false :: true :: true :: true :: y)
                      ⟨false :: false :: false :: true :: true :: true :: y, rfl,
                        List.cons_ne_nil _ _, hy⟩
          | true :: true :: v₃ =>
            refine Safe_of_stepPlus (step_B_ones_ft 3 (true :: v₃) d M u) fun k₁ hk₁ => ?_
            exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0, 0, 0]
              ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v₃, rfl, hv⟩
              fun k₂ hk₂ w₁ hw₁ => by
                change Safe k₂ (retB (true :: true :: true :: false :: false :: w₁)
                  ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
                rw [retB_of_B_t]
                refine Safe_of_stepPlus
                  (step_B_ones_ff 2 w₁ (InL0_ne_nil hw₁) (d + 1) M u) fun k₃ hk₃ => ?_
                refine Safe_of_stepPlus (step_B_ones_ft 1 w₁ (d + 2) M u) fun k₄ hk₄ => ?_
                have hk₄lt : k₄ < k :=
                  Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
                exact (ih k₄ hk₄lt).2.2.2.2.2.2.2.2.1 w₁ 1 [0]
                  ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)) hw₁
                  fun k₅ hk₅ w₂ hw₂ => by
                    change Safe k₅ (retB (true :: false :: false :: w₂)
                      ((1 : Fin 2) >> encBuf ((d + 2) :: M) ((0 : Fin 2) >> u)))
                    rw [retB_of_B_t]
                    refine Safe_of_stepPlus
                      (step_B_ones_ff 0 w₂ (InL1_ne_nil hw₂) (d + 3) M u) fun k₆ hk₆ => ?_
                    refine Safe_of_stepPlus (step_B_ft w₂ (d + 4) M u) fun k₇ hk₇ => ?_
                    have hk₇lt : k₇ < k :=
                      Nat.lt_trans hk₇ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅ hk₄lt))
                    exact (ih k₇ hk₇lt).2.2.2.2.2.2.2.2.2.2.2.1 w₂ 0 ((d + 5) :: M) u hw₂
                      fun k₈ hk₈ w₃ hw₃ => by
                        rcases hw₃ with ⟨y, rfl, hy⟩
                        change Safe k₈ (retB (sweepBits M
                          (zeros (d + 4 + 1) ++ true :: false :: false :: y)) u)
                        rw [sweep_lift_4]
                        exact hcont k₈ (Nat.lt_trans hk₈ hk₇lt)
                          (false :: false :: false :: false :: true :: false :: false :: y)
                          ⟨false :: false :: false :: true :: false :: false :: y, rfl,
                            List.cons_ne_nil _ _, hy⟩
    have hb_1D2 : SafeB (InL1 .D2) InL0p k := by
      intro w d M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: false :: _ => cases hv
      | true :: true :: _ => cases hv
      | false :: true :: v₁ =>
        refine Safe_of_stepPlus (step_B_ones_ft 0 v₁ d M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.1 v₁ 1 []
          ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) hv fun k₂ hk₂ w' hw' => by
            change Safe k₂ (retB (false :: false :: w')
              ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
            rw [retB_of_B_t]
            refine Safe_of_stepPlus
              (step_B_ff w' (InL_ne_nil (fun h => by cases h) hw') (d + 1) M u) fun k₃ hk₃ => ?_
            rw [sweep_lift_1]
            exact hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
              (false :: true :: true :: w') ⟨true :: true :: w', rfl, List.cons_ne_nil _ _, hw'⟩
      | true :: false :: v₁ =>
        match v₁ with
        | [] => cases hv
        | [b] => cases b <;> cases hv
        | false :: true :: _ => cases hv
        | true :: true :: _ => cases hv
        | false :: false :: v₂ =>
          refine Safe_of_stepPlus
            (step_B_ones_ff 1 (false :: v₂) (List.cons_ne_nil _ _) d M u) fun k₁ hk₁ => ?_
          refine Safe_of_stepPlus (step_B_ones_ft 0 (false :: v₂) (d + 1) M u) fun k₂ hk₂ => ?_
          exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.1 (false :: v₂) 1 []
            ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)) ⟨v₂, rfl, hv.1, hv.2⟩
            fun k₃ hk₃ w₁ hw₁ => by
              change Safe k₃ (retB (false :: false :: w₁)
                ((1 : Fin 2) >> encBuf ((d + 1) :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus (step_B_ff w₁ (InL1_ne_nil hw₁) (d + 2) M u) fun k₄ hk₄ => ?_
              rcases hw₁ with ⟨y, rfl, hy⟩
              rw [sweep_lift_2]
              exact hcont k₄
                (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
                (false :: false :: true :: true :: true :: y)
                ⟨false :: true :: true :: true :: y, rfl, List.cons_ne_nil _ _, hy⟩
        | true :: false :: v₂ =>
          refine Safe_of_stepPlus (step_B_ones_ft 1 (false :: v₂) d M u) fun k₁ hk₁ => ?_
          exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.1 (false :: v₂) 1 [0]
            ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)) ⟨v₂, rfl, hv⟩
            fun k₂ hk₂ w₁ hw₁ => by
              change Safe k₂ (retB (true :: false :: false :: w₁)
                ((1 : Fin 2) >> encBuf (d :: M) ((0 : Fin 2) >> u)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus
                (step_B_ones_ff 0 w₁ (InL1_ne_nil hw₁) (d + 1) M u) fun k₃ hk₃ => ?_
              refine Safe_of_stepPlus (step_B_ft w₁ (d + 2) M u) fun k₄ hk₄ => ?_
              have hk₄lt : k₄ < k :=
                Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))
              exact (ih k₄ hk₄lt).2.2.2.2.2.2.2.2.2.2.2.1 w₁ 0 ((d + 3) :: M) u hw₁
                fun k₅ hk₅ w₂ hw₂ => by
                  rcases hw₂ with ⟨y, rfl, hy⟩
                  change Safe k₅ (retB (sweepBits M
                    (zeros (d + 2 + 1) ++ true :: false :: false :: y)) u)
                  rw [sweep_lift_2]
                  exact hcont k₅ (Nat.lt_trans hk₅ hk₄lt)
                    (false :: false :: true :: false :: false :: y)
                    ⟨false :: true :: false :: false :: y, rfl, List.cons_ne_nil _ _, hy⟩
    have fb_Z1b : SafeC (InL .Z1b) (InL .Sd) k := by
      intro w M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: false :: _ => cases hw
      | true :: false :: _ => cases hw
      | false :: true :: v =>
        refine Safe_of_stepPlus (step_C_ft v M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.1 v 1 M u hw fun k₂ hk₂ w' hw' =>
          hcont k₂ (Nat.lt_trans hk₂ hk₁) (false :: false :: w') hw'
      | true :: true :: v =>
        refine Safe_of_stepPlus (step_C_t (true :: v) M u) fun k₁ hk₁ => ?_
        refine Safe_of_stepPlus (step_C_t v (0 :: M) u) fun k₂ hk₂ => ?_
        exact (ih k₂ (Nat.lt_trans hk₂ hk₁)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 v (0 :: 0 :: M) u hw
          fun k₃ hk₃ w' hw' =>
            hcont k₃ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)) (true :: true :: w') hw'
    have fb_Z0a : SafeC (InL .Z0a) (InL .D1) k := by
      intro w M u hw hcont
      match w with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: true :: _ => cases hw
      | true :: true :: _ => cases hw
      | false :: false :: v =>
        exact Safe_of_stepPlus (step_C_ff v hw.1 M u) fun k' hk' =>
          hcont k' hk' (false :: true :: v) hw.2
      | true :: false :: v =>
        refine Safe_of_stepPlus (step_C_t (false :: v) M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (false :: v) (0 :: M) u ⟨v, rfl, hw⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (true :: false :: y) hy
    have fb_0D0 : SafeC (InL0 .D0) (InL0 .Z1b) k := by
      intro w M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: false :: _ => cases hv
      | true :: true :: _ => cases hv
      | false :: true :: v' =>
        exact Safe_of_stepPlus (step_C_ff (true :: v') (List.cons_ne_nil _ _) M u) fun k' hk' =>
          hcont k' hk' (false :: true :: true :: v') ⟨true :: true :: v', rfl, hv⟩
      | true :: false :: v' =>
        refine Safe_of_stepPlus (step_C_ft (false :: v') M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.1 (false :: v') 1 M u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (false :: false :: true :: y)
              ⟨false :: true :: y, rfl, hy⟩
    have fb_0S0 : SafeC (InL0 .S0) (InL0 .Z0b) k := by
      intro w M u hw hcont
      rcases hw with ⟨v, rfl, hv⟩
      match v with
      | [] => cases hv
      | [b] => cases b <;> cases hv
      | false :: true :: _ => cases hv
      | true :: false :: _ => cases hv
      | false :: false :: v' =>
        exact Safe_of_stepPlus (step_C_ff (false :: v') (List.cons_ne_nil _ _) M u) fun k' hk' =>
          hcont k' hk' (false :: true :: false :: v') ⟨true :: false :: v', rfl, hv⟩
      | true :: true :: v' =>
        refine Safe_of_stepPlus (step_C_ft (true :: v') M u) fun k₁ hk₁ => ?_
        exact (ih k₁ hk₁).2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v') 1 M u ⟨v', rfl, hv⟩
          fun k₂ hk₂ w' hw' => by
            rcases hw' with ⟨y, rfl, hy⟩
            exact hcont k₂ (Nat.lt_trans hk₂ hk₁) (false :: false :: false :: y)
              ⟨false :: false :: y, rfl, hy⟩
    exact ⟨hb_Z1a, hb_Z0b, hb_D1, hb_D2, hb_Sd, hb_S1,
      hb_0Z1a, hb_0Z0b, hb_0D0, hb_0S0,
      hb_1Z0a, hb_1Z1b, hb_1Sd, hb_1D2,
      fb_Z1b, fb_Z0a, fb_0D0, fb_0S0⟩

private theorem top_Sd_safe (k : ℕ) : ∀ w, InL .Sd w → Safe k (retB w default) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro w hw
    match w with
    | [] => cases hw
    | [b] => cases b <;> cases hw
    | false :: true :: _ => cases hw
    | true :: false :: _ => cases hw
    | false :: false :: v =>
      exact Safe_of_stepPlus (step_top_ff v (InL_ne_nil (fun h => by cases h) hw)) fun k₁ hk₁ =>
        ih k₁ hk₁ (true :: true :: v) hw
    | true :: true :: v =>
      match v with
      | [] => cases hw
      | [b] => cases b <;> cases hw
      | false :: false :: _ => cases hw
      | true :: true :: _ => cases hw
      | false :: true :: v₂ =>
        refine Safe_of_stepPlus (step_top_t (true :: false :: true :: v₂)) fun k₁ hk₁ => ?_
        refine Safe_of_stepPlus
            (step_C_ones_ft 1 v₂ [] ((1 : Fin 2) >> (default : ListBlank (Fin 2)))) fun k₂ hk₂ => ?_
        exact (inv_holds k₂).1 v₂ 1 [0]
            ((1 : Fin 2) >> (default : ListBlank (Fin 2))) hw fun k₃ hk₃ w₁ hw₁ => by
          change Safe k₃
              (retB (true :: false :: false :: w₁) ((1 : Fin 2) >> (default : ListBlank (Fin 2))))
          rw [retB_of_top_t]
          refine Safe_of_stepPlus
            (step_B_ones_ff 0 w₁ (InL_ne_nil (fun h =>
                by cases h) hw₁) 0 [] default) fun k₄ hk₄ => ?_
          refine Safe_of_stepPlus (step_B_ft w₁ 1 [] default) fun k₅ hk₅ => ?_
          exact (inv_holds k₅).2.1 w₁ 0 [2] default hw₁ fun k₆ hk₆ w₂ hw₂ =>
            ih k₆ (Nat.lt_trans hk₆ (Nat.lt_trans hk₅ (Nat.lt_trans hk₄
              (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))))
              (false :: false :: true :: false :: w₂) hw₂
      | true :: false :: v₂ =>
        match v₂ with
        | [] => cases hw
        | [b] => cases b <;> cases hw
        | false :: false :: _ => cases hw
        | true :: false :: _ => cases hw
        | false :: true :: v₃ =>
          refine Safe_of_stepPlus
            (step_top_t (true :: true :: false :: false :: true :: v₃)) fun k₁ hk₁ => ?_
          refine Safe_of_stepPlus
            (step_C_ones_ff 2 (true :: v₃) (List.cons_ne_nil _ _) [] ((1 : Fin 2) >>
                (default : ListBlank (Fin 2))))
            fun k₂ hk₂ => ?_
          change Safe k₂
              (retB (true :: true :: false :: true :: true :: v₃) ((1 : Fin 2) >>
              (default : ListBlank (Fin 2))))
          rw [retB_of_top_t]
          refine Safe_of_stepPlus (step_B_ones_ft 1 (true :: v₃) 0 [] default) fun k₃ hk₃ => ?_
          exact (inv_holds k₃).2.2.2.2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0]
            ((1 : Fin 2) >> encBuf [0] ((0 : Fin 2) >> default)) ⟨v₃, rfl, hw⟩
            fun k₄ hk₄ w₁ hw₁ => by
              change Safe k₄ (retB (true :: false :: false :: w₁)
                ((1 : Fin 2) >> encBuf [0] ((0 : Fin 2) >> default)))
              rw [retB_of_B_t]
              refine Safe_of_stepPlus
                (step_B_ones_ff 0 w₁ (InL0p_ne_nil hw₁) 1 [] default) fun k₅ hk₅ => ?_
              refine Safe_of_stepPlus (step_B_ft w₁ 2 [] default) fun k₆ hk₆ => ?_
              have hk₆lt : k₆ < k :=
                Nat.lt_trans hk₆ (Nat.lt_trans hk₅ (Nat.lt_trans hk₄
                  (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁))))
              exact (inv_holds k₆).2.2.2.2.2.2.1 w₁ 0 [3] default hw₁ fun k₇ hk₇ w₂ hw₂ => by
                rcases hw₂ with ⟨y, rfl, hy⟩
                exact ih k₇ (Nat.lt_trans hk₇ hk₆lt)
                  (false :: false :: false :: true :: false :: true :: y) hy
        | true :: true :: v₃ =>
          refine Safe_of_stepPlus
            (step_top_t (true :: true :: false :: true :: true :: v₃)) fun k₁ hk₁ => ?_
          refine Safe_of_stepPlus
            (step_C_ones_ft 2 (true :: v₃) [] ((1 : Fin 2) >>
                (default : ListBlank (Fin 2)))) fun k₂ hk₂ => ?_
          exact (inv_holds k₂).2.2.2.2.2.2.2.2.2.2.1 (true :: v₃) 1 [0, 0]
            ((1 : Fin 2) >> (default : ListBlank (Fin 2))) ⟨v₃, rfl, hw⟩ fun k₃ hk₃ w₁ hw₁ => by
              change Safe k₃
                  (retB (true :: true :: false :: false :: w₁) ((1 : Fin 2) >>
                  (default : ListBlank (Fin 2))))
              rw [retB_of_top_t]
              refine Safe_of_stepPlus
                (step_B_ones_ff 1 w₁ (InL0_ne_nil hw₁) 0 [] default) fun k₄ hk₄ => ?_
              refine Safe_of_stepPlus (step_B_ones_ft 0 w₁ 1 [] default) fun k₅ hk₅ => ?_
              have hk₅lt : k₅ < k :=
                Nat.lt_trans hk₅ (Nat.lt_trans hk₄ (Nat.lt_trans hk₃ (Nat.lt_trans hk₂ hk₁)))
              exact (inv_holds k₅).2.2.2.2.2.2.2.2.1 w₁ 1 []
                ((1 : Fin 2) >> encBuf [1] ((0 : Fin 2) >> default)) hw₁ fun k₆ hk₆ w₂ hw₂ => by
                  change Safe k₆ (retB (false :: false :: w₂)
                    ((1 : Fin 2) >> encBuf [1] ((0 : Fin 2) >> default)))
                  rw [retB_of_B_t]
                  refine Safe_of_stepPlus
                    (step_B_ff w₂ (InL1_ne_nil hw₂) 2 [] default) fun k₇ hk₇ => ?_
                  rcases hw₂ with ⟨y, rfl, hy⟩
                  exact ih k₇ (Nat.lt_trans hk₇ (Nat.lt_trans hk₆ hk₅lt))
                    (false :: false :: false :: true :: true :: true :: y) hy


private theorem is_does_not_halt : IsNotHalt target_tm :=
  isNotHalt_of_forall_safe
    (retB [false, false, false, true] default)
    init_reaches_start
    (fun k => top_Sd_safe k [false, false, false, true] start_in_Sd)


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LF---_1LB1RF` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0LC_0LA1RD_1LA0RE_1RE0RF_1LFHHH_1LB1RF
