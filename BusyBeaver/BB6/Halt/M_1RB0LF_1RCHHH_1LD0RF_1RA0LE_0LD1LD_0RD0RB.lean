/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB` — `is_halt` (`IsHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LF_1RCHHH_1LD0RF_1RA0LE_0LD1LD_0RD0RB

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LF_1RC---_1LD0RF_1RA0LE_0LD1LD_0RD0RB`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => none
  | 2, 0 => some (some 3, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 1, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS
set_option autoImplicit true
set_option linter.unusedSimpArgs false


def A : Fin 6 := 0
def B : Fin 6 := 1
def C : Fin 6 := 2
def D : Fin 6 := 3
def E : Fin 6 := 4
def F : Fin 6 := 5


-- ============================================================================
-- Section 6: Proof of Halting (IsHalt target_tm)
-- ============================================================================
open Counter

namespace Solution

set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

@[simp] lemma init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
    ⟨some A, ⟨0, default, default⟩⟩ := rfl

-- ============================================================================
-- Section 6.2: Word Encoding (`LD`, `Lmp`, `RC`, `cfgL`, `cfgR`, `cfgC`)
-- ============================================================================

def encWord : LD → List (Fin 2)
  | .W0 => [1, 0, 0]
  | .W1 => [1, 1, 1]

/-- Left tape encoding with the invariant MSB sentinel `[.W1, .W1]` (`[1, 1, 1, 1, 1, 1]`) built in. -/
def Lmp (x : List LD) : ListBlank (Fin 2) :=
  encTape encWord ([1, 1, 1, 1, 1, 1] +> default) x

@[simp] lemma Lmp_nil : Lmp [] = [1, 1, 1, 1, 1, 1] +> default := rfl

lemma Lmp_cons (d : LD) (xs : List LD) : Lmp (d :: xs) = encWord d +> Lmp xs :=
  encTape_cons encWord ([1, 1, 1, 1, 1, 1] +> default) d xs

@[simp] lemma Lmp_W0 (xs : List LD) :
    Lmp (.W0 :: xs) = (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Lmp xs := by
  rw [Lmp_cons]; rfl

@[simp] lemma Lmp_W1 (xs : List LD) :
    Lmp (.W1 :: xs) = (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lmp xs := by
  rw [Lmp_cons]; rfl

@[simp] lemma Lmp_head (x : List LD) : (Lmp x).head = 1 := by
  cases x with
  | nil => rfl
  | cons d xs => cases d <;> simp [Lmp_W0, Lmp_W1]

@[simp] lemma Lmp_cons_tail (x : List LD) :
    (1 : Fin 2) >> (Lmp x).tail = Lmp x := by
  rw [← Lmp_head x, Turing.ListBlank.cons_head_tail]

def RC (m : ℕ) : ListBlank (Fin 2) :=
  [1] +> ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))

def cfgL (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{E}}> ([1, 0, 1, 0] +> r)

def cfgR (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> ([1, 1] +> r)

def cfgC (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  l {{C}}> ([1] +> r)

-- ============================================================================
-- Section 6.3: Micro-Step Rules
-- ============================================================================

macro "step1" : tactic => `(tactic| (
  try simp only [cfgL, cfgR, cfgC, RC, Lmp_W0, Lmp_W1, Lmp_nil,
    Lmp_head, Lmp_cons_tail,
    pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]
  refine multiStep_step (by rfl) ?_
  simp only [Turing.Tape.move, Tape.write,
    Lmp_head, Lmp_cons_tail,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail]))

macro "run_steps" n:num : tactic => `(tactic| (
  iterate $n step1
  simp only [cfgL, cfgR, cfgC, RC, Lmp_W0, Lmp_W1, Lmp_nil,
    Lmp_head, Lmp_cons_tail,
    pow_succ_list, pow_zero_list,
    List.singleton_append, List.nil_append, List.cons_append,
    listblank_append_cons, listblank_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    zero_cons_default, default_head, default_tail, multiStep_zero]
  rfl))

theorem LInc_w0_1 (xs : List LD) (r : ListBlank (Fin 2)) :
    (cfgL (Lmp (.W0 :: xs)) ([1] +> r)) [target_tm]⊢^{19}
      (cfgL (Lmp xs) ([1, 0, 1, 1] +> r)) := by
  run_steps 19

theorem LInc_w10 (xs : List LD) (r : ListBlank (Fin 2)) :
    (cfgL (Lmp (.W1 :: .W0 :: xs)) ([1] +> r)) [target_tm]⊢^{40}
      (cfgR (Lmp (.W1 :: .W1 :: xs)) ([0, 1, 1] +> r)) := by
  run_steps 40

theorem LInc_w11_1 (xs : List LD) (r : ListBlank (Fin 2)) :
    (cfgL (Lmp (.W1 :: .W1 :: xs)) ([1] +> r)) [target_tm]⊢^{6}
      (cfgL (Lmp xs) ([1, 0, 1, 0, 1, 0, 1] +> r)) := by
  run_steps 6

theorem RInc_w0 (xs : List LD) (r : ListBlank (Fin 2)) :
    (cfgR (Lmp xs) ([0, 1, 1] +> r)) [target_tm]⊢^{3}
      (cfgR (Lmp (.W0 :: xs)) r) := by
  run_steps 3

theorem RInc_w11 (xs' : List LD) (r : ListBlank (Fin 2)) :
    (cfgR (Lmp xs') ([0, 1, 1, 0, 1, 0, 1, 0, 1] +> r)) [target_tm]⊢^{28}
      (cfgR (Lmp (.W1 :: .W0 :: xs')) ([0, 1, 1] +> r)) := by
  run_steps 28

theorem RC_turn_48 (x : List LD) :
    (cfgR (Lmp x) ([0, 1] +> default)) [target_tm]⊢^{48}
      (cfgL (Lmp x) (RC 1)) := by
  run_steps 48

theorem lov_nil_48 (r : ListBlank (Fin 2)) :
    (cfgL (Lmp []) ([1] +> r)) [target_tm]⊢^{48}
      (cfgC (Lmp [.W0, .W0]) r) := by
  run_steps 48

theorem lov_w0_7 (u : List LD) (r : ListBlank (Fin 2)) :
    (cfgC (Lmp u) ([0, 1, 1] +> r)) [target_tm]⊢^{7}
      (cfgC (Lmp (.W1 :: u)) r) := by
  run_steps 7

theorem lov_w11_0_28 (x : List LD) (r : ListBlank (Fin 2)) :
    (cfgC (Lmp (.W0 :: x)) ([0, 1, 0, 1, 0, 1] +> r)) [target_tm]⊢^{28}
      (cfgC (Lmp (.W0 :: .W0 :: .W1 :: x)) r) := by
  run_steps 28

theorem lov_w11_1_start (z : List LD) (r : ListBlank (Fin 2)) :
    (cfgC (Lmp (.W1 :: z)) ([0, 1, 0, 1, 0, 1] +> r)) [target_tm]⊢^{13}
      (cfgL (Lmp z) ([1, 0, 1, 1, 0, 1] +> r)) := by
  run_steps 13

theorem lov_w11_1_end (z' : List LD) (r : ListBlank (Fin 2)) :
    (cfgR (Lmp z') ([0, 1, 1, 0, 1, 1, 0, 1] +> r)) [target_tm]⊢^{9}
      (cfgC (Lmp (.W0 :: .W0 :: .W0 :: z')) r) := by
  run_steps 9

theorem lov_finish_13 (y : List LD) :
    (cfgC (Lmp (.W1 :: y)) ([0, 1] +> default)) [target_tm]⊢^{13}
      (cfgL (Lmp y) (RC 0)) := by
  run_steps 13

-- ============================================================================
-- Section 6.4: Carry Invariant (`LInc_RC`, `round_step`)
-- ============================================================================

theorem LInc_step {x x' : List LD} (h : LInc x x') :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL (Lmp x) ([1] +> r)) [target_tm]⊢* (cfgR (Lmp x') ([0, 1, 1] +> r)) := by
  induction h with
  | @w0 xs xs' _ ih =>
    intro r
    exact stepStar_trans ⟨19, LInc_w0_1 xs r⟩
      (stepStar_trans (ih ([0, 1, 1] +> r)) ⟨3, RInc_w0 xs' ([0, 1, 1] +> r)⟩)
  | w10 xs =>
    intro r; exact ⟨40, LInc_w10 xs r⟩
  | @w11 xs xs' _ ih =>
    intro r
    exact stepStar_trans ⟨6, LInc_w11_1 xs r⟩
      (stepStar_trans (ih ([0, 1, 0, 1, 0, 1] +> r)) ⟨28, RInc_w11 xs' r⟩)

theorem RC_return : ∀ (m : ℕ) (x : List LD),
    (cfgR (Lmp x) ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default)))
      [target_tm]⊢* (cfgL (Lmp x) (RC (m + 1)))
  | 0, x => ⟨48, RC_turn_48 x⟩
  | m + 1, x => by
    rw [pow_succ_list, listblank_append_assoc]
    exact stepStar_trans ⟨3, RInc_w0 x ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))⟩
      (stepStar_trans (RC_return m (.W0 :: x))
        ⟨19, LInc_w0_1 x ((([0, 1, 1] : List (Fin 2)) ^ (m + 1)) +> ([0, 1] +> default))⟩)

theorem LInc_RC {x x' : List LD} (h : LInc x x') (m : ℕ) :
    (cfgL (Lmp x) (RC m)) [target_tm]⊢* (cfgL (Lmp x') (RC (m + 2))) := by
  refine stepStar_trans (LInc_step h ((([0, 1, 1] : List (Fin 2)) ^ m) +> ([0, 1] +> default))) ?_
  exact RC_return (m + 1) x'

theorem LIncs_RC {n : ℕ} {x x' : List LD} (h : LIncs n x x') :
    ∀ (m : ℕ), (cfgL (Lmp x) (RC m)) [target_tm]⊢* (cfgL (Lmp x') (RC (m + 2 * n))) := by
  induction h with
  | zero x =>
    intro m; rw [Nat.mul_zero, Nat.add_zero]; exact stepStar_refl _ _
  | @succ n x y z h1 _ ih =>
    intro m
    have heq : m + 2 * (n + 1) = (m + 2) + 2 * n := by omega
    rw [heq]
    exact stepStar_trans (LInc_RC h1 m) (ih (m + 2))

lemma LIncsP_pow9_bound {n : ℕ} {xs xs' : List LD} (h : LIncsP n xs xs') :
    LIncsP (512 * n + 511)
      ((([.W1, .W0] : List LD) ^ 9) ++ xs)
      ((([.W1, .W1] : List LD) ^ 9) ++ xs') := by
  have h1 := LIncsP.w10 h
  have h2 := LIncsP.w10 h1
  have h3 := LIncsP.w10 h2
  have h4 := LIncsP.w10 h3
  have h5 := LIncsP.w10 h4
  have h6 := LIncsP.w10 h5
  have h7 := LIncsP.w10 h6
  have h8 := LIncsP.w10 h7
  have h9 := LIncsP.w10 h8
  have heq : 2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * (2 * n + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1 =
      512 * n + 511 := by omega
  rwa [heq] at h9

lemma LOv2_correct_aux {w u y : List LD} (h : LOv2 w u y) (hu : u = [.W0, .W0]) :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL (Lmp w) ([1] +> r)) [target_tm]⊢* (cfgC (Lmp y) r) := by
  induction h with
  | nil =>
    subst hu; intro r; exact ⟨48, lov_nil_48 r⟩
  | @w0 xs _ u' _ ih =>
    intro r
    exact stepStar_trans ⟨19, LInc_w0_1 xs r⟩
      (stepStar_trans (ih hu ([0, 1, 1] +> r)) ⟨7, lov_w0_7 u' r⟩)
  | @w11_0 xs _ x _ ih =>
    intro r
    exact stepStar_trans ⟨6, LInc_w11_1 xs r⟩
      (stepStar_trans (ih hu ([0, 1, 0, 1, 0, 1] +> r)) ⟨28, lov_w11_0_28 x r⟩)
  | @w11_1 xs _ z z' _ hz ih =>
    intro r
    exact stepStar_trans ⟨6, LInc_w11_1 xs r⟩
      (stepStar_trans (ih hu ([0, 1, 0, 1, 0, 1] +> r))
        (stepStar_trans ⟨13, lov_w11_1_start z r⟩
          (stepStar_trans (LInc_step hz ([0, 1, 1, 0, 1] +> r))
            ⟨9, lov_w11_1_end z' r⟩)))

theorem LOv2_correct {w y : List LD} (h : LOv2 w [.W0, .W0] y) :
    ∀ (r : ListBlank (Fin 2)),
      (cfgL (Lmp w) ([1] +> r)) [target_tm]⊢* (cfgC (Lmp y) r) :=
  LOv2_correct_aux h rfl

theorem lov_w0_iter : ∀ (m : ℕ) (y : List LD) (r : ListBlank (Fin 2)),
    (cfgC (Lmp y) ((([0, 1, 1] : List (Fin 2)) ^ m) +> r))
      [target_tm]⊢*
    (cfgC (Lmp ((([.W1] : List LD) ^ m) ++ y)) r)
  | 0, y, r => stepStar_refl _ _
  | m + 1, y, r => by
    rw [pow_succ_right, listblank_append_assoc]
    refine stepStar_trans (lov_w0_iter m y ([0, 1, 1] +> r)) ?_
    have h7 := lov_w0_7 ((([.W1] : List LD) ^ m) ++ y) r
    rw [pow_succ_list, List.singleton_append, List.cons_append]
    exact ⟨7, h7⟩

theorem full_overflow_step {w y : List LD} (m : ℕ) (h : LOv2 w [.W0, .W0] y) :
    (cfgL (Lmp w) (RC (m + 1))) [target_tm]⊢*
      (cfgL (Lmp ((([.W1] : List LD) ^ m) ++ y)) (RC 0)) := by
  refine stepStar_trans (LOv2_correct h ((([0, 1, 1] : List (Fin 2)) ^ (m + 1)) +> ([0, 1] +> default))) ?_
  refine stepStar_trans (lov_w0_iter (m + 1) y ([0, 1] +> default)) ?_
  rw [pow_succ_list, List.singleton_append, List.cons_append]
  exact ⟨13, lov_finish_13 ((([.W1] : List LD) ^ m) ++ y)⟩

theorem round_step {X X' Y Z : List LD} (m : ℕ)
    (h1 : LIncsP m X X')
    (h2 : LOv2 X' [.W0, .W0] Y)
    (h3 : LInc ((([.W1] : List LD) ^ (2 * m + 1)) ++ Y) Z) :
    (cfgL (Lmp X) (RC 2)) [target_tm]⊢* (cfgL (Lmp Z) (RC 2)) := by
  have h_incs := LIncs_RC (LIncsP_to_LIncs h1) 2
  have heq : 2 + 2 * m = (2 * m + 1) + 1 := by omega
  rw [heq] at h_incs
  exact stepStar_trans h_incs
    (stepStar_trans (full_overflow_step (2 * m + 1) h2) (LInc_RC h3 0))

-- ============================================================================
-- Section 6.5: Initial Bootstrap (`init` -> `x2` -> `x3`)
-- ============================================================================

def ux2 : List LD :=
  [.W1, .W1, .W0, .W1, .W0, .W0, .W1, .W1, .W0, .W0, .W0, .W0, .W1, .W1]

def x2 : List LD := (([.W1, .W0] : List LD) ^ 9) ++ ux2

def u0_tail : List LD :=
  [.W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1, .W0, .W1,
   .W0, .W0, .W0, .W0, .W0, .W0, .W0, .W0, .W1, .W0, .W1, .W0, .W0, .W1, .W1]

def u0 : List LD := .W1 :: .W1 :: u0_tail

def c_init_104 : CCfg (Fin 2) (Fin 6) := ⟨A, 0, [], ([0] : List (Fin 2)) ^ 104⟩

def c_x2 : CCfg (Fin 2) (Fin 6) :=
  ⟨E, 1,
   [1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0,
    1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1,
    1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
   [0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1]⟩

def cmultiStepChunk : ℕ → ℕ → CCfg (Fin 2) (Fin 6) → Option (CCfg (Fin 2) (Fin 6))
  | 0, _, c => some c
  | k + 1, m, c => (cmultiStep target_tm m c).bind (cmultiStepChunk k m)

theorem cmultiStepChunk_sound : ∀ (k m : ℕ) (c c' : CCfg (Fin 2) (Fin 6)) (r_tail : ListBlank (Fin 2)),
    cmultiStepChunk k m c = some c' → (evalCCfg r_tail c) [target_tm]⊢^{m * k} (evalCCfg r_tail c')
  | 0, m, c, c', _, h => by
    injection h with h'; subst h'; simp
  | k + 1, m, c, c', r_tail, h => by
    simp only [cmultiStepChunk, Option.bind_eq_some_iff] at h
    rcases h with ⟨c₁, h₁, h₂⟩
    rw [Nat.mul_succ, Nat.add_comm]
    exact multiStep_trans
      (cmultiStep_sound m c c₁ r_tail h₁)
      (cmultiStepChunk_sound k m c₁ c' r_tail h₂)

theorem init_to_x2 : (init []) [target_tm]⊢* (cfgL (Lmp x2) (RC 2)) := by
  have h_eq1 : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) = evalCCfg default c_init_104 := by
    simp [evalCCfg, evalWindow, c_init_104, zeros_append_default]
  have h_eq2 : evalCCfg default c_x2 = cfgL (Lmp x2) (RC 2) := rfl
  have h_steps : cmultiStepChunk 6 901 c_init_104 = some c_x2 := by decide
  rw [h_eq1, ← h_eq2]
  exact ⟨901 * 6, cmultiStepChunk_sound 6 901 c_init_104 c_x2 default h_steps⟩

theorem x2_to_x3 :
    ∃ m3 ≥ 511,
      (cfgL (Lmp x2) (RC 2)) [target_tm]⊢*
        (cfgL (Lmp ((([.W1, .W0] : List LD) ^ m3) ++ u0)) (RC 2)) := by
  let ux2' := (lincspFinite ux2).getD []
  have h_ux2 : LIncsP (lincspCount ux2) ux2 ux2' :=
    lincspFinite_sound (by decide : lincspFinite ux2 = some ux2')
  have h_9 : LIncsP (512 * lincspCount ux2 + 511) x2 ((([.W1, .W1] : List LD) ^ 9) ++ ux2') :=
    LIncsP_pow9_bound h_ux2
  let x2' := ((([.W1, .W1] : List LD) ^ 9) ++ ux2')
  have h_ov : LOv2 x2' [.W0, .W0] (.W0 :: u0_tail) :=
    lov2Finite_sound (by decide : lov2Finite x2' [.W0, .W0] = some (.W0 :: u0_tail))
  let m3 := 512 * lincspCount ux2 + 511
  refine ⟨m3, by omega, ?_⟩
  have h_inc : LInc ((([.W1] : List LD) ^ (2 * m3 + 1)) ++ (.W0 :: u0_tail))
      ((([.W1, .W0] : List LD) ^ m3) ++ u0) := by
    rw [pow_W1_odd m3 (.W0 :: u0_tail)]
    exact LInc_pow_11_10 m3 u0_tail
  exact round_step m3 h_9 h_ov h_inc

-- ============================================================================
-- Section 6.6: Buffer Shielding (`isBuffer_8_B1`, `chain_round_step`, `runU_steps`)
-- ============================================================================

theorem isBuffer_8_B1 : IsBuffer 8 [.W1, .W1, .W0] := by decide

lemma LInc_round_tail (m : ℕ) (s : List LD) :
    LInc ((([.W1] : List LD) ^ (2 * m + 1)) ++
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ s)))
      ((([.W1, .W0] : List LD) ^ m) ++
      ([.W1, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 11) ++ s))) := by
  rw [pow_W1_odd]
  exact LInc_pow_11_10 m ([.W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ s))

lemma chain_round_step_aux {r m : ℕ} (hr : r ≤ 8) (hm : m ≥ 26)
    {T T₀' u u' W' : List LD}
    (h_10 : LIncsP m ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u)) ((([.W1, .W1] : List LD) ^ 10) ++ W'))
    (h_ov : LOv2 W' [.W0, .W0] ([.W0, .W0, .W1, .W0] ++ (T₀' ++ u')))
    (h_ct0 : ChainTail r T₀') :
    ∃ T', ChainTail r T' ∧
      ((cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u))) (RC 2))
        [target_tm]⊢*
      (cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u'))) (RC 2))) := by
  have h_ov10 : LOv2 ((([.W1, .W1] : List LD) ^ 10) ++ W') [.W0, .W0]
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ (T₀' ++ u'))) :=
    LOv2_append (LOv2_pow_11 10 (T₀' ++ u')) h_ov
  let B1 : List LD := [.W1, .W1, .W0]
  let tail_rest := ((([.W1, .W0] : List LD) ^ 11) ++ (T₀' ++ u'))
  have h_inc : LInc ((([.W1] : List LD) ^ (2 * m + 1)) ++
      ([.W0, .W0, .W1, .W0] ++ ((([.W1, .W0] : List LD) ^ 10) ++ (T₀' ++ u'))))
      ((([.W1, .W0] : List LD) ^ m) ++ (B1 ++ tail_rest)) :=
    LInc_round_tail m (T₀' ++ u')
  have h_step := round_step m h_10 h_ov10 h_inc
  have hm_split : m = 10 + ((m - 10 - 2 * r) + 2 * r) := by omega
  let T' := ((([.W1, .W0] : List LD) ^ (m - 10 - 2 * r)) ++
    ((([.W1, .W0] : List LD) ^ (2 * r)) ++ (B1 ++ ((([.W1, .W0] : List LD) ^ 11) ++ T₀'))))
  have hB1 : IsBuffer r B1 := isBuffer_le hr isBuffer_8_B1
  have h_ct_T' : ChainTail r T' :=
    ChainTail_pow_pair (m - 10 - 2 * r) (.buf hB1 (ChainTail_pow_pair 11 h_ct0))
  have h_eq : ((([.W1, .W0] : List LD) ^ m) ++ (B1 ++ tail_rest)) =
      ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u')) := by
    conv_lhs => rw [hm_split, list_pow_add, list_pow_add]
    simp only [T', tail_rest, List.append_assoc]
  rw [h_eq] at h_step
  exact ⟨T', h_ct_T', h_step⟩

theorem chain_round_step {r : ℕ} (hr : r ≤ 8) {T : List LD} (hT : ChainTail (r + 1) T)
    {u u' : List LD} (hu : macroStepFinite u = some u') :
    ∃ T', ChainTail r T' ∧
      ((cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u))) (RC 2))
        [target_tm]⊢*
      (cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u'))) (RC 2))) := by
  rcases ChainTail_step hT hu with ⟨n, W', T₀', h_lp, h_ov, h_ct0⟩
  exact chain_round_step_aux hr (by omega) (LIncsP_pow10_bound h_lp) h_ov h_ct0

theorem runU_steps : ∀ (k : ℕ) (r : ℕ), r + k ≤ 8 →
    ∀ {T u u' : List LD},
      ChainTail (r + k) T →
      runU k u = some u' →
      ∃ T', ChainTail r T' ∧
        ((cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T ++ u))) (RC 2))
          [target_tm]⊢*
        (cfgL (Lmp ((([.W1, .W0] : List LD) ^ 10) ++ (T' ++ u'))) (RC 2)))
  | 0, r, _, T, u, _, hT, hu => by
    injection hu with hu'; subst hu'
    exact ⟨T, hT, stepStar_refl _ _⟩
  | k + 1, r, hrk, T, u, u', hT, hu => by
    simp only [runU, Option.bind_eq_some_iff] at hu
    rcases hu with ⟨u₁, hu₁, hu₂⟩
    have h_eq : r + (k + 1) = (r + k) + 1 := by omega
    rw [h_eq] at hT
    rcases chain_round_step (by omega : r + k ≤ 8) hT hu₁ with ⟨T₁, hT₁, h_step1⟩
    rcases runU_steps k r (by omega) hT₁ hu₂ with ⟨T', hT', h_step2⟩
    exact ⟨T', hT', stepStar_trans h_step1 h_step2⟩

-- ============================================================================
-- Section 6.7: `Only011` Prefix Sweep & 896-Step Halt from `msb_13`
-- ============================================================================

theorem Only011_skip {P : List LD} (hP : Only011 P) (s : List LD) :
    ∀ (r : ListBlank (Fin 2)),
      ∃ r', (cfgL (Lmp (P ++ s)) ([1] +> r)) [target_tm]⊢* (cfgL (Lmp s) ([1] +> r')) := by
  induction hP with
  | nil =>
    intro r; exact ⟨r, stepStar_refl _ _⟩
  | @w0 xs _ ih =>
    intro r
    rcases ih ([0, 1, 1] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans ⟨19, LInc_w0_1 (xs ++ s) r⟩ hr'⟩
  | @w11 xs _ ih =>
    intro r
    rcases ih ([0, 1, 0, 1, 0, 1] +> r) with ⟨r', hr'⟩
    exact ⟨r', stepStar_trans ⟨6, LInc_w11_1 (xs ++ s) r⟩ hr'⟩

def msb_13 : List LD :=
  [.W0, .W1, .W1, .W1, .W1, .W0, .W0, .W0, .W1, .W1, .W0, .W1, .W1]

def u8 : List LD := (runU 8 u0).getD []

def u8_pre' : List LD := ((lincspFinite u8).getD []).take 38

theorem runU_8_eq : runU 8 u0 = some u8 := by decide

theorem u8_lincsp_eq : lincspFinite u8 = some (u8_pre' ++ msb_13) := by decide

theorem u8_pre'_only011 : checkOnly011 u8_pre' = true := by decide

def c_msb_start : CCfg (Fin 2) (Fin 6) :=
  ⟨E, 1, encWords encWord msb_13 ++ [1, 1, 1, 1, 1, 1], [0, 1, 0, 1]⟩

def c_msb_halt : CCfg (Fin 2) (Fin 6) := (cmultiStep target_tm 896 c_msb_start).getD c_msb_start

theorem msb_13_halt (r : ListBlank (Fin 2)) :
    ∃ cfg, ((cfgL (Lmp msb_13) ([1] +> r)) [target_tm]⊢* cfg) ∧
      (step target_tm cfg).isNone := by
  have h_start : cfgL (Lmp msb_13) ([1] +> r) = evalCCfg r c_msb_start := by
    simp [cfgL, Lmp, encTape, c_msb_start, evalCCfg, evalWindow, listblank_append_assoc]
  have h_896 : cmultiStep target_tm 896 c_msb_start = some c_msb_halt := by decide
  have h_q : c_msb_halt.q = B := by decide
  have h_cur : c_msb_halt.cur = 1 := by decide
  refine ⟨evalCCfg r c_msb_halt, ?_, ?_⟩
  · rw [h_start]
    exact ⟨896, cmultiStep_sound 896 c_msb_start c_msb_halt r h_896⟩
  · simp [step, evalCCfg, evalWindow, h_q, h_cur, B, target_tm]

-- ============================================================================
-- Section 6.9: Top-Level Halting Theorem (`proved_is_halt`)
-- ============================================================================

theorem sol_is_halt (_ : True) : IsHalt target_tm := by
  rcases x2_to_x3 with ⟨m3, hm3, h23⟩
  have h_init_x3 := stepStar_trans init_to_x2 h23
  have hm3_split : m3 = 10 + ((m3 - 26) + 2 * 8) := by omega
  let T0 := ((([.W1, .W0] : List LD) ^ (m3 - 26)) ++ (([.W1, .W0] : List LD) ^ (2 * 8)))
  have h_T0 : ChainTail (0 + 8) T0 :=
    ChainTail_pow_pair (m3 - 26) .nil
  have h_x3_eq : ((([.W1, .W0] : List LD) ^ m3) ++ u0) =
      ((([.W1, .W0] : List LD) ^ 10) ++ (T0 ++ u0)) := by
    conv_lhs => rw [hm3_split, list_pow_add, list_pow_add]
    simp only [T0, List.append_assoc]
  rw [h_x3_eq] at h_init_x3
  rcases runU_steps 8 0 (by omega) h_T0 runU_8_eq with ⟨T8, h_T8, h_rounds⟩
  have h_to_8 := stepStar_trans h_init_x3 h_rounds
  rcases ChainTail_zero_lincsp h_T8 with ⟨nT, T8', h_lpT⟩
  have h_lpU := lincspFinite_sound u8_lincsp_eq
  rcases LIncsP_append h_lpT h_lpU with ⟨nTU, h_lpTU⟩
  rcases LIncsP_pow_10 10 h_lpTU with ⟨nAll, h_lpAll⟩
  have h_incs_final := LIncs_RC (LIncsP_to_LIncs h_lpAll) 2
  have h_to_inc := stepStar_trans h_to_8 h_incs_final
  have h_10T_only : Only011 ((([.W1, .W1] : List LD) ^ 10) ++ T8') := by
    rcases LIncsP_pow_10 10 h_lpT with ⟨_, h10T⟩
    exact LIncsP_only011 h10T
  let P_all := ((([.W1, .W1] : List LD) ^ 10) ++ T8') ++ u8_pre'
  have h_P_only : Only011 P_all :=
    Only011_append h_10T_only (checkOnly011_sound u8_pre'_only011)
  have h_assoc : ((([.W1, .W1] : List LD) ^ 10) ++ (T8' ++ (u8_pre' ++ msb_13))) =
      P_all ++ msb_13 := by
    simp only [P_all, List.append_assoc]
  rw [h_assoc] at h_to_inc
  rcases Only011_skip h_P_only msb_13
      ((([0, 1, 1] : List (Fin 2)) ^ (2 + 2 * nAll)) +> ([0, 1] +> default)) with ⟨r', h_skip⟩
  have h_to_msb := stepStar_trans h_to_inc h_skip
  rcases msb_13_halt r' with ⟨cfg_halt, h_halt_steps, h_is_none⟩
  exact ⟨cfg_halt, stepStar_trans h_to_msb h_halt_steps, h_is_none⟩

end Solution

/--
Halting theorem for Suspect 158 (Holdout #707):
The machine halts when started on the blank tape.
-/

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_halt : IsHalt target_tm := (Solution.sol_is_halt True.intro)

end BusyBeaver.M_1RB0LF_1RCHHH_1LD0RF_1RA0LE_0LD1LD_0RD0RB
