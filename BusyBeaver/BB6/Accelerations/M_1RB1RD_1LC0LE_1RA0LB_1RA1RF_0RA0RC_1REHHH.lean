/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---`
(https://wiki.bbchallenge.org/wiki/1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---, which redirects to the
wiki page of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`).

This machine is the transition table of `1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` restarted from
its state `C` and brought to tree normal form: reading its states `A`, `B`, `C`, `D`, `E`, `F` as
the states `C`, `D`, `E`, `F`, `B`, `A` of that machine, the two transition tables coincide, so both
machines run the same closed pair-stack system. The proof below is the mechanical relabelling of the
proof in
[`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA`](./M_1RBHHH_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA.lean);
only the blank-tape entry lemma `init_reaches_nontrivial` is specific to this start state.

<!-- hardness:begin -->
## Hardness

*Hardness class:* Wiki stack — trigger **as #85 (same table, started from its state `C`)**, growth
as #85, shield as #85.

*Verdict (heuristic; community analysis, see the wiki page):* same dynamics as
`1RB---_0RC0RE_1RD1RF_1LE0LB_1RC0LD_1RC1RA` (#85) (wiki: "when the TM starts on any starting state,
it exhibits the same probviously halting behaviour").

*Hazard:* as #85 (community estimate)

*Simulated horizon:* as #85

*Why it is hard:* the proof is the state relabelling of the #85 proof with its own blank-tape entry
(12 raw steps)

See `BusyBeaver.BB6.Hardness` for the vocabulary and the full table.
<!-- hardness:end -->
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH

open SixState Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1RE---"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Local Step Tactics and Pair-Stack Encodings -/

local macro "normalize" : tactic => `(tactic| (
  try simp only [ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "normalize_at" h:ident : tactic => `(tactic| (
  try simp only [ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one] at $h:ident))

local macro "step" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  refine ReachesPlus.head (by rfl) ?_
  simp only [Tape.move, Tape.write,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

private def encRight : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (a, b) :: L => (encRight L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1))

private def encLeft : List (ℕ × ℕ) → ListBlank (Fin 2)
  | [] => default
  | (d, b) :: R => (([1] : List (Fin 2)) ^ (1 * d + 1)) +> ((([0] : List (Fin 2)) ^ (1 + b % 1)) +>
      encLeft R)

@[simp] private theorem encRight_nil : encRight [] = default := rfl

@[simp] private theorem encRight_cons (a b : ℕ) (L : List (ℕ × ℕ)) :
    encRight ((a, b) :: L) = (encRight L <+ (([0] : List (Fin 2)) ^ (1 + b % 1))) <+
      (([1] : List (Fin 2)) ^ (1 * a + 1)) := rfl

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl

@[simp] private theorem encLeft_cons (d b : ℕ) (R : List (ℕ × ℕ)) :
    encLeft ((d, b) :: R) = (([1] : List (Fin 2)) ^ (1 * d + 1)) +>
      ((([0] : List (Fin 2)) ^ (1 + b % 1)) +> encLeft R) := rfl

private theorem encRight_mod1 (a b : ℕ) (L : List (ℕ × ℕ)) :
    encRight ((a, b) :: L) = encRight ((a, b % 1) :: L) := by
  simp only [encRight_cons, Nat.mod_mod]

private theorem encRight_succ (a b : ℕ) (L : List (ℕ × ℕ)) :
    encRight ((a + 1, b) :: L) = (1 : Fin 2) >> encRight ((a, b) :: L) := by
  simp only [encRight_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, ListBlank.append_assoc]
  rfl

private theorem encRight_d0_s0 (L : List (ℕ × ℕ)) :
    encRight ((0, 0) :: L) = (1 : Fin 2) >> (0 : Fin 2) >> encRight L := rfl

private theorem encRight_d1_s0 (L : List (ℕ × ℕ)) :
    encRight ((1, 0) :: L) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encRight L := rfl

private theorem encRight_run_s0 (a : ℕ) (L : List (ℕ × ℕ)) :
    encRight ((a, 0) :: L) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      encRight L) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encRight_succ, ih]; normalize

private theorem encLeft_mod1 (a b : ℕ) (R : List (ℕ × ℕ)) :
    encLeft ((a, b) :: R) = encLeft ((a, b % 1) :: R) := by
  simp only [encLeft_cons, Nat.mod_mod]

private theorem encLeft_succ (a b : ℕ) (R : List (ℕ × ℕ)) :
    encLeft ((a + 1, b) :: R) = (1 : Fin 2) >> encLeft ((a, b) :: R) := by
  simp only [encLeft_cons]
  rw [show 1 * (a + 1) + 1 = 1 + (1 * a + 1) by omega, list_pow_add, ListBlank.append_assoc]
  rfl

private theorem encLeft_d0_s0 (R : List (ℕ × ℕ)) :
    encLeft ((0, 0) :: R) = (1 : Fin 2) >> (0 : Fin 2) >> encLeft R := rfl

private theorem encLeft_d1_s0 (R : List (ℕ × ℕ)) :
    encLeft ((1, 0) :: R) = (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encLeft R := rfl

private theorem encLeft_run_s0 (a : ℕ) (R : List (ℕ × ℕ)) :
    encLeft ((a, 0) :: R) = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >>
      encLeft R) := by
  induction a with
  | zero => rfl
  | succ k ih => rw [encLeft_succ, ih]; normalize

@[simp] private theorem encRight_cons_one (L : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encRight L = encRight (bumpPairHead L) := by
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · simp [bumpPairHead, encRight]
  · exact (encRight_succ a b L').symm

@[simp] private theorem encLeft_cons_one (R : List (ℕ × ℕ)) :
    (1 : Fin 2) >> encLeft R = encLeft (bumpPairHead R) := by
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · simp [bumpPairHead, encLeft]
  · exact (encLeft_succ a b R').symm

local macro "finish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encLeft_nil, encRight_nil, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.head_default_fin,
    ListBlank.tail_default, ListBlank.cons_zero_default, list_pow_zero, list_pow_succ,
    List.nil_append, List.cons_append, zeros_append_default,
    Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  simp only [encLeft_cons_one, encRight_cons_one, multiStep_zero]
  try rfl))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

private def cfg_AR_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft R) {{A}}> (encRight L)

private def cfg_CL_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft R) <{{C}} (encRight L)

private def cfg_BL_0_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft R) <{{B}} ([0] +> encRight L)

private def cfg_BR_n_n (L R : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  (encLeft R) {{B}}> (encRight L)

private inductive StackMode
  | AR_n_n
  | CL_n_n
  | BL_0_n
  | BR_n_n
  deriving DecidableEq

private def evalStackCfg : StackMode → List (ℕ × ℕ) → List (ℕ × ℕ) → Cfg (Fin 2) (Fin 6)
  | .AR_n_n, L, R => cfg_AR_n_n R L
  | .CL_n_n, L, R => cfg_CL_n_n R L
  | .BL_0_n, L, R => cfg_BL_0_n R L
  | .BR_n_n, L, R => cfg_BR_n_n R L

private def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

/-! ## Inner Token System -/

private def encTokens : List ℕ → List (ℕ × ℕ) → ListBlank (Fin 2)
  | [], R3 => encLeft R3
  | k :: K, R3 => (([1] : List (Fin 2)) ^ k) +> ((0 : Fin 2) >> encTokens K R3)

@[simp] private theorem encTokens_nil (R3 : List (ℕ × ℕ)) : encTokens [] R3 = encLeft R3 := rfl

@[simp] private theorem encTokens_zero (K : List ℕ) (R3 : List (ℕ × ℕ)) :
    encTokens (0 :: K) R3 = (0 : Fin 2) >> encTokens K R3 := rfl

@[simp] private theorem encTokens_succ (k : ℕ) (K : List ℕ) (R3 : List (ℕ × ℕ)) :
    encTokens ((k + 1) :: K) R3 = (1 : Fin 2) >> encTokens (k :: K) R3 := by
  simp only [encTokens, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]

private def encRightNat : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: L => (1 : Fin 2) >> (([1] : List (Fin 2)) ^ a) +> ((0 : Fin 2) >> encRightNat L)

@[simp] private theorem encRightNat_nil : encRightNat [] = default := rfl

@[simp] private theorem encRightNat_zero (L : List ℕ) :
    encRightNat (0 :: L) = (1 : Fin 2) >> (0 : Fin 2) >> encRightNat L := rfl

@[simp] private theorem encRightNat_succ (a : ℕ) (L : List ℕ) :
    encRightNat ((a + 1) :: L) = (1 : Fin 2) >> encRightNat (a :: L) := by
  simp only [encRightNat, list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]

private theorem encRight_eq_nat (L : List (ℕ × ℕ)) : encRight L = encRightNat (L.map Prod.fst) := by
  induction L with
  | nil => rfl
  | cons p L ih =>
    rcases p with ⟨a, b⟩
    rw [encRight_mod1 a b L, Nat.mod_one b, encRight_run_s0 a L, ih]
    rfl

private theorem encRightNat_eq (L : List ℕ) : encRightNat L = encRight (L.map (fun x => (x, 0))) :=
  by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.map_cons, encRightNat, ih, encRight_run_s0]

@[simp] private theorem encRightNat_cons_one (L : List ℕ) :
    (1 : Fin 2) >> encRightNat L = encRightNat (bumpHead L) := by
  rcases L with _ | ⟨a, L'⟩
  · simp [bumpHead, encRightNat]
  · simp [bumpHead]

local macro "tstep" : tactic => `(tactic| (
  try refine ReachesPlus.to_star ?_
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  refine ReachesPlus.head (by rfl) ?_
  simp only [Tape.move, Tape.write, encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]))

local macro "tfinish" : tactic => `(tactic| (
  refine ⟨0, ?_⟩
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    encTokens_nil, encTokens_zero, encTokens_succ,
    encRightNat_nil, encRightNat_zero, encRightNat_succ, encLeft_nil, encRight_nil,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default,
    list_pow_zero, list_pow_succ, List.nil_append, List.cons_append,
    zeros_append_default, Nat.mul_zero, Nat.mul_add, Nat.mul_one]
  simp only [encRightNat_cons_one, encLeft_cons_one, encRight_cons_one, multiStep_zero]
  try rfl))

local macro "texecute" n:num : tactic => `(tactic| (
  iterate $n tstep
  tfinish))

private def tok_AR (K : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encTokens K R3) {{A}}> (encRightNat L)

private def tok_BR (K : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encTokens K R3) {{B}}> (encRightNat L)

private def tok_CL (K : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  (encTokens K R3) <{{C}} (encRightNat L)

private theorem tok_CL_exit_zero (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_CL [0] R3 L) [target]⊢⁺ cfg_AR_n_n (L.map (fun x => (x, 0))) (bumpPairHead R3) := by
  unfold tok_CL cfg_AR_n_n
  rw [← encRightNat_eq L]
  texecute 1

private theorem tok_CL_0_cons (k1 : ℕ) (K2 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_CL (0 :: k1 :: K2) R3 L) [target]⊢⁺ tok_AR ((k1 + 1) :: K2) R3 L := by
  unfold tok_CL tok_AR; texecute 1

private theorem tok_CL_1 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_CL (1 :: K1) R3 L) [target]⊢⁺ tok_CL K1 R3 (0 :: L) := by
  unfold tok_CL; texecute 2

private theorem tok_CL_2 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_CL (2 :: K1) R3 (0 :: L)) [target]⊢⁺ tok_CL K1 R3 (0 :: 1 :: L) := by
  unfold tok_CL; texecute 7

private theorem tok_CL_add3 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    (tok_CL ((k + 3) :: K1) R3 L) [target]⊢⁺ tok_BR (2 :: k :: K1) R3 L := by
  unfold tok_CL tok_BR; texecute 5

private theorem tok_BR_nil_8 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_BR (2 :: K1) R3 []) [target]⊢⁺ tok_CL K1 R3 [0, 1] := by
  unfold tok_BR tok_CL; texecute 8

private theorem tok_BR_zero (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L1 : List ℕ) :
    (tok_BR (2 :: K1) R3 (0 :: L1)) [target]⊢⁺ tok_BR (2 :: 1 :: K1) R3 L1 := by
  unfold tok_BR; texecute 4

private theorem tok_BR_1_nil_28 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_BR (2 :: K1) R3 [1]) [target]⊢⁺ tok_CL (1 :: K1) R3 [0, 0, 0, 1] := by
  unfold tok_BR tok_CL; texecute 28

private theorem tok_BR_succ (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L1 : List ℕ) :
    (tok_BR (2 :: K1) R3 ((a + 1) :: L1)) [target]⊢⁺ tok_AR (1 :: 1 :: K1) R3 (a :: L1) := by
  unfold tok_BR tok_AR; texecute 3

private theorem tok_AR_1_nil_9 (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_AR (1 :: K1) R3 []) [target]⊢⁺ tok_CL K1 R3 [0, 1] := by
  unfold tok_AR tok_CL; texecute 9

private theorem tok_AR_add2_nil_21 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_AR ((k + 2) :: K1) R3 []) [target]⊢⁺ tok_CL (k :: K1) R3 [0, 0, 1] := by
  unfold tok_AR tok_CL; texecute 21

private theorem tok_AR_zero (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L1 : List ℕ) :
    (tok_AR (k :: K1) R3 (0 :: L1)) [target]⊢⁺ tok_AR ((k + 2) :: K1) R3 L1 := by
  unfold tok_AR; texecute 2

private theorem tok_AR_1_nil_33 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_AR (k :: K1) R3 [1]) [target]⊢⁺ tok_CL (k :: K1) R3 [0, 0, 0, 1] := by
  unfold tok_AR tok_CL; texecute 33

private theorem tok_AR_1_0 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (L2 : List ℕ) :
    (tok_AR (k :: K1) R3 (1 :: 0 :: L2)) [target]⊢⁺ tok_AR (1 :: (k + 3) :: K1) R3 L2 := by
  unfold tok_AR; texecute 5

private theorem tok_AR_1_1_nil_25 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) :
    (tok_AR (k :: K1) R3 [1, 1]) [target]⊢⁺ tok_CL (k :: K1) R3 [0, 0, 1] := by
  unfold tok_AR tok_CL; texecute 25

private theorem tok_AR_1_1_cons_25 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (c : ℕ) (L3 : List ℕ) :
    (tok_AR (k :: K1) R3 (1 :: 1 :: c :: L3)) [target]⊢⁺
      tok_CL (k :: K1) R3 (0 :: 0 :: (c + 2) :: L3) := by
  unfold tok_AR tok_CL; texecute 25

private theorem tok_AR_1_add2 (k : ℕ) (K1 : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L2 : List ℕ) :
    (tok_AR (k :: K1) R3 (1 :: (a + 2) :: L2)) [target]⊢⁺ tok_BR (2 :: 1 :: k :: K1) R3 (a :: L2) :=
      by
  unfold tok_AR tok_BR; texecute 15

private theorem tok_AR_add2_halts (K : List ℕ) (R3 : List (ℕ × ℕ)) (a : ℕ) (L1 : List ℕ) :
    ∃ cfg_, ((tok_AR K R3 ((a + 2) :: L1)) [target]⊢⁺ cfg_) ∧
            (step target cfg_).isNone := by
  refine ⟨((1 : Fin 2) >> (1 : Fin 2) >> encTokens K R3) {{F}}> (encRightNat (a :: L1)), ?_,
    by simp only [encRightNat]; bb_halt⟩
  unfold tok_AR; texecute 2

/-! ## Weight and Lexicographic Measure -/

@[simp]
private def predNat : ℕ → ℕ
  | 0 => 0
  | a + 1 => a

@[simp]
private def wtL : List ℕ → ℕ
  | [] => 0
  | [a] => predNat a
  | a :: b :: L => a + wtL (b :: L)

@[simp] private theorem predNat_succ (a : ℕ) : predNat (a + 1) = a := rfl

@[simp] private theorem wtL_single (a : ℕ) : wtL [a] = predNat a := rfl

@[simp] private theorem wtL_cons_cons (a b : ℕ) (L : List ℕ) : wtL (a :: b :: L) =
  a + wtL (b :: L) := rfl

@[simp] private theorem wtL_zero_cons (L : List ℕ) : wtL (0 :: L) = wtL L := by
  rcases L with _ | ⟨b, L'⟩
  · rfl
  · exact Nat.zero_add (wtL (b :: L'))

private theorem wtL_1_1_cons (c : ℕ) (L3 : List ℕ) : wtL ((c + 2) :: L3) ≤ wtL (1 :: 1 :: c :: L3)
  := by
  rcases L3 with _ | ⟨d, L4⟩
  · rcases c with _ | c'
    · decide
    · simp only [wtL_cons_cons, wtL_single, predNat_succ]; omega
  · simp only [wtL_cons_cons]; omega

private theorem wtL_1_add2 (b : ℕ) (L2 : List ℕ) : wtL (b :: L2) + 2 ≤ wtL (1 :: (b + 2) :: L2) :=
  by
  rcases L2 with _ | ⟨d, L3⟩
  · rcases b with _ | b'
    · decide
    · simp only [wtL_cons_cons, wtL_single, predNat_succ]; omega
  · simp only [wtL_cons_cons]; omega

@[simp]
private def sumL : List ℕ → ℕ
  | [] => 0
  | a :: L => a + sumL L

@[simp]
private def countNonOne : List ℕ → ℕ
  | [] => 0
  | 0 :: K => 1 + countNonOne K
  | 1 :: K => countNonOne K
  | (_ + 2) :: K => 1 + countNonOne K

@[simp] private theorem countNonOne_zero (K : List ℕ) : countNonOne (0 :: K) = 1 + countNonOne K :=
  rfl

@[simp] private theorem countNonOne_one (K : List ℕ) : countNonOne (1 :: K) = countNonOne K := rfl

@[simp] private theorem countNonOne_add2 (k : ℕ) (K : List ℕ) : countNonOne ((k + 2) :: K) =
  1 + countNonOne K := rfl

private theorem countNonOne_cons_le (k : ℕ) (K : List ℕ) : countNonOne (k :: K) ≤ 1 + countNonOne K
  := by
  rcases k with _ | _ | k'
  · exact Nat.le_refl _
  · exact Nat.le_add_left _ 1
  · exact Nat.le_refl _

private theorem le_countNonOne_cons (k : ℕ) (K : List ℕ) : countNonOne K ≤ countNonOne (k :: K) :=
  by
  rcases k with _ | _ | k'
  · exact Nat.le_add_left _ 1
  · exact Nat.le_refl _
  · exact Nat.le_add_left _ 1

@[simp]
private def scores : List ℕ → List (ℕ × ℕ)
  | [] => []
  | 0 :: K => scores K ++ [(K.length, 0)]
  | 1 :: K => scores K
  | (k + 2) :: K => scores K ++ [(K.length, k + 2)]

@[simp] private theorem scores_zero (K : List ℕ) : scores (0 :: K) = scores K ++ [(K.length, 0)] :=
  rfl

@[simp] private theorem scores_one (K : List ℕ) : scores (1 :: K) = scores K := rfl

@[simp] private theorem scores_add2 (k : ℕ) (K : List ℕ) : scores ((k + 2) :: K) = scores K ++
  [(K.length, k + 2)] := rfl

private theorem scores_cons_ext (k : ℕ) (K : List ℕ) : ∃ ext, scores (k :: K) = scores K ++ ext :=
  by
  rcases k with _ | _ | k'
  · exact ⟨[(K.length, 0)], rfl⟩
  · exact ⟨[], (List.append_nil (scores K)).symm⟩
  · exact ⟨[(K.length, k' + 2)], rfl⟩

private theorem scores_length (K : List ℕ) : (scores K).length = countNonOne K := by
  induction K with
  | nil => rfl
  | cons k K ih =>
    rcases k with _ | _ | k'
    · simp only [scores_zero, countNonOne_zero, List.length_append, List.length_singleton,
        ih]; omega
    · exact ih
    · dsimp only [scores, countNonOne]
      rw [List.length_append, List.length_singleton, ih]
      omega

private def PairLt (p q : ℕ × ℕ) : Prop :=
  p.1 < q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)

private inductive BoundedLex : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | head {m : ℕ} {x y : ℕ × ℕ} {xs ys : List (ℕ × ℕ)} :
      PairLt x y → BoundedLex (m + 1) (x :: xs) (y :: ys)
  | cons {m : ℕ} {z : ℕ × ℕ} {xs ys : List (ℕ × ℕ)} :
      BoundedLex m xs ys → BoundedLex (m + 1) (z :: xs) (z :: ys)

private theorem boundedLex_append (P : List (ℕ × ℕ)) {m : ℕ} {x y : ℕ × ℕ} (rest ext : List (ℕ × ℕ))
    (hxy : PairLt x y) (hlen : P.length < m) :
    BoundedLex m (P ++ (x :: ext)) (P ++ (y :: rest)) := by
  induction P generalizing m with
  | nil =>
    rcases m with _ | m'
    · omega
    · exact BoundedLex.head hxy
  | cons z P' ih =>
    rcases m with _ | m'
    · simp at hlen
    · simp only [List.cons_append]
      exact BoundedLex.cons (ih (by simp at hlen; omega))

private theorem boundedLex_acc_snd (m a : ℕ)
    (ih_m : ∀ xs, Acc (BoundedLex m) xs)
    (ih_a : ∀ a' < a, ∀ b ys, Acc (BoundedLex (m + 1)) ((a', b) :: ys))
    (n : ℕ) :
    ∀ b ≤ n, ∀ ys, Acc (BoundedLex (m + 1)) ((a, b) :: ys) := by
  induction n with
  | zero =>
    intro b hb ys
    have hb0 : b = 0 := by omega
    subst hb0
    induction (ih_m ys) with
    | intro ys _ ih_ys =>
      refine Acc.intro ((a, 0) :: ys) (fun zs h => ?_)
      cases h with
      | @head _ x _ xs _ hlt =>
        rcases x with ⟨a', b'⟩
        rcases hlt with ha' | ⟨rfl, hb'⟩
        · exact ih_a a' ha' b' xs
        · dsimp at hb'; omega
      | cons hsub => exact ih_ys _ hsub
  | succ n ih_n =>
    intro b hb ys
    rcases Nat.of_le_succ hb with hle | rfl
    · exact ih_n b hle ys
    · induction (ih_m ys) with
      | intro ys _ ih_ys =>
        refine Acc.intro ((a, n + 1) :: ys) (fun zs h => ?_)
        cases h with
        | @head _ x _ xs _ hlt =>
          rcases x with ⟨a', b'⟩
          rcases hlt with ha' | ⟨rfl, hb'⟩
          · exact ih_a a' ha' b' xs
          · dsimp at hb'; exact ih_n b' (by omega) xs
        | cons hsub => exact ih_ys _ hsub

private theorem boundedLex_acc_fst (m : ℕ) (ih_m : ∀ xs, Acc (BoundedLex m) xs) (n : ℕ) :
    ∀ a ≤ n, ∀ b ys, Acc (BoundedLex (m + 1)) ((a, b) :: ys) := by
  induction n with
  | zero =>
    intro a ha b ys
    have ha0 : a = 0 := by omega
    subst ha0
    exact boundedLex_acc_snd m 0 ih_m (fun _ hlt => by omega) b b (Nat.le_refl b) ys
  | succ n ih_n =>
    intro a ha b ys
    rcases Nat.of_le_succ ha with hle | rfl
    · exact ih_n a hle b ys
    · exact boundedLex_acc_snd m (n + 1) ih_m (fun a' hlt => ih_n a' (by omega)) b b (Nat.le_refl b)
        ys

private theorem boundedLex_acc (m : ℕ) (xs : List (ℕ × ℕ)) : Acc (BoundedLex m) xs := by
  induction m generalizing xs with
  | zero => exact Acc.intro xs (fun _ h => nomatch h)
  | succ m ih_m =>
    rcases xs with _ | ⟨⟨a, b⟩, ys⟩
    · exact Acc.intro [] (fun _ h => nomatch h)
    · exact boundedLex_acc_fst m ih_m a a (Nat.le_refl a) b ys

/-! ## Bounce Lemmas for `AR` and `BR` -/

private theorem bounce_len (R3 : List (ℕ × ℕ)) (n : ℕ) :
    ∀ (L : List ℕ), 2 * sumL L + L.length ≤ n →
      (∀ (k0 : ℕ) (K_acc : List ℕ),
        (∃ cfg_, ((tok_AR ((k0 + 1) :: K_acc) R3 L) [target]⊢⁺ cfg_) ∧ (step target cfg_).isNone) ∨
        (∃ K_out L_out, ((tok_AR ((k0 + 1) :: K_acc) R3 L) [target]⊢⁺
          tok_CL K_out R3 (0 :: L_out)) ∧
          (∃ ext, scores K_out = scores K_acc ++ ext) ∧
          (countNonOne K_out + wtL L_out ≤ countNonOne K_acc + wtL L ∨
           (countNonOne K_out + wtL L_out ≤ countNonOne K_acc + 1 + wtL L ∧
            (k0 ≠ 0 → ∃ d ext, scores K_out = scores K_acc ++ ((K_acc.length, d) :: ext)))))) ∧
      (∀ (K_acc : List ℕ),
        (∃ cfg_, ((tok_BR (2 :: K_acc) R3 L) [target]⊢⁺ cfg_) ∧ (step target cfg_).isNone) ∨
        (∃ K_out L_out, ((tok_BR (2 :: K_acc) R3 L) [target]⊢⁺ tok_CL K_out R3 (0 :: L_out)) ∧
          countNonOne K_out + wtL L_out ≤ countNonOne K_acc + wtL L ∧
          (∃ ext, scores K_out = scores K_acc ++ ext))) := by
  induction n with
  | zero =>
    intro L hlen
    rcases L with _ | ⟨a, L1⟩
    · refine ⟨fun k0 K_acc => ?_, fun K_acc => ?_⟩
      · rcases k0 with _ | k'
        · refine Or.inr ⟨K_acc, [1], tok_AR_1_nil_9 K_acc R3, ⟨[], by simp⟩, Or.inl (by simp)⟩
        · rcases k' with _ | m
          · refine Or.inr ⟨0 :: K_acc, [0, 1], tok_AR_add2_nil_21 0 K_acc R3, ⟨[(K_acc.length, 0)],
              by simp⟩, Or.inr ⟨by simp; omega, fun _ => ⟨0, [], by simp⟩⟩⟩
          · rcases m with _ | m'
            · refine Or.inr ⟨1 :: K_acc, [0, 1], tok_AR_add2_nil_21 1 K_acc R3, ⟨[], by simp⟩,
                Or.inl (by simp)⟩
            · refine Or.inr ⟨(m' + 2) :: K_acc, [0, 1], tok_AR_add2_nil_21 (m' + 2) K_acc R3,
                ⟨[(K_acc.length, m' + 2)], by simp⟩, Or.inr ⟨by simp; omega, fun _ => ⟨m' + 2, [],
                  by simp⟩⟩⟩
      · exact Or.inr ⟨K_acc, [1], tok_BR_nil_8 K_acc R3, by simp, ⟨[], by simp⟩⟩
    · simp at hlen
  | succ n ih_n =>
    intro L hlen
    rcases Nat.of_le_succ hlen with hle | heq
    · exact ih_n L hle
    · refine ⟨fun k0 K_acc => ?_, fun K_acc => ?_⟩
      · rcases L with _ | ⟨a, L1⟩
        · simp at heq
        · rcases a with _ | _ | a'
          · have hstep1 := tok_AR_zero (k0 + 1) K_acc R3 L1
            rcases (ih_n L1 (by simp at heq ⊢; omega)).1 (k0 + 2) K_acc with
              ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, hext, hbr⟩
            · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
            · refine Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, hext, ?_⟩
              rcases hbr with hlt | ⟨hle, hd⟩
              · exact Or.inl (by simpa using hlt)
              · exact Or.inr ⟨by simpa using hle, fun _ => hd (by omega)⟩
          · rcases L1 with _ | ⟨b, L2⟩
            · rcases k0 with _ | k'
              · refine Or.inr ⟨1 :: K_acc, [0, 0, 1], tok_AR_1_nil_33 1 K_acc R3, ⟨[], by simp⟩,
                  Or.inl (by simp)⟩
              · refine Or.inr ⟨(k' + 2) :: K_acc, [0, 0, 1], tok_AR_1_nil_33 (k' + 2) K_acc R3,
                  ⟨[(K_acc.length, k' + 2)], by simp⟩, Or.inr ⟨by simp; omega, fun _ => ⟨k' + 2, [],
                    by simp⟩⟩⟩
            · rcases b with _ | _ | b'
              · have hstep1 := tok_AR_1_0 (k0 + 1) K_acc R3 L2
                rcases (ih_n L2 (by simp at heq ⊢; omega)).1 0 ((k0 + 4) :: K_acc) with
                  ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, ⟨ext, hsc⟩, hbr⟩
                · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
                · have hsc' : scores K_out = scores K_acc ++ ((K_acc.length, k0 + 4) :: ext) := by
                    simpa [scores_add2 (k0 + 2) K_acc, List.append_assoc] using hsc
                  refine Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, ⟨(K_acc.length,
                    k0 + 4) :: ext, hsc'⟩, ?_⟩
                  have hwt : wtL ((0 + 1) :: 0 :: L2) = 1 + wtL L2 := by simp
                  have hcnt : countNonOne ((k0 + 4) :: K_acc) = 1 + countNonOne K_acc :=
                    countNonOne_add2 (k0 + 2) K_acc
                  rcases hbr with hlt | ⟨hle, _⟩
                  · exact Or.inl (by omega)
                  · exact Or.inr ⟨by omega, fun _ => ⟨k0 + 4, ext, hsc'⟩⟩
              · rcases L2 with _ | ⟨c, L3⟩
                · have hstep := tok_AR_1_1_nil_25 (k0 + 1) K_acc R3
                  have hcnt := countNonOne_cons_le (k0 + 1) K_acc
                  refine Or.inr ⟨(k0 + 1) :: K_acc, [0, 1], hstep, scores_cons_ext (k0 + 1) K_acc,
                    Or.inl ?_⟩
                  simp at hcnt ⊢; omega
                · have hstep := tok_AR_1_1_cons_25 (k0 + 1) K_acc R3 c L3
                  have hwt : wtL ((c + 2) :: L3) ≤ wtL ((0 + 1) :: (0 + 1) :: c :: L3) :=
                    wtL_1_1_cons c L3
                  rcases k0 with _ | k'
                  · refine Or.inr ⟨1 :: K_acc, 0 :: (c + 2) :: L3, hstep, ⟨[], by simp⟩, Or.inl ?_⟩
                    simp only [countNonOne_one, wtL_zero_cons]; omega
                  · refine Or.inr ⟨(k' + 2) :: K_acc, 0 :: (c + 2) :: L3, hstep, ⟨[(K_acc.length,
                      k' + 2)], by simp⟩, Or.inr ⟨?_, fun _ => ⟨k' + 2, [], by simp⟩⟩⟩
                    simp only [countNonOne_add2, wtL_zero_cons]; omega
              · have hstep1 := tok_AR_1_add2 (k0 + 1) K_acc R3 b' L2
                rcases (ih_n (b' :: L2) (by simp at heq ⊢; omega)).2 (1 :: (k0 + 1) :: K_acc) with
                  ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, hle, ⟨ext, hsc⟩⟩
                · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
                · obtain ⟨ext0, hsc0⟩ := scores_cons_ext (k0 + 1) K_acc
                  have hcnt := countNonOne_cons_le (k0 + 1) K_acc
                  have hwt : wtL (b' :: L2) + 2 ≤ wtL ((0 + 1) :: (b' + 1 + 1) :: L2) :=
                    wtL_1_add2 b' L2
                  refine Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, ⟨ext0 ++ ext,
                    by simp [hsc, hsc0, List.append_assoc]⟩, Or.inl ?_⟩
                  simp only [countNonOne_one] at hle
                  omega
          · exact Or.inl (tok_AR_add2_halts ((k0 + 1) :: K_acc) R3 a' L1)
      · rcases L with _ | ⟨a, L1⟩
        · simp at heq
        · rcases a with _ | a'
          · have hstep1 := tok_BR_zero K_acc R3 L1
            rcases (ih_n L1 (by simp at heq ⊢; omega)).2 (1 :: K_acc) with
              ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, hle, ⟨ext, hsc⟩⟩
            · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
            · exact Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, by simpa using hle, ⟨ext,
                by simpa using hsc⟩⟩
          · rcases L1 with _ | ⟨b, L2⟩
            · rcases a' with _ | a''
              · exact Or.inr ⟨1 :: K_acc, [0, 0, 1], tok_BR_1_nil_28 K_acc R3, by simp, ⟨[],
                  by simp⟩⟩
              · have hstep1 := tok_BR_succ K_acc R3 (a'' + 1) []
                rcases (ih_n [a'' + 1] (by simp at heq ⊢; omega)).1 0 (1 :: K_acc) with
                  ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, ⟨ext, hsc⟩, hbr⟩
                · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
                · refine Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, ?_, ⟨ext,
                    by simpa using hsc⟩⟩
                  rcases hbr with hlt | ⟨hle, _⟩
                  · simp at hlt ⊢; omega
                  · simp at hle ⊢; omega
            · have hstep1 := tok_BR_succ K_acc R3 a' (b :: L2)
              rcases (ih_n (a' :: b :: L2) (by simp at heq ⊢; omega)).1 0 (1 :: K_acc) with
                ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, ⟨ext, hsc⟩, hbr⟩
              · exact Or.inl ⟨cfg_, ReachesPlus.trans hstep1 hstep2, hhalt⟩
              · refine Or.inr ⟨K_out, L_out, ReachesPlus.trans hstep1 hstep2, ?_, ⟨ext,
                  by simpa using hsc⟩⟩
                rcases hbr with hlt | ⟨hle, _⟩
                · simp at hlt ⊢; omega
                · simp at hle ⊢; omega

private theorem bounce_AR (R3 : List (ℕ × ℕ)) (k0 : ℕ) (K_acc : List ℕ) (L : List ℕ) :
    (∃ cfg_, ((tok_AR ((k0 + 1) :: K_acc) R3 L) [target]⊢⁺ cfg_) ∧ (step target cfg_).isNone) ∨
    (∃ K_out L_out, ((tok_AR ((k0 + 1) :: K_acc) R3 L) [target]⊢⁺ tok_CL K_out R3 (0 :: L_out)) ∧
      (∃ ext, scores K_out = scores K_acc ++ ext) ∧
      (countNonOne K_out + wtL L_out ≤ countNonOne K_acc + wtL L ∨
       (countNonOne K_out + wtL L_out ≤ countNonOne K_acc + 1 + wtL L ∧
        (k0 ≠ 0 → ∃ d ext, scores K_out = scores K_acc ++ ((K_acc.length, d) :: ext))))) :=
  (bounce_len R3 (2 * sumL L + L.length) L (Nat.le_refl _)).1 k0 K_acc

private theorem bounce_BR (R3 : List (ℕ × ℕ)) (K_acc : List ℕ) (L : List ℕ) :
    (∃ cfg_, ((tok_BR (2 :: K_acc) R3 L) [target]⊢⁺ cfg_) ∧ (step target cfg_).isNone) ∨
    (∃ K_out L_out, ((tok_BR (2 :: K_acc) R3 L) [target]⊢⁺ tok_CL K_out R3 (0 :: L_out)) ∧
      countNonOne K_out + wtL L_out ≤ countNonOne K_acc + wtL L ∧
      (∃ ext, scores K_out = scores K_acc ++ ext)) :=
  (bounce_len R3 (2 * sumL L + L.length) L (Nat.le_refl _)).2 K_acc

/-! ## Token System Termination -/

private theorem bl_step_macro_len (R3 : List (ℕ × ℕ)) (n : ℕ) :
    ∀ (K : List ℕ), K.length ≤ n → ∀ (L : List ℕ),
      (∃ cfg_, ((tok_CL K R3 (0 :: L)) [target]⊢* cfg_) ∧
               (IsInStackSystem cfg_ ∨ (step target cfg_).isNone)) ∨
      (∃ K' L', ((tok_CL K R3 (0 :: L)) [target]⊢⁺ tok_CL K' R3 (0 :: L')) ∧
                countNonOne K' + wtL L' < countNonOne K + wtL L) ∨
      (∃ K' L' P x y rest ext, ((tok_CL K R3 (0 :: L)) [target]⊢⁺ tok_CL K' R3 (0 :: L')) ∧
                countNonOne K' + wtL L' = countNonOne K + wtL L ∧ PairLt x y ∧
                scores K = P ++ (y :: rest) ∧ scores K' = P ++ (x :: ext)) := by
  induction n with
  | zero =>
    intro K hlen L
    cases K with
    | nil =>
      refine Or.inl ⟨cfg_CL_n_n ((0 :: L).map (fun x => (x, 0))) R3, ⟨0, ?_⟩,
        Or.inl ⟨.CL_n_n, R3, (0 :: L).map (fun x => (x, 0)), rfl⟩⟩
      unfold tok_CL cfg_CL_n_n
      rw [encTokens_nil, encRightNat_eq]
      rfl
    | cons _ _ => simp at hlen
  | succ n ih_n =>
    intro K hlen L
    rcases K with _ | ⟨k1, K1⟩
    · refine Or.inl ⟨cfg_CL_n_n ((0 :: L).map (fun x => (x, 0))) R3, ⟨0, ?_⟩,
        Or.inl ⟨.CL_n_n, R3, (0 :: L).map (fun x => (x, 0)), rfl⟩⟩
      unfold tok_CL cfg_CL_n_n
      rw [encTokens_nil, encRightNat_eq]
      rfl
    · rcases k1 with _ | _ | _ | k'
      · rcases K1 with _ | ⟨k2, K2⟩
        · exact Or.inl ⟨cfg_AR_n_n ((0 :: L).map (fun x => (x, 0))) (bumpPairHead R3),
            ReachesPlus.to_star (tok_CL_exit_zero R3 (0 :: L)),
            Or.inl ⟨.AR_n_n, bumpPairHead R3, (0 :: L).map (fun x => (x, 0)), rfl⟩⟩
        · have hstep1 :=
            ReachesPlus.trans (tok_CL_0_cons k2 K2 R3 (0 :: L)) (tok_AR_zero (k2 + 1) K2 R3 L)
          rcases bounce_AR R3 (k2 + 2) K2 L with
            ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, _, hbr⟩
          · exact Or.inl ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans hstep1 hstep2), Or.inr hhalt⟩
          · have hstep := ReachesPlus.trans hstep1 hstep2
            rcases hbr with hlt | ⟨hle, hd⟩
            · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
              have hcnt := le_countNonOne_cons k2 K2
              simp only [countNonOne_zero]; omega
            · rcases k2 with _ | _ | k2'
              · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
                simp only [countNonOne_zero]; omega
              · rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
                · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
                  simp only [Nat.zero_add, countNonOne_zero, countNonOne_one]; omega
                · obtain ⟨d, ext, hsc_out⟩ := hd (by omega)
                  refine Or.inr (Or.inr ⟨K_out, L_out, scores K2, (K2.length, d), ((1 :: K2).length,
                    0),
                    [], ext, hstep, by simp only [Nat.zero_add, countNonOne_zero,
                      countNonOne_one]; omega,
                    Or.inl (by simp), by simp, hsc_out⟩)
              · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
                simp only [countNonOne_zero, countNonOne_add2]; omega
      · have hstep1 := tok_CL_1 K1 R3 (0 :: L)
        rcases ih_n K1 (by simp at hlen; omega) (0 :: L) with
          ⟨cfg_, hstep2, hsys⟩ |
          ⟨K', L', hstep2, hlt⟩ |
          ⟨K', L', P, x, y, rest, ext, hstep2, heq, hxy, hsc1, hsc2⟩
        · exact Or.inl ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans_star hstep1 hstep2), hsys⟩
        · refine Or.inr (Or.inl ⟨K', L', ReachesPlus.trans hstep1 hstep2, ?_⟩)
          simpa using hlt
        · refine Or.inr (Or.inr ⟨K', L', P, x, y, rest, ext, ReachesPlus.trans hstep1 hstep2,
            by simpa using heq, hxy, by simpa using hsc1, hsc2⟩)
      · have hstep1 := tok_CL_2 K1 R3 L
        rcases L with _ | ⟨a, L1⟩
        · refine Or.inr (Or.inl ⟨K1, [1], hstep1, ?_⟩)
          simp
        · have hwt1 : wtL (1 :: a :: L1) = 1 + wtL (a :: L1) := by simp
          rcases ih_n K1 (by simp at hlen; omega) (1 :: a :: L1) with
            ⟨cfg_, hstep2, hsys⟩ |
            ⟨K', L', hstep2, hlt⟩ |
            ⟨K', L', P, x, y, rest, ext, hstep2, heq, hxy, hsc1, hsc2⟩
          · exact Or.inl ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans_star hstep1 hstep2), hsys⟩
          · refine Or.inr (Or.inl ⟨K', L', ReachesPlus.trans hstep1 hstep2, ?_⟩)
            simp only [countNonOne_add2 0 K1]; omega
          · refine Or.inr (Or.inr ⟨K', L', P, x, y, rest ++ [(K1.length, 2)], ext,
              ReachesPlus.trans hstep1 hstep2, by simp only [countNonOne_add2 0 K1]; omega,
              hxy, by simp [hsc1, List.append_assoc], hsc2⟩)
      · have hstep1 :=
          ReachesPlus.trans (tok_CL_add3 k' K1 R3 (0 :: L)) (tok_BR_zero (k' :: K1) R3 L)
        rcases bounce_BR R3 (1 :: k' :: K1) L with
          ⟨cfg_, hstep2, hhalt⟩ | ⟨K_out, L_out, hstep2, hle, ⟨ext, hsc⟩⟩
        · exact Or.inl ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans hstep1 hstep2), Or.inr hhalt⟩
        · have hstep := ReachesPlus.trans hstep1 hstep2
          simp only [countNonOne_one, scores_one] at hle hsc
          rcases k' with _ | _ | k''
          · rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
            · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
              simp only [countNonOne_zero, countNonOne_add2] at hlt' ⊢; omega
            · refine Or.inr (Or.inr ⟨K_out, L_out, scores K1, (K1.length, 0), (K1.length, 3),
                [], ext, hstep, by simp only [countNonOne_zero, countNonOne_add2] at heq' ⊢; omega,
                Or.inr ⟨rfl, by simp⟩, by simp,
                  by simpa [List.append_assoc] using hsc⟩)
          · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
            simp only [Nat.zero_add, countNonOne_one, countNonOne_add2] at hle ⊢; omega
          · rcases Nat.lt_or_eq_of_le hle with hlt' | heq'
            · refine Or.inr (Or.inl ⟨K_out, L_out, hstep, ?_⟩)
              simp only [countNonOne_add2] at hlt' ⊢; omega
            · refine Or.inr (Or.inr ⟨K_out, L_out, scores K1, (K1.length, k'' + 2), (K1.length,
                k'' + 5),
                [], ext, hstep, by simp only [countNonOne_add2] at heq' ⊢; omega,
                Or.inr ⟨rfl, by simp⟩, by simp,
                  by simpa [List.append_assoc] using hsc⟩)

private theorem bl_terminates_acc (R3 : List (ℕ × ℕ)) (m : ℕ)
    (ih_m : ∀ (K : List ℕ) (L : List ℕ),
      countNonOne K + wtL L < m →
      ∃ cfg_, ((tok_CL K R3 (0 :: L)) [target]⊢* cfg_) ∧
              (IsInStackSystem cfg_ ∨ (step target cfg_).isNone))
    (S : List (ℕ × ℕ)) (hacc : Acc (BoundedLex m) S) :
    ∀ (K : List ℕ) (L : List ℕ),
      scores K = S → countNonOne K + wtL L = m →
      ∃ cfg_, ((tok_CL K R3 (0 :: L)) [target]⊢* cfg_) ∧
              (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  induction hacc with
  | intro S _ ih_acc =>
    intro K L hS hm
    rcases bl_step_macro_len R3 K.length K (Nat.le_refl K.length) L with
      ⟨cfg_, hstep, hsys⟩ |
      ⟨K', L', hstep, hlt⟩ |
      ⟨K', L', P, x, y, rest, ext, hstep, heq, hxy, hsc1, hsc2⟩
    · exact ⟨cfg_, hstep, hsys⟩
    · obtain ⟨cfg_, hstep2, hsys⟩ := ih_m K' L' (by omega)
      exact ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans_star hstep hstep2), hsys⟩
    · have hlenP : P.length < m := by
        have hlenK := scores_length K
        rw [hsc1, List.length_append, List.length_cons] at hlenK
        omega
      have hlex : BoundedLex m (scores K') S := by
        rw [← hS, hsc1, hsc2]
        exact boundedLex_append P rest ext hxy hlenP
      obtain ⟨cfg_, hstep2, hsys⟩ := ih_acc (scores K') hlex K' L' rfl (by omega)
      exact ⟨cfg_, ReachesPlus.to_star (ReachesPlus.trans_star hstep hstep2), hsys⟩

private theorem bl_terminates_le (R3 : List (ℕ × ℕ)) (n : ℕ) :
    ∀ (m : ℕ), m ≤ n → ∀ (K : List ℕ) (L : List ℕ),
      countNonOne K + wtL L = m →
      ∃ cfg_, ((tok_CL K R3 (0 :: L)) [target]⊢* cfg_) ∧
              (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  induction n with
  | zero =>
    intro m hm K L hM
    have hm0 : m = 0 := by omega
    subst hm0
    exact bl_terminates_acc R3 0 (fun _ _ hlt => by omega) (scores K) (boundedLex_acc 0 (scores K))
      K L rfl hM
  | succ n ih_n =>
    intro m hm K L hM
    rcases Nat.of_le_succ hm with hle | rfl
    · exact ih_n m hle K L hM
    · refine bl_terminates_acc R3 (n + 1) (fun K' L' hlt => ?_)
        (scores K) (boundedLex_acc (n + 1) (scores K)) K L rfl hM
      exact ih_n (countNonOne K' + wtL L') (by omega) K' L' rfl

private theorem tok_BR_2_0_closed (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ cfg_, ((tok_BR [2, 0] R3 L) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases bounce_BR R3 [0] L with ⟨cfg_, hstep, hhalt⟩ | ⟨K_out, L_out, hstep, _, _⟩
  · exact ⟨cfg_, hstep, Or.inr hhalt⟩
  · obtain ⟨cfg_, hstep2, hsys⟩ := bl_terminates_le R3 (countNonOne K_out + wtL L_out)
      (countNonOne K_out + wtL L_out) (Nat.le_refl _) K_out L_out rfl
    exact ⟨cfg_, ReachesPlus.trans_star hstep hstep2, hsys⟩

private theorem tok_AR_1_0_closed (R3 : List (ℕ × ℕ)) (L : List ℕ) :
    ∃ cfg_, ((tok_AR [1, 0] R3 L) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases bounce_AR R3 0 [0] L with ⟨cfg_, hstep, hhalt⟩ | ⟨K_out, L_out, hstep, _, _⟩
  · exact ⟨cfg_, hstep, Or.inr hhalt⟩
  · obtain ⟨cfg_, hstep2, hsys⟩ := bl_terminates_le R3 (countNonOne K_out + wtL L_out)
      (countNonOne K_out + wtL L_out) (Nat.le_refl _) K_out L_out rfl
    exact ⟨cfg_, ReachesPlus.trans_star hstep hstep2, hsys⟩

/-! ## Mode Closure Theorems -/

private theorem mode_AR_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg_, ((cfg_AR_n_n L R) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · refine ⟨cfg_CL_n_n [(0, 0)] (bumpPairHead R), ?_, Or.inl ⟨.CL_n_n, bumpPairHead R, [(0, 0)],
      rfl⟩⟩
    unfold cfg_AR_n_n cfg_CL_n_n
    rw [encRight_d0_s0 [], ← encLeft_cons_one R]
    execute 2
  · rcases a1 with _ | a5
    · refine ⟨cfg_AR_n_n L3 (bumpPairHead (bumpPairHead R)), ?_, Or.inl ⟨.AR_n_n,
        bumpPairHead (bumpPairHead R), L3, rfl⟩⟩
      unfold cfg_AR_n_n
      rw [encRight_mod1 0 b2 L3, Nat.mod_one b2, encRight_d0_s0 L3,
        ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
      execute 2
    · rcases a5 with _ | a14
      · rcases L3 with _ | ⟨⟨a6, b7⟩, L8⟩
        · refine ⟨cfg_CL_n_n [(0, 0)] ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead R))), ?_,
            Or.inl ⟨.CL_n_n, (0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead R)), [(0, 0)], rfl⟩⟩
          unfold cfg_AR_n_n cfg_CL_n_n
          rw [encRight_mod1 1 b2 [], Nat.mod_one b2, encRight_d1_s0 [], encRight_d0_s0 [],
            encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead R))),
            ← encLeft_cons_one (bumpPairHead (bumpPairHead R)),
            ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
          execute 6
        · rcases a6 with _ | a10
          · refine ⟨cfg_AR_n_n L8 ((0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead R))), ?_,
              Or.inl ⟨.AR_n_n, (0, 0) :: bumpPairHead (bumpPairHead (bumpPairHead R)), L8, rfl⟩⟩
            unfold cfg_AR_n_n
            rw [encRight_mod1 1 b2 ((0, b7) :: L8), Nat.mod_one b2, encRight_d1_s0 ((0, b7) :: L8),
              encRight_mod1 0 b7 L8, Nat.mod_one b7, encRight_d0_s0 L8,
              encLeft_d0_s0 (bumpPairHead (bumpPairHead (bumpPairHead R))),
              ← encLeft_cons_one (bumpPairHead (bumpPairHead R)),
              ← encLeft_cons_one (bumpPairHead R), ← encLeft_cons_one R]
            execute 5
          · rcases a10 with _ | a11
            · refine ⟨cfg_CL_n_n (bumpPairHead L8) ((1, 0) :: (0, 0) :: R), ?_, Or.inl ⟨.CL_n_n, (1,
                0) :: (0, 0) :: R, bumpPairHead L8, rfl⟩⟩
              unfold cfg_AR_n_n cfg_CL_n_n
              rw [encRight_mod1 1 b2 ((1, b7) :: L8), Nat.mod_one b2,
                encRight_d1_s0 ((1, b7) :: L8), encRight_mod1 1 b7 L8, Nat.mod_one b7,
                encRight_d1_s0 L8, ← encRight_cons_one L8, encLeft_d1_s0 ((0, 0) :: R),
                encLeft_d0_s0 R]
              execute 16
            · refine ⟨cfg_BR_n_n ((a11, 0) :: L8) ((1, 0) :: (0, 0) :: R), ?_, Or.inl ⟨.BR_n_n, (1,
                0) :: (0, 0) :: R, (a11, 0) :: L8, rfl⟩⟩
              unfold cfg_AR_n_n cfg_BR_n_n
              rw [encRight_mod1 1 b2 ((a11 + 2, b7) :: L8), Nat.mod_one b2,
                encRight_d1_s0 ((a11 + 2, b7) :: L8), encRight_mod1 (a11 + 2) b7 L8,
                Nat.mod_one b7, encRight_succ (a11 + 1) 0 L8, encRight_succ a11 0 L8,
                encRight_run_s0 a11 L8, encLeft_d1_s0 ((0, 0) :: R), encLeft_d0_s0 R]
              execute 15
      · refine ⟨((1 : Fin 2) >> (1 : Fin 2) >> encLeft R) {{F}}> (encRight ((a14, 0) :: L3)), ?_,
          Or.inr (by rw [encRight_run_s0]; bb_halt)⟩
        unfold cfg_AR_n_n
        rw [encRight_mod1 (a14 + 2) b2 L3, Nat.mod_one b2, encRight_succ (a14 + 1) 0 L3,
          encRight_succ a14 0 L3]
        execute 2

private theorem mode_CL_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg_, ((cfg_CL_n_n L R) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases R with _ | ⟨⟨r1, b2⟩, R3⟩
  · refine ⟨cfg_AR_n_n L [(0, 0)], ?_, Or.inl ⟨.AR_n_n, [(0, 0)], L, rfl⟩⟩
    unfold cfg_CL_n_n cfg_AR_n_n
    rw [encLeft_d0_s0 []]
    execute 1
  · rcases r1 with _ | r5
    · refine ⟨cfg_CL_n_n ((0, 0) :: L) R3, ?_, Or.inl ⟨.CL_n_n, R3, (0, 0) :: L, rfl⟩⟩
      unfold cfg_CL_n_n
      rw [encLeft_mod1 0 b2 R3, Nat.mod_one b2, encLeft_d0_s0 R3, encRight_d0_s0 L]
      execute 2
    · refine ⟨cfg_BL_0_n L ((r5, 0) :: R3), ?_, Or.inl ⟨.BL_0_n, (r5, 0) :: R3, L, rfl⟩⟩
      unfold cfg_CL_n_n cfg_BL_0_n
      rw [encLeft_mod1 (r5 + 1) b2 R3, Nat.mod_one b2, encLeft_succ r5 0 R3, encLeft_run_s0 r5 R3]
      execute 1

private theorem mode_BL_0_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg_, ((cfg_BL_0_n L R) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases R with _ | ⟨⟨r1, b2⟩, R3⟩
  · refine ⟨cfg_AR_n_n L [(2, 0)], ?_, Or.inl ⟨.AR_n_n, [(2, 0)], L, rfl⟩⟩
    unfold cfg_BL_0_n cfg_AR_n_n
    rw [encLeft_succ 1 0 [], encLeft_d1_s0 []]
    execute 4
  · rcases r1 with _ | _ | r5
    · refine ⟨cfg_CL_n_n ((0, 0) :: bumpPairHead L) R3, ?_, Or.inl ⟨.CL_n_n, R3, (0,
        0) :: bumpPairHead L, rfl⟩⟩
      unfold cfg_BL_0_n cfg_CL_n_n
      rw [encLeft_mod1 0 b2 R3, Nat.mod_one b2, encLeft_d0_s0 R3, encRight_d0_s0 (bumpPairHead L),
        ← encRight_cons_one L]
      execute 6
    · obtain ⟨cfg_, hstep2, hsys⟩ := tok_BR_2_0_closed R3 (L.map Prod.fst)
      refine ⟨cfg_, ReachesPlus.trans ?_ hstep2, hsys⟩
      unfold cfg_BL_0_n tok_BR
      rw [encLeft_mod1 1 b2 R3, Nat.mod_one b2, encLeft_d1_s0 R3, encRight_eq_nat L,
        encTokens_succ, encTokens_succ, encTokens_zero, encTokens_zero, encTokens_nil]
      texecute 4
    · refine ⟨cfg_BR_n_n L ((1, 0) :: (r5, 0) :: R3), ?_, Or.inl ⟨.BR_n_n, (1, 0) :: (r5, 0) :: R3,
        L, rfl⟩⟩
      unfold cfg_BL_0_n cfg_BR_n_n
      rw [encLeft_mod1 (r5 + 2) b2 R3, Nat.mod_one b2, encLeft_succ (r5 + 1) 0 R3,
        encLeft_succ r5 0 R3, encLeft_run_s0 r5 R3, encLeft_d1_s0 ((r5, 0) :: R3),
        encLeft_run_s0 r5 R3]
      execute 4

private theorem mode_BR_n_n_closed (L R : List (ℕ × ℕ)) :
    ∃ cfg_, ((cfg_BR_n_n L R) [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases L with _ | ⟨⟨a1, b2⟩, L3⟩
  · refine ⟨cfg_CL_n_n [(0, 0)] R, ?_, Or.inl ⟨.CL_n_n, R, [(0, 0)], rfl⟩⟩
    unfold cfg_BR_n_n cfg_CL_n_n
    rw [encRight_d0_s0 []]
    execute 1
  · rcases R with _ | ⟨⟨r1, b4⟩, R3⟩
    · rcases a1 with _ | a5
      · refine ⟨cfg_CL_n_n (bumpPairHead L3) [(0, 0)], ?_, Or.inl ⟨.CL_n_n, [(0, 0)],
          bumpPairHead L3, rfl⟩⟩
        unfold cfg_BR_n_n cfg_CL_n_n
        rw [encRight_mod1 0 b2 L3, Nat.mod_one b2, encRight_d0_s0 L3, ← encRight_cons_one L3,
          encLeft_d0_s0 []]
        execute 4
      · refine ⟨cfg_BR_n_n ((a5, 0) :: L3) [(0, 0)], ?_, Or.inl ⟨.BR_n_n, [(0, 0)], (a5, 0) :: L3,
          rfl⟩⟩
        unfold cfg_BR_n_n
        rw [encRight_mod1 (a5 + 1) b2 L3, Nat.mod_one b2, encRight_succ a5 0 L3,
          encRight_run_s0 a5 L3, encLeft_d0_s0 []]
        execute 3
    · rcases r1 with _ | r5
      · rcases a1 with _ | a5
        · obtain ⟨cfg_, hstep2, hsys⟩ := tok_BR_2_0_closed R3 (L3.map Prod.fst)
          refine ⟨cfg_, ReachesPlus.trans ?_ hstep2, hsys⟩
          unfold cfg_BR_n_n tok_BR
          rw [encRight_mod1 0 b2 L3, Nat.mod_one b2, encRight_d0_s0 L3, encLeft_mod1 0 b4 R3,
            Nat.mod_one b4, encLeft_d0_s0 R3, encRight_eq_nat L3, encTokens_succ, encTokens_succ,
            encTokens_zero, encTokens_zero, encTokens_nil]
          texecute 4
        · obtain ⟨cfg_, hstep2, hsys⟩ := tok_AR_1_0_closed R3 (a5 :: L3.map Prod.fst)
          refine ⟨cfg_, ReachesPlus.trans ?_ hstep2, hsys⟩
          unfold cfg_BR_n_n tok_AR
          rw [encRight_mod1 (a5 + 1) b2 L3, Nat.mod_one b2, encRight_succ a5 0 L3,
            encRight_run_s0 a5 L3, encLeft_mod1 0 b4 R3, Nat.mod_one b4, encLeft_d0_s0 R3,
            encRight_eq_nat L3, encTokens_succ, encTokens_zero, encTokens_zero, encTokens_nil]
          change (((1 : Fin 2) >> (0 : Fin 2) >> encLeft R3) {{B}}> ((1 : Fin 2) >>
            encRightNat (a5 :: List.map Prod.fst L3))) [target]⊢⁺ (((1 : Fin 2) >> (0 : Fin 2) >>
              (0 : Fin 2) >> encLeft R3) {{A}}> (encRightNat (a5 :: List.map Prod.fst L3)))
          texecute 3
      · rcases a1 with _ | a5
        · refine ⟨cfg_BR_n_n L3 ((1, 0) :: (r5, 0) :: R3), ?_, Or.inl ⟨.BR_n_n, (1, 0) :: (r5,
            0) :: R3, L3, rfl⟩⟩
          unfold cfg_BR_n_n
          rw [encRight_mod1 0 b2 L3, Nat.mod_one b2, encRight_d0_s0 L3,
            encLeft_mod1 (r5 + 1) b4 R3, Nat.mod_one b4, encLeft_succ r5 0 R3,
            encLeft_run_s0 r5 R3, encLeft_d1_s0 ((r5, 0) :: R3), encLeft_run_s0 r5 R3]
          execute 4
        · refine ⟨cfg_AR_n_n ((a5, 0) :: L3) ((0, 0) :: (r5, 0) :: R3), ?_, Or.inl ⟨.AR_n_n, (0,
            0) :: (r5, 0) :: R3, (a5, 0) :: L3, rfl⟩⟩
          unfold cfg_BR_n_n cfg_AR_n_n
          rw [encRight_mod1 (a5 + 1) b2 L3, Nat.mod_one b2, encRight_succ a5 0 L3,
            encRight_run_s0 a5 L3, encLeft_mod1 (r5 + 1) b4 R3, Nat.mod_one b4,
            encLeft_succ r5 0 R3, encLeft_run_s0 r5 R3, encLeft_d0_s0 ((r5, 0) :: R3),
            encLeft_run_s0 r5 R3]
          execute 3

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem cfg) :
    ∃ cfg_, (cfg [target]⊢⁺ cfg_) ∧
            (IsInStackSystem cfg_ ∨ (step target cfg_).isNone) := by
  rcases h with ⟨m, R, L, rfl⟩
  cases m with
  | AR_n_n => exact mode_AR_n_n_closed L R
  | CL_n_n => exact mode_CL_n_n_closed L R
  | BL_0_n => exact mode_BL_0_n_closed L R
  | BR_n_n => exact mode_BR_n_n_closed L R

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg .BR_n_n [(3, 0)] [(0, 0), (0, 0)] := by
  have hL : encLeft [(3, 0)] =
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default := rfl
  have hR : encRight [(0, 0), (0, 0)] =
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default := rfl
  dsimp only [evalStackCfg, cfg_BR_n_n]
  rw [hL, hR]
  execute 12

private theorem step_CL_transfer (z : ℕ × ℕ) (L R : List (ℕ × ℕ)) :
    (evalStackCfg .CL_n_n ((0, 0) :: z :: L) R) [target]⊢⁺
      evalStackCfg .CL_n_n (z :: L) ((0, 0) :: R) := by
  dsimp only [evalStackCfg, cfg_CL_n_n]
  rw [encLeft_d0_s0 (z :: L), encRight_d0_s0 R]
  execute 2

private theorem encRight_head (a b : ℕ) (L : List (ℕ × ℕ)) :
    (encRight ((a, b) :: L)).head = 1 := by
  rw [encRight_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, list_pow_succ, List.cons_append]
  simp only [ListBlank.append_cons, ListBlank.head_cons]

private theorem encRight_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ L : List (ℕ × ℕ), encRight L ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro L h
  rcases L with _ | ⟨⟨a, b⟩, L'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encRight_mod1] at h
    have hb0 : b % 1 = 0 := Nat.mod_one b
    rw [hb0, encRight_run_s0] at h
    rcases a with _ | a'
    · rcases L' with _ | ⟨⟨a', b'⟩, L''⟩
      · have h2 := congrArg (fun s => s.tail.tail.tail.head) h
        simp at h2
      · have h1 := congrArg (fun s => s.tail.tail.head) h
        normalize_at h1
        rw [encRight_head a' b' L''] at h1; contradiction
    · have h1 := congrArg (fun s => s.tail.head) h
      normalize_at h1
      contradiction

private theorem encLeft_head (a b : ℕ) (R : List (ℕ × ℕ)) :
    (encLeft ((a, b) :: R)).head = 1 := by
  rw [encLeft_cons, show 1 * a + 1 = (1 * a + 0) + 1 by omega, list_pow_succ, List.cons_append]
  simp only [ListBlank.append_cons, ListBlank.head_cons]

private theorem encLeft_not_surjective :
    ∃ t : ListBlank (Fin 2), t.head = 1 ∧ ∀ R : List (ℕ × ℕ), encLeft R ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro R h
  rcases R with _ | ⟨⟨a, b⟩, R'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp at h1
  · rw [encLeft_mod1] at h
    have hb0 : b % 1 = 0 := Nat.mod_one b
    rw [hb0, encLeft_run_s0] at h
    rcases a with _ | a'
    · rcases R' with _ | ⟨⟨a', b'⟩, L''⟩
      · have h2 := congrArg (fun s => s.tail.tail.tail.head) h
        simp at h2
      · have h1 := congrArg (fun s => s.tail.tail.head) h
        normalize_at h1
        rw [encLeft_head a' b' L''] at h1; contradiction
    · have h1 := congrArg (fun s => s.tail.head) h
      normalize_at h1
      contradiction

private theorem valid_stack_modes : IsValidStackModes encLeft encRight evalStackCfg := by
  intro m
  cases m with
  | AR_n_n => exact ⟨A, .id [], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩
  | CL_n_n => exact ⟨C, .id [], .id [], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | BL_0_n => exact ⟨B, .id [], .id [0], by decide, by decide, Or.inr (Or.inl (fun _ _ => rfl))⟩
  | BR_n_n => exact ⟨B, .id [], .id [], by decide, by decide, Or.inr (Or.inr (fun _ _ => rfl))⟩


/-! ## Stack Reduction Witness -/

/-- `target` reduces to a closed 2nd-order digit-stack transition system. -/
theorem has_stack_reduction : HasStackReduction target := by
  refine ⟨StackMode, 1, 0, encLeft, encRight, evalStackCfg, IsInStackSystem,
    Or.inl ⟨rfl, rfl⟩, rfl, rfl,
    encLeft_head, encRight_head, encLeft_not_surjective, encRight_not_surjective,
    ⟨1, 1, 1, 1, 1, 1, 1, 1, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide, by decide,
      fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    ⟨[.AR_n_n, .CL_n_n, .BL_0_n, .BR_n_n], by decide, by intro m; cases m <;> decide⟩,
    valid_stack_modes,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    ⟨.BR_n_n, [(3, 0)], [(0, 0), (0, 0)], init_reaches_nontrivial,
      by decide, ⟨(3, 0), by decide, by decide⟩⟩,
    Or.inl ⟨.CL_n_n, .CL_n_n, (0, 0), id, ((0, 0) :: ·),
      fun _ => Nat.le_succ _, step_CL_transfer⟩,
    stack_system_closed⟩

end BusyBeaver.M_1RB1RD_1LC0LE_1RA0LB_1RA1RF_0RA0RC_1REHHH
