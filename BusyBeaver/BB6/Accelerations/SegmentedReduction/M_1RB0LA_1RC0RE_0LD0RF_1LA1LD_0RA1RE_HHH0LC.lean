/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Stack
public import BusyBeaver.WordRunStack

/-!
# Busy Beaver Holdout `1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC` (#433)

Formal `IsSegmentedCryptid` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC` (bbchallenge holdout #433).
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_HHH0LC

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 5, 0 => none
  | 5, 1 => some (some 2, Stmt.write 0 Dir.left)

private theorem target_eq_target_tm : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl


local notation "zB" => ListBlank (Fin 2)

open Counter

local macro "finish" : tactic => `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine stepPlus_stepStar ?_) <;>
    refine step_stepStar_stepPlus
      (by (try simp only [Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
      zero_cons_default, default_head, default_tail])
local macro "step1" : tactic => `(tactic| try (any_goals (first | finish | gstep)))
local macro "execute" : tactic =>
  `(tactic| (step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1; step1))

/-- Five head modes of Holdout `#433` (`1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`). -/
inductive SegMode where
  | mBR
  | mER0
  | mER1
  | mDL
  | mAL
deriving DecidableEq, Repr

/-- Left half-tape one-run suffix `1^(o+1) ++ [0]`. -/
def oWord (o : ℕ) : List (Fin 2) :=
  Nat.rec [1, 0] (fun _ acc => 1 :: acc) o

@[simp] private theorem oWord_zero : oWord 0 = [1, 0] := rfl
@[simp] private theorem oWord_succ (o : ℕ) : oWord (o + 1) = 1 :: oWord o := rfl

/-- Left half-tape parameterized run-pair word `0^z ++ 1^(o+1) ++ [0]`. -/
def lWord (p : ℕ × ℕ) : List (Fin 2) :=
  Nat.rec (oWord p.2) (fun _ acc => 0 :: acc) p.1

@[simp] private theorem lWord_zero (o : ℕ) : lWord (0, o) = oWord o := rfl
@[simp] private theorem lWord_succ (z o : ℕ) : lWord (z + 1, o) = 0 :: lWord (z, o) := rfl

/-- Right half-tape word `1^(d+1) ++ (if b then [0, 0] else [0])`, forbidding `[0, 0, 0, 1]`. -/
def rWord (p : ℕ × Bool) : List (Fin 2) :=
  Nat.rec (cond p.2 [1, 0, 0] [1, 0]) (fun _ acc => 1 :: acc) p.1

@[simp] private theorem rWord_zero_false : rWord (0, false) = [1, 0] := rfl
@[simp] private theorem rWord_zero_true : rWord (0, true) = [1, 0, 0] := rfl
@[simp] private theorem rWord_succ (d : ℕ) (b : Bool) :
    rWord (d + 1, b) = 1 :: rWord (d, b) := rfl

def encLeft (L : List (ℕ × ℕ)) : ListBlank (Fin 2) :=
  List.rec default (fun p _ acc => lWord p +> acc) L

@[simp] private theorem encLeft_nil : encLeft [] = default := rfl
@[simp] private theorem encLeft_cons (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    encLeft (p :: L) = lWord p +> encLeft L := rfl

def encRight (R : List (ℕ × Bool)) : ListBlank (Fin 2) :=
  List.rec default (fun p _ acc => rWord p +> acc) R

@[simp] private theorem encRight_nil : encRight [] = default := rfl
@[simp] private theorem encRight_cons (p : ℕ × Bool) (R : List (ℕ × Bool)) :
    encRight (p :: R) = rWord p +> encRight R := rfl

/-- Full right stack reconstructed from upper frames `Rs` and bottom accumulator `d_bot`. -/
def fullR (Rs : List (ℕ × Bool)) (d_bot : ℕ) : List (ℕ × Bool) :=
  Rs ++ [(d_bot, false)]

@[simp]
private theorem fullR_cons (p : ℕ × Bool) (Rs : List (ℕ × Bool)) (d_bot : ℕ) :
    fullR (p :: Rs) d_bot = p :: fullR Rs d_bot := rfl

private theorem fullR_ne_nil (Rs : List (ℕ × Bool)) (d_bot : ℕ) : fullR Rs d_bot ≠ [] := by
  simp [fullR]

@[simp]
private def bumpR : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => [(0, false)]
  | (d, b) :: R => (d + 1, b) :: R

@[simp]
private def bumpRs : List (ℕ × Bool) → ℕ → List (ℕ × Bool) × ℕ
  | [], d_bot => ([], d_bot + 1)
  | (d, b) :: Rs, d_bot => ((d + 1, b) :: Rs, d_bot)

private theorem fullR_bumpRs (Rs : List (ℕ × Bool)) (d_bot : ℕ) :
    fullR (bumpRs Rs d_bot).1 (bumpRs Rs d_bot).2 = bumpR (fullR Rs d_bot) := by
  rcases Rs with _ | ⟨⟨d, b⟩, Rs⟩ <;> rfl

@[simp]
private def bumpRN : ℕ → List (ℕ × Bool) → List (ℕ × Bool)
  | 0, R => R
  | n + 1, R => bumpRN n (bumpR R)

private theorem bumpRN_cons (n d : ℕ) (b : Bool) (R : List (ℕ × Bool)) :
    bumpRN n ((d, b) :: R) = (d + n, b) :: R := by
  induction n generalizing d with
  | zero => simp [bumpRN]
  | succ n ih =>
    simp only [bumpRN, bumpR, ih]
    congr 1; congr 1; omega

@[simp]
private def push100R : List (ℕ × Bool) → List (ℕ × Bool)
  | [] => [(0, false)]
  | p :: R => (0, true) :: p :: R

private theorem push100R_fullR (Rs : List (ℕ × Bool)) (d_bot : ℕ) :
    push100R (fullR Rs d_bot) = fullR ((0, true) :: Rs) d_bot := by
  cases Rs <;> rfl

@[simp]
private def push0L : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (z, o) :: L => (z + 1, o) :: L

@[simp]
private def push0LN : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, L => L
  | n + 1, L => push0LN n (push0L L)

private theorem push0LN_cons (n z o : ℕ) (L : List (ℕ × ℕ)) :
    push0LN n ((z, o) :: L) = (z + n, o) :: L := by
  induction n generalizing z with
  | zero => simp [push0LN]
  | succ n ih =>
    simp only [push0LN, push0L, ih]
    congr 1; congr 1; omega

@[simp]
private def push1L : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (0, o) :: L => (0, o + 1) :: L
  | (z + 1, o) :: L => (0, 0) :: (z, o) :: L

@[simp]
private def push1LN : ℕ → List (ℕ × ℕ) → List (ℕ × ℕ)
  | 0, L => L
  | n + 1, L => push1LN n (push1L L)

private theorem push1LN_zero_cons (n o : ℕ) (L : List (ℕ × ℕ)) :
    push1LN n ((0, o) :: L) = (0, o + n) :: L := by
  induction n generalizing o with
  | zero => simp [push1LN]
  | succ n ih =>
    simp only [push1LN, push1L, ih]
    congr 1; congr 1; omega

private theorem push1LN_succ2_nil (d : ℕ) :
    push1LN (d + 2) [] = [(0, d + 1)] := by
  change push1LN (d + 1) (push1L []) = [(0, d + 1)]
  simp only [push1L, push1LN_zero_cons, Nat.zero_add]

private theorem push1LN_succ2_pos (d z o : ℕ) (L : List (ℕ × ℕ)) :
    push1LN (d + 2) ((z + 1, o) :: L) = (0, d + 1) :: (z, o) :: L := by
  change push1LN (d + 1) (push1L ((z + 1, o) :: L)) = (0, d + 1) :: (z, o) :: L
  simp only [push1L, push1LN_zero_cons, Nat.zero_add]

abbrev SegState := SegMode × List (ℕ × ℕ) × List (ℕ × Bool) × ℕ

@[simp]
def modeOf (s : SegState) : SegMode := s.1

@[simp]
def headD (R : List (ℕ × Bool)) : ℕ :=
  List.casesOn R 0 (fun p _ => p.1)

@[simp]
def validLt (Lt : List (ℕ × ℕ)) : Prop :=
  List.rec True (fun p _ acc => p.2 ≤ 6 ∧ acc) Lt

@[simp]
def validR (R : List (ℕ × Bool)) : Prop :=
  List.rec False (fun p tl acc =>
    List.casesOn tl
      (p.2 = false ∧ p.1 ≤ 1)
      (fun q _ =>
        Bool.casesOn p.2
          (p.1 ≤ 5 ∧ (2 ≤ p.1 → q.1 ≤ 1) ∧ (4 ≤ p.1 → q.1 = 0) ∧ acc)
          (p.1 ≤ 1 ∧ q.1 = 0 ∧ acc))) R

@[simp]
def validR_BR (R : List (ℕ × Bool)) : Prop :=
  List.casesOn R False (fun p tl =>
    List.casesOn tl
      (p.2 = false ∧ p.1 ≤ 2)
      (fun q _ =>
        Bool.casesOn p.2
          (p.1 ≤ 6 ∧ (3 ≤ p.1 → q.1 ≤ 1) ∧ (5 ≤ p.1 → q.1 = 0) ∧ validR tl)
          (p.1 ≤ 2 ∧ q.1 = 0 ∧ validR tl)))

@[simp]
def validR_DL (R : List (ℕ × Bool)) : Prop :=
  List.casesOn R False (fun p tl =>
    List.casesOn tl
      (p.2 = false ∧ 1 ≤ p.1 ∧ p.1 ≤ 3)
      (fun q _ =>
        Bool.casesOn p.2
          (1 ≤ p.1 ∧ p.1 ≤ 7 ∧ (4 ≤ p.1 → q.1 ≤ 1) ∧ (6 ≤ p.1 → q.1 = 0) ∧ validR tl)
          (1 ≤ p.1 ∧ p.1 ≤ 3 ∧ q.1 = 0 ∧ validR tl)))

@[simp]
def ValidSeg (s : SegState) : Prop :=
  Prod.casesOn s fun m rest =>
    Prod.casesOn rest fun L rest2 =>
      Prod.casesOn rest2 fun Rs d_bot =>
        match m with
        | .mBR =>
            let R := fullR Rs d_bot
            validR_BR R ∧
            List.casesOn L True (fun hd Lt =>
              Prod.casesOn hd fun z o =>
                Nat.casesOn z
                  (validLt Lt ∧ o ≤ 6 ∧ (headD R = 0 ∨ (headD R = 1 ∧ 2 ≤ o ∧ o ≤ 4)))
                  (fun z' => Nat.casesOn z'
                    (validLt Lt ∧ o ≤ 8) (fun _ => validLt Lt ∧ o ≤ 6)))
        | .mER0 =>
            let R := fullR Rs d_bot
            validR R ∧
            List.casesOn L (headD R = 0) (fun hd Lt =>
              Prod.casesOn hd fun z o =>
                Nat.casesOn z
                  (validLt Lt ∧ o ≤ 5 ∧ (headD R = 0 ∨ (headD R = 1 ∧ 1 ≤ o ∧ o ≤ 3)))
                  (fun z' => Nat.casesOn z'
                    (validLt Lt ∧ o ≤ 6 ∧ headD R ≤ 1)
                    (fun _ => validLt Lt ∧ o ≤ 6 ∧ headD R = 0)))
        | .mER1 =>
            List.casesOn Rs False (fun hd Rs' =>
              Prod.casesOn hd fun d₀ b₀ =>
                let Rt := fullR Rs' d_bot
                b₀ = false ∧ validR Rt ∧
                List.casesOn L
                  (d₀ ≤ 5 ∧ (2 ≤ d₀ → headD Rt ≤ 1) ∧ (4 ≤ d₀ → headD Rt = 0))
                  (fun p Lt =>
                    Prod.casesOn p fun z o =>
                      Nat.casesOn z
                        (validLt Lt ∧ o ≤ 4 ∧ d₀ = 0 ∧ headD Rt ≤ 1 ∧ (3 ≤ o → headD Rt = 0))
                        (fun _ => validLt Lt ∧ o ≤ 6 ∧ d₀ ≤ 5 ∧
                          (2 ≤ d₀ → headD Rt ≤ 1) ∧ (4 ≤ d₀ → headD Rt = 0))))
        | .mDL =>
            validR_DL (fullR Rs d_bot) ∧
            List.casesOn L True (fun hd Lt =>
              Prod.casesOn hd fun z o =>
                Nat.casesOn z False (fun _ => validLt Lt ∧ o ≤ 6))
        | .mAL =>
            let R := fullR Rs d_bot
            validR R ∧
            List.casesOn L False (fun hd Lt =>
              Prod.casesOn hd fun z o =>
                Nat.casesOn z
                  (validLt Lt ∧ 2 ≤ o ∧ o ≤ 8 ∧ (7 ≤ o → headD R = 0) ∧
                    (5 ≤ o → headD R ≤ 1))
                  (fun _ => False))

@[simp]
def segsL (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.2.1.map rWord), .reg [1] s.2.2.2, .gadget [1, 0]]

@[simp]
def segsR (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.1.map lWord)]

private theorem append_assoc_blank (a b : List (Fin 2)) (s : zB) :
    (a ++ b) +> s = a +> (b +> s) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

private theorem reg_gadget_eq_encRight_bot (d_bot : ℕ) :
    (([1] : List (Fin 2)) ^ d_bot) +> ([1, 0] +> (default : zB)) = encRight [(d_bot, false)] := by
  induction d_bot with
  | zero => simp [ListBlank.append]
  | succ d ih =>
    rw [Counter.pow_succ_list, append_assoc_blank]
    simp only [encRight_nil, encRight_cons, rWord_succ,
      ListBlank.append] at ih ⊢
    exact congrArg ((1 : Fin 2) >> ·) ih

private theorem evalSegRegion_lWord (L : List (ℕ × ℕ)) :
    evalSegRegion (.finWord (L.map lWord)) +> (default : zB) = encLeft L := by
  induction L with
  | nil => simp [evalSegRegion]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, encLeft_cons, ← ih]
    exact append_assoc_blank (lWord p) (evalSegRegion (.finWord (rest.map lWord))) default

private theorem evalSegRegion_rWord_tail (Rs : List (ℕ × Bool)) (d_bot : ℕ) :
    evalSegRegion (.finWord (Rs.map rWord)) +> encRight [(d_bot, false)] =
      encRight (fullR Rs d_bot) := by
  induction Rs with
  | nil => simp [evalSegRegion, fullR]
  | cons p rest ih =>
    simp only [List.map_cons, evalSegRegion, fullR_cons]
    change (rWord p ++ evalSegRegion (.finWord (rest.map rWord))) +> encRight [(d_bot, false)] =
      rWord p +> encRight (fullR rest d_bot)
    rw [← ih]
    exact append_assoc_blank (rWord p) (evalSegRegion (.finWord (rest.map rWord))) _

@[simp]
private theorem evalSegmentedHalf_segsL (m : SegMode) (L : List (ℕ × ℕ)) (Rs : List (ℕ × Bool))
  (d_bot : ℕ) :
    evalSegmentedHalf (segsL (m, L, Rs, d_bot)) = encRight (fullR Rs d_bot) := by
  simp only [segsL, evalSegmentedHalf, evalSegRegion, reg_gadget_eq_encRight_bot]
  exact evalSegRegion_rWord_tail Rs d_bot

@[simp]
private theorem evalSegmentedHalf_segsR (m : SegMode) (L : List (ℕ × ℕ)) (Rs : List (ℕ × Bool))
  (d_bot : ℕ) :
    evalSegmentedHalf (segsR (m, L, Rs, d_bot)) = encLeft L :=
  evalSegRegion_lWord L

-- 1. Right Nowhere-Dense Proof (`NoFactor [0, 0, 0, 1]`)

private theorem encRight_nth_zero (p : ℕ × Bool) (R : List (ℕ × Bool)) :
    (encRight (p :: R)).nth 0 = 1 := by
  rcases p with ⟨_ | d, _ | _⟩ <;>
    simp only [encRight_cons, rWord_zero_false, rWord_zero_true, rWord_succ,
      ListBlank.append, WordRunStack.nth_cons_zero]

private theorem noFactor_0001_rWord_nil (d : ℕ) (b : Bool) :
    WordRunStack.NoFactor [0, 0, 0, 1] (rWord (d, b) +> (default : zB)) := by
  have hd : WordRunStack.NoFactor [0, 0, 0, 1] (default : zB) :=
    WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  induction d with
  | zero =>
    cases b <;> (
      simp only [rWord_zero_false, rWord_zero_true, ListBlank.append, zero_cons_default]
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) default hd 0
        (by decide) (by rw [WordRunStack.nth_cons_zero]; decide))
  | succ d ih =>
    simp only [rWord_succ, ListBlank.append]
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_0001_rWord_cons (d : ℕ) (b : Bool) (t : zB) (ht0 : t.nth 0 = 1)
    (ht : WordRunStack.NoFactor [0, 0, 0, 1] t) :
    WordRunStack.NoFactor [0, 0, 0, 1] (rWord (d, b) +> t) := by
  induction d with
  | zero =>
    cases b with
    | false =>
      simp only [rWord_zero_false, ListBlank.append]
      have h0 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
          (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h0 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    | true =>
      simp only [rWord_zero_true, ListBlank.append]
      have h0 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) t ht 1 (by decide)
          (by rw [WordRunStack.nth_cons_succ, ht0]; decide)
      have h00 : WordRunStack.NoFactor [0, 0, 0, 1] ((0 : Fin 2) >> (0 : Fin 2) >> t) :=
        WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (0 : Fin 2) _ h0 2 (by decide)
          (by rw [WordRunStack.nth_cons_succ, WordRunStack.nth_cons_succ, ht0]; decide)
      exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ h00 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
  | succ d ih =>
    simp only [rWord_succ, ListBlank.append]
    exact WordRunStack.noFactor_cons_of_nth_ne [0, 0, 0, 1] (1 : Fin 2) _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

private theorem noFactor_0001_encRight :
    ∀ R : List (ℕ × Bool), WordRunStack.NoFactor [0, 0, 0, 1] (encRight R)
  | [] => WordRunStack.noFactor_default [0, 0, 0, 1] 3 (by decide) (by decide)
  | [(d, b)] => noFactor_0001_rWord_nil d b
  | (d, b) :: p :: R =>
    noFactor_0001_rWord_cons d b (encRight (p :: R)) (encRight_nth_zero p R)
      (noFactor_0001_encRight (p :: R))

private theorem segsL_nowhere_dense : IsNowhereDenseHalf ValidSeg segsL :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsL [0, 0, 0, 1]
    (fun ⟨_, _, Rs, d_bot⟩ _ => by
      rw [evalSegmentedHalf_segsL]
      exact noFactor_0001_encRight (fullR Rs d_bot))

-- 2. Left Nowhere-Dense Proof (`NoFactor [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]`)

private abbrev wOnes10 : List (Fin 2) := [1, 1, 1, 1, 1, 1, 1, 1, 1, 1]

private theorem oWord_nth_succ (o : ℕ) (t : zB) : (oWord o +> t).nth (o + 1) = 0 := by
  induction o with
  | zero =>
    simp only [oWord_zero, ListBlank.append, WordRunStack.nth_cons_succ,
      WordRunStack.nth_cons_zero]
  | succ o ih =>
    simp only [oWord_succ, ListBlank.append]
    rw [WordRunStack.nth_cons_succ]
    exact ih

private theorem noFactor_wOnes10_oWord (o : ℕ) (ho : o ≤ 8) (t : zB)
    (ht : WordRunStack.NoFactor wOnes10 t) :
    WordRunStack.NoFactor wOnes10 (oWord o +> t) := by
  induction o with
  | zero =>
    simp only [oWord_zero, ListBlank.append]
    have h0 : WordRunStack.NoFactor wOnes10 ((0 : Fin 2) >> t) :=
      WordRunStack.noFactor_cons_of_nth_ne wOnes10 0 t ht 0 (by decide)
        (by rw [WordRunStack.nth_cons_zero]; decide)
    exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ h0 1 (by decide)
      (by rw [WordRunStack.nth_cons_succ, WordRunStack.nth_cons_zero]; decide)
  | succ o ih =>
    have ih' := ih (by omega)
    have hnth := oWord_nth_succ o t
    simp only [oWord_succ, ListBlank.append]
    rcases o with _ | _ | _ | _ | _ | _ | _ | _ | o
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 2 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 3 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 4 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 5 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 6 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 7 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 8 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 1 _ ih' 9 (by decide)
        (by rw [WordRunStack.nth_cons_succ, hnth]; decide)
    · omega

private theorem noFactor_wOnes10_lWord (z o : ℕ) (ho : o ≤ 8) (t : zB)
    (ht : WordRunStack.NoFactor wOnes10 t) :
    WordRunStack.NoFactor wOnes10 (lWord (z, o) +> t) := by
  induction z with
  | zero => simp only [lWord_zero]; exact noFactor_wOnes10_oWord o ho t ht
  | succ z ih =>
    simp only [lWord_succ, ListBlank.append]
    exact WordRunStack.noFactor_cons_of_nth_ne wOnes10 0 _ ih 0 (by decide)
      (by rw [WordRunStack.nth_cons_zero]; decide)

@[simp]
private def allOLe8 : List (ℕ × ℕ) → Prop
  | [] => True
  | (_, o) :: Lt => o ≤ 8 ∧ allOLe8 Lt

private theorem validLt_imp_allOLe8 : ∀ Lt : List (ℕ × ℕ), validLt Lt → allOLe8 Lt
  | [], _ => trivial
  | (_, _) :: Lt, ⟨ho, hlt⟩ => ⟨by omega, validLt_imp_allOLe8 Lt hlt⟩

private theorem validSeg_imp_allOLe8 (s : SegState) (hv : ValidSeg s) : allOLe8 s.2.1 := by
  rcases s with ⟨m, L, Rs, d_bot⟩
  cases m with
  | mBR =>
    rcases L with _ | ⟨⟨_ | _ | z, o⟩, Lt⟩
    · trivial
    · have ho := hv.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
    · exact ⟨hv.2.2, validLt_imp_allOLe8 Lt hv.2.1⟩
    · have ho := hv.2.2; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
  | mER0 =>
    rcases L with _ | ⟨⟨_ | _ | z, o⟩, Lt⟩
    · trivial
    · have ho := hv.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
    · have ho := hv.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
    · have ho := hv.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
  | mER1 =>
    rcases Rs with _ | ⟨⟨d₀, b₀⟩, Rs'⟩
    · exact False.elim hv
    · rcases L with _ | ⟨⟨_ | z, o⟩, Lt⟩
      · trivial
      · have ho := hv.2.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.2.1⟩
      · have ho := hv.2.2.2.1; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.2.1⟩
  | mDL =>
    rcases L with _ | ⟨⟨_ | z, o⟩, Lt⟩
    · trivial
    · exact False.elim hv.2
    · have ho := hv.2.2; exact ⟨by omega, validLt_imp_allOLe8 Lt hv.2.1⟩
  | mAL =>
    rcases L with _ | ⟨⟨_ | z, o⟩, Lt⟩
    · exact False.elim hv.2
    · exact ⟨hv.2.2.2.1, validLt_imp_allOLe8 Lt hv.2.1⟩
    · exact False.elim hv.2

private theorem noFactor_wOnes10_encLeft :
    ∀ (L : List (ℕ × ℕ)), allOLe8 L → WordRunStack.NoFactor wOnes10 (encLeft L)
  | [], _ => WordRunStack.noFactor_default wOnes10 0 (by decide) (by decide)
  | (z, o) :: Lt, ⟨ho, hlt⟩ =>
      noFactor_wOnes10_lWord z o ho (encLeft Lt) (noFactor_wOnes10_encLeft Lt hlt)

private theorem segsR_nowhere_dense : IsNowhereDenseHalf ValidSeg segsR :=
  WordRunStack.isNowhereDenseHalf_of_noFactor ValidSeg segsR wOnes10
    (fun s hv => by
      rcases s with ⟨m, L, Rs, d_bot⟩
      rw [evalSegmentedHalf_segsR]
      exact noFactor_wOnes10_encLeft L (validSeg_imp_allOLe8 (m, L, Rs, d_bot) hv))


-- 3. Mode Configuration Semantics

@[simp]
def evalSegCfg : SegMode → List (ℕ × ℕ) → List (ℕ × Bool) → Cfg (Fin 2) (Fin 6)
  | .mBR, L, R => (applyView (.id []) (encRight R)) {{1}}> (applyView (.id []) (encLeft L))
  | .mER0, L, R => (applyView (.id [0]) (encRight R)) {{4}}> (applyView (.id []) (encLeft L))
  | .mER1, L, R => (applyView (.id []) (encRight R)) {{4}}> (applyView (.id []) (encLeft L))
  | .mDL, L, R => (applyView (.id []) (encRight R)) <{{3}} (applyView (.id []) (encLeft L))
  | .mAL, L, R => (applyView (.id []) (encRight R)) <{{0}} (applyView (.id []) (encLeft L))

@[simp]
def evalCfg (s : SegState) : Cfg (Fin 2) (Fin 6) :=
  evalSegCfg s.1 s.2.1 (fullR s.2.2.1 s.2.2.2)

private theorem valid_seg_modes :
    ∀ m : SegMode, ∃ (q : Fin 6) (vL vR : HalfTapeView (Fin 2)),
      viewPrefixLen vL ≤ 8 ∧ viewPrefixLen vR ≤ 8 ∧
      ∀ s : SegState, ValidSeg s → modeOf s = m →
        (evalCfg s = ⟨some q, ⟨0,
          applyView vL (evalSegmentedHalf (segsL s)),
          applyView vR (evalSegmentedHalf (segsR s))⟩⟩) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) <{{q}}
          (applyView vR (evalSegmentedHalf (segsR s)))) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) {{q}}>
          (applyView vR (evalSegmentedHalf (segsR s)))) := by
  intro m
  cases m with
  | mBR =>
    refine ⟨1, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, Rs, d_bot⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mER0 =>
    refine ⟨4, .id [0], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, Rs, d_bot⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mER1 =>
    refine ⟨4, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, Rs, d_bot⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inr rfl)
  | mDL =>
    refine ⟨3, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, Rs, d_bot⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)
  | mAL =>
    refine ⟨0, .id [], .id [], by decide, by decide, ?_⟩
    rintro ⟨_, L, Rs, d_bot⟩ _ rfl
    rw [evalSegmentedHalf_segsL, evalSegmentedHalf_segsR]
    exact Or.inr (Or.inl rfl)

-- 4. Encoding Cons Rewrites & Macro Transition Lemmas

private theorem cons_one_encRight (R : List (ℕ × Bool)) :
    ((1 : Fin 2) >> encRight R) = encRight (bumpR R) := by
  rcases R with _ | ⟨⟨_ | d, b⟩, R⟩
  · simp [bumpR, ListBlank.append]
  · cases b <;> simp [bumpR, ListBlank.append]
  · simp [bumpR, ListBlank.append]

private theorem cons_100_encRight (R : List (ℕ × Bool)) :
    ((1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> encRight R) = encRight (push100R R) := by
  rcases R with _ | ⟨p, R⟩
  · simp [push100R, ListBlank.append]
  · simp [push100R, ListBlank.append]

private theorem cons_zero_encLeft (L : List (ℕ × ℕ)) :
    ((0 : Fin 2) >> encLeft L) = encLeft (push0L L) := by
  rcases L with _ | ⟨⟨z, o⟩, L⟩
  · simp [push0L]
  · simp [push0L]

private theorem cons_one_encLeft (L : List (ℕ × ℕ)) :
    ((1 : Fin 2) >> encLeft L) = encLeft (push1L L) := by
  rcases L with _ | ⟨⟨_ | z, o⟩, L⟩
  · simp [push1L, ListBlank.append]
  · simp [push1L]
  · simp [push1L, ListBlank.append]

@[simp]
private def s₀ : SegState := (.mBR, [], [], 0)

private theorem validSeg_s₀ : ValidSeg s₀ := by
  simp [s₀, ValidSeg, fullR, validR_BR]

private theorem step_mAL_nil (L : List (ℕ × ℕ)) :
    (evalSegCfg .mAL L []) [target_tm]⊢⁺ evalSegCfg .mBR L [(0, false)] := by
  dsimp only [evalSegCfg, applyView]
  simp only [encRight_nil, encRight_cons, rWord_zero_false,
    ListBlank.append, zero_cons_default, default_head, default_tail]
  execute

private theorem init_reaches_segmented_system :
    (init []) [target_tm]⊢⁺ evalCfg s₀ := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]
  simp only [evalCfg, s₀, fullR, List.nil_append, evalSegCfg, applyView, encLeft_nil,
    encRight_nil, encRight_cons, rWord_zero_false, ListBlank.append,
    zero_cons_default, default_head, default_tail]
  execute

private theorem step_mBR_nil (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR [] R) [target_tm]⊢⁺ evalSegCfg .mDL [] (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight]
  simp only [encLeft_nil, ListBlank.append, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons, default_head, default_tail]
  execute

private theorem step_mBR_0_0 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR ((0, 0) :: L) R) [target_tm]⊢⁺ evalSegCfg .mER0 (push0L L) R := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_zero_encLeft]
  simp only [encLeft_cons, lWord_zero, oWord_zero,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mBR_0_succ (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR ((0, o + 1) :: L) R) [target_tm]⊢⁺ evalSegCfg .mER0 ((0, o) :: L) R := by
  dsimp only [evalSegCfg, applyView]
  simp only [encLeft_cons, lWord_zero, oWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mBR_1_0_halts (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    ∃ cfg_h, ((evalSegCfg .mBR ((1, 0) :: L) R) [target_tm]⊢⁺ cfg_h) ∧
      (step target_tm cfg_h).isNone := by
  have h1 : (evalSegCfg .mBR ((1, 0) :: L) R) [target_tm]⊢⁺
      (((0 : Fin 2) >> (1 : Fin 2) >> encRight R) {{5}}> ((0 : Fin 2) >> encLeft L)) := by
    simp only [evalSegCfg, applyView, encLeft_cons, lWord_zero, lWord_succ,
      oWord_zero, ListBlank.append, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
    execute
  refine ⟨_, h1, ?_⟩
  simp [step, target_tm, Turing.ListBlank.head_cons]

private theorem step_mBR_1_1 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR ((1, 1) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mDL (push0L (push0L (push0L L))) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]
  rw [← cons_one_encRight, ← cons_zero_encLeft, ← cons_zero_encLeft, ← cons_zero_encLeft]
  simp only [encLeft_cons, lWord_zero, lWord_succ, oWord_zero, oWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mBR_1_succ2 (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR ((1, o + 2) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mDL ((2, o) :: L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight]
  simp only [encLeft_cons, lWord_zero, lWord_succ, oWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mBR_succ2 (z o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mBR ((z + 2, o) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mDL ((z + 1, o) :: L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight]
  simp only [encLeft_cons, lWord_succ, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER0_nil (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 [] R) [target_tm]⊢⁺ evalSegCfg .mBR [] (push100R R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_100_encRight]
  simp only [encLeft_nil, ListBlank.append, default_head, default_tail]
  execute

private theorem step_mER0_0_0 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 ((0, 0) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mER1 (push0L L) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_zero_encLeft]
  simp only [encLeft_cons, encRight_cons, lWord_zero,
    rWord_zero_false, oWord_zero, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER0_0_succ (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 ((0, o + 1) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mER1 ((0, o) :: L) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]
  simp only [encLeft_cons, encRight_cons, lWord_zero,
    rWord_zero_false, oWord_succ, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER0_1_0 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 ((1, 0) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR (push0L (push0L L)) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_zero_encLeft, ← cons_zero_encLeft]
  simp only [encLeft_cons, encRight_cons, lWord_zero, lWord_succ,
    rWord_zero_false, oWord_zero, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER0_1_succ (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 ((1, o + 1) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR ((1, o) :: L) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]
  simp only [encLeft_cons, encRight_cons, lWord_zero, lWord_succ,
    rWord_zero_false, oWord_succ, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER0_succ2 (z o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER0 ((z + 2, o) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR ((z, o) :: L) (push100R R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_100_encRight]
  simp only [encLeft_cons, lWord_succ, ListBlank.append,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER1_nil (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 [] R) [target_tm]⊢⁺ evalSegCfg .mBR [] ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]
  simp only [encLeft_nil, encRight_cons, rWord_zero_false,
    ListBlank.append, default_head, default_tail]
  execute

private theorem step_mER1_0_0 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((0, 0) :: L) R) [target_tm]⊢⁺ evalSegCfg .mER1 (push0L L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight, ← cons_zero_encLeft]
  simp only [encLeft_cons, lWord_zero, oWord_zero,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER1_0_succ (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((0, o + 1) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mER1 ((0, o) :: L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight]
  simp only [encLeft_cons, lWord_zero, oWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER1_sweep (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((0, o) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mER1 (push0L L) (bumpRN (o + 1) R) := by
  induction o generalizing R with
  | zero => exact step_mER1_0_0 L R
  | succ o ih => exact stepPlus_trans (step_mER1_0_succ o L R) (ih (bumpR R))

private theorem step_mER1_1_0 (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((1, 0) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR (push0L (push0L L)) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]
  rw [← cons_one_encRight, ← cons_zero_encLeft, ← cons_zero_encLeft]
  simp only [encLeft_cons, lWord_zero, lWord_succ, oWord_zero,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER1_1_succ (o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((1, o + 1) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR ((1, o) :: L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight]
  simp only [encLeft_cons, lWord_zero, lWord_succ, oWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mER1_succ2 (z o : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mER1 ((z + 2, o) :: L) R) [target_tm]⊢⁺
      evalSegCfg .mBR ((z, o) :: L) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]
  simp only [encLeft_cons, encRight_cons, lWord_succ,
    rWord_zero_false, ListBlank.append, Turing.ListBlank.head_cons,
    Turing.ListBlank.tail_cons]
  execute

private theorem step_mDL_0_false (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mDL L ((0, false) :: R)) [target_tm]⊢⁺
      evalSegCfg .mAL (push1L (push1L L)) R := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encLeft, ← cons_one_encLeft]
  simp only [encRight_cons, rWord_zero_false,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mDL_0_true (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mDL L ((0, true) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push1L (push1L L)) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]
  rw [← cons_one_encRight, ← cons_one_encLeft, ← cons_one_encLeft]
  simp only [encRight_cons, rWord_zero_true,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mDL_succ (d : ℕ) (b : Bool) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mDL L ((d + 1, b) :: R)) [target_tm]⊢⁺
      evalSegCfg .mDL (push1L L) ((d, b) :: R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encLeft]
  simp only [encRight_cons, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mDL_sweep_false (d : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mDL L ((d, false) :: R)) [target_tm]⊢⁺
      evalSegCfg .mAL (push1LN (d + 2) L) R := by
  induction d generalizing L with
  | zero => exact step_mDL_0_false L R
  | succ d ih => exact stepPlus_trans (step_mDL_succ d false L R) (ih (push1L L))

private theorem step_mDL_sweep_true (d : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mDL L ((d, true) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push1LN (d + 2) L) (bumpR R) := by
  induction d generalizing L with
  | zero => exact step_mDL_0_true L R
  | succ d ih => exact stepPlus_trans (step_mDL_succ d true L R) (ih (push1L L))

private theorem step_mAL_0_false (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mAL L ((0, false) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push0L L) (bumpR R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_one_encRight, ← cons_zero_encLeft]
  simp only [encRight_cons, rWord_zero_false,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAL_0_true (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mAL L ((0, true) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push0L L) ((0, false) :: R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_zero_encLeft]
  simp only [encRight_cons, rWord_zero_false, rWord_zero_true,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAL_succ (d : ℕ) (b : Bool) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mAL L ((d + 1, b) :: R)) [target_tm]⊢⁺
      evalSegCfg .mAL (push0L L) ((d, b) :: R) := by
  dsimp only [evalSegCfg, applyView]; rw [← cons_zero_encLeft]
  simp only [encRight_cons, rWord_succ,
    ListBlank.append, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  execute

private theorem step_mAL_sweep_false (d : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mAL L ((d, false) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push0LN (d + 1) L) (bumpR R) := by
  induction d generalizing L with
  | zero => exact step_mAL_0_false L R
  | succ d ih => exact stepPlus_trans (step_mAL_succ d false L R) (ih (push0L L))

private theorem step_mAL_sweep_true (d : ℕ) (L : List (ℕ × ℕ)) (R : List (ℕ × Bool)) :
    (evalSegCfg .mAL L ((d, true) :: R)) [target_tm]⊢⁺
      evalSegCfg .mBR (push0LN (d + 1) L) ((0, false) :: R) := by
  induction d generalizing L with
  | zero => exact step_mAL_0_true L R
  | succ d ih => exact stepPlus_trans (step_mAL_succ d true L R) (ih (push0L L))

-- 5. `List`-Inductive Multi-Frame Stack Transduction Sweep (`sweep_mAL_0true`)

/-- Peels any contiguous prefix of `(0, true)` (`[1, 0, 0]`) frames from `Rs`, pushing one
    `(1, 0)` (`[0, 1, 0]`) frame per peeled `(0, true)` frame onto `Lt` beneath `(0, 2)`. -/
@[simp]
private def peel0True : List (ℕ × Bool) → List (ℕ × ℕ) → List (ℕ × ℕ) × List (ℕ × Bool)
  | [], Lt => (Lt, [])
  | (d, b) :: Rs, Lt =>
      if d = 0 ∧ b = true then peel0True Rs ((1, 0) :: Lt)
      else (Lt, (d, b) :: Rs)

private theorem step_mAL_02_peel1 (Lt : List (ℕ × ℕ)) (R_tail : List (ℕ × Bool)) :
    (evalSegCfg .mAL ((0, 2) :: Lt) ((0, true) :: R_tail)) [target_tm]⊢⁺
      evalSegCfg .mAL ((0, 2) :: (1, 0) :: Lt) R_tail := by
  have h1 : (evalSegCfg .mAL ((0, 2) :: Lt) ((0, true) :: R_tail)) [target_tm]⊢⁺
      evalSegCfg .mBR ((1, 2) :: Lt) ((0, false) :: R_tail) :=
    step_mAL_0_true ((0, 2) :: Lt) R_tail
  have h2 : (evalSegCfg .mBR ((1, 2) :: Lt) ((0, false) :: R_tail)) [target_tm]⊢⁺
      evalSegCfg .mDL ((2, 0) :: Lt) ((1, false) :: R_tail) :=
    step_mBR_1_succ2 0 Lt ((0, false) :: R_tail)
  have h3 : (evalSegCfg .mDL ((2, 0) :: Lt) ((1, false) :: R_tail)) [target_tm]⊢⁺
      evalSegCfg .mAL ((0, 2) :: (1, 0) :: Lt) R_tail := by
    simpa only [push1LN_succ2_pos] using step_mDL_sweep_false 1 ((2, 0) :: Lt) R_tail
  exact stepPlus_trans h1 (stepPlus_trans h2 h3)

/-- Full `List`-inductive stack-transduction sweep in mode `.mAL`: peels an arbitrary prefix of
    `(0, true)` frames from `Rs` into `(1, 0)` frames on `L` in `[target_tm]⊢⁺`. -/
private theorem sweep_mAL_0true (Rs : List (ℕ × Bool)) (Lt : List (ℕ × ℕ)) (d_bot : ℕ) :
    (evalSegCfg .mAL ((0, 2) :: Lt) (fullR ((0, true) :: Rs) d_bot)) [target_tm]⊢⁺
      evalSegCfg .mAL ((0, 2) :: (peel0True Rs ((1, 0) :: Lt)).1)
        (fullR (peel0True Rs ((1, 0) :: Lt)).2 d_bot) := by
  induction Rs generalizing Lt with
  | nil =>
    simp only [peel0True, fullR_cons]
    exact step_mAL_02_peel1 Lt (fullR [] d_bot)
  | cons p Rs' ih =>
    rcases p with ⟨d, b⟩
    by_cases hdb : d = 0 ∧ b = true
    · rcases hdb with ⟨rfl, rfl⟩
      simp only [peel0True, and_self, ↓reduceIte]
      exact stepPlus_trans (step_mAL_02_peel1 Lt (fullR ((0, true) :: Rs') d_bot))
        (ih ((1, 0) :: Lt))
    · simp only [peel0True, hdb]
      exact step_mAL_02_peel1 Lt (fullR ((d, b) :: Rs') d_bot)

-- 6. Invariant Preservation Helpers

private theorem validR_BR_of_validR (R : List (ℕ × Bool)) (hR : validR R) : validR_BR R := by
  rcases R with _ | ⟨⟨d₁, _ | _⟩, _ | ⟨⟨d₂, b₂⟩, Rt⟩⟩
  · exact False.elim hR
  · simp only [validR, validR_BR] at hR ⊢; exact ⟨hR.1, by omega⟩
  · simp only [validR, validR_BR] at hR ⊢
    exact ⟨by omega, fun h => hR.2.1 (by omega), fun h => hR.2.2.1 (by omega), hR.2.2.2⟩
  · exact Bool.noConfusion hR.1
  · simp only [validR, validR_BR] at hR ⊢; exact ⟨by omega, hR.2.1, hR.2.2⟩

private theorem validR_of_validR_BR_le1 (R : List (ℕ × Bool)) (hR : validR_BR R) (hhd : headD R ≤
  1) :
    validR R := by
  rcases R with _ | ⟨⟨d₁, _ | _⟩, _ | ⟨⟨d₂, b₂⟩, Rt⟩⟩
  · exact False.elim hR
  · simp only [headD] at hhd; exact ⟨hR.1, hhd⟩
  · simp only [headD] at hhd
    exact ⟨by omega, fun h => by omega, fun h => by omega, hR.2.2.2⟩
  · exact Bool.noConfusion hR.1
  · simp only [headD] at hhd; exact ⟨hhd, hR.2.1, hR.2.2⟩

private theorem validR_BR_bumpR (R : List (ℕ × Bool)) (hR : validR R) : validR_BR (bumpR R) := by
  rcases R with _ | ⟨⟨d₁, _ | _⟩, _ | ⟨⟨d₂, b₂⟩, Rt⟩⟩
  · exact False.elim hR
  · simp only [validR, bumpR, validR_BR] at hR ⊢; exact ⟨hR.1, by omega⟩
  · simp only [validR, bumpR, validR_BR] at hR ⊢
    exact ⟨by omega, fun h => hR.2.1 (by omega), fun h => hR.2.2.1 (by omega), hR.2.2.2⟩
  · exact Bool.noConfusion hR.1
  · simp only [validR, bumpR, validR_BR] at hR ⊢; exact ⟨by omega, hR.2.1, hR.2.2⟩

private theorem validR_DL_bumpR (R : List (ℕ × Bool)) (hR : validR_BR R) : validR_DL (bumpR R) := by
  rcases R with _ | ⟨⟨d₁, _ | _⟩, _ | ⟨⟨d₂, b₂⟩, Rt⟩⟩
  · exact False.elim hR
  · simp only [validR_BR, bumpR, validR_DL] at hR ⊢; exact ⟨hR.1, by omega, by omega⟩
  · simp only [validR_BR, bumpR, validR_DL] at hR ⊢
    exact ⟨by omega, by omega, fun h => hR.2.1 (by omega), fun h => hR.2.2.1 (by omega), hR.2.2.2⟩
  · exact Bool.noConfusion hR.1
  · simp only [validR_BR, bumpR, validR_DL] at hR ⊢
    exact ⟨by omega, by omega, hR.2.1, hR.2.2⟩

private theorem validR_cons_0false (R : List (ℕ × Bool)) (hR : validR R) : validR ((0,
  false) :: R) := by
  rcases R with _ | ⟨⟨d₂, b₂⟩, Rt⟩
  · exact False.elim hR
  · exact ⟨by decide, fun h => by omega, fun h => by omega, hR⟩

private theorem validR_cons_0true (R : List (ℕ × Bool)) (hR : validR R) (hhd : headD R = 0) :
    validR ((0, true) :: R) := by
  rcases R with _ | ⟨⟨d₂, b₂⟩, Rt⟩
  · exact False.elim hR
  · simp only [headD] at hhd
    exact ⟨by decide, hhd, hR⟩

private theorem validR_cons_false_of_bounds (d₀ : ℕ) (Rt : List (ℕ × Bool))
    (hRt : validR Rt) (hd5 : d₀ ≤ 5)
    (h2 : 2 ≤ d₀ → headD Rt ≤ 1) (h4 : 4 ≤ d₀ → headD Rt = 0) :
    validR ((d₀, false) :: Rt) := by
  rcases Rt with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
  · exact False.elim hRt
  · simp only [headD] at h2 h4
    exact ⟨hd5, h2, h4, hRt⟩

private theorem peel0True_validLt :
    ∀ (Rs : List (ℕ × Bool)) (Lt : List (ℕ × ℕ)), validLt Lt → validLt (peel0True Rs Lt).1
  | [], _, hlt => hlt
  | (d, b) :: Rs, Lt, hlt => by
      by_cases hdb : d = 0 ∧ b = true
      · simp only [peel0True, hdb]
        exact peel0True_validLt Rs ((1, 0) :: Lt) ⟨by decide, hlt⟩
      · simp only [peel0True, hdb]
        exact hlt

private theorem peel0True_validR :
    ∀ (Rs : List (ℕ × Bool)) (Lt : List (ℕ × ℕ)) (d_bot : ℕ),
      validR (fullR Rs d_bot) → validR (fullR (peel0True Rs Lt).2 d_bot)
  | [], _, _, hR => hR
  | (d, b) :: Rs, Lt, d_bot, hR => by
      by_cases hdb : d = 0 ∧ b = true
      · rcases hdb with ⟨rfl, rfl⟩
        simp only [peel0True, and_self, ↓reduceIte]
        have hR' : validR (fullR Rs d_bot) := by
          rcases hRs : fullR Rs d_bot with _ | ⟨⟨d₂, b₂⟩, Rt⟩
          · exact absurd hRs (fullR_ne_nil Rs d_bot)
          · rw [fullR_cons, hRs] at hR; exact hR.2.2
        exact peel0True_validR Rs ((1, 0) :: Lt) d_bot hR'
      · simp only [peel0True, hdb]
        exact hR

@[simp]
private def ltAfterDL : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => []
  | (0, _) :: Lt => Lt
  | (z + 1, o) :: Lt => (z, o) :: Lt

private theorem push1LN_ar_eq (d : ℕ) (L : List (ℕ × ℕ))
    (hL : List.casesOn L True (fun hd Lt =>
      Prod.casesOn hd fun z o => Nat.casesOn z False (fun _ => validLt Lt ∧ o ≤ 6))) :
    push1LN (d + 2) L = (0, d + 1) :: ltAfterDL L ∧ validLt (ltAfterDL L) := by
  rcases L with _ | ⟨⟨_ | z, o⟩, Lt⟩
  · exact ⟨push1LN_succ2_nil d, trivial⟩
  · exact False.elim hL
  · exact ⟨push1LN_succ2_pos d z o Lt, hL.2, hL.1⟩

-- 7. Closedness & Soundness (`segmented_step_sound`, `segmented_system_closed`)

private theorem segmented_step_sound (m : SegMode) (L : List (ℕ × ℕ)) (Rs : List (ℕ × Bool)) (d_bot
  : ℕ)
    (hv : ValidSeg (m, L, Rs, d_bot)) :
    ∃ cfg', ((evalCfg (m, L, Rs, d_bot)) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) := by
  cases m with
  | mBR =>
    have hRBR : validR_BR (fullR Rs d_bot) := hv.1
    let R1 := bumpRs Rs d_bot
    have hR1_eq : fullR R1.1 R1.2 = bumpR (fullR Rs d_bot) := fullR_bumpRs Rs d_bot
    have hR1_DL : validR_DL (fullR R1.1 R1.2) := by
      rw [hR1_eq]; exact validR_DL_bumpR (fullR Rs d_bot) hRBR
    rcases L with _ | ⟨⟨_ | _ | z, o⟩, Lt⟩
    · refine ⟨evalCfg (.mDL, [], R1.1, R1.2), ?_,
        Or.inl ⟨(.mDL, [], R1.1, R1.2), ⟨hR1_DL, trivial⟩, rfl⟩⟩
      simp only [evalCfg]; rw [hR1_eq]; exact step_mBR_nil (fullR Rs d_bot)
    · cases o with
      | zero =>
        rcases hv.2 with ⟨hlt, _, hhd⟩
        have hhd0 : headD (fullR Rs d_bot) = 0 := by omega
        have hR : validR (fullR Rs d_bot) := validR_of_validR_BR_le1 _ hRBR (by omega)
        refine ⟨evalCfg (.mER0, push0L Lt, Rs, d_bot), step_mBR_0_0 Lt (fullR Rs d_bot),
          Or.inl ⟨(.mER0, push0L Lt, Rs, d_bot), ?_, rfl⟩⟩
        rcases Lt with _ | ⟨⟨_ | z', o'⟩, Lt'⟩
        · exact ⟨hR, hhd0⟩
        · exact ⟨hR, hlt.2, hlt.1, by omega⟩
        · exact ⟨hR, hlt.2, hlt.1, hhd0⟩
      | succ o =>
        rcases hv.2 with ⟨hlt, ho, hhd⟩
        have hR : validR (fullR Rs d_bot) := validR_of_validR_BR_le1 _ hRBR (by omega)
        exact ⟨evalCfg (.mER0, (0, o) :: Lt, Rs, d_bot),
          step_mBR_0_succ o Lt (fullR Rs d_bot),
          Or.inl ⟨(.mER0, (0, o) :: Lt, Rs, d_bot), ⟨hR, hlt, by omega, by omega⟩, rfl⟩⟩
    · rcases o with _ | _ | o
      · rcases step_mBR_1_0_halts Lt (fullR Rs d_bot) with ⟨cfg_h, hplus, hhalt⟩
        exact ⟨cfg_h, hplus, Or.inr hhalt⟩
      · have hlt : validLt Lt := hv.2.1
        refine ⟨evalCfg (.mDL, push0L (push0L (push0L Lt)), R1.1, R1.2), ?_,
          Or.inl ⟨(.mDL, push0L (push0L (push0L Lt)), R1.1, R1.2), ?_, rfl⟩⟩
        · simp only [evalCfg]; rw [hR1_eq]; exact step_mBR_1_1 Lt (fullR Rs d_bot)
        · rcases Lt with _ | ⟨⟨z', o'⟩, Lt'⟩
          · exact ⟨hR1_DL, trivial⟩
          · exact ⟨hR1_DL, hlt.2, hlt.1⟩
      · rcases hv.2 with ⟨hlt, ho⟩
        refine ⟨evalCfg (.mDL, (2, o) :: Lt, R1.1, R1.2), ?_,
          Or.inl ⟨(.mDL, (2, o) :: Lt, R1.1, R1.2), ⟨hR1_DL, hlt, by omega⟩, rfl⟩⟩
        simp only [evalCfg]; rw [hR1_eq]; exact step_mBR_1_succ2 o Lt (fullR Rs d_bot)
    · rcases hv.2 with ⟨hlt, ho⟩
      refine ⟨evalCfg (.mDL, (z + 1, o) :: Lt, R1.1, R1.2), ?_,
        Or.inl ⟨(.mDL, (z + 1, o) :: Lt, R1.1, R1.2), ⟨hR1_DL, hlt, ho⟩, rfl⟩⟩
      simp only [evalCfg]; rw [hR1_eq]; exact step_mBR_succ2 z o Lt (fullR Rs d_bot)
  | mER0 =>
    have hR : validR (fullR Rs d_bot) := hv.1
    rcases L with _ | ⟨⟨_ | _ | z, o⟩, Lt⟩
    · have hhd : headD (fullR Rs d_bot) = 0 := hv.2
      have hR100 : validR_BR (fullR ((0, true) :: Rs) d_bot) :=
        validR_BR_of_validR _ (validR_cons_0true (fullR Rs d_bot) hR hhd)
      refine ⟨evalCfg (.mBR, [], (0, true) :: Rs, d_bot), ?_,
        Or.inl ⟨(.mBR, [], (0, true) :: Rs, d_bot), ⟨hR100, trivial⟩, rfl⟩⟩
      simp only [evalCfg, ← push100R_fullR]
      exact step_mER0_nil (fullR Rs d_bot)
    · cases o with
      | zero =>
        have hlt : validLt Lt := hv.2.1
        refine ⟨evalCfg (.mER1, push0L Lt, (0, false) :: Rs, d_bot),
          step_mER0_0_0 Lt (fullR Rs d_bot),
          Or.inl ⟨(.mER1, push0L Lt, (0, false) :: Rs, d_bot), ?_, rfl⟩⟩
        rcases Lt with _ | ⟨⟨z', o'⟩, Lt'⟩
        · exact ⟨rfl, hR, by decide, fun h => by omega, fun h => by omega⟩
        · exact ⟨rfl, hR, hlt.2, hlt.1, by decide, fun h => by omega, fun h => by omega⟩
      | succ o =>
        rcases hv.2 with ⟨hlt, ho, hhd⟩
        exact ⟨evalCfg (.mER1, (0, o) :: Lt, (0, false) :: Rs, d_bot),
          step_mER0_0_succ o Lt (fullR Rs d_bot),
          Or.inl ⟨(.mER1, (0, o) :: Lt, (0, false) :: Rs, d_bot),
            ⟨rfl, hR, hlt, by omega, rfl, by omega, fun h3 => by omega⟩, rfl⟩⟩
    · have hR0 : validR_BR (fullR ((0, false) :: Rs) d_bot) :=
        validR_BR_of_validR _ (validR_cons_0false (fullR Rs d_bot) hR)
      cases o with
      | zero =>
        have hlt : validLt Lt := hv.2.1
        refine ⟨evalCfg (.mBR, push0L (push0L Lt), (0, false) :: Rs, d_bot),
          step_mER0_1_0 Lt (fullR Rs d_bot),
          Or.inl ⟨(.mBR, push0L (push0L Lt), (0, false) :: Rs, d_bot), ?_, rfl⟩⟩
        rcases Lt with _ | ⟨⟨z', o'⟩, Lt'⟩
        · exact ⟨hR0, trivial⟩
        · exact ⟨hR0, hlt.2, hlt.1⟩
      | succ o =>
        rcases hv.2 with ⟨hlt, ho, _⟩
        exact ⟨evalCfg (.mBR, (1, o) :: Lt, (0, false) :: Rs, d_bot),
          step_mER0_1_succ o Lt (fullR Rs d_bot),
          Or.inl ⟨(.mBR, (1, o) :: Lt, (0, false) :: Rs, d_bot), ⟨hR0, hlt, by omega⟩, rfl⟩⟩
    · rcases hv.2 with ⟨hlt, ho, hhd⟩
      have hR100 : validR_BR (fullR ((0, true) :: Rs) d_bot) :=
        validR_BR_of_validR _ (validR_cons_0true (fullR Rs d_bot) hR hhd)
      refine ⟨evalCfg (.mBR, (z, o) :: Lt, (0, true) :: Rs, d_bot), ?_,
        Or.inl ⟨(.mBR, (z, o) :: Lt, (0, true) :: Rs, d_bot), ?_, rfl⟩⟩
      · simp only [evalCfg, ← push100R_fullR]
        exact step_mER0_succ2 z o Lt (fullR Rs d_bot)
      · rcases z with _ | _ | z'
        · exact ⟨hR100, hlt, ho, Or.inl rfl⟩
        · exact ⟨hR100, hlt, by omega⟩
        · exact ⟨hR100, hlt, ho⟩
  | mER1 =>
    rcases Rs with _ | ⟨⟨d₀, b₀⟩, Rs'⟩
    · exact False.elim hv
    · rcases hv with ⟨rfl, hRt, hL⟩
      let Rt := fullR Rs' d_bot
      rcases L with _ | ⟨⟨_ | _ | z, o⟩, Lt⟩
      · rcases hL with ⟨hd5, h2, h4⟩
        have hR : validR ((d₀, false) :: Rt) := validR_cons_false_of_bounds d₀ Rt hRt hd5 h2 h4
        have hR0 : validR_BR (fullR ((0, false) :: (d₀, false) :: Rs') d_bot) :=
          validR_BR_of_validR _ (validR_cons_0false _ hR)
        exact ⟨evalCfg (.mBR, [], (0, false) :: (d₀, false) :: Rs', d_bot),
          step_mER1_nil ((d₀, false) :: Rt),
          Or.inl ⟨(.mBR, [], (0, false) :: (d₀, false) :: Rs', d_bot), ⟨hR0, trivial⟩, rfl⟩⟩
      · rcases hL with ⟨hlt, ho4, rfl, hhd1, hhd0⟩
        refine ⟨evalCfg (.mER1, push0L Lt, (o + 1, false) :: Rs', d_bot), ?_,
          Or.inl ⟨(.mER1, push0L Lt, (o + 1, false) :: Rs', d_bot), ?_, rfl⟩⟩
        · have hstep := step_mER1_sweep o Lt ((0, false) :: Rt)
          rw [bumpRN_cons, Nat.zero_add] at hstep
          exact hstep
        · rcases Lt with _ | ⟨⟨z', o'⟩, Lt'⟩
          · exact ⟨rfl, hRt, by omega, fun _ => hhd1, fun h4 => hhd0 (by omega)⟩
          · exact ⟨rfl, hRt, hlt.2, hlt.1, by omega, fun _ => hhd1, fun h4 => hhd0 (by omega)⟩
      · rcases hL with ⟨hlt, ho6, hd5, h2, h4⟩
        have hR : validR ((d₀, false) :: Rt) := validR_cons_false_of_bounds d₀ Rt hRt hd5 h2 h4
        have hRb : validR_BR (fullR ((d₀ + 1, false) :: Rs') d_bot) :=
          validR_BR_bumpR ((d₀, false) :: Rt) hR
        cases o with
        | zero =>
          refine ⟨evalCfg (.mBR, push0L (push0L Lt), (d₀ + 1, false) :: Rs', d_bot),
            step_mER1_1_0 Lt ((d₀, false) :: Rt),
            Or.inl ⟨(.mBR, push0L (push0L Lt), (d₀ + 1, false) :: Rs', d_bot), ?_, rfl⟩⟩
          rcases Lt with _ | ⟨⟨z', o'⟩, Lt'⟩
          · exact ⟨hRb, trivial⟩
          · exact ⟨hRb, hlt.2, hlt.1⟩
        | succ o =>
          exact ⟨evalCfg (.mBR, (1, o) :: Lt, (d₀ + 1, false) :: Rs', d_bot),
            step_mER1_1_succ o Lt ((d₀, false) :: Rt),
            Or.inl ⟨(.mBR, (1, o) :: Lt, (d₀ + 1, false) :: Rs', d_bot), ⟨hRb, hlt, by omega⟩, rfl⟩⟩
      · rcases hL with ⟨hlt, ho6, hd5, h2, h4⟩
        have hR : validR ((d₀, false) :: Rt) := validR_cons_false_of_bounds d₀ Rt hRt hd5 h2 h4
        have hR0 : validR_BR (fullR ((0, false) :: (d₀, false) :: Rs') d_bot) :=
          validR_BR_of_validR _ (validR_cons_0false _ hR)
        refine ⟨evalCfg (.mBR, (z, o) :: Lt, (0, false) :: (d₀, false) :: Rs', d_bot),
          step_mER1_succ2 z o Lt ((d₀, false) :: Rt),
          Or.inl ⟨(.mBR, (z, o) :: Lt, (0, false) :: (d₀, false) :: Rs', d_bot), ?_, rfl⟩⟩
        rcases z with _ | _ | z'
        · exact ⟨hR0, hlt, ho6, Or.inl rfl⟩
        · exact ⟨hR0, hlt, by omega⟩
        · exact ⟨hR0, hlt, ho6⟩
  | mDL =>
    rcases hv with ⟨hRDL, hL⟩
    rcases push1LN_ar_eq 0 L hL with ⟨_, hlt_ar⟩
    rcases Rs with _ | ⟨⟨d, _ | _⟩, Rs'⟩
    · simp only [fullR, List.nil_append, validR_DL] at hRDL
      rcases push1LN_ar_eq d_bot L hL with ⟨hp_eq, _⟩
      refine ⟨evalCfg (.mBR, (0, d_bot + 1) :: ltAfterDL L, [], 0), ?_,
        Or.inl ⟨(.mBR, (0, d_bot + 1) :: ltAfterDL L, [], 0),
          ⟨⟨rfl, by decide⟩, hlt_ar, by omega, Or.inl rfl⟩, rfl⟩⟩
      have h1 := step_mDL_sweep_false d_bot L []
      have h2 := step_mAL_nil (push1LN (d_bot + 2) L)
      rw [hp_eq] at h1 h2
      exact stepPlus_trans h1 h2
    · rcases push1LN_ar_eq d L hL with ⟨hp_eq, _⟩
      have hRt_props : 1 ≤ d ∧ d ≤ 7 ∧ (4 ≤ d → headD (fullR Rs' d_bot) ≤ 1) ∧
          (6 ≤ d → headD (fullR Rs' d_bot) = 0) ∧ validR (fullR Rs' d_bot) := by
        rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
        · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
        · rw [fullR_cons, hRs'] at hRDL
          exact ⟨hRDL.1, hRDL.2.1, hRDL.2.2.1, hRDL.2.2.2.1, hRDL.2.2.2.2⟩
      rcases hRt_props with ⟨hd1, hd7, h4, h6, hRt⟩
      refine ⟨evalCfg (.mAL, (0, d + 1) :: ltAfterDL L, Rs', d_bot), ?_,
        Or.inl ⟨(.mAL, (0, d + 1) :: ltAfterDL L, Rs', d_bot),
          ⟨hRt, hlt_ar, by omega, by omega, fun h7 => h6 (by omega), fun h5 => h4 (by omega)⟩,
          rfl⟩⟩
      have h1 := step_mDL_sweep_false d L (fullR Rs' d_bot)
      rw [hp_eq] at h1
      exact h1
    · rcases push1LN_ar_eq d L hL with ⟨hp_eq, _⟩
      have hRt_props : 1 ≤ d ∧ d ≤ 3 ∧ headD (fullR Rs' d_bot) = 0 ∧ validR (fullR Rs' d_bot) := by
        rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
        · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
        · rw [fullR_cons, hRs'] at hRDL
          exact ⟨hRDL.1, hRDL.2.1, hRDL.2.2.1, hRDL.2.2.2⟩
      rcases hRt_props with ⟨hd1, hd3, hhd0, hRt⟩
      let R1 := bumpRs Rs' d_bot
      have hR1_eq : fullR R1.1 R1.2 = bumpR (fullR Rs' d_bot) := fullR_bumpRs Rs' d_bot
      have hR1_BR : validR_BR (fullR R1.1 R1.2) := by
        rw [hR1_eq]; exact validR_BR_bumpR _ hRt
      have hR1_hd : headD (fullR R1.1 R1.2) = 1 := by
        rw [hR1_eq]
        rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
        · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
        · rw [hRs'] at hhd0; simp only [headD] at hhd0; subst hhd0; rfl
      refine ⟨evalCfg (.mBR, (0, d + 1) :: ltAfterDL L, R1.1, R1.2), ?_,
        Or.inl ⟨(.mBR, (0, d + 1) :: ltAfterDL L, R1.1, R1.2),
          ⟨hR1_BR, hlt_ar, by omega, Or.inr ⟨hR1_hd, by omega, by omega⟩⟩, rfl⟩⟩
      simp only [evalCfg, fullR_cons]; rw [hR1_eq]
      have h1 := step_mDL_sweep_true d L (fullR Rs' d_bot)
      rw [hp_eq] at h1
      exact h1
  | mAL =>
    rcases hv with ⟨hR, hL⟩
    rcases L with _ | ⟨⟨_ | z, o⟩, Lt⟩
    · exact False.elim hL
    · rcases hL with ⟨hlt, ho2, ho8, ho7, ho5⟩
      rcases Rs with _ | ⟨⟨d, _ | _⟩, Rs'⟩
      · simp only [fullR, List.nil_append, validR, headD] at hR ho7
        refine ⟨evalCfg (.mBR, (d_bot + 1, o) :: Lt, [], 0), ?_,
          Or.inl ⟨(.mBR, (d_bot + 1, o) :: Lt, [], 0), ?_, rfl⟩⟩
        · have h1 := step_mAL_sweep_false d_bot ((0, o) :: Lt) []
          rw [push0LN_cons, Nat.zero_add] at h1
          exact h1
        · rcases d_bot with _ | d'
          · exact ⟨⟨rfl, by decide⟩, hlt, ho8⟩
          · exact ⟨⟨rfl, by decide⟩, hlt, by omega⟩
      · let Rt := fullR Rs' d_bot
        have hRt : validR Rt := by
          change validR (fullR Rs' d_bot)
          rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
          · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
          · rw [fullR_cons, hRs'] at hR; exact hR.2.2.2
        let R1 := bumpRs Rs' d_bot
        have hR1_eq : fullR R1.1 R1.2 = bumpR Rt := fullR_bumpRs Rs' d_bot
        have hR1_BR : validR_BR (fullR R1.1 R1.2) := by
          rw [hR1_eq]; exact validR_BR_bumpR Rt hRt
        refine ⟨evalCfg (.mBR, (d + 1, o) :: Lt, R1.1, R1.2), ?_,
          Or.inl ⟨(.mBR, (d + 1, o) :: Lt, R1.1, R1.2), ?_, rfl⟩⟩
        · simp only [evalCfg, fullR_cons]; rw [hR1_eq]
          have h1 := step_mAL_sweep_false d ((0, o) :: Lt) Rt
          rw [push0LN_cons, Nat.zero_add] at h1
          exact h1
        · simp only [fullR_cons, headD] at ho7
          rcases d with _ | d'
          · exact ⟨hR1_BR, hlt, ho8⟩
          · exact ⟨hR1_BR, hlt, by omega⟩
      · by_cases hsweep : d = 0 ∧ o = 2
        · rcases hsweep with ⟨rfl, rfl⟩
          have hRt : validR (fullR Rs' d_bot) := by
            rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
            · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
            · rw [fullR_cons, hRs'] at hR; exact hR.2.2
          let P := peel0True Rs' ((1, 0) :: Lt)
          exact ⟨evalCfg (.mAL, (0, 2) :: P.1, P.2, d_bot),
            sweep_mAL_0true Rs' Lt d_bot,
            Or.inl ⟨(.mAL, (0, 2) :: P.1, P.2, d_bot),
              ⟨peel0True_validR Rs' ((1, 0) :: Lt) d_bot hRt,
               peel0True_validLt Rs' ((1, 0) :: Lt) ⟨by decide, hlt⟩,
               by decide, by decide, fun h => by omega, fun h => by omega⟩, rfl⟩⟩
        · let Rt := fullR Rs' d_bot
          have hRt : validR Rt := by
            change validR (fullR Rs' d_bot)
            rcases hRs' : fullR Rs' d_bot with _ | ⟨⟨d₂, b₂⟩, Rt'⟩
            · exact absurd hRs' (fullR_ne_nil Rs' d_bot)
            · rw [fullR_cons, hRs'] at hR; exact hR.2.2
          have hR0 : validR_BR (fullR ((0, false) :: Rs') d_bot) :=
            validR_BR_of_validR _ (validR_cons_0false Rt hRt)
          refine ⟨evalCfg (.mBR, (d + 1, o) :: Lt, (0, false) :: Rs', d_bot), ?_,
            Or.inl ⟨(.mBR, (d + 1, o) :: Lt, (0, false) :: Rs', d_bot), ?_, rfl⟩⟩
          · have h1 := step_mAL_sweep_true d ((0, o) :: Lt) Rt
            rw [push0LN_cons, Nat.zero_add] at h1
            exact h1
          · simp only [fullR_cons, headD] at ho7
            rcases d with _ | d'
            · exact ⟨hR0, hlt, ho8⟩
            · exact ⟨hR0, hlt, by omega⟩
    · exact False.elim hL

private theorem segmented_system_closed (s : SegState) (hv : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2.1 s.2.2.2 hv


private theorem lWord_ne_nil (p : ℕ × ℕ) : lWord p ≠ [] := by
  rcases p with ⟨_ | z, o⟩
  · cases o <;> simp
  · simp

private theorem lWord_ne_zero : ∀ p : ℕ × ℕ, lWord p ≠ [(0 : Fin 2)]
  | (0, o) => by cases o <;> simp
  | (z + 1, o) => by
      unfold lWord
      intro h
      exact lWord_ne_nil (z, o) (List.cons.inj h).2

private theorem rWord_len : ∀ p : ℕ × Bool, 2 ≤ (rWord p).length
  | (0, false) => by simp
  | (0, true) => by simp
  | (d + 1, b) => by have := rWord_len (d, b); simp only [    rWord_succ, List.length_cons]; omega

private theorem rWord_ne_nil (p : ℕ × Bool) : rWord p ≠ [] := by
  intro h; have := rWord_len p; simp [h] at this

private theorem rWord_ne_zero (p : ℕ × Bool) : rWord p ≠ [(0 : Fin 2)] := by
  intro h; have := rWord_len p; simp [h] at this

private theorem segs_wf (s : SegState) (_ : ValidSeg s) :
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 ∧
      (∀ r ∈ segsL s, r.WellFormed) ∧ (∀ r ∈ segsR s, r.WellFormed) := by
  refine ⟨by simp [segsL], by simp [segsR], ?_, ?_⟩
  · simp only [segsL, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl | rfl)
    · refine ⟨fun w hw => ?_, fun h => ?_⟩
      · rcases List.mem_map.mp hw with ⟨p, _, rfl⟩
        exact rWord_ne_nil p
      · rcases List.mem_map.mp (h 0) with ⟨p, _, hp⟩
        exact rWord_ne_zero p hp
    · simp [SegRegionKind.WellFormed]
    · simp [SegRegionKind.WellFormed]
  · simp only [segsR, List.mem_singleton]
    rintro _ rfl
    refine ⟨fun w hw => ?_, fun h => ?_⟩
    · rcases List.mem_map.mp hw with ⟨p, _, rfl⟩
      exact lWord_ne_nil p
    · rcases List.mem_map.mp (h 0) with ⟨p, _, hp⟩
      exact lWord_ne_zero p hp

/-- Canonical mode list for `1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`. -/
def modes : List SegMode := [.mBR, .mER0, .mER1, .mDL, .mAL]

/-- Explicit `IsClosedSegmentedSystem` witness for `1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`. -/
theorem is_closed_segmented_system :
    IsClosedSegmentedSystem target modes ValidSeg modeOf segsL segsR evalCfg := by
  rw [target_eq_target_tm]
  refine ⟨by decide, by decide, fun m => by cases m <;> simp [modes],
    segs_wf, valid_seg_modes, Or.inl segsL_nowhere_dense, Or.inl segsL_nowhere_dense,
      Or.inl segsR_nowhere_dense,
    ⟨s₀, validSeg_s₀, init_reaches_segmented_system⟩, segmented_system_closed⟩

/-- Segmented cryptid certificate for `1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_---0LC`. -/
theorem is_segmented_cryptid : IsSegmentedCryptid target :=
  ⟨SegState, SegMode, modes, ValidSeg, modeOf, segsL, segsR, evalCfg,
    is_closed_segmented_system⟩

end BusyBeaver.M_1RB0LA_1RC0RE_0LD0RF_1LA1LD_0RA1RE_HHH0LC
