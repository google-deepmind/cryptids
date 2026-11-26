/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.WordRunStack

/-!
# Busy Beaver Holdout `1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC` (#536)

Formal `IsClosedSegmentedSystem` and `IsSegmentedCryptid` proofs for the 6-state, 2-symbol
Busy Beaver holdout `1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC` (bbchallenge holdout #536).
-/

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RA_0LC0RF_0LB1RD_1LEHHH_1RA0LF_1LE0RC

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 0, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 1, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 3, 1 => none
  | 4, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 4, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 2, Stmt.write 0 Dir.right)

private theorem target_eq_target_tm : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl


open WordRunStack

/-- Three nullary separator modes for Holdout `#536`. -/
inductive SegMode where
  | Fwd
  | RetF
  | RetB
  deriving DecidableEq

/-- Left half-tape word grammar frames (`[0, 1]`, `[0, 1, 1, 1]`, `0^(z+1) ++ [1, 1]`). -/
inductive LFrame536 where
  | f01
  | f0111
  | f2 (z : ℕ)
  deriving DecidableEq

/-- Right-tape word grammar frames (`[0] ++ 1^(o+1)`, `[0, 0] ++ 1^(o+1)`, `0^(z+3) ++ [1]`). -/
inductive RFrame536 where
  | z1 (o : ℕ)
  | z2 (o : ℕ)
  | z3 (z : ℕ)
  deriving DecidableEq

def oWord (k : ℕ) : List (Fin 2) :=
  Nat.rec [1] (fun _ acc => 1 :: acc) k

def zWord (k : ℕ) : List (Fin 2) :=
  Nat.rec [1] (fun _ acc => 0 :: acc) k

def f2Tail (z : ℕ) : List (Fin 2) :=
  Nat.rec [1, 1] (fun _ acc => 0 :: acc) z

def wordL : LFrame536 → List (Fin 2)
  | .f01 => [0, 1]
  | .f0111 => [0, 1, 1, 1]
  | .f2 z => 0 :: f2Tail z

def wordR : RFrame536 → List (Fin 2)
  | .z1 o => 0 :: oWord o
  | .z2 o => 0 :: 0 :: oWord o
  | .z3 z => zWord (z + 3)

abbrev SegState := SegMode × List LFrame536 × List RFrame536

def ValidSeg (_ : SegState) : Prop := True

def modeOf (s : SegState) : SegMode := s.1

def encL (L : List LFrame536) : ListBlank (Fin 2) :=
  List.rec ([0, 1] +> default) (fun x _ acc => wordL x +> acc) L

def encR (R : List RFrame536) : ListBlank (Fin 2) :=
  List.rec default (fun x _ acc => wordR x +> acc) R

def segsL (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.1.map wordL), .gadget [0, 1]]

def segsR (s : SegState) : List (SegRegionKind (Fin 2)) :=
  [.finWord (s.2.2.map wordR)]

def evalSegCfg : SegMode → List LFrame536 → List RFrame536 → Cfg (Fin 2) (Fin 6)
  | .Fwd, L, R => (applyView (.id []) (encL L)) {{0}}> (applyView (.id []) (encR R))
  | .RetF, L, R => (applyView (.id []) (encL L)) <{{5}} (applyView (.id []) (encR R))
  | .RetB, L, R => (applyView (.id []) (encL L)) {{1}}> (applyView (.id [0, 0, 1]) (encR R))

def evalCfg (s : SegState) : Cfg (Fin 2) (Fin 6) :=
  evalSegCfg s.1 s.2.1 s.2.2

private def modeSpec : SegMode → SegModeSpec (Fin 2) (Fin 6)
  | .Fwd => { q := 0, dir := .right, vL := .id [], vR := .id [] }
  | .RetF => { q := 5, dir := .left, vL := .id [], vR := .id [] }
  | .RetB => { q := 1, dir := .right, vL := .id [], vR := .id [0, 0, 1] }

private theorem encL_eq : ∀ L : List LFrame536, encL L = encWordsTail wordL ([0, 1] +> default) L
  | [] => rfl
  | x :: L => congrArg (wordL x +> ·) (encL_eq L)

private theorem encR_eq : ∀ R : List RFrame536, encR R = encWords wordR R
  | [] => rfl
  | x :: R => congrArg (wordR x +> ·) (encR_eq R)

private def s₀ : SegState := (.Fwd, [], [.z1 0])

-- ----------------------------------------------------------------------------
-- 1. Two-Sided Nowhere-Dense Proofs (`NoFactor [1,1,1,1]` on L, `NoFactor [0,0,0,1,1]` on R)
-- ----------------------------------------------------------------------------

private theorem encL_tail_zero : ∀ L : List LFrame536, ∃ tl : ListBlank (Fin 2), encL L = [0] +> tl
  | [] => ⟨[1] +> default, rfl⟩
  | .f01 :: lt => ⟨[1] +> encL lt, rfl⟩
  | .f0111 :: lt => ⟨[1, 1, 1] +> encL lt, rfl⟩
  | .f2 z :: lt => ⟨f2Tail z +> encL lt, rfl⟩

private theorem encL_nth_zero (L : List LFrame536) : (encL L).nth 0 = 0 := by
  obtain ⟨tl, h⟩ := encL_tail_zero L
  rw [h]
  exact nth_cons_zero 0 tl

private theorem noFactor_1111_default : NoFactor ([1, 1, 1, 1] : List (Fin 2)) default :=
  noFactor_default [1, 1, 1, 1] 0 (by decide) (by decide)

private theorem noFactor_1111_zero_cons {t : ListBlank (Fin 2)}
    (ht : NoFactor ([1, 1, 1, 1] : List (Fin 2)) t) :
    NoFactor ([1, 1, 1, 1] : List (Fin 2)) ((0 : Fin 2) >> t) :=
  noFactor_cons_of_nth_ne [1, 1, 1, 1] 0 t ht 0 (by decide) (by rw [nth_cons_zero]; decide)

private theorem noFactor_1111_one1 {t : ListBlank (Fin 2)}
    (ht : NoFactor ([1, 1, 1, 1] : List (Fin 2)) t) (h0 : t.nth 0 = 0) :
    NoFactor ([1, 1, 1, 1] : List (Fin 2)) ((1 : Fin 2) >> t) :=
  noFactor_cons_of_nth_ne [1, 1, 1, 1] 1 t ht 1 (by decide)
    (by rw [nth_cons_one, h0]; decide)

private theorem noFactor_1111_one2 {t : ListBlank (Fin 2)}
    (ht : NoFactor ([1, 1, 1, 1] : List (Fin 2)) t) (h0 : t.nth 0 = 0) :
    NoFactor ([1, 1, 1, 1] : List (Fin 2)) ((1 : Fin 2) >> ((1 : Fin 2) >> t)) :=
  noFactor_cons_of_nth_ne [1, 1, 1, 1] 1 ((1 : Fin 2) >> t) (noFactor_1111_one1 ht h0) 2
    (by decide) (by rw [nth_cons_two, nth_cons_one, h0]; decide)

private theorem noFactor_1111_one3 {t : ListBlank (Fin 2)}
    (ht : NoFactor ([1, 1, 1, 1] : List (Fin 2)) t) (h0 : t.nth 0 = 0) :
    NoFactor ([1, 1, 1, 1] : List (Fin 2))
      ((1 : Fin 2) >> ((1 : Fin 2) >> ((1 : Fin 2) >> t))) :=
  noFactor_cons_of_nth_ne [1, 1, 1, 1] 1 ((1 : Fin 2) >> ((1 : Fin 2) >> t))
    (noFactor_1111_one2 ht h0) 3 (by decide)
    (by rw [nth_cons_three, nth_cons_two, nth_cons_one, h0]; decide)

private theorem noFactor_1111_f2Tail : ∀ (z : ℕ) {t : ListBlank (Fin 2)},
    NoFactor ([1, 1, 1, 1] : List (Fin 2)) t → t.nth 0 = 0 →
      NoFactor ([1, 1, 1, 1] : List (Fin 2)) (f2Tail z +> t)
  | 0, _, ht, h0 => noFactor_1111_one2 ht h0
  | z + 1, _, ht, h0 => noFactor_1111_zero_cons (noFactor_1111_f2Tail z ht h0)

private theorem noFactor_1111_encL : ∀ L : List LFrame536,
    NoFactor ([1, 1, 1, 1] : List (Fin 2)) (encL L)
  | [] => noFactor_1111_zero_cons (noFactor_1111_one1 noFactor_1111_default (nth_default 0))
  | .f01 :: lt =>
      noFactor_1111_zero_cons (noFactor_1111_one1 (noFactor_1111_encL lt) (encL_nth_zero lt))
  | .f0111 :: lt =>
      noFactor_1111_zero_cons (noFactor_1111_one3 (noFactor_1111_encL lt) (encL_nth_zero lt))
  | .f2 z :: lt =>
      noFactor_1111_zero_cons
        (noFactor_1111_f2Tail z (noFactor_1111_encL lt) (encL_nth_zero lt))

private theorem segsL_nowhere_dense : IsNowhereDenseHalf ValidSeg segsL :=
  isNowhereDenseHalf_of_family
    (fun s => (evalSegmentedHalf_finWord_gadget wordL [0, 1] s.2.1).trans (encL_eq s.2.1).symm)
    (isNowhereDenseFamily_of_noFactor ValidSeg (fun s => encL s.2.1) [1, 1, 1, 1]
      (fun s _ => noFactor_1111_encL s.2.1))

private theorem encR_nth_zero : ∀ R : List RFrame536, (encR R).nth 0 = 0
  | [] => nth_default 0
  | .z1 o :: rt => nth_cons_zero 0 (oWord o +> encR rt)
  | .z2 o :: rt => nth_cons_zero 0 ((0 : Fin 2) >> (oWord o +> encR rt))
  | .z3 z :: rt => nth_cons_zero 0 (zWord (z + 2) +> encR rt)

private theorem oWord_nth_zero : ∀ (o : ℕ) (t : ListBlank (Fin 2)), (oWord o +> t).nth 0 = 1
  | 0, t => nth_cons_zero 1 t
  | o + 1, t => nth_cons_zero 1 (oWord o +> t)

private theorem noFactor_00011_default : NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) default :=
  noFactor_default [0, 0, 0, 1, 1] 3 (by decide) (by decide)

private theorem noFactor_00011_one_cons {t : ListBlank (Fin 2)}
    (ht : NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) t) :
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) ((1 : Fin 2) >> t) :=
  noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 1 t ht 0 (by decide) (by rw [nth_cons_zero]; decide)

private theorem noFactor_00011_oWord : ∀ (o : ℕ) {t : ListBlank (Fin 2)},
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) t →
      NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) (oWord o +> t)
  | 0, _, ht => noFactor_00011_one_cons ht
  | o + 1, _, ht => noFactor_00011_one_cons (noFactor_00011_oWord o ht)

private theorem noFactor_00011_z1 (o : ℕ) {t : ListBlank (Fin 2)}
    (ht : NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) t) :
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) ((0 : Fin 2) >> (oWord o +> t)) :=
  noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 (oWord o +> t) (noFactor_00011_oWord o ht) 1
    (by decide) (by rw [nth_cons_one, oWord_nth_zero]; decide)

private theorem noFactor_00011_z2 (o : ℕ) {t : ListBlank (Fin 2)}
    (ht : NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) t) :
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) ((0 : Fin 2) >> ((0 : Fin 2) >> (oWord o +> t))) :=
  noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 ((0 : Fin 2) >> (oWord o +> t))
    (noFactor_00011_z1 o ht) 2 (by decide)
    (by rw [nth_cons_two, nth_cons_one, oWord_nth_zero]; decide)

private theorem noFactor_00011_zWord : ∀ (m : ℕ) {t : ListBlank (Fin 2)},
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) t → t.nth 0 = 0 →
      NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) (zWord m +> t)
  | 0, _, ht, _ => noFactor_00011_one_cons ht
  | 1, t, ht, h0 =>
      noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 (zWord 0 +> t) (noFactor_00011_zWord 0 ht h0) 1
        (by decide) (by simp only [zWord, ListBlank.append, nth_cons_one, nth_cons_zero]; decide)
  | 2, t, ht, h0 =>
      noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 (zWord 1 +> t) (noFactor_00011_zWord 1 ht h0) 2
        (by decide)
        (by simp only [zWord, ListBlank.append, nth_cons_two, nth_cons_one, nth_cons_zero]; decide)
  | 3, t, ht, h0 =>
      noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 (zWord 2 +> t) (noFactor_00011_zWord 2 ht h0) 4
        (by decide)
        (by simp only [zWord, ListBlank.append, nth_cons_four, nth_cons_three, nth_cons_two,
              nth_cons_one, h0]; decide)
  | m + 4, t, ht, h0 =>
      noFactor_cons_of_nth_ne [0, 0, 0, 1, 1] 0 (zWord (m + 3) +> t)
        (noFactor_00011_zWord (m + 3) ht h0) 3 (by decide)
        (by simp only [zWord, ListBlank.append, nth_cons_three, nth_cons_two, nth_cons_one,
              nth_cons_zero]; decide)

private theorem noFactor_00011_encR : ∀ R : List RFrame536,
    NoFactor ([0, 0, 0, 1, 1] : List (Fin 2)) (encR R)
  | [] => noFactor_00011_default
  | .z1 o :: rt => noFactor_00011_z1 o (noFactor_00011_encR rt)
  | .z2 o :: rt => noFactor_00011_z2 o (noFactor_00011_encR rt)
  | .z3 z :: rt => noFactor_00011_zWord (z + 3) (noFactor_00011_encR rt) (encR_nth_zero rt)

private theorem segsR_nowhere_dense : IsNowhereDenseHalf ValidSeg segsR :=
  isNowhereDenseHalf_of_family
    (fun s => (evalSegmentedHalf_finWord_map wordR s.2.2).trans (encR_eq s.2.2).symm)
    (isNowhereDenseFamily_of_noFactor ValidSeg (fun s => encR s.2.2) [0, 0, 0, 1, 1]
      (fun s _ => noFactor_00011_encR s.2.2))

-- ----------------------------------------------------------------------------
-- 2. Initial Entry (`init_reaches_segmented_system`)
-- ----------------------------------------------------------------------------

private theorem win_step {n : ℕ} {q : Fin 6} {ls rs : List (Fin 2)} {q' : Fin 6}
    {ls' rs' : List (Fin 2)} (l r : ListBlank (Fin 2))
    (h : checkHeadRight false false target_tm n q ls rs q' ls' rs' = true) :
    ((ls +> l) {{q}}> (rs +> r)) [target_tm]⊢^{n} ((ls' +> l) {{q'}}> (rs' +> r)) :=
  @checkHeadRight_sound (Fin 2) (Fin 6) _ _ _ _ false false target_tm n q ls rs q' ls' rs' l r
    (by intro hc; contradiction) (by intro hc; contradiction) h

private theorem default_eq_00 : (default : ListBlank (Fin 2)) = [0, 0] +> default := by
  simp [ListBlank.append]

private theorem init_reaches_segmented_system : (init []) [target_tm]⊢⁺ evalCfg s₀ := by
  refine ⟨8, by omega, ?_⟩
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) =
      (([0, 0] +> default) {{0}}> ([0, 0] +> default)) := by
    have hd : (default : ListBlank (Fin 2)).head = 0 := rfl
    have tl : (default : ListBlank (Fin 2)).tail = default := rfl
    have hmk : (Tape.mk₁ ([] : List (Fin 2))) = ⟨0, default, default⟩ := rfl
    simp [init, hmk, hd, tl, ListBlank.append]
  have h1 : evalCfg s₀ = (([0, 1] +> default) {{0}}> ([0, 1] +> default)) := rfl
  rw [h0, h1]
  exact win_step default default rfl

-- ----------------------------------------------------------------------------
-- 3. Genuine `List.rec` Stack-Sweep Compactions & `walkWordRight` / `walkWordLeft` Runs
-- ----------------------------------------------------------------------------

/-- Peels the maximal leading prefix of `(.z1 0, .z1 0)` pairs from `R` (`List.rec`). -/
private def peelZ10Pairs (L : List LFrame536) : List RFrame536 → ℕ × List LFrame536 × List RFrame536
  | .z1 0 :: .z1 0 :: rt =>
      let res := peelZ10Pairs (.f2 1 :: L) rt
      (res.1 + 1, res.2.1, res.2.2)
  | R => (0, L, R)

/-- Full `List`-level rightward stack-sweep compaction in mode `.Fwd`: sweeps all `k` leading
    `(.z1 0, .z1 0)` pairs on `R` into `(.f2 1)^k` on `L` in `6 * k` steps. -/
private theorem sweep_fwd_z10_pairs : ∀ (R : List RFrame536) (L : List LFrame536),
    (evalCfg (.Fwd, L, R)) [target_tm]⊢^{6 * (peelZ10Pairs L R).1}
      (evalCfg (.Fwd, (peelZ10Pairs L R).2.1, (peelZ10Pairs L R).2.2))
  | .z1 0 :: .z1 0 :: rt, L => by
      have hstep : (evalCfg (.Fwd, L, .z1 0 :: .z1 0 :: rt)) [target_tm]⊢^{6}
          (evalCfg (.Fwd, .f2 1 :: L, rt)) := by
        simpa [evalCfg, evalSegCfg, applyView, encL, encR,
          wordL, f2Tail, wordR, oWord, append_assoc_blank] using
          win_step (encL L) (encR rt)
            (h := (rfl : checkHeadRight false false target_tm 6 0 [] [0, 1, 0, 1] 0 [0, 0, 1, 1] []
              = true))
      have hih := sweep_fwd_z10_pairs rt (.f2 1 :: L)
      simp only [peelZ10Pairs]
      rw [show 6 * ((peelZ10Pairs (.f2 1 :: L) rt).1 + 1) =
          6 + 6 * (peelZ10Pairs (.f2 1 :: L) rt).1 by ring]
      exact Counter.multiStep_trans target_tm _ _ _ 6 _ hstep hih
  | [], _ => by simp [peelZ10Pairs, multiStep]
  | [.z1 0], _ => by simp [peelZ10Pairs, multiStep]
  | .z1 0 :: .z1 (_ + 1) :: _, _ => by simp [peelZ10Pairs, multiStep]
  | .z1 0 :: .z2 _ :: _, _ => by simp [peelZ10Pairs, multiStep]
  | .z1 0 :: .z3 _ :: _, _ => by simp [peelZ10Pairs, multiStep]
  | .z1 (_ + 1) :: _, _ => by simp [peelZ10Pairs, multiStep]
  | .z2 _ :: _, _ => by simp [peelZ10Pairs, multiStep]
  | .z3 _ :: _, _ => by simp [peelZ10Pairs, multiStep]

/-- Peels the maximal leading prefix of `.f01` frames from `L` (`List.rec`). -/
private def peelF01 : List LFrame536 → List RFrame536 → List LFrame536 × List RFrame536
  | .f01 :: lt, R => peelF01 lt (.z1 0 :: R)
  | L, R => (L, R)

/-- Full `List`-level leftward stack-sweep compaction in mode `.RetF`: sweeps all leading
    `.f01` frames on `.f01 :: lt` into `.z1 0` frames on `R` in `[target_tm]⊢⁺`. -/
private theorem sweep_retF_f01 (lt : List LFrame536) (R : List RFrame536) :
    (evalCfg (.RetF, .f01 :: lt, R)) [target_tm]⊢⁺
      (evalCfg (.RetF, (peelF01 lt (.z1 0 :: R)).1, (peelF01 lt (.z1 0 :: R)).2)) := by
  induction lt generalizing R with
  | nil =>
      obtain ⟨tl, htl⟩ := encL_tail_zero []
      refine ⟨2, by omega, ?_⟩
      have h1 : evalCfg (.RetF, [.f01], R) = (([1, 0] +> tl) {{5}}> ([0] +> encR R)) := by
        change (([0, 1] +> encL []) <{{5}} encR R) = _
        rw [htl]
        simp [ListBlank.append]
      have h2 : evalCfg (.RetF, [], .z1 0 :: R) = (([] +> tl) {{5}}> ([0, 0, 1] +> encR R)) := by
        change (encL [] <{{5}} ([0, 1] +> encR R)) = _
        rw [htl]
        simp [ListBlank.append]
      dsimp only [peelF01]
      rw [h1, h2]
      exact win_step tl (encR R) rfl
  | cons l1 lt2 ih =>
      obtain ⟨tl, htl⟩ := encL_tail_zero (l1 :: lt2)
      have hstep : (evalCfg (.RetF, .f01 :: l1 :: lt2, R)) [target_tm]⊢^{2}
          (evalCfg (.RetF, l1 :: lt2, .z1 0 :: R)) := by
        have h1 : evalCfg (.RetF, .f01 :: l1 :: lt2, R) =
            (([1, 0] +> tl) {{5}}> ([0] +> encR R)) := by
          change (([0, 1] +> encL (l1 :: lt2)) <{{5}} encR R) = _
          rw [htl]
          simp [ListBlank.append]
        have h2 : evalCfg (.RetF, l1 :: lt2, .z1 0 :: R) =
            (([] +> tl) {{5}}> ([0, 0, 1] +> encR R)) := by
          change (encL (l1 :: lt2) <{{5}} ([0, 1] +> encR R)) = _
          rw [htl]
          simp [ListBlank.append]
        rw [h1, h2]
        exact win_step tl (encR R) rfl
      cases l1 with
      | f01 =>
          obtain ⟨k, hk, hrest⟩ := ih (.z1 0 :: R)
          exact ⟨2 + k, by omega, Counter.multiStep_trans target_tm _ _ _ 2 k hstep hrest⟩
      | f0111 => exact ⟨2, by omega, hstep⟩
      | f2 _ => exact ⟨2, by omega, hstep⟩

/-- Peels the maximal leading prefix of `.f2 1` frames from `L` (`List.rec`). -/
private def peelF21 : List LFrame536 → List RFrame536 → List LFrame536 × List RFrame536
  | .f2 1 :: lt, R => peelF21 lt (.z3 0 :: R)
  | L, R => (L, R)

/-- Full `List`-level leftward stack-sweep compaction in mode `.RetB`: sweeps all leading
    `.f2 1` frames on `.f2 1 :: lt` into `.z3 0` frames on `R` in `[target_tm]⊢⁺`. -/
private theorem sweep_retB_f21 (lt : List LFrame536) (R : List RFrame536) :
    (evalCfg (.RetB, .f2 1 :: lt, R)) [target_tm]⊢⁺
      (evalCfg (.RetB, (peelF21 lt (.z3 0 :: R)).1, (peelF21 lt (.z3 0 :: R)).2)) := by
  induction lt generalizing R with
  | nil =>
      refine ⟨8, by omega, ?_⟩
      simpa [peelF21, evalCfg, evalSegCfg, applyView, encL, encR,
        wordL, f2Tail, wordR, zWord, append_assoc_blank] using
        win_step (encL []) (encR R)
          (h := (rfl : checkHeadRight false false target_tm 8 1 [0, 0, 1, 1] [0, 0, 1] 1 []
            [0, 0, 1, 0, 0, 0, 1] = true))
  | cons l1 lt2 ih =>
      have hstep : (evalCfg (.RetB, .f2 1 :: l1 :: lt2, R)) [target_tm]⊢^{8}
          (evalCfg (.RetB, l1 :: lt2, .z3 0 :: R)) := by
        simpa [evalCfg, evalSegCfg, applyView, encL, encR,
          wordL, f2Tail, wordR, zWord, append_assoc_blank] using
          win_step (encL (l1 :: lt2)) (encR R)
            (h := (rfl : checkHeadRight false false target_tm 8 1 [0, 0, 1, 1] [0, 0, 1] 1 []
              [0, 0, 1, 0, 0, 0, 1] = true))
      cases l1 with
      | f01 => exact ⟨8, by omega, hstep⟩
      | f0111 => exact ⟨8, by omega, hstep⟩
      | f2 z =>
          rcases z with _ | _ | z
          · exact ⟨8, by omega, hstep⟩
          · obtain ⟨k, hk, hrest⟩ := ih (.z3 0 :: R)
            exact ⟨8 + k, by omega, Counter.multiStep_trans target_tm _ _ _ 8 k hstep hrest⟩
          · exact ⟨8, by omega, hstep⟩

private theorem oWord_eq_pow : ∀ (o : ℕ) (r : ListBlank (Fin 2)),
    oWord o +> r = (([1] : List (Fin 2)) ^ (o + 1)) +> r
  | 0, _ => rfl
  | o + 1, r => by
      change (1 : Fin 2) >> (oWord o +> r) = _
      rw [oWord_eq_pow o r, Counter.pow_succ_list, append_assoc_blank]
      rfl

private theorem pow0_f2_eq : ∀ (k : ℕ) (l : ListBlank (Fin 2)),
    (([0] : List (Fin 2)) ^ k) +> ([0, 1, 1] +> l) = wordL (.f2 k) +> l
  | 0, _ => rfl
  | k + 1, l => by
      rw [Counter.pow_succ_list, append_assoc_blank]
      change (0 : Fin 2) >> ((([0] : List (Fin 2)) ^ k) +> ([0, 1, 1] +> l)) = _
      rw [pow0_f2_eq k l]
      rfl

/-- Rightward `walkWordRight` run drain for `.Fwd` on `.z1 0 :: .z1 o2 :: rt`. -/
private theorem drain_fwd_z10_z1 (L : List LFrame536) (o2 : ℕ) (rt : List RFrame536) :
    (evalCfg (.Fwd, L, .z1 0 :: .z1 o2 :: rt)) [target_tm]⊢^{6 + o2}
      (evalCfg (.Fwd, .f2 (o2 + 1) :: L, rt)) := by
  have hpre : (evalCfg (.Fwd, L, .z1 0 :: .z1 o2 :: rt)) [target_tm]⊢^{5}
      (([0, 1, 1] +> encL L) {{0}}> (oWord o2 +> encR rt)) := by
    simpa [evalCfg, evalSegCfg, applyView, encL, encR,
      wordL, wordR, oWord, append_assoc_blank] using
      win_step (encL L) (oWord o2 +> encR rt)
        (h := (rfl : checkHeadRight false false target_tm 5 0 [] [0, 1, 0] 0 [0, 1, 1] [] = true))
  have hwalk := walkWordRight (M := target_tm) 1 0 [] [0] [] [1] rfl
    (o2 + 1) ([0, 1, 1] +> encL L) (encR rt)
  simp only [one_mul] at hwalk
  change ((([0, 1, 1] +> encL L) {{0}}> ((([1] : List (Fin 2)) ^ (o2 + 1)) +> encR rt))
    [target_tm]⊢^{o2 + 1}
    ((((([0] : List (Fin 2)) ^ (o2 + 1)) +> ([0, 1, 1] +> encL L)) {{0}}> encR rt))) at hwalk
  rw [← oWord_eq_pow o2 (encR rt), pow0_f2_eq (o2 + 1) (encL L)] at hwalk
  have hgoal : ((wordL (.f2 (o2 + 1)) +> encL L) {{0}}> encR rt) =
      evalCfg (.Fwd, .f2 (o2 + 1) :: L, rt) := rfl
  rw [hgoal] at hwalk
  rw [show 6 + o2 = 5 + (o2 + 1) by omega]
  exact Counter.multiStep_trans target_tm _ _ _ 5 (o2 + 1) hpre hwalk

private theorem f2_even_split : ∀ (m : ℕ) (l : ListBlank (Fin 2)),
    wordL (.f2 (2 * m + 2)) +> l = (([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 1, 1] +> l)
  | 0, _ => rfl
  | m + 1, l => by
      have h1 : wordL (.f2 (2 * (m + 1) + 2)) +> l =
          [0, 0] +> (wordL (.f2 (2 * m + 2)) +> l) := rfl
      rw [h1, f2_even_split m l, Counter.pow_succ_list [0, 0] (m + 1), append_assoc_blank]

private theorem f2_odd_split : ∀ (m : ℕ) (l : ListBlank (Fin 2)),
    wordL (.f2 (2 * m + 3)) +> l = (([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 0, 1, 1] +> l)
  | 0, _ => rfl
  | m + 1, l => by
      have h1 : wordL (.f2 (2 * (m + 1) + 3)) +> l =
          [0, 0] +> (wordL (.f2 (2 * m + 3)) +> l) := rfl
      rw [h1, f2_odd_split m l, Counter.pow_succ_list [0, 0] (m + 1), append_assoc_blank]

private theorem pow00_zWord_eq : ∀ (m : ℕ) (r : ListBlank (Fin 2)),
    (([0, 0] : List (Fin 2)) ^ m) +> ([0, 1] +> r) = zWord (2 * m + 1) +> r
  | 0, _ => rfl
  | m + 1, r => by
      rw [Counter.pow_succ_list, append_assoc_blank, pow00_zWord_eq m r]
      rfl

private theorem step_retB_to_fwd (L : List LFrame536) (R : List RFrame536)
    (l_tail : ListBlank (Fin 2)) (hL : encL L = [0, 1] +> l_tail) :
    (evalCfg (.RetB, L, R)) [target_tm]⊢^{6} (evalCfg (.Fwd, L, .z2 0 :: R)) := by
  have h1 : evalCfg (.RetB, L, R) = (([0, 1] +> l_tail) {{1}}> ([0, 0, 1] +> encR R)) := by
    change (encL L {{1}}> ([0, 0, 1] +> encR R)) = _
    rw [hL]
  have h2 : evalCfg (.Fwd, L, .z2 0 :: R) = (([0, 1] +> l_tail) {{0}}> ([0, 0, 1] +> encR R)) := by
    change (encL L {{0}}> ([0, 0, 1] +> encR R)) = _
    rw [hL]
  rw [h1, h2]
  exact win_step l_tail (encR R) rfl

/-- Leftward `walkWordLeft` run drain for `.RetB` on `.f2 (2*m + 2) :: lt`. -/
private theorem drain_retB_f2_even (m : ℕ) (lt : List LFrame536) (R : List RFrame536) :
    (evalCfg (.RetB, .f2 (2 * m + 2) :: lt, R)) [target_tm]⊢^{2 * (m + 1) + 6}
      (evalCfg (.Fwd, .f2 0 :: lt, .z3 (2 * m + 1) :: R)) := by
  have hwalk := walkWordLeft (M := target_tm) 2 1 [] [0, 0] [0] [0, 0] rfl
    (m + 1) ([0, 1, 1] +> encL lt) ([0, 1] +> encR R)
  have hstart : (([] +> ((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 1, 1] +> encL lt))) {{1}}>
      ([0] +> ([0, 1] +> encR R))) = evalCfg (.RetB, .f2 (2 * m + 2) :: lt, R) := by
    change (((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 1, 1] +> encL lt)) {{1}}>
      ([0, 0, 1] +> encR R)) = ((wordL (.f2 (2 * m + 2)) +> encL lt) {{1}}> ([0, 0, 1] +> encR R))
    rw [f2_even_split m (encL lt)]
  have hmid : (([] +> ([0, 1, 1] +> encL lt)) {{(1 : Fin 6)}}>
      ([0] +> ((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 1] +> encR R)))) =
      (([0, 1] +> ([1] +> encL lt)) {{(1 : Fin 6)}}> ([0, 0] +> (zWord (2 * m + 2) +>
        encR R))) := by
    rw [Counter.pow_succ_list [0, 0] m, append_assoc_blank, pow00_zWord_eq m (encR R)]
    rfl
  rw [hstart, hmid] at hwalk
  have hpost : (([0, 1] +> ([1] +> encL lt)) {{1}}> ([0, 0] +> (zWord (2 * m + 2) +> encR R)))
      [target_tm]⊢^{6}
      (evalCfg (.Fwd, .f2 0 :: lt, .z3 (2 * m + 1) :: R)) := by
    simpa [evalCfg, evalSegCfg, applyView, encL, encR,
      wordL, f2Tail, wordR, zWord, append_assoc_blank] using
      win_step ([1] +> encL lt) (zWord (2 * m + 2) +> encR R)
        (h := (rfl : checkHeadRight false false target_tm 6 1 [0, 1] [0, 0] 0 [0, 1] [0, 0] = true))
  exact Counter.multiStep_trans target_tm _ _ _ (2 * (m + 1)) 6 hwalk hpost

/-- Leftward `walkWordLeft` run drain for `.RetB` on `.f2 (2*m + 3) :: lt`. -/
private theorem drain_retB_f2_odd (m : ℕ) (lt : List LFrame536) (R : List RFrame536) :
    (evalCfg (.RetB, .f2 (2 * m + 3) :: lt, R)) [target_tm]⊢^{2 * (m + 1) + 8}
      (evalCfg (.RetB, lt, .z3 (2 * m + 2) :: R)) := by
  have hwalk := walkWordLeft (M := target_tm) 2 1 [] [0, 0] [0] [0, 0] rfl
    (m + 1) ([0, 0, 1, 1] +> encL lt) ([0, 1] +> encR R)
  have hstart : (([] +> ((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 0, 1, 1] +> encL lt))) {{1}}>
      ([0] +> ([0, 1] +> encR R))) = evalCfg (.RetB, .f2 (2 * m + 3) :: lt, R) := by
    change (((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 0, 1, 1] +> encL lt)) {{1}}>
      ([0, 0, 1] +> encR R)) = ((wordL (.f2 (2 * m + 3)) +> encL lt) {{1}}> ([0, 0, 1] +> encR R))
    rw [f2_odd_split m (encL lt)]
  have hmid : (([] +> ([0, 0, 1, 1] +> encL lt)) {{(1 : Fin 6)}}>
      ([0] +> ((([0, 0] : List (Fin 2)) ^ (m + 1)) +> ([0, 1] +> encR R)))) =
      (([0, 0, 1, 1] +> encL lt) {{(1 : Fin 6)}}> ([0, 0] +> (zWord (2 * m + 2) +> encR R))) := by
    rw [Counter.pow_succ_list [0, 0] m, append_assoc_blank, pow00_zWord_eq m (encR R)]
    rfl
  rw [hstart, hmid] at hwalk
  have hpost : (([0, 0, 1, 1] +> encL lt) {{1}}> ([0, 0] +> (zWord (2 * m + 2) +> encR R)))
      [target_tm]⊢^{8}
      (evalCfg (.RetB, lt, .z3 (2 * m + 2) :: R)) := by
    simpa [evalCfg, evalSegCfg, applyView, encL, encR,
      wordL, f2Tail, wordR, zWord, append_assoc_blank] using
      win_step (encL lt) (zWord (2 * m + 2) +> encR R)
        (h := (rfl : checkHeadRight false false target_tm 8 1 [0, 0, 1, 1] [0, 0] 1 []
          [0, 0, 1, 0, 0, 0] = true))
  exact Counter.multiStep_trans target_tm _ _ _ (2 * (m + 1)) 8 hwalk hpost

-- ----------------------------------------------------------------------------
-- 4. Bounded Boundary Transitions & Halting Branch
-- ----------------------------------------------------------------------------

/-- Helper peeling one leading `0` from `encR rt` when `rt` does not start with `.z1`. -/
private def peel0NonZ1 : List RFrame536 → List RFrame536
  | [] => []
  | .z1 o :: rt => .z1 o :: rt
  | .z2 o :: rt => .z1 o :: rt
  | .z3 0 :: rt => .z2 0 :: rt
  | .z3 (z + 1) :: rt => .z3 z :: rt

private theorem encR_peel0NonZ1 : ∀ (rt : List RFrame536),
    (∀ o rt2, rt ≠ .z1 o :: rt2) → encR rt = [0] +> encR (peel0NonZ1 rt)
  | [], _ => by simp [peel0NonZ1, encR, ListBlank.append]
  | .z1 o :: rt2, h => absurd rfl (h o rt2)
  | .z2 _ :: _, _ => rfl
  | .z3 0 :: _, _ => rfl
  | .z3 (_ + 1) :: _, _ => rfl

/-- Helper replacing `[0]` prefix of `encR rt` with `[0, 1]` for `Fwd` on `.z1 2 :: rt`. -/
private def peel0Push01 : List RFrame536 → List RFrame536
  | [] => [.z1 0]
  | .z1 o :: rt => .z1 (o + 1) :: rt
  | .z2 o :: rt => .z1 0 :: .z1 o :: rt
  | .z3 0 :: rt => .z1 0 :: .z2 0 :: rt
  | .z3 (z + 1) :: rt => .z1 0 :: .z3 z :: rt

private theorem encR_peel0Push01 : ∀ (rt : List RFrame536),
    ∃ r_tail : ListBlank (Fin 2), encR rt = [0] +> r_tail ∧ encR (peel0Push01 rt) = [0, 1] +> r_tail
  | [] => ⟨default,
    by simp [encR, ListBlank.append], rfl⟩
  | .z1 o :: rt => ⟨oWord o +> encR rt, rfl, rfl⟩
  | .z2 o :: rt => ⟨encR (.z1 o :: rt), rfl, rfl⟩
  | .z3 0 :: rt => ⟨encR (.z2 0 :: rt), rfl, rfl⟩
  | .z3 (z + 1) :: rt => ⟨encR (.z3 z :: rt), rfl, rfl⟩

private theorem step_fwd_to_retF_00 (L : List LFrame536) (R R' : List RFrame536)
    (r_tail : ListBlank (Fin 2)) (hR : encR R = [0, 0] +> r_tail)
    (hR' : encR R' = [0, 1] +> r_tail) :
    (evalCfg (.Fwd, L, R)) [target_tm]⊢^{5} (evalCfg (.RetF, L, R')) := by
  obtain ⟨tl, htl⟩ := encL_tail_zero L
  have h1 : evalCfg (.Fwd, L, R) = (([0] +> tl) {{0}}> ([0, 0] +> r_tail)) := by
    change (encL L {{0}}> encR R) = _
    rw [htl, hR]
  have h2 : evalCfg (.RetF, L, R') = (([] +> tl) {{5}}> ([0, 0, 1] +> r_tail)) := by
    change (encL L <{{5}} encR R') = _
    rw [htl, hR']
    simp [ListBlank.append]
  rw [h1, h2]
  exact win_step tl r_tail rfl

private theorem step_fwd_z10_nonZ1 (L : List LFrame536) (rt : List RFrame536)
    (h : ∀ o rt2, rt ≠ .z1 o :: rt2) :
    (evalCfg (.Fwd, L, .z1 0 :: rt)) [target_tm]⊢^{5}
      (evalCfg (.Fwd, .f2 0 :: L, peel0NonZ1 rt)) := by
  have hrt := encR_peel0NonZ1 rt h
  have h1 : evalCfg (.Fwd, L, .z1 0 :: rt) =
      (([] +> encL L) {{0}}> ([0, 1, 0] +> encR (peel0NonZ1 rt))) := by
    change (encL L {{0}}> ([0, 1] +> encR rt)) = _
    rw [hrt]
    simp [ListBlank.append]
  have h2 : evalCfg (.Fwd, .f2 0 :: L, peel0NonZ1 rt) =
      (([0, 1, 1] +> encL L) {{0}}> ([] +> encR (peel0NonZ1 rt))) := rfl
  rw [h1, h2]
  exact win_step (encL L) (encR (peel0NonZ1 rt)) rfl

private theorem step_fwd_z11_to_fwd (L : List LFrame536) (rt R' : List RFrame536)
    (r_tail : ListBlank (Fin 2)) (hrt : encR rt = [0] +> r_tail)
    (hR' : encR R' = [0, 0] +> r_tail) :
    (evalCfg (.Fwd, L, .z1 1 :: rt)) [target_tm]⊢^{10}
      (evalCfg (.Fwd, .f01 :: L, R')) := by
  obtain ⟨tl, htl⟩ := encL_tail_zero L
  have h1 : evalCfg (.Fwd, L, .z1 1 :: rt) =
      (([0] +> tl) {{0}}> ([0, 1, 1, 0] +> r_tail)) := by
    change (encL L {{0}}> ([0, 1, 1] +> encR rt)) = _
    rw [htl, hrt]
    simp [ListBlank.append]
  have h2 : evalCfg (.Fwd, .f01 :: L, R') =
      (([0, 1, 0] +> tl) {{0}}> ([0, 0] +> r_tail)) := by
    change (([0, 1] +> encL L) {{0}}> encR R') = _
    rw [htl, hR']
    simp [ListBlank.append]
  rw [h1, h2]
  exact win_step tl r_tail rfl

private theorem step_fwd_z11_z2 (L : List LFrame536) (o2 : ℕ) (rt2 : List RFrame536) :
    (evalCfg (.Fwd, L, .z1 1 :: .z2 o2 :: rt2)) [target_tm]⊢^{15}
      (evalCfg (.RetF, .f01 :: L, .z1 0 :: .z1 o2 :: rt2)) := by
  obtain ⟨tl, htl⟩ := encL_tail_zero L
  have h1 : evalCfg (.Fwd, L, .z1 1 :: .z2 o2 :: rt2) =
      (([0] +> tl) {{0}}> ([0, 1, 1, 0, 0] +> (oWord o2 +> encR rt2))) := by
    change (encL L {{0}}> ([0, 1, 1, 0, 0] +> (oWord o2 +> encR rt2))) = _
    rw [htl]
  have h2 : evalCfg (.RetF, .f01 :: L, .z1 0 :: .z1 o2 :: rt2) =
      (([1, 0] +> tl) {{5}}> ([0, 0, 1, 0] +> (oWord o2 +> encR rt2))) := by
    change (([0, 1] +> encL L) <{{5}} ([0, 1, 0] +> (oWord o2 +> encR rt2))) = _
    rw [htl]
    simp [ListBlank.append]
  rw [h1, h2]
  exact win_step tl (oWord o2 +> encR rt2) rfl

private theorem step_fwd_z12 (L : List LFrame536) (rt : List RFrame536) :
    (evalCfg (.Fwd, L, .z1 2 :: rt)) [target_tm]⊢^{9}
      (evalCfg (.Fwd, .f2 0 :: L, peel0Push01 rt)) := by
  obtain ⟨r_tail, hrt, hpush⟩ := encR_peel0Push01 rt
  have h1 : evalCfg (.Fwd, L, .z1 2 :: rt) =
      (([] +> encL L) {{0}}> ([0, 1, 1, 1, 0] +> r_tail)) := by
    change (encL L {{0}}> ([0, 1, 1, 1] +> encR rt)) = _
    rw [hrt]
    simp [ListBlank.append]
  have h2 : evalCfg (.Fwd, .f2 0 :: L, peel0Push01 rt) =
      (([0, 1, 1] +> encL L) {{0}}> ([0, 1] +> r_tail)) := by
    change (([0, 1, 1] +> encL L) {{0}}> encR (peel0Push01 rt)) = _
    rw [hpush]
  rw [h1, h2]
  exact win_step (encL L) r_tail rfl

private theorem step_fwd_z1_ge3_halts (L : List LFrame536) (o : ℕ) (rt : List RFrame536) :
    SegStepOut target_tm ValidSeg evalCfg (evalCfg (.Fwd, L, .z1 (o + 3) :: rt)) := by
  refine SegStepOut.halt (cfg_h := ([1, 0, 0, 1] +> encL L) {{(3 : Fin 6)}}> ([] +> (oWord o +>
    encR rt)))
    ⟨4, by omega, ?_⟩ ?_
  · have h1 : evalCfg (.Fwd, L, .z1 (o + 3) :: rt) =
        (([] +> encL L) {{(0 : Fin 6)}}> ([0, 1, 1, 1] +> (oWord o +> encR rt))) := by
      simp [evalCfg, evalSegCfg, applyView, encR, wordR, oWord, ListBlank.append]
    rw [h1]
    exact win_step (n := 4) (q := 0) (ls := []) (rs := [0, 1, 1, 1]) (q' := 3)
      (ls' := [1, 0, 0, 1]) (rs' := []) (encL L) (oWord o +> encR rt) rfl
  · cases o <;> simp [step, target_tm, oWord, ListBlank.append]

-- ----------------------------------------------------------------------------
-- 5. Complete Macro-Step Closure (`segmented_step_sound` & `segmented_system_closed`)
-- ----------------------------------------------------------------------------

private theorem segmented_step_sound (m : SegMode) (L : List LFrame536) (R : List RFrame536) :
    SegStepOut target_tm ValidSeg evalCfg (evalCfg (m, L, R)) := by
  cases m with
  | Fwd =>
      rcases R with _ | ⟨r0, rt⟩
      · exact SegStepOut.step trivial ⟨5, by omega,
          step_fwd_to_retF_00 L [] [.z1 0] default default_eq_00 rfl⟩
      · cases r0 with
        | z2 o =>
            exact SegStepOut.step trivial ⟨5, by omega,
              step_fwd_to_retF_00 L (.z2 o :: rt) (.z1 (o + 1) :: rt) (oWord o +> encR rt) rfl rfl⟩
        | z3 z =>
            rcases z with _ | _ | z
            · exact SegStepOut.step trivial ⟨5, by omega,
                step_fwd_to_retF_00 L (.z3 0 :: rt) (.z1 0 :: .z1 0 :: rt) (encR (.z1 0 :: rt)) rfl
                  rfl⟩
            · exact SegStepOut.step trivial ⟨5, by omega,
                step_fwd_to_retF_00 L (.z3 1 :: rt) (.z1 0 :: .z2 0 :: rt) (encR (.z2 0 :: rt)) rfl
                  rfl⟩
            · exact SegStepOut.step trivial ⟨5, by omega,
                step_fwd_to_retF_00 L (.z3 (z + 2) :: rt) (.z1 0 :: .z3 z :: rt) (encR (.z3 z ::
                  rt)) rfl rfl⟩
        | z1 o =>
            rcases o with _ | _ | _ | o
            · rcases rt with _ | ⟨r1, rt2⟩
              · exact SegStepOut.step trivial ⟨5, by omega,
                  step_fwd_z10_nonZ1 L [] (fun _ _ h => nomatch h)⟩
              · cases r1 with
                | z1 o2 =>
                    rcases o2 with _ | o2
                    · have hs := sweep_fwd_z10_pairs (.z1 0 :: .z1 0 :: rt2) L
                      refine SegStepOut.step trivial ⟨6 * (peelZ10Pairs L (.z1 0 :: .z1 0 ::
                        rt2)).1,
                        ?_, hs⟩
                      simp only [peelZ10Pairs]
                      omega
                    · exact SegStepOut.step trivial ⟨6 + (o2 + 1), by omega,
                        drain_fwd_z10_z1 L (o2 + 1) rt2⟩
                | z2 o2 =>
                    exact SegStepOut.step trivial ⟨5, by omega,
                      step_fwd_z10_nonZ1 L (.z2 o2 :: rt2) (fun _ _ h => nomatch h)⟩
                | z3 z2 =>
                    exact SegStepOut.step trivial ⟨5, by omega,
                      step_fwd_z10_nonZ1 L (.z3 z2 :: rt2) (fun _ _ h => nomatch h)⟩
            · rcases rt with _ | ⟨r1, rt2⟩
              · exact SegStepOut.step trivial ⟨10, by omega,
                  step_fwd_z11_to_fwd L [] [] default
                    (by simp [encR, ListBlank.append])
                    default_eq_00⟩
              · cases r1 with
                | z1 o2 =>
                    exact SegStepOut.step trivial ⟨10, by omega,
                      step_fwd_z11_to_fwd L (.z1 o2 :: rt2) (.z2 o2 :: rt2)
                        (oWord o2 +> encR rt2) rfl rfl⟩
                | z2 o2 =>
                    exact SegStepOut.step trivial ⟨15, by omega, step_fwd_z11_z2 L o2 rt2⟩
                | z3 z2 =>
                    exact SegStepOut.step trivial ⟨10, by omega,
                      step_fwd_z11_to_fwd L (.z3 z2 :: rt2) (.z3 (z2 + 1) :: rt2)
                        (zWord (z2 + 2) +> encR rt2) rfl rfl⟩
            · exact SegStepOut.step trivial ⟨9, by omega, step_fwd_z12 L rt⟩
            · exact step_fwd_z1_ge3_halts L o rt
  | RetF =>
      rcases L with _ | ⟨l0, lt⟩
      · refine SegStepOut.step (s' := (.Fwd, [], .z1 0 :: R)) trivial ⟨5, by omega, ?_⟩
        have h1 : evalCfg (.RetF, [], R) = (([1, 0, 0] +> default) {{5}}> ([0] +> encR R)) := by
          simp [evalCfg, evalSegCfg, applyView, encL,   ListBlank.append]
        have h2 : evalCfg (.Fwd, [], .z1 0 :: R) =
          (([0, 1] +> default) {{0}}> ([0, 1] +> encR R)) := rfl
        rw [h1, h2]
        exact win_step default (encR R) rfl
      · cases l0 with
        | f01 =>
            exact SegStepOut.step trivial (sweep_retF_f01 lt R)
        | f0111 =>
            obtain ⟨tl, htl⟩ := encL_tail_zero lt
            refine SegStepOut.step (s' := (.RetF, lt, .z1 0 :: .z1 0 :: R)) trivial ⟨8,
              by omega, ?_⟩
            have h1 : evalCfg (.RetF, .f0111 :: lt, R) =
                (([1, 1, 1, 0] +> tl) {{5}}> ([0] +> encR R)) := by
              change (([0, 1, 1, 1] +> encL lt) <{{5}} encR R) = _
              rw [htl]
              simp [ListBlank.append]
            have h2 : evalCfg (.RetF, lt, .z1 0 :: .z1 0 :: R) =
                (([] +> tl) {{5}}> ([0, 0, 1, 0, 1] +> encR R)) := by
              change (encL lt <{{5}} ([0, 1, 0, 1] +> encR R)) = _
              rw [htl]
              simp [ListBlank.append]
            rw [h1, h2]
            exact win_step tl (encR R) rfl
        | f2 z =>
            rcases z with _ | _ | z
            · refine SegStepOut.step (s' := (.RetB, lt, R)) trivial ⟨4, by omega, ?_⟩
              have h1 : evalCfg (.RetF, .f2 0 :: lt, R) =
                  (([1, 1] +> encL lt) {{5}}> ([0] +> encR R)) := by
                simp [evalCfg, evalSegCfg, applyView, encL, wordL, f2Tail, ListBlank.append]
              have h2 : evalCfg (.RetB, lt, R) =
                  (([] +> encL lt) {{1}}> ([0, 0, 1] +> encR R)) := rfl
              rw [h1, h2]
              exact win_step (encL lt) (encR R) rfl
            · refine SegStepOut.step (s' := (.Fwd, .f0111 :: lt, R)) trivial ⟨3, by omega, ?_⟩
              have h1 : evalCfg (.RetF, .f2 1 :: lt, R) =
                  (([0, 1, 1] +> encL lt) {{5}}> ([0] +> encR R)) := by
                simp [evalCfg, evalSegCfg, applyView, encL, wordL, f2Tail, ListBlank.append]
              have h2 : evalCfg (.Fwd, .f0111 :: lt, R) =
                  (([0, 1, 1, 1] +> encL lt) {{0}}> ([] +> encR R)) := rfl
              rw [h1, h2]
              exact win_step (encL lt) (encR R) rfl
            · refine SegStepOut.step (s' := (.Fwd, .f01 :: .f2 z :: lt, R)) trivial ⟨3,
              by omega, ?_⟩
              have h1 : evalCfg (.RetF, .f2 (z + 2) :: lt, R) =
                  (([0] +> encL (.f2 z :: lt)) {{5}}> ([0] +> encR R)) := by
                simp [evalCfg, evalSegCfg, applyView, encL, wordL, f2Tail, ListBlank.append]
              have h2 : evalCfg (.Fwd, .f01 :: .f2 z :: lt, R) =
                  (([0, 1] +> encL (.f2 z :: lt)) {{0}}> ([] +> encR R)) := rfl
              rw [h1, h2]
              exact win_step (encL (.f2 z :: lt)) (encR R) rfl
  | RetB =>
      rcases L with _ | ⟨l0, lt⟩
      · exact SegStepOut.step trivial ⟨6, by omega, step_retB_to_fwd [] R default rfl⟩
      · cases l0 with
        | f01 =>
            exact SegStepOut.step trivial ⟨6,
              by omega, step_retB_to_fwd (.f01 :: lt) R (encL lt) rfl⟩
        | f0111 =>
            exact SegStepOut.step trivial ⟨6, by omega,
              step_retB_to_fwd (.f0111 :: lt) R ([1, 1] +> encL lt) rfl⟩
        | f2 z =>
            rcases z with _ | _ | z
            · exact SegStepOut.step trivial ⟨6, by omega,
                step_retB_to_fwd (.f2 0 :: lt) R ([1] +> encL lt) rfl⟩
            · exact SegStepOut.step trivial (sweep_retB_f21 lt R)
            · rcases Nat.even_or_odd z with ⟨m, rfl⟩ | ⟨m, rfl⟩
              · rw [show m + m = 2 * m by omega]
                exact SegStepOut.step trivial ⟨2 * (m + 1) + 6, by omega, drain_retB_f2_even m lt R⟩
              · exact SegStepOut.step trivial ⟨2 * (m + 1) + 8, by omega, drain_retB_f2_odd m lt R⟩


/-- Canonical mode list for holdout #536. -/
def modes : List SegMode := [.Fwd, .RetF, .RetB]

private theorem wordL_len (x : LFrame536) : 2 ≤ (wordL x).length := by
  cases x with
  | f01 => decide
  | f0111 => decide
  | f2 z =>
    simp only [wordL, f2Tail]
    induction z <;> simp

private theorem wordL_ne_nil (x : LFrame536) : wordL x ≠ [] := by
  intro h; have := wordL_len x; simp [h] at this

private theorem wordL_ne_zero (x : LFrame536) : wordL x ≠ [(0 : Fin 2)] := by
  intro h; have := wordL_len x; simp [h] at this

private theorem wordR_len (x : RFrame536) : 2 ≤ (wordR x).length := by
  cases x with
  | z1 o => simp only [wordR, List.length_cons, oWord]; induction o <;> simp
  | z2 o => simp only [wordR, List.length_cons, oWord]; induction o <;> simp
  | z3 z => simp only [wordR, zWord, List.length_cons]; omega

private theorem wordR_ne_nil (x : RFrame536) : wordR x ≠ [] := by
  intro h; have := wordR_len x; simp [h] at this

private theorem wordR_ne_zero (x : RFrame536) : wordR x ≠ [(0 : Fin 2)] := by
  intro h; have := wordR_len x; simp [h] at this

private theorem segs_wf (s : SegState) (_ : ValidSeg s) :
    (segsL s).length ≤ 3 ∧ (segsR s).length ≤ 3 ∧
      (∀ r ∈ segsL s, r.WellFormed) ∧ (∀ r ∈ segsR s, r.WellFormed) := by
  refine ⟨by simp [segsL], by simp [segsR], ?_, ?_⟩
  · simp only [segsL, List.mem_cons, List.not_mem_nil, or_false]
    rintro _ (rfl | rfl)
    · refine ⟨fun w hw => ?_, fun h => ?_⟩
      · rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
        exact wordL_ne_nil x
      · rcases List.mem_map.mp (h 0) with ⟨x, _, hx⟩
        exact wordL_ne_zero x hx
    · simp [SegRegionKind.WellFormed]
  · simp only [segsR, List.mem_singleton]
    rintro _ rfl
    refine ⟨fun w hw => ?_, fun h => ?_⟩
    · rcases List.mem_map.mp hw with ⟨x, _, rfl⟩
      exact wordR_ne_nil x
    · rcases List.mem_map.mp (h 0) with ⟨x, _, hx⟩
      exact wordR_ne_zero x hx

private theorem valid_seg_modes (m : SegMode) :
    ∃ (q : Fin 6) (vL vR : HalfTapeView (Fin 2)),
      viewPrefixLen vL ≤ 8 ∧ viewPrefixLen vR ≤ 8 ∧
      ∀ s, ValidSeg s → modeOf s = m →
        (evalCfg s = ⟨some q, ⟨(0 : Fin 2),
          applyView vL (evalSegmentedHalf (segsL s)),
          applyView vR (evalSegmentedHalf (segsR s))⟩⟩) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) <{{q}}
          (applyView vR (evalSegmentedHalf (segsR s)))) ∨
        (evalCfg s = (applyView vL (evalSegmentedHalf (segsL s))) {{q}}>
          (applyView vR (evalSegmentedHalf (segsR s)))) := by
  refine ⟨(modeSpec m).q, (modeSpec m).vL, (modeSpec m).vR,
    by cases m <;> decide,
    by cases m <;> decide, ?_⟩
  intro s _ hm
  have hL : evalSegmentedHalf (segsL s) = encL s.2.1 :=
    (evalSegmentedHalf_finWord_gadget wordL [0, 1] s.2.1).trans (encL_eq s.2.1).symm
  have hR : evalSegmentedHalf (segsR s) = encR s.2.2 :=
    (evalSegmentedHalf_finWord_map wordR s.2.2).trans (encR_eq s.2.2).symm
  rw [hL, hR]
  rcases s with ⟨m', L, R⟩
  dsimp [modeOf] at hm
  subst hm
  cases m' with
  | Fwd => exact Or.inr (Or.inr rfl)
  | RetF => exact Or.inr (Or.inl rfl)
  | RetB => exact Or.inr (Or.inr rfl)

private theorem segmented_system_closed (s : SegState) (_ : ValidSeg s) :
    ∃ cfg', ((evalCfg s) [target_tm]⊢⁺ cfg') ∧
      ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (step target_tm cfg').isNone) :=
  segmented_step_sound s.1 s.2.1 s.2.2

/-- Explicit `IsClosedSegmentedSystem` witness for `1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC`. -/
theorem is_closed_segmented_system :
    IsClosedSegmentedSystem target modes ValidSeg modeOf segsL segsR evalCfg := by
  rw [target_eq_target_tm]
  refine ⟨by decide, by decide, fun m => by cases m <;> simp [modes],
    segs_wf, valid_seg_modes, Or.inl segsL_nowhere_dense, Or.inl segsL_nowhere_dense,
    Or.inl segsR_nowhere_dense, ⟨s₀, trivial, init_reaches_segmented_system⟩,
    segmented_system_closed⟩

/-- Segmented cryptid certificate for `1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC`. -/
theorem is_segmented_cryptid : IsSegmentedCryptid target :=
  ⟨SegState, SegMode, modes, ValidSeg, modeOf, segsL, segsR, evalCfg, is_closed_segmented_system⟩

end BusyBeaver.M_1RB0RA_0LC0RF_0LB1RD_1LEHHH_1RA0LF_1LE0RC
