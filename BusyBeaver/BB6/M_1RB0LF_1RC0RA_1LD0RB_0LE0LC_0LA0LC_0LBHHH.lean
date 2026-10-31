/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Bridge
public import BusyBeaver.BB6.A6.Entry0
public import BusyBeaver.BB6.A6.Entry1
public import BusyBeaver.BB6.A6.Entry2
public import BusyBeaver.BB6.A6.Entry3
public import BusyBeaver.BB6.A6.Entry4
public import BusyBeaver.BB6.A6.Entry5
public import BusyBeaver.BB6.A6.ReturnExits
public import BusyBeaver.BB6.A6.ReturnReplay

/-!
# Non-Halting of `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` (`A6`)

Combines the six kernel-verified Entry milestone phases (`init [] ⊢* C(8)` in
`752,265,440,525,431,967` steps) with the symbolic affine Return certificate (`C(k + 8) ⊢⁺ C(k + 9)`
in `304,037,417,082 + 119,808 * k` steps for every `k : ℕ`) to establish `IsNotHalt target` and
`¬ ConjectureMachines.Halts machine`.
-/

@[expose] public section

namespace BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH

/-- The six-state `A6` machine loaded via Cryptids' shared RLE parser. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---"

/-- Canonical `BusyBeaver.Machine` representation of `A6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH

namespace BusyBeaver.BB6.A6

open Turing
open BusyBeaver.WordRLE BusyBeaver.AffRLE

/-! ## Canonical Configuration Family and Stack Flattening Helpers -/

/-- Composite word lookup for `A6`'s synthesized 414-word vocabulary. -/
def wOf : ℕ → List (Fin 2) :=
  vocabWord baseWord a6Vocab

/-- Canonical symbolic configuration family `familyCfg k = C(k + 8)`. -/
def familyCfg (k : ℕ) : Cfg (Fin 2) (Fin 6) :=
  evalAffCfg qOf wOf k initReturnCfg

private def repList (n : ℕ) (xs : List α) : List α :=
  match n with
  | 0 => []
  | n + 1 => xs ++ repList n xs

private def flatLeftRuns (wordOf : ℕ → List (Fin 2)) : List Run → List (Fin 2)
  | [] => []
  | ⟨w, c⟩ :: rest => (wordOf w).reverse ^ c ++ flatLeftRuns wordOf rest

private theorem evalSide_false_eq_flat (wordOf : ℕ → List (Fin 2)) (xs : List Run) :
    evalSide false wordOf xs = ListBlank.append (flatLeftRuns wordOf xs) default := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with ⟨w, c⟩
    simp [evalSide, flatLeftRuns, ih, ListBlank.append_assoc]

private theorem flatLeftRuns_append (wordOf : ℕ → List (Fin 2)) (xs ys : List Run) :
    flatLeftRuns wordOf (xs ++ ys) = flatLeftRuns wordOf xs ++ flatLeftRuns wordOf ys := by
  induction xs with
  | nil => rfl
  | cons r xs ih => simp [flatLeftRuns, ih, List.append_assoc]

private theorem flatLeftRuns_repList (wordOf : ℕ → List (Fin 2)) (n : ℕ) (xs : List Run) :
    flatLeftRuns wordOf (repList n xs) = (flatLeftRuns wordOf xs) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [repList, flatLeftRuns_append, ih, ← list_pow_succ]

private def flatAffLeft (wordOf : ℕ → List (Fin 2)) (k : ℕ) : List AffRun → List (Fin 2)
  | [] => []
  | ⟨w, c⟩ :: rest => (wordOf w).reverse ^ c.eval k ++ flatAffLeft wordOf k rest

private theorem evalAffSide_false_eq_flat (wordOf : ℕ → List (Fin 2)) (k : ℕ) (xs : List AffRun) :
    evalAffSide false wordOf k xs = ListBlank.append (flatAffLeft wordOf k xs) default := by
  induction xs with
  | nil => rfl
  | cons r xs ih =>
    rcases r with ⟨w, c⟩
    simp [evalAffSide, flatAffLeft, ih, ListBlank.append_assoc]

private theorem flatAffLeft_append (wordOf : ℕ → List (Fin 2)) (k : ℕ) (xs ys : List AffRun) :
    flatAffLeft wordOf k (xs ++ ys) =
      flatAffLeft wordOf k xs ++ flatAffLeft wordOf k ys := by
  induction xs with
  | nil => rfl
  | cons r xs ih => simp [flatAffLeft, ih, List.append_assoc]

private theorem flatAffLeft_const (wordOf : ℕ → List (Fin 2)) (k : ℕ) :
    ∀ {xs : List AffRun}, xs.all (fun r ↦ Nat.beq r.count.a 0) = true →
      flatAffLeft wordOf k xs = flatAffLeft wordOf 0 xs
  | [], _ => rfl
  | ⟨w, ⟨a, b⟩⟩ :: xs, h => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have ha : a = 0 := Nat.eq_of_beq_eq_true h.1
    subst ha
    simp [flatAffLeft, AffNat.eval, flatAffLeft_const wordOf k h.2]

/-! ## Part 1: Entry Derivation from Blank Tape to `C(8)` -/

private theorem evalEntryCfg_start :
    evalEntryCfg qOf baseWord ⟨0, false, [], []⟩ = init [] := by
  simpa [evalEntryCfg, dirCfg, evalSide, qOf] using
    (init_nil_eq_headLeft (Γ := Fin 2) (Λ := Fin 6)).symm

/-- Exact Entry derivation from the blank tape `init []` to `C(8)` in
`752,265,440,525,431,967` steps. -/
theorem entry_to_c8 :
    ReachesStar a6Target (init []) (evalEntryCfg qOf baseWord (entryMilestone 8)) := by
  have hchain : EntryReaches stepEntry 752265440525431967 ⟨0, false, [], []⟩ (entryMilestone 8) :=
    EntryReaches.cast_dt
      (entry_phase0.trans (entry_phase1.trans (entry_phase2.trans
        (entry_phase3.trans (entry_phase4.trans entry_phase5)))))
      (by decide +kernel)
  have hsound := hchain.sound stepEntry_sound
  rw [evalEntryCfg_start] at hsound
  exact hsound.to_star

/-! ## Part 2: Bridge Equality `evalEntryCfg ... (entryMilestone 8) = familyCfg 0` -/

private def wRunsRev : List Run := pushRunsLeft wRuns []
private def qRunsRev : List Run := pushRunsLeft qRuns []
private def vTailRunsRev : List Run := (pushRunsLeft vRuns []).take 8
private def pRunsRev : List Run := pushRunsLeft pRuns []
private def uRunsRev : List Run := pushRunsLeft uRuns []

private theorem entry8_left_decomp :
    (entryMilestone 8).left =
      wRunsRev ++ repList 8 qRunsRev ++ vTailRunsRev ++
        [Run.mk 2 791761176] ++ repList 8 pRunsRev ++ uRunsRev := by
  exact eq_of_beq (by decide +kernel)

private theorem init_left_decomp :
    initReturnCfg.left =
      initReturnCfg.left.take 5 ++
        [AffRun.mk 5 ⟨1, 8⟩] ++
        (initReturnCfg.left.drop 6).take 8 ++
        [AffRun.mk 2 ⟨0, 791761176⟩] ++
        [AffRun.mk 4 ⟨1, 8⟩] ++
        initReturnCfg.left.drop 16 := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_w :
    flatLeftRuns baseWord wRunsRev = flatAffLeft wOf 0 (initReturnCfg.left.take 5) := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_q :
    flatLeftRuns baseWord qRunsRev = (wOf 5).reverse := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_v :
    flatLeftRuns baseWord vTailRunsRev =
      flatAffLeft wOf 0 ((initReturnCfg.left.drop 6).take 8) := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_x : wOf 2 = baseWord 2 := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_p :
    flatLeftRuns baseWord pRunsRev = (wOf 4).reverse := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_u :
    flatLeftRuns baseWord uRunsRev = flatAffLeft wOf 0 (initReturnCfg.left.drop 16) := by
  exact eq_of_beq (by decide +kernel)

private theorem bridge1_y : wOf 1 = baseWord 1 := by
  exact eq_of_beq (by decide +kernel)

/-- The Entry milestone configuration `C(8)` is identical to `familyCfg 0`. -/
theorem entryMilestone_eight_eq :
    evalEntryCfg qOf baseWord (entryMilestone 8) = familyCfg 0 := by
  have heq : (entryMilestone 8).q = 1 := rfl
  have hed : (entryMilestone 8).dir = true := rfl
  have her : (entryMilestone 8).right = [⟨1, 6⟩] := rfl
  have hiq : initReturnCfg.q = 1 := eq_of_beq (by decide +kernel)
  have hid : initReturnCfg.dir = true := eq_of_beq (by decide +kernel)
  have hir : initReturnCfg.right = [⟨1, ⟨0, 6⟩⟩] := eq_of_beq (by decide +kernel)
  unfold evalEntryCfg familyCfg evalAffCfg
  rw [heq, hed, her, hiq, hid, hir]
  refine congr (congrArg (dirCfg qOf 1 true) ?_) ?_
  · rw [evalSide_false_eq_flat, evalAffSide_false_eq_flat]
    refine congrArg (ListBlank.append · default) ?_
    rw [entry8_left_decomp, init_left_decomp]
    simp only [flatLeftRuns_append, flatAffLeft_append, flatLeftRuns_repList]
    have hq0 : flatAffLeft wOf 0 [AffRun.mk 5 ⟨1, 8⟩] = (wOf 5).reverse ^ 8 := by
      simp [flatAffLeft, AffNat.eval]
    have hx0 : flatLeftRuns baseWord [Run.mk 2 791761176] =
        flatAffLeft wOf 0 [AffRun.mk 2 ⟨0, 791761176⟩] := by
      simp [flatLeftRuns, flatAffLeft, AffNat.eval, bridge1_x]
    have hp0 : flatAffLeft wOf 0 [AffRun.mk 4 ⟨1, 8⟩] = (wOf 4).reverse ^ 8 := by
      simp [flatAffLeft, AffNat.eval]
    rw [bridge1_w, bridge1_q, hq0, bridge1_v, hx0, bridge1_p, hp0, bridge1_u]
  · simp [evalSide, evalAffSide, AffNat.eval, bridge1_y]

/-! ## Part 3: Bridge Equality `evalAffCfg ... k a6FinalCfg = familyCfg (k + 1)` -/

private def finalPre : List AffRun := a6FinalCfg.left.take 5
private def finalQBRuns : List AffRun := (a6FinalCfg.left.drop 5).take 9
private def finalQChunk : List AffRun :=
  finalQBRuns ++ [AffRun.mk 413 ⟨1, 8⟩, AffRun.mk 2 ⟨0, 32⟩]
private def finalMid : List AffRun := (a6FinalCfg.left.drop 16).take 8
private def finalPTail : List AffRun := (a6FinalCfg.left.drop 28).take 8
private def finalXPChunk : List AffRun :=
  [AffRun.mk 2 ⟨0, 791761144⟩, AffRun.mk 241 ⟨0, 1⟩,
    AffRun.mk 410 ⟨0, 1⟩, AffRun.mk 294 ⟨1, 6⟩] ++ finalPTail
private def finalSuf : List AffRun := a6FinalCfg.left.drop 36

private theorem final_left_decomp :
    a6FinalCfg.left =
      finalPre ++ finalQChunk ++ finalMid ++ finalXPChunk ++ finalSuf := by
  exact eq_of_beq (by decide +kernel)

private theorem const_pre_eq : finalPre = initReturnCfg.left.take 5 :=
  eq_of_beq (by decide +kernel)
private theorem const_pre_ok : finalPre.all (fun r ↦ Nat.beq r.count.a 0) = true := by
  decide +kernel
private theorem const_mid_eq : finalMid = (initReturnCfg.left.drop 6).take 8 :=
  eq_of_beq (by decide +kernel)
private theorem const_mid_ok : finalMid.all (fun r ↦ Nat.beq r.count.a 0) = true := by
  decide +kernel
private theorem const_suf_eq : finalSuf = initReturnCfg.left.drop 16 :=
  eq_of_beq (by decide +kernel)
private theorem const_suf_ok : finalSuf.all (fun r ↦ Nat.beq r.count.a 0) = true := by
  decide +kernel
private theorem const_qb_ok : finalQBRuns.all (fun r ↦ Nat.beq r.count.a 0) = true := by
  decide +kernel
private theorem const_pt_ok : finalPTail.all (fun r ↦ Nat.beq r.count.a 0) = true := by
  decide +kernel

private def qARev : List (Fin 2) := (wOf 2).reverse ^ 32
private def qBRev : List (Fin 2) := flatAffLeft wOf 0 finalQBRuns

private theorem q_word_413 : (wOf 413).reverse = qARev ++ qBRev := by
  exact eq_of_beq (by decide +kernel)

private theorem q_word_5 : (wOf 5).reverse = qBRev ++ qARev := by
  exact eq_of_beq (by decide +kernel)

private theorem final_q_chunk_eq (k : ℕ) :
    flatAffLeft wOf k finalQChunk =
      flatAffLeft wOf (k + 1) [AffRun.mk 5 ⟨1, 8⟩] := by
  unfold finalQChunk
  rw [flatAffLeft_append, flatAffLeft_const wOf k const_qb_ok]
  change qBRev ++ ((wOf 413).reverse ^ (AffNat.mk 1 8).eval k ++
      ((wOf 2).reverse ^ (AffNat.mk 0 32).eval k ++ [])) =
    (wOf 5).reverse ^ (AffNat.mk 1 8).eval (k + 1) ++ []
  have hk1 : (AffNat.mk 1 8).eval k = k + 8 := by simp [AffNat.eval]
  have hk2 : (AffNat.mk 0 32).eval k = 32 := by simp [AffNat.eval]
  have hk3 : (AffNat.mk 1 8).eval (k + 1) = (k + 8) + 1 := by dsimp [AffNat.eval]; omega
  rw [hk1, hk2, hk3, List.append_nil, List.append_nil]
  change qBRev ++ ((wOf 413).reverse ^ (k + 8) ++ qARev) = (wOf 5).reverse ^ ((k + 8) + 1)
  rw [q_word_413, q_word_5, lpow_rot qARev qBRev (k + 8), ← List.append_assoc, ← list_pow_succ]

private def pBRev : List (Fin 2) := (wOf 0).reverse ++ (wOf 1).reverse ^ 5
private def pARev : List (Fin 2) := (wOf 1).reverse ^ 5 ++ (wOf 2).reverse ^ 8

private theorem p_word_241 : (wOf 241).reverse = (wOf 2).reverse ^ 19 := by
  exact eq_of_beq (by decide +kernel)

private theorem p_word_410 : (wOf 410).reverse = (wOf 2).reverse ^ 13 ++ pBRev := by
  exact eq_of_beq (by decide +kernel)

private theorem p_word_294 : (wOf 294).reverse = pARev ++ pBRev := by
  exact eq_of_beq (by decide +kernel)

private theorem p_word_4 : (wOf 4).reverse = pBRev ++ pARev := by
  exact eq_of_beq (by decide +kernel)

private theorem p_tail_eq :
    flatAffLeft wOf 0 finalPTail = pARev ++ (wOf 4).reverse ^ 2 := by
  exact eq_of_beq (by decide +kernel)

private theorem final_xp_chunk_eq (k : ℕ) :
    flatAffLeft wOf k finalXPChunk =
      flatAffLeft wOf (k + 1) [AffRun.mk 2 ⟨0, 791761176⟩] ++
        flatAffLeft wOf (k + 1) [AffRun.mk 4 ⟨1, 8⟩] := by
  unfold finalXPChunk
  rw [flatAffLeft_append, flatAffLeft_const wOf k const_pt_ok, p_tail_eq]
  have he1 : (AffNat.mk 0 791761144).eval k = 791761144 := by simp [AffNat.eval]
  have he2 : (AffNat.mk 0 1).eval k = 1 := by simp [AffNat.eval]
  have he3 : (AffNat.mk 1 6).eval k = k + 6 := by simp [AffNat.eval]
  have he4 : (AffNat.mk 0 791761176).eval (k + 1) = 791761176 := by simp [AffNat.eval]
  have he5 : (AffNat.mk 1 8).eval (k + 1) = (k + 6) + 1 + 2 := by dsimp [AffNat.eval]; omega
  simp only [flatAffLeft, he1, he2, he3, he4, he5, list_pow_one, List.append_nil]
  rw [p_word_241, p_word_410, p_word_294]
  simp only [List.append_assoc]
  have hx1 : ∀ tail : List (Fin 2),
      (wOf 2).reverse ^ 19 ++ ((wOf 2).reverse ^ 13 ++ tail) =
        (wOf 2).reverse ^ 32 ++ tail := by
    intro tail; rw [← List.append_assoc, ← list_pow_add]
  have hx2 : ∀ tail : List (Fin 2),
      (wOf 2).reverse ^ 791761144 ++ ((wOf 2).reverse ^ 32 ++ tail) =
        (wOf 2).reverse ^ 791761176 ++ tail := by
    intro tail
    have hnum : 791761144 + 32 = 791761176 := eq_of_beq (by decide +kernel)
    rw [← List.append_assoc, ← list_pow_add, hnum]
  rw [hx1, hx2]
  refine congrArg ((wOf 2).reverse ^ 791761176 ++ ·) ?_
  have hrot : pBRev ++ ((pARev ++ pBRev) ^ (k + 6) ++ (pARev ++ (wOf 4).reverse ^ 2)) =
      (pBRev ++ ((pARev ++ pBRev) ^ (k + 6) ++ pARev)) ++ (wOf 4).reverse ^ 2 := by
    simp only [List.append_assoc]
  rw [hrot, lpow_rot pARev pBRev (k + 6), ← List.append_assoc, ← p_word_4,
    ← list_pow_succ, ← list_pow_add]

/-- The post-return symbolic configuration `a6FinalCfg` at `k` equals `familyCfg (k + 1)`. -/
theorem a6_final_eq_next (k : ℕ) :
    evalAffCfg qOf wOf k a6FinalCfg = familyCfg (k + 1) := by
  have hfq : a6FinalCfg.q = 1 := eq_of_beq (by decide +kernel)
  have hfd : a6FinalCfg.dir = true := eq_of_beq (by decide +kernel)
  have hfr : a6FinalCfg.right = [⟨1, ⟨0, 6⟩⟩] := eq_of_beq (by decide +kernel)
  have hiq : initReturnCfg.q = 1 := eq_of_beq (by decide +kernel)
  have hid : initReturnCfg.dir = true := eq_of_beq (by decide +kernel)
  have hir : initReturnCfg.right = [⟨1, ⟨0, 6⟩⟩] := eq_of_beq (by decide +kernel)
  unfold familyCfg evalAffCfg
  rw [hfq, hfd, hfr, hiq, hid, hir]
  refine congr (congrArg (dirCfg qOf 1 true) ?_) ?_
  · rw [evalAffSide_false_eq_flat, evalAffSide_false_eq_flat]
    refine congrArg (ListBlank.append · default) ?_
    rw [final_left_decomp, init_left_decomp]
    simp only [flatAffLeft_append]
    have h1 : flatAffLeft wOf k finalPre =
        flatAffLeft wOf (k + 1) (initReturnCfg.left.take 5) := by
      rw [flatAffLeft_const wOf k const_pre_ok, ← const_pre_eq,
        ← flatAffLeft_const wOf (k + 1) const_pre_ok]
    have h3 : flatAffLeft wOf k finalMid =
        flatAffLeft wOf (k + 1) ((initReturnCfg.left.drop 6).take 8) := by
      rw [flatAffLeft_const wOf k const_mid_ok, ← const_mid_eq,
        ← flatAffLeft_const wOf (k + 1) const_mid_ok]
    have h5 : flatAffLeft wOf k finalSuf =
        flatAffLeft wOf (k + 1) (initReturnCfg.left.drop 16) := by
      rw [flatAffLeft_const wOf k const_suf_ok, ← const_suf_eq,
        ← flatAffLeft_const wOf (k + 1) const_suf_ok]
    rw [h1, final_q_chunk_eq k, h3, final_xp_chunk_eq k, h5]
    simp only [List.append_assoc]
  · simp [evalAffSide, AffNat.eval]

/-! ## Part 4: Symbolic Family Step and Non-Halting Closure -/

private theorem reachesPlus_of_reachesIn_eq {n : ℕ} {c₁ c₂ c₂' : Cfg (Fin 2) (Fin 6)}
    (hpos : 0 < n) (hr : ReachesIn a6Target n c₁ c₂) (heq : c₂ = c₂') :
    ReachesPlus a6Target c₁ c₂' :=
  ⟨n, hpos, heq ▸ hr⟩

/-- For every `k : ℕ`, `familyCfg k` reaches `familyCfg (k + 1)` in
`304,037,417,082 + 119,808 * k > 0` steps. -/
theorem family_step (k : ℕ) :
    ReachesPlus a6Target (familyCfg k) (familyCfg (k + 1)) := by
  have hcert : ReachesIn a6Target (returnTarget.eval k)
      (familyCfg k) (evalAffCfg qOf wOf k a6FinalCfg) :=
    verifyReturnCert_sound (cert := a6Cert) fastExit2_sound baseWord_zero_blank
      a6_vocab_blank0 a6_exits_ok a6_replay_ok k
  have hpos : 0 < returnTarget.eval k :=
    Nat.add_pos_right (119808 * k) (by decide)
  exact reachesPlus_of_reachesIn_eq hpos hcert (a6_final_eq_next k)

end BusyBeaver.BB6.A6

namespace BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH

private theorem a6Target_eq_target : BB6.A6.a6Target = target := by
  funext ⟨q, hq⟩ ⟨a, ha⟩
  have hq6 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  have ha2 : a = 0 ∨ a = 1 := by omega
  rcases hq6 with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases ha2 with rfl | rfl <;>
    rfl

/-- Machine `1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LB---` (`A6`) does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← a6Target_eq_target]
  have hinit : ReachesStar BB6.A6.a6Target (init []) (BB6.A6.familyCfg 0) := by
    rw [← BB6.A6.entryMilestone_eight_eq]
    exact BB6.A6.entry_to_c8
  exact AffRLE.isNotHalt_of_family BB6.A6.familyCfg hinit BB6.A6.family_step

/-- `ConjectureMachines.Halts` reformulation of `is_not_halt`. -/
theorem not_halts : ¬ ConjectureMachines.Halts machine :=
  (ConjectureMachines.isNotHalt_toBB_iff_not_halts machine).mp is_not_halt

end BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH

end
