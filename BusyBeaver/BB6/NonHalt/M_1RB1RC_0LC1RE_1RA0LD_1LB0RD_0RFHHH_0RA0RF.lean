/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify


/-!
# Busy Beaver Machine `1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RF---_0RA0RF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 5, Stmt.write 0 Dir.right)
  | 4, 1 => none
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => some (some 5, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

/-! ## Elementary Tape Sweeps and Macro Step (`mstep`) -/

private abbrev qA : Fin 6 := 0
private abbrev qC : Fin 6 := 2
private abbrev b0 : Fin 2 := 0
private abbrev b1 : Fin 2 := 1

private def oo : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => b1 :: b1 :: oo n

private def pr : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => b0 :: b1 :: pr n

private def tn : ℕ → List (Fin 2)
  | 0 => []
  | n + 1 => b1 :: b0 :: tn n

private theorem oo_shift (n : ℕ) (s : ListBlank (Fin 2)) :
    oo n +> (b1 >> s) = b1 >> (oo n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [oo, listblank_append_cons, ih]

private theorem pr_tn (n : ℕ) (s : ListBlank (Fin 2)) :
    pr n +> (b0 >> s) = b0 >> (tn n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pr, tn, listblank_append_cons, ih]

private theorem pr_succ_shift (n : ℕ) (s : ListBlank (Fin 2)) :
    pr n +> (b0 >> b1 >> s) = b0 >> b1 >> (pr n +> s) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pr, listblank_append_cons, ih]

private theorem pr_add (a b : ℕ) (s : ListBlank (Fin 2)) :
    pr a +> (pr b +> s) = pr (a + b) +> s := by
  induction a with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    simp only [pr, listblank_append_cons, ih]

local macro "tm_norm" : tactic =>
  `(tactic|
    try simp only [Cfg.headRight, Cfg.headLeft, Tape.move, Tape.write, ListBlank.head_cons,
      ListBlank.tail_cons, zero_cons_default, default_head, default_tail,
      listblank_append_nil, listblank_append_cons])

local macro "tm_finish" : tactic =>
  `(tactic| tm_norm <;> exact ReachesStar.refl target_tm _)

local macro "tm_step" : tactic =>
  `(tactic|
    (first
      | refine ReachesPlus.head
          (by (try simp only [Cfg.headRight, Cfg.headLeft, ListBlank.head_cons, ListBlank.tail_cons,
                zero_cons_default, default_head, default_tail, listblank_append_nil,
                listblank_append_cons]); rfl) ?_
      | refine ReachesStar.head
          (by (try simp only [Cfg.headRight, Cfg.headLeft, ListBlank.head_cons, ListBlank.tail_cons,
                zero_cons_default, default_head, default_tail, listblank_append_nil,
                listblank_append_cons]); rfl) ?_) <;>
    tm_norm)

local macro "tm_exec12" : tactic =>
  `(tactic|
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step) <;>
    (try first | tm_finish | tm_step))

private theorem sweep (m : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target_tm ((oo m +> l) <{{qC}} r) (l <{{qC}} (pr m +> r)) := by
  induction m generalizing l r with
  | zero =>
    dsimp only [oo, pr]
    tm_finish
  | succ m ih =>
    dsimp only [oo, pr]
    tm_step; tm_step; tm_step; tm_step
    refine ReachesStar.trans (ih l (b0 >> b1 >> r)) ?_
    rw [pr_succ_shift]

private theorem aloop (k : ℕ) (l r : ListBlank (Fin 2)) :
    ReachesStar target_tm (l {{qA}}> (tn k +> r)) ((oo k +> l) {{qA}}> r) := by
  induction k generalizing l r with
  | zero =>
    dsimp only [tn, oo]
    tm_finish
  | succ k ih =>
    dsimp only [tn, oo]
    tm_step; tm_step
    refine ReachesStar.trans (ih (b1 >> b1 >> l) r) ?_
    rw [oo_shift, oo_shift]

private theorem ruleA (k : ℕ) (L z : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (L {{qA}}> (pr (k + 2) +> (b0 >> z)))
      ((oo k +> (b0 >> b0 >> b0 >> b1 >> b1 >> L)) {{qA}}> z) := by
  dsimp only [pr]
  tm_step; tm_step; tm_step; tm_step
  rw [pr_tn]
  tm_step
  exact aloop k (b0 >> b0 >> b0 >> b1 >> b1 >> L) z

private theorem ruleB (k : ℕ) (L z : ListBlank (Fin 2)) :
    ReachesStar target_tm
      (L {{qA}}> (b0 >> b1 >> b0 >> (pr k +> (b0 >> z))))
      ((oo k +> (b0 >> b0 >> b1 >> b1 >> L)) {{qA}}> z) := by
  tm_step; tm_step; tm_step
  rw [pr_tn]
  tm_step
  exact aloop k (b0 >> b0 >> b1 >> b1 >> L) z

/-! ## Token Alphabet and Carry Semantics -/

private inductive Tok where
  | tZ (n : ℕ)
  | tO (n : ℕ)
  | tA (n : ℕ)
  | tB (n : ℕ)
  | tC (n : ℕ)
  | tD (n : ℕ)
  deriving DecidableEq

private def el : List Tok → ListBlank (Fin 2)
  | [] => default
  | .tZ n :: r => b0 >> b0 >> b0 >> b1 >> b1 >> (oo n +> el r)
  | .tO n :: r => b0 >> b0 >> b1 >> b1 >> b1 >> (oo n +> el r)
  | .tA n :: r => b0 >> b0 >> b0 >> b1 >> b1 >> b1 >> (oo n +> el r)
  | .tB n :: r => b0 >> b0 >> b1 >> b1 >> (oo n +> el r)
  | .tC n :: r => b0 >> b1 >> b1 >> (oo n +> el r)
  | .tD n :: r => b0 >> b1 >> b1 >> b1 >> (oo n +> el r)

private def enc (w : List Tok) (K : ℕ) : Cfg (Fin 2) (Fin 6) :=
  (oo K +> el w) {{qA}}> default

private def ins (y : Tok) (r : List Tok) : List Tok :=
  match y with
  | .tZ n => .tA 0 :: .tB n :: r
  | .tO n => .tA 0 :: .tD n :: r
  | .tA n => .tA 0 :: .tO n :: r
  | .tB n => .tA 0 :: .tC n :: r
  | .tC n => .tA (n + 1) :: r
  | .tD n => .tZ (n + 2) :: r

private inductive Res where
  | Bnc (l : List Tok)
  | Stp (l : List Tok) (q : ℕ)
  deriving DecidableEq

private def inn : List Tok → Option Res
  | [] => some (.Bnc [.tO 0])
  | .tZ n :: r => some (.Bnc (.tO (n + 1) :: r))
  | .tA n :: r => some (.Bnc (.tB (n + 2) :: r))
  | .tB e :: [] => some (.Stp [.tA 0] e)
  | .tB e :: y :: r => some (.Stp (ins y r) e)
  | .tO c :: r =>
    match inn r with
    | some (.Bnc l) => some (.Stp l (c + 2))
    | some (.Stp l q) => some (.Stp (.tZ q :: l) c)
    | none => none
  | _ => none

private def mstep (w : List Tok) (K : ℕ) : Option (List Tok × ℕ) :=
  match inn w with
  | none => none
  | some (.Bnc l) => some (l, K)
  | some (.Stp l q) =>
    match K with
    | 0 => some (l, q)
    | 1 => some (.tB q :: l, 0)
    | K' + 2 => some (.tZ q :: l, K')

private def Xcfg (m : ℕ) (w : List Tok) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (oo m +> (b1 >> el w)) <{{qC}} r

private theorem cross3 (m : ℕ) (L r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((oo m +> (b1 >> b0 >> b0 >> b0 >> L)) <{{qC}} r)
      ((b1 >> L) {{qA}}> (b0 >> b1 >> b0 >> (pr m +> r))) := by
  refine ReachesStar.trans_plus (sweep m _ r) ?_
  tm_exec12

private theorem cross2 (m : ℕ) (L r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((oo m +> (b1 >> b0 >> b0 >> L)) <{{qC}} r)
      (L <{{qC}} (b0 >> b1 >> b0 >> (pr m +> r))) := by
  refine ReachesStar.trans_plus (sweep m _ r) ?_
  tm_exec12

private theorem stop_even (e : ℕ) (y : Tok) (r : List Tok) (m : ℕ) (rho : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((oo m +> (b1 >> b0 >> b0 >> b1 >> b1 >> (oo e +> el (y :: r)))) <{{qC}} rho)
      ((oo e +> el (ins y r)) {{qA}}> (pr m +> rho)) := by
  refine ReachesPlus.trans_star (cross2 m _ rho) ?_
  have h_oo : (b1 >> b1 >> (oo e +> el (y :: r))) = oo (e + 1) +> el (y :: r) := rfl
  rw [h_oo]
  refine ReachesStar.trans (sweep (e + 1) (el (y :: r)) (b0 >> b1 >> b0 >> (pr m +> rho))) ?_
  dsimp only [pr, listblank_append_cons]
  rw [pr_succ_shift]
  cases y with
  | tZ n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b0 >> b0 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)
  | tO n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b0 >> b1 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)
  | tA n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b0 >> b0 >> b1 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)
  | tB n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b0 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)
  | tC n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)
  | tD n =>
    dsimp only [el, ins, oo, listblank_append_nil, listblank_append_cons]
    tm_step
    simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
      ListBlank.tail_cons] using
      ruleA e (b1 >> b1 >> b1 >> b1 >> (oo n +> el r)) (pr m +> rho)

private theorem cross_blank (m : ℕ) (r : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((oo m +> (b1 >> default)) <{{qC}} r)
      ((b1 >> default) {{qA}}> (b0 >> b1 >> b0 >> (pr m +> r))) := by
  have h := cross3 m default r
  simpa only [zero_cons_default] using h

private theorem stop_blank (e m : ℕ) (rho : ListBlank (Fin 2)) :
    ReachesPlus target_tm
      ((oo m +> (b1 >> b0 >> b0 >> b1 >> b1 >> (oo e +> default))) <{{qC}} rho)
      ((oo e +> (b0 >> b0 >> b0 >> b1 >> b1 >> b1 >> default)) {{qA}}> (pr m +> rho)) := by
  refine ReachesPlus.trans_star (cross2 m _ rho) ?_
  have h_oo : (b1 >> b1 >> (oo e +> default)) = oo (e + 1) +> default := rfl
  rw [h_oo]
  refine ReachesStar.trans (sweep (e + 1) default (b0 >> b1 >> b0 >> (pr m +> rho))) ?_
  dsimp only [pr, listblank_append_cons]
  rw [pr_succ_shift]
  tm_step
  simpa only [Cfg.headRight, pr, listblank_append_cons, ListBlank.head_cons,
    ListBlank.tail_cons] using ruleA e (b1 >> default) (pr m +> rho)

private theorem inn_ok (w : List Tok) :
    (∀ l, inn w = some (.Bnc l) → ∀ m k z,
      ReachesPlus target_tm (Xcfg m w (pr k +> (b0 >> z))) ((oo (m + k) +> el l) {{qA}}> z)) ∧
    (∀ l q, inn w = some (.Stp l q) → ∀ m r,
      ReachesPlus target_tm (Xcfg m w r) ((oo q +> el l) {{qA}}> (pr m +> r))) := by
  induction w with
  | nil =>
    refine ⟨?_, fun _ _ h => nomatch h⟩
    intro l h m k z
    rcases h with ⟨rfl⟩
    unfold Xcfg
    dsimp only [el, oo, listblank_append_nil]
    refine ReachesPlus.trans_star (cross_blank m (pr k +> (b0 >> z))) ?_
    rw [pr_add]
    exact ruleB (m + k) (b1 >> default) z
  | cons t w ih =>
    obtain ⟨ihB, ihS⟩ := ih
    cases t with
    | tZ n =>
      refine ⟨?_, fun _ _ h => nomatch h⟩
      intro l h m k z
      dsimp only [inn] at h
      rcases h with ⟨rfl⟩
      unfold Xcfg
      dsimp only [el]
      refine ReachesPlus.trans_star (cross3 m _ (pr k +> (b0 >> z))) ?_
      rw [pr_add]
      simpa only [el, oo, listblank_append_cons] using
        ruleB (m + k) (b1 >> b1 >> b1 >> (oo n +> el w)) z
    | tO c =>
      refine ⟨?_, ?_⟩
      · intro l h
        dsimp only [inn] at h
        rcases hw : inn w with _ | ⟨_ | _⟩ <;> rw [hw] at h <;> nomatch h
      · intro l q h m r
        dsimp only [inn] at h
        unfold Xcfg
        dsimp only [el]
        refine ReachesPlus.trans (cross2 m _ r) ?_
        have hE : (b1 >> b1 >> b1 >> (oo c +> el w)) = oo (c + 1) +> (b1 >> el w) := by
          dsimp only [oo, listblank_append_cons]
          rw [oo_shift]
        rw [hE]
        rcases hw : inn w with _ | ⟨l1 | ⟨l1, q1⟩⟩ <;> rw [hw] at h
        · nomatch h
        · dsimp only at h
          injection h with h'
          injection h' with hl hq
          subst hl hq
          have h1 := ihB l1 hw (c + 1) 1 (pr m +> r)
          unfold Xcfg at h1
          dsimp only [pr, listblank_append_cons, listblank_append_nil] at h1
          exact h1
        · dsimp only at h
          injection h with h'
          injection h' with hl hq
          subst hl hq
          refine ReachesPlus.trans_star (ihS l1 q1 hw (c + 1) (b0 >> b1 >> b0 >> (pr m +> r))) ?_
          dsimp only [pr, listblank_append_cons]
          rw [pr_succ_shift]
          have h_pr :
              (b0 >> b1 >> b0 >> b1 >> (pr c +> (b0 >> (pr m +> r)))) =
              pr (c + 2) +> (b0 >> (pr m +> r)) := rfl
          rw [h_pr]
          simpa only [el] using ruleA c (oo q1 +> el l1) (pr m +> r)
    | tA n =>
      refine ⟨?_, fun _ _ h => nomatch h⟩
      intro l h m k z
      dsimp only [inn] at h
      rcases h with ⟨rfl⟩
      unfold Xcfg
      dsimp only [el]
      refine ReachesPlus.trans_star (cross3 m _ (pr k +> (b0 >> z))) ?_
      rw [pr_add]
      simpa only [el, oo, listblank_append_cons] using
        ruleB (m + k) (b1 >> b1 >> b1 >> b1 >> (oo n +> el w)) z
    | tB e =>
      refine ⟨?_, ?_⟩
      · intro l h
        rcases w with _ | ⟨y, w'⟩ <;> nomatch h
      · intro l q h m r
        unfold Xcfg
        dsimp only [el]
        rcases w with _ | ⟨y, w'⟩
        · dsimp only [inn] at h
          injection h with h'
          injection h' with hl hq
          subst hl hq
          simpa only [el, oo, listblank_append_nil] using stop_blank e m r
        · dsimp only [inn] at h
          injection h with h'
          injection h' with hl hq
          subst hl hq
          exact stop_even e y w' m r
    | tC _ =>
      refine ⟨?_, ?_⟩
      · intro _ h; nomatch h
      · intro _ _ h; nomatch h
    | tD _ =>
      refine ⟨?_, ?_⟩
      · intro _ h; nomatch h
      · intro _ _ h; nomatch h

private theorem enc_Xcfg (w : List Tok) (K : ℕ) :
    ReachesPlus target_tm (enc w K) (Xcfg K w default) := by
  unfold enc Xcfg
  tm_step
  have h_sh : (b1 >> (oo K +> el w)) = oo K +> (b1 >> el w) := (oo_shift K (el w)).symm
  change ReachesStar target_tm ((b1 >> (oo K +> el w)) {{1}}> default) _
  rw [h_sh]
  tm_step
  tm_finish

private theorem step_ok (w : List Tok) (K : ℕ) (w' : List Tok) (K' : ℕ)
    (h : mstep w K = some (w', K')) :
    ReachesPlus target_tm (enc w K) (enc w' K') := by
  unfold mstep at h
  obtain ⟨hB, hS⟩ := inn_ok w
  refine ReachesPlus.trans (enc_Xcfg w K) ?_
  rcases hw : inn w with _ | ⟨l | ⟨l, q⟩⟩ <;> rw [hw] at h
  · nomatch h
  · dsimp only at h
    injection h with h'
    injection h' with hw' hK'
    subst hw' hK'
    have h1 := hB l hw K 0 default
    rw [Nat.add_zero] at h1
    simpa only [pr, listblank_append_nil, zero_cons_default, enc] using h1
  · dsimp only at h
    refine ReachesPlus.trans_star (hS l q hw K default) ?_
    rcases K with _ | _ | K2 <;>
      (injection h with h'; injection h' with hw' hK'; subst hw' hK')
    · dsimp only [pr, listblank_append_nil]
      exact ReachesStar.refl target_tm _
    · unfold enc
      dsimp only [pr, oo, el, listblank_append_cons, listblank_append_nil]
      tm_exec12
    · have hA := ruleA K2 (oo q +> el l) default
      simpa only [zero_cons_default, enc, el] using hA

/-! ## Token Invariant (`Good`, `V`, `psi`, `Inv`) -/

private def arr (w : List Tok) : Option (List Tok) :=
  match inn w with
  | none => none
  | some (.Bnc l) => some l
  | some (.Stp l q) => some (.tZ q :: l)

private def gapl : List Tok → ℕ
  | .tZ _ :: r => gapl r + 1
  | .tO _ :: r => gapl r + 1
  | _ => 0

private def Good (K n : ℕ) : List Tok → Prop
  | [] => True
  | .tZ _ :: r => Good K (n + 1) r
  | .tO _ :: r => Good K (n + 1) r
  | .tC _ :: _ => False
  | .tD _ :: _ => False
  | _ :: [] => False
  | _ :: .tA _ :: _ => False
  | _ :: .tB _ :: r => K ≤ n + 3 * gapl r ∧ Good K (n + 2) r
  | _ :: .tC _ :: r => K + 1 ≤ n + 3 * gapl r ∧ Good K (n + 2) r
  | _ :: .tD _ :: r => Good K (n + 2) r
  | _ :: .tZ _ :: r => K + 2 ≤ n + 3 * (gapl r + 1) ∧ Good K (n + 2) r
  | _ :: .tO _ :: r => K + 2 ≤ n + 3 * (gapl r + 1) ∧ Good K (n + 2) r

private def dg : Tok → ℕ
  | .tZ _ => 0
  | .tO _ => 2
  | .tA _ => 1
  | .tB _ => 1
  | .tC _ => 0
  | .tD _ => 0

private def V : List Tok → ℕ
  | [] => 0
  | t :: r => dg t + 2 * V r

private def psi : List Tok → ℕ
  | .tZ _ :: r => 2 * psi r
  | .tO _ :: r => 1 + 2 * psi r
  | .tA _ :: _ => 2
  | _ => 3

private theorem Good_mono :
    ∀ (T : List Tok) (K n K' n' : ℕ), Good K n T → K' + n ≤ K + n' → Good K' n' T
  | [], _, _, _, _, _, _ => trivial
  | .tZ _ :: r, K, n, K', n', hG, hle => Good_mono r K (n + 1) K' (n' + 1) hG (by omega)
  | .tO _ :: r, K, n, K', n', hG, hle => Good_mono r K (n + 1) K' (n' + 1) hG (by omega)
  | .tC _ :: _, _, _, _, _, hG, _ => hG
  | .tD _ :: _, _, _, _, _, hG, _ => hG
  | .tA _ :: [], _, _, _, _, hG, _ => hG
  | .tB _ :: [], _, _, _, _, hG, _ => hG
  | .tA _ :: .tA _ :: _, _, _, _, _, hG, _ => hG
  | .tB _ :: .tA _ :: _, _, _, _, _, hG, _ => hG
  | .tA _ :: .tB _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tB _ :: .tB _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tA _ :: .tC _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tB _ :: .tC _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tA _ :: .tD _ :: r, K, n, K', n', hG, hle =>
    Good_mono r K (n + 2) K' (n' + 2) hG (by omega)
  | .tB _ :: .tD _ :: r, K, n, K', n', hG, hle =>
    Good_mono r K (n + 2) K' (n' + 2) hG (by omega)
  | .tA _ :: .tZ _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tB _ :: .tZ _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tA _ :: .tO _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩
  | .tB _ :: .tO _ :: r, K, n, K', n', ⟨h1, h2⟩, hle =>
    ⟨by omega, Good_mono r K (n + 2) K' (n' + 2) h2 (by omega)⟩

private theorem psi_pos (T : List Tok) : 1 ≤ psi T := by
  induction T with
  | nil => decide
  | cons t r ih =>
    cases t <;> dsimp [psi] <;> omega

private theorem psi_lt (T : List Tok) : psi T + 1 ≤ 4 * 2 ^ gapl T := by
  induction T with
  | nil => decide
  | cons t r ih =>
    cases t <;> dsimp [psi, gapl] <;> (try rw [Nat.pow_succ]) <;> omega

private def low : List Tok → ℕ
  | .tZ _ :: _ => 0
  | .tO _ :: _ => 1
  | _ => 2

private def Stepd (K n : ℕ) (T T1 P1 : List Tok) : Prop :=
  psi T + 1 ≤ psi T1 ∧ Good K n T1 ∧
    ((P1 = [] ∧ ∃ d, T1.length = T.length + d ∧ V T1 ≤ (V T + 2) * 2 ^ d) ∨
     (V T1 = 0 ∧ K + 2 ≤ n + T1.length))

private theorem arr_tO (c : ℕ) (w l : List Tok) (h : arr w = some l) :
    ∃ c', arr (.tO c :: w) = some (.tZ c' :: l) := by
  unfold arr at *
  dsimp only [inn]
  rcases hw : inn w with _ | ⟨l1 | ⟨l1, q1⟩⟩ <;> rw [hw] at h
  · nomatch h
  · rcases h with ⟨rfl⟩; exact ⟨c + 2, rfl⟩
  · rcases h with ⟨rfl⟩; exact ⟨c, rfl⟩

private theorem arrive (T P : List Tok) (K n : ℕ)
    (hG : Good K n T) (hV : V T + 2 < 2 ^ (T.length + 1)) :
    ∃ T1 P1, arr (T ++ P) = some (T1 ++ (P1 ++ P)) ∧ Stepd K n T T1 P1 ∧
      (low T = 0 → low T1 = 1) ∧ (low T = 1 → low T1 = 0) := by
  induction T generalizing K n with
  | nil =>
    dsimp [V] at hV
    omega
  | cons t T' ih =>
    cases t with
    | tZ x =>
      refine ⟨.tO (x + 1) :: T', [], rfl, ?_, fun _ => rfl, fun h => nomatch h⟩
      refine ⟨by dsimp [psi]; omega, hG, Or.inl ⟨rfl, 0, by simp, ?_⟩⟩
      dsimp [V, dg]
      omega
    | tO x =>
      dsimp only [Good] at hG
      have hV' : V T' + 2 < 2 ^ (T'.length + 1) := by
        dsimp only [List.length_cons, V, dg] at hV
        rw [Nat.pow_succ] at hV
        omega
      obtain ⟨T1, P1, ha, ⟨hp, hg, hr⟩, _⟩ := ih K (n + 1) hG hV'
      obtain ⟨c', hc⟩ := arr_tO x (T' ++ P) (T1 ++ (P1 ++ P)) ha
      refine ⟨.tZ c' :: T1, P1, hc, ?_, by dsimp [low]; exact ⟨by omega, by omega⟩⟩
      refine ⟨by dsimp [psi]; omega, hg, ?_⟩
      rcases hr with ⟨hP1, d, hl, hv⟩ | ⟨hv, hk⟩
      · refine Or.inl ⟨hP1, d, by dsimp; omega, ?_⟩
        dsimp only [V, dg]
        nlinarith
      · refine Or.inr ⟨by dsimp [V, dg]; omega, by dsimp; omega⟩
    | tA x =>
      rcases T' with _ | ⟨y, T2⟩
      · exact False.elim hG
      refine ⟨.tB (x + 2) :: y :: T2, [], rfl, ?_, by dsimp [low]; exact ⟨by omega, by omega⟩⟩
      refine ⟨by dsimp [psi]; omega, ?_, Or.inl ⟨rfl, 0, rfl, by dsimp [V, dg]; omega⟩⟩
      cases y <;> exact hG
    | tB x =>
      rcases T' with _ | ⟨y, T2⟩
      · exact False.elim hG
      cases y with
      | tZ z =>
        obtain ⟨h1, h2⟩ := hG
        refine ⟨.tZ x :: .tA 0 :: .tB z :: T2, [], rfl, ?_,
          by dsimp [low]; exact ⟨by omega, by omega⟩⟩
        refine ⟨by dsimp [psi]; omega, ⟨by omega,
          Good_mono T2 K (n + 2) K (n + 3) h2 (by omega)⟩,
          Or.inl ⟨rfl, 1, rfl, by dsimp [V, dg]; omega⟩⟩
      | tO z =>
        obtain ⟨h1, h2⟩ := hG
        refine ⟨.tZ x :: .tA 0 :: .tD z :: T2, [], rfl, ?_,
          by dsimp [low]; exact ⟨by omega, by omega⟩⟩
        refine ⟨by dsimp [psi]; omega, Good_mono T2 K (n + 2) K (n + 3) h2 (by omega),
          Or.inl ⟨rfl, 1, rfl, by dsimp [V, dg]; omega⟩⟩
      | tA _ => exact False.elim hG
      | tB z =>
        obtain ⟨h1, h2⟩ := hG
        refine ⟨.tZ x :: .tA 0 :: .tC z :: T2, [], rfl, ?_,
          by dsimp [low]; exact ⟨by omega, by omega⟩⟩
        refine ⟨by dsimp [psi]; omega, ⟨by omega,
          Good_mono T2 K (n + 2) K (n + 3) h2 (by omega)⟩,
          Or.inl ⟨rfl, 1, rfl, by dsimp [V, dg]; omega⟩⟩
      | tC z =>
        obtain ⟨h1, h2⟩ := hG
        have h_short (h0 : gapl T2 = 0) :
            ∃ T1 P1, arr ((.tB x :: .tC z :: T2) ++ P) = some (T1 ++ (P1 ++ P)) ∧
              Stepd K n (.tB x :: .tC z :: T2) T1 P1 ∧
              (low (.tB x :: .tC z :: T2) = 0 → low T1 = 1) ∧
              (low (.tB x :: .tC z :: T2) = 1 → low T1 = 0) := by
          refine ⟨[.tZ x], .tA (z + 1) :: T2, rfl, ?_,
            by dsimp [low]; exact ⟨by omega, by omega⟩⟩
          refine ⟨by dsimp [psi]; omega, trivial, Or.inr ⟨rfl, ?_⟩⟩
          rw [h0] at h1
          dsimp
          omega
        rcases T2 with _ | ⟨u, T3⟩
        · exact h_short rfl
        cases u with
        | tZ u =>
          refine ⟨.tZ x :: .tA (z + 1) :: .tZ u :: T3, [], rfl, ?_,
            by dsimp [low]; exact ⟨by omega, by omega⟩⟩
          refine ⟨by dsimp [psi]; omega, ⟨by dsimp [gapl] at h1 ⊢; omega, h2⟩,
            Or.inl ⟨rfl, 0, rfl, by dsimp [V, dg]; omega⟩⟩
        | tO u =>
          refine ⟨.tZ x :: .tA (z + 1) :: .tO u :: T3, [], rfl, ?_,
            by dsimp [low]; exact ⟨by omega, by omega⟩⟩
          refine ⟨by dsimp [psi]; omega, ⟨by dsimp [gapl] at h1 ⊢; omega, h2⟩,
            Or.inl ⟨rfl, 0, rfl, by dsimp [V, dg]; omega⟩⟩
        | tA _ => exact h_short rfl
        | tB _ => exact h_short rfl
        | tC _ => exact h_short rfl
        | tD _ => exact h_short rfl
      | tD z =>
        have hP := psi_pos T2
        refine ⟨.tZ x :: .tZ (z + 2) :: T2, [], rfl, ?_,
          by dsimp [low]; exact ⟨by omega, by omega⟩⟩
        refine ⟨by dsimp [psi]; omega, hG,
          Or.inl ⟨rfl, 0, rfl, by dsimp [V, dg]; omega⟩⟩
    | tC _ => exact False.elim hG
    | tD _ => exact False.elim hG

/-! ## Super-Era Recurrence and Invariant Closure -/

private def N (j : ℕ) : ℕ :=
  if j % 2 = 0 then 3 * j else 6 * j + 2

private def nj (j : ℕ) : ℕ :=
  if j % 2 = 0 then 3 * (j / 2) + 1 else 3 * (j / 2) + 3

private theorem ev_or (j : ℕ) :
    (∃ i, j = 2 * i ∧ N j = 6 * i ∧ nj j = 3 * i + 1) ∨
    (∃ i, j = 2 * i + 1 ∧ N j = 12 * i + 8 ∧ nj j = 3 * i + 3) := by
  by_cases hj : j % 2 = 0
  · exact Or.inl ⟨j / 2, by omega, by unfold N; simp [hj]; omega, by unfold nj; simp [hj]⟩
  · exact Or.inr ⟨j / 2, by omega, by unfold N; simp [hj]; omega, by unfold nj; simp [hj]⟩

private theorem N_mod2 (j : ℕ) : N j % 2 = 0 := by
  unfold N; split_ifs <;> omega

private def Inv (j M : ℕ) (w : List Tok) : Prop :=
  ∃ T P K, w = T ++ P ∧ Good K 0 T ∧
    V T + 2 * M + 48 * j ≤ 2 ^ (T.length + 1) ∧
    N j ≤ psi T + M ∧ M ≤ N j ∧ 8 * j ≤ 2 ^ K ∧
    low T = M % 2

private theorem inv_arr (j M : ℕ) (w : List Tok) (hj : 1 ≤ j) (hInv : Inv j (M + 1) w) :
    ∃ w', arr w = some w' ∧ Inv j M w' := by
  obtain ⟨T, P, K, rfl, hG, hF, hpsi, hM, hK, hlow⟩ := hInv
  obtain ⟨T1, P1, ha, ⟨hp, hg, hr⟩, h0, h1⟩ := arrive T P K 0 hG (by omega)
  refine ⟨T1 ++ (P1 ++ P), ha, ?_⟩
  have hlow1 : low T1 = M % 2 := by
    by_cases hMe : M % 2 = 0
    · have : (M + 1) % 2 = 1 := by omega
      rw [this] at hlow
      rw [h1 hlow, hMe]
    · have hMo : M % 2 = 1 := by omega
      have : (M + 1) % 2 = 0 := by omega
      rw [this] at hlow
      rw [h0 hlow, hMo]
  have hN : N j ≤ 6 * j + 2 := by
    unfold N; split_ifs <;> omega
  rcases hr with ⟨rfl, d, hl, hv⟩ | ⟨hv, hk⟩
  · refine ⟨T1, P, K, rfl, hg, ?_, by omega, by omega, hK, hlow1⟩
    have hlen : T1.length + 1 = (T.length + 1) + d := by omega
    rw [hlen, Nat.pow_add]
    have hd : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hE : (V T + 2 * (M + 1) + 48 * j) * 2 ^ d ≤ 2 ^ (T.length + 1) * 2 ^ d :=
      Nat.mul_le_mul_right (2 ^ d) hF
    nlinarith
  · refine ⟨T1, P1 ++ P, K, rfl, hg, ?_, by omega, by omega, hK, hlow1⟩
    rw [hv]
    have hpow : 2 ^ (K + 3) ≤ 2 ^ (T1.length + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [Nat.pow_add] at hpow
    change 2 ^ K * 8 ≤ 2 ^ (T1.length + 1) at hpow
    omega

private theorem inv_low (j M : ℕ) (w : List Tok) (h : Inv j M w) :
    low w = M % 2 := by
  obtain ⟨T, P, K, rfl, _, _, _, _, _, hlow⟩ := h
  rcases T with _ | ⟨t, T'⟩
  · dsimp [low] at hlow; omega
  · cases t
    · exact hlow
    · exact hlow
    · dsimp [low] at hlow; omega
    · dsimp [low] at hlow; omega
    · dsimp [low] at hlow; omega
    · dsimp [low] at hlow; omega

private theorem inv_payload (j M x x' : ℕ) (r : List Tok) (h : Inv j M (.tO x :: r)) :
    Inv j M (.tO x' :: r) := by
  obtain ⟨T, P, K, hE, hG, hF, hpsi, hM, hK, hlow⟩ := h
  rcases T with _ | ⟨t, T'⟩
  · dsimp [low] at hlow; omega
  · cases t <;> try cases hE
    exact ⟨.tO x' :: T', P, K, rfl, hG, hF, hpsi, hM, hK, hlow⟩

private def nl : Res → List Tok
  | .Bnc l => l
  | .Stp l q => .tZ q :: l

private def dc : Res → ℕ
  | .Bnc _ => 3
  | .Stp _ _ => 1

private theorem inv_last (j M : ℕ) (w : List Tok) (hj : 1 ≤ j)
    (h : Inv j (M + 1) w) (ho : (M + 1) % 2 = 1) :
    ∃ l q, inn w = some (.Stp l q) ∧ Inv j M (.tZ q :: l) := by
  have hl := inv_low j (M + 1) w h
  rw [ho] at hl
  obtain ⟨w1, ha, hi⟩ := inv_arr j M w hj h
  rcases w with _ | ⟨t, w0⟩
  · cases hl
  cases t <;> try cases hl
  rename_i x
  unfold arr at ha
  dsimp only [inn] at ha ⊢
  rcases hw0 : inn w0 with _ | ⟨l | ⟨l, q⟩⟩ <;> rw [hw0] at ha
  · nomatch ha
  · rcases ha with ⟨rfl⟩; exact ⟨l, x + 2, rfl, hi⟩
  · rcases ha with ⟨rfl⟩; exact ⟨.tZ q :: l, x, rfl, hi⟩

private theorem inv_first (j M : ℕ) (w : List Tok) (hj : 1 ≤ j)
    (h : Inv j (M + 1) w) (he : (M + 1) % 2 = 0) :
    ∃ x w0, w = .tZ x :: w0 ∧ Inv j M (.tO (x + 1) :: w0) := by
  have hl := inv_low j (M + 1) w h
  rw [he] at hl
  obtain ⟨w1, ha, hi⟩ := inv_arr j M w hj h
  rcases w with _ | ⟨t, w0⟩
  · cases hl
  cases t <;> try cases hl
  rename_i x
  rcases ha with ⟨rfl⟩
  exact ⟨x, w0, rfl, hi⟩

private theorem inv_two (j M : ℕ) (w : List Tok) (hj : 1 ≤ j) (h : Inv j (M + 2) w) :
    ∃ r1 r2, inn w = some r1 ∧ inn (nl r1) = some r2 ∧ dc r1 + dc r2 = 4 ∧ Inv j M (nl r2) := by
  by_cases he : (M + 2) % 2 = 0
  · obtain ⟨x, w0, rfl, hi⟩ := inv_first j (M + 1) w hj h he
    obtain ⟨l, q, el1, hi2⟩ := inv_last j M (.tO (x + 1) :: w0) hj hi (by omega)
    exact ⟨.Bnc (.tO (x + 1) :: w0), .Stp l q, rfl, el1, rfl, hi2⟩
  · obtain ⟨l, q, el1, hi⟩ := inv_last j (M + 1) w hj h (by omega)
    obtain ⟨x, w0, hEq, hi2⟩ := inv_first j M (.tZ q :: l) hj hi (by omega)
    injection hEq with h1 h2
    injection h1 with hqx
    subst hqx h2
    exact ⟨.Stp l q, .Bnc (.tO (q + 1) :: l), el1, rfl, rfl, hi2⟩

private theorem pow_three_mul_succ (k : ℕ) :
    2 ^ (3 * k + 1) = 2 * (2 ^ k * (2 ^ k * 2 ^ k)) := by
  have hk : 3 * k + 1 = k + (k + k) + 1 := by omega
  rw [hk, Nat.pow_succ, Nat.pow_add, Nat.pow_add]
  omega

private theorem inv_S (j x : ℕ) (w0 : List Tok) (hj : 46 ≤ j) (h : Inv j 0 (.tZ x :: w0)) :
    ∃ y r, w0 = y :: r ∧ Inv (nj j) (N (nj j)) (.tZ (x + 3) :: ins y r) := by
  obtain ⟨T, P, K, hE, hG, hF, hpsi, _, hK, hlow⟩ := h
  rcases T with _ | ⟨t, T'⟩
  · dsimp [low] at hlow; omega
  cases t <;> try cases hE
  have hN3 : 3 * j ≤ N j := by unfold N; split_ifs <;> omega
  have hnx : 2 * nj j ≤ 3 * j + 3 := by unfold nj; split_ifs <;> omega
  have hN2 : N (nj j) ≤ 6 * nj j + 2 := by unfold N; split_ifs <;> omega
  have hlt : 3 * j + 1 ≤ 4 * 2 ^ gapl (.tZ x :: T') := by
    have := psi_lt (.tZ x :: T')
    omega
  rcases T' with _ | ⟨u, T2⟩
  · dsimp [gapl] at hlt; omega
  cases u with
  | tZ z =>
    refine ⟨.tZ z, T2 ++ P, rfl, ?_⟩
    dsimp only [gapl] at hlt
    rw [Nat.pow_succ, Nat.pow_succ] at hlt
    set k2 := gapl T2
    set K' := min (K + 1) (3 * k2 + 1)
    have hK' : 8 * nj j ≤ 2 ^ K' := by
      dsimp only [K']
      rcases le_total (K + 1) (3 * k2 + 1) with hle | hle
      · rw [Nat.min_eq_left hle, Nat.pow_succ]
        omega
      · rw [Nat.min_eq_right hle, pow_three_mul_succ]
        set Y := 2 ^ k2
        have hY : 9 ≤ Y := by omega
        nlinarith
    refine ⟨.tZ (x + 3) :: .tA 0 :: .tB z :: T2, P, K', rfl, ?_, ?_, ?_, le_rfl, hK', ?_⟩
    · refine ⟨by dsimp [Good]; omega,
        Good_mono T2 K 2 K' 3 hG (by omega)⟩
    · simp only [List.length_cons, V, dg, Nat.pow_succ] at hF ⊢
      omega
    · dsimp only [psi]
      have := psi_pos T2
      omega
    · rw [N_mod2]; rfl
  | tO z =>
    refine ⟨.tO z, T2 ++ P, rfl, ?_⟩
    refine ⟨.tZ (x + 3) :: .tA 0 :: .tD z :: T2, P, K + 1, rfl, ?_, ?_, ?_, le_rfl, ?_, ?_⟩
    · exact Good_mono T2 K 2 (K + 1) 3 hG (by omega)
    · simp only [List.length_cons, V, dg, Nat.pow_succ] at hF ⊢
      omega
    · dsimp only [psi]
      have := psi_pos T2
      omega
    · rw [Nat.pow_succ]; omega
    · rw [N_mod2]; rfl
  | tA _ => dsimp [gapl] at hlt; omega
  | tB _ => dsimp [gapl] at hlt; omega
  | tC _ => dsimp [gapl] at hlt; omega
  | tD _ => dsimp [gapl] at hlt; omega

/-! ## Macro-Step Groups and Super-Era Progress (`super_step`) -/

private theorem tick4 (b a : ℕ) (w : List Tok) (K : ℕ) (r : Res) (h : inn w = some r) :
    ReachesPlus target_tm
      (enc (.tZ b :: .tZ a :: w) (K + 4))
      (enc (.tZ (b + 4) :: .tZ (a + dc r) :: nl r) K) := by
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  apply step_ok
  unfold mstep
  dsimp only [inn]
  rw [h]
  cases r <;> rfl

private theorem tick2O (c : ℕ) (w : List Tok) (K : ℕ) (r : Res) (h : inn w = some r) :
    ReachesPlus target_tm (enc (.tO c :: w) (K + 2)) (enc (.tO (c + dc r) :: nl r) K) := by
  cases r with
  | Bnc l =>
    have h1 : mstep (.tO c :: w) (K + 2) = some (.tZ (c + 2) :: l, K) := by
      unfold mstep; dsimp only [inn]; rw [h]
    exact ReachesPlus.trans (step_ok _ _ _ _ h1) (step_ok _ _ _ _ rfl)
  | Stp l q =>
    have h1 : mstep (.tO c :: w) (K + 2) = some (.tZ c :: .tZ q :: l, K) := by
      unfold mstep; dsimp only [inn]; rw [h]
    exact ReachesPlus.trans (step_ok _ _ _ _ h1) (step_ok _ _ _ _ rfl)

private theorem tick2Z (c : ℕ) (w : List Tok) (K : ℕ) (r : Res) (h : inn w = some r) :
    ReachesPlus target_tm (enc (.tZ c :: w) (K + 2)) (enc (.tZ (c + dc r) :: nl r) K) := by
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  apply step_ok
  unfold mstep
  dsimp only [inn]
  rw [h]
  cases r <;> rfl

private theorem era1end (b a : ℕ) (w : List Tok) :
    ReachesPlus target_tm (enc (.tZ b :: .tZ a :: w) 0) (enc (.tO (a + 1) :: w) (b + 3)) :=
  ReachesPlus.trans (step_ok _ _ _ _ rfl) (step_ok _ _ _ _ rfl)

private theorem stage1 (B : ℕ) (y : Tok) (r : List Tok) (K : ℕ) :
    ReachesPlus target_tm
      (enc (.tA 0 :: .tB B :: y :: r) (K + 14))
      (enc (.tZ 14 :: .tZ 6 :: .tZ (B + 3) :: ins y r) K) := by
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  exact step_ok _ _ _ _ rfl

private theorem end2O (c : ℕ) (w l : List Tok) (q : ℕ) (h : inn w = some (.Stp l q)) :
    ReachesPlus target_tm (enc (.tO c :: w) 1) (enc (.tA 0 :: .tB q :: l) c) := by
  have h1 : mstep (.tO c :: w) 1 = some (.tB c :: .tZ q :: l, 0) := by
    unfold mstep; dsimp only [inn]; rw [h]
  exact ReachesPlus.trans (step_ok _ _ _ _ h1) (step_ok _ _ _ _ rfl)

private theorem end2Z (c x : ℕ) (w0 : List Tok) :
    ReachesPlus target_tm
      (enc (.tO c :: .tZ x :: w0) 1)
      (enc (.tA 0 :: .tD (x + 1) :: w0) (c + 2)) :=
  ReachesPlus.trans (step_ok _ _ _ _ rfl) (step_ok _ _ _ _ rfl)

private theorem era3start (x : ℕ) (w0 : List Tok) (K : ℕ) :
    ReachesPlus target_tm
      (enc (.tA 0 :: .tD x :: w0) (K + 4))
      (enc (.tZ 5 :: .tO (x + 3) :: w0) K) := by
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  exact step_ok _ _ _ _ rfl

private theorem end3 (c : ℕ) (w l : List Tok) (q : ℕ) (h : inn w = some (.Stp l q)) :
    ReachesPlus target_tm (enc (.tZ c :: w) 1) (enc (.tA 0 :: .tB q :: l) (c + 1)) := by
  refine ReachesPlus.trans (step_ok _ _ _ _ rfl) ?_
  have h1 : mstep (.tO (c + 1) :: w) 1 = some (.tB (c + 1) :: .tZ q :: l, 0) := by
    unfold mstep; dsimp only [inn]; rw [h]
  exact ReachesPlus.trans (step_ok _ _ _ _ h1) (step_ok _ _ _ _ rfl)

private theorem era1 (p j M : ℕ) (w : List Tok) (a b K : ℕ)
    (hj : 1 ≤ j) (h : Inv j (2 * p + M) w) :
    ∃ w', ReachesStar target_tm
      (enc (.tZ b :: .tZ a :: w) (8 * p + K))
      (enc (.tZ (8 * p + b) :: .tZ (4 * p + a) :: w') K) ∧ Inv j M w' := by
  induction p generalizing w a b K with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add] at h ⊢
    exact ⟨w, ReachesStar.refl target_tm _, h⟩
  | succ p ih =>
    have h2 : 2 * (p + 1) + M = (2 * p + M) + 2 := by omega
    rw [h2] at h
    obtain ⟨r1, r2, e1, e2, e3, hi⟩ := inv_two j (2 * p + M) w hj h
    obtain ⟨w', hrun, hw'⟩ := ih (nl r2) ((a + dc r1) + dc r2) (b + 8) K hi
    refine ⟨w', ?_, hw'⟩
    have hK : 8 * (p + 1) + K = ((8 * p + K) + 4) + 4 := by omega
    rw [hK]
    have hstep := ReachesPlus.trans (tick4 b a w ((8 * p + K) + 4) r1 e1)
      (tick4 (b + 4) (a + dc r1) (nl r1) (8 * p + K) r2 e2)
    have hb : 8 * p + (b + 8) = 8 * (p + 1) + b := by omega
    have ha : 4 * p + ((a + dc r1) + dc r2) = 4 * (p + 1) + a := by omega
    have hb0 : (b + 4) + 4 = b + 8 := by omega
    rw [hb, ha] at hrun
    rw [hb0] at hstep
    exact ReachesStar.trans hstep.to_star hrun

private theorem era2 (p j M : ℕ) (w : List Tok) (c K : ℕ)
    (hj : 1 ≤ j) (h : Inv j (2 * p + M) w) :
    ∃ w', ReachesStar target_tm
      (enc (.tO c :: w) (4 * p + K))
      (enc (.tO (4 * p + c) :: w') K) ∧ Inv j M w' := by
  induction p generalizing w c K with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add] at h ⊢
    exact ⟨w, ReachesStar.refl target_tm _, h⟩
  | succ p ih =>
    have h2 : 2 * (p + 1) + M = (2 * p + M) + 2 := by omega
    rw [h2] at h
    obtain ⟨r1, r2, e1, e2, e3, hi⟩ := inv_two j (2 * p + M) w hj h
    obtain ⟨w', hrun, hw'⟩ := ih (nl r2) ((c + dc r1) + dc r2) K hi
    refine ⟨w', ?_, hw'⟩
    have hK : 4 * (p + 1) + K = ((4 * p + K) + 2) + 2 := by omega
    rw [hK]
    have hstep := ReachesPlus.trans (tick2O c w ((4 * p + K) + 2) r1 e1)
      (tick2O (c + dc r1) (nl r1) (4 * p + K) r2 e2)
    have hc : 4 * p + ((c + dc r1) + dc r2) = 4 * (p + 1) + c := by omega
    rw [hc] at hrun
    exact ReachesStar.trans hstep.to_star hrun

private theorem era3 (p j M : ℕ) (w : List Tok) (c K : ℕ)
    (hj : 1 ≤ j) (h : Inv j (2 * p + M) w) :
    ∃ w', ReachesStar target_tm
      (enc (.tZ c :: w) (4 * p + K))
      (enc (.tZ (4 * p + c) :: w') K) ∧ Inv j M w' := by
  induction p generalizing w c K with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add] at h ⊢
    exact ⟨w, ReachesStar.refl target_tm _, h⟩
  | succ p ih =>
    have h2 : 2 * (p + 1) + M = (2 * p + M) + 2 := by omega
    rw [h2] at h
    obtain ⟨r1, r2, e1, e2, e3, hi⟩ := inv_two j (2 * p + M) w hj h
    obtain ⟨w', hrun, hw'⟩ := ih (nl r2) ((c + dc r1) + dc r2) K hi
    refine ⟨w', ?_, hw'⟩
    have hK : 4 * (p + 1) + K = ((4 * p + K) + 2) + 2 := by omega
    rw [hK]
    have hstep := ReachesPlus.trans (tick2Z c w ((4 * p + K) + 2) r1 e1)
      (tick2Z (c + dc r1) (nl r1) (4 * p + K) r2 e2)
    have hc : 4 * p + ((c + dc r1) + dc r2) = 4 * (p + 1) + c := by omega
    rw [hc] at hrun
    exact ReachesStar.trans hstep.to_star hrun

private def anchorCfg (p : List Tok × ℕ) : Cfg (Fin 2) (Fin 6) :=
  enc (.tZ 14 :: .tZ 6 :: p.1) (4 * p.2 - 12)

private def PP (p : List Tok × ℕ) : Prop :=
  46 ≤ p.2 ∧ Inv p.2 (N p.2) p.1

private theorem nj_ge (j : ℕ) : j ≤ nj j := by
  unfold nj; split_ifs <;> omega

private theorem super_step (p : List Tok × ℕ) (hp : PP p) :
    ∃ p', ReachesPlus target_tm (anchorCfg p) (anchorCfg p') ∧ PP p' := by
  obtain ⟨w, j⟩ := p
  obtain ⟨hj, hInv⟩ := hp
  dsimp only at hj hInv
  unfold anchorCfg
  dsimp only
  have hj1 : 1 ≤ j := by omega
  rcases ev_or j with ⟨i, ej, eN, en⟩ | ⟨i, ej, eN, en⟩
  · rw [eN] at hInv
    have hK0 : 4 * j - 12 = 8 * (i - 2) + 4 := by omega
    have hM0 : 6 * i = 2 * (i - 2) + (4 * (i - 2) + 12) := by omega
    rw [hM0] at hInv
    rw [hK0]
    obtain ⟨w1, r1, h1⟩ := era1 (i - 2) j (4 * (i - 2) + 12) w 6 14 4 hj1 hInv
    set M1 := 4 * (i - 2) + 11
    have hM1 : 4 * (i - 2) + 12 = M1 + 1 := by omega
    rw [hM1] at h1
    obtain ⟨x, w10, rfl, h2⟩ := inv_first j M1 w1 hj1 h1 (by omega)
    set vb1 := 8 * (i - 2) + 14
    set a1 := 4 * (i - 2) + 6
    have r2 :
        ReachesPlus target_tm
          (enc (.tZ vb1 :: .tZ a1 :: .tZ x :: w10) 4)
          (enc (.tO ((a1 + 3) + 1) :: .tO (x + 1) :: w10) ((vb1 + 4) + 3)) :=
      ReachesPlus.trans (tick4 vb1 a1 (.tZ x :: w10) 0 (.Bnc (.tO (x + 1) :: w10)) rfl)
        (era1end (vb1 + 4) (a1 + 3) (.tO (x + 1) :: w10))
    have hK2 : (vb1 + 4) + 3 = 4 * (2 * (i - 2) + 5) + 1 := by omega
    rw [hK2] at r2
    have hM2 : M1 = 2 * (2 * (i - 2) + 5) + 1 := by omega
    rw [hM2] at h2
    obtain ⟨w3, r3, h3⟩ :=
      era2 (2 * (i - 2) + 5) j 1 (.tO (x + 1) :: w10) ((a1 + 3) + 1) 1 hj1 h2
    obtain ⟨l, q, el1, h4⟩ := inv_last j 0 w3 hj1 h3 rfl
    obtain ⟨y, r, hl_eq, h5⟩ := inv_S j q l hj h4
    refine ⟨(.tZ (q + 3) :: ins y r, nj j), ?_, ⟨by have := nj_ge j; omega, h5⟩⟩
    refine ReachesStar.trans_plus r1 ?_
    refine ReachesPlus.trans r2 ?_
    refine ReachesStar.trans_plus r3 ?_
    refine ReachesPlus.trans (end2O (4 * (2 * (i - 2) + 5) + ((a1 + 3) + 1)) w3 l q el1) ?_
    dsimp only
    have hKf : 4 * (2 * (i - 2) + 5) + ((a1 + 3) + 1) = (4 * nj j - 12) + 14 := by omega
    rw [hl_eq, hKf]
    exact stage1 q y r (4 * nj j - 12)
  · rw [eN] at hInv
    have hK0 : 4 * j - 12 = 8 * (i - 1) + 0 := by omega
    have hM0 : 12 * i + 8 = 2 * (i - 1) + (10 * (i - 1) + 20) := by omega
    rw [hM0] at hInv
    rw [hK0]
    obtain ⟨w1, r1, h1⟩ := era1 (i - 1) j (10 * (i - 1) + 20) w 6 14 0 hj1 hInv
    set vb1 := 8 * (i - 1) + 14
    set a1 := 4 * (i - 1) + 6
    have r2 := era1end vb1 a1 w1
    have hK2 : vb1 + 3 = 4 * (2 * (i - 1) + 4) + 1 := by omega
    rw [hK2] at r2
    have hM2 : 10 * (i - 1) + 20 = 2 * (2 * (i - 1) + 4) + (6 * (i - 1) + 12) := by omega
    rw [hM2] at h1
    obtain ⟨w2, r3, h2⟩ := era2 (2 * (i - 1) + 4) j (6 * (i - 1) + 12) w1 (a1 + 1) 1 hj1 h1
    set M2 := 6 * (i - 1) + 11
    have hM3 : 6 * (i - 1) + 12 = M2 + 1 := by omega
    rw [hM3] at h2
    obtain ⟨x, w20, rfl, h3⟩ := inv_first j M2 w2 hj1 h2 (by omega)
    set c2 := 4 * (2 * (i - 1) + 4) + (a1 + 1)
    have r4 :
        ReachesPlus target_tm
          (enc (.tO c2 :: .tZ x :: w20) 1)
          (enc (.tZ 5 :: .tO (x + 4) :: w20) (4 * (3 * (i - 1) + 5) + 1)) := by
      refine ReachesPlus.trans (end2Z c2 x w20) ?_
      have hc2 : c2 + 2 = (4 * (3 * (i - 1) + 5) + 1) + 4 := by omega
      rw [hc2]
      exact era3start (x + 1) w20 (4 * (3 * (i - 1) + 5) + 1)
    have h4 := inv_payload j M2 (x + 1) (x + 4) w20 h3
    have hM4 : M2 = 2 * (3 * (i - 1) + 5) + 1 := by omega
    rw [hM4] at h4
    obtain ⟨w4, r5, h5⟩ := era3 (3 * (i - 1) + 5) j 1 (.tO (x + 4) :: w20) 5 1 hj1 h4
    obtain ⟨l, q, el1, h6⟩ := inv_last j 0 w4 hj1 h5 rfl
    obtain ⟨y, r, hl_eq, h7⟩ := inv_S j q l hj h6
    refine ⟨(.tZ (q + 3) :: ins y r, nj j), ?_, ⟨by have := nj_ge j; omega, h7⟩⟩
    refine ReachesStar.trans_plus r1 ?_
    refine ReachesPlus.trans r2 ?_
    refine ReachesStar.trans_plus r3 ?_
    refine ReachesPlus.trans r4 ?_
    refine ReachesStar.trans_plus r5 ?_
    refine ReachesPlus.trans (end3 (4 * (3 * (i - 1) + 5) + 5) w4 l q el1) ?_
    dsimp only
    have hKf : (4 * (3 * (i - 1) + 5) + 5) + 1 = (4 * nj j - 12) + 14 := by omega
    rw [hl_eq, hKf]
    exact stage1 q y r (4 * nj j - 12)

/-! ## Blank-Tape Trajectory (861 Macro Steps) and `is_not_halt` -/

private def runm : ℕ → List Tok → ℕ → Option (List Tok × ℕ)
  | 0, w, K => some (w, K)
  | n + 1, w, K =>
    match mstep w K with
    | none => none
    | some (w1, K1) => runm n w1 K1

private theorem runm_trans {m n : ℕ} {w w1 w2 : List Tok} {K K1 K2 : ℕ}
    (h1 : runm m w K = some (w1, K1)) (h2 : runm n w1 K1 = some (w2, K2)) :
    runm (m + n) w K = some (w2, K2) := by
  induction m generalizing w K with
  | zero =>
    rw [Nat.zero_add]
    dsimp only [runm] at h1
    injection h1 with h1'
    injection h1' with hw hK
    subst hw hK
    exact h2
  | succ m ih =>
    rw [Nat.succ_add]
    dsimp only [runm] at h1 ⊢
    rcases hm : mstep w K with _ | ⟨wa, Ka⟩ <;> rw [hm] at h1
    · nomatch h1
    · exact ih h1

private theorem runm_ok (n : ℕ) (w : List Tok) (K : ℕ) (w' : List Tok) (K' : ℕ)
    (h : runm (n + 1) w K = some (w', K')) :
    ReachesPlus target_tm (enc w K) (enc w' K') := by
  induction n generalizing w K with
  | zero =>
    dsimp only [runm] at h
    rcases hm : mstep w K with _ | ⟨w1, K1⟩ <;> rw [hm] at h
    · nomatch h
    · dsimp only at h
      injection h with h'
      injection h' with hw' hK'
      subst hw' hK'
      exact step_ok w K w1 K1 hm
  | succ n ih =>
    change (match mstep w K with | none => none | some (w1, K1) => runm (n + 1) w1 K1) =
      some (w', K') at h
    rcases hm : mstep w K with _ | ⟨w1, K1⟩ <;> rw [hm] at h
    · nomatch h
    · exact ReachesPlus.trans (step_ok w K w1 K1 hm) (ih w1 K1 h)

private def T0 : List Tok :=
  [.tZ 340, .tA 0, .tD 46, .tO 22, .tO 69, .tO 3, .tA 0, .tC 29, .tO 33, .tO 6, .tB 2, .tC 9]

private def P0 : List Tok :=
  [.tO 26, .tA 0, .tB 10, .tZ 12, .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0]

private def cp100 : List Tok × ℕ :=
  ([.tO 11, .tZ 5, .tB 35, .tZ 6, .tZ 10, .tZ 3, .tZ 2, .tO 0], 20)

private def cp200 : List Tok × ℕ :=
  ([.tO 46, .tO 79, .tZ 21, .tO 10, .tO 10, .tA 0, .tB 10, .tZ 3, .tZ 2, .tO 0], 5)

private def cp300 : List Tok × ℕ :=
  ([.tO 67, .tZ 116, .tO 15, .tZ 6, .tZ 25, .tA 0, .tB 10, .tZ 12, .tB 2, .tB 10,
    .tZ 3, .tZ 2, .tO 0], 11)

private def cp400 : List Tok × ℕ :=
  ([.tO 47, .tZ 144, .tZ 10, .tZ 5, .tB 21, .tZ 9, .tO 26, .tA 0, .tB 10, .tZ 12,
    .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0], 73)

private def cp500 : List Tok × ℕ :=
  ([.tZ 26, .tZ 195, .tZ 34, .tZ 17, .tO 26, .tZ 2, .tA 0, .tC 9, .tO 26, .tA 0,
    .tB 10, .tZ 12, .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0], 95)

private def cp600 : List Tok × ℕ :=
  ([.tO 3, .tA 0, .tC 243, .tZ 58, .tZ 29, .tO 33, .tO 6, .tB 2, .tC 9, .tO 26,
    .tA 0, .tB 10, .tZ 12, .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0], 120)

private def cp700 : List Tok × ℕ :=
  ([.tO 103, .tZ 50, .tZ 269, .tO 11, .tZ 5, .tB 61, .tZ 29, .tO 33, .tO 6, .tB 2,
    .tC 9, .tO 26, .tA 0, .tB 10, .tZ 12, .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0], 20)

private def cp800 : List Tok × ℕ :=
  ([.tZ 141, .tO 314, .tO 34, .tO 15, .tZ 65, .tZ 2, .tA 0, .tC 29, .tO 33, .tO 6,
    .tB 2, .tC 9, .tO 26, .tA 0, .tB 10, .tZ 12, .tB 2, .tB 10, .tZ 3, .tZ 2, .tO 0], 45)

private theorem runm_chain {m n k : ℕ} {w w1 w2 : List Tok} {K K1 K2 : ℕ}
    (h1 : runm m w K = some (w1, K1)) (h2 : runm n w1 K1 = some (w2, K2))
    (hmn : m + n = k := by decide) :
    runm k w K = some (w2, K2) := by
  subst hmn
  exact runm_trans h1 h2

private theorem run_c1 : runm 100 [] 0 = some cp100 := by decide +kernel
private theorem run_c2 : runm 100 cp100.1 cp100.2 = some cp200 := by decide +kernel
private theorem run_c3 : runm 100 cp200.1 cp200.2 = some cp300 := by decide +kernel
private theorem run_c4 : runm 100 cp300.1 cp300.2 = some cp400 := by decide +kernel
private theorem run_c5 : runm 100 cp400.1 cp400.2 = some cp500 := by decide +kernel
private theorem run_c6 : runm 100 cp500.1 cp500.2 = some cp600 := by decide +kernel
private theorem run_c7 : runm 100 cp600.1 cp600.2 = some cp700 := by decide +kernel
private theorem run_c8 : runm 100 cp700.1 cp700.2 = some cp800 := by decide +kernel
private theorem run_c9 :
    runm 61 cp800.1 cp800.2 = some (.tZ 14 :: .tZ 6 :: (T0 ++ P0), 4 * 46 - 12) := by decide +kernel

private theorem run0 :
    runm 861 [] 0 = some (.tZ 14 :: .tZ 6 :: (T0 ++ P0), 4 * 46 - 12) := by
  have h200 : runm 200 [] 0 = some cp200 := runm_chain run_c1 run_c2
  have h300 : runm 300 [] 0 = some cp300 := runm_chain h200 run_c3
  have h400 : runm 400 [] 0 = some cp400 := runm_chain h300 run_c4
  have h500 : runm 500 [] 0 = some cp500 := runm_chain h400 run_c5
  have h600 : runm 600 [] 0 = some cp600 := runm_chain h500 run_c6
  have h700 : runm 700 [] 0 = some cp700 := runm_chain h600 run_c7
  have h800 : runm 800 [] 0 = some cp800 := runm_chain h700 run_c8
  exact runm_chain h800 run_c9

private theorem inv0 : PP (T0 ++ P0, 46) := by
  refine ⟨by decide, T0, P0, 9, rfl, ?_, by decide, by decide, by decide, by decide, rfl⟩
  dsimp only [T0, Good, gapl]
  exact ⟨by decide, by decide, trivial⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  have h_init_eq : (init [] : Cfg (Fin 2) (Fin 6)) = enc [] 0 := rfl
  have h_reach : ReachesStar target_tm (init []) (anchorCfg (T0 ++ P0, 46)) := by
    rw [h_init_eq]
    exact (runm_ok 860 [] 0 (.tZ 14 :: .tZ 6 :: (T0 ++ P0)) (4 * 46 - 12) run0).to_star
  refine IsNotHalt.of_reachesPlus_invariant h_reach
    (P := fun cfg => ∃ p, cfg = anchorCfg p ∧ PP p)
    ⟨(T0 ++ P0, 46), rfl, inv0⟩ ?_
  rintro cfg ⟨p, rfl, hp⟩
  obtain ⟨p', hplus, hp'⟩ := super_step p hp
  exact ⟨anchorCfg p', hplus, p', rfl, hp'⟩


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB1RC_0LC1RE_1RA0LD_1LB0RD_0RFHHH_0RA0RF
