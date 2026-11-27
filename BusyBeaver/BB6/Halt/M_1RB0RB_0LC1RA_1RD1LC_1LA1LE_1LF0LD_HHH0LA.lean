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
import BusyBeaver.Calculi.RunWin

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_HHH0LA


variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_HHH0LA` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_HHH0LA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA`. -/
private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)


open Mathlib Relation Nat Turing BusyBeaver BusyBeaver.RunWin


private def tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 2, 1 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 0, Stmt.write 0 Dir.left)

/-! ## Layer 0: Letter transducer (Sim356) -/

private inductive L2 where
  | a | b

private def l2Beq : L2 → L2 → Bool
  | .a, .a => true
  | .b, .b => true
  | _, _ => false

private def l2ListBeq : List L2 → List L2 → Bool
  | [], [] => true
  | x :: xs, y :: ys => if l2Beq x y then l2ListBeq xs ys else false
  | _, _ => false

private theorem l2ListBeq_eq {xs ys : List L2} : l2ListBeq xs ys = true → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [l2ListBeq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [l2ListBeq]
    | cons y ys =>
      cases x <;> cases y <;> simp only [l2ListBeq, l2Beq, ite_true, ite_false,
        Bool.false_eq_true, false_implies, List.cons.injEq, true_and]
      · exact ih
      · exact ih

private inductive P3 where
  | a | b | c

private inductive St where
  | t0 | t1 | t2

private def stBeq : St → St → Bool
  | .t0, .t0 | .t1, .t1 | .t2, .t2 => true
  | _, _ => false

private theorem stBeq_eq {s t : St} : stBeq s t = true → s = t := by
  cases s <;> cases t <;> simp [stBeq]

private def stListBeq : List St → List St → Bool
  | [], [] => true
  | x :: xs, y :: ys => if stBeq x y then stListBeq xs ys else false
  | _, _ => false

private theorem stListBeq_eq {xs ys : List St} : stListBeq xs ys = true → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [stListBeq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [stListBeq]
    | cons y ys =>
      simp only [stListBeq]
      intro h
      cases hx : stBeq x y
      · simp [hx] at h
      · simp only [hx, ite_true] at h
        rw [stBeq_eq hx, ih h]

private def lcL : L2 → Fin 2
  | .a => 1
  | .b => 0

private def pushL (x : L2) (l : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.cons 1 (ListBlank.cons (lcL x) l)

private def encL : List L2 → ListBlank (Fin 2)
  | [] => default
  | x :: w' => pushL x (encL w')

private def lcP : P3 → Fin 2
  | .a => 1
  | .b => 0
  | .c => 1

private def rcP : P3 → Fin 2
  | .a => 1
  | .b => 1
  | .c => 0

private def encR : List P3 → ListBlank (Fin 2) → ListBlank (Fin 2)
  | [], r => r
  | x :: v', r => ListBlank.cons (lcP x) (ListBlank.cons (rcP x) (encR v' r))

private def cfgL (q : Option (Fin 6)) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨q, Tape.mk l.head l.tail r⟩

private def cfgR (q : Option (Fin 6)) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨q, Tape.mk r.head l r.tail⟩

private def recCfg (u : List L2) : Cfg (Fin 2) (Fin 6) :=
  ⟨some 1, Tape.mk 0 (ListBlank.cons 1 (encL u)) default⟩

private theorem fin2_cases (c : Fin 2) : c = 0 ∨ c = 1 := by
  rcases Nat.lt_or_ge c.val 1 with h0 | h1
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr (Fin.ext (by omega))

private theorem sim_init : ReachesStar tm (init []) (recCfg [.b, .b, .a, .a]) := by
  refine symRun_blank_star_of_eq tm
    (SymCfg.mk (some 0) (.mid [] 0 []))
    (SymCfg.mk (some 1) (.mid [1, 1, 0, 1, 0, 1, 1, 1, 1] 0 []))
    31 eval_init ?_ (by decide +kernel)
  rfl

-- 14 Cell rules via RunWin
private theorem rule_D_a (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 3) (pushL .a l) r)
      (cfgL (some 3) l (ListBlank.cons 0 (ListBlank.cons 1 r))) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 3) (.mid [1] 1 []))
    (SymCfg.mk (some 3) (.leftHead [0, 1]))
    2 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_D_ab (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 3) (pushL .b (pushL .a l)) r)
      (cfgR (some 0) (pushL .b (pushL .b l)) r) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 3) (.mid [0, 1, 1] 1 []))
    (SymCfg.mk (some 0) (.rightHead [1, 0, 1, 0]))
    11 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_D_bb (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 3) (pushL .b (pushL .b l)) r)
      (cfgL (some 2) l (encR [.c, .a] r)) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 3) (.mid [0, 1, 0] 1 []))
    (SymCfg.mk (some 2) (.leftHead [1, 0, 1, 1]))
    6 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgL, encR, lcP, rcP, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_C_a (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 2) (pushL .a l) r)
      (cfgL (some 2) l (ListBlank.cons 1 (ListBlank.cons 1 r))) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 2) (.mid [1] 1 []))
    (SymCfg.mk (some 2) (.leftHead [1, 1]))
    2 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_C_b (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 2) (pushL .b l) r)
      (cfgL (some 3) l (ListBlank.cons 0 (ListBlank.cons 1 r))) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 2) (.mid [0] 1 []))
    (SymCfg.mk (some 3) (.leftHead [0, 1]))
    4 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_D_grow (r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 3) default r)
      (cfgR (some 0) (pushL .a default) r) :=
  symRun_blankL_star_of_eq r tm
    (SymCfg.mk (some 3) (.mid [] 0 []))
    (SymCfg.mk (some 0) (.rightHead [1, 1]))
    3 (by simp [cfgL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_D_halt (r : ListBlank (Fin 2)) :
    HaltsFrom tm (cfgL (some 3) (pushL .b default) r) := by
  have hstar : ReachesStar tm (cfgL (some 3) (pushL .b default) r)
      ⟨some 5, Tape.mk 0 default (ListBlank.cons 1 (ListBlank.cons 1 r))⟩ :=
    symRun_blankL_star_of_eq r tm
      (SymCfg.mk (some 3) (.mid [0] 1 []))
      (SymCfg.mk (some 5) (.mid [] 0 [1, 1]))
      2 (by simp [cfgL, pushL, lcL, SymCfg.eval, SymCursor.eval]) rfl (by decide +kernel)
  exact ⟨_, hstar, rfl⟩

private theorem rule_C_edge (r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgL (some 2) default (ListBlank.cons 1 r))
      (cfgR (some 0) (pushL .a default) (ListBlank.cons 0 (ListBlank.cons 1 r))) :=
  symRun_blankL_star_of_eq r tm
    (SymCfg.mk (some 2) (.mid [] 0 [1]))
    (SymCfg.mk (some 0) (.mid [1, 1] 0 [1]))
    6 (by simp [cfgL, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_A_b (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgR (some 0) l (ListBlank.cons 0 (ListBlank.cons 1 r)))
      (cfgR (some 0) (pushL .a l) r) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 0) (.mid [] 0 [1]))
    (SymCfg.mk (some 0) (.rightHead [1, 1]))
    2 (by simp [cfgR, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_A_a (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgR (some 0) l (ListBlank.cons 1 (ListBlank.cons 1 r)))
      (cfgR (some 0) (pushL .b l) r) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 0) (.mid [] 1 [1]))
    (SymCfg.mk (some 0) (.rightHead [1, 0]))
    2 (by simp [cfgR, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_A_c (l r : ListBlank (Fin 2)) :
    ReachesStar tm (cfgR (some 0) l (ListBlank.cons 1 (ListBlank.cons 0 r)))
      (cfgR (some 0) (pushL .b l) r) :=
  symRun_open_star_of_eq l r tm
    (SymCfg.mk (some 0) (.mid [] 1 [0]))
    (SymCfg.mk (some 0) (.rightHead [1, 0]))
    6 (by simp [cfgR, SymCfg.eval, SymCursor.eval])
    (by simp [cfgR, pushL, lcL, SymCfg.eval, SymCursor.eval]) (by decide +kernel)

private theorem rule_A_end (l : ListBlank (Fin 2)) :
    ReachesPlus tm (cfgR (some 0) l default)
      ⟨some 1, Tape.mk 0 (ListBlank.cons 1 l) default⟩ :=
  symRun_blankR_plus_of_eq l tm
    (SymCfg.mk (some 0) (.mid [] 0 []))
    (SymCfg.mk (some 1) (.mid [1] 0 []))
    0 (by simp [cfgR, SymCfg.eval, SymCursor.eval]) rfl (by decide +kernel)

private theorem rule_A_end0 (l : ListBlank (Fin 2)) :
    ReachesPlus tm (cfgR (some 0) l (ListBlank.cons 0 default))
      ⟨some 1, Tape.mk 0 (ListBlank.cons 1 l) default⟩ := by
  rw [ListBlank.cons_zero_default]
  exact rule_A_end l

private theorem rule_B_start (l : ListBlank (Fin 2)) :
    ReachesStar tm ⟨some 1, Tape.mk 0 (ListBlank.cons 1 (pushL .b l)) default⟩
      (cfgL (some 3) l (encR [.b, .c] default)) := by
  refine symRun_blankR_star_of_eq l tm
    (SymCfg.mk (some 1) (.mid [1, 1, 0] 0 []))
    (SymCfg.mk (some 3) (.leftHead [0, 1, 1]))
    6 rfl ?_ (by decide +kernel)
  simp [encR, lcP, rcP, cfgL, SymCfg.eval, SymCursor.eval, ListBlank.cons_zero_default]

private inductive DOut where
  | dturn (w : List L2) (v : List P3)
  | dhalt
  | dovf (v : List P3)

private def dscan : St → List L2 → List P3 → DOut
  | .t0, [], v => .dturn [.a] v
  | .t1, [], _ => .dhalt
  | .t2, [], v => .dovf v
  | .t0, .a :: w', v => dscan .t0 w' (.b :: v)
  | .t1, .a :: w', v => .dturn (.b :: .b :: w') v
  | .t2, .a :: w', v => dscan .t2 w' (.a :: v)
  | .t0, .b :: w', v => dscan .t1 w' v
  | .t1, .b :: w', v => dscan .t2 w' (.c :: .a :: v)
  | .t2, .b :: w', v => dscan .t0 w' (.b :: v)

private def dconf
    (s : St) (w : List L2) (v : List P3) (r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  match s with
  | .t0 => cfgL (some 3) (encL w) (encR v r)
  | .t1 => cfgL (some 3) (encL (.b :: w)) (encR v r)
  | .t2 => cfgL (some 2) (encL w) (encR v r)

private def DGood (c : Cfg (Fin 2) (Fin 6)) (o : DOut) (r : ListBlank (Fin 2)) : Prop :=
  match o with
  | .dturn w v => ReachesStar tm c (cfgR (some 0) (encL w) (encR v r))
  | .dhalt => HaltsFrom tm c
  | .dovf v => ReachesStar tm c (cfgL (some 2) default (encR v r))

private theorem DGood_step {c c' : Cfg (Fin 2) (Fin 6)} {o : DOut} {r : ListBlank (Fin 2)}
    (h1 : ReachesStar tm c c') (h2 : DGood c' o r) : DGood c o r := by
  cases o with
  | dturn w v => exact stepStar_trans h1 h2
  | dhalt => exact HaltsFrom.of_reachesStar h1 h2
  | dovf v => exact stepStar_trans h1 h2

private theorem dscan_spec (w : List L2) :
    ∀ s v r, DGood (dconf s w v r) (dscan s w v) r := by
  induction w with
  | nil =>
    intro s v r
    cases s with
    | t0 => exact rule_D_grow (encR v r)
    | t1 => exact rule_D_halt (encR v r)
    | t2 => exact ReachesStar.refl tm _
  | cons x w ih =>
    intro s v r
    cases x <;> cases s
    · exact DGood_step (rule_D_a (encL w) (encR v r)) (ih .t0 (.b :: v) r)
    · exact rule_D_ab (encL w) (encR v r)
    · exact DGood_step (rule_C_a (encL w) (encR v r)) (ih .t2 (.a :: v) r)
    · exact ih .t1 v r
    · exact DGood_step (rule_D_bb (encL w) (encR v r)) (ih .t2 (.c :: .a :: v) r)
    · exact DGood_step (rule_C_b (encL w) (encR v r)) (ih .t0 (.b :: v) r)

private def sig : P3 → L2
  | .a => .b
  | .b => .a
  | .c => .b

private theorem apass (v : List P3) :
    ∀ w r, ReachesStar tm (cfgR (some 0) (encL w) (encR v r))
      (cfgR (some 0) (encL (List.reverseAux (v.map sig) w)) r) := by
  induction v with
  | nil => intro w r; exact ReachesStar.refl tm _
  | cons x v ih =>
    intro w r
    cases x
    · exact stepStar_trans (rule_A_a (encL w) (encR v r)) (ih (.b :: w) r)
    · exact stepStar_trans (rule_A_b (encL w) (encR v r)) (ih (.a :: w) r)
    · exact stepStar_trans (rule_A_c (encL w) (encR v r)) (ih (.b :: w) r)

private def aletter : Fin 2 → Fin 2 → Option L2
  | 0, 1 => some .a
  | 1, 1 => some .b
  | 1, 0 => some .b
  | 0, 0 => none

private def oscan : Fin 2 → List P3 → List L2 → Option (List L2)
  | carry, [], acc => match carry with | 0 => some acc | 1 => none
  | carry, x :: v', acc =>
    match aletter carry (lcP x) with
    | some y => oscan (rcP x) v' (y :: acc)
    | none => none

private theorem oscan_spec (v : List P3) :
    ∀ carry acc u, oscan carry v acc = some u →
      ReachesPlus tm (cfgR (some 0) (encL acc) (ListBlank.cons carry (encR v default)))
          (recCfg u) := by
  induction v with
  | nil =>
    intro carry acc u h
    rcases fin2_cases carry with rfl | rfl
    · simp only [oscan, Option.some.injEq] at h; subst h; exact rule_A_end0 (encL acc)
    · simp [oscan] at h
  | cons x v ih =>
    intro carry acc u h
    simp only [oscan] at h
    rcases h1 : aletter carry (lcP x) with _ | y
    · simp [h1] at h
    · simp only [h1] at h
      have hstep : ReachesStar tm
          (cfgR (some 0) (encL acc) (ListBlank.cons carry (encR (x :: v) default)))
          (cfgR (some 0) (encL (y :: acc)) (ListBlank.cons (rcP x) (encR v default))) := by
        rcases fin2_cases carry with rfl | rfl
        · cases x
          · simp only [aletter, lcP, Option.some.injEq] at h1; subst h1
            exact rule_A_b (encL acc) (ListBlank.cons (rcP .a) (encR v default))
          · simp [aletter, lcP] at h1
          · simp only [aletter, lcP, Option.some.injEq] at h1; subst h1
            exact rule_A_b (encL acc) (ListBlank.cons (rcP .c) (encR v default))
        · cases x
          · simp only [aletter, lcP, Option.some.injEq] at h1; subst h1
            exact rule_A_a (encL acc) (ListBlank.cons (rcP .a) (encR v default))
          · simp only [aletter, lcP, Option.some.injEq] at h1; subst h1
            exact rule_A_c (encL acc) (ListBlank.cons (rcP .b) (encR v default))
          · simp only [aletter, lcP, Option.some.injEq] at h1; subst h1
            exact rule_A_a (encL acc) (ListBlank.cons (rcP .c) (encR v default))
      exact stepStar_stepPlus_stepPlus hstep (ih (rcP x) (y :: acc) u h)

private inductive Out where
  | next (u : List L2)
  | halt
  | stuck

private def ovf : List P3 → Out
  | [] => .stuck
  | x :: v =>
    match lcP x with
    | 1 => match oscan 0 (x :: v) [.a] with | some u => .next u | none => .stuck
    | 0 => .stuck

private def sweep : List L2 → Out
  | .b :: w =>
    match dscan .t0 w [.b, .c] with
    | .dturn w' v => .next (List.reverseAux (v.map sig) w')
    | .dhalt => .halt
    | .dovf v => ovf v
  | _ => .stuck

private def Good (c : Cfg (Fin 2) (Fin 6)) (o : Out) : Prop :=
  match o with
  | .next u => ReachesPlus tm c (recCfg u)
  | .halt => HaltsFrom tm c
  | .stuck => True

private theorem sim (u : List L2) : Good (recCfg u) (sweep u) := by
  cases u with
  | nil => trivial
  | cons x w =>
    cases x
    · trivial
    · simp only [sweep]
      have h0 : ReachesStar tm (recCfg (.b :: w)) (dconf .t0 w [.b, .c] default) :=
        rule_B_start (encL w)
      have hd := dscan_spec w .t0 [.b, .c] default
      cases hm : dscan .t0 w [.b, .c] with
      | dturn w' v =>
        simp only [hm] at hd
        exact stepStar_stepPlus_stepPlus
            (stepStar_trans h0 (stepStar_trans hd (apass v w' default)))
          (rule_A_end (encL (List.reverseAux (v.map sig) w')))
      | dhalt =>
        simp only [hm] at hd
        exact HaltsFrom.of_reachesStar h0 hd
      | dovf v =>
        simp only [hm, DGood] at hd
        cases v with
        | nil => trivial
        | cons x v' =>
          simp only [ovf]
          have hfx : lcP x = 0 ∨ lcP x = 1 := by cases x <;> simp [lcP]
          rcases hfx with hlc | hlc
          · simp only [hlc]; trivial
          · simp only [hlc]
            cases ho : oscan 0 (x :: v') [.a] with
            | none => trivial
            | some u' =>
              have hos : ReachesPlus tm
                  (cfgR (some 0) (pushL .a default)
                      (ListBlank.cons 0
                      (ListBlank.cons 1 (ListBlank.cons (rcP x) (encR v' default)))))
                  (recCfg u') := by
                simpa [encL, encR, hlc] using oscan_spec (x :: v') 0 [.a] u' ho
              have hd' : ReachesStar tm (dconf .t0 w [.b, .c] default)
                  (cfgL (some 2) default
                      (ListBlank.cons 1 (ListBlank.cons (rcP x) (encR v' default)))) := by
                simpa [encR, hlc] using hd
              have hedge := rule_C_edge (ListBlank.cons (rcP x) (encR v' default))
              exact stepStar_stepPlus_stepPlus (stepStar_trans h0 (stepStar_trans hd' hedge)) hos

private def runSim : Nat → List L2 → Out
  | 0, u => .next u
  | n + 1, u =>
    match sweep u with
    | .next u' => runSim n u'
    | o => o

private def Good' (c : Cfg (Fin 2) (Fin 6)) (o : Out) : Prop :=
  match o with
  | .next u => ReachesStar tm c (recCfg u)
  | .halt => HaltsFrom tm c
  | .stuck => True

private theorem reachesPlus_to_reachesStar {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus tm c₁ c₂) : ReachesStar tm c₁ c₂ :=
  ⟨h.choose, h.choose_spec.2⟩

private theorem run_spec (n : Nat) : ∀ u, Good' (recCfg u) (runSim n u) := by
  induction n with
  | zero => intro u; exact ReachesStar.refl tm (recCfg u)
  | succ n ih =>
    intro u
    simp only [runSim]
    have hsim := sim u
    cases hs : sweep u with
    | next u' =>
      simp only [hs, Good] at hsim
      have hih := ih u'
      cases hr : runSim n u' with
      | next u'' =>
        simp only [hr, Good'] at hih ⊢
        exact stepStar_trans (reachesPlus_to_reachesStar hsim) hih
      | halt =>
        simp only [hr, Good'] at hih ⊢
        exact HaltsFrom.of_reachesStar (reachesPlus_to_reachesStar hsim) hih
      | stuck => simp only [hr, Good']
    | halt =>
      simp only [hs, Good] at hsim
      exact hsim
    | stuck => trivial

private theorem run_halts (u0 : List L2) (n : Nat) (h0 : ReachesStar tm (init []) (recCfg u0))
    (hr : runSim n u0 = .halt) : IsHalt tm := by
  have hs := run_spec n u0
  rw [hr] at hs
  exact HaltsFrom.of_reachesStar h0 hs

private theorem run_reach (u0 : List L2) (n : Nat) (u : List L2)
    (h0 : ReachesStar tm (init []) (recCfg u0))
    (hr : runSim n u0 = .next u) : ReachesStar tm (init []) (recCfg u) := by
  have hs := run_spec n u0
  rw [hr] at hs
  exact stepStar_trans h0 hs

/-! ## Fast transducer equivalence (`actp` / `sweepFast`) -/

private def actp : St → List L2 → List L2 × Option St
  | s, [] => ([], some s)
  | .t0, .a :: u' => let r := actp .t0 u'; (.a :: r.1, r.2)
  | .t1, .a :: u' => (.b :: u', none)
  | .t2, .a :: u' => let r := actp .t2 u'; (.b :: r.1, r.2)
  | .t0, .b :: u' => let r := actp .t1 u'; (.b :: r.1, r.2)
  | .t1, .b :: u' => let r := actp .t2 u'; (.b :: r.1, r.2)
  | .t2, .b :: u' => let r := actp .t0 u'; (.a :: r.1, r.2)

private def actpRev (s : St) : List L2 → List L2 → List L2 × Option St
  | [], acc => (acc.reverse, some s)
  | .a :: u', acc =>
    match s with
    | .t0 => actpRev .t0 u' (.a :: acc)
    | .t1 => (acc.reverseAux (.b :: u'), none)
    | .t2 => actpRev .t2 u' (.b :: acc)
  | .b :: u', acc =>
    match s with
    | .t0 => actpRev .t1 u' (.b :: acc)
    | .t1 => actpRev .t2 u' (.b :: acc)
    | .t2 => actpRev .t0 u' (.a :: acc)

private theorem actpRev_eq (s : St) (u acc : List L2) :
    actpRev s u acc = let r := actp s u; (acc.reverseAux r.1, r.2) := by
  induction u generalizing s acc with
  | nil => simp [actpRev, actp]
  | cons x u ih =>
    cases x <;> cases s <;> simp [actpRev, actp, ih, List.reverseAux]

private theorem actp_eq_actpRev (s : St) (u : List L2) : actp s u = actpRev s u [] := by
  simp [actpRev_eq, List.reverseAux]

private theorem actp_app (u : List L2) : ∀ s x,
    actp s (u ++ x) = match actp s u with
      | (u', some s') => let r := actp s' x; (u' ++ r.1, r.2)
      | (u', none) => (u' ++ x, none) := by
  induction u with
  | nil => intro s x; simp [actp]
  | cons x0 u ih =>
    intro s x
    cases x0 <;> cases s <;> simp only [actp, ih, List.cons_append]
    all_goals cases h : actp _ u with | mk u' o =>
      cases o <;> simp

private def pre : St → List L2
  | .t1 => [.b]
  | _ => []

private def grow : List L2 × Option St → List L2
  | (u, some .t0) => u ++ [.a]
  | (u, _) => u

private theorem dscan_actp (w : List L2) : ∀ s v,
    match dscan s w v with
    | .dturn w' v' =>
      (v'.map sig).reverse ++ w' =
        (v.map sig).reverse ++ (pre s ++ grow (actp s w)) ∧
        ((actp s w).2 = none ∨ (actp s w).2 = some .t0)
    | .dhalt => (actp s w).2 = some .t1
    | .dovf _ => (actp s w).2 = some .t2 := by
  induction w with
  | nil =>
    intro s v
    cases s <;> simp [dscan, actp, pre, grow]
  | cons x w ih =>
    intro s v
    cases x <;> cases s
    · have h := ih .t0 (.b :: v)
      simp only [dscan, actp] at h ⊢
      cases hd : dscan .t0 w (.b :: v) <;> simp only [hd] at h ⊢
      · cases ha : actp .t0 w with | mk u o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;> simp [hrev, grow, pre, sig,
            List.append_assoc]
      · exact h
      · exact h
    · simp [dscan, actp, pre, grow]
    · have h := ih .t2 (.a :: v)
      simp only [dscan, actp] at h ⊢
      cases hd : dscan .t2 w (.a :: v) <;> simp only [hd] at h ⊢
      · cases ha : actp .t2 w with | mk u o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;> simp [hrev, grow, pre, sig,
            List.append_assoc]
      · exact h
      · exact h
    · have h := ih .t1 v
      simp only [dscan, actp] at h ⊢
      cases hd : dscan .t1 w v <;> simp only [hd] at h ⊢
      · cases ha : actp .t1 w with | mk u o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;> simp [hrev, grow, pre]
      · exact h
      · exact h
    · have h := ih .t2 (.c :: .a :: v)
      simp only [dscan, actp] at h ⊢
      cases hd : dscan .t2 w (.c :: .a :: v) <;> simp only [hd] at h ⊢
      · cases ha : actp .t2 w with | mk u o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;> simp [hrev, grow, pre, sig,
            List.append_assoc]
      · exact h
      · exact h
    · have h := ih .t0 (.b :: v)
      simp only [dscan, actp] at h ⊢
      cases hd : dscan .t0 w (.b :: v) <;> simp only [hd] at h ⊢
      · cases ha : actp .t0 w with | mk u o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;> simp [hrev, grow, pre, sig,
            List.append_assoc]
      · exact h
      · exact h

private def sweepFast : List L2 → Out
  | .b :: w =>
    match actpRev .t0 w [] with
    | (u, none) => .next (.b :: .a :: u)
    | (u, some .t0) => .next (.b :: .a :: (u ++ [.a]))
    | (_, some .t1) => .halt
    | (_, some .t2) =>
      match dscan .t0 w [.b, .c] with
      | .dovf v => ovf v
      | _ => .stuck
  | _ => .stuck

private theorem sweep_eq_sweepFast (u : List L2) : sweep u = sweepFast u := by
  cases u with
  | nil => rfl
  | cons x w =>
    cases x
    · rfl
    · simp only [sweep, sweepFast, ← actp_eq_actpRev]
      have h := dscan_actp w .t0 [.b, .c]
      cases hd : dscan .t0 w [.b, .c] <;> simp only [hd] at h
      · cases ha : actp .t0 w with | mk u' o =>
        simp only [ha] at h
        rcases h with ⟨hrev, ho | ho⟩ <;> subst ho <;>
          simp [hrev, grow, pre, sig]
      · cases ha : actp .t0 w with | mk u' o =>
        simp only [ha] at h; simp [h]
      · cases ha : actp .t0 w with | mk u' o =>
        simp only [ha] at h; simp [h]

private def runSimFast : Nat → List L2 → Out
  | 0, u => .next u
  | n + 1, u =>
    match sweepFast u with
    | .next u' => runSimFast n u'
    | o => o

private theorem runSim_eq_runSimFast (n : Nat) : ∀ u, runSim n u = runSimFast n u := by
  induction n with
  | zero => intro u; rfl
  | succ n ih =>
    intro u
    simp only [runSim, runSimFast, sweep_eq_sweepFast]
    cases sweepFast u with
    | next u' => exact ih u'
    | halt => rfl
    | stuck => rfl

/-! ## Layer 1a: Blocks, emitters and cascades (Blocks356) -/

private def UU (n : Nat) (z : List L2) : List L2 := .b :: List.replicate n .a ++ .b :: z

private theorem actp_t0_block (n : Nat) (z : List L2) :
    actp .t0 (List.replicate n .a ++ .b :: z) =
      (let r := actp .t1 z; (List.replicate n .a ++ .b :: r.1, r.2)) := by
  induction n with
  | zero => simp [actp]
  | succ n ih => simp [List.replicate_succ, actp, ih]

private theorem sweep_quiet (n : Nat) (z z' : List L2) (h : actp .t1 z = (z', none)) :
    sweep (UU n z) = .next (UU (n + 1) z') := by
  rw [sweep_eq_sweepFast]
  simp only [UU, sweepFast, ← actp_eq_actpRev]
  simp [actp_t0_block, h, List.replicate_succ]

private theorem sweep_grow (n : Nat) (z z' : List L2) (h : actp .t1 z = (z', some .t0)) :
    sweep (UU n z) = .next (UU (n + 1) (z' ++ [.a])) := by
  rw [sweep_eq_sweepFast]
  simp only [UU, sweepFast, ← actp_eq_actpRev]
  simp [actp_t0_block, h, List.replicate_succ, List.append_assoc]

private theorem sweep_halt (n : Nat) (z z' : List L2) (h : actp .t1 z = (z', some .t1)) :
    sweep (UU n z) = .halt := by
  rw [sweep_eq_sweepFast]
  simp only [UU, sweepFast, ← actp_eq_actpRev]
  simp [actp_t0_block, h]

private def qf : Nat → List L2 → Option (List L2)
  | 0, u => some u
  | m + 1, u =>
    match actp .t1 u with
    | (u1, none) => qf m u1
    | _ => none

private def em1 (u : List L2) : Option (St × List L2) :=
  match actp .t1 u with
  | (u1, some s) => some (s, u1)
  | _ => none

private def emf : Nat → List L2 → Option (St × List L2)
  | 0, _ => none
  | m + 1, u =>
    match qf m u with
    | some u1 => em1 u1
    | none => none

private theorem qf_add (m1 : Nat) : ∀ m2 u u1, qf m1 u = some u1 → qf (m1 + m2) u = qf m2 u1 := by
  induction m1 with
  | zero => intro m2 u u1 h; simp only [qf,
      Option.some.injEq] at h; subst h; simp only [Nat.zero_add]
  | succ m1 ih =>
    intro m2 u u1 h
    simp only [qf] at h
    cases ha : actp .t1 u with | mk u0 o =>
    simp only [ha] at h
    cases o with
    | none =>
      simp only [Nat.succ_add, qf, ha]
      exact ih m2 u0 u1 h
    | some _ => simp at h

private theorem emf_qf (m1 m2 : Nat) (u u1 : List L2) (h : qf m1 u = some u1) :
    emf (m1 + (m2 + 1)) u = emf (m2 + 1) u1 := by
  rw [← Nat.add_assoc]
  simp only [emf, qf_add m1 m2 u u1 h]

private theorem qf_app (m : Nat) : ∀ u u' v, qf m u = some u' → qf m (u ++ v) = some (u' ++ v) := by
  induction m with
  | zero => intro u u' v h; simp only [qf, Option.some.injEq] at h; subst h; rfl
  | succ m ih =>
    intro u u' v h
    simp only [qf] at h ⊢
    rw [actp_app]
    cases ha : actp .t1 u with | mk u0 o =>
    simp only [ha] at h ⊢
    cases o with
    | none => exact ih u0 u' v h
    | some _ => simp at h

private theorem emf_then_quiet {m : Nat} {u : List L2} {s : St} {u1 v v1 : List L2}
    (h1 : emf m u = some (s, u1)) (hv : actp s v = (v1, none)) :
    qf m (u ++ v) = some (u1 ++ v1) := by
  cases m with
  | zero => simp [emf] at h1
  | succ m =>
    simp only [emf] at h1
    cases hq : qf m u with
    | none => simp [hq] at h1
    | some u0 =>
      simp only [hq, em1] at h1
      cases ha : actp .t1 u0 with | mk u2 o =>
      simp only [ha] at h1
      cases o with
      | none => simp at h1
      | some s' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        have := qf_app m u u0 v hq
        rw [qf_add m 1 (u ++ v) (u0 ++ v) this]
        simp only [qf, actp_app, ha, hv]

private theorem emf_then_emit {m : Nat} {u : List L2} {s : St} {u1 v v1 : List L2} {t : St}
    (h1 : emf m u = some (s, u1)) (hv : actp s v = (v1, some t)) :
    emf m (u ++ v) = some (t, u1 ++ v1) := by
  cases m with
  | zero => simp [emf] at h1
  | succ m =>
    simp only [emf] at h1 ⊢
    cases hq : qf m u with
    | none => simp [hq] at h1
    | some u0 =>
      simp only [hq, em1] at h1 ⊢
      cases ha : actp .t1 u0 with | mk u2 o =>
      simp only [ha] at h1
      cases o with
      | none => simp at h1
      | some s' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        rcases h1 with ⟨rfl, rfl⟩
        simp only [qf_app m u u0 v hq, actp_app, ha, hv]

private inductive Feed : List L2 → List L2 → Nat → List L2 → List L2 → Prop where
  | nil (u v : List L2) : Feed u v 0 u v
  | step {u v : List L2} {m : Nat} {s : St} {u1 v1 : List L2} {M : Nat} {u' v' : List L2} :
      emf m u = some (s, u1) → actp s v = (v1, none) → Feed u1 v1 M u' v' →
      Feed u v (m + M) u' v'

private theorem Feed.quiet {u v : List L2} {M : Nat} {u' v' : List L2}
    (h : Feed u v M u' v') : qf M (u ++ v) = some (u' ++ v') := by
  induction h with
  | nil => rfl
  | @step u v m s u1 v1 M u' v' h1 h2 _ ih =>
    rw [qf_add m M (u ++ v) (u1 ++ v1) (emf_then_quiet h1 h2)]
    exact ih

private theorem Feed.emit {u v : List L2} {M : Nat} {u1 v1 : List L2} {m : Nat} {s : St}
    {u2 v2 : List L2} {t : St}
    (hf : Feed u v M u1 v1) (h1 : emf m u1 = some (s, u2)) (h2 : actp s v1 = (v2, some t)) :
    emf (M + m) (u ++ v) = some (t, u2 ++ v2) := by
  cases m with
  | zero => simp [emf] at h1
  | succ m =>
    rw [emf_qf M m (u ++ v) (u1 ++ v1) hf.quiet]
    exact emf_then_emit h1 h2

/-! ## Layer 0b: Level-end image (Ovf356) -/

private def dstep : St → L2 → Option (P3 × St)
  | .t0, .a => some (.b, .t0)
  | .t0, .b => some (.a, .t1)
  | .t1, .a => none
  | .t1, .b => some (.c, .t2)
  | .t2, .a => some (.a, .t2)
  | .t2, .b => some (.b, .t0)

private def oimg : St → List L2 → Option (Fin 2 × List L2 × List P3)
  | .t2, [] => some (0, [], [])
  | _, [] => none
  | s, x :: w' =>
    match dstep s x with
    | none => none
    | some (d, s') =>
      match oimg s' w' with
      | none => none
      | some (c', i', d') =>
        match aletter c' (lcP d) with
        | some y => some (rcP d, y :: i', d :: d')
        | none => none

private def oim : St → List L2 → Option (Fin 2 × List L2)
  | .t2, [] => some (0, [])
  | _, [] => none
  | s, x :: w' =>
    match dstep s x with
    | none => none
    | some (d, s') =>
      match oim s' w' with
      | none => none
      | some (c', i') =>
        match aletter c' (lcP d) with
        | some y => some (rcP d, y :: i')
        | none => none

private theorem oim_oimg (w : List L2) :
    ∀ s c i, oim s w = some (c, i) → ∃ d, oimg s w = some (c, i, d) := by
  induction w with
  | nil =>
    intro s c i h
    cases s <;> simp only [oim, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨[], rfl⟩
  | cons x w ih =>
    intro s c i h
    simp only [oim] at h
    cases hd : dstep s x with
    | none => simp [hd] at h
    | some ds =>
      rcases ds with ⟨d, s'⟩
      simp only [hd] at h
      cases ho : oim s' w with
      | none => simp [ho] at h
      | some ci =>
        rcases ci with ⟨c', i'⟩
        simp only [ho] at h
        obtain ⟨d', hd'⟩ := ih s' c' i' ho
        simp only [oimg, hd, hd']
        cases ha : aletter c' (lcP d) with
        | none => simp [ha] at h
        | some y =>
          simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact ⟨d :: d', rfl⟩

private def pend : St → List P3
  | .t1 => [.a]
  | _ => []

private theorem dscan_oimg (w : List L2) : ∀ s v c i d,
    oimg s w = some (c, i, d) → dscan s w v = .dovf (d.reverseAux (pend s ++ v)) := by
  induction w with
  | nil =>
    intro s v c i d h
    cases s <;> simp only [oimg, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    rcases h with ⟨_, _, rfl⟩
    rfl
  | cons x w ih =>
    intro s v c i d h
    cases x <;> cases s <;> simp only [oimg, dstep] at h
    · cases ho : oimg .t0 w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP .b) <;> simp only [ha] at h
        · simp at h
        · rcases h with ⟨_, _, rfl⟩
          simp [dscan, ih .t0 (.b :: v) c' i' d' ho, List.reverseAux, pend]
    · simp at h
    · cases ho : oimg .t2 w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP .a) <;> simp only [ha] at h
        · simp at h
        · rcases h with ⟨_, _, rfl⟩
          simp [dscan, ih .t2 (.a :: v) c' i' d' ho, List.reverseAux, pend]
    · cases ho : oimg .t1 w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP .a) <;> simp only [ha] at h
        · simp at h
        · rcases h with ⟨_, _, rfl⟩
          simp [dscan, ih .t1 v c' i' d' ho, List.reverseAux, pend]
    · cases ho : oimg .t2 w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP .c) <;> simp only [ha] at h
        · simp at h
        · rcases h with ⟨_, _, rfl⟩
          simp [dscan, ih .t2 (.c :: .a :: v) c' i' d' ho, List.reverseAux, pend]
    · cases ho : oimg .t0 w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP .b) <;> simp only [ha] at h
        · simp at h
        · rcases h with ⟨_, _, rfl⟩
          simp [dscan, ih .t0 (.b :: v) c' i' d' ho, List.reverseAux, pend]

private def ost : Fin 2 → List P3 → List L2 → Option (Fin 2 × List L2)
  | c, [], acc => some (c, acc)
  | c, x :: v', acc =>
    match aletter c (lcP x) with
    | some y => ost (rcP x) v' (y :: acc)
    | none => none

private theorem ost_app (v1 : List P3) : ∀ c v2 acc,
    ost c (v1 ++ v2) acc = match ost c v1 acc with
      | some (c', acc') => ost c' v2 acc'
      | none => none := by
  induction v1 with
  | nil => intro c v2 acc; simp [ost]
  | cons x v1 ih =>
    intro c v2 acc
    simp only [ost, List.cons_append]
    cases aletter c (lcP x) with
    | none => rfl
    | some y => exact ih (rcP x) v2 (y :: acc)

private theorem oscan_ost (v : List P3) : ∀ c acc,
    oscan c v acc = match ost c v acc with
      | some (0, acc') => some acc'
      | _ => none := by
  induction v with
  | nil =>
    intro c acc
    rcases fin2_cases c with rfl | rfl <;> simp [oscan, ost]
  | cons x v ih =>
    intro c acc
    simp only [oscan, ost]
    cases aletter c (lcP x) with
    | none => rfl
    | some y => exact ih (rcP x) (y :: acc)

private theorem ost_oimg (w : List L2) : ∀ s c i d,
    oimg s w = some (c, i, d) → ost 0 d.reverse [.a] = some (c, i ++ [.a]) := by
  induction w with
  | nil =>
    intro s c i d h
    cases s <;> simp only [oimg, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    rcases h with ⟨rfl, rfl, rfl⟩
    rfl
  | cons x w ih =>
    intro s c i d h
    simp only [oimg] at h
    cases hd : dstep s x with
    | none => simp [hd] at h
    | some ds =>
      rcases ds with ⟨d0, s'⟩
      simp only [hd] at h
      cases ho : oimg s' w with
      | none => simp [ho] at h
      | some cid =>
        rcases cid with ⟨c', i', d'⟩
        simp only [ho] at h
        cases ha : aletter c' (lcP d0) with
        | none => simp [ha] at h
        | some y =>
          simp only [ha, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl⟩
          simp only [List.reverse_cons, ost_app, ih s' c' i' d' ho, ost, ha]
          rfl

private theorem ovf_of_oscan (v : List P3) (u : List L2) (hne : v ≠ [])
    (h : oscan 0 v [.a] = some u) : ovf v = .next u := by
  cases v with
  | nil => exact absurd rfl hne
  | cons x v' =>
    simp only [ovf]
    have hfx : lcP x = 0 ∨ lcP x = 1 := by cases x <;> simp [lcP]
    rcases hfx with h0 | h1
    · simp only [oscan, h0, aletter] at h; simp at h
    · simp only [h1, h]

private theorem sweep_ovf (w i : List L2) (h : oim .t0 w = some (1, i)) :
    sweep (.b :: w) = .next (.b :: .b :: i ++ [.a]) := by
  obtain ⟨d, hd⟩ := oim_oimg w .t0 1 i h
  simp only [sweep, dscan_oimg w .t0 [.b, .c] 1 i d hd, pend, List.nil_append]
  rw [List.reverseAux_eq_append]
  apply ovf_of_oscan
  · cases hd0 : d.reverse <;> simp [hd0]
  · simp [oscan_ost, ost_app, ost_oimg w .t0 1 i d hd, ost, lcP, rcP, aletter]

private def stt : St → List L2 → Option St
  | s, [] => some s
  | s, x :: u' =>
    match dstep s x with
    | none => none
    | some (_, s') => stt s' u'

private def oblk : St → List L2 → Fin 2 → Option (Fin 2 × List L2)
  | _, [], cin => some (cin, [])
  | s, x :: u', cin =>
    match dstep s x with
    | none => none
    | some (d, s') =>
      match oblk s' u' cin with
      | none => none
      | some (c', i') =>
        match aletter c' (lcP d) with
        | some y => some (rcP d, y :: i')
        | none => none

private theorem oim_app (u : List L2) : ∀ s x so cx ix c iu,
    stt s u = some so → oim so x = some (cx, ix) → oblk s u cx = some (c, iu) →
    oim s (u ++ x) = some (c, iu ++ ix) := by
  induction u with
  | nil =>
    intro s x so cx ix c iu hs hx hu
    simp only [stt, Option.some.injEq] at hs; subst hs
    simp only [oblk, Option.some.injEq, Prod.mk.injEq] at hu; rcases hu with ⟨rfl, rfl⟩
    exact hx
  | cons a0 u ih =>
    intro s x so cx ix c iu hs hx hu
    simp only [stt, oblk, oim, List.cons_append] at hs hu ⊢
    cases hd : dstep s a0 with
    | none => simp [hd] at hs
    | some ds =>
      rcases ds with ⟨d, s'⟩
      simp only [hd] at hs hu ⊢
      cases hob : oblk s' u cx with
      | none => simp [hob] at hu
      | some ci =>
        rcases ci with ⟨c', i'⟩
        simp only [hob] at hu
        simp only [ih s' x so cx ix c' i' hs hx hob]
        cases ha : aletter c' (lcP d) with
        | none => simp [ha] at hu
        | some y =>
          simp only [ha, Option.some.injEq, Prod.mk.injEq] at hu
          rcases hu with ⟨rfl, rfl⟩
          simp

private theorem stt_app (u : List L2) : ∀ s v,
    stt s (u ++ v) = match stt s u with | some so => stt so v | none => none := by
  induction u with
  | nil => intro s v; simp [stt]
  | cons x u ih =>
    intro s v
    simp only [stt, List.cons_append]
    cases dstep s x with
    | none => rfl
    | some ds => exact ih ds.2 v

private theorem oblk_app (u : List L2) : ∀ s v so cin cv iv c iu,
    stt s u = some so → oblk so v cin = some (cv, iv) → oblk s u cv = some (c, iu) →
    oblk s (u ++ v) cin = some (c, iu ++ iv) := by
  induction u with
  | nil =>
    intro s v so cin cv iv c iu hs hv hu
    simp only [stt, Option.some.injEq] at hs; subst hs
    simp only [oblk, Option.some.injEq, Prod.mk.injEq] at hu; rcases hu with ⟨rfl, rfl⟩
    exact hv
  | cons a0 u ih =>
    intro s v so cin cv iv c iu hs hv hu
    simp only [stt, oblk, List.cons_append] at hs hu ⊢
    cases hd : dstep s a0 with
    | none => simp [hd] at hs
    | some ds =>
      rcases ds with ⟨d, s'⟩
      simp only [hd] at hs hu ⊢
      cases hob : oblk s' u cv with
      | none => simp [hob] at hu
      | some ci =>
        rcases ci with ⟨c', i'⟩
        simp only [hob] at hu
        simp only [ih s' v so cin cv iv c' i' hs hv hob]
        cases ha : aletter c' (lcP d) with
        | none => simp [ha] at hu
        | some y =>
          simp only [ha, Option.some.injEq, Prod.mk.injEq] at hu
          rcases hu with ⟨rfl, rfl⟩
          simp

private theorem stt_rep_a (n : Nat) : stt .t0 (List.replicate n .a) = some .t0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem oblk_rep_a (n : Nat) : oblk .t0 (List.replicate n .a) 1 = some (1,
    List.replicate n .b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, oblk, dstep, ih, lcP, rcP, aletter]

private theorem sweep_ovf_UU (n : Nat) (z i : List L2) (h : oim .t1 z = some (0, i)) :
    sweep (UU n z) = .next (UU 0 (List.replicate n .b ++ .a :: i ++ [.a])) := by
  have h1 : oim .t0 (.b :: z) = some (1, .a :: i) := by
    simp [oim, dstep, h, lcP, rcP, aletter]
  have hoim := oim_app (List.replicate n .a) .t0 (.b :: z) .t0 1 (.a :: i) 1 (List.replicate n .b)
    (stt_rep_a n) h1 (oblk_rep_a n)
  have hsw := sweep_ovf (List.replicate n .a ++ .b :: z) (List.replicate n .b ++ .a :: i) hoim
  simpa [UU, List.append_assoc] using hsw

/-! ## Layer 1b: Periodic emitter R11 (Tail356) -/

private def B12 : List L2 := List.replicate 12 .b
private def R11_V1 : List L2 := [.b, .b, .a, .b, .b, .a, .b, .b, .a, .b, .b, .a]
private def R11_V2 : List L2 := [.b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a]
private def R11_V3 : List L2 := [.b, .b, .a, .a, .b, .b, .b, .a, .b, .b, .a, .a]

private def R11_C0 : Nat → List L2
  | 0 => [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b]
  | q + 1 => R11_C0 q ++ B12

private def R11_C1 : Nat → List L2
  | 0 => [.b, .a, .b, .b, .a, .b, .b, .a, .b, .b, .a]
  | q + 1 => R11_C1 q ++ R11_V1

private def R11_C3 : Nat → List L2
  | 0 => [.b, .a, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  | q + 1 => R11_C3 q ++ R11_V3

private def R11_C2 : Nat → List L2
  | 0 => [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a]
  | q + 1 => R11_C3 q ++ R11_V2

private def R11_G1 : Nat → Nat
  | 0 => 1
  | q + 1 => R11_G1 q

private def R11_G4 : Nat → Nat
  | 0 => 4
  | q + 1 => R11_G4 q + (R11_G4 q + (R11_G4 q + R11_G4 q))

private def R11_G3 : Nat → Nat
  | 0 => 3
  | q + 1 => R11_G4 q + (R11_G4 q + R11_G4 q)

private def R11_G2 : Nat → Nat
  | 0 => 7
  | q + 1 => R11_G2 q + (R11_G3 q + (R11_G4 q + (R11_G4 q + (R11_G4 q + (R11_G4 q + R11_G4 q)))))

private theorem R11_tail (q : Nat) :
    emf (R11_G1 q) (R11_C0 q) = some (.t0, R11_C1 q) ∧
    emf (R11_G2 q) (R11_C1 q) = some (.t0, R11_C2 q) ∧
    emf (R11_G3 q) (R11_C2 q) = some (.t0, R11_C3 q) ∧
    emf (R11_G4 q) (R11_C3 q) = some (.t0, R11_C3 q) := by
  induction q with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ q ih =>
    rcases ih with ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact emf_then_emit h1 (rfl : actp .t0 B12 = (R11_V1, some .t0))
    · have hf : Feed (R11_C1 q) R11_V1 (R11_G2 q +
          (R11_G3 q + (R11_G4 q + (R11_G4 q + (R11_G4 q + R11_G4 q)))))
          (R11_C3 q) [.b, .b, .a, .a, .b, .b, .b, .a, .b, .b, .b, .b] :=
        Feed.step h2 (rfl : actp .t0 R11_V1 = (_, none))
          (Feed.step h3 (rfl : actp .t0 _ = (_, none))
            (Feed.step h4 (rfl : actp .t0 _ = (_, none))
              (Feed.step h4 (rfl : actp .t0 _ = (_, none))
                (Feed.step h4 (rfl : actp .t0 _ = (_, none))
                  (Feed.step h4 (rfl : actp .t0 _ = ([.b, .b, .a, .a, .b, .b, .b, .a, .b, .b, .b,
                      .b], none))
                    (Feed.nil _ _))))))
      have he := hf.emit (v2 := R11_V2) h4 (by rfl)
      simpa only [R11_G2, R11_C1, R11_C2, Nat.add_assoc] using he
    · have hf : Feed (R11_C3 q) R11_V2 (R11_G4 q + R11_G4 q) (R11_C3 q)
          [.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a] :=
        Feed.step h4 (rfl : actp .t0 R11_V2 = (_, none))
          (Feed.step h4 (rfl : actp .t0 _ = ([.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a],
              none))
            (Feed.nil _ _))
      have he := hf.emit (v2 := R11_V3) h4 (by rfl)
      simpa only [R11_G3, R11_C2, R11_C3, Nat.add_assoc] using he
    · have hf : Feed (R11_C3 q) R11_V3 (R11_G4 q + (R11_G4 q + R11_G4 q)) (R11_C3 q)
          [.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a] :=
        Feed.step h4 (rfl : actp .t0 R11_V3 = (_, none))
          (Feed.step h4 (rfl : actp .t0 _ = (_, none))
            (Feed.step h4 (rfl : actp .t0 _ = ([.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a],
                none))
              (Feed.nil _ _)))
      have he := hf.emit (v2 := R11_V3) h4 (by rfl)
      simpa only [R11_G4, R11_C3, Nat.add_assoc] using he

private theorem R11_C0_repeat (q : Nat) : R11_C0 q = List.replicate (12 * q + 11) .b := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [R11_C0, ih, B12, ← List.replicate_add]
    have heq : 12 * q + 11 + 12 = 12 * (q + 1) + 11 := by omega
    rw [heq]

private theorem R11_g4_eq (q : Nat) : R11_G4 q = 4 * 4 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih => rw [R11_G4, ih, Nat.pow_succ]; ring

private theorem R11_g3_eq (q : Nat) : R11_G3 (q + 1) = 12 * 4 ^ q := by
  rw [R11_G3, R11_g4_eq]; ring

private theorem R11_g2_eq (q : Nat) : 3 * R11_G2 (q + 1) + 2 = 92 * 4 ^ q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    have hg3 := R11_g3_eq q
    have hg4 := R11_g4_eq (q + 1)
    rw [R11_G2, hg3, hg4, Nat.pow_succ]
    omega

private theorem R11_gaps (q : Nat) :
    3 * R11_G1 (q + 1) = 3 ∧
    3 * R11_G2 (q + 1) + 2 = 92 * 4 ^ q ∧
    3 * R11_G3 (q + 1) = 36 * 4 ^ q ∧
    3 * R11_G4 (q + 1) = 48 * 4 ^ q := by
  refine ⟨?_, R11_g2_eq q, ?_, ?_⟩
  · induction q with
    | zero => rfl
    | succ q ih => exact ih
  · rw [R11_g3_eq]; ring
  · rw [R11_g4_eq, Nat.pow_succ]; ring

private def R11_H : Nat → Nat
  | 0 => 3
  | q + 1 => (R11_G4 q + (R11_G4 q + R11_G4 q)) + R11_H q

private def R11_Pre : Nat → List L2
  | 0 => [.b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a]
  | q + 1 => R11_Pre q ++ [.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a]

private def R11_Img : Nat → List L2
  | 0 => [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]
  | q + 1 => R11_Img q ++ [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]

private theorem R11_G4_H (q : Nat) : R11_G4 q = R11_H q + 1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [R11_G4, R11_H]; omega

private theorem R11_pre (q : Nat) :
    qf (R11_H q) (R11_C3 q) = some (R11_Pre q) ∧
    actp .t1 (R11_Pre q) = (R11_C3 q, some .t0) := by
  induction q with
  | zero => exact ⟨rfl, rfl⟩
  | succ q ih =>
    rcases ih with ⟨ih1, ih2⟩
    obtain ⟨_, _, _, h4⟩ := R11_tail q
    refine ⟨?_, ?_⟩
    · have hf : Feed (R11_C3 q) R11_V3 (R11_G4 q + (R11_G4 q + R11_G4 q))
          (R11_C3 q) [.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a] :=
        Feed.step h4 (rfl : actp .t0 R11_V3 = (_, none))
          (Feed.step h4 (rfl : actp .t0 _ = (_, none))
            (Feed.step h4 (rfl : actp .t0 _ = ([.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a],
                none))
              (Feed.nil _ _)))
      simp only [R11_H, R11_C3, R11_Pre]
      rw [qf_add _ (R11_H q) _ _ hf.quiet, qf_app (R11_H q) (R11_C3 q) _ _ ih1]
    · simp only [R11_Pre, R11_C3, actp_app, ih2]
      rfl

private theorem R11_img (q : Nat) :
    stt .t1 (R11_Pre q) = some .t0 ∧ oblk .t1 (R11_Pre q) 1 = some (0, R11_Img q) := by
  induction q with
  | zero => exact ⟨rfl, rfl⟩
  | succ q ih =>
    rcases ih with ⟨ih1, ih2⟩
    refine ⟨?_, ?_⟩
    · simp only [R11_Pre, stt_app, ih1]; rfl
    · simp only [R11_Pre, R11_Img]
      exact oblk_app (R11_Pre q) .t1 _ .t0 1 1 _ 0 (R11_Img q) ih1 rfl ih2

/-! ## Layer 1c: Slowed-down reduced level (Level356) -/

private def zstep (z : List L2) : Option (List L2) :=
  match actp .t1 z with
  | (z', none) => some z'
  | (z', some .t0) => some (z' ++ [.a])
  | _ => none

private def zrun : Nat → List L2 → Option (List L2)
  | 0, z => some z
  | j + 1, z =>
    match zstep z with
    | some z1 => zrun j z1
    | none => none

private theorem sweep_zstep (n : Nat) (z z' : List L2) (h : zstep z = some z') :
    sweep (UU n z) = .next (UU (n + 1) z') := by
  simp only [zstep] at h
  cases ha : actp .t1 z with | mk z1 o =>
  simp only [ha] at h
  cases o with
  | none => simp only [Option.some.injEq] at h; subst h; exact sweep_quiet n z z1 ha
  | some s =>
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h; exact sweep_grow n z z1 ha

private theorem runSim_zrun (j : Nat) : ∀ n z z',
    zrun j z = some z' → runSim j (UU n z) = .next (UU (j + n) z') := by
  induction j with
  | zero => intro n z z' h; simp only [zrun, Option.some.injEq] at h; subst h; simp [runSim]
  | succ j ih =>
    intro n z z' h
    simp only [zrun] at h
    cases hz : zstep z with
    | none => simp [hz] at h
    | some z1 =>
      simp only [hz] at h
      simp only [runSim, sweep_zstep n z z1 hz]
      rw [ih (n + 1) z1 z' h, Nat.add_right_comm, Nat.add_assoc]

private theorem zrun_add (j1 : Nat) : ∀ j2 z z1,
    zrun j1 z = some z1 → zrun (j1 + j2) z = zrun j2 z1 := by
  induction j1 with
  | zero => intro j2 z z1 h; simp only [zrun,
      Option.some.injEq] at h; subst h; simp only [Nat.zero_add]
  | succ j1 ih =>
    intro j2 z z1 h
    simp only [zrun] at h
    cases hz : zstep z with
    | none => simp [hz] at h
    | some za =>
      simp only [hz] at h
      simp only [Nat.succ_add, zrun, hz]
      exact ih j2 za z1 h

private theorem zrun_qf (m : Nat) : ∀ z z', qf m z = some z' → zrun m z = some z' := by
  induction m with
  | zero => intro z z' h; simp only [qf, zrun] at h ⊢; exact h
  | succ m ih =>
    intro z z' h
    simp only [qf] at h
    cases ha : actp .t1 z with | mk z1 o =>
    simp only [ha] at h
    cases o with
    | none => simp only [zrun, zstep, ha]; exact ih z1 z' h
    | some _ => simp at h

private theorem runSim_add (m1 : Nat) : ∀ m2 u u1,
    runSim m1 u = .next u1 → runSim (m1 + m2) u = runSim m2 u1 := by
  induction m1 with
  | zero => intro m2 u u1 h; simp only [runSim] at h; cases h; simp only [Nat.zero_add]
  | succ m1 ih =>
    intro m2 u u1 h
    simp only [runSim] at h
    cases hs : sweep u with
    | next ua =>
      simp only [hs] at h
      simp only [Nat.succ_add, runSim, hs]
      exact ih m2 ua u1 h
    | halt => simp [hs] at h
    | stuck => simp [hs] at h

private theorem zstep_cascade (dp d' z0 z0' : List L2)
    (hp : actp .t1 dp = (d', some .t0)) (hz : zstep z0 = some z0') :
    zstep (dp ++ .b :: z0) = some (d' ++ .b :: z0') := by
  simp only [zstep] at hz ⊢
  rw [actp_app, hp]
  simp only [actp]
  cases ha : actp .t1 z0 with | mk z1 o =>
  simp only [ha] at hz
  cases o with
  | none => simp only [Option.some.injEq] at hz; subst hz; rfl
  | some s =>
    cases s <;> simp only [Option.some.injEq, reduceCtorEq] at hz
    subst hz; simp [List.append_assoc]

private theorem zrun_emit (m : Nat) (d d' z0 z0' : List L2)
    (he : emf m d = some (.t0, d')) (hz : zstep z0 = some z0') :
    zrun m (d ++ .b :: z0) = some (d' ++ .b :: z0') := by
  cases m with
  | zero => simp [emf] at he
  | succ m =>
    simp only [emf] at he
    cases hq : qf m d with
    | none => simp [hq] at he
    | some dp =>
      simp only [hq, em1] at he
      cases ha : actp .t1 dp with | mk u o =>
      simp only [ha] at he
      cases o with
      | none => simp at he
      | some s =>
        cases s <;> simp only [Option.some.injEq, reduceCtorEq, Prod.mk.injEq, true_and,
          false_and] at he
        subst he
        rw [zrun_add m 1 (d ++ .b :: z0) (dp ++ .b ::
            z0) (zrun_qf m _ _ (qf_app m d dp (.b :: z0) hq))]
        simp only [zrun, zstep_cascade dp u z0 z0' ha hz]

private theorem zrun_periodic (g : Nat) (p : List L2) (hp : emf g p = some (.t0, p))
    (j : Nat) : ∀ z0 z1, zrun j z0 = some z1 → zrun (j * g) (p ++ .b :: z0) =
        some (p ++ .b :: z1) := by
  induction j with
  | zero => intro z0 z1 h; simp only [zrun, Option.some.injEq] at h; subst h; simp [zrun]
  | succ j ih =>
    intro z0 z1 h
    simp only [zrun] at h
    cases hz : zstep z0 with
    | none => simp [hz] at h
    | some za =>
      simp only [hz] at h
      rw [Nat.succ_mul, Nat.add_comm]
      rw [zrun_add g (j * g) (p ++ .b :: z0) (p ++ .b :: za) (zrun_emit g p p z0 za hp hz)]
      exact ih za z1 h

private def TT (q j : Nat) : Nat := R11_G1 q + (R11_G2 q + (R11_G3 q + j * R11_G4 q))

private theorem level_quiet (q j : Nat) (z0 z3 z1 : List L2)
    (h3 : zrun 3 z0 = some z3) (hj : zrun j z3 = some z1) :
    zrun (TT q j) (R11_C0 q ++ .b :: z0) = some (R11_C3 q ++ .b :: z1) := by
  obtain ⟨h1, h2, h3', h4⟩ := R11_tail q
  simp only [zrun] at h3
  cases ha : zstep z0 with | none => simp [ha] at h3 | some za =>
  simp only [ha] at h3
  cases hb : zstep za with | none => simp [hb] at h3 | some zb =>
  simp only [hb] at h3
  cases hc : zstep zb with | none => simp [hc] at h3 | some zc =>
  simp only [hc] at h3
  simp only [Option.some.injEq] at h3; subst h3
  unfold TT
  rw [zrun_add (R11_G1 q) _ _ _ (zrun_emit _ _ _ _ _ h1 ha)]
  rw [zrun_add (R11_G2 q) _ _ _ (zrun_emit _ _ _ _ _ h2 hb)]
  rw [zrun_add (R11_G3 q) _ _ _ (zrun_emit _ _ _ _ _ h3' hc)]
  exact zrun_periodic (R11_G4 q) (R11_C3 q) h4 j zc z1 hj

private theorem level_pre (q j : Nat) (z0 z3 z1 : List L2)
    (h3 : zrun 3 z0 = some z3) (hj : zrun j z3 = some z1) :
    runSim (TT q j + R11_H q) (UU 0 (R11_C0 q ++ .b :: z0)) =
      .next (UU (TT q j + R11_H q) (R11_Pre q ++ .b :: z1)) := by
  obtain ⟨p1, _⟩ := R11_pre q
  have h1 := level_quiet q j z0 z3 z1 h3 hj
  have h2 := zrun_qf (R11_H q) _ _ (qf_app (R11_H q) (R11_C3 q) (R11_Pre q) (.b :: z1) p1)
  have hrun := runSim_zrun (TT q j + R11_H q) 0 _ _ (by rw [zrun_add _ _ _ _ h1]; exact h2)
  simpa using hrun

private theorem level_end (q j : Nat) (z0 z3 z1 i : List L2)
    (h3 : zrun 3 z0 = some z3) (hj : zrun j z3 = some z1) (hi : oim .t0 (.b :: z1) = some (1, i)) :
    runSim (TT q j + R11_H q + 1) (UU 0 (R11_C0 q ++ .b :: z0)) =
      .next (UU 0 (List.replicate (TT q j + R11_H q) .b ++ .a :: (R11_Img q ++ i) ++ [.a])) := by
  obtain ⟨i1, i2⟩ := R11_img q
  rw [runSim_add (TT q j + R11_H q) 1 _ _ (level_pre q j z0 z3 z1 h3 hj)]
  have hsw := sweep_ovf_UU (TT q j + R11_H q) (R11_Pre q ++ .b :: z1) (R11_Img q ++ i)
    (oim_app (R11_Pre q) .t1 (.b :: z1) .t0 1 i 0 (R11_Img q) i1 hi i2)
  simp only [runSim, hsw]

private theorem level_halt (q j : Nat) (z0 z3 z1 z' : List L2)
    (h3 : zrun 3 z0 = some z3) (hj : zrun j z3 = some z1) (hz : actp .t1 z1 = (z', some .t1)) :
    runSim (TT q j + R11_H q + 1) (UU 0 (R11_C0 q ++ .b :: z0)) = .halt := by
  obtain ⟨_, p2⟩ := R11_pre q
  rw [runSim_add (TT q j + R11_H q) 1 _ _ (level_pre q j z0 z3 z1 h3 hj)]
  have hact : actp .t1 (R11_Pre q ++ .b :: z1) = (R11_C3 q ++ .b :: z', some .t1) := by
    rw [actp_app, p2]; simp [actp, hz]
  have hsw := sweep_halt (TT q j + R11_H q) (R11_Pre q ++ .b :: z1) (R11_C3 q ++ .b :: z') hact
  simp only [runSim, hsw]

private theorem kform (q j : Nat) :
    3 * (TT (q + 1) j + R11_H (q + 1)) + 2 = (3 * j + 11) * 4 ^ (q + 2) := by
  unfold TT
  obtain ⟨e1, e2, e3, e4⟩ := R11_gaps q
  have e5 := R11_G4_H (q + 1)
  have hpow : 4 ^ (q + 2) = 16 * 4 ^ q := by rw [Nat.pow_add, Nat.mul_comm]
  have e6 : 3 * (j * R11_G4 (q + 1)) = 48 * (j * 4 ^ q) := by
    calc
      3 * (j * R11_G4 (q + 1)) = j * (3 * R11_G4 (q + 1)) := by ring
      _ = j * (48 * 4 ^ q) := by rw [e4]
      _ = 48 * (j * 4 ^ q) := by ring
  rw [hpow]
  have hrhs : (3 * j + 11) * (16 * 4 ^ q) = 48 * (j * 4 ^ q) + 176 * 4 ^ q := by ring
  rw [hrhs]
  omega


/-! ## Layer 2a: Symbolic run counts & verified program evaluator (Sym356) -/

private def rep (u : List L2) : Nat → List L2
  | 0 => []
  | n + 1 => u ++ rep u n

private theorem rep_add (u : List L2) (a b : Nat) : rep u (a + b) = rep u a ++ rep u b := by
  induction a with
  | zero => simp [rep]
  | succ a ih => simp [rep, Nat.succ_add, ih, List.append_assoc]

private theorem rep_snoc (u : List L2) (n : Nat) : rep u n ++ u = rep u (n + 1) := by
  induction n with
  | zero => simp [rep]
  | succ n ih => simp [rep, List.append_assoc, ih]

private inductive VarExpr where
  | const (k : Nat)
  | varPlus (idx : Nat) (k : Nat)

private def varExprBeq : VarExpr → VarExpr → Bool
  | .const a, .const b => Nat.beq a b
  | .varPlus i1 k1, .varPlus i2 k2 => Nat.beq i1 i2 && Nat.beq k1 k2
  | _, _ => false

private theorem varExprBeq_eq {a b : VarExpr} : varExprBeq a b = true → a = b := by
  cases a <;> cases b <;> simp [varExprBeq]

private def getAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, i + 1 => getAt xs i

private theorem getAt_out {xs : List Nat} {i : Nat} (h : xs.length ≤ i) : getAt xs i = 0 := by
  induction xs generalizing i with
  | nil => simp [getAt]
  | cons x xs ih =>
    cases i with
    | zero => simp at h
    | succ i => exact ih (by simp at h; omega)

private def evalVar (vars : List Nat) : VarExpr → Nat
  | .const k => k
  | .varPlus idx k => k + getAt vars idx

private def varDec : VarExpr → Option VarExpr
  | .const (k + 1) => some (.const k)
  | .varPlus idx (k + 1) => some (.varPlus idx k)
  | _ => none

private theorem evalVar_varDec {cnt cnt' : VarExpr} (h : varDec cnt = some cnt') (vars : List Nat) :
    evalVar vars cnt = evalVar vars cnt' + 1 := by
  cases cnt with
  | const k =>
    cases k with
    | zero => simp [varDec] at h
    | succ k => simp only [varDec, Option.some.injEq] at h; subst h; rfl
  | varPlus idx k =>
    cases k with
    | zero => simp [varDec] at h
    | succ k => simp only [varDec, Option.some.injEq] at h; subst h; simp [evalVar]; omega

private inductive SymItem where
  | lit (w : List L2)
  | run (u : List L2) (cnt : VarExpr)

private def symItemBeq : SymItem → SymItem → Bool
  | .lit w1, .lit w2 => l2ListBeq w1 w2
  | .run u1 c1, .run u2 c2 => l2ListBeq u1 u2 && varExprBeq c1 c2
  | _, _ => false

private theorem symItemBeq_eq {a b : SymItem} : symItemBeq a b = true → a = b := by
  cases a <;> cases b <;> simp only [symItemBeq, Bool.false_eq_true, false_implies,
    SymItem.lit.injEq, SymItem.run.injEq]
  · exact l2ListBeq_eq
  · simp only [Bool.and_eq_true]; rintro ⟨h1, h2⟩; exact ⟨l2ListBeq_eq h1, varExprBeq_eq h2⟩

private def symListBeq : List SymItem → List SymItem → Bool
  | [], [] => true
  | x :: xs, y :: ys => if symItemBeq x y then symListBeq xs ys else false
  | _, _ => false

private theorem symListBeq_eq {xs ys : List SymItem} : symListBeq xs ys = true → xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [symListBeq]
  | cons x xs ih =>
    cases ys with
    | nil => simp [symListBeq]
    | cons y ys =>
      simp only [symListBeq]
      intro h
      cases hx : symItemBeq x y
      · simp [hx] at h
      · simp only [hx, ite_true] at h
        rw [symItemBeq_eq hx, ih h]

private def den (vars : List Nat) : List SymItem → List L2
  | [] => []
  | .lit w :: rest => w ++ den vars rest
  | .run u cnt :: rest => rep u (evalVar vars cnt) ++ den vars rest

private theorem den_append (vars : List Nat) (a b : List SymItem) :
    den vars (a ++ b) = den vars a ++ den vars b := by
  induction a with
  | nil => rfl
  | cons x a ih =>
    cases x <;> simp [den, ih, List.append_assoc]

private def pushLit (w : List L2) : List SymItem → List SymItem
  | [] => if w.isEmpty then [] else [.lit w]
  | .lit w' :: rest => if w.isEmpty then .lit w' :: rest else .lit (w ++ w') :: rest
  | x :: rest => if w.isEmpty then x :: rest else .lit w :: x :: rest

private theorem den_pushLit (vars : List Nat) (w : List L2) (xs : List SymItem) :
    den vars (pushLit w xs) = w ++ den vars xs := by
  cases xs with
  | nil => cases w <;> simp [pushLit, den]
  | cons x xs =>
    cases x <;> cases w <;> simp [pushLit, den, List.append_assoc]

private def appendLit (a : List L2) : List SymItem → List SymItem
  | [] => if a.isEmpty then [] else [.lit a]
  | [.lit w] => if a.isEmpty then [.lit w] else [.lit (w ++ a)]
  | x :: xs => x :: appendLit a xs

private theorem den_appendLit (vars : List Nat) (a : List L2) (xs : List SymItem) :
    den vars (appendLit a xs) = den vars xs ++ a := by
  induction xs with
  | nil => cases a <;> simp [appendLit, den]
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases x <;> cases a <;> simp [appendLit, den]
    | cons y ys =>
      cases x <;> simp [appendLit, den, ih, List.append_assoc]

private def appendSym : List SymItem → List SymItem → List SymItem
  | [], b => b
  | [.lit w], b => pushLit w b
  | x :: xs, b => x :: appendSym xs b

private theorem den_appendSym (vars : List Nat) (a b : List SymItem) :
    den vars (appendSym a b) = den vars a ++ den vars b := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil =>
      cases x with
      | lit w => simp [appendSym, den, den_pushLit]
      | run u c => simp [appendSym, den]
    | cons y ys =>
      cases x <;> simp [appendSym, den, ih, List.append_assoc]

private theorem actp_rep (u u' : List L2) (s : St) (h : actp s u = (u', some s)) :
    ∀ n, actp s (rep u n) = (rep u' n, some s) := by
  intro n
  induction n with
  | zero => simp [rep, actp]
  | succ n ih => simp [rep, actp_app, h, ih]

private def pushRun (u : List L2) (cnt : VarExpr) (rest : List SymItem) : List SymItem :=
  match cnt with
  | .const 0 => rest
  | _ => .run u cnt :: rest

private theorem den_pushRun (vars : List Nat) (u : List L2) (cnt : VarExpr) (rest : List SymItem) :
    den vars (pushRun u cnt rest) = rep u (evalVar vars cnt) ++ den vars rest := by
  cases cnt with
  | const k => cases k <;> simp [pushRun, den, evalVar, rep]
  | varPlus idx k => simp [pushRun, den, evalVar]

private def sactp : Nat → St → List SymItem → Option (List SymItem × Option St)
  | 0, _, _ => none
  | _, s, [] => some ([], some s)
  | f + 1, s, .lit w :: rest =>
    match actp s w with
    | (w', some s') =>
      match sactp f s' rest with
      | some (r', o) => some (pushLit w' r', o)
      | none => none
    | (w', none) => some (pushLit w' rest, none)
  | f + 1, s, .run u cnt :: rest =>
    match actp s u with
    | (u', some s') =>
      if stBeq s s' then
        match sactp f s rest with
        | some (r', o) =>
          match cnt with
          | .const 0 => some (r', o)
          | _ => some (.run u' cnt :: r', o)
        | none => none
      else
        match varDec cnt with
        | none => none
        | some cnt' =>
          match sactp f s' (pushRun u cnt' rest) with
          | some (r', o) => some (pushLit u' r', o)
          | none => none
    | (u', none) =>
      match varDec cnt with
      | none => none
      | some cnt' => some (pushLit u' (pushRun u cnt' rest), none)

private theorem rep_add_one (u : List L2) (n : Nat) : rep u (n + 1) = u ++ rep u n := rfl

private theorem sactp_sound (f : Nat) : ∀ (s : St) (w w' : List SymItem) (o : Option St),
    sactp f s w = some (w', o) → ∀ vars, actp s (den vars w) = (den vars w', o) := by
  induction f with
  | zero => intro s w w' o h; cases w <;> simp [sactp] at h
  | succ f ih =>
    intro s w w' o h vars
    cases w with
    | nil =>
      simp only [sactp, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | cons item rest =>
      cases item with
      | lit lw =>
        simp only [sactp] at h
        simp only [den, actp_app]
        cases ha : actp s lw with | mk lw' os =>
        simp only [ha] at h
        cases os with
        | none =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          simp [den_pushLit]
        | some s' =>
          simp only at h
          cases hs : sactp f s' rest with
          | none => simp [hs] at h
          | some res =>
            rcases res with ⟨r', o'⟩
            simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            simp [ih s' rest r' o' hs vars, den_pushLit]
      | run u cnt =>
        simp only [sactp] at h
        cases ha : actp s u with | mk u' os =>
        simp only [ha] at h
        cases os with
        | none =>
          cases hd : varDec cnt with
          | none => simp [hd] at h
          | some cnt' =>
            simp only [hd, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [den, evalVar_varDec hd vars, rep_add_one, den_pushLit, den_pushRun]
            rw [List.append_assoc, actp_app, ha]
        | some s' =>
          cases heq : stBeq s s' with
          | true =>
            have hs' := stBeq_eq heq; subst hs'
            simp only [heq, ↓reduceIte] at h
            cases hs : sactp f s rest with
            | none => simp [hs] at h
            | some res =>
              rcases res with ⟨r', o'⟩
              simp only [hs] at h
              have hrep := actp_rep u u' s ha (evalVar vars cnt)
              cases cnt with
              | const k =>
                cases k with
                | zero =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  simpa [den, evalVar, rep] using ih s rest r' o' hs vars
                | succ k =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  simp [den, actp_app, hrep, ih s rest r' o' hs vars]
              | varPlus idx k =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                simp [den, actp_app, hrep, ih s rest r' o' hs vars]
          | false =>
            simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
            cases hd : varDec cnt with
            | none => simp [hd] at h
            | some cnt' =>
              simp only [hd] at h
              cases hs : sactp f s' (pushRun u cnt' rest) with
              | none => simp [hs] at h
              | some res =>
                rcases res with ⟨r', o'⟩
                simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl⟩
                have hih := ih s' (pushRun u cnt' rest) r' o' hs vars
                rw [den_pushRun] at hih
                rw [den, evalVar_varDec hd vars, rep_add_one, List.append_assoc, actp_app, ha]
                simp [hih, den_pushLit]

private def szstep (f : Nat) (w : List SymItem) : Option (List SymItem) :=
  match sactp f .t1 w with
  | some (w', none) => some w'
  | some (w', some .t0) => some (appendLit [.a] w')
  | _ => none

private def szrun (f : Nat) : Nat → List SymItem → Option (List SymItem)
  | 0, w => some w
  | m + 1, w =>
    match szstep f w with
    | some w1 => szrun f m w1
    | none => none

private theorem szstep_sound
    (f : Nat) (w w' : List SymItem) (h : szstep f w = some w') (vars : List Nat) :
    zstep (den vars w) = some (den vars w') := by
  simp only [szstep] at h
  cases hs : sactp f .t1 w with
  | none => simp [hs] at h
  | some res =>
    rcases res with ⟨w1, o⟩
    simp only [hs] at h
    have ha := sactp_sound f .t1 w w1 o hs vars
    cases o with
    | none => simp only [Option.some.injEq] at h; subst h; simp [zstep, ha]
    | some s =>
      cases s <;> simp only [Option.some.injEq, reduceCtorEq] at h
      subst h; simp [zstep, ha, den_appendLit]

private theorem szrun_sound (f m : Nat) : ∀ w w',
    szrun f m w = some w' → ∀ vars, zrun m (den vars w) = some (den vars w') := by
  induction m with
  | zero => intro w w' h vars; simp only [szrun, Option.some.injEq] at h; subst h; rfl
  | succ m ih =>
    intro w w' h vars
    simp only [szrun] at h
    cases hz : szstep f w with
    | none => simp [hz] at h
    | some w1 =>
      simp only [hz] at h
      simp only [zrun, szstep_sound f w w1 hz vars]
      exact ih w1 w' h vars

private def ocons (o : Option St) (l : List St) : List St :=
  match o with | some s => s :: l | none => l

private def thru : List St → List L2 → List L2 × List St
  | [], v => (v, [])
  | s :: l', v =>
    let r1 := actp s v
    let r2 := thru l' r1.1
    (r2.1, ocons r1.2 r2.2)

private def srun : Nat → List L2 → List L2 × List St
  | 0, u => (u, [])
  | m + 1, u =>
    let r1 := actp .t1 u
    let r2 := srun m r1.1
    (r2.1, ocons r1.2 r2.2)

private theorem thru_nil (l : List St) : thru l [] = ([], l) := by
  induction l with
  | nil => rfl
  | cons s l ih => simp [thru, actp, ih, ocons]

private theorem thru_app (l : List St) : ∀ v w,
    thru l (v ++ w) =
      let rv := thru l v
      let rw_res := thru rv.2 w
      (rv.1 ++ rw_res.1, rw_res.2) := by
  induction l with
  | nil => intro v w; simp [thru]
  | cons s l ih =>
    intro v w
    simp only [thru, actp_app]
    cases h1 : actp s v with | mk v1 o =>
    cases o with
    | none => simp only [ih, ocons]
    | some t => simp only [ih, ocons, thru]

private theorem srun_app (m : Nat) : ∀ u v,
    srun m (u ++ v) =
      let ru := srun m u
      let rv := thru ru.2 v
      (ru.1 ++ rv.1, rv.2) := by
  induction m with
  | zero => intro u v; simp [srun, thru]
  | succ m ih =>
    intro u v
    simp only [srun, actp_app]
    cases h1 : actp .t1 u with | mk u1 o =>
    cases o with
    | none => simp only [ih, ocons]
    | some t => simp only [ih, ocons, thru]

private theorem srun_add (a : Nat) : ∀ b u,
    srun (a + b) u =
      let r1 := srun a u
      let r2 := srun b r1.1
      (r2.1, r1.2 ++ r2.2) := by
  induction a with
  | zero => intro b u; simp [srun]
  | succ a ih =>
    intro b u
    simp only [Nat.succ_add, srun, ih]
    cases (actp .t1 u).2 <;> simp [ocons]

private theorem thru_rep (l : List St) (v : List L2) (h : thru l v = (v, l)) :
    ∀ c, thru l (rep v c) = (rep v c, l) := by
  intro c
  induction c with
  | zero => simp [rep, thru_nil]
  | succ c ih => simp [rep, thru_app, h, ih]

private theorem srun_zrun (m : Nat) : ∀ z z', srun m z = (z', []) → zrun m z = some z' := by
  induction m with
  | zero => intro z z' h; simp only [srun, Prod.mk.injEq] at h; cases h.1; rfl
  | succ m ih =>
    intro z z' h
    simp only [srun] at h
    cases h1 : actp .t1 z with | mk z1 o =>
    simp only [h1] at h
    cases o with
    | some _ => simp [ocons] at h
    | none =>
      simp only [ocons] at h
      have hsub := congrArg Prod.fst h
      have hnil := congrArg Prod.snd h
      simp only at hsub hnil
      simp only [zrun, zstep, h1]
      exact ih z1 z' (Prod.ext hsub hnil)

private theorem front_gen (p : Nat) (r : List L2) (l : List St) (fWord u v x : List L2)
    (hr : srun p r = (r, l)) (hf : thru l (fWord ++ u) = (v ++ fWord, [])) (hv : thru l v = (v,
        l)) :
    ∀ j c, srun (p * j) (r ++ rep v c ++ fWord ++ rep u j ++ x) =
      (r ++ rep v (c + j) ++ fWord ++ x, []) := by
  intro j
  induction j with
  | zero => intro c; simp [srun, rep]
  | succ j ih =>
    intro c
    have he : srun p (r ++ rep v c ++ fWord ++ rep u (j + 1) ++ x) =
        (r ++ rep v (c + 1) ++ fWord ++ rep u j ++ x, []) := by
      have hfu : r ++ rep v c ++ fWord ++ rep u (j + 1) ++ x =
          r ++ (rep v c ++ ((fWord ++ u) ++ (rep u j ++ x))) := by
        simp [rep, List.append_assoc]
      rw [hfu, srun_app, hr]
      simp only [thru_app, thru_rep l v hv c, hf, thru]
      rw [← rep_snoc v c]
      simp [List.append_assoc]
    rw [Nat.mul_succ, Nat.add_comm (p * j) p, srun_add, he]
    have ih' := ih (c + 1)
    rw [show c + 1 + j = c + (j + 1) by omega] at ih'
    simpa [List.append_assoc] using ih'

private def ssrun (f : Nat) : Nat → List SymItem → Option (List SymItem × List St)
  | 0, w => some (w, [])
  | m + 1, w =>
    match sactp f .t1 w with
    | some (w1, o) =>
      match ssrun f m w1 with
      | some (w', l) => some (w', ocons o l)
      | none => none
    | none => none

private theorem ssrun_sound (f m : Nat) : ∀ w w' l,
    ssrun f m w = some (w', l) → ∀ vars, srun m (den vars w) = (den vars w', l) := by
  induction m with
  | zero => intro w w' l h vars; simp only [ssrun, Option.some.injEq,
      Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
  | succ m ih =>
    intro w w' l h vars
    simp only [ssrun] at h
    cases hs1 : sactp f .t1 w with
    | none => simp [hs1] at h
    | some r1 =>
      rcases r1 with ⟨w1, o⟩
      simp only [hs1] at h
      cases hs2 : ssrun f m w1 with
      | none => simp [hs2] at h
      | some r2 =>
        rcases r2 with ⟨w2, l2⟩
        simp only [hs2, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [srun, sactp_sound f .t1 w w1 o hs1 vars, ih w1 w2 l2 hs2 vars]

private def splitAtRun :
    Nat → Nat → List SymItem → Option (List SymItem × List L2 × List L2 × VarExpr × List SymItem)
  | 0, 0, .run u cnt :: rest => some ([], [], u, cnt, rest)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | pos + 1, fLen, x :: xs =>
    match pos, x, xs with
    | 0, .lit w, .run u cnt :: rest =>
      if w.length >= fLen then
        let k := w.length - fLen
        let wPrefix := w.take k
        let fWord := w.drop k
        let rs := if wPrefix.isEmpty then [] else [.lit wPrefix]
        some (rs, fWord, u, cnt, rest)
      else none
    | _, _, _ =>
      match splitAtRun pos fLen xs with
      | some (rs, fWord, u, cnt, rest) => some (x :: rs, fWord, u, cnt, rest)
      | none => none

private theorem splitAtRun_sound : ∀ pos fLen w rs fWord u cnt rest,
    splitAtRun pos fLen w = some (rs, fWord, u, cnt, rest) →
    ∀ vars, den vars w = den vars rs ++ fWord ++ rep u (evalVar vars cnt) ++ den vars rest := by
  intro pos
  induction pos with
  | zero =>
    intro fLen w rs fWord u cnt rest h vars
    cases fLen with
    | zero =>
      cases w with
      | nil => simp [splitAtRun] at h
      | cons x xs =>
        cases x with
        | lit _ => simp [splitAtRun] at h
        | run u0 c0 =>
          simp only [splitAtRun, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          simp [den]
    | succ f' => simp [splitAtRun] at h
  | succ pos ih =>
    intro fLen w rs fWord u cnt rest h vars
    cases w with
    | nil => simp [splitAtRun] at h
    | cons x xs =>
      cases pos with
      | zero =>
        cases x with
        | run u0 cnt0 =>
          simp only [splitAtRun] at h
          cases hs : splitAtRun 0 fLen xs with
          | none => simp [hs] at h
          | some q =>
            rcases q with ⟨rs0, fw0, u1, cnt1, rest0⟩
            simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
            have hsub := ih fLen xs rs0 fw0 u1 cnt1 rest0 hs vars
            simp [den, hsub, List.append_assoc]
        | lit lw =>
          cases xs with
          | nil => simp [splitAtRun] at h
          | cons y ys =>
            cases y with
            | lit ly =>
              simp only [splitAtRun] at h
              cases hs : splitAtRun 0 fLen (.lit ly :: ys) with
              | none => simp at h
              | some q => simp [splitAtRun] at hs
            | run u1 cnt1 =>
              simp only [splitAtRun] at h
              split at h
              · simp only [Option.some.injEq, Prod.mk.injEq] at h
                rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
                have htake : lw.take (lw.length - fLen) ++ lw.drop (lw.length - fLen) = lw :=
                  List.take_append_drop _ lw
                cases hw : (lw.take (lw.length - fLen)).isEmpty
                · simp [den, List.append_assoc, htake]
                · have hnil : lw.take (lw.length - fLen) = [] := List.isEmpty_iff.mp hw
                  rw [hnil, List.nil_append] at htake
                  simp [den, htake, List.append_assoc]
              · simp at h
      | succ pos' =>
        simp only [splitAtRun] at h
        cases hs : splitAtRun (pos' + 1) fLen xs with
        | none => simp [hs] at h
        | some q =>
          rcases q with ⟨rs0, fw0, u1, cnt1, rest0⟩
          simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl, rfl, rfl, rfl⟩
          have hsub := ih fLen xs rs0 fw0 u1 cnt1 rest0 hs vars
          cases x <;> simp [den, hsub, List.append_assoc]

private inductive SymOp where
  | lit (n : Nat)
  | front (pos : Nat) (fLen : Nat) (p : Nat) (v : List L2)

private def frontMid (v : List L2) (cnt : VarExpr) : List SymItem :=
  match cnt with | .const 0 => [] | _ => [.run v cnt]

private def frontTail (fWord : List L2) (rest : List SymItem) : List SymItem :=
  if fWord.isEmpty then rest else pushLit fWord rest

private def stepOp (f : Nat) (w : List SymItem) : SymOp → Option (List SymItem × Nat × VarExpr)
  | .lit n =>
    match szrun f n w with
    | some w' => some (w', n, .const 1)
    | none => none
  | .front pos fLen p v =>
    match splitAtRun pos fLen w with
    | some (rs, fWord, u, cnt, rest) =>
      match ssrun f p rs with
      | some (r1, l) =>
        if symListBeq r1 rs then
          let rFU := thru l (fWord ++ u)
          if rFU.2.isEmpty && l2ListBeq rFU.1 (v ++ fWord) then
            let rV := thru l v
            if l2ListBeq rV.1 v && stListBeq rV.2 l then
              some (appendSym rs (frontMid v cnt ++ frontTail fWord rest), p, cnt)
            else none
          else none
        else none
      | none => none
    | none => none

private def evalTerms (vars : List Nat) : List (Nat × VarExpr) → Nat
  | [] => 0
  | (c, e) :: rest => c * evalVar vars e + evalTerms vars rest

private theorem den_front_rhs
    (vars : List Nat) (rs rest : List SymItem) (fWord v : List L2) (cnt : VarExpr) :
    den vars (appendSym rs (frontMid v cnt ++ frontTail fWord rest)) =
      den vars rs ++ rep v (evalVar vars cnt) ++ fWord ++ den vars rest := by
  rw [den_appendSym, den_append]
  have hmid : den vars (frontMid v cnt) = rep v (evalVar vars cnt) := by
    cases cnt with
    | const k => cases k <;> simp [frontMid, den, evalVar, rep]
    | varPlus idx k => simp [frontMid, den, evalVar]
  have htail : den vars (frontTail fWord rest) = fWord ++ den vars rest := by
    simp only [frontTail]
    cases he : fWord.isEmpty
    · simp [den_pushLit]
    · have hf0 : fWord = [] := List.isEmpty_iff.mp he
      simp [hf0]
  rw [hmid, htail, List.append_assoc, List.append_assoc]

private theorem stepOp_sound (f : Nat) (w w' : List SymItem) (op : SymOp) (c : Nat) (e : VarExpr)
    (h : stepOp f w op = some (w', c, e)) (vars : List Nat) :
    zrun (c * evalVar vars e) (den vars w) = some (den vars w') := by
  cases op with
  | lit n =>
    simp only [stepOp] at h
    cases hz : szrun f n w with
    | none => simp [hz] at h
    | some w1 =>
      simp only [hz, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl, rfl⟩
      simpa [evalVar] using szrun_sound f n w w1 hz vars
  | front pos fLen p v =>
    simp only [stepOp] at h
    cases hsp : splitAtRun pos fLen w with
    | none => simp [hsp] at h
    | some q =>
      rcases q with ⟨rs, fWord, u, cnt, rest⟩
      simp only [hsp] at h
      cases hss : ssrun f p rs with
      | none => simp [hss] at h
      | some r1l =>
        rcases r1l with ⟨r1, l⟩
        simp only [hss] at h
        cases hrs : symListBeq r1 rs with
        | false => simp [hrs] at h
        | true =>
          simp only [hrs, ↓reduceIte] at h
          cases hfu :
              (thru l (fWord ++ u)).2.isEmpty && l2ListBeq (thru l (fWord ++ u)).1 (v ++ fWord) with
          | false => simp [hfu] at h
          | true =>
            simp only [hfu, ↓reduceIte] at h
            cases hv : l2ListBeq (thru l v).1 v && stListBeq (thru l v).2 l with
            | false => simp [hv] at h
            | true =>
              simp only [hv, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl, rfl⟩
              have hr1 : r1 = rs := symListBeq_eq hrs
              subst hr1
              have hss_den : srun p (den vars r1) = (den vars r1, l) :=
                  ssrun_sound f p r1 r1 l hss vars
              rw [Bool.and_eq_true] at hfu hv
              have hfu1 : (thru l (fWord ++ u)).1 = v ++ fWord := l2ListBeq_eq hfu.2
              have hfu2 : (thru l (fWord ++ u)).2 = [] := List.isEmpty_iff.mp hfu.1
              have hfu_eq : thru l (fWord ++ u) = (v ++ fWord, []) := Prod.ext hfu1 hfu2
              have hv_eq : thru l v = (v, l) := Prod.ext (l2ListBeq_eq hv.1) (stListBeq_eq hv.2)
              have hfg :=
                  front_gen p (den vars r1) l fWord u v (den vars rest) hss_den hfu_eq hv_eq
                  (evalVar vars cnt) 0
              have hz :=
                  srun_zrun (p * evalVar vars cnt) _ _ (by simpa [rep, List.append_assoc] using hfg)
              have hden_w := splitAtRun_sound pos fLen w r1 fWord u cnt rest hsp vars
              rw [den_front_rhs, hden_w]
              simpa [List.append_assoc] using hz

private def runProg
    (f : Nat) : List SymOp → List SymItem → Option (List SymItem × List (Nat × VarExpr))
  | [], w => some (w, [])
  | op :: ops, w =>
    match stepOp f w op with
    | some (w1, c, e) =>
      match runProg f ops w1 with
      | some (w2, ts) => some (w2, (c, e) :: ts)
      | none => none
    | none => none

private theorem runProg_sound (f : Nat) (ops : List SymOp) : ∀ w w' ts,
    runProg f ops w = some (w',
        ts) → ∀ vars, zrun (evalTerms vars ts) (den vars w) = some (den vars w') := by
  induction ops with
  | nil => intro w w' ts h vars; simp only [runProg, Option.some.injEq,
      Prod.mk.injEq] at h; rcases h with ⟨rfl, rfl⟩; rfl
  | cons op ops ih =>
    intro w w' ts h vars
    simp only [runProg] at h
    cases hs : stepOp f w op with
    | none => simp [hs] at h
    | some res1 =>
      rcases res1 with ⟨w1, c, e⟩
      simp only [hs] at h
      cases hr : runProg f ops w1 with
      | none => simp [hr] at h
      | some res2 =>
        rcases res2 with ⟨w2, ts2⟩
        simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
        rcases h with ⟨rfl, rfl⟩
        simp only [evalTerms]
        rw [zrun_add (c * evalVar vars e) (evalTerms vars ts2) _ _
            (stepOp_sound f w w1 op c e hs vars)]
        exact ih w1 w2 ts2 hr vars

/-! ## Level-end image on SymItem (`soim`) and symbolic equivalence (`normSym`) -/

private theorem stt_rep (s : St) (u : List L2) (h : stt s u = some s) :
    ∀ n, stt s (rep u n) = some s := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [rep, stt_app, h, ih]

private theorem oblk_rep (s : St) (u u' : List L2) (c : Fin 2)
    (hs : stt s u = some s) (hu : oblk s u c = some (c, u')) :
    ∀ n, oblk s (rep u n) c = some (c, rep u' n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => exact oblk_app u s (rep u n) s c c (rep u' n) c u' hs ih hu

private def soim : Nat → St → List SymItem → Option (Fin 2 × List SymItem)
  | 0, _, _ => none
  | _ + 1, s, [] => match s with | .t2 => some (0, []) | _ => none
  | f + 1, s, .lit w :: rest =>
    match stt s w with
    | none => none
    | some so =>
      match soim f so rest with
      | none => none
      | some (cx, ix) =>
        match oblk s w cx with
        | none => none
        | some (c, iw) => some (c, pushLit iw ix)
  | f + 1, s, .run u cnt :: rest =>
    match stt s u with
    | none => none
    | some so =>
      if stBeq s so then
        match soim f s rest with
        | none => none
        | some (cx, ix) =>
          match oblk s u cx with
          | none => none
          | some (c1, uA) =>
            if c1 == cx then some (cx, pushRun uA cnt ix)
            else
              match varDec cnt with
              | none => none
              | some cnt' =>
                match oblk s u c1 with
                | none => none
                | some (c2, uB) =>
                  if c2 == c1 then some (c1, pushRun uB cnt' (pushLit uA ix))
                  else none
      else
        match varDec cnt with
        | none => none
        | some cnt' => soim f s (.lit u :: pushRun u cnt' rest)

private theorem soim_sound (f : Nat) : ∀ s w c i,
    soim f s w = some (c, i) → ∀ vars, oim s (den vars w) = some (c, den vars i) := by
  induction f with
  | zero => intro s w c i h; simp [soim] at h
  | succ f ih =>
    intro s w c i h vars
    cases w with
    | nil =>
      cases s <;> simp only [soim, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl
    | cons item rest =>
      cases item with
      | lit lw =>
        simp only [soim] at h
        cases hs : stt s lw with
        | none => simp [hs] at h
        | some so =>
          simp only [hs] at h
          cases ho : soim f so rest with
          | none => simp [ho] at h
          | some cxix =>
            rcases cxix with ⟨cx, ix⟩
            simp only [ho] at h
            cases hob : oblk s lw cx with
            | none => simp [hob] at h
            | some ciw =>
              rcases ciw with ⟨c', iw⟩
              simp only [hob, Option.some.injEq, Prod.mk.injEq] at h
              rcases h with ⟨rfl, rfl⟩
              simpa [den, den_pushLit] using
                oim_app lw s (den vars rest) so cx (den vars ix) c' iw hs
                    (ih so rest cx ix ho vars) hob
      | run u cnt =>
        simp only [soim] at h
        cases hs : stt s u with
        | none => simp [hs] at h
        | some so =>
          simp only [hs] at h
          cases heq : stBeq s so with
          | true =>
            have hso := stBeq_eq heq; subst hso
            simp only [heq, ↓reduceIte] at h
            cases ho : soim f s rest with
            | none => simp [ho] at h
            | some cxix =>
              rcases cxix with ⟨cx, ix⟩
              simp only [ho] at h
              cases hob1 : oblk s u cx with
              | none => simp [hob1] at h
              | some cuA =>
                rcases cuA with ⟨c1, uA⟩
                simp only [hob1] at h
                cases hec : (c1 == cx) with
                | true =>
                  have hc1 : c1 = cx := beq_iff_eq.mp hec
                  rw [hc1] at hob1
                  simp only [hec, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                  rcases h with ⟨rfl, rfl⟩
                  simpa [den, den_pushRun] using
                    oim_app (rep u (evalVar vars cnt)) s (den vars rest) s cx (den vars ix) cx
                        (rep uA (evalVar vars cnt))
                      (stt_rep s u hs _) (ih s rest cx ix ho vars) (oblk_rep s u uA cx hs hob1 _)
                | false =>
                  simp only [hec, Bool.false_eq_true, ↓reduceIte] at h
                  cases hd : varDec cnt with
                  | none => simp [hd] at h
                  | some cnt' =>
                    simp only [hd] at h
                    cases hob2 : oblk s u c1 with
                    | none => simp [hob2] at h
                    | some cuB =>
                      rcases cuB with ⟨c2, uB⟩
                      simp only [hob2] at h
                      cases hec2 : (c2 == c1) with
                      | false => simp [hec2] at h
                      | true =>
                        have hc2 : c2 = c1 := beq_iff_eq.mp hec2
                        rw [hc2] at hob2
                        simp only [hec2, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
                        rcases h with ⟨rfl, rfl⟩
                        have hih := ih s rest cx ix ho vars
                        have hstt : stt s (rep u (evalVar vars cnt') ++ u) = some s := by
                          rw [stt_app, stt_rep s u hs _]; exact hs
                        have hob_full : oblk s (rep u (evalVar vars cnt') ++ u) cx =
                            some (c1, rep uB (evalVar vars cnt') ++ uA) :=
                          oblk_app (rep u (evalVar vars cnt')) s u s cx c1 uA c1
                              (rep uB (evalVar vars cnt'))
                            (stt_rep s u hs _) hob1 (oblk_rep s u uB c1 hs hob2 _)
                        have hoim :=
                            oim_app _ s (den vars rest) s cx (den vars ix) c1 _ hstt hih hob_full
                        rw [rep_snoc] at hoim
                        rw [den, evalVar_varDec hd vars, den_pushRun, den_pushLit]
                        simpa [List.append_assoc] using hoim
          | false =>
            simp only [heq, Bool.false_eq_true, ↓reduceIte] at h
            cases hd : varDec cnt with
            | none => simp [hd] at h
            | some cnt' =>
              simp only [hd] at h
              have hih := ih s (.lit u :: pushRun u cnt' rest) c i h vars
              rw [den, evalVar_varDec hd vars, rep_add_one]
              simpa [den, den_pushRun, List.append_assoc] using hih

private def normItem : SymItem → List SymItem
  | .lit w => if w.isEmpty then [] else [.lit w]
  | .run u (.const k) => let w := rep u k; if w.isEmpty then [] else [.lit w]
  | .run u (.varPlus idx k) =>
    let pref := rep u k
    let head := if pref.isEmpty then [] else [.lit pref]
    head ++ [.run u (.varPlus idx 0)]

private def normSym : List SymItem → List SymItem
  | [] => []
  | .lit w :: xs => pushLit w (normSym xs)
  | .run u cnt :: xs => appendSym (normItem (.run u cnt)) (normSym xs)

private theorem den_normSym (vars : List Nat) (w : List SymItem) :
    den vars (normSym w) = den vars w := by
  induction w with
  | nil => rfl
  | cons item xs ih =>
    cases item with
    | lit lw => simp [normSym, den_pushLit, ih, den]
    | run u cnt =>
      cases cnt with
      | const k =>
        simp only [normSym, normItem, den_appendSym, ih, den, evalVar]
        cases h : (rep u k).isEmpty
        · simp [den]
        · have he := List.isEmpty_iff.mp h; simp [den, he]
      | varPlus idx k =>
        simp only [normSym, normItem, den_appendSym, ih, den, evalVar, den_append]
        have hrep : k + getAt vars idx = k + (0 + getAt vars idx) := by omega
        rw [hrep, rep_add u k (0 + getAt vars idx)]
        cases h : (rep u k).isEmpty
        · simp [den, List.append_assoc]
        · have he := List.isEmpty_iff.mp h; simp [den, he]

private def symDenEq (a b : List SymItem) : Bool :=
  symListBeq (normSym a) (normSym b)

private theorem symDenEq_sound {a b : List SymItem} (h : symDenEq a b = true) (vars : List Nat) :
    den vars a = den vars b := by
  rw [← den_normSym vars a, ← den_normSym vars b, symListBeq_eq h]

private def termsBeq : List (Nat × VarExpr) → List (Nat × VarExpr) → Bool
  | [], [] => true
  | (c1, e1) :: xs, (c2, e2) :: ys => Nat.beq c1 c2 && varExprBeq e1 e2 && termsBeq xs ys
  | _, _ => false

private theorem termsBeq_eq {a b : List (Nat × VarExpr)} : termsBeq a b = true → a = b := by
  induction a generalizing b with
  | nil => cases b <;> simp [termsBeq]
  | cons x xs ih =>
    cases b with
    | nil => simp [termsBeq]
    | cons y ys =>
      rcases x with ⟨c1, e1⟩
      rcases y with ⟨c2, e2⟩
      simp only [termsBeq, Bool.and_eq_true, Nat.beq_eq]
      rintro ⟨⟨rfl, he⟩, ht⟩
      rw [varExprBeq_eq he, ih ht]

/-! ## Pure Nat Modular Residue Engine (Resid356) -/

private def p3 (e : Nat) : Nat := 3 ^ e

private theorem p3_pos (e : Nat) : 0 < p3 e := Nat.pow_pos (by omega)

private theorem p3_succ (e : Nat) : p3 (e + 1) = 3 * p3 e := by
  simp [p3, Nat.pow_succ, Nat.mul_comm]

private theorem pow4_p3 (e : Nat) : ∃ t, 4 ^ p3 e = 1 + p3 (e + 1) * t := by
  induction e with
  | zero => exact ⟨1, rfl⟩
  | succ e ih =>
    rcases ih with ⟨t, ht⟩
    refine ⟨t + 3 * p3 e * t ^ 2 + 3 * (p3 e) ^ 2 * t ^ 3, ?_⟩
    rw [p3_succ (e + 1), show 4 ^ p3 (e + 1) = (4 ^ p3 e) ^ 3 by rw [p3_succ e, Nat.mul_comm,
                                                               Nat.pow_mul], ht]
    rw [p3_succ e]
    ring

private theorem pow4_period (e a t : Nat) :
    4 ^ (a + p3 e * t) % p3 (e + 1) = 4 ^ a % p3 (e + 1) := by
  obtain ⟨s, hs⟩ := pow4_p3 e
  rw [Nat.pow_add, Nat.pow_mul, hs, Nat.mul_mod]
  rw [show (1 + p3 (e + 1) * s) ^ t % p3 (e + 1) = 1 % p3 (e + 1) by
    rw [Nat.pow_mod, Nat.mul_comm (p3 (e + 1)) s, Nat.add_mul_mod_self_right, ← Nat.pow_mod,
        Nat.one_pow]]
  rw [← Nat.mul_mod, Nat.mul_one]

private def modpow (b x m : Nat) : Nat :=
  if h : x = 0 then 1 % m
  else
    let half := modpow b (x / 2) m
    let sq := (half * half) % m
    if x % 2 = 0 then sq else (b * sq) % m
termination_by x

private theorem modpow_spec (b x m : Nat) : modpow b x m = b ^ x % m := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
    unfold modpow
    split
    · rename_i h0; subst h0; simp
    · rename_i hne
      have hlt : x / 2 < x := Nat.div_lt_self (Nat.pos_of_ne_zero hne) (by omega)
      rw [ih (x / 2) hlt]
      split
      · rename_i hev
        have hx : x = (x / 2) + (x / 2) := by omega
        conv_rhs => rw [hx, Nat.pow_add]
        simp [Nat.mul_mod]
      · rename_i hodd
        have hx : x = ((x / 2) + (x / 2)) + 1 := by omega
        conv_rhs => rw [hx, Nat.pow_add, Nat.pow_add, Nat.pow_one]
        rw [Nat.mul_comm (b ^ (x / 2) * b ^ (x / 2)) b]
        simp [Nat.mul_mod]

private def Kres (e d cq cA : Nat) : Nat :=
  let m := p3 e
  ((4 * ((cA * modpow 4 (cq + d - 1) (3 * m)) % (3 * m)) + (12 * m - 2)) % (12 * m)) / 3

private theorem K_step_nat (e d K A q cq cA cK : Nat)
    (hK : 3 * K + 2 = A * 4 ^ (q + d)) (hd : 1 ≤ d)
    (hq : q % p3 e = cq) (hA : A % p3 (e + 1) = cA)
    (hres : Kres e d cq cA = cK) :
    K % (4 * p3 e) = cK := by
  have hm : 0 < p3 e := p3_pos e
  have hm3 : p3 (e + 1) = 3 * p3 e := p3_succ e
  rw [hm3] at hA
  have h1 : 4 ^ (q + d - 1) % (3 * p3 e) = modpow 4 (cq + d - 1) (3 * p3 e) := by
    rw [modpow_spec]
    have hdm := Nat.div_add_mod q (p3 e)
    have hsplit : q + d - 1 = (cq + d - 1) + p3 e * (q / p3 e) := by
      rw [← hq]; omega
    rw [hsplit, ← hm3]
    exact pow4_period e (cq + d - 1) (q / p3 e)
  let W := A * 4 ^ (q + d - 1)
  have hW : 3 * K + 2 = 4 * W := by
    have hp : 4 ^ (q + d) = 4 * 4 ^ (q + d - 1) := by
      conv_lhs => rw [show q + d = (q + d - 1) + 1 by omega, Nat.pow_succ']
    rw [hK, hp]; unfold W; ring
  have hWmod : W % (3 * p3 e) = (cA * modpow 4 (cq + d - 1) (3 * p3 e)) % (3 * p3 e) := by
    unfold W; rw [Nat.mul_mod, hA, h1]
  have hm12 : 12 * p3 e ≥ 2 := by omega
  have h3K : (3 * K) % (12 * p3 e) = (4 * (W % (3 * p3 e)) + (12 * p3 e - 2)) % (12 * p3 e) := by
    have he1 : (3 * K) % (12 * p3 e) = (3 * K + 12 * p3 e) % (12 * p3 e) :=
        (Nat.add_mod_right _ _).symm
    have he2 : 3 * K + 12 * p3 e = 4 * W + (12 * p3 e - 2) := by omega
    have hdivW := (Nat.div_add_mod W (3 * p3 e)).symm
    have he3 :
        4 * W + (12 * p3 e - 2) = 12 * p3 e * (W / (3 * p3 e)) +
        (4 * (W % (3 * p3 e)) + (12 * p3 e - 2)) := by
      calc 4 * W + (12 * p3 e - 2) = 4 * (3 * p3 e * (W / (3 * p3 e)) + W % (3 * p3 e)) +
          (12 * p3 e - 2) := by rw [← hdivW]
        _ = 12 * p3 e * (W / (3 * p3 e)) + (4 * (W % (3 * p3 e)) + (12 * p3 e - 2)) := by ring
    rw [he1, he2, he3, Nat.mul_add_mod]
  have h3K2 : (3 * K) % (12 * p3 e) = 3 * (K % (4 * p3 e)) := by
    rw [show 12 * p3 e = 3 * (4 * p3 e) by ring]
    exact Nat.mul_mod_mul_left 3 K (4 * p3 e)
  rw [h3K2] at h3K
  unfold Kres at hres
  dsimp only at hres
  rw [← hWmod, ← h3K] at hres
  rw [Nat.mul_div_right _ (by omega)] at hres
  exact hres

private theorem K_step_j_nat (e d K j q cq cj cK : Nat)
    (hK : 3 * K + 2 = (3 * j + 11) * 4 ^ (q + d)) (hd : 1 ≤ d)
    (hq : q % p3 e = cq) (hj : j % p3 e = cj)
    (hres : Kres e d cq ((3 * cj + 11) % p3 (e + 1)) = cK) :
    K % (4 * p3 e) = cK := by
  have hA : (3 * j + 11) % p3 (e + 1) = (3 * cj + 11) % p3 (e + 1) := by
    rw [p3_succ, ← hj]
    have hdiv := (Nat.div_add_mod j (p3 e)).symm
    calc (3 * j + 11) % (3 * p3 e)
        = (3 * (p3 e * (j / p3 e) + j % p3 e) + 11) % (3 * p3 e) := by conv_lhs => rw [hdiv]
      _ = ((3 * p3 e) * (j / p3 e) + (3 * (j % p3 e) + 11)) % (3 * p3 e) := by ring_nf
      _ = (3 * (j % p3 e) + 11) % (3 * p3 e) := Nat.mul_add_mod _ _ _
  exact K_step_nat e d K (3 * j + 11) q cq ((3 * cj + 11) % p3 (e + 1)) cK hK hd hq hA hres

private theorem K_ge
    (K A x : Nat) (hK : 3 * K + 2 = A * 4 ^ x) (hA : 10 ≤ A) (hx : 1 ≤ x) : 12 ≤ K := by
  have hp : 4 ≤ 4 ^ x := by
    obtain ⟨x', rfl⟩ := Nat.exists_eq_add_of_le' hx
    rw [Nat.pow_succ]
    have : 1 ≤ 4 ^ x' := Nat.one_le_pow _ _ (by omega)
    omega
  nlinarith

private theorem K_split_nat (e K r cK : Nat)
    (hK : K % (4 * p3 (e + 1)) = cK) (hr : cK % 12 = r) (hge : 12 ≤ K) :
    K = 12 * (K / 12 - 1) + 12 + r := by
  have hdvd : 12 ∣ 4 * p3 (e + 1) := by
    rw [p3_succ]
    exact ⟨p3 e, by ring⟩
  have hm12 : K % 12 = r := by
    rw [← hr, ← hK]
    exact (Nat.mod_mod_of_dvd K hdvd).symm
  have hdm := Nat.div_add_mod K 12
  rw [hm12] at hdm
  have hdiv : 1 ≤ K / 12 := Nat.div_pos hge (by omega)
  omega

private theorem q_step_nat (e K q r cK cq : Nat)
    (hK : K = 12 * q + 12 + r) (hr : r < 12)
    (hcK : K % (4 * p3 (e + 1)) = cK)
    (hcq : (cK / 12 + (p3 e - 1)) % p3 e = cq) :
    q % p3 e = cq := by
  let m := p3 e
  have hm : 0 < m := p3_pos e
  have h12m : 4 * p3 (e + 1) = 12 * m := by rw [p3_succ]; ring
  rw [h12m] at hcK
  have hq1 : 12 * q + 12 + r = 12 * (q + 1) + r := by omega
  rw [hK, hq1] at hcK
  have hd := Nat.div_add_mod (q + 1) m
  have hu : (q + 1) % m < m := Nat.mod_lt _ hm
  have hbound : 12 * ((q + 1) % m) + r < 12 * m := by omega
  have hmod : (12 * (q + 1) + r) % (12 * m) = 12 * ((q + 1) % m) + r := by
    calc (12 * (q + 1) + r) % (12 * m)
        = (12 * (m * ((q + 1) / m) + (q + 1) % m) + r) % (12 * m) := by rw [hd]
      _ = ((12 * m) * ((q + 1) / m) + (12 * ((q + 1) % m) + r)) % (12 * m) := by ring_nf
      _ = (12 * ((q + 1) % m) + r) % (12 * m) := Nat.mul_add_mod _ _ _
      _ = 12 * ((q + 1) % m) + r := Nat.mod_eq_of_lt hbound
  rw [hmod] at hcK
  have hcdiv : cK / 12 = (q + 1) % m := by
    rw [← hcK, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr, Nat.add_zero]
  rw [hcdiv] at hcq
  rw [← hcq]
  rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  have hm_eq : q + 1 + (m - 1) = q + m := by omega
  rw [hm_eq, Nat.add_mod_right]

private theorem res_down1 (e x c c' : Nat)
    (hx : x % p3 (e + 1) = c) (hc : c % p3 e = c') :
    x % p3 e = c' := by
  rw [← hc, ← hx]
  exact (Nat.mod_mod_of_dvd x ⟨3, by rw [p3_succ]; ring⟩).symm

private theorem res_shift_nat (m c k y cc cy : Nat)
    (hm : 0 < m) (hck : c = k + y) (hc : c % m = cc)
    (hcy : (cc + (m - k % m)) % m = cy) :
    y % m = cy := by
  have hdiv := Nat.div_add_mod k m
  have hlt := Nat.mod_lt k hm
  calc y % m
      = (m * (k / m + 1) + y) % m := (Nat.mul_add_mod _ _ _).symm
    _ = (k + y + (m - k % m)) % m := by congr 1; rw [Nat.mul_add, Nat.mul_one]; omega
    _ = (c + (m - k % m)) % m := by rw [hck]
    _ = (cc + (m - k % m)) % m := by
      conv_rhs => rw [Nat.add_mod, ← hc, Nat.mod_mod, ← Nat.add_mod]
    _ = cy := hcy

private theorem res_add_shift_nat (m y a s c cy : Nat)
    (hm : 0 < m) (hy : y % m = c) (hs : s ≤ y)
    (hcy : (c + a + (m - s % m)) % m = cy) :
    (y + a - s) % m = cy := by
  have hsub : y + a = s + (y + a - s) := by omega
  have hcm : c % m = c := by rw [← hy, Nat.mod_mod]
  have hc' : (y + a) % m = (c + a) % m := by
    rw [Nat.add_mod, hy]
    conv_rhs => rw [Nat.add_mod, hcm]
  refine res_shift_nat m (y + a) s (y + a - s) ((c + a) % m) cy hm hsub hc' ?_
  rw [Nat.mod_add_mod]
  exact hcy

private theorem q_grows (q j K q' r : Nat) (hq : 4 ≤ q)
    (hK : 3 * K + 2 = (3 * j + 11) * 4 ^ (q + 1))
    (hS : K = 12 * q' + 12 + r) (hr : r < 12) :
    q ≤ q' := by
  have hlin : ∀ n, 1 ≤ n → 8 * (n + 1) ≤ 4 ^ (n + 1) := by
    intro n hn
    induction n with
    | zero => omega
    | succ n ih =>
      cases n with
      | zero => decide
      | succ n =>
        have ih' := ih (by omega)
        have hp : 4 ^ (n + 1 + 1 + 1) = 4 ^ (n + 1 + 1) * 4 := Nat.pow_succ 4 _
        omega
  have h4 := hlin q (by omega)
  have hp : 11 * 4 ^ (q + 1) ≤ (3 * j + 11) * 4 ^ (q + 1) := Nat.mul_le_mul_right _ (by omega)
  nlinarith

/-! ## Layer 2c & Layer 3: Reflective Tower Step & Halting (`Step356` + `Reach356`) -/

private def img0 : List L2 := [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]
private def imglit : List L2 := [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]

private theorem R11_Img_rep (q : Nat) : R11_Img q = img0 ++ rep imglit q := by
  induction q with
  | zero => rfl
  | succ q ih =>
    simp only [R11_Img, ih, List.append_assoc]
    congr 1
    exact rep_snoc imglit q

private def liftItem : SymItem → SymItem
  | .lit w => .lit w
  | .run u (.const k) => .run u (.const k)
  | .run u (.varPlus idx k) => .run u (.varPlus (idx + 1) k)

private def liftIm : List SymItem → List SymItem
  | [] => []
  | it :: rest => liftItem it :: liftIm rest

private theorem den_liftIm (qp : Nat) (vars : List Nat) (i : List SymItem) :
    den (qp :: vars) (liftIm i) = den vars i := by
  induction i with
  | nil => rfl
  | cons x xs ihx =>
    cases x with
    | lit lw => simp [liftIm, liftItem, den, ihx]
    | run u cnt =>
      cases cnt with
      | const k => simp [liftIm, liftItem, den, evalVar, ihx]
      | varPlus idx k => simp [liftIm, liftItem, den, evalVar, getAt, ihx]

private theorem zone_form (K q r qp : Nat) (i : List SymItem) (vars : List Nat)
    (hK : K = 12 * q + 12 + r) :
    List.replicate K .b ++ .a :: (R11_Img qp ++ den vars i) ++ [.a] =
      R11_C0 q ++ .b :: den (qp :: vars)
        ([.lit (List.replicate r .b ++ .a :: img0),
            .run imglit (.varPlus 0 0)] ++ liftIm i ++ [.lit [.a]]) := by
  subst hK
  rw [R11_C0_repeat, R11_Img_rep]
  have hsum : 12 * q + 12 + r = (12 * q + 11) + (r + 1) := by omega
  rw [hsum, List.replicate_add]
  have hr1 : List.replicate (r + 1) L2.b = L2.b :: List.replicate r L2.b := List.replicate_succ
  rw [hr1]
  simp only [den_append, den, evalVar, getAt, Nat.zero_add, den_liftIm, List.append_assoc,
      List.cons_append, List.nil_append]

private structure LevelSpec where
  fuel : Nat
  w0 : List SymItem
  ops : List SymOp
  expectedJ : List (Nat × VarExpr)
  isHalt : Bool
  im : List SymItem

private def checkLevProg (spec : LevelSpec) : Bool :=
  match szrun spec.fuel 3 spec.w0 with
  | none => false
  | some w3 =>
    match runProg spec.fuel spec.ops w3 with
    | none => false
    | some (w1, ts) =>
      if termsBeq ts spec.expectedJ then
        if spec.isHalt then
          match sactp spec.fuel .t1 w1 with
          | some (_, some .t1) => true
          | _ => false
        else
          match soim spec.fuel .t0 (.lit [.b] :: w1) with
          | some (1, i1) => symDenEq i1 spec.im
          | _ => false
      else false

private def evalTermsMod (m : Nat) (cvars : List Nat) : List (Nat × VarExpr) → Nat
  | [] => 0
  | (c, e) :: rest => (c * (evalVar cvars e) + evalTermsMod m cvars rest) % m

private theorem evalTerms_mod (m : Nat) (vars cvars : List Nat)
    (ts : List (Nat × VarExpr))
    (hvars : ∀ idx, getAt vars idx % m = getAt cvars idx) :
    evalTerms vars ts % m = evalTermsMod m cvars ts := by
  induction ts with
  | nil => simp [evalTerms, evalTermsMod]
  | cons p ts ih =>
    rcases p with ⟨c, e⟩
    simp only [evalTerms, evalTermsMod]
    have he : evalVar vars e % m = evalVar cvars e % m := by
      cases e with
      | const k => rfl
      | varPlus idx k =>
        simp only [evalVar]
        rw [Nat.add_mod, hvars idx]
        conv_rhs => rw [Nat.add_mod, ← hvars idx, Nat.mod_mod, hvars idx]
    simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, he, ih]

private def ReachState
    (w0 : List SymItem) (e cq : Nat) (cvars : List Nat) (lbs : List Nat) : Prop :=
  ∃ q : Nat, ∃ vars : List Nat,
    ReachesStar tm (init []) (recCfg (UU 0 (R11_C0 q ++ .b :: den vars w0))) ∧
    1000 ≤ q ∧ q % p3 e = cq ∧
    vars.length = cvars.length ∧
    lbs.length = cvars.length ∧
    (∀ i, i < cvars.length → getAt vars i % p3 e = getAt cvars i ∧ getAt lbs i ≤ getAt vars i)

private def shiftLhsItem (dq : Nat) (shifts : List (Nat × Nat)) : SymItem → SymItem
  | .lit w => .lit w
  | .run u (.const k) => .run u (.const k)
  | .run u (.varPlus 0 k) => .run u (.varPlus 0 (k + dq))
  | .run u (.varPlus (i + 1) k) =>
    let s := match shifts[i]? with | some p => p.2 | none => 0
    .run u (.varPlus (i + 1) (k + s))

private def shiftRhsItem (shifts : List (Nat × Nat)) : SymItem → SymItem
  | .lit w => .lit w
  | .run u (.const k) => .run u (.const k)
  | .run u (.varPlus 0 k) => .run u (.varPlus 0 k)
  | .run u (.varPlus (i + 1) k) =>
    let a := match shifts[i]? with | some p => p.1 | none => 0
    .run u (.varPlus (i + 1) (k + a))

private def symIdxLt (n : Nat) : List SymItem → Bool
  | [] => true
  | .lit _ :: rest => symIdxLt n rest
  | .run _ (.const _) :: rest => symIdxLt n rest
  | .run _ (.varPlus idx _) :: rest => decide (idx < n) && symIdxLt n rest

private def checkVarPairs : List (Nat × Nat) → List Nat → List Nat → Bool
  | [], [], [] => true
  | (a, s) :: rest, lb :: lbs', lbN :: lbsN' =>
    ((a == 0) || (s == 0)) && decide (s ≤ lb) && decide (lbN ≤ lb + a - s) &&
    checkVarPairs rest lbs' lbsN'
  | _, _, _ => false

private def checkShifts (shifts : List (Nat × Nat)) (lbs lbsNext : List Nat) (dq : Nat) : Bool :=
  Nat.beq shifts.length lbs.length &&
  Nat.beq lbsNext.length (lbs.length + 1) &&
  decide (dq ≤ 1000) &&
  decide (getAt lbsNext 0 ≤ 1000 - dq) &&
  checkVarPairs shifts lbs (lbsNext.drop 1)

private def computeNextRes (e cq : Nat) (cvars : List Nat) (jTerms : List (Nat × VarExpr))
    (dq : Nat) (shifts : List (Nat × Nat)) : Nat × Nat × Nat × List Nat :=
  let m := p3 e
  let mNext := p3 (e - 1)
  let cJ := evalTermsMod m cvars jTerms
  let cA := (3 * cJ + 11) % p3 (e + 1)
  let cK := Kres e 1 cq cA
  let r := cK % 12
  let cqNext := (cK / 12 + (mNext - 1)) % mNext
  let xqNext := (cq % mNext + (mNext - dq % mNext)) % mNext
  let restNext := (cvars.zip shifts).map (fun (c, (a, s)) =>
    ((c % mNext) + a + (mNext - s % mNext)) % mNext)
  (r, cqNext, xqNext, restNext)

private def checkStep (spec : LevelSpec) (w0Next : List SymItem) (e cq cqNext : Nat)
    (cvars cvarsNext lbs lbsNext : List Nat) (dq : Nat) (shifts : List (Nat × Nat)) : Bool :=
  let res := computeNextRes e cq cvars spec.expectedJ dq shifts
  let r := res.1
  let expCq := res.2.1
  let expXq := res.2.2.1
  let expRest := res.2.2.2
  let lhs :=
      [.lit (List.replicate r .b ++ .a :: img0),
      .run imglit (.varPlus 0 0)] ++ liftIm spec.im ++ [.lit [.a]]
  decide (e ≥ 2) &&
  (!spec.isHalt) &&
  Nat.beq cvars.length lbs.length &&
  Nat.beq cvarsNext.length (cvars.length + 1) &&
  checkShifts shifts lbs lbsNext dq &&
  Nat.beq expCq cqNext &&
  (cvarsNext == expXq :: expRest) &&
  symIdxLt (1 + cvars.length) lhs &&
  symIdxLt cvarsNext.length w0Next &&
  symDenEq (lhs.map (shiftLhsItem dq shifts)) (w0Next.map (shiftRhsItem shifts))

private theorem checkVarPairs_spec (shifts : List (Nat × Nat)) (lbs lbsNextRest vars : List Nat)
    (hchk : checkVarPairs shifts lbs lbsNextRest = true)
    (hlb : ∀ i, i < lbs.length → getAt lbs i ≤ getAt vars i)
    (hlen : vars.length = lbs.length) :
    ∀ i, i < shifts.length →
      match shifts[i]? with
      | some (a, s) =>
        (a = 0 ∨ s = 0) ∧ s ≤ getAt vars i ∧
        getAt lbsNextRest i ≤ getAt vars i + a - s
      | none => False := by
  induction shifts generalizing lbs lbsNextRest vars with
  | nil => intro i hi; simp at hi
  | cons p shifts ih =>
    rcases p with ⟨a, s⟩
    cases lbs with
    | nil => simp [checkVarPairs] at hchk
    | cons lb lbs' =>
      cases lbsNextRest with
      | nil => simp [checkVarPairs] at hchk
      | cons lbN lbsN' =>
        cases vars with
        | nil => simp at hlen
        | cons v vs =>
          simp only [checkVarPairs, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
              decide_eq_true_eq] at hchk
          rcases hchk with ⟨⟨⟨has, hs⟩, hlbN⟩, hrest⟩
          intro i hi
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero]
            have hv0 := hlb 0 (by simp)
            simp only [getAt] at hv0 ⊢
            refine ⟨has, by omega, ?_⟩
            rcases has with rfl | rfl <;> omega
          | succ i' =>
            simp only [List.getElem?_cons_succ, getAt]
            have hlb' : ∀ j, j < lbs'.length → getAt lbs' j ≤ getAt vs j := by
              intro j hj; exact hlb (j + 1) (by simp; omega)
            have hi' : i' < shifts.length := by simp at hi; omega
            exact ih lbs' lbsN' vs hrest hlb' (by simp at hlen; omega) i' hi'

private theorem getAt_zipWith (vars : List Nat) (shifts : List (Nat × Nat)) (i : Nat)
    (hi : i < shifts.length) (hvl : vars.length = shifts.length) :
    match shifts[i]? with
    | some (_, s) => getAt (List.zipWith (fun v p => v - p.2) vars shifts) i = getAt vars i - s
    | none => False := by
  induction shifts generalizing vars i with
  | nil => simp at hi
  | cons p shifts ih =>
    cases vars with
    | nil => simp at hvl
    | cons v vs =>
      cases i with
      | zero => simp [List.zipWith, getAt]
      | succ i' =>
        simp only [List.zipWith, getAt, List.getElem?_cons_succ]
        exact ih vs i' (by simp at hi; omega) (by simp at hvl; omega)

private theorem getAt_zipWith_next (vars : List Nat) (shifts : List (Nat × Nat)) (i : Nat)
    (hi : i < shifts.length) (hvl : vars.length = shifts.length) :
    match shifts[i]? with
    | some (a,
        s) => getAt (List.zipWith (fun v p => v + p.1 - p.2) vars shifts) i = getAt vars i + a - s
    | none => False := by
  induction shifts generalizing vars i with
  | nil => simp at hi
  | cons p shifts ih =>
    cases vars with
    | nil => simp at hvl
    | cons v vs =>
      cases i with
      | zero => simp [List.zipWith, getAt]
      | succ i' =>
        simp only [List.zipWith, getAt, List.getElem?_cons_succ]
        exact ih vs i' (by simp at hi; omega) (by simp at hvl; omega)

private theorem den_shiftLhs (xs : List SymItem) (q : Nat) (vars : List Nat) (dq : Nat)
    (shifts : List (Nat × Nat)) (hq : dq ≤ q)
    (hidx : symIdxLt (1 + shifts.length) xs = true)
    (hvl : vars.length = shifts.length)
    (hsub : ∀ i, i < shifts.length →
      match shifts[i]? with | some (_, s) => s ≤ getAt vars i | none => False) :
    den ((q - dq) :: List.zipWith (fun v p =>
        v - p.2) vars shifts) (xs.map (shiftLhsItem dq shifts)) =
      den (q :: vars) xs := by
  induction xs with
  | nil => rfl
  | cons item xs ih =>
    cases item with
    | lit lw =>
      simp only [symIdxLt] at hidx
      simp [List.map, shiftLhsItem, den, ih hidx]
    | run u cnt =>
      cases cnt with
      | const k =>
        simp only [symIdxLt] at hidx
        simp [List.map, shiftLhsItem, den, evalVar, ih hidx]
      | varPlus idx k =>
        simp only [symIdxLt, Bool.and_eq_true, decide_eq_true_eq] at hidx
        rcases hidx with ⟨hi, hrest⟩
        cases idx with
        | zero =>
          simp only [List.map, shiftLhsItem, den, evalVar, getAt]
          rw [show k + dq + (q - dq) = k + q by omega, ih hrest]
        | succ i =>
          have hi' : i < shifts.length := by omega
          have hzw := getAt_zipWith vars shifts i hi' hvl
          have hsi := hsub i hi'
          cases hs : shifts[i]? with
          | none => simp [hs] at hsi
          | some p =>
            simp only [hs] at hzw hsi
            simp only [List.map, shiftLhsItem, hs, den, evalVar, getAt, hzw]
            rw [show k + p.2 + (getAt vars i - p.2) = k + getAt vars i by omega, ih hrest]

private theorem den_shiftRhs (xs : List SymItem) (q : Nat) (vars : List Nat) (dq : Nat)
    (shifts : List (Nat × Nat))
    (hidx : symIdxLt (1 + shifts.length) xs = true)
    (hvl : vars.length = shifts.length)
    (hsh : ∀ i, i < shifts.length →
      match shifts[i]? with | some (a, s) => (a = 0 ∨ s = 0) ∧ s ≤ getAt vars i | none => False) :
    den ((q - dq) :: List.zipWith (fun v p => v - p.2) vars shifts) (xs.map (shiftRhsItem shifts)) =
      den ((q - dq) :: List.zipWith (fun v p => v + p.1 - p.2) vars shifts) xs := by
  induction xs with
  | nil => rfl
  | cons item xs ih =>
    cases item with
    | lit lw =>
      simp only [symIdxLt] at hidx
      simp [List.map, shiftRhsItem, den, ih hidx]
    | run u cnt =>
      cases cnt with
      | const k =>
        simp only [symIdxLt] at hidx
        simp [List.map, shiftRhsItem, den, evalVar, ih hidx]
      | varPlus idx k =>
        simp only [symIdxLt, Bool.and_eq_true, decide_eq_true_eq] at hidx
        rcases hidx with ⟨hi, hrest⟩
        cases idx with
        | zero =>
          simp only [List.map, shiftRhsItem, den, evalVar, getAt, ih hrest]
        | succ i =>
          have hi' : i < shifts.length := by omega
          have hzw1 := getAt_zipWith vars shifts i hi' hvl
          have hzw2 := getAt_zipWith_next vars shifts i hi' hvl
          have hsi := hsh i hi'
          cases hs : shifts[i]? with
          | none => simp [hs] at hsi
          | some p =>
            simp only [hs] at hzw1 hzw2 hsi
            rcases hsi with ⟨hor, hle⟩
            simp only [List.map, shiftRhsItem, hs, den, evalVar, getAt, hzw1, hzw2]
            have heq : k + p.1 + (getAt vars i - p.2) = k + (getAt vars i + p.1 - p.2) := by
              rcases hor with h0 | h0 <;> simp only [h0] <;> omega
            rw [heq, ih hrest]

private theorem map_zip_res (eNext : Nat) (hmN : 0 < p3 eNext)
    (vars cvars : List Nat) (shifts : List (Nat × Nat))
    (hvl : vars.length = cvars.length) (hsl : shifts.length = cvars.length)
    (hvars : ∀ i, i < cvars.length → getAt vars i % p3 (eNext + 1) = getAt cvars i)
    (hsub : ∀ i, i < shifts.length →
      match shifts[i]? with | some (_, s) => s ≤ getAt vars i | none => False) :
    ∀ i, i < shifts.length →
      getAt (List.zipWith (fun v p => v + p.1 - p.2) vars shifts) i % p3 eNext =
        getAt ((cvars.zip shifts).map (fun (c, (a, s)) =>
          ((c % p3 eNext) + a + (p3 eNext - s % p3 eNext)) % p3 eNext)) i := by
  induction shifts generalizing vars cvars with
  | nil => intro i hi; simp at hi
  | cons p shifts ih =>
    rcases p with ⟨a, s⟩
    cases vars with
    | nil => simp at hvl hsl; omega
    | cons v vs =>
      cases cvars with
      | nil => simp at hsl
      | cons c cs =>
        intro i hi
        cases i with
        | zero =>
          simp only [List.zipWith, List.zip_cons_cons, List.map_cons, getAt]
          have hv0 := hvars 0 (by simp)
          simp only [getAt] at hv0
          have hs0 := hsub 0 (by simp)
          simp only [List.getElem?_cons_zero] at hs0
          have hdown : v % p3 eNext = c % p3 eNext := res_down1 eNext v c (c % p3 eNext) hv0 rfl
          exact res_add_shift_nat (p3 eNext) v a s (c % p3 eNext) _ hmN hdown hs0 rfl
        | succ i' =>
          simp only [List.zipWith, List.zip_cons_cons, List.map_cons, getAt]
          apply ih vs cs (by simp at hvl; omega) (by simp at hsl; omega)
          · intro j hj; exact hvars (j + 1) (by simp at hsl ⊢; omega)
          · intro j hj; exact hsub (j + 1) (by simp at hi ⊢; omega)
          · simp at hi; omega

private theorem getAt_drop_one (xs : List Nat) (j : Nat) : getAt (xs.drop 1) j = getAt xs (j + 1) :=
    by
  cases xs with
  | nil => simp [getAt]
  | cons x xs' => simp [getAt]

private theorem tower_step (spec : LevelSpec) (w0Next : List SymItem) (e cq cqNext : Nat)
    (cvars cvarsNext lbs lbsNext : List Nat) (dq : Nat) (shifts : List (Nat × Nat))
    (hprog : checkLevProg spec = true)
    (hchk : checkStep spec w0Next e cq cqNext cvars cvarsNext lbs lbsNext dq shifts = true)
    (hreach : ReachState spec.w0 e cq cvars lbs) :
    ReachState w0Next (e - 1) cqNext cvarsNext lbsNext := by
  simp only [checkLevProg] at hprog
  cases hw3 : szrun spec.fuel 3 spec.w0 with
  | none => simp [hw3] at hprog
  | some w3 =>
    simp only [hw3] at hprog
    cases hrp : runProg spec.fuel spec.ops w3 with
    | none => simp [hrp] at hprog
    | some w1ts =>
      rcases w1ts with ⟨w1, ts⟩
      simp only [hrp] at hprog
      cases hts : termsBeq ts spec.expectedJ with
      | false => simp [hts] at hprog
      | true =>
        simp only [hts, ↓reduceIte] at hprog
        simp only [checkStep, Bool.and_eq_true, decide_eq_true_eq, Nat.beq_eq, beq_iff_eq] at hchk
        rcases hchk with ⟨⟨⟨⟨⟨⟨⟨⟨⟨he2, hnh⟩, hlen_cl⟩, hlen_cn⟩, hsh⟩, hcq_eq⟩, hcv_eq⟩, hidxL⟩,
            hidxR⟩, hez⟩
        have hnh' : spec.isHalt = false := by cases h : spec.isHalt <;> simp_all
        simp only [hnh', Bool.false_eq_true, ↓reduceIte] at hprog
        cases hso : soim spec.fuel .t0 (.lit [.b] :: w1) with
        | none => simp [hso] at hprog
        | some cim =>
          rcases cim with ⟨c0, i1⟩
          simp only [hso] at hprog
          have hc0 : c0 = 1 := by
            rcases fin2_cases c0 with rfl | rfl
            · simp at hprog
            · rfl
          subst hc0
          simp only at hprog
          rcases hreach with ⟨q, vars, hre, hq1000, hqcq, hlen_vc, hlen_lc, hvars_ok⟩
          have hts_eq := termsBeq_eq hts
          rw [← hts_eq] at hcq_eq hcv_eq hidxL hez
          have hrun_z3 : ∀ vs, zrun 3 (den vs spec.w0) = some (den vs w3) :=
              szrun_sound spec.fuel 3 spec.w0 w3 hw3
          have hrun_j : ∀ vs, zrun (evalTerms vs ts) (den vs w3) = some (den vs w1) :=
              runProg_sound spec.fuel spec.ops w3 w1 ts hrp
          have him : ∀ vs, oim .t0 (.b :: den vs w1) = some (1, den vs spec.im) := by
            intro vs
            have hso_s := soim_sound spec.fuel .t0 (.lit [.b] :: w1) 1 i1 hso vs
            simpa [den, symDenEq_sound hprog vs] using hso_s
          let J := evalTerms vars ts
          let K := TT q J + R11_H q
          have hq1 : 1 ≤ q := by omega
          obtain ⟨q0, hq0⟩ := Nat.exists_eq_add_of_le' hq1
          have hend :=
              level_end q J (den vars spec.w0) (den vars w3) (den vars w1) (den vars spec.im)
            (hrun_z3 vars) (hrun_j vars) (him vars)
          have hKform : 3 * K + 2 = (3 * J + 11) * 4 ^ (q + 1) := by
            have heq := kform q0 J
            rw [show q0 + 2 = (q0 + 1) + 1 by omega, ← hq0] at heq
            exact heq
          have hreach_K : ReachesStar tm (init [])
              (recCfg (UU 0 (List.replicate K .b ++ .a :: (R11_Img q ++ den vars spec.im) ++
                  [.a]))) :=
            run_reach _ (K + 1) _ hre hend
          have hJmod : J % p3 e = evalTermsMod (p3 e) cvars ts := by
            apply evalTerms_mod (p3 e) vars cvars ts
            intro idx
            by_cases hi : idx < cvars.length
            · exact (hvars_ok idx hi).1
            · rw [getAt_out (by omega), getAt_out (by omega)]; exact Nat.zero_mod _
          let cJ := evalTermsMod (p3 e) cvars ts
          let cA := (3 * cJ + 11) % p3 (e + 1)
          let cK := Kres e 1 cq cA
          let r := cK % 12
          have hKmod : K % (4 * p3 e) = cK :=
            K_step_j_nat e 1 K J q cq cJ cK hKform (by omega) hqcq hJmod rfl
          have hKge : 12 ≤ K := K_ge K (3 * J + 11) (q + 1) hKform (by omega) (by omega)
          have he_split : e = (e - 1) + 1 := by omega
          have hKmod' : K % (4 * p3 ((e - 1) + 1)) = cK := by rw [← he_split]; exact hKmod
          have hSK : K = 12 * (K / 12 - 1) + 12 + r :=
            K_split_nat (e - 1) K r cK hKmod' rfl hKge
          let q' := K / 12 - 1
          have hq'_mod : q' % p3 (e - 1) = cqNext :=
            q_step_nat (e - 1) K q' r cK cqNext hSK (Nat.mod_lt _ (by omega)) hKmod' hcq_eq
          have hq'_ge : 1000 ≤ q' :=
              Nat.le_trans hq1000
              (q_grows q J K q' r (by omega) hKform hSK (Nat.mod_lt _ (by omega)))
          let lhs :=
              [.lit (List.replicate (computeNextRes e cq cvars ts dq shifts).1 .b ++ .a :: img0),
              .run imglit (.varPlus 0 0)] ++ liftIm spec.im ++ [.lit [.a]]
          have hr_eq : r = (computeNextRes e cq cvars ts dq shifts).1 := rfl
          rw [zone_form K q' r q spec.im vars hSK, hr_eq] at hreach_K
          simp only [checkShifts, Bool.and_eq_true, Nat.beq_eq, decide_eq_true_eq] at hsh
          rcases hsh with ⟨⟨⟨⟨hs_len, hlN_len⟩, hdq⟩, hlbN0⟩, hvp⟩
          have hcv_pairs := checkVarPairs_spec shifts lbs (lbsNext.drop 1) vars hvp
            (fun i hi => (hvars_ok i (by omega)).2) (by omega)
          let varsNext := (q - dq) :: List.zipWith (fun v p => v + p.1 - p.2) vars shifts
          have h_ez_raw :
              den ((q - dq) :: List.zipWith (fun v p =>
                  v - p.2) vars shifts) (List.map (shiftLhsItem dq shifts) lhs) =
                den ((q - dq) :: List.zipWith (fun v p =>
                    v - p.2) vars shifts) (List.map (shiftRhsItem shifts) w0Next) :=
            symDenEq_sound hez ((q - dq) :: List.zipWith (fun v p => v - p.2) vars shifts)
          have h_lhs :=
              den_shiftLhs lhs q vars dq shifts (by omega) (by dsimp only [lhs]; simpa only [hs_len,
              hlen_cl] using hidxL) (by omega)
            (fun i hi => by
              have hp := hcv_pairs i hi
              cases hss : shifts[i]? with
              | none => simp only [hss] at hp
              | some p => simp only [hss] at hp; exact hp.2.1)
          have h_rhs :=
              den_shiftRhs w0Next q vars dq shifts (by simpa only [hs_len, hlen_cl, hlen_cn,
              Nat.add_comm] using hidxR) (by omega)
            (fun i hi => by
              have hp := hcv_pairs i hi
              cases hss : shifts[i]? with
              | none => simp only [hss] at hp
              | some p => simp only [hss] at hp; exact ⟨hp.1, hp.2.1⟩)
          have h_ez : den (q :: vars) lhs = den varsNext w0Next := by
            rw [← h_lhs, h_ez_raw, h_rhs]
          change ReachesStar tm (init [])
              (recCfg (UU 0 (R11_C0 q' ++ L2.b :: den (q :: vars) lhs))) at hreach_K
          rw [h_ez] at hreach_K
          refine ⟨q', varsNext, hreach_K, hq'_ge, hq'_mod, ?_, ?_, ?_⟩
          · simp [varsNext, List.length_zipWith, hlen_cn]; omega
          · omega
          · intro i hi
            cases i with
            | zero =>
              simp only [varsNext, getAt, hcv_eq]
              have hq_down : q % p3 (e - 1) = cq % p3 (e - 1) := by
                rw [he_split] at hqcq
                exact res_down1 (e - 1) q cq (cq % p3 (e - 1)) hqcq rfl
              have hxq :
                  (q - dq) % p3 (e - 1) = (cq % p3 (e - 1) + (p3 (e - 1) - dq % p3 (e - 1))) % p3
                  (e - 1) :=
                res_shift_nat (p3 (e - 1)) q dq (q - dq) (cq % p3 (e - 1)) _ (p3_pos _)
                    (by omega) hq_down rfl
              exact ⟨hxq, by omega⟩
            | succ j =>
              have hj : j < shifts.length := by omega
              have hcv_j := hcv_pairs j hj
              have hzw_j := getAt_zipWith_next vars shifts j hj (by omega)
              cases hsj : shifts[j]? with
              | none => simp [hsj] at hcv_j
              | some p =>
                simp only [hsj] at hcv_j hzw_j
                simp only [varsNext, getAt, hzw_j]
                refine ⟨?_, ?_⟩
                · rw [hcv_eq]
                  simp only [getAt]
                  have hres_all :=
                    map_zip_res (e - 1) (p3_pos _) vars cvars shifts hlen_vc (by omega)
                      (fun k hk => by rw [← he_split]; exact (hvars_ok k hk).1)
                      (fun k hk => by
                        have hp := hcv_pairs k hk
                        cases hsk : shifts[k]? with
                        | none => simp only [hsk] at hp
                        | some p => simp only [hsk] at hp; exact hp.2.1) j hj
                  rw [← hzw_j]
                  exact hres_all
                · rw [← getAt_drop_one lbsNext j]
                  exact hcv_j.2.2

private theorem tower_halt (spec : LevelSpec) (e cq : Nat) (cvars lbs : List Nat)
    (hprog : checkLevProg spec = true) (hhalt : spec.isHalt = true)
    (hreach : ReachState spec.w0 e cq cvars lbs) :
    IsHalt tm := by
  simp only [checkLevProg] at hprog
  cases hw3 : szrun spec.fuel 3 spec.w0 with
  | none => simp [hw3] at hprog
  | some w3 =>
    simp only [hw3] at hprog
    cases hrp : runProg spec.fuel spec.ops w3 with
    | none => simp [hrp] at hprog
    | some w1ts =>
      rcases w1ts with ⟨w1, ts⟩
      simp only [hrp] at hprog
      cases hts : termsBeq ts spec.expectedJ with
      | false => simp [hts] at hprog
      | true =>
        simp only [hts, hhalt, ↓reduceIte] at hprog
        cases hsa : sactp spec.fuel .t1 w1 with
        | none => simp [hsa] at hprog
        | some w1o =>
          rcases w1o with ⟨w', o⟩
          simp only [hsa] at hprog
          cases o with
          | none => simp at hprog
          | some st =>
            cases st <;> simp at hprog
            rcases hreach with ⟨q, vars, hre, _⟩
            have h3 := szrun_sound spec.fuel 3 spec.w0 w3 hw3 vars
            have hj := runProg_sound spec.fuel spec.ops w3 w1 ts hrp vars
            have hz : actp .t1 (den vars w1) = (den vars w', some .t1) :=
                sactp_sound spec.fuel .t1 w1 w' (some .t1) hsa vars
            let J := evalTerms vars ts
            let K := TT q J + R11_H q
            exact run_halts _ (K + 1) hre
                (level_halt q J (den vars spec.w0) (den vars w3) (den vars w1) (den vars w') h3 hj
                hz)

private def outBeq : Out → Out → Bool
  | .next a, .next b => l2ListBeq a b
  | .halt, .halt => true
  | .stuck, .stuck => true
  | _, _ => false

private theorem outBeq_eq {a b : Out} : outBeq a b = true → a = b := by
  cases a <;> cases b <;> simp only [outBeq, Bool.false_eq_true, false_implies, imp_self,
    Out.next.injEq]
  exact l2ListBeq_eq

private def optListL2Beq : Option (List L2) → Option (List L2) → Bool
  | none, none => true
  | some a, some b => l2ListBeq a b
  | _, _ => false

private theorem optListL2Beq_eq {a b : Option (List L2)} : optListL2Beq a b = true → a = b := by
  cases a <;> cases b <;> simp only [optListL2Beq, Bool.false_eq_true, false_implies, imp_self,
    Option.some.injEq]
  exact l2ListBeq_eq

private def optFin2ListL2Beq : Option (Fin 2 × List L2) → Option (Fin 2 × List L2) → Bool
  | none, none => true
  | some (c1, a), some (c2, b) => Nat.beq c1.val c2.val && l2ListBeq a b
  | _, _ => false

private theorem optFin2ListL2Beq_eq
    {a b : Option (Fin 2 × List L2)} : optFin2ListL2Beq a b = true → a = b := by
  cases a with
  | none => cases b <;> simp [optFin2ListL2Beq]
  | some p =>
    cases b with
    | none => simp [optFin2ListL2Beq]
    | some q =>
      rcases p with ⟨c1, l1⟩; rcases q with ⟨c2, l2⟩
      simp only [optFin2ListL2Beq, Bool.and_eq_true, Nat.beq_eq]
      rintro ⟨hc, hl⟩
      exact congrArg some (Prod.ext (Fin.ext hc) (l2ListBeq_eq hl))


private def U0 : List L2 := [.b, .b, .a, .a]

private def U_A6 : List L2 :=
    [.b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .a, .b,
    .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .a]

private def U_B518 : List L2 :=
    [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
    .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b,
        .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]

private def Z0_1 : List L2 :=
    [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
    .a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .a]

private def Z3_1 : List L2 :=
    [.b, .a, .b, .b, .b, .b, .a, .b, .b, .a, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
    .b, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .a]

private def Z1_1 : List L2 :=
    [.b, .b, .a, .b, .b, .a, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
    .b, .b, .a, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .a]

private def I_1 : List L2 :=
    [.a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
    .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .a]

private def lev2W0Init : List SymItem := [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.const 42),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a],
    SymItem.lit [.a]
  ]


private theorem run_A6 : runSim 36 U0 = .next U_A6 := by
  have h : outBeq (runSimFast 36 U0) (.next U_A6) = true := by decide +kernel
  rw [← runSim_eq_runSimFast] at h
  exact outBeq_eq h

private theorem run_B518 : runSim 519 U_A6 = .next U_B518 := by
  have h : outBeq (runSimFast 519 U_A6) (.next U_B518) = true := by decide +kernel
  rw [← runSim_eq_runSimFast] at h
  exact outBeq_eq h

private theorem reach_B518 : ReachesStar tm (init []) (recCfg U_B518) :=
  run_reach U_A6 519 U_B518 (run_reach U0 36 U_A6 sim_init run_A6) run_B518

private theorem start1_eq : U_B518 = UU 0 (R11_C0 42 ++ .b :: Z0_1) :=
  l2ListBeq_eq (by decide +kernel)

private theorem red1_3 : zrun 3 Z0_1 = some Z3_1 :=
  optListL2Beq_eq (by decide +kernel)

private theorem red1_j : zrun 1 Z3_1 = some Z1_1 :=
  optListL2Beq_eq (by decide +kernel)

private theorem red1_end : oim .t0 (.b :: Z1_1) = some (1, I_1) :=
  optFin2ListL2Beq_eq (by decide +kernel)

private theorem reach2_init : ReachState lev2W0Init 24 97639870189 [] [] := by
  have hend : runSim (TT 42 1 + R11_H 42 + 1) U_B518 =
      .next (UU 0 (List.replicate (TT 42 1 + R11_H 42) .b ++ .a :: (R11_Img 42 ++ I_1) ++ [.a])) :=
          by
    rw [start1_eq]
    exact level_end 42 1 Z0_1 Z3_1 Z1_1 I_1 red1_3 red1_j red1_end
  generalize hK2_def : TT 42 1 + R11_H 42 = K2 at hend
  have hKform : 3 * K2 + 2 = 14 * 4 ^ 43 := by
    rw [← hK2_def]
    simpa using kform 41 1
  have hKmod : K2 % (4 * p3 25) = Kres 25 1 42 14 :=
    K_step_nat 25 1 K2 14 42 42 14 (Kres 25 1 42 14) hKform (by omega) rfl rfl rfl
  have hmod12 : Kres 25 1 42 14 % 12 = 6 := by decide +kernel
  have hcq2 : (Kres 25 1 42 14 / 12 + (p3 24 - 1)) % p3 24 = 97639870189 := by decide +kernel
  have hp43 : 4 ^ 10 ≤ 4 ^ 43 := Nat.pow_le_pow_right (by omega) (by omega)
  have hp10 : 4 ^ 10 = 1048576 := by decide +kernel
  have hmul14 : 14 * 1048576 ≤ 14 * 4 ^ 43 := by
    rw [← hp10]
    exact Nat.mul_le_mul_left 14 hp43
  have hKge : 12 ≤ K2 := by omega
  have hq2ge : 1000 ≤ K2 / 12 - 1 := by omega
  have hSK : K2 = 12 * (K2 / 12 - 1) + 12 + 6 :=
      K_split_nat 24 K2 6 (Kres 25 1 42 14) hKmod hmod12 hKge
  have hq2mod : (K2 / 12 - 1) % p3 24 = 97639870189 :=
    q_step_nat 24 K2 (K2 / 12 - 1) 6 (Kres 25 1 42 14) 97639870189 hSK (by omega) hKmod hcq2
  have hre2 :
      ReachesStar tm (init [])
      (recCfg (UU 0 (List.replicate K2 .b ++ .a :: (R11_Img 42 ++ I_1) ++ [.a]))) :=
    run_reach U_B518 (K2 + 1) _ reach_B518 hend
  have hden_i1 : I_1 = den [] [.lit I_1] := by simp [den]
  rw [hden_i1] at hre2
  rw [zone_form K2 (K2 / 12 - 1) 6 42 [.lit I_1] [] hSK] at hre2
  have hden_lev2 : den [42] ([.lit (List.replicate 6 .b ++ .a :: img0),
      .run imglit (.varPlus 0 0)] ++ liftIm [.lit I_1] ++ [.lit [.a]]) =
      den [] lev2W0Init := by
    have h1 : den [42] ([.lit (List.replicate 6 .b ++ .a :: img0),
        .run imglit (.varPlus 0 0)] ++ liftIm [.lit I_1] ++ [.lit [.a]]) =
        den [] [.lit (List.replicate 6 .b ++ .a :: img0), .run imglit (.const 42), .lit I_1,
            .lit [.a]] := by
      simp only [den_append, den, evalVar, getAt, liftIm, liftItem, List.append_nil,
          List.append_assoc]
    rw [h1]
    exact symDenEq_sound (by decide +kernel : symDenEq [.lit (List.replicate 6 .b ++ .a :: img0),
        .run imglit (.const 42), .lit I_1, .lit [.a]] lev2W0Init = true) []
  rw [hden_lev2] at hre2
  exact ⟨K2 / 12 - 1, [], hre2, hq2ge, hq2mod, rfl, rfl, fun i hi => by simp at hi⟩


private def lev2W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.const 42),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a],
    SymItem.lit [.a]
  ]

private def lev2Ops : List SymOp :=
  [
    SymOp.lit 32,
    SymOp.front 1 7 96 [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymOp.lit 243
  ]

private def lev2J : List (Nat × VarExpr) :=
  [
    (32, VarExpr.const 1),
    (96, VarExpr.const 41),
    (243, VarExpr.const 1)
  ]

private def lev2Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.lit [.a]
  ]

private def lev2Spec : LevelSpec :=
  { fuel := 69, w0 := lev2W0, ops := lev2Ops, expectedJ := lev2J, isHalt := false, im := lev2Im }

private theorem lev2_ok : checkLevProg lev2Spec = true := by decide +kernel

private def lev3W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.const 44),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev3Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 181,
    SymOp.front 3 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 43
  ]

private def lev3J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (181, VarExpr.const 1),
    (96, VarExpr.const 43),
    (43, VarExpr.const 1)
  ]

private def lev3Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 1),
    SymItem.lit [.b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .a]
  ]

private def lev3Spec : LevelSpec :=
  { fuel := 69, w0 := lev3W0, ops := lev3Ops, expectedJ := lev3J, isHalt := false, im := lev3Im }

private theorem lev3_ok : checkLevProg lev3Spec = true := by decide +kernel

private def lev4W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 45),
    SymItem.lit [.b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a,
            .a]
  ]

private def lev4Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 384,
    SymOp.front 3 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 5 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128
  ]

private def lev4J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (384, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 45),
    (128, VarExpr.const 1)
  ]

private def lev4Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev4Spec : LevelSpec :=
  { fuel := 69, w0 := lev4W0, ops := lev4Ops, expectedJ := lev4J, isHalt := false, im := lev4Im }

private theorem lev4_ok : checkLevProg lev4Spec = true := by decide +kernel

private def lev5W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 49),
    SymItem.lit [.b, .b, .a, .a, .a]
  ]

private def lev5Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 3 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 5 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 7 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 16
  ]

private def lev5J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (96, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (24, VarExpr.const 49),
    (16, VarExpr.const 1)
  ]

private def lev5Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .a]
  ]

private def lev5Spec : LevelSpec :=
  { fuel := 69, w0 := lev5W0, ops := lev5Ops, expectedJ := lev5J, isHalt := false, im := lev5Im }

private theorem lev5_ok : checkLevProg lev5Spec = true := by decide +kernel

private def lev6W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 49),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .a, .a]
  ]

private def lev6Ops : List SymOp :=
  [
    SymOp.lit 207,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 180,
    SymOp.front 3 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 5 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 7 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 9 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 64
  ]

private def lev6J : List (Nat × VarExpr) :=
  [
    (207, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (180, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 49),
    (64, VarExpr.const 1)
  ]

private def lev6Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 1),
    SymItem.lit [.b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev6Spec : LevelSpec :=
  { fuel := 69, w0 := lev6W0, ops := lev6Ops, expectedJ := lev6J, isHalt := false, im := lev6Im }

private theorem lev6_ok : checkLevProg lev6Spec = true := by decide +kernel

private def lev7W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 49),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .a]
  ]

private def lev7Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 352,
    SymOp.front 3 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 5 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 7 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 11 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96
  ]

private def lev7J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (352, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (96, VarExpr.const 49),
    (96, VarExpr.const 1)
  ]

private def lev7Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 1),
    SymItem.lit [.b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev7Spec : LevelSpec :=
  { fuel := 69, w0 := lev7W0, ops := lev7Ops, expectedJ := lev7J, isHalt := false, im := lev7Im }

private theorem lev7_ok : checkLevProg lev7Spec = true := by decide +kernel

private def lev8W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 50),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev8Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 3 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 5 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 7 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 9 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 11 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 13 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 35
  ]

private def lev8J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (96, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 3 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 4 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 5 1),
    (24, VarExpr.const 50),
    (35, VarExpr.const 1)
  ]

private def lev8Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 1),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev8Spec : LevelSpec :=
  { fuel := 69, w0 := lev8W0, ops := lev8Ops, expectedJ := lev8J, isHalt := false, im := lev8Im }

private theorem lev8_ok : checkLevProg lev8Spec = true := by decide +kernel

private def lev9W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.const 51),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev9Ops : List SymOp :=
  [
    SymOp.lit 11
  ]

private def lev9J : List (Nat × VarExpr) :=
  [
    (11, VarExpr.const 1)
  ]

private def lev9Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 1 1),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .a]
  ]

private def lev9Spec : LevelSpec :=
  { fuel := 69, w0 := lev9W0, ops := lev9Ops, expectedJ := lev9J, isHalt := false, im := lev9Im }

private theorem lev9_ok : checkLevProg lev9Spec = true := by decide +kernel

private def lev10W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.const 51),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev10Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 3 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160
  ]

private def lev10J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (160, VarExpr.const 1)
  ]

private def lev10Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b],
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev10Spec : LevelSpec :=
  { fuel := 69, w0 := lev10W0, ops := lev10Ops, expectedJ := lev10J, isHalt := false,
      im := lev10Im }

private theorem lev10_ok : checkLevProg lev10Spec = true := by decide +kernel

private def lev11W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.const 52),
    SymItem.lit [.a, .a]
  ]

private def lev11Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 384,
    SymOp.front 3 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 5 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 360,
    SymOp.front 7 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 11 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 13 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 15 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 17 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 19 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]
  ]

private def lev11J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (384, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (360, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (96, VarExpr.const 52)
  ]

private def lev11Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 1),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .a, .b, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev11Spec : LevelSpec :=
  { fuel := 69, w0 := lev11W0, ops := lev11Ops, expectedJ := lev11J, isHalt := false,
      im := lev11Im }

private theorem lev11_ok : checkLevProg lev11Spec = true := by decide +kernel

private def lev12W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 52),
    SymItem.lit [.b, .a, .b, .b, .b, .b, .a, .a]
  ]

private def lev12Ops : List SymOp :=
  [
    SymOp.lit 207,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 316,
    SymOp.front 3 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 5 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 7 4 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 9 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 11 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 13 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 15 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 17 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 19 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 21 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32
  ]

private def lev12J : List (Nat × VarExpr) :=
  [
    (207, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (316, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (96, VarExpr.const 52),
    (32, VarExpr.const 1)
  ]

private def lev12Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 1),
    SymItem.lit [.b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev12Spec : LevelSpec :=
  { fuel := 69, w0 := lev12W0, ops := lev12Ops, expectedJ := lev12J, isHalt := false,
      im := lev12Im }

private theorem lev12_ok : checkLevProg lev12Spec = true := by decide +kernel

private def lev13W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 52),
    SymItem.lit [.b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev13Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 55,
    SymOp.front 3 8 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 5 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 7 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 9 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 11 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 13 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 15 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 17 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 19 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 21 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 23 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32
  ]

private def lev13J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (55, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 3 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 4 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 5 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 6 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 7 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 8 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 9 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 10 1),
    (24, VarExpr.const 52),
    (32, VarExpr.const 1)
  ]

private def lev13Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b],
    SymItem.lit [.a]
  ]

private def lev13Spec : LevelSpec :=
  { fuel := 69, w0 := lev13W0, ops := lev13Ops, expectedJ := lev13J, isHalt := false,
      im := lev13Im }

private theorem lev13_ok : checkLevProg lev13Spec = true := by decide +kernel


private def lev14W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 5),
    SymItem.lit [.b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 53),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev14Ops : List SymOp :=
  [
    SymOp.lit 207,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 460,
    SymOp.front 3 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 5 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 7 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 11 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 13 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 15 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 17 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 19 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 21 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 23 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 25 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96
  ]

private def lev14J : List (Nat × VarExpr) :=
  [
    (207, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (460, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (96, VarExpr.const 53),
    (96, VarExpr.const 1)
  ]

private def lev14Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 1),
    SymItem.lit [.b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev14Spec : LevelSpec :=
  { fuel := 69, w0 := lev14W0, ops := lev14Ops, expectedJ := lev14J, isHalt := false,
      im := lev14Im }

private theorem lev14_ok : checkLevProg lev14Spec = true := by decide +kernel

private def lev15W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 54),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .a]
  ]

private def lev15Ops : List SymOp :=
  [
    SymOp.lit 11
  ]

private def lev15J : List (Nat × VarExpr) :=
  [
    (11, VarExpr.const 1)
  ]

private def lev15Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a]
  ]

private def lev15Spec : LevelSpec :=
  { fuel := 69, w0 := lev15W0, ops := lev15Ops, expectedJ := lev15J, isHalt := false,
      im := lev15Im }

private theorem lev15_ok : checkLevProg lev15Spec = true := by decide +kernel

private def lev16W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 13 2),
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.const 54),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev16Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 3 6 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 64
  ]

private def lev16J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (64, VarExpr.const 1)
  ]

private def lev16Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b],
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev16Spec : LevelSpec :=
  { fuel := 69, w0 := lev16W0, ops := lev16Ops, expectedJ := lev16J, isHalt := false,
      im := lev16Im }

private theorem lev16_ok : checkLevProg lev16Spec = true := by decide +kernel

private def lev17W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 54),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .a, .a]
  ]

private def lev17Ops : List SymOp :=
  [
    SymOp.lit 7
  ]

private def lev17J : List (Nat × VarExpr) :=
  [
    (7, VarExpr.const 1)
  ]

private def lev17Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 13 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 14 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a]
  ]

private def lev17Spec : LevelSpec :=
  { fuel := 69, w0 := lev17W0, ops := lev17Ops, expectedJ := lev17J, isHalt := false,
      im := lev17Im }

private theorem lev17_ok : checkLevProg lev17Spec = true := by decide +kernel

private def lev18W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 1 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 2 3),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 13 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 14 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 15 2),
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.const 54),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev18Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 264,
    SymOp.front 3 5 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 280,
    SymOp.front 5 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 7 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 8 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 11 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 13 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 15 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 17 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 19 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 21 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 23 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 25 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 27 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 29 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 31 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 33 9 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128
  ]

private def lev18J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (264, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (280, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 12 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 13 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 14 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 15 1),
    (96, VarExpr.const 54),
    (128, VarExpr.const 1)
  ]

private def lev18Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev18Spec : LevelSpec :=
  { fuel := 69, w0 := lev18W0, ops := lev18Ops, expectedJ := lev18J, isHalt := false,
      im := lev18Im }

private theorem lev18_ok : checkLevProg lev18Spec = true := by decide +kernel

private def lev19W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 55),
    SymItem.lit [.b, .b, .a, .b, .b, .a, .a, .a]
  ]

private def lev19Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 3 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 5 8 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 48,
    SymOp.front 7 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 9 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 11 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 13 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 15 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 17 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 19 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 21 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 23 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 25 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 27 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 29 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 31 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 33 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 35 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 16
  ]

private def lev19J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (96, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (48, VarExpr.const 1),
    (24, VarExpr.varPlus 3 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 4 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 5 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 6 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 7 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 8 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 9 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 10 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 11 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 12 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 13 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 14 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 15 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 16 1),
    (24, VarExpr.const 55),
    (16, VarExpr.const 1)
  ]

private def lev19Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .a, .b, .b, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev19Spec : LevelSpec :=
  { fuel := 69, w0 := lev19W0, ops := lev19Ops, expectedJ := lev19J, isHalt := false,
      im := lev19Im }

private theorem lev19_ok : checkLevProg lev19Spec = true := by decide +kernel


private def lev20W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 55),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b, .b, .a, .a]
  ]

private def lev20Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 288,
    SymOp.front 3 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 5 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 7 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 11 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 13 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 15 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 17 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 19 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 21 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 23 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 25 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 27 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 29 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 31 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 33 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 35 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 37 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96
  ]

private def lev20J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (288, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 12 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 13 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 14 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 15 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 16 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 17 1),
    (96, VarExpr.const 55),
    (96, VarExpr.const 1)
  ]

private def lev20Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 1),
    SymItem.lit [.b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.lit [.a]
  ]

private def lev20Spec : LevelSpec :=
  { fuel := 69, w0 := lev20W0, ops := lev20Ops, expectedJ := lev20J, isHalt := false,
      im := lev20Im }

private theorem lev20_ok : checkLevProg lev20Spec = true := by decide +kernel

private def lev21W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 56),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev21Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 384,
    SymOp.front 3 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 5 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 7 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 9 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 11 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 13 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 15 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 17 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 19 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 21 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 23 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 25 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 27 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 29 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 31 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 33 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 35 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 37 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 39 7 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]
  ]

private def lev21J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (384, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 12 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 13 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 14 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 15 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 16 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 17 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 18 1),
    (96, VarExpr.const 56)
  ]

private def lev21Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a]
  ]

private def lev21Spec : LevelSpec :=
  { fuel := 69, w0 := lev21W0, ops := lev21Ops, expectedJ := lev21J, isHalt := false,
      im := lev21Im }

private theorem lev21_ok : checkLevProg lev21Spec = true := by decide +kernel

private def lev22W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 19 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 56),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .a]
  ]

private def lev22Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 3 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 5 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 7 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 9 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 11 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 13 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 15 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 17 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 19 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 21 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 23 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 25 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 27 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 29 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 31 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 33 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 35 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 37 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 39 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 41 7 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b]
  ]

private def lev22J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (96, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 3 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 4 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 5 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 6 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 7 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 8 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 9 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 10 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 11 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 12 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 13 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 14 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 15 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 16 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 17 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 18 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 19 1),
    (24, VarExpr.const 56)
  ]

private def lev22Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 19 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .a]
  ]

private def lev22Spec : LevelSpec :=
  { fuel := 69, w0 := lev22W0, ops := lev22Ops, expectedJ := lev22J, isHalt := false,
      im := lev22Im }

private theorem lev22_ok : checkLevProg lev22Spec = true := by decide +kernel

private def lev23W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 3),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 19 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 20 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 56),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .a, .a]
  ]

private def lev23Ops : List SymOp :=
  [
    SymOp.lit 53,
    SymOp.front 1 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 72,
    SymOp.front 3 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 5 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 7 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 9 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 11 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 13 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 15 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 17 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 19 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 21 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 23 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32,
    SymOp.front 25 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 27 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 29 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 31 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 33 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 35 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 40,
    SymOp.front 37 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 39 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 24,
    SymOp.front 41 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 43 3 24 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 47
  ]

private def lev23J : List (Nat × VarExpr) :=
  [
    (53, VarExpr.const 1),
    (24, VarExpr.varPlus 0 1),
    (72, VarExpr.const 1),
    (24, VarExpr.varPlus 1 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 2 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 3 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 4 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 5 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 6 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 7 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 8 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 9 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 10 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 11 1),
    (32, VarExpr.const 1),
    (24, VarExpr.varPlus 12 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 13 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 14 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 15 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 16 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 17 1),
    (40, VarExpr.const 1),
    (24, VarExpr.varPlus 18 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 19 1),
    (24, VarExpr.const 1),
    (24, VarExpr.varPlus 20 1),
    (24, VarExpr.const 56),
    (47, VarExpr.const 1)
  ]

private def lev23Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 16 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 17 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 18 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
        .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 19 0),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 20 1),
    SymItem.lit [.b, .a, .b],
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev23Spec : LevelSpec :=
  { fuel := 69, w0 := lev23W0, ops := lev23Ops, expectedJ := lev23J, isHalt := false,
      im := lev23Im }

private theorem lev23_ok : checkLevProg lev23Spec = true := by decide +kernel


private def lev24W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 3),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 1 5),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 6 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 7 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 8 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 9 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 10 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 13 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 14 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 15 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 16 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 17 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 18 2),
    SymItem.lit [.b, .a, .b, .b, .b, .a, .b, .b],
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 19 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 20 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.varPlus 21 2),
    SymItem.run [.b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b] (VarExpr.const 58),
    SymItem.lit [.a, .b, .b, .b, .b, .a, .a]
  ]

private def lev24Ops : List SymOp :=
  [
    SymOp.lit 207,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 460,
    SymOp.front 3 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 5 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 7 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 11 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 13 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 15 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 17 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 19 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 21 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 23 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 25 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 27 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 29 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 31 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 33 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 35 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 37 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 39 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 41 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 43 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 45 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 32
  ]

private def lev24J : List (Nat × VarExpr) :=
  [
    (207, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (460, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 12 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 13 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 14 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 15 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 16 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 17 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 18 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 19 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 20 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 21 1),
    (96, VarExpr.const 58),
    (32, VarExpr.const 1)
  ]

private def lev24Im : List SymItem :=
  [
    SymItem.lit [.a],
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 0 0),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
            .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
            .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 1 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 19 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b,
        .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 20 0),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 21 1),
    SymItem.lit [.b, .b, .a, .b, .b, .b],
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b,
            .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b,
            .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.lit [.a]
  ]

private def lev24Spec : LevelSpec :=
  { fuel := 69, w0 := lev24W0, ops := lev24Ops, expectedJ := lev24J, isHalt := false,
      im := lev24Im }

private theorem lev24_ok : checkLevProg lev24Spec = true := by decide +kernel

private def lev25W0 : List SymItem :=
  [
    SymItem.lit [.b, .b, .b, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymItem.run [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b] (VarExpr.varPlus 0 2),
    SymItem.lit [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a,
        .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a],
    SymItem.run [.b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a] (VarExpr.varPlus 1 2),
    SymItem.lit [.b, .b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 2 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 3 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 4 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 5 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 6 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 7 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 8 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 9 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 10 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 11 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 12 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 13 2),
    SymItem.lit [.b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 14 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 15 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 16 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 17 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 18 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 19 2),
    SymItem.lit [.b, .b, .a, .b, .b, .b, .a, .b],
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 20 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 21 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.varPlus 22 2),
    SymItem.run [.b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .b] (VarExpr.const 58),
    SymItem.lit [.b, .b, .a, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b, .a, .a]
  ]

private def lev25Ops : List SymOp :=
  [
    SymOp.lit 63,
    SymOp.front 1 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 328,
    SymOp.front 3 6 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 192,
    SymOp.front 5 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 7 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 9 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 11 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 13 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 15 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 17 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 19 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 21 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 23 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 25 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 27 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 128,
    SymOp.front 29 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 31 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 33 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 35 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 37 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 39 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 160,
    SymOp.front 41 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 43 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 96,
    SymOp.front 45 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.front 47 3 96 [.a, .b, .b, .b, .a, .b, .b, .b, .a, .b, .b, .b],
    SymOp.lit 76
  ]

private def lev25J : List (Nat × VarExpr) :=
  [
    (63, VarExpr.const 1),
    (96, VarExpr.varPlus 0 1),
    (328, VarExpr.const 1),
    (96, VarExpr.varPlus 1 1),
    (192, VarExpr.const 1),
    (96, VarExpr.varPlus 2 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 3 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 4 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 5 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 6 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 7 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 8 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 9 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 10 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 11 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 12 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 13 1),
    (128, VarExpr.const 1),
    (96, VarExpr.varPlus 14 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 15 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 16 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 17 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 18 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 19 1),
    (160, VarExpr.const 1),
    (96, VarExpr.varPlus 20 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 21 1),
    (96, VarExpr.const 1),
    (96, VarExpr.varPlus 22 1),
    (96, VarExpr.const 58),
    (76, VarExpr.const 1)
  ]

private def lev25Im : List SymItem :=
  []

private def lev25Spec : LevelSpec :=
  { fuel := 69, w0 := lev25W0, ops := lev25Ops, expectedJ := lev25J, isHalt := true, im := lev25Im }

private theorem lev25_ok : checkLevProg lev25Spec = true := by decide +kernel


private theorem fin2_cases_root (c : Fin 2) : c = 0 ∨ c = 1 := by
  rcases Nat.lt_or_ge c.val 1 with h0 | h1
  · exact Or.inl (Fin.ext (by omega))
  · exact Or.inr (Fin.ext (by omega))

private theorem fin6_cases (x : Fin 6) :
    x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by
  omega

private theorem tm_eq_target_tm : tm = target_tm := by
  funext q s
  rcases fin6_cases q with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases fin2_cases_root s with rfl | rfl <;> rfl

private theorem reach2 : ReachState lev2Spec.w0 24 97639870189 [] [] := by
  have heq : lev2W0Init = lev2Spec.w0 := symListBeq_eq (by decide +kernel)
  rw [← heq]
  exact reach2_init

private def shifts2 : List (Nat × Nat) := []
private def cvars3 : List Nat := [3496691360]
private def lbs3 : List Nat := [998]

private theorem step2_ok :
    checkStep lev2Spec lev3Spec.w0 24 97639870189 15938652886 [] cvars3 [] lbs3 2 shifts2 = true :=
        by
  decide +kernel

private theorem reach3 : ReachState lev3Spec.w0 23 15938652886 cvars3 lbs3 :=
  tower_step lev2Spec lev3Spec.w0 24 97639870189 15938652886 [] cvars3
      [] lbs3 2 shifts2 lev2_ok step2_ok reach2

private def shifts3 : List (Nat × Nat) := [(0, 2)]
private def cvars4 : List Nat := [15938652884, 3496691358]
private def lbs4 : List Nat := [998, 996]

private theorem step3_ok :
    checkStep lev3Spec lev4Spec.w0 23 15938652886 21270722858 [3496691360] cvars4
        [998] lbs4 2 shifts3 = true := by
  decide +kernel

private theorem reach4 : ReachState lev4Spec.w0 22 21270722858 cvars4 lbs4 :=
  tower_step lev3Spec lev4Spec.w0 23 15938652886 21270722858 [3496691360] cvars4
      [998] lbs4 2 shifts3 lev3_ok step3_ok reach3

private def shifts4 : List (Nat × Nat) := [(0, 2), (3, 0)]
private def cvars5 : List Nat := [350016449, 5478299679, 3496691361]
private def lbs5 : List Nat := [997, 996, 999]

private theorem step4_ok :
    checkStep lev4Spec lev5Spec.w0 22 21270722858 8296339348 [15938652884, 3496691358] cvars5 [998,
        996] lbs5 3 shifts4 = true := by
  decide +kernel

private theorem reach5 : ReachState lev5Spec.w0 21 8296339348 cvars5 lbs5 :=
  tower_step lev4Spec lev5Spec.w0 22 21270722858 8296339348 [15938652884, 3496691358] cvars5 [998,
      996] lbs5 3 shifts4 lev4_ok step4_ok reach4

private def shifts5 : List (Nat × Nat) := [(1, 0), (3, 0), (0, 0)]
private def cvars6 : List Nat := [1322770543, 350016450, 1991515281, 9906960]
private def lbs6 : List Nat := [997, 998, 999, 999]

private theorem step5_ok :
    checkStep lev5Spec lev6Spec.w0 21 8296339348 2488551090 [350016449, 5478299679,
        3496691361] cvars6 [997, 996, 999] lbs6 3 shifts5 = true := by
  decide +kernel

private theorem reach6 : ReachState lev6Spec.w0 20 2488551090 cvars6 lbs6 :=
  tower_step lev5Spec lev6Spec.w0 21 8296339348 2488551090 [350016449, 5478299679,
      3496691361] cvars6 [997, 996, 999] lbs6 3 shifts5 lev5_ok step5_ok reach5

private def shifts6 : List (Nat × Nat) := [(0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars7 : List Nat := [164028154, 160509076, 350016450, 829253814, 9906960]
private def lbs7 : List Nat := [998, 997, 998, 999, 999]

private theorem step6_ok :
    checkStep lev6Spec lev7Spec.w0 20 2488551090 515692085 [1322770543, 350016450, 1991515281,
        9906960] cvars7 [997, 998, 999, 999] lbs7 2 shifts6 = true := by
  decide +kernel

private theorem reach7 : ReachState lev7Spec.w0 19 515692085 cvars7 lbs7 :=
  tower_step lev6Spec lev7Spec.w0 20 2488551090 515692085 [1322770543, 350016450, 1991515281,
      9906960] cvars7 [997, 998, 999, 999] lbs7 2 shifts6 lev6_ok step6_ok reach6

private def shifts7 : List (Nat × Nat) := [(0, 2), (2, 0), (0, 0), (0, 0), (0, 0)]
private def cvars8 : List Nat := [128271593, 164028152, 160509078, 350016450, 54412836, 9906960]
private def lbs8 : List Nat := [997, 996, 999, 998, 999, 999]

private theorem step7_ok :
    checkStep lev7Spec lev8Spec.w0 19 515692085 333219469 [164028154, 160509076, 350016450,
        829253814, 9906960] cvars8 [998, 997, 998, 999, 999] lbs8 3 shifts7 = true := by
  decide +kernel

private theorem reach8 : ReachState lev8Spec.w0 18 333219469 cvars8 lbs8 :=
  tower_step lev7Spec lev8Spec.w0 19 515692085 333219469 [164028154, 160509076, 350016450,
      829253814, 9906960] cvars8 [998, 997, 998, 999, 999] lbs8 3 shifts7 lev7_ok step7_ok reach7

private def shifts8 : List (Nat × Nat) := [(1, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars9 : List Nat :=
    [74939141, 128271594, 34887992, 31368915, 91736124, 54412836, 9906960]
private def lbs9 : List Nat := [998, 998, 999, 999, 998, 999, 999]

private theorem step8_ok :
    checkStep lev8Spec lev9Spec.w0 18 333219469 88007614 [128271593, 164028152, 160509078,
        350016450, 54412836, 9906960] cvars9 [997, 996, 999, 998, 999, 999] lbs9 2 shifts8 = true :=
        by
  decide +kernel

private theorem reach9 : ReachState lev9Spec.w0 17 88007614 cvars9 lbs9 :=
  tower_step lev8Spec lev9Spec.w0 18 333219469 88007614 [128271593, 164028152, 160509078, 350016450,
      54412836, 9906960] cvars9 [997, 996, 999, 998, 999,
      999] lbs9 2 shifts8 lev8_ok step8_ok reach8

private def shifts9 : List (Nat × Nat) := [(1, 0), (0, 1), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars10 : List Nat :=
    [1914170, 31892421, 42178151, 34887992, 31368915, 5642682, 11366115, 9906960]
private def lbs10 : List Nat := [998, 999, 997, 999, 999, 998, 999, 999]

private theorem step9_ok :
    checkStep lev9Spec lev10Spec.w0 17 88007614 13640371 [74939141, 128271594, 34887992, 31368915,
        91736124, 54412836, 9906960] cvars10 [998, 998, 999, 999, 998, 999,
        999] lbs10 2 shifts9 = true := by
  decide +kernel

private theorem reach10 : ReachState lev10Spec.w0 16 13640371 cvars10 lbs10 :=
  tower_step lev9Spec lev10Spec.w0 17 88007614 13640371 [74939141, 128271594, 34887992, 31368915,
      91736124, 54412836, 9906960] cvars10 [998, 998, 999, 999, 998, 999,
      999] lbs10 2 shifts9 lev9_ok step9_ok reach9

private def shifts10 : List (Nat × Nat) :=
    [(0, 2), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars11 : List Nat :=
    [13640369, 1914168, 3194607, 13480337, 6190178, 2671101, 5642682, 11366115, 9906960]
private def lbs11 : List Nat := [998, 996, 999, 997, 999, 999, 998, 999, 999]

private theorem step10_ok :
    checkStep lev10Spec lev11Spec.w0 16 13640371 777199 [1914170, 31892421, 42178151, 34887992,
        31368915, 5642682, 11366115, 9906960] cvars11 [998, 999, 997, 999, 999, 998, 999,
        999] lbs11 2 shifts10 = true := by
  decide +kernel

private theorem reach11 : ReachState lev11Spec.w0 15 777199 cvars11 lbs11 :=
  tower_step lev10Spec lev11Spec.w0 16 13640371 777199 [1914170, 31892421, 42178151, 34887992,
      31368915, 5642682, 11366115, 9906960] cvars11 [998, 999, 997, 999, 999, 998, 999,
      999] lbs11 2 shifts10 lev10_ok step10_ok reach10

private def shifts11 : List (Nat × Nat) :=
    [(0, 1), (3, 0), (0, 0), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars12 : List Nat :=
    [777196, 4074430, 1914171, 3194607, 3914401, 1407209, 2671101, 859713, 1800177, 341022]
private def lbs12 : List Nat := [997, 997, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step11_ok :
    checkStep lev11Spec lev12Spec.w0 15 777199 2983876 [13640369, 1914168, 3194607, 13480337,
        6190178, 2671101, 5642682, 11366115, 9906960] cvars12 [998, 996, 999, 997, 999, 999, 998,
        999, 999] lbs12 3 shifts11 = true := by
  decide +kernel

private theorem reach12 : ReachState lev12Spec.w0 14 2983876 cvars12 lbs12 :=
  tower_step lev11Spec lev12Spec.w0 15 777199 2983876 [13640369, 1914168, 3194607, 13480337,
      6190178, 2671101, 5642682, 11366115, 9906960] cvars12 [998, 996, 999, 997, 999, 999, 998, 999,
      999] lbs12 3 shifts11 lev11_ok step11_ok reach11

private def shifts12 : List (Nat × Nat) :=
    [(1, 0), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars13 : List Nat :=
    [1389550, 777197, 885786, 319848, 5961, 725755, 1407209, 1076778, 859713, 205854, 341022]
private def lbs13 : List Nat := [997, 998, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step12_ok :
    checkStep lev12Spec lev13Spec.w0 14 2983876 326367 [777196, 4074430, 1914171, 3194607, 3914401,
        1407209, 2671101, 859713, 1800177, 341022] cvars13 [997, 997, 999, 999, 999, 999, 999, 998,
        999, 999] lbs13 3 shifts12 = true := by
  decide +kernel

private theorem reach13 : ReachState lev13Spec.w0 13 326367 cvars13 lbs13 :=
  tower_step lev12Spec lev13Spec.w0 14 2983876 326367 [777196, 4074430, 1914171, 3194607, 3914401,
      1407209, 2671101, 859713, 1800177, 341022] cvars13 [997, 997, 999, 999, 999, 999, 999, 998,
      999, 999] lbs13 3 shifts12 lev12_ok step12_ok reach12

private def shifts13 : List (Nat × Nat) :=
    [(0, 2), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars14 : List Nat :=
    [326364, 326666, 245757, 354345, 319848, 5961, 194314, 344327, 13896, 328272, 205854, 341022]
private def lbs14 : List Nat := [997, 995, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step13_ok :
    checkStep lev13Spec lev14Spec.w0 13 326367 512497 [1389550, 777197, 885786, 319848, 5961,
        725755, 1407209, 1076778, 859713, 205854, 341022] cvars14 [997, 998, 999, 999, 999, 999,
        999, 999, 998, 999, 999] lbs14 3 shifts13 = true := by
  decide +kernel

private theorem reach14 : ReachState lev14Spec.w0 12 512497 cvars14 lbs14 :=
  tower_step lev13Spec lev14Spec.w0 13 326367 512497 [1389550, 777197, 885786, 319848, 5961, 725755,
      1407209, 1076778, 859713, 205854, 341022] cvars14 [997, 998, 999, 999, 999, 999, 999, 999,
      998, 999, 999] lbs14 3 shifts13 lev13_ok step13_ok reach13

private def shifts14 : List (Nat × Nat) :=
    [(0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars15 : List Nat :=
    [158201, 149217, 149522, 68610, 51, 142701, 5961, 17167, 167180, 13896, 151125, 28707, 163875]
private def lbs15 : List Nat := [998, 997, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step14_ok :
    checkStep lev14Spec lev15Spec.w0 12 512497 59582 [326364, 326666, 245757, 354345, 319848, 5961,
        194314, 344327, 13896, 328272, 205854, 341022] cvars15 [997, 995, 999, 999, 999, 999, 999,
        999, 999, 998, 999, 999] lbs15 2 shifts14 = true := by
  decide +kernel

private theorem reach15 : ReachState lev15Spec.w0 11 59582 cvars15 lbs15 :=
  tower_step lev14Spec lev15Spec.w0 12 512497 59582 [326364, 326666, 245757, 354345, 319848, 5961,
      194314, 344327, 13896, 328272, 205854, 341022] cvars15 [997, 995, 999, 999, 999, 999, 999,
      999, 999, 998, 999, 999] lbs15 2 shifts14 lev14_ok step14_ok reach14

private def shifts15 : List (Nat × Nat) :=
    [(1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0)]
private def cvars16 : List Nat :=
    [530, 40104, 31119, 31424, 9561, 51, 24603, 5961, 17167, 49082, 13896, 33027, 28707, 45777]
private def lbs16 : List Nat :=
    [997, 999, 997, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step15_ok :
    checkStep lev15Spec lev16Spec.w0 11 59582 57419 [158201, 149217, 149522, 68610, 51, 142701,
        5961, 17167, 167180, 13896, 151125, 28707, 163875] cvars16 [998, 997, 998, 999, 999, 999,
        999, 999, 999, 999, 998, 999, 999] lbs16 3 shifts15 = true := by
  decide +kernel

private theorem reach16 : ReachState lev16Spec.w0 10 57419 cvars16 lbs16 :=
  tower_step lev15Spec lev16Spec.w0 11 59582 57419 [158201, 149217, 149522, 68610, 51, 142701, 5961,
      17167, 167180, 13896, 151125, 28707, 163875] cvars16 [998, 997, 998, 999, 999, 999, 999, 999,
      999, 999, 998, 999, 999] lbs16 3 shifts15 lev15_ok step15_ok reach15

private def shifts16 : List (Nat × Nat) :=
    [(1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0)]
private def cvars17 : List Nat :=
    [18051, 531, 738, 11436, 11741, 9561, 51, 4920, 5961, 17167, 9716, 13896, 13344, 9024, 6411]
private def lbs17 : List Nat :=
    [998, 998, 999, 997, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step16_ok :
    checkStep lev16Spec lev17Spec.w0 10 57419 7905 [530, 40104, 31119, 31424, 9561, 51, 24603, 5961,
        17167, 49082, 13896, 33027, 28707, 45777] cvars17 [997, 999, 997, 998, 999, 999, 999, 999,
        999, 999, 999, 998, 999, 999] lbs17 2 shifts16 = true := by
  decide +kernel

private theorem reach17 : ReachState lev17Spec.w0 9 7905 cvars17 lbs17 :=
  tower_step lev16Spec lev17Spec.w0 10 57419 7905 [530, 40104, 31119, 31424, 9561, 51, 24603, 5961,
      17167, 49082, 13896, 33027, 28707, 45777] cvars17 [997, 999, 997, 998, 999, 999, 999, 999,
      999, 999, 999, 998, 999, 999] lbs17 2 shifts16 lev16_ok step16_ok reach16

private def shifts17 : List (Nat × Nat) :=
    [(0, 0), (0, 1), (0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0)]
private def cvars18 : List Nat :=
    [1342, 4929, 530, 738, 4878, 5180, 3000, 51, 4920, 5961, 4045, 3155, 774, 222, 2463, 6411]
private def lbs18 : List Nat :=
    [998, 998, 997, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step17_ok :
    checkStep lev17Spec lev18Spec.w0 9 7905 1507 [18051, 531, 738, 11436, 11741, 9561, 51, 4920,
        5961, 17167, 9716, 13896, 13344, 9024, 6411] cvars18 [998, 998, 999, 997, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs18 2 shifts17 = true := by
  decide +kernel

private theorem reach18 : ReachState lev18Spec.w0 8 1507 cvars18 lbs18 :=
  tower_step lev17Spec lev18Spec.w0 9 7905 1507 [18051, 531, 738, 11436, 11741, 9561, 51, 4920,
      5961, 17167, 9716, 13896, 13344, 9024, 6411] cvars18 [998, 998, 999, 997, 998, 999, 999, 999,
      999, 999, 999, 999, 998, 999, 999] lbs18 2 shifts17 lev17_ok step17_ok reach17

private def shifts18 : List (Nat × Nat) :=
    [(0, 2), (1, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars19 : List Nat :=
    [1504, 1340, 556, 531, 738, 504, 806, 813, 51, 546, 1587, 1858, 968, 774, 222, 276, 2037]
private def lbs19 : List Nat :=
    [997, 996, 999, 998, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step18_ok :
    checkStep lev18Spec lev19Spec.w0 8 1507 1906 [1342, 4929, 530, 738, 4878, 5180, 3000, 51, 4920,
        5961, 4045, 3155, 774, 222, 2463, 6411] cvars19 [998, 998, 997, 999, 1000, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs19 3 shifts18 = true := by
  decide +kernel

private theorem reach19 : ReachState lev19Spec.w0 7 1906 cvars19 lbs19 :=
  tower_step lev18Spec lev19Spec.w0 8 1507 1906 [1342, 4929, 530, 738, 4878, 5180, 3000, 51, 4920,
      5961, 4045, 3155, 774, 222, 2463, 6411] cvars19 [998, 998, 997, 999, 1000, 998, 999, 999, 999,
      999, 999, 999, 999, 998, 999, 999] lbs19 3 shifts18 lev18_ok step18_ok reach18

private def shifts19 : List (Nat × Nat) :=
    [(0, 0), (3, 0), (0, 0), (1, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars20 : List Nat :=
    [446, 46, 614, 556, 532, 9, 504, 77, 84, 51, 546, 129, 400, 239, 45, 222, 276, 579]
private def lbs20 : List Nat :=
    [998, 997, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step19_ok :
    checkStep lev19Spec lev20Spec.w0 7 1906 424 [1504, 1340, 556, 531, 738, 504, 806, 813, 51, 546,
        1587, 1858, 968, 774, 222, 276, 2037] cvars20 [997, 996, 999, 998, 999, 1000, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs20 2 shifts19 = true := by
  decide +kernel

private theorem reach20 : ReachState lev20Spec.w0 6 424 cvars20 lbs20 :=
  tower_step lev19Spec lev20Spec.w0 7 1906 424 [1504, 1340, 556, 531, 738, 504, 806, 813, 51, 546,
      1587, 1858, 968, 774, 222, 276, 2037] cvars20 [997, 996, 999, 998, 999, 1000, 998, 999, 999,
      999, 999, 999, 999, 999, 998, 999, 999] lbs20 2 shifts19 lev19_ok step19_ok reach19

private def shifts20 : List (Nat × Nat) :=
    [(0, 2), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars21 : List Nat :=
    [179, 201, 48, 128, 70, 46, 9, 18, 77, 84, 51, 60, 129, 157, 239, 45, 222, 33, 93]
private def lbs21 : List Nat :=
    [998, 996, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999, 999]

private theorem step20_ok :
    checkStep lev20Spec lev21Spec.w0 6 424 77 [446, 46, 614, 556, 532, 9, 504, 77, 84, 51, 546, 129,
        400, 239, 45, 222, 276, 579] cvars21 [998, 997, 999, 999, 999, 999, 1000, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs21 2 shifts20 = true := by
  decide +kernel

private theorem reach21 : ReachState lev21Spec.w0 5 77 cvars21 lbs21 :=
  tower_step lev20Spec lev21Spec.w0 6 424 77 [446, 46, 614, 556, 532, 9, 504, 77, 84, 51, 546, 129,
      400, 239, 45, 222, 276, 579] cvars21 [998, 997, 999, 999, 999, 999, 1000, 998, 999, 999, 999,
      999, 999, 999, 999, 998, 999, 999] lbs21 2 shifts20 lev20_ok step20_ok reach20

private def shifts21 : List (Nat × Nat) :=
    [(0, 2), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars22 : List Nat :=
    [74, 15, 42, 48, 47, 70, 46, 9, 18, 77, 3, 51, 60, 48, 76, 77, 45, 60, 33, 12]
private def lbs22 : List Nat :=
    [997, 996, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998, 999,
    999]

private theorem step21_ok :
    checkStep lev21Spec lev22Spec.w0 5 77 46 [179, 201, 48, 128, 70, 46, 9, 18, 77, 84, 51, 60, 129,
        157, 239, 45, 222, 33, 93] cvars22 [998, 996, 999, 999, 999, 999, 999, 1000, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs22 3 shifts21 = true := by
  decide +kernel

private theorem reach22 : ReachState lev22Spec.w0 4 46 cvars22 lbs22 :=
  tower_step lev21Spec lev22Spec.w0 5 77 46 [179, 201, 48, 128, 70, 46, 9, 18, 77, 84, 51, 60, 129,
      157, 239, 45, 222, 33, 93] cvars22 [998, 996, 999, 999, 999, 999, 999, 1000, 998, 999, 999,
      999, 999, 999, 999, 999, 998, 999, 999] lbs22 3 shifts21 lev21_ok step21_ok reach21

private def shifts22 : List (Nat × Nat) :=
    [(0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars23 : List Nat :=
    [16, 20, 18, 15, 21, 20, 16, 19, 9, 18, 23, 3, 24, 6, 21, 22, 23, 18, 6, 6, 12]
private def lbs23 : List Nat :=
    [997, 997, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999, 998,
    999, 999]

private theorem step22_ok :
    checkStep lev22Spec lev23Spec.w0 4 46 19 [74, 15, 42, 48, 47, 70, 46, 9, 18, 77, 3, 51, 60, 48,
        76, 77, 45, 60, 33, 12] cvars23 [997, 996, 999, 999, 999, 999, 999, 999, 1000, 998, 999,
        999, 999, 999, 999, 999, 999, 998, 999, 999] lbs23 3 shifts22 = true := by
  decide +kernel

private theorem reach23 : ReachState lev23Spec.w0 3 19 cvars23 lbs23 :=
  tower_step lev22Spec lev23Spec.w0 4 46 19 [74, 15, 42, 48, 47, 70, 46, 9, 18, 77, 3, 51, 60, 48,
      76, 77, 45, 60, 33, 12] cvars23 [997, 996, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999,
      999, 999, 999, 999, 999, 998, 999, 999] lbs23 3 shifts22 lev22_ok step22_ok reach22

private def shifts23 : List (Nat × Nat) :=
    [(0, 2), (2, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars24 : List Nat := [7, 5, 4, 0, 6, 3, 2, 7, 1, 0, 0, 5, 3, 6, 6, 3, 4, 5, 0, 6, 6, 3]
private def lbs24 : List Nat :=
    [997, 995, 999, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999, 999,
    998, 999, 999]

private theorem step23_ok :
    checkStep lev23Spec lev24Spec.w0 3 19 1 [16, 20, 18, 15, 21, 20, 16, 19, 9, 18, 23, 3, 24, 6,
        21, 22, 23, 18, 6, 6, 12] cvars24 [997, 997, 999, 999, 999, 999, 999, 999, 999, 1000, 998,
        999, 999, 999, 999, 999, 999, 999, 998, 999, 999] lbs24 3 shifts23 = true := by
  decide +kernel

private theorem reach24 : ReachState lev24Spec.w0 2 1 cvars24 lbs24 :=
  tower_step lev23Spec lev24Spec.w0 3 19 1 [16, 20, 18, 15, 21, 20, 16, 19, 9, 18, 23, 3, 24, 6, 21,
      22, 23, 18, 6, 6, 12] cvars24 [997, 997, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999,
      999, 999, 999, 999, 999, 999, 998, 999, 999] lbs24 3 shifts23 lev23_ok step23_ok reach23

private def shifts24 : List (Nat × Nat) :=
    [(0, 0), (3, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0),
    (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0), (0, 0)]
private def cvars25 : List Nat :=
    [2, 1, 2, 1, 0, 0, 0, 2, 1, 1, 0, 0, 2, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0]
private def lbs25 : List Nat :=
    [998, 997, 998, 999, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999, 999, 999, 999,
    999, 998, 999, 999]

private theorem step24_ok :
    checkStep lev24Spec lev25Spec.w0 2 1 2 [7, 5, 4, 0, 6, 3, 2, 7, 1, 0, 0, 5, 3, 6, 6, 3, 4, 5, 0,
        6, 6, 3] cvars25 [997, 995, 999, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999,
        999, 999, 999, 999, 999, 998, 999, 999] lbs25 2 shifts24 = true := by
  decide +kernel

private theorem reach25 : ReachState lev25Spec.w0 1 2 cvars25 lbs25 :=
  tower_step lev24Spec lev25Spec.w0 2 1 2 [7, 5, 4, 0, 6, 3, 2, 7, 1, 0, 0, 5, 3, 6, 6, 3, 4, 5, 0,
      6, 6, 3] cvars25 [997, 995, 999, 999, 999, 999, 999, 999, 999, 999, 1000, 998, 999, 999, 999,
      999, 999, 999, 999, 998, 999, 999] lbs25 2 shifts24 lev24_ok step24_ok reach24

private theorem tm_halt : IsHalt tm :=
  tower_halt lev25Spec 1 2 cvars25 lbs25 lev25_ok rfl reach25


private theorem is_halt_tm : IsHalt target_tm := by
  rw [← tm_eq_target_tm]
  exact tm_halt


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA` halts from the blank tape. -/
theorem is_halt : IsHalt target := by
  rw [← target_tm_eq_target]
  exact is_halt_tm

end

end BusyBeaver.M_1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_HHH0LA
