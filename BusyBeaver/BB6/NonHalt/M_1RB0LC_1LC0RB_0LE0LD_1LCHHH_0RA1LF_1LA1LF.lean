/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic

/-!
# Busy Beaver Machine `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`
and defines `target_tm` for `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LC_1LC0RB_0LE0LD_1LC---_0RA1LF_1LA1LF`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 3, Stmt.write 0 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => none
  | 4, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 5, 1 => some (some 5, Stmt.write 1 Dir.left)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

def iterOpt {α : Type*} (f : α → Option α) : ℕ → α → Option α
  | 0, x => some x
  | n + 1, x => (f x).bind (iterOpt f n)


@[simp] lemma iterOpt_zero {α : Type*} (f : α → Option α) (x : α) :
    iterOpt f 0 x = some x := rfl


@[simp] lemma iterOpt_succ {α : Type*} (f : α → Option α) (n : ℕ) (x : α) :
    iterOpt f (n + 1) x = (f x).bind (iterOpt f n) := rfl


@[simp] lemma option_some_bind {α β : Type*} (x : α) (f : α → Option β) :
    (some x).bind f = f x := rfl


@[simp] lemma option_bind_some_fun {α : Type*} (o : Option α) :
    o.bind (fun a => some a) = o := by
  cases o <;> rfl


lemma iterOpt_add {α : Type*} (f : α → Option α) (m n : ℕ) (x : α) :
    iterOpt f (m + n) x = (iterOpt f m x).bind (iterOpt f n) := by
  induction m generalizing x with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_add, iterOpt_succ, iterOpt_succ]
    cases f x <;> simp [ih]


lemma iterOpt_trans {α : Type*} {f : α → Option α} {m n : ℕ} {x y z : α}
    (h1 : iterOpt f m x = some y) (h2 : iterOpt f n y = some z) :
    iterOpt f (m + n) x = some z := by
  rw [iterOpt_add, h1, option_some_bind, h2]

@[simp] lemma dirL_cons (q : Fin 6) (a : Fin 2) (l r : ListBlank (Fin 2)) :
    ((ListBlank.cons a l) <{{q}} r) = ⟨some q, ⟨a, l, r⟩⟩ := by simp


@[simp] lemma dirR_cons (q : Fin 6) (a : Fin 2) (l r : ListBlank (Fin 2)) :
    (l {{q}}> (ListBlank.cons a r)) = ⟨some q, ⟨a, l, r⟩⟩ := by simp


@[simp] lemma dirL_default (q : Fin 6) (r : ListBlank (Fin 2)) :
    ((default : ListBlank (Fin 2)) <{{q}} r) = ⟨some q, ⟨0, default, r⟩⟩ := rfl


@[simp] lemma dirR_default (q : Fin 6) (l : ListBlank (Fin 2)) :
    (l {{q}}> (default : ListBlank (Fin 2))) = ⟨some q, ⟨0, l, default⟩⟩ := rfl


@[simp] lemma listBlank_append_nil (s : ListBlank (Fin 2)) :
    ([] : List (Fin 2)) +> s = s := rfl


@[simp] lemma listBlank_append_cons (a : Fin 2) (l : List (Fin 2)) (s : ListBlank (Fin 2)) :
    (a :: l) +> s = ListBlank.cons a (l +> s) := rfl


@[simp] lemma listBlank_cons_zero_default :
    ListBlank.cons (0 : Fin 2) (default : ListBlank (Fin 2)) = default := by
  apply ListBlank.ext
  intro i
  cases i <;> rfl


@[simp] lemma step_0135_0_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 0, ⟨0, l, r⟩⟩ = some ((ListBlank.cons 1 l) {{1}}> r) := rfl


@[simp] lemma step_0135_0_1 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 0, ⟨1, l, r⟩⟩ = some (l <{{2}} (ListBlank.cons 0 r)) := rfl


@[simp] lemma step_0135_1_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 1, ⟨0, l, r⟩⟩ = some (l <{{2}} (ListBlank.cons 1 r)) := rfl


@[simp] lemma step_0135_1_1 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 1, ⟨1, l, r⟩⟩ = some ((ListBlank.cons 0 l) {{1}}> r) := rfl


@[simp] lemma step_0135_2_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 2, ⟨0, l, r⟩⟩ = some (l <{{4}} (ListBlank.cons 0 r)) := rfl


@[simp] lemma step_0135_2_1 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 2, ⟨1, l, r⟩⟩ = some (l <{{3}} (ListBlank.cons 0 r)) := rfl


@[simp] lemma step_0135_3_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 3, ⟨0, l, r⟩⟩ = some (l <{{2}} (ListBlank.cons 1 r)) := rfl


@[simp] lemma step_0135_4_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 4, ⟨0, l, r⟩⟩ = some ((ListBlank.cons 0 l) {{0}}> r) := rfl


@[simp] lemma step_0135_4_1 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 4, ⟨1, l, r⟩⟩ = some (l <{{5}} (ListBlank.cons 1 r)) := rfl


@[simp] lemma step_0135_5_0 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 5, ⟨0, l, r⟩⟩ = some (l <{{0}} (ListBlank.cons 1 r)) := rfl


@[simp] lemma step_0135_5_1 (l r : ListBlank (Fin 2)) :
    step target_tm ⟨some 5, ⟨1, l, r⟩⟩ = some (l <{{5}} (ListBlank.cons 1 r)) := rfl

-- ----------------------------------------------------------------------------
-- Layer 1B: Stage 1 (decode_blk and 22-Clause Transducer step_blk)
-- ----------------------------------------------------------------------------


inductive LToken where
  | L1 | L10 | L00
  deriving DecidableEq, Repr


def toLC : List LToken → ListBlank (Fin 2)
  | [] => default
  | .L1 :: l => ListBlank.cons 1 (toLC l)
  | .L10 :: l => ListBlank.cons 0 (ListBlank.cons 1 (toLC l))
  | .L00 :: l => ListBlank.cons 0 (ListBlank.cons 0 (toLC l))


@[simp] lemma toLC_nil : toLC [] = default := rfl
@[simp] lemma toLC_L1 (l : List LToken) : toLC (.L1 :: l) = ListBlank.cons 1 (toLC l) := rfl
@[simp] lemma toLC_L10 (l : List LToken) :
    toLC (.L10 :: l) = ListBlank.cons 0 (ListBlank.cons 1 (toLC l)) := rfl

@[simp] lemma toLC_L00 (l : List LToken) :
    toLC (.L00 :: l) = ListBlank.cons 0 (ListBlank.cons 0 (toLC l)) := rfl


def toRBlank : List ℕ → ListBlank (Fin 2)
  | [] => default
  | 0 :: B => ListBlank.cons 1 (toRBlank B)
  | (a + 1) :: B => ListBlank.cons 0 (toRBlank (a :: B))


@[simp] lemma toRBlank_nil : toRBlank [] = default := by rw [toRBlank]
@[simp] lemma toRBlank_zero (B : List ℕ) :
    toRBlank (0 :: B) = ListBlank.cons 1 (toRBlank B) := by rw [toRBlank]

@[simp] lemma toRBlank_succ (a : ℕ) (B : List ℕ) :
    toRBlank ((a + 1) :: B) = ListBlank.cons 0 (toRBlank (a :: B)) := by rw [toRBlank]


inductive Mode6 where
  | h11D | h10B | h100F | h10F | h1E | hL
  deriving DecidableEq, Repr


abbrev BlkCfg := Mode6 × List LToken × List ℕ


def decode_blk : BlkCfg → Cfg (Fin 2) (Fin 6)
  | (.h11D, l, B) => (toRBlank B) <{{0}} ([1, 1] +> toLC l)
  | (.h10B, l, B) => (toRBlank B) <{{2}} ([0, 1] +> toLC l)
  | (.h100F, l, B) => (toRBlank B) <{{3}} ([0, 0, 1] +> toLC l)
  | (.h10F, l, B) => (toRBlank B) <{{3}} ([0, 1] +> toLC l)
  | (.h1E, l, B) => (toRBlank B) <{{5}} ([1] +> toLC l)
  | (.hL, l, B) => ([0, 0] +> toRBlank B) {{1}}> (toLC l)


lemma init_reaches_blk0 :
    (init []) [target_tm]⊢^{12} (decode_blk (.h11D, [.L10, .L1], [])) := by
  change multiStep target_tm ⟨some 0, ⟨0, default, default⟩⟩ 12 =
    some (decode_blk (.h11D, [.L10, .L1], []))
  simp [decode_blk, multiStep_succ', multiStep_zero]


def step_blk : BlkCfg → Option BlkCfg
  | (.h11D, l, []) => some (.hL, l, [0])
  | (.h11D, l, 0 :: B') => some (.h10B, .L1 :: l, B')
  | (.h11D, l, (a + 1) :: B') => some (.hL, l, 0 :: a :: B')
  | (.h10B, l, []) => some (.h11D, .L10 :: .L1 :: .L1 :: l, [])
  | (.h10B, l, 0 :: B') => some (.h100F, l, B')
  | (.h10B, l, 1 :: B') => some (.h1E, .L00 :: .L1 :: l, B')
  | (.h10B, l, 2 :: B') => some (.h10F, .L10 :: .L1 :: l, B')
  | (.h10B, l, 3 :: B') => some (.h1E, .L10 :: .L10 :: .L1 :: l, B')
  | (.h10B, l, (a + 4) :: B') => some (.h11D, .L10 :: .L1 :: .L1 :: l, a :: B')
  | (.h100F, l, []) => some (.h11D, .L10 :: .L10 :: l, [])
  | (.h100F, _, 0 :: _) => none
  | (.h100F, l, 1 :: B') => some (.h10F, .L00 :: .L1 :: l, B')
  | (.h100F, l, 2 :: B') => some (.h1E, .L10 :: .L00 :: .L1 :: l, B')
  | (.h100F, l, (a + 3) :: B') => some (.h11D, .L10 :: .L10 :: l, a :: B')
  | (.h10F, l, []) => some (.h11D, .L10 :: .L1 :: l, [])
  | (.h10F, _, 0 :: _) => none
  | (.h10F, l, 1 :: B') => some (.h10F, .L10 :: l, B')
  | (.h10F, l, 2 :: B') => some (.h1E, .L10 :: .L10 :: l, B')
  | (.h10F, l, (a + 3) :: B') => some (.h11D, .L10 :: .L1 :: l, a :: B')
  | (.h1E, l, []) => some (.h11D, l, [])
  | (.h1E, l, 0 :: B') => some (.h1E, .L1 :: l, B')
  | (.h1E, l, (a + 1) :: B') => some (.h11D, l, a :: B')
  | (.hL, _, []) => none
  | (.hL, [], a :: B') => some (.h11D, [.L10], a :: B')
  | (.hL, .L00 :: l', a :: B') => some (.h11D, .L10 :: l', a :: B')
  | (.hL, .L10 :: l', a :: B') => some (.hL, l', 0 :: (a + 1) :: B')
  | (.hL, .L1 :: l', a :: B') => some (.hL, l', (a + 1) :: B')


theorem step_blk_correct (c c' : BlkCfg) (h : step_blk c = some c') :
    (decode_blk c) [target_tm]⊢⁺ (decode_blk c') := by
  rcases c with ⟨m, l, B⟩
  cases m with
  | h11D =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h; subst h
      exact ⟨3, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
    · rcases a with _ | a
      · simp [step_blk] at h; subst h
        exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨3, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
  | h10B =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h; subst h
      exact ⟨14, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
    · rcases a with _ | _ | _ | _ | a
      · simp [step_blk] at h; subst h
        exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨2, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨7, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨8, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨14, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
  | h100F =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h; subst h
      exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
    · rcases a with _ | _ | _ | a
      · simp [step_blk] at h
      · simp [step_blk] at h; subst h
        exact ⟨2, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨3, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
  | h10F =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h; subst h
      exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
    · rcases a with _ | _ | _ | a
      · simp [step_blk] at h
      · simp [step_blk] at h; subst h
        exact ⟨2, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨3, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
  | h1E =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h; subst h
      exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
    · rcases a with _ | a
      · simp [step_blk] at h; subst h
        exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · simp [step_blk] at h; subst h
        exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
  | hL =>
    rcases B with _ | ⟨a, B'⟩
    · simp [step_blk] at h
    · rcases l with _ | ⟨tok, l'⟩
      · simp [step_blk] at h; subst h
        exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
      · cases tok with
        | L00 =>
          simp [step_blk] at h; subst h
          exact ⟨9, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
        | L10 =>
          simp [step_blk] at h; subst h
          exact ⟨6, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩
        | L1 =>
          simp [step_blk] at h; subst h
          exact ⟨1, by omega, by simp [decode_blk, multiStep_succ', multiStep_zero]⟩

-- ----------------------------------------------------------------------------
-- Layer 1C: Stage 2 (SBlock, Phi, and 25-Clause Transducer step_5mode)
-- ----------------------------------------------------------------------------


inductive SBlock where
  | A (k : ℕ)
  | B (k : ℕ)
  deriving DecidableEq, Repr


def evalSB : List SBlock → List LToken
  | [] => []
  | .A k :: ls => List.replicate k .L1 ++ (.L10 :: evalSB ls)
  | .B k :: ls => List.replicate k .L1 ++ (.L00 :: evalSB ls)


@[simp] lemma evalSB_nil : evalSB [] = [] := rfl
@[simp] lemma evalSB_A (k : ℕ) (ls : List SBlock) :
    evalSB (.A k :: ls) = List.replicate k .L1 ++ (.L10 :: evalSB ls) := rfl

@[simp] lemma evalSB_B (k : ℕ) (ls : List SBlock) :
    evalSB (.B k :: ls) = List.replicate k .L1 ++ (.L00 :: evalSB ls) := rfl


def incTop : List SBlock → ℕ → List SBlock
  | [], d => [.A d]
  | .A k :: ls, d => .A (k + d) :: ls
  | .B k :: ls, d => .B (k + d) :: ls


@[simp] lemma incTop_nil (d : ℕ) : incTop [] d = [.A d] := rfl
@[simp] lemma incTop_A (k : ℕ) (ls : List SBlock) (d : ℕ) :
    incTop (.A k :: ls) d = .A (k + d) :: ls := rfl

@[simp] lemma incTop_B (k : ℕ) (ls : List SBlock) (d : ℕ) :
    incTop (.B k :: ls) d = .B (k + d) :: ls := rfl


lemma evalSB_incTop {ls : List SBlock} (hls : ls ≠ []) (d : ℕ) :
    evalSB (incTop ls d) = List.replicate d .L1 ++ evalSB ls := by
  rcases ls with _ | ⟨sb, lsp⟩
  · contradiction
  · cases sb with
    | A k =>
      simp only [evalSB_A, incTop_A, Nat.add_comm k d, List.replicate_add, List.append_assoc]
    | B k =>
      simp only [evalSB_B, incTop_B, Nat.add_comm k d, List.replicate_add, List.append_assoc]


inductive Mode5 where
  | hL | h10B | h1E | h100F | h10F
  deriving DecidableEq, Repr

abbrev Cfg5 := Mode5 × List SBlock × List ℕ


def Phi : Cfg5 → BlkCfg
  | (.hL, ls, rs) => (.hL, evalSB ls, 0 :: rs)
  | (.h10B, ls, rs) => (.h10B, evalSB ls, rs)
  | (.h1E, ls, rs) => (.h1E, evalSB ls, rs)
  | (.h100F, ls, rs) => (.h100F, evalSB ls, rs)
  | (.h10F, ls, rs) => (.h10F, evalSB ls, rs)


lemma pop_L1_run (r a : ℕ) (l' : List LToken) (rs : List ℕ) :
    iterOpt step_blk r (.hL, List.replicate r .L1 ++ l', a :: rs) =
      some (.hL, l', (a + r) :: rs) := by
  induction r generalizing a with
  | zero => simp
  | succ r ih =>
    rw [List.replicate_succ, List.cons_append, Nat.add_comm r 1]
    have h1 : iterOpt step_blk 1 (.hL, .L1 :: (List.replicate r .L1 ++ l'), a :: rs) =
        some (.hL, List.replicate r .L1 ++ l', (a + 1) :: rs) := rfl
    refine iterOpt_trans h1 ?_
    rw [ih (a + 1), show a + 1 + r = a + (1 + r) by omega]


lemma pop_L1_run_zero (r : ℕ) (l' : List LToken) (rs : List ℕ) :
    iterOpt step_blk r (.hL, List.replicate r .L1 ++ l', 0 :: rs) =
      some (.hL, l', r :: rs) := by
  simpa [Nat.zero_add] using pop_L1_run r 0 l' rs


def step_5mode : Cfg5 → Option Cfg5
  | (.hL, [], rs) => some (.h10B, [.A 1], rs)
  | (.hL, .A k :: lsp, rs) => some (.hL, lsp, (k + 1) :: rs)
  | (.hL, .B 0 :: lsp, rs) => some (.h10B, .A 1 :: lsp, rs)
  | (.hL, .B (k + 1) :: lsp, rs) => some (.hL, lsp, 1 :: k :: rs)
  | (.h10B, ls, []) => some (.hL, .A 0 :: incTop ls 2, [])
  | (.h10B, ls, 0 :: rsp) => some (.h100F, ls, rsp)
  | (.h10B, ls, 1 :: rsp) => some (.h1E, .B 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 2 :: rsp) => some (.h10F, .A 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 3 :: rsp) => some (.h1E, .A 0 :: .A 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 4 :: rsp) => some (.h10B, .A 1 :: incTop ls 2, rsp)
  | (.h10B, ls, (a + 5) :: rsp) => some (.hL, .A 0 :: incTop ls 2, a :: rsp)
  | (.h100F, ls, []) => some (.hL, .A 0 :: .A 0 :: ls, [])
  | (.h100F, _, 0 :: _) => none
  | (.h100F, ls, 1 :: rsp) => some (.h10F, .B 0 :: incTop ls 1, rsp)
  | (.h100F, ls, 2 :: rsp) => some (.h1E, .A 0 :: .B 0 :: incTop ls 1, rsp)
  | (.h100F, ls, 3 :: rsp) => some (.h10B, .A 1 :: .A 0 :: ls, rsp)
  | (.h100F, ls, (a + 4) :: rsp) => some (.hL, .A 0 :: .A 0 :: ls, a :: rsp)
  | (.h10F, ls, []) => some (.hL, .A 0 :: incTop ls 1, [])
  | (.h10F, _, 0 :: _) => none
  | (.h10F, ls, 1 :: rsp) => some (.h10F, .A 0 :: ls, rsp)
  | (.h10F, ls, 2 :: rsp) => some (.h1E, .A 0 :: .A 0 :: ls, rsp)
  | (.h10F, ls, 3 :: rsp) => some (.h10B, .A 1 :: incTop ls 1, rsp)
  | (.h10F, ls, (a + 4) :: rsp) => some (.hL, .A 0 :: incTop ls 1, a :: rsp)
  | (.h1E, ls, []) => some (.hL, ls, [])
  | (.h1E, ls, 0 :: rsp) => some (.h1E, incTop ls 1, rsp)
  | (.h1E, ls, 1 :: rsp) => some (.h10B, incTop ls 1, rsp)
  | (.h1E, ls, (a + 2) :: rsp) => some (.hL, ls, a :: rsp)


theorem step_5mode_correct (c c' : Cfg5)
    (hguard : c.1 ≠ .hL → c.2.1 ≠ [])
    (h : step_5mode c = some c') :
    ∃ j > 0, iterOpt step_blk j (Phi c) = some (Phi c') := by
  rcases c with ⟨m, ls, rs⟩
  cases m with
  | hL =>
    rcases ls with _ | ⟨sb, lsp⟩
    · simp [step_5mode] at h; subst h
      exact ⟨2, by omega, rfl⟩
    · cases sb with
      | A k =>
        simp [step_5mode] at h; subst h
        refine ⟨k + 1, by omega, ?_⟩
        simp only [Phi, evalSB_A]
        exact iterOpt_trans (pop_L1_run_zero k (.L10 :: evalSB lsp) rs) rfl
      | B k =>
        rcases k with _ | k
        · simp [step_5mode] at h; subst h
          exact ⟨2, by omega, rfl⟩
        · simp [step_5mode] at h; subst h
          refine ⟨(k + 1) + 3, by omega, ?_⟩
          simp only [Phi, evalSB_B]
          exact iterOpt_trans (pop_L1_run_zero (k + 1) (.L00 :: evalSB lsp) rs) rfl
  | h10B =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h
      exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
    · rcases r0 with _ | _ | _ | _ | _ | a
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
  | h100F =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h
      exact ⟨2, by omega, by simp [Phi, step_blk]⟩
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_5mode] at h
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk]⟩
  | h10F =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h
      exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_5mode] at h
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
  | h1E =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h
      exact ⟨2, by omega, by simp [Phi, step_blk]⟩
    · rcases r0 with _ | _ | a
      · simp [step_5mode] at h; subst h
        exact ⟨1, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk, evalSB_incTop hls]⟩
      · simp [step_5mode] at h; subst h
        exact ⟨2, by omega, by simp [Phi, step_blk]⟩

-- ----------------------------------------------------------------------------
-- Layer 2: Stage 3 (Spine, step_sq, and Startup to c_319)
-- ----------------------------------------------------------------------------


def W_5 : List SBlock := [.A 3, .A 0, .A 2, .A 0, .A 2]


def Spine : ℕ → List SBlock
  | 0 => W_5
  | n + 1 => .A 0 :: .A 2 :: Spine n


lemma spine_nonempty (n : ℕ) : Spine n ≠ [] := by
  cases n <;> simp [Spine, W_5]


def rep31 : ℕ → List ℕ
  | 0 => []
  | n + 1 => rep31 n ++ [3, 1]


lemma spine_left_drain (n : ℕ) (L₀ : List SBlock) (R : List ℕ) :
    iterOpt step_5mode (2 * n) (.hL, (List.replicate n [.A 0, .A 2]).flatten ++ L₀, R) =
      some (.hL, L₀, rep31 n ++ R) := by
  induction n generalizing R with
  | zero => simp [rep31]
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2]
    simp only [List.replicate_succ, List.flatten_cons, List.append_assoc]
    have h2 : iterOpt step_5mode 2
        (.hL, .A 0 :: .A 2 :: ((List.replicate n [.A 0, .A 2]).flatten ++ L₀), R) =
        some (.hL, (List.replicate n [.A 0, .A 2]).flatten ++ L₀, 3 :: 1 :: R) := rfl
    refine iterOpt_trans h2 ?_
    rw [ih (3 :: 1 :: R)]
    simp [rep31, List.append_assoc]


lemma spine_eq_flatten (n : ℕ) :
    Spine n = (List.replicate n [.A 0, .A 2]).flatten ++ W_5 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Spine, List.replicate_succ, ih]


lemma w5_bottom_bounce (R' : List ℕ) :
    iterOpt step_5mode 11 (.hL, W_5, R') = some (.h10B, .A 1 :: W_5, R') := rfl


lemma spine_right_climb (n : ℕ) (L₀ : List SBlock) (R : List ℕ) :
    iterOpt step_5mode (2 * n) (.h10B, .A 1 :: L₀, rep31 n ++ R) =
      some (.h10B, .A 1 :: ((List.replicate n [.A 0, .A 2]).flatten ++ L₀), R) := by
  induction n generalizing L₀ R with
  | zero => simp [rep31]
  | succ n ih =>
    rw [Nat.mul_succ, rep31, List.append_assoc]
    have h_ih := ih L₀ ([3, 1] ++ R)
    refine iterOpt_trans h_ih ?_
    have h2 : iterOpt step_5mode 2
        (.h10B, .A 1 :: ((List.replicate n [.A 0, .A 2]).flatten ++ L₀), 3 :: 1 :: R) =
        some (.h10B, .A 1 :: .A 0 :: .A 2 :: ((List.replicate n [.A 0, .A 2]).flatten ++ L₀), R) := rfl
    simpa [List.replicate_succ] using h2


theorem spine_bounce_stationary (n : ℕ) (R : List ℕ) :
    iterOpt step_5mode (4 * n + 11) (.hL, Spine n, R) =
      some (.h10B, .A 1 :: Spine n, R) := by
  rw [spine_eq_flatten]
  have h1 := spine_left_drain n W_5 R
  have h2 := w5_bottom_bounce (rep31 n ++ R)
  have h3 := spine_right_climb n W_5 R
  have h12 := iterOpt_trans h1 h2
  have h123 := iterOpt_trans h12 h3
  have h_len : 2 * n + 11 + 2 * n = 4 * n + 11 := by omega
  rwa [h_len] at h123


theorem spine_bounce_absorb (n : ℕ) (R : List ℕ) :
    iterOpt step_5mode (4 * n + 15) (.hL, [.A 0, .A 2] ++ Spine n, R) =
      some (.h10B, .A 1 :: Spine (n + 1), R) := by
  have h := spine_bounce_stationary (n + 1) R
  have h_len : 4 * (n + 1) + 11 = 4 * n + 15 := by omega
  rwa [h_len] at h


abbrev CfgSq := Mode5 × List SBlock × List ℕ


def Psi_sq (n : ℕ) : CfgSq → Cfg5
  | (m, ls, rs) => (m, ls ++ Spine n, rs)


def step_sq : CfgSq → Option CfgSq
  | (.hL, [], rs) => some (.h10B, [.A 1], rs)
  | (.hL, [.A 0, .A 2], rs) => some (.h10B, [.A 1], rs)
  | (.hL, .A k :: lsp, rs) => some (.hL, lsp, (k + 1) :: rs)
  | (.hL, .B 0 :: lsp, rs) => some (.h10B, .A 1 :: lsp, rs)
  | (.hL, .B (k + 1) :: lsp, rs) => some (.hL, lsp, 1 :: k :: rs)
  | (.h10B, ls, []) => some (.hL, .A 0 :: incTop ls 2, [])
  | (.h10B, ls, 0 :: rsp) => some (.h100F, ls, rsp)
  | (.h10B, ls, 1 :: rsp) => some (.h1E, .B 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 2 :: rsp) => some (.h10F, .A 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 3 :: rsp) => some (.h1E, .A 0 :: .A 0 :: incTop ls 1, rsp)
  | (.h10B, ls, 4 :: rsp) => some (.h10B, .A 1 :: incTop ls 2, rsp)
  | (.h10B, ls, (a + 5) :: rsp) => some (.hL, .A 0 :: incTop ls 2, a :: rsp)
  | (.h100F, ls, []) => some (.hL, .A 0 :: .A 0 :: ls, [])
  | (.h100F, _, 0 :: _) => none
  | (.h100F, ls, 1 :: rsp) => some (.h10F, .B 0 :: incTop ls 1, rsp)
  | (.h100F, ls, 2 :: rsp) => some (.h1E, .A 0 :: .B 0 :: incTop ls 1, rsp)
  | (.h100F, ls, 3 :: rsp) => some (.h10B, .A 1 :: .A 0 :: ls, rsp)
  | (.h100F, ls, (a + 4) :: rsp) => some (.hL, .A 0 :: .A 0 :: ls, a :: rsp)
  | (.h10F, ls, []) => some (.hL, .A 0 :: incTop ls 1, [])
  | (.h10F, _, 0 :: _) => none
  | (.h10F, ls, 1 :: rsp) => some (.h10F, .A 0 :: ls, rsp)
  | (.h10F, ls, 2 :: rsp) => some (.h1E, .A 0 :: .A 0 :: ls, rsp)
  | (.h10F, ls, 3 :: rsp) => some (.h10B, .A 1 :: incTop ls 1, rsp)
  | (.h10F, ls, (a + 4) :: rsp) => some (.hL, .A 0 :: incTop ls 1, a :: rsp)
  | (.h1E, ls, []) => some (.hL, ls, [])
  | (.h1E, ls, 0 :: rsp) => some (.h1E, incTop ls 1, rsp)
  | (.h1E, ls, 1 :: rsp) => some (.h10B, incTop ls 1, rsp)
  | (.h1E, ls, (a + 2) :: rsp) => some (.hL, ls, a :: rsp)


lemma incTop_nonempty (ls : List SBlock) (d : ℕ) : incTop ls d ≠ [] := by
  cases ls with
  | nil => simp
  | cons sb lsp => cases sb <;> simp


lemma incTop_append {ls : List SBlock} (hls : ls ≠ []) (S : List SBlock) (d : ℕ) :
    incTop (ls ++ S) d = incTop ls d ++ S := by
  rcases ls with _ | ⟨sb, lsp⟩
  · contradiction
  · cases sb <;> rfl


lemma step_sq_preserves_guard (c c' : CfgSq)
    (hguard : c.1 ≠ .hL → c.2.1 ≠ [])
    (h : step_sq c = some c') :
    c'.1 ≠ .hL → c'.2.1 ≠ [] := by
  rcases c with ⟨m, ls, rs⟩
  cases m with
  | hL =>
    rcases ls with _ | ⟨sb, lsp⟩
    · simp [step_sq] at h; subst h; simp
    · cases sb with
      | A k =>
        rcases k with _ | k
        · rcases lsp with _ | ⟨sb2, lsp2⟩
          · simp [step_sq] at h; subst h; simp
          · cases sb2 with
            | A k2 =>
              rcases k2 with _ | _ | _ | k2
              · simp [step_sq] at h; subst h; simp
              · simp [step_sq] at h; subst h; simp
              · rcases lsp2 with _ | ⟨sb3, lsp3⟩
                · simp [step_sq] at h; subst h; simp
                · simp [step_sq] at h; subst h; simp
              · simp [step_sq] at h; subst h; simp
            | B k2 => simp [step_sq] at h; subst h; simp
        · simp [step_sq] at h; subst h; simp
      | B k =>
        rcases k with _ | k
        · simp [step_sq] at h; subst h; simp
        · simp [step_sq] at h; subst h; simp
  | h10B =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | _ | a <;>
        (simp [step_sq] at h; subst h; intro _; first | exact hls | exact incTop_nonempty _ _ | simp)
  | h100F =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_sq] at h
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
  | h10F =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_sq] at h
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
      · simp [step_sq] at h; subst h; simp
  | h1E =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h; simp
    · rcases r0 with _ | _ | a
      · simp [step_sq] at h; subst h; intro _; exact incTop_nonempty _ _
      · simp [step_sq] at h; subst h; intro _; exact incTop_nonempty _ _
      · simp [step_sq] at h; subst h; simp


def decode_sq (n : ℕ) (c : CfgSq) : Cfg (Fin 2) (Fin 6) :=
  decode_blk (Phi (Psi_sq n c))


lemma psi_sq_guard (n : ℕ) (c : CfgSq) :
    (Psi_sq n c).1 ≠ .hL → (Psi_sq n c).2.1 ≠ [] := by
  rcases c with ⟨m, ls, rs⟩
  intro _
  simp only [Psi_sq]
  intro h_empty
  have := List.append_eq_nil_iff.mp h_empty
  exact spine_nonempty n this.2


theorem step_sq_lift (n : ℕ) (c c' : CfgSq)
    (hguard : c.1 ≠ .hL → c.2.1 ≠ [])
    (h : step_sq c = some c') :
    ∃ n' k, k > 0 ∧ iterOpt step_5mode k (Psi_sq n c) = some (Psi_sq n' c') := by
  rcases c with ⟨m, ls, rs⟩
  cases m with
  | hL =>
    rcases ls with _ | ⟨sb, lsp⟩
    · simp [step_sq] at h; subst h
      exact ⟨n, 4 * n + 11, by omega, spine_bounce_stationary n rs⟩
    · cases sb with
      | A k =>
        rcases k with _ | k
        · rcases lsp with _ | ⟨sb2, lsp2⟩
          · simp [step_sq] at h; subst h
            exact ⟨n, 1, by omega, rfl⟩
          · cases sb2 with
            | A k2 =>
              rcases k2 with _ | _ | _ | k2
              · simp [step_sq] at h; subst h
                exact ⟨n, 1, by omega, rfl⟩
              · simp [step_sq] at h; subst h
                exact ⟨n, 1, by omega, rfl⟩
              · rcases lsp2 with _ | ⟨sb3, lsp3⟩
                · simp [step_sq] at h; subst h
                  exact ⟨n + 1, 4 * n + 15, by omega, spine_bounce_absorb n rs⟩
                · simp [step_sq] at h; subst h
                  exact ⟨n, 1, by omega, rfl⟩
              · simp [step_sq] at h; subst h
                exact ⟨n, 1, by omega, rfl⟩
            | B k2 =>
              simp [step_sq] at h; subst h
              exact ⟨n, 1, by omega, rfl⟩
        · simp [step_sq] at h; subst h
          exact ⟨n, 1, by omega, rfl⟩
      | B k =>
        rcases k with _ | k
        · simp [step_sq] at h; subst h
          exact ⟨n, 1, by omega, rfl⟩
        · simp [step_sq] at h; subst h
          exact ⟨n, 1, by omega, rfl⟩
  | h10B =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h
      exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
    · rcases r0 with _ | _ | _ | _ | _ | a <;>
        (simp [step_sq] at h; subst h;
         exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩)
  | h100F =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h
      exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_sq] at h
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
  | h10F =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h
      exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_sq] at h
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
  | h1E =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_sq] at h; subst h
      exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩
    · rcases r0 with _ | _ | a
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode, incTop_append hls]⟩
      · simp [step_sq] at h; subst h
        exact ⟨n, 1, by omega, by simp [Psi_sq, step_5mode]⟩


def c0_sq : CfgSq := (.hL, [.A 0], [])

def c319_sq : CfgSq := (.h10B, [.A 1], [3, 1, 0, 1, 3, 1, 1, 1, 1, 1, 0, 1])


def SqReachesPlus (R₁ R₂ : List ℕ) : Prop :=
  ∃ k > 0, iterOpt step_sq k (.h10B, [.A 1], R₁) = some (.h10B, [.A 1], R₂)


def SqReachesStar (R₁ R₂ : List ℕ) : Prop :=
  ∃ k, iterOpt step_sq k (.h10B, [.A 1], R₁) = some (.h10B, [.A 1], R₂)


lemma sqReachesStar_refl (R : List ℕ) : SqReachesStar R R :=
  ⟨0, rfl⟩


lemma sqReachesStar_of_plus {R₁ R₂ : List ℕ} (h : SqReachesPlus R₁ R₂) :
    SqReachesStar R₁ R₂ := by
  rcases h with ⟨k, _, hk⟩
  exact ⟨k, hk⟩


lemma sqReachesPlus_trans {R₁ R₂ R₃ : List ℕ}
    (h₁ : SqReachesPlus R₁ R₂) (h₂ : SqReachesPlus R₂ R₃) :
    SqReachesPlus R₁ R₃ := by
  rcases h₁ with ⟨k₁, hk₁, hstep₁⟩
  rcases h₂ with ⟨k₂, hk₂, hstep₂⟩
  exact ⟨k₁ + k₂, by omega, iterOpt_trans hstep₁ hstep₂⟩


lemma sqReachesPlus_star_trans {R₁ R₂ R₃ : List ℕ}
    (h₁ : SqReachesPlus R₁ R₂) (h₂ : SqReachesStar R₂ R₃) :
    SqReachesPlus R₁ R₃ := by
  rcases h₁ with ⟨k₁, hk₁, hstep₁⟩
  rcases h₂ with ⟨k₂, hstep₂⟩
  exact ⟨k₁ + k₂, by omega, iterOpt_trans hstep₁ hstep₂⟩


lemma sqReachesStar_trans {R₁ R₂ R₃ : List ℕ}
    (h₁ : SqReachesStar R₁ R₂) (h₂ : SqReachesStar R₂ R₃) :
    SqReachesStar R₁ R₃ := by
  rcases h₁ with ⟨k₁, hstep₁⟩
  rcases h₂ with ⟨k₂, hstep₂⟩
  exact ⟨k₁ + k₂, iterOpt_trans hstep₁ hstep₂⟩


lemma replicate_append_cons_same {α : Type*} (k : ℕ) (x : α) (L : List α) :
    List.replicate k x ++ (x :: L) = List.replicate (k + 1) x ++ L := by
  induction k with
  | zero => rfl
  | succ k ih => simp [List.replicate_succ, ih]


lemma replicate_two_mul_append_two {α : Type*} (k : ℕ) (x : α) (R : List α) :
    List.replicate (2 * (k + 1)) x ++ R = List.replicate (2 * k) x ++ (x :: x :: R) := by
  rw [Nat.mul_succ, List.replicate_add, List.append_assoc]
  rfl


lemma incTop_incTop (ls : List SBlock) (d1 d2 : ℕ) :
    incTop (incTop ls d1) d2 = incTop ls (d1 + d2) := by
  cases ls with
  | nil => rfl
  | cons sb lsp => cases sb <;> simp [incTop, Nat.add_assoc]


lemma scan_ones_h10B (k : ℕ) (ls : List SBlock) (R : List ℕ) :
    iterOpt step_sq (2 * (k + 1)) (.h10B, ls, List.replicate (2 * (k + 1)) 1 ++ R) =
      some (.h10B, .B 1 :: (List.replicate k (.B 2) ++ incTop ls 1), R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [replicate_two_mul_append_two (k + 1), Nat.mul_succ 2 (k + 1)]
    refine iterOpt_trans (ih (1 :: 1 :: R)) ?_
    have h2 : iterOpt step_sq 2
        (.h10B, .B 1 :: (List.replicate k (.B 2) ++ incTop ls 1), 1 :: 1 :: R) =
        some (.h10B, .B 1 :: .B 2 :: (List.replicate k (.B 2) ++ incTop ls 1), R) := rfl
    simpa [List.replicate_succ] using h2


lemma scan_ones_h1E (k : ℕ) (ls : List SBlock) (R : List ℕ) :
    iterOpt step_sq (2 * (k + 1)) (.h1E, ls, List.replicate (2 * (k + 1)) 1 ++ R) =
      some (.h1E, .B 0 :: (List.replicate k (.B 2) ++ incTop ls 2), R) := by
  induction k generalizing R with
  | zero =>
    simp [iterOpt, step_sq, incTop_incTop]
  | succ k ih =>
    rw [replicate_two_mul_append_two (k + 1), Nat.mul_succ 2 (k + 1)]
    refine iterOpt_trans (ih (1 :: 1 :: R)) ?_
    have h2 : iterOpt step_sq 2
        (.h1E, .B 0 :: (List.replicate k (.B 2) ++ incTop ls 2), 1 :: 1 :: R) =
        some (.h1E, .B 0 :: .B 2 :: (List.replicate k (.B 2) ++ incTop ls 2), R) := rfl
    simpa [List.replicate_succ] using h2


lemma scan_ones_h10F (k : ℕ) (ls : List SBlock) (R : List ℕ) :
    iterOpt step_sq k (.h10F, ls, List.replicate k 1 ++ R) =
      some (.h10F, List.replicate k (.A 0) ++ ls, R) := by
  induction k generalizing ls with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    conv_lhs => rw [Nat.add_comm k 1]
    have h1 : iterOpt step_sq 1 (.h10F, ls, 1 :: (List.replicate k 1 ++ R)) =
        some (.h10F, .A 0 :: ls, List.replicate k 1 ++ R) := rfl
    refine iterOpt_trans h1 ?_
    rw [ih (.A 0 :: ls), replicate_append_cons_same]


lemma step_sq_hL_A0 (lsp : List SBlock) (h : lsp ≠ [.A 2]) (rs : List ℕ) :
    step_sq (.hL, .A 0 :: lsp, rs) = some (.hL, lsp, 1 :: rs) := by
  rcases lsp with _ | ⟨sb, lsp2⟩
  · rfl
  · cases sb with
    | A k =>
      rcases k with _ | _ | _ | k
      · rfl
      · rfl
      · rcases lsp2 with _ | ⟨sb3, lsp3⟩
        · exact absurd rfl h
        · rfl
      · rfl
    | B k => rfl


lemma replicate_A0_append_ne_A2 (k : ℕ) {ls : List SBlock} (h : ls ≠ [.A 2]) :
    List.replicate k (.A 0) ++ ls ≠ [.A 2] := by
  cases k with
  | zero => exact h
  | succ k =>
    rw [List.replicate_succ, List.cons_append]
    intro hc; injection hc with h1 _; cases h1


lemma pop_B2_run_hL (k : ℕ) (ls : List SBlock) (R : List ℕ) :
    iterOpt step_sq k (.hL, List.replicate k (.B 2) ++ ls, R) =
      some (.hL, ls, List.replicate (2 * k) 1 ++ R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    conv_lhs => rw [Nat.add_comm k 1]
    have h1 : iterOpt step_sq 1 (.hL, .B 2 :: (List.replicate k (.B 2) ++ ls), R) =
        some (.hL, List.replicate k (.B 2) ++ ls, 1 :: 1 :: R) := rfl
    refine iterOpt_trans h1 ?_
    rw [ih (1 :: 1 :: R), ← replicate_two_mul_append_two]


def stackAfterOnes (k : ℕ) (L : List SBlock) : List SBlock :=
  match k with
  | 0 => .A 1 :: L
  | k' + 1 => .B 1 :: (List.replicate k' (.B 2) ++ (.A 2 :: L))


lemma scan_ones_h10B_any (k : ℕ) (L : List SBlock) (R : List ℕ) :
    iterOpt step_sq (2 * k) (.h10B, .A 1 :: L, List.replicate (2 * k) 1 ++ R) =
      some (.h10B, stackAfterOnes k L, R) := by
  cases k with
  | zero => rfl
  | succ k' => exact scan_ones_h10B k' (.A 1 :: L) R


@[simp] lemma incTop_stackAfterOnes (k : ℕ) (L : List SBlock) :
    incTop (stackAfterOnes k L) 1 = List.replicate k (.B 2) ++ (.A 2 :: L) := by
  cases k <;> rfl


lemma pop_B2_A2_hL (k : ℕ) (L : List SBlock) (R : List ℕ) :
    iterOpt step_sq (k + 1) (.hL, List.replicate k (.B 2) ++ (.A 2 :: L), R) =
      some (.hL, L, 3 :: (List.replicate (2 * k) 1 ++ R)) := by
  refine iterOpt_trans (pop_B2_run_hL k (.A 2 :: L) R) ?_
  rfl


lemma rep_B2_A2_ne_A2 (k : ℕ) (L : List SBlock) (h : k ≥ 1 ∨ L ≠ []) :
    List.replicate k (.B 2) ++ (.A 2 :: L) ≠ [.A 2] := by
  rcases k with _ | k
  · simp only [List.replicate_zero, List.nil_append, ne_eq, List.cons.injEq, true_and]
    rcases h with hk | hL
    · omega
    · exact hL
  · rw [List.replicate_succ, List.cons_append]
    intro hc; injection hc with h1 _; cases h1


lemma pop_B1_B2_A2_hL (k : ℕ) (L : List SBlock) (R : List ℕ) :
    iterOpt step_sq (k + 2) (.hL, .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), R) =
      some (.hL, L, 3 :: (List.replicate (2 * k + 1) 1 ++ (0 :: R))) := by
  rw [show k + 2 = 1 + (k + 1) by omega]
  have h1 : iterOpt step_sq 1 (.hL, .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), R) =
      some (.hL, List.replicate k (.B 2) ++ (.A 2 :: L), 1 :: 0 :: R) := rfl
  refine iterOpt_trans h1 ?_
  rw [pop_B2_A2_hL k L (1 :: 0 :: R), replicate_append_cons_same]


lemma bounce_hL_suffix (S : List SBlock) (hS : S = [] ∨ S = [.A 0, .A 2]) (R : List ℕ) :
    iterOpt step_sq 1 (.hL, S, R) = some (.h10B, [.A 1], R) := by
  rcases hS with rfl | rfl <;> rfl


lemma double3_reduction (R : List ℕ) :
    SqReachesPlus (3 :: 3 :: R) (1 :: 1 :: R) :=
  ⟨4, by decide, rfl⟩

-- ----------------------------------------------------------------------------
-- Layer 3B: Loop Templates, Tail Reflections, Contraction Loops & Bridges
-- ----------------------------------------------------------------------------


def CfgSqReachesPlus (c₁ c₂ : CfgSq) : Prop :=
  ∃ k > 0, iterOpt step_sq k c₁ = some c₂


def CfgSqReachesStar (c₁ c₂ : CfgSq) : Prop :=
  ∃ k, iterOpt step_sq k c₁ = some c₂


lemma cfgSqReachesStar_of_iterOpt {k : ℕ} {c₁ c₂ : CfgSq}
    (h : iterOpt step_sq k c₁ = some c₂) : CfgSqReachesStar c₁ c₂ :=
  ⟨k, h⟩


lemma cfgSqReachesPlus_of_iterOpt {k : ℕ} {c₁ c₂ : CfgSq}
    (hk : k > 0) (h : iterOpt step_sq k c₁ = some c₂) : CfgSqReachesPlus c₁ c₂ :=
  ⟨k, hk, h⟩


lemma cfgSqReachesPlus_trans {c₁ c₂ c₃ : CfgSq}
    (h₁ : CfgSqReachesPlus c₁ c₂) (h₂ : CfgSqReachesPlus c₂ c₃) :
    CfgSqReachesPlus c₁ c₃ := by
  rcases h₁ with ⟨k₁, hk₁, hs₁⟩
  rcases h₂ with ⟨k₂, hk₂, hs₂⟩
  exact ⟨k₁ + k₂, by omega, iterOpt_trans hs₁ hs₂⟩


lemma cfgSqReachesStar_plus_trans {c₁ c₂ c₃ : CfgSq}
    (h₁ : CfgSqReachesStar c₁ c₂) (h₂ : CfgSqReachesPlus c₂ c₃) :
    CfgSqReachesPlus c₁ c₃ := by
  rcases h₁ with ⟨k₁, hs₁⟩
  rcases h₂ with ⟨k₂, hk₂, hs₂⟩
  exact ⟨k₁ + k₂, by omega, iterOpt_trans hs₁ hs₂⟩


def TailWord (w z δ : ℕ) : List ℕ :=
  List.replicate w 1 ++ (3 :: (List.replicate z 1 ++ [δ, 1]))


def R_tail (w z δ : ℕ) : List ℕ :=
  3 :: TailWord w z δ


def M_sq (v w z δ : ℕ) : List ℕ :=
  3 :: (List.replicate v 1 ++ (2 :: 1 :: R_tail w z δ))


def M2_sq (v w Z δ : ℕ) : List ℕ :=
  3 :: (List.replicate v 1 ++ (2 :: R_tail w Z δ))


def H_sq (v w0 z δ : ℕ) : List ℕ :=
  3 :: (List.replicate v 1 ++ (0 :: R_tail w0 z δ))


def F_sq (u v j w0 z δ : ℕ) : List ℕ :=
  3 :: (List.replicate u 1 ++ (3 :: (List.replicate v 1 ++ (3 :: (List.replicate j 1 ++ (0 :: R_tail w0 z δ))))))


def G_sq (v j w z δ : ℕ) : List ℕ :=
  3 :: (List.replicate v 1 ++ (3 :: (List.replicate j 1 ++ (0 :: R_tail w z δ))))


def psiTilde (w z : ℕ) : ℕ × ℕ :=
  if w % 2 = 0 then (w + 1, z) else (w - 1, z + 2)


def psiShift (w z : ℕ) : ℕ × ℕ :=
  if w % 2 = 0 then (w + 1, z + 2) else (w - 1, z + 4)

-- ----------------------------------------------------------------------------
-- Multi-Step Lift Lemmas (step_sq -> step_5mode -> step_blk -> target_tm)
-- ----------------------------------------------------------------------------

lemma iterOpt_step_blk_plus {j : ℕ} (hj : j > 0) {b₁ b₂ : BlkCfg}
    (h : iterOpt step_blk j b₁ = some b₂) :
    (decode_blk b₁) [target_tm]⊢⁺ (decode_blk b₂) := by
  induction j generalizing b₁ with
  | zero => omega
  | succ j ih =>
    rcases hs : step_blk b₁ with _ | bm
    · simp [hs] at h
    · rcases j with _ | j'
      · simp [hs] at h; subst h
        exact step_blk_correct b₁ bm hs
      · simp only [iterOpt_succ, hs, option_some_bind] at h
        exact stepPlus_trans (step_blk_correct b₁ bm hs) (ih (by omega) h)

lemma step_5mode_preserves_guard (c c' : Cfg5)
    (hguard : c.1 ≠ .hL → c.2.1 ≠ [])
    (h : step_5mode c = some c') :
    c'.1 ≠ .hL → c'.2.1 ≠ [] := by
  rcases c with ⟨m, ls, rs⟩
  cases m with
  | hL =>
    rcases ls with _ | ⟨sb, lsp⟩
    · simp [step_5mode] at h; subst h; simp
    · cases sb with
      | A k => simp [step_5mode] at h; subst h; simp
      | B k =>
        rcases k with _ | k <;> (simp [step_5mode] at h; subst h; simp)
  | h10B =>
    have hls : ls ≠ [] := hguard (by intro hc; cases hc)
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | _ | a <;>
        (simp [step_5mode] at h; subst h; intro _; first | exact hls | exact incTop_nonempty _ _ | simp)
  | h100F =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_5mode] at h
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
  | h10F =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h; simp
    · rcases r0 with _ | _ | _ | _ | a
      · simp [step_5mode] at h
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
      · simp [step_5mode] at h; subst h; simp
  | h1E =>
    rcases rs with _ | ⟨r0, rsp⟩
    · simp [step_5mode] at h; subst h; simp
    · rcases r0 with _ | _ | a
      · simp [step_5mode] at h; subst h; intro _; exact incTop_nonempty _ _
      · simp [step_5mode] at h; subst h; intro _; exact incTop_nonempty _ _
      · simp [step_5mode] at h; subst h; simp

lemma iterOpt_step_5mode_lift {k : ℕ} (hk : k > 0) {c₁ c₂ : Cfg5}
    (hguard : c₁.1 ≠ .hL → c₁.2.1 ≠ [])
    (h : iterOpt step_5mode k c₁ = some c₂) :
    (decode_blk (Phi c₁)) [target_tm]⊢⁺ (decode_blk (Phi c₂)) := by
  induction k generalizing c₁ with
  | zero => omega
  | succ k ih =>
    rcases hs : step_5mode c₁ with _ | cm
    · simp [hs] at h
    · obtain ⟨j, hj, hblk⟩ := step_5mode_correct c₁ cm hguard hs
      have hp1 := iterOpt_step_blk_plus hj hblk
      rcases k with _ | k'
      · simp [hs] at h; subst h; exact hp1
      · simp only [iterOpt_succ, hs, option_some_bind] at h
        have hg' := step_5mode_preserves_guard c₁ cm hguard hs
        exact stepPlus_trans hp1 (ih (by omega) hg' h)

lemma iterOpt_step_sq_lift {k : ℕ} (hk : k > 0) (n : ℕ) {c₁ c₂ : CfgSq}
    (hguard : c₁.1 ≠ .hL → c₁.2.1 ≠ [])
    (h : iterOpt step_sq k c₁ = some c₂) :
    ∃ n', (decode_sq n c₁) [target_tm]⊢⁺ (decode_sq n' c₂) := by
  induction k generalizing n c₁ with
  | zero => omega
  | succ k ih =>
    rcases hs : step_sq c₁ with _ | cm
    · simp [hs] at h
    · obtain ⟨n_mid, j, hj, h5⟩ := step_sq_lift n c₁ cm hguard hs
      have hp1 : (decode_sq n c₁) [target_tm]⊢⁺ (decode_sq n_mid cm) :=
        iterOpt_step_5mode_lift hj (psi_sq_guard n c₁) h5
      rcases k with _ | k'
      · simp [hs] at h; subst h; exact ⟨n_mid, hp1⟩
      · simp only [iterOpt_succ, hs, option_some_bind] at h
        have hg' := step_sq_preserves_guard c₁ cm hguard hs
        obtain ⟨n', hp2⟩ := ih (by omega) n_mid hg' h
        exact ⟨n', stepPlus_trans hp1 hp2⟩

lemma sqReachesPlus_to_tm {R₁ R₂ : List ℕ} (h : SqReachesPlus R₁ R₂) (n : ℕ) :
    ∃ n', (decode_sq n (.h10B, [.A 1], R₁)) [target_tm]⊢⁺ (decode_sq n' (.h10B, [.A 1], R₂)) := by
  rcases h with ⟨k, hk, hiter⟩
  exact iterOpt_step_sq_lift hk n (by simp) hiter

def c50_sq : CfgSq := (.hL, [.B 2, .A 2, .A 0, .A 2], [1, 4, 1])
def c100_sq : CfgSq := (.hL, [.B 0, .A 2, .A 0, .A 2], [1, 1, 4, 1])
def c150_sq : CfgSq := (.hL, [.A 2, .A 2, .A 0, .A 2], [1, 0, 1, 0, 3, 4, 1])
def c200_sq : CfgSq := (.h10B, [.A 1, .A 1, .B 2, .A 2, .A 0, .A 2], [1, 1, 2, 1])
def c250_sq : CfgSq := (.h10B, [.A 1, .A 2, .A 0, .B 3, .A 2], [1, 1, 0, 1])
def c300_sq : CfgSq := (.hL, [.A 0, .B 1, .B 2, .B 2, .A 2, .A 2, .A 1, .A 2, .A 0, .A 2], [])

lemma init_reaches_c319 :
    ∃ n₀, (init []) [target_tm]⊢* (decode_sq n₀ c319_sq) := by
  have h1 : (init []) [target_tm]⊢* (decode_blk (.h11D, [.L10, .L1], [])) :=
    ReachesIn.to_star init_reaches_blk0
  have h2_iter : iterOpt step_blk 35 (.h11D, [.L10, .L1], []) = some (Phi (Psi_sq 0 c0_sq)) := rfl
  have h2 : (decode_blk (.h11D, [.L10, .L1], [])) [target_tm]⊢⁺ (decode_sq 0 c0_sq) :=
    iterOpt_step_blk_plus (by decide) h2_iter
  have s1 : iterOpt step_sq 50 c0_sq = some c50_sq := rfl
  have s2 : iterOpt step_sq 50 c50_sq = some c100_sq := rfl
  have s3 : iterOpt step_sq 50 c100_sq = some c150_sq := rfl
  have s4 : iterOpt step_sq 50 c150_sq = some c200_sq := rfl
  have s5 : iterOpt step_sq 50 c200_sq = some c250_sq := rfl
  have s6 : iterOpt step_sq 50 c250_sq = some c300_sq := rfl
  have s7 : iterOpt step_sq 19 c300_sq = some c319_sq := rfl
  have h3_iter : iterOpt step_sq 319 c0_sq = some c319_sq :=
    iterOpt_trans s1 (iterOpt_trans s2 (iterOpt_trans s3
      (iterOpt_trans s4 (iterOpt_trans s5 (iterOpt_trans s6 s7)))))
  obtain ⟨n₀, h3⟩ := iterOpt_step_sq_lift (by decide) 0 (by intro hc; exact absurd rfl hc) h3_iter
  exact ⟨n₀, stepStar_trans h1 (stepStar_trans (stepPlus_stepStar h2) (stepPlus_stepStar h3))⟩

lemma psiTilde_psiTilde (w z : ℕ) :
    psiTilde (psiTilde w z).1 (psiTilde w z).2 = (w, z + 2) := by
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw
  · have h1 : psiTilde w z = (w + 1, z) := by simp [psiTilde, hw]
    rw [h1]; simp [psiTilde, show (w + 1) % 2 = 1 by omega]
  · have h1 : psiTilde w z = (w - 1, z + 2) := by simp [psiTilde, hw]
    rw [h1]; simp [psiTilde, show (w - 1) % 2 = 0 by omega]; omega


lemma psiTilde_snd_odd (w z : ℕ) (hz : z % 2 = 1) :
    (psiTilde w z).2 % 2 = 1 := by
  try dsimp [psiTilde]
  split_ifs <;> omega


lemma psiTilde_add_two (w z : ℕ) :
    psiTilde w (z + 2) = psiShift w z := rfl


lemma psiShift_eq_psiTilde_step (w z : ℕ) :
    psiShift w z = ((psiTilde w z).1, (psiTilde w z).2 + 2) := by
  try dsimp [psiTilde, psiShift]
  split_ifs <;> rfl


lemma replicate_succ_append {α : Type*} (k : ℕ) (x : α) (R : List α) :
    List.replicate (k + 1) x ++ R = List.replicate k x ++ (x :: R) := by
  rw [← replicate_append_cons_same]


def stackP1 (u : ℕ) (L : List SBlock) : List SBlock :=
  List.replicate u (.B 2) ++ (.A 2 :: .A 0 :: .A 2 :: L)


lemma prefix_P1_scan (u : ℕ) (L : List SBlock) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, 3 :: (List.replicate (2 * (u + 1)) 1 ++ (3 :: R)))
      (.h10B, .A 1 :: stackP1 u L, 1 :: R) := by
  have h1 : CfgSqReachesPlus
      (.h10B, .A 1 :: L, 3 :: (List.replicate (2 * (u + 1)) 1 ++ (3 :: R)))
      (.h1E, .A 0 :: .A 0 :: .A 2 :: L, List.replicate (2 * (u + 1)) 1 ++ (3 :: R)) :=
    ⟨1, by decide, rfl⟩
  have h2 := cfgSqReachesPlus_of_iterOpt (by omega)
    (scan_ones_h1E u (.A 0 :: .A 0 :: .A 2 :: L) (3 :: R))
  have h3 : CfgSqReachesPlus
      (.h1E, .B 0 :: (List.replicate u (.B 2) ++ (.A 2 :: .A 0 :: .A 2 :: L)), 3 :: R)
      (.h10B, .A 1 :: stackP1 u L, 1 :: R) :=
    ⟨2, by decide, rfl⟩
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3


lemma prefix_P1_pop (u : ℕ) (L : List SBlock) (R' : List ℕ) :
    CfgSqReachesPlus
      (.hL, stackP1 u L, R')
      (.hL, .A 0 :: .A 2 :: L, 3 :: (List.replicate (2 * u) 1 ++ R')) :=
  cfgSqReachesPlus_of_iterOpt (by omega) (pop_B2_A2_hL u (.A 0 :: .A 2 :: L) R')


def stackP2 (m : ℕ) (L : List SBlock) : List SBlock :=
  List.replicate m (.B 2) ++ (.A 2 :: L)


lemma prefix_P2_scan (m : ℕ) (L : List SBlock) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, 1 :: (List.replicate (2 * m) 1 ++ (3 :: R)))
      (.h10B, .A 1 :: stackP2 m L, 1 :: R) := by
  rw [← List.cons_append, ← List.replicate_succ, replicate_succ_append]
  have h1 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m L (1 :: 3 :: R))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes m L, 1 :: 3 :: R)
      (.h10B, .A 1 :: stackP2 m L, 1 :: R) :=
    ⟨3, by decide, by simp [iterOpt, step_sq, stackP2]⟩
  exact cfgSqReachesStar_plus_trans h1 h2


lemma prefix_P2_pop (m : ℕ) (L : List SBlock) (R' : List ℕ) :
    CfgSqReachesPlus
      (.hL, stackP2 m L, R')
      (.hL, L, 3 :: (List.replicate (2 * m) 1 ++ R')) :=
  cfgSqReachesPlus_of_iterOpt (by omega) (pop_B2_A2_hL m L R')


def stackP3 (m : ℕ) (S : List SBlock) : List SBlock :=
  .A 0 :: (List.replicate m (.B 2) ++ (.A 2 :: S))


lemma prefix_P3_scan_from_S (m : ℕ) (S : List SBlock) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: S, List.replicate (2 * m) 1 ++ (3 :: 1 :: R))
      (.h10B, .A 1 :: stackP3 m S, R) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any m S (3 :: 1 :: R))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes m S, 3 :: 1 :: R)
      (.h10B, .A 1 :: stackP3 m S, R) :=
    ⟨2, by decide, by simp [iterOpt, step_sq, stackP3]⟩
  exact cfgSqReachesStar_plus_trans h1 h2


lemma prefix_P3_scan (m : ℕ) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, [.A 1], 3 :: (List.replicate (2 * m + 1) 1 ++ (3 :: 1 :: R)))
      (.h10B, .A 1 :: stackP3 m [.A 0, .A 2], R) := by
  rw [List.replicate_succ, List.cons_append]
  have h0 : CfgSqReachesPlus
      (.h10B, [.A 1], 3 :: 1 :: (List.replicate (2 * m) 1 ++ (3 :: 1 :: R)))
      (.h10B, .A 1 :: [.A 0, .A 2], List.replicate (2 * m) 1 ++ (3 :: 1 :: R)) :=
    ⟨2, by decide, rfl⟩
  exact cfgSqReachesPlus_trans h0 (prefix_P3_scan_from_S m [.A 0, .A 2] R)


lemma cons_replicate_append {α : Type*} (k : ℕ) (x : α) (R : List α) :
    x :: (List.replicate k x ++ R) = List.replicate (k + 1) x ++ R := by
  rw [List.replicate_succ, List.cons_append]


lemma cons_replicate_odd_append {α : Type*} (j : ℕ) (x : α) (R : List α) :
    x :: (List.replicate (2 * j + 1) x ++ R) = List.replicate (2 * (j + 1)) x ++ R :=
  cons_replicate_append (2 * j + 1) x R


lemma prefix_M2_scan (u : ℕ) (L : List SBlock) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, 3 :: (List.replicate (2 * (u + 1)) 1 ++ (2 :: R)))
      (.h10B, .A 1 :: stackP1 u L, 0 :: R) := by
  have h1 : CfgSqReachesPlus
      (.h10B, .A 1 :: L, 3 :: (List.replicate (2 * (u + 1)) 1 ++ (2 :: R)))
      (.h1E, .A 0 :: .A 0 :: .A 2 :: L, List.replicate (2 * (u + 1)) 1 ++ (2 :: R)) :=
    ⟨1, by decide, rfl⟩
  have h2 := cfgSqReachesPlus_of_iterOpt (by omega)
    (scan_ones_h1E u (.A 0 :: .A 0 :: .A 2 :: L) (2 :: R))
  have h3 : CfgSqReachesPlus
      (.h1E, .B 0 :: (List.replicate u (.B 2) ++ (.A 2 :: .A 0 :: .A 2 :: L)), 2 :: R)
      (.h10B, .A 1 :: stackP1 u L, 0 :: R) :=
    ⟨2, by decide, rfl⟩
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3


def enc_odd (a b c d : ℕ) : List ℕ :=
  3 :: (List.replicate a 1 ++ (0 :: TailWord b c d))


def enc_even (a b c d : ℕ) : List ℕ :=
  List.replicate (a - 1) 1 ++ (0 :: 1 :: R_tail b c d)


def R_mid (c d : ℕ) : List ℕ :=
  if d = 0 then 3 :: (List.replicate c 1 ++ [3, 1])
  else R_tail (c - 1) 1 0


lemma pass1_turnaround_d0 (r : ℕ) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r + 1) 1 ++ [0, 1])
      (.hL, L, 3 :: (List.replicate (2 * r + 1) 1 ++ [3, 1])) := by
  rw [replicate_succ_append (2 * r)]
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L [1, 0, 1])
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r L, [1, 0, 1])
      (.hL, List.replicate r (.B 2) ++ (.A 2 :: L), [1, 3, 1]) :=
    ⟨6, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL r L [1, 3, 1])
  rw [replicate_append_cons_same (2 * r)] at h3
  exact cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3


lemma pass1_turnaround_d2 (r : ℕ) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r + 1) 1 ++ [2, 1])
      (.hL, L, R_tail (2 * r) 1 0) := by
  rw [replicate_succ_append (2 * r)]
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L [1, 2, 1])
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r L, [1, 2, 1])
      (.hL, List.replicate r (.B 2) ++ (.A 2 :: L), [3, 1, 0, 1]) :=
    ⟨9, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL r L [3, 1, 0, 1])
  exact cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3


lemma pass1_turnaround (r d : ℕ) (hd : d = 0 ∨ d = 2) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r + 1) 1 ++ [d, 1])
      (.hL, L, R_mid (2 * r + 1) d) := by
  rcases hd with rfl | rfl
  · simpa [R_mid] using pass1_turnaround_d0 r L
  · simpa [R_mid] using pass1_turnaround_d2 r L


lemma pass2_turnaround (r : ℕ) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r + 1) 1 ++ [3, 1])
      (.hL, L, R_tail (2 * r) 1 2) := by
  rw [replicate_succ_append (2 * r)]
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L [1, 3, 1])
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r L, [1, 3, 1])
      (.hL, List.replicate r (.B 2) ++ (.A 2 :: L), [3, 1, 2, 1]) :=
    ⟨9, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL r L [3, 1, 2, 1])
  exact cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3


lemma prefix_P2_scan_2 (m : ℕ) (L : List SBlock) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, 1 :: (List.replicate (2 * m) 1 ++ (2 :: R)))
      (.h10B, .A 1 :: stackP2 m L, 0 :: R) := by
  rw [← List.cons_append, ← List.replicate_succ, replicate_succ_append]
  have h1 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m L (1 :: 2 :: R))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes m L, 1 :: 2 :: R)
      (.h10B, .A 1 :: stackP2 m L, 0 :: R) :=
    ⟨3, by decide, by simp [iterOpt, step_sq, stackP2]⟩
  exact cfgSqReachesStar_plus_trans h1 h2


lemma psiShift_psiTilde_add (w z k : ℕ) :
    psiShift (psiTilde w z).1 ((psiTilde w z).2 + 2 * k) = (w, z + 2 * k + 4) := by
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw
  · have h1 : psiTilde w z = (w + 1, z) := by simp [psiTilde, hw]
    rw [h1]; dsimp [psiShift]; rw [if_neg (by omega)]
  · have h1 : psiTilde w z = (w - 1, z + 2) := by simp [psiTilde, hw]
    rw [h1]; dsimp [psiShift]; rw [if_pos (by omega)]; exact Prod.ext (by omega) (by omega)


lemma exit_3_2 (R : List ℕ) :
    SqReachesPlus (3 :: 2 :: R) (1 :: 0 :: R) :=
  ⟨4, by decide, rfl⟩


lemma exit_odd_0_3 (r : ℕ) (R : List ℕ) :
    SqReachesPlus
      (List.replicate (2 * r + 1) 1 ++ (0 :: 3 :: R))
      (3 :: (List.replicate (2 * r + 1) 1 ++ (0 :: 1 :: R))) := by
  rw [replicate_succ_append (2 * r)]
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r [] (1 :: 0 :: 3 :: R))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r [], 1 :: 0 :: 3 :: R)
      (.hL, .B 1 :: (List.replicate r (.B 2) ++ [.A 2]), 1 :: R) :=
    ⟨3, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B1_B2_A2_hL r [] (1 :: R))
  have h4 := cfgSqReachesPlus_of_iterOpt (by decide)
    (bounce_hL_suffix [] (Or.inl rfl)
      (3 :: (List.replicate (2 * r + 1) 1 ++ (0 :: 1 :: R))))
  exact cfgSqReachesPlus_trans
    (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4


def splitTwoAux : ℕ → ℕ → ℕ × ℕ
  | 0, m => (0, m)
  | fuel + 1, m =>
    if m % 2 = 0 then
      let p := splitTwoAux fuel (m / 2)
      (p.1 + 1, p.2)
    else (0, m)


def splitTwo (m : ℕ) : ℕ × ℕ := splitTwoAux m m


lemma splitTwoAux_eq (f1 f2 m : ℕ) (hm : m ≥ 1) (hf1 : m ≤ f1) (hf2 : m ≤ f2) :
    splitTwoAux f1 m = splitTwoAux f2 m := by
  induction f1 generalizing f2 m with
  | zero => omega
  | succ f1 ih =>
    rcases f2 with _ | f2
    · omega
    · dsimp [splitTwoAux]
      split_ifs with h0
      · rw [ih f2 (m / 2) (by omega) (by omega) (by omega)]
      · rfl


lemma splitTwo_odd (m : ℕ) (hm : m % 2 = 1) : splitTwo m = (0, m) := by
  rcases m with _ | m
  · omega
  · dsimp [splitTwo, splitTwoAux]
    rw [if_neg (by omega)]


lemma splitTwo_two_mul (m : ℕ) (hm : m ≥ 1) :
    splitTwo (2 * m) = ((splitTwo m).1 + 1, (splitTwo m).2) := by
  have h2m : 2 * m = (2 * m - 1) + 1 := by omega
  unfold splitTwo
  rw [h2m]
  try dsimp [splitTwoAux]
  rw [if_pos (by omega), show (2 * m - 1 + 1) / 2 = m by omega]
  rw [splitTwoAux_eq (2 * m - 1) m m hm (by omega) (le_refl m)]


lemma mul_pos_of_pos_of_odd {x a : ℕ} (hx : x ≥ 1) (ha : a % 2 = 1) : x * a ≥ 1 := by
  have ha1 : a ≥ 1 := by omega
  calc x * a ≥ 1 * 1 := Nat.mul_le_mul hx ha1
    _ = 1 := rfl


lemma splitTwo_pow_mul_odd (ν a : ℕ) (ha : a % 2 = 1) :
    splitTwo (2 ^ ν * a) = (ν, a) := by
  induction ν with
  | zero => simp [splitTwo_odd a ha]
  | succ ν ih =>
    have hpos : 2 ^ ν * a ≥ 1 := mul_pos_of_pos_of_odd Nat.one_le_two_pow ha
    rw [Nat.pow_succ', Nat.mul_assoc, splitTwo_two_mul _ hpos, ih]

-- ----------------------------------------------------------------------------
-- Stage 4A: Even-Run Turnarounds, Tail Reflection & Separators
-- ----------------------------------------------------------------------------

lemma turnaround_even_ones_d0 (r : ℕ) (L' : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L', List.replicate (2 * r) 1 ++ [0, 1])
      (.hL, L', 3 :: (List.replicate (2 * r + 1) 1 ++ [0, 1])) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L' [0, 1])
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r L', [0, 1])
      (.hL, .B 1 :: (List.replicate r (.B 2) ++ (.A 2 :: L')), [1]) :=
    ⟨4, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega) (pop_B1_B2_A2_hL r L' [1])
  exact cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3

lemma turnaround_even_ones_d2 (r : ℕ) (L' : List SBlock) (hL' : L' ≠ []) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L', List.replicate (2 * r) 1 ++ [2, 1])
      (.hL, L', 3 :: (List.replicate (2 * r + 1) 1 ++ [2, 1])) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L' [2, 1])
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes r L', [2, 1])
      (.hL, .A 0 :: (List.replicate r (.B 2) ++ (.A 2 :: L')), [2, 1]) :=
    ⟨5, by decide, by simp [iterOpt, step_sq]⟩
  have hne := rep_B2_A2_ne_A2 r L' (Or.inr hL')
  have h3 : CfgSqReachesPlus
      (.hL, .A 0 :: (List.replicate r (.B 2) ++ (.A 2 :: L')), [2, 1])
      (.hL, List.replicate r (.B 2) ++ (.A 2 :: L'), [1, 2, 1]) :=
    ⟨1, by decide, by simp [iterOpt, step_sq_hL_A0 _ hne]⟩
  have h4 := cfgSqReachesPlus_of_iterOpt (by omega) (pop_B2_A2_hL r L' [1, 2, 1])
  rw [replicate_append_cons_same (2 * r)] at h4
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4

lemma turnaround_even_ones (r d : ℕ) (hd : d = 0 ∨ d = 2) (L' : List SBlock) (hL' : L' ≠ []) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L', List.replicate (2 * r) 1 ++ [d, 1])
      (.hL, L', 3 :: (List.replicate (2 * r + 1) 1 ++ [d, 1])) := by
  rcases hd with rfl | rfl
  · exact turnaround_even_ones_d0 r L'
  · exact turnaround_even_ones_d2 r L' hL'

lemma tail_reflect (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2)
    (L : List SBlock) (hL : L ≠ []) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, TailWord w z d)
      (.hL, L, R_tail (psiTilde w z).1 (psiTilde w z).2 d) := by
  have hz_eq : z = 2 * (z / 2) + 1 := by omega
  set s := z / 2
  rcases Nat.mod_two_eq_zero_or_one w with hw | hw
  · have hw_eq : w = 2 * (w / 2) := by omega
    set k := w / 2
    have hpsi : psiTilde w z = (2 * k + 1, 2 * s + 1) := by
      ext <;> dsimp only [psiTilde] <;> split_ifs <;> omega
    rw [hpsi]
    have htw : TailWord w z d = List.replicate (2 * k) 1 ++ (3 :: 1 :: (List.replicate (2 * s) 1 ++ [d, 1])) := by
      simp [TailWord, hw_eq, hz_eq, List.replicate_succ, List.cons_append]
    rw [htw]
    have h1 := prefix_P3_scan_from_S k L (List.replicate (2 * s) 1 ++ [d, 1])
    have h2 := turnaround_even_ones s d hd (stackP3 k L) (by simp [stackP3])
    have hne := rep_B2_A2_ne_A2 k L (Or.inr hL)
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 k L, 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))
        (.hL, List.replicate k (.B 2) ++ (.A 2 :: L), 1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1])) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL k L (1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1])))
    rw [replicate_append_cons_same (2 * k)] at h4
    simpa [R_tail, TailWord] using
      cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  · have hw_eq : w = 2 * (w / 2) + 1 := by omega
    set k := w / 2
    have hpsi : psiTilde w z = (2 * k, 2 * (s + 1) + 1) := by
      ext <;> dsimp only [psiTilde] <;> split_ifs <;> omega
    rw [hpsi]
    have htw : TailWord w z d = 1 :: (List.replicate (2 * k) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))) := by
      rw [TailWord, hw_eq, hz_eq, Nat.add_comm (2 * k) 1, List.replicate_add]
      rfl
    rw [htw]
    have h1 := prefix_P2_scan k L (List.replicate (2 * s + 1) 1 ++ [d, 1])
    rw [cons_replicate_odd_append s 1 [d, 1]] at h1
    have h2 := turnaround_even_ones (s + 1) d hd (stackP2 k L) (by cases k <;> simp [stackP2])
    have h3 := prefix_P2_pop k L (3 :: (List.replicate (2 * (s + 1) + 1) 1 ++ [d, 1]))
    simpa [R_tail, TailWord] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3

lemma sep_0 (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, 0 :: R_tail w z d)
      (.hL, L, 2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) := by
  have h1 : CfgSqReachesPlus
      (.h10B, .A 1 :: L, 0 :: 3 :: TailWord w z d)
      (.h10B, .A 1 :: .A 0 :: .A 1 :: L, TailWord w z d) :=
    ⟨2, by decide, rfl⟩
  have h2 := tail_reflect w z d hz hd (.A 0 :: .A 1 :: L) (by simp)
  have h3 : CfgSqReachesPlus
      (.hL, .A 0 :: .A 1 :: L, R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.hL, L, 2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) :=
    ⟨2, by decide, rfl⟩
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3

lemma sep_even_0 (k : ℕ) (L : List SBlock) (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * (k + 1)) 1 ++ (0 :: R_tail w z d))
      (.hL, L, 3 :: (List.replicate (2 * k + 1) 1 ++ (0 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any (k + 1) L (0 :: 3 :: TailWord w z d))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes (k + 1) L, 0 :: 3 :: TailWord w z d)
      (.h10B, .A 1 :: .A 0 :: .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), TailWord w z d) :=
    ⟨2, by decide, rfl⟩
  have h3 := tail_reflect w z d hz hd (.A 0 :: .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L))) (by simp)
  have h4 : CfgSqReachesPlus
      (.hL, .A 0 :: .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.hL, .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) :=
    ⟨1, by decide, rfl⟩
  have h5 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B1_B2_A2_hL k L (1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5

lemma sep_even_01 (k : ℕ) (L : List SBlock) (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * k) 1 ++ (0 :: 1 :: R_tail w z d))
      (.hL, L, 3 :: (List.replicate (2 * k + 1) 1 ++ (0 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k L (0 :: 1 :: 3 :: TailWord w z d))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes k L, 0 :: 1 :: 3 :: TailWord w z d)
      (.h10B, .A 1 :: .B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), TailWord w z d) :=
    ⟨3, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := tail_reflect w z d hz hd (.B 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L))) (by simp)
  have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B1_B2_A2_hL k L (R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4

lemma sep_even_2 (k : ℕ) (L : List SBlock) (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * k) 1 ++ (2 :: R_tail w z d))
      (.hL, L, 3 :: (List.replicate (2 * k) 1 ++ (2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k L (2 :: 3 :: TailWord w z d))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes k L, 2 :: 3 :: TailWord w z d)
      (.h10B, .A 1 :: .A 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), TailWord w z d) :=
    ⟨2, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := tail_reflect w z d hz hd (.A 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L))) (by simp)
  have h4 : CfgSqReachesPlus
      (.hL, .A 1 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.hL, List.replicate k (.B 2) ++ (.A 2 :: L), 2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) :=
    ⟨1, by decide, rfl⟩
  have h5 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL k L (2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5

lemma sep_even_21 (k : ℕ) (L : List SBlock) (hkL : k ≥ 1 ∨ L ≠ [])
    (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * k) 1 ++ (2 :: 1 :: R_tail w z d))
      (.hL, L, 3 :: (List.replicate (2 * k + 1) 1 ++ (2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))) := by
  have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any k L (2 :: 1 :: 3 :: TailWord w z d))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes k L, 2 :: 1 :: 3 :: TailWord w z d)
      (.h10B, .A 1 :: .A 1 :: .A 0 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), TailWord w z d) :=
    ⟨3, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := tail_reflect w z d hz hd (.A 1 :: .A 0 :: (List.replicate k (.B 2) ++ (.A 2 :: L))) (by simp)
  have hne := rep_B2_A2_ne_A2 k L hkL
  have h4 : CfgSqReachesPlus
      (.hL, .A 1 :: .A 0 :: (List.replicate k (.B 2) ++ (.A 2 :: L)), R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.hL, List.replicate k (.B 2) ++ (.A 2 :: L), 1 :: 2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) := by
    refine ⟨2, by decide, ?_⟩
    dsimp only [iterOpt]
    have hs1 : step_sq (.hL, .A 1 :: .A 0 :: (List.replicate k (.B 2) ++ (.A 2 :: L)),
        R_tail (psiTilde w z).1 (psiTilde w z).2 d) =
        some (.hL, .A 0 :: (List.replicate k (.B 2) ++ (.A 2 :: L)),
          2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) := rfl
    rw [hs1]; dsimp
    rw [step_sq_hL_A0 _ hne]; rfl
  have h5 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL k L (1 :: 2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  rw [replicate_append_cons_same (2 * k)] at h5
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5

lemma sep_21_nil (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (2 :: 1 :: R_tail w z d) (2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) := by
  have h1 : CfgSqReachesPlus
      (.h10B, [.A 1], 2 :: 1 :: 3 :: TailWord w z d)
      (.h10B, [.A 1, .A 1, .A 0, .A 2], TailWord w z d) :=
    ⟨3, by decide, rfl⟩
  have h2 := tail_reflect w z d hz hd [.A 1, .A 0, .A 2] (by simp)
  have h3 : CfgSqReachesPlus
      (.hL, [.A 1, .A 0, .A 2], R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.h10B, [.A 1], 2 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) :=
    ⟨2, by decide, rfl⟩
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3

-- ----------------------------------------------------------------------------
-- Stage 4B: Contraction Loops, Bridges, Phase 1, Phase 2 & Even Cascade
-- ----------------------------------------------------------------------------

lemma bounce_from_A0A2 {R₁ R₂ : List ℕ}
    (h : CfgSqReachesPlus (.h10B, [.A 1], R₁) (.hL, [.A 0, .A 2], R₂)) :
    SqReachesPlus R₁ R₂ :=
  cfgSqReachesPlus_trans h (cfgSqReachesPlus_of_iterOpt (by decide) (bounce_hL_suffix [.A 0, .A 2] (Or.inr rfl) R₂))

lemma bounce_from_nil {R₁ R₂ : List ℕ}
    (h : CfgSqReachesPlus (.h10B, [.A 1], R₁) (.hL, [], R₂)) :
    SqReachesPlus R₁ R₂ :=
  cfgSqReachesPlus_trans h (cfgSqReachesPlus_of_iterOpt (by decide) (bounce_hL_suffix [] (Or.inl rfl) R₂))

lemma prefix_odd_3 (m : ℕ) (R : List ℕ) :
    CfgSqReachesPlus
      (.h10B, [.A 1], 3 :: (List.replicate (2 * m + 1) 1 ++ R))
      (.h10B, .A 1 :: [.A 0, .A 2], List.replicate (2 * m) 1 ++ R) := by
  rw [Nat.add_comm (2 * m) 1, List.replicate_add]
  exact ⟨2, by decide, rfl⟩

lemma M2_sq_odd_step (m w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (M2_sq (2 * m + 1) w Z d) (M2_sq (2 * m) (psiTilde w Z).1 (psiTilde w Z).2 d) := by
  apply bounce_from_A0A2
  exact cfgSqReachesPlus_trans
    (prefix_odd_3 m (2 :: R_tail w Z d))
    (sep_even_2 m [.A 0, .A 2] w Z d hZ hd)

lemma M_sq_odd_to_M2 (m w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (M_sq (2 * m + 1) w z d) (M2_sq (2 * m) w (z + 2) d) := by
  have hb1 : SqReachesPlus (M_sq (2 * m + 1) w z d)
      (M2_sq (2 * m + 1) (psiTilde w z).1 (psiTilde w z).2 d) := by
    apply bounce_from_A0A2
    exact cfgSqReachesPlus_trans
      (prefix_odd_3 m (2 :: 1 :: R_tail w z d))
      (sep_even_21 m [.A 0, .A 2] (Or.inr (by simp)) w z d hz hd)
  have hb2 := M2_sq_odd_step m (psiTilde w z).1 (psiTilde w z).2 d (psiTilde_snd_odd w z hz) hd
  rw [psiTilde_psiTilde] at hb2
  exact sqReachesPlus_trans hb1 hb2

lemma loop_L1F (u v j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (F_sq (2 * u + 4) (2 * v) (2 * j + 1) w z d)
      (F_sq (2 * u) (2 * v) (2 * j + 3) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (F_sq (2 * u + 4) (2 * v) (2 * j + 1) w z d)
      (3 :: (List.replicate (2 * u + 2) 1 ++ (3 :: (List.replicate (2 * v) 1 ++
        (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))))) := by
    apply bounce_from_A0A2
    have h1 : CfgSqReachesPlus
        (.h10B, [.A 1], F_sq (2 * u + 4) (2 * v) (2 * j + 1) w z d)
        (.h10B, .A 1 :: stackP1 (u + 1) [], 1 :: (List.replicate (2 * v) 1 ++
          (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))))) := by
      simpa [F_sq, show 2 * u + 4 = 2 * (u + 1 + 1) by omega] using
        prefix_P1_scan (u + 1) [] (List.replicate (2 * v) 1 ++
          (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))))
    have h2 := prefix_P2_scan v (stackP1 (u + 1) []) (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))
    rw [cons_replicate_odd_append j 1 (0 :: R_tail w z d)] at h2
    have h3 := sep_even_0 j (stackP2 v (stackP1 (u + 1) [])) w z d hz hd
    have h4 := prefix_P2_pop v (stackP1 (u + 1) [])
      (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
    have h5 := prefix_P1_pop (u + 1) []
      (3 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5
  have hb2 : SqReachesPlus
      (3 :: (List.replicate (2 * u + 2) 1 ++ (3 :: (List.replicate (2 * v) 1 ++
        (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))))
      (F_sq (2 * u) (2 * v) (2 * j + 3) w (z + 2) d) := by
    apply bounce_from_A0A2
    have h1 := prefix_P1_scan u [] (List.replicate (2 * v) 1 ++
      (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))
    have h2 := prefix_P2_scan v (stackP1 u []) (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))
    rw [cons_replicate_odd_append j 1 (0 :: 1 :: R_tail wt zt d)] at h2
    have h3 := sep_even_01 (j + 1) (stackP2 v (stackP1 u [])) wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h3
    have h4 := prefix_P2_pop v (stackP1 u [])
      (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w (z + 2) d)))
    have h5 := prefix_P1_pop u []
      (3 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w (z + 2) d)))))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5
  exact sqReachesPlus_trans hb1 hb2

lemma bridge_F2 (v j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (F_sq 2 (2 * v) (2 * j + 1) w z d)
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (F_sq 2 (2 * v) (2 * j + 1) w z d)
      (3 :: 3 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))) := by
    apply bounce_from_A0A2
    have h1 := prefix_P1_scan 0 [] (List.replicate (2 * v) 1 ++
      (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))))
    have h2 := prefix_P2_scan v (stackP1 0 []) (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))
    rw [cons_replicate_odd_append j 1 (0 :: R_tail w z d)] at h2
    have h3 := sep_even_0 j (stackP2 v (stackP1 0 [])) w z d hz hd
    have h4 := prefix_P2_pop v (stackP1 0 [])
      (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
    have h5 := prefix_P1_pop 0 []
      (3 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5
  have hb2 := double3_reduction (List.replicate (2 * v) 1 ++
    (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))
  have hb3 : SqReachesPlus
      (1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d) := by
    apply bounce_from_nil
    have heq : 1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))) =
        List.replicate (2 * (v + 1)) 1 ++ (3 :: 1 :: (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d))) := by
      rw [show 2 * (v + 1) = 2 + 2 * v by omega, show 2 * j + 1 = 1 + 2 * j by omega]
      simp [List.replicate_add, List.cons_append]
    rw [heq]
    have h1 := prefix_P3_scan_from_S (v + 1) [] (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d))
    have h2 := sep_even_01 j (stackP3 (v + 1) []) wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h2
    have hne := rep_B2_A2_ne_A2 (v + 1) [] (Or.inl (by omega))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 (v + 1) [], 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d)))
        (.hL, List.replicate (v + 1) (.B 2) ++ [.A 2], 1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL (v + 1) [] (1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))))
    rw [replicate_append_cons_same (2 * (v + 1)), show 2 * (v + 1) + 1 = 2 * v + 3 by omega] at h4
    simpa [G_sq] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  exact sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3

lemma bridge_F0_ge3 (v j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (F_sq 0 (2 * v) (2 * j + 3) w z d)
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (F_sq 0 (2 * v) (2 * j + 3) w z d)
      (1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w z d))))) :=
    double3_reduction (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w z d))))
  have hb2 : SqReachesPlus
      (1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w z d)))))
      (3 :: (List.replicate (2 * v + 3) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))) := by
    apply bounce_from_nil
    have heq : 1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w z d)))) =
        List.replicate (2 * (v + 1)) 1 ++ (3 :: 1 :: (List.replicate (2 * (j + 1)) 1 ++ (0 :: R_tail w z d))) := by
      rw [show 2 * (v + 1) = 2 + 2 * v by omega, show 2 * j + 3 = 1 + 2 * (j + 1) by omega]
      simp [List.replicate_add, List.cons_append]
    rw [heq]
    have h1 := prefix_P3_scan_from_S (v + 1) [] (List.replicate (2 * (j + 1)) 1 ++ (0 :: R_tail w z d))
    have h2 := sep_even_0 j (stackP3 (v + 1) []) w z d hz hd
    have hne := rep_B2_A2_ne_A2 (v + 1) [] (Or.inl (by omega))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 (v + 1) [], 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
        (.hL, List.replicate (v + 1) (.B 2) ++ [.A 2], 1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL (v + 1) [] (1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))
    rw [replicate_append_cons_same (2 * (v + 1)), show 2 * (v + 1) + 1 = 2 * v + 3 by omega] at h4
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  have hb3 : SqReachesPlus
      (3 :: (List.replicate (2 * v + 3) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v + 3) (2 * j + 1) w (z + 2) d) := by
    apply bounce_from_A0A2
    have h1 := prefix_P3_scan (v + 1) (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d))
    have heq1 : 3 :: (List.replicate (2 * (v + 1) + 1) 1 ++ (3 :: 1 :: (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d)))) =
        3 :: (List.replicate (2 * v + 3) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))) := by
      rw [show 2 * (v + 1) + 1 = 2 * v + 3 by omega, show 2 * j + 1 = 1 + 2 * j by omega]
      simp [List.replicate_add]
    rw [heq1] at h1
    have h2 := sep_even_01 j (stackP3 (v + 1) [.A 0, .A 2]) wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h2
    have hne := rep_B2_A2_ne_A2 (v + 1) [.A 0, .A 2] (Or.inl (by omega))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 (v + 1) [.A 0, .A 2], 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d)))
        (.hL, List.replicate (v + 1) (.B 2) ++ (.A 2 :: [.A 0, .A 2]), 1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL (v + 1) [.A 0, .A 2] (1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))))
    rw [replicate_append_cons_same (2 * (v + 1)), show 2 * (v + 1) + 1 = 2 * v + 3 by omega] at h4
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  exact sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3

lemma bridge_F0_1 (v w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (F_sq 0 (2 * v) 1 w z d)
      (M_sq (2 * v + 3) (psiTilde w z).1 (psiTilde w z).2 d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (F_sq 0 (2 * v) 1 w z d)
      (1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: 1 :: 0 :: R_tail w z d))) :=
    double3_reduction (List.replicate (2 * v) 1 ++ (3 :: 1 :: 0 :: R_tail w z d))
  have hb2 : SqReachesPlus
      (1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: 1 :: 0 :: R_tail w z d)))
      (M_sq (2 * v + 3) wt zt d) := by
    apply bounce_from_nil
    have heq : 1 :: 1 :: (List.replicate (2 * v) 1 ++ (3 :: 1 :: 0 :: R_tail w z d)) =
        List.replicate (2 * (v + 1)) 1 ++ (3 :: 1 :: 0 :: R_tail w z d) := by
      rw [show 2 * (v + 1) = 2 + 2 * v by omega]
      simp [List.replicate_add, List.cons_append]
    rw [heq]
    have h1 := prefix_P3_scan_from_S (v + 1) [] (0 :: R_tail w z d)
    have h2 := sep_0 w z d hz hd (stackP3 (v + 1) [])
    have hne := rep_B2_A2_ne_A2 (v + 1) [] (Or.inl (by omega))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 (v + 1) [], 2 :: 1 :: R_tail wt zt d)
        (.hL, List.replicate (v + 1) (.B 2) ++ [.A 2], 1 :: 2 :: 1 :: R_tail wt zt d) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL (v + 1) [] (1 :: 2 :: 1 :: R_tail wt zt d))
    rw [replicate_append_cons_same (2 * (v + 1)), show 2 * (v + 1) + 1 = 2 * v + 3 by omega] at h4
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  exact sqReachesPlus_trans hb1 hb2

lemma loop_L2G (m j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq (2 * m + 1) (2 * j + 3) w z d)
      (G_sq (2 * m + 1) (2 * j + 1) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (G_sq (2 * m + 1) (2 * j + 3) w z d)
      (3 :: (List.replicate (2 * m + 1) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))) := by
    apply bounce_from_A0A2
    have heq : G_sq (2 * m + 1) (2 * j + 3) w z d =
        3 :: (List.replicate (2 * m + 1) 1 ++ (3 :: 1 :: (List.replicate (2 * (j + 1)) 1 ++ (0 :: R_tail w z d)))) := by
      simp [G_sq, show 2 * j + 3 = 1 + 2 * (j + 1) by omega, List.replicate_add]
    rw [heq]
    have h1 := prefix_P3_scan m (List.replicate (2 * (j + 1)) 1 ++ (0 :: R_tail w z d))
    have h2 := sep_even_0 j (stackP3 m [.A 0, .A 2]) w z d hz hd
    have hne := rep_B2_A2_ne_A2 m [.A 0, .A 2] (Or.inr (by simp))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 m [.A 0, .A 2], 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
        (.hL, List.replicate m (.B 2) ++ (.A 2 :: [.A 0, .A 2]), 1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL m [.A 0, .A 2] (1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))
    rw [replicate_append_cons_same (2 * m)] at h4
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  have hb2 : SqReachesPlus
      (3 :: (List.replicate (2 * m + 1) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * m + 1) (2 * j + 1) w (z + 2) d) := by
    apply bounce_from_A0A2
    have heq : List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d) =
        1 :: (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d)) := by
      rw [Nat.add_comm (2 * j) 1, List.replicate_add]; rfl
    rw [heq]
    have h1 := prefix_P3_scan m (List.replicate (2 * j) 1 ++ (0 :: 1 :: R_tail wt zt d))
    have h2 := sep_even_01 j (stackP3 m [.A 0, .A 2]) wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h2
    have hne := rep_B2_A2_ne_A2 m [.A 0, .A 2] (Or.inr (by simp))
    have h3 : CfgSqReachesPlus
        (.hL, stackP3 m [.A 0, .A 2], 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d)))
        (.hL, List.replicate m (.B 2) ++ (.A 2 :: [.A 0, .A 2]), 1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))) :=
      ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
    have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
      (pop_B2_A2_hL m [.A 0, .A 2] (1 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w (z + 2) d))))
    rw [replicate_append_cons_same (2 * m)] at h4
    simpa [G_sq] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4
  exact sqReachesPlus_trans hb1 hb2

lemma G_odd_1_to_M (m w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq (2 * m + 1) 1 w z d)
      (M_sq (2 * m + 1) (psiTilde w z).1 (psiTilde w z).2 d) := by
  apply bounce_from_A0A2
  have h1 := prefix_P3_scan m (0 :: R_tail w z d)
  have h2 := sep_0 w z d hz hd (stackP3 m [.A 0, .A 2])
  have hne := rep_B2_A2_ne_A2 m [.A 0, .A 2] (Or.inr (by simp))
  have h3 : CfgSqReachesPlus
      (.hL, stackP3 m [.A 0, .A 2], 2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d)
      (.hL, List.replicate m (.B 2) ++ (.A 2 :: [.A 0, .A 2]), 1 :: 2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d) :=
    ⟨1, by decide, by simp [stackP3, iterOpt, step_sq_hL_A0 _ hne]⟩
  have h4 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL m [.A 0, .A 2] (1 :: 2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  rw [replicate_append_cons_same (2 * m)] at h4
  simpa [G_sq, M_sq] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4

lemma G_odd_drain (m j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq (2 * m + 1) (2 * j + 1) w z d)
      (M2_sq (2 * m) (psiTilde w z).1 ((psiTilde w z).2 + 2 * j + 2) d) := by
  induction j generalizing z with
  | zero =>
    have h1 := G_odd_1_to_M m w z d hz hd
    have h2 := M_sq_odd_to_M2 m (psiTilde w z).1 (psiTilde w z).2 d (psiTilde_snd_odd w z hz) hd
    exact sqReachesPlus_trans h1 h2
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
    have h1 := loop_L2G m j w z d hz hd
    have h2 := ih (z + 2) (by omega)
    have hpsi : psiTilde w (z + 2) = ((psiTilde w z).1, (psiTilde w z).2 + 2) := by
      rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
    rw [hpsi] at h2
    have htot := sqReachesPlus_trans h1 h2
    rwa [show (psiTilde w z).2 + 2 + 2 * j + 2 = (psiTilde w z).2 + 2 * (j + 1) + 2 by omega] at htot

lemma F_universal_drain (u v j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (F_sq (2 * u) (2 * v) (2 * j + 1) w z d)
      (M2_sq (2 * v + 2) (psiTilde w z).1 ((psiTilde w z).2 + 2 * (u + j + 1)) d) := by
  have h_even_odd : ∀ k u0, u0 = 0 ∨ u0 = 1 → ∀ j0 z0, z0 % 2 = 1 →
      SqReachesPlus
        (F_sq (2 * (2 * k + u0)) (2 * v) (2 * j0 + 1) w z0 d)
        (M2_sq (2 * v + 2) (psiTilde w z0).1 ((psiTilde w z0).2 + 2 * (2 * k + u0 + j0 + 1)) d) := by
    intro k
    induction k with
    | zero =>
      intro u0 hu0 j0 z0 hz0
      rcases hu0 with rfl | rfl
      · rcases j0 with _ | j'
        · have h1 := bridge_F0_1 v w z0 d hz0 hd
          have h2 := M_sq_odd_to_M2 (v + 1) (psiTilde w z0).1 (psiTilde w z0).2 d (psiTilde_snd_odd w z0 hz0) hd
          rw [show 2 * (v + 1) + 1 = 2 * v + 3 by omega, show 2 * (v + 1) = 2 * v + 2 by omega] at h2
          exact sqReachesPlus_trans h1 h2
        · rw [show 2 * (j' + 1) + 1 = 2 * j' + 3 by omega]
          have h1 := bridge_F0_ge3 v j' w z0 d hz0 hd
          have h2 := G_odd_drain (v + 1) j' w (z0 + 2) d (by omega) hd
          have hpsi : psiTilde w (z0 + 2) = ((psiTilde w z0).1, (psiTilde w z0).2 + 2) := by
            rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
          rw [hpsi, show 2 * (v + 1) + 1 = 2 * v + 3 by omega, show 2 * (v + 1) = 2 * v + 2 by omega] at h2
          have htot := sqReachesPlus_trans h1 h2
          rwa [show (psiTilde w z0).2 + 2 + 2 * j' + 2 = (psiTilde w z0).2 + 2 * (2 * 0 + 0 + (j' + 1) + 1) by omega] at htot
      · have h1 := bridge_F2 v j0 w z0 d hz0 hd
        have h2 := G_odd_drain (v + 1) j0 w (z0 + 2) d (by omega) hd
        have hpsi : psiTilde w (z0 + 2) = ((psiTilde w z0).1, (psiTilde w z0).2 + 2) := by
          rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
        rw [hpsi, show 2 * (v + 1) + 1 = 2 * v + 3 by omega, show 2 * (v + 1) = 2 * v + 2 by omega] at h2
        have htot := sqReachesPlus_trans h1 h2
        rwa [show (psiTilde w z0).2 + 2 + 2 * j0 + 2 = (psiTilde w z0).2 + 2 * (2 * 0 + 1 + j0 + 1) by omega] at htot
    | succ k ih =>
      intro u0 hu0 j0 z0 hz0
      have heq : 2 * (2 * (k + 1) + u0) = 2 * (2 * k + u0) + 4 := by omega
      rw [heq]
      have h1 := loop_L1F (2 * k + u0) v j0 w z0 d hz0 hd
      have h2 := ih u0 hu0 (j0 + 1) (z0 + 2) (by omega)
      have hpsi : psiTilde w (z0 + 2) = ((psiTilde w z0).1, (psiTilde w z0).2 + 2) := by
        rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
      rw [hpsi, show 2 * (j0 + 1) + 1 = 2 * j0 + 3 by omega] at h2
      have htot := sqReachesPlus_trans h1 h2
      rwa [show (psiTilde w z0).2 + 2 + 2 * (2 * k + u0 + (j0 + 1) + 1) =
          (psiTilde w z0).2 + 2 * (2 * (k + 1) + u0 + j0 + 1) by omega] at htot
  have hu_split : u = 2 * (u / 2) + u % 2 := by omega
  have hmod : u % 2 = 0 ∨ u % 2 = 1 := Nat.mod_two_eq_zero_or_one u
  have hmain := h_even_odd (u / 2) (u % 2) hmod j z hz
  rwa [← hu_split] at hmain

lemma loop_LH (m w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (H_sq (2 * m + 3) w z d)
      (H_sq (2 * m + 1) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (H_sq (2 * m + 3) w z d)
      (3 :: (List.replicate (2 * m + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))) := by
    apply bounce_from_A0A2
    have h1 := prefix_odd_3 (m + 1) (0 :: R_tail w z d)
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega] at h1
    have h2 := sep_even_0 m [.A 0, .A 2] w z d hz hd
    exact cfgSqReachesPlus_trans h1 h2
  have hb2 : SqReachesPlus
      (3 :: (List.replicate (2 * m + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
      (H_sq (2 * m + 1) w (z + 2) d) := by
    apply bounce_from_A0A2
    have h1 := prefix_odd_3 m (0 :: 1 :: R_tail wt zt d)
    have h2 := sep_even_01 m [.A 0, .A 2] wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h2
    exact cfgSqReachesPlus_trans h1 h2
  exact sqReachesPlus_trans hb1 hb2

lemma H_base_to_M2 (w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (H_sq 1 w z d)
      (M2_sq 0 (psiTilde w z).1 ((psiTilde w z).2 + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus (H_sq 1 w z d) (2 :: 1 :: R_tail wt zt d) := by
    apply bounce_from_A0A2
    exact cfgSqReachesPlus_trans (prefix_odd_3 0 (0 :: R_tail w z d)) (sep_0 w z d hz hd [.A 0, .A 2])
  have hb2 := sep_21_nil wt zt d (psiTilde_snd_odd w z hz) hd
  rw [psiTilde_psiTilde] at hb2
  have hb3 : SqReachesPlus (2 :: R_tail w (z + 2) d) (M2_sq 0 wt (zt + 2) d) := by
    apply bounce_from_nil
    have h := sep_even_2 0 [] w (z + 2) d (by omega) hd
    have hpsi : psiTilde w (z + 2) = (wt, zt + 2) := by
      rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
    rw [hpsi] at h
    exact h
  exact sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3

lemma H_drain (m w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (H_sq (2 * m + 1) w z d)
      (M2_sq 0 (psiTilde w z).1 ((psiTilde w z).2 + 2 * m + 2) d) := by
  induction m generalizing z with
  | zero => exact H_base_to_M2 w z d hz hd
  | succ m ih =>
    rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
    have h1 := loop_LH m w z d hz hd
    have h2 := ih (z + 2) (by omega)
    have hpsi : psiTilde w (z + 2) = ((psiTilde w z).1, (psiTilde w z).2 + 2) := by
      rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
    rw [hpsi] at h2
    have htot := sqReachesPlus_trans h1 h2
    rwa [show (psiTilde w z).2 + 2 + 2 * m + 2 = (psiTilde w z).2 + 2 * (m + 1) + 2 by omega] at htot

-- Phase 1: Unified J_even / J_odd and enc_odd -> M2_sq

def J_even (m r w z d : ℕ) : List ℕ :=
  3 :: (List.replicate (2 * m) 1 ++ (3 :: (List.replicate (2 * r) 1 ++ (2 :: R_tail w z d))))

def J_odd (m r w z d : ℕ) : List ℕ :=
  3 :: (List.replicate (2 * m) 1 ++ (3 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail w z d))))

lemma pop_A0_run_hL (k : ℕ) (L : List SBlock) (hL : L ≠ [.A 2]) (R : List ℕ) :
    iterOpt step_sq k (.hL, List.replicate k (.A 0) ++ L, R) =
      some (.hL, L, List.replicate k 1 ++ R) := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    conv_lhs => rw [Nat.add_comm k 1]
    have hne := replicate_A0_append_ne_A2 k hL
    have h1 : iterOpt step_sq 1 (.hL, .A 0 :: (List.replicate k (.A 0) ++ L), R) =
        some (.hL, List.replicate k (.A 0) ++ L, 1 :: R) := by
      dsimp [iterOpt]
      rw [step_sq_hL_A0 _ hne R]
      rfl
    refine iterOpt_trans h1 ?_
    rw [ih (1 :: R), replicate_append_cons_same]

lemma enc_odd_b1_step1 (m s d : ℕ) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_odd (2 * m + 1) 1 (2 * s + 1) d)
      (3 :: (List.replicate (2 * m + 1) 1 ++ (0 :: R_mid (2 * s + 1) d))) := by
  apply bounce_from_A0A2
  have h0 : enc_odd (2 * m + 1) 1 (2 * s + 1) d =
      3 :: (List.replicate (2 * m + 1) 1 ++ (0 :: 1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))) := rfl
  rw [h0]
  have h1 := prefix_odd_3 m (0 :: 1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))
  have h2 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m [.A 0, .A 2] (0 :: 1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1])))
  have h3 : CfgSqReachesPlus
      (.h10B, stackAfterOnes m [.A 0, .A 2], 0 :: 1 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))
      (.h10B, .A 1 :: .B 1 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]), List.replicate (2 * s + 1) 1 ++ [d, 1]) :=
    ⟨3, by decide, by simp [iterOpt, step_sq]⟩
  have h4 := pass1_turnaround s d hd (.B 1 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]))
  have h5 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B1_B2_A2_hL m [.A 0, .A 2] (R_mid (2 * s + 1) d))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 (cfgSqReachesStar_plus_trans h2 h3)) h4) h5

lemma enc_odd_ge2_mid (m k s d : ℕ) (hd : d = 0 ∨ d = 2) :
    CfgSqReachesPlus
      (.h10B, [.A 1], enc_odd (2 * m + 1) (k + 2) (2 * s + 1) d)
      (.h10B, .A 1 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]),
        List.replicate k 1 ++ (2 :: R_mid (2 * s + 1) d)) := by
  have h0 : enc_odd (2 * m + 1) (k + 2) (2 * s + 1) d =
      3 :: (List.replicate (2 * m + 1) 1 ++ (0 :: 1 :: (List.replicate (k + 1) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))))) := by
    simp [enc_odd, TailWord, show k + 2 = 1 + (k + 1) by omega, List.replicate_add]
  rw [h0]
  have h1 := prefix_odd_3 m (0 :: 1 :: (List.replicate (k + 1) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))))
  have h2 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any m [.A 0, .A 2] (0 :: 1 :: (List.replicate (k + 1) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1])))))
  have h3 : CfgSqReachesPlus
      (.h10B, stackAfterOnes m [.A 0, .A 2], 0 :: 1 :: (List.replicate (k + 1) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))))
      (.h10F, .B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]), List.replicate (k + 1) 1 ++ (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))) :=
    ⟨2, by decide, by simp [iterOpt, step_sq]⟩
  have h4 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10F (k + 1) (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])) (3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1])))
  have h5 : CfgSqReachesPlus
      (.h10F, List.replicate (k + 1) (.A 0) ++ (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])),
        3 :: (List.replicate (2 * s + 1) 1 ++ [d, 1]))
      (.h10B, .A 1 :: .A 1 :: (List.replicate k (.A 0) ++ (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]))),
        List.replicate (2 * s + 1) 1 ++ [d, 1]) :=
    ⟨1, by decide, by simp [List.replicate_succ, iterOpt, step_sq]⟩
  have h6 := pass1_turnaround s d hd
    (.A 1 :: (List.replicate k (.A 0) ++ (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]))))
  have h7 : CfgSqReachesPlus
      (.hL, .A 1 :: (List.replicate k (.A 0) ++ (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]))), R_mid (2 * s + 1) d)
      (.hL, List.replicate k (.A 0) ++ (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])), 2 :: R_mid (2 * s + 1) d) :=
    ⟨1, by decide, rfl⟩
  have h8 := cfgSqReachesStar_of_iterOpt
    (pop_A0_run_hL k (.B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])) (by simp) (2 :: R_mid (2 * s + 1) d))
  have h9 : CfgSqReachesPlus
      (.hL, .B 0 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]), List.replicate k 1 ++ (2 :: R_mid (2 * s + 1) d))
      (.h10B, .A 1 :: (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2]), List.replicate k 1 ++ (2 :: R_mid (2 * s + 1) d)) :=
    ⟨1, by decide, rfl⟩
  exact cfgSqReachesPlus_trans
    (cfgSqReachesPlus_trans
      (cfgSqReachesPlus_trans
        (cfgSqReachesPlus_trans
          (cfgSqReachesPlus_trans h1 (cfgSqReachesStar_plus_trans h2 h3))
          (cfgSqReachesStar_plus_trans h4 h5))
        h6)
      h7)
    (cfgSqReachesStar_plus_trans h8 h9)

lemma rmid_even_2 (r s d : ℕ) (hd : d = 0 ∨ d = 2) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r) 1 ++ (2 :: R_mid (2 * s + 1) d))
      (.hL, L, 3 :: (List.replicate (2 * r) 1 ++ (2 :: R_tail (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)))) := by
  rcases hd with rfl | rfl
  · simp only [R_mid, ↓reduceIte]
    have h1 := cfgSqReachesStar_of_iterOpt (scan_ones_h10B_any r L (2 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1])))
    have h2 : CfgSqReachesPlus
        (.h10B, stackAfterOnes r L, 2 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))
        (.h10B, .A 1 :: .A 1 :: (List.replicate r (.B 2) ++ (.A 2 :: L)), List.replicate (2 * s + 1) 1 ++ [3, 1]) :=
      ⟨2, by decide, by simp [iterOpt, step_sq]⟩
    have h3 := pass2_turnaround s (.A 1 :: (List.replicate r (.B 2) ++ (.A 2 :: L)))
    have h4 : CfgSqReachesPlus
        (.hL, .A 1 :: (List.replicate r (.B 2) ++ (.A 2 :: L)), R_tail (2 * s) 1 2)
        (.hL, List.replicate r (.B 2) ++ (.A 2 :: L), 2 :: R_tail (2 * s) 1 2) :=
      ⟨1, by decide, rfl⟩
    have h5 := cfgSqReachesPlus_of_iterOpt (by omega) (pop_B2_A2_hL r L (2 :: R_tail (2 * s) 1 2))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5
  · simp only [R_mid, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte, show 2 * s + 1 - 1 = 2 * s by omega,
      show 2 - 2 = 0 by rfl]
    have h := sep_even_2 r L (2 * s) 1 0 (by decide) (Or.inl rfl)
    simpa [psiTilde] using h

lemma rmid_odd_2 (r s d : ℕ) (hd : d = 0 ∨ d = 2) (L : List SBlock) :
    CfgSqReachesPlus
      (.h10B, .A 1 :: L, List.replicate (2 * r + 1) 1 ++ (2 :: R_mid (2 * s + 1) d))
      (.hL, L, 3 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)))) := by
  have heq : List.replicate (2 * r + 1) 1 ++ (2 :: R_mid (2 * s + 1) d) =
      1 :: (List.replicate (2 * r) 1 ++ (2 :: R_mid (2 * s + 1) d)) := by
    rw [Nat.add_comm (2 * r) 1, List.replicate_add]; rfl
  rw [heq]
  have hp := prefix_P2_scan_2 r L (R_mid (2 * s + 1) d)
  rcases hd with rfl | rfl
  · simp only [R_mid, ↓reduceIte] at hp ⊢
    have h2 : CfgSqReachesPlus
        (.h10B, .A 1 :: stackP2 r L, 0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))
        (.h10B, .A 1 :: .A 0 :: .A 1 :: stackP2 r L, List.replicate (2 * s + 1) 1 ++ [3, 1]) :=
      ⟨2, by decide, rfl⟩
    have h3 := pass2_turnaround s (.A 0 :: .A 1 :: stackP2 r L)
    have h4 : CfgSqReachesPlus
        (.hL, .A 0 :: .A 1 :: stackP2 r L, R_tail (2 * s) 1 2)
        (.hL, stackP2 r L, 2 :: 1 :: R_tail (2 * s) 1 2) :=
      ⟨2, by decide, rfl⟩
    have h5 := prefix_P2_pop r L (2 :: 1 :: R_tail (2 * s) 1 2)
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans hp h2) h3) h4) h5
  · simp only [R_mid, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte, show 2 * s + 1 - 1 = 2 * s by omega,
      show 2 - 2 = 0 by rfl] at hp ⊢
    have h2 := sep_0 (2 * s) 1 0 (by decide) (Or.inl rfl) (stackP2 r L)
    have hpsi : psiTilde (2 * s) 1 = (2 * s + 1, 1) := by simp [psiTilde]
    rw [hpsi] at h2
    have h3 := prefix_P2_pop r L (2 :: 1 :: R_tail (2 * s + 1) 1 0)
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans hp h2) h3

lemma enc_odd_even_b_step1 (m r s d : ℕ) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_odd (2 * m + 1) (2 * r + 2) (2 * s + 1) d)
      (J_even m r (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)) := by
  apply bounce_from_A0A2
  have h1 := enc_odd_ge2_mid m (2 * r) s d hd
  have h2 := rmid_even_2 r s d hd (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL m [.A 0, .A 2] (3 :: (List.replicate (2 * r) 1 ++ (2 :: R_tail (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)))))
  simpa [J_even] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3

lemma enc_odd_odd_b_step1 (m r s d : ℕ) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_odd (2 * m + 1) (2 * r + 3) (2 * s + 1) d)
      (J_odd m r (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)) := by
  apply bounce_from_A0A2
  have h1 := enc_odd_ge2_mid m (2 * r + 1) s d hd
  have h2 := rmid_odd_2 r s d hd (List.replicate m (.B 2) ++ [.A 2, .A 0, .A 2])
  have h3 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL m [.A 0, .A 2] (3 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail (if d = 0 then 2 * s else 2 * s + 1) 1 (2 - d)))))
  simpa [J_odd] using cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3

lemma J_even_zero_to_M2 (r w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (J_even 0 r w z d) (M2_sq (2 * r + 2) (psiTilde w z).1 (psiTilde w z).2 d) := by
  have hb1 : SqReachesPlus (J_even 0 r w z d)
      (List.replicate (2 * (r + 1)) 1 ++ (2 :: R_tail w z d)) := by
    have hd3 : SqReachesPlus (J_even 0 r w z d)
        (1 :: 1 :: (List.replicate (2 * r) 1 ++ (2 :: R_tail w z d))) :=
      double3_reduction (List.replicate (2 * r) 1 ++ (2 :: R_tail w z d))
    have heq : 1 :: 1 :: (List.replicate (2 * r) 1 ++ (2 :: R_tail w z d)) =
        List.replicate (2 * (r + 1)) 1 ++ (2 :: R_tail w z d) := by
      rw [show 2 * (r + 1) = 2 + 2 * r by omega]
      simp [List.replicate_add, List.cons_append]
    rwa [heq] at hd3
  have hb2 : SqReachesPlus
      (List.replicate (2 * (r + 1)) 1 ++ (2 :: R_tail w z d))
      (M2_sq (2 * (r + 1)) (psiTilde w z).1 (psiTilde w z).2 d) :=
    bounce_from_nil (sep_even_2 (r + 1) [] w z d hz hd)
  rw [show 2 * (r + 1) = 2 * r + 2 by omega] at hb2
  exact sqReachesPlus_trans hb1 hb2

lemma J_even_succ_to_J_odd (m r w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (J_even (m + 1) r w z d) (J_odd m r (psiTilde w z).1 (psiTilde w z).2 d) := by
  apply bounce_from_A0A2
  have h1 := prefix_P1_scan m [] (List.replicate (2 * r) 1 ++ (2 :: R_tail w z d))
  have h2 := prefix_P2_scan_2 r (stackP1 m []) (R_tail w z d)
  have h3 := sep_0 w z d hz hd (stackP2 r (stackP1 m []))
  have h4 := prefix_P2_pop r (stackP1 m []) (2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d)
  have h5 := prefix_P1_pop m [] (3 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d)))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5

lemma J_odd_zero_to_M2 (r w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (J_odd 0 r w z d) (M2_sq (2 * r + 2) w (z + 2) d) := by
  have hb1 : SqReachesPlus (J_odd 0 r w z d)
      (List.replicate (2 * (r + 1)) 1 ++ (2 :: 1 :: R_tail w z d)) := by
    have hd3 : SqReachesPlus (J_odd 0 r w z d)
        (1 :: 1 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail w z d))) :=
      double3_reduction (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail w z d))
    have heq : 1 :: 1 :: (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail w z d)) =
        List.replicate (2 * (r + 1)) 1 ++ (2 :: 1 :: R_tail w z d) := by
      rw [show 2 * (r + 1) = 2 + 2 * r by omega]
      simp [List.replicate_add, List.cons_append]
    rwa [heq] at hd3
  have hb2 : SqReachesPlus
      (List.replicate (2 * (r + 1)) 1 ++ (2 :: 1 :: R_tail w z d))
      (M2_sq (2 * (r + 1) + 1) (psiTilde w z).1 (psiTilde w z).2 d) :=
    bounce_from_nil (sep_even_21 (r + 1) [] (Or.inl (by omega)) w z d hz hd)
  have hb3 := M2_sq_odd_step (r + 1) (psiTilde w z).1 (psiTilde w z).2 d (psiTilde_snd_odd w z hz) hd
  rw [psiTilde_psiTilde, show 2 * (r + 1) = 2 * r + 2 by omega] at hb3
  exact sqReachesPlus_trans (sqReachesPlus_trans hb1 hb2) hb3

lemma J_odd_succ_to_F (m r w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (J_odd (m + 1) r w z d) (F_sq (2 * m) (2 * r) 1 (psiTilde w z).1 (psiTilde w z).2 d) := by
  apply bounce_from_A0A2
  have h1 := prefix_P1_scan m [] (List.replicate (2 * r) 1 ++ (2 :: 1 :: R_tail w z d))
  have h2 := prefix_P2_scan_2 r (stackP1 m []) (1 :: R_tail w z d)
  have h3 := sep_even_01 0 (stackP2 r (stackP1 m [])) w z d hz hd
  have h4 := prefix_P2_pop r (stackP1 m []) (3 :: [1] ++ (0 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))
  have h5 := prefix_P1_pop m [] (3 :: (List.replicate (2 * r) 1 ++ (3 :: [1] ++ (0 :: R_tail (psiTilde w z).1 (psiTilde w z).2 d))))
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3) h4) h5

lemma phase1_b1_d0 (m s : ℕ) :
    SqReachesPlus (enc_odd (2 * m + 1) 1 (2 * s + 1) 0) (M2_sq 0 (2 * s) (2 * m + 3) 2) := by
  have h1 := enc_odd_b1_step1 m s 0 (Or.inl rfl)
  simp only [R_mid, ↓reduceIte] at h1
  rcases m with _ | m'
  · have h2 : SqReachesPlus
        (3 :: [1] ++ (0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1])))
        (2 :: 1 :: R_tail (2 * s) 1 2) := by
      apply bounce_from_A0A2
      have ha : CfgSqReachesPlus
          (.h10B, [.A 1], 3 :: 1 :: 0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))
          (.h10B, .A 1 :: [.A 0, .A 1, .A 0, .A 2], List.replicate (2 * s + 1) 1 ++ [3, 1]) :=
        ⟨4, by decide, rfl⟩
      have hb := pass2_turnaround s [.A 0, .A 1, .A 0, .A 2]
      have hc : CfgSqReachesPlus
          (.hL, [.A 0, .A 1, .A 0, .A 2], R_tail (2 * s) 1 2)
          (.hL, [.A 0, .A 2], 2 :: 1 :: R_tail (2 * s) 1 2) :=
        ⟨2, by decide, rfl⟩
      exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans ha hb) hc
    have h3 := sep_21_nil (2 * s) 1 2 (by decide) (Or.inr rfl)
    have hpsi : psiTilde (2 * s) 1 = (2 * s + 1, 1) := by simp [psiTilde]
    rw [hpsi] at h3
    have h4 : SqReachesPlus (2 :: R_tail (2 * s + 1) 1 2) (M2_sq 0 (2 * s) 3 2) := by
      have hx := bounce_from_nil (sep_even_2 0 [] (2 * s + 1) 1 2 (by decide) (Or.inr rfl))
      have hpsi2 : psiTilde (2 * s + 1) 1 = (2 * s, 3) := by simp [psiTilde]
      rwa [hpsi2] at hx
    exact sqReachesPlus_trans (sqReachesPlus_trans (sqReachesPlus_trans h1 h2) h3) h4
  · have h2 : SqReachesPlus
        (3 :: (List.replicate (2 * (m' + 1) + 1) 1 ++ (0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))))
        (3 :: (List.replicate (2 * m' + 1) 1 ++ (0 :: 1 :: R_tail (2 * s) 1 2))) := by
      apply bounce_from_A0A2
      have ha := prefix_odd_3 (m' + 1) (0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))
      have hb := cfgSqReachesStar_of_iterOpt
        (scan_ones_h10B_any (m' + 1) [.A 0, .A 2] (0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1])))
      have hc : CfgSqReachesPlus
          (.h10B, stackAfterOnes (m' + 1) [.A 0, .A 2], 0 :: 3 :: (List.replicate (2 * s + 1) 1 ++ [3, 1]))
          (.h10B, .A 1 :: .A 0 :: .B 1 :: (List.replicate m' (.B 2) ++ [.A 2, .A 0, .A 2]), List.replicate (2 * s + 1) 1 ++ [3, 1]) :=
        ⟨2, by decide, rfl⟩
      have hd' := pass2_turnaround s (.A 0 :: .B 1 :: (List.replicate m' (.B 2) ++ [.A 2, .A 0, .A 2]))
      have he : CfgSqReachesPlus
          (.hL, .A 0 :: .B 1 :: (List.replicate m' (.B 2) ++ [.A 2, .A 0, .A 2]), R_tail (2 * s) 1 2)
          (.hL, .B 1 :: (List.replicate m' (.B 2) ++ [.A 2, .A 0, .A 2]), 1 :: R_tail (2 * s) 1 2) :=
        ⟨1, by decide, rfl⟩
      have hf := cfgSqReachesPlus_of_iterOpt (by omega)
        (pop_B1_B2_A2_hL m' [.A 0, .A 2] (1 :: R_tail (2 * s) 1 2))
      exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans ha (cfgSqReachesStar_plus_trans hb hc)) hd') he) hf
    have h3 : SqReachesPlus
        (3 :: (List.replicate (2 * m' + 1) 1 ++ (0 :: 1 :: R_tail (2 * s) 1 2)))
        (H_sq (2 * m' + 1) (2 * s + 1) 1 2) := by
      apply bounce_from_A0A2
      have ha := prefix_odd_3 m' (0 :: 1 :: R_tail (2 * s) 1 2)
      have hb := sep_even_01 m' [.A 0, .A 2] (2 * s) 1 2 (by decide) (Or.inr rfl)
      have hpsi : psiTilde (2 * s) 1 = (2 * s + 1, 1) := by simp [psiTilde]
      rw [hpsi] at hb
      exact cfgSqReachesPlus_trans ha hb
    have h4 := H_drain m' (2 * s + 1) 1 2 (by decide) (Or.inr rfl)
    have hpsi2 : psiTilde (2 * s + 1) 1 = (2 * s, 3) := by simp [psiTilde]
    rw [hpsi2] at h4
    have htot := sqReachesPlus_trans (sqReachesPlus_trans (sqReachesPlus_trans h1 h2) h3) h4
    rwa [show 3 + 2 * m' + 2 = 2 * (m' + 1) + 3 by omega] at htot

structure OddState where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving DecidableEq, Repr

def InSodd (s : OddState) : Prop :=
  s.a % 2 = 1 ∧ s.b ≥ 1 ∧ s.c ≥ 3 ∧ s.c % 2 = 1 ∧ (s.d = 0 ∨ s.d = 2)

lemma phase1_to_M2 (s : OddState) (hs : InSodd s) :
    SqReachesPlus
      (enc_odd s.a s.b s.c s.d)
      (M2_sq (2 * (s.b / 2))
        (if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1)
        (if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2)
        (2 - s.d)) := by
  rcases hs with ⟨ha_odd, hb_ge1, hc_ge3, hc_odd, hd⟩
  have ha_eq : s.a = 2 * (s.a / 2) + 1 := by omega
  have hc_eq : s.c = 2 * (s.c / 2) + 1 := by omega
  set m := s.a / 2
  set sc := s.c / 2
  rcases Nat.mod_two_eq_zero_or_one s.b with hb_ev | hb_od
  · -- s.b even >= 2: write s.b = 2 * r + 2
    have hb_eq : s.b = 2 * (s.b / 2 - 1) + 2 := by omega
    set r := s.b / 2 - 1
    have hq : 2 * (s.b / 2) = 2 * r + 2 := by omega
    set w1 := if s.d = 0 then 2 * sc else 2 * sc + 1
    set dp := 2 - s.d
    have hstep1 : SqReachesPlus (enc_odd s.a s.b s.c s.d) (J_even m r w1 1 dp) := by
      rw [ha_eq, hb_eq, hc_eq]
      exact enc_odd_even_b_step1 m r sc s.d hd
    have hdp : dp = 0 ∨ dp = 2 := by dsimp [dp]; omega
    have hpsi1 : psiTilde w1 1 = (if s.d = 0 then 2 * sc + 1 else 2 * sc, if s.d = 0 then 1 else 3) := by
      ext <;> dsimp only [w1, psiTilde] <;> split_ifs <;> omega
    have hJ : SqReachesPlus (J_even m r w1 1 dp)
        (M2_sq (2 * r + 2) (psiTilde w1 1).1 ((psiTilde w1 1).2 + 2 * m) dp) := by
      rcases m with _ | m1
      · exact J_even_zero_to_M2 r w1 1 dp (by decide) hdp
      · rcases m1 with _ | m2
        · have hj1 := J_even_succ_to_J_odd 0 r w1 1 dp (by decide) hdp
          have hj2 := J_odd_zero_to_M2 r (psiTilde w1 1).1 (psiTilde w1 1).2 dp (psiTilde_snd_odd w1 1 (by decide)) hdp
          exact sqReachesPlus_trans hj1 hj2
        · have hj1 := J_even_succ_to_J_odd (m2 + 1) r w1 1 dp (by decide) hdp
          have hj2 := J_odd_succ_to_F m2 r (psiTilde w1 1).1 (psiTilde w1 1).2 dp (psiTilde_snd_odd w1 1 (by decide)) hdp
          rw [psiTilde_psiTilde] at hj2
          have hj3 := F_universal_drain m2 r 0 w1 3 dp (by decide) hdp
          have hpsi3 : psiTilde w1 3 = ((psiTilde w1 1).1, (psiTilde w1 1).2 + 2) := by
            rw [show (3 : ℕ) = 1 + 2 by rfl, psiTilde_add_two, psiShift_eq_psiTilde_step]
          rw [hpsi3] at hj3
          have htotJ := sqReachesPlus_trans (sqReachesPlus_trans hj1 hj2) hj3
          rwa [show (psiTilde w1 1).2 + 2 + 2 * (m2 + 0 + 1) = (psiTilde w1 1).2 + 2 * (m2 + 2) by omega] at htotJ
    have htot := sqReachesPlus_trans hstep1 hJ
    rw [hpsi1, ← hq] at htot
    have hw_eq : (if s.d = 0 then 2 * sc + 1 else 2 * sc) =
        (if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1) := by
      split_ifs <;> omega
    have hz_eq : (if s.d = 0 then 1 else 3) + 2 * m =
        (if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2) := by
      split_ifs <;> omega
    rwa [hw_eq, hz_eq] at htot
  · -- s.b odd >= 1: split s.b = 1 vs s.b = 2 * r + 3
    rcases (show s.b = 1 ∨ s.b ≥ 3 by omega) with hb1 | hb3
    · rcases hd with hd0 | hd2
      · have hq0 : 2 * (s.b / 2) = 0 := by omega
        have hw0 : (if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1) = 2 * sc := by
          split_ifs <;> omega
        have hz0 : (if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2) = 2 * m + 3 := by
          split_ifs <;> omega
        have hd0' : 2 - s.d = 2 := by omega
        rw [hq0, hw0, hz0, hd0', ha_eq, hb1, hc_eq, hd0]
        exact phase1_b1_d0 m sc
      · have h1 := enc_odd_b1_step1 m sc 2 (Or.inr rfl)
        simp only [R_mid, show (2 : ℕ) ≠ 0 by decide, ↓reduceIte, show 2 * sc + 1 - 1 = 2 * sc by omega] at h1
        have h2 := H_drain m (2 * sc) 1 0 (by decide) (Or.inl rfl)
        have hpsi : psiTilde (2 * sc) 1 = (2 * sc + 1, 1) := by
          unfold psiTilde; rw [if_pos (by omega)]
        rw [hpsi] at h2
        have htot : SqReachesPlus (enc_odd (2 * m + 1) 1 (2 * sc + 1) 2) (M2_sq 0 (2 * sc + 1) (1 + 2 * m + 2) 0) :=
          sqReachesPlus_trans h1 h2
        have hq0 : 2 * (s.b / 2) = 0 := by omega
        have hw0 : (if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1) = 2 * sc + 1 := by
          split_ifs <;> omega
        have hz0 : (if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2) = 1 + 2 * m + 2 := by
          split_ifs <;> omega
        have hd2' : 2 - s.d = 0 := by omega
        rw [hq0, hw0, hz0, hd2', ha_eq, hb1, hc_eq, hd2]
        exact htot
    · have hb_eq : s.b = 2 * (s.b / 2 - 1) + 3 := by omega
      set r := s.b / 2 - 1
      have hq : 2 * (s.b / 2) = 2 * r + 2 := by omega
      set w1 := if s.d = 0 then 2 * sc else 2 * sc + 1
      set dp := 2 - s.d
      have hstep1 : SqReachesPlus (enc_odd s.a s.b s.c s.d) (J_odd m r w1 1 dp) := by
        rw [ha_eq, hb_eq, hc_eq]
        exact enc_odd_odd_b_step1 m r sc s.d hd
      have hdp : dp = 0 ∨ dp = 2 := by dsimp [dp]; omega
      have hJ : SqReachesPlus (J_odd m r w1 1 dp) (M2_sq (2 * r + 2) w1 (2 * m + 3) dp) := by
        rcases m with _ | m1
        · exact J_odd_zero_to_M2 r w1 1 dp (by decide) hdp
        · have hj1 := J_odd_succ_to_F m1 r w1 1 dp (by decide) hdp
          have hj2 := F_universal_drain m1 r 0 (psiTilde w1 1).1 (psiTilde w1 1).2 dp
            (psiTilde_snd_odd w1 1 (by decide)) hdp
          rw [psiTilde_psiTilde] at hj2
          have htotJ := sqReachesPlus_trans hj1 hj2
          rwa [show 1 + 2 + 2 * (m1 + 0 + 1) = 2 * (m1 + 1) + 3 by omega] at htotJ
      have htot := sqReachesPlus_trans hstep1 hJ
      rw [← hq] at htot
      have hw_eq : w1 = (if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1) := by
        dsimp only [w1]; split_ifs <;> omega
      have hz_eq : 2 * m + 3 = (if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2) := by
        split_ifs <;> omega
      rwa [hw_eq, hz_eq] at htot

-- Phase 2: M2_sq (2 * (k - 1)) w Z d -> enc_odd / enc_even

lemma M2_ge4_to_G (m w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (M2_sq (2 * m + 4) w Z d) (G_sq (2 * m) 1 w (Z + 2) d) := by
  set wt := (psiTilde w Z).1
  set Zt := (psiTilde w Z).2
  have hb1 : SqReachesPlus (M2_sq (2 * m + 4) w Z d)
      (3 :: (List.replicate (2 * m + 2) 1 ++ (2 :: 1 :: R_tail wt Zt d))) := by
    apply bounce_from_A0A2
    have h1 := prefix_M2_scan (m + 1) [] (R_tail w Z d)
    have h2 := sep_0 w Z d hZ hd (stackP1 (m + 1) [])
    have h3 := prefix_P1_pop (m + 1) [] (2 :: 1 :: R_tail wt Zt d)
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  have hb2 : SqReachesPlus
      (3 :: (List.replicate (2 * m + 2) 1 ++ (2 :: 1 :: R_tail wt Zt d)))
      (G_sq (2 * m) 1 w (Z + 2) d) := by
    apply bounce_from_A0A2
    have h1 := prefix_M2_scan m [] (1 :: R_tail wt Zt d)
    have h2 := sep_even_01 0 (stackP1 m []) wt Zt d (psiTilde_snd_odd w Z hZ) hd
    rw [psiTilde_psiTilde] at h2
    have h3 := prefix_P1_pop m [] (3 :: [1] ++ (0 :: R_tail w (Z + 2) d))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  exact sqReachesPlus_trans hb1 hb2

lemma loop_L1G (v j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq (2 * v + 4) (2 * j + 1) w z d)
      (G_sq (2 * v) (2 * j + 3) w (z + 2) d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus
      (G_sq (2 * v + 4) (2 * j + 1) w z d)
      (3 :: (List.replicate (2 * v + 2) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))))) := by
    apply bounce_from_A0A2
    have h1 := prefix_P1_scan (v + 1) [] (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))
    rw [cons_replicate_odd_append j 1 (0 :: R_tail w z d)] at h1
    have h2 := sep_even_0 j (stackP1 (v + 1) []) w z d hz hd
    have h3 := prefix_P1_pop (v + 1) [] (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  have hb2 : SqReachesPlus
      (3 :: (List.replicate (2 * v + 2) 1 ++ (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))))
      (G_sq (2 * v) (2 * j + 3) w (z + 2) d) := by
    apply bounce_from_A0A2
    have h1 := prefix_P1_scan v [] (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))
    rw [cons_replicate_odd_append j 1 (0 :: 1 :: R_tail wt zt d)] at h1
    have h2 := sep_even_01 (j + 1) (stackP1 v []) wt zt d (psiTilde_snd_odd w z hz) hd
    rw [psiTilde_psiTilde] at h2
    have h3 := prefix_P1_pop v [] (3 :: (List.replicate (2 * j + 3) 1 ++ (0 :: R_tail w (z + 2) d)))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  exact sqReachesPlus_trans hb1 hb2

lemma G_even_0_exit (j w z d : ℕ) :
    SqReachesPlus (G_sq 0 (2 * j + 1) w z d) (enc_odd (2 * j + 3) (w + 1) z d) := by
  have hb1 : SqReachesPlus (G_sq 0 (2 * j + 1) w z d)
      (List.replicate (2 * (j + 1) + 1) 1 ++ (0 :: 3 :: TailWord w z d)) := by
    have hd3 : SqReachesPlus (G_sq 0 (2 * j + 1) w z d)
        (1 :: 1 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 3 :: TailWord w z d))) :=
      double3_reduction (List.replicate (2 * j + 1) 1 ++ (0 :: 3 :: TailWord w z d))
    have heq1 : 1 :: 1 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 3 :: TailWord w z d)) =
        List.replicate (2 * (j + 1) + 1) 1 ++ (0 :: 3 :: TailWord w z d) := by
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by omega]
      simp [List.replicate_add, List.cons_append]
    rwa [heq1] at hd3
  have hb2 := exit_odd_0_3 (j + 1) (TailWord w z d)
  have heq : 3 :: (List.replicate (2 * (j + 1) + 1) 1 ++ (0 :: 1 :: TailWord w z d)) =
      enc_odd (2 * j + 3) (w + 1) z d := by
    rw [show 2 * (j + 1) + 1 = 2 * j + 3 by omega]
    simp only [enc_odd, TailWord, List.replicate_succ, List.cons_append]
  rw [heq] at hb2
  exact sqReachesPlus_trans hb1 hb2

lemma G_even_2_exit (j w z d : ℕ) (hz : z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq 2 (2 * j + 1) w z d)
      (enc_even (2 * j + 4) (psiTilde w z).1 (psiTilde w z).2 d) := by
  set wt := (psiTilde w z).1
  set zt := (psiTilde w z).2
  have hb1 : SqReachesPlus (G_sq 2 (2 * j + 1) w z d)
      (3 :: 3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))) := by
    apply bounce_from_A0A2
    have h1 := prefix_P1_scan 0 [] (List.replicate (2 * j + 1) 1 ++ (0 :: R_tail w z d))
    rw [cons_replicate_odd_append j 1 (0 :: R_tail w z d)] at h1
    have h2 := sep_even_0 j (stackP1 0 []) w z d hz hd
    have h3 := prefix_P1_pop 0 [] (3 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)))
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  have hb2 := double3_reduction (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d))
  have heq : 1 :: 1 :: (List.replicate (2 * j + 1) 1 ++ (0 :: 1 :: R_tail wt zt d)) =
      enc_even (2 * j + 4) wt zt d := by
    rw [enc_even, show 2 * j + 4 - 1 = (2 * j + 1) + 1 + 1 by omega]
    simp only [List.replicate_succ, List.cons_append]
  rw [heq] at hb2
  exact sqReachesPlus_trans hb1 hb2

lemma M2_0_exit (w Z d : ℕ) :
    SqReachesPlus (M2_sq 0 w Z d) (enc_odd 1 (w + 1) Z d) := by
  have hb1 : SqReachesPlus (M2_sq 0 w Z d) (1 :: 0 :: 3 :: TailWord w Z d) :=
    exit_3_2 (3 :: TailWord w Z d)
  have hb2 : SqReachesPlus (1 :: 0 :: 3 :: TailWord w Z d)
      (3 :: (1 :: 0 :: 1 :: TailWord w Z d)) := exit_odd_0_3 0 (TailWord w Z d)
  have heq : 3 :: (1 :: 0 :: 1 :: TailWord w Z d) = enc_odd 1 (w + 1) Z d := by
    simp only [enc_odd, TailWord, List.replicate_succ, List.replicate_zero,
      List.cons_append, List.nil_append]
  rw [heq] at hb2
  exact sqReachesPlus_trans hb1 hb2

lemma M2_2_exit (w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (M2_sq 2 w Z d) (enc_even 2 (psiTilde w Z).1 (psiTilde w Z).2 d) := by
  set wt := (psiTilde w Z).1
  set Zt := (psiTilde w Z).2
  have hb1 : SqReachesPlus (M2_sq 2 w Z d) (3 :: 2 :: 1 :: R_tail wt Zt d) := by
    apply bounce_from_A0A2
    have h1 := prefix_M2_scan 0 [] (R_tail w Z d)
    have h2 := sep_0 w Z d hZ hd (stackP1 0 [])
    have h3 := prefix_P1_pop 0 [] (2 :: 1 :: R_tail wt Zt d)
    exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans h1 h2) h3
  have hb2 := exit_3_2 (1 :: R_tail wt Zt d)
  exact sqReachesPlus_trans hb1 hb2

lemma G_even_drain_0 (r j w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (G_sq (4 * r) (2 * j + 1) w Z d) (enc_odd (2 * (j + r) + 3) (w + 1) (Z + 2 * r) d) := by
  induction r generalizing j Z with
  | zero => exact G_even_0_exit j w Z d
  | succ r ih =>
    have h1 : SqReachesPlus (G_sq (4 * (r + 1)) (2 * j + 1) w Z d) (G_sq (4 * r) (2 * (j + 1) + 1) w (Z + 2) d) := by
      have hl := loop_L1G (2 * r) j w Z d hZ hd
      rwa [show 2 * (2 * r) + 4 = 4 * (r + 1) by omega, show 2 * (2 * r) = 4 * r by omega] at hl
    have h2 := ih (j + 1) (Z + 2) (by omega)
    have htot := sqReachesPlus_trans h1 h2
    rwa [show 2 * (j + 1 + r) + 3 = 2 * (j + (r + 1)) + 3 by omega,
         show Z + 2 + 2 * r = Z + 2 * (r + 1) by omega] at htot

lemma G_even_drain_2 (r j w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (G_sq (4 * r + 2) (2 * j + 1) w Z d)
      (enc_even (2 * (j + r) + 4) (psiTilde w Z).1 ((psiTilde w Z).2 + 2 * r) d) := by
  induction r generalizing j Z with
  | zero => exact G_even_2_exit j w Z d hZ hd
  | succ r ih =>
    have h1 : SqReachesPlus (G_sq (4 * (r + 1) + 2) (2 * j + 1) w Z d) (G_sq (4 * r + 2) (2 * (j + 1) + 1) w (Z + 2) d) := by
      have hl := loop_L1G (2 * r + 1) j w Z d hZ hd
      rwa [show 2 * (2 * r + 1) + 4 = 4 * (r + 1) + 2 by omega, show 2 * (2 * r + 1) = 4 * r + 2 by omega] at hl
    have h2 := ih (j + 1) (Z + 2) (by omega)
    have hpsi : psiTilde w (Z + 2) = ((psiTilde w Z).1, (psiTilde w Z).2 + 2) := by
      rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
    rw [hpsi] at h2
    have htot := sqReachesPlus_trans h1 h2
    rwa [show 2 * (j + 1 + r) + 4 = 2 * (j + (r + 1)) + 4 by omega,
         show (psiTilde w Z).2 + 2 + 2 * r = (psiTilde w Z).2 + 2 * (r + 1) by omega] at htot

lemma phase2_odd (r w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus (M2_sq (4 * r) w Z d) (enc_odd (2 * r + 1) (w + 1) (Z + 2 * r) d) := by
  rcases r with _ | r'
  · exact M2_0_exit w Z d
  · have h1 : SqReachesPlus (M2_sq (4 * (r' + 1)) w Z d) (G_sq (4 * r') 1 w (Z + 2) d) := by
      have hm := M2_ge4_to_G (2 * r') w Z d hZ hd
      rwa [show 2 * (2 * r') + 4 = 4 * (r' + 1) by omega, show 2 * (2 * r') = 4 * r' by omega] at hm
    have h2 := G_even_drain_0 r' 0 w (Z + 2) d (by omega) hd
    have htot := sqReachesPlus_trans h1 h2
    rwa [show 2 * (0 + r') + 3 = 2 * (r' + 1) + 1 by omega,
         show Z + 2 + 2 * r' = Z + 2 * (r' + 1) by omega] at htot

lemma phase2_even (r w Z d : ℕ) (hZ : Z % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (M2_sq (4 * r + 2) w Z d)
      (enc_even (2 * r + 2) (psiTilde w Z).1 ((psiTilde w Z).2 + 2 * r) d) := by
  rcases r with _ | r'
  · exact M2_2_exit w Z d hZ hd
  · have h1 : SqReachesPlus (M2_sq (4 * (r' + 1) + 2) w Z d) (G_sq (4 * r' + 2) 1 w (Z + 2) d) := by
      have hm := M2_ge4_to_G (2 * r' + 1) w Z d hZ hd
      rwa [show 2 * (2 * r' + 1) + 4 = 4 * (r' + 1) + 2 by omega, show 2 * (2 * r' + 1) = 4 * r' + 2 by omega] at hm
    have h2 := G_even_drain_2 r' 0 w (Z + 2) d (by omega) hd
    have hpsi : psiTilde w (Z + 2) = ((psiTilde w Z).1, (psiTilde w Z).2 + 2) := by
      rw [psiTilde_add_two, psiShift_eq_psiTilde_step]
    rw [hpsi] at h2
    have htot := sqReachesPlus_trans h1 h2
    rwa [show 2 * (0 + r') + 4 = 2 * (r' + 1) + 2 by omega,
         show (psiTilde w Z).2 + 2 + 2 * r' = (psiTilde w Z).2 + 2 * (r' + 1) by omega] at htot

-- Even Halving Cascade & R_odd_sound

lemma enc_even_step1 (k' B C d : ℕ) (hB : B ≥ 1) (hC : C % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_even (2 * (k' + 1)) B C d)
      (M_sq (2 * k' + 1) (psiTilde (B - 1) C).1 (psiTilde (B - 1) C).2 d) := by
  apply bounce_from_nil
  have hrt : R_tail B C d = 3 :: 1 :: TailWord (B - 1) C d := by
    have hb_eq : B = (B - 1) + 1 := by omega
    dsimp only [R_tail, TailWord]
    conv_lhs => rw [hb_eq, List.replicate_succ, List.cons_append]
  have heq : enc_even (2 * (k' + 1)) B C d =
      List.replicate (2 * k') 1 ++ (1 :: 0 :: 1 :: 3 :: 1 :: TailWord (B - 1) C d) := by
    rw [enc_even, hrt, show 2 * (k' + 1) - 1 = 2 * k' + 1 by omega, replicate_succ_append]
  rw [heq]
  have h1 := cfgSqReachesStar_of_iterOpt
    (scan_ones_h10B_any k' [] (1 :: 0 :: 1 :: 3 :: 1 :: TailWord (B - 1) C d))
  have h2 : CfgSqReachesPlus
      (.h10B, stackAfterOnes k' [], 1 :: 0 :: 1 :: 3 :: 1 :: TailWord (B - 1) C d)
      (.h10B, .A 1 :: .A 0 :: .B 3 :: (List.replicate k' (.B 2) ++ [.A 2]), TailWord (B - 1) C d) :=
    ⟨5, by decide, by simp [iterOpt, step_sq]⟩
  have h3 := tail_reflect (B - 1) C d hC hd
    (.A 0 :: .B 3 :: (List.replicate k' (.B 2) ++ [.A 2])) (by simp)
  have h4 : CfgSqReachesPlus
      (.hL, .A 0 :: .B 3 :: (List.replicate k' (.B 2) ++ [.A 2]),
        R_tail (psiTilde (B - 1) C).1 (psiTilde (B - 1) C).2 d)
      (.hL, List.replicate k' (.B 2) ++ [.A 2],
        1 :: 2 :: 1 :: R_tail (psiTilde (B - 1) C).1 (psiTilde (B - 1) C).2 d) :=
    ⟨2, by decide, rfl⟩
  have h5 := cfgSqReachesPlus_of_iterOpt (by omega)
    (pop_B2_A2_hL k' [] (1 :: 2 :: 1 :: R_tail (psiTilde (B - 1) C).1 (psiTilde (B - 1) C).2 d))
  rw [replicate_append_cons_same (2 * k')] at h5
  exact cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesPlus_trans (cfgSqReachesStar_plus_trans h1 h2) h3) h4) h5

lemma enc_even_to_M2 (k' B C d : ℕ) (hB : B ≥ 1) (hC : C % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_even (2 * (k' + 1)) B C d)
      (M2_sq (2 * k') (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) d) :=
  sqReachesPlus_trans
    (enc_even_step1 k' B C d hB hC hd)
    (M_sq_odd_to_M2 k' (psiTilde (B - 1) C).1 (psiTilde (B - 1) C).2 d
      (psiTilde_snd_odd (B - 1) C hC) hd)

lemma step_even_halve (r B C d : ℕ) (hB : B ≥ 1) (hC : C % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_even (2 * (2 * r + 2)) B C d)
      (enc_even (2 * r + 2) (B - 1) (C + (2 * r + 2) + 2) d) := by
  have h1 : SqReachesPlus
      (enc_even (2 * (2 * r + 2)) B C d)
      (M2_sq (4 * r + 2) (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) d) := by
    have he := enc_even_to_M2 (2 * r + 1) B C d hB hC hd
    rwa [show 2 * (2 * r + 1 + 1) = 2 * (2 * r + 2) by omega,
         show 2 * (2 * r + 1) = 4 * r + 2 by omega] at he
  have hCt_odd : ((psiTilde (B - 1) C).2 + 2) % 2 = 1 := by
    have := psiTilde_snd_odd (B - 1) C hC; omega
  have h2 := phase2_even r (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) d hCt_odd hd
  have hpsi : psiTilde (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) = (B - 1, C + 4) := by
    rw [psiTilde_add_two]
    simpa using psiShift_psiTilde_add (B - 1) C 0
  rw [hpsi] at h2
  have htot := sqReachesPlus_trans h1 h2
  rwa [show C + 4 + 2 * r = C + (2 * r + 2) + 2 by omega] at htot

lemma step_even_exit (r B C d : ℕ) (hB : B ≥ 1) (hC : C % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesPlus
      (enc_even (2 * (2 * r + 1)) B C d)
      (enc_odd (2 * r + 1) ((psiTilde (B - 1) C).1 + 1) ((psiTilde (B - 1) C).2 + 2 + 2 * r) d) := by
  have h1 : SqReachesPlus
      (enc_even (2 * (2 * r + 1)) B C d)
      (M2_sq (4 * r) (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) d) := by
    have he := enc_even_to_M2 (2 * r) B C d hB hC hd
    rwa [show 2 * (2 * r) = 4 * r by omega] at he
  have hCt_odd : ((psiTilde (B - 1) C).2 + 2) % 2 = 1 := by
    have := psiTilde_snd_odd (B - 1) C hC; omega
  exact sqReachesPlus_trans h1
    (phase2_odd r (psiTilde (B - 1) C).1 ((psiTilde (B - 1) C).2 + 2) d hCt_odd hd)

lemma even_cascade (t a' B C d : ℕ) (ha' : a' % 2 = 1) (hB : B ≥ t)
    (hC : C % 2 = 1) (hd : d = 0 ∨ d = 2) :
    SqReachesStar
      (enc_even (2 ^ (t + 1) * a') B C d)
      (enc_even (2 * a') (B - t) (C + (2 ^ (t + 1) - 2) * a' + 2 * t) d) := by
  induction t generalizing B C with
  | zero =>
    simpa using sqReachesStar_refl (enc_even (2 * a') B C d)
  | succ t ih =>
    have hpow_ge : 2 ^ (t + 1) * a' ≥ 2 := by
      have hp : 2 ^ (t + 1) ≥ 2 := by
        rw [Nat.pow_succ']
        have := @Nat.one_le_two_pow t
        omega
      have ha1 : a' ≥ 1 := by omega
      calc 2 ^ (t + 1) * a' ≥ 2 * 1 := Nat.mul_le_mul hp ha1
        _ = 2 := rfl
    have hpow_ev : (2 ^ (t + 1) * a') % 2 = 0 := by
      rw [Nat.pow_succ', Nat.mul_assoc]
      omega
    set r := (2 ^ (t + 1) * a' - 2) / 2
    have hr_eq : 2 ^ (t + 1) * a' = 2 * r + 2 := by omega
    have hhead : 2 * (2 ^ (t + 1) * a') = 2 ^ (t + 1 + 1) * a' := by
      rw [Nat.pow_succ' (n := t + 1), Nat.mul_assoc]
    have h1 := sqReachesStar_of_plus (step_even_halve r B C d (by omega) hC hd)
    rw [← hr_eq, hhead] at h1
    have h2 := ih (B - 1) (C + 2 ^ (t + 1) * a' + 2) (by omega) (by omega)
    have hsub : B - 1 - t = B - (t + 1) := by omega
    have hsum : C + 2 ^ (t + 1) * a' + 2 + (2 ^ (t + 1) - 2) * a' + 2 * t =
        C + (2 ^ (t + 2) - 2) * a' + 2 * (t + 1) := by
      have hp1 : 2 ^ (t + 1) ≥ 2 := by
        rw [Nat.pow_succ']; have := @Nat.one_le_two_pow t; omega
      have hmul : 2 ^ (t + 1) * a' + (2 ^ (t + 1) - 2) * a' = (2 ^ (t + 2) - 2) * a' := by
        rw [← Nat.add_mul, show t + 2 = (t + 1) + 1 by omega, Nat.pow_succ']
        exact congrArg (· * a') (by omega)
      omega
    rw [hsub, hsum] at h2
    exact sqReachesStar_trans h1 h2

-- ----------------------------------------------------------------------------
-- Stage 5A: OddState, R_odd, Soundness & Sandwich Bounds
-- ----------------------------------------------------------------------------

lemma splitTwoAux_spec (fuel m : ℕ) (hm : m ≥ 1) (hfuel : m ≤ fuel) :
    2 ^ (splitTwoAux fuel m).1 * (splitTwoAux fuel m).2 = m ∧
      (splitTwoAux fuel m).2 % 2 = 1 := by
  induction fuel generalizing m with
  | zero => omega
  | succ fuel ih =>
    dsimp [splitTwoAux]
    split_ifs with hev
    · obtain ⟨heq, hodd⟩ := ih (m / 2) (by omega) (by omega)
      refine ⟨?_, hodd⟩
      rw [Nat.pow_succ', Nat.mul_assoc, heq]
      omega
    · exact ⟨by simp, by omega⟩

lemma splitTwo_spec (m : ℕ) (hm : m ≥ 1) :
    2 ^ (splitTwo m).1 * (splitTwo m).2 = m ∧ (splitTwo m).2 % 2 = 1 :=
  splitTwoAux_spec m m hm (le_refl m)

def InSdom (s : OddState) : Prop :=
  InSodd s ∧ s.c ≥ s.a

def bInSdom (s : OddState) : Bool :=
  (s.a % 2 == 1) && (1 ≤ s.b) && (3 ≤ s.c) && (s.c % 2 == 1) &&
  ((s.d == 0) || (s.d == 2)) && (s.a ≤ s.c)

lemma bInSdom_iff (s : OddState) : bInSdom s = true ↔ InSdom s := by
  simp only [bInSdom, InSdom, InSodd, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
  omega

def sigma_true (b d : ℕ) : ℕ :=
  if b % 4 = 1 then 0
  else if b % 4 = 0 then (if d = 0 then 1 else 0)
  else if b % 4 = 2 then (if d = 0 then 1 else 0)
  else (if d = 2 then 1 else 0)

lemma sigma_true_le_one (b d : ℕ) : sigma_true b d ≤ 1 := by
  unfold sigma_true; split_ifs <;> omega

def nu_of (s : OddState) : ℕ := (splitTwo (s.b / 2 + 1)).1

def a_next_of (s : OddState) : ℕ := (splitTwo (s.b / 2 + 1)).2

def R_odd (s : OddState) : Option OddState :=
  let m := s.b / 2 + 1
  let ν := nu_of s
  let a' := a_next_of s
  let σ := sigma_true s.b s.d
  if s.c < σ + ν then none
  else
    let M := s.c - σ - ν
    let d' := 2 - s.d
    if ν = 0 then
      let b' := if s.b % 4 = 1 then s.c + s.d / 2 else s.c + 1 - s.d / 2
      let c' := if s.b % 4 = 1 then s.a + a' + 1 else s.a + a' - 1 + s.d
      some ⟨a', b', c', d'⟩
    else
      let b' := if M % 2 = 0 then M + 2 else M
      let c' := 2 * m - a' + s.a + 2 * ν +
        (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0) +
        (if M % 2 = 0 then 0 else 2) - 1
      some ⟨a', b', c', d'⟩

lemma R_odd_halt_iff (s : OddState) :
    R_odd s = none ↔ s.c < sigma_true s.b s.d + nu_of s := by
  unfold R_odd
  by_cases h1 : s.c < sigma_true s.b s.d + nu_of s
  · simp [h1]
  · simp only [h1, ↓reduceIte]
    split_ifs <;> simp

theorem R_odd_sound (s s' : OddState) (hs : InSodd s) (hr : R_odd s = some s') :
    SqReachesPlus (enc_odd s.a s.b s.c s.d) (enc_odd s'.a s'.b s'.c s'.d) := by
  have hp1 := phase1_to_M2 s hs
  rcases hs with ⟨ha_odd, hb_ge1, hc_ge3, hc_odd, hd⟩
  set m := s.b / 2 + 1
  obtain ⟨hm_eq, ha'_odd⟩ : 2 ^ (nu_of s) * (a_next_of s) = m ∧ (a_next_of s) % 2 = 1 :=
    splitTwo_spec m (by omega)
  unfold R_odd at hr
  by_cases hlt : s.c < sigma_true s.b s.d + nu_of s
  · simp [hlt] at hr
  · simp only [hlt, ↓reduceIte] at hr
    set w₁ := if (s.b % 2 = 0 ∧ s.d = 0) ∨ (s.b % 2 = 1 ∧ s.d = 2) then s.c else s.c - 1
    set Z₁ := if s.b % 2 = 0 ∧ s.d = 0 then s.a else s.a + 2
    set d' := 2 - s.d
    have hd' : d' = 0 ∨ d' = 2 := by dsimp [d']; omega
    have hZ₁_odd : Z₁ % 2 = 1 := by dsimp [Z₁]; split_ifs <;> omega
    rcases hnu : nu_of s with _ | t
    · -- ν = 0: m = a_next_of s is odd, so s.b / 2 = 2 * ((a' - 1) / 2)
      simp only [hnu, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rw [hnu, Nat.pow_zero, Nat.one_mul] at hm_eq
      set r := (a_next_of s - 1) / 2
      have ha'_eq : a_next_of s = 2 * r + 1 := by omega
      have hqb : 2 * (s.b / 2) = 4 * r := by omega
      rw [hqb] at hp1
      have hp2 := phase2_odd r w₁ Z₁ d' hZ₁_odd hd'
      have htot := sqReachesPlus_trans hp1 hp2
      have hbw : w₁ + 1 = (if s.b % 4 = 1 then s.c + s.d / 2 else s.c + 1 - s.d / 2) := by
        dsimp [w₁]
        rcases hd with hd0 | hd2 <;> (split_ifs <;> omega)
      have hcz : Z₁ + 2 * r = (if s.b % 4 = 1 then s.a + a_next_of s + 1 else s.a + a_next_of s - 1 + s.d) := by
        dsimp [Z₁]
        rcases hd with hd0 | hd2 <;> (split_ifs <;> omega)
      rw [← ha'_eq, hbw, hcz] at htot
      exact htot
    · -- ν = t + 1 ≥ 1: m = 2 ^ (t + 1) * a' is even
      simp only [hnu, Nat.succ_ne_zero, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      rw [hnu] at hm_eq hlt
      have hm_ev : m % 2 = 0 := by
        rw [← hm_eq, Nat.pow_succ', Nat.mul_assoc]; omega
      have hm_ge2 : m ≥ 2 := by omega
      set r₀ := (m - 2) / 2
      have hqb : 2 * (s.b / 2) = 4 * r₀ + 2 := by omega
      have hr0_m : 2 * r₀ + 2 = m := by omega
      rw [hqb] at hp1
      have hp2 := phase2_even r₀ w₁ Z₁ d' hZ₁_odd hd'
      rw [hr0_m] at hp2
      -- Evaluate psiTilde w₁ Z₁: since m is even, s.b / 2 is odd, so s.b % 4 ∈ {2, 3}!
      have hb_mod4 : s.b % 4 = 2 ∨ s.b % 4 = 3 := by omega
      have hsig_eq : sigma_true s.b s.d =
          if (s.b % 4 = 2 ∧ s.d = 0) ∨ (s.b % 4 = 3 ∧ s.d = 2) then 1 else 0 := by
        unfold sigma_true; split_ifs <;> omega
      have hw1_val : (w₁ = s.c ∧ sigma_true s.b s.d = 1) ∨
          (w₁ = s.c - 1 ∧ sigma_true s.b s.d = 0) := by
        rw [hsig_eq]; dsimp only [w₁]; split_ifs <;> omega
      have hB0 : (psiTilde w₁ Z₁).1 = s.c - sigma_true s.b s.d := by
        rcases hw1_val with ⟨hw, hs_eq⟩ | ⟨hw, hs_eq⟩ <;>
          (rw [hw, hs_eq]; dsimp only [psiTilde]; split_ifs <;> omega)
      have hC0 : (psiTilde w₁ Z₁).2 + 2 * r₀ =
          m + s.a + (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0) := by
        have hwZ : (w₁ = s.c ∧ Z₁ = s.a ∧ ¬(s.b % 2 = 1 ∧ s.d = 2)) ∨
            (w₁ = s.c - 1 ∧ Z₁ = s.a + 2 ∧ ¬(s.b % 2 = 1 ∧ s.d = 2)) ∨
            (w₁ = s.c ∧ Z₁ = s.a + 2 ∧ (s.b % 2 = 1 ∧ s.d = 2)) := by
          dsimp only [w₁, Z₁]; split_ifs <;> omega
        rcases hwZ with ⟨hw, hZ, hbd⟩ | ⟨hw, hZ, hbd⟩ | ⟨hw, hZ, hbd⟩
        · rw [hw, hZ, if_neg hbd]; dsimp only [psiTilde]; split_ifs <;> omega
        · rw [hw, hZ, if_neg hbd]; dsimp only [psiTilde]; split_ifs <;> omega
        · rw [hw, hZ, if_pos hbd]; dsimp only [psiTilde]; split_ifs <;> omega
      rw [hB0, hC0] at hp2
      set B₀ := s.c - sigma_true s.b s.d
      set C₀ := m + s.a + (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0)
      have hC0_odd : C₀ % 2 = 1 := by dsimp [C₀]; split_ifs <;> omega
      have hB0_ge : B₀ ≥ t + 1 := by dsimp [B₀]; omega
      rw [← hm_eq] at hp2
      have hcas := even_cascade t (a_next_of s) B₀ C₀ d' ha'_odd (by omega) hC0_odd hd'
      set r' := (a_next_of s - 1) / 2
      have ha'_eq : a_next_of s = 2 * r' + 1 := by omega
      set Ct := C₀ + (2 ^ (t + 1) - 2) * (a_next_of s) + 2 * t
      have hCt_odd : Ct % 2 = 1 := by
        dsimp [Ct]
        have : ((2 ^ (t + 1) - 2) * a_next_of s) % 2 = 0 := by
          have hp2_ge : 2 ^ (t + 1) ≥ 2 := by
            rw [Nat.pow_succ']; have := @Nat.one_le_two_pow t; omega
          have hev2 : (2 ^ (t + 1) - 2) % 2 = 0 := by
            rw [Nat.pow_succ']; omega
          rw [Nat.mul_mod, hev2, Nat.zero_mul]
        omega
      have hexit := step_even_exit r' (B₀ - t) Ct d' (by omega) hCt_odd hd'
      rw [← ha'_eq] at hexit
      have htot := sqReachesPlus_trans (sqReachesPlus_trans hp1 (sqReachesPlus_star_trans hp2 hcas)) hexit
      set M := s.c - sigma_true s.b s.d - (t + 1)
      have hBt : B₀ - t - 1 = M := by dsimp [B₀, M]; omega
      rw [hBt] at htot
      have hb_final : (psiTilde M Ct).1 + 1 = (if M % 2 = 0 then M + 2 else M) := by
        dsimp [psiTilde]; split_ifs <;> omega
      have hc_final : (psiTilde M Ct).2 + 2 + 2 * r' =
          2 * m - a_next_of s + s.a + 2 * (t + 1) +
            (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0) +
            (if M % 2 = 0 then 0 else 2) - 1 := by
        have hm_sub : (2 ^ (t + 1) - 2) * a_next_of s = m - 2 * a_next_of s := by
          rw [Nat.sub_mul, hm_eq]
        dsimp [psiTilde, Ct, C₀]
        rw [hm_sub]
        have hm_ge_2a : m ≥ 2 * a_next_of s := by
          rw [← hm_eq, Nat.pow_succ', Nat.mul_assoc]
          exact Nat.mul_le_mul_left 2 (by
            calc 2 ^ t * a_next_of s ≥ 1 * a_next_of s := Nat.mul_le_mul_right _ Nat.one_le_two_pow
              _ = a_next_of s := Nat.one_mul _)
        split_ifs <;> omega
      rw [hb_final, hc_final] at htot
      exact htot

lemma R_odd_props (s s' : OddState) (hs : InSdom s) (hr : R_odd s = some s') :
    InSdom s' ∧
    s'.a = a_next_of s ∧
    2 ^ (nu_of s + 1) * s'.a = 2 * (s.b / 2 + 1) ∧
    2 * (s.b / 2 + 1) - 2 ≤ s.b ∧ s.b ≤ 2 * (s.b / 2 + 1) - 1 ∧
    s.b + s.a + 2 * nu_of s ≤ 2 * s'.c ∧
    2 ^ (nu_of s + 1) ≤ s.b + 2 ∧
    (nu_of s = 0 →
      s.c ≤ s'.b ∧ s'.b ≤ s.c + 1 ∧
      s.a + s'.a - 1 ≤ s'.c ∧ s'.c ≤ s.a + s'.a + 1) ∧
    (nu_of s ≥ 1 →
      s'.b + nu_of s - 2 ≤ s.c ∧ s.c ≤ s'.b + nu_of s + 1 ∧
      2 * (s.b / 2 + 1) - s'.a + s.a + 2 * nu_of s - 1 ≤ s'.c ∧
      s'.c ≤ 2 * (s.b / 2 + 1) - s'.a + s.a + 2 * nu_of s + 3) := by
  rcases hs with ⟨⟨ha_odd, hb_ge1, hc_ge3, hc_odd, hd⟩, hca⟩
  set m := s.b / 2 + 1
  obtain ⟨hm_eq, ha'_odd⟩ : 2 ^ (nu_of s) * (a_next_of s) = m ∧ (a_next_of s) % 2 = 1 :=
    splitTwo_spec m (by omega)
  have h2m : 2 ^ (nu_of s + 1) * a_next_of s = 2 * m := by
    rw [Nat.pow_succ', Nat.mul_assoc, hm_eq]
  have hsig := sigma_true_le_one s.b s.d
  unfold R_odd at hr
  by_cases hlt : s.c < sigma_true s.b s.d + nu_of s
  · simp [hlt] at hr
  · simp only [hlt, ↓reduceIte] at hr
    by_cases hnu0 : nu_of s = 0
    · simp only [hnu0, ↓reduceIte, Option.some.injEq] at hr
      rw [hnu0, Nat.pow_zero, Nat.one_mul] at hm_eq
      have hb4_cases :
          (s.b % 4 = 1 ∧ s' = ⟨a_next_of s, s.c + s.d / 2, s.a + a_next_of s + 1, 2 - s.d⟩) ∨
          (s.b % 4 ≠ 1 ∧ s' = ⟨a_next_of s, s.c + 1 - s.d / 2, s.a + a_next_of s - 1 + s.d, 2 - s.d⟩) := by
        by_cases hb4 : s.b % 4 = 1
        · rw [if_pos hb4, if_pos hb4] at hr; exact Or.inl ⟨hb4, hr.symm⟩
        · rw [if_neg hb4, if_neg hb4] at hr; exact Or.inr ⟨hb4, hr.symm⟩
      rcases hb4_cases with ⟨hb4, rfl⟩ | ⟨hb4, rfl⟩ <;> rcases hd with hd0 | hd2
      all_goals
        dsimp only [InSdom, InSodd]
        refine ⟨⟨⟨ha'_odd, by omega, by omega, by omega, by omega⟩, by omega⟩,
          rfl, h2m, by omega, by omega, by omega, by rw [hnu0]; omega,
          fun _ => ⟨by omega, by omega, by omega, by omega⟩, fun hge => by omega⟩
    · simp only [hnu0, ↓reduceIte, Option.some.injEq] at hr
      have hnu_ge1 : nu_of s ≥ 1 := by omega
      have hm_ge_2a : m ≥ 2 * a_next_of s := by
        rw [← hm_eq]
        obtain ⟨t, ht⟩ : ∃ t, nu_of s = t + 1 := ⟨nu_of s - 1, by omega⟩
        rw [ht, Nat.pow_succ', Nat.mul_assoc]
        exact Nat.mul_le_mul_left 2 (by
          calc 2 ^ t * a_next_of s ≥ 1 * a_next_of s := Nat.mul_le_mul_right _ Nat.one_le_two_pow
            _ = a_next_of s := Nat.one_mul _)
      have hpow_le : 2 ^ (nu_of s + 1) ≤ 2 * m := by
        rw [← h2m]
        calc 2 ^ (nu_of s + 1) = 2 ^ (nu_of s + 1) * 1 := (Nat.mul_one _).symm
          _ ≤ 2 ^ (nu_of s + 1) * a_next_of s := Nat.mul_le_mul_left _ (by omega)
      set M := s.c - sigma_true s.b s.d - nu_of s
      have hM_def : M = s.c - sigma_true s.b s.d - nu_of s := rfl
      have hs'_cases :
          (M % 2 = 0 ∧ (s.b % 2 = 1 ∧ s.d = 2) ∧
            s' = ⟨a_next_of s, M + 2, 2 * m - a_next_of s + s.a + 2 * nu_of s + 2 + 0 - 1, 2 - s.d⟩) ∨
          (M % 2 = 0 ∧ ¬(s.b % 2 = 1 ∧ s.d = 2) ∧
            s' = ⟨a_next_of s, M + 2, 2 * m - a_next_of s + s.a + 2 * nu_of s + 0 + 0 - 1, 2 - s.d⟩) ∨
          (M % 2 ≠ 0 ∧ (s.b % 2 = 1 ∧ s.d = 2) ∧
            s' = ⟨a_next_of s, M, 2 * m - a_next_of s + s.a + 2 * nu_of s + 2 + 2 - 1, 2 - s.d⟩) ∨
          (M % 2 ≠ 0 ∧ ¬(s.b % 2 = 1 ∧ s.d = 2) ∧
            s' = ⟨a_next_of s, M, 2 * m - a_next_of s + s.a + 2 * nu_of s + 0 + 2 - 1, 2 - s.d⟩) := by
        by_cases hM : M % 2 = 0 <;> by_cases hbd : s.b % 2 = 1 ∧ s.d = 2
        · rw [if_pos hM, if_pos hbd, if_pos hM] at hr; exact Or.inl ⟨hM, hbd, hr.symm⟩
        · rw [if_pos hM, if_neg hbd, if_pos hM] at hr; exact Or.inr (Or.inl ⟨hM, hbd, hr.symm⟩)
        · rw [if_neg hM, if_pos hbd, if_neg hM] at hr; exact Or.inr (Or.inr (Or.inl ⟨hM, hbd, hr.symm⟩))
        · rw [if_neg hM, if_neg hbd, if_neg hM] at hr; exact Or.inr (Or.inr (Or.inr ⟨hM, hbd, hr.symm⟩))
      rcases hs'_cases with ⟨hM, hbd, rfl⟩ | ⟨hM, hbd, rfl⟩ | ⟨hM, hbd, rfl⟩ | ⟨hM, hbd, rfl⟩
      all_goals
        dsimp only [InSdom, InSodd]
        refine ⟨⟨⟨ha'_odd, by omega, by omega, by omega, by omega⟩, by omega⟩,
          rfl, h2m, by omega, by omega, by omega, by omega,
          fun hz => absurd hz hnu0,
          fun _ => ⟨by omega, by omega, by omega, by omega⟩⟩

-- ----------------------------------------------------------------------------
-- Stage 5B: Two-Step 2-Adic Collapse Bounds (halt_3 & halt_5)
-- ----------------------------------------------------------------------------

lemma pow_two_ge_succ (n : ℕ) : 2 ^ n ≥ n + 1 := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ']; omega

lemma pow_two_ge_8 (E : ℕ) (hE : E ≥ 3) : 2 ^ (E + 1) ≥ 8 * E - 8 := by
  induction E with
  | zero => omega
  | succ E ih =>
    rcases (show E = 2 ∨ E ≥ 3 by omega) with rfl | hge
    · decide
    · have := ih hge; rw [Nat.pow_succ']; omega

lemma pow_two_ge_14 (E : ℕ) (hE : E ≥ 3) : 2 ^ (E + 1) ≥ 14 * E - 26 := by
  induction E with
  | zero => omega
  | succ E ih =>
    rcases (show E = 2 ∨ E ≥ 3 by omega) with rfl | hge
    · decide
    · have := ih hge; rw [Nat.pow_succ']; omega

lemma pow_two_ge_16 (n : ℕ) (hn : n ≥ 5) : 2 ^ (n + 1) ≥ 16 * n - 16 := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases (show n = 4 ∨ n ≥ 5 by omega) with rfl | hge
    · decide
    · have := ih hge; rw [Nat.pow_succ']; omega

lemma sq_lt_pow2_succ (E : ℕ) (hE : E ≥ 3) : E * E < 2 ^ (E + 1) := by
  induction E with
  | zero => omega
  | succ E ih =>
    rcases (show E = 2 ∨ E ≥ 3 by omega) with rfl | hge
    · decide
    · have h1 := ih hge
      have h2 := pow_two_ge_8 E hge
      have hexp : (E + 1) * (E + 1) = E * E + 2 * E + 1 := by ring
      rw [Nat.pow_succ', hexp]; omega

lemma quad_step1_lt (E : ℕ) (hE : E ≥ 8) : (5 * E + 5) * E < 2 ^ (E + 1) := by
  induction E with
  | zero => omega
  | succ E ih =>
    rcases (show E = 7 ∨ E = 8 ∨ E ≥ 9 by omega) with rfl | rfl | hge
    · decide
    · decide
    · have h1 := ih (by omega)
      have h2 := pow_two_ge_14 E (by omega)
      have hexp : (5 * (E + 1) + 5) * (E + 1) = (5 * E + 5) * E + 10 * E + 10 := by ring
      rw [Nat.pow_succ', hexp]; omega

lemma quad_step2a_lt (ν : ℕ) (hν : ν ≥ 10) : (3 * ν + 6) * (3 * ν + 7) < 2 ^ (ν + 1) := by
  induction ν with
  | zero => omega
  | succ ν ih =>
    rcases (show ν = 9 ∨ ν ≥ 10 by omega) with rfl | hge
    · decide
    · have h1 := ih hge
      have h2 := pow_two_ge_16 ν (by omega)
      have hexp : (3 * (ν + 1) + 6) * (3 * (ν + 1) + 7) =
          (3 * ν + 6) * (3 * ν + 7) + 18 * ν + 48 := by ring
      have h3 : 2 ^ (ν + 1) > 18 * ν + 48 := by
        rcases (show ν = 10 ∨ ν ≥ 11 by omega) with rfl | h11
        · decide
        · obtain ⟨k, rfl⟩ : ∃ k, ν = k + 6 := ⟨ν - 6, by omega⟩
          have hk := pow_two_ge_16 (k + 5) (by omega)
          have : 2 ^ (k + 6 + 1) = 2 * 2 ^ (k + 5 + 1) := by
            rw [show k + 6 + 1 = (k + 5 + 1) + 1 by omega, Nat.pow_succ']
          omega
      rw [Nat.pow_succ', hexp]; omega

lemma quad_step2b_lt (ν : ℕ) (hν : ν ≥ 11) : (6 * ν + 11) * (3 * ν + 8) < 2 ^ (ν + 1) := by
  have hlin : ∀ n, n ≥ 11 → 2 ^ (n + 1) > 36 * n + 99 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih =>
      intro hn
      rcases (show n = 10 ∨ n ≥ 11 by omega) with rfl | hge
      · decide
      · have := ih hge; rw [Nat.pow_succ']; omega
  induction ν with
  | zero => omega
  | succ ν ih =>
    rcases (show ν = 10 ∨ ν ≥ 11 by omega) with rfl | hge
    · decide
    · have h1 := ih hge
      have h2 := hlin ν hge
      have hexp : (6 * (ν + 1) + 11) * (3 * (ν + 1) + 8) =
          (6 * ν + 11) * (3 * ν + 8) + 36 * ν + 99 := by ring
      rw [Nat.pow_succ', hexp]; omega

lemma pow2_dvd_diff_ge {u w₁ w₂ x₁ x₂ : ℕ} (hu1 : u ≤ w₁) (hu2 : u ≤ w₂)
    (hlt : 2 ^ w₁ * x₁ < 2 ^ w₂ * x₂) :
    2 ^ u ≤ 2 ^ w₂ * x₂ - 2 ^ w₁ * x₁ := by
  have hw1 : 2 ^ w₁ * x₁ = 2 ^ u * (2 ^ (w₁ - u) * x₁) := by
    conv_lhs => rw [show w₁ = u + (w₁ - u) by omega, Nat.pow_add, Nat.mul_assoc]
  have hw2 : 2 ^ w₂ * x₂ = 2 ^ u * (2 ^ (w₂ - u) * x₂) := by
    conv_lhs => rw [show w₂ = u + (w₂ - u) by omega, Nat.pow_add, Nat.mul_assoc]
  rw [hw1, hw2] at hlt ⊢
  rw [← Nat.mul_sub_left_distrib]
  have hq : 2 ^ (w₂ - u) * x₂ - 2 ^ (w₁ - u) * x₁ ≥ 1 := by
    by_contra h0
    have hle : 2 ^ (w₂ - u) * x₂ ≤ 2 ^ (w₁ - u) * x₁ := by omega
    have := Nat.mul_le_mul_left (2 ^ u) hle
    omega
  calc 2 ^ u = 2 ^ u * 1 := (Nat.mul_one _).symm
    _ ≤ 2 ^ u * (2 ^ (w₂ - u) * x₂ - 2 ^ (w₁ - u) * x₁) := Nat.mul_le_mul_left _ hq

lemma pow2_odd_inj {u₁ u₂ x₁ x₂ : ℕ} (hx1 : x₁ % 2 = 1) (hx2 : x₂ % 2 = 1)
    (heq : 2 ^ u₁ * x₁ = 2 ^ u₂ * x₂) : u₁ = u₂ ∧ x₁ = x₂ := by
  have h := congrArg splitTwo heq
  rw [splitTwo_pow_mul_odd u₁ x₁ hx1, splitTwo_pow_mul_odd u₂ x₂ hx2] at h
  exact Prod.mk.inj h

lemma mul_pred_add_self (A n : ℕ) (hn : n ≥ 1) : A * (n - 1) + A = A * n := by
  rcases n with _ | n'
  · omega
  · simp [Nat.mul_succ]

lemma halt3_step1_bounds (s2 s1 s0 : OddState)
    (hs2 : InSdom s2) (hr2 : R_odd s2 = some s1)
    (hr1 : R_odd s1 = some s0) (hr0 : R_odd s0 = none) :
    nu_of s2 ≥ 1 ∧ s2.c ≤ s1.b + nu_of s2 + 1 ∧
    (nu_of s2 ≤ 7 → s1.a ≤ 3 ∧ s2.c ≤ 15 ∧ 2 * s1.a + s2.c ≤ 16 ∧ 2 * s1.a + s2.c ≤ nu_of s2 + 11) ∧
    (nu_of s2 ≥ 8 → 4 * s1.a + 2 * s1.b ≤ nu_of s2 + 10) := by
  have hp2 := R_odd_props s2 s1 hs2 hr2
  have hs1 : InSdom s1 := hp2.1
  have hp1 := R_odd_props s1 s0 hs1 hr1
  have hs0 : InSdom s0 := hp1.1
  have ha0_s0_odd : s0.a % 2 = 1 := hs0.1.1
  have hhalt0 : s0.c < sigma_true s0.b s0.d + nu_of s0 := (R_odd_halt_iff s0).mp hr0
  have hsig0 := sigma_true_le_one s0.b s0.d
  have hE_ge3 : nu_of s0 ≥ 3 := by have := hs0.1.2.2.1; clear hp2 hp1; omega
  obtain ⟨hm0_eq, ha0_odd⟩ : 2 ^ (nu_of s0) * (a_next_of s0) = s0.b / 2 + 1 ∧ (a_next_of s0) % 2 = 1 :=
    splitTwo_spec (s0.b / 2 + 1) (by have := hs0.1.2.1; clear hp2 hp1; omega)
  have hm0_pow : 2 ^ (nu_of s0 + 1) * a_next_of s0 = 2 * (s0.b / 2 + 1) := by
    rw [Nat.pow_succ', Nat.mul_assoc, hm0_eq]
  have hm0_ge_pow : 2 * (s0.b / 2 + 1) ≥ 2 ^ (nu_of s0 + 1) := by
    rw [← hm0_pow]
    calc 2 ^ (nu_of s0 + 1) = 2 ^ (nu_of s0 + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (nu_of s0 + 1) * a_next_of s0 := Nat.mul_le_mul_left _ (by clear hp2 hp1; omega)
  have hp0_8 : 2 ^ (nu_of s0 + 1) ≥ 8 * nu_of s0 - 8 := pow_two_ge_8 (nu_of s0) hE_ge3
  have hb0_lo : 2 * (s0.b / 2 + 1) - 2 ≤ s0.b := by clear hp2 hp1; omega
  have hb0_hi : s0.b ≤ 2 * (s0.b / 2 + 1) - 1 := by clear hp2 hp1; omega
  -- Uniform s1 -> s0 bounds: nu_of s0 ≥ s1.a + (s1.b + 1) / 2 + 2 * nu_of s1 and 2*(s0.b/2+1) + nu_of s1 - 4 ≤ s1.c ≤ 2*(s0.b/2+1) + nu_of s1
  have hs1_unif : nu_of s0 ≥ s1.a + (s1.b + 1) / 2 + 2 * nu_of s1 ∧
      2 * (s0.b / 2 + 1) + nu_of s1 - 4 ≤ s1.c ∧ s1.c ≤ 2 * (s0.b / 2 + 1) + nu_of s1 := by
    rcases hnu1 : nu_of s1 with _ | t1
    · have h0 := hp1.2.2.2.2.2.2.2.1 hnu1
      have ha0_eq : s0.a = s1.b / 2 + 1 := by
        have := hp1.2.2.1; rw [hnu1] at this; clear hp2 hp1; omega
      have ha1_eq : a_next_of s1 = s1.b / 2 + 1 := by
        rw [← hp1.2.1, ha0_eq]
      refine ⟨?_, by clear hp2 hp1; omega, by clear hp2 hp1; omega⟩
      have hhalt0' : s0.c < sigma_true s0.b s0.d + nu_of s0 := hhalt0
      generalize hE0 : nu_of s0 = E0 at hhalt0' ⊢
      clear hE0
      unfold R_odd at hr1
      by_cases hlt1 : s1.c < sigma_true s1.b s1.d + nu_of s1
      · simp [hlt1] at hr1
      · simp only [hlt1, ↓reduceIte] at hr1
        simp only [hnu1, ↓reduceIte, Option.some.injEq] at hr1
        rw [← hr1] at hhalt0'
        dsimp only [sigma_true] at hhalt0'
        have hc1_odd := hs1.1.2.2.2.1
        have hd1 := hs1.1.2.2.2.2
        clear hp2 hp1 hs2 hs1 hs0 h0 hhalt0 hsig0 hm0_eq hm0_pow hm0_ge_pow hp0_8 hb0_lo hb0_hi hE_ge3
        rcases hd1 with hd10 | hd12
        · simp only [hd10] at hhalt0'
          norm_num at hhalt0'
          split_ifs at hhalt0' <;> omega
        · simp only [hd12] at hhalt0'
          norm_num at hhalt0'
          split_ifs at hhalt0' <;> omega
    · have h1 := hp1.2.2.2.2.2.2.2.2 (by clear hp2 hp1; omega)
      have hm1_2 : 2 * (s1.b / 2 + 1) ≥ 4 * s0.a := by
        have := hp1.2.2.1
        rw [hnu1, show t1 + 1 + 1 = 2 + t1 by clear hp2 hp1; omega, Nat.pow_add, Nat.mul_assoc] at this
        have : 2 ^ t1 * s0.a ≥ s0.a := by
          calc 2 ^ t1 * s0.a ≥ 1 * s0.a := Nat.mul_le_mul_right _ Nat.one_le_two_pow
            _ = s0.a := Nat.one_mul _
        clear hp2 hp1; omega
      have ha0_ge1 : s0.a ≥ 1 := by have := hs0.1.1; clear hp2 hp1; omega
      clear hp2 hp1 hs2 hs1 hs0; omega
  rcases hs1_unif with ⟨hE_lb, hc1_lo, hc1_hi⟩
  clear hp1 hr1 hr0 hs0 ha0_s0_odd hhalt0 hsig0 hm0_eq hb0_lo hb0_hi
  -- Eliminate nu_of s2 = 0
  have hnu2_ge1 : nu_of s2 ≥ 1 := by
    by_contra h0
    have hnu2_0 : nu_of s2 = 0 := by clear hp2 hs2 hs1; omega
    have hz := hp2.2.2.2.2.2.2.2.1 hnu2_0
    have ha2_le : s2.a ≤ s2.c := hs2.2
    have ha1_ge1 : s1.a ≥ 1 := by have := hs1.1.1; clear hp2 hs2 hs1; omega
    clear hp2 hs2 hs1; omega
  have hz2 := hp2.2.2.2.2.2.2.2.2 hnu2_ge1
  have hc2_ub : s2.c ≤ s1.b + nu_of s2 + 1 := hz2.2.1
  have hm2_pow : 2 ^ (nu_of s2 + 1) * s1.a = 2 * (s2.b / 2 + 1) := hp2.2.2.1
  have ha2_le_c2 : s2.a ≤ s2.c := hs2.2
  have ha2_odd : s2.a % 2 = 1 := hs2.1.1
  have ha1_odd : s1.a % 2 = 1 := hs1.1.1
  have hb1_ge1 : s1.b ≥ 1 := hs1.1.2.1
  clear hp2 hr2 hs2 hs1
  generalize hE_def : nu_of s0 = E at *
  generalize hm0_def : 2 * (s0.b / 2 + 1) = m0_2 at *
  generalize hnu2_def : nu_of s2 = nu2 at *
  generalize hm2_def : 2 * (s2.b / 2 + 1) = m2_2 at *
  generalize hnu1_def : nu_of s1 = nu1 at *
  clear hE_def hm0_def hnu2_def hm2_def hnu1_def
  have hm2_ge_2a : m2_2 ≥ 2 * s1.a := by
    rw [← hm2_pow]
    obtain ⟨t2, ht2⟩ : ∃ t2, nu2 = t2 + 1 := ⟨nu2 - 1, by omega⟩
    rw [ht2, show t2 + 1 + 1 = 1 + (t2 + 1) by omega, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 (by
      calc 2 ^ (t2 + 1) * s1.a ≥ 1 * s1.a := Nat.mul_le_mul_right _ Nat.one_le_two_pow
        _ = s1.a := Nat.one_mul _)
  have ha2_le : s2.a ≤ s1.b + nu2 + 1 := by omega
  have ha2_ge1 : s2.a ≥ 1 := by omega
  -- Prove m2_2 < m0_2
  have hm2_lt_m0 : m2_2 < m0_2 := by
    have hL : m2_2 + 2 * nu2 ≤ m0_2 + s1.a + nu1 := by omega
    rcases (show m2_2 < m0_2 ∨ m2_2 = m0_2 ∨ m0_2 < m2_2 by omega) with hlt | heq | hgt
    · exact hlt
    · rw [← hm2_pow, ← hm0_pow] at heq
      obtain ⟨hnu_eq, _⟩ := pow2_odd_inj ha1_odd ha0_odd heq
      have : nu2 = E := by omega
      omega
    · rw [← hm2_pow, ← hm0_pow] at hgt
      by_cases hEnu : E ≤ nu2
      · have hdvd := pow2_dvd_diff_ge (u := E + 1) (by omega) (by omega) hgt
        rw [hm2_pow, hm0_pow] at hdvd
        omega
      · have hdvd := pow2_dvd_diff_ge (u := nu2 + 1) (by omega) (by omega) hgt
        rw [hm2_pow, hm0_pow] at hdvd
        have hpow_le_E : 2 ^ (nu2 + 1) ≤ E := by omega
        have ha1_le_E : s1.a ≤ E := by omega
        have hprod : m2_2 ≤ E * E := by
          rw [← hm2_pow]
          exact Nat.mul_le_mul hpow_le_E ha1_le_E
        have hsq := sq_lt_pow2_succ E hE_ge3
        omega
  have hdiff_ub : m0_2 - m2_2 ≤ s1.b + 3 * nu2 + 8 - s1.a - nu1 := by omega
  clear hz2 hc1_lo hc1_hi ha2_le_c2 ha2_odd ha2_le ha2_ge1
  refine ⟨hnu2_ge1, hc2_ub, ?_, ?_⟩
  · -- Suppose nu2 ≤ 7: prove s1.a ≤ 3 ∧ s2.c ≤ 15
    intro hnu2_le7
    by_cases hcaseA : nu2 ≤ E
    · -- Case A: nu2 ≤ E
      have hdvd : 2 ^ (nu2 + 1) ≤ m0_2 - m2_2 := by
        rw [← hm0_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm0_pow])
      have h2E : 2 * E ≥ 2 * s1.a + s1.b := by omega
      have hpow_ub : 2 ^ (nu2 + 1) ≤ 2 * E + 3 * nu2 + 5 := by omega
      have hE_le7 : E ≤ 7 := by
        by_contra hE8
        have hq := quad_step1_lt E (by omega)
        have ha1_le : s1.a ≤ E - 1 := by omega
        have hp_le : 2 ^ (nu2 + 1) ≤ 5 * E + 5 := by omega
        have hprod : m2_2 ≤ (5 * E + 5) * (E - 1) := by
          rw [← hm2_pow]; exact Nat.mul_le_mul hp_le ha1_le
        have hexp := mul_pred_add_self (5 * E + 5) E (by omega)
        omega
      -- Since E ≤ 7, 2^(nu2+1) ≤ 19 + 3*nu2 forces nu2 ≤ 3!
      have hnu2_le3 : nu2 ≤ 3 := by
        rcases (show nu2 ≤ 3 ∨ nu2 = 4 ∨ nu2 = 5 ∨ nu2 = 6 ∨ nu2 = 7 by omega) with h | h4 | h5 | h6 | h7
        · exact h
        · rw [h4] at hpow_ub; norm_num at hpow_ub; omega
        · rw [h5] at hpow_ub; norm_num at hpow_ub; omega
        · rw [h6] at hpow_ub; norm_num at hpow_ub; omega
        · rw [h7] at hpow_ub; norm_num at hpow_ub; omega
      -- With nu2 ≤ 3, 2^(nu2+1) ≤ 16; E ∈ {6, 7} contradicts hm0_ge_pow
      have hpow_le16 : 2 ^ (nu2 + 1) ≤ 16 := by
        rcases (show nu2 = 1 ∨ nu2 = 2 ∨ nu2 = 3 by omega) with h1 | h2 | h3
        · rw [h1]; decide
        · rw [h2]; decide
        · rw [h3]; decide
      have hm2_le_16a : m2_2 ≤ 16 * s1.a := by
        rw [← hm2_pow]; exact Nat.mul_le_mul_right s1.a hpow_le16
      have hE_le5 : E ≤ 5 := by
        rcases (show E ≤ 5 ∨ E = 6 ∨ E = 7 by omega) with h | h6 | h7
        · exact h
        · rw [h6] at hm0_ge_pow; norm_num at hm0_ge_pow; omega
        · rw [h7] at hm0_ge_pow; norm_num at hm0_ge_pow; omega
      omega
    · -- Case B with nu2 ≤ 7: E < nu2 ≤ 7, so E ≤ 6
      have hdvd : 2 ^ (E + 1) ≤ m0_2 - m2_2 := by
        rw [← hm0_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm0_pow])
      have hp14 := pow_two_ge_14 E hE_ge3
      omega
  · -- Suppose nu2 ≥ 8: prove 4 * s1.a + 2 * s1.b ≤ nu2 + 10
    intro hnu2_ge8
    by_cases hcaseA : nu2 ≤ E
    · -- Case A impossible for nu2 ≥ 8!
      have hdvd : 2 ^ (nu2 + 1) ≤ m0_2 - m2_2 := by
        rw [← hm0_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm0_pow])
      have hq := quad_step1_lt E (by omega)
      have ha1_le : s1.a ≤ E - 1 := by omega
      have hp_le : 2 ^ (nu2 + 1) ≤ 5 * E + 5 := by omega
      have hprod : m2_2 ≤ (5 * E + 5) * (E - 1) := by
        rw [← hm2_pow]; exact Nat.mul_le_mul hp_le ha1_le
      have hexp := mul_pred_add_self (5 * E + 5) E (by omega)
      omega
    · -- Case B (E < nu2): 14 * E - 26 ≤ 2 ^ (E + 1) ≤ b1 - a1 + 3 * nu2 + 8
      have hdvd : 2 ^ (E + 1) ≤ m0_2 - m2_2 := by
        rw [← hm0_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm0_pow])
      have hp14 := pow_two_ge_14 E hE_ge3
      omega

lemma halt5_nu2_le_7 (s4 s3 s2 s1 s0 : OddState)
    (hs4 : InSdom s4) (hr4 : R_odd s4 = some s3) (hr3 : R_odd s3 = some s2)
    (hr2 : R_odd s2 = some s1) (hr1 : R_odd s1 = some s0) (hr0 : R_odd s0 = none) :
    nu_of s2 ≤ 7 := by
  have hp4 := R_odd_props s4 s3 hs4 hr4
  have hs3 : InSdom s3 := hp4.1
  have hp3 := R_odd_props s3 s2 hs3 hr3
  have hs2 : InSdom s2 := hp3.1
  have hstep1 := halt3_step1_bounds s2 s1 s0 hs2 hr2 hr1 hr0
  by_contra hgt7
  have hnu2_ge8 : nu_of s2 ≥ 8 := by omega
  have hc2_ub : s2.c ≤ s1.b + nu_of s2 + 1 := hstep1.2.1
  have hlin1 : 4 * s1.a + 2 * s1.b ≤ nu_of s2 + 10 := hstep1.2.2.2 hnu2_ge8
  clear hstep1 hr1 hr0 hgt7
  have hp2 := R_odd_props s2 s1 hs2 hr2
  have hm2_pow : 2 ^ (nu_of s2 + 1) * s1.a = 2 * (s2.b / 2 + 1) := hp2.2.2.1
  have ha1_odd : s1.a % 2 = 1 := hp2.1.1.1
  have hb2_lo : 2 * (s2.b / 2 + 1) - 2 ≤ s2.b := hp2.2.2.2.1
  have hb2_hi : s2.b ≤ 2 * (s2.b / 2 + 1) - 1 := hp2.2.2.2.2.1
  clear hp2 hr2 hs2
  have ha3_odd : s3.a % 2 = 1 := hs3.1.1
  have hb3_ge1 : s3.b ≥ 1 := hs3.1.2.1
  have hb3_sum_raw : s3.b + s3.a + 2 * nu_of s3 ≤ 2 * s2.c := hp3.2.2.2.2.2.1
  have hpow_nu3 : 2 ^ (nu_of s3 + 1) ≤ s3.b + 2 := hp3.2.2.2.2.2.2.1
  have hc3_sand : 2 * (s2.b / 2 + 1) + nu_of s3 - 4 ≤ s3.c ∧ s3.c ≤ 2 * (s2.b / 2 + 1) + nu_of s3 := by
    by_cases hnu3_0 : nu_of s3 = 0
    · have hz3 := hp3.2.2.2.2.2.2.2.1 hnu3_0; clear hp4 hp3 hs4 hs3; omega
    · have hz3 := hp3.2.2.2.2.2.2.2.2 (by omega); clear hp4 hp3 hs4 hs3; omega
  clear hp3 hr3 hs3 hb2_lo hb2_hi
  have hb3_sum : s3.b + s3.a + 2 * nu_of s3 ≤ 3 * nu_of s2 + 8 := by
    clear hp4 hs4 hr4; omega
  clear hb3_sum_raw hc2_ub
  have hm4_pow : 2 ^ (nu_of s4 + 1) * s3.a = 2 * (s4.b / 2 + 1) := hp4.2.2.1
  have ha4_odd : s4.a % 2 = 1 := hs4.1.1
  have ha4_le_c4 : s4.a ≤ s4.c := hs4.2
  have hz4_zero := hp4.2.2.2.2.2.2.2.1
  have hz4_pos := hp4.2.2.2.2.2.2.2.2
  clear hp4 hs4 hr4
  generalize hm2_def : 2 * (s2.b / 2 + 1) = m2_2 at *
  generalize hm4_def : 2 * (s4.b / 2 + 1) = m4_2 at *
  generalize hnu2_def : nu_of s2 = nu2 at *
  generalize hnu3_def : nu_of s3 = nu3 at *
  generalize hnu4_def : nu_of s4 = nu4 at *
  clear hm2_def hm4_def hnu2_def hnu3_def hnu4_def
  have hm2_ge_pow : m2_2 ≥ 2 ^ (nu2 + 1) := by
    rw [← hm2_pow]
    calc 2 ^ (nu2 + 1) = 2 ^ (nu2 + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ 2 ^ (nu2 + 1) * s1.a := Nat.mul_le_mul_left _ (by omega)
  have hp2_14 : 2 ^ (nu2 + 1) ≥ 14 * nu2 - 26 := pow_two_ge_14 nu2 (by omega)
  have hnu4_ge1 : nu4 ≥ 1 := by
    by_contra h0
    have hnu4_0 : nu4 = 0 := by omega
    have hz4 := hz4_zero hnu4_0
    omega
  have hz4 := hz4_pos hnu4_ge1
  clear hz4_zero hz4_pos
  have hm4_ge_2a : m4_2 ≥ 2 * s3.a := by
    rw [← hm4_pow]
    obtain ⟨t4, ht4⟩ : ∃ t4, nu4 = t4 + 1 := ⟨nu4 - 1, by omega⟩
    rw [ht4, show t4 + 1 + 1 = 1 + (t4 + 1) by omega, Nat.pow_add, Nat.mul_assoc]
    exact Nat.mul_le_mul_left 2 (by
      calc 2 ^ (t4 + 1) * s3.a ≥ 1 * s3.a := Nat.mul_le_mul_right _ Nat.one_le_two_pow
        _ = s3.a := Nat.one_mul _)
  have ha4_ge1 : s4.a ≥ 1 := by omega
  have ha4_le : s4.a ≤ s3.b + nu4 + 1 := by omega
  have hL : m4_2 + 2 * nu4 ≤ m2_2 + s3.a + nu3 := by omega
  have hU : m2_2 + nu3 ≤ m4_2 + s3.b + 3 * nu4 + 8 - s3.a := by omega
  clear hz4 hc3_sand ha4_odd ha4_le_c4 ha4_ge1 ha4_le
  -- Compare m4_2 vs m2_2
  rcases (show m4_2 = m2_2 ∨ m2_2 < m4_2 ∨ m4_2 < m2_2 by omega) with heq | hgt | hlt
  · -- Branch 1: m4_2 = m2_2 => nu4 = nu2 ∧ s3.a = s1.a
    rw [← hm4_pow, ← hm2_pow] at heq
    obtain ⟨hnu_eq, ha_eq⟩ := pow2_odd_inj ha3_odd ha1_odd heq
    have hnu3_ge3 : nu3 ≥ 3 := by omega
    have hp8 := pow_two_ge_8 nu3 hnu3_ge3
    omega
  · -- Branch 2: m2_2 < m4_2
    by_cases hnu4_ge : nu2 ≤ nu4
    · have hdvd : 2 ^ (nu2 + 1) ≤ m4_2 - m2_2 := by
        rw [← hm4_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm4_pow])
      omega
    · have hdvd : 2 ^ (nu4 + 1) ≤ m4_2 - m2_2 := by
        rw [← hm4_pow, ← hm2_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm2_pow, hm4_pow])
      have hp_ub : 2 ^ (nu4 + 1) ≤ 3 * nu2 + 6 := by omega
      have ha3_ub : s3.a ≤ 3 * nu2 + 7 := by omega
      rcases (show nu2 = 8 ∨ nu2 = 9 ∨ nu2 ≥ 10 by omega) with h8 | h9 | h10
      · have hnu4_le3 : nu4 ≤ 3 := by
          rcases (show nu4 ≤ 3 ∨ nu4 = 4 ∨ nu4 ≥ 5 by omega) with h | h4 | h5
          · exact h
          · rw [h4] at hp_ub; omega
          · have := pow_two_ge_16 nu4 h5; omega
        rcases (show nu4 = 1 ∨ nu4 = 2 ∨ nu4 = 3 by omega) with hnu4 | hnu4 | hnu4 <;>
          (rw [h8] at hm2_ge_pow ha3_ub; rw [hnu4] at hm4_pow; norm_num at hm2_ge_pow hm4_pow; omega)
      · have hnu4_le3 : nu4 ≤ 3 := by
          rcases (show nu4 ≤ 3 ∨ nu4 = 4 ∨ nu4 ≥ 5 by omega) with h | h4 | h5
          · exact h
          · rw [h4] at hL hdvd; norm_num at hdvd; omega
          · have := pow_two_ge_16 nu4 h5; omega
        rcases (show nu4 = 1 ∨ nu4 = 2 ∨ nu4 = 3 by omega) with hnu4 | hnu4 | hnu4 <;>
          (rw [h9] at hm2_ge_pow ha3_ub; rw [hnu4] at hm4_pow; norm_num at hm2_ge_pow hm4_pow; omega)
      · have hprod : m4_2 ≤ (3 * nu2 + 6) * (3 * nu2 + 7) := by
          rw [← hm4_pow]; exact Nat.mul_le_mul hp_ub ha3_ub
        have hq := quad_step2a_lt nu2 h10
        omega
  · -- Branch 3: m4_2 < m2_2
    by_cases hnu4_ge : nu2 ≤ nu4
    · -- Subbranch 3a: nu2 ≤ nu4 and 2^(nu4+1)*a3 < 2^(nu2+1)*a1
      have hdvd : 2 ^ (nu2 + 1) ≤ m2_2 - m4_2 := by
        rw [← hm2_pow, ← hm4_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm4_pow, hm2_pow])
      have hquot : 2 ^ (nu4 - nu2) < s1.a := by
        have hlt_pow : 2 ^ (nu2 + 1) * (2 ^ (nu4 - nu2) * s3.a) < 2 ^ (nu2 + 1) * s1.a := by
          have heq : 2 ^ (nu2 + 1) * (2 ^ (nu4 - nu2) * s3.a) = m4_2 := by
            rw [← hm4_pow, ← Nat.mul_assoc, ← Nat.pow_add, show nu2 + 1 + (nu4 - nu2) = nu4 + 1 by omega]
          rwa [heq, hm2_pow]
        have h1 : 2 ^ (nu4 - nu2) * s3.a < s1.a := Nat.lt_of_mul_lt_mul_left hlt_pow
        have h2 : 2 ^ (nu4 - nu2) ≤ 2 ^ (nu4 - nu2) * s3.a := by
          calc 2 ^ (nu4 - nu2) = 2 ^ (nu4 - nu2) * 1 := (Nat.mul_one _).symm
            _ ≤ 2 ^ (nu4 - nu2) * s3.a := Nat.mul_le_mul_left _ (by omega)
        omega
      have hsucc := pow_two_ge_succ (nu4 - nu2)
      omega
    · -- Subbranch 3b: 1 ≤ nu4 < nu2 and m4_2 < m2_2
      have hdvd : 2 ^ (nu4 + 1) ≤ m2_2 - m4_2 := by
        rw [← hm2_pow, ← hm4_pow]
        exact pow2_dvd_diff_ge (by omega) (by omega) (by rwa [hm4_pow, hm2_pow])
      have h2a3 : 2 ^ (nu4 + 1) + 2 * s3.a ≤ 3 * nu2 + 3 * nu4 + 16 := by omega
      have ha3_ub : s3.a ≤ 3 * nu2 + 7 := by omega
      rcases (show nu2 = 8 ∨ nu2 = 9 ∨ nu2 = 10 ∨ nu2 ≥ 11 by omega) with h8 | h9 | h10 | h11
      · have hnu4_le4 : nu4 ≤ 4 := by
          by_contra h5; have := pow_two_ge_16 nu4 (by omega); omega
        rw [h8] at hm2_ge_pow h2a3 hb3_sum
        rcases (show nu4 = 1 ∨ nu4 = 2 ∨ nu4 = 3 ∨ nu4 = 4 by omega) with hnu4 | hnu4 | hnu4 | hnu4 <;>
          (rw [hnu4] at hm4_pow h2a3 hU; norm_num at hm2_ge_pow hm4_pow h2a3; omega)
      · have hnu4_le4 : nu4 ≤ 4 := by
          by_contra h5; have := pow_two_ge_16 nu4 (by omega); omega
        rw [h9] at hm2_ge_pow h2a3 hb3_sum
        rcases (show nu4 = 1 ∨ nu4 = 2 ∨ nu4 = 3 ∨ nu4 = 4 by omega) with hnu4 | hnu4 | hnu4 | hnu4 <;>
          (rw [hnu4] at hm4_pow h2a3 hU; norm_num at hm2_ge_pow hm4_pow h2a3; omega)
      · have hnu4_le4 : nu4 ≤ 4 := by
          by_contra h5; have := pow_two_ge_16 nu4 (by omega); omega
        rw [h10] at hm2_ge_pow h2a3 hb3_sum
        rcases (show nu4 = 1 ∨ nu4 = 2 ∨ nu4 = 3 ∨ nu4 = 4 by omega) with hnu4 | hnu4 | hnu4 | hnu4 <;>
          (rw [hnu4] at hm4_pow h2a3 hU; norm_num at hm2_ge_pow hm4_pow h2a3; omega)
      · have hp_ub : 2 ^ (nu4 + 1) ≤ 6 * nu2 + 11 := by omega
        have hrem_ub : m2_2 - m4_2 ≤ 6 * nu2 + 11 := by omega
        have hprod : m4_2 ≤ (6 * nu2 + 11) * (3 * nu2 + 7) := by
          rw [← hm4_pow]; exact Nat.mul_le_mul hp_ub ha3_ub
        have hexp : (6 * nu2 + 11) * (3 * nu2 + 7) + (6 * nu2 + 11) = (6 * nu2 + 11) * (3 * nu2 + 8) := by ring
        have hq := quad_step2b_lt nu2 h11
        omega

-- ----------------------------------------------------------------------------
-- Stage 5C: Analytic 1-Step Inverse, Finite Preimage Exhaustion & Non-Halting
-- ----------------------------------------------------------------------------

def candPreimage (s' : OddState) (ν β : ℕ) : OddState :=
  let d := 2 - s'.d
  let b := 2 ^ (ν + 1) * s'.a - 2 + β
  let c :=
    if ν = 0 then
      if b % 4 = 1 then s'.b - d / 2 else s'.b + d / 2 - 1
    else
      (if s'.b % 2 = 0 then s'.b - 2 else s'.b) + sigma_true b d + ν
  let M := c - sigma_true b d - ν
  let a :=
    if ν = 0 then
      if b % 4 = 1 then s'.c - s'.a - 1 else s'.c + 1 - s'.a - d
    else
      s'.c + 1 + s'.a - 2 * (b / 2 + 1) - 2 * ν -
        (if b % 2 = 1 ∧ d = 2 then 2 else 0) - (if M % 2 = 0 then 0 else 2)
  ⟨a, b, c, d⟩

lemma candPreimage_eq (s s' : OddState) (hs : InSdom s) (hr : R_odd s = some s') :
    candPreimage s' (nu_of s) (s.b % 2) = s := by
  have hp := R_odd_props s s' hs hr
  have h2m : 2 ^ (nu_of s + 1) * a_next_of s = 2 * (s.b / 2 + 1) := by
    rw [← hp.2.1]; exact hp.2.2.1
  clear hp
  rcases hs with ⟨⟨ha_odd, hb_ge1, hc_ge3, hc_odd, hd⟩, hca⟩
  unfold R_odd at hr
  by_cases hlt : s.c < sigma_true s.b s.d + nu_of s
  · simp [hlt] at hr
  · simp only [hlt, ↓reduceIte] at hr
    by_cases hnu0 : nu_of s = 0
    · simp only [hnu0, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      unfold candPreimage
      dsimp only []
      simp only [hnu0, ↓reduceIte]
      have hb_rec : 2 ^ (0 + 1) * a_next_of s - 2 + s.b % 2 = s.b := by
        rw [hnu0] at h2m; omega
      have hd_rec : 2 - (2 - s.d) = s.d := by omega
      simp only [hb_rec, hd_rec]
      have hc_rec : (if s.b % 4 = 1
          then (if s.b % 4 = 1 then s.c + s.d / 2 else s.c + 1 - s.d / 2) - s.d / 2
          else (if s.b % 4 = 1 then s.c + s.d / 2 else s.c + 1 - s.d / 2) + s.d / 2 - 1) = s.c := by
        rcases hd with hd0 | hd2 <;> (split_ifs <;> omega)
      have ha_rec : (if s.b % 4 = 1
          then (if s.b % 4 = 1 then s.a + a_next_of s + 1 else s.a + a_next_of s - 1 + s.d) - a_next_of s - 1
          else (if s.b % 4 = 1 then s.a + a_next_of s + 1 else s.a + a_next_of s - 1 + s.d) + 1 - a_next_of s - s.d) = s.a := by
        rcases hd with hd0 | hd2 <;> (split_ifs <;> omega)
      rw [hc_rec, ha_rec]
    · simp only [hnu0, ↓reduceIte, Option.some.injEq] at hr
      subst hr
      unfold candPreimage
      dsimp only []
      simp only [hnu0, ↓reduceIte]
      have hb_rec : 2 ^ (nu_of s + 1) * a_next_of s - 2 + s.b % 2 = s.b := by omega
      have hd_rec : 2 - (2 - s.d) = s.d := by omega
      simp only [hb_rec, hd_rec]
      set M := s.c - sigma_true s.b s.d - nu_of s
      have hM_def : M = s.c - sigma_true s.b s.d - nu_of s := rfl
      have hc_rec : (if (if M % 2 = 0 then M + 2 else M) % 2 = 0
          then (if M % 2 = 0 then M + 2 else M) - 2
          else (if M % 2 = 0 then M + 2 else M)) + sigma_true s.b s.d + nu_of s = s.c := by
        split_ifs <;> omega
      simp only [hc_rec]
      have h2m_ge : 2 * (s.b / 2 + 1) ≥ a_next_of s := by
        rw [← h2m]
        have : 2 ^ (nu_of s + 1) ≥ 1 := Nat.one_le_two_pow
        calc 2 ^ (nu_of s + 1) * a_next_of s ≥ 1 * a_next_of s := Nat.mul_le_mul_right _ this
          _ = a_next_of s := Nat.one_mul _
      have ha_rec :
          (2 * (s.b / 2 + 1) - a_next_of s + s.a + 2 * nu_of s +
            (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0) + (if M % 2 = 0 then 0 else 2) - 1) + 1 + a_next_of s -
            2 * (s.b / 2 + 1) - 2 * nu_of s -
            (if s.b % 2 = 1 ∧ s.d = 2 then 2 else 0) -
            (if (s.c - sigma_true s.b s.d - nu_of s) % 2 = 0 then 0 else 2) = s.a := by
        rw [← hM_def]
        split_ifs <;> omega
      rw [ha_rec]

lemma nu_le_of_R_odd (s s' : OddState) (hs : InSdom s) (hr : R_odd s = some s') :
    (s'.c ≤ 15 → nu_of s ≤ 4) ∧ (s'.c ≤ 125 → nu_of s ≤ 7) := by
  have hp := R_odd_props s s' hs hr
  have h2m := hp.2.2.1
  have ha'_ge1 : s'.a ≥ 1 := by have := hp.1.1.1; omega
  have ha_ge1 : s.a ≥ 1 := by have := hs.1.1; omega
  refine ⟨?_, ?_⟩
  · intro hc15
    by_contra hgt4
    have hnu5 : nu_of s ≥ 5 := by omega
    have hz := hp.2.2.2.2.2.2.2.2 (by omega)
    have hpow := pow_two_ge_16 (nu_of s) hnu5
    have hm_ge : 2 * (s.b / 2 + 1) ≥ 2 ^ (nu_of s + 1) := by
      rw [← h2m]
      calc 2 ^ (nu_of s + 1) = 2 ^ (nu_of s + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ (nu_of s + 1) * s'.a := Nat.mul_le_mul_left _ ha'_ge1
    have h2m_2a : 2 * (s.b / 2 + 1) ≥ 2 * s'.a := by
      rw [← h2m, show nu_of s + 1 = 1 + nu_of s by omega, Nat.pow_add, Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (by
        calc 2 ^ nu_of s * s'.a ≥ 1 * s'.a := Nat.mul_le_mul_right _ Nat.one_le_two_pow
          _ = s'.a := Nat.one_mul _)
    -- Note 2 * m - s'.a ≥ m ≥ 2^5 = 32 > 15:
    have hm_half : 2 * (s.b / 2 + 1) - s'.a ≥ s.b / 2 + 1 := by omega
    omega
  · intro hc125
    by_contra hgt7
    have hnu8 : nu_of s ≥ 8 := by omega
    have hz := hp.2.2.2.2.2.2.2.2 (by omega)
    have hpow : 2 ^ (nu_of s + 1) ≥ 512 := by
      have : 2 ^ (8 + 1) ≤ 2 ^ (nu_of s + 1) := Nat.pow_le_pow_right (by decide) (by omega)
      norm_num at this; exact this
    have hm_ge : 2 * (s.b / 2 + 1) ≥ 2 ^ (nu_of s + 1) := by
      rw [← h2m]
      calc 2 ^ (nu_of s + 1) = 2 ^ (nu_of s + 1) * 1 := (Nat.mul_one _).symm
        _ ≤ 2 ^ (nu_of s + 1) * s'.a := Nat.mul_le_mul_left _ ha'_ge1
    have h2m_2a : 2 * (s.b / 2 + 1) ≥ 2 * s'.a := by
      rw [← h2m, show nu_of s + 1 = 1 + nu_of s by omega, Nat.pow_add, Nat.mul_assoc]
      exact Nat.mul_le_mul_left 2 (by
        calc 2 ^ nu_of s * s'.a ≥ 1 * s'.a := Nat.mul_le_mul_right _ Nat.one_le_two_pow
          _ = s'.a := Nat.one_mul _)
    omega

def validPreimages (s' : OddState) (max_nu : ℕ) : List OddState :=
  ((List.range (max_nu + 1)).flatMap fun ν =>
    [0, 1].map fun β => candPreimage s' ν β).filter fun s =>
      bInSdom s && (R_odd s == some s')

lemma validPreimages_complete (s s' : OddState) (max_nu : ℕ)
    (hs : InSdom s) (hr : R_odd s = some s') (hnu : nu_of s ≤ max_nu) :
    s ∈ validPreimages s' max_nu := by
  unfold validPreimages
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_flatMap]
    refine ⟨nu_of s, List.mem_range.mpr (by omega), ?_⟩
    rw [List.mem_map]
    refine ⟨s.b % 2, ?_, candPreimage_eq s s' hs hr⟩
    rcases Nat.mod_two_eq_zero_or_one s.b with h | h <;> simp [h]
  · simp [(bInSdom_iff s).mpr hs, hr]

def isHalt3Bool (s2 : OddState) : Bool :=
  bInSdom s2 &&
  match R_odd s2 with
  | none => false
  | some s1 =>
    match R_odd s1 with
    | none => false
    | some s0 => decide (s0.c < sigma_true s0.b s0.d + nu_of s0)

def halt3_window : List OddState :=
  (([1, 2, 3, 4, 5, 6, 7] : List ℕ).flatMap fun ν2 =>
    [1, 3].flatMap fun a1 =>
      [0, 1].flatMap fun β2 =>
        (([3, 5, 7, 9, 11, 13] : List ℕ).filter (fun c2 => ν2 ≤ c2 && 2 * a1 + c2 ≤ ν2 + 11)).flatMap fun c2 =>
          ([1, 3, 5, 7, 9, 11, 13].filter (· ≤ c2)).flatMap fun a2 =>
            [0, 2].map fun d2 =>
              ⟨a2, 2 ^ (ν2 + 1) * a1 - 2 + β2, c2, d2⟩).filter isHalt3Bool

def w3_list : List OddState :=
  [⟨3, 6, 3, 2⟩, ⟨1, 7, 3, 0⟩, ⟨5, 31, 5, 0⟩, ⟨3, 62, 7, 0⟩,
   ⟨3, 63, 7, 2⟩, ⟨3, 126, 7, 2⟩, ⟨1, 127, 7, 0⟩]

lemma halt3_window_eq : halt3_window = w3_list := by decide

def halt4_window : List OddState :=
  w3_list.flatMap fun s2 => validPreimages s2 4

def w4_list : List OddState :=
  [⟨1, 4, 5, 0⟩, ⟨3, 5, 61, 2⟩, ⟨3, 5, 63, 0⟩, ⟨5, 4, 125, 0⟩]

lemma halt4_window_eq : halt4_window = w4_list := by decide

def halt5_window : List OddState :=
  w4_list.flatMap fun s3 => validPreimages s3 7

def w5_list : List OddState :=
  [⟨3, 1, 3, 2⟩, ⟨1, 2, 3, 2⟩, ⟨9, 46, 9, 0⟩, ⟨9, 47, 9, 2⟩]

lemma halt5_window_eq : halt5_window = w5_list := by decide

def halt6_window : List OddState :=
  w5_list.flatMap fun s4 => validPreimages s4 4

lemma w3_list_c_le : ∀ s ∈ w3_list, s.c ≤ 15 := by decide

lemma w4_list_c_le : ∀ s ∈ w4_list, s.c ≤ 125 := by decide

lemma w5_list_c_le : ∀ s ∈ w5_list, s.c ≤ 15 := by decide

lemma halt6_window_eq_nil : halt6_window = [] := by decide

lemma odd_mem_13 {x : ℕ} (hodd : x % 2 = 1) (hlo : x ≥ 1) (hhi : x ≤ 13) :
    x ∈ ([1, 3, 5, 7, 9, 11, 13] : List ℕ) := by
  rcases (show x = 1 ∨ x = 3 ∨ x = 5 ∨ x = 7 ∨ x = 9 ∨ x = 11 ∨ x = 13 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma odd_mem_3_13 {x : ℕ} (hodd : x % 2 = 1) (hlo : x ≥ 3) (hhi : x ≤ 13) :
    x ∈ ([3, 5, 7, 9, 11, 13] : List ℕ) := by
  rcases (show x = 3 ∨ x = 5 ∨ x = 7 ∨ x = 9 ∨ x = 11 ∨ x = 13 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl <;> simp

lemma halt5_s2_in_halt3_window (s4 s3 s2 s1 s0 : OddState)
    (hs4 : InSdom s4) (hr4 : R_odd s4 = some s3) (hr3 : R_odd s3 = some s2)
    (hr2 : R_odd s2 = some s1) (hr1 : R_odd s1 = some s0) (hr0 : R_odd s0 = none) :
    s2 ∈ halt3_window := by
  have hs3 : InSdom s3 := (R_odd_props s4 s3 hs4 hr4).1
  have hs2 : InSdom s2 := (R_odd_props s3 s2 hs3 hr3).1
  have hp2 := R_odd_props s2 s1 hs2 hr2
  have hnu2_le7 := halt5_nu2_le_7 s4 s3 s2 s1 s0 hs4 hr4 hr3 hr2 hr1 hr0
  have hstep1 := halt3_step1_bounds s2 s1 s0 hs2 hr2 hr1 hr0
  have hnu2_ge1 := hstep1.1
  have hb1 := hstep1.2.2.1 hnu2_le7
  have hnohalt2 : ¬(s2.c < sigma_true s2.b s2.d + nu_of s2) := by
    intro hlt; rw [(R_odd_halt_iff s2).mpr hlt] at hr2; cases hr2
  have hc2_le13 : s2.c ≤ 13 := by
    have := hs2.1.2.2.2.1; have := hp2.1.1.1; omega
  unfold halt3_window
  rw [List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_flatMap]
    have hnu2_mem : nu_of s2 ∈ ([1, 2, 3, 4, 5, 6, 7] : List ℕ) := by
      rcases (show nu_of s2 = 1 ∨ nu_of s2 = 2 ∨ nu_of s2 = 3 ∨ nu_of s2 = 4 ∨
          nu_of s2 = 5 ∨ nu_of s2 = 6 ∨ nu_of s2 = 7 by omega) with
        h | h | h | h | h | h | h <;> simp [h]
    refine ⟨nu_of s2, hnu2_mem, ?_⟩
    rw [List.mem_flatMap]
    have ha1_mem : s1.a ∈ ([1, 3] : List ℕ) := by
      have := hp2.1.1.1
      rcases (show s1.a = 1 ∨ s1.a = 3 by omega) with h | h <;> simp [h]
    refine ⟨s1.a, ha1_mem, ?_⟩
    rw [List.mem_flatMap]
    have hbeta_mem : s2.b % 2 ∈ ([0, 1] : List ℕ) := by
      rcases Nat.mod_two_eq_zero_or_one s2.b with h | h <;> simp [h]
    refine ⟨s2.b % 2, hbeta_mem, ?_⟩
    rw [List.mem_flatMap]
    have hc2_mem : s2.c ∈ ([3, 5, 7, 9, 11, 13] : List ℕ).filter
        (fun c2 => nu_of s2 ≤ c2 && 2 * s1.a + c2 ≤ nu_of s2 + 11) := by
      rw [List.mem_filter]
      exact ⟨odd_mem_3_13 hs2.1.2.2.2.1 hs2.1.2.2.1 hc2_le13,
        by simp [show nu_of s2 ≤ s2.c by omega, hb1.2.2.2]⟩
    refine ⟨s2.c, hc2_mem, ?_⟩
    rw [List.mem_flatMap]
    have ha2_mem : s2.a ∈ ([1, 3, 5, 7, 9, 11, 13] : List ℕ).filter (· ≤ s2.c) :=
      List.mem_filter.mpr ⟨odd_mem_13 hs2.1.1 (by have := hs2.1.1; omega) (by have := hs2.2; omega),
        decide_eq_true hs2.2⟩
    refine ⟨s2.a, ha2_mem, ?_⟩
    rw [List.mem_map]
    have hd2_mem : s2.d ∈ ([0, 2] : List ℕ) := by
      rcases hs2.1.2.2.2.2 with h | h <;> simp [h]
    refine ⟨s2.d, hd2_mem, ?_⟩
    have hb2_eq : 2 ^ (nu_of s2 + 1) * s1.a - 2 + s2.b % 2 = s2.b := by
      have := hp2.2.2.1; omega
    rcases s2 with ⟨a2, b2, c2, d2⟩
    dsimp at hb2_eq ⊢
    rw [hb2_eq]
  · unfold isHalt3Bool
    simp [(bInSdom_iff s2).mpr hs2, hr2, hr1, (R_odd_halt_iff s0).mp hr0]

theorem no_halt6 (s5 s4 s3 s2 s1 s0 : OddState)
    (hs5 : InSdom s5) (hr5 : R_odd s5 = some s4) (hr4 : R_odd s4 = some s3)
    (hr3 : R_odd s3 = some s2) (hr2 : R_odd s2 = some s1)
    (hr1 : R_odd s1 = some s0) (hr0 : R_odd s0 = none) : False := by
  have hs4 : InSdom s4 := (R_odd_props s5 s4 hs5 hr5).1
  have hs3 : InSdom s3 := (R_odd_props s4 s3 hs4 hr4).1
  have hm2 : s2 ∈ w3_list := halt3_window_eq ▸ halt5_s2_in_halt3_window s4 s3 s2 s1 s0 hs4 hr4 hr3 hr2 hr1 hr0
  have hc2 : s2.c ≤ 15 := w3_list_c_le s2 hm2
  have hnu3 : nu_of s3 ≤ 4 := (nu_le_of_R_odd s3 s2 hs3 hr3).1 hc2
  have hm3 : s3 ∈ w4_list := halt4_window_eq ▸ by
    unfold halt4_window; rw [List.mem_flatMap]
    exact ⟨s2, hm2, validPreimages_complete s3 s2 4 hs3 hr3 hnu3⟩
  have hc3 : s3.c ≤ 125 := w4_list_c_le s3 hm3
  have hnu4 : nu_of s4 ≤ 7 := (nu_le_of_R_odd s4 s3 hs4 hr4).2 hc3
  have hm4 : s4 ∈ w5_list := halt5_window_eq ▸ by
    unfold halt5_window; rw [List.mem_flatMap]
    exact ⟨s3, hm3, validPreimages_complete s4 s3 7 hs4 hr4 hnu4⟩
  have hc4 : s4.c ≤ 15 := w5_list_c_le s4 hm4
  have hnu5 : nu_of s5 ≤ 4 := (nu_le_of_R_odd s5 s4 hs5 hr5).1 hc4
  have hm5 : s5 ∈ halt6_window := by
    unfold halt6_window; rw [List.mem_flatMap]
    exact ⟨s4, hm4, validPreimages_complete s5 s4 4 hs5 hr5 hnu5⟩
  rw [halt6_window_eq_nil] at hm5
  cases hm5

def P5 (s : OddState) : Prop :=
  InSdom s ∧ ∃ s1 s2 s3 s4 s5,
    R_odd s = some s1 ∧ R_odd s1 = some s2 ∧ R_odd s2 = some s3 ∧
    R_odd s3 = some s4 ∧ R_odd s4 = some s5

lemma P5_step (s : OddState) (h : P5 s) :
    ∃ s1, R_odd s = some s1 ∧ P5 s1 := by
  rcases h with ⟨hs, s1, s2, s3, s4, s5, hr0, hr1, hr2, hr3, hr4⟩
  refine ⟨s1, hr0, (R_odd_props s s1 hs hr0).1, ?_⟩
  rcases hr5 : R_odd s5 with _ | s6
  · exfalso; exact no_halt6 s s1 s2 s3 s4 s5 hs hr0 hr1 hr2 hr3 hr4 hr5
  · exact ⟨s2, s3, s4, s5, s6, hr1, hr2, hr3, hr4, hr5⟩

def s0_odd : OddState := ⟨1, 1, 5, 0⟩

lemma P5_s0_odd : P5 s0_odd := by
  refine ⟨(bInSdom_iff s0_odd).mp (by decide),
    ⟨1, 5, 3, 2⟩, ⟨3, 4, 5, 0⟩, ⟨3, 6, 5, 2⟩, ⟨1, 3, 15, 0⟩, ⟨1, 16, 5, 2⟩,
    by decide, by decide, by decide, by decide, by decide⟩

lemma c319_eq_s0_odd :
    c319_sq = (.h10B, [.A 1], enc_odd s0_odd.a s0_odd.b s0_odd.c s0_odd.d) := rfl

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  obtain ⟨n₀, hinit⟩ := init_reaches_c319
  rw [c319_eq_s0_odd] at hinit
  refine IsNotHalt.of_reachesPlus_invariant hinit
    (P := fun cfg => ∃ n s, P5 s ∧ cfg = decode_sq n (.h10B, [.A 1], enc_odd s.a s.b s.c s.d))
    ⟨n₀, s0_odd, P5_s0_odd, rfl⟩ ?_
  rintro cfg ⟨n, s, hP5, rfl⟩
  obtain ⟨s', hr, hP5'⟩ := P5_step s hP5
  obtain ⟨n', hplus⟩ := sqReachesPlus_to_tm (R_odd_sound s s' hP5.1.1 hr) n
  exact ⟨_, hplus, n', s', hP5', rfl⟩

end BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF
