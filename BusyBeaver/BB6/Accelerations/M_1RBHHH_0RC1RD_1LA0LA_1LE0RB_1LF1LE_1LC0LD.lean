/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.BB6.Accelerations.Stack
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`

Formal `HasStackReduction` proof for the 6-state, 2-symbol Busy Beaver holdout
`1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD`
(see <https://wiki.bbchallenge.org/wiki/1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD>).

Both half-tapes are encoded as unary digit stacks `encStack : List ℕ → ListBlank (Fin 2)` sending
`[a₀, a₁, …]` to `1^{a₀ + 1} 0 1^{a₁ + 1} 0 …`. Under the state relabeling
`(A, B, C, D, E, F) = (3, 4, 5, 2, 0, 1)`, the blank-tape trajectory enters the 4-mode stack
system `{BR, FL, AL, CR}` in 1 step and is closed under `ReachesPlus` up to halting (`01 -> ---`),
with mode `CR` on `1 :: R'` evaluated via well-founded colexicographic induction (`rvec`,
`ColexLt`) on the inner right-stack transducer.
-/

@[expose] public section

namespace BusyBeaver.M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD

open Turing Stack

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

/-! ## Permuted State Labels and Stack Encoding Helpers -/

private abbrev A : Fin 6 := 3
private abbrev B : Fin 6 := 4
private abbrev C : Fin 6 := 5
private abbrev D : Fin 6 := 2
private abbrev E : Fin 6 := 0
private abbrev F : Fin 6 := 1

private theorem encStack_nil : encStack [] = default := rfl

private theorem encStack_cons_head (a : ℕ) (L : List ℕ) :
    (encStack (a :: L)).head = (1 : Fin 2) := by
  simp [encStack, list_pow_succ]

private theorem cons_one_encStack_tail (a : ℕ) (L : List ℕ) :
    (1 : Fin 2) >> (encStack (a :: L)).tail = encStack (a :: L) := by
  simp [encStack, list_pow_succ]

private theorem bumpHead_cons (a : ℕ) (L : List ℕ) :
    bumpHead (a :: L) = (a + 1) :: L := rfl

private theorem encStack_zero (L : List ℕ) :
    encStack (0 :: L) = (1 : Fin 2) >> (0 : Fin 2) >> encStack L := rfl

private theorem encStack_zero_nil : encStack [0] = (1 : Fin 2) >> default := by
  rw [encStack_zero, encStack_nil, ListBlank.cons_zero_default]

private theorem encStack_succ (a : ℕ) (L : List ℕ) :
    encStack ((a + 1) :: L) = (1 : Fin 2) >> encStack (a :: L) := by
  simp only [encStack, ListBlank.append_pow_succ, ListBlank.append_cons, ListBlank.append_nil]

private theorem encStack_bumpHead (L : List ℕ) :
    encStack (bumpHead L) = (1 : Fin 2) >> encStack L := by
  rcases L with _ | ⟨a, L'⟩
  · exact encStack_zero_nil
  · exact encStack_succ a L'

local macro "finish" : tactic => `(tactic| (
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.mk_nil, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default,
    encStack_nil, encStack_zero, encStack_succ, encStack_bumpHead,
    encStack_cons_head, cons_one_encStack_tail]
  exact ReachesStar.refl _ _))

local macro "step" : tactic => `(tactic| (
  try simp only [Cfg.headRight, Cfg.headLeft, init, Tape.mk₁, Tape.mk₂, Tape.mk',
    ListBlank.mk_nil, list_pow_succ, list_pow_zero, List.cons_append, List.nil_append,
    ListBlank.append_cons, ListBlank.append_nil, ListBlank.head_cons, ListBlank.tail_cons,
    ListBlank.cons_zero_default, ListBlank.head_default_fin, ListBlank.tail_default,
    encStack_nil, encStack_zero, encStack_succ, encStack_bumpHead,
    encStack_cons_head, cons_one_encStack_tail]
  first
  | refine ReachesPlus.head (by rfl) ?_
  | refine ReachesStar.head (by rfl) ?_
  simp only [Tape.move, Tape.write, list_pow_succ, list_pow_zero,
    List.cons_append, List.nil_append, ListBlank.append_cons, ListBlank.append_nil,
    ListBlank.head_cons, ListBlank.tail_cons, ListBlank.cons_zero_default,
    ListBlank.head_default_fin, ListBlank.tail_default,
    encStack_nil, encStack_zero, encStack_succ, encStack_bumpHead,
    encStack_cons_head, cons_one_encStack_tail]))

local macro "execute" n:num : tactic => `(tactic| (
  iterate $n step
  finish))

/-! ## Outer Stack Modes and Inner Transducer Configurations -/

private inductive StackMode
  | BR
  | FL
  | AL
  | CR
  deriving DecidableEq

private def evalStackCfg : StackMode → List ℕ → List ℕ → Cfg (Fin 2) (Fin 6)
  | .BR, L, R => (encStack L) <{{B}} (encStack R)
  | .FL, L, R => (encStack L) {{F}}> (encStack R)
  | .AL, L, R => (encStack L) {{A}}> (encStack R)
  | .CR, L, R => (encStack L) <{{C}} (encStack R)

private def IsInStackSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ m L R, cfg = evalStackCfg m L R

private def cfg_BR1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (encStack R) <{{B}} (encStack L)
private def cfg_FL1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (encStack R) {{F}}> (encStack L)
private def cfg_AL1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (encStack R) {{A}}> (encStack L)
private def cfg_CR1 (L R : List ℕ) : Cfg (Fin 2) (Fin 6) := (encStack R) <{{C}} (encStack L)

private theorem in_BR1 (L R : List ℕ) : IsInStackSystem (cfg_BR1 L R) :=
  ⟨.BR, R, L, rfl⟩

private theorem in_FL1 (L R : List ℕ) : IsInStackSystem (cfg_FL1 L R) :=
  ⟨.FL, R, L, rfl⟩

private theorem in_AL1 (L R : List ℕ) : IsInStackSystem (cfg_AL1 L R) :=
  ⟨.AL, R, L, rfl⟩

private theorem in_CR1 (L R : List ℕ) : IsInStackSystem (cfg_CR1 L R) :=
  ⟨.CR, R, L, rfl⟩

private abbrev bump2 (L : List ℕ) : List ℕ := bumpHead (bumpHead L)
private abbrev bump3 (L : List ℕ) : List ℕ := bumpHead (bump2 L)

private def tok10 (W : ListBlank (Fin 2)) : ListBlank (Fin 2) := (1 : Fin 2) >> (0 : Fin 2) >> W
private def tok1 (W : ListBlank (Fin 2)) : ListBlank (Fin 2) := (1 : Fin 2) >> W
private def tok0 (W : ListBlank (Fin 2)) : ListBlank (Fin 2) := (0 : Fin 2) >> W

private def FwdA (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W {{A}}> (encStack L)
private def FwdF : List ℕ → ListBlank (Fin 2) → Cfg (Fin 2) (Fin 6)
  | [], W => W {{F}}> (encStack [0])
  | a :: L, W => W {{F}}> ((0 : Fin 2) >> (encStack (a :: L)).tail)
private def RetB (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{B}} (encStack L)
private def RetC (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{C}} (encStack L)
private def RetD (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{D}} (encStack L)
private def RetE (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{E}} ((1 : Fin 2) >> encStack L)
private def RetE0 (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{E}} ((0 : Fin 2) >> encStack L)
private def RetA (L : List ℕ) (W : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  W <{{A}} ((0 : Fin 2) >> encStack L)

/-! ## Concrete Micro-Step Transitions -/

private theorem step_FwdA_nil (W : ListBlank (Fin 2)) :
    (FwdA [] W) [target]⊢⁺ RetB [0] W := by
  unfold FwdA RetB
  execute 1

private theorem step_FwdA_0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA (0 :: L) W) [target]⊢⁺ FwdF L (tok10 W) := by
  rcases L with _ | ⟨a, L'⟩ <;>
  · unfold FwdA FwdF tok10
    execute 4

private theorem step_FwdA_1 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA (1 :: L) W) [target]⊢⁺ RetB (bumpHead L) (tok10 W) := by
  unfold FwdA RetB tok10
  execute 3

private theorem step_FwdA_ge2 (a : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA ((a + 2) :: L) W) [target]⊢⁺ FwdA (a :: L) (tok10 W) := by
  unfold FwdA tok10
  execute 2

private theorem step_FwdF_nil (W : ListBlank (Fin 2)) :
    (FwdF [] W) [target]⊢⁺ RetB [0] (tok1 W) := by
  unfold FwdF RetB tok1
  execute 2

private theorem step_FwdF_0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdF (0 :: L) W) [target]⊢⁺ FwdA L (tok1 (tok1 W)) := by
  unfold FwdF FwdA tok1
  execute 4

private theorem step_FwdF_succ (a : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdF ((a + 1) :: L) W) [target]⊢⁺ FwdF (a :: L) (tok1 W) := by
  unfold FwdF tok1
  execute 3

private theorem step_RetB_tok10 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB L (tok10 W)) [target]⊢⁺ RetC (bump2 L) W := by
  unfold RetB RetC tok10
  execute 2

private theorem step_RetC_tok10 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetC L (tok10 W)) [target]⊢⁺ RetB (0 :: L) W := by
  unfold RetC RetB tok10
  execute 2

private theorem step_RetD_tok10 (d : ℕ) (M : List ℕ) (W : ListBlank (Fin 2)) :
    (RetD (d :: M) (tok10 W)) [target]⊢⁺ FwdF ((d + 1) :: M) (tok1 W) := by
  unfold RetD FwdF tok10 tok1
  execute 2

private theorem step_RetE_tok10_halt (L : List ℕ) (W : ListBlank (Fin 2)) :
    (step target (RetE L (tok10 W))).isNone = true := by
  unfold RetE tok10
  bb_halt

private theorem step_RetE0_tok10_halt (L : List ℕ) (W : ListBlank (Fin 2)) :
    (step target (RetE0 L (tok10 W))).isNone = true := by
  unfold RetE0 tok10
  bb_halt

private theorem step_RetB_tok1 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB L (tok1 W)) [target]⊢⁺ RetB (bumpHead L) W := by
  unfold RetB tok1
  execute 1

private theorem step_RetC_tok1 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetC L (tok1 W)) [target]⊢⁺ RetA L W := by
  unfold RetC RetA tok1
  execute 1

private theorem step_RetD_tok1 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetD L (tok1 W)) [target]⊢⁺ RetE0 L W := by
  unfold RetD RetE0 tok1
  execute 1

private theorem step_RetE_tok1_halt (L : List ℕ) (W : ListBlank (Fin 2)) :
    (step target (RetE L (tok1 W))).isNone = true := by
  unfold RetE tok1
  bb_halt

private theorem step_RetE0_tok1_halt (L : List ℕ) (W : ListBlank (Fin 2)) :
    (step target (RetE0 L (tok1 W))).isNone = true := by
  unfold RetE0 tok1
  bb_halt

private theorem step_RetA_tok1 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetA L (tok1 W)) [target]⊢⁺ FwdF L (tok10 W) := by
  rcases L with _ | ⟨a, L'⟩ <;>
  · unfold RetA FwdF tok1 tok10
    execute 4

private theorem step_RetB_tok0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB L (tok0 W)) [target]⊢⁺ RetC (bumpHead L) W := by
  unfold RetB RetC tok0
  execute 1

private theorem step_RetC_tok0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetC L (tok0 W)) [target]⊢⁺ RetD (bumpHead L) W := by
  unfold RetC RetD tok0
  execute 1

private theorem step_RetD_tok0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetD L (tok0 W)) [target]⊢⁺ RetE L W := by
  unfold RetD RetE tok0
  execute 1

private theorem step_RetE_tok0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetE L (tok0 W)) [target]⊢⁺ FwdA L (tok1 (tok1 W)) := by
  unfold RetE FwdA tok0 tok1
  execute 2

private theorem step_RetE0_tok0 (d : ℕ) (M : List ℕ) (W : ListBlank (Fin 2)) :
    (RetE0 (d :: M) (tok0 W)) [target]⊢⁺ FwdF ((d + 1) :: M) (tok1 W) := by
  unfold RetE0 FwdF tok0 tok1
  execute 1

private theorem step_RetA_tok0 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetA L (tok0 W)) [target]⊢⁺ RetB (0 :: L) W := by
  unfold RetA RetB tok0
  execute 1

private theorem stepStar_FwdF_drain (a : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdF (a :: L) W) [target]⊢* FwdF (0 :: L) ((tok1^[a]) W) := by
  induction a generalizing W with
  | zero => exact ReachesStar.refl target _
  | succ a' ih =>
    rw [Function.iterate_succ_apply]
    exact (step_FwdF_succ a' L W).to_star.trans (ih (tok1 W))

private theorem stepPlus_FwdF_cons (a : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdF (a :: L) W) [target]⊢⁺ FwdA L ((tok1^[a + 2]) W) := by
  have h1 := stepStar_FwdF_drain a L W
  have h2 := step_FwdF_0 L ((tok1^[a]) W)
  have h3 : tok1 (tok1 ((tok1^[a]) W)) = (tok1^[a + 2]) W := by
    rw [Nat.add_comm a 2, Function.iterate_add_apply, Function.iterate_succ_apply',
      Function.iterate_one]
  rw [h3] at h2
  exact h1.trans_plus h2

private theorem stepPlus_RetD_tok10 (d : ℕ) (M : List ℕ) (W : ListBlank (Fin 2)) :
    (RetD (d :: M) (tok10 W)) [target]⊢⁺ FwdA M ((tok1^[d + 4]) W) := by
  have s1 := step_RetD_tok10 d M W
  have s2 := stepPlus_FwdF_cons (d + 1) M (tok1 W)
  have htok : (tok1^[d + 1 + 2]) (tok1 W) = (tok1^[d + 4]) W := by
    rw [← Function.iterate_succ_apply]
  rw [htok] at s2
  exact s1.trans s2

private theorem stepPlus_RetE0_tok0 (d : ℕ) (M : List ℕ) (W : ListBlank (Fin 2)) :
    (RetE0 (d :: M) (tok0 W)) [target]⊢⁺ FwdA M ((tok1^[d + 4]) W) := by
  have s1 := step_RetE0_tok0 d M W
  have s2 := stepPlus_FwdF_cons (d + 1) M (tok1 W)
  have htok : (tok1^[d + 1 + 2]) (tok1 W) = (tok1^[d + 4]) W := by
    rw [← Function.iterate_succ_apply]
  rw [htok] at s2
  exact s1.trans s2

private theorem tok1_iter_tok0_encStack (n : ℕ) (R : List ℕ) :
    (tok1^[n + 1]) (tok0 (encStack R)) = encStack (n :: R) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [Function.iterate_succ_apply', ih, tok1, encStack_succ]

private theorem tok1_iter_encStack (n : ℕ) (R : List ℕ) :
    (tok1^[n]) (encStack R) = encStack ((bumpHead^[n]) R) := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, tok1,
      encStack_bumpHead]

/-! ## Outer Mode Closure (`BR`, `FL`, `AL`, and `CR` Entry) -/

private theorem step_BR1_nil (L : List ℕ) :
    (cfg_BR1 L []) [target]⊢⁺ cfg_CR1 (bumpHead L) [] := by
  unfold cfg_BR1 cfg_CR1
  execute 1

private theorem step_BR1_0 (L R' : List ℕ) :
    (cfg_BR1 L (0 :: R')) [target]⊢⁺ cfg_CR1 (bump2 L) R' := by
  unfold cfg_BR1 cfg_CR1
  execute 2

private theorem step_BR1_succ (L : List ℕ) (b : ℕ) (R' : List ℕ) :
    (cfg_BR1 L ((b + 1) :: R')) [target]⊢⁺ cfg_BR1 (bumpHead L) (b :: R') := by
  unfold cfg_BR1
  execute 1

private theorem close_BR1 (L R : List ℕ) :
    ∃ cfg, ((cfg_BR1 L R) [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases R with _ | ⟨d, R'⟩
  · exact ⟨cfg_CR1 (bumpHead L) [], step_BR1_nil L, Or.inl (in_CR1 _ _)⟩
  · rcases d with _ | b
    · exact ⟨cfg_CR1 (bump2 L) R', step_BR1_0 L R', Or.inl (in_CR1 _ _)⟩
    · exact ⟨cfg_BR1 (bumpHead L) (b :: R'), step_BR1_succ L b R', Or.inl (in_BR1 _ _)⟩

private theorem step_FL1_nil (R : List ℕ) :
    (cfg_FL1 [] R) [target]⊢⁺ cfg_FL1 [0] (bumpHead R) := by
  unfold cfg_FL1
  execute 3

private theorem step_FL1_0 (L' R : List ℕ) :
    (cfg_FL1 (0 :: L') R) [target]⊢⁺ cfg_BR1 (bumpHead L') (bumpHead R) := by
  unfold cfg_FL1 cfg_BR1
  execute 2

private theorem step_FL1_succ (a : ℕ) (L' R : List ℕ) :
    (cfg_FL1 ((a + 1) :: L') R) [target]⊢⁺ cfg_AL1 (a :: L') (bumpHead R) := by
  unfold cfg_FL1 cfg_AL1
  execute 1

private theorem close_FL1 (L R : List ℕ) :
    ∃ cfg, ((cfg_FL1 L R) [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases L with _ | ⟨a, L'⟩
  · exact ⟨cfg_FL1 [0] (bumpHead R), step_FL1_nil R, Or.inl (in_FL1 _ _)⟩
  · rcases a with _ | a'
    · exact ⟨cfg_BR1 (bumpHead L') (bumpHead R), step_FL1_0 L' R, Or.inl (in_BR1 _ _)⟩
    · exact ⟨cfg_AL1 (a' :: L') (bumpHead R), step_FL1_succ a' L' R, Or.inl (in_AL1 _ _)⟩

private theorem step_AL1_nil (R : List ℕ) :
    (cfg_AL1 [] R) [target]⊢⁺ cfg_BR1 [0] R := by
  unfold cfg_AL1 cfg_BR1
  execute 1

private theorem step_AL1_0_nil (R : List ℕ) :
    (cfg_AL1 [0] R) [target]⊢⁺ cfg_FL1 [0] (0 :: R) := by
  unfold cfg_AL1 cfg_FL1
  execute 4

private theorem step_AL1_0_cons_in (b : ℕ) (L' R : List ℕ) :
    (cfg_AL1 (0 :: b :: L') R) [target]⊢⁺ FwdF ((b + 1) :: L') (tok0 (encStack R)) := by
  unfold cfg_AL1 FwdF tok0
  execute 1

private theorem step_AL1_0_cons (b : ℕ) (L' R : List ℕ) :
    (cfg_AL1 (0 :: b :: L') R) [target]⊢⁺ cfg_AL1 L' ((b + 2) :: R) := by
  have s1 := step_AL1_0_cons_in b L' R
  have s2 := stepPlus_FwdF_cons (b + 1) L' (tok0 (encStack R))
  have htok : (tok1^[b + 1 + 2]) (tok0 (encStack R)) = encStack ((b + 2) :: R) :=
    tok1_iter_tok0_encStack (b + 2) R
  rw [htok] at s2
  exact s1.trans s2

private theorem step_AL1_1 (L' R : List ℕ) :
    (cfg_AL1 (1 :: L') R) [target]⊢⁺ cfg_BR1 (bumpHead L') (0 :: R) := by
  unfold cfg_AL1 cfg_BR1
  execute 3

private theorem step_AL1_ge2 (a : ℕ) (L' R : List ℕ) :
    (cfg_AL1 ((a + 2) :: L') R) [target]⊢⁺ cfg_AL1 (a :: L') (0 :: R) := by
  unfold cfg_AL1
  execute 2

private theorem close_AL1 (L R : List ℕ) :
    ∃ cfg, ((cfg_AL1 L R) [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases L with _ | ⟨a, L'⟩
  · exact ⟨cfg_BR1 [0] R, step_AL1_nil R, Or.inl (in_BR1 _ _)⟩
  · rcases a with _ | a1
    · rcases L' with _ | ⟨b, L''⟩
      · exact ⟨cfg_FL1 [0] (0 :: R), step_AL1_0_nil R, Or.inl (in_FL1 _ _)⟩
      · exact ⟨cfg_AL1 L'' ((b + 2) :: R), step_AL1_0_cons b L'' R, Or.inl (in_AL1 _ _)⟩
    · rcases a1 with _ | a2
      · exact ⟨cfg_BR1 (bumpHead L') (0 :: R), step_AL1_1 L' R, Or.inl (in_BR1 _ _)⟩
      · exact ⟨cfg_AL1 (a2 :: L') (0 :: R), step_AL1_ge2 a2 L' R, Or.inl (in_AL1 _ _)⟩

private theorem step_CR1_nil (L : List ℕ) :
    (cfg_CR1 L []) [target]⊢⁺ cfg_FL1 (bump2 L) [0] := by
  unfold cfg_CR1 cfg_FL1
  execute 3

private theorem step_CR1_0 (L R' : List ℕ) :
    (cfg_CR1 L (0 :: R')) [target]⊢⁺ cfg_BR1 (0 :: L) R' := by
  unfold cfg_CR1 cfg_BR1
  execute 2

private theorem step_CR1_ge2 (L : List ℕ) (b : ℕ) (R' : List ℕ) :
    (cfg_CR1 L ((b + 2) :: R')) [target]⊢⁺ cfg_AL1 (0 :: L) (b :: R') := by
  unfold cfg_CR1 cfg_AL1
  execute 1

private theorem step_CR1_1_entry (L R' : List ℕ) :
    (cfg_CR1 L (1 :: R')) [target]⊢⁺ FwdF L (tok1 (tok0 (tok0 (encStack R')))) := by
  rcases L with _ | ⟨a, L'⟩ <;>
  · unfold cfg_CR1 FwdF tok1 tok0
    execute 5

/-! ## Inner Transducer Weights and Zero-Weight Evaluation -/

private def wtA : List ℕ → ℕ
  | [] => 0
  | [a] => if a % 4 = 2 ∨ a % 4 = 3 then 0 else 3
  | a :: b :: L =>
    (if a % 4 = 2 then 0 else if a % 4 = 0 then 3 else if a % 4 = 1 then 7 else 8) +
      wtA (b :: L)

private def wtC : List ℕ → ℕ
  | [] => 0
  | [a] => if a % 4 = 2 ∨ a % 4 = 3 then 0 else 1
  | a :: b :: L =>
    if a % 4 = 2 then wtC (b :: L)
    else (if a % 4 = 0 then 1 else if a % 4 = 1 then 6 else 7) + wtA (b :: L)

private def elen : List ℕ → ℕ
  | [] => 0
  | a :: L => (a / 4 + 1) + elen L

private theorem wtC_two_cons (L : List ℕ) : wtC (2 :: L) = wtC L := by
  rcases L with _ | ⟨b, L'⟩
  · rfl
  · simp [wtC]

private theorem elen_two_cons (L : List ℕ) : elen (2 :: L) = 1 + elen L := rfl

private theorem elen_add4_cons (a : ℕ) (L : List ℕ) :
    elen ((a + 4) :: L) = 1 + elen (a :: L) := by
  simp only [elen]
  omega

private theorem step_FwdA_1_retC (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA (1 :: L) W) [target]⊢⁺ RetC (bump3 L) W :=
  (step_FwdA_1 L W).trans (step_RetB_tok10 (bumpHead L) W)

private theorem step_FwdA_2 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA (2 :: L) W) [target]⊢⁺ FwdF L (tok10 (tok10 W)) :=
  (step_FwdA_ge2 0 L W).trans (step_FwdA_0 L (tok10 W))

private theorem step_FwdA_3_retB (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA (3 :: L) W) [target]⊢⁺ RetB (0 :: bump3 L) W :=
  (step_FwdA_ge2 1 L W).trans
    ((step_FwdA_1_retC L (tok10 W)).trans (step_RetC_tok10 (bump3 L) W))

private theorem step_FwdA_add4 (a : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (FwdA ((a + 4) :: L) W) [target]⊢⁺ FwdA (a :: L) (tok10 (tok10 W)) :=
  (step_FwdA_ge2 (a + 2) L W).trans (step_FwdA_ge2 a L (tok10 W))

private theorem step_RetB_tok10_2 (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB (0 :: L) (tok10 (tok10 W))) [target]⊢⁺ RetB (0 :: 2 :: L) W :=
  (step_RetB_tok10 (0 :: L) (tok10 W)).trans (step_RetC_tok10 (2 :: L) W)

private theorem stepStar_RetB_tok1 (n : ℕ) (b : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB (b :: L) ((tok1^[n]) W)) [target]⊢* RetB ((b + n) :: L) W := by
  induction n generalizing b W with
  | zero =>
    simp only [Nat.add_zero, Function.iterate_zero, id_eq]
    exact ReachesStar.refl target _
  | succ n' ih =>
    rw [Function.iterate_succ_apply']
    have s1 := (step_RetB_tok1 (b :: L) ((tok1^[n']) W)).to_star
    have s2 := ih (b + 1) W
    have hadd : b + 1 + n' = b + (n' + 1) := by omega
    rw [bumpHead_cons] at s1
    rw [hadd] at s2
    exact s1.trans s2

private theorem stepStar_RetB_zero_tok1 (n : ℕ) (L : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB (0 :: L) ((tok1^[n]) W)) [target]⊢* RetB (n :: L) W := by
  have h := stepStar_RetB_tok1 n 0 L W
  rwa [Nat.zero_add] at h

private theorem step_RetB_d_tok10_2 (d : ℕ) (M : List ℕ) (W : ListBlank (Fin 2)) :
    (RetB (d :: M) (tok10 (tok10 W))) [target]⊢⁺ RetB (0 :: (d + 2) :: M) W :=
  (step_RetB_tok10 (d :: M) (tok10 W)).trans (step_RetC_tok10 ((d + 2) :: M) W)

private theorem step_FwdF_nil_retB (W : ListBlank (Fin 2)) :
    (FwdF [] W) [target]⊢⁺ RetB [1] W :=
  (step_FwdF_nil W).trans (step_RetB_tok1 [0] W)

private theorem wtC_add4_cons (a : ℕ) (L : List ℕ) :
    wtC ((a + 4) :: L) = wtC (a :: L) := by
  rcases L with _ | ⟨b, L'⟩ <;> simp only [wtC] <;> split_ifs <;> omega

private theorem wtC_zero_cons_ne0 (L : List ℕ) : wtC (0 :: L) ≠ 0 := by
  rcases L with _ | ⟨b, L'⟩ <;> simp [wtC]

private theorem wtC_one_cons_ne0 (L : List ℕ) : wtC (1 :: L) ≠ 0 := by
  rcases L with _ | ⟨b, L'⟩ <;> simp [wtC]

private theorem wtC_three_cons_cons_ne0 (b : ℕ) (L' : List ℕ) : wtC (3 :: b :: L') ≠ 0 := by
  simp [wtC]

private theorem eval_zero (L : List ℕ) (h0 : wtC L = 0) :
    (∀ W, ∃ M, ((FwdA L W) [target]⊢⁺ RetB (0 :: M) W) ∧ wtC M = 0 ∧ elen M = elen L) ∧
    (∀ W, ∃ b M, ((FwdF L W) [target]⊢⁺ RetB (b :: M) W) ∧
      wtC ((b + 2) :: M) = 0 ∧ elen ((b + 2) :: M) = elen L + 1) := by
  induction L with
  | nil =>
    refine ⟨fun W => ⟨[], step_FwdA_nil W, rfl, rfl⟩,
      fun W => ⟨1, [], step_FwdF_nil_retB W, rfl, rfl⟩⟩
  | cons a L' ih =>
    have hF : ∀ W, ∃ b M, ((FwdF (a :: L') W) [target]⊢⁺ RetB (b :: M) W) ∧
        wtC ((b + 2) :: M) = 0 ∧ elen ((b + 2) :: M) = elen (a :: L') + 1 := by
      intro W
      rcases L' with _ | ⟨c, L''⟩
      · have s1 := stepPlus_FwdF_cons a [] W
        have s2 := step_FwdA_nil ((tok1^[a + 2]) W)
        have s3 := stepStar_RetB_zero_tok1 (a + 2) [] W
        refine ⟨a + 2, [], (s1.trans s2).trans_star s3, ?_, ?_⟩
        · simp only [wtC] at h0 ⊢
          split_ifs at h0 ⊢ <;> omega
        · simp only [elen]
          omega
      · have ha2 : a % 4 = 2 := by
          simp only [wtC] at h0
          split_ifs at h0 with h <;> omega
        have hL'0 : wtC (c :: L'') = 0 := by
          simp only [wtC, ite_eq_left ha2] at h0
          exact h0
        obtain ⟨M, hstepA, hM0, hE⟩ := (ih hL'0).1 ((tok1^[a + 2]) W)
        have s1 := stepPlus_FwdF_cons a (c :: L'') W
        have s3 := stepStar_RetB_zero_tok1 (a + 2) M W
        refine ⟨a + 2, M, (s1.trans hstepA).trans_star s3, ?_, ?_⟩
        · rcases M with _ | ⟨m, M'⟩
          · simp only [wtC]
            split_ifs <;> omega
          · simp only [wtC]
            rw [ite_eq_left (by omega)]
            exact hM0
        · simp only [elen] at hE ⊢
          omega
    have hA : ∀ a : ℕ, wtC (a :: L') = 0 → ∀ W,
        ∃ M, ((FwdA (a :: L') W) [target]⊢⁺ RetB (0 :: M) W) ∧
          wtC M = 0 ∧ elen M = elen (a :: L') := by
      clear hF h0 a
      intro a
      induction a using Nat.strongRecOn with
      | ind a iha =>
        intro h0a W
        rcases a with _ | _ | _ | _ | a'
        · exact absurd h0a (wtC_zero_cons_ne0 L')
        · exact absurd h0a (wtC_one_cons_ne0 L')
        · rcases L' with _ | ⟨c, L''⟩
          · refine ⟨[3], (step_FwdA_2 [] W).trans
              ((step_FwdF_nil_retB (tok10 (tok10 W))).trans
                (step_RetB_d_tok10_2 1 [] W)), rfl, rfl⟩
          · have hL'0 : wtC (c :: L'') = 0 := by
              rw [wtC_two_cons] at h0a
              exact h0a
            obtain ⟨d, M, hstepF, hdM0, hE⟩ := (ih hL'0).2 (tok10 (tok10 W))
            refine ⟨(d + 2) :: M, (step_FwdA_2 (c :: L'') W).trans
              (hstepF.trans (step_RetB_d_tok10_2 d M W)), hdM0, ?_⟩
            rw [elen_two_cons]
            omega
        · rcases L' with _ | ⟨c, L''⟩
          · exact ⟨[2], step_FwdA_3_retB [] W, rfl, rfl⟩
          · exact absurd h0a (wtC_three_cons_cons_ne0 c L'')
        · have h0a' : wtC (a' :: L') = 0 := by
            rw [← wtC_add4_cons]
            exact h0a
          obtain ⟨M, hstep, hM0, hE⟩ := iha a' (by omega) h0a' (tok10 (tok10 W))
          refine ⟨2 :: M, (step_FwdA_add4 a' L' W).trans
            (hstep.trans (step_RetB_tok10_2 M W)), ?_, ?_⟩
          · rw [wtC_two_cons]
            exact hM0
          · rw [elen_two_cons, elen_add4_cons, hE]
    exact ⟨hA a h0, hF⟩

private def HaltsPlus (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ cfg, (c [target]⊢⁺ cfg) ∧ (step target cfg).isNone

private theorem HaltsPlus.stepPlus {c1 c2 : Cfg (Fin 2) (Fin 6)} (h12 : c1 [target]⊢⁺ c2)
    (h2 : HaltsPlus c2) : HaltsPlus c1 := by
  rcases h2 with ⟨cfg, hstep, hnone⟩
  exact ⟨cfg, h12.trans hstep, hnone⟩

private theorem haltsPlus_RetE_tok1 {c : Cfg (Fin 2) (Fin 6)} {L : List ℕ} {W : ListBlank (Fin 2)}
    (h : c [target]⊢⁺ RetE L (tok1 W)) : HaltsPlus c :=
  ⟨RetE L (tok1 W), h, step_RetE_tok1_halt L W⟩

private theorem haltsPlus_RetE_tok10 {c : Cfg (Fin 2) (Fin 6)} {L : List ℕ} {W : ListBlank (Fin 2)}
    (h : c [target]⊢⁺ RetE L (tok10 W)) : HaltsPlus c :=
  ⟨RetE L (tok10 W), h, step_RetE_tok10_halt L W⟩

private theorem haltsPlus_RetE0_tok1 {c : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetE0 L (tok1 W)) : HaltsPlus c :=
  ⟨RetE0 L (tok1 W), h, step_RetE0_tok1_halt L W⟩

private theorem haltsPlus_RetE0_tok10 {c : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetE0 L (tok10 W)) : HaltsPlus c :=
  ⟨RetE0 L (tok10 W), h, step_RetE0_tok10_halt L W⟩

private theorem haltsPlus_RetD_tok1_tok1 {c : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetD L (tok1 (tok1 W))) : HaltsPlus c :=
  haltsPlus_RetE0_tok1 (h.trans (step_RetD_tok1 L (tok1 W)))

private theorem haltsPlus_RetE_tok1_succ {c : Cfg (Fin 2) (Fin 6)} (n : ℕ) {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetE L ((tok1^[n + 1]) W)) :
    HaltsPlus c := by
  rw [Function.iterate_succ_apply'] at h
  exact haltsPlus_RetE_tok1 h

private theorem haltsPlus_RetE0_tok1_succ {c : Cfg (Fin 2) (Fin 6)} (n : ℕ) {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetE0 L ((tok1^[n + 1]) W)) :
    HaltsPlus c := by
  rw [Function.iterate_succ_apply'] at h
  exact haltsPlus_RetE0_tok1 h

private theorem haltsPlus_RetD_tok1_add2 {c : Cfg (Fin 2) (Fin 6)} (n : ℕ) {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : c [target]⊢⁺ RetD L ((tok1^[n + 2]) W)) :
    HaltsPlus c := by
  rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at h
  exact haltsPlus_RetD_tok1_tok1 h

/-! ## Colexicographic Rank Order and Well-Founded Induction -/

private def rvec : List ℕ → List ℕ
  | [] => [0, 0]
  | [a] => if a % 4 = 1 then [0, 1] else if a % 4 = 0 then [1, 0] else [0, 0]
  | a :: b :: L =>
    if a % 4 = 2 then rvec (b :: L)
    else if a % 4 = 0 then bumpHead (rvec (b :: L))
    else 0 :: elen (b :: L) :: rvec (b :: L)

private def ColexLt : List ℕ → List ℕ → Prop
  | [], _ :: _ => True
  | a :: xs, b :: ys => ColexLt xs ys ∨ (xs = ys ∧ a < b)
  | _, _ => False

private def ColexLe (xs ys : List ℕ) : Prop :=
  ColexLt xs ys ∨ xs = ys

private def GoodB (M L : List ℕ) : Prop :=
  ColexLe (rvec M) (rvec L)

private def GoodC (M L : List ℕ) : Prop :=
  ColexLt (rvec M) (rvec L)

private def StrongLt (M L : List ℕ) : Prop :=
  ∀ N, GoodB N M → ∀ d, GoodC (d :: N) L

private theorem acc_colex_cons {ys : List ℕ} (hys : Acc ColexLt ys) :
    ∀ b, Acc ColexLt (b :: ys) := by
  induction hys with
  | intro ys _ ih_ys =>
    intro b
    induction b using Nat.strongRecOn with
    | ind b ih_b =>
      refine Acc.intro (b :: ys) fun z h => ?_
      rcases z with _ | ⟨a, xs⟩
      · exact Acc.intro [] fun w hw => by cases w <;> cases hw
      · rcases h with hlt | ⟨rfl, hab⟩
        · exact ih_ys xs hlt a
        · exact ih_b a hab

private theorem acc_ColexLt (ys : List ℕ) : Acc ColexLt ys := by
  induction ys with
  | nil => exact Acc.intro [] fun z h => by cases z <;> cases h
  | cons b ys ih => exact acc_colex_cons ih b

private theorem colexLt_trans {xs ys zs : List ℕ} (h1 : ColexLt xs ys) (h2 : ColexLt ys zs) :
    ColexLt xs zs := by
  induction xs generalizing ys zs with
  | nil =>
    rcases ys with _ | ⟨b, ys⟩
    · cases h1
    rcases zs with _ | ⟨c, zs⟩
    · cases h2
    trivial
  | cons a xs ih =>
    rcases ys with _ | ⟨b, ys⟩
    · cases h1
    rcases zs with _ | ⟨c, zs⟩
    · cases h2
    rcases h1 with h1 | ⟨rfl, hab⟩ <;> rcases h2 with h2 | ⟨rfl, hbc⟩
    · exact Or.inl (ih h1 h2)
    · exact Or.inl h1
    · exact Or.inl h2
    · exact Or.inr ⟨rfl, by omega⟩

private theorem colexLt_of_lt_of_le {xs ys zs : List ℕ} (h1 : ColexLt xs ys) (h2 : ColexLe ys zs) :
    ColexLt xs zs := by
  rcases h2 with h2 | rfl
  · exact colexLt_trans h1 h2
  · exact h1

private theorem colexLt_of_le_of_lt {xs ys zs : List ℕ} (h1 : ColexLe xs ys) (h2 : ColexLt ys zs) :
    ColexLt xs zs := by
  rcases h1 with h1 | rfl
  · exact colexLt_trans h1 h2
  · exact h2

private theorem colexLe_trans {xs ys zs : List ℕ} (h1 : ColexLe xs ys) (h2 : ColexLe ys zs) :
    ColexLe xs zs := by
  rcases h1 with h1 | rfl
  · exact Or.inl (colexLt_of_lt_of_le h1 h2)
  · exact h2

private theorem colexLt_of_length_lt {xs ys : List ℕ} (h : xs.length < ys.length) :
    ColexLt xs ys := by
  induction xs generalizing ys with
  | nil =>
    rcases ys with _ | ⟨b, ys⟩
    · simp at h
    · trivial
  | cons a xs ih =>
    rcases ys with _ | ⟨b, ys⟩
    · simp at h
    · simp only [List.length_cons] at h
      exact Or.inl (ih (by omega))

private theorem length_le_of_colexLt {xs ys : List ℕ} (h : ColexLt xs ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => exact Nat.zero_le _
  | cons a xs ih =>
    rcases ys with _ | ⟨b, ys⟩
    · cases h
    · simp only [List.length_cons]
      rcases h with h | ⟨rfl, _⟩
      · exact Nat.succ_le_succ (ih h)
      · exact Nat.le_refl _

private theorem rvec_exists_cons (L : List ℕ) : ∃ x y xs, rvec L = x :: y :: xs := by
  induction L with
  | nil => exact ⟨0, 0, [], rfl⟩
  | cons a L' ih =>
    rcases L' with _ | ⟨b, L''⟩
    · simp only [rvec]
      split_ifs
      · exact ⟨0, 1, [], rfl⟩
      · exact ⟨1, 0, [], rfl⟩
      · exact ⟨0, 0, [], rfl⟩
    · obtain ⟨x, y, xs, h⟩ := ih
      simp only [rvec]
      split_ifs
      · exact ⟨x, y, xs, h⟩
      · rw [h]
        exact ⟨x + 1, y, xs, rfl⟩
      · exact ⟨0, elen (b :: L''), rvec (b :: L''), rfl⟩

private theorem length_bumpHead_rvec (L : List ℕ) :
    (bumpHead (rvec L)).length = (rvec L).length := by
  obtain ⟨x, y, xs, h⟩ := rvec_exists_cons L
  rw [h]
  rfl

private theorem length_rvec_ge_two (L : List ℕ) : 2 ≤ (rvec L).length := by
  obtain ⟨x, y, xs, h⟩ := rvec_exists_cons L
  rw [h]
  simp

private theorem length_rvec_singleton (a : ℕ) : (rvec [a]).length = 2 := by
  simp only [rvec]
  split_ifs <;> rfl

private theorem rvec_eq_zero_of_wtC_zero {L : List ℕ} (h0 : wtC L = 0) : rvec L = [0, 0] := by
  induction L with
  | nil => rfl
  | cons a L' ih =>
    rcases L' with _ | ⟨b, L''⟩
    · simp only [wtC] at h0
      have ha : a % 4 = 2 ∨ a % 4 = 3 := by
        split_ifs at h0 with h
        exact h
      have h1 : ¬(a % 4 = 1) := by omega
      have h0' : ¬(a % 4 = 0) := by omega
      simp only [rvec, ite_eq_right h1, ite_eq_right h0']
    · have ha2 : a % 4 = 2 := by
        simp only [wtC] at h0
        split_ifs at h0 <;> omega
      have hb0 : wtC (b :: L'') = 0 := by
        simp only [wtC, ite_eq_left ha2] at h0
        exact h0
      simp only [rvec, ite_eq_left ha2]
      exact ih hb0

private theorem colexLe_zero_two (L : List ℕ) : ColexLe [0, 0] (rvec L) := by
  obtain ⟨x, y, xs, h⟩ := rvec_exists_cons L
  rw [h]
  rcases xs with _ | ⟨z, zs⟩
  · by_cases hy : y = 0
    · subst hy
      by_cases hx : x = 0
      · subst hx
        exact Or.inr rfl
      · exact Or.inl (Or.inr ⟨rfl, by omega⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨rfl, by omega⟩))
  · exact Or.inl (Or.inl (Or.inl trivial))

private theorem goodB_of_wtC_zero {M : List ℕ} (h0 : wtC M = 0) (L : List ℕ) : GoodB M L := by
  unfold GoodB
  rw [rvec_eq_zero_of_wtC_zero h0]
  exact colexLe_zero_two L

private theorem add4_mod4 (a : ℕ) : (a + 4) % 4 = a % 4 := by omega

private theorem rvec_mod4_eq_2 {a : ℕ} (L : List ℕ) (ha : a % 4 = 2) :
    rvec (a :: L) = rvec L := by
  rcases L with _ | ⟨b, L'⟩
  · simp only [rvec, ha]
    decide
  · simp only [rvec, ite_eq_left ha]

private theorem rvec_mod4_eq_0 {a : ℕ} (L : List ℕ) (ha : a % 4 = 0) :
    rvec (a :: L) = bumpHead (rvec L) := by
  rcases L with _ | ⟨b, L'⟩
  · simp only [rvec, ha]
    decide
  · have ha2 : a % 4 ≠ 2 := by omega
    simp only [rvec, ite_eq_right ha2, ite_eq_left ha]

private theorem rvec_add4_cons (a : ℕ) (L : List ℕ) :
    rvec ((a + 4) :: L) = rvec (a :: L) := by
  rcases L with _ | ⟨b, L'⟩ <;> simp only [rvec, add4_mod4]

private theorem colexLt_bumpHead_iff (a b : ℕ) (xs ys : List ℕ) :
    ColexLt (a :: xs) (bumpHead (b :: ys)) ↔ ColexLe (a :: xs) (b :: ys) := by
  simp only [bumpHead, ColexLt, ColexLe, List.cons.injEq]
  constructor
  · rintro (h | ⟨rfl, hab⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hab) with hlt | rfl
      · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
      · exact Or.inr ⟨rfl, rfl⟩
  · rintro ((h | ⟨rfl, hab⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩

private theorem colexLe_bumpHead_iff (a b : ℕ) (xs ys : List ℕ) :
    ColexLe (bumpHead (a :: xs)) (b :: ys) ↔ ColexLt (a :: xs) (b :: ys) := by
  simp only [bumpHead, ColexLt, ColexLe, List.cons.injEq]
  constructor
  · rintro ((h | ⟨rfl, hab⟩) | ⟨rfl, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩
    · exact Or.inr ⟨rfl, by omega⟩
  · rintro (h | ⟨rfl, hab⟩)
    · exact Or.inl (Or.inl h)
    · rcases Nat.lt_or_eq_of_le hab with hlt | heq
      · exact Or.inl (Or.inr ⟨rfl, hlt⟩)
      · exact Or.inr ⟨heq, rfl⟩

private theorem colexLt_bumpHead_bumpHead_iff (a b : ℕ) (xs ys : List ℕ) :
    ColexLt (bumpHead (a :: xs)) (bumpHead (b :: ys)) ↔ ColexLt (a :: xs) (b :: ys) := by
  simp only [bumpHead, ColexLt]
  constructor <;>
  · rintro (h | ⟨rfl, hab⟩)
    · exact Or.inl h
    · exact Or.inr ⟨rfl, by omega⟩

private theorem colexLt_self_bumpHead (a : ℕ) (xs : List ℕ) :
    ColexLt (a :: xs) (bumpHead (a :: xs)) :=
  Or.inr ⟨rfl, by omega⟩

private theorem goodC_iff_goodB_of_mod4_eq_0 {a : ℕ} (M L : List ℕ) (ha : a % 4 = 0) :
    GoodC M (a :: L) ↔ GoodB M L := by
  unfold GoodC GoodB
  rw [rvec_mod4_eq_0 L ha]
  obtain ⟨x, y, xs, hM⟩ := rvec_exists_cons M
  obtain ⟨u, v, ys, hL⟩ := rvec_exists_cons L
  rw [hM, hL]
  exact colexLt_bumpHead_iff x u (y :: xs) (v :: ys)

private theorem goodB_cons_of_goodC_of_mod4_eq_0 {a : ℕ} {M L : List ℕ} (ha : a % 4 = 0)
    (h : GoodC M L) : GoodB (a :: M) L := by
  unfold GoodB GoodC at *
  rw [rvec_mod4_eq_0 M ha]
  obtain ⟨x, y, xs, hM⟩ := rvec_exists_cons M
  obtain ⟨u, v, ys, hL⟩ := rvec_exists_cons L
  rw [hM, hL] at h ⊢
  exact (colexLe_bumpHead_iff x u (y :: xs) (v :: ys)).mpr h

private theorem goodB_cons_of_goodC_even {d : ℕ} {M L : List ℕ} (heven : d % 2 = 0)
    (h : GoodC M L) : GoodB (d :: M) L := by
  have h4 : d % 4 = 2 ∨ d % 4 = 0 := by omega
  rcases h4 with h2 | h0
  · unfold GoodB
    rw [rvec_mod4_eq_2 M h2]
    exact Or.inl h
  · exact goodB_cons_of_goodC_of_mod4_eq_0 h0 h

private theorem goodC_imp_goodB {M L : List ℕ} (h : GoodC M L) : GoodB M L := Or.inl h

private theorem goodB_trans {M1 M2 M3 : List ℕ} (h12 : GoodB M1 M2) (h23 : GoodB M2 M3) :
    GoodB M1 M3 := colexLe_trans h12 h23

private theorem goodC_of_goodC_of_goodB {M1 M2 M3 : List ℕ} (h12 : GoodC M1 M2)
    (h23 : GoodB M2 M3) : GoodC M1 M3 := colexLt_of_lt_of_le h12 h23

private theorem goodC_of_goodB_of_goodC {M1 M2 M3 : List ℕ} (h12 : GoodB M1 M2)
    (h23 : GoodC M2 M3) : GoodC M1 M3 := colexLt_of_le_of_lt h12 h23

private theorem goodB_self (L : List ℕ) : GoodB L L := Or.inr rfl

private theorem strongLt_apply {M L : List ℕ} (h : StrongLt M L) (d : ℕ) : GoodC (d :: M) L :=
  h M (goodB_self M) d

private theorem strongLt_of_strongLt_of_goodB {M L1 L2 : List ℕ} (h1 : StrongLt M L1)
    (h2 : GoodB L1 L2) : StrongLt M L2 :=
  fun N hNM d => goodC_of_goodC_of_goodB (h1 N hNM d) h2

private theorem strongLt_of_goodB_of_strongLt {M1 M2 L : List ℕ} (h1 : GoodB M1 M2)
    (h2 : StrongLt M2 L) : StrongLt M1 L :=
  fun N hNM1 d => h2 N (goodB_trans hNM1 h1) d

private theorem goodB_tail_cons (a : ℕ) (L : List ℕ) : GoodB L (a :: L) := by
  rcases L with _ | ⟨b, L'⟩
  · exact goodB_of_wtC_zero rfl [a]
  · unfold GoodB
    simp only [rvec]
    split_ifs with h2 h0
    · exact Or.inr rfl
    · obtain ⟨x, y, xs, h⟩ := rvec_exists_cons (b :: L')
      rw [h]
      exact Or.inl (colexLt_self_bumpHead x (y :: xs))
    · refine Or.inl (colexLt_of_length_lt ?_)
      simp

private theorem goodB_of_strongLt {M L : List ℕ} (h : StrongLt M L) : GoodB M L :=
  goodB_trans (goodB_tail_cons 2 M) (goodC_imp_goodB (strongLt_apply h 2))

private theorem goodC_of_strongLt {M L : List ℕ} (h : StrongLt M L) : GoodC M L :=
  goodC_of_goodB_of_goodC (goodB_tail_cons 2 M) (strongLt_apply h 2)

private theorem strongLt_cons_of_strongLt_of_strongLt (d : ℕ) {M1 M L : List ℕ}
    (h1 : StrongLt M1 M) (h2 : StrongLt M L) : StrongLt (d :: M1) L :=
  strongLt_of_goodB_of_strongLt (goodC_imp_goodB (strongLt_apply h1 d)) h2

private theorem goodC_cons_of_goodC_odd {a : ℕ} {M Lp : List ℕ} (hodd : a % 2 = 1)
    (hpos : wtC Lp > 0) (h : GoodC M Lp) (d : ℕ) : GoodC (d :: M) (a :: Lp) := by
  rcases Lp with _ | ⟨c, L''⟩
  · simp [wtC] at hpos
  · have ha2 : a % 4 ≠ 2 := by omega
    have ha0 : a % 4 ≠ 0 := by omega
    unfold GoodC at h ⊢
    simp only [rvec, ite_eq_right ha2, ite_eq_right ha0]
    have hlenM : (rvec M).length ≤ (rvec (c :: L'')).length := length_le_of_colexLt h
    rcases M with _ | ⟨m, M'⟩
    · refine colexLt_of_length_lt ?_
      have hge := length_rvec_ge_two (c :: L'')
      rw [length_rvec_singleton]
      simp only [List.length_cons]
      omega
    · simp only [rvec]
      split_ifs with hd2 hd0
      · refine colexLt_of_length_lt ?_
        simp only [List.length_cons]
        omega
      · refine colexLt_of_length_lt ?_
        rw [length_bumpHead_rvec]
        simp only [List.length_cons]
        omega
      · exact Or.inl (Or.inl h)

private theorem strongLt_of_goodC_odd {a : ℕ} {M Lp : List ℕ} (hodd : a % 2 = 1)
    (hpos : wtC Lp > 0) (h : GoodC M Lp) : StrongLt M (a :: Lp) :=
  fun _ hNM d => goodC_cons_of_goodC_odd hodd hpos (goodC_of_goodB_of_goodC hNM h) d

private theorem goodC_add4_cons_of_goodC {a : ℕ} {M Lp : List ℕ} (hpos : wtC Lp > 0)
    (h : GoodC M Lp) : GoodC ((a + 4) :: M) (a :: Lp) := by
  by_cases hodd : a % 2 = 1
  · exact goodC_cons_of_goodC_odd hodd hpos h (a + 4)
  · have h4 : a % 4 = 2 ∨ a % 4 = 0 := by omega
    rcases h4 with h2 | h0
    · unfold GoodC at h ⊢
      rw [rvec_add4_cons, rvec_mod4_eq_2 M h2, rvec_mod4_eq_2 Lp h2]
      exact h
    · unfold GoodC at h ⊢
      rw [rvec_add4_cons, rvec_mod4_eq_0 M h0, rvec_mod4_eq_0 Lp h0]
      obtain ⟨x, y, xs, hM⟩ := rvec_exists_cons M
      obtain ⟨u, v, ys, hL⟩ := rvec_exists_cons Lp
      rw [hM, hL] at h ⊢
      exact (colexLt_bumpHead_bumpHead_iff x u (y :: xs) (v :: ys)).mpr h

private theorem rvec_eq_of_wtC_zero_elen_eq (a : ℕ) {M Lp : List ℕ} (hM0 : wtC M = 0)
    (hL0 : wtC Lp = 0) (hE : elen M = elen Lp) : rvec ((a + 4) :: M) = rvec (a :: Lp) := by
  rw [rvec_add4_cons]
  rcases M with _ | ⟨m, M'⟩ <;> rcases Lp with _ | ⟨c, L''⟩
  · rfl
  · simp only [elen] at hE
    omega
  · simp only [elen] at hE
    omega
  · have hm : rvec (m :: M') = [0, 0] := rvec_eq_zero_of_wtC_zero hM0
    have hc : rvec (c :: L'') = [0, 0] := rvec_eq_zero_of_wtC_zero hL0
    simp only [rvec, hm, hc, hE]

private theorem goodC_bump3_one (L' : List ℕ) : GoodC (bump3 L') (1 :: L') := by
  unfold GoodC
  rcases L' with _ | ⟨b, _ | ⟨c, L3⟩⟩
  · exact Or.inl (Or.inr ⟨rfl, by decide⟩)
  · refine colexLt_of_length_lt ?_
    simp only [bump3, bump2, bumpHead]
    rw [length_rvec_singleton]
    have hge := length_rvec_ge_two [b]
    rw [rvec]
    simp only [show ¬(1 % 4 = 2) by decide, show ¬(1 % 4 = 0) by decide, ite_false,
      List.length_cons]
    omega
  · change ColexLt (rvec ((b + 1 + 1 + 1) :: c :: L3)) (rvec (1 :: b :: c :: L3))
    simp only [rvec, show ¬(1 % 4 = 2) by decide,
      show ¬(1 % 4 = 0) by decide, ite_false]
    have h4 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by omega
    rcases h4 with hb0 | hb1 | hb2 | hb3
    · have hb32 : ¬((b + 1 + 1 + 1) % 4 = 2) := by omega
      have hb30 : ¬((b + 1 + 1 + 1) % 4 = 0) := by omega
      have hb2 : ¬(b % 4 = 2) := by omega
      simp only [ite_eq_right hb32, ite_eq_right hb30, ite_eq_right hb2, ite_eq_left hb0]
      obtain ⟨x, y, xs, h⟩ := rvec_exists_cons (c :: L3)
      rw [h]
      exact Or.inl (Or.inl (colexLt_self_bumpHead x (y :: xs)))
    · have hb32 : ¬((b + 1 + 1 + 1) % 4 = 2) := by omega
      have hb30 : (b + 1 + 1 + 1) % 4 = 0 := by omega
      have hb2 : ¬(b % 4 = 2) := by omega
      have hb0 : ¬(b % 4 = 0) := by omega
      simp only [ite_eq_right hb32, ite_eq_left hb30, ite_eq_right hb2, ite_eq_right hb0]
      refine colexLt_of_length_lt ?_
      rw [length_bumpHead_rvec]
      simp only [List.length_cons]
      omega
    · have hb32 : ¬((b + 1 + 1 + 1) % 4 = 2) := by omega
      have hb30 : ¬((b + 1 + 1 + 1) % 4 = 0) := by omega
      simp only [ite_eq_right hb32, ite_eq_right hb30, ite_eq_left hb2]
      exact Or.inl (Or.inr ⟨rfl, by simp only [elen]; omega⟩)
    · have hb32 : (b + 1 + 1 + 1) % 4 = 2 := by omega
      have hb2 : ¬(b % 4 = 2) := by omega
      have hb0 : ¬(b % 4 = 0) := by omega
      simp only [ite_eq_left hb32, ite_eq_right hb2, ite_eq_right hb0]
      refine colexLt_of_length_lt ?_
      simp only [List.length_cons]
      omega

private theorem goodC_bump3_three (b : ℕ) (L'' : List ℕ) :
    GoodC (bump3 (b :: L'')) (3 :: b :: L'') := by
  have h1 := goodC_bump3_one (b :: L'')
  unfold GoodC at h1 ⊢
  have hr : rvec (3 :: b :: L'') = rvec (1 :: b :: L'') := rfl
  rw [hr]
  exact h1

private def GoodBA (M L : List ℕ) : Prop :=
  GoodC M L ∨ (rvec M = rvec L ∧ elen M ≤ elen L)

private def GoodBF (M L : List ℕ) : Prop :=
  GoodC M L ∨ (rvec M = rvec L ∧ elen M ≤ elen L + 1)

private theorem goodC_imp_goodBA {M L : List ℕ} (h : GoodC M L) : GoodBA M L := Or.inl h

private theorem goodC_imp_goodBF {M L : List ℕ} (h : GoodC M L) : GoodBF M L := Or.inl h

private theorem goodBA_imp_goodB {M L : List ℕ} (h : GoodBA M L) : GoodB M L := by
  rcases h with hC | ⟨hrv, _⟩
  · exact Or.inl hC
  · exact Or.inr hrv

private theorem goodBF_imp_goodB {M L : List ℕ} (h : GoodBF M L) : GoodB M L := by
  rcases h with hC | ⟨hrv, _⟩
  · exact Or.inl hC
  · exact Or.inr hrv

private theorem goodBA_two_of_goodBF {M Lp : List ℕ} (h : GoodBF M Lp) : GoodBA M (2 :: Lp) := by
  rcases h with hC | ⟨hrv, hE⟩
  · left
    unfold GoodC at hC ⊢
    rw [rvec_mod4_eq_2 Lp rfl]
    exact hC
  · right
    rw [rvec_mod4_eq_2 Lp rfl, elen_two_cons]
    exact ⟨hrv, by omega⟩

private theorem goodBA_two_add4 {a : ℕ} {M Lp : List ℕ} (h : GoodBA M (a :: Lp)) :
    GoodBA (2 :: M) ((a + 4) :: Lp) := by
  rcases h with hC | ⟨hrv, hE⟩
  · left
    unfold GoodC at hC ⊢
    rw [rvec_mod4_eq_2 M rfl, rvec_add4_cons]
    exact hC
  · right
    rw [rvec_mod4_eq_2 M rfl, rvec_add4_cons, elen_two_cons, elen_add4_cons]
    exact ⟨hrv, by omega⟩

private theorem goodBF_add4_cons_of_goodBA {a : ℕ} {M Lp : List ℕ} (hpos : wtC Lp > 0)
    (h : GoodBA M Lp) : GoodBF ((a + 4) :: M) (a :: Lp) := by
  rcases h with hC | ⟨hrv, hE⟩
  · exact Or.inl (goodC_add4_cons_of_goodC hpos hC)
  · have hE4 : elen ((a + 4) :: M) ≤ elen (a :: Lp) + 1 := by
      simp only [elen]
      omega
    by_cases hodd : a % 2 = 1
    · rcases Lp with _ | ⟨c, L''⟩
      · simp [wtC] at hpos
      · rcases M with _ | ⟨m, M'⟩
        · left
          unfold GoodC
          have ha2 : a % 4 ≠ 2 := by omega
          have ha0 : a % 4 ≠ 0 := by omega
          have hge := length_rvec_ge_two (c :: L'')
          refine colexLt_of_length_lt ?_
          simp only [rvec, ite_eq_right ha2, ite_eq_right ha0]
          split_ifs <;> simp <;> omega
        · rcases Nat.lt_or_eq_of_le hE with hlt | heq
          · left
            unfold GoodC
            rw [rvec_add4_cons]
            have ha2 : a % 4 ≠ 2 := by omega
            have ha0 : a % 4 ≠ 0 := by omega
            simp only [rvec, ite_eq_right ha2, ite_eq_right ha0]
            exact Or.inl (Or.inr ⟨hrv, hlt⟩)
          · right
            refine ⟨?_, hE4⟩
            rw [rvec_add4_cons]
            have ha2 : a % 4 ≠ 2 := by omega
            have ha0 : a % 4 ≠ 0 := by omega
            simp only [rvec, ite_eq_right ha2, ite_eq_right ha0, hrv, heq]
    · have h4 : a % 4 = 2 ∨ a % 4 = 0 := by omega
      right
      refine ⟨?_, hE4⟩
      rcases h4 with h2 | h0
      · rw [rvec_add4_cons, rvec_mod4_eq_2 M h2, rvec_mod4_eq_2 Lp h2, hrv]
      · rw [rvec_add4_cons, rvec_mod4_eq_0 M h0, rvec_mod4_eq_0 Lp h0, hrv]

/-! ## Inner Transducer Positive-Weight Evaluation -/

private def OutAllStrong (c0 : Cfg (Fin 2) (Fin 6)) (L : List ℕ) (W : ListBlank (Fin 2)) : Prop :=
  HaltsPlus c0 ∨
  (∃ b M, (c0 [target]⊢⁺ RetB (b :: M) W) ∧ StrongLt M L) ∨
  (∃ M, (c0 [target]⊢⁺ RetC M W) ∧ StrongLt M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetD (d :: M) W) ∧ StrongLt M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetE (d :: M) W) ∧ StrongLt M L) ∨
  (∃ M, (c0 [target]⊢⁺ RetA M W) ∧ StrongLt M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetE0 (d :: M) W) ∧ StrongLt M L)

private def OutStrong (c0 : Cfg (Fin 2) (Fin 6)) (L : List ℕ) (W : ListBlank (Fin 2)) : Prop :=
  HaltsPlus c0 ∨
  (∃ b M, (c0 [target]⊢⁺ RetB (b :: M) W) ∧ StrongLt M L) ∨
  (∃ M, (c0 [target]⊢⁺ RetC M W) ∧ GoodC M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetD (d :: M) W) ∧ StrongLt M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetE (d :: M) W) ∧ StrongLt M L) ∨
  (∃ M, (c0 [target]⊢⁺ RetA M W) ∧ StrongLt M L) ∨
  (∃ d M, (c0 [target]⊢⁺ RetE0 (d :: M) W) ∧ StrongLt M L)

private def OutA (L : List ℕ) (W : ListBlank (Fin 2)) : Prop :=
  OutStrong (FwdA L W) L W ∨
  (∃ M, ((FwdA L W) [target]⊢⁺ RetB (0 :: M) W) ∧ GoodBA M L)

private def OutTok10 (L : List ℕ) (W : ListBlank (Fin 2)) : Prop :=
  OutStrong (FwdF L (tok10 W)) L W ∨
  (∃ M, ((FwdF L (tok10 W)) [target]⊢⁺ RetB (0 :: M) W) ∧ GoodC M L) ∨
  (∃ M, ((FwdF L (tok10 W)) [target]⊢⁺ RetC M W) ∧ GoodBF M L)

private theorem outAllStrong_imp_outStrong {c0 : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h : OutAllStrong c0 L W) : OutStrong c0 L W := by
  rcases h with hH | hB | ⟨M, hs, hC⟩ | hD | hE | hA | hE0
  · exact Or.inl hH
  · exact Or.inr (Or.inl hB)
  · exact Or.inr (Or.inr (Or.inl ⟨M, hs, goodC_of_strongLt hC⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hD)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hE))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hA)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hE0)))))

private theorem outAllStrong_stepPlus {c0 c1 : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h01 : c0 [target]⊢⁺ c1) (h1 : OutAllStrong c1 L W) :
    OutAllStrong c0 L W := by
  rcases h1 with hH | ⟨b, M, hs, hB⟩ | ⟨M, hs, hC⟩ | ⟨d, M, hs, hD⟩ |
    ⟨d, M, hs, hE⟩ | ⟨M, hs, hA⟩ | ⟨d, M, hs, hE0⟩
  · exact Or.inl (HaltsPlus.stepPlus h01 hH)
  · exact Or.inr (Or.inl ⟨b, M, h01.trans hs, hB⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨M, h01.trans hs, hC⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, h01.trans hs, hD⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, h01.trans hs, hE⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨M, h01.trans hs, hA⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, M, h01.trans hs, hE0⟩)))))

private theorem outStrong_stepPlus {c0 c1 : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)} (h01 : c0 [target]⊢⁺ c1) (h1 : OutStrong c1 L W) :
    OutStrong c0 L W := by
  rcases h1 with hH | ⟨b, M, hs, hB⟩ | ⟨M, hs, hC⟩ | ⟨d, M, hs, hD⟩ |
    ⟨d, M, hs, hE⟩ | ⟨M, hs, hA⟩ | ⟨d, M, hs, hE0⟩
  · exact Or.inl (HaltsPlus.stepPlus h01 hH)
  · exact Or.inr (Or.inl ⟨b, M, h01.trans hs, hB⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨M, h01.trans hs, hC⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, h01.trans hs, hD⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, h01.trans hs, hE⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨M, h01.trans hs, hA⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, M, h01.trans hs, hE0⟩)))))

private theorem outStrong_mono {c0 : Cfg (Fin 2) (Fin 6)} {L1 L2 : List ℕ} {W : ListBlank (Fin 2)}
    (h1 : OutStrong c0 L1 W) (h12 : GoodB L1 L2) : OutStrong c0 L2 W := by
  rcases h1 with hH | ⟨b, M, hs, hB⟩ | ⟨M, hs, hC⟩ | ⟨d, M, hs, hD⟩ |
    ⟨d, M, hs, hE⟩ | ⟨M, hs, hA⟩ | ⟨d, M, hs, hE0⟩
  · exact Or.inl hH
  · exact Or.inr (Or.inl ⟨b, M, hs, strongLt_of_strongLt_of_goodB hB h12⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨M, hs, goodC_of_goodC_of_goodB hC h12⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, hs, strongLt_of_strongLt_of_goodB hD h12⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨d, M, hs, strongLt_of_strongLt_of_goodB hE h12⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨M, hs, strongLt_of_strongLt_of_goodB hA h12⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨d, M, hs, strongLt_of_strongLt_of_goodB hE0 h12⟩)))))

private theorem outAllStrong_of_outStrong_strongLt {c0 : Cfg (Fin 2) (Fin 6)} {M L : List ℕ}
    {W : ListBlank (Fin 2)} (hSL : StrongLt M L) (hOut : OutStrong c0 M W) :
    OutAllStrong c0 L W := by
  have hBML : GoodB M L := goodB_of_strongLt hSL
  rcases hOut with hH | ⟨b, M1, hs, hB⟩ | ⟨M1, hs, hC⟩ | ⟨d, M1, hs, hD⟩ |
    ⟨d, M1, hs, hE⟩ | ⟨M1, hs, hA⟩ | ⟨d, M1, hs, hE0⟩
  · exact Or.inl hH
  · exact Or.inr (Or.inl ⟨b, M1, hs, strongLt_of_strongLt_of_goodB hB hBML⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨M1, hs, strongLt_of_goodB_of_strongLt (goodC_imp_goodB hC) hSL⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1, hs, strongLt_of_strongLt_of_goodB hD hBML⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨d, M1, hs, strongLt_of_strongLt_of_goodB hE hBML⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨M1, hs, strongLt_of_strongLt_of_goodB hA hBML⟩)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨d, M1, hs, strongLt_of_strongLt_of_goodB hE0 hBML⟩)))))

private theorem outAllStrong_of_outA_strongLt {M L : List ℕ} {W : ListBlank (Fin 2)}
    (hSL : StrongLt M L) (hOut : OutA M W) : OutAllStrong (FwdA M W) L W := by
  rcases hOut with hS | ⟨M1, hs, hBA⟩
  · exact outAllStrong_of_outStrong_strongLt hSL hS
  · exact Or.inr (Or.inl ⟨0, M1, hs, strongLt_of_goodB_of_strongLt (goodBA_imp_goodB hBA) hSL⟩)

private theorem outAllStrong_of_outTok10_strongLt {M L : List ℕ} {W : ListBlank (Fin 2)}
    (hSL : StrongLt M L) (hOut : OutTok10 M W) : OutAllStrong (FwdF M (tok10 W)) L W := by
  rcases hOut with hS | ⟨M1, hs, hCM1⟩ | ⟨M1, hs, hBF⟩
  · exact outAllStrong_of_outStrong_strongLt hSL hS
  · exact Or.inr (Or.inl ⟨0, M1, hs, strongLt_of_goodB_of_strongLt (goodC_imp_goodB hCM1) hSL⟩)
  · exact Or.inr (Or.inr (Or.inl
      ⟨M1, hs, strongLt_of_goodB_of_strongLt (goodBF_imp_goodB hBF) hSL⟩))

private theorem drain_tok1_allStrong {L : List ℕ}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (n : ℕ) :
    (∀ {c0 : Cfg (Fin 2) (Fin 6)} {M : List ℕ} {W : ListBlank (Fin 2)},
      StrongLt M L → (c0 [target]⊢⁺ RetA M ((tok1^[n]) W)) → OutAllStrong c0 L W) ∧
    (∀ {c0 : Cfg (Fin 2) (Fin 6)} {W : ListBlank (Fin 2)},
      OutAllStrong c0 L ((tok1^[n]) W) → OutAllStrong c0 L W) := by
  induction n using Nat.strongRecOn with
  | ind n ihn =>
    have hRetA : ∀ {c0 : Cfg (Fin 2) (Fin 6)} {M : List ℕ} {W : ListBlank (Fin 2)},
        StrongLt M L → (c0 [target]⊢⁺ RetA M ((tok1^[n]) W)) → OutAllStrong c0 L W := by
      intro c0 M W hSL hstep
      rcases n with _ | n'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨M, hstep, hSL⟩)))))
      · rw [Function.iterate_succ_apply'] at hstep
        have s_to_F := hstep.trans (step_RetA_tok1 M ((tok1^[n']) W))
        by_cases hM0 : wtC M = 0
        · obtain ⟨b, M1, sF, hM1_0, _⟩ := (eval_zero M hM0).2 (tok10 ((tok1^[n']) W))
          have sC := step_RetB_tok10 (b :: M1) ((tok1^[n']) W)
          have s_all := s_to_F.trans (sF.trans sC)
          have hSL1 : StrongLt ((b + 2) :: M1) L :=
            strongLt_of_goodB_of_strongLt (goodB_of_wtC_zero hM1_0 M) hSL
          exact (ihn n' (by omega)).2
            (Or.inr (Or.inr (Or.inl ⟨(b + 2) :: M1, s_all, hSL1⟩)))
        · have hOut := outAllStrong_stepPlus s_to_F
            (outAllStrong_of_outTok10_strongLt hSL
              ((ih_sub M (goodC_of_strongLt hSL) (Nat.pos_of_ne_zero hM0)).2 ((tok1^[n']) W)))
          exact (ihn n' (by omega)).2 hOut
    refine ⟨hRetA, ?_⟩
    intro c0 W hOut
    rcases hOut with hH | ⟨b, M1, hs, hB⟩ | ⟨M1, hs, hC⟩ | ⟨d, M1, hs, hD⟩ |
      ⟨d, M1, hs, hE⟩ | ⟨M1, hs, hA⟩ | ⟨d, M1, hs, hE0⟩
    · exact Or.inl hH
    · exact Or.inr (Or.inl ⟨b + n, M1,
        hs.trans_star (stepStar_RetB_tok1 n b M1 W), hB⟩)
    · rcases n with _ | n'
      · exact Or.inr (Or.inr (Or.inl ⟨M1, hs, hC⟩))
      · rw [Function.iterate_succ_apply'] at hs
        exact (ihn n' (by omega)).1 hC (hs.trans (step_RetC_tok1 M1 ((tok1^[n']) W)))
    · rcases n with _ | _ | n'
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1, hs, hD⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨d, M1, hs.trans (step_RetD_tok1 (d :: M1) W), hD⟩)))))
      · exact Or.inl (haltsPlus_RetD_tok1_add2 n' hs)
    · rcases n with _ | n'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1, hs, hE⟩))))
      · exact Or.inl (haltsPlus_RetE_tok1_succ n' hs)
    · exact hRetA hA hs
    · rcases n with _ | n'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, M1, hs, hE0⟩)))))
      · exact Or.inl (haltsPlus_RetE0_tok1_succ n' hs)

private theorem drain_FwdA_allStrong {c0 : Cfg (Fin 2) (Fin 6)} {M L : List ℕ}
    {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (n : ℕ) (hSL : StrongLt M L) (hstep : c0 [target]⊢⁺ FwdA M ((tok1^[n]) W)) :
    OutAllStrong c0 L W := by
  by_cases hM0 : wtC M = 0
  · obtain ⟨M1, sA, hM1_0, _⟩ := (eval_zero M hM0).1 ((tok1^[n]) W)
    have hSL1 : StrongLt M1 L := strongLt_of_goodB_of_strongLt (goodB_of_wtC_zero hM1_0 M) hSL
    exact (drain_tok1_allStrong ih_sub n).2
      (Or.inr (Or.inl ⟨0, M1, hstep.trans sA, hSL1⟩))
  · have hOut := outAllStrong_stepPlus hstep
      (outAllStrong_of_outA_strongLt hSL
        ((ih_sub M (goodC_of_strongLt hSL) (Nat.pos_of_ne_zero hM0)).1 ((tok1^[n]) W)))
    exact (drain_tok1_allStrong ih_sub n).2 hOut

private theorem peel_tok0_strong {c0 : Cfg (Fin 2) (Fin 6)} {M L : List ℕ}
    {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (hSL : StrongLt M L) (hstep : c0 [target]⊢⁺ FwdF M (tok10 (tok0 W))) :
    OutStrong c0 L W := by
  by_cases hM0 : wtC M = 0
  · obtain ⟨b, M1, sF, hM1_0, _⟩ := (eval_zero M hM0).2 (tok10 (tok0 W))
    have sC0 := step_RetB_tok10 (b :: M1) (tok0 W)
    have sD0 := step_RetC_tok0 ((b + 2) :: M1) W
    have s_all := hstep.trans (sF.trans (sC0.trans sD0))
    have hBM1 : GoodB M1 M :=
      goodB_trans (goodB_tail_cons (b + 2) M1) (goodB_of_wtC_zero hM1_0 M)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨b + 3, M1, s_all,
      strongLt_of_goodB_of_strongLt hBM1 hSL⟩)))
  · rcases (ih_sub M (goodC_of_strongLt hSL) (Nat.pos_of_ne_zero hM0)).2 (tok0 W) with
      (hH | ⟨b, M1, sF, hB⟩ | ⟨M1, sF, hC⟩ | ⟨d, M1, sF, hD⟩ |
        ⟨d, M1, sF, hE⟩ | ⟨M1, sF, hA⟩ | ⟨d, M1, sF, hE0⟩) |
      ⟨M1, sF, hCM1⟩ | ⟨M1, sF, hBF⟩
    · exact Or.inl (HaltsPlus.stepPlus hstep hH)
    · have hSL1 : StrongLt M1 L := strongLt_of_strongLt_of_goodB hB (goodB_of_strongLt hSL)
      exact Or.inr (Or.inr (Or.inl ⟨(b + 1) :: M1,
        hstep.trans (sF.trans (step_RetB_tok0 (b :: M1) W)),
        strongLt_apply hSL1 (b + 1)⟩))
    · have hSL1 : StrongLt M1 L := strongLt_of_goodB_of_strongLt (goodC_imp_goodB hC) hSL
      rcases M1 with _ | ⟨d, M2⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, [],
          hstep.trans (sF.trans (step_RetC_tok0 [] W)), hSL1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d + 1, M2,
          hstep.trans (sF.trans (step_RetC_tok0 (d :: M2) W)),
          strongLt_of_goodB_of_strongLt (goodB_tail_cons d M2) hSL1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1,
        hstep.trans (sF.trans (step_RetD_tok0 (d :: M1) W)),
        strongLt_of_strongLt_of_goodB hD (goodB_of_strongLt hSL)⟩))))
    · exact outAllStrong_imp_outStrong
        (drain_FwdA_allStrong ih_sub 2 (strongLt_cons_of_strongLt_of_strongLt d hE hSL)
          (hstep.trans (sF.trans (step_RetE_tok0 (d :: M1) W))))
    · exact Or.inr (Or.inl ⟨0, M1,
        hstep.trans (sF.trans (step_RetA_tok0 M1 W)),
        strongLt_of_strongLt_of_goodB hA (goodB_of_strongLt hSL)⟩)
    · exact outAllStrong_imp_outStrong
        (drain_FwdA_allStrong ih_sub (d + 4)
          (strongLt_of_strongLt_of_goodB hE0 (goodB_of_strongLt hSL))
          (hstep.trans (sF.trans (stepPlus_RetE0_tok0 d M1 W))))
    · have hSL1 : StrongLt M1 L := strongLt_of_goodB_of_strongLt (goodC_imp_goodB hCM1) hSL
      exact Or.inr (Or.inr (Or.inl ⟨1 :: M1,
        hstep.trans (sF.trans (step_RetB_tok0 (0 :: M1) W)),
        strongLt_apply hSL1 1⟩))
    · have hSL1 : StrongLt M1 L := strongLt_of_goodB_of_strongLt (goodBF_imp_goodB hBF) hSL
      rcases M1 with _ | ⟨d, M2⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨0, [],
          hstep.trans (sF.trans (step_RetC_tok0 [] W)), hSL1⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨d + 1, M2,
          hstep.trans (sF.trans (step_RetC_tok0 (d :: M2) W)),
          strongLt_of_goodB_of_strongLt (goodB_tail_cons d M2) hSL1⟩)))

private theorem peel_tok10_outStrong {c0 : Cfg (Fin 2) (Fin 6)} {L : List ℕ}
    {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (hOut : OutStrong c0 L (tok10 W)) :
    OutStrong c0 L W ∨ (∃ M1, (c0 [target]⊢⁺ RetB (0 :: M1) W) ∧ GoodC M1 L) := by
  rcases hOut with hH | ⟨b, M1, hs, hB⟩ | ⟨M1, hs, hC⟩ | ⟨d, M1, hs, hD⟩ |
    ⟨d, M1, hs, hE⟩ | ⟨M1, hs, hA⟩ | ⟨d, M1, hs, hE0⟩
  · exact Or.inl (Or.inl hH)
  · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨(b + 2) :: M1,
      hs.trans (step_RetB_tok10 (b :: M1) W), strongLt_apply hB (b + 2)⟩)))
  · exact Or.inr ⟨M1, hs.trans (step_RetC_tok10 M1 W), hC⟩
  · exact Or.inl (outAllStrong_imp_outStrong
      (drain_FwdA_allStrong ih_sub (d + 4) hD (hs.trans (stepPlus_RetD_tok10 d M1 W))))
  · exact Or.inl (Or.inl (haltsPlus_RetE_tok10 hs))
  · exact Or.inl (peel_tok0_strong ih_sub hA
      (hs.trans (step_RetA_tok1 M1 (tok0 W))))
  · exact Or.inl (Or.inl (haltsPlus_RetE0_tok10 hs))

private theorem outTok10_of_outStrong_tok10 {L : List ℕ} {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (hOut : OutStrong (FwdF L (tok10 W)) L (tok10 W)) : OutTok10 L W := by
  rcases peel_tok10_outStrong ih_sub hOut with hS | hB0
  · exact Or.inl hS
  · exact Or.inr (Or.inl hB0)

private theorem outTok10_of_outAllStrong_tok1_tok10 {L : List ℕ} {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (n : ℕ) (hOut : OutAllStrong (FwdF L (tok10 W)) L ((tok1^[n]) (tok10 W))) : OutTok10 L W :=
  outTok10_of_outStrong_tok10 ih_sub
    (outAllStrong_imp_outStrong ((drain_tok1_allStrong ih_sub n).2 hOut))

private theorem outA_of_outStrong_tok10 {L : List ℕ} {W : ListBlank (Fin 2)}
    (ih_sub : ∀ M : List ℕ, GoodC M L → wtC M > 0 → (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W))
    (hOut : OutStrong (FwdA L W) L (tok10 W)) : OutA L W := by
  rcases peel_tok10_outStrong ih_sub hOut with hS | ⟨M1, hs, hCM1⟩
  · exact Or.inl hS
  · exact Or.inr ⟨M1, hs, goodC_imp_goodBA hCM1⟩

private theorem eval_AF (L : List ℕ) (hpos : wtC L > 0) :
    (∀ W, OutA L W) ∧ (∀ W, OutTok10 L W) := by
  have hmain : ∀ v, Acc ColexLt v → ∀ L : List ℕ, rvec L = v → wtC L > 0 →
      (∀ W, OutA L W) ∧ (∀ W, OutTok10 L W) := by
    intro v hv
    induction hv with
    | intro v _ ih_acc =>
      intro L hrv hpos
      induction L with
      | nil => simp [wtC] at hpos
      | cons a Lp ih_L =>
        have ih_sub : ∀ M : List ℕ, GoodC M (a :: Lp) → wtC M > 0 →
            (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W) := by
          intro M hGM hMpos
          exact ih_acc (rvec M) (hrv ▸ hGM) M rfl hMpos
        have ih_Lp : wtC Lp > 0 → (∀ W, OutA Lp W) ∧ (∀ W, OutTok10 Lp W) := by
          intro hLp_pos
          rcases goodB_tail_cons a Lp with hlt | heq
          · exact ih_sub Lp hlt hLp_pos
          · exact ih_L (hrv ▸ heq) hLp_pos
        have hF : ∀ W, OutTok10 (a :: Lp) W := by
          intro W
          have s_in := stepPlus_FwdF_cons a Lp (tok10 W)
          by_cases hLp0 : wtC Lp = 0
          · obtain ⟨M, sA, hM0, hE⟩ := (eval_zero Lp hLp0).1 ((tok1^[a + 2]) (tok10 W))
            have sB := stepStar_RetB_zero_tok1 (a + 2) M (tok10 W)
            have sC := step_RetB_tok10 ((a + 2) :: M) W
            have s_all : (FwdF (a :: Lp) (tok10 W)) [target]⊢⁺ RetC ((a + 4) :: M) W :=
              ((s_in.trans sA).trans_star sB).trans sC
            refine Or.inr (Or.inr ⟨(a + 4) :: M, s_all, ?_⟩)
            right
            refine ⟨rvec_eq_of_wtC_zero_elen_eq a hM0 hLp0 hE, ?_⟩
            simp only [elen, hE]
            omega
          · have hLp_pos : wtC Lp > 0 := Nat.pos_of_ne_zero hLp0
            have hGLp : GoodB Lp (a :: Lp) := goodB_tail_cons a Lp
            have hdrain : ∀ n : ℕ, ∀ M : List ℕ, n % 2 = (a + 2) % 2 → GoodC M Lp →
                ((FwdF (a :: Lp) (tok10 W)) [target]⊢⁺ RetC M ((tok1^[n]) (tok10 W))) →
                OutTok10 (a :: Lp) W := by
              intro n
              induction n using Nat.strongRecOn with
              | ind n ihn =>
                intro M hpar hGM hstepC
                rcases n with _ | _ | n'
                · exact Or.inr (Or.inl ⟨M, hstepC.trans (step_RetC_tok10 M W),
                    goodC_of_goodC_of_goodB hGM hGLp⟩)
                · have hodd : a % 2 = 1 := by omega
                  have hSL : StrongLt M (a :: Lp) := strongLt_of_goodC_odd hodd hLp_pos hGM
                  exact outTok10_of_outAllStrong_tok1_tok10 ih_sub 1
                    (Or.inr (Or.inr (Or.inl ⟨M, hstepC, hSL⟩)))
                · have htok :
                      (tok1^[n' + 2]) (tok10 W) = tok1 (tok1 ((tok1^[n']) (tok10 W))) := by
                    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
                  rw [htok] at hstepC
                  have s1 : (RetC M (tok1 (tok1 ((tok1^[n']) (tok10 W))))) [target]⊢⁺
                      FwdF M (tok10 ((tok1^[n']) (tok10 W))) :=
                    (step_RetC_tok1 M (tok1 ((tok1^[n']) (tok10 W)))).trans
                      (step_RetA_tok1 M ((tok1^[n']) (tok10 W)))
                  have s_to_F := hstepC.trans s1
                  by_cases hM0 : wtC M = 0
                  · obtain ⟨b, M1, sF, hM1_0, _⟩ :=
                      (eval_zero M hM0).2 (tok10 ((tok1^[n']) (tok10 W)))
                    have sC := step_RetB_tok10 (b :: M1) ((tok1^[n']) (tok10 W))
                    have s_next := s_to_F.trans (sF.trans sC)
                    have hGM1 : GoodC ((b + 2) :: M1) Lp :=
                      goodC_of_goodB_of_goodC (goodB_of_wtC_zero hM1_0 M) hGM
                    exact ihn n' (by omega) ((b + 2) :: M1) (by omega) hGM1 s_next
                  · have hMpos : wtC M > 0 := Nat.pos_of_ne_zero hM0
                    have hGMa : GoodC M (a :: Lp) := goodC_of_goodC_of_goodB hGM hGLp
                    rcases (ih_sub M hGMa hMpos).2 ((tok1^[n']) (tok10 W)) with
                      (hH | ⟨b, M1, sF, hB1⟩ | ⟨M1, sF, hC1⟩ | ⟨d, M1, sF, hD1⟩ |
                        ⟨d, M1, sF, hE1⟩ | ⟨M1, sF, hA1⟩ | ⟨d, M1, sF, hE01⟩) |
                      ⟨M1, sF, hCM1⟩ | ⟨M1, sF, hBF1⟩
                    · exact Or.inl (Or.inl (HaltsPlus.stepPlus s_to_F hH))
                    · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub n'
                        (Or.inr (Or.inl ⟨b, M1, s_to_F.trans sF,
                          strongLt_of_strongLt_of_goodB hB1 (goodC_imp_goodB hGMa)⟩))
                    · exact ihn n' (by omega) M1 (by omega) (colexLt_trans hC1 hGM)
                        (s_to_F.trans sF)
                    · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub n'
                        (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1, s_to_F.trans sF,
                          strongLt_of_strongLt_of_goodB hD1 (goodC_imp_goodB hGMa)⟩))))
                    · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub n'
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M1, s_to_F.trans sF,
                          strongLt_of_strongLt_of_goodB hE1 (goodC_imp_goodB hGMa)⟩)))))
                    · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub n'
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                          ⟨M1, s_to_F.trans sF,
                            strongLt_of_strongLt_of_goodB hA1 (goodC_imp_goodB hGMa)⟩))))))
                    · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub n'
                        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                          ⟨d, M1, s_to_F.trans sF,
                            strongLt_of_strongLt_of_goodB hE01 (goodC_imp_goodB hGMa)⟩))))))
                    · have sB := stepStar_RetB_tok1 n' 0 M1 (tok10 W)
                      have sC := step_RetB_tok10 ((0 + n') :: M1) W
                      have s_all := ((s_to_F.trans sF).trans_star sB).trans sC
                      refine Or.inr (Or.inr ⟨(0 + n' + 2) :: M1, s_all, ?_⟩)
                      by_cases hodd : a % 2 = 1
                      · have hSL :=
                          strongLt_of_goodC_odd hodd hLp_pos (colexLt_trans hCM1 hGM)
                        exact goodC_imp_goodBF (strongLt_apply hSL (0 + n' + 2))
                      · have heven : (0 + n' + 2) % 2 = 0 := by omega
                        have hBM1 : GoodB ((0 + n' + 2) :: M1) M :=
                          goodB_cons_of_goodC_even heven hCM1
                        exact goodC_imp_goodBF (goodC_of_goodB_of_goodC hBM1 hGMa)
                    · exact ihn n' (by omega) M1 (by omega)
                        (goodC_of_goodB_of_goodC (goodBF_imp_goodB hBF1) hGM)
                        (s_to_F.trans sF)
            rcases (ih_Lp hLp_pos).1 ((tok1^[a + 2]) (tok10 W)) with
              (hH | ⟨b, M, sA, hB⟩ | ⟨M, sA, hGM⟩ | ⟨d, M, sA, hD⟩ |
                ⟨d, M, sA, hE⟩ | ⟨M, sA, hA1⟩ | ⟨d, M, sA, hE0⟩) | ⟨M, sA, hBA⟩
            · exact Or.inl (Or.inl (HaltsPlus.stepPlus s_in hH))
            · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub (a + 2)
                (Or.inr (Or.inl ⟨b, M, s_in.trans sA,
                  strongLt_of_strongLt_of_goodB hB hGLp⟩))
            · exact hdrain (a + 2) M rfl hGM (s_in.trans sA)
            · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub (a + 2)
                (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, s_in.trans sA,
                  strongLt_of_strongLt_of_goodB hD hGLp⟩))))
            · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub (a + 2)
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d, M, s_in.trans sA,
                  strongLt_of_strongLt_of_goodB hE hGLp⟩)))))
            · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub (a + 2)
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨M, s_in.trans sA,
                  strongLt_of_strongLt_of_goodB hA1 hGLp⟩))))))
            · exact outTok10_of_outAllStrong_tok1_tok10 ih_sub (a + 2)
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d, M, s_in.trans sA,
                  strongLt_of_strongLt_of_goodB hE0 hGLp⟩))))))
            · have sB := stepStar_RetB_zero_tok1 (a + 2) M (tok10 W)
              have sC := step_RetB_tok10 ((a + 2) :: M) W
              have s_all := ((s_in.trans sA).trans_star sB).trans sC
              exact Or.inr (Or.inr ⟨(a + 4) :: M, s_all,
                goodBF_add4_cons_of_goodBA hLp_pos hBA⟩)
        have hA : ∀ a' : ℕ, rvec (a' :: Lp) = rvec (a :: Lp) → wtC (a' :: Lp) > 0 →
            ∀ W, OutA (a' :: Lp) W := by
          intro a'
          induction a' using Nat.strongRecOn with
          | ind a' iha =>
            intro hrva' hpos' W
            have ih_sub_a' : ∀ M : List ℕ, GoodC M (a' :: Lp) → wtC M > 0 →
                (∀ W, OutA M W) ∧ (∀ W, OutTok10 M W) := by
              intro M hGM hMpos
              have hGMa : GoodC M (a :: Lp) := by
                unfold GoodC at hGM ⊢
                rwa [← hrva']
              exact ih_sub M hGMa hMpos
            rcases a' with _ | _ | _ | _ | a''
            · have s0 := step_FwdA_0 Lp W
              have hB0 : GoodB Lp (0 :: Lp) := goodB_tail_cons 0 Lp
              by_cases hLp0 : wtC Lp = 0
              · obtain ⟨b, M, sF, hM0, _⟩ := (eval_zero Lp hLp0).2 (tok10 W)
                have sC := step_RetB_tok10 (b :: M) W
                have hC0 : GoodC ((b + 2) :: M) (0 :: Lp) :=
                  (goodC_iff_goodB_of_mod4_eq_0 ((b + 2) :: M) Lp rfl).mpr
                    (goodB_of_wtC_zero hM0 Lp)
                exact Or.inl (Or.inr (Or.inr (Or.inl ⟨(b + 2) :: M,
                  s0.trans (sF.trans sC), hC0⟩)))
              · rcases (ih_Lp (Nat.pos_of_ne_zero hLp0)).2 W with
                  hS | ⟨M, sF, hCM⟩ | ⟨M, sF, hBF⟩
                · exact Or.inl (outStrong_mono (outStrong_stepPlus s0 hS) hB0)
                · exact Or.inr ⟨M, s0.trans sF,
                    goodC_imp_goodBA (goodC_of_goodC_of_goodB hCM hB0)⟩
                · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨M, s0.trans sF,
                    (goodC_iff_goodB_of_mod4_eq_0 M Lp rfl).mpr (goodBF_imp_goodB hBF)⟩)))
            · exact Or.inl (Or.inr (Or.inr (Or.inl ⟨bump3 Lp,
                step_FwdA_1_retC Lp W, goodC_bump3_one Lp⟩)))
            · have s2 := step_FwdA_2 Lp W
              have hB2 : GoodB Lp (2 :: Lp) := goodB_tail_cons 2 Lp
              by_cases hLp0 : wtC Lp = 0
              · exact absurd hLp0 (by
                  rw [wtC_two_cons] at hpos'
                  exact Nat.ne_of_gt hpos')
              · rcases (ih_Lp (Nat.pos_of_ne_zero hLp0)).2 (tok10 W) with
                  hS | ⟨M, sF, hCM⟩ | ⟨M, sF, hBF⟩
                · exact outA_of_outStrong_tok10 ih_sub_a'
                    (outStrong_mono (outStrong_stepPlus s2 hS) hB2)
                · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨2 :: M,
                    s2.trans (sF.trans (step_RetB_tok10 (0 :: M) W)), ?_⟩)))
                  unfold GoodC at hCM ⊢
                  rw [rvec_mod4_eq_2 M rfl, rvec_mod4_eq_2 Lp rfl]
                  exact hCM
                · exact Or.inr ⟨M,
                    s2.trans (sF.trans (step_RetC_tok10 M W)),
                    goodBA_two_of_goodBF hBF⟩
            · rcases Lp with _ | ⟨c, L''⟩
              · simp [wtC] at hpos'
              · exact Or.inr ⟨bump3 (c :: L''), step_FwdA_3_retB (c :: L'') W,
                  goodC_imp_goodBA (goodC_bump3_three c L'')⟩
            · have hrva'' : rvec (a'' :: Lp) = rvec (a :: Lp) := by
                rw [← rvec_add4_cons a'' Lp, hrva']
              have hpos'' : wtC (a'' :: Lp) > 0 := by
                rw [← wtC_add4_cons a'' Lp]
                exact hpos'
              have s4 := step_FwdA_add4 a'' Lp W
              have hBa'' : GoodB (a'' :: Lp) ((a'' + 4) :: Lp) := by
                unfold GoodB
                rw [rvec_add4_cons]
                exact Or.inr rfl
              rcases iha a'' (by omega) hrva'' hpos'' (tok10 (tok10 W)) with
                hS | ⟨M, sA, hBA⟩
              · rcases peel_tok10_outStrong ih_sub_a'
                  (outStrong_mono (outStrong_stepPlus s4 hS) hBa'') with
                  hS1 | ⟨M1, hs1, hCM1⟩
                · exact outA_of_outStrong_tok10 ih_sub_a' hS1
                · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨2 :: M1,
                    hs1.trans (step_RetB_tok10 (0 :: M1) W), ?_⟩)))
                  unfold GoodC at hCM1 ⊢
                  rw [rvec_mod4_eq_2 M1 rfl]
                  exact hCM1
              · exact Or.inr ⟨2 :: M,
                  s4.trans (sA.trans (step_RetB_tok10_2 M W)),
                  goodBA_two_add4 hBA⟩
        exact ⟨hA a rfl hpos, hF⟩
  exact hmain (rvec L) (acc_ColexLt (rvec L)) L rfl hpos

/-! ## Outer `CR` Mode Closure and Stack Reduction Assembly -/

private theorem step_RetD_encStack_nil (L : List ℕ) :
    (RetD L (encStack [])) [target]⊢⁺ cfg_FL1 (bumpHead L) [0] := by
  unfold RetD cfg_FL1
  execute 2

private theorem step_RetE_encStack_nil (L : List ℕ) :
    (RetE L (encStack [])) [target]⊢⁺ cfg_FL1 (bumpHead L) [0] := by
  unfold RetE cfg_FL1
  execute 1

private theorem stepPlus_RetD_encStack_zero (d : ℕ) (M R'' : List ℕ) :
    (RetD (d :: M) (encStack (0 :: R''))) [target]⊢⁺ cfg_AL1 M ((bumpHead^[d + 4]) R'') := by
  have h1 : encStack (0 :: R'') = tok10 (encStack R'') := rfl
  rw [h1]
  have s1 := stepPlus_RetD_tok10 d M (encStack R'')
  rw [tok1_iter_encStack (d + 4) R''] at s1
  exact s1

private theorem step_RetE_tok0_encStack (L R' : List ℕ) :
    (RetE L (tok0 (encStack R'))) [target]⊢⁺ cfg_AL1 L (bump2 R') := by
  have s1 := step_RetE_tok0 L (encStack R')
  have h1 : tok1 (tok1 (encStack R')) = encStack (bump2 R') := by
    simp [tok1, bump2, encStack_bumpHead]
  rw [h1] at s1
  exact s1

private theorem stepPlus_RetE0_tok0_encStack (d : ℕ) (M R' : List ℕ) :
    (RetE0 (d :: M) (tok0 (encStack R'))) [target]⊢⁺ cfg_AL1 M ((bumpHead^[d + 4]) R') := by
  have s1 := stepPlus_RetE0_tok0 d M (encStack R')
  rw [tok1_iter_encStack (d + 4) R'] at s1
  exact s1

private theorem close_RetD_encStack (d : ℕ) (M R' : List ℕ) {c0 : Cfg (Fin 2) (Fin 6)}
    (hs : c0 [target]⊢⁺ RetD (d :: M) (encStack R')) :
    ∃ cfg, (c0 [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases R' with _ | ⟨c, R''⟩
  · exact ⟨cfg_FL1 ((d + 1) :: M) [0],
      hs.trans (step_RetD_encStack_nil (d :: M)), Or.inl (in_FL1 _ _)⟩
  · rcases c with _ | c'
    · exact ⟨cfg_AL1 M ((bumpHead^[d + 4]) R''),
        hs.trans (stepPlus_RetD_encStack_zero d M R''), Or.inl (in_AL1 _ _)⟩
    · have h1 : encStack ((c' + 1) :: R'') = tok1 (tok1 (encStack (c' :: R'')).tail) := by
        rw [encStack_succ, tok1, tok1, cons_one_encStack_tail]
      rw [h1] at hs
      rcases haltsPlus_RetD_tok1_tok1 hs with ⟨cfg, hstep, hnone⟩
      exact ⟨cfg, hstep, Or.inr hnone⟩

private theorem close_RetE_encStack (d : ℕ) (M R' : List ℕ) {c0 : Cfg (Fin 2) (Fin 6)}
    (hs : c0 [target]⊢⁺ RetE (d :: M) (encStack R')) :
    ∃ cfg, (c0 [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases R' with _ | ⟨c, R''⟩
  · exact ⟨cfg_FL1 ((d + 1) :: M) [0],
      hs.trans (step_RetE_encStack_nil (d :: M)), Or.inl (in_FL1 _ _)⟩
  · have h1 : encStack (c :: R'') = tok1 (encStack (c :: R'')).tail := by
      rw [tok1, cons_one_encStack_tail]
    rw [h1] at hs
    rcases haltsPlus_RetE_tok1 hs with ⟨cfg, hstep, hnone⟩
    exact ⟨cfg, hstep, Or.inr hnone⟩

private theorem close_CR1 (L R : List ℕ) :
    ∃ cfg, ((cfg_CR1 L R) [target]⊢⁺ cfg) ∧
      (IsInStackSystem cfg ∨ (step target cfg).isNone) := by
  rcases R with _ | ⟨b, R'⟩
  · exact ⟨cfg_FL1 (bump2 L) [0], step_CR1_nil L, Or.inl (in_FL1 _ _)⟩
  · rcases b with _ | _ | b'
    · exact ⟨cfg_BR1 (0 :: L) R', step_CR1_0 L R', Or.inl (in_BR1 _ _)⟩
    · have s_in : (cfg_CR1 L (1 :: R')) [target]⊢⁺ FwdF L (tok10 (tok0 (encStack R'))) :=
        step_CR1_1_entry L R'
      by_cases hL0 : wtC L = 0
      · obtain ⟨b, M1, sF, _⟩ := (eval_zero L hL0).2 (tok10 (tok0 (encStack R')))
        have sC0 := step_RetB_tok10 (b :: M1) (tok0 (encStack R'))
        have sD0 := step_RetC_tok0 ((b + 2) :: M1) (encStack R')
        exact close_RetD_encStack (b + 3) M1 R'
          (s_in.trans (sF.trans (sC0.trans sD0)))
      · rcases (eval_AF L (Nat.pos_of_ne_zero hL0)).2 (tok0 (encStack R')) with
          (hH | ⟨b, M1, sF, _⟩ | ⟨M1, sF, _⟩ | ⟨d, M1, sF, _⟩ |
            ⟨d, M1, sF, _⟩ | ⟨M1, sF, _⟩ | ⟨d, M1, sF, _⟩) |
          ⟨M1, sF, _⟩ | ⟨M1, sF, _⟩
        · rcases HaltsPlus.stepPlus s_in hH with ⟨cfg, hs, hnone⟩
          exact ⟨cfg, hs, Or.inr hnone⟩
        · exact ⟨cfg_CR1 ((b + 1) :: M1) R',
            s_in.trans (sF.trans (step_RetB_tok0 (b :: M1) (encStack R'))),
            Or.inl (in_CR1 _ _)⟩
        · rcases M1 with _ | ⟨d, M2⟩
          · exact close_RetD_encStack 0 [] R'
              (s_in.trans (sF.trans (step_RetC_tok0 [] (encStack R'))))
          · exact close_RetD_encStack (d + 1) M2 R'
              (s_in.trans (sF.trans (step_RetC_tok0 (d :: M2) (encStack R'))))
        · exact close_RetE_encStack d M1 R'
            (s_in.trans (sF.trans (step_RetD_tok0 (d :: M1) (encStack R'))))
        · exact ⟨cfg_AL1 (d :: M1) (bump2 R'),
            s_in.trans (sF.trans (step_RetE_tok0_encStack (d :: M1) R')),
            Or.inl (in_AL1 _ _)⟩
        · exact ⟨cfg_BR1 (0 :: M1) R',
            s_in.trans (sF.trans (step_RetA_tok0 M1 (encStack R'))),
            Or.inl (in_BR1 _ _)⟩
        · exact ⟨cfg_AL1 M1 ((bumpHead^[d + 4]) R'),
            s_in.trans (sF.trans (stepPlus_RetE0_tok0_encStack d M1 R')),
            Or.inl (in_AL1 _ _)⟩
        · exact ⟨cfg_CR1 (1 :: M1) R',
            s_in.trans (sF.trans (step_RetB_tok0 (0 :: M1) (encStack R'))),
            Or.inl (in_CR1 _ _)⟩
        · rcases M1 with _ | ⟨d, M2⟩
          · exact close_RetD_encStack 0 [] R'
              (s_in.trans (sF.trans (step_RetC_tok0 [] (encStack R'))))
          · exact close_RetD_encStack (d + 1) M2 R'
              (s_in.trans (sF.trans (step_RetC_tok0 (d :: M2) (encStack R'))))
    · exact ⟨cfg_AL1 (0 :: L) (b' :: R'), step_CR1_ge2 L b' R', Or.inl (in_AL1 _ _)⟩

private theorem init_to_FL1 :
    (init [] : Cfg (Fin 2) (Fin 6)) [target]⊢⁺ cfg_FL1 [] [0] := by
  unfold cfg_FL1
  execute 1

private theorem encStack_not_surjective_witness :
    ∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ M : List ℕ, encStack M ≠ t := by
  refine ⟨(1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default, rfl, ?_⟩
  intro M h
  rcases M with _ | ⟨a, M'⟩
  · have h1 := congrArg (fun s => s.head) h
    simp [encStack_nil] at h1
  · rcases a with _ | a'
    · rcases M' with _ | ⟨a2, M''⟩
      · have h1 := congrArg (fun s => s.tail.tail.tail.head) h
        simp [encStack_zero, encStack_nil] at h1
      · have h1 := congrArg (fun s => s.tail.tail.head) h
        simp [encStack_zero, encStack_cons_head] at h1
    · have h1 := congrArg (fun s => s.tail.head) h
      simp [encStack_succ, encStack_cons_head] at h1

private theorem valid_stack_modes : IsValidStackModes encStack encStack evalStackCfg := by
  intro m
  cases m with
  | BR => exact ⟨B, .id [], .id [], by decide, by decide, Or.inr (Or.inl fun _ _ => rfl)⟩
  | FL => exact ⟨F, .id [], .id [], by decide, by decide, Or.inr (Or.inr fun _ _ => rfl)⟩
  | AL => exact ⟨A, .id [], .id [], by decide, by decide, Or.inr (Or.inr fun _ _ => rfl)⟩
  | CR => exact ⟨C, .id [], .id [], by decide, by decide, Or.inr (Or.inl fun _ _ => rfl)⟩

private theorem block_encoding :
    ∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
      strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
      strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
      (∀ a L, encStack (a :: L) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encStack L))) ∧
      (∀ d R, encStack (d :: R) =
        ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
          (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encStack R))) :=
  ⟨1, 1, 1, 1, 1, 1, by decide, by decide, by decide, by decide, by decide, by decide,
    fun a L => by simp [encStack], fun d R => by simp [encStack]⟩

private theorem modes_bounded :
    ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes :=
  ⟨[.BR, .FL, .AL, .CR], by decide, fun m => by cases m <;> decide⟩

private theorem init_reaches_nontrivial :
    (init []) [target]⊢⁺ evalStackCfg .AL [0, 1] [3] :=
  init_to_FL1
    |>.trans (step_FL1_nil [0])
    |>.trans (step_FL1_0 [] [1])
    |>.trans (step_BR1_succ [0] 1 [])
    |>.trans (step_BR1_succ [1] 0 [])
    |>.trans (step_BR1_0 [2] [])
    |>.trans (step_CR1_nil [4])
    |>.trans (step_FL1_succ 5 [] [0])
    |>.trans (step_AL1_ge2 3 [] [1])

private theorem stack_system_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : IsInStackSystem cfg) :
    ∃ cfg', (cfg [target]⊢⁺ cfg') ∧
      (IsInStackSystem cfg' ∨ (step target cfg').isNone) := by
  rcases h with ⟨m, L, R, rfl⟩
  cases m with
  | BR => exact close_BR1 R L
  | FL => exact close_FL1 R L
  | AL => exact close_AL1 R L
  | CR => exact close_CR1 R L

/-- `target` reduces to a closed 4-mode 2nd-order digit-stack system. -/
theorem has_stack_reduction : HasStackReduction target :=
  HasStackReduction.of_oneDigit target StackMode encStack encStack evalStackCfg IsInStackSystem
    ⟨rfl, rfl, encStack_cons_head, encStack_cons_head,
      encStack_not_surjective_witness, encStack_not_surjective_witness,
      block_encoding, modes_bounded, valid_stack_modes,
      fun _ => Iff.rfl, fun m L R => ⟨m, L, R, rfl⟩,
      ⟨.AL, [0, 1], [3], init_reaches_nontrivial, by decide, ⟨3, by decide, by decide⟩⟩,
      Or.inl ⟨.CR, .BR, 0, id, (0 :: ·),
        fun _ => Nat.le_succ _, fun z L R => step_CR1_0 R (z :: L)⟩,
      stack_system_closed⟩

end BusyBeaver.M_1RBHHH_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD
