/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs
public import BusyBeaver.Basic

/-!
# Shared Windowed Symbolic Runner (`BusyBeaver.RunWin`)

Direct-import-only module (not re-exported by `BusyBeaver.Import`). Load with
`import BusyBeaver.RunWin` (or `public import BusyBeaver.RunWin` inside `module` files).

Provides kernel-reducible finite-window symbolic Turing machine execution `symRun` over
`SymCfg Γ Λ` (`SymCursor Γ`: `.mid l h r`, `.leftHead r`, `.rightHead l`) parameterized by
abstract left/right boundary `ListBlank Γ` tails `(Lt, Rt)`, together with soundness theorems
reducing multi-step `[M]⊢⁺` / `[M]⊢*` / `[M]⊢^{n}` reachability claims to a single `rfl` check
`symRun blankL blankR M s₁ n = some s₂`.
-/

@[expose] public section

namespace BusyBeaver.RunWin

open Turing BusyBeaver

/-- Symbolic tape cursor relative to abstract left/right boundary `ListBlank` tails `(Lt, Rt)`:
- `.mid l h r`: explicit head symbol `h`, left window `l` (closest-to-head first), right window `r`.
- `.leftHead r`: head is at `Lt.head` (left tail `Lt.tail`), revealed right window `r`.
- `.rightHead l`: head is at `Rt.head` (right tail `Rt.tail`), revealed left window `l`. -/
inductive SymCursor (Γ : Type*) where
  | mid (l : List Γ) (h : Γ) (r : List Γ)
  | leftHead (r : List Γ)
  | rightHead (l : List Γ)
deriving DecidableEq, Repr

/-- Symbolic configuration with control state `q` and windowed cursor `cur`. -/
structure SymCfg (Γ Λ : Type*) where
  q : Option Λ
  cur : SymCursor Γ
deriving DecidableEq, Repr

section

variable {Γ Λ : Type*} [Inhabited Γ] [DecidableEq Γ] [Inhabited Λ]

/-- Evaluate a `SymCursor` relative to abstract left/right boundary tapes `(Lt, Rt)`. -/
@[inline] def SymCursor.eval (Lt Rt : ListBlank Γ) : SymCursor Γ → Tape Γ
  | .mid l h r => ⟨h, l +> Lt, r +> Rt⟩
  | .leftHead r => ⟨Lt.head, Lt.tail, r +> Rt⟩
  | .rightHead l => ⟨Rt.head, l +> Lt, Rt.tail⟩

/-- Evaluate a `SymCfg` relative to abstract left/right boundary tapes `(Lt, Rt)`. -/
@[inline] def SymCfg.eval (Lt Rt : ListBlank Γ) (s : SymCfg Γ Λ) : Cfg Γ Λ :=
  ⟨s.q, s.cur.eval Lt Rt⟩

/-- Prepend `a` onto a finite window `xs`, trimming a single trailing `default` when `blank = true`
(representing `xs +> default`). -/
@[inline] def consSym (blank : Bool) (a : Γ) (xs : List Γ) : List Γ :=
  if blank then
    match xs with
    | [] => if a = default then [] else [a]
    | _ => a :: xs
  else
    a :: xs

theorem consSym_append (blank : Bool) (a : Γ) (xs : List Γ) (t : ListBlank Γ)
    (ht : blank = true → t = default) :
    (consSym blank a xs) +> t = a >> (xs +> t) := by
  cases blank with
  | false => rfl
  | true =>
    have hdef : t = default := ht rfl
    subst hdef
    cases xs with
    | nil =>
      dsimp only [consSym]
      by_cases ha : a = default
      · simp [ha, ListBlank.cons_default_default]
      · simp [ha]
    | cons _ _ => rfl

/-- Core single-step symbolic execution given control state `q` and cursor `.mid l h r`. -/
@[inline] def symStepMid (blankL blankR : Bool) (M : Machine Γ Λ) (q : Λ)
    (l : List Γ) (h : Γ) (r : List Γ) : Option (SymCfg Γ Λ) :=
  match M q h with
  | none => none
  | some (q', .write a .left) =>
    match l with
    | [] =>
      if blankL then
        some ⟨q', .mid [] default (consSym blankR a r)⟩
      else
        some ⟨q', .leftHead (consSym blankR a r)⟩
    | lh :: lt =>
      some ⟨q', .mid lt lh (consSym blankR a r)⟩
  | some (q', .write a .right) =>
    match r with
    | [] =>
      if blankR then
        some ⟨q', .mid (consSym blankL a l) default []⟩
      else
        some ⟨q', .rightHead (consSym blankL a l)⟩
    | rh :: rt =>
      some ⟨q', .mid (consSym blankL a l) rh rt⟩

/-- Single-step symbolic execution on `SymCfg`. Stepping past `.leftHead` (resp. `.rightHead`)
requires `blankL = true` (resp. `blankR = true`). -/
@[inline] def symStep (blankL blankR : Bool) (M : Machine Γ Λ) (s : SymCfg Γ Λ) :
    Option (SymCfg Γ Λ) :=
  match s.q with
  | none => none
  | some q =>
    match s.cur with
    | .mid l h r => symStepMid blankL blankR M q l h r
    | .leftHead r => if blankL then symStepMid true blankR M q [] default r else none
    | .rightHead l => if blankR then symStepMid blankL true M q l default [] else none

/-- Bounded `n`-step symbolic execution on `SymCfg`, returning `none` if `M` halts early or steps
across an abstract non-blank boundary tape. -/
def symRun (blankL blankR : Bool) (M : Machine Γ Λ) : SymCfg Γ Λ → ℕ → Option (SymCfg Γ Λ)
  | s, 0 => some s
  | s, n + 1 =>
    match symStep blankL blankR M s with
    | none => none
    | some s' => symRun blankL blankR M s' n

theorem symStepMid_sound (blankL blankR : Bool) (M : Machine Γ Λ)
    (Lt Rt : ListBlank Γ)
    (hL : blankL = true → Lt = default)
    (hR : blankR = true → Rt = default)
    (q : Λ) (l : List Γ) (h : Γ) (r : List Γ) (s' : SymCfg Γ Λ)
    (hs : symStepMid blankL blankR M q l h r = some s') :
    step M ⟨some q, ⟨h, l +> Lt, r +> Rt⟩⟩ = some (s'.eval Lt Rt) := by
  dsimp only [symStepMid] at hs
  rcases hm : M q h with _ | ⟨q', ⟨a, d⟩⟩
  · rw [hm] at hs; simp at hs
  · rw [hm] at hs
    cases d with
    | left =>
      dsimp only at hs
      cases l with
      | nil =>
        cases blankL with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
          subst hs
          simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_nil,
            SymCfg.eval, SymCursor.eval]
          rw [consSym_append blankR a r Rt hR]
        | true =>
          simp only [↓reduceIte, Option.some.injEq] at hs
          subst hs
          have hLt : Lt = default := hL rfl
          subst hLt
          simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_nil,
            ListBlank.head_default, ListBlank.tail_default, SymCfg.eval, SymCursor.eval]
          rw [consSym_append blankR a r Rt hR]
      | cons lh lt =>
        simp only [Option.some.injEq] at hs
        subst hs
        simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_cons,
          ListBlank.head_cons, ListBlank.tail_cons, SymCfg.eval, SymCursor.eval,
          consSym_append blankR a r Rt hR]
    | right =>
      dsimp only at hs
      cases r with
      | nil =>
        cases blankR with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hs
          subst hs
          simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_nil,
            SymCfg.eval, SymCursor.eval]
          rw [consSym_append blankL a l Lt hL]
        | true =>
          simp only [↓reduceIte, Option.some.injEq] at hs
          subst hs
          have hRt : Rt = default := hR rfl
          subst hRt
          simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_nil,
            ListBlank.head_default, ListBlank.tail_default, SymCfg.eval, SymCursor.eval]
          rw [consSym_append blankL a l Lt hL]
      | cons rh rt =>
        simp only [Option.some.injEq] at hs
        subst hs
        simp only [step, hm, Option.map_some, Tape.write, Tape.move, ListBlank.append_cons,
          ListBlank.head_cons, ListBlank.tail_cons, SymCfg.eval, SymCursor.eval,
          consSym_append blankL a l Lt hL]

theorem symStep_sound (blankL blankR : Bool) (M : Machine Γ Λ)
    (Lt Rt : ListBlank Γ)
    (hL : blankL = true → Lt = default)
    (hR : blankR = true → Rt = default)
    (s₁ s₂ : SymCfg Γ Λ)
    (hs : symStep blankL blankR M s₁ = some s₂) :
    step M (s₁.eval Lt Rt) = some (s₂.eval Lt Rt) := by
  rcases s₁ with ⟨qopt, cur⟩
  cases qopt with
  | none => simp [symStep] at hs
  | some q =>
    cases cur with
    | mid l h r =>
      exact symStepMid_sound blankL blankR M Lt Rt hL hR q l h r s₂ hs
    | leftHead r =>
      dsimp only [symStep] at hs
      cases blankL with
      | false => simp at hs
      | true =>
        have hLt : Lt = default := hL rfl
        subst hLt
        have hm := symStepMid_sound true blankR M default Rt hL hR q [] default r s₂ hs
        simpa only [SymCfg.eval, SymCursor.eval, ListBlank.head_default, ListBlank.tail_default,
          ListBlank.append_nil] using hm
    | rightHead l =>
      dsimp only [symStep] at hs
      cases blankR with
      | false => simp at hs
      | true =>
        have hRt : Rt = default := hR rfl
        subst hRt
        have hm := symStepMid_sound blankL true M Lt default hL hR q l default [] s₂ hs
        simpa only [SymCfg.eval, SymCursor.eval, ListBlank.head_default, ListBlank.tail_default,
          ListBlank.append_nil] using hm

theorem symRun_multiStep (blankL blankR : Bool) (M : Machine Γ Λ)
    (Lt Rt : ListBlank Γ)
    (hL : blankL = true → Lt = default)
    (hR : blankR = true → Rt = default)
    (n : ℕ) :
    ∀ s₁ s₂ : SymCfg Γ Λ,
      symRun blankL blankR M s₁ n = some s₂ →
      multiStep M (s₁.eval Lt Rt) n = some (s₂.eval Lt Rt) := by
  induction n with
  | zero =>
    intro s₁ s₂ h
    simp only [symRun, Option.some.injEq] at h
    subst h
    exact multiStep_zero M _
  | succ n ih =>
    intro s₁ s₂ h
    dsimp only [symRun] at h
    rcases hs : symStep blankL blankR M s₁ with _ | s'
    · rw [hs] at h; simp at h
    · rw [hs] at h
      rw [multiStep_of_step (symStep_sound blankL blankR M Lt Rt hL hR s₁ s' hs)]
      exact ih s' s₂ h

theorem symRun_star (blankL blankR : Bool) (M : Machine Γ Λ)
    (Lt Rt : ListBlank Γ)
    (hL : blankL = true → Lt = default)
    (hR : blankR = true → Rt = default)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun blankL blankR M s₁ n = some s₂) :
    (s₁.eval Lt Rt) [M]⊢* s₂.eval Lt Rt :=
  ⟨n, symRun_multiStep blankL blankR M Lt Rt hL hR n s₁ s₂ h⟩

theorem symRun_plus (blankL blankR : Bool) (M : Machine Γ Λ)
    (Lt Rt : ListBlank Γ)
    (hL : blankL = true → Lt = default)
    (hR : blankR = true → Rt = default)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun blankL blankR M s₁ (n + 1) = some s₂) :
    (s₁.eval Lt Rt) [M]⊢⁺ s₂.eval Lt Rt :=
  ⟨n + 1, Nat.zero_lt_succ n, symRun_multiStep blankL blankR M Lt Rt hL hR (n + 1) s₁ s₂ h⟩

/-! ## Convenience Specializations (Zero Boundary Obligations) -/

theorem symRun_open_star (Lt Rt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun false false M s₁ n = some s₂) :
    (s₁.eval Lt Rt) [M]⊢* s₂.eval Lt Rt :=
  symRun_star false false M Lt Rt (fun h => absurd h Bool.false_ne_true)
    (fun h => absurd h Bool.false_ne_true) s₁ s₂ n h

theorem symRun_blankL_star (Rt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun true false M s₁ n = some s₂) :
    (s₁.eval default Rt) [M]⊢* s₂.eval default Rt :=
  symRun_star true false M default Rt (fun _ => rfl)
    (fun h => absurd h Bool.false_ne_true) s₁ s₂ n h

theorem symRun_blankR_star (Lt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun false true M s₁ n = some s₂) :
    (s₁.eval Lt default) [M]⊢* s₂.eval Lt default :=
  symRun_star false true M Lt default (fun h => absurd h Bool.false_ne_true)
    (fun _ => rfl) s₁ s₂ n h

theorem symRun_blank_star (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun true true M s₁ n = some s₂) :
    (s₁.eval default default) [M]⊢* s₂.eval default default :=
  symRun_star true true M default default (fun _ => rfl) (fun _ => rfl) s₁ s₂ n h

theorem symRun_open_plus (Lt Rt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun false false M s₁ (n + 1) = some s₂) :
    (s₁.eval Lt Rt) [M]⊢⁺ s₂.eval Lt Rt :=
  symRun_plus false false M Lt Rt (fun h => absurd h Bool.false_ne_true)
    (fun h => absurd h Bool.false_ne_true) s₁ s₂ n h

theorem symRun_blankL_plus (Rt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun true false M s₁ (n + 1) = some s₂) :
    (s₁.eval default Rt) [M]⊢⁺ s₂.eval default Rt :=
  symRun_plus true false M default Rt (fun _ => rfl)
    (fun h => absurd h Bool.false_ne_true) s₁ s₂ n h

theorem symRun_blankR_plus (Lt : ListBlank Γ) (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun false true M s₁ (n + 1) = some s₂) :
    (s₁.eval Lt default) [M]⊢⁺ s₂.eval Lt default :=
  symRun_plus false true M Lt default (fun h => absurd h Bool.false_ne_true)
    (fun _ => rfl) s₁ s₂ n h

theorem symRun_blank_plus (M : Machine Γ Λ)
    (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h : symRun true true M s₁ (n + 1) = some s₂) :
    (s₁.eval default default) [M]⊢⁺ s₂.eval default default :=
  symRun_plus true true M default default (fun _ => rfl) (fun _ => rfl) s₁ s₂ n h

theorem symRun_open_star_of_eq (Lt Rt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval Lt Rt) (h₂ : s₂.eval Lt Rt = c₂)
    (h : symRun false false M s₁ n = some s₂) :
    c₁ [M]⊢* c₂ := by
  rw [h₁, ← h₂]
  exact symRun_open_star Lt Rt M s₁ s₂ n h

theorem symRun_blankL_star_of_eq (Rt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval default Rt) (h₂ : s₂.eval default Rt = c₂)
    (h : symRun true false M s₁ n = some s₂) :
    c₁ [M]⊢* c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blankL_star Rt M s₁ s₂ n h

theorem symRun_blankR_star_of_eq (Lt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval Lt default) (h₂ : s₂.eval Lt default = c₂)
    (h : symRun false true M s₁ n = some s₂) :
    c₁ [M]⊢* c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blankR_star Lt M s₁ s₂ n h

theorem symRun_blank_star_of_eq (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval default default) (h₂ : s₂.eval default default = c₂)
    (h : symRun true true M s₁ n = some s₂) :
    c₁ [M]⊢* c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blank_star M s₁ s₂ n h

theorem symRun_open_plus_of_eq (Lt Rt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval Lt Rt) (h₂ : s₂.eval Lt Rt = c₂)
    (h : symRun false false M s₁ (n + 1) = some s₂) :
    c₁ [M]⊢⁺ c₂ := by
  rw [h₁, ← h₂]
  exact symRun_open_plus Lt Rt M s₁ s₂ n h

theorem symRun_blankL_plus_of_eq (Rt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval default Rt) (h₂ : s₂.eval default Rt = c₂)
    (h : symRun true false M s₁ (n + 1) = some s₂) :
    c₁ [M]⊢⁺ c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blankL_plus Rt M s₁ s₂ n h

theorem symRun_blankR_plus_of_eq (Lt : ListBlank Γ) (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval Lt default) (h₂ : s₂.eval Lt default = c₂)
    (h : symRun false true M s₁ (n + 1) = some s₂) :
    c₁ [M]⊢⁺ c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blankR_plus Lt M s₁ s₂ n h

theorem symRun_blank_plus_of_eq (M : Machine Γ Λ)
    {c₁ c₂ : Cfg Γ Λ} (s₁ s₂ : SymCfg Γ Λ) (n : ℕ)
    (h₁ : c₁ = s₁.eval default default) (h₂ : s₂.eval default default = c₂)
    (h : symRun true true M s₁ (n + 1) = some s₂) :
    c₁ [M]⊢⁺ c₂ := by
  rw [h₁, ← h₂]
  exact symRun_blank_plus M s₁ s₂ n h

/-! ## Normalization Helpers for Goal Configurations -/

omit [DecidableEq Γ] in
theorem eval_init :
    (init ([] : List Γ) : Cfg Γ Λ) =
      (SymCfg.mk (some (default : Λ)) (.mid [] (default : Γ) [])).eval default default := by
  simp only [init, Turing.Tape.mk₁, Turing.Tape.mk₂, Turing.Tape.mk', ListBlank.mk_nil]
  rfl

omit [DecidableEq Γ] [Inhabited Λ] in
theorem eval_headRight_cons (q : Λ) (l : ListBlank Γ) (h : Γ) (r : ListBlank Γ) :
    (l {{q}}> (h >> r)) = ⟨some q, ⟨h, l, r⟩⟩ := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]

omit [DecidableEq Γ] [Inhabited Λ] in
theorem eval_headLeft_cons (q : Λ) (h : Γ) (l r : ListBlank Γ) :
    ((h >> l) <{{q}} r) = ⟨some q, ⟨h, l, r⟩⟩ := by
  simp only [ListBlank.head_cons, ListBlank.tail_cons]

end

end BusyBeaver.RunWin
