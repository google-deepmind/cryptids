/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Calculi.Counter
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.WordRunStack

variable {Γ : Type*} [Inhabited Γ]

theorem append_assoc_blank (u v : List Γ) (lb : ListBlank Γ) :
    (u ++ v) +> lb = u +> (v +> lb) := by
  induction u with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

theorem nth_cons_zero (x : Γ) (t : ListBlank Γ) : (x >> t).nth 0 = x := by
  rw [ListBlank.nth_zero, ListBlank.head_cons]

theorem nth_cons_succ (x : Γ) (t : ListBlank Γ) (i : ℕ) : (x >> t).nth (i + 1) = t.nth i := by
  rw [ListBlank.nth_succ, ListBlank.tail_cons]

theorem nth_cons_one (x : Γ) (t : ListBlank Γ) : (x >> t).nth 1 = t.nth 0 :=
  nth_cons_succ x t 0

theorem nth_cons_two (x : Γ) (t : ListBlank Γ) : (x >> t).nth 2 = t.nth 1 :=
  nth_cons_succ x t 1

theorem nth_cons_three (x : Γ) (t : ListBlank Γ) : (x >> t).nth 3 = t.nth 2 :=
  nth_cons_succ x t 2

theorem nth_cons_four (x : Γ) (t : ListBlank Γ) : (x >> t).nth 4 = t.nth 3 :=
  nth_cons_succ x t 3

theorem nth_default : ∀ i : ℕ, (default : ListBlank Γ).nth i = default
  | 0 => by
      rw [ListBlank.nth_zero]
      exact ListBlank.head_mk []
  | i + 1 => by
      rw [ListBlank.nth_succ]
      have htail : (default : ListBlank Γ).tail = default := ListBlank.tail_mk []
      rw [htail]
      exact nth_default i

/-- Extracts the first `n` symbols of a `ListBlank Γ`. -/
def takeBlank {Γ : Type*} [Inhabited Γ] : ℕ → ListBlank Γ → List Γ
  | 0, _ => []
  | n + 1, lb => lb.head :: takeBlank n lb.tail

theorem takeBlank_length : ∀ (n : ℕ) (lb : ListBlank Γ), (takeBlank n lb).length = n
  | 0, _ => rfl
  | n + 1, lb => by
      simp only [takeBlank, List.length_cons, takeBlank_length n lb.tail]

theorem nth_takeBlank_append_of_lt :
    ∀ (n : ℕ) (lb : ListBlank Γ) (v : List Γ) (t : ListBlank Γ) (i : ℕ), i < n →
      ((takeBlank n lb ++ v) +> t).nth i = lb.nth i
  | 0, _, _, _, _, h => nomatch h
  | n + 1, lb, v, t, 0, _ => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [nth_cons_zero, ListBlank.nth_zero]
  | n + 1, lb, v, t, i + 1, h => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [nth_cons_succ, ListBlank.nth_succ]
      exact nth_takeBlank_append_of_lt n lb.tail v t i (Nat.lt_of_succ_lt_succ h)

theorem nth_takeBlank_append_add :
    ∀ (n : ℕ) (lb : ListBlank Γ) (v : List Γ) (t : ListBlank Γ) (j : ℕ),
      ((takeBlank n lb ++ v) +> t).nth (n + j) = (v +> t).nth j
  | 0, _, _, _, _ => by simp only [takeBlank, List.nil_append, Nat.zero_add]
  | n + 1, lb, v, t, j => by
      simp only [takeBlank, List.cons_append, ListBlank.append]
      rw [Nat.succ_add, nth_cons_succ]
      exact nth_takeBlank_append_add n lb.tail v t j

theorem nth_append_of_lt :
    ∀ (v : List Γ) (t : ListBlank Γ) (j : ℕ), j < v.length → (v +> t).nth j = v.getD j default
  | [], _, _, h => nomatch h
  | x :: v, t, 0, _ => by
      simp only [ListBlank.append, List.getD_cons_zero]
      exact nth_cons_zero x (v +> t)
  | x :: v, t, j + 1, h => by
      simp only [ListBlank.append, List.getD_cons_succ]
      rw [nth_cons_succ]
      exact nth_append_of_lt v t j (Nat.lt_of_succ_lt_succ h)

def NoFactor (pat : List Γ) (t : ListBlank Γ) : Prop :=
  ∀ i : ℕ, ¬ ∀ j : ℕ, j < pat.length → t.nth (i + j) = pat.getD j default

theorem noFactor_default (pat : List Γ) (j : ℕ) (hj : j < pat.length)
    (hne : pat.getD j default ≠ default) : NoFactor pat (default : ListBlank Γ) := by
  intro i h
  exact hne ((h j hj).symm.trans (nth_default (i + j)))

theorem noFactor_cons_of_nth_ne (pat : List Γ) (x : Γ) (t : ListBlank Γ) (ht : NoFactor pat t)
    (j : ℕ) (hj : j < pat.length) (hne : (x >> t).nth j ≠ pat.getD j default) :
    NoFactor pat (x >> t) := by
  intro i h
  cases i with
  | zero => exact hne (by simpa using h j hj)
  | succ i =>
      apply ht i
      intro j' hj'
      have := h j' hj'
      rwa [Nat.succ_add, nth_cons_succ] at this

theorem isNowhereDenseFamily_of_noFactor {S : Type*} (Valid : S → Prop) (enc : S → ListBlank Γ)
    (pat : List Γ) (hforb : ∀ s, Valid s → NoFactor pat (enc s)) :
    IsNowhereDenseFamily Valid enc := by
  intro s hs n
  refine ⟨(takeBlank n (enc s) ++ pat) +> default, ?_, ?_⟩
  · intro i hi
    exact nth_takeBlank_append_of_lt n _ pat default i hi
  · intro s' hs' heq
    apply hforb s' hs' n
    intro j hj
    rw [heq, nth_takeBlank_append_add, nth_append_of_lt pat default j hj]

theorem isNowhereDenseHalf_of_noFactor {S : Type*} (Valid : S → Prop)
    (segs : S → List (SegRegionKind Γ)) (pat : List Γ)
    (hforb : ∀ s, Valid s → NoFactor pat (evalSegmentedHalf (segs s))) :
    IsNowhereDenseHalf Valid segs :=
  isNowhereDenseFamily_of_noFactor Valid (fun s => evalSegmentedHalf (segs s)) pat hforb

/-!
### Word-List Encoders & `SegModeSpec` Helpers (`PairStackSeg`)
-/

/-- Encodes a list of tokens `xs : List α` onto `tail : ListBlank Γ` via word map `w`. -/
def encWordsTail {Γ α : Type*} [Inhabited Γ] (w : α → List Γ) (tail : ListBlank Γ) :
    List α → ListBlank Γ
  | [] => tail
  | x :: xs => w x +> encWordsTail w tail xs

/-- Encodes a list of tokens `xs : List α` onto the blank half-tape `default`. -/
def encWords {Γ α : Type*} [Inhabited Γ] (w : α → List Γ) (xs : List α) : ListBlank Γ :=
  encWordsTail w default xs

@[simp] theorem encWordsTail_nil {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) (tail : ListBlank Γ) :
    encWordsTail w tail [] = tail :=
  rfl

@[simp] theorem encWordsTail_cons {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) (tail : ListBlank Γ) (x : α) (xs : List α) :
    encWordsTail w tail (x :: xs) = w x +> encWordsTail w tail xs :=
  rfl

@[simp] theorem encWords_nil {Γ α : Type*} [Inhabited Γ] (w : α → List Γ) :
    encWords w [] = default :=
  rfl

@[simp] theorem encWords_cons {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) (x : α) (xs : List α) :
    encWords w (x :: xs) = w x +> encWords w xs :=
  rfl

/-- Bridge from `evalSegRegion (.finWord (xs.map w)) +> tail` to `encWordsTail w tail xs`. -/
theorem evalSegRegion_finWord_map {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) :
    ∀ (xs : List α) (tail : ListBlank Γ),
      evalSegRegion (.finWord (xs.map w)) +> tail = encWordsTail w tail xs
  | [], tail => by simp [evalSegRegion, encWordsTail]
  | x :: xs, tail => by
      simp only [List.map_cons, evalSegRegion, encWordsTail]
      rw [append_assoc_blank, evalSegRegion_finWord_map w xs tail]

/-- Bridge from `evalSegmentedHalf [.finWord (xs.map w)]` to `encWords w xs`. -/
theorem evalSegmentedHalf_finWord_map {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) (xs : List α) :
    evalSegmentedHalf [.finWord (xs.map w)] = encWords w xs := by
  simp only [evalSegmentedHalf, encWords]
  exact evalSegRegion_finWord_map w xs default

/-- Bridge from `evalSegmentedHalf [.finWord (xs.map w), .gadget base]` to `encWordsTail`. -/
theorem evalSegmentedHalf_finWord_gadget {Γ α : Type*} [Inhabited Γ]
    (w : α → List Γ) (base : List Γ) (xs : List α) :
    evalSegmentedHalf [.finWord (xs.map w), .gadget base] =
      encWordsTail w (base +> default) xs := by
  simp only [evalSegmentedHalf, evalSegRegion]
  exact evalSegRegion_finWord_map w xs (base +> default)

/-- Non-empty `1`-run `1^(d+1)` defined by structural recursion. -/
def oWord : ℕ → List (Fin 2)
  | 0 => [1]
  | d + 1 => 1 :: oWord d

@[simp] theorem oWord_zero : oWord 0 = [1] := rfl
@[simp] theorem oWord_succ (d : ℕ) : oWord (d + 1) = 1 :: oWord d := rfl

/-- Zero-run word `0^k ++ [1]` defined by structural recursion. -/
def zWord : ℕ → List (Fin 2)
  | 0 => [1]
  | k + 1 => 0 :: zWord k

@[simp] theorem zWord_zero : zWord 0 = [1] := rfl
@[simp] theorem zWord_succ (k : ℕ) : zWord (k + 1) = 0 :: zWord k := rfl

/-- Head orientation for a segmented mode descriptor. -/
inductive SegHeadDir
  | left
  | right
  | mid
  deriving DecidableEq

/-- Table entry describing the TM state, head orientation, and left/right `HalfTapeView`s
    for a segmented mode `m : Mode`. -/
structure SegModeSpec (Γ Λ : Type*) where
  q : Λ
  dir : SegHeadDir
  vL : HalfTapeView Γ := .id []
  vR : HalfTapeView Γ := .id []

/-- Evaluates a `SegModeSpec` on encoded left and right half-tapes `l, r : ListBlank Γ`. -/
@[reducible] def evalSegModeSpec {Γ Λ : Type*} [Inhabited Γ] [OfNat Γ 0]
    (spec : SegModeSpec Γ Λ) (l r : ListBlank Γ) : Cfg Γ Λ :=
  match spec.dir with
  | .left => (applyView spec.vL l) <{{spec.q}} (applyView spec.vR r)
  | .right => (applyView spec.vL l) {{spec.q}}> (applyView spec.vR r)
  | .mid => ⟨some spec.q, ⟨(0 : Γ), applyView spec.vL l, applyView spec.vR r⟩⟩

/-- `SegStepOut M ValidSeg evalCfg c`: from `c`, machine `M` advances in `⊢⁺` either to
    `evalCfg s'` for some valid `s'` (`ValidSeg s'`), or to a halting configuration. -/
def SegStepOut {Γ Λ SegState : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (ValidSeg : SegState → Prop) (evalCfg : SegState → Cfg Γ Λ)
    (c : Cfg Γ Λ) : Prop :=
  ∃ cfg', (c [M]⊢⁺ cfg') ∧
    ((∃ s', ValidSeg s' ∧ cfg' = evalCfg s') ∨ (BusyBeaver.step M cfg').isNone)

/-- Close `SegStepOut` by stepping in `⊢⁺` to `evalCfg s'` for a valid state `s'`. -/
theorem SegStepOut.step {Γ Λ SegState : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {ValidSeg : SegState → Prop} {evalCfg : SegState → Cfg Γ Λ}
    {c : Cfg Γ Λ} {s' : SegState} (hs' : ValidSeg s') (h : c [M]⊢⁺ evalCfg s') :
    SegStepOut M ValidSeg evalCfg c :=
  ⟨evalCfg s', h, Or.inl ⟨s', hs', rfl⟩⟩

/-- Close `SegStepOut` by stepping in `⊢⁺` to a halting configuration `cfg_h`. -/
theorem SegStepOut.halt {Γ Λ SegState : Type*} [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} {ValidSeg : SegState → Prop} {evalCfg : SegState → Cfg Γ Λ}
    {c cfg_h : Cfg Γ Λ} (h : c [M]⊢⁺ cfg_h) (hhalt : (BusyBeaver.step M cfg_h).isNone) :
    SegStepOut M ValidSeg evalCfg c :=
  ⟨cfg_h, h, Or.inr hhalt⟩

/-- Evaluates a pair-stack state `(m, L, R) : Mode × α × β` via `modeSpec` and encoders. -/
@[reducible] def evalPairCfg {Γ Λ Mode α β : Type*} [Inhabited Γ] [OfNat Γ 0]
    (modeSpec : Mode → SegModeSpec Γ Λ)
    (encL : α → ListBlank Γ) (encR : β → ListBlank Γ)
    (s : Mode × α × β) : Cfg Γ Λ :=
  evalSegModeSpec (modeSpec s.1) (encL s.2.1) (encR s.2.2)

/-- Transport `IsNowhereDenseFamily` along a pointwise description of evaluated segments. -/
theorem isNowhereDenseHalf_of_family {S : Type*} {Valid : S → Prop}
    {segs : S → List (SegRegionKind Γ)} {enc : S → ListBlank Γ}
    (heq : ∀ s, evalSegmentedHalf (segs s) = enc s) (h : IsNowhereDenseFamily Valid enc) :
    IsNowhereDenseHalf Valid segs := by
  unfold IsNowhereDenseHalf
  rw [show (fun s => evalSegmentedHalf (segs s)) = enc from funext heq]
  exact h

/-- Decidable `n`-step window checker from `(ls +> l) {{q}}> (rs +> r)` to
    `(ls' +> l) {{q'}}> (rs' +> r)`. -/
def checkHeadRight {Γ Λ : Type*} [DecidableEq Γ] [DecidableEq Λ] [Inhabited Γ] [Inhabited Λ]
    (bL bR : Bool) (M : Machine Γ Λ) (n : ℕ)
    (q : Λ) (ls rs : List Γ) (q' : Λ) (ls' rs' : List Γ) : Bool :=
  match rs with
  | [] =>
      if !bR then false
      else
        match rs' with
        | a' :: rs₀' =>
            Counter.multiStepWindow bL true M n ⟨q, default, ls, []⟩ ==
              some ⟨q', a', ls', rs₀'⟩
        | [] =>
            Counter.multiStepWindow bL true M n ⟨q, default, ls, []⟩ ==
              some ⟨q', default, ls', []⟩
  | a :: rs₀ =>
      match rs' with
      | a' :: rs₀' =>
          Counter.multiStepWindow bL bR M n ⟨q, a, ls, rs₀⟩ == some ⟨q', a', ls', rs₀'⟩
      | [] =>
          if bR then
            Counter.multiStepWindow bL true M n ⟨q, a, ls, rs₀⟩ ==
              some ⟨q', default, ls', []⟩
          else
            match n with
            | 0 => false
            | m + 1 =>
                match Counter.multiStepWindow bL false M m ⟨q, a, ls, rs₀⟩ with
                | some ⟨q₀, x, ls₀, []⟩ =>
                    match M q₀ x with
                    | some (some q₁, Stmt.write w Dir.right) =>
                        (q₁ == q') && (Counter.pushWindow bL w ls₀ == ls')
                    | _ => false
                | _ => false

private theorem evalWindow_eq_headRight_cons {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (l r : ListBlank Γ) (q : Λ) (a : Γ) (ls rs₀ : List Γ) :
    Counter.evalWindow l r ⟨q, a, ls, rs₀⟩ = (ls +> l) {{q}}> ((a :: rs₀) +> r) := by
  simp [Counter.evalWindow]

private theorem evalWindow_eq_headRight_nil {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (l : ListBlank Γ) (q : Λ) (ls : List Γ) :
    Counter.evalWindow l default ⟨q, default, ls, []⟩ = (ls +> l) {{q}}> ([] +> default) := by
  have hd : (default : ListBlank Γ).head = default := rfl
  have tl : (default : ListBlank Γ).tail = default := rfl
  simp [Counter.evalWindow, hd, tl]

/-- Soundness of `checkHeadRight`. -/
theorem checkHeadRight_sound {Γ Λ : Type*} [DecidableEq Γ] [DecidableEq Λ]
    [Inhabited Γ] [Inhabited Λ]
    {bL bR : Bool} {M : Machine Γ Λ}
    (n : ℕ) (q : Λ) (ls rs : List Γ) (q' : Λ) (ls' rs' : List Γ)
    (l r : ListBlank Γ)
    (hL : bL = true → l = default) (hR : bR = true → r = default)
    (h : checkHeadRight bL bR M n q ls rs q' ls' rs' = true) :
    ((ls +> l) {{q}}> (rs +> r)) [M]⊢^{n} ((ls' +> l) {{q'}}> (rs' +> r)) := by
  unfold checkHeadRight at h
  cases rs with
  | nil =>
      cases hbR : bR with
      | false => simp [hbR] at h
      | true =>
          simp only [hbR, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          have hr_def := hR hbR
          subst hr_def
          cases rs' with
          | cons a' rs₀' =>
              have hms := eq_of_beq h
              have hsnd := Counter.multiStepWindow_sound l default hL (fun _ => rfl) n _ _ hms
              rwa [evalWindow_eq_headRight_nil, evalWindow_eq_headRight_cons] at hsnd
          | nil =>
              have hms := eq_of_beq h
              have hsnd := Counter.multiStepWindow_sound l default hL (fun _ => rfl) n _ _ hms
              rwa [evalWindow_eq_headRight_nil, evalWindow_eq_headRight_nil] at hsnd
  | cons a rs₀ =>
      cases rs' with
      | cons a' rs₀' =>
          have hms := eq_of_beq h
          have hsnd := Counter.multiStepWindow_sound l r hL hR n _ _ hms
          rwa [evalWindow_eq_headRight_cons, evalWindow_eq_headRight_cons] at hsnd
      | nil =>
          cases hbR : bR with
          | true =>
              simp only [hbR, ↓reduceIte] at h
              have hr_def := hR hbR
              subst hr_def
              have hms := eq_of_beq h
              have hsnd := Counter.multiStepWindow_sound l default hL (fun _ => rfl) n _ _ hms
              rwa [evalWindow_eq_headRight_cons, evalWindow_eq_headRight_nil] at hsnd
          | false =>
              simp only [hbR, Bool.false_eq_true, ↓reduceIte] at h
              cases n with
              | zero => nomatch h
              | succ m =>
                  dsimp only at h
                  split at h
                  · next val q₀ x ls₀ hms =>
                      split at h
                      · next htm q_opt stmt =>
                          simp only [Bool.and_eq_true, beq_iff_eq] at h
                          rcases h with ⟨rfl, hpush⟩
                          have hsnd := Counter.multiStepWindow_sound l r hL
                            (by intro hc; contradiction) m _ _ hms
                          rw [evalWindow_eq_headRight_cons,
                            evalWindow_eq_headRight_cons] at hsnd
                          have hstep1 : (((ls₀ +> l) {{q₀}}> ([x] +> r)) [M]⊢
                              ((ls' +> l) {{htm}}> ([] +> r))) := by
                            rw [← hpush, Counter.pushWindow_append q_opt ls₀ l hL]
                            simp [step, stmt, Turing.Tape.write, Turing.Tape.move]
                          exact Counter.multiStep_trans M _ _ _ m 1 hsnd hstep1
                      · nomatch h
                  · nomatch h

/-- Inductive rightward word-run transducer walk. -/
theorem walkWordRight {Γ Λ : Type*} [DecidableEq Γ] [DecidableEq Λ]
    [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} (s : ℕ) (q : Λ) (pL u pR v : List Γ)
    (hbody : checkHeadRight false false M s q pL (pR ++ v) q (pL ++ u) pR = true) :
    ∀ (k : ℕ) (l r : ListBlank Γ),
      ((pL +> l) {{q}}> (pR +> ((v ^ k) +> r))) [M]⊢^{s * k}
        ((pL +> ((u ^ k) +> l)) {{q}}> (pR +> r))
  | 0, l, r => by simp
  | k + 1, l, r => by
      rw [Counter.pow_succ_list, append_assoc_blank v (v ^ k) r,
        ← append_assoc_blank pR v ((v ^ k) +> r)]
      have h1 := @checkHeadRight_sound Γ Λ _ _ _ _ false false M s q pL (pR ++ v) q (pL ++ u) pR
        l ((v ^ k) +> r) (by intro hc; contradiction) (by intro hc; contradiction) hbody
      rw [append_assoc_blank pL u l] at h1
      have h2 := walkWordRight s q pL u pR v hbody k (u +> l) r
      rw [← append_assoc_blank (u ^ k) u l, ← Counter.pow_succ_right] at h2
      rw [show s * (k + 1) = s + s * k by ring]
      exact Counter.multiStep_trans M _ _ _ s (s * k) h1 h2

/-- Inductive leftward word-run transducer walk. -/
theorem walkWordLeft {Γ Λ : Type*} [DecidableEq Γ] [DecidableEq Λ]
    [Inhabited Γ] [Inhabited Λ]
    {M : Machine Γ Λ} (s : ℕ) (q : Λ) (pL u pR v : List Γ)
    (hbody : checkHeadRight false false M s q (pL ++ u) pR q pL (pR ++ v) = true) :
    ∀ (k : ℕ) (l r : ListBlank Γ),
      ((pL +> ((u ^ k) +> l)) {{q}}> (pR +> r)) [M]⊢^{s * k}
        ((pL +> l) {{q}}> (pR +> ((v ^ k) +> r)))
  | 0, l, r => by simp
  | k + 1, l, r => by
      rw [Counter.pow_succ_list, append_assoc_blank u (u ^ k) l,
        ← append_assoc_blank pL u ((u ^ k) +> l)]
      have h1 := @checkHeadRight_sound Γ Λ _ _ _ _ false false M s q (pL ++ u) pR q pL (pR ++ v)
        ((u ^ k) +> l) r (by intro hc; contradiction) (by intro hc; contradiction) hbody
      rw [append_assoc_blank pR v r] at h1
      have h2 := walkWordLeft s q pL u pR v hbody k l (v +> r)
      rw [← append_assoc_blank (v ^ k) v r, ← Counter.pow_succ_right] at h2
      rw [show s * (k + 1) = s + s * k by ring]
      exact Counter.multiStep_trans M _ _ _ s (s * k) h1 h2

end BusyBeaver.WordRunStack
