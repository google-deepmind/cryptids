/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic

/-!
# Spatial Word-Vocabulary Run-Length Simulation (`BusyBeaver.WordRLE`)

Reusable, machine-polymorphic infrastructure for kernel-verified Turing machine simulation over
run-length-encoded (RLE) stacks of finite spatial words:

- `withNat` — Call-by-value `ℕ` normalizer (`withNat n k = k n`) forcing intermediate arithmetic
  results to weak-head normal form in Lean's C++ kernel.
- `BTree` & `NatTrie` — Logarithmic-depth tree and radix-trie containers for compact certificates.
- `dirCfg` & `WordExit` — Translation-invariant directed configurations (`Cfg.headRight` /
  `Cfg.headLeft` over `ListBlank Γ`) and verified local word-exit transitions.
- `simWord` & `sweepWord_sound` — Certified single-word zipper execution and `k`-copy homogeneous
  sweeps (`ReachesIn M (dt * k) ...`).
- `simSubwords` — Certified composite-word exit computation from a verified base-word exit table.
- `EntryCfg` & `EntryReaches` — Concrete RLE stack simulator with pluggable macro-transition
  hooks and `O(1)` chunked certificate composition.
-/

@[expose] public section

namespace BusyBeaver.WordRLE

open Turing

/-! ## Call-by-Value Kernel Normalizer (`withNat`) -/

/-- Force `n : ℕ` to weak-head normal form (`0` or `Nat.succ m`) before passing it to `k`,
preventing call-by-name thunk accumulation during `decide +kernel` reduction while remaining
definitionally equal to `k n` on numerals and provably `k n` for all `n`. -/
@[inline]
def withNat {α : Type*} (n : ℕ) (k : ℕ → α) : α :=
  match n with
  | 0 => k 0
  | m + 1 => k (Nat.succ m)

@[simp]
theorem withNat_eq {α : Type*} (n : ℕ) (k : ℕ → α) : withNat n k = k n := by
  cases n <;> rfl

/-- Force `b : Bool` to weak-head normal form (`true` or `false`) before passing it to `k`. -/
@[inline]
def withBool {α : Type*} (b : Bool) (k : Bool → α) : α :=
  if b then k true else k false

@[simp]
theorem withBool_eq {α : Type*} (b : Bool) (k : Bool → α) : withBool b k = k b := by
  cases b <;> rfl

/-! ## Balanced Binary Trees (`BTree`) and `ℕ`-Keyed Radix Tries (`NatTrie`) -/

/-- Balanced binary tree keeping certificate expression depth logarithmic (`O(log N)`). -/
inductive BTree (α : Type) where
  /-- Empty tree. -/
  | empty : BTree α
  /-- Single element leaf. -/
  | leaf (val : α) : BTree α
  /-- Internal binary node. -/
  | node (left right : BTree α) : BTree α
  deriving DecidableEq, Inhabited

/-- Convert a `BTree α` to a `List α` in left-to-right order with accumulator `acc`. -/
def BTree.toListAcc {α : Type} : BTree α → List α → List α
  | .empty, acc => acc
  | .leaf x, acc => x :: acc
  | .node l r, acc => l.toListAcc (r.toListAcc acc)

/-- Convert a `BTree α` to a `List α` in left-to-right order. -/
def BTree.toList {α : Type} (t : BTree α) : List α :=
  t.toListAcc []

/-- Little-endian binary radix trie keyed by `ℕ`, enabling `O(log N)` constructor-match lookups
inside the Lean kernel with zero rebuild overhead when emitted directly as a certificate tree. -/
inductive NatTrie (α : Type) where
  /-- Empty subtrie. -/
  | leaf : NatTrie α
  /-- Binary trie node with optional value at key `0` and even/odd child subtries. -/
  | node (val : Option α) (even odd : NatTrie α) : NatTrie α
  deriving DecidableEq, Inhabited

namespace NatTrie

/-- Look up key `n` in radix trie `t`. -/
def find? {α : Type} : NatTrie α → ℕ → Option α
  | .leaf, _ => none
  | .node v _ _, 0 => v
  | .node _ l r, n + 1 =>
    let m := n + 1
    if Nat.beq (m % 2) 0 then find? l (m / 2) else find? r (m / 2)

/-- Fuel-bounded radix-trie insertion helper. -/
def insFuel {α : Type} : ℕ → NatTrie α → ℕ → α → NatTrie α
  | 0, t, _, _ => t
  | _ + 1, .leaf, 0, val => .node (some val) .leaf .leaf
  | fuel + 1, .leaf, n + 1, val =>
    let m := n + 1
    if Nat.beq (m % 2) 0 then .node none (insFuel fuel .leaf (m / 2) val) .leaf
    else .node none .leaf (insFuel fuel .leaf (m / 2) val)
  | _ + 1, .node _ l r, 0, val => .node (some val) l r
  | fuel + 1, .node v l r, n + 1, val =>
    let m := n + 1
    if Nat.beq (m % 2) 0 then .node v (insFuel fuel l (m / 2) val) r
    else .node v l (insFuel fuel r (m / 2) val)

/-- Insert `(k, val)` into radix trie `t` (supports keys up to `2^32 - 1`). -/
def insert {α : Type} (t : NatTrie α) (k : ℕ) (val : α) : NatTrie α :=
  insFuel 32 t k val

/-- Check predicate `p key val` on every stored entry in `t`, reconstructing keys as
`keyPrefix + localKey * bitMul`. -/
def checkAll {α : Type} (p : ℕ → α → Bool) (keyPrefix bitMul : ℕ) : NatTrie α → Bool
  | .leaf => true
  | .node val? l r =>
    let selfOk := match val? with | none => true | some v => p keyPrefix v
    selfOk &&
      checkAll p keyPrefix (bitMul * 2) l &&
      checkAll p (keyPrefix + bitMul) (bitMul * 2) r

theorem checkAll_node_iff {α : Type} (p : ℕ → α → Bool) (keyPrefix bitMul : ℕ)
    (val? : Option α) (l r : NatTrie α) :
    checkAll p keyPrefix bitMul (.node val? l r) = true ↔
      (match val? with | none => true | some v => p keyPrefix v) = true ∧
      checkAll p keyPrefix (bitMul * 2) l = true ∧
      checkAll p (keyPrefix + bitMul) (bitMul * 2) r = true := by
  simp only [checkAll, Bool.and_eq_true, and_assoc]

/-- Any value found via `NatTrie.find?` in a `checkAll`-verified subtrie satisfies `p`. -/
theorem checkAll_find? {α : Type} {p : ℕ → α → Bool} :
    ∀ (t : NatTrie α) (keyPrefix bitMul n : ℕ) (val : α),
      checkAll p keyPrefix bitMul t = true →
      t.find? n = some val →
      p (keyPrefix + n * bitMul) val = true
  | .leaf, _, _, _, _, _, hf => by simp [find?] at hf
  | .node val? l r, keyPrefix, bitMul, 0, val, hc, hf => by
    rw [checkAll_node_iff] at hc
    simp only [find?] at hf
    subst hf
    simpa using hc.1
  | .node val? l r, keyPrefix, bitMul, n + 1, val, hc, hf => by
    rw [checkAll_node_iff] at hc
    simp only [find?] at hf
    by_cases hev : Nat.beq ((n + 1) % 2) 0 = true
    · simp only [hev, ↓reduceIte] at hf
      have hmod : (n + 1) % 2 = 0 := Nat.eq_of_beq_eq_true hev
      have ih := checkAll_find? l keyPrefix (bitMul * 2) ((n + 1) / 2) val hc.2.1 hf
      have hkey : keyPrefix + (n + 1) / 2 * (bitMul * 2) = keyPrefix + (n + 1) * bitMul := by
        have hdiv : (n + 1) / 2 * 2 = n + 1 := by omega
        rw [Nat.mul_comm bitMul 2, ← Nat.mul_assoc, Nat.mul_comm ((n + 1) / 2) 2]
        have h2 : 2 * ((n + 1) / 2) = n + 1 := by omega
        rw [h2]
      rwa [hkey] at ih
    · have hne : Nat.beq ((n + 1) % 2) 0 = false := Bool.eq_false_iff.mpr hev
      simp only [hne, Bool.false_eq_true, ↓reduceIte] at hf
      have hmod : (n + 1) % 2 = 1 := by
        have hnz : (n + 1) % 2 ≠ 0 := fun h0 ↦ hev (by rw [h0]; rfl)
        omega
      have ih := checkAll_find? r (keyPrefix + bitMul) (bitMul * 2) ((n + 1) / 2) val hc.2.2 hf
      have hkey :
          keyPrefix + bitMul + (n + 1) / 2 * (bitMul * 2) = keyPrefix + (n + 1) * bitMul := by
        have hdiv : 2 * ((n + 1) / 2) + 1 = n + 1 := by omega
        calc
          keyPrefix + bitMul + (n + 1) / 2 * (bitMul * 2)
            = keyPrefix + (bitMul + (n + 1) / 2 * (2 * bitMul)) := by
                rw [Nat.mul_comm bitMul 2, Nat.add_assoc]
          _ = keyPrefix + (1 * bitMul + (n + 1) / 2 * 2 * bitMul) := by
                rw [Nat.one_mul, Nat.mul_assoc]
          _ = keyPrefix + (2 * ((n + 1) / 2) + 1) * bitMul := by
                rw [Nat.add_comm (1 * bitMul), ← Nat.add_mul, Nat.mul_comm ((n + 1) / 2) 2]
          _ = keyPrefix + (n + 1) * bitMul := by rw [hdiv]
      rwa [hkey] at ih

/-- Root-level specialization of `checkAll_find?`: if `checkAll p 0 1 t = true` and
`t.find? n = some val`, then `p n val = true`. -/
theorem checkAll_sound {α : Type} {p : ℕ → α → Bool} {t : NatTrie α}
    (hc : checkAll p 0 1 t = true) {n : ℕ} {val : α} (hf : t.find? n = some val) :
    p n val = true := by
  simpa using checkAll_find? t 0 1 n val hc hf

end NatTrie

/-! ## Word Repetition, Rotation, Concatenation, and Blank-Tape Identities -/

section ListIdentities

variable {Γ : Type*}

/-- Reversing `u ^ n` reverses the base word `u`. -/
theorem reverse_pow (u : List Γ) (n : ℕ) : (u ^ n).reverse = u.reverse ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [list_pow_succ, List.reverse_append, ih, ← list_pow_succ']

/-- Word-power rotation identity: `(u ++ w) ^ n ++ u = u ++ (w ++ u) ^ n`. -/
theorem lpow_rot (u w : List Γ) (n : ℕ) : (u ++ w) ^ n ++ u = u ++ (w ++ u) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [list_pow_succ, list_pow_succ, List.append_assoc, ih]
    simp [List.append_assoc]

/-- Concatenate a list of subword indices left-to-right using `baseWord : ℕ → List Γ`. -/
def concatSubwords (baseWord : ℕ → List Γ) : List ℕ → List Γ
  | [] => []
  | s :: ss => baseWord s ++ concatSubwords baseWord ss

@[simp]
theorem concatSubwords_append (baseWord : ℕ → List Γ) (xs ys : List ℕ) :
    concatSubwords baseWord (xs ++ ys) =
      concatSubwords baseWord xs ++ concatSubwords baseWord ys := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [concatSubwords, ih, List.append_assoc]

theorem lb_blank_word [Inhabited Γ] (z : List Γ) (hz : ∀ x ∈ z, x = default) :
    ListBlank.append z default = default := by
  induction z with
  | nil => rfl
  | cons x z ih =>
    rw [ListBlank.append_cons, ih (fun y hy ↦ hz y (List.mem_cons_of_mem _ hy)),
      hz x List.mem_cons_self, ListBlank.cons_default_default]

theorem lb_blank_pow [Inhabited Γ] (z : List Γ) (hz : ∀ x ∈ z, x = default) (n : ℕ) :
    ListBlank.append (z ^ n) default = default := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [list_pow_succ, ListBlank.append_assoc, ih, lb_blank_word z hz]

end ListIdentities

/-! ## Directed Configurations and Local Word-Exit Semantics -/

section WordSemantics

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Directed machine configuration: `Cfg.headRight` when `dir = true` and `Cfg.headLeft` when
`dir = false`, indexing control states via `qOf : ℕ → Λ`. -/
def dirCfg (qOf : ℕ → Λ) (q : ℕ) (dir : Bool) (l r : ListBlank Γ) : Cfg Γ Λ :=
  if dir then Cfg.headRight (qOf q) l r else Cfg.headLeft (qOf q) l r

/-- Agreement between a pure `ℕ`-indexed transition function `stepCode` and `M : Machine Γ Λ`. -/
def StepCodeAgrees (M : Machine Γ Λ) (qOf : ℕ → Λ)
    (stepCode : ℕ → Γ → Option (Γ × Bool × ℕ)) : Prop :=
  ∀ q a b dir' q', stepCode q a = some (b, dir', q') →
    M (qOf q) a = some (some (qOf q'), Stmt.write b (if dir' then Dir.right else Dir.left))

/-- Place spatial word `w` (written left-to-right) adjacent to the head on side `side` (`true` for
right half-tape, `false` for left half-tape where nearest-to-head comes first via `w.reverse`). -/
def placeSide (side : Bool) (w : List Γ) (l r : ListBlank Γ) : ListBlank Γ × ListBlank Γ :=
  if side then (l, ListBlank.append w r) else (ListBlank.append w.reverse l, r)

/-- Semantic specification of a local finite-word exit: entering spatial word `u` in state `q`
moving in direction `dir` exits in `dt` steps leaving spatial word `v` behind the head in state `q'`
moving in direction `dir'`, for arbitrary surrounding half-tapes `l` and `r`. -/
def WordExit (M : Machine Γ Λ) (qOf : ℕ → Λ)
    (u : List Γ) (q : ℕ) (dir : Bool) (v : List Γ) (q' : ℕ) (dir' : Bool) (dt : ℕ) : Prop :=
  ∀ l r : ListBlank Γ,
    let (l₁, r₁) := placeSide dir u l r
    let (l₂, r₂) := placeSide (!dir') v l r
    ReachesIn M dt (dirCfg qOf q dir l₁ r₁) (dirCfg qOf q' dir' l₂ r₂)

/-- Local symbol-level finite-word zipper simulator. -/
def simWord (stepCode : ℕ → Γ → Option (Γ × Bool × ℕ)) :
    ℕ → ℕ → Bool → List Γ → List Γ → ℕ → Option (List Γ × ℕ × Bool × ℕ)
  | 0, _, _, _, _, _ => none
  | _ + 1, q, true, lw, [], dt =>
    withNat q fun q' ↦ withNat dt fun d ↦ some (lw.reverse, q', true, d)
  | fuel + 1, q, true, lw, a :: rw, dt =>
    match stepCode q a with
    | none => none
    | some (b, true, q') =>
      withNat (dt + 1) fun dt' ↦ simWord stepCode fuel q' true (b :: lw) rw dt'
    | some (b, false, q') =>
      withNat (dt + 1) fun dt' ↦ simWord stepCode fuel q' false lw (b :: rw) dt'
  | _ + 1, q, false, [], rw, dt =>
    withNat q fun q' ↦ withNat dt fun d ↦ some (rw, q', false, d)
  | fuel + 1, q, false, a :: lw, rw, dt =>
    match stepCode q a with
    | none => none
    | some (b, true, q') =>
      withNat (dt + 1) fun dt' ↦ simWord stepCode fuel q' true (b :: lw) rw dt'
    | some (b, false, q') =>
      withNat (dt + 1) fun dt' ↦ simWord stepCode fuel q' false lw (b :: rw) dt'

/-- Run `simWord` on spatial word `u` from state `q` and entry direction `dir`. -/
def runWordExit (stepCode : ℕ → Γ → Option (Γ × Bool × ℕ)) (fuel : ℕ)
    (u : List Γ) (q : ℕ) (dir : Bool) : Option (List Γ × ℕ × Bool × ℕ) :=
  if dir then simWord stepCode fuel q true [] u 0
  else simWord stepCode fuel q false u.reverse [] 0

private theorem simWord_sound_aux {M : Machine Γ Λ} {qOf : ℕ → Λ}
    {stepCode : ℕ → Γ → Option (Γ × Bool × ℕ)} (hag : StepCodeAgrees M qOf stepCode) :
    ∀ (fuel q : ℕ) (dir : Bool) (lw rw : List Γ) (dt : ℕ)
      (v : List Γ) (q' : ℕ) (dir' : Bool) (dtOut : ℕ) (l r : ListBlank Γ),
      simWord stepCode fuel q dir lw rw dt = some (v, q', dir', dtOut) →
      dt ≤ dtOut ∧
        let (l₂, r₂) := placeSide (!dir') v l r
        ReachesIn M (dtOut - dt)
          (dirCfg qOf q dir (ListBlank.append lw l) (ListBlank.append rw r))
          (dirCfg qOf q' dir' l₂ r₂)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [simWord] at h
  | _ + 1, q, true, lw, [], dt, v, q', dir', dtOut, l, r, h => by
    simp only [simWord, withNat_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨Nat.le_refl dt, ?_⟩
    simp [placeSide, List.reverse_reverse]
  | fuel + 1, q, true, lw, a :: rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simWord, withNat_eq] at h
    rcases hsc : stepCode q a with _ | ⟨b, dNext, qNext⟩
    · simp [hsc] at h
    · rw [hsc] at h
      cases dNext
      · simp only at h
        obtain ⟨hle, hreach⟩ :=
          simWord_sound_aux hag fuel qNext false lw (b :: rw) (dt + 1) v q' dir' dtOut l r h
        have hstep := step_headRight_left (hag q a b false qNext hsc)
          (ListBlank.append lw l) (ListBlank.append rw r)
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = (dtOut - (dt + 1)) + 1 := by omega
        rw [hsub]
        exact ReachesIn.step_left hstep hreach
      · simp only at h
        obtain ⟨hle, hreach⟩ :=
          simWord_sound_aux hag fuel qNext true (b :: lw) rw (dt + 1) v q' dir' dtOut l r h
        have hstep := step_headRight_right (hag q a b true qNext hsc)
          (ListBlank.append lw l) (ListBlank.append rw r)
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = (dtOut - (dt + 1)) + 1 := by omega
        rw [hsub]
        exact ReachesIn.step_left hstep hreach
  | _ + 1, q, false, [], rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simWord, withNat_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨Nat.le_refl dt, ?_⟩
    simp [placeSide]
  | fuel + 1, q, false, a :: lw, rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simWord, withNat_eq] at h
    rcases hsc : stepCode q a with _ | ⟨b, dNext, qNext⟩
    · simp [hsc] at h
    · rw [hsc] at h
      cases dNext
      · simp only at h
        obtain ⟨hle, hreach⟩ :=
          simWord_sound_aux hag fuel qNext false lw (b :: rw) (dt + 1) v q' dir' dtOut l r h
        have hstep := step_headLeft_left (hag q a b false qNext hsc)
          (ListBlank.append lw l) (ListBlank.append rw r)
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = (dtOut - (dt + 1)) + 1 := by omega
        rw [hsub]
        exact ReachesIn.step_left hstep hreach
      · simp only at h
        obtain ⟨hle, hreach⟩ :=
          simWord_sound_aux hag fuel qNext true (b :: lw) rw (dt + 1) v q' dir' dtOut l r h
        have hstep := step_headLeft_right (hag q a b true qNext hsc)
          (ListBlank.append lw l) (ListBlank.append rw r)
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = (dtOut - (dt + 1)) + 1 := by omega
        rw [hsub]
        exact ReachesIn.step_left hstep hreach

/-- Soundness of `runWordExit`: a successful finite-word zipper run establishes `WordExit`. -/
theorem runWordExit_sound {M : Machine Γ Λ} {qOf : ℕ → Λ}
    {stepCode : ℕ → Γ → Option (Γ × Bool × ℕ)} (hag : StepCodeAgrees M qOf stepCode)
    {fuel : ℕ} {u : List Γ} {q : ℕ} {dir : Bool}
    {v : List Γ} {q' : ℕ} {dir' : Bool} {dt : ℕ}
    (h : runWordExit stepCode fuel u q dir = some (v, q', dir', dt)) :
    WordExit M qOf u q dir v q' dir' dt := by
  intro l r
  unfold runWordExit at h
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    simpa [placeSide] using (simWord_sound_aux hag fuel q false u.reverse [] 0 v q' dir' dt l r h).2
  · simp only [↓reduceIte] at h
    simpa [placeSide] using (simWord_sound_aux hag fuel q true [] u 0 v q' dir' dt l r h).2

/-- Homogeneous `k`-copy sweep: if `(u, q, dir)` exits in the same state and direction `(q, dir)`
leaving `v` in `dt` steps, then `u ^ k` exits in `(q, dir)` leaving `v ^ k` in `dt * k` steps. -/
theorem sweepWord_sound {M : Machine Γ Λ} {qOf : ℕ → Λ}
    {u v : List Γ} {q : ℕ} {dir : Bool} {dt : ℕ}
    (hex : WordExit M qOf u q dir v q dir dt) (k : ℕ) :
    WordExit M qOf (u ^ k) q dir (v ^ k) q dir (dt * k) := by
  induction k with
  | zero =>
    intro l r
    simp [placeSide]
  | succ k ih =>
    intro l r
    cases dir
    · simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false]
      rw [list_pow_succ' u k, List.reverse_append, ListBlank.append_assoc,
        list_pow_succ' v k, ListBlank.append_assoc]
      have h1 := hex (ListBlank.append (u ^ k).reverse l) r
      simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h1
      have h2 := ih l (ListBlank.append v r)
      simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at h2
      have htr := h1.trans h2
      have hdt : dt + dt * k = dt * (k + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      rwa [hdt] at htr
    · simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true]
      rw [list_pow_succ u k, ListBlank.append_assoc,
        list_pow_succ v k, List.reverse_append, ListBlank.append_assoc]
      have h1 := hex l (ListBlank.append (u ^ k) r)
      simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at h1
      have h2 := ih (ListBlank.append v.reverse l) r
      simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at h2
      have htr := h1.trans h2
      have hdt : dt + dt * k = dt * (k + 1) := by rw [Nat.mul_succ, Nat.add_comm]
      rwa [hdt] at htr

/-! ## Composite Subword Zipper (`simSubwords`) -/

/-- Soundness predicate for a base-word exit function `(q, dir, s) ↦ (s', q', dir', dt)`. -/
def BaseExitSound (M : Machine Γ Λ) (qOf : ℕ → Λ) (baseWord : ℕ → List Γ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)) : Prop :=
  ∀ q dir s s' q' dir' dt,
    baseExit q dir s = some (s', q', dir', dt) →
    WordExit M qOf (baseWord s) q dir (baseWord s') q' dir' dt

/-- Subword-level local zipper simulator over a verified `baseExit` table. -/
def simSubwords (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)) :
    ℕ → ℕ → Bool → List ℕ → List ℕ → ℕ → Option (List ℕ × ℕ × Bool × ℕ)
  | 0, _, _, _, _, _ => none
  | _ + 1, q, true, lw, [], dt =>
    withNat q fun q' ↦ withNat dt fun d ↦ some (lw.reverse, q', true, d)
  | fuel + 1, q, true, lw, a :: rw, dt =>
    match baseExit q true a with
    | none => none
    | some (s', q', dir', exDt) =>
      withNat (dt + exDt) fun dt' ↦
        if dir' then simSubwords baseExit fuel q' true (s' :: lw) rw dt'
        else simSubwords baseExit fuel q' false lw (s' :: rw) dt'
  | _ + 1, q, false, [], rw, dt =>
    withNat q fun q' ↦ withNat dt fun d ↦ some (rw, q', false, d)
  | fuel + 1, q, false, a :: lw, rw, dt =>
    match baseExit q false a with
    | none => none
    | some (s', q', dir', exDt) =>
      withNat (dt + exDt) fun dt' ↦
        if dir' then simSubwords baseExit fuel q' true (s' :: lw) rw dt'
        else simSubwords baseExit fuel q' false lw (s' :: rw) dt'

/-- Compute the composite exit of subword list `u` from `(q, dir)` using `baseExit`. -/
def runCompositeExit (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ))
    (u : List ℕ) (q : ℕ) (dir : Bool) : Option (List ℕ × ℕ × Bool × ℕ) :=
  withNat (u.length * 16 + 16) fun fuel ↦
    if dir then simSubwords baseExit fuel q true [] u 0
    else simSubwords baseExit fuel q false u.reverse [] 0

private def leftSubTape (baseWord : ℕ → List Γ) : List ℕ → ListBlank Γ → ListBlank Γ
  | [], l => l
  | s :: lw, l => ListBlank.append (baseWord s).reverse (leftSubTape baseWord lw l)

private def rightSubTape (baseWord : ℕ → List Γ) : List ℕ → ListBlank Γ → ListBlank Γ
  | [], r => r
  | s :: rw, r => ListBlank.append (baseWord s) (rightSubTape baseWord rw r)

private theorem rightSubTape_eq (baseWord : ℕ → List Γ) (rw : List ℕ) (r : ListBlank Γ) :
    rightSubTape baseWord rw r = ListBlank.append (concatSubwords baseWord rw) r := by
  induction rw with
  | nil => rfl
  | cons s rw ih =>
    simp [rightSubTape, concatSubwords, ih, ListBlank.append_assoc]

private theorem leftSubTape_append (baseWord : ℕ → List Γ) (xs ys : List ℕ) (l : ListBlank Γ) :
    leftSubTape baseWord (xs ++ ys) l = leftSubTape baseWord xs (leftSubTape baseWord ys l) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [leftSubTape, ih]

private theorem leftSubTape_reverse_eq (baseWord : ℕ → List Γ) (u : List ℕ) (l : ListBlank Γ) :
    leftSubTape baseWord u.reverse l =
      ListBlank.append (concatSubwords baseWord u).reverse l := by
  induction u generalizing l with
  | nil => rfl
  | cons s u ih =>
    simp only [List.reverse_cons, leftSubTape_append, leftSubTape, concatSubwords,
      List.reverse_append, ListBlank.append_assoc]
    rw [ih]

private theorem leftSubTape_eq (baseWord : ℕ → List Γ) (lw : List ℕ) (l : ListBlank Γ) :
    leftSubTape baseWord lw l =
      ListBlank.append (concatSubwords baseWord lw.reverse).reverse l := by
  simpa using leftSubTape_reverse_eq baseWord lw.reverse l

private theorem simSubwords_sound_aux {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit) :
    ∀ (fuel q : ℕ) (dir : Bool) (lw rw : List ℕ) (dt : ℕ)
      (v : List ℕ) (q' : ℕ) (dir' : Bool) (dtOut : ℕ) (l r : ListBlank Γ),
      simSubwords baseExit fuel q dir lw rw dt = some (v, q', dir', dtOut) →
      dt ≤ dtOut ∧
        let (l₂, r₂) := placeSide (!dir') (concatSubwords baseWord v) l r
        ReachesIn M (dtOut - dt)
          (dirCfg qOf q dir (leftSubTape baseWord lw l) (rightSubTape baseWord rw r))
          (dirCfg qOf q' dir' l₂ r₂)
  | 0, _, _, _, _, _, _, _, _, _, _, _, h => by simp [simSubwords] at h
  | _ + 1, q, true, lw, [], dt, v, q', dir', dtOut, l, r, h => by
    simp only [simSubwords, withNat_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨Nat.le_refl dt, ?_⟩
    simp [placeSide, leftSubTape_eq, rightSubTape]
  | fuel + 1, q, true, lw, a :: rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simSubwords, withNat_eq] at h
    rcases hb : baseExit q true a with _ | ⟨s', qNext, dNext, exDt⟩
    · simp [hb] at h
    · rw [hb] at h
      have hex := hbase q true a s' qNext dNext exDt hb
        (leftSubTape baseWord lw l) (rightSubTape baseWord rw r)
      cases dNext
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        simp only [placeSide, ↓reduceIte, Bool.not_false] at hex
        obtain ⟨hle, hreach⟩ :=
          simSubwords_sound_aux hbase fuel qNext false lw (s' :: rw) (dt + exDt) v q' dir' dtOut
            l r h
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = exDt + (dtOut - (dt + exDt)) := by omega
        rw [hsub]
        exact hex.trans hreach
      · simp only [↓reduceIte] at h
        simp only [placeSide, ↓reduceIte, Bool.not_true] at hex
        obtain ⟨hle, hreach⟩ :=
          simSubwords_sound_aux hbase fuel qNext true (s' :: lw) rw (dt + exDt) v q' dir' dtOut
            l r h
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = exDt + (dtOut - (dt + exDt)) := by omega
        rw [hsub]
        exact hex.trans hreach
  | _ + 1, q, false, [], rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simSubwords, withNat_eq, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨Nat.le_refl dt, ?_⟩
    simp [placeSide, leftSubTape, rightSubTape_eq]
  | fuel + 1, q, false, a :: lw, rw, dt, v, q', dir', dtOut, l, r, h => by
    simp only [simSubwords, withNat_eq] at h
    rcases hb : baseExit q false a with _ | ⟨s', qNext, dNext, exDt⟩
    · simp [hb] at h
    · rw [hb] at h
      have hex := hbase q false a s' qNext dNext exDt hb
        (leftSubTape baseWord lw l) (rightSubTape baseWord rw r)
      cases dNext
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_false] at hex
        obtain ⟨hle, hreach⟩ :=
          simSubwords_sound_aux hbase fuel qNext false lw (s' :: rw) (dt + exDt) v q' dir' dtOut
            l r h
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = exDt + (dtOut - (dt + exDt)) := by omega
        rw [hsub]
        exact hex.trans hreach
      · simp only [↓reduceIte] at h
        simp only [placeSide, Bool.false_eq_true, ↓reduceIte, Bool.not_true] at hex
        obtain ⟨hle, hreach⟩ :=
          simSubwords_sound_aux hbase fuel qNext true (s' :: lw) rw (dt + exDt) v q' dir' dtOut
            l r h
        refine ⟨by omega, ?_⟩
        have hsub : dtOut - dt = exDt + (dtOut - (dt + exDt)) := by omega
        rw [hsub]
        exact hex.trans hreach

/-- Soundness of `runCompositeExit`: lifts base-word exits to composite subword exits. -/
theorem runCompositeExit_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    {u : List ℕ} {q : ℕ} {dir : Bool} {v : List ℕ} {q' : ℕ} {dir' : Bool} {dt : ℕ}
    (h : runCompositeExit baseExit u q dir = some (v, q', dir', dt)) :
    WordExit M qOf (concatSubwords baseWord u) q dir (concatSubwords baseWord v) q' dir' dt := by
  intro l r
  unfold runCompositeExit at h
  rw [withNat_eq] at h
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    have ⟨_, hr⟩ := simSubwords_sound_aux hbase (u.length * 16 + 16) q false u.reverse [] 0
      v q' dir' dt l r h
    simpa [placeSide, leftSubTape_reverse_eq, rightSubTape] using hr
  · simp only [↓reduceIte] at h
    have ⟨_, hr⟩ := simSubwords_sound_aux hbase (u.length * 16 + 16) q true [] u 0
      v q' dir' dt l r h
    simpa [placeSide, leftSubTape, rightSubTape_eq] using hr

/-! ## Concrete RLE Stack Configurations and Multi-Step Reachability -/

/-- A concrete run of `count` copies of vocabulary word `sym` (`sym = 0` denotes the blank word). -/
structure Run where
  /-- Vocabulary index of the repeated spatial word. -/
  sym : ℕ
  /-- Repetition count (`count ≥ 1` in normalized stacks). -/
  count : ℕ
  deriving DecidableEq, Inhabited

/-- Concrete RLE configuration with head state `q`, direction `dir`, and RLE half-tape stacks. -/
structure EntryCfg where
  /-- Current state index. -/
  q : ℕ
  /-- Head direction (`true` = right, `false` = left). -/
  dir : Bool
  /-- Left half-tape stack (nearest-to-head run first). -/
  left : List Run
  /-- Right half-tape stack (nearest-to-head run first). -/
  right : List Run
  deriving DecidableEq, Inhabited

/-- Push `count ≥ 1` copies of `sym` onto `stk`, suppressing leading blank runs (`sym = 0` on `[]`)
and merging adjacent runs of the same word. -/
@[inline]
def pushLit (sym count : ℕ) : List Run → List Run
  | [] => if Nat.beq sym 0 then [] else [⟨sym, count⟩]
  | ⟨ts, tc⟩ :: rest =>
    if Nat.beq ts sym then withNat (tc + count) fun c ↦ ⟨ts, c⟩ :: rest
    else ⟨sym, count⟩ :: ⟨ts, tc⟩ :: rest

/-- Safe push handling `count = 0` as a no-op. -/
def pushRun (sym count : ℕ) (stk : List Run) : List Run :=
  if Nat.beq count 0 then stk else pushLit sym count stk

/-- Push a spatial left-to-right list of `(sym, count)` runs onto a left RLE stack so the last pair
in the list sits closest to the head. -/
def pushRunsLeft : List (ℕ × ℕ) → List Run → List Run
  | [], stk => stk
  | (s, n) :: rest, stk => pushRunsLeft rest (pushRun s n stk)

/-- Evaluate an RLE stack on side `side` (`true` = right stack using `wordOf w ^ c`, `false` = left
stack using `(wordOf w).reverse ^ c`). -/
def evalSide (side : Bool) (wordOf : ℕ → List Γ) : List Run → ListBlank Γ
  | [] => default
  | ⟨w, c⟩ :: rest =>
    if side then ListBlank.append (wordOf w ^ c) (evalSide true wordOf rest)
    else ListBlank.append ((wordOf w).reverse ^ c) (evalSide false wordOf rest)

/-- Evaluate a concrete `EntryCfg` into a `BusyBeaver.Cfg Γ Λ`. -/
def evalEntryCfg (qOf : ℕ → Λ) (wordOf : ℕ → List Γ) (c : EntryCfg) : Cfg Γ Λ :=
  dirCfg qOf c.q c.dir (evalSide false wordOf c.left) (evalSide true wordOf c.right)

/-- Soundness of `pushLit` when `wordOf 0` consists solely of blank symbols (`default`). -/
theorem evalSide_pushLit {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    (side : Bool) (sym count : ℕ) (stk : List Run) :
    evalSide side wordOf (pushLit sym count stk) =
      if side then ListBlank.append (wordOf sym ^ count) (evalSide true wordOf stk)
      else ListBlank.append ((wordOf sym).reverse ^ count) (evalSide false wordOf stk) := by
  have hzRev : ∀ x ∈ (wordOf 0).reverse, x = default := by
    intro x hx; exact hz x (List.mem_reverse.mp hx)
  cases stk with
  | nil =>
    simp only [pushLit]
    by_cases hs : Nat.beq sym 0 = true
    · have h0 : sym = 0 := Nat.eq_of_beq_eq_true hs
      subst h0
      cases side <;> simp [evalSide, lb_blank_pow _ hz, lb_blank_pow _ hzRev]
    · have hne : Nat.beq sym 0 = false := Bool.eq_false_iff.mpr hs
      rw [hne]
      cases side <;> rfl
  | cons top rest =>
    rcases top with ⟨ts, tc⟩
    simp only [pushLit]
    by_cases hs : Nat.beq ts sym = true
    · have heq : ts = sym := Nat.eq_of_beq_eq_true hs
      subst heq
      simp only [hs, ↓reduceIte, withNat_eq]
      cases side <;>
        simp [evalSide, ListBlank.append_append, ← list_pow_add, Nat.add_comm]
    · have hne : Nat.beq ts sym = false := Bool.eq_false_iff.mpr hs
      rw [hne]
      cases side <;> rfl

theorem evalSide_pushRun {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    (side : Bool) (sym count : ℕ) (stk : List Run) :
    evalSide side wordOf (pushRun sym count stk) =
      if side then ListBlank.append (wordOf sym ^ count) (evalSide true wordOf stk)
      else ListBlank.append ((wordOf sym).reverse ^ count) (evalSide false wordOf stk) := by
  unfold pushRun
  by_cases hc : Nat.beq count 0 = true
  · have h0 : count = 0 := Nat.eq_of_beq_eq_true hc
    subst h0
    cases side <;> simp
  · have hne : Nat.beq count 0 = false := Bool.eq_false_iff.mpr hc
    rw [hne]
    exact evalSide_pushLit hz side sym count stk

/-- Soundness predicate for a single-step concrete RLE transition function `stepFn`. -/
def StepFnSound (M : Machine Γ Λ) (qOf : ℕ → Λ) (wordOf : ℕ → List Γ)
    (stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)) : Prop :=
  ∀ q dir l r dt c',
    stepFn q dir l r = some (dt, c') →
    ReachesIn M dt (evalEntryCfg qOf wordOf ⟨q, dir, l, r⟩) (evalEntryCfg qOf wordOf c')

/-- Execute exactly `fuel` accelerated RLE steps using `stepFn`, accumulating exact TM steps. -/
def runExact (stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)) :
    ℕ → ℕ → EntryCfg → Option (ℕ × EntryCfg)
  | 0, acc, c => some (acc, c)
  | fuel + 1, acc, ⟨q, dir, l, r⟩ =>
    match stepFn q dir l r with
    | none => none
    | some (dt, c') => withNat (acc + dt) fun acc' ↦ runExact stepFn fuel acc' c'

/-- Boolean check that `runExact stepFn fuel 0 c` yields `(expDt, expC)`. -/
def checkRunExact (stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg))
    (fuel expDt : ℕ) (c expC : EntryCfg) : Bool :=
  match runExact stepFn fuel 0 c with
  | none => false
  | some (dt, c') => Nat.beq dt expDt && (c' == expC)

private theorem runExact_sound_aux {M : Machine Γ Λ} {qOf : ℕ → Λ} {wordOf : ℕ → List Γ}
    {stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)}
    (hs : StepFnSound M qOf wordOf stepFn) :
    ∀ (fuel acc : ℕ) (c : EntryCfg) (accOut : ℕ) (cOut : EntryCfg),
      runExact stepFn fuel acc c = some (accOut, cOut) →
      acc ≤ accOut ∧
        ReachesIn M (accOut - acc) (evalEntryCfg qOf wordOf c) (evalEntryCfg qOf wordOf cOut)
  | 0, acc, c, accOut, cOut, h => by
    simp only [runExact, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨Nat.le_refl acc, by simp⟩
  | fuel + 1, acc, ⟨q, dir, l, r⟩, accOut, cOut, h => by
    simp only [runExact] at h
    rcases hst : stepFn q dir l r with _ | ⟨dt, c'⟩
    · simp [hst] at h
    · rw [hst] at h
      simp only [withNat_eq] at h
      obtain ⟨hle, hrest⟩ := runExact_sound_aux hs fuel (acc + dt) c' accOut cOut h
      have h1 := hs q dir l r dt c' hst
      refine ⟨by omega, ?_⟩
      have hsub : accOut - acc = dt + (accOut - (acc + dt)) := by omega
      rw [hsub]
      exact h1.trans hrest

/-- Inductive certificate tree chaining kernel-checked `checkRunExact` chunks with `O(1)` proof
composition. -/
inductive EntryReaches (stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)) :
    ℕ → EntryCfg → EntryCfg → Prop where
  /-- Zero-step reflexive reachability. -/
  | refl (c : EntryCfg) : EntryReaches stepFn 0 c c
  /-- Single kernel-checked `fuel`-loop chunk. -/
  | chunk {fuel dt : ℕ} {c c' : EntryCfg} :
      checkRunExact stepFn fuel dt c c' = true →
      EntryReaches stepFn dt c c'
  /-- Transitive composition of two chunks. -/
  | trans {d₁ d₂ : ℕ} {c₁ c₂ c₃ : EntryCfg} :
      EntryReaches stepFn d₁ c₁ c₂ → EntryReaches stepFn d₂ c₂ c₃ →
      EntryReaches stepFn (d₁ + d₂) c₁ c₃

/-- Cast the accumulated step sum `d₁` to a normalized `ℕ` literal `d₂` via `Nat.beq`. -/
theorem EntryReaches.cast_dt {stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)}
    {d₁ d₂ : ℕ} {c₁ c₂ : EntryCfg}
    (h : EntryReaches stepFn d₁ c₁ c₂) (heq : Nat.beq d₁ d₂ = true) :
    EntryReaches stepFn d₂ c₁ c₂ := by
  have hd : d₁ = d₂ := Nat.eq_of_beq_eq_true heq
  exact hd ▸ h

/-- Boolean check that `(d₁, c₁, c₂)` matches target `(d₂, c₁', c₂')`. -/
def checkEntryEnds (d₁ d₂ : ℕ) (c₁ c₁' c₂ c₂' : EntryCfg) : Bool :=
  Nat.beq d₁ d₂ && (c₁ == c₁') && (c₂ == c₂')

/-- Cast `(d₁, c₁, c₂)` to target expressions `(d₂, c₁', c₂')` via a kernel-checked `Bool`
certificate, avoiding elaborator `isDefEq` unfolding on large closed-form milestones. -/
theorem EntryReaches.cast_ends {stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)}
    {d₁ d₂ : ℕ} {c₁ c₁' c₂ c₂' : EntryCfg}
    (h : EntryReaches stepFn d₁ c₁ c₂)
    (heq : checkEntryEnds d₁ d₂ c₁ c₁' c₂ c₂' = true) :
    EntryReaches stepFn d₂ c₁' c₂' := by
  unfold checkEntryEnds at heq
  simp only [Bool.and_eq_true] at heq
  have hd : d₁ = d₂ := Nat.eq_of_beq_eq_true heq.1.1
  have hc1 : c₁ = c₁' := eq_of_beq heq.1.2
  have hc2 : c₂ = c₂' := eq_of_beq heq.2
  subst hd; subst hc1; subst hc2
  exact h

/-- Soundness of `EntryReaches`: translates any `EntryReaches` derivation into `ReachesIn M`. -/
theorem EntryReaches.sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {wordOf : ℕ → List Γ}
    {stepFn : ℕ → Bool → List Run → List Run → Option (ℕ × EntryCfg)}
    (hs : StepFnSound M qOf wordOf stepFn) {dt : ℕ} {c₁ c₂ : EntryCfg}
    (h : EntryReaches stepFn dt c₁ c₂) :
    ReachesIn M dt (evalEntryCfg qOf wordOf c₁) (evalEntryCfg qOf wordOf c₂) := by
  induction h with
  | refl c => exact ReachesIn.zero M _
  | @chunk fuel d c c' hc =>
    unfold checkRunExact at hc
    rcases hr : runExact stepFn fuel 0 c with _ | ⟨dOut, cOut⟩
    · simp [hr] at hc
    · rw [hr] at hc
      simp only [Bool.and_eq_true] at hc
      have hd : dOut = d := Nat.eq_of_beq_eq_true hc.1
      have hcEq : cOut = c' := eq_of_beq hc.2
      subst hd
      subst hcEq
      simpa using (runExact_sound_aux hs fuel 0 c dOut cOut hr).2
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end WordSemantics

end BusyBeaver.WordRLE

end
