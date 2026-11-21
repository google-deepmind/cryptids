/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic

/-!
# Accelerated reductions (`BusyBeaver.Accelerated`)

Direct-import-only shared bridge library (`import BusyBeaver.Accelerated`; not re-exported by
`BusyBeaver.Import`) formalizing explicit, cost-certified macro reductions and bridges to `IsHalt`
and `IsNotHalt`, including `IsQueriedAcceleration`, which places zero syntactic or symbol
restrictions on `encode`:

0. **`IsAcceleration M start encode next cost`**: soundness-only acceleration (blank-tape entry,
   counted defined steps, halting undefined steps) with bridges `isHalt_iff`, `isHalt`, and
   `isNotHalt`.
1. **`IsAcceleratedReduction M start encode next cost`** (any state space `S`): `IsAcceleration`
   plus `cost_unbounded` over the domain of `next`, with bridges `isHalt_iff`, `isHalt`, and
   `isNotHalt`.
1Q. **`IsQueriedAcceleration M start encode stateOf cellAt next cost`**: `IsAcceleratedReduction`
   equipped with a kernel-verified random-access configuration oracle `(stateOf, cellAt)`
   (`stateOf s = (encode s).q`, `cellAt s i = (encode s).tape.nth i`), pinning the entire infinite
   tape of `encode s` while running in compressed time at arbitrary scale, plus `Tape.nth` /
   `ListBlank.nth` oracle soundness lemmas.
2. **`IsFrameAccelerated M W modes start next cost`**: forced frame-stack encoding `encodeFrame`.
3. **`CollatzMap k` / `IsCollatzLike M`**: guarded integer-affine rule tables on `≤ 4` counters.
-/

@[expose] public section

open Mathlib Relation Nat Turing

namespace BusyBeaver

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Extending a macro trajectory by one defined step. -/
theorem CollatzReachesStar.snoc {S : Type*} {next : S → Option S} {s₀ s s' : S}
    (h : CollatzReachesStar next s₀ s) (hs : next s = some s') :
    CollatzReachesStar next s₀ s' := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  unfold CollatzReachesIn at *
  rw [Function.iterate_succ_apply', hn]
  simpa using hs


/-! ## Layer 0: soundness-only accelerations (`IsAcceleration`) -/

/--
`IsAcceleration M start encode next cost`:
1. `M` reaches `encode start` from the blank tape;
2. every defined macro step `next s = some s'` is simulated by exactly `cost s > 0` machine
   steps from `encode s` to `encode s'`;
3. every undefined macro step `next s = none` leads `M` from `encode s` to a halting
   configuration.
-/
structure IsAcceleration (M : Machine Γ Λ) {S : Type*}
    (start : S) (encode : S → Cfg Γ Λ) (next : S → Option S) (cost : S → ℕ) : Prop where
  init_reaches : ReachesStar M (init []) (encode start)
  step_some : ∀ s s', next s = some s' →
    0 < cost s ∧ ReachesIn M (cost s) (encode s) (encode s')
  step_none : ∀ s, next s = none →
    ∃ cfg', ReachesStar M (encode s) cfg' ∧ (step M cfg').isNone

namespace IsAcceleration

variable {M : Machine Γ Λ} {S : Type*} {start : S} {encode : S → Cfg Γ Λ}
  {next : S → Option S} {cost : S → ℕ}

theorem toValid (h : IsAcceleration M start encode next cost) :
    IsValidAcceleration M start encode next where
  init_reaches := h.init_reaches
  step_some s s' hs := ⟨cost s, (h.step_some s s' hs).1, (h.step_some s s' hs).2⟩
  step_none := h.step_none

theorem isHalt_iff (h : IsAcceleration M start encode next cost) :
    IsHalt M ↔ CollatzHalts next start :=
  h.toValid.isHalt_iff

theorem init_reaches_of_reachesStar (h : IsAcceleration M start encode next cost)
    {s : S} (hs : CollatzReachesStar next start s) :
    ReachesStar M (init []) (encode s) := by
  obtain ⟨n, hn⟩ := hs
  have go : ∀ m s₁, CollatzReachesIn next m s₁ s → ReachesStar M (encode s₁) (encode s) := by
    intro m
    induction m with
    | zero =>
      intro s₁ hs₁
      unfold CollatzReachesIn at hs₁
      simp only [Function.iterate_zero_apply, Option.some.injEq] at hs₁
      subst hs₁
      exact ReachesStar.refl M (encode s₁)
    | succ m ih =>
      intro s₁ hs₁
      unfold CollatzReachesIn at hs₁
      rw [Function.iterate_succ_apply] at hs₁
      rcases hnext : next s₁ with _ | s'
      · have hnone : ∀ k, (Option.bind · next)^[k] none = none := by
          intro k; induction k with
          | zero => rfl
          | succ k ihk => rw [Function.iterate_succ_apply]; exact ihk
        change (Option.bind · next)^[m] (next s₁) = some s at hs₁
        rw [hnext, hnone] at hs₁
        cases hs₁
      · refine (h.toValid.step_some s₁ s' hnext).to_star.trans (ih s' ?_)
        unfold CollatzReachesIn
        simpa [hnext] using hs₁
  exact h.init_reaches.trans (go n start hn)

theorem isNotHalt (h : IsAcceleration M start encode next cost)
    (closed : ∀ s, CollatzReachesStar next start s → next s ≠ none) :
    IsNotHalt M := by
  refine IsNotHalt.of_reachesPlus_invariant
    (P := fun cfg => ∃ s, cfg = encode s ∧ CollatzReachesStar next start s)
    h.init_reaches ⟨start, rfl, CollatzReachesStar.refl next start⟩ ?_
  rintro cfg ⟨s, rfl, hs⟩
  rcases hnext : next s with _ | s'
  · exact absurd hnext (closed s hs)
  · exact ⟨encode s', h.toValid.step_some s s' hnext, s', rfl, hs.snoc hnext⟩

theorem isHalt (h : IsAcceleration M start encode next cost)
    (hhalt : CollatzHalts next start) :
    IsHalt M :=
  h.isHalt_iff.mpr hhalt

end IsAcceleration

/-! ## Layer 1: accelerated reductions over an arbitrary state space -/

/--
`IsAcceleratedReduction M start encode next cost`:
1. `M` reaches `encode start` from the blank tape;
2. every defined macro step `next s = some s'` is simulated by exactly `cost s > 0` machine
   steps from `encode s` to `encode s'`;
3. every undefined macro step `next s = none` leads `M` from `encode s` to a halting
   configuration;
4. the cost is unbounded over the domain of `next`.
-/
structure IsAcceleratedReduction (M : Machine Γ Λ) {S : Type*}
    (start : S) (encode : S → Cfg Γ Λ) (next : S → Option S) (cost : S → ℕ) : Prop where
  init_reaches : ReachesStar M (init []) (encode start)
  step_some : ∀ s s', next s = some s' →
    0 < cost s ∧ ReachesIn M (cost s) (encode s) (encode s')
  step_none : ∀ s, next s = none →
    ∃ cfg', ReachesStar M (encode s) cfg' ∧ (step M cfg').isNone
  cost_unbounded : ∀ C : ℕ, ∃ s s', next s = some s' ∧ C ≤ cost s

namespace IsAcceleratedReduction

variable {M : Machine Γ Λ} {S : Type*} {start : S} {encode : S → Cfg Γ Λ}
  {next : S → Option S} {cost : S → ℕ}

theorem toAcceleration (h : IsAcceleratedReduction M start encode next cost) :
    IsAcceleration M start encode next cost where
  init_reaches := h.init_reaches
  step_some := h.step_some
  step_none := h.step_none

theorem toValid (h : IsAcceleratedReduction M start encode next cost) :
    IsValidAcceleration M start encode next where
  init_reaches := h.init_reaches
  step_some s s' hs := ⟨cost s, (h.step_some s s' hs).1, (h.step_some s s' hs).2⟩
  step_none := h.step_none

theorem isHalt_iff (h : IsAcceleratedReduction M start encode next cost) :
    IsHalt M ↔ CollatzHalts next start :=
  h.toValid.isHalt_iff

theorem init_reaches_of_reachesStar (h : IsAcceleratedReduction M start encode next cost)
    {s : S} (hs : CollatzReachesStar next start s) :
    ReachesStar M (init []) (encode s) :=
  h.toAcceleration.init_reaches_of_reachesStar hs

end IsAcceleratedReduction

/-- **The bridge.** If the macro system never halts on its reachable states, `M` does not halt. -/
theorem IsAcceleratedReduction.isNotHalt {M : Machine Γ Λ} {S : Type*} {start : S}
    {encode : S → Cfg Γ Λ} {next : S → Option S} {cost : S → ℕ}
    (h : IsAcceleratedReduction M start encode next cost)
    (closed : ∀ s, CollatzReachesStar next start s → next s ≠ none) :
    IsNotHalt M :=
  h.toAcceleration.isNotHalt closed

/-- The halting direction of the bridge: a halting macro trajectory is a halting run of `M`. -/
theorem IsAcceleratedReduction.isHalt {M : Machine Γ Λ} {S : Type*} {start : S}
    {encode : S → Cfg Γ Λ} {next : S → Option S} {cost : S → ℕ}
    (h : IsAcceleratedReduction M start encode next cost)
    (hhalt : CollatzHalts next start) :
    IsHalt M :=
  h.isHalt_iff.mpr hhalt

/-! ## Layer 1Q: Structure-free runtime-observable acceleration (`encode` unrestricted) -/

/--
`IsQueriedAcceleration M start encode stateOf cellAt next cost`:
An `IsAcceleratedReduction` paired with a full random-access configuration oracle
`(stateOf : S → Option Λ, cellAt : S → ℤ → Γ)` certified equal to
`((encode s).q, (encode s).tape.nth)` for every state `s` and every integer cell coordinate `i : ℤ`.
Mathematically `(stateOf s, cellAt s)` uniquely determines `encode s` across the entire infinite
tape, while answering single-cell queries in compressed time under the runtime stopwatch.
Imposes zero syntactic or symbol restrictions on `encode`.
-/
structure IsQueriedAcceleration (M : Machine Γ Λ) {S : Type*}
    (start : S) (encode : S → Cfg Γ Λ)
    (stateOf : S → Option Λ) (cellAt : S → ℤ → Γ)
    (next : S → Option S) (cost : S → ℕ) : Prop where
  accelerated : IsAcceleratedReduction M start encode next cost
  state_sound : ∀ s : S, stateOf s = (encode s).q
  cell_sound : ∀ s : S, ∀ i : ℤ, cellAt s i = (encode s).tape.nth i

namespace IsQueriedAcceleration

variable {M : Machine Γ Λ} {S : Type*} {start : S} {encode : S → Cfg Γ Λ}
  {stateOf : S → Option Λ} {cellAt : S → ℤ → Γ} {next : S → Option S} {cost : S → ℕ}

theorem isHalt_iff (h : IsQueriedAcceleration M start encode stateOf cellAt next cost) :
    IsHalt M ↔ CollatzHalts next start :=
  h.accelerated.isHalt_iff

theorem isNotHalt (h : IsQueriedAcceleration M start encode stateOf cellAt next cost)
    (closed : ∀ s, CollatzReachesStar next start s → next s ≠ none) :
    IsNotHalt M :=
  h.accelerated.isNotHalt closed

theorem isHalt (h : IsQueriedAcceleration M start encode stateOf cellAt next cost)
    (hhalt : CollatzHalts next start) :
    IsHalt M :=
  h.accelerated.isHalt hhalt

end IsQueriedAcceleration


/-! ### Reusable `Tape.nth` & `ListBlank.nth` Soundness Lemmas for `IsQueriedAcceleration` -/

theorem tape_nth_zero {Γ : Type*} [Inhabited Γ] (h : Γ) (L R : ListBlank Γ) :
    (⟨h, L, R⟩ : Tape Γ).nth 0 = h :=
  rfl

theorem tape_nth_ofNat_succ {Γ : Type*} [Inhabited Γ] (h : Γ) (L R : ListBlank Γ) (n : ℕ) :
    (⟨h, L, R⟩ : Tape Γ).nth (Int.ofNat (n + 1)) = R.nth n :=
  rfl

theorem tape_nth_negSucc {Γ : Type*} [Inhabited Γ] (h : Γ) (L R : ListBlank Γ) (n : ℕ) :
    (⟨h, L, R⟩ : Tape Γ).nth (Int.negSucc n) = L.nth n :=
  rfl

theorem listBlank_nth_default {Γ : Type*} [Inhabited Γ] :
    ∀ n : ℕ, (default : ListBlank Γ).nth n = default
  | 0 => by simp [ListBlank.nth_zero, ListBlank.head_default]
  | n + 1 => by simp [ListBlank.nth_succ, ListBlank.tail_default, listBlank_nth_default n]

theorem listBlank_nth_cons_zero {Γ : Type*} [Inhabited Γ] (a : Γ) (lb : ListBlank Γ) :
    (ListBlank.cons a lb).nth 0 = a := by
  simp [ListBlank.nth_zero]

theorem listBlank_nth_cons_succ {Γ : Type*} [Inhabited Γ] (a : Γ) (lb : ListBlank Γ) (n : ℕ) :
    (ListBlank.cons a lb).nth (n + 1) = lb.nth n := by
  simp [ListBlank.nth_succ]

theorem listBlank_nth_append_lt {Γ : Type*} [Inhabited Γ] :
    ∀ (u : List Γ) (lb : ListBlank Γ) (n : ℕ) (h : n < u.length),
      (ListBlank.append u lb).nth n = u[n]
  | [], _, _, h => absurd h (Nat.not_lt_zero _)
  | a :: u, lb, 0, _ => by simp [ListBlank.append, ListBlank.nth_zero]
  | a :: u, lb, n + 1, h => by
    simp only [ListBlank.append, ListBlank.nth_succ, ListBlank.tail_cons, List.getElem_cons_succ]
    exact listBlank_nth_append_lt u lb n (Nat.lt_of_succ_lt_succ h)

theorem listBlank_nth_append_ge {Γ : Type*} [Inhabited Γ] :
    ∀ (u : List Γ) (lb : ListBlank Γ) (n : ℕ) (_h : u.length ≤ n),
      (ListBlank.append u lb).nth n = lb.nth (n - u.length)
  | [], lb, n, _ => by simp [ListBlank.append]
  | a :: u, _, 0, h => absurd h (Nat.not_le_of_gt (Nat.succ_pos _))
  | a :: u, lb, n + 1, h => by
    simp only [ListBlank.append, ListBlank.nth_succ, ListBlank.tail_cons, List.length_cons,
      Nat.succ_sub_succ_eq_sub]
    exact listBlank_nth_append_ge u lb n (Nat.le_of_succ_le_succ h)

theorem listBlank_nth_replicate_lt {Γ : Type*} [Inhabited Γ] (k : ℕ) (a : Γ) (lb : ListBlank Γ)
    {n : ℕ} (hn : n < k) :
    (ListBlank.append (List.replicate k a) lb).nth n = a := by
  have hlen : n < (List.replicate k a).length := by simpa using hn
  rw [listBlank_nth_append_lt _ _ n hlen, List.getElem_replicate]

theorem listBlank_nth_replicate_ge {Γ : Type*} [Inhabited Γ] (k : ℕ) (a : Γ) (lb : ListBlank Γ)
    {n : ℕ} (hn : k ≤ n) :
    (ListBlank.append (List.replicate k a) lb).nth n = lb.nth (n - k) := by
  have hlen : (List.replicate k a).length ≤ n := by simpa using hn
  simpa using listBlank_nth_append_ge (List.replicate k a) lb n hlen

/-! ## Layer 2: the frame rung (word-block stacks, sweep transducers, odometers) -/

/-- A frame `(i, n)` denotes the word `W.words[i]` repeated `n` times. -/
abbrev Frame := ℕ × ℕ

/-- The declared word alphabet of a frame system. -/
structure FrameAlphabet (Γ : Type*) where
  words : List (List Γ)

namespace FrameAlphabet

def WellFormed (W : FrameAlphabet Γ) : Prop :=
  W.words.length ≤ 8 ∧ W.words.Nodup ∧
  ∀ w ∈ W.words, 0 < w.length ∧ w.length ≤ 6 ∧ w ≠ List.replicate w.length default

def word (W : FrameAlphabet Γ) (i : ℕ) : List Γ := W.words.getD i []

def frameSize (W : FrameAlphabet Γ) (f : Frame) : ℕ := f.2 * (W.word f.1).length

def encodeHalf (W : FrameAlphabet Γ) (fs : List Frame) : ListBlank Γ :=
  ListBlank.append (fs.flatMap fun f => (W.word f.1) ^ f.2) default

def facedSize (W : FrameAlphabet Γ) : List Frame → ℕ
  | [] => 0
  | [f] => W.frameSize f
  | f :: g :: rest =>
    if f.1 = g.1 then W.frameSize f + facedSize W (g :: rest) else W.frameSize f

end FrameAlphabet

structure FrameMode (Γ Λ : Type*) where
  state : Λ
  head : Γ
  pfxL : List Γ := []
  pfxR : List Γ := []

abbrev FrameState := ℕ × List Frame × List Frame

def encodeFrame (W : FrameAlphabet Γ) (modes : List (FrameMode Γ Λ)) (s : FrameState) :
    Cfg Γ Λ :=
  match modes[s.1]? with
  | some m => ⟨some m.state,
      ⟨m.head, ListBlank.append m.pfxL (W.encodeHalf s.2.1),
        ListBlank.append m.pfxR (W.encodeHalf s.2.2)⟩⟩
  | none => default

def facedFrameSize (M : Machine Γ Λ) (W : FrameAlphabet Γ) (modes : List (FrameMode Γ Λ))
    (s : FrameState) : ℕ :=
  match modes[s.1]? with
  | some m =>
    match M m.state m.head with
    | some (_, Stmt.write _ Dir.left) => m.pfxL.length + W.facedSize s.2.1
    | some (_, Stmt.write _ Dir.right) => m.pfxR.length + W.facedSize s.2.2
    | none => 0
  | none => 0

structure IsFrameAccelerated (M : Machine Γ Λ) (W : FrameAlphabet Γ)
    (modes : List (FrameMode Γ Λ)) (start : FrameState)
    (next : FrameState → Option FrameState) (cost : FrameState → ℕ) : Prop where
  wellFormed : W.WellFormed
  modes_le : modes.length ≤ 16
  accelerated : IsAcceleratedReduction M start (encodeFrame W modes) next cost
  faced : ∀ s s', next s = some s' → facedFrameSize M W modes s ≤ cost s

namespace IsFrameAccelerated

variable {M : Machine Γ Λ} {W : FrameAlphabet Γ} {modes : List (FrameMode Γ Λ)}
  {start : FrameState} {next : FrameState → Option FrameState} {cost : FrameState → ℕ}

theorem isHalt_iff (h : IsFrameAccelerated M W modes start next cost) :
    IsHalt M ↔ CollatzHalts next start :=
  h.accelerated.isHalt_iff

theorem isNotHalt (h : IsFrameAccelerated M W modes start next cost)
    (closed : ∀ s, CollatzReachesStar next start s → next s ≠ none) :
    IsNotHalt M :=
  h.accelerated.isNotHalt closed

end IsFrameAccelerated

/-! ## Layer 3: the Collatz rung (guarded integer-affine rule tables on `k` counters) -/

structure LinForm (k : ℕ) where
  const : ℤ
  coeffs : Fin k → ℤ

namespace LinForm

def eval {k : ℕ} (f : LinForm k) (x : Fin k → ℕ) : ℤ :=
  f.const + (List.ofFn fun i => f.coeffs i * (x i : ℤ)).sum

end LinForm

inductive Guard (k : ℕ)
  | nonneg (f : LinForm k)
  | congr (f : LinForm k) (m r : ℕ)
  | and (g₁ g₂ : Guard k)
  | true

namespace Guard

def eval {k : ℕ} : Guard k → (Fin k → ℕ) → Bool
  | .nonneg f, x => decide (0 ≤ f.eval x)
  | .congr f m r, x => decide (f.eval x % (m : ℤ) = (r : ℤ))
  | .and g₁ g₂, x => g₁.eval x && g₂.eval x
  | .true, _ => Bool.true

end Guard

structure Rule (k : ℕ) where
  guard : Guard k
  update : Fin k → LinForm k

namespace Rule

def apply {k : ℕ} (r : Rule k) (x : Fin k → ℕ) : Option (Fin k → ℕ) :=
  if r.guard.eval x && (List.ofFn fun i => decide (0 ≤ (r.update i).eval x)).all id then
    some fun i => ((r.update i).eval x).toNat
  else
    none

end Rule

structure CollatzMap (k : ℕ) where
  rules : List (Rule k)

namespace CollatzMap

def next {k : ℕ} (f : CollatzMap k) (x : Fin k → ℕ) : Option (Fin k → ℕ) :=
  f.rules.findSome? fun r => r.apply x

end CollatzMap

def IsCollatzLike (M : Machine Γ Λ) : Prop :=
  ∃ (k : ℕ) (f : CollatzMap k) (start : Fin k → ℕ) (encode : (Fin k → ℕ) → Cfg Γ Λ)
    (cost : (Fin k → ℕ) → ℕ),
    k ≤ 4 ∧ f.rules.length ≤ 16 ∧ IsAcceleratedReduction M start encode f.next cost

theorem IsCollatzLike.exists_isHalt_iff {M : Machine Γ Λ} (h : IsCollatzLike M) :
    ∃ (k : ℕ) (f : CollatzMap k) (start : Fin k → ℕ),
      k ≤ 4 ∧ f.rules.length ≤ 16 ∧ (IsHalt M ↔ CollatzHalts f.next start) := by
  obtain ⟨k, f, start, encode, cost, hk, hlen, hacc⟩ := h
  exact ⟨k, f, start, hk, hlen, hacc.isHalt_iff⟩

end BusyBeaver
