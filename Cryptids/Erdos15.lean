/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Machines

/-!
# Erdos15

The 15-state Turing machine `erdos_15` halts on the blank tape if and only if some power `2 ^ n`
with `n > 8` has no digit `2` in base `3`, i.e. if and only if Erdős's conjecture on the ternary
digits of powers of two is false.

## Provenance and Attribution

* Tristan Stérin and Damien Woods, *Hardness of busy beaver value BB(15)*
  (<https://arxiv.org/abs/2107.12475>, 2021): the 5-state, 4-symbol machine `powers_of_two_5_4`
  and its 15-state, 2-symbol compilation `powers_of_two_15_2`, published in
  <https://github.com/tcosmo/bbsim> (`machines/powers_of_two_15_2.txt`, commit `3f655ba2c73b`) and
  mirrored at <https://docs.bbchallenge.org/other/powers_of_two_15_2.txt>. The file is kept
  verbatim in `baselines/sources/erdos_15_sterin_woods.txt`; `verify.py` re-derives
  `baselines/tables/erdos_15.txt` from it and checks that they match: the start state `mul2_G_sim`
  becomes `0`, the other states are numbered in order of appearance, and the blank symbol `b`
  becomes `0` and `a` becomes `1`. Their correctness proof is on paper; this file gives a Lean
  proof.

## Machine Layout

The machine simulates a 4-symbol machine whose symbols `0`, `1`, `2`, `#` are stored as cell
pairs `01`, `10`, `11`, `00`. Between two passes the tape reads, from left to right,
`[counter] # d₀ d₁ … dₖ`, where `d₀ … dₖ` are the base-3 digits of `2 ^ n`, least significant
first, and the counter cell holds `#`, `0`, `1` or `2` when `0`, `1`, `2` or `3` of the powers
`2 ^ 0, …, 2 ^ n` have no digit `2`. One pass doubles the number (states `0`–`3`, `7`–`9`), scans
the digits from the most significant one for a `2` (states `4`–`6`), returns to the first digit
(states `10`–`12`) and, if no `2` was found, increments the counter (states `13`, `14`). Some
states are shared: rewinding also uses `8`, and incrementing the counter also uses `8`, `9` and
`12`. The machine halts at the fourth power without a digit `2`; the first three are `2 ^ 0`,
`2 ^ 2` and `2 ^ 8`.
-/

@[expose] public section

namespace ConjectureMachines.Erdos15

open Turing (Dir)
open StateTransition

/-- 15-state Erdős powers-of-two machine (`erdos_15`, Stérin & Woods 2021). -/
abbrev erdos15 : Machine 15 2 := Machines.erdos15

/-! ## Base-3 Doubling -/

/-- Doubles a base-3 digit list (least significant digit first) and adds the carry `c`. -/
def dbl : List ℕ → ℕ → List ℕ
  | [], c => if c = 0 then [] else [c]
  | d :: ds, c => (2 * d + c) % 3 :: dbl ds ((2 * d + c) / 3)

theorem dbl_lt (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (c : ℕ) (hc : c ≤ 1) :
    ∀ d ∈ dbl ds c, d < 3 := by
  induction ds generalizing c with
  | nil =>
    intro d hd
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · simp [dbl] at hd
    · simp [dbl] at hd; omega
  | cons x xs ih =>
    intro d hd
    have hx := hds x (by simp)
    simp only [dbl, List.mem_cons] at hd
    rcases hd with rfl | hd
    · omega
    · exact ih (fun y hy => hds y (List.mem_cons_of_mem x hy)) _ (by omega) d hd

/-- The base-3 digits of `2 ^ n`, computed by repeated doubling. -/
def pw : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => dbl (pw n) 0

theorem pw_lt (n : ℕ) : ∀ d ∈ pw n, d < 3 := by
  induction n with
  | zero => simp [pw]
  | succ n ih => exact dbl_lt (pw n) ih 0 (by omega)

/-- The number of `k ≤ n` such that `2 ^ k` has no digit `2` in base `3`. -/
def cnt : ℕ → ℕ
  | 0 => 1
  | n + 1 => cnt n + if 2 ∈ pw (n + 1) then 0 else 1

theorem cnt_succ_of_mem {n : ℕ} (h : 2 ∈ pw (n + 1)) : cnt (n + 1) = cnt n := by
  simp [cnt, h]

theorem cnt_succ_of_not_mem {n : ℕ} (h : 2 ∉ pw (n + 1)) : cnt (n + 1) = cnt n + 1 := by
  simp [cnt, h]

/-- `2 ^ 0 = 1`, `2 ^ 2 = 11₃` and `2 ^ 8 = 100111₃` are the only powers `2 ^ k` with `k ≤ 8`
without a digit `2`. -/
theorem cnt_eight : cnt 8 = 3 := by decide

/-! ## Tape Encoding -/

/-- Left cell of the pair encoding the digit `d` (`0 ↦ 01`, `1 ↦ 10`, `2 ↦ 11`). -/
def hi : ℕ → Fin 2
  | 0 => 0
  | _ => 1

/-- Right cell of the pair encoding the digit `d`. -/
def lo : ℕ → Fin 2
  | 1 => 0
  | _ => 1

@[simp] theorem hi_zero : hi 0 = 0 := rfl
@[simp] theorem hi_one : hi 1 = 1 := rfl
@[simp] theorem hi_two : hi 2 = 1 := rfl
@[simp] theorem lo_zero : lo 0 = 1 := rfl
@[simp] theorem lo_one : lo 1 = 0 := rfl
@[simp] theorem lo_two : lo 2 = 1 := rfl

/-- The cells of a digit list, read from left to right. -/
def encR : List ℕ → List (Fin 2)
  | [] => []
  | d :: ds => hi d :: lo d :: encR ds

/-- The cells of a digit list, read from right to left. -/
def encL : List ℕ → List (Fin 2)
  | [] => []
  | d :: ds => encL ds ++ [lo d, hi d]

/-- Left cell of the counter pair (`0 ↦ 00`, `1 ↦ 01`, `2 ↦ 10`, `3 ↦ 11`). -/
def chi : ℕ → Fin 2
  | 0 => 0
  | 1 => 0
  | _ => 1

/-- Right cell of the counter pair. -/
def clo : ℕ → Fin 2
  | 1 => 1
  | 3 => 1
  | _ => 0

def B0 : ListBlank (Fin 2) := ListBlank.mk []

theorem B0_cons_zero : B0.cons 0 = B0 :=
  Quot.sound (Or.inr ⟨1, rfl⟩)

/-- Head on the first cell of `L`. -/
def Tape.mkL (L R : ListBlank (Fin 2)) : Tape (Fin 2) :=
  ⟨L.head, L.tail, R⟩

@[simp]
theorem Tape.mkL_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mkL (L.cons a) R = ⟨a, L, R⟩ := by
  simp [Tape.mkL]

@[simp]
theorem Tape.mk'_cons (a : Fin 2) (L R : ListBlank (Fin 2)) :
    Tape.mk' L (R.cons a) = ⟨a, L, R⟩ := by
  simp [Tape.mk']

@[simp]
theorem Tape.mk'_B0 (L : ListBlank (Fin 2)) : Tape.mk' L B0 = ⟨0, L, B0⟩ :=
  rfl

/-- The cells left of the first digit: the `#` pair, then the counter pair. -/
def LH (c : ℕ) : ListBlank (Fin 2) :=
  ListBlank.append [0, 0, clo c, chi c] B0

/-- Start of the pass that doubles `2 ^ n`, with counter `c`. -/
def stageCfg (c n : ℕ) : Cfg 15 2 :=
  ⟨1, Tape.mk' (LH c) (ListBlank.append (encR (pw n)) B0)⟩

/-! ## Step Infrastructure -/

def nSteps (M : Machine 15 2) (n : ℕ) : Cfg 15 2 → Option (Cfg 15 2) :=
  Nat.rec (motive := fun _ => Cfg 15 2 → Option (Cfg 15 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero (M : Machine 15 2) (c : Cfg 15 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ (M : Machine 15 2) (n : ℕ) (c : Cfg 15 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {M : Machine 15 2} {n : ℕ} {c c' : Cfg 15 2}
    (h : nSteps M n c = some c') : Reaches (step M) c c' := by
  induction n generalizing c with
  | zero =>
    injection h with h'
    subst h'
    exact Relation.ReflTransGen.refl
  | succ n ih =>
    simp only [nSteps, Option.bind_eq_some_iff] at h
    obtain ⟨c₁, hstep, hrest⟩ := h
    exact Relation.ReflTransGen.head hstep (ih hrest)

theorem nSteps_add {M : Machine 15 2} (m n : ℕ) (c : Cfg 15 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    rw [Nat.succ_add, nSteps, nSteps]
    cases step M c <;> simp [ih]

theorem nSteps_bind_eq {M : Machine 15 2} {m n : ℕ} {c c₁ c₂ : Cfg 15 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem step_one {M : Machine 15 2} {c c₁ : Cfg 15 2} (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps, h]; rfl

theorem reaches_imp_nSteps {M : Machine 15 2} {a b : Cfg 15 2}
    (h : Reaches (step M) a b) : ∃ k, nSteps M k a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, nSteps_bind_eq hk (step_one hstep)⟩

theorem nSteps_eq_none_of_step_none {M : Machine 15 2} {k : ℕ} (s : ℕ) {a b : Cfg 15 2}
    (hk : nSteps M k a = some b) (hnone : step M b = none) (hks : k < s) :
    nSteps M s a = none := by
  have hs : s = k + ((s - k - 1) + 1) := by omega
  rw [hs, nSteps_add, hk, Option.bind_some, nSteps_succ, hnone, Option.bind_none]

/-! ## Transition Table -/

theorem stepR {q q' : Fin 15} {a b : Fin 2} (h : erdos15.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step erdos15 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem stepL {q q' : Fin 15} {a b : Fin 2} (h : erdos15.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step erdos15 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem s0_0 (L R) : step erdos15 ⟨0, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s0_1 (L R) : step erdos15 ⟨0, ⟨1, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s1_0 (L R) : step erdos15 ⟨1, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem s1_1 (L R) : step erdos15 ⟨1, ⟨1, L, R⟩⟩ = some ⟨2, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s2_0 (L R) : step erdos15 ⟨2, ⟨0, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s2_1 (L R) : step erdos15 ⟨2, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem s3_0 (L R) : step erdos15 ⟨3, ⟨0, L, R⟩⟩ = some ⟨5, Tape.mkL L (R.cons 0)⟩ := stepL rfl L R
theorem s3_1 (L R) : step erdos15 ⟨3, ⟨1, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s4_0 (L R) : step erdos15 ⟨4, ⟨0, L, R⟩⟩ = some ⟨6, Tape.mkL L (R.cons 0)⟩ := stepL rfl L R
theorem s4_1 (L R) : step erdos15 ⟨4, ⟨1, L, R⟩⟩ = some ⟨5, Tape.mkL L (R.cons 1)⟩ := stepL rfl L R
theorem s5_0 (L R) : step erdos15 ⟨5, ⟨0, L, R⟩⟩ = some ⟨4, Tape.mkL L (R.cons 0)⟩ := stepL rfl L R
theorem s5_1 (L R) : step erdos15 ⟨5, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem s6_0 (L R) : step erdos15 ⟨6, ⟨0, L, R⟩⟩ = some ⟨13, Tape.mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem s6_1 (L R) : step erdos15 ⟨6, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mkL L (R.cons 1)⟩ := stepL rfl L R
theorem s7_0 (L R) : step erdos15 ⟨7, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mkL L (R.cons 1)⟩ := stepL rfl L R
theorem s7_1 (L R) : step erdos15 ⟨7, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem s8_0 (L R) : step erdos15 ⟨8, ⟨0, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem s8_1 (L R) : step erdos15 ⟨8, ⟨1, L, R⟩⟩ = some ⟨1, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem s9_0 (L R) : step erdos15 ⟨9, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem s9_1 (L R) : step erdos15 ⟨9, ⟨1, L, R⟩⟩ = some ⟨7, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem s10_0 (L R) : step erdos15 ⟨10, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem s10_1 (L R) : step erdos15 ⟨10, ⟨1, L, R⟩⟩ = some ⟨11, Tape.mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem s11_0 (L R) : step erdos15 ⟨11, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem s11_1 (L R) : step erdos15 ⟨11, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem s12_0 (L R) : step erdos15 ⟨12, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem s12_1 (L R) : step erdos15 ⟨12, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mkL L (R.cons 1)⟩ :=
  stepL rfl L R
theorem s13_0 (L R) : step erdos15 ⟨13, ⟨0, L, R⟩⟩ = some ⟨12, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem s13_1 (L R) : step erdos15 ⟨13, ⟨1, L, R⟩⟩ = some ⟨14, Tape.mkL L (R.cons 0)⟩ :=
  stepL rfl L R
theorem s14_0 (L R) : step erdos15 ⟨14, ⟨0, L, R⟩⟩ = some ⟨9, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R

theorem s14_1 (L R : ListBlank (Fin 2)) : step erdos15 ⟨14, ⟨1, L, R⟩⟩ = none := rfl

/-- Runs the machine through a fixed sequence of steps on a concrete tape. -/
local macro "tm_run" : tactic => `(tactic| simp only [nSteps_succ, nSteps_zero, Option.bind_some,
  s0_0, s0_1, s1_0, s1_1, s2_0, s2_1, s3_0, s3_1, s4_0, s4_1, s5_0, s5_1, s6_0, s6_1, s7_0,
  s7_1, s8_0, s8_1, s9_0, s9_1, s10_0, s10_1, s11_0, s11_1, s12_0, s12_1, s13_0, s13_1, s14_0,
  Tape.mk'_cons, Tape.mkL_cons, Tape.mk'_B0, ListBlank.append, hi_zero, hi_one, hi_two, lo_zero,
  lo_one, lo_two])

/-! ## Doubling Pass (States `0`–`3`, `7`–`9`) -/

/-- The doubling state for carry `c`: `mul2_F` (`1`) for carry `0`, `mul2_G` (`0`) for carry `1`. -/
def st : ℕ → Fin 15
  | 0 => 1
  | _ => 0

theorem digit_step (d c : ℕ) (hd : d < 3) (hc : c ≤ 1) (L R : ListBlank (Fin 2)) :
    ∃ s, nSteps erdos15 s ⟨st c, ⟨hi d, L, R.cons (lo d)⟩⟩ =
      some ⟨st ((2 * d + c) / 3),
        Tape.mk' (ListBlank.append [lo ((2 * d + c) % 3), hi ((2 * d + c) % 3)] L) R⟩ := by
  rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;>
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl <;>
    simp only [st, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv]
  · exact ⟨2, by tm_run⟩
  · exact ⟨2, by tm_run⟩
  · exact ⟨2, by tm_run⟩
  · exact ⟨4, by tm_run⟩
  · exact ⟨2, by tm_run⟩
  · exact ⟨2, by tm_run⟩

theorem blank_step (L : ListBlank (Fin 2)) :
    nSteps erdos15 3 ⟨1, Tape.mk' L B0⟩ = some ⟨4, Tape.mkL L B0⟩ := by
  tm_run
  rw [B0_cons_zero, B0_cons_zero]

/-- One pass doubles the digit list `ds` with carry `c`; it ends in state `4` on the right cell
of the most significant digit. -/
theorem mul2_pass (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (c : ℕ) (hc : c ≤ 1)
    (L : ListBlank (Fin 2)) :
    ∃ s, nSteps erdos15 s ⟨st c, Tape.mk' L (ListBlank.append (encR ds) B0)⟩ =
      some ⟨4, Tape.mkL (ListBlank.append (encL (dbl ds c)) L) B0⟩ := by
  induction ds generalizing c L with
  | nil =>
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · exact ⟨3, blank_step L⟩
    · refine ⟨2 + 3, nSteps_bind_eq (c₁ := ⟨1, Tape.mk' ((L.cons 1).cons 0) B0⟩) ?_ ?_⟩
      · simp only [st, encR, ListBlank.append]; tm_run
      · exact blank_step _
  | cons d ds ih =>
    have hd := hds d (by simp)
    obtain ⟨s₁, hs₁⟩ := digit_step d c hd hc L (ListBlank.append (encR ds) B0)
    obtain ⟨s₂, hs₂⟩ := ih (fun x hx => hds x (by simp [hx])) ((2 * d + c) / 3) (by omega)
      (ListBlank.append [lo ((2 * d + c) % 3), hi ((2 * d + c) % 3)] L)
    have e : ListBlank.append (encL (dbl (d :: ds) c)) L =
        ListBlank.append (encL (dbl ds ((2 * d + c) / 3)))
          (ListBlank.append [lo ((2 * d + c) % 3), hi ((2 * d + c) % 3)] L) := by
      simp only [dbl, encL, ListBlank.append_assoc]
    rw [e]
    refine ⟨s₁ + s₂, nSteps_bind_eq ?_ hs₂⟩
    simpa only [encR, ListBlank.append, Tape.mk'_cons] using hs₁

/-! ## Search for a `2` (States `4`–`6`, `10`–`12`) -/

theorem pair_scan (q : Fin 15) (hq : q = 4 ∨ q = 10) (d : ℕ) (hd : d < 3)
    (L R : ListBlank (Fin 2)) :
    nSteps erdos15 2 ⟨q, ⟨lo d, L.cons (hi d), R⟩⟩ =
      some ⟨if q = 10 ∨ d = 2 then 10 else 4, Tape.mkL L ((R.cons (lo d)).cons (hi d))⟩ := by
  rcases hq with rfl | rfl <;> rcases (by omega : d = 0 ∨ d = 1 ∨ d = 2) with rfl | rfl | rfl <;>
    tm_run <;> simp

/-- Scanning left over `ds` from its most significant digit finds a `2` iff `2 ∈ ds`; after a
`2` the machine keeps moving left in the rewind states. -/
theorem find2_scan (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (L R : ListBlank (Fin 2)) :
    nSteps erdos15 (2 * ds.length) ⟨4, Tape.mkL (ListBlank.append (encL ds) L) R⟩ =
      some ⟨if 2 ∈ ds then 10 else 4, Tape.mkL L (ListBlank.append (encR ds) R)⟩ := by
  induction ds generalizing L with
  | nil => simp [encL, encR]
  | cons d ds ih =>
    have hd := hds d (by simp)
    have h₁ := ih (fun x hx => hds x (by simp [hx]))
      (ListBlank.append [lo d, hi d] L)
    rw [show 2 * (d :: ds).length = 2 * ds.length + 2 by rw [List.length_cons]; omega, encL,
      ListBlank.append_assoc, nSteps_add, h₁, Option.bind_some]
    have hq : (if 2 ∈ ds then (10 : Fin 15) else 4) = 4 ∨
        (if 2 ∈ ds then (10 : Fin 15) else 4) = 10 := by
      by_cases h : 2 ∈ ds <;> simp [h]
    simp only [ListBlank.append, Tape.mkL_cons]
    rw [pair_scan _ hq d hd]
    congr 2
    by_cases h₂ : 2 ∈ ds <;> by_cases hd₂ : d = 2 <;> simp [h₂, hd₂, eq_comm]

/-! ## The `#` Cell and the Counter -/

theorem hash_rewind (c : ℕ) (R : ListBlank (Fin 2)) :
    nSteps erdos15 3 ⟨10, Tape.mkL (LH c) R⟩ = some ⟨1, Tape.mk' (LH c) R⟩ := by
  simp only [LH, ListBlank.append, Tape.mkL_cons]
  tm_run

theorem hash_find (c : ℕ) (R : ListBlank (Fin 2)) :
    nSteps erdos15 2 ⟨4, Tape.mkL (LH c) R⟩ =
      some ⟨13, Tape.mkL (ListBlank.append [clo c, chi c] B0) ((R.cons 0).cons 0)⟩ := by
  simp only [LH, ListBlank.append, Tape.mkL_cons]
  tm_run

theorem counter_inc (c : ℕ) (hc : c < 3) (R : ListBlank (Fin 2)) :
    ∃ s, nSteps erdos15 s
        ⟨13, Tape.mkL (ListBlank.append [clo c, chi c] B0) ((R.cons 0).cons 0)⟩ =
      some ⟨1, Tape.mk' (LH (c + 1)) R⟩ := by
  rcases (by omega : c = 0 ∨ c = 1 ∨ c = 2) with rfl | rfl | rfl
  · exact ⟨3, by simp only [LH, clo, chi, ListBlank.append, Tape.mkL_cons]; tm_run⟩
  · exact ⟨5, by simp only [LH, clo, chi, ListBlank.append, Tape.mkL_cons]; tm_run⟩
  · exact ⟨3, by simp only [LH, clo, chi, ListBlank.append, Tape.mkL_cons]; tm_run⟩

theorem counter_halt (R : ListBlank (Fin 2)) :
    ∃ cfg, nSteps erdos15 1
        ⟨13, Tape.mkL (ListBlank.append [clo 3, chi 3] B0) ((R.cons 0).cons 0)⟩ = some cfg ∧
      step erdos15 cfg = none := by
  refine ⟨⟨14, ⟨1, B0, (((R.cons 0).cons 0).cons 0)⟩⟩, ?_, s14_1 _ _⟩
  simp only [clo, chi, ListBlank.append, Tape.mkL_cons]
  tm_run

/-! ## Stages -/

theorem stage_scan (c n : ℕ) :
    ∃ s, nSteps erdos15 s (stageCfg c n) = some
      ⟨if 2 ∈ pw (n + 1) then 10 else 4,
        Tape.mkL (LH c) (ListBlank.append (encR (pw (n + 1))) B0)⟩ := by
  obtain ⟨s₁, hs₁⟩ := mul2_pass (pw n) (pw_lt n) 0 (by omega) (LH c)
  have h₂ := find2_scan (pw (n + 1)) (pw_lt (n + 1)) (LH c) B0
  exact ⟨s₁ + 2 * (pw (n + 1)).length, nSteps_bind_eq hs₁ h₂⟩

theorem stage_keep (c n : ℕ) (h : 2 ∈ pw (n + 1)) :
    ∃ s, 1 ≤ s ∧ nSteps erdos15 s (stageCfg c n) = some (stageCfg c (n + 1)) := by
  obtain ⟨s₁, hs₁⟩ := stage_scan c n
  simp only [h, ↓reduceIte] at hs₁
  exact ⟨s₁ + 3, by omega, nSteps_bind_eq hs₁ (hash_rewind c _)⟩

theorem stage_inc (c n : ℕ) (hc : c < 3) (h : 2 ∉ pw (n + 1)) :
    ∃ s, 1 ≤ s ∧ nSteps erdos15 s (stageCfg c n) = some (stageCfg (c + 1) (n + 1)) := by
  obtain ⟨s₁, hs₁⟩ := stage_scan c n
  simp only [h, ↓reduceIte] at hs₁
  obtain ⟨s₃, hs₃⟩ := counter_inc c hc (ListBlank.append (encR (pw (n + 1))) B0)
  exact ⟨s₁ + 2 + s₃, by omega,
    nSteps_bind_eq (nSteps_bind_eq hs₁ (hash_find c _)) hs₃⟩

theorem stage_halt (n : ℕ) (h : 2 ∉ pw (n + 1)) :
    ∃ s cfg, nSteps erdos15 s (stageCfg 3 n) = some cfg ∧ step erdos15 cfg = none := by
  obtain ⟨s₁, hs₁⟩ := stage_scan 3 n
  simp only [h, ↓reduceIte] at hs₁
  obtain ⟨cfg, hcfg, hnone⟩ := counter_halt (ListBlank.append (encR (pw (n + 1))) B0)
  exact ⟨s₁ + 2 + 1, cfg, nSteps_bind_eq (nSteps_bind_eq hs₁ (hash_find 3 _)) hcfg, hnone⟩

theorem init_eq : (init : Cfg 15 2) = ⟨st 1, Tape.mk' (LH 0) (ListBlank.append (encR []) B0)⟩ := by
  have : LH 0 = ListBlank.mk [] := Quot.sound (Or.inr ⟨4, rfl⟩)
  rw [this]
  rfl

theorem boot : ∃ s, nSteps erdos15 s init = some (stageCfg 1 0) := by
  obtain ⟨s₁, hs₁⟩ := mul2_pass [] (by simp) 1 (by omega) (LH 0)
  have h₂ := find2_scan (dbl [] 1) (by simp [dbl]) (LH 0) B0
  simp only [show 2 ∉ dbl [] 1 by simp [dbl], ↓reduceIte] at h₂
  obtain ⟨s₃, hs₃⟩ := counter_inc 0 (by omega) (ListBlank.append (encR (dbl [] 1)) B0)
  rw [init_eq]
  exact ⟨s₁ + _ + 2 + s₃,
    nSteps_bind_eq (nSteps_bind_eq (nSteps_bind_eq hs₁ h₂) (hash_find 0 _)) hs₃⟩

/-! ## Counting Powers Without a Digit `2` -/

theorem reach (n : ℕ) (hn : cnt n ≤ 3) :
    ∃ s, n ≤ s ∧ nSteps erdos15 s init = some (stageCfg (cnt n) n) := by
  induction n with
  | zero =>
    obtain ⟨s, hs⟩ := boot
    exact ⟨s, Nat.zero_le s, hs⟩
  | succ n ih =>
    by_cases h : 2 ∈ pw (n + 1)
    · rw [cnt_succ_of_mem h] at hn ⊢
      obtain ⟨s₁, hs₁n, hs₁⟩ := ih hn
      obtain ⟨s₂, hs₂1, hs₂⟩ := stage_keep (cnt n) n h
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩
    · rw [cnt_succ_of_not_mem h] at hn ⊢
      obtain ⟨s₁, hs₁n, hs₁⟩ := ih (by omega)
      obtain ⟨s₂, hs₂1, hs₂⟩ := stage_inc (cnt n) n (by omega) h
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩

theorem halt_of (n : ℕ) (h3 : cnt n = 3) (h : 2 ∉ pw (n + 1)) :
    ∃ s cfg, nSteps erdos15 s init = some cfg ∧ step erdos15 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := reach n (by omega)
  rw [h3] at hs₁
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt n h
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem cnt_stays (K : ℕ) (hK : 8 ≤ K) (hall : ∀ m, 8 < m → m ≤ K → 2 ∈ pw m) : cnt K = 3 := by
  induction K, hK using Nat.le_induction with
  | base => exact cnt_eight
  | succ K hK ih =>
    rw [cnt_succ_of_mem (hall (K + 1) (by omega) le_rfl)]
    exact ih fun m hm hmK => hall m hm (by omega)

theorem first_free (n : ℕ) (h8 : 8 < n) (h : 2 ∉ pw n) :
    ∃ m, cnt m = 3 ∧ 2 ∉ pw (m + 1) := by
  have key : ∀ j, 8 ≤ j → cnt j = 3 ∨ ∃ m, cnt m = 3 ∧ 2 ∉ pw (m + 1) := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => exact Or.inl cnt_eight
    | succ j _ ih =>
      rcases ih with h3 | hm
      · by_cases hj2 : 2 ∈ pw (j + 1)
        · exact Or.inl (by rw [cnt_succ_of_mem hj2, h3])
        · exact Or.inr ⟨j, h3, hj2⟩
      · exact Or.inr hm
  rcases key (n - 1) (by omega) with h3 | hm
  · exact ⟨n - 1, h3, by rwa [Nat.sub_add_cancel (by omega)]⟩
  · exact hm

theorem free_or_none (K : ℕ) :
    (∃ m, 8 < m ∧ m ≤ K ∧ 2 ∉ pw m) ∨ (∀ m, 8 < m → m ≤ K → 2 ∈ pw m) := by
  induction K with
  | zero => exact Or.inr fun m hm hmK => absurd hmK (by omega)
  | succ K ih =>
    rcases ih with ⟨m, hm, hmK, hfree⟩ | hall
    · exact Or.inl ⟨m, hm, by omega, hfree⟩
    · by_cases h : 2 ∈ pw (K + 1)
      · refine Or.inr fun m hm hmK => ?_
        rcases (by omega : m ≤ K ∨ m = K + 1) with hmK' | rfl
        · exact hall m hm hmK'
        · exact h
      · by_cases hK : 8 < K + 1
        · exact Or.inl ⟨K + 1, hK, le_rfl, h⟩
        · exact Or.inr fun m hm hmK => absurd hm (by omega)

/-! ## Halting Equivalence -/

/-- The 15-state machine `erdos15` (`erdos_15`) halts on the blank tape if and only if some
power `2 ^ n` with `n > 8` has no digit `2` in base `3`, with the digits computed by `pw`. -/
theorem halts_erdos15_iff_exists_free :
    ConjectureMachines.Halts erdos15 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n := by
  unfold ConjectureMachines.Halts
  constructor
  · intro hdom
    rw [Part.dom_iff_mem] at hdom
    obtain ⟨b, hb⟩ := hdom
    rw [mem_eval'] at hb
    obtain ⟨hreach, hnone⟩ := hb
    obtain ⟨k, hk⟩ := reaches_imp_nSteps hreach
    rcases free_or_none (k + 9) with ⟨m, hm, -, hfree⟩ | hall
    · exact ⟨m, hm, hfree⟩
    · have h3 := cnt_stays (k + 9) (by omega) hall
      obtain ⟨s, hks, hs⟩ := reach (k + 9) (by omega)
      rw [nSteps_eq_none_of_step_none s hk hnone (by omega)] at hs
      cases hs
  · rintro ⟨n, h8, hfree⟩
    obtain ⟨m, h3, hm⟩ := first_free n h8 hfree
    obtain ⟨s, cfg, hs, hnone⟩ := halt_of m h3 hm
    rw [Part.dom_iff_mem]
    exact ⟨cfg, mem_eval'.mpr ⟨nSteps_reaches hs, hnone⟩⟩

end ConjectureMachines.Erdos15
