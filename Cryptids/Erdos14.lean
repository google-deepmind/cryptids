/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Erdos15

/-!
# Erdos14

The 14-state Turing machine `erdos_14` halts on the blank tape if and only if some power `2 ^ n`
with `n > 8` has no digit `2` in base `3`. So it halts if and only if the 15-state machine
`erdos_15` does (`candidate_equivalent`). Neither proof uses `Classical.choice`.

## Provenance and Attribution

Tristan Stérin announced the machine on the bbchallenge Discord in October 2026
(<https://discord.com/channels/960643023006490684/1561295445312151622/1562203343114473472>).
It is listed on the Cryptids page of the bbchallenge wiki
(<https://wiki.bbchallenge.org/w/index.php?title=Cryptids&oldid=9722>) as

```
1LB1RA_1LC1LB_0RD0RA_1LM0RE_1LF1RE_0LJ1LG_1RK0LH_1RI1LH_0LJ0RE_0RD1LJ_0LL1RK_1RN0LC_0LN---_0RK0LM
```

and `artifacts/erdos_14/machine.txt` is this table with the states `A`–`N` numbered `0`–`13`.

## Machine Layout

The machine keeps `2 ^ n` in unary: a block of `2 ^ n` ones, with a separator `0` and a counter
to its left. Each stage reads the base-3 digits of the block length by repeated division by `3`,
with a single `0` (the hole) in the block marking where the quotient ends.

* `D` (state `3`) starts dividing the `q` ones before the hole: it erases the first one, making a
  new hole. Each round `E`, `F`, `G` (`4`–`6`) move the old hole two cells left and `H`, `I` (`7`,
  `8`) move the new hole one cell right. If `q % 3 = 2` (a digit `2`), `G` fills the new hole and
  the stage ends. Otherwise `J` (`9`) returns to the start, and the hole now follows `q / 3` ones.
* When `q` reaches `0` with no digit `2`, `D` fills the hole and `M`, `N`, `K`, `L` (`12`, `13`,
  `10`, `11`) advance the counter (`000`, `100`, `111` left of the separator); the third such stage
  halts in `M`.
* At the end of a stage `K`, `L` remove one cell and `A`, `B`, `C` (`0`–`2`) double the block: `C`
  takes a cell from the part still to double, `A` adds a cell at the right end and `B` fills the
  gap.

The boot writes `11`, so the first stage checks `2 ^ 1` and the counter skips `2 ^ 0`. The machine
halts at the third power `2 ^ n` with `n ≥ 1` and no digit `2`; the first two are `2 ^ 2` and
`2 ^ 8`.
-/

@[expose] public section

namespace ConjectureMachines.Erdos14

open Turing (Dir)
open StateTransition
open Erdos15 (B0 B0_cons_zero pw pw_lt dbl cnt cnt_succ_of_mem cnt_succ_of_not_mem cnt_stays
  first_free free_or_none)

local notation "mkL" => Erdos15.Tape.mkL

/-- 15-state Erdős reference machine (`erdos_15`, Stérin & Woods 2021). -/
abbrev reference : BundledMachine 2 := Machines.erdos15.bundle

/-- 14-state Erdős candidate machine (`erdos_14`, Stérin 2026). -/
abbrev candidate : BundledMachine 2 := Machines.erdos14.bundle

/-- The candidate as a `Machine 14 2`. -/
abbrev erdos14 : Machine 14 2 := Machines.erdos14

/-! ## Base-3 Digits by Division -/

/-- `2` is a base-3 digit of `m`. -/
def Has2 (m : ℕ) : Prop := ∃ k, m / 3 ^ k % 3 = 2

theorem not_has2_zero : ¬ Has2 0 := by
  rintro ⟨k, hk⟩
  rw [Nat.zero_div] at hk
  omega

theorem has2_iff (m : ℕ) : Has2 m ↔ m % 3 = 2 ∨ Has2 (m / 3) := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      rw [pow_zero, Nat.div_one] at hk
      exact Or.inl hk
    | succ k =>
      rw [pow_succ', ← Nat.div_div_eq_div_mul] at hk
      exact Or.inr ⟨k, hk⟩
  · rintro (h | ⟨k, hk⟩)
    · exact ⟨0, by rw [pow_zero, Nat.div_one]; exact h⟩
    · exact ⟨k + 1, by rw [pow_succ', ← Nat.div_div_eq_div_mul]; exact hk⟩

/-- The number with base-3 digits `ds`, least significant first. -/
def val : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + 3 * val ds

theorem val_dbl (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) (c : ℕ) (hc : c ≤ 1) :
    val (dbl ds c) = 2 * val ds + c := by
  induction ds generalizing c with
  | nil =>
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · rfl
    · rfl
  | cons d ds ih =>
    have hd := hds d (by simp)
    simp only [dbl, val]
    rw [ih (fun x hx => hds x (List.mem_cons_of_mem d hx)) _ (by omega)]
    omega

theorem val_pw (n : ℕ) : val (pw n) = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pw, val_dbl _ (pw_lt n) 0 (by omega), ih, pow_succ]
    omega

theorem has2_val (ds : List ℕ) (hds : ∀ d ∈ ds, d < 3) : Has2 (val ds) ↔ 2 ∈ ds := by
  induction ds with
  | nil => exact ⟨fun h => absurd h not_has2_zero, fun h => absurd h List.not_mem_nil⟩
  | cons d ds ih =>
    have hd := hds d (by simp)
    rw [val, has2_iff, show (d + 3 * val ds) % 3 = d by omega,
      show (d + 3 * val ds) / 3 = val ds by omega,
      ih (fun x hx => hds x (List.mem_cons_of_mem d hx)), List.mem_cons, eq_comm]

/-- `2 ^ n` has a digit `2` in base `3` if and only if `pw n` contains `2`. -/
theorem has2_pow (n : ℕ) : Has2 (2 ^ n) ↔ 2 ∈ pw n := by
  rw [← val_pw]
  exact has2_val _ (pw_lt n)

/-! ## Tape Encoding -/

/-- `k` ones followed by `L`. -/
def ones (k : ℕ) (L : ListBlank (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append (List.replicate k 1) L

theorem ones_succ' (k : ℕ) (L : ListBlank (Fin 2)) : ones (k + 1) L = ones k (L.cons 1) := by
  rw [ones, List.replicate_succ', ListBlank.append_assoc]
  rfl

theorem ones_add (j k : ℕ) (L : ListBlank (Fin 2)) : ones (j + k) L = ones j (ones k L) := by
  rw [ones, List.replicate_add, ListBlank.append_assoc]
  rfl

/-- The counter cells left of the separator, nearest first: `000`, `100` or `111`. -/
def CT : ℕ → ListBlank (Fin 2)
  | 0 => ListBlank.append [0, 0, 0] B0
  | 1 => ListBlank.append [1, 0, 0] B0
  | _ => ListBlank.append [1, 1, 1] B0

/-- The cells left of the block: the separator `0`, then the counter. -/
def CL (c : ℕ) : ListBlank (Fin 2) := (CT c).cons 0

/-- `D` at the start of the block, which holds `q` ones, the hole, then `r` ones. -/
def divCfg (c q r : ℕ) : Cfg 14 2 :=
  ⟨3, Tape.mk' (CL c) (ones q ((ones r B0).cons 0))⟩

/-- Start of the stage that checks `2 ^ n`, with counter `c`. -/
def stageCfg (c n : ℕ) : Cfg 14 2 := divCfg c (2 ^ n) 0

/-- `E` on the first of the `b` cells between the two holes, with `a` ones before the first hole
and `r` ones after the second. -/
def cfgE (c a b r : ℕ) : Cfg 14 2 :=
  ⟨4, Tape.mk' ((ones a (CL c)).cons 0) (ones b ((ones r B0).cons 0))⟩

/-- `C` on the last of the `j + 1` cells still to double, with `t` doubled cells after it. -/
def cfgC (c j t : ℕ) : Cfg 14 2 :=
  ⟨2, Tape.mk' (ones j (CL c)) (ones (t + 1) B0)⟩

theorem divCfg_top (c M : ℕ) : divCfg c M 0 = ⟨3, Tape.mk' (CL c) (ones M B0)⟩ := by
  change (⟨3, Tape.mk' (CL c) (ones M (B0.cons 0))⟩ : Cfg 14 2) = _
  rw [B0_cons_zero]

theorem mkL_B0 (R : ListBlank (Fin 2)) : mkL B0 R = ⟨0, B0, R⟩ := rfl

/-! ## Step Infrastructure -/

/-- `n` steps of `M` from `c`, or `none` if `M` halts first. -/
def nSteps (M : Machine 14 2) (n : ℕ) : Cfg 14 2 → Option (Cfg 14 2) :=
  Nat.rec (motive := fun _ => Cfg 14 2 → Option (Cfg 14 2))
    (fun c => some c)
    (fun _ ih c => (step M c).bind ih)
    n

@[simp]
theorem nSteps_zero (M : Machine 14 2) (c : Cfg 14 2) :
    nSteps M 0 c = some c := rfl

@[simp]
theorem nSteps_succ (M : Machine 14 2) (n : ℕ) (c : Cfg 14 2) :
    nSteps M (n + 1) c = (step M c).bind (nSteps M n) := rfl

attribute [eqns nSteps_zero nSteps_succ] nSteps

theorem nSteps_reaches {M : Machine 14 2} {n : ℕ} {c c' : Cfg 14 2}
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

theorem nSteps_add {M : Machine 14 2} (m n : ℕ) (c : Cfg 14 2) :
    nSteps M (m + n) c = (nSteps M m c).bind (nSteps M n) := by
  induction m generalizing c with
  | zero => simp [nSteps]
  | succ m ih =>
    rw [Nat.succ_add, nSteps, nSteps]
    cases step M c <;> simp [ih]

theorem nSteps_bind_eq {M : Machine 14 2} {m n : ℕ} {c c₁ c₂ : Cfg 14 2}
    (h₁ : nSteps M m c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (m + n) c = some c₂ := by
  rw [nSteps_add, h₁, Option.bind_some, h₂]

theorem nSteps_cons {M : Machine 14 2} {n : ℕ} {c c₁ c₂ : Cfg 14 2}
    (h₁ : step M c = some c₁) (h₂ : nSteps M n c₁ = some c₂) :
    nSteps M (n + 1) c = some c₂ := by
  rw [nSteps_succ, h₁, Option.bind_some, h₂]

theorem step_one {M : Machine 14 2} {c c₁ : Cfg 14 2} (h : step M c = some c₁) :
    nSteps M 1 c = some c₁ := by
  rw [nSteps, h]; rfl

theorem reaches_imp_nSteps {M : Machine 14 2} {a b : Cfg 14 2}
    (h : Reaches (step M) a b) : ∃ k, nSteps M k a = some b := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨k, hk⟩ := ih
    exact ⟨k + 1, nSteps_bind_eq hk (step_one hstep)⟩

theorem nSteps_eq_none_of_step_none {M : Machine 14 2} {k : ℕ} (s : ℕ) {a b : Cfg 14 2}
    (hk : nSteps M k a = some b) (hnone : step M b = none) (hks : k < s) :
    nSteps M s a = none := by
  have hs : s = k + ((s - k - 1) + 1) := by omega
  rw [hs, nSteps_add, hk, Option.bind_some, nSteps_succ, hnone, Option.bind_none]

/-! ## Transition Table -/

theorem stepR {q q' : Fin 14} {a b : Fin 2} (h : erdos14.transition q a = some (b, .right, q'))
    (L R : ListBlank (Fin 2)) :
    step erdos14 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem stepL {q q' : Fin 14} {a b : Fin 2} (h : erdos14.transition q a = some (b, .left, q'))
    (L R : ListBlank (Fin 2)) :
    step erdos14 ⟨q, ⟨a, L, R⟩⟩ = some ⟨q', mkL L (R.cons b)⟩ := by
  simp only [step, h, Option.map_some]; rfl

theorem sA_0 (L R) : step erdos14 ⟨0, ⟨0, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sA_1 (L R) : step erdos14 ⟨0, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem sB_0 (L R) : step erdos14 ⟨1, ⟨0, L, R⟩⟩ = some ⟨2, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sB_1 (L R) : step erdos14 ⟨1, ⟨1, L, R⟩⟩ = some ⟨1, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sC_0 (L R) : step erdos14 ⟨2, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem sC_1 (L R) : step erdos14 ⟨2, ⟨1, L, R⟩⟩ = some ⟨0, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem sD_0 (L R) : step erdos14 ⟨3, ⟨0, L, R⟩⟩ = some ⟨12, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sD_1 (L R) : step erdos14 ⟨3, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem sE_0 (L R) : step erdos14 ⟨4, ⟨0, L, R⟩⟩ = some ⟨5, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sE_1 (L R) : step erdos14 ⟨4, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem sF_0 (L R) : step erdos14 ⟨5, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sF_1 (L R) : step erdos14 ⟨5, ⟨1, L, R⟩⟩ = some ⟨6, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sG_0 (L R) : step erdos14 ⟨6, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem sG_1 (L R) : step erdos14 ⟨6, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sH_0 (L R) : step erdos14 ⟨7, ⟨0, L, R⟩⟩ = some ⟨8, Tape.mk' (L.cons 1) R⟩ := stepR rfl L R
theorem sH_1 (L R) : step erdos14 ⟨7, ⟨1, L, R⟩⟩ = some ⟨7, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sI_0 (L R) : step erdos14 ⟨8, ⟨0, L, R⟩⟩ = some ⟨9, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sI_1 (L R) : step erdos14 ⟨8, ⟨1, L, R⟩⟩ = some ⟨4, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem sJ_0 (L R) : step erdos14 ⟨9, ⟨0, L, R⟩⟩ = some ⟨3, Tape.mk' (L.cons 0) R⟩ := stepR rfl L R
theorem sJ_1 (L R) : step erdos14 ⟨9, ⟨1, L, R⟩⟩ = some ⟨9, mkL L (R.cons 1)⟩ := stepL rfl L R
theorem sK_0 (L R) : step erdos14 ⟨10, ⟨0, L, R⟩⟩ = some ⟨11, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sK_1 (L R) : step erdos14 ⟨10, ⟨1, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL_0 (L R) : step erdos14 ⟨11, ⟨0, L, R⟩⟩ = some ⟨13, Tape.mk' (L.cons 1) R⟩ :=
  stepR rfl L R
theorem sL_1 (L R) : step erdos14 ⟨11, ⟨1, L, R⟩⟩ = some ⟨2, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sM_0 (L R) : step erdos14 ⟨12, ⟨0, L, R⟩⟩ = some ⟨13, mkL L (R.cons 0)⟩ := stepL rfl L R
theorem sM_1 (L R : ListBlank (Fin 2)) : step erdos14 ⟨12, ⟨1, L, R⟩⟩ = none := rfl
theorem sN_0 (L R) : step erdos14 ⟨13, ⟨0, L, R⟩⟩ = some ⟨10, Tape.mk' (L.cons 0) R⟩ :=
  stepR rfl L R
theorem sN_1 (L R) : step erdos14 ⟨13, ⟨1, L, R⟩⟩ = some ⟨12, mkL L (R.cons 0)⟩ := stepL rfl L R

/-- Runs the machine through a fixed sequence of steps on a concrete tape. -/
local macro "tm_run" : tactic => `(tactic| simp only [nSteps_succ, nSteps_zero, Option.bind_some,
  sA_0, sA_1, sB_0, sB_1, sC_0, sC_1, sD_0, sD_1, sE_0, sE_1, sF_0, sF_1, sG_0, sG_1, sH_0, sH_1,
  sI_0, sI_1, sJ_0, sJ_1, sK_0, sK_1, sL_0, sL_1, sM_0, sN_0, sN_1, Erdos15.Tape.mk'_cons,
  Erdos15.Tape.mkL_cons, Erdos15.Tape.mk'_B0, mkL_B0, ListBlank.append, B0_cons_zero])

/-! ## Sweeps over Ones -/

theorem sweepR {q : Fin 14}
    (h : ∀ L R, step erdos14 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, Tape.mk' (L.cons 1) R⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps erdos14 k ⟨q, Tape.mk' L (ones k R)⟩ = some ⟨q, Tape.mk' (ones k L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) R = (ones k R).cons 1 from rfl, Erdos15.Tape.mk'_cons, h,
      Option.bind_some, ih, ones_succ']

theorem sweepL {q : Fin 14}
    (h : ∀ L R, step erdos14 ⟨q, ⟨1, L, R⟩⟩ = some ⟨q, mkL L (R.cons 1)⟩)
    (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps erdos14 k ⟨q, mkL (ones k L) R⟩ = some ⟨q, mkL L (ones k R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [nSteps_succ, show ones (k + 1) L = (ones k L).cons 1 from rfl, Erdos15.Tape.mkL_cons, h,
      Option.bind_some, ih, ones_succ']

/-- `J` returns over `a` ones to the separator and hands over to `D`. -/
theorem j_return (c a : ℕ) (Y : ListBlank (Fin 2)) :
    ∃ s, nSteps erdos14 s ⟨9, mkL (ones a (CL c)) Y⟩ = some ⟨3, Tape.mk' (CL c) (ones a Y)⟩ := by
  have h₁ := sweepL sJ_1 a (CL c) Y
  have h₂ : step erdos14 ⟨9, mkL (CL c) (ones a Y)⟩ = some ⟨3, Tape.mk' (CL c) (ones a Y)⟩ := by
    rw [CL, Erdos15.Tape.mkL_cons, sJ_0]
  exact ⟨_, nSteps_bind_eq h₁ (step_one h₂)⟩

/-- After a stage, `K` stands right of the block of `j + 2` ones; `K`, `L` remove the last one
and hand over to `C`. -/
theorem kl_finish (c j : ℕ) :
    nSteps erdos14 2 ⟨10, Tape.mk' (ones (j + 2) (CL c)) B0⟩ = some (cfgC c j 0) := by
  change nSteps erdos14 2 ⟨10, Tape.mk' (((ones j (CL c)).cons 1).cons 1) B0⟩ =
    some ⟨2, Tape.mk' (ones j (CL c)) (B0.cons 1)⟩
  tm_run

/-! ## Doubling (States `A`, `B`, `C`) -/

/-- One doubling round: `C` takes the last cell, `A` adds a cell at the right end and `B` fills
the gap. -/
theorem dbl_round (c j t : ℕ) :
    ∃ s, nSteps erdos14 s (cfgC c j t) = some ⟨2, mkL (ones j (CL c)) (ones (t + 2) B0)⟩ := by
  have h₁ : step erdos14 (cfgC c j t) =
      some ⟨0, Tape.mk' ((ones j (CL c)).cons 0) (ones t B0)⟩ := by
    change step erdos14 ⟨2, Tape.mk' (ones j (CL c)) ((ones t B0).cons 1)⟩ = _
    rw [Erdos15.Tape.mk'_cons, sC_1]
  have h₂ := sweepR sA_1 t ((ones j (CL c)).cons 0) B0
  have h₃ : step erdos14 ⟨0, Tape.mk' (ones t ((ones j (CL c)).cons 0)) B0⟩ =
      some ⟨1, mkL (ones t ((ones j (CL c)).cons 0)) (B0.cons 1)⟩ := by
    rw [Erdos15.Tape.mk'_B0, sA_0]
  have h₄ := sweepL sB_1 t ((ones j (CL c)).cons 0) (B0.cons 1)
  have h₅ : step erdos14 ⟨1, mkL ((ones j (CL c)).cons 0) (ones t (B0.cons 1))⟩ =
      some ⟨2, mkL (ones j (CL c)) (ones (t + 2) B0)⟩ := by
    rw [Erdos15.Tape.mkL_cons, sB_0, ones_succ' (t + 1)]
    rfl
  exact ⟨_, nSteps_cons h₁ (nSteps_bind_eq h₂ (nSteps_cons h₃ (nSteps_bind_eq h₄
    (step_one h₅))))⟩

/-- Doubling the `j + 1` cells before `t` doubled cells ends at the next stage start. -/
theorem dbl_loop (c j : ℕ) :
    ∀ t, ∃ s, 1 ≤ s ∧ nSteps erdos14 s (cfgC c j t) = some (divCfg c (t + 2 * (j + 1)) 0) := by
  induction j with
  | zero =>
    intro t
    obtain ⟨s, hs⟩ := dbl_round c 0 t
    have h : step erdos14 ⟨2, mkL (ones 0 (CL c)) (ones (t + 2) B0)⟩ =
        some (divCfg c (t + 2 * (0 + 1)) 0) := by
      rw [divCfg_top]
      change step erdos14 ⟨2, mkL ((CT c).cons 0) (ones (t + 2) B0)⟩ =
        some ⟨3, Tape.mk' ((CT c).cons 0) (ones (t + 2) B0)⟩
      rw [Erdos15.Tape.mkL_cons, sC_0]
    exact ⟨s + 1, by omega, nSteps_bind_eq hs (step_one h)⟩
  | succ j ih =>
    intro t
    obtain ⟨s₁, hs₁⟩ := dbl_round c (j + 1) t
    obtain ⟨s₂, hs₂1, hs₂⟩ := ih (t + 2)
    have e : (⟨2, mkL (ones (j + 1) (CL c)) (ones (t + 2) B0)⟩ : Cfg 14 2) = cfgC c j (t + 2) := by
      change (⟨2, mkL ((ones j (CL c)).cons 1) (ones (t + 2) B0)⟩ : Cfg 14 2) =
        ⟨2, Tape.mk' (ones j (CL c)) ((ones (t + 2) B0).cons 1)⟩
      rw [Erdos15.Tape.mkL_cons, Erdos15.Tape.mk'_cons]
    rw [e] at hs₁
    refine ⟨s₁ + s₂, by omega, ?_⟩
    rw [show t + 2 * (j + 1 + 1) = t + 2 + 2 * (j + 1) by omega]
    exact nSteps_bind_eq hs₁ hs₂

/-! ## Division by `3` (States `D`–`J`) -/

theorem div_start (c q r : ℕ) : step erdos14 (divCfg c (q + 1) r) = some (cfgE c 0 q r) := by
  change step erdos14 ⟨3, Tape.mk' (CL c) ((ones q ((ones r B0).cons 0)).cons 1)⟩ = _
  rw [Erdos15.Tape.mk'_cons, sD_1]
  rfl

/-- `E` runs to the second hole and fills it, and `F` steps back. -/
theorem e_pass (c a b r : ℕ) : ∃ s, nSteps erdos14 s (cfgE c a b r) =
    some ⟨5, mkL (ones b ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ := by
  have h₁ := sweepR sE_1 b ((ones a (CL c)).cons 0) ((ones r B0).cons 0)
  have h₂ : step erdos14 ⟨4, Tape.mk' (ones b ((ones a (CL c)).cons 0)) ((ones r B0).cons 0)⟩ =
      some ⟨5, mkL (ones b ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ := by
    rw [Erdos15.Tape.mk'_cons, sE_0]
    rfl
  exact ⟨_, nSteps_bind_eq h₁ (step_one h₂)⟩

/-- No cell between the holes: the quotient is `a` and the digit is `1`. -/
theorem out_x (c a r : ℕ) : ∃ s, nSteps erdos14 s (cfgE c a 0 r) = some (divCfg c a (r + 1)) := by
  obtain ⟨s₁, hs₁⟩ := e_pass c a 0 r
  have h₂ : step erdos14 ⟨5, mkL (ones 0 ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ =
      some ⟨9, mkL (ones a (CL c)) ((ones (r + 1) B0).cons 0)⟩ := by
    change step erdos14 ⟨5, mkL ((ones a (CL c)).cons 0) (ones (r + 1) B0)⟩ = _
    rw [Erdos15.Tape.mkL_cons, sF_0]
  obtain ⟨s₃, hs₃⟩ := j_return c a ((ones (r + 1) B0).cons 0)
  exact ⟨_, nSteps_bind_eq hs₁ (nSteps_cons h₂ hs₃)⟩

/-- One cell between the holes: the digit is `2`; `G` fills the first hole and `K` runs to the
end of the block. -/
theorem out_y (c a r : ℕ) :
    ∃ s, nSteps erdos14 s (cfgE c a 1 r) = some (cfgC c (a + r + 1) 0) := by
  obtain ⟨s₁, hs₁⟩ := e_pass c a 1 r
  have h₂ : nSteps erdos14 2 ⟨5, mkL (ones 1 ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ =
      some ⟨10, Tape.mk' ((ones a (CL c)).cons 1) (ones (r + 2) B0)⟩ := by
    change nSteps erdos14 2 ⟨5, mkL (((ones a (CL c)).cons 0).cons 1) (ones (r + 1) B0)⟩ =
      some ⟨10, Tape.mk' ((ones a (CL c)).cons 1) ((ones (r + 1) B0).cons 1)⟩
    tm_run
  have h₃ := sweepR sK_1 (r + 2) ((ones a (CL c)).cons 1) B0
  have e : ones (r + 2) ((ones a (CL c)).cons 1) = ones (a + r + 1 + 2) (CL c) := by
    rw [show a + r + 1 + 2 = (r + 2) + (a + 1) by omega, ones_add (r + 2) (a + 1)]
    rfl
  rw [e] at h₃
  exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ (kl_finish c (a + r + 1))))⟩

/-- Two cells between the holes: the quotient is `a + 1` and the digit is `0`. -/
theorem out_z (c a r : ℕ) :
    ∃ s, nSteps erdos14 s (cfgE c a 2 r) = some (divCfg c (a + 1) (r + 2)) := by
  obtain ⟨s₁, hs₁⟩ := e_pass c a 2 r
  have h₂ : nSteps erdos14 4 ⟨5, mkL (ones 2 ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ =
      some ⟨9, mkL (ones (a + 1) (CL c)) ((ones (r + 2) B0).cons 0)⟩ := by
    change nSteps erdos14 4 ⟨5, mkL ((((ones a (CL c)).cons 0).cons 1).cons 1) (ones (r + 1) B0)⟩ =
      some ⟨9, mkL ((ones a (CL c)).cons 1) (((ones (r + 1) B0).cons 1).cons 0)⟩
    tm_run
  obtain ⟨s₃, hs₃⟩ := j_return c (a + 1) ((ones (r + 2) B0).cons 0)
  exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq h₂ hs₃)⟩

/-- A full round with at least three cells between the holes. -/
theorem div_round (c a b r : ℕ) :
    ∃ s, nSteps erdos14 s (cfgE c a (b + 3) r) = some (cfgE c (a + 1) b (r + 2)) := by
  obtain ⟨s₁, hs₁⟩ := e_pass c a (b + 3) r
  have h₂ : nSteps erdos14 2
      ⟨5, mkL (ones (b + 3) ((ones a (CL c)).cons 0)) (ones (r + 1) B0)⟩ =
      some ⟨7, mkL (ones (b + 1) ((ones a (CL c)).cons 0))
        (((ones (r + 1) B0).cons 1).cons 0)⟩ := by
    change nSteps erdos14 2
      ⟨5, mkL (((ones (b + 1) ((ones a (CL c)).cons 0)).cons 1).cons 1) (ones (r + 1) B0)⟩ = _
    tm_run
  have h₃ := sweepL sH_1 (b + 1) ((ones a (CL c)).cons 0) (((ones (r + 1) B0).cons 1).cons 0)
  have h₄ : nSteps erdos14 2
      ⟨7, mkL ((ones a (CL c)).cons 0) (ones (b + 1) (((ones (r + 1) B0).cons 1).cons 0))⟩ =
      some (cfgE c (a + 1) b (r + 2)) := by
    change nSteps erdos14 2
      ⟨7, mkL ((ones a (CL c)).cons 0) ((ones b (((ones (r + 1) B0).cons 1).cons 0)).cons 1)⟩ =
      some ⟨4, Tape.mk' (((ones a (CL c)).cons 1).cons 0)
        (ones b (((ones (r + 1) B0).cons 1).cons 0))⟩
    tm_run
  exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq h₂ (nSteps_bind_eq h₃ h₄))⟩

theorem loop0 (c k : ℕ) : ∀ a r,
    ∃ s, nSteps erdos14 s (cfgE c a (3 * k) r) = some (divCfg c (a + k) (r + 2 * k + 1)) := by
  induction k with
  | zero => exact out_x c
  | succ k ih =>
    intro a r
    obtain ⟨s₁, hs₁⟩ := div_round c a (3 * k) r
    obtain ⟨s₂, hs₂⟩ := ih (a + 1) (r + 2)
    rw [show 3 * (k + 1) = 3 * k + 3 by omega, show a + (k + 1) = a + 1 + k by omega,
      show r + 2 * (k + 1) + 1 = r + 2 + 2 * k + 1 by omega]
    exact ⟨_, nSteps_bind_eq hs₁ hs₂⟩

theorem loop1 (c k : ℕ) : ∀ a r,
    ∃ s, nSteps erdos14 s (cfgE c a (3 * k + 1) r) = some (cfgC c (a + k + (r + 2 * k) + 1) 0) := by
  induction k with
  | zero => exact out_y c
  | succ k ih =>
    intro a r
    obtain ⟨s₁, hs₁⟩ := div_round c a (3 * k + 1) r
    obtain ⟨s₂, hs₂⟩ := ih (a + 1) (r + 2)
    rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 3 by omega,
      show a + (k + 1) + (r + 2 * (k + 1)) + 1 = a + 1 + k + (r + 2 + 2 * k) + 1 by omega]
    exact ⟨_, nSteps_bind_eq hs₁ hs₂⟩

theorem loop2 (c k : ℕ) : ∀ a r,
    ∃ s, nSteps erdos14 s (cfgE c a (3 * k + 2) r) =
      some (divCfg c (a + k + 1) (r + 2 * k + 2)) := by
  induction k with
  | zero => exact out_z c
  | succ k ih =>
    intro a r
    obtain ⟨s₁, hs₁⟩ := div_round c a (3 * k + 2) r
    obtain ⟨s₂, hs₂⟩ := ih (a + 1) (r + 2)
    rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 3 by omega,
      show a + (k + 1) + 1 = a + 1 + k + 1 by omega,
      show r + 2 * (k + 1) + 2 = r + 2 + 2 * k + 2 by omega]
    exact ⟨_, nSteps_bind_eq hs₁ hs₂⟩

/-- Dividing `3 * k + 1` ones: digit `1`, quotient `k`. -/
theorem level_one (c k r : ℕ) :
    ∃ s, nSteps erdos14 s (divCfg c (3 * k + 1) r) = some (divCfg c k (r + 2 * k + 1)) := by
  obtain ⟨s, hs⟩ := loop0 c k 0 r
  rw [Nat.zero_add] at hs
  exact ⟨_, nSteps_cons (div_start c (3 * k) r) hs⟩

/-- Dividing `3 * k + 2` ones: digit `2`. -/
theorem level_two (c k r : ℕ) :
    ∃ s, nSteps erdos14 s (divCfg c (3 * k + 2) r) = some (cfgC c (3 * k + 1 + r) 0) := by
  obtain ⟨s, hs⟩ := loop1 c k 0 r
  rw [show 0 + k + (r + 2 * k) + 1 = 3 * k + 1 + r by omega] at hs
  exact ⟨_, nSteps_cons (div_start c (3 * k + 1) r) hs⟩

/-- Dividing `3 * k + 3` ones: digit `0`, quotient `k + 1`. -/
theorem level_zero (c k r : ℕ) :
    ∃ s, nSteps erdos14 s (divCfg c (3 * k + 3) r) = some (divCfg c (k + 1) (r + 2 * k + 2)) := by
  obtain ⟨s, hs⟩ := loop2 c k 0 r
  rw [show 0 + k + 1 = k + 1 by omega] at hs
  exact ⟨_, nSteps_cons (div_start c (3 * k + 2) r) hs⟩

/-- Repeated division of the `q` ones before the hole either finds a digit `2` and reaches the
doubling phase, or finds none and reaches `q = 0`. -/
theorem descend (c n : ℕ) : ∀ q r, q ≤ n →
    (Has2 q ∧ ∃ s, nSteps erdos14 s (divCfg c q r) = some (cfgC c (q + r - 1) 0)) ∨
    (¬ Has2 q ∧ ∃ s, nSteps erdos14 s (divCfg c q r) = some (divCfg c 0 (q + r))) := by
  induction n with
  | zero =>
    intro q r hq
    obtain rfl : q = 0 := by omega
    exact Or.inr ⟨not_has2_zero, 0, by rw [Nat.zero_add]; rfl⟩
  | succ n ih =>
    intro q r hq
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · exact Or.inr ⟨not_has2_zero, 0, by rw [Nat.zero_add]; rfl⟩
    obtain ⟨k, hk⟩ : ∃ k, q = 3 * k + 1 ∨ q = 3 * k + 2 ∨ q = 3 * k + 3 :=
      ⟨(q - 1) / 3, by omega⟩
    rcases hk with rfl | rfl | rfl
    · obtain ⟨s₁, hs₁⟩ := level_one c k r
      have hdiv : (3 * k + 1) / 3 = k := by omega
      rcases ih k (r + 2 * k + 1) (by omega) with ⟨h2, s₂, hs₂⟩ | ⟨h2, s₂, hs₂⟩
      · refine Or.inl ⟨(has2_iff _).mpr (Or.inr (by rw [hdiv]; exact h2)), s₁ + s₂, ?_⟩
        rw [show 3 * k + 1 + r - 1 = k + (r + 2 * k + 1) - 1 by omega]
        exact nSteps_bind_eq hs₁ hs₂
      · refine Or.inr ⟨fun h => ?_, s₁ + s₂, ?_⟩
        · rcases (has2_iff _).mp h with h | h
          · omega
          · rw [hdiv] at h
            exact h2 h
        · rw [show 3 * k + 1 + r = k + (r + 2 * k + 1) by omega]
          exact nSteps_bind_eq hs₁ hs₂
    · obtain ⟨s₁, hs₁⟩ := level_two c k r
      refine Or.inl ⟨(has2_iff _).mpr (Or.inl (by omega)), s₁, ?_⟩
      rw [show 3 * k + 2 + r - 1 = 3 * k + 1 + r by omega]
      exact hs₁
    · obtain ⟨s₁, hs₁⟩ := level_zero c k r
      have hdiv : (3 * k + 3) / 3 = k + 1 := by omega
      rcases ih (k + 1) (r + 2 * k + 2) (by omega) with ⟨h2, s₂, hs₂⟩ | ⟨h2, s₂, hs₂⟩
      · refine Or.inl ⟨(has2_iff _).mpr (Or.inr (by rw [hdiv]; exact h2)), s₁ + s₂, ?_⟩
        rw [show 3 * k + 3 + r - 1 = k + 1 + (r + 2 * k + 2) - 1 by omega]
        exact nSteps_bind_eq hs₁ hs₂
      · refine Or.inr ⟨fun h => ?_, s₁ + s₂, ?_⟩
        · rcases (has2_iff _).mp h with h | h
          · omega
          · rw [hdiv] at h
            exact h2 h
        · rw [show 3 * k + 3 + r = k + 1 + (r + 2 * k + 2) by omega]
          exact nSteps_bind_eq hs₁ hs₂

/-! ## Counter (States `K`–`N`) -/

theorem counter_zero (X : ListBlank (Fin 2)) :
    nSteps erdos14 6 ⟨3, Tape.mk' (CL 0) (X.cons 0)⟩ = some ⟨10, Tape.mk' (CL 1) (X.cons 1)⟩ := by
  simp only [CL, CT]
  tm_run

theorem counter_one (X : ListBlank (Fin 2)) :
    nSteps erdos14 14 ⟨3, Tape.mk' (CL 1) (X.cons 0)⟩ = some ⟨10, Tape.mk' (CL 2) (X.cons 1)⟩ := by
  simp only [CL, CT]
  tm_run

theorem counter_two (X : ListBlank (Fin 2)) :
    nSteps erdos14 3 ⟨3, Tape.mk' (CL 2) (X.cons 0)⟩ =
      some ⟨12, ⟨1, B0.cons 1, ((X.cons 1).cons 0).cons 0⟩⟩ := by
  simp only [CL, CT]
  tm_run

/-- A stage without a digit `2` advances the counter, then `K` runs to the end of the block. -/
theorem counter_inc (c r : ℕ) (hc : c < 2) :
    ∃ s, nSteps erdos14 s (divCfg c 0 (r + 1)) = some (cfgC (c + 1) r 0) := by
  have h₁ : ∃ s, nSteps erdos14 s (divCfg c 0 (r + 1)) =
      some ⟨10, Tape.mk' (CL (c + 1)) (ones (r + 2) B0)⟩ := by
    rcases (by omega : c = 0 ∨ c = 1) with rfl | rfl
    · exact ⟨6, counter_zero _⟩
    · exact ⟨14, counter_one _⟩
  obtain ⟨s₁, hs₁⟩ := h₁
  have h₂ := sweepR sK_1 (r + 2) (CL (c + 1)) B0
  exact ⟨_, nSteps_bind_eq hs₁ (nSteps_bind_eq h₂ (kl_finish (c + 1) r))⟩

/-- The third stage without a digit `2` halts. -/
theorem counter_halt (r : ℕ) :
    ∃ s cfg, nSteps erdos14 s (divCfg 2 0 r) = some cfg ∧ step erdos14 cfg = none :=
  ⟨3, _, counter_two _, sM_1 _ _⟩

/-! ## Stages -/

private theorem two_mul_pow (n : ℕ) : 0 + 2 * (2 ^ n + 0 - 1 + 1) = 2 ^ (n + 1) := by
  have := Nat.two_pow_pos n
  rw [pow_succ]
  omega

theorem stage_keep (c n : ℕ) (h : 2 ∈ pw n) :
    ∃ s, 1 ≤ s ∧ nSteps erdos14 s (stageCfg c n) = some (stageCfg c (n + 1)) := by
  rcases descend c (2 ^ n) (2 ^ n) 0 le_rfl with ⟨-, s₁, hs₁⟩ | ⟨hn, -⟩
  · obtain ⟨s₂, hs₂1, hs₂⟩ := dbl_loop c (2 ^ n + 0 - 1) 0
    rw [two_mul_pow] at hs₂
    exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩
  · exact absurd ((has2_pow n).mpr h) hn

theorem stage_inc (c n : ℕ) (hc : c < 2) (h : 2 ∉ pw n) :
    ∃ s, 1 ≤ s ∧ nSteps erdos14 s (stageCfg c n) = some (stageCfg (c + 1) (n + 1)) := by
  rcases descend c (2 ^ n) (2 ^ n) 0 le_rfl with ⟨hn, -⟩ | ⟨-, s₁, hs₁⟩
  · exact absurd ((has2_pow n).mp hn) h
  · have := Nat.two_pow_pos n
    rw [show 2 ^ n + 0 = 2 ^ n + 0 - 1 + 1 by omega] at hs₁
    obtain ⟨s₂, hs₂⟩ := counter_inc c (2 ^ n + 0 - 1) hc
    obtain ⟨s₃, hs₃1, hs₃⟩ := dbl_loop (c + 1) (2 ^ n + 0 - 1) 0
    rw [two_mul_pow] at hs₃
    exact ⟨s₁ + s₂ + s₃, by omega, nSteps_bind_eq (nSteps_bind_eq hs₁ hs₂) hs₃⟩

theorem stage_halt (n : ℕ) (h : 2 ∉ pw n) :
    ∃ s cfg, nSteps erdos14 s (stageCfg 2 n) = some cfg ∧ step erdos14 cfg = none := by
  rcases descend 2 (2 ^ n) (2 ^ n) 0 le_rfl with ⟨hn, -⟩ | ⟨-, s₁, hs₁⟩
  · exact absurd ((has2_pow n).mp hn) h
  · obtain ⟨s₂, cfg, hs₂, hnone⟩ := counter_halt (2 ^ n + 0)
    exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

theorem init_eq : (init : Cfg 14 2) = ⟨0, Tape.mk' B0 B0⟩ := rfl

/-- The boot writes `11` and starts the stage that checks `2 ^ 1`. -/
theorem boot : nSteps erdos14 3 init = some (stageCfg 0 1) := by
  rw [init_eq]
  change nSteps erdos14 3 ⟨0, Tape.mk' B0 B0⟩ =
    some ⟨3, Tape.mk' (CL 0) (((B0.cons 0).cons 1).cons 1)⟩
  simp only [CL, CT]
  tm_run

/-! ## Counting Powers Without a Digit `2` -/

theorem cnt_pos (n : ℕ) : 1 ≤ cnt n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    by_cases h : 2 ∈ pw (n + 1)
    · rw [cnt_succ_of_mem h]; exact ih
    · rw [cnt_succ_of_not_mem h]; omega

theorem reach (n : ℕ) (hn : cnt n ≤ 3) :
    ∃ s, n ≤ s ∧ nSteps erdos14 s init = some (stageCfg (cnt n - 1) (n + 1)) := by
  induction n with
  | zero => exact ⟨3, by omega, boot⟩
  | succ n ih =>
    have hpos := cnt_pos n
    by_cases h : 2 ∈ pw (n + 1)
    · rw [cnt_succ_of_mem h] at hn ⊢
      obtain ⟨s₁, hs₁n, hs₁⟩ := ih hn
      obtain ⟨s₂, hs₂1, hs₂⟩ := stage_keep (cnt n - 1) (n + 1) h
      exact ⟨s₁ + s₂, by omega, nSteps_bind_eq hs₁ hs₂⟩
    · rw [cnt_succ_of_not_mem h] at hn ⊢
      obtain ⟨s₁, hs₁n, hs₁⟩ := ih (by omega)
      obtain ⟨s₂, hs₂1, hs₂⟩ := stage_inc (cnt n - 1) (n + 1) (by omega) h
      refine ⟨s₁ + s₂, by omega, ?_⟩
      rw [show cnt n + 1 - 1 = cnt n - 1 + 1 by omega]
      exact nSteps_bind_eq hs₁ hs₂

theorem halt_of (n : ℕ) (h3 : cnt n = 3) (h : 2 ∉ pw (n + 1)) :
    ∃ s cfg, nSteps erdos14 s init = some cfg ∧ step erdos14 cfg = none := by
  obtain ⟨s₁, -, hs₁⟩ := reach n (by omega)
  rw [h3] at hs₁
  obtain ⟨s₂, cfg, hs₂, hnone⟩ := stage_halt (n + 1) h
  exact ⟨s₁ + s₂, cfg, nSteps_bind_eq hs₁ hs₂, hnone⟩

/-! ## Halting Equivalence -/

/-- The 14-state machine `erdos14` (`erdos_14`) halts on the blank tape if and only if some
power `2 ^ n` with `n > 8` has no digit `2` in base `3`, with the digits computed by `pw`. -/
theorem halts_erdos14_iff_exists_free :
    ConjectureMachines.Halts erdos14 ↔ ∃ n, 8 < n ∧ 2 ∉ pw n := by
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

/-- The 14-state machine halts on the blank tape if and only if the 15-state machine does. -/
theorem candidate_equivalent : Halts candidate ↔ Halts reference :=
  halts_erdos14_iff_exists_free.trans Erdos15.halts_erdos15_iff_exists_free.symm

/-- The candidate has one state fewer than the 15-state reference. -/
theorem candidate_fewer_states : candidate.states < reference.states := by
  decide +kernel

end ConjectureMachines.Erdos14
