/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.WordRLE

/-!
# Symbolic Affine Run-Length Certificates (`BusyBeaver.AffRLE`)

Machine-polymorphic reflective verifier for symbolic families of Turing machine configurations
whose word-run exponents and step counts are affine functions `a * k + b` of a parameter `k : ℕ`:

- `AffNat` (`a * k + b`) & `AffCfg` — Symbolic RLE stacks over composite vocabulary words.
- `CompExit` & `checkExitEntry` — Radix-trie composite word-exit certificates verified against
  `WordRLE.runCompositeExit`.
- `stepAffOnce` — Single symbolic RLE step supporting `O(1)` homogeneous affine sweeps (`a * k + b`
  copies in `(a * dt) * k + b * dt` steps) and exact target-remainder partial sweeps.
- `Aff2Nat` (`a * k + b + dp * j - dn * j`) & `verifyCycle` — Certified symbolic inner-loop
  acceleration discharging `K(k)` multi-step macro-cycles in `O(L)` kernel work.
- `ReturnCert` & `verifyReturnCert_sound` — Complete symbolic family transition verifier and
  `IsNotHalt.of_aff_return` non-halting closure principle.
-/

@[expose] public section

namespace BusyBeaver.AffRLE

open Turing BusyBeaver.WordRLE

/-! ## Affine Natural Numbers (`a * k + b`) -/

/-- Symbolic affine expression `a * k + b` over a non-negative integer parameter `k : ℕ`. -/
structure AffNat where
  /-- Linear coefficient of `k`. -/
  a : ℕ
  /-- Constant offset. -/
  b : ℕ
  deriving DecidableEq, Inhabited

namespace AffNat

/-- Evaluate `x` at parameter value `k : ℕ`. -/
def eval (k : ℕ) (x : AffNat) : ℕ :=
  x.a * k + x.b

/-- Force both coefficients of `x` to weak-head normal form before invoking `f`. -/
@[inline]
def strict {α : Type*} (x : AffNat) (f : AffNat → α) : α :=
  withNat x.a fun a ↦ withNat x.b fun b ↦ f ⟨a, b⟩

@[simp]
theorem strict_eq {α : Type*} (x : AffNat) (f : AffNat → α) : x.strict f = f x := by
  cases x
  simp [strict]

/-- Test whether `x` is identically `0` (`0 * k + 0`). -/
def isZero (x : AffNat) : Bool :=
  Nat.beq x.a 0 && Nat.beq x.b 0

/-- Test whether `x` is identically `1` (`0 * k + 1`). -/
def isOne (x : AffNat) : Bool :=
  Nat.beq x.a 0 && Nat.beq x.b 1

/-- Sufficient condition (`m ≤ x.b`) ensuring `m ≤ x.eval k` for all `k : ℕ`. -/
def geConst (x : AffNat) (m : ℕ) : Bool :=
  Nat.ble m x.b

/-- Pointwise sum `(x.a + y.a) * k + (x.b + y.b)` with CBV coefficient normalization. -/
def add (x y : AffNat) : AffNat :=
  withNat (x.a + y.a) fun a ↦ withNat (x.b + y.b) fun b ↦ ⟨a, b⟩

/-- Coefficient-wise subtraction returning `some (x - y)` when `y.a ≤ x.a` and `y.b ≤ x.b`. -/
def sub? (x y : AffNat) : Option AffNat :=
  if Nat.ble y.a x.a && Nat.ble y.b x.b then
    withNat (x.a - y.a) fun a ↦ withNat (x.b - y.b) fun b ↦ some ⟨a, b⟩
  else none

/-- Scalar product `(x.a * c) * k + (x.b * c)` with CBV coefficient normalization. -/
def scale (x : AffNat) (c : ℕ) : AffNat :=
  withNat (x.a * c) fun a ↦ withNat (x.b * c) fun b ↦ ⟨a, b⟩

/-- Lexicographic order on `(a, b)` for selecting minimal cycle counts at discovery time. -/
def lexLt (x y : AffNat) : Bool :=
  if Nat.beq x.a y.a then Nat.ble (x.b + 1) y.b else Nat.ble (x.a + 1) y.a

theorem eval_eq_zero_of_isZero {x : AffNat} (h : x.isZero = true) (k : ℕ) : x.eval k = 0 := by
  unfold isZero at h
  simp only [Bool.and_eq_true] at h
  have ha := Nat.eq_of_beq_eq_true h.1
  have hb := Nat.eq_of_beq_eq_true h.2
  simp [eval, ha, hb]

theorem eval_eq_one_of_isOne {x : AffNat} (h : x.isOne = true) (k : ℕ) : x.eval k = 1 := by
  unfold isOne at h
  simp only [Bool.and_eq_true] at h
  have ha := Nat.eq_of_beq_eq_true h.1
  have hb := Nat.eq_of_beq_eq_true h.2
  simp [eval, ha, hb]

theorem le_eval_of_geConst {x : AffNat} {m : ℕ} (h : x.geConst m = true) (k : ℕ) :
    m ≤ x.eval k := by
  have hb : m ≤ x.b := Nat.le_of_ble_eq_true h
  unfold eval
  omega

@[simp]
theorem eval_add (x y : AffNat) (k : ℕ) : (x.add y).eval k = x.eval k + y.eval k := by
  simp only [add, withNat_eq, eval, Nat.add_mul]
  omega

theorem eval_sub? {x y z : AffNat} (h : x.sub? y = some z) (k : ℕ) :
    x.eval k = y.eval k + z.eval k := by
  unfold sub? at h
  by_cases hle : (Nat.ble y.a x.a && Nat.ble y.b x.b) = true
  · simp only [hle, ↓reduceIte, withNat_eq, Option.some.injEq] at h
    subst h
    simp only [Bool.and_eq_true] at hle
    have ha : y.a ≤ x.a := Nat.le_of_ble_eq_true hle.1
    have hb : y.b ≤ x.b := Nat.le_of_ble_eq_true hle.2
    simp only [eval]
    have hmul : y.a * k + (x.a - y.a) * k = x.a * k := by
      rw [← Nat.add_mul, Nat.add_sub_of_le ha]
    omega
  · have hne : (Nat.ble y.a x.a && Nat.ble y.b x.b) = false := Bool.eq_false_iff.mpr hle
    simp [hne] at h

@[simp]
theorem eval_scale (x : AffNat) (c k : ℕ) : (x.scale c).eval k = c * x.eval k := by
  simp only [scale, withNat_eq, eval]
  calc
    x.a * c * k + x.b * c = c * (x.a * k) + c * x.b := by
      rw [Nat.mul_right_comm x.a c k, Nat.mul_comm c (x.a * k), Nat.mul_comm x.b c]
    _ = c * (x.a * k + x.b) := by rw [← Nat.mul_add]

theorem eval_scale_comm (x : AffNat) (c k : ℕ) : (x.scale c).eval k = x.eval k * c := by
  rw [eval_scale, Nat.mul_comm]

end AffNat

/-! ## Symbolic Affine Stacks (`AffRun`, `AffCfg`) -/

/-- A symbolic run of `count(k)` copies of composite vocabulary word `wid`. -/
structure AffRun where
  /-- Composite word index in `vocab`. -/
  wid : ℕ
  /-- Symbolic affine repetition count. -/
  count : AffNat
  deriving DecidableEq, Inhabited

/-- Force the top entry of an `AffRun` stack to weak-head normal form. -/
@[inline]
def strictAffStack {α : Type*} (stk : List AffRun) (f : List AffRun → α) : α :=
  match stk with
  | [] => f []
  | ⟨w, ⟨a, b⟩⟩ :: rest =>
    withNat w fun w' ↦ withNat a fun a' ↦ withNat b fun b' ↦ f (⟨w', ⟨a', b'⟩⟩ :: rest)

@[simp]
theorem strictAffStack_eq {α : Type*} (stk : List AffRun) (f : List AffRun → α) :
    strictAffStack stk f = f stk := by
  rcases stk with _ | ⟨⟨w, ⟨a, b⟩⟩, rest⟩ <;> simp [strictAffStack]

/-- CPS push of `count` copies of `wid` onto symbolic stack `stk`, suppressing blank `wid = 0` on
an empty stack and merging adjacent runs of the same word. -/
def pushAffK {α : Type*} (wid : ℕ) (count : AffNat) (stk : List AffRun)
    (f : Option (List AffRun) → α) : α :=
  if count.isZero then f (some stk)
  else match stk with
    | [] =>
      if Nat.beq wid 0 then f (some [])
      else if count.geConst 1 then
        withNat wid fun w' ↦ count.strict fun c' ↦ f (some [⟨w', c'⟩])
      else f none
    | ⟨tw, tc⟩ :: rest =>
      if !count.geConst 1 then f none
      else if Nat.beq tw wid then
        (tc.add count).strict fun c' ↦ f (some (⟨tw, c'⟩ :: rest))
      else
        withNat wid fun w' ↦ count.strict fun c' ↦ f (some (⟨w', c'⟩ :: ⟨tw, tc⟩ :: rest))

/-- Direct `Option`-returning push of `count` copies of `wid` onto `stk`. -/
def pushAff (wid : ℕ) (count : AffNat) (stk : List AffRun) : Option (List AffRun) :=
  pushAffK wid count stk id

theorem pushAffK_eq {α : Type*} (wid : ℕ) (count : AffNat) (stk : List AffRun)
    (f : Option (List AffRun) → α) :
    pushAffK wid count stk f = f (pushAff wid count stk) := by
  unfold pushAff pushAffK
  by_cases hz : count.isZero = true
  · simp [hz]
  · have hnz : count.isZero = false := Bool.eq_false_iff.mpr hz
    rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
    · simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      by_cases hw : Nat.beq wid 0 = true
      · simp [hw]
      · have hnw : Nat.beq wid 0 = false := Bool.eq_false_iff.mpr hw
        by_cases hg : count.geConst 1 = true
        · simp [hnw, hg]
        · have hng : count.geConst 1 = false := Bool.eq_false_iff.mpr hg
          simp [hnw, hng]
    · simp only [hnz, Bool.false_eq_true, ↓reduceIte]
      by_cases hg : count.geConst 1 = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        by_cases hw : Nat.beq tw wid = true
        · simp [hw]
        · have hnw : Nat.beq tw wid = false := Bool.eq_false_iff.mpr hw
          simp [hnw]
      · have hng : count.geConst 1 = false := Bool.eq_false_iff.mpr hg
        simp [hng]

/-- CPS pop of `count` copies from symbolic stack `stk`, popping `(0, [])` from `[]` when
`count = 1`. -/
def popAffK {α : Type*} (count : AffNat) (stk : List AffRun)
    (f : Option (ℕ × List AffRun) → α) : α :=
  match stk with
  | [] => if count.isOne then f (some (0, [])) else f none
  | ⟨tw, tc⟩ :: rest =>
    match tc.sub? count with
    | none => f none
    | some rem =>
      if rem.isZero then f (some (tw, rest))
      else if rem.geConst 1 then
        rem.strict fun rem' ↦ f (some (tw, ⟨tw, rem'⟩ :: rest))
      else f none

/-- Direct `Option`-returning pop of `count` copies from `stk`. -/
def popAff (count : AffNat) (stk : List AffRun) : Option (ℕ × List AffRun) :=
  popAffK count stk id

theorem popAffK_eq {α : Type*} (count : AffNat) (stk : List AffRun)
    (f : Option (ℕ × List AffRun) → α) :
    popAffK count stk f = f (popAff count stk) := by
  unfold popAff popAffK
  rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
  · by_cases h1 : count.isOne = true
    · simp [h1]
    · have hn1 : count.isOne = false := Bool.eq_false_iff.mpr h1
      simp [hn1]
  · simp only
    rcases hs : tc.sub? count with _ | rem
    · rfl
    · simp only
      by_cases hz : rem.isZero = true
      · simp [hz]
      · have hnz : rem.isZero = false := Bool.eq_false_iff.mpr hz
        by_cases hg : rem.geConst 1 = true
        · simp [hnz, hg]
        · have hng : rem.geConst 1 = false := Bool.eq_false_iff.mpr hg
          simp [hnz, hng]

/-- Push a spatial left-to-right list of constant `(wid, n)` runs onto a symbolic stack. -/
def pushAffConstRuns : List (ℕ × ℕ) → List AffRun → List AffRun
  | [], stk => stk
  | (w, n) :: rest, stk =>
    match pushAff w ⟨0, n⟩ stk with
    | some stk' => pushAffConstRuns rest stk'
    | none => stk

/-- Symbolic directed RLE configuration parameterized by `k : ℕ`. -/
structure AffCfg where
  /-- Current control state index. -/
  q : ℕ
  /-- Head direction (`true` = right, `false` = left). -/
  dir : Bool
  /-- Left symbolic RLE stack (nearest-to-head run first). -/
  left : List AffRun
  /-- Right symbolic RLE stack (nearest-to-head run first). -/
  right : List AffRun
  deriving DecidableEq, Inhabited

/-- Construct an `AffCfg` with CBV-normalized state, direction, and stack heads. -/
@[inline]
def mkStrictAffCfg (q : ℕ) (dir : Bool) (l r : List AffRun) : AffCfg :=
  withNat q fun q' ↦
  withBool dir fun d' ↦
  strictAffStack l fun l' ↦
  strictAffStack r fun r' ↦
    ⟨q', d', l', r'⟩

@[simp]
theorem mkStrictAffCfg_eq (q : ℕ) (dir : Bool) (l r : List AffRun) :
    mkStrictAffCfg q dir l r = ⟨q, dir, l, r⟩ := by
  simp [mkStrictAffCfg]

/-! ## Composite Exit Table & Single-Step Affine RLE Transition -/

/-- Certified exit record for a composite vocabulary word. -/
structure CompExit where
  /-- Resulting composite vocabulary word index. -/
  wid' : ℕ
  /-- Resulting control state index. -/
  q' : ℕ
  /-- Resulting exit direction. -/
  dir' : Bool
  /-- Exact number of TM steps taken inside the word. -/
  dt : ℕ
  deriving DecidableEq, Inhabited

/-- Pack `(wid, q, dir)` into a single `ℕ` trie key for a machine with `numStates` states. -/
@[inline]
def compKey (numStates wid q : ℕ) (dir : Bool) : ℕ :=
  wid * (2 * numStates) + q * 2 + (if dir then 1 else 0)

/-- Verify a single `(key, ex)` entry in an `exits` trie against `runCompositeExit`. -/
def checkExitEntry (numStates : ℕ)
    (baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ))
    (vocab : NatTrie (BTree ℕ)) (key : ℕ) (ex : CompExit) : Bool :=
  let stride := 2 * numStates
  if Nat.beq stride 0 then false
  else
    let wid := key / stride
    let rem := key % stride
    let q := rem / 2
    let dir := Nat.beq (rem % 2) 1
    match vocab.find? wid, vocab.find? ex.wid' with
    | some uTree, some vTree =>
      runCompositeExit baseExit uTree.toList q dir ==
        some (vTree.toList, ex.q', ex.dir', ex.dt)
    | _, _ => false

/-- Check that `wid = 0` in `vocab` consists exclusively of blank base-word `0` indices. -/
def checkVocabBlank0 (vocab : NatTrie (BTree ℕ)) : Bool :=
  match vocab.find? 0 with
  | none => true
  | some t => t.toList.all (Nat.beq · 0)

/-- Execute one symbolic affine RLE step (either a 1-copy exit or a homogeneous sweep of the top
run, optionally clipped to `targetRem?` when dividing the remaining step budget cleanly). -/
def stepAffOnce (numStates : ℕ) (exits : NatTrie CompExit) (targetRem? : Option AffNat)
    (q : ℕ) (dir : Bool) (l r : List AffRun) : Option (AffNat × AffCfg) :=
  if !Nat.ble (q + 1) numStates then none
  else
    let src := if dir then r else l
    let wid := match src with | [] => 0 | top :: _ => top.wid
    match exits.find? (compKey numStates wid q dir) with
    | none => none
    | some ex =>
      let same := Nat.beq ex.q' q && Bool.beq ex.dir' dir
      let count? : Option AffNat :=
        if same then
          match src with
          | [] => none
          | top :: _ =>
            let full := top.count
            match targetRem? with
            | none => some full
            | some rem =>
              if Nat.ble 1 ex.dt && Nat.beq (rem.a % ex.dt) 0 && Nat.beq (rem.b % ex.dt) 0 then
                let part : AffNat := ⟨rem.a / ex.dt, rem.b / ex.dt⟩
                if part.geConst 1 && (full.sub? part).isSome then some part else some full
              else some full
        else some ⟨0, 1⟩
      match count? with
      | none => none
      | some count =>
        if dir then
          popAffK count r fun
            | none => none
            | some (_, r') =>
              (count.scale ex.dt).strict fun dt ↦
                if ex.dir' then
                  pushAffK ex.wid' count l fun
                    | none => none
                    | some l₂ => some (dt, mkStrictAffCfg ex.q' true l₂ r')
                else
                  pushAffK ex.wid' count r' fun
                    | none => none
                    | some r₂ => some (dt, mkStrictAffCfg ex.q' false l r₂)
        else
          popAffK count l fun
            | none => none
            | some (_, l') =>
              (count.scale ex.dt).strict fun dt ↦
                if ex.dir' then
                  pushAffK ex.wid' count l' fun
                    | none => none
                    | some l₂ => some (dt, mkStrictAffCfg ex.q' true l₂ r)
                else
                  pushAffK ex.wid' count r fun
                    | none => none
                    | some r₂ => some (dt, mkStrictAffCfg ex.q' false l' r₂)

/-! ## Two-Variable Inner-Cycle Verifier (`Aff2Nat`, `verifyCycle`) -/

/-- Symbolic expression `a * k + b + dp * j - dn * j` over outer parameter `k : ℕ` and inner loop
index `0 ≤ j ≤ K(k)`. -/
structure Aff2Nat where
  /-- Outer linear coefficient of `k`. -/
  a : ℕ
  /-- Outer constant offset. -/
  b : ℕ
  /-- Positive inner-loop slope (`+dp * j`). -/
  dp : ℕ
  /-- Negative inner-loop slope (`-dn * j`). -/
  dn : ℕ
  deriving DecidableEq, Inhabited

namespace Aff2Nat

/-- Evaluate `x` at outer parameter `k` and inner loop index `j`. -/
def eval (k j : ℕ) (x : Aff2Nat) : ℕ :=
  x.a * k + x.b + x.dp * j - x.dn * j

/-- Test whether `x` is identically `0`. -/
def isZero (x : Aff2Nat) : Bool :=
  Nat.beq x.a 0 && Nat.beq x.b 0 && Nat.beq x.dp 0 && Nat.beq x.dn 0

/-- Extract constant `b` when `a = dp = dn = 0`. -/
def isConst (x : Aff2Nat) : Option ℕ :=
  if Nat.beq x.a 0 && Nat.beq x.dp 0 && Nat.beq x.dn 0 then some x.b else none

/-- Check that `x.dn * j + m ≤ x.a * k + x.b + x.dp * j` holds for all `k` and all
`j < K.eval k`. -/
def geForLoop (x : Aff2Nat) (K : AffNat) (m : ℕ) : Bool :=
  if Nat.beq x.dn 0 then Nat.ble m x.b
  else if Nat.ble x.dn x.dp then Nat.ble m x.b
  else
    let netN := x.dn - x.dp
    Nat.ble (netN * K.a) x.a && Nat.ble (netN * K.b + m) (x.b + netN)

/-- Add two `Aff2Nat` expressions, normalizing `(dp, dn)`. -/
def add (x y : Aff2Nat) : Aff2Nat :=
  let p := x.dp + y.dp
  let n := x.dn + y.dn
  let (dp', dn') := if Nat.ble n p then (p - n, 0) else (0, n - p)
  ⟨x.a + y.a, x.b + y.b, dp', dn'⟩

/-- Subtract `y` from `x` when valid throughout `0 ≤ j < K.eval k`. -/
def sub? (x y : Aff2Nat) (K : AffNat) : Option Aff2Nat :=
  if Nat.ble y.a x.a && Nat.ble y.b x.b then
    let a' := x.a - y.a
    let b' := x.b - y.b
    let p := x.dp + y.dn
    let n := x.dn + y.dp
    let (dp', dn') := if Nat.ble n p then (p - n, 0) else (0, n - p)
    let res : Aff2Nat := ⟨a', b', dp', dn'⟩
    if res.geForLoop K 0 then some res else none
  else none

/-- Shift `j ↦ j + 1`: `a * k + (b + dp - dn) + dp * j - dn * j`. -/
def shiftJ? (x : Aff2Nat) : Option Aff2Nat :=
  if Nat.ble x.dn (x.b + x.dp) then
    some ⟨x.a, x.b + x.dp - x.dn, x.dp, x.dn⟩
  else none

/-- Substitute `j = K.eval k` at loop completion. -/
def atEnd? (x : Aff2Nat) (K : AffNat) : Option AffNat :=
  let pa := x.a + x.dp * K.a
  let pb := x.b + x.dp * K.b
  let na := x.dn * K.a
  let nb := x.dn * K.b
  if Nat.ble na pa && Nat.ble nb pb then
    AffNat.strict ⟨pa - na, pb - nb⟩ some
  else none

theorem noUnderflow_of_geForLoop {x : Aff2Nat} {K : AffNat} {m k j : ℕ}
    (hg : x.geForLoop K m = true) (hj : j < K.eval k) :
    x.dn * j + m ≤ x.a * k + x.b + x.dp * j := by
  unfold geForLoop at hg
  by_cases hdn0 : Nat.beq x.dn 0 = true
  · have h0 : x.dn = 0 := Nat.eq_of_beq_eq_true hdn0
    simp only [hdn0, ↓reduceIte] at hg
    have hb : m ≤ x.b := Nat.le_of_ble_eq_true hg
    rw [h0]
    omega
  · have hndn0 : Nat.beq x.dn 0 = false := Bool.eq_false_iff.mpr hdn0
    rw [hndn0] at hg
    simp only [Bool.false_eq_true, ↓reduceIte] at hg
    by_cases hle : Nat.ble x.dn x.dp = true
    · simp only [hle, ↓reduceIte] at hg
      have hdp : x.dn ≤ x.dp := Nat.le_of_ble_eq_true hle
      have hb : m ≤ x.b := Nat.le_of_ble_eq_true hg
      have hmul : x.dn * j ≤ x.dp * j := Nat.mul_le_mul_right j hdp
      omega
    · have hnle : Nat.ble x.dn x.dp = false := Bool.eq_false_iff.mpr hle
      rw [hnle] at hg
      simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true] at hg
      have hgt : x.dp < x.dn := by
        have : ¬ x.dn ≤ x.dp := fun h ↦ hle (Nat.ble_eq.mpr h)
        omega
      have ha : (x.dn - x.dp) * K.a ≤ x.a := Nat.le_of_ble_eq_true hg.1
      have hb : (x.dn - x.dp) * K.b + m ≤ x.b + (x.dn - x.dp) := Nat.le_of_ble_eq_true hg.2
      unfold AffNat.eval at hj
      have hj1 : (x.dn - x.dp) * (j + 1) ≤ (x.dn - x.dp) * (K.a * k + K.b) :=
        Nat.mul_le_mul_left (x.dn - x.dp) hj
      have hak : (x.dn - x.dp) * K.a * k ≤ x.a * k := Nat.mul_le_mul_right k ha
      have hexp1 : (x.dn - x.dp) * (j + 1) = (x.dn - x.dp) * j + (x.dn - x.dp) := by
        rw [Nat.mul_add, Nat.mul_one]
      have hexp2 :
          (x.dn - x.dp) * (K.a * k + K.b) = (x.dn - x.dp) * K.a * k + (x.dn - x.dp) * K.b := by
        rw [Nat.mul_add, Nat.mul_assoc]
      have hnet : (x.dn - x.dp) * j + x.dp * j = x.dn * j := by
        rw [← Nat.add_mul, Nat.sub_add_cancel (Nat.le_of_lt hgt)]
      omega

theorem eval_eq_zero_of_isZero {x : Aff2Nat} (h : x.isZero = true) (k j : ℕ) :
    x.eval k j = 0 := by
  unfold isZero at h
  simp only [Bool.and_eq_true] at h
  have ha := Nat.eq_of_beq_eq_true h.1.1.1
  have hb := Nat.eq_of_beq_eq_true h.1.1.2
  have hdp := Nat.eq_of_beq_eq_true h.1.2
  have hdn := Nat.eq_of_beq_eq_true h.2
  simp [eval, ha, hb, hdp, hdn]

theorem isConst_eq {x : Aff2Nat} {c : ℕ} (h : x.isConst = some c) :
    x = ⟨0, c, 0, 0⟩ := by
  unfold isConst at h
  by_cases hc : (Nat.beq x.a 0 && Nat.beq x.dp 0 && Nat.beq x.dn 0) = true
  · simp only [hc, ↓reduceIte, Option.some.injEq] at h
    simp only [Bool.and_eq_true] at hc
    rcases x with ⟨a, b, dp, dn⟩
    simp only at hc h
    have ha := Nat.eq_of_beq_eq_true hc.1.1
    have hdp := Nat.eq_of_beq_eq_true hc.1.2
    have hdn := Nat.eq_of_beq_eq_true hc.2
    subst ha; subst hdp; subst hdn; subst h
    rfl
  · have hnc := Bool.eq_false_iff.mpr hc
    simp [hnc] at h

theorem add_const_eval (x : Aff2Nat) (c k j : ℕ)
    (hx : x.dn * j ≤ x.a * k + x.b + x.dp * j) :
    (x.add ⟨0, c, 0, 0⟩).eval k j = x.eval k j + c := by
  unfold add eval
  simp only [Nat.add_zero]
  by_cases hle : Nat.ble x.dn x.dp = true
  · simp only [hle, ↓reduceIte, Nat.zero_mul, Nat.sub_zero]
    have hdp : x.dn ≤ x.dp := Nat.le_of_ble_eq_true hle
    have hsub : (x.dp - x.dn) * j + x.dn * j = x.dp * j := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hdp]
    omega
  · have hnle : Nat.ble x.dn x.dp = false := Bool.eq_false_iff.mpr hle
    simp only [hnle, Bool.false_eq_true, ↓reduceIte, Nat.zero_mul, Nat.add_zero]
    have hgt : x.dp ≤ x.dn := by
      have : ¬ x.dn ≤ x.dp := fun h ↦ hle (Nat.ble_eq.mpr h)
      omega
    have hsub : (x.dn - x.dp) * j + x.dp * j = x.dn * j := by
      rw [← Nat.add_mul, Nat.sub_add_cancel hgt]
    omega

theorem add_const_geForLoop {x : Aff2Nat} {K : AffNat} {c m : ℕ}
    (hx : x.geForLoop K m = true) :
    (x.add ⟨0, c, 0, 0⟩).geForLoop K m = true := by
  unfold add
  simp only [Nat.add_zero]
  by_cases hle : Nat.ble x.dn x.dp = true
  · simp only [hle, ↓reduceIte]
    have hdp : x.dn ≤ x.dp := Nat.le_of_ble_eq_true hle
    unfold geForLoop at hx ⊢
    simp only [Nat.beq_refl, ↓reduceIte]
    by_cases hdn0 : Nat.beq x.dn 0 = true
    · simp only [hdn0, ↓reduceIte] at hx
      have hb := Nat.le_of_ble_eq_true hx
      exact Nat.ble_eq.mpr (by omega)
    · have hndn0 := Bool.eq_false_iff.mpr hdn0
      simp only [hndn0, Bool.false_eq_true, ↓reduceIte, hle] at hx
      have hb := Nat.le_of_ble_eq_true hx
      exact Nat.ble_eq.mpr (by omega)
  · have hnle : Nat.ble x.dn x.dp = false := Bool.eq_false_iff.mpr hle
    simp only [hnle, Bool.false_eq_true, ↓reduceIte]
    have hgt : x.dp < x.dn := by
      have : ¬ x.dn ≤ x.dp := fun h ↦ hle (Nat.ble_eq.mpr h)
      omega
    have hdn0 : Nat.beq x.dn 0 = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have := Nat.eq_of_beq_eq_true h0
      omega
    unfold geForLoop at hx ⊢
    simp only [hdn0, Bool.false_eq_true, ↓reduceIte, hnle, Bool.and_eq_true] at hx
    have hsub0 : Nat.beq (x.dn - x.dp) 0 = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have := Nat.eq_of_beq_eq_true h0
      omega
    have hsuble : Nat.ble (x.dn - x.dp) 0 = false := by
      apply Bool.eq_false_iff.mpr
      intro h0
      have := Nat.le_of_ble_eq_true h0
      omega
    simp only [hsub0, Bool.false_eq_true, ↓reduceIte, hsuble, Nat.sub_zero, Bool.and_eq_true]
    refine ⟨hx.1, ?_⟩
    have hb := Nat.le_of_ble_eq_true hx.2
    exact Nat.ble_eq.mpr (by omega)

theorem sub_const_eval {x rem : Aff2Nat} {K : AffNat} {c k j : ℕ}
    (hsub : x.sub? ⟨0, c, 0, 0⟩ K = some rem) (hj : j < K.eval k) :
    x.eval k j = c + rem.eval k j := by
  unfold sub? at hsub
  have h0a : Nat.ble 0 x.a = true := Nat.ble_eq.mpr (Nat.zero_le x.a)
  simp only [h0a, Bool.true_and, Nat.sub_zero, Nat.add_zero] at hsub
  by_cases hcb : Nat.ble c x.b = true
  · simp only [hcb, ↓reduceIte] at hsub
    have hcle : c ≤ x.b := Nat.le_of_ble_eq_true hcb
    by_cases hg :
        (Aff2Nat.mk x.a (x.b - c)
          (if Nat.ble x.dn x.dp then (x.dp - x.dn, 0) else (0, x.dn - x.dp)).1
          (if Nat.ble x.dn x.dp then (x.dp - x.dn, 0) else (0, x.dn - x.dp)).2).geForLoop K 0 = true
    · simp only [hg, ↓reduceIte, Option.some.injEq] at hsub
      have hno := noUnderflow_of_geForLoop hg hj
      subst hsub
      by_cases hle : Nat.ble x.dn x.dp = true
      · simp only [hle, ↓reduceIte] at hno ⊢
        unfold eval
        simp only [Nat.zero_mul, Nat.sub_zero]
        have hdp : x.dn ≤ x.dp := Nat.le_of_ble_eq_true hle
        have hm : (x.dp - x.dn) * j + x.dn * j = x.dp * j := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hdp]
        omega
      · have hnle : Nat.ble x.dn x.dp = false := Bool.eq_false_iff.mpr hle
        simp only [hnle, Bool.false_eq_true, ↓reduceIte] at hno ⊢
        unfold eval
        simp only [Nat.zero_mul, Nat.add_zero]
        have hgt : x.dp ≤ x.dn := by
          have : ¬ x.dn ≤ x.dp := fun h ↦ hle (Nat.ble_eq.mpr h)
          omega
        have hm : (x.dn - x.dp) * j + x.dp * j = x.dn * j := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hgt]
        omega
    · have hng := Bool.eq_false_iff.mpr hg
      rw [hng] at hsub
      simp at hsub
  · have hncb := Bool.eq_false_iff.mpr hcb
    simp [hncb] at hsub

theorem shiftJ_eval {x x' : Aff2Nat} {K : AffNat} {cEnd : AffNat} {k j : ℕ}
    (hsh : x.shiftJ? = some x') (hend : x.atEnd? K = some cEnd) (hj : j < K.eval k) :
    x'.eval k j = x.eval k (j + 1) := by
  unfold shiftJ? at hsh
  by_cases hle1 : Nat.ble x.dn (x.b + x.dp) = true
  · simp only [hle1, ↓reduceIte, Option.some.injEq] at hsh
    subst hsh
    have hdnb : x.dn ≤ x.b + x.dp := Nat.le_of_ble_eq_true hle1
    unfold atEnd? at hend
    by_cases hle2 :
        (Nat.ble (x.dn * K.a) (x.a + x.dp * K.a) &&
          Nat.ble (x.dn * K.b) (x.b + x.dp * K.b)) = true
    · simp only [Bool.and_eq_true] at hle2
      have ha : x.dn * K.a ≤ x.a + x.dp * K.a := Nat.le_of_ble_eq_true hle2.1
      have hb : x.dn * K.b ≤ x.b + x.dp * K.b := Nat.le_of_ble_eq_true hle2.2
      unfold eval
      simp only [Nat.mul_add, Nat.mul_one]
      by_cases hdp : x.dn ≤ x.dp
      · have hm : x.dn * j ≤ x.dp * j := Nat.mul_le_mul_right j hdp
        omega
      · have hgt : x.dp ≤ x.dn := by omega
        have hna : (x.dn - x.dp) * K.a ≤ x.a := by
          have : (x.dn - x.dp) * K.a + x.dp * K.a = x.dn * K.a := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hgt]
          omega
        have hnb : (x.dn - x.dp) * K.b ≤ x.b := by
          have : (x.dn - x.dp) * K.b + x.dp * K.b = x.dn * K.b := by
            rw [← Nat.add_mul, Nat.sub_add_cancel hgt]
          omega
        unfold AffNat.eval at hj
        have hjK : (x.dn - x.dp) * (j + 1) ≤ (x.dn - x.dp) * (K.a * k + K.b) :=
          Nat.mul_le_mul_left (x.dn - x.dp) hj
        have hak : (x.dn - x.dp) * K.a * k ≤ x.a * k := Nat.mul_le_mul_right k hna
        have hexp :
            (x.dn - x.dp) * (K.a * k + K.b) = (x.dn - x.dp) * K.a * k + (x.dn - x.dp) * K.b := by
          rw [Nat.mul_add, Nat.mul_assoc]
        have hm1 : (x.dn - x.dp) * (j + 1) + x.dp * (j + 1) = x.dn * (j + 1) := by
          rw [← Nat.add_mul, Nat.sub_add_cancel hgt]
        have hexp2 : x.dp * (j + 1) = x.dp * j + x.dp := by rw [Nat.mul_add, Nat.mul_one]
        have hexp3 : x.dn * (j + 1) = x.dn * j + x.dn := by rw [Nat.mul_add, Nat.mul_one]
        omega
    · have hnle2 := Bool.eq_false_iff.mpr hle2
      simp [hnle2] at hend
  · have hnle1 := Bool.eq_false_iff.mpr hle1
    simp [hnle1] at hsh

theorem atEnd_eval {x : Aff2Nat} {K cEnd : AffNat} (hend : x.atEnd? K = some cEnd) (k : ℕ) :
    x.eval k (K.eval k) = cEnd.eval k := by
  unfold atEnd? at hend
  by_cases hle :
      (Nat.ble (x.dn * K.a) (x.a + x.dp * K.a) &&
        Nat.ble (x.dn * K.b) (x.b + x.dp * K.b)) = true
  · simp only [hle, ↓reduceIte, AffNat.strict_eq, Option.some.injEq] at hend
    subst hend
    simp only [Bool.and_eq_true] at hle
    have ha : x.dn * K.a ≤ x.a + x.dp * K.a := Nat.le_of_ble_eq_true hle.1
    have hb : x.dn * K.b ≤ x.b + x.dp * K.b := Nat.le_of_ble_eq_true hle.2
    unfold eval AffNat.eval
    simp only
    have hpa : (x.a + x.dp * K.a - x.dn * K.a) * k + x.dn * K.a * k =
        (x.a + x.dp * K.a) * k := by
      rw [← Nat.add_mul, Nat.sub_add_cancel ha]
    have hexp1 : (x.a + x.dp * K.a) * k = x.a * k + x.dp * (K.a * k) := by
      rw [Nat.add_mul, Nat.mul_assoc]
    have hexp2 : x.dp * (K.a * k + K.b) = x.dp * (K.a * k) + x.dp * K.b := Nat.mul_add _ _ _
    have hexp3 : x.dn * (K.a * k + K.b) = x.dn * K.a * k + x.dn * K.b := by
      rw [Nat.mul_add, Nat.mul_assoc]
    omega
  · have hnle := Bool.eq_false_iff.mpr hle
    simp [hnle] at hend

end Aff2Nat

/-- Two-variable symbolic word run inside an inner cycle. -/
structure Aff2Run where
  /-- Composite word index in `vocab`. -/
  wid : ℕ
  /-- Symbolic count `a * k + b + dp * j - dn * j`. -/
  count : Aff2Nat
  deriving DecidableEq, Inhabited

/-- Push `count` copies of `wid` onto an `Aff2Run` stack during inner-cycle verification. -/
def pushAff2 (K : AffNat) (wid : ℕ) (count : Aff2Nat) (stk : List Aff2Run) :
    Option (List Aff2Run) :=
  if count.isZero then some stk
  else if !count.geForLoop K 1 then none
  else match stk with
    | [] => if Nat.beq wid 0 then some [] else some [⟨wid, count⟩]
    | top :: rest =>
      if Nat.beq top.wid wid then some (⟨wid, top.count.add count⟩ :: rest)
      else some (⟨wid, count⟩ :: stk)

/-- Pop `count` copies from an `Aff2Run` stack during inner-cycle verification. -/
def popAff2 (K : AffNat) (count : Aff2Nat) (stk : List Aff2Run) :
    Option (ℕ × List Aff2Run) :=
  match stk with
  | [] => if count == ⟨0, 1, 0, 0⟩ then some (0, []) else none
  | top :: rest =>
    match top.count.sub? count K with
    | none => none
    | some rem =>
      if rem.isZero then some (top.wid, rest)
      else if rem.geForLoop K 1 then some (top.wid, ⟨top.wid, rem⟩ :: rest)
      else none

/-- Two-variable symbolic configuration inside an inner cycle. -/
structure Aff2Cfg where
  /-- Current control state index. -/
  q : ℕ
  /-- Head direction (`true` = right, `false` = left). -/
  dir : Bool
  /-- Left two-variable stack. -/
  left : List Aff2Run
  /-- Right two-variable stack. -/
  right : List Aff2Run
  deriving DecidableEq, Inhabited

/-- Execute one constant-count symbolic RLE step inside an inner cycle body. -/
def stepAff2Once (numStates : ℕ) (exits : NatTrie CompExit) (K : AffNat) (c : Aff2Cfg) :
    Option (ℕ × Aff2Cfg) :=
  if !Nat.ble (c.q + 1) numStates then none
  else
    let src := if c.dir then c.right else c.left
    let wid := match src with | [] => 0 | top :: _ => top.wid
    match exits.find? (compKey numStates wid c.q c.dir) with
    | none => none
    | some ex =>
      let same := Nat.beq ex.q' c.q && Bool.beq ex.dir' c.dir
      let count? : Option Aff2Nat :=
        if same then
          match src with
          | [] => none
          | top :: _ => some top.count
        else some ⟨0, 1, 0, 0⟩
      match count? with
      | none => none
      | some count =>
        match count.isConst with
        | none => none
        | some cntVal =>
          match popAff2 K count src with
          | none => none
          | some (_, src') =>
            let l₁ := if c.dir then c.left else src'
            let r₁ := if c.dir then src' else c.right
            let dst? :=
              if ex.dir' then (pushAff2 K ex.wid' count l₁).map fun l₂ ↦ (l₂, r₁)
              else (pushAff2 K ex.wid' count r₁).map fun r₂ ↦ (l₁, r₂)
            match dst? with
            | none => none
            | some (l₂, r₂) =>
              withNat (cntVal * ex.dt) fun dt ↦
                some (dt, ⟨ex.q', ex.dir', l₂, r₂⟩)

/-- Execute `n` steps of `stepAff2Once`, accumulating the constant per-iteration step count. -/
def runAff2Steps (numStates : ℕ) (exits : NatTrie CompExit) (K : AffNat) :
    ℕ → ℕ → Aff2Cfg → Option (ℕ × Aff2Cfg)
  | 0, acc, c => some (acc, c)
  | n + 1, acc, c =>
    match stepAff2Once numStates exits K c with
    | none => none
    | some (dt, c') =>
      withNat (acc + dt) fun acc' ↦ runAff2Steps numStates exits K n acc' c'

/-- Attach inner-loop `(dp, dn)` slopes to a symbolic `AffRun` stack. -/
def attachDeltas : List AffRun → List (ℕ × ℕ) → Option (List Aff2Run × List (ℕ × ℕ))
  | [], ds => some ([], ds)
  | r :: rs, (dp, dn) :: ds =>
    match attachDeltas rs ds with
    | none => none
    | some (out, ds') => some (⟨r.wid, ⟨r.count.a, r.count.b, dp, dn⟩⟩ :: out, ds')
  | _, [] => none

/-- Shift every entry in an `Aff2Run` stack from `j` to `j + 1`. -/
def shiftStackJ : List Aff2Run → Option (List Aff2Run)
  | [] => some []
  | r :: rs =>
    match r.count.shiftJ?, shiftStackJ rs with
    | some c', some rs' => some (⟨r.wid, c'⟩ :: rs')
    | _, _ => none

/-- Evaluate an `Aff2Run` stack at loop completion `j = K.eval k`. -/
def evalStackEnd (K : AffNat) : List Aff2Run → Option (List AffRun)
  | [] => some []
  | r :: rs =>
    match r.count.atEnd? K, evalStackEnd K rs with
    | some c', some rs' =>
      if c'.geConst 1 then some (⟨r.wid, c'⟩ :: rs') else none
    | _, _ => none

/-- Verify a `K(k)`-iteration inner cycle of `L` RLE steps from `c`, returning total affine steps
`K.scale dtIter` and the post-cycle `AffCfg`. -/
def verifyCycle (numStates : ℕ) (exits : NatTrie CompExit) (L : ℕ) (K : AffNat)
    (deltas : List (ℕ × ℕ)) (c : AffCfg) : Option (AffNat × AffCfg) :=
  if !K.geConst 1 then none
  else
    match attachDeltas c.left deltas with
    | none => none
    | some (l₂, dsRem) =>
      match attachDeltas c.right dsRem with
      | none => none
      | some (r₂, []) =>
        let initOk :=
          l₂.all (fun r ↦ r.count.geForLoop K 1) &&
          r₂.all (fun r ↦ r.count.geForLoop K 1)
        if !initOk then none
        else
          let c₀ : Aff2Cfg := ⟨c.q, c.dir, l₂, r₂⟩
          match runAff2Steps numStates exits K L 0 c₀, shiftStackJ l₂, shiftStackJ r₂ with
          | some (dtIter, c₁), some lShift, some rShift =>
            if c₁ == ⟨c.q, c.dir, lShift, rShift⟩ then
              match evalStackEnd K l₂, evalStackEnd K r₂ with
              | some lEnd, some rEnd =>
                (K.scale dtIter).strict fun dtTot ↦
                  some (dtTot, mkStrictAffCfg c.q c.dir lEnd rEnd)
              | _, _ => none
            else none
          | _, _, _ => none
      | some (_, _ :: _) => none

/-! ## Certificate Replay (`AffOp`, `ReturnCert`, `replayAffTree`) -/

/-- Certificate operation: either `n` affine RLE steps or a `K(k)`-iteration inner cycle. -/
inductive AffOp where
  /-- Execute `n` consecutive `stepAffOnce` steps. -/
  | steps (n : ℕ) : AffOp
  /-- Execute a `K`-iteration cycle of `L` steps with stack slopes `deltas`. -/
  | cycle (L : ℕ) (K : AffNat) (deltas : List (ℕ × ℕ)) : AffOp
  deriving DecidableEq, Inhabited

/-- Self-contained direct-trie symbolic return certificate. -/
structure ReturnCert where
  /-- Composite word vocabulary (`wid ↦ BTree` of base-word indices). -/
  vocab : NatTrie (BTree ℕ)
  /-- Certified composite word exits keyed by `compKey numStates wid q dir`. -/
  exits : NatTrie CompExit
  /-- Balanced binary tree of certificate operations. -/
  ops : BTree AffOp
  deriving DecidableEq, Inhabited

/-- Execute `n` consecutive `stepAffOnce` transitions, accumulating total affine TM steps. -/
def runStepCount (numStates : ℕ) (exits : NatTrie CompExit) (target : AffNat) :
    ℕ → AffNat → AffCfg → Option (AffNat × AffCfg)
  | 0, acc, c => some (acc, c)
  | n + 1, acc, ⟨q, dir, l, r⟩ =>
    let rem? := target.sub? acc
    match stepAffOnce numStates exits rem? q dir l r with
    | none => none
    | some (dt, c') =>
      (acc.add dt).strict fun acc' ↦ runStepCount numStates exits target n acc' c'

/-- Replay a balanced `BTree AffOp` of symbolic affine transitions. -/
def replayAffTree (numStates : ℕ) (exits : NatTrie CompExit) (target : AffNat) :
    BTree AffOp → AffNat → AffCfg → Option (AffNat × AffCfg)
  | .empty, acc, c => some (acc, c)
  | .leaf (.steps n), acc, c => runStepCount numStates exits target n acc c
  | .leaf (.cycle L K deltas), acc, c =>
    match verifyCycle numStates exits L K deltas c with
    | none => none
    | some (dt, c') => (acc.add dt).strict fun acc' ↦ some (acc', c')
  | .node l r, acc, c =>
    match replayAffTree numStates exits target l acc c with
    | none => none
    | some (acc₁, c₁) => replayAffTree numStates exits target r acc₁ c₁

/-- Boolean check that `replayAffTree` on subtree `ops` maps `(acc, c)` to `(expAcc, expC)`. -/
def checkReplaySlice (numStates : ℕ) (exits : NatTrie CompExit) (target : AffNat)
    (ops : BTree AffOp) (acc : AffNat) (c : AffCfg) (expAcc : AffNat) (expC : AffCfg) : Bool :=
  match replayAffTree numStates exits target ops acc c with
  | none => false
  | some (acc', c') => (acc' == expAcc) && (c' == expC)

/-- Compositional subtree-sliced derivation of `replayAffTree ... = some (expAcc, expC)` enabling
bounded-memory `mkAuxTheorem` kernel verification. -/
inductive AffReplayReaches (numStates : ℕ) (exits : NatTrie CompExit) (target : AffNat) :
    BTree AffOp → AffNat → AffCfg → AffNat → AffCfg → Prop where
  /-- Leaf slice verified by `checkReplaySlice`. -/
  | slice {ops : BTree AffOp} {acc expAcc : AffNat} {c expC : AffCfg} :
      checkReplaySlice numStates exits target ops acc c expAcc expC = true →
      AffReplayReaches numStates exits target ops acc c expAcc expC
  /-- Binary node combining two verified child subtrees. -/
  | node {l r : BTree AffOp} {a₀ a₁ a₂ : AffNat} {c₀ c₁ c₂ : AffCfg} :
      AffReplayReaches numStates exits target l a₀ c₀ a₁ c₁ →
      AffReplayReaches numStates exits target r a₁ c₁ a₂ c₂ →
      AffReplayReaches numStates exits target (.node l r) a₀ c₀ a₂ c₂

theorem AffReplayReaches.to_eq {numStates : ℕ} {exits : NatTrie CompExit} {target : AffNat}
    {ops : BTree AffOp} {a₀ a₁ : AffNat} {c₀ c₁ : AffCfg}
    (h : AffReplayReaches numStates exits target ops a₀ c₀ a₁ c₁) :
    replayAffTree numStates exits target ops a₀ c₀ = some (a₁, c₁) := by
  induction h with
  | @slice ops acc expAcc c expC hs =>
    unfold checkReplaySlice at hs
    rcases hr : replayAffTree numStates exits target ops acc c with _ | ⟨a', c'⟩
    · simp [hr] at hs
    · rw [hr] at hs
      simp only [Bool.and_eq_true] at hs
      have ha : a' = expAcc := eq_of_beq hs.1
      have hc : c' = expC := eq_of_beq hs.2
      subst ha; subst hc; rfl
  | node _ _ ihl ihr =>
    simp [replayAffTree, ihl, ihr]

/-! ## Semantic Evaluation and Soundness Theorems -/

section Semantics

variable {Γ : Type*}

/-- Expand composite word `wid` in `vocab` into `List Γ` via `baseWord`. -/
def vocabWord (baseWord : ℕ → List Γ) (vocab : NatTrie (BTree ℕ)) (wid : ℕ) : List Γ :=
  match vocab.find? wid with
  | some t => concatSubwords baseWord t.toList
  | none => []

theorem vocabWord_zero_blank [Inhabited Γ] {baseWord : ℕ → List Γ}
    (hb0 : ∀ x ∈ baseWord 0, x = default) {vocab : NatTrie (BTree ℕ)}
    (hv0 : checkVocabBlank0 vocab = true) :
    ∀ x ∈ vocabWord baseWord vocab 0, x = default := by
  unfold checkVocabBlank0 at hv0
  unfold vocabWord
  rcases hf : vocab.find? 0 with _ | t
  · intro x hx; cases hx
  · rw [hf] at hv0
    have hall : ∀ s ∈ t.toList, Nat.beq s 0 = true := List.all_eq_true.mp hv0
    have hrec : ∀ (ss : List ℕ), (∀ s ∈ ss, Nat.beq s 0 = true) →
        ∀ x ∈ concatSubwords baseWord ss, x = default := by
      intro ss hss
      induction ss with
      | nil => intro x hx; cases hx
      | cons s ss ih =>
        intro x hx
        simp only [concatSubwords, List.mem_append] at hx
        rcases hx with hx1 | hx2
        · have hs0 : s = 0 := Nat.eq_of_beq_eq_true (hss s List.mem_cons_self)
          subst hs0
          exact hb0 x hx1
        · exact ih (fun y hy ↦ hss y (List.mem_cons_of_mem _ hy)) x hx2
    exact hrec t.toList hall

end Semantics

section MachineSoundness

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Evaluate a symbolic `AffRun` stack at parameter `k` on half-tape `side`. -/
def evalAffSide (side : Bool) (wordOf : ℕ → List Γ) (k : ℕ) : List AffRun → ListBlank Γ
  | [] => default
  | ⟨w, c⟩ :: rest =>
    if side then ListBlank.append (wordOf w ^ c.eval k) (evalAffSide true wordOf k rest)
    else ListBlank.append ((wordOf w).reverse ^ c.eval k) (evalAffSide false wordOf k rest)

/-- Evaluate a symbolic `AffCfg` at parameter `k` into `BusyBeaver.Cfg Γ Λ`. -/
def evalAffCfg (qOf : ℕ → Λ) (wordOf : ℕ → List Γ) (k : ℕ) (c : AffCfg) : Cfg Γ Λ :=
  dirCfg qOf c.q c.dir (evalAffSide false wordOf k c.left) (evalAffSide true wordOf k c.right)

/-- Evaluate a two-variable `Aff2Run` stack at `(k, j)` on half-tape `side`. -/
def evalAff2Side (side : Bool) (wordOf : ℕ → List Γ) (k j : ℕ) : List Aff2Run → ListBlank Γ
  | [] => default
  | ⟨w, c⟩ :: rest =>
    if side then ListBlank.append (wordOf w ^ c.eval k j) (evalAff2Side true wordOf k j rest)
    else ListBlank.append ((wordOf w).reverse ^ c.eval k j) (evalAff2Side false wordOf k j rest)

/-- Evaluate a two-variable `Aff2Cfg` at `(k, j)` into `BusyBeaver.Cfg Γ Λ`. -/
def evalAff2Cfg (qOf : ℕ → Λ) (wordOf : ℕ → List Γ) (k j : ℕ) (c : Aff2Cfg) : Cfg Γ Λ :=
  dirCfg qOf c.q c.dir (evalAff2Side false wordOf k j c.left) (evalAff2Side true wordOf k j c.right)

private def topWid : List AffRun → ℕ
  | [] => 0
  | top :: _ => top.wid

private def topWid2 : List Aff2Run → ℕ
  | [] => 0
  | top :: _ => top.wid

private theorem popAff_sound {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    {count : AffNat} {stk stk' : List AffRun} {w : ℕ}
    (hp : popAff count stk = some (w, stk')) (side : Bool) (k : ℕ) :
    w = topWid stk ∧
      evalAffSide side wordOf k stk =
        if side then ListBlank.append (wordOf w ^ count.eval k) (evalAffSide true wordOf k stk')
        else ListBlank.append ((wordOf w).reverse ^ count.eval k)
          (evalAffSide false wordOf k stk') := by
  have hzRev : ∀ x ∈ (wordOf 0).reverse, x = default :=
    fun x hx ↦ hz x (List.mem_reverse.mp hx)
  unfold popAff popAffK id at hp
  rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
  · by_cases h1 : count.isOne = true
    · simp only [h1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      refine ⟨rfl, ?_⟩
      have hc1 := AffNat.eval_eq_one_of_isOne h1 k
      cases side <;> simp [evalAffSide, hc1, lb_blank_word _ hz, lb_blank_word _ hzRev]
    · have hn1 := Bool.eq_false_iff.mpr h1
      simp [hn1] at hp
  · simp only at hp
    rcases hs : tc.sub? count with _ | rem
    · simp [hs] at hp
    · rw [hs] at hp
      simp only at hp
      have hsub := AffNat.eval_sub? hs k
      by_cases hrz : rem.isZero = true
      · simp only [hrz, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        have hr0 := AffNat.eval_eq_zero_of_isZero hrz k
        have htc : tc.eval k = count.eval k := by omega
        refine ⟨rfl, ?_⟩
        cases side <;> simp [evalAffSide, htc]
      · have hnrz := Bool.eq_false_iff.mpr hrz
        rw [hnrz] at hp
        by_cases hrg : rem.geConst 1 = true
        · simp only [Bool.false_eq_true, ↓reduceIte, hrg, AffNat.strict_eq,
            Option.some.injEq, Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩
          refine ⟨rfl, ?_⟩
          cases side <;>
            simp [evalAffSide, hsub, list_pow_add, ListBlank.append_assoc]
        · have hnrg := Bool.eq_false_iff.mpr hrg
          simp [hnrg] at hp

private theorem pushAff_sound {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    {wid : ℕ} {count : AffNat} {stk stk' : List AffRun}
    (hp : pushAff wid count stk = some stk') (side : Bool) (k : ℕ) :
    evalAffSide side wordOf k stk' =
      if side then ListBlank.append (wordOf wid ^ count.eval k) (evalAffSide true wordOf k stk)
      else ListBlank.append ((wordOf wid).reverse ^ count.eval k)
        (evalAffSide false wordOf k stk) := by
  have hzRev : ∀ x ∈ (wordOf 0).reverse, x = default :=
    fun x hx ↦ hz x (List.mem_reverse.mp hx)
  unfold pushAff pushAffK id at hp
  by_cases hcz : count.isZero = true
  · simp only [hcz, ↓reduceIte, Option.some.injEq] at hp
    subst hp
    have hc0 := AffNat.eval_eq_zero_of_isZero hcz k
    cases side <;> simp [hc0]
  · have hncz := Bool.eq_false_iff.mpr hcz
    rw [hncz] at hp
    rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp
      by_cases hw : Nat.beq wid 0 = true
      · simp only [hw, ↓reduceIte, Option.some.injEq] at hp
        subst hp
        have hw0 := Nat.eq_of_beq_eq_true hw
        subst hw0
        cases side <;> simp [evalAffSide, lb_blank_pow _ hz, lb_blank_pow _ hzRev]
      · have hnw := Bool.eq_false_iff.mpr hw
        rw [hnw] at hp
        by_cases hg : count.geConst 1 = true
        · simp only [Bool.false_eq_true, ↓reduceIte, hg, withNat_eq, AffNat.strict_eq,
            Option.some.injEq] at hp
          subst hp
          cases side <;> rfl
        · have hng := Bool.eq_false_iff.mpr hg
          simp [hng] at hp
    · simp only [Bool.false_eq_true, ↓reduceIte] at hp
      by_cases hg : count.geConst 1 = true
      · simp only [hg, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hp
        by_cases hw : Nat.beq tw wid = true
        · simp only [hw, ↓reduceIte, AffNat.strict_eq, Option.some.injEq] at hp
          subst hp
          have htw := Nat.eq_of_beq_eq_true hw
          subst htw
          cases side <;>
            simp [evalAffSide, ListBlank.append_append, ← list_pow_add, Nat.add_comm]
        · have hnw := Bool.eq_false_iff.mpr hw
          simp only [hnw, Bool.false_eq_true, ↓reduceIte, withNat_eq, AffNat.strict_eq,
            Option.some.injEq] at hp
          subst hp
          cases side <;> rfl
      · have hng := Bool.eq_false_iff.mpr hg
        simp [hng] at hp

private theorem lookup_exit_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {wid q : ℕ} {dir : Bool} {ex : CompExit}
    (hq : q < numStates) (hf : exits.find? (compKey numStates wid q dir) = some ex) :
    WordExit M qOf (vocabWord baseWord vocab wid) q dir
      (vocabWord baseWord vocab ex.wid') ex.q' ex.dir' ex.dt := by
  have hchk := NatTrie.checkAll_sound hexits hf
  unfold checkExitEntry at hchk
  have hstride : Nat.beq (2 * numStates) 0 = false := by
    apply Bool.eq_false_iff.mpr
    intro h0
    have := Nat.eq_of_beq_eq_true h0
    omega
  simp only [hstride, Bool.false_eq_true, ↓reduceIte] at hchk
  have hd_lt : q * 2 + (if dir then 1 else 0) < 2 * numStates := by
    cases dir <;> simp <;> omega
  have hdiv : compKey numStates wid q dir / (2 * numStates) = wid := by
    unfold compKey
    have hpos : 0 < 2 * numStates := by omega
    calc
      (wid * (2 * numStates) + q * 2 + if dir then 1 else 0) / (2 * numStates)
        = ((q * 2 + if dir then 1 else 0) + wid * (2 * numStates)) / (2 * numStates) := by
            congr 1; omega
      _ = (q * 2 + if dir then 1 else 0) / (2 * numStates) + wid :=
            Nat.add_mul_div_right _ _ hpos
      _ = wid := by rw [Nat.div_eq_of_lt hd_lt, Nat.zero_add]
  have hmod : compKey numStates wid q dir % (2 * numStates) = q * 2 + (if dir then 1 else 0) := by
    unfold compKey
    calc
      (wid * (2 * numStates) + q * 2 + if dir then 1 else 0) % (2 * numStates)
        = ((q * 2 + if dir then 1 else 0) + wid * (2 * numStates)) % (2 * numStates) := by
            congr 1; omega
      _ = (q * 2 + if dir then 1 else 0) % (2 * numStates) := Nat.add_mul_mod_self_right _ _ _
      _ = q * 2 + (if dir then 1 else 0) := Nat.mod_eq_of_lt hd_lt
  have hq_eq : (q * 2 + if dir then 1 else 0) / 2 = q := by
    cases dir
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
      omega
    · simp only [↓reduceIte]
      omega
  have hdir_eq : Nat.beq ((q * 2 + if dir then 1 else 0) % 2) 1 = dir := by
    cases dir
    · simp only [Bool.false_eq_true, ↓reduceIte, add_zero, Nat.mul_mod_left]
      rfl
    · simp only [↓reduceIte]
      exact Nat.beq_eq.mpr (by omega)
  rw [hdiv, hmod, hq_eq, hdir_eq] at hchk
  rcases hu : vocab.find? wid with _ | uTree
  · simp [hu] at hchk
  · rcases hv : vocab.find? ex.wid' with _ | vTree
    · simp [hu, hv] at hchk
    · rw [hu, hv] at hchk
      have hrun : runCompositeExit baseExit uTree.toList q dir =
          some (vTree.toList, ex.q', ex.dir', ex.dt) := eq_of_beq hchk
      have hex := runCompositeExit_sound hbase hrun
      simpa [vocabWord, hu, hv] using hex

private theorem wordExit_apply_aff {M : Machine Γ Λ} {qOf : ℕ → Λ} {wordOf : ℕ → List Γ}
    {wid wid' q q' : ℕ} {dir dir' : Bool} {exDt : ℕ} {count : AffNat}
    (hz : ∀ x ∈ wordOf 0, x = default)
    (hex : WordExit M qOf (wordOf wid) q dir (wordOf wid') q' dir' exDt)
    (hsame : (Nat.beq q' q && Bool.beq dir' dir) = true ∨ count = ⟨0, 1⟩)
    {l r l₂ r₂ : List AffRun}
    (hstep_stacks :
      if dir then
        ∃ r', popAff count r = some (wid, r') ∧
          if dir' then pushAff wid' count l = some l₂ ∧ r₂ = r'
          else l₂ = l ∧ pushAff wid' count r' = some r₂
      else
        ∃ l', popAff count l = some (wid, l') ∧
          if dir' then pushAff wid' count l' = some l₂ ∧ r₂ = r
          else l₂ = l' ∧ pushAff wid' count r = some r₂)
    (k : ℕ) :
    ReachesIn M ((count.scale exDt).eval k)
      (evalAffCfg qOf wordOf k ⟨q, dir, l, r⟩)
      (evalAffCfg qOf wordOf k ⟨q', dir', l₂, r₂⟩) := by
  have hexPow : WordExit M qOf (wordOf wid ^ count.eval k) q dir
      (wordOf wid' ^ count.eval k) q' dir' ((count.scale exDt).eval k) := by
    rcases hsame with hs | rfl
    · simp only [Bool.and_eq_true] at hs
      have hqq : q' = q := Nat.eq_of_beq_eq_true hs.1
      have hdd : dir' = dir := eq_of_beq hs.2
      subst hqq; subst hdd
      rw [AffNat.eval_scale]
      exact sweepWord_sound hex (count.eval k)
    · have hc1 : (AffNat.mk 0 1).eval k = 1 := by simp [AffNat.eval]
      have hsc : ((AffNat.mk 0 1).scale exDt).eval k = exDt := by simp [AffNat.scale, AffNat.eval]
      rw [hc1, hsc, list_pow_one, list_pow_one]
      exact hex
  unfold evalAffCfg
  simp only
  cases dir
  · simp only [Bool.false_eq_true, ↓reduceIte] at hstep_stacks
    obtain ⟨l', hpop, hpush⟩ := hstep_stacks
    have ⟨_, hpopEq⟩ := popAff_sound hz hpop false k
    simp only [Bool.false_eq_true, ↓reduceIte] at hpopEq
    have hrun := hexPow (evalAffSide false wordOf k l') (evalAffSide true wordOf k r)
    simp only [placeSide, Bool.false_eq_true, ↓reduceIte, reverse_pow] at hrun
    rw [hpopEq]
    cases dir'
    · simp only [Bool.false_eq_true, ↓reduceIte] at hpush
      rcases hpush with ⟨rfl, hpushR⟩
      have hpushEq := pushAff_sound hz hpushR true k
      simp only [↓reduceIte] at hpushEq
      simp only [Bool.not_false, ↓reduceIte] at hrun
      rwa [hpushEq]
    · simp only [↓reduceIte] at hpush
      rcases hpush with ⟨hpushL, rfl⟩
      have hpushEq := pushAff_sound hz hpushL false k
      simp only [Bool.false_eq_true, ↓reduceIte] at hpushEq
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
      rwa [hpushEq]
  · simp only [↓reduceIte] at hstep_stacks
    obtain ⟨r', hpop, hpush⟩ := hstep_stacks
    have ⟨_, hpopEq⟩ := popAff_sound hz hpop true k
    simp only [↓reduceIte] at hpopEq
    have hrun := hexPow (evalAffSide false wordOf k l) (evalAffSide true wordOf k r')
    simp only [placeSide, ↓reduceIte] at hrun
    rw [hpopEq]
    cases dir'
    · simp only [Bool.false_eq_true, ↓reduceIte] at hpush
      rcases hpush with ⟨rfl, hpushR⟩
      have hpushEq := pushAff_sound hz hpushR true k
      simp only [↓reduceIte] at hpushEq
      simp only [Bool.not_false, ↓reduceIte] at hrun
      rwa [hpushEq]
    · simp only [↓reduceIte] at hpush
      rcases hpush with ⟨hpushL, rfl⟩
      have hpushEq := pushAff_sound hz hpushL false k
      simp only [Bool.false_eq_true, ↓reduceIte] at hpushEq
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, reverse_pow] at hrun
      rwa [hpushEq]

/-- Soundness of `stepAffOnce`. -/
theorem stepAffOnce_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {rem? : Option AffNat} {q : ℕ} {dir : Bool} {l r : List AffRun}
    {dt : AffNat} {c' : AffCfg}
    (hst : stepAffOnce numStates exits rem? q dir l r = some (dt, c')) (k : ℕ) :
    ReachesIn M (dt.eval k)
      (evalAffCfg qOf (vocabWord baseWord vocab) k ⟨q, dir, l, r⟩)
      (evalAffCfg qOf (vocabWord baseWord vocab) k c') := by
  have hz := vocabWord_zero_blank hb0 hv0
  unfold stepAffOnce at hst
  by_cases hqb : Nat.ble (q + 1) numStates = true
  · simp only [hqb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hst
    have hq : q < numStates := Nat.le_of_ble_eq_true hqb
    set src := if dir then r else l
    set wid := match src with | [] => 0 | top :: _ => top.wid
    rcases hf : exits.find? (compKey numStates wid q dir) with _ | ex
    · simp [hf] at hst
    · rw [hf] at hst
      have hex := lookup_exit_sound hbase hexits hq hf
      have hcnt : ∃ count : AffNat,
          ((Nat.beq ex.q' q && Bool.beq ex.dir' dir) = true ∨ count = ⟨0, 1⟩) ∧
          (if dir then
            popAffK count r fun
              | none => none
              | some (_, r') =>
                (count.scale ex.dt).strict fun dt ↦
                  if ex.dir' then
                    pushAffK ex.wid' count l fun
                      | none => none
                      | some l₂ => some (dt, mkStrictAffCfg ex.q' true l₂ r')
                  else
                    pushAffK ex.wid' count r' fun
                      | none => none
                      | some r₂ => some (dt, mkStrictAffCfg ex.q' false l r₂)
          else
            popAffK count l fun
              | none => none
              | some (_, l') =>
                (count.scale ex.dt).strict fun dt ↦
                  if ex.dir' then
                    pushAffK ex.wid' count l' fun
                      | none => none
                      | some l₂ => some (dt, mkStrictAffCfg ex.q' true l₂ r)
                  else
                    pushAffK ex.wid' count r fun
                      | none => none
                      | some r₂ => some (dt, mkStrictAffCfg ex.q' false l' r₂)) =
              some (dt, c') := by
        simp only at hst
        by_cases hsm : (Nat.beq ex.q' q && Bool.beq ex.dir' dir) = true
        · simp only [hsm, ↓reduceIte] at hst
          rcases hsrc : src with _ | ⟨top, rest⟩
          · simp [hsrc] at hst
          · rw [hsrc] at hst
            cases rem? with
            | none => exact ⟨top.count, Or.inl hsm, hst⟩
            | some rem =>
              simp only at hst
              by_cases hc1 :
                  (Nat.ble 1 ex.dt && Nat.beq (rem.a % ex.dt) 0 && Nat.beq (rem.b % ex.dt) 0) = true
              · simp only [hc1, ↓reduceIte] at hst
                by_cases hc2 :
                    ((AffNat.mk (rem.a / ex.dt) (rem.b / ex.dt)).geConst 1 &&
                      (top.count.sub? ⟨rem.a / ex.dt, rem.b / ex.dt⟩).isSome) = true
                · simp only [hc2, ↓reduceIte] at hst
                  exact ⟨_, Or.inl hsm, hst⟩
                · have hnc2 := Bool.eq_false_iff.mpr hc2
                  simp only [hnc2, Bool.false_eq_true, ↓reduceIte] at hst
                  exact ⟨top.count, Or.inl hsm, hst⟩
              · have hnc1 := Bool.eq_false_iff.mpr hc1
                simp only [hnc1, Bool.false_eq_true, ↓reduceIte] at hst
                exact ⟨top.count, Or.inl hsm, hst⟩
        · have hnsm := Bool.eq_false_iff.mpr hsm
          simp only [hnsm, Bool.false_eq_true, ↓reduceIte] at hst
          exact ⟨⟨0, 1⟩, Or.inr rfl, hst⟩
      obtain ⟨count, hsame, hbody⟩ := hcnt
      cases dir
      · simp only [Bool.false_eq_true, ↓reduceIte, popAffK_eq] at hbody
        rcases hpop : popAff count l with _ | ⟨pw, l'⟩
        · simp [hpop] at hbody
        · rw [hpop] at hbody
          simp only [AffNat.strict_eq] at hbody
          have ⟨hpw, _⟩ := popAff_sound hz hpop false k
          have hpwid : pw = wid := by
            simpa [wid, src, topWid] using hpw
          subst hpwid
          cases hdir' : ex.dir'
          · simp only [hdir', Bool.false_eq_true, ↓reduceIte, pushAffK_eq,
              mkStrictAffCfg_eq] at hbody
            rcases hpush : pushAff ex.wid' count r with _ | r₂
            · simp [hpush] at hbody
            · rw [hpush] at hbody
              simp only [Option.some.injEq, Prod.mk.injEq] at hbody
              rcases hbody with ⟨rfl, rfl⟩
              rw [hdir'] at hex hsame
              refine wordExit_apply_aff hz hex hsame ?_ k
              exact ⟨l', hpop, rfl, hpush⟩
          · simp only [hdir', ↓reduceIte, pushAffK_eq, mkStrictAffCfg_eq] at hbody
            rcases hpush : pushAff ex.wid' count l' with _ | l₂
            · simp [hpush] at hbody
            · rw [hpush] at hbody
              simp only [Option.some.injEq, Prod.mk.injEq] at hbody
              rcases hbody with ⟨rfl, rfl⟩
              rw [hdir'] at hex hsame
              refine wordExit_apply_aff hz hex hsame ?_ k
              exact ⟨l', hpop, hpush, rfl⟩
      · simp only [↓reduceIte, popAffK_eq] at hbody
        rcases hpop : popAff count r with _ | ⟨pw, r'⟩
        · simp [hpop] at hbody
        · rw [hpop] at hbody
          simp only [AffNat.strict_eq] at hbody
          have ⟨hpw, _⟩ := popAff_sound hz hpop true k
          have hpwid : pw = wid := by
            simpa [wid, src, topWid] using hpw
          subst hpwid
          cases hdir' : ex.dir'
          · simp only [hdir', Bool.false_eq_true, ↓reduceIte, pushAffK_eq,
              mkStrictAffCfg_eq] at hbody
            rcases hpush : pushAff ex.wid' count r' with _ | r₂
            · simp [hpush] at hbody
            · rw [hpush] at hbody
              simp only [Option.some.injEq, Prod.mk.injEq] at hbody
              rcases hbody with ⟨rfl, rfl⟩
              rw [hdir'] at hex hsame
              refine wordExit_apply_aff hz hex hsame ?_ k
              exact ⟨r', hpop, rfl, hpush⟩
          · simp only [hdir', ↓reduceIte, pushAffK_eq, mkStrictAffCfg_eq] at hbody
            rcases hpush : pushAff ex.wid' count l with _ | l₂
            · simp [hpush] at hbody
            · rw [hpush] at hbody
              simp only [Option.some.injEq, Prod.mk.injEq] at hbody
              rcases hbody with ⟨rfl, rfl⟩
              rw [hdir'] at hex hsame
              refine wordExit_apply_aff hz hex hsame ?_ k
              exact ⟨r', hpop, hpush, rfl⟩
  · have hnqb := Bool.eq_false_iff.mpr hqb
    simp [hnqb] at hst

/-! ### Soundness of Inner-Cycle Verifier (`verifyCycle_sound`) -/

private def stackWF (K : AffNat) (stk : List Aff2Run) : Prop :=
  ∀ r ∈ stk, r.count.geForLoop K 1 = true

private theorem popAff2_const_sound {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    {K : AffNat} {cntVal : ℕ} {stk stk' : List Aff2Run} {w : ℕ}
    (hwf : stackWF K stk)
    (hp : popAff2 K ⟨0, cntVal, 0, 0⟩ stk = some (w, stk'))
    (side : Bool) {k j : ℕ} (hj : j < K.eval k) :
    stackWF K stk' ∧
      w = topWid2 stk ∧
      evalAff2Side side wordOf k j stk =
        if side then ListBlank.append (wordOf w ^ cntVal) (evalAff2Side true wordOf k j stk')
        else ListBlank.append ((wordOf w).reverse ^ cntVal)
          (evalAff2Side false wordOf k j stk') := by
  have hzRev : ∀ x ∈ (wordOf 0).reverse, x = default :=
    fun x hx ↦ hz x (List.mem_reverse.mp hx)
  unfold popAff2 at hp
  rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
  · by_cases hc1 : (Aff2Nat.mk 0 cntVal 0 0 == Aff2Nat.mk 0 1 0 0) = true
    · simp only [hc1, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
      rcases hp with ⟨rfl, rfl⟩
      have h1 : Aff2Nat.mk 0 cntVal 0 0 = Aff2Nat.mk 0 1 0 0 := eq_of_beq hc1
      injection h1 with _ hcv _ _
      subst hcv
      refine ⟨(fun r hr ↦ by cases hr), rfl, ?_⟩
      cases side <;> simp [evalAff2Side, lb_blank_word _ hz, lb_blank_word _ hzRev]
    · have hnc1 := Bool.eq_false_iff.mpr hc1
      simp [hnc1] at hp
  · simp only at hp
    rcases hs : tc.sub? ⟨0, cntVal, 0, 0⟩ K with _ | rem
    · simp [hs] at hp
    · rw [hs] at hp
      simp only at hp
      have hsub := Aff2Nat.sub_const_eval hs hj
      have hwfRest : stackWF K rest := fun r hr ↦ hwf r (List.mem_cons_of_mem _ hr)
      by_cases hrz : rem.isZero = true
      · simp only [hrz, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hp
        rcases hp with ⟨rfl, rfl⟩
        have hr0 := Aff2Nat.eval_eq_zero_of_isZero hrz k j
        have htc : tc.eval k j = cntVal := by omega
        refine ⟨hwfRest, rfl, ?_⟩
        cases side <;> simp [evalAff2Side, htc]
      · have hnrz := Bool.eq_false_iff.mpr hrz
        rw [hnrz] at hp
        by_cases hrg : rem.geForLoop K 1 = true
        · simp only [Bool.false_eq_true, ↓reduceIte, hrg, Option.some.injEq, Prod.mk.injEq] at hp
          rcases hp with ⟨rfl, rfl⟩
          have hwfNew : stackWF K (⟨tw, rem⟩ :: rest) := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hmem
            · exact hrg
            · exact hwfRest r hmem
          refine ⟨hwfNew, rfl, ?_⟩
          cases side <;> simp [evalAff2Side, hsub, list_pow_add, ListBlank.append_assoc]
        · have hnrg := Bool.eq_false_iff.mpr hrg
          simp [hnrg] at hp

private theorem pushAff2_const_sound {wordOf : ℕ → List Γ} (hz : ∀ x ∈ wordOf 0, x = default)
    {K : AffNat} {wid cntVal : ℕ} {stk stk' : List Aff2Run}
    (hwf : stackWF K stk)
    (hp : pushAff2 K wid ⟨0, cntVal, 0, 0⟩ stk = some stk')
    (side : Bool) {k j : ℕ} (hj : j < K.eval k) :
    stackWF K stk' ∧
      evalAff2Side side wordOf k j stk' =
        if side then ListBlank.append (wordOf wid ^ cntVal) (evalAff2Side true wordOf k j stk)
        else ListBlank.append ((wordOf wid).reverse ^ cntVal)
          (evalAff2Side false wordOf k j stk) := by
  have hzRev : ∀ x ∈ (wordOf 0).reverse, x = default :=
    fun x hx ↦ hz x (List.mem_reverse.mp hx)
  unfold pushAff2 at hp
  by_cases hcz : (Aff2Nat.mk 0 cntVal 0 0).isZero = true
  · simp only [hcz, ↓reduceIte, Option.some.injEq] at hp
    subst hp
    have hc0 : cntVal = 0 := by
      have := Aff2Nat.eval_eq_zero_of_isZero hcz 0 0
      simpa [Aff2Nat.eval] using this
    subst hc0
    refine ⟨hwf, ?_⟩
    cases side <;> simp
  · have hncz := Bool.eq_false_iff.mpr hcz
    rw [hncz] at hp
    by_cases hg : (Aff2Nat.mk 0 cntVal 0 0).geForLoop K 1 = true
    · simp only [Bool.false_eq_true, ↓reduceIte, hg, Bool.not_true] at hp
      rcases stk with _ | ⟨⟨tw, tc⟩, rest⟩
      · by_cases hw : Nat.beq wid 0 = true
        · simp only [hw, ↓reduceIte, Option.some.injEq] at hp
          subst hp
          have hw0 := Nat.eq_of_beq_eq_true hw
          subst hw0
          refine ⟨(fun r hr ↦ by cases hr), ?_⟩
          cases side <;> simp [evalAff2Side, lb_blank_pow _ hz, lb_blank_pow _ hzRev]
        · have hnw := Bool.eq_false_iff.mpr hw
          simp only [hnw, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hp
          subst hp
          have hwf1 : stackWF K [⟨wid, ⟨0, cntVal, 0, 0⟩⟩] := by
            intro r hr
            rcases List.mem_singleton.mp hr with rfl
            exact hg
          have hcv : (Aff2Nat.mk 0 cntVal 0 0).eval k j = cntVal := by simp [Aff2Nat.eval]
          refine ⟨hwf1, ?_⟩
          cases side <;> simp [evalAff2Side, hcv]
      · simp only at hp
        by_cases hw : Nat.beq tw wid = true
        · simp only [hw, ↓reduceIte, Option.some.injEq] at hp
          subst hp
          have htw := Nat.eq_of_beq_eq_true hw
          subst htw
          have htcwf : tc.geForLoop K 1 = true := hwf _ List.mem_cons_self
          have hno : tc.dn * j ≤ tc.a * k + tc.b + tc.dp * j := by
            have := Aff2Nat.noUnderflow_of_geForLoop htcwf hj
            omega
          have haddEq := Aff2Nat.add_const_eval tc cntVal k j hno
          have hwfNew : stackWF K (⟨tw, tc.add ⟨0, cntVal, 0, 0⟩⟩ :: rest) := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hmem
            · exact Aff2Nat.add_const_geForLoop htcwf
            · exact hwf r (List.mem_cons_of_mem _ hmem)
          refine ⟨hwfNew, ?_⟩
          cases side <;>
            simp [evalAff2Side, haddEq, ListBlank.append_append, ← list_pow_add, Nat.add_comm]
        · have hnw := Bool.eq_false_iff.mpr hw
          simp only [hnw, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hp
          subst hp
          have hwfNew : stackWF K (⟨wid, ⟨0, cntVal, 0, 0⟩⟩ :: ⟨tw, tc⟩ :: rest) := by
            intro r hr
            rcases List.mem_cons.mp hr with rfl | hmem
            · exact hg
            · exact hwf r hmem
          have hcv : (Aff2Nat.mk 0 cntVal 0 0).eval k j = cntVal := by simp [Aff2Nat.eval]
          refine ⟨hwfNew, ?_⟩
          cases side <;> simp [evalAff2Side, hcv]
    · have hng := Bool.eq_false_iff.mpr hg
      simp [hng] at hp

private theorem stepAff2Once_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {K : AffNat} {c c' : Aff2Cfg} {dt : ℕ}
    (hwfL : stackWF K c.left) (hwfR : stackWF K c.right)
    (hst : stepAff2Once numStates exits K c = some (dt, c'))
    {k j : ℕ} (hj : j < K.eval k) :
    stackWF K c'.left ∧ stackWF K c'.right ∧
      ReachesIn M dt
        (evalAff2Cfg qOf (vocabWord baseWord vocab) k j c)
        (evalAff2Cfg qOf (vocabWord baseWord vocab) k j c') := by
  have hz := vocabWord_zero_blank hb0 hv0
  rcases c with ⟨q, dir, l, r⟩
  unfold stepAff2Once at hst
  simp only at hst
  by_cases hqb : Nat.ble (q + 1) numStates = true
  · simp only [hqb, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hst
    have hq : q < numStates := Nat.le_of_ble_eq_true hqb
    set src := if dir then r else l
    set wid := match src with | [] => 0 | top :: _ => top.wid
    rcases hf : exits.find? (compKey numStates wid q dir) with _ | ex
    · simp [hf] at hst
    · rw [hf] at hst
      have hex := lookup_exit_sound hbase hexits hq hf
      have hcnt : ∃ count : Aff2Nat,
          ((Nat.beq ex.q' q && Bool.beq ex.dir' dir) = true ∨ count = ⟨0, 1, 0, 0⟩) ∧
          (match count.isConst with
          | none => none
          | some cntVal =>
            match popAff2 K count src with
            | none => none
            | some (_, src') =>
              let l₁ := if dir then l else src'
              let r₁ := if dir then src' else r
              let dst? :=
                if ex.dir' then (pushAff2 K ex.wid' count l₁).map fun l₂ ↦ (l₂, r₁)
                else (pushAff2 K ex.wid' count r₁).map fun r₂ ↦ (l₁, r₂)
              match dst? with
              | none => none
              | some (l₂, r₂) =>
                withNat (cntVal * ex.dt) fun dt ↦
                  some (dt, ⟨ex.q', ex.dir', l₂, r₂⟩)) = some (dt, c') := by
        simp only at hst
        by_cases hsm : (Nat.beq ex.q' q && Bool.beq ex.dir' dir) = true
        · simp only [hsm, ↓reduceIte] at hst
          rcases hsrc : src with _ | ⟨top, rest⟩
          · simp [hsrc] at hst
          · rw [hsrc] at hst
            exact ⟨top.count, Or.inl hsm, hst⟩
        · have hnsm := Bool.eq_false_iff.mpr hsm
          simp only [hnsm, Bool.false_eq_true, ↓reduceIte] at hst
          exact ⟨⟨0, 1, 0, 0⟩, Or.inr rfl, hst⟩
      obtain ⟨count, hsame, hbody⟩ := hcnt
      rcases hconst : count.isConst with _ | cntVal
      · simp [hconst] at hbody
      · rw [hconst] at hbody
        have hce := Aff2Nat.isConst_eq hconst
        subst hce
        have hexPow : WordExit M qOf (vocabWord baseWord vocab wid ^ cntVal) q dir
            (vocabWord baseWord vocab ex.wid' ^ cntVal) ex.q' ex.dir' (cntVal * ex.dt) := by
          rcases hsame with hs | h1
          · simp only [Bool.and_eq_true] at hs
            have hqq := Nat.eq_of_beq_eq_true hs.1
            have hdd : ex.dir' = dir := eq_of_beq hs.2
            rw [hqq, hdd] at hex ⊢
            rw [Nat.mul_comm cntVal ex.dt]
            exact sweepWord_sound hex cntVal
          · injection h1 with _ hcv _ _
            subst hcv
            simpa using hex
        cases dir
        · simp only [src, Bool.false_eq_true, ↓reduceIte] at hbody
          rcases hpop : popAff2 K ⟨0, cntVal, 0, 0⟩ l with _ | ⟨pw, l'⟩
          · simp [hpop] at hbody
          · rw [hpop] at hbody
            have ⟨hwfL', hpw, hpopEq⟩ := popAff2_const_sound hz hwfL hpop false hj
            have hpwid : pw = wid := by simpa [wid, src, topWid2] using hpw
            subst hpwid
            simp only [Bool.false_eq_true, ↓reduceIte] at hpopEq
            have hrun := hexPow
              (evalAff2Side false (vocabWord baseWord vocab) k j l')
              (evalAff2Side true (vocabWord baseWord vocab) k j r)
            simp only [placeSide, Bool.false_eq_true, ↓reduceIte, reverse_pow] at hrun
            cases hdir' : ex.dir'
            · simp only [hdir', Bool.false_eq_true, ↓reduceIte] at hbody
              rcases hpush : pushAff2 K ex.wid' ⟨0, cntVal, 0, 0⟩ r with _ | r₂
              · simp [hpush] at hbody
              · simp only [hpush, Option.map_some, withNat_eq, Option.some.injEq,
                  Prod.mk.injEq] at hbody
                rcases hbody with ⟨rfl, rfl⟩
                have ⟨hwfR₂, hpushEq⟩ := pushAff2_const_sound hz hwfR hpush true hj
                simp only [↓reduceIte] at hpushEq
                simp only [hdir', Bool.not_false, ↓reduceIte] at hrun
                refine ⟨hwfL', hwfR₂, ?_⟩
                unfold evalAff2Cfg; simp only
                rw [hpopEq, hpushEq]; exact hrun
            · simp only [hdir', ↓reduceIte] at hbody
              rcases hpush : pushAff2 K ex.wid' ⟨0, cntVal, 0, 0⟩ l' with _ | l₂
              · simp [hpush] at hbody
              · simp only [hpush, Option.map_some, withNat_eq, Option.some.injEq,
                  Prod.mk.injEq] at hbody
                rcases hbody with ⟨rfl, rfl⟩
                have ⟨hwfL₂, hpushEq⟩ := pushAff2_const_sound hz hwfL' hpush false hj
                simp only [Bool.false_eq_true, ↓reduceIte] at hpushEq
                simp only [hdir', Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hrun
                refine ⟨hwfL₂, hwfR, ?_⟩
                unfold evalAff2Cfg; simp only
                rw [hpopEq, hpushEq]; exact hrun
        · simp only [src, ↓reduceIte] at hbody
          rcases hpop : popAff2 K ⟨0, cntVal, 0, 0⟩ r with _ | ⟨pw, r'⟩
          · simp [hpop] at hbody
          · rw [hpop] at hbody
            have ⟨hwfR', hpw, hpopEq⟩ := popAff2_const_sound hz hwfR hpop true hj
            have hpwid : pw = wid := by simpa [wid, src, topWid2] using hpw
            subst hpwid
            simp only [↓reduceIte] at hpopEq
            have hrun := hexPow
              (evalAff2Side false (vocabWord baseWord vocab) k j l)
              (evalAff2Side true (vocabWord baseWord vocab) k j r')
            simp only [placeSide, ↓reduceIte] at hrun
            cases hdir' : ex.dir'
            · simp only [hdir', Bool.false_eq_true, ↓reduceIte] at hbody
              rcases hpush : pushAff2 K ex.wid' ⟨0, cntVal, 0, 0⟩ r' with _ | r₂
              · simp [hpush] at hbody
              · simp only [hpush, Option.map_some, withNat_eq, Option.some.injEq,
                  Prod.mk.injEq] at hbody
                rcases hbody with ⟨rfl, rfl⟩
                have ⟨hwfR₂, hpushEq⟩ := pushAff2_const_sound hz hwfR' hpush true hj
                simp only [↓reduceIte] at hpushEq
                simp only [hdir', Bool.not_false, ↓reduceIte] at hrun
                refine ⟨hwfL, hwfR₂, ?_⟩
                unfold evalAff2Cfg; simp only
                rw [hpopEq, hpushEq]; exact hrun
            · simp only [hdir', ↓reduceIte] at hbody
              rcases hpush : pushAff2 K ex.wid' ⟨0, cntVal, 0, 0⟩ l with _ | l₂
              · simp [hpush] at hbody
              · simp only [hpush, Option.map_some, withNat_eq, Option.some.injEq,
                  Prod.mk.injEq] at hbody
                rcases hbody with ⟨rfl, rfl⟩
                have ⟨hwfL₂, hpushEq⟩ := pushAff2_const_sound hz hwfL hpush false hj
                simp only [Bool.false_eq_true, ↓reduceIte] at hpushEq
                simp only [hdir', Bool.not_true, Bool.false_eq_true, ↓reduceIte,
                  reverse_pow] at hrun
                refine ⟨hwfL₂, hwfR', ?_⟩
                unfold evalAff2Cfg; simp only
                rw [hpopEq, hpushEq]; exact hrun
  · have hnqb := Bool.eq_false_iff.mpr hqb
    simp [hnqb] at hst

private theorem runAff2Steps_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {K : AffNat} :
    ∀ (n acc : ℕ) (c : Aff2Cfg) (accOut : ℕ) (cOut : Aff2Cfg),
      stackWF K c.left → stackWF K c.right →
      runAff2Steps numStates exits K n acc c = some (accOut, cOut) →
      ∀ {k j : ℕ}, j < K.eval k →
        acc ≤ accOut ∧
          ReachesIn M (accOut - acc)
            (evalAff2Cfg qOf (vocabWord baseWord vocab) k j c)
            (evalAff2Cfg qOf (vocabWord baseWord vocab) k j cOut)
  | 0, acc, c, accOut, cOut, _, _, hrun, _, _, _ => by
    simp only [runAff2Steps, Option.some.injEq, Prod.mk.injEq] at hrun
    rcases hrun with ⟨rfl, rfl⟩
    exact ⟨Nat.le_refl acc, by simp⟩
  | n + 1, acc, c, accOut, cOut, hwfL, hwfR, hrun, k, j, hj => by
    simp only [runAff2Steps] at hrun
    rcases hst : stepAff2Once numStates exits K c with _ | ⟨dt, c'⟩
    · simp [hst] at hrun
    · rw [hst] at hrun
      simp only [withNat_eq] at hrun
      obtain ⟨hwfL', hwfR', hstep⟩ :=
        stepAff2Once_sound hbase hb0 hv0 hexits hwfL hwfR hst hj
      obtain ⟨hle, hrest⟩ :=
        runAff2Steps_sound hbase hb0 hv0 hexits n (acc + dt) c' accOut cOut hwfL' hwfR' hrun hj
      refine ⟨by omega, ?_⟩
      have hsub : accOut - acc = dt + (accOut - (acc + dt)) := by omega
      rw [hsub]
      exact hstep.trans hrest

private theorem attachDeltas_eval0 (wordOf : ℕ → List Γ) (side : Bool) (k : ℕ) :
    ∀ (stk : List AffRun) (ds ds' : List (ℕ × ℕ)) (stk₂ : List Aff2Run),
      attachDeltas stk ds = some (stk₂, ds') →
      evalAff2Side side wordOf k 0 stk₂ = evalAffSide side wordOf k stk
  | [], ds, ds', stk₂, h => by
    simp only [attachDeltas, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    rfl
  | r :: rs, [], _, _, h => by simp [attachDeltas] at h
  | r :: rs, (dp, dn) :: ds, ds', stk₂, h => by
    simp only [attachDeltas] at h
    rcases hat : attachDeltas rs ds with _ | ⟨out, rem⟩
    · simp [hat] at h
    · rw [hat] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      have ih1 := attachDeltas_eval0 wordOf true k rs ds rem out hat
      have ih0 := attachDeltas_eval0 wordOf false k rs ds rem out hat
      have hev : (Aff2Nat.mk r.count.a r.count.b dp dn).eval k 0 = r.count.eval k := by
        simp [Aff2Nat.eval, AffNat.eval]
      cases side <;> simp [evalAff2Side, evalAffSide, hev, ih1, ih0]

private theorem shiftStackJ_eval (wordOf : ℕ → List Γ) (K : AffNat) (side : Bool) {k j : ℕ}
    (hj : j < K.eval k) :
    ∀ (stk stkShift : List Aff2Run) (stkEnd : List AffRun),
      shiftStackJ stk = some stkShift →
      evalStackEnd K stk = some stkEnd →
      evalAff2Side side wordOf k j stkShift = evalAff2Side side wordOf k (j + 1) stk
  | [], stkShift, _, hsh, _ => by
    simp only [shiftStackJ, Option.some.injEq] at hsh
    subst hsh
    rfl
  | r :: rs, stkShift, stkEnd, hsh, hend => by
    simp only [shiftStackJ] at hsh
    simp only [evalStackEnd] at hend
    rcases h1 : r.count.shiftJ? with _ | c'
    · simp [h1] at hsh
    · rcases h2 : shiftStackJ rs with _ | rs'
      · simp [h1, h2] at hsh
      · rw [h1, h2] at hsh
        simp only [Option.some.injEq] at hsh
        subst hsh
        rcases he1 : r.count.atEnd? K with _ | ce
        · simp [he1] at hend
        · rcases he2 : evalStackEnd K rs with _ | rse
          · simp [he1, he2] at hend
          · have hcEq := Aff2Nat.shiftJ_eval h1 he1 hj
            have ih1 := shiftStackJ_eval wordOf K true hj rs rs' rse h2 he2
            have ih0 := shiftStackJ_eval wordOf K false hj rs rs' rse h2 he2
            cases side <;> simp [evalAff2Side, hcEq, ih1, ih0]

private theorem evalStackEnd_sound (wordOf : ℕ → List Γ) (K : AffNat) (side : Bool) (k : ℕ) :
    ∀ (stk : List Aff2Run) (stkEnd : List AffRun),
      evalStackEnd K stk = some stkEnd →
      evalAff2Side side wordOf k (K.eval k) stk = evalAffSide side wordOf k stkEnd
  | [], stkEnd, hend => by
    simp only [evalStackEnd, Option.some.injEq] at hend
    subst hend
    rfl
  | r :: rs, stkEnd, hend => by
    simp only [evalStackEnd] at hend
    rcases he1 : r.count.atEnd? K with _ | ce
    · simp [he1] at hend
    · rcases he2 : evalStackEnd K rs with _ | rse
      · simp [he1, he2] at hend
      · rw [he1, he2] at hend
        by_cases hg : ce.geConst 1 = true
        · simp only [hg, ↓reduceIte, Option.some.injEq] at hend
          subst hend
          have hcEq := Aff2Nat.atEnd_eval he1 k
          have ih1 := evalStackEnd_sound wordOf K true k rs rse he2
          have ih0 := evalStackEnd_sound wordOf K false k rs rse he2
          cases side <;> simp [evalAff2Side, evalAffSide, hcEq, ih1, ih0]
        · have hng := Bool.eq_false_iff.mpr hg
          simp [hng] at hend

/-- Soundness of `verifyCycle`: discharges `K(k)` iterations of an `L`-step inner loop. -/
theorem verifyCycle_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {L : ℕ} {K : AffNat} {deltas : List (ℕ × ℕ)} {c : AffCfg}
    {dtTot : AffNat} {cEnd : AffCfg}
    (hvc : verifyCycle numStates exits L K deltas c = some (dtTot, cEnd)) (k : ℕ) :
    ReachesIn M (dtTot.eval k)
      (evalAffCfg qOf (vocabWord baseWord vocab) k c)
      (evalAffCfg qOf (vocabWord baseWord vocab) k cEnd) := by
  unfold verifyCycle at hvc
  by_cases hk1 : K.geConst 1 = true
  · simp only [hk1, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hvc
    rcases hatL : attachDeltas c.left deltas with _ | ⟨l₂, dsRem⟩
    · simp [hatL] at hvc
    · rw [hatL] at hvc
      simp only at hvc
      rcases hatR : attachDeltas c.right dsRem with _ | ⟨r₂, dsRem2⟩
      · simp [hatR] at hvc
      · rw [hatR] at hvc
        rcases dsRem2 with _ | ⟨_, _⟩
        · simp only at hvc
          by_cases hinit :
              (l₂.all (fun r ↦ r.count.geForLoop K 1) &&
                r₂.all (fun r ↦ r.count.geForLoop K 1)) = true
          · simp only [hinit, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hvc
            simp only [Bool.and_eq_true] at hinit
            have hwfL : stackWF K l₂ := List.all_eq_true.mp hinit.1
            have hwfR : stackWF K r₂ := List.all_eq_true.mp hinit.2
            rcases hrun : runAff2Steps numStates exits K L 0 ⟨c.q, c.dir, l₂, r₂⟩ with
              _ | ⟨dtIter, c₁⟩
            · simp [hrun] at hvc
            · rcases hshL : shiftStackJ l₂ with _ | lShift
              · simp [hrun, hshL] at hvc
              · rcases hshR : shiftStackJ r₂ with _ | rShift
                · simp [hrun, hshL, hshR] at hvc
                · rw [hrun, hshL, hshR] at hvc
                  by_cases hc1eq : (c₁ == ⟨c.q, c.dir, lShift, rShift⟩) = true
                  · simp only [hc1eq, ↓reduceIte] at hvc
                    have hc1 : c₁ = ⟨c.q, c.dir, lShift, rShift⟩ := eq_of_beq hc1eq
                    subst hc1
                    rcases hendL : evalStackEnd K l₂ with _ | lEnd
                    · simp [hendL] at hvc
                    · rcases hendR : evalStackEnd K r₂ with _ | rEnd
                      · simp [hendL, hendR] at hvc
                      · rw [hendL, hendR] at hvc
                        simp only [AffNat.strict_eq, mkStrictAffCfg_eq, Option.some.injEq,
                          Prod.mk.injEq] at hvc
                        rcases hvc with ⟨rfl, rfl⟩
                        set wOf := vocabWord baseWord vocab
                        have hloop : ∀ m : ℕ, m ≤ K.eval k →
                            ReachesIn M (dtIter * m)
                              (evalAff2Cfg qOf wOf k 0 ⟨c.q, c.dir, l₂, r₂⟩)
                              (evalAff2Cfg qOf wOf k m ⟨c.q, c.dir, l₂, r₂⟩) := by
                          intro m hm
                          induction m with
                          | zero => simp
                          | succ m ih =>
                            have hm_lt : m < K.eval k := hm
                            have hprev := ih (Nat.le_of_lt hm_lt)
                            have ⟨_, hiter⟩ :=
                              runAff2Steps_sound hbase hb0 hv0 hexits L 0
                                ⟨c.q, c.dir, l₂, r₂⟩ dtIter ⟨c.q, c.dir, lShift, rShift⟩
                                hwfL hwfR hrun hm_lt
                            simp only [Nat.sub_zero] at hiter
                            have hshEqL := shiftStackJ_eval wOf K false hm_lt l₂ lShift lEnd
                              hshL hendL
                            have hshEqR := shiftStackJ_eval wOf K true hm_lt r₂ rShift rEnd
                              hshR hendR
                            have hcfgEq :
                                evalAff2Cfg qOf wOf k m ⟨c.q, c.dir, lShift, rShift⟩ =
                                evalAff2Cfg qOf wOf k (m + 1) ⟨c.q, c.dir, l₂, r₂⟩ := by
                              simp [evalAff2Cfg, hshEqL, hshEqR]
                            rw [hcfgEq] at hiter
                            have htr := hprev.trans hiter
                            rwa [← Nat.mul_succ] at htr
                        have htot := hloop (K.eval k) (Nat.le_refl _)
                        have h0L := attachDeltas_eval0 wOf false k c.left deltas dsRem l₂ hatL
                        have h0R := attachDeltas_eval0 wOf true k c.right dsRem [] r₂ hatR
                        have hstartEq :
                            evalAff2Cfg qOf wOf k 0 ⟨c.q, c.dir, l₂, r₂⟩ =
                            evalAffCfg qOf wOf k c := by
                          simp [evalAff2Cfg, evalAffCfg, h0L, h0R]
                        have hendEqL := evalStackEnd_sound wOf K false k l₂ lEnd hendL
                        have hendEqR := evalStackEnd_sound wOf K true k r₂ rEnd hendR
                        have hendEq :
                            evalAff2Cfg qOf wOf k (K.eval k) ⟨c.q, c.dir, l₂, r₂⟩ =
                            evalAffCfg qOf wOf k ⟨c.q, c.dir, lEnd, rEnd⟩ := by
                          simp [evalAff2Cfg, evalAffCfg, hendEqL, hendEqR]
                        rw [hstartEq, hendEq, ← AffNat.eval_scale] at htot
                        exact htot
                  · have hnc1eq := Bool.eq_false_iff.mpr hc1eq
                    simp [hnc1eq] at hvc
          · have hninit := Bool.eq_false_iff.mpr hinit
            simp [hninit] at hvc
        · simp at hvc
  · have hnk1 := Bool.eq_false_iff.mpr hk1
    simp [hnk1] at hvc

/-! ### Soundness of Certificate Tree Replay & Non-Halting Closure -/

private theorem runStepCount_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {target : AffNat} :
    ∀ (n : ℕ) (acc : AffNat) (c : AffCfg) (accOut : AffNat) (cOut : AffCfg),
      runStepCount numStates exits target n acc c = some (accOut, cOut) →
      ∀ k : ℕ, ∃ d : ℕ, accOut.eval k = acc.eval k + d ∧
        ReachesIn M d
          (evalAffCfg qOf (vocabWord baseWord vocab) k c)
          (evalAffCfg qOf (vocabWord baseWord vocab) k cOut)
  | 0, acc, c, accOut, cOut, h, k => by
    simp only [runStepCount, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨0, by omega, ReachesIn.zero M _⟩
  | n + 1, acc, ⟨q, dir, l, r⟩, accOut, cOut, h, k => by
    simp only [runStepCount] at h
    rcases hst : stepAffOnce numStates exits (target.sub? acc) q dir l r with _ | ⟨dt, c'⟩
    · simp [hst] at h
    · rw [hst] at h
      simp only [AffNat.strict_eq] at h
      have h1 := stepAffOnce_sound hbase hb0 hv0 hexits hst k
      obtain ⟨d₂, hd₂, h2⟩ :=
        runStepCount_sound hbase hb0 hv0 hexits n (acc.add dt) c' accOut cOut h k
      refine ⟨dt.eval k + d₂, ?_, h1.trans h2⟩
      rw [hd₂, AffNat.eval_add, Nat.add_assoc]

private theorem replayAffTree_sound_aux {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {vocab : NatTrie (BTree ℕ)} {exits : NatTrie CompExit}
    (hv0 : checkVocabBlank0 vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit vocab) 0 1 exits = true)
    {target : AffNat} :
    ∀ (ops : BTree AffOp) (acc : AffNat) (c : AffCfg) (accOut : AffNat) (cOut : AffCfg),
      replayAffTree numStates exits target ops acc c = some (accOut, cOut) →
      ∀ k : ℕ, ∃ d : ℕ, accOut.eval k = acc.eval k + d ∧
        ReachesIn M d
          (evalAffCfg qOf (vocabWord baseWord vocab) k c)
          (evalAffCfg qOf (vocabWord baseWord vocab) k cOut)
  | .empty, acc, c, accOut, cOut, h, k => by
    simp only [replayAffTree, Option.some.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨0, by omega, ReachesIn.zero M _⟩
  | .leaf (.steps n), acc, c, accOut, cOut, h, k =>
    runStepCount_sound hbase hb0 hv0 hexits n acc c accOut cOut h k
  | .leaf (.cycle L K deltas), acc, c, accOut, cOut, h, k => by
    simp only [replayAffTree] at h
    rcases hvc : verifyCycle numStates exits L K deltas c with _ | ⟨dt, c'⟩
    · simp [hvc] at h
    · rw [hvc] at h
      simp only [AffNat.strict_eq, Option.some.injEq, Prod.mk.injEq] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨dt.eval k, AffNat.eval_add acc dt k,
        verifyCycle_sound hbase hb0 hv0 hexits hvc k⟩
  | .node l r, acc, c, accOut, cOut, h, k => by
    simp only [replayAffTree] at h
    rcases hl : replayAffTree numStates exits target l acc c with _ | ⟨a₁, c₁⟩
    · simp [hl] at h
    · rw [hl] at h
      obtain ⟨d₁, hd₁, h1⟩ := replayAffTree_sound_aux hbase hb0 hv0 hexits l acc c a₁ c₁ hl k
      obtain ⟨d₂, hd₂, h2⟩ := replayAffTree_sound_aux hbase hb0 hv0 hexits r a₁ c₁ accOut cOut h k
      refine ⟨d₁ + d₂, ?_, h1.trans h2⟩
      omega

/-- Soundness of a verified `ReturnCert`: establishes `ReachesIn M (target.eval k)` for every
`k : ℕ`. -/
theorem verifyReturnCert_sound {M : Machine Γ Λ} {qOf : ℕ → Λ} {baseWord : ℕ → List Γ}
    {baseExit : ℕ → Bool → ℕ → Option (ℕ × ℕ × Bool × ℕ)}
    (hbase : BaseExitSound M qOf baseWord baseExit)
    (hb0 : ∀ x ∈ baseWord 0, x = default)
    {numStates : ℕ} {cert : ReturnCert} {target : AffNat} {initCfg finalCfg : AffCfg}
    (hv0 : checkVocabBlank0 cert.vocab = true)
    (hexits : NatTrie.checkAll (checkExitEntry numStates baseExit cert.vocab) 0 1 cert.exits = true)
    (hrep : AffReplayReaches numStates cert.exits target cert.ops ⟨0, 0⟩ initCfg target finalCfg)
    (k : ℕ) :
    ReachesIn M (target.eval k)
      (evalAffCfg qOf (vocabWord baseWord cert.vocab) k initCfg)
      (evalAffCfg qOf (vocabWord baseWord cert.vocab) k finalCfg) := by
  obtain ⟨d, hd, hr⟩ :=
    replayAffTree_sound_aux hbase hb0 hv0 hexits cert.ops ⟨0, 0⟩ initCfg target finalCfg
      hrep.to_eq k
  have h0 : (AffNat.mk 0 0).eval k = 0 := by simp [AffNat.eval]
  have hdeq : d = target.eval k := by omega
  rwa [hdeq] at hr

/-- Non-halting closure principle for affine-exponent symbolic configuration families `C : ℕ → Cfg`:
if `M` reaches `C 0` from the blank tape `init []` and `C k` reaches `C (k + 1)` in positive steps
for every `k : ℕ`, then `IsNotHalt M`. -/
theorem isNotHalt_of_family {M : Machine Γ Λ} (C : ℕ → Cfg Γ Λ)
    (hinit : ReachesStar M (init []) (C 0))
    (hstep : ∀ k : ℕ, ReachesPlus M (C k) (C (k + 1))) :
    IsNotHalt M := by
  refine IsNotHalt.of_reachesPlus_invariant (P := fun c ↦ ∃ k : ℕ, c = C k) hinit ⟨0, rfl⟩ ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨C (k + 1), hstep k, ⟨k + 1, rfl⟩⟩

end MachineSoundness

end BusyBeaver.AffRLE

end
