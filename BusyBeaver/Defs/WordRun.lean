/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Nat.Basic
public import BusyBeaver.Defs.Core
public import BusyBeaver.Defs.Stack

/-!
# Word-Run Stack Definitions (`BusyBeaver.Defs.WordRun`)

Closed invariant-relative word-run stack cryptid (`IsWordRunCryptid`) and supporting definitions
for parameterized word stacks with accumulator registers.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

/-- Specification for one half-tape of a word-run stack with `numRegs` (`≤ 2`) bottom
    accumulator registers. -/
structure WordStackSpec (Γ Tok : Type*) (numRegs : ℕ) where
  word : Tok → List Γ
  stride : Tok → ℕ
  offset : Tok → ℕ
  base : List Γ
  regWord : Fin numRegs → List Γ

/-- Encodes `m` accumulator registers `(rw 0 ^ r 0) +> ... +> tail`. -/
def encRegsAux {Γ : Type*} [Inhabited Γ] :
    (m : ℕ) → (Fin m → List Γ) → (Fin m → ℕ) → ListBlank Γ → ListBlank Γ
  | 0, _, _, tail => tail
  | m + 1, rw, r, tail =>
      ListBlank.append ((rw 0) ^ (r 0))
        (encRegsAux m (fun i => rw i.succ) (fun i => r i.succ) tail)

/-- Encodes the bottom accumulator registers + `base` of a `WordStackSpec`. -/
def encRegs {Γ Tok : Type*} [Inhabited Γ] {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (regs : Fin numRegs → ℕ) : ListBlank Γ :=
  encRegsAux numRegs spec.regWord regs (ListBlank.append spec.base default)

/-- Encodes a word-run stack `List (Tok × ℕ)` on top of `encRegs spec regs`:
    `encHalf spec regs ((t, d) :: rest) =
      ListBlank.append ((word t)^(stride t * d + offset t)) (encHalf spec regs rest)`. -/
def encHalf {Γ Tok : Type*} [Inhabited Γ] {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (regs : Fin numRegs → ℕ) :
    List (Tok × ℕ) → ListBlank Γ
  | [] => encRegs spec regs
  | (t, d) :: rest =>
      ListBlank.append ((spec.word t) ^ (spec.stride t * d + spec.offset t))
        (encHalf spec regs rest)

/-- Exact encoded symbol length of a single word-run frame `(t, d)`. -/
def frameBitLen {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (f : Tok × ℕ) : ℕ :=
  (spec.word f.1).length * (spec.stride f.1 * f.2 + spec.offset f.1)

/-- Encoded symbol length of the active top frame (`0` on empty stack `[]`). -/
def topFrameBitLen {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) : List (Tok × ℕ) → ℕ
  | [] => 0
  | f :: _ => frameBitLen spec f

/-- Total encoded symbol length across all frames of `xs`. -/
def stackBitLen {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) : List (Tok × ℕ) → ℕ
  | [] => 0
  | f :: rest => frameBitLen spec f + stackBitLen spec rest

/-- Total encoded symbol length of the bottom accumulator registers. -/
def regsBitLenAux {Γ : Type*} : (m : ℕ) → (Fin m → List Γ) → (Fin m → ℕ) → ℕ
  | 0, _, _ => 0
  | m + 1, rw, r => (rw 0).length * r 0 + regsBitLenAux m (fun i => rw i.succ) (fun i => r i.succ)

section
universe u v

/-- Prefix length of a `HalfTapeView`. -/
def viewPrefixLen {Γ : Type u} (v : HalfTapeView Γ) : ℕ :=
  HalfTapeView.casesOn (motive := fun _ => ℕ) v List.length List.length

/-- Prefix-extensible non-surjectivity of a family of half-tapes `enc s` (`s` ranging over the
    valid states): every finite window of every valid half-tape extends to a half-tape that no
    valid state encodes, i.e. the image has empty interior in the prefix topology. A
    bounded-prefix restriction such as "the head cell is `0`" never satisfies it, so a family
    certified by it carries a genuine unbounded grammar rather than a renaming of the raw tape. -/
def IsNowhereDenseFamily {Γ : Type u} {S : Type v} [Inhabited Γ]
    (Valid : S → Prop) (enc : S → ListBlank Γ) : Prop :=
  ∀ s, Valid s → ∀ n : ℕ, ∃ bad : ListBlank Γ,
    (∀ i, i < n → bad.nth i = (enc s).nth i) ∧ ∀ s', Valid s' → enc s' ≠ bad

end

/-- Full symbolic state of a two-sided word-run stack + accumulator system. -/
structure WordSysState (Mode TokL TokR : Type*) (numRegsL numRegsR : ℕ) where
  mode : Mode
  regsL : Fin numRegsL → ℕ
  regsR : Fin numRegsR → ℕ
  L : List (TokL × ℕ)
  R : List (TokR × ℕ)

/-- Total active bit-length of both stacks and registers in `s`. -/
def totalSystemBitLen {Γ Mode TokL TokR : Type*} {numRegsL numRegsR : ℕ}
    (specL : WordStackSpec Γ TokL numRegsL)
    (specR : WordStackSpec Γ TokR numRegsR)
    (s : WordSysState Mode TokL TokR numRegsL numRegsR) : ℕ :=
  stackBitLen specL s.L + stackBitLen specR s.R +
    regsBitLenAux numRegsL specL.regWord s.regsL +
    regsBitLenAux numRegsR specR.regWord s.regsR

/-- Every `Mode` evaluates `s` as a fixed control state `q` and bounded `HalfTapeView`s
    (`≤ 8`-symbol prefixes) of `encHalf specL s.regsL s.L` and `encHalf specR s.regsR s.R`. -/
def IsValidWordModes {Γ Λ Mode TokL TokR : Type*} [Inhabited Γ] [OfNat Γ 0]
    {numRegsL numRegsR : ℕ}
    (specL : WordStackSpec Γ TokL numRegsL)
    (specR : WordStackSpec Γ TokR numRegsR)
    (evalCfg : WordSysState Mode TokL TokR numRegsL numRegsR → Cfg Γ Λ) : Prop :=
  ∀ m : Mode, ∃ (q : Λ) (vL vR : HalfTapeView Γ),
    viewPrefixLen vL ≤ 8 ∧
    viewPrefixLen vR ≤ 8 ∧
    ((∀ rL rR L R,
        evalCfg ⟨m, rL, rR, L, R⟩ =
          ⟨some q, ⟨(0 : Γ), applyView vL (encHalf specL rL L),
            applyView vR (encHalf specR rR R)⟩⟩) ∨
     (∀ rL rR L R,
        evalCfg ⟨m, rL, rR, L, R⟩ =
          Cfg.headLeft q (applyView vL (encHalf specL rL L)) (applyView vR (encHalf specR rR R))) ∨
     (∀ rL rR L R,
        evalCfg ⟨m, rL, rR, L, R⟩ =
          Cfg.headRight q (applyView vL (encHalf specL rL L)) (applyView vR (encHalf specR rR R))))

/-- Iterates a partial macro-transition `stepMacro : S → Option S` for `k` macro-steps. -/
def iterWordMacro {S : Type*} (stepMacro : S → Option S) : ℕ → S → Option S
  | 0, s => some s
  | k + 1, s =>
      match stepMacro s with
      | none => none
      | some s' => iterWordMacro stepMacro k s'

/-- `PreservesOrGrows spec xs xs'` holds when `xs` is NOT net-drained above a shared suffix `rest`:
    `xs = u ++ rest` and `xs' = pfx ++ rest` with `stackBitLen spec u ≤ stackBitLen spec pfx`. -/
def PreservesOrGrows {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (xs xs' : List (Tok × ℕ)) : Prop :=
  ∃ u pfx rest,
    xs = u ++ rest ∧
    xs' = pfx ++ rest ∧
    stackBitLen spec u ≤ stackBitLen spec pfx

/-- `DrainsTop spec xs xs'` holds whenever the transition `xs ↦ xs'` net-drains encoded bits
    from the stack (`¬ PreservesOrGrows spec xs xs'`). -/
def DrainsTop {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (xs xs' : List (Tok × ℕ)) : Prop :=
  ¬ PreservesOrGrows spec xs xs'

/-- `PopsTop xs xs'` holds when the active top frame `f` of `xs = f :: xs'` is
    completely popped. -/
def PopsTop {Tok : Type*} (xs xs' : List (Tok × ℕ)) : Prop :=
  ∃ f, xs = f :: xs'

/-- `DrainsTopFrame spec xs xs'` holds when the active top frame `f` of `xs = f :: rest`
    is popped or replaced by at most an `8`-bit remainder prefix `pfx` (`xs' = pfx ++ rest`). -/
def DrainsTopFrame {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) (xs xs' : List (Tok × ℕ)) : Prop :=
  ∃ f pfx rest,
    xs = f :: rest ∧
    xs' = pfx ++ rest ∧
    stackBitLen spec pfx ≤ 8

/-- Strict frame-length progress law over `WordSysState`. -/
def StrictFrameProgress {Γ Mode TokL TokR : Type*} {numRegsL numRegsR : ℕ}
    (specL : WordStackSpec Γ TokL numRegsL)
    (specR : WordStackSpec Γ TokR numRegsR)
    (s s' : WordSysState Mode TokL TokR numRegsL numRegsR) (n : ℕ) : Prop :=
  1 ≤ n ∧
  (DrainsTop specL s.L s'.L → 2 ≤ topFrameBitLen specL s.L → 2 ≤ n) ∧
  (DrainsTop specR s.R s'.R → 2 ≤ topFrameBitLen specR s.R → 2 ≤ n) ∧
  (PopsTop s.L s'.L → topFrameBitLen specL s.L ≤ n) ∧
  (PopsTop s.R s'.R → topFrameBitLen specR s.R ≤ n)

/-- Side selector (`leftSide` vs `rightSide`) for orbit-exercised run-drain witnesses. -/
inductive StackSide
  | leftSide
  | rightSide

/-- Every pair of adjacent frames on the stack has distinct token constructors (`t₁ ≠ t₂`). -/
def AdjacentDistinctTok {Tok : Type*} : List (Tok × ℕ) → Prop
  | [] => True
  | [_] => True
  | (t₁, _) :: (t₂, d₂) :: rest => t₁ ≠ t₂ ∧ AdjacentDistinctTok ((t₂, d₂) :: rest)

/-- Canonical merged word-run frame discipline. -/
def MergedRunFrames {Γ Tok : Type*} {numRegs : ℕ}
    (spec : WordStackSpec Γ Tok numRegs) : List (Tok × ℕ) → Prop
  | [] => True
  | [(t, d)] => spec.stride t = 0 → d = 0
  | (t₁, d₁) :: (t₂, d₂) :: rest =>
      (spec.stride t₁ = 0 → d₁ = 0) ∧
      (1 ≤ spec.stride t₁ → t₁ ≠ t₂) ∧
      MergedRunFrames spec ((t₂, d₂) :: rest)

/-- Non-blank bottom-anchor discipline. -/
def AnchoredFrames {k numRegs : ℕ} {Tok : Type*}
    (spec : WordStackSpec (Fin (k + 2)) Tok numRegs) : List (Tok × ℕ) → Prop
  | [] => True
  | [(t, _)] => (∃ x ∈ spec.word t, x ≠ 0) ∨ (∃ x ∈ spec.base, x ≠ 0)
  | _ :: f₂ :: rest => AnchoredFrames spec (f₂ :: rest)

/-- Boundary-aligned H4 run-pair side discipline when `encHalf` is universal (`kraftSum = B^M`). -/
def IsBoundaryAlignedSide {Γ Λ Mode TokL TokR : Type*} [Inhabited Γ] [OfNat Γ 0]
    {numRegsL numRegsR : ℕ}
    (side : StackSide)
    (specL : WordStackSpec Γ TokL numRegsL)
    (specR : WordStackSpec Γ TokR numRegsR)
    (ValidState : WordSysState Mode TokL TokR numRegsL numRegsR → Prop)
    (evalCfg : WordSysState Mode TokL TokR numRegsL numRegsR → Cfg Γ Λ) : Prop :=
  match side with
  | .leftSide =>
      numRegsL = 0 ∧
      specL.base = [] ∧
      (∀ t : TokL, (specL.word t).length = 1 ∧ specL.stride t = 1 ∧ specL.offset t = 1) ∧
      (∀ s, ValidState s → AdjacentDistinctTok s.L) ∧
      (∀ m : Mode, ∃ (q : Λ) (vR : HalfTapeView Γ),
        viewPrefixLen vR ≤ 8 ∧
        ((∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            ⟨some q, ⟨(0 : Γ), encHalf specL rL L, applyView vR (encHalf specR rR R)⟩⟩) ∨
         (∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            Cfg.headLeft q (encHalf specL rL L) (applyView vR (encHalf specR rR R))) ∨
         (∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            Cfg.headRight q (encHalf specL rL L) (applyView vR (encHalf specR rR R)))))
  | .rightSide =>
      numRegsR = 0 ∧
      specR.base = [] ∧
      (∀ t : TokR, (specR.word t).length = 1 ∧ specR.stride t = 1 ∧ specR.offset t = 1) ∧
      (∀ s, ValidState s → AdjacentDistinctTok s.R) ∧
      (∀ m : Mode, ∃ (q : Λ) (vL : HalfTapeView Γ),
        viewPrefixLen vL ≤ 8 ∧
        ((∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            ⟨some q, ⟨(0 : Γ), applyView vL (encHalf specL rL L), encHalf specR rR R⟩⟩) ∨
         (∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            Cfg.headLeft q (applyView vL (encHalf specL rL L)) (encHalf specR rR R)) ∨
         (∀ rL rR L R, evalCfg ⟨m, rL, rR, L, R⟩ =
            Cfg.headRight q (applyView vL (encHalf specL rL L)) (encHalf specR rR R))))

/-- Closed Invariant-Relative Word-Run Stack Cryptid (`IsWordRunCryptid`). -/
def IsWordRunCryptid {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (Mode TokL TokR : Type)
    (numRegsL numRegsR : ℕ)
    (specL : WordStackSpec (Fin (k + 2)) TokL numRegsL)
    (specR : WordStackSpec (Fin (k + 2)) TokR numRegsR)
    (ValidState : WordSysState Mode TokL TokR numRegsL numRegsR → Prop)
    (evalCfg : WordSysState Mode TokL TokR numRegsL numRegsR → Cfg (Fin (k + 2)) Λ)
    (stepMacro : WordSysState Mode TokL TokR numRegsL numRegsR →
      Option (WordSysState Mode TokL TokR numRegsL numRegsR)),
    numRegsL ≤ 2 ∧ numRegsR ≤ 2 ∧
    specL.base.length ≤ 8 ∧ specR.base.length ≤ 8 ∧
    Function.Injective specL.word ∧ Function.Injective specR.word ∧
    (∀ i : Fin numRegsL, 1 ≤ (specL.regWord i).length ∧ (specL.regWord i).length ≤ 8 ∧
      (∃ x ∈ specL.regWord i, x ≠ 0)) ∧
    (∀ i : Fin numRegsR, 1 ≤ (specR.regWord i).length ∧ (specR.regWord i).length ≤ 8 ∧
      (∃ x ∈ specR.regWord i, x ≠ 0)) ∧
    (∃ modes : List Mode,
      modes.Nodup ∧ 1 ≤ modes.length ∧ modes.length ≤ 8 ∧ ∀ m : Mode, m ∈ modes) ∧
    (∃ (toksL : List TokL) (toksR : List TokR),
      toksL.Nodup ∧ toksR.Nodup ∧
      1 ≤ toksL.length ∧ toksL.length ≤ 8 ∧
      1 ≤ toksR.length ∧ toksR.length ≤ 8 ∧
      3 ≤ toksL.length + toksR.length ∧
      (∀ t : TokL, t ∈ toksL ∧ 1 ≤ (specL.word t).length ∧ (specL.word t).length ≤ 8 ∧
        1 ≤ specL.offset t ∧ specL.stride t ≤ 8 ∧ specL.offset t ≤ 2 ∧
        (specL.stride t = 0 → specL.offset t = 1) ∧
        (1 ≤ specL.stride t → ∃ x ∈ specL.word t, x ≠ 0)) ∧
      (∀ t : TokR, t ∈ toksR ∧ 1 ≤ (specR.word t).length ∧ (specR.word t).length ≤ 8 ∧
        1 ≤ specR.offset t ∧ specR.stride t ≤ 8 ∧ specR.offset t ≤ 2 ∧
        (specR.stride t = 0 → specR.offset t = 1) ∧
        (1 ≤ specR.stride t → ∃ x ∈ specR.word t, x ≠ 0))) ∧
    IsValidWordModes specL specR evalCfg ∧
    (∀ s, ValidState s →
      MergedRunFrames specL s.L ∧ MergedRunFrames specR s.R ∧
      AnchoredFrames specL s.L ∧ AnchoredFrames specR s.R) ∧
    IsNowhereDenseFamily ValidState (fun s => encHalf specL s.regsL s.L) ∧
    IsNowhereDenseFamily ValidState (fun s => encHalf specR s.regsR s.R) ∧
    (∀ s s', ValidState s → stepMacro s = some s' →
      ValidState s' ∧ ∃ n, StrictFrameProgress specL specR s s' n ∧
        ReachesIn M n (evalCfg s) (evalCfg s')) ∧
    (∀ s, ValidState s → stepMacro s = none →
      ∃ (n_h : ℕ) (cfg_h : Cfg (Fin (k + 2)) Λ),
        1 ≤ n_h ∧ n_h ≤ 32 ∧ ReachesIn M n_h (evalCfg s) cfg_h ∧ (step M cfg_h).isNone) ∧
    (∃ s_depth : ℕ → WordSysState Mode TokL TokR numRegsL numRegsR,
      ∀ D : ℕ, ValidState (s_depth D) ∧ D ≤ (s_depth D).L.length + (s_depth D).R.length) ∧
    ∃ s₀ : WordSysState Mode TokL TokR numRegsL numRegsR,
      ValidState s₀ ∧
      s₀.L.length + s₀.R.length ≤ 4 ∧
      ReachesPlus M (init []) (evalCfg s₀) ∧
      (∃ (n_grow1 n_grow2 : ℕ) (s_g1 s_g2 : WordSysState Mode TokL TokR numRegsL numRegsR),
        64 ≤ n_grow1 ∧ n_grow1 < n_grow2 ∧ n_grow2 ≤ 2048 ∧
        iterWordMacro stepMacro n_grow1 s₀ = some s_g1 ∧
        iterWordMacro stepMacro n_grow2 s₀ = some s_g2 ∧
        32 ≤ totalSystemBitLen specL specR s_g1 ∧
        totalSystemBitLen specL specR s_g1 + 32 ≤ totalSystemBitLen specL specR s_g2 ∧
        2 ≤ s_g1.L.length + s_g1.R.length ∧
        4 ≤ s_g1.L.length + s_g1.R.length + numRegsL + numRegsR) ∧
      (∃ (k_d1 k_d2 b₁ b₂ : ℕ)
          (s_d1 s_d1' s_d2 s_d2' : WordSysState Mode TokL TokR numRegsL numRegsR),
        64 ≤ k_d1 ∧ k_d1 < k_d2 ∧ k_d2 ≤ 2048 ∧
        26 ≤ b₁ ∧ b₁ < b₂ ∧
        iterWordMacro stepMacro k_d1 s₀ = some s_d1 ∧ stepMacro s_d1 = some s_d1' ∧
        iterWordMacro stepMacro k_d2 s₀ = some s_d2 ∧ stepMacro s_d2 = some s_d2' ∧
        ((s_d1'.regsL = s_d1.regsL ∧ PopsTop s_d1.L s_d1'.L ∧ b₁ = topFrameBitLen specL s_d1.L) ∨
         (s_d1'.regsR = s_d1.regsR ∧ PopsTop s_d1.R s_d1'.R ∧ b₁ = topFrameBitLen specR s_d1.R)) ∧
        ((s_d2'.regsL = s_d2.regsL ∧ PopsTop s_d2.L s_d2'.L ∧ b₂ = topFrameBitLen specL s_d2.L) ∨
         (s_d2'.regsR = s_d2.regsR ∧ PopsTop s_d2.R s_d2'.R ∧ b₂ = topFrameBitLen specR s_d2.R))) ∧
      (numRegsL = 0 → ∃ (k_L : ℕ) (s_L s_L' : WordSysState Mode TokL TokR numRegsL numRegsR),
        64 ≤ k_L ∧ k_L ≤ 2048 ∧
        iterWordMacro stepMacro k_L s₀ = some s_L ∧ stepMacro s_L = some s_L' ∧
        s_L'.regsL = s_L.regsL ∧ PopsTop s_L.L s_L'.L ∧ 18 ≤ topFrameBitLen specL s_L.L) ∧
      (numRegsR = 0 → ∃ (k_R : ℕ) (s_R s_R' : WordSysState Mode TokL TokR numRegsL numRegsR),
        64 ≤ k_R ∧ k_R ≤ 2048 ∧
        iterWordMacro stepMacro k_R s₀ = some s_R ∧ stepMacro s_R = some s_R' ∧
        s_R'.regsR = s_R.regsR ∧ PopsTop s_R.R s_R'.R ∧ 18 ≤ topFrameBitLen specR s_R.R) ∧
      (∀ i : Fin numRegsL, ∃ (n_reg : ℕ) (s_reg : WordSysState Mode TokL TokR numRegsL numRegsR),
        n_reg ≤ 2048 ∧ iterWordMacro stepMacro n_reg s₀ = some s_reg ∧ 2 ≤ s_reg.regsL i) ∧
      (∀ i : Fin numRegsR, ∃ (n_reg : ℕ) (s_reg : WordSysState Mode TokL TokR numRegsL numRegsR),
        n_reg ≤ 2048 ∧ iterWordMacro stepMacro n_reg s₀ = some s_reg ∧ 2 ≤ s_reg.regsR i) ∧
      (∀ m : Mode, ∃ (n_m : ℕ) (s_m : WordSysState Mode TokL TokR numRegsL numRegsR),
        n_m ≤ 256 ∧ iterWordMacro stepMacro n_m s₀ = some s_m ∧ s_m.mode = m) ∧
      (∀ t : TokL, ∃ (n_t : ℕ) (s_t : WordSysState Mode TokL TokR numRegsL numRegsR) (d : ℕ),
        n_t ≤ 2048 ∧ iterWordMacro stepMacro n_t s₀ = some s_t ∧ (t, d) ∈ s_t.L) ∧
      (∀ t : TokR, ∃ (n_t : ℕ) (s_t : WordSysState Mode TokL TokR numRegsL numRegsR) (d : ℕ),
        n_t ≤ 2048 ∧ iterWordMacro stepMacro n_t s₀ = some s_t ∧ (t, d) ∈ s_t.R) ∧
      ((∃ (t_run : TokL) (s_fam : ℕ → WordSysState Mode TokL TokR numRegsL numRegsR),
          1 ≤ specL.stride t_run ∧
          (∃ n_r s_r d_r, n_r ≤ 2048 ∧ iterWordMacro stepMacro n_r s₀ = some s_r ∧
            1 ≤ d_r ∧ (t_run, d_r) ∈ s_r.L) ∧
          (∀ d : ℕ, ValidState (s_fam d) ∧
            (∃ d₀ rest, d ≤ d₀ ∧ (s_fam d).L = (t_run, d₀) :: rest) ∧
            (∃ s', stepMacro (s_fam d) = some s' ∧ PopsTop (s_fam d).L s'.L ∧
              topFrameBitLen specL (s_fam d).L ≤ totalSystemBitLen specL specR s' + 8))) ∨
       (∃ (t_run : TokR) (s_fam : ℕ → WordSysState Mode TokL TokR numRegsL numRegsR),
          1 ≤ specR.stride t_run ∧
          (∃ n_r s_r d_r, n_r ≤ 2048 ∧ iterWordMacro stepMacro n_r s₀ = some s_r ∧
            1 ≤ d_r ∧ (t_run, d_r) ∈ s_r.R) ∧
          (∀ d : ℕ, ValidState (s_fam d) ∧
            (∃ d₀ rest, d ≤ d₀ ∧ (s_fam d).R = (t_run, d₀) :: rest) ∧
            (∃ s', stepMacro (s_fam d) = some s' ∧ PopsTop (s_fam d).R s'.R ∧
              topFrameBitLen specR (s_fam d).R ≤ totalSystemBitLen specL specR s' + 8))))

end BusyBeaver
