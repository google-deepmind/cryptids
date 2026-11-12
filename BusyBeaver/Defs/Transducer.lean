/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Defs.Core
public import BusyBeaver.Defs.Stack

/-!
# Word-Stack Transducers (`BusyBeaver.Defs.Transducer`)

Bidirectional word-stack transducers:

- `IsValidTransducerModes` — bounded-prefix transducer mode views.
- `kraftSum` — scaled integer Kraft-McMillan weight.
- `iterTransducerMacro` — macro-step iteration.
- `HasTransducerReduction` — strict-sub-Kraft finite-alphabet word-stack transducer reduction.
-/

@[expose] public section

namespace BusyBeaver

open Relation Turing

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Every `TransducerMode` evaluates `(L, R)` as a fixed control state `q` and fixed bounded
`HalfTapeView`s `vL, vR` (`≤ 8`-symbol prefixes) of `encLeft L` and `encRight R` (either scanning
`0` between them or stepping onto the left or right view). -/
def IsValidTransducerModes {Γ Λ TransducerMode TokL TokR : Type*} [Inhabited Γ] [OfNat Γ 0]
    (encLeft : List TokL → ListBlank Γ)
    (encRight : List TokR → ListBlank Γ)
    (eval : TransducerMode → List TokL → List TokR → Cfg Γ Λ) : Prop :=
  ∀ m : TransducerMode, ∃ (q : Λ) (vL vR : HalfTapeView Γ),
    (match vL with | .id p => p.length ≤ 8 | .tail p => p.length ≤ 8) ∧
    (match vR with | .id p => p.length ≤ 8 | .tail p => p.length ≤ 8) ∧
    ((∀ L R, eval m L R =
      ⟨some q, ⟨(0 : Γ), applyView vL (encLeft L), applyView vR (encRight R)⟩⟩) ∨
    (∀ L R, eval m L R = Cfg.headLeft q (applyView vL (encLeft L)) (applyView vR (encRight R))) ∨
    (∀ L R, eval m L R = Cfg.headRight q (applyView vL (encLeft L)) (applyView vR (encRight R))))

/-- Scaled integer Kraft-McMillan weight `∑_{t ∈ toks} base ^ (maxLen - (word t).length)`. -/
@[reducible, simp]
def kraftSum {Tok Γ : Type*} (base maxLen : ℕ) (word : Tok → List Γ) : List Tok → ℕ
  | [] => 0
  | t :: ts => base ^ (maxLen - (word t).length) + kraftSum base maxLen word ts

/-- Iterate a partial macro-transducer step `stepMacro` for `n` macro-steps. -/
@[reducible, simp]
def iterTransducerMacro {Mode TokL TokR : Type*}
    (stepMacro : Mode → List TokL → List TokR → Option (Mode × List TokL × List TokR)) :
    ℕ → (Mode × List TokL × List TokR) → Option (Mode × List TokL × List TokR)
  | 0, s => some s
  | n + 1, (m, L, R) =>
      match stepMacro m L R with
      | none => none
      | some s' => iterTransducerMacro stepMacro n s'

/-- The blank-tape trajectory of `M` is governed by a closed, full-tape, strict-sub-Kraft
finite-alphabet word-stack transducer (`TransducerMode`, `TokL`, `TokR`, `stepMacro`) with bounded
blank-tape entry, `512..2048`-step stack expansion, full constructor orbit reachability, a single
boundary-closed halting exit gate, and orbit-exercised bidirectional multi-bit block-transduction
sweeps. -/
def HasTransducerReduction {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) : Prop :=
  ∃ (TransducerMode TokL TokR : Type)
    (baseL baseR : List (Fin (k + 2)))
    (wordL : TokL → List (Fin (k + 2)))
    (wordR : TokR → List (Fin (k + 2)))
    (encLeft : List TokL → ListBlank (Fin (k + 2)))
    (encRight : List TokR → ListBlank (Fin (k + 2)))
    (evalTransducerCfg : TransducerMode → List TokL → List TokR → Cfg (Fin (k + 2)) Λ)
    (stepMacro : TransducerMode → List TokL → List TokR →
      Option (TransducerMode × List TokL × List TokR))
    (IsInTransducerSystem : Cfg (Fin (k + 2)) Λ → Prop),
    (∃ modes : List TransducerMode,
      2 ≤ modes.length ∧ modes.length ≤ 8 ∧ ∀ m : TransducerMode, m ∈ modes) ∧
    (∃ (toksL : List TokL) (maxLenL : ℕ),
      toksL.Nodup ∧ (toksL.map wordL).Nodup ∧ maxLenL ≤ 8 ∧
      2 ≤ toksL.length ∧ toksL.length ≤ 8 ∧ (∀ t : TokL, t ∈ toksL) ∧
      (∀ t : TokL, 1 ≤ (wordL t).length ∧ (wordL t).length ≤ maxLenL) ∧
      kraftSum (k + 2) maxLenL wordL toksL < (k + 2) ^ maxLenL) ∧
    (∃ (toksR : List TokR) (maxLenR : ℕ),
      toksR.Nodup ∧ (toksR.map wordR).Nodup ∧ maxLenR ≤ 8 ∧
      2 ≤ toksR.length ∧ toksR.length ≤ 8 ∧ (∀ t : TokR, t ∈ toksR) ∧
      (∀ t : TokR, 1 ≤ (wordR t).length ∧ (wordR t).length ≤ maxLenR) ∧
      kraftSum (k + 2) maxLenR wordR toksR < (k + 2) ^ maxLenR) ∧
    baseL.length ≤ 8 ∧ baseR.length ≤ 8 ∧
    ((∀ t : TokL, 2 ≤ (wordL t).length) ∨ (∀ t : TokR, 2 ≤ (wordR t).length)) ∧
    (∃ t : TokL, (0 : Fin (k + 2)) ∈ wordL t ∧ ∃ a, a ∈ wordL t ∧ a ≠ 0) ∧
    (∃ t : TokR, (0 : Fin (k + 2)) ∈ wordR t ∧ ∃ a, a ∈ wordR t ∧ a ≠ 0) ∧
    encLeft [] = ListBlank.append baseL default ∧
    (∀ t L, encLeft (t :: L) = ListBlank.append (wordL t) (encLeft L)) ∧
    encRight [] = ListBlank.append baseR default ∧
    (∀ t R, encRight (t :: R) = ListBlank.append (wordR t) (encRight R)) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ L : List TokL, encLeft L ≠ t) ∧
    (∃ t : ListBlank (Fin (k + 2)), ∀ R : List TokR, encRight R ≠ t) ∧
    IsValidTransducerModes encLeft encRight evalTransducerCfg ∧
    (∀ cfg, IsInTransducerSystem cfg ↔ ∃ m L R, cfg = evalTransducerCfg m L R) ∧
    (∀ m L R m' L' R',
      stepMacro m L R = some (m', L', R') →
        ReachesPlus M (evalTransducerCfg m L R) (evalTransducerCfg m' L' R')) ∧
    ∃ (m₀ : TransducerMode) (L₀ : List TokL) (R₀ : List TokR),
      L₀.length + R₀.length ≤ 4 ∧
      ReachesPlus M (init []) (evalTransducerCfg m₀ L₀ R₀) ∧
      (∃ (n_grow : ℕ) (m_g : TransducerMode) (L_g : List TokL) (R_g : List TokR),
        512 ≤ n_grow ∧ n_grow ≤ 2048 ∧
        iterTransducerMacro stepMacro n_grow (m₀, L₀, R₀) = some (m_g, L_g, R_g) ∧
        20 ≤ L_g.length + R_g.length) ∧
      (∀ m : TransducerMode, ∃ (n_m : ℕ) (L_m : List TokL) (R_m : List TokR),
        n_m ≤ 256 ∧
        iterTransducerMacro stepMacro n_m (m₀, L₀, R₀) = some (m, L_m, R_m)) ∧
      (∀ t : TokL, ∃ (n_t : ℕ) (m_t : TransducerMode) (L_t : List TokL) (R_t : List TokR),
        n_t ≤ 256 ∧
        iterTransducerMacro stepMacro n_t (m₀, L₀, R₀) = some (m_t, L_t, R_t) ∧
        t ∈ L_t) ∧
      (∀ t : TokR, ∃ (n_t : ℕ) (m_t : TransducerMode) (L_t : List TokL) (R_t : List TokR),
        n_t ≤ 256 ∧
        iterTransducerMacro stepMacro n_t (m₀, L₀, R₀) = some (m_t, L_t, R_t) ∧
        t ∈ R_t) ∧
      ((∃ (m_exit : TransducerMode) (tL_exit : TokL) (exitNext : List TokL),
          exitNext.Nodup ∧ exitNext ≠ [] ∧
          (∀ R : List TokR, (stepMacro m_exit [tL_exit] R).isSome) ∧
          (∀ m L R,
            stepMacro m L R = none ↔
              (m = m_exit ∧ ∃ t₂ L'', t₂ ∈ exitNext ∧ L = tL_exit :: t₂ :: L'')) ∧
          (∀ t₂ ∈ exitNext, ∀ R : List TokR, ∃ cfg_h,
            ReachesPlus M (evalTransducerCfg m_exit [tL_exit, t₂] R) cfg_h ∧
              (step M cfg_h).isNone) ∧
          (∀ t₂ ∈ exitNext, ∃ sfx : List TokL, sfx.length ≤ 2 ∧
            ∀ (L'' : List TokL) (R : List TokR), ∃ cfg_h,
              ReachesPlus M (evalTransducerCfg m_exit (tL_exit :: t₂ :: (sfx ++ L'')) R) cfg_h ∧
                (step M cfg_h).isNone)) ∨
        (∃ (m_exit : TransducerMode) (tR_exit : TokR) (exitNext : List TokR),
          exitNext.Nodup ∧ exitNext ≠ [] ∧
          (∀ L : List TokL, (stepMacro m_exit L [tR_exit]).isSome) ∧
          (∀ m L R,
            stepMacro m L R = none ↔
              (m = m_exit ∧ ∃ t₂ R'', t₂ ∈ exitNext ∧ R = tR_exit :: t₂ :: R'')) ∧
          (∀ t₂ ∈ exitNext, ∀ L : List TokL, ∃ cfg_h,
            ReachesPlus M (evalTransducerCfg m_exit L [tR_exit, t₂]) cfg_h ∧
              (step M cfg_h).isNone) ∧
          (∀ t₂ ∈ exitNext, ∃ sfx : List TokR, sfx.length ≤ 2 ∧
            ∀ (L : List TokL) (R'' : List TokR), ∃ cfg_h,
              ReachesPlus M (evalTransducerCfg m_exit L (tR_exit :: t₂ :: (sfx ++ R''))) cfg_h ∧
                (step M cfg_h).isNone))) ∧
      (∃ (m_lr m_rl : TransducerMode) (tL tL' : TokL) (tR tR' : TokR) (s₁ s₂ s₃ s₄ : ℕ),
        1 ≤ s₁ ∧ s₁ ≤ 4 ∧ 1 ≤ s₂ ∧ s₂ ≤ 4 ∧
        1 ≤ s₃ ∧ s₃ ≤ 4 ∧ 1 ≤ s₄ ∧ s₄ ≤ 4 ∧
        2 ≤ (wordL tL).length ∧ 2 ≤ (wordR tR).length ∧
        2 ≤ (wordL tL').length ∧ 2 ≤ (wordR tR').length ∧
        (((wordL tL) ^ s₁).reverse ≠ (wordR tR) ^ s₂ ∨
          ((wordR tR') ^ s₃).reverse ≠ (wordL tL') ^ s₄) ∧
        (wordL tL ≠ wordL tL' ∨ wordR tR ≠ wordR tR' ∨ s₁ ≠ s₂ ∨ s₃ ≠ s₄) ∧
        (∃ (n_lr : ℕ) (L_lr : List TokL) (R_lr : List TokR),
          n_lr ≤ 256 ∧
          iterTransducerMacro stepMacro n_lr (m₀, L₀, R₀) = some (m_lr, L_lr, R_lr) ∧
          L_lr.take (2 * s₁) = List.replicate (2 * s₁) tL) ∧
        (∃ (n_rl : ℕ) (L_rl : List TokL) (R_rl : List TokR),
          n_rl ≤ 256 ∧
          iterTransducerMacro stepMacro n_rl (m₀, L₀, R₀) = some (m_rl, L_rl, R_rl) ∧
          R_rl.take (2 * s₃) = List.replicate (2 * s₃) tR') ∧
        (∀ (n : ℕ) (L : List TokL) (R : List TokR),
          ReachesPlus M
            (evalTransducerCfg m_lr (List.replicate (s₁ * (n + 1)) tL ++ L) R)
            (evalTransducerCfg m_lr L (List.replicate (s₂ * (n + 1)) tR ++ R))) ∧
        (∀ (n : ℕ) (L : List TokL) (R : List TokR),
          ReachesPlus M
            (evalTransducerCfg m_rl L (List.replicate (s₃ * (n + 1)) tR' ++ R))
            (evalTransducerCfg m_rl (List.replicate (s₄ * (n + 1)) tL' ++ L) R)))

end BusyBeaver
