/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Semantics.PA.Syntax
public import Cryptids.Semantics.PA.Adequacy
public import Cryptids.Semantics.PA.Completeness
public import Cryptids.Semantics.PA.Arithmetic
public import Cryptids.Semantics.PA.Zf380Internal
public import Cryptids.Semantics.PA.Zf393BackendInternal
public import Cryptids.Semantics.PA.Zf393ProgramInternal
public import Cryptids.Semantics.PA.Zf393SoundnessInternal

/-!
# First-Order Peano Arithmetic Semantics & Internalized `ZF` Reductions (`Cryptids.Semantics.PA`)

Re-exports the foundational metatheory of the deeply embedded Peano Arithmetic system `PAProvable`
(`Cryptids.Propositions`) together with the full first-order `PA` internalization of `zf_393` and
`zf_380`:

1. [`Cryptids.Semantics.PA.Syntax`](./PA/Syntax.lean):
   General $\mathcal{L}_{\mathrm{PA}}$-structures (`PAStructure`), models (`PAModel`), classical
   soundness (`paProvable_sound`, `paProvable_sound_nat`), and constructive consistency via the
   Gödel–Gentzen negative translation (`not_paProvable_false`, zero `Classical.choice`).
2. [`Cryptids.Semantics.PA.Adequacy`](./PA/Adequacy.lean):
   Constructive standard-model adequacy of the $\Sigma_1^0$ arithmetizations of binary Turing
   machine halting and `ZF` inconsistency (`paHalts_holds_iff_halts` and
   `paZFInconsistent_holds_iff_zfInconsistent`, zero `Classical.choice`).
3. [`Cryptids.Semantics.PA.Completeness`](./PA/Completeness.lean):
   Gödel–Henkin soundness and completeness across all first-order `PAModel`s
   (`paProvable_iff_holdsIn_all_models`).
4. [`Cryptids.Semantics.PA.Arithmetic`](./PA/Arithmetic.lean):
   Internal arithmetic in arbitrary `PAModel`s (`PAM M`), Euclidean division, `2^k`, Gödel's
   $\beta$-function sequence coding via `PAM.ind1`, Cantor pairing (`mPair`/`mUnpair`), and model
   bridges for `paHalts` and `paZFInconsistent`.
5. [`Cryptids.Semantics.PA.Zf380Internal`](./PA/Zf380Internal.lean):
   First-order `PA` proof of `PAProvable ((paHalts Machines.zf380).iff (paHalts Machines.zf393))`
   (`paProvable_halts_zf380_iff_zf393`).
6. [`Cryptids.Semantics.PA.Zf393BackendInternal`](./PA/Zf393BackendInternal.lean),
   [`Cryptids.Semantics.PA.Zf393ProgramInternal`](./PA/Zf393ProgramInternal.lean), &
   [`Cryptids.Semantics.PA.Zf393SoundnessInternal`](./PA/Zf393SoundnessInternal.lean):
   Full Layer 1–3 internalization of `zf_393` and `zf_380` inside `PAProvable`:
   `paProvable_halts_zf393_iff_zfInconsistent` and `paProvable_halts_zf380_iff_zfInconsistent`.
-/
