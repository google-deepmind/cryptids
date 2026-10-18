/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition

@[expose] public section

namespace ConjectureMachines.Riemann95.FinitePrefix

open Turing ConjectureMachines

def prefixStep95 (q : Fin 95) (L R : List (Fin 2)) : Option (Fin 95 × List (Fin 2) × List (Fin
  2)) :=
  match R with
  | [] => none
  | a :: R' =>
    match machine.transition q a with
    | none => none
    | some (w, .right, q') => some (q', w :: L, R')
    | some (w, .left, q') =>
      match L with
      | [] => none
      | a' :: L' => some (q', L', a' :: w :: R')

def prefixRun95 : Nat → Fin 95 → List (Fin 2) → List (Fin 2) → Option (Fin 95 × List (Fin 2) ×
  List (Fin 2))
  | 0, q, L, R => some (q, L, R)
  | n + 1, q, L, R =>
    match prefixStep95 q L R with
    | none => none
    | some (q', L', R') => prefixRun95 n q' L' R'

theorem prefixRun95_sound {n : Nat} {q q' : Fin 95} {L R L' R' : List (Fin 2)} (hr :
  prefixRun95 n q L R = some (q', L', R')) (L₀ R₀ : ListBlank (Fin 2)) : nSteps n ⟨q, Tape.mk'
  (ListBlank.append L L₀) (ListBlank.append R R₀)⟩ = some ⟨q', Tape.mk' (ListBlank.append L' L₀)
  (ListBlank.append R' R₀)⟩ := by
  induction n generalizing q L R with
  | zero =>
    simp only [prefixRun95] at hr
    cases hr
    rfl
  | succ n ih =>
    simp only [prefixRun95] at hr
    cases hs : prefixStep95 q L R with
    | none => simp only [hs] at hr; contradiction
    | some c =>
      rcases c with ⟨q₁, L₁, R₁⟩
      simp only [hs] at hr
      have hstep : step machine ⟨q, Tape.mk' (ListBlank.append L L₀) (ListBlank.append R R₀)⟩ =
          some ⟨q₁, Tape.mk' (ListBlank.append L₁ L₀) (ListBlank.append R₁ R₀)⟩ := by
        cases R with
        | nil => simp only [prefixStep95] at hs; contradiction
        | cons a R =>
          simp only [prefixStep95] at hs
          cases ht : machine.transition q a with
          | none => simp only [ht] at hs; contradiction
          | some t =>
            rcases t with ⟨w, d, qt⟩
            cases d with
            | right =>
              simp only [ht] at hs
              cases hs
              simp [step, Tape.mk', Tape.write, Tape.move, ListBlank.append, ht]
            | left =>
              cases L with
              | nil => simp only [ht] at hs; contradiction
              | cons b L =>
                simp only [ht] at hs
                cases hs
                simp [step, Tape.mk', Tape.write, Tape.move, ListBlank.append, ht]
      rw [nSteps, hstep]
      exact ih hr

end ConjectureMachines.Riemann95.FinitePrefix
