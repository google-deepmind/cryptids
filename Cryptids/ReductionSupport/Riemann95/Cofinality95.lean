/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.ReductionSupport.Riemann95.WidthLift95
public import Cryptids.ReductionSupport.Riemann95.BootEndpoint95

@[expose] public section

namespace ConjectureMachines.Riemann95

/-- Exact physical stage outcomes, supplied by the arithmetic simulation. -/
def StageOutcomes : Prop := ∀ M P : Nat, M + 21 ≤ P → ∀ extra : List Nat,
    (¬ Riemann120.ShuniaCounterexample (M + 2) →
      ∃ P' ≥ P + 1, ∃ s ≥ 1, ∃ extra',
        nSteps s (Physical.rootCfg P [] ([0,0,0,M,0] ++ extra)) =
          some (Physical.rootCfg P' [] ([0,0,0,M+1,0] ++ extra'))) ∧
    (Riemann120.ShuniaCounterexample (M + 2) →
      ∃ s, ∃ c : ConjectureMachines.Cfg 95 2,
        nSteps s (Physical.rootCfg P [] ([0,0,0,M,0] ++ extra)) = some c ∧
          ConjectureMachines.step machine c = none)

/-- Positive stage progress makes physical runs cofinal in the natural stage index. -/
theorem physical_stage0_halts_iff_witness_of_outcomes (outcomes : StageOutcomes) :
    (StateTransition.eval (ConjectureMachines.step machine)
      (Physical.rootCfg 22 [] ([0,0,0,0,0] ++ List.replicate 4 0))).Dom ↔
      ∃ M : Nat, Riemann120.ShuniaCounterexample (M+2) := by
  classical
  let start := Physical.rootCfg 22 [] ([0,0,0,0,0] ++ List.replicate 4 0)
  have stages : ∀ k : Nat,
      (∀ m : Nat, m < k → ¬ Riemann120.ShuniaCounterexample (m+2)) →
      ∃ P, k+21 ≤ P ∧ ∃ t, k ≤ t ∧ ∃ extra,
        nSteps t start = some (Physical.rootCfg P [] ([0,0,0,k,0] ++ extra)) := by
    intro k
    induction k with
    | zero =>
      intro hs
      exact ⟨22, by omega, 0, by omega, List.replicate 4 0, rfl⟩
    | succ k ih =>
      intro hs
      obtain ⟨P, hP, t, ht, extra, heq⟩ := ih (by
        intro m hmk
        exact hs m (by omega))
      obtain ⟨P', hP', s, hs', extra', hstep⟩ :=
        (outcomes k P hP extra).1 (hs k (by omega))
      refine ⟨P', by omega, t+s, by omega, extra', ?_⟩
      rw [Dispatch.nSteps_composition, heq]
      exact hstep
  have finite : ∀ {a b : ConjectureMachines.Cfg 95 2},
      StateTransition.Reaches (ConjectureMachines.step machine) a b →
      ∃ n, nSteps n a = some b := by
    intro a b hab
    induction hab with
    | refl => exact ⟨0, rfl⟩
    | @tail b c hab hbc ih =>
      obtain ⟨n, hn⟩ := ih
      refine ⟨n+1, ?_⟩
      rw [Dispatch.nSteps_composition, hn]
      change ConjectureMachines.step machine b = some c at hbc
      change (ConjectureMachines.step machine b).bind (fun x => some x) = some c
      rw [hbc]
      rfl
  constructor
  · intro h
    by_contra hw
    have hsafe : ∀ M : Nat, ¬ Riemann120.ShuniaCounterexample (M+2) := by
      intro M hce
      exact hw ⟨M, hce⟩
    let b := (StateTransition.eval (ConjectureMachines.step machine) start).get h
    have hb : b ∈ StateTransition.eval (ConjectureMachines.step machine) start := ⟨h, rfl⟩
    obtain ⟨hr, hstop⟩ := StateTransition.mem_eval.mp hb
    obtain ⟨N, hN⟩ := finite hr
    obtain ⟨P, hP, t, ht, extra, hLong⟩ := stages (N+1) (by
      intro m hm
      exact hsafe m)
    have hadd : t = N + ((t-N-1)+1) := by omega
    rw [hadd, Dispatch.nSteps_composition, hN] at hLong
    change (ConjectureMachines.step machine b).bind (nSteps (t-N-1)) =
      some (Physical.rootCfg P [] ([0,0,0,N+1,0] ++ extra)) at hLong
    rw [hstop] at hLong
    cases hLong
  · intro hw
    let K := Nat.find hw
    have hK : Riemann120.ShuniaCounterexample (K+2) := Nat.find_spec hw
    obtain ⟨P, hP, t, ht, extra, hstage⟩ := stages K (by
      intro m hmk hcem
      have hmin := Nat.find_min' hw hcem
      dsimp [K] at hmk
      omega)
    obtain ⟨s, c, hsteps, hstop⟩ := (outcomes K P hP extra).2 hK
    have hrun : nSteps (t+s) start = some c := by
      rw [Dispatch.nSteps_composition, hstage]
      exact hsteps
    have hr : StateTransition.Reaches (ConjectureMachines.step machine) start c := by
      apply ConjectureMachines.Zf380.nSteps_reaches
      rw [← BootCertificate.nSteps_eq]
      exact hrun
    exact (StateTransition.mem_eval.mpr ⟨hr, hstop⟩).1

end ConjectureMachines.Riemann95
