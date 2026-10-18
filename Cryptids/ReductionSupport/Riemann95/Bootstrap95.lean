/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition
public import Cryptids.Zf380

/-! # Blank-tape initialization -/

@[expose] public section

/-! ## Finite execution certificate -/

section

namespace ConjectureMachines.Riemann95.BootCertificate
open Turing
open ConjectureMachines


def runZip : Nat → Fin 95 → List (Fin 2) → Fin 2 → List (Fin 2) →
    Option (Fin 95 × List (Fin 2) × Fin 2 × List (Fin 2))
  | 0, q, L, h, R => some (q, L, h, R)
  | n + 1, q, L, h, R =>
    match Zf380.stepFast machine q L h R with
    | none => none
    | some (q', L', h', R') => runZip n q' L' h' R'

theorem runZip_eq (n : Nat) (q : Fin 95) (L : List (Fin 2)) (h : Fin 2) (R : List (Fin 2)) :
    runZip n q L h R = Zf380.runFast machine n q L h R := by
  induction n generalizing q L h R with
  | zero => rw [runZip, Zf380.runFast]
  | succ n ih =>
    rw [runZip, Zf380.runFast]
    rcases Zf380.stepFast machine q L h R with _ | ⟨q', L', h', R'⟩
    · rfl
    · exact ih q' L' h' R'

def finalL : List (Fin 2) := [1, 0, 0, 0]
def finalR : List (Fin 2) := [
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
  0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

theorem boot_fast :
    runZip 3634 0 [] 0 [] = some (15, finalL, 0, finalR) := by
  decide +kernel

end ConjectureMachines.Riemann95.BootCertificate

end

/-! ## Full tape and halting equivalence -/

section

namespace ConjectureMachines.Riemann95.BootCertificate
open Turing
open ConjectureMachines
open ConjectureMachines.Semantics.Riemann.Layer1 (default_cons_zero)


theorem finalCfg_eq_initialRoot :
    Zf380.cfgOfFast 15 finalL 0 finalR = initialRoot := by
  have hL : ListBlank.append finalL (default : ListBlank (Fin 2)) =
      ListBlank.cons 1 default := by
    simp only [finalL, ListBlank.append, default_cons_zero]
  have hR : (ListBlank.append finalR (default : ListBlank (Fin 2))).cons 0 =
      ListBlank.mk (ConjectureMachines.Riemann120.mapStack [] ++
        List.replicate (22 - (ConjectureMachines.Riemann120.mapStack []).length) 0 ++
        [1, 0] ++ ConjectureMachines.Semantics.Riemann.Layer1.encodeRegs
          (initialRegs ++ initialExtra)) := by
    change ListBlank.cons 0 (ListBlank.append finalR (ListBlank.mk [])) = _
    rw [ListBlank.append_mk, List.append_nil, ListBlank.cons_mk]
    rfl
  unfold Zf380.cfgOfFast initialRoot
  rw [hL, hR]

theorem nSteps_eq (n : Nat) (c : Cfg 95 2) :
    Riemann95.nSteps n c = Zf380.nSteps machine n c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    change (step machine c).bind (Riemann95.nSteps n) =
      (step machine c).bind (Zf380.nSteps machine n)
    congr 1
    funext d
    exact ih d

/-- Exact 3,634-step blank bootstrap, including the full tape. -/
theorem boot_reaches_initialRoot :
    Riemann95.nSteps 3634 (init : Cfg 95 2) = some initialRoot := by
  rw [nSteps_eq, Zf380.init_eq_cfgOfFast, Zf380.nSteps_of_runFast,
      ← runZip_eq, boot_fast, Option.map_some]
  rw [finalCfg_eq_initialRoot]

/-- The finite prefix may be removed from the remaining halting proof. -/
theorem halts_iff_initialRoot :
    Halts candidate ↔ (StateTransition.eval (step machine) initialRoot).Dom := by
  change (StateTransition.eval (step machine) (init : Cfg 95 2)).Dom ↔ _
  have h : Zf380.nSteps machine 3634 (init : Cfg 95 2) = some initialRoot := by
    rw [← nSteps_eq]
    exact boot_reaches_initialRoot
  exact Zf380.nSteps_eval_dom h


end ConjectureMachines.Riemann95.BootCertificate

end
