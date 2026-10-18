/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann95Definition
public import Cryptids.Zf380

@[expose] public section
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
