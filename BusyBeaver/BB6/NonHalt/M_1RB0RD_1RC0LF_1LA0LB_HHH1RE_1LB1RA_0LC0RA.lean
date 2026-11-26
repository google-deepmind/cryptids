/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import BusyBeaver.Basic
public import BusyBeaver.Bridge
import BusyBeaver.Calculi.Compat
import BusyBeaver.BB6.NonHalt.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC

/-!
# Busy Beaver Machine `1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA` — `is_does_not_halt` (`IsNotHalt
  target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Import`
and defines `target_tm` for `1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

@[expose] public section

/-- Machine `1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA` (Turing machine transition table). -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA"

/-- Target machine on `Fin 2 → Fin 6`. -/
abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end

/-- Transition function for `1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 5, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 2, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 3, 0 => none
  | 3, 1 => some (some 4, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 5, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 5, 1 => some (some 0, Stmt.write 0 Dir.right)

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

private abbrev tmLF : Machine (Fin 2) (Fin 6) :=
  BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.target_tm

/-- State bijection `q_LF ↦ q_RD` (`0↦1, 1↦2, 2↦0, 3↦3, 4↦4, 5↦5`, unmirrored). -/
private def permState : Fin 6 → Fin 6
  | 0 => 1
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 4
  | 5 => 5

private def isoCfg (c : Cfg (Fin 2) (Fin 6)) : Cfg (Fin 2) (Fin 6) :=
  ⟨c.q.map permState, c.tape⟩

private theorem step_iso (c c' : Cfg (Fin 2) (Fin 6))
    (h : step tmLF c = some c') : step target_tm (isoCfg c) = some (isoCfg c') := by
  rcases c with ⟨st, ⟨hd, l, r⟩⟩
  rcases st with _ | ⟨qn, hqn⟩
  · cases h
  · rcases hd with ⟨hn, hhn⟩
    match qn, hn with
    | 0, 0 => cases h; rfl
    | 0, 1 => cases h; rfl
    | 1, 0 => cases h; rfl
    | 1, 1 => cases h; rfl
    | 2, 0 => cases h; rfl
    | 2, 1 => cases h; rfl
    | 3, 0 => cases h
    | 3, 1 => cases h; rfl
    | 4, 0 => cases h; rfl
    | 4, 1 => cases h; rfl
    | 5, 0 => cases h; rfl
    | 5, 1 => cases h; rfl
    | _ + 6, _ => omega
    | _, _ + 2 => omega

private theorem multiStep_iso : ∀ (n : ℕ) (c c' : Cfg (Fin 2) (Fin 6)),
    multiStep tmLF c n = some c' → multiStep target_tm (isoCfg c) n = some (isoCfg c')
  | 0, _, _, h => by
    cases h; rfl
  | n + 1, c, c', h => by
    rw [multiStep, Function.iterate_succ_apply'] at h ⊢
    change (multiStep tmLF c n).bind (step tmLF) = some c' at h
    change (multiStep target_tm (isoCfg c) n).bind (step target_tm) = some (isoCfg c')
    rcases hm : multiStep tmLF c n with _ | cm
    · rw [hm] at h; cases h
    · rw [hm] at h
      rw [multiStep_iso n c cm hm]
      exact step_iso cm c' h

private theorem reachesPlus_iso {c c' : Cfg (Fin 2) (Fin 6)}
    (h : ReachesPlus tmLF c c') : ReachesPlus target_tm (isoCfg c) (isoCfg c') := by
  rcases h with ⟨n, hpos, hn⟩
  exact ⟨n, hpos, multiStep_iso n c c' hn⟩

private def startStateRD : BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.SState :=
  ⟨false, false, [], []⟩

private theorem checkEntry_ok :
    BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.symRunPos 4420 startStateRD =
      some (BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.cpState
        10 ⟨0, 0, 37⟩ ⟨0, 0, 114⟩) :=
  rfl

private theorem init_reaches_entry :
    ReachesStar target_tm (init [])
      (isoCfg (BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.encodeCP 10 37 114)) := by
  have hrun :=
    BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.symRunPos_sound 0 0 checkEntry_ok
  rw [BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.evalSym_cpState] at hrun
  have hiso := reachesPlus_iso hrun
  have hinit :
      isoCfg (BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.evalSym 0 0 startStateRD) =
        init [] := by
    dsimp only [isoCfg, permState,
      BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.evalSym, startStateRD,
      BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.exSide,
      BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.boolToFin2,
      init, Tape.mk₁]
    rfl
  rw [hinit] at hiso
  exact hiso.to_star

private def InAttractor (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ c, BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.InAttractor c ∧ cfg = isoCfg c

private theorem inv_entry :
    BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.Inv 10 37 114 := by
  have hr : BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.remA 10 = 0 := rfl
  refine ⟨by omega, by omega, by omega, by omega⟩

private theorem attractor_closed (cfg : Cfg (Fin 2) (Fin 6)) (h : InAttractor cfg) :
    ∃ cfg', ReachesPlus target_tm cfg cfg' ∧ InAttractor cfg' := by
  rcases h with ⟨c, hc, rfl⟩
  obtain ⟨c', hc', hstep⟩ :=
    BusyBeaver.M_1RB0LF_1LC0LA_1RA0RD_HHH1RE_1LA1RC_0LB0RC.attractor_closed c hc
  exact ⟨isoCfg c', reachesPlus_iso hc', c', hstep, rfl⟩

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm :=
  IsNotHalt.of_reachesPlus_invariant
    init_reaches_entry
    ⟨_, ⟨10, 37, 114, inv_entry, rfl⟩, rfl⟩
    attractor_closed


private theorem target_tm_eq_target : target_tm = target := by
  funext q s
  match q, s with
  | 0, 0 | 0, 1 | 1, 0 | 1, 1 | 2, 0 | 2, 1
  | 3, 0 | 3, 1 | 4, 0 | 4, 1 | 5, 0 | 5, 1 => rfl

public section

/-- The machine `1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA` does not halt from the blank tape. -/
theorem is_not_halt : IsNotHalt target := by
  rw [← target_tm_eq_target]
  exact is_does_not_halt

end

end BusyBeaver.M_1RB0RD_1RC0LF_1LA0LB_HHH1RE_1LB1RA_0LC0RA
