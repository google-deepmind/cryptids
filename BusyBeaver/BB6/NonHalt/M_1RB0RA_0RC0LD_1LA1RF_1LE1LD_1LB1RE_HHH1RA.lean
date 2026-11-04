module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver SixState

@[expose] public section

namespace BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA

end

namespace BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA

open BusyBeaver.Excursion
open M240

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

theorem entry : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) [tm]⊢⁺ Beq 5 [] := by
  have h23 : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) [tm]⊢^{23} Bev 0 [] 4 [] := by
    unfold Bev; rw [encL_nil, encS_nil]; run_steps 23
  exact sp_trans (stepN_to_sp (by decide) h23)
    (sp_trans (bev0_nil_bounce 0 []) (R12 0 []))

theorem is_does_not_halt : IsNotHalt target_tm := by
  exact BusyBeaver.Excursion.does_not_halt_of_advances
    (M240.sp_to_ss entry)
    (M240.root_of_5 M240.validL_nil)
    M240.root_advances

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA
