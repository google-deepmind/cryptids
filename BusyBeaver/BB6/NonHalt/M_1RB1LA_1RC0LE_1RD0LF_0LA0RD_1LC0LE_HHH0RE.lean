module

public import BusyBeaver.Bridge
import BusyBeaver.Calculi.SharedDonorsA

open Mathlib Relation Nat Turing BusyBeaver

@[expose] public section

namespace BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

end BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE

end

namespace BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE

open TM24Donor Records Stack Cap

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

set_option maxHeartbeats 2000000 in
set_option maxRecDepth 200000 in
theorem init_to_active :
    (init []) [target_tm]⊢* active (SCap C0) (REnd (seed_offset ++ [1])) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold active stack_side cap_word put_left records_side seed_offset TM24Donor.digits stepCfg
  simp only [List.foldl_cons, List.foldl_nil,
    List.flatMap_cons, List.flatMap_nil,
    listPow_succ, listPow_zero, bit0, bit1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute



theorem is_does_not_halt : IsNotHalt target_tm :=
  isNotHalt_of_neverHaltsFrom init_to_active (source_nonhalt initial_source)

public section

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE
