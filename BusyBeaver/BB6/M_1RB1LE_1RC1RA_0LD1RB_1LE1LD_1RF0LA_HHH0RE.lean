/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`

We define the configuration for $b, d \ge 0$:

$$
E(b, d) := 0^\infty \ (10)^b \ 1111 \ \mathrm{E}{>} \ 1^{d+2} \ 0^\infty.
$$

Starting from $E(0, 1)$ (reached after 28 steps from the blank tape), with $c = d + 1$ and
$m = \lfloor d / 2 \rfloor$, the machine follows the map $T$:

$$
T(E(b, d)) = \begin{cases}
  E(0, 2c+3) & \text{if } b = m+1, \\
  E(2, 2c+1) & \text{if } b = m+2, \\
  E(b-m-3, 2c+5) & \text{if } b \ge m+3, \\
  E(0, 2c+2) & \text{if } b \le m \text{ and } c - 2b \le 2, \\
  \text{Halt} & \text{if } b \le m \text{ and } c - 2b = 3, \\
  E(2b+2, 2(c-2b)-7) & \text{if } b \le m \text{ and } 4 \le c - 2b \le 6, \\
  E(2b+4, c-2b-7) & \text{if } b \le m \text{ and } c - 2b \ge 7.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some E, Stmt.write 1 Dir.left) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
private theorem target_B_1 : target B 1 = some (some A, Stmt.write 1 Dir.right) := rfl
private theorem target_C_0 : target C 0 = some (some D, Stmt.write 0 Dir.left) := rfl
private theorem target_C_1 : target C 1 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_D_0 : target D 0 = some (some E, Stmt.write 1 Dir.left) := rfl
private theorem target_D_1 : target D 1 = some (some D, Stmt.write 1 Dir.left) := rfl
private theorem target_E_0 : target E 0 = some (some F, Stmt.write 1 Dir.right) := rfl
private theorem target_E_1 : target E 1 = some (some A, Stmt.write 0 Dir.left) := rfl
private theorem target_F_0 : target F 0 = none := rfl
private theorem target_F_1 : target F 1 = some (some E, Stmt.write 0 Dir.right) := rfl

local macro "pat_step" : tactic =>
  `(tactic| (
    simp only [evalTapePattern_some, evalTapeExpr_default, evalTapeExpr_sym, evalTapeExpr_rep,
      list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append, List.nil_append,
      ListBlank.append_nil, ListBlank.append_cons, Cfg.headRight, step,
      target_A_0, target_A_1, target_B_0, target_B_1, target_C_0, target_C_1,
      target_D_0, target_D_1, target_E_0, target_E_1, target_F_0, target_F_1,
      Option.map, Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.head_default_fin, ListBlank.tail_default, ListBlank.cons_zero_default]))

private def pat_0 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .default }

private def pat_3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some C
    right := .default }

private def pat_5 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .default }

private def pat_6 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_7 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_8 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_9 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_10 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_11 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_12 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_13 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_14 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_15 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_16 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_17 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_18 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_19 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .default }

private def pat_20 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_21 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_22 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_23 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .default }

private def pat_24 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_25 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_26 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_27 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some C
    right := .default }

private def pat_28 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_29 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_30 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .default }

private def pat_31 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_32 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .default }

private def pat_33 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_34 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_35 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_36 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .default }

private def pat_37 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .default }

private def pat_38 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_39 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_40 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .default }

private def pat_41 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_42 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .default }

private def pat_43 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_44 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some E
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_45 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_46 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some C
    right := .default }

private def pat_47 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some C
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_48 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_49 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_50 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_51 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_52 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_53 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_54 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_55 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_56 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_57 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_58 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some A
    right := .default }

private def pat_59 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some A
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_60 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_61 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_62 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some E
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_63 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_64 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_65 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_66 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_67 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_68 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_69 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some A
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

private def pat_70 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_71 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_72 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_73 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_74 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_75 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_76 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_77 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .sym 0 (.sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_78 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 1 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_79 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.rep [1, 1] 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 .default))))))
    head := some C
    right := .sym 1 (.sym 0 (.rep [1, 0] 2 (.sym 1 (.rep [1] 3 .default)))) }

/-- Canonical tape pattern
$D(a, b, c) := 0^\infty\,(10)^b\,(11)^{a+1}\,\mathrm{D}{>}\,1^{c+1}\,0^\infty$. -/
def pat_D : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some D
    right := .sym 1 (.rep [1] 2 .default) }

/-- Canonical tape pattern
$E(a, b, c) := 0^\infty\,(10)^b\,(11)^{a+1}\,\mathrm{E}{>}\,1^{c+1}\,0^\infty$. -/
def pat_E : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.rep [1, 1] 0 (.rep [0, 1] 1 .default)))
    head := some E
    right := .sym 1 (.rep [1] 2 .default) }

/-- Closed pattern set for `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`. -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_D, .true), (pat_E, .true)]

private theorem mem_ps_D : (pat_D, VarCond.true) ∈ ps :=
  .head _

private theorem in_ps_D (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_D vars) :=
  ⟨(pat_D, .true), mem_ps_D, vars, rfl, trivial⟩

private theorem mem_ps_E : (pat_E, VarCond.true) ∈ ps :=
  .tail _ (.head _)

private theorem in_ps_E (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_E vars) :=
  ⟨(pat_E, .true), mem_ps_E, vars, rfl, trivial⟩

private theorem in_ps_7 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_7 vars) :=
  in_ps_D fun k => match k with | 0 => vars 0 | 1 => 0 | 2 => vars 1 | _ => 0

private theorem in_ps_51 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_51 vars) :=
  in_ps_D fun k => match k with | 0 => vars 0 | 1 => vars 1 + 1 | 2 => vars 2 | _ => 0

private theorem in_ps_8 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_8 vars) :=
  in_ps_E fun k => match k with | 0 => vars 0 | 1 => 0 | 2 => vars 1 | _ => 0

private theorem in_ps_62 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_62 vars) :=
  in_ps_E fun k => match k with | 0 => vars 0 | 1 => vars 1 + 1 | 2 => vars 2 | _ => 0

private theorem step_base {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    (h_in : IsInPatternSet ps c₂) :
    ∃ cfg', ReachesPlus target c₁ cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  ⟨c₂, ReachesPlus.single h_step, Or.inl h_in⟩

private theorem step_chain {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    (h_next : ∃ cfg', ReachesPlus target c₂ cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone)) :
    ∃ cfg', ReachesPlus target c₁ cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_next with ⟨cfg', h₂, h_in⟩
  exact ⟨cfg', (ReachesPlus.single h_step).trans h₂, h_in⟩

private theorem step_pat_4 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_4 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_base ?_ (in_ps_7 (fun k => match k with | 0 => vars 0 | 1 => 0 | _ => 0))
  dsimp only [pat_4, pat_7, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_2 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_2 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_4 (fun k => match k with | 0 => vars 0 | _ => 0))
  dsimp only [pat_2, pat_4, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_5 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_5 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_2 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
  dsimp only [pat_5, pat_2, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_6 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_6 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_base ?_ (in_ps_8 (fun k => match k with | 0 => vars 0 | 1 => 1 | _ => 0))
    dsimp only [pat_6, pat_8, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base ?_
      (in_ps_8 (fun k => match k with | 0 => vars 0 | 1 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_6, pat_8, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_3 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_3 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_5 (fun k => match k with | 0 => vars 0 | _ => 0))
    dsimp only [pat_3, pat_5, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_6 (fun k => match k with | 0 => vars 0 | 1 => u | _ => 0))
    dsimp only [pat_3, pat_6, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_1 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_1 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_2 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
    dsimp only [pat_1, pat_2, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_3 (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | _ => 0))
    dsimp only [pat_1, pat_3, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_0 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_0 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_1 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_0, pat_1, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_10 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_10 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_base ?_ (in_ps_7 (fun k => match k with | 0 => vars 0 | 1 => 1 | _ => 0))
    dsimp only [pat_10, pat_7, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base ?_
      (in_ps_7 (fun k => match k with | 0 => vars 0 | 1 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_10, pat_7, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_30 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_30 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine ⟨Cfg.headRight F
    (ListBlank.append [1, 0, 1]
      (ListBlank.append (([0, 1] : List (Fin 2)) ^ vars 0) default))
    default, ReachesPlus.single ?_, Or.inr (by bb_halt)⟩
  dsimp only [pat_30, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_36 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_36 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_2 (fun k => match k with | 0 => 0 | _ => 0))
  dsimp only [pat_36, pat_2, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_46 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_46 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_base ?_
    (in_ps_51 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => 0 | _ => 0))
  dsimp only [pat_46, pat_51, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_42 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_42 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_46 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_42, pat_46, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_37 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_37 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_42 (fun k => match k with | 0 => 0 | 1 => vars 0 | _ => 0))
  dsimp only [pat_37, pat_42, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_38 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_38 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_0 (fun k => match k with | 0 => 0 | 1 => vars 0 | _ => 0))
  dsimp only [pat_38, pat_0, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_58 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_58 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_42 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | _ => 0))
  dsimp only [pat_58, pat_42, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_59 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_59 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · refine step_base ?_
      (in_ps_62 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => 1 | _ => 0))
    dsimp only [pat_59, pat_62, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base ?_
      (in_ps_62 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_59, pat_62, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_52 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_52 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_58 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
    dsimp only [pat_52, pat_58, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_59 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => u | _ => 0))
    dsimp only [pat_52, pat_59, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_47 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_47 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_
      (step_pat_42 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | _ => 0))
    dsimp only [pat_47, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_52 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | 2 => u | _ => 0))
    dsimp only [pat_47, pat_52, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_43 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_43 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_47 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => vars 2 | _ => 0))
  dsimp only [pat_43, pat_47, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_39 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_39 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_43 (fun k => match k with | 0 => 0 | 1 => vars 0 | 2 => vars 1 | _ => 0))
  dsimp only [pat_39, pat_43, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_31 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_31 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_36 (fun _ => 0))
      dsimp only [pat_31, pat_36, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_37 (fun k => match k with | 0 => v | _ => 0))
      dsimp only [pat_31, pat_37, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_38 (fun k => match k with | 0 => u | _ => 0))
      dsimp only [pat_31, pat_38, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_39 (fun k => match k with | 0 => v | 1 => u | _ => 0))
      dsimp only [pat_31, pat_39, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem step_pat_26 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_26 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_30 (fun k => match k with | 0 => 0 | _ => 0))
    dsimp only [pat_26, pat_30, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_31 (fun k => match k with | 0 => 0 | 1 => u | _ => 0))
    dsimp only [pat_26, pat_31, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_22 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_22 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_26 (fun k => match k with | 0 => vars 0 | _ => 0))
  dsimp only [pat_22, pat_26, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_18 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_18 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_22 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
  dsimp only [pat_18, pat_22, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_14 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_14 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_18 (fun k => match k with | 0 => 0 | _ => 0))
    dsimp only [pat_14, pat_18, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_18 (fun k => match k with | 0 => (u + 1) | _ => 0))
    dsimp only [pat_14, pat_18, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_9 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_9 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_14 (fun k => match k with | 0 => 1 | _ => 0))
    dsimp only [pat_9, pat_14, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_14 (fun k => match k with | 0 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_9, pat_14, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_27 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_27 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_9 (fun k => match k with | 0 => 0 | _ => 0))
    dsimp only [pat_27, pat_9, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_10 (fun k => match k with | 0 => v | 1 => 0 | _ => 0))
    dsimp only [pat_27, pat_10, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private theorem step_pat_23 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_23 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_27 (fun k => match k with | 0 => 0 | _ => 0))
  dsimp only [pat_23, pat_27, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_19 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_19 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_23 (fun _ => 0))
  dsimp only [pat_19, pat_23, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_32 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_32 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_27 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
  dsimp only [pat_32, pat_27, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_40 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_40 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_32 (fun k => match k with | 0 => vars 0 | _ => 0))
  dsimp only [pat_40, pat_32, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_48 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_48 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_22 (fun k => match k with | 0 => 0 | _ => 0))
    dsimp only [pat_48, pat_22, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_22 (fun k => match k with | 0 => (u + 1) | _ => 0))
    dsimp only [pat_48, pat_22, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_70 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_70 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_30 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
    dsimp only [pat_70, pat_30, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_31 (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | _ => 0))
    dsimp only [pat_70, pat_31, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_63 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_63 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_70 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_63, pat_70, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_71 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_71 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine step_chain ?_
      (step_pat_63 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 2 | _ => 0))
    dsimp only [pat_71, pat_63, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine @step_chain _
      (evalTapePattern pat_64
        (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | 2 => vars 2 | _ => 0))
      ?_
      (step_chain ?_
        (ih
          (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | 2 => vars 2 | _ => 0) rfl))
    · dsimp only [pat_71, pat_64, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_64, pat_71, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_64 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_64 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_71 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => vars 2 | _ => 0))
  dsimp only [pat_64, pat_71, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_60 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_60 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_63 (fun k => match k with | 0 => 0 | 1 => vars 1 | _ => 0))
    dsimp only [pat_60, pat_63, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_64 (fun k => match k with | 0 => 0 | 1 => u | 2 => vars 1 | _ => 0))
    dsimp only [pat_60, pat_64, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_53 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_53 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_60 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_53, pat_60, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_49 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_49 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_53 (fun k => match k with | 0 => 0 | 1 => vars 1 | _ => 0))
    dsimp only [pat_49, pat_53, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_53 (fun k => match k with | 0 => (u + 1) | 1 => vars 1 | _ => 0))
    dsimp only [pat_49, pat_53, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_44 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_44 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_48 (fun k => match k with | 0 => 0 | _ => 0))
    dsimp only [pat_44, pat_48, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_49 (fun k => match k with | 0 => 0 | 1 => u | _ => 0))
    dsimp only [pat_44, pat_49, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_54 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_54 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_49 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | _ => 0))
  dsimp only [pat_54, pat_49, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_50 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_50 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · refine step_chain ?_ (step_pat_54 (fun k => match k with | 0 => 0 | 1 => vars 2 | _ => 0))
      dsimp only [pat_50, pat_54, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_54 (fun k => match k with | 0 => (u + 1) | 1 => vars 2 | _ => 0))
      dsimp only [pat_50, pat_54, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · refine @step_chain _
        (evalTapePattern pat_55
          (fun k => match k with | 0 => v | 1 => 0 | 2 => vars 2 | _ => 0))
        ?_
        (step_chain ?_ (ih (fun k => match k with | 0 => v | 1 => 1 | 2 => vars 2 | _ => 0) rfl))
      · dsimp only [pat_50, pat_55, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [pat_55, pat_50, evalTapePattern, evalTapeExpr]; pat_step
    · refine @step_chain _
        (evalTapePattern pat_55
          (fun k => match k with | 0 => v | 1 => (u + 1) | 2 => vars 2 | _ => 0))
        ?_
        (step_chain ?_
          (ih
            (fun k => match k with | 0 => v | 1 => ((u + 1) + 1) | 2 => vars 2 | _ => 0) rfl))
      · dsimp only [pat_50, pat_55, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [pat_55, pat_50, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_41 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_41 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_44 (fun k => match k with | 0 => 1 | _ => 0))
      dsimp only [pat_41, pat_44, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine @step_chain _
        (evalTapePattern pat_45
          (fun k => match k with | 0 => v | 1 => 1 | _ => 0))
        ?_
        (step_chain ?_ (step_pat_50 (fun k => match k with | 0 => v | 1 => 0 | 2 => 0 | _ => 0)))
      · dsimp only [pat_41, pat_45, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [pat_45, pat_50, evalTapePattern, evalTapeExpr]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_44 (fun k => match k with | 0 => ((u + 1) + 1) | _ => 0))
      dsimp only [pat_41, pat_44, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine @step_chain _
        (evalTapePattern pat_45
          (fun k => match k with | 0 => v | 1 => ((u + 1) + 1) | _ => 0))
        ?_
        (step_chain ?_
          (step_pat_50
            (fun k => match k with | 0 => v | 1 => 0 | 2 => (u + 1) | _ => 0)))
      · dsimp only [pat_41, pat_45, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
      · dsimp only [pat_45, pat_50, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_33 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_33 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_40 (fun k => match k with | 0 => (vars 0 + 1) | _ => 0))
    dsimp only [pat_33, pat_40, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_41 (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | _ => 0))
    dsimp only [pat_33, pat_41, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_28 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_28 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_32 (fun k => match k with | 0 => vars 0 | _ => 0))
    dsimp only [pat_28, pat_32, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_33 (fun k => match k with | 0 => vars 0 | 1 => u | _ => 0))
    dsimp only [pat_28, pat_33, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_24 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_24 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_28 (fun k => match k with | 0 => 0 | 1 => vars 0 | _ => 0))
  dsimp only [pat_24, pat_28, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_20 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_20 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_24 (fun k => match k with | 0 => vars 0 | _ => 0))
  dsimp only [pat_20, pat_24, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_15 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_15 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_19 (fun _ => 0))
    dsimp only [pat_15, pat_19, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_20 (fun k => match k with | 0 => u | _ => 0))
    dsimp only [pat_15, pat_20, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_11 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_11 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_15 (fun k => match k with | 0 => 1 | _ => 0))
    dsimp only [pat_11, pat_15, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_15 (fun k => match k with | 0 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_11, pat_15, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_34 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_34 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_28 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | _ => 0))
  dsimp only [pat_34, pat_28, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_29 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_29 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine step_chain ?_ (step_pat_34 (fun k => match k with | 0 => vars 0 | 1 => vars 2 | _ => 0))
    dsimp only [pat_29, pat_34, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine @step_chain _
      (evalTapePattern pat_35
        (fun k => match k with | 0 => vars 0 | 1 => u | 2 => vars 2 | _ => 0))
      ?_
      (step_chain ?_
        (ih
          (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | 2 => vars 2 | _ => 0) rfl))
    · dsimp only [pat_29, pat_35, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_35, pat_29, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_25 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_25 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_29 (fun k => match k with | 0 => 0 | 1 => vars 0 | 2 => vars 1 | _ => 0))
  dsimp only [pat_25, pat_29, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_21 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_21 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_25 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_21, pat_25, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_16 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_16 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_21 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | _ => 0))
  dsimp only [pat_16, pat_21, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_12 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_12 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_16 (fun k => match k with | 0 => 0 | 1 => vars 1 | _ => 0))
    dsimp only [pat_12, pat_16, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_16 (fun k => match k with | 0 => (u + 1) | 1 => vars 1 | _ => 0))
    dsimp only [pat_12, pat_16, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_17 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_17 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine step_chain ?_
      (step_pat_12 (fun k => match k with | 0 => (vars 1 + 1) | 1 => vars 2 | _ => 0))
    dsimp only [pat_17, pat_12, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine @step_chain _
      (evalTapePattern pat_13
        (fun k => match k with | 0 => v | 1 => (vars 1 + 1) | 2 => vars 2 | _ => 0))
      ?_
      (step_chain ?_
        (ih
          (fun k => match k with | 0 => v | 1 => (vars 1 + 1) | 2 => vars 2 | _ => 0) rfl))
    · dsimp only [pat_17, pat_13, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_13, pat_17, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_13 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_13 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_
      (step_pat_17 (fun k => match k with | 0 => vars 0 | 1 => 0 | 2 => vars 2 | _ => 0))
    dsimp only [pat_13, pat_17, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_17 (fun k => match k with | 0 => vars 0 | 1 => (u + 1) | 2 => vars 2 | _ => 0))
    dsimp only [pat_13, pat_17, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_35 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_35 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_29 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | 2 => vars 2 | _ => 0))
  dsimp only [pat_35, pat_29, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_65 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_65 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_ (step_pat_15 (fun k => match k with | 0 => ((vars 0 + 1) + 1) | _ => 0))
  dsimp only [pat_65, pat_15, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_66 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_66 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_31 (fun k => match k with | 0 => vars 0 | 1 => ((vars 1 + 1) + 1) | _ => 0))
  dsimp only [pat_66, pat_31, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_61 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_61 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_65 (fun k => match k with | 0 => 0 | _ => 0))
      dsimp only [pat_61, pat_65, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_66 (fun k => match k with | 0 => v | 1 => 0 | _ => 0))
      dsimp only [pat_61, pat_66, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_65 (fun k => match k with | 0 => (u + 1) | _ => 0))
      dsimp only [pat_61, pat_65, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_66 (fun k => match k with | 0 => v | 1 => (u + 1) | _ => 0))
      dsimp only [pat_61, pat_66, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem step_pat_56 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_56 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_61 (fun k => match k with | 0 => vars 0 | 1 => 1 | _ => 0))
    dsimp only [pat_56, pat_61, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_61 (fun k => match k with | 0 => vars 0 | 1 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_56, pat_61, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_57 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_57 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · refine step_base ?_
      (in_ps_51 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => 1 | _ => 0))
    dsimp only [pat_57, pat_51, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base ?_
      (in_ps_51 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_57, pat_51, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_51 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_51 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_56 (fun k => match k with | 0 => vars 1 | 1 => 1 | _ => 0))
      dsimp only [pat_51, pat_56, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_57 (fun k => match k with | 0 => v | 1 => vars 1 | 2 => 1 | _ => 0))
      dsimp only [pat_51, pat_57, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_
        (step_pat_56 (fun k => match k with | 0 => vars 1 | 1 => ((u + 1) + 1) | _ => 0))
      dsimp only [pat_51, pat_56, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_57 (fun k => match k with | 0 => v | 1 => vars 1 | 2 => ((u + 1) + 1) | _ => 0))
      dsimp only [pat_51, pat_57, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem step_pat_55 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_55 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_50 (fun k => match k with | 0 => vars 0 | 1 => (vars 1 + 1) | 2 => vars 2 | _ => 0))
  dsimp only [pat_55, pat_50, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_67 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_67 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_31 (fun k => match k with | 0 => vars 0 | 1 => 1 | _ => 0))
    dsimp only [pat_67, pat_31, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_31 (fun k => match k with | 0 => vars 0 | 1 => ((u + 1) + 1) | _ => 0))
    dsimp only [pat_67, pat_31, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_78 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_78 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine step_chain ?_
      (step_pat_0 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 2 | _ => 0))
    dsimp only [pat_78, pat_0, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine @step_chain _
      (evalTapePattern pat_76
        (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | 2 => vars 2 | _ => 0))
      ?_
      (step_chain ?_
        (ih
          (fun k => match k with | 0 => (vars 0 + 1) | 1 => u | 2 => vars 2 | _ => 0) rfl))
    · dsimp only [pat_78, pat_76, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_76, pat_78, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_76 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_76 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_78 (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => vars 2 | _ => 0))
  dsimp only [pat_76, pat_78, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_74 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_74 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_76 (fun k => match k with | 0 => 0 | 1 => vars 0 | 2 => vars 1 | _ => 0))
  dsimp only [pat_74, pat_76, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_79 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_79 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    refine step_chain ?_
      (step_pat_43 (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | 2 => vars 3 | _ => 0))
    dsimp only [pat_79, pat_43, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine @step_chain _
      (evalTapePattern pat_77
        (fun k => match k with | 0 => (vars 0 + 1) | 1 => vars 1 | 2 => u | 3 => vars 3 | _ => 0))
      ?_
      (step_chain ?_
        (ih (fun k =>
          match k with | 0 => (vars 0 + 1) | 1 => vars 1 | 2 => u | 3 => vars 3 | _ => 0) rfl))
    · dsimp only [pat_79, pat_77, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_77, pat_79, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_77 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_77 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_79
      (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => vars 2 | 3 => vars 3 | _ => 0))
  dsimp only [pat_77, pat_79, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_75 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_75 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  refine step_chain ?_
    (step_pat_77
      (fun k => match k with | 0 => 0 | 1 => vars 0 | 2 => vars 1 | 3 => vars 2 | _ => 0))
  dsimp only [pat_75, pat_77, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_72 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_72 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_74 (fun k => match k with | 0 => vars 1 | 1 => vars 2 | _ => 0))
    dsimp only [pat_72, pat_74, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_
      (step_pat_75 (fun k => match k with | 0 => v | 1 => vars 1 | 2 => vars 2 | _ => 0))
    dsimp only [pat_72, pat_75, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private theorem step_pat_68 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_68 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_
      (step_pat_72 (fun k => match k with | 0 => vars 0 | 1 => 0 | 2 => vars 2 | _ => 0))
    dsimp only [pat_68, pat_72, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_72 (fun k => match k with | 0 => vars 0 | 1 => (u + 1) | 2 => vars 2 | _ => 0))
    dsimp only [pat_68, pat_72, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_73 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_73 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine step_chain ?_
      (step_pat_68 (fun k => match k with | 0 => vars 1 | 1 => (vars 2 + 1) | 2 => vars 3 | _ => 0))
    dsimp only [pat_73, pat_68, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine @step_chain _
      (evalTapePattern pat_69
        (fun k => match k with | 0 => v | 1 => vars 1 | 2 => (vars 2 + 1) | 3 => vars 3 | _ => 0))
      ?_
      (step_chain ?_
        (ih (fun k =>
          match k with | 0 => v | 1 => vars 1 | 2 => (vars 2 + 1) | 3 => vars 3 | _ => 0) rfl))
    · dsimp only [pat_73, pat_69, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_69, pat_73, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_69 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_69 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_
      (step_pat_73
        (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => 0 | 3 => vars 3 | _ => 0))
    dsimp only [pat_69, pat_73, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_
      (step_pat_73
        (fun k => match k with | 0 => vars 0 | 1 => vars 1 | 2 => (u + 1) | 3 => vars 3 | _ => 0))
    dsimp only [pat_69, pat_73, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_62 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_62 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 2 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_67 (fun k => match k with | 0 => vars 1 | 1 => 0 | _ => 0))
      dsimp only [pat_62, pat_67, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_59 (fun k => match k with | 0 => v | 1 => vars 1 | 2 => 0 | _ => 0))
      dsimp only [pat_62, pat_59, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_
        (step_pat_68 (fun k => match k with | 0 => vars 1 | 1 => 0 | 2 => u | _ => 0))
      dsimp only [pat_62, pat_68, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_69 (fun k => match k with | 0 => v | 1 => vars 1 | 2 => 0 | 3 => u | _ => 0))
      dsimp only [pat_62, pat_69, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem step_pat_7 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_7 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_9 (fun k => match k with | 0 => 1 | _ => 0))
      dsimp only [pat_7, pat_9, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_10 (fun k => match k with | 0 => v | 1 => 1 | _ => 0))
      dsimp only [pat_7, pat_10, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_9 (fun k => match k with | 0 => ((u + 1) + 1) | _ => 0))
      dsimp only [pat_7, pat_9, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_
        (step_pat_10 (fun k => match k with | 0 => v | 1 => ((u + 1) + 1) | _ => 0))
      dsimp only [pat_7, pat_10, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem step_pat_8 (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_8 vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_11 (fun k => match k with | 0 => 0 | _ => 0))
      dsimp only [pat_8, pat_11, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_6 (fun k => match k with | 0 => v | 1 => 0 | _ => 0))
      dsimp only [pat_8, pat_6, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_12 (fun k => match k with | 0 => 0 | 1 => u | _ => 0))
      dsimp only [pat_8, pat_12, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step
    · refine step_chain ?_ (step_pat_13 (fun k => match k with | 0 => v | 1 => 0 | 2 => u | _ => 0))
      dsimp only [pat_8, pat_13, evalTapePattern, evalTapeExpr]; rw [h_vr, h_vl]; pat_step

private theorem rule_D_b0 (vars : ℕ → ℕ) (h_b : vars 1 = 0) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_D vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h_eq :
      evalTapePattern pat_D vars =
        evalTapePattern pat_7 fun k =>
          match k with | 0 => vars 0 | 1 => vars 2 | _ => 0 := by
    dsimp only [pat_D, pat_7, evalTapePattern, evalTapeExpr]
    rw [h_b]
    rfl
  rw [h_eq]
  exact step_pat_7 fun k => match k with | 0 => vars 0 | 1 => vars 2 | _ => 0

private theorem rule_D_succ (vars : ℕ → ℕ) (u : ℕ) (h_b : vars 1 = u + 1) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_D vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h_eq :
      evalTapePattern pat_D vars =
        evalTapePattern pat_51 fun k =>
          match k with | 0 => vars 0 | 1 => u | 2 => vars 2 | _ => 0 := by
    dsimp only [pat_D, pat_51, evalTapePattern, evalTapeExpr]
    rw [h_b]
    rfl
  rw [h_eq]
  exact step_pat_51 fun k => match k with | 0 => vars 0 | 1 => u | 2 => vars 2 | _ => 0

private theorem rule_E_b0 (vars : ℕ → ℕ) (h_b : vars 1 = 0) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_E vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h_eq :
      evalTapePattern pat_E vars =
        evalTapePattern pat_8 fun k =>
          match k with | 0 => vars 0 | 1 => vars 2 | _ => 0 := by
    dsimp only [pat_E, pat_8, evalTapePattern, evalTapeExpr]
    rw [h_b]
    rfl
  rw [h_eq]
  exact step_pat_8 fun k => match k with | 0 => vars 0 | 1 => vars 2 | _ => 0

private theorem rule_E_succ (vars : ℕ → ℕ) (u : ℕ) (h_b : vars 1 = u + 1) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_E vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  have h_eq :
      evalTapePattern pat_E vars =
        evalTapePattern pat_62 fun k =>
          match k with | 0 => vars 0 | 1 => u | 2 => vars 2 | _ => 0 := by
    dsimp only [pat_E, pat_62, evalTapePattern, evalTapeExpr]
    rw [h_b]
    rfl
  rw [h_eq]
  exact step_pat_62 fun k => match k with | 0 => vars 0 | 1 => u | 2 => vars 2 | _ => 0

private theorem step_pat_D (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_D vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_v1 : vars 1 with _ | u
  · exact rule_D_b0 vars h_v1
  · exact rule_D_succ vars u h_v1

private theorem step_pat_E (vars : ℕ → ℕ) :
    ∃ cfg', ReachesPlus target (evalTapePattern pat_E vars) cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_v1 : vars 1 with _ | u
  · exact rule_E_b0 vars h_v1
  · exact rule_E_succ vars u h_v1

private theorem init_reaches_pat_D :
    ReachesStar target (init [])
      (evalTapePattern pat_D fun k =>
        match k with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 0) := by
  dsimp only [pat_D, evalTapePattern, evalTapeExpr]
  bb_steps

private theorem init_reaches_ps :
    ∃ cfg₀, ReachesStar target (init []) cfg₀ ∧ IsInPatternSet ps cfg₀ :=
  ⟨evalTapePattern pat_D fun k => match k with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 0,
    init_reaches_pat_D,
    in_ps_D fun k => match k with | 0 => 1 | 1 => 0 | 2 => 0 | _ => 0⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨init_reaches_ps, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact step_pat_D vars
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact step_pat_E vars
  · nomatch h_mem

/-- `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`. -/
inductive State where
  /-- $D(a, b, c) := 0^\infty\,(10)^b\,(11)^{a+1}\,\mathrm{D}{>}\,1^{c+1}\,0^\infty$. -/
  | D (a b c : ℕ)
  /-- $E(a, b, c) := 0^\infty\,(10)^b\,(11)^{a+1}\,\mathrm{E}{>}\,1^{c+1}\,0^\infty$. -/
  | E (a b c : ℕ)

/-- Initial symbolic state $D(1, 0, 0)$, reached after 14 raw TM steps. -/
def start : State := .D 1 0 0

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .D a b c =>
    evalTapePattern pat_D fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0
  | .E a b c =>
    evalTapePattern pat_E fun k => match k with | 0 => a | 1 => b | 2 => c | _ => 0

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .D (a + 1) b c => some (.D a b (c + 2))
  | .D 0 0 0 => some (.D 2 0 0)
  | .D 0 0 (c + 1) => some (.E 1 0 (c + 1))
  | .D 0 1 0 => some (.D 0 2 0)
  | .D 0 1 1 => some (.D 1 2 0)
  | .D 0 1 2 => some (.D 2 2 0)
  | .D 0 1 (c + 3) => some (.E 1 2 (c + 1))
  | .D 0 (b + 2) c => some (.E 1 b (c + 2))
  | .E (a + 1) b 0 => some (.E a b 1)
  | .E 0 0 0 => some (.D 0 0 1)
  | .E 0 (b + 1) 0 => some (.D 1 b 0)
  | .E a 0 1 => some (.D (a + 1) 0 1)
  | .E a 0 2 => some (.D (a + 2) 0 1)
  | .E _ 0 3 => none
  | .E a 0 4 => some (.D 0 (a + 3) 0)
  | .E a 0 5 => some (.D 1 (a + 3) 0)
  | .E a 0 6 => some (.D 2 (a + 3) 0)
  | .E a 0 (c + 7) => some (.E 1 (a + 3) (c + 1))
  | .E a (b + 1) 1 => some (.D (a + 2) b 0)
  | .E a (b + 1) 2 => some (.D (a + 3) b 0)
  | .E a (b + 1) (c + 3) => some (.E (a + 2) b (c + 1))

private abbrev v2 (x y : ℕ) : ℕ → ℕ :=
  fun k => match k with | 0 => x | 1 => y | _ => 0

private abbrev v3 (x y z : ℕ) : ℕ → ℕ :=
  fun k => match k with | 0 => x | 1 => y | 2 => z | _ => 0

private abbrev v4 (x y z w : ℕ) : ℕ → ℕ :=
  fun k => match k with | 0 => x | 1 => y | 2 => z | 3 => w | _ => 0

local macro "pat_steps" : tactic =>
  `(tactic| (
    dsimp only [encode, v2, v3, v4, pat_D, pat_E,
      pat_0, pat_12, pat_17, pat_28, pat_29, pat_30, pat_34, pat_43,
      pat_50, pat_54, pat_63, pat_68, pat_71, pat_72, pat_73, pat_78, pat_79,
      evalTapePattern, evalTapeExpr]
    simp only [list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append,
      List.nil_append, ListBlank.append_nil, ListBlank.append_cons,
      ListBlank.head_cons, ListBlank.tail_cons]
    bb_steps))

private theorem reach_17 (v : ℕ) : ∀ w c,
    ReachesPlus target (evalTapePattern pat_17 (v3 v w c))
      (evalTapePattern pat_12 (v2 (v + w + 1) c)) := by
  induction v with
  | zero =>
    intro w c
    rw [Nat.zero_add]
    pat_steps
  | succ v ih =>
    intro w c
    have h1 : ReachesPlus target (evalTapePattern pat_17 (v3 (v + 1) w c))
        (evalTapePattern pat_17 (v3 v (w + 1) c)) := by pat_steps
    have h_eq : v + 1 + w + 1 = v + (w + 1) + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) c)

private theorem reach_29 (u : ℕ) : ∀ w c,
    ReachesPlus target (evalTapePattern pat_29 (v3 w u c))
      (evalTapePattern pat_34 (v2 (w + u) c)) := by
  induction u with
  | zero =>
    intro w c
    rw [Nat.add_zero]
    pat_steps
  | succ u ih =>
    intro w c
    have h1 : ReachesPlus target (evalTapePattern pat_29 (v3 w (u + 1) c))
        (evalTapePattern pat_29 (v3 (w + 1) u c)) := by pat_steps
    have h_eq : w + (u + 1) = w + 1 + u := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) c)

private theorem reach_50 (v : ℕ) : ∀ w u,
    ReachesPlus target (evalTapePattern pat_50 (v3 v w u))
      (evalTapePattern pat_54 (v2 (v + w) u)) := by
  induction v with
  | zero =>
    intro w u
    rw [Nat.zero_add]
    pat_steps
  | succ v ih =>
    intro w u
    have h1 : ReachesPlus target (evalTapePattern pat_50 (v3 (v + 1) w u))
        (evalTapePattern pat_50 (v3 v (w + 1) u)) := by pat_steps
    have h_eq : v + 1 + w = v + (w + 1) := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) u)

private theorem reach_71 (u : ℕ) : ∀ w c,
    ReachesPlus target (evalTapePattern pat_71 (v3 w u c))
      (evalTapePattern pat_63 (v2 (w + u + 1) c)) := by
  induction u with
  | zero =>
    intro w c
    rw [Nat.add_zero]
    pat_steps
  | succ u ih =>
    intro w c
    have h1 : ReachesPlus target (evalTapePattern pat_71 (v3 w (u + 1) c))
        (evalTapePattern pat_71 (v3 (w + 1) u c)) := by pat_steps
    have h_eq : w + (u + 1) + 1 = w + 1 + u + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) c)

private theorem reach_73 (v : ℕ) : ∀ b w c,
    ReachesPlus target (evalTapePattern pat_73 (v4 v b w c))
      (evalTapePattern pat_68 (v3 b (v + w + 1) c)) := by
  induction v with
  | zero =>
    intro b w c
    rw [Nat.zero_add]
    pat_steps
  | succ v ih =>
    intro b w c
    have h1 : ReachesPlus target (evalTapePattern pat_73 (v4 (v + 1) b w c))
        (evalTapePattern pat_73 (v4 v b (w + 1) c)) := by pat_steps
    have h_eq : v + 1 + w + 1 = v + (w + 1) + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih b (w + 1) c)

private theorem reach_78 (u : ℕ) : ∀ w c,
    ReachesPlus target (evalTapePattern pat_78 (v3 w u c))
      (evalTapePattern pat_0 (v2 (w + u + 1) c)) := by
  induction u with
  | zero =>
    intro w c
    rw [Nat.add_zero]
    pat_steps
  | succ u ih =>
    intro w c
    have h1 : ReachesPlus target (evalTapePattern pat_78 (v3 w (u + 1) c))
        (evalTapePattern pat_78 (v3 (w + 1) u c)) := by pat_steps
    have h_eq : w + (u + 1) + 1 = w + 1 + u + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) c)

private theorem reach_79 (u : ℕ) : ∀ w b c,
    ReachesPlus target (evalTapePattern pat_79 (v4 w b u c))
      (evalTapePattern pat_43 (v3 (w + u + 1) b c)) := by
  induction u with
  | zero =>
    intro w b c
    rw [Nat.add_zero]
    pat_steps
  | succ u ih =>
    intro w b c
    have h1 : ReachesPlus target (evalTapePattern pat_79 (v4 w b (u + 1) c))
        (evalTapePattern pat_79 (v4 (w + 1) b u c)) := by pat_steps
    have h_eq : w + (u + 1) + 1 = w + 1 + u + 1 := by omega
    rw [h_eq]
    exact h1.trans (ih (w + 1) b c)

private theorem reach_E_zero_pos (a c : ℕ) :
    ReachesPlus target (encode (.E a 0 (c + 1))) (evalTapePattern pat_28 (v2 (a + 1) c)) := by
  have h1 : ReachesPlus target (encode (.E a 0 (c + 1))) (evalTapePattern pat_12 (v2 a c)) := by
    rcases a with _ | v
    · pat_steps
    · have ha : ReachesPlus target (encode (.E (v + 1) 0 (c + 1)))
          (evalTapePattern pat_17 (v3 v 0 c)) := by pat_steps
      have hb := reach_17 v 0 c
      rw [Nat.add_zero] at hb
      exact ha.trans hb
  have h2 : ReachesPlus target (evalTapePattern pat_12 (v2 a c))
      (evalTapePattern pat_29 (v3 0 a c)) := by pat_steps
  have h3 := reach_29 a 0 c
  rw [Nat.zero_add] at h3
  have h4 : ReachesPlus target (evalTapePattern pat_34 (v2 a c))
      (evalTapePattern pat_28 (v2 (a + 1) c)) := by pat_steps
  exact ((h1.trans h2).trans h3).trans h4

private theorem reach_E_zero_ge3 (a u : ℕ) :
    ReachesPlus target (encode (.E a 0 (u + 3))) (evalTapePattern pat_63 (v2 (a + 2) u)) := by
  have h1 := reach_E_zero_pos a (u + 2)
  have h2 : ReachesPlus target (evalTapePattern pat_28 (v2 (a + 1) (u + 2)))
      (evalTapePattern pat_50 (v3 (a + 1) 0 u)) := by pat_steps
  have h3 := reach_50 (a + 1) 0 u
  rw [Nat.add_zero] at h3
  have h4 : ReachesPlus target (evalTapePattern pat_54 (v2 (a + 1) u))
      (evalTapePattern pat_71 (v3 0 (a + 1) u)) := by pat_steps
  have h5 := reach_71 (a + 1) 0 u
  rw [Nat.zero_add] at h5
  exact (((h1.trans h2).trans h3).trans h4).trans h5

private theorem reach_E_succ_pos (a b c : ℕ) :
    ReachesPlus target (encode (.E a (b + 1) (c + 1)))
      (evalTapePattern pat_72 (v3 b a c)) := by
  rcases a with _ | v
  · pat_steps
  · have h1 : ReachesPlus target (encode (.E (v + 1) (b + 1) (c + 1)))
        (evalTapePattern pat_73 (v4 v b 0 c)) := by pat_steps
    have h2 := reach_73 v b 0 c
    rw [Nat.add_zero] at h2
    have h3 : ReachesPlus target (evalTapePattern pat_68 (v3 b (v + 1) c))
        (evalTapePattern pat_72 (v3 b (v + 1) c)) := by pat_steps
    exact (h1.trans h2).trans h3

private theorem reach_E_one_pos (a c : ℕ) :
    ReachesPlus target (encode (.E a 1 (c + 1)))
      (evalTapePattern pat_0 (v2 (a + 1) c)) := by
  have h1 := reach_E_succ_pos a 0 c
  have h2 : ReachesPlus target (evalTapePattern pat_72 (v3 0 a c))
      (evalTapePattern pat_78 (v3 0 a c)) := by pat_steps
  have h3 := reach_78 a 0 c
  rw [Nat.zero_add] at h3
  exact (h1.trans h2).trans h3

private theorem reach_E_ge2_pos (a b c : ℕ) :
    ReachesPlus target (encode (.E a (b + 2) (c + 1)))
      (evalTapePattern pat_43 (v3 (a + 1) b c)) := by
  have h1 := reach_E_succ_pos a (b + 1) c
  have h2 : ReachesPlus target (evalTapePattern pat_72 (v3 (b + 1) a c))
      (evalTapePattern pat_79 (v4 0 b a c)) := by pat_steps
  have h3 := reach_79 a 0 b c
  rw [Nat.zero_add] at h3
  exact (h1.trans h2).trans h3

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_pat_D
  step_some := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩) s' hnext
    · rcases a with _ | a
      · rcases b with _ | _ | b
        · rcases c with _ | c
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
        · rcases c with _ | _ | _ | c
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
        · rcases b with _ | b
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        pat_steps
    · rcases c with _ | c
      · rcases a with _ | a
        · rcases b with _ | _ | b
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            pat_steps
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          pat_steps
      · rcases b with _ | _ | b
        · rcases c with _ | _ | _ | _ | _ | _ | c
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_pos a 0).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_pos a 1).trans ?_
            pat_steps
          · simp [next] at hnext
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_ge3 a 1).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_ge3 a 2).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_ge3 a 3).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_zero_ge3 a (c + 4)).trans ?_
            pat_steps
        · rcases c with _ | _ | c
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_one_pos a 0).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_one_pos a 1).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_one_pos a (c + 2)).trans ?_
            pat_steps
        · rcases c with _ | _ | c
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_ge2_pos a b 0).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_ge2_pos a b 1).trans ?_
            pat_steps
          · simp only [next, Option.some.injEq] at hnext
            subst hnext
            refine (reach_E_ge2_pos a b (c + 2)).trans ?_
            pat_steps
  step_none := by
    rintro (⟨a, b, c⟩ | ⟨a, b, c⟩) hnext
    · rcases a with _ | a <;> rcases b with _ | _ | b <;> rcases c with _ | _ | _ | c <;>
        simp [next] at hnext
    · rcases c with _ | c
      · rcases a with _ | a <;> rcases b with _ | b <;> simp [next] at hnext
      · rcases b with _ | b
        · rcases c with _ | _ | _ | _ | _ | _ | c
          · simp [next] at hnext
          · simp [next] at hnext
          · have h1 := reach_E_zero_ge3 a 0
            have h2 :
                ReachesPlus target (evalTapePattern pat_63 (v2 (a + 2) 0))
                  (Cfg.headRight F
                    (ListBlank.append [1, 0, 1]
                      (ListBlank.append (([0, 1] : List (Fin 2)) ^ (a + 3)) default))
                    default) := by pat_steps
            exact ⟨_, (h1.trans h2).to_star, by bb_halt⟩
          · simp [next] at hnext
          · simp [next] at hnext
          · simp [next] at hnext
          · simp [next] at hnext
        · rcases c with _ | _ | c <;> simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

private inductive MidState where
  | E (a b c : ℕ)

private def midStart : MidState := .E 1 0 2

private def midToState : MidState → State
  | .E a b c => .E a b c

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midNext : MidState → Option MidState
  | .E (a + 1) b 0 => some (.E a b 1)
  | .E 0 0 0 => some (.E 1 0 1)
  | .E 0 1 0 => some (.E 1 0 2)
  | .E 0 2 0 => some (.E 1 0 6)
  | .E 0 (b + 3) 0 => some (.E 1 b 4)
  | .E a 0 1 => some (.E 1 0 (2 * a + 3))
  | .E a 0 2 => some (.E 1 0 (2 * a + 5))
  | .E _ 0 3 => none
  | .E a 0 4 => some (.E 1 (a + 1) 2)
  | .E a 0 5 => some (.E 1 (a + 1) 4)
  | .E a 0 6 => some (.E 1 (a + 1) 6)
  | .E a 0 (c + 7) => some (.E 1 (a + 3) (c + 1))
  | .E a 1 1 => some (.E 1 0 (2 * a + 4))
  | .E a 1 2 => some (.E 1 0 (2 * a + 6))
  | .E a 2 1 => some (.E 1 2 (2 * a + 2))
  | .E a 2 2 => some (.E 1 2 (2 * a + 4))
  | .E a (b + 3) 1 => some (.E 1 b (2 * a + 6))
  | .E a (b + 3) 2 => some (.E 1 b (2 * a + 8))
  | .E a (b + 1) (c + 3) =>
    let k := min (b + 1) ((c + 2) / 2)
    some (.E (a + 2 * k) (b + 1 - k) (c + 3 - 2 * k))

private theorem reaches_E_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.E a (b + k) (c + 1 + 2 * k)) (.E (a + 2 * k) b (c + 1)) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.E a (b + (k + 1)) (c + 1 + 2 * (k + 1))) =
        some (.E (a + 2) (b + k) (c + 1 + 2 * k)) := by
      have h1 : b + (k + 1) = (b + k) + 1 := by omega
      have h2 : c + 1 + 2 * (k + 1) = (c + 2 * k) + 3 := by omega
      rw [h1, h2]
      simp only [next]
      have : c + 2 * k + 1 = c + 1 + 2 * k := by omega
      rw [this]
    have ih' := ih (a + 2)
    have h_a : a + 2 + 2 * k = a + 2 * (k + 1) := by omega
    rw [h_a] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_E_drain (a b c : ℕ) :
    CollatzStepsTo next (.E a (b + 1) (c + 1 + 1 + 1))
      (some (.E (a + 2 * min (b + 1) ((c + 2) / 2))
        (b + 1 - min (b + 1) ((c + 2) / 2))
        (c + 3 - 2 * min (b + 1) ((c + 2) / 2)))) := by
  let k := min (b + 1) ((c + 2) / 2)
  have hk_pos : 0 < k := by
    dsimp [k]
    have : 0 < b + 1 := Nat.succ_pos b
    have : 0 < (c + 2) / 2 := by omega
    exact Nat.lt_min.mpr ⟨‹_›, ‹_›⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
  have h_head : next (.E a (b + 1) (c + 1 + 1 + 1)) = some (.E (a + 2) b (c + 1)) := by
    have : c + 1 + 1 + 1 = c + 3 := by omega
    rw [this]
    simp [next]
  have h_star := reaches_E_diag m (a + 2) (b + 1 - k) (c + 3 - 2 * k - 1)
  have hb : b + 1 - k + m = b := by omega
  have hc : c + 3 - 2 * k - 1 + 1 + 2 * m = c + 1 := by omega
  have ha : a + 2 + 2 * m = a + 2 * k := by omega
  have hc' : c + 3 - 2 * k - 1 + 1 = c + 3 - 2 * k := by omega
  rw [hb, hc, ha, hc'] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem reaches_D_zero : ∀ (a b c : ℕ),
    CollatzReachesStar next (.D a b c) (.D 0 b (c + 2 * a))
  | 0, b, c => by
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | a + 1, b, c => by
    have ih := reaches_D_zero a b (c + 2)
    have h_eq : c + 2 + 2 * a = c + 2 * (a + 1) := by omega
    rw [h_eq] at ih
    exact CollatzReachesStar.head rfl ih

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  have h_init : CollatzReachesStar next start (midToState midStart) :=
    CollatzReachesStar.head rfl (CollatzReachesStar.head rfl (CollatzReachesStar.refl next _))
  refine is_valid_acceleration.of_collatz (embed := midToState) h_init ?_
  rintro ⟨a, b, c⟩
  rcases c with _ | _ | _ | c
  · rcases a with _ | a
    · rcases b with _ | _ | _ | b
      · exact CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)
      · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
      · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl
          (CollatzStepsTo.head rfl (CollatzStepsTo.head rfl
            (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl)))))
      · exact CollatzStepsTo.head rfl (CollatzStepsTo.head rfl (CollatzStepsTo.of_eq rfl))
    · exact CollatzStepsTo.of_eq rfl
  · rcases b with _ | _ | _ | b
    · have h0 : next (.E a 0 1) = some (.D (a + 1) 0 1) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 1) 0 1
      have hc : 1 + 2 * (a + 1) = (2 * a + 2) + 1 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a 1 1) = some (.D (a + 2) 0 0) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 2) 0 0
      have hc : 0 + 2 * (a + 2) = (2 * a + 3) + 1 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a 2 1) = some (.D (a + 2) 1 0) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 2) 1 0
      have hc : 0 + 2 * (a + 2) = (2 * a + 1) + 3 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a (b + 3) 1) = some (.D (a + 2) (b + 2) 0) := by
        rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 2) (b + 2) 0
      have hc : 0 + 2 * (a + 2) = 2 * a + 4 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rcases b with _ | b <;> rfl)))
  · rcases b with _ | _ | _ | b
    · have h0 : next (.E a 0 2) = some (.D (a + 2) 0 1) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 2) 0 1
      have hc : 1 + 2 * (a + 2) = (2 * a + 4) + 1 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a 1 2) = some (.D (a + 3) 0 0) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 3) 0 0
      have hc : 0 + 2 * (a + 3) = (2 * a + 5) + 1 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a 2 2) = some (.D (a + 3) 1 0) := by rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 3) 1 0
      have hc : 0 + 2 * (a + 3) = (2 * a + 3) + 3 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rfl)))
    · have h0 : next (.E a (b + 3) 2) = some (.D (a + 3) (b + 2) 0) := by
        rcases a with _ | a <;> rfl
      have h1 := reaches_D_zero (a + 3) (b + 2) 0
      have hc : 0 + 2 * (a + 3) = 2 * a + 6 := by omega
      rw [hc] at h1
      exact CollatzStepsTo.head h0 (CollatzStepsTo.of_reachesStar h1
        (CollatzStepsTo.of_eq (by rcases a with _ | a <;> rcases b with _ | b <;> rfl)))
  · rcases b with _ | b
    · rcases c with _ | _ | _ | _ | c
      · exact CollatzStepsTo.of_eq (by simp [next, midToState, midNext])
      · have h0 : next (.E a 0 4) = some (.D 0 (a + 3) 0) := by simp [next]
        exact CollatzStepsTo.head h0
          (CollatzStepsTo.of_eq (by simp [next, midToState, midNext]))
      · have h0 : next (.E a 0 5) = some (.D 1 (a + 3) 0) := by simp [next]
        have h1 : next (.D 1 (a + 3) 0) = some (.D 0 (a + 3) 2) := rfl
        exact CollatzStepsTo.head h0
          (CollatzStepsTo.head h1
            (CollatzStepsTo.of_eq (by simp [next, midToState, midNext])))
      · have h0 : next (.E a 0 6) = some (.D 2 (a + 3) 0) := by simp [next]
        have h1 : next (.D 2 (a + 3) 0) = some (.D 1 (a + 3) 2) := rfl
        have h2 : next (.D 1 (a + 3) 2) = some (.D 0 (a + 3) 4) := rfl
        exact CollatzStepsTo.head h0
          (CollatzStepsTo.head h1
            (CollatzStepsTo.head h2
              (CollatzStepsTo.of_eq (by simp [next, midToState, midNext]))))
      · exact CollatzStepsTo.of_eq (by simp [next, midToState, midNext])
    · have h_eq : midNext (.E a (b + 1) (c + 1 + 1 + 1)) =
          some (.E (a + 2 * min (b + 1) ((c + 2) / 2))
            (b + 1 - min (b + 1) ((c + 2) / 2))
            (c + 3 - 2 * min (b + 1) ((c + 2) / 2))) := by
        simp [midNext]
      rw [h_eq]
      exact reaches_E_drain a b c

/-- Single-family high-level symbolic configuration state space for
`1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_---0RE`. -/
inductive HighLevelState where
  /-- $E(b, d) := 0^\infty\,(10)^b\,1111\,\mathrm{E}{>}\,1^{d+2}\,0^\infty$. -/
  | E (b d : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $E(0, 1)$. -/
def highLevelStart : HighLevelState := .E 0 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .E b d => .E 1 b (d + 1)

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

private def toMid : HighLevelState → MidState
  | .E b d => .E 1 b (d + 1)

/-- High-level accelerated transition function on $E(b, d)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .E b d =>
    let c := d + 1
    let m := d / 2
    if b > m then
      if b = m + 1 then some (.E 0 (2 * c + 3))
      else if b = m + 2 then some (.E 2 (2 * c + 1))
      else some (.E (b - m - 3) (2 * c + 5))
    else
      let rem := c - 2 * b
      if rem ≤ 2 then some (.E 0 (2 * c + 2))
      else if rem = 3 then none
      else if rem ≤ 6 then some (.E (2 * b + 2) (2 * rem - 7))
      else some (.E (2 * b + 4) (rem - 7))

private theorem midNext_b_gt (a b c : ℕ) (h12 : c = 1 ∨ c = 2) :
    midNext (.E a (b + 1) c) =
      if b = 0 then some (.E 1 0 (2 * a + 2 * c + 2))
      else if b = 1 then some (.E 1 2 (2 * a + 2 * c))
      else some (.E 1 (b - 2) (2 * a + 2 * c + 4)) := by
  rcases h12 with rfl | rfl <;> rcases b with _ | _ | b <;> simp [midNext]

private theorem midNext_b_zero (a rem : ℕ) (hrem : 1 ≤ rem) :
    midNext (.E a 0 rem) =
      if rem ≤ 2 then some (.E 1 0 (2 * a + 2 * rem + 1))
      else if rem = 3 then none
      else if rem ≤ 6 then some (.E 1 (a + 1) (2 * rem - 6))
      else some (.E 1 (a + 3) (rem - 6)) := by
  rcases rem with _ | _ | _ | _ | _ | _ | _ | rem
  · omega
  all_goals simp [midNext]

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_mid_acceleration.of_collatz (embed := toMid)
    (CollatzReachesStar.refl midNext _) ?_
  rintro ⟨b, d⟩
  rcases b with _ | b
  · refine CollatzStepsTo.of_eq ?_
    rw [show toMid (.E 0 d) = .E 1 0 (d + 1) from rfl, midNext_b_zero 1 (d + 1) (by omega)]
    dsimp only [highLevelNext]
    split_ifs <;>
      (try simp only [Option.map_some, Option.map_none, toMid, Option.some.injEq,
        MidState.E.injEq, true_and]) <;> omega
  · rcases d with _ | _ | d
    · refine CollatzStepsTo.of_eq ?_
      rw [show toMid (.E (b + 1) 0) = .E 1 (b + 1) 1 from rfl,
        midNext_b_gt 1 b 1 (Or.inl rfl)]
      dsimp only [highLevelNext]
      split_ifs <;>
        (try simp only [Option.map_some, Option.map_none, toMid, Option.some.injEq,
          MidState.E.injEq, true_and, and_true]) <;> omega
    · refine CollatzStepsTo.of_eq ?_
      rw [show toMid (.E (b + 1) 1) = .E 1 (b + 1) 2 from rfl,
        midNext_b_gt 1 b 2 (Or.inr rfl)]
      dsimp only [highLevelNext]
      split_ifs <;>
        (try simp only [Option.map_some, Option.map_none, toMid, Option.some.injEq,
          MidState.E.injEq, true_and, and_true]) <;> omega
    · by_cases hgt : b + 1 > (d + 2) / 2
      · have hk : min (b + 1) ((d + 2) / 2) = (d + 2) / 2 := by omega
        obtain ⟨t, ht⟩ : ∃ t, b + 1 - (d + 2) / 2 = t + 1 := ⟨b - (d + 2) / 2, by omega⟩
        have h_step1 : midNext (.E 1 (b + 1) (d + 3)) =
            some (.E (1 + 2 * ((d + 2) / 2)) (t + 1) (d + 3 - 2 * ((d + 2) / 2))) := by
          simp only [midNext, hk, ht]
        refine CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq ?_)
        rw [midNext_b_gt _ t _ (by omega)]
        dsimp only [highLevelNext]
        split_ifs <;>
          (try simp only [Option.map_some, toMid, Option.some.injEq,
            MidState.E.injEq, true_and]) <;> omega
      · have hk : min (b + 1) ((d + 2) / 2) = b + 1 := by omega
        have h_step1 : midNext (.E 1 (b + 1) (d + 3)) =
            some (.E (1 + 2 * (b + 1)) 0 (d + 3 - 2 * (b + 1))) := by
          simp only [midNext, hk, Nat.sub_self]
        refine CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq ?_)
        rw [midNext_b_zero _ _ (by omega)]
        dsimp only [highLevelNext]
        split_ifs <;>
          (try simp only [Option.map_some, Option.map_none, toMid, Option.some.injEq,
            MidState.E.injEq, true_and]) <;> omega

/-- `target` halts from the blank tape if and only if the high-level acceleration `highLevelNext`
halts from `highLevelStart`. -/
theorem isHalt_iff_highLevel_acceleration :
    IsHalt target ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_highLevel_acceleration.isHalt_iff

/-- The initial acceleration `next` halts from `start` if and only if the high-level acceleration
`highLevelNext` halts from `highLevelStart`. -/
theorem acceleration_iff_highLevel_acceleration :
    CollatzHalts next start ↔ CollatzHalts highLevelNext highLevelStart :=
  is_valid_acceleration.collatzHalts_iff is_valid_highLevel_acceleration

end BusyBeaver.M_1RB1LE_1RC1RA_0LD1RB_1LE1LD_1RF0LA_HHH0RE
