/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Busy Beaver Holdout `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`

Formal `IsClosedPatternSet`, `HasCollatzReduction`, and `IsValidAcceleration` proofs for the
6-state, 2-symbol Busy Beaver holdout `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`
(bbchallenge holdout #754, `suspect_41`, redirects to BMO5;
see <https://wiki.bbchallenge.org/wiki/1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE>).

Starting from the blank tape (`init []`), the trajectory reaches the canonical configuration family
$$B_2(a, b, c) := 0^\infty\,(10)^b\,11\,(10)^{a+1}\,\mathrm{B}{>}\,1^{c+1}\,0^\infty$$
at $B_2(0, 1, 2)$ in 30 steps, and every configuration in $\{B_2(a, b, c)\}$ steps in
`ReachesPlus` either to another configuration in the family or to a halting configuration.

## Collatz-like Acceleration Rules

```text
Consider:
B2(a, b, c) = 0^inf (10)^b 11 (10)^{a+1} B> 1^{c+1} 0^inf

B2(0, b, 0)         -> B2(0, 1, 2b + 10)
B2(a + 1, b, 0)     -> B2(a, b, 1)
B2(a, b, 1)         -> B2(0, 1, 4a + 2b + 14)
B2(a, 0, 2)         -> Halt
B2(a, 0, 3)         -> Halt
B2(a, 0, 4)         -> B2(0, 1, 2a + 12)
B2(a, 0, 5)         -> B2(0, 1, 2a + 16)
B2(a, 0, c + 6)     -> B2(0, a + 4, c)
B2(a, b + 1, c + 2) -> B2(a + 2, b, c)

Start: B2(0, 1, 2), reached after 30 raw TM steps
```
-/

@[expose] public section

namespace BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE

open SixState Turing

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private theorem target_A_0 : target A 0 = some (some B, Stmt.write 1 Dir.right) := rfl
private theorem target_A_1 : target A 1 = some (some C, Stmt.write 1 Dir.left) := rfl
private theorem target_B_0 : target B 0 = some (some C, Stmt.write 1 Dir.right) := rfl
private theorem target_B_1 : target B 1 = some (some D, Stmt.write 0 Dir.left) := rfl
private theorem target_C_0 : target C 0 = some (some A, Stmt.write 1 Dir.left) := rfl
private theorem target_C_1 : target C 1 = some (some B, Stmt.write 0 Dir.right) := rfl
private theorem target_D_0 : target D 0 = some (some B, Stmt.write 1 Dir.left) := rfl
private theorem target_D_1 : target D 1 = some (some E, Stmt.write 1 Dir.left) := rfl
private theorem target_E_0 : target E 0 = some (some F, Stmt.write 1 Dir.right) := rfl
private theorem target_E_1 : target E 1 = some (some A, Stmt.write 0 Dir.left) := rfl
private theorem target_F_0 : target F 0 = none := rfl
private theorem target_F_1 : target F 1 = some (some E, Stmt.write 0 Dir.right) := rfl

local macro "v1" a:term:arg : term =>
  `(fun k => match k with | 0 => $a | _ => 0)

local macro "v2" a:term:arg b:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | _ => 0)

local macro "v3" a:term:arg b:term:arg c:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | 2 => $c | _ => 0)

local macro "v4" a:term:arg b:term:arg c:term:arg d:term:arg : term =>
  `(fun k => match k with | 0 => $a | 1 => $b | 2 => $c | 3 => $d | _ => 0)

local macro "pat_step" : tactic =>
  `(tactic| (
    simp only [step, Cfg.headRight, Cfg.headLeft,
      target_A_0, target_A_1, target_B_0, target_B_1,
      target_C_0, target_C_1, target_D_0, target_D_1,
      target_E_0, target_E_1, target_F_0, target_F_1,
      list_pow_zero, list_pow_succ, List.cons_append, List.singleton_append, List.nil_append,
      Tape.write, Tape.move, ListBlank.append_nil, ListBlank.append_cons,
      ListBlank.head_cons, ListBlank.tail_cons,
      ListBlank.cons_zero_default,
      ListBlank.head_default_fin, ListBlank.tail_default, Option.map]
    try rfl))

local macro "congr_vars" : tactic =>
  `(tactic| (
    first
    | (refine congrArg (fun x => some (evalTapePattern _ x)) (funext fun k => ?_);
       rcases k with _ | _ | _ | _ | k <;> (first | rfl | (simp -failIfUnchanged only []; omega)))
    | (refine congrArg _ (funext fun k => ?_);
       rcases k with _ | _ | _ | _ | k <;> (first | rfl | (simp -failIfUnchanged only []; omega)))))

private def pat_0 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .default }

private def pat_2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some C
    right := .default }

private def pat_4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .default }

private def pat_5 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .default }

private def pat_6 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_7 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_8 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_9 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_10 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_11 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_12 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_13 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_14 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .default }

private def pat_15 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_16 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_17 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_18 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_19 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_20 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_21 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_22 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1
      .default))))))) }

private def pat_23 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2
      .default))))))) }

private def pat_24 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_25 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_26 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_27 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_28 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_29 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_30 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_31 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_32 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_33 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_34 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_35 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_36 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_37 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_38 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_39 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_40 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some F
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_41 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .default }

private def pat_42 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_43 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_44 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_45 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .default }

private def pat_46 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .default }

private def pat_47 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .default }

private def pat_48 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_49 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_50 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_51 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_52 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some F
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_53 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .default }

private def pat_54 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .default }

private def pat_55 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_56 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_57 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some C
    right := .default }

private def pat_58 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some C
    right := .default }

private def pat_59 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some C
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_60 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_61 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some A
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_62 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_63 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .default }

private def pat_64 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_65 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .default }

private def pat_66 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_67 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some C
    right := .default }

private def pat_68 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some D
    right := .default }

private def pat_69 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some D
    right := .default }

private def pat_70 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_71 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_72 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some C
    right := .default }

private def pat_73 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some D
    right := .default }

private def pat_74 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some D
    right := .default }

private def pat_75 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_76 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 2 .default))) }

private def pat_77 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_78 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_79 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_80 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_81 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some A
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_82 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_83 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_84 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))) }

private def pat_85 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_86 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_87 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_88 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_89 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_90 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_91 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_92 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_93 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_94 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_95 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_96 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_97 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_98 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 2 (.sym 0 (.sym 1 (.rep [1] 3 .default)))))) }

private def pat_99 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_100 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_101 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1
      .default))))))) }

private def pat_102 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1
      .default))))))) }

private def pat_103 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2
      .default))))))) }

private def pat_104 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_105 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 .default))
    head := some E
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2
      .default))))))) }

private def pat_106 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2
      .default))))))) }

private def pat_107 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 2 (.sym 0 (.sym 1 (.rep [1] 3
      .default))))))) }

private def pat_108 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .default }

private def pat_109 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_110 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_111 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_112 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))
    head := some A
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_113 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .default }

private def pat_114 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_115 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_116 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))))) }

private def pat_117 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_118 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some C
    right := .default }

private def pat_119 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some C
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_120 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_121 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_122 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_123 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 .default))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_124 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_125 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 .default)))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_126 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some A
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_127 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .default }

private def pat_128 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_129 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_130 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_131 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_132 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))))) }

private def pat_133 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [1] 2 .default)) }

private def pat_134 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default)))))))
    head := some B
    right := .sym 0 (.sym 1 (.rep [0, 1] 2 (.sym 0 (.sym 1 (.rep [1] 3 .default))))) }

private def pat_135 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some C
    right := .sym 1 (.rep [1] 0 .default) }

private def pat_136 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some C
    right := .default }

private def pat_137 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some D
    right := .default }

private def pat_138 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some D
    right := .default }

private def pat_139 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 0 .default))) }

private def pat_140 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_141 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_142 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_143 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_144 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some C
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_145 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default))) }

private def pat_146 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 .default)))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_147 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some C
    right := .sym 1 (.rep [1] 2 .default) }

private def pat_148 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [1] 2 .default))) }

private def pat_149 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1
    .default))))))))
    head := some C
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 2 (.sym 0 (.sym 1 (.rep [1] 3 .default)))))) }

private def pat_150 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some B
    right := .default }

private def pat_151 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some A
    right := .sym 1 (.rep [1] 1 .default) }

private def pat_152 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 0 .default)))) }

private def pat_153 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [1] 1 .default)))) }

private def pat_154 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some C
    right := .default }

private def pat_155 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 0 .default)) }

private def pat_156 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some C
    right := .sym 0 (.sym 1 (.rep [1] 1 .default)) }

private def pat_157 : TapePattern (Fin 2) (Fin 6) :=
  { left := .default
    head := some D
    right := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_158 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 1 .default)
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1 .default)))))) }

private def pat_159 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default))))
    head := some D
    right := .sym 0 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2 .default)))))) }

private def pat_160 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 .default
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 0 (.sym 1 (.rep [1] 1
      .default))))))) }

private def pat_161 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 .default)))
    head := some B
    right := .sym 1 (.sym 1 (.sym 0 (.sym 1 (.rep [0, 1] 1 (.sym 0 (.sym 1 (.rep [1] 2
      .default))))))) }

/-- Canonical tape pattern
$B_2(a, b, c) := 0^\infty\,(10)^b\,11\,(10)^{a+1}\,\mathrm{B}{>}\,1^{c+1}\,0^\infty$. -/
def pat_B2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 0 (.sym 1 (.rep [0, 1] 0 (.sym 1 (.sym 1 (.rep [0, 1] 1 .default)))))
    head := some B
    right := .sym 1 (.rep [1] 2 .default) }

/-- Closed `TapePatternSet` for `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE` (Level A). -/
def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_B2, .true)]

private theorem mem_ps_B2 : (pat_B2, VarCond.true) ∈ ps := .head _

private theorem in_ps_B2 (vars : ℕ → ℕ) : IsInPatternSet ps (evalTapePattern pat_B2 vars) :=
  ⟨(pat_B2, .true), mem_ps_B2, vars, rfl, trivial⟩

private theorem pat_64_eq_B2 (vars : ℕ → ℕ) :
    evalTapePattern pat_64 vars =
      evalTapePattern pat_B2 (v3 (vars 0) 0 (vars 1)) := by
  simp only [evalTapePattern_some, pat_64, pat_B2, evalTapeExpr,
    list_pow_zero, ListBlank.append_nil]

private theorem pat_66_eq_B2 (vars : ℕ → ℕ) :
    evalTapePattern pat_66 vars =
      evalTapePattern pat_B2 (v3 (vars 0) (vars 1 + 1) (vars 2)) := by
  simp only [evalTapePattern_some, pat_66, pat_B2, evalTapeExpr,
    list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]

private def ReachesTarget (c₁ : Cfg (Fin 2) (Fin 6)) (t : Option (Cfg (Fin 2) (Fin 6))) : Prop :=
  match t with
  | some cfg' => ReachesPlus target c₁ cfg' ∧ IsInPatternSet ps cfg'
  | none => ∃ cfg_h, ReachesPlus target c₁ cfg_h ∧ (step target cfg_h).isNone

private theorem reachesTarget_to_exists {c₁ : Cfg (Fin 2) (Fin 6)}
    {t : Option (Cfg (Fin 2) (Fin 6))} (h : ReachesTarget c₁ t) :
    ∃ cfg', ReachesPlus target c₁ cfg' ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  cases t with
  | some cfg' => exact ⟨cfg', h.1, Or.inl h.2⟩
  | none =>
    rcases h with ⟨cfg_h, h₁, h₂⟩
    exact ⟨cfg_h, h₁, Or.inr h₂⟩

private theorem step_base_64 {c₁ : Cfg (Fin 2) (Fin 6)} (vars : ℕ → ℕ)
    (h_step : step target c₁ = some (evalTapePattern pat_64 vars)) :
    ReachesTarget c₁
      (some (evalTapePattern pat_B2 (v3 (vars 0) 0 (vars 1)))) := by
  rw [pat_64_eq_B2] at h_step
  exact ⟨⟨1, Nat.zero_lt_one, h_step⟩, in_ps_B2 _⟩

private theorem step_base_66 {c₁ : Cfg (Fin 2) (Fin 6)} (vars : ℕ → ℕ)
    (h_step : step target c₁ = some (evalTapePattern pat_66 vars)) :
    ReachesTarget c₁
      (some (evalTapePattern pat_B2 (v3 (vars 0) (vars 1 + 1) (vars 2)))) := by
  rw [pat_66_eq_B2] at h_step
  exact ⟨⟨1, Nat.zero_lt_one, h_step⟩, in_ps_B2 _⟩

private theorem step_halt {c₁ c₂ : Cfg (Fin 2) (Fin 6)}
    (h_step : step target c₁ = some c₂)
    (h_halt : (step target c₂).isNone) :
    ReachesTarget c₁ none :=
  ⟨c₂, ⟨1, Nat.zero_lt_one, h_step⟩, h_halt⟩

private theorem step_chain {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {t : Option (Cfg (Fin 2) (Fin 6))}
    (h_step : step target c₁ = some c₂)
    (h_next : ReachesTarget c₂ t) :
    ReachesTarget c₁ t := by
  cases t with
  | some cfg' =>
    exact ⟨ReachesPlus.trans ⟨1, Nat.zero_lt_one, h_step⟩ h_next.1, h_next.2⟩
  | none =>
    rcases h_next with ⟨cfg_h, h₂, h_halt⟩
    exact ⟨cfg_h, ReachesPlus.trans ⟨1, Nat.zero_lt_one, h_step⟩ h₂, h_halt⟩

private theorem cast_target {c₁ : Cfg (Fin 2) (Fin 6)} {t₁ t₂ : Option (Cfg (Fin 2) (Fin 6))}
    (h_eq : t₁ = t₂) (h : ReachesTarget c₁ t₂) : ReachesTarget c₁ t₁ :=
  h_eq ▸ h

private def ReachesPat0 (x y : ℕ) (c₁ : Cfg (Fin 2) (Fin 6)) : Prop :=
  ReachesPlus target c₁
    (evalTapePattern pat_0 (v2 x y))

private theorem cast_pat0 {c₁ : Cfg (Fin 2) (Fin 6)} {x₁ x₂ y₁ y₂ : ℕ}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h : ReachesPat0 x₂ y₂ c₁) : ReachesPat0 x₁ y₁ c₁ :=
  hx ▸ hy ▸ h

private theorem step_base_0 {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {x y : ℕ}
    (h_step : step target c₁ = some c₂)
    (h_eq : c₂ = evalTapePattern pat_0 (v2 x y)) :
    ReachesPat0 x y c₁ := by
  subst h_eq
  exact ⟨1, Nat.zero_lt_one, h_step⟩

private theorem step_chain_0 {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {x y : ℕ}
    (h_step : step target c₁ = some c₂)
    (h_next : ReachesPat0 x y c₂) :
    ReachesPat0 x y c₁ :=
  ReachesPlus.trans ⟨1, Nat.zero_lt_one, h_step⟩ h_next

private theorem reaches_pat_0_chain {c₁ : Cfg (Fin 2) (Fin 6)} {x y : ℕ}
    {t : Option (Cfg (Fin 2) (Fin 6))}
    (h₁ : ReachesPat0 x y c₁)
    (h₂ : ReachesTarget
      (evalTapePattern pat_0 (v2 x y)) t) :
    ReachesTarget c₁ t := by
  cases t with
  | none =>
    rcases h₂ with ⟨cfg_h, h_plus, h_halt⟩
    exact ⟨cfg_h, ReachesPlus.trans h₁ h_plus, h_halt⟩
  | some cfg' =>
    exact ⟨ReachesPlus.trans h₁ h₂.1, h₂.2⟩

private def target_pat_12_pos (u : ℕ) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_B2 (v3 0 1 u))

private theorem step_pat_12_pos (u : ℕ) (vars : ℕ → ℕ) (h_vr : vars 0 = u + 1) :
    ReachesTarget (evalTapePattern pat_12 vars) (target_pat_12_pos u) := by
  have h_plus : ReachesPlus target (evalTapePattern pat_12 vars)
      (evalTapePattern pat_66 (v3 0 0 u)) := by
    dsimp only [pat_12, pat_66, evalTapePattern, evalTapeExpr]
    rw [h_vr]
    simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]
    bb_steps
  rw [pat_66_eq_B2] at h_plus
  exact ⟨h_plus, in_ps_B2 _⟩

private def target_pat_8_pos (vars : ℕ → Nat) (u : ℕ) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_12_pos (2 * vars 0 + u)

private theorem step_pat_8_pos (vars : ℕ → Nat) :
  ∀ u : ℕ, vars 1 = u + 1 →
  ReachesTarget (evalTapePattern pat_8 vars) (target_pat_8_pos vars u) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    intro u h_vr
    refine cast_target ?_ (step_chain ?_ (step_pat_12_pos u (v1 (u + 1)) rfl))
    · dsimp only [target_pat_8_pos]; rw [h_vl, Nat.mul_zero, Nat.zero_add]
    · dsimp only [pat_8, pat_12, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  | succ v ih =>
    intro u h_vr
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_13 (v2 v (u + 1))) _ ?_
      (step_chain ?_ (ih (v2 v (((u + 1) + 1) + 1)) rfl ((u + 1) + 1) rfl)))
    · dsimp only [target_pat_8_pos, target_pat_12_pos]; rw [h_vl]; congr_vars
    · dsimp only [pat_8, pat_13, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · dsimp only [pat_13, pat_8, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_3 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_8_pos (v2 (vars 0) 1) 0

private theorem step_pat_3 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_3 vars) (target_pat_3 vars) := by
  refine step_chain ?_ (step_pat_8_pos (v2 (vars 0) 1) 0
    rfl)
  dsimp only [pat_3, pat_8, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_1 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_3 (v1 (vars 0))

private theorem step_pat_1 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_1 vars) (target_pat_1 vars) := by
  refine step_chain ?_ (step_pat_3 (v1 (vars 0)))
  dsimp only [pat_1, pat_3, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_29 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0) (vars 1) (evalTapePattern pat_29 vars) := by
  refine step_base_0 ?_ rfl
  dsimp only [pat_29, pat_0, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_26 (vars : ℕ → Nat) :
  ReachesPat0 0 (vars 0) (evalTapePattern pat_26 vars) := by
  refine step_chain_0 ?_ (step_pat_29 (v2 0 (vars 0)))
  dsimp only [pat_26, pat_29, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_32 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 1) (vars 1) (evalTapePattern pat_32 vars) := by
  refine step_chain_0 ?_ (step_pat_29 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_32, pat_29, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_30 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + vars 1 + 1) (vars 2) (evalTapePattern pat_30 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine step_chain_0 ?_ (step_pat_32 (v2 (vars 0) (vars 2)))
    dsimp only [pat_30, pat_32, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_pat0 (by simp -failIfUnchanged only []; omega) rfl (@step_chain_0 _
      (evalTapePattern pat_33
      (v3 (vars 0) u (vars 2))) _ _ ?_ (step_chain_0 ?_ (ih (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [pat_30, pat_33, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_33, pat_30, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_27 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 1) (vars 1) (evalTapePattern pat_27 vars) := by
  refine cast_pat0 (by simp -failIfUnchanged only []; omega) rfl (step_chain_0 ?_ (step_pat_30
    (v3 0 (vars 0) (vars 1))))
  dsimp only [pat_27, pat_30, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_21 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0) (vars 1) (evalTapePattern pat_21 vars) := by
  rcases h_vr : vars 0 with _ | u
  · refine step_chain_0 ?_ (step_pat_26 (v1 (vars 1)))
    dsimp only [pat_21, pat_26, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain_0 ?_ (step_pat_27 (v2 u (vars 1)))
    dsimp only [pat_21, pat_27, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private theorem step_pat_15 (vars : ℕ → Nat) :
  ReachesPat0 0 (vars 0) (evalTapePattern pat_15 vars) := by
  refine step_chain_0 ?_ (step_pat_21 (v2 0 (vars 0)))
  dsimp only [pat_15, pat_21, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_16 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 1) (vars 1) (evalTapePattern pat_16 vars) := by
  refine step_chain_0 ?_ (step_pat_21 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_16, pat_21, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_10 (vars : ℕ → Nat) :
  ReachesPat0 1 (vars 0) (evalTapePattern pat_10 vars) := by
  refine step_chain_0 ?_ (step_pat_16 (v2 0 (vars 0)))
  dsimp only [pat_10, pat_16, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_6 (vars : ℕ → Nat) :
  ReachesPat0 1 (vars 0) (evalTapePattern pat_6 vars) := by
  refine step_chain_0 ?_ (step_pat_10 (v1 (vars 0)))
  dsimp only [pat_6, pat_10, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_22 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 2) (vars 1) (evalTapePattern pat_22 vars) := by
  refine step_chain_0 ?_ (step_pat_16 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_22, pat_16, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_17 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 2) (vars 1) (evalTapePattern pat_17 vars) := by
  refine step_chain_0 ?_ (step_pat_22 (v2 (vars 0) (vars 1)))
  dsimp only [pat_17, pat_22, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_23 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + vars 1 + 3) (vars 2) (evalTapePattern pat_23 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_pat0 (by simp -failIfUnchanged only []; omega) rfl (step_chain_0 ?_ (step_pat_17
      (v2 (vars 1 + 1) (vars 2))))
    dsimp only [pat_23, pat_17, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine cast_pat0 (by simp -failIfUnchanged only []; omega) rfl (@step_chain_0 _
      (evalTapePattern pat_18
      (v3 v (vars 1 + 1) (vars 2))) _ _ ?_ (step_chain_0 ?_ (ih
      (v3 v (vars 1 + 1) (vars 2)) rfl)))
    · dsimp only [pat_23, pat_18, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_18, pat_23, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_18 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + vars 1 + 3) (vars 2) (evalTapePattern pat_18 vars) := by
  refine step_chain_0 ?_ (step_pat_23 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_18, pat_23, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_11 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 2) (vars 1) (evalTapePattern pat_11 vars) := by
  rcases h_vl : vars 0 with _ | v
  · refine step_chain_0 ?_ (step_pat_17 (v2 0 (vars 1)))
    dsimp only [pat_11, pat_17, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain_0 ?_ (step_pat_18 (v3 v 0 (vars 1)))
    dsimp only [pat_11, pat_18, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private theorem step_pat_7 (vars : ℕ → Nat) :
  ReachesPat0 (vars 0 + 2) (vars 1) (evalTapePattern pat_7 vars) := by
  refine step_chain_0 ?_ (step_pat_11 (v2 (vars 0) (vars 1)))
  dsimp only [pat_7, pat_11, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_4 (_vars : ℕ → Nat) :
  ReachesPat0 0 0 (evalTapePattern pat_4 _vars) := by
  refine @step_chain_0 _ (evalTapePattern pat_9 (v1 1)) _ _ ?_
    (step_chain_0 ?_ (step_pat_15 (v1 0)))
  · dsimp only [pat_4, pat_9, evalTapePattern, evalTapeExpr]; pat_step
  · dsimp only [pat_9, pat_15, evalTapePattern, evalTapeExpr]; pat_step

private theorem step_pat_2_pos (u : ℕ) (vars : ℕ → Nat) (h_vr : vars 1 = u + 1) :
  ReachesPat0 (vars 0 + 1) u (evalTapePattern pat_2 vars) := by
  rcases h_vl : vars 0 with _ | v
  · refine step_chain_0 ?_ (step_pat_6 (v1 u))
    dsimp only [pat_2, pat_6, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  · refine step_chain_0 ?_ (step_pat_7 (v2 v u))
    dsimp only [pat_2, pat_7, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step

private theorem step_pat_2_zero (vars : ℕ → Nat) (h_vr : vars 1 = 0) :
  ReachesPat0 (vars 0) 0 (evalTapePattern pat_2 vars) := by
  rcases h_vl : vars 0 with _ | v
  · refine step_chain_0 ?_ (step_pat_4 (fun _ => 0))
    dsimp only [pat_2, pat_4, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  · refine @step_chain_0 _ (evalTapePattern pat_5 (v1 v)) _ _ ?_
      (step_chain_0 ?_ (step_pat_2_pos 0 (v2 v 1) rfl))
    · dsimp only [pat_2, pat_5, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · dsimp only [pat_5, pat_2, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_0 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_B2 (v3 0 1 (2 * vars 0 + 2 * vars 1 + 2)))

private theorem step_pat_0_aux (n : ℕ) : ∀ vars : ℕ → Nat, vars 1 ≤ n →
  ReachesTarget (evalTapePattern pat_0 vars) (target_pat_0 vars) := by
  induction n with
  | zero =>
    intro vars h_le
    have h_vr : vars 1 = 0 := Nat.eq_zero_of_le_zero h_le
    refine cast_target ?_ (step_chain ?_ (step_pat_1 (v1 (vars 0 + 1))))
    · dsimp only [target_pat_0, target_pat_1, target_pat_3, target_pat_8_pos, target_pat_12_pos]
      rw [h_vr]; congr_vars
    · dsimp only [pat_0, pat_1, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ n ih =>
    intro vars h_le
    rcases h_vr : vars 1 with _ | u
    · exact ih vars (by omega)
    · have h_step : step target (evalTapePattern pat_0 vars) = some (evalTapePattern pat_2
        (v2 (vars 0 + 1) u)) := by
        dsimp only [pat_0, pat_2, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
      rcases u with _ | u'
      · refine cast_target ?_ (step_chain h_step (reaches_pat_0_chain (step_pat_2_zero _ rfl)
          (ih _ (by simp -failIfUnchanged only []; omega))))
        · dsimp only [target_pat_0]; rw [h_vr]; congr_vars
      · refine cast_target ?_ (step_chain h_step (reaches_pat_0_chain (step_pat_2_pos u' _ rfl)
          (ih _ (by simp -failIfUnchanged only []; omega))))
        · dsimp only [target_pat_0]; rw [h_vr]; congr_vars

private theorem step_pat_0 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_0 vars) (target_pat_0 vars) :=
  step_pat_0_aux (vars 1) vars (Nat.le_refl _)

private def target_pat_2 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_B2 (v3 0 1 (2 * vars 0 + 2 * vars 1 + 2)))

private theorem step_pat_2 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_2 vars) (target_pat_2 vars) := by
  rcases h_vr : vars 1 with _ | u
  · refine cast_target ?_ (reaches_pat_0_chain (step_pat_2_zero vars h_vr) (step_pat_0 _))
    dsimp only [target_pat_2, target_pat_0]; rw [h_vr]; congr_vars
  · refine cast_target ?_ (reaches_pat_0_chain (step_pat_2_pos u vars h_vr) (step_pat_0 _))
    dsimp only [target_pat_2, target_pat_0]; rw [h_vr]; congr_vars

private def target_pat_25 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_1 (v1 0)
  | u + 1 => target_pat_2 (v2 0 u)
private theorem step_pat_25 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_25 vars) (target_pat_25 vars) := by
  unfold target_pat_25
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_1 (v1 0))
    dsimp only [pat_25, pat_1, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_2 (v2 0 u))
    dsimp only [pat_25, pat_2, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_41 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  none
private theorem step_pat_41 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_41 vars) (target_pat_41 vars) := by
  unfold target_pat_41
  refine @step_halt _ (evalTapePattern pat_45 (v1 (vars 0))) ?_ (by
    dsimp only [pat_45, evalTapePattern, evalTapeExpr]; bb_halt)
  dsimp only [pat_41, pat_45, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_61 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_25 (v1 1)
  | u + 1 => target_pat_25 (v1 ((u + 1) + 1))
private theorem step_pat_61 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_61 vars) (target_pat_61 vars) := by
  unfold target_pat_61
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_25 (v1 1))
    dsimp only [pat_61, pat_25, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_25 (v1 ((u + 1) + 1)))
    dsimp only [pat_61, pat_25, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_57 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_61 (v1 1)
private theorem step_pat_57 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_57 vars) (target_pat_57 vars) := by
  unfold target_pat_57
  refine step_chain ?_ (step_pat_61 (v1 1))
  dsimp only [pat_57, pat_61, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_53 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_57 (fun _ => 0)
private theorem step_pat_53 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_53 vars) (target_pat_53 vars) := by
  unfold target_pat_53
  refine step_chain ?_ (step_pat_57 (fun _ => 0))
  dsimp only [pat_53, pat_57, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_46 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_53 (fun _ => 0)
private theorem step_pat_46 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_46 vars) (target_pat_46 vars) := by
  unfold target_pat_46
  refine step_chain ?_ (step_pat_53 (fun _ => 0))
  dsimp only [pat_46, pat_53, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_62 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_0 (v2 (vars 0) 1)
  | u + 1 => target_pat_0 (v2 (vars 0) ((u + 1) + 1))
private theorem step_pat_62 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_62 vars) (target_pat_62 vars) := by
  unfold target_pat_62
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_0 (v2 (vars 0) 1))
    dsimp only [pat_62, pat_0, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_0 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_62, pat_0, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_58 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_62 (v2 (vars 0) 1)
private theorem step_pat_58 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_58 vars) (target_pat_58 vars) := by
  unfold target_pat_58
  refine step_chain ?_ (step_pat_62 (v2 (vars 0) 1))
  dsimp only [pat_58, pat_62, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_54 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_58 (v1 (vars 0))
private theorem step_pat_54 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_54 vars) (target_pat_54 vars) := by
  unfold target_pat_54
  refine step_chain ?_ (step_pat_58 (v1 (vars 0)))
  dsimp only [pat_54, pat_58, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_47 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_54 (v1 (vars 0))
private theorem step_pat_47 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_47 vars) (target_pat_47 vars) := by
  unfold target_pat_47
  refine step_chain ?_ (step_pat_54 (v1 (vars 0)))
  dsimp only [pat_47, pat_54, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_85 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_61 (v1 ((vars 0 + 1) + 1))
private theorem step_pat_85 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_85 vars) (target_pat_85 vars) := by
  unfold target_pat_85
  refine step_chain ?_ (step_pat_61 (v1 ((vars 0 + 1) + 1)))
  dsimp only [pat_85, pat_61, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_77 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_85 (v1 (2 * vars 0 + vars 1))
private theorem step_pat_77 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_77 vars) (target_pat_77 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_85 (v1 0)))
      · dsimp only [target_pat_77]; rw [h_vr, h_vl]
      · dsimp only [pat_77, pat_85, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_85 (v1 (u + 1))))
      · dsimp only [target_pat_77]; rw [h_vr, h_vl, Nat.mul_zero, Nat.zero_add]
      · dsimp only [pat_77, pat_85, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_86 (v2 v 0)) _ ?_ (step_chain
        ?_ (ih (v2 v 2)
        rfl)))
      · dsimp only [target_pat_77]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_77, pat_86, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
      · dsimp only [pat_86, pat_77, evalTapePattern, evalTapeExpr]; pat_step
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_86 (v2 v (u + 1))) _ ?_
        (step_chain ?_ (ih (v2 v (((u + 1) + 1) + 1)) rfl)))
      · dsimp only [target_pat_77]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_77, pat_86, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
      · dsimp only [pat_86, pat_77, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_67 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_77 (v2 (vars 0) 1)
private theorem step_pat_67 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_67 vars) (target_pat_67 vars) := by
  unfold target_pat_67
  refine step_chain ?_ (step_pat_77 (v2 (vars 0) 1))
  dsimp only [pat_67, pat_77, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_63 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_67 (v1 (vars 0))
private theorem step_pat_63 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_63 vars) (target_pat_63 vars) := by
  unfold target_pat_63
  refine step_chain ?_ (step_pat_67 (v1 (vars 0)))
  dsimp only [pat_63, pat_67, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_59 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_63 (v1 0)
  | u + 1 => some (evalTapePattern pat_B2 (v3 ((v2 0 u) 0) 0 ((v2 0 u) 1)))
private theorem step_pat_59 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_59 vars) (target_pat_59 vars) := by
  unfold target_pat_59
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_63 (v1 0))
    dsimp only [pat_59, pat_63, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base_64 (v2 0 u) ?_
    dsimp only [pat_59, pat_64, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_55 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_59 (v1 (vars 0))
private theorem step_pat_55 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_55 vars) (target_pat_55 vars) := by
  unfold target_pat_55
  refine step_chain ?_ (step_pat_59 (v1 (vars 0)))
  dsimp only [pat_55, pat_59, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_48 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_55 (v1 (vars 0))
private theorem step_pat_48 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_48 vars) (target_pat_48 vars) := by
  unfold target_pat_48
  refine step_chain ?_ (step_pat_55 (v1 (vars 0)))
  dsimp only [pat_48, pat_55, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_92 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_62 (v2 (vars 0) ((vars 1 + 1) + 1))
private theorem step_pat_92 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_92 vars) (target_pat_92 vars) := by
  unfold target_pat_92
  refine step_chain ?_ (step_pat_62 (v2 (vars 0) ((vars 1 + 1) + 1)))
  dsimp only [pat_92, pat_62, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_81 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_92 (v2 (vars 1) (2 * vars 0 + vars 2))
private theorem step_pat_81 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_81 vars) (target_pat_81 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 2 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_92 (v2 (vars 1) 0)))
      · dsimp only [target_pat_81]; rw [h_vr, h_vl]
      · dsimp only [pat_81, pat_92, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_92 (v2 (vars 1) (u + 1))))
      · dsimp only [target_pat_81]; rw [h_vr, h_vl, Nat.mul_zero, Nat.zero_add]
      · dsimp only [pat_81, pat_92, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  | succ v ih =>
    rcases h_vr : vars 2 with _ | u
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_93 (v3 v (vars 1) 0)) _
        ?_ (step_chain ?_ (ih (v3 v (vars 1) 2) rfl)))
      · dsimp only [target_pat_81]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_81, pat_93, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
      · dsimp only [pat_93, pat_81, evalTapePattern, evalTapeExpr]; pat_step
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_93 (v3 v (vars 1) (u + 1))) _
        ?_ (step_chain ?_ (ih (v3 v (vars 1) (((u + 1) + 1) + 1)) rfl)))
      · dsimp only [target_pat_81]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_81, pat_93, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
      · dsimp only [pat_93, pat_81, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_72 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_81 (v3 (vars 0) (vars 1) 1)
private theorem step_pat_72 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_72 vars) (target_pat_72 vars) := by
  unfold target_pat_72
  refine step_chain ?_ (step_pat_81 (v3 (vars 0) (vars 1) 1))
  dsimp only [pat_72, pat_81, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_65 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_72 (v2 (vars 0) (vars 1))
private theorem step_pat_65 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_65 vars) (target_pat_65 vars) := by
  unfold target_pat_65
  refine step_chain ?_ (step_pat_72 (v2 (vars 0) (vars 1)))
  dsimp only [pat_65, pat_72, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_60 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_65 (v2 0 (vars 0))
  | u + 1 => some (evalTapePattern pat_B2
    (v3 ((v3 0 (vars 0) u) 0) ((v3 0 (vars 0) u) 1 + 1) ((v3 0 (vars 0) u) 2)))
private theorem step_pat_60 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_60 vars) (target_pat_60 vars) := by
  unfold target_pat_60
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_65 (v2 0 (vars 0)))
    dsimp only [pat_60, pat_65, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base_66 (v3 0 (vars 0) u) ?_
    dsimp only [pat_60, pat_66, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_56 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_60 (v2 (vars 0) (vars 1))
private theorem step_pat_56 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_56 vars) (target_pat_56 vars) := by
  unfold target_pat_56
  refine step_chain ?_ (step_pat_60 (v2 (vars 0) (vars 1)))
  dsimp only [pat_56, pat_60, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_49 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_56 (v2 (vars 0) (vars 1))
private theorem step_pat_49 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_49 vars) (target_pat_49 vars) := by
  unfold target_pat_49
  refine step_chain ?_ (step_pat_56 (v2 (vars 0) (vars 1)))
  dsimp only [pat_49, pat_56, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_42 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => match vars 0 with
    | 0 => target_pat_46 (fun _ => 0)
    | v + 1 => target_pat_47 (v1 v)
  | u + 1 => match vars 0 with
    | 0 => target_pat_48 (v1 u)
    | v + 1 => target_pat_49 (v2 v u)
private theorem step_pat_42 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_42 vars) (target_pat_42 vars) := by
  unfold target_pat_42
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_46 (fun _ => 0))
      dsimp only [pat_42, pat_46, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_47 (v1 v))
      dsimp only [pat_42, pat_47, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_48 (v1 u))
      dsimp only [pat_42, pat_48, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_49 (v2 v u))
      dsimp only [pat_42, pat_49, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step

private def target_pat_38 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_41 (v1 0)
  | u + 1 => target_pat_42 (v2 0 u)
private theorem step_pat_38 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_38 vars) (target_pat_38 vars) := by
  unfold target_pat_38
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_41 (v1 0))
    dsimp only [pat_38, pat_41, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_42 (v2 0 u))
    dsimp only [pat_38, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_36 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_38 (v1 (vars 0))
private theorem step_pat_36 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_36 vars) (target_pat_36 vars) := by
  unfold target_pat_36
  refine step_chain ?_ (step_pat_38 (v1 (vars 0)))
  dsimp only [pat_36, pat_38, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_34 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_36 (v1 0)
  | u + 1 => target_pat_36 (v1 (u + 1))
private theorem step_pat_34 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_34 vars) (target_pat_34 vars) := by
  unfold target_pat_34
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_36 (v1 0))
    dsimp only [pat_34, pat_36, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_36 (v1 (u + 1)))
    dsimp only [pat_34, pat_36, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_50 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_41 (v1 (vars 0 + 1))
  | u + 1 => target_pat_42 (v2 (vars 0 + 1) u)
private theorem step_pat_50 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_50 vars) (target_pat_50 vars) := by
  unfold target_pat_50
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_41 (v1 (vars 0 + 1)))
    dsimp only [pat_50, pat_41, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_42 (v2 (vars 0 + 1) u))
    dsimp only [pat_50, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_43 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_50 (v2 (vars 0) (vars 1))
private theorem step_pat_43 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_43 vars) (target_pat_43 vars) := by
  unfold target_pat_43
  refine step_chain ?_ (step_pat_50 (v2 (vars 0) (vars 1)))
  dsimp only [pat_43, pat_50, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_39 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_43 (v2 0 (vars 0))
private theorem step_pat_39 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_39 vars) (target_pat_39 vars) := by
  unfold target_pat_39
  refine step_chain ?_ (step_pat_43 (v2 0 (vars 0)))
  dsimp only [pat_39, pat_43, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_51 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_43 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_51 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_51 vars) (target_pat_51 vars) := by
  unfold target_pat_51
  refine step_chain ?_ (step_pat_43 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_51, pat_43, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_44 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_51 (v2 (vars 0 + (vars 1)) (vars 2))
private theorem step_pat_44 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_44 vars) (target_pat_44 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_51 (v2 (vars 0) (vars 2))))
    · dsimp only [target_pat_44]; congr_vars
    · dsimp only [pat_44, pat_51, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_52 (v3 (vars 0) u (vars 2))) _
      ?_ (step_chain ?_ (ih (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_44]; congr_vars
    · dsimp only [pat_44, pat_52, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_52, pat_44, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_40 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_44 (v3 0 (vars 0) (vars 1))
private theorem step_pat_40 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_40 vars) (target_pat_40 vars) := by
  unfold target_pat_40
  refine step_chain ?_ (step_pat_44 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_40, pat_44, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_37 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_39 (v1 (vars 1))
  | u + 1 => target_pat_40 (v2 u (vars 1))
private theorem step_pat_37 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_37 vars) (target_pat_37 vars) := by
  unfold target_pat_37
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_39 (v1 (vars 1)))
    dsimp only [pat_37, pat_39, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_40 (v2 u (vars 1)))
    dsimp only [pat_37, pat_40, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_35 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_37 (v2 0 (vars 0))
private theorem step_pat_35 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_35 vars) (target_pat_35 vars) := by
  unfold target_pat_35
  refine step_chain ?_ (step_pat_37 (v2 0 (vars 0)))
  dsimp only [pat_35, pat_37, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_31 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_34 (v1 0)
  | u + 1 => target_pat_35 (v1 u)
private theorem step_pat_31 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_31 vars) (target_pat_31 vars) := by
  unfold target_pat_31
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_34 (v1 0))
    dsimp only [pat_31, pat_34, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_35 (v1 u))
    dsimp only [pat_31, pat_35, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_28 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_31 (v1 (vars 0))
private theorem step_pat_28 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_28 vars) (target_pat_28 vars) := by
  unfold target_pat_28
  refine step_chain ?_ (step_pat_31 (v1 (vars 0)))
  dsimp only [pat_28, pat_31, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_24 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_28 (v1 (vars 0 + 1))
private theorem step_pat_24 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_24 vars) (target_pat_24 vars) := by
  unfold target_pat_24
  refine step_chain ?_ (step_pat_28 (v1 (vars 0 + 1)))
  dsimp only [pat_24, pat_28, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_19 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_24 (v1 0)
  | u + 1 => target_pat_24 (v1 (u + 1))
private theorem step_pat_19 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_19 vars) (target_pat_19 vars) := by
  unfold target_pat_19
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_24 (v1 0))
    dsimp only [pat_19, pat_24, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_24 (v1 (u + 1)))
    dsimp only [pat_19, pat_24, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_154 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_19 (v1 1)
private theorem step_pat_154 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_154 vars) (target_pat_154 vars) := by
  unfold target_pat_154
  refine step_chain ?_ (step_pat_19 (v1 1))
  dsimp only [pat_154, pat_19, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_150 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_154 (fun _ => 0)
private theorem step_pat_150 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_150 vars) (target_pat_150 vars) := by
  unfold target_pat_150
  refine step_chain ?_ (step_pat_154 (fun _ => 0))
  dsimp only [pat_150, pat_154, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_20 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_25 (v1 (vars 0))
private theorem step_pat_20 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_20 vars) (target_pat_20 vars) := by
  unfold target_pat_20
  refine step_chain ?_ (step_pat_25 (v1 (vars 0)))
  dsimp only [pat_20, pat_25, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_14 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_20 (v1 0)
private theorem step_pat_14 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_14 vars) (target_pat_14 vars) := by
  unfold target_pat_14
  refine step_chain ?_ (step_pat_20 (v1 0))
  dsimp only [pat_14, pat_20, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_9 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_14 (fun _ => 0)
  | u + 1 => target_pat_0 (v2 0 u)
private theorem step_pat_9 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_9 vars) (target_pat_9 vars) := by
  unfold target_pat_9
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_14 (fun _ => 0))
    dsimp only [pat_9, pat_14, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (reaches_pat_0_chain (step_pat_15 (v1 u)) (step_pat_0 _))
    dsimp only [pat_9, pat_15, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_135 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_150 (fun _ => 0)
  | u + 1 => target_pat_9 (v1 u)
private theorem step_pat_135 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_135 vars) (target_pat_135 vars) := by
  unfold target_pat_135
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_150 (fun _ => 0))
    dsimp only [pat_135, pat_150, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_9 (v1 u))
    dsimp only [pat_135, pat_9, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_126 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_135 (v1 1)
  | u + 1 => target_pat_135 (v1 ((u + 1) + 1))
private theorem step_pat_126 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_126 vars) (target_pat_126 vars) := by
  unfold target_pat_126
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_135 (v1 1))
    dsimp only [pat_126, pat_135, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_135 (v1 ((u + 1) + 1)))
    dsimp only [pat_126, pat_135, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_155 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_126 (v1 ((vars 0 + 1) + 1))
private theorem step_pat_155 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_155 vars) (target_pat_155 vars) := by
  unfold target_pat_155
  refine step_chain ?_ (step_pat_126 (v1 ((vars 0 + 1) + 1)))
  dsimp only [pat_155, pat_126, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_151 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_155 (v1 (2 * vars 0 + vars 1))
private theorem step_pat_151 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_151 vars) (target_pat_151 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (step_chain ?_ (step_pat_155 (v1 0)))
      · dsimp only [target_pat_151]; rw [h_vr, h_vl]
      · dsimp only [pat_151, pat_155, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
        pat_step
    · refine cast_target ?_ (step_chain ?_ (step_pat_155 (v1 (u + 1))))
      · dsimp only [target_pat_151]; rw [h_vr, h_vl, Nat.mul_zero, Nat.zero_add]
      · dsimp only [pat_151, pat_155, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
        pat_step
  | succ v ih =>
    rcases h_vr : vars 1 with _ | u
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_156 (v2 v 0)) _ ?_ (step_chain
        ?_ (ih (v2 v 2) rfl)))
      · dsimp only [target_pat_151]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_151, pat_156, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
        pat_step
      · dsimp only [pat_156, pat_151, evalTapePattern, evalTapeExpr]; pat_step
    · refine cast_target ?_ (@step_chain _ (evalTapePattern pat_156 (v2 v (u + 1))) _ ?_
        (step_chain ?_ (ih (v2 v (((u + 1) + 1) + 1)) rfl)))
      · dsimp only [target_pat_151]; rw [h_vr, h_vl]; congr_vars
      · dsimp only [pat_151, pat_156, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
        pat_step
      · dsimp only [pat_156, pat_151, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_136 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_151 (v2 (vars 0) 1)
private theorem step_pat_136 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_136 vars) (target_pat_136 vars) := by
  unfold target_pat_136
  refine step_chain ?_ (step_pat_151 (v2 (vars 0) 1))
  dsimp only [pat_136, pat_151, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_127 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_136 (v1 (vars 0))
private theorem step_pat_127 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_127 vars) (target_pat_127 vars) := by
  unfold target_pat_127
  refine step_chain ?_ (step_pat_136 (v1 (vars 0)))
  dsimp only [pat_127, pat_136, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_137 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_31 (v1 1)
private theorem step_pat_137 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_137 vars) (target_pat_137 vars) := by
  unfold target_pat_137
  refine step_chain ?_ (step_pat_31 (v1 1))
  dsimp only [pat_137, pat_31, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_157 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_37 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_157 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_157 vars) (target_pat_157 vars) := by
  unfold target_pat_157
  refine step_chain ?_ (step_pat_37 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_157, pat_37, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_152 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_157 (v2 0 (vars 0))
private theorem step_pat_152 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_152 vars) (target_pat_152 vars) := by
  unfold target_pat_152
  refine step_chain ?_ (step_pat_157 (v2 0 (vars 0)))
  dsimp only [pat_152, pat_157, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_139 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_152 (v1 (vars 0))
private theorem step_pat_139 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_139 vars) (target_pat_139 vars) := by
  unfold target_pat_139
  refine step_chain ?_ (step_pat_152 (v1 (vars 0)))
  dsimp only [pat_139, pat_152, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_160 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_157 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_160 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_160 vars) (target_pat_160 vars) := by
  unfold target_pat_160
  refine step_chain ?_ (step_pat_157 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_160, pat_157, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_158 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_160 (v2 (vars 0) (vars 1))
private theorem step_pat_158 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_158 vars) (target_pat_158 vars) := by
  unfold target_pat_158
  refine step_chain ?_ (step_pat_160 (v2 (vars 0) (vars 1)))
  dsimp only [pat_158, pat_160, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_161 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_158 (v2 ((vars 1 + (vars 0)) + 1) (vars 2))
private theorem step_pat_161 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_161 vars) (target_pat_161 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_158 (v2 (vars 1 + 1) (vars 2))))
    · dsimp only [target_pat_161]; congr_vars
    · dsimp only [pat_161, pat_158, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_159
      (v3 v (vars 1 + 1) (vars 2))) _ ?_ (step_chain ?_ (ih (v3 v (vars 1 + 1) (vars 2)) rfl)))
    · dsimp only [target_pat_161]; congr_vars
    · dsimp only [pat_161, pat_159, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_159, pat_161, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_159 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_161 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_159 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_159 vars) (target_pat_159 vars) := by
  unfold target_pat_159
  refine step_chain ?_ (step_pat_161 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_159, pat_161, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_153 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_158 (v2 0 (vars 1))
  | v + 1 => target_pat_159 (v3 v 0 (vars 1))
private theorem step_pat_153 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_153 vars) (target_pat_153 vars) := by
  unfold target_pat_153
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_158 (v2 0 (vars 1)))
    dsimp only [pat_153, pat_158, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_159 (v3 v 0 (vars 1)))
    dsimp only [pat_153, pat_159, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_140 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_153 (v2 (vars 0) (vars 1))
private theorem step_pat_140 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_140 vars) (target_pat_140 vars) := by
  unfold target_pat_140
  refine step_chain ?_ (step_pat_153 (v2 (vars 0) (vars 1)))
  dsimp only [pat_140, pat_153, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_128 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => match vars 0 with
    | 0 => target_pat_137 (fun _ => 0)
    | v + 1 => match v with
      | 0 => target_pat_139 (v1 0)
      | v' + 1 => target_pat_140 (v2 v' 0)
  | u + 1 => match vars 0 with
    | 0 => target_pat_139 (v1 u)
    | v + 1 => target_pat_140 (v2 v u)
private theorem step_pat_128 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_128 vars) (target_pat_128 vars) := by
  unfold target_pat_128
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_137 (fun _ => 0))
      dsimp only [pat_128, pat_137, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · rcases v with _ | v'
      · refine @step_chain _ (evalTapePattern pat_138 (v1 0)) _
          ?_ (@step_chain _ (evalTapePattern pat_128 (v2 0 1)) _ ?_ (step_chain
            ?_ (step_pat_139 (v1 0))))
        · dsimp only [pat_128, pat_138, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
          pat_step
        · dsimp only [pat_138, pat_128, evalTapePattern, evalTapeExpr]; pat_step
        · dsimp only [pat_128, pat_139, evalTapePattern, evalTapeExpr]; pat_step
      · refine @step_chain _ (evalTapePattern pat_138 (v1 (v' + 1))) _ ?_
          (@step_chain _ (evalTapePattern pat_128 (v2 (v' + 1) 1)) _ ?_ (step_chain
            ?_ (step_pat_140 (v2 v' 0))))
        · dsimp only [pat_128, pat_138, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]
          pat_step
        · dsimp only [pat_138, pat_128, evalTapePattern, evalTapeExpr]; pat_step
        · dsimp only [pat_128, pat_140, evalTapePattern, evalTapeExpr]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_139 (v1 u))
      dsimp only [pat_128, pat_139, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_140 (v2 v u))
      dsimp only [pat_128, pat_140, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step

private def target_pat_141 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_127 (v1 (vars 0 + 1))
  | u + 1 => target_pat_128 (v2 (vars 0 + 1) u)
private theorem step_pat_141 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_141 vars) (target_pat_141 vars) := by
  unfold target_pat_141
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_127 (v1 (vars 0 + 1)))
    dsimp only [pat_141, pat_127, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_128 (v2 (vars 0 + 1) u))
    dsimp only [pat_141, pat_128, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_129 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_141 (v2 (vars 0) (vars 1))
private theorem step_pat_129 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_129 vars) (target_pat_129 vars) := by
  unfold target_pat_129
  refine step_chain ?_ (step_pat_141 (v2 (vars 0) (vars 1)))
  dsimp only [pat_129, pat_141, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_120 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_129 (v2 0 (vars 0))
private theorem step_pat_120 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_120 vars) (target_pat_120 vars) := by
  unfold target_pat_120
  refine step_chain ?_ (step_pat_129 (v2 0 (vars 0)))
  dsimp only [pat_120, pat_129, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_142 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_129 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_142 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_142 vars) (target_pat_142 vars) := by
  unfold target_pat_142
  refine step_chain ?_ (step_pat_129 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_142, pat_129, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_130 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_142 (v2 (vars 0 + (vars 1)) (vars 2))
private theorem step_pat_130 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_130 vars) (target_pat_130 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_142 (v2 (vars 0) (vars 2))))
    · dsimp only [target_pat_130]; congr_vars
    · dsimp only [pat_130, pat_142, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_143 (v3 (vars 0) u (vars 2))) _
      ?_ (step_chain ?_ (ih (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_130]; congr_vars
    · dsimp only [pat_130, pat_143, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_143, pat_130, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_121 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_130 (v3 0 (vars 0) (vars 1))
private theorem step_pat_121 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_121 vars) (target_pat_121 vars) := by
  unfold target_pat_121
  refine step_chain ?_ (step_pat_130 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_121, pat_130, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_115 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_120 (v1 (vars 1))
  | u + 1 => target_pat_121 (v2 u (vars 1))
private theorem step_pat_115 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_115 vars) (target_pat_115 vars) := by
  unfold target_pat_115
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_120 (v1 (vars 1)))
    dsimp only [pat_115, pat_120, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_121 (v2 u (vars 1)))
    dsimp only [pat_115, pat_121, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_110 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_115 (v2 (vars 0) (vars 1))
private theorem step_pat_110 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_110 vars) (target_pat_110 vars) := by
  unfold target_pat_110
  refine step_chain ?_ (step_pat_115 (v2 (vars 0) (vars 1)))
  dsimp only [pat_110, pat_115, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_100 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_110 (v2 0 (vars 0))
private theorem step_pat_100 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_100 vars) (target_pat_100 vars) := by
  unfold target_pat_100
  refine step_chain ?_ (step_pat_110 (v2 0 (vars 0)))
  dsimp only [pat_100, pat_110, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_101 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_110 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_101 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_101 vars) (target_pat_101 vars) := by
  unfold target_pat_101
  refine step_chain ?_ (step_pat_110 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_101, pat_110, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_89 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_101 (v2 (vars 0) (vars 1))
private theorem step_pat_89 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_89 vars) (target_pat_89 vars) := by
  unfold target_pat_89
  refine step_chain ?_ (step_pat_101 (v2 (vars 0) (vars 1)))
  dsimp only [pat_89, pat_101, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_102 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_102 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_102 vars) (target_pat_102 vars) := by
  unfold target_pat_102
  refine step_chain ?_ (step_pat_89 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_102, pat_89, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_90 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_102 (v2 (vars 0) (vars 1))
private theorem step_pat_90 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_90 vars) (target_pat_90 vars) := by
  unfold target_pat_90
  refine step_chain ?_ (step_pat_102 (v2 (vars 0) (vars 1)))
  dsimp only [pat_90, pat_102, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_103 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_90 (v2 ((vars 1 + (vars 0)) + 1) (vars 2))
private theorem step_pat_103 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_103 vars) (target_pat_103 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_90 (v2 (vars 1 + 1) (vars 2))))
    · dsimp only [target_pat_103]; congr_vars
    · dsimp only [pat_103, pat_90, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_91 (v3 v (vars 1 + 1) (vars 2))) _
      ?_ (step_chain ?_ (ih (v3 v (vars 1 + 1) (vars 2)) rfl)))
    · dsimp only [target_pat_103]; congr_vars
    · dsimp only [pat_103, pat_91, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_91, pat_103, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_144 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_63 (v1 (vars 0 + 1))
  | u + 1 => some (evalTapePattern pat_B2 (v3 ((v2 (vars 0 + 1) u) 0) 0 ((v2 (vars 0 + 1) u) 1)))
private theorem step_pat_144 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_144 vars) (target_pat_144 vars) := by
  unfold target_pat_144
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_63 (v1 (vars 0 + 1)))
    dsimp only [pat_144, pat_63, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base_64 (v2 (vars 0 + 1) u) ?_
    dsimp only [pat_144, pat_64, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_131 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_144 (v2 (vars 0) (vars 1))
private theorem step_pat_131 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_131 vars) (target_pat_131 vars) := by
  unfold target_pat_131
  refine step_chain ?_ (step_pat_144 (v2 (vars 0) (vars 1)))
  dsimp only [pat_131, pat_144, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_122 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_131 (v2 0 (vars 0))
private theorem step_pat_122 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_122 vars) (target_pat_122 vars) := by
  unfold target_pat_122
  refine step_chain ?_ (step_pat_131 (v2 0 (vars 0)))
  dsimp only [pat_122, pat_131, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_145 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_131 (v2 (vars 0 + 1) (vars 1))
private theorem step_pat_145 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_145 vars) (target_pat_145 vars) := by
  unfold target_pat_145
  refine step_chain ?_ (step_pat_131 (v2 (vars 0 + 1) (vars 1)))
  dsimp only [pat_145, pat_131, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_132 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_145 (v2 (vars 0 + (vars 1)) (vars 2))
private theorem step_pat_132 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_132 vars) (target_pat_132 vars) := by
  induction h_vr : vars 1 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_145 (v2 (vars 0) (vars 2))))
    · dsimp only [target_pat_132]; congr_vars
    · dsimp only [pat_132, pat_145, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_146 (v3 (vars 0) u (vars 2))) _
      ?_ (step_chain ?_ (ih (v3 (vars 0 + 1) u (vars 2)) rfl)))
    · dsimp only [target_pat_132]; congr_vars
    · dsimp only [pat_132, pat_146, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_146, pat_132, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_123 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_132 (v3 0 (vars 0) (vars 1))
private theorem step_pat_123 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_123 vars) (target_pat_123 vars) := by
  unfold target_pat_123
  refine step_chain ?_ (step_pat_132 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_123, pat_132, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_116 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_122 (v1 (vars 1))
  | u + 1 => target_pat_123 (v2 u (vars 1))
private theorem step_pat_116 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_116 vars) (target_pat_116 vars) := by
  unfold target_pat_116
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_122 (v1 (vars 1)))
    dsimp only [pat_116, pat_122, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_123 (v2 u (vars 1)))
    dsimp only [pat_116, pat_123, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_111 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_116 (v2 (vars 0) (vars 1))
private theorem step_pat_111 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_111 vars) (target_pat_111 vars) := by
  unfold target_pat_111
  refine step_chain ?_ (step_pat_116 (v2 (vars 0) (vars 1)))
  dsimp only [pat_111, pat_116, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_147 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => target_pat_65 (v2 (vars 0 + 1) (vars 1))
  | u + 1 => some (evalTapePattern pat_B2
    (v3 ((v3 (vars 0 + 1) (vars 1) u) 0) ((v3 (vars 0 + 1) (vars 1) u) 1 + 1) ((v3 (vars 0 + 1)
      (vars 1) u) 2)))
private theorem step_pat_147 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_147 vars) (target_pat_147 vars) := by
  unfold target_pat_147
  rcases h_vr : vars 2 with _ | u
  · refine step_chain ?_ (step_pat_65 (v2 (vars 0 + 1) (vars 1)))
    dsimp only [pat_147, pat_65, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_base_66 (v3 (vars 0 + 1) (vars 1) u)
      ?_
    dsimp only [pat_147, pat_66, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_133 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_147 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_133 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_133 vars) (target_pat_133 vars) := by
  unfold target_pat_133
  refine step_chain ?_ (step_pat_147 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_133, pat_147, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_124 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_133 (v3 0 (vars 0) (vars 1))
private theorem step_pat_124 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_124 vars) (target_pat_124 vars) := by
  unfold target_pat_124
  refine step_chain ?_ (step_pat_133 (v3 0 (vars 0) (vars 1)))
  dsimp only [pat_124, pat_133, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_148 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_133 (v3 (vars 0 + 1) (vars 1) (vars 2))
private theorem step_pat_148 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_148 vars) (target_pat_148 vars) := by
  unfold target_pat_148
  refine step_chain ?_ (step_pat_133 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_148, pat_133, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_134 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_148 (v3 (vars 0 + (vars 2)) (vars 1) (vars 3))
private theorem step_pat_134 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_134 vars) (target_pat_134 vars) := by
  induction h_vr : vars 2 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_148 (v3 (vars 0) (vars 1) (vars 3))))
    · dsimp only [target_pat_134]; congr_vars
    · dsimp only [pat_134, pat_148, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  | succ u ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_149
      (v4 (vars 0) (vars 1) u (vars 3))) _ ?_ (step_chain ?_ (ih
        (v4 (vars 0 + 1) (vars 1) u (vars 3)) rfl)))
    · dsimp only [target_pat_134]; congr_vars
    · dsimp only [pat_134, pat_149, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
    · dsimp only [pat_149, pat_134, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_125 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_134 (v4 0 (vars 0) (vars 1) (vars 2))
private theorem step_pat_125 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_125 vars) (target_pat_125 vars) := by
  unfold target_pat_125
  refine step_chain ?_ (step_pat_134 (v4 0 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_125, pat_134, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_117 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_124 (v2 (vars 0) (vars 2))
  | u + 1 => target_pat_125 (v3 (vars 0) u (vars 2))
private theorem step_pat_117 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_117 vars) (target_pat_117 vars) := by
  unfold target_pat_117
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_124 (v2 (vars 0) (vars 2)))
    dsimp only [pat_117, pat_124, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_125 (v3 (vars 0) u (vars 2)))
    dsimp only [pat_117, pat_125, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_112 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_117 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_112 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_112 vars) (target_pat_112 vars) := by
  unfold target_pat_112
  refine step_chain ?_ (step_pat_117 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_112, pat_117, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_104 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_111 (v2 0 (vars 1))
  | v + 1 => target_pat_112 (v3 v 0 (vars 1))
private theorem step_pat_104 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_104 vars) (target_pat_104 vars) := by
  unfold target_pat_104
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_111 (v2 0 (vars 1)))
    dsimp only [pat_104, pat_111, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_112 (v3 v 0 (vars 1)))
    dsimp only [pat_104, pat_112, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_105 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_111 (v2 (vars 1 + 1) (vars 2))
  | v + 1 => target_pat_112 (v3 v (vars 1 + 1) (vars 2))
private theorem step_pat_105 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_105 vars) (target_pat_105 vars) := by
  unfold target_pat_105
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_111 (v2 (vars 1 + 1) (vars 2)))
    dsimp only [pat_105, pat_111, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_112 (v3 v (vars 1 + 1) (vars 2)))
    dsimp only [pat_105, pat_112, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_96 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_105 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_96 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_96 vars) (target_pat_96 vars) := by
  unfold target_pat_96
  refine step_chain ?_ (step_pat_105 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_96, pat_105, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_106 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_96 (v3 (vars 0) (vars 1 + 1) (vars 2))
private theorem step_pat_106 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_106 vars) (target_pat_106 vars) := by
  unfold target_pat_106
  refine step_chain ?_ (step_pat_96 (v3 (vars 0) (vars 1 + 1) (vars 2)))
  dsimp only [pat_106, pat_96, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_97 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_106 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_97 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_97 vars) (target_pat_97 vars) := by
  unfold target_pat_97
  refine step_chain ?_ (step_pat_106 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_97, pat_106, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_107 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_97 (v3 (vars 1) ((vars 2 + (vars 0)) + 1) (vars 3))
private theorem step_pat_107 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_107 vars) (target_pat_107 vars) := by
  induction h_vl : vars 0 generalizing vars with
  | zero =>
    refine cast_target ?_ (step_chain ?_ (step_pat_97 (v3 (vars 1) (vars 2 + 1) (vars 3))))
    · dsimp only [target_pat_107]; congr_vars
    · dsimp only [pat_107, pat_97, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  | succ v ih =>
    refine cast_target ?_ (@step_chain _ (evalTapePattern pat_98
      (v4 v (vars 1) (vars 2 + 1) (vars 3))) _ ?_ (step_chain ?_ (ih
        (v4 v (vars 1) (vars 2 + 1) (vars 3)) rfl)))
    · dsimp only [target_pat_107]; congr_vars
    · dsimp only [pat_107, pat_98, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
    · dsimp only [pat_98, pat_107, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_118 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_126 (v1 1)
private theorem step_pat_118 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_118 vars) (target_pat_118 vars) := by
  unfold target_pat_118
  refine step_chain ?_ (step_pat_126 (v1 1))
  dsimp only [pat_118, pat_126, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_113 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_118 (fun _ => 0)
private theorem step_pat_113 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_113 vars) (target_pat_113 vars) := by
  unfold target_pat_113
  refine step_chain ?_ (step_pat_118 (fun _ => 0))
  dsimp only [pat_113, pat_118, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_108 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_113 (fun _ => 0)
private theorem step_pat_108 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_108 vars) (target_pat_108 vars) := by
  unfold target_pat_108
  refine step_chain ?_ (step_pat_113 (fun _ => 0))
  dsimp only [pat_108, pat_113, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_119 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_127 (v1 0)
  | u + 1 => target_pat_128 (v2 0 u)
private theorem step_pat_119 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_119 vars) (target_pat_119 vars) := by
  unfold target_pat_119
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_127 (v1 0))
    dsimp only [pat_119, pat_127, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_128 (v2 0 u))
    dsimp only [pat_119, pat_128, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_114 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_119 (v1 (vars 0))
private theorem step_pat_114 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_114 vars) (target_pat_114 vars) := by
  unfold target_pat_114
  refine step_chain ?_ (step_pat_119 (v1 (vars 0)))
  dsimp only [pat_114, pat_119, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_109 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_114 (v1 (vars 0))
private theorem step_pat_109 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_109 vars) (target_pat_109 vars) := by
  unfold target_pat_109
  refine step_chain ?_ (step_pat_114 (v1 (vars 0)))
  dsimp only [pat_109, pat_114, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_143 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_130 (v3 (vars 0 + 1) (vars 1) (vars 2))
private theorem step_pat_143 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_143 vars) (target_pat_143 vars) := by
  unfold target_pat_143
  refine step_chain ?_ (step_pat_130 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_143, pat_130, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_146 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_132 (v3 (vars 0 + 1) (vars 1) (vars 2))
private theorem step_pat_146 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_146 vars) (target_pat_146 vars) := by
  unfold target_pat_146
  refine step_chain ?_ (step_pat_132 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_146, pat_132, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_149 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_134 (v4 (vars 0 + 1) (vars 1) (vars 2) (vars 3))
private theorem step_pat_149 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_149 vars) (target_pat_149 vars) := by
  unfold target_pat_149
  refine step_chain ?_ (step_pat_134 (v4 (vars 0 + 1) (vars 1) (vars 2) (vars 3)))
  dsimp only [pat_149, pat_134, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_52 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_44 (v3 (vars 0 + 1) (vars 1) (vars 2))
private theorem step_pat_52 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_52 vars) (target_pat_52 vars) := by
  unfold target_pat_52
  refine step_chain ?_ (step_pat_44 (v3 (vars 0 + 1) (vars 1) (vars 2)))
  dsimp only [pat_52, pat_44, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_99 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_108 (fun _ => 0)
  | u + 1 => target_pat_109 (v1 u)
private theorem step_pat_99 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_99 vars) (target_pat_99 vars) := by
  unfold target_pat_99
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_108 (fun _ => 0))
    dsimp only [pat_99, pat_108, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_109 (v1 u))
    dsimp only [pat_99, pat_109, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_87 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_99 (v1 1)
  | u + 1 => target_pat_99 (v1 ((u + 1) + 1))
private theorem step_pat_87 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_87 vars) (target_pat_87 vars) := by
  unfold target_pat_87
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_99 (v1 1))
    dsimp only [pat_87, pat_99, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_99 (v1 ((u + 1) + 1)))
    dsimp only [pat_87, pat_99, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_88 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_100 (v1 (vars 0))
private theorem step_pat_88 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_88 vars) (target_pat_88 vars) := by
  unfold target_pat_88
  refine step_chain ?_ (step_pat_100 (v1 (vars 0)))
  dsimp only [pat_88, pat_100, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_78 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_87 (v1 0)
  | u + 1 => target_pat_88 (v1 u)
private theorem step_pat_78 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_78 vars) (target_pat_78 vars) := by
  unfold target_pat_78
  rcases h_vr : vars 0 with _ | u
  · refine step_chain ?_ (step_pat_87 (v1 0))
    dsimp only [pat_78, pat_87, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_88 (v1 u))
    dsimp only [pat_78, pat_88, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_68 (_vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_78 (v1 1)
private theorem step_pat_68 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_68 vars) (target_pat_68 vars) := by
  unfold target_pat_68
  refine step_chain ?_ (step_pat_78 (v1 1))
  dsimp only [pat_68, pat_78, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_69 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_B2 (v3 ((v2 (vars 0) 1) 0) 0 ((v2 (vars 0) 1) 1)))
private theorem step_pat_69 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_69 vars) (target_pat_69 vars) := by
  unfold target_pat_69
  refine step_base_64 (v2 (vars 0) 1) ?_
  dsimp only [pat_69, pat_64, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_79 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_89 (v2 0 (vars 0))
private theorem step_pat_79 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_79 vars) (target_pat_79 vars) := by
  unfold target_pat_79
  refine step_chain ?_ (step_pat_89 (v2 0 (vars 0)))
  dsimp only [pat_79, pat_89, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_70 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_79 (v1 (vars 0))
private theorem step_pat_70 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_70 vars) (target_pat_70 vars) := by
  unfold target_pat_70
  refine step_chain ?_ (step_pat_79 (v1 (vars 0)))
  dsimp only [pat_70, pat_79, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_91 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_103 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_91 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_91 vars) (target_pat_91 vars) := by
  unfold target_pat_91
  refine step_chain ?_ (step_pat_103 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_91, pat_103, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_80 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_90 (v2 0 (vars 1))
  | v + 1 => target_pat_91 (v3 v 0 (vars 1))
private theorem step_pat_80 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_80 vars) (target_pat_80 vars) := by
  unfold target_pat_80
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_90 (v2 0 (vars 1)))
    dsimp only [pat_80, pat_90, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_91 (v3 v 0 (vars 1)))
    dsimp only [pat_80, pat_91, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_71 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_80 (v2 (vars 0) (vars 1))
private theorem step_pat_71 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_71 vars) (target_pat_71 vars) := by
  unfold target_pat_71
  refine step_chain ?_ (step_pat_80 (v2 (vars 0) (vars 1)))
  dsimp only [pat_71, pat_80, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_64 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => match vars 0 with
    | 0 => target_pat_68 (fun _ => 0)
    | v + 1 => target_pat_69 (v1 v)
  | u + 1 => match vars 0 with
    | 0 => target_pat_70 (v1 u)
    | v + 1 => target_pat_71 (v2 v u)
private theorem step_pat_64 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_64 vars) (target_pat_64 vars) := by
  unfold target_pat_64
  rcases h_vr : vars 1 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_68 (fun _ => 0))
      dsimp only [pat_64, pat_68, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_69 (v1 v))
      dsimp only [pat_64, pat_69, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_70 (v1 u))
      dsimp only [pat_64, pat_70, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_71 (v2 v u))
      dsimp only [pat_64, pat_71, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step

private def target_pat_94 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_42 (v2 (vars 0) 1)
  | u + 1 => target_pat_42 (v2 (vars 0) ((u + 1) + 1))
private theorem step_pat_94 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_94 vars) (target_pat_94 vars) := by
  unfold target_pat_94
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_42 (v2 (vars 0) 1))
    dsimp only [pat_94, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_42 (v2 (vars 0) ((u + 1) + 1)))
    dsimp only [pat_94, pat_42, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_95 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_104 (v2 (vars 0) (vars 1))
private theorem step_pat_95 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_95 vars) (target_pat_95 vars) := by
  unfold target_pat_95
  refine step_chain ?_ (step_pat_104 (v2 (vars 0) (vars 1)))
  dsimp only [pat_95, pat_104, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_82 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_94 (v2 (vars 0) 0)
  | u + 1 => target_pat_95 (v2 (vars 0) u)
private theorem step_pat_82 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_82 vars) (target_pat_82 vars) := by
  unfold target_pat_82
  rcases h_vr : vars 1 with _ | u
  · refine step_chain ?_ (step_pat_94 (v2 (vars 0) 0))
    dsimp only [pat_82, pat_94, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step
  · refine step_chain ?_ (step_pat_95 (v2 (vars 0) u))
    dsimp only [pat_82, pat_95, evalTapePattern, evalTapeExpr]; rw [h_vr]; pat_step

private def target_pat_73 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_82 (v2 (vars 0) 1)
private theorem step_pat_73 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_73 vars) (target_pat_73 vars) := by
  unfold target_pat_73
  refine step_chain ?_ (step_pat_82 (v2 (vars 0) 1))
  dsimp only [pat_73, pat_82, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_74 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  some (evalTapePattern pat_B2 (v3 ((v3 (vars 0) (vars 1) 1) 0) ((v3 (vars 0) (vars 1) 1) 1 + 1)
    ((v3 (vars 0) (vars 1) 1) 2)))
private theorem step_pat_74 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_74 vars) (target_pat_74 vars) := by
  unfold target_pat_74
  refine step_base_66 (v3 (vars 0) (vars 1) 1) ?_
  dsimp only [pat_74, pat_66, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_83 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_96 (v3 (vars 0) 0 (vars 1))
private theorem step_pat_83 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_83 vars) (target_pat_83 vars) := by
  unfold target_pat_83
  refine step_chain ?_ (step_pat_96 (v3 (vars 0) 0 (vars 1)))
  dsimp only [pat_83, pat_96, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_75 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_83 (v2 (vars 0) (vars 1))
private theorem step_pat_75 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_75 vars) (target_pat_75 vars) := by
  unfold target_pat_75
  refine step_chain ?_ (step_pat_83 (v2 (vars 0) (vars 1)))
  dsimp only [pat_75, pat_83, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_98 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_107 (v4 (vars 0) (vars 1) (vars 2) (vars 3))
private theorem step_pat_98 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_98 vars) (target_pat_98 vars) := by
  unfold target_pat_98
  refine step_chain ?_ (step_pat_107 (v4 (vars 0) (vars 1) (vars 2) (vars 3)))
  dsimp only [pat_98, pat_107, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_84 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 0 with
  | 0 => target_pat_97 (v3 (vars 1) 0 (vars 2))
  | v + 1 => target_pat_98 (v4 v (vars 1) 0 (vars 2))
private theorem step_pat_84 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_84 vars) (target_pat_84 vars) := by
  unfold target_pat_84
  rcases h_vl : vars 0 with _ | v
  · refine step_chain ?_ (step_pat_97 (v3 (vars 1) 0 (vars 2)))
    dsimp only [pat_84, pat_97, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step
  · refine step_chain ?_ (step_pat_98 (v4 v (vars 1) 0 (vars 2)))
    dsimp only [pat_84, pat_98, evalTapePattern, evalTapeExpr]; rw [h_vl]; pat_step

private def target_pat_76 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  target_pat_84 (v3 (vars 0) (vars 1) (vars 2))
private theorem step_pat_76 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_76 vars) (target_pat_76 vars) := by
  unfold target_pat_76
  refine step_chain ?_ (step_pat_84 (v3 (vars 0) (vars 1) (vars 2)))
  dsimp only [pat_76, pat_84, evalTapePattern, evalTapeExpr]; pat_step

private def target_pat_66 (vars : ℕ → Nat) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 2 with
  | 0 => match vars 0 with
    | 0 => target_pat_73 (v1 (vars 1))
    | v + 1 => target_pat_74 (v2 v (vars 1))
  | u + 1 => match vars 0 with
    | 0 => target_pat_75 (v2 (vars 1) u)
    | v + 1 => target_pat_76 (v3 v (vars 1) u)
private theorem step_pat_66 (vars : ℕ → Nat) :
  ReachesTarget (evalTapePattern pat_66 vars) (target_pat_66 vars) := by
  unfold target_pat_66
  rcases h_vr : vars 2 with _ | u
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_73 (v1 (vars 1)))
      dsimp only [pat_66, pat_73, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_74 (v2 v (vars 1)))
      dsimp only [pat_66, pat_74, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
  · rcases h_vl : vars 0 with _ | v
    · refine step_chain ?_ (step_pat_75 (v2 (vars 1) u))
      dsimp only [pat_66, pat_75, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step
    · refine step_chain ?_ (step_pat_76 (v3 v (vars 1) u))
      dsimp only [pat_66, pat_76, evalTapePattern, evalTapeExpr]; rw [h_vr]; rw [h_vl]; pat_step

/-- Canonical configuration $B_2(a, b, c)$. -/
private def cfg_B2 (a b c : ℕ) : Cfg (Fin 2) (Fin 6) :=
  evalTapePattern pat_B2 (v3 a b c)

private def target_pat_B2 (vars : ℕ → ℕ) : Option (Cfg (Fin 2) (Fin 6)) :=
  match vars 1 with
  | 0 => target_pat_64 (v2 (vars 0) (vars 2))
  | b + 1 => target_pat_66 (v3 (vars 0) b (vars 2))

private theorem step_pat_B2 (vars : ℕ → ℕ) :
    ReachesTarget (evalTapePattern pat_B2 vars) (target_pat_B2 vars) := by
  rcases h_b : vars 1 with _ | b
  · have h_eq : evalTapePattern pat_B2 vars =
        evalTapePattern pat_64 (v2 (vars 0) (vars 2)) := by
      dsimp only [evalTapePattern, pat_B2, pat_64, evalTapeExpr]
      rw [h_b]
      simp only [list_pow_zero, ListBlank.append_nil]
    rw [h_eq]
    refine cast_target ?_ (step_pat_64 _)
    dsimp only [target_pat_B2]
    rw [h_b]
  · have h_eq : evalTapePattern pat_B2 vars =
        evalTapePattern pat_66 (v3 (vars 0) b (vars 2)) := by
      dsimp only [evalTapePattern, pat_B2, pat_66, evalTapeExpr]
      rw [h_b]
      simp only [list_pow_succ, List.cons_append, List.nil_append, ListBlank.append_cons]
    rw [h_eq]
    refine cast_target ?_ (step_pat_66 _)
    dsimp only [target_pat_B2]
    rw [h_b]

private theorem init_reaches_pat_B2 :
    ReachesStar target (init []) (cfg_B2 0 1 2) := by
  dsimp only [cfg_B2, pat_B2, evalTapePattern, evalTapeExpr]
  simp only [list_pow_zero, list_pow_succ, List.cons_append, List.nil_append,
    ListBlank.append_nil, ListBlank.append_cons]
  bb_steps

private theorem init_reaches_ps :
    ∃ cfg₀, ReachesStar target (init []) cfg₀ ∧ IsInPatternSet ps cfg₀ :=
  ⟨cfg_B2 0 1 2, init_reaches_pat_B2,
    in_ps_B2 (v3 0 1 2)⟩

/-- `ps` is a closed accelerated `TapePatternSet` for `target` (Level A). -/
theorem is_closed_pattern_set : IsClosedPatternSet target ps := by
  refine ⟨init_reaches_ps, ?_⟩
  intro cfg h_in
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  rcases h_mem with ⟨⟩ | ⟨_, h_mem⟩
  · exact reachesTarget_to_exists (step_pat_B2 vars)
  · nomatch h_mem

/-- `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE` has a Collatz-like reduction. -/
theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

/-! ## Concrete-Target Acceleration Rules on `cfg_B2` -/

local macro "unfold_targets" : tactic =>
  `(tactic| simp -failIfUnchanged only [cfg_B2, target_pat_B2, target_pat_66, target_pat_76,
    target_pat_84, target_pat_98, target_pat_75, target_pat_83, target_pat_74, target_pat_73,
    target_pat_82,
    target_pat_95, target_pat_94, target_pat_64, target_pat_71, target_pat_80, target_pat_91,
    target_pat_70, target_pat_79, target_pat_69, target_pat_68, target_pat_78, target_pat_88,
    target_pat_87, target_pat_99, target_pat_52, target_pat_149, target_pat_146, target_pat_143,
    target_pat_109, target_pat_114, target_pat_119, target_pat_108, target_pat_113,
    target_pat_118, target_pat_107, target_pat_97, target_pat_106, target_pat_96, target_pat_105,
    target_pat_104, target_pat_112, target_pat_117, target_pat_125, target_pat_134,
    target_pat_148, target_pat_124, target_pat_133, target_pat_147, target_pat_111,
    target_pat_116, target_pat_123, target_pat_132, target_pat_145, target_pat_122,
    target_pat_131, target_pat_144, target_pat_103, target_pat_90, target_pat_102, target_pat_89,
    target_pat_101, target_pat_100, target_pat_110, target_pat_115, target_pat_121,
    target_pat_130, target_pat_142, target_pat_120, target_pat_129, target_pat_141,
    target_pat_128, target_pat_140, target_pat_153, target_pat_159, target_pat_161,
    target_pat_158, target_pat_160, target_pat_139, target_pat_152, target_pat_157,
    target_pat_137, target_pat_127, target_pat_136, target_pat_151, target_pat_155,
    target_pat_126, target_pat_135, target_pat_9, target_pat_14, target_pat_20, target_pat_150,
    target_pat_154, target_pat_19, target_pat_24, target_pat_28, target_pat_31, target_pat_35,
    target_pat_37, target_pat_40, target_pat_44, target_pat_51, target_pat_39, target_pat_43,
    target_pat_50, target_pat_34, target_pat_36, target_pat_38, target_pat_42, target_pat_49,
    target_pat_56, target_pat_60, target_pat_65, target_pat_72, target_pat_81, target_pat_92,
    target_pat_48, target_pat_55, target_pat_59, target_pat_63, target_pat_67, target_pat_77,
    target_pat_85, target_pat_47, target_pat_54, target_pat_58, target_pat_62, target_pat_46,
    target_pat_53, target_pat_57, target_pat_61, target_pat_41, target_pat_25, target_pat_2,
    target_pat_0, target_pat_1, target_pat_3, target_pat_8_pos, target_pat_12_pos])

/-- Rule 1: $B_2(0, b, 0) \vdash^+ B_2(0, 1, 2b + 10)$. -/
private theorem rule_1 (b : ℕ) :
    ReachesPlus target (cfg_B2 0 b 0) (cfg_B2 0 1 (2 * b + 10)) := by
  have h := step_pat_B2 (v3 0 b 0)
  have h_t :
      target_pat_B2 (v3 0 b 0) =
        some (cfg_B2 0 1 (2 * b + 10)) := by
    rcases b with _ | _ | b'
    · rfl
    · rfl
    · unfold_targets
      refine congrArg some (congrArg (evalTapePattern pat_B2) (funext fun k => ?_))
      rcases k with _ | _ | _ | _ | k <;> rfl
  rw [h_t] at h
  exact h.1

/-- Rule 2: $B_2(a + 1, b, 0) \vdash^+ B_2(a, b, 1)$. -/
private theorem rule_2 (a b : ℕ) :
    ReachesPlus target (cfg_B2 (a + 1) b 0) (cfg_B2 a b 1) := by
  have h := step_pat_B2 (v3 (a + 1) b 0)
  have h_t :
      target_pat_B2 (v3 (a + 1) b 0) =
        some (cfg_B2 a b 1) := by
    rcases b with _ | b' <;> rfl
  rw [h_t] at h
  exact h.1

local macro "close_B2_eq" : tactic =>
  `(tactic| (
    unfold_targets
    try (
      (first
       | refine congrArg some (congrArg (evalTapePattern pat_B2) (funext fun k => ?_))
       | refine congrArg (evalTapePattern pat_B2) (funext fun k => ?_))
      rcases k with _ | _ | _ | _ | k <;>
        (first | rfl | (simp -failIfUnchanged only [Nat.add_eq]; omega)))))

/-- Rule 3: $B_2(a, b, 1) \vdash^+ B_2(0, 1, 4a + 2b + 14)$. -/
private theorem rule_3 (a b : ℕ) :
    ReachesPlus target (cfg_B2 a b 1) (cfg_B2 0 1 (4 * a + 2 * b + 14)) := by
  have h := step_pat_B2 (v3 a b 1)
  have h_t :
      target_pat_B2 (v3 a b 1) =
        some (cfg_B2 0 1 (4 * a + 2 * b + 14)) := by
    rcases b with _ | _ | b' <;> rcases a with _ | _ | a' <;> close_B2_eq
  rw [h_t] at h
  exact h.1

/-- Rule 4: $B_2(a, 0, 2) \vdash^+ \text{Halt}$. -/
private theorem rule_4 (a : ℕ) :
    ∃ cfg_h, ReachesPlus target (cfg_B2 a 0 2) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_B2 (v3 a 0 2)
  have h_t : target_pat_B2 (v3 a 0 2) = none := by
    rcases a with _ | _ | a' <;> rfl
  rw [h_t] at h
  exact h

/-- Rule 5: $B_2(a, 0, 3) \vdash^+ \text{Halt}$. -/
private theorem rule_5 (a : ℕ) :
    ∃ cfg_h, ReachesPlus target (cfg_B2 a 0 3) cfg_h ∧ (step target cfg_h).isNone := by
  have h := step_pat_B2 (v3 a 0 3)
  have h_t : target_pat_B2 (v3 a 0 3) = none := by
    rcases a with _ | _ | a' <;> rfl
  rw [h_t] at h
  exact h

/-- Rule 6: $B_2(a, 0, 4) \vdash^+ B_2(0, 1, 2a + 12)$. -/
private theorem rule_6 (a : ℕ) :
    ReachesPlus target (cfg_B2 a 0 4) (cfg_B2 0 1 (2 * a + 12)) := by
  have h := step_pat_B2 (v3 a 0 4)
  have h_t :
      target_pat_B2 (v3 a 0 4) =
        some (cfg_B2 0 1 (2 * a + 12)) := by
    rcases a with _ | _ | a'
    · rfl
    · rfl
    · unfold_targets
      refine congrArg some (congrArg (evalTapePattern pat_B2) (funext fun k => ?_))
      rcases k with _ | _ | _ | _ | k <;> (first | rfl | (simp -failIfUnchanged only []; omega))
  rw [h_t] at h
  exact h.1

/-- Rule 7: $B_2(a, 0, 5) \vdash^+ B_2(0, 1, 2a + 16)$. -/
private theorem rule_7 (a : ℕ) :
    ReachesPlus target (cfg_B2 a 0 5) (cfg_B2 0 1 (2 * a + 16)) := by
  have h := step_pat_B2 (v3 a 0 5)
  have h_t :
      target_pat_B2 (v3 a 0 5) =
        some (cfg_B2 0 1 (2 * a + 16)) := by
    rcases a with _ | _ | a'
    · rfl
    · rfl
    · unfold_targets
      refine congrArg some (congrArg (evalTapePattern pat_B2) (funext fun k => ?_))
      rcases k with _ | _ | _ | _ | k <;> (first | rfl | (simp -failIfUnchanged only []; omega))
  rw [h_t] at h
  exact h.1

/-- Rule 8: $B_2(a, 0, c + 6) \vdash^+ B_2(0, a + 4, c)$. -/
private theorem rule_8 (a c : ℕ) :
    ReachesPlus target (cfg_B2 a 0 (c + 6)) (cfg_B2 0 (a + 4) c) := by
  have h := step_pat_B2 (v3 a 0 (c + 6))
  have h_t :
      target_pat_B2 (v3 a 0 (c + 6)) =
        some (cfg_B2 0 (a + 4) c) := by
    rcases a with _ | _ | a' <;> close_B2_eq
  rw [h_t] at h
  exact h.1

/-- Rule 9: $B_2(a, b + 1, c + 2) \vdash^+ B_2(a + 2, b, c)$. -/
private theorem rule_9 (a b c : ℕ) :
    ReachesPlus target (cfg_B2 a (b + 1) (c + 2)) (cfg_B2 (a + 2) b c) := by
  have h := step_pat_B2 (v3 a (b + 1) (c + 2))
  have h_t :
      target_pat_B2 (v3 a (b + 1) (c + 2)) =
        some (cfg_B2 (a + 2) b c) := by
    rcases b with _ | b' <;> rcases a with _ | _ | a' <;> close_B2_eq
  rw [h_t] at h
  exact h.1

/-! ## Collatz-Like Acceleration (Level B) -/

/-- Symbolic configuration state space for `1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_---0RE`. -/
inductive State where
  /-- $B_2(a, b, c) := 0^\infty\,(10)^b\,11\,(10)^{a+1}\,\mathrm{B}{>}\,1^{c+1}\,0^\infty$. -/
  | B2 (a b c : ℕ)

/-- Initial symbolic state $B_2(0, 1, 2)$, reached after 30 raw TM steps. -/
def start : State := .B2 0 1 2

/-- Decode a symbolic `State` into a concrete Turing machine configuration. -/
def encode : State → Cfg (Fin 2) (Fin 6)
  | .B2 a b c =>
    Cfg.headRight B
      (ListBlank.cons 0 (ListBlank.cons 1
        (ListBlank.append (([0, 1] : List (Fin 2)) ^ a)
          (ListBlank.cons 1 (ListBlank.cons 1
            (ListBlank.append (([0, 1] : List (Fin 2)) ^ b) default))))))
      (ListBlank.cons 1 (ListBlank.append (([1] : List (Fin 2)) ^ c) default))

/-- Accelerated Collatz-like transition function. -/
def next : State → Option State
  | .B2 0 b 0 => some (.B2 0 1 (2 * b + 10))
  | .B2 (a + 1) b 0 => some (.B2 a b 1)
  | .B2 a b 1 => some (.B2 0 1 (4 * a + 2 * b + 14))
  | .B2 _ 0 2 => none
  | .B2 _ 0 3 => none
  | .B2 a 0 4 => some (.B2 0 1 (2 * a + 12))
  | .B2 a 0 5 => some (.B2 0 1 (2 * a + 16))
  | .B2 a 0 (c + 6) => some (.B2 0 (a + 4) c)
  | .B2 a (b + 1) (c + 2) => some (.B2 (a + 2) b c)

/-- `start`, `encode`, and `next` form a valid Collatz-like acceleration of `target`. -/
theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := init_reaches_pat_B2
  step_some := by
    rintro ⟨a, b, c⟩ s' hnext
    rcases c with _ | _ | c
    · rcases a with _ | a
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_1 b
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_2 a b
    · simp only [next, Option.some.injEq] at hnext
      subst hnext
      exact rule_3 a b
    · rcases b with _ | b
      · rcases c with _ | _ | _ | _ | c
        · simp [next] at hnext
        · simp [next] at hnext
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_6 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_7 a
        · simp only [next, Option.some.injEq] at hnext
          subst hnext
          exact rule_8 a c
      · simp only [next, Option.some.injEq] at hnext
        subst hnext
        exact rule_9 a b c
  step_none := by
    rintro ⟨a, b, c⟩ hnext
    rcases c with _ | _ | c
    · rcases a with _ | a <;> simp [next] at hnext
    · simp [next] at hnext
    · rcases b with _ | b
      · rcases c with _ | _ | _ | _ | c
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_4 a
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · obtain ⟨cfg_h, h_reach, h_halt⟩ := rule_5 a
          exact ⟨cfg_h, h_reach.to_star, h_halt⟩
        · simp [next] at hnext
        · simp [next] at hnext
        · simp [next] at hnext
      · simp [next] at hnext

/-- `target` halts from the blank tape if and only if the Collatz-like acceleration `next` halts
from `start`. -/
theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

end BusyBeaver.M_1RB1LC_1RC0LD_1LA0RB_1LB1LE_1RF0LA_HHH0RE
