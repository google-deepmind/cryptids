/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Cert

/-!
# Busy Beaver Holdout `1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD`

We define the configuration for $a, d \ge 0$:

$$
P(a, d) := 0^\infty \ 1111 \ (01)^a \ 1 \ \mathrm{C}{>} \ 011 \ (01)^d \ 1 \ 0^\infty.
$$

Starting from $P(1, 1)$ (reached after 70 steps from the blank tape), the machine follows
the map $T$:

$$
T(P(a, d)) = \begin{cases}
  P(a-d-2, 2d+3) & \text{if } a \ge d+2, \\
  \text{Halt} & \text{if } a = d+1, \\
  P(2a+4, 1) & \text{if } a = d, \\
  P(4a+6, d-3a) & \text{if } a < d \text{ and } 3a+1 \le d, \\
  P(4a+6, 2) & \text{if } a < d < 3a+1 \text{ and } d - a \text{ is even}, \\
  P(4a+6, 1) & \text{if } a < d < 3a+1 \text{ and } d - a \text{ is odd}.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

/-- Variable environment `[a, b, c, d, e, f]` (all other variables `0`) for 6-variable
certificates. -/
private def env6 (a b c d e f : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | 3 => d
  | 4 => e
  | 5 => f
  | _ => 0

private theorem env6_0 (a b c d e f : Nat) : env6 a b c d e f 0 = a := rfl
private theorem env6_1 (a b c d e f : Nat) : env6 a b c d e f 1 = b := rfl
private theorem env6_2 (a b c d e f : Nat) : env6 a b c d e f 2 = c := rfl
private theorem env6_3 (a b c d e f : Nat) : env6 a b c d e f 3 = d := rfl

private theorem congr_cfg3 (f : Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) :
    f a1 b1 c1 = f a2 b2 c2 := by
  subst ha hb hc; rfl

private theorem congr_cfg4 (f : Nat → Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 d1 d2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    f a1 b1 c1 d1 = f a2 b2 c2 d2 := by
  subst ha hb hc hd; rfl

private def hub_1 : Cert.SC :=
  ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [0, 0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

private def hub_2 : Cert.SC :=
  ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

private def hub_3 : Cert.SC :=
  ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩]⟩

private def hub_4 : Cert.SC :=
  ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, [1]⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0,
  1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [0, 0, 0, 1]⟩⟩]⟩

private def hubs : List Cert.SC := [hub_1, hub_2, hub_3, hub_4]

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 (.sym 1 .default))) }

def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 .default) }

def pat_P3 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 .default }

def pat_P4 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [1, 0] 0 (.rep [1] 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.rep [0, 1] 3 .default)) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true), (pat_P3, .true), (pat_P4, .true)]

private def cfg_P1 (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_1.den (env6 a b c d 0 0) default default

private theorem eval_pat_P1 (vars : Nat → Nat) :
    evalTapePattern pat_P1 vars = cfg_P1 (vars 0) (vars 1) (vars 2) (vars 3) :=
  Cert.toPat_eval hub_1 rfl vars

private def cfg_P2 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_2.den (env6 a b c 0 0 0) default default

private theorem eval_pat_P2 (vars : Nat → Nat) :
    evalTapePattern pat_P2 vars = cfg_P2 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_2 rfl vars

private theorem in_ps_P2 (a b c : Nat) : IsInPatternSet ps (cfg_P2 a b c) :=
  Cert.in_hubsPS hubs (by decide) hub_2 (by simp [hubs]) (env6 a b c 0 0 0)

private def cfg_P3 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_3.den (env6 a b c 0 0 0) default default

private theorem eval_pat_P3 (vars : Nat → Nat) :
    evalTapePattern pat_P3 vars = cfg_P3 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_3 rfl vars

private def cfg_P4 (a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_4.den (env6 a b c d 0 0) default default

private theorem eval_pat_P4 (vars : Nat → Nat) :
    evalTapePattern pat_P4 vars = cfg_P4 (vars 0) (vars 1) (vars 2) (vars 3) :=
  Cert.toPat_eval hub_4 rfl vars

private def rdefs : List Cert.RDef := [
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0],
  .prove ⟨⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨1, [0, 1]⟩⟩]⟩, ⟨4, true,
    [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩, true,
    false⟩ [.rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step,
    .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
    .rw true 1 (.pack 2), .rw true 1 .merge, .done],
  .iter 0 ⟨4, true, [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩], [⟨[1, 0], ⟨0, [0, 1]⟩⟩]⟩ 1 [1, 0]
]

private def rule_1_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 2 .splitF, .rw false 2 .unpack, .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 1: `P_1(0, 2b, c, 0) -> P_2(0, 0, b + c + 2)`. -/
private theorem rule_1 (b c : Nat) :
    (cfg_P1 0 (2 * b) c 0) [target]⊢⁺ (cfg_P2 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_2.substAll [⟨0, []⟩,
      ⟨0, []⟩, ⟨2, [0, 1, 1]⟩])
    rule_1_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 0 (2 * b) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_2_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1),
  .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2),
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 2: `P_1(0, 2b + 1, c, 0) -> P_1(b + c, 4, 1, 2)`. -/
private theorem rule_2 (b c : Nat) :
    (cfg_P1 0 (2 * b + 1) c 0) [target]⊢⁺ (cfg_P1 (b + c) 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 1,
      1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_2_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 0 (2 * b + 1) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_3_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw false 0 (.pack 2), .rw false 0 .merge, .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩,
  ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 3: `P_1(1, 0, c, 0) -> P_1(c, 4, 1, 2)`. -/
private theorem rule_3 (c : Nat) :
    (cfg_P1 1 0 c 0) [target]⊢⁺ (cfg_P1 c 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩,
      ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_3_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 0 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_4_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .zdrop, .step, .step, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1),
  .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1),
  .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .done]

set_option maxRecDepth 200000 in
/-- Rule 4: `P_1(1, 1, c, 0) -> P_1(0, 0, 1, c + 2)`. -/
private theorem rule_4 (c : Nat) :
    (cfg_P1 1 1 c 0) [target]⊢⁺ (cfg_P1 0 0 1 (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, []⟩, ⟨0,
      []⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩])
    rule_4_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 1 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨1, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 0 0 1 (c + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_5_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .splitF, .step, .rw true 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .rw true 1 .merge, .rw true 1 (.zins [1, 0]), .rw false 3 .splitF,
  .rw false 3 .unpack, .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 4 (.pack 2), .rw false 4 .merge, .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 5: `P_1(1, 2, c, 0) -> P_2(0, 2, c + 3)`. -/
private theorem rule_5 (c : Nat) :
    (cfg_P1 1 2 c 0) [target]⊢⁺ (cfg_P2 0 2 (c + 3)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_2.substAll [⟨0, []⟩, ⟨2,
      []⟩, ⟨3, [0, 0, 1]⟩])
    rule_5_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 1 2 c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨2, []⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P2 0 2 (c + 3) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_6_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨0, [0, 1]⟩⟩], [⟨[0], ⟨1, []⟩⟩,
  ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_6_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 .splitF, .step, .rw true 0 .splitF, .done]

/-- Rule 6 (Halting): `P_1(1, b + 3, c, 0) -> Halt`. -/
private theorem rule_6_halt (b c : Nat) :
    ∃ cfg', ((cfg_P1 1 (b + 3) c 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_1.substAll [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) rule_6_rhs
    rule_6_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_1.substAll [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 1 (b + 3) c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨3, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_6_rhs.den (env6 0 b c 0 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_7_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .step, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 7: `P_1(a + 2, b, c, 0) -> P_1(a, b, 1, c + 2)`. -/
private theorem rule_7 (a b c : Nat) :
    (cfg_P1 (a + 2) b c 0) [target]⊢⁺ (cfg_P1 a b 1 (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [1]⟩,
      ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩])
    rule_7_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 a b c 0 0 0) default default = cfg_P1 (a + 2) b c 0 :=
    (Cert.SC.den_substAll hub_1 [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P1 a b 1 (c + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_8_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩]⟩
private def rule_8_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 8 (Halting): `P_1(0, 0, 0, d + 1) -> Halt`. -/
private theorem rule_8_halt (d : Nat) :
    ∃ cfg', ((cfg_P1 0 0 0 (d + 1)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0, 1]⟩]) rule_8_rhs
    rule_8_pf rfl (env6 0 0 0 d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 0 d 0 0) default default = cfg_P1 0 0 0 (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 0 d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rw [hL] at h_tr
  exact ⟨rule_8_rhs.den (env6 0 0 0 d 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_9_pf : List Cert.Ins :=
  [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 9: `P_1(0, 0, c + 1, d + 1) -> P_4(c, 4, 1, d + 2)`. -/
private theorem rule_9 (c d : Nat) :
    (cfg_P1 0 0 (c + 1) (d + 1)) [target]⊢⁺ (cfg_P4 c 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩]) (hub_4.substAll [⟨0,
      [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_9_pf rfl (env6 0 0 c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P1 0 0 (c + 1) (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P4 c 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_4 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_10_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .rw false 0 (.pack 2), .rw false 0 .merge, .shift, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 10: `P_1(0, 2b + 2, c, d + 1) -> P_4(b + c, 4, 1, d + 2)`. -/
private theorem rule_10 (b c d : Nat) :
    (cfg_P1 0 (2 * b + 2) c (d + 1)) [target]⊢⁺ (cfg_P4 (b + c) 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_10_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 (2 * b + 2) c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 (b + c) 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_4 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_11_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

set_option maxRecDepth 200000 in
/-- Rule 11: `P_1(0, 2b + 1, c, d + 1) -> P_1(0, 0, b + c + 2, d)`. -/
private theorem rule_11 (b c d : Nat) :
    (cfg_P1 0 (2 * b + 1) c (d + 1)) [target]⊢⁺ (cfg_P1 0 0 (b + c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_11_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 (2 * b + 1) c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 0 0 (b + c + 2) d :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_12_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 12: `P_1(a + 1, b, c, d + 1) -> P_1(a, b, c + 2, d)`. -/
private theorem rule_12 (a b c d : Nat) :
    (cfg_P1 (a + 1) b c (d + 1)) [target]⊢⁺ (cfg_P1 a b (c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_12_pf rfl (env6 a b c d 0 0)
  have hL : (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P1 (a + 1) b c (d + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P1 a b (c + 2) d :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_13_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_13_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, []⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, []⟩, ⟨1, []⟩],
  .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 13 (Halting): `P_2(0, 0, 0) -> Halt`. -/
private theorem rule_13_halt :
    ∃ cfg', ((cfg_P2 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_13_rhs
    rule_13_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P2 0 0 0 :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_13_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_14_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, []⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, []⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .done]

/-- Rule 14: `P_2(0, 0, c + 1) -> P_1(c, 4, 1, 1)`. -/
private theorem rule_14 (c : Nat) :
    (cfg_P2 0 0 (c + 1)) [target]⊢⁺ (cfg_P1 c 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩,
      ⟨1, []⟩, ⟨1, []⟩])
    rule_14_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P2 0 0 (c + 1) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_15_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .done]

set_option maxRecDepth 200000 in
/-- Rule 15: `P_2(0, 2b + 2, c) -> P_1(b + c, 4, 1, 1)`. -/
private theorem rule_15 (b c : Nat) :
    (cfg_P2 0 (2 * b + 2) c) [target]⊢⁺ (cfg_P1 (b + c) 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4,
      []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_15_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 (2 * b + 2) c :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_16_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step, .rw true 0 (.group 2),
  .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 16: `P_2(0, 2b + 1, c) -> P_3(0, 0, b + c + 2)`. -/
private theorem rule_16 (b c : Nat) :
    (cfg_P2 0 (2 * b + 1) c) [target]⊢⁺ (cfg_P3 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩,
      ⟨2, [0, 1, 1]⟩])
    rule_16_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_2.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 (2 * b + 1) c :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_17_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 17: `P_2(a + 1, b, c) -> P_3(a, b, c + 2)`. -/
private theorem rule_17 (a b c : Nat) :
    (cfg_P2 (a + 1) b c) [target]⊢⁺ (cfg_P3 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩]) (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0,
      1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_17_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_2.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P2 (a + 1) b c :=
    (Cert.SC.den_substAll hub_2 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 a b (c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_18_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_18_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop, .step, .done]

/-- Rule 18 (Halting): `P_3(0, 0, 0) -> Halt`. -/
private theorem rule_18_halt :
    ∃ cfg', ((cfg_P3 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_18_rhs
    rule_18_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P3 0 0 0 :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_18_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_19_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 19: `P_3(0, 0, c + 1) -> P_1(c, 4, 1, 2)`. -/
private theorem rule_19 (c : Nat) :
    (cfg_P3 0 0 (c + 1)) [target]⊢⁺ (cfg_P1 c 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩,
      ⟨1, []⟩, ⟨2, []⟩])
    rule_19_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
    1]⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P3 0 0 (c + 1) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0,
      1]⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_20_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .done]

/-- Rule 20: `P_3(0, 2b + 2, c) -> P_1(b + c, 4, 1, 2)`. -/
private theorem rule_20 (b c : Nat) :
    (cfg_P3 0 (2 * b + 2) c) [target]⊢⁺ (cfg_P1 (b + c) 4 1 2) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4,
      []⟩, ⟨1, []⟩, ⟨2, []⟩])
    rule_20_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 (2 * b + 2) c :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 2 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_21_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 21: `P_3(0, 2b + 1, c) -> P_2(0, 0, b + c + 2)`. -/
private theorem rule_21 (b c : Nat) :
    (cfg_P3 0 (2 * b + 1) c) [target]⊢⁺ (cfg_P2 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩]) (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩,
      ⟨2, [0, 1, 1]⟩])
    rule_21_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_3.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 (2 * b + 1) c :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_2.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P2 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_22_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 22: `P_3(a + 1, b, c) -> P_2(a, b, c + 2)`. -/
private theorem rule_22 (a b c : Nat) :
    (cfg_P3 (a + 1) b c) [target]⊢⁺ (cfg_P2 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_3.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩]) (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0,
      1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_22_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_3.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 (a + 1) b c :=
    (Cert.SC.den_substAll hub_3 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P2 a b (c + 2) :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_23_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_23_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .step, .done]

/-- Rule 23 (Halting): `P_4(0, 0, 0, 0) -> Halt`. -/
private theorem rule_23_halt :
    ∃ cfg', ((cfg_P4 0 0 0 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩]) rule_23_rhs
    rule_23_pf rfl (env6 0 0 0 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0,
    []⟩]).den (env6 0 0 0 0 0 0) default default = cfg_P4 0 0 0 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨0,
      []⟩] (env6 0 0 0 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_23_rhs.den (env6 0 0 0 0 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_24_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2),
  .rw false 0 (.pack 2), .done]

/-- Rule 24: `P_4(0, 0, c + 1, 0) -> P_1(c, 4, 1, 1)`. -/
private theorem rule_24 (c : Nat) :
    (cfg_P4 0 0 (c + 1) 0) [target]⊢⁺ (cfg_P1 c 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 0, 1]⟩,
      ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_24_pf rfl (env6 0 0 c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P4 0 0 (c + 1) 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 0 c 0 0 0) default default = cfg_P1 c 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 0 c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_25_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2),
  .rw false 0 (.pack 2), .done]

/-- Rule 25: `P_4(0, 2b + 2, c, 0) -> P_1(b + c, 4, 1, 1)`. -/
private theorem rule_25 (b c : Nat) :
    (cfg_P4 0 (2 * b + 2) c 0) [target]⊢⁺ (cfg_P1 (b + c) 4 1 1) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨0, [0, 1,
      1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩])
    rule_25_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P4 0 (2 * b + 2) c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P1 (b + c) 4 1 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        rfl)
  rwa [hL, hR] at h_tr

private def rule_26_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop, .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 26: `P_4(0, 2b + 1, c, 0) -> P_3(0, 0, b + c + 2)`. -/
private theorem rule_26 (b c : Nat) :
    (cfg_P4 0 (2 * b + 1) c 0) [target]⊢⁺ (cfg_P3 0 0 (b + c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_3.substAll [⟨0, []⟩,
      ⟨0, []⟩, ⟨2, [0, 1, 1]⟩])
    rule_26_pf rfl (env6 0 b c 0 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 0 b c 0 0 0) default default = cfg_P4 0 (2 * b + 1) c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_3.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
    1]⟩]).den (env6 0 b c 0 0 0) default default = cfg_P3 0 0 (b + c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1,
      1]⟩] (env6 0 b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_27_pf : List Cert.Ins := [.shift, .step, .rw false 0 .zdrop, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 27: `P_4(a + 1, b, c, 0) -> P_3(a, b, c + 2)`. -/
private theorem rule_27 (a b c : Nat) :
    (cfg_P4 (a + 1) b c 0) [target]⊢⁺ (cfg_P3 a b (c + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0, []⟩]) (hub_3.substAll [⟨0, [1]⟩,
      ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩])
    rule_27_pf rfl (env6 a b c 0 0 0)
  have hL : (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
    []⟩]).den (env6 a b c 0 0 0) default default = cfg_P4 (a + 1) b c 0 :=
    (Cert.SC.den_substAll hub_4 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨0,
      []⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl)
  have hR : (hub_3.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
    1]⟩]).den (env6 a b c 0 0 0) default default = cfg_P3 a b (c + 2) :=
    (Cert.SC.den_substAll hub_3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0,
      1]⟩] (env6 a b c 0 0 0) default default)
      |>.trans (congr_cfg3 cfg_P3
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_28_rhs : Cert.SC :=
  ⟨0, false, [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 0, 0, 1]⟩⟩, ⟨[1],
  ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_28_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨1, []⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .zdrop,
  .step, .done]

/-- Rule 28 (Halting): `P_4(0, 0, 0, d + 1) -> Halt`. -/
private theorem rule_28_halt (d : Nat) :
    ∃ cfg', ((cfg_P4 0 0 0 (d + 1)) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0, 1]⟩]) rule_28_rhs
    rule_28_pf rfl (env6 0 0 0 d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 0 d 0 0) default default = cfg_P4 0 0 0 (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 0 d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rw [hL] at h_tr
  exact ⟨rule_28_rhs.den (env6 0 0 0 d 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_29_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, []⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2),
  .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 29: `P_4(0, 0, c + 1, d + 1) -> P_1(c, 4, 1, d + 2)`. -/
private theorem rule_29 (c d : Nat) :
    (cfg_P4 0 0 (c + 1) (d + 1)) [target]⊢⁺ (cfg_P1 c 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0, 1]⟩]) (hub_1.substAll [⟨0,
      [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_29_pf rfl (env6 0 0 c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P4 0 0 (c + 1) (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨1, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 0 c d 0 0) default default = cfg_P1 c 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 0 c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_30_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨1, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .rw false 0 (.pack 2), .rw false 0 .merge, .shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .done]

/-- Rule 30: `P_4(0, 2b + 2, c, d + 1) -> P_1(b + c, 4, 1, d + 2)`. -/
private theorem rule_30 (b c d : Nat) :
    (cfg_P4 0 (2 * b + 2) c (d + 1)) [target]⊢⁺ (cfg_P1 (b + c) 4 1 (d + 2)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩])
    rule_30_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 (2 * b + 2) c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨2, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_1.substAll [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P1 (b + c) 4 1 (d + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_31_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .zdrop,
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 31: `P_4(0, 2b + 1, c, d + 1) -> P_4(0, 0, b + c + 2, d)`. -/
private theorem rule_31 (b c d : Nat) :
    (cfg_P4 0 (2 * b + 1) c (d + 1)) [target]⊢⁺ (cfg_P4 0 0 (b + c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_31_pf rfl (env6 0 b c d 0 0)
  have hL : (hub_4.substAll [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 (2 * b + 1) c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨1, [0, 2]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 0 b c d 0 0) default default = cfg_P4 0 0 (b + c + 2) d :=
    (Cert.SC.den_substAll hub_4 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 0 b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

private def rule_32_pf : List Cert.Ins := [.shift, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 32: `P_4(a + 1, b, c, d + 1) -> P_4(a, b, c + 2, d)`. -/
private theorem rule_32 (a b c d : Nat) :
    (cfg_P4 (a + 1) b c (d + 1)) [target]⊢⁺ (cfg_P4 a b (c + 2) d) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩]) (hub_4.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩])
    rule_32_pf rfl (env6 a b c d 0 0)
  have hL : (hub_4.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P4 (a + 1) b c (d + 1) :=
    (Cert.SC.den_substAll hub_4 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩, ⟨1, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  have hR : (hub_4.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
    1]⟩]).den (env6 a b c d 0 0) default default = cfg_P4 a b (c + 2) d :=
    (Cert.SC.den_substAll hub_4 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0,
      1]⟩] (env6 a b c d 0 0) default default)
      |>.trans (congr_cfg4 cfg_P4
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env6_0,
          env6_1, env6_2, env6_3]; omega))
  rwa [hL, hR] at h_tr

/-! ## Blank-Tape Entry and Closure of `ps` (Level A) -/

private def init_pf : List Cert.Ins :=
  [.step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 2 (.pack 2),
  .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Blank initial tape `init []` reaches `cfg_P2 0 0 2` in 12 concrete steps. -/
private theorem init_reaches_P2 : (init []) [target]⊢* (cfg_P2 0 0 2) :=
  Cert.checkInit_sound target rdefs ⟨2, true, [⟨[1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, []⟩⟩, ⟨[1], ⟨0,
    []⟩⟩], [⟨[0, 1], ⟨2, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩ init_pf rfl (env6 0 0 0 0 0 0)

private def hub_1_pf : List Cert.Ins := [.shift, .step, .splitZ 3, .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2),
  .rw true 0 .merge, .shift, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 2 .splitF, .rw false 2 .unpack, .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩],
  .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨2, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2),
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 0,
  .rw true 0 .zdrop, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge,
  .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩],
  .rw true 0 .splitF, .step, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step,
  .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, []⟩, ⟨0, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩],
  .rw true 0 .splitF, .step, .splitZ 1, .rw true 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .rw true 1 .merge, .rw true 1 (.zins [1, 0]), .rw false 3 .splitF,
  .rw false 3 .unpack, .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 4 (.pack 2), .rw false 4 .merge, .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 1 [⟨0, []⟩, ⟨2, []⟩, ⟨3, [0, 0, 1]⟩],
  .rw true 0 .splitF, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .step,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨1, []⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .shift,
  .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1),
  .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF,
  .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge,
  .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2), .hub 3 [⟨0, [0, 0, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 3 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF, .step,
  .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 5 (.rotB 1), .rw false 5 (.rot 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge,
  .rw false 0 (.pack 2), .rw false 0 .merge, .hub 0 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0,
  0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 0 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 1 (`cfg_P1 a b c d`) across all `(a b c d) ∈ ℕ^4`. -/
private theorem step_P1_all (a b c d : Nat) :
    ∃ cfg', ((cfg_P1 a b c d) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_1 hub_1_pf rfl (env6 a b c d 0 0)

private def hub_2_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .rw true 0 (.rotB 1),
  .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge,
  .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4,
  []⟩, ⟨1, []⟩, ⟨1, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
  []⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 2 (`cfg_P2 a b c`) across all `(a b c) ∈ ℕ^3`. -/
private theorem step_P2_all (a b c : Nat) :
    ∃ cfg', ((cfg_P2 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_2 hub_2_pf rfl (env6 a b c 0 0 0)

private def hub_3_pf : List Cert.Ins := [.shift, .step, .step, .step, .step, .step, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2,
  .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge,
  .rw true 2 .merge, .rw false 5 (.pack 2), .rw false 3 (.pack 2), .rw false 3 .merge,
  .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, []⟩], .rw true 0 .splitF,
  .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge,
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 1 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 1 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 3 (`cfg_P3 a b c`) across all `(a b c) ∈ ℕ^3`. -/
private theorem step_P3_all (a b c : Nat) :
    ∃ cfg', ((cfg_P3 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_3 hub_3_pf rfl (env6 a b c 0 0 0)

private def hub_4_pf : List Cert.Ins := [.shift, .step, .splitZ 3, .rw false 0 .zdrop, .step, .step,
  .step, .rw true 0 (.rotB 1), .shift, .step, .step, .splitZ 0, .rw true 0 .zdrop, .splitM 1 2,
  .rw true 0 (.group 2), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 0 (.rot 1), .step, .step, .rw false 0 (.rotB 1), .rw true 1 (.zins [0,
  1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩], .rw false 0 .zdrop, .rw false 0 (.pack 2),
  .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0, 1]⟩], .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 0 .splitF, .rw true 0 .unpack,
  .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop, .step, .halt, .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0,
  [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1, []⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step,
  .step, .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 3 (.pack 2), .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨1,
  []⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step, .rw true 1 (.zins [1]),
  .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 .merge, .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1),
  .rw false 0 (.rotB 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩], .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .splitZ 0, .rw true 0 .zdrop, .splitM 1 2, .rw true 0 (.group 2), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw false 0 (.rot 1), .step, .step,
  .rw false 0 (.rotB 1), .rw true 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨0, [0, 1]⟩],
  .rw false 0 .zdrop, .rw false 0 (.pack 2), .rw false 0 .merge, .app 1 [⟨0, [0, 1]⟩, ⟨1, [0, 0,
  1]⟩], .rw false 0 .zdrop, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .shift,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .splitZ 1, .splitZ 2, .rw true 0 .zdrop,
  .step, .halt, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw true 1 (.rotB 1), .rw true 4 .merge, .rw true 3 .merge, .rw true 2 .merge,
  .rw false 4 .splitF, .rw false 4 .unpack, .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 5 (.pack 2),
  .rw false 5 .merge, .rw false 3 (.pack 2), .rw false 3 .merge, .rw false 0 (.pack 2),
  .hub 0 [⟨0, [0, 0, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0, 0, 1]⟩], .rw true 0 .splitF,
  .rw true 0 .unpack, .step, .step, .step, .rw true 1 (.rotB 1), .rw true 4 .merge,
  .rw true 3 .merge, .rw true 2 .merge, .rw false 4 .splitF, .rw false 4 .unpack,
  .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1), .rw false 2 (.rotB 1),
  .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1), .rw false 5 (.rot 1),
  .rw false 6 (.rot 1), .rw false 5 (.pack 2), .rw false 5 .merge, .rw false 3 (.pack 2),
  .rw false 3 .merge, .rw false 0 (.pack 2), .hub 0 [⟨0, [0, 1, 1]⟩, ⟨4, []⟩, ⟨1, []⟩, ⟨2, [0, 0,
  0, 1]⟩], .rw true 0 .splitF, .step, .rw true 0 (.group 2), .shift, .step,
  .rw true 1 (.zins [1]), .rw true 1 (.zins [1, 0]), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 .merge, .rw false 5 (.rotB 1),
  .rw false 5 (.rot 1), .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
  .rw false 3 (.rot 1), .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2),
  .rw false 0 .merge, .hub 3 [⟨0, []⟩, ⟨0, []⟩, ⟨2, [0, 1, 1]⟩, ⟨0, [0, 0, 0, 1]⟩],
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .rw false 2 (.rotB 1),
  .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 5 (.rotB 1), .rw false 5 (.rot 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 3 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨2, [0, 0, 1]⟩, ⟨0, [0, 0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 4 (`cfg_P4 a b c d`) across all `(a b c d) ∈ ℕ^4`. -/
private theorem step_P4_all (a b c d : Nat) :
    ∃ cfg', ((cfg_P4 a b c d) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_4 hub_4_pf rfl (env6 a b c d 0 0)

private theorem step_all (cfg : Cfg (Fin 2) (Fin 6)) (h_in : IsInPatternSet ps cfg) :
    ∃ cfg', ((cfg) [target]⊢⁺ cfg') ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl | rfl | rfl
  · rw [eval_pat_P1 vars]
    exact step_P1_all (vars 0) (vars 1) (vars 2) (vars 3)
  · rw [eval_pat_P2 vars]
    exact step_P2_all (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_P3 vars]
    exact step_P3_all (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_P4 vars]
    exact step_P4_all (vars 0) (vars 1) (vars 2) (vars 3)

theorem is_closed_pattern_set : IsClosedPatternSet target ps :=
  ⟨⟨cfg_P2 0 0 2, init_reaches_P2, in_ps_P2 0 0 2⟩, step_all⟩

theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

inductive State where
  | P_1 (a b c d : ℕ)
  | P_2 (a b c : ℕ)
  | P_3 (a b c : ℕ)
  | P_4 (a b c d : ℕ)
  deriving DecidableEq, Repr

def start : State := .P_2 0 0 2

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a b c d => evalTapePattern pat_P1 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0
  | .P_2 a b c => evalTapePattern pat_P2 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 0
  | .P_3 a b c => evalTapePattern pat_P3 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else 0
  | .P_4 a b c d => evalTapePattern pat_P4 fun i =>
      if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0

private theorem encode_P1 (a b c d : ℕ) : encode (.P_1 a b c d) = cfg_P1 a b c d :=
  eval_pat_P1 fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0

private theorem encode_P2 (a b c : ℕ) : encode (.P_2 a b c) = cfg_P2 a b c :=
  eval_pat_P2 fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0

private theorem encode_P3 (a b c : ℕ) : encode (.P_3 a b c) = cfg_P3 a b c :=
  eval_pat_P3 fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0

private theorem encode_P4 (a b c d : ℕ) : encode (.P_4 a b c d) = cfg_P4 a b c d :=
  eval_pat_P4 fun i =>
    if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else 0

def next : State → Option State
  | .P_1 0 b c 0 =>
    if b % 2 = 0 then some (.P_2 0 0 (b / 2 + c + 2))
    else some (.P_1 (b / 2 + c) 4 1 2)
  | .P_1 1 0 c 0 => some (.P_1 c 4 1 2)
  | .P_1 1 1 c 0 => some (.P_1 0 0 1 (c + 2))
  | .P_1 1 2 c 0 => some (.P_2 0 2 (c + 3))
  | .P_1 1 (_ + 3) _ 0 => none
  | .P_1 (a + 2) b c 0 => some (.P_1 a b 1 (c + 2))
  | .P_1 0 0 0 (_ + 1) => none
  | .P_1 0 0 (c + 1) (d + 1) => some (.P_4 c 4 1 (d + 2))
  | .P_1 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_4 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_1 0 0 (b' / 2 + c + 2) d)
  | .P_1 (a + 1) b c (d + 1) => some (.P_1 a b (c + 2) d)
  | .P_2 0 0 0 => none
  | .P_2 0 0 (c + 1) => some (.P_1 c 4 1 1)
  | .P_2 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_2 (a + 1) b c => some (.P_3 a b (c + 2))
  | .P_3 0 0 0 => none
  | .P_3 0 0 (c + 1) => some (.P_1 c 4 1 2)
  | .P_3 0 (b' + 1) c =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 2)
    else some (.P_2 0 0 (b' / 2 + c + 2))
  | .P_3 (a + 1) b c => some (.P_2 a b (c + 2))
  | .P_4 0 0 0 0 => none
  | .P_4 0 0 (c + 1) 0 => some (.P_1 c 4 1 1)
  | .P_4 0 (b' + 1) c 0 =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 1)
    else some (.P_3 0 0 (b' / 2 + c + 2))
  | .P_4 (a + 1) b c 0 => some (.P_3 a b (c + 2))
  | .P_4 0 0 0 (_ + 1) => none
  | .P_4 0 0 (c + 1) (d + 1) => some (.P_1 c 4 1 (d + 2))
  | .P_4 0 (b' + 1) c (d + 1) =>
    if (b' + 1) % 2 = 0 then some (.P_1 (b' / 2 + c) 4 1 (d + 2))
    else some (.P_4 0 0 (b' / 2 + c + 2) d)
  | .P_4 (a + 1) b c (d + 1) => some (.P_4 a b (c + 2) d)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone = true
  | .P_1 0 b c 0 => by
    simp only [next]
    split_ifs with h
    · have h_r := rule_1 (b / 2) c
      have hb : 2 * (b / 2) = b := by omega
      rw [hb] at h_r
      simp only [encode_P1, encode_P2]
      exact h_r
    · have h_r := rule_2 (b / 2) c
      have hb : 2 * (b / 2) + 1 = b := by omega
      rw [hb] at h_r
      simp only [encode_P1]
      exact h_r
  | .P_1 1 0 c 0 => by simp only [next, encode_P1]; exact rule_3 c
  | .P_1 1 1 c 0 => by simp only [next, encode_P1]; exact rule_4 c
  | .P_1 1 2 c 0 => by simp only [next, encode_P1, encode_P2]; exact rule_5 c
  | .P_1 1 (b + 3) c 0 => by
    simp only [next, encode_P1]
    rcases rule_6_halt b c with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_1 (a + 2) b c 0 => by simp only [next, encode_P1]; exact rule_7 a b c
  | .P_1 0 0 0 (d + 1) => by
    simp only [next, encode_P1]
    rcases rule_8_halt d with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_1 0 0 (c + 1) (d + 1) => by simp only [next, encode_P1, encode_P4]; exact rule_9 c d
  | .P_1 0 (b' + 1) c (d + 1) => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P1, encode_P4, hb]
      exact rule_10 (b' / 2) c d
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P1, hb]
      exact rule_11 (b' / 2) c d
  | .P_1 (a + 1) b c (d + 1) => by simp only [next, encode_P1]; exact rule_12 a b c d
  | .P_2 0 0 0 => by
    simp only [next, encode_P2]
    rcases rule_13_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_2 0 0 (c + 1) => by simp only [next, encode_P2, encode_P1]; exact rule_14 c
  | .P_2 0 (b' + 1) c => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P2, encode_P1, hb]
      exact rule_15 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P2, encode_P3, hb]
      exact rule_16 (b' / 2) c
  | .P_2 (a + 1) b c => by simp only [next, encode_P2, encode_P3]; exact rule_17 a b c
  | .P_3 0 0 0 => by
    simp only [next, encode_P3]
    rcases rule_18_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_3 0 0 (c + 1) => by simp only [next, encode_P3, encode_P1]; exact rule_19 c
  | .P_3 0 (b' + 1) c => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P3, encode_P1, hb]
      exact rule_20 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P3, encode_P2, hb]
      exact rule_21 (b' / 2) c
  | .P_3 (a + 1) b c => by simp only [next, encode_P3, encode_P2]; exact rule_22 a b c
  | .P_4 0 0 0 0 => by
    simp only [next, encode_P4]
    rcases rule_23_halt with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_4 0 0 (c + 1) 0 => by simp only [next, encode_P4, encode_P1]; exact rule_24 c
  | .P_4 0 (b' + 1) c 0 => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P4, encode_P1, hb]
      exact rule_25 (b' / 2) c
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P4, encode_P3, hb]
      exact rule_26 (b' / 2) c
  | .P_4 (a + 1) b c 0 => by simp only [next, encode_P4, encode_P3]; exact rule_27 a b c
  | .P_4 0 0 0 (d + 1) => by
    simp only [next, encode_P4]
    rcases rule_28_halt d with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_4 0 0 (c + 1) (d + 1) => by simp only [next, encode_P4, encode_P1]; exact rule_29 c d
  | .P_4 0 (b' + 1) c (d + 1) => by
    simp only [next]
    split_ifs with h
    · have hb : b' + 1 = 2 * (b' / 2) + 2 := by omega
      simp only [encode_P4, encode_P1, hb]
      exact rule_30 (b' / 2) c d
    · have hb : b' + 1 = 2 * (b' / 2) + 1 := by omega
      simp only [encode_P4, hb]
      exact rule_31 (b' / 2) c d
  | .P_4 (a + 1) b c (d + 1) => by simp only [next, encode_P4]; exact rule_32 a b c d

theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := by
    dsimp [start]
    rw [encode_P2]
    exact init_reaches_P2
  step_some s s' hnext := by
    have h := step_state s
    rw [hnext] at h
    exact h
  step_none s hnext := by
    have h := step_state s
    rw [hnext] at h
    exact h

theorem isHalt_iff_acceleration : IsHalt target ↔ CollatzHalts next start :=
  is_valid_acceleration.isHalt_iff

/-! ## High-Level Collatz-Like Acceleration -/

/-- Single-family state space
$P(a, d) := 0^\infty\,1111\,(01)^a\,1\,\mathrm{C}{>}\,011\,(01)^d\,1\,0^\infty$
for the high-level Collatz-like acceleration. -/
inductive HighLevelState where
  /-- $P(a, d) := 0^\infty\,1111\,(01)^a\,1\,\mathrm{C}{>}\,011\,(01)^d\,1\,0^\infty$. -/
  | P (a d : ℕ)
  deriving DecidableEq, Repr

/-- Initial state $P(1, 1)$ for the high-level Collatz-like acceleration. -/
def highLevelStart : HighLevelState := .P 1 1

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .P a d => .P_1 a 4 1 d

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

/-- High-level accelerated Collatz-like transition function on $P(a, d)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .P a d =>
    if a ≥ d + 2 then some (.P (a - d - 2) (2 * d + 3))
    else if a = d + 1 then none
    else if a = d then some (.P (2 * a + 4) 1)
    else if 3 * a + 1 ≤ d then some (.P (4 * a + 6) (d - 3 * a))
    else if (d - a) % 2 = 0 then some (.P (4 * a + 6) 2)
    else some (.P (4 * a + 6) 1)

private def evalP23_4 : Bool → ℕ → ℕ → HighLevelState
  | false, 0, c => .P (1 + c) 1
  | true, 0, c => .P (1 + c) 2
  | false, a + 1, c => evalP23_4 true a (c + 2)
  | true, a + 1, c => evalP23_4 false a (c + 2)

private def evalP4_4 : ℕ → ℕ → ℕ → HighLevelState
  | 0, c, 0 => .P (1 + c) 1
  | a + 1, c, 0 => evalP23_4 true a (c + 2)
  | 0, c, d + 1 => .P (1 + c) (d + 2)
  | a + 1, c, d + 1 => evalP4_4 a (c + 2) d

private theorem evalP23_4_eq (isP3 : Bool) (a c : ℕ) :
    evalP23_4 isP3 a c =
      .P (2 * a + c + 1) (if (if isP3 then a % 2 = 0 else a % 2 = 1) then 2 else 1) := by
  induction a generalizing isP3 c with
  | zero => cases isP3 <;> simp [evalP23_4, Nat.add_comm]
  | succ a ih =>
    cases isP3
    · rw [evalP23_4, ih true (c + 2)]
      congr 1
      · omega
      · have : (a % 2 = 0) ↔ ((a + 1) % 2 = 1) := by omega
        simp [this]
    · rw [evalP23_4, ih false (c + 2)]
      congr 1
      · omega
      · have : (a % 2 = 1) ↔ ((a + 1) % 2 = 0) := by omega
        simp [this]

private theorem evalP4_4_eq (a c d : ℕ) :
    evalP4_4 a c d =
      if a ≤ d then .P (2 * a + c + 1) (d - a + 1)
      else if (a - d) % 2 = 1 then .P (2 * a + c + 1) 2
      else .P (2 * a + c + 1) 1 := by
  induction a generalizing c d with
  | zero =>
    cases d <;> simp [evalP4_4] <;> omega
  | succ a ih =>
    cases d with
    | zero =>
      rw [evalP4_4, evalP23_4_eq]
      simp only [↓reduceIte]
      split_ifs <;> congr 1 <;> omega
    | succ d =>
      rw [evalP4_4, ih (c + 2) d]
      split_ifs <;> congr 1 <;> omega

private theorem reaches_P1_diag (k : ℕ) (a b c d : ℕ) :
    CollatzReachesStar next (.P_1 (a + k) b c (d + k)) (.P_1 a b (c + 2 * k) d) := by
  induction k generalizing c with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.P_1 (a + (k + 1)) b c (d + (k + 1))) =
        some (.P_1 (a + k) b (c + 2) (d + k)) := by
      have h1 : a + (k + 1) = (a + k) + 1 := by omega
      have h2 : d + (k + 1) = (d + k) + 1 := by omega
      rw [h1, h2]
      simp [next]
    have ih' := ih (c + 2)
    have hc : c + 2 + 2 * k = c + 2 * (k + 1) := by omega
    rw [hc] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem stepsTo_P23_4 : ∀ (isP3 : Bool) (a c : ℕ),
    CollatzStepsTo next (if isP3 then .P_3 a 4 c else .P_2 a 4 c)
      (some (toState (evalP23_4 isP3 a c)))
  | false, 0, _ => CollatzStepsTo.of_eq rfl
  | true, 0, _ => CollatzStepsTo.of_eq rfl
  | false, a + 1, c => CollatzStepsTo.head rfl (stepsTo_P23_4 true a (c + 2))
  | true, a + 1, c => CollatzStepsTo.head rfl (stepsTo_P23_4 false a (c + 2))

private theorem stepsTo_P4_4 : ∀ (a c d : ℕ),
    CollatzStepsTo next (.P_4 a 4 c d) (some (toState (evalP4_4 a c d)))
  | 0, _, 0 => CollatzStepsTo.of_eq rfl
  | a + 1, c, 0 => CollatzStepsTo.head rfl (stepsTo_P23_4 true a (c + 2))
  | 0, _, _ + 1 => CollatzStepsTo.of_eq rfl
  | a + 1, c, d + 1 => CollatzStepsTo.head rfl (stepsTo_P4_4 a (c + 2) d)

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  have h_init : CollatzReachesStar next start (toState highLevelStart) :=
    CollatzReachesStar.head rfl (CollatzReachesStar.refl next _)
  refine is_valid_acceleration.of_collatz (embed := toState) h_init ?_
  rintro ⟨a, d⟩
  dsimp [toState, highLevelNext]
  split_ifs with h1 h2 h3 h4 h5
  · have h_diag := reaches_P1_diag d (a - d) 4 1 0
    have ha : a - d + d = a := by omega
    have hd : 0 + d = d := by omega
    rw [ha, hd] at h_diag
    have h_step : next (.P_1 (a - d) 4 (1 + 2 * d) 0) =
        some (.P_1 (a - d - 2) 4 1 (2 * d + 3)) := by
      have ha2 : a - d = (a - d - 2) + 2 := by omega
      have hc2 : 1 + 2 * d + 2 = 2 * d + 3 := by omega
      rw [ha2]
      simp [next, hc2]
    exact CollatzStepsTo.of_reachesStar h_diag (CollatzStepsTo.of_eq h_step)
  · subst h2
    have h_diag := reaches_P1_diag d 1 4 1 0
    have hd : 0 + d = d := by omega
    have ha : 1 + d = d + 1 := by omega
    rw [ha, hd] at h_diag
    exact CollatzStepsTo.of_reachesStar h_diag (CollatzStepsTo.of_eq rfl)
  · subst h3
    have h_diag := reaches_P1_diag a 0 4 1 0
    simp only [Nat.zero_add] at h_diag
    have h_step1 : next (.P_1 0 4 (1 + 2 * a) 0) = some (.P_2 0 0 ((2 * a + 4) + 1)) := by
      simp [next]
      omega
    exact CollatzStepsTo.of_reachesStar h_diag
      (CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq rfl))
  · have h_diag := reaches_P1_diag a 0 4 1 (d - a)
    have hd : d - a + a = d := by omega
    simp only [Nat.zero_add, hd] at h_diag
    have h_step1 : next (.P_1 0 4 (1 + 2 * a) (d - a)) =
        some (.P_4 (2 * a + 2) 4 1 (d - a + 1)) := by
      have hda : d - a = (d - a - 1) + 1 := by omega
      rw [hda]
      simp [next]
      omega
    have h_p4 := stepsTo_P4_4 (2 * a + 2) 1 (d - a + 1)
    have h_eq : evalP4_4 (2 * a + 2) 1 (d - a + 1) = .P (4 * a + 6) (d - 3 * a) := by
      rw [evalP4_4_eq]
      have hle : 2 * a + 2 ≤ d - a + 1 := by omega
      simp only [hle, ↓reduceIte]
      congr 1 <;> omega
    rw [h_eq] at h_p4
    exact CollatzStepsTo.of_reachesStar h_diag (CollatzStepsTo.head h_step1 h_p4)
  · have h_diag := reaches_P1_diag a 0 4 1 (d - a)
    have hd : d - a + a = d := by omega
    simp only [Nat.zero_add, hd] at h_diag
    have h_step1 : next (.P_1 0 4 (1 + 2 * a) (d - a)) =
        some (.P_4 (2 * a + 2) 4 1 (d - a + 1)) := by
      have hda : d - a = (d - a - 1) + 1 := by omega
      rw [hda]
      simp [next]
      omega
    have h_p4 := stepsTo_P4_4 (2 * a + 2) 1 (d - a + 1)
    have h_eq : evalP4_4 (2 * a + 2) 1 (d - a + 1) = .P (4 * a + 6) 2 := by
      rw [evalP4_4_eq]
      have hle : ¬ (2 * a + 2 ≤ d - a + 1) := by omega
      have hpar : (2 * a + 2 - (d - a + 1)) % 2 = 1 := by omega
      simp only [hle, ↓reduceIte, hpar]
      congr 1
      omega
    rw [h_eq] at h_p4
    exact CollatzStepsTo.of_reachesStar h_diag (CollatzStepsTo.head h_step1 h_p4)
  · have h_diag := reaches_P1_diag a 0 4 1 (d - a)
    have hd : d - a + a = d := by omega
    simp only [Nat.zero_add, hd] at h_diag
    have h_step1 : next (.P_1 0 4 (1 + 2 * a) (d - a)) =
        some (.P_4 (2 * a + 2) 4 1 (d - a + 1)) := by
      have hda : d - a = (d - a - 1) + 1 := by omega
      rw [hda]
      simp [next]
      omega
    have h_p4 := stepsTo_P4_4 (2 * a + 2) 1 (d - a + 1)
    have h_eq : evalP4_4 (2 * a + 2) 1 (d - a + 1) = .P (4 * a + 6) 1 := by
      rw [evalP4_4_eq]
      have hle : ¬ (2 * a + 2 ≤ d - a + 1) := by omega
      have hpar : ¬ ((2 * a + 2 - (d - a + 1)) % 2 = 1) := by omega
      simp only [hle, ↓reduceIte, hpar]
      congr 1
      omega
    rw [h_eq] at h_p4
    exact CollatzStepsTo.of_reachesStar h_diag (CollatzStepsTo.head h_step1 h_p4)

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

end BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD
