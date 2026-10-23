/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Cert

/-!
# Busy Beaver Holdout `1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`

We define the configuration for $b, c \ge 0$:

$$
P(b, c) := 0^\infty \ 11 \ (01)^b \ 10101 \ \mathrm{D}{>} \ (10)^c \ 1111 \ 0^\infty.
$$

Starting from $P(1, 0)$ (reached after 73 steps from the blank tape), the machine follows the
map $T$:

$$
T(P(b, c)) = \begin{cases}
  P(2b+4, c-b-3) & \text{if } c \ge b+3, \\
  \text{Halt} & \text{if } c = b+2, \\
  P(0, 2b+6) & \text{if } c = b+1, \\
  P(b-3c, 4c+6) & \text{if } c \le b \text{ and } 3c+1 \le b, \\
  P(1, 4c+6) & \text{if } b < 3c+1 \le 3b+1 \text{ and } b - c \text{ is odd}, \\
  P(0, 4c+6) & \text{if } b < 3c+1 \le 3b+1 \text{ and } b - c \text{ is even}.
\end{cases}
$$
-/

@[expose] public section

namespace BusyBeaver.M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB

open SixState Turing

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

/-- Variable environment `[a, b, c]` (all other variables `0`) for 3-variable certificates. -/
private def env3 (a b c : Nat) : Nat → Nat
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => 0

private theorem env3_0 (a b c : Nat) : env3 a b c 0 = a := rfl
private theorem env3_1 (a b c : Nat) : env3 a b c 1 = b := rfl
private theorem env3_2 (a b c : Nat) : env3 a b c 2 = c := rfl

private theorem congr_cfg3 (f : Nat → Nat → Nat → Cfg (Fin 2) (Fin 6))
    {a1 a2 b1 b2 c1 c2 : Nat} (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) :
    f a1 b1 c1 = f a2 b2 c2 := by
  subst ha hb hc; rfl

private def hub_1 : Cert.SC :=
  ⟨2, true, [⟨[0, 1], ⟨0, [1]⟩⟩, ⟨[1, 0], ⟨0, [0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩],
  [⟨[0, 1], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

private def hub_2 : Cert.SC := ⟨3, true, [⟨[1], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩, ⟨[1, 0], ⟨0, [0, 1]⟩⟩,
  ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[1, 0], ⟨0, [0, 0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩,
  ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩

private def hubs : List Cert.SC := [hub_1, hub_2]

def pat_P1 : TapePattern (Fin 2) (Fin 6) :=
  { left := .rep [0, 1] 0 (.rep [1, 0] 1 (.sym 1 .default))
    head := some C
    right := .rep [0, 1] 2 (.sym 1 (.sym 1 (.sym 1 .default))) }

def pat_P2 : TapePattern (Fin 2) (Fin 6) :=
  { left := .sym 1 (.rep [0, 1] 0 (.rep [1, 0] 1 (.sym 1 (.sym 1 .default))))
    head := some D
    right := .rep [1, 0] 2 (.sym 1 (.sym 1 (.sym 1 (.sym 1 .default)))) }

def ps : TapePatternSet (Fin 2) (Fin 6) :=
  [(pat_P1, .true), (pat_P2, .true)]

private def cfg_P1 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_1.den (env3 a b c) default default

private theorem eval_pat_P1 (vars : Nat → Nat) :
    evalTapePattern pat_P1 vars = cfg_P1 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_1 rfl vars

private theorem in_ps_P1 (a b c : Nat) : IsInPatternSet ps (cfg_P1 a b c) :=
  Cert.in_hubsPS hubs (by decide) hub_1 (by simp [hubs]) (env3 a b c)

private def cfg_P2 (a b c : Nat) : Cfg (Fin 2) (Fin 6) :=
  hub_2.den (env3 a b c) default default

private theorem eval_pat_P2 (vars : Nat → Nat) :
    evalTapePattern pat_P2 vars = cfg_P2 (vars 0) (vars 1) (vars 2) :=
  Cert.toPat_eval hub_2 rfl vars

private def rdefs : List Cert.RDef := [
  .prove ⟨⟨3, false, [⟨[1, 0], ⟨1, [0, 1]⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩]⟩, ⟨3, false,
    [⟨[1, 0], ⟨0, [0, 1]⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨1, [1]⟩⟩]⟩, true,
    false⟩ [.rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .step,
    .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1),
    .rw false 1 (.pack 2), .rw false 1 .merge, .done],
  .iter 0 ⟨3, false, [⟨[1, 0], ⟨0, [0, 1]⟩⟩], [⟨[0], ⟨1, []⟩⟩, ⟨[0, 1], ⟨0, [1]⟩⟩]⟩ 1 [1, 0]
]

private def rule_1_rhs : Cert.SC :=
  ⟨1, true, [⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1,
  []⟩⟩, ⟨[0], ⟨1, []⟩⟩, ⟨[1, 0], ⟨1, [0, 1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[1], ⟨1, []⟩⟩,
  ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_1_pf : List Cert.Ins :=
  [.rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw true 0 (.rotB 1), .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨1, []⟩],
  .rw true 0 .zdrop, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .rw false 0 .zdrop, .step, .done]

/-- Rule 1 (Halting): `P_1(0, b, 0) -> Halt`. -/
private theorem rule_1_halt (b : Nat) :
    ∃ cfg', ((cfg_P1 0 b 0) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩]) rule_1_rhs
    rule_1_pf rfl (env3 0 b 0)
  have hL : (hub_1.substAll [⟨0, []⟩, ⟨0, [0, 1]⟩, ⟨0,
    []⟩]).den (env3 0 b 0) default default = cfg_P1 0 b 0 :=
    (Cert.SC.den_substAll hub_1 [⟨0, []⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩] (env3 0 b 0) default default)
      |>.trans (congr_cfg3 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_1_rhs.den (env3 0 b 0) default default, h_tr.1, h_tr.2⟩

private def rule_2_pf : List Cert.Ins :=
  [.rw false 0 .zdrop, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw true 0 (.rotB 1), .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨2,
  [1]⟩], .rw true 0 .zdrop, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 5 .splitF,
  .rw true 5 .unpack, .rw true 6 (.rotB 1), .rw true 5 (.rotB 1), .rw true 5 (.rot 1),
  .rw true 6 (.rot 1), .rw true 5 (.pack 2), .rw true 5 .merge, .rw true 3 (.pack 2),
  .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 0 (.rotB 1), .done]

/-- Rule 2: `P_1(a + 1, b, 0) -> P_2(2, b + 1, a)`. -/
private theorem rule_2 (a b : Nat) :
    (cfg_P1 (a + 1) b 0) [target]⊢⁺ (cfg_P2 2 (b + 1) a) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩]) (hub_2.substAll [⟨2, []⟩, ⟨1, [0, 1]⟩, ⟨0,
      [1]⟩])
    rule_2_pf rfl (env3 a b 0)
  have hL : (hub_1.substAll [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0,
    []⟩]).den (env3 a b 0) default default = cfg_P1 (a + 1) b 0 :=
    (Cert.SC.den_substAll hub_1 [⟨1, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩] (env3 a b 0) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl)
  have hR : (hub_2.substAll [⟨2, []⟩, ⟨1, [0, 1]⟩, ⟨0,
    [1]⟩]).den (env3 a b 0) default default = cfg_P2 2 (b + 1) a :=
    (Cert.SC.den_substAll hub_2 [⟨2, []⟩, ⟨1, [0, 1]⟩, ⟨0, [1]⟩] (env3 a b 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_3_pf : List Cert.Ins := [.rw false 0 .splitF, .rw false 0 .unpack, .step, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .zdrop, .step, .step, .step, .rw false 2 (.pack 2),
  .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step, .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 2 (.pack 2), .rw true 2 .merge, .rw true 0 (.pack 2), .rw true 0 .merge,
  .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨3, [1]⟩], .rw true 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 5 (.zins [1,
  0]), .rw true 3 (.pack 2), .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 1 .splitF,
  .rw false 1 .unpack, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 3: `P_1(a, 0, 1) -> P_2(2, 0, a + 1)`. -/
private theorem rule_3 (a : Nat) :
    (cfg_P1 a 0 1) [target]⊢⁺ (cfg_P2 2 0 (a + 1)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨1, []⟩]) (hub_2.substAll [⟨2, []⟩, ⟨0, []⟩, ⟨1, [1]⟩])
    rule_3_pf rfl (env3 a 0 0)
  have hL : (hub_1.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨1,
    []⟩]).den (env3 a 0 0) default default = cfg_P1 a 0 1 :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, []⟩, ⟨1, []⟩] (env3 a 0 0) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        rfl)
  have hR : (hub_2.substAll [⟨2, []⟩, ⟨0, []⟩, ⟨1,
    [1]⟩]).den (env3 a 0 0) default default = cfg_P2 2 0 (a + 1) :=
    (Cert.SC.den_substAll hub_2 [⟨2, []⟩, ⟨0, []⟩, ⟨1, [1]⟩] (env3 a 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_4_pf : List Cert.Ins := [.rw false 0 .splitF, .rw false 0 .unpack, .step, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .zdrop, .step, .step, .step, .rw false 2 (.pack 2),
  .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge,
  .rw false 2 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step,
  .rw true 1 .splitF, .rw true 1 .unpack, .rw true 3 .splitF, .rw true 3 .unpack,
  .rw true 5 .splitF, .rw true 5 .unpack, .rw true 6 (.rotB 1), .rw true 5 (.rotB 1),
  .rw true 4 (.rotB 1), .rw true 3 (.rotB 1), .rw true 2 (.rotB 1), .rw true 1 (.rotB 1),
  .rw true 0 (.rotB 1), .rw true 0 (.rot 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
  .rw true 3 (.rot 1), .rw true 4 (.rot 1), .rw true 5 (.rot 1), .rw true 6 (.rot 1),
  .rw true 7 (.rot 1), .rw true 9 (.zins [1, 0]), .rw true 6 (.pack 2), .rw true 6 .merge,
  .rw true 4 (.pack 2), .rw true 4 .merge, .rw true 2 (.pack 2), .rw true 2 .merge,
  .rw true 0 (.pack 2), .rw true 0 .merge, .done]

set_option maxRecDepth 200000 in
/-- Rule 4: `P_1(a, 0, c + 2) -> P_1(a + 4, 0, c)`. -/
private theorem rule_4 (a c : Nat) :
    (cfg_P1 a 0 (c + 2)) [target]⊢⁺ (cfg_P1 (a + 4) 0 c) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨2, [0, 0, 1]⟩]) (hub_1.substAll [⟨4, [1]⟩, ⟨0, []⟩, ⟨0,
      [0, 0, 1]⟩])
    rule_4_pf rfl (env3 a 0 c)
  have hL : (hub_1.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨2, [0, 0,
    1]⟩]).den (env3 a 0 c) default default = cfg_P1 a 0 (c + 2) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨0, []⟩, ⟨2, [0, 0, 1]⟩] (env3 a 0 c) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  have hR : (hub_1.substAll [⟨4, [1]⟩, ⟨0, []⟩, ⟨0, [0, 0,
    1]⟩]).den (env3 a 0 c) default default = cfg_P1 (a + 4) 0 c :=
    (Cert.SC.den_substAll hub_1 [⟨4, [1]⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩] (env3 a 0 c) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_5_pf : List Cert.Ins := [.rw false 0 .splitF, .rw false 0 .unpack, .step, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw false 2 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step,
  .rw true 1 .splitF, .rw true 1 .unpack, .rw true 2 (.rotB 1), .rw true 1 (.rotB 1),
  .rw true 0 (.rotB 1), .rw true 5 (.rotB 1), .rw true 0 (.rot 1), .rw true 1 (.rot 1),
  .rw true 2 (.rot 1), .rw true 3 (.rot 1), .rw true 2 (.pack 2), .rw true 2 .merge,
  .rw true 0 (.pack 2), .rw true 0 .merge, .done]

/-- Rule 5: `P_1(a, b + 1, c + 1) -> P_1(a + 2, b, c)`. -/
private theorem rule_5 (a b c : Nat) :
    (cfg_P1 a (b + 1) (c + 1)) [target]⊢⁺ (cfg_P1 (a + 2) b c) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_1.substAll [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩]) (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0,
      1]⟩, ⟨0, [0, 0, 1]⟩])
    rule_5_pf rfl (env3 a b c)
  have hL : (hub_1.substAll [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0,
    1]⟩]).den (env3 a b c) default default = cfg_P1 a (b + 1) (c + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0,
      1]⟩] (env3 a b c) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  have hR : (hub_1.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env3 a b c) default default = cfg_P1 (a + 2) b c :=
    (Cert.SC.den_substAll hub_1 [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env3 a b c) default default)
      |>.trans (congr_cfg3 cfg_P1
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_6_pf : List Cert.Ins :=
  [.rw false 0 (.rot 1), .step, .rw false 0 .zdrop, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 3 (.pack 2), .rw true 3 .merge, .rw true 1 (.pack 2), .rw true 1 .merge,
  .rw true 0 (.rotB 1), .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨2, [1]⟩],
  .rw true 0 .zdrop, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .step, .step,
  .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1),
  .shift, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step,
  .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .rw true 4 .splitF, .rw true 4 .unpack,
  .rw true 5 (.rotB 1), .rw true 4 (.rotB 1), .rw true 3 (.rotB 1), .rw true 2 (.rotB 1),
  .rw true 2 (.rot 1), .rw true 3 (.rot 1), .rw true 4 (.rot 1), .rw true 5 (.rot 1),
  .rw true 4 (.pack 2), .rw true 4 .merge, .rw true 2 (.pack 2), .rw true 2 .merge,
  .rw true 0 (.pack 2), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 6: `P_2(a, b, 0) -> P_1(1, b + 2, a + 1)`. -/
private theorem rule_6 (a b : Nat) :
    (cfg_P2 a b 0) [target]⊢⁺ (cfg_P1 1 (b + 2) (a + 1)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩]) (hub_1.substAll [⟨1, []⟩, ⟨2, [0, 1]⟩, ⟨1,
      [1]⟩])
    rule_6_pf rfl (env3 a b 0)
  have hL : (hub_2.substAll [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨0,
    []⟩]).den (env3 a b 0) default default = cfg_P2 a b 0 :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, []⟩] (env3 a b 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl)
  have hR : (hub_1.substAll [⟨1, []⟩, ⟨2, [0, 1]⟩, ⟨1,
    [1]⟩]).den (env3 a b 0) default default = cfg_P1 1 (b + 2) (a + 1) :=
    (Cert.SC.den_substAll hub_1 [⟨1, []⟩, ⟨2, [0, 1]⟩, ⟨1, [1]⟩] (env3 a b 0) default default)
      |>.trans (congr_cfg3 cfg_P1
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_7_pf : List Cert.Ins := [.rw false 0 (.rot 1), .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .rw false 1 (.pack 2),
  .rw false 0 .merge, .shift, .rw false 0 .zdrop, .step, .step, .step, .step,
  .rw true 1 (.pack 2), .rw true 1 .merge, .rw true 0 (.rotB 1), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .rw true 0 (.pack 2), .rw true 0 .merge,
  .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨6, [1]⟩], .rw true 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 5 (.zins [1,
  0]), .rw true 3 (.pack 2), .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 1 .splitF,
  .rw false 1 .unpack, .rw false 3 .splitF, .rw false 3 .unpack, .rw false 5 .splitF,
  .rw false 5 .unpack, .rw false 7 .splitF, .rw false 7 .unpack, .rw false 8 (.rotB 1),
  .rw false 7 (.rotB 1), .rw false 6 (.rotB 1), .rw false 5 (.rotB 1), .rw false 4 (.rotB 1),
  .rw false 3 (.rotB 1), .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1),
  .rw false 4 (.rot 1), .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 7 (.rot 1),
  .rw false 6 (.pack 2), .rw false 6 .merge, .rw false 4 (.pack 2), .rw false 4 .merge,
  .rw false 2 (.pack 2), .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .done]

/-- Rule 7: `P_2(a, 0, 1) -> P_2(2, 0, a + 4)`. -/
private theorem rule_7 (a : Nat) :
    (cfg_P2 a 0 1) [target]⊢⁺ (cfg_P2 2 0 (a + 4)) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨1, []⟩]) (hub_2.substAll [⟨2, []⟩, ⟨0, []⟩, ⟨4, [1]⟩])
    rule_7_pf rfl (env3 a 0 0)
  have hL : (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨1,
    []⟩]).den (env3 a 0 0) default default = cfg_P2 a 0 1 :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, []⟩, ⟨1, []⟩] (env3 a 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        rfl)
  have hR : (hub_2.substAll [⟨2, []⟩, ⟨0, []⟩, ⟨4,
    [1]⟩]).den (env3 a 0 0) default default = cfg_P2 2 0 (a + 4) :=
    (Cert.SC.den_substAll hub_2 [⟨2, []⟩, ⟨0, []⟩, ⟨4, [1]⟩] (env3 a 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_8_rhs : Cert.SC :=
  ⟨1, true, [⟨[0], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1, 0],
  ⟨3, [1]⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩], [⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩]⟩
private def rule_8_pf : List Cert.Ins := [.rw false 0 (.rot 1), .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .rw false 1 (.pack 2),
  .rw false 0 .merge, .shift, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step,
  .rw false 0 .zdrop, .step, .done]

/-- Rule 8 (Halting): `P_2(a, 0, 2) -> Halt`. -/
private theorem rule_8_halt (a : Nat) :
    ∃ cfg', ((cfg_P2 a 0 2) [target]⊢⁺ cfg') ∧
            (step target cfg').isNone := by
  have h_tr := Cert.checkHaltTrans_sound target rdefs
    (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨2, []⟩]) rule_8_rhs
    rule_8_pf rfl (env3 a 0 0)
  have hL : (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨2,
    []⟩]).den (env3 a 0 0) default default = cfg_P2 a 0 2 :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, []⟩, ⟨2, []⟩] (env3 a 0 0) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        rfl)
  rw [hL] at h_tr
  exact ⟨rule_8_rhs.den (env3 a 0 0) default default, h_tr.1, h_tr.2⟩

private def rule_9_pf : List Cert.Ins := [.rw false 0 (.rot 1), .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw false 0 (.pack 2), .rw false 0 .merge, .rw false 1 (.pack 2),
  .rw false 0 .merge, .shift, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step,
  .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step, .step, .step,
  .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 5 .splitF, .rw true 5 .unpack, .rw true 7 .splitF, .rw true 7 .unpack,
  .rw true 8 (.rotB 1), .rw true 7 (.rotB 1), .rw true 6 (.rotB 1), .rw true 5 (.rotB 1),
  .rw true 5 (.rot 1), .rw true 6 (.rot 1), .rw true 7 (.rot 1), .rw true 8 (.rot 1),
  .rw true 7 (.pack 2), .rw true 7 .merge, .rw true 5 (.pack 2), .rw true 5 .merge,
  .rw true 3 (.pack 2), .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 0 (.rotB 1), .done]

/-- Rule 9: `P_2(a, 0, c + 3) -> P_2(2, a + 2, c)`. -/
private theorem rule_9 (a c : Nat) :
    (cfg_P2 a 0 (c + 3)) [target]⊢⁺ (cfg_P2 2 (a + 2) c) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨3, [0, 0, 1]⟩]) (hub_2.substAll [⟨2, []⟩, ⟨2, [1]⟩, ⟨0,
      [0, 0, 1]⟩])
    rule_9_pf rfl (env3 a 0 c)
  have hL : (hub_2.substAll [⟨0, [1]⟩, ⟨0, []⟩, ⟨3, [0, 0,
    1]⟩]).den (env3 a 0 c) default default = cfg_P2 a 0 (c + 3) :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨0, []⟩, ⟨3, [0, 0, 1]⟩] (env3 a 0 c) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  have hR : (hub_2.substAll [⟨2, []⟩, ⟨2, [1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env3 a 0 c) default default = cfg_P2 2 (a + 2) c :=
    (Cert.SC.den_substAll hub_2 [⟨2, []⟩, ⟨2, [1]⟩, ⟨0, [0, 0, 1]⟩] (env3 a 0 c) default default)
      |>.trans (congr_cfg3 cfg_P2
        rfl
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

private def rule_10_pf : List Cert.Ins := [.rw false 0 (.rot 1), .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .rw true 0 (.pack 2), .rw true 0 .merge, .shift,
  .rw true 0 (.rot 1), .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw false 2 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .rw true 0 .splitF,
  .rw true 0 .unpack, .rw true 2 .splitF, .rw true 2 .unpack, .rw true 3 (.rotB 1),
  .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 0 (.rotB 1), .rw true 6 (.rotB 1),
  .rw true 0 (.rot 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1), .rw true 3 (.rot 1),
  .rw true 4 (.rot 1), .rw true 3 (.pack 2), .rw true 3 .merge, .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw false 0 (.rotB 1), .done]

/-- Rule 10: `P_2(a, b + 1, c + 1) -> P_2(a + 2, b, c)`. -/
private theorem rule_10 (a b c : Nat) :
    (cfg_P2 a (b + 1) (c + 1)) [target]⊢⁺ (cfg_P2 (a + 2) b c) := by
  have h_tr := Cert.checkTrans_sound target rdefs
    (hub_2.substAll [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0, 1]⟩]) (hub_2.substAll [⟨2, [1]⟩, ⟨0, [0,
      1]⟩, ⟨0, [0, 0, 1]⟩])
    rule_10_pf rfl (env3 a b c)
  have hL : (hub_2.substAll [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0,
    1]⟩]).den (env3 a b c) default default = cfg_P2 a (b + 1) (c + 1) :=
    (Cert.SC.den_substAll hub_2 [⟨0, [1]⟩, ⟨1, [0, 1]⟩, ⟨1, [0, 0,
      1]⟩] (env3 a b c) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  have hR : (hub_2.substAll [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
    1]⟩]).den (env3 a b c) default default = cfg_P2 (a + 2) b c :=
    (Cert.SC.den_substAll hub_2 [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0,
      1]⟩] (env3 a b c) default default)
      |>.trans (congr_cfg3 cfg_P2
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega)
        (by dsimp [Cert.sem, Cert.getD_zero, Cert.getD_succ, Cert.Lin.eval, Cert.dotv, env3_0,
          env3_1, env3_2]; omega))
  rwa [hL, hR] at h_tr

/-! ## Blank-Tape Entry and Closure of `ps` (Level A) -/

private def init_pf : List Cert.Ins :=
  [.step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .rw true 2 (.zins [1, 0]),
  .rw true 0 (.pack 2), .rw false 0 (.zins [0, 1]), .done]

/-- Blank initial tape `init []` reaches `cfg_P1 1 0 0` in 16 concrete steps. -/
private theorem init_reaches_P1 : (init []) [target]⊢* (cfg_P1 1 0 0) :=
  Cert.checkInit_sound target rdefs ⟨2, true, [⟨[0, 1], ⟨1, []⟩⟩, ⟨[1, 0], ⟨0, []⟩⟩, ⟨[1], ⟨1,
    []⟩⟩], [⟨[0, 1], ⟨0, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1, []⟩⟩, ⟨[1], ⟨1,
    []⟩⟩]⟩ init_pf rfl (env3 0 0 0)

private def hub_1_pf : List Cert.Ins := [.splitZ 2, .rw false 0 .zdrop, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 1 (.pack 2), .rw true 1 .merge, .rw true 0 (.rotB 1), .rw false 1 (.zins [0, 1]),
  .app 1 [⟨0, []⟩, ⟨1, [1]⟩], .rw true 0 .zdrop, .step, .step, .rw true 0 (.rotB 1), .shift,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw false 1 (.pack 2),
  .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step, .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .splitZ 0, .rw false 0 .zdrop, .step, .halt,
  .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .rw true 5 .splitF, .rw true 5 .unpack,
  .rw true 6 (.rotB 1), .rw true 5 (.rotB 1), .rw true 5 (.rot 1), .rw true 6 (.rot 1),
  .rw true 5 (.pack 2), .rw true 5 .merge, .rw true 3 (.pack 2), .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw false 0 (.rotB 1), .hub 1 [⟨2, []⟩, ⟨1, [0, 1]⟩, ⟨0, [1]⟩],
  .rw false 0 .splitF, .rw false 0 .unpack, .step, .shift, .rw true 0 (.rot 1), .step, .splitZ 1,
  .rw true 0 .zdrop, .step, .step, .step, .rw false 2 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .splitZ 2, .rw false 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw true 2 (.pack 2), .rw true 2 .merge, .rw true 0 (.pack 2), .rw true 0 .merge,
  .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨3, [1]⟩], .rw true 0 .zdrop, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack,
  .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .rw true 5 (.zins [1,
  0]), .rw true 3 (.pack 2), .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 1 .splitF,
  .rw false 1 .unpack, .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 1 [⟨2, []⟩, ⟨0, []⟩, ⟨1, [1]⟩], .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .rw true 0 (.rotB 1), .shift, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw false 1 (.pack 2), .rw false 1 .merge, .rw false 2 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .rw true 1 .splitF, .rw true 1 .unpack,
  .rw true 3 .splitF, .rw true 3 .unpack, .rw true 5 .splitF, .rw true 5 .unpack,
  .rw true 6 (.rotB 1), .rw true 5 (.rotB 1), .rw true 4 (.rotB 1), .rw true 3 (.rotB 1),
  .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 0 (.rotB 1), .rw true 0 (.rot 1),
  .rw true 1 (.rot 1), .rw true 2 (.rot 1), .rw true 3 (.rot 1), .rw true 4 (.rot 1),
  .rw true 5 (.rot 1), .rw true 6 (.rot 1), .rw true 7 (.rot 1), .rw true 9 (.zins [1, 0]),
  .rw true 6 (.pack 2), .rw true 6 .merge, .rw true 4 (.pack 2), .rw true 4 .merge,
  .rw true 2 (.pack 2), .rw true 2 .merge, .rw true 0 (.pack 2), .rw true 0 .merge, .hub 0 [⟨4,
  [1]⟩, ⟨0, []⟩, ⟨0, [0, 0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step,
  .rw false 2 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step,
  .rw true 1 .splitF, .rw true 1 .unpack, .rw true 2 (.rotB 1), .rw true 1 (.rotB 1),
  .rw true 0 (.rotB 1), .rw true 5 (.rotB 1), .rw true 0 (.rot 1), .rw true 1 (.rot 1),
  .rw true 2 (.rot 1), .rw true 3 (.rot 1), .rw true 2 (.pack 2), .rw true 2 .merge,
  .rw true 0 (.pack 2), .rw true 0 .merge, .hub 0 [⟨2, [1]⟩, ⟨0, [0, 1]⟩, ⟨0, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 1 (`cfg_P1 a b c`) across all `(a b c) ∈ ℕ^3`. -/
private theorem step_P1_all (a b c : Nat) :
    ∃ cfg', ((cfg_P1 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_1 hub_1_pf rfl (env3 a b c)

private def hub_2_pf : List Cert.Ins := [.rw false 0 (.rot 1), .step, .splitZ 2, .rw false 0 .zdrop,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .rw true 3 (.pack 2), .rw true 3 .merge, .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw true 0 (.rotB 1), .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩, ⟨2,
  [1]⟩], .rw true 0 .zdrop, .step, .step, .rw true 0 (.rotB 1), .shift, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge,
  .rw false 0 (.rotB 1), .shift, .step, .step, .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .rw true 4 .splitF,
  .rw true 4 .unpack, .rw true 5 (.rotB 1), .rw true 4 (.rotB 1), .rw true 3 (.rotB 1),
  .rw true 2 (.rotB 1), .rw true 2 (.rot 1), .rw true 3 (.rot 1), .rw true 4 (.rot 1),
  .rw true 5 (.rot 1), .rw true 4 (.pack 2), .rw true 4 .merge, .rw true 2 (.pack 2),
  .rw true 2 .merge, .rw true 0 (.pack 2), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1),
  .rw false 0 (.rot 1), .rw false 1 (.rot 1), .rw false 0 (.pack 2), .rw false 0 .merge,
  .hub 0 [⟨1, []⟩, ⟨2, [0, 1]⟩, ⟨1, [1]⟩], .rw false 0 .splitF, .rw false 0 .unpack, .step,
  .rw true 0 (.pack 2), .rw true 0 .merge, .shift, .rw true 0 (.rot 1), .step, .splitZ 1,
  .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .rw false 0 (.pack 2), .rw false 0 .merge, .rw false 1 (.pack 2), .rw false 0 .merge, .shift,
  .splitZ 2, .rw false 0 .zdrop, .step, .step, .step, .step, .rw true 1 (.pack 2),
  .rw true 1 .merge, .rw true 0 (.rotB 1), .shift, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw false 1 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift, .step,
  .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw true 0 (.pack 2), .rw true 0 .merge, .rw false 1 (.zins [0, 1]), .app 1 [⟨0, []⟩,
  ⟨6, [1]⟩], .rw true 0 .zdrop, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .rw false 0 .splitF,
  .rw false 0 .unpack, .step, .step, .step, .step, .step, .step, .step, .step, .step, .step,
  .step, .step, .step, .step, .step, .rw true 5 (.zins [1, 0]), .rw true 3 (.pack 2),
  .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 1 .splitF, .rw false 1 .unpack,
  .rw false 3 .splitF, .rw false 3 .unpack, .rw false 5 .splitF, .rw false 5 .unpack,
  .rw false 7 .splitF, .rw false 7 .unpack, .rw false 8 (.rotB 1), .rw false 7 (.rotB 1),
  .rw false 6 (.rotB 1), .rw false 5 (.rotB 1), .rw false 4 (.rotB 1), .rw false 3 (.rotB 1),
  .rw false 2 (.rotB 1), .rw false 1 (.rotB 1), .rw false 0 (.rotB 1), .rw false 0 (.rot 1),
  .rw false 1 (.rot 1), .rw false 2 (.rot 1), .rw false 3 (.rot 1), .rw false 4 (.rot 1),
  .rw false 5 (.rot 1), .rw false 6 (.rot 1), .rw false 7 (.rot 1), .rw false 6 (.pack 2),
  .rw false 6 .merge, .rw false 4 (.pack 2), .rw false 4 .merge, .rw false 2 (.pack 2),
  .rw false 2 .merge, .rw false 0 (.pack 2), .rw false 0 .merge, .hub 1 [⟨2, []⟩, ⟨0, []⟩, ⟨4,
  [1]⟩], .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .splitZ 2, .rw false 0 .zdrop,
  .step, .halt, .rw false 0 .splitF, .rw false 0 .unpack, .step, .step, .step, .step, .step,
  .step, .step, .rw true 0 .splitF, .rw true 0 .unpack, .step, .step, .step, .step, .step, .step,
  .step, .step, .rw true 5 .splitF, .rw true 5 .unpack, .rw true 7 .splitF, .rw true 7 .unpack,
  .rw true 8 (.rotB 1), .rw true 7 (.rotB 1), .rw true 6 (.rotB 1), .rw true 5 (.rotB 1),
  .rw true 5 (.rot 1), .rw true 6 (.rot 1), .rw true 7 (.rot 1), .rw true 8 (.rot 1),
  .rw true 7 (.pack 2), .rw true 7 .merge, .rw true 5 (.pack 2), .rw true 5 .merge,
  .rw true 3 (.pack 2), .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 0 (.rotB 1),
  .hub 1 [⟨2, []⟩, ⟨2, [1]⟩, ⟨0, [0, 0, 1]⟩], .rw true 0 .splitF, .rw true 0 .unpack, .step,
  .step, .step, .rw false 2 (.pack 2), .rw false 1 .merge, .rw false 0 (.rotB 1), .shift,
  .rw true 0 .splitF, .rw true 0 .unpack, .rw true 2 .splitF, .rw true 2 .unpack,
  .rw true 3 (.rotB 1), .rw true 2 (.rotB 1), .rw true 1 (.rotB 1), .rw true 0 (.rotB 1),
  .rw true 6 (.rotB 1), .rw true 0 (.rot 1), .rw true 1 (.rot 1), .rw true 2 (.rot 1),
  .rw true 3 (.rot 1), .rw true 4 (.rot 1), .rw true 3 (.pack 2), .rw true 3 .merge,
  .rw true 1 (.pack 2), .rw true 1 .merge, .rw false 0 (.rotB 1), .hub 1 [⟨2, [1]⟩, ⟨0, [0, 1]⟩,
  ⟨0, [0, 0, 1]⟩]]

set_option maxRecDepth 200000 in
/-- Complete closure of Hub 2 (`cfg_P2 a b c`) across all `(a b c) ∈ ℕ^3`. -/
private theorem step_P2_all (a b c : Nat) :
    ∃ cfg', ((cfg_P2 a b c) [target]⊢⁺ cfg') ∧
            (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) :=
  Cert.checkHub_sound target hubs rdefs hub_2 hub_2_pf rfl (env3 a b c)

private theorem step_all (cfg : Cfg (Fin 2) (Fin 6)) (h_in : IsInPatternSet ps cfg) :
    ∃ cfg', ((cfg) [target]⊢⁺ cfg') ∧
      (IsInPatternSet ps cfg' ∨ (step target cfg').isNone) := by
  rcases h_in with ⟨entry, h_mem, vars, rfl, _⟩
  simp only [ps, List.mem_cons, List.not_mem_nil, or_false] at h_mem
  rcases h_mem with rfl | rfl
  · rw [eval_pat_P1 vars]
    exact step_P1_all (vars 0) (vars 1) (vars 2)
  · rw [eval_pat_P2 vars]
    exact step_P2_all (vars 0) (vars 1) (vars 2)

theorem is_closed_pattern_set : IsClosedPatternSet target ps :=
  ⟨⟨cfg_P1 1 0 0, init_reaches_P1, in_ps_P1 1 0 0⟩, step_all⟩

theorem has_collatz_reduction : HasCollatzReduction target :=
  ⟨ps, is_closed_pattern_set⟩

inductive State where
  | P_1 (a b c : ℕ)
  | P_2 (a b c : ℕ)
  deriving DecidableEq, Repr

def start : State := .P_1 1 0 0

def encode : State → Cfg (Fin 2) (Fin 6)
  | .P_1 a b c => evalTapePattern pat_P1
      (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)
  | .P_2 a b c => evalTapePattern pat_P2
      (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)

private theorem encode_P1 (a b c : ℕ) : encode (.P_1 a b c) = cfg_P1 a b c :=
  eval_pat_P1 (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)

private theorem encode_P2 (a b c : ℕ) : encode (.P_2 a b c) = cfg_P2 a b c :=
  eval_pat_P2 (fun i => if i = 0 then a else if i = 1 then b else if i = 2 then c else 0)

def next : State → Option State
  | .P_1 0 _ 0 => none
  | .P_1 (a + 1) b 0 => some (.P_2 2 (b + 1) a)
  | .P_1 a 0 1 => some (.P_2 2 0 (a + 1))
  | .P_1 a 0 (c + 2) => some (.P_1 (a + 4) 0 c)
  | .P_1 a (b + 1) (c + 1) => some (.P_1 (a + 2) b c)
  | .P_2 a b 0 => some (.P_1 1 (b + 2) (a + 1))
  | .P_2 a 0 1 => some (.P_2 2 0 (a + 4))
  | .P_2 _ 0 2 => none
  | .P_2 a 0 (c + 3) => some (.P_2 2 (a + 2) c)
  | .P_2 a (b + 1) (c + 1) => some (.P_2 (a + 2) b c)

private theorem step_state : ∀ s : State,
    match next s with
    | some s' => ReachesPlus target (encode s) (encode s')
    | none => ∃ cfg', ReachesStar target (encode s) cfg' ∧ (step target cfg').isNone = true
  | .P_1 0 b 0 => by
    simp only [next, encode_P1]
    rcases rule_1_halt b with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_1 (a + 1) b 0 => by
    simp only [next, encode_P1, encode_P2]
    exact rule_2 a b
  | .P_1 a 0 1 => by
    simp only [next, encode_P1, encode_P2]
    exact rule_3 a
  | .P_1 a 0 (c + 2) => by
    simp only [next, encode_P1]
    exact rule_4 a c
  | .P_1 a (b + 1) (c + 1) => by
    simp only [next, encode_P1]
    exact rule_5 a b c
  | .P_2 a b 0 => by
    simp only [next, encode_P2, encode_P1]
    exact rule_6 a b
  | .P_2 a 0 1 => by
    simp only [next, encode_P2]
    exact rule_7 a
  | .P_2 a 0 2 => by
    simp only [next, encode_P2]
    rcases rule_8_halt a with ⟨cfg', hp, hd⟩
    exact ⟨cfg', hp.to_star, hd⟩
  | .P_2 a 0 (c + 3) => by
    simp only [next, encode_P2]
    exact rule_9 a c
  | .P_2 a (b + 1) (c + 1) => by
    simp only [next, encode_P2]
    exact rule_10 a b c

theorem is_valid_acceleration : IsValidAcceleration target start encode next where
  init_reaches := by
    dsimp [start]
    rw [encode_P1]
    exact init_reaches_P1
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

private inductive MidState where
  | P_2 (a b c : ℕ)

private def midStart : MidState := .P_2 2 1 0

private def midToState : MidState → State
  | .P_2 a b c => .P_2 a b c

private def midEncode (s : MidState) : Cfg (Fin 2) (Fin 6) :=
  encode (midToState s)

private def midNext : MidState → Option MidState
  | .P_2 a b 0 =>
    if a ≤ b + 1 then some (.P_2 2 (b + 2 - a) (2 * a + 2))
    else if (a - (b + 2)) % 2 = 0 then some (.P_2 2 0 (2 * a + 2))
    else some (.P_2 2 1 (2 * a + 2))
  | .P_2 a 0 1 => some (.P_2 2 0 (a + 4))
  | .P_2 _ 0 2 => none
  | .P_2 a 0 (c + 3) => some (.P_2 2 (a + 2) c)
  | .P_2 a (b + 1) (c + 1) =>
    let k := min (b + 1) (c + 1)
    some (.P_2 (a + 2 * k) (b + 1 - k) (c + 1 - k))

private theorem reaches_P2_diag (k : ℕ) (a b c : ℕ) :
    CollatzReachesStar next (.P_2 a (b + k) (c + k)) (.P_2 (a + 2 * k) b c) := by
  induction k generalizing a with
  | zero =>
    simp only [Nat.add_zero, Nat.mul_zero]
    exact CollatzReachesStar.refl next _
  | succ k ih =>
    have h_next : next (.P_2 a (b + (k + 1)) (c + (k + 1))) =
        some (.P_2 (a + 2) (b + k) (c + k)) := by
      have h1 : b + (k + 1) = (b + k) + 1 := by omega
      have h2 : c + (k + 1) = (c + k) + 1 := by omega
      rw [h1, h2]
      simp [next]
    have ih' := ih (a + 2)
    have ha : a + 2 + 2 * k = a + 2 * (k + 1) := by omega
    rw [ha] at ih'
    exact CollatzReachesStar.head h_next ih'

private theorem reaches_P2_drain (a b c : ℕ) :
    CollatzStepsTo next (.P_2 a (b + 1) (c + 1))
      (some (.P_2 (a + 2 * min (b + 1) (c + 1))
        (b + 1 - min (b + 1) (c + 1))
        (c + 1 - min (b + 1) (c + 1)))) := by
  let k := min (b + 1) (c + 1)
  have hk_pos : 0 < k := by
    dsimp [k]
    have : 0 < b + 1 := Nat.succ_pos b
    have : 0 < c + 1 := Nat.succ_pos c
    exact Nat.lt_min.mpr ⟨‹_›, ‹_›⟩
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk_pos)
  have h_head : next (.P_2 a (b + 1) (c + 1)) = some (.P_2 (a + 2) b c) := by simp [next]
  have h_star := reaches_P2_diag m (a + 2) (b + 1 - k) (c + 1 - k)
  have hb : b + 1 - k + m = b := by omega
  have hc : c + 1 - k + m = c := by omega
  have ha : a + 2 + 2 * m = a + 2 * k := by omega
  rw [hb, hc, ha] at h_star
  exact CollatzReachesPlus.head h_head h_star

private theorem next_P1_succ (a b c : ℕ) :
    next (.P_1 a (b + 1) (c + 1)) = some (.P_1 (a + 2) b c) := by
  simp [next]

private theorem next_P1_zero_ge2 (a c : ℕ) :
    next (.P_1 a 0 (c + 2)) = some (.P_1 (a + 4) 0 c) := by
  simp [next]

private theorem next_P1_zero_one (a : ℕ) :
    next (.P_1 a 0 1) = some (.P_2 2 0 (a + 1)) := by
  simp [next]

private theorem reaches_P1_le : ∀ (c a b : ℕ), c ≤ b →
    CollatzReachesStar next (.P_1 a b c) (.P_1 (a + 2 * c) (b - c) 0)
  | 0, a, b, _ => by
    simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
    exact CollatzReachesStar.refl next _
  | c + 1, _, 0, h => by omega
  | c + 1, a, b + 1, h => by
    have ih := reaches_P1_le c (a + 2) b (by omega)
    have h1 : a + 2 + 2 * c = a + 2 * (c + 1) := by omega
    have h2 : b - c = b + 1 - (c + 1) := by omega
    rw [h1, h2] at ih
    exact CollatzReachesStar.head (next_P1_succ a b c) ih

private theorem reaches_P1_ge : ∀ (b a c : ℕ), b ≤ c →
    CollatzReachesStar next (.P_1 a b c) (.P_1 (a + 2 * b) 0 (c - b))
  | 0, a, c, _ => by
    simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
    exact CollatzReachesStar.refl next _
  | b + 1, _, 0, h => by omega
  | b + 1, a, c + 1, h => by
    have ih := reaches_P1_ge b (a + 2) c (by omega)
    have h1 : a + 2 + 2 * b = a + 2 * (b + 1) := by omega
    have h2 : c - b = c + 1 - (b + 1) := by omega
    rw [h1, h2] at ih
    exact CollatzReachesStar.head (next_P1_succ a b c) ih

private theorem reaches_P1_even : ∀ (k a : ℕ),
    CollatzReachesStar next (.P_1 a 0 (2 * k)) (.P_1 (a + 4 * k) 0 0)
  | 0, a => by
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, a => by
    have ih := reaches_P1_even k (a + 4)
    have h1 : a + 4 + 4 * k = a + 4 * (k + 1) := by omega
    have h2 : 2 * (k + 1) = 2 * k + 2 := by omega
    rw [h1] at ih
    rw [h2]
    exact CollatzReachesStar.head (next_P1_zero_ge2 a (2 * k)) ih

private theorem reaches_P1_odd : ∀ (k a : ℕ),
    CollatzReachesStar next (.P_1 a 0 (2 * k + 1)) (.P_1 (a + 4 * k) 0 1)
  | 0, a => by
    simp only [Nat.mul_zero, Nat.add_zero]
    exact CollatzReachesStar.refl next _
  | k + 1, a => by
    have ih := reaches_P1_odd k (a + 4)
    have h1 : a + 4 + 4 * k = a + 4 * (k + 1) := by omega
    have h2 : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by omega
    rw [h1] at ih
    rw [h2]
    exact CollatzReachesStar.head (next_P1_zero_ge2 a (2 * k + 1)) ih

private theorem is_valid_mid_acceleration :
    IsValidAcceleration target midStart midEncode midNext := by
  have h_init : CollatzReachesStar next start (midToState midStart) :=
    CollatzReachesStar.head rfl (CollatzReachesStar.refl next _)
  refine is_valid_acceleration.of_collatz (embed := midToState) h_init ?_
  rintro ⟨a, b, c⟩
  rcases c with _ | c
  · dsimp [midNext]
    split_ifs with hle hmod
    · have h1 := reaches_P1_le (a + 1) 1 (b + 2) (by omega)
      have ha : 1 + 2 * (a + 1) = (2 * a + 2) + 1 := by omega
      have hb : b + 2 - (a + 1) = b + 1 - a := by omega
      have hb' : b + 1 - a + 1 = b + 2 - a := by omega
      rw [ha, hb] at h1
      exact CollatzStepsTo.head rfl
        (CollatzStepsTo.of_reachesStar h1 (CollatzStepsTo.of_eq (by simp [next, midToState, hb'])))
    · have h1 := reaches_P1_ge (b + 2) 1 (a + 1) (by omega)
      have hk : a + 1 - (b + 2) = 2 * ((a - (b + 2)) / 2) + 1 := by omega
      rw [hk] at h1
      have h2 := reaches_P1_odd ((a - (b + 2)) / 2) (1 + 2 * (b + 2))
      have ha : 1 + 2 * (b + 2) + 4 * ((a - (b + 2)) / 2) = 2 * a + 1 := by omega
      rw [ha] at h2
      exact CollatzStepsTo.head rfl
        (CollatzStepsTo.of_reachesStar h1
          (CollatzStepsTo.of_reachesStar h2
            (CollatzStepsTo.of_eq (next_P1_zero_one (2 * a + 1)))))
    · have h1 := reaches_P1_ge (b + 2) 1 (a + 1) (by omega)
      have hk : a + 1 - (b + 2) = 2 * ((a - (b + 2)) / 2 + 1) := by omega
      rw [hk] at h1
      have h2 := reaches_P1_even ((a - (b + 2)) / 2 + 1) (1 + 2 * (b + 2))
      have ha : 1 + 2 * (b + 2) + 4 * ((a - (b + 2)) / 2 + 1) = (2 * a + 2) + 1 := by omega
      rw [ha] at h2
      exact CollatzStepsTo.head rfl
        (CollatzStepsTo.of_reachesStar h1
          (CollatzStepsTo.of_reachesStar h2 (CollatzStepsTo.of_eq rfl)))
  · rcases b with _ | b
    · rcases c with _ | _ | c
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.of_eq rfl
    · have h_eq : midNext (.P_2 a (b + 1) (c + 1)) =
          some (.P_2 (a + 2 * min (b + 1) (c + 1))
            (b + 1 - min (b + 1) (c + 1))
            (c + 1 - min (b + 1) (c + 1))) := by
        simp [midNext]
      rw [h_eq]
      exact reaches_P2_drain a b c

/-- Single-family high-level symbolic configuration state space for
`1RB1RF_1LC---_1LE1RD_1RA0RC_0LF0LA_0LD0RB`. -/
inductive HighLevelState where
  /-- $P(b, c) := 0^\infty\,11\,(01)^b\,10101\,\mathrm{D}{>}\,(10)^c\,1111\,0^\infty$. -/
  | P (b c : ℕ)
  deriving DecidableEq, Repr

/-- Initial high-level symbolic state $P(1, 0)$. -/
def highLevelStart : HighLevelState := .P 1 0

/-- Embed a `HighLevelState` into `State`. -/
def toState : HighLevelState → State
  | .P b c => .P_2 2 b c

/-- Decode a `HighLevelState` into a concrete Turing machine configuration. -/
def highLevelEncode (s : HighLevelState) : Cfg (Fin 2) (Fin 6) :=
  encode (toState s)

private def toMid : HighLevelState → MidState
  | .P b c => .P_2 2 b c

/-- High-level accelerated transition function on $P(b, c)$. -/
def highLevelNext : HighLevelState → Option HighLevelState
  | .P b c =>
    if c ≥ b + 3 then some (.P (2 * b + 4) (c - b - 3))
    else if c = b + 2 then none
    else if c = b + 1 then some (.P 0 (2 * b + 6))
    else if 3 * c + 1 ≤ b then some (.P (b - 3 * c) (4 * c + 6))
    else if (b - c) % 2 = 1 then some (.P 1 (4 * c + 6))
    else some (.P 0 (4 * c + 6))

/-- `highLevelStart`, `highLevelEncode`, and `highLevelNext` form a valid Collatz-like acceleration
of `target`. -/
theorem is_valid_highLevel_acceleration :
    IsValidAcceleration target highLevelStart highLevelEncode highLevelNext := by
  refine is_valid_mid_acceleration.of_collatz (embed := toMid)
    (CollatzReachesStar.refl midNext _) ?_
  rintro ⟨b, c⟩
  rcases c with _ | c
  · rcases b with _ | b
    · exact CollatzStepsTo.of_eq rfl
    · exact CollatzStepsTo.of_eq (by simp [toMid, highLevelNext, midNext])
  · rcases b with _ | b
    · rcases c with _ | _ | c
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.of_eq rfl
      · exact CollatzStepsTo.of_eq (by simp [toMid, highLevelNext, midNext])
    · dsimp [toMid, highLevelNext]
      split_ifs with h1 h2 h3 h4 h5
      · have h_step1 : midNext (.P_2 2 (b + 1) (c + 1)) =
            some (.P_2 (2 * b + 4) 0 ((c - b - 3) + 3)) := by
          simp [midNext]; omega
        exact CollatzStepsTo.head h_step1
          (CollatzStepsTo.of_eq (by simp [midNext, toMid]; congr 1))
      · have h_step1 : midNext (.P_2 2 (b + 1) (c + 1)) = some (.P_2 (2 * b + 4) 0 2) := by
          simp [midNext]; omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq rfl)
      · have h_step1 : midNext (.P_2 2 (b + 1) (c + 1)) = some (.P_2 (2 * b + 4) 0 1) := by
          simp [midNext]; omega
        exact CollatzStepsTo.head h_step1
          (CollatzStepsTo.of_eq (by simp [midNext, toMid]; congr 1))
      · obtain ⟨t, rfl⟩ : ∃ t, b = c + t := ⟨b - c, by omega⟩
        have h_step1 : midNext (.P_2 2 (c + t + 1) (c + 1)) = some (.P_2 (2 * c + 4) t 0) := by
          have hk : min (c + t + 1) (c + 1) = c + 1 := by omega
          simp only [midNext, hk, Option.some.injEq, MidState.P_2.injEq]; omega
        have h_step2 : midNext (.P_2 (2 * c + 4) t 0) =
            some (.P_2 2 (c + t + 1 - 3 * (c + 1)) (4 * (c + 1) + 6)) := by
          simp only [midNext]
          split_ifs <;> simp only [Option.some.injEq, MidState.P_2.injEq, true_and] <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
      · obtain ⟨t, rfl⟩ : ∃ t, b = c + t := ⟨b - c, by omega⟩
        have h_step1 : midNext (.P_2 2 (c + t + 1) (c + 1)) = some (.P_2 (2 * c + 4) t 0) := by
          have hk : min (c + t + 1) (c + 1) = c + 1 := by omega
          simp only [midNext, hk, Option.some.injEq, MidState.P_2.injEq]; omega
        have h_step2 : midNext (.P_2 (2 * c + 4) t 0) = some (.P_2 2 1 (4 * (c + 1) + 6)) := by
          simp only [midNext]
          split_ifs <;> simp only [Option.some.injEq, MidState.P_2.injEq, true_and] <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)
      · obtain ⟨t, rfl⟩ : ∃ t, b = c + t := ⟨b - c, by omega⟩
        have h_step1 : midNext (.P_2 2 (c + t + 1) (c + 1)) = some (.P_2 (2 * c + 4) t 0) := by
          have hk : min (c + t + 1) (c + 1) = c + 1 := by omega
          simp only [midNext, hk, Option.some.injEq, MidState.P_2.injEq]; omega
        have h_step2 : midNext (.P_2 (2 * c + 4) t 0) = some (.P_2 2 0 (4 * (c + 1) + 6)) := by
          simp only [midNext]
          split_ifs <;> simp only [Option.some.injEq, MidState.P_2.injEq, true_and] <;> omega
        exact CollatzStepsTo.head h_step1 (CollatzStepsTo.of_eq h_step2)

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

end BusyBeaver.M_1RB1RF_1LCHHH_1LE1RD_1RA0RC_0LF0LA_0LD0RB
