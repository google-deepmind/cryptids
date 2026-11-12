/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Stack
public import BusyBeaver.WordRunStack

@[expose] public section


/-!
# Busy Beaver Machine `1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA` (`IsOdometerCryptid`)

Formal `IsOdometerCryptid` proof for `1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA` (`target`).
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RBHHH_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA

/-- The `(6, 2)` Turing machine in `ConjectureMachines.Machine` form. -/
def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB---_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA"

/-- The `(6, 2)` Turing machine in `BusyBeaver.Machine` form. -/
abbrev target : Machine (Fin 2) (Fin 6) :=
  machine.toBB

private def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => none
  | 1, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 0 Dir.right)
  | 3, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 4, 0 => some (some 2, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 3, Stmt.write 1 Dir.right)
  | 5, 1 => some (some 0, Stmt.write 1 Dir.right)

private theorem target_eq_target_tm : target = target_tm := by
  funext q s
  fin_cases q <;> fin_cases s <;> rfl

local notation "zB" => ListBlank (Fin 2)

@[simp] private theorem zMz {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (config : Cfg Γ Λ) :
  multiStep M config 0 = some config := rfl
@[simp] private theorem zMo {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (config : Cfg Γ Λ) :
  multiStep M config 1 = step M config := rfl
@[simp] private theorem zMs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ] (M : Machine Γ Λ)
    (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] private theorem z00 : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl

@[simp] private theorem zDh : (default : zB).head = 0 := rfl
@[simp] private theorem zDt : (default : zB).tail = default := rfl

private theorem zSm {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢^{1} c₂ := by simp [h]

private theorem z01 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ : Cfg Γ Λ) (h : c₁ [tm]⊢ c₂) : c₁ [tm]⊢⁺ c₂ :=
  ⟨1, by decide, zSm tm c₁ c₂ h⟩

private theorem zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih => rw [Nat.add_succ, zMs, ih, Option.bind_assoc]; simp_rw [zMs]

private theorem zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c3 : Cfg Γ Λ) (n m : Nat)
    (h1 : c₁ [tm]⊢^{n} c₂) (h2 : c₂ [tm]⊢^{m} c3) : c₁ [tm]⊢^{n+m} c3 := by
  rw [zMa, h1]; simp [h2]

private theorem zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) : c₁ [tm]⊢* c₂ := by
  obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

private theorem z02 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h1 : c₁ [tm]⊢⁺ c₂) (h2 : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 := by
  obtain ⟨n, n_pos, hn⟩ := h1; obtain ⟨m, hm⟩ := h2
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c3 n m hn hm⟩

private theorem z03 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h1 : c₁ [tm]⊢ c₂) (h2 : c₂ [tm]⊢* c3) : c₁ [tm]⊢⁺ c3 :=
  z02 (z01 tm c₁ c₂ h1) h2

private theorem zPpp {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c3 : Cfg Γ Λ}
    (h1 : c₁ [tm]⊢⁺ c₂) (h2 : c₂ [tm]⊢⁺ c3) : c₁ [tm]⊢⁺ c3 :=
  z02 h1 (zPs h2)

local macro "finish" : tactic => `(tactic| exists 0 <;> fail)
local macro "gstep" : tactic =>
  `(tactic| (try refine zPs ?_) <;>
    refine z03 (by (try simp only [Turing.ListBlank.head_cons, zDh]); rfl) ?_ <;>
    simp only [Turing.Tape.move, Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
      Tape.write, z00, zDh, zDt])
local macro "execute" : tactic => `(tactic| repeat (any_goals (first | finish | gstep)))

private theorem fin2_cases (b : Fin 2) : b = 0 ∨ b = 1 := by
  match b with
  | ⟨0, _⟩ => left; rfl
  | ⟨1, _⟩ => right; rfl

private inductive OdomTok where
  | L0
  | L1
  | L2
deriving DecidableEq, Repr

@[simp]
private def odomWord : OdomTok → List (Fin 2)
  | .L0 => [0, 0, 1, 0]
  | .L1 => [1, 0, 1, 0]
  | .L2 => [1, 1, 0]

@[simp]
private def encOdom : List OdomTok → zB
  | [] => [1] +> default
  | t :: l => odomWord t +> encOdom l

private theorem encOdom_non_surjective :
    ∃ t : zB, ∀ stk : List OdomTok, encOdom stk ≠ t := by
  refine ⟨default, fun stk h => ?_⟩
  cases stk with
  | nil =>
    have h1 : (encOdom []).head = (default : zB).head := congrArg ListBlank.head h
    simp only [encOdom, ListBlank.append, ListBlank.head_cons, zDh] at h1
    revert h1; decide
  | cons t tl =>
    cases t with
    | L0 =>
      have h1 : (encOdom (.L0 :: tl)).tail.tail.head = (default : zB).tail.tail.head :=
        congrArg (fun x => x.tail.tail.head) h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.tail_cons, ListBlank.head_cons,
        zDt, zDh] at h1
      revert h1; decide
    | L1 =>
      have h1 : (encOdom (.L1 :: tl)).head = (default : zB).head := congrArg ListBlank.head h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.head_cons, zDh] at h1
      revert h1; decide
    | L2 =>
      have h1 : (encOdom (.L2 :: tl)).head = (default : zB).head := congrArg ListBlank.head h
      simp only [encOdom, odomWord, ListBlank.append, ListBlank.head_cons, zDh] at h1
      revert h1; decide

@[simp] private def state_R (_ : List OdomTok) : Fin 6 := 3

@[simp] private def cfg_R (l : List OdomTok) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  evalOdomR .leftOdom (state_R l) [1, 0] (encOdom l) r

@[simp] private def cfg_L (l : List OdomTok) (r : zB) : Cfg (Fin 2) (Fin 6) :=
  evalOdomL .leftOdom 1 [1, 0] (encOdom l) r

private def IsInOdomSystem (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ stk w, cfg = evalOdomR .leftOdom (state_R stk) [1, 0] (encOdom stk) w

private def init_w0 : zB := (0 : Fin 2) >> 1 >> 0 >> 1 >> default

private theorem step_init : (init []) [target_tm]⊢⁺ cfg_R [] init_w0 := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]; simp only [cfg_R, state_R, init_w0, evalOdomR, encOdom, ListBlank.append
   ]; execute

private theorem step_R_0 (l : List OdomTok) (r : zB) :
    (cfg_R l ((0 : Fin 2) >> r)) [target_tm]⊢⁺ cfg_L l ((1 : Fin 2) >> r) := by
  simp only [cfg_L, cfg_R, state_R, evalOdomL, evalOdomR, ListBlank.append]; execute

private theorem step_R_100 (l : List OdomTok) (r : zB) :
    (cfg_R l ((1 : Fin 2) >> 0 >> 0 >> r)) [target_tm]⊢⁺ cfg_R (.L2 :: l) r := by
  simp only [cfg_R, state_R, evalOdomR, encOdom, odomWord, ListBlank.append]; execute

private theorem step_R_11 (l : List OdomTok) (r : zB) :
    (cfg_R l ((1 : Fin 2) >> 1 >> r)) [target_tm]⊢⁺ cfg_L l ((1 : Fin 2) >> 0 >> r) := by
  simp only [cfg_L, cfg_R, state_R, evalOdomL, evalOdomR, ListBlank.append]; execute

private theorem step_R_1010 (l : List OdomTok) (r : zB) :
    (cfg_R l ((1 : Fin 2) >> 0 >> 1 >> 0 >> r)) [target_tm]⊢⁺ cfg_R (.L0 :: l) r := by
  simp only [cfg_R, state_R, evalOdomR, encOdom, odomWord, ListBlank.append]; execute

private theorem step_L_L0 (l : List OdomTok) (r : zB) :
    (cfg_L (.L0 :: l) r) [target_tm]⊢⁺ cfg_R (.L1 :: l) r := by
  simp only [cfg_L, cfg_R, state_R, evalOdomL, evalOdomR, encOdom, odomWord, ListBlank.append
   ]; execute

private theorem step_L_L1 (l : List OdomTok) (r : zB) :
    (cfg_L (.L1 :: l) r) [target_tm]⊢⁺ cfg_L l ((1 : Fin 2) >> 0 >> 1 >> 0 >> r) := by
  simp only [cfg_L, evalOdomL, encOdom, odomWord, ListBlank.append]; execute

private theorem step_L_L2 (l : List OdomTok) (r : zB) :
    (cfg_L (.L2 :: l) r) [target_tm]⊢⁺ cfg_L l ((0 : Fin 2) >> 1 >> 0 >> r) := by
  simp only [cfg_L, evalOdomL, encOdom, odomWord, ListBlank.append]; execute

private theorem step_L_nil (r : zB) :
    (cfg_L [] r) [target_tm]⊢⁺ cfg_R [] ((1 : Fin 2) >> 0 >> r) := by
  simp only [cfg_L, cfg_R, state_R, evalOdomL, evalOdomR, encOdom, ListBlank.append]; execute

@[simp]
private def cap : List OdomTok → Nat
  | [] => 0
  | .L0 :: l => 2 * cap l + 1
  | .L1 :: l => 2 * cap l
  | .L2 :: l => cap l / 3

@[simp]
private def dec_fuel : Nat → List OdomTok → List OdomTok
  | 0, l => l
  | _ + 1, [] => []
  | _ + 1, .L0 :: l => .L1 :: l
  | n + 1, .L1 :: l => .L0 :: dec_fuel n l
  | n + 1, .L2 :: l => .L2 :: dec_fuel n (dec_fuel n (dec_fuel n l))

private def dec (l : List OdomTok) : List OdomTok := dec_fuel l.length l

@[simp]
private theorem length_dec_fuel (n : Nat) (l : List OdomTok) : (dec_fuel n l).length = l.length :=
  by
  induction n generalizing l with
  | zero => rfl
  | succ n ih =>
    cases l with
    | nil => rfl
    | cons t tl => cases t <;> simp [dec_fuel, ih]

@[simp]
private theorem length_dec (l : List OdomTok) : (dec l).length = l.length :=
  length_dec_fuel l.length l

@[simp] private theorem dec_nil : dec [] = [] := rfl
@[simp] private theorem dec_L0 (l : List OdomTok) : dec (.L0 :: l) = .L1 :: l := rfl
@[simp] private theorem dec_L1 (l : List OdomTok) : dec (.L1 :: l) = .L0 :: dec l := rfl
@[simp] private theorem dec_L2 (l : List OdomTok) : dec (.L2 :: l) = .L2 :: dec (dec (dec l)) := by
  simp only [dec, List.length_cons, dec_fuel, length_dec_fuel]

private theorem cap_dec_aux (n : Nat) :
    ∀ l : List OdomTok, l.length ≤ n → cap l ≥ 1 → cap (dec l) = cap l - 1 := by
  induction n with
  | zero =>
    intro l hlen h
    cases l <;> simp at hlen h
  | succ n ih =>
    intro l hlen h
    cases l with
    | nil => simp at h
    | cons t l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => simp
      | L1 =>
        simp only [cap, dec_L1] at h ⊢
        have h1 : cap l ≥ 1 := by omega
        rw [ih l hlen h1]; omega
      | L2 =>
        simp only [cap, dec_L2] at h ⊢
        have h1 : cap l ≥ 3 := by omega
        have ih1 := ih l hlen (by omega)
        have hlen1 : (dec l).length ≤ n := by rw [length_dec]; exact hlen
        have ih2 := ih (dec l) hlen1 (by omega)
        have hlen2 : (dec (dec l)).length ≤ n := by rw [length_dec, length_dec]; exact hlen
        have ih3 := ih (dec (dec l)) hlen2 (by omega)
        rw [ih3, ih2, ih1]; omega

private theorem cap_dec (l : List OdomTok) (h : cap l ≥ 1) : cap (dec l) = cap l - 1 :=
  cap_dec_aux l.length l (Nat.le_refl _) h

private theorem runHL_dec_aux (n : Nat) :
    ∀ (l : List OdomTok) (r : zB), l.length ≤ n → cap l ≥ 1 →
      (cfg_L l r) [target_tm]⊢⁺ cfg_R (dec l) r := by
  induction n with
  | zero =>
    intro l _ hlen h
    cases l <;> simp at hlen h
  | succ n ih =>
    intro l r hlen h
    cases l with
    | nil => simp at h
    | cons t l =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 =>
        simp only [dec_L0]
        exact step_L_L0 l r
      | L1 =>
        simp only [cap, dec_L1] at h ⊢
        have h1 : cap l ≥ 1 := by omega
        exact zPpp (step_L_L1 l r)
          (zPpp (ih l _ hlen h1) (step_R_1010 (dec l) r))
      | L2 =>
        simp only [cap, dec_L2] at h ⊢
        have hc3 : cap l ≥ 3 := by omega
        have hdec1 : cap (dec l) = cap l - 1 := cap_dec l (by omega)
        have hdec2 : cap (dec (dec l)) = cap l - 2 := by
          rw [cap_dec (dec l) (by omega), hdec1]; omega
        have hlen1 : (dec l).length ≤ n := by rw [length_dec]; exact hlen
        have hlen2 : (dec (dec l)).length ≤ n := by rw [length_dec]; exact hlen1
        exact zPpp (step_L_L2 l r)
          (zPpp (ih l _ hlen (by omega))
            (zPpp (step_R_0 (dec l) _)
              (zPpp (ih (dec l) _ hlen1 (by omega))
                (zPpp (step_R_11 (dec (dec l)) _)
                  (zPpp (ih (dec (dec l)) _ hlen2 (by omega))
                    (step_R_100 (dec (dec (dec l))) r))))))

private theorem runHL_dec (l : List OdomTok) (r : zB) (h : cap l ≥ 1) :
    (cfg_L l r) [target_tm]⊢⁺ cfg_R (dec l) r :=
  runHL_dec_aux l.length l r (Nat.le_refl _) h

@[simp]
private def mod3Bits (c : Nat) : List (Fin 2) :=
  if c % 3 = 0 then [0, 1, 0]
  else if c % 3 = 1 then [1, 1, 0]
  else [1, 0, 0]

@[simp]
private def drain : List OdomTok → List (Fin 2)
  | [] => [1, 0]
  | .L0 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L1 :: tl => drain tl ++ [1, 0, 1, 0]
  | .L2 :: tl => drain tl ++ mod3Bits (cap tl)

private theorem drain_ne_nil : ∀ l : List OdomTok, drain l ≠ []
  | [] => by decide
  | .L0 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _
  | .L1 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _
  | .L2 :: tl => List.append_ne_nil_of_left_ne_nil (drain_ne_nil tl) _

private theorem drain_dec_aux (n : Nat) :
    ∀ l : List OdomTok, l.length ≤ n → cap l ≥ 1 → drain (dec l) = drain l := by
  induction n with
  | zero =>
    intro l hlen hcap
    cases l <;> simp at hlen hcap
  | succ n ih =>
    intro l hlen hcap
    cases l with
    | nil => simp at hcap
    | cons t tl =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => rfl
      | L1 =>
        simp only [cap, dec_L1, drain] at hcap ⊢
        rw [ih tl hlen (by omega)]
      | L2 =>
        simp only [cap, dec_L2, drain] at hcap ⊢
        have hc3 : cap tl ≥ 3 := by omega
        have hdec1' : cap (dec tl) = cap tl - 1 := cap_dec tl (by omega)
        have hdec2 : cap (dec (dec tl)) = cap tl - 2 := by
          rw [cap_dec (dec tl) (by omega), hdec1']; omega
        have hdec3 : cap (dec (dec (dec tl))) = cap tl - 3 := by
          rw [cap_dec (dec (dec tl)) (by omega), hdec2]; omega
        have hlen1 : (dec tl).length ≤ n := by rw [length_dec]; exact hlen
        have hlen2 : (dec (dec tl)).length ≤ n := by rw [length_dec]; exact hlen1
        have ih1 := ih tl hlen (by omega)
        have ih2 := ih (dec tl) hlen1 (by omega)
        have ih3 := ih (dec (dec tl)) hlen2 (by omega)
        have hmod : mod3Bits (cap (dec (dec (dec tl)))) = mod3Bits (cap tl) := by
          simp only [mod3Bits, hdec3]
          have hrem : (cap tl - 3) % 3 = cap tl % 3 := by omega
          rw [hrem]
        rw [ih3, ih2, ih1, hmod]

private theorem drain_dec (l : List OdomTok) (hcap : cap l ≥ 1) : drain (dec l) = drain l :=
  drain_dec_aux l.length l (Nat.le_refl _) hcap

private theorem append_list_assoc (xs ys : List (Fin 2)) (w : zB) :
    (xs ++ ys) +> w = xs +> (ys +> w) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append, ListBlank.append, ih]

private theorem run_drain_aux (n : Nat) :
    ∀ (l : List OdomTok) (w : zB), l.length ≤ n → cap l = 0 →
      (cfg_L l w) [target_tm]⊢⁺ cfg_R [] (drain l +> w) := by
  induction n with
  | zero =>
    intro l w hlen _
    cases l with
    | nil => exact step_L_nil w
    | cons _ _ => simp at hlen
  | succ n ih =>
    intro l w hlen hcap
    cases l with
    | nil => exact step_L_nil w
    | cons t tl =>
      simp only [List.length_cons, Nat.add_le_add_iff_right] at hlen
      cases t with
      | L0 => simp only [cap] at hcap; omega
      | L1 =>
        simp only [cap] at hcap
        have htl : cap tl = 0 := by omega
        simp only [drain, append_list_assoc]
        exact zPpp (step_L_L1 tl w) (ih tl ([1, 0, 1, 0] +> w) hlen htl)
      | L2 =>
        simp only [cap] at hcap
        simp only [drain, append_list_assoc]
        have hcases : cap tl = 0 ∨ cap tl = 1 ∨ cap tl = 2 := by omega
        rcases hcases with h0 | h1 | h2
        · have hm : mod3Bits (cap tl) = [0, 1, 0] := by simp [mod3Bits, h0]
          rw [hm]
          exact zPpp (step_L_L2 tl w) (ih tl ([0, 1, 0] +> w) hlen h0)
        · have hm : mod3Bits (cap tl) = [1, 1, 0] := by simp [mod3Bits, h1]
          rw [hm]
          have hdec1_cap : cap (dec tl) = 0 := by have := cap_dec tl (by omega); omega
          have hdec1_len : (dec tl).length ≤ n := by rw [length_dec]; exact hlen
          have h_ih := ih (dec tl) ([1, 1, 0] +> w) hdec1_len hdec1_cap
          rw [drain_dec tl (by omega)] at h_ih
          exact zPpp (step_L_L2 tl w)
            (zPpp (runHL_dec tl ((0 : Fin 2) >> 1 >> 0 >> w) (by omega))
              (zPpp (step_R_0 (dec tl) ((1 : Fin 2) >> 0 >> w)) h_ih))
        · have hm : mod3Bits (cap tl) = [1, 0, 0] := by simp [mod3Bits, h2]
          rw [hm]
          have hdec1_cap : cap (dec tl) = 1 := by have := cap_dec tl (by omega); omega
          have hdec2_cap : cap (dec (dec tl)) = 0 := by
            have := cap_dec (dec tl) (by omega); omega
          have hdec1_len : (dec tl).length ≤ n := by rw [length_dec]; exact hlen
          have hdec2_len : (dec (dec tl)).length ≤ n := by rw [length_dec]; exact hdec1_len
          have h_ih := ih (dec (dec tl)) ([1, 0, 0] +> w) hdec2_len hdec2_cap
          rw [drain_dec (dec tl) (by omega), drain_dec tl (by omega)] at h_ih
          exact zPpp (step_L_L2 tl w)
            (zPpp (runHL_dec tl ((0 : Fin 2) >> 1 >> 0 >> w) (by omega))
              (zPpp (step_R_0 (dec tl) ((1 : Fin 2) >> 0 >> w))
                (zPpp (runHL_dec (dec tl) ((1 : Fin 2) >> 1 >> 0 >> w) (by omega))
                  (zPpp (step_R_11 (dec (dec tl)) ((0 : Fin 2) >> w)) h_ih))))

private theorem run_drain (l : List OdomTok) (w : zB) (hcap : cap l = 0) :
    (cfg_L l w) [target_tm]⊢⁺ cfg_R [] (drain l +> w) :=
  run_drain_aux l.length l w (Nat.le_refl _) hcap

private def stepL_state (l : List OdomTok) (w : zB) : List OdomTok × zB :=
  if cap l ≥ 1 then (dec l, w) else ([], drain l +> w)

private theorem stepL_state_sound (l : List OdomTok) (w : zB) :
    (cfg_L l w) [target_tm]⊢⁺ cfg_R (stepL_state l w).1 (stepL_state l w).2 := by
  unfold stepL_state
  split_ifs with hcap
  · exact runHL_dec l w hcap
  · have hz : cap l = 0 := by omega
    exact run_drain l w hz

private theorem step_R_partition (l : List OdomTok) (w : zB)
    (hguard : w.head = 0 ∨ (w.tail.head = 0 ∧ (w.tail.tail.head = 0 ∨ w.tail.tail.tail.head = 0))) :
    (∃ t w', (cfg_R l w) [target_tm]⊢⁺ cfg_R (t :: l) w') ∨
    (∃ w', (cfg_R l w) [target_tm]⊢⁺ cfg_L l w') ∨
    (∃ cfg', ((cfg_R l w) [target_tm]⊢⁺ cfg') ∧ (step target_tm cfg').isNone) := by
  rcases fin2_cases w.head with h0 | h1
  · have hw0 : w = (0 : Fin 2) >> w.tail := by
      conv_lhs => rw [← ListBlank.cons_head_tail w, h0]
    rw [hw0]
    exact Or.inr (Or.inl ⟨(1 : Fin 2) >> w.tail, step_R_0 l w.tail⟩)
  · rcases fin2_cases w.tail.head with h10 | h11
    · rcases fin2_cases w.tail.tail.head with h100 | h101
      · have hw : w = (1 : Fin 2) >> 0 >> 0 >> w.tail.tail.tail := by
          conv_lhs =>
            rw [← ListBlank.cons_head_tail w, h1,
                ← ListBlank.cons_head_tail w.tail, h10,
                ← ListBlank.cons_head_tail w.tail.tail, h100]
        rw [hw]
        exact Or.inl ⟨.L2, w.tail.tail.tail, step_R_100 l w.tail.tail.tail⟩
      · rcases fin2_cases w.tail.tail.tail.head with h1010 | h1011
        · have hw : w = (1 : Fin 2) >> 0 >> 1 >> 0 >> w.tail.tail.tail.tail := by
            conv_lhs =>
              rw [← ListBlank.cons_head_tail w, h1,
                  ← ListBlank.cons_head_tail w.tail, h10,
                  ← ListBlank.cons_head_tail w.tail.tail, h101,
                  ← ListBlank.cons_head_tail w.tail.tail.tail, h1010]
          rw [hw]
          exact Or.inl ⟨.L0, w.tail.tail.tail.tail, step_R_1010 l w.tail.tail.tail.tail⟩
        · rcases hguard with hg0 | ⟨_, hg2 | hg3⟩
          · rw [h1] at hg0; nomatch hg0
          · rw [h101] at hg2; nomatch hg2
          · rw [h1011] at hg3; nomatch hg3
    · rcases hguard with hg0 | ⟨hg1, _⟩
      · rw [h1] at hg0; nomatch hg0
      · rw [h11] at hg1; nomatch hg1

private theorem step_R_closed (l : List OdomTok) (w : zB)
    (hguard : w.head = 0 ∨ (w.tail.head = 0 ∧ (w.tail.tail.head = 0 ∨ w.tail.tail.tail.head = 0))) :
    ∃ cfg', ((cfg_R l w) [target_tm]⊢⁺ cfg') ∧
      (IsInOdomSystem cfg' ∨ (step target_tm cfg').isNone) := by
  rcases step_R_partition l w hguard with ⟨t, w', hpush⟩ | ⟨w', hrefl⟩ | ⟨cfg_halt, hhalt, hnone⟩
  · exact ⟨cfg_R (t :: l) w', hpush, Or.inl ⟨t :: l, w', rfl⟩⟩
  · exact ⟨cfg_R (stepL_state l w').1 (stepL_state l w').2,
      zPpp hrefl (stepL_state_sound l w'),
      Or.inl ⟨(stepL_state l w').1, (stepL_state l w').2, rfl⟩⟩
  · exact ⟨cfg_halt, hhalt, Or.inr hnone⟩

private theorem step_init_nontrivial : (init []) [target_tm]⊢⁺ cfg_R [.L0, .L0] default := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = ((default : zB) {{0}}> (default : zB)) := rfl
  rw [h_init]; simp only [cfg_R, state_R, evalOdomR, encOdom, odomWord, ListBlank.append
   ]; execute


theorem is_odometer_cryptid : IsOdometerCryptid target := by
  rw [target_eq_target_tm]
  refine ⟨OdomTok, .leftOdom, state_R, 1, [1, 0], [1, 0], [1], odomWord, encOdom, cap, dec,
    (fun _ => []), drain, IsInOdomSystem, ?_, ?_, ?_, rfl, ?_, encOdom_non_surjective, rfl, ?_,
    length_dec, cap_dec, runHL_dec, (fun stk _ => drain_ne_nil stk), run_drain,
    step_R_0, step_R_partition, (fun _ => Iff.rfl),
    ⟨[.L0, .L0], default, step_init_nontrivial, by decide, by decide⟩, step_R_closed⟩
  · refine ⟨[.L0, .L1, .L2], by decide, by decide, ?_⟩
    intro t; cases t <;> decide
  · decide
  · intro t; cases t <;> decide
  · intro t stk; rfl
  · refine ⟨.L0, .L1, .L2, 3, [1, 0, 1, 0], [1, 0, 0],
      by decide, by decide, by decide, (fun _ => rfl), (fun _ => rfl), (fun _ => rfl),
      step_R_1010, step_R_100⟩

end BusyBeaver.M_1RBHHH_1RC0LE_0LD0RF_1LB0RE_0RC0LE_1RD1RA
