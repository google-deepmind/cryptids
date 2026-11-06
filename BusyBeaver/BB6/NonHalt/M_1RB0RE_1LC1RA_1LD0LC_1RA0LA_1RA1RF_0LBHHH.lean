/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.WordCalculusA
public import BusyBeaver.Calculi.WordCalculusB
public import BusyBeaver.Calculi.WordCalculusC
public import BusyBeaver.Calculi.WordCalculusD
public import BusyBeaver.Calculi.WordCalculusE

open Mathlib Relation Nat Turing BusyBeaver SixState WordCalculus Word ChoiceE

namespace BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

namespace Solution

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
-- A..F inherited directly from SixState
abbrev HalfTape := ListBlank (Fin 2)
abbrev BitWord := List (Fin 2)
abbrev WordList := List Word

@[simp] theorem multiStep_zero (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) :
    multiStep M config 0 = some config := rfl
@[simp] theorem multiStep_one (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) :
    multiStep M config 1 = step M config := rfl
@[simp] theorem multiStep_succ (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] theorem cons_zero_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head : (default : HalfTape).head = 0 := rfl
@[simp] theorem default_tail : (default : HalfTape).tail = default := rfl
@[simp] theorem append_nil (s : HalfTape) : ([] : BitWord) +> s = s := rfl
@[simp] theorem append_cons (a : Fin 2) (l : BitWord) (s : HalfTape) :
    (a :: l) +> s = a >> (l +> s) := rfl
@[simp] theorem append_assoc (l1 l2 : BitWord) (s : HalfTape) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]
theorem step_to_multiStep_one {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
theorem step_to_stepPlus {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, step_to_multiStep_one tm c_1 c_2 h⟩
theorem multiStep_add {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 : Cfg Γ₀ Λ₀) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ, ih, Option.bind_assoc]
    simp_rw [multiStep_succ]
theorem multiStep_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 c_3 : Cfg Γ₀ Λ₀) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [multiStep_add, h₁]; simp [h₂]
theorem stepPlus_to_stepStar {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 : Cfg Γ₀ Λ₀} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
theorem stepPlus_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans tm c_1 c_2 c_3 n m hn hm⟩
theorem stepPlus_stepStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m),
      multiStep_trans tm c_1 c_2 c_3 n m hn hm⟩
theorem step_stepStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  stepPlus_stepStar_trans (step_to_stepPlus tm c_1 c_2 h₁) h₂
macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_to_stepStar ?_) <;>
    refine step_stepStar_trans (by (try simp only [BusyBeaver.Cfg.headRight,
        BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons, default_head]); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
        Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, cons_zero_default,
        default_head, default_tail])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev t : BitWord := [1, 1, 0, 0]
abbrev d0 : BitWord := [0, 0]
abbrev d1 : BitWord := [1, 0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
@[simp] theorem append_d0_default : d0 +> (default : HalfTape) = default := by
  simp [d0]

inductive Call where
  | ch
  | cj
  | cp
  | ca

def callWord : Call -> BitWord
  | .ch => [1]
  | .cj => [1, 1]
  | .cp => [1, 0]
  | .ca => [1, 1, 1, 0, 1, 1]

def CallStep (tm : Machine (Fin 2) (Fin 6))
    (cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6))
    (cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6))
    (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l, (cR l c r1) [tm]⊢⁺ (cL l r2)

inductive Side (stepRel : Call -> HalfTape -> HalfTape -> Prop) :
    List Call -> HalfTape -> HalfTape -> Prop where
  | nil (r : HalfTape) : Side stepRel [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : HalfTape} :
      stepRel c r1 r2 -> Side stepRel ls r2 r3 -> Side stepRel (c :: ls) r1 r3

def Seg (stepRel : Call -> HalfTape -> HalfTape -> Prop)
    (ls_in ls_out : List Call) (w1 w2 : BitWord) : Prop :=
  ∀ r1 r2, Side stepRel ls_out r1 r2 -> Side stepRel ls_in (w1 +> r1) (w2 +> r2)

@[simp] theorem list_pow_zero {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem list_pow_succ {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem list_pow_one_add {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem list_pow_one {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
theorem list_pow_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, list_pow_succ, list_pow_succ, ih, List.append_assoc]

theorem side_append {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {ls1 ls2 : List Call} {r1 r2 r3 : HalfTape}
    (h1 : Side stepRel ls1 r1 r2) (h2 : Side stepRel ls2 r2 r3) :
    Side stepRel (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)

theorem side_append_inv {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {ls1 ls2 : List Call} {r1 r3 : HalfTape}
    (h : Side stepRel (ls1 ++ ls2) r1 r3) :
    ∃ r2, Side stepRel ls1 r1 r2 /\ Side stepRel ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1, Side.nil r1, h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc, hrest⟩
    rcases ih hrest with ⟨r2, h1, h2⟩
    exact ⟨r2, Side.cons hc h1, h2⟩

theorem seg_nil {stepRel : Call -> HalfTape -> HalfTape -> Prop} (w : BitWord) :
    Seg stepRel [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)

theorem seg_apply {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {ls1 ls2 : List Call} {w1 w2 : BitWord} {r1 r2 : HalfTape}
    (h1 : Seg stepRel ls1 ls2 w1 w2) (h2 : Side stepRel ls2 r1 r2) :
    Side stepRel ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2

theorem seg_append {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : BitWord}
    (h1 : Seg stepRel ls1 ls2 w1 w2) (h2 : Seg stepRel ls3 ls4 w2 w3) :
    Seg stepRel (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases side_append_inv h with ⟨r2, ha, hb⟩
  exact side_append (h1 r1 r2 ha) (h2 r2 r3 hb)

theorem seg_step1 {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r, (cR l c (w1 +> r)) [tm]⊢⁺ (cL l (w2 +> r))) :
    Seg (CallStep tm cR cL) [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)

theorem seg_step2 {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {c_in c_out : Call} {w1 w2 mid : BitWord}
    (h1 : ∀ l r, (cR l c_in (w1 +> r)) [tm]⊢⁺ (cR (mid +> l) c_out r))
    (h2 : ∀ l r, (cL (mid +> l) r) [tm]⊢⁺ (cL l (w2 +> r))) :
    Seg (CallStep tm cR cL) [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact stepPlus_trans (h1 l r1) (stepPlus_trans (hc1 (mid +> l)) (h2 l r2))

theorem seg_step3 {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
    (h1 : ∀ l r, (cR l c_in (w1 +> r)) [tm]⊢⁺ (cR (mid1 +> l) c1 r))
    (h2 : ∀ l r, (cL (mid1 +> l) r) [tm]⊢⁺ (cR (mid2 +> l) c2 r))
    (h3 : ∀ l r, (cL (mid2 +> l) r) [tm]⊢⁺ (cL l (w2 +> r))) :
    Seg (CallStep tm cR cL) [c_in] [c1, c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact stepPlus_trans (h1 l r1)
    (stepPlus_trans (hc1 (mid1 +> l))
      (stepPlus_trans (h2 l _)
        (stepPlus_trans (hc2 (mid2 +> l)) (h3 l r3))))

theorem seg_step3_eq {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
    (h1 : ∀ l r, cR l c_in (w1 +> r) = cR (mid1 +> l) c1 r)
    (h2 : ∀ l r, (cL (mid1 +> l) r) [tm]⊢⁺ (cR (mid2 +> l) c2 r))
    (h3 : ∀ l r, (cL (mid2 +> l) r) [tm]⊢⁺ (cL l (w2 +> r))) :
    Seg (CallStep tm cR cL) [c_in] [c1, c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  rw [h1 l r1]
  exact stepPlus_trans (hc1 (mid1 +> l))
    (stepPlus_trans (h2 l _)
      (stepPlus_trans (hc2 (mid2 +> l)) (h3 l r3)))

structure SegRules (stepRel : Call -> HalfTape -> HalfTape -> Prop) : Prop where
  cp_t : Seg stepRel [.cp] [] t (t ++ one)
  cj_t : Seg stepRel [.cj] [.cj] t t
  ch_t : Seg stepRel [.ch] [.ch, .ch] t t
  cp_d1_d0 : Seg stepRel [.cp] [] (d1 ++ d0) (t ++ one)
  ch_t_one : Seg stepRel [.ch] [.cj, .ch] (t ++ one) t
  cj_d1_d0 : Seg stepRel [.cj] [.cj] (d1 ++ d0) t
  cp_d1_d1 : Seg stepRel [.cp] [.cp] (d1 ++ d1) t
  cj_d1_d1 : Seg stepRel [.cj] [.cp, .ch] (d1 ++ d1) t
  cj_d0 : Seg stepRel [.cj] [] d0 (d0 ++ one)
  ch_d0_one : Seg stepRel [.ch] [] (d0 ++ one) (d1 ++ one)
  ch_d1_one : Seg stepRel [.ch] [.cj] (d1 ++ one) d0
  cj_d1 : Seg stepRel [.cj] [.cp] d1 d0
  ch_d0 : Seg stepRel [.ch] [] d0 d1
  ch_d1 : Seg stepRel [.ch] [.ch] d1 d0
  ca_nil : Seg stepRel [.ca] [.cj, .ch] [] t

theorem seg_ch_pow_t {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact seg_nil t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [list_pow_succ, h_eq, list_pow_add]
    exact seg_append rules.ch_t ih

theorem seg_ch_pow_half {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {w2 : BitWord} (hw : Seg stepRel [.ch, .ch] [.ch] w2 w2) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact seg_nil w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, list_pow_add, list_pow_succ]
    exact seg_append hw ih

theorem seg_ch2_d0 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) : Seg stepRel [.ch, .ch] [.ch] d0 d0 :=
  seg_append rules.ch_d0 rules.ch_d1

theorem seg_ch2_d1 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) : Seg stepRel [.ch, .ch] [.ch] d1 d1 :=
  seg_append rules.ch_d1 rules.ch_d0

theorem seg_cp_ch_t {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [list_pow_one_add, List.cons_append, List.nil_append] using
    seg_append (seg_append rules.cp_t rules.ch_t_one) (seg_ch_pow_t rules n)

theorem seg_cj_ch_t {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) t t :=
  seg_append rules.cj_t (seg_ch_pow_t rules n)

theorem seg_cp_ch_d1_d0 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [list_pow_one_add, List.cons_append, List.nil_append] using
    seg_append (seg_append rules.cp_d1_d0 rules.ch_t_one) (seg_ch_pow_t rules n)

theorem seg_cj_ch_d1_d0 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  seg_append rules.cj_d1_d0 (seg_ch_pow_t rules n)

theorem seg_cp_ch_d1_d1 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  seg_append rules.cp_d1_d1 (seg_ch_pow_t rules n)

theorem seg_cj_ch_d1_d1 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [list_pow_one_add, List.cons_append, List.nil_append] using
    seg_append rules.cj_d1_d1 (seg_ch_pow_t rules n)

theorem seg_cj_ch_d0_d0 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg stepRel [.cj, .ch, .ch] [.cj] d0 d0 :=
    seg_append rules.cj_d0 (seg_append rules.ch_d0_one rules.ch_d1_one)
  have h1 := seg_append h0 (seg_ch_pow_half (seg_ch2_d0 rules) n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq, list_pow_one_add, List.cons_append, List.nil_append] using h1

theorem seg_cj_ch_d1_d0_half {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  seg_append rules.cj_d1 (seg_ch_pow_half (seg_ch2_d0 rules) n)

theorem seg_cj_ch_d0_one {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) :
    Seg stepRel [.cj, .ch] [] d0 (d1 ++ one) :=
  seg_append rules.cj_d0 rules.ch_d0_one

theorem seg_cj_ch_d0_d1 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg stepRel [.cj, .ch, .ch, .ch] [.cj] d0 d1 :=
    seg_append rules.cj_d0 (seg_append rules.ch_d0_one (seg_append rules.ch_d1_one rules.ch_d0))
  have h1 := seg_append h0 (seg_ch_pow_half (seg_ch2_d1 rules) n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq, list_pow_one_add, List.cons_append, List.nil_append] using h1

theorem seg_cj_ch_d1_d1_half {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg stepRel [.cj, .ch] [.cp] d1 d1 := seg_append rules.cj_d1 rules.ch_d0
  have h1 := seg_append h0 (seg_ch_pow_half (seg_ch2_d1 rules) n)
  simpa only [list_pow_one_add, List.cons_append, List.nil_append] using h1

inductive BRIncs : Nat -> HalfTape -> HalfTape -> Prop where
  | zero (r : HalfTape) : BRIncs 0 r (one +> r)
  | T {n : Nat} {r r' : HalfTape} :
      BRIncs (n * 2) r r' -> BRIncs (1 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : HalfTape} :
      BRIncs (n * 2) r r' -> BRIncs (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : HalfTape} :
      BRIncs (1 + n * 2) r r' -> BRIncs (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : HalfTape} :
      BRIncs (n * 2) r r' -> BRIncs (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : HalfTape} :
      BRIncs (1 + n * 2) r r' -> BRIncs (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : HalfTape} :
      BRIncs (n * 2) r r' -> BRIncs (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : HalfTape} :
      BRIncs (1 + n * 2) r r' -> BRIncs (4 + n * 4) (d1 +> r) (d1 +> r')
inductive Binary : Nat -> Nat -> HalfTape -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)


theorem binary_bounds {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    0 < A /\ 0 < H /\ 2 ^ H <= A * 2 /\ A < 2 ^ H := by
  induction h with
  | one => decide
  | @zero n H r _ ih =>
    rw [pow_two_one_add H]; omega
  | @two n H r _ ih =>
    rw [pow_two_one_add H]; omega

theorem brIncs_of_binary {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    BRIncs ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := BRIncs.zero (default : HalfTape)
    have hd : d1 +> (default : HalfTape) = one +> default := by simp [d1,one]
    rw [hd]; exact h0
  | @zero n H r _ ih =>
    have ih' : BRIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := BRIncs.short00 ih'
    rw [append_d0_default] at hs
    have heq : ((2 + n * 2) - 1) * 2 = 2 + n * 4 := by omega
    rwa [heq]
  | @two n H r _ ih =>
    have ih' : BRIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := BRIncs.short10 ih'
    rw [append_d0_default] at hs
    have heq : ((3 + n * 2) - 1) * 2 = 4 + n * 4 := by omega
    rwa [heq]

theorem digitVal_unique {A H : Nat} {u : WordList} (h1 : DigitVal A H u) :
    ∀ {v : WordList},DigitVal A H v -> u = v := by
  induction h1 with
  | nil =>
    intro v h2
    cases v with
    | nil => rfl
    | cons w v' =>
      cases w with
      | V => exact False.elim (digitVal_not_cons_V h2)
      | K =>
        rcases digitVal_cons_K_inv h2 with ⟨_,_,_,_,h⟩
        (try omega)
      | Q =>
        rcases digitVal_cons_Q_inv h2 with ⟨_,_,_,_,h⟩
        (try omega)
  | @zero A H u _ ih =>
    intro v h2
    generalize hA_eq : A * 2 = A0 at h2
    generalize hH_eq : 1 + H = H0 at h2
    cases h2 with
    | nil => omega
    | @zero A' H' v' hD =>
      have hA : A = A' := by omega
      have hH : H = H' := by omega
      subst hA hH
      rw [ih hD]
    | one _ => omega
  | @one A H u _ ih =>
    intro v h2
    generalize hA_eq : 1 + A * 2 = A0 at h2
    generalize hH_eq : 1 + H = H0 at h2
    cases h2 with
    | nil => omega
    | zero _ => omega
    | @one A' H' v' hD =>
      have hA : A = A' := by omega
      have hH : H = H' := by omega
      subst hA hH
      rw [ih hD]

theorem scan_cons_Q_K_inv {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a (Q :: K :: u) b v l) :
    ∃ n w s,a = 1 + n /\ Scan (n * 2) u b w s /\ v = V :: w /\ l = (1 + s) * (1 / 2) := by
  cases hI with
  | @pair0 n _ _ w s hJ =>
    exact ⟨n,w,s,rfl,hJ,rfl,rfl⟩
  | @short01 n _ _ _ _ hJ =>
    exact False.elim (not_scan_odd_cons_K n u b _ _ hJ)
  | @short11 n _ _ _ _ hJ =>
    exact False.elim (not_scan_odd_cons_K n u b _ _ hJ)

inductive BScan : Nat -> WordList -> Nat -> WordList -> Rat -> Rat -> Prop where
  | nil (k : Nat) : BScan k [] k [] 0 0
  | T {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (1 + n) (V :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair0 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (1 + n) (Q :: K :: u) k (V :: v) (a * (1 / 2)) (b * (1 / 2))
  | pair1 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (1 + n) (Q :: Q :: u) k (V :: v) (a * (1 / 2)) ((1 / 4) +
          b * (1 / 2))
  | short00 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (2 + n * 4) (K :: u) k (K :: v) (2 + a * 2) (b * 2)
  | short01 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (2 + n * 4) (Q :: u) k (K :: v) (1 + a * 2) (b * 2)
  | short10 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (n * 2) u k v a b -> BScan (4 + n * 4) (K :: u) k (Q :: v) (3 + a * 2) (b * 2)
  | short11 {n : Nat} {u : WordList} {k : Nat} {v : WordList} {a b : Rat} :
      BScan (1 + n * 2) u k v a b -> BScan (4 + n * 4) (Q :: u) k (Q :: v) (2 + a * 2) (b * 2)

theorem bscan_scale_eq {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : BScan k u k' v a b) :
    (k : Rat) - 2 = ((k' : Rat) - 2) * wordScale v + 2 * (a - b) := by
  induction h with
  | nil k => simp [wordScale]
  | T _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [wordScale]; push_cast at ih ⊢; linarith

theorem bscan_mass_bounds {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : BScan k u k' v a b) :
    wordMass v <= wordMass u /\ 0 <= a /\ a <= 2 * wordMass u + wordMassK u /\ 0 <= b /\
    wordMass v + a - b - wordMassQ v <= 2 * wordMass u + wordMassK u := by
  induction h with
  | nil _ => simp [wordMass,wordMassK,wordMassQ]
  | @T n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @pair0 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @pair1 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @short00 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @short01 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @short10 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩
  | @short11 n u k v a b _ ih =>
    have hw := wordMass_nonneg u; have hm := wordMass_eq_add u
    dsimp [wordMass,wordMassK,wordMassQ]; refine ⟨by linarith,by linarith,by linarith,by linarith,by
        linarith⟩

theorem bscan_append {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h1 : BScan k u k' v a b) :
    ∀ {w : WordList} {k'' : Nat} {x : WordList} {c d : Rat},
      BScan k' w k'' x c d ->
      ∃ a' b',BScan k (u ++ w) k'' (v ++ x) a' b' /\
        a' = a + wordScale v * c /\ b' = b + wordScale v * d := by
  induction h1 with
  | nil _ =>
    intro w k'' x c d h2
    exact ⟨c,d,h2,by simp [wordScale],by simp [wordScale]⟩
  | T _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨a' * (1 / 2), b' * (1 / 2), BScan.T hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | pair0 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨a' * (1 / 2), b' * (1 / 2), BScan.pair0 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | pair1 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨a' * (1 / 2), (1 / 4) + b' * (1 / 2), BScan.pair1 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | short00 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨2 + a' * 2, b' * 2, BScan.short00 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | short01 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨1 + a' * 2, b' * 2, BScan.short01 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | short10 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨3 + a' * 2, b' * 2, BScan.short10 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith
  | short11 _ ih =>
    intro w k'' x c d h2
    rcases ih h2 with ⟨a', b', hK, hA, hB⟩
    refine ⟨2 + a' * 2, b' * 2, BScan.short11 hK, ?_, ?_⟩
    · dsimp [wordScale]; linarith
    · dsimp [wordScale]; linarith

theorem exists_bscan_of_wordPrefix {e : Bool} {u : WordList} (hI : WordPrefix e u) :
    ∀ (k : Nat),(e = true -> ∃ n,k = n * 2) ->
      6 * wordMass u < (k : Rat) - 2 ->
      ∃ b v lp lm,BScan k u b v lp lm /\ 2 < b := by
  induction hI with
  | nil e =>
    intro k _ hk
    dsimp [wordMass] at hk
    have hk_gt : (2 : Rat) < (k : Rat) := by linarith
    have hk_nat : 2 < k := by exact_mod_cast hk_gt
    exact ⟨k,[],0,0,BScan.nil k,hk_nat⟩
  | @T e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),lm * (1 / 2),BScan.T hS,hB⟩
  | @short0 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases even_or_odd_mul_two n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,3 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact BScan.short10 hS
    · rcases ih (a * 2) (fun _ => ⟨a,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,2 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact BScan.short00 hS
  | @short1 u _ ih =>
    intro k hEk hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    rcases hEk rfl with ⟨n,rfl⟩
    rcases even_or_odd_mul_two n with ⟨a,rfl⟩ | ⟨a,rfl⟩
    · cases a with
      | zero => push_cast at hk; linarith
      | succ a =>
        rcases ih (1 + a * 2) (fun h =>
            by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
        refine ⟨b,Q :: v,2 + lp * 2,lm * 2,?_,hB⟩
        have heq : (a + 1) * 2 * 2 = 4 + a * 4 := by omega
        rw [heq]; exact BScan.short11 hS
    · rcases ih (1 + a * 2) (fun h =>
        by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      refine ⟨b,K :: v,1 + lp * 2,lm * 2,?_,hB⟩
      have heq : (1 + a * 2) * 2 = 2 + a * 4 := by omega
      rw [heq]; exact BScan.short01 hS
  | @pair0 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (k * 2) (fun _ => ⟨k,rfl⟩) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),lm * (1 / 2),BScan.pair0 hS,hB⟩
  | @pair1 e u _ ih =>
    intro k _ hk
    have hw := wordMass_nonneg u
    dsimp [wordMass] at hk
    cases k with
    | zero => push_cast at hk; linarith
    | succ k =>
      have h1k : k + 1 = 1 + k := by omega
      rw [h1k] at hk ⊢
      rcases ih (1 + k * 2) (fun h =>
          by contradiction) (by push_cast at hk ⊢; linarith) with ⟨b,v,lp,lm,hS,hB⟩
      exact ⟨b,V :: v,lp * (1 / 2),(1 / 4) + lm * (1 / 2),BScan.pair1 hS,hB⟩

theorem exists_bscan_even (u : WordList) (k : Nat) (h : 6 * wordMass u < ((k * 2 : Nat) : Rat) - 2)
    :
    ∃ b v lp lm,BScan (k * 2) u b v lp lm /\ 2 < b :=
  exists_bscan_of_wordPrefix (wordPrefix_true_and_cases u).1 (k * 2) (fun _ => ⟨k,rfl⟩) h

theorem bscan_of_scan_digitVal {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {l : Rat}
    (hI : Scan k u k' v l) :
    ∀ {A H : Nat},DigitVal A H u ->
      ∃ a b,BScan k u k' v a b /\ a <= 2 * wordMass v + l /\ b <= l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,0,BScan.nil k,by simp [wordMass],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),b * (1 / 2),BScan.pair0 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨a * (1 / 2),(1 / 4) + b * (1 / 2),BScan.pair1 hJ,by dsimp [wordMass]; linarith,by
        linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨2 + a * 2,b * 2,BScan.short00 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨1 + a * 2,b * 2,BScan.short01 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨3 + a * 2,b * 2,BScan.short10 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨a,b,hJ,hP,hM⟩
    exact ⟨2 + a * 2,b * 2,BScan.short11 hJ,by dsimp [wordMass]; linarith,by linarith⟩

theorem scan_of_bscan_digitVal {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ {A H : Nat},DigitVal A H u ->
      ∃ l,Scan k u k' v l /\ a <= 2 * wordMass v + l /\ b <= l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [wordMass],by linarith⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hP,hM⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [wordMass]; linarith,by linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hP,hM⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [wordMass]; linarith,by linarith⟩

theorem bscan_scale_le {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : BScan k u k' v a b) : wordScale v <= wordScale u := by
  induction h with
  | nil _ => simp [wordScale]
  | T _ ih => dsimp [wordScale]; linarith
  | @pair0 _ u _ _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | @pair1 _ u _ _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [wordScale]; linarith
  | short01 _ ih => dsimp [wordScale]; linarith
  | short10 _ ih => dsimp [wordScale]; linarith
  | short11 _ ih => dsimp [wordScale]; linarith

set_option maxHeartbeats 800000 in
-- Justification: induction over all 8 BScan constructors with rational ring arithmetic.
theorem bscan_split {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (h : BScan k u k' v a b) :
    ∀ (p q : WordList),u = p ++ q -> SplitCond p q ->
      ∃ m x y a1 b1 a2 b2,BScan k p m x a1 b1 /\ BScan m q k' y a2 b2 /\
        v = x ++ y /\ a = a1 + wordScale x * a2 /\ b = b1 + wordScale x * b2 := by
  induction h with
  | nil k =>
    intro p q hE _
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨k,[],[],0,0,0,0,BScan.nil k,BScan.nil k,rfl,by simp [wordScale],by simp [wordScale]⟩
    | cons s p => simp at hE
  | T hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.T hI,rfl,by simp [wordScale],by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons V p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,V :: x,y,a1 * (1 / 2),b1 * (1 / 2),a2,b2,BScan.T hJ,hK,rfl,
        by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | pair0 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.pair0 hI,rfl,by simp [wordScale],by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := splitCond_of_cons K p q (splitCond_of_cons Q (K :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),b1 * (1 / 2),a2,b2,BScan.pair0 hJ,hK,rfl,
          by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | pair1 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.pair1 hI,rfl,by simp [wordScale],by simp [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      cases p with
      | nil =>
        simp at hE; subst hE
        rcases hP with hP | ⟨r,hP⟩ <;> nomatch hP
      | cons s2 p =>
        simp at hE; rcases hE with ⟨rfl,hE⟩
        have hP' := splitCond_of_cons Q p q (splitCond_of_cons Q (Q :: p) q hP)
        rcases ih p q hE hP' with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
        exact ⟨m,V :: x,y,a1 * (1 / 2),(1 / 4) + b1 * (1 / 2),a2,b2,BScan.pair1 hJ,hK,rfl,
          by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | short00 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short00 hI,rfl,by simp [wordScale],by simp
          [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,2 + a1 * 2,b1 * 2,a2,b2,BScan.short00 hJ,hK,rfl,
        by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | short01 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short01 hI,rfl,by simp [wordScale],by simp
          [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,K :: x,y,1 + a1 * 2,b1 * 2,a2,b2,BScan.short01 hJ,hK,rfl,
        by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | short10 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short10 hI,rfl,by simp [wordScale],by simp
          [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons K p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,3 + a1 * 2,b1 * 2,a2,b2,BScan.short10 hJ,hK,rfl,
        by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩
  | short11 hI ih =>
    intro p q hE hP
    cases p with
    | nil =>
      simp at hE; subst hE
      exact ⟨_,[],_,0,0,_,_,BScan.nil _,BScan.short11 hI,rfl,by simp [wordScale],by simp
          [wordScale]⟩
    | cons s p =>
      simp at hE; rcases hE with ⟨rfl,hE⟩
      rcases ih p q hE (splitCond_of_cons Q p q hP) with ⟨m,x,y,a1,b1,a2,b2,hJ,hK,rfl,hA,hB⟩
      exact ⟨m,Q :: x,y,2 + a1 * 2,b1 * 2,a2,b2,BScan.short11 hJ,hK,rfl,
        by dsimp [wordScale]; rw [hA]; ring,by dsimp [wordScale]; rw [hB]; ring⟩

theorem bscan_replicate_Q_K (r k : Nat) (u : WordList) (k' : Nat) (v : WordList) (a b : Rat)
    (hI : BScan k (u ++ List.replicate (1 + r * 2) Q ++ [K]) k' v a b) :
    ∃ w n,v = w ++ List.replicate (1 + r) V /\ k' = n * 2 ^ (1 + r) := by
  rcases split_trailing_Q u with ⟨p,n,rfl,hP⟩
  have hE : (p ++ List.replicate n Q) ++ List.replicate (1 + r * 2) Q ++ [K] =
      p ++ (List.replicate (1 + r * 2 + n) Q ++ [K]) := by
    have heq : 1 + r * 2 + n = n + (1 + r * 2) := by omega
    rw [heq,List.replicate_add n (1 + r * 2)]; simp only [List.append_assoc]
  rw [hE] at hI
  rcases bscan_split hI p (List.replicate (1 + r * 2 + n) Q ++ [K]) rfl (Or.inl hP)
    with ⟨m,x,y,_,_,_,_,_,hK,rfl,_,_⟩
  have hD : DigitVal ((2 ^ (1 + r * 2 + n) - 1) + 0 * 2 ^ (1 + r * 2 + n)) ((1 + r * 2 + n) + 1)
      (List.replicate (1 + r * 2 + n) Q ++ [K]) :=
    digitVal_append (digitVal_replicate_Q (1 + r * 2 + n)) (DigitVal.zero DigitVal.nil)
  rcases scan_of_bscan_digitVal hK hD with ⟨l,hL,_,_⟩
  rcases scan_add_Q_K_inv n r m k' y l hL with ⟨w,q,rfl,rfl⟩
  exact ⟨x ++ w,q,by rw [List.append_assoc],rfl⟩

theorem scan_defect_of_bscan_digitVal {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ {A H : Nat},DigitVal A H u ->
      ∃ l,Scan k u k' v l /\ a - b - wordMassQ v <= wordMass v + l := by
  induction hI with
  | nil k =>
    intro A H _
    exact ⟨0,Scan.nil k,by simp [wordMass,wordMassQ]⟩
  | T _ _ =>
    intro A H hD
    exact False.elim (digitVal_not_cons_V hD)
  | pair0 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 + l) * (1 / 2),Scan.pair0 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩
  | pair1 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_Q_inv hD1 with ⟨A2,H2,hD2,_,_⟩
    rcases ih hD2 with ⟨l,hJ,hL⟩
    exact ⟨(1 / 4) + l * (1 / 2),Scan.pair1 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩
  | short00 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short00 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩
  | short01 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short01 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩
  | short10 _ ih =>
    intro A H hD
    rcases digitVal_cons_K_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨1 + l * 2,Scan.short10 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩
  | short11 _ ih =>
    intro A H hD
    rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
    rcases ih hD1 with ⟨l,hJ,hL⟩
    exact ⟨l * 2,Scan.short11 hJ,by dsimp [wordMass,wordMassQ]; linarith⟩

theorem scan_append_K_bounds {k : Nat} {ds : WordList} {k' : Nat} {v : WordList} {l : Rat}
    (hI : Scan k (ds ++ [K]) k' v l)
    (hLow : ∃ w, ds = Q :: K :: w)
    (hDig : ∃ A H, DigitVal A H ds) :
    wordMass v <= wordMassK ds * (1 / 4) /\ wordMass v + l <= wordMassK ds * (1 / 2) + (1 / 2) := by
  rcases hLow with ⟨w,rfl⟩
  rcases hDig with ⟨A,H,hD⟩
  rcases digitVal_cons_Q_inv hD with ⟨A1,H1,hD1,_,_⟩
  rcases digitVal_cons_K_inv hD1 with ⟨A2,H2,hK,_,_⟩
  change Scan k (Q :: K :: (w ++ [K])) k' v l at hI
  rcases scan_cons_Q_K_inv hI with ⟨n,x,s,_,hJ,rfl,hL⟩
  rcases scan_tailDefect_bound hJ (tailDefect_append_K_of_digitVal hK) with ⟨hM,hS,_⟩
  dsimp [wordMassK,wordMass]
  constructor <;> linarith

theorem bscan_append_K_bounds {k : Nat} {ds : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : BScan k (ds ++ [K]) k' v a b)
    (hLow : ∃ w, ds = Q :: K :: w)
    (hDig : ∃ A H, DigitVal A H ds) :
    wordMass v <= wordMassK ds * (1 / 4) /\ a <= wordMassK ds /\
    wordMass v + a - b - wordMassQ v <= wordMassK ds := by
  rcases hDig with ⟨A,H,hD⟩
  have hFull := digitVal_append hD (DigitVal.zero DigitVal.nil)
  rcases scan_of_bscan_digitVal hI hFull with ⟨l,hJ,hP,_⟩
  rcases scan_defect_of_bscan_digitVal hI hFull with ⟨l',hJ',hE⟩
  rcases scan_append_K_bounds hJ hLow ⟨A,H,hD⟩ with ⟨hM1,hL1⟩
  rcases scan_append_K_bounds hJ' hLow ⟨A,H,hD⟩ with ⟨_,hL2⟩
  rcases hLow with ⟨w,rfl⟩
  have hw := wordMass_nonneg w
  dsimp [wordMassK] at hM1 hL1 hL2 ⊢
  refine ⟨by linarith,by linarith,by linarith⟩

set_option maxHeartbeats 800000 in
-- Justification: non-linear rational arithmetic for BScan split bounds.
theorem bscan_four_split {u : WordList} {A H : Nat} {ds : WordList} (hDig : DigitVal A H ds)
    (hHeight : wordScale u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hPhi : 3 * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 64)
    (hLow : ∃ w,ds = Q :: K :: w) :
    ∃ k v a b,BScan 4 (u ++ ds ++ [K]) k v a b /\ 2 < k /\
      a <= 2 * wordMass u + wordMassK u + wordScale u * wordMassK ds /\
      wordMass v <= wordMass u + wordScale u * wordMassK ds * (1 / 4) /\
      wordMass v + a - b - wordMassQ v <= 2 * wordMass u + wordMassK u + wordScale u * wordMassK
          ds := by
  have hWu := wordMass_nonneg u
  have hWd := wordMass_nonneg ds
  have hSu := wordScale_pos u
  have hSmall : 6 * wordMass u < ((2 * 2 : Nat) : Rat) - 2 := by
    push_cast; nlinarith
  rcases exists_bscan_even u 2 hSmall with ⟨m,x,a1,b1,hI,hPos⟩
  have hBudget := bscan_scale_eq hI
  have hBounds := bscan_mass_bounds hI
  have hGain := bscan_scale_le hI
  have hSx := wordScale_pos x
  have hCarry : 1 < (m : Rat) * wordScale x := by
    push_cast at hBudget; nlinarith
  rcases hLow with ⟨w,hEq⟩
  have hRest : (wordMass (w ++ [K]) + wordMassK (w ++ [K]) + 2) * wordScale x <= 1 := by
    have hDs := (digitVal_scale_and_mass hDig).1
    rw [<- hDs] at hHeight
    rw [hEq] at hDig hHeight
    dsimp [wordScale] at hHeight
    rcases digitVal_cons_Q_inv hDig with ⟨A1,H1,hD1,_,_⟩
    rcases digitVal_cons_K_inv hD1 with ⟨A2,H2,hJw,_,_⟩
    rcases digitVal_scale_and_mass hJw with ⟨hDw,hMw,_⟩
    have hWw := wordMass_nonneg w
    have hMsw := wordMass_eq_add w
    have hSw := wordScale_pos w
    rw [wordMass_append,wordMassK_append]
    dsimp [wordMass,wordMassK]
    nlinarith
  cases m with
  | zero => omega
  | succ m =>
    have hEx_w : (wordMass (w ++ [K]) + wordMassK (w ++ [K])) * 2 < ((m * 2 : Nat) : Rat) := by
      push_cast at hCarry ⊢; nlinarith
    rcases exists_scan_of_mass_lt (w ++ [K]) m hEx_w with ⟨k,y,l,hJ,_⟩
    have hCore : Scan (m + 1) (ds ++ [K]) k (V :: y) ((1 + l) * (1 / 2)) := by
      rw [hEq]
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      exact Scan.pair0 hJ
    have hFull := digitVal_append hDig (DigitVal.zero DigitVal.nil)
    rcases bscan_of_scan_digitVal hCore hFull with ⟨a2,b2,hJ',_,_⟩
    rcases bscan_append hI hJ' with ⟨a,b,hIJ,hAp,hBp⟩
    rcases bscan_append_K_bounds hJ' ⟨w,hEq⟩ ⟨A,H,hDig⟩ with ⟨hMt,hAt,hEt⟩
    have hIJ' : BScan 4 (u ++ ds ++ [K]) k (x ++ V :: y) a b := by
      simpa [List.append_assoc] using hIJ
    have hAfull : a <= 2 * wordMass u + wordMassK u + wordScale u * wordMassK ds := by
      nlinarith
    have hPositive : 2 < k := by
      have hB := bscan_scale_eq hIJ
      have hF := bscan_mass_bounds hIJ
      have hS := wordScale_pos (x ++ V :: y)
      have hk_gt : (2 : Rat) < (k : Rat) := by
        push_cast at hB; nlinarith
      exact_mod_cast hk_gt
    refine ⟨k,x ++ V :: y,a,b,hIJ',hPositive,hAfull,?_,?_⟩
    · rw [wordMass_append]; nlinarith
    · rw [wordMass_append,wordMassQ_append]; nlinarith

theorem bscan_replicate_V (p : Nat) :
    ∀ (k k' : Nat) (v : WordList) (a b : Rat),
      BScan k (List.replicate p V) k' v a b ->
      v = List.replicate p V /\ k' + 2 * 2 ^ p = k * 2 ^ p + 2 /\ a = 0 /\ b = 0 := by
  induction p with
  | zero =>
    intro k k' v a b hI
    cases hI
    exact ⟨rfl,by simp,rfl,rfl⟩
  | succ p ih =>
    intro k k' v a b hI
    cases hI with
    | @T n _ _ v0 a0 b0 hJ =>
      rcases ih (n * 2) k' v0 a0 b0 hJ with ⟨rfl,hEq,rfl,rfl⟩
      refine ⟨rfl,?_,by ring,by ring⟩
      calc k' + 2 * 2 ^ (p + 1)
        _ = (k' + 2 * 2 ^ p) + 2 * 2 ^ p := by rw [Nat.pow_succ]; ring
        _ = (n * 2 * 2 ^ p + 2) + 2 * 2 ^ p := by rw [hEq]
        _ = (1 + n) * 2 ^ (p + 1) + 2 := by rw [Nat.pow_succ]; ring

theorem heightShift_append (u : WordList) :
    ∀ (v : WordList) (h H : Nat),heightShift (u ++ v) h = some H ->
      ∃ j,heightShift u h = some j /\ heightShift v j = some H := by
  induction u with
  | nil =>
    intro v h H hE
    exact ⟨h,rfl,hE⟩
  | cons w u ih =>
    intro v h H hE
    cases w with
    | V => exact ih v (h + 1) H hE
    | K =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE
    | Q =>
      cases h with
      | zero => contradiction
      | succ h => exact ih v h H hE

theorem heightShift_replicate_V (n : Nat) :
    ∀ (h : Nat),heightShift (List.replicate n V) h = some (h + n) := by
  induction n with
  | zero => intro h; simp [heightShift]
  | succ n ih =>
    intro h
    dsimp [List.replicate,heightShift]
    rw [ih (h + 1)]
    congr 1; omega

theorem le_of_heightShift_replicate_V (u : WordList) (n h H : Nat)
    (hE : heightShift (u ++ List.replicate n V) h = some H) : n <= H := by
  rcases heightShift_append u (List.replicate n V) h H hE with ⟨j,_,hJ⟩
  rw [heightShift_replicate_V] at hJ
  injection hJ with hJ
  (try omega)

theorem exists_heightShift_of_mass_lt (u : WordList) :
    ∀ (h : Nat),wordMass u < ((2 ^ h : Nat) : Rat) -> ∃ H,heightShift u h = some H := by
  induction u with
  | nil => intro h _; exact ⟨h,rfl⟩
  | cons w u ih =>
    intro h hM
    cases w with
    | V =>
      dsimp [wordMass,heightShift] at hM ⊢
      apply ih (h + 1)
      rw [Nat.pow_succ]; push_cast at hM ⊢; linarith
    | K =>
      cases h with
      | zero =>
        have hw := (wordMass_nonneg u).1
        dsimp [wordMass] at hM; linarith
      | succ h =>
        dsimp [wordMass,heightShift] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith
    | Q =>
      cases h with
      | zero =>
        have hw := (wordMass_nonneg u).1
        dsimp [wordMass] at hM; linarith
      | succ h =>
        dsimp [wordMass,heightShift] at hM ⊢
        apply ih h
        rw [Nat.pow_succ] at hM; push_cast at hM ⊢; linarith

theorem bscan_bound_lt {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ (h H : Nat),heightShift v h = some H -> k < 2 ^ (1 + h) -> k' < 2 ^ (1 + H) := by
  induction hI with
  | nil k =>
    intro h H hHeight hBound
    injection hHeight with hEq; subst hEq; exact hBound
  | T _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | pair0 _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | pair1 _ ih =>
    intro h H hHeight hBound
    apply ih (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | short00 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short01 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short10 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short11 _ ih =>
    intro h H hHeight hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply ih h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega

theorem bscan_bound_lt_of_ne_nil {k : Nat} {u : WordList} {k' : Nat} {v : WordList} {a b : Rat}
    (hI : BScan k u k' v a b) :
    ∀ (h H : Nat),heightShift v h = some H -> u ≠ [] -> k <= 2 ^ (1 + h) -> k' < 2 ^ (1 + H) := by
  cases hI with
  | nil _ => intro _ _ _ hNe _; exact False.elim (hNe rfl)
  | T hSub =>
    intro h H hHeight _ hBound
    apply bscan_bound_lt hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | pair0 hSub =>
    intro h H hHeight _ hBound
    apply bscan_bound_lt hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | pair1 hSub =>
    intro h H hHeight _ hBound
    apply bscan_bound_lt hSub (h + 1) H hHeight
    have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
    rw [heq,pow_two_one_add (1 + h)]; omega
  | short00 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply bscan_bound_lt hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short01 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply bscan_bound_lt hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short10 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply bscan_bound_lt hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega
  | short11 hSub =>
    intro h H hHeight _ hBound
    cases h with
    | zero => contradiction
    | succ h =>
      apply bscan_bound_lt hSub h H hHeight
      have heq : 1 + (h + 1) = 1 + (1 + h) := by omega
      rw [heq,pow_two_one_add (1 + h),pow_two_one_add h] at hBound
      rw [pow_two_one_add h]; omega

def HasVPrefixK (u : WordList) : Prop :=
  ∃ p w,u = List.replicate (1 + p) V ++ K :: w

theorem hasVPrefixK_append (u v : WordList) (h : HasVPrefixK u) : HasVPrefixK (u ++ v) := by
  rcases h with ⟨p,w,rfl⟩
  exact ⟨p,w ++ v,by simp [List.append_assoc]⟩

theorem bscan_four_vPrefixK (p : Nat) (u : WordList) (k : Nat) (v : WordList) (a b : Rat)
    (hI : BScan 4 (List.replicate (1 + p) V ++ K :: u) k v a b) :
    ∃ w a' b',v = List.replicate (1 + p) V ++ K :: w /\ BScan (2 ^ (1 + p)) u k w a' b' := by
  rcases bscan_split hI (List.replicate (1 + p) V) (K :: u) rfl (Or.inl (notEndsWithQ_replicate_V (1
      + p)))
    with ⟨m,x,y,_,_,_,_,hJ,hK,rfl,_,_⟩
  rcases bscan_replicate_V (1 + p) 4 m x _ _ hJ with ⟨rfl,hEq,_,_⟩
  have hm : m = 2 + 2 ^ (1 + p) * 2 := by
    rw [pow_two_one_add p] at hEq ⊢; omega
  cases hK with
  | @short00 n _ _ w0 a0 b0 hSub =>
    have hn : n * 2 = 2 ^ (1 + p) := by
      rw [pow_two_one_add p] at hm ⊢; omega
    rw [hn] at hSub
    exact ⟨w0,a0,b0,rfl,hSub⟩
  | @short10 n _ _ _ _ _ _ =>
    rw [pow_two_one_add p] at hm; omega

theorem hasQKSubword_replicate_V_append (p : Nat) (u : WordList) : hasQKSubword (List.replicate p V
    ++ u) = hasQKSubword u := by
  induction p with
  | zero => rfl
  | succ p ih => exact ih

theorem bscan_four_preserves_vPrefixK {orig : WordList} {k : Nat} {v : WordList} {a b : Rat} {J :
    Nat}
    (hI : BScan 4 orig k v a b) (hGu : HasVPrefixK orig) (hPair : hasQKSubword orig = true)
    (hHeight : heightShift v 0 = some J) :
    HasVPrefixK (V :: v) /\ k < 2 ^ (1 + J) := by
  rcases hGu with ⟨p,u,rfl⟩
  rcases bscan_four_vPrefixK p u k v a b hI with ⟨w,a',b',rfl,hS⟩
  refine ⟨⟨1 + p,w,?_⟩,?_⟩
  · have hrep : List.replicate (1 + (1 + p)) V = V :: List.replicate (1 + p) V := by
      rw [Nat.add_comm 1 (1 + p),List.replicate_succ]
    rw [hrep,List.cons_append]
  · have hH : heightShift w p = some J := by
      rcases heightShift_append (List.replicate (1 + p) V) (K :: w) 0 J hHeight with ⟨j,h1,h2⟩
      rw [heightShift_replicate_V] at h1
      injection h1 with h1; subst h1
      have hp : 0 + (1 + p) = p + 1 := by omega
      rw [hp] at h2
      exact h2
    have hNe : u ≠ [] := by
      intro hEmpty
      subst hEmpty
      rw [hasQKSubword_replicate_V_append] at hPair
      contradiction
    exact bscan_bound_lt_of_ne_nil hS p J hH hNe (by omega)

theorem digitVal_mod_four_one {n H : Nat} {ds : WordList} (hD : DigitVal (1 + n * 4) H ds) (hH : 2
    <= H) :
    ∃ w,ds = Q :: K :: w := by
  generalize hA_eq : 1 + n * 4 = A at hD
  cases hD with
  | nil => omega
  | zero _ => omega
  | @one A1 H1 u1 hD1 =>
    have hA1 : A1 = n * 2 := by omega
    subst hA1
    generalize hA1_eq : n * 2 = A1' at hD1
    cases hD1 with
    | nil => omega
    | @zero A2 H2 w _ => exact ⟨w,rfl⟩
    | one _ => omega

theorem digitVal_suffix_six_Q {B H : Nat} {ds : WordList} {unit : Rat}
    (hD : DigitVal B H ds) (hU : 0 < unit)
    (hHeight : unit * ((2 ^ H : Nat) : Rat) = 1)
    (hZ : 2 <= wordMassK ds)
    (hSmall : unit * (1 + wordMassK ds) <= 1 / 64) :
    ∃ rest,ds = rest ++ List.replicate 6 Q := by
  have hH6 : 6 <= H := by
    by_contra hlt
    have hle : H <= 5 := by omega
    have hpow_le : 2 ^ H <= 32 := by
      calc 2 ^ H <= 2 ^ 5 := Nat.pow_le_pow_right (by decide) hle
      _ = 32 := by decide
    have hpow_q : ((2 ^ H : Nat) : Rat) <= 32 := by exact_mod_cast hpow_le
    nlinarith
  have hShift : unit * ((2 ^ (H - 6) : Nat) : Rat) = 1 / 64 := by
    have heq : H = (H - 6) + 6 := by omega
    have hpow : 2 ^ H = 2 ^ (H - 6) * 64 := by
      rw [heq,Nat.pow_add]; rfl
    have hpow_q : ((2 ^ H : Nat) : Rat) = ((2 ^ (H - 6) : Nat) : Rat) * 64 := by
      exact_mod_cast hpow
    rw [hpow_q] at hHeight
    linarith
  have hEq := digitVal_wordMassK_eq hD
  have hH_split : (H - 6) + 6 = H := by omega
  have hD' : DigitVal B ((H - 6) + 6) ds := by rwa [hH_split]
  apply digitVal_high_ones_suffix (H - 6) 6 B ds hD'
  have hL_q : ((2 ^ ((H - 6) + 6) : Nat) : Rat) <= ((B + 2 ^ (H - 6) : Nat) : Rat) := by
    rw [hH_split]
    push_cast at hEq hShift ⊢
    nlinarith
  exact_mod_cast hL_q

inductive BGood : WordList -> Prop where
  | intro (H : Nat) (u : WordList) (A : Nat) (ds : WordList) :
      DigitVal A H ds ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 1 / 2 ->
      HasVPrefixK u ->
      (∃ w,u = w ++ [V]) ->
      (∃ w,ds = Q :: K :: w) ->
      (∃ w,ds = w ++ List.replicate 6 Q) ->
      3 * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 64 ->
      BGood (u ++ ds)

inductive BStep : WordList -> WordList -> Prop where
  | intro (orig : WordList) (n : Nat) (v : WordList) (a b : Rat) (J : Nat) (ds : WordList) :
      BScan 4 (orig ++ [K]) (n * 2) v a b ->
      DigitVal (1 + n) J ds ->
      BStep orig (V :: (v ++ ds))

set_option maxHeartbeats 800000 in
-- Justification: non-linear rational potential bound across BStep transition.
theorem bstep_of_bgood {orig : WordList} (hG : BGood orig) :
    ∃ out,BStep orig out /\ BGood out := by
  rcases hG with ⟨H,u,A,ds,hDig,hHeight,hGu,_,hLow,hHigh,hPhi⟩
  have hWu := wordMass_nonneg u
  have hWd := wordMass_nonneg ds
  have hSu := wordScale_pos u
  rcases bscan_four_split hDig hHeight hPhi hLow with ⟨k,v,a,b,hI,_,hAp,hMass,hEnergy⟩
  have hMassSmall : wordMass v < 1 := by nlinarith
  have hMassSmall0 : wordMass v < ((2 ^ 0 : Nat) : Rat) := by push_cast; exact hMassSmall
  rcases exists_heightShift_of_mass_lt v 0 hMassSmall0 with ⟨J,hHv⟩
  have hUnit := heightShift_sound v 0 J hHv
  have hUnit1 : wordScale v * ((2 ^ J : Nat) : Rat) = 1 := by
    have h20 : ((2 ^ 0 : Nat) : Rat) = 1 := rfl
    rwa [h20] at hUnit
  rcases hHigh with ⟨hi,hHi⟩
  have hIH : BScan 4 ((u ++ hi ++ [Q]) ++ List.replicate (1 + 2 * 2) Q ++ [K]) k v a b := by
    have h6 : List.replicate 6 Q = [Q] ++ List.replicate (1 + 2 * 2) Q := rfl
    rw [hHi,h6] at hI
    simpa [List.append_assoc] using hI
  rcases bscan_replicate_Q_K 2 4 (u ++ hi ++ [Q]) k v a b hIH with ⟨last,n,hV,rfl⟩
  have hJ3 : 3 <= J := by
    apply le_of_heightShift_replicate_V last 3 0 J
    rw [<- hV]; exact hHv
  have hPair : hasQKSubword (u ++ ds ++ [K]) = true := by
    rcases hLow with ⟨w,rfl⟩
    have h10 : hasQKSubword (Q :: K :: w ++ [K]) = true := rfl
    have heq : u ++ (Q :: K :: w) ++ [K] = u ++ (Q :: K :: w ++ [K]) := by simp [List.append_assoc]
    rw [heq]
    exact hasQKSubword_append_right u _ h10
  rcases bscan_four_preserves_vPrefixK hI (hasVPrefixK_append (u ++
      ds) [K] (hasVPrefixK_append u ds hGu)) hPair hHv with ⟨hGuardV,hUpper⟩
  have hPow : 2 ^ J = 8 * 2 ^ (J - 3) := by
    have heq : J = 3 + (J - 3) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPow1 : 2 ^ (1 + J) = 16 * 2 ^ (J - 3) := by
    have heq : 1 + J = 4 + (J - 3) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hBound : 1 + n * 4 < 2 ^ J := by
    rw [hPow1] at hUpper
    rw [hPow]
    have : n * (2 ^ (1 + 2)) = n * 8 := rfl
    (try omega)
  rcases exists_digitVal_of_lt_pow J (1 + n * 4) hBound with ⟨ds',hD'⟩
  have hLow' : ∃ w,ds' = Q :: K :: w := digitVal_mod_four_one hD' (by omega)
  have hDef := digitVal_wordMassK_eq hD'
  have hBudget := bscan_scale_eq hI
  have hDeficit : wordScale v * wordMassK ds' = a - b - 3 * wordScale v := by
    have h1n4 : ((1 + n * 4 : Nat) : Rat) = 1 + (n : Rat) * 4 := by push_cast; ring
    have hn8 : ((n * 2 ^ (1 + 2) : Nat) : Rat) = (n : Rat) * 8 := by push_cast; ring
    have h4 : ((4 : Nat) : Rat) = 4 := rfl
    rw [h1n4] at hDef
    rw [hn8,h4] at hBudget
    have hSv_def : wordScale v * (wordMassK ds' + (1 + (n : Rat) * 4) + 1) = 1 := by
      rw [hDef]; exact hUnit1
    nlinarith
  have hPhiNew : 3 * wordMass (V :: v) + wordMassK (V :: v) + wordScale (V :: v) * wordMassK ds' <=
      (7 / 8) * (3 * wordMass u + wordMassK u + wordScale u * wordMassK ds) := by
    have hSv := wordScale_pos v
    have hSplit := wordMass_eq_add v
    dsimp [wordMass,wordMassK,wordScale]
    nlinarith
  have hHigh' : ∃ w,ds' = w ++ List.replicate 6 Q := by
    refine digitVal_suffix_six_Q hD' (wordScale_pos v) hUnit1 ?_ ?_
    · rcases hLow' with ⟨w,rfl⟩
      have hw := wordMass_nonneg w
      dsimp [wordMassK]; linarith
    · have hBnd := bscan_mass_bounds hI
      have hSv := wordScale_pos v
      nlinarith
  refine ⟨V :: (v ++ ds'),?_,?_⟩
  · refine BStep.intro (u ++ ds) (n * 4) v a b J ds' ?_ hD'
    have heq : (n * 4) * 2 = n * 2 ^ (1 + 2) := by ring
    rw [heq]
    simpa [List.append_assoc] using hI
  · have hOut_eq : V :: (v ++ ds') = (V :: v) ++ ds' := rfl
    rw [hOut_eq]
    refine BGood.intro J (V :: v) (1 + n * 4) ds' hD' ?_ hGuardV ?_ hLow' hHigh' (by linarith)
    · dsimp [wordScale]; linarith
    · refine ⟨V :: (last ++ [V, V]),?_⟩
      rw [hV]; simp [List.replicate,List.append_assoc]

theorem brIncs_of_bscan {a : Nat} {u : WordList} {b : Nat} {v : WordList} {lp lm : Rat}
    (h : BScan a u b v lp lm) :
    ∀ {r r' : HalfTape},BRIncs b r r' -> BRIncs a (evalWords u r) (evalWords v r') := by
  induction h with
  | nil _ => intro r r' hR; exact hR
  | T _ ih => intro r r' hR; exact BRIncs.T (ih hR)
  | pair0 _ ih => intro r r' hR; exact BRIncs.pair0 (ih hR)
  | pair1 _ ih => intro r r' hR; exact BRIncs.pair1 (ih hR)
  | short00 _ ih => intro r r' hR; exact BRIncs.short00 (ih hR)
  | short01 _ ih => intro r r' hR; exact BRIncs.short01 (ih hR)
  | short10 _ ih => intro r r' hR; exact BRIncs.short10 (ih hR)
  | short11 _ ih => intro r r' hR; exact BRIncs.short11 (ih hR)

theorem evalWords_zero_digitVal {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hZ : A = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A H u _ ih =>
    have hA0 : A = 0 := by omega
    change d0 +> evalWords u default = default
    rw [ih hA0,append_d0_default]
  | one _ => omega

theorem brIncs_of_digitVal_pos {A H : Nat} {da : WordList} (hD : DigitVal A H da) (hPos : 0 < A) :
    BRIncs ((A - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A H u _ ih =>
    have hA_pos : 0 < A := by omega
    have hIH := ih hA_pos
    have hs := BRIncs.short00 hIH
    rw [append_d0_default] at hs
    have heq : (A * 2 - 1) * 2 = 2 + (A - 1) * 4 := by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A H u hDu ih =>
    cases A with
    | zero =>
      change BRIncs 0 default (d1 +> evalWords u default)
      rw [evalWords_zero_digitVal hDu rfl]
      have h0 := BRIncs.zero (default : HalfTape)
      have hd : d1 +> (default : HalfTape) = one +> default := by simp
      rw [hd]; exact h0
    | succ A =>
      have hA_pos : 0 < A + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A + 1 - 1) * 2 = A * 2 := by omega
      rw [heq_in] at hIH
      have hs := BRIncs.short10 hIH
      rw [append_d0_default] at hs
      have heq : (1 + (A + 1) * 2 - 1) * 2 = 4 + A * 4 := by omega
      dsimp [evalWords]
      rwa [heq]

theorem brIncs_of_bstep {orig out : WordList} (hS : BStep orig out) :
    ∃ r,BRIncs 4 (evalWords orig default) r /\ evalWords out default = t +> r := by
  rcases hS with ⟨n,v,a,b,J,ds,hI,hD⟩
  refine ⟨evalWords v (evalWords ds default),?_,?_⟩
  · have hB : BRIncs (n * 2) default (evalWords ds default) := by
      have heq : n * 2 = ((1 + n) - 1) * 2 := by omega
      rw [heq]
      exact brIncs_of_digitVal_pos hD (by omega)
    have hR := brIncs_of_bscan hI hB
    simpa [evalWords_append,evalWords] using hR
  · simp [evalWords_append,evalWords]

def buildPrefix : Nat -> Nat -> Option (WordList)
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    match buildPrefix fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

theorem binary_of_buildPrefix (fuel : Nat) :
    ∀ (m : Nat) (ws : WordList),buildPrefix fuel m = some ws ->
      ∃ H,Binary m H (evalWords ws default) := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1,Binary.one⟩
    · dsimp [buildPrefix] at h
      cases hrec : buildPrefix fuel ((m + 2) / 2) with
      | none => rw [hrec] at h; contradiction
      | some ws' =>
        rw [hrec] at h
        injection h with h; subst h
        rcases ih ((m + 2) / 2) ws' hrec with ⟨H,hB⟩
        have hq : (m + 2) / 2 = 1 + ((m + 2) / 2 - 1) := by omega
        rw [hq] at hB
        rcases Nat.mod_two_eq_zero_or_one (m + 2) with hmod | hmod
        · have hcond : ((m + 2) % 2 == 0) = true := beq_iff_eq.mpr hmod
          rw [hcond]; dsimp [evalWords]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 2 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.zero hB
        · have hcond : ((m + 2) % 2 == 0) = false := beq_false_of_ne (by omega)
          rw [hcond]; dsimp [evalWords]
          refine ⟨1 + H,?_⟩
          have heq : m + 2 = 3 + ((m + 2) / 2 - 1) * 2 := by omega
          rw [heq]; exact Binary.two hB

def choiceNextA : ChoiceE -> Nat -> Nat
  | CT,n | CP0,n | CP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4

def choiceNextB : ChoiceE -> Nat -> Nat
  | CT,n | CP0,n | CS00,n | CS10,n => n * 2
  | CP1,n | CS01,n | CS11,n => 1 + n * 2

def evalCodeAux : CodeE -> Nat -> WordList -> Option (WordList)
  | .Stop n,k,u =>
    if k == n * 2 then
      if u.all isWordK then buildPrefix 64 (1 + n) else none
    else none
  | .More ch n c,k,u =>
    if k == choiceNextA ch n then
      match stripWordPrefix (choiceInWordsE ch) u with
      | none => none
      | some w =>
        match evalCodeAux c (choiceNextB ch n) w with
        | none => none
        | some v => some (choiceOutWordE ch :: v)
    else none

theorem brIncs_of_evalCodeAux (c : CodeE) :
    ∀ (k : Nat) (u v : WordList),evalCodeAux c k u = some v ->
      BRIncs k (evalWords u default) (evalWords v default) := by
  induction c with
  | Stop n =>
    intro k u v hE
    dsimp [evalCodeAux] at hE
    cases hk : (k == n * 2) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      have rfl_k : k = n * 2 := beq_iff_eq.mp hk
      subst rfl_k
      cases hu : u.all isWordK with
      | false => rw [hu] at hE; contradiction
      | true =>
        rw [hu] at hE
        dsimp at hE
        rw [evalWords_default_of_all_K u hu]
        rcases binary_of_buildPrefix 64 (1 + n) v hE with ⟨H,hB⟩
        have hR := brIncs_of_binary hB
        have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
        rwa [heq] at hR
  | More ch n c ih =>
    intro k u v hE
    dsimp [evalCodeAux] at hE
    cases hk : (k == choiceNextA ch n) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      dsimp at hE
      have rfl_k : k = choiceNextA ch n := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : stripWordPrefix (choiceInWordsE ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE
        dsimp at hE
        cases hC : evalCodeAux c (choiceNextB ch n) w with
        | none => rw [hC] at hE; contradiction
        | some x =>
          rw [hC] at hE
          injection hE with hE; subst hE
          have rfl_u := stripWordPrefix_sound (choiceInWordsE ch) u w hU
          subst rfl_u
          have hIH := ih (choiceNextB ch n) w x hC
          cases ch
          · exact BRIncs.T hIH
          · exact BRIncs.pair0 hIH
          · exact BRIncs.pair1 hIH
          · exact BRIncs.short00 hIH
          · exact BRIncs.short01 hIH
          · exact BRIncs.short10 hIH
          · exact BRIncs.short11 hIH

def evalCodeStep (c : CodeE) (u : WordList) : Option (WordList) :=
  match evalCodeAux c 4 (u ++ [K]) with
  | some v => some (V :: v)
  | none => none

theorem brIncs_of_evalCodeStep (c : CodeE) (u v : WordList) (h : evalCodeStep c u = some v) :
    ∃ r,BRIncs 4 (evalWords u default) r /\ evalWords v default = t +> r := by
  dsimp [evalCodeStep] at h
  cases hE : evalCodeAux c 4 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨evalWords w default,?_,rfl⟩
    have hR := brIncs_of_evalCodeAux c 4 (u ++ [K]) w hE
    simpa [evalWords_append,evalWords] using hR

inductive Rounds : HalfTape -> HalfTape -> Prop where
  | refl (r : HalfTape) : Rounds r r
  | next {r s t0 : HalfTape} :
      BRIncs 4 r s -> Rounds (t +> s) t0 -> Rounds r t0

def evalCodeList : List CodeE -> WordList -> Option (WordList)
  | [],u => some u
  | c :: cs,u =>
    match evalCodeStep c u with
    | none => none
    | some v => evalCodeList cs v

theorem rounds_of_evalCodeList (cs : List CodeE) :
    ∀ (u v : WordList),evalCodeList cs u = some v ->
      Rounds (evalWords u default) (evalWords v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact Rounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [evalCodeList] at h
    cases hW : evalCodeStep c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases brIncs_of_evalCodeStep c u w hW with ⟨r,hR,hEq⟩
      refine Rounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

theorem bgood_of_checks (u ds : WordList) (p : Nat)
    (hD : ds.all isDigitWord = true)
    (hS : wordScale u * wordScale ds = 1 / 2)
    (hGu : u = List.replicate (1 + p) V ++ K :: u.drop (2 + p))
    (hEnd : u = u.take (u.length - 1) ++ [V])
    (hLo : ds = Q :: K :: ds.drop 2)
    (hHi : ds = ds.take (ds.length - 6) ++ List.replicate 6 Q)
    (hF : 3 * wordMass u + wordMassK u + wordScale u * wordMassK ds <= 1 / 64) :
    BGood (u ++ ds) := by
  rcases exists_digitVal_of_all_isDigitWord ds hD with ⟨A,hI⟩
  refine BGood.intro ds.length u A ds hI ?_ ⟨p,u.drop (2 + p),hGu⟩
    ⟨u.take (u.length - 1),hEnd⟩ ⟨ds.drop 2,hLo⟩ ⟨ds.take (ds.length - 6),hHi⟩ hF
  rw [<- (digitVal_scale_and_mass hI).1]
  exact hS


inductive Num : Nat -> BitWord -> List Call -> Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

def NumRel (stepRel : Call -> HalfTape -> HalfTape -> Prop) (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs, Num k w hs -> Side stepRel hs (w +> r) r'

theorem numRel_zero_inv {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    {r r' : HalfTape} (h : NumRel stepRel 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

theorem numRel_T {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (n * 2) r r') : NumRel stepRel (1 + n) (t +> r) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil]
    cases m with
    | zero =>
      have hn0 : n * 2 = 0 := by omega
      rw [hn0] at hI
      have hr' := numRel_zero_inv hI
      subst hr'
      rw [<- append_assoc t one r]
      exact seg_apply rules.cp_t (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine seg_apply (seg_cp_ch_t rules m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil]
    refine seg_apply (seg_cj_ch_t rules m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

theorem numRel_pair0 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (n * 2) r r') : NumRel stepRel (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil, <- append_assoc d1 d0 r]
    cases m with
    | zero =>
      have hn0 : n * 2 = 0 := by omega
      rw [hn0] at hI
      have hr' := numRel_zero_inv hI
      subst hr'
      rw [<- append_assoc t one r]
      exact seg_apply rules.cp_d1_d0 (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine seg_apply (seg_cp_ch_d1_d0 rules m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil, <- append_assoc d1 d0 r]
    refine seg_apply (seg_cj_ch_d1_d0 rules m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

theorem numRel_pair1 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (1 + n * 2) r r') :
    NumRel stepRel (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil, <- append_assoc d1 d1 r]
    refine seg_apply (seg_cp_ch_d1_d1 rules m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using hI [] _ hN1
  | @even m =>
    simp only [append_nil, <- append_assoc d1 d1 r]
    refine seg_apply (seg_cj_ch_d1_d1 rules m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (1 + m * 2)
    simpa using hI [] _ hN1

theorem numRel_short00 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (n * 2) r r') : NumRel stepRel (2 + n * 4) (d0 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    cases n with
    | zero =>
      have hr' := numRel_zero_inv hI
      subst hr'
      rw [<- append_assoc d0 one r]
      exact seg_apply rules.cj_d0 (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine seg_apply (seg_cj_ch_d0_d0 rules n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2

theorem numRel_short01 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (1 + n * 2) r r') :
    NumRel stepRel (2 + n * 4) (d1 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    refine seg_apply (seg_cj_ch_d1_d0_half rules n) ?_
    simpa using hI [] _ (Num.odd n)

theorem numRel_short10 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (n * 2) r r') : NumRel stepRel (4 + n * 4) (d0 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    cases n with
    | zero =>
      have hr' := numRel_zero_inv hI
      subst hr'
      rw [<- append_assoc d1 one r]
      exact seg_apply (seg_cj_ch_d0_one rules) (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine seg_apply (seg_cj_ch_d0_d1 rules n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2

theorem numRel_short11 {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRel stepRel (1 + n * 2) r r') :
    NumRel stepRel (4 + n * 4) (d1 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    refine seg_apply (seg_cj_ch_d1_d1_half rules n) ?_
    simpa using hI [] _ (Num.odd n)

theorem numRel_of_brIncs {stepRel : Call -> HalfTape -> HalfTape -> Prop}
    (rules : SegRules stepRel) {k : Nat} {r r' : HalfTape} (hI : BRIncs k r r') :
    NumRel stepRel k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
  | T _ ih => exact numRel_T rules ih
  | pair0 _ ih => exact numRel_pair0 rules ih
  | pair1 _ ih => exact numRel_pair1 rules ih
  | short00 _ ih => exact numRel_short00 rules ih
  | short01 _ ih => exact numRel_short01 rules ih
  | short10 _ ih => exact numRel_short10 rules ih
  | short11 _ ih => exact numRel_short11 rules ih

theorem brIncs4_step {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    (rules : SegRules (CallStep tm cR cL))
    (h_cl_to_cf : ∀ r, (cL lh r) [tm]⊢⁺ (cR lh .ca r))
    {r r' : HalfTape} (hI : BRIncs 4 r r') :
    (cR lh .ca r) [tm]⊢⁺ (cR lh .ca (t +> r')) := by
  have hC := numRel_of_brIncs rules hI [] ([.cj] ++ [.ch] ^ 1) (Num.even 1)
  have hS := seg_apply rules.ca_nil hC
  dsimp at hS
  rcases hS with _ | ⟨hca, hnil⟩
  cases hnil
  exact stepPlus_trans (hca lh) (h_cl_to_cf (t +> r'))

theorem bstep_cfg_step {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    (rules : SegRules (CallStep tm cR cL))
    (h_cl_to_cf : ∀ r, (cL lh r) [tm]⊢⁺ (cR lh .ca r))
    {orig out : WordList} (hS : BStep orig out) :
    (cR lh .ca (evalWords orig default)) [tm]⊢⁺ (cR lh .ca (evalWords out default)) := by
  rcases brIncs_of_bstep hS with ⟨r, hI, hEq⟩
  rw [hEq]
  exact brIncs4_step rules h_cl_to_cf hI

theorem rounds_cfg_steps {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    (rules : SegRules (CallStep tm cR cL))
    (h_cl_to_cf : ∀ r, (cL lh r) [tm]⊢⁺ (cR lh .ca r))
    {r r' : HalfTape} (h : Rounds r r') :
    (cR lh .ca r) [tm]⊢* (cR lh .ca r') := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hR _ ih =>
    rcases brIncs4_step rules h_cl_to_cf hR with ⟨n, _, hn⟩
    rcases ih with ⟨m, hm⟩
    exact ⟨n + m, multiStep_trans tm _ _ _ n m hn hm⟩

theorem multiStep_isSome_of_add {tm : Machine (Fin 2) (Fin 6)}
    {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep tm c (j + d) = some c') :
    (multiStep tm c j).isSome := by
  rw [multiStep_add] at h
  cases h_j : multiStep tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

theorem reach_bgood_at {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    (rules : SegRules (CallStep tm cR cL))
    (h_cl_to_cf : ∀ r, (cL lh r) [tm]⊢⁺ (cR lh .ca r))
    {r_init : HalfTape} {w_init : WordList}
    (h_init : (init []) [tm]⊢⁺ (cR lh .ca r_init))
    (h_rounds : Rounds r_init (evalWords w_init default))
    (h_bgood : BGood w_init) (m : Nat) :
    ∃ N ≥ m, ∃ w, multiStep tm (init []) N = some (cR lh .ca (evalWords w default)) /\ BGood w := by
  induction m with
  | zero =>
    rcases h_init with ⟨k1, _, hk1⟩
    rcases rounds_cfg_steps rules h_cl_to_cf h_rounds with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, w_init,
      multiStep_trans tm _ _ _ k1 k2 hk1 hk2, h_bgood⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, w, h_ms, h_good⟩
    rcases bstep_of_bgood h_good with ⟨w', hStep, h_good'⟩
    rcases bstep_cfg_step rules h_cl_to_cf hStep with ⟨k, hk_pos, h_step_k⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, w',
      multiStep_trans tm _ _ _ N k h_ms h_step_k, h_good'⟩

theorem does_not_halt_of_segRules {tm : Machine (Fin 2) (Fin 6)}
    {cR : HalfTape -> Call -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    {cL : HalfTape -> HalfTape -> Cfg (Fin 2) (Fin 6)}
    (rules : SegRules (CallStep tm cR cL))
    (h_cl_to_cf : ∀ r, (cL lh r) [tm]⊢⁺ (cR lh .ca r))
    {r_init : HalfTape} {w_init : WordList}
    (h_init : (init []) [tm]⊢⁺ (cR lh .ca r_init))
    (h_rounds : Rounds r_init (evalWords w_init default))
    (h_bgood : BGood w_init) :
    IsNotHalt tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases reach_bgood_at rules h_cl_to_cf h_init h_rounds h_bgood (n + 1) with ⟨N, hN, _, h_N, _⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [<- h_eq] at h_N
  have h_some := multiStep_isSome_of_add h_N
  rw [multiStep_succ, hn] at h_some
  exact h_some

def callState : Call -> Fin 6
  | .ch => B
  | .cj => A
  | .cp => A
  | .ca => A

def cfgR (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ((l <+ callWord c) {{callState c}}> r)

def cfgL (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (l <{{C}} ([0] +> r))

def cfgF (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  cfgR lh .ca r

syntax "run_0lb" : tactic
macro_rules
  | `(tactic| run_0lb) =>
    `(tactic| (
      dsimp [cfgR, cfgL, callWord, callState, t, d0, d1, one]
      try simp only [List.cons_append, List.nil_append, append_cons, append_nil]
      execute))

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 8000000 in
-- Justification: symbolic execution of all 15 elementary segment transitions for target_tm.
theorem segRules_0lb : SegRules (CallStep target_tm cfgR cfgL) where
  cp_t := seg_step1 (fun _ _ => by run_0lb)
  cj_t := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  ch_t := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_0lb) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cp_d1_d0 := seg_step1 (fun _ _ => by run_0lb)
  ch_t_one := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_0lb) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cj_d1_d0 := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cp_d1_d1 := seg_step2 (mid := [1, 0, 1, 0]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cj_d1_d1 := seg_step3 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by run_0lb) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cj_d0 := seg_step1 (fun _ _ => by run_0lb)
  ch_d0_one := seg_step1 (fun _ _ => by run_0lb)
  ch_d1_one := seg_step2 (mid := [1, 1]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  cj_d1 := seg_step2 (mid := [1, 1]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  ch_d0 := seg_step1 (fun _ _ => by run_0lb)
  ch_d1 := seg_step2 (mid := [1, 1]) (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)
  ca_nil := seg_step3_eq (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
    (fun _ _ => by unfold cfgR callWord callState; simp only [append_cons, append_nil])
    (fun _ _ => by run_0lb) (fun _ _ => by run_0lb)

theorem cl_to_cf (r : HalfTape) :
    (cfgL lh r) [target_tm]⊢⁺ (cfgR lh .ca r) := by
  unfold cfgL cfgR lh callWord callState
  simp only [append_cons, append_nil]
  execute

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 2000000 in
-- Justification: symbolic execution of 58-step initial transition to canonical configuration.
theorem init_to_cf :
    (init []) [target_tm]⊢⁺ (cfgR lh .ca default) := by
  have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
  rw [h_init]
  unfold cfgR lh callWord callState
  simp only [append_cons, append_nil]
  execute

def initWords : WordList := []

def initCodes : List CodeE := [
  (.More CS10 0 (.Stop 0)),
  (.More CT 3 (.More CS01 1 (.More CP0 2 (.Stop 2)))),
  (.More CT 3 (.More CT 5 (.More CS00 2 (.More CT 3 (.More CS01 1 (.More CP0 2 (.Stop 2))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CS00 4 (.More CT 7 (.More CS00 3 (.More CT 5 (.More
      CS01 2 (.More CP0 4 (.Stop 4)))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CS00 8 (.More CT 15 (.More CS00 7 (.More
      CT 13 (.More CS00 6 (.More CT 11 (.More CP0 21 (.More CP0 41 (.Stop 41))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CS00 16 (.More CT 31 (.More
      CS00 15 (.More CT 29 (.More CS00 14 (.More CT 27 (.More CT 53 (.More CT 105 (.More CS00 52
      (.More CP0 103 (.More CP0 205 (.More CP0 409 (.Stop 409)))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CS00 32 (.More
      CT 63 (.More CS00 31 (.More CT 61 (.More CS00 30 (.More CT 59 (.More CT 117 (.More CT 233
      (.More CS00 116 (.More CT 231 (.More CT 461 (.More CT 921 (.More CS00 460 (.More CP0 919
      (.More CS01 459 (.More CP0 918 (.More CS10 458 (.More CS11 228 (.More CP0 456 (.Stop
      456)))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More
      CS00 64 (.More CT 127 (.More CS00 63 (.More CT 125 (.More CS00 62 (.More CT 123 (.More CT 245
      (.More CT 489 (.More CS00 244 (.More CT 487 (.More CT 973 (.More CT 1945 (.More CS00 972
      (.More CT 1943 (.More CS00 971 (.More CT 1941 (.More CP1 3881 (.More CT 7762 (.More CP0 15523
      (.More CS00 7761 (.More CP0 15521 (.More CS00 7760 (.More CP1 15519 (.More CP0 31038 (.Stop
      31038)))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CS00 128 (.More CT 255 (.More CS00 127 (.More CT 253 (.More CS00 126 (.More CT 251
      (.More CT 501 (.More CT 1001 (.More CS00 500 (.More CT 999 (.More CT 1997 (.More CT 3993
      (.More CS00 1996 (.More CT 3991 (.More CS00 1995 (.More CT 3989 (.More CT 7977 (.More CT 15953
      (.More CT 31905 (.More CS00 15952 (.More CT 31903 (.More CS00 15951 (.More CT 31901 (.More CT
      63801 (.More CS01 31900 (.More CP1 63800 (.More CP1 127600 (.More CP0 255200 (.More CS10
      127599 (.More CP0 255197 (.More CS00 127598 (.More CS11 63798 (.More CP1 127596 (.More CP0
      255192 (.Stop 255192))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CT 513 (.More CS00 256 (.More CT 511 (.More CS00 255 (.More CT 509 (.More CS00 254
      (.More CT 507 (.More CT 1013 (.More CT 2025 (.More CS00 1012 (.More CT 2023 (.More CT 4045
      (.More CT 8089 (.More CS00 4044 (.More CT 8087 (.More CS00 4043 (.More CT 8085 (.More CT 16169
      (.More CT 32337 (.More CT 64673 (.More CS00 32336 (.More CT 64671 (.More CS00 32335 (.More CT
      64669 (.More CT 129337 (.More CS00 64668 (.More CT 129335 (.More CT 258669 (.More CT 517337
      (.More CS01 258668 (.More CT 517336 (.More CS10 258667 (.More CS01 129333 (.More CT 258666
      (.More CT 517331 (.More CP0 1034661 (.More CS00 517330 (.More CS11 258664 (.More CP0 517328
      (.More CS11 258663 (.More CP0 517326 (.More CS10 258662 (.More CP0 517323 (.More CS00 258661
      (.More CP1 517321 (.More CP1 1034642 (.More CP0 2069284 (.Stop
      2069284)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 3 (.More CT 5 (.More CT 9 (.More CT 17 (.More CT 33 (.More CT 65 (.More CT 129 (.More CT
      257 (.More CT 513 (.More CT 1025 (.More CS00 512 (.More CT 1023 (.More CS00 511 (.More CT 1021
      (.More CS00 510 (.More CT 1019 (.More CT 2037 (.More CT 4073 (.More CS00 2036 (.More CT 4071
      (.More CT 8141 (.More CT 16281 (.More CS00 8140 (.More CT 16279 (.More CS00 8139 (.More CT
      16277 (.More CT 32553 (.More CT 65105 (.More CT 130209 (.More CS00 65104 (.More CT 130207
      (.More CS00 65103 (.More CT 130205 (.More CT 260409 (.More CS00 130204 (.More CT 260407 (.More
      CT 520813 (.More CT 1041625 (.More CS00 520812 (.More CT 1041623 (.More CP0 2083245 (.More CT
      4166489 (.More CT 8332977 (.More CT 16665953 (.More CS00 8332976 (.More CS11 4166487 (.More CT
      8332974 (.More CS11 4166486 (.More CT 8332972 (.More CS11 4166485 (.More CT 8332970 (.More
      CS10 4166484 (.More CT 8332967 (.More CT 16665933 (.More CT 33331865 (.More CP0 66663729
      (.More CP0 133327457 (.More CS00 66663728 (.More CP0 133327455 (.More CS00 66663727 (.More
      CS01 33331863 (.More CP0 66663726 (.More CS10 33331862 (.More CP0 66663723 (.More CS00
      33331861 (.More CS01 16665930 (.More CP1 33331860 (.More CP1 66663720 (.More CP0 133327440
      (.Stop 133327440))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def initU : WordList :=
    [V, V, V, V, V, V, V, V, V, V, V, K, V, K, V, K, V, V, V, K, V, V, V, K, V, K, V, V, V, V, K, V,
        K, V, V, K, V, V, V, K, V, V, V, V, V, K, Q, V, Q, V, Q, V, Q, V, V, V, V, V, K, V, K, K, V,
        Q, V, K, K, V, V, V]

def initDs : WordList :=
    [Q, K, K, K, Q, K, Q, K, K, Q, K, Q, K, Q, Q, K, K, Q, K, K, Q, Q, Q, Q, Q, Q, Q]


set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
-- Justification: kernel evaluation of 11-round CodeE trace certificate.
theorem init_rounds :
    Rounds default (evalWords (initU ++ initDs) default) := by
  have h1 : Rounds (evalWords initWords default) (evalWords (initU ++ initDs) default) := by
    apply rounds_of_evalCodeList initCodes
    decide
  simpa [initWords, evalWords] using h1

set_option maxRecDepth 4000000 in
set_option maxHeartbeats 4000000 in
-- Justification: rational arithmetic evaluation of wordMass and wordScale on 97-word list.
theorem init_bgood :
    BGood (initU ++ initDs) := by
  apply bgood_of_checks initU initDs 10
  · decide
  · norm_num [initU, initDs, wordScale]
  · decide
  · decide
  · decide
  · decide
  · norm_num [initU, initDs, wordMass, wordMassK, wordScale]

end Solution

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm :=
  does_not_halt_of_segRules segRules_0lb cl_to_cf init_to_cf init_rounds init_bgood

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RE_1LC1RA_1LD0LC_1RA0LA_1RA1RF_0LBHHH
