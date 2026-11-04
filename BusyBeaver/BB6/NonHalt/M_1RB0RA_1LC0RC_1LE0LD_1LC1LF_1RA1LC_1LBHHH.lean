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

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LBHHH

@[expose] public section

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LBHHH"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

variable {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
-- A..F inherited directly from SixState
abbrev HalfTape := ListBlank (Fin 2)
abbrev BitWord := List (Fin 2)

@[simp] theorem multiStep_zero_eq (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) :
    multiStep M config 0 = some config := rfl
@[simp] theorem multiStep_one_eq (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) :
    multiStep M config 1 = step M config := rfl
@[simp] theorem multiStep_succ_eq (M : Machine Γ₀ Λ₀) (config : Cfg Γ₀ Λ₀) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] theorem zero_shift_default : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head_zero : (default : HalfTape).head = 0 := rfl
@[simp] theorem default_tail_default : (default : HalfTape).tail = default := rfl
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
theorem multiStep_add_bind {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 : Cfg Γ₀ Λ₀) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ_eq, ih, Option.bind_assoc]
    simp_rw [multiStep_succ_eq]
theorem multiStep_trans_add {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 c_3 : Cfg Γ₀ Λ₀) (n m : Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [multiStep_add_bind, h₁]; simp [h₂]
theorem stepPlus_to_stepStar {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 : Cfg Γ₀ Λ₀} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
theorem stepPlus_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans_add tm c_1 c_2 c_3 n m hn hm⟩
theorem stepPlus_stepStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m),
    multiStep_trans_add tm c_1 c_2 c_3 n m hn hm⟩
theorem step_stepStar_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  stepPlus_stepStar_trans (step_to_stepPlus tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| exists 0 <;> fail)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_to_stepStar ?_) <;>
    refine step_stepStar_trans (by
      (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
        Turing.ListBlank.head_cons, default_head_zero]);
      rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write,
      zero_shift_default, default_head_zero, default_tail_default])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev t : BitWord := [1, 1, 0, 0]
abbrev d0 : BitWord := [0, 0]
abbrev d1 : BitWord := [1, 0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default

@[simp] theorem d0_append_default : d0 +> (default : HalfTape) = default := by
  simp

inductive Call where
  | ch
  | cj
  | cp
  | ca

def callState (st_ch st_c : Fin 6) : Call → Fin 6
  | .ch => st_ch
  | .cj => st_c
  | .cp => st_c
  | .ca => st_c

def callWord : Call → BitWord
  | .ch => [1]
  | .cj => [1, 1]
  | .cp => [1, 0]
  | .ca => [1, 1, 1, 0, 1, 0]

def cfgCR (mir : Bool) (st_ch st_c : Fin 6) (l : HalfTape) (c : Call) (r : HalfTape) :
    Cfg (Fin 2) (Fin 6) :=
  if mir then ((l <+ callWord c) {{callState st_ch st_c c}}> r)
  else (r <{{callState st_ch st_c c}} (l <+ callWord c))

def cfgCL (mir : Bool) (st_ret : Fin 6) (l : HalfTape) (r : HalfTape) :
    Cfg (Fin 2) (Fin 6) :=
  if mir then (l <{{st_ret}} ([0] +> r))
  else (([0] +> r) {{st_ret}}> l)

def cfgCf (mir : Bool) (st_ret : Fin 6) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  cfgCL mir st_ret lh r

def callStep (tm : Machine (Fin 2) (Fin 6))
    (fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6))
    (fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6))
    (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l, (fCR l c r1) [tm]⊢⁺ (fCL l r2)

inductive Side (cs : Call → HalfTape → HalfTape → Prop) :
    List Call → HalfTape → HalfTape → Prop where
  | nil (r : HalfTape) : Side cs [] r r
  | cons {c : Call} {ls : List Call} {r1 r2 r3 : HalfTape} :
      cs c r1 r2 → Side cs ls r2 r3 → Side cs (c :: ls) r1 r3

def Seg (cs : Call → HalfTape → HalfTape → Prop)
    (ls_in ls_out : List Call) (w1 w2 : BitWord) : Prop :=
  ∀ r1 r2, Side cs ls_out r1 r2 → Side cs ls_in (w1 +> r1) (w2 +> r2)

structure SegRules (cs : Call → HalfTape → HalfTape → Prop) : Prop where
  r0b : Seg cs [.cp] [.cj] t t
  r0c : Seg cs [.cj] [.cj, .ch] t t
  r0d : Seg cs [.ch] [.ch, .ch] t t
  r0e : Seg cs [.cp] [] (d1 ++ d0) (t ++ one)
  rH2 : Seg cs [.ch] [.cj, .ch] (t ++ one) t
  r0f : Seg cs [.cj] [.cj] (d1 ++ d0) t
  r0g : Seg cs [.cp] [.cp] (d1 ++ d1) t
  r0h : Seg cs [.cj] [.cp, .ch] (d1 ++ d1) t
  r0i : Seg cs [.cj] [] d0 (d0 ++ one)
  rH1 : Seg cs [.ch] [] (d0 ++ one) (d1 ++ one)
  rH3 : Seg cs [.ch] [.cj] (d1 ++ one) d0
  r0j : Seg cs [.cj] [.cp] d1 d0
  rH0 : Seg cs [.ch] [] d0 d1
  rH4 : Seg cs [.ch] [.ch] d1 d0
  r0k : Seg cs [.ca] [.cj] [] t

inductive InitKind where
  | kindA
  | kindB
  | kindC
  | kindD

def initTape : InitKind → HalfTape
  | .kindA => d1 +> default
  | .kindB => t +> (d1 +> (d1 +> default))
  | .kindC => d0 +> (d1 +> default)
  | .kindD => t +> default

theorem seg_of_step4 {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r, (fCR l c (w1 +> r)) [tm]⊢⁺ (fCL l (w2 +> r))) :
    Seg (callStep tm fCR fCL) [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)

theorem seg_of_step2 {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c_in c_out : Call} {w1 w2 mid : BitWord}
    (h1 : ∀ l r, (fCR l c_in (w1 +> r)) [tm]⊢⁺ (fCR (mid +> l) c_out r))
    (h2 : ∀ l r, (fCL (mid +> l) r) [tm]⊢⁺ (fCL l (w2 +> r))) :
    Seg (callStep tm fCR fCL) [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact stepPlus_trans (h1 l r1) (stepPlus_trans (hc1 (mid +> l)) (h2 l r2))

theorem seg_of_step5 {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c_in c1 c2 : Call} {w1 w2 mid1 mid2 : BitWord}
    (h1 : ∀ l r, (fCR l c_in (w1 +> r)) [tm]⊢⁺ (fCR (mid1 +> l) c1 r))
    (h2 : ∀ l r, (fCL (mid1 +> l) r) [tm]⊢⁺ (fCR (mid2 +> l) c2 r))
    (h3 : ∀ l r, (fCL (mid2 +> l) r) [tm]⊢⁺ (fCL l (w2 +> r))) :
    Seg (callStep tm fCR fCL) [c_in] [c1, c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact stepPlus_trans (h1 l r1)
    (stepPlus_trans (hc1 (mid1 +> l))
      (stepPlus_trans (h2 l _)
        (stepPlus_trans (hc2 (mid2 +> l)) (h3 l r3))))

theorem seg_ca_cj {tm : Machine (Fin 2) (Fin 6)}
    {mir : Bool} {st_ch st_c st_ret : Fin 6}
    (h2 : ∀ l r, (cfgCL mir st_ret ([1, 0, 1, 0] +> l) r) [tm]⊢⁺ (cfgCL mir st_ret l (t +> r))) :
    Seg (callStep tm (cfgCR mir st_ch st_c) (cfgCL mir st_ret)) [.ca] [.cj] [] t := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  have h1 : cfgCR mir st_ch st_c l .ca ([] +> r1) =
      cfgCR mir st_ch st_c ([1, 0, 1, 0] +> l) .cj r1 := by
    cases mir <;>
      (unfold cfgCR callWord callState
       simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil])
  rw [h1]
  exact stepPlus_trans (hc1 ([1, 0, 1, 0] +> l)) (h2 l r2)

syntax "seg_exec" : tactic
macro_rules
  | `(tactic| seg_exec) => `(tactic| (
    intro l r
    dsimp [cfgCf, cfgCL, cfgCR, callState, callWord, lh, d1, d0, t, one]
    try simp only [↓reduceIte, Bool.false_eq_true, List.cons_append, List.nil_append,
      append_cons, append_nil]
    execute))

syntax "prove_seg_rules" : tactic
macro_rules
  | `(tactic| prove_seg_rules) => `(tactic|
    refine
      { r0b := seg_of_step2 (mid := [1, 0, 1, 0]) (by seg_exec) (by seg_exec)
        r0c := seg_of_step5 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
          (by seg_exec) (by seg_exec) (by seg_exec)
        r0d := seg_of_step5 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
          (by seg_exec) (by seg_exec) (by seg_exec)
        r0e := seg_of_step4 (by seg_exec)
        rH2 := seg_of_step5 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
          (by seg_exec) (by seg_exec) (by seg_exec)
        r0f := seg_of_step2 (mid := [1, 0, 1, 0]) (by seg_exec) (by seg_exec)
        r0g := seg_of_step2 (mid := [1, 0, 1, 0]) (by seg_exec) (by seg_exec)
        r0h := seg_of_step5 (mid1 := [1, 0, 1, 1]) (mid2 := [1, 0, 1, 0])
          (by seg_exec) (by seg_exec) (by seg_exec)
        r0i := seg_of_step4 (by seg_exec)
        rH1 := seg_of_step4 (by seg_exec)
        rH3 := seg_of_step2 (mid := [1, 1]) (by seg_exec) (by seg_exec)
        r0j := seg_of_step2 (mid := [1, 1]) (by seg_exec) (by seg_exec)
        rH0 := seg_of_step4 (by seg_exec)
        rH4 := seg_of_step2 (mid := [1, 1]) (by seg_exec) (by seg_exec)
        r0k := seg_ca_cj (by seg_exec) })

end

section

@[simp] theorem pow_zero_nil {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem pow_succ_append {α : Type*} (l : List α) (n : Nat) :
    l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem pow_one_add_append {α : Type*} (l : List α) (n : Nat) :
    l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem pow_one_self {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l
theorem pow_add_append {α : Type*} (l : List α) (m n : Nat) :
    l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, pow_succ_append, pow_succ_append, ih, List.append_assoc]

variable {cs : Call → HalfTape → HalfTape → Prop} (R : SegRules cs)

theorem side_append {ls1 ls2 : List Call} {r1 r2 r3 : HalfTape}
    (h1 : Side cs ls1 r1 r2) (h2 : Side cs ls2 r2 r3) : Side cs (ls1 ++ ls2) r1 r3 := by
  induction h1 with
  | nil _ => exact h2
  | cons hc _ ih => exact Side.cons hc (ih h2)

theorem side_split {ls1 ls2 : List Call} {r1 r3 : HalfTape}
    (h : Side cs (ls1 ++ ls2) r1 r3) : ∃ r2, Side cs ls1 r1 r2 ∧ Side cs ls2 r2 r3 := by
  induction ls1 generalizing r1 with
  | nil => exact ⟨r1, Side.nil r1, h⟩
  | cons c ls1 ih =>
    rcases h with _ | ⟨hc, hrest⟩
    rcases ih hrest with ⟨r2, h1, h2⟩
    exact ⟨r2, Side.cons hc h1, h2⟩

theorem seg_nil (w : BitWord) : Seg cs [] [] w w := by
  intro r1 r2 h; cases h; exact Side.nil (w +> r1)

theorem seg_apply {ls1 ls2 : List Call} {w1 w2 : BitWord} {r1 r2 : HalfTape}
    (h1 : Seg cs ls1 ls2 w1 w2) (h2 : Side cs ls2 r1 r2) :
    Side cs ls1 (w1 +> r1) (w2 +> r2) :=
  h1 r1 r2 h2

theorem seg_comp {ls1 ls2 ls3 ls4 : List Call} {w1 w2 w3 : BitWord}
    (h1 : Seg cs ls1 ls2 w1 w2) (h2 : Seg cs ls3 ls4 w2 w3) :
    Seg cs (ls1 ++ ls3) (ls2 ++ ls4) w1 w3 := by
  intro r1 r3 h
  rcases side_split h with ⟨r2, ha, hb⟩
  exact side_append (h1 r1 r2 ha) (h2 r2 r3 hb)

include R in
theorem seg_ch_pow (n : Nat) : Seg cs ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact seg_nil t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [pow_succ_append, h_eq, pow_add_append]
    exact seg_comp R.r0d ih

theorem seg_ch_halve {w2 : BitWord} (hw : Seg cs [.ch, .ch] [.ch] w2 w2) (n : Nat) :
    Seg cs ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact seg_nil w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, pow_add_append, pow_succ_append]
    exact seg_comp hw ih

include R in
theorem seg_ch2_d0 : Seg cs [.ch, .ch] [.ch] d0 d0 :=
  seg_comp R.rH0 R.rH4

include R in
theorem seg_ch2_d1 : Seg cs [.ch, .ch] [.ch] d1 d1 :=
  seg_comp R.rH4 R.rH0

include R in
theorem seg_cp_t (n : Nat) : Seg cs ([.cp] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) t t :=
  seg_comp R.r0b (seg_ch_pow R n)

include R in
theorem seg_cj_t (n : Nat) : Seg cs ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [pow_one_add_append, List.cons_append, List.nil_append] using
    seg_comp R.r0c (seg_ch_pow R n)

include R in
theorem seg_cp_d1d0 (n : Nat) :
    Seg cs ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [pow_one_add_append, List.cons_append, List.nil_append] using
    seg_comp (seg_comp R.r0e R.rH2) (seg_ch_pow R n)

include R in
theorem seg_cj_d1d0 (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  seg_comp R.r0f (seg_ch_pow R n)

include R in
theorem seg_cp_d1d1 (n : Nat) :
    Seg cs ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  seg_comp R.r0g (seg_ch_pow R n)

include R in
theorem seg_cj_d1d1 (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [pow_one_add_append, List.cons_append, List.nil_append] using
    seg_comp R.r0h (seg_ch_pow R n)

include R in
theorem seg_cj_d0d0 (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg cs [.cj, .ch, .ch] [.cj] d0 d0 :=
    seg_comp R.r0i (seg_comp R.rH1 R.rH3)
  have h1 := seg_comp h0 (seg_ch_halve (seg_ch2_d0 R) n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq, pow_one_add_append, List.cons_append, List.nil_append] using h1

include R in
theorem seg_cj_d1d0_short (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  seg_comp R.r0j (seg_ch_halve (seg_ch2_d0 R) n)

include R in
theorem seg_cj_ch_d0 : Seg cs [.cj, .ch] [] d0 (d1 ++ one) :=
  seg_comp R.r0i R.rH1

include R in
theorem seg_cj_d0d1 (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg cs [.cj, .ch, .ch, .ch] [.cj] d0 d1 :=
    seg_comp R.r0i (seg_comp R.rH1 (seg_comp R.rH3 R.rH0))
  have h1 := seg_comp h0 (seg_ch_halve (seg_ch2_d1 R) n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq, pow_one_add_append, List.cons_append, List.nil_append] using h1

include R in
theorem seg_cj_d1d1_short (n : Nat) :
    Seg cs ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg cs [.cj, .ch] [.cp] d1 d1 := seg_comp R.r0j R.rH0
  have h1 := seg_comp h0 (seg_ch_halve (seg_ch2_d1 R) n)
  simpa only [pow_one_add_append, List.cons_append, List.nil_append] using h1

include R in
theorem seg_ca_ch : Seg cs [.ca, .ch] ([.cj] ++ [.ch] ^ 2) [] t :=
  seg_comp R.r0k R.r0d

inductive RIncs : Nat -> HalfTape -> HalfTape -> Prop where
  | zero (r : HalfTape) : RIncs 0 r (one +> r)
  | T {n : Nat} {r r' : HalfTape} :
      RIncs ((1 + n) * 2) r r' -> RIncs (1 + n) (t +> r) (t +> r')
  | pair0 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (1 + n) (d1 +> (d0 +> r)) (t +> r')
  | pair1 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (1 + n) (d1 +> (d1 +> r)) (t +> r')
  | short00 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (2 + n * 4) (d0 +> r) (d0 +> r')
  | short01 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (2 + n * 4) (d1 +> r) (d0 +> r')
  | short10 {n : Nat} {r r' : HalfTape} :
      RIncs (n * 2) r r' -> RIncs (4 + n * 4) (d0 +> r) (d1 +> r')
  | short11 {n : Nat} {r r' : HalfTape} :
      RIncs (1 + n * 2) r r' -> RIncs (4 + n * 4) (d1 +> r) (d1 +> r')
inductive Binary : Nat -> Nat -> HalfTape -> Prop where
  | one : Binary 1 1 (d1 +> default)
  | zero {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (2 + n * 2) (1 + H) (d0 +> r)
  | two {n H : Nat} {r : HalfTape} :
      Binary (1 + n) H r -> Binary (3 + n * 2) (1 + H) (d1 +> r)

open WordCalculus Word
local notation "WordList" => List Word

theorem eight_pow_pos (n : Nat) : 0 < 8 ^ n := by
  induction n with
  | zero => decide
  | succ n ih => rw [Nat.pow_succ]; omega

theorem binary_bounds {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    0 < A /\ 0 < H /\ 2 ^ H <= A * 2 /\ A < 2 ^ H := by
  induction h with
  | one => decide
  | @zero n H r _ ih =>
    rw [pow_two_one_add H]; omega
  | @two n H r _ ih =>
    rw [pow_two_one_add H]; omega

theorem exists_binary (n : Nat) : ∃ H r,Binary (1 + n) H r := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => exact ⟨1,d1 +> default,Binary.one⟩
    | succ m =>
      rcases even_or_odd_mul_two m with ⟨a,rfl⟩ | ⟨a,rfl⟩
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d0 +> r,?_⟩
        have heq : 1 + (a * 2 + 1) = 2 + a * 2 := by omega
        rw [heq]; exact Binary.zero hI
      · rcases ih a (by omega) with ⟨H0,r,hI⟩
        refine ⟨1 + H0,d1 +> r,?_⟩
        have heq : 1 + ((1 + a * 2) + 1) = 3 + a * 2 := by omega
        rw [heq]; exact Binary.two hI

theorem binary_rincs {A H : Nat} {r : HalfTape} (h : Binary A H r) :
    RIncs ((A - 1) * 2) default r := by
  induction h with
  | one =>
    have h0 := RIncs.zero (default : HalfTape)
    have hd : d1 +> (default : HalfTape) = one +> default := by simp
    rw [hd]; exact h0
  | @zero n H r _ ih =>
    have ih' : RIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := RIncs.short00 ih'
    rw [d0_append_default] at hs
    have heq : ((2 + n * 2) - 1) * 2 = 2 + n * 4 := by omega
    rwa [heq]
  | @two n H r _ ih =>
    have ih' : RIncs (n * 2) default r := by
      have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
      rwa [heq] at ih
    have hs := RIncs.short10 ih'
    rw [d0_append_default] at hs
    have heq : ((3 + n * 2) - 1) * 2 = 4 + n * 4 := by omega
    rwa [heq]

theorem digitVal_binary_append {A H : Nat} {u : WordList} (h1 : DigitVal A H u) :
    ∀ {B J : Nat} {r : HalfTape},Binary B J r -> Binary (A + B * 2 ^ H) (H + J) (evalWords u r) :=
        by
  induction h1 with
  | nil =>
    intro B J r h2
    simpa [evalWords] using h2
  | @zero A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := binary_bounds hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (evalWords u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.zero hI'
    have heq1 : 2 + (A + B * 2 ^ H - 1) * 2 = A * 2 + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [evalWords,heq1,heq2] using h3
  | @one A H u _ ih =>
    intro B J r h2
    have hI := ih h2
    have hB := binary_bounds hI
    have hI' : Binary (1 + (A + B * 2 ^ H - 1)) (H + J) (evalWords u r) := by
      have heq : 1 + (A + B * 2 ^ H - 1) = A + B * 2 ^ H := by omega
      rwa [heq]
    have h3 := Binary.two hI'
    have heq1 : 3 + (A + B * 2 ^ H - 1) * 2 = (1 + A * 2) + B * 2 ^ (1 + H) := by
      rw [pow_two_one_add H,Nat.mul_add]; omega
    have heq2 : 1 + (H + J) = (1 + H) + J := by omega
    simpa [evalWords,heq1,heq2] using h3

theorem binary_191_8 : Binary 191 8 (evalWords (List.replicate 6 Q ++ [K,Q]) default) := by
  dsimp [List.replicate,evalWords]
  exact Binary.two (n := 94) (Binary.two (n := 46) (Binary.two (n := 22)
    (Binary.two (n := 10) (Binary.two (n := 4) (Binary.two (n := 1)
      (Binary.zero (n := 0) Binary.one))))))

def HasKKPrefix (ds : WordList) : Prop := ∃ v,ds = K :: K :: v

def HasQ6Suffix (ds : WordList) : Prop := ∃ v,ds = v ++ List.replicate 6 Q

theorem exists_digitVal_window (r k : Nat) (hL : 191 * 2 ^ r <= k * 2) (hU : k * 2 < 192 * 2 ^ r) :
    ∃ ds,DigitVal (k * 8 - 512 * 2 ^ r) (8 + r) ds /\ HasKKPrefix ds /\ HasQ6Suffix ds /\
      Binary (k * 8) (10 + r) (evalWords ds (d0 +> (d1 +> default))) := by
  let a := k * 2 - 191 * 2 ^ r
  have hA : a + 191 * 2 ^ r = k * 2 := by omega
  have ha_lt : a < 2 ^ r := by omega
  rcases exists_digitVal_of_lt_pow r a ha_lt with ⟨v,hD⟩
  refine ⟨K :: K :: (v ++ List.replicate 6 Q),?_,⟨_,rfl⟩,⟨K :: K :: v,rfl⟩,?_⟩
  · have hApp := digitVal_append hD (digitVal_replicate_Q 6)
    have hZ1 := DigitVal.zero hApp
    have hZ2 := DigitVal.zero hZ1
    have hpos := pow_two_pos r
    have heq1 : ((a + (2 ^ 6 - 1) * 2 ^ r) * 2) * 2 = k * 8 - 512 * 2 ^ r := by
      change ((a + 63 * 2 ^ r) * 2) * 2 = k * 8 - 512 * 2 ^ r
      (try omega)
    have heq2 : 1 + (1 + (r + 6)) = 8 + r := by omega
    rwa [heq1,heq2] at hZ2
  · have hB := digitVal_binary_append hD binary_191_8
    rw [evalWords_append] at hB
    dsimp [evalWords] at hB ⊢
    rw [evalWords_append]
    have hpos := pow_two_pos r
    have hB' : Binary (1 + (a + 191 * 2 ^ r - 1)) (r + 8)
        (evalWords v (evalWords (List.replicate 6 Q) (d0 +> (d1 +> default)))) := by
      have heq : 1 + (a + 191 * 2 ^ r - 1) = a + 191 * 2 ^ r := by omega
      rwa [heq]
    have hB1 := Binary.zero hB'
    have hB1' : Binary (1 + (2 * (a + 191 * 2 ^ r) - 1)) (1 + (r + 8))
        (d0 +> evalWords v (evalWords (List.replicate 6 Q) (d0 +> (d1 +> default)))) := by
      have heq : 1 + (2 * (a + 191 * 2 ^ r) - 1) = 2 + (a + 191 * 2 ^ r - 1) * 2 := by omega
      rwa [heq]
    have hB2 := Binary.zero hB1'
    have heq1 : 2 + (2 * (a + 191 * 2 ^ r) - 1) * 2 = k * 8 := by omega
    have heq2 : 1 + (1 + (r + 8)) = 10 + r := by omega
    rwa [heq1,heq2] at hB2

theorem two_pow_three_mul (n : Nat) : 2 ^ (3 * n) = 8 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have heq : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [heq,Nat.pow_add,ih,Nat.pow_succ]; ring

theorem eight_pow_bounds (n : Nat) :
    2 ^ (10 + 3 * n) = 256 * 2 ^ (2 + 3 * n) /\ 8 ^ (3 + n) = 128 * 2 ^ (2 + 3 * n) := by
  constructor
  · have heq : 10 + 3 * n = (2 + 3 * n) + 8 := by omega
    rw [heq,Nat.pow_add]; ring
  · rw [Nat.pow_add 8 3 n,Nat.pow_add 2 2 (3 * n),two_pow_three_mul]; ring

theorem rincs_evalWords_step {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    ∀ {r r' : HalfTape},RIncs b r r' -> RIncs a (evalWords u r) (evalWords v r') := by
  induction h with
  | nil _ => intro r r' hR; exact hR
  | T _ ih => intro r r' hR; exact RIncs.T (ih hR)
  | pair0 _ ih => intro r r' hR; exact RIncs.pair0 (ih hR)
  | pair1 _ ih => intro r r' hR; exact RIncs.pair1 (ih hR)
  | short00 _ ih => intro r r' hR; exact RIncs.short00 (ih hR)
  | short01 _ ih => intro r r' hR; exact RIncs.short01 (ih hR)
  | short10 _ ih => intro r r' hR; exact RIncs.short10 (ih hR)
  | short11 _ ih => intro r r' hR; exact RIncs.short11 (ih hR)

theorem wordScale_append_k {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) :
    (a : Rat) = (b : Rat) * wordScale v + (wordMassQ v + l) * 2 := by
  induction h with
  | nil k => simp [wordMassQ,wordScale]
  | T _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | pair0 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | pair1 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short00 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short01 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short10 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith
  | short11 _ ih => dsimp [wordMassQ,wordScale]; push_cast at ih ⊢; linarith

theorem wordMass_append_k {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) : wordScale v <= wordScale u := by
  induction h with
  | nil _ => simp [wordScale]
  | T _ ih => dsimp [wordScale]; linarith
  | @pair0 _ u _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | @pair1 _ u _ _ _ _ _ => have hp := wordScale_pos u; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [wordScale]; linarith
  | short01 _ ih => dsimp [wordScale]; linarith
  | short10 _ ih => dsimp [wordScale]; linarith
  | short11 _ ih => dsimp [wordScale]; linarith

theorem scan_wordScale_mul_eight_le {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) (he : hasQKSubword u = true) : wordScale v * 8 <= wordScale u := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | pair0 hS _ => have := wordMass_append_k hS; dsimp [wordScale]; linarith
  | pair1 hS _ => have := wordMass_append_k hS; dsimp [wordScale]; linarith
  | short00 _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | @short01 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hS)
      | Q => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
  | short10 _ ih => dsimp [hasQKSubword,wordScale] at he ⊢; have := ih he; linarith
  | @short11 n u k v l hS ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hS)
      | Q => dsimp [hasQKSubword,wordScale] at he ih ⊢; have := ih he; linarith

theorem wordMass_lt_scale {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (h : Scan a u b v l) (he : hasQKSubword u = true) : 0 < l := by
  induction h with
  | nil _ => contradiction
  | T _ ih => dsimp [hasQKSubword] at he; have := ih he; linarith
  | pair0 hI _ => have := scan_mass_bounds hI; linarith
  | pair1 hI _ => have := scan_mass_bounds hI; linarith
  | short00 hI _ => have := scan_mass_bounds hI; linarith
  | @short01 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword] at he; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hI)
      | Q => dsimp [hasQKSubword] at he; have := ih he; linarith
  | short10 hI _ => have := scan_mass_bounds hI; linarith
  | @short11 n u k v l hI ih =>
    cases u with
    | nil => contradiction
    | cons w u' =>
      cases w with
      | V => dsimp [hasQKSubword] at he; have := ih he; linarith
      | K => exact False.elim (not_scan_odd_cons_K n u' k v l hI)
      | Q => dsimp [hasQKSubword] at he; have := ih he; linarith

theorem isDigitWord_append (r : Nat) :
    List.replicate (3 + r) V = List.replicate r V ++ [V,V,V] := by
  have heq : 3 + r = r + 3 := by omega
  rw [heq,List.replicate_add]; rfl

theorem exists_digitVal_of_isDigitWord (n a b : Nat) (v : WordList) (l : Rat)
    (hI : Scan a (List.replicate (6 + n) Q ++ [K]) b v l) :
    ∃ w k,v = w ++ [V,V,V] /\ b = k * 8 := by
  rcases even_or_odd_mul_two n with ⟨a0,rfl⟩ | ⟨a0,rfl⟩
  · have heq : 6 + a0 * 2 = 2 + (2 + a0) * 2 := by omega
    rw [heq] at hI
    rcases scan_even_Q_K_inv (2 + a0) a b v l hI with ⟨d,k,rfl,rfl,_⟩
    refine ⟨d :: List.replicate a0 V,k * 2 ^ (1 + a0),?_,?_⟩
    · have heq2 : 1 + (2 + a0) = 3 + a0 := by omega
      rw [heq2,isDigitWord_append]; rfl
    · have heq2 : 2 + (2 + a0) = (1 + a0) + 3 := by omega
      rw [heq2,Nat.pow_add]; ring
  · have heq : 6 + (1 + a0 * 2) = 1 + (3 + a0) * 2 := by omega
    rw [heq] at hI
    rcases scan_odd_Q_K_inv (3 + a0) a b v l hI with ⟨rfl,rfl,_⟩
    refine ⟨List.replicate (1 + a0) V,(a - 1) * 2 ^ (1 + a0),?_,?_⟩
    · have heq2 : 1 + (3 + a0) = 3 + (1 + a0) := by omega
      rw [heq2,isDigitWord_append]
    · have heq2 : 1 + (3 + a0) = (1 + a0) + 3 := by omega
      rw [heq2,Nat.pow_add]; ring

theorem digitVal_append (n : Nat) :
    ∀ (a b : Nat) (v : WordList) (l : Rat),
      Scan a (List.replicate n V) b v l ->
      v = List.replicate n V /\ b = a * 2 ^ n /\ l = 0 := by
  induction n with
  | zero =>
    intro a b v l hI
    cases hI
    exact ⟨rfl,by simp,rfl⟩
  | succ n ih =>
    intro a b v l hI
    cases hI with
    | @T m _ _ v0 l0 hJ =>
      rcases ih ((1 + m) * 2) b v0 l0 hJ with ⟨rfl,rfl,rfl⟩
      refine ⟨rfl,?_,by ring⟩
      rw [Nat.pow_succ]; ring

theorem digitVal_to_binary {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a (u ++ [V, V, V]) b v l) :
    ∃ w k, v = w ++ [V, V, V] /\ b = k * 8 := by
  rcases scan_split_of_splitCond hI u [V, V, V] rfl (Or.inr ⟨[V, V], rfl⟩) with
    ⟨c, x, y, s, t0, _, hK, rfl, _⟩
  rcases digitVal_append 3 c b y t0 hK with ⟨rfl, rfl, _⟩
  exact ⟨x, c, rfl, rfl⟩

theorem rincs_of_stepWord {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a (u ++ List.replicate 6 Q ++ [K]) b v l) :
    ∃ w k, v = w ++ [V, V, V] /\ b = k * 8 := by
  rcases split_trailing_Q u with ⟨p, n, rfl, hP⟩
  have hE : (p ++ List.replicate n Q) ++ List.replicate 6 Q ++ [K] =
      p ++ (List.replicate (6 + n) Q ++ [K]) := by
    have heq : 6 + n = n + 6 := by omega
    rw [heq, List.replicate_add]; simp [List.append_assoc]
  rw [hE] at hI
  rcases scan_split_of_splitCond hI p (List.replicate (6 + n) Q ++
      [K]) rfl (Or.inl hP) with ⟨c, x, y, s, t0, _, hK, rfl, _⟩
  rcases exists_digitVal_of_isDigitWord n c b y t0 hK with ⟨w, k, rfl, rfl⟩
  exact ⟨x ++ w, k, by rw [List.append_assoc], rfl⟩

theorem rincs_of_stepWords {n : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan (n * 8) (K :: K :: u) b v l) : hasQKSubword v = true := by
  generalize ha : n * 8 = a at hI
  cases hI with
  | short00 hJ => omega
  | @short10 m _ _ _ _ hJ =>
    generalize hb : m * 2 = a2 at hJ
    cases hJ with
    | short00 _ => rfl
    | short10 _ => omega

theorem scan_tailDefect_wordScale_bounds {a : Nat} {u : WordList} {b : Nat} {v : WordList}
    {l : Rat} {c : Nat} {ds w : WordList} {m z : Rat}
    (hI : Scan a u b v l) (hE : hasQKSubword u = true)
    (hJ : Scan b ds c w m) (hD : TailDefect ds z) (hZ : 3 <= z) :
    wordScale v * wordMass w <= (7 / 24) * (wordScale u * z) /\
    wordScale v * m <= (7 / 24) * (wordScale u * z) := by
  have hg := scan_wordScale_mul_eight_le hI hE
  rcases scan_tailDefect_bound hJ hD with ⟨hM, hL, _⟩
  have hp := wordScale_pos v
  have h1 : wordScale v * (1 + z * 2) <= (7 / 24) * (wordScale u * z) := by nlinarith
  constructor <;> nlinarith

theorem wordMass_append_tailDefect_bounds {a : Nat} {u : WordList} {b : Nat}
    {v : WordList} {l : Rat} {c : Nat} {ds w : WordList} {m z : Rat}
    (hI : Scan a u b v l) (hE : hasQKSubword u = true)
    (hJ : Scan b ds c w m) (hD : TailDefect ds z) (hZ : 3 <= z) :
    wordMass (v ++ w) <= wordMass u + (7 / 24) * (wordScale u * z) /\
    wordMass (v ++
        w) + l + wordScale v * m <= wordMass u + wordMassK u + (7 / 12) * (wordScale u * z) := by
  have hb := scan_mass_bounds hI
  have hd := scan_tailDefect_wordScale_bounds hI hE hJ hD hZ
  rw [wordMass_append]
  constructor <;> linarith

theorem hasQKSubword_stepWords {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    (hI : Scan a u b v l) (hB : 0 < b) :
    ∃ H r, Binary b H r /\ RIncs a (evalWords u (d1 +> default)) (evalWords v (t +> r)) := by
  cases b with
  | zero => omega
  | succ n =>
    have h1n : n + 1 = 1 + n := by omega
    rw [h1n] at hI ⊢
    rcases exists_binary n with ⟨H, r, hD⟩
    refine ⟨H, r, hD, ?_⟩
    refine rincs_evalWords_step hI ?_
    have hR := binary_rincs hD
    have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
    rw [heq] at hR
    have hp := RIncs.pair0 hR
    rwa [d0_append_default] at hp

theorem hasVPrefix_stepWords {u : WordList} {A H : Nat} {ds : WordList} (hD : DigitVal A H ds)
    (hE : wordScale u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hF : wordMass u * 2 + wordMassK u + wordScale u * wordMassK ds <= 1 / 64) :
    ∃ b v l J r,
      Scan 6 (u ++ ds ++ [K]) b v l /\ Binary b J r /\
      RIncs 6 (evalWords (u ++ ds) (d0 +> (d1 +> default))) (evalWords v (t +> r)) := by
  rcases digitVal_scale_and_mass hD with ⟨hS, hM, _⟩
  have hU := (wordMass_nonneg u).1
  have hP := wordScale_pos u
  have hEx : (wordMass (u ++ ds ++ [K]) + wordMassK (u ++ ds ++ [K])) * 2 <
      ((3 * 2 : Nat) : Rat) := by
    rw [wordMass_append, wordMass_append, wordMassK_append, wordMassK_append, wordScale_append]
    dsimp [wordMass, wordMassK, wordScale]
    rw [hS]
    have hM' : wordMass ds = ((2 ^ H : Nat) : Rat) - 1 := by linarith
    rw [hM']
    nlinarith
  rcases exists_scan_of_mass_lt (u ++ ds ++ [K]) 3 hEx with ⟨b, v, l, hI, hB⟩
  rcases hasQKSubword_stepWords hI hB with ⟨J, r, hR, hK⟩
  refine ⟨b, v, l, J, r, hI, hR, ?_⟩
  simpa [evalWords_append, evalWords] using hK

def HasV15Prefix (u : WordList) : Prop := ∃ p, u = p ++ [V, V, V]

theorem hasQKSubword_append_left (u v : WordList) (h : hasQKSubword u = true) :
    hasQKSubword (u ++ v) = true := by
  induction u with
  | nil => contradiction
  | cons w u ih =>
    cases w with
    | V => exact ih h
    | K => exact ih h
    | Q =>
      cases u with
      | nil => contradiction
      | cons w2 u' =>
        cases w2 with
        | V => exact ih h
        | K => rfl
        | Q => exact ih h

theorem rincs_evalWords_round {u : WordList} {A H : Nat} {ds : WordList} (hD : DigitVal A H ds)
    (hHs : wordScale u * ((2 ^ H : Nat) : Rat) = 1 / 2)
    (hF : wordMass u * 2 + wordMassK u + wordScale u * wordMassK ds <= 1 / 64)
    (hU : HasV15Prefix u) (hW : hasQKSubword u =
        true) (hLo : HasKKPrefix ds) (hHi : HasQ6Suffix ds) :
    ∃ k v l g,
      Scan 6 (u ++ ds ++ [K]) (k * 8) v l /\
      HasV15Prefix v /\ hasQKSubword v = true /\
      wordScale v * ((8 ^ g : Nat) : Rat) = 1 /\
      wordMass v <= wordMass u + (7 / 24) * (wordScale u * wordMassK ds) /\
      wordMass v + l <= wordMass u + wordMassK u + (7 / 12) * (wordScale u * wordMassK ds) /\
      0 < wordMassQ v + l /\ wordMassQ v + l <= 1 / 64 := by
  rcases hU with ⟨p, hU⟩
  rcases hasVPrefix_stepWords hD hHs hF with ⟨b, v, l, _, _, hI, _, _⟩
  have hCu : SplitCond u (ds ++ [K]) := by
    left
    rw [hU]
    have heq : p ++ [V, V, V] = (p ++ [V, V]) ++ [V] := by simp [List.append_assoc]
    rw [heq, notEndsWithQ_append_singleton]; rfl
  have hI_assoc : Scan 6 (u ++ (ds ++ [K])) b v l := by
    simpa [List.append_assoc] using hI
  rcases scan_split_of_splitCond hI_assoc u (ds ++ [K]) rfl hCu with
    ⟨c, x, y, s, t0, hI1, hI2, hV, hL⟩
  have hHv : hasQKSubword v = true := by
    have hJ1 := hI1
    rw [hU] at hJ1
    rcases digitVal_to_binary hJ1 with ⟨z, k, _, rfl⟩
    rcases hLo with ⟨w, rfl⟩
    have hLow := rincs_of_stepWords hI2
    rw [hV]
    exact hasQKSubword_append_right x y hLow
  have hBv : ∃ p' k, v = p' ++ [V, V, V] /\ b = k * 8 := by
    rcases hHi with ⟨w, rfl⟩
    have hI' : Scan 6 ((u ++ w) ++ List.replicate 6 Q ++ [K]) b v l := by
      simpa [List.append_assoc] using hI
    exact rincs_of_stepWord hI'
  rcases hBv with ⟨z, k, hZ, rfl⟩
  rcases scan_scale_pow_eight hI with ⟨g, hG⟩
  have hS : wordScale v * ((8 ^ g : Nat) : Rat) = 1 := by
    have hDs := (digitVal_scale_and_mass hD).1
    rw [wordScale_append, wordScale_append] at hG
    dsimp [wordScale] at hG
    rw [hDs] at hG
    nlinarith
  have hZd : 3 <= wordMassK ds := by
    rcases hLo with ⟨w, rfl⟩
    have hw := (wordMass_nonneg w).2.1
    dsimp [wordMassK]; linarith
  rcases wordMass_append_tailDefect_bounds hI1 hW hI2 (tailDefect_append_K_of_digitVal hD) hZd with
    ⟨hM, hB⟩
  rw [<- hV] at hM hB
  have hB' : wordMass v + l <= wordMass u + wordMassK u +
      (7 / 12) * (wordScale u * wordMassK ds) := by linarith
  refine ⟨k, v, l, g, hI, ⟨z, hZ⟩, hHv, hS, hM, hB', ?_, ?_⟩
  · have hwv := wordMass_nonneg v
    have hloss := wordMass_lt_scale hI
        (hasQKSubword_append_left (u ++ ds) [K] (hasQKSubword_append_left u ds hW))
    linarith
  · have hwv := wordMass_nonneg v
    have hwu := wordMass_nonneg u
    have hwds := wordMass_nonneg ds
    have hsu := wordScale_pos u
    have hms := wordMass_eq_add v
    nlinarith

theorem good_next_round_aux {g k : Nat} {s delta : Rat}
    (hS : s * ((8 ^ g : Nat) : Rat) = 1)
    (hB : (6 : Rat) = ((k * 8 : Nat) : Rat) * s + delta * 2)
    (hD : 0 < delta) (hU : delta <= 1 / 64) :
    ∃ n,g = 3 + n /\ 191 * 2 ^ (2 + 3 * n) <= k * 2 /\ k * 2 < 192 * 2 ^ (2 + 3 * n) := by
  have hP_nat := eight_pow_pos g
  have hP : (0 : Rat) < ((8 ^ g : Nat) : Rat) := Nat.cast_pos.mpr hP_nat
  have hE : ((k * 8 : Nat) : Rat) = (6 - delta * 2) * ((8 ^ g : Nat) : Rat) := by
    have hT : ((k * 8 : Nat) : Rat) * s = 6 - delta * 2 := by linarith
    calc ((k * 8 : Nat) : Rat)
      _ = (((k * 8 : Nat) : Rat) * s) * ((8 ^ g : Nat) : Rat) := by
          rw [mul_assoc,hS,mul_one]
      _ = (6 - delta * 2) * ((8 ^ g : Nat) : Rat) := by rw [hT]
  have hL_q : ((191 * 8 ^ g : Nat) : Rat) <= ((256 * k : Nat) : Rat) := by
    push_cast at hP hE ⊢; nlinarith
  have hL : 191 * 8 ^ g <= 256 * k := Nat.cast_le.mp hL_q
  have hR_q : ((k * 8 : Nat) : Rat) < ((6 * 8 ^ g : Nat) : Rat) := by
    push_cast at hP hE ⊢; nlinarith
  have hR : k * 8 < 6 * 8 ^ g := Nat.cast_lt.mp hR_q
  rcases g with _ | _ | _ | n
  · omega
  · omega
  · omega
  · have hp := (eight_pow_bounds n).2
    have h3n : n + 1 + 1 + 1 = 3 + n := by omega
    rw [h3n,hp] at hL hR
    exact ⟨n,by omega,by omega,by omega⟩

theorem good_next_round_main {a : Nat} {u : WordList} {b : Nat} {v : WordList} {l : Rat}
    {H : Nat} {r : HalfTape}
    (hI : Scan a u b v l) (hB : Binary b H r) :
    RIncs a (evalWords u (d1 +> default)) (evalWords v (t +> r)) := by
  have hb := (binary_bounds hB).1
  cases b with
  | zero => omega
  | succ b =>
    have h1b : b + 1 = 1 + b := by omega
    rw [h1b] at hI hB
    refine rincs_evalWords_step hI ?_
    have hR := binary_rincs hB
    have heq : ((1 + b) - 1) * 2 = b * 2 := by omega
    rw [heq] at hR
    have hp := RIncs.pair0 hR
    rwa [d0_append_default] at hp

inductive Good : HalfTape -> Prop where
  | intro (u : WordList) (A H : Nat) (ds : WordList) :
      DigitVal A H ds ->
      wordScale u * ((2 ^ H : Nat) : Rat) = 1 / 2 ->
      wordMass u * 2 + wordMassK u + wordScale u * wordMassK ds <= 1 / 64 ->
      HasV15Prefix u -> hasQKSubword u = true -> HasKKPrefix ds -> HasQ6Suffix ds ->
      Good (evalWords (u ++ ds) (d0 +> (d1 +> default)))

theorem good_next_round {r : HalfTape} (hG : Good r) :
    ∃ r',RIncs 6 r r' /\ Good (t +> r') := by
  rcases hG with ⟨u,A,H,ds,hD,hHs,hF,hU,hW,hLo,hHi⟩
  rcases rincs_evalWords_round hD hHs hF hU hW hLo hHi with
    ⟨k,v,l,g,hI,hTv,hV,hS,hM,hL,hPos,hBound⟩
  have hB := wordScale_append_k hI
  rcases good_next_round_aux hS hB hPos hBound with ⟨n,rfl,hKl,hKu⟩
  rcases exists_digitVal_window (2 + 3 * n) k hKl hKu with ⟨ds',hD',hLo',hHi',hBin⟩
  refine ⟨evalWords v (t +> evalWords ds' (d0 +> (d1 +> default))),?_,?_⟩
  · have hR := good_next_round_main hI hBin
    simpa [evalWords_append,evalWords] using hR
  · have hOut : t +> evalWords v (t +> evalWords ds' (d0 +> (d1 +> default))) =
        evalWords ((V :: (v ++ [V])) ++ ds') (d0 +> (d1 +> default)) := by
      simp [evalWords_append,evalWords]
    rw [hOut]
    have hp1 := (eight_pow_bounds n).1
    have hp2 := (eight_pow_bounds n).2
    have h82 : 8 + (2 + 3 * n) = 10 + 3 * n := by omega
    refine Good.intro (V :: (v ++ [V])) _ (8 + (2 + 3 * n)) ds' hD' ?_ ?_ ?_ ?_ hLo' hHi'
    · rw [hp2] at hS
      rw [h82,hp1]
      dsimp [wordScale]; rw [wordScale_append]; dsimp [wordScale]
      push_cast at hS ⊢
      nlinarith
    · have hZ := digitVal_wordMassK_eq hD'
      rw [h82,hp1] at hZ
      have hAeq : (k * 8 - 512 * 2 ^ (2 + 3 * n)) + 512 * 2 ^ (2 + 3 * n) = k * 8 := by omega
      have hAE : (((k * 8 - 512 * 2 ^ (2 + 3 * n) : Nat) : Rat)) + ((512 * 2 ^ (2 + 3 * n) : Nat) :
          Rat) = ((k * 8 : Nat) : Rat) := by
        exact_mod_cast hAeq
      rw [hp2] at hS
      push_cast at hZ hAE hS hB
      dsimp [wordMass,wordMassK,wordScale]
      rw [wordMass_append,wordMassK_append,wordScale_append]
      dsimp [wordMass,wordMassK,wordScale]
      have hms := wordMass_eq_add v
      have hwu := wordMass_nonneg u
      have hwds := wordMass_nonneg ds
      have hsu := wordScale_pos u
      have hsv := wordScale_pos v
      nlinarith
    · rcases hTv with ⟨w,rfl⟩
      refine ⟨V :: (w ++ [V]),?_⟩
      simp [List.append_assoc]
    · dsimp [hasQKSubword]
      exact hasQKSubword_append_left v [V] hV

def pow_four_eq : Nat -> Nat -> Option (WordList)
  | 0,_ => none
  | _ + 1,0 => none
  | _ + 1,1 => some [Q]
  | fuel + 1,m + 2 =>
    match pow_four_eq fuel ((m + 2) / 2) with
    | none => none
    | some ws => some ((if (m + 2) % 2 == 0 then K else Q) :: ws)

theorem execCodeE (fuel : Nat) :
    ∀ (m : Nat) (ws : WordList),pow_four_eq fuel m = some ws ->
      ∃ H,Binary m H (evalWords ws default) := by
  induction fuel with
  | zero => intro m ws h; contradiction
  | succ fuel ih =>
    intro m ws h
    rcases m with _ | _ | m
    · contradiction
    · injection h with h; subst h
      exact ⟨1,Binary.one⟩
    · dsimp [pow_four_eq] at h
      cases hrec : pow_four_eq fuel ((m + 2) / 2) with
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

open ChoiceE
def execCodeE_sound : ChoiceE -> Nat -> Nat
  | CT,n | CP0,n | CP1,n => 1 + n
  | CS00,n | CS01,n => 2 + n * 4
  | CS10,n | CS11,n => 4 + n * 4

def execCodeE_complete : ChoiceE -> Nat -> Nat
  | CT,n => (1 + n) * 2
  | CP0,n | CS00,n | CS10,n => n * 2
  | CP1,n | CS01,n | CS11,n => 1 + n * 2

def checkRoundE : CodeE -> Nat -> WordList -> Option (WordList)
  | .Stop n,k,u =>
    if k == n * 2 then
      if u.all isWordK then pow_four_eq 64 (1 + n) else none
    else none
  | .More ch n c,k,u =>
    if k == execCodeE_sound ch n then
      match stripWordPrefix (choiceInWordsE ch) u with
      | none => none
      | some w =>
        match checkRoundE c (execCodeE_complete ch n) w with
        | none => none
        | some v => some (choiceOutWordE ch :: v)
    else none

theorem checkRoundE_sound (c : CodeE) :
    ∀ (k : Nat) (u v : WordList),checkRoundE c k u = some v ->
      RIncs k (evalWords u default) (evalWords v default) := by
  induction c with
  | Stop n =>
    intro k u v hE
    dsimp [checkRoundE] at hE
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
        rcases execCodeE 64 (1 + n) v hE with ⟨H,hB⟩
        have hR := binary_rincs hB
        have heq : ((1 + n) - 1) * 2 = n * 2 := by omega
        rwa [heq] at hR
  | More ch n c ih =>
    intro k u v hE
    dsimp [checkRoundE] at hE
    cases hk : (k == execCodeE_sound ch n) with
    | false => rw [hk] at hE; contradiction
    | true =>
      rw [hk] at hE
      dsimp at hE
      have rfl_k : k = execCodeE_sound ch n := beq_iff_eq.mp hk
      subst rfl_k
      cases hU : stripWordPrefix (choiceInWordsE ch) u with
      | none => rw [hU] at hE; contradiction
      | some w =>
        rw [hU] at hE
        dsimp at hE
        cases hC : checkRoundE c (execCodeE_complete ch n) w with
        | none => rw [hC] at hE; contradiction
        | some x =>
          rw [hC] at hE
          injection hE with hE; subst hE
          have rfl_u := stripWordPrefix_sound (choiceInWordsE ch) u w hU
          subst rfl_u
          have hIH := ih (execCodeE_complete ch n) w x hC
          cases ch
          · exact RIncs.T hIH
          · exact RIncs.pair0 hIH
          · exact RIncs.pair1 hIH
          · exact RIncs.short00 hIH
          · exact RIncs.short01 hIH
          · exact RIncs.short10 hIH
          · exact RIncs.short11 hIH

def roundStepE (c : CodeE) (u : WordList) : Option (WordList) :=
  match checkRoundE c 6 (u ++ [K]) with
  | some v => some (V :: v)
  | none => none

theorem roundStepE_trans (c : CodeE) (u v : WordList) (h : roundStepE c u = some v) :
    ∃ r,RIncs 6 (evalWords u default) r /\ evalWords v default = t +> r := by
  dsimp [roundStepE] at h
  cases hE : checkRoundE c 6 (u ++ [K]) with
  | none => rw [hE] at h; contradiction
  | some w =>
    rw [hE] at h
    injection h with h; subst h
    refine ⟨evalWords w default,?_,rfl⟩
    have hR := checkRoundE_sound c 6 (u ++ [K]) w hE
    simpa [evalWords_append,evalWords] using hR

inductive Rounds : HalfTape -> HalfTape -> Prop where
  | refl (r : HalfTape) : Rounds r r
  | next {r s t0 : HalfTape} :
      RIncs 6 r s -> Rounds (t +> s) t0 -> Rounds r t0

def checkRoundsE : List CodeE -> WordList -> Option (WordList)
  | [],u => some u
  | c :: cs,u =>
    match roundStepE c u with
    | none => none
    | some v => checkRoundsE cs v

theorem checkRoundsE_sound (cs : List CodeE) :
    ∀ (u v : WordList),checkRoundsE cs u = some v ->
      Rounds (evalWords u default) (evalWords v default) := by
  induction cs with
  | nil =>
    intro u v h
    injection h with h; subst h
    exact Rounds.refl _
  | cons c cs ih =>
    intro u v h
    dsimp [checkRoundsE] at h
    cases hW : roundStepE c u with
    | none => rw [hW] at h; contradiction
    | some w =>
      rw [hW] at h
      rcases roundStepE_trans c u w hW with ⟨r,hR,hEq⟩
      refine Rounds.next hR ?_
      rw [<- hEq]
      exact ih w v h

theorem good_of_checks (u ds : WordList)
    (hD : ds.all isDigitWord = true)
    (hS : wordScale u * wordScale ds = 1 / 2)
    (hF : wordMass u * 2 + wordMassK u + wordScale u * wordMassK ds <= 1 / 64)
    (hU : HasV15Prefix u) (hW : hasQKSubword u =
        true) (hLo : HasKKPrefix ds) (hHi : HasQ6Suffix ds) :
    Good (evalWords (u ++ ds) (d0 +> (d1 +> default))) := by
  rcases exists_digitVal_of_all_isDigitWord ds hD with ⟨A,hI⟩
  refine Good.intro u A ds.length ds hI ?_ hF hU hW hLo hHi
  rw [<- (digitVal_scale_and_mass hI).1]
  exact hS


def initWords_A : WordList := [Q]

def initCodes_A : List CodeE := [
  .More CP0 5 (.Stop 5),
  .More CT 5 (.More CT 11 (.More CS10 5 (.More CS01 2 (.More CP0 4 (.Stop 4))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CP0 47 (.More CT 93 (.More CP0 187 (.More CP0 373
      (.Stop 373))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CS10 383 (.More CS01 191 (.More CP0 382 (.More CP1 763 (.More CP0 1526 (.More
      CP0 3051 (.Stop 3051)))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CT 1535 (.More CP0 3071 (.More CT 6141 (.More CT 12283 (.More CT 24567 (.More CT
      49135 (.More CS10 24567 (.More CS00 12283 (.More CS01 6141 (.More CP0 12282 (.More CP1 24563
      (.More CP1 49126 (.More CP0 98252 (.More CP0 196503 (.Stop 196503))))))))))))))))))))))
]

def goodPrefix_A : WordList := [V,V,V,V,V,V,V,V,V,V,V,V,V,V,V,Q,K,K,V,V,V,V,V]

def goodSuffix_A : WordList := [K,K,K,Q,Q,K,K,Q,Q,Q,Q,Q,Q,Q,Q,Q]

theorem init_rounds_A :
    Rounds (evalWords initWords_A default) (evalWords (goodPrefix_A ++ goodSuffix_A) (d0 +> (d1 +>
        default))) := by
  have h1 : Rounds (evalWords initWords_A default) (evalWords (goodPrefix_A ++ goodSuffix_A ++
      [K,Q]) default) := by
    apply checkRoundsE_sound initCodes_A
    decide
  simpa [evalWords_append,evalWords] using h1

theorem init_good_A :
    Good (evalWords (goodPrefix_A ++ goodSuffix_A) (d0 +> (d1 +> default))) := by
  apply good_of_checks
  · decide
  · norm_num [goodPrefix_A,goodSuffix_A,wordScale]
  · norm_num [goodPrefix_A,goodSuffix_A,wordMass,wordMassK,wordScale]
  · exact ⟨goodPrefix_A.take 20,by decide⟩
  · decide
  · exact ⟨goodSuffix_A.drop 2,by decide⟩
  · exact ⟨goodSuffix_A.take 10,by decide⟩


def initWords_B : WordList := [V,Q,Q]

def initCodes_B : List CodeE := [
  (.More CT 5 (.More CS11 2 (.More CP0 4 (.Stop 4)))),
  (.More CT 5 (.More CT 11 (.More CS11 5 (.More CT 10 (.More CP0 21 (.More CP0 41 (.Stop 41))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CS11 11 (.More CT 22 (.More CT 45 (.More CT 91 (.More
      CS10 45 (.More CP0 89 (.More CP0 177 (.More CP0 353 (.Stop 353)))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CS11 23 (.More CT 46 (.More CT 93 (.More
      CT 187 (.More CS11 93 (.More CT 186 (.More CT 373 (.More CT 747 (.More CS10 373 (.More CP0 745
      (.More CS00 372 (.More CS10 185 (.More CS01 92 (.More CP0 184 (.More CP0 367 (.Stop
      367)))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CS11 47 (.More CT 94 (.More
      CT 189 (.More CT 379 (.More CS11 189 (.More CT 378 (.More CT 757 (.More CT 1515 (.More CS11
      757 (.More CT 1514 (.More CS00 757 (.More CP0 1513 (.More CT 3025 (.More CT 6051 (.More CS10
      3025 (.More CS00 1512 (.More CS10 755 (.More CS00 377 (.More CP1 753 (.More CP0 1506 (.More
      CP0 3011 (.Stop 3011))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CS11 95
      (.More CT 190 (.More CT 381 (.More CT 763 (.More CS11 381 (.More CT 762 (.More CT 1525 (.More
      CT 3051 (.More CS11 1525 (.More CT 3050 (.More CS00 1525 (.More CT 3049 (.More CT 6099 (.More
      CT 12199 (.More CP0 24399 (.More CP0 48797 (.More CT 97593 (.More CT 195187 (.More CT 390375
      (.More CS10 195187 (.More CS00 97593 (.More CP0 195185 (.More CS00 97592 (.More CS10 48795
      (.More CS01 24397 (.More CP1 48794 (.More CP0 97588 (.More CP0 195175 (.Stop
      195175))))))))))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CS11 191 (.More CT 382 (.More CT 765 (.More CT 1531 (.More CS11 765 (.More CT 1530 (.More CT
      3061 (.More CT 6123 (.More CS11 3061 (.More CT 6122 (.More CS00 3061 (.More CT 6121 (.More CT
      12243 (.More CT 24487 (.More CT 48975 (.More CT 97951 (.More CT 195903 (.More CT 391807 (.More
      CT 783615 (.More CP0 1567231 (.More CT 3134461 (.More CS10 1567230 (.More CP0 3134459 (.More
      CT 6268917 (.More CT 12537835 (.More CT 25075671 (.More CS10 12537835 (.More CS00 6268917
      (.More CS00 3134458 (.More CP0 6268915 (.More CS01 3134457 (.More CP0 6268914 (.More CS10
      3134456 (.More CP0 6268911 (.More CP1 12537821 (.More CP1 25075642 (.More CP0 50151284 (.More
      CP0 100302567 (.Stop 100302567)))))))))))))))))))))))))))))))))))))))))))))),
  (.More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CS11 383 (.More CT 766 (.More CT 1533 (.More CT 3067 (.More CS11 1533 (.More CT
      3066 (.More CT 6133 (.More CT 12267 (.More CS11 6133 (.More CT 12266 (.More CS00 6133 (.More
      CT 12265 (.More CT 24531 (.More CT 49063 (.More CT 98127 (.More CT 196255 (.More CT 392511
      (.More CT 785023 (.More CT 1570047 (.More CT 3140095 (.More CT 6280191 (.More CS11 3140095
      (.More CT 6280190 (.More CT 12560381 (.More CT 25120763 (.More CT 50241527 (.More CP0
      100483055 (.More CS00 50241527 (.More CT 100483053 (.More CS10 50241526 (.More CT 100483051
      (.More CS11 50241525 (.More CT 100483050 (.More CT 200966101 (.More CT 401932203 (.More CT
      803864407 (.More CT 1607728815 (.More CS10 803864407 (.More CS00 401932203 (.More CS00
      200966101 (.More CP0 401932201 (.More CP1 803864401 (.More CP0 1607728802 (.More CS11
      803864400 (.More CP1 1607728800 (.More CP1 3215457600 (.More CP0 6430915200 (.More CS10
      3215457599 (.More CP0 6430915197 (.More CS01 3215457598 (.More CP1 6430915196 (.More CP1
      12861830392 (.More CP0 25723660784 (.More CP0 51447321567 (.Stop
      51447321567)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def goodPrefix_B : WordList :=
  [V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, Q, V, K, V, V, V, V, V, V, V, V, V, V,
   Q, V, V, V, V, V, K, V, Q, V, Q, V, V, V, V, V, Q, K, K, V, V, V, Q, V, V, V, Q, V, K, V,
   V, V, V]

def goodSuffix_B : WordList :=
  [K, K, K, K, K, Q, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q,
   Q, Q, Q, Q]

theorem init_rounds_B :
    Rounds (evalWords initWords_B default) (evalWords (goodPrefix_B ++ goodSuffix_B) (d0 +> (d1 +>
        default))) := by
  have h1 : Rounds (evalWords initWords_B default) (evalWords (goodPrefix_B ++ goodSuffix_B ++
      [K,Q]) default) := by
    apply checkRoundsE_sound initCodes_B
    decide
  simpa [evalWords_append,evalWords] using h1

theorem init_good_B :
    Good (evalWords (goodPrefix_B ++ goodSuffix_B) (d0 +> (d1 +> default))) := by
  apply good_of_checks
  · decide
  · norm_num [goodPrefix_B,goodSuffix_B,wordScale]
  · norm_num [goodPrefix_B,goodSuffix_B,wordMass,wordMassK,wordScale]
  · exact ⟨goodPrefix_B.take (goodPrefix_B.length - 3),by decide⟩
  · decide
  · exact ⟨goodSuffix_B.drop 2,by decide⟩
  · exact ⟨goodSuffix_B.take (goodSuffix_B.length - 6),by decide⟩


def initWords_C : WordList := [K,Q]

def initCodes_C : List CodeE := [
  .More CS00 1 (.More CP0 1 (.Stop 1)),
  .More CT 5 (.More CS10 2 (.More CT 3 (.More CS10 1 (.More CP0 1 (.Stop 1))))),
  .More CT 5 (.More CT 11 (.More CS11 5 (.More CT 10 (.More CS01 5 (.More CT 10 (.More CS00 5 (.More
      CP0 9 (.Stop 9)))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CS11 11 (.More CT 22 (.More CS00 11 (.More CT 21
      (.More CS10 10 (.More CT 19 (.More CS10 9 (.More CP0 17 (.More CP0 33 (.Stop 33)))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CS11 23 (.More CT 46 (.More CS00 23
      (.More CT 45 (.More CS11 22 (.More CT 44 (.More CS01 22 (.More CT 44 (.More CT 89 (.More CS10
      44 (.More CP0 87 (.More CS00 43 (.More CS00 21 (.More CP0 41 (.Stop 41)))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CS11 47 (.More CT 94 (.More
      CS00 47 (.More CT 93 (.More CS11 46 (.More CT 92 (.More CS00 46 (.More CT 91 (.More CT 183
      (.More CS11 91 (.More CT 182 (.More CS00 91 (.More CS00 45 (.More CT 89 (.More CS10 44 (.More
      CP0 87 (.More CP0 173 (.More CP0 345 (.Stop 345))))))))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CS11 95 (.More
      CT 190 (.More CS00 95 (.More CT 189 (.More CS11 94 (.More CT 188 (.More CS00 94 (.More CT 187
      (.More CT 375 (.More CS11 187 (.More CT 374 (.More CS00 187 (.More CS00 93 (.More CT 185
      (.More CS11 92 (.More CT 184 (.More CT 369 (.More CT 739 (.More CS10 369 (.More CP0 737 (.More
      CS01 368 (.More CP0 736 (.More CP0 1471 (.More CP0 2941 (.Stop
      2941)))))))))))))))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CS11 191 (.More CT 382 (.More CS00 191 (.More CT 381 (.More CS11 190 (.More CT 380 (.More CS00
      190 (.More CT 379 (.More CT 759 (.More CS11 379 (.More CT 758 (.More CS00 379 (.More CS00 189
      (.More CT 377 (.More CS11 188 (.More CT 376 (.More CT 753 (.More CT 1507 (.More CS11 753
      (.More CT 1506 (.More CS00 753 (.More CT 1505 (.More CT 3011 (.More CT 6023 (.More CS10 3011
      (.More CS01 1505 (.More CP1 3010 (.More CP1 6020 (.More CP0 12040 (.More CS11 6019 (.More CP0
      12038 (.More CP0 24075 (.Stop 24075))))))))))))))))))))))))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CS11 383 (.More CT 766 (.More CS00 383 (.More CT 765 (.More CS11 382 (.More CT
      764 (.More CS00 382 (.More CT 763 (.More CT 1527 (.More CS11 763 (.More CT 1526 (.More CS00
      763 (.More CS00 381 (.More CT 761 (.More CS11 380 (.More CT 760 (.More CT 1521 (.More CT 3043
      (.More CS11 1521 (.More CT 3042 (.More CS00 1521 (.More CT 3041 (.More CT 6083 (.More CT 12167
      (.More CP0 24335 (.More CT 48669 (.More CT 97339 (.More CT 194679 (.More CS11 97339 (.More CT
      194678 (.More CT 389357 (.More CS10 194678 (.More CS10 97338 (.More CS11 48668 (.More CP0
      97336 (.More CS10 48667 (.More CS00 24333 (.More CS00 12166 (.More CS10 6082 (.More CS11 3040
      (.More CP1 6080 (.More CP0 12160 (.More CP0 24319 (.Stop
      24319))))))))))))))))))))))))))))))))))))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CT 1535 (.More CS11 767 (.More CT 1534 (.More CS00 767 (.More CT 1533 (.More
      CS11 766 (.More CT 1532 (.More CS00 766 (.More CT 1531 (.More CT 3063 (.More CS11 1531 (.More
      CT 3062 (.More CS00 1531 (.More CS00 765 (.More CT 1529 (.More CS11 764 (.More CT 1528 (.More
      CT 3057 (.More CT 6115 (.More CS11 3057 (.More CT 6114 (.More CS00 3057 (.More CT 6113 (.More
      CT 12227 (.More CT 24455 (.More CT 48911 (.More CT 97823 (.More CT 195647 (.More CT 391295
      (.More CS11 195647 (.More CT 391294 (.More CT 782589 (.More CS11 391294 (.More CP1 782588
      (.More CT 1565176 (.More CP0 3130353 (.More CS00 1565176 (.More CP1 3130351 (.More CT 6260702
      (.More CT 12521405 (.More CT 25042811 (.More CS10 12521405 (.More CS00 6260702 (.More CS10
      3130350 (.More CS10 1565174 (.More CS10 782586 (.More CS10 391292 (.More CS10 195645 (.More
      CS00 97822 (.More CP1 195643 (.More CP1 391286 (.More CP0 782572 (.More CP0 1565143 (.Stop
      1565143))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CT 767 (.More CT 1535 (.More CT 3071 (.More CS11 1535 (.More CT 3070 (.More CS00 1535 (.More
      CT 3069 (.More CS11 1534 (.More CT 3068 (.More CS00 1534 (.More CT 3067 (.More CT 6135 (.More
      CS11 3067 (.More CT 6134 (.More CS00 3067 (.More CS00 1533 (.More CT 3065 (.More CS11 1532
      (.More CT 3064 (.More CT 6129 (.More CT 12259 (.More CS11 6129 (.More CT 12258 (.More CS00
      6129 (.More CT 12257 (.More CT 24515 (.More CT 49031 (.More CT 98063 (.More CT 196127 (.More
      CT 392255 (.More CT 784511 (.More CS11 392255 (.More CT 784510 (.More CT 1569021 (.More CS11
      784510 (.More CT 1569020 (.More CT 3138041 (.More CT 6276083 (.More CS10 3138041 (.More CT
      6276081 (.More CT 12552163 (.More CT 25104327 (.More CT 50208655 (.More CP0 100417311 (.More
      CP1 200834621 (.More CP1 401669242 (.More CP0 803338484 (.More CT 1606676967 (.More CT
      3213353935 (.More CT 6426707871 (.More CT 12853415743 (.More CS10 6426707871 (.More CS00
      3213353935 (.More CS00 1606676967 (.More CS01 803338483 (.More CP0 1606676966 (.More CP1
      3213353931 (.More CP0 6426707862 (.More CS10 3213353930 (.More CS10 1606676964 (.More CS10
      803338481 (.More CS01 401669240 (.More CP1 803338480 (.More CP1 1606676960 (.More CP0
      3213353920 (.More CP0 6426707839 (.Stop
      6426707839)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
]

def goodPrefix_C : WordList :=
  [V, V, V, V, V, V, V, V, V, V, V, Q, V, K, V, Q, V, K, V, V, Q, V, K, K, V, Q, V, V, V, Q,
   V, K, V, V, V, V, V, V, V, Q, V, V, Q, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, Q,
   K, K, K, V, V, V, Q, Q, Q, K, V, V, V, V]

def goodSuffix_C : WordList :=
  [K, K, K, K, K, K, K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, Q,
   Q]

set_option maxHeartbeats 2000000 in
-- Justification: Finite decision procedure over the 12-round CodeE trace for kind C.
theorem init_rounds_C :
    Rounds (evalWords initWords_C default) (evalWords (goodPrefix_C ++ goodSuffix_C) (d0 +> (d1 +>
        default))) := by
  have h1 : Rounds (evalWords initWords_C default) (evalWords (goodPrefix_C ++ goodSuffix_C ++
      [K,Q]) default) := by
    apply checkRoundsE_sound initCodes_C
    decide
  simpa [evalWords_append,evalWords] using h1

set_option maxHeartbeats 2000000 in
-- Justification: Arithmetic and prefix/suffix verification for the kind-C initial Good word.
theorem init_good_C :
    Good (evalWords (goodPrefix_C ++ goodSuffix_C) (d0 +> (d1 +> default))) := by
  apply good_of_checks
  · decide
  · norm_num [goodPrefix_C,goodSuffix_C,wordScale]
  · norm_num [goodPrefix_C,goodSuffix_C,wordMass,wordMassK,wordScale]
  · exact ⟨goodPrefix_C.take 71,by decide⟩
  · decide
  · exact ⟨goodSuffix_C.drop 2,by decide⟩
  · exact ⟨goodSuffix_C.take 25,by decide⟩


def initWords_D : WordList := [V]

def initCodes_D : List CodeE := [
  .More CT 5 (.Stop 6),
  .More CT 5 (.More CT 11 (.More CP1 23 (.More CP0 46 (.Stop 46)))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CS11 47 (.More CP1 94 (.More
      CP0 188 (.More CP0 375 (.Stop 375))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CS11 95 (.More
      CT 190 (.More CT 381 (.More CT 763 (.More CS10 381 (.More CS00 190 (.More CS10 94 (.More CS11
      46 (.More CP1 92 (.More CP0 184 (.More CP0 367 (.Stop 367))))))))))))))))),
  .More CT 5 (.More CT 11 (.More CT 23 (.More CT 47 (.More CT 95 (.More CT 191 (.More CT 383 (.More
      CS11 191 (.More CT 382 (.More CT 765 (.More CT 1531 (.More CP0 3063 (.More CP1 6125 (.More CT
      12250 (.More CT 24501 (.More CT 49003 (.More CS10 24501 (.More CS00 12250 (.More CS10 6124
      (.More CS10 3061 (.More CP1 6121 (.More CP0 12242 (.More CP0 24483 (.Stop
      24483)))))))))))))))))))))))
]

def goodPrefix_D : WordList := [V,V,V,V,V,V,V,V,Q,V,V,V,V,V,V,V,V,Q,K,Q,Q,V,V,V]

def goodSuffix_D : WordList := [K,K,Q,K,K,Q,K,Q,Q,Q,Q,Q,Q]

theorem init_rounds_D :
    Rounds (evalWords initWords_D default) (evalWords (goodPrefix_D ++ goodSuffix_D) (d0 +> (d1 +>
        default))) := by
  have h1 : Rounds (evalWords initWords_D default) (evalWords (goodPrefix_D ++ goodSuffix_D ++
      [K,Q]) default) := by
    apply checkRoundsE_sound initCodes_D
    decide
  simpa [evalWords_append,evalWords] using h1

theorem init_good_D :
    Good (evalWords (goodPrefix_D ++ goodSuffix_D) (d0 +> (d1 +> default))) := by
  apply good_of_checks
  · decide
  · norm_num [goodPrefix_D,goodSuffix_D,wordScale]
  · norm_num [goodPrefix_D,goodSuffix_D,wordMass,wordMassK,wordScale]
  · exact ⟨goodPrefix_D.take 21,by decide⟩
  · decide
  · exact ⟨goodSuffix_D.drop 2,by decide⟩
  · exact ⟨goodSuffix_D.take 7,by decide⟩



theorem initKind_good (kind : InitKind) :
    ∃ r₁, Rounds (initTape kind) r₁ ∧ Good r₁ := by
  cases kind
  · exact ⟨_, init_rounds_A, init_good_A⟩
  · exact ⟨_, init_rounds_B, init_good_B⟩
  · exact ⟨_, init_rounds_C, init_good_C⟩
  · exact ⟨_, init_rounds_D, init_good_D⟩

inductive Num : Nat → BitWord → List Call → Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

def NumSide (cs : Call → HalfTape → HalfTape → Prop) (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs, Num k w hs → Side cs hs (w +> r) r'

theorem numSide_zero {r r' : HalfTape} (h : NumSide cs 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

include R in
theorem numSide_T {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs ((1 + n) * 2) r r') : NumSide cs (1 + n) (t +> r) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil]
    refine seg_apply (seg_cp_t R m) ?_
    have hN2 : Num ((1 + n) * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : (1 + n) * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil]
    refine seg_apply (seg_cj_t R m) ?_
    have hN2 : Num ((1 + n) * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : (1 + n) * 2 = 2 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.even (1 + m * 2)
    simpa using hI [] _ hN2

include R in
theorem numSide_pair0 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (n * 2) r r') : NumSide cs (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil, ← append_assoc d1 d0 r]
    cases m with
    | zero =>
      have hn0 : n * 2 = 0 := by omega
      rw [hn0] at hI
      have hr' := numSide_zero hI
      subst hr'
      rw [← append_assoc t one r]
      exact seg_apply R.r0e (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine seg_apply (seg_cp_d1d0 R m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil, ← append_assoc d1 d0 r]
    refine seg_apply (seg_cj_d1d0 R m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

include R in
theorem numSide_pair1 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (1 + n * 2) r r') : NumSide cs (1 + n) (d1 +> (d1 +> r)) (t +> r') := by
  intro w hs hN
  generalize hk : 1 + n = k at hN
  cases hN with
  | zero => omega
  | @odd m =>
    simp only [append_nil, ← append_assoc d1 d1 r]
    refine seg_apply (seg_cp_d1d1 R m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (m * 2)) := by
      have hm : 1 + n * 2 = 1 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (m * 2)
    simpa using hI [] _ hN1
  | @even m =>
    simp only [append_nil, ← append_assoc d1 d1 r]
    refine seg_apply (seg_cj_d1d1 R m) ?_
    have hN1 : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ (1 + m * 2)) := by
      have hm : 1 + n * 2 = 1 + (1 + m * 2) * 2 := by omega
      rw [hm]; exact Num.odd (1 + m * 2)
    simpa using hI [] _ hN1

include R in
theorem numSide_short00 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (n * 2) r r') : NumSide cs (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := numSide_zero hI
      subst hr'
      rw [← append_assoc d0 one r]
      exact seg_apply R.r0i (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine seg_apply (seg_cj_d0d0 R n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2

include R in
theorem numSide_short01 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (1 + n * 2) r r') : NumSide cs (2 + n * 4) (d1 +> r) (d0 +> r') := by
  intro w hs hN
  generalize hk : 2 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = n * 2 := by omega
    subst hm
    refine seg_apply (seg_cj_d1d0_short R n) ?_
    simpa using hI [] _ (Num.odd n)

include R in
theorem numSide_short10 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (n * 2) r r') : NumSide cs (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := numSide_zero hI
      subst hr'
      rw [← append_assoc d1 one r]
      exact seg_apply (seg_cj_ch_d0 R) (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine seg_apply (seg_cj_d0d1 R n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2

include R in
theorem numSide_short11 {n : Nat} {r r' : HalfTape}
    (hI : NumSide cs (1 + n * 2) r r') : NumSide cs (4 + n * 4) (d1 +> r) (d1 +> r') := by
  intro w hs hN
  generalize hk : 4 + n * 4 = k at hN
  cases hN with
  | zero => omega
  | odd _ => omega
  | @even m =>
    simp only [append_nil]
    have hm : m = 1 + n * 2 := by omega
    subst hm
    refine seg_apply (seg_cj_d1d1_short R n) ?_
    simpa using hI [] _ (Num.odd n)

include R in
theorem rincs_to_numSide {k : Nat} {r r' : HalfTape} (hI : RIncs k r r') :
    NumSide cs k r r' := by
  induction hI with
  | zero r =>
    intro w hs hN
    generalize hk : 0 = k0 at hN
    cases hN with
    | zero => exact Side.nil (one +> r)
    | odd _ => omega
    | even _ => omega
  | T _ ih => exact numSide_T R ih
  | pair0 _ ih => exact numSide_pair0 R ih
  | pair1 _ ih => exact numSide_pair1 R ih
  | short00 _ ih => exact numSide_short00 R ih
  | short01 _ ih => exact numSide_short01 R ih
  | short10 _ ih => exact numSide_short10 R ih
  | short11 _ ih => exact numSide_short11 R ih

theorem step_round_of_rincs6 {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (R : SegRules (callStep tm fCR fCL))
    (h0z : ∀ r, (fCL lh r) [tm]⊢⁺ (fCR ([1] +> default) .ca r))
    (h0A : ∀ r, (fCL ([1] +> default) r) [tm]⊢⁺ (fCR lh .ch r))
    {r r' : HalfTape} (hI : RIncs 6 r r') :
    (fCL lh r) [tm]⊢⁺ fCL lh (t +> r') := by
  have hC := rincs_to_numSide R hI [] ([.cj] ++ [.ch] ^ 2) (Num.even 2)
  have hS := seg_apply (seg_ca_ch R) hC
  dsimp at hS
  rcases hS with _ | ⟨hca, hrest⟩
  rcases hrest with _ | ⟨hch, hnil⟩
  cases hnil
  exact stepPlus_trans (h0z r)
    (stepPlus_trans (hca ([1] +> default))
      (stepPlus_trans (h0A _) (hch lh)))

theorem stepStar_of_rounds {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (R : SegRules (callStep tm fCR fCL))
    (h0z : ∀ r, (fCL lh r) [tm]⊢⁺ (fCR ([1] +> default) .ca r))
    (h0A : ∀ r, (fCL ([1] +> default) r) [tm]⊢⁺ (fCR lh .ch r))
    {r r' : HalfTape} (h : Rounds r r') :
    (fCL lh r) [tm]⊢* fCL lh r' := by
  induction h with
  | refl _ => exact ⟨0, rfl⟩
  | next hR _ ih =>
    rcases step_round_of_rincs6 R h0z h0A hR with ⟨n, _, hn⟩
    rcases ih with ⟨m, hm⟩
    exact ⟨n + m, multiStep_trans_add tm _ _ _ n m hn hm⟩

theorem isSome_of_multiStep_add {tm : Machine (Fin 2) (Fin 6)}
    {c c' : Cfg (Fin 2) (Fin 6)} {j d : Nat}
    (h : multiStep tm c (j + d) = some c') :
    (multiStep tm c j).isSome := by
  rw [multiStep_add_bind] at h
  cases h_j : multiStep tm c j with
  | none => rw [h_j] at h; contradiction
  | some _ => rfl

theorem reach_good_arbitrarily_far {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (R : SegRules (callStep tm fCR fCL))
    (h0z : ∀ r, (fCL lh r) [tm]⊢⁺ (fCR ([1] +> default) .ca r))
    (h0A : ∀ r, (fCL ([1] +> default) r) [tm]⊢⁺ (fCR lh .ch r))
    (kind : InitKind)
    (h0B : (init []) [tm]⊢⁺ fCL lh (initTape kind))
    (m : Nat) :
    ∃ N ≥ m, ∃ r, multiStep tm (init []) N = some (fCL lh r) ∧ Good r := by
  induction m with
  | zero =>
    rcases h0B with ⟨k1, _, hk1⟩
    rcases initKind_good kind with ⟨r₁, h_rnd, h_gd⟩
    rcases stepStar_of_rounds R h0z h0A h_rnd with ⟨k2, hk2⟩
    exact ⟨k1 + k2, Nat.zero_le _, _, multiStep_trans_add tm _ _ _ k1 k2 hk1 hk2, h_gd⟩
  | succ m ih =>
    rcases ih with ⟨N, hN, r, h_ms, h_good⟩
    rcases good_next_round h_good with ⟨r', hR, h_good'⟩
    rcases step_round_of_rincs6 R h0z h0A hR with ⟨k, hk_pos, h_step_k⟩
    exact ⟨N + k, Nat.add_le_add hN hk_pos, t +> r',
      multiStep_trans_add tm _ _ _ N k h_ms h_step_k, h_good'⟩

end

@[expose] public section

theorem does_not_halt_of_seg_rules {tm : Machine (Fin 2) (Fin 6)}
    {fCR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {fCL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (R : SegRules (callStep tm fCR fCL))
    (h0z : ∀ r, (fCL lh r) [tm]⊢⁺ (fCR ([1] +> default) .ca r))
    (h0A : ∀ r, (fCL ([1] +> default) r) [tm]⊢⁺ (fCR lh .ch r))
    (kind : InitKind)
    (h0B : (init []) [tm]⊢⁺ fCL lh (initTape kind)) :
    IsNotHalt tm := by
  intro cfg h_reach
  rcases h_reach with ⟨n, hn⟩
  rcases reach_good_arbitrarily_far R h0z h0A kind h0B (n + 1) with ⟨N, hN, _, h_N, _⟩
  have h_eq : (n + 1) + (N - (n + 1)) = N := Nat.add_sub_of_le hN
  rw [← h_eq] at h_N
  have h_some := isSome_of_multiStep_add h_N
  rw [multiStep_succ_eq, hn] at h_some
  exact h_some

set_option maxHeartbeats 2000000 in
-- Justification: Finite symbolic execution of the 15 elementary SegRules and 3 stem steps.
theorem is_not_halt : IsNotHalt target := by
  refine does_not_halt_of_seg_rules
    (fCR := cfgCR false E C) (fCL := cfgCL false A)
    (by prove_seg_rules)
    (fun r => by
      dsimp [cfgCL, cfgCR, callState, callWord, lh]
      try simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
      execute)
    (fun r => by
      dsimp [cfgCL, cfgCR, callState, callWord, lh]
      try simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
      execute)
    .kindA
    (by
      have h_init : (init [] : Cfg (Fin 2) (Fin 6)) = (default {{A}}> default) := rfl
      rw [h_init]
      dsimp [initTape, cfgCL, lh, d1]
      try simp only [↓reduceIte, Bool.false_eq_true, append_cons, append_nil]
      execute)

end

end BusyBeaver.M_1RB0RA_1LC0RC_1LE0LD_1LC1LF_1RA1LC_1LBHHH
