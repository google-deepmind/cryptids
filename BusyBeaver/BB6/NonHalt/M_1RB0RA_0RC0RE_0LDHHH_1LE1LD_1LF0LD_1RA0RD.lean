/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Calculi.WordCalculusA
public import BusyBeaver.Calculi.WordCalculusB
public import BusyBeaver.Calculi.WordCalculusC
public import BusyBeaver.Calculi.WordCalculusD
public import BusyBeaver.Calculi.WordCalculusE

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RA_0RC0RE_0LDHHH_1LE1LD_1LF0LD_1RA0RD

@[expose] public section

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_0RC0RE_0LDHHH_1LE1LD_1LF0LD_1RA0RD"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

abbrev target_tm : Machine (Fin 2) (Fin 6) := target

end

namespace Solution

open Counter WordCalculus WordCalculus.Word

@[expose] public section

variable {Γ₀ Λ₀ α : Type*} [Inhabited Γ₀] [Inhabited Λ₀]

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

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

theorem step_one {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]

theorem step_plus {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    (tm : Machine Γ₀ Λ₀) (c_1 c_2 : Cfg Γ₀ Λ₀) (h : c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide +kernel, step_one tm c_1 c_2 h⟩

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
    c_1 [tm]⊢^{n + m} c_3 := by
  rw [multiStep_add, h₁]; simp [h₂]

theorem plus_to_star {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 : Cfg Γ₀ Λ₀} (h : c_1 [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

theorem plus_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans tm c_1 c_2 c_3 n m hn hm⟩

theorem plus_star_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m),
    multiStep_trans tm c_1 c_2 c_3 n m hn hm⟩

theorem step_star_trans {Γ₀ Λ₀ : Type*} [Inhabited Γ₀] [Inhabited Λ₀]
    {tm : Machine Γ₀ Λ₀} {c_1 c_2 c_3 : Cfg Γ₀ Λ₀}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  plus_star_trans (step_plus tm c_1 c_2 h₁) h₂

theorem eq_state_head {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c1 c2 : Cfg Γ Λ}
    (hq : c1.q = c2.q) (hh : c1.tape.head = c2.tape.head) (h : c1 = c2) : c1 [tm]⊢* c2 :=
  h ▸ ⟨0, rfl⟩

theorem step_R {Λ : Type*} [Inhabited Λ]
    {tm : Machine (Fin 2) Λ} {q q' : Λ} {h w : Fin 2} {l r : HalfTape} {c_3 : Cfg (Fin 2) Λ}
    (hm : tm q h = some (some q', Stmt.write w Dir.right))
    (h₂ : (⟨some q', ⟨r.head, w >> l, r.tail⟩⟩ : Cfg (Fin 2) Λ) [tm]⊢* c_3) :
    (⟨some q, ⟨h, l, r⟩⟩ : Cfg (Fin 2) Λ) [tm]⊢⁺ c_3 :=
  step_star_trans (by simp [step, hm, Turing.Tape.write, Turing.Tape.move]) h₂

theorem step_L {Λ : Type*} [Inhabited Λ]
    {tm : Machine (Fin 2) Λ} {q q' : Λ} {h w : Fin 2} {l r : HalfTape} {c_3 : Cfg (Fin 2) Λ}
    (hm : tm q h = some (some q', Stmt.write w Dir.left))
    (h₂ : (⟨some q', ⟨l.head, l.tail, w >> r⟩⟩ : Cfg (Fin 2) Λ) [tm]⊢* c_3) :
    (⟨some q, ⟨h, l, r⟩⟩ : Cfg (Fin 2) Λ) [tm]⊢⁺ c_3 :=
  step_star_trans (by simp [step, hm, Turing.Tape.write, Turing.Tape.move]) h₂

macro "finish" : tactic =>
  `(tactic| refine eq_state_head (by with_reducible rfl) rfl rfl)

macro "step" : tactic =>
  `(tactic| (try refine plus_to_star ?_) <;>
    (first | refine step_R (by
               try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
                 Turing.ListBlank.head_cons, default_head]
               rfl) ?_
           | refine step_L (by
               try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
                 Turing.ListBlank.head_cons, default_head]
               rfl) ?_) <;>
    (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.ListBlank.head_cons,
       Turing.ListBlank.tail_cons, cons_zero_default, default_head, default_tail]))

macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | finish | step)))

abbrev t : BitWord := [1, 1, 0, 0]
abbrev d0 : BitWord := [0, 0]
abbrev d1 : BitWord := [1, 0]
abbrev one : BitWord := [1]
abbrev lh : HalfTape := [1, 0, 1] +> default
abbrev w_pre : BitWord := t ++ t ++ one

@[simp] theorem d0_append_default : d0 +> (default : HalfTape) = default := by
  simp [d0]

inductive Call where
  | ch
  | cj
  | cp
  | ca

def CallStep (tm : Machine (Fin 2) (Fin 6))
    (cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6))
    (cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6))
    (c : Call) (r1 r2 : HalfTape) : Prop :=
  ∀ l, (cfgR l c r1) [tm]⊢⁺ (cfgL l r2)

@[simp] theorem pow_zero_list {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem pow_succ_list {α : Type*} (l : List α) (n : Nat) :
    l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem pow_one_add_list {α : Type*} (l : List α) (n : Nat) :
    l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem pow_one_list {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

theorem pow_add_list {α : Type*} (l : List α) (m n : Nat) :
    l ^ (m + n) = l ^ m ++ l ^ n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_right_comm, pow_succ_list, pow_succ_list, ih, List.append_assoc]

theorem seg4 {tm : Machine (Fin 2) (Fin 6)}
    {cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c : Call} {w1 w2 : BitWord}
    (h1 : ∀ l r, (cfgR l c (w1 +> r)) [tm]⊢⁺ (cfgL l (w2 +> r))) :
    Seg (CallStep tm cfgR cfgL) [c] [] w1 w2 := by
  intro r1 r2 h; cases h
  exact Side.cons (fun l => h1 l r1) (Side.nil _)

theorem seg2 {tm : Machine (Fin 2) (Fin 6)}
    {cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c_in c_out : Call} {w1 w2 : BitWord} (mid : BitWord)
    (h1 : ∀ l r, (cfgR l c_in (w1 +> r)) [tm]⊢⁺ (cfgR (mid +> l) c_out r))
    (h2 : ∀ l r, (cfgL (mid +> l) r) [tm]⊢⁺ (cfgL l (w2 +> r))) :
    Seg (CallStep tm cfgR cfgL) [c_in] [c_out] w1 w2 := by
  intro r1 r2 h
  rcases h with _ | ⟨hc1, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact plus_trans (h1 l r1) (plus_trans (hc1 (mid +> l)) (h2 l r2))

theorem seg5 {tm : Machine (Fin 2) (Fin 6)}
    {cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    {c_in c1 c2 : Call} {w1 w2 : BitWord} (mid1 mid2 : BitWord)
    (h1 : ∀ l r, (cfgR l c_in (w1 +> r)) [tm]⊢⁺ (cfgR (mid1 +> l) c1 r))
    (h2 : ∀ l r, (cfgL (mid1 +> l) r) [tm]⊢⁺ (cfgR (mid2 +> l) c2 r))
    (h3 : ∀ l r, (cfgL (mid2 +> l) r) [tm]⊢⁺ (cfgL l (w2 +> r))) :
    Seg (CallStep tm cfgR cfgL) [c_in] [c1, c2] w1 w2 := by
  intro r1 r3 h
  rcases h with _ | ⟨hc1, hrest⟩
  rcases hrest with _ | ⟨hc2, hnil⟩
  cases hnil
  refine Side.cons (fun l => ?_) (Side.nil _)
  exact plus_trans (h1 l r1)
    (plus_trans (hc1 (mid1 +> l))
      (plus_trans (h2 l _)
        (plus_trans (hc2 (mid2 +> l)) (h3 l r3))))

structure BaseRules (stepRel : Call → HalfTape → HalfTape → Prop) : Prop where
  seg_cp_t : Seg stepRel [.cp] [.ch] t (t ++ [0])
  seg_cj_t : Seg stepRel [.cj] [.ch] t (t ++ one)
  seg_ch_t0 : Seg stepRel [.ch] [.cj] (t ++ [0]) t
  seg_ch_t1 : Seg stepRel [.ch] [.cj, .ch] (t ++ one) t
  seg_ch_t : Seg stepRel [.ch] [.ch, .ch] t t
  seg_cp_d10 : Seg stepRel [.cp] [] (d1 ++ d0) (t ++ one)
  seg_cj_d10 : Seg stepRel [.cj] [.cj] (d1 ++ d0) t
  seg_cp_d11 : Seg stepRel [.cp] [.cp] (d1 ++ d1) t
  seg_cj_d11 : Seg stepRel [.cj] [.cp, .ch] (d1 ++ d1) t
  seg_cj_d0 : Seg stepRel [.cj] [] d0 (d0 ++ one)
  seg_ch_d01 : Seg stepRel [.ch] [] (d0 ++ one) (d1 ++ one)
  seg_ch_d11 : Seg stepRel [.ch] [.cj] (d1 ++ one) d0
  seg_cj_d1 : Seg stepRel [.cj] [.cp] d1 d0
  seg_ch_d0 : Seg stepRel [.ch] [] d0 d1
  seg_ch_d1 : Seg stepRel [.ch] [.ch] d1 d0
  side_ch_blank : Side stepRel [.ch] default (d1 +> default)

variable {stepRel : Call → HalfTape → HalfTape → Prop}

theorem seg_ch_pow_t (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ n) ([Call.ch] ^ (n * 2)) t t := by
  induction n with
  | zero => exact Seg_nil t
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [pow_succ_list, h_eq, pow_add_list]
    exact Seg_par hb.seg_ch_t ih

theorem seg_ch_pair_pow {w2 : BitWord}
    (hw : Seg stepRel [.ch, .ch] [.ch] w2 w2) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) w2 w2 := by
  induction n with
  | zero => exact Seg_nil w2
  | succ n ih =>
    have h_eq : (n + 1) * 2 = 2 + n * 2 := by omega
    rw [h_eq, pow_add_list, pow_succ_list]
    exact Seg_par hw ih

theorem seg_ch2_d0 (hb : BaseRules stepRel) : Seg stepRel [.ch, .ch] [.ch] d0 d0 :=
  Seg_par hb.seg_ch_d0 hb.seg_ch_d1

theorem seg_ch2_d1 (hb : BaseRules stepRel) : Seg stepRel [.ch, .ch] [.ch] d1 d1 :=
  Seg_par hb.seg_ch_d1 hb.seg_ch_d0

theorem seg_ch_even_d0 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d0 d0 :=
  seg_ch_pair_pow (seg_ch2_d0 hb) n

theorem seg_ch_odd_d0 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ n) d0 d1 := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par hb.seg_ch_d0 (seg_ch_pair_pow (seg_ch2_d1 hb) n)

theorem seg_ch_even_d1 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (n * 2)) ([Call.ch] ^ n) d1 d1 :=
  seg_ch_pair_pow (seg_ch2_d1 hb) n

theorem seg_ch_odd_d1 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([Call.ch] ^ (1 + n * 2)) ([Call.ch] ^ (1 + n)) d1 d0 := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par hb.seg_ch_d1 (seg_ch_pair_pow (seg_ch2_d0 hb) n)

theorem seg_cp_ch_t (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ (1 + n)) ([.ch, .cj] ++ [.ch] ^ (n * 2)) t t := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par (Seg_par hb.seg_cp_t hb.seg_ch_t0) (seg_ch_pow_t hb n)

theorem seg_cj_ch_t (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (1 + n)) ([.ch, .cj] ++ [.ch] ^ (1 + n * 2)) t t := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par (Seg_par hb.seg_cj_t hb.seg_ch_t1) (seg_ch_pow_t hb n)

theorem seg_cp_ch_d10 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ (1 + n)) ([.cj] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d0) t := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par (Seg_par hb.seg_cp_d10 hb.seg_ch_t1) (seg_ch_pow_t hb n)

theorem seg_cj_ch_d10 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ n) ([.cj] ++ [.ch] ^ (n * 2)) (d1 ++ d0) t :=
  Seg_par hb.seg_cj_d10 (seg_ch_pow_t hb n)

theorem seg_cp_ch_d11 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cp] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (n * 2)) (d1 ++ d1) t :=
  Seg_par hb.seg_cp_d11 (seg_ch_pow_t hb n)

theorem seg_cj_ch_d11 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ n) ([.cp] ++ [.ch] ^ (1 + n * 2)) (d1 ++ d1) t := by
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using
    Seg_par hb.seg_cj_d11 (seg_ch_pow_t hb n)

theorem seg_cj_ch_even_d0 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (2 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d0 := by
  have h0 : Seg stepRel [.cj, .ch, .ch] [.cj] d0 d0 :=
    Seg_par hb.seg_cj_d0 (Seg_par hb.seg_ch_d01 hb.seg_ch_d11)
  have h1 := Seg_par h0 (seg_ch_pair_pow (seg_ch2_d0 hb) n)
  have heq : (2 + n * 2) = 1 + (1 + n * 2) := by omega
  simpa only [heq, pow_one_add_list, List.cons_append, List.nil_append] using h1

theorem seg_cj_ch_even_d10 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (n * 2)) ([.cp] ++ [.ch] ^ n) d1 d0 :=
  Seg_par hb.seg_cj_d1 (seg_ch_pair_pow (seg_ch2_d0 hb) n)

theorem seg_cj_ch_base_d01 (hb : BaseRules stepRel) :
    Seg stepRel [.cj, .ch] [] d0 (d1 ++ one) :=
  Seg_par hb.seg_cj_d0 hb.seg_ch_d01

theorem seg_cj_ch_odd_d01 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (3 + n * 2)) ([.cj] ++ [.ch] ^ n) d0 d1 := by
  have h0 : Seg stepRel [.cj, .ch, .ch, .ch] [.cj] d0 d1 :=
    Seg_par hb.seg_cj_d0 (Seg_par hb.seg_ch_d01 (Seg_par hb.seg_ch_d11 hb.seg_ch_d0))
  have h1 := Seg_par h0 (seg_ch_pair_pow (seg_ch2_d1 hb) n)
  have heq : (3 + n * 2) = 1 + (1 + (1 + n * 2)) := by omega
  simpa only [heq, pow_one_add_list, List.cons_append, List.nil_append] using h1

theorem seg_cj_ch_odd_d11 (hb : BaseRules stepRel) (n : Nat) :
    Seg stepRel ([.cj] ++ [.ch] ^ (1 + n * 2)) ([.cp] ++ [.ch] ^ n) d1 d1 := by
  have h0 : Seg stepRel [.cj, .ch] [.cp] d1 d1 := Seg_par hb.seg_cj_d1 hb.seg_ch_d0
  have h1 := Seg_par h0 (seg_ch_pair_pow (seg_ch2_d1 hb) n)
  simpa only [pow_one_add_list, List.cons_append, List.nil_append] using h1

inductive Num : Nat → BitWord → List Call → Prop where
  | zero : Num 0 one []
  | odd (n : Nat) : Num (1 + n * 2) [] ([.cp] ++ [.ch] ^ n)
  | even (n : Nat) : Num (2 + n * 2) [] ([.cj] ++ [.ch] ^ n)

theorem exists_num {k : Nat} (hK : 0 < k) : ∃ hs, Num k [] hs := by
  rcases even_or_odd_mul_two k with ⟨a, rfl⟩ | ⟨a, rfl⟩
  · cases a with
    | zero => omega
    | succ a =>
      have heq : (a + 1) * 2 = 2 + a * 2 := by omega
      rw [heq]; exact ⟨[.cj] ++ [.ch] ^ a, Num.even a⟩
  · exact ⟨[.cp] ++ [.ch] ^ a, Num.odd a⟩

theorem num_unique {k : Nat} {hs hs' : List Call}
    (h1 : Num k [] hs) (h2 : Num k [] hs') : hs = hs' := by
  cases h1 with
  | @odd n =>
    generalize hk : 1 + n * 2 = k0 at h2
    cases h2 with
    | @odd m =>
      have hnm : n = m := by omega
      subst hnm; rfl
    | even _ => omega
  | @even n =>
    generalize hk : 2 + n * 2 = k0 at h2
    cases h2 with
    | odd _ => omega
    | @even m =>
      have hnm : n = m := by omega
      subst hnm; rfl

def NumRun (stepRel : Call → HalfTape → HalfTape → Prop)
    (k : Nat) (r r' : HalfTape) : Prop :=
  ∀ w hs, Num k w hs → Side stepRel hs (w +> r) r'

theorem numRun_zero {r r' : HalfTape} (h : NumRun stepRel 0 r r') :
    r' = one +> r := by
  have h0 := h one [] Num.zero
  cases h0
  rfl

theorem numRun_d0_d0 (hb : BaseRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRun stepRel (n * 2) r r') :
    NumRun stepRel (2 + n * 4) (d0 +> r) (d0 +> r') := by
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
      have hr' := numRun_zero hI
      subst hr'
      rw [← append_assoc d0 one r]
      exact Seg_apply hb.seg_cj_d0 (Side.nil r)
    | succ n =>
      have heq : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [heq]
      refine Seg_apply (seg_cj_ch_even_d0 hb n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        rw [heq]; exact Num.even n
      simpa using hI [] _ hN2

theorem numRun_d0_d1 (hb : BaseRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRun stepRel (n * 2) r r') :
    NumRun stepRel (4 + n * 4) (d0 +> r) (d1 +> r') := by
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
      have hr' := numRun_zero hI
      subst hr'
      rw [← append_assoc d1 one r]
      exact Seg_apply (seg_cj_ch_base_d01 hb) (Side.nil r)
    | succ n =>
      have heq : 1 + (n + 1) * 2 = 3 + n * 2 := by omega
      rw [heq]
      refine Seg_apply (seg_cj_ch_odd_d01 hb n) ?_
      have hN2 : Num ((n + 1) * 2) [] ([.cj] ++ [.ch] ^ n) := by
        have heq2 : (n + 1) * 2 = 2 + n * 2 := by omega
        rw [heq2]; exact Num.even n
      simpa using hI [] _ hN2

theorem evalWords_eq_default_of_zero {A_val H : Nat} {da : WordList}
    (hD : DigitVal A_val H da) (hZ : A_val = 0) :
    evalWords da default = default := by
  induction hD with
  | nil => rfl
  | @zero A_val H u _ ih =>
    have hA0 : A_val = 0 := by omega
    dsimp only [evalWords]
    rw [ih hA0, d0_append_default]
  | one _ => omega

theorem numRun_of_digitVal (hb : BaseRules stepRel) {A_val H : Nat} {da : WordList}
    (hD : DigitVal A_val H da) (hPos : 0 < A_val) :
    NumRun stepRel ((A_val - 1) * 2) default (evalWords da default) := by
  induction hD with
  | nil => omega
  | @zero A_val H u _ ih =>
    have hA_pos : 0 < A_val := by omega
    have hIH := ih hA_pos
    have hs := numRun_d0_d0 hb hIH
    rw [d0_append_default] at hs
    have heq : (A_val * 2 - 1) * 2 = 2 + (A_val - 1) * 4 := by omega
    dsimp [evalWords]
    rwa [heq]
  | @one A_val H u hDu ih =>
    cases A_val with
    | zero =>
      change NumRun stepRel 0 default (d1 +> evalWords u default)
      rw [evalWords_eq_default_of_zero hDu rfl]
      intro w hs hN
      generalize hk : 0 = k0 at hN
      cases hN with
      | zero =>
        have hd : d1 +> (default : HalfTape) = one +> default := by simp [d1, one]
        rw [hd]; exact Side.nil (one +> default)
      | odd _ => omega
      | even _ => omega
    | succ A_val =>
      have hA_pos : 0 < A_val + 1 := by omega
      have hIH := ih hA_pos
      have heq_in : (A_val + 1 - 1) * 2 = A_val * 2 := by omega
      rw [heq_in] at hIH
      have hs := numRun_d0_d1 hb hIH
      rw [d0_append_default] at hs
      have heq : (1 + (A_val + 1) * 2 - 1) * 2 = 4 + A_val * 4 := by omega
      dsimp [evalWords]
      rwa [heq]

theorem seg_of_wordEffect (hb : BaseRules stepRel) {n : Nat} {u : WordList}
    {b : Nat} {v : WordList} (hI : WordEffect n u b v) :
    ∀ {A_val H : Nat}, DigitVal A_val H v →
      Seg stepRel ([Call.ch] ^ n) ([Call.ch] ^ b) (wordsToBits u) (wordsToBits v) := by
  induction hI with
  | nil n =>
    intro A_val H _
    exact Seg_refl ([Call.ch] ^ n)
  | T _ _ =>
    intro A_val H hD
    exact False.elim (digitVal_not_cons_V hD)
  | d00 _ ih =>
    intro A_val H hD
    rcases digitVal_cons_K_inv hD with ⟨A', H', hD', _, _⟩
    exact Seg_seq (seg_ch_even_d0 hb _) (ih hD')
  | d01 _ ih =>
    intro A_val H hD
    rcases digitVal_cons_Q_inv hD with ⟨A', H', hD', _, _⟩
    exact Seg_seq (seg_ch_odd_d0 hb _) (ih hD')
  | d10 _ ih =>
    intro A_val H hD
    rcases digitVal_cons_Q_inv hD with ⟨A', H', hD', _, _⟩
    exact Seg_seq (seg_ch_even_d1 hb _) (ih hD')
  | d11 _ ih =>
    intro A_val H hD
    rcases digitVal_cons_K_inv hD with ⟨A', H', hD', _, _⟩
    exact Seg_seq (seg_ch_odd_d1 hb _) (ih hD')

theorem num_seg_t (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (3 + n) [] hs) (hJ : Num (2 + n * 2) [] hs') :
    Seg stepRel hs ([Call.ch] ++ hs') t t := by
  generalize hk1 : 3 + n = k1 at hI
  generalize hk2 : 2 + n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = m * 2 := by omega
        subst hq; rw [h1m]; exact seg_cp_ch_t hb m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = 1 + m * 2 := by omega
        subst hq; rw [h1m]; exact seg_cj_ch_t hb m

theorem num_seg_d10 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg stepRel hs hs' (d1 ++ d0) t := by
  generalize hk1 : 1 + n = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases m with
      | zero => omega
      | succ m =>
        have h1m : m + 1 = 1 + m := by omega
        have hq : q = 1 + m * 2 := by omega
        subst hq; rw [h1m]; exact seg_cp_ch_d10 hb m
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      have hq : q = m * 2 := by omega
      subst hq; exact seg_cj_ch_d10 hb m

theorem num_seg_d11 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (1 + n) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg stepRel hs hs' (d1 ++ d1) t := by
  generalize hk1 : 1 + n = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | @odd m =>
    cases hJ with
    | @odd q =>
      have hq : q = m * 2 := by omega
      subst hq; exact seg_cp_ch_d11 hb m
    | even _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hq : q = 1 + m * 2 := by omega
      subst hq; exact seg_cj_ch_d11 hb m
    | even _ => omega

theorem num_seg_short00 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg stepRel hs hs' d0 d0 := by
  generalize hk1 : 2 + n * 4 = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m = 2 + q * 2 := by omega
        subst hm; exact seg_cj_ch_even_d0 hb q

theorem num_seg_short01 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (2 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg stepRel hs hs' d1 d0 := by
  generalize hk1 : 2 + n * 4 = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m = q * 2 := by omega
      subst hm; exact seg_cj_ch_even_d10 hb q
    | even _ => omega

theorem num_seg_short10 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (n * 2) [] hs') :
    Seg stepRel hs hs' d0 d1 := by
  generalize hk1 : 4 + n * 4 = k1 at hI
  generalize hk2 : n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | odd _ => omega
    | @even q =>
      cases n with
      | zero => omega
      | succ n =>
        have hm : m = 3 + q * 2 := by omega
        subst hm; exact seg_cj_ch_odd_d01 hb q

theorem num_seg_short11 (hb : BaseRules stepRel) {n : Nat} {hs hs' : List Call}
    (hI : Num (4 + n * 4) [] hs) (hJ : Num (1 + n * 2) [] hs') :
    Seg stepRel hs hs' d1 d1 := by
  generalize hk1 : 4 + n * 4 = k1 at hI
  generalize hk2 : 1 + n * 2 = k2 at hJ
  cases hI with
  | odd _ => omega
  | @even m =>
    cases hJ with
    | @odd q =>
      have hm : m = 1 + q * 2 := by omega
      subst hm; exact seg_cj_ch_odd_d11 hb q
    | even _ => omega

theorem seg_of_phaseScan (hb : BaseRules stepRel)
    {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) :
    ∀ {u : WordList} {n n' : Nat} {hs hs' : List Call},
      WordEffect n u n' v → Num k [] hs → Num k' [] hs' →
      Seg stepRel (([Call.ch] ^ n) ++ hs) (([Call.ch] ^ n') ++ hs')
        (wordsToBits u) (wordsToBits w) := by
  induction hI with
  | nil k =>
    intro u n n' hs hs' hE hN hN'
    cases hE
    rw [num_unique hN hN']
    exact Seg_refl (([Call.ch] ^ n) ++ hs')
  | @T m _ _ _ _ _ _ ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    cases hE with
    | T hSub =>
      rcases exists_num (by omega : 0 < 2 + m * 2) with ⟨hs0, hN0⟩
      have hIH := ih hSub hN0 hN'
      have hStep := Seg_par (seg_ch_pow_t hb n0) (num_seg_t hb hN hN0)
      have heq : ([Call.ch] ^ (n0 * 2)) ++ ([Call.ch] ++ hs0) =
          ([Call.ch] ^ (1 + n0 * 2)) ++ hs0 := by
        have h1 : 1 + n0 * 2 = n0 * 2 + 1 := by omega
        rw [h1, pow_add_list, pow_one_list, List.append_assoc]
      rw [heq] at hStep
      exact Seg_seq hStep hIH
  | @pair0 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q, K] ++ u) at hE
    rcases wordEffect_split_output [Q, K] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases exists_num hPos with ⟨hs0, hN0⟩
    have hD10 : DigitVal 1 2 [Q, K] := DigitVal.one (DigitVal.zero DigitVal.nil)
    have hStep := Seg_par (seg_of_wordEffect hb hL hD10) (num_seg_d10 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')
  | @pair1 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q, Q] ++ u) at hE
    rcases wordEffect_split_output [Q, Q] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    rcases exists_num (by omega : 0 < 1 + m * 2) with ⟨hs0, hN0⟩
    have hD11 : DigitVal 3 2 [Q, Q] := DigitVal.one (DigitVal.one DigitVal.nil)
    have hStep := Seg_par (seg_of_wordEffect hb hL hD11) (num_seg_d11 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')
  | @short00 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases exists_num hPos with ⟨hs0, hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := Seg_par (seg_of_wordEffect hb hL hD0) (num_seg_short00 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')
  | @short01 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    rcases exists_num (by omega : 0 < 1 + m * 2) with ⟨hs0, hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := Seg_par (seg_of_wordEffect hb hL hD1) (num_seg_short01 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')
  | @short10 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([K] ++ u) at hE
    rcases wordEffect_split_output [K] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    have hPos : 0 < m * 2 := phaseScan_pos_of_out_pos hSub (by cases hN' <;> omega)
    rcases exists_num hPos with ⟨hs0, hN0⟩
    have hD0 : DigitVal 0 1 [K] := DigitVal.zero DigitVal.nil
    have hStep := Seg_par (seg_of_wordEffect hb hL hD0) (num_seg_short10 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')
  | @short11 m u _ _ _ _ hSub ih =>
    intro u0 n0 n1 hs hs' hE hN hN'
    change WordEffect n0 u0 n1 ([Q] ++ u) at hE
    rcases wordEffect_split_output [Q] hE with ⟨u1, u2, q, rfl, hL, hR⟩
    rcases exists_num (by omega : 0 < 1 + m * 2) with ⟨hs0, hN0⟩
    have hD1 : DigitVal 1 1 [Q] := DigitVal.one DigitVal.nil
    have hStep := Seg_par (seg_of_wordEffect hb hL hD1) (num_seg_short11 hb hN hN0)
    rw [wordsToBits_append]
    exact Seg_seq hStep (ih hR hN0 hN')

theorem numRun_d10_t (hb : BaseRules stepRel) {n : Nat} {r r' : HalfTape}
    (hI : NumRun stepRel (n * 2) r r') :
    NumRun stepRel (1 + n) (d1 +> (d0 +> r)) (t +> r') := by
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
      have hr' := numRun_zero hI
      subst hr'
      rw [← append_assoc t one r]
      exact Seg_apply hb.seg_cp_d10 (Side.nil r)
    | succ m =>
      have h1m : m + 1 = 1 + m := by omega
      rw [h1m]
      refine Seg_apply (seg_cp_ch_d10 hb m) ?_
      have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (1 + m * 2)) := by
        have hm : n * 2 = 2 + (1 + m * 2) * 2 := by omega
        rw [hm]; exact Num.even (1 + m * 2)
      simpa using hI [] _ hN2
  | @even m =>
    simp only [append_nil, ← append_assoc d1 d0 r]
    refine Seg_apply (seg_cj_ch_d10 hb m) ?_
    have hN2 : Num (n * 2) [] ([.cj] ++ [.ch] ^ (m * 2)) := by
      have hm : n * 2 = 2 + (m * 2) * 2 := by omega
      rw [hm]; exact Num.even (m * 2)
    simpa using hI [] _ hN2

theorem numRun_of_phaseScan (hb : BaseRules stepRel)
    {k : Nat} {v : WordList} {k' : Nat} {w : WordList} {a b : Rat}
    (hI : PhaseScan k v k' w a b) {u : WordList} {r' : HalfTape}
    (hE : WordEffect 0 u 1 v) (hK : 0 < k') (hC : NumRun stepRel k' (d1 +> default) r') :
    NumRun stepRel k (evalWords u default) (evalWords w r') := by
  intro w0 hs hN
  have hPosK : 0 < k := phaseScan_pos_of_out_pos hI hK
  have hw0 : w0 = [] := by cases hN <;> first | rfl | omega
  subst hw0
  rcases exists_num hK with ⟨hs', hN'⟩
  have hSeg := seg_of_phaseScan hb hI hE hN hN'
  dsimp at hSeg
  have hSide := Seg_apply hSeg (Side_append hb.side_ch_blank (hC [] hs' hN'))
  rwa [wordsToBits_append_tape, wordsToBits_append_tape] at hSide

theorem numRun_of_step (hb : BaseRules stepRel) {orig out : WordList} (hS : Step orig out) :
    ∃ r, NumRun stepRel 12 (evalWords orig default) r ∧ evalWords out default = t +> r := by
  cases hS with
  | intro eff k v a b J A_val da hE hI hDA hSum =>
    have hposJ := pow_two_pos J
    have hPosK : 0 < k := by omega
    have hDFull : DigitVal k (J + 1) (da ++ [Q]) := by
      have h := digitVal_append hDA (DigitVal.one DigitVal.nil)
      have heq : A_val + 1 * 2 ^ J = k := by omega
      rwa [heq] at h
    have hC0 : NumRun stepRel ((k - 1) * 2) default (evalWords (da ++ [Q]) default) :=
      numRun_of_digitVal hb hDFull hPosK
    have hC1 : NumRun stepRel k (d1 +> default) (evalWords (V :: (da ++ [Q])) default) := by
      have h := numRun_d10_t hb hC0
      have hk : 1 + (k - 1) = k := by omega
      rwa [hk, d0_append_default] at h
    have hRun := numRun_of_phaseScan hb hI hE hPosK hC1
    rw [← evalWords_append] at hRun
    exact ⟨evalWords (v ++ V :: (da ++ [Q])) default, hRun, rfl⟩

theorem cycle_ca_ch {tm : Machine (Fin 2) (Fin 6)}
    {cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (hb : BaseRules (CallStep tm cfgR cfgL))
    (hP : Seg (CallStep tm cfgR cfgL) [.ca] [.ch, .ch] t [1, 1, 0, 0, 0, 1, 1, 0, 0])
    (hQ : Seg (CallStep tm cfgR cfgL) [.ch] [.ch] [1, 1, 0, 0, 0, 1, 1, 0, 0] (t ++ t ++ one))
    (hS : ∀ r, (cfgL lh r) [tm]⊢⁺ (cfgR ([1] +> default) .ca r))
    (hT : ∀ r, (cfgL ([1] +> default) r) [tm]⊢⁺ (cfgR lh .ch r))
    {r r' : HalfTape} (hI : NumRun (CallStep tm cfgR cfgL) 12 r r') :
    (cfgL lh (w_pre +> r)) [tm]⊢⁺ (cfgL lh (w_pre +> (t +> r'))) := by
  have h1 : Seg (CallStep tm cfgR cfgL) [.ca, .ch] [.ch, .ch, .ch] t (t ++ t ++ one) :=
    Seg_par hP hQ
  have h2 : Seg (CallStep tm cfgR cfgL) [.ch, .ch, .ch] ([.cj] ++ [.ch] ^ 5) (t ++ one) t :=
    Seg_par hb.seg_ch_t1 (seg_ch_pow_t hb 2)
  have hR : Seg (CallStep tm cfgR cfgL) [.ca, .ch] ([.cj] ++ [.ch] ^ 5) w_pre (w_pre ++ t) := by
    simpa only [w_pre, List.append_assoc, List.cons_append, List.nil_append] using Seg_seq h1 h2
  have h_num : Num 12 [] ([.cj] ++ [.ch] ^ 5) := Num.even 5
  have hC := hI [] ([.cj] ++ [.ch] ^ 5) h_num
  have hSide := Seg_apply hR hC
  rcases hSide with _ | ⟨hca, hrest⟩
  rcases hrest with _ | ⟨hch, hnil⟩
  cases hnil
  have hs1 := plus_trans (hS (w_pre +> r)) (hca ([1] +> default))
  have hs2 := plus_trans (hT _) (hch lh)
  have hs3 := plus_trans hs1 hs2
  rwa [append_assoc] at hs3

theorem cycle_ch_ca {tm : Machine (Fin 2) (Fin 6)}
    {cfgR : HalfTape → Call → HalfTape → Cfg (Fin 2) (Fin 6)}
    {cfgL : HalfTape → HalfTape → Cfg (Fin 2) (Fin 6)}
    (hb : BaseRules (CallStep tm cfgR cfgL))
    (hP : Seg (CallStep tm cfgR cfgL) [.ca] [.ch] t (t ++ t ++ one))
    (hR_step : ∀ r, (cfgL lh r) [tm]⊢⁺ (cfgR ([1, 1, 0, 1, 0, 1] +> default) .ch r))
    (hS_step : ∀ r, (cfgL ([1, 1, 0, 1, 0, 1] +> default) r) [tm]⊢⁺ (cfgR lh .ca r))
    {r r' : HalfTape} (hI : NumRun (CallStep tm cfgR cfgL) 12 r r') :
    (cfgL lh (w_pre +> r)) [tm]⊢⁺ (cfgL lh (w_pre +> (t +> r'))) := by
  have h1 : Seg (CallStep tm cfgR cfgL) [.ch, .ca] [.ch, .ch, .ch] t (t ++ t ++ one) :=
    Seg_par hb.seg_ch_t hP
  have h2 : Seg (CallStep tm cfgR cfgL) [.ch, .ch, .ch] ([.cj] ++ [.ch] ^ 5) (t ++ one) t :=
    Seg_par hb.seg_ch_t1 (seg_ch_pow_t hb 2)
  have hQ : Seg (CallStep tm cfgR cfgL) [.ch, .ca] ([.cj] ++ [.ch] ^ 5) w_pre (w_pre ++ t) := by
    simpa only [w_pre, List.append_assoc, List.cons_append, List.nil_append] using Seg_seq h1 h2
  have h_num : Num 12 [] ([.cj] ++ [.ch] ^ 5) := Num.even 5
  have hC := hI [] ([.cj] ++ [.ch] ^ 5) h_num
  have hSide := Seg_apply hQ hC
  rcases hSide with _ | ⟨hch, hrest⟩
  rcases hrest with _ | ⟨hca, hnil⟩
  cases hnil
  have hs1 := plus_trans (hR_step (w_pre +> r)) (hch ([1, 1, 0, 1, 0, 1] +> default))
  have hs2 := plus_trans (hS_step _) (hca lh)
  have hs3 := plus_trans hs1 hs2
  rwa [append_assoc] at hs3

theorem step_sim {tm : Machine (Fin 2) (Fin 6)}
    {cfgAt : HalfTape → Cfg (Fin 2) (Fin 6)}
    (hb : BaseRules stepRel)
    (h_cycle : ∀ {r r' : HalfTape}, NumRun stepRel 12 r r' → (cfgAt r) [tm]⊢⁺ (cfgAt (t +> r')))
    {orig out : WordList} (hS : Step orig out) :
    (cfgAt (evalWords orig default)) [tm]⊢⁺ (cfgAt (evalWords out default)) := by
  rcases numRun_of_step hb hS with ⟨r, hC, hEq⟩
  rw [hEq]
  exact h_cycle hC

theorem rounds_sim {tm : Machine (Fin 2) (Fin 6)}
    {cfgAt : HalfTape → Cfg (Fin 2) (Fin 6)}
    (hb : BaseRules stepRel)
    (h_cycle : ∀ {r r' : HalfTape}, NumRun stepRel 12 r r' → (cfgAt r) [tm]⊢⁺ (cfgAt (t +> r')))
    {u v : WordList} (hR : Rounds u v) :
    (cfgAt (evalWords u default)) [tm]⊢* (cfgAt (evalWords v default)) := by
  induction hR with
  | refl u => exact ⟨0, rfl⟩
  | next hS _ ih =>
    rcases step_sim hb h_cycle hS with ⟨n1, _, hn1⟩
    rcases ih with ⟨n2, hn2⟩
    exact ⟨n1 + n2, multiStep_trans tm _ _ _ n1 n2 hn1 hn2⟩

theorem is_not_halt_of_aggState {tm : Machine (Fin 2) (Fin 6)}
    {cfgAt : HalfTape → Cfg (Fin 2) (Fin 6)}
    (hb : BaseRules stepRel)
    (h_cycle : ∀ {r r' : HalfTape}, NumRun stepRel 12 r r' → (cfgAt r) [tm]⊢⁺ (cfgAt (t +> r')))
    {c_init : Cfg (Fin 2) (Fin 6)} {u0 pref pref_next : WordList} {p0 q0 : Nat}
    (h_safe : isSafePrefix pref_next = true)
    (h_copy : ∀ q, 5 ≤ q →
      CopyTwelve (List.replicate q V ++ pref) (List.replicate q V ++ pref_next))
    (h_stem : c_init [tm]⊢* cfgAt (evalWords u0 default))
    (h_entry : ∃ v, Rounds u0 v ∧ AggState pref p0 q0 v) :
    ∀ (cfg : Cfg (Fin 2) (Fin 6)), (c_init [tm]⊢* cfg) → (step tm cfg).isSome := by
  refine Counter.does_not_halt_of_invariant
    (fun c => ∃ p q w, c = cfgAt (evalWords w default) ∧ AggState pref p q w) ?_ ?_
  · rcases h_entry with ⟨v0, hRounds, hGood0⟩
    exact ⟨cfgAt (evalWords v0 default),
      Counter.stepStar_trans h_stem (rounds_sim hb h_cycle hRounds),
      p0, q0, v0, rfl, hGood0⟩
  · rintro _ ⟨p, q, w, rfl, h_good⟩
    rcases aggState_step_of_copyTwelve pref pref_next h_safe h_copy p q w h_good
      with ⟨w', hStep, h_good'⟩
    exact ⟨cfgAt (evalWords w' default), step_sim hb h_cycle hStep, 1 + p, 1 + q, w', rfl, h_good'⟩

def pref_A : WordList :=
  [Q,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V]
def pref_next_A : WordList :=
  [K,V,K,V,V,V,V,V,V,K,V,V,V,K,V]
theorem copy_base_A (n : Nat) :
    Copy (31 + 32 * n) (260 + 256 * n) pref_A pref_next_A (4617 + 4096 * n)
      (30684 + 32768 * n) := by
  unfold pref_A pref_next_A
  refine copy_step_d11 (n' := 16 + 16 * n) (k' := 128 + 128 * n) (m := 64 + 64 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 33 + 32 * n) (k' := 252 + 256 * n) (m := 125 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 17 + 16 * n) (k' := 124 + 128 * n) (m := 62 + 64 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 35 + 32 * n) (k' := 244 + 256 * n) (m := 121 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 71 + 64 * n) (k' := 484 + 512 * n) (m := 241 + 256 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 143 + 128 * n) (k' := 964 + 1024 * n) (m := 481 + 512 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 287 + 256 * n) (k' := 1924 + 2048 * n) (m := 961 + 1024 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 575 + 512 * n) (k' := 3844 + 4096 * n) (m := 1921 + 2048 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 1151 + 1024 * n) (k' := 7684 + 8192 * n) (m := 3841 + 4096 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 576 + 512 * n) (k' := 3840 + 4096 * n) (m := 1920 + 2048 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 1153 + 1024 * n) (k' := 7676 + 8192 * n) (m := 3837 + 4096 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 2307 + 2048 * n) (k' := 15348 + 16384 * n) (m := 7673 + 8192 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4615 + 4096 * n) (k' := 30692 + 32768 * n) (m := 15345 + 16384 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 2308 + 2048 * n) (k' := 15344 + 16384 * n) (m := 7672 + 8192 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4617 + 4096 * n) (k' := 30684 + 32768 * n) (m := 15341 + 16384 * n)
    (by omega) (by omega) (by omega) ?_
  exact Copy.nil _ _
theorem copyTwelve_A (q : Nat) (hQ : 5 <= q) :
    CopyTwelve (List.replicate q V ++ pref_A) (List.replicate q V ++ pref_next_A) := by
  have hPow : 2 ^ q = 32 * 2 ^ (q - 5) := by
    have heq : q = 5 + (q - 5) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPos := pow_two_pos (q - 5)
  have hTs := copy_replicate_V q 0 8
  have hBase := copy_base_A (2 ^ (q - 5) - 1)
  have h1 : (1 + 0) * 2 ^ q - 1 = 31 + 32 * (2 ^ (q - 5) - 1) := by omega
  have h2 : 4 + 8 * 2 ^ q = 260 + 256 * (2 ^ (q - 5) - 1) := by omega
  rw [h1,h2] at hTs
  exact ⟨_,_,copy_append hTs hBase⟩
theorem safe_pref_A : isSafePrefix pref_next_A = true := by decide +kernel
def tail_A : WordList :=
  [K,Q,K,Q,Q,Q,Q,Q,K] ++ List.replicate 15 Q
def u0_A : WordList :=
  [V,V,Q,V,Q,V,K,K,V,Q,K]
def u5_A : WordList := [
    V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, V, Q, V,
    Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, K, K, Q, Q, Q, K, Q, Q, Q, Q, K,
    Q, K, K, Q, Q, K, Q, Q, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q
  ]
def u10_A : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V, V, V, Q, V, V,
    V, V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, Q, V,
    V, V, Q, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, Q, V, V, V, Q, V,
    Q, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, Q, V, V, V, V, V, V, V, Q, V, V, V, V,
    V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, K, V, Q, Q, V, V, Q, V, K,
    V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V, Q, V, K, V,
    V, Q, V, V, V, V, Q, K, V, V, V, V, V, Q, V, Q, V, K, V, V, Q, K, Q, V, V, V, V, V,
    V, K, V, V, V, V, V, Q, V, V, V, V, V, K, K, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, K,
    K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, K, Q, K, Q, K, K, K, Q, K,
    Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q,
    Q, K, K, Q, K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, Q, K,
    Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
def u12_p1_A : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V, V, V, Q,
    V, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V,
    Q, V, V, V, Q, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, Q, V, V, V,
    Q, V, Q, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, Q, V, V, V, V, V, V, V, Q, V, V,
    V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V, Q, V,
    Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V, Q, V, Q,
    V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, Q, V, Q, V, V, Q, Q, K, V, V, V, V,
    V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, V, Q, V, Q, V, Q,
    V, V, K, K, Q, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q,
    V, Q, V, Q, V, V, Q, K, K, V, V, V, V, V, V, Q, V, V, V, V, V, V, V
  ]
def u12_p2_A : WordList := [
    V, V, V, V, V, V, V, Q, V, Q, V, K, V, V, Q, V, Q, V, Q, K, V, V, K, V, V, V, K, V,
    V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, K,
    V, Q, V, K, V, V, Q, K, Q, V, V, V, V, V, V, K, V, V, V, V, V, Q, V, V, V, V, V, V,
    K, K, K, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, Q, K, Q, K, Q, Q,
    Q, K, K, K, Q, K, Q, K, K, K, K, K, K, K, K, K, K, K, K, K, Q, K, Q, Q, Q, K, K, Q,
    Q, K, K, Q, Q, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, K, Q,
    K, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, K, Q, K, Q,
    K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K,
    Q, Q, K, K, Q, K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, Q,
    K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
def u14_p1_A : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V, V,
    V, Q, V, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V,
    Q, V, Q, V, V, V, Q, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, Q, V,
    V, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, Q, V, V, V, V, V, V, V, Q,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V,
    Q, V, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V, Q,
    V, Q, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, Q, V, Q, V, V, Q, V, V, V, V,
    V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, V, Q, V, Q, V,
    Q, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q,
    V, K, V, K, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V,
    V, Q, V, Q, V, Q, V, V, Q, V, Q, V, Q, Q, V, V, Q, V, V, V, Q, V, V, V, V, V, V, V,
    V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, K, V, Q, V, V,
    Q, Q, K, V, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V,
    Q, V, V, Q, V, Q, V, Q, K, V, V, V, Q, Q, V, V, V, V, V, V, Q, V, K, V, V, V, Q, V,
    Q, V, V, Q, V, K, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, V,
    V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, Q, V, Q, V, V, Q, K, K,
    V, V
  ]
def u14_p2_A : WordList := [
    V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, K, V, V,
    Q, V, Q, V, Q, K, K, V, V, V, V, Q, Q, V, V, K, K, V, Q, V, Q, V, V, Q, V, K, V, V,
    V, V, V, V, V, V, V, V, K, V, V, V, V, V, V, V, Q, V, K, V, V, V, V, K, K, V, K, Q,
    V, V, V, V, V, V, Q, V, Q, V, K, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V,
    V, V, Q, V, V, V, Q, V, V, V, V, Q, K, V, Q, V, K, V, V, Q, K, Q, V, V, V, V, V, V,
    K, V, V, V, V, V, Q, V, V, V, V, V, V, V, K, K, K, K, K, K, K, Q, K, K, Q, K, Q, Q,
    Q, Q, K, Q, K, Q, K, Q, K, K, K, K, Q, Q, Q, K, Q, Q, Q, K, K, K, Q, Q, K, K, K, Q,
    Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, K, Q, Q, K, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q,
    K, K, Q, Q, Q, K, K, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q,
    K, Q, K, K, Q, Q, K, K, K, Q, Q, K, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q,
    K, K, Q, Q, K, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K, Q, Q,
    Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q,
    Q, K, K, K, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, K, K, K, K, Q, K, Q, K, K,
    Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, Q, Q, Q, Q,
    Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, K, K, Q,
    K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q, Q, K, Q, K, Q, Q,
    Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
def u15_p1_A : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V, V,
    V, Q, V, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V,
    Q, V, Q, V, V, V, Q, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, Q, V,
    V, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, Q, V, V, V, V, V, V, V, Q,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V,
    Q, V, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V, Q,
    V, Q, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, Q, V, Q, V, V, Q, V, V, V, V,
    V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, V, Q, V, Q, V,
    Q, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q,
    V, K, V, K, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V,
    V, Q, V, Q, V, Q, V, V, Q, V, Q, V, Q, Q, V, V, Q, V, V, V, Q, V, V, V, V, V, V, V,
    V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, K, V, K, V, V,
    Q, V, V, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, Q,
    V, V, Q, V, Q, V, Q, Q, V, V, V, Q, Q, V, V, V, V, V, V, Q, V, Q, V, V, V, Q, V, Q,
    V, V, Q, V, Q, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, V, V,
    V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, K, V, Q, V, V, Q, Q, K, V, V
  ]
def u15_p2_A : WordList := [
    V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, Q, V, V,
    Q, V, Q, V, Q, K, Q, V, V, V, V, Q, Q, V, V, V, V, K, V, Q, V, V, Q, V, Q, V, V, V,
    V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V,
    V, V, V, Q, V, Q, V, Q, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q,
    V, V, V, Q, V, V, V, V, Q, Q, V, Q, V, Q, V, V, Q, K, K, V, V, V, V, V, V, Q, V, V,
    V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, K, V, V, Q, V, Q, V, Q, K, Q,
    V, V, V, V, Q, Q, Q, K, V, V, K, Q, V, V, V, V, V, V, K, V, K, Q, K, Q, Q, Q, K, K,
    K, Q, Q, V, V, V, Q, V, K, Q, V, V, V, V, V, V, V, V, Q, V, K, V, K, V, Q, V, K, V,
    Q, V, V, V, V, V, V, V, Q, V, K, V, V, Q, V, V, V, V, V, V, V, K, Q, V, V, V, V, V,
    Q, V, V, Q, V, V, Q, V, V, V, V, V, Q, Q, Q, Q, V, V, V, V, V, V, V, Q, K, V, K, V,
    K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q,
    K, V, Q, V, K, V, V, Q, K, Q, V, V, V, V, V, V, K, V, V, V, V, V, V, V, V, V, V, V, V
  ]
def u15_p3_A : WordList := [
    K, K, K, K, K, K, K, Q, Q, Q, K, K, Q, K, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, K, K, K,
    Q, Q, Q, K, Q, Q, Q, K, K, Q, Q, Q, K, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q,
    Q, Q, K, Q, Q, Q, K, K, Q, Q, Q, Q, K, K, K, Q, Q, K, Q, K, K, Q, Q, Q, K, K, Q, Q,
    K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, K, Q, Q, K, Q, Q, K, K, K, Q,
    K, K, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, K, K, K, K, K, Q, Q, K, K, Q, K, Q, Q, Q,
    Q, Q, Q, Q, Q, Q, K, Q, Q, K, K, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q,
    K, Q, K, Q, K, K, Q, Q, Q, K, Q, K, Q, K, Q, Q, K, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q,
    Q, K, Q, Q, Q, K, K, K, Q, K, K, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K,
    K, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, K, K, Q, K, K, Q, K, Q,
    Q, Q, Q, Q, K, Q, Q, Q, K, K, K, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, K, K,
    K, K, Q, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, K, Q,
    K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q,
    K, K, Q, Q, K, K, Q, K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K,
    Q, Q, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
def u16_p1_A : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, Q, V,
    V, V, Q, V, V, V, V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q,
    V, Q, V, Q, V, V, V, Q, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, Q,
    V, V, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V, V, Q, V, Q, Q, V, V, V, V, V, V, V,
    Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, Q, V, V, V,
    V, Q, V, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V,
    Q, V, Q, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, Q, V, Q, V, V, Q, V, V, V,
    V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, V, Q, V, Q,
    V, Q, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q,
    Q, V, K, V, K, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V,
    V, V, Q, V, Q, V, Q, V, V, Q, V, Q, V, Q, Q, V, V, Q, V, V, V, Q, V, V, V, V, V, V,
    V, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, K, V, K, V,
    V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, V,
    Q, V, V, Q, V, Q, V, Q, Q, V, V, V, Q, Q, V, V, V, V, V, V, Q, V, Q, V, V, V, Q, V,
    Q, V, V, Q, V, Q, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, V,
    V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, K, V, K, V, V, Q, V, V, V
  ]
def u16_p2_A : WordList := [
    V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, Q, V, V,
    Q, V, Q, V, Q, Q, K, V, V, V, V, Q, Q, V, V, V, V, Q, V, K, V, V, Q, V, Q, V, V, V,
    V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V,
    V, V, V, Q, V, Q, V, Q, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q,
    V, V, V, Q, V, V, V, V, Q, Q, V, K, V, Q, V, V, Q, Q, K, V, V, V, V, V, V, Q, V, V,
    V, V, V, Q, V, V, V, V, V, V, V, Q, V, V, V, V, Q, V, Q, V, V, Q, V, Q, V, Q, K, Q,
    V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, V, V, Q, V, V, K, V, V, Q, Q, Q, K, V, V,
    V, Q, V, V, V, V, V, V, V, V, V, V, Q, V, Q, V, K, V, K, V, Q, V, K, V, V, V, V, V,
    V, V, Q, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, V, V, Q,
    V, V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, Q, Q, V, Q, V, K, V, V, V, V, V, V, V,
    V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, Q, V, Q, V, V, Q,
    K, K, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V
  ]
def u16_p3_A : WordList := [
    V, V, V, V, Q, V, Q, V, K, V, V, Q, V, Q, V, Q, K, K, V, V, V, V, Q, Q, Q, K, V, V,
    V, V, V, Q, V, V, V, K, V, V, Q, Q, V, V, V, Q, V, Q, V, Q, V, V, Q, V, K, Q, V, V,
    V, V, V, V, V, Q, K, V, V, Q, V, Q, K, V, K, V, V, Q, V, V, V, V, Q, K, V, K, Q, Q,
    V, V, V, V, V, V, V, V, Q, V, K, K, V, V, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, Q,
    Q, V, K, V, V, V, V, V, Q, V, V, Q, V, V, Q, V, V, Q, V, V, V, V, V, V, V, Q, Q, V,
    V, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, Q, Q, Q, Q, V, V, V, V, V, V, V, Q, K,
    V, K, V, K, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V,
    V, V, Q, K, V, Q, V, K, V, V, Q, K, Q, V, V, V, V, V, V, K, V, V, V, V, V, Q, V, V,
    V, V, V, V, V
  ]
def u16_p4_A : WordList := [
    K, K, K, K, K, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, K, K, K, Q,
    Q, Q, K, Q, Q, Q, K, K, Q, Q, Q, K, K, K, Q, K, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q,
    Q, Q, Q, K, K, Q, Q, K, K, K, Q, Q, Q, Q, Q, K, Q, Q, K, K, K, K, Q, K, Q, Q, K, Q,
    Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, Q, Q, K, K, Q,
    Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, Q, K, Q, K, K, K, Q, Q, Q, K,
    K, K, Q, Q, K, K, K, K, K, K, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q, K, Q, Q, K, Q, K,
    K, Q, Q, Q, K, Q, K, K, K, K, K, K, K, Q, K, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q,
    K, K, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q,
    Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, K, Q, K, K, Q,
    K, Q
  ]
def u16_p5_A : WordList := [
    Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q,
    Q, Q, Q, Q, Q, K, Q, K, Q, K, Q, K, Q, K, K, Q, K, Q, K, K, K, Q, Q, K, Q, Q, Q, Q,
    Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, K, K, Q, K, K, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q,
    Q, Q, Q, Q, K, K, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, K, K, Q,
    K, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K, K, K, K, Q, Q, Q, K, Q, Q, Q, K, Q, Q,
    Q, Q, Q, K, K, K, K, Q, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q,
    Q, K, Q, K, Q, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K, Q, Q, Q,
    Q, Q, Q, Q, Q, K, K, Q, Q, K, K, Q, K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q,
    Q, Q, K, Q, K, Q, Q, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q,
    Q, Q
  ]
theorem entrySpec_A : EntrySpec 18 pref_A tail_A 11000 :=
  entrySpec_of_checkEntrySpec (by decide +kernel)
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_0_5_A : evalRounds 5 u0_A = some u5_A := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_5_10_A : evalRounds 5 u5_A = some u10_A := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_10_12_A : evalRounds 2 u10_A = some (u12_p1_A ++ u12_p2_A) := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_12_14_A :
    evalRounds 2 (u12_p1_A ++ u12_p2_A) = some (u14_p1_A ++ u14_p2_A) := by
  decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem step_14_15_A :
    checkStepTwoPieces u14_p1_A u14_p2_A
      110434817290149211768284085870454066060546939462225549259006050933145647
      7067168235385531200914694256602959202955917586119058258266247915060068152
      (12608249447398561729463940017754846819701602849629166142431 * 10^59 +
        43022817523291247800206387780525642753349635545663353377664)
      u15_p1_A u15_p2_A u15_p3_A = true := by
  decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem step_15_16_A :
    checkStepThreePieces (V :: u15_p1_A) (u15_p2_A ++ [V]) (u15_p3_A ++ [Q])
      1766902070710385858937921437335091786398117464135613873040684957281812527
      (63045172591469524831973228231685135810857921777046899566448 * 10^58 +
        3969260760571151030486379468182403867732674229876057702399)
      113076451955992548153983074076597066130126825388972272726165497219966302796
      (676910774998025375822660775135045812617818152164822448708937095 * 10^63 +
        293664528614370053480259847094293709720004454266978684988792836)
      (16759499027875054834400200871060218370496769749035807992084659312172062036053 * 10^77 +
        25682553129796896712940054963540497648261454412042999479128922952102697101568)
      u16_p1_A u16_p2_A u16_p3_A u16_p4_A u16_p5_A = true := by
  decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem check_entry_A :
    checkEntryThreePieces 18 pref_A tail_A 11000
      (V :: u16_p1_A) u16_p2_A (u16_p3_A ++ [V]) u16_p4_A u16_p5_A
      244 416 508
      28269993083910161508169751504624082417804810888089862649298329268595458391
      (169232962271100938707715443929017058497083679336597570160963934 * 10^63 +
        441725064445424265138458712223603740228005634717572939333509119)
      (83800103984907189572674308122271855628514314969710333018531300610894322517282 * 10^76 +
        3266912222700929127475495397164689088385716467769609144035444689331281199359)
      28948472917924005384365825540735060395832126349404019352881489171041749393536
      47079 4103 = true := by
  decide +kernel
theorem entry_A : ∃ v,Rounds u0_A v /\ AggState pref_A 16 18 v := by
  have h0_5 := evalRounds_sound 5 u0_A u5_A rounds_0_5_A
  have h5_10 := evalRounds_sound 5 u5_A u10_A rounds_5_10_A
  have h10_12 := evalRounds_sound 2 u10_A (u12_p1_A ++ u12_p2_A) rounds_10_12_A
  have h12_14 := evalRounds_sound 2 (u12_p1_A ++ u12_p2_A) (u14_p1_A ++ u14_p2_A) rounds_12_14_A
  have h14_15 := step_of_checkStepTwoPieces _ _ _ _ _ _ _ _ step_14_15_A
  have h15_16 := step_of_checkStepThreePieces _ _ _ _ _ _ _ _ _ _ _ _ _ step_15_16_A
  have hEq15 : V :: ((u15_p1_A ++ u15_p2_A) ++ V :: (u15_p3_A ++ [Q])) =
      (V :: u15_p1_A) ++ (u15_p2_A ++ [V]) ++ (u15_p3_A ++ [Q]) := by
    simp [List.append_assoc]
  rw [hEq15] at h14_15
  have hEq16 : V :: ((u16_p1_A ++ u16_p2_A ++ u16_p3_A) ++ V :: ((u16_p4_A ++ u16_p5_A) ++ [Q])) =
      ((V :: u16_p1_A) ++ u16_p2_A ++ (u16_p3_A ++ [V])) ++ (u16_p4_A ++ u16_p5_A) ++ [Q] := by
    simp [List.append_assoc]
  rw [hEq16] at h15_16
  have hGood := good_of_checkEntryThreePieces _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    entrySpec_A check_entry_A
  refine ⟨_,?_,hGood⟩
  exact rounds_trans h0_5 (rounds_trans h5_10 (rounds_trans h10_12 (rounds_trans h12_14
    (Rounds.next h14_15 (Rounds.next h15_16 (Rounds.refl _))))))

def pref_B : WordList :=
  [Q,V,V,Q,Q,V,K,V,K,V,V,V,Q,V,V,V,V,V,V,Q,V,V,V,Q,V,Q,V,Q,Q,V]
def pref_next_B : WordList :=
  [K,V,V,K,Q,V,Q,V,Q,V,V,V,K,V,V,V,V,V,V,K,V,V,V,K,V,K,V,K,Q,V]
theorem copy_base_B (n : Nat) :
    Copy (31 + 32 * n) (260 + 256 * n) pref_B pref_next_B (9351 + 8192 * n)
      (58338 + 65536 * n) := by
  unfold pref_B pref_next_B
  refine copy_step_d11 (n' := 16 + 16 * n) (k' := 128 + 128 * n) (m := 64 + 64 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 33 + 32 * n) (k' := 252 + 256 * n) (m := 125 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 67 + 64 * n) (k' := 500 + 512 * n) (m := 249 + 256 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 34 + 32 * n) (k' := 248 + 256 * n) (m := 124 + 128 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_d10 (n' := 17 + 16 * n) (k' := 123 + 128 * n) (m := 61 + 64 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 35 + 32 * n) (k' := 242 + 256 * n) (m := 120 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d01 (n' := 17 + 16 * n) (k' := 121 + 128 * n) (m := 60 + 64 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 35 + 32 * n) (k' := 238 + 256 * n) (m := 118 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d01 (n' := 17 + 16 * n) (k' := 119 + 128 * n) (m := 59 + 64 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 35 + 32 * n) (k' := 234 + 256 * n) (m := 116 + 128 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 71 + 64 * n) (k' := 464 + 512 * n) (m := 231 + 256 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 143 + 128 * n) (k' := 924 + 1024 * n) (m := 461 + 512 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 72 + 64 * n) (k' := 460 + 512 * n) (m := 230 + 256 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 145 + 128 * n) (k' := 916 + 1024 * n) (m := 457 + 512 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 291 + 256 * n) (k' := 1828 + 2048 * n) (m := 913 + 1024 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 583 + 512 * n) (k' := 3652 + 4096 * n) (m := 1825 + 2048 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 1167 + 1024 * n) (k' := 7300 + 8192 * n) (m := 3649 + 4096 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 2335 + 2048 * n) (k' := 14596 + 16384 * n) (m := 7297 + 8192 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4671 + 4096 * n) (k' := 29188 + 32768 * n) (m := 14593 + 16384 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 2336 + 2048 * n) (k' := 14592 + 16384 * n) (m := 7296 + 8192 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 4673 + 4096 * n) (k' := 29180 + 32768 * n) (m := 14589 + 16384 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 9347 + 8192 * n) (k' := 58356 + 65536 * n) (m := 29177 + 32768 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 18695 + 16384 * n) (k' := 116708 + 131072 * n) (m := 58353 + 65536 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 9348 + 8192 * n) (k' := 58352 + 65536 * n) (m := 29176 + 32768 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 18697 + 16384 * n) (k' := 116700 + 131072 * n) (m := 58349 + 65536 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 9349 + 8192 * n) (k' := 58348 + 65536 * n) (m := 29174 + 32768 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 18699 + 16384 * n) (k' := 116692 + 131072 * n) (m := 58345 + 65536 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_d11 (n' := 9350 + 8192 * n) (k' := 58344 + 65536 * n) (m := 29172 + 32768 * n)
    (by omega) (by omega) (by omega) (by omega) ?_
  refine copy_step_d10 (n' := 4675 + 4096 * n) (k' := 29171 + 32768 * n) (m := 14585 + 16384 * n)
    (by omega) (by omega) (by omega) ?_
  refine copy_step_T (n' := 9351 + 8192 * n) (k' := 58338 + 65536 * n) (m := 29168 + 32768 * n)
    (by omega) (by omega) (by omega) ?_
  exact Copy.nil _ _
theorem copyTwelve_B (q : Nat) (hQ : 5 <= q) :
    CopyTwelve (List.replicate q V ++ pref_B) (List.replicate q V ++ pref_next_B) := by
  have hPow : 2 ^ q = 32 * 2 ^ (q - 5) := by
    have heq : q = 5 + (q - 5) := by omega
    conv_lhs => rw [heq,Nat.pow_add]
  have hPos := pow_two_pos (q - 5)
  have hTs := copy_replicate_V q 0 8
  have hBase := copy_base_B (2 ^ (q - 5) - 1)
  have h1 : (1 + 0) * 2 ^ q - 1 = 31 + 32 * (2 ^ (q - 5) - 1) := by omega
  have h2 : 4 + 8 * 2 ^ q = 260 + 256 * (2 ^ (q - 5) - 1) := by omega
  rw [h1,h2] at hTs
  exact ⟨_,_,copy_append hTs hBase⟩
theorem safe_pref_B : isSafePrefix pref_next_B = true := by decide +kernel
def tail_B : WordList :=
  [K,Q,Q,Q,K,K,Q,Q,K] ++ List.replicate 15 Q
def u0_B : WordList :=
  List.replicate 4 V ++ [Q,V,V,Q,Q,V,K,V,Q,K,K,Q,Q]
def u5_B : WordList := [
    V, V, V, V, V, V, V, V, V, Q, V, V, Q, Q, V, K, V, K, V, V, V, Q, V, V, V, V, V, V,
    Q, V, V, V, Q, V, Q, V, Q, Q, V, V, V, V, Q, V, V, V, V, V, Q, K, V, Q, V, V, V, K,
    K, K, Q, Q, K, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q
  ]
def u10_B : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, Q, V, K, V, K, V, V, V, Q, V,
    V, V, V, V, V, Q, V, V, V, Q, V, Q, V, Q, Q, V, V, V, V, Q, V, V, V, V, V, Q, Q, V,
    K, V, V, V, V, V, Q, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, V, V, Q, V, V, Q, V, V,
    Q, V, V, V, Q, Q, V, K, V, V, V, V, Q, V, V, V, Q, V, V, V, V, V, V, Q, V, V, Q, V,
    V, V, Q, Q, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q,
    V, V, V, Q, Q, V, K, V, V, V, V, V, V, V, V, Q, V, V, V, K, V, V, K, K, V, Q, K, Q,
    K, V, Q, V, K, V, V, V, K, V, V, V, V, Q, Q, V, V, V, V, V, K, V, V, V, Q, Q, V, V,
    V, V, V, V, V, K, K, K, K, K, Q, Q, Q, K, Q, Q, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, K,
    K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, K, Q, K, K, K, Q, Q, Q, Q,
    K, Q, K, K, K, K, K, K, K, Q, Q, Q, K, Q, K, Q, Q, K, K, K, K, Q, Q, K, K, Q, Q, Q,
    K, Q, Q, Q, Q, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
def u15_B : WordList := [
    V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, Q, Q, V, K, V, K,
    V, V, V, Q, V, V, V, V, V, V, Q, V, V, V, Q, V, Q, V, Q, Q, V, V, V, V, Q, V, V, V,
    V, V, Q, Q, V, K, V, V, V, V, V, Q, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, V, V, Q,
    V, V, Q, V, V, Q, V, V, V, Q, Q, V, K, V, V, V, V, Q, V, V, V, Q, V, V, V, V, V, V,
    Q, V, V, Q, V, V, V, Q, Q, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, V, V,
    V, V, V, V, Q, V, V, V, Q, Q, V, K, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, V,
    V, V, V, V, Q, V, Q, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, V, V, Q, Q,
    V, V, V, V, V, V, V, V, V, V, V, V, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, V, V, V,
    V, V, Q, Q, V, V, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, V, V, Q, Q, V,
    K, V, V, V, V, V, V, Q, V, V, V, V, V, Q, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, V, V, V,
    Q, Q, V, V, V, V, V, Q, V, V, V, Q, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V,
    Q, Q, V, V, V, V, Q, V, Q, V, V, Q, V, Q, V, V, V, Q, V, V, Q, V, V, V, V, V, V, V,
    V, V, V, V, V, Q, V, V, Q, V, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V,
    V, Q, Q, V, V, V, V, V, Q, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, V, V, Q, Q, V, K,
    V, V, V, V, V, V, V, V, V, V, V, V, V, Q, Q, V, V, V, V, Q, V, Q, V, V, Q, V, V, V,
    V, V, V, V, Q, V, K, V, V, K, Q, V, V, V, V, Q, V, Q, V, Q, V, V, Q, K, V, V, V, Q,
    V, V, Q, V, K, V, K, Q, V, V, V, Q, V, Q, V, V, V, V, V, Q, Q, K, V, Q, V, V, V, V,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, Q, V, V, V, V, V, Q, V, V, V, V,
    Q, Q, V, V, V, V, V, Q, V, V, V, Q, Q, V, V, V, V, V, V, V, V, V, V, V, V, V, V, V,
    V, Q, Q, V, V, V, V, Q, V, Q, K, V, Q, V, V, Q, Q, V, Q, V, Q, Q, V, V, K, K, Q, K,
    Q, K, Q, K, V, Q, K, K, V, Q, Q, V, V, V, V, V, V, V, V, Q, V, V, V, V, V, V, V, V,
    Q, K, Q, V, Q, V, K, V, Q, V, V, V, V, V, V, V, Q, K, V, V, V, Q, K, V, V, V, Q, V,
    V, K, V, K, V, Q, K, V, V, V, Q, V, K, V, V, V, V, V, Q, K, K, V, Q, V, K, V, Q, V,
    V, V, V, V, V, Q, V, V, V, V, V, V, V, V, V, V, Q, Q, Q, Q, V, V, V, V, K, V, V, V,
    V, Q, Q, V, V, V, V, V, K, V, V, V, Q, Q, V, Q, V, V, V, V, V, V, V, V, K, K, K, K,
    K, K, K, K, Q, K, Q, Q, K, Q, K, Q, K, Q, Q, K, Q, Q, K, Q, K, K, K, Q, Q, Q, Q, K,
    K, Q, Q, Q, K, K, Q, Q, K, Q, K, K, Q, K, K, Q, K, Q, Q, Q, Q, Q, K, Q, Q, Q, K, K,
    Q, K, Q, K, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, K, Q, K, Q, Q,
    K, Q, K, K, K, Q, K, K, Q, K, Q, K, K, K, Q, Q, Q, K, K, Q, Q, Q, Q, Q, Q, Q, Q, K,
    K, K, K, Q, K, Q, K, Q, K, Q, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q, K,
    Q, K, Q, Q, Q, Q, Q, Q, K, K, K, K, Q, K, K, K, Q, Q, K, K, Q, Q, Q, K, Q, Q, Q, Q,
    K, Q, K, K, Q, K, Q, K, Q, K, Q, K, Q, K, Q, Q, Q, Q, Q, Q, Q, K, Q, Q, Q, Q, Q, Q,
    Q, K, Q, Q, Q, Q, K, Q, K, Q, Q, K, Q, Q, K, K, K, K, Q, K, Q, K, Q, K, Q, K, Q, K,
    Q, Q, Q, Q, Q, Q, K, K, Q, K, Q, Q, Q, Q, Q, Q, Q, Q, Q, K, Q, K, K, Q, K, Q, K, Q,
    K, Q, Q, K, Q, Q, Q, Q, K, Q, K, Q, Q, Q, Q, K, K, K, K, Q, Q, Q, Q, Q, Q, Q, Q, Q,
    Q, Q, Q, Q, Q, K, Q, Q, K, Q, K, K, K, Q, Q, Q, Q, K, Q, K, K, K, K, K, K, K, Q, Q,
    Q, K, Q, K, Q, Q, K, K, K, K, Q, Q, K, K, Q, Q, Q, K, Q, Q, Q, Q, K, K, K, Q, Q, Q,
    Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q, Q
  ]
theorem entrySpec_B : EntrySpec 19 pref_B tail_B 12000 :=
  entrySpec_of_checkEntrySpec (by decide +kernel)
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_0_5_B : evalRounds 5 u0_B = some u5_B := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_5_10_B : evalRounds 5 u5_B = some u10_B := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem rounds_10_15_B : evalRounds 5 u10_B = some u15_B := by decide +kernel
-- Justification: WordCalculus symbolic round evaluation requires elevated recursion depth.
set_option maxRecDepth 4000000 in
theorem check_entry_B :
    checkEntryTwo 19 pref_B tail_B 12000 u15_B
      118572124402667226942787183035401251327472713866885815623334278971049653593343273
      (91740737713243040051863840645548241264047970202147880 * 10^53 +
        52537224621593528352222997552707606800391029695717887) = true := by
  decide +kernel
theorem entry_B : ∃ v,Rounds u0_B v /\ AggState pref_B 16 19 v := by
  refine ⟨u15_B,?_,good_of_checkEntryTwo _ _ _ _ _ _ _ entrySpec_B check_entry_B⟩
  exact rounds_trans (evalRounds_sound 5 u0_B u5_B rounds_0_5_B)
    (rounds_trans (evalRounds_sound 5 u5_B u10_B rounds_5_10_B)
      (evalRounds_sound 5 u10_B u15_B rounds_10_15_B))

end

def callState_1RA0RD : Call → Fin 6
  | .ch => F
  | .cj => E
  | .cp => E
  | .ca => F

def callWord_1RA0RD : Call → BitWord
  | .ch => [1]
  | .cj => [1, 1]
  | .cp => [1, 0]
  | .ca => [1, 1, 1, 0, 1, 0]

def cfgR_1RA0RD (l : HalfTape) (c : Call) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (r <{{callState_1RA0RD c}} (l <+ callWord_1RA0RD c))

def cfgL_1RA0RD (l : HalfTape) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  (([0] +> r) {{A}}> l)

def cfgAt_1RA0RD (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  cfgL_1RA0RD lh (w_pre +> r)

abbrev Step_1RA0RD := CallStep target cfgR_1RA0RD cfgL_1RA0RD

syntax "run_1RA0RD" : tactic
macro_rules
  | `(tactic| run_1RA0RD) =>
    `(tactic| (
      intro l r
      dsimp [cfgR_1RA0RD, cfgL_1RA0RD, callWord_1RA0RD, callState_1RA0RD, t, d0, d1, one, lh]
      try simp only [List.cons_append, List.nil_append, append_cons, append_nil, cons_zero_default]
      execute))

theorem baseRules_1RA0RD : BaseRules Step_1RA0RD where
  seg_cp_t := seg2 [1, 1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD)
  seg_cj_t := seg2 [1, 1, 0, 1, 1] (by run_1RA0RD) (by run_1RA0RD)
  seg_ch_t0 := seg2 [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD)
  seg_ch_t1 := seg5 [1, 0, 1, 1] [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD) (by run_1RA0RD)
  seg_ch_t := seg5 [1, 0, 1, 1] [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD) (by run_1RA0RD)
  seg_cp_d10 := seg4 (by run_1RA0RD)
  seg_cj_d10 := seg2 [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD)
  seg_cp_d11 := seg2 [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD)
  seg_cj_d11 := seg5 [1, 0, 1, 1] [1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD) (by run_1RA0RD)
  seg_cj_d0 := seg4 (by run_1RA0RD)
  seg_ch_d01 := seg4 (by run_1RA0RD)
  seg_ch_d11 := seg2 [1, 1] (by run_1RA0RD) (by run_1RA0RD)
  seg_cj_d1 := seg2 [1, 1] (by run_1RA0RD) (by run_1RA0RD)
  seg_ch_d0 := seg4 (by run_1RA0RD)
  seg_ch_d1 := seg2 [1, 1] (by run_1RA0RD) (by run_1RA0RD)
  side_ch_blank := by
    refine Side.cons (fun l => ?_) (Side.nil _)
    simp only [cfgR_1RA0RD, cfgL_1RA0RD, callWord_1RA0RD, callState_1RA0RD, d1,
      List.cons_append, List.nil_append, append_cons, append_nil, cons_zero_default]
    execute

theorem seg_ca_t_1RA0RD : Seg Step_1RA0RD [.ca] [.ch, .ch] t [1, 1, 0, 0, 0, 1, 1, 0, 0] :=
  seg5 [1, 0, 1, 1, 1, 1, 0, 1, 0] [1, 0, 1, 0, 1, 1, 0, 1, 0]
    (by run_1RA0RD) (by run_1RA0RD) (by run_1RA0RD)

theorem seg_ch_mid_1RA0RD :
    Seg Step_1RA0RD [.ch] [.ch] [1, 1, 0, 0, 0, 1, 1, 0, 0] (t ++ t ++ one) :=
  seg2 [1, 1, 0, 1, 1, 1, 0, 1, 0] (by run_1RA0RD) (by run_1RA0RD)

theorem step_ca_1RA0RD (r : HalfTape) :
    (cfgL_1RA0RD lh r) [target]⊢⁺ (cfgR_1RA0RD ([1] +> default) .ca r) := by
  simp only [cfgR_1RA0RD, cfgL_1RA0RD, callWord_1RA0RD, callState_1RA0RD, lh,
    List.cons_append, List.nil_append, append_cons, append_nil, cons_zero_default]; execute

theorem step_ch_1RA0RD (r : HalfTape) :
    (cfgL_1RA0RD ([1] +> default) r) [target]⊢⁺ (cfgR_1RA0RD lh .ch r) := by
  simp only [cfgR_1RA0RD, cfgL_1RA0RD, callWord_1RA0RD, callState_1RA0RD, lh,
    List.cons_append, List.nil_append, append_cons, append_nil, cons_zero_default]; execute

theorem cycle_1RA0RD {r r' : HalfTape} (hI : NumRun Step_1RA0RD 12 r r') :
    (cfgAt_1RA0RD r) [target]⊢⁺ (cfgAt_1RA0RD (t +> r')) :=
  cycle_ca_ch baseRules_1RA0RD seg_ca_t_1RA0RD seg_ch_mid_1RA0RD step_ca_1RA0RD step_ch_1RA0RD hI

def c_end_1RA0RD : Counter.CCfg (Fin 2) (Fin 6) :=
  ⟨0, 1,
    [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0,
      1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 1],
    [0, 1]⟩

-- Justification: Bounded window simulation over 1107 steps.
set_option maxRecDepth 4000000 in
theorem stem_1RA0RD : (init []) [target]⊢* cfgAt_1RA0RD (evalWords u0_A default) := by
  have h0 : (init [] : Cfg (Fin 2) (Fin 6)) = evalBCfg ⟨0, 0, [], []⟩ := rfl
  have h1 : evalBCfg c_end_1RA0RD = cfgAt_1RA0RD (evalWords u0_A default) := by
    unfold evalBCfg evalWindow c_end_1RA0RD cfgAt_1RA0RD cfgL_1RA0RD lh w_pre u0_A
    simp only [List.replicate, List.cons_append, List.nil_append, evalWords, wordsToBits,
      t, d1, d0, one, append_cons, append_nil, cons_zero_default]
    rfl
  rw [h0, ← h1]
  exact ⟨1107, Counter.bmultiStep_sound (tm := target) 1107 ⟨0, 0, [], []⟩ c_end_1RA0RD (by decide)⟩

def c_end_1LA0LE : Counter.CCfg (Fin 2) (Fin 6) :=
  ⟨0, 1,
    [0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 1,
      0, 0, 1, 0, 1, 1, 0, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1,
      0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 1],
    [0, 1]⟩

-- Justification: Bounded window simulation over 5370 steps for conjugate twin 1LA0LE.
set_option maxRecDepth 4000000 in
theorem stem_1LA0LE :
    (((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) [target]⊢*
      cfgAt_1RA0RD (evalWords u0_B default) := by
  have h0 : (((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) =
      evalBCfg ⟨5, 0, [], []⟩ := rfl
  have h1 : evalBCfg c_end_1LA0LE = cfgAt_1RA0RD (evalWords u0_B default) := by
    unfold evalBCfg evalWindow c_end_1LA0LE cfgAt_1RA0RD cfgL_1RA0RD lh w_pre u0_B
    simp only [List.replicate, List.cons_append, List.nil_append, evalWords, wordsToBits,
      t, d1, d0, one, append_cons, append_nil, cons_zero_default]
    rfl
  rw [h0, ← h1]
  exact ⟨5370, Counter.bmultiStep_sound (tm := target) 5370 ⟨5, 0, [], []⟩ c_end_1LA0LE (by decide)⟩

end Solution

@[expose] public section

open Solution in
theorem is_not_halt_from_1LA0LE :
    ∀ cfg : Cfg (Fin 2) (Fin 6),
      ((((default : ListBlank (Fin 2)) {{5}}> default) : Cfg (Fin 2) (Fin 6)) [target]⊢* cfg) →
      (step target cfg).isSome :=
  is_not_halt_of_aggState baseRules_1RA0RD cycle_1RA0RD
    safe_pref_B copyTwelve_B stem_1LA0LE entry_B

open Solution in
theorem is_does_not_halt : IsNotHalt target_tm :=
  is_not_halt_of_aggState baseRules_1RA0RD cycle_1RA0RD
    safe_pref_A copyTwelve_A stem_1RA0RD entry_A

theorem is_not_halt : IsNotHalt target := is_does_not_halt

end

end BusyBeaver.M_1RB0RA_0RC0RE_0LDHHH_1LE1LD_1LF0LD_1RA0RD
