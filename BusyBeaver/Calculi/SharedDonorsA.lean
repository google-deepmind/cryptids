module

public import BusyBeaver.Bridge
public import BusyBeaver.Calculi.Counter
public import BusyBeaver.Calculi.Excursion

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver


namespace TM24Donor

abbrev HalfTape := ListBlank (Fin 2)
abbrev BitWord := List (Fin 2)

def donor24_machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LA_1RC0LE_1RD0LF_0LA0RD_1LC0LE_HHH0RE"

abbrev tm24 : Machine (Fin 2) (Fin 6) := donor24_machine.toBB

abbrev bit0 : BitWord := [0]
abbrev bit1 : BitWord := [1]

@[simp] theorem multiStep_zero' (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 0 = some config := rfl
@[simp] theorem multiStep_one' (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) :
    multiStep M config 1 = step M config := rfl
@[simp] theorem multiStep_succ' (M : Machine (Fin 2) (Fin 6)) (config : Cfg (Fin 2) (Fin 6)) (n :
    Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]
@[simp] theorem zero_cons_default' : Turing.ListBlank.cons (0 : Fin 2) default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem default_head' : (default : HalfTape).head = 0 := rfl
@[simp] theorem default_tail' : (default : HalfTape).tail = default := rfl
@[simp] theorem append_nil (s : HalfTape) : ([] : BitWord) +> s = s := rfl
@[simp] theorem append_cons (a : Fin 2) (l : BitWord) (s : HalfTape) :
    (a :: l) +> s = Turing.ListBlank.cons a (l +> s) := rfl
@[simp] theorem append_assoc (l1 l2 : BitWord) (s : HalfTape) :
    (l1 ++ l2) +> s = l1 +> (l2 +> s) := by
  induction l1 with
  | nil => rfl
  | cons a l1 ih => simp only [List.cons_append, append_cons, ih]

theorem stepPlus_of_multiStep (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h :
    c_1 [tm]⊢ c_2) :
    c_1 [tm]⊢^{1} c_2 := by simp [h]
theorem step_right_cons (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 : Cfg (Fin 2) (Fin 6)) (h : c_1
    [tm]⊢ c_2) :
    c_1 [tm]⊢⁺ c_2 := ⟨1, by decide, stepPlus_of_multiStep tm c_1 c_2 h⟩
theorem multiStep_add' (tm : Machine (Fin 2) (Fin 6)) (c_1 : Cfg (Fin 2) (Fin 6)) (n m : Nat) :
    multiStep tm c_1 (n + m) = (multiStep tm c_1 n).bind (fun c_2 => multiStep tm c_2 m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, multiStep_succ', ih, Option.bind_assoc]
    simp_rw [multiStep_succ']
theorem multiStep_trans' (tm : Machine (Fin 2) (Fin 6)) (c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)) (n m :
    Nat)
    (h₁ : c_1 [tm]⊢^{n} c_2) (h₂ : c_2 [tm]⊢^{m} c_3) :
    c_1 [tm]⊢^{n+m} c_3 := by
  rw [multiStep_add', h₁]; simp [h₂]
theorem stepPlus_stepStar' {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 : Cfg (Fin 2) (Fin 6)} (h : c_1
    [tm]⊢⁺ c_2) :
    c_1 [tm]⊢* c_2 := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩
theorem stepStar_trans' {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans' tm c_1 c_2 c_3 n m hn hm⟩
theorem step_right_default {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢⁺ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m),
      multiStep_trans' tm c_1 c_2 c_3 n m hn hm⟩
theorem stepPlus_of_step {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢⁺ c_3) : c_1 [tm]⊢⁺ c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, multiStep_trans' tm c_1 c_2 c_3 n m hn hm⟩
theorem stepPlus_trans' {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢* c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢* c_3 := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, multiStep_trans' tm c_1 c_2 c_3 n m hn hm⟩
theorem step_left_cons {tm : Machine (Fin 2) (Fin 6)} {c_1 c_2 c_3 : Cfg (Fin 2) (Fin 6)}
    (h₁ : c_1 [tm]⊢ c_2) (h₂ : c_2 [tm]⊢* c_3) : c_1 [tm]⊢⁺ c_3 :=
  step_right_default (step_right_cons tm c_1 c_2 h₁) h₂

macro "finish" : tactic =>
  `(tactic| try exact ⟨0, rfl⟩)
macro "step" : tactic =>
  `(tactic| (try refine stepPlus_stepStar' ?_) <;>
    refine step_left_cons (by (try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft,
        Turing.ListBlank.head_cons, default_head']); rfl) ?_ <;>
    simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move,
        Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons, Tape.write, zero_cons_default',
        default_head', default_tail'])
macro "execute" : tactic =>
  `(tactic| repeat (any_goals (first | exact ⟨0, rfl⟩ | step)))

abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

@[simp] theorem listPow_zero {α : Type*} (l : List α) : l ^ (0 : Nat) = [] := rfl
@[simp] theorem listPow_succ {α : Type*} (l : List α) (n : Nat) : l ^ (n + 1) = l ++ l ^ n := rfl
@[simp] theorem listPow_succ' {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ++ l ^ n := by
  rw [Nat.add_comm 1 n]; rfl
@[simp] theorem listPow_one {α : Type*} (l : List α) : l ^ (1 : Nat) = l := by
  change l ++ [] = l; exact List.append_nil l

theorem listPow_add {α : Type*} (l : List α) (m n : Nat) : l ^ (m + n) = l ^ m ++ l ^ n :=
  BusyBeaver.list_pow_add l m n

theorem listPow_shift {α : Type*} (l : List α) (n : Nat) : l ^ (1 + n) = l ^ n ++ l := by
  rw [Nat.add_comm 1 n, BusyBeaver.list_pow_succ']

theorem step_left_default (l : BitWord) (n : Nat) (s : HalfTape) : (l ^ (1 + n)) +> s = l +>
    ((l ^ n) +> s) := by
  rw [listPow_succ', append_assoc]

theorem step_right_zero_default (l : BitWord) (n : Nat) (s : HalfTape) : (l ^ n) +> (l +>
    s) = (l ^ (1 + n)) +> s := by
  rw [listPow_shift, append_assoc]

theorem rot_0 (n : Nat) (r : HalfTape) :
    (bit0 ^ n) +> ([0] +> r) = [0] +> ((bit0 ^ n) +> r) := by
  rw [step_right_zero_default bit0 n r, step_left_default bit0 n r]

theorem rot_0_3 (n : Nat) (r : HalfTape) :
    (bit0 ^ n) +> ([0, 0, 0] +> r) = [0, 0, 0] +> ((bit0 ^ n) +> r) := by
  have h1 : ([0, 0, 0] : BitWord) +> r = [0] +> ([0] +> ([0] +> r)) := rfl
  rw [h1, rot_0, rot_0, rot_0]
  rfl

-- ============================================================================
-- Section 1: Directed-Head Configurations & Local Tape Sweeps (Others_v1.v:13-176)
-- ============================================================================

def stepCfg (l r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  ([0] +> l) {{D}}> r

def root (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  stepCfg ([1] +> default) r

def backCfg (l r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  l <{{E}} ([0, 0, 0] +> r)

def returnCfg (l r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  l <{{E}} ([0, 0] +> r)

theorem shiftL_E_1_step (l r : HalfTape) :
    (([1] +> l) <{{E}} r) [tm24]⊢* (l <{{E}} ([0] +> r)) := by
  simp only [append_cons, append_nil]
  execute

theorem shiftL_E_1 (n : Nat) (l r : HalfTape) :
    (((bit1 ^ n) +> l) <{{E}} r) [tm24]⊢* (l <{{E}} ((bit0 ^ n) +> r)) := by
  induction n generalizing r with
  | zero =>
    simp only [listPow_zero, append_nil]
    finish
  | succ n ih =>
    have hn : n + 1 = 1 + n := by omega
    rw [hn, step_left_default bit1 n l]
    refine stepPlus_trans' (shiftL_E_1_step ((bit1 ^ n) +> l) r) ?_
    simpa only [step_right_zero_default bit0 n r] using ih ([0] +> r)

theorem back_digit_head (l r : HalfTape) :
    (backCfg ([0] +> ([1, 1] +> l)) r) [tm24]⊢* (l <{{E}} ([0, 0, 0] +> ([1, 1, 0] +> r))) := by
  unfold backCfg
  simp only [append_cons, append_nil]
  execute

theorem back_digit (n : Nat) (l r : HalfTape) :
    (backCfg ([0] +> ((bit1 ^ (2 + n)) +> l)) r) [tm24]⊢*
      (backCfg l (((bit0 ^ n) ++ [1, 1, 0]) +> r)) := by
  have h1 : (bit1 ^ (2 + n)) +> l = [1, 1] +> ((bit1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, step_left_default bit1 (1 + n) l, step_left_default bit1 n l]
    rfl
  rw [h1]
  refine stepPlus_trans' (back_digit_head ((bit1 ^ n) +> l) r) ?_
  refine stepPlus_trans' (shiftL_E_1 n l ([0, 0, 0] +> ([1, 1, 0] +> r))) ?_
  unfold backCfg
  rw [rot_0_3 n ([1, 1, 0] +> r), append_assoc]


theorem start_back_head (l r : HalfTape) :
    (stepCfg ([0] +> ([1, 1] +> l)) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (l <{{E}} ([0, 0, 0] +> ([0] +> ([1, 1, 0] +> r)))) := by
  unfold stepCfg
  simp only [append_cons, append_nil]
  execute

theorem start_back (n : Nat) (l r : HalfTape) :
    (stepCfg ([0] +> ((bit1 ^ (2 + n)) +> l)) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (backCfg l ((bit0 ^ (1 + n)) +> ([1, 1, 0] +> r))) := by
  have h1 : (bit1 ^ (2 + n)) +> l = [1, 1] +> ((bit1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, step_left_default bit1 (1 + n) l, step_left_default bit1 n l]
    rfl
  rw [h1]
  refine step_right_default (start_back_head ((bit1 ^ n) +> l) r) ?_
  refine stepPlus_trans' (shiftL_E_1 n l ([0, 0, 0] +> ([0] +> ([1, 1, 0] +> r)))) ?_
  unfold backCfg
  rw [rot_0_3 n ([0] +> ([1, 1, 0] +> r)), step_right_zero_default bit0 n ([1, 1, 0] +> r)]


def pending (hs : List Nat) (l : HalfTape) : HalfTape :=
  hs.foldl (fun l h => [0] +> ((bit1 ^ (2 + h)) +> l)) l

@[simp] theorem pending_nil (l : HalfTape) : pending [] l = l := rfl
@[simp] theorem pending_cons (h : Nat) (hs : List Nat) (l : HalfTape) :
    pending (h :: hs) l = pending hs ([0] +> ((bit1 ^ (2 + h)) +> l)) := rfl

def back_word (hs : List Nat) : BitWord :=
  hs.flatMap (fun h => (bit0 ^ h) ++ [1, 1, 0])

@[simp] theorem back_word_nil : back_word [] = [] := rfl
@[simp] theorem back_word_cons (h : Nat) (hs : List Nat) :
    back_word (h :: hs) = (bit0 ^ h) ++ [1, 1, 0] ++ back_word hs := rfl

theorem pending_back (hs : List Nat) (l r : HalfTape) :
    (backCfg (pending hs l) r) [tm24]⊢* (backCfg l (back_word hs +> r)) := by
  induction hs generalizing l r with
  | nil =>
    simp only [pending_nil, back_word_nil, append_nil]
    finish
  | cons h hs ih =>
    simp only [pending_cons, back_word_cons, append_assoc]
    refine stepPlus_trans' (ih ([0] +> ((bit1 ^ (2 + h)) +> l)) r) ?_
    refine stepPlus_trans' (back_digit h l (back_word hs +> r)) ?_
    rw [append_assoc]


def digits (ds : List Nat) : BitWord :=
  ds.flatMap (fun d => (bit0 ^ (1 + d)) ++ [1, 1])

@[simp] theorem digits_nil : digits [] = [] := rfl
@[simp] theorem digits_cons (d : Nat) (ds : List Nat) :
    digits (d :: ds) = (bit0 ^ (1 + d)) ++ [1, 1] ++ digits ds := rfl

inductive IsBinary : List Nat → Prop where
  | nil : IsBinary []
  | cons {d : Nat} {ds : List Nat} : d ≤ 1 → IsBinary ds → IsBinary (d :: ds)

theorem isBinary_append {u v : List Nat} : IsBinary (u ++ v) ↔ IsBinary u ∧ IsBinary v := by
  induction u with
  | nil =>
    simp only [List.nil_append]
    exact ⟨fun h => ⟨IsBinary.nil, h⟩, fun ⟨_, h⟩ => h⟩
  | cons d u ih =>
    constructor
    · intro h
      cases h with
      | cons hd hrest =>
        rcases ih.mp hrest with ⟨hu, hv⟩
        exact ⟨IsBinary.cons hd hu, hv⟩
    · rintro ⟨hu, hv⟩
      cases hu with
      | cons hd hu' =>
        exact IsBinary.cons hd (ih.mpr ⟨hu', hv⟩)

theorem scan_digit_one {d : Nat} (hd : d ≤ 1) (l r : HalfTape) :
    (stepCfg l ((bit0 ^ (1 + d)) +> ([1, 1] +> r))) [tm24]⊢*
      (stepCfg ([0] +> ((bit1 ^ (2 + d)) +> l)) r) := by
  rcases d with _ | _ | d
  · unfold stepCfg
    simp only [Nat.add_zero, listPow_succ, listPow_zero, bit0, bit1, List.cons_append,
        List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  · unfold stepCfg
    simp only [listPow_succ, listPow_zero, bit0, bit1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  · omega

theorem scan_digits {ds : List Nat} (hds : IsBinary ds) (l r : HalfTape) :
    (stepCfg l (digits ds +> r)) [tm24]⊢* (stepCfg (pending ds l) r) := by
  induction hds generalizing l r with
  | nil =>
    simp only [digits_nil, append_nil, pending_nil]
    finish
  | @cons d ds hd hds ih =>
    simp only [digits_cons, pending_cons, append_assoc]
    refine stepPlus_trans' (scan_digit_one hd l (digits ds +> r)) ?_
    exact ih ([0] +> ((bit1 ^ (2 + d)) +> l)) r

theorem ordinary_return {ds : List Nat} {n : Nat} (hds : IsBinary ds) (hn : n ≤ 1) (l r : HalfTape)
    :
    (stepCfg l (digits ds +> ((bit0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r)))) [tm24]⊢⁺
      (backCfg l (back_word ds +> ((bit0 ^ (1 + n)) +> ([1, 1, 0] +> r)))) := by
  refine stepPlus_of_step (scan_digits hds l ((bit0 ^ (1 + n)) +> ([1, 1, 0, 0, 0] +> r))) ?_
  have hsplit : ([1, 1, 0, 0, 0] : BitWord) +> r = [1, 1] +> ([0, 0, 0] +> r) := rfl
  rw [hsplit]
  refine stepPlus_of_step (scan_digit_one hn (pending ds l) ([0, 0, 0] +> r)) ?_
  refine step_right_default (start_back n (pending ds l) r) ?_
  exact pending_back ds l ((bit0 ^ (1 + n)) +> ([1, 1, 0] +> r))

theorem zero_back_word (ds : List Nat) (r : HalfTape) :
    [0] +> (back_word ds +> r) = digits ds +> ([0] +> r) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [back_word_cons, digits_cons, append_assoc]
    have h1 : ([1, 1, 0] : BitWord) +> (back_word ds +> r) = [1,
        1] +> ([0] +> (back_word ds +> r)) := rfl
    rw [h1, ih, ← rot_0 d ([1, 1] +> (digits ds +> ([0] +> r))), ← step_right_zero_default bit0 d]

theorem close6 (l r : HalfTape) :
    (backCfg ((bit0 ^ 6) +> l) r) [tm24]⊢*
      (stepCfg ([1] +> ([0] +> l)) ([0, 0, 1, 1, 1, 0] +> r)) := by
  unfold backCfg stepCfg
  simp only [listPow_succ, listPow_zero, bit0, List.cons_append, List.nil_append, List.append_nil,
      append_cons, append_nil]
  execute

theorem close2 (l r : HalfTape) :
    (backCfg ([0, 0] +> ((bit1 ^ 4) +> l)) r) [tm24]⊢*
      (l <{{A}} ((bit1 ^ 8) +> ([0] +> r))) := by
  unfold backCfg
  simp only [listPow_succ, listPow_zero, bit1, List.cons_append, List.nil_append, List.append_nil,
      append_cons, append_nil]
  execute

theorem block_back_head (l r : HalfTape) :
    (([0] +> ([1, 1] +> l)) <{{A}} ((bit1 ^ 8) +> r)) [tm24]⊢*
      (l <{{E}} ([0, 0, 0] +> ([0] +> ((bit1 ^ 7) +> r)))) := by
  simp only [listPow_succ, listPow_zero, bit1, List.cons_append, List.nil_append, List.append_nil,
      append_cons, append_nil]
  execute

theorem block_back_one (n : Nat) (l r : HalfTape) :
    (([0] +> ((bit1 ^ (2 + n)) +> l)) <{{A}} ((bit1 ^ 8) +> r)) [tm24]⊢*
      (backCfg l ((bit0 ^ (1 + n)) +> ((bit1 ^ 7) +> r))) := by
  have h1 : (bit1 ^ (2 + n)) +> l = [1, 1] +> ((bit1 ^ n) +> l) := by
    have h2n : 2 + n = 1 + (1 + n) := by omega
    rw [h2n, step_left_default bit1 (1 + n) l, step_left_default bit1 n l]
    rfl
  rw [h1]
  refine stepPlus_trans' (block_back_head ((bit1 ^ n) +> l) r) ?_
  refine stepPlus_trans' (shiftL_E_1 n l ([0, 0, 0] +> ([0] +> ((bit1 ^ 7) +> r)))) ?_
  unfold backCfg
  rw [rot_0_3 n ([0] +> ((bit1 ^ 7) +> r)), step_right_zero_default bit0 n ((bit1 ^ 7) +> r)]


theorem block_back (hs : List Nat) (n : Nat) (l r : HalfTape) :
    (([0] +> ((bit1 ^ (2 + n)) +> pending hs l)) <{{A}} ((bit1 ^ 8) +> r)) [tm24]⊢*
      (backCfg l (back_word hs +> ((bit0 ^ (1 + n)) +> ((bit1 ^ 7) +> r)))) := by
  refine stepPlus_trans' (block_back_one n (pending hs l) r) ?_
  exact pending_back hs l ((bit0 ^ (1 + n)) +> ((bit1 ^ 7) +> r))

theorem scan_seven {b : Nat} (hb : b = 1 ∨ b = 2) (l r : HalfTape) :
    (stepCfg l ((bit0 ^ b) +> ((bit1 ^ 7) +> r))) [tm24]⊢*
      (stepCfg ((bit0 ^ 6) +> ((bit1 ^ (1 + b)) +> l)) r) := by
  rcases hb with rfl | rfl <;> {
    unfold stepCfg
    simp only [listPow_succ, listPow_zero, bit0, bit1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  }

theorem last7 (b : Nat) (ds : List Nat) (n : Nat) (l r : HalfTape)
    (hb : b = 1 ∨ b = 2) (hds : IsBinary ds) (hn : n ≤ 1) :
    (stepCfg l ((bit0 ^ b) +> ((bit1 ^ 7) +> (digits ds +> ((bit0 ^ (1 + n)) +> ([1, 1, 0, 0,
        0] +> r)))))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((bit1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits ds +> ((bit0 ^ (2 + n)) +> ([1, 1, 0] +> r))))) := by
  refine stepPlus_of_step (scan_seven hb l (digits ds +> ((bit0 ^ (1 + n)) +> ([1, 1, 0, 0,
      0] +> r)))) ?_
  refine step_right_default (ordinary_return hds hn ((bit0 ^ 6) +> ((bit1 ^ (1 + b)) +> l)) r) ?_
  refine stepPlus_trans' (close6 ((bit1 ^ (1 + b)) +> l) (back_word ds +> ((bit0 ^ (1 + n)) +> ([1,
      1, 0] +> r)))) ?_
  have h1 : ([0, 0, 1, 1, 1, 0] : BitWord) +> (back_word ds +> ((bit0 ^ (1 + n)) +> ([1, 1,
      0] +> r))) =
      [0, 0, 1, 1, 1] +> ([0] +> (back_word ds +> ((bit0 ^ (1 + n)) +> ([1, 1, 0] +> r)))) := rfl
  have h2n : 2 + n = 1 + (1 + n) := by omega
  rw [h1, zero_back_word, h2n, step_left_default bit0 (1 + n) ([1, 1, 0] +> r)]


theorem active_scan (l r : HalfTape) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1] +> r)) [tm24]⊢*
      (stepCfg ([0, 0] +> ((bit1 ^ 4) +> l)) r) := by
  unfold stepCfg
  simp only [listPow_succ, listPow_zero, bit1, List.cons_append, List.nil_append, List.append_nil,
      append_cons, append_nil]
  execute

theorem active_turn (l r : HalfTape) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1, 0, 0, 0] +> r)) [tm24]⊢⁺
      (stepCfg ([0] +> ((bit1 ^ 3) +> l)) ([0, 0, 1, 1, 0] +> r)) := by
  unfold stepCfg
  simp only [listPow_succ, listPow_zero, bit1, List.cons_append, List.nil_append, List.append_nil,
      append_cons, append_nil]
  execute

def payload (ds : List Nat) : BitWord :=
  ds.flatMap (fun d => (bit0 ^ d) ++ [1, 1])

def put_left (hs : List Nat) (l : HalfTape) : HalfTape :=
  hs.foldl (fun l h => [0] +> ((bit1 ^ h) +> l)) l

def seed : List Nat := [2, 2, 1, 2, 2, 1, 2]

def cap_entry (ds : List Nat) (h : Nat) (r : HalfTape) : Cfg (Fin 2) (Fin 6) :=
  root ([0, 0] +> (payload ds +> ((bit0 ^ h) +> ((bit1 ^ 7) +> r))))

theorem bridge0 (r : HalfTape) :
    (cap_entry [] 4 r) [tm24]⊢⁺
      (stepCfg (put_left [3] default) (payload [2] +> ([0, 0] +> ((bit1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    listPow_succ, listPow_zero, bit0, bit1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

theorem bridge1 (r : HalfTape) :
    (cap_entry [2, 2] 3 r) [tm24]⊢⁺
      (stepCfg (put_left [4, 3] default) (payload [2, 1, 1] +> ([0] +> ((bit1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    listPow_succ, listPow_zero, bit0, bit1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

theorem bridge2 (r : HalfTape) :
    (cap_entry [3, 2, 2, 1, 1] 2 r) [tm24]⊢⁺
      (stepCfg (put_left [3] default) (payload [2, 1, 2, 2, 1, 1] +> ([0,
          0] +> ((bit1 ^ 7) +> r)))) := by
  unfold cap_entry root stepCfg payload put_left
  simp only [List.flatMap_nil, List.flatMap_cons, List.foldl_cons, List.foldl_nil,
    listPow_succ, listPow_zero, bit0, bit1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

theorem bridge3 (r : HalfTape) :
    (cap_entry [2, 2, 1, 2, 2, 1, 1] 3 r) [tm24]⊢⁺
      (root ([0, 0] +> ((bit1 ^ 7) +> (payload seed +> ([0] +> ((bit1 ^ 7) +> r)))))) := by
  unfold cap_entry root stepCfg payload seed
  simp only [List.flatMap_nil, List.flatMap_cons,
    listPow_succ, listPow_zero, bit0, bit1,
    List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
  execute

-- ============================================================================
-- Section 2: Prefix Value, Tail, Num, Tags, Segment, Block, Carry, Advance
-- (Others_v1.v:180-665)
-- ============================================================================

def prefix_value : Nat → List Nat → Nat
  | k + 1, d :: ds => d * 2 ^ k + prefix_value k ds
  | _, _ => 0

theorem prefix_carry (n : Nat) (u : List Nat) (a : Nat) (t : List Nat) :
    prefix_value n (u ++ [a, 3] ++ t) ≤ prefix_value n (u ++ [1 + a, 1] ++ t) ∧
    prefix_value n (u ++ [1 + a, 1] ++ t) ≤ 1 + prefix_value n (u ++ [a, 3] ++ t) := by
  induction u generalizing n with
  | nil =>
    rcases n with _ | _ | k
    · simp [prefix_value]
    · simp [prefix_value]
    · simp only [List.nil_append, List.cons_append, prefix_value]
      have heq : (1 + a) * 2 ^ (k + 1) + (1 * 2 ^ k + prefix_value k t) =
          a * 2 ^ (k + 1) + (3 * 2 ^ k + prefix_value k t) := by
        rw [Nat.pow_succ]
        ring
      omega
  | cons d u ih =>
    rcases n with _ | k
    · simp [prefix_value]
    · simp only [List.cons_append, prefix_value]
      have h := ih k
      simp only [List.append_assoc] at h ⊢
      omega

theorem prefix_last (n : Nat) (u : List Nat) (a : Nat) (h : n ≤ 1 + u.length) :
    prefix_value n (u ++ [a]) ≤ prefix_value n (u ++ [1 + a]) ∧
    prefix_value n (u ++ [1 + a]) ≤ 1 + prefix_value n (u ++ [a]) := by
  induction u generalizing n with
  | nil =>
    rcases n with _ | _ | k
    · simp [prefix_value]
    · simp [prefix_value]
    · simp at h
  | cons d u ih =>
    rcases n with _ | k
    · simp [prefix_value]
    · simp only [List.length_cons] at h
      simp only [List.cons_append, prefix_value]
      have h' := ih k (by omega)
      omega

inductive Tail : List Nat → Prop where
  | nil : Tail []
  | zero (ds : List Nat) : Tail ds → Tail (0 :: ds)
  | one (ds : List Nat) : Tail ds → Tail (1 :: ds)
  | two (n : Nat) : Tail (2 :: List.replicate n 0)

inductive Num : Bool → List Nat → Prop where
  | nil (p : Bool) : Num p []
  | zero (p : Bool) (ds : List Nat) : Tail ds → Num p (0 :: ds)
  | one (p : Bool) (ds : List Nat) : Num (!p) ds → Num p (1 :: ds)
  | two (n : Nat) : Num false (2 :: List.replicate n 0)

theorem tail_zeros (n : Nat) : Tail (List.replicate n 0) := by
  induction n with
  | zero => exact Tail.nil
  | succ n ih => exact Tail.zero (List.replicate n 0) ih

theorem tail_prefix {u t : List Nat} (hu : IsBinary u) (ht : Tail t) : Tail (u ++ t) := by
  induction hu with
  | nil => exact ht
  | @cons d ds hd _ ih =>
    rcases d with _ | _ | d
    · exact Tail.zero (ds ++ t) ih
    · exact Tail.one (ds ++ t) ih
    · omega

theorem tail_binary {u : List Nat} (hu : IsBinary u) : Tail u := by
  simpa using tail_prefix hu Tail.nil

theorem num_binary {u : List Nat} (hu : IsBinary u) (p : Bool) : Num p u := by
  induction hu generalizing p with
  | nil => exact Num.nil p
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · exact Num.zero p ds (tail_binary hds)
    · exact Num.one p ds (ih (!p))
    · omega

theorem num_tail {p : Bool} {ds : List Nat} (h : Num p ds) : Tail ds := by
  induction h with
  | nil => exact Tail.nil
  | zero _ ds ht => exact Tail.zero ds ht
  | one _ ds _ ih => exact Tail.one ds ih
  | two n => exact Tail.two n

theorem num_one {p : Bool} {ds : List Nat} (h : Num p (1 :: ds)) : Num (!p) ds := by
  cases h with
  | one _ _ h' => exact h'

theorem num_two {p : Bool} {ds : List Nat} (h : Num p (2 :: ds)) : p = false := by
  cases h
  rfl

theorem tail_bump {u : List Nat} (a n : Nat) (hu : IsBinary u) (ha : a ≤ 1) :
    Tail (u ++ [1 + a] ++ List.replicate n 0) := by
  rw [List.append_assoc]
  refine tail_prefix hu ?_
  rcases a with _ | _ | a
  · exact Tail.one (List.replicate n 0) (tail_zeros n)
  · exact Tail.two n
  · omega

theorem num_carry (p : Bool) {u : List Nat} (a n : Nat)
    (hu : IsBinary u) (ha : a ≤ 1)
    (h : Num p (u ++ [a, 2] ++ List.replicate n 0)) :
    Num (!p) (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  induction hu generalizing p with
  | nil =>
    rcases a with _ | _ | a
    · exact Num.one (!p) (0 :: List.replicate n 0) (Num.zero (!!p) (List.replicate n 0) (tail_zeros
        n))
    · simp only [List.nil_append, List.cons_append] at h ⊢
      have hp : (!p) = false := num_two (num_one h)
      rcases p with _ | _
      · cases hp
      · exact Num.two (n + 1)
    · omega
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · simp only [List.cons_append]
      have hrep : [1 + a, 0] ++ List.replicate n 0 = [1 + a] ++ List.replicate (n + 1) 0 := rfl
      rw [List.append_assoc, hrep, ← List.append_assoc]
      exact Num.zero (!p) _ (tail_bump a (n + 1) hds ha)
    · simp only [List.cons_append] at h ⊢
      refine Num.one (!p) _ ?_
      have h' := ih (!p) (num_one h)
      simpa using h'
    · omega

def mass : List Nat → Nat
  | [] => 0
  | d :: ds => 1 + d + mass ds

theorem mass_app (u v : List Nat) : mass (u ++ v) = mass u + mass v := by
  induction u with
  | nil => simp [mass]
  | cons d u ih => simp only [List.cons_append, mass, ih]; omega

theorem mass_zeros (n : Nat) : mass (List.replicate n 0) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, mass, ih]; omega

def oddB : Nat → Bool
  | 0 => false
  | n + 1 => !(oddB n)

theorem odd_next (n : Nat) : oddB (1 + n) = !(oddB n) := by
  rw [Nat.add_comm 1 n]; rfl

theorem odd_succ (n : Nat) : oddB (n + 1) = !(oddB n) := rfl

theorem odd_add (a b : Nat) : oddB (a + b) = xor (oddB a) (oddB b) := by
  induction a with
  | zero => simp [oddB]
  | succ a ih =>
    rw [Nat.succ_add, odd_succ, odd_succ, ih]
    cases oddB a <;> cases oddB b <;> rfl

inductive AllOnes : List Nat → Prop where
  | nil : AllOnes []
  | cons {ds : List Nat} : AllOnes ds → AllOnes (1 :: ds)

theorem mass_ones {u : List Nat} (h : AllOnes u) : oddB (mass u) = false := by
  induction h with
  | nil => rfl
  | @cons ds _ ih =>
    simp only [mass]
    have h1 : 1 + 1 + mass ds = 1 + (1 + mass ds) := by omega
    rw [h1, odd_next, odd_next, Bool.not_not, ih]

def Tags (p : Bool) (b : Nat) (ds : List Nat) : Prop :=
  oddB ds.length = !(b == 0) ∧ oddB (mass ds + b) = p

def Head (p : Bool) (ds : List Nat) : Prop :=
  match ds with
  | [] => False
  | d :: _ => d = 1 ∨ (d = 2 ∧ p = false)

def Segment (p : Bool) (b : Nat) (ds : List Nat) : Prop :=
  Num p ds ∧ Head p ds ∧ Tags p b ds ∧
  7 + (if b == 0 then 1 else 0) ≤ ds.length

theorem num_end (p : Bool) {u : List Nat} (hu : IsBinary u)
    (h : AllOnes u → p = oddB u.length) :
    Num p (u ++ [2]) := by
  induction hu generalizing p with
  | nil =>
    have hp := h AllOnes.nil
    subst hp
    exact Num.two 0
  | @cons d ds hd hds ih =>
    rcases d with _ | _ | d
    · exact Num.zero p (ds ++ [2]) (tail_prefix hds (Tail.two 0))
    · refine Num.one p (ds ++ [2]) (ih (!p) ?_)
      intro hone
      have hp := h (AllOnes.cons hone)
      simp only [List.length_cons, odd_succ] at hp
      rw [hp, Bool.not_not]
    · omega

theorem num_last_tags (p : Bool) (b : Nat) {u : List Nat} (a : Nat)
    (hu : IsBinary u) (ha : a ≤ 1)
    (ht : Tags p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Num (!p) (u ++ [1 + a]) := by
  rcases ht with ⟨hlen, hsum⟩
  rcases a with _ | _ | a
  · exact num_binary (isBinary_append.mpr ⟨hu, IsBinary.cons (by omega) IsBinary.nil⟩) (!p)
  · refine num_end (!p) hu ?_
    intro hone
    rw [mass_app] at hsum
    simp only [mass] at hsum
    have hlen' : (u ++ [1]).length = u.length + 1 := by simp
    rw [hlen', odd_succ] at hlen
    have hmass1 : mass u + (1 + 1 + 0) + b = mass u + (2 + b) := by omega
    rw [hmass1, odd_add, mass_ones hone] at hsum
    rcases hb with rfl | rfl
    · simp only [Bool.false_xor] at hsum
      have ho2 : oddB 2 = false := rfl
      rw [ho2] at hsum
      subst hsum
      simpa using hlen.symm
    · simp only [Bool.false_xor] at hsum
      have ho5 : oddB 5 = true := rfl
      rw [ho5] at hsum
      subst hsum
      simpa using hlen.symm
  · omega

theorem odd_adjacent (x y : Nat) (h : x = 1 + y ∨ y = 1 + x) :
    oddB y = !(oddB x) := by
  rcases h with rfl | rfl
  · rw [odd_next, Bool.not_not]
  · rw [odd_next]

theorem tags_carry {p : Bool} {b : Nat} {u : List Nat} {a n : Nat}
    (ht : Tags p b (u ++ [a, 2] ++ List.replicate n 0)) :
    Tags (!p) b (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  rcases ht with ⟨hlen, hsum⟩
  refine ⟨?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    exact hlen
  · rw [← hsum]
    apply odd_adjacent
    left
    simp only [List.append_assoc, mass_app, mass]
    omega

theorem head_carry {p : Bool} {u : List Nat} {a n : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hnum : Num p (u ++ [a, 2] ++ List.replicate n 0))
    (hhead : Head p (u ++ [a, 2] ++ List.replicate n 0)) :
    Head (!p) (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  cases hu with
  | nil =>
    simp only [List.nil_append, List.cons_append, Head] at hnum hhead ⊢
    have ha1 : a = 1 := by rcases hhead with h | ⟨h, _⟩ <;> omega
    subst ha1
    right
    exact ⟨rfl, num_two (num_one hnum)⟩
  | @cons d ds hd _ =>
    simp only [List.cons_append, Head] at hhead ⊢
    left
    rcases hhead with h | ⟨h, _⟩ <;> omega

theorem segment_carry {p : Bool} {b : Nat} {u : List Nat} {a n : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hs : Segment p b (u ++ [a, 2] ++ List.replicate n 0)) :
    Segment (!p) b (u ++ [1 + a, 0] ++ List.replicate n 0) := by
  rcases hs with ⟨hn, hh, ht, hl⟩
  refine ⟨num_carry p a n hu ha hn, head_carry hu ha hn hh, tags_carry ht, ?_⟩
  simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
  exact hl

theorem tags_last {p : Bool} {b : Nat} {u : List Nat} {a : Nat}
    (ht : Tags p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Tags (!p) (b - 2) (u ++ [1 + a]) := by
  rcases ht with ⟨hlen, hsum⟩
  refine ⟨?_, ?_⟩
  · rcases hb with rfl | rfl <;> {
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
      exact hlen
    }
  · rw [← hsum]
    apply odd_adjacent
    rcases hb with rfl | rfl
    · right; simp only [mass_app, mass]; omega
    · left; simp only [mass_app, mass]; omega

theorem segment_last {p : Bool} {b : Nat} {u : List Nat} {a : Nat}
    (hu : IsBinary u) (ha : a ≤ 1)
    (hs : Segment p b (u ++ [a])) (hb : b = 0 ∨ b = 3) :
    Segment (!p) (b - 2) (u ++ [1 + a]) := by
  rcases hs with ⟨hn, hh, ht, hl⟩
  refine ⟨num_last_tags p b a hu ha ht hb, ?_, tags_last ht hb, ?_⟩
  · cases hu with
    | nil =>
      simp only [List.nil_append, List.length_singleton] at hl
      rcases hb with rfl | rfl <;> omega
    | @cons d ds hd _ =>
      simp only [List.cons_append, Head] at hh ⊢
      left
      rcases hh with h | ⟨h, _⟩ <;> omega
  · rcases hb with rfl | rfl <;> {
      simp only [List.length_append, List.length_cons, List.length_nil] at hl ⊢
      exact hl
    }

theorem head_binary {p : Bool} {ds : List Nat} (h : IsBinary ds) (hh : Head p ds) :
    Head true ds := by
  cases h with
  | nil => exact hh
  | @cons d ds hd _ =>
    simp only [Head] at hh ⊢
    left
    rcases hh with h1 | ⟨h2, _⟩ <;> omega

theorem head_any (p : Bool) {ds : List Nat} (hh : Head true ds) : Head p ds := by
  rcases ds with _ | ⟨d, ds⟩
  · exact hh
  · simp only [Head] at hh ⊢
    rcases hh with h1 | ⟨_, h2⟩
    · exact Or.inl h1
    · cases h2

def Block (p : Bool) (x : List Nat × Nat) : Prop :=
  IsBinary x.1 ∧ x.2 ≤ 1 ∧ Head true x.1 ∧
  Tags p (1 + x.2) x.1 ∧ 7 ≤ x.1.length

theorem block_length {p : Bool} {ds : List Nat} {n : Nat} (h : Block p (ds, n)) :
    7 ≤ ds.length := h.2.2.2.2

theorem scanned_block (p : Bool) (b : Nat) {ds : List Nat}
    (hs : Segment p b ds) (hu : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    Block p (ds, b - 1) := by
  rcases hs with ⟨_, hh, ⟨hlen, hsum⟩, hl⟩
  dsimp only [Block]
  rcases hb with rfl | rfl <;> {
    refine ⟨hu, by omega, head_binary hu hh, ⟨hlen, hsum⟩, by omega⟩
  }

theorem emitted_segment {p : Bool} {ds : List Nat} {n : Nat}
    (hb : Block p (ds, n)) : Segment (!p) (2 + n) ds := by
  dsimp only [Block] at hb
  rcases hb with ⟨hu, hn, hh, ⟨hlen, hsum⟩, hl⟩
  have h1 : (1 + n == 0) = false := by cases n <;> rfl
  have h2 : (2 + n == 0) = false := by cases n <;> rfl
  refine ⟨num_binary hu (!p), head_any (!p) hh, ⟨?_, ?_⟩, ?_⟩
  · rw [h1] at hlen
    rw [h2]
    exact hlen
  · rw [← hsum]
    apply odd_adjacent
    right
    omega
  · rw [h2]
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega

theorem tail_split {ds : List Nat} (ht : Tail ds) :
    IsBinary ds ∨ ∃ u n, IsBinary u ∧ ds = u ++ 2 :: List.replicate n 0 := by
  induction ht with
  | nil => exact Or.inl IsBinary.nil
  | zero ds _ ih =>
    rcases ih with hb | ⟨u, n, hu, rfl⟩
    · exact Or.inl (IsBinary.cons (by omega) hb)
    · exact Or.inr ⟨0 :: u, n, IsBinary.cons (by omega) hu, rfl⟩
  | one ds _ ih =>
    rcases ih with hb | ⟨u, n, hu, rfl⟩
    · exact Or.inl (IsBinary.cons (by omega) hb)
    · exact Or.inr ⟨1 :: u, n, IsBinary.cons (by omega) hu, rfl⟩
  | two n =>
    exact Or.inr ⟨[], n, IsBinary.nil, rfl⟩

inductive Carry : List Nat → Nat → List Nat → Nat → Prop where
  | inside (u : List Nat) (a n b : Nat) :
      IsBinary u → a ≤ 1 →
      Carry (u ++ [a, 2] ++ List.replicate n 0) b (u ++ [1 + a, 0] ++ List.replicate n 0) b
  | last (u : List Nat) (a b : Nat) :
      IsBinary u → a ≤ 1 → (b = 0 ∨ b = 3) →
      Carry (u ++ [a]) b (u ++ [1 + a]) (b - 2)

theorem carry_segment (p : Bool) {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hs : Segment p b ds) :
    Segment (!p) b' ds' := by
  cases hc with
  | inside u a n b hu ha => exact segment_carry hu ha hs
  | last u a b hu ha hb => exact segment_last hu ha hs hb

theorem carry_zero {ds ds' : List Nat} {b' : Nat} (hc : Carry ds 0 ds' b') : b' = 0 := by
  cases hc <;> rfl

theorem carry_header {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hb : 1 ≤ b ∧ b ≤ 3) : 1 ≤ b' ∧ b' ≤ 3 := by
  cases hc with
  | inside => exact hb
  | last _ _ _ _ _ hb' => omega

theorem list_snoc {α : Type*} (ds : List α) (hne : ds ≠ []) :
    ∃ u a, ds = u ++ [a] := by
  induction ds with
  | nil => contradiction
  | cons d ds ih =>
    rcases ds with _ | ⟨x, xs⟩
    · exact ⟨[], d, rfl⟩
    · rcases ih (by simp) with ⟨u, a, h⟩
      exact ⟨d :: u, a, by simp [h]⟩

theorem word_progress (b : Nat) (ds : List Nat)
    (ht : Tail ds) (hh : Head true ds) (hb : b ≤ 3) :
    (∃ ds' b', Carry ds b ds' b') ∨ (IsBinary ds ∧ (b = 1 ∨ b = 2)) := by
  rcases tail_split ht with hd | ⟨u, n, hu, rfl⟩
  · have hb' : (b = 0 ∨ b = 3) ∨ (b = 1 ∨ b = 2) := by omega
    rcases hb' with hb' | hb'
    · left
      have hne : ds ≠ [] := by rintro rfl; exact hh
      rcases list_snoc ds hne with ⟨u, a, rfl⟩
      rcases isBinary_append.mp hd with ⟨hu, ha1⟩
      cases ha1 with
      | cons ha _ => exact ⟨u ++ [1 + a], b - 2, Carry.last u a b hu ha hb'⟩
    · exact Or.inr ⟨hd, hb'⟩
  · left
    have hne : u ≠ [] := by
      rintro rfl
      simp only [List.nil_append, Head] at hh
      rcases hh with h | ⟨_, h⟩ <;> cases h
    rcases list_snoc u hne with ⟨v, a, rfl⟩
    rcases isBinary_append.mp hu with ⟨hv, ha1⟩
    cases ha1 with
    | cons ha _ =>
      have heq : (v ++ [a]) ++ 2 :: List.replicate n 0 = v ++ [a, 2] ++ List.replicate n 0 := by
        simp [List.append_assoc]
      rw [heq]
      exact ⟨v ++ [1 + a, 0] ++ List.replicate n 0, b, Carry.inside v a n b hv ha⟩

theorem record_progress (b : Nat) (ds : List Nat)
    (hs : Segment true b ds) (hb : b ≤ 3) :
    (∃ ds' b', Carry ds b ds' b') ∨ (IsBinary ds ∧ (b = 1 ∨ b = 2)) :=
  word_progress b ds (num_tail hs.1) hs.2.1 hb

theorem segment_progress (b : Nat) (ds : List Nat)
    (hs : Segment false b ds) (hb : b ≤ 3) :
    (∃ k, ds = 2 :: List.replicate k 0) ∨
    (∃ ds' b', Carry ds b ds' b') ∨
    (IsBinary ds ∧ (b = 1 ∨ b = 2)) := by
  rcases hs with ⟨hn, hh, _⟩
  rcases ds with _ | ⟨d, ds⟩
  · contradiction
  · rcases hh with rfl | ⟨rfl, _⟩
    · exact Or.inr (word_progress b (1 :: ds) (num_tail hn) (Or.inl rfl) hb)
    · left
      cases hn with
      | two k => exact ⟨k, rfl⟩

inductive Records where
  | REnd (ds : List Nat)
  | RMore (ds : List Nat) (b : Nat) (rs : Records)

open Records

def Good : Bool → Records → Prop
  | p, REnd ds => Segment p 0 ds
  | p, RMore ds b rs => Segment p b ds ∧ (1 ≤ b ∧ b ≤ 3) ∧ Good true rs

inductive Advance : Records → List (List Nat × Nat) → Records → Prop where
  | AEnd (ds ds' : List Nat) :
      Carry ds 0 ds' 0 → Advance (REnd ds) [] (REnd ds')
  | AStop (ds : List Nat) (b : Nat) (ds' : List Nat) (b' : Nat) (rs : Records) :
      0 < b → Carry ds b ds' b' →
      Advance (RMore ds b rs) [] (RMore ds' b' rs)
  | AGo (ds : List Nat) (b : Nat) (rs : Records) (bs : List (List Nat × Nat)) (rs' : Records) :
      IsBinary ds → (b = 1 ∨ b = 2) →
      Advance rs bs rs' →
      Advance (RMore ds b rs) ((ds, b - 1) :: bs) rs'

inductive AllBlocks (p : Bool) : List (List Nat × Nat) → Prop where
  | nil : AllBlocks p []
  | cons {x : List Nat × Nat} {bs : List (List Nat × Nat)} :
      Block p x → AllBlocks p bs → AllBlocks p (x :: bs)

theorem advance_total (rs : Records) (h : Good true rs) :
    ∃ bs rs', Advance rs bs rs' ∧ AllBlocks true bs ∧ Good false rs' := by
  induction rs with
  | REnd ds =>
    rcases record_progress 0 ds h (by omega) with ⟨ds', b', hc⟩ | ⟨_, hb⟩
    · have hb' := carry_zero hc
      subst hb'
      exact ⟨[], REnd ds', Advance.AEnd ds ds' hc, AllBlocks.nil, carry_segment true hc h⟩
    · omega
  | RMore ds b rs ih =>
    rcases h with ⟨hs, hb, hr⟩
    rcases record_progress b ds hs hb.2 with ⟨ds', b', hc⟩ | ⟨hd, hb12⟩
    · exact ⟨[], RMore ds' b' rs, Advance.AStop ds b ds' b' rs (by omega) hc,
        AllBlocks.nil, carry_segment true hc hs, carry_header hc hb, hr⟩
    · rcases ih hr with ⟨bs, rs', ha, hbs, hg⟩
      exact ⟨(ds, b - 1) :: bs, rs', Advance.AGo ds b rs bs rs' hd hb12 ha,
        AllBlocks.cons (scanned_block true b hs hd hb12) hbs, hg⟩

def measure (ds : List Nat) : Nat := prefix_value 7 (ds.map Nat.succ)

def first_digits : Records → List Nat
  | REnd ds => ds
  | RMore ds _ _ => ds

def protected_digits (bs : List (List Nat × Nat)) (rs : Records) : List Nat :=
  match bs with
  | [] => first_digits rs
  | (ds, _) :: _ => ds

theorem segment_length {p : Bool} {b : Nat} {ds : List Nat} (h : Segment p b ds) :
    7 ≤ ds.length := by
  have hl := h.2.2.2
  omega

theorem carry_bound {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hl : 7 ≤ ds.length) :
    measure ds' ≤ 1 + measure ds := by
  cases hc with
  | inside u a n b hu ha =>
    unfold measure
    simp only [List.map_append, List.map_cons, List.map_nil]
    have ha1 : (1 + a).succ = 1 + (a + 1) := by omega
    rw [ha1]
    have h := (prefix_carry 7 (u.map Nat.succ) (a + 1) ((List.replicate n 0).map Nat.succ)).2
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using h
  | last u a b hu ha hb =>
    unfold measure
    simp only [List.map_append, List.map_cons, List.map_nil]
    have ha1 : (1 + a).succ = 1 + (a + 1) := by omega
    rw [ha1]
    refine (prefix_last 7 (u.map Nat.succ) (a + 1) ?_).2
    simp only [List.length_append, List.length_singleton] at hl
    simp only [List.length_map]
    omega

theorem advance_bound {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (ha : Advance rs bs rs') (hg : Good true rs) :
    measure (protected_digits bs rs') ≤ 1 + measure (first_digits rs) := by
  cases ha with
  | AEnd ds ds' hc =>
    exact carry_bound hc (segment_length hg)
  | AStop ds b ds' b' rs _ hc =>
    exact carry_bound hc (segment_length hg.1)
  | AGo =>
    simp only [protected_digits, first_digits]
    omega

theorem carry_not_scan {ds : List Nat} {b : Nat} {ds' : List Nat} {b' : Nat}
    (hc : Carry ds b ds' b') (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) : False := by
  cases hc with
  | inside u a n b _ _ =>
    rcases isBinary_append.mp hd with ⟨hu2, _⟩
    rcases isBinary_append.mp hu2 with ⟨_, ha2⟩
    cases ha2 with
    | cons _ h2 =>
      cases h2 with
      | cons hbad _ => omega
  | last _ _ _ _ _ hb' => omega

theorem advance_go {ds : List Nat} {b : Nat} {rs : Records} {bs : List (List Nat × Nat)} {rs' :
    Records}
    (ha : Advance (RMore ds b rs) bs rs') (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ bs', bs = (ds, b - 1) :: bs' ∧ Advance rs bs' rs' := by
  cases ha with
  | AStop _ _ _ _ _ _ hc =>
    exact False.elim (carry_not_scan hc hd hb)
  | AGo _ _ _ bs' _ _ _ ha' =>
    exact ⟨bs', rfl, ha'⟩

def seed_offset : List Nat := [1, 1, 0, 1, 1, 0, 1]

theorem seed_binary : IsBinary seed_offset := by
  repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)

theorem seed_segment : Segment true 1 seed_offset := by
  refine ⟨num_binary seed_binary true, Or.inl rfl, ⟨by decide, by decide⟩, by decide⟩

theorem seed_measure : measure seed_offset = 236 := rfl

-- ============================================================================
-- Section 3: Record Chains, Cap Rules, Stack & Ready Progress (Others_v1.v:666-1510)
-- ============================================================================

theorem digits_app (u v : List Nat) : digits (u ++ v) = digits u ++ digits v := by
  unfold digits
  exact List.flatMap_append

theorem last7_snoc (b : Nat) {u : List Nat} (a : Nat) (l r : HalfTape)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((bit0 ^ b) +> ((bit1 ^ 7) +> (digits (u ++ [a]) +> ([0, 0, 0] +> r))))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((bit1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a]) +> ([0] +> r)))) := by
  have h_lhs : digits (u ++ [a]) +> ([0, 0, 0] +> r) =
      digits u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0, 0, 0] +> r)) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a]) +> ([0] +> r) =
      digits u +> ((bit0 ^ (2 + a)) +> ([1, 1, 0] +> r)) := by
    rw [digits_app]
    have h2a : 2 + a = 1 + (1 + a) := by omega
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil, h2a]
  rw [h_lhs, h_rhs]
  exact last7 b u a l r hb hu ha

theorem last7_inside (b : Nat) {u : List Nat} (a n : Nat) (l r : HalfTape)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((bit0 ^ b) +> ((bit1 ^ 7) +> (digits (u ++ [a,
        2] ++ List.replicate n 0) +> r)))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((bit1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r))) := by
  have h_lhs : digits (u ++ [a, 2] ++ List.replicate n 0) +> r =
      digits (u ++ [a]) +> ([0, 0, 0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, listPow_succ, listPow_zero, bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r =
      digits (u ++ [1 + a]) +> ([0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, listPow_succ, listPow_zero, bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs, h_rhs]
  exact last7_snoc b a l ([1, 1] +> (digits (List.replicate n 0) +> r)) hb hu ha

theorem last7_blank (b : Nat) {u : List Nat} (a : Nat) (l : HalfTape)
    (hb : b = 1 ∨ b = 2) (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l ((bit0 ^ b) +> ((bit1 ^ 7) +> (digits (u ++ [a]) +> default)))) [tm24]⊢⁺
      (stepCfg ([1] +> ([0] +> ((bit1 ^ (1 + b)) +> l)))
        ([0, 0, 1, 1, 1] +> (digits (u ++ [1 + a]) +> default))) := by
  have h := last7_snoc b a l default hb hu ha
  simpa only [append_cons, append_nil, zero_cons_default'] using h

def records_side : Records → HalfTape
  | REnd ds => digits ds +> default
  | RMore ds b rs => digits ds +> ((bit0 ^ b) +> ((bit1 ^ 7) +> records_side rs))

def record_stack (bs : List (List Nat × Nat)) (l : HalfTape) : HalfTape :=
  bs.foldl (fun l x => [0] +> ((bit1 ^ (2 + x.2)) +> pending x.1 ((bit0 ^ 5) +> l))) l

theorem advance_spec {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (ha : Advance rs bs rs') (h : Nat) (l : HalfTape) (hh : h = 1 ∨ h = 2) :
    (stepCfg l ((bit0 ^ h) +> ((bit1 ^ 7) +> records_side rs))) [tm24]⊢⁺
      (stepCfg ([1] +> record_stack bs ([0] +> ((bit1 ^ (1 + h)) +> l)))
        ([0, 0, 1, 1, 1] +> records_side rs')) := by
  induction ha generalizing h l with
  | AEnd ds ds' hc =>
    simp only [records_side, record_stack, List.foldl_nil]
    cases hc with
    | inside u a n _ hu ha => exact last7_inside h a n l default hh hu ha
    | last u a _ hu ha _ => exact last7_blank h a l hh hu ha
  | AStop ds b ds' b' rs hbpos hc =>
    simp only [records_side, record_stack, List.foldl_nil]
    cases hc with
    | inside u a n _ hu ha =>
      exact last7_inside h a n l ((bit0 ^ b) +> ((bit1 ^ 7) +> records_side rs)) hh hu ha
    | last u a _ hu ha hb03 =>
      have hb3 : b = 3 := by omega
      subst hb3
      exact last7_snoc h a l ((bit1 ^ 7) +> records_side rs) hh hu ha
  | AGo ds b rs bs rs' hd hb12 _ ih =>
    simp only [records_side, record_stack, List.foldl_cons]
    refine stepPlus_of_step (scan_seven hh l (digits ds +> ((bit0 ^ b) +> ((bit1 ^ 7) +>
        records_side rs)))) ?_
    refine stepPlus_of_step (scan_digits hd ((bit0 ^ 6) +> ((bit1 ^ (1 + h)) +> l)) ((bit0 ^ b) +>
        ((bit1 ^ 7) +> records_side rs))) ?_
    have hstep := ih b (pending ds ((bit0 ^ 6) +> ((bit1 ^ (1 + h)) +> l))) hb12
    have h6 : (bit0 ^ 6) +> ((bit1 ^ (1 + h)) +> l) = (bit0 ^ 5) +> ([0] +> ((bit1 ^ (1 + h)) +>
        l)) := by
      simp [listPow_succ, bit0]
    have hb2 : 2 + (b - 1) = 1 + b := by omega
    rw [h6] at hstep
    rw [hb2]
    exact hstep

theorem reset_rule {rs : Records} (hr : Good true rs) :
    ∃ bs rs', AllBlocks true ((seed_offset, 0) :: bs) ∧ Good false rs' ∧
      (cap_entry [2, 2, 1, 2, 2, 1, 1] 3 (records_side rs)) [tm24]⊢⁺
        (stepCfg ([1] +> record_stack ((seed_offset, 0) :: bs) (put_left [4] default))
          ([0, 0, 1, 1, 1] +> records_side rs')) := by
  have hg : Good true (RMore seed_offset 1 rs) := ⟨seed_segment, ⟨by omega, by omega⟩, hr⟩
  rcases advance_total (RMore seed_offset 1 rs) hg with ⟨bs, rs', ha, hb, hg'⟩
  rcases advance_go ha seed_binary (Or.inl rfl) with ⟨bs', rfl, _⟩
  refine ⟨bs', rs', hb, hg', ?_⟩
  refine stepStar_trans' (bridge3 (records_side rs)) ?_
  exact advance_spec ha 2 ([1] +> default) (Or.inr rfl)

inductive Cap where
  | C0
  | C1
  | C2
  | C3
  deriving DecidableEq

open Cap

def cap_word : Cap → List Nat
  | C0 => [4]
  | C1 => [3, 3, 3]
  | C2 => [4, 3, 3, 2, 2, 2]
  | C3 => [3, 3, 2, 3, 3, 2, 2, 3]

def cap_prefix : Cap → List Nat
  | C0 => []
  | C1 => [2, 2]
  | C2 => [3, 2, 2, 1, 1]
  | C3 => [2, 2, 1, 2, 2, 1, 1]

def cap_height : Cap → Nat
  | C0 => 4
  | C1 => 3
  | C2 => 2
  | C3 => 3

def cap_bound : Cap → Nat
  | C0 => 236
  | C1 => 238
  | C2 => 240
  | C3 => 242

def next_cap : Cap → Cap
  | C0 => C1
  | C1 => C2
  | C2 => C3
  | C3 => C0

theorem cap_prefix_spec (c : Cap) {rs : Records} {bs : List (List Nat × Nat)} {rs' : Records}
    (hc : c ≠ C3) (ha : Advance rs bs rs') :
    (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺
      (stepCfg ([1] +> record_stack bs (put_left (cap_word (next_cap c)) default))
        ([0, 0, 1, 1, 1] +> records_side rs')) := by
  cases c with
  | C0 =>
    refine stepStar_trans' (bridge0 (records_side rs)) ?_
    have hb1 : IsBinary [1] := IsBinary.cons (by decide) IsBinary.nil
    refine stepPlus_of_step (scan_digits hb1 (put_left [3] default) ([0,
        0] +> ((bit1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 2 (pending [1] (put_left [3] default)) (Or.inr rfl)
  | C1 =>
    refine stepStar_trans' (bridge1 (records_side rs)) ?_
    have hb100 : IsBinary [1, 0, 0] :=
      IsBinary.cons (by decide) (IsBinary.cons (by decide) (IsBinary.cons (by decide) IsBinary.nil))
    refine stepPlus_of_step (scan_digits hb100 (put_left [4,
        3] default) ([0] +> ((bit1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 1 (pending [1, 0, 0] (put_left [4, 3] default)) (Or.inl rfl)
  | C2 =>
    refine stepStar_trans' (bridge2 (records_side rs)) ?_
    have hb101100 : IsBinary [1, 0, 1, 1, 0, 0] := by
      repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)
    refine stepPlus_of_step (scan_digits hb101100 (put_left [3] default) ([0,
        0] +> ((bit1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 2 (pending [1, 0, 1, 1, 0, 0] (put_left [3] default)) (Or.inr rfl)
  | C3 => contradiction

theorem cap_rule (c : Cap) {rs : Records}
    (hg : Good true rs) (hm : measure (first_digits rs) ≤ 1 + cap_bound c) :
    ∃ bs rs', AllBlocks true bs ∧ Good false rs' ∧
      measure (protected_digits bs rs') ≤ cap_bound (next_cap c) ∧
      (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺
        (stepCfg ([1] +> record_stack bs (put_left (cap_word (next_cap c)) default))
          ([0, 0, 1, 1, 1] +> records_side rs')) := by
  cases c with
  | C0 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega,
        cap_prefix_spec C0 (by decide) ha⟩
  | C1 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega,
        cap_prefix_spec C1 (by decide) ha⟩
  | C2 =>
    rcases advance_total rs hg with ⟨bs, rs', ha, hb, hr⟩
    have hmb := advance_bound ha hg
    exact ⟨bs, rs', hb, hr, by simp [cap_bound, next_cap] at hm ⊢; omega,
        cap_prefix_spec C2 (by decide) ha⟩
  | C3 =>
    rcases reset_rule hg with ⟨bs, rs', hb, hr, hs⟩
    refine ⟨(seed_offset, 0) :: bs, rs', hb, hr, ?_, hs⟩
    simp only [protected_digits, cap_bound, next_cap, seed_measure, le_refl]

theorem records_zero {p : Bool} {rs : Records} (h : Good p rs) :
    ∃ r, records_side rs = [0] +> r := by
  cases rs with
  | REnd ds =>
    rcases ds with _ | ⟨d, ds⟩
    · exact False.elim h.2.1
    · refine ⟨((bit0 ^ d) ++ [1, 1] ++ digits ds) +> default, ?_⟩
      simp only [records_side, digits_cons, listPow_succ', bit0, List.cons_append, List.nil_append,
          append_cons, append_nil, append_assoc]
  | RMore ds b rs =>
    rcases ds with _ | ⟨d, ds⟩
    · exact False.elim h.1.2.1
    · refine ⟨((bit0 ^ d) ++ [1,
        1] ++ digits ds) +> ((bit0 ^ b) +> ((bit1 ^ 7) +> records_side rs)), ?_⟩
      simp only [records_side, digits_cons, listPow_succ', bit0, List.cons_append, List.nil_append,
          append_cons, append_nil, append_assoc]

theorem return_separator (l r : HalfTape) (hr : ∃ r', r = [0] +> r') :
    (returnCfg ([0, 0] +> ((bit1 ^ 4) +> l)) r) [tm24]⊢*
      (l <{{A}} ((bit1 ^ 8) +> r)) := by
  rcases hr with ⟨r', rfl⟩
  exact close2 l r'

theorem return_six (l r : HalfTape) (hr : ∃ r', r = [0] +> r') :
    (returnCfg ((bit0 ^ 6) +> l) r) [tm24]⊢*
      (stepCfg ([1] +> ([0] +> l)) ([0, 0, 1, 1, 1] +> r)) := by
  rcases hr with ⟨r', rfl⟩
  exact close6 l r'

theorem emit_block (ds : List Nat) (n : Nat) (l r : HalfTape) :
    (([0] +> ((bit1 ^ (2 + n)) +> pending ds l)) <{{A}} ((bit1 ^ 8) +> r)) [tm24]⊢*
      (returnCfg l (digits ds +> ((bit0 ^ (2 + n)) +> ((bit1 ^ 7) +> r)))) := by
  refine stepPlus_trans' (block_back ds n l r) ?_
  unfold backCfg returnCfg
  have h1 : ([0, 0, 0] : BitWord) +> (back_word ds +> ((bit0 ^ (1 + n)) +> ((bit1 ^ 7) +> r))) =
      [0, 0] +> ([0] +> (back_word ds +> ((bit0 ^ (1 + n)) +> ((bit1 ^ 7) +> r)))) := rfl
  have h2n : 2 + n = 1 + (1 + n) := by omega
  rw [h1, zero_back_word, h2n, step_left_default bit0 (1 + n) ((bit1 ^ 7) +> r)]


inductive Stack where
  | SCap (c : Cap)
  | SPush (six : Bool) (older : Stack) (ds : List Nat) (n : Nat)

open Stack

def stack_good : Stack → Prop
  | SCap _ => True
  | SPush six older ds n => stack_good older ∧ Block six (ds, n)

def stack_side : Stack → HalfTape
  | SCap c => put_left (cap_word c) default
  | SPush six older ds n =>
      [0] +> ((bit1 ^ (2 + n)) +> pending ds
        (if six then (bit0 ^ 5) +> stack_side older
         else [0, 0] +> ((bit1 ^ 4) +> stack_side older)))

def stack_cap : Stack → Cap
  | SCap c => c
  | SPush _ older _ _ => stack_cap older

def stack_protected : Stack → List Nat → List Nat
  | SCap _, ds => ds
  | SPush _ older pfx _, _ => stack_protected older pfx

theorem stack_zero (st : Stack) : ∃ l, stack_side st = [0] +> l := by
  rcases st with ⟨_ | _ | _ | _⟩ | ⟨six, older, ds, n⟩ <;> {
    dsimp only [stack_side, cap_word, put_left, List.foldl]
    exact ⟨_, rfl⟩
  }

def active (st : Stack) (rs : Records) : Cfg (Fin 2) (Fin 6) :=
  stepCfg ([1] +> stack_side st) ([0, 0, 1, 1, 1] +> records_side rs)

def restored : Stack → Records → Cfg (Fin 2) (Fin 6)
  | SCap c, rs => cap_entry (cap_prefix c) (cap_height c) (records_side rs)
  | SPush true older ds n, rs => active older (RMore ds (2 + n) rs)
  | SPush false older ds n, rs => restored older (RMore ds (2 + n) rs)

theorem emitted_good (p : Bool) {ds : List Nat} {n : Nat} {rs : Records}
    (hb : Block p (ds, n)) (hr : Good true rs) :
    Good (!p) (RMore ds (2 + n) rs) := by
  refine ⟨emitted_segment hb, ⟨by omega, ?_⟩, hr⟩
  have hn := hb.2.1
  dsimp only at hn
  omega

theorem cap_emit (c : Cap) (r : HalfTape) :
    ((put_left (cap_word c) default) <{{A}} ((bit1 ^ 8) +> r)) [tm24]⊢*
      (cap_entry (cap_prefix c) (cap_height c) r) := by
  cases c <;> {
    unfold put_left cap_word cap_entry cap_prefix cap_height root stepCfg payload
    simp only [List.foldl_cons, List.foldl_nil, List.flatMap_cons, List.flatMap_nil,
      listPow_succ, listPow_zero, bit0, bit1,
      List.cons_append, List.nil_append, List.append_nil, append_cons, append_nil]
    execute
  }

theorem stack_return (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs) :
    ((stack_side st) <{{A}} ((bit1 ^ 8) +> records_side rs)) [tm24]⊢* (restored st rs) := by
  induction st generalizing rs with
  | SCap c => exact cap_emit c (records_side rs)
  | SPush six older ds n ih =>
    rcases hl with ⟨hl', hb⟩
    rcases six with _ | _
    · simp only [stack_side, restored]
      refine stepPlus_trans' (emit_block ds n ([0,
          0] +> ((bit1 ^ 4) +> stack_side older)) (records_side rs)) ?_
      have hg' := emitted_good false hb hr
      refine stepPlus_trans' (return_separator (stack_side older) (records_side (RMore ds (2 + n)
          rs)) (records_zero hg')) ?_
      exact ih (RMore ds (2 + n) rs) hl' hg'
    · simp only [stack_side, restored, ↓reduceIte]
      refine stepPlus_trans' (emit_block ds n ((bit0 ^ 5) +> stack_side older) (records_side rs)) ?_
      have hg' := emitted_good true hb hr
      rcases stack_zero older with ⟨l, hst⟩
      unfold active
      rw [hst]
      have h6 : (bit0 ^ 5) +> ([0] +> l) = (bit0 ^ 6) +> l := by
        simp [listPow_succ, bit0]
      rw [h6]
      exact return_six l (records_side (RMore ds (2 + n) rs)) (records_zero hg')

theorem restored_good (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs) :
    (∃ st' rs', restored st rs = active st' rs' ∧
      stack_good st' ∧ Good false rs' ∧ stack_cap st' = stack_cap st ∧
      stack_protected st' (first_digits rs') = stack_protected st (first_digits rs)) ∨
    (∃ rs', restored st rs =
      cap_entry (cap_prefix (stack_cap st)) (cap_height (stack_cap st)) (records_side rs') ∧
      Good true rs' ∧ first_digits rs' = stack_protected st (first_digits rs)) := by
  induction st generalizing rs with
  | SCap c =>
    exact Or.inr ⟨rs, rfl, hr, rfl⟩
  | SPush six older ds n ih =>
    rcases hl with ⟨hl', hb⟩
    rcases six with _ | _
    · exact ih (RMore ds (2 + n) rs) hl' (emitted_good false hb hr)
    · exact Or.inl ⟨older, RMore ds (2 + n) rs, rfl, hl', emitted_good true hb hr, rfl, rfl⟩

theorem carry_word {u : List Nat} (a : Nat) (l r : HalfTape)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a]) +> ([0, 0, 0] +> r))) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> ([0] +> r))) := by
  have h_lhs : digits (u ++ [a]) +> ([0, 0, 0] +> r) =
      digits u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0, 0, 0] +> r)) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs]
  have h1 := ordinary_return hu ha l r
  refine step_right_default h1 ?_
  unfold backCfg returnCfg
  have h2 : ([0, 0, 0] : BitWord) +> (back_word u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      [0, 0] +> ([0] +> (back_word u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r)))) := rfl
  have h_rhs : digits u +> ([0] +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      digits (u ++ [1 + a]) +> ([0] +> r) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, listPow_succ', bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h2, zero_back_word, h_rhs]


theorem carry_inside {u : List Nat} (a n : Nat) (l r : HalfTape)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a, 2] ++ List.replicate n 0) +> r)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r)) := by
  have h_lhs : digits (u ++ [a, 2] ++ List.replicate n 0) +> r =
      digits (u ++ [a]) +> ([0, 0, 0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, listPow_succ, listPow_zero, bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  have h_rhs : digits (u ++ [1 + a, 0] ++ List.replicate n 0) +> r =
      digits (u ++ [1 + a]) +> ([0] +> ([1, 1] +> (digits (List.replicate n 0) +> r))) := by
    simp only [digits_app, digits_cons, digits_nil, listPow_succ, listPow_zero, bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h_lhs, h_rhs]
  exact carry_word a l ([1, 1] +> (digits (List.replicate n 0) +> r)) hu ha

theorem carry_blank {u : List Nat} (a : Nat) (l : HalfTape)
    (hu : IsBinary u) (ha : a ≤ 1) :
    (stepCfg l (digits (u ++ [a]) +> default)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> default)) := by
  have h := carry_word a l default hu ha
  simpa only [append_cons, append_nil, zero_cons_default'] using h

theorem carry_records_spec {rs rs' : Records} (ha : Advance rs [] rs') (l : HalfTape) :
    (stepCfg l (records_side rs)) [tm24]⊢⁺ (returnCfg l (records_side rs')) := by
  cases ha with
  | AEnd ds ds' hc =>
    simp only [records_side]
    cases hc with
    | inside u a n _ hu ha => exact carry_inside a n l default hu ha
    | last u a _ hu ha _ => exact carry_blank a l hu ha
  | AStop ds b ds' b' tail _ hc =>
    simp only [records_side]
    cases hc with
    | inside u a n _ hu ha =>
      exact carry_inside a n l ((bit0 ^ b) +> ((bit1 ^ 7) +> records_side tail)) hu ha
    | last u a _ hu ha hb03 =>
      have hb3 : b = 3 := by omega
      subst hb3
      exact carry_word a l ((bit1 ^ 7) +> records_side tail) hu ha

theorem carry_records_good (p : Bool) {rs rs' : Records}
    (ha : Advance rs [] rs') (hg : Good p rs) : Good (!p) rs' := by
  cases ha with
  | AEnd ds ds' hc => exact carry_segment p hc hg
  | AStop ds b ds' b' tail _ hc =>
    rcases hg with ⟨hs, hb, hr⟩
    exact ⟨carry_segment p hc hs, carry_header hc hb, hr⟩

theorem active_return {st : Stack} {rs rs' : Records}
    (hl : stack_good st) (hr : Good false rs) (ha : Advance rs [] rs') :
    (active st rs) [tm24]⊢⁺ (restored st rs') := by
  have hg : Good true rs' := carry_records_good false ha hr
  unfold active
  refine stepPlus_of_step (active_scan (stack_side st) (records_side rs)) ?_
  refine step_right_default (carry_records_spec ha ([0, 0] +> ((bit1 ^ 4) +> stack_side st))) ?_
  refine stepPlus_trans' (return_separator (stack_side st) (records_side rs') (records_zero hg)) ?_
  exact stack_return st rs' hl hg

def extend_stack (bs : List (List Nat × Nat)) (st : Stack) : Stack :=
  bs.foldl (fun st x => SPush true st x.1 x.2) st

@[simp] theorem record_stack_nil (l : HalfTape) : record_stack [] l = l := rfl
@[simp] theorem record_stack_cons (x : List Nat × Nat) (bs : List (List Nat × Nat)) (l : HalfTape) :
    record_stack (x :: bs) l =
      record_stack bs ([0] +> ((bit1 ^ (2 + x.2)) +> pending x.1 ((bit0 ^ 5) +> l))) := rfl
@[simp] theorem extend_stack_nil (st : Stack) : extend_stack [] st = st := rfl
@[simp] theorem extend_stack_cons (x : List Nat × Nat) (bs : List (List Nat × Nat)) (st : Stack) :
    extend_stack (x :: bs) st = extend_stack bs (SPush true st x.1 x.2) := rfl

theorem extend_side (bs : List (List Nat × Nat)) (st : Stack) :
    stack_side (extend_stack bs st) = record_stack bs (stack_side st) := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih =>
    rw [extend_stack_cons, record_stack_cons, ih (SPush true st x.1 x.2)]
    rfl

theorem extend_good {bs : List (List Nat × Nat)} {st : Stack}
    (hb : AllBlocks true bs) (hl : stack_good st) :
    stack_good (extend_stack bs st) := by
  induction hb generalizing st with
  | nil => exact hl
  | @cons x bs hbx _ ih => exact ih ⟨hl, hbx⟩

theorem extend_cap (bs : List (List Nat × Nat)) (st : Stack) :
    stack_cap (extend_stack bs st) = stack_cap st := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih => exact ih (SPush true st x.1 x.2)

theorem extend_protected (bs : List (List Nat × Nat)) (st : Stack) (rs : Records) :
    stack_protected (extend_stack bs st) (first_digits rs) =
    stack_protected st (protected_digits bs rs) := by
  induction bs generalizing st with
  | nil => rfl
  | cons x bs ih => exact ih (SPush true st x.1 x.2)

theorem active_constructor {st : Stack} {ds : List Nat} {b : Nat} {rs : Records}
    (hl : stack_good st) (hs : Segment false b ds) (hr : Good true rs)
    (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ st' rs', stack_good st' ∧ Good false rs' ∧
      stack_cap st' = stack_cap st ∧
      stack_protected st' (first_digits rs') = stack_protected st ds ∧
      (active st (RMore ds b rs)) [tm24]⊢⁺ (active st' rs') := by
  rcases advance_total rs hr with ⟨bs, rs', ha, hbs, hg⟩
  refine ⟨extend_stack bs (SPush false st ds (b - 1)), rs',
    extend_good hbs ⟨hl, scanned_block false b hs hd hb⟩, hg,
    extend_cap bs (SPush false st ds (b - 1)),
    extend_protected bs (SPush false st ds (b - 1)) rs', ?_⟩
  unfold active
  rw [extend_side]
  simp only [records_side, stack_side]
  refine stepPlus_of_step (active_scan (stack_side st) (digits ds +> ((bit0 ^ b) +> ((bit1 ^ 7) +>
      records_side rs)))) ?_
  refine stepPlus_of_step (scan_digits hd ([0,
      0] +> ((bit1 ^ 4) +> stack_side st)) ((bit0 ^ b) +> ((bit1 ^ 7) +> records_side rs))) ?_
  have hstep := advance_spec ha b (pending ds ([0, 0] +> ((bit1 ^ 4) +> stack_side st))) hb
  have hb2 : 2 + (b - 1) = 1 + b := by omega
  rw [hb2]
  exact hstep

def Source (st : Stack) (rs : Records) : Prop :=
  stack_good st ∧ Good false rs ∧
  measure (stack_protected st (first_digits rs)) ≤ cap_bound (stack_cap st)

theorem prefix_app (n : Nat) (u v : List Nat) (h : n ≤ u.length) :
    prefix_value n (u ++ v) = prefix_value n u := by
  induction u generalizing n with
  | nil =>
    have hn : n = 0 := by simpa using h
    subst hn
    rfl
  | cons d u ih =>
    rcases n with _ | k
    · rfl
    · simp only [List.length_cons] at h
      simp only [List.cons_append, prefix_value, ih k (by omega)]

theorem measure_app (u v : List Nat) (h : 7 ≤ u.length) :
    measure (u ++ v) = measure u := by
  unfold measure
  rw [List.map_append]
  exact prefix_app 7 (u.map Nat.succ) (v.map Nat.succ) (by simpa using h)

theorem long_measure (k : Nat) (hk : 6 ≤ k) :
    measure (2 :: List.replicate k 0) = 255 := by
  have hk' : k = 6 + (k - 6) := by omega
  rw [hk', List.replicate_add, ← List.cons_append]
  rw [measure_app (2 :: List.replicate 6 0) (List.replicate (k - 6) 0) (by decide)]
  rfl

theorem long_segment (b k : Nat) (hs : Segment false b (2 :: List.replicate k 0)) (hb : b ≤ 3) :
    (b = 0 ∧ oddB k = true) ∨ ((b = 1 ∨ b = 3) ∧ oddB k = false) := by
  rcases hs with ⟨_, _, ⟨hl, hm⟩, _⟩
  simp only [List.length_cons, List.length_replicate, mass, mass_zeros] at hl hm
  rw [odd_succ] at hl
  have hm' : 1 + 2 + k + b = k + (3 + b) := by omega
  rw [hm', odd_add] at hm
  rcases b with _ | _ | _ | _ | b
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · cases hodd : oddB k <;> simp_all [oddB]
  · omega

theorem source_long_marked (st : Stack) (b k : Nat)
    (hs : Segment false b (2 :: List.replicate k 0))
    (hm : measure (stack_protected st (2 :: List.replicate k 0)) ≤ cap_bound (stack_cap st)) :
    ∃ six older ds n, st = SPush six older ds n := by
  rcases st with ⟨c⟩ | ⟨six, older, ds, n⟩
  · have hl := segment_length hs
    simp only [List.length_cons, List.length_replicate] at hl
    simp only [stack_protected, stack_cap] at hm
    rw [long_measure k (by omega)] at hm
    cases c <;> simp [cap_bound] at hm
  · exact ⟨six, older, ds, n, rfl⟩

def merged (ds : List Nat) (n k : Nat) : List Nat :=
  ds ++ [n, 1, 1, 0] ++ List.replicate k 0

theorem merged_succ (ds : List Nat) (n k : Nat) :
    merged ds n (1 + k) = merged ds n k ++ [0] := by
  unfold merged
  have hk : 1 + k = k + 1 := by omega
  rw [hk, List.replicate_add]
  simp [List.append_assoc]

theorem zeros_binary (k : Nat) : IsBinary (List.replicate k 0) := by
  induction k with
  | zero => exact IsBinary.nil
  | succ k ih => exact IsBinary.cons (by omega) ih

theorem merged_binary {ds : List Nat} {n : Nat} (k : Nat)
    (hd : IsBinary ds) (hn : n ≤ 1) : IsBinary (merged ds n k) := by
  unfold merged
  refine isBinary_append.mpr ⟨isBinary_append.mpr ⟨hd, ?_⟩, zeros_binary k⟩
  exact IsBinary.cons hn (IsBinary.cons (by decide) (IsBinary.cons (by decide) (IsBinary.cons (by
      decide) IsBinary.nil)))

theorem merged_length (ds : List Nat) (n k : Nat) :
    (merged ds n k).length = ds.length + 4 + k := by
  unfold merged
  simp only [List.length_append, List.length_cons, List.length_nil, List.length_replicate]

theorem merged_mass (ds : List Nat) (n k : Nat) :
    mass (merged ds n k) = mass ds + 6 + n + k := by
  unfold merged
  rw [mass_app, mass_app, mass_zeros]
  simp only [mass]
  omega

theorem merged_segment (p : Bool) {ds : List Nat} {n : Nat} (b k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false b (2 :: List.replicate k 0)) :
    Segment p b (merged ds n k) := by
  dsimp only [Block] at hb
  rcases hb with ⟨hd, hn, hh, ⟨hl, hm⟩, hmin⟩
  rcases hs with ⟨_, _, ⟨hk, hsum⟩, _⟩
  have h1 : (1 + n == 0) = false := by cases n <;> rfl
  rw [h1] at hl
  simp only [List.length_cons, List.length_replicate, mass, mass_zeros] at hk hsum
  refine ⟨num_binary (merged_binary k hd hn) p, ?_, ⟨?_, ?_⟩, ?_⟩
  · rcases ds with _ | ⟨d, ds⟩
    · exact False.elim hh
    · simp only [Head, merged, List.cons_append] at hh ⊢
      rcases hh with h | ⟨_, h⟩
      · exact Or.inl h
      · cases h
  · rw [merged_length]
    have hlen_eq : ds.length + 4 + k = k + (1 + (1 + (1 + (1 + ds.length)))) := by omega
    rw [hlen_eq, odd_add, odd_next, odd_next, odd_next, odd_next, Bool.not_not, Bool.not_not, hl]
    have h2 : (!false) = true := rfl
    rw [h2, Bool.xor_true]
    rw [odd_succ] at hk
    exact hk
  · have hmass_eq : mass (merged ds n k) + b = (mass ds + (1 + n)) + (1 + (1 + (1 + 2 + k + b))) :=
      by
      rw [merged_mass]; omega
    rw [hmass_eq, odd_add, hm, odd_next, odd_next, Bool.not_not, hsum, Bool.xor_false]
  · rw [merged_length]
    cases (b == 0) <;> { simp only [Bool.false_eq_true, ↓reduceIte]; omega }

theorem merged_block (p : Bool) {ds : List Nat} {n : Nat} (k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false 1 (2 :: List.replicate k 0)) :
    Block p (merged ds n k, 0) :=
  scanned_block p 1 (merged_segment p 1 k hb hs) (merged_binary k hb.1 hb.2.1) (Or.inl rfl)

theorem merged_bump_segment (p : Bool) {ds : List Nat} {n : Nat} (b k : Nat)
    (hb : Block p (ds, n)) (hs : Segment false b (2 :: List.replicate (1 + k) 0))
    (hb03 : b = 0 ∨ b = 3) :
    Segment (!p) (b - 2) (merged ds n k ++ [1]) := by
  have hs' := merged_segment p b (1 + k) hb hs
  rw [merged_succ] at hs'
  exact segment_last (merged_binary k hb.1 hb.2.1) (by omega) hs' hb03

theorem stack_measure (st : Stack) {u v : List Nat} (h : measure u = measure v) :
    measure (stack_protected st u) = measure (stack_protected st v) := by
  cases st <;> simp [stack_protected, h]

theorem merged_measure (ds : List Nat) (n k : Nat) (h : 7 ≤ ds.length) :
    measure (merged ds n k) = measure ds := by
  unfold merged
  rw [List.append_assoc]
  exact measure_app ds ([n, 1, 1, 0] ++ List.replicate k 0) h

theorem bumped_measure (ds : List Nat) (n k : Nat) (h : 7 ≤ ds.length) :
    measure (merged ds n k ++ [1]) = measure ds := by
  unfold merged
  simp only [List.append_assoc]
  exact measure_app ds ([n, 1, 1, 0] ++ (List.replicate k 0 ++ [1])) h


theorem initial_source : Source (SCap C0) (REnd (seed_offset ++ [1])) := by
  have hbin : IsBinary (seed_offset ++ [1]) := by
    unfold seed_offset
    repeat (first | exact IsBinary.nil | refine IsBinary.cons (by decide) ?_)
  refine ⟨trivial, ⟨num_binary hbin false, Or.inl rfl, ⟨by decide, by decide⟩, by decide⟩,
      by decide⟩


theorem pending_app (u v : List Nat) (l : HalfTape) :
    pending (u ++ v) l = pending v (pending u l) := by
  unfold pending
  exact List.foldl_append

theorem merged_pending (ds : List Nat) (n k : Nat) (l : HalfTape) :
    pending (merged ds n k) l =
    pending ([1, 0] ++ List.replicate k 0)
      ([0] +> ((bit1 ^ 3) +> ([0] +> ((bit1 ^ (2 + n)) +> pending ds l)))) := by
  unfold merged
  rw [pending_app, pending_app, pending_app]
  simp only [pending_cons, pending_nil]

theorem long_scan (k : Nat) (l r : HalfTape) :
    (stepCfg ([1] +> l) ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate k 0) +> r))) [tm24]⊢⁺
      (stepCfg (pending ([1, 0] ++ List.replicate k 0) ([0] +> ((bit1 ^ 3) +> l))) r) := by
  have hd : ([0, 0, 1, 1, 1] : BitWord) +> (digits (2 :: List.replicate k 0) +> r) =
      [0, 0, 1, 1, 1, 0, 0, 0] +> ([1, 1] +> (digits (List.replicate k 0) +> r)) := by
    simp only [digits_cons, listPow_succ, listPow_zero, bit0, List.cons_append, List.nil_append]
    rfl
  rw [hd]
  refine step_right_default (active_turn l ([1, 1] +> (digits (List.replicate k 0) +> r))) ?_
  have hd2 : ([0, 0, 1, 1, 0] : BitWord) +> ([1, 1] +> (digits (List.replicate k 0) +> r)) =
      digits ([1, 0] ++ List.replicate k 0) +> r := by
    simp only [List.cons_append, List.nil_append, digits_cons, listPow_succ, listPow_zero, bit0]
    rfl
  rw [hd2]
  have hbin : IsBinary ([1, 0] ++ List.replicate k 0) :=
    IsBinary.cons (by decide) (IsBinary.cons (by decide) (zeros_binary k))
  exact scan_digits hbin ([0] +> ((bit1 ^ 3) +> l)) r

theorem long_pending (ds : List Nat) (n k : Nat) (l r : HalfTape) :
    (stepCfg ([1] +> ([0] +> ((bit1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate k 0) +> r))) [tm24]⊢⁺
      (stepCfg (pending (merged ds n k) l) r) := by
  rw [merged_pending]
  exact long_scan k ([0] +> ((bit1 ^ (2 + n)) +> pending ds l)) r

theorem pending_carry (u : List Nat) (a : Nat) (l r : HalfTape) :
    (stepCfg (pending (u ++ [a]) l) ([0, 0, 0] +> r)) [tm24]⊢⁺
      (returnCfg l (digits (u ++ [1 + a]) +> ([0] +> r))) := by
  rw [pending_app]
  simp only [pending_cons, pending_nil]
  refine step_right_default (start_back a (pending u l) r) ?_
  refine stepPlus_trans' (pending_back u l ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r))) ?_
  unfold backCfg returnCfg
  have h1 : ([0, 0, 0] : BitWord) +> (back_word u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      [0, 0] +> ([0] +> (back_word u +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r)))) := rfl
  have h_rhs : digits u +> ([0] +> ((bit0 ^ (1 + a)) +> ([1, 1, 0] +> r))) =
      digits (u ++ [1 + a]) +> ([0] +> r) := by
    rw [digits_app]
    simp only [digits_cons, digits_nil, listPow_succ', bit0,
      List.cons_append, List.nil_append, List.append_nil, append_assoc, append_cons, append_nil]
  rw [h1, zero_back_word, h_rhs]


theorem long_pending_return (ds : List Nat) (n k : Nat) (l r : HalfTape) :
    (stepCfg ([1] +> ([0] +> ((bit1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate (1 + k) 0) +> ([0, 0, 0] +> r)))) [tm24]⊢⁺
      (returnCfg l (digits (merged ds n k ++ [1]) +> ([0] +> r))) := by
  refine stepStar_trans' (long_pending ds n (1 + k) l ([0, 0, 0] +> r)) ?_
  rw [merged_succ]
  exact pending_carry (merged ds n k) 0 l r

theorem long_pending_blank (ds : List Nat) (n k : Nat) (l : HalfTape) :
    (stepCfg ([1] +> ([0] +> ((bit1 ^ (2 + n)) +> pending ds l)))
      ([0, 0, 1, 1, 1] +> (digits (2 :: List.replicate (1 + k) 0) +> default))) [tm24]⊢⁺
      (returnCfg l (digits (merged ds n k ++ [1]) +> default)) := by
  have h := long_pending_return ds n k l default
  simpa only [append_cons, append_nil, zero_cons_default'] using h

def return_to (six : Bool) (older : Stack) (rs : Records) : Cfg (Fin 2) (Fin 6) :=
  if six then active older rs else restored older rs

theorem finish_return (six : Bool) (older : Stack) (rs : Records)
    (hl : stack_good older) (hr : Good (!six) rs) :
    (returnCfg
      (if six then (bit0 ^ 5) +> stack_side older else [0, 0] +> ((bit1 ^ 4) +> stack_side older))
      (records_side rs)) [tm24]⊢* (return_to six older rs) := by
  rcases six with _ | _
  · simp only [return_to]
    refine stepPlus_trans' (return_separator (stack_side older) (records_side rs) (records_zero hr))
        ?_
    exact stack_return older rs hl hr
  · simp only [return_to, ↓reduceIte]
    unfold active
    rcases stack_zero older with ⟨l, hst⟩
    rw [hst]
    have h6 : (bit0 ^ 5) +> ([0] +> l) = (bit0 ^ 6) +> l := by
      simp [listPow_succ, bit0]
    rw [h6]
    exact return_six l (records_side rs) (records_zero hr)

inductive Ready : Cfg (Fin 2) (Fin 6) → Prop where
  | ReadyP (st : Stack) (rs : Records) : Source st rs → Ready (active st rs)
  | ReadyCap (c : Cap) (rs : Records) :
      Good true rs → measure (first_digits rs) ≤ 1 + cap_bound c →
      Ready (cap_entry (cap_prefix c) (cap_height c) (records_side rs))

open Ready

theorem cap_progress (c : Cap) (rs : Records)
    (hr : Good true rs) (hm : measure (first_digits rs) ≤ 1 + cap_bound c) :
    ∃ q, Ready q ∧ (cap_entry (cap_prefix c) (cap_height c) (records_side rs)) [tm24]⊢⁺ q := by
  rcases cap_rule c hr hm with ⟨bs, rs', hb, hg, hv, hs⟩
  refine ⟨active (extend_stack bs (SCap (next_cap c))) rs', ?_, ?_⟩
  · refine ReadyP _ _ ⟨extend_good hb trivial, hg, ?_⟩
    rw [extend_protected, extend_cap]
    exact hv
  · unfold active
    rw [extend_side]
    exact hs

theorem restored_ready (st : Stack) (rs : Records)
    (hl : stack_good st) (hr : Good true rs)
    (hm : measure (stack_protected st (first_digits rs)) ≤ cap_bound (stack_cap st)) :
    Ready (restored st rs) := by
  rcases restored_good st rs hl hr with ⟨st', rs', he, hl', hr', hc, hp⟩ | ⟨rs', he, hr', hp⟩
  · rw [he]
    refine ReadyP st' rs' ⟨hl', hr', ?_⟩
    rw [hc, hp]
    exact hm
  · rw [he]
    refine ReadyCap (stack_cap st) rs' hr' ?_
    rw [hp]
    omega

theorem carry_records_bound (p : Bool) {rs rs' : Records}
    (ha : Advance rs [] rs') (hg : Good p rs) :
    measure (first_digits rs') ≤ 1 + measure (first_digits rs) := by
  cases ha with
  | AEnd ds ds' hc => exact carry_bound hc (segment_length hg)
  | AStop ds b ds' b' tail _ hc => exact carry_bound hc (segment_length hg.1)

theorem ordinary_progress (st : Stack) (rs rs' : Records)
    (hs : Source st rs) (ha : Advance rs [] rs') :
    Ready (restored st rs') ∧ (active st rs) [tm24]⊢⁺ (restored st rs') := by
  rcases hs with ⟨hl, hr, hm⟩
  refine ⟨?_, active_return hl hr ha⟩
  have hg : Good true rs' := carry_records_good false ha hr
  rcases st with ⟨c⟩ | ⟨six, older, ds, n⟩
  · refine ReadyCap c rs' hg ?_
    have hb := carry_records_bound false ha hr
    simp only [stack_protected, stack_cap] at hm
    omega
  · exact restored_ready (SPush six older ds n) rs' hl hg hm

theorem constructor_progress (st : Stack) (ds : List Nat) (b : Nat) (rs : Records)
    (hs : Source st (RMore ds b rs)) (hd : IsBinary ds) (hb : b = 1 ∨ b = 2) :
    ∃ q, Ready q ∧ (active st (RMore ds b rs)) [tm24]⊢⁺ q := by
  rcases hs with ⟨hl, ⟨hseg, hb13, hr⟩, hm⟩
  rcases active_constructor hl hseg hr hd hb with ⟨st', rs', hl', hr', hc, hp, ht⟩
  refine ⟨active st' rs', ReadyP st' rs' ⟨hl', hr', ?_⟩, ht⟩
  rw [hc, hp]
  exact hm

theorem return_to_ready (six : Bool) (older : Stack) (rs : Records)
    (hl : stack_good older) (hr : Good (!six) rs)
    (hm : measure (stack_protected older (first_digits rs)) ≤ cap_bound (stack_cap older)) :
    Ready (return_to six older rs) := by
  rcases six with _ | _
  · exact restored_ready older rs hl hr hm
  · exact ReadyP older rs ⟨hl, hr, hm⟩

theorem long_constructor_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat) (rs :
    Records)
    (hs : Source (SPush six older ds n) (RMore (2 :: List.replicate k 0) 1 rs)) :
    ∃ q, Ready q ∧
        (active (SPush six older ds n) (RMore (2 :: List.replicate k 0) 1 rs)) [tm24]⊢⁺ q := by
  rcases hs with ⟨⟨hl, hb⟩, ⟨hseg, _, hr⟩, hm⟩
  rcases advance_total rs hr with ⟨bs, rs', ha, hbs, hg⟩
  refine ⟨active (extend_stack bs (SPush six older (merged ds n k) 0)) rs', ?_, ?_⟩
  · refine ReadyP _ _ ⟨extend_good hbs ⟨hl, merged_block six k hb hseg⟩, hg, ?_⟩
    rw [extend_cap, extend_protected]
    simp only [stack_cap, stack_protected] at hm ⊢
    rw [stack_measure older (merged_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    rw [extend_side]
    simp only [stack_side, records_side]
    refine stepStar_trans' (long_pending ds n k
      (if six then (bit0 ^ 5) +> stack_side older else [0, 0] +> ((bit1 ^ 4) +> stack_side older))
      ((bit0 ^ 1) +> ((bit1 ^ 7) +> records_side rs))) ?_
    exact advance_spec ha 1 (pending (merged ds n k)
      (if six then (bit0 ^ 5) +> stack_side older else [0,
          0] +> ((bit1 ^ 4) +> stack_side older))) (Or.inl rfl)

theorem long_end_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat)
    (hs : Source (SPush six older ds n) (REnd (2 :: List.replicate (1 + k) 0))) :
    ∃ q, Ready q ∧
        (active (SPush six older ds n) (REnd (2 :: List.replicate (1 + k) 0))) [tm24]⊢⁺ q := by
  rcases hs with ⟨⟨hl, hb⟩, hseg, hm⟩
  have hg : Good (!six) (REnd (merged ds n k ++ [1])) :=
    merged_bump_segment six 0 k hb hseg (Or.inl rfl)
  refine ⟨return_to six older (REnd (merged ds n k ++ [1])), ?_, ?_⟩
  · refine return_to_ready six older (REnd (merged ds n k ++ [1])) hl hg ?_
    simp only [first_digits, stack_protected, stack_cap] at hm ⊢
    rw [stack_measure older (bumped_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    simp only [stack_side, records_side]
    refine step_right_default (long_pending_blank ds n k
      (if six then (bit0 ^ 5) +> stack_side older else [0,
          0] +> ((bit1 ^ 4) +> stack_side older))) ?_
    exact finish_return six older (REnd (merged ds n k ++ [1])) hl hg

theorem long_three_progress (six : Bool) (older : Stack) (ds : List Nat) (n k : Nat) (rs : Records)
    (hs : Source (SPush six older ds n) (RMore (2 :: List.replicate (1 + k) 0) 3 rs)) :
    ∃ q, Ready q ∧
        (active (SPush six older ds n) (RMore (2 :: List.replicate (1 + k) 0) 3 rs)) [tm24]⊢⁺ q :=
        by
  rcases hs with ⟨⟨hl, hb⟩, ⟨hseg, _, hr⟩, hm⟩
  have hg : Good (!six) (RMore (merged ds n k ++ [1]) 1 rs) :=
    ⟨merged_bump_segment six 3 k hb hseg (Or.inr rfl), ⟨by omega, by omega⟩, hr⟩
  refine ⟨return_to six older (RMore (merged ds n k ++ [1]) 1 rs), ?_, ?_⟩
  · refine return_to_ready six older (RMore (merged ds n k ++ [1]) 1 rs) hl hg ?_
    simp only [first_digits, stack_protected, stack_cap] at hm ⊢
    rw [stack_measure older (bumped_measure ds n k (block_length hb))]
    exact hm
  · unfold active
    simp only [stack_side, records_side]
    have h03 : (bit0 ^ 3) +> ((bit1 ^ 7) +> records_side rs) = [0, 0,
        0] +> ((bit1 ^ 7) +> records_side rs) := rfl
    rw [h03]
    refine step_right_default (long_pending_return ds n k
      (if six then (bit0 ^ 5) +> stack_side older else [0, 0] +> ((bit1 ^ 4) +> stack_side older))
      ((bit1 ^ 7) +> records_side rs)) ?_
    exact finish_return six older (RMore (merged ds n k ++ [1]) 1 rs) hl hg

theorem source_progress (st : Stack) (rs : Records) (h : Source st rs) :
    ∃ q, Ready q ∧ (active st rs) [tm24]⊢⁺ q := by
  cases rs with
  | REnd ds =>
    rcases h.2 with ⟨hs, hm⟩
    rcases segment_progress 0 ds hs (by omega) with ⟨k, rfl⟩ | ⟨ds', b', hc⟩ | ⟨_, hb⟩
    · rcases source_long_marked st 0 k hs hm with ⟨six, older, ds, n, rfl⟩
      rcases k with _ | k
      · have hl := segment_length hs
        simp at hl
      · have hk1 : k + 1 = 1 + k := by omega
        rw [hk1] at h ⊢
        exact long_end_progress six older ds n k h
    · have hb' := carry_zero hc
      subst hb'
      rcases ordinary_progress st (REnd ds) (REnd ds') h (Advance.AEnd ds ds' hc) with ⟨hr, hstep⟩
      exact ⟨restored st (REnd ds'), hr, hstep⟩
    · omega
  | RMore ds b rs =>
    rcases h.2 with ⟨⟨hs, hb, hr⟩, hm⟩
    rcases segment_progress b ds hs hb.2 with ⟨k, rfl⟩ | ⟨ds', b', hc⟩ | ⟨hd, hb12⟩
    · rcases source_long_marked st b k hs hm with ⟨six, older, ds, n, rfl⟩
      rcases long_segment b k hs hb.2 with ⟨rfl, _⟩ | ⟨hb13, _⟩
      · omega
      · rcases hb13 with rfl | rfl
        · exact long_constructor_progress six older ds n k rs h
        · rcases k with _ | k
          · have hl := segment_length hs
            simp at hl
          · have hk1 : k + 1 = 1 + k := by omega
            rw [hk1] at h ⊢
            exact long_three_progress six older ds n k rs h
    · rcases ordinary_progress st (RMore ds b rs) (RMore ds' b' rs) h
        (Advance.AStop ds b ds' b' rs (by omega) hc) with ⟨hr', hstep⟩
      exact ⟨restored st (RMore ds' b' rs), hr', hstep⟩
    · exact constructor_progress st ds b rs h hd hb12

theorem ready_progress (q : Cfg (Fin 2) (Fin 6)) (h : Ready q) :
    ∃ q', Ready q' ∧ q [tm24]⊢⁺ q' := by
  cases h with
  | ReadyP st rs hs => exact source_progress st rs hs
  | ReadyCap c rs hr hm => exact cap_progress c rs hr hm

theorem source_nonhalt {st : Stack} {rs : Records} (h : Source st rs) :
    NeverHaltsFrom tm24 (active st rs) := by
  refine NeverHaltsFrom.of_reachesPlus_invariant ?_ (ReadyP st rs h)
  intro c hc
  rcases ready_progress c hc with ⟨c', hc', hstep⟩
  exact ⟨c', hstep, hc'⟩

theorem neverHaltsFrom_of_reachesStar {M : Machine (Fin 2) (Fin 6)} {c₁ c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : c₁ [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : NeverHaltsFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M c₁ k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, BusyBeaver.multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩


theorem isNotHalt_of_neverHaltsFrom {M : Machine (Fin 2) (Fin 6)} {c₀ : Cfg (Fin 2) (Fin 6)}
    (hinit : (init []) [M]⊢* c₀) (h_never : NeverHaltsFrom M c₀) : IsNotHalt M := by
  obtain ⟨k₀, hk₀⟩ := hinit
  intro cfg ⟨k, hk⟩
  rcases Nat.lt_or_ge k k₀ with hlt | hge
  · rcases hstep_cfg : step M cfg with _ | _
    · have hnone : (step M cfg).isNone := by simp [hstep_cfg]
      have hnone_k₀ : multiStep M (init []) k₀ = none := by
        have hsplit : k₀ = k + (k₀ - k) := by omega
        rw [hsplit]
        exact multiStep_eq_none_of_isNone hk hnone (by omega)
      rw [hnone_k₀] at hk₀
      cases hk₀
    · rfl
  · have hsplit : k = k₀ + (k - k₀) := by omega
    rw [hsplit, BusyBeaver.multiStep_add, hk₀, Option.bind_some] at hk
    exact h_never cfg ⟨k - k₀, hk⟩



end TM24Donor

namespace M240

open BusyBeaver.Excursion
variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def tm240_machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA"

abbrev tm : Machine (Fin 2) (Fin 6) := tm240_machine.toBB

def qA : Fin 6 := 0
def qB : Fin 6 := 1
def qC : Fin 6 := 2
def qD : Fin 6 := 3
def qE : Fin 6 := 4
def qF : Fin 6 := 5

abbrev T := ListBlank (Fin 2)

def K (q : Fin 6) (L : T) (h : Fin 2) (R : T) : Cfg (Fin 2) (Fin 6) := ⟨some q, ⟨h, L, R⟩⟩

@[simp] theorem ms_zero (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 0 = some c := rfl
@[simp] theorem ms_one (M : Machine Γ Λ) (c : Cfg Γ Λ) : multiStep M c 1 = step M c := rfl
@[simp] theorem ms_succ (M : Machine Γ Λ) (c : Cfg Γ Λ) (n : ℕ) :
    multiStep M c (n + 1) = Option.bind (multiStep M c n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

theorem ms_add (M : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : ℕ) :
    multiStep M c₁ (n + m) = (multiStep M c₁ n).bind (fun c₂ => multiStep M c₂ m) := by
  induction m with
  | zero => simp
  | succ m' ih =>
    rw [Nat.add_succ, ms_succ, ih, Option.bind_assoc]
    simp_rw [ms_succ]

theorem ms_trans (M : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : ℕ)
    (h₁ : c₁ [M]⊢^{n} c₂) (h₂ : c₂ [M]⊢^{m} c₃) : c₁ [M]⊢^{n+m} c₃ := by
  rw [ms_add, h₁]; simp [h₂]

theorem ss_refl (M : Machine Γ Λ) (c : Cfg Γ Λ) : c [M]⊢* c := ⟨0, rfl⟩
theorem step_to_sp {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [M]⊢ c₂) : c₁ [M]⊢⁺ c₂ :=
  ⟨1, Nat.succ_pos 0, h⟩
theorem stepN_to_ss {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ} (h : c₁ [M]⊢^{n} c₂) :
    c₁ [M]⊢* c₂ := ⟨n, h⟩
theorem stepN_to_sp {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} {n : ℕ} (hn : 0 < n)
    (h : c₁ [M]⊢^{n} c₂) : c₁ [M]⊢⁺ c₂ := ⟨n, hn, h⟩
theorem sp_to_ss {M : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [M]⊢⁺ c₂) : c₁ [M]⊢* c₂ := by
  rcases h with ⟨n, _, hn⟩; exact ⟨n, hn⟩
theorem ss_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢* c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, ms_trans M c₁ c₂ c₃ n m hn hm⟩
theorem sp_ss_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢* c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn_pos, hn⟩; rcases h₂ with ⟨m, hm⟩
  exact ⟨n + m, Nat.add_pos_left hn_pos m, ms_trans M c₁ c₂ c₃ n m hn hm⟩
theorem ss_sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ := by
  rcases h₁ with ⟨n, hn⟩; rcases h₂ with ⟨m, hm_pos, hm⟩
  exact ⟨n + m, Nat.add_pos_right n hm_pos, ms_trans M c₁ c₂ c₃ n m hn hm⟩
theorem sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢⁺ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  sp_ss_trans h₁ (sp_to_ss h₂)
theorem step_sp_trans {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [M]⊢ c₂) (h₂ : c₂ [M]⊢⁺ c₃) : c₁ [M]⊢⁺ c₃ :=
  sp_trans (step_to_sp h₁) h₂
theorem ms_step {M : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ} {n : ℕ}
    (h₁ : c₁ [M]⊢ c₂) (h₂ : c₂ [M]⊢^{n} c₃) : c₁ [M]⊢^{n + 1} c₃ := by
  have := ms_trans M c₁ c₂ c₃ 1 n h₁ h₂
  rwa [Nat.add_comm 1 n] at this

omit [Inhabited Γ] in
@[simp] theorem p_zero_list (l : List Γ) : l ^ (0 : ℕ) = [] := rfl
omit [Inhabited Γ] in
theorem p_succ_list (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ++ l ^ n := rfl
omit [Inhabited Γ] in
@[simp] theorem l_pow_add (l : List Γ) (n m : ℕ) : l ^ (n + m) = l ^ n ++ l ^ m := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.succ_add, p_succ_list, p_succ_list, ih, List.append_assoc]
omit [Inhabited Γ] in
theorem p_succ_right (l : List Γ) (n : ℕ) : l ^ (n + 1) = l ^ n ++ l := by
  rw [l_pow_add]; simp

@[simp] theorem lb_append_nil (s : ListBlank Γ) : ([] : List Γ) +> s = s := rfl
@[simp] theorem lb_append_cons (a : Γ) (l : List Γ) (s : ListBlank Γ) : (a :: l) +> s = a >> (l +>
    s) := rfl
@[simp] theorem lb_append_assoc (l₁ l₂ : List Γ) (s : ListBlank Γ) : (l₁ ++ l₂) +> s = l₁ +> (l₂ +>
    s) :=
  Turing.ListBlank.append_assoc l₁ l₂ s
@[simp] theorem def_head : (default : T).head = 0 := rfl
@[simp] theorem def_tail : (default : T).tail = default := rfl
@[simp] theorem z_cons_def : (0 : Fin 2) >> (default : T) = default := by
  change ListBlank.cons default default = default
  exact ListBlank.cons_head_tail default
@[simp] theorem m_init_nil : (init ([] : List (Fin 2)) : Cfg (Fin 2) (Fin 6)) =
    K qA default 0 default := rfl

theorem pow1_succ (x : Fin 2) (n : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (n + 1) +>
    s = x >> (([x] : List (Fin 2)) ^ n +> s) := rfl
theorem pow1_succ' (x : Fin 2) (n : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (n + 1) +>
    s = ([x] : List (Fin 2)) ^ n +> (x >> s) := by
  rw [p_succ_right, lb_append_assoc]; rfl
theorem pow1_add (x : Fin 2) (a b : ℕ) (s : T) : ([x] : List (Fin 2)) ^ (a + b) +>
    s = ([x] : List (Fin 2)) ^ a +> (([x] : List (Fin 2)) ^ b +> s) := by
  rw [l_pow_add, lb_append_assoc]
theorem pow_blk_succ (u : List (Fin 2)) (n : ℕ) (s : T) : u ^ (n + 1) +> s = u +> (u ^ n +> s) := by
  rw [p_succ_list, lb_append_assoc]
theorem pow_blk_succ' (u : List (Fin 2)) (n : ℕ) (s : T) : u ^ (n + 1) +> s = u ^ n +> (u +> s) :=
    by
  rw [p_succ_right, lb_append_assoc]
theorem pow_blk_add (u : List (Fin 2)) (a b : ℕ) (s : T) : u ^ (a + b) +> s = u ^ a +> (u ^ b +>
    s) := by
  rw [l_pow_add, lb_append_assoc]
@[simp] theorem zeros_default (n : ℕ) : ([0] : List (Fin 2)) ^ n +> (default : T) = default := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow1_succ, ih, z_cons_def]

macro "step1" : tactic => `(tactic| (
  try simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, K, m_init_nil, p_succ_list,
      p_zero_list, Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one,
    List.singleton_append, List.nil_append, List.cons_append,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail]
  refine ms_step (by rfl) ?_
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, Turing.Tape.move, Tape.write,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail]))

macro "run_steps" n:num : tactic => `(tactic| (
  iterate $n step1
  simp only [BusyBeaver.Cfg.headRight, BusyBeaver.Cfg.headLeft, K, p_succ_list, p_zero_list,
      Nat.mul_zero, Nat.zero_add, Nat.add_zero, Nat.mul_one,
    List.singleton_append, List.nil_append, List.cons_append,
    lb_append_cons, lb_append_nil,
    Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons,
    z_cons_def, def_head, def_tail, ms_zero]
  rfl))

-- ---------------------------------------------------------------------------
-- Elementary runs & bounce lemmas
-- ---------------------------------------------------------------------------

theorem a1_run (k : ℕ) (L R : T) :
    (K qA L 1 (([1] : List (Fin 2)) ^ k +>
        ((0 : Fin 2) >> R))) [tm]⊢⁺ K qA (([0] : List (Fin 2)) ^ (k + 1) +> L) 0 R := by
  induction k generalizing L with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qA L 1 (([1] : List (Fin 2)) ^ (k + 1) +> ((0 : Fin 2) >> R))) [tm]⊢^{1}
        K qA ((0 : Fin 2) >> L) 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R)) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((0 : Fin 2) >> L)
    rwa [← pow1_succ'] at h2

theorem d1_run (k : ℕ) (L R : T) (s : Fin 2) :
    (K qD (([1] : List (Fin 2)) ^ k +>
        (s >> L)) 1 R) [tm]⊢⁺ K qD L s (([1] : List (Fin 2)) ^ (k + 1) +> R) := by
  induction k generalizing R with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qD (([1] : List (Fin 2)) ^ (k + 1) +> (s >> L)) 1 R) [tm]⊢^{1}
        K qD (([1] : List (Fin 2)) ^ k +> (s >> L)) 1 ((1 : Fin 2) >> R) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> R)
    rwa [← pow1_succ'] at h2

theorem e1_run (k : ℕ) (L R : T) :
    (K qE L 1 (([1] : List (Fin 2)) ^ k +>
        ((0 : Fin 2) >> R))) [tm]⊢⁺ K qE (([1] : List (Fin 2)) ^ (k + 1) +> L) 0 R := by
  induction k generalizing L with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ k ih =>
    have h1 : (K qE L 1 (([1] : List (Fin 2)) ^ (k + 1) +> ((0 : Fin 2) >> R))) [tm]⊢^{1}
        K qE ((1 : Fin 2) >> L) 1 (([1] : List (Fin 2)) ^ k +> ((0 : Fin 2) >> R)) := by run_steps 1
    refine step_sp_trans h1 ?_
    have h2 := ih ((1 : Fin 2) >> L)
    rwa [← pow1_succ'] at h2

theorem b1_walk (a : ℕ) (s : Fin 2) (L R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> (s >> L)) 1 R) [tm]⊢⁺ K qD L s (([1] : List (Fin 2)) ^ a +>
        ((0 : Fin 2) >> R)) := by
  cases a with
  | zero => exact ⟨1, by decide, by run_steps 1⟩
  | succ a =>
    have h1 : (K qB (([1] : List (Fin 2)) ^ (a + 1) +> (s >> L)) 1 R) [tm]⊢^{1}
        K qD (([1] : List (Fin 2)) ^ a +> (s >> L)) 1 ((0 : Fin 2) >> R) := by run_steps 1
    exact step_sp_trans h1 (d1_run a L ((0 : Fin 2) >> R) s)

theorem b1_zero_one (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> ((0 : Fin 2) >> (1 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (a + 1) +> Rest) 1 ((1 : Fin 2) >> R) := by
  refine sp_trans (b1_walk a 0 ((1 : Fin 2) >> Rest) R) ?_
  have h1 : (K qD ((1 : Fin 2) >> Rest) 0 (([1] : List (Fin 2)) ^ a +>
      ((0 : Fin 2) >> R))) [tm]⊢^{1}
      K qE Rest 1 (([1] : List (Fin 2)) ^ (a + 1) +> ((0 : Fin 2) >> R)) := by run_steps 1
  refine step_sp_trans h1 ?_
  refine sp_ss_trans (e1_run (a + 1) Rest R) ?_
  refine stepN_to_ss (n := 1) ?_
  rw [pow1_succ (1 : Fin 2) (a + 1)]
  run_steps 1

theorem b1_two_zeros_one (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ a +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qB Rest 1 (([1] : List (Fin 2)) ^ (a + 2) +> ((0 : Fin 2) >> R)) := by
  refine sp_ss_trans (b1_walk a 0 ((0 : Fin 2) >> (1 : Fin 2) >> Rest) R) ?_
  refine stepN_to_ss (n := 2) ?_
  rw [pow1_succ, pow1_succ]
  run_steps 2

theorem b1_three_zeros (a : ℕ) (Rest R : T) :
    (K qB (([1] : List (Fin 2)) ^ (a + 1) +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Rest)) 1 R) [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (a + 1) +>
          ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Rest)) 0 R := by
  refine sp_trans (b1_walk (a + 1) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Rest) R) ?_
  have h1 : (K qD ((0 : Fin 2) >> (0 : Fin 2) >> Rest) 0 (([1] : List (Fin 2)) ^ (a + 1) +>
      ((0 : Fin 2) >> R))) [tm]⊢^{5}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> Rest) 1 (([1] : List (Fin 2)) ^ a +>
          ((0 : Fin 2) >> R)) := by
    rw [pow1_succ]; run_steps 5
  exact ss_sp_trans (stepN_to_ss h1) (a1_run a _ R)

theorem a0_zero_R (c : ℕ) (L R : T) :
    (K qA L 0 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c + 3) +> ((0 : Fin 2) >> R)))) [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (c + 1) +>
          ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> L)) 0 R := by
  have h1 : (K qA L 0 ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (c + 3) +>
      ((0 : Fin 2) >> R)))) [tm]⊢^{4}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          L) 1 (([1] : List (Fin 2)) ^ c +> ((0 : Fin 2) >> R)) := by
    rw [pow1_succ, pow1_succ, pow1_succ]; run_steps 4
  exact ss_sp_trans (stepN_to_ss h1) (a1_run c _ R)

theorem a0_step (L R : T) : (K qA L 0 ((1 : Fin 2) >> R)) [tm]⊢^{1} K qB ((1 : Fin 2) >> L) 1 R :=
    by
  run_steps 1

def EBounce (j : ℕ) (s : Fin 2) (L' R' : T) : Cfg (Fin 2) (Fin 6) :=
  K qE L' s (([1] : List (Fin 2)) ^ (2 * j + 2) +> ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +>
      R')))

theorem ebounce_to_B1 (j : ℕ) (L' R' : T) :
    (EBounce j 1 L' R') [tm]⊢⁺ K qB (([1] : List (Fin 2)) ^ (2 * j + 2) +>
        L') 1 (([1] : List (Fin 2)) ^ (j + 1) +> R') := by
  unfold EBounce
  refine sp_ss_trans (e1_run (2 * j + 2) L' _) ?_
  refine stepN_to_ss (n := 1) ?_
  rw [pow1_succ (1 : Fin 2) (2 * j + 2), pow1_succ (1 : Fin 2) j]
  run_steps 1

theorem ebounce_one (j : ℕ) (s : Fin 2) (L' R' : T) :
    (EBounce j 1 ((1 : Fin 2) >> (0 : Fin 2) >> s >> L') R') [tm]⊢⁺ EBounce (j + 1) s L' R' := by
  refine sp_trans (ebounce_to_B1 j _ R') ?_
  rw [← pow1_succ']
  refine sp_ss_trans (b1_walk (2 * j + 3) 0 (s >> L') _) ?_
  refine stepN_to_ss (n := 1) ?_
  unfold EBounce
  have e1 : 2 * (j + 1) + 2 = (2 * j + 3) + 1 := by ring
  rw [e1, pow1_succ (1 : Fin 2) (2 * j + 3)]
  run_steps 1

theorem ebounce_zero (j : ℕ) (L₀ R' : T) :
    (EBounce j 0 ((0 : Fin 2) >> L₀) R') [tm]⊢⁺
      K qA (([0] : List (Fin 2)) ^ (2 * j + 1) +>
          ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L₀)) 0 (([1] : List (Fin 2)) ^ j +> R') :=
          by
  unfold EBounce
  have h1 : (K qE ((0 : Fin 2) >> L₀) 0 (([1] : List (Fin 2)) ^ (2 * j + 2) +>
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R')))) [tm]⊢^{4}
      K qA ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> L₀) 1 (([1] : List (Fin 2)) ^ (2 * j) +>
          ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R'))) := by
    rw [pow1_succ (1 : Fin 2) (2 * j + 1), pow1_succ (1 : Fin 2) (2 * j)]; run_steps 4
  exact ss_sp_trans (stepN_to_ss h1) (a1_run (2 * j) _ _)

theorem e0_to_B1 (j : ℕ) (L' R' : T) :
    (EBounce j 0 ((1 : Fin 2) >> L') R') [tm]⊢^{1} K qB L' 1 (([1] : List (Fin 2)) ^ (2 * j + 3) +>
        ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ j +> R'))) := by
  unfold EBounce
  rw [pow1_succ (1 : Fin 2) (2 * j + 2)]
  run_steps 1

theorem a0_odd_zeros (j : ℕ) : ∀ (s : Fin 2) (L' R' : T),
    (K qA (([0] : List (Fin 2)) ^ (2 * j + 1) +> (s >> L')) 0 (([1] : List (Fin 2)) ^ (j + 1) +>
        R')) [tm]⊢⁺
      EBounce j s L' R' := by
  induction j with
  | zero =>
    intro s L' R'
    exact ⟨4, by decide, by unfold EBounce; run_steps 4⟩
  | succ j ih =>
    intro s L' R'
    have e1 : 2 * (j + 1) + 1 = (2 * j + 1) + 1 + 1 := by ring
    rw [e1, pow1_succ' (0 : Fin 2) (2 * j + 1 + 1), pow1_succ' (0 : Fin 2) (2 * j + 1),
      pow1_succ' (1 : Fin 2) (j + 1)]
    refine sp_trans (ih 0 ((0 : Fin 2) >> s >> L') ((1 : Fin 2) >> R')) ?_
    refine sp_trans (ebounce_zero j (s >> L') ((1 : Fin 2) >> R')) ?_
    rw [← pow1_succ' (1 : Fin 2) j]
    refine sp_trans (ih 1 ((1 : Fin 2) >> (0 : Fin 2) >> s >> L') R') ?_
    exact ebounce_one j s L' R'

theorem a0_cascade (k : ℕ) : ∀ (Lrem R' : T),
    (K qA (([0] : List (Fin 2)) ^ (2 * k + 1) +>
        ((1 : Fin 2) >> (1 : Fin 2) >> Lrem)) 0 (([1] : List (Fin 2)) ^ k +> R')) [tm]⊢*
      K qA (([0, 1, 1] : List (Fin 2)) ^ (k + 1) +> Lrem) 0 R' := by
  induction k with
  | zero => intro Lrem R'; exact ss_refl _ _
  | succ k ih =>
    intro Lrem R'
    have e1 : 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 := by ring
    rw [e1, pow1_succ' (0 : Fin 2) (2 * k + 1 + 1), pow1_succ' (0 : Fin 2) (2 * k + 1)]
    refine ss_trans (sp_to_ss (a0_odd_zeros k 0 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        Lrem) R')) ?_
    refine ss_trans (sp_to_ss (ebounce_zero k ((1 : Fin 2) >> (1 : Fin 2) >> Lrem) R')) ?_
    have h := ih ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> Lrem) R'
    rw [pow_blk_succ' ([0, 1, 1] : List (Fin 2)) (k + 1)]
    exact h

theorem b1_zero_one_run (w : ℕ) : ∀ (a m : ℕ) (Rest R' : T),
    (K qB (([1] : List (Fin 2)) ^ (a + 1) +> (([0, 1,
        1] : List (Fin 2)) ^ w +> Rest)) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢*
      K qB (([1] : List (Fin 2)) ^ (a + 2 * w + 1) +> Rest) 1 (([1] : List (Fin 2)) ^ (m + w) +>
          R') := by
  induction w with
  | zero => intro a m Rest R'; exact ss_refl _ _
  | succ w ih =>
    intro a m Rest R'
    rw [pow_blk_succ ([0, 1, 1] : List (Fin 2)) w]
    simp only [lb_append_cons, lb_append_nil]
    refine ss_trans (sp_to_ss (b1_zero_one (a + 1) _ _)) ?_
    rw [← pow1_succ' (1 : Fin 2) (a + 1 + 1), ← pow1_succ (1 : Fin 2) m]
    have h := ih (a + 2) (m + 1) Rest R'
    have e1 : a + 2 + 2 * w + 1 = a + 2 * (w + 1) + 1 := by ring
    have e2 : m + 1 + w = m + (w + 1) := by ring
    have e0 : a + 2 + 1 = a + 1 + 1 + 1 := rfl
    rw [e0, e1, e2] at h
    exact h

theorem m_round (j : ℕ) (L R : T) :
    (K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + 1) +>
        R)) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (2 * j + 3) +>
          ((0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + 1) +> R) := by
  refine sp_trans (b1_three_zeros (2 * j) L _) ?_
  refine sp_trans (a0_odd_zeros j 1 ((1 : Fin 2) >> (0 : Fin 2) >> L) R) ?_
  have h := ebounce_to_B1 j ((1 : Fin 2) >> (0 : Fin 2) >> L) R
  rw [← pow1_succ' (1 : Fin 2) (2 * j + 2)] at h
  exact h

theorem m_rounds (n : ℕ) : ∀ (j : ℕ) (L R : T),
    (K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +> (([0] : List (Fin 2)) ^ (2 * n + 2) +>
        L)) 1 (([1] : List (Fin 2)) ^ (j + n) +> R)) [tm]⊢*
      K qB (([1] : List (Fin 2)) ^ (2 * j + 2 * n + 1) +>
          ((0 : Fin 2) >> (0 : Fin 2) >> L)) 1 (([1] : List (Fin 2)) ^ (j + n) +> R) := by
  induction n with
  | zero => intro j L R; exact ss_refl _ _
  | succ n ih =>
    intro j L R
    have e1 : 2 * (n + 1) + 2 = (2 * n + 1) + 1 + 1 + 1 := by ring
    rw [e1, pow1_succ (0 : Fin 2), pow1_succ (0 : Fin 2), pow1_succ (0 : Fin 2)]
    have e2 : j + (n + 1) = (j + 1) + n := by ring
    rw [e2, pow1_add (1 : Fin 2) (j + 1) n]
    refine ss_trans (sp_to_ss (m_round j _ _)) ?_
    have h := ih (j + 1) L R
    have e3 : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
    have e4 : 2 * (j + 1) + 2 * n + 1 = 2 * j + 2 * (n + 1) + 1 := by ring
    have e5 : 2 * n + 2 = (2 * n + 1) + 1 := rfl
    rw [e3, e4, e5, pow1_succ (0 : Fin 2) (2 * n + 1), pow1_add (1 : Fin 2) (j + 1) n] at h
    exact h

theorem fixed89 (Lrem : T) :
    (K qA (([0, 1, 1] : List (Fin 2)) ^ 5 +> Lrem) 0 default) [tm]⊢^{89}
      K qB (([1] : List (Fin 2)) ^ 12 +> Lrem) 1 (([1] : List (Fin 2)) ^ 5 +> default) := by
  run_steps 89

theorem fixed23 (Rest : T) :
    (K qA ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> Rest) 0 default) [tm]⊢^{23}
      K qB ((1 : Fin 2) >> (0 : Fin 2) >> Rest) 1 (([1] : List (Fin 2)) ^ 4 +> default) := by
  run_steps 23

-- ---------------------------------------------------------------------------
-- Two-stack configuration family & 17 macro rules
-- ---------------------------------------------------------------------------

def encL : List (ℕ × ℕ) → T
  | [] => default
  | (z, w) :: l => ([0] : List (Fin 2)) ^ (z + 1) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
          1] : List (Fin 2)) ^ (w + 5) +> encL l))

def encS : List ℕ → T
  | [] => default
  | b :: s => (0 : Fin 2) >> (([1] : List (Fin 2)) ^ b +> encS s)

@[simp] theorem encL_nil : encL [] = default := rfl
@[simp] theorem encL_cons (z w : ℕ) (l : List (ℕ × ℕ)) : encL ((z,
    w) :: l) = ([0] : List (Fin 2)) ^ (z + 1) +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
          1] : List (Fin 2)) ^ (w + 5) +> encL l)) := rfl
@[simp] theorem encS_nil : encS [] = default := rfl
@[simp] theorem encS_cons (b : ℕ) (s : List ℕ) : encS (b :: s) = (0 : Fin 2) >>
    (([1] : List (Fin 2)) ^ b +> encS s) := rfl

def Beq (m : ℕ) (l : List (ℕ × ℕ)) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * m + 2) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> default)
def Bev (j : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * j + 1) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> encS s)
def Bodd (k : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qB (([1] : List (Fin 2)) ^ (2 * k + 10) +> encL l) 1 (([1] : List (Fin 2)) ^ m +> encS s)
def Amega (z w : ℕ) (l : List (ℕ × ℕ)) (m : ℕ) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qA (encL ((z, w) :: l)) 0 (([1] : List (Fin 2)) ^ m +> encS s)
def Bounce (w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) : Cfg (Fin 2) (Fin 6) :=
  K qA (([0, 1, 1] : List (Fin 2)) ^ (w + 5) +> encL l) 0 (encS s)

theorem default3 : (default : T) = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default := by simp
theorem zeros3 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 3) +>
    X = (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
theorem zeros3' (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 3) +> X = ([0] : List (Fin 2)) ^ n +>
    ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> X) := by
  rw [pow1_add]; rfl
theorem zeros2 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 2) +>
    X = (0 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
theorem zeros1 (n : ℕ) (X : T) : ([0] : List (Fin 2)) ^ (n + 1) +>
    X = (0 : Fin 2) >> (([0] : List (Fin 2)) ^ n +> X) := rfl
theorem ones1 (n : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (n + 1) +>
    X = (1 : Fin 2) >> (([1] : List (Fin 2)) ^ n +> X) := rfl
theorem ones1' (n : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (n + 1) +> X = ([1] : List (Fin 2)) ^ n +>
    ((1 : Fin 2) >> X) := pow1_succ' 1 n X
theorem ones_one (X : T) : ([1] : List (Fin 2)) ^ 1 +> X = (1 : Fin 2) >> X := rfl
theorem ones_add (a b : ℕ) (X : T) : ([1] : List (Fin 2)) ^ (a + b) +>
    X = ([1] : List (Fin 2)) ^ a +> (([1] : List (Fin 2)) ^ b +> X) := pow1_add 1 a b X
theorem blk_add (a b : ℕ) (X : T) : ([0, 1, 1] : List (Fin 2)) ^ (a + b) +> X = ([0, 1,
    1] : List (Fin 2)) ^ a +> (([0, 1, 1] : List (Fin 2)) ^ b +> X) := pow_blk_add _ a b X

theorem R4 (j r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((z + 2, w) :: l') (j + 1 + r) s) [tm]⊢⁺ Bev (j + 1) ((z, w) :: l') (j + 1 + r) s := by
  unfold Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, ones_add (j + 1) r]
  have h :=
      m_round j (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l')))
    (([1] : List (Fin 2)) ^ r +> encS s)
  have e : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e]; exact h

theorem R4nil (j r : ℕ) (s : List ℕ) :
    (Bev j [] (j + 1 + r) s) [tm]⊢⁺ Bev (j + 1) [] (j + 1 + r) s := by
  unfold Bev
  rw [encL_nil, default3, ones_add (j + 1) r]
  have h := m_round j default (([1] : List (Fin 2)) ^ r +> encS s)
  have e : 2 * (j + 1) + 1 = 2 * j + 3 := by ring
  rw [e]
  simp only [z_cons_def] at h ⊢
  exact h

theorem R5 (m z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev (m + 4) ((z + 2, w) :: l') (m + 4) s) [tm]⊢⁺ Bounce m ((z, w) :: l') s := by
  unfold Bev Bounce
  rw [encL_cons, encL_cons, zeros3, zeros1]
  refine sp_ss_trans (b1_three_zeros (2 * (m + 4)) _ _) ?_
  have h :=
      a0_cascade (m + 4) ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (encS s)
  have e : m + 4 + 1 = m + 5 := by ring
  rw [e] at h; exact h

theorem R5nil (m : ℕ) (s : List ℕ) :
    (Bev (m + 4) [] (m + 4) s) [tm]⊢⁺ Bounce m [] s := by
  unfold Bev Bounce
  rw [encL_nil, default3]
  refine sp_ss_trans (b1_three_zeros (2 * (m + 4)) _ _) ?_
  have h := a0_cascade (m + 4) ((0 : Fin 2) >> default) (encS s)
  have e : m + 4 + 1 = m + 5 := by ring
  rw [e] at h
  simp only [z_cons_def] at h ⊢
  exact h

theorem pop_frame0 (a m w : ℕ) (l' : List (ℕ × ℕ)) (R' : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> encL ((0,
        w) :: l')) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (a + 2 * w + 13) +>
          encL l') 1 (([1] : List (Fin 2)) ^ (m + w + 7) +> R') := by
  rw [encL_cons, zeros1, p_zero_list, lb_append_nil]
  refine sp_trans (b1_zero_one a _ _) ?_
  rw [← ones1' (a + 1)]
  refine sp_ss_trans (b1_zero_one (a + 2) _ _) ?_
  rw [← ones1 m, ← ones1 (m + 1)]
  have h := b1_zero_one_run (w + 5) (a + 2) (m + 2) (encL l') R'
  have e1 : a + 2 + 2 * (w + 5) + 1 = a + 2 * w + 13 := by ring
  have e2 : m + 2 + (w + 5) = m + w + 7 := by ring
  have e3 : m + 2 = m + 1 + 1 := rfl
  rw [e1, e2, e3] at h
  exact h

theorem pop_frame1 (a m w : ℕ) (l' : List (ℕ × ℕ)) (R' : T) :
    (K qB (([1] : List (Fin 2)) ^ a +> encL ((1,
        w) :: l')) 1 (([1] : List (Fin 2)) ^ m +> R')) [tm]⊢⁺
      K qB (([1] : List (Fin 2)) ^ (2 * w + 12) +> encL l') 1 (([1] : List (Fin 2)) ^ (a + w + 8) +>
          ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R'))) := by
  rw [encL_cons, zeros2, p_zero_list, lb_append_nil]
  refine sp_trans (b1_two_zeros_one a _ _) ?_
  have h1 :=
      b1_zero_one 1 (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l') (([1] : List (Fin 2)) ^ (a + 2) +>
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +> R')))
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_ss_trans h1 ?_
  rw [← ones1 (a + 2)]
  have h :=
      b1_zero_one_run (w + 5) 1 (a + 2 + 1) (encL l') ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ m +>
      R'))
  have e1 : 1 + 2 * (w + 5) + 1 = 2 * w + 12 := by ring
  have e2 : a + 2 + 1 + (w + 5) = a + w + 8 := by ring
  rw [e1, e2] at h
  exact h

theorem R2 (m w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq m ((0, w) :: l')) [tm]⊢⁺ Bev (m + w + 7) l' (m + w + 7) [] := by
  unfold Beq Bev
  have h := pop_frame0 (2 * m + 2) m w l' default
  have e : 2 * m + 2 + 2 * w + 13 = 2 * (m + w + 7) + 1 := by ring
  rw [e] at h; rw [encS_nil]; exact h

theorem R3 (m w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq m ((1, w) :: l')) [tm]⊢⁺ Bodd (w + 1) l' (2 * m + w + 10) [m] := by
  unfold Beq Bodd
  have h := pop_frame1 (2 * m + 2) m w l' default
  have e1 : 2 * m + 2 + w + 8 = 2 * m + w + 10 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons, encS_nil]; exact h

theorem R6 (j m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((0, w) :: l') m s) [tm]⊢⁺ Bodd (j + w + 2) l' (m + w + 7) s := by
  unfold Bev Bodd
  have h := pop_frame0 (2 * j + 1) m w l' (encS s)
  have e : 2 * j + 1 + 2 * w + 13 = 2 * (j + w + 2) + 10 := by ring
  rw [e] at h; exact h

theorem R7 (j m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bev j ((1, w) :: l') m s) [tm]⊢⁺ Bodd (w + 1) l' (2 * j + w + 9) (m :: s) := by
  unfold Bev Bodd
  have h := pop_frame1 (2 * j + 1) m w l' (encS s)
  have e1 : 2 * j + 1 + w + 8 = 2 * j + w + 9 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons]; exact h

theorem R8a (k m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((0, w) :: l') m s) [tm]⊢⁺ Bev (k + w + 11) l' (m + w + 7) s := by
  unfold Bodd Bev
  have h := pop_frame0 (2 * k + 10) m w l' (encS s)
  have e : 2 * k + 10 + 2 * w + 13 = 2 * (k + w + 11) + 1 := by ring
  rw [e] at h; exact h

theorem R8b (k m w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((1, w) :: l') m s) [tm]⊢⁺ Bodd (w + 1) l' (2 * k + w + 18) (m :: s) := by
  unfold Bodd
  have h := pop_frame1 (2 * k + 10) m w l' (encS s)
  have e1 : 2 * k + 10 + w + 8 = 2 * k + w + 18 := by ring
  have e2 : 2 * w + 12 = 2 * (w + 1) + 10 := by ring
  rw [e1, e2] at h; rw [encS_cons]; exact h

theorem R8 (k r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ) :
    (Bodd k ((z + 2, w) :: l') (k + 5 + r) s) [tm]⊢⁺ Bev 0 ((z,
        w) :: l') (2 * k + 11) ((k + 4 + r) :: s) := by
  unfold Bodd Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons]
  have e0 : 2 * k + 10 = (2 * k + 9) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * k + 9) _ _) ?_
  rw [show k + 5 + r = (k + 4 + r) + 1 by ring, ones1 (k + 4 + r)]
  refine ss_sp_trans (stepN_to_ss (a0_step _ _)) ?_
  have e1 : 2 * k + 9 + 1 = 2 * (k + 4) + 2 := by ring
  rw [e1]
  have hr :=
      m_rounds (k + 4) 0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l'))))
    (([1] : List (Fin 2)) ^ r +> encS s)
  rw [← ones_add (0 + (k + 4)) r] at hr
  simp only [Nat.zero_add, Nat.mul_zero, ones_one] at hr
  refine ss_sp_trans hr ?_
  have h :=
      b1_two_zeros_one (2 * (k + 4) + 1) ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ (k + 4 + r) +> encS s)
  have e2 : 2 * (k + 4) + 1 + 2 = 2 * k + 11 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

theorem R8nil (k r : ℕ) (s : List ℕ) :
    (Bodd k [] (k + 5 + r) s) [tm]⊢⁺ Bev 0 [] (2 * k + 11) ((k + 4 + r) :: s) := by
  unfold Bodd Bev
  rw [encL_nil, default3, encS_cons]
  have e0 : 2 * k + 10 = (2 * k + 9) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * k + 9) _ _) ?_
  rw [show k + 5 + r = (k + 4 + r) + 1 by ring, ones1 (k + 4 + r)]
  refine ss_sp_trans (stepN_to_ss (a0_step _ _)) ?_
  have e1 : 2 * k + 9 + 1 = 2 * (k + 4) + 2 := by ring
  rw [e1]
  have hr :=
      m_rounds (k + 4) 0 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      default) (([1] : List (Fin 2)) ^ r +> encS s)
  rw [← ones_add (0 + (k + 4)) r] at hr
  simp only [Nat.zero_add, Nat.mul_zero, ones_one] at hr
  refine ss_sp_trans hr ?_
  have h :=
      b1_two_zeros_one (2 * (k + 4) + 1) ((1 : Fin 2) >> (0 : Fin 2) >>
      default) (([1] : List (Fin 2)) ^ (k + 4 + r) +> encS s)
  have e2 : 2 * (k + 4) + 1 + 2 = 2 * k + 11 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one, z_cons_def] at h ⊢
  exact h

theorem R1 (m z w : ℕ) (l' : List (ℕ × ℕ)) :
    (Beq (m + 5) ((z + 2, w) :: l')) [tm]⊢⁺ Bev 0 ((z, w) :: l') (2 * (m + 5) + 4) [m + 5] := by
  unfold Beq Bev
  rw [encL_cons, encL_cons, zeros3, zeros1, encS_cons, encS_nil]
  have e0 : 2 * (m + 5) + 2 = (2 * m + 11) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * m + 11) _ _) ?_
  have e1 : 2 * m + 11 + 1 = (2 * (m + 4) + 1) + 3 := by ring
  rw [e1, zeros3']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Y : T :=
      (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l'))) with hY
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero (m + 4) ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade (m + 4) ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  rw [show m + 4 + 1 = 5 + m by ring, blk_add 5 m]
  refine ss_sp_trans (stepN_to_ss (fixed89 _)) ?_
  have hrun := b1_zero_one_run m 11 5 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default
  refine ss_sp_trans hrun ?_
  rw [hY]
  have h :=
      b1_two_zeros_one (11 + 2 * m + 1) ((1 : Fin 2) >> (0 : Fin 2) >> (([0] : List (Fin 2)) ^ z +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l')))) (([1] : List (Fin 2)) ^ (5 + m) +> default)
  have e2 : 11 + 2 * m + 1 + 2 = 2 * (5 + m) + 4 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one]
  exact h

theorem R1nil (m : ℕ) :
    (Beq (m + 5) []) [tm]⊢⁺ Bev 0 [] (2 * (m + 5) + 4) [m + 5] := by
  unfold Beq Bev
  rw [encL_nil, encS_cons, encS_nil]
  rw [show (([1] : List (Fin 2)) ^ (2 * (m + 5) + 2) +>
      (default : T)) = ([1] : List (Fin 2)) ^ (2 * (m + 5) + 2) +>
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> default) by simp]
  have e0 : 2 * (m + 5) + 2 = (2 * m + 11) + 1 := by ring
  rw [e0]
  refine sp_trans (b1_three_zeros (2 * m + 11) _ _) ?_
  have e1 : 2 * m + 11 + 1 = (2 * (m + 4) + 1) + 3 := by ring
  rw [e1, zeros3']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Y : T := (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> default with hY
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  refine sp_trans (ebounce_zero (m + 4) ((0 : Fin 2) >> Y) default) ?_
  refine ss_sp_trans (a0_cascade (m + 4) ((0 : Fin 2) >> (0 : Fin 2) >> Y) default) ?_
  rw [show m + 4 + 1 = 5 + m by ring, blk_add 5 m]
  refine ss_sp_trans (stepN_to_ss (fixed89 _)) ?_
  have hrun := b1_zero_one_run m 11 5 ((0 : Fin 2) >> (0 : Fin 2) >> Y) default
  refine ss_sp_trans hrun ?_
  rw [hY]
  have h :=
      b1_two_zeros_one (11 + 2 * m + 1) ((1 : Fin 2) >> (0 : Fin 2) >>
      default) (([1] : List (Fin 2)) ^ (5 + m) +> default)
  have e2 : 11 + 2 * m + 1 + 2 = 2 * (5 + m) + 4 := by ring
  rw [e2] at h
  simp only [Nat.mul_zero, Nat.zero_add, ones_one, z_cons_def] at h ⊢
  exact h

theorem R9 (m z' w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * (m + 5) + z') w l (m + 5) s) [tm]⊢⁺ Bounce m ((z', w) :: l) s := by
  unfold Amega Bounce
  rw [encL_cons, encL_cons]
  have e1 : 2 * (m + 5) + z' + 1 = (2 * (m + 4) + 1) + (z' + 2) := by ring
  rw [e1, pow1_add (0 : Fin 2) _ (z' + 2), zeros2 z', zeros1 z']
  rw [show m + 5 = (m + 4) + 1 by ring]
  set Z : T :=
      ([0] : List (Fin 2)) ^ z' +>
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l)) with hZ
  refine sp_trans (a0_odd_zeros (m + 4) 0 ((0 : Fin 2) >> Z) (encS s)) ?_
  refine sp_ss_trans (ebounce_zero (m + 4) Z (encS s)) ?_
  exact a0_cascade (m + 4) ((0 : Fin 2) >> Z) (encS s)

theorem R10 (k r w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * k) w l (k + 1 + r) s) [tm]⊢⁺ Bodd (k + w + 2) l (k + 1 + r + w + 6) s := by
  unfold Amega Bodd
  rw [encL_cons, zeros1, ones_add (k + 1) r]
  refine sp_trans (a0_odd_zeros k 1 _ _) ?_
  refine sp_trans (ebounce_to_B1 k _ _) ?_
  rw [← ones1' (2 * k + 2)]
  refine sp_ss_trans (b1_zero_one (2 * k + 3) _ _) ?_
  rw [← ones_add (k + 1) r, ← ones1 (k + 1 + r)]
  have h := b1_zero_one_run (w + 5) (2 * k + 3) (k + 1 + r + 1) (encL l) (encS s)
  have e1 : 2 * k + 3 + 2 * (w + 5) + 1 = 2 * (k + w + 2) + 10 := by ring
  have e2 : k + 1 + r + 1 + (w + 5) = k + 1 + r + w + 6 := by ring
  rw [e1, e2] at h
  exact h

theorem R11 (k r w : ℕ) (l : List (ℕ × ℕ)) (s : List ℕ) :
    (Amega (2 * k + 1) w l (k + 1 + r) s) [tm]⊢⁺ Bodd (w + 1) l (2 * k + w + 9) ((k + r) :: s) := by
  unfold Amega Bodd
  rw [encL_cons, pow1_succ' (0 : Fin 2) (2 * k + 1), ones_add (k + 1) r, encS_cons]
  refine sp_trans (a0_odd_zeros k 0 _ _) ?_
  refine ss_sp_trans (stepN_to_ss (e0_to_B1 k _ _)) ?_
  rw [← ones_add k r]
  have h1 :=
      b1_zero_one 1 (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l) (([1] : List (Fin 2)) ^ (2 * k + 3) +>
      ((0 : Fin 2) >> (([1] : List (Fin 2)) ^ (k + r) +> encS s)))
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_ss_trans h1 ?_
  rw [← ones1 (2 * k + 3)]
  have h :=
      b1_zero_one_run (w + 5) 1 (2 * k + 4) (encL l) ((0 : Fin 2) >>
      (([1] : List (Fin 2)) ^ (k + r) +> encS s))
  have e1 : 1 + 2 * (w + 5) + 1 = 2 * (w + 1) + 10 := by ring
  have e2 : 2 * k + 4 + (w + 5) = 2 * k + w + 9 := by ring
  rw [e1, e2] at h
  exact h

theorem R12 (w : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l []) [tm]⊢⁺ Beq (w + 5) l := by
  unfold Bounce Beq
  rw [encS_nil, show w + 5 = 5 + w by ring, blk_add 5 w]
  refine sp_ss_trans (stepN_to_sp (n := 89) (by decide) (fixed89 _)) ?_
  have h := b1_zero_one_run w 11 5 (encL l) default
  have e1 : 11 + 2 * w + 1 = 2 * (5 + w) + 2 := by ring
  rw [e1] at h
  exact h

theorem R13 (w : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l [5]) [tm]⊢⁺ Bodd (w + 2) l (w + 11) [] := by
  unfold Bounce Bodd
  rw [encS_cons, encS_nil]
  have hz : (([1] : List (Fin 2)) ^ 5 +> default) = ([1] : List (Fin 2)) ^ (2 + 3) +>
      ((0 : Fin 2) >> default) := by simp
  rw [hz]
  refine sp_trans (a0_zero_R 2 _ _) ?_
  rw [zeros3 0, p_zero_list, lb_append_nil]
  refine ss_sp_trans (stepN_to_ss (fixed23 _)) ?_
  have h1 :=
      b1_zero_one 1 ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l)) (([1] : List (Fin 2)) ^ 4 +> default)
  rw [pow1_succ (1 : Fin 2) 0, p_zero_list, lb_append_nil] at h1
  refine sp_trans h1 ?_
  rw [← ones1' 2, ← ones1 4]
  refine sp_ss_trans (b1_zero_one 3 _ _) ?_
  rw [← ones1 5]
  have h := b1_zero_one_run (w + 5) 3 (5 + 1) (encL l) default
  have e1 : 3 + 2 * (w + 5) + 1 = 2 * (w + 2) + 10 := by ring
  have e2 : 5 + 1 + (w + 5) = w + 11 := by ring
  rw [e1, e2] at h
  exact h

theorem R14 (w b' : ℕ) (l : List (ℕ × ℕ)) :
    (Bounce w l [b' + 15]) [tm]⊢⁺ Beq 5 ((b', w) :: l) := by
  unfold Bounce Beq
  rw [encS_cons, encS_nil, encL_cons]
  set X : T :=
      (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (([0, 1,
      1] : List (Fin 2)) ^ (w + 5) +> encL l) with hX
  have hz : (([1] : List (Fin 2)) ^ (b' + 15) +>
      default) = ([1] : List (Fin 2)) ^ ((b' + 12) + 3) +> ((0 : Fin 2) >> default) := by
    rw [show b' + 12 + 3 = b' + 15 by ring, z_cons_def]
  rw [hz]
  refine sp_trans (a0_zero_R (b' + 12) _ _) ?_
  rw [show b' + 12 + 1 = (b' + 10) + 3 by ring, zeros3]
  refine ss_sp_trans (stepN_to_ss (fixed23 _)) ?_
  have hr := m_rounds 4 0 (([0] : List (Fin 2)) ^ (b' + 1) +> X) default
  rw [show (2 : ℕ) * 0 + 1 = 1 by norm_num, show (2 : ℕ) * 4 + 2 = 10 by norm_num,
    show (0 : ℕ) + 4 = 4 by norm_num, show (2 : ℕ) * 0 + 2 * 4 + 1 = 9 by norm_num, ones_one,
    ← pow1_add (0 : Fin 2) 10 (b' + 1), show 10 + (b' + 1) = (b' + 10) + 1 by ring,
        zeros1 (b' + 10)] at hr
  refine ss_sp_trans hr ?_
  rw [zeros1 b']
  refine sp_ss_trans (b1_three_zeros 8 _ _) ?_
  refine ss_trans (a0_cascade 4 ((0 : Fin 2) >> (([0] : List (Fin 2)) ^ b' +> X)) default) ?_
  exact stepN_to_ss (fixed89 _)

theorem R15 (w b₁ b₂ : ℕ) (l : List (ℕ × ℕ)) (s' : List ℕ) :
    (Bounce w l ((b₁ + 3) :: b₂ :: s')) [tm]⊢⁺ Amega b₁ w l b₂ s' := by
  unfold Bounce Amega
  rw [encS_cons, encS_cons, encL_cons]
  exact a0_zero_R b₁ _ _

-- Iterated R4 / R4nil helpers
theorem R4_iter (d : ℕ) : ∀ (j r z w : ℕ) (l' : List (ℕ × ℕ)) (s : List ℕ),
    (Bev j ((z + 2 * d, w) :: l') (j + d + r) s) [tm]⊢* Bev (j + d) ((z, w) :: l') (j + d + r) s :=
        by
  induction d with
  | zero =>
    intro j r z w l' s
    simp only [Nat.mul_zero, Nat.add_zero]
    exact ss_refl _ _
  | succ d ih =>
    intro j r z w l' s
    have h_step := sp_to_ss (R4 j (d + r) (z + 2 * d) w l' s)
    have e_z : (z + 2 * d) + 2 = z + 2 * (d + 1) := by omega
    have e_m : j + 1 + (d + r) = j + (d + 1) + r := by omega
    rw [e_z, e_m] at h_step
    refine ss_trans h_step ?_
    have h2 := ih (j + 1) r z w l' s
    have e1 : j + 1 + d = j + (d + 1) := by omega
    rw [e1] at h2
    exact h2

theorem R4nil_iter (d : ℕ) : ∀ (j r : ℕ) (s : List ℕ),
    (Bev j [] (j + d + r) s) [tm]⊢* Bev (j + d) [] (j + d + r) s := by
  induction d with
  | zero =>
    intro j r s
    simp only [Nat.add_zero]
    exact ss_refl _ _
  | succ d ih =>
    intro j r s
    have h_step := sp_to_ss (R4nil j (d + r) s)
    have e_m : j + 1 + (d + r) = j + (d + 1) + r := by omega
    rw [e_m] at h_step
    refine ss_trans h_step ?_
    have h2 := ih (j + 1) r s
    have e1 : j + 1 + d = j + (d + 1) := by omega
    rw [e1] at h2
    exact h2

theorem bev0_nil_bounce (m' : ℕ) (s : List ℕ) :
    (Bev 0 [] (m' + 4) s) [tm]⊢⁺ Bounce m' [] s := by
  have h1 := R4nil_iter (m' + 4) 0 0 s
  simp only [Nat.zero_add, Nat.add_zero] at h1
  exact ss_sp_trans h1 (R5nil m' s)

-- ---------------------------------------------------------------------------
-- Stack-polymorphic linear excursion calculus & root invariant
-- ---------------------------------------------------------------------------

def ValidL (l : List (ℕ × ℕ)) : Prop := ∀ p ∈ l, 27 ≤ p.2

theorem validL_nil : ValidL [] := by
  intro p hp; cases hp

theorem validL_cons {z w : ℕ} {l : List (ℕ × ℕ)} (hw : 27 ≤ w) (hl : ValidL l) :
    ValidL ((z, w) :: l) := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hmem
  · exact hw
  · exact hl p hmem

theorem validL_head {z w : ℕ} {l : List (ℕ × ℕ)} (hl : ValidL ((z, w) :: l)) : 27 ≤ w :=
  hl (z, w) (List.mem_cons_self ..)

theorem validL_tail {z w : ℕ} {l : List (ℕ × ℕ)} (hl : ValidL ((z, w) :: l)) : ValidL l :=
  fun p hp => hl p (List.mem_cons_of_mem _ hp)

@[reducible] def bx (j m : ℕ) : ℕ := m - (5 * m - (4 * j + 165)) / 60 - 1
@[reducible] def bdw (j m : ℕ) : ℕ := bx j m - 5
@[reducible] def bxw (j m : ℕ) : ℕ := m + j / 15 + 27
@[reducible] def ox (k M : ℕ) : ℕ := M - (5 * M - (4 * k + 30)) / 60 - 2
@[reducible] def odw (k M : ℕ) : ℕ := ox k M - 5
@[reducible] def oxw (k M : ℕ) : ℕ := M + k / 15 + 55

local macro "lin_omega" : tactic =>
  `(tactic| (dsimp only [bx, bdw, bxw, ox, odw, oxw] at *; omega))

theorem div15_spec (n : ℕ) : ∃ q r : ℕ, r < 15 ∧ n = 15 * q + r ∧ n / 15 = q :=
  ⟨n / 15, n % 15, Nat.mod_lt n (by decide), (Nat.div_add_mod n 15).symm, rfl⟩

theorem bx_spec (j m : ℕ) :
    ∃ bxv : ℕ, bx j m = bxv ∧ bdw j m = bxv - 5 ∧
      ((5 * m ≤ 4 * j + 165 ∧ bxv = m - 1) ∨
       (∃ q r : ℕ, r < 60 ∧ 5 * m = 4 * j + 165 + 60 * q + r ∧ bxv = m - q - 1)) := by
  refine ⟨bx j m, rfl, rfl, ?_⟩
  dsimp only [bx]
  rcases Nat.lt_or_ge (4 * j + 165) (5 * m) with hgt | hle
  · right
    refine ⟨(5 * m - (4 * j + 165)) / 60, (5 * m - (4 * j + 165)) % 60,
      Nat.mod_lt _ (by decide), ?_, rfl⟩
    have hdm := Nat.div_add_mod (5 * m - (4 * j + 165)) 60
    omega
  · left
    exact ⟨hle, by rw [Nat.sub_eq_zero_of_le hle]; omega⟩

theorem ox_spec (k M : ℕ) :
    ∃ oxv : ℕ, ox k M = oxv ∧ odw k M = oxv - 5 ∧
      ((5 * M ≤ 4 * k + 30 ∧ oxv = M - 2) ∨
       (∃ q r : ℕ, r < 60 ∧ 5 * M = 4 * k + 30 + 60 * q + r ∧ oxv = M - q - 2)) := by
  refine ⟨ox k M, rfl, rfl, ?_⟩
  dsimp only [ox]
  rcases Nat.lt_or_ge (4 * k + 30) (5 * M) with hgt | hle
  · right
    refine ⟨(5 * M - (4 * k + 30)) / 60, (5 * M - (4 * k + 30)) % 60,
      Nat.mod_lt _ (by decide), ?_, rfl⟩
    have hdm := Nat.div_add_mod (5 * M - (4 * k + 30)) 60
    omega
  · left
    exact ⟨hle, by rw [Nat.sub_eq_zero_of_le hle]; omega⟩

def Exit (tx tdw txw : ℕ) (S : List ℕ) (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  (∃ w l, ValidL l ∧ 27 ≤ w ∧ tdw ≤ w ∧ c = Bounce w l S) ∨
  (∃ x w l, ValidL l ∧ 27 ≤ w ∧ tx ≤ x ∧ txw ≤ x + w ∧ c = Bounce w l (x :: S))

theorem exit_mono {tx₁ tdw₁ txw₁ tx₂ tdw₂ txw₂ : ℕ} {S : List ℕ} {c : Cfg (Fin 2) (Fin 6)}
    (h : Exit tx₂ tdw₂ txw₂ S c) (h1 : tx₁ ≤ tx₂) (h2 : tdw₁ ≤ tdw₂) (h3 : txw₁ ≤ txw₂) :
    Exit tx₁ tdw₁ txw₁ S c := by
  rcases h with ⟨w, l, hl, hw, htdw, rfl⟩ | ⟨x, w, l, hl, hw, htx, htxw, rfl⟩
  · exact Or.inl ⟨w, l, hl, hw, by omega, rfl⟩
  · exact Or.inr ⟨x, w, l, hl, hw, by omega, by omega, rfl⟩

def LeadsUpTo (N : ℕ) (c : Cfg (Fin 2) (Fin 6)) (P : Cfg (Fin 2) (Fin 6) → Prop) : Prop :=
  ∀ n, n ≤ N → HaltsIn tm c n → ∃ m d, m ≤ n ∧ P d ∧ HaltsIn tm d m

theorem leadsUpTo_here {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P : Cfg (Fin 2) (Fin 6) → Prop}
    (hc : P c) : LeadsUpTo N c P :=
  fun n _ hn => ⟨n, c, Nat.le_refl n, hc, hn⟩

theorem leadsUpTo_mono {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P Q : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : LeadsUpTo N c P) (h₂ : ∀ d, P d → Q d) : LeadsUpTo N c Q := by
  intro n hnN hn
  rcases h₁ n hnN hn with ⟨m, d, hmn, hPd, hm⟩
  exact ⟨m, d, hmn, h₂ d hPd, hm⟩

theorem leadsUpTo_trans {N : ℕ} {c : Cfg (Fin 2) (Fin 6)} {P Q : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : LeadsUpTo N c P) (h₂ : ∀ d, P d → LeadsUpTo N d Q) : LeadsUpTo N c Q := by
  intro n hnN hn
  rcases h₁ n hnN hn with ⟨m, d, hmn, hPd, hm⟩
  rcases h₂ d hPd m (Nat.le_trans hmn hnN) hm with ⟨k, e, hkm, hQe, hk⟩
  exact ⟨k, e, Nat.le_trans hkm hmn, hQe, hk⟩

theorem leadsUpTo_stepPlus {N : ℕ} {c₁ c₂ : Cfg (Fin 2) (Fin 6)} {P : Cfg (Fin 2) (Fin 6) → Prop}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : ∀ m, m < N → LeadsUpTo m c₂ P) : LeadsUpTo N c₁ P := by
  intro n hnN hn
  rcases haltsIn_reduce_stepPlus h₁ hn with ⟨m, hmn, hm⟩
  rcases h₂ m (Nat.lt_of_lt_of_le hmn hnN) m (Nat.le_refl m) hm with ⟨k, d, hkm, hPd, hk⟩
  exact ⟨k, d, Nat.le_trans hkm (Nat.le_of_lt hmn), hPd, hk⟩

def BevBound (N : ℕ) : Prop :=
  ∀ j l m S, ValidL l → j ≤ m → 35 ≤ m →
    LeadsUpTo N (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S)

def BoddBound (N : ℕ) : Prop :=
  ∀ k l M S, ValidL l → 28 ≤ k → k + 5 ≤ M → 36 ≤ M →
    LeadsUpTo N (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S)

def LoopBound (N : ℕ) : Prop :=
  ∀ kc lc Mc x tx tdw txw S,
    ValidL lc → 28 ≤ kc → kc + 5 ≤ Mc → 36 ≤ Mc →
    34 ≤ tx → tdw = tx - 5 → tx ≤ x →
    695 * tx + 27 ≤ 11 * (Mc + 61 * x) →
    60 * tx ≤ 2 * Mc + 55 * x + 200 →
    12 * txw + 72 ≤ 11 * Mc + 12 * x →
    30 * txw ≤ Mc + 30 * x + 1700 →
    LeadsUpTo N (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S)

theorem amega_bounce_step {N : ℕ}
    (ih : ∀ m, m < N → BevBound m ∧ BoddBound m ∧ LoopBound m)
    {z0 w1 x tx tdw txw : ℕ} {l1 : List (ℕ × ℕ)} {S : List ℕ}
    (hl1 : ValidL l1) (hw1 : 27 ≤ w1) (hz0_ge3 : 3 ≤ z0)
    (htx34 : 34 ≤ tx) (htdw : tdw = tx - 5) (htxx : tx ≤ x)
    (h_r10_tx : ∀ kp, z0 = 3 + kp * 2 → kp + 1 ≤ x → tx ≤ ox (kp + w1 + 2) (x + w1 + 6))
    (h_r10_txw : ∀ kp, z0 = 3 + kp * 2 → kp + 1 ≤ x → txw ≤ oxw (kp + w1 + 2) (x + w1 + 6))
    (h_r11_x : ∀ kp, z0 = 4 + kp * 2 → kp + 1 ≤ x → tx ≤ x - 1)
    (h_r11_i1 : ∀ kp,
        z0 = 4 + kp * 2 → kp + 1 ≤ x → 695 * tx + 27 ≤ 11 * ((2 * kp + w1 + 9) + 61 * (x - 1)))
    (h_r11_i2 : ∀ kp,
        z0 = 4 + kp * 2 → kp + 1 ≤ x → 60 * tx ≤ 2 * (2 * kp + w1 + 9) + 55 * (x - 1) + 200)
    (h_r11_i3 : ∀ kp,
        z0 = 4 + kp * 2 → kp + 1 ≤ x → 12 * txw + 72 ≤ 11 * (2 * kp + w1 + 9) + 12 * (x - 1))
    (h_r11_i4 : ∀ kp,
        z0 = 4 + kp * 2 → kp + 1 ≤ x → 30 * txw ≤ (2 * kp + w1 + 9) + 30 * (x - 1) + 1700) :
    LeadsUpTo N (Bounce w1 l1 (z0 :: x :: S)) (Exit tx tdw txw S) := by
  rcases Nat.lt_or_ge (z0 - 3) (2 * x) with hlt | hge
  · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
    · have hz_eq : z0 = 3 + kp * 2 := by omega
      have hkpx : kp + 1 ≤ x := by omega
      have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bodd (kp + w1 + 2) l1 (x + w1 + 6) S := by
        have h1 : Bounce w1 l1 (z0 :: x :: S) =
            Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (x - (kp + 1))) :: S) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h2 := sp_trans (R15 w1 (2 * kp) (kp + 1 + (x - (kp + 1))) l1 S)
          (R10 kp (x - (kp + 1)) w1 l1 S)
        have e1 : kp + 1 + (x - (kp + 1)) + w1 + 6 = x + w1 + 6 := by omega
        rwa [e1] at h2
      refine leadsUpTo_stepPlus h_step (fun m hm => ?_)
      have hb := (ih m hm).2.1 (kp + w1 + 2) l1 (x + w1 + 6) S hl1 (by omega) (by omega) (by omega)
      refine leadsUpTo_mono hb (fun d hd => ?_)
      have htx' := h_r10_tx kp hz_eq hkpx
      have htxw' := h_r10_txw kp hz_eq hkpx
      exact exit_mono hd htx' (by dsimp only [odw]; omega) htxw'
    · have hz_eq : z0 = 4 + kp * 2 := by omega
      have hkpx : kp + 1 ≤ x := by omega
      have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bodd (w1 + 1) l1 (2 * kp + w1 + 9) ((x - 1)
          :: S) := by
        have h1 : Bounce w1 l1 (z0 :: x :: S) =
            Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (x - (kp + 1))) :: S) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h2 := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (x - (kp + 1))) l1 S)
          (R11 kp (x - (kp + 1)) w1 l1 S)
        have e1 : kp + (x - (kp + 1)) = x - 1 := by omega
        rwa [e1] at h2
      refine leadsUpTo_stepPlus h_step (fun m hm => ?_)
      exact (ih m hm).2.2 (w1 + 1) l1 (2 * kp + w1 + 9) (x - 1) tx tdw txw S
        hl1 (by omega) (by omega) (by omega) htx34 htdw
        (h_r11_x kp hz_eq hkpx) (h_r11_i1 kp hz_eq hkpx)
        (h_r11_i2 kp hz_eq hkpx) (h_r11_i3 kp hz_eq hkpx) (h_r11_i4 kp hz_eq hkpx)
  · have h_step : (Bounce w1 l1 (z0 :: x :: S)) [tm]⊢⁺ Bounce (x - 5) ((z0 - 3 - 2 * x,
      w1) :: l1) S := by
      have h1 : Bounce w1 l1 (z0 :: x :: S) =
          Bounce w1 l1 (((2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) + 3) :: ((x - 5) + 5) :: S) := by
        congr 1; congr 1
        · omega
        · congr 1; omega
      rw [h1]
      exact sp_trans (R15 w1 (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l1 S)
        (R9 (x - 5) (z0 - 3 - 2 * x) w1 l1 S)
    refine leadsUpTo_stepPlus h_step (fun m _ => ?_)
    exact leadsUpTo_here (Or.inl ⟨x - 5, (z0 - 3 - 2 * x, w1) :: l1,
      validL_cons hw1 hl1, by omega, by omega, rfl⟩)

theorem excursion_bundle (N : ℕ) : BevBound N ∧ BoddBound N ∧ LoopBound N := by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    have h_bev : BevBound N := by
      intro j l m S hl hjm hm35
      rcases l with _ | ⟨⟨z, w⟩, l'⟩
      · rcases Nat.lt_or_ge j m with hlt | hge
        · have h_eq : Bev j [] m S = Bev j [] (j + 1 + (m - (j + 1))) S := by congr 1; omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R4nil j (m - (j + 1)) S) (fun n' hn' => ?_)
          have h_sub : j + 1 + (m - (j + 1)) = m := by omega
          rw [h_sub]
          refine leadsUpTo_mono ((ih n' hn').1 (j + 1) [] m S validL_nil (by omega) hm35) (fun d hd
              => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · have hjm_eq : j = m := by omega
          subst hjm_eq
          have h_eq : Bev j [] j S = Bev ((j - 4) + 4) [] ((j - 4) + 4) S := by congr 1 <;> omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R5nil (j - 4) S) (fun _ _ => ?_)
          exact leadsUpTo_here (Or.inl ⟨j - 4, [], validL_nil, by omega, by lin_omega, rfl⟩)
      · have hw : 27 ≤ w := validL_head hl
        have hl' : ValidL l' := validL_tail hl
        rcases z with _ | _ | z'
        · refine leadsUpTo_stepPlus (R6 j m w l' S) (fun n' hm' => ?_)
          refine leadsUpTo_mono ((ih n' hm').2.1 (j + w + 2) l' (m + w + 7) S hl'
            (by omega) (by omega) (by omega)) (fun d hd => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · refine leadsUpTo_stepPlus (R7 j m w l' S) (fun n' hn' => ?_)
          have hb_all : 34 ≤ bx j m ∧ bx j m ≤ m ∧
              695 * bx j m + 27 ≤ 11 * ((2 * j + w + 9) + 61 * m) ∧
              60 * bx j m ≤ 2 * (2 * j + w + 9) + 55 * m + 200 ∧
              12 * bxw j m + 72 ≤ 11 * (2 * j + w + 9) + 12 * m ∧
              30 * bxw j m ≤ (2 * j + w + 9) + 30 * m + 1700 := by
            rcases bx_spec j m with ⟨bxv, hbxv, _, hbx_cases⟩
            rcases div15_spec j with ⟨qj, rj, hrj, hjeq, hjdiv⟩
            dsimp only [bxw]
            rw [hbxv, hjdiv]
            rcases hbx_cases with ⟨hle, rfl⟩ | ⟨q, r, hr, heq, rfl⟩
            · omega
            · refine ⟨by omega, by omega, ?_, by omega, by omega, by omega⟩
              rcases j with _ | _ | _ | _ | j' <;> omega
          exact (ih n' hn').2.2 (w + 1) l' (2 * j + w + 9) m (bx j m) (bdw j m) (bxw j m) S
            hl' (by omega) (by omega) (by omega) hb_all.1 rfl hb_all.2.1
            hb_all.2.2.1 hb_all.2.2.2.1 hb_all.2.2.2.2.1 hb_all.2.2.2.2.2
        · rcases Nat.lt_or_ge j m with hlt | hge
          · have h_eq : Bev j ((z' + 2, w) :: l') m S =
                Bev j ((z' + 2, w) :: l') (j + 1 + (m - (j + 1))) S := by congr 1; omega
            rw [h_eq]
            refine leadsUpTo_stepPlus (R4 j (m - (j + 1)) z' w l' S) (fun n' hn' => ?_)
            have h_sub : j + 1 + (m - (j + 1)) = m := by omega
            rw [h_sub]
            refine leadsUpTo_mono ((ih n' hn').1 (j + 1) ((z', w) :: l') m S
              (validL_cons hw hl') (by omega) hm35) (fun d hd => ?_)
            exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
          · have hjm_eq : j = m := by omega
            subst hjm_eq
            have h_eq : Bev j ((z' + 2, w) :: l') j S =
                Bev ((j - 4) + 4) ((z' + 2, w) :: l') ((j - 4) + 4) S := by congr 1 <;> omega
            rw [h_eq]
            refine leadsUpTo_stepPlus (R5 (j - 4) z' w l' S) (fun _ _ => ?_)
            exact leadsUpTo_here (Or.inl ⟨j - 4, (z', w) :: l', validL_cons hw hl',
              by omega, by lin_omega, rfl⟩)
    have h_bodd : BoddBound N := by
      intro k l M S hl hk28 hkM hM36
      have h_r8_post : ∀ (l'' : List (ℕ × ℕ)), ValidL l'' →
          ∀ m', m' < N → LeadsUpTo m' (Bev 0 l'' (2 * k + 11) ((M - 1) :: S))
            (Exit (ox k M) (odw k M) (oxw k M) S) := by
        intro l'' hl'' m' hm'
        refine leadsUpTo_trans ((ih m' hm').1 0 l'' (2 * k + 11) ((M - 1) :: S) hl'' (by omega) (by
            omega)) ?_
        rintro d (⟨w1, l1, hl1, hw1, hbdw, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hbx, hbxw, rfl⟩)
        · rcases bx_spec 0 (2 * k + 11) with ⟨bxv, _, hbdwv, hbx_c⟩
          rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
          rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
          rw [hbdwv] at hbdw
          refine leadsUpTo_here (Or.inr ⟨M - 1, w1, l1, hl1, hw1, ?_, ?_, rfl⟩)
          · rw [hoxv]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
          · dsimp only [oxw]; rw [hkdiv]
            rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
        · have hz3 : 3 ≤ z0 := by lin_omega
          have hox34 : 34 ≤ ox k M := by lin_omega
          have hoxM : ox k M ≤ M - 1 := by lin_omega
          exact amega_bounce_step (fun m'' hm'' => ih m'' (Nat.lt_trans hm'' hm'))
            hl1 hw1 hz3 hox34 rfl hoxM
            (fun kp hz hkpx => by
              rcases bx_spec 0 (2 * k + 11) with ⟨bxv, hbxv, _, hbx_c⟩
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              rcases ox_spec (kp + w1 + 2) ((M - 1) + w1 + 6) with ⟨ox2, hox2, _, hox2_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hbxv] at hbx; rw [hoxv, hox2]
              rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox2_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              rcases div15_spec (kp + w1 + 2) with ⟨qo, ro, hro, hoeq, hodiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv, hodiv]; omega)
            (fun kp hz hkpx => by
              rcases bx_spec 0 (2 * k + 11) with ⟨bxv, hbxv, _, hbx_c⟩
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              rw [hbxv] at hbx; rw [hoxv]
              rcases hbx_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
                rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hoxv]
              rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
              dsimp only [bxw] at hbxw
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hoxv]
              rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv]; omega)
            (fun kp hz hkpx => by
              rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
              dsimp only [bxw, oxw] at hbxw ⊢
              have h0 : 0 / 15 = 0 := rfl
              rw [h0] at hbxw; rw [hkdiv]; omega)
      rcases l with _ | ⟨⟨z, w⟩, l'⟩
      · have h_eq : Bodd k [] M S = Bodd k [] (k + 5 + (M - (k + 5))) S := by congr 1; omega
        rw [h_eq]
        refine leadsUpTo_stepPlus (R8nil k (M - (k + 5)) S) (fun m' hm' => ?_)
        have e1 : k + 4 + (M - (k + 5)) = M - 1 := by omega
        rw [e1]
        exact h_r8_post [] validL_nil m' hm'
      · have hw : 27 ≤ w := validL_head hl
        have hl' : ValidL l' := validL_tail hl
        rcases z with _ | _ | z'
        · refine leadsUpTo_stepPlus (R8a k M w l' S) (fun m' hm' => ?_)
          refine leadsUpTo_mono ((ih m' hm').1 (k + w + 11) l' (M + w + 7) S hl'
            (by omega) (by omega)) (fun d hd => ?_)
          exact exit_mono hd (by lin_omega) (by lin_omega) (by lin_omega)
        · refine leadsUpTo_stepPlus (R8b k M w l' S) (fun m' hm' => ?_)
          have ho_all : 34 ≤ ox k M ∧ ox k M ≤ M ∧
              695 * ox k M + 27 ≤ 11 * ((2 * k + w + 18) + 61 * M) ∧
              60 * ox k M ≤ 2 * (2 * k + w + 18) + 55 * M + 200 ∧
              12 * oxw k M + 72 ≤ 11 * (2 * k + w + 18) + 12 * M ∧
              30 * oxw k M ≤ (2 * k + w + 18) + 30 * M + 1700 := by
            rcases ox_spec k M with ⟨oxv, hoxv, _, hox_c⟩
            rcases div15_spec k with ⟨qk, rk, hrk, hkeq, hkdiv⟩
            dsimp only [oxw]
            rw [hoxv, hkdiv]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
          exact (ih m' hm').2.2 (w + 1) l' (2 * k + w + 18) M (ox k M) (odw k M) (oxw k M) S
            hl' (by omega) (by omega) (by omega) ho_all.1 rfl ho_all.2.1
            ho_all.2.2.1 ho_all.2.2.2.1 ho_all.2.2.2.2.1 ho_all.2.2.2.2.2
        · have h_eq : Bodd k ((z' + 2, w) :: l') M S =
              Bodd k ((z' + 2, w) :: l') (k + 5 + (M - (k + 5))) S := by congr 1; omega
          rw [h_eq]
          refine leadsUpTo_stepPlus (R8 k (M - (k + 5)) z' w l' S) (fun m' hm' => ?_)
          have e1 : k + 4 + (M - (k + 5)) = M - 1 := by omega
          rw [e1]
          exact h_r8_post ((z', w) :: l') (validL_cons hw hl') m' hm'
    have h_loop : LoopBound N := by
      intro kc lc Mc x tx tdw txw S hlc hkc28 hkcMc hMc36 htx34 htdw htxx hi1 hi2 hi3 hi4
      refine leadsUpTo_trans (h_bodd kc lc Mc (x :: S) hlc hkc28 hkcMc hMc36) ?_
      rintro d (⟨w1, l1, hl1, hw1, hodw, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hox, hoxw, rfl⟩)
      · rcases ox_spec kc Mc with ⟨oxv, _, hodwv, hox_c⟩
        rw [hodwv] at hodw
        refine leadsUpTo_here (Or.inr ⟨x, w1, l1, hl1, hw1, htxx, ?_, rfl⟩)
        rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega
      · have hz3 : 3 ≤ z0 := by lin_omega
        exact amega_bounce_step ih hl1 hw1 hz3 htx34 htdw htxx
          (fun kp hz hkpx => by
            rcases ox_spec kc Mc with ⟨oxv, hoxv, _, hox_c⟩
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            rcases ox_spec (kp + w1 + 2) (x + w1 + 6) with ⟨ox2, hox2, _, hox2_c⟩
            dsimp only [oxw] at hoxw
            rw [hoxv] at hox; rw [hkcdiv] at hoxw; rw [hox2]
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;>
              rcases hox2_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            rcases div15_spec (kp + w1 + 2) with ⟨qo, ro, hro, hoeq, hodiv⟩
            dsimp only [oxw] at hoxw ⊢
            rw [hkcdiv] at hoxw; rw [hodiv]; omega)
          (fun kp hz hkpx => by
            rcases ox_spec kc Mc with ⟨oxv, hoxv, _, hox_c⟩
            rw [hoxv] at hox
            rcases hox_c with ⟨_, rfl⟩ | ⟨_, _, _, _, rfl⟩ <;> omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
          (fun kp hz hkpx => by
            rcases div15_spec kc with ⟨qkc, rkc, hrkc, hkceq, hkcdiv⟩
            dsimp only [oxw] at hoxw
            rw [hkcdiv] at hoxw; omega)
    exact ⟨h_bev, h_bodd, h_loop⟩

theorem bev_leads {j m : ℕ} {l : List (ℕ × ℕ)} {S : List ℕ}
    (hl : ValidL l) (hjm : j ≤ m) (hm35 : 35 ≤ m) :
    Leads tm (Bev j l m S) (Exit (bx j m) (bdw j m) (bxw j m) S) :=
  fun n hn => (excursion_bundle n).1 j l m S hl hjm hm35 n (Nat.le_refl n) hn

theorem bodd_leads {k M : ℕ} {l : List (ℕ × ℕ)} {S : List ℕ}
    (hl : ValidL l) (hk28 : 28 ≤ k) (hkM : k + 5 ≤ M) (hM36 : 36 ≤ M) :
    Leads tm (Bodd k l M S) (Exit (ox k M) (odw k M) (oxw k M) S) :=
  fun n hn => (excursion_bundle n).2.1 k l M S hl hk28 hkM hM36 n (Nat.le_refl n) hn

theorem loop_leads {kc Mc x tx tdw txw : ℕ} {lc : List (ℕ × ℕ)} {S : List ℕ}
    (hlc : ValidL lc) (hkc28 : 28 ≤ kc) (hkcMc : kc + 5 ≤ Mc) (hMc36 : 36 ≤ Mc)
    (htx34 : 34 ≤ tx) (htdw : tdw = tx - 5) (htxx : tx ≤ x)
    (hi1 : 695 * tx + 27 ≤ 11 * (Mc + 61 * x))
    (hi2 : 60 * tx ≤ 2 * Mc + 55 * x + 200)
    (hi3 : 12 * txw + 72 ≤ 11 * Mc + 12 * x)
    (hi4 : 30 * txw ≤ Mc + 30 * x + 1700) :
    Leads tm (Bodd kc lc Mc (x :: S)) (Exit tx tdw txw S) :=
  fun n hn => (excursion_bundle n).2.2 kc lc Mc x tx tdw txw S
    hlc hkc28 hkcMc hMc36 htx34 htdw htxx hi1 hi2 hi3 hi4 n (Nat.le_refl n) hn

-- ---------------------------------------------------------------------------
-- Root invariant closure (`RootInv`)
-- ---------------------------------------------------------------------------

def RootInv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ M l, (M = 5 ∨ 18 ≤ M) ∧ ValidL l ∧ c = Beq M l

theorem root_of_5 {l : List (ℕ × ℕ)} (hl : ValidL l) : RootInv (Beq 5 l) :=
  ⟨5, l, Or.inl rfl, hl, rfl⟩

theorem root_of_ge18 {M : ℕ} {l : List (ℕ × ℕ)} (hM : 18 ≤ M) (hl : ValidL l) : RootInv (Beq M l) :=
  ⟨M, l, Or.inr hM, hl, rfl⟩

theorem exit_nil_leads_root {tx tdw txw : ℕ} (htx : 15 ≤ tx) {c : Cfg (Fin 2) (Fin 6)}
    (hc : Exit tx tdw txw [] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨x, w, l, hl, hw, hxx, _, rfl⟩
  · exact (Advances.of_stepPlus (R12 w l) (root_of_ge18 (by omega) hl)).to_leads
  · have h_eq : Bounce w l [x] = Bounce w l [(x - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w (x - 15) l) (root_of_5 (validL_cons hw hl))).to_leads

theorem bev_nil_leads_root {j m : ℕ} {l : List (ℕ × ℕ)}
    (hl : ValidL l) (hjm : j ≤ m) (hm35 : 35 ≤ m) :
    Leads tm (Bev j l m []) RootInv :=
  (bev_leads hl hjm hm35).trans (fun _ hd => exit_nil_leads_root (by lin_omega) hd)

theorem bodd_nil_leads_root {k M : ℕ} {l : List (ℕ × ℕ)}
    (hl : ValidL l) (hk28 : 28 ≤ k) (hkM : k + 5 ≤ M) (hM36 : 36 ≤ M) :
    Leads tm (Bodd k l M []) RootInv :=
  (bodd_leads hl hk28 hkM hM36).trans (fun _ hd => exit_nil_leads_root (by lin_omega) hd)

theorem exit_single_forced_r9 {tx tdw txw x : ℕ} (hx18 : 18 ≤ x) (htx_r9 : 2 * x + 3 ≤ tx)
    {c : Cfg (Fin 2) (Fin 6)} (hc : Exit tx tdw txw [x] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨z0, w, l, hl, hw, hz0, _, rfl⟩
  · have h_eq : Bounce w l [x] = Bounce w l [(x - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w (x - 15) l) (root_of_5 (validL_cons hw hl))).to_leads
  · have h_step := sp_trans
      (sp_trans (R15 w (2 * ((x - 5) + 5) + (z0 - 3 - 2 * x)) ((x - 5) + 5) l [])
        (R9 (x - 5) (z0 - 3 - 2 * x) w l []))
      (R12 (x - 5) ((z0 - 3 - 2 * x, w) :: l))
    have e1 : 2 * ((x - 5) + 5) + (z0 - 3 - 2 * x) + 3 = z0 := by omega
    have e2 : (x - 5) + 5 = x := by omega
    rw [e1, e2] at h_step
    exact (Advances.of_stepPlus h_step (root_of_ge18 hx18 (validL_cons hw hl))).to_leads

theorem exit_5_leads_root {tx tdw txw : ℕ} (htx : 13 ≤ tx) {c : Cfg (Fin 2) (Fin 6)}
    (hc : Exit tx tdw txw [5] c) : Leads tm c RootInv := by
  rcases hc with ⟨w, l, hl, hw, _, rfl⟩ | ⟨z0, w, l, hl, hw, hz0, _, rfl⟩
  · exact Leads.of_stepPlus_leads (R13 w l)
      (bodd_nil_leads_root hl (by omega) (by omega) (by omega))
  · have h1 : Bounce w l [z0, 5] = Bounce w l (((2 * (0 + 5) + (z0 - 13)) + 3) :: (0 + 5) :: []) :=
      by
      congr 1; congr 1; omega
    rw [h1]
    have h_step := sp_trans
      (sp_trans (R15 w (2 * (0 + 5) + (z0 - 13)) (0 + 5) l [])
        (R9 0 (z0 - 13) w l []))
      (R12 0 ((z0 - 13, w) :: l))
    exact (Advances.of_stepPlus h_step (root_of_5 (validL_cons hw hl))).to_leads
theorem bev0_35_20_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bev 0 l 35 [20]) RootInv := by
  refine (bev_leads hl (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
  · exact (Advances.of_stepPlus (R14 w1 5 l1) (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    have hzw62 : 62 ≤ z0 + w1 := by lin_omega
    rcases Nat.lt_or_ge (z0 - 3) 40 with hlt | hge
    · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
      · have h1 : Bounce w1 l1 [z0, 20] =
            Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (20 - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R10 kp (20 - (kp + 1)) w1 l1 [])
        have e1 : kp + 1 + (20 - (kp + 1)) + w1 + 6 = w1 + 26 := by omega
        rw [e1] at h_step
        exact Leads.of_stepPlus_leads h_step
          (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
      · have h1 : Bounce w1 l1 [z0, 20] =
            Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (20 - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (20 - (kp + 1))) l1 [])
          (R11 kp (20 - (kp + 1)) w1 l1 [])
        have e1 : kp + (20 - (kp + 1)) = 19 := by omega
        rw [e1] at h_step
        refine Leads.of_stepPlus_leads h_step ?_
        exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · have h1 : Bounce w1 l1 [z0, 20] =
          Bounce w1 l1 (((2 * (15 + 5) + (z0 - 43)) + 3) :: (15 + 5) :: []) := by
        congr 1; congr 1; omega
      rw [h1]
      have h_step := sp_trans
        (sp_trans (R15 w1 (2 * (15 + 5) + (z0 - 43)) (15 + 5) l1 [])
          (R9 15 (z0 - 43) w1 l1 []))
        (R12 15 ((z0 - 43, w1) :: l1))
      exact (Advances.of_stepPlus h_step (root_of_ge18 (by omega) (validL_cons hw1 hl1))).to_leads

theorem bodd12_21_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bodd 12 l 21 []) RootInv := by
  rcases l with _ | ⟨⟨z, w⟩, l'⟩
  · exact Leads.of_stepPlus_leads (R8nil 12 4 []) (bev0_35_20_leads_root validL_nil)
  · have hw : 27 ≤ w := validL_head hl
    have hl' : ValidL l' := validL_tail hl
    rcases z with _ | _ | z'
    · exact Leads.of_stepPlus_leads (R8a 12 21 w l' [])
        (bev_nil_leads_root hl' (by omega) (by omega))
    · refine Leads.of_stepPlus_leads (R8b 12 21 w l' []) ?_
      exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
        (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · exact Leads.of_stepPlus_leads (R8 12 4 z' w l' [])
        (bev0_35_20_leads_root (validL_cons hw hl'))

theorem bev_33_19_walk (rem : ℕ) : ∀ {j : ℕ} {l : List (ℕ × ℕ)},
    rem = 33 - j → j ≤ 33 → ValidL l → Leads tm (Bev j l 33 [19]) RootInv := by
  induction rem with
  | zero =>
    intro j l hrem hj hl
    have hj33 : j = 33 := by omega
    subst hj33
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · exact (Advances.of_stepPlus (sp_trans (R5nil 29 [19]) (R14 29 4 []))
        (root_of_5 (validL_cons (by omega) validL_nil))).to_leads
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 33 33 w l' [19]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
      · refine Leads.of_stepPlus_leads (R7 33 33 w l' [19]) ?_
        refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
        rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
        · have h_step := sp_trans (R15 w1 30 19 l1 []) (R10 15 3 w1 l1 [])
          exact Leads.of_stepPlus_leads h_step
            (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
        · have hz34 : 34 ≤ z0 := by lin_omega
          have hzw92 : 92 ≤ z0 + w1 := by lin_omega
          rcases Nat.lt_or_ge (z0 - 3) 66 with hlt | hge
          · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R10 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + 1 + (33 - (kp + 1)) + w1 + 6 = w1 + 39 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
                (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R11 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + (33 - (kp + 1)) = 32 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              refine (bodd_leads hl1 (by omega) (by omega) (by omega)).trans ?_
              rintro d2 (⟨w2, l2, hl2, hw2, hodw2, rfl⟩ | ⟨z2, w2, l2, hl2, hw2, hz2, _, rfl⟩)
              · have hw85 : 85 ≤ w2 := by lin_omega
                have h_s2 := sp_trans (R15 w2 29 19 l2 []) (R11 14 4 w2 l2 [])
                refine Leads.of_stepPlus_leads h_s2 ?_
                exact (bodd_leads hl2 (by omega) (by omega) (by omega)).trans
                  (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
              · have hz90 : 90 ≤ z2 := by lin_omega
                have h2 : Bounce w2 l2 [z2, 32, 19] =
                    Bounce w2 l2 (((2 * (27 + 5) + (z2 - 67)) + 3) :: (27 + 5) :: [19]) := by
                  congr 1; congr 1; omega
                rw [h2]
                have h_s2 := sp_trans
                  (sp_trans (R15 w2 (2 * (27 + 5) + (z2 - 67)) (27 + 5) l2 [19])
                    (R9 27 (z2 - 67) w2 l2 [19]))
                  (R14 27 4 ((z2 - 67, w2) :: l2))
                exact (Advances.of_stepPlus h_s2
                  (root_of_5 (validL_cons (by omega) (validL_cons hw2 hl2)))).to_leads
          · have h1 : Bounce w1 l1 [z0, 33, 19] =
                Bounce w1 l1 (((2 * (28 + 5) + (z0 - 69)) + 3) :: (28 + 5) :: [19]) := by
              congr 1; congr 1; omega
            rw [h1]
            have h_step := sp_trans
              (sp_trans (R15 w1 (2 * (28 + 5) + (z0 - 69)) (28 + 5) l1 [19])
                (R9 28 (z0 - 69) w1 l1 [19]))
              (R14 28 4 ((z0 - 69, w1) :: l1))
            exact (Advances.of_stepPlus h_step
              (root_of_5 (validL_cons (by omega) (validL_cons hw1 hl1)))).to_leads
      · exact (Advances.of_stepPlus (sp_trans (R5 29 z' w l' [19]) (R14 29 4 ((z', w) :: l')))
          (root_of_5 (validL_cons (by omega) (validL_cons hw hl')))).to_leads
  | succ rem ih =>
    intro j l hrem hj hl
    have hj_lt : j < 33 := by omega
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Bev j [] 33 [19] = Bev j [] (j + 1 + (32 - j)) [19] := by congr 1; omega
      rw [h_eq]
      refine Leads.of_stepPlus_leads (R4nil j (32 - j) [19]) ?_
      have e1 : j + 1 + (32 - j) = 33 := by omega
      rw [e1]
      exact ih (by omega) (by omega) validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 j 33 w l' [19]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
      · refine Leads.of_stepPlus_leads (R7 j 33 w l' [19]) ?_
        refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
        rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
        · have h_step := sp_trans (R15 w1 30 19 l1 []) (R10 15 3 w1 l1 [])
          exact Leads.of_stepPlus_leads h_step
            (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
        · have hz34 : 34 ≤ z0 := by lin_omega
          have hzw92 : 92 ≤ z0 + w1 := by lin_omega
          rcases Nat.lt_or_ge (z0 - 3) 66 with hlt | hge
          · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R10 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + 1 + (33 - (kp + 1)) + w1 + 6 = w1 + 39 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
                (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
            · have h1 : Bounce w1 l1 [z0, 33, 19] =
                  Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (33 - (kp + 1))) :: [19]) := by
                congr 1; congr 1
                · omega
                · congr 1; omega
              rw [h1]
              have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (33 - (kp + 1))) l1 [19])
                (R11 kp (33 - (kp + 1)) w1 l1 [19])
              have e1 : kp + (33 - (kp + 1)) = 32 := by omega
              rw [e1] at h_step
              refine Leads.of_stepPlus_leads h_step ?_
              refine (bodd_leads hl1 (by omega) (by omega) (by omega)).trans ?_
              rintro d2 (⟨w2, l2, hl2, hw2, hodw2, rfl⟩ | ⟨z2, w2, l2, hl2, hw2, hz2, _, rfl⟩)
              · have hw85 : 85 ≤ w2 := by lin_omega
                have h_s2 := sp_trans (R15 w2 29 19 l2 []) (R11 14 4 w2 l2 [])
                refine Leads.of_stepPlus_leads h_s2 ?_
                exact (bodd_leads hl2 (by omega) (by omega) (by omega)).trans
                  (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
              · have hz90 : 90 ≤ z2 := by lin_omega
                have h2 : Bounce w2 l2 [z2, 32, 19] =
                    Bounce w2 l2 (((2 * (27 + 5) + (z2 - 67)) + 3) :: (27 + 5) :: [19]) := by
                  congr 1; congr 1; omega
                rw [h2]
                have h_s2 := sp_trans
                  (sp_trans (R15 w2 (2 * (27 + 5) + (z2 - 67)) (27 + 5) l2 [19])
                    (R9 27 (z2 - 67) w2 l2 [19]))
                  (R14 27 4 ((z2 - 67, w2) :: l2))
                exact (Advances.of_stepPlus h_s2
                  (root_of_5 (validL_cons (by omega) (validL_cons hw2 hl2)))).to_leads
          · have h1 : Bounce w1 l1 [z0, 33, 19] =
                Bounce w1 l1 (((2 * (28 + 5) + (z0 - 69)) + 3) :: (28 + 5) :: [19]) := by
              congr 1; congr 1; omega
            rw [h1]
            have h_step := sp_trans
              (sp_trans (R15 w1 (2 * (28 + 5) + (z0 - 69)) (28 + 5) l1 [19])
                (R9 28 (z0 - 69) w1 l1 [19]))
              (R14 28 4 ((z0 - 69, w1) :: l1))
            exact (Advances.of_stepPlus h_step
              (root_of_5 (validL_cons (by omega) (validL_cons hw1 hl1)))).to_leads
      · have h_eq : Bev j ((z' + 2, w) :: l') 33 [19] =
            Bev j ((z' + 2, w) :: l') (j + 1 + (32 - j)) [19] := by congr 1; omega
        rw [h_eq]
        refine Leads.of_stepPlus_leads (R4 j (32 - j) z' w l' [19]) ?_
        have e1 : j + 1 + (32 - j) = 33 := by omega
        rw [e1]
        exact ih (by omega) (by omega) (validL_cons hw hl')

theorem bodd11_20_leads_root {l : List (ℕ × ℕ)} (hl : ValidL l) :
    Leads tm (Bodd 11 l 20 []) RootInv := by
  rcases l with _ | ⟨⟨z, w⟩, l'⟩
  · exact Leads.of_stepPlus_leads (R8nil 11 4 []) (bev_33_19_walk 33 rfl (by omega) validL_nil)
  · have hw : 27 ≤ w := validL_head hl
    have hl' : ValidL l' := validL_tail hl
    rcases z with _ | _ | z'
    · exact Leads.of_stepPlus_leads (R8a 11 20 w l' [])
        (bev_nil_leads_root hl' (by omega) (by omega))
    · refine Leads.of_stepPlus_leads (R8b 11 20 w l' []) ?_
      exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
        (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
    · exact Leads.of_stepPlus_leads (R8 11 4 z' w l' [])
        (bev_33_19_walk 33 rfl (by omega) (validL_cons hw hl'))

theorem r7_14_5_leads_root {j w : ℕ} {l' : List (ℕ × ℕ)} (hj : j ≤ 14) (hw : 27 ≤ w) (hl' : ValidL
    l') :
    Leads tm (Bev j ((1, w) :: l') 14 [5]) RootInv := by
  refine Leads.of_stepPlus_leads (R7 j 14 w l' [5]) ?_
  refine (bodd_leads hl' (by omega) (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, _, rfl⟩)
  · have h_step := sp_trans (sp_trans (R15 w1 11 5 l1 []) (R9 0 1 w1 l1 [])) (R12 0 ((1, w1) :: l1))
    exact (Advances.of_stepPlus h_step (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    have h1 : Bounce w1 l1 [z0, 14, 5] =
        Bounce w1 l1 (((2 * (9 + 5) + (z0 - 31)) + 3) :: (9 + 5) :: [5]) := by
      congr 1; congr 1; omega
    rw [h1]
    have h_step := sp_trans
      (sp_trans (R15 w1 (2 * (9 + 5) + (z0 - 31)) (9 + 5) l1 [5])
        (R9 9 (z0 - 31) w1 l1 [5]))
      (R13 9 ((z0 - 31, w1) :: l1))
    exact Leads.of_stepPlus_leads h_step (bodd11_20_leads_root (validL_cons hw1 hl1))

theorem bev_14_5_walk (rem : ℕ) : ∀ {j : ℕ} {l : List (ℕ × ℕ)},
    rem = 14 - j → j ≤ 14 → ValidL l → Leads tm (Bev j l 14 [5]) RootInv := by
  induction rem with
  | zero =>
    intro j l hrem hj hl
    have hj14 : j = 14 := by omega
    subst hj14
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · exact Leads.of_stepPlus_leads (sp_trans (R5nil 10 [5]) (R13 10 []))
        (bodd12_21_leads_root validL_nil)
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 14 14 w l' [5]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact r7_14_5_leads_root (by omega) hw hl'
      · exact Leads.of_stepPlus_leads (sp_trans (R5 10 z' w l' [5]) (R13 10 ((z', w) :: l')))
          (bodd12_21_leads_root (validL_cons hw hl'))
  | succ rem ih =>
    intro j l hrem hj hl
    rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Bev j [] 14 [5] = Bev j [] (j + 1 + (13 - j)) [5] := by congr 1; omega
      rw [h_eq]
      refine Leads.of_stepPlus_leads (R4nil j (13 - j) [5]) ?_
      have e1 : j + 1 + (13 - j) = 14 := by omega
      rw [e1]
      exact ih (by omega) (by omega) validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · refine Leads.of_stepPlus_leads (R6 j 14 w l' [5]) ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact r7_14_5_leads_root hj hw hl'
      · have h_eq : Bev j ((z' + 2, w) :: l') 14 [5] =
            Bev j ((z' + 2, w) :: l') (j + 1 + (13 - j)) [5] := by congr 1; omega
        rw [h_eq]
        refine Leads.of_stepPlus_leads (R4 j (13 - j) z' w l' [5]) ?_
        have e1 : j + 1 + (13 - j) = 14 := by omega
        rw [e1]
        exact ih (by omega) (by omega) (validL_cons hw hl')

theorem bev0_ge18_leads_root {M : ℕ} {l : List (ℕ × ℕ)} (hM18 : 18 ≤ M) (hl : ValidL l) :
    Leads tm (Bev 0 l (2 * M + 4) [M]) RootInv := by
  refine (bev_leads hl (by omega) (by omega)).trans ?_
  rintro d (⟨w1, l1, hl1, hw1, _, rfl⟩ | ⟨z0, w1, l1, hl1, hw1, hz0, hzw, rfl⟩)
  · have h_eq : Bounce w1 l1 [M] = Bounce w1 l1 [(M - 15) + 15] := by
      congr 1; congr 1; omega
    rw [h_eq]
    exact (Advances.of_stepPlus (R14 w1 (M - 15) l1) (root_of_5 (validL_cons hw1 hl1))).to_leads
  · have hz34 : 34 ≤ z0 := by lin_omega
    rcases Nat.lt_or_ge (z0 - 3) (2 * M) with hlt | hge
    · rcases mod2 (z0 - 3) with ⟨kp, hkp⟩ | ⟨kp, hkp⟩
      · have h1 : Bounce w1 l1 [z0, M] =
            Bounce w1 l1 (((2 * kp) + 3) :: (kp + 1 + (M - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp) (kp + 1 + (M - (kp + 1))) l1 [])
          (R10 kp (M - (kp + 1)) w1 l1 [])
        have e1 : kp + 1 + (M - (kp + 1)) + w1 + 6 = M + w1 + 6 := by omega
        rw [e1] at h_step
        exact Leads.of_stepPlus_leads h_step
          (bodd_nil_leads_root hl1 (by omega) (by omega) (by omega))
      · have hM21 : 21 ≤ M := by lin_omega
        have h1 : Bounce w1 l1 [z0, M] =
            Bounce w1 l1 (((2 * kp + 1) + 3) :: (kp + 1 + (M - (kp + 1))) :: []) := by
          congr 1; congr 1
          · omega
          · congr 1; omega
        rw [h1]
        have h_step := sp_trans (R15 w1 (2 * kp + 1) (kp + 1 + (M - (kp + 1))) l1 [])
          (R11 kp (M - (kp + 1)) w1 l1 [])
        have e1 : kp + (M - (kp + 1)) = M - 1 := by omega
        rw [e1] at h_step
        refine Leads.of_stepPlus_leads h_step ?_
        rcases Nat.lt_or_ge M 35 with hsmall | hbig
        · exact (bodd_leads hl1 (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_single_forced_r9 (by omega) (by lin_omega) hd)
        · exact (loop_leads hl1 (by omega) (by omega) (by omega)
            (tx := 34) (tdw := 29) (txw := 63) (by omega) rfl (by omega)
            (by lin_omega) (by lin_omega) (by lin_omega) (by lin_omega)).trans
            (fun _ hd => exit_nil_leads_root (by omega) hd)
    · have h_step := sp_trans
        (sp_trans (R15 w1 (2 * ((M - 5) + 5) + (z0 - 3 - 2 * M)) ((M - 5) + 5) l1 [])
          (R9 (M - 5) (z0 - 3 - 2 * M) w1 l1 []))
        (R12 (M - 5) ((z0 - 3 - 2 * M, w1) :: l1))
      have e1 : 2 * ((M - 5) + 5) + (z0 - 3 - 2 * M) + 3 = z0 := by omega
      have e2 : (M - 5) + 5 = M := by omega
      rw [e1, e2] at h_step
      exact (Advances.of_stepPlus h_step (root_of_ge18 hM18 (validL_cons hw1 hl1))).to_leads

theorem root_advances : ∀ c, RootInv c → Advances tm c RootInv := by
  rintro _ ⟨M, l, hM_or, hl, rfl⟩
  rcases hM_or with rfl | hM18
  · rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_step : (Beq 5 []) [tm]⊢⁺ Beq 5 [(5, 31)] := by
        refine sp_trans (R1nil 0) ?_
        refine sp_trans (bev0_nil_bounce 10 [5]) ?_
        refine sp_trans (R13 10 []) ?_
        refine sp_trans (R8nil 12 4 []) ?_
        refine sp_trans (bev0_nil_bounce 31 [20]) ?_
        exact R14 31 5 []
      exact Advances.of_stepPlus h_step (root_of_5 (validL_cons (by omega) validL_nil))
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · exact Advances.of_stepPlus_leads (R2 5 w l')
          (bev_nil_leads_root hl' (Nat.le_refl _) (by omega))
      · refine Advances.of_stepPlus_leads (R3 5 w l') ?_
        exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
          (fun _ hd => exit_5_leads_root (by lin_omega) hd)
      · exact Advances.of_stepPlus_leads (R1 0 z' w l')
          (bev_14_5_walk 14 rfl (by omega) (validL_cons hw hl'))
  · rcases l with _ | ⟨⟨z, w⟩, l'⟩
    · have h_eq : Beq M [] = Beq ((M - 5) + 5) [] := by congr 1; omega
      rw [h_eq]
      refine Advances.of_stepPlus_leads (R1nil (M - 5)) ?_
      have e1 : (M - 5) + 5 = M := by omega
      rw [e1]
      exact bev0_ge18_leads_root hM18 validL_nil
    · have hw : 27 ≤ w := validL_head hl
      have hl' : ValidL l' := validL_tail hl
      rcases z with _ | _ | z'
      · exact Advances.of_stepPlus_leads (R2 M w l')
          (bev_nil_leads_root hl' (Nat.le_refl _) (by omega))
      · refine Advances.of_stepPlus_leads (R3 M w l') ?_
        rcases Nat.lt_or_ge M 35 with hsmall | hbig
        · exact (bodd_leads hl' (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_single_forced_r9 hM18 (by lin_omega) hd)
        · exact (loop_leads hl' (by omega) (by omega) (by omega)
            (tx := 34) (tdw := 29) (txw := 63) (by omega) rfl (by omega)
            (by omega) (by omega) (by omega) (by omega)).trans
            (fun _ hd => exit_nil_leads_root (by omega) hd)
      · have h_eq : Beq M ((z' + 2, w) :: l') = Beq ((M - 5) + 5) ((z' + 2, w) :: l') := by
          congr 1; omega
        rw [h_eq]
        refine Advances.of_stepPlus_leads (R1 (M - 5) z' w l') ?_
        have e1 : (M - 5) + 5 = M := by omega
        rw [e1]
        exact bev0_ge18_leads_root hM18 (validL_cons hw hl')



end M240

namespace TM311Donor

open BusyBeaver.Counter

@[reducible] def donor311_machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1RC_1LC0LE_0RA1RD_1RF1LB_1LD0LA_HHH0RC"

abbrev donor311_tm : Machine (Fin 2) (Fin 6) := donor311_machine.toBB


abbrev LocalState := Counter.LocalState (Fin 2) (Fin 6)
@[simp] theorem append_nil (l : ListBlank (Fin 2)) : ([] : List (Fin 2)) +> l = l := rfl
@[simp] theorem append_cons (a : Fin 2) (as : List (Fin 2)) (l : ListBlank (Fin 2)) :
    (a :: as) +> l = a >> (as +> l) := rfl

def cfg_modeC (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> l) {{2}}> r)

def cfg_modeE1 (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> r))

def cfg_modeE0_first (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_modeE0_loop (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> r))

def cfg_b101_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> l) <{{4}} ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> (1 : Fin 2) >> default))

def cfg_e0f_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> default))

def cfg_e0l_mid (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)))

def cfg_transA_mid (l : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      l) {{1}}> ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> default))

def cfg_transB_mid (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  (((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
      (0 : Fin 2) >> l) {{1}}> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))

theorem init_reaches_modeC :
    (init []) [donor311_tm]⊢⁺ cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default) default := by
  refine run_local_plus_eq (n := 9) (s1 :=
      ⟨[(0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2)], 0, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], ([] : List (Fin 2)), 2,
      .right⟩) default default rfl ?_ ?_
  · simp only [cfg_of, init, Tape.mk₁, append_cons, append_nil, zero_cons_default, default_head,
      default_tail]; rfl
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, default_head, default_tail]

theorem step_modeC_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC l default) [donor311_tm]⊢⁺
      cfg_modeE0_first l := by
  refine run_local_plus_eq (n := 5) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, zero_cons_default, default_head,
      default_tail]
  · simp only [cfg_of, cfg_modeE0_first, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_modeC ((1 : Fin 2) >> (0 : Fin 2) >> l) r := by
  refine run_local_plus_eq (n := 1) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], ([] : List (Fin 2)), 2,
      .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil]

theorem step_modeC_b01_b10101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (0 : Fin 2) >> (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          ((1 : Fin 2) >> (0 : Fin 2) >> l)) r := by
  refine run_local_plus_eq (n := 6) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2)], ([] : List (Fin 2)), 2, .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil]

theorem step_modeC_b11 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((1 : Fin 2) >> (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_modeE1 l r := by
  refine run_local_plus_eq (n := 2) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01_b000 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        r)) [donor311_tm]⊢⁺
      cfg_modeE0_loop l r := by
  refine run_local_plus_eq (n := 13) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
      (0 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01_b101_nil_1 (l : ListBlank (Fin 2)) :
    (cfg_modeC ((1 : Fin 2) >> (0 : Fin 2) >> l) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        default)) [donor311_tm]⊢⁺
      cfg_b101_mid l := by
  refine run_local_plus_eq (n := 33) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2,
      .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
      [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_b101_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01_b101_nil_2 (l : ListBlank (Fin 2)) :
    (cfg_b101_mid l) [donor311_tm]⊢⁺
      cfg_modeE1 ((1 : Fin 2) >> (0 : Fin 2) >> l) ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default) := by
  refine run_local_plus_eq (n := 32) (s1 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
      [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_b101_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01_b1011101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 16) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
      (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE1_base (r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) r) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            r))) := by
  refine run_local_plus_eq (n := 24) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
      (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE1_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((1 : Fin 2) >> (0 : Fin 2) >> l) r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 5) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01_b101_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        default)) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01 l _)
    (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_1 l)
      (stepPlus_stepPlus_stepPlus (step_modeC_b01_b101_nil_2 l) (step_modeE1_b10 l _)))

theorem step_modeE1_b011_10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((0 : Fin 2) >> (1 : Fin 2) >> default)) r) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r))) := by
  refine run_local_plus_eq (n := 33) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE1_b011_10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l)) r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 14) (s1 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_base :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> default)) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            default))) := by
  refine run_local_plus_eq (n := 24) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
      (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_first, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_b10 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((1 : Fin 2) >> (0 : Fin 2) >> l)) [donor311_tm]⊢⁺
      cfg_modeE0_loop l default := by
  refine run_local_plus_eq (n := 5) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2)], 4, .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_first, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_b011_10_base_1 :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((0 : Fin 2) >> (1 : Fin 2) >> default))) [donor311_tm]⊢⁺
      cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) ((0 : Fin 2) >> (0 : Fin 2) >>
          (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 35) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) default default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_first, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_b011_10_base :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((0 : Fin 2) >> (1 : Fin 2) >> default))) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> default)))) :=
  stepPlus_stepPlus_stepPlus step_modeE0_first_b011_10_base_1 (step_modeE1_base _)

theorem step_modeE0_first_b011_10_b10_1 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))) [donor311_tm]⊢⁺
      cfg_e0f_mid l := by
  refine run_local_plus_eq (n := 20) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1,
      .right⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_first, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_e0f_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_b011_10_b10_2 (l : ListBlank (Fin 2)) :
    (cfg_e0f_mid l) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 20) (s1 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4,
      .left⟩) l default rfl ?_ ?_
  · simp only [cfg_of, cfg_e0f_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_first_b011_10_b10 (l : ListBlank (Fin 2)) :
    (cfg_modeE0_first ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_first_b011_10_b10_1 l) (step_modeE0_first_b011_10_b10_2 l)

theorem step_modeE0_loop_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((0 : Fin 2) >> (1 : Fin 2) >> default) r) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          ((0 : Fin 2) >> (1 : Fin 2) >> default))
        ((0 : Fin 2) >> (1 : Fin 2) >> r) := by
  refine run_local_plus_eq (n := 26) (s1 :=
      ⟨[(0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2),
      (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2)], 2, .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
        default)) r) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            ((1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r))))) := by
  refine run_local_plus_eq (n := 24) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
      (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)],
      4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 2,
      .right⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >>
        l)) r) [donor311_tm]⊢⁺
      cfg_modeE0_loop l ((1 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 5) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2),
      (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
      (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_b011_10_base_1 (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) r) [donor311_tm]⊢⁺
      cfg_modeE1 ((0 : Fin 2) >> (1 : Fin 2) >> default) ((0 : Fin 2) >> (0 : Fin 2) >>
          (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 35) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) default r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_b011_10_base (r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default))) r) [donor311_tm]⊢⁺
      cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> default)
        ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
            (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> r)))) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_base_1 r) (step_modeE1_base _)

theorem step_modeE0_loop_b10_b011_10_b10_1 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) r) [donor311_tm]⊢⁺
      cfg_e0l_mid l r := by
  refine run_local_plus_eq (n := 20) (s1 :=
      ⟨[(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_e0l_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_b011_10_b10_2 (l r : ListBlank (Fin 2)) :
    (cfg_e0l_mid l r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> r)) := by
  refine run_local_plus_eq (n := 20) (s1 :=
      ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 1, .right⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
      (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_e0l_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeE0_loop_b10_b011_10_b10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((1 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> ((1 : Fin 2) >> (0 : Fin 2) >> l))) r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
          ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> r)) :=
  stepPlus_stepPlus_stepPlus (step_modeE0_loop_b10_b011_10_b10_1 l r)
      (step_modeE0_loop_b10_b011_10_b10_2 l r)

theorem step_modeE0_loop_b011_10 (l r : ListBlank (Fin 2)) :
    (cfg_modeE0_loop ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        l) r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >>
          (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> r)))) := by
  refine run_local_plus_eq (n := 27) (s1 :=
      ⟨[(0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2),
      (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) (s2 :=
      ⟨[(1 : Fin 2), (0 : Fin 2)], [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
      (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩) l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeE0_loop, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01110_b10_b101_nil_1 (l : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [donor311_tm]⊢⁺
      cfg_transA_mid l := by
  refine run_local_plus_eq (n := 40)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
        (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
                (0 : Fin 2), (0 : Fin 2), (0 : Fin 2)], 2, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
        (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1,
                .right⟩)
    l default rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, zero_cons_default,
      Turing.ListBlank.head_cons, Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_transA_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01110_b10_b101_nil_2 (l : ListBlank (Fin 2)) :
    (cfg_transA_mid l) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> default)) := by
  refine run_local_plus_eq (n := 40)
    (s1 := ⟨[(1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
        (1 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1,
                .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2),
                (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2),
                (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 4, .left⟩)
    l default rfl ?_ ?_
  · simp only [cfg_of, cfg_transA_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01110_b10_b101_nil (l : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >>
        ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> default)) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b101_nil_1 l) (step_modeC_b01110_b10_b101_nil_2
      l)

theorem step_modeC_b01110_b10_b0000101_1 (l r : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_transB_mid l r := by
  refine run_local_plus_eq (n := 23)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (1 : Fin 2),
        (0 : Fin 2), (1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
                (1 : Fin 2)], 2, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
        (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
                (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    l r rfl ?_ ?_
  · simp only [cfg_of, cfg_modeC, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_transB_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01110_b10_b0000101_2 (l r : ListBlank (Fin 2)) :
    (cfg_transB_mid l r) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >>
            (1 : Fin 2) >> r)))) := by
  refine run_local_plus_eq (n := 23)
    (s1 := ⟨[(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
        (0 : Fin 2)],
            [(1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2),
                (1 : Fin 2), (0 : Fin 2), (1 : Fin 2)], 1, .right⟩)
    (s2 := ⟨[(1 : Fin 2), (0 : Fin 2)],
            [(0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (0 : Fin 2),
                (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2), (0 : Fin 2), (1 : Fin 2),
                (0 : Fin 2), (1 : Fin 2)], 4, .left⟩)
    l r rfl ?_ ?_
  · simp only [cfg_of, cfg_transB_mid, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]
  · simp only [cfg_of, cfg_modeE1, append_cons, append_nil, Turing.ListBlank.head_cons,
      Turing.ListBlank.tail_cons]

theorem step_modeC_b01110_b10_b0000101 (l r : ListBlank (Fin 2)) :
    (cfg_modeC ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> l))
      ((0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> r)) [donor311_tm]⊢⁺
      cfg_modeE1 l ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
        ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >>
            (1 : Fin 2) >> r)))) :=
  stepPlus_stepPlus_stepPlus (step_modeC_b01110_b10_b0000101_1 l r)
      (step_modeC_b01110_b10_b0000101_2 l r)

-- ============================================================================
-- Parametric Left-Tape Encoding and Invariant
-- ============================================================================

def prepend10 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, l => l
  | k + 1, l => (1 : Fin 2) >> (0 : Fin 2) >> prepend10 k l

def encL_tail : List ℕ → ListBlank (Fin 2)
  | [] => (0 : Fin 2) >> (1 : Fin 2) >> default
  | k :: ks =>
    (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      prepend10 k (encL_tail ks)

def encL (k₀ : ℕ) (ks : List ℕ) : ListBlank (Fin 2) :=
  prepend10 k₀ (encL_tail ks)

@[simp] theorem encL_zero_nil : encL 0 [] = (0 : Fin 2) >> (1 : Fin 2) >> default := rfl
@[simp] theorem encL_succ (k : ℕ) (ks : List ℕ) :
    encL (k + 1) ks = (1 : Fin 2) >> (0 : Fin 2) >> encL k ks := rfl
@[simp] theorem encL_zero_cons (k : ℕ) (ks : List ℕ) :
    encL 0 (k :: ks) =
      (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> encL k ks := rfl

def prepend01 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | k + 1, r => (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k r

theorem prepend01_add (a b : ℕ) (r : ListBlank (Fin 2)) :
    prepend01 (a + b) r = prepend01 a (prepend01 b r) := by
  induction a with
  | zero => simp [prepend01]
  | succ a ih => simp only [Nat.succ_add, prepend01, ih]

def prepend11_01 : ℕ → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, r => r
  | d + 1, r => (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d r

theorem prepend11_01_add (a b : ℕ) (r : ListBlank (Fin 2)) :
    prepend11_01 (a + b) r = prepend11_01 a (prepend11_01 b r) := by
  induction a with
  | zero => simp [prepend11_01]
  | succ a ih => simp only [Nat.succ_add, prepend11_01, ih]

-- ============================================================================
-- Macro Transitions (Mode C / E1 / E0_loop)
-- ============================================================================

theorem modeC_prepend01_star : ∀ (n k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeC (encL k₀ ks) (prepend01 n r)) [donor311_tm]⊢*
      cfg_modeC (encL (k₀ + n) ks) r
  | 0, k₀, ks, r => ⟨0, by simp [prepend01]⟩
  | n + 1, k₀, ks, r => by
    have h1 : (cfg_modeC (encL k₀ ks) ((0 : Fin 2) >> (1 : Fin 2) >> prepend01 n r)) [donor311_tm]⊢⁺
        cfg_modeC (encL (k₀ + 1) ks) (prepend01 n r) := step_modeC_b01 (encL k₀ ks) (prepend01 n r)
    have h2 := modeC_prepend01_star n (k₀ + 1) ks r
    have heq : k₀ + 1 + n = k₀ + (n + 1) := by omega
    rw [heq] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

theorem e0_loop_drain_pairs : ∀ (d rem : ℕ) (xs : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeE0_loop (encL (rem + 2 * d) xs) r) [donor311_tm]⊢*
      cfg_modeE0_loop (encL rem xs) (prepend11_01 d r)
  | 0, rem, xs, r => ⟨0, by simp [prepend11_01]⟩
  | d + 1, rem, xs, r => by
    have heq : rem + 2 * (d + 1) = ((rem + 2 * d) + 1) + 1 := by omega
    rw [heq]
    have h1 : (cfg_modeE0_loop (encL (((rem + 2 * d) + 1) + 1) xs) r) [donor311_tm]⊢⁺
        cfg_modeE0_loop (encL (rem + 2 * d) xs) (prepend11_01 1 r) :=
      step_modeE0_loop_b10_b10 (encL (rem + 2 * d) xs) r
    have h2 := e0_loop_drain_pairs d rem xs (prepend11_01 1 r)
    rw [← prepend11_01_add] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

theorem modeE1_drain_k0 : ∀ (k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeE1 (encL k₀ ks) r) [donor311_tm]⊢*
      cfg_modeE1 (encL 0 ks) (prepend01 k₀ r)
  | 0, ks, r => ⟨0, rfl⟩
  | k₀ + 1, ks, r => by
    have h1 : (cfg_modeE1 (encL (k₀ + 1) ks) r) [donor311_tm]⊢⁺
        cfg_modeE1 (encL k₀ ks) (prepend01 1 r) := step_modeE1_b10 (encL k₀ ks) r
    have h2 := modeE1_drain_k0 k₀ ks (prepend01 1 r)
    rw [← prepend01_add] at h2
    exact stepPlus_stepStar (stepPlus_stepStar_stepPlus h1 h2)

theorem modeE1_to_modeC : ∀ (ks : List ℕ) (k₀ : ℕ) (r : ListBlank (Fin 2)),
    ValidKS ks →
    let b := bump_enc k₀ ks
    (cfg_modeE1 (encL k₀ ks) r) [donor311_tm]⊢⁺ cfg_modeC (encL b.1 b.2) r
  | [], k₀, r, _ => by
    dsimp [bump_enc]
    have h1 := modeE1_drain_k0 k₀ [] r
    have h2 : (cfg_modeE1 (encL 0 []) (prepend01 k₀ r)) [donor311_tm]⊢⁺
        cfg_modeC (encL 0 []) (prepend01 3 (prepend01 k₀ r)) := step_modeE1_base (prepend01 k₀ r)
    rw [← prepend01_add, Nat.add_comm 3 k₀] at h2
    have h3 := modeC_prepend01_star (k₀ + 3) 0 [] r
    rw [Nat.zero_add] at h3
    exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)
  | [k₁], k₀, r, _ => by
    dsimp [bump_enc, add_last]
    have h1 := modeE1_drain_k0 k₀ [k₁] r
    cases k₁ with
    | zero =>
      have h2 := step_modeE1_b011_10_base (prepend01 k₀ r)
      have h3 :=
          step_modeC_b01 (encL 0 []) ((0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          prepend01 k₀ r))
      have h4 :=
          step_modeC_b01 (encL 1 []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r)
      have h5 : (cfg_modeC (encL 2 []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
          [donor311_tm]⊢⁺ cfg_modeC (encL 0 [3]) (prepend01 k₀ r) :=
        step_modeC_b01_b10101 (encL 2 []) (prepend01 k₀ r)
      have h6 := modeC_prepend01_star k₀ 0 [3] r
      rw [Nat.zero_add] at h6
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepPlus_stepPlus h4
              (stepPlus_stepStar_stepPlus h5 h6))))
    | succ k₁' =>
      have h2 : (cfg_modeE1 (encL 0 [k₁' + 1]) (prepend01 k₀ r)) [donor311_tm]⊢⁺
          cfg_modeE1 (encL k₁' []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
              (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) :=
        step_modeE1_b011_10_b10 (encL k₁' []) (prepend01 k₀ r)
      have h3 :=
          modeE1_to_modeC [] k₁' ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) trivial
      dsimp [bump_enc] at h3
      have h4 : (cfg_modeC (encL (k₁' + 3) []) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r))
          [donor311_tm]⊢⁺ cfg_modeC (encL 0 [k₁' + 4]) (prepend01 k₀ r) :=
        step_modeC_b01_b10101 (encL (k₁' + 3) []) (prepend01 k₀ r)
      have h5 := modeC_prepend01_star k₀ 0 [k₁' + 4] r
      rw [Nat.zero_add] at h5
      have heq : k₁' + 1 + 3 = k₁' + 4 := by omega
      rw [heq]
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepStar_stepPlus h4 h5)))
  | k₁ :: k₂ :: ks'', k₀, r, ⟨hk1, hval'⟩ => by
    dsimp [bump_enc, add_last]
    cases k₁ with
    | zero => omega
    | succ k₁' =>
      have h1 := modeE1_drain_k0 k₀ ((k₁' + 1) :: k₂ :: ks'') r
      have h2 : (cfg_modeE1 (encL 0 ((k₁' + 1) :: k₂ :: ks'')) (prepend01 k₀ r)) [donor311_tm]⊢⁺
          cfg_modeE1 (encL k₁' (k₂ :: ks'')) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
              (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) :=
        step_modeE1_b011_10_b10 (encL k₁' (k₂ :: ks'')) (prepend01 k₀ r)
      have h3 :=
          modeE1_to_modeC (k₂ :: ks'') k₁' ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
          (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> prepend01 k₀ r) hval'
      dsimp [bump_enc] at h3
      have h4 : (cfg_modeC (encL k₁' (add_last (k₂ :: ks'') 3)) ((0 : Fin 2) >> (1 : Fin 2) >>
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          prepend01 k₀ r))
          [donor311_tm]⊢⁺ cfg_modeC (encL 0 ((k₁' + 1) :: add_last (k₂ :: ks'') 3)) (prepend01 k₀
              r) :=
        step_modeC_b01_b10101 (encL k₁' (add_last (k₂ :: ks'') 3)) (prepend01 k₀ r)
      have h5 := modeC_prepend01_star k₀ 0 ((k₁' + 1) :: add_last (k₂ :: ks'') 3) r
      rw [Nat.zero_add] at h5
      exact stepStar_stepPlus_stepPlus h1
        (stepPlus_stepPlus_stepPlus h2
          (stepPlus_stepPlus_stepPlus h3
            (stepPlus_stepStar_stepPlus h4 h5)))

theorem modeC_consume_11_01_nil : ∀ (n k₀ : ℕ) (r : ListBlank (Fin 2)),
    (cfg_modeC (encL k₀ []) (prepend11_01 n r)) [donor311_tm]⊢*
      cfg_modeC (encL (k₀ + 4 * n) []) r
  | 0, k₀, r => ⟨0, by simp [prepend11_01]⟩
  | n + 1, k₀, r => by
    have h1 := step_modeC_b11 (encL k₀ []) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r)
    have h2 := modeE1_to_modeC [] k₀ ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r) trivial
    dsimp [bump_enc] at h2
    have h3 : (cfg_modeC (encL (k₀ + 3) []) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r))
        [donor311_tm]⊢⁺ cfg_modeC (encL (k₀ + 4) []) (prepend11_01 n r) :=
      step_modeC_b01 (encL (k₀ + 3) []) (prepend11_01 n r)
    have h4 := modeC_consume_11_01_nil n (k₀ + 4) r
    have heq : k₀ + 4 + 4 * n = k₀ + 4 * (n + 1) := by omega
    rw [heq] at h4
    exact stepPlus_stepStar (stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2
        (stepPlus_stepStar_stepPlus h3 h4)))

theorem modeC_consume_11_01_nonempty : ∀ (n k₀ : ℕ) (ks : List ℕ) (r : ListBlank (Fin 2)),
    ks ≠ [] → ValidKS ks →
    (cfg_modeC (encL k₀ ks) (prepend11_01 n r)) [donor311_tm]⊢*
      cfg_modeC (encL (k₀ + n) (add_last ks (3 * n))) r
  | 0, k₀, ks, r, _, _ => ⟨0, by simp [prepend11_01, add_last_zero]⟩
  | n + 1, k₀, ks, r, hne, hval => by
    have h1 := step_modeC_b11 (encL k₀ ks) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r)
    have h2 := modeE1_to_modeC ks k₀ ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r) hval
    rw [bump_enc_nonempty k₀ hne] at h2
    have h3 : (cfg_modeC (encL k₀ (add_last ks 3)) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 n r))
        [donor311_tm]⊢⁺ cfg_modeC (encL (k₀ + 1) (add_last ks 3)) (prepend11_01 n r) :=
      step_modeC_b01 (encL k₀ (add_last ks 3)) (prepend11_01 n r)
    have h4 := modeC_consume_11_01_nonempty n (k₀ + 1) (add_last ks 3) r
      (add_last_ne_nil ks 3 hne) (ValidKS_add_last ks 3 hval)
    rw [add_last_add] at h4
    have heq1 : k₀ + 1 + n = k₀ + (n + 1) := by omega
    have heq2 : 3 + 3 * n = 3 * (n + 1) := by omega
    rw [heq1, heq2] at h4
    exact stepPlus_stepStar (stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2
        (stepPlus_stepStar_stepPlus h3 h4)))

theorem unwrap_11_01_1011101_step (m₀ : ℕ) (ms : List ℕ) (R : ListBlank (Fin 2))
    (h_valid : ValidKS ms) :
    let p := bump_enc_twice m₀ ms
    (cfg_modeC (encL m₀ ms)
      ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> R))
      [donor311_tm]⊢⁺
      cfg_modeC (encL 0 ((p.1 + 1) :: p.2)) R := by
  dsimp [bump_enc_twice]
  set p1 := bump_enc m₀ ms
  set p2 := bump_enc p1.1 p1.2
  have h1 := step_modeC_b11 (encL m₀ ms)
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
  have h2 := modeE1_to_modeC ms m₀
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) h_valid
  have h3 := step_modeC_b01_b1011101 (encL p1.1 p1.2) R
  have h4 := modeE1_to_modeC p1.2 p1.1
    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> R)
    (ValidKS_bump_enc m₀ ms h_valid)
  have h5 : (cfg_modeC (encL p2.1 p2.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R))
      [donor311_tm]⊢⁺ cfg_modeC (encL 0 ((p2.1 + 1) :: p2.2)) R :=
    step_modeC_b01_b10101 (encL p2.1 p2.2) R
  exact stepPlus_stepPlus_stepPlus h1
    (stepPlus_stepPlus_stepPlus h2
      (stepPlus_stepPlus_stepPlus h3
        (stepPlus_stepPlus_stepPlus h4 h5)))

-- ============================================================================
-- Master Lemma 1: e0_loop_leave1_goodks
-- ============================================================================

set_option maxRecDepth 200000 in
theorem e0_loop_leave1_goodks :
    ∀ (n : ℕ) (x₀ : ℕ) (xs : List ℕ) (S : ℕ) (R : ListBlank (Fin 2)),
    xs.length = n →
    S ≥ 36 →
    (xs = [] → 2 * S ≤ 35 * x₀) →
    (xs ≠ [] → x₀ ≥ 2 ∧ 2 * S ≤ 35 * (x₀ + 3)) →
    GoodKS (2 * S + 63 * (x₀ + 3)) xs →
    ∃ m₀ ms,
      ((cfg_modeE0_loop (encL x₀ xs) R) [donor311_tm]⊢⁺
        cfg_modeC (encL m₀ ms) ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)) ∧
      ValidKS ms ∧
      (ms = [] → m₀ ≥ 7) ∧
      (let p := bump_enc_twice m₀ ms; GoodKS S ((p.1 + 1) :: p.2)) ∧
      ((xs = [] → x₀ ≥ 10) → S = 81 →
        let p1 := bump_enc m₀ ms; GoodKS 81 ((p1.1 + 1) :: p1.2))
  | 0, x₀, xs, S, R, hlen, hS, h_nil, h_cons, h_gks => by
    cases xs with
    | cons _ _ => simp at hlen
    | nil =>
      have hx0 : 2 * S ≤ 35 * x₀ := h_nil rfl
      have hx0_ge : x₀ ≥ 3 := by omega
      set d := x₀ / 2
      set rem := x₀ % 2
      have h_div : rem + 2 * d = x₀ := by omega
      have h_rem : rem = 0 ∨ rem = 1 := by omega
      rcases h_rem with h_even | h_odd
      · -- Case 2: xs = [], x₀ = 2 * d (d ≥ 2)
        have hd : d ≥ 2 := by omega
        refine ⟨d, [3 * d - 3], ?_, trivial, by simp, ?_, ?_⟩
        · have hd_split : x₀ = 0 + 2 * d := by omega
          rw [hd_split]
          have h1 := e0_loop_drain_pairs d 0 [] R
          have h2 : (cfg_modeE0_loop (encL 0 []) (prepend11_01 d R)) [donor311_tm]⊢⁺
              cfg_modeC (encL 0 [0]) ((0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R) :=
            step_modeE0_loop_base (prepend11_01 d R)
          have h3 : (cfg_modeC (encL 0 [0]) ((0 : Fin 2) >> (1 : Fin 2) >>
              prepend11_01 d R)) [donor311_tm]⊢⁺
              cfg_modeC (encL 1 [0]) (prepend11_01 d R) :=
            step_modeC_b01 (encL 0 [0]) (prepend11_01 d R)
          have hd_eq : d = (d - 1) + 1 := by omega
          have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >>
              (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            conv_lhs => rw [hd_eq]
            rw [prepend11_01_add]; rfl
          have h4 := modeC_consume_11_01_nonempty (d - 1) 1 [0]
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) (by simp) trivial
          simp only [add_last, Nat.zero_add] at h4
          have heq1 : 1 + (d - 1) = d := by omega
          have heq2 : 3 * (d - 1) = 3 * d - 3 := by omega
          rw [← h_p11, heq1, heq2] at h4
          exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepStar_stepPlus h3 h4))
        · simp only [bump_enc_twice, bump_enc, add_last, GoodKS]
          refine ⟨by omega, ?_, trivial⟩
          omega
        · intro hx10 hS81
          have hx10' : x₀ ≥ 10 := hx10 rfl
          have hd5 : d ≥ 5 := by omega
          simp only [bump_enc, add_last, GoodKS]
          refine ⟨by omega, ?_, trivial⟩
          omega
      · -- Case 1: xs = [], x₀ = 2 * d + 1 (d ≥ 1)
        have hd : d ≥ 1 := by omega
        refine ⟨4 * d + 3, [], ?_, trivial, fun _ => by omega, ?_, ?_⟩
        · have hd_split : x₀ = 1 + 2 * d := by omega
          rw [hd_split]
          have h1 := e0_loop_drain_pairs d 1 [] R
          have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d R)) [donor311_tm]⊢⁺
              cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) R)) :=
            step_modeE0_loop_b10_base (prepend11_01 d R)
          have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) R)
          rw [Nat.zero_add] at h3
          have h_p11 : prepend11_01 (d + 1) R = prepend11_01 d ((1 : Fin 2) >> (1 : Fin 2) >>
              (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            rw [prepend11_01_add]; rfl
          have h4 :=
              modeC_consume_11_01_nil d 3 ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
              (1 : Fin 2) >> R)
          have heq : 3 + 4 * d = 4 * d + 3 := by omega
          rw [← h_p11, heq] at h4
          exact stepStar_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4))
        · simp only [bump_enc_twice, bump_enc, GoodKS]
          exact ⟨by omega, trivial⟩
        · intro _ _
          simp only [bump_enc, GoodKS]
          exact ⟨by omega, trivial⟩
  | n' + 1, x₀, xs, S, R, hlen, hS, h_nil, h_cons, h_gks => by
    cases xs with
    | nil => simp at hlen
    | cons x₁ xs_rest =>
      have hlen' : xs_rest.length = n' := by simpa using hlen
      have ⟨hx0_ge, hx0_bound⟩ := h_cons (by simp)
      have ⟨h_x1_bound, h_gks_rest⟩ := h_gks
      have hx1_ge : x₁ ≥ 1 := by omega
      have h_valid_xs : ValidKS (x₁ :: xs_rest) :=
        GoodKS_valid (x₁ :: xs_rest) (2 * S + 63 * (x₀ + 3)) (by omega) h_gks
      have h_valid_rest : ValidKS xs_rest :=
        GoodKS_valid xs_rest (2 * S + 63 * (x₀ + 3) + 63 * (x₁ + 2)) (by omega) h_gks_rest
      set d := x₀ / 2
      set rem := x₀ % 2
      have hd : d ≥ 1 := by omega
      have h_rem : rem = 0 ∨ rem = 1 := by omega
      rcases h_rem with h_even | h_odd
      · -- Case 3: xs = x₁ :: xs_rest, x₀ = 2 * d (d ≥ 1)
        have hd_split : x₀ = 0 + 2 * d := by omega
        set b := bump_enc x₁ xs_rest
        cases h_rest : xs_rest with
        | nil =>
          -- Subcase 3a: xs_rest = []
          have hb : b = (x₁ + 3, []) := by simp [b, h_rest, bump_enc]
          refine ⟨x₁ + 4 * d + 3, [], ?_, trivial, fun _ => by omega, ?_, ?_⟩
          · rw [hd_split]
            have h1 := e0_loop_drain_pairs d 0 [x₁] R
            have h2 : (cfg_modeE0_loop (encL 0 [x₁]) (prepend11_01 d R)) [donor311_tm]⊢⁺
                cfg_modeE1 (encL x₁ []) (prepend01 4 (prepend11_01 d R)) :=
              step_modeE0_loop_b011_10 (encL x₁ []) (prepend11_01 d R)
            have h3 := modeE1_to_modeC [] x₁ (prepend01 4 (prepend11_01 d R)) trivial
            dsimp only [bump_enc] at h3
            have h4 := modeC_prepend01_star 4 (x₁ + 3) [] (prepend11_01 d R)
            have hd_eq : d = (d - 1) + 1 := by omega
            have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >>
                (0 : Fin 2) >> (1 : Fin 2) >> R) := by
              conv_lhs => rw [hd_eq]
              rw [prepend11_01_add]; rfl
            have h5 := modeC_consume_11_01_nil (d - 1) (x₁ + 3 + 4)
              ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
            have heq : x₁ + 3 + 4 + 4 * (d - 1) = x₁ + 4 * d + 3 := by omega
            rw [← h_p11, heq] at h5
            exact stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
          · simp only [bump_enc_twice, bump_enc, GoodKS]
            exact ⟨by omega, trivial⟩
          · intro _ _
            simp only [bump_enc, GoodKS]
            exact ⟨by omega, trivial⟩
        | cons x₂ rest' =>
          -- Subcase 3b: xs_rest = x₂ :: rest'
          have hne_rest : (x₂ :: rest') ≠ [] := by simp
          rw [h_rest] at h_gks_rest h_valid_rest
          refine ⟨x₁ + d + 3, add_last (x₂ :: rest') (3 * d), ?_,
            ValidKS_add_last (x₂ :: rest') (3 * d) h_valid_rest,
            fun h_emp => absurd h_emp (add_last_ne_nil (x₂ :: rest') (3 * d) hne_rest),
            ?_, ?_⟩
          · rw [hd_split]
            have h1 := e0_loop_drain_pairs d 0 (x₁ :: x₂ :: rest') R
            have h2 : (cfg_modeE0_loop (encL 0 (x₁ :: x₂ :: rest')) (prepend11_01 d R))
                [donor311_tm]⊢⁺
                cfg_modeE1 (encL x₁ (x₂ :: rest')) (prepend01 4 (prepend11_01 d R)) :=
              step_modeE0_loop_b011_10 (encL x₁ (x₂ :: rest')) (prepend11_01 d R)
            have h3 :=
                modeE1_to_modeC (x₂ :: rest') x₁ (prepend01 4 (prepend11_01 d R)) h_valid_rest
            rw [bump_enc_nonempty x₁ hne_rest] at h3
            dsimp only at h3
            have h4 := modeC_prepend01_star 4 x₁ (add_last (x₂ :: rest') 3) (prepend11_01 d R)
            have hd_eq : d = (d - 1) + 1 := by omega
            have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >>
                (0 : Fin 2) >> (1 : Fin 2) >> R) := by
              conv_lhs => rw [hd_eq]
              rw [prepend11_01_add]; rfl
            have h5 := modeC_consume_11_01_nonempty (d - 1) (x₁ + 4) (add_last (x₂ :: rest') 3)
              ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R)
              (add_last_ne_nil (x₂ :: rest') 3 hne_rest)
              (ValidKS_add_last (x₂ :: rest') 3 h_valid_rest)
            rw [add_last_add] at h5
            have heq1 : x₁ + 4 + (d - 1) = x₁ + d + 3 := by omega
            have heq2 : 3 + 3 * (d - 1) = 3 * d := by omega
            rw [← h_p11, heq1, heq2] at h5
            exact stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
          · rw [bump_enc_twice_nonempty (x₁ + d + 3) (add_last_ne_nil (x₂ :: rest') (3 * d)
              hne_rest), add_last_add]
            simp only [GoodKS]
            refine ⟨by omega, ?_⟩
            apply GoodKS_add_last
            exact GoodKS_mono (x₂ :: rest') _ _ (by omega) h_gks_rest
          · intro _ hS81
            subst hS81
            rw [bump_enc_nonempty (x₁ + d + 3) (add_last_ne_nil (x₂ :: rest') (3 * d) hne_rest),
                add_last_add]
            simp only [GoodKS]
            refine ⟨by omega, ?_⟩
            apply GoodKS_add_last
            exact GoodKS_mono (x₂ :: rest') _ _ (by omega) h_gks_rest
      · -- Case 4: xs = x₁ :: xs_rest, x₀ = 2 * d + 1 (d ≥ 1)
        have hd_split : x₀ = 1 + 2 * d := by omega
        set S_sub := S + 63 * (d + 2)
        have hS_sub : S_sub ≥ 36 := by omega
        have h_eq_2S : 2 * S + 63 * (x₀ + 3) = 2 * S_sub := by omega
        have hx1_ge10 : x₁ ≥ 10 := by omega
        set sub := bump_enc (x₁ - 1) xs_rest
        have h_sub_len : sub.2.length = n' := by
          cases xs_rest with
          | nil => simpa [sub, bump_enc] using hlen'
          | cons _ _ => simp [sub, bump_enc, add_last_length, hlen']
        have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
          cases xs_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys =>
            intro h_emp
            exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
          cases xs_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys =>
            intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
          cases xs_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * S_sub + 63 * (x₁ - 1 + 3) = 2 * S + 63 * (x₀ + 3) + 63 * (x₁ + 2) := by
              omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        set R_tail :=
            (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
            (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d R
        rcases e0_loop_leave1_goodks n' sub.1 sub.2 S_sub R_tail h_sub_len hS_sub h_sub_nil
            h_sub_cons h_sub_gks
          with ⟨y₀, ys, h_step_sub, h_val_ys, h_ys_emp, h_gks_sub, _⟩
        set py := bump_enc_twice y₀ ys
        set ks_mid := (py.1 + 1) :: py.2
        have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
        have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
        refine ⟨d - 1, add_last ks_mid (3 * (d - 1)), ?_,
          ValidKS_add_last ks_mid (3 * (d - 1)) hval_mid,
          fun h_emp => absurd h_emp (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid),
          ?_, ?_⟩
        · rw [hd_split]
          have h1 := e0_loop_drain_pairs d 1 (x₁ :: xs_rest) R
          have hx1_eq : x₁ = (x₁ - 1) + 1 := by omega
          have h2 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) (prepend11_01 d R)) [donor311_tm]⊢⁺
              cfg_modeE1 (encL (x₁ - 1) xs_rest)
                ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                    R_tail) := by
            rw [show encL 1 (x₁ :: xs_rest) = encL 1 (((x₁ - 1) + 1) :: xs_rest) by rw [← hx1_eq]]
            exact step_modeE0_loop_b10_b011_10_b10 (encL (x₁ - 1) xs_rest) (prepend11_01 d R)
          have h3 := modeE1_to_modeC xs_rest (x₁ - 1)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                R_tail) h_valid_rest
          have h4 : (cfg_modeC (encL sub.1 sub.2)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
              [donor311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
            step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
          have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d R) h_val_ys
          have hd_eq : d = (d - 1) + 1 := by omega
          have h_p11 : prepend11_01 d R = prepend11_01 (d - 1) ((1 : Fin 2) >> (1 : Fin 2) >>
              (0 : Fin 2) >> (1 : Fin 2) >> R) := by
            conv_lhs => rw [hd_eq]
            rw [prepend11_01_add]; rfl
          have h6 := modeC_consume_11_01_nonempty (d - 1) 0 ks_mid
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R) hne_mid hval_mid
          rw [← h_p11, Nat.zero_add] at h6
          exact stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepPlus_stepPlus h3
                (stepPlus_stepPlus_stepPlus h4
                  (stepPlus_stepPlus_stepPlus h_step_sub
                    (stepPlus_stepStar_stepPlus h5 h6)))))
        · rw [bump_enc_twice_nonempty (d - 1) (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid),
            add_last_add]
          dsimp only
          have hd1 : d - 1 + 1 = d := by omega
          rw [hd1]
          simp only [GoodKS]
          refine ⟨by omega, ?_⟩
          exact GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 6) h_gks_sub
        · intro _ hS81
          subst hS81
          rw [bump_enc_nonempty (d - 1) (add_last_ne_nil ks_mid (3 * (d - 1)) hne_mid),
              add_last_add]
          dsimp only
          have hd1 : d - 1 + 1 = d := by omega
          rw [hd1]
          simp only [GoodKS]
          refine ⟨by omega, ?_⟩
          exact GoodKS_add_last ks_mid S_sub (3 * (d - 1) + 3) h_gks_sub

-- ============================================================================
-- Master Lemma 2a: k₀ ≥ 1 Transition (step_k0_pos)
-- ============================================================================

theorem step_k0_pos (k₀ : ℕ) (ks : List ℕ) (hk0 : k₀ ≥ 1) (h_inv : InvNil k₀ ks) :
    ∃ k₀' ks',
      ((cfg_modeC (encL k₀ ks) default) [donor311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  set x₀ := k₀ - 1
  have hk0_eq : k₀ = x₀ + 1 := by omega
  have h_to_e0 : (cfg_modeC (encL k₀ ks) default) [donor311_tm]⊢⁺ cfg_modeE0_loop (encL x₀ ks)
      default := by
    rw [hk0_eq]
    exact stepPlus_stepPlus_stepPlus (step_modeC_nil (encL (x₀ + 1) ks)) (step_modeE0_first_b10
        (encL x₀ ks))
  set d := x₀ / 2
  set rem := x₀ % 2
  have h_rem : rem = 0 ∨ rem = 1 := by omega
  rcases h_inv with ⟨ rfl, hk5 ⟩ | ⟨ hne, h_gks ⟩
  · -- ks = [], k₀ ≥ 5 (so x₀ ≥ 4)
    rcases h_rem with h_even | h_odd
    · -- Branch 2: ks = [], x₀ = 2 * d (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hx_split : x₀ = 0 + 2 * d := by omega
      refine ⟨d + 1, [3 * d], ?_, Or.inr ⟨by simp, ?_⟩⟩
      · rw [hx_split] at h_to_e0
        have h1 := e0_loop_drain_pairs d 0 [] default
        have h2 := step_modeE0_loop_base (prepend11_01 d default)
        have h3 := step_modeC_b01 (encL 0 [0]) (prepend11_01 d default)
        have h4 := modeC_consume_11_01_nonempty d 1 [0] default (by simp) trivial
        simp only [add_last, Nat.zero_add] at h4
        have heq : 1 + d = d + 1 := by omega
        rw [heq] at h4
        exact stepPlus_stepPlus_stepPlus h_to_e0
          (stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepStar_stepPlus h3 h4)))
      · have hd1_ne : d + 1 ≠ 1 := by omega
        simp only [hd1_ne, ite_false, GoodKS]
        exact ⟨by omega, trivial⟩
    · -- Branch 1: ks = [], x₀ = 2 * d + 1 (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hx_split : x₀ = 1 + 2 * d := by omega
      refine ⟨4 * d + 7, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
      · rw [hx_split] at h_to_e0
        have h1 := e0_loop_drain_pairs d 1 [] default
        have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d default)) [donor311_tm]⊢⁺
            cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) default)) :=
          step_modeE0_loop_b10_base (prepend11_01 d default)
        have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) default)
        rw [Nat.zero_add] at h3
        have h4 := modeC_consume_11_01_nil (d + 1) 3 default
        have heq : 3 + 4 * (d + 1) = 4 * d + 7 := by omega
        rw [heq] at h4
        exact stepPlus_stepPlus_stepPlus h_to_e0
          (stepStar_stepPlus_stepPlus h1
            (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 h4)))
  · -- ks = k₁ :: ks_rest
    cases ks with
    | nil => contradiction
    | cons k₁ ks_rest =>
      set S_in := if k₀ = 1 then 81 else 36 * (k₀ + 2)
      have hS_in_ge : S_in ≥ 81 := by
        dsimp [S_in]; split_ifs <;> omega
      have ⟨hk1_bound, h_gks_rest⟩ := h_gks
      have hk1_ge : k₁ ≥ 1 := by omega
      have h_valid_rest : ValidKS ks_rest :=
        GoodKS_valid ks_rest (S_in + 63 * (k₁ + 2)) (by omega) h_gks_rest
      rcases h_rem with h_even | h_odd
      · -- Branch 3: ks = k₁ :: ks_rest, x₀ = 2 * d (d ≥ 0, k₀ = 2 * d + 1)
        have hx_split : x₀ = 0 + 2 * d := by omega
        cases ks_rest with
        | nil =>
          refine ⟨k₁ + 4 * d + 7, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
          rw [hx_split] at h_to_e0
          have h1 := e0_loop_drain_pairs d 0 [k₁] default
          have h2 : (cfg_modeE0_loop (encL 0 [k₁]) (prepend11_01 d default)) [donor311_tm]⊢⁺
              cfg_modeE1 (encL k₁ []) (prepend01 4 (prepend11_01 d default)) :=
            step_modeE0_loop_b011_10 (encL k₁ []) (prepend11_01 d default)
          have h3 := modeE1_to_modeC [] k₁ (prepend01 4 (prepend11_01 d default)) trivial
          dsimp [bump_enc] at h3
          have h4 := modeC_prepend01_star 4 (k₁ + 3) [] (prepend11_01 d default)
          have h5 := modeC_consume_11_01_nil d (k₁ + 3 + 4) default
          have heq : k₁ + 3 + 4 + 4 * d = k₁ + 4 * d + 7 := by omega
          rw [heq] at h5
          exact stepPlus_stepPlus_stepPlus h_to_e0
            (stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5))))
        | cons k₂ rest' =>
          have hne_rest : (k₂ :: rest') ≠ [] := by simp
          refine ⟨k₁ + d + 4, add_last (k₂ :: rest') (3 * d + 3), ?_,
            Or.inr ⟨add_last_ne_nil (k₂ :: rest') (3 * d + 3) hne_rest, ?_⟩⟩
          · rw [hx_split] at h_to_e0
            have h1 := e0_loop_drain_pairs d 0 (k₁ :: k₂ :: rest') default
            have h2 : (cfg_modeE0_loop (encL 0 (k₁ :: k₂ :: rest')) (prepend11_01 d default))
                [donor311_tm]⊢⁺
                cfg_modeE1 (encL k₁ (k₂ :: rest')) (prepend01 4 (prepend11_01 d default)) :=
              step_modeE0_loop_b011_10 (encL k₁ (k₂ :: rest')) (prepend11_01 d default)
            have h3 :=
                modeE1_to_modeC (k₂ :: rest') k₁ (prepend01 4 (prepend11_01 d default)) h_valid_rest
            rw [bump_enc_nonempty k₁ hne_rest] at h3
            have h4 := modeC_prepend01_star 4 k₁ (add_last (k₂ :: rest') 3) (prepend11_01 d default)
            have h5 := modeC_consume_11_01_nonempty d (k₁ + 4) (add_last (k₂ :: rest') 3) default
              (add_last_ne_nil (k₂ :: rest') 3 hne_rest)
              (ValidKS_add_last (k₂ :: rest') 3 h_valid_rest)
            rw [add_last_add] at h5
            have heq1 : k₁ + 4 + d = k₁ + d + 4 := by omega
            have heq2 : 3 + 3 * d = 3 * d + 3 := by omega
            rw [heq1, heq2] at h5
            exact stepPlus_stepPlus_stepPlus h_to_e0
              (stepStar_stepPlus_stepPlus h1
                (stepPlus_stepPlus_stepPlus h2
                  (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5))))
          · have h_ne1 : k₁ + d + 4 ≠ 1 := by omega
            simp only [h_ne1, ite_false]
            apply GoodKS_add_last
            apply GoodKS_mono (k₂ :: rest') _ (S_in + 63 * (k₁ + 2)) ?_ h_gks_rest
            dsimp [S_in]; split_ifs <;> omega
      · -- Branch 4: ks = k₁ :: ks_rest, x₀ = 2 * d + 1 (d ≥ 0, k₀ = 2 * d + 2 ≥ 2)
        have hx_split : x₀ = 1 + 2 * d := by omega
        have hk0_ne1 : k₀ ≠ 1 := by omega
        have hS_in_eq : S_in = 72 * (d + 2) := by
          dsimp [S_in]; split_ifs <;> omega
        set S_sub := 36 * (d + 2)
        have hS_sub : S_sub ≥ 36 := by omega
        have hk1_ge3 : k₁ ≥ 3 := by omega
        set sub := bump_enc (k₁ - 1) ks_rest
        have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
          cases ks_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
          cases ks_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys => intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
          cases ks_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * S_sub + 63 * (k₁ - 1 + 3) = S_in + 63 * (k₁ + 2) := by omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        set R_tail :=
            (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
            (0 : Fin 2) >> (1 : Fin 2) >> prepend11_01 d default
        rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 S_sub R_tail rfl hS_sub h_sub_nil
            h_sub_cons h_sub_gks
          with ⟨y₀, ys, h_step_sub, h_val_ys, _, h_gks_sub, _⟩
        set py := bump_enc_twice y₀ ys
        set ks_mid := (py.1 + 1) :: py.2
        have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
        have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
        refine ⟨d, add_last ks_mid (3 * d), ?_,
          Or.inr ⟨add_last_ne_nil ks_mid (3 * d) hne_mid, ?_⟩⟩
        · rw [hx_split] at h_to_e0
          have h1 := e0_loop_drain_pairs d 1 (k₁ :: ks_rest) default
          have hk1_eq : k₁ = (k₁ - 1) + 1 := by omega
          have h2 : (cfg_modeE0_loop (encL 1 (k₁ :: ks_rest)) (prepend11_01 d default))
              [donor311_tm]⊢⁺
              cfg_modeE1 (encL (k₁ - 1) ks_rest)
                ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                    R_tail) := by
            rw [show encL 1 (k₁ :: ks_rest) = encL 1 (((k₁ - 1) + 1) :: ks_rest) by rw [← hk1_eq]]
            exact step_modeE0_loop_b10_b011_10_b10 (encL (k₁ - 1) ks_rest) (prepend11_01 d default)
          have h3 := modeE1_to_modeC ks_rest (k₁ - 1)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                R_tail) h_valid_rest
          have h4 : (cfg_modeC (encL sub.1 sub.2)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
              [donor311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
            step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
          have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d default) h_val_ys
          have h6 := modeC_consume_11_01_nonempty d 0 ks_mid default hne_mid hval_mid
          rw [Nat.zero_add] at h6
          exact stepPlus_stepPlus_stepPlus h_to_e0
            (stepStar_stepPlus_stepPlus h1
              (stepPlus_stepPlus_stepPlus h2
                (stepPlus_stepPlus_stepPlus h3
                  (stepPlus_stepPlus_stepPlus h4
                    (stepPlus_stepPlus_stepPlus h_step_sub
                      (stepPlus_stepStar_stepPlus h5 h6))))))
        · apply GoodKS_add_last
          apply GoodKS_mono ks_mid _ S_sub ?_ h_gks_sub
          split_ifs <;> omega

-- ============================================================================
-- Master Lemma 2b: Drain at R = 01 >> 01 >> default (Cases 0a & 0b of k₀ = 0)
-- ============================================================================

set_option maxRecDepth 200000 in
theorem e0_loop_drain_plus2 (w₀ : ℕ) (ws : List ℕ) (S_w : ℕ)
    (h_empty : ws = [] → w₀ ≥ 4)
    (h_sw : 36 ≤ S_w + 54 * (w₀ / 2))
    (h_gks : GoodKS (S_w + 63 * (w₀ + 3)) ws) :
    ∃ k₀' ks',
      ((cfg_modeE0_loop (encL w₀ ws) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          default))
        [donor311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  set R0 := (0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
  have hR0 : R0 = prepend01 2 default := rfl
  set d := w₀ / 2
  set rem := w₀ % 2
  have h_rem : rem = 0 ∨ rem = 1 := by omega
  cases ws with
  | nil =>
    have hw4 : w₀ ≥ 4 := h_empty rfl
    rcases h_rem with h_even | h_odd
    · -- Case 2: ws = [], w₀ = 2 * d (d ≥ 2)
      have hd : d ≥ 2 := by omega
      have hw_split : w₀ = 0 + 2 * d := by omega
      refine ⟨d + 3, [3 * d], ?_, Or.inr ⟨by simp, ?_⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 0 [] R0
        have h2 := step_modeE0_loop_base (prepend11_01 d R0)
        have h3 := step_modeC_b01 (encL 0 [0]) (prepend11_01 d R0)
        have h4 := modeC_consume_11_01_nonempty d 1 [0] R0 (by simp) trivial
        simp only [add_last, Nat.zero_add] at h4
        rw [hR0] at h4
        have h5 := modeC_prepend01_star 2 (1 + d) [3 * d] default
        have heq : 1 + d + 2 = d + 3 := by omega
        rw [heq] at h5
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 h5)))
      · have hd3_ne : d + 3 ≠ 1 := by omega
        simp only [hd3_ne, ite_false, GoodKS]
        exact ⟨by omega, trivial⟩
    · -- Case 1: ws = [], w₀ = 2 * d + 1 (d ≥ 1)
      have hd : d ≥ 1 := by omega
      have hw_split : w₀ = 1 + 2 * d := by omega
      refine ⟨4 * d + 9, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 1 [] R0
        have h2 : (cfg_modeE0_loop (encL 1 []) (prepend11_01 d R0)) [donor311_tm]⊢⁺
            cfg_modeC (encL 0 []) (prepend01 3 (prepend11_01 (d + 1) R0)) :=
          step_modeE0_loop_b10_base (prepend11_01 d R0)
        have h3 := modeC_prepend01_star 3 0 [] (prepend11_01 (d + 1) R0)
        rw [Nat.zero_add] at h3
        have h4 := modeC_consume_11_01_nil (d + 1) 3 R0
        rw [hR0] at h4
        have h5 := modeC_prepend01_star 2 (3 + 4 * (d + 1)) [] default
        have heq : 3 + 4 * (d + 1) + 2 = 4 * d + 9 := by omega
        rw [heq] at h5
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepStar_stepPlus h2 (stepStar_trans h3 (stepStar_trans h4 h5)))
  | cons w₁ ws_rest =>
    have ⟨hw1_bound, h_gks_rest⟩ := h_gks
    have hw1_ge : w₁ ≥ 4 := by omega
    have h_valid_rest : ValidKS ws_rest :=
      GoodKS_valid ws_rest (S_w + 63 * (w₀ + 3) + 63 * (w₁ + 2)) (by omega) h_gks_rest
    rcases h_rem with h_even | h_odd
    · -- Case 3: ws = w₁ :: ws_rest, w₀ = 2 * d (d ≥ 0)
      have hw_split : w₀ = 0 + 2 * d := by omega
      cases ws_rest with
      | nil =>
        refine ⟨w₁ + 4 * d + 9, [], ?_, Or.inl ⟨rfl, by omega⟩⟩
        rw [hw_split]
        have h1 := e0_loop_drain_pairs d 0 [w₁] R0
        have h2 : (cfg_modeE0_loop (encL 0 [w₁]) (prepend11_01 d R0)) [donor311_tm]⊢⁺
            cfg_modeE1 (encL w₁ []) (prepend01 4 (prepend11_01 d R0)) :=
          step_modeE0_loop_b011_10 (encL w₁ []) (prepend11_01 d R0)
        have h3 := modeE1_to_modeC [] w₁ (prepend01 4 (prepend11_01 d R0)) trivial
        dsimp [bump_enc] at h3
        have h4 := modeC_prepend01_star 4 (w₁ + 3) [] (prepend11_01 d R0)
        have h5 := modeC_consume_11_01_nil d (w₁ + 3 + 4) R0
        rw [hR0] at h5
        have h6 := modeC_prepend01_star 2 (w₁ + 3 + 4 + 4 * d) [] default
        have heq : w₁ + 3 + 4 + 4 * d + 2 = w₁ + 4 * d + 9 := by omega
        rw [heq] at h6
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 (stepStar_trans h5 h6))))
      | cons w₂ rest' =>
        have hne_rest : (w₂ :: rest') ≠ [] := by simp
        refine ⟨w₁ + d + 6, add_last (w₂ :: rest') (3 * d + 3), ?_,
          Or.inr ⟨add_last_ne_nil (w₂ :: rest') (3 * d + 3) hne_rest, ?_⟩⟩
        · rw [hw_split]
          have h1 := e0_loop_drain_pairs d 0 (w₁ :: w₂ :: rest') R0
          have h2 : (cfg_modeE0_loop (encL 0 (w₁ :: w₂ :: rest')) (prepend11_01 d R0))
              [donor311_tm]⊢⁺
              cfg_modeE1 (encL w₁ (w₂ :: rest')) (prepend01 4 (prepend11_01 d R0)) :=
            step_modeE0_loop_b011_10 (encL w₁ (w₂ :: rest')) (prepend11_01 d R0)
          have h3 := modeE1_to_modeC (w₂ :: rest') w₁ (prepend01 4 (prepend11_01 d R0)) h_valid_rest
          rw [bump_enc_nonempty w₁ hne_rest] at h3
          have h4 := modeC_prepend01_star 4 w₁ (add_last (w₂ :: rest') 3) (prepend11_01 d R0)
          have h5 := modeC_consume_11_01_nonempty d (w₁ + 4) (add_last (w₂ :: rest') 3) R0
            (add_last_ne_nil (w₂ :: rest') 3 hne_rest)
            (ValidKS_add_last (w₂ :: rest') 3 h_valid_rest)
          have heq1 : w₁ + 4 + d + 2 = w₁ + d + 6 := by omega
          have heq2 : 3 + 3 * d = 3 * d + 3 := by omega
          rw [add_last_add, heq2, hR0] at h5
          have h6 :=
              modeC_prepend01_star 2 (w₁ + 4 + d) (add_last (w₂ :: rest') (3 * d + 3)) default
          rw [heq1] at h6
          exact stepStar_stepPlus_stepPlus h1
            (stepPlus_stepPlus_stepPlus h2
              (stepPlus_stepStar_stepPlus h3 (stepStar_trans h4 (stepStar_trans h5 h6))))
        · have h_ne1 : w₁ + d + 6 ≠ 1 := by omega
          simp only [h_ne1, ite_false]
          apply GoodKS_add_last
          exact GoodKS_mono (w₂ :: rest') _ _ (by omega) h_gks_rest
    · -- Case 4: ws = w₁ :: ws_rest, w₀ = 2 * d + 1 (d ≥ 0)
      have hw_split : w₀ = 1 + 2 * d := by omega
      set S_sub := 36 * (d + 4)
      have hS_sub : S_sub ≥ 36 := by omega
      have h_2S_le : 2 * S_sub ≤ S_w + 63 * (w₀ + 3) := by omega
      set sub := bump_enc (w₁ - 1) ws_rest
      have h_sub_nil : sub.2 = [] → 2 * S_sub ≤ 35 * sub.1 := by
        cases ws_rest with
        | nil => intro _; simp [sub, bump_enc]; omega
        | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
      have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * S_sub ≤ 35 * (sub.1 + 3) := by
        cases ws_rest with
        | nil => intro h_ne; simp [sub, bump_enc] at h_ne
        | cons y ys => intro _; simp [sub, bump_enc]; omega
      have h_sub_gks : GoodKS (2 * S_sub + 63 * (sub.1 + 3)) sub.2 := by
        cases ws_rest with
        | nil => simp [sub, bump_enc, GoodKS]
        | cons y ys =>
          simp only [sub, bump_enc]
          apply GoodKS_add_last
          exact GoodKS_mono (y :: ys) _ _ (by omega) h_gks_rest
      set R_tail :=
          (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
          (1 : Fin 2) >> prepend11_01 d R0
      rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 S_sub R_tail rfl hS_sub h_sub_nil
          h_sub_cons h_sub_gks
        with ⟨y₀, ys, h_step_sub, h_val_ys, _, h_gks_sub, _⟩
      set py := bump_enc_twice y₀ ys
      set ks_mid := (py.1 + 1) :: py.2
      have hne_mid : ks_mid ≠ [] := by simp [ks_mid]
      have hval_mid : ValidKS ks_mid := GoodKS_succ_valid S_sub py.1 py.2 h_gks_sub
      refine ⟨d + 2, add_last ks_mid (3 * d), ?_,
        Or.inr ⟨add_last_ne_nil ks_mid (3 * d) hne_mid, ?_⟩⟩
      · rw [hw_split]
        have h1 := e0_loop_drain_pairs d 1 (w₁ :: ws_rest) R0
        have hw1_eq : w₁ = (w₁ - 1) + 1 := by omega
        have h2 : (cfg_modeE0_loop (encL 1 (w₁ :: ws_rest)) (prepend11_01 d R0)) [donor311_tm]⊢⁺
            cfg_modeE1 (encL (w₁ - 1) ws_rest)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail) :=
                  by
          rw [show encL 1 (w₁ :: ws_rest) = encL 1 (((w₁ - 1) + 1) :: ws_rest) by rw [← hw1_eq]]
          exact step_modeE0_loop_b10_b011_10_b10 (encL (w₁ - 1) ws_rest) (prepend11_01 d R0)
        have h3 := modeE1_to_modeC ws_rest (w₁ - 1)
          ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
              R_tail) h_valid_rest
        have h4 : (cfg_modeC (encL sub.1 sub.2)
            ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> R_tail))
            [donor311_tm]⊢⁺ cfg_modeE0_loop (encL sub.1 sub.2) R_tail :=
          step_modeC_b01_b000 (encL sub.1 sub.2) R_tail
        have h5 := unwrap_11_01_1011101_step y₀ ys (prepend11_01 d R0) h_val_ys
        have h6 := modeC_consume_11_01_nonempty d 0 ks_mid R0 hne_mid hval_mid
        rw [Nat.zero_add, hR0] at h6
        have h7 := modeC_prepend01_star 2 d (add_last ks_mid (3 * d)) default
        exact stepStar_stepPlus_stepPlus h1
          (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepPlus_stepPlus h3
              (stepPlus_stepPlus_stepPlus h4
                (stepPlus_stepPlus_stepPlus h_step_sub
                  (stepPlus_stepStar_stepPlus h5 (stepStar_trans h6 h7))))))
      · have hd2_ne : d + 2 ≠ 1 := by omega
        simp only [hd2_ne, ite_false]
        exact GoodKS_add_last ks_mid S_sub (3 * d) h_gks_sub

-- ============================================================================
-- k₀ = 0 Transition (Cases 0a, 0b, 0c)
-- ============================================================================

theorem step_b01_b101_nil_to_e0_loop (p₀ : ℕ) (ps : List ℕ) (h_val : ValidKS ps) :
    let w := bump_enc p₀ ps
    (cfg_modeC (encL p₀ ps) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
        (1 : Fin 2) >> default))
      [donor311_tm]⊢⁺
      cfg_modeE0_loop (encL w.1 w.2) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
          default) := by
  dsimp
  set w := bump_enc p₀ ps
  have h1 := step_modeC_b01_b101_nil (encL p₀ ps)
  have h2 := modeE1_to_modeC ps p₀
    ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> ((0 : Fin 2) >>
        (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >> default)))
    h_val
  have h3 :=
      step_modeC_b01_b000 (encL w.1 w.2) ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
      (1 : Fin 2) >> default)
  exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 h3)

theorem step_k0_zero (ks : List ℕ) (h_inv : InvNil 0 ks) :
    ∃ k₀' ks',
      ((cfg_modeC (encL 0 ks) default) [donor311_tm]⊢⁺ cfg_modeC (encL k₀' ks') default) ∧
      InvNil k₀' ks' := by
  rcases h_inv with ⟨ _, hk5 ⟩ | ⟨ hne, h_gks ⟩
  · omega
  · simp only [ Nat.reduceEqDiff, ite_false ] at h_gks
    cases ks with
    | nil => contradiction
    | cons k₁ ks_rest =>
      have ⟨hk1_bound, h_gks_rest⟩ := h_gks
      have hk1_ge : k₁ ≥ 1 := by omega
      have h_valid_rest : ValidKS ks_rest :=
        GoodKS_valid ks_rest (72 + 63 * (k₁ + 2)) (by omega) h_gks_rest
      set sub := bump_enc (k₁ - 1) ks_rest
      have h_to_sub : (cfg_modeC (encL 0 (k₁ :: ks_rest)) default) [donor311_tm]⊢⁺
          cfg_modeE0_loop (encL sub.1 sub.2) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
              default) := by
        have hk1_eq : k₁ = (k₁ - 1) + 1 := by omega
        have h1 := step_modeC_nil (encL 0 (k₁ :: ks_rest))
        have h2 : (cfg_modeE0_first (encL 0 (k₁ :: ks_rest))) [donor311_tm]⊢⁺
            cfg_modeE1 (encL (k₁ - 1) ks_rest)
              ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                  ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) := by
          rw [show encL 0 (k₁ :: ks_rest) = encL 0 (((k₁ - 1) + 1) :: ks_rest) by rw [← hk1_eq]]
          exact step_modeE0_first_b011_10_b10 (encL (k₁ - 1) ks_rest)
        have h3 := modeE1_to_modeC ks_rest (k₁ - 1)
          ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
              ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default))
          h_valid_rest
        have h4 :=
            step_modeC_b01_b000 (encL sub.1 sub.2) ((1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
            default)
        exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2
            (stepPlus_stepPlus_stepPlus h3 h4))
      -- Split on ks_rest = [] ∨ k₁ ≥ 3 (Case 0a), k₁ = 1 ∧ ks_rest ≠ [] (Case 0b), k₁ = 2 ∧ ks_rest
      -- ≠ [] (Case 0c)
      by_cases h_0a : ks_rest = [] ∨ k₁ ≥ 3
      · -- Case 0a: leave1(sub.1, sub.2) with S = 36
        have h_sub_nil : sub.2 = [] → 2 * 36 ≤ 35 * sub.1 := by
          cases ks_rest with
          | nil => intro _; simp [sub, bump_enc]; omega
          | cons y ys => intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
        have h_sub_cons : sub.2 ≠ [] → sub.1 ≥ 2 ∧ 2 * 36 ≤ 35 * (sub.1 + 3) := by
          cases ks_rest with
          | nil => intro h_ne; simp [sub, bump_enc] at h_ne
          | cons y ys =>
            rcases h_0a with h_emp | hk3
            · simp at h_emp
            · intro _; simp [sub, bump_enc]; omega
        have h_sub_gks : GoodKS (2 * 36 + 63 * (sub.1 + 3)) sub.2 := by
          cases ks_rest with
          | nil => simp [sub, bump_enc, GoodKS]
          | cons y ys =>
            simp only [sub, bump_enc]
            have heq_s : 2 * 36 + 63 * (k₁ - 1 + 3) = 72 + 63 * (k₁ + 2) := by omega
            rw [heq_s]
            exact GoodKS_add_last (y :: ys) _ 3 h_gks_rest
        rcases e0_loop_leave1_goodks sub.2.length sub.1 sub.2 36 ((1 : Fin 2) >> (0 : Fin 2) >>
            (1 : Fin 2) >> default)
          rfl (by omega) h_sub_nil h_sub_cons h_sub_gks
          with ⟨m₀, ms, h_step_l1, h_val_ms, h_ms_emp, h_gks_w, _⟩
        set p1 := bump_enc m₀ ms
        set w := bump_enc_twice m₀ ms
        have hw_eq : w = bump_enc p1.1 p1.2 := rfl
        have h_c11 : (cfg_modeC (encL m₀ ms)
            ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                (0 : Fin 2) >> (1 : Fin 2) >> default))
            [donor311_tm]⊢⁺
            cfg_modeC (encL p1.1 p1.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                (1 : Fin 2) >> default) :=
          stepPlus_stepPlus_stepPlus
            (step_modeC_b11 (encL m₀ ms) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                (0 : Fin 2) >> (1 : Fin 2) >> default))
            (modeE1_to_modeC ms m₀ ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                (1 : Fin 2) >> default) h_val_ms)
        have h_to_w := step_b01_b101_nil_to_e0_loop p1.1 p1.2 (ValidKS_bump_enc m₀ ms h_val_ms)
        have h_w_empty : w.2 = [] → w.1 ≥ 4 := by
          cases ms with
          | nil =>
            intro _; dsimp only [w, bump_enc_twice, bump_enc]; omega
          | cons u us =>
            intro h_emp
            dsimp only [w] at h_emp
            rw [bump_enc_twice_nonempty m₀ (by simp)] at h_emp
            exact absurd h_emp (add_last_ne_nil (u :: us) 6 (by simp))
        have h_gks_ws : GoodKS (36 + 63 * (w.1 + 3)) w.2 := by
          have h2 := h_gks_w.2
          have heq : 36 + 63 * (w.1 + 1 + 2) = 36 + 63 * (w.1 + 3) := by omega
          rw [heq] at h2; exact h2
        rcases e0_loop_drain_plus2 w.1 w.2 36 h_w_empty (by omega) h_gks_ws with ⟨k₀', ks', h_drain,
            h_inv'⟩
        exact ⟨k₀', ks',
          stepPlus_stepPlus_stepPlus h_to_sub
            (stepPlus_stepPlus_stepPlus h_step_l1
              (stepPlus_stepPlus_stepPlus h_c11
                (stepPlus_stepPlus_stepPlus h_to_w h_drain))),
          h_inv'⟩
      · -- Not Case 0a: ks_rest ≠ [] and k₁ < 3 (so k₁ = 1 or k₁ = 2)
        push Not at h_0a
        rcases h_0a with ⟨hne_rest, hk1_lt3⟩
        cases ks_rest with
        | nil => contradiction
        | cons k₂ ks_tail =>
          have hk1_cases : k₁ = 1 ∨ k₁ = 2 := by omega
          rcases hk1_cases with rfl | rfl
          · -- Case 0b: k₁ = 1, ks_rest = k₂ :: ks_tail
            have h_sub_eq : sub = (0, add_last (k₂ :: ks_tail) 3) := rfl
            have h_gks_sub : GoodKS 261 (add_last (k₂ :: ks_tail) 3) :=
              GoodKS_add_last (k₂ :: ks_tail) 261 3 h_gks_rest
            cases h_al : add_last (k₂ :: ks_tail) 3 with
            | nil => exact absurd h_al (add_last_ne_nil (k₂ :: ks_tail) 3 (by simp))
            | cons x₁ xs_rest =>
              rw [h_al] at h_gks_sub
              have ⟨hx1_bound, h_gks_xs⟩ := h_gks_sub
              have hx1_ge6 : x₁ ≥ 6 := by omega
              have h_val_xs : ValidKS xs_rest :=
                GoodKS_valid xs_rest (261 + 63 * (x₁ + 2)) (by omega) h_gks_xs
              set xb := bump_enc x₁ xs_rest
              set p1 : ℕ × List ℕ := (xb.1 + 3, xb.2)
              set w := bump_enc p1.1 p1.2
              have h_step_0b : (cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >>
                  (0 : Fin 2) >> (1 : Fin 2) >> default))
                  [donor311_tm]⊢⁺
                  cfg_modeC (encL p1.1 p1.2) ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                      (0 : Fin 2) >> (1 : Fin 2) >> default) := by
                have h1 : (cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >> (0 : Fin 2) >>
                    (1 : Fin 2) >> default))
                    [donor311_tm]⊢⁺
                    cfg_modeE1 (encL x₁ xs_rest) (prepend01 3 ((0 : Fin 2) >> (1 : Fin 2) >>
                        (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default)) :=
                  step_modeE0_loop_b011_10 (encL x₁ xs_rest) ((1 : Fin 2) >> (0 : Fin 2) >>
                      (1 : Fin 2) >> default)
                have h2 := modeE1_to_modeC xs_rest x₁
                  (prepend01 3 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >>
                      (1 : Fin 2) >> default)) h_val_xs
                have h3 :=
                    modeC_prepend01_star 3 xb.1 xb.2 ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                    (0 : Fin 2) >> (1 : Fin 2) >> default)
                exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepStar_stepPlus h2 h3)
              have h_val_p1 : ValidKS p1.2 := ValidKS_bump_enc x₁ xs_rest h_val_xs
              have h_to_w := step_b01_b101_nil_to_e0_loop p1.1 p1.2 h_val_p1
              have hw1_ge9 : w.1 ≥ 9 := by
                cases xs_rest with
                | nil => dsimp only [w, p1, xb, bump_enc]; omega
                | cons y ys =>
                  have hw_cons : w = (x₁ + 3, add_last (y :: ys) 6) := by
                    change bump_enc (x₁ + 3) (add_last (y :: ys) 3) = _
                    rw [bump_enc_nonempty (x₁ + 3) (add_last_ne_nil (y :: ys) 3 (by simp)),
                        add_last_add]
                  rw [hw_cons]; dsimp only; omega
              have h_w_empty : w.2 = [] → w.1 ≥ 4 := fun _ => by omega
              have h_sw9 : 36 ≤ 9 + 54 * (w.1 / 2) := by omega
              have h_gks_ws : GoodKS (9 + 63 * (w.1 + 3)) w.2 := by
                cases xs_rest with
                | nil => simp [w, p1, xb, bump_enc, GoodKS]
                | cons y ys =>
                  have hw_cons : w = (x₁ + 3, add_last (y :: ys) 6) := by
                    change bump_enc (x₁ + 3) (add_last (y :: ys) 3) = _
                    rw [bump_enc_nonempty (x₁ + 3) (add_last_ne_nil (y :: ys) 3 (by simp)),
                        add_last_add]
                  rw [hw_cons]
                  dsimp only
                  have heq : 9 + 63 * (x₁ + 3 + 3) = 261 + 63 * (x₁ + 2) := by omega
                  rw [heq]
                  exact GoodKS_add_last (y :: ys) _ 6 h_gks_xs
              rcases e0_loop_drain_plus2 w.1 w.2 9 h_w_empty h_sw9 h_gks_ws with ⟨k₀', ks', h_drain,
                  h_inv'⟩
              have h_to_sub' : (cfg_modeC (encL 0 (1 :: k₂ :: ks_tail)) default) [donor311_tm]⊢⁺
                  cfg_modeE0_loop (encL 0 (x₁ :: xs_rest)) ((1 : Fin 2) >> (0 : Fin 2) >>
                      (1 : Fin 2) >> default) := by
                simpa [h_sub_eq, h_al] using h_to_sub
              exact ⟨k₀', ks',
                stepPlus_stepPlus_stepPlus h_to_sub'
                  (stepPlus_stepPlus_stepPlus h_step_0b
                    (stepPlus_stepPlus_stepPlus h_to_w h_drain)),
                h_inv'⟩
          · -- Case 0c: k₁ = 2, ks_rest = k₂ :: ks_tail
            have h_sub_eq : sub = (1, add_last (k₂ :: ks_tail) 3) := rfl
            have h_gks_sub : GoodKS 324 (add_last (k₂ :: ks_tail) 3) :=
              GoodKS_add_last (k₂ :: ks_tail) 324 3 h_gks_rest
            cases h_al : add_last (k₂ :: ks_tail) 3 with
            | nil => exact absurd h_al (add_last_ne_nil (k₂ :: ks_tail) 3 (by simp))
            | cons x₁ xs_rest =>
              rw [h_al] at h_gks_sub
              have ⟨hx1_bound, h_gks_xs⟩ := h_gks_sub
              have hx1_ge8 : x₁ ≥ 8 := by omega
              have h_val_xs : ValidKS xs_rest :=
                GoodKS_valid xs_rest (324 + 63 * (x₁ + 2)) (by omega) h_gks_xs
              set sub2 := bump_enc (x₁ - 1) xs_rest
              set R_101 := (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> default
              set R_1011101_101 :=
                  (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >>
                  (0 : Fin 2) >> (1 : Fin 2) >> R_101
              -- Step 1 of Case 0c
              have h_step1 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101) [donor311_tm]⊢⁺
                  cfg_modeE0_loop (encL sub2.1 sub2.2) R_1011101_101 := by
                have hx1_eq : x₁ = (x₁ - 1) + 1 := by omega
                have h1 : (cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101) [donor311_tm]⊢⁺
                    cfg_modeE1 (encL (x₁ - 1) xs_rest)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                          R_1011101_101) := by
                  rw [show encL 1 (x₁ :: xs_rest) =
                      encL 1 (((x₁ - 1) + 1) :: xs_rest) by rw [← hx1_eq]]
                  exact step_modeE0_loop_b10_b011_10_b10 (encL (x₁ - 1) xs_rest) R_101
                have h2 := modeE1_to_modeC xs_rest (x₁ - 1)
                  ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                      R_1011101_101) h_val_xs
                have h3 := step_modeC_b01_b000 (encL sub2.1 sub2.2) R_1011101_101
                exact stepPlus_stepPlus_stepPlus h1 (stepPlus_stepPlus_stepPlus h2 h3)
              -- Step 2 of Case 0c: leave1(sub2.1, sub2.2) at S = 162
              have h_sub2_nil : sub2.2 = [] → 2 * 162 ≤ 35 * sub2.1 := by
                cases xs_rest with
                | nil => intro _; simp [sub2, bump_enc]; omega
                | cons y ys =>
                    intro h_emp; exact absurd h_emp (add_last_ne_nil (y :: ys) 3 (by simp))
              have h_sub2_cons : sub2.2 ≠ [] → sub2.1 ≥ 2 ∧ 2 * 162 ≤ 35 * (sub2.1 + 3) := by
                cases xs_rest with
                | nil => intro h_ne; simp [sub2, bump_enc] at h_ne
                | cons y ys => intro _; simp [sub2, bump_enc]; omega
              have h_sub2_gks : GoodKS (2 * 162 + 63 * (sub2.1 + 3)) sub2.2 := by
                cases xs_rest with
                | nil => simp [sub2, bump_enc, GoodKS]
                | cons y ys =>
                  simp only [sub2, bump_enc]
                  have heq_s : 2 * 162 + 63 * (x₁ - 1 + 3) = 324 + 63 * (x₁ + 2) := by omega
                  rw [heq_s]
                  exact GoodKS_add_last (y :: ys) _ 3 h_gks_xs
              rcases e0_loop_leave1_goodks sub2.2.length sub2.1 sub2.2 162 R_1011101_101
                rfl (by omega) h_sub2_nil h_sub2_cons h_sub2_gks
                with ⟨y₀, ys, h_step_l2, h_val_ys, h_ys_emp, h_gks_z, _⟩
              have h_unwrap2 := unwrap_11_01_1011101_step y₀ ys R_101 h_val_ys
              set pz := bump_enc_twice y₀ ys
              set z₁ := pz.1 + 1
              set zs := pz.2
              have ⟨hz1_bound, h_gks_zs⟩ := h_gks_z
              have hz1_ge3 : z₁ ≥ 3 := by omega
              have h_zs_emp_z1 : zs = [] → z₁ ≥ 14 := by
                cases ys with
                | nil =>
                  have hy7 : y₀ ≥ 7 := h_ys_emp rfl
                  intro _; dsimp only [z₁, pz, bump_enc_twice, bump_enc]; omega
                | cons u us =>
                  intro h_emp
                  dsimp only [zs, pz] at h_emp
                  rw [bump_enc_twice_nonempty y₀ (by simp)] at h_emp
                  exact absurd h_emp (add_last_ne_nil (u :: us) 6 (by simp))
              have h_val_zs : ValidKS zs :=
                GoodKS_valid zs (162 + 63 * (z₁ + 2)) (by omega) h_gks_zs
              -- Step 3 & 4 of Case 0c: Transition A + Transition B
              set zb := bump_enc (z₁ - 1) zs
              set w := bump_enc zb.1 zb.2
              set R_0000101 :=
                  (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                  (0 : Fin 2) >> (1 : Fin 2) >> default
              set R_101_01_01 :=
                  (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> ((0 : Fin 2) >> (1 : Fin 2) >>
                  ((0 : Fin 2) >> (1 : Fin 2) >> default))
              have h_step34 : (cfg_modeC (encL 0 (z₁ :: zs)) R_101) [donor311_tm]⊢⁺
                  cfg_modeE0_loop (encL w.1 w.2) R_101_01_01 := by
                have hz1_eq : z₁ = (z₁ - 1) + 1 := by omega
                have hA : (cfg_modeC (encL 0 (z₁ :: zs)) R_101) [donor311_tm]⊢⁺
                    cfg_modeE1 (encL (z₁ - 1) zs)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                          (0 : Fin 2) >> (1 : Fin 2) >> R_0000101) := by
                  rw [show encL 0 (z₁ :: zs) = encL 0 (((z₁ - 1) + 1) :: zs) by rw [← hz1_eq]]
                  exact step_modeC_b01110_b10_b101_nil (encL (z₁ - 1) zs)
                have hA2 := modeE1_to_modeC zs (z₁ - 1)
                  ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                      (0 : Fin 2) >> (1 : Fin 2) >> R_0000101) h_val_zs
                have hA3 : (cfg_modeC (encL zb.1 zb.2)
                    ((0 : Fin 2) >> (1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >>
                        (0 : Fin 2) >> (1 : Fin 2) >> R_0000101))
                    [donor311_tm]⊢⁺ cfg_modeC (encL 0 ((zb.1 + 1) :: zb.2)) R_0000101 :=
                  step_modeC_b01_b10101 (encL zb.1 zb.2) R_0000101
                have hB : (cfg_modeC (encL 0 ((zb.1 + 1) :: zb.2)) R_0000101) [donor311_tm]⊢⁺
                    cfg_modeE1 (encL zb.1 zb.2)
                      ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                          R_101_01_01) :=
                  step_modeC_b01110_b10_b0000101 (encL zb.1 zb.2) default
                have hB2 := modeE1_to_modeC zb.2 zb.1
                  ((0 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >> (0 : Fin 2) >>
                      R_101_01_01)
                  (ValidKS_bump_enc (z₁ - 1) zs h_val_zs)
                have hB3 := step_modeC_b01_b000 (encL w.1 w.2) R_101_01_01
                exact stepPlus_stepPlus_stepPlus hA
                  (stepPlus_stepPlus_stepPlus hA2
                    (stepPlus_stepPlus_stepPlus hA3
                      (stepPlus_stepPlus_stepPlus hB
                        (stepPlus_stepPlus_stepPlus hB2 hB3))))
              -- Step 5 of Case 0c: leave1(w.1, w.2) at S = 81
              have hw_def : w = bump_enc_twice (z₁ - 1) zs := rfl
              have h_w_nil : w.2 = [] → 2 * 81 ≤ 35 * w.1 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hz14 : z₁ ≥ 14 := h_zs_emp_z1 h_zs
                  have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro _; dsimp only; omega
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro h_emp
                  exact absurd h_emp (add_last_ne_nil (y :: ys') 6 (by simp))
              have h_w_ge10 : w.2 = [] → w.1 ≥ 10 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hz14 : z₁ ≥ 14 := h_zs_emp_z1 h_zs
                  have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro _; dsimp only; omega
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro h_emp
                  exact absurd h_emp (add_last_ne_nil (y :: ys') 6 (by simp))
              have h_w_cons : w.2 ≠ [] → w.1 ≥ 2 ∧ 2 * 81 ≤ 35 * (w.1 + 3) := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; intro h_ne; exact absurd rfl h_ne
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]; intro _; dsimp only; omega
              have h_w_gks : GoodKS (2 * 81 + 63 * (w.1 + 3)) w.2 := by
                rcases h_zs : zs with _ | ⟨y, ys'⟩
                · have hw_nil : w = (z₁ - 1 + 3 + 3, []) := by rw [hw_def, h_zs]; rfl
                  rw [hw_nil]; trivial
                · have hw_cons : w = (z₁ - 1, add_last (y :: ys') 6) := by
                    rw [hw_def, h_zs, bump_enc_twice_nonempty (z₁ - 1) (by simp)]
                  rw [hw_cons]
                  dsimp only
                  have heq_s : 2 * 81 + 63 * (z₁ - 1 + 3) = 162 + 63 * (z₁ + 2) := by omega
                  rw [heq_s]
                  have h_gks_zs' : GoodKS (162 + 63 * (z₁ + 2)) (y :: ys') := by
                    rw [← h_zs]; exact h_gks_zs
                  exact GoodKS_add_last (y :: ys') _ 6 h_gks_zs'
              rcases e0_loop_leave1_goodks w.2.length w.1 w.2 81 R_101_01_01
                rfl (by omega) h_w_nil h_w_cons h_w_gks
                with ⟨m₀, ms, h_step_l5, h_val_ms, _, _, h_gks_81_fn⟩
              have h_gks_b1 := h_gks_81_fn h_w_ge10 rfl
              set b1 := bump_enc m₀ ms
              -- Step 6 of Case 0c: 4 final steps to cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default
              have h_step6 : (cfg_modeC (encL m₀ ms)
                  ((1 : Fin 2) >> (1 : Fin 2) >> (0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01))
                  [donor311_tm]⊢⁺
                  cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default := by
                have h1 := step_modeC_b11 (encL m₀ ms) ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01)
                have h2 :=
                    modeE1_to_modeC ms m₀ ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01) h_val_ms
                have h3 : (cfg_modeC (encL b1.1 b1.2) ((0 : Fin 2) >> (1 : Fin 2) >> R_101_01_01))
                    [donor311_tm]⊢⁺
                    cfg_modeC (encL 0 ((b1.1 + 1) :: b1.2)) ((0 : Fin 2) >> (1 : Fin 2) >>
                        default) :=
                  step_modeC_b01_b10101 (encL b1.1 b1.2) ((0 : Fin 2) >> (1 : Fin 2) >> default)
                have h4 : (cfg_modeC (encL 0 ((b1.1 + 1) :: b1.2)) ((0 : Fin 2) >> (1 : Fin 2) >>
                    default))
                    [donor311_tm]⊢⁺
                    cfg_modeC (encL 1 ((b1.1 + 1) :: b1.2)) default :=
                  step_modeC_b01 (encL 0 ((b1.1 + 1) :: b1.2)) default
                exact stepPlus_stepPlus_stepPlus h1
                  (stepPlus_stepPlus_stepPlus h2
                    (stepPlus_stepPlus_stepPlus h3 h4))
              have h_to_sub' : (cfg_modeC (encL 0 (2 :: k₂ :: ks_tail)) default) [donor311_tm]⊢⁺
                  cfg_modeE0_loop (encL 1 (x₁ :: xs_rest)) R_101 := by
                simpa [h_sub_eq, h_al] using h_to_sub
              exact ⟨1, (b1.1 + 1) :: b1.2,
                stepPlus_stepPlus_stepPlus h_to_sub'
                  (stepPlus_stepPlus_stepPlus h_step1
                    (stepPlus_stepPlus_stepPlus h_step_l2
                      (stepPlus_stepPlus_stepPlus h_unwrap2
                        (stepPlus_stepPlus_stepPlus h_step34
                          (stepPlus_stepPlus_stepPlus h_step_l5 h_step6))))),
                Or.inr ⟨by simp, by simpa [InvNil] using h_gks_b1⟩⟩

-- ============================================================================
-- Top-Level Invariant and Non-Halting Theorem
-- ============================================================================

def Inv (c : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ k₀ ks, c = cfg_modeC (encL k₀ ks) default ∧ InvNil k₀ ks


theorem inv_step (c : Cfg (Fin 2) (Fin 6)) (h : Inv c) :
    ∃ c', (c [donor311_tm]⊢⁺ c') ∧ Inv c' := by
  rcases h with ⟨k₀, ks, rfl, h_inv⟩
  cases k₀ with
  | zero =>
    rcases step_k0_zero ks h_inv with ⟨k₀', ks', h_step, h_inv'⟩
    exact ⟨cfg_modeC (encL k₀' ks') default, h_step, ⟨k₀', ks', rfl, h_inv'⟩⟩
  | succ k₀' =>
    rcases step_k0_pos (k₀' + 1) ks (by omega) h_inv with ⟨k₀'', ks'', h_step, h_inv'⟩
    exact ⟨cfg_modeC (encL k₀'' ks'') default, h_step, ⟨k₀'', ks'', rfl, h_inv'⟩⟩




end TM311Donor

namespace TM1Donor

open BusyBeaver.Counter

def donor1_machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB1LD_0RC1RC_1LA1RE_HHH1LE_1RF0RC_0RB0LF"

abbrev tm1 : Machine (Fin 2) (Fin 6) := donor1_machine.toBB



-- ============================================================================
-- 1. Canonical Configuration Family `Kr n a b c d` & `Ev N X`
-- ============================================================================

def G : List (Fin 2) :=
  [0, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 1, 1, 0, 1, 1,
   0, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 1, 1, 0, 0]

def l39Bits : List (Fin 2) :=
  [1, 1, 0, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0,
   0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 0, 1, 0, 1, 1]

def l41Bits : List (Fin 2) := [0, 1] ++ l39Bits

def krRightList (n a b c d : Nat) : List (Fin 2) :=
  G ++ [1] ++ ([1, 1] : List (Fin 2)) ^ n ++
  [0] ++ ([1, 1] : List (Fin 2)) ^ a ++
  [0, 1, 1, 0] ++ ([1, 1] : List (Fin 2)) ^ b ++
  [0, 0, 0, 0, 0, 0, 1] ++ ([1, 1] : List (Fin 2)) ^ c ++
  [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] ++ ([1, 1] : List (Fin 2)) ^ d ++
  [0, 1, 1, 0, 0, 1, 1, 0, 1, 1, 1]

def Kr (n a b c d : Nat) : Cfg (Fin 2) (Fin 6) :=
  default <{{5}} (krRightList n a b c d +> default)

theorem Kr_congr {n1 n2 a1 a2 b1 b2 c1 c2 d1 d2 : Nat}
    (hn : n1 = n2) (ha : a1 = a2) (hb : b1 = b2) (hc : c1 = c2) (hd : d1 = d2) :
    Kr n1 a1 b1 c1 d1 = Kr n2 a2 b2 c2 d2 := by
  subst hn; subst ha; subst hb; subst hc; subst hd; rfl

def Ev (N X : Nat) : Cfg (Fin 2) (Fin 6) :=
  Kr N (4 * X + 26) (2 * X + 32) 17 9

-- ============================================================================
-- 2. Elementary 2-Cell Shift Lemmas, Word Commutations & Chaotic-Edge Jumps
-- ============================================================================

theorem shiftR_2_11_one (l r : ListBlank (Fin 2)) :
    (l {{2}}> ([1, 1] +> r)) [tm1]⊢* (([0, 1] +> l) {{2}}> r) :=
  run_local_spec (tm := tm1) (n := 2)
    (s1 := ⟨[], [1, 1], 2, .right⟩) (s2 := ⟨[0, 1], [], 2, .right⟩) rfl l r

theorem shiftR_2_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{2}}> (([1, 1] : List (Fin 2)) ^ k +> r)) [tm1]⊢*
      ((([0, 1] : List (Fin 2)) ^ k +> l) {{2}}> r) := by
  induction k generalizing l with
  | zero => try exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k r,
        right_pow_succ_right ([0, 1] : List (Fin 2)) k l]
    exact stepStar_trans (shiftR_2_11_one l _) (ih ([0, 1] +> l))

theorem shiftR_2_11_plus (l r : ListBlank (Fin 2)) :
    (l {{2}}> ([1] +> ([1] +> r))) [tm1]⊢⁺ (([0, 1] +> l) {{2}}> r) := by
  have h1 : (l {{2}}> ([1] +> ([1] +> r))) [tm1]⊢ (([1] +> l) {{4}}> ([1] +> r)) :=
    step_local_spec (tm := tm1) (s1 := ⟨[], [1], 2, .right⟩) (s2 := ⟨[1], [], 4, .right⟩)
      rfl l ([1] +> r)
  have h2 : (([1] +> l) {{4}}> ([1] +> r)) [tm1]⊢ (([0, 1] +> l) {{2}}> r) :=
    step_local_spec (tm := tm1) (s1 := ⟨[1], [1], 4, .right⟩) (s2 := ⟨[0, 1], [], 2, .right⟩)
      rfl l r
  exact stepPlus_trans (step_stepPlus tm1 _ _ h1) (step_stepPlus tm1 _ _ h2)

theorem shiftR_4_11_one (l r : ListBlank (Fin 2)) :
    (l {{4}}> ([1, 1] +> r)) [tm1]⊢* (([1, 0] +> l) {{4}}> r) :=
  run_local_spec (tm := tm1) (n := 2)
    (s1 := ⟨[], [1, 1], 4, .right⟩) (s2 := ⟨[1, 0], [], 4, .right⟩) rfl l r

theorem shiftR_4_11 (k : Nat) (l r : ListBlank (Fin 2)) :
    (l {{4}}> (([1, 1] : List (Fin 2)) ^ k +> r)) [tm1]⊢*
      ((([1, 0] : List (Fin 2)) ^ k +> l) {{4}}> r) := by
  induction k generalizing l with
  | zero => try exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k r,
        right_pow_succ_right ([1, 0] : List (Fin 2)) k l]
    exact stepStar_trans (shiftR_4_11_one l _) (ih ([1, 0] +> l))

theorem shiftR_4_11_plus (l r : ListBlank (Fin 2)) :
    (l {{4}}> ([1] +> ([1] +> r))) [tm1]⊢⁺ (([1, 0] +> l) {{4}}> r) := by
  have h1 : (l {{4}}> ([1] +> ([1] +> r))) [tm1]⊢ (([0] +> l) {{2}}> ([1] +> r)) :=
    step_local_spec (tm := tm1) (s1 := ⟨[], [1], 4, .right⟩) (s2 := ⟨[0], [], 2, .right⟩)
      rfl l ([1] +> r)
  have h2 : (([0] +> l) {{2}}> ([1] +> r)) [tm1]⊢ (([1, 0] +> l) {{4}}> r) :=
    step_local_spec (tm := tm1) (s1 := ⟨[0], [1], 2, .right⟩) (s2 := ⟨[1, 0], [], 4, .right⟩)
      rfl l r
  exact stepPlus_trans (step_stepPlus tm1 _ _ h1) (step_stepPlus tm1 _ _ h2)

theorem shiftL_5_10_one (l r : ListBlank (Fin 2)) :
    (([1, 0] +> l) <{{5}} ([0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0] +> ([1, 1] +> r))) :=
  run_local_spec (tm := tm1) (n := 12)
    (s1 := ⟨[1, 0], [0, 0], 5, .left⟩) (s2 := ⟨[], [0, 0, 1, 1], 5, .left⟩) rfl l r

theorem shiftL_5_10 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((([1, 0] : List (Fin 2)) ^ k +> l) <{{5}} ([0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing r with
  | zero => try exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([1, 0] : List (Fin 2)) k l,
        right_pow_succ_right ([1, 1] : List (Fin 2)) k r]
    exact stepStar_trans (shiftL_5_10_one _ r) (ih ([1, 1] +> r))

theorem shiftL_5_01_one (l r : ListBlank (Fin 2)) :
    (([0, 1] +> l) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0, 0] +> ([1, 1] +> r))) :=
  run_local_spec (tm := tm1) (n := 12)
    (s1 := ⟨[0, 1], [0, 0, 0], 5, .left⟩) (s2 := ⟨[], [0, 0, 0, 1, 1], 5, .left⟩) rfl l r

theorem shiftL_5_01 (k : Nat) (l r : ListBlank (Fin 2)) :
    ((([0, 1] : List (Fin 2)) ^ k +> l) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (l <{{5}} ([0, 0, 0] +> (([1, 1] : List (Fin 2)) ^ k +> r))) := by
  induction k generalizing r with
  | zero => try exact stepStar_refl tm1 _
  | succ k ih =>
    rw [right_pow_succ ([0, 1] : List (Fin 2)) k l,
        right_pow_succ_right ([1, 1] : List (Fin 2)) k r]
    exact stepStar_trans (shiftL_5_01_one _ r) (ih ([1, 1] +> r))

theorem rot_w11 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 1] : List (Fin 2)) ^ k +> ([1] +> s)) =
      [1] +> (([1, 1] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([1, 1] : List (Fin 2)) k,
        right_pow_succ ([1, 1] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

theorem rot_w10 (k : Nat) (s : ListBlank (Fin 2)) :
    (([1, 0] : List (Fin 2)) ^ k +> ([1] +> s)) =
      [1] +> (([0, 1] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([1, 0] : List (Fin 2)) k,
        right_pow_succ ([0, 1] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

theorem rot_w01 (k : Nat) (s : ListBlank (Fin 2)) :
    (([0, 1] : List (Fin 2)) ^ k +> ([0] +> s)) =
      [0] +> (([1, 0] : List (Fin 2)) ^ k +> s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [right_pow_succ ([0, 1] : List (Fin 2)) k,
        right_pow_succ ([1, 0] : List (Fin 2)) k]
    simp only [listblank_append_cons, listblank_append_nil] at ih ⊢
    rw [ih]

theorem zero_list_default : ([0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
  zero_cons_default

theorem zeros2_list_default : ([0, 0] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default :=
    by
  change [0] +> ([0] +> default) = default
  rw [zero_list_default, zero_list_default]

theorem nil_list_default : ([] : List (Fin 2)) +> (default : ListBlank (Fin 2)) = default := rfl

set_option maxRecDepth 200000 in
theorem edge_in_raw (r : ListBlank (Fin 2)) :
    (((l39Bits ++ [0]) +> default) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (([] +> default) <{{5}} (G +> r)) :=
  run_local_spec (tm := tm1) (n := 524)
    (s1 := ⟨l39Bits ++ [0], [0, 0, 0], 5, .left⟩)
    (s2 := ⟨[], G, 5, .left⟩) rfl default r

theorem edge_in (r : ListBlank (Fin 2)) :
    ((l39Bits +> default) <{{5}} ([0, 0, 0] +> r)) [tm1]⊢*
      (default <{{5}} (G +> r)) := by
  have h := edge_in_raw r
  rw [listblank_append_assoc l39Bits [0] default, zero_list_default, nil_list_default] at h
  exact h

set_option maxRecDepth 200000 in
theorem edge_out_raw (r : ListBlank (Fin 2)) :
    (([0, 0] +> default) <{{5}} ((G ++ [1]) +> r)) [tm1]⊢*
      (((l41Bits ++ [0]) +> default) {{2}}> ([1, 1, 1, 1] +> r)) :=
  run_local_spec (tm := tm1) (n := 237)
    (s1 := ⟨[0, 0], G ++ [1], 5, .left⟩)
    (s2 := ⟨l41Bits ++ [0], [1, 1, 1, 1], 2, .right⟩) rfl default r

theorem edge_out (r : ListBlank (Fin 2)) :
    (default <{{5}} (G +> ([1] +> r))) [tm1]⊢*
      ((l41Bits +> default) {{2}}> ([1, 1, 1, 1] +> r)) := by
  have h := edge_out_raw r
  rw [zeros2_list_default, listblank_append_assoc l41Bits [0] default, zero_list_default,
      listblank_append_assoc G [1] r] at h
  exact h

-- ============================================================================
-- 3. Compressed Symbolic Bouncer Verifier (`Q6`, `SymTok`, `runSym`, `checkSym`)
-- ============================================================================

inductive Q6 where
  | q0 | q1 | q2 | q3 | q4 | q5
  deriving DecidableEq

def q6Eq : Q6 → Q6 → Bool
  | .q0, .q0 | .q1, .q1 | .q2, .q2 | .q3, .q3 | .q4, .q4 | .q5, .q5 => true
  | _, _ => false

theorem q6Eq_sound {qa qb : Q6} (h : q6Eq qa qb = true) : qa = qb := by
  cases qa <;> cases qb <;> first | rfl | nomatch h

def dirEq : Dir → Dir → Bool
  | .left, .left | .right, .right => true
  | _, _ => false

theorem dirEq_sound {d1 d2 : Dir} (h : dirEq d1 d2 = true) : d1 = d2 := by
  cases d1 <;> cases d2 <;> first | rfl | nomatch h

def evalQ : Q6 → Fin 6
  | .q0 => 0
  | .q1 => 1
  | .q2 => 2
  | .q3 => 3
  | .q4 => 4
  | .q5 => 5

def evalBit : Bool → Fin 2
  | false => 0
  | true => 1

def stepQ : Q6 → Bool → Option (Q6 × Bool × Dir)
  | .q0, false => some (.q1, true, .right)
  | .q0, true  => some (.q3, true, .left)
  | .q1, false => some (.q2, false, .right)
  | .q1, true  => some (.q2, true, .right)
  | .q2, false => some (.q0, true, .left)
  | .q2, true  => some (.q4, true, .right)
  | .q3, false => none
  | .q3, true  => some (.q4, true, .left)
  | .q4, false => some (.q5, true, .right)
  | .q4, true  => some (.q2, false, .right)
  | .q5, false => some (.q1, false, .right)
  | .q5, true  => some (.q5, false, .left)

theorem stepQ_sound {q q' : Q6} {x w_bit : Bool} {d' : Dir}
    (h : stepQ q x = some (q', w_bit, d')) :
    tm1 (evalQ q) (evalBit x) = some (some (evalQ q'), Stmt.write (evalBit w_bit) d') := by
  cases q <;> cases x <;> cases h <;> rfl

inductive W2 where
  | w01
  | w10
  | w11
  deriving DecidableEq

def w2Eq : W2 → W2 → Bool
  | .w01, .w01 | .w10, .w10 | .w11, .w11 => true
  | _, _ => false

theorem w2Eq_sound {w1 w2 : W2} (h : w2Eq w1 w2 = true) : w1 = w2 := by
  cases w1 <;> cases w2 <;> first | rfl | nomatch h

def evalW2 : W2 → List (Fin 2)
  | .w01 => [0, 1]
  | .w10 => [1, 0]
  | .w11 => [1, 1]

inductive Var where
  | v0
  | vn
  | va
  | vb
  | vc
  | vd
  | vbc
  deriving DecidableEq

def varEq : Var → Var → Bool
  | .v0, .v0 | .vn, .vn | .va, .va | .vb, .vb | .vc, .vc | .vd, .vd | .vbc, .vbc => true
  | _, _ => false

theorem varEq_sound {v1 v2 : Var} (h : varEq v1 v2 = true) : v1 = v2 := by
  cases v1 <;> cases v2 <;> first | rfl | nomatch h

def evalVar (n a b c d : Nat) : Var → Nat
  | .v0 => 0
  | .vn => n
  | .va => a
  | .vb => b
  | .vc => c
  | .vd => d
  | .vbc => b + c

def canMergeVars : Var → Var → Option Var
  | .v0, v2 => some v2
  | v1, .v0 => some v1
  | .vb, .vc => some .vbc
  | .vc, .vb => some .vbc
  | _, _ => none

theorem canMergeVars_sound (n a b c d : Nat) {v1 v2 vm : Var}
    (h : canMergeVars v1 v2 = some vm) :
    evalVar n a b c d v1 + evalVar n a b c d v2 = evalVar n a b c d vm := by
  cases v1 <;> cases v2 <;> cases h <;> simp only [evalVar] <;> omega

inductive SymTok where
  | b0
  | b1
  | pow (w : W2) (k : Nat) (v : Var)
  deriving DecidableEq

def tokEq : SymTok → SymTok → Bool
  | .b0, .b0 => true
  | .b1, .b1 => true
  | .pow w1 k1 v1, .pow w2 k2 v2 => w2Eq w1 w2 && Nat.beq k1 k2 && varEq v1 v2
  | _, _ => false

theorem tokEq_sound {t1 t2 : SymTok} (h : tokEq t1 t2 = true) : t1 = t2 := by
  rcases t1 with _ | _ | ⟨w1, k1, v1⟩ <;> rcases t2 with _ | _ | ⟨w2, k2, v2⟩
  · rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · rfl
  · nomatch h
  · nomatch h
  · nomatch h
  · dsimp [tokEq] at h
    simp only [Bool.and_assoc, Bool.and_eq_true, Nat.beq_eq] at h
    rcases h with ⟨hw, rfl, hv⟩
    rw [w2Eq_sound hw, varEq_sound hv]

def tokListEq : List SymTok → List SymTok → Bool
  | [], [] => true
  | x :: xs, y :: ys => tokEq x y && tokListEq xs ys
  | _, _ => false

theorem tokListEq_sound {l1 l2 : List SymTok} (h : tokListEq l1 l2 = true) : l1 = l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons _ _ => nomatch h
  | cons x xs ih =>
    cases l2 with
    | nil => nomatch h
    | cons y ys =>
      dsimp [tokListEq] at h
      simp only [Bool.and_eq_true] at h
      rw [tokEq_sound h.1, ih h.2]

def bitToTok : Fin 2 → SymTok
  | 0 => .b0
  | 1 => .b1

def evalTok (n a b c d : Nat) : SymTok → List (Fin 2)
  | .b0 => [0]
  | .b1 => [1]
  | .pow w k v => evalW2 w ^ (k + evalVar n a b c d v)

theorem evalTok_bitToTok (n a b c d : Nat) : ∀ (x : Fin 2), evalTok n a b c d (bitToTok x) = [x]
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl

def evalHalf (n a b c d : Nat) : List SymTok → ListBlank (Fin 2)
  | [] => default
  | t :: ts => evalTok n a b c d t +> evalHalf n a b c d ts

theorem evalHalf_map_bit (bs : List (Fin 2)) (rest : List SymTok) (n a b c d : Nat) :
    evalHalf n a b c d (bs.map bitToTok ++ rest) = bs +> evalHalf n a b c d rest := by
  induction bs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons_append, evalHalf, evalTok_bitToTok, ih]
    rfl

theorem evalHalf_map_bit_end (bs : List (Fin 2)) (n a b c d : Nat) :
    evalHalf n a b c d (bs.map bitToTok) = bs +> default := by
  simpa only [List.append_nil, evalHalf] using evalHalf_map_bit bs [] n a b c d

def gToks : List SymTok :=
  [SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0]

theorem gToks_eq : gToks = G.map bitToTok := rfl

def l39Toks : List SymTok :=
  [SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1]

theorem l39Toks_eq : l39Toks = l39Bits.map bitToTok := rfl

def l41Toks : List SymTok :=
  [SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0,
      SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.b1]

theorem l41Toks_eq : l41Toks = l41Bits.map bitToTok := rfl

structure SymState where
  q : Q6
  dir : Dir
  l : List SymTok
  r : List SymTok
  prog : Bool
  deriving DecidableEq

def evalState (n a b c d : Nat) (s : SymState) : Cfg (Fin 2) (Fin 6) :=
  cfg_of (evalQ s.q) s.dir (evalHalf n a b c d s.l) (evalHalf n a b c d s.r)

def pushBit : Bool → List SymTok → List SymTok
  | false, [] => []
  | false, xs => .b0 :: xs
  | true, xs => .b1 :: xs

theorem pushBit_sound (n a b c d : Nat) (x : Bool) (xs : List SymTok) :
    evalHalf n a b c d (pushBit x xs) = ([evalBit x] : List (Fin 2)) +> evalHalf n a b c d xs := by
  cases x <;> cases xs
  · exact zero_cons_default.symm
  · rfl
  · rfl
  · rfl

def pushPowAux (w : W2) (k : Nat) (v : Var) : List SymTok → List SymTok
  | [] => [.pow w k v]
  | .pow w2 k2 v2 :: ys =>
    match w2Eq w w2 with
    | true =>
      match canMergeVars v v2 with
      | some vm => pushPowAux w (k + k2) vm ys
      | none => .pow w k v :: .pow w2 k2 v2 :: ys
    | false =>
      .pow w k v :: .pow w2 k2 v2 :: ys
  | .b0 :: ys =>
    match w with
    | .w01 => .b0 :: pushPowAux .w10 k v ys
    | .w10 => .pow .w10 k v :: .b0 :: ys
    | .w11 => .pow .w11 k v :: .b0 :: ys
  | .b1 :: ys =>
    match w with
    | .w11 => .b1 :: pushPowAux .w11 k v ys
    | .w10 => .b1 :: pushPowAux .w01 k v ys
    | .w01 => .pow .w01 k v :: .b1 :: ys

theorem pushPowAux_sound (n a b c d : Nat) (w : W2) (k : Nat) (v : Var) (xs : List SymTok) :
    evalHalf n a b c d (pushPowAux w k v xs) =
      evalTok n a b c d (.pow w k v) +> evalHalf n a b c d xs := by
  induction xs generalizing w k v with
  | nil => rfl
  | cons y ys ih =>
    rcases y with _ | _ | ⟨w2, k2, v2⟩
    · cases w <;> dsimp [pushPowAux]
      · simp only [evalHalf, evalTok, evalW2, ih .w10 k v]
        exact (rot_w01 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
      · rfl
      · rfl
    · cases w <;> dsimp [pushPowAux]
      · rfl
      · simp only [evalHalf, evalTok, evalW2, ih .w01 k v]
        exact (rot_w10 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
      · simp only [evalHalf, evalTok, evalW2, ih .w11 k v]
        exact (rot_w11 (k + evalVar n a b c d v) (evalHalf n a b c d ys)).symm
    · dsimp [pushPowAux]
      cases hw : w2Eq w w2 with
      | false => rfl
      | true =>
        have hw_eq := w2Eq_sound hw
        subst hw_eq
        cases hm : canMergeVars v v2 with
        | none => rfl
        | some vm =>
          dsimp only
          rw [ih w (k + k2) vm]
          have hvm := canMergeVars_sound n a b c d hm
          have hexp :
              (k + evalVar n a b c d v) + (k2 + evalVar n a b c d v2) =
                (k + k2) + evalVar n a b c d vm := by omega
          simp only [evalHalf, evalTok, ← listblank_append_assoc, ← list_pow_add, hexp]

def pushPow (w : W2) (k : Nat) (v : Var) (xs : List SymTok) : List SymTok :=
  match k, v with
  | 0, .v0 => xs
  | _, _ => pushPowAux w k v xs

theorem pushPow_sound (n a b c d : Nat) (w : W2) (k : Nat) (v : Var) (xs : List SymTok) :
    evalHalf n a b c d (pushPow w k v xs) =
      evalTok n a b c d (.pow w k v) +> evalHalf n a b c d xs := by
  rcases k with _ | k' <;> cases v <;> try exact pushPowAux_sound n a b c d w _ _ xs
  rfl

def unrollPow1 (w : W2) (k : Nat) (v : Var) (tail : List SymTok) : Option (List SymTok) :=
  match k with
  | 0 => none
  | k' + 1 =>
    match w with
    | .w01 => some (.b0 :: .b1 :: pushPow .w01 k' v tail)
    | .w10 => some (.b1 :: .b0 :: pushPow .w10 k' v tail)
    | .w11 => some (.b1 :: .b1 :: pushPow .w11 k' v tail)

theorem unrollPow1_sound (n a b c d : Nat) {w : W2} {k : Nat} {v : Var}
    {tail ys : List SymTok} (h : unrollPow1 w k v tail = some ys) :
    evalHalf n a b c d (.pow w k v :: tail) = evalHalf n a b c d ys := by
  rcases k with _ | k'
  · nomatch h
  · cases w <;> dsimp [unrollPow1] at h <;> injection h with h <;> subst h <;>
      simp only [evalHalf, evalTok, evalW2, pushPow_sound, Nat.succ_add] <;>
      exact right_pow_succ _ (k' + evalVar n a b c d v) (evalHalf n a b c d tail)

def rotateHead : List SymTok → Option (List SymTok)
  | .pow w1 k1 v1 :: .pow w2 k2 v2 :: ys =>
    match w2Eq w1 w2 with
    | true =>
      match canMergeVars v1 v2 with
      | some vm => some (.pow w1 (k1 + k2) vm :: ys)
      | none => unrollPow1 w1 k1 v1 (.pow w2 k2 v2 :: ys)
    | false =>
      unrollPow1 w1 k1 v1 (.pow w2 k2 v2 :: ys)
  | .pow w k v :: .b0 :: ys =>
    match w with
    | .w01 => some (.b0 :: pushPow .w10 k v ys)
    | .w10 => unrollPow1 .w10 k v (.b0 :: ys)
    | .w11 => unrollPow1 .w11 k v (.b0 :: ys)
  | .pow w k v :: .b1 :: ys =>
    match w with
    | .w11 => some (.b1 :: pushPow .w11 k v ys)
    | .w10 => some (.b1 :: pushPow .w01 k v ys)
    | .w01 => unrollPow1 .w01 k v (.b1 :: ys)
  | .pow w k v :: [] => unrollPow1 w k v []
  | _ => none

theorem rotateHead_sound (n a b c d : Nat) {xs ys : List SymTok}
    (h : rotateHead xs = some ys) :
    evalHalf n a b c d xs = evalHalf n a b c d ys := by
  rcases xs with _ | ⟨_ | _ | ⟨w1, k1, v1⟩, tail⟩
  · nomatch h
  · nomatch h
  · nomatch h
  · rcases tail with _ | ⟨_ | _ | ⟨w2, k2, v2⟩, rest⟩
    · exact unrollPow1_sound n a b c d h
    · cases w1
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w01 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
      · exact unrollPow1_sound n a b c d h
      · exact unrollPow1_sound n a b c d h
    · cases w1
      · exact unrollPow1_sound n a b c d h
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w10 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
      · dsimp [rotateHead] at h
        injection h with h'; subst h'
        simp only [evalHalf, evalTok, evalW2, pushPow_sound]
        exact rot_w11 (k1 + evalVar n a b c d v1) (evalHalf n a b c d rest)
    · dsimp [rotateHead] at h
      cases hw : w2Eq w1 w2 with
      | false =>
        rw [hw] at h
        exact unrollPow1_sound n a b c d h
      | true =>
        rw [hw] at h
        have hw_eq := w2Eq_sound hw
        subst hw_eq
        cases hm : canMergeVars v1 v2 with
        | none =>
          rw [hm] at h
          exact unrollPow1_sound n a b c d h
        | some vm =>
          rw [hm] at h
          injection h with h'; subst h'
          have hvm := canMergeVars_sound n a b c d hm
          have hexp :
              (k1 + evalVar n a b c d v1) + (k2 + evalVar n a b c d v2) =
                (k1 + k2) + evalVar n a b c d vm := by omega
          simp only [evalHalf, evalTok, ← listblank_append_assoc, ← list_pow_add, hexp]

def popBitOpt : List SymTok → Option (Bool × List SymTok)
  | [] => some (false, [])
  | .b0 :: xs => some (false, xs)
  | .b1 :: xs => some (true, xs)
  | .pow w (k' + 1) .v0 :: xs =>
    match w with
    | .w01 => some (false, pushBit true (pushPow .w01 k' .v0 xs))
    | .w10 => some (true, pushBit false (pushPow .w10 k' .v0 xs))
    | .w11 => some (true, pushBit true (pushPow .w11 k' .v0 xs))
  | .pow _ _ _ :: _ => none

theorem popBitOpt_sound (n a b c d : Nat) {xs : List SymTok} {cur : Bool} {rest : List SymTok}
    (h : popBitOpt xs = some (cur, rest)) :
    evalHalf n a b c d xs = ([evalBit cur] : List (Fin 2)) +> evalHalf n a b c d rest := by
  rcases xs with _ | ⟨_ | _ | ⟨w, _ | k', v⟩, tail⟩
  · dsimp [popBitOpt] at h
    injection h with h
    rcases h with ⟨rfl, rfl⟩
    exact zero_cons_default.symm
  · dsimp [popBitOpt] at h
    injection h with h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · dsimp [popBitOpt] at h
    injection h with h
    rcases h with ⟨rfl, rfl⟩
    rfl
  · nomatch h
  · cases v
    · cases w <;> dsimp [popBitOpt] at h <;> injection h with h <;> rcases h with ⟨rfl, rfl⟩ <;>
        simp only [evalHalf, evalTok, evalVar, evalW2, evalBit,
          pushBit_sound, pushPow_sound, Nat.add_zero] <;>
        exact right_pow_succ _ k' (evalHalf n a b c d tail)
    · nomatch h
    · nomatch h
    · nomatch h
    · nomatch h
    · nomatch h
    · nomatch h

def popOne1 : List SymTok → Option (List SymTok)
  | .b1 :: rest => some rest
  | .pow .w11 (k' + 1) v :: rest => some (.b1 :: pushPow .w11 k' v rest)
  | _ => none

theorem popOne1_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : popOne1 xs = some rem) :
    evalHalf n a b c d xs = [1] +> evalHalf n a b c d rem := by
  rcases xs with _ | ⟨_ | _ | ⟨w, _ | k', v⟩, rest⟩
  · nomatch h
  · nomatch h
  · injection h with h'; subst h'; rfl
  · cases w <;> nomatch h
  · cases w
    · nomatch h
    · simp only [popOne1] at h; nomatch h
    · dsimp [popOne1] at h
      injection h with h
      subst h
      simp only [evalHalf, evalTok, evalW2, pushPow_sound, Nat.succ_add]
      exact right_pow_succ [1, 1] (k' + evalVar n a b c d v) (evalHalf n a b c d rest)

def stripPrefix : List SymTok → List SymTok → Option (List SymTok)
  | [], xs => some xs
  | p :: ps, x :: xs =>
    match tokEq p x with
    | true => stripPrefix ps xs
    | false => none
  | _ :: _, [] => none

theorem stripPrefix_eq {pre xs rem : List SymTok}
    (h : stripPrefix pre xs = some rem) : xs = pre ++ rem := by
  induction pre generalizing xs with
  | nil => simpa [stripPrefix] using h
  | cons p ps ih =>
    rcases xs with _ | ⟨x, rest⟩
    · nomatch h
    · dsimp [stripPrefix] at h
      cases heq : tokEq p x with
      | false => rw [heq] at h; nomatch h
      | true =>
        rw [heq] at h
        rw [tokEq_sound heq, ih h]
        rfl

def matchZero1 : List SymTok → Option (List SymTok)
  | [] => some []
  | .b0 :: xs => some xs
  | _ => none

theorem matchZero1_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZero1 xs = some rem) :
    evalHalf n a b c d xs = [0] +> evalHalf n a b c d rem := by
  rcases xs with _ | ⟨_ | _ | ⟨w, k, v⟩, rest⟩
  · injection h with h'; subst h'
    exact zero_list_default.symm
  · injection h with h'; subst h'
    rfl
  · nomatch h
  · nomatch h

def matchZeros2 (xs : List SymTok) : Option (List SymTok) :=
  (matchZero1 xs).bind matchZero1

theorem matchZeros2_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZeros2 xs = some rem) :
    evalHalf n a b c d xs = [0, 0] +> evalHalf n a b c d rem := by
  unfold matchZeros2 at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨m1, h1, h2⟩
  rw [matchZero1_sound n a b c d h1, matchZero1_sound n a b c d h2]
  rfl

def matchZeros3 (xs : List SymTok) : Option (List SymTok) :=
  (matchZeros2 xs).bind matchZero1

theorem matchZeros3_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchZeros3 xs = some rem) :
    evalHalf n a b c d xs = [0, 0, 0] +> evalHalf n a b c d rem := by
  unfold matchZeros3 at h
  rw [Option.bind_eq_some_iff] at h
  rcases h with ⟨m2, h1, h2⟩
  rw [matchZeros2_sound n a b c d h1, matchZero1_sound n a b c d h2]
  rfl

def ReachRel (prog : Bool) (c1 c2 : Cfg (Fin 2) (Fin 6)) : Prop :=
  if prog then c1 [tm1]⊢⁺ c2 else c1 [tm1]⊢* c2

theorem ReachRel_eq {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 = c3) : ReachRel prog c1 c3 :=
  h2 ▸ h1

theorem ReachRel_star {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢* c3) : ReachRel prog c1 c3 := by
  cases prog
  · exact stepStar_trans h1 h2
  · exact stepPlus_stepStar_trans h1 h2

theorem ReachRel_plus {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢⁺ c3) : ReachRel true c1 c3 := by
  cases prog
  · exact stepStar_stepPlus_trans h1 h2
  · exact stepPlus_trans h1 h2

theorem ReachRel_step {prog : Bool} {c1 c2 c3 : Cfg (Fin 2) (Fin 6)}
    (h1 : ReachRel prog c1 c2) (h2 : c2 [tm1]⊢ c3) : ReachRel true c1 c3 :=
  ReachRel_plus h1 (step_stepPlus tm1 c2 c3 h2)

def fallbackRightRot (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match rotateHead r with
  | some r' => some ⟨q, .right, l, r', prog⟩
  | none => none

theorem fallbackRightRot_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok} {prog : Bool}
    {s' : SymState} (h : fallbackRightRot q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold fallbackRightRot at h
  cases hr : rotateHead r with
  | none => rw [hr] at h; cases h
  | some r' =>
    rw [hr] at h; injection h with h; subst h
    refine ReachRel_eq h0 ?_
    simp only [evalState]
    rw [rotateHead_sound n a b c d hr]

def fallbackLeftRot (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match rotateHead l with
  | some l' => some ⟨q, .left, l', r, prog⟩
  | none => none

theorem fallbackLeftRot_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok} {prog : Bool}
    {s' : SymState} (h : fallbackLeftRot q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold fallbackLeftRot at h
  cases hl : rotateHead l with
  | none => rw [hl] at h; cases h
  | some l' =>
    rw [hl] at h; injection h with h; subst h
    refine ReachRel_eq h0 ?_
    simp only [evalState]
    rw [rotateHead_sound n a b c d hl]

def tryRightShift (q : Q6) (w : W2) (k : Nat) (v : Var) (l r_rest : List SymTok) (prog : Bool) :
    Option SymState :=
  match q, w with
  | .q2, .w11 => some ⟨.q2, .right, pushPow .w01 k v l, r_rest, prog⟩
  | .q4, .w11 => some ⟨.q4, .right, pushPow .w10 k v l, r_rest, prog⟩
  | _, _ => fallbackRightRot q l (.pow w k v :: r_rest) prog

theorem tryRightShift_sound (n a b c d : Nat) {q : Q6} {w : W2} {k : Nat} {v : Var}
    {l r_rest : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryRightShift q w k v l r_rest prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, .pow w k v :: r_rest, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases w <;> try exact fallbackRightRot_sound n a b c d h h0
  · injection h with h'; subst h'
    refine ReachRel_star h0 ?_
    simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, pushPow_sound]
    exact shiftR_2_11 (k + evalVar n a b c d v) (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
  · injection h with h'; subst h'
    refine ReachRel_star h0 ?_
    simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, pushPow_sound]
    exact shiftR_4_11 (k + evalVar n a b c d v) (evalHalf n a b c d l) (evalHalf n a b c d r_rest)

def tryLeftShift01 (k : Nat) (v : Var) (l_rest r : List SymTok) (prog : Bool) :
    Option SymState :=
  match matchZeros3 r with
  | some rem_r =>
    match tokListEq l_rest l39Toks with
    | true =>
      some ⟨.q5, .left, [], List.append gToks (pushPow .w11 k v rem_r), prog⟩
    | false =>
      some ⟨.q5, .left, l_rest,
          pushBit false (pushBit false (pushBit false (pushPow .w11 k v rem_r))), prog⟩
  | none => fallbackLeftRot .q5 (.pow .w01 k v :: l_rest) r prog

theorem tryLeftShift01_sound (n a b c d : Nat) {k : Nat} {v : Var}
    {l_rest r : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryLeftShift01 k v l_rest r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨.q5, .left, .pow .w01 k v :: l_rest, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold tryLeftShift01 at h
  cases hm : matchZeros3 r with
  | none =>
    simp only [hm] at h
    exact fallbackLeftRot_sound n a b c d h h0
  | some rem_r =>
    simp only [hm] at h
    have hr := matchZeros3_sound n a b c d hm
    cases hl39 : tokListEq l_rest l39Toks with
    | true =>
      rw [hl39] at h
      have hl_eq := tokListEq_sound hl39
      subst hl_eq
      injection h with h'; subst h'
      have hsh := shiftL_5_01 (k + evalVar n a b c d v)
        (evalHalf n a b c d l39Toks) (evalHalf n a b c d rem_r)
      have hl_eval : evalHalf n a b c d l39Toks = l39Bits +> default := by
        rw [l39Toks_eq]
        exact evalHalf_map_bit_end l39Bits n a b c d
      have hg_eval :
          evalHalf n a b c d (List.append gToks (pushPow .w11 k v rem_r)) =
            G +> (([1, 1] : List (Fin 2)) ^ (k + evalVar n a b c d v) +>
              evalHalf n a b c d rem_r) := by
        change evalHalf n a b c d (gToks ++ pushPow .w11 k v rem_r) = _
        rw [gToks_eq, evalHalf_map_bit, pushPow_sound, evalTok, evalW2]
      have hed := edge_in (([1, 1] : List (Fin 2)) ^ (k + evalVar n a b c d v) +>
        evalHalf n a b c d rem_r)
      rw [hl_eval] at hsh
      refine ReachRel_star h0 ?_
      simp only [evalState, evalQ, cfg_of, evalHalf, evalTok, evalW2, hr, hl_eval, hg_eval]
      exact stepStar_trans hsh hed
    | false =>
      rw [hl39] at h
      injection h with h'; subst h'
      have hsh := shiftL_5_01 (k + evalVar n a b c d v)
        (evalHalf n a b c d l_rest) (evalHalf n a b c d rem_r)
      refine ReachRel_star h0 ?_
      simpa only [evalState, evalQ, evalBit, cfg_of, evalHalf, evalTok, evalW2, hr,
        pushBit_sound, pushPow_sound, listblank_append_cons, listblank_append_nil] using hsh

def tryLeftShift (q : Q6) (w : W2) (k : Nat) (v : Var) (l_rest r : List SymTok) (prog : Bool) :
    Option SymState :=
  match q, w with
  | .q5, .w10 =>
    match matchZeros2 r with
    | some rem_r =>
      some ⟨.q5, .left, l_rest, pushBit false (pushBit false (pushPow .w11 k v rem_r)), prog⟩
    | none => fallbackLeftRot q (.pow w k v :: l_rest) r prog
  | .q5, .w01 =>
    tryLeftShift01 k v l_rest r prog
  | _, _ =>
    fallbackLeftRot q (.pow w k v :: l_rest) r prog

theorem tryLeftShift_sound (n a b c d : Nat) {q : Q6} {w : W2} {k : Nat} {v : Var}
    {l_rest r : List SymTok} {prog : Bool} {s' : SymState}
    (h : tryLeftShift q w k v l_rest r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, .pow w k v :: l_rest, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases w <;> try exact fallbackLeftRot_sound n a b c d h h0
  · exact tryLeftShift01_sound n a b c d h h0
  · dsimp [tryLeftShift] at h
    cases hm : matchZeros2 r with
    | none =>
      simp only [hm] at h
      exact fallbackLeftRot_sound n a b c d h h0
    | some rem_r =>
      simp only [hm] at h
      injection h with h'; subst h'
      have hr := matchZeros2_sound n a b c d hm
      have hsh := shiftL_5_10 (k + evalVar n a b c d v)
        (evalHalf n a b c d l_rest) (evalHalf n a b c d rem_r)
      refine ReachRel_star h0 ?_
      simpa only [evalState, evalQ, evalBit, cfg_of, evalHalf, evalTok, evalW2, hr,
        pushBit_sound, pushPow_sound, listblank_append_cons, listblank_append_nil] using hsh

def canCreatePow (usePow : Bool) (l : List SymTok) : Bool :=
  match usePow, l with
  | true, .b0 :: .pow _ _ _ :: _ => false
  | true, _ => true
  | false, _ => false

def matchTwoOnes : List SymTok → Option (List SymTok)
  | .b1 :: .b1 :: rest => some rest
  | _ => none

theorem matchTwoOnes_sound (n a b c d : Nat) {xs rem : List SymTok}
    (h : matchTwoOnes xs = some rem) :
    evalHalf n a b c d xs = [1] +> ([1] +> evalHalf n a b c d rem) := by
  rcases xs with _ | ⟨t1, rest1⟩
  · nomatch h
  · rcases t1 with _ | _ | _
    · nomatch h
    · rcases rest1 with _ | ⟨t2, rest⟩
      · nomatch h
      · rcases t2 with _ | _ | _
        · nomatch h
        · injection h with h'; subst h'; rfl
        · nomatch h
    · nomatch h

def stepConcreteRightPop (q : Q6) (l r : List SymTok) : Option SymState :=
  match popBitOpt r with
  | none => none
  | some (cur, r_rest) =>
    match stepQ q cur with
    | some (q', w_bit, .right) =>
      some ⟨q', .right, pushBit w_bit l, r_rest, true⟩
    | some (q', w_bit, .left) =>
      some ⟨q', .left, l, pushBit w_bit r_rest, true⟩
    | none => none

theorem stepConcreteRightPop_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteRightPop q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteRightPop at h
  cases hp : popBitOpt r with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨cur, r_rest⟩
    simp only [hp] at h
    have hr := popBitOpt_sound n a b c d hp
    cases hsq : stepQ q cur with
    | none => rw [hsq] at h; cases h
    | some val =>
      rcases val with ⟨q', w_bit, d'⟩
      have htm := stepQ_sound hsq
      cases d' with
      | left =>
        rw [hsq] at h; injection h with h; subst h
        have hsl : step_local tm1 ⟨[], [evalBit cur], evalQ q, .right⟩ =
            some ⟨[], [evalBit w_bit], evalQ q', .left⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hr, ← pushBit_sound n a b c d w_bit r_rest] at hst
        exact ReachRel_step h0 hst
      | right =>
        rw [hsq] at h; injection h with h; subst h
        have hsl : step_local tm1 ⟨[], [evalBit cur], evalQ q, .right⟩ =
            some ⟨[evalBit w_bit], [], evalQ q', .right⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hr, ← pushBit_sound n a b c d w_bit l] at hst
        exact ReachRel_step h0 hst

def stepConcreteRight (usePow : Bool) (q : Q6) (l r : List SymTok) : Option SymState :=
  match matchTwoOnes r with
  | some r_rest =>
    match canCreatePow usePow l, q with
    | true, .q2 => some ⟨.q2, .right, pushPow .w01 1 .v0 l, r_rest, true⟩
    | true, .q4 => some ⟨.q4, .right, pushPow .w10 1 .v0 l, r_rest, true⟩
    | _, _ => stepConcreteRightPop q l r
  | none => stepConcreteRightPop q l r

theorem stepConcreteRight_sound (n a b c d : Nat) {usePow : Bool} {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteRight usePow q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .right, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteRight at h
  cases hm : matchTwoOnes r with
  | none =>
    simp only [hm] at h
    exact stepConcreteRightPop_sound n a b c d h h0
  | some r_rest =>
    simp only [hm] at h
    have hr := matchTwoOnes_sound n a b c d hm
    cases hcan : canCreatePow usePow l with
    | false =>
      rw [hcan] at h
      exact stepConcreteRightPop_sound n a b c d h h0
    | true =>
      rw [hcan] at h
      cases q <;> try exact stepConcreteRightPop_sound n a b c d h h0
      · injection h with h'; subst h'
        refine ReachRel_plus h0 ?_
        simp only [evalState, evalQ, cfg_of, evalTok, evalVar, evalW2, hr, pushPow_sound]
        exact shiftR_2_11_plus (evalHalf n a b c d l) (evalHalf n a b c d r_rest)
      · injection h with h'; subst h'
        refine ReachRel_plus h0 ?_
        simp only [evalState, evalQ, cfg_of, evalTok, evalVar, evalW2, hr, pushPow_sound]
        exact shiftR_4_11_plus (evalHalf n a b c d l) (evalHalf n a b c d r_rest)

def stepConcreteLeftPop (q : Q6) (l r : List SymTok) : Option SymState :=
  match popBitOpt l with
  | none => none
  | some (cur, l_rest) =>
    match stepQ q cur with
    | some (q', w_bit, .right) =>
      some ⟨q', .right, pushBit w_bit l_rest, r, true⟩
    | some (q', w_bit, .left) =>
      some ⟨q', .left, l_rest, pushBit w_bit r, true⟩
    | none => none

theorem stepConcreteLeftPop_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteLeftPop q l r = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  unfold stepConcreteLeftPop at h
  cases hp : popBitOpt l with
  | none => simp [hp] at h
  | some pair =>
    rcases pair with ⟨cur, l_rest⟩
    simp only [hp] at h
    have hl := popBitOpt_sound n a b c d hp
    cases hsq : stepQ q cur with
    | none => rw [hsq] at h; cases h
    | some val =>
      rcases val with ⟨q', w_bit, d'⟩
      have htm := stepQ_sound hsq
      cases d' with
      | left =>
        rw [hsq] at h; injection h with h; subst h
        have hsl : step_local tm1 ⟨[evalBit cur], [], evalQ q, .left⟩ =
            some ⟨[], [evalBit w_bit], evalQ q', .left⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l_rest) (evalHalf n a b c d r)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hl, ← pushBit_sound n a b c d w_bit r] at hst
        exact ReachRel_step h0 hst
      | right =>
        rw [hsq] at h; injection h with h; subst h
        have hsl : step_local tm1 ⟨[evalBit cur], [], evalQ q, .left⟩ =
            some ⟨[evalBit w_bit], [], evalQ q', .right⟩ := by
          simp [step_local, htm]
        have hst := step_local_spec hsl (evalHalf n a b c d l_rest) (evalHalf n a b c d r)
        simp only [cfg_of, listblank_append_nil] at hst
        rw [← hl, ← pushBit_sound n a b c d w_bit l_rest] at hst
        exact ReachRel_step h0 hst

def stepConcreteLeft (q : Q6) (l r : List SymTok) (prog : Bool) : Option SymState :=
  match q, l with
  | .q5, [] =>
    match stripPrefix gToks r with
    | some r_after_g =>
      match popOne1 r_after_g with
      | some rem_r => some ⟨.q2, .right, l41Toks, pushPow .w11 2 .v0 rem_r, prog⟩
      | none => stepConcreteLeftPop .q5 [] r
    | none => stepConcreteLeftPop .q5 [] r
  | q, l => stepConcreteLeftPop q l r

theorem stepConcreteLeft_sound (n a b c d : Nat) {q : Q6} {l r : List SymTok}
    {prog : Bool} {s' : SymState}
    (h : stepConcreteLeft q l r prog = some s')
    {c0 : Cfg (Fin 2) (Fin 6)}
    (h0 : ReachRel prog c0 (evalState n a b c d ⟨q, .left, l, r, prog⟩)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  cases q <;> cases l <;> dsimp [stepConcreteLeft] at h <;>
    try exact stepConcreteLeftPop_sound n a b c d h h0
  cases hs : stripPrefix gToks r with
  | none =>
    simp only [hs] at h
    exact stepConcreteLeftPop_sound n a b c d h h0
  | some r_after_g =>
    simp only [hs] at h
    cases hp1 : popOne1 r_after_g with
    | none =>
      simp only [hp1] at h
      exact stepConcreteLeftPop_sound n a b c d h h0
    | some rem_r =>
      simp only [hp1] at h
      injection h with h'; subst h'
      have hr_eq := stripPrefix_eq hs
      have hp1_eq := popOne1_sound n a b c d hp1
      have hr_eval : evalHalf n a b c d r = G +> ([1] +> evalHalf n a b c d rem_r) := by
        rw [hr_eq, gToks_eq, evalHalf_map_bit, hp1_eq]
      have hl41_eval : evalHalf n a b c d l41Toks = l41Bits +> default := by
        rw [l41Toks_eq]
        exact evalHalf_map_bit_end l41Bits n a b c d
      have hr_out :
          evalHalf n a b c d (pushPow .w11 2 .v0 rem_r) =
            [1, 1, 1, 1] +> evalHalf n a b c d rem_r := by
        rw [pushPow_sound]
        rfl
      refine ReachRel_star h0 ?_
      simp only [evalState, evalQ, cfg_of, evalHalf, hr_eval, hl41_eval, hr_out]
      exact edge_out (evalHalf n a b c d rem_r)

def symStep (usePow : Bool) (s : SymState) : Option SymState :=
  match s.dir with
  | .right =>
    match s.r with
    | .pow w k v :: r_rest => tryRightShift s.q w k v s.l r_rest s.prog
    | _ => stepConcreteRight usePow s.q s.l s.r
  | .left =>
    match s.l with
    | .pow w k v :: l_rest => tryLeftShift s.q w k v l_rest s.r s.prog
    | _ => stepConcreteLeft s.q s.l s.r s.prog

theorem symStep_sound (n a b c d : Nat) {usePow : Bool} {s s' : SymState}
    (h : symStep usePow s = some s')
    {c0 : Cfg (Fin 2) (Fin 6)} (h0 : ReachRel s.prog c0 (evalState n a b c d s)) :
    ReachRel s'.prog c0 (evalState n a b c d s') := by
  rcases s with ⟨q, dir, l, r, prog⟩
  cases dir with
  | left =>
    rcases l with _ | ⟨_ | _ | ⟨w, k, v⟩, l_rest⟩ <;> dsimp [symStep] at h
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact stepConcreteLeft_sound n a b c d h h0
    · exact tryLeftShift_sound n a b c d h h0
  | right =>
    rcases r with _ | ⟨_ | _ | ⟨w, k, v⟩, r_rest⟩ <;> dsimp [symStep] at h
    · exact stepConcreteRight_sound n a b c d h h0
    · exact stepConcreteRight_sound n a b c d h h0
    · exact stepConcreteRight_sound n a b c d h h0
    · exact tryRightShift_sound n a b c d h h0

def runSym (usePow : Bool) : Nat → SymState → Option SymState
  | 0, s => some s
  | k + 1, s =>
    match symStep usePow s with
    | some s' => runSym usePow k s'
    | none => none

theorem runSym_sound (n a b c d : Nat) {usePow : Bool} :
    ∀ (k : Nat) {s s' : SymState},
      runSym usePow k s = some s' →
      ∀ {c0 : Cfg (Fin 2) (Fin 6)},
        ReachRel s.prog c0 (evalState n a b c d s) →
        ReachRel s'.prog c0 (evalState n a b c d s')
  | 0, s, s', h, _, h0 => by
    injection h with h'; subst h'; exact h0
  | k + 1, s, s', h, _, h0 => by
    unfold runSym at h
    cases hs : symStep usePow s with
    | none => simp [hs] at h
    | some sm =>
      simp only [hs] at h
      exact runSym_sound n a b c d k h (symStep_sound n a b c d hs h0)

def insertCanon (t : SymTok) (xs : List SymTok) : List SymTok :=
  match t with
  | .b0 => pushBit false xs
  | .b1 =>
    match xs with
    | .b1 :: rest => pushPow .w11 1 .v0 rest
    | _ => pushBit true xs
  | .pow w k v => pushPow w k v xs

theorem evalHalf_insertCanon (n a b c d : Nat) (t : SymTok) (xs : List SymTok) :
    evalHalf n a b c d (insertCanon t xs) =
      evalTok n a b c d t +> evalHalf n a b c d xs := by
  rcases t with _ | _ | ⟨w, k, v⟩
  · exact pushBit_sound n a b c d false xs
  · rcases xs with _ | ⟨_ | _ | ⟨w2, k2, v2⟩, rest⟩
    · exact pushBit_sound n a b c d true []
    · exact pushBit_sound n a b c d true (.b0 :: rest)
    · dsimp [insertCanon]
      rw [pushPow_sound]
      rfl
    · exact pushBit_sound n a b c d true (.pow w2 k2 v2 :: rest)
  · exact pushPow_sound n a b c d w k v xs

def canonHalf : List SymTok → List SymTok
  | [] => []
  | x :: xs => insertCanon x (canonHalf xs)

theorem evalHalf_canonHalf (n a b c d : Nat) (xs : List SymTok) :
    evalHalf n a b c d (canonHalf xs) = evalHalf n a b c d xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [canonHalf, evalHalf_insertCanon, ih, evalHalf]

def checkMid (usePow : Bool) (fuel : Nat) (s1 s2 : SymState) : Bool :=
  match runSym usePow fuel { s1 with prog := false } with
  | some s' =>
    s'.prog &&
    q6Eq s'.q s2.q &&
    dirEq s'.dir s2.dir &&
    tokListEq s'.l s2.l &&
    tokListEq s'.r s2.r
  | none => false

theorem checkMid_sound (n a b c d : Nat) {usePow : Bool} {fuel : Nat} {s1 s2 : SymState}
    (h : checkMid usePow fuel s1 s2 = true) :
    (evalState n a b c d s1) [tm1]⊢* (evalState n a b c d s2) := by
  unfold checkMid at h
  cases hr : runSym usePow fuel { s1 with prog := false } with
  | none => rw [hr] at h; cases h
  | some s' =>
    simp only [hr, Bool.and_assoc, Bool.and_eq_true] at h
    rcases h with ⟨hp, hq, hdir, hl, hr_eq⟩
    have h0 : ReachRel false (evalState n a b c d s1)
        (evalState n a b c d { s1 with prog := false }) :=
      stepStar_refl tm1 _
    have hreach := runSym_sound n a b c d fuel hr h0
    rw [hp] at hreach
    have heq : evalState n a b c d s' = evalState n a b c d s2 := by
      simp only [evalState, q6Eq_sound hq, dirEq_sound hdir, tokListEq_sound hl,
          tokListEq_sound hr_eq]
    rw [heq] at hreach
    exact stepPlus_stepStar hreach

def checkSym (usePow : Bool) (fuel : Nat) (s1 s2 : SymState) : Bool :=
  match runSym usePow fuel { s1 with prog := false } with
  | some s' =>
    s'.prog &&
    q6Eq s'.q s2.q &&
    dirEq s'.dir s2.dir &&
    tokListEq (canonHalf s'.l) (canonHalf s2.l) &&
    tokListEq (canonHalf s'.r) (canonHalf s2.r)
  | none => false

theorem checkSym_sound (n a b c d : Nat) {usePow : Bool} {fuel : Nat} {s1 s2 : SymState}
    (h : checkSym usePow fuel s1 s2 = true) :
    (evalState n a b c d s1) [tm1]⊢⁺ (evalState n a b c d s2) := by
  unfold checkSym at h
  cases hr : runSym usePow fuel { s1 with prog := false } with
  | none => rw [hr] at h; cases h
  | some s' =>
    simp only [hr, Bool.and_assoc, Bool.and_eq_true] at h
    rcases h with ⟨hp, hq, hdir, hl_c, hr_c⟩
    have h0 : ReachRel false (evalState n a b c d s1)
        (evalState n a b c d { s1 with prog := false }) :=
      stepStar_refl tm1 _
    have hreach := runSym_sound n a b c d fuel hr h0
    rw [hp] at hreach
    have heq : evalState n a b c d s' = evalState n a b c d s2 := by
      have hl_eq : evalHalf n a b c d s'.l = evalHalf n a b c d s2.l := by
        rw [← evalHalf_canonHalf n a b c d s'.l, tokListEq_sound hl_c, evalHalf_canonHalf]
      have hr_eq : evalHalf n a b c d s'.r = evalHalf n a b c d s2.r := by
        rw [← evalHalf_canonHalf n a b c d s'.r, tokListEq_sound hr_c, evalHalf_canonHalf]
      simp only [evalState, q6Eq_sound hq, dirEq_sound hdir, hl_eq, hr_eq]
    rwa [heq] at hreach

-- ============================================================================
-- 4. Symbolic `Kr` Builders & The Five Macro Transitions (`S_step`, `TE`, `TO`, `T6`, `T8`)
-- ============================================================================

def segVar (pre : List (Fin 2)) (k0 : Nat) (v : Var) : List SymTok :=
  pre.map bitToTok ++ [.pow .w11 k0 v]

def segConst (pre : List (Fin 2)) (k0 : Nat) : List SymTok :=
  segVar pre k0 .v0

theorem evalHalf_segVar (pre : List (Fin 2)) (k0 : Nat) (v : Var) (rest : List SymTok)
    (n a b c d : Nat) :
    evalHalf n a b c d (segVar pre k0 v ++ rest) =
      pre +> (([1, 1] : List (Fin 2)) ^ (k0 + evalVar n a b c d v) +> evalHalf n a b c d rest) := by
  rw [segVar, List.append_assoc, evalHalf_map_bit]
  rfl

theorem evalHalf_segConst (pre : List (Fin 2)) (k0 : Nat) (rest : List SymTok) (n a b c d : Nat) :
    evalHalf n a b c d (segConst pre k0 ++ rest) =
      pre +> (([1, 1] : List (Fin 2)) ^ k0 +> evalHalf n a b c d rest) := by
  rw [segConst, evalHalf_segVar]
  rfl

def krTailToks : List SymTok :=
  [SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.b1]

theorem krTailToks_eq : krTailToks = ([0, 1, 1, 0, 0, 1, 1, 0, 1, 1,
    1] : List (Fin 2)).map bitToTok := rfl

def mkSymKr (r : List SymTok) : SymState :=
  ⟨.q5, .left, [], r, false⟩

def symS_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segVar [0] 5 .va ++
    segVar [0, 1, 1, 0] 3 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 3 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 1 .vd ++
    krTailToks)

def symS_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 24 .vn ++
    segVar [0] 1 .va ++
    segVar [0, 1, 1, 0] 5 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 3 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 3 .vd ++
    krTailToks)

set_option maxRecDepth 200000 in
theorem S_step_cert : checkSym true 2192 symS_lhs symS_rhs = true := by
  decide

theorem S_step (n a b c d : Nat) :
    (Kr n (5 + a) (3 + b) (3 + c) (1 + d)) [tm1]⊢⁺
      (Kr (24 + n) (1 + a) (5 + b) (3 + c) (3 + d)) := by
  have h := checkSym_sound n a b c d S_step_cert
  have h1 : evalState n a b c d symS_lhs = Kr n (5 + a) (3 + b) (3 + c) (1 + d) := by
    simp only [symS_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_map_bit_end, evalHalf, evalVar, Nat.zero_add,
        listblank_append_assoc]
  have h2 : evalState n a b c d symS_rhs = Kr (24 + n) (1 + a) (5 + b) (3 + c) (3 + d) := by
    simp only [symS_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_map_bit_end, evalHalf, evalVar,
        listblank_append_assoc]
  rwa [h1, h2] at h

theorem S_iter (k n a b c d : Nat) :
    (Kr n (4 * k + 1 + a) (3 + b) (3 + c) (1 + d)) [tm1]⊢*
      (Kr (24 * k + n) (1 + a) (2 * k + 3 + b) (3 + c) (2 * k + 1 + d)) := by
  induction k generalizing n b d with
  | zero =>
    have h0 : Kr n (4 * 0 + 1 + a) (3 + b) (3 + c) (1 + d) =
        Kr (24 * 0 + n) (1 + a) (2 * 0 + 3 + b) (3 + c) (2 * 0 + 1 + d) :=
      Kr_congr (by omega) (by omega) (by omega) (by omega) (by omega)
    rw [h0]
    try exact stepStar_refl tm1 _
  | succ k ih =>
    have h_lhs : Kr n (4 * (k + 1) + 1 + a) (3 + b) (3 + c) (1 + d) =
        Kr n (5 + (4 * k + a)) (3 + b) (3 + c) (1 + d) :=
      Kr_congr rfl (by omega) rfl rfl rfl
    have h1 : (Kr n (5 + (4 * k + a)) (3 + b) (3 + c) (1 + d)) [tm1]⊢*
        (Kr (24 + n) (4 * k + 1 + a) (3 + (2 + b)) (3 + c) (1 + (2 + d))) := by
      have hs := stepPlus_stepStar (S_step n (4 * k + a) b c d)
      have h_mid : Kr (24 + n) (1 + (4 * k + a)) (5 + b) (3 + c) (3 + d) =
          Kr (24 + n) (4 * k + 1 + a) (3 + (2 + b)) (3 + c) (1 + (2 + d)) :=
        Kr_congr rfl (by omega) (by omega) rfl (by omega)
      rwa [h_mid] at hs
    have h2 := ih (24 + n) (2 + b) (2 + d)
    have h_rhs :
        Kr (24 * k + (24 + n)) (1 + a) (2 * k + 3 + (2 + b)) (3 + c) (2 * k + 1 + (2 + d)) =
          Kr (24 * (k + 1) + n) (1 + a) (2 * (k + 1) + 3 + b) (3 + c) (2 * (k + 1) + 1 + d) :=
      Kr_congr (by omega) rfl (by omega) rfl (by omega)
    rw [h_lhs]
    rw [h_rhs] at h2
    exact stepStar_trans h1 h2

def symTE_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 2 ++
    segVar [0, 1, 1, 0] 44 .vb ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 10 .vd ++
    krTailToks)

def symTE_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 278 .vn ++
    segVar [0] 1 .vb ++
    segConst [0, 1, 1, 0] 41 ++
    segVar [0, 0, 0, 0, 0, 0, 1] 35 .vd ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def TE_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 91 .vn, SymTok.b0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 30 .vb, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 24 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 29 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 3 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

def TE_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 184 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 16 .vb, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.pow .w11 31 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 37 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def TE_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 269 .vn, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 0 .vb, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 43 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 34 .vd, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 1 .v0])

set_option maxRecDepth 200000 in
theorem TE_cert1 : checkMid true 8440 symTE_lhs TE_mid1 = true := by
  decide

set_option maxRecDepth 200000 in
theorem TE_cert2 : checkMid true 8286 TE_mid1 TE_mid2 = true := by
  decide

set_option maxRecDepth 200000 in
theorem TE_cert3 : checkMid true 8494 TE_mid2 TE_mid3 = true := by
  decide

set_option maxRecDepth 200000 in
theorem TE_cert_end : checkSym true 226 TE_mid3 symTE_rhs = true := by
  decide

theorem TE (n b d : Nat) :
    (Kr n 2 (44 + b) 17 (10 + d)) [tm1]⊢⁺
      (Kr (278 + n) (1 + b) 41 (35 + d) 9) := by
  have h :=
      (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d TE_cert1) (stepStar_stepPlus_trans
      (checkMid_sound n 0 b 0 d TE_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d
      TE_cert3) (checkSym_sound n 0 b 0 d TE_cert_end))))
  have h1 : evalState n 0 b 0 d symTE_lhs = Kr n 2 (44 + b) 17 (10 + d) := by
    simp only [symTE_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, Nat.zero_add, listblank_append_assoc]
  have h2 : evalState n 0 b 0 d symTE_rhs = Kr (278 + n) (1 + b) 41 (35 + d) 9 := by
    simp only [symTE_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, listblank_append_assoc]
  rwa [h1, h2] at h

def symTO_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 1 ++
    segVar [0, 1, 1, 0] 41 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 18 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 .vd ++
    krTailToks)

def symTO_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 294 .vn ++
    segVar [0] 14 .vbc ++
    segVar [0, 1, 1, 0] 40 .vd ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def TO_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 121 .vn, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 43 .vbc, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 26 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0,
      SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def TO_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 212 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 27 .vbc, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 31 .vd, SymTok.b0,
      SymTok.pow .w11 17 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 3 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 5 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

set_option maxRecDepth 200000 in
theorem TO_cert1 : checkMid true 8454 symTO_lhs TO_mid1 = true := by
  decide

set_option maxRecDepth 200000 in
theorem TO_cert2 : checkMid true 8069 TO_mid1 TO_mid2 = true := by
  decide

set_option maxRecDepth 200000 in
theorem TO_cert_end : checkSym true 7854 TO_mid2 symTO_rhs = true := by
  decide

theorem TO (n b c d : Nat) :
    (Kr n 1 (41 + b) (18 + c) (9 + d)) [tm1]⊢⁺
      (Kr (294 + n) (14 + b + c) (40 + d) 17 9) := by
  have h :=
      (stepStar_stepPlus_trans (checkMid_sound n 0 b c d TO_cert1) (stepStar_stepPlus_trans
      (checkMid_sound n 0 b c d TO_cert2) (checkSym_sound n 0 b c d TO_cert_end)))
  have h1 : evalState n 0 b c d symTO_lhs = Kr n 1 (41 + b) (18 + c) (9 + d) := by
    simp only [symTO_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, Nat.zero_add, listblank_append_assoc]
  have h2 : evalState n 0 b c d symTO_rhs = Kr (294 + n) (14 + b + c) (40 + d) 17 9 := by
    rw [show 14 + b + c = 14 + (b + c) from Nat.add_assoc 14 b c]
    simp only [symTO_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, listblank_append_assoc]
  rwa [h1, h2] at h

def symT6_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 3 ++
    segVar [0, 1, 1, 0] 41 .vb ++
    segVar [0, 0, 0, 0, 0, 0, 1] 17 .vc ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 .vd ++
    krTailToks)

def symT6_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 296 .vn ++
    segVar [0] 13 .vbc ++
    segVar [0, 1, 1, 0] 40 .vd ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def T6_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 118 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 42 .vbc, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 23 .vd, SymTok.b0,
      SymTok.pow .w11 10 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 4 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

def T6_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 202 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 28 .vbc, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.pow .w11 30 .vd, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 19 .v0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T6_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 287 .vn, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 12 .vbc, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 42 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 16 .v0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 1 .v0])

set_option maxRecDepth 200000 in
theorem T6_cert1 : checkMid true 7880 symT6_lhs T6_mid1 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T6_cert2 : checkMid true 8036 T6_mid1 T6_mid2 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T6_cert3 : checkMid true 8494 T6_mid2 T6_mid3 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T6_cert_end : checkSym true 226 T6_mid3 symT6_rhs = true := by
  decide

theorem T6 (n b c d : Nat) :
    (Kr n 3 (41 + b) (17 + c) (9 + d)) [tm1]⊢⁺
      (Kr (296 + n) (13 + b + c) (40 + d) 17 9) := by
  have h :=
      (stepStar_stepPlus_trans (checkMid_sound n 0 b c d T6_cert1) (stepStar_stepPlus_trans
      (checkMid_sound n 0 b c d T6_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b c d
      T6_cert3) (checkSym_sound n 0 b c d T6_cert_end))))
  have h1 : evalState n 0 b c d symT6_lhs = Kr n 3 (41 + b) (17 + c) (9 + d) := by
    simp only [symT6_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, Nat.zero_add, listblank_append_assoc]
  have h2 : evalState n 0 b c d symT6_rhs = Kr (296 + n) (13 + b + c) (40 + d) 17 9 := by
    rw [show 13 + b + c = 13 + (b + c) from Nat.add_assoc 13 b c]
    simp only [symT6_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, listblank_append_assoc]
  rwa [h1, h2] at h

def symT8_lhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 0 .vn ++
    segConst [0] 4 ++
    segVar [0, 1, 1, 0] 44 .vb ++
    segConst [0, 0, 0, 0, 0, 0, 1] 17 ++
    segVar [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 10 .vd ++
    krTailToks)

def symT8_rhs : SymState :=
  mkSymKr (
    segVar (G ++ [1]) 270 .vn ++
    segVar [0] 7 .vb ++
    segConst [0, 1, 1, 0] 43 ++
    segVar [0, 0, 0, 0, 0, 0, 1] 33 .vd ++
    segConst [0, 1, 1, 0, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0] 9 ++
    krTailToks)

def T8_mid1 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 92 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 36 .vb, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b1, SymTok.pow .w11 26 .v0, SymTok.b0,
      SymTok.pow .w11 20 .vd, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 10 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1])

def T8_mid2 : SymState :=
  mkSymKr (List.append gToks [SymTok.pow .w11 176 .vn, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.pow .w11 22 .vb, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0,
      SymTok.b1, SymTok.b1, SymTok.pow .w11 33 .v0, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0,
      SymTok.b0, SymTok.b0, SymTok.pow .w11 35 .vd, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.pow .w11 1 .v0, SymTok.b0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.pow .w11 6 .v0, SymTok.b0, SymTok.b1, SymTok.b1])

def T8_mid3 : SymState :=
  mkSymKr (List.append gToks [SymTok.b1, SymTok.b1, SymTok.pow .w11 261 .vn, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.pow .w11 6 .vb, SymTok.b0,
      SymTok.b0, SymTok.pow .w11 45 .v0, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1,
      SymTok.pow .w11 32 .vd, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0,
      SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.pow .w11 2 .v0, SymTok.b0, SymTok.b0,
      SymTok.b0, SymTok.b0, SymTok.b0, SymTok.b0, SymTok.pow .w11 9 .v0, SymTok.b0, SymTok.b1,
      SymTok.b1, SymTok.b0, SymTok.b0, SymTok.b1, SymTok.b1, SymTok.b0, SymTok.b1,
      SymTok.pow .w11 1 .v0])

set_option maxRecDepth 200000 in
theorem T8_cert1 : checkMid true 8149 symT8_lhs T8_mid1 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T8_cert2 : checkMid true 8036 T8_mid1 T8_mid2 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T8_cert3 : checkMid true 8494 T8_mid2 T8_mid3 = true := by
  decide

set_option maxRecDepth 200000 in
theorem T8_cert_end : checkSym true 226 T8_mid3 symT8_rhs = true := by
  decide

theorem T8 (n b d : Nat) :
    (Kr n 4 (44 + b) 17 (10 + d)) [tm1]⊢⁺
      (Kr (270 + n) (7 + b) 43 (33 + d) 9) := by
  have h :=
      (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d T8_cert1) (stepStar_stepPlus_trans
      (checkMid_sound n 0 b 0 d T8_cert2) (stepStar_stepPlus_trans (checkMid_sound n 0 b 0 d
      T8_cert3) (checkSym_sound n 0 b 0 d T8_cert_end))))
  have h1 : evalState n 0 b 0 d symT8_lhs = Kr n 4 (44 + b) 17 (10 + d) := by
    simp only [symT8_lhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, Nat.zero_add, listblank_append_assoc]
  have h2 : evalState n 0 b 0 d symT8_rhs = Kr (270 + n) (7 + b) 43 (33 + d) 9 := by
    simp only [symT8_rhs, mkSymKr, krTailToks_eq, Kr, krRightList, evalState, evalQ, cfg_of,
        List.append_assoc, evalHalf_segVar, evalHalf_segConst, evalHalf_map_bit_end, evalHalf,
        evalVar, listblank_append_assoc]
  rwa [h1, h2] at h

theorem DC (N X : Nat) : (Ev N X) [tm1]⊢⁺ Ev (48 * X + 716 + N) (4 + X) := by
  have h1 : (Ev N X) [tm1]⊢*
      Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11)) := by
    have hs := S_iter (X + 6) N 1 (2 * X + 29) 14 8
    have hl : Kr N (4 * (X + 6) + 1 + 1) (3 + (2 * X + 29)) (3 + 14) (1 + 8) = Ev N X :=
      Kr_congr rfl (by omega) (by omega) rfl rfl
    have hr :
        Kr (24 * (X + 6) + N) (1 + 1) (2 * (X + 6) + 3 + (2 * X + 29)) (3 + 14)
            (2 * (X + 6) + 1 + 8) =
          Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11)) :=
      Kr_congr rfl rfl (by omega) rfl (by omega)
    rwa [hl, hr] at hs
  have h2 : (Kr (24 * (X + 6) + N) 2 (44 + 4 * X) 17 (10 + (2 * X + 11))) [tm1]⊢⁺
      Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8) := by
    have hte := TE (24 * (X + 6) + N) (4 * X) (2 * X + 11)
    have hr :
        Kr (278 + (24 * (X + 6) + N)) (1 + 4 * X) 41 (35 + (2 * X + 11)) 9 =
          Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8) :=
      Kr_congr (by omega) (by omega) rfl (by omega) rfl
    rwa [hr] at hte
  have h3 : (Kr (422 + 24 * X + N) (4 * X + 1 + 0) (3 + 38) (3 + (2 * X + 43)) (1 + 8))
      [tm1]⊢*
        Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X) := by
    have hs := S_iter X (422 + 24 * X + N) 0 38 (2 * X + 43) 8
    have hr :
        Kr (24 * X + (422 + 24 * X + N)) (1 + 0) (2 * X + 3 + 38) (3 + (2 * X + 43))
            (2 * X + 1 + 8) =
          Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X) :=
      Kr_congr (by omega) rfl (by omega) (by omega) (by omega)
    rwa [hr] at hs
  have h4 :
      (Kr (422 + 48 * X + N) 1 (41 + 2 * X) (18 + (2 * X + 28)) (9 + 2 * X)) [tm1]⊢⁺
        Ev (48 * X + 716 + N) (4 + X) := by
    have hto := TO (422 + 48 * X + N) (2 * X) (2 * X + 28) (2 * X)
    have hr :
        Kr (294 + (422 + 48 * X + N)) (14 + 2 * X + (2 * X + 28)) (40 + 2 * X) 17 9 =
          Ev (48 * X + 716 + N) (4 + X) := by
      unfold Ev
      exact Kr_congr (by omega) (by omega) (by omega) rfl rfl
    rwa [hr] at hto
  exact stepPlus_trans (stepStar_stepPlus_trans h1 h2) (stepStar_stepPlus_trans h3 h4)

-- ============================================================================

def Inv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ N X : Nat, cfg = Ev N X



end TM1Donor

end BusyBeaver
