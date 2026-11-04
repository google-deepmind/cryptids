/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

@[expose] public section

open Mathlib Relation Nat Turing BusyBeaver SixState

namespace BusyBeaver.M_1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_HHH1LE

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

def machine : ConjectureMachines.Machine 6 2 :=
  load_rle_machine% "1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_HHH1LE"

abbrev target : Machine (Fin 2) (Fin 6) := machine.toBB

def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 3, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 1 => some (some 0, Stmt.write 1 Dir.right)
  | 2, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 4, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 5, Stmt.write 1 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 5, 0 => none
  | 5, 1 => some (some 4, Stmt.write 1 Dir.left)

theorem target_eq_target_tm : target = target_tm := by
  funext q a
  fin_cases q <;> fin_cases a <;> simp [target, machine, ConjectureMachines.Machine.toBB, ConjectureMachines.Machine.ofRows, target_tm]
abbrev A : Fin 6 := 0
abbrev B : Fin 6 := 1
abbrev C : Fin 6 := 2
abbrev D : Fin 6 := 3
abbrev E : Fin 6 := 4
abbrev F : Fin 6 := 5

local infixr:67 (priority := high) " >> " =>
  (ListBlank.cons : Fin 2 → ListBlank (Fin 2) → ListBlank (Fin 2))

/-- Explicit configuration constructor with head symbol `s`, left stream `l`, and right stream `r`. -/
def mkCfg (q : Fin 6) (s : Fin 2) (l r : ListBlank (Fin 2)) : Cfg (Fin 2) (Fin 6) :=
  ⟨some q, ⟨s, l, r⟩⟩

@[simp] theorem zMs (M : Machine Γ Λ) (config : Cfg Γ Λ) (n : Nat) :
    multiStep M config (n + 1) = Option.bind (multiStep M config n) (step M) := by
  rw [multiStep, Function.iterate_succ', Function.comp_apply, multiStep]

@[simp] theorem zZcd : (0 : Fin 2) >> default = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl
@[simp] theorem zDh : (default : ListBlank (Fin 2)).head = (0 : Fin 2) := rfl
@[simp] theorem zDt : (default : ListBlank (Fin 2)).tail = default := rfl

theorem zMa {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ : Cfg Γ Λ) (n m : Nat) :
    multiStep tm c₁ (n + m) = (multiStep tm c₁ n).bind (fun c₂ => multiStep tm c₂ m) := by
  induction m with
  | zero => simp [multiStep]
  | succ m' ih =>
    rw [Nat.add_succ, zMs, ih, Option.bind_assoc]
    simp_rw [zMs]

theorem zMt {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (tm : Machine Γ Λ) (c₁ c₂ c₃ : Cfg Γ Λ) (n m : Nat)
    (h₁ : c₁ [tm]⊢^{n} c₂) (h₂ : c₂ [tm]⊢^{m} c₃) :
    c₁ [tm]⊢^{n+m} c₃ := by
  rw [zMa, h₁]; simp [h₂]

theorem zPs {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ : Cfg Γ Λ} (h : c₁ [tm]⊢⁺ c₂) :
    c₁ [tm]⊢* c₂ := by obtain ⟨n, _, hn⟩ := h; exact ⟨n, hn⟩

theorem q7 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢⁺ c₂) (h₂ : c₂ [tm]⊢* c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, n_pos, hn⟩ := h₁; obtain ⟨m, hm⟩ := h₂
  exact ⟨n + m, lt_of_lt_of_le n_pos (Nat.le_add_right n m), zMt tm c₁ c₂ c₃ n m hn hm⟩

theorem q8 {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    {tm : Machine Γ Λ} {c₁ c₂ c₃ : Cfg Γ Λ}
    (h₁ : c₁ [tm]⊢* c₂) (h₂ : c₂ [tm]⊢⁺ c₃) : c₁ [tm]⊢⁺ c₃ := by
  obtain ⟨n, hn⟩ := h₁; obtain ⟨m, m_pos, hm⟩ := h₂
  exact ⟨n + m, by omega, zMt tm c₁ c₂ c₃ n m hn hm⟩

/-- General invariant theorem for `IsNotHalt`. -/
theorem isNotHalt_of_invariant {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]
    (M : Machine Γ Λ) (Inv : Cfg Γ Λ → Prop)
    (h_init : ∃ c₀, ((init []) [M]⊢⁺ c₀) ∧ Inv c₀)
    (h_step : ∀ c, Inv c → ∃ c', (c [M]⊢⁺ c') ∧ Inv c') :
    IsNotHalt M := by
  have h_reach : ∀ k, ∃ m ≥ k, ∃ c, multiStep M (init []) m = some c ∧ Inv c := by
    intro k
    induction k with
    | zero =>
      rcases h_init with ⟨c₀, ⟨m, _, hm⟩, hinv⟩
      exact ⟨m, Nat.zero_le m, c₀, hm, hinv⟩
    | succ k ih =>
      rcases ih with ⟨m, hm_ge, c, hm, hinv⟩
      rcases h_step c hinv with ⟨c', ⟨d, hd_pos, hd⟩, hinv'⟩
      refine ⟨m + d, by omega, c', zMt M (init []) c c' m d hm hd, hinv'⟩
  intro cfg ⟨n, hn⟩
  rcases h_reach (n + 1) with ⟨m, hm_ge, c_end, hm, _⟩
  have h_split : m = n + 1 + (m - (n + 1)) := by omega
  rw [h_split, zMa M (init []) (n + 1) (m - (n + 1)), zMs M (init []) n, hn] at hm
  simp only [Option.bind] at hm
  cases h_st : step M cfg with
  | none => simp [h_st] at hm
  | some _ => rfl

/-- Prepend `n` ones onto a `ListBlank (Fin 2)` stream. -/
def rep1 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, s => s
  | n + 1, s => 1 >> rep1 n s

/-- Prepend `m` alternating `0, 1` pairs (`0` nearest head). -/
def rep01 : Nat → ListBlank (Fin 2) → ListBlank (Fin 2)
  | 0, s => s
  | m + 1, s => 0 >> 1 >> rep01 m s

theorem rep1_add (a b : Nat) (s : ListBlank (Fin 2)) :
    rep1 a (rep1 b s) = rep1 (a + b) s := by
  induction a generalizing b s with
  | zero => simp [rep1]
  | succ a ih => simp [rep1, Nat.succ_add, ih]

theorem rep01_snoc (m : Nat) (s : ListBlank (Fin 2)) :
    rep01 m (0 >> 1 >> s) = rep01 (m + 1) s := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => show 0 >> 1 >> rep01 m (0 >> 1 >> s) = 0 >> 1 >> rep01 (m + 1) s; rw [ih s]

/-- Canonical 2-parameter family: `0^∞ 1^a <B 1^(c+1) 0^∞`. -/
def cfgB : Nat → Nat → Cfg (Fin 2) (Fin 6)
  | 0, c => mkCfg B 0 default (rep1 (c + 1) default)
  | k + 1, c => mkCfg B 1 (rep1 k default) (rep1 (c + 1) default)

/-- Intermediate peeling configuration: `mkCfg B 1 (rep01 k (rep1 a default)) (rep1 (r + 1) default)`. -/
def peelState (k a r : Nat) : Cfg (Fin 2) (Fin 6) :=
  mkCfg B 1 (rep01 k (rep1 a default)) (rep1 (r + 1) default)

theorem peelState_zero (a r : Nat) : peelState 0 a r = cfgB (a + 1) r := rfl

theorem step_C_left_one (L R : ListBlank (Fin 2)) :
    (mkCfg C 1 (0 >> 1 >> L) R) [target_tm]⊢⁺ (mkCfg C 1 L (0 >> 1 >> R)) :=
  ⟨2, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

/-- Sweep left across `rep01 m L` in state `C` (`2m` steps). -/
theorem sweep_C_left (m : Nat) (L R : ListBlank (Fin 2)) :
    (mkCfg C 1 (rep01 m L) R) [target_tm]⊢* (mkCfg C 1 L (rep01 m R)) := by
  induction m generalizing L R with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h1 := step_C_left_one (rep01 m L) R
    have h2 := ih L (0 >> 1 >> R)
    rw [rep01_snoc] at h2
    exact zPs (q7 h1 h2)

theorem step_A_right_one (L R : ListBlank (Fin 2)) :
    (mkCfg A 1 (1 >> L) (0 >> 1 >> R)) [target_tm]⊢⁺ (mkCfg A 1 (1 >> (0 >> 1 >> L)) R) :=
  ⟨4, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

/-- Sweep right across `rep01 m R` in state `A` (`4m` steps). -/
theorem sweep_A_right (m : Nat) (L R : ListBlank (Fin 2)) :
    (mkCfg A 1 (1 >> L) (rep01 m R)) [target_tm]⊢* (mkCfg A 1 (1 >> rep01 m L) R) := by
  induction m generalizing L R with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h1 := step_A_right_one L (rep01 m R)
    have h2 := ih (0 >> 1 >> L) R
    rw [rep01_snoc] at h2
    exact zPs (q7 h1 h2)

theorem step_AB_right_one (L R : ListBlank (Fin 2)) :
    (mkCfg A 0 L (1 >> 0 >> 1 >> R)) [target_tm]⊢⁺ (mkCfg A 0 (1 >> 1 >> L) (1 >> R)) :=
  ⟨2, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

/-- Sweep right across `1 >> rep01 m R` in state `A` (`2m` steps). -/
theorem sweep_AB_right (m : Nat) (L R : ListBlank (Fin 2)) :
    (mkCfg A 0 L (1 >> rep01 m R)) [target_tm]⊢* (mkCfg A 0 (rep1 (2 * m) L) (1 >> R)) := by
  induction m generalizing L R with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h1 := step_AB_right_one L (rep01 m R)
    have h2 := ih (1 >> 1 >> L) R
    have heq : rep1 (2 * m) (1 >> 1 >> L) = rep1 (2 * (m + 1)) L := by
      calc
        rep1 (2 * m) (1 >> 1 >> L) = rep1 (2 * m) (rep1 2 L) := rfl
        _ = rep1 (2 * m + 2) L := rep1_add (2 * m) 2 L
        _ = rep1 (2 * (m + 1)) L := rfl
    rw [heq] at h2
    exact zPs (q7 h1 h2)

theorem step_FE_left_one (L R : ListBlank (Fin 2)) :
    (mkCfg F 1 (0 >> 1 >> L) R) [target_tm]⊢⁺ (mkCfg F 1 L (1 >> 1 >> R)) :=
  ⟨2, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

/-- Sweep left across `rep01 m L` in state `F` (`2m` steps). -/
theorem sweep_FE_left (m : Nat) (L R : ListBlank (Fin 2)) :
    (mkCfg F 1 (rep01 m L) R) [target_tm]⊢* (mkCfg F 1 L (rep1 (2 * m) R)) := by
  induction m generalizing L R with
  | zero => exact ⟨0, rfl⟩
  | succ m ih =>
    have h1 := step_FE_left_one (rep01 m L) R
    have h2 := ih L (1 >> 1 >> R)
    have heq : rep1 (2 * m) (1 >> 1 >> R) = rep1 (2 * (m + 1)) R := by
      calc
        rep1 (2 * m) (1 >> 1 >> R) = rep1 (2 * m) (rep1 2 R) := rfl
        _ = rep1 (2 * m + 2) R := rep1_add (2 * m) 2 R
        _ = rep1 (2 * (m + 1)) R := rfl
    rw [heq] at h2
    exact zPs (q7 h1 h2)

theorem peel_entry (L R : ListBlank (Fin 2)) :
    (mkCfg B 1 L (1 >> 1 >> R)) [target_tm]⊢⁺ (mkCfg C 1 L (0 >> 1 >> R)) :=
  ⟨4, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

theorem peel_mid (L R : ListBlank (Fin 2)) :
    (mkCfg C 1 (1 >> L) R) [target_tm]⊢⁺ (mkCfg A 1 (1 >> L) R) :=
  ⟨2, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

theorem peel_end (L R : ListBlank (Fin 2)) :
    (mkCfg A 1 (1 >> L) (0 >> 1 >> R)) [target_tm]⊢⁺ (mkCfg B 1 (0 >> 1 >> L) (1 >> R)) :=
  ⟨3, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, A, B, C, D, E, F]⟩

theorem left_turn (R : ListBlank (Fin 2)) :
    (mkCfg C 1 default R) [target_tm]⊢⁺ (mkCfg A 0 default (1 >> R)) :=
  ⟨3, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩

theorem right_entry (L : ListBlank (Fin 2)) :
    (mkCfg B 1 L (1 >> default)) [target_tm]⊢⁺ (mkCfg F 1 (0 >> 1 >> L) (1 >> default)) :=
  ⟨4, by decide, by
    simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
      Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
      ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩

/-- Single peel step: `(peelState k (a + 1) (r + 1)) ⊢⁺ (peelState (k + 1) a r)`. -/
theorem peelState_step (k a r : Nat) :
    (peelState k (a + 1) (r + 1)) [target_tm]⊢⁺ (peelState (k + 1) a r) := by
  unfold peelState
  have h1 := peel_entry (rep01 k (1 >> rep1 a default)) (rep1 r default)
  have h2 := sweep_C_left k (1 >> rep1 a default) (0 >> 1 >> rep1 r default)
  have h3 := peel_mid (rep1 a default) (rep01 k (0 >> 1 >> rep1 r default))
  have h4 := sweep_A_right k (rep1 a default) (0 >> 1 >> rep1 r default)
  have h5 := peel_end (rep01 k (rep1 a default)) (rep1 r default)
  exact q7 (q8 (zPs (q7 h1 h2)) (q7 h3 h4)) (zPs h5)

/-- Iterated peel lemma across `n` steps. -/
theorem peelState_many (n k a r : Nat) :
    (peelState k (n + a) (n + r)) [target_tm]⊢* (peelState (k + n) a r) := by
  induction n generalizing k a r with
  | zero =>
    have ha : 0 + a = a := Nat.zero_add a
    have hr : 0 + r = r := Nat.zero_add r
    rw [ha, hr, Nat.add_zero]
  | succ n ih =>
    have ha : (n + 1) + a = n + a + 1 := by omega
    have hr : (n + 1) + r = n + r + 1 := by omega
    rw [ha, hr]
    have h1 := peelState_step k (n + a) (n + r)
    have h2 := ih (k + 1) a r
    have hk : k + 1 + n = k + (n + 1) := by omega
    rw [hk] at h2
    exact zPs (q7 h1 h2)

/-- Rule 1 (`a ≤ c - 1`): `(cfgB a (a + d + 1)) ⊢⁺ (cfgB (2a + 2) d)`. -/
theorem rule_lt (a d : Nat) :
    (cfgB a (a + d + 1)) [target_tm]⊢⁺ (cfgB (2 * a + 2) d) := by
  cases a with
  | zero =>
    have hd : 0 + d + 1 = d + 1 := by omega
    rw [hd]
    show (mkCfg B 0 default (1 >> 1 >> rep1 d default)) [target_tm]⊢⁺
        (mkCfg B 1 (1 >> default) (1 >> rep1 d default))
    exact ⟨3, by decide, by
      simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
        Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
        ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩
  | succ k =>
    have h0 : cfgB (k + 1) (k + 1 + d + 1) = peelState 0 (k + 0) (k + (d + 2)) := by
      rw [peelState_zero]; congr 1; omega
    rw [h0]
    refine q8 (peelState_many k 0 0 (d + 2)) ?_
    rw [Nat.zero_add]
    unfold peelState rep1
    have h1 := peel_entry (rep01 k default) (1 >> rep1 d default)
    have h2 := sweep_C_left k default (0 >> 1 >> 1 >> rep1 d default)
    rw [rep01_snoc] at h2
    have h3 := left_turn (rep01 (k + 1) (1 >> rep1 d default))
    have h4 := sweep_AB_right (k + 1) default (1 >> rep1 d default)
    have h5 : (mkCfg A 0 (rep1 (2 * (k + 1)) default) (1 >> 1 >> rep1 d default)) [target_tm]⊢⁺
        (cfgB (2 * (k + 1) + 2) d) := by
      show (mkCfg A 0 (rep1 (2 * (k + 1)) default) (1 >> 1 >> rep1 d default)) [target_tm]⊢⁺
          (mkCfg B 1 (1 >> rep1 (2 * (k + 1)) default) (1 >> rep1 d default))
      exact ⟨1, by decide, by
        simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
          Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
          ListBlank.tail_cons, A, B, C, D, E, F]⟩
    exact q7 (q8 (zPs (q7 h1 h2)) (q7 h3 h4)) (zPs h5)

/-- Rule 2 (`a = c`): `(cfgB a a) ⊢⁺ (cfgB (2a + 2) 0)`. -/
theorem rule_eq (a : Nat) :
    (cfgB a a) [target_tm]⊢⁺ (cfgB (2 * a + 2) 0) := by
  cases a with
  | zero =>
    show (mkCfg B 0 default (1 >> default)) [target_tm]⊢⁺
        (mkCfg B 1 (1 >> default) (1 >> default))
    exact ⟨7, by decide, by
      simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
        Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
        ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩
  | succ k =>
    have h0 : cfgB (k + 1) (k + 1) = peelState 0 (k + 0) (k + 1) := rfl
    rw [h0]
    refine q8 (peelState_many k 0 0 1) ?_
    rw [Nat.zero_add]
    unfold peelState rep1
    have h1 := peel_entry (rep01 k default) default
    have h2 := sweep_C_left k default (0 >> 1 >> default)
    rw [rep01_snoc] at h2
    have h3 := left_turn (rep01 (k + 1) default)
    have h4 := sweep_AB_right (k + 1) default default
    have h5 : (mkCfg A 0 (rep1 (2 * (k + 1)) default) (1 >> default)) [target_tm]⊢⁺
        (cfgB (2 * (k + 1) + 2) 0) := by
      show (mkCfg A 0 (rep1 (2 * (k + 1)) default) (1 >> default)) [target_tm]⊢⁺
          (mkCfg B 1 (1 >> rep1 (2 * (k + 1)) default) (1 >> default))
      exact ⟨5, by decide, by
        simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
          Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
          ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩
    exact q7 (q8 (zPs (q7 h1 h2)) (q7 h3 h4)) (zPs h5)

/-- Rule 3 (`a ≥ c + 2`): `(cfgB (c + d + 2) c) ⊢⁺ (cfgB d (2c + 4))`. -/
theorem rule_ge (d c : Nat) :
    (cfgB (c + d + 2) c) [target_tm]⊢⁺ (cfgB d (2 * c + 4)) := by
  have h0 : cfgB (c + d + 2) c = peelState 0 (c + (d + 1)) (c + 0) := rfl
  rw [h0]
  refine q8 (peelState_many c 0 (d + 1) 0) ?_
  rw [Nat.zero_add]
  unfold peelState
  have h1 := right_entry (rep01 c (rep1 (d + 1) default))
  have h2 := sweep_FE_left (c + 1) (rep1 (d + 1) default) (1 >> default)
  have heq : rep1 (2 * (c + 1)) (1 >> default) = rep1 (2 * c + 3) default := by
    calc
      rep1 (2 * (c + 1)) (1 >> default)
          = rep1 (2 * (c + 1)) (rep1 1 default) := rfl
      _ = rep1 (2 * (c + 1) + 1) default := rep1_add (2 * (c + 1)) 1 default
      _ = rep1 (2 * c + 3) default := rfl
  rw [heq] at h2
  have h3 : (mkCfg F 1 (rep1 (d + 1) default) (rep1 (2 * c + 3) default)) [target_tm]⊢⁺
      (cfgB d (2 * c + 4)) := by
    cases d with
    | zero =>
      show (mkCfg F 1 (1 >> default) (rep1 (2 * c + 3) default)) [target_tm]⊢⁺
          (mkCfg B 0 default (1 >> 1 >> rep1 (2 * c + 3) default))
      exact ⟨2, by decide, by
        simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
          Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
          ListBlank.tail_cons, zDh, zDt, zZcd, A, B, C, D, E, F]⟩
    | succ d' =>
      show (mkCfg F 1 (1 >> 1 >> rep1 d' default) (rep1 (2 * c + 3) default)) [target_tm]⊢⁺
          (mkCfg B 1 (rep1 d' default) (1 >> 1 >> rep1 (2 * c + 3) default))
      exact ⟨2, by decide, by
        simp only [multiStep, Function.iterate_succ', Function.iterate_zero, id_eq, Function.comp_apply,
          Option.bind, Option.map, step, Tape.mk₂, Tape.mk', target_tm, mkCfg, Tape.write, Tape.move, ListBlank.head_cons,
          ListBlank.tail_cons, A, B, C, D, E, F]⟩
  exact q7 (q7 h1 h2) (zPs h3)

@[simp] theorem zEmpty : (ListBlank.mk ([] : List (Fin 2)) : ListBlank (Fin 2)) = default := by
  apply Turing.ListBlank.ext; intro i; cases i <;> rfl

/-- Blank-tape entry (`3` micro-steps): `(init []) ⊢⁺ (cfgB 0 0)`. -/
theorem init_to_cfgB : (init []) [target_tm]⊢⁺ (cfgB 0 0) :=
  ⟨3, by decide, by
    simp only [init, Tape.mk₁, Tape.mk₂, Tape.mk', zEmpty, multiStep, Function.iterate_succ',
      Function.iterate_zero, id_eq, Function.comp_apply, Option.bind, Option.map, step, target_tm,
      cfgB, rep1, mkCfg, Tape.write, Tape.move, ListBlank.head_cons, ListBlank.tail_cons,
      zDh, zDt, zZcd, A, B, C, D, E, F, Fin.default_eq_zero]⟩

/-- Computable macro-stepper for `cfgB a c`. -/
def stepB : Nat × Nat → Option (Nat × Nat)
  | (a, c) =>
    if a < c then some (2 * a + 2, c - a - 1)
    else if a == c then some (2 * a + 2, 0)
    else if a == c + 1 then none
    else some (a - c - 2, 2 * c + 4)

theorem stepB_sound (p p' : Nat × Nat) (h : stepB p = some p') :
    (cfgB p.1 p.2) [target_tm]⊢⁺ (cfgB p'.1 p'.2) := by
  rcases p with ⟨a, c⟩
  dsimp only
  dsimp only [stepB] at h
  by_cases h1 : a < c
  · rw [if_pos h1] at h; simp at h; rcases h with ⟨rfl, rfl⟩
    dsimp only
    have hc : c = a + (c - a - 1) + 1 := by omega
    nth_rw 1 [hc]
    exact rule_lt a (c - a - 1)
  · rw [if_neg h1] at h
    by_cases h2 : a = c
    · subst h2; simp at h; rcases h with ⟨rfl, rfl⟩
      exact rule_eq a
    · have h2b : (a == c) = false := beq_false_of_ne h2
      rw [h2b] at h; simp only [Bool.false_eq_true, ↓reduceIte] at h
      have h3 : a ≠ c + 1 := by
        intro heq; subst heq; simp at h
      have h3b : (a == c + 1) = false := beq_false_of_ne h3
      rw [h3b] at h; simp at h; rcases h with ⟨rfl, rfl⟩
      dsimp only
      have ha : a = c + (a - c - 2) + 2 := by omega
      nth_rw 1 [ha]
      exact rule_ge (a - c - 2) c

/-- Tail-recursive multi-step evaluator for `stepB`. -/
def runStepB : Nat → Nat × Nat → Option (Nat × Nat)
  | 0, p => some p
  | n + 1, p =>
    match stepB p with
    | none => none
    | some p' => runStepB n p'

theorem runStepB_sound (n : Nat) (p p' : Nat × Nat) (h : runStepB n p = some p') :
    (cfgB p.1 p.2) [target_tm]⊢* (cfgB p'.1 p'.2) := by
  induction n generalizing p with
  | zero =>
    simp [runStepB] at h; subst h; exact ⟨0, rfl⟩
  | succ n ih =>
    simp only [runStepB] at h
    cases hst : stepB p with
    | none => rw [hst] at h; simp at h
    | some pm =>
      rw [hst] at h
      exact zPs (q7 (stepB_sound p pm hst) (ih pm h))

/-- Kernel-checked 303-macro-step trajectory from `(0, 0)` to `(150, 300)` (`5,056,008` steps). -/
theorem bootstrap_303 : runStepB 303 (0, 0) = some (150, 300) := by
  decide

theorem reach_150_300 : (init []) [target_tm]⊢⁺ (cfgB 150 300) :=
  q7 init_to_cfgB (runStepB_sound 303 (0, 0) (150, 300) bootstrap_303)

/-- Closed infinite loop invariant: `{ cfgB (n + 1) (2 * (n + 1)) | n : ℕ }`. -/
def Inv (cfg : Cfg (Fin 2) (Fin 6)) : Prop :=
  ∃ n : Nat, cfg = cfgB (n + 1) (2 * (n + 1))

theorem loop_step (n : Nat) :
    (cfgB (n + 1) (2 * (n + 1))) [target_tm]⊢⁺ (cfgB (n + 2) (2 * (n + 2))) := by
  have h1 : (cfgB (n + 1) (2 * (n + 1))) [target_tm]⊢⁺ (cfgB (2 * n + 4) n) := by
    have heq1 : 2 * (n + 1) = (n + 1) + n + 1 := by omega
    rw [heq1]
    have hlt := rule_lt (n + 1) n
    have heq2 : 2 * (n + 1) + 2 = 2 * n + 4 := by omega
    rwa [heq2] at hlt
  have h2 : (cfgB (2 * n + 4) n) [target_tm]⊢⁺ (cfgB (n + 2) (2 * (n + 2))) := by
    have heq3 : 2 * n + 4 = n + (n + 2) + 2 := by omega
    rw [heq3]
    have hge := rule_ge (n + 2) n
    have heq4 : 2 * n + 4 = 2 * (n + 2) := by omega
    rwa [heq4] at hge
  exact q7 h1 (zPs h2)



theorem is_does_not_halt : IsNotHalt target_tm := by
  refine isNotHalt_of_invariant target_tm Inv ?_ ?_
  · exact ⟨cfgB 150 300, reach_150_300, ⟨149, rfl⟩⟩
  · intro c hc
    rcases hc with ⟨n, rfl⟩
    exact ⟨cfgB (n + 2) (2 * (n + 2)), loop_step n, ⟨n + 1, rfl⟩⟩

theorem is_not_halt : IsNotHalt target := by
  rw [target_eq_target_tm]
  exact is_does_not_halt

end BusyBeaver.M_1RB0RD_0LC1RA_0RA1LB_1RE1LB_1LF1LB_HHH1LE
