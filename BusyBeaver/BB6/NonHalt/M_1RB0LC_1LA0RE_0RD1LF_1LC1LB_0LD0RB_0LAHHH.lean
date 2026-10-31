/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import BusyBeaver.Basic
import BusyBeaver.Longitudinal

/-!
# Busy Beaver Machine `1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LA---` — `is_does_not_halt` (`IsNotHalt target_tm`)

This file imports shared trusted definitions from `BusyBeaver.Basic`, `BusyBeaver.Longitudinal`
and defines `target_tm` for `1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LA---`. Do not modify the trusted
definitions section or the goal theorem signature.
-/

open Mathlib Relation Nat Turing BusyBeaver

namespace BusyBeaver.M_1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LAHHH

-- BEGIN TRUSTED DEFINITIONS (DO NOT MODIFY)

variable {Γ Λ : Type*} [Inhabited Γ] [Inhabited Λ]

/-- Transition function for `1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LA---`. -/
def target_tm : Machine (Fin 2) (Fin 6)
  | 0, 0 => some (some 1, Stmt.write 1 Dir.right)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.left)
  | 1, 0 => some (some 0, Stmt.write 1 Dir.left)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.right)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.left)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.left)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.left)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.right)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.left)
  | 5, 1 => none

-- END TRUSTED DEFINITIONS

-- BEGIN EXPLORATORY DEFINITIONS AND LEMMAS

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 2000000
set_option maxHeartbeats 20000000

open BusyBeaver.Longitudinal
open BusyBeaver.Longitudinal.BoundedConfig


abbrev Q := Fin 6
abbrev Sym := Fin 2


/-- TM1 (`1RB0LC_1LA0RE_0RD0LA_1RE1RA_0LD1RF_0RB---`, donor Holdout #272 for Holdout #87) -/
def tm1 : Machine Sym Q
  | 0, 0 => some (some 1, ⟨1, .right⟩)
  | 0, 1 => some (some 2, ⟨0, .left⟩)
  | 1, 0 => some (some 0, ⟨1, .left⟩)
  | 1, 1 => some (some 4, ⟨0, .right⟩)
  | 2, 0 => some (some 3, ⟨0, .right⟩)
  | 2, 1 => some (some 0, ⟨0, .left⟩)
  | 3, 0 => some (some 4, ⟨1, .right⟩)
  | 3, 1 => some (some 0, ⟨1, .right⟩)
  | 4, 0 => some (some 3, ⟨0, .left⟩)
  | 4, 1 => some (some 5, ⟨1, .right⟩)
  | 5, 0 => some (some 1, ⟨0, .right⟩)
  | 5, 1 => none

abbrev t : List Sym := [1, 0]
abbrev u : List Sym := [1, 0, 1]
abbrev d : List Sym := [1, 1, 0]
abbrev w : List Sym := [1, 0, 1, 1, 0]
abbrev v : List Sym := [1, 1, 0, 1, 0]

abbrev hp : List (DH0 Sym Q × DH0 Sym Q) := [((B, [0]), (C, [0]))]
abbrev hq : List (DH0 Sym Q × DH0 Sym Q) := [((B, [0]), (A, [0, 0]))]
abbrev hr : List (DH0 Sym Q × DH0 Sym Q) := [((B, [0]), (A, [0, 0, 0, 0]))]
abbrev hi : List (DH0 Sym Q × DH0 Sym Q) := [((B, [1, 1, 0]), (C, [0, 1, 0]))]
abbrev hc : List (DH0 Sym Q × DH0 Sym Q) := [((B, []), (A, []))]
abbrev hm : List (DH0 Sym Q × DH0 Sym Q) := [((B, [1]), (A, [0]))]

def P (n : ℕ) (r s : ListBlank Sym) : Prop := SideRLs tm1 (hp ^ n) r s
def I (n : ℕ) (r s : ListBlank Sym) : Prop := SideRLs tm1 (hi ^ n) r s

theorem Pd : SegRLs tm1 hp (hp ^ 2) d u :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem PdQP : SegRLs tm1 hp (hp ++ hq) d [1, 0, 0, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem PdR : SegRLs tm1 hp hr d (w ++ [1]) :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pt : SegRLs tm1 hp hi t t :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Id : SegRLs tm1 hi hp d d :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pw : SegRLs tm1 hp hp w w :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Iq : SegRLs tm1 hi hq d (d ++ [1]) :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pwq : SegRLs tm1 hp hq w (w ++ [1]) :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Iv : SegRLs tm1 hi hi v v :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pv : SegRLs tm1 hp (hi ^ 2) v w :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pdw : SegRLs tm1 hp (hp ^ 2) (d ++ w) (w ++ d) :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Icarry : SegRLs tm1 hi hc [] [] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pcarry0 : SegRLs tm1 hp hc [0, 0] [0, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Pcarry1 : SegRLs tm1 hp hc t t :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem carry0 : SegRLs tm1 hc [] [0, 0] [1, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem carry1 : SegRLs tm1 hc hc [1, 0] [0, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem carry_bit0 : SegRLs tm1 hc [] [0] [1] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem carry_word0 : SegRLs tm1 hc [] [0, 1, 0] d :=
  segRLs_c_spec tm1 (T := 500) (by decide)

-- Overflow finite rules via hm = [((B, [1]), (A, [0]))]
theorem Iov_t : SegRLs tm1 hi hm t t :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Qov_00 : SegRLs tm1 hq hm [0, 0] [0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Mov_t : SegRLs tm1 hm hm t [0, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Mov_dp : SegRLs tm1 hm hp d [0, 1, 0] :=
  segRLs_c_spec tm1 (T := 500) (by decide)
theorem Mov_dq : SegRLs tm1 hm hq d [0, 1, 0, 1] :=
  segRLs_c_spec tm1 (T := 500) (by decide)

theorem Mov_ts (k : ℕ) : SegRLs tm1 hm hm (t ^ k) ([0, 0] ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm1 hm
  | succ k ih =>
    rw [Longitudinal.pow_succ_list, Longitudinal.pow_succ_list]
    exact Mov_t.concat ih

theorem lpow_shift_list {α : Type*} (xs : List α) (k : ℕ) :
    xs ^ k ++ xs = xs ++ xs ^ k := by
  rw [← pow_succ_list', Longitudinal.pow_succ_list]

theorem lpow_shift_stream (xs : List Sym) (k : ℕ) (r : ListBlank Sym) :
    xs ^ k +> (xs +> r) = xs +> (xs ^ k +> r) := by
  rw [← append_assoc, lpow_shift_list, append_assoc]

theorem lpow_rotate' (a₁ a₀ : List Sym) (b : ListBlank Sym) (n : ℕ) :
    (a₁ ++ a₀) ^ n +> (a₁ +> b) = a₁ +> ((a₀ ++ a₁) ^ n +> b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Longitudinal.pow_succ_list, Longitudinal.pow_succ_list, append_assoc, append_assoc, ih]
    simp only [append_assoc]

theorem lpow_rotate_list {α : Type*} (a₁ a₀ : List α) (n : ℕ) :
    (a₁ ++ a₀) ^ n ++ a₁ = a₁ ++ (a₀ ++ a₁) ^ n := by
  induction n with
  | zero => simp [Longitudinal.pow_zero_list]
  | succ n ih =>
    rw [Longitudinal.pow_succ_list, Longitudinal.pow_succ_list]
    simp only [List.append_assoc]
    rw [ih]

theorem zero_pair_shift (k : ℕ) (ys : List Sym) :
    ([0] : List Sym) ++ ([0, 0] ^ k ++ (0 :: ys)) = [0, 0] ^ (1 + k) ++ ys := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h1 : ([0, 0] : List Sym) ^ (k + 1) = [0, 0] ++ [0, 0] ^ k := rfl
    have h2 : ([0, 0] : List Sym) ^ (1 + (k + 1)) = [0, 0] ++ [0, 0] ^ (1 + k) := rfl
    rw [h1, h2, List.append_assoc]
    change (0 : Sym) :: 0 :: ([0] ++ ([0, 0] ^ k ++ (0 :: ys))) = 0 :: 0 :: ([0, 0] ^ (1 + k) ++ ys)
    rw [ih]

theorem P_add {a b : ℕ} {r s z : ListBlank Sym} (h1 : P a r s) (h2 : P b s z) :
    P (a + b) r z :=
  SideRLs.trans_add h1 h2

theorem I_add {a b : ℕ} {r s z : ListBlank Sym} (h1 : I a r s) (h2 : I b s z) :
    I (a + b) r z :=
  SideRLs.trans_add h1 h2

theorem P_split (a b : ℕ) {r z : ListBlank Sym} (h : P (a + b) r z) :
    ∃ s, P a r s ∧ P b s z := by
  unfold P at h ⊢
  rw [pow_add_list] at h
  exact h.split

theorem I_split (a b : ℕ) {r z : ListBlank Sym} (h : I (a + b) r z) :
    ∃ s, I a r s ∧ I b s z := by
  unfold I at h ⊢
  rw [pow_add_list] at h
  exact h.split

theorem Pws (n k : ℕ) : SegRLs tm1 (hp ^ n) (hp ^ n) (w ^ k) (w ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm1 (hp ^ n)
  | succ k ih =>
    rw [Longitudinal.pow_succ_list]
    exact (Pw.wall_pow n).concat ih

theorem Ivs (n k : ℕ) : SegRLs tm1 (hi ^ n) (hi ^ n) (v ^ k) (v ^ k) := by
  induction k with
  | zero => exact SegRLs.empty tm1 (hi ^ n)
  | succ k ih =>
    rw [Longitudinal.pow_succ_list]
    exact (Iv.wall_pow n).concat ih

theorem Pts (n : ℕ) : SegRLs tm1 (hp ^ n) (hi ^ n) t t :=
  Pt.wall_pow n

theorem Ids (n : ℕ) : SegRLs tm1 (hi ^ n) (hp ^ n) d d :=
  Id.wall_pow n

theorem Pvs (n k : ℕ) : SegRLs tm1 (hp ^ n) (hi ^ (n * 2)) (v ^ (n + k)) (w ^ n ++ v ^ k) := by
  induction n with
  | zero =>
    rw [Nat.zero_add]
    exact SegRLs.nil (M := tm1) (v ^ k)
  | succ n ih =>
    have h_hi : hi ^ ((n + 1) * 2) = hi ^ 2 ++ hi ^ (n * 2) := by
      have : (n + 1) * 2 = 2 + n * 2 := by omega
      rw [this, pow_add_list]
    have h_v : v ^ (n + 1 + k) = v ++ v ^ (n + k) := by
      have : n + 1 + k = (n + k) + 1 := by omega
      rw [this, Longitudinal.pow_succ_list]
    have h_hp : hp ^ (n + 1) = hp ++ hp ^ n := rfl
    have h_w : w ^ (n + 1) ++ v ^ k = w ++ (w ^ n ++ v ^ k) := by
      rw [Longitudinal.pow_succ_list, List.append_assoc]
    rw [h_hp, h_hi, h_v, h_w]
    exact (Pv.concat (Ivs 2 (n + k))).trans ((Pw.wall_pow n).concat ih)

theorem P_w (n k : ℕ) {r s : ListBlank Sym} (h : P n r s) :
    P n (w ^ k +> r) (w ^ k +> s) :=
  (Pws n k).sideRLs_concat h

theorem I_v (n k : ℕ) {r s : ListBlank Sym} (h : I n r s) :
    I n (v ^ k +> r) (v ^ k +> s) :=
  (Ivs n k).sideRLs_concat h

theorem P_t (n : ℕ) {r s : ListBlank Sym} (h : I n r s) :
    P n (t +> r) (t +> s) :=
  (Pts n).sideRLs_concat h

theorem I_d (n : ℕ) {r s : ListBlank Sym} (h : P n r s) :
    I n (d +> r) (d +> s) :=
  (Ids n).sideRLs_concat h

theorem P_d {r s : ListBlank Sym} (h : P 2 r s) :
    P 1 (d +> r) (u +> s) :=
  Pd.sideRLs_concat h

inductive G1 : ListBlank Sym → ListBlank Sym → Prop where
  | GP {r s : ListBlank Sym} : P 1 r s → G1 r s
  | GQ {r s : ListBlank Sym} : SideRLs tm1 hq r s → G1 r ([1] +> s)

inductive G : ℕ → ListBlank Sym → ListBlank Sym → Prop where
  | G0 (r : ListBlank Sym) : G 0 r r
  | GS {n : ℕ} {r s z : ListBlank Sym} : G1 r s → G n s z → G (n + 1) r z

theorem G_add {a b : ℕ} {r s z : ListBlank Sym} (h1 : G a r s) (h2 : G b s z) :
    G (a + b) r z := by
  induction h1 with
  | G0 _ => simpa only [Nat.zero_add] using h2
  | @GS n r' s' z' hg1 _ ih =>
    have : n + 1 + b = (n + b) + 1 := by omega
    rw [this]
    exact .GS hg1 (ih h2)

theorem G_w {n : ℕ} {r s : ListBlank Sym} (h : G n r s) :
    P n (w +> r) (w +> s) := by
  induction h with
  | G0 _ => exact .nil _
  | @GS n r' s' z' hg1 _ ih =>
    have : n + 1 = 1 + n := by omega
    rw [this]
    refine P_add (a := 1) (b := n) ?_ ih
    cases hg1 with
    | GP hp1 => exact Pw.sideRLs_concat hp1
    | GQ hq1 =>
      have : P 1 (w +> r') ((w ++ [1]) +> _) := Pwq.sideRLs_concat hq1
      simpa only [append_assoc] using this

theorem G_d {n : ℕ} {r s : ListBlank Sym} (h : G n r s) :
    I n (d +> r) (d +> s) := by
  induction h with
  | G0 _ => exact .nil _
  | @GS n r' s' z' hg1 _ ih =>
    have : n + 1 = 1 + n := by omega
    rw [this]
    refine I_add (a := 1) (b := n) ?_ ih
    cases hg1 with
    | GP hp1 => exact Id.sideRLs_concat hp1
    | GQ hq1 =>
      have : I 1 (d +> r') ((d ++ [1]) +> _) := Iq.sideRLs_concat hq1
      simpa only [append_assoc] using this

theorem P_G {n : ℕ} {r s : ListBlank Sym} (h : P n r s) : G n r s := by
  induction n generalizing r with
  | zero =>
    cases h
    exact .G0 _
  | succ n ih =>
    have h' : P (1 + n) r s := by
      have : 1 + n = n + 1 := by omega
      rwa [this]
    obtain ⟨z, h1, hn⟩ := P_split 1 n h'
    exact .GS (.GP h1) (ih hn)

theorem column1 (b : ℕ) {r x s : ListBlank Sym} (hi2 : I 2 r x) (hg : G (1 + b) x s) :
    ∃ z, P b (v +> r) z ∧ P 1 (d +> z) (w +> (d +> s)) := by
  have h : P (1 + (1 + b)) (v +> r) (w +> s) :=
    P_add (Pv.sideRLs_concat hi2) (G_w hg)
  have heq : 1 + (1 + b) = b + 2 := by omega
  rw [heq] at h
  obtain ⟨z, hz, h2⟩ := P_split b 2 h
  refine ⟨z, hz, ?_⟩
  have hpd := P_d h2
  simpa only [u, w, d, append_cons, append_nil] using hpd

theorem column_aux (a b : ℕ) {r x s : ListBlank Sym}
    (hi_a : I (a * 2) r x) (hg : G (a + b) x s) :
    ∃ z, G b (v ^ a +> r) z ∧ G a (d +> z) (w ^ a +> (d +> s)) := by
  induction a generalizing b r x s with
  | zero =>
    cases hi_a
    exact ⟨s, by simpa using hg, .G0 _⟩
  | succ a ih =>
    have hi' : I (2 + a * 2) r x := by
      have : 2 + a * 2 = (a + 1) * 2 := by omega
      rwa [this]
    obtain ⟨y, hy, hx⟩ := I_split 2 (a * 2) hi'
    have hg' : G (a + (1 + b)) x s := by
      have : a + (1 + b) = a + 1 + b := by omega
      rwa [this]
    obtain ⟨z, hz, hs⟩ := ih (1 + b) hx hg'
    obtain ⟨z', hz', h1⟩ := column1 b (I_v 2 a hy) hz
    refine ⟨z', P_G hz', ?_⟩
    have : a + 1 = 1 + a := by omega
    rw [Longitudinal.pow_succ_list w, append_assoc, this]
    exact P_G (P_add h1 (G_w hs))

inductive Run (a b c : ℕ) (r s : ListBlank Sym) : Prop where
  | run (x y : ListBlank Sym) : P c r x → I b ([1] +> x) y → G a y s → Run a b c r s

abbrev Suffix (a b : ℕ) (r s : ListBlank Sym) : Prop := Run a b 2 r s

theorem column {a b : ℕ} {r s : ListBlank Sym} (h : Suffix (a + b) (a * 2 + 1) r s) :
    Suffix a b (w ^ a +> (d +> r)) (w ^ a +> (d +> s)) := by
  rcases h with ⟨x, y, hp2, hi_ab, ha⟩
  have hi' : I (1 + a * 2) ([1] +> x) y := by
    have : 1 + a * 2 = a * 2 + 1 := by omega
    rwa [this]
  obtain ⟨z, h1, hz⟩ := I_split 1 (a * 2) hi'
  obtain ⟨z', hb, ha'⟩ := column_aux a b hz ha
  refine ⟨w ^ a +> (t +> z), d +> z', ?_, ?_, ha'⟩
  · refine P_w 2 a (P_add (a := 1) (b := 1) (P_d hp2) ?_)
    have hpt := P_t 1 h1
    simpa only [u, t, append_cons, append_nil] using hpt
  · have hrot := lpow_rotate' t d z a
    have hgd := G_d hb
    have hwv : w = t ++ d := rfl
    have hvw : v = d ++ t := rfl
    have h_eq : ([1] : List Sym) +> (w ^ a +> (t +> z)) = d +> (v ^ a +> z) := by
      rw [hwv, hrot, ← hvw]
      rfl
    rwa [h_eq]

theorem PdPd (b : ℕ) {r x s : ListBlank Sym} (hp2 : P 2 r x) (hi1 : I (1 + b) ([1] +> x) s) :
    ∃ z, P b (d +> r) z ∧ P 1 (d +> z) (w +> s) := by
  have h : P (1 + (1 + b)) (d +> r) (t +> s) := by
    refine P_add (a := 1) (b := 1 + b) (P_d hp2) ?_
    have hpt := P_t (1 + b) hi1
    simpa only [u, t, append_cons, append_nil] using hpt
  have heq : 1 + (1 + b) = b + 2 := by omega
  rw [heq] at h
  obtain ⟨z, hz, h2⟩ := P_split b 2 h
  refine ⟨z, hz, ?_⟩
  have hpd := P_d h2
  simpa only [u, w, t, append_cons, append_nil] using hpd

theorem run_w_g {a b c : ℕ} {r x y z s : ListBlank Sym}
    (hg : G c r x) (hp2 : P 2 x y) (hi1 : I (1 + b) ([1] +> y) z) (ha : G a z s) :
    Run (1 + a) b c (w +> r) (w +> s) := by
  obtain ⟨z', hb, h1⟩ := PdPd b hp2 hi1
  exact ⟨w +> x, d +> z', G_w hg, I_d b hb, P_G (P_add h1 (G_w ha))⟩

theorem run_w {a b c : ℕ} {r s : ListBlank Sym} (h : Run a (1 + b) (c + 2) r s) :
    Run (1 + a) b c (w +> r) (w +> s) := by
  rcases h with ⟨x, y, hp_c2, hi1, ha⟩
  obtain ⟨z, hc, h2⟩ := P_split c 2 hp_c2
  exact run_w_g (P_G hc) h2 hi1 ha

theorem run_ws (j a b c : ℕ) {r s : ListBlank Sym}
    (h : Run a (b + j) (c + j * 2) r s) :
    Run (a + j) b c (w ^ j +> r) (w ^ j +> s) := by
  induction j generalizing b c with
  | zero => simpa using h
  | succ j ih =>
    have h' : Run a ((1 + b) + j) ((c + 2) + j * 2) r s := by
      have h1 : (1 + b) + j = b + (j + 1) := by omega
      have h2 : (c + 2) + j * 2 = c + (j + 1) * 2 := by omega
      rwa [h1, h2]
    have ih_res := run_w (ih (1 + b) (c + 2) h')
    have h3 : 1 + (a + j) = a + (j + 1) := by omega
    rw [Longitudinal.pow_succ_list, append_assoc, ← h3]
    exact ih_res

theorem column_partial {a b j : ℕ} {r s : ListBlank Sym}
    (hj : j ≤ a) (h : Run (a - j) (b + j) (j * 2 + 2) r s) :
    Suffix a b (w ^ j +> r) (w ^ j +> s) := by
  have h' : Run (a - j) (b + j) (2 + j * 2) r s := by
    have : 2 + j * 2 = j * 2 + 2 := by omega
    rwa [this]
  have hres := run_ws j (a - j) b 2 h'
  have : a - j + j = a := by omega
  rwa [this] at hres

theorem column_early {a b j : ℕ} {r x y z s : ListBlank Sym}
    (hj0 : 0 < j) (hja : j ≤ a)
    (hg : G (j * 2) r x) (hp2 : P 2 x y) (hi_bj : I (b + j) ([1] +> y) z) (hs : G (a - j) z s) :
    Suffix a b (w ^ j +> r) (w ^ j +> s) := by
  rcases j with _ | j
  · omega
  · rw [Longitudinal.pow_succ_list w j, append_assoc w (w ^ j) r, append_assoc w (w ^ j) s,
      ← lpow_shift_stream w j r, ← lpow_shift_stream w j s]
    refine column_partial (j := j) (by omega) ?_
    have hg' : G (j * 2 + 2) r x := by
      have : j * 2 + 2 = (j + 1) * 2 := by omega
      rwa [this]
    have hi' : I (1 + (b + j)) ([1] +> y) z := by
      have : 1 + (b + j) = b + (j + 1) := by omega
      rwa [this]
    have hrun := run_w_g hg' hp2 hi' hs
    have : 1 + (a - (j + 1)) = a - j := by omega
    rwa [this] at hrun

inductive Inner (j : ℕ) (r s : ListBlank Sym) : Prop where
  | InnerP : P (j * 2 + 2) r s → Inner j r s
  | InnerG (x : ListBlank Sym) : 0 < j → G (j * 2) r x → P 2 x s → Inner j r s

theorem inner_column {a b j : ℕ} {r x y s : ListBlank Sym}
    (hj : j ≤ a) (hin : Inner j r x) (hi_bj : I (b + j) ([1] +> x) y) (hg : G (a - j) y s) :
    Suffix a b (w ^ j +> r) (w ^ j +> s) := by
  cases hin with
  | InnerP hp => exact column_partial hj ⟨x, y, hp, hi_bj, hg⟩
  | InnerG x' hj0 hg_j hp2 => exact column_early hj0 hj hg_j hp2 hi_bj hg

def cfg (r : ListBlank Sym) : Cfg Sym Q :=
  default {{C}}> ([0, 0, 1, 0] +> r)

theorem root_step {r s : ListBlank Sym} (h : P 1 r s) :
    (cfg r) [tm1]⊢⁺ (cfg ([1] +> s)) := by
  have h1 : (cfg r) [tm1]⊢* (toDHCfg ((B, [0]), .right) ([1, 1, 0] +> default) r) :=
    steps_spec tm1 10 ⟨[], [0, 0, 1, 0], C, .right⟩
      (x' := ⟨[0, 1, 1, 0], [], B, .right⟩) (by decide) default r
  have h2 : (toDHCfg ((B, [0]), .right) ([1, 1, 0] +> default) r) [tm1]⊢⁺
      (toDHCfg ((C, [0]), .left) ([1, 1, 0] +> default) s) :=
    h.elim_single ([1, 1, 0] +> default)
  have h3 : (toDHCfg ((C, [0]), .left) ([1, 1, 0] +> default) s) [tm1]⊢* (cfg ([1] +> s)) := by
    have h3' := steps_spec tm1 50 ⟨[0], [1, 1, 0], C, .left⟩
      (x' := ⟨[0, 1, 0, 1], [], C, .left⟩) (by decide) default s
    simpa [toDHCfg, toCfg, cfg, append_cons, ListBlank.head_cons, ListBlank.tail_cons] using h3'
  exact stepStar_stepPlus_trans h1 (stepPlus_stepStar_trans h2 h3)

theorem root_base {r s : ListBlank Sym} (h : Suffix 0 1 r s) :
    (cfg (d +> (d +> r))) [tm1]⊢⁺ (cfg (d +> (d +> s))) := by
  rcases h with ⟨x, y, hp2, hi1, ha⟩
  cases ha
  have h1 : P 2 (d +> r) (t +> s) := by
    refine P_add (a := 1) (b := 1) (P_d hp2) ?_
    have hpt := P_t 1 hi1
    simpa only [u, t, append_cons, append_nil] using hpt
  have h2 : P 1 (d +> (d +> r)) (u +> (t +> s)) := P_d h1
  have h3 := root_step h2
  simpa only [u, d, t, append_cons, append_nil] using h3

inductive Frame : ℕ → ℕ → List Sym → Prop where
  | Frame0 : Frame 0 1 (d ++ d)
  | FrameS {a b : ℕ} {xs : List Sym} : Frame a b xs → Frame (a + b) (a * 2 + 1) (xs ++ w ^ a ++ d)

theorem Frame_phase {a b : ℕ} {xs : List Sym} (h : Frame a b xs) :
    (a = b ∧ a % 4 = 1) ∨ (b = a + 1 ∧ a % 2 = 0) := by
  induction h with
  | Frame0 => right; omega
  | FrameS _ ih =>
    rcases ih with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · right; omega
    · left; omega

theorem frame_step {a b : ℕ} {xs : List Sym} (hf : Frame a b xs) {r s : ListBlank Sym}
    (hs : Suffix a b r s) :
    (cfg (xs +> r)) [tm1]⊢⁺ (cfg (xs +> s)) := by
  induction hf generalizing r s with
  | Frame0 =>
    simpa only [append_assoc] using root_base hs
  | FrameS _ ih =>
    simpa only [List.append_assoc, append_assoc] using ih (column hs)

inductive Num : ℕ → ListBlank Sym → Prop where
  | Num0 : Num 0 default
  | Num00 (n : ℕ) {r : ListBlank Sym} : Num n r → Num (n * 2) ([0, 0] +> r)
  | Num10 (n : ℕ) {r : ListBlank Sym} : Num n r → Num (n * 2 + 1) (t +> r)

theorem carry_num_0 : SideRLs tm1 hc default (t +> default) :=
  sideRLs_c_spec tm1 (r := []) (r' := t) (T := 500) (by decide)

theorem P_num_0 : P 1 default ([0, 0, 1, 0] +> default) :=
  sideRLs_c_spec tm1 (r := []) (r' := [0, 0, 1, 0]) (T := 500) (by decide)

theorem carry_num {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (1 + n) s ∧ SideRLs tm1 hc r s := by
  induction h with
  | Num0 => exact ⟨t +> default, .Num10 0 .Num0, carry_num_0⟩
  | Num00 n hn _ =>
    refine ⟨t +> _, ?_, carry0.sideRLs_concat (.nil _)⟩
    have : 1 + n * 2 = n * 2 + 1 := by omega
    rw [this]
    exact .Num10 n hn
  | Num10 n _ ih =>
    obtain ⟨s, hs, hc_s⟩ := ih
    refine ⟨[0, 0] +> s, ?_, carry1.sideRLs_concat hc_s⟩
    have : 1 + (n * 2 + 1) = (1 + n) * 2 := by omega
    rw [this]
    exact .Num00 (1 + n) hs

theorem I_num {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (1 + n) s ∧ I 1 r s := by
  obtain ⟨s, hs, hc_s⟩ := carry_num h
  exact ⟨s, hs, Icarry.sideRLs_concat hc_s⟩

theorem P_num {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (n + 2) s ∧ P 1 r s := by
  cases h with
  | Num0 =>
    exact ⟨[0, 0, 1, 0] +> default, .Num00 1 (.Num10 0 .Num0), P_num_0⟩
  | Num00 n hn =>
    obtain ⟨s, hs, hc_s⟩ := carry_num hn
    refine ⟨[0, 0] +> s, ?_, Pcarry0.sideRLs_concat hc_s⟩
    have : n * 2 + 2 = (1 + n) * 2 := by omega
    rw [this]
    exact .Num00 (1 + n) hs
  | Num10 n hn =>
    obtain ⟨s, hs, hc_s⟩ := carry_num hn
    refine ⟨t +> s, ?_, Pcarry1.sideRLs_concat hc_s⟩
    have : n * 2 + 1 + 2 = (1 + n) * 2 + 1 := by omega
    rw [this]
    exact .Num10 (1 + n) hs

theorem I_nums (k : ℕ) {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (n + k) s ∧ I k r s := by
  induction k generalizing n r with
  | zero => exact ⟨r, h, .nil _⟩
  | succ k ih =>
    obtain ⟨s, hs, h1⟩ := I_num h
    obtain ⟨z, hz, hk⟩ := ih hs
    refine ⟨z, ?_, ?_⟩
    · have : n + (k + 1) = 1 + n + k := by omega
      rwa [this]
    · have : k + 1 = 1 + k := by omega
      rw [this]
      exact I_add h1 hk

theorem P_nums (k : ℕ) {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (n + k * 2) s ∧ P k r s := by
  induction k generalizing n r with
  | zero => exact ⟨r, h, .nil _⟩
  | succ k ih =>
    obtain ⟨s, hs, h1⟩ := P_num h
    obtain ⟨z, hz, hk⟩ := ih hs
    refine ⟨z, ?_, ?_⟩
    · have : n + (k + 1) * 2 = n + 2 + k * 2 := by omega
      rwa [this]
    · have : k + 1 = 1 + k := by omega
      rw [this]
      exact P_add h1 hk

theorem G_nums (k : ℕ) {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (n + k * 2) s ∧ G k r s := by
  obtain ⟨s, hs, hp_s⟩ := P_nums k h
  exact ⟨s, hs, P_G hp_s⟩

inductive Word : ℕ → ℕ → List Sym → Prop where
  | Word0 : Word 0 0 [0, 1, 0]
  | Word1 : Word 0 1 d
  | Word00 (k n : ℕ) {xs : List Sym} : Word k n xs → Word (k + 1) (n * 2) ([0, 0] ++ xs)
  | Word10 (k n : ℕ) {xs : List Sym} : Word k n xs → Word (k + 1) (n * 2 + 1) (t ++ xs)

theorem Word_bound {k n : ℕ} {xs : List Sym} (h : Word k n xs) :
    n < 2 ^ (1 + k) := by
  induction h with
  | Word0 => decide
  | Word1 => decide
  | Word00 k n _ ih =>
    have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    omega
  | Word10 k n _ ih =>
    have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    omega

inductive Bin : ℕ → ℕ → List Sym → Prop where
  | Bin0 : Bin 0 0 [0]
  | Bin1 : Bin 0 1 [1]
  | Bin00 (k n : ℕ) {xs : List Sym} : Bin k n xs → Bin (k + 1) (n * 2) ([0, 0] ++ xs)
  | Bin10 (k n : ℕ) {xs : List Sym} : Bin k n xs → Bin (k + 1) (n * 2 + 1) (t ++ xs)

private theorem Bin_unique_aux {k n m : ℕ} {xs ys : List Sym}
    (h : Bin k n xs) (h' : Bin k m ys) (heq : n = m) : xs = ys := by
  induction h generalizing m ys with
  | Bin0 =>
    cases h' with
    | Bin0 => rfl
    | Bin1 => omega
  | Bin1 =>
    cases h' with
    | Bin0 => omega
    | Bin1 => rfl
  | Bin00 k n h_xs ih =>
    cases h' with
    | Bin00 _ n' h_ys =>
      rw [ih h_ys (by omega)]
    | Bin10 _ n' _ => omega
  | Bin10 k n h_xs ih =>
    cases h' with
    | Bin00 _ n' _ => omega
    | Bin10 _ n' h_ys =>
      rw [ih h_ys (by omega)]

theorem Bin_unique {k n : ℕ} {xs : List Sym} (h : Bin k n xs) {ys : List Sym} (h' : Bin k n ys) :
    xs = ys :=
  Bin_unique_aux h h' rfl

theorem Bin_bound {k n : ℕ} {xs : List Sym} (h : Bin k n xs) :
    n < 2 ^ (1 + k) := by
  induction h with
  | Bin0 => decide
  | Bin1 => decide
  | Bin00 k n _ ih =>
    have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    omega
  | Bin10 k n _ ih =>
    have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    omega

theorem Bin_zero (k : ℕ) : Bin k 0 ([0, 0] ^ k ++ [0]) := by
  induction k with
  | zero => exact .Bin0
  | succ k ih =>
    rw [Longitudinal.pow_succ_list, List.append_assoc]
    exact .Bin00 k 0 ih

theorem Bin_top (k : ℕ) : Bin k (2 ^ k) ([0, 0] ^ k ++ [1]) := by
  induction k with
  | zero => exact .Bin1
  | succ k ih =>
    have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    rw [Longitudinal.pow_succ_list, List.append_assoc, h2]
    exact .Bin00 k (2 ^ k) ih

theorem Bin_one {k : ℕ} (hk : 0 < k) : Bin k 1 ([1] ++ [0, 0] ^ k) := by
  rcases k with _ | k
  · omega
  · have h := Bin.Bin10 k 0 (Bin_zero k)
    have hrot : ([0, 0] : List Sym) ^ k ++ [0] = [0] ++ [0, 0] ^ k :=
      lpow_rotate_list ([0] : List Sym) [0] k
    have h_eq : t ++ ([0, 0] ^ k ++ [0]) = [1] ++ [0, 0] ^ (k + 1) := by
      change (1 : Sym) :: (0 :: ([0, 0] ^ k ++ [0])) = 1 :: ([0, 0] ++ [0, 0] ^ k)
      congr 1
      rw [hrot]
      rfl
    rwa [h_eq] at h

theorem Bin_inc {k n : ℕ} {xs : List Sym} (h : Bin k n xs) (hn : n + 1 < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + 1) ys ∧ SegRLs tm1 hc [] xs ys := by
  induction h with
  | Bin0 => exact ⟨[1], .Bin1, carry_bit0⟩
  | Bin1 => omega
  | Bin00 k n h_xs _ =>
    exact ⟨t ++ _, .Bin10 k n h_xs, carry0.concat (.nil _)⟩
  | Bin10 k n h_xs ih =>
    have hn' : n + 1 < 2 ^ (1 + k) := by
      have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
      omega
    obtain ⟨ys, hy, hc_y⟩ := ih hn'
    refine ⟨[0, 0] ++ ys, ?_, carry1.concat hc_y⟩
    have : n * 2 + 1 + 1 = (n + 1) * 2 := by omega
    rw [this]
    exact .Bin00 k (n + 1) hy

theorem I_Bin {k n : ℕ} {xs : List Sym} (h : Bin k n xs) (hn : n + 1 < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + 1) ys ∧ SegRLs tm1 hi [] xs ys := by
  obtain ⟨ys, hy, hc_y⟩ := Bin_inc h hn
  exact ⟨ys, hy, Icarry.concat hc_y⟩

theorem P_Bin {k n : ℕ} {xs : List Sym} (h : Bin k n xs) (hk : 0 < k) (hn : n + 2 < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + 2) ys ∧ SegRLs tm1 hp [] xs ys := by
  cases h with
  | Bin0 => omega
  | Bin1 => omega
  | Bin00 k' n' h_xs =>
    have hn' : n' + 1 < 2 ^ (1 + k') := by
      have : 2 ^ (1 + (k' + 1)) = 2 ^ (1 + k') * 2 := by ring
      omega
    obtain ⟨ys, hy, hc_y⟩ := Bin_inc h_xs hn'
    refine ⟨[0, 0] ++ ys, ?_, Pcarry0.concat hc_y⟩
    have : n' * 2 + 2 = (n' + 1) * 2 := by omega
    rw [this]
    exact .Bin00 k' (n' + 1) hy
  | Bin10 k' n' h_xs =>
    have hn' : n' + 1 < 2 ^ (1 + k') := by
      have : 2 ^ (1 + (k' + 1)) = 2 ^ (1 + k') * 2 := by ring
      omega
    obtain ⟨ys, hy, hc_y⟩ := Bin_inc h_xs hn'
    refine ⟨t ++ ys, ?_, Pcarry1.concat hc_y⟩
    have : n' * 2 + 1 + 2 = (n' + 1) * 2 + 1 := by omega
    rw [this]
    exact .Bin10 k' (n' + 1) hy

theorem Bin_repeat (h : List (DH0 Sym Q × DH0 Sym Q)) (s k : ℕ)
    (hstep : ∀ n xs, Bin k n xs → n + s < 2 ^ (1 + k) → ∃ ys, Bin k (n + s) ys ∧ SegRLs tm1 h [] xs ys)
    (i : ℕ) {n : ℕ} {xs : List Sym} (hw : Bin k n xs) (hn : n + i * s < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + i * s) ys ∧ SegRLs tm1 (h ^ i) [] xs ys := by
  induction i generalizing n xs with
  | zero => exact ⟨xs, by simpa using hw, .nil _⟩
  | succ i ih =>
    have hn1 : n + s < 2 ^ (1 + k) := by
      have : (i + 1) * s = s + i * s := by ring
      omega
    obtain ⟨ys, hy, h1⟩ := hstep n xs hw hn1
    have hn2 : (n + s) + i * s < 2 ^ (1 + k) := by
      have : (i + 1) * s = s + i * s := by ring
      omega
    obtain ⟨zs, hz, hi⟩ := ih hy hn2
    refine ⟨zs, ?_, ?_⟩
    · have : n + (i + 1) * s = n + s + i * s := by ring
      rwa [this]
    · rw [Longitudinal.pow_succ_list]
      exact h1.trans hi

theorem I_Bins {k : ℕ} (i : ℕ) {n : ℕ} {xs : List Sym} (hw : Bin k n xs) (hn : n + i < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + i) ys ∧ SegRLs tm1 (hi ^ i) [] xs ys := by
  have hn' : n + i * 1 < 2 ^ (1 + k) := by omega
  have hres := Bin_repeat hi 1 k (fun _ _ h hlt => I_Bin h hlt) i hw hn'
  simpa only [Nat.mul_one] using hres

theorem P_Bins {k : ℕ} (i : ℕ) {n : ℕ} {xs : List Sym} (hw : Bin k n xs) (hk : 0 < k)
    (hn : n + i * 2 < 2 ^ (1 + k)) :
    ∃ ys, Bin k (n + i * 2) ys ∧ SegRLs tm1 (hp ^ i) [] xs ys :=
  Bin_repeat hp 2 k (fun _ _ h hlt => P_Bin h hk hlt) i hw hn

theorem Word_inc {k n : ℕ} {xs : List Sym} (h : Word k n xs) (hn : n + 1 < 2 ^ (1 + k)) :
    ∃ ys, Word k (n + 1) ys ∧ SegRLs tm1 hc [] xs ys := by
  induction h with
  | Word0 => exact ⟨d, .Word1, carry_word0⟩
  | Word1 => omega
  | Word00 k n h_xs _ =>
    exact ⟨t ++ _, .Word10 k n h_xs, carry0.concat (.nil _)⟩
  | Word10 k n h_xs ih =>
    have hn' : n + 1 < 2 ^ (1 + k) := by
      have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
      omega
    obtain ⟨ys, hy, hc_y⟩ := ih hn'
    refine ⟨[0, 0] ++ ys, ?_, carry1.concat hc_y⟩
    have : n * 2 + 1 + 1 = (n + 1) * 2 := by omega
    rw [this]
    exact .Word00 k (n + 1) hy

theorem I_word_inc {k n : ℕ} {xs : List Sym} (r : ListBlank Sym)
    (h : Word k n xs) (hn : n + 1 < 2 ^ (1 + k)) :
    ∃ ys, Word k (n + 1) ys ∧ I 1 (xs +> r) (ys +> r) := by
  obtain ⟨ys, hy, hc_y⟩ := Word_inc h hn
  exact ⟨ys, hy, (Icarry.concat hc_y).sideRLs_concat (.nil _)⟩

def one : ℕ → List Sym
  | 0 => d
  | k + 1 => t ++ [0, 0] ^ k ++ [0, 1, 0]

theorem I_overflow_p (k : ℕ) {r s : ListBlank Sym} (h : P 1 r s) :
    I 1 (t ^ k +> (d +> r)) (one k +> s) := by
  rcases k with _ | k
  · exact Id.sideRLs_concat h
  · have hseg : SegRLs tm1 hi hp (t ++ (t ^ k ++ d)) (t ++ ([0, 0] ^ k ++ [0, 1, 0])) :=
      Iov_t.concat ((Mov_ts k).concat Mov_dp)
    have hres : I 1 ((t ++ (t ^ k ++ d)) +> r) ((t ++ ([0, 0] ^ k ++ [0, 1, 0])) +> s) :=
      hseg.sideRLs_concat h
    simpa only [one, Longitudinal.pow_succ_list, List.append_assoc, append_assoc] using hres

theorem I_overflow_q (k : ℕ) {r s : ListBlank Sym} (h : SideRLs tm1 hq r s) :
    I 1 (t ^ k +> (d +> r)) (one k +> ([1] +> s)) := by
  rcases k with _ | k
  · have hres : I 1 (d +> r) ((d ++ [1]) +> s) := Iq.sideRLs_concat h
    simpa only [one, Longitudinal.pow_zero_list, append_nil, append_assoc] using hres
  · have hseg : SegRLs tm1 hi hq (t ++ (t ^ k ++ d)) (t ++ ([0, 0] ^ k ++ [0, 1, 0, 1])) :=
      Iov_t.concat ((Mov_ts k).concat Mov_dq)
    have hres : I 1 ((t ++ (t ^ k ++ d)) +> r) ((t ++ ([0, 0] ^ k ++ [0, 1, 0, 1])) +> s) :=
      hseg.sideRLs_concat h
    simpa only [one, Longitudinal.pow_succ_list, List.append_assoc, append_assoc, append_cons, append_nil] using hres

theorem Q_overflow_p (k : ℕ) {r s : ListBlank Sym} (h : P 1 r s) :
    SideRLs tm1 hq ([0, 0] +> (t ^ k +> (d +> r))) ([0, 0] ^ (1 + k) +> (t +> s)) := by
  have hseg : SegRLs tm1 hq hp ([0, 0] ++ (t ^ k ++ d)) ([0] ++ ([0, 0] ^ k ++ [0, 1, 0])) :=
    Qov_00.concat ((Mov_ts k).concat Mov_dp)
  rw [zero_pair_shift k t] at hseg
  have hres := hseg.sideRLs_concat h
  simpa only [append_assoc] using hres

theorem Q_overflow_q (k : ℕ) {r s : ListBlank Sym} (h : SideRLs tm1 hq r s) :
    SideRLs tm1 hq ([0, 0] +> (t ^ k +> (d +> r))) ([0, 0] ^ (1 + k) +> (t +> ([1] +> s))) := by
  have hseg : SegRLs tm1 hq hq ([0, 0] ++ (t ^ k ++ d)) ([0] ++ ([0, 0] ^ k ++ [0, 1, 0, 1])) :=
    Qov_00.concat ((Mov_ts k).concat Mov_dq)
  rw [zero_pair_shift k [1, 0, 1]] at hseg
  have hres := hseg.sideRLs_concat h
  simpa only [append_assoc, append_cons, append_nil] using hres

theorem Q_R {r s : ListBlank Sym} (h : SideRLs tm1 hq r ([0, 0] +> s)) :
    SideRLs tm1 hr r s := by
  refine .cons (fun l => ?_) (.nil _)
  have h1 := h.elim_single l
  simpa only [toDHCfg, append_assoc, append_cons, append_nil] using h1

theorem P_d_second_Q {r x s : ListBlank Sym} (hp1 : P 1 r x) (hq1 : SideRLs tm1 hq x s) :
    P 1 (d +> r) ([1, 0, 0, 0] +> s) :=
  PdQP.sideRLs_concat (hp1.trans hq1)

theorem G_zero0_raw : P 1 (d +> default) ((t ++ one 2) +> default) :=
  sideRLs_c_spec tm1 (r := d) (r' := t ++ one 2) (T := 500) (by decide)

theorem G_zero0 : G1 (d +> default) ((t ++ one 2) +> default) :=
  .GP G_zero0_raw

theorem G_zero1_raw : P 1 ((d ++ t) +> default) ((w ++ [0, 0, 1, 0]) +> default) :=
  sideRLs_c_spec tm1 (r := d ++ t) (r' := w ++ [0, 0, 1, 0]) (T := 500) (by decide)

theorem G_zero1 : G1 (d +> (t +> default)) (w +> ([0, 0, 1, 0] +> default)) := by
  have h := G1.GP G_zero1_raw
  simpa only [append_assoc] using h



theorem pow2_succ_right (k : ℕ) : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
theorem pow2_succ_left (k : ℕ) : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
theorem pow2_1_succ (k : ℕ) : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
theorem pow2_pos (k : ℕ) : 0 < 2 ^ k := Nat.pos_of_ne_zero (by positivity)

theorem Q_overflow (k : ℕ) {r s : ListBlank Sym} (h : G1 r s) :
    SideRLs tm1 hq ([0, 0] +> (t ^ k +> (d +> r))) ([0, 0] ^ (1 + k) +> (t +> s)) := by
  cases h with
  | GP hp1 => exact Q_overflow_p k hp1
  | GQ hq1 => exact Q_overflow_q k hq1

theorem Word_zero (k : ℕ) : Word k 0 ([0, 0] ^ k ++ [0, 1, 0]) := by
  induction k with
  | zero => exact .Word0
  | succ k ih =>
    rw [Longitudinal.pow_succ_list, List.append_assoc]
    exact .Word00 k 0 ih

theorem Word_one (k : ℕ) : Word k 1 (one k) := by
  rcases k with _ | k
  · exact .Word1
  · simp only [one, List.append_assoc]
    exact .Word10 k 0 (Word_zero k)

theorem Word_max {k n : ℕ} {xs : List Sym} (h : Word k n xs) (hn : n + 1 = 2 ^ (1 + k)) :
    xs = t ^ k ++ d := by
  induction h with
  | Word0 => omega
  | Word1 => rfl
  | Word00 k n _ _ =>
    have := pow2_1_succ k
    omega
  | Word10 k n h_xs ih =>
    have h_p := pow2_1_succ k
    have hn' : n + 1 = 2 ^ (1 + k) := by omega
    rw [Longitudinal.pow_succ_list, List.append_assoc, ih hn']

theorem Word_before_Q {k n : ℕ} {xs : List Sym}
    (h : Word (k + 1) n xs) (he : n + 2 = 2 ^ (2 + k)) :
    xs = [0, 0] ++ t ^ k ++ d := by
  have hp1 : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
  cases h with
  | Word00 _ n' hy =>
    rw [Word_max hy (by omega), List.append_assoc]
  | Word10 _ n' _ => omega

theorem I_overflow (k : ℕ) {r s : ListBlank Sym} (h : G1 r s) :
    I 1 (t ^ k +> (d +> r)) (one k +> s) := by
  cases h with
  | GP hp1 => exact I_overflow_p k hp1
  | GQ hq1 => exact I_overflow_q k hq1

theorem P_word_inc {k n : ℕ} {xs : List Sym} (r : ListBlank Sym)
    (h : Word k n xs) (hk : 0 < k) (hn : n + 2 < 2 ^ (1 + k)) :
    ∃ ys, Word k (n + 2) ys ∧ P 1 (xs +> r) (ys +> r) := by
  cases h with
  | Word0 => omega
  | Word1 => omega
  | Word00 k' n' h_xs =>
    have hn' : n' + 1 < 2 ^ (1 + k') := by
      have := pow2_1_succ k'
      omega
    obtain ⟨ys, hy, hc_y⟩ := Word_inc h_xs hn'
    refine ⟨[0, 0] ++ ys, ?_, (Pcarry0.concat hc_y).sideRLs_concat (.nil _)⟩
    have : n' * 2 + 2 = (n' + 1) * 2 := by omega
    rw [this]
    exact .Word00 k' (n' + 1) hy
  | Word10 k' n' h_xs =>
    have hn' : n' + 1 < 2 ^ (1 + k') := by
      have := pow2_1_succ k'
      omega
    obtain ⟨ys, hy, hc_y⟩ := Word_inc h_xs hn'
    refine ⟨t ++ ys, ?_, (Pcarry1.concat hc_y).sideRLs_concat (.nil _)⟩
    have : n' * 2 + 1 + 2 = (n' + 1) * 2 + 1 := by omega
    rw [this]
    exact .Word10 k' (n' + 1) hy

theorem P_word_linear {k : ℕ} (i : ℕ) {n : ℕ} {xs : List Sym} (r : ListBlank Sym)
    (hw : Word k n xs) (hk : 0 < k) (hbound : n + i * 2 < 2 ^ (1 + k)) :
    ∃ ys, Word k (n + i * 2) ys ∧ P i (xs +> r) (ys +> r) := by
  induction i generalizing n xs with
  | zero => exact ⟨xs, by simpa using hw, .nil _⟩
  | succ i ih =>
    have hb1 : n + 2 < 2 ^ (1 + k) := by omega
    obtain ⟨ys, hy, hp1⟩ := P_word_inc r hw hk hb1
    have hb2 : (n + 2) + i * 2 < 2 ^ (1 + k) := by omega
    obtain ⟨zs, hz, hrest⟩ := ih hy hb2
    refine ⟨zs, ?_, ?_⟩
    · have : n + (i + 1) * 2 = n + 2 + i * 2 := by omega
      rwa [this]
    · have : i + 1 = 1 + i := by omega
      rw [this]
      exact P_add hp1 hrest

theorem G_word_odd (k : ℕ) {r s : ListBlank Sym} (h : G1 r s) :
    G1 (t ^ (1 + k) +> (d +> r)) ((t ++ one k) +> s) := by
  have h1 : t ^ (1 + k) +> (d +> r) = t +> (t ^ k +> (d +> r)) := by
    have : 1 + k = k + 1 := by omega
    rw [this, Longitudinal.pow_succ_list, append_assoc]
  rw [h1, append_assoc]
  exact .GP (P_t 1 (I_overflow k h))

theorem G_word_even (k : ℕ) {r s : ListBlank Sym} (h : G1 r s) :
    G1 ([0, 0] +> (t ^ k +> (d +> r))) (one (k + 1) +> s) := by
  have hq_ov := Q_overflow k h
  have hgq := G1.GQ hq_ov
  have h_eq : ([1] : List Sym) +> ([0, 0] ^ (1 + k) +> (t +> s)) = one (k + 1) +> s := by
    have hrot : ([0, 0] : List Sym) ^ k ++ [0] = [0] ++ [0, 0] ^ k :=
      lpow_rotate_list ([0] : List Sym) [0] k
    have h_list : ([1] : List Sym) ++ [0, 0] ^ (1 + k) ++ t = one (k + 1) := by
      have : 1 + k = k + 1 := by omega
      rw [this, Longitudinal.pow_succ_list, one]
      change (1 : Sym) :: 0 :: (0 :: [0, 0] ^ k ++ t) = 1 :: 0 :: ([0, 0] ^ k ++ [0, 1, 0])
      congr 2
      have h2 : (0 : Sym) :: [0, 0] ^ k ++ t = ([0] ++ [0, 0] ^ k) ++ t := rfl
      rw [h2, ← hrot, List.append_assoc]
      rfl
    rw [← h_list]
    simp only [List.append_assoc, append_assoc]
  rwa [h_eq] at hgq

theorem G_split (a b : ℕ) {r s : ListBlank Sym} (h : G (a + b) r s) :
    ∃ z, G a r z ∧ G b z s := by
  induction a generalizing r with
  | zero => exact ⟨r, .G0 r, by simpa using h⟩
  | succ a ih =>
    have h' : G ((a + b) + 1) r s := by
      have : (a + b) + 1 = a + 1 + b := by omega
      rwa [this]
    cases h' with
    | GS h1 hn =>
      obtain ⟨z', ha, hb⟩ := ih hn
      exact ⟨z', .GS h1 ha, hb⟩

theorem G_single {r s : ListBlank Sym} (h : G1 r s) : G 1 r s :=
  .GS h (.G0 s)

theorem G_unone {r s : ListBlank Sym} (h : G 1 r s) : G1 r s := by
  cases h with
  | GS h1 hn =>
    cases hn
    exact h1

inductive ICounter (k : ℕ) : ℕ → ℕ → ℕ → Prop where
  | ICinc (n : ℕ) : n + 1 < 2 ^ (1 + k) → ICounter k n (n + 1) 0
  | ICov (n : ℕ) : n + 1 = 2 ^ (1 + k) → ICounter k n 1 1

theorem I_counter {k n n' c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hc : ICounter k n n' c) (hg : G c r s) :
    ∃ ys, Word k n' ys ∧ I 1 (xs +> r) (ys +> s) := by
  cases hc with
  | ICinc hn =>
    cases hg
    exact I_word_inc r hw hn
  | ICov hn =>
    refine ⟨one k, Word_one k, ?_⟩
    rw [Word_max hw hn, append_assoc]
    exact I_overflow k (G_unone hg)

inductive GCounter (k : ℕ) : ℕ → ℕ → ℕ → Prop where
  | GCinc (n : ℕ) : n + 2 < 2 ^ (1 + k) → GCounter k n (n + 2) 0
  | GCev (n : ℕ) : n + 2 = 2 ^ (1 + k) → GCounter k n 1 1
  | GCod (n : ℕ) : n + 1 = 2 ^ (1 + k) → GCounter k n 3 1

theorem G_counter {k n n' c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hk : 0 < k) (hc : GCounter k n n' c) (hg : G c r s) :
    ∃ ys, Word k n' ys ∧ G1 (xs +> r) (ys +> s) := by
  cases hc with
  | GCinc hn =>
    cases hg
    obtain ⟨ys, hy, hp1⟩ := P_word_inc r hw hk hn
    exact ⟨ys, hy, .GP hp1⟩
  | GCev hn =>
    cases hw with
    | Word0 => omega
    | Word1 => omega
    | Word00 k' n' hw' =>
      have hp := pow2_1_succ k'
      have en : n' + 1 = 2 ^ (1 + k') := by omega
      refine ⟨one (k' + 1), Word_one (k' + 1), ?_⟩
      rw [Word_max hw' en]
      simpa only [List.append_assoc, append_assoc] using G_word_even k' (G_unone hg)
    | Word10 k' n' _ =>
      have hp := pow2_1_succ k'
      omega
  | GCod hn =>
    rcases k with _ | k'
    · omega
    · refine ⟨t ++ one k', .Word10 k' 1 (Word_one k'), ?_⟩
      rw [Word_max hw hn, append_assoc]
      have h_k : 1 + k' = k' + 1 := by omega
      rw [← h_k]
      exact G_word_odd k' (G_unone hg)

theorem GCounter_odd {k n m c : ℕ} (h : GCounter k n m c) (hn : n % 2 = 1) :
    m % 2 = 1 := by
  cases h <;> omega

theorem P_counter {k n n' c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hk : 0 < k) (hodd : n % 2 = 1)
    (hc : GCounter k n n' c) (hg : G c r s) :
    ∃ ys, Word k n' ys ∧ P 1 (xs +> r) (ys +> s) := by
  cases hc with
  | GCinc hn =>
    cases hg
    exact P_word_inc r hw hk hn
  | GCev hn =>
    rcases k with _ | k'
    · omega
    · have hp := pow2_1_succ k'
      omega
  | GCod hn =>
    rcases k with _ | k'
    · omega
    · refine ⟨t ++ one k', .Word10 k' 1 (Word_one k'), ?_⟩
      rw [Word_max hw hn, Longitudinal.pow_succ_list, List.append_assoc, append_assoc, append_assoc]
      exact P_t 1 (I_overflow k' (G_unone hg))

inductive CounterRun (step : ℕ → ℕ → ℕ → Prop) : ℕ → ℕ → ℕ → ℕ → Prop where
  | Counter0 (n : ℕ) : CounterRun step 0 n n 0
  | CounterS {i n m z c d : ℕ} : step n m c → CounterRun step i m z d →
      CounterRun step (i + 1) n z (c + d)

theorem CounterRun_split {step : ℕ → ℕ → ℕ → Prop} (i j : ℕ) {n m c : ℕ}
    (h : CounterRun step (i + j) n m c) :
    ∃ z c₀ c₁, c = c₀ + c₁ ∧ CounterRun step i n z c₀ ∧ CounterRun step j z m c₁ := by
  induction i generalizing n c with
  | zero => exact ⟨n, 0, c, by omega, .Counter0 n, by simpa using h⟩
  | succ i ih =>
    have h' : CounterRun step ((i + j) + 1) n m c := by
      have : (i + j) + 1 = i + 1 + j := by omega
      rwa [this]
    cases h' with
    | @CounterS _ _ m' _ c₀ d h0 h1 =>
      obtain ⟨x, c₂, c₃, he, h2, h3⟩ := ih h1
      exact ⟨x, c₀ + c₂, c₃, by omega, .CounterS h0 h2, h3⟩

theorem CounterRun_add {step : ℕ → ℕ → ℕ → Prop} {i j n m z c e : ℕ}
    (h1 : CounterRun step i n m c) (h2 : CounterRun step j m z e) :
    CounterRun step (i + j) n z (c + e) := by
  induction h1 with
  | Counter0 _ => simpa using h2
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    have h_i : i' + 1 + j = (i' + j) + 1 := by omega
    have h_c : c' + d' + e = c' + (d' + e) := by omega
    rw [h_i, h_c]
    exact .CounterS hs (ih h2)

theorem I_counter_run {k i n m c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hc : CounterRun (ICounter k) i n m c) (hg : G c r s) :
    ∃ ys, Word k m ys ∧ I i (xs +> r) (ys +> s) := by
  induction hc generalizing xs r s with
  | Counter0 _ =>
    cases hg
    exact ⟨xs, hw, .nil _⟩
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    obtain ⟨z_r, hg1, hd⟩ := G_split c' d' hg
    obtain ⟨ys, hy, hi1⟩ := I_counter hw hs hg1
    obtain ⟨zs, hz, hrest⟩ := ih hy hd
    have : i' + 1 = 1 + i' := by omega
    rw [this]
    exact ⟨zs, hz, I_add hi1 hrest⟩

theorem G_counter_run {k i n m c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hk : 0 < k) (hc : CounterRun (GCounter k) i n m c) (hg : G c r s) :
    ∃ ys, Word k m ys ∧ G i (xs +> r) (ys +> s) := by
  induction hc generalizing xs r s with
  | Counter0 _ =>
    cases hg
    exact ⟨xs, hw, .G0 _⟩
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    obtain ⟨z_r, hg1, hd⟩ := G_split c' d' hg
    obtain ⟨ys, hy, hg_step⟩ := G_counter hw hk hs hg1
    obtain ⟨zs, hz, hrest⟩ := ih hy hd
    exact ⟨zs, hz, .GS hg_step hrest⟩

theorem P_counter_run {k i n m c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hk : 0 < k) (hodd : n % 2 = 1)
    (hc : CounterRun (GCounter k) i n m c) (hg : G c r s) :
    ∃ ys, Word k m ys ∧ P i (xs +> r) (ys +> s) := by
  induction hc generalizing xs r s with
  | Counter0 _ =>
    cases hg
    exact ⟨xs, hw, .nil _⟩
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    obtain ⟨z_r, hg1, hd⟩ := G_split c' d' hg
    obtain ⟨ys, hy, hp1⟩ := P_counter hw hk hodd hs hg1
    obtain ⟨zs, hz, hrest⟩ := ih hy (GCounter_odd hs hodd) hd
    have : i' + 1 = 1 + i' := by omega
    rw [this]
    exact ⟨zs, hz, P_add hp1 hrest⟩

theorem ICounter_total (k n : ℕ) (h : n < 2 ^ (1 + k)) :
    ∃ m c, ICounter k n m c ∧ m < 2 ^ (1 + k) := by
  by_cases hlt : n + 1 < 2 ^ (1 + k)
  · exact ⟨n + 1, 0, .ICinc n hlt, hlt⟩
  · have hp := pow2_pos k
    have : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
    exact ⟨1, 1, .ICov n (by omega), by omega⟩

theorem GCounter_total (k n : ℕ) (hk : 0 < k) (h : n < 2 ^ (1 + k)) :
    ∃ m c, GCounter k n m c ∧ m < 2 ^ (1 + k) := by
  by_cases hlt : n + 2 < 2 ^ (1 + k)
  · exact ⟨n + 2, 0, .GCinc n hlt, hlt⟩
  · by_cases heq : n + 2 = 2 ^ (1 + k)
    · have hp := pow2_pos k
      have : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
      exact ⟨1, 1, .GCev n heq, by omega⟩
    · rcases k with _ | k'
      · omega
      · have hp := pow2_pos k'
        have : 2 ^ (1 + (k' + 1)) = 2 ^ k' * 4 := by ring
        exact ⟨3, 1, .GCod n (by omega), by omega⟩

theorem CounterRun_total {step : ℕ → ℕ → ℕ → Prop} {bound : ℕ}
    (hstep : ∀ n, n < bound → ∃ m c, step n m c ∧ m < bound)
    (i n : ℕ) (hn : n < bound) :
    ∃ m c, CounterRun step i n m c ∧ m < bound := by
  induction i generalizing n with
  | zero => exact ⟨n, 0, .Counter0 n, hn⟩
  | succ i ih =>
    obtain ⟨m, c, hc, hm⟩ := hstep n hn
    obtain ⟨z, d, hd, hz⟩ := ih m hm
    exact ⟨z, c + d, .CounterS hc hd, hz⟩

inductive Tail : ListBlank Sym → Prop where
  | TailNum {n : ℕ} {r : ListBlank Sym} : Num n r → Tail r
  | TailWord {k n : ℕ} {xs : List Sym} {r : ListBlank Sym} :
      0 < k → Word k n xs → Tail r → Tail (xs +> r)

theorem G_total {r : ListBlank Sym} (ht : Tail r) (i : ℕ) :
    ∃ s, Tail s ∧ G i r s := by
  induction ht generalizing i with
  | TailNum hn =>
    obtain ⟨s, hs, hg⟩ := G_nums i hn
    exact ⟨s, .TailNum hs, hg⟩
  | @TailWord k n xs r' hk hw _ ih =>
    obtain ⟨m, c, hc, _⟩ := CounterRun_total (fun z hz => GCounter_total k z hk hz) i n (Word_bound hw)
    obtain ⟨s, hs, hg⟩ := ih c
    obtain ⟨ys, hy, hrun⟩ := G_counter_run hw hk hc hg
    exact ⟨ys +> s, .TailWord hk hy hs, hrun⟩

theorem I_total {r : ListBlank Sym} (ht : Tail r) (i : ℕ) :
    ∃ s, Tail s ∧ I i r s := by
  cases ht with
  | TailNum hn =>
    obtain ⟨s, hs, hi⟩ := I_nums i hn
    exact ⟨s, .TailNum hs, hi⟩
  | @TailWord k n xs r' hk hw htail =>
    obtain ⟨m, c, hc, _⟩ := CounterRun_total (ICounter_total k) i n (Word_bound hw)
    obtain ⟨s, hs, hg⟩ := G_total htail c
    obtain ⟨ys, hy, hrun⟩ := I_counter_run hw hc hg
    exact ⟨ys +> s, .TailWord hk hy hs, hrun⟩

theorem ICounter_balance {k n m c : ℕ} (h : ICounter k n m c) :
    m + c * (2 ^ (1 + k) - 1) = n + 1 := by
  cases h <;> omega

theorem ICounterRun_balance {k i n m c : ℕ} (h : CounterRun (ICounter k) i n m c) :
    m + c * (2 ^ (1 + k) - 1) = n + i := by
  induction h with
  | Counter0 _ => omega
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    have hb := ICounter_balance hs
    have : (c' + d') * (2 ^ (1 + k) - 1) = c' * (2 ^ (1 + k) - 1) + d' * (2 ^ (1 + k) - 1) := by ring
    omega

theorem ICounterRun_positive {k i n m c : ℕ} (h : CounterRun (ICounter k) i n m c) (hn : 0 < n) :
    0 < m := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih =>
    apply ih
    cases hs <;> omega

theorem ICounterRun_bound {k i n m c : ℕ} (h : CounterRun (ICounter k) i n m c)
    (hn : n < 2 ^ (1 + k)) : m < 2 ^ (1 + k) := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih =>
    apply ih
    cases hs with
    | ICinc hlt => exact hlt
    | ICov _ =>
      have hp := pow2_pos k
      have : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
      omega

theorem ICounterRun_linear {k i n m c : ℕ} (h : CounterRun (ICounter k) i n m c)
    (hbound : n + i < 2 ^ (1 + k)) : m = n + i ∧ c = 0 := by
  induction h with
  | Counter0 _ => omega
  | CounterS hs _ ih =>
    cases hs <;> omega

def phi (n : ℕ) : ℕ := n + n % 2 - 1

theorem phi_odd (n : ℕ) : phi (n * 2 + 1) = n * 2 + 1 := by
  unfold phi; omega

theorem phi_bounds {n : ℕ} (hn : 0 < n) :
    0 < phi n ∧ phi n ≤ n ∧ n ≤ phi n + 1 := by
  unfold phi; omega

theorem GCounter_positive {k n m c : ℕ} (h : GCounter k n m c) : 0 < m := by
  cases h <;> omega

theorem GCounter_balance {k n m c : ℕ} (hk : 0 < k) (hn : 0 < n) (h : GCounter k n m c) :
    phi m + c * ((2 ^ k - 1) * 2) = phi n + 2 := by
  have hp := pow2_pos k
  have hp2 : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
  cases h <;> unfold phi <;> omega

theorem GCounterRun_balance {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hk : 0 < k) (hn : 0 < n) :
    phi m + c * ((2 ^ k - 1) * 2) = phi n + i * 2 := by
  induction h with
  | Counter0 _ => omega
  | @CounterS i' n' m' z' c' d' hs _ ih =>
    have hb := GCounter_balance hk hn hs
    have ih_res := ih (GCounter_positive hs)
    have : (c' + d') * ((2 ^ k - 1) * 2) = c' * ((2 ^ k - 1) * 2) + d' * ((2 ^ k - 1) * 2) := by ring
    omega

theorem GCounterRun_positive {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c) (hn : 0 < n) :
    0 < m := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih => exact ih (GCounter_positive hs)

theorem GCounterRun_linear {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hbound : n + i * 2 < 2 ^ (1 + k)) : m = n + i * 2 ∧ c = 0 := by
  induction h with
  | Counter0 _ => omega
  | CounterS hs _ ih =>
    cases hs <;> omega

theorem GCounterRun_even {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hm : m % 2 = 0) : c = 0 ∧ m = n + i * 2 ∧ n % 2 = 0 := by
  induction h with
  | Counter0 _ => omega
  | CounterS hs _ ih =>
    obtain ⟨hc, hz, hn'⟩ := ih hm
    cases hs <;> omega

theorem GCounterRun_bound {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hk : 0 < k) (hn : n < 2 ^ (1 + k)) : m < 2 ^ (1 + k) := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih =>
    apply ih
    cases hs with
    | GCinc hlt => exact hlt
    | GCev _ =>
      have hp := pow2_pos k
      have : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
      omega
    | GCod _ =>
      rcases k with _ | k'
      · omega
      · have hp := pow2_pos k'
        have : 2 ^ (1 + (k' + 1)) = 2 ^ k' * 4 := by ring
        omega

theorem GCounterRun_saturated {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hk : 0 < k) (hn : n < 2 ^ (1 + k)) (hi : 2 ^ (1 + k) ≤ n + i * 2) :
    m % 2 = 1 := by
  have hb := GCounterRun_bound h hk hn
  by_cases he : m % 2 = 0
  · obtain ⟨_, h_eq, _⟩ := GCounterRun_even h he
    omega
  · omega

theorem GCounterRun_odd {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c) (hn : n % 2 = 1) :
    m % 2 = 1 := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih => exact ih (GCounter_odd hs hn)

theorem GCounterRun_three {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    (hi : 0 < i) (hn : n % 2 = 1) : 3 ≤ m := by
  induction h with
  | Counter0 _ => omega
  | @CounterS i' n' m' z' c' d' hs hrest ih =>
    rcases i' with _ | i''
    · cases hrest
      have hp := pow2_pos k
      have : 2 ^ (1 + k) = 2 ^ k * 2 := pow2_succ_left k
      cases hs <;> omega
    · exact ih (by omega) (GCounter_odd hs hn)

theorem counter_inner {k j n m c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word k n xs) (hk : 0 < k) (hguard : n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + j * 4)
    (hc : CounterRun (GCounter k) (j * 2 + 2) n m c) (hg : G c r s) :
    ∃ ys, Word k m ys ∧ Inner j (xs +> r) (ys +> s) := by
  rcases hguard with hodd | hsat
  · obtain ⟨ys, hy, hp⟩ := P_counter_run hw hk hodd hc hg
    exact ⟨ys, hy, .InnerP hp⟩
  · obtain ⟨z, c₀, c₁, rfl, h0, h1⟩ := CounterRun_split (j * 2) 2 hc
    obtain ⟨r₀, hg0, hg1⟩ := G_split c₀ c₁ hg
    obtain ⟨zs, hz, hgz⟩ := G_counter_run hw hk h0 hg0
    have hodd : z % 2 = 1 :=
      GCounterRun_saturated h0 hk (Word_bound hw) (by omega)
    obtain ⟨ys, hy, hp⟩ := P_counter_run hz hk hodd h1 hg1
    have hj0 : 0 < j := by
      have hb := Word_bound hw
      omega
    exact ⟨ys, hy, .InnerG (zs +> r₀) hj0 hgz hp⟩

private theorem Word_odd_inv_aux {k1 m n : ℕ} {xs : List Sym}
    (h : Word k1 m xs) (hm : m = n * 2 + 1) :
    ∀ k, k1 = k + 1 → ∃ ys, Word k n ys ∧ xs = t ++ ys := by
  cases h with
  | Word0 => omega
  | Word1 =>
    intro k hk
    omega
  | Word00 k' n' _ => omega
  | Word10 k' n' hy =>
    intro k hk
    have hk_eq : k' = k := by omega
    have hn_eq : n' = n := by omega
    subst hk_eq hn_eq
    exact ⟨_, hy, rfl⟩

theorem Word_odd_inv {k n : ℕ} {xs : List Sym} (h : Word (k + 1) (n * 2 + 1) xs) :
    ∃ ys, Word k n ys ∧ xs = t ++ ys :=
  Word_odd_inv_aux h rfl k rfl

theorem counter_inner_phase {k j n m c : ℕ} (hk : 0 < k) (hn : n < 2 ^ (1 + k))
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + j * 4)
    (hc : CounterRun (GCounter k) (j * 2 + 2) n m c) :
    m % 2 = 1 ∧ 3 ≤ m := by
  rcases hguard with hodd | hsat
  · exact ⟨GCounterRun_odd hc hodd, GCounterRun_three hc (by omega) hodd⟩
  · obtain ⟨z, c₀, c₁, _, h0, h1⟩ := CounterRun_split (j * 2) 2 hc
    have hodd : z % 2 = 1 := GCounterRun_saturated h0 hk hn (by omega)
    exact ⟨GCounterRun_odd h1 hodd, GCounterRun_three h1 (by omega) hodd⟩

theorem descent_boundary {a b : ℕ} {fs : List Sym} {k n u_val z c₀ c₁ : ℕ}
    {xs : List Sym} {r s : ListBlank Sym}
    (hf : Frame a b fs) (hw : Word (k + 1) n xs) (hk : 0 < k)
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + (k + 1)) ≤ n + a * 4)
    (h0 : CounterRun (GCounter (k + 1)) (a * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter k) (b + a) u_val z c₁)
    (hg : G (c₀ + c₁) r s) :
    ∃ ys, Word k z ys ∧
      (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (ys +> s))) := by
  obtain ⟨r₀, hg0, hg1⟩ := G_split c₀ c₁ hg
  obtain ⟨xs₀, hw0, hin⟩ := counter_inner hw (by omega) hguard h0 hg0
  obtain ⟨ys₀, hy0, rfl⟩ := Word_odd_inv hw0
  obtain ⟨ys, hy, hrun⟩ := G_counter_run hy0 hk h1 hg1
  refine ⟨ys, hy, ?_⟩
  simp only [List.append_assoc, append_assoc]
  refine frame_step hf ?_
  have h_sub : a - a = 0 := by omega
  have hin' : Inner a (xs +> r) (t +> (ys₀ +> r₀)) := by
    simpa only [append_assoc] using hin
  have hgd : I (b + a) ([1] +> (t +> (ys₀ +> r₀))) (d +> (ys +> s)) := by
    simpa only [d, t, append_cons, append_nil] using G_d hrun
  exact inner_column (by omega) hin' hgd (by rw [h_sub]; exact .G0 _)

theorem descent_inside {a b j : ℕ} {fs : List Sym} {k n u_val x y z c₀ c₁ c₂ c₃ : ℕ}
    {xs : List Sym} {r s : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hw : Word (k + 2) n xs) (hk : 0 < k)
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + (k + 2)) ≤ n + j * 4) (hodd : x % 2 = 1)
    (h0 : CounterRun (GCounter (k + 2)) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter (k + 1)) (b + j) u_val x c₁)
    (h2 : CounterRun (GCounter (k + 1)) 2 x (y * 2 + 1) c₂)
    (h3 : CounterRun (GCounter k) (a - j - 1) y z c₃)
    (hg : G (c₀ + (c₁ + (c₂ + c₃))) r s) :
    ∃ ys, Word k z ys ∧
      (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (ys +> s)))) := by
  obtain ⟨r₀, hg0, hg'⟩ := G_split c₀ (c₁ + (c₂ + c₃)) hg
  obtain ⟨r₁, hg1, hg''⟩ := G_split c₁ (c₂ + c₃) hg'
  obtain ⟨r₂, hg2, hg3⟩ := G_split c₂ c₃ hg''
  obtain ⟨xs₀, hw0, hin⟩ := counter_inner hw (by omega) hguard h0 hg0
  obtain ⟨ys₀, hy0, rfl⟩ := Word_odd_inv (k := k + 1) hw0
  obtain ⟨xs₁, hw1, hrun1⟩ := G_counter_run hy0 (by omega) h1 hg1
  obtain ⟨xs₂, hw2, hrun2⟩ := P_counter_run hw1 (by omega) hodd h2 hg2
  obtain ⟨ys₂, hy2, rfl⟩ := Word_odd_inv (k := k) hw2
  obtain ⟨ys, hy, hrun3⟩ := G_counter_run hy2 hk h3 hg3
  refine ⟨ys, hy, ?_⟩
  rw [pow_add_list w j 1, pow_one_list, append_assoc]
  refine frame_step hf ?_
  have hin' : Inner j (xs +> r) (t +> (ys₀ +> r₀)) := by
    simpa only [append_assoc] using hin
  have hgd1 : I (b + j) ([1] +> (t +> (ys₀ +> r₀))) (d +> (xs₁ +> r₁)) := by
    simpa only [d, t, append_cons, append_nil] using G_d hrun1
  refine inner_column (by omega) hin' hgd1 ?_
  have h_aj : a - j = 1 + (a - j - 1) := by omega
  rw [h_aj]
  have hpd2 : G 1 (d +> (xs₁ +> r₁)) (w +> (ys₂ +> r₂)) := by
    have hp := P_d hrun2
    exact P_G (by simpa only [u, w, t, append_assoc, append_cons, append_nil] using hp)
  exact G_add hpd2 (P_G (G_w hrun3))

theorem descent_boundary_balance (a b k n u_val z c₀ c₁ q : ℕ)
    (hk : 0 < k) (hn : 0 < n) (hu : 0 < u_val)
    (h0 : CounterRun (GCounter (k + 1)) (a * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter k) (b + a) u_val z c₁) :
    (phi z + (2 ^ k - 1) * (q + (c₀ + c₁) * 2)) * 2 + 1 + q + c₀ * 2 + (u_val - phi u_val) * 2 =
      phi n + (2 ^ (k + 1) - 1) * q + (a * 2 + b + 1) * 4 := by
  have e0 := GCounterRun_balance h0 (by omega) hn
  have e1 := GCounterRun_balance h1 hk hu
  have hpu : phi u_val ≤ u_val := (phi_bounds hu).2.1
  rw [phi_odd] at e0
  have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hp01 : 1 ≤ 2 ^ (k + 1) := pow2_pos (k + 1)
  zify [hp0, hp01, hpu] at e0 e1 hp1 ⊢
  ring_nf at e0 e1 hp1 ⊢
  linarith

theorem descent_inside_balance (a b j k n u_val x y z c₀ c₁ c₂ c₃ q : ℕ)
    (hj : j < a) (hk : 0 < k) (hn : 0 < n) (hu : 0 < u_val) (hy : 0 < y)
    (h0 : CounterRun (GCounter (k + 2)) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter (k + 1)) (b + j) u_val x c₁)
    (h2 : CounterRun (GCounter (k + 1)) 2 x (y * 2 + 1) c₂)
    (h3 : CounterRun (GCounter k) (a - j - 1) y z c₃) :
    (phi z + (2 ^ k - 1) * (q + (c₀ + c₁ + c₂ + c₃) * 2)) * 4 +
      3 + q * 3 + c₀ * 6 + (c₁ + c₂) * 4 + (u_val - phi u_val) * 2 + (y - phi y) * 4 =
      phi n + (2 ^ (k + 2) - 1) * q + (a * 2 + b + 1) * 4 := by
  have e0 := GCounterRun_balance h0 (by omega) hn
  have e1 := GCounterRun_balance h1 (by omega) hu
  have e2 := GCounterRun_balance h2 (by omega) (GCounterRun_positive h1 hu)
  have e3 := GCounterRun_balance h3 hk hy
  have hpu : phi u_val ≤ u_val := (phi_bounds hu).2.1
  have hpy : phi y ≤ y := (phi_bounds hy).2.1
  have haj1 : 1 ≤ a - j := by omega
  have haj : j ≤ a := by omega
  rw [phi_odd] at e0 e2
  have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
  have hp2 : 2 ^ (k + 2) = 2 ^ k * 4 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hp01 : 1 ≤ 2 ^ (k + 1) := pow2_pos (k + 1)
  have hp02 : 1 ≤ 2 ^ (k + 2) := pow2_pos (k + 2)
  zify [hp0, hp01, hp02, hpu, hpy, haj1, haj] at e0 e1 e2 e3 hp1 hp2 ⊢
  ring_nf at e0 e1 e2 e3 hp1 hp2 ⊢
  linarith

theorem descent_boundary_calls (a b k n u_val z c₀ c₁ L : ℕ)
    (hk : 0 < k) (hn : 0 < n) (hu : 0 < u_val) (hz : 0 < z) (hzb : z < 2 ^ (1 + k)) (hL : 2 ≤ L)
    (hsize : (a * 2 + b + 1) * 4 = 2 ^ (2 + k) * L)
    (h0 : CounterRun (GCounter (k + 1)) (a * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter k) (b + a) u_val z c₁) :
    L ≤ c₀ + c₁ := by
  have e := descent_boundary_balance a b k n u_val z c₀ c₁ 0 hk hn hu h0 h1
  have hphi_n := phi_bounds hn
  have hphi_u := phi_bounds hu
  have hphi_z := phi_bounds hz
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  have hp2 : 2 ^ (2 + k) = 2 ^ k * 4 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hpu : phi u_val ≤ u_val := hphi_u.2.1
  by_contra hlt
  rcases hphi_n with ⟨hpn1, hpn2, hpn3⟩
  rcases hphi_u with ⟨hpu1, hpu2, hpu3⟩
  rcases hphi_z with ⟨hpz1, hpz2, hpz3⟩
  have h_gap : (2 ^ k * (c₀ + c₁ + 1)) * 4 + 2 ≤ (2 ^ k * L) * 4 + c₀ * 2 + c₁ * 4 := by
    by_cases hc : c₀ + c₁ = 0
    · have hle2 : c₀ + c₁ + 2 ≤ L := by omega
      have hmul2 := Nat.mul_le_mul_left (2 ^ k) hle2
      ring_nf at hmul2 ⊢
      omega
    · have hle1 : c₀ + c₁ + 1 ≤ L := by omega
      have hmul1 := Nat.mul_le_mul_left (2 ^ k) hle1
      ring_nf at hmul1 ⊢
      omega
  zify [hp0, hpu2] at hp0 e hpn1 hpu3 hpz2 hzb hp1 hp2 hsize h_gap
  ring_nf at e hzb hsize h_gap
  omega

theorem descent_inside_calls (a b j k n u_val x y z c₀ c₁ c₂ c₃ L : ℕ)
    (hj : j < a) (hk : 0 < k) (hn : 0 < n) (hu : 0 < u_val) (hy : 0 < y) (hz : 0 < z)
    (hzb : z < 2 ^ (1 + k)) (hL : 4 ≤ L)
    (hsize : (a * 2 + b + 1) * 4 = 2 ^ (3 + k) * L)
    (h0 : CounterRun (GCounter (k + 2)) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter (k + 1)) (b + j) u_val x c₁)
    (h2 : CounterRun (GCounter (k + 1)) 2 x (y * 2 + 1) c₂)
    (h3 : CounterRun (GCounter k) (a - j - 1) y z c₃) :
    L ≤ c₀ + c₁ + c₂ + c₃ := by
  have e := descent_inside_balance a b j k n u_val x y z c₀ c₁ c₂ c₃ 0 hj hk hn hu hy h0 h1 h2 h3
  have hphi_n := phi_bounds hn
  have hphi_u := phi_bounds hu
  have hphi_y := phi_bounds hy
  have hphi_z := phi_bounds hz
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  have hp3 : 2 ^ (3 + k) = 2 ^ k * 8 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hpu : phi u_val ≤ u_val := hphi_u.2.1
  have hpy : phi y ≤ y := hphi_y.2.1
  by_contra hlt
  rcases hphi_n with ⟨hpn1, hpn2, hpn3⟩
  rcases hphi_u with ⟨hpu1, hpu2, hpu3⟩
  rcases hphi_y with ⟨hpy1, hpy2, hpy3⟩
  rcases hphi_z with ⟨hpz1, hpz2, hpz3⟩
  have h_gap : (2 ^ k * (c₀ + c₁ + c₂ + c₃ + 1)) * 8 + 6 ≤
      (2 ^ k * L) * 8 + c₀ * 2 + (c₁ + c₂) * 4 + c₃ * 8 := by
    by_cases hc : c₀ + c₁ + c₂ + c₃ ≤ 2
    · have hle2 : c₀ + c₁ + c₂ + c₃ + 2 ≤ L := by omega
      have hmul2 := Nat.mul_le_mul_left (2 ^ k) hle2
      ring_nf at hmul2 ⊢
      omega
    · have hle1 : c₀ + c₁ + c₂ + c₃ + 1 ≤ L := by omega
      have hmul1 := Nat.mul_le_mul_left (2 ^ k) hle1
      ring_nf at hmul1 ⊢
      omega
  zify [hp0, hpu2, hpy2] at hp0 e hpn1 hpu3 hpy3 hpz2 hzb hp1 hp3 hsize h_gap
  ring_nf at e hzb hsize h_gap
  omega

theorem counter_inner_total (k j n : ℕ) (hk : 0 < k) (hn : n < 2 ^ (1 + k))
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + j * 4) :
    ∃ u_val c, 0 < u_val ∧ u_val < 2 ^ k ∧
      CounterRun (GCounter k) (j * 2 + 2) n (u_val * 2 + 1) c := by
  obtain ⟨m, c, hc, hm⟩ := CounterRun_total (fun z hz => GCounter_total k z hk hz) (j * 2 + 2) n hn
  obtain ⟨hodd, hthree⟩ := counter_inner_phase hk hn hguard hc
  have em : m = m / 2 * 2 + 1 := by omega
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  refine ⟨m / 2, c, by omega, by omega, ?_⟩
  rwa [← em]

theorem Num_zero {n : ℕ} {r : ListBlank Sym} (h : Num n r) (hn : n = 0) :
    r = default := by
  induction h with
  | Num0 => rfl
  | Num00 n' _ ih =>
    rw [ih (by omega)]
    exact all0_spec (a := [0, 0]) rfl
  | Num10 _ _ _ => omega

theorem Num_one {n : ℕ} {r : ListBlank Sym} (h : Num n r) (hn : n = 1) :
    r = t +> default := by
  cases h with
  | Num0 => omega
  | Num00 _ _ => omega
  | Num10 n' h' =>
    rw [Num_zero h' (by omega)]

inductive Value : ℕ → ListBlank Sym → Prop where
  | ValueNum {n : ℕ} {r : ListBlank Sym} : Num n r → Value n r
  | ValueEnd {n : ℕ} {r : ListBlank Sym} : Num n r → n ≤ 1 → Value (n * 2 + 1) (d +> r)
  | ValueWord {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym} :
      0 < k → 0 < n → Word k n xs → Value q r → Value (phi n + (2 ^ k - 1) * q) (xs +> r)

theorem G_value_one {r : ListBlank Sym} {q : ℕ} (h : Value q r) :
    ∃ s, Value (q + 2) s ∧ G1 r s := by
  induction h with
  | ValueNum hn =>
    obtain ⟨s, hs, hp⟩ := P_num hn
    exact ⟨s, .ValueNum hs, .GP hp⟩
  | @ValueEnd n r' hn hle =>
    by_cases hn0 : n = 0
    · rw [Num_zero hn hn0]
      subst hn0
      refine ⟨(t ++ one 2) +> default, ?_, G_zero0⟩
      exact Value.ValueWord (k := 3) (n := 3) (q := 0) (by decide) (by decide)
        (.Word10 2 1 (Word_one 2)) (.ValueNum .Num0)
    · have hn1 : n = 1 := by omega
      rw [Num_one hn hn1]
      subst hn1
      refine ⟨w +> ([0, 0, 1, 0] +> default), ?_, G_zero1⟩
      exact Value.ValueWord (k := 1) (n := 3) (q := 2) (by decide) (by decide)
        (.Word10 0 1 .Word1) (.ValueNum (.Num00 1 (.Num10 0 .Num0)))
  | @ValueWord k n xs q' r' hk hn0 hw hval ih =>
    obtain ⟨m, c, hc, hm⟩ := GCounter_total k n hk (Word_bound hw)
    have htail : ∃ s, Value (q' + c * 2) s ∧ G c r' s := by
      have hc_le : c ≤ 1 := by cases hc <;> omega
      rcases c with _ | _ | c
      · exact ⟨r', hval, .G0 r'⟩
      · obtain ⟨s, hs, hg⟩ := ih
        exact ⟨s, hs, G_single hg⟩
      · omega
    obtain ⟨s, hs, hg⟩ := htail
    obtain ⟨ys, hy, hrun⟩ := G_counter hw hk hc hg
    refine ⟨ys +> s, ?_, hrun⟩
    have hb := GCounter_balance hk hn0 hc
    have heq : phi n + (2 ^ k - 1) * q' + 2 = phi m + (2 ^ k - 1) * (q' + c * 2) := by
      have : (2 ^ k - 1) * (q' + c * 2) = (2 ^ k - 1) * q' + c * ((2 ^ k - 1) * 2) := by ring
      omega
    rw [heq]
    exact .ValueWord hk (GCounter_positive hc) hy hs

theorem G_value {r : ListBlank Sym} {q : ℕ} (h : Value q r) (i : ℕ) :
    ∃ s, Value (q + i * 2) s ∧ G i r s := by
  induction i generalizing r q with
  | zero => exact ⟨r, by simpa using h, .G0 r⟩
  | succ i ih =>
    obtain ⟨s, hs, h1⟩ := G_value_one h
    obtain ⟨z, hz, hi⟩ := ih hs
    refine ⟨z, ?_, .GS h1 hi⟩
    have : q + (i + 1) * 2 = q + 2 + i * 2 := by omega
    rwa [this]

theorem GCounterRun_one {i n m c : ℕ} (h : CounterRun (GCounter 1) (2 + i) n m c)
    (hn : 0 < n) (hbound : n < 4) :
    m = 3 ∧ i + 1 ≤ c ∧ c ≤ i + 2 := by
  have hm : m < 4 := GCounterRun_bound h (by decide) hbound
  have hthree : 3 ≤ m := by
    by_cases hodd : n % 2 = 1
    · exact GCounterRun_three h (by omega) hodd
    · have hn2 : n = 2 := by omega
      subst hn2
      have h' : CounterRun (GCounter 1) ((1 + i) + 1) 2 m c := by
        have : (1 + i) + 1 = 2 + i := by omega
        rwa [this]
      cases h' with
      | CounterS h0 h1 =>
        cases h0 with
        | GCinc hlt =>
          have : 2 ^ (1 + 1) = 4 := rfl
          omega
        | GCev _ =>
          exact GCounterRun_three h1 (by omega) rfl
        | GCod heq =>
          have : 2 ^ (1 + 1) = 4 := rfl
          omega
  have e := GCounterRun_balance h (by decide) hn
  have hm3 : m = 3 := by omega
  subst hm3
  unfold phi at e
  have : (2 ^ 1 - 1) * 2 = 2 := rfl
  omega

theorem narrow_inside (R : ℕ → ListBlank Sym → Prop)
    {a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hw : Word (k + 2) n xs) (hk : 0 < k) (hn : 0 < n)
    (hv : ∀ c, ∃ s, R c s ∧ G c r s)
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + (k + 2)) ≤ n + j * 4)
    (hB : 2 ^ (1 + k) ≤ b + j)
    (hcap : phi n + (2 ^ (k + 2) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ z c ys s,
      Word k z ys ∧ 0 < z ∧ R c s ∧ G c r s ∧
      phi z + (2 ^ k - 1) * (q + c * 2) < (a * 2 + b + 1) * 2 ∧
      (z % 2 = 0 → (a - j) * 2 ≤ z) ∧
      (k = 1 → 3 ≤ a - j → z = 3) ∧
      (∀ L, 4 ≤ L → (a * 2 + b + 1) * 4 = 2 ^ (3 + k) * L → L ≤ c) ∧
      (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (ys +> s)))) := by
  obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total (k + 2) j n (by omega) (Word_bound hw) hguard
  have hub' : u_val < 2 ^ (1 + (k + 1)) := by
    have : 1 + (k + 1) = k + 2 := by omega
    rwa [this]
  obtain ⟨x, c₁, h1, hxb⟩ := CounterRun_total (fun z hz => GCounter_total (k + 1) z (by omega) hz) (b + j) u_val hub'
  have hodd : x % 2 = 1 := by
    refine GCounterRun_saturated h1 (by omega) hub' ?_
    have : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    omega
  obtain ⟨y, c₂, hy, hyb, h2⟩ := counter_inner_total (k + 1) 0 x (by omega) hxb (Or.inl hodd)
  have hyb' : y < 2 ^ (1 + k) := by
    have : 1 + k = k + 1 := by omega
    rwa [this]
  obtain ⟨z, c₃, h3, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total k z' hk hz') (a - j - 1) y hyb'
  obtain ⟨s, hs, hg⟩ := hv (c₀ + (c₁ + (c₂ + c₃)))
  obtain ⟨ys, hys, hstep⟩ := descent_inside hf hj hw hk hguard hodd h0 h1 h2 h3 hg
  have hz_pos : 0 < z := GCounterRun_positive h3 hy
  refine ⟨z, c₀ + (c₁ + (c₂ + c₃)), ys, s, hys, hz_pos, hs, hg, ?_, ?_, ?_, ?_, hstep⟩
  · have e := descent_inside_balance a b j k n u_val x y z c₀ c₁ c₂ c₃ q hj hk hn hu hy h0 h1 h2 h3
    have hphi_u := phi_bounds hu
    have hphi_y := phi_bounds hy
    have h_assoc : c₀ + (c₁ + (c₂ + c₃)) = c₀ + c₁ + c₂ + c₃ := by omega
    rw [h_assoc]
    omega
  · intro heven
    obtain ⟨_, he, _⟩ := GCounterRun_even h3 heven
    omega
  · intro hk1 hU
    subst hk1
    have h3' : CounterRun (GCounter 1) (2 + (a - j - 3)) y z c₃ := by
      have : 2 + (a - j - 3) = a - j - 1 := by omega
      rwa [this]
    exact (GCounterRun_one h3' hy hyb').1
  · intro L hL hsize
    have hcalls := descent_inside_calls a b j k n u_val x y z c₀ c₁ c₂ c₃ L hj hk hn hu hy hz_pos hzb hL hsize h0 h1 h2 h3
    omega

theorem narrow_boundary (R : ℕ → ListBlank Sym → Prop)
    {a b : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a b fs) (hw : Word (k + 1) n xs) (hk : 0 < k) (hn : 0 < n)
    (hv : ∀ c, ∃ s, R c s ∧ G c r s)
    (hguard : n % 2 = 1 ∨ 2 ^ (1 + (k + 1)) ≤ n + a * 4)
    (hB : 2 ^ k ≤ b + a)
    (hcap : phi n + (2 ^ (k + 1) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ z c ys s,
      Word k z ys ∧ z % 2 = 1 ∧ R c s ∧ G c r s ∧
      phi z + (2 ^ k - 1) * (q + c * 2) < (a * 2 + b + 1) * 4 ∧
      (∀ L, 2 ≤ L → (a * 2 + b + 1) * 4 = 2 ^ (2 + k) * L → L ≤ c) ∧
      (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (ys +> s))) := by
  obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total (k + 1) a n (by omega) (Word_bound hw) hguard
  have hub' : u_val < 2 ^ (1 + k) := by
    have : 1 + k = k + 1 := by omega
    rwa [this]
  obtain ⟨z, c₁, h1, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total k z' hk hz') (b + a) u_val hub'
  obtain ⟨s, hs, hg⟩ := hv (c₀ + c₁)
  obtain ⟨ys, hys, hstep⟩ := descent_boundary hf hw hk hguard h0 h1 hg
  refine ⟨z, c₀ + c₁, ys, s, hys, ?_, hs, hg, ?_, ?_, hstep⟩
  · refine GCounterRun_saturated h1 hk hub' ?_
    have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    omega
  · have e := descent_boundary_balance a b k n u_val z c₀ c₁ q hk hn hu h0 h1
    have hphi_u := phi_bounds hu
    omega
  · intro L hL hsize
    exact descent_boundary_calls a b k n u_val z c₀ c₁ L hk hn hu (GCounterRun_positive h1 hu) hzb hL hsize h0 h1

theorem odd_d {k n m c : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word (k + 1) n xs) (hodd : n % 2 = 1)
    (hc : CounterRun (GCounter (k + 1)) 2 n (m * 2 + 1) c) (hg : G c r s) :
    ∃ ys, Word k m ys ∧ ∀ i z, G i (ys +> s) z → P (1 + i) (d +> (xs +> r)) (w +> z) := by
  obtain ⟨zs, hz, hp⟩ := P_counter_run hw (by omega) hodd hc hg
  obtain ⟨ys, hy, rfl⟩ := Word_odd_inv hz
  refine ⟨ys, hy, fun i z hrun => ?_⟩
  refine P_add (a := 1) (b := i) ?_ (G_w hrun)
  have hpd := P_d hp
  simpa only [u, w, t, append_assoc, append_cons, append_nil] using hpd

theorem odd_d_value (R : ℕ → ListBlank Sym → Prop)
    {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym} (i : ℕ)
    (hw : Word (k + 1) n xs) (hk : 0 < k) (hodd : n % 2 = 1)
    (hv : ∀ c, ∃ s, R (q + c * 2) s ∧ G c r s) :
    ∃ z c ys s,
      Word k z ys ∧ 0 < z ∧ R (q + c * 2) s ∧
      (phi z + (2 ^ k - 1) * (q + c * 2)) * 2 ≤ phi n + (2 ^ (k + 1) - 1) * q + 3 + i * 4 ∧
      (z % 2 = 0 → 2 + i * 2 ≤ z) ∧
      (k = 1 → 2 ≤ i → z = 3) ∧
      P (1 + i) (d +> (xs +> r)) (w +> (ys +> s)) ∧
      ∃ child, P 1 (d +> (xs +> r)) (w +> child) ∧ G i child (ys +> s) := by
  obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total (k + 1) 0 n (by omega) (Word_bound hw) (Or.inl hodd)
  have hub' : u_val < 2 ^ (1 + k) := by
    have : 1 + k = k + 1 := by omega
    rwa [this]
  obtain ⟨z, c₁, h1, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total k z' hk hz') i u_val hub'
  obtain ⟨s, hs, hg⟩ := hv (c₀ + c₁)
  obtain ⟨r₀, hg0, hg1⟩ := G_split c₀ c₁ hg
  obtain ⟨ys₀, hy0, hloop⟩ := odd_d hw hodd h0 hg0
  obtain ⟨ys, hy, hrun⟩ := G_counter_run hy0 hk h1 hg1
  refine ⟨z, c₀ + c₁, ys, s, hy, GCounterRun_positive h1 hu, hs, ?_, ?_, ?_, hloop i (ys +> s) hrun, ?_⟩
  · have hn0 : 0 < n := by omega
    have e0 := GCounterRun_balance h0 (by omega) hn0
    have e1 := GCounterRun_balance h1 hk hu
    have hphi_u := phi_bounds hu
    have hpu : phi u_val ≤ u_val := hphi_u.2.1
    rw [phi_odd] at e0
    have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    have hp0 : 1 ≤ 2 ^ k := pow2_pos k
    have hp01 : 1 ≤ 2 ^ (k + 1) := pow2_pos (k + 1)
    zify [hp0, hp01, hpu] at e0 e1 hp1 hphi_u ⊢
    ring_nf at e0 e1 hp1 ⊢
    linarith
  · intro heven
    obtain ⟨_, he, _⟩ := GCounterRun_even h1 heven
    omega
  · intro hk1 hi2
    subst hk1
    have h1' : CounterRun (GCounter 1) (2 + (i - 2)) u_val z c₁ := by
      have : 2 + (i - 2) = i := by omega
      rwa [this]
    exact (GCounterRun_one h1' hu hub').1
  · exact ⟨ys₀ +> r₀, hloop 0 (ys₀ +> r₀) (.G0 _), hrun⟩

theorem two_inside {a b j : ℕ} {fs : List Sym} {n u_val c₀ c₁ : ℕ}
    {xs : List Sym} {r s z : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hw : Word 2 n xs)
    (hguard : n % 2 = 1 ∨ 8 ≤ n + j * 4)
    (h0 : CounterRun (GCounter 2) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter 1) (b + j) u_val 3 c₁)
    (hg : G (c₀ + (c₁ + 2)) r s) (hz : G (a - j - 1) (d +> s) z) :
    (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> z))) := by
  obtain ⟨r₀, hg0, hg'⟩ := G_split c₀ (c₁ + 2) hg
  obtain ⟨r₁, hg1, hg2⟩ := G_split c₁ 2 hg'
  obtain ⟨xs₀, hw0, hin⟩ := counter_inner hw (by decide) hguard h0 hg0
  obtain ⟨ys₀, hy0, rfl⟩ := Word_odd_inv (k := 1) hw0
  obtain ⟨ys, hy, hrun⟩ := G_counter_run hy0 (by decide) h1 hg1
  have hy_eq : ys = w := Word_max hy rfl
  subst hy_eq
  rw [pow_add_list w j 1, pow_one_list, append_assoc]
  refine frame_step hf ?_
  have hin' : Inner j (xs +> r) (t +> (ys₀ +> r₀)) := by
    simpa only [append_assoc] using hin
  have hgd : I (b + j) ([1] +> (t +> (ys₀ +> r₀))) (d +> (w +> r₁)) := by
    simpa only [d, t, append_cons, append_nil] using G_d hrun
  refine inner_column (by omega) hin' hgd ?_
  have h_aj : a - j = 1 + (a - j - 1) := by omega
  rw [h_aj]
  have h1_step : G 1 (d +> (w +> r₁)) (w +> (d +> s)) := by
    have hp := P_d (G_w hg2)
    exact P_G (by simpa only [u, w, d, append_assoc, append_cons, append_nil] using hp)
  exact G_add h1_step (P_G (G_w hz))

theorem two_boundary {a b : ℕ} {fs : List Sym} {n u_val c₀ c₁ : ℕ}
    {xs : List Sym} {r s : ListBlank Sym}
    (hf : Frame a b fs) (hw : Word 2 n xs)
    (hguard : n % 2 = 1 ∨ 8 ≤ n + a * 4)
    (h0 : CounterRun (GCounter 2) (a * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter 1) (b + a) u_val 3 c₁)
    (hg : G (c₀ + c₁) r s) :
    (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (w +> s))) := by
  obtain ⟨ys, hy, hstep⟩ := descent_boundary (k := 1) hf hw (by decide) hguard h0 h1 hg
  rwa [Word_max hy rfl] at hstep

theorem one_boundary {a b : ℕ} {fs : List Sym} {n c : ℕ}
    {xs : List Sym} {r s z : ListBlank Sym}
    (hf : Frame a b fs) (hw : Word 1 n xs)
    (hguard : n % 2 = 1 ∨ 4 ≤ n + a * 4)
    (hc : CounterRun (GCounter 1) (a * 2 + 2) n 3 c)
    (hg : G c r s) (hz : G (b + a) (d +> s) z) :
    (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> z)) := by
  obtain ⟨ys, hy, hin⟩ := counter_inner hw (by decide) hguard hc hg
  have hy_eq : ys = w := Word_max hy rfl
  subst hy_eq
  simp only [List.append_assoc, append_assoc]
  refine frame_step hf ?_
  have hin' : Inner a (xs +> r) (w +> s) := hin
  have hgd : I (b + a) ([1] +> (w +> s)) (d +> z) := by
    simpa only [w, d, append_cons, append_nil] using G_d hz
  have h_sub : a - a = 0 := by omega
  exact inner_column (by omega) hin' hgd (by rw [h_sub]; exact .G0 _)

theorem counter_one_loop (i : ℕ) : CounterRun (GCounter 1) i 3 3 i := by
  induction i with
  | zero => exact .Counter0 3
  | succ i ih =>
    have h := CounterRun.CounterS (.GCod (k := 1) 3 rfl) ih
    rwa [Nat.add_comm 1 i] at h

theorem counter_one_start (i : ℕ) : CounterRun (GCounter 1) (i + 1) 1 3 i := by
  simpa using CounterRun.CounterS (.GCinc (k := 1) 1 (by decide)) (counter_one_loop i)

theorem one_neighbor {b j : ℕ} {fs xs : List Sym} {r s z out : ListBlank Sym}
    (hf : Frame (1 + j) b fs) (hw : Word 1 1 xs)
    (hg : G (j * 2 + 1) r s) (hz : G (b + j) (d +> s) (w +> z)) (hout : G 2 z out) :
    (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ (1 + j) ++ d) +> out)) := by
  have hc : CounterRun (GCounter 1) (j * 2 + 2) 1 3 (j * 2 + 1) :=
    counter_one_start (j * 2 + 1)
  obtain ⟨ys, hy, hin⟩ := counter_inner hw (by decide) (Or.inl rfl) hc hg
  have hy_eq : ys = w := Word_max hy rfl
  subst hy_eq
  have h_pow : w ^ (1 + j) = w ^ j ++ w := by
    rw [Nat.add_comm 1 j, pow_add_list, pow_one_list]
  rw [h_pow]
  simp only [List.append_assoc, append_assoc]
  refine frame_step hf ?_
  have hgd : I (b + j) ([1] +> (w +> s)) (d +> (w +> z)) := by
    simpa only [w, d, append_cons, append_nil] using G_d hz
  have h_sub : 1 + j - j = 1 := by omega
  refine inner_column (by omega) hin hgd ?_
  rw [h_sub]
  have hp := P_d (G_w hout)
  exact P_G (by simpa only [u, w, d, append_assoc, append_cons, append_nil] using hp)

private theorem Num_odd_inv_aux {m n : ℕ} {r : ListBlank Sym}
    (h : Num m r) (hm : m = n * 2 + 1) :
    ∃ s, Num n s ∧ r = t +> s := by
  cases h with
  | Num0 => omega
  | Num00 _ _ => omega
  | Num10 n' hs =>
    have : n' = n := by omega
    subst this
    exact ⟨_, hs, rfl⟩

theorem Num_odd_inv {n : ℕ} {r : ListBlank Sym} (h : Num (n * 2 + 1) r) :
    ∃ s, Num n s ∧ r = t +> s :=
  Num_odd_inv_aux h rfl

theorem P_odd_end (k : ℕ) {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ s, Num (n + (1 + k) * 2) s ∧ P (1 + k) (d +> (t +> r)) (w +> s) := by
  obtain ⟨x, hx, hi⟩ := I_nums 2 h
  obtain ⟨s, hs, hg⟩ := G_nums k hx
  refine ⟨s, ?_, ?_⟩
  · have : n + (1 + k) * 2 = n + 2 + k * 2 := by omega
    rwa [this]
  · refine P_add (a := 1) (b := k) ?_ (G_w hg)
    have hpd := P_d (P_t 2 hi)
    simpa only [u, w, t, append_cons, append_nil] using hpd

theorem pure_odd_boundary {a b : ℕ} {xs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hf : Frame a b xs) (hn : Num n r) :
    ∃ s, Num (n + (a * 2 + b + 1) * 2) s ∧
      (cfg (xs +> (w ^ a +> (t +> r)))) [tm1]⊢⁺ (cfg ((xs ++ w ^ a ++ d) +> s)) := by
  obtain ⟨x, hx, hi⟩ := I_nums (a * 2 + 2) hn
  obtain ⟨s, hs, hg⟩ := G_nums (b + a) hx
  refine ⟨s, ?_, ?_⟩
  · have : n + (a * 2 + b + 1) * 2 = n + (a * 2 + 2) + (b + a) * 2 := by omega
    rwa [this]
  · simp only [List.append_assoc, append_assoc]
    refine frame_step hf (column_partial (by omega) ?_)
    have h_sub : a - a = 0 := by omega
    refine ⟨t +> x, d +> s, P_t (a * 2 + 2) hi, ?_, by rw [h_sub]; exact .G0 _⟩
    simpa only [d, t, append_cons, append_nil] using G_d hg

theorem pure_three {a b j : ℕ} {xs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hf : Frame a b xs) (hj : j < a) (hn : Num n r) :
    ∃ s, Num (n + a * 2 + b + 1) s ∧
      (cfg (xs +> (w ^ j +> (t +> (t +> r))))) [tm1]⊢⁺ (cfg (xs +> (w ^ (j + 1) +> s))) := by
  obtain ⟨x, hx, hi⟩ := I_nums (j * 2 + 2) (.Num10 n hn)
  have hx' : Num ((n + j + 1) * 2 + 1) x := by
    have : (n + j + 1) * 2 + 1 = n * 2 + 1 + (j * 2 + 2) := by omega
    rwa [this]
  obtain ⟨x', hx'_num, rfl⟩ := Num_odd_inv hx'
  obtain ⟨y, hy, hyI⟩ := I_nums (b + j) hx'_num
  obtain ⟨s, hs, hp⟩ := P_odd_end (a - j - 1) hy
  refine ⟨s, ?_, ?_⟩
  · have : n + a * 2 + b + 1 = n + j + 1 + (b + j) + (1 + (a - j - 1)) * 2 := by omega
    rwa [this]
  · rw [pow_add_list w j 1, pow_one_list, append_assoc]
    refine frame_step hf (column_partial (by omega) ?_)
    refine ⟨t +> (t +> x'), d +> (t +> y), P_t (j * 2 + 2) hi, ?_, ?_⟩
    · simpa only [d, t, append_cons, append_nil] using G_d (P_G (P_t (b + j) hyI))
    · have : a - j = 1 + (a - j - 1) := by omega
      rw [this]
      exact P_G hp

theorem G_zero {n : ℕ} {r : ListBlank Sym} (h : Num n r) (hn : n ≤ 1) :
    ∃ s, Value (n * 2 + 3) s ∧ G1 (d +> r) s := by
  have : n * 2 + 3 = (n * 2 + 1) + 2 := by omega
  rw [this]
  exact G_value_one (.ValueEnd h hn)

theorem one_prefix (k : ℕ) : ([1] : List Sym) ++ [0, 0] ^ k ++ t = one k := by
  rcases k with _ | k
  · rfl
  · have hrot : ([0, 0] : List Sym) ^ k ++ [0] = [0] ++ [0, 0] ^ k :=
      lpow_rotate_list ([0] : List Sym) [0] k
    simp only [one, Longitudinal.pow_succ_list, List.append_assoc]
    change (1 : Sym) :: 0 :: (0 :: ([0, 0] ^ k ++ [1, 0])) = 1 :: 0 :: ([0, 0] ^ k ++ [0, 1, 0])
    congr 2
    have h2 : (0 : Sym) :: ([0, 0] ^ k ++ [1, 0]) = ([0] ++ [0, 0] ^ k) ++ [1, 0] := rfl
    rw [h2, ← hrot, List.append_assoc]
    rfl

theorem P_d_first_Q (k : ℕ) {r s : ListBlank Sym} (h : G1 r s) :
    P 1 (d +> ([0, 0] +> (t ^ k +> (d +> r)))) (w +> (one k +> s)) := by
  rw [← one_prefix k]
  have hq := Q_overflow k h
  have h_pow : ([0, 0] : List Sym) ^ (1 + k) = [0, 0] ++ [0, 0] ^ k := by
    rw [Nat.add_comm 1 k, Longitudinal.pow_succ_list]
  rw [h_pow, append_assoc] at hq
  have hqr := Q_R hq
  have hres := PdR.sideRLs_concat hqr
  rw [P, pow_one_list]
  simpa only [List.append_assoc, append_assoc] using hres

theorem P_d_last_Q {k n : ℕ} {xs : List Sym} {r s : ListBlank Sym}
    (hw : Word (k + 1) n xs) (he : n + 4 = 2 ^ (2 + k)) (hg : G1 r s) :
    P 1 (d +> (xs +> r)) ([1, 0, 0, 0] +> ([0, 0] ^ (1 + k) +> (t +> s))) := by
  have hp1 : 2 ^ (2 + k) = 2 ^ (1 + (k + 1)) := by
    have : 2 + k = 1 + (k + 1) := by omega
    rw [this]
  obtain ⟨ys, hy, hp⟩ := P_word_inc r hw (by omega) (by omega)
  refine P_d_second_Q hp ?_
  rw [Word_before_Q hy (by omega)]
  simpa only [List.append_assoc, append_assoc] using Q_overflow k hg

theorem Num_zeros (k : ℕ) {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    Num (n * 2 ^ k) ([0, 0] ^ k +> r) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have : n * 2 ^ (k + 1) = (n * 2 ^ k) * 2 := by ring
    rw [this, Longitudinal.pow_succ_list, append_assoc]
    exact .Num00 (n * 2 ^ k) ih

theorem column_late {a b j : ℕ} {r x y s : ListBlank Sym}
    (hj : j < a) (h0 : G (j * 2 + 2) r x) (h1 : G (b + j) (d +> x) y) (h2 : G (a - j) (d +> y) s) :
    Suffix a b (w ^ (1 + j) +> r) (w ^ j +> s) := by
  have h_pow : w ^ (1 + j) = w ^ j ++ w := by
    rw [Nat.add_comm 1 j, pow_add_list, pow_one_list]
  rw [h_pow, append_assoc]
  refine column_partial (by omega) ⟨w +> x, d +> y, G_w h0, ?_, h2⟩
  simpa only [w, d, append_cons, append_nil] using G_d h1

theorem late_first_Q {a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {r r₁ s out : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hb : 0 < b + j) (hw : Word (k + 1) n xs)
    (he : n + j * 4 + 6 = 2 ^ (2 + k)) (htail : G1 r r₁)
    (hmid : G (b + j + 1) (one k +> r₁) s) (hout : G (a - j - 1) (d +> s) out) :
    (cfg (fs +> (w ^ (1 + j) +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (1 + j) +> out))) := by
  have hp_bound : n + (j * 2 + 2) * 2 < 2 ^ (1 + (k + 1)) := by
    have : 2 ^ (1 + (k + 1)) = 2 ^ (2 + k) := by ring
    omega
  obtain ⟨ys, hy, hpre⟩ := P_word_linear (j * 2 + 2) r hw (by omega) hp_bound
  rw [Word_before_Q hy (by omega)] at hpre
  have hmid' : G ((b + j - 1) + 2) (one k +> r₁) s := by
    have : (b + j - 1) + 2 = b + j + 1 := by omega
    rwa [this]
  obtain ⟨z, hz, h2⟩ := G_split (b + j - 1) 2 hmid'
  refine frame_step hf ?_
  have h_w : w ^ (1 + j) +> out = w ^ j +> (w +> out) := by
    have : 1 + j = j + 1 := by omega
    rw [this, pow_add_list, pow_one_list, append_assoc]
  rw [h_w]
  have hpre' : G (j * 2 + 2) (xs +> r) ([0, 0] +> (t ^ k +> (d +> r))) := by
    simpa only [List.append_assoc, append_assoc] using P_G hpre
  have hmid_col : G (b + j) (d +> ([0, 0] +> (t ^ k +> (d +> r)))) (w +> z) := by
    have : b + j = 1 + (b + j - 1) := by omega
    rw [this]
    exact G_add (P_G (P_d_first_Q k htail)) (P_G (G_w hz))
  have hout_col : G (a - j) (d +> (w +> z)) (w +> out) := by
    have : a - j = 1 + (a - j - 1) := by omega
    rw [this]
    have hpd2 : G 1 (d +> (w +> z)) (w +> (d +> s)) := by
      have hp := P_d (G_w h2)
      exact P_G (by simpa only [u, w, d, append_assoc, append_cons, append_nil] using hp)
    exact G_add hpd2 (P_G (G_w hout))
  exact column_late hj hpre' hmid_col hout_col

theorem late_second_Q {a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hb : 0 < b + j) (hw : Word (k + 1) n xs)
    (he : n + j * 4 + 8 = 2 ^ (2 + k)) (hr : Num q r) :
    ∃ out, Num ((q * 2 + 5) * 2 ^ (2 + k) + (b + j - 1) + (a - j) * 2) out ∧
      (cfg (fs +> (w ^ (1 + j) +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (1 + j) +> out))) := by
  have hp_bound : n + (j * 2 + 2) * 2 < 2 ^ (1 + (k + 1)) := by
    have : 2 ^ (1 + (k + 1)) = 2 ^ (2 + k) := by ring
    omega
  obtain ⟨ys, hy, hpre⟩ := P_word_linear (j * 2 + 2) r hw (by omega) hp_bound
  obtain ⟨r₁, hr1, htail⟩ := P_num hr
  have hfirst := P_d_last_Q hy (by omega) (.GP htail)
  have hnum : Num (((q * 2 + 5) * 2 ^ (2 + k)) * 2 + 1)
      ([1, 0, 0, 0] +> ([0, 0] ^ (1 + k) +> (t +> r₁))) := by
    have h0 := Num.Num10 (((q + 2) * 2 + 1) * 2 ^ (1 + k) * 2)
      (.Num00 (((q + 2) * 2 + 1) * 2 ^ (1 + k)) (Num_zeros (1 + k) (.Num10 (q + 2) hr1)))
    have h_eq : (((q + 2) * 2 + 1) * 2 ^ (1 + k) * 2) * 2 + 1 = ((q * 2 + 5) * 2 ^ (2 + k)) * 2 + 1 := by
      have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
      ring
    rw [← h_eq]
    simpa only [t, append_cons, append_nil] using h0
  obtain ⟨s, hs, hmid⟩ := G_nums (b + j - 1) hnum
  have hs' : Num ((((q * 2 + 5) * 2 ^ (2 + k) + (b + j - 1)) * 2) + 1) s := by
    have : (((q * 2 + 5) * 2 ^ (2 + k) + (b + j - 1)) * 2) + 1 =
      (((q * 2 + 5) * 2 ^ (2 + k)) * 2 + 1) + (b + j - 1) * 2 := by ring
    rwa [this]
  obtain ⟨s₁, hs1, rfl⟩ := Num_odd_inv hs'
  obtain ⟨out, hnumout, hout⟩ := P_odd_end (a - j - 1) hs1
  refine ⟨out, ?_, ?_⟩
  · have : (q * 2 + 5) * 2 ^ (2 + k) + (b + j - 1) + (a - j) * 2 =
      (q * 2 + 5) * 2 ^ (2 + k) + (b + j - 1) + (1 + (a - j - 1)) * 2 := by omega
    rwa [this]
  · refine frame_step hf ?_
    have h_w : w ^ (1 + j) +> out = w ^ j +> (w +> out) := by
      have : 1 + j = j + 1 := by omega
      rw [this, pow_add_list, pow_one_list, append_assoc]
    rw [h_w]
    have hmid_col : G (b + j) (d +> (ys +> r)) (t +> s₁) := by
      have : b + j = 1 + (b + j - 1) := by omega
      rw [this]
      exact G_add (P_G hfirst) hmid
    have hout_col : G (a - j) (d +> (t +> s₁)) (w +> out) := by
      have : a - j = 1 + (a - j - 1) := by omega
      rw [this]
      exact P_G hout
    exact column_late hj (P_G hpre) hmid_col hout_col



set_option linter.unusedVariables false

theorem pow2_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by decide) h

theorem pow2_lt_iff {a b : ℕ} : 2 ^ a < 2 ^ b ↔ a < b :=
  Nat.pow_lt_pow_iff_right (by decide)

theorem pow2_le_iff {a b : ℕ} : 2 ^ a ≤ 2 ^ b ↔ a ≤ b :=
  Nat.pow_le_pow_iff_right (by decide)

abbrev NonHaltFrom (M : Machine Sym Q) (c₀ : Cfg Sym Q) : Prop :=
  NeverHaltsFrom M c₀

theorem nonHaltFrom_of_progress {Inv : Cfg Sym Q → Prop}
    (h_prog : ∀ c, Inv c → ∃ c', (c [tm1]⊢⁺ c') ∧ Inv c')
    {c₀ : Cfg Sym Q} (hc₀ : Inv c₀) : NonHaltFrom tm1 c₀ :=
  NeverHaltsFrom.of_reachesPlus_invariant h_prog hc₀

theorem late_first_Q_boundary {a : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a (a + 1) fs) (ha : 2 ≤ a) (hpow : a * 6 + 4 = 2 ^ (2 + k))
    (hw : Word (k + 1) (a * 2 + 2) xs) (hr : Num q r) :
    ∃ ys s, Word k (a + 3) ys ∧ Num (q + 4) s ∧
      (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (ys +> s))) := by
  have hk : 0 < k := by
    rcases k with _ | k' <;> omega
  obtain ⟨z, c, hc, hz⟩ := CounterRun_total (fun z' hz' => GCounter_total k z' hk hz')
    (a * 2 + 1) 1 (Word_bound (Word_one k))
  have hodd : z % 2 = 1 := GCounterRun_odd hc rfl
  have e := GCounterRun_balance hc hk (by decide)
  have hp2 : 2 ^ (2 + k) = 2 ^ k * 4 := by ring
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  have epow : (2 ^ k - 1) * 2 = a * 3 := by omega
  rw [epow] at e
  have ez : z + c * (a * 3) = a * 4 + 3 := by
    unfold phi at e
    omega
  have hz' : z < a * 3 + 2 := by omega
  have ec : c = 1 ∧ z = a + 3 := by
    rcases c with _ | _ | c
    · omega
    · constructor <;> omega
    · nlinarith
  rcases ec with ⟨rfl, rfl⟩
  obtain ⟨r₀, h0, hp⟩ := P_num hr
  obtain ⟨s, hs, hp'⟩ := P_num h0
  obtain ⟨ys, hy, hg⟩ := G_counter_run (Word_one k) hk hc (P_G hp')
  refine ⟨ys, s, hy, by simpa only [Nat.add_assoc] using hs, ?_⟩
  simp only [List.append_assoc, append_assoc]
  have hstep := late_first_Q (a := a) (b := a + 1) (j := a - 1) (k := k) (n := a * 2 + 2)
    (r₁ := r₀) (s := ys +> s) (out := d +> (ys +> s))
    hf (by omega) (by omega) hw (by omega) (.GP hp)
    (by
      have : a + 1 + (a - 1) + 1 = a * 2 + 1 := by omega
      rwa [this])
    (by
      have : a - (a - 1) - 1 = 0 := by omega
      rw [this]
      exact .G0 _)
  have ha_eq : 1 + (a - 1) = a := by omega
  rwa [ha_eq] at hstep

theorem Word_split {k n : ℕ} {xs : List Sym} (hw : Word k n xs) (hn : 0 < n) (hpow : n ≠ 2 ^ k) :
    ∃ a b z ys, k = 1 + a + b ∧ n = 2 ^ a * (z * 2 + 1) ∧ Word b z ys ∧
      xs = [0, 0] ^ a ++ t ++ ys ∧ [1] ++ xs = one a ++ ys := by
  induction hw with
  | Word0 => omega
  | Word1 =>
    exfalso
    exact hpow rfl
  | Word00 k' n' h_xs ih =>
    have hn' : 0 < n' := by omega
    have hpow' : n' ≠ 2 ^ k' := by
      intro heq
      apply hpow
      rw [heq]
      ring
    obtain ⟨a, b, z, ys, hk_eq, hv, hw', hx, hx'⟩ := ih hn' hpow'
    refine ⟨1 + a, b, z, ys, by omega, ?_, hw', ?_, ?_⟩
    · rw [hv]
      ring
    · have h_pow : ([0, 0] : List Sym) ^ (1 + a) = [0, 0] ++ [0, 0] ^ a := by
        rw [Nat.add_comm 1 a, Longitudinal.pow_succ_list]
      rw [h_pow, hx]
      simp only [List.append_assoc]
    · rw [hx, ← one_prefix (1 + a)]
      have h_pow : ([0, 0] : List Sym) ^ (1 + a) = [0, 0] ++ [0, 0] ^ a := by
        rw [Nat.add_comm 1 a, Longitudinal.pow_succ_list]
      rw [h_pow]
      simp only [List.append_assoc]
  | Word10 k' n' h_xs _ =>
    refine ⟨0, k', n', _, by omega, by omega, h_xs, ?_, ?_⟩
    · simp only [Longitudinal.pow_zero_list, List.nil_append]
    · rfl

theorem split_root {a b j : ℕ} {fs : List Sym} {r : ListBlank Sym} {k : ℕ} {tail : ListBlank Sym}
    {n c m e : ℕ} {s : ListBlank Sym}
    (hf : Frame a b fs) (hj : j ≤ a) (hk : 0 < k)
    (hp : P (j * 2 + 2) r ([0, 0] ^ k +> (t +> tail)))
    (hc : CounterRun (ICounter k) (b + j) 1 n c)
    (he : CounterRun (GCounter k) (a - j) n m e)
    (hg : G (c + e) tail s) :
    ∃ xs, Word k m xs ∧ (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ (cfg (fs +> (w ^ j +> (xs +> s)))) := by
  obtain ⟨r₀, hg0, hg1⟩ := G_split c e hg
  obtain ⟨ys, hy, hi⟩ := I_counter_run (Word_one k) hc hg0
  obtain ⟨xs, hx, hrun⟩ := G_counter_run hy hk he hg1
  refine ⟨xs, hx, frame_step hf (column_partial hj ⟨_, _, hp, ?_, hrun⟩)⟩
  rw [← one_prefix k] at hi
  simpa only [List.append_assoc, append_assoc] using hi

theorem split_d {k i n c : ℕ} {tail r s : ListBlank Sym}
    (hp : P 2 r ([0, 0] ^ k +> (t +> tail)))
    (hc : CounterRun (ICounter k) i 1 n c)
    (hg : G c tail s) :
    ∃ xs, Word (k + 1) (n * 2 + 1) xs ∧ P (1 + i) (d +> r) (xs +> s) := by
  obtain ⟨ys, hy, hi⟩ := I_counter_run (Word_one k) hc hg
  refine ⟨t ++ ys, .Word10 k n hy, ?_⟩
  rw [append_assoc]
  refine P_add (a := 1) (b := i) ?_ (P_t i hi)
  have hpd := P_d hp
  rw [← one_prefix k]
  simpa only [u, t, List.append_assoc, append_assoc, append_cons, append_nil] using hpd

theorem split_inside {a b j : ℕ} {fs : List Sym} {r r₀ r₁ : ListBlank Sym}
    {k : ℕ} {tail : ListBlank Sym} {n c : ℕ} {s : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hin : Inner j r (t +> r₀))
    (hmid : G (b + j) r₀ r₁) (hp : P 2 r₁ ([0, 0] ^ k +> (t +> tail)))
    (hc : CounterRun (ICounter k) (a - j - 1) 1 n c)
    (hg : G c tail s) :
    ∃ xs, Word (k + 1) (n * 2 + 1) xs ∧
      (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ (cfg (fs +> (w ^ j +> (xs +> s)))) := by
  obtain ⟨xs, hw, hrun⟩ := split_d hp hc hg
  refine ⟨xs, hw, frame_step hf ?_⟩
  have hgd : I (b + j) ([1] +> (t +> r₀)) (d +> r₁) := by
    simpa only [d, t, append_cons, append_nil] using G_d hmid
  refine inner_column (by omega) hin hgd ?_
  have : a - j = 1 + (a - j - 1) := by omega
  rw [this]
  exact P_G hrun

theorem first_Q_inside {a b j : ℕ} {fs : List Sym} {r r₀ : ListBlank Sym}
    {k : ℕ} {tail tail' s : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hin : Inner j r (t +> r₀))
    (hmid : G (b + j) r₀ ([0, 0] +> (t ^ k +> (d +> tail))))
    (htail : G1 tail tail')
    (hrest : G (a - j - 1) (one k +> tail') s) :
    (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> s))) := by
  rw [pow_add_list w j 1, pow_one_list, append_assoc]
  refine frame_step hf ?_
  have hgd : I (b + j) ([1] +> (t +> r₀)) (d +> ([0, 0] +> (t ^ k +> (d +> tail)))) := by
    simpa only [d, t, append_cons, append_nil] using G_d hmid
  refine inner_column (by omega) hin hgd ?_
  have : a - j = 1 + (a - j - 1) := by omega
  rw [this]
  exact G_add (P_G (P_d_first_Q k htail)) (P_G (G_w hrest))

theorem Num_factor {n : ℕ} {r : ListBlank Sym} (h : Num n r) (hn : 0 < n) :
    ∃ j q s, n = (q * 2 + 1) * 2 ^ j ∧ Num q s ∧ r = [0, 0] ^ j +> (t +> s) := by
  induction h with
  | Num0 => omega
  | Num00 n' h_r ih =>
    obtain ⟨j, q, s, he, hs, hr⟩ := ih (by omega)
    refine ⟨1 + j, q, s, ?_, hs, ?_⟩
    · rw [he]
      ring
    · have h_pow : ([0, 0] : List Sym) ^ (1 + j) = [0, 0] ++ [0, 0] ^ j := by
        rw [Nat.add_comm 1 j, Longitudinal.pow_succ_list]
      rw [h_pow, hr, append_assoc]
  | Num10 n' h_r _ =>
    exact ⟨0, n', _, by omega, h_r, rfl⟩

theorem P_end_birth {n : ℕ} {r : ListBlank Sym} (h : Num n r) :
    ∃ j q s, n + 4 = (q * 2 + 1) * 2 ^ j ∧ Num q s ∧ P 1 (d +> r) ((t ++ one j) +> s) := by
  obtain ⟨x, hx, hp⟩ := P_nums 2 h
  obtain ⟨j, q, s, he, hs, hr⟩ := Num_factor hx (by omega)
  refine ⟨j, q, s, he, hs, ?_⟩
  rw [hr] at hp
  rw [← one_prefix j]
  have hpd := P_d hp
  simpa only [u, t, List.append_assoc, append_assoc, append_cons, append_nil] using hpd

theorem G_end {n : ℕ} {r : ListBlank Sym} (i : ℕ) (h : Num n r) (hi : 0 < i) :
    ∃ q s, Value q s ∧ q ≤ n + i * 2 + 2 ∧ G i (d +> r) s := by
  rcases i with _ | i
  · omega
  · obtain ⟨j, q, s, he, hs, hp⟩ := P_end_birth h
    have hv : Value (3 + (2 ^ (1 + j) - 1) * q) ((t ++ one j) +> s) := by
      have h_phi : (3 : ℕ) = phi 3 := rfl
      rw [h_phi]
      have h_1j : 1 + j = j + 1 := by omega
      rw [h_1j]
      exact Value.ValueWord (k := j + 1) (n := 3) (q := q) (by omega) (by decide)
        (.Word10 j 1 (Word_one j)) (.ValueNum hs)
    obtain ⟨z, hz, hg⟩ := G_value hv i
    refine ⟨_, z, hz, ?_, ?_⟩
    · have h_1j : 2 ^ (1 + j) = 2 ^ j * 2 := by ring
      have hp0 : 1 ≤ 2 ^ j := pow2_pos j
      have h_3 : 3 ≤ 2 ^ j + q := by
        rcases q with _ | _ | q' <;> nlinarith
      have hp1 : 1 ≤ 2 ^ (1 + j) := pow2_pos (1 + j)
      zify [hp1, hp0] at hp1 hp0 h_1j he h_3 ⊢
      nlinarith
    · have : i + 1 = 1 + i := by omega
      rw [this]
      exact G_add (P_G hp) hg

theorem G_end_word {n : ℕ} {r : ListBlank Sym} (i : ℕ) (h : Num n r) (hi : 0 < i) :
    ∃ k q z c xs s,
      n + 4 = (q * 2 + 1) * 2 ^ k ∧
      CounterRun (GCounter (k + 1)) (i - 1) 3 z c ∧
      Word (k + 1) z xs ∧ Num (q + c * 2) s ∧ z % 2 = 1 ∧
      phi z + (2 ^ (k + 1) - 1) * (q + c * 2) ≤ n + i * 2 + 2 ∧
      G i (d +> r) (xs +> s) := by
  rcases i with _ | i
  · omega
  · obtain ⟨k, q, r₀, he, h0, hp⟩ := P_end_birth h
    have hw : Word (k + 1) 3 (t ++ one k) := .Word10 k 1 (Word_one k)
    obtain ⟨z, c, hc, hz⟩ := CounterRun_total
      (fun z' hz' => GCounter_total (k + 1) z' (by omega) hz') i 3 (Word_bound hw)
    obtain ⟨s, hs, hg⟩ := G_nums c h0
    obtain ⟨xs, hx, hrun⟩ := G_counter_run hw (by omega) hc hg
    refine ⟨k, q, z, c, xs, s, he, by simpa using hc, hx, hs,
      GCounterRun_odd hc rfl, ?_, ?_⟩
    · have e := GCounterRun_balance hc (by omega) (by decide)
      have h_phi3 : phi 3 = 3 := rfl
      rw [h_phi3] at e
      have hp0 : 1 ≤ 2 ^ k := pow2_pos k
      have hp1 : 1 ≤ 2 ^ (k + 1) := pow2_pos (k + 1)
      have h_pow : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
      have h_3 : 3 ≤ 2 ^ k + q := by
        rcases q with _ | _ | q' <;> nlinarith
      zify [hp0, hp1] at hp0 hp1 h_pow e he h_3 ⊢
      nlinarith
    · have : i + 1 = 1 + i := by omega
      rw [this]
      exact G_add (P_G hp) hrun

theorem pure_even {a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hf : Frame a b fs) (hj : j ≤ a) (hn : Num (n * 2) r) :
    ∃ k q m c z e xs s,
      0 < k ∧ n * 2 + j * 4 + 4 = (q * 2 + 1) * 2 ^ k ∧
      CounterRun (ICounter k) (b + j) 1 m c ∧
      CounterRun (GCounter k) (a - j) m z e ∧
      Word k z xs ∧ Num (q + (c + e) * 2) s ∧
      (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ (cfg (fs +> (w ^ j +> (xs +> s)))) := by
  obtain ⟨r₀, h0, hp⟩ := P_nums (j * 2 + 2) hn
  obtain ⟨k, q, r₁, he, h1, er⟩ := Num_factor h0 (by omega)
  have hk : 0 < k := by
    rcases k with _ | k' <;> omega
  obtain ⟨m, c, hc, hm⟩ := CounterRun_total (ICounter_total k) (b + j) 1 (Word_bound (Word_one k))
  obtain ⟨z, e, hz, _⟩ := CounterRun_total (fun z' hz' => GCounter_total k z' hk hz') (a - j) m hm
  obtain ⟨s, hs, hg⟩ := G_nums (c + e) h1
  rw [er] at hp
  obtain ⟨xs, hx, hstep⟩ := split_root hf hj hk hp hc hz hg
  exact ⟨k, q, m, c, z, e, xs, s, hk, by omega, hc, hz, hx, hs, hstep⟩

theorem pure_one {a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hf : Frame a b fs) (hj : j < a) (hn : Num n r) :
    ∃ k q z c xs s,
      0 < k ∧ n * 2 + j * 4 + b * 2 + 6 = (q * 2 + 1) * 2 ^ k ∧
      CounterRun (GCounter (k + 1)) (a - j - 1) 3 z c ∧
      Word (k + 1) z xs ∧ Num (q + c * 2) s ∧
      (cfg (fs +> (w ^ j +> (t +> ([0, 0] +> r))))) [tm1]⊢⁺ (cfg (fs +> (w ^ j +> (xs +> s)))) := by
  obtain ⟨x, hx, hi⟩ := I_nums (j * 2 + 2) (.Num00 n hn)
  obtain ⟨y, hy, hb⟩ := G_nums (b + j) hx
  obtain ⟨k, q, r₀, he, h0, hp⟩ := P_end_birth hy
  have hk : 0 < k := by
    rcases k with _ | k' <;> omega
  have hw : Word (k + 1) 3 (t ++ one k) := .Word10 k 1 (Word_one k)
  obtain ⟨z, c, hc, hz⟩ := CounterRun_total
    (fun z' hz' => GCounter_total (k + 1) z' (by omega) hz') (a - j - 1) 3 (Word_bound hw)
  obtain ⟨s, hs, gc⟩ := G_nums c h0
  obtain ⟨xs, hxs, hg⟩ := G_counter_run hw (by omega) hc gc
  refine ⟨k, q, z, c, xs, s, hk, by omega, hc, hxs, hs, ?_⟩
  refine frame_step hf (column_partial (by omega) ⟨t +> x, d +> y, P_t (j * 2 + 2) hi, ?_, ?_⟩)
  · simpa only [d, t, append_cons, append_nil] using G_d hb
  · have : a - j = 1 + (a - j - 1) := by omega
    rw [this]
    exact G_add (P_G hp) hg

theorem late_second_Q_pair {a : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a a fs) (ha : 2 ≤ a) (hpow : a * 6 + 2 = 2 ^ (2 + k))
    (hw : Word (k + 1) (a * 2 + 2) xs) (hr : Num q r) :
    ∃ s, Num ((q * 3 + 11) * a + q + 3) s ∧
      (cfg (fs +> (w ^ (a - 1) +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ a +> s))) := by
  obtain ⟨s₀, h0, hfirst⟩ := late_second_Q (a := a) (b := a) (j := a - 2)
    hf (by omega) (by omega) hw (by omega) hr
  have h_eq0 : (q * 2 + 5) * 2 ^ (2 + k) + (a + (a - 2) - 1) + (a - (a - 2)) * 2 =
      (((q * 3 + 8) * a + q + 2) * 2 + 1) * 2 + 1 := by
    have h_sub1 : a + (a - 2) - 1 = a * 2 - 3 := by omega
    have h_sub2 : (a - (a - 2)) * 2 = 4 := by omega
    rw [← hpow, h_sub1, h_sub2]
    have ha3 : 3 ≤ a * 2 := by omega
    zify [ha3] at ha3 ⊢
    ring
  rw [h_eq0] at h0
  obtain ⟨s₁, h1, rfl⟩ := Num_odd_inv h0
  obtain ⟨s₂, h2, rfl⟩ := Num_odd_inv h1
  obtain ⟨s, hs, hsecond⟩ := pure_three (a := a) (b := a) (j := a - 1) hf (by omega) h2
  refine ⟨s, ?_, ?_⟩
  · have : (q * 3 + 11) * a + q + 3 = (q * 3 + 8) * a + q + 2 + a * 2 + a + 1 := by ring
    rwa [this]
  · have ha1 : 1 + (a - 2) = a - 1 := by omega
    have ha2 : a - 1 + 1 = a := by omega
    rw [ha1] at hfirst
    rw [ha2] at hsecond
    exact ReachesPlus.trans hfirst hsecond

theorem late_second_Q_recover {a : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hf : Frame a a fs) (ha : 5 ≤ a) (hpow : a * 6 + 2 = 2 ^ (2 + k))
    (hw : Word (k + 1) (a * 2 + 2) xs) (hr : Num q r) (hq : q ≤ 3) :
    ∃ K z Q ys s,
      0 < K ∧ K ≤ 4 + k ∧ Word K z ys ∧ Num Q s ∧ z % 2 = 1 ∧
      (2 ^ (2 + k) ≤ 2 ^ K → z = a * 4 + 1) ∧
      phi z + (2 ^ K - 1) * Q < (a * 3 + 1) * 8 ∧
      (K = 1 → z = 3 ∧ Q ≤ (a + a) * 8) ∧
      (cfg (fs +> (w ^ (a - 1) +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (ys +> s))) := by
  have hmod : a % 4 = 1 := by
    rcases Frame_phase hf with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  obtain ⟨r₂, h2, hfirst⟩ := late_second_Q_pair hf (by omega) hpow hw hr
  have ea : a = a / 4 * 4 + 1 := by omega
  have h_even : (q * 3 + 11) * a + q + 3 = ((q * 3 + 11) * (a / 4) * 2 + q * 2 + 7) * 2 := by
    nlinarith
  rw [h_even] at h2
  obtain ⟨l, q₀, m, c, z₀, e, ys, r₃, hl, he, hc, hz0, hy, h3, hthird⟩ :=
    pure_even (a := a) (b := a) (j := a) hf (by omega) h2
  have el : l = 1 := by
    rcases l with _ | _ | l'
    · omega
    · rfl
    · have : (q₀ * 2 + 1) * 2 ^ (l' + 2) = ((q₀ * 2 + 1) * 2 ^ l') * 4 := by ring
      rw [this] at he
      omega
  subst el
  have ha_sub : a - a = 0 := by omega
  rw [ha_sub] at hz0
  cases hz0
  have hm : 0 < m := ICounterRun_positive hc (by decide)
  have hmb : m < 4 := Word_bound hy
  obtain ⟨z₁, c₁, hc1, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total 1 z' (by decide) hz')
    (a * 2 + 2) m hmb
  have hc1' : CounterRun (GCounter 1) (2 + a * 2) m z₁ c₁ := by
    have : 2 + a * 2 = a * 2 + 2 := by omega
    rwa [this]
  obtain ⟨rfl, hcl, hcu⟩ := GCounterRun_one hc1' hm hmb
  have h3' : Num (q₀ + c * 2) r₃ := by simpa using h3
  obtain ⟨r₄, h4, hg⟩ := G_nums c₁ h3'
  obtain ⟨l, q₁, z, c₂, ys', s, ebirth, hc2, hy', hs, hodd, hvalue, hlast⟩ :=
    G_end_word (a + a) h4 (by omega)
  have ecount := ICounterRun_balance hc
  have h_2_1 : 2 ^ (1 + 1) - 1 = 3 := rfl
  rw [h_2_1] at ecount
  have hpm := phi_bounds hm
  have hq_a : (q * 3 + 11) * (a / 4) ≤ 20 * (a / 4) := by
    rcases q with _ | _ | _ | _ | q' <;> omega
  have hbirth : 2 ^ l < 2 ^ (4 + k) := by
    have hp4 : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
    have hle_mul : 1 * 2 ^ l ≤ (q₁ * 2 + 1) * 2 ^ l := Nat.mul_le_mul_right (2 ^ l) (by omega)
    omega
  refine ⟨l + 1, z, q₁ + c₂ * 2, ys', s, by omega, ?_, hy', hs, hodd, ?_, ?_, ?_, ?_⟩
  · have hlt := pow2_lt_iff.mp hbirth
    omega
  · intro hwide
    have hp_wide : 2 ^ (2 + k) * 2 ≤ 2 ^ (1 + (l + 1)) := by
      have : 2 ^ (1 + (l + 1)) = 2 ^ (l + 1) * 2 := by ring
      omega
    obtain ⟨hz', _⟩ := GCounterRun_linear hc2 (by omega)
    omega
  · omega
  · intro eK
    have el0 : l = 0 := by omega
    subst el0
    have hzlo := GCounterRun_three hc2 (by omega) rfl
    have hzhi := Word_bound hy'
    have ez : z = 3 := by
      change z < 4 at hzhi
      omega
    subst ez
    refine ⟨rfl, ?_⟩
    have e2 := GCounterRun_balance hc2 (by decide) (by decide)
    have h_phi3 : phi 3 = 3 := rfl
    have h_21 : (2 ^ 1 - 1) * 2 = 2 := rfl
    rw [h_phi3, h_21] at e2
    change q₀ + c * 2 + c₁ * 2 + 4 = (q₁ * 2 + 1) * 1 at ebirth
    omega
  · exact ReachesPlus.trans hfirst (ReachesPlus.trans hthird
      (one_boundary hf hy (Or.inr (by omega)) hc1 hg hlast))

theorem translated_step {a j : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hf : Frame a a fs) (ha : a = j + 1) (hpow : a * 6 + 2 = 2 ^ k)
    (hw : Bin k (a * 2 + 2) xs) :
    (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ j +> (xs +> ([1] +> r))))) := by
  have hk : 0 < k := by
    rcases k with _ | k' <;> omega
  have hp_1k : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  obtain ⟨ys, hy, hp⟩ := P_Bins (a * 2) hw hk (by omega)
  have h_top : a * 2 + 2 + a * 2 * 2 = 2 ^ k := by omega
  rw [h_top] at hy
  rw [Bin_unique hy (Bin_top k)] at hp
  obtain ⟨zs, hz, hi⟩ := I_Bins (a + j) (Bin_one hk) (by omega)
  obtain ⟨xs', hx, hlast⟩ := P_Bin hz hk (by omega)
  have ex : xs' = xs := by
    have : 1 + (a + j) + 2 = a * 2 + 2 := by omega
    rw [this] at hx
    exact Bin_unique hx hw
  subst ex
  refine frame_step hf (column_partial (by omega) ⟨[0, 0] ^ k +> ([1] +> r), zs +> ([1] +> r), ?_, ?_, ?_⟩)
  · have h_concat := hp.sideRLs_concat (SideRLs.nil r)
    have h_p : j * 2 + 2 = a * 2 := by omega
    rw [h_p]
    simpa only [P, List.append_assoc, append_assoc, append_nil] using h_concat
  · have h_concat := hi.sideRLs_concat (SideRLs.nil ([1] +> r))
    simpa only [I, List.append_assoc, append_assoc, append_nil] using h_concat
  · have h_aj : a - j = 1 := by omega
    rw [h_aj]
    apply P_G
    have h_concat := hlast.sideRLs_concat (SideRLs.nil ([1] +> r))
    simpa only [P, pow_one_list, List.append_assoc, append_assoc, append_nil] using h_concat

theorem translated_nonhalt {a j : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hf : Frame a a fs) (ha : a = j + 1) (hpow : a * 6 + 2 = 2 ^ k)
    (hw : Bin k (a * 2 + 2) xs) :
    NonHaltFrom tm1 (cfg (fs +> (w ^ j +> (xs +> r)))) := by
  refine nonHaltFrom_of_progress (Inv := fun c => ∃ s, c = cfg (fs +> (w ^ j +> (xs +> s)))) ?_ ⟨r, rfl⟩
  rintro c ⟨s, rfl⟩
  exact ⟨cfg (fs +> (w ^ j +> (xs +> ([1] +> s)))), translated_step hf ha hpow hw, ⟨[1] +> s, rfl⟩⟩

theorem Word_Bin {k n : ℕ} {xs : List Sym} (hw : Word k n xs) :
    ∃ bs, Bin k n bs ∧ xs = bs ++ t := by
  induction hw with
  | Word0 => exact ⟨[0], .Bin0, rfl⟩
  | Word1 => exact ⟨[1], .Bin1, rfl⟩
  | Word00 k' n' _ ih =>
    obtain ⟨bs, hb, rfl⟩ := ih
    exact ⟨[0, 0] ++ bs, .Bin00 k' n' hb, by simp only [List.append_assoc]⟩
  | Word10 k' n' _ ih =>
    obtain ⟨bs, hb, rfl⟩ := ih
    exact ⟨t ++ bs, .Bin10 k' n' hb, by simp only [List.append_assoc]⟩

theorem translated_word_nonhalt {a j : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hf : Frame a a fs) (ha : a = j + 1) (hpow : a * 6 + 2 = 2 ^ k)
    (hw : Word k (a * 2 + 2) xs) :
    NonHaltFrom tm1 (cfg (fs +> (w ^ j +> (xs +> r)))) := by
  obtain ⟨bs, hb, rfl⟩ := Word_Bin hw
  rw [append_assoc]
  exact translated_nonhalt hf ha hpow hb

def frame : ℕ → ℕ × ℕ × List Sym
  | 0 => (0, 1, d ++ d)
  | n + 1 =>
    let (a, b, xs) := frame n
    (a + b, a * 2 + 1, xs ++ w ^ a ++ d)

theorem frame_spec (n : ℕ) :
    let (a, b, xs) := frame n
    Frame a b xs := by
  induction n with
  | zero => exact .Frame0
  | succ n ih =>
    dsimp [frame]
    exact .FrameS ih

theorem Frame_close {a b : ℕ} {xs : List Sym} (h : Frame a b xs) :
    a ≤ b ∧ b ≤ a + 1 := by
  induction h with
  | Frame0 => omega
  | FrameS _ ih => omega

theorem narrow_next_guard {a b j : ℕ} {fs : List Sym} {k z : ℕ}
    (hf : Frame a b fs) (hj : j < a) (hsize : 2 ^ (1 + k) ≤ b + j)
    (hlower : z % 2 = 0 → (a - j) * 2 ≤ z) :
    z % 2 = 1 ∨ ((a - (j + 1)) * 2 + 2 ≤ z ∧ 2 ^ k - z / 2 ≤ (j + 1) * 2) := by
  have hclose := Frame_close hf
  by_cases hodd : z % 2 = 1
  · exact Or.inl hodd
  · right
    have hlow := hlower (by omega)
    have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    omega

theorem frame_size (n : ℕ) :
    let (a, b, _) := frame n
    a * 2 + b + 1 = 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [frame] at ih ⊢
    have : 2 ^ (n + 1 + 1) = 2 ^ (n + 1) * 2 := by ring
    omega

def prefix_word (n : ℕ) : List Sym := (frame n).2.2

def word : ℕ → ℕ → List Sym
  | 0, 0 => [0, 1, 0]
  | 0, _ => d
  | k + 1, n => (if n % 2 == 0 then [0, 0] else t) ++ word k (n / 2)

theorem word_spec (k n : ℕ) (hn : n < 2 ^ (1 + k)) : Word k n (word k n) := by
  induction k generalizing n with
  | zero =>
    rcases n with _ | _ | n'
    · exact .Word0
    · exact .Word1
    · change n' + 2 < 2 at hn
      omega
  | succ k ih =>
    dsimp [word]
    have hp : 2 ^ (1 + (k + 1)) = 2 ^ (1 + k) * 2 := by ring
    by_cases he : n % 2 = 0
    · have hbeq : (n % 2 == 0) = true := beq_iff_eq.mpr he
      rw [hbeq, if_pos rfl]
      have hn_eq : (n / 2) * 2 = n := by omega
      have hw0 := Word.Word00 k (n / 2) (ih (n / 2) (by omega))
      rwa [hn_eq] at hw0
    · have hbeq : (n % 2 == 0) = false := by
        rcases h : (n % 2 == 0)
        · rfl
        · exfalso; exact he (beq_iff_eq.mp h)
      rw [hbeq, if_neg Bool.false_ne_true]
      have hn_eq : (n / 2) * 2 + 1 = n := by omega
      have hw1 := Word.Word10 k (n / 2) (ih (n / 2) (by omega))
      rwa [hn_eq] at hw1

structure Level (h a b : ℕ) (fs : List Sym) : Prop where
  level_frame : Frame a b fs
  level_height : 5 ≤ h
  level_size : a * 2 + b + 1 = 2 ^ (h - 1)

theorem Level_bounds {h a b : ℕ} {fs : List Sym} (hl : Level h a b fs) :
    5 ≤ h ∧ 5 ≤ a ∧ a ≤ b ∧ b ≤ a + 1 := by
  rcases hl with ⟨hf, hh, hsize⟩
  have hclose := Frame_close hf
  have h16 : 16 ≤ 2 ^ (h - 1) := by
    have : (16 : ℕ) = 2 ^ 4 := rfl
    rw [this]
    exact pow2_mono (by omega)
  omega

theorem Level_next {h a b : ℕ} {fs : List Sym} (hl : Level h a b fs) :
    Level (1 + h) (a + b) (a * 2 + 1) (fs ++ w ^ a ++ d) := by
  rcases hl with ⟨hf, hh, hsize⟩
  refine ⟨.FrameS hf, by omega, ?_⟩
  have h_sub : 1 + h - 1 = (h - 1) + 1 := by omega
  rw [h_sub, pow2_succ_right]
  omega

def Narrow (a j k n : ℕ) : Prop :=
  n % 2 = 1 ∨ ((a - j) * 2 + 2 ≤ n ∧ 2 ^ (1 + k) ≤ n + j * 4)

def Two (a j n : ℕ) : Prop :=
  n % 2 = 1 ∨ (a - j) * 2 + 2 ≤ n

inductive SinglePhase (h a b j : ℕ) : ℕ → ℕ → ℕ → Prop where
  | SN (k n q : ℕ) : 3 ≤ k → k + 2 ≤ h → Narrow a j k n → SinglePhase h a b j k n q
  | S2 (n q : ℕ) : Two a j n → SinglePhase h a b j 2 n q
  | S1 (n q : ℕ) : (j = a ∨ (j + 1 = a ∧ n = 1 ∧ q + 1 ≤ (a * 2 + b + 1) * 2)) →
      SinglePhase h a b j 1 n q
  | SX (k q : ℕ) :
      ((h = k + 1 ∧ q ≤ 1) ∨ (k = h ∧ q = 0) ∨ (k = h + 1 ∧ j = a ∧ a = b ∧ q = 0)) →
      SinglePhase h a b j k (a * 2 + b + 1 - j) q
  | SY (k q : ℕ) : h ≤ k + 1 → k ≤ h + 1 → (k < h ∨ j < a) →
      SinglePhase h a b j k ((a - j) * 2 + 1) q
  | SZ (n : ℕ) : n * 2 = (a * 2 + b + 1) * 2 + (a - j) → SinglePhase h a b j (h - 1) n 0

inductive Single (h a b j : ℕ) : ListBlank Sym → Prop where
  | SNum (n : ℕ) (r : ListBlank Sym) : Num n r → n ≤ a * 8 → Single h a b j r
  | SWord (k n q : ℕ) (xs : List Sym) (r : ListBlank Sym) :
      0 < k → 0 < n → Word k n xs → Num q r →
      SinglePhase h a b j k n q → phi n + (2 ^ k - 1) * q ≤ (a * 2 + b + 1) * 4 →
      Single h a b j (xs +> r)

inductive SRoot : Cfg Sym Q → Prop where
  | sroot (h a b j : ℕ) (fs : List Sym) (r : ListBlank Sym) :
      Level h a b fs → j ≤ a → Single h a b j r → SRoot (cfg (fs +> (w ^ j +> r)))

theorem single_odd_phase {h a b j k n q : ℕ}
    (hk : 2 ≤ k) (hmax : k ≤ h + 1) (hodd : n % 2 = 1)
    (hwide : h ≤ k + 1 → n = (a - j) * 2 + 1 ∧ (k < h ∨ j < a)) :
    SinglePhase h a b j k n q := by
  by_cases hge : h ≤ k + 1
  · obtain ⟨rfl, hj⟩ := hwide hge
    exact .SY k q hge hmax hj
  · rcases k with _ | _ | _ | k'
    · omega
    · omega
    · exact .S2 n q (Or.inl hodd)
    · exact .SN (k' + 3) n q (by omega) (by omega) (Or.inl hodd)

theorem split_capacity {k i j m c z e : ℕ} (q : ℕ)
    (hk : 0 < k) (hi : CounterRun (ICounter k) i 1 m c)
    (hg : CounterRun (GCounter k) j m z e) :
    phi z + (2 ^ k - 1) * (q + (c + e) * 2) + c + (m - phi m) =
      1 + i + j * 2 + (2 ^ k - 1) * q := by
  have hm : 0 < m := ICounterRun_positive hi (by decide)
  have e0 := ICounterRun_balance hi
  have e1 := GCounterRun_balance hg hk hm
  have hpm : phi m ≤ m := (phi_bounds hm).2.1
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hp01 : 1 ≤ 2 ^ (1 + k) := pow2_pos (1 + k)
  zify [hp0, hp01, hpm] at hp0 hp01 hpm e0 e1 hp1 ⊢
  ring_nf at e0 e1 hp1 ⊢
  linarith

theorem pure_odd_boundary_closed {h a b : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hn : Num n r) (hbound : n * 2 + 1 ≤ a * 8) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ a +> (t +> r)))) [tm1]⊢⁺ c := by
  have hb := Level_bounds hl
  obtain ⟨s, hs, hstep⟩ := pure_odd_boundary hl.level_frame hn
  refine ⟨_, ?_, hstep⟩
  have h_w0 : (fs ++ w ^ a ++ d) +> s = (fs ++ w ^ a ++ d) +> (w ^ 0 +> s) := rfl
  rw [h_w0]
  exact .sroot (1 + h) (a + b) (a * 2 + 1) 0 (fs ++ w ^ a ++ d) s
    (Level_next hl) (by omega) (.SNum _ s hs (by omega))

theorem pure_three_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hn : Num n r) (hbound : n * 4 + 3 ≤ a * 8) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (t +> (t +> r))))) [tm1]⊢⁺ c := by
  have hb := Level_bounds hl
  obtain ⟨s, hs, hstep⟩ := pure_three hl.level_frame hj hn
  exact ⟨_, .sroot h a b (j + 1) fs s hl (by omega) (.SNum _ s hs (by omega)), hstep⟩

theorem pure_one_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hn : Num n r) (hbound : n * 4 + 1 ≤ a * 8) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (t +> ([0, 0] +> r))))) [tm1]⊢⁺ c := by
  have hb := Level_bounds hl
  rcases hl with ⟨hf, hh, hsize⟩
  obtain ⟨k, q, z, c, xs, s, hk, he, hc, hw, hs, hstep⟩ := pure_one hf hj hn
  have hwidth : k + 1 ≤ h + 1 := by
    have hlt : 2 ^ k < 2 ^ (h + 1) := by
      have : h + 1 = (h - 1) + 2 := by omega
      rw [this]
      have : 2 ^ ((h - 1) + 2) = 2 ^ (h - 1) * 4 := by ring
      nlinarith
    have := pow2_lt_iff.mp hlt
    omega
  have hodd : z % 2 = 1 := GCounterRun_odd hc rfl
  have hphase : SinglePhase h a b j (k + 1) z (q + c * 2) := by
    refine single_odd_phase (by omega) hwidth hodd (fun hwide => ?_)
    have hp : 2 ^ (h - 1) ≤ 2 ^ (k + 1) := pow2_mono (by omega)
    have h_lin_bound : 3 + (a - j - 1) * 2 < 2 ^ (1 + (k + 1)) := by
      have : 2 ^ (1 + (k + 1)) = 2 ^ (k + 1) * 2 := by ring
      omega
    obtain ⟨hz, _⟩ := GCounterRun_linear hc h_lin_bound
    exact ⟨by omega, Or.inr hj⟩
  have hvalue : phi z + (2 ^ (k + 1) - 1) * (q + c * 2) ≤ (a * 2 + b + 1) * 4 := by
    have e := GCounterRun_balance hc (by omega) (by decide)
    have h_phi3 : phi 3 = 3 := rfl
    rw [h_phi3] at e
    have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
    have hp0 : 1 ≤ 2 ^ k := pow2_pos k
    have hp01 : 1 ≤ 2 ^ k * 2 := by omega
    have haj1 : 1 ≤ a - j := by omega
    have haj : j ≤ a := by omega
    rw [hp1] at e ⊢
    zify [hp0, hp01, haj1, haj] at hp0 hp01 haj1 haj e he hb hbound ⊢
    nlinarith
  have hz_pos : 0 < z := by omega
  exact ⟨_, .sroot h a b j fs (xs +> s) ⟨hf, hh, hsize⟩ (by omega)
    (.SWord (k + 1) z (q + c * 2) xs s (by omega) hz_pos hw hs hphase hvalue), hstep⟩

theorem even_birth_phase {h a b j : ℕ} {fs : List Sym} {n k q m c z e : ℕ}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : n ≤ a * 4) (hk : 2 ≤ k)
    (he : n * 2 + j * 4 + 4 = (q * 2 + 1) * 2 ^ k)
    (hi : CounterRun (ICounter k) (b + j) 1 m c)
    (hg : CounterRun (GCounter k) (a - j) m z e) :
    SinglePhase h a b j k z (q + (c + e) * 2) := by
  have hb := Level_bounds hl
  rcases hl with ⟨hf, hh, hsize⟩
  have hm : 0 < m := ICounterRun_positive hi (by decide)
  have hwidth : k ≤ h + 1 := by
    have hle : 2 ^ k ≤ 2 ^ (h + 1) := by
      have : h + 1 = (h - 1) + 2 := by omega
      rw [this]
      have : 2 ^ ((h - 1) + 2) = 2 ^ (h - 1) * 4 := by ring
      nlinarith
    exact pow2_le_iff.mp hle
  by_cases hwide : h ≤ k + 1
  · have hp : 2 ^ (h - 1) ≤ 2 ^ k := pow2_mono (by omega)
    have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
    obtain ⟨ez, ee⟩ := GCounterRun_linear hg (by omega)
    subst em ec ez ee
    have h_q : q + (0 + 0) * 2 = q := by omega
    have h_z : 1 + (b + j) + (a - j) * 2 = a * 2 + b + 1 - j := by omega
    rw [h_q, h_z]
    refine .SX k q ?_
    by_cases hlo : h = k + 1
    · left
      refine ⟨hlo, ?_⟩
      have hk_sub : h - 1 = k := by omega
      rw [hk_sub] at hsize
      nlinarith
    · right
      by_cases hhi : k = h
      · left
        subst hhi
        refine ⟨rfl, ?_⟩
        have ep : 2 ^ k = 2 ^ (k - 1) * 2 := by
          have : k = (k - 1) + 1 := by omega
          conv_lhs => rw [this]
          ring
        nlinarith
      · right
        have ek : k = h + 1 := by omega
        subst ek
        have ep : 2 ^ (h + 1) = 2 ^ (h - 1) * 4 := by
          have : h + 1 = (h - 1) + 2 := by omega
          rw [this]
          ring
        refine ⟨rfl, by nlinarith, by nlinarith, by nlinarith⟩
  · have ht : Two a j z := by
      by_cases hz : z % 2 = 0
      · right
        obtain ⟨_, ez, _⟩ := GCounterRun_even hg hz
        omega
      · left; omega
    by_cases hk2 : k = 2
    · subst hk2
      exact .S2 z (q + (c + e) * 2) ht
    · refine .SN k z (q + (c + e) * 2) (by omega) (by omega) ?_
      by_cases hodd : z % 2 = 1
      · exact Or.inl hodd
      · have heven : z % 2 = 0 := by omega
        have hlower : (a - j) * 2 + 2 ≤ z := by
          rcases ht with h1 | h2 <;> omega
        right
        refine ⟨hlower, ?_⟩
        by_cases hsmall : k + 3 ≤ h
        · have hp : 2 ^ (2 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
          have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
          omega
        · have ek : k + 2 = h := by omega
          have hk_sub : h - 1 = 1 + k := by omega
          rw [hk_sub] at hsize
          obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
          obtain ⟨_, ez, _⟩ := GCounterRun_even hg heven
          omega

theorem even_birth_capacity {a b j n k q m c z e : ℕ}
    (hab : a ≤ b) (hba : b ≤ a + 1) (hj : j ≤ a) (hn : n ≤ a * 4) (hk : 0 < k)
    (he : n * 2 + j * 4 + 4 = (q * 2 + 1) * 2 ^ k)
    (hi : CounterRun (ICounter k) (b + j) 1 m c)
    (hg : CounterRun (GCounter k) (a - j) m z e) :
    phi z + (2 ^ k - 1) * (q + (c + e) * 2) ≤ (a * 2 + b + 1) * 4 := by
  have e_cap := split_capacity q hk hi hg
  have h1 : 2 ^ k - 1 ≤ 2 ^ k := Nat.sub_le _ _
  have h2 : (2 ^ k - 1) * q * 2 ≤ (q * 2 + 1) * 2 ^ k := by nlinarith
  omega

theorem even_birth_small_root {h a b j : ℕ} {fs : List Sym} {n q m c z e : ℕ}
    {xs : List Sym} {s : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : n ≤ a * 4)
    (he : n * 2 + j * 4 + 4 = (q * 2 + 1) * 2)
    (hi : CounterRun (ICounter 1) (b + j) 1 m c)
    (hg : CounterRun (GCounter 1) (a - j) m z e)
    (hw : Word 1 z xs) (hs : Num (q + (c + e) * 2) s) :
    SRoot (cfg (fs +> (w ^ j +> (xs +> s)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hm : 0 < m := ICounterRun_positive hi (by decide)
  have hz : 0 < z := GCounterRun_positive hg hm
  have hmb : m < 4 := ICounterRun_bound hi (by decide)
  have hzb : z < 4 := Word_bound hw
  have hvalue : phi z + (2 ^ 1 - 1) * (q + (c + e) * 2) ≤ (a * 2 + b + 1) * 4 :=
    even_birth_capacity hab hba hj hn (by decide) he hi hg
  by_cases hedge : j = a
  · exact .sroot h a b j fs (xs +> s) hl hj
      (.SWord 1 z (q + (c + e) * 2) xs s (by decide) hz hw hs (.S1 z _ (Or.inl hedge)) hvalue)
  · by_cases hz3 : z = 3
    · subst hz3
      have e0 := ICounterRun_balance hi
      have e1 := GCounterRun_balance hg (by decide) hm
      have hpm := phi_bounds hm
      have h_21 : 2 ^ (1 + 1) - 1 = 3 := rfl
      have h_20 : (2 ^ 1 - 1) * 2 = 2 := rfl
      have h_phi3 : phi 3 = 3 := rfl
      rw [h_21] at e0
      rw [h_20, h_phi3] at e1
      have htail : q + (c + e) * 2 ≤ a * 8 := by omega
      rw [Word_max hw rfl]
      change SRoot (cfg (fs +> (w ^ j +> (w +> s))))
      have en : w ^ j +> (w +> s) = w ^ (j + 1) +> s := by
        rw [pow_add_list w j 1, pow_one_list, append_assoc]
      rw [en]
      exact .sroot h a b (j + 1) fs s hl (by omega) (.SNum _ s hs htail)
    · have hu : a - j = 1 := by
        by_cases htwo : 2 ≤ a - j
        · have hrun : CounterRun (GCounter 1) (2 + (a - j - 2)) m z e := by
            have : 2 + (a - j - 2) = a - j := by omega
            rwa [this]
          obtain ⟨ez, _⟩ := GCounterRun_one hrun hm hmb
          omega
        · omega
      have ez : z = 1 := by
        by_cases heven : z % 2 = 0
        · obtain ⟨_, ez', _⟩ := GCounterRun_even hg heven
          omega
        · omega
      subst ez
      have htail : q + (c + e) * 2 + 1 ≤ (a * 2 + b + 1) * 2 := by
        have e_cap := split_capacity q (by decide) hi hg
        have h_phi1 : phi 1 = 1 := rfl
        have h_21 : 2 ^ 1 - 1 = 1 := rfl
        rw [h_phi1, h_21] at e_cap
        omega
      exact .sroot h a b j fs (xs +> s) hl hj
        (.SWord 1 1 (q + (c + e) * 2) xs s (by decide) (by decide) hw hs
          (.S1 1 _ (Or.inr ⟨by omega, rfl, htail⟩)) hvalue)

theorem pure_even_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hr : Num (n * 2) r) (hn : n ≤ a * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨k, q, m, c, z, e, xs, s, hk, he, hi, hg, hw, hs, hstep⟩ :=
    pure_even hl.level_frame hj hr
  refine ⟨_, ?_, hstep⟩
  by_cases hk1 : k = 1
  · subst hk1
    exact even_birth_small_root hl hj hn he hi hg hw hs
  · refine .sroot h a b j fs (xs +> s) hl hj (.SWord k z (q + (c + e) * 2) xs s hk ?_ hw hs ?_ ?_)
    · exact GCounterRun_positive hg (ICounterRun_positive hi (by decide))
    · exact even_birth_phase hl hj hn (by omega) he hi hg
    · exact even_birth_capacity hab hba hj hn hk he hi hg

theorem pure_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : Num n r) (hbound : n ≤ a * 8) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> r))) [tm1]⊢⁺ c := by
  cases hn with
  | Num0 =>
    exact pure_even_closed (n := 0) hl hj .Num0 (by omega)
  | Num00 n' hr =>
    exact pure_even_closed hl hj (.Num00 n' hr) (by omega)
  | Num10 n' hr =>
    by_cases hja : j = a
    · subst hja
      exact pure_odd_boundary_closed hl hr hbound
    · cases hr with
      | Num0 =>
        have h00 : ([0, 0] : List Sym) +> (default : ListBlank Sym) = default :=
          all0_spec (a := [0, 0]) rfl
        rw [← h00]
        exact pure_one_closed hl (by omega) .Num0 (by omega)
      | Num00 n'' hr' =>
        exact pure_one_closed hl (by omega) hr' (by omega)
      | Num10 n'' hr' =>
        exact pure_three_closed hl (by omega) hr' (by omega)

theorem small_single_root {h a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 0 < k) (hwidth : k + 3 ≤ h) (hn : 0 < n)
    (hw : Word k n xs) (hr : Num q r)
    (hcap : phi n + (2 ^ k - 1) * q ≤ (a * 2 + b + 1) * 2)
    (hlower : n % 2 = 0 → (a - j) * 2 + 2 ≤ n)
    (hsmall : k = 1 → j + 2 ≤ a → n = 3) :
    SRoot (cfg (fs +> (w ^ j +> (xs +> r)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  by_cases hk1 : k = 1
  · subst hk1
    have hnb : n < 4 := Word_bound hw
    by_cases hedge : j = a
    · exact .sroot h a b j fs (xs +> r) hl hj
        (.SWord 1 n q xs r (by decide) hn hw hr (.S1 n q (Or.inl hedge)) (by omega))
    · by_cases hn3 : n = 3
      · subst hn3
        rw [Word_max hw rfl]
        change SRoot (cfg (fs +> (w ^ j +> (w +> r))))
        have en : w ^ j +> (w +> r) = w ^ (j + 1) +> r := by
          rw [pow_add_list w j 1, pow_one_list, append_assoc]
        rw [en]
        refine .sroot h a b (j + 1) fs r hl (by omega) (.SNum q r hr ?_)
        have h_phi3 : phi 3 = 3 := rfl
        have h_21 : 2 ^ 1 - 1 = 1 := rfl
        rw [h_phi3, h_21] at hcap
        omega
      · have hnear : j + 1 = a := by
          have := hsmall rfl
          omega
        have en : n = 1 := by
          by_cases hev : n % 2 = 0
          · have := hlower hev
            omega
          · omega
        subst en
        refine .sroot h a b j fs (xs +> r) hl hj
          (.SWord 1 1 q xs r (by decide) (by decide) hw hr (.S1 1 q (Or.inr ⟨hnear, rfl, ?_⟩)) (by omega))
        have h_phi1 : phi 1 = 1 := rfl
        have h_21 : 2 ^ 1 - 1 = 1 := rfl
        rw [h_phi1, h_21] at hcap
        omega
  · refine .sroot h a b j fs (xs +> r) hl hj (.SWord k n q xs r hk hn hw hr ?_ (by omega))
    by_cases hk2 : k = 2
    · subst hk2
      refine .S2 n q ?_
      by_cases hodd : n % 2 = 1
      · exact Or.inl hodd
      · exact Or.inr (hlower (by omega))
    · refine .SN k n q (by omega) (by omega) ?_
      by_cases hodd : n % 2 = 1
      · exact Or.inl hodd
      · right
        refine ⟨hlower (by omega), ?_⟩
        have hp : 2 ^ (2 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
        omega

theorem narrow_closed {h a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 3 ≤ k) (hwidth : k + 2 ≤ h) (hn : 0 < n)
    (hw : Word k n xs) (hr : Num q r) (hguard : Narrow a j k n)
    (hcap : phi n + (2 ^ k - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hinner : n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + j * 4 := by
    rcases hguard with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have htail : ∀ c, ∃ s, Num (q + c * 2) s ∧ G c r s := fun c => G_nums c hr
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · by_cases hja : j = a
    · subst hja
      have hb_pow : 2 ^ (2 + k) ≤ b + j := by
        have hp : 2 ^ (4 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
        omega
      have hw' : Word ((2 + k) + 1) n xs := by
        have : (2 + k) + 1 = k + 3 := by omega
        rwa [this]
      have hinner' : n % 2 = 1 ∨ 2 ^ (1 + ((2 + k) + 1)) ≤ n + j * 4 := by
        have : 1 + ((2 + k) + 1) = 1 + (k + 3) := by omega
        rwa [this]
      have hcap' : phi n + (2 ^ ((2 + k) + 1) - 1) * q ≤ (j * 2 + b + 1) * 4 := by
        have : (2 + k) + 1 = k + 3 := by omega
        rwa [this]
      obtain ⟨z, c, ys, s, hys, hodd, hs, hg, hvalue, hcalls, hstep⟩ :=
        narrow_boundary (fun c => Num (q + c * 2)) (k := 2 + k)
          hl.level_frame hw' (by omega) hn htail hinner' hb_pow hcap'
      refine ⟨_, ?_, hstep⟩
      have h_w0 : (fs ++ w ^ j ++ d) +> (ys +> s) = (fs ++ w ^ j ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
      rw [h_w0]
      exact small_single_root (Level_next hl) (by omega) (by omega) (by omega) (by omega)
        hys hs (by omega) (by omega) (by omega)
    · have hb_pow : 2 ^ (2 + k) ≤ b + j := by
        have hp : 2 ^ (4 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
        omega
      have hB' : 2 ^ (1 + (1 + k)) ≤ b + j := by
        have : 1 + (1 + k) = 2 + k := by omega
        rwa [this]
      have hw' : Word ((1 + k) + 2) n xs := by
        have : (1 + k) + 2 = k + 3 := by omega
        rwa [this]
      have hinner' : n % 2 = 1 ∨ 2 ^ (1 + ((1 + k) + 2)) ≤ n + j * 4 := by
        have : 1 + ((1 + k) + 2) = 1 + (k + 3) := by omega
        rwa [this]
      have hcap' : phi n + (2 ^ ((1 + k) + 2) - 1) * q ≤ (a * 2 + b + 1) * 4 := by
        have : (1 + k) + 2 = k + 3 := by omega
        rwa [this]
      obtain ⟨z, c, ys, s, hys, hz, hs, hg, hvalue, hlower, hsmall, hcalls, hstep⟩ :=
        narrow_inside (fun c => Num (q + c * 2)) (k := 1 + k)
          hl.level_frame (by omega) hw' (by omega) hn htail hinner' hB' hcap'
      refine ⟨_, ?_, hstep⟩
      exact small_single_root hl (by omega) (by omega) (by omega) hz hys hs
        (by omega) (fun hev => by have := hlower hev; omega) (fun hk1 h2 => hsmall hk1 (by omega))

theorem end_single_root {h a b j : ℕ} {fs : List Sym} {n : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hr : Num n r)
    (hbirth : n + 4 < (a * 2 + b + 1) * 4)
    (hcap : n + (a - j) * 2 + 2 ≤ (a * 2 + b + 1) * 4) :
    ∃ s, G (a - j) (d +> r) s ∧ SRoot (cfg (fs +> (w ^ j +> s))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨k, q, z, c, xs, s, he, hc, hw, hs, hodd, hvalue, hg⟩ :=
    G_end_word (a - j) hr (by omega)
  refine ⟨xs +> s, hg, ?_⟩
  have hwidth : k + 1 ≤ h + 1 := by
    have hlt : 2 ^ k < 2 ^ (h + 1) := by
      have : h + 1 = (h - 1) + 2 := by omega
      rw [this]
      have : 2 ^ ((h - 1) + 2) = 2 ^ (h - 1) * 4 := by ring
      rw [← hl.level_size] at this
      nlinarith
    have := pow2_lt_iff.mp hlt
    omega
  rcases k with _ | k
  · have ez : z = 3 := by
      have hb : z < 4 := Word_bound hw
      rcases h_aj : a - j - 1 with _ | i'
      · rw [h_aj] at hc
        cases hc
        rfl
      · rw [h_aj] at hc
        have := GCounterRun_three hc (by omega) rfl
        omega
    subst ez
    have e := GCounterRun_balance hc (by decide) (by decide)
    have h_phi3 : phi 3 = 3 := rfl
    have h_21 : (2 ^ 1 - 1) * 2 = 2 := rfl
    rw [h_phi3, h_21] at e
    have htail : q + c * 2 ≤ a * 8 := by
      change n + 4 = (q * 2 + 1) * 1 at he
      omega
    rw [Word_max hw rfl]
    change SRoot (cfg (fs +> (w ^ j +> (w +> s))))
    have en : w ^ j +> (w +> s) = w ^ (j + 1) +> s := by
      rw [pow_add_list w j 1, pow_one_list, append_assoc]
    rw [en]
    exact .sroot h a b (j + 1) fs s hl (by omega) (.SNum _ s hs htail)
  · refine .sroot h a b j fs (xs +> s) hl (by omega)
      (.SWord (k + 2) z (q + c * 2) xs s (by omega) (by omega) hw hs ?_ (hvalue.trans hcap))
    refine single_odd_phase (by omega) hwidth hodd (fun hwide => ⟨?_, Or.inr hj⟩)
    have hp : 2 ^ (h - 1) ≤ 2 ^ (k + 2) := pow2_mono (by omega)
    rw [← hl.level_size] at hp
    have h_lin_bound : 3 + (a - j - 1) * 2 < 2 ^ (1 + (k + 2)) := by
      have : 2 ^ (1 + (k + 2)) = 2 ^ (k + 2) * 2 := by ring
      omega
    obtain ⟨ez, _⟩ := GCounterRun_linear hc h_lin_bound
    omega

theorem two_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : 0 < n)
    (hw : Word 2 n xs) (hr : Num q r) (hphase : Two a j n)
    (hcap : phi n + 3 * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hnb : n < 8 := Word_bound hw
  have hguard : n % 2 = 1 ∨ 8 ≤ n + j * 4 := by
    rcases hphase with h | h <;> [exact Or.inl h; (right; omega)]
  obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total 2 j n (by decide) hnb hguard
  obtain ⟨z, c₁, h1, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total 1 z' (by decide) hz')
    (b + j) u_val hub
  have hrun : CounterRun (GCounter 1) (2 + (b + j - 2)) u_val z c₁ := by
    have : 2 + (b + j - 2) = b + j := by omega
    rwa [this]
  obtain ⟨rfl, hc1lo, hc1hi⟩ := GCounterRun_one hrun hu hub
  have e0 := GCounterRun_balance h0 (by decide) hn
  rw [phi_odd] at e0
  have h_22 : (2 ^ 2 - 1) * 2 = 6 := rfl
  rw [h_22] at e0
  have hc0 : c₀ * 6 ≤ phi n + j * 4 + 1 := by omega
  by_cases hja : j = a
  · subst hja
    obtain ⟨s, hs, hg⟩ := G_nums (c₀ + c₁) hr
    refine ⟨_, ?_, two_boundary hl.level_frame hw hguard h0 h1 hg⟩
    have h_w1 : (fs ++ w ^ j ++ d) +> (w +> s) = (fs ++ w ^ j ++ d) +> (w ^ 1 +> s) := rfl
    rw [h_w1]
    exact .sroot (1 + h) (j + b) (j * 2 + 1) 1 (fs ++ w ^ j ++ d) s
      (Level_next hl) (by omega) (.SNum _ s hs (by omega))
  · obtain ⟨s, hs, hg⟩ := G_nums (c₀ + (c₁ + 2)) hr
    by_cases hedge : j + 1 = a
    · have hstep : (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (d +> s)))) := by
        refine two_inside hl.level_frame (by omega) hw hguard h0 h1 hg ?_
        have : a - j - 1 = 0 := by omega
        rw [this]
        exact .G0 _
      refine ⟨_, ?_, hstep⟩
      have h_eq : cfg (fs +> (w ^ (j + 1) +> (d +> s))) = cfg ((fs ++ w ^ a ++ d) +> (w ^ 0 +> s)) := by
        rw [hedge]
        simp only [Longitudinal.pow_zero_list, List.append_assoc, append_assoc, append_nil]
      rw [h_eq]
      exact .sroot (1 + h) (a + b) (a * 2 + 1) 0 (fs ++ w ^ a ++ d) s
        (Level_next hl) (by omega) (.SNum _ s hs (by omega))
    · obtain ⟨out, hout, hroot⟩ := end_single_root (j := j + 1) hl (by omega) hs (by omega) (by omega)
      refine ⟨cfg (fs +> (w ^ (j + 1) +> out)), hroot, ?_⟩
      refine two_inside hl.level_frame (by omega) hw hguard h0 h1 hg ?_
      have : a - j - 1 = a - (j + 1) := by omega
      rwa [this]

theorem one_boundary_closed {h a b : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hn : 0 < n) (hw : Word 1 n xs) (hr : Num q r)
    (hcap : phi n + q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hnb : n < 4 := Word_bound hw
  obtain ⟨z, c, hc, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total 1 z' (by decide) hz')
    (a * 2 + 2) n hnb
  have hrun : CounterRun (GCounter 1) (2 + a * 2) n z c := by
    have : 2 + a * 2 = a * 2 + 2 := by omega
    rwa [this]
  obtain ⟨rfl, hclo, hchi⟩ := GCounterRun_one hrun hn hnb
  obtain ⟨s, hs, hg⟩ := G_nums c hr
  obtain ⟨out, hout, hroot⟩ := end_single_root (j := 0) (Level_next hl) (by omega) hs (by omega) (by omega)
  refine ⟨cfg ((fs ++ w ^ a ++ d) +> out), hroot, ?_⟩
  refine one_boundary hl.level_frame hw (Or.inr (by omega)) hc hg ?_
  have : b + a = a + b - 0 := by omega
  rwa [this]

theorem one_neighbor_split {a b j : ℕ} {fs xs : List Sym} {r s : ListBlank Sym}
    {k n : ℕ} {ys : List Sym} {tail : ListBlank Sym} {m c : ℕ} {out : ListBlank Sym}
    (hf : Frame a b fs) (hj : j + 1 = a) (hw : Word 1 1 xs)
    (hg : G (j * 2 + 1) r s) (hmid : G (b + j) (d +> s) (ys +> tail))
    (hy : Word (k + 1) n ys) (hodd : n % 2 = 1)
    (hc : CounterRun (GCounter (k + 1)) 2 n (m * 2 + 1) c)
    (hout : G c tail out) :
    ∃ zs, Word k m zs ∧
      (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (zs +> out)))) := by
  obtain ⟨vs, hv, hp⟩ := P_counter_run hy (by omega) hodd hc hout
  obtain ⟨zs, hz, rfl⟩ := Word_odd_inv hv
  have hfirst : CounterRun (GCounter 1) (j * 2 + 2) 1 3 (j * 2 + 1) :=
    counter_one_start (j * 2 + 1)
  obtain ⟨ws, hws, hin⟩ := counter_inner hw (by decide) (Or.inl rfl) hfirst hg
  rw [Word_max hws rfl] at hin
  refine ⟨zs, hz, ?_⟩
  rw [pow_add_list w j 1, pow_one_list, append_assoc]
  refine frame_step hf ?_
  have hin' : Inner j (xs +> r) (t +> (d +> s)) := by
    simpa only [w, t, d, Longitudinal.pow_succ_list, Longitudinal.pow_zero_list,
      List.append_assoc, append_assoc, append_cons, append_nil] using hin
  have hgd : I (b + j) ([1] +> (t +> (d +> s))) (d +> (ys +> tail)) := by
    simpa only [d, t, append_cons, append_nil] using G_d hmid
  refine inner_column (by omega) hin' hgd ?_
  have : a - j = 1 := by omega
  rw [this]
  apply P_G
  have hpd := P_d hp
  simpa only [u, w, t, List.append_assoc, append_assoc, append_cons, append_nil] using hpd

theorem neighbor_birth_root {h a b : ℕ} {fs : List Sym} {q k t_val m c : ℕ}
    {xs : List Sym} {r : ListBlank Sym}
    (hl : Level h a b fs) (hq : q + 1 ≤ (a * 2 + b + 1) * 2)
    (he : q + a * 4 + 2 = (t_val * 2 + 1) * 2 ^ k)
    (hc : CounterRun (GCounter (k + 1)) (a + b) 3 (m * 2 + 1) c)
    (hm : 0 < m) (hw : Word k m xs) (hr : Num (t_val + c * 2) r) :
    SRoot (cfg (fs +> (w ^ a +> (xs +> r)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have e := GCounterRun_balance hc (by omega) (by decide)
  rw [phi_odd] at e
  have h_phi3 : phi 3 = 3 := rfl
  rw [h_phi3] at e
  have ebal : m + (2 ^ (k + 1) - 1) * c = a + b + 1 := by nlinarith
  have hbirth : q + a * 4 + 2 < (a * 2 + b + 1) * 4 := by omega
  by_cases hk0 : k = 0
  · subst hk0
    have hmb : m < 2 := Word_bound hw
    have hm1 : m = 1 := by omega
    subst hm1
    rw [Word_max hw rfl]
    change SRoot (cfg (fs +> (w ^ a +> (d +> r))))
    have h_eq : cfg (fs +> (w ^ a +> (d +> r))) = cfg ((fs ++ w ^ a ++ d) +> (w ^ 0 +> r)) := by
      simp only [Longitudinal.pow_zero_list, List.append_assoc, append_assoc, append_nil]
    rw [h_eq]
    refine .sroot (1 + h) (a + b) (a * 2 + 1) 0 (fs ++ w ^ a ++ d) r
      (Level_next hl) (by omega) (.SNum _ r hr ?_)
    have h_21 : 2 ^ 1 - 1 = 1 := rfl
    rw [h_21] at ebal
    change q + a * 4 + 2 = (t_val * 2 + 1) * 1 at he
    omega
  · have hwidth : k ≤ h := by
      have hlt : 2 ^ k < 2 ^ (h + 1) := by
        have : h + 1 = (h - 1) + 2 := by omega
        rw [this]
        have : 2 ^ ((h - 1) + 2) = 2 ^ (h - 1) * 4 := by ring
        rw [← hl.level_size] at this
        nlinarith
      have := pow2_lt_iff.mp hlt
      omega
    have hvalue : phi m + (2 ^ k - 1) * (t_val + c * 2) ≤ (a * 2 + b + 1) * 4 := by
      have hpm := phi_bounds hm
      have hp1 : 2 ^ (k + 1) = 2 ^ k * 2 := by ring
      have hp0 : 1 ≤ 2 ^ k := pow2_pos k
      have hp01 : 1 ≤ 2 ^ k * 2 := by omega
      rw [hp1] at ebal
      zify [hp0, hp01] at hp0 hp01 ebal he hq hpm hab hba ⊢
      nlinarith
    refine .sroot h a b a fs (xs +> r) hl (by omega)
      (.SWord k m (t_val + c * 2) xs r (by omega) hm hw hr ?_ hvalue)
    by_cases hwide : h ≤ k + 1
    · have hp : 2 ^ (h - 1) ≤ 2 ^ k := pow2_mono (by omega)
      rw [← hl.level_size] at hp
      have h_lin : 3 + (a + b) * 2 < 2 ^ (1 + (k + 1)) := by
        have : 2 ^ (1 + (k + 1)) = 2 ^ k * 4 := by ring
        omega
      obtain ⟨em, ec⟩ := GCounterRun_linear hc h_lin
      subst ec
      have h_t : t_val + 0 * 2 = t_val := by omega
      have h_m : m = a * 2 + b + 1 - a := by omega
      rw [h_t, h_m]
      refine .SX k t_val ?_
      by_cases heq : h = k + 1
      · left
        refine ⟨heq, ?_⟩
        have hsize := hl.level_size
        have hk_sub : h - 1 = k := by omega
        rw [hk_sub] at hsize
        nlinarith
      · right; left
        have ek : k = h := by omega
        refine ⟨ek, ?_⟩
        have hp' : 2 ^ k = (a * 2 + b + 1) * 2 := by
          rw [ek]
          have : h = (h - 1) + 1 := by omega
          conv_lhs => rw [this]
          rw [pow2_succ_right, ← hl.level_size]
        nlinarith
    · by_cases hone : k = 1
      · subst hone
        exact .S1 m (t_val + c * 2) (Or.inl rfl)
      · by_cases htwo : k = 2
        · subst htwo
          refine .S2 m (t_val + c * 2) ?_
          by_cases hodd : m % 2 = 1 <;> [exact Or.inl hodd; (right; omega)]
        · refine .SN k m (t_val + c * 2) (by omega) (by omega) ?_
          by_cases hodd : m % 2 = 1
          · exact Or.inl hodd
          · right
            refine ⟨by omega, ?_⟩
            have hp : 2 ^ (1 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
            rw [← hl.level_size] at hp
            omega

theorem one_neighbor_closed {h a b j : ℕ} {fs : List Sym} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j + 1 = a) (hw : Word 1 1 xs) (hr : Num q r)
    (hq : q + 1 ≤ (a * 2 + b + 1) * 2) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨s, hs, hg⟩ := G_nums (j * 2 + 1) hr
  obtain ⟨k, t_val, n, c, ys, tail, he, hc, hy, htail, hodd, hvalue, hmid⟩ :=
    G_end_word (b + j) hs (by omega)
  obtain ⟨m, c', hm, hmb, hlast⟩ :=
    counter_inner_total (k + 1) 0 n (by omega) (Word_bound hy) (Or.inl hodd)
  obtain ⟨out, hout, hfinal⟩ := G_nums c' htail
  obtain ⟨zs, hz, hstep⟩ :=
    one_neighbor_split hl.level_frame hj hw hg hmid hy hodd hlast hfinal
  refine ⟨_, ?_, hstep⟩
  rw [hj]
  have hrun := CounterRun_add hc hlast
  have hrun' : CounterRun (GCounter (k + 1)) (a + b) 3 (m * 2 + 1) (c + c') := by
    have : b + j - 1 + (0 * 2 + 2) = a + b := by omega
    rwa [this] at hrun
  have hout' : Num (t_val + (c + c') * 2) out := by
    have : t_val + (c + c') * 2 = t_val + c * 2 + c' * 2 := by omega
    rwa [this]
  exact neighbor_birth_root hl hq (by omega) hrun' hm hz hout'

inductive Atom : ℕ → ℕ → ℕ → ListBlank Sym → Prop where
  | AtomWord (k tau n q : ℕ) (xs : List Sym) (r : ListBlank Sym) :
      0 < k → 0 < n → Word k n xs → Num q r →
      tau ≤ 2 ^ k → (n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + tau * 2) →
      Atom k tau (phi n + (2 ^ k - 1) * q) (xs +> r)
  | AtomEnd (q : ℕ) (r : ListBlank Sym) :
      Num q r → q ≤ 1 → Atom 1 1 (q * 2 + 1) (d +> r)

inductive Sat (L : ℕ) : ℕ → ListBlank Sym → Prop where
  | SatWord (k n q : ℕ) (xs : List Sym) (r : ListBlank Sym) :
      0 < k → k ≤ L → Word k n xs → Num q r →
      n % 2 = 1 → (k = 1 → n = 3) →
      Sat L (phi n + (2 ^ k - 1) * q) (xs +> r)

theorem Atom_value {k tau x : ℕ} {r : ListBlank Sym} (h : Atom k tau x r) : Value x r := by
  cases h with
  | AtomWord k tau n q xs r hk hn hw hr _ _ =>
    exact .ValueWord hk hn hw (.ValueNum hr)
  | AtomEnd q r hr hq =>
    exact .ValueEnd hr hq

theorem Atom_bound {k tau x : ℕ} {r : ListBlank Sym} (h : Atom k tau x r) :
    0 < k ∧ tau ≤ 2 ^ k := by
  cases h with
  | AtomWord _ _ _ _ _ _ hk _ _ _ htau _ => exact ⟨hk, htau⟩
  | AtomEnd _ _ _ _ => decide

theorem Sat_value {L x : ℕ} {r : ListBlank Sym} (h : Sat L x r) : Value x r := by
  cases h with
  | SatWord k n q xs r hk _ hw hr hodd _ =>
    exact .ValueWord hk (by omega) hw (.ValueNum hr)

theorem Sat_mono {L M x : ℕ} {r : ListBlank Sym} (h : Sat L x r) (hle : L ≤ M) :
    Sat M x r := by
  cases h with
  | SatWord k n q xs r hk hL hw hr hodd h1 =>
    exact .SatWord k n q xs r hk (by omega) hw hr hodd h1

theorem G_word_data {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym} (i : ℕ)
    (hk : 0 < k) (hw : Word k n xs) (hr : Num q r) :
    ∃ m c ys s, CounterRun (GCounter k) i n m c ∧
      Word k m ys ∧ Num (q + c * 2) s ∧ G i (xs +> r) (ys +> s) := by
  obtain ⟨m, c, hc, _⟩ := CounterRun_total (fun n' hn' => GCounter_total k n' hk hn') i n (Word_bound hw)
  obtain ⟨s, hs, hg⟩ := G_nums c hr
  obtain ⟨ys, hy, hrun⟩ := G_counter_run hw hk hc hg
  exact ⟨m, c, ys, s, hc, hy, hs, hrun⟩

theorem GCounterRun_one_three {i n m c : ℕ} (h : CounterRun (GCounter 1) i n m c) (hn : n = 3) :
    m = 3 := by
  induction h with
  | Counter0 _ => exact hn
  | CounterS hs _ ih =>
    apply ih
    cases hs with
    | GCinc hlt =>
      have : 2 ^ (1 + 1) = 4 := rfl
      omega
    | GCev heq =>
      have : 2 ^ (1 + 1) = 4 := rfl
      omega
    | GCod _ => rfl

theorem G_sat {L x : ℕ} {r : ListBlank Sym} (i : ℕ) (hsat : Sat L x r) :
    ∃ s, Sat L (x + i * 2) s ∧ G i r s := by
  rcases hsat with ⟨k, n, q, xs, r, hk, hL, hw, hr, hodd, hsmall⟩
  obtain ⟨m, c, ys, s, hc, hy, hs, hg⟩ := G_word_data i hk hw hr
  refine ⟨ys +> s, ?_, hg⟩
  have e := GCounterRun_balance hc hk (by omega)
  have h_eq : phi n + (2 ^ k - 1) * q + i * 2 = phi m + (2 ^ k - 1) * (q + c * 2) := by
    nlinarith
  rw [h_eq]
  exact .SatWord k m (q + c * 2) ys s hk hL hy hs (GCounterRun_odd hc hodd)
    (fun ek => by subst ek; exact GCounterRun_one_three hc (hsmall rfl))

theorem G_atom_sat {k tau x : ℕ} {r : ListBlank Sym} (i : ℕ)
    (h : Atom k tau x r) (hi : 2 ≤ i) (htau : tau ≤ i) :
    ∃ s, Sat (Nat.max k 3) (x + i * 2) s ∧ G i r s := by
  cases h with
  | AtomWord k tau n q xs r hk hn hw hr htb hguard =>
    obtain ⟨m, c, ys, s, hc, hy, hs, hg⟩ := G_word_data i hk hw hr
    refine ⟨ys +> s, ?_, hg⟩
    have e := GCounterRun_balance hc hk hn
    have h_eq : phi n + (2 ^ k - 1) * q + i * 2 = phi m + (2 ^ k - 1) * (q + c * 2) := by
      nlinarith
    rw [h_eq]
    refine .SatWord k m (q + c * 2) ys s hk (Nat.le_max_left k 3) hy hs ?_ ?_
    · rcases hguard with hodd | hsat
      · exact GCounterRun_odd hc hodd
      · exact GCounterRun_saturated hc hk (Word_bound hw) (by omega)
    · intro ek
      subst ek
      have hc' : CounterRun (GCounter 1) (2 + (i - 2)) n m c := by
        have : 2 + (i - 2) = i := by omega
        rwa [this]
      exact (GCounterRun_one hc' hn (Word_bound hw)).1
  | AtomEnd q r hr hq =>
    have hfirst : ∃ s, Sat 3 (q * 2 + 3) s ∧ G1 (d +> r) s := by
      by_cases hq0 : q = 0
      · rw [Num_zero hr hq0]
        subst hq0
        refine ⟨(t ++ one 2) +> default, ?_, G_zero0⟩
        exact Sat.SatWord (L := 3) 3 3 0 (t ++ one 2) default
          (by decide) (by decide) (.Word10 2 1 (Word_one 2)) .Num0 rfl (by decide)
      · have hq1 : q = 1 := by omega
        rw [Num_one hr hq1]
        subst hq1
        refine ⟨w +> ([0, 0, 1, 0] +> default), ?_, G_zero1⟩
        exact Sat.SatWord (L := 3) 1 3 2 w ([0, 0, 1, 0] +> default)
          (by decide) (by decide) (.Word10 0 1 .Word1) (.Num00 1 (.Num10 0 .Num0)) rfl (fun _ => rfl)
    obtain ⟨s₀, h0, g0⟩ := hfirst
    obtain ⟨s, hs, hg⟩ := G_sat (i - 1) h0
    refine ⟨s, ?_, ?_⟩
    · have : q * 2 + 1 + i * 2 = q * 2 + 3 + (i - 1) * 2 := by omega
      rwa [this]
    · have : i = (i - 1) + 1 := by omega
      rw [this]
      exact .GS g0 hg

theorem sat_single_root {h a b j : ℕ} {fs : List Sym} {x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hsat : Sat (h - 2) x r)
    (hcap : x ≤ (a * 2 + b + 1) * 2) :
    SRoot (cfg (fs +> (w ^ j +> r))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  rcases hsat with ⟨k, n, q, xs, r, hk, hL, hw, hr, hodd, hsmall⟩
  by_cases hk1 : k = 1
  · subst hk1
    have hn3 : n = 3 := hsmall rfl
    subst hn3
    by_cases hedge : j = a
    · exact .sroot h a b j fs (xs +> r) hl hj
        (.SWord 1 3 q xs r (by decide) (by decide) hw hr (.S1 3 q (Or.inl hedge)) (by omega))
    · rw [Word_max hw rfl]
      change SRoot (cfg (fs +> (w ^ j +> (w +> r))))
      have en : w ^ j +> (w +> r) = w ^ (j + 1) +> r := by
        rw [pow_add_list w j 1, pow_one_list, append_assoc]
      rw [en]
      refine .sroot h a b (j + 1) fs r hl (by omega) (.SNum q r hr ?_)
      have h_phi3 : phi 3 = 3 := rfl
      have h_21 : 2 ^ 1 - 1 = 1 := rfl
      rw [h_phi3, h_21] at hcap
      omega
  · refine .sroot h a b j fs (xs +> r) hl hj
      (.SWord k n q xs r hk (by omega) hw hr ?_ (by omega))
    by_cases hk2 : k = 2
    · subst hk2
      exact .S2 n q (Or.inl hodd)
    · exact .SN k n q (by omega) (by omega) (Or.inl hodd)

theorem d_sat_finish {h a b j : ℕ} {fs : List Sym} {x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hsat : Sat (h - 2) x r)
    (hbirth : x + 5 < (a * 2 + b + 1) * 4)
    (hcap : x + (a - j) * 4 + 3 ≤ (a * 2 + b + 1) * 4) :
    ∃ child s, P 1 (d +> r) (w +> child) ∧ G (a - j) child s ∧
      SRoot (cfg (fs +> (w ^ j +> s))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  rcases hsat with ⟨k, n, q, xs, r, hk, hL, hw, hr, hodd, hsmall⟩
  rcases k with _ | _ | k
  · omega
  · have hn3 : n = 3 := hsmall rfl
    subst hn3
    rw [Word_max hw rfl]
    change ∃ child s, P 1 (d +> (w +> r)) (w +> child) ∧ G (a - j) child s ∧
      SRoot (cfg (fs +> (w ^ j +> s)))
    obtain ⟨r₀, h0, g0⟩ := G_nums 2 hr
    have h_phi3 : phi 3 = 3 := rfl
    have h_21 : 2 ^ 1 - 1 = 1 := rfl
    rw [h_phi3, h_21, Nat.one_mul] at hbirth hcap
    have hfirst : P 1 (d +> (w +> r)) (w +> (d +> r₀)) := by
      have hp := P_d (G_w g0)
      simpa only [u, w, d, append_assoc, append_cons, append_nil] using hp
    by_cases hja : j = a
    · subst hja
      refine ⟨d +> r₀, d +> r₀, hfirst, ?_, ?_⟩
      · have : j - j = 0 := by omega
        rw [this]
        exact .G0 _
      · have h_eq : cfg (fs +> (w ^ j +> (d +> r₀))) = cfg ((fs ++ w ^ j ++ d) +> (w ^ 0 +> r₀)) := by
          simp only [Longitudinal.pow_zero_list, List.append_assoc, append_assoc, append_nil]
        rw [h_eq]
        exact .sroot (1 + h) (j + b) (j * 2 + 1) 0 (fs ++ w ^ j ++ d) r₀
          (Level_next hl) (by omega) (.SNum _ r₀ h0 (by omega))
    · obtain ⟨s, hs, hroot⟩ := end_single_root (j := j) hl (by omega) h0 (by omega) (by omega)
      exact ⟨d +> r₀, s, hfirst, hs, hroot⟩
  · have hw' : Word ((k + 1) + 1) n xs := hw
    obtain ⟨z, c, ys, s, hy, hz, hs, hvalue, hlower, hsmall', hp, child, hfirst, hrest⟩ :=
      odd_d_value Num (k := k + 1) (a - j) hw' (by omega) hodd (fun c => G_nums c hr)
    refine ⟨child, ys +> s, hfirst, hrest, ?_⟩
    exact small_single_root hl hj (by omega) (by omega) hz hy hs
      (by omega) (fun hev => by have := hlower hev; omega) (fun hk1 h2 => hsmall' hk1 (by omega))

theorem d_sat_root {h a b j : ℕ} {fs : List Sym} {x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hsat : Sat (h - 2) x r)
    (hbirth : x + 5 < (a * 2 + b + 1) * 4)
    (hcap : x + (a - j) * 4 ≤ (a * 2 + b + 1) * 4) :
    ∃ s, P (a - j) (d +> r) s ∧ SRoot (cfg (fs +> (w ^ j +> s))) := by
  obtain ⟨child, s, hfirst, hrest, hroot⟩ :=
    d_sat_finish (j := j + 1) hl (by omega) hsat hbirth (by omega)
  refine ⟨w +> s, ?_, ?_⟩
  · have : a - j = 1 + (a - (j + 1)) := by omega
    rw [this]
    exact P_add hfirst (G_w hrest)
  · rw [pow_add_list w j 1, pow_one_list, append_assoc] at hroot
    exact hroot

theorem atom_level_budget {h a b : ℕ} {fs : List Sym} {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hwidth : l + 2 ≤ h) (hr : Atom l tau x r) :
    tau ≤ a * 2 - 1 := by
  have hb := Level_bounds hl
  have hab := Atom_bound hr
  have hp : 2 ^ (1 + l) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
  rw [← hl.level_size] at hp
  have : 2 ^ (1 + l) = 2 ^ l * 2 := by ring
  omega

theorem atom_sat_level {h a b : ℕ} {fs : List Sym} {l tau x : ℕ} {r : ListBlank Sym} (i : ℕ)
    (hl : Level h a b fs) (hwidth : l + 2 ≤ h) (hr : Atom l tau x r)
    (hi : 2 ≤ i) (htau : tau ≤ i) :
    ∃ s, Sat (h - 2) (x + i * 2) s ∧ G i r s := by
  have hh := hl.level_height
  obtain ⟨s, hs, hg⟩ := G_atom_sat i hr hi htau
  exact ⟨s, Sat_mono hs (Nat.max_le.mpr ⟨by omega, by omega⟩), hg⟩

theorem two_count_bounds {b j n u_val c₀ c₁ : ℕ}
    (hn : 0 < n) (hnb : n < 8) (hguard : n % 2 = 1 ∨ 8 ≤ n + j * 4)
    (h0 : CounterRun (GCounter 2) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter 1) (b + j) u_val 3 c₁) :
    c₀ * 6 ≤ phi n + j * 4 + 1 ∧ b + j - 1 ≤ c₁ ∧ c₁ ≤ b + j := by
  have hphase := counter_inner_phase (by decide) hnb hguard h0
  have hub : u_val * 2 + 1 < 8 := GCounterRun_bound h0 (by decide) hnb
  have hu : 0 < u_val := by omega
  have hpu := phi_bounds hu
  have e0 := GCounterRun_balance h0 (by decide) hn
  have e1 := GCounterRun_balance h1 (by decide) hu
  rw [phi_odd] at e0
  have h_22 : (2 ^ 2 - 1) * 2 = 6 := rfl
  have h_21 : (2 ^ 1 - 1) * 2 = 2 := rfl
  have h_phi3 : phi 3 = 3 := rfl
  rw [h_22] at e0
  rw [h_21, h_phi3] at e1
  exact ⟨by omega, by omega, by omega⟩

theorem double_two_closed {h a b j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym} {u_val c₀ c₁ : ℕ}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : 0 < n) (hw : Word 2 n xs) (hphase : Two a j n)
    (hr : Atom l tau x r) (hwidth : l + 2 ≤ h)
    (h0 : CounterRun (GCounter 2) (j * 2 + 2) n (u_val * 2 + 1) c₀)
    (h1 : CounterRun (GCounter 1) (b + j) u_val 3 c₁)
    (hbudget : j = a ∨ tau ≤ c₀ + c₁ + 2)
    (hcap : phi n + 3 * x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hnb : n < 8 := Word_bound hw
  have hguard : n % 2 = 1 ∨ 8 ≤ n + j * 4 := by
    rcases hphase with h | h <;> [exact Or.inl h; (right; omega)]
  obtain ⟨hc0, hc1lo, hc1hi⟩ := two_count_bounds hn hnb hguard h0 h1
  by_cases hja : j = a
  · subst hja
    have htau := atom_level_budget hl hwidth hr
    obtain ⟨s, hs, hg⟩ := atom_sat_level (c₀ + c₁) hl hwidth hr (by omega) (by omega)
    refine ⟨_, ?_, two_boundary hl.level_frame hw hguard h0 h1 hg⟩
    have h_w1 : (fs ++ w ^ j ++ d) +> (w +> s) = (fs ++ w ^ j ++ d) +> (w ^ 1 +> s) := rfl
    rw [h_w1]
    exact sat_single_root (Level_next hl) (by omega) (Sat_mono hs (by omega)) (by omega)
  · obtain ⟨s, hs, hg⟩ := atom_sat_level (c₀ + (c₁ + 2)) hl hwidth hr (by omega) (by omega)
    by_cases hedge : j + 1 = a
    · have hstep : (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (d +> s)))) := by
        refine two_inside hl.level_frame (by omega) hw hguard h0 h1 hg ?_
        have : a - j - 1 = 0 := by omega
        rw [this]
        exact .G0 _
      refine ⟨_, ?_, hstep⟩
      have h_eq : cfg (fs +> (w ^ (j + 1) +> (d +> s))) = cfg ((fs ++ w ^ a ++ d) +> (w ^ 0 +> s)) := by
        rw [hedge]
        simp only [Longitudinal.pow_zero_list, List.append_assoc, append_assoc, append_nil]
      rw [h_eq]
      exact sat_single_root (Level_next hl) (by omega) (Sat_mono hs (by omega)) (by omega)
    · obtain ⟨out, hout, hroot⟩ := d_sat_root (j := j + 1) hl (by omega) hs (by omega) (by omega)
      refine ⟨cfg (fs +> (w ^ (j + 1) +> out)), hroot, ?_⟩
      refine two_inside hl.level_frame (by omega) hw hguard h0 h1 hg ?_
      have : a - j - 1 = a - (j + 1) := by omega
      rw [this]
      exact P_G hout

theorem double_one_boundary_closed {h a b : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hn : 0 < n) (hw : Word 1 n xs)
    (hr : Atom l tau x r) (hwidth : l + 2 ≤ h)
    (hcap : phi n + x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hnb : n < 4 := Word_bound hw
  obtain ⟨z, c, hc, hzb⟩ := CounterRun_total (fun z' hz' => GCounter_total 1 z' (by decide) hz')
    (a * 2 + 2) n hnb
  have hrun : CounterRun (GCounter 1) (2 + a * 2) n z c := by
    have : 2 + a * 2 = a * 2 + 2 := by omega
    rwa [this]
  obtain ⟨rfl, hclo, hchi⟩ := GCounterRun_one hrun hn hnb
  have htau := atom_level_budget hl hwidth hr
  obtain ⟨s, hs, hg⟩ := atom_sat_level c hl hwidth hr (by omega) (by omega)
  have hs' : Sat ((1 + h) - 2) (x + c * 2) s := Sat_mono hs (by omega)
  obtain ⟨out, hout, hroot⟩ := d_sat_root (j := 0) (Level_next hl) (by omega) hs' (by omega) (by omega)
  refine ⟨cfg ((fs ++ w ^ a ++ d) +> out), hroot, ?_⟩
  refine one_boundary hl.level_frame hw (Or.inr (by omega)) hc hg ?_
  have : b + a = a + b - 0 := by omega
  rw [this]
  exact P_G hout

theorem double_one_neighbor_closed {h a b j : ℕ} {fs : List Sym} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j + 1 = a) (hw : Word 1 1 xs)
    (hr : Atom l tau x r) (hwidth : l + 2 ≤ h)
    (hcap : 1 + x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have htau := atom_level_budget hl hwidth hr
  obtain ⟨s, hs, hg⟩ := atom_sat_level (j * 2 + 1) hl hwidth hr (by omega) (by omega)
  have hs' : Sat ((1 + h) - 2) (x + (j * 2 + 1) * 2) s := Sat_mono hs (by omega)
  obtain ⟨child, out, hfirst, hrest, hroot⟩ :=
    d_sat_finish (j := 0) (Level_next hl) (by omega) hs' (by omega) (by omega)
  have hsplit : G ((b + j - 1) + 2) child out := by
    have : (b + j - 1) + 2 = a + b - 0 := by omega
    rwa [this]
  obtain ⟨mid, hbefore, hafter⟩ := G_split (b + j - 1) 2 hsplit
  have hmid : G (b + j) (d +> s) (w +> mid) := by
    apply P_G
    have : b + j = 1 + (b + j - 1) := by omega
    rw [this]
    exact P_add hfirst (G_w hbefore)
  refine ⟨cfg ((fs ++ w ^ a ++ d) +> out), hroot, ?_⟩
  have ha_eq : a = 1 + j := by omega
  have hf' : Frame (1 + j) b fs := by
    rw [← ha_eq]
    exact hl.level_frame
  have hstep := one_neighbor hf' hw hg hmid hafter
  rwa [← ha_eq] at hstep

inductive DoublePhase (h a b j : ℕ) : ℕ → ℕ → ℕ → ℕ → Prop where
  | DN (k n l tau : ℕ) :
      3 ≤ k → k + 2 ≤ h → Narrow a j k n → k + l ≤ h →
      DoublePhase h a b j k n l tau
  | DY (l tau : ℕ) :
      l ≤ 1 → DoublePhase h a b j (h - 1) ((a - j) * 2 + 1) l tau
  | D2 (n l tau : ℕ) :
      Two a j n → l + 2 ≤ h → (j = a ∨ tau ≤ b + j + 1) →
      DoublePhase h a b j 2 n l tau
  | D1 (n l tau : ℕ) :
      l + 2 ≤ h → (j = a ∨ (j + 1 = a ∧ n = 1)) →
      DoublePhase h a b j 1 n l tau

inductive Double (h a b j : ℕ) : ListBlank Sym → Prop where
  | DWord (k n : ℕ) (xs : List Sym) (l tau x : ℕ) (r : ListBlank Sym) :
      0 < k → 0 < n → Word k n xs → Atom l tau x r →
      DoublePhase h a b j k n l tau → phi n + (2 ^ k - 1) * x ≤ (a * 2 + b + 1) * 4 →
      Double h a b j (xs +> r)

inductive DRoot : Cfg Sym Q → Prop where
  | droot (h a b j : ℕ) (fs : List Sym) (r : ListBlank Sym) :
      Level h a b fs → j ≤ a → Double h a b j r → DRoot (cfg (fs +> (w ^ j +> r)))

def Normal (c : Cfg Sym Q) : Prop := SRoot c ∨ DRoot c

theorem sat_double_root {h a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {L x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 0 < k) (hwidth : k + 3 ≤ h) (hn : 0 < n)
    (hw : Word k n xs) (hr : Sat L x r)
    (hrank : k + L ≤ h) (hL : L + 2 ≤ h)
    (hcap : phi n + (2 ^ k - 1) * x ≤ (a * 2 + b + 1) * 2)
    (hlower : n % 2 = 0 → (a - j) * 2 + 2 ≤ n)
    (hsmall : k = 1 → j + 2 ≤ a → n = 3) :
    Normal (cfg (fs +> (w ^ j +> (xs +> r)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  rcases hr with ⟨l, z, q, ys, s, hlpos, hlL, hy, hs, hodd, hthree⟩
  have hsat_r : Sat L (phi z + (2 ^ l - 1) * q) (ys +> s) :=
    .SatWord l z q ys s hlpos hlL hy hs hodd hthree
  have hat : Atom l 0 (phi z + (2 ^ l - 1) * q) (ys +> s) :=
    .AtomWord l 0 z q ys s hlpos (by omega) hy hs (Nat.zero_le _) (Or.inl hodd)
  by_cases hk1 : k = 1
  · subst hk1
    have hnb : n < 4 := Word_bound hw
    by_cases hedge : j = a
    · right
      exact .droot h a b j fs (xs +> (ys +> s)) hl hj
        (.DWord 1 n xs l 0 _ (ys +> s) (by decide) hn hw hat
          (.D1 n l 0 (by omega) (Or.inl hedge)) (by omega))
    · by_cases hn3 : n = 3
      · subst hn3
        left
        rw [Word_max hw rfl]
        change SRoot (cfg (fs +> (w ^ j +> (w +> (ys +> s)))))
        have en : w ^ j +> (w +> (ys +> s)) = w ^ (j + 1) +> (ys +> s) := by
          rw [pow_add_list w j 1, pow_one_list, append_assoc]
        rw [en]
        refine sat_single_root hl (by omega) (Sat_mono hsat_r (by omega)) ?_
        have h_phi3 : phi 3 = 3 := rfl
        have h_21 : 2 ^ 1 - 1 = 1 := rfl
        rw [h_phi3, h_21] at hcap
        omega
      · have hnear : j + 1 = a := by
          have := hsmall rfl
          omega
        have en : n = 1 := by
          by_cases hev : n % 2 = 0
          · have := hlower hev
            omega
          · omega
        subst en
        right
        exact .droot h a b j fs (xs +> (ys +> s)) hl hj
          (.DWord 1 1 xs l 0 _ (ys +> s) (by decide) (by decide) hw hat
            (.D1 1 l 0 (by omega) (Or.inr ⟨hnear, rfl⟩)) (by omega))
  · right
    refine .droot h a b j fs (xs +> (ys +> s)) hl hj
      (.DWord k n xs l 0 _ (ys +> s) hk hn hw hat ?_ (by omega))
    by_cases hk2 : k = 2
    · subst hk2
      refine .D2 n l 0 ?_ (by omega) (Or.inr (by omega))
      by_cases hodd' : n % 2 = 1
      · exact Or.inl hodd'
      · exact Or.inr (hlower (by omega))
    · refine .DN k n l 0 (by omega) (by omega) ?_ (by omega)
      by_cases hodd' : n % 2 = 1
      · exact Or.inl hodd'
      · right
        refine ⟨hlower (by omega), ?_⟩
        have hp : 2 ^ (2 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
        omega

theorem G_atom_ready {k tau x : ℕ} {r : ListBlank Sym} (hr : Atom k tau x r) (i : ℕ) :
    ∃ s, (tau ≤ i → 2 ≤ i → Sat (Nat.max k 3) (x + i * 2) s) ∧ G i r s := by
  by_cases htau : tau ≤ i
  · by_cases hi : 2 ≤ i
    · obtain ⟨s, hs, hg⟩ := G_atom_sat i hr hi htau
      exact ⟨s, fun _ _ => hs, hg⟩
    · obtain ⟨s, _, hg⟩ := G_value (Atom_value hr) i
      exact ⟨s, fun _ h2 => by omega, hg⟩
  · obtain ⟨s, _, hg⟩ := G_value (Atom_value hr) i
    exact ⟨s, fun ht _ => by omega, hg⟩

theorem level_call_scale {h a b : ℕ} {fs : List Sym} (k : ℕ)
    (hl : Level h a b fs) (hk : k ≤ h) :
    (a * 2 + b + 1) * 4 = 2 ^ (1 + k) * 2 ^ (h - k) := by
  have hh := hl.level_height
  rw [← Nat.pow_add]
  have h_exp : 1 + k + (h - k) = (h - 1) + 2 := by omega
  rw [h_exp]
  have : 2 ^ ((h - 1) + 2) = 2 ^ (h - 1) * 4 := by ring
  rw [this, ← hl.level_size]

theorem narrow_calls_saturate {h a b : ℕ} {fs : List Sym} {k l tau x : ℕ} {r : ListBlank Sym} {c : ℕ}
    (hl : Level h a b fs) (hwidth : k + 2 ≤ h) (hrank : k + l ≤ h)
    (hr : Atom l tau x r)
    (hcalls : ∀ L, 4 ≤ L → (a * 2 + b + 1) * 4 = 2 ^ (1 + k) * L → L ≤ c) :
    tau ≤ c ∧ 2 ≤ c := by
  have hab := Atom_bound hr
  have hL : 4 ≤ 2 ^ (h - k) := by
    have : (4 : ℕ) = 2 ^ 2 := rfl
    rw [this]
    exact pow2_mono (by omega)
  have hc := hcalls (2 ^ (h - k)) hL (level_call_scale k hl (by omega))
  have hp : 2 ^ l ≤ 2 ^ (h - k) := pow2_mono (by omega)
  omega

theorem double_narrow_closed {h a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 3 ≤ k) (hwidth : k + 2 ≤ h) (hn : 0 < n)
    (hw : Word k n xs) (hr : Atom l tau x r) (hrank : k + l ≤ h)
    (hguard : Narrow a j k n)
    (hcap : phi n + (2 ^ k - 1) * x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, Normal c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hinner : n % 2 = 1 ∨ 2 ^ (1 + k) ≤ n + j * 4 := by
    rcases hguard with h | ⟨_, h⟩
    · exact Or.inl h
    · exact Or.inr h
  have htail := G_atom_ready hr
  rcases k with _ | _ | _ | k
  · omega
  · omega
  · omega
  · by_cases hja : j = a
    · subst hja
      have hb_pow : 2 ^ (2 + k) ≤ b + j := by
        have hp : 2 ^ (4 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
        omega
      have hw' : Word ((2 + k) + 1) n xs := by
        have : (2 + k) + 1 = k + 3 := by omega
        rwa [this]
      have hinner' : n % 2 = 1 ∨ 2 ^ (1 + ((2 + k) + 1)) ≤ n + j * 4 := by
        have : 1 + ((2 + k) + 1) = 1 + (k + 3) := by omega
        rwa [this]
      have hcap' : phi n + (2 ^ ((2 + k) + 1) - 1) * x ≤ (j * 2 + b + 1) * 4 := by
        have : (2 + k) + 1 = k + 3 := by omega
        rwa [this]
      obtain ⟨z, c, ys, s, hys, hodd, hs, hg, hvalue, hcalls, hstep⟩ :=
        narrow_boundary (fun c s => tau ≤ c → 2 ≤ c → Sat (Nat.max l 3) (x + c * 2) s)
          (k := 2 + k) hl.level_frame hw' (by omega) hn htail hinner' hb_pow hcap'
      obtain ⟨htau, htwo⟩ := narrow_calls_saturate (k := 3 + k) hl
        (by omega) (by omega) hr (fun L hL hsize => hcalls L (by omega)
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize))
      have hs' := hs htau htwo
      have hmax1 : (2 + k) + Nat.max l 3 ≤ 1 + h := by
        have : Nat.max l 3 ≤ h - (1 + k) := Nat.max_le.mpr ⟨by omega, by omega⟩
        omega
      have hmax2 : Nat.max l 3 + 2 ≤ 1 + h := by
        have : Nat.max l 3 ≤ h - 1 := Nat.max_le.mpr ⟨by omega, by omega⟩
        omega
      refine ⟨_, ?_, hstep⟩
      have h_w0 : (fs ++ w ^ j ++ d) +> (ys +> s) = (fs ++ w ^ j ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
      rw [h_w0]
      exact sat_double_root (j := 0) (Level_next hl) (by omega) (by omega) (by omega) (by omega)
        hys hs' hmax1 hmax2 (by omega) (by omega) (by omega)
    · have hb_pow : 2 ^ (2 + k) ≤ b + j := by
        have hp : 2 ^ (4 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        rw [← hl.level_size] at hp
        have : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
        omega
      have hB' : 2 ^ (1 + (1 + k)) ≤ b + j := by
        have : 1 + (1 + k) = 2 + k := by omega
        rwa [this]
      have hw' : Word ((1 + k) + 2) n xs := by
        have : (1 + k) + 2 = k + 3 := by omega
        rwa [this]
      have hinner' : n % 2 = 1 ∨ 2 ^ (1 + ((1 + k) + 2)) ≤ n + j * 4 := by
        have : 1 + ((1 + k) + 2) = 1 + (k + 3) := by omega
        rwa [this]
      have hcap' : phi n + (2 ^ ((1 + k) + 2) - 1) * x ≤ (a * 2 + b + 1) * 4 := by
        have : (1 + k) + 2 = k + 3 := by omega
        rwa [this]
      obtain ⟨z, c, ys, s, hys, hz, hs, hg, hvalue, hlower, hsmall, hcalls, hstep⟩ :=
        narrow_inside (fun c s => tau ≤ c → 2 ≤ c → Sat (Nat.max l 3) (x + c * 2) s)
          (k := 1 + k) hl.level_frame (by omega) hw' (by omega) hn htail hinner' hB' hcap'
      obtain ⟨htau, htwo⟩ := narrow_calls_saturate (k := 3 + k) hl
        (by omega) (by omega) hr (fun L hL hsize => hcalls L hL
          (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsize))
      have hs' := hs htau htwo
      have hmax1 : (1 + k) + Nat.max l 3 ≤ h := by
        have : Nat.max l 3 ≤ h - (1 + k) := Nat.max_le.mpr ⟨by omega, by omega⟩
        omega
      have hmax2 : Nat.max l 3 + 2 ≤ h := by
        have : Nat.max l 3 ≤ h - 2 := Nat.max_le.mpr ⟨by omega, by omega⟩
        omega
      refine ⟨_, ?_, hstep⟩
      exact sat_double_root (j := j + 1) hl (by omega) (by omega) (by omega) hz hys hs'
        hmax1 hmax2 (by omega)
        (fun hev => by have := hlower hev; omega) (fun hk1 h2 => hsmall hk1 (by omega))

theorem descent_y_inside_calls (a b j k u_val v y z c₁ c₂ c₃ : ℕ)
    (hj : j < a) (hk : 0 < k) (hsize : a * 2 + b + 1 = 2 ^ (2 + k))
    (hu : 0 < u_val) (hy : 0 < y) (hz : 0 < z) (hzb : z < 2 ^ (1 + k))
    (h0 : CounterRun (GCounter (k + 2)) (j * 2 + 2) ((a - j) * 2 + 1) (u_val * 2 + 1) 0)
    (h1 : CounterRun (GCounter (k + 1)) (b + j) u_val v c₁)
    (h2 : CounterRun (GCounter (k + 1)) 2 v (y * 2 + 1) c₂)
    (h3 : CounterRun (GCounter k) (a - j - 1) y z c₃) :
    2 ≤ c₁ + c₂ + c₃ := by
  have e := descent_inside_balance a b j k ((a - j) * 2 + 1) u_val v y z 0 c₁ c₂ c₃ 0
    hj hk (by omega) hu hy h0 h1 h2 h3
  have hphi_u := phi_bounds hu
  have hphi_y := phi_bounds hy
  have hphi_z := phi_bounds hz
  rw [phi_odd] at e
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  have hp2 : 2 ^ (2 + k) = 2 ^ k * 4 := by ring
  have hp2' : 2 ^ (k + 2) = 2 ^ k * 4 := by ring
  have hp0 : 1 ≤ 2 ^ k := pow2_pos k
  have hpu : phi u_val ≤ u_val := hphi_u.2.1
  have hpy : phi y ≤ y := hphi_y.2.1
  have haj : j ≤ a := by omega
  by_contra hlt
  rcases hphi_u with ⟨hpu1, hpu2, hpu3⟩
  rcases hphi_y with ⟨hpy1, hpy2, hpy3⟩
  rcases hphi_z with ⟨hpz1, hpz2, hpz3⟩
  have h_gap : (2 ^ k * (c₁ + c₂ + c₃ + 1)) * 8 + 4 ≤
      (2 ^ k * 2) * 8 + (c₁ + c₂) * 4 + c₃ * 8 := by
    by_cases hc : c₁ + c₂ + c₃ = 0
    · have hle2 : c₁ + c₂ + c₃ + 2 ≤ 2 := by omega
      have hmul2 := Nat.mul_le_mul_left (2 ^ k) hle2
      ring_nf at hmul2 ⊢
      omega
    · have hle1 : c₁ + c₂ + c₃ + 1 ≤ 2 := by omega
      have hmul1 := Nat.mul_le_mul_left (2 ^ k) hle1
      ring_nf at hmul1 ⊢
      omega
  zify [hp0, hpu2, hpy2, haj] at hp0 haj e hpu3 hpy3 hpz2 hzb hp1 hp2 hp2' hsize h_gap
  ring_nf at e hzb hsize h_gap
  omega

theorem double_y_closed {h a b j : ℕ} {fs : List Sym} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a)
    (hw : Word (h - 1) ((a - j) * 2 + 1) xs)
    (hr : Atom l tau x r) (hl1 : l ≤ 1)
    (hcap : phi ((a - j) * 2 + 1) + (2 ^ (h - 1) - 1) * x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, Normal c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨hlpos, htau⟩ := Atom_bound hr
  have el : l = 1 := by omega
  subst el
  change tau ≤ 2 at htau
  have eh : h = (h - 4) + 4 := by omega
  set k := h - 4
  have hsize : a * 2 + b + 1 = 2 ^ (3 + k) := by
    have : h - 1 = 3 + k := by omega
    rw [← this, hl.level_size]
  have hw' : Word ((2 + k) + 1) ((a - j) * 2 + 1) xs := by
    have : (2 + k) + 1 = h - 1 := by omega
    rwa [this]
  have hcap' : phi ((a - j) * 2 + 1) + (2 ^ ((2 + k) + 1) - 1) * x ≤ (a * 2 + b + 1) * 4 := by
    have : (2 + k) + 1 = h - 1 := by omega
    rwa [this]
  have hguard : ((a - j) * 2 + 1) % 2 = 1 ∨ 2 ^ (1 + ((2 + k) + 1)) ≤ (a - j) * 2 + 1 + j * 4 :=
    Or.inl (by omega)
  by_cases hja : j = a
  · subst hja
    have hb_pow : 2 ^ (2 + k) ≤ b + j := by
      have : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
      omega
    obtain ⟨z, c, ys, s, hys, hodd, hs, hg, hvalue, hcalls, hstep⟩ :=
      narrow_boundary (fun c s => tau ≤ c → 2 ≤ c → Sat (Nat.max 1 3) (x + c * 2) s)
        (k := 2 + k) hl.level_frame hw' (by omega) (by omega) (G_atom_ready hr)
        hguard hb_pow hcap'
    have htwo : 2 ≤ c := by
      refine hcalls 2 (by decide) ?_
      have : 2 ^ (2 + (2 + k)) = 2 ^ (3 + k) * 2 := by ring
      omega
    have hs' : Sat 3 (x + c * 2) s := hs (by omega) htwo
    refine ⟨_, ?_, hstep⟩
    have h_w0 : (fs ++ w ^ j ++ d) +> (ys +> s) = (fs ++ w ^ j ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
    rw [h_w0]
    exact sat_double_root (j := 0) (L := 3) (Level_next hl) (by omega) (by omega) (by omega) (by omega)
      hys hs' (by omega) (by omega) (by omega) (by omega) (by omega)
  · have hw'' : Word ((1 + k) + 2) ((a - j) * 2 + 1) xs := by
      have : (1 + k) + 2 = (2 + k) + 1 := by omega
      rwa [this]
    have hguard' : ((a - j) * 2 + 1) % 2 = 1 ∨ 2 ^ (1 + ((1 + k) + 2)) ≤ (a - j) * 2 + 1 + j * 4 :=
      Or.inl (by omega)
    obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total ((1 + k) + 2) j ((a - j) * 2 + 1)
      (by omega) (Word_bound hw'') hguard'
    have h_lin0 : (a - j) * 2 + 1 + (j * 2 + 2) * 2 < 2 ^ (1 + ((1 + k) + 2)) := by
      have : 2 ^ (1 + ((1 + k) + 2)) = 2 ^ (3 + k) * 2 := by ring
      omega
    obtain ⟨eu, ec0⟩ := GCounterRun_linear h0 h_lin0
    have eu' : u_val = a + j + 2 := by omega
    subst eu' ec0
    have hub' : a + j + 2 < 2 ^ (1 + ((1 + k) + 1)) := by
      have : 1 + ((1 + k) + 1) = (1 + k) + 2 := by omega
      rwa [this]
    obtain ⟨v, c₁, h1, hvb⟩ := CounterRun_total
      (fun v' hv' => GCounter_total ((1 + k) + 1) v' (by omega) hv') (b + j) (a + j + 2) hub'
    have hodd : v % 2 = 1 := by
      refine GCounterRun_saturated h1 (by omega) hub' ?_
      have : 2 ^ (1 + ((1 + k) + 1)) = 2 ^ (3 + k) := by
        have : 1 + ((1 + k) + 1) = 3 + k := by omega
        rw [this]
      omega
    obtain ⟨y, c₂, hy, hyb, h2⟩ := counter_inner_total ((1 + k) + 1) 0 v (by omega) hvb (Or.inl hodd)
    have hyb' : y < 2 ^ (1 + (1 + k)) := by
      have : 1 + (1 + k) = (1 + k) + 1 := by omega
      rwa [this]
    obtain ⟨z, c₃, h3, hzb⟩ := CounterRun_total
      (fun z' hz' => GCounter_total (1 + k) z' (by omega) hz') (a - j - 1) y hyb'
    have hz : 0 < z := GCounterRun_positive h3 hy
    have hsize' : a * 2 + b + 1 = 2 ^ (2 + (1 + k)) := by
      have : 2 + (1 + k) = 3 + k := by omega
      rwa [this]
    have htwo : 2 ≤ c₁ + c₂ + c₃ :=
      descent_y_inside_calls a b j (1 + k) (a + j + 2) v y z c₁ c₂ c₃
        (by omega) (by omega) hsize' hu hy hz hzb h0 h1 h2 h3
    obtain ⟨s, hs, hg⟩ := G_atom_sat (c₁ + (c₂ + c₃)) hr (by omega) (by omega)
    have hs' : Sat 3 (x + (c₁ + (c₂ + c₃)) * 2) s := hs
    have hg' : G (0 + (c₁ + (c₂ + c₃))) r s := by simpa using hg
    obtain ⟨ys, hys, hstep⟩ := descent_inside hl.level_frame (by omega) hw'' (by omega)
      hguard' hodd h0 h1 h2 h3 hg'
    have hvalue : phi z + (2 ^ (1 + k) - 1) * (x + (c₁ + (c₂ + c₃)) * 2) < (a * 2 + b + 1) * 2 := by
      have e := descent_inside_balance a b j (1 + k) ((a - j) * 2 + 1) (a + j + 2) v y z 0 c₁ c₂ c₃ x
        (by omega) (by omega) (by omega) hu hy h0 h1 h2 h3
      have hphi_u := phi_bounds hu
      have hphi_y := phi_bounds hy
      have h_assoc : 0 + c₁ + c₂ + c₃ = c₁ + (c₂ + c₃) := by omega
      have h_k : (1 + k) + 2 = (2 + k) + 1 := by omega
      rw [h_assoc, h_k] at e
      omega
    have hlower : z % 2 = 0 → (a - j) * 2 ≤ z := by
      intro heven
      obtain ⟨_, ez, _⟩ := GCounterRun_even h3 heven
      omega
    refine ⟨_, ?_, hstep⟩
    exact sat_double_root (j := j + 1) (L := 3) hl (by omega) (by omega) (by omega) hz hys hs'
      (by omega) (by omega) (by omega)
      (fun hev => by have := hlower hev; omega) (by omega)

theorem double_phase_progress {h a b j : ℕ} {fs : List Sym} {k n : ℕ} {xs : List Sym}
    {l tau x : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 0 < k) (hn : 0 < n)
    (hw : Word k n xs) (hr : Atom l tau x r) (hp : DoublePhase h a b j k n l tau)
    (hcap : phi n + (2 ^ k - 1) * x ≤ (a * 2 + b + 1) * 4) :
    ∃ c, Normal c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  cases hp with
  | DN k n l tau hkn hwidth hphase hrank =>
    exact double_narrow_closed hl hj hkn hwidth hn hw hr hrank hphase hcap
  | DY l tau hl1 =>
    exact double_y_closed hl hj hw hr hl1 hcap
  | D2 n l tau hphase hwidth hbudget =>
    obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
    have hnb : n < 8 := Word_bound hw
    have hguard : n % 2 = 1 ∨ 8 ≤ n + j * 4 := by
      rcases hphase with h | h <;> [exact Or.inl h; (right; omega)]
    obtain ⟨u_val, c₀, hu, hub, h0⟩ := counter_inner_total 2 j n (by decide) hnb hguard
    obtain ⟨z, c₁, h1, _⟩ := CounterRun_total (fun z' hz' => GCounter_total 1 z' (by decide) hz')
      (b + j) u_val hub
    have hrun : CounterRun (GCounter 1) (2 + (b + j - 2)) u_val z c₁ := by
      have : 2 + (b + j - 2) = b + j := by omega
      rwa [this]
    obtain ⟨rfl, hlo, hhi⟩ := GCounterRun_one hrun hu hub
    have h_22 : 2 ^ 2 - 1 = 3 := rfl
    rw [h_22] at hcap
    obtain ⟨c, hroot, hstep⟩ := double_two_closed hl hj hn hw hphase hr hwidth h0 h1
      (by omega) hcap
    exact ⟨c, Or.inl hroot, hstep⟩
  | D1 n l tau hwidth hpos =>
    have h_21 : 2 ^ 1 - 1 = 1 := rfl
    rw [h_21, Nat.one_mul] at hcap
    rcases hpos with rfl | ⟨hnear, rfl⟩
    · obtain ⟨c, hroot, hstep⟩ := double_one_boundary_closed hl hn hw hr hwidth hcap
      exact ⟨c, Or.inl hroot, hstep⟩
    · have h_phi1 : phi 1 = 1 := rfl
      rw [h_phi1] at hcap
      obtain ⟨c, hroot, hstep⟩ := double_one_neighbor_closed hl hnear hw hr hwidth hcap
      exact ⟨c, Or.inl hroot, hstep⟩

theorem double_progress {c : Cfg Sym Q} (hd : DRoot c) :
    ∃ c', Normal c' ∧ c [tm1]⊢⁺ c' := by
  rcases hd with ⟨h, a, b, j, fs, r, hl, hj, hd'⟩
  rcases hd' with ⟨k, n, xs, l, tau, x, r, hk, hn, hw, hr, hp, hcap⟩
  exact double_phase_progress hl hj hk hn hw hr hp hcap



set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000000

theorem late_first_Q_boundary_closed {k a : ℕ} {fs xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (2 + k) a (a + 1) fs) (hw : Word (k + 1) (a * 2 + 2) xs)
    (hr : Num q r) (hq : q ≤ 1) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + (a + 1) + 1 = 2 ^ (1 + k) := by
    have : 2 + k - 1 = 1 + k := by omega
    rw [← this, hl.level_size]
  have hpow : a * 6 + 4 = 2 ^ (2 + k) := by
    have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
    omega
  obtain ⟨ys, s, hy, hs, hstep⟩ :=
    late_first_Q_boundary hl.level_frame (by omega) hpow hw hr
  have hodd : (a + 3) % 2 = 1 := by
    rcases Frame_phase hl.level_frame with ⟨h1, _⟩ | ⟨_, h2⟩ <;> omega
  refine ⟨_, ?_, hstep⟩
  have h_w0 : (fs ++ w ^ a ++ d) +> (ys +> s) = (fs ++ w ^ a ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
  rw [h_w0]
  refine small_single_root (j := 0) (Level_next hl) (by omega) (by omega) (by omega) (by omega)
    hy hs ?_ (by omega) (by omega)
  have hphi : phi (a + 3) = a + 3 := by unfold phi; omega
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  rw [hphi]
  have hq_mul : (2 ^ k - 1) * (q + 4) ≤ (2 ^ k - 1) * 5 := Nat.mul_le_mul_left _ (by omega)
  omega

theorem late_second_Q_recover_closed {k a : ℕ} {fs xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (2 + k) a a fs) (hw : Word (k + 1) (a * 2 + 2) xs)
    (hr : Num q r) (hq : q ≤ 3) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ (a - 1) +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + a + 1 = 2 ^ (1 + k) := by
    have : 2 + k - 1 = 1 + k := by omega
    rw [← this, hl.level_size]
  have hpow : a * 6 + 2 = 2 ^ (2 + k) := by
    have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
    omega
  obtain ⟨K, z, Q, ys, s, hK, hwidth, hy, hs, hodd, hwide, hcap, hsmall, hstep⟩ :=
    late_second_Q_recover hl.level_frame ha hpow hw hr hq
  refine ⟨_, ?_, hstep⟩
  by_cases hK1 : K = 1
  · subst hK1
    obtain ⟨rfl, htail⟩ := hsmall rfl
    have eys := Word_max hy rfl
    change ys = w at eys
    rw [eys]
    have h_w1 : (fs ++ w ^ a ++ d) +> (w +> s) = (fs ++ w ^ a ++ d) +> (w ^ 1 +> s) := rfl
    rw [h_w1]
    exact .sroot (1 + (2 + k)) (a + a) (a * 2 + 1) 1 (fs ++ w ^ a ++ d) s
      (Level_next hl) (by omega) (.SNum Q s hs htail)
  · have h_w0 : (fs ++ w ^ a ++ d) +> (ys +> s) = (fs ++ w ^ a ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
    rw [h_w0]
    refine .sroot (1 + (2 + k)) (a + a) (a * 2 + 1) 0 (fs ++ w ^ a ++ d) (ys +> s)
      (Level_next hl) (by omega)
      (.SWord K z Q ys s hK (by omega) hy hs ?_ (by omega))
    refine single_odd_phase (by omega) (by omega) hodd (fun hwider => ⟨?_, Or.inr (by omega)⟩)
    have hp : 2 ^ (2 + k) ≤ 2 ^ K := pow2_mono (by omega)
    have hz := hwide hp
    omega

theorem first_Q_x_closed {k a j : ℕ} {fs xs : List Sym} {r : ListBlank Sym}
    (hl : Level (2 + k) a a fs) (hj : j * 7 + 4 = a * 5)
    (hw : Word (2 + k) (a * 3 + 1 - j) xs) (hr : Num 0 r) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + a + 1 = 2 ^ (1 + k) := by
    have : 2 + k - 1 = 1 + k := by omega
    rw [← this, hl.level_size]
  have hodd : (a * 3 + 1 - j) % 2 = 1 := by
    rcases Frame_phase hl.level_frame with ⟨_, h⟩ | ⟨h, _⟩ <;> omega
  have h_lin1 : a * 3 + 1 - j + (j * 2 + 2) * 2 < 2 ^ (1 + (2 + k)) := by
    have : 2 ^ (1 + (2 + k)) = 2 ^ (1 + k) * 4 := by ring
    omega
  obtain ⟨ys, hy, hp⟩ := P_word_linear (j * 2 + 2) r hw (by omega) h_lin1
  set u_val := (a * 3 + 1 - j + j * 4 + 3) / 2
  have hu_eq : a * 3 + 1 - j + (j * 2 + 2) * 2 = u_val * 2 + 1 := by omega
  rw [hu_eq] at hy
  have hy' : Word ((1 + k) + 1) (u_val * 2 + 1) ys := by
    have : (1 + k) + 1 = 2 + k := by omega
    rwa [this]
  obtain ⟨zs, hz, rfl⟩ := Word_odd_inv hy'
  have h_lin2 : u_val + (a + j) * 2 < 2 ^ (1 + (1 + k)) := by
    have : 2 ^ (1 + (1 + k)) = 2 ^ (1 + k) * 2 := by ring
    omega
  obtain ⟨bs, hb, hmid⟩ := P_word_linear (a + j) r hz (by omega) h_lin2
  have etop : u_val + (a + j) * 2 + 2 = 2 ^ (2 + k) := by
    have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
    omega
  have hb' : Word (k + 1) (u_val + (a + j) * 2) bs := by
    have : k + 1 = 1 + k := by omega
    rwa [this]
  rw [Word_before_Q hb' etop] at hmid
  obtain ⟨r₁, h1, htail⟩ := P_num hr
  have h_lin3 : 1 + (a - j - 1) * 2 < 2 ^ (1 + k) := by omega
  obtain ⟨out, hout, hlast⟩ := P_word_linear (a - j - 1) r₁ (Word_one k) (by omega) h_lin3
  have hstep : (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (out +> r₁)))) := by
    refine first_Q_inside hl.level_frame (by omega)
      (.InnerP (by simpa only [List.append_assoc, append_assoc] using hp))
      (P_G (by simpa only [List.append_assoc, append_assoc] using hmid))
      (.GP htail) (P_G hlast)
  refine ⟨_, ?_, hstep⟩
  refine .sroot (2 + k) a a (j + 1) fs (out +> r₁) hl (by omega)
    (.SWord k (1 + (a - j - 1) * 2) 2 out r₁ (by omega) (by omega) hout h1
      (.SN k _ 2 (by omega) (by omega) (Or.inl (by omega))) ?_)
  unfold phi
  have hp1 : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  omega

theorem late_first_Q_z_closed {k a j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a (a + 1) fs) (hj : j * 7 = a * 5)
    (hn : n * 2 = (a * 3 + 2) * 2 + (a - j))
    (hw : Word (2 + k) n xs) (hr : Num 0 r) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + (a + 1) + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  obtain ⟨r₁, h1, htail⟩ := P_num hr
  obtain ⟨u_val, c, ys, s, hc, hy, hs, hg⟩ :=
    G_word_data (a + 1 + j) (by omega) (Word_one (1 + k)) h1
  have hodd : u_val % 2 = 1 := GCounterRun_odd hc rfl
  have hub := Word_bound hy
  have e := GCounterRun_balance hc (by omega) (by decide)
  have ec : c = 1 := by
    have hper : (2 ^ (1 + k) - 1) * 2 = a * 3 := by
      have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
      omega
    rw [hper] at e
    unfold phi at e
    have hub' : u_val < a * 3 + 2 := by
      have : 2 ^ (1 + (1 + k)) = 2 ^ (2 + k) := by
        have : 1 + (1 + k) = 2 + k := by omega
        rw [this]
      omega
    rcases c with _ | _ | c'
    · omega
    · rfl
    · nlinarith
  subst ec
  have hs' : Num 4 s := hs
  have hy' : Word (k + 1) u_val ys := by
    have : k + 1 = 1 + k := by omega
    rwa [this]
  obtain ⟨z, e_cnt, zs, out, hz, hzpos, hout, hcap, hlower, hsmall, hp, _⟩ :=
    odd_d_value Num (a - j - 1) hy' (by omega) hodd (fun c => G_nums c hs')
  have hstep : (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (zs +> out)))) := by
    rw [pow_add_list w j 1, pow_one_list, append_assoc]
    have hw' : Word ((1 + k) + 1) n xs := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    have he_pow : n + (j - 1) * 4 + 6 = 2 ^ (2 + (1 + k)) := by
      have : 2 ^ (2 + (1 + k)) = 2 ^ (2 + k) * 2 := by ring
      omega
    have hg' : G (a + 1 + (j - 1) + 1) (one (1 + k) +> r₁) (ys +> s) := by
      have : a + 1 + (j - 1) + 1 = a + 1 + j := by omega
      rwa [this]
    have hout_g : G (a - (j - 1) - 1) (d +> (ys +> s)) (w +> (zs +> out)) := by
      have : a - (j - 1) - 1 = 1 + (a - j - 1) := by omega
      rw [this]
      exact P_G hp
    have h_lfq := late_first_Q (a := a) (b := a + 1) (j := j - 1) (k := 1 + k)
      hl.level_frame (by omega) (by omega) hw' he_pow (.GP htail) hg' hout_g
    have hj_eq : 1 + (j - 1) = j := by omega
    rwa [hj_eq] at h_lfq
  refine ⟨_, ?_, hstep⟩
  refine small_single_root (j := j + 1) hl (by omega) (by omega) (by omega) hzpos hz hout ?_
    (fun hev => by have := hlower hev; omega) (fun hk1 h2 => hsmall hk1 (by omega))
  have hphi : phi u_val = u_val := by
    unfold phi; omega
  have h_phi1 : phi 1 = 1 := rfl
  rw [hphi] at e hcap
  try rw [h_phi1] at e
  have hp1 : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
  have hp2 : 2 ^ (k + 1) = 2 ^ (1 + k) := by
    have : k + 1 = 1 + k := by omega
    rw [this]
  rw [hp2] at hcap
  clear hc hy hs hg hy' hz hout hp hstep hlower hsmall h1 htail hl hw hr hs'
  omega

theorem single_low_descent_closed {k a b j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a) (hn : 0 < n)
    (hw : Word (2 + k) n xs) (hr : Num q r)
    (hguard : n % 2 = 1 ∨ 2 ^ (3 + k) ≤ n + j * 4)
    (hready : ∀ u_val v c₀ c₁,
      CounterRun (GCounter (2 + k)) (j * 2 + 2) n (u_val * 2 + 1) c₀ →
      CounterRun (GCounter (1 + k)) (b + j) u_val v c₁ → v % 2 = 1)
    (hcap : phi n + (2 ^ (2 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hguard1 : n % 2 = 1 ∨ 2 ^ (1 + (2 + k)) ≤ n + j * 4 := by
    have : 1 + (2 + k) = 3 + k := by omega
    rwa [this]
  obtain ⟨u_val, c₀, hu, hub, h0⟩ :=
    counter_inner_total (2 + k) j n (by omega) (Word_bound hw) hguard1
  have hub' : u_val < 2 ^ (1 + (1 + k)) := by
    have : 1 + (1 + k) = 2 + k := by omega
    rwa [this]
  obtain ⟨v, c₁, h1, hvb⟩ := CounterRun_total
    (fun z' hz' => GCounter_total (1 + k) z' (by omega) hz') (b + j) u_val hub'
  have hodd : v % 2 = 1 := hready u_val v c₀ c₁ h0 h1
  by_cases hja : j = a
  · subst hja
    obtain ⟨s, hs, hg⟩ := G_nums (c₀ + c₁) hr
    have hw' : Word ((1 + k) + 1) n xs := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    have h0' : CounterRun (GCounter ((1 + k) + 1)) (j * 2 + 2) n (u_val * 2 + 1) c₀ := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    have hguard' : n % 2 = 1 ∨ 2 ^ (1 + ((1 + k) + 1)) ≤ n + j * 4 := by
      have : 1 + ((1 + k) + 1) = 3 + k := by omega
      rwa [this]
    obtain ⟨ys, hys, hstep⟩ :=
      descent_boundary hl.level_frame hw' (by omega) hguard' h0' h1 hg
    have e := descent_boundary_balance j b (1 + k) n u_val v c₀ c₁ q (by omega) hn hu h0' h1
    have hpu := phi_bounds hu
    refine ⟨_, ?_, hstep⟩
    have h_w0 : (fs ++ w ^ j ++ d) +> (ys +> s) = (fs ++ w ^ j ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
    rw [h_w0]
    refine small_single_root (Level_next hl) (by omega) (by omega) (by omega) (by omega)
      hys hs ?_ (by omega) (by omega)
    have : (1 + k) + 1 = 2 + k := by omega
    rw [this] at e
    omega
  · obtain ⟨y, c₂, hy, hyb, h2⟩ :=
      counter_inner_total (1 + k) 0 v (by omega) hvb (Or.inl hodd)
    have hyb' : y < 2 ^ (1 + k) := hyb
    obtain ⟨z, c₃, h3, hzb⟩ := CounterRun_total
      (fun z' hz' => GCounter_total k z' (by omega) hz') (a - j - 1) y hyb'
    obtain ⟨s, hs, hg⟩ := G_nums (c₀ + (c₁ + (c₂ + c₃))) hr
    have hw' : Word (k + 2) n xs := by
      have : k + 2 = 2 + k := by omega
      rwa [this]
    have hguard' : n % 2 = 1 ∨ 2 ^ (1 + (k + 2)) ≤ n + j * 4 := by
      have : 1 + (k + 2) = 3 + k := by omega
      rwa [this]
    have h0' : CounterRun (GCounter (k + 2)) (j * 2 + 2) n (u_val * 2 + 1) c₀ := by
      have : k + 2 = 2 + k := by omega
      rwa [this]
    have h1' : CounterRun (GCounter (k + 1)) (b + j) u_val v c₁ := by
      have : k + 1 = 1 + k := by omega
      rwa [this]
    have h2' : CounterRun (GCounter (k + 1)) 2 v (y * 2 + 1) c₂ := by
      have : k + 1 = 1 + k := by omega
      rwa [this]
    obtain ⟨ys, hys, hstep⟩ :=
      descent_inside hl.level_frame (by omega) hw' (by omega) hguard' hodd h0' h1' h2' h3 hg
    have e := descent_inside_balance a b j k n u_val v y z c₀ c₁ c₂ c₃ q
      (by omega) (by omega) hn hu hy h0' h1' h2' h3
    have hpu := phi_bounds hu
    have hpy := phi_bounds hy
    have hz : 0 < z := GCounterRun_positive h3 hy
    refine ⟨_, ?_, hstep⟩
    refine small_single_root hl (by omega) (by omega) (by omega) hz hys hs ?_ ?_ (by omega)
    · have h_assoc : c₀ + (c₁ + (c₂ + c₃)) = c₀ + c₁ + c₂ + c₃ := by omega
      have h_k : k + 2 = 2 + k := by omega
      rw [h_assoc]
      rw [h_k] at e
      omega
    · intro heven
      obtain ⟨_, ez, _⟩ := GCounterRun_even h3 heven
      omega

theorem single_y_low_closed {k a b j : ℕ} {fs xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hw : Word (2 + k) ((a - j) * 2 + 1) xs) (hr : Num q r)
    (hcap : phi ((a - j) * 2 + 1) + (2 ^ (2 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  refine single_low_descent_closed hl hj (by omega) hw hr (Or.inl (by omega)) ?_ hcap
  intro u_val v c₀ c₁ h0 h1
  have h_lin : (a - j) * 2 + 1 + (j * 2 + 2) * 2 < 2 ^ (1 + (2 + k)) := by
    have : 2 ^ (1 + (2 + k)) = 2 ^ (2 + k) * 2 := by ring
    omega
  obtain ⟨eu, ec0⟩ := GCounterRun_linear h0 h_lin
  refine GCounterRun_saturated h1 (by omega) ?_ ?_
  · have : 2 ^ (1 + (1 + k)) = 2 ^ (2 + k) := by
      have : 1 + (1 + k) = 2 + k := by omega
      rw [this]
    omega
  · have : 2 ^ (1 + (1 + k)) = 2 ^ (2 + k) := by
      have : 1 + (1 + k) = 2 + k := by omega
      rw [this]
    omega

theorem single_x_low_odd_closed {k a b j : ℕ} {fs xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hodd : (a * 2 + b + 1 - j) % 2 = 1)
    (hw : Word (2 + k) (a * 2 + b + 1 - j) xs) (hr : Num q r)
    (hcap : phi (a * 2 + b + 1 - j) + (2 ^ (2 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  refine single_low_descent_closed hl hj (by omega) hw hr (Or.inl hodd) ?_ hcap
  intro u_val v c₀ c₁ h0 h1
  have hub := GCounterRun_bound h0 (by omega) (Word_bound hw)
  have e := GCounterRun_balance h0 (by omega) (by omega)
  rw [phi_odd] at e
  have hphi : phi (a * 2 + b + 1 - j) = a * 2 + b + 1 - j := by
    unfold phi; omega
  rw [hphi] at e
  have h_pow : 2 ^ (1 + (1 + k)) = 2 ^ (2 + k) := by
    have : 1 + (1 + k) = 2 + k := by omega
    rw [this]
  have h_pow2 : 2 ^ (1 + (2 + k)) = 2 ^ (2 + k) * 2 := by ring
  refine GCounterRun_saturated h1 (by omega) (by omega) ?_
  rw [h_pow, ← hsize]
  have ep : 2 ^ (2 + k) - 1 = a * 2 + b := by omega
  rw [ep] at e
  rcases c₀ with _ | _ | c₀'
  · omega
  · omega
  · have : 2 * ((a * 2 + b) * 2) ≤ (c₀' + 1 + 1) * ((a * 2 + b) * 2) :=
      Nat.mul_le_mul_right _ (by omega)
    omega

theorem single_x_top_closed {k a : ℕ} {fs xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a a fs) (hw : Word (4 + k) (a * 2 + 1) xs) (hr : Num 0 r) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + a + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have h_lin1 : a * 2 + 1 + (a * 2 + 2) * 2 < 2 ^ (1 + (4 + k)) := by
    have : 2 ^ (1 + (4 + k)) = 2 ^ (2 + k) * 8 := by ring
    omega
  obtain ⟨ys, hy, hp⟩ := P_word_linear (a * 2 + 2) r hw (by omega) h_lin1
  have h_eq1 : a * 2 + 1 + (a * 2 + 2) * 2 = (a * 3 + 2) * 2 + 1 := by omega
  rw [h_eq1] at hy
  have hy' : Word ((3 + k) + 1) ((a * 3 + 2) * 2 + 1) ys := by
    have : (3 + k) + 1 = 4 + k := by omega
    rwa [this]
  obtain ⟨zs, hz, rfl⟩ := Word_odd_inv hy'
  have h_lin2 : a * 3 + 2 + (a + a) * 2 < 2 ^ (1 + (3 + k)) := by
    have : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
    omega
  obtain ⟨out, hout, hmid⟩ := P_word_linear (a + a) r hz (by omega) h_lin2
  have hstep : (cfg (fs +> (w ^ a +> (xs +> r)))) [tm1]⊢⁺ (cfg ((fs ++ w ^ a ++ d) +> (out +> r))) := by
    simp only [List.append_assoc, append_assoc]
    refine frame_step hl.level_frame ?_
    have hin : Inner a (xs +> r) (t +> (zs +> r)) :=
      .InnerP (by simpa only [List.append_assoc, append_assoc] using hp)
    have hgd : I (a + a) ([1] +> (t +> (zs +> r))) (d +> (out +> r)) := by
      simpa only [d, t, append_cons, append_nil] using G_d (P_G hmid)
    have h_sub : a - a = 0 := by omega
    exact inner_column (by omega) hin hgd (by rw [h_sub]; exact .G0 _)
  refine ⟨_, ?_, hstep⟩
  have h_w0 : (fs ++ w ^ a ++ d) +> (out +> r) = (fs ++ w ^ a ++ d) +> (w ^ 0 +> (out +> r)) := rfl
  rw [h_w0]
  refine .sroot (1 + (3 + k)) (a + a) (a * 2 + 1) 0 (fs ++ w ^ a ++ d) (out +> r)
    (Level_next hl) (by omega)
    (.SWord (3 + k) (a * 3 + 2 + (a + a) * 2) 0 out r (by omega) (by omega) hout hr ?_ ?_)
  · have h_sz := SinglePhase.SZ (h := 1 + (3 + k)) (a := a + a) (b := a * 2 + 1) (j := 0)
      (a * 3 + 2 + (a + a) * 2) (by omega)
    simpa using h_sz
  · unfold phi; omega

theorem single_y_top_odd_closed {k a b j : ℕ} {fs xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j < a)
    (hodd : (a + b * 2 + j * 3 + 2) % 2 = 1)
    (hw : Word (4 + k) ((a - j) * 2 + 1) xs) (hr : Num 0 r) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have h_lin1 : (a - j) * 2 + 1 + (j * 2 + 2) * 2 < 2 ^ (1 + (4 + k)) := by
    have : 2 ^ (1 + (4 + k)) = 2 ^ (2 + k) * 8 := by ring
    omega
  obtain ⟨ys, hy, hp⟩ := P_word_linear (j * 2 + 2) r hw (by omega) h_lin1
  have h_eq1 : (a - j) * 2 + 1 + (j * 2 + 2) * 2 = (a + j + 2) * 2 + 1 := by omega
  rw [h_eq1] at hy
  have hy' : Word ((3 + k) + 1) ((a + j + 2) * 2 + 1) ys := by
    have : (3 + k) + 1 = 4 + k := by omega
    rwa [this]
  obtain ⟨zs, hz, rfl⟩ := Word_odd_inv hy'
  have h_lin2 : a + j + 2 + (b + j) * 2 < 2 ^ (1 + (3 + k)) := by
    have : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
    omega
  obtain ⟨bs, hb, hmid⟩ := P_word_linear (b + j) r hz (by omega) h_lin2
  have h_eq2 : a + j + 2 + (b + j) * 2 = a + b * 2 + j * 3 + 2 := by omega
  rw [h_eq2] at hb
  have h_lin3 : a + b * 2 + j * 3 + 2 + 2 * 2 < 2 ^ (1 + (3 + k)) := by
    have : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
    omega
  obtain ⟨cs, hc, htwo⟩ := P_word_linear 2 r hb (by omega) h_lin3
  set y := (a + b * 2 + j * 3 + 5) / 2
  have h_eq3 : a + b * 2 + j * 3 + 2 + 2 * 2 = y * 2 + 1 := by omega
  rw [h_eq3] at hc
  have hc' : Word ((2 + k) + 1) (y * 2 + 1) cs := by
    have : (2 + k) + 1 = 3 + k := by omega
    rwa [this]
  obtain ⟨ds, hd, rfl⟩ := Word_odd_inv hc'
  have h_lin4 : y + (a - j - 1) * 2 < 2 ^ (1 + (2 + k)) := by
    have : 2 ^ (1 + (2 + k)) = 2 ^ (2 + k) * 2 := by ring
    omega
  obtain ⟨out, hout, hlast⟩ := P_word_linear (a - j - 1) r hd (by omega) h_lin4
  have hstep : (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ (cfg (fs +> (w ^ (j + 1) +> (out +> r)))) := by
    rw [pow_add_list w j 1, pow_one_list, append_assoc]
    refine frame_step hl.level_frame ?_
    have hin : Inner j (xs +> r) (t +> (zs +> r)) :=
      .InnerP (by simpa only [List.append_assoc, append_assoc] using hp)
    have hgd : I (b + j) ([1] +> (t +> (zs +> r))) (d +> (bs +> r)) := by
      simpa only [d, t, append_cons, append_nil] using G_d (P_G hmid)
    refine inner_column (by omega) hin hgd ?_
    have : a - j = 1 + (a - j - 1) := by omega
    rw [this]
    have hpd : G 1 (d +> (bs +> r)) (w +> (ds +> r)) := by
      have h_d := P_d htwo
      exact P_G (by simpa only [u, w, t, List.append_assoc, append_assoc, append_cons, append_nil] using h_d)
    exact G_add hpd (P_G (G_w (P_G hlast)))
  refine ⟨_, ?_, hstep⟩
  refine .sroot (3 + k) a b (j + 1) fs (out +> r) hl (by omega)
    (.SWord (2 + k) (y + (a - j - 1) * 2) 0 out r (by omega) (by omega) hout hr ?_ ?_)
  · have h_sz := SinglePhase.SZ (h := 3 + k) (a := a) (b := b) (j := j + 1)
      (y + (a - j - 1) * 2) (by omega)
    simpa using h_sz
  · unfold phi; omega

theorem single_mid_descent_closed {k a b j : ℕ} {fs : List Sym} {n u_val : ℕ}
    {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a) (hn : 0 < n)
    (hupper : n ≤ a * 2 + b + 1 - j) (eu : n + (j * 2 + 2) * 2 = u_val * 2 + 1)
    (hw : Word (3 + k) n xs) (hr : Num q r)
    (hready : u_val % 2 = 1 ∨ 2 ^ (3 + k) ≤ u_val + (b + j) * 2)
    (hcap : phi n + (2 ^ (3 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ c, SRoot c ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ c := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have hguard : n % 2 = 1 ∨ 2 ^ (1 + (3 + k)) ≤ n + j * 4 := Or.inl (by omega)
  obtain ⟨u₀, c₀, hu, hub, h0⟩ :=
    counter_inner_total (3 + k) j n (by omega) (Word_bound hw) hguard
  have h_lin0 : n + (j * 2 + 2) * 2 < 2 ^ (1 + (3 + k)) := by
    have : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
    omega
  obtain ⟨eu0, ec0⟩ := GCounterRun_linear h0 h_lin0
  have euu : u_val = u₀ := by omega
  subst u₀ ec0
  have hub' : u_val < 2 ^ (1 + (2 + k)) := by
    have : 1 + (2 + k) = 3 + k := by omega
    rwa [this]
  obtain ⟨v, c₁, h1, hvb⟩ := CounterRun_total
    (fun z' hz' => GCounter_total (2 + k) z' (by omega) hz') (b + j) u_val hub'
  have hodd : v % 2 = 1 := by
    rcases hready with hodd' | hsat
    · exact GCounterRun_odd h1 hodd'
    · refine GCounterRun_saturated h1 (by omega) hub' ?_
      have : 1 + (2 + k) = 3 + k := by omega
      rwa [this]
  by_cases hja : j = a
  · subst hja
    obtain ⟨s, hs, hg⟩ := G_nums c₁ hr
    have hw' : Word ((2 + k) + 1) n xs := by
      have : (2 + k) + 1 = 3 + k := by omega
      rwa [this]
    have hguard' : n % 2 = 1 ∨ 2 ^ (1 + ((2 + k) + 1)) ≤ n + j * 4 := Or.inl (by omega)
    have h0' : CounterRun (GCounter ((2 + k) + 1)) (j * 2 + 2) n (u_val * 2 + 1) 0 := by
      have : (2 + k) + 1 = 3 + k := by omega
      rwa [this]
    have hg' : G (0 + c₁) r s := by simpa using hg
    obtain ⟨ys, hys, hstep⟩ :=
      descent_boundary hl.level_frame hw' (by omega) hguard' h0' h1 hg'
    have e := descent_boundary_balance j b (2 + k) n u_val v 0 c₁ q (by omega) hn hu h0' h1
    have hpu := phi_bounds hu
    refine ⟨_, ?_, hstep⟩
    have h_w0 : (fs ++ w ^ j ++ d) +> (ys +> s) = (fs ++ w ^ j ++ d) +> (w ^ 0 +> (ys +> s)) := rfl
    rw [h_w0]
    refine .sroot (1 + (3 + k)) (j + b) (j * 2 + 1) 0 (fs ++ w ^ j ++ d) (ys +> s)
      (Level_next hl) (by omega)
      (.SWord (2 + k) v (q + c₁ * 2) ys s (by omega) (GCounterRun_positive h1 hu) hys hs
        (.SN (2 + k) v _ (by omega) (by omega) (Or.inl hodd)) ?_)
    have : (2 + k) + 1 = 3 + k := by omega
    rw [this, Nat.zero_add] at e
    omega
  · obtain ⟨y, c₂, hy, hyb, h2⟩ :=
      counter_inner_total (2 + k) 0 v (by omega) hvb (Or.inl hodd)
    have hyb' : y < 2 ^ (1 + (1 + k)) := by
      have : 1 + (1 + k) = 2 + k := by omega
      rwa [this]
    obtain ⟨z, c₃, h3, hzb⟩ := CounterRun_total
      (fun z' hz' => GCounter_total (1 + k) z' (by omega) hz') (a - j - 1) y hyb'
    obtain ⟨s, hs, hg⟩ := G_nums (c₁ + (c₂ + c₃)) hr
    have hw' : Word ((1 + k) + 2) n xs := by
      have : (1 + k) + 2 = 3 + k := by omega
      rwa [this]
    have hguard' : n % 2 = 1 ∨ 2 ^ (1 + ((1 + k) + 2)) ≤ n + j * 4 := Or.inl (by omega)
    have h0' : CounterRun (GCounter ((1 + k) + 2)) (j * 2 + 2) n (u_val * 2 + 1) 0 := by
      have : (1 + k) + 2 = 3 + k := by omega
      rwa [this]
    have h1' : CounterRun (GCounter ((1 + k) + 1)) (b + j) u_val v c₁ := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    have h2' : CounterRun (GCounter ((1 + k) + 1)) 2 v (y * 2 + 1) c₂ := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    have hg' : G (0 + (c₁ + (c₂ + c₃))) r s := by simpa using hg
    obtain ⟨ys, hys, hstep⟩ :=
      descent_inside hl.level_frame (by omega) hw' (by omega) hguard' hodd h0' h1' h2' h3 hg'
    have hz : 0 < z := GCounterRun_positive h3 hy
    refine ⟨_, ?_, hstep⟩
    refine .sroot (3 + k) a b (j + 1) fs (ys +> s) hl (by omega)
      (.SWord (1 + k) z (q + (c₁ + (c₂ + c₃)) * 2) ys s (by omega) hz hys hs ?_ ?_)
    · refine .SN (1 + k) z _ (by omega) (by omega) ?_
      by_cases hzo : z % 2 = 1
      · exact Or.inl hzo
      · right
        obtain ⟨_, ez, _⟩ := GCounterRun_even h3 (by omega)
        refine ⟨by omega, ?_⟩
        have h_pow : 2 ^ (1 + (1 + k)) = 2 ^ (2 + k) := by
          have : 1 + (1 + k) = 2 + k := by omega
          rw [this]
        rw [h_pow, ← hsize]
        by_cases hnear : b ≤ j * 2 + 1
        · omega
        · have h_lin1 : u_val + (b + j) * 2 < 2 ^ (1 + (2 + k)) := by
            have : 2 ^ (1 + (2 + k)) = 2 ^ (2 + k) * 2 := by ring
            omega
          obtain ⟨ev, ec1⟩ := GCounterRun_linear h1 h_lin1
          have h_lin2 : v + 2 * 2 < 2 ^ (1 + (2 + k)) := by
            have : 2 ^ (1 + (2 + k)) = 2 ^ (2 + k) * 2 := by ring
            omega
          obtain ⟨ey, ec2⟩ := GCounterRun_linear h2 h_lin2
          omega
    · have e := descent_inside_balance a b j (1 + k) n u_val v y z 0 c₁ c₂ c₃ q
        (by omega) (by omega) hn hu hy h0' h1' h2' h3
      have hpu := phi_bounds hu
      have hpy := phi_bounds hy
      have h_assoc : 0 + c₁ + c₂ + c₃ = c₁ + (c₂ + c₃) := by omega
      have h_k : (1 + k) + 2 = 3 + k := by omega
      rw [h_assoc, h_k] at e
      omega

theorem G_word_atom {k n : ℕ} {xs : List Sym} {q : ℕ} {r : ListBlank Sym} (i : ℕ)
    (hk : 0 < k) (hn : 0 < n) (hw : Word k n xs) (hr : Num q r) :
    ∃ m c ys s,
      CounterRun (GCounter k) i n m c ∧ Word k m ys ∧ Num (q + c * 2) s ∧
      Atom k (2 ^ k) (phi n + (2 ^ k - 1) * q + i * 2) (ys +> s) ∧
      G i (xs +> r) (ys +> s) := by
  obtain ⟨m, c, ys, s, hc, hy, hs, hg⟩ := G_word_data i hk hw hr
  have e := GCounterRun_balance hc hk hn
  refine ⟨m, c, ys, s, hc, hy, hs, ?_, hg⟩
  have h_eq : phi n + (2 ^ k - 1) * q + i * 2 = phi m + (2 ^ k - 1) * (q + c * 2) := by
    nlinarith
  rw [h_eq]
  refine .AtomWord k (2 ^ k) m (q + c * 2) ys s hk (GCounterRun_positive hc hn) hy hs (by omega) ?_
  right
  have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
  omega

theorem split_O_capacity {a b j l K z Q m c : ℕ}
    (hj : j < a) (hl : 0 < l) (hK : 0 < K) (hz : 0 < z)
    (hcap : (2 ^ l * (z * 2 + 1)) * 2 + (2 ^ (2 + l + K) - 1) * Q ≤
      (a * 2 + b + 1) * 4 + b * 4 + j * 8 + 11)
    (hi : CounterRun (ICounter l) (a - j - 1) 1 m c) :
    phi (m * 2 + 1) + (2 ^ (1 + l) - 1) * (phi z + (2 ^ K - 1) * Q + c * 2) <
      (a * 2 + b + 1) * 4 := by
  have e := ICounterRun_balance hi
  have haj : 1 + (a - j - 1) = a - j := by omega
  rw [haj] at e
  have ephi : phi (m * 2 + 1) = m * 2 + 1 := phi_odd m
  rw [ephi]
  have eq_val : m * 2 + 1 + (2 ^ (1 + l) - 1) * (phi z + (2 ^ K - 1) * Q + c * 2) =
      (a - j) * 2 + 1 + (2 ^ (1 + l) - 1) * (phi z + (2 ^ K - 1) * Q) := by
    nlinarith
  rw [eq_val]
  have hphi := phi_bounds hz
  have hp : 2 ≤ 2 ^ l := by
    have : (2 : ℕ) = 2 ^ 1 := rfl
    rw [this]
    exact pow2_mono (by omega)
  have hT : 2 ≤ 2 ^ K := by
    have : (2 : ℕ) = 2 ^ 1 := rfl
    rw [this]
    exact pow2_mono (by omega)
  have ep : 2 ^ (2 + l + K) = 4 * 2 ^ l * 2 ^ K := by
    rw [Nat.pow_add, Nat.pow_add]
  have hp1 : 2 ^ (1 + l) = 2 * 2 ^ l := by ring
  rw [ep] at hcap
  rw [hp1]
  have hp0 : 1 ≤ 2 ^ l := by omega
  have hT0 : 1 ≤ 2 ^ K := by omega
  have hp2 : 1 ≤ 2 * 2 ^ l := by omega
  have hp4 : 1 ≤ 4 * 2 ^ l * 2 ^ K := by nlinarith
  have hcoef : 2 * (2 * 2 ^ l - 1) * (2 ^ K - 1) ≤ 4 * 2 ^ l * 2 ^ K - 1 := by
    zify [hp0, hT0, hp2, hp4] at hp hT ⊢
    nlinarith
  have hQ : 2 * (2 * 2 ^ l - 1) * (2 ^ K - 1) * Q ≤ (4 * 2 ^ l * 2 ^ K - 1) * Q :=
    Nat.mul_le_mul_right Q hcoef
  have hz' : 2 * (2 * 2 ^ l - 1) * phi z + 6 ≤ (2 ^ l * (z * 2 + 1)) * 2 := by
    have hpz : phi z ≤ z := hphi.2.1
    zify [hp0, hp2, hpz] at hp hpz hz ⊢
    nlinarith
  have h_tot : 2 * ((2 * 2 ^ l - 1) * (phi z + (2 ^ K - 1) * Q)) + 6 ≤
      (2 ^ l * (z * 2 + 1)) * 2 + (4 * 2 ^ l * 2 ^ K - 1) * Q := by
    linarith
  omega

theorem split_head_narrow {h a b j : ℕ} {fs : List Sym} {k m c z e : ℕ}
    (hl : Level h a b fs) (hj : j ≤ a) (hk : 3 ≤ k) (hwidth : k + 2 ≤ h)
    (hi : CounterRun (ICounter k) (b + j) 1 m c)
    (hg : CounterRun (GCounter k) (a - j) m z e) :
    Narrow a j k z := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  by_cases hodd : z % 2 = 1
  · exact Or.inl hodd
  · obtain ⟨_, ez, hm⟩ := GCounterRun_even hg (by omega)
    have hpos := ICounterRun_positive hi (by decide)
    right
    refine ⟨by omega, ?_⟩
    have hsize := hl.level_size
    by_cases hsmall : k + 3 ≤ h
    · have hp : 2 ^ (2 + k) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
      have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
      omega
    · have eh : h - 1 = 1 + k := by omega
      rw [eh] at hsize
      obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
      omega

theorem split_E_capacity {a b j n l K z q m c v e : ℕ}
    (ha : 5 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1) (hj : j ≤ a)
    (hn : 0 < n) (hl : 0 < l) (hK : 0 < K) (hz : 0 < z)
    (he : n + j * 4 + 4 = 2 ^ l * (z * 2 + 1))
    (hcap : phi n + (2 ^ (1 + l + K) - 1) * q ≤ (a * 2 + b + 1) * 4)
    (hi : CounterRun (ICounter l) (b + j) 1 m c)
    (hg : CounterRun (GCounter l) (a - j) m v e) :
    phi v + (2 ^ l - 1) * (phi z + (2 ^ K - 1) * q + (c + e) * 2) <
      (a * 2 + b + 1) * 4 := by
  have e_cap := split_capacity (phi z + (2 ^ K - 1) * q) hl hi hg
  have hpn := phi_bounds hn
  have hpz := phi_bounds hz
  have ep : 2 ^ (1 + l + K) = 2 * 2 ^ l * 2 ^ K := by
    rw [Nat.pow_add, Nat.pow_add]
  rw [ep] at hcap
  have hp : 2 ≤ 2 ^ l := by
    have : (2 : ℕ) = 2 ^ 1 := rfl
    rw [this]
    exact pow2_mono (by omega)
  have hQ : 2 ≤ 2 ^ K := by
    have : (2 : ℕ) = 2 ^ 1 := rfl
    rw [this]
    exact pow2_mono (by omega)
  have hp0 : 1 ≤ 2 ^ l := by omega
  have hQ0 : 1 ≤ 2 ^ K := by omega
  have hp2 : 1 ≤ 2 * 2 ^ l * 2 ^ K := by nlinarith
  have hcoef : 2 * (2 ^ l - 1) * (2 ^ K - 1) ≤ 2 * 2 ^ l * 2 ^ K - 1 := by
    zify [hp0, hQ0, hp2] at hp hQ ⊢
    nlinarith
  have hq : 2 * (2 ^ l - 1) * (2 ^ K - 1) * q ≤ (2 * 2 ^ l * 2 ^ K - 1) * q :=
    Nat.mul_le_mul_right q hcoef
  have hz' : 2 * (2 ^ l - 1) * phi z ≤ n + j * 4 + 4 := by
    have hpz_le : phi z ≤ z := hpz.2.1
    zify [hp0, hpz_le] at hp hpz_le he ⊢
    nlinarith
  have h_dist : 2 * ((2 ^ l - 1) * (phi z + (2 ^ K - 1) * q)) =
      2 * (2 ^ l - 1) * phi z + 2 * (2 ^ l - 1) * (2 ^ K - 1) * q := by ring
  have hx : 2 * ((2 ^ l - 1) * (phi z + (2 ^ K - 1) * q)) ≤ (a * 2 + b + 1) * 4 + j * 4 + 5 := by
    omega
  omega

theorem split_E_one_capacity {a b j n K z q m c e : ℕ}
    (ha : 5 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1) (hj : j < a)
    (hn : 0 < n) (hK : 0 < K) (hz : 0 < z)
    (he : n + j * 4 + 4 = 2 * (z * 2 + 1))
    (hcap : phi n + (2 ^ (2 + K) - 1) * q ≤ (a * 2 + b + 1) * 4)
    (hi : CounterRun (ICounter 1) (b + j) 1 m c)
    (hg : CounterRun (GCounter 1) (a - j) m 3 e) :
    phi z + (2 ^ K - 1) * q + (c + e) * 2 < (a * 2 + b + 1) * 2 := by
  have hm_pos := ICounterRun_positive hi (by decide)
  have e0 := ICounterRun_balance hi
  have e1 := GCounterRun_balance hg (by decide) hm_pos
  have hm := ICounterRun_bound hi (by decide)
  have hpn := phi_bounds hn
  have hpz := phi_bounds hz
  have hpm := phi_bounds hm_pos
  have h_21 : 2 ^ (1 + 1) - 1 = 3 := rfl
  have h_20 : (2 ^ 1 - 1) * 2 = 2 := rfl
  have h_phi3 : phi 3 = 3 := rfl
  rw [h_21] at e0
  rw [h_20, h_phi3] at e1
  have hp_2K : 2 ^ (2 + K) = 2 ^ K * 4 := by ring
  rw [hp_2K] at hcap
  have hq_le : (2 ^ K - 1) * 4 * q ≤ (2 ^ K * 4 - 1) * q :=
    Nat.mul_le_mul_right q (by omega)
  have hq_eq : (2 ^ K - 1) * 4 * q = (2 ^ K - 1) * q * 4 := by ring
  omega

theorem split_E_absorb_root {h a b j : ℕ} {fs : List Sym} {K z m c e Z C : ℕ}
    {ys : List Sym} {Q : ℕ} {s : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hK : 0 < K) (hwidth : K + 2 ≤ h)
    (hz : 0 < z) (hzbound : z < 2 ^ (1 + K))
    (hedge : K + 2 = h → a * 2 + b + 1 + j * 3 + 2 ≤ z * 4)
    (hi : CounterRun (ICounter 1) (b + j) 1 m c)
    (hg : CounterRun (GCounter 1) (a - j) m 3 e)
    (hright : CounterRun (GCounter K) (c + e) z Z C)
    (hw : Word K Z ys) (hr : Num Q s)
    (hcap : phi Z + (2 ^ K - 1) * Q ≤ (a * 2 + b + 1) * 2) :
    SRoot (cfg (fs +> (w ^ (j + 1) +> (ys +> s)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hm := ICounterRun_positive hi (by decide)
  have hmb : m < 4 := ICounterRun_bound hi (by decide)
  have ei := ICounterRun_balance hi
  have eg := GCounterRun_balance hg (by decide) hm
  have hphi := phi_bounds hm
  have h_21 : 2 ^ (1 + 1) - 1 = 3 := rfl
  have h_20 : (2 ^ 1 - 1) * 2 = 2 := rfl
  have h_phi3 : phi 3 = 3 := rfl
  rw [h_21] at ei
  rw [h_20, h_phi3] at eg
  have he : a - j - 1 ≤ e := by omega
  have hZ : 0 < Z := GCounterRun_positive hright hz
  have hlower : Z % 2 = 0 → (a - (j + 1)) * 2 + 2 ≤ Z := by
    intro heven
    obtain ⟨_, eZ, _⟩ := GCounterRun_even hright heven
    omega
  by_cases hsmall : K + 3 ≤ h
  · refine small_single_root (j := j + 1) hl (by omega) hK hsmall hZ hw hr hcap hlower ?_
    rintro rfl hfar
    have hright' : CounterRun (GCounter 1) (2 + (c + e - 2)) z Z C := by
      have : 2 + (c + e - 2) = c + e := by omega
      rwa [this]
    exact (GCounterRun_one hright' hz hzbound).1
  · have eK : K + 2 = h := by omega
    have hedge' := hedge eK
    refine .sroot h a b (j + 1) fs (ys +> s) hl (by omega)
      (.SWord K Z Q ys s hK hZ hw hr ?_ (by omega))
    refine .SN K Z Q (by omega) (by omega) ?_
    by_cases hodd : Z % 2 = 1
    · exact Or.inl hodd
    · right
      refine ⟨hlower (by omega), ?_⟩
      obtain ⟨_, eZ, _⟩ := GCounterRun_even hright (by omega)
      have hsize := hl.level_size
      have hk_sub : h - 1 = 1 + K := by omega
      rw [hk_sub] at hsize
      clear hcap hw hr hright hi hg hl hlower hedge
      omega

theorem split_E_positive_closed {h a b j : ℕ} {fs : List Sym} {n l K z : ℕ}
    {ys : List Sym} {q : ℕ} {r input : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hn : 0 < n) (hlpos : 0 < l)
    (hlwidth : l + 2 ≤ h) (hK : 0 < K) (hz : 0 < z) (hrank : 1 + l + K ≤ h)
    (hedge : l = 1 → K + 2 = h → a * 2 + b + 1 + j * 3 + 2 ≤ z * 4)
    (hy : Word K z ys) (hr : Num q r)
    (he : n + j * 4 + 4 = 2 ^ l * (z * 2 + 1))
    (hcap : phi n + (2 ^ (1 + l + K) - 1) * q ≤ (a * 2 + b + 1) * 4)
    (hp : P (j * 2 + 2) input ([0, 0] ^ l +> (t +> (ys +> r)))) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> input))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨m, c, hi, hm⟩ :=
    CounterRun_total (ICounter_total l) (b + j) 1 (Word_bound (Word_one l))
  obtain ⟨v, e, hg, hv⟩ :=
    CounterRun_total (fun z' hz' => GCounter_total l z' hlpos hz') (a - j) m hm
  obtain ⟨Z, C, zs, s, hright, hzs, hs, hat, hrun⟩ :=
    G_word_atom (c + e) hK hz hy hr
  obtain ⟨xs, hx, hstep⟩ :=
    split_root hl.level_frame hj hlpos hp hi hg hrun
  refine ⟨cfg (fs +> (w ^ j +> (xs +> (zs +> s)))), ?_, hstep⟩
  have htotal := split_E_capacity ha hab hba hj hn hlpos hK hz he hcap hi hg
  have hvpos : 0 < v := GCounterRun_positive hg (ICounterRun_positive hi (by decide))
  by_cases hlarge : 3 ≤ l
  · right
    exact .droot h a b j fs (xs +> (zs +> s)) hl hj
      (.DWord l v xs K (2 ^ K) _ (zs +> s) hlpos hvpos hx hat
        (.DN l v K (2 ^ K) hlarge hlwidth (split_head_narrow hl hj hlarge hlwidth hi hg) (by omega))
        (by omega))
  · rcases l with _ | _ | _ | l'
    · omega
    · by_cases hedgej : j = a
      · right
        exact .droot h a b j fs (xs +> (zs +> s)) hl hj
          (.DWord 1 v xs K (2 ^ K) _ (zs +> s) (by decide) hvpos hx hat
            (.D1 v K (2 ^ K) (by omega) (Or.inl hedgej)) (by omega))
      · by_cases hv3 : v = 3
        · subst hv3
          left
          have ehw := Word_max hx rfl
          change xs = w at ehw
          rw [ehw]
          change SRoot (cfg (fs +> (w ^ j +> (w +> (zs +> s)))))
          have ew : w ^ j +> (w +> (zs +> s)) = w ^ (j + 1) +> (zs +> s) := by
            rw [pow_add_list w j 1, pow_one_list, append_assoc]
          rw [ew]
          refine split_E_absorb_root hl (by omega) hK (by omega) hz (Word_bound hy)
            (hedge rfl) hi hg hright hzs hs ?_
          have hstrong := split_E_one_capacity ha hab hba (by omega) hn hK hz he hcap hi hg
          have e_bal := GCounterRun_balance hright hK hz
          nlinarith
        · have hnear : j + 1 = a := by
            by_cases hfar : j + 2 ≤ a
            · have hg' : CounterRun (GCounter 1) (2 + (a - j - 2)) m v e := by
                have : 2 + (a - j - 2) = a - j := by omega
                rwa [this]
              have := (GCounterRun_one hg' (ICounterRun_positive hi (by decide)) hm).1
              omega
            · omega
          have ev : v = 1 := by
            by_cases heven : v % 2 = 0
            · obtain ⟨_, ev', _⟩ := GCounterRun_even hg heven
              have := ICounterRun_positive hi (by decide)
              change v < 4 at hv
              omega
            · change v < 4 at hv
              omega
          subst ev
          right
          exact .droot h a b j fs (xs +> (zs +> s)) hl hj
            (.DWord 1 1 xs K (2 ^ K) _ (zs +> s) (by decide) (by decide) hx hat
              (.D1 1 K (2 ^ K) (by omega) (Or.inr ⟨hnear, rfl⟩)) (by omega))
    · right
      refine .droot h a b j fs (xs +> (zs +> s)) hl hj
        (.DWord 2 v xs K (2 ^ K) _ (zs +> s) (by decide) hvpos hx hat ?_ (by omega))
      refine .D2 v K (2 ^ K) ?_ (by omega) ?_
      · by_cases hodd : v % 2 = 1
        · exact Or.inl hodd
        · right
          obtain ⟨_, ev, _⟩ := GCounterRun_even hg (by omega)
          have := ICounterRun_positive hi (by decide)
          omega
      · right
        have hsize := hl.level_size
        have hpow : 2 ^ (K + 2) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
        have : 2 ^ (K + 2) = 2 ^ K * 4 := by ring
        nlinarith
    · omega

theorem split_E_end_closed {h a b j : ℕ} {fs : List Sym} {l q : ℕ}
    {r input : ListBlank Sym}
    (hl : Level h a b fs) (hjpos : 0 < j) (hj : j ≤ a) (hwidth : l + 2 = h)
    (hr : Num q r) (hq : q ≤ 1)
    (hp : P (j * 2 + 2) input ([0, 0] ^ l +> (t +> (d +> r)))) :
    ∃ out, DRoot out ∧ (cfg (fs +> (w ^ j +> input))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize := hl.level_size
  have hk_sub : h - 1 = 1 + l := by omega
  rw [hk_sub] at hsize
  obtain ⟨m, c, hi, hm⟩ :=
    CounterRun_total (ICounter_total l) (b + j) 1 (Word_bound (Word_one l))
  obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
  subst em ec
  obtain ⟨v, e, hg, hv⟩ :=
    CounterRun_total (fun z' hz' => GCounter_total l z' (by omega) hz') (a - j) (1 + (b + j)) hm
  obtain ⟨ev, ee⟩ := GCounterRun_linear hg (by omega)
  subst ee
  obtain ⟨xs, hx, hstep⟩ :=
    split_root hl.level_frame hj (by omega) hp hi hg (.G0 (d +> r))
  refine ⟨cfg (fs +> (w ^ j +> (xs +> (d +> r)))), ?_, hstep⟩
  refine .droot h a b j fs (xs +> (d +> r)) hl hj
    (.DWord l v xs 1 1 (q * 2 + 1) (d +> r) (by omega) (by omega) hx
      (.AtomEnd q r hr hq)
      (.DN l v 1 1 (by omega) (by omega) (split_head_narrow hl hj (by omega) (by omega) hi hg) (by omega))
      ?_)
  have hpv := phi_bounds (by omega : 0 < v)
  have hp1 : 2 ^ (1 + l) = 2 ^ l * 2 := by ring
  have hq3 : (2 ^ l - 1) * (q * 2 + 1) ≤ (2 ^ l - 1) * 3 := Nat.mul_le_mul_left _ (by omega)
  omega

theorem split_O_small_budget {h a b j : ℕ} {fs : List Sym} {K z m c Z C : ℕ}
    (hl : Level h a b fs) (hj : j < a) (hK : 0 < K) (hwidth : K + 2 ≤ h) (hz : 0 < z)
    (hedge : K + 2 = h → a * 2 + b + 1 + j * 3 + 2 ≤ z * 4)
    (hi : CounterRun (ICounter 1) (a - j - 1) 1 m c)
    (hg : CounterRun (GCounter K) c z Z C) (heven : Z % 2 = 0) :
    2 ^ (1 + K) ≤ Z + (b + j + 1) * 2 := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize := hl.level_size
  obtain ⟨_, eZ, _⟩ := GCounterRun_even hg heven
  by_cases hsmall : K + 3 ≤ h
  · have hp : 2 ^ (2 + K) ≤ 2 ^ (h - 1) := pow2_mono (by omega)
    have : 2 ^ (2 + K) = 2 ^ (1 + K) * 2 := by ring
    omega
  · have eK : K + 2 = h := by omega
    have hedge' := hedge eK
    have hk_sub : h - 1 = 1 + K := by omega
    rw [hk_sub] at hsize
    have ei := ICounterRun_balance hi
    have hm : m < 4 := ICounterRun_bound hi (by decide)
    have h_21 : 2 ^ (1 + 1) - 1 = 3 := rfl
    rw [h_21] at ei
    omega

theorem split_O_positive_closed {h a b j : ℕ} {fs : List Sym} {l K z : ℕ}
    {ys : List Sym} {Q : ℕ} {r input r₀ r₁ : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hlpos : 0 < l) (hlwidth : l + 2 ≤ h)
    (hK : 0 < K) (hz : 0 < z) (hrank : 1 + l + K ≤ h)
    (hedge : l = 1 → K + 2 = h → a * 2 + b + 1 + j * 3 + 2 ≤ z * 4)
    (hy : Word K z ys) (hr : Num Q r)
    (hcap : (2 ^ l * (z * 2 + 1)) * 2 + (2 ^ (2 + l + K) - 1) * Q ≤
      (a * 2 + b + 1) * 4 + b * 4 + j * 8 + 11)
    (hin : Inner j input (t +> r₀)) (hmid : G (b + j) r₀ r₁)
    (hp : P 2 r₁ ([0, 0] ^ l +> (t +> (ys +> r)))) :
    ∃ out, DRoot out ∧ (cfg (fs +> (w ^ j +> input))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  obtain ⟨m, c, hi, hm⟩ :=
    CounterRun_total (ICounter_total l) (a - j - 1) 1 (Word_bound (Word_one l))
  obtain ⟨Z, C, zs, s, hright, hzs, hs, hat, hrun⟩ :=
    G_word_atom c hK hz hy hr
  obtain ⟨xs, hx, hstep⟩ :=
    split_inside hl.level_frame hj hin hmid hp hi hrun
  refine ⟨cfg (fs +> (w ^ j +> (xs +> (zs +> s)))), ?_, hstep⟩
  have htotal := split_O_capacity hj hlpos hK hz hcap hi
  refine .droot h a b j fs (xs +> (zs +> s)) hl (by omega) ?_
  by_cases hl1 : l = 1
  · subst hl1
    have hatom : Atom K (Nat.min (2 ^ K) (b + j + 1)) (phi z + (2 ^ K - 1) * Q + c * 2) (zs +> s) := by
      have e_bal := GCounterRun_balance hright hK hz
      have h_eq : phi z + (2 ^ K - 1) * Q + c * 2 = phi Z + (2 ^ K - 1) * (Q + C * 2) := by
        nlinarith
      rw [h_eq]
      refine .AtomWord K (Nat.min (2 ^ K) (b + j + 1)) Z (Q + C * 2) zs s
        hK (GCounterRun_positive hright hz) hzs hs (Nat.min_le_left _ _) ?_
      by_cases hodd : Z % 2 = 1
      · exact Or.inl hodd
      · right
        by_cases hmin : 2 ^ K ≤ b + j + 1
        · have hmin_eq : Nat.min (2 ^ K) (b + j + 1) = 2 ^ K := by unfold Nat.min; omega
          rw [hmin_eq]
          have : 2 ^ (1 + K) = 2 ^ K * 2 := by ring
          omega
        · have hmin_eq : Nat.min (2 ^ K) (b + j + 1) = b + j + 1 := by unfold Nat.min; omega
          rw [hmin_eq]
          exact split_O_small_budget hl hj hK (by omega) hz (hedge rfl) hi hright (by omega)
    exact .DWord 2 (m * 2 + 1) xs K (Nat.min (2 ^ K) (b + j + 1)) _ (zs +> s)
      (by decide) (by omega) hx hatom
      (.D2 (m * 2 + 1) K _ (Or.inl (by omega)) (by omega) (Or.inr (Nat.min_le_right _ _)))
      (by omega)
  · have hx' : Word (1 + l) (m * 2 + 1) xs := by
      have : 1 + l = l + 1 := by omega
      rwa [this]
    refine .DWord (1 + l) (m * 2 + 1) xs K (2 ^ K) _ (zs +> s)
      (by omega) (by omega) hx' hat ?_ (by omega)
    by_cases hsmall : l + 3 ≤ h
    · exact .DN (1 + l) (m * 2 + 1) K (2 ^ K) (by omega) (by omega) (Or.inl (by omega)) (by omega)
    · have el : 1 + l = h - 1 := by omega
      have hsize := hl.level_size
      rw [← el] at hsize
      obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
      have hm_eq : m * 2 + 1 = (a - j) * 2 + 1 := by omega
      rw [hm_eq, el]
      exact .DY K (2 ^ K) (by omega)

theorem split_O_end_closed {h a b j : ℕ} {fs : List Sym} {l q : ℕ}
    {r input r₀ r₁ : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hwidth : l + 2 = h)
    (hr : Num q r) (hq : q ≤ 1)
    (hin : Inner j input (t +> r₀)) (hmid : G (b + j) r₀ r₁)
    (hp : P 2 r₁ ([0, 0] ^ l +> (t +> (d +> r)))) :
    ∃ out, DRoot out ∧ (cfg (fs +> (w ^ j +> input))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize := hl.level_size
  have hk_sub : h - 1 = 1 + l := by omega
  rw [hk_sub] at hsize
  obtain ⟨m, c, hi, hm⟩ :=
    CounterRun_total (ICounter_total l) (a - j - 1) 1 (Word_bound (Word_one l))
  obtain ⟨em, ec⟩ := ICounterRun_linear hi (by omega)
  subst ec
  obtain ⟨xs, hx, hstep⟩ :=
    split_inside hl.level_frame hj hin hmid hp hi (.G0 (d +> r))
  refine ⟨cfg (fs +> (w ^ j +> (xs +> (d +> r)))), ?_, hstep⟩
  have hx' : Word (h - 1) ((a - j) * 2 + 1) xs := by
    have h1 : h - 1 = l + 1 := by omega
    have h2 : (a - j) * 2 + 1 = m * 2 + 1 := by omega
    rwa [h1, h2]
  refine .droot h a b j fs (xs +> (d +> r)) hl (by omega)
    (.DWord (h - 1) ((a - j) * 2 + 1) xs 1 1 (q * 2 + 1) (d +> r)
      (by omega) (by omega) hx' (.AtomEnd q r hr hq) (.DY 1 1 (by decide)) ?_)
  rw [phi_odd, hk_sub, ← hsize]
  have hq3 : (a * 2 + b + 1 - 1) * (q * 2 + 1) ≤ (a * 2 + b + 1 - 1) * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  omega

theorem single_y_split_closed {h a b j : ℕ} {fs : List Sym} {k : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hmin : h ≤ k + 1) (hmax : k ≤ h)
    (heven : (a + b * 2 + j * 3 + 2) % 2 = 0)
    (hw : Word (1 + k) ((a - j) * 2 + 1) xs) (hr : Num q r)
    (hcap : phi ((a - j) * 2 + 1) + (2 ^ (1 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ out, DRoot out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize := hl.level_size
  have hpow : a * 2 + b + 1 ≤ 2 ^ k := by
    rw [hsize]
    exact pow2_mono (by omega)
  have hX : a + b * 2 + j * 3 + 6 < (a * 2 + b + 1) * 2 := by omega
  have h_lin1 : (a - j) * 2 + 1 + (j * 2 + 2) * 2 < 2 ^ (1 + (1 + k)) := by
    have : 2 ^ (1 + (1 + k)) = 2 ^ k * 4 := by ring
    omega
  obtain ⟨xs₀, h0, hfirst⟩ := P_word_linear (j * 2 + 2) r hw (by omega) h_lin1
  have h_eq1 : (a - j) * 2 + 1 + (j * 2 + 2) * 2 = (a + j + 2) * 2 + 1 := by omega
  rw [h_eq1] at h0
  have h0' : Word (k + 1) ((a + j + 2) * 2 + 1) xs₀ := by
    have : k + 1 = 1 + k := by omega
    rwa [this]
  obtain ⟨ys₀, hys0, rfl⟩ := Word_odd_inv h0'
  have h_lin2 : a + j + 2 + (b + j) * 2 < 2 ^ (1 + k) := by
    have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    omega
  obtain ⟨xs₁, h1, hmid⟩ := P_word_linear (b + j) r hys0 (by omega) h_lin2
  have h_eq2 : a + j + 2 + (b + j) * 2 = a + b * 2 + j * 3 + 2 := by omega
  rw [h_eq2] at h1
  have h_lin3 : a + b * 2 + j * 3 + 2 + 2 * 2 < 2 ^ (1 + k) := by
    have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    omega
  obtain ⟨xs₂, h2, htwo⟩ := P_word_linear 2 r h1 (by omega) h_lin3
  have h_eq3 : a + b * 2 + j * 3 + 2 + 2 * 2 = a + b * 2 + j * 3 + 6 := by omega
  rw [h_eq3] at h2
  have hmark : a + b * 2 + j * 3 + 6 ≠ 2 ^ k := by
    by_cases hkh : k = h
    · subst hkh
      have : k = (k - 1) + 1 := by omega
      conv_rhs => rw [this, pow2_succ_right, ← hsize]
      omega
    · have ek : k = h - 1 := by omega
      rw [ek, ← hsize]
      omega
  obtain ⟨l, K, z, ys, erank, evalue, hy, es, eone⟩ :=
    Word_split h2 (by omega) hmark
  have hlpos : 0 < l := by
    rcases l with _ | l'
    · change a + b * 2 + j * 3 + 6 = 1 * (z * 2 + 1) at evalue
      omega
    · omega
  have hz : 0 < z := by
    rcases z with _ | z'
    · have ep : 2 ^ l ≤ 2 ^ (h - 1) := pow2_mono (by omega)
      nlinarith
    · omega
  have hlwidth : l + 2 ≤ h := by
    by_contra hlt
    have ep : 2 ^ (h - 1) ≤ 2 ^ l := pow2_mono (by omega)
    nlinarith
  have hq : q ≤ 1 := by
    rw [phi_odd] at hcap
    have : 2 ^ (1 + k) = 2 ^ k * 2 := by ring
    by_contra hgt
    have hq2 : (2 ^ (1 + k) - 1) * 2 ≤ (2 ^ (1 + k) - 1) * q :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  rw [es] at htwo
  rcases K with _ | K
  · have el : l + 2 = h := by omega
    have hb_hy : z < 2 := Word_bound hy
    have ez : z = 1 := by omega
    subst ez
    have eys := Word_max hy rfl
    change ys = d at eys
    subst eys
    exact split_O_end_closed (l := l) hl hj el hr hq
      (.InnerP (by simpa only [List.append_assoc, append_assoc] using hfirst))
      (P_G hmid) (by simpa only [List.append_assoc, append_assoc] using htwo)
  · refine split_O_positive_closed (l := l) (K := K + 1) (z := z) (Q := q)
      hl hj hlpos hlwidth (by omega) hz (by omega) ?_ hy hr ?_
      (.InnerP (by simpa only [List.append_assoc, append_assoc] using hfirst))
      (P_G hmid) (by simpa only [List.append_assoc, append_assoc] using htwo)
    · rintro rfl eK
      change a + b * 2 + j * 3 + 6 = 2 * (z * 2 + 1) at evalue
      omega
    · have h_exp : 2 + l + (K + 1) = 1 + k := by omega
      rw [h_exp, ← evalue]
      rw [phi_odd] at hcap
      omega

theorem single_y_closed {k a b j : ℕ} {fs : List Sym} {K : ℕ} {xs : List Sym}
    {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hmin : 3 + k ≤ K + 1) (hmax : K ≤ 4 + k) (hinside : K < 3 + k ∨ j < a)
    (hw : Word K ((a - j) * 2 + 1) xs) (hr : Num q r)
    (hcap : phi ((a - j) * 2 + 1) + (2 ^ K - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  by_cases hK_low : K = 2 + k
  · subst hK_low
    obtain ⟨out, hout, hstep⟩ := single_y_low_closed hl hj hw hr hcap
    exact ⟨out, Or.inl hout, hstep⟩
  · have hj' : j < a := by
      rcases hinside with h1 | h2 <;> omega
    by_cases hodd : (a + b * 2 + j * 3 + 2) % 2 = 1
    · have hodd0 : (a + j + 2) % 2 = 1 := by omega
      by_cases hK_mid : K = 3 + k
      · subst hK_mid
        obtain ⟨out, hout, hstep⟩ :=
          single_mid_descent_closed hl hj (by omega) (by omega) (by omega) hw hr (Or.inl hodd0) hcap
        exact ⟨out, Or.inl hout, hstep⟩
      · have eK : K = 4 + k := by omega
        subst eK
        have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
          have : 3 + k - 1 = 2 + k := by omega
          rw [← this, hl.level_size]
        have eq0 : q = 0 := by
          rw [phi_odd] at hcap
          have : 2 ^ (4 + k) = 2 ^ (2 + k) * 4 := by ring
          by_contra hgt
          have hq1 : (2 ^ (4 + k) - 1) * 1 ≤ (2 ^ (4 + k) - 1) * q :=
            Nat.mul_le_mul_left _ (by omega)
          omega
        subst eq0
        obtain ⟨out, hout, hstep⟩ := single_y_top_odd_closed hl hj' hodd hw hr
        exact ⟨out, Or.inl hout, hstep⟩
    · have heven' : (a + b * 2 + j * 3 + 2) % 2 = 0 := by omega
      rcases K with _ | K'
      · omega
      · have hw' : Word (1 + K') ((a - j) * 2 + 1) xs := by
          have : 1 + K' = K' + 1 := by omega
          rwa [this]
        have hcap' : phi ((a - j) * 2 + 1) + (2 ^ (1 + K') - 1) * q ≤ (a * 2 + b + 1) * 4 := by
          have : 1 + K' = K' + 1 := by omega
          rwa [this]
        obtain ⟨out, hout, hstep⟩ :=
          single_y_split_closed hl hj' (by omega) (by omega) heven' hw' hr hcap'
        exact ⟨out, Or.inr hout, hstep⟩

theorem single_even_split_closed {h a b j : ℕ} {fs : List Sym} {k n : ℕ}
    {xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level h a b fs) (hj : j ≤ a) (hmin : h ≤ k + 1) (hmax : k ≤ h)
    (hn : 0 < n) (heven : n % 2 = 0)
    (hlower : a * 2 + b + 1 < n + j * 4 + 4)
    (hupper : n + j * 4 + 4 < (a * 2 + b + 1) * 3)
    (hlinear : n + j * 4 + 4 < 2 ^ (1 + k))
    (hmarker : n + j * 4 + 4 ≠ 2 ^ k)
    (hphase : k = h → a * 2 + b + 1 - j ≤ n)
    (hq : k + 1 = h → q ≤ 1)
    (hzero : j = 0 → n * 2 + 8 < (a * 2 + b + 1) * 3)
    (hw : Word k n xs) (hr : Num q r)
    (hcap : phi n + (2 ^ k - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize := hl.level_size
  obtain ⟨zs, hzs, hp⟩ := P_word_linear (j * 2 + 2) r hw (by omega) (by omega)
  have h_eq : n + (j * 2 + 2) * 2 = n + j * 4 + 4 := by omega
  rw [h_eq] at hzs
  obtain ⟨l, K, z, ys, erank, evalue, hy, es, eone⟩ :=
    Word_split hzs (by omega) hmarker
  have hlpos : 0 < l := by
    rcases l with _ | l'
    · change n + j * 4 + 4 = 1 * (z * 2 + 1) at evalue
      omega
    · omega
  have hz : 0 < z := by
    rcases z with _ | z'
    · have ep : 2 ^ l ≤ 2 ^ (h - 1) := pow2_mono (by omega)
      nlinarith
    · omega
  have hlwidth : l + 2 ≤ h := by
    by_contra hlt
    have ep : 2 ^ (h - 1) ≤ 2 ^ l := pow2_mono (by omega)
    nlinarith
  rw [es] at hp
  rcases K with _ | K
  · have el : l + 2 = h := by omega
    have hb_hy : z < 2 := Word_bound hy
    have ez : z = 1 := by omega
    subst ez
    have eys := Word_max hy rfl
    change ys = d at eys
    subst eys
    have hjpos : 0 < j := by
      rcases j with _ | j'
      · have h0 := hzero rfl
        have hk_sub : h - 1 = 1 + l := by omega
        rw [hk_sub] at hsize
        have : 2 ^ (1 + l) = 2 ^ l * 2 := by ring
        nlinarith
      · omega
    obtain ⟨out, hout, hstep⟩ :=
      split_E_end_closed hl hjpos hj el hr (hq (by omega))
        (by simpa only [List.append_assoc, append_assoc] using hp)
    exact ⟨out, Or.inr hout, hstep⟩
  · refine split_E_positive_closed (n := n) (l := l) (K := K + 1) (z := z) (q := q)
      hl hj hn hlpos hlwidth (by omega) hz (by omega) ?_ hy hr evalue ?_
      (by simpa only [List.append_assoc, append_assoc] using hp)
    · rintro rfl eK
      have hph := hphase (by omega)
      change n + j * 4 + 4 = 2 * (z * 2 + 1) at evalue
      omega
    · have : 1 + l + (K + 1) = k := by omega
      rwa [this]

theorem single_x_low_closed {k a b j : ℕ} {fs xs : List Sym} {q : ℕ} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hw : Word (2 + k) (a * 2 + b + 1 - j) xs) (hr : Num q r) (hq : q ≤ 1)
    (hcap : phi (a * 2 + b + 1 - j) + (2 ^ (2 + k) - 1) * q ≤ (a * 2 + b + 1) * 4) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  by_cases hodd : (a * 2 + b + 1 - j) % 2 = 1
  · obtain ⟨out, hout, hstep⟩ := single_x_low_odd_closed hl hj hodd hw hr hcap
    exact ⟨out, Or.inl hout, hstep⟩
  · by_cases hlate : 2 ^ (3 + k) ≤ a * 2 + b + 1 - j + j * 4 + 4
    · have hp : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
      by_cases hab_eq : a = b
      · subst hab_eq
        have ej : j = a - 1 := by omega
        subst ej
        have hw' : Word ((1 + k) + 1) (a * 2 + 2) xs := by
          have h1 : (1 + k) + 1 = 2 + k := by omega
          have h2 : a * 2 + 2 = a * 2 + a + 1 - (a - 1) := by omega
          rwa [h1, h2]
        have hl' : Level (2 + (1 + k)) a a fs := by
          have : 2 + (1 + k) = 3 + k := by omega
          rwa [this]
        obtain ⟨out, hout, hstep⟩ :=
          late_second_Q_recover_closed hl' hw' hr (by omega)
        exact ⟨out, Or.inl hout, hstep⟩
      · have eb : b = a + 1 := by omega
        subst eb
        have ej : j = a := by omega
        subst ej
        have hw' : Word ((1 + k) + 1) (j * 2 + 2) xs := by
          have h1 : (1 + k) + 1 = 2 + k := by omega
          have h2 : j * 2 + 2 = j * 2 + (j + 1) + 1 - j := by omega
          rwa [h1, h2]
        have hl' : Level (2 + (1 + k)) j (j + 1) fs := by
          have : 2 + (1 + k) = 3 + k := by omega
          rwa [this]
        obtain ⟨out, hout, hstep⟩ :=
          late_first_Q_boundary_closed hl' hw' hr hq
        exact ⟨out, Or.inl hout, hstep⟩
    · refine single_even_split_closed (h := 3 + k) (k := 2 + k) (n := a * 2 + b + 1 - j) (q := q)
        hl hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        ?_ (by omega) (by omega) (fun _ => hq) (by omega) hw hr hcap
      have : 1 + (2 + k) = 3 + k := by omega
      rw [this]
      omega

theorem pow2_mod7 (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    have : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
    omega

theorem CounterRun_unique {step : ℕ → ℕ → ℕ → Prop}
    (hd : ∀ n m c m' c', step n m c → step n m' c' → m = m' ∧ c = c')
    {i n m c : ℕ} (h : CounterRun step i n m c) :
    ∀ {m' c'}, CounterRun step i n m' c' → m = m' ∧ c = c' := by
  induction h with
  | Counter0 _ =>
    intro m' c' h'
    cases h'
    exact ⟨rfl, rfl⟩
  | @CounterS i' n' m₀ z c₀ d hs _ ih =>
    intro m' c' h'
    cases h' with
    | CounterS hs' hr' =>
      obtain ⟨rfl, rfl⟩ := hd _ _ _ _ _ hs hs'
      obtain ⟨rfl, rfl⟩ := ih hr'
      exact ⟨rfl, rfl⟩

theorem GCounterRun_unique {k i n m c : ℕ} (h : CounterRun (GCounter k) i n m c)
    {m' c' : ℕ} (h' : CounterRun (GCounter k) i n m' c') : m = m' ∧ c = c' := by
  refine CounterRun_unique (fun n₀ m₁ c₁ m₂ c₂ h1 h2 => ?_) h h'
  cases h1 <;> cases h2 <;> omega

theorem pow2_mod15 (n : ℕ) :
    2 ^ n % 15 = 1 ∨ 2 ^ n % 15 = 2 ∨ 2 ^ n % 15 = 4 ∨ 2 ^ n % 15 = 8 := by
  induction n with
  | zero => exact Or.inl rfl
  | succ n ih =>
    have : 2 ^ (n + 1) = 2 ^ n * 2 := by ring
    omega

def RootProgress (c : Cfg Sym Q) : Prop :=
  (∃ out, Normal out ∧ (c [tm1]⊢⁺ out)) ∨ NonHaltFrom tm1 c

theorem split_O_word_closed {h a b j : ℕ} {fs : List Sym} {k x : ℕ}
    {xs : List Sym} {q : ℕ} {r input r₀ : ListBlank Sym}
    (hl : Level h a b fs) (hj : j < a) (hk : 0 < k) (hwidth : k + 1 ≤ h)
    (heven : x % 2 = 0) (hlower : 2 ^ k < x + 4) (hupper : x + 4 < 2 ^ (1 + k))
    (hend : (x + 4) * 2 = 2 ^ k * 3 → k + 1 = h ∧ q ≤ 1)
    (hw : Word k x xs) (hr : Num q r)
    (hcap : (x + 4) * 2 + (2 ^ (1 + k) - 1) * q ≤ (a * 2 + b + 1) * 4 + b * 4 + j * 8 + 11)
    (hin : Inner j input (t +> r₀)) (hmid : G (b + j) r₀ (xs +> r)) :
    ∃ out, DRoot out ∧ (cfg (fs +> (w ^ j +> input))) [tm1]⊢⁺ out := by
  obtain ⟨zs, hzs, hp⟩ := P_word_linear 2 r hw hk (by omega)
  obtain ⟨l, K, z, ys, erank, evalue, hy, es, eone⟩ :=
    Word_split hzs (by omega) (by omega)
  have hlpos : 0 < l := by
    rcases l with _ | l'
    · change x + 2 * 2 = 1 * (z * 2 + 1) at evalue
      omega
    · omega
  have hz : 0 < z := by
    rcases z with _ | z'
    · have ep : 2 ^ l ≤ 2 ^ k := pow2_mono (by omega)
      nlinarith
    · omega
  rw [es] at hp
  rcases K with _ | K
  · have hb_hy : z < 2 := Word_bound hy
    have ez : z = 1 := by omega
    subst ez
    have eys := Word_max hy rfl
    change ys = d at eys
    subst eys
    have hk_eq : k = 1 + l := by omega
    have h_end_cond : (x + 4) * 2 = 2 ^ k * 3 := by
      rw [hk_eq]
      have : 2 ^ (1 + l) = 2 ^ l * 2 := by ring
      omega
    obtain ⟨hkh, hq⟩ := hend h_end_cond
    exact split_O_end_closed (l := l) hl hj (by omega) hr hq hin hmid
      (by simpa only [List.append_assoc, append_assoc] using hp)
  · refine split_O_positive_closed (l := l) (K := K + 1) (z := z) (Q := q)
      hl hj hlpos (by omega) (by omega) hz (by omega) (by omega) hy hr ?_ hin hmid
      (by simpa only [List.append_assoc, append_assoc] using hp)
    have h_exp : 2 + l + (K + 1) = 1 + k := by omega
    rw [h_exp, ← evalue]
    simpa only [Nat.add_assoc] using hcap

theorem single_x_mid_closed {k a b j : ℕ} {fs xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hw : Word (3 + k) (a * 2 + b + 1 - j) xs) (hr : Num 0 r) :
    RootProgress (cfg (fs +> (w ^ j +> (xs +> r)))) := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have hp4 : 2 ^ (2 + k) = 2 ^ k * 4 := by ring
  have hmod := pow2_mod7 (2 + k)
  rw [← hsize] at hmod
  have hcap : phi (a * 2 + b + 1 - j) + (2 ^ (3 + k) - 1) * 0 ≤ (a * 2 + b + 1) * 4 := by
    unfold phi; omega
  by_cases heven : (a * 2 + b + 1 - j) % 2 = 0
  · by_cases hmark : a * 2 + b + 1 - j + j * 4 + 4 = 2 ^ (3 + k)
    · have hp : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
      have eb : b = a ∧ a = j + 1 := by
        clear hmod hw hr hl hcap
        omega
      rcases eb with ⟨eb_eq, ea⟩
      subst b
      right
      refine translated_word_nonhalt (k := 3 + k) hl.level_frame ea (by omega) ?_
      have : a * 2 + 2 = a * 2 + a + 1 - j := by omega
      rwa [this]
    · left
      have hp1 : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
      exact single_even_split_closed (h := 3 + k) (k := 3 + k) (n := a * 2 + b + 1 - j) (q := 0)
        hl hj (by omega) (by omega) (by omega) heven (by omega) (by omega)
        (by omega) hmark (by omega) (by omega) (by omega) hw hr hcap
  · obtain ⟨u_val, eu⟩ : ∃ u_val, a * 2 + b + 1 - j + (j * 2 + 2) * 2 = u_val * 2 + 1 :=
      ⟨(a * 2 + b + j * 3 + 4) / 2, by omega⟩
    by_cases huodd : u_val % 2 = 1
    · obtain ⟨out, hout, hstep⟩ :=
        single_mid_descent_closed hl hj (by omega) (by omega) eu hw hr (Or.inl huodd) hcap
      exact Or.inl ⟨out, Or.inl hout, hstep⟩
    · by_cases hsat : 2 ^ (3 + k) ≤ u_val + (b + j) * 2
      · obtain ⟨out, hout, hstep⟩ :=
          single_mid_descent_closed hl hj (by omega) (by omega) eu hw hr (Or.inr hsat) hcap
        exact Or.inl ⟨out, Or.inl hout, hstep⟩
      · have hp : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
        have hj' : j < a := by
          clear hmod hw hr hl hcap
          omega
        by_cases hlate : 2 ^ (3 + k) ≤ u_val + (b + j) * 2 + 4
        · have h_lin_cases : u_val + (b + j) * 2 + 2 = (a * 2 + b + 1) * 2 ∨
              u_val + (b + j) * 2 + 4 = (a * 2 + b + 1) * 2 := by
            clear hmod hw hr hl hcap
            omega
          have ecase : b = a ∧ j * 7 + 4 = a * 5 := by
            clear huodd hsat hlate heven hsize hp hp4 hw hr hl hcap
            omega
          rcases ecase with ⟨eb_eq, ej⟩
          subst b
          have hl' : Level (2 + (1 + k)) a a fs := by
            have : 2 + (1 + k) = 3 + k := by omega
            rwa [this]
          have hw' : Word (2 + (1 + k)) (a * 3 + 1 - j) xs := by
            have h1 : 2 + (1 + k) = 3 + k := by omega
            have h2 : a * 3 + 1 - j = a * 2 + a + 1 - j := by omega
            rwa [h1, h2]
          obtain ⟨out, hout, hstep⟩ := first_Q_x_closed hl' ej hw' hr
          exact Or.inl ⟨out, Or.inl hout, hstep⟩
        · have h_lin1 : a * 2 + b + 1 - j + (j * 2 + 2) * 2 < 2 ^ (1 + (3 + k)) := by
            have : 2 ^ (1 + (3 + k)) = 2 ^ (2 + k) * 4 := by ring
            omega
          obtain ⟨bs, hbs, hp_step⟩ := P_word_linear (j * 2 + 2) r hw (by omega) h_lin1
          rw [eu] at hbs
          have hbs' : Word ((2 + k) + 1) (u_val * 2 + 1) bs := by
            have : (2 + k) + 1 = 3 + k := by omega
            rwa [this]
          obtain ⟨cs, hcs, rfl⟩ := Word_odd_inv hbs'
          have h_lin2 : u_val + (b + j) * 2 < 2 ^ (1 + (2 + k)) := by
            have : 1 + (2 + k) = 3 + k := by omega
            rw [this]
            omega
          obtain ⟨ds, hds, hmid⟩ := P_word_linear (b + j) r hcs (by omega) h_lin2
          have h_upper : u_val + (b + j) * 2 + 4 < 2 ^ (1 + (2 + k)) := by
            have : 1 + (2 + k) = 3 + k := by omega
            rw [this]
            omega
          obtain ⟨out, hout, hstep⟩ :=
            split_O_word_closed (h := 3 + k) (k := 2 + k) (x := u_val + (b + j) * 2) (q := 0)
              hl hj' (by omega) (by omega) (by omega) (by omega) h_upper
              (fun _ => ⟨by omega, by omega⟩) hds hr (by omega)
              (.InnerP (by simpa only [List.append_assoc, append_assoc] using hp_step))
              (P_G hmid)
          exact Or.inl ⟨out, Or.inr hout, hstep⟩

theorem z_middle_bounds {a b j n u_val v c : ℕ}
    (ha : 5 ≤ a) (hab : a ≤ b) (hba : b ≤ a + 1) (hj : j ≤ a)
    (hn : n * 2 = (a * 2 + b + 1) * 2 + (a - j))
    (hu : 0 < u_val) (hub : u_val < a * 2 + b + 1)
    (ev : v = u_val + (b + j) * 2) (hv : v < a * 2 + b + 1) (hevenv : v % 2 = 0)
    (e : u_val * 2 + 1 + c * ((a * 2 + b) * 2) = phi n + (j * 2 + 2) * 2)
    (hguard : n % 2 = 1 ∨ (a * 2 + b + 1) * 2 ≤ n + j * 4)
    (hmod : (a * 2 + b + 1) % 15 = 1 ∨ (a * 2 + b + 1) % 15 = 2 ∨
      (a * 2 + b + 1) % 15 = 4 ∨ (a * 2 + b + 1) % 15 = 8) :
    j < a ∧ a * 2 + b + 1 < (v + 4) * 2 ∧ v + 4 < a * 2 + b + 1 ∧
      (v + 4) * 4 ≠ (a * 2 + b + 1) * 3 := by
  have hphi : phi n ≤ n := by unfold phi; omega
  have hc : c ≤ 1 := by
    rcases c with _ | _ | c'
    · omega
    · omega
    · have : 2 * ((a * 2 + b) * 2) ≤ (c' + 1 + 1) * ((a * 2 + b) * 2) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
  have hce : n % 2 = 0 → c = 1 := by
    intro heven
    rcases c with _ | c'
    · unfold phi at e
      omega
    · omega
  have hj' : j < a := by omega
  have hlower : a * 2 + b + 1 < (v + 4) * 2 := by omega
  have hphi_cases : (n % 2 = 1 ∧ phi n = n) ∨ (n % 2 = 0 ∧ phi n = n - 1) := by
    unfold phi; omega
  refine ⟨hj', hlower, ?_, ?_⟩
  · rcases c with _ | _ | c'
    · rcases hphi_cases with ⟨hno, hpe⟩ | ⟨hne, hpe⟩ <;> [rw [hpe] at e; (have := hce hne; omega)]
      omega
    · rcases hphi_cases with ⟨hno, hpe⟩ | ⟨hne, hpe⟩ <;> rw [hpe] at e <;> omega
    · omega
  · rcases c with _ | _ | c'
    · rcases hphi_cases with ⟨hno, hpe⟩ | ⟨hne, hpe⟩ <;> [rw [hpe] at e; (have := hce hne; omega)]
      clear hmod hguard hphi hce
      omega
    · rcases hphi_cases with ⟨hno, hpe⟩ | ⟨hne, hpe⟩ <;> rw [hpe] at e <;>
        (clear hmod hguard hphi hce; omega)
    · omega

theorem single_z_guard_closed {k a b j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hn : n * 2 = (a * 2 + b + 1) * 2 + (a - j))
    (hw : Word (2 + k) n xs) (hr : Num 0 r)
    (hguard : n % 2 = 1 ∨ 2 ^ (3 + k) ≤ n + j * 4) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have hnpos : 0 < n := by omega
  have hcap : phi n + (2 ^ (2 + k) - 1) * 0 ≤ (a * 2 + b + 1) * 4 := by
    have := phi_bounds hnpos
    omega
  have hguard1 : n % 2 = 1 ∨ 2 ^ (1 + (2 + k)) ≤ n + j * 4 := by
    have : 1 + (2 + k) = 3 + k := by omega
    rwa [this]
  obtain ⟨u_val, c₀, hu, hub, h0⟩ :=
    counter_inner_total (2 + k) j n (by omega) (Word_bound hw) hguard1
  have hub' : u_val < 2 ^ (1 + (1 + k)) := by
    have : 1 + (1 + k) = 2 + k := by omega
    rwa [this]
  obtain ⟨v, c₁, h1, hvb⟩ := CounterRun_total
    (fun z' hz' => GCounter_total (1 + k) z' (by omega) hz') (b + j) u_val hub'
  by_cases hodd : v % 2 = 1
  · have hready : ∀ u' v' c₀' c₁',
        CounterRun (GCounter (2 + k)) (j * 2 + 2) n (u' * 2 + 1) c₀' →
        CounterRun (GCounter (1 + k)) (b + j) u' v' c₁' → v' % 2 = 1 := by
      intro u' v' c₀' c₁' h0' h1'
      obtain ⟨eu, _⟩ := GCounterRun_unique h0 h0'
      have hu_eq : u' = u_val := by omega
      subst hu_eq
      obtain ⟨rfl, _⟩ := GCounterRun_unique h1 h1'
      exact hodd
    obtain ⟨out, hout, hstep⟩ :=
      single_low_descent_closed hl hj hnpos hw hr hguard hready hcap
    exact ⟨out, Or.inl hout, hstep⟩
  · obtain ⟨rfl, ev, huo⟩ := GCounterRun_even h1 (by omega)
    have e := GCounterRun_balance h0 (by omega) hnpos
    rw [phi_odd] at e
    have hmod := pow2_mod15 (2 + k)
    rw [← hsize] at hmod
    have h_sub : 2 ^ (2 + k) - 1 = a * 2 + b := by omega
    have e' : u_val * 2 + 1 + c₀ * ((a * 2 + b) * 2) = phi n + (j * 2 + 2) * 2 := by
      rw [h_sub] at e
      exact e
    have hguard' : n % 2 = 1 ∨ (a * 2 + b + 1) * 2 ≤ n + j * 4 := by
      have : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
      omega
    have hvb' : v < a * 2 + b + 1 := by
      have : 1 + (1 + k) = 2 + k := by omega
      rw [this, ← hsize] at hvb
      exact hvb
    obtain ⟨hj', hlower, hupper, hend⟩ :=
      z_middle_bounds ha hab hba hj hn hu (by omega) ev hvb' (by omega) e' hguard' hmod
    obtain ⟨s, hs, htail⟩ := G_nums c₀ hr
    obtain ⟨bs, hbs, hin⟩ := counter_inner hw (by omega) hguard1 h0 htail
    have hbs' : Word ((1 + k) + 1) (u_val * 2 + 1) bs := by
      have : (1 + k) + 1 = 2 + k := by omega
      rwa [this]
    obtain ⟨cs, hcs, rfl⟩ := Word_odd_inv hbs'
    obtain ⟨ds, hds, hmid⟩ := G_counter_run hcs (by omega) h1 (.G0 s)
    have h_low_pow : 2 ^ (1 + k) < v + 4 := by
      have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
      omega
    have h_up_pow : v + 4 < 2 ^ (1 + (1 + k)) := by
      have : 1 + (1 + k) = 2 + k := by omega
      rw [this, ← hsize]
      exact hupper
    have h_end_imp : (v + 4) * 2 = 2 ^ (1 + k) * 3 → (1 + k) + 1 = 3 + k ∧ 0 + c₀ * 2 ≤ 1 := by
      intro heq
      exfalso
      have : 2 ^ (2 + k) = 2 ^ (1 + k) * 2 := by ring
      omega
    have h_cap_word : (v + 4) * 2 + (2 ^ (1 + (1 + k)) - 1) * (0 + c₀ * 2) ≤
        (a * 2 + b + 1) * 4 + b * 4 + j * 8 + 11 := by
      have : 1 + (1 + k) = 2 + k := by omega
      rw [this, h_sub]
      have hphi : phi n ≤ n := by unfold phi; omega
      clear hmod hguard hguard1 hguard' hcap hw hr h0 h1 htail hin hmid hbs hbs' hcs hds hs
      rcases c₀ with _ | _ | c₀'
      · omega
      · omega
      · have : 2 * ((a * 2 + b) * 2) ≤ (c₀' + 1 + 1) * ((a * 2 + b) * 2) :=
          Nat.mul_le_mul_right _ (by omega)
        omega
    obtain ⟨out, hout, hstep⟩ :=
      split_O_word_closed (h := 3 + k) (k := 1 + k) (x := v) (q := 0 + c₀ * 2)
        hl hj' (by omega) (by omega) (by omega) h_low_pow h_up_pow h_end_imp
        hds hs h_cap_word
        (by simpa only [List.append_assoc, append_assoc] using hin) hmid
    exact ⟨out, Or.inr hout, hstep⟩

theorem single_z_closed {k a b j : ℕ} {fs : List Sym} {n : ℕ} {xs : List Sym} {r : ListBlank Sym}
    (hl : Level (3 + k) a b fs) (hj : j ≤ a)
    (hn : n * 2 = (a * 2 + b + 1) * 2 + (a - j))
    (hw : Word (2 + k) n xs) (hr : Num 0 r) :
    ∃ out, Normal out ∧ (cfg (fs +> (w ^ j +> (xs +> r)))) [tm1]⊢⁺ out := by
  obtain ⟨hh, ha, hab, hba⟩ := Level_bounds hl
  have hsize : a * 2 + b + 1 = 2 ^ (2 + k) := by
    have : 3 + k - 1 = 2 + k := by omega
    rw [← this, hl.level_size]
  have hp4 : 2 ^ (2 + k) = 2 ^ k * 4 := by ring
  by_cases hodd : n % 2 = 1
  · exact single_z_guard_closed hl hj hn hw hr (Or.inl hodd)
  · by_cases hguard : 2 ^ (3 + k) ≤ n + j * 4
    · exact single_z_guard_closed hl hj hn hw hr (Or.inr hguard)
    · by_cases hend : 2 ^ (3 + k) ≤ n + j * 4 + 4
      · have hmod := pow2_mod7 (2 + k)
        rw [← hsize] at hmod
        have hp : 2 ^ (3 + k) = 2 ^ (2 + k) * 2 := by ring
        have h_lin_cases : n + j * 4 + 2 = (a * 2 + b + 1) * 2 ∨
            n + j * 4 + 4 = (a * 2 + b + 1) * 2 := by
          clear hmod hw hr hl
          omega
        have ecase : b = a + 1 ∧ j * 7 = a * 5 := by
          clear hodd hguard hend hsize hp hp4 hw hr hl
          omega
        rcases ecase with ⟨eb_eq, ej⟩
        subst b
        obtain ⟨out, hout, hstep⟩ := late_first_Q_z_closed hl ej (by omega) hw hr
        exact ⟨out, Or.inl hout, hstep⟩
      · have hp : 2 ^ (1 + (2 + k)) = 2 ^ (3 + k) := by
          have : 1 + (2 + k) = 3 + k := by omega
          rw [this]
        have hpn := phi_bounds (by omega : 0 < n)
        exact single_even_split_closed (h := 3 + k) (k := 2 + k) (n := n) (q := 0)
          hl hj (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega) hw hr (by omega)

theorem root_progress_single {c : Cfg Sym Q} (h : ∃ out, SRoot out ∧ (c [tm1]⊢⁺ out)) :
    RootProgress c := by
  obtain ⟨out, hout, hstep⟩ := h
  exact Or.inl ⟨out, Or.inl hout, hstep⟩

theorem single_root_progress {c : Cfg Sym Q} (hs_root : SRoot c) : RootProgress c := by
  rcases hs_root with ⟨h, a, b, j, fs, r, hl, hj, hs⟩
  have hh := hl.level_height
  rcases h with _ | _ | _ | k
  · omega
  · omega
  · omega
  · have hl' : Level (3 + k) a b fs := by
      have : 3 + k = k + 3 := by omega
      rwa [this]
    cases hs with
    | SNum n r hr hbound =>
      exact root_progress_single (pure_closed hl' hj hr hbound)
    | SWord K n q xs r hK hn hw hr hp hcap =>
      cases hp with
      | SN K n q hK3 hwidth hguard =>
        exact root_progress_single (narrow_closed hl' hj hK3 (by omega) hn hw hr hguard hcap)
      | S2 n q hphase =>
        have h_22 : 2 ^ 2 - 1 = 3 := rfl
        rw [h_22] at hcap
        exact root_progress_single (two_closed hl' hj hn hw hr hphase hcap)
      | S1 n q hpos =>
        have h_21 : 2 ^ 1 - 1 = 1 := rfl
        rw [h_21, Nat.one_mul] at hcap
        rcases hpos with rfl | ⟨hnear, rfl, hq⟩
        · exact root_progress_single (one_boundary_closed hl' hn hw hr hcap)
        · exact root_progress_single (one_neighbor_closed hl' hnear hw hr hq)
      | SX K q hcases =>
        rcases hcases with ⟨eK, hq⟩ | ⟨rfl, rfl⟩ | ⟨rfl, ej, eb, rfl⟩
        · have eK' : K = 2 + k := by omega
          subst eK'
          exact Or.inl (single_x_low_closed hl' hj hw hr hq hcap)
        · have hw' : Word (3 + k) (a * 2 + b + 1 - j) xs := by
            have : 3 + k = k + 3 := by omega
            rwa [this]
          exact single_x_mid_closed hl' hj hw' hr
        · subst b j
          have hw' : Word (4 + k) (a * 2 + 1) xs := by
            have h1 : 4 + k = k + 3 + 1 := by omega
            have h2 : a * 2 + 1 = a * 2 + a + 1 - a := by omega
            rwa [h1, h2]
          exact root_progress_single (single_x_top_closed hl' hw' hr)
      | SY K q hmin hmax hinside =>
        exact Or.inl (single_y_closed hl' hj (by omega) (by omega) (by omega) hw hr hcap)
      | SZ n hn_eq =>
        have hw' : Word (2 + k) n xs := by
          have : 2 + k = k + 3 - 1 := by omega
          rwa [this]
        exact Or.inl (single_z_closed hl' hj hn_eq hw' hr)

theorem normal_nonhalt {c : Cfg Sym Q} (hc : Normal c) : NonHaltFrom tm1 c := by
  refine nonHaltFrom_of_progress (Inv := fun x => Normal x ∨ NonHaltFrom tm1 x) ?_ (Or.inl hc)
  intro x hx
  have hp : RootProgress x := by
    rcases hx with (hs | hd) | hnh
    · exact single_root_progress hs
    · exact Or.inl (double_progress hd)
    · exact Or.inr hnh
  rcases hp with ⟨y, hy, hstep⟩ | hnh
  · exact ⟨y, hstep, Or.inl hy⟩
  · have hsome := hnh x ⟨0, rfl⟩
    rcases hst : step tm1 x with _ | y
    · rw [hst] at hsome; cases hsome
    · refine ⟨y, ⟨1, by decide, hst⟩, Or.inr (fun z ⟨m, hm⟩ => ?_)⟩
      refine hnh z ⟨1 + m, ?_⟩
      rw [BusyBeaver.multiStep_add, show multiStep tm1 x 1 = step tm1 x from rfl, hst, Option.bind_some]
      exact hm

theorem initial_level : Level 5 5 5 (prefix_word 3) :=
  ⟨frame_spec 3, by decide, rfl⟩

theorem initial_root : SRoot (cfg (prefix_word 3 +> (t ^ 4 +> default))) := by
  have h_eq : prefix_word 3 +> (t ^ 4 +> (default : ListBlank Sym)) =
      prefix_word 3 +> (w ^ 0 +> (t +> (t +> (t +> (t +> default))))) := rfl
  rw [h_eq]
  refine .sroot 5 5 5 0 (prefix_word 3) _ initial_level (by decide)
    (.SNum 15 _ (.Num10 7 (.Num10 3 (.Num10 1 (.Num10 0 .Num0)))) (by decide))

theorem initial2_root :
    SRoot (cfg (prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> default)))) := by
  have h_eq : prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> (default : ListBlank Sym))) =
      prefix_word 3 +> (w ^ 0 +> (word 3 11 +> ([0, 0] +> (t +> default)))) := rfl
  rw [h_eq]
  exact .sroot 5 5 5 0 (prefix_word 3) _ initial_level (by decide)
    (.SWord 3 11 2 (word 3 11) _ (by decide) (by decide)
      (word_spec 3 11 (by decide)) (.Num00 1 (.Num10 0 .Num0))
      (.SN 3 11 2 (by decide) (by decide) (Or.inl rfl)) (by decide))

theorem initial3_root :
    SRoot (cfg (prefix_word 3 +> (word 2 5 +> ([0, 0, 1, 0, 1, 0] +> default)))) := by
  have h_eq : prefix_word 3 +> (word 2 5 +> ([0, 0, 1, 0, 1, 0] +> (default : ListBlank Sym))) =
      prefix_word 3 +> (w ^ 0 +> (word 2 5 +> ([0, 0] +> (t +> (t +> default))))) := rfl
  rw [h_eq]
  exact .sroot 5 5 5 0 (prefix_word 3) _ initial_level (by decide)
    (.SWord 2 5 6 (word 2 5) _ (by decide) (by decide)
      (word_spec 2 5 (by decide)) (.Num00 3 (.Num10 1 (.Num10 0 .Num0)))
      (.S2 5 6 (Or.inl rfl)) (by decide))



/-- `BLECv4.v:TM2` (`flipTM` of Holdout #87): `1LB0RC_1RA0LE_0LD1RF_1RC1RB_0RD0LB_0RA---` -/
def tm87_flip : Machine Sym Q
  | 0, 0 => some (some 1, Stmt.write 1 Dir.left)
  | 0, 1 => some (some 2, Stmt.write 0 Dir.right)
  | 1, 0 => some (some 0, Stmt.write 1 Dir.right)
  | 1, 1 => some (some 4, Stmt.write 0 Dir.left)
  | 2, 0 => some (some 3, Stmt.write 0 Dir.left)
  | 2, 1 => some (some 5, Stmt.write 1 Dir.right)
  | 3, 0 => some (some 2, Stmt.write 1 Dir.right)
  | 3, 1 => some (some 1, Stmt.write 1 Dir.right)
  | 4, 0 => some (some 3, Stmt.write 0 Dir.right)
  | 4, 1 => some (some 1, Stmt.write 0 Dir.left)
  | 5, 0 => some (some 0, Stmt.write 0 Dir.right)
  | 5, 1 => none

lemma init_87_flip_raw :
    (init ([] : List Sym)) [tm87_flip]⊢*
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ := by
  rw [← toCfg_zero (K := 6)]
  exact ⟨4293, stepsNat_sound tm87_flip 4293 ⟨0, 0, 0, 0⟩ ⟨4, 0, 0, 19288074671834⟩
    (by decide +kernel) (by decide)⟩

def rename87 : Q → Q
  | 0 => 1 | 1 => 0 | 2 => 4 | 3 => 3 | 4 => 2 | 5 => 5

def mapCfg (f : Q → Q) (c : Cfg Sym Q) : Cfg Sym Q :=
  ⟨c.q.map f, c.tape⟩

lemma step_rename87 (c : Cfg Sym Q) :
    step tm87_flip (mapCfg rename87 c) = (step tm1 c).map (mapCfg rename87) := by
  rcases c with ⟨_ | ⟨_ | _ | _ | _ | _ | _ | q, hq⟩, ⟨⟨_ | _ | h, hh⟩, l, r⟩⟩ <;>
    (try rfl) <;>
    omega

lemma multiStep_rename87 (c : Cfg Sym Q) (n : Nat) :
    multiStep tm87_flip (mapCfg rename87 c) n = (multiStep tm1 c n).map (mapCfg rename87) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    rw [BusyBeaver.multiStep_succ, BusyBeaver.multiStep_succ, ih]
    rcases multiStep tm1 c n with _ | c'
    · rfl
    · exact step_rename87 c'

lemma nonHaltFrom_of_stepStar {M : Machine Sym Q} {c₁ c₂ : Cfg Sym Q}
    (h₁ : c₁ [M]⊢* c₂) (h₂ : NonHaltFrom M c₂) : NonHaltFrom M c₁ := by
  obtain ⟨k₀, hk₀⟩ := h₁
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
    exact h₂ cfg ⟨k - k₀, hk⟩

lemma nonHaltFrom_rename87 {c : Cfg Sym Q} (h : NonHaltFrom tm1 c) :
    NonHaltFrom tm87_flip (mapCfg rename87 c) := by
  intro c' ⟨n, hn⟩
  rw [multiStep_rename87, Option.map_eq_some_iff] at hn
  rcases hn with ⟨d, hd, rfl⟩
  rw [step_rename87, Option.isSome_map]
  exact h d ⟨n, hd⟩

lemma target_tm_eq_flipTM : target_tm = flipTM tm87_flip := by
  funext ⟨q, hq⟩ ⟨a, ha⟩
  rcases q with _ | _ | _ | _ | _ | _ | q <;> rcases a with _ | _ | a <;> (try rfl) <;> omega

lemma isNotHalt_flipTM {M : Machine Sym Q} (h : IsNotHalt M) :
    IsNotHalt (flipTM M) := by
  intro c ⟨n, hn⟩
  have h_init : (init ([] : List Sym) : Cfg Sym Q) = flipCfg (init ([] : List Sym) : Cfg Sym Q) := rfl
  rw [h_init, multiStep_flipTM, Option.map_eq_some_iff] at hn
  rcases hn with ⟨d, hd, rfl⟩
  rw [step_flipTM, Option.isSome_map]
  exact h d ⟨n, hd⟩

lemma toCfg_87_eq :
    NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ =
    mapCfg rename87 (cfg (prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> default)))) := by
  have h1 : NatCfg.toCfg (K := 6) ⟨4, 0, 0, 19288074671834⟩ =
      Cfg.headRight E (decodeHalf 0) (decodeHalf (2 * 19288074671834)) :=
    toCfg_headRight (K := 6) E 0 (2 * 19288074671834)
  have h2 : decodeHalf (2 * 19288074671834) =
      ([0, 0, 1, 0] ++ prefix_word 3 ++ word 3 11 ++ [0, 0, 1, 0]) +> (default : ListBlank Sym) := by
    rw [← decodeHalf_zero, decodeHalf_encodeList]
    congr 1
  rw [h1, h2, decodeHalf_zero]
  simp only [cfg, mapCfg, rename87, Option.map_some, Cfg.headRight, append_assoc]

-- END EXPLORATORY DEFINITIONS AND LEMMAS

-- BEGIN GOAL STATEMENT (DO NOT MODIFY SIGNATURE)

theorem is_does_not_halt : IsNotHalt target_tm := by
  rw [target_tm_eq_flipTM]
  apply isNotHalt_flipTM
  have h_reach : (init ([] : List Sym)) [tm87_flip]⊢*
      mapCfg rename87 (cfg (prefix_word 3 +> (word 3 11 +> ([0, 0, 1, 0] +> default)))) := by
    rw [← toCfg_87_eq]
    exact init_87_flip_raw
  exact nonHaltFrom_of_stepStar h_reach (nonHaltFrom_rename87 (normal_nonhalt (Or.inl initial2_root)))

end BusyBeaver.M_1RB0LC_1LA0RE_0RD1LF_1LC1LB_0LD0RB_0LAHHH
