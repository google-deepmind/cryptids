/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Riemann120

/-!
# Tape Gadgets & Lockstep Call-Stack Dispatcher for `riemann120` and `riemann104`

Unified symbolic tape-gadget engine on `common121`, 5-register abstract machine
`ConjectureMachines.Riemann120.Layer2`, and lockstep simulation theorems
`halts_tm_iff_rhRegHaltsOf (isEd : Bool)` and `halts_riemann121_iff_rhRegHalts`.
-/

@[expose] public section

set_option linter.style.setOption false
set_option linter.style.maxHeartbeats false
set_option linter.flexible false

namespace ConjectureMachines.Riemann120.Backend

open Turing (Dir)
open StateTransition ConjectureMachines
open ConjectureMachines.Riemann120
open ConjectureMachines.Semantics.Riemann.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_reaches nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps
   mk_append_replicate_zero default_eq_mk_nil
   default_cons_zero append_replicate_zero_default fin2_cases
   Tape.mkL Tape.mkL_cons Tape.mk'_cons Tape.mkL_default
   append_replicate_cons append_cons_snoc append_reverse_cons
   encodeReg encodeReg_length encodeReg_reverse append_encodeReg_reverse append_encodeReg
   encodeRegs encodeRegs_nil encodeRegs_cons encodeRegs_append
   regsTape regsTape_nil regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)
open ConjectureMachines.Semantics.Zf.Layer1
  (rootLeft rootLeft_eq_append stackLeft stackLeft_nil stackLeft_eq_append
   stackLeft_append stackLeft_append_singleton)
open ConjectureMachines.Semantics.Zf.Boot
  (pair01 pair10 pair01_snoc pair10_snoc cons_one_pair01 pair10_succ_eq
   bootLeft bootLeft_zero)

set_option maxRecDepth 200000

/-!
## 3. Symbolic Step Helpers & `NoFourZeros` Scanner (`4.run.0..3`, `6.continue.0..2`)
-/

theorem step_mkL_left {q q' : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step common121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, commonTrans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right {q q' : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step common121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, commonTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_right {q q' : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step common121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, commonTrans_eq, h, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left {q q' : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step common121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, commonTrans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem nSteps_mkL_left_scan {q : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan {q : Fin 121} {a b : Fin 2}
    (h : commonTrans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]

/-- `NoFourZeros bits`: `true` iff no 4 consecutive `0`s (`[0, 0, 0, 0]`) occur in `bits`. -/
def NoFourZeros : List (Fin 2) → Bool
  | 0 :: 0 :: 0 :: 0 :: _ => false
  | _ :: xs => NoFourZeros xs
  | [] => true

theorem NoFourZeros_head4 (a b c d : Fin 2) (xs : List (Fin 2)) :
    NoFourZeros (a :: b :: c :: d :: xs) =
      (NoFourZeros [a, b, c, d] && NoFourZeros (b :: c :: d :: xs)) := by
  rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
    rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

theorem NoFourZeros_snoc_one : ∀ l : List (Fin 2), NoFourZeros (l ++ [1]) = NoFourZeros l
  | [] => rfl
  | [a] => by revert a; decide
  | [a, b] => by revert a b; decide
  | [a, b, c] => by revert a b c; decide
  | a :: b :: c :: d :: xs => by
    have ih := NoFourZeros_snoc_one (b :: c :: d :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 a b c d (xs ++ [1]), NoFourZeros_head4 a b c d xs, ih]

theorem NoFourZeros_snoc_one_bit (b₀ : Fin 2) :
    ∀ l : List (Fin 2), NoFourZeros (l ++ [1, b₀]) = NoFourZeros l
  | [] => by revert b₀; decide
  | [a] => by revert a b₀; decide
  | [a, b] => by revert a b b₀; decide
  | [a, b, c] => by revert a b c b₀; decide
  | a :: b :: c :: d :: xs => by
    have ih := NoFourZeros_snoc_one_bit b₀ (b :: c :: d :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 a b c d (xs ++ [1, b₀]), NoFourZeros_head4 a b c d xs, ih]

theorem NoFourZeros_append_replicate_one (l : List (Fin 2)) (p : ℕ) :
    NoFourZeros (l ++ List.replicate p 1) = NoFourZeros l := by
  induction p generalizing l with
  | zero => simp
  | succ p ih =>
    rw [List.replicate_succ', ← List.append_assoc, NoFourZeros_snoc_one, ih]

theorem NoFourZeros_snoc_of_head4 (a b c d : Fin 2) :
    ∀ xs : List (Fin 2),
      NoFourZeros (xs ++ [d, c, b, a]) =
        (NoFourZeros [a, b, c, d] && NoFourZeros (xs ++ [d, c, b]))
  | [] => by revert a b c d; decide
  | [x₁] => by revert a b c d x₁; decide
  | [x₁, x₂] => by revert a b c d x₁ x₂; decide
  | [x₁, x₂, x₃] => by revert a b c d x₁ x₂ x₃; decide
  | x₁ :: x₂ :: x₃ :: x₄ :: xs => by
    have ih := NoFourZeros_snoc_of_head4 a b c d (x₂ :: x₃ :: x₄ :: xs)
    simp only [List.cons_append] at ih ⊢
    rw [NoFourZeros_head4 x₁ x₂ x₃ x₄ (xs ++ [d, c, b, a]),
      NoFourZeros_head4 x₁ x₂ x₃ x₄ (xs ++ [d, c, b]), ih]
    rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;>
      rcases fin2_cases x₃ with rfl | rfl <;> rcases fin2_cases x₄ with rfl | rfl <;>
      rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
      rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

theorem NoFourZeros_reverse : ∀ bits : List (Fin 2), NoFourZeros bits.reverse = NoFourZeros bits
  | [] => rfl
  | [a] => by revert a; decide
  | [a, b] => by revert a b; decide
  | [a, b, c] => by revert a b c; decide
  | a :: b :: c :: d :: xs => by
    have hrev : (a :: b :: c :: d :: xs).reverse = xs.reverse ++ [d, c, b, a] := by
      simp [List.reverse_cons, List.append_assoc]
    rw [hrev, NoFourZeros_snoc_of_head4]
    have ih := NoFourZeros_reverse (b :: c :: d :: xs)
    have hrev3 : (b :: c :: d :: xs).reverse = xs.reverse ++ [d, c, b] := by
      simp [List.reverse_cons, List.append_assoc]
    rw [← hrev3, ih, NoFourZeros_head4]
    rcases fin2_cases a with rfl | rfl <;> rcases fin2_cases b with rfl | rfl <;>
      rcases fin2_cases c with rfl | rfl <;> rcases fin2_cases d with rfl | rfl <;> rfl

/-- `4.run.0..3` scanner states (`0 ↦ 12`, `1 ↦ 14`, `2 ↦ 16`, `3 ↦ 18`). -/
def rhRunState : ℕ → Fin 121
  | 0 => 12
  | 1 => 14
  | 2 => 16
  | 3 => 18
  | _ => 12

/-- Scanning left across `rev` from `rhRunState z` (`z ≤ 3`) when `NoFourZeros` holds. -/
theorem rhRun_scan_rev (rev : List (Fin 2)) (z : ℕ) (hz : z ≤ 3)
    (hok : NoFourZeros (List.replicate z 0 ++ rev) = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 3 ∧
      nSteps common121 rev.length
        ⟨rhRunState z, Tape.mkL (ListBlank.append rev default) R⟩ =
      some ⟨rhRunState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing z R with
  | nil =>
    exact ⟨z, hz, rfl⟩
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · match z, hz with
      | 0, _ =>
        have hstep : step common121 ⟨12, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨14, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 1 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 1, _ =>
        have hstep : step common121 ⟨14, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨16, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 2 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 2, _ =>
        have hstep : step common121 ⟨16, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
            some ⟨18, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
          step_mkL_left (by rfl) _ _
        obtain ⟨z', hz', hrest⟩ := ih 3 (by decide) hok (R.cons 0)
        rw [append_cons_snoc, ← List.reverse_cons] at hrest
        exact ⟨z', hz', step_nSteps hstep hrest⟩
      | 3, _ =>
        cases hok
    · have htr1_all : ∀ z₀, z₀ ≤ 3 → commonTrans (rhRunState z₀) 1 = some (1, .left, 12) := by
        decide
      have hstep : step common121
          ⟨rhRunState z, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
          some ⟨12, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left (htr1_all z hz) _ _
      have hok' : NoFourZeros (List.replicate 0 0 ++ xs) = true := by
        match z, hz with
        | 0, _ => exact hok
        | 1, _ => exact hok
        | 2, _ => exact hok
        | 3, _ => exact hok
      obtain ⟨z', hz', hrest⟩ := ih 0 (by decide) hok' (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', step_nSteps hstep hrest⟩

/-- Bouncing off `default` from `rhRunState z` (`z ≤ 3`) into `4.dispatch.scan` (`State 20`). -/
theorem rhRun_bounce_default (z : ℕ) (hz : z ≤ 3) (R : ListBlank (Fin 2)) :
    nSteps common121 (2 * (3 - z) + 1) ⟨rhRunState z, Tape.mkL default R⟩ =
      some ⟨20, Tape.mk' default R⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have hb3 : ∀ R' : ListBlank (Fin 2),
      nSteps common121 1 ⟨18, Tape.mkL default R'⟩ = some ⟨20, Tape.mk' default R'⟩ := by
    intro R'
    apply step_one
    conv_lhs => rw [hdef]
    rw [step_mkL_right (by rfl), default_cons_zero]
  match z, hz with
  | 3, _ => exact hb3 R
  | 2, _ =>
    have h1 : step common121 ⟨16, Tape.mkL default R⟩ =
        some ⟨18, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 := hb3 (R.cons 0)
    have h3 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 1 default R
    rw [append_replicate_zero_default] at h3
    exact step_nSteps h1 (nSteps_bind_eq (m := 1) (n := 1) h2 h3)
  | 1, _ =>
    have h1 : step common121 ⟨14, Tape.mkL default R⟩ =
        some ⟨16, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 : step common121 ⟨16, Tape.mkL default (R.cons 0)⟩ =
        some ⟨18, Tape.mkL default ((R.cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h3 := hb3 ((R.cons 0).cons 0)
    have h4 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 2 default R
    rw [append_replicate_zero_default] at h4
    exact step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq h3 h4))
  | 0, _ =>
    have h1 : step common121 ⟨12, Tape.mkL default R⟩ =
        some ⟨14, Tape.mkL default (R.cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default R
    have h2 : step common121 ⟨14, Tape.mkL default (R.cons 0)⟩ =
        some ⟨16, Tape.mkL default ((R.cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h3 : step common121 ⟨16, Tape.mkL default ((R.cons 0).cons 0)⟩ =
        some ⟨18, Tape.mkL default (((R.cons 0).cons 0).cons 0)⟩ := by
      conv_lhs => rw [hdef]
      exact step_mkL_left (by rfl) default _
    have h4 := hb3 (((R.cons 0).cons 0).cons 0)
    have h5 := nSteps_mk'_right_scan (q := 20) (a := 0) (b := 0) (by rfl) 3 default R
    rw [append_replicate_zero_default] at h5
    exact step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq h4 h5)))

set_option maxHeartbeats 400000 in
-- Finite state-table decision procedure.
theorem common_sub_rh121 (q : Fin 121) (a : Fin 2) (t : Fin 2 × Dir × Fin 121) :
    commonTrans q a = some t → riemann121.transition q a = some t := by
  revert q a t; decide

theorem step_rh_of_common {c c' : Cfg 121 2}
    (hs : step common121 c = some c') : step riemann121 c = some c' := by
  obtain ⟨q, T⟩ := c
  dsimp only [step] at hs ⊢
  change (commonTrans q T.head).map _ = some c' at hs
  rcases htr : commonTrans q T.head with _ | t
  · rw [htr] at hs; cases hs
  · rw [common_sub_rh121 q T.head t htr]
    rw [htr] at hs; exact hs

theorem nSteps_rh_of_common {n : ℕ} {c c' : Cfg 121 2}
    (hn : nSteps common121 n c = some c') : nSteps riemann121 n c = some c' := by
  induction n generalizing c with
  | zero => exact hn
  | succ n ih =>
    rw [nSteps_succ, Option.bind_eq_some_iff] at hn ⊢
    obtain ⟨c₁, hs, hrest⟩ := hn
    exact ⟨c₁, step_rh_of_common hs, ih hrest⟩

theorem step_mk'_right_rh {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mk', Tape.write, Tape.move]

/-- From `4.dispatch.scan` (`State 20`) at `[1, 1, b]`, `riemann121` takes 3 steps
(`20 -> 22 -> 25 -> 27`) writing `0` over `b` to enter `main.0` (`State 27`). -/
theorem root_scan_to_main (b : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨20, Tape.mk' default (ListBlank.append [1, 1, b] R)⟩ =
      some ⟨27, Tape.mk' rootLeft R⟩ := by
  simp only [ListBlank.append]
  have h1 : step riemann121 ⟨20, Tape.mk' default (((R.cons b).cons 1).cons 1)⟩ =
      some ⟨22, Tape.mk' (ListBlank.cons 1 default) ((R.cons b).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h2 : step riemann121 ⟨22, Tape.mk' (ListBlank.cons 1 default) ((R.cons b).cons 1)⟩ =
      some ⟨25, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons b)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h3 : step riemann121 ⟨25, Tape.mk' ((ListBlank.cons 1 default).cons 1) (R.cons b)⟩ =
      some ⟨27, Tape.mk' rootLeft R⟩ := by
    rcases fin2_cases b with rfl | rfl
    · exact step_mk'_right_rh (by rfl) _ _
    · exact step_mk'_right_rh (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- From `12` (`4.run.0`), if `prefix = [1, 1, b] ++ rest` satisfies `NoFourZeros prefix = true`,
`common121` scans left to `default` and reaches `27` (`main.0`) with `rootLeft` on `Tape.left`
and `rest` on `Tape.right`. -/
theorem run0_reaches_main0 (b : Fin 2) (rest : List (Fin 2))
    (hok : NoFourZeros ([1, 1, b] ++ rest) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨12, Tape.mkL (ListBlank.append ([1, 1, b] ++ rest).reverse default) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append rest R)⟩ := by
  have hrev_ok : NoFourZeros ([1, 1, b] ++ rest).reverse = true := by
    rwa [NoFourZeros_reverse]
  obtain ⟨z', hz', hscan⟩ := rhRun_scan_rev ([1, 1, b] ++ rest).reverse 0 (by decide) hrev_ok R
  rw [List.reverse_reverse] at hscan
  have hbounce := rhRun_bounce_default z' hz' (ListBlank.append ([1, 1, b] ++ rest) R)
  rw [ListBlank.append_assoc] at hbounce
  have hroot := root_scan_to_main b (ListBlank.append rest R)
  exact ⟨_, by omega, nSteps_bind_eq (nSteps_rh_of_common hscan)
    (nSteps_bind_eq (nSteps_rh_of_common hbounce) hroot)⟩

/-- From `10` (`6.continue.0`), if `rev` contains `1` and satisfies `NoFourZeros rev = true`,
`common121` scans left into `12` (`4.run.0`) and reaches `default` in `rhRunState z'`. -/
theorem continue0_scan_rev (rev : List (Fin 2)) (hone : (1 : Fin 2) ∈ rev)
    (hok : NoFourZeros rev = true) (R : ListBlank (Fin 2)) :
    ∃ z', z' ≤ 3 ∧ ∃ s, 1 ≤ s ∧
      nSteps common121 s ⟨10, Tape.mkL (ListBlank.append rev default) R⟩ =
      some ⟨rhRunState z', Tape.mkL default (ListBlank.append rev.reverse R)⟩ := by
  induction rev generalizing R with
  | nil => cases hone
  | cons a xs ih =>
    rcases fin2_cases a with rfl | rfl
    · have hone' : (1 : Fin 2) ∈ xs := by
        rcases List.mem_cons.mp hone with h | h
        · cases h
        · exact h
      have hok' : NoFourZeros xs = true := by
        rcases xs with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, xs'⟩⟩⟩
        · rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;> rfl
        · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;>
            rcases fin2_cases x₃ with rfl | rfl <;> first | exact hok | cases hok
      have hstep : step common121 ⟨10, Tape.mkL ((ListBlank.append xs default).cons 0) R⟩ =
          some ⟨10, Tape.mkL (ListBlank.append xs default) (R.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨z', hz', s, hs1, hrest⟩ := ih hone' hok' (R.cons 0)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', s + 1, by omega, step_nSteps hstep hrest⟩
    · have hstep : step common121 ⟨10, Tape.mkL ((ListBlank.append xs default).cons 1) R⟩ =
          some ⟨12, Tape.mkL (ListBlank.append xs default) (R.cons 1)⟩ :=
        step_mkL_left (by rfl) _ _
      obtain ⟨z', hz', hrest⟩ := rhRun_scan_rev xs 0 (by decide) hok (R.cons 1)
      rw [append_cons_snoc, ← List.reverse_cons] at hrest
      exact ⟨z', hz', xs.length + 1, by omega, step_nSteps hstep hrest⟩

/-- From `10` (`6.continue.0`), if `prefix = [1, 1, b] ++ rest` satisfies `NoFourZeros prefix`,
`common121` scans left and enters `27` (`main.0`) with `rootLeft` on `Tape.left` and `rest` on
`Tape.right`. -/
theorem continue0_reaches_main0 (b : Fin 2) (rest : List (Fin 2))
    (hok : NoFourZeros ([1, 1, b] ++ rest) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨10, Tape.mkL (ListBlank.append ([1, 1, b] ++ rest).reverse default) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append rest R)⟩ := by
  have hone : (1 : Fin 2) ∈ ([1, 1, b] ++ rest).reverse := by
    rw [List.mem_reverse]
    simp
  have hrev_ok : NoFourZeros ([1, 1, b] ++ rest).reverse = true := by
    rwa [NoFourZeros_reverse]
  obtain ⟨z', hz', s₁, _, hscan⟩ :=
    continue0_scan_rev ([1, 1, b] ++ rest).reverse hone hrev_ok R
  rw [List.reverse_reverse] at hscan
  have hbounce := rhRun_bounce_default z' hz' (ListBlank.append ([1, 1, b] ++ rest) R)
  rw [ListBlank.append_assoc] at hbounce
  have hroot := root_scan_to_main b (ListBlank.append rest R)
  exact ⟨_, by omega, nSteps_bind_eq (nSteps_rh_of_common hscan)
    (nSteps_bind_eq (nSteps_rh_of_common hbounce) hroot)⟩

/-!
## 4. Canonical Tape Layouts (`rhRootCfg`, `rhPrepCfg`) & 5-Register Gadgets (`m, j, x, f, v`)
-/

/-- Canonical root configuration at `main.0` (`State 27`):
- Left of head: `rootLeft = (default.cons 1 |>.cons 1 |>.cons 0)`.
- Right of head: `stack`, then `padTotal - stack.length` zeros, `[1, 0]`, `encodeRegs regs`,
  and `extra` (which defaults to `default`). -/
def rhRootCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  ⟨27, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem rhRootCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    rhRootCfg padTotal stack regs default =
      ⟨27, Tape.mk' rootLeft
        (ListBlank.append stack
          (ListBlank.append (List.replicate (padTotal - stack.length) 0)
            (regsTape (0 :: regs))))⟩ := by
  unfold rhRootCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- Prepared configuration at `main.0` (`State 27`) after Pass 1 (`1b.reg.prep_1/2`):
`padTotal - stack.length` zeros + `[1, 0]` have been turned into `[1, 0]` followed by
`encodeReg (padTotal - stack.length - 2)` and `encodeRegs regs`. -/
def rhPrepCfg (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  ⟨27, Tape.mk' rootLeft
    (ListBlank.append
      (stack ++ [1, 0] ++ encodeRegs ((padTotal - stack.length - 2) :: regs))
      extra)⟩

theorem rhPrepCfg_default_eq (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ) :
    rhPrepCfg padTotal stack regs default =
      ⟨27, Tape.mk' rootLeft
        (ListBlank.append stack
          ((regsTape ((padTotal - stack.length - 2) :: regs)).cons 0 |>.cons 1))⟩ := by
  unfold rhPrepCfg
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

/-- `3.<reg_k>.inc` states for the 5 registers (`0=m, 1=j, 2=x, 3=f, 4=v`). -/
def regIncStage3 : ℕ → Fin 121
  | 0 => 4
  | 1 => 44
  | 2 => 99
  | 3 => 36
  | 4 => 70
  | _ => 4

/-- `3.<reg_k>.decnz` states for the 5 registers (`0=m, 1=j, 2=x, 3=f, 4=v`). -/
def regDecnzStage3 : ℕ → Fin 121
  | 0 => 31
  | 1 => 47
  | 2 => 71
  | 3 => 46
  | 4 => 73
  | _ => 31

/-- `2b.reg.<m-2>.inc` chain (`0 ↦ -2.inc = 11`, `1 ↦ -1.inc = 9`, `2..6 ↦ 0..4.inc`). -/
def rhRegIncrChain : ℕ → Fin 121
  | 0 => 11
  | 1 => 9
  | 2 => 7
  | 3 => 53
  | 4 => 52
  | 5 => 43
  | 6 => 85
  | _ => 11

/-- `2b.reg.<m-2>.dec` chain (`0 ↦ -2.dec = 51`, `1 ↦ -1.dec = 42`, `2..6 ↦ 0..4.dec`). -/
def rhRegDecrChain : ℕ → Fin 121
  | 0 => 51
  | 1 => 42
  | 2 => 35
  | 3 => 57
  | 4 => 69
  | 5 => 56
  | 6 => 87
  | _ => 51

/-- Return scan from `10` (`6.continue.0`) on `stackLeft w` when `NoFourZeros ([1, 1, 0] ++ w)`. -/
theorem continue0_return (w : List (Fin 2)) (hw : NoFourZeros ([1, 1, 0] ++ w) = true)
    (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨10, Tape.mkL (stackLeft w) R⟩ =
      some ⟨27, Tape.mk' rootLeft (ListBlank.append w R)⟩ := by
  rw [stackLeft_eq_append]
  exact continue0_reaches_main0 0 w hw R

/-- `6.continue.0` (`10`) scans left across `z` zeros in `z` steps. -/
theorem continue0_scan_zeros (z : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 z ⟨10, Tape.mkL (ListBlank.append (List.replicate z 0) L) R⟩ =
      some ⟨10, Tape.mkL L (ListBlank.append (List.replicate z 0) R)⟩ :=
  nSteps_mkL_left_scan (by rfl) z L R

/-- Pass 1 register prep scan (`1b.reg.prep_1/2` = `6/8`) from `State 6` to `State 10`. -/
theorem prep_pass1_to_10 (L : ListBlank (Fin 2)) (p : ℕ) (R : ListBlank (Fin 2)) :
    nSteps common121 (p + 2)
      ⟨6, Tape.mk' (L.cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨10, Tape.mkL
        (ListBlank.append (List.replicate p 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨6, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨8, Tape.mk' ((L.cons 1).cons 0)
        (ListBlank.append (List.replicate p 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan := nSteps_mk'_right_scan (q := 8) (a := 0) (b := 1) (by rfl) p
    ((L.cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h2 : step common121
      ⟨8, Tape.mk' (ListBlank.append (List.replicate p 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨10, Tape.mkL
        (ListBlank.append (List.replicate p 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left (by rfl) _ (R.cons 0)
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

theorem regIncStage3_trans_zero (k : ℕ) (hk : k < 5) :
    commonTrans (regIncStage3 k) 0 = some (1, .right, 6) := by
  revert k hk; decide

theorem regDecnzStage3_trans_zero (k : ℕ) (hk : k < 5) :
    commonTrans (regDecnzStage3 k) 0 = some (1, .right, 6) := by
  revert k hk; decide

/-!
## 5. Pass 2 Register Return Scans (`15/17` = `return_0`, `63/78` = `return_1`)
-/

theorem return0_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (r + 2)
      ⟨15, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨15, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨17, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step common121
      ⟨17, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨15, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem return0_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (encodeRegs regs).length
      ⟨15, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return0_scan_reg, ListBlank.append_assoc]

theorem return0_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 ((encodeRegs regs).length + 2)
      ⟨15, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨19, Tape.mkL L ((ListBlank.append (encodeRegs regs) R).cons 0 |>.cons 0)⟩ := by
  have hregs := return0_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step common121
      ⟨15, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step common121
      ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ =
      some ⟨19, Tape.mkL L (((ListBlank.append (encodeRegs regs) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

theorem return1_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (r + 2)
      ⟨63, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨63, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨63, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨78, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step common121
      ⟨78, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨63, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 63) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem return1_scan_regs (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (encodeRegs regs).length
      ⟨63, Tape.mkL (ListBlank.append (encodeRegs regs).reverse L) R⟩ =
      some ⟨63, Tape.mkL L (ListBlank.append (encodeRegs regs) R)⟩ := by
  induction regs generalizing L R with
  | nil => rfl
  | cons r rs ih =>
    rw [encodeRegs_cons, List.reverse_append, ListBlank.append_assoc,
      List.length_append, Nat.add_comm, nSteps_add]
    rw [ih (ListBlank.append (encodeReg r).reverse L) R, Option.bind_some,
      encodeReg_length, return1_scan_reg, ListBlank.append_assoc]

theorem return1_scan_fence (regs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 ((encodeRegs regs).length + 1)
      ⟨63, Tape.mkL (ListBlank.append (encodeRegs regs).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨78, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ := by
  have hregs := return1_scan_regs regs ((L.cons 0).cons 0) R
  have h1 : step common121
      ⟨63, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs regs) R)⟩ =
      some ⟨78, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs regs) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_one h1)

/-!
## 6. Pass 2 Register Increment & Decrement (`inc`, `decnz_zero`, `decnz_succ`)
-/

theorem regIncStage3_trans_one (k : ℕ) (hk : k < 4) :
    commonTrans (regIncStage3 k) 1 = some (0, .right, rhRegIncrChain (k + 2)) := by
  revert k hk; decide

theorem rhRegIncrChain_trans_one (m : ℕ) (hm : m ≤ 5) :
    commonTrans (rhRegIncrChain m) 1 = some (1, .right, rhRegIncrChain m) := by
  revert m hm; decide

theorem rhRegIncrChain_trans_zero (m : ℕ) (hm : m < 4) :
    commonTrans (rhRegIncrChain (m + 1)) 0 = some (0, .right, rhRegIncrChain m) := by
  revert m hm; decide

theorem rhRegIncrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 3)
    (L R : ListBlank (Fin 2)) :
    nSteps common121 ((encodeRegs pref).length + 1)
      ⟨rhRegIncrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨11, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 4 := by omega
    have hrs_le : rs.length ≤ 3 := by omega
    have h0 : step common121
        ⟨rhRegIncrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨rhRegIncrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (rhRegIncrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan (rhRegIncrChain_trans_one (rs.length + 1) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Rightward shift in States `13`/`11` (`2b.reg.inc.shift_1/2`) and return scan in `15`. -/
theorem inc_shift_eval (suff : List ℕ) (m : ℕ) (L_prev : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev) (regsTape suff)⟩ =
      some ⟨15, Tape.mkL L_prev (regsTape (m :: suff))⟩ := by
  induction suff generalizing m L_prev with
  | nil =>
    rw [regsTape_nil, List.replicate_succ, ListBlank.append]
    have h1 : step common121
        ⟨13, Tape.mk' ((ListBlank.append (List.replicate m 1) L_prev).cons 1) default⟩ =
        some ⟨15, Tape.mkL ((ListBlank.append (List.replicate m 1) L_prev).cons 1)
          (ListBlank.cons 0 default)⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      exact step_mk'_left (by rfl) _ default
    have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl)
      (m + 1) L_prev (ListBlank.cons 0 default)
    conv at hscan => lhs; rw [List.replicate_succ, ListBlank.append]
    have hcomb := step_nSteps h1 hscan
    rw [← append_encodeReg, ← regsTape_nil, ← regsTape_cons] at hcomb
    exact ⟨m + 2, by omega, hcomb⟩
  | cons r rs ih =>
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step common121
        ⟨13, Tape.mk' (ListBlank.append (List.replicate (m + 1) 1) L_prev)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨11, Tape.mk' ((ListBlank.append (List.replicate (m + 1) 1) L_prev).cons 0)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    rw [← append_encodeReg_reverse] at h1
    have hscan := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
      r (ListBlank.append (encodeReg m).reverse L_prev) ((regsTape rs).cons 0)
    have h2 : step common121
        ⟨11, Tape.mk' (ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)) ((regsTape rs).cons 0)⟩ =
        some ⟨13, Tape.mk' ((ListBlank.append (List.replicate r 1)
          (ListBlank.append (encodeReg m).reverse L_prev)).cons 1) (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcons1 : (ListBlank.append (List.replicate r 1)
        (ListBlank.append (encodeReg m).reverse L_prev)).cons 1 =
        ListBlank.append (List.replicate (r + 1) 1)
          (ListBlank.append (encodeReg m).reverse L_prev) := by
      rw [List.replicate_succ, ListBlank.append]
    rw [hcons1] at h2
    obtain ⟨s, hs1, hs⟩ := ih r (ListBlank.append (encodeReg m).reverse L_prev)
    have hret := return0_scan_reg m L_prev (regsTape (r :: rs))
    rw [← regsTape_cons] at hret
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan
      (step_nSteps h2 (nSteps_bind_eq hs hret)))
    exact ⟨_, by omega, hcomb⟩

/-- Pass 2 `3.<reg_k>.inc` (`k < 3`): increments `regs[k]` and lands in `19` (`6.break.0`). -/
theorem stage3_inc_pass2 (k : ℕ) (hk3 : k < 3) (p : ℕ) (regs : List ℕ) (hk : k < regs.length)
    (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨19, Tape.mkL L_stack
        ((regsTape (p :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (r :: suff)) := by
    have hlist : p :: regs = pref ++ r :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step common121
      ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegIncrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (r :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regIncStage3_trans_one k (by omega)) L_stack _
  have hpref_scan := rhRegIncrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (r :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hr_scan : nSteps common121 ((r + 1) + 1)
      ⟨11, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step common121
        ⟨11, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) L_pref)
          ((regsTape suff).cons 0)⟩ =
        some ⟨13, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := inc_shift_eval suff (r + 1) L_pref
  have hret := return0_scan_fence pref L_stack (regsTape ((r + 1) :: suff))
  have hset : ListBlank.append (encodeRegs pref) (regsTape ((r + 1) :: suff)) =
      regsTape (p :: regs.set k (r + 1)) := by
    rw [← regsTape_append]
    congr 1
    simp only [pref, List.cons_append]
    congr 1
    exact list_take_set_drop regs k (r + 1) hk
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift hret)))
  exact ⟨_, by omega, htotal⟩

theorem regDecnzStage3_trans_one (k : ℕ) (hk : k < 5) :
    commonTrans (regDecnzStage3 k) 1 = some (0, .right, rhRegDecrChain (k + 2)) := by
  revert k hk; decide

theorem rhRegDecrChain_trans_one (m : ℕ) (hm1 : 1 ≤ m) (hm6 : m ≤ 5) :
    commonTrans (rhRegDecrChain m) 1 = some (1, .right, rhRegDecrChain m) := by
  match m with
  | 0 => exfalso; omega
  | 1 | 2 | 3 | 4 | 5 => rfl
  | _ + 6 => exfalso; omega

theorem rhRegDecrChain_trans_zero (m : ℕ) (hm : m < 6) :
    commonTrans (rhRegDecrChain (m + 1)) 0 = some (0, .right, rhRegDecrChain m) := by
  revert m hm; decide

theorem rhRegDecrChain_scan_pref (pref : List ℕ) (hpref : pref.length ≤ 5)
    (L R : ListBlank (Fin 2)) :
    nSteps common121 ((encodeRegs pref).length + 1)
      ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨51, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_mk'_right (by rfl) L R)
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 6 := by omega
    have hrs_le : rs.length ≤ 5 := by omega
    have h0 : step common121
        ⟨rhRegDecrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨rhRegDecrChain (rs.length + 1),
          Tape.mk' (L.cons 0)
            (ListBlank.append (List.replicate (r + 1) 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := step_mk'_right (rhRegDecrChain_trans_zero (rs.length + 1) hrs_lt) L
        (ListBlank.append (encodeRegs (r :: rs)) R)
      conv at h => rhs; rw [encodeRegs_cons, ListBlank.append_assoc, append_encodeReg]
      exact h
    have hones := nSteps_mk'_right_scan
      (rhRegDecrChain_trans_one (rs.length + 1) (by omega) (by omega))
      (r + 1) (L.cons 0) ((ListBlank.append (encodeRegs rs) R).cons 0)
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← append_encodeReg_reverse, ← ListBlank.append_assoc, ← List.reverse_append,
      ← encodeRegs_cons] at hrest
    have hcomb := step_nSteps h0 (nSteps_bind_eq hones hrest)
    have hlen : (r + 1) + ((encodeRegs rs).length + 1) + 1 =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

/-- Leftward shift of a single register `m` in States `106`/`100` (`2b.reg.dec.shift_2/1`). -/
theorem dec_shift_reg (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (m + 2)
      ⟨106, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) R⟩ =
      some ⟨106, Tape.mkL L (ListBlank.append (encodeReg m) R)⟩ := by
  rw [List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨106, Tape.mkL ((ListBlank.append (List.replicate m 1) (L.cons 0)).cons 1) R⟩ =
      some ⟨100, Tape.mkL (ListBlank.append (List.replicate m 1) (L.cons 0)) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 100) (a := 1) (b := 1) (by rfl)
    m (L.cons 0) (R.cons 0)
  have h2 : step common121
      ⟨100, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate m 1) (R.cons 0))⟩ =
      some ⟨106, Tape.mkL L ((ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hcons : (ListBlank.append (List.replicate m 1) (R.cons 0)).cons 1 =
      ListBlank.append (encodeReg m) R := by
    rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  rw [hcons] at h2
  have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
  simpa [Nat.add_assoc] using hcomb

/-- Forward scan in States `92`/`79` (`scan_2/1`) and leftward shift in `100`/`106`. -/
theorem dec_scan_and_shift (suff : List ℕ) (m : ℕ) (L : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨92, Tape.mk' (ListBlank.append (encodeReg m).reverse (L.cons 0)) (regsTape suff)⟩ =
      some ⟨106, Tape.mkL L (regsTape (m :: (suff ++ [0])))⟩ := by
  induction suff generalizing m L with
  | nil =>
    rw [regsTape_nil, append_encodeReg_reverse]
    have h1 : step common121
        ⟨92, Tape.mk'
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨100, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ := by
      have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default :=
        default_cons_zero.symm
      conv_lhs => rw [hdef]
      rw [step_mk'_left (by rfl), default_cons_zero]
    have h2 : step common121
        ⟨100, Tape.mkL
          ((ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)).cons 0) default⟩ =
        some ⟨106, Tape.mkL (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0))
          (regsTape [0])⟩ := by
      have h := step_mkL_left (q := 100) (q' := 106) (a := 0) (b := 1) (by rfl)
        (ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)) default
      have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
        rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
        rfl
      rw [h0] at h
      exact h
    have hshift := dec_shift_reg m L (regsTape [0])
    rw [← regsTape_cons] at hshift
    exact ⟨m + 4, by omega, step_nSteps h1 (step_nSteps h2 hshift)⟩
  | cons r rs ih =>
    let L' := ListBlank.append (List.replicate (m + 1) 1) (L.cons 0)
    have hL' : ListBlank.append (encodeReg m).reverse (L.cons 0) = L'.cons 0 :=
      append_encodeReg_reverse m (L.cons 0)
    rw [hL', regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step common121
        ⟨92, Tape.mk' (L'.cons 0)
          ((ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0)).cons 1)⟩ =
        some ⟨79, Tape.mk' ((L'.cons 0).cons 1)
          (ListBlank.append (List.replicate r 1) ((regsTape rs).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 79) (a := 1) (b := 1) (by rfl)
      r ((L'.cons 0).cons 1) ((regsTape rs).cons 0)
    have h2 : step common121
        ⟨79, Tape.mk' (ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1))
          ((regsTape rs).cons 0)⟩ =
        some ⟨92, Tape.mk' ((ListBlank.append (List.replicate r 1) ((L'.cons 0).cons 1)).cons 0)
          (regsTape rs)⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan_reg := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r (L'.cons 0)] at hscan_reg
    obtain ⟨s, hs1, hs⟩ := ih r L'
    have hshift := dec_shift_reg m L (regsTape (r :: (rs ++ [0])))
    rw [← regsTape_cons] at hshift
    have hcomb := nSteps_bind_eq hscan_reg (nSteps_bind_eq hs hshift)
    exact ⟨_, by omega, hcomb⟩

theorem dec_shift2_scan_reg (r : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (r + 2)
      ⟨106, Tape.mkL (ListBlank.append (encodeReg r).reverse L) R⟩ =
      some ⟨15, Tape.mkL L (ListBlank.append (encodeReg r) R)⟩ := by
  rw [append_encodeReg_reverse, List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨106, Tape.mkL (((ListBlank.append (List.replicate r 1) L).cons 1).cons 0) R⟩ =
      some ⟨15, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step common121
      ⟨15, Tape.mkL ((ListBlank.append (List.replicate r 1) L).cons 1) (R.cons 0)⟩ =
      some ⟨15, Tape.mkL (ListBlank.append (List.replicate r 1) L) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan := nSteps_mkL_left_scan (q := 15) (a := 1) (b := 1) (by rfl) r L ((R.cons 0).cons 1)
  have hcomb := step_nSteps h1 (step_nSteps h2 hscan)
  rw [hcomb, append_replicate_cons, append_cons_snoc]
  rfl

theorem dec_return0_scan_fence (p : ℕ) (rs : List ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 ((encodeRegs (p :: rs)).length + 2)
      ⟨106, Tape.mkL (ListBlank.append (encodeRegs (p :: rs)).reverse ((L.cons 0).cons 0)) R⟩ =
      some ⟨19, Tape.mkL L ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0 |>.cons 0)⟩ := by
  have hscan_nonempty : ∀ (pref : List ℕ), pref ≠ [] → ∀ L' R',
      nSteps common121 (encodeRegs pref).length
        ⟨106, Tape.mkL (ListBlank.append (encodeRegs pref).reverse L') R'⟩ =
        some ⟨15, Tape.mkL L' (ListBlank.append (encodeRegs pref) R')⟩ := by
    intro pref hne L' R'
    induction pref using List.reverseRecOn generalizing L' R' with
    | nil => contradiction
    | append_singleton xs x _ =>
      rw [encodeRegs_append, encodeRegs_cons, encodeRegs_nil, List.append_nil,
        List.reverse_append, ListBlank.append_assoc, List.length_append,
        Nat.add_comm, nSteps_add, encodeReg_length,
        dec_shift2_scan_reg, Option.bind_some, return0_scan_regs, ListBlank.append_assoc]
  have hregs := hscan_nonempty (p :: rs) (List.cons_ne_nil p rs) ((L.cons 0).cons 0) R
  have h1 : step common121
      ⟨15, Tape.mkL ((L.cons 0).cons 0) (ListBlank.append (encodeRegs (p :: rs)) R)⟩ =
      some ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  have h2 : step common121
      ⟨17, Tape.mkL (L.cons 0) ((ListBlank.append (encodeRegs (p :: rs)) R).cons 0)⟩ =
      some ⟨19, Tape.mkL L (((ListBlank.append (encodeRegs (p :: rs)) R).cons 0).cons 0)⟩ :=
    step_mkL_left (by rfl) _ _
  exact nSteps_bind_eq hregs (step_nSteps h1 (step_one h2))

/-- Pass 2 `3.<reg_k>.decnz` when `regs[k] = 0`: leaves `regs` unchanged and enters `91`. -/
theorem stage3_decnz_pass2_zero (k : ℕ) (hk5 : k < 5) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hz : regs[k] = 0) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨78, Tape.mkL (L_stack.cons 0) ((regsTape (p :: regs)).cons 0)⟩ := by
  set pref := p :: regs.take k
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape (0 :: suff)) := by
    have hlist : p :: regs = pref ++ 0 :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hz]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step common121
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape (0 :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk5) L_stack _
  have hpref_scan := rhRegDecrChain_scan_pref pref (by omega)
    (L_stack.cons 0) (regsTape (0 :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have h1 : step common121 ⟨51, Tape.mk' L_pref (regsTape (0 :: suff))⟩ =
      some ⟨64, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mk'_right (by rfl) L_pref ((regsTape suff).cons 0)
  have h2 : step common121 ⟨64, Tape.mk' (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨51, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ :=
    step_mk'_left (by rfl) (L_pref.cons 0) (regsTape suff)
  have h3 : step common121 ⟨51, Tape.mkL (L_pref.cons 0) ((regsTape suff).cons 0)⟩ =
      some ⟨63, Tape.mkL L_pref (regsTape (0 :: suff))⟩ := by
    rw [regsTape_cons, append_encodeReg]
    exact step_mkL_left (by rfl) L_pref ((regsTape suff).cons 0)
  have hret := return1_scan_fence pref L_stack (regsTape (0 :: suff))
  rw [← hregs_split] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps h1 (step_nSteps h2 (step_nSteps h3 hret))))
  exact ⟨_, by omega, htotal⟩

/-- Pass 2 `3.<reg_k>.decnz` when `regs[k] > 0`:
decrements `regs[k]`, appends `[0]`, enters `19`. -/
theorem stage3_decnz_pass2_pos (k : ℕ) (hk5 : k < 5) (p : ℕ) (regs : List ℕ)
    (hk : k < regs.length) (hpos : 0 < regs[k]) (L_stack : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨19, Tape.mkL L_stack
        ((regsTape (p :: (regs.set k (regs[k] - 1) ++ [0]))).cons 0 |>.cons 0)⟩ := by
  set pref := p :: regs.take k
  set r' := regs[k] - 1
  set suff := regs.drop (k + 1)
  have hr_eq : regs[k] = r' + 1 := by omega
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have hpref_len : pref.length = k + 1 := by
    simp [pref, List.length_take_of_le hle]
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff)) := by
    have hlist : p :: regs = pref ++ (r' + 1) :: suff := by
      simp only [pref, List.cons_append]
      congr 1
      rw [← hr_eq]
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  have h0 : step common121
      ⟨regDecnzStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
      some ⟨rhRegDecrChain (pref.length + 1),
        Tape.mk' (L_stack.cons 0)
          ((ListBlank.append (encodeRegs pref) (regsTape ((r' + 1) :: suff))).cons 0)⟩ := by
    rw [hregs_split, hpref_len]
    exact step_mk'_right (regDecnzStage3_trans_one k hk5) L_stack _
  have hpref_scan := rhRegDecrChain_scan_pref pref (by omega) (L_stack.cons 0)
    (regsTape ((r' + 1) :: suff))
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_stack.cons 0).cons 0)
  have hinit : step common121 ⟨51, Tape.mk' L_pref (regsTape ((r' + 1) :: suff))⟩ =
      some ⟨64, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ := by
    have hcons : regsTape ((r' + 1) :: suff) = (regsTape (r' :: suff)).cons 1 := by
      rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append,
        ← append_encodeReg, ← regsTape_cons]
    rw [hcons]
    exact step_mk'_right (by rfl) L_pref (regsTape (r' :: suff))
  have hr'_scan : nSteps common121 (r' + 2)
      ⟨64, Tape.mk' (L_pref.cons 0) (regsTape (r' :: suff))⟩ =
      some ⟨92, Tape.mk' (ListBlank.append (encodeReg r').reverse (L_pref.cons 0))
        (regsTape suff)⟩ := by
    rw [regsTape_cons, append_encodeReg, List.replicate_succ, ListBlank.append]
    have h1 : step common121
        ⟨64, Tape.mk' (L_pref.cons 0)
          ((ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0)).cons 1)⟩ =
        some ⟨79, Tape.mk' ((L_pref.cons 0).cons 1)
          (ListBlank.append (List.replicate r' 1) ((regsTape suff).cons 0))⟩ :=
      step_mk'_right (by rfl) _ _
    have hscan := nSteps_mk'_right_scan (q := 79) (a := 1) (b := 1) (by rfl)
      r' ((L_pref.cons 0).cons 1) ((regsTape suff).cons 0)
    have h2 : step common121
        ⟨79, Tape.mk' (ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1))
          ((regsTape suff).cons 0)⟩ =
        some ⟨92, Tape.mk'
          ((ListBlank.append (List.replicate r' 1) ((L_pref.cons 0).cons 1)).cons 0)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := step_nSteps h1 (nSteps_bind_eq hscan (step_one h2))
    rw [append_replicate_cons, ← append_encodeReg_reverse r' (L_pref.cons 0)] at hcomb
    simpa [Nat.add_assoc] using hcomb
  obtain ⟨s_shift, hs1, hshift⟩ := dec_scan_and_shift suff r' L_pref
  have hret := dec_return0_scan_fence p (regs.take k) L_stack (regsTape (r' :: (suff ++ [0])))
  have hset : ListBlank.append (encodeRegs pref) (regsTape (r' :: (suff ++ [0]))) =
      regsTape (p :: (regs.set k r' ++ [0])) := by
    rw [← regsTape_append]
    congr 1
    have h1 : pref ++ r' :: (suff ++ [0]) = p :: ((regs.take k ++ r' :: suff) ++ [0]) := by
      simp [pref]
    rw [h1, list_take_set_drop regs k r' hk]
  rw [hset] at hret
  have htotal := step_nSteps h0 (nSteps_bind_eq hpref_scan
    (step_nSteps hinit (nSteps_bind_eq hr'_scan (nSteps_bind_eq hshift hret))))
  exact ⟨_, by omega, htotal⟩

/-!
## 7. Break, Cleanup, Halt & End-to-End Root Gadgets
-/

theorem halt_at_6 (L R : ListBlank (Fin 2)) :
    step common121 ⟨6, Tape.mk' L (R.cons 1)⟩ = none := by
  simp [step, commonTrans_eq, Tape.mk']; rfl

theorem halt_at_77 (L R : ListBlank (Fin 2)) :
    step common121 ⟨77, Tape.mk' L (R.cons 1)⟩ = none := by
  simp [step, commonTrans_eq, Tape.mk']; rfl

theorem cleanup_to_10 (L : ListBlank (Fin 2)) (z p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨21, Tape.mk' L (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg p) R))⟩ =
      some ⟨10, Tape.mkL L (ListBlank.append (List.replicate (z + p) 0)
        (ListBlank.append [1, 0] R))⟩ := by
  have hscan_z := nSteps_mk'_right_scan (q := 21) (a := 0) (b := 0) (by rfl) z
    L (ListBlank.append (encodeReg p) R)
  conv at hscan_z => rhs; rw [append_encodeReg, List.replicate_succ, ListBlank.append]
  have h1 : step common121
      ⟨21, Tape.mk' (ListBlank.append (List.replicate z 0) L)
        ((ListBlank.append (List.replicate p 1) (R.cons 0)).cons 1)⟩ =
      some ⟨23, Tape.mk' ((ListBlank.append (List.replicate z 0) L).cons 0)
        (ListBlank.append (List.replicate p 1) (R.cons 0))⟩ :=
    step_mk'_right (by rfl) _ _
  have hscan_p := nSteps_mk'_right_scan (q := 23) (a := 1) (b := 0) (by rfl) p
    ((ListBlank.append (List.replicate z 0) L).cons 0) (R.cons 0)
  have hzeros : ListBlank.append (List.replicate p 0)
      ((ListBlank.append (List.replicate z 0) L).cons 0) =
      (ListBlank.append (List.replicate (z + p) 0) L).cons 0 := by
    rw [append_replicate_cons, ← ListBlank.append_assoc, ← List.replicate_add]
    have hadd : p + 1 + z = (z + p) + 1 := by omega
    rw [hadd, List.replicate_succ, ListBlank.append]
  rw [hzeros] at hscan_p
  have h2 : step common121
      ⟨23, Tape.mk' ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨24, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ :=
    step_mk'_left (by rfl) _ R
  have h3 : step common121
      ⟨24, Tape.mkL ((ListBlank.append (List.replicate (z + p) 0) L).cons 0) (R.cons 0)⟩ =
      some ⟨10, Tape.mkL (ListBlank.append (List.replicate (z + p) 0) L)
        (ListBlank.append [1, 0] R)⟩ :=
    step_mkL_left (by rfl) _ _
  have hscan_back := continue0_scan_zeros (z + p) L (ListBlank.append [1, 0] R)
  have htotal := nSteps_bind_eq hscan_z (step_nSteps h1 (nSteps_bind_eq hscan_p
    (step_nSteps h2 (step_nSteps h3 hscan_back))))
  exact ⟨_, by omega, htotal⟩

theorem break0_step (c₀ : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps common121 (c₀ + 1)
      ⟨19, Tape.mkL (ListBlank.append (List.replicate c₀ 1) (L.cons 0)) R⟩ =
      some ⟨21, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ := by
  have hscan := nSteps_mkL_left_scan (q := 19) (a := 1) (b := 0) (by rfl) c₀ (L.cons 0) R
  have h1 : step common121
      ⟨19, Tape.mkL (L.cons 0) (ListBlank.append (List.replicate c₀ 0) R)⟩ =
      some ⟨21, Tape.mk' (L.cons 1) (ListBlank.append (List.replicate c₀ 0) R)⟩ :=
    step_mkL_right (by rfl) _ _
  exact nSteps_bind_eq hscan (step_one h1)


/-!
## 8. Bootstrap Proof (`0a.boot1` & `0b.boot2`) from `init` to `main.0` (`State 27`)
-/

theorem step_mkL_left_rh {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.write, Tape.move]

theorem step_mkL_right_rh {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mkL (L.cons a) R⟩ = some ⟨q', Tape.mk' (L.cons b) R⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem step_mk'_left_rh {q q' : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step riemann121 ⟨q, Tape.mk' L (R.cons a)⟩ = some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, rh121Trans_eq, h, Tape.mkL, Tape.mk', Tape.write, Tape.move]

theorem nSteps_mkL_left_scan_rh {q : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .left, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 k ⟨q, Tape.mkL (ListBlank.append (List.replicate k a) L) R⟩ =
      some ⟨q, Tape.mkL L (ListBlank.append (List.replicate k b) R)⟩ := by
  induction k generalizing R with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mkL_left_rh h]
    simp only [Option.bind_some]
    rw [ih (R.cons b), append_replicate_cons]

theorem nSteps_mk'_right_scan_rh {q : Fin 121} {a b : Fin 2}
    (h : rh121Trans q a = some (b, .right, q)) (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 k ⟨q, Tape.mk' L (ListBlank.append (List.replicate k a) R)⟩ =
      some ⟨q, Tape.mk' (ListBlank.append (List.replicate k b) L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, ListBlank.append, nSteps_succ, step_mk'_right_rh h]
    simp only [Option.bind_some]
    rw [ih (L.cons b), append_replicate_cons]


theorem boot1_scan_DE (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨3, Tape.mk' L (ListBlank.append (pair10 k) R)⟩ =
      some ⟨3, Tape.mk' (ListBlank.append (pair10 k).reverse L) R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
    simp only [pair10, ListBlank.append]
    have h1 : step riemann121
        ⟨3, Tape.mk' L (((ListBlank.append (pair10 k) R).cons 0).cons 1)⟩ =
        some ⟨5, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ :=
      step_mk'_right_rh (by rfl) _ _
    have h2 : step riemann121
        ⟨5, Tape.mk' (L.cons 1) ((ListBlank.append (pair10 k) R).cons 0)⟩ =
        some ⟨3, Tape.mk' ((L.cons 1).cons 0) (ListBlank.append (pair10 k) R)⟩ :=
      step_mk'_right_rh (by rfl) _ _
    have hrest := ih ((L.cons 1).cons 0)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    rw [hlen] at hcomb
    simpa [pair10, List.reverse_cons, ListBlank.append_assoc] using hcomb

theorem boot1_scan_DB (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨3, Tape.mkL (ListBlank.append (pair10 k).reverse L) R⟩ =
      some ⟨3, Tape.mkL L (ListBlank.append (pair01 k) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step riemann121
        ⟨3, Tape.mkL (((ListBlank.append (pair10 k).reverse L).cons 1).cons 0) R⟩ =
        some ⟨1, Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 1)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have h2 : step riemann121
        ⟨1, Tape.mkL ((ListBlank.append (pair10 k).reverse L).cons 1) (R.cons 1)⟩ =
        some ⟨3, Tape.mkL (ListBlank.append (pair10 k).reverse L) ((R.cons 1).cons 0)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have hrest := ih L ((R.cons 1).cons 0)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hR : ListBlank.append (pair01 k) ((R.cons 1).cons 0) =
        ListBlank.append (pair01 (k + 1)) R := by
      rw [← pair01_snoc, ListBlank.append_assoc]
      rfl
    rw [hlen, hR] at hcomb
    exact hcomb

theorem boot1_scan_AC (k : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k) ⟨0, Tape.mkL (ListBlank.append (pair01 k).reverse L) R⟩ =
      some ⟨0, Tape.mkL L (ListBlank.append (List.replicate (2 * k) 1) R)⟩ := by
  induction k generalizing L R with
  | zero => rfl
  | succ k ih =>
    rw [← pair01_snoc, List.reverse_append, ListBlank.append_assoc]
    have h1 : step riemann121
        ⟨0, Tape.mkL (((ListBlank.append (pair01 k).reverse L).cons 0).cons 1) R⟩ =
        some ⟨2, Tape.mkL ((ListBlank.append (pair01 k).reverse L).cons 0) (R.cons 1)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have h2 : step riemann121
        ⟨2, Tape.mkL ((ListBlank.append (pair01 k).reverse L).cons 0) (R.cons 1)⟩ =
        some ⟨0, Tape.mkL (ListBlank.append (pair01 k).reverse L) ((R.cons 1).cons 1)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have hrest := ih L ((R.cons 1).cons 1)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * k + 1 + 1 = 2 * (k + 1) := by omega
    have hR : ListBlank.append (List.replicate (2 * k) 1) ((R.cons 1).cons 1) =
        ListBlank.append (List.replicate (2 * (k + 1)) 1) R := by
      rw [append_replicate_cons, append_replicate_cons, hlen]
    rw [hlen, hR] at hcomb
    exact hcomb

def rhMidCfg (k m : ℕ) (R : ListBlank (Fin 2)) : Cfg 121 2 :=
  ⟨0, Tape.mk' default
    (ListBlank.append ([0, 1, 1] ++ pair01 k ++ List.replicate m 1) R)⟩

theorem rhMidCfg_to_state3 (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 2 ⟨0, Tape.mk' default (ListBlank.append ([0, 1, 1] ++ pair01 k) R)⟩ =
      some ⟨3, Tape.mk' default (ListBlank.append (pair10 (k + 1) ++ [1]) R)⟩ := by
  simp only [List.cons_append, List.nil_append, ListBlank.append]
  have h1 : step riemann121
      ⟨0, Tape.mk' default (((ListBlank.append (pair01 k) R).cons 1).cons 1 |>.cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default)
        (((ListBlank.append (pair01 k) R).cons 1).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h2 : step riemann121
      ⟨1, Tape.mk' (ListBlank.cons 1 default)
        (((ListBlank.append (pair01 k) R).cons 1).cons 1)⟩ =
      some ⟨3, Tape.mk' default
        (((ListBlank.append (pair01 k) R).cons 1).cons 0 |>.cons 1)⟩ := by
    rw [step_mk'_left_rh (by rfl), Tape.mkL_cons, ← Tape.mk'_cons]
  have hcomb := step_nSteps h1 (step_one h2)
  have hR : (((ListBlank.append (pair01 k) R).cons 1).cons 0 |>.cons 1) =
      ListBlank.append (pair10 (k + 1) ++ [1]) R := by
    change ListBlank.append (1 :: 0 :: 1 :: pair01 k) R = _
    rw [cons_one_pair01]
    rfl
  rw [hR] at hcomb
  exact hcomb

theorem rhMidCfg_step_two (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 17) (rhMidCfg k 2 R) =
      some (rhMidCfg (k + 3) 0 (R.cons 0)) := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
  have hinit := rhMidCfg_to_state3 k (ListBlank.append [1, 1] R)
  have hscanR := boot1_scan_DE (k + 1) default (ListBlank.append [1, 1, 1] R)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  have hs1 : step riemann121 ⟨3, Tape.mk' L_k (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs2 : step riemann121 ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs3 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 1)⟩ =
      some ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left_rh (by rfl) _ _
  have hs4 : step riemann121 ⟨3, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have hs5 : step riemann121 ⟨1, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨3, Tape.mkL L_k (((R.cons 0).cons 1).cons 0)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have hturn := step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3 (step_nSteps hs4 (step_one hs5))))
  have hscanL := boot1_scan_DB (k + 1) default (((R.cons 0).cons 1).cons 0)
  set R_k := ListBlank.append (pair01 (k + 1)) (((R.cons 0).cons 1).cons 0)
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step riemann121 ⟨3, Tape.mkL default R_k⟩ =
      some ⟨1, Tape.mkL default (R_k.cons 1)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left_rh (by rfl) default R_k
  have he2 : step riemann121 ⟨1, Tape.mkL default (R_k.cons 1)⟩ =
      some ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_left_rh (by rfl) default (R_k.cons 1)
  have he3 : step riemann121 ⟨0, Tape.mkL default ((R_k.cons 1).cons 0)⟩ =
      some ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    exact step_mkL_right_rh (by rfl) default ((R_k.cons 1).cons 0)
  have he4 : step riemann121 ⟨1, Tape.mk' (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ :=
    step_mk'_left_rh (by rfl) _ (R_k.cons 1)
  have he5 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) ((R_k.cons 1).cons 0)⟩ =
      some ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have he6 : step riemann121 ⟨2, Tape.mkL default (((R_k.cons 1).cons 0).cons 1)⟩ =
      some ⟨0, Tape.mk' default ((((R_k.cons 1).cons 0).cons 1).cons 1 |>.cons 0)⟩ := by
    conv_lhs => rw [hdef]
    rw [step_mkL_left_rh (by rfl), Tape.mkL_default]
  have hedge := step_nSteps he1 (step_nSteps he2 (step_nSteps he3
    (step_nSteps he4 (step_nSteps he5 (step_one he6)))))
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (nSteps_bind_eq hturn (nSteps_bind_eq hscanL hedge)))
  have hlen : 2 + (2 * (k + 1) + (5 + (2 * (k + 1) + 6))) = 4 * k + 17 := by omega
  rw [hlen] at htotal
  have hR_eq : ((((R_k.cons 1).cons 0).cons 1).cons 1 |>.cons 0) =
      ListBlank.append [0, 1, 1] (ListBlank.append (pair01 (k + 3)) (R.cons 0)) := by
    simp only [R_k]
    change ListBlank.append [0, 1, 1]
      (ListBlank.append (pair01 (k + 2)) (ListBlank.append [0, 1] (R.cons 0))) = _
    rw [← ListBlank.append_assoc (pair01 (k + 2)), pair01_snoc]
  rw [hR_eq] at htotal
  exact htotal

theorem rhMidCfg_step_three (k m : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 17) (rhMidCfg k (m + 3) R) =
      some (rhMidCfg (k + 4) m R) := by
  have heq :
      rhMidCfg k (m + 3) R = rhMidCfg k 2 (ListBlank.append (List.replicate (m + 1) 1) R) := by
    unfold rhMidCfg
    have hrep : List.replicate (m + 3) (1 : Fin 2) =
        List.replicate 2 1 ++ List.replicate (m + 1) 1 := by
      rw [show m + 3 = 2 + (m + 1) by omega, List.replicate_add]
    simp only [hrep, List.append_assoc, ListBlank.append_assoc]
  rw [heq, rhMidCfg_step_two]
  congr 1
  unfold rhMidCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc, ListBlank.append]
  have hpair : ListBlank.append (pair01 (k + 3))
      (((ListBlank.append (List.replicate m 1) R).cons 1).cons 0) =
      ListBlank.append (pair01 (k + 4)) (ListBlank.append (List.replicate m 1) R) := by
    rw [← pair01_snoc (k + 3), ListBlank.append_assoc]
    rfl
  rw [hpair]

theorem rhMidCfg_loop (j k r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, nSteps riemann121 s (rhMidCfg k (3 * j + r) R) =
      some (rhMidCfg (k + 4 * j) r R) := by
  induction j generalizing k with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
    exact ⟨0, rfl⟩
  | succ j ih =>
    have h1 : 3 * (j + 1) + r = (3 * j + r) + 3 := by omega
    rw [h1]
    have hstep := rhMidCfg_step_three k (3 * j + r) R
    obtain ⟨s, hs⟩ := ih (k + 4)
    have h2 : k + 4 + 4 * j = k + 4 * (j + 1) := by omega
    rw [h2] at hs
    exact ⟨_, nSteps_bind_eq hstep hs⟩

theorem rhMidCfg_step_zero (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (4 * k + 12) (rhMidCfg k 0 ((R.cons 0).cons 0)) =
      some (rhMidCfg 0 (2 * k + 2) ((R.cons 1).cons 0)) := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_nil]
  have hinit := rhMidCfg_to_state3 k ((R.cons 0).cons 0)
  have hpair : ListBlank.append (pair10 (k + 1) ++ [1]) ((R.cons 0).cons 0) =
      ListBlank.append (pair10 (k + 2)) (R.cons 0) := by
    rw [ListBlank.append_assoc, ← pair10_snoc (k + 1), ListBlank.append_assoc]
    rfl
  rw [hpair] at hinit
  have hscanR := boot1_scan_DE (k + 2) default (R.cons 0)
  have hL_split : ListBlank.append (pair10 (k + 2)).reverse default =
      (ListBlank.append (pair01 (k + 1)).reverse (ListBlank.cons 1 default)).cons 0 := by
    simp only [pair10_succ_eq (k + 1), List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, ListBlank.append_assoc, ListBlank.append]
  rw [hL_split] at hscanR
  set L_p := ListBlank.append (pair01 (k + 1)).reverse (ListBlank.cons 1 default)
  have hs1 : step riemann121 ⟨3, Tape.mk' (L_p.cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ :=
    step_mk'_left_rh (by rfl) _ _
  have hs2 : step riemann121 ⟨1, Tape.mkL (L_p.cons 0) (R.cons 1)⟩ =
      some ⟨0, Tape.mkL L_p ((R.cons 1).cons 0)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have hscanL := boot1_scan_AC (k + 1) (ListBlank.cons 1 default) ((R.cons 1).cons 0)
  set R_ones := ListBlank.append (List.replicate (2 * (k + 1)) 1) ((R.cons 1).cons 0)
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have he1 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) R_ones⟩ =
      some ⟨2, Tape.mkL default (R_ones.cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have he2 : step riemann121 ⟨2, Tape.mkL default (R_ones.cons 1)⟩ =
      some ⟨0, Tape.mk' default (((R_ones.cons 1).cons 1).cons 0)⟩ := by
    conv_lhs => rw [hdef]
    rw [step_mkL_left_rh (by rfl), Tape.mkL_default]
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscanL
      (step_nSteps he1 (step_one he2))))))
  have hlen : 2 + (2 * (k + 2) + (2 * (k + 1) + (1 + 1) + 1 + 1)) = 4 * k + 12 := by omega
  rw [hlen] at htotal
  have hR_eq : (((R_ones.cons 1).cons 1).cons 0) =
      ListBlank.append ([0, 1, 1] ++ pair01 0 ++ List.replicate (2 * k + 2) 1)
        ((R.cons 1).cons 0) := by
    simp only [R_ones, pair01, List.append_nil]
    rfl
  rw [hR_eq] at htotal
  exact htotal

theorem rhMidCfg_exit_one (k : ℕ) (R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * k + 11) (rhMidCfg k 1 (R.cons 0)) =
      some ⟨4, Tape.mk' (ListBlank.append (pair10 (k + 1) ++ [1]).reverse default)
        ((R.cons 0).cons 1)⟩ := by
  unfold rhMidCfg
  simp only [List.replicate, List.append_assoc, ListBlank.append_assoc]
  have hinit := rhMidCfg_to_state3 k ((R.cons 0).cons 1)
  have hscanR := boot1_scan_DE (k + 1) default (((R.cons 0).cons 1).cons 1)
  simp only [ListBlank.append_assoc, ListBlank.append] at hinit hscanR
  set L_k := ListBlank.append (pair10 (k + 1)).reverse default
  have hs1 : step riemann121 ⟨3, Tape.mk' L_k (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs2 : step riemann121 ⟨5, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs3 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ :=
    step_mk'_left_rh (by rfl) _ _
  have hs4 : step riemann121 ⟨0, Tape.mkL ((L_k.cons 1).cons 0) (R.cons 0)⟩ =
      some ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mkL_right_rh (by rfl) _ _
  have hs5 : step riemann121 ⟨1, Tape.mk' ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_left_rh (by rfl) _ _
  have hs6 : step riemann121 ⟨0, Tape.mkL ((L_k.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have hs7 : step riemann121 ⟨2, Tape.mkL (L_k.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨4, Tape.mk' (L_k.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mkL_right_rh (by rfl) _ _
  have htotal := nSteps_bind_eq hinit (nSteps_bind_eq hscanR
    (step_nSteps hs1 (step_nSteps hs2 (step_nSteps hs3
      (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6 (step_one hs7))))))))
  have hlen : 2 + (2 * (k + 1) + 7) = 2 * k + 11 := by omega
  rw [hlen] at htotal
  simpa [L_k, List.reverse_append, ListBlank.append_assoc] using htotal

theorem boot1_eval :
    ∃ s, nSteps riemann121 s init =
      some ⟨4, Tape.mk' (ListBlank.append (pair10 1909 ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ := by
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have h0_1 : step riemann121 init = some ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_right_rh (q := 0) (q' := 1) (a := 0) (b := 1) (by rfl) default default
    rwa [← hdef] at h
  have h0_2 : step riemann121 ⟨1, Tape.mk' (ListBlank.cons 1 default) default⟩ =
      some ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ := by
    have h := step_mk'_left_rh (q := 1) (q' := 0) (a := 0) (b := 0) (by rfl)
      (ListBlank.cons 1 default) default
    rwa [← hdef] at h
  have h0_3 : step riemann121 ⟨0, Tape.mkL (ListBlank.cons 1 default) default⟩ =
      some ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have h0_4 : step riemann121 ⟨2, Tape.mkL default (ListBlank.cons 1 default)⟩ =
      some (rhMidCfg 0 0 default) := by
    have h := step_mkL_left_rh (q := 2) (q' := 0) (a := 0) (b := 1) (by rfl)
      default (ListBlank.cons 1 default)
    rw [← hdef, Tape.mkL_default] at h
    exact h
  have hr0 : nSteps riemann121 4 init = some (rhMidCfg 0 0 default) :=
    step_nSteps h0_1 (step_nSteps h0_2 (step_nSteps h0_3 (step_one h0_4)))
  have hr0_1 : nSteps riemann121 12 (rhMidCfg 0 0 default) =
      some (rhMidCfg 0 2 (ListBlank.append [0, 1] default)) := by
    have h := rhMidCfg_step_zero 0 default
    rwa [default_cons_zero, default_cons_zero] at h
  have hr1_a := rhMidCfg_step_two 0 (ListBlank.append [0, 1] default)
  have hr1_b : nSteps riemann121 24 (rhMidCfg 3 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (rhMidCfg 0 8 (ListBlank.append [0, 1, 1] default)) :=
    rhMidCfg_step_zero 3 (ListBlank.cons 1 default)
  obtain ⟨s2, hr2_loop⟩ := rhMidCfg_loop 2 0 2 (ListBlank.append [0, 1, 1] default)
  have hr2_a := rhMidCfg_step_two 8 (ListBlank.append [0, 1, 1] default)
  have hr2_b : nSteps riemann121 56
      (rhMidCfg 11 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 24 (ListBlank.append [0, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 11 (ListBlank.append [1, 1] default)
  obtain ⟨s3, hr3_loop⟩ := rhMidCfg_loop 8 0 0 (ListBlank.append [0, 1, 1, 1] default)
  have hr3_eq : rhMidCfg 32 0 (ListBlank.append [0, 1, 1, 1] default) = rhMidCfg 33 2 default := by
    unfold rhMidCfg
    simp only [List.replicate, List.append_nil, List.append_assoc, ListBlank.append_assoc]
    have hp : ListBlank.append (pair01 32) (ListBlank.append [0, 1, 1, 1] default) =
        ListBlank.append (pair01 33) (ListBlank.append [1, 1] default) := by
      rw [← pair01_snoc 32, ListBlank.append_assoc]
      rfl
    rw [hp]
  rw [hr3_eq] at hr3_loop
  have hr3_a := rhMidCfg_step_two 33 default
  have hr3_b : nSteps riemann121 156 (rhMidCfg 36 0 (ListBlank.cons 0 default)) =
      some (rhMidCfg 0 74 (ListBlank.append [0, 1] default)) := by
    have h := rhMidCfg_step_zero 36 default
    rwa [default_cons_zero] at h
  obtain ⟨s4, hr4_loop⟩ := rhMidCfg_loop 24 0 2 (ListBlank.append [0, 1] default)
  have hr4_a := rhMidCfg_step_two 96 (ListBlank.append [0, 1] default)
  have hr4_b : nSteps riemann121 408 (rhMidCfg 99 0 ((ListBlank.append [0, 1] default).cons 0)) =
      some (rhMidCfg 0 200 (ListBlank.append [0, 1, 1] default)) :=
    rhMidCfg_step_zero 99 (ListBlank.cons 1 default)
  obtain ⟨s5, hr5_loop⟩ := rhMidCfg_loop 66 0 2 (ListBlank.append [0, 1, 1] default)
  have hr5_a := rhMidCfg_step_two 264 (ListBlank.append [0, 1, 1] default)
  have hr5_b : nSteps riemann121 1080
      (rhMidCfg 267 0 ((ListBlank.append [0, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 536 (ListBlank.append [0, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 267 (ListBlank.append [1, 1] default)
  obtain ⟨s6, hr6_loop⟩ := rhMidCfg_loop 178 0 2 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_a := rhMidCfg_step_two 712 (ListBlank.append [0, 1, 1, 1] default)
  have hr6_b : nSteps riemann121 2872
      (rhMidCfg 715 0 ((ListBlank.append [0, 1, 1, 1] default).cons 0)) =
      some (rhMidCfg 0 1432 (ListBlank.append [0, 1, 1, 1, 1] default)) :=
    rhMidCfg_step_zero 715 (ListBlank.append [1, 1, 1] default)
  obtain ⟨s7, hr7_loop⟩ := rhMidCfg_loop 477 0 1 (ListBlank.append [0, 1, 1, 1, 1] default)
  have hexit := rhMidCfg_exit_one 1908 (ListBlank.append [1, 1, 1, 1] default)
  exact ⟨_, nSteps_bind_eq hr0 (nSteps_bind_eq hr0_1 (nSteps_bind_eq hr1_a (nSteps_bind_eq hr1_b
    (nSteps_bind_eq hr2_loop (nSteps_bind_eq hr2_a (nSteps_bind_eq hr2_b
      (nSteps_bind_eq hr3_loop (nSteps_bind_eq hr3_a (nSteps_bind_eq hr3_b
        (nSteps_bind_eq hr4_loop (nSteps_bind_eq hr4_a (nSteps_bind_eq hr4_b
          (nSteps_bind_eq hr5_loop (nSteps_bind_eq hr5_a (nSteps_bind_eq hr5_b
            (nSteps_bind_eq hr6_loop (nSteps_bind_eq hr6_a (nSteps_bind_eq hr6_b
              (nSteps_bind_eq hr7_loop hexit)))))))))))))))))))⟩

theorem boot2_scan_pair (L R : ListBlank (Fin 2)) :
    nSteps riemann121 2 ⟨24, Tape.mk' L (ListBlank.append [1, 0] R)⟩ =
      some ⟨24, Tape.mk' ((L.cons 1).cons 0) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L ((R.cons 0).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) (R.cons 0)⟩ :=
    step_mk'_right_rh (by rfl) L (R.cons 0)
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) (R.cons 0)⟩ =
      some ⟨24, Tape.mk' ((L.cons 1).cons 0) R⟩ :=
    step_mk'_right_rh (by rfl) (L.cons 1) R
  exact step_nSteps h1 (step_one h2)

theorem boot2_scan_pairs (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * m) ⟨24, Tape.mk' L (ListBlank.append (pair10 m) R)⟩ =
      some ⟨24, Tape.mk' (ListBlank.append (pair10 m).reverse L) R⟩ := by
  induction m generalizing L with
  | zero => rfl
  | succ m ih =>
    have hp : ListBlank.append (pair10 (m + 1)) R =
        ListBlank.append [1, 0] (ListBlank.append (pair10 m) R) := rfl
    rw [hp]
    have h1 := boot2_scan_pair L (ListBlank.append (pair10 m) R)
    have h2 := ih ((L.cons 1).cons 0)
    have hcomb := nSteps_bind_eq h1 h2
    have hlen : 2 + 2 * m = 2 * (m + 1) := by omega
    rw [hlen] at hcomb
    simpa [pair10, List.reverse_cons, ListBlank.append_assoc] using hcomb

theorem boot2_to_inc0 (L R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨24, Tape.mk' L (ListBlank.append [1, 1, 0] R)⟩ =
      some ⟨4, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L (((R.cons 0).cons 1).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) ((R.cons 0).cons 1)⟩ =
      some ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h3 : step riemann121 ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 0)⟩ =
      some ⟨4, Tape.mk' (((L.cons 1).cons 1).cons 0) R⟩ :=
    step_mk'_right_rh (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

theorem boot2_to_decnz0 (L R : ListBlank (Fin 2)) :
    nSteps riemann121 3 ⟨24, Tape.mk' L (ListBlank.append [1, 1, 1] R)⟩ =
      some ⟨31, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ := by
  have h1 : step riemann121 ⟨24, Tape.mk' L (((R.cons 1).cons 1).cons 1)⟩ =
      some ⟨26, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h2 : step riemann121 ⟨26, Tape.mk' (L.cons 1) ((R.cons 1).cons 1)⟩ =
      some ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have h3 : step riemann121 ⟨28, Tape.mk' ((L.cons 1).cons 1) (R.cons 1)⟩ =
      some ⟨31, Tape.mk' (((L.cons 1).cons 1).cons 1) R⟩ :=
    step_mk'_right_rh (by rfl) _ _
  exact step_nSteps h1 (step_nSteps h2 (step_one h3))

/-- `rhRunState 0` (`12`) scans left across `(pair10 m).reverse` in `2 * m` steps, landing back in
`12` (`4.run.0`) because every `0` in `pair10 m` is immediately preceded by `1`! -/
theorem rhRun_scan_pair10 (m : ℕ) (L R : ListBlank (Fin 2)) :
    nSteps riemann121 (2 * m) ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse L) R⟩ =
      some ⟨12, Tape.mkL L (ListBlank.append (pair10 m) R)⟩ := by
  induction m generalizing L R with
  | zero => rfl
  | succ m ih =>
    have hL : ListBlank.append (pair10 (m + 1)).reverse L =
        ((ListBlank.append (pair10 m).reverse L).cons 1).cons 0 := by
      rw [← pair10_snoc, List.reverse_append, ListBlank.append_assoc]
      rfl
    rw [hL]
    have h1 : step riemann121
        ⟨12, Tape.mkL (((ListBlank.append (pair10 m).reverse L).cons 1).cons 0) R⟩ =
        some ⟨14, Tape.mkL ((ListBlank.append (pair10 m).reverse L).cons 1) (R.cons 0)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have h2 : step riemann121
        ⟨14, Tape.mkL ((ListBlank.append (pair10 m).reverse L).cons 1) (R.cons 0)⟩ =
        some ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse L) ((R.cons 0).cons 1)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    have hrest := ih L ((R.cons 0).cons 1)
    have hcomb := step_nSteps h1 (step_nSteps h2 hrest)
    have hlen : 2 * m + 1 + 1 = 2 * (m + 1) := by omega
    have hR : ListBlank.append (pair10 m) ((R.cons 0).cons 1) =
        ListBlank.append (pair10 (m + 1)) R := by
      rw [← pair10_snoc, ListBlank.append_assoc]
      rfl
    rw [hlen, hR] at hcomb
    exact hcomb

/-- From `12` (`4.run.0`) with `pair10 m` (`1 ≤ m`) reversed on `default`, `riemann121` bounces off
`default` into `20 -> 22 -> 24` and scans right back to `State 24` (`0b.boot2.0`). -/
theorem rhRun_to_boot2 (m : ℕ) (hm : 1 ≤ m) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨12, Tape.mkL (ListBlank.append (pair10 m).reverse default) R⟩ =
      some ⟨24, Tape.mk' (ListBlank.append (pair10 m).reverse default) R⟩ := by
  have hscan := rhRun_scan_pair10 m default R
  have hbounce :=
    nSteps_rh_of_common (rhRun_bounce_default 0 (by decide) (ListBlank.append (pair10 m) R))
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hp : ListBlank.append (pair10 (m' + 1)) R =
      ((ListBlank.append (pair10 m') R).cons 0).cons 1 := rfl
  rw [hp] at hbounce
  have hs1 : step riemann121
      ⟨20, Tape.mk' default (((ListBlank.append (pair10 m') R).cons 0).cons 1)⟩ =
      some ⟨22, Tape.mk' (ListBlank.cons 1 default)
        ((ListBlank.append (pair10 m') R).cons 0)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs2 : step riemann121
      ⟨22, Tape.mk' (ListBlank.cons 1 default)
        ((ListBlank.append (pair10 m') R).cons 0)⟩ =
      some ⟨24, Tape.mk' ((ListBlank.cons 1 default).cons 0)
        (ListBlank.append (pair10 m') R)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hboot := boot2_scan_pairs m' ((ListBlank.cons 1 default).cons 0) R
  have hL_eq : ListBlank.append (pair10 m').reverse ((ListBlank.cons 1 default).cons 0) =
      ListBlank.append (pair10 (m' + 1)).reverse default := by
    simp [pair10, List.reverse_cons, ListBlank.append_assoc]
  rw [hL_eq] at hboot
  have htotal := nSteps_bind_eq hscan (nSteps_bind_eq hbounce
    (step_nSteps hs1 (step_nSteps hs2 hboot)))
  exact ⟨_, by omega, htotal⟩

theorem continue0_boot_pos (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s ⟨10, Tape.mkL (bootLeft m a) R⟩ =
      some ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a) R⟩ := by
  unfold bootLeft
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h1 : step riemann121 ⟨10, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R⟩ =
        some ⟨10, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ := step_mkL_left_rh (by rfl) _ _
    have h2 : step riemann121 ⟨10, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 0)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h3 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 0).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 0] R)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 0] R)
    have hinc := boot2_to_inc0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hinc)))⟩
  · have h1 : step riemann121 ⟨10, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R⟩ =
        some ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h2 : step riemann121 ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R.cons 1)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h3 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R.cons 1).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 1] R)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 1] R)
    have hdec := boot2_to_decnz0 L_m R
    exact ⟨_, by omega, step_nSteps h1 (step_nSteps h2 (step_nSteps h3 (nSteps_bind_eq hb hdec)))⟩

theorem boot_pass1_eval (m : ℕ) (hm : 1 ≤ m) (a : Fin 2) (r : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps riemann121 s
      ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a)
        (ListBlank.append (List.replicate (r + 3) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨if a = 0 then 4 else 31, Tape.mk' (bootLeft m a)
        ((ListBlank.append (encodeReg (r + 1)) R).cons 0 |>.cons 1)⟩ := by
  set q : Fin 121 := if a = 0 then 4 else 31
  have hq : rh121Trans q 0 = some (1, .right, 6) := by
    rcases fin2_cases a with rfl | rfl <;> rfl
  set L := bootLeft m a
  have hrep : List.replicate (r + 3) (0 : Fin 2) = 0 :: 0 :: List.replicate (r + 1) 0 := rfl
  rw [hrep, ListBlank.append, ListBlank.append]
  have h1 : step riemann121
      ⟨q, Tape.mk' L (((ListBlank.append (List.replicate (r + 1) 0)
        (ListBlank.append [1, 0] R)).cons 0).cons 0)⟩ =
      some ⟨6, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ :=
    step_mk'_right_rh hq _ _
  have h2 : step riemann121
      ⟨6, Tape.mk' (L.cons 1)
        ((ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R)).cons 0)⟩ =
      some ⟨8, Tape.mk' ((L.cons 1).cons 0)
        (ListBlank.append (List.replicate (r + 1) 0) (ListBlank.append [1, 0] R))⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hscan_r := nSteps_mk'_right_scan_rh (q := 8) (a := 0) (b := 1) (by rfl) (r + 1)
    ((L.cons 1).cons 0) (ListBlank.append [1, 0] R)
  have h3 : step riemann121
      ⟨8, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨10, Tape.mkL (ListBlank.append (List.replicate (r + 1) 1) ((L.cons 1).cons 0))
        (ListBlank.append [1, 0] R)⟩ :=
    step_mk'_left_rh (by rfl) _ (R.cons 0)
  rw [List.replicate_succ, ListBlank.append] at h3
  have h4 : step riemann121
      ⟨10, Tape.mkL ((ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0)).cons 1)
        (ListBlank.append [1, 0] R)⟩ =
      some ⟨12, Tape.mkL (ListBlank.append (List.replicate r 1) ((L.cons 1).cons 0))
        ((ListBlank.append [1, 0] R).cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have hscan_back := nSteps_mkL_left_scan_rh (q := 12) (a := 1) (b := 1) (by rfl) r
    ((L.cons 1).cons 0) ((ListBlank.append [1, 0] R).cons 1)
  have henc : ListBlank.append (List.replicate r 1) ((ListBlank.append [1, 0] R).cons 1) =
      ListBlank.append (encodeReg (r + 1)) R := by
    have h10 : ListBlank.append [1, 0] R = (R.cons 0).cons 1 := rfl
    rw [h10, append_replicate_cons, append_replicate_cons, ← append_encodeReg]
  rw [henc] at hscan_back
  set R_enc := ListBlank.append (encodeReg (r + 1)) R
  have h5 : step riemann121 ⟨12, Tape.mkL ((L.cons 1).cons 0) R_enc⟩ =
      some ⟨14, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  have h6 : step riemann121 ⟨14, Tape.mkL (L.cons 1) (R_enc.cons 0)⟩ =
      some ⟨12, Tape.mkL L ((R_enc.cons 0).cons 1)⟩ :=
    step_mkL_left_rh (by rfl) _ _
  set R_prep := (R_enc.cons 0).cons 1
  set L_m := ListBlank.append (pair10 m).reverse default
  rcases fin2_cases a with rfl | rfl
  · have h7 : step riemann121 ⟨12, Tape.mkL (((L_m.cons 1).cons 1).cons 0) R_prep⟩ =
        some ⟨14, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ := step_mkL_left_rh (by rfl) _ _
    have h8 : step riemann121 ⟨14, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 0)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h9 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 0).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 0] R_prep)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 0] R_prep)
    have hinc := boot2_to_inc0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hinc)))))))))))
    exact ⟨_, by omega, htotal⟩
  · have h7 : step riemann121 ⟨12, Tape.mkL (((L_m.cons 1).cons 1).cons 1) R_prep⟩ =
        some ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h8 : step riemann121 ⟨12, Tape.mkL ((L_m.cons 1).cons 1) (R_prep.cons 1)⟩ =
        some ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ := step_mkL_left_rh (by rfl) _ _
    have h9 : step riemann121 ⟨12, Tape.mkL (L_m.cons 1) ((R_prep.cons 1).cons 1)⟩ =
        some ⟨12, Tape.mkL L_m (ListBlank.append [1, 1, 1] R_prep)⟩ :=
      step_mkL_left_rh (by rfl) _ _
    obtain ⟨s_b, _, hb⟩ := rhRun_to_boot2 m hm (ListBlank.append [1, 1, 1] R_prep)
    have hdec := boot2_to_decnz0 L_m R_prep
    have htotal := step_nSteps h1 (step_nSteps h2 (nSteps_bind_eq hscan_r
      (step_nSteps h3 (step_nSteps h4 (nSteps_bind_eq hscan_back
        (step_nSteps h5 (step_nSteps h6 (step_nSteps h7 (step_nSteps h8
          (step_nSteps h9 (nSteps_bind_eq hb hdec)))))))))))
    exact ⟨_, by omega, htotal⟩

def rhBoot2CycleCfg (m i : ℕ) : Cfg 121 2 :=
  ⟨4, Tape.mk' (bootLeft m 0)
    (ListBlank.append (List.replicate (2 * i + 3) 0)
      (ListBlank.append [1, 0] (regsTape (List.replicate i 0))))⟩

theorem boot2_init_step (m : ℕ) (hm : 1 ≤ m) :
    ∃ s, nSteps riemann121 s
      ⟨4, Tape.mk' (ListBlank.append (pair10 (m + 1) ++ [1]).reverse default)
        (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some (rhBoot2CycleCfg m 1) := by
  set L_m := ListBlank.append (pair10 m).reverse default
  have hL : ListBlank.append (pair10 (m + 1) ++ [1]).reverse default =
      (((L_m.cons 1).cons 0).cons 1) := by
    rw [← pair10_snoc m, List.append_assoc, List.reverse_append, ListBlank.append_assoc]
    rfl
  rw [hL]
  set L₀ := ((L_m.cons 1).cons 0).cons 1
  have hdef : (default : ListBlank (Fin 2)) = ListBlank.cons 0 default := default_cons_zero.symm
  have hs1 : step riemann121 ⟨4, Tape.mk' L₀ (ListBlank.append [1, 0, 1, 1, 1, 1] default)⟩ =
      some ⟨7, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hs2 : step riemann121
      ⟨7, Tape.mk' (L₀.cons 0) (ListBlank.append [0, 1, 1, 1, 1] default)⟩ =
      some ⟨9, Tape.mk' ((L₀.cons 0).cons 0) (ListBlank.append (List.replicate 4 1) default)⟩ :=
    step_mk'_right_rh (by rfl) _ _
  have hscan := nSteps_mk'_right_scan_rh (q := 9) (a := 1) (b := 1) (by rfl) 4
    ((L₀.cons 0).cons 0) default
  set L_ones := ListBlank.append (List.replicate 4 1) ((L₀.cons 0).cons 0)
  have hs3 : step riemann121 ⟨9, Tape.mk' L_ones default⟩ =
      some ⟨11, Tape.mk' (ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0))
        default⟩ := by
    rw [append_encodeReg_reverse]
    have h := step_mk'_right_rh (q := 9) (q' := 11) (a := 0) (b := 0) (by rfl) L_ones default
    rwa [← hdef] at h
  set L_p := ListBlank.append (encodeReg 3).reverse ((L₀.cons 0).cons 0)
  have hs4 : step riemann121 ⟨11, Tape.mk' L_p default⟩ =
      some ⟨13, Tape.mk' (L_p.cons 1) default⟩ := by
    have h := step_mk'_right_rh (q := 11) (q' := 13) (a := 0) (b := 1) (by rfl) L_p default
    rwa [← hdef] at h
  have hs5 : step riemann121 ⟨13, Tape.mk' (L_p.cons 1) default⟩ =
      some ⟨15, Tape.mkL (L_p.cons 1) default⟩ := by
    have h := step_mk'_left_rh (q := 13) (q' := 15) (a := 0) (b := 0) (by rfl) (L_p.cons 1) default
    rwa [← hdef] at h
  have hs6 : step riemann121 ⟨15, Tape.mkL (L_p.cons 1) default⟩ =
      some ⟨15, Tape.mkL L_p (regsTape [0])⟩ := by
    have h := step_mkL_left_rh (q := 15) (q' := 15) (a := 1) (b := 1) (by rfl) L_p default
    have h0 : (default : ListBlank (Fin 2)).cons 1 = regsTape [0] := by
      rw [regsTape_cons, regsTape_nil, append_encodeReg, default_cons_zero]
      rfl
    rwa [h0] at h
  have hret := nSteps_rh_of_common (return0_scan_fence [3] L₀ (regsTape [0]))
  simp only [encodeRegs_cons, encodeRegs_nil, List.append_nil] at hret
  have hb0 := nSteps_rh_of_common (break0_step 1 (L_m.cons 1)
    ((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0 |>.cons 0))
  simp only [List.replicate, ListBlank.append] at hb0
  have hs7 : step riemann121
      ⟨21, Tape.mk' ((L_m.cons 1).cons 1)
        ((((ListBlank.append (encodeReg 3) (regsTape [0])).cons 0).cons 0).cons 0)⟩ =
      some ⟨21, Tape.mk' (bootLeft m 0)
        (ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg 3) (regsTape [0])))⟩ :=
    step_mk'_right_rh (by rfl) _ _
  obtain ⟨s_cl, _, hcl_c⟩ := cleanup_to_10 (bootLeft m 0) 2 3 (regsTape [0])
  have hcl := nSteps_rh_of_common hcl_c
  obtain ⟨s_cont, _, hcont⟩ := continue0_boot_pos m hm 0
    (ListBlank.append (List.replicate 5 0) (ListBlank.append [1, 0] (regsTape [0])))
  have htotal := step_nSteps hs1 (step_nSteps hs2 (nSteps_bind_eq hscan
    (step_nSteps hs3 (step_nSteps hs4 (step_nSteps hs5 (step_nSteps hs6
      (nSteps_bind_eq hret (nSteps_bind_eq hb0 (step_nSteps hs7 (nSteps_bind_eq hcl hcont))))))))))
  exact ⟨_, htotal⟩

theorem boot2_cycle_to_10 (m' i : ℕ) (hi : 1 ≤ i) :
    ∃ s, nSteps riemann121 s (rhBoot2CycleCfg (m' + 1) i) =
      some ⟨10, Tape.mkL (bootLeft m' 0)
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))⟩ := by
  have hm : 1 ≤ m' + 1 := by omega
  have hi_split : List.replicate i 0 = 0 :: List.replicate (i - 1) 0 := by
    conv_lhs => rw [show i = (i - 1) + 1 by omega, List.replicate_succ]
  obtain ⟨sA, _, hA⟩ := boot_pass1_eval (m' + 1) hm 0 (2 * i) (regsTape (List.replicate i 0))
  simp only [↓reduceIte, ← regsTape_cons] at hA
  rw [hi_split] at hA
  obtain ⟨sB1, _, hB1_c⟩ := stage3_inc_pass2 0 (by decide) (2 * i + 1)
    (0 :: List.replicate (i - 1) 0) (by simp) (bootLeft (m' + 1) 0)
  have hB1 := nSteps_rh_of_common hB1_c
  simp only [List.set_cons_zero, List.getElem_cons_zero, Nat.zero_add] at hB1
  have hB2 : step riemann121
      ⟨19, Tape.mkL (bootLeft (m' + 1) 0)
        ((regsTape ((2 * i + 1) :: 1 :: List.replicate (i - 1) 0)).cons 0 |>.cons 0)⟩ =
      some ⟨21, Tape.mk' (bootLeft (m' + 1) 1)
        (ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg (2 * i + 1))
            (regsTape (1 :: List.replicate (i - 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mkL_right_rh (by rfl) _ _
  obtain ⟨sB3, _, hB3_c⟩ := cleanup_to_10 (bootLeft (m' + 1) 1) 2 (2 * i + 1)
    (regsTape (1 :: List.replicate (i - 1) 0))
  have hB3 := nSteps_rh_of_common hB3_c
  obtain ⟨sB4, _, hB4⟩ := continue0_boot_pos (m' + 1) hm 1
    (ListBlank.append (List.replicate (2 + (2 * i + 1)) 0)
      (ListBlank.append [1, 0] (regsTape (1 :: List.replicate (i - 1) 0))))
  have haddB : 2 + (2 * i + 1) = 2 * i + 3 := by omega
  rw [haddB] at hB3 hB4
  obtain ⟨sC, _, hC⟩ := boot_pass1_eval (m' + 1) hm 1 (2 * i)
    (regsTape (1 :: List.replicate (i - 1) 0))
  have h10 : (1 : Fin 2) = 0 ↔ False := by decide
  simp only [h10, ↓reduceIte, ← regsTape_cons] at hB4 hC
  obtain ⟨sD1, _, hD1_c⟩ := stage3_decnz_pass2_pos 0 (by decide) (2 * i + 1)
    (1 :: List.replicate (i - 1) 0) (by simp) (by simp) (bootLeft (m' + 1) 1)
  have hD1 := nSteps_rh_of_common hD1_c
  simp only [List.getElem_cons_zero, Nat.sub_self, List.set_cons_zero] at hD1
  have hrep_snoc : 0 :: List.replicate (i - 1) 0 ++ [0] =
      List.replicate (i + 1) 0 := by
    rw [← hi_split, ← List.replicate_succ']
  rw [hrep_snoc] at hD1
  set L_m' := ListBlank.append (pair10 m').reverse default
  have hboot_split : bootLeft (m' + 1) 1 =
      ListBlank.append (List.replicate 3 1) ((L_m'.cons 1).cons 0) := by
    unfold bootLeft
    rw [← pair10_snoc m', List.reverse_append, ListBlank.append_assoc]
    rfl
  have hD2 := nSteps_rh_of_common (break0_step 3 (L_m'.cons 1)
    ((regsTape ((2 * i + 1) :: List.replicate (i + 1) 0)).cons 0 |>.cons 0))
  rw [← hboot_split] at hD2
  have hD3 : step riemann121
      ⟨21, Tape.mk' ((L_m'.cons 1).cons 1)
        (ListBlank.append (List.replicate 3 0)
          ((regsTape ((2 * i + 1) :: List.replicate (i + 1) 0)).cons 0 |>.cons 0))⟩ =
      some ⟨21, Tape.mk' (bootLeft m' 0)
        (ListBlank.append (List.replicate 4 0)
          (ListBlank.append (encodeReg (2 * i + 1)) (regsTape (List.replicate (i + 1) 0))))⟩ := by
    rw [regsTape_cons]
    exact step_mk'_right_rh (by rfl) _ _
  obtain ⟨sD4, _, hD4_c⟩ := cleanup_to_10 (bootLeft m' 0) 4 (2 * i + 1)
    (regsTape (List.replicate (i + 1) 0))
  have hD4 := nSteps_rh_of_common hD4_c
  have haddD : 4 + (2 * i + 1) = 2 * (i + 1) + 3 := by omega
  rw [haddD] at hD4
  unfold rhBoot2CycleCfg
  rw [hi_split]
  exact ⟨_, nSteps_bind_eq hA (nSteps_bind_eq hB1 (step_nSteps hB2
    (nSteps_bind_eq hB3 (nSteps_bind_eq hB4 (nSteps_bind_eq hC
      (nSteps_bind_eq hD1 (nSteps_bind_eq hD2 (step_nSteps hD3 hD4))))))))⟩

theorem boot2_loop (m i : ℕ) (hm : 1 ≤ m) (hi : 1 ≤ i) :
    ∃ s, nSteps riemann121 s (rhBoot2CycleCfg m i) =
      some (rhRootCfg (2 * (i + m) + 3) [] (List.replicate (i + m) 0)) := by
  induction m generalizing i with
  | zero => exfalso; omega
  | succ m' ih =>
    obtain ⟨s₁, h10⟩ := boot2_cycle_to_10 m' i hi
    cases m' with
    | zero =>
      rw [bootLeft_zero] at h10
      set R_end := ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
        (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0)))
      obtain ⟨s₂, _, hret⟩ := continue0_return [] (by decide) R_end
      simp only [ListBlank.append] at hret
      have hroot_eq : ⟨27, Tape.mk' rootLeft R_end⟩ =
          rhRootCfg (2 * (i + 1) + 3) [] (List.replicate (i + 1) 0) := by
        rw [rhRootCfg_default_eq, regsTape_cons]
        rfl
      rw [hroot_eq] at hret
      exact ⟨_, nSteps_bind_eq h10 hret⟩
    | succ m'' =>
      let m' := m'' + 1
      have hm'1 : 1 ≤ m' := by omega
      obtain ⟨s₂, _, hcont⟩ := continue0_boot_pos m' hm'1 0
        (ListBlank.append (List.replicate (2 * (i + 1) + 3) 0)
          (ListBlank.append [1, 0] (regsTape (List.replicate (i + 1) 0))))
      obtain ⟨s₃, hrest⟩ := ih (i + 1) hm'1 (by omega)
      have hadd : i + 1 + m' = i + (m' + 1) := by omega
      rw [hadd] at hrest
      exact ⟨_, nSteps_bind_eq h10 (nSteps_bind_eq hcont hrest)⟩

/-- Complete bootstrap theorem: starting from `init = ⟨0, default⟩`, `riemann121` reaches
`main.0` (`State 27`) at `rhRootCfg 3821 [] (List.replicate 1909 0)` (i.e. `3821` pad zeros
followed by `[1, 0]`, `[0, 0, 0, 0, 0]`, and `regsTape (List.replicate 1904 0)`). -/
theorem boot_to_root :
    ∃ s, nSteps riemann121 s init =
      some (rhRootCfg 3821 [] (List.replicate 1909 0) default) := by
  obtain ⟨s₁, hb1⟩ := boot1_eval
  obtain ⟨s₂, hb2_init⟩ := boot2_init_step 1908 (by decide)
  obtain ⟨s₃, hb2_loop⟩ := boot2_loop 1908 1 (by decide) (by decide)
  exact ⟨s₁ + (s₂ + s₃), nSteps_bind_eq hb1 (nSteps_bind_eq hb2_init hb2_loop)⟩

/-- Equivalent 5-register form of `boot_to_root`: reaches `main.0` (`State 27`)
with `[0, 0, 0, 0, 0]` and trailing register tape `regsTape (List.replicate 1904 0)`. -/
theorem boot_reaches_main0 :
    ∃ s, nSteps riemann121 s init =
      some (rhRootCfg 3821 [] [0, 0, 0, 0, 0] (regsTape (List.replicate 1904 0))) := by
  obtain ⟨s, hs⟩ := boot_to_root
  have heq : rhRootCfg 3821 [] (List.replicate 1909 0) default =
      rhRootCfg 3821 [] [0, 0, 0, 0, 0] (regsTape (List.replicate 1904 0)) := by
    have hr : List.replicate 1909 0 = [0, 0, 0, 0, 0] ++ List.replicate 1904 0 := rfl
    unfold rhRootCfg
    rw [hr, encodeRegs_append]
    simp only [List.append_assoc, ListBlank.append_assoc]
    rfl
  rw [heq] at hs
  exact ⟨s, hs⟩

end ConjectureMachines.Riemann120.Backend


namespace ConjectureMachines.Riemann120.Layer2

open Turing (Dir)
open StateTransition ConjectureMachines.Riemann120

set_option maxRecDepth 200000

/-- Exact 10 register leaf states `3.<reg>.{inc,decnz}` of `canon121`. -/
def isLeafState (q : Fin 121) : Bool :=
  match q.val with
  | 4 | 31 | 44 | 47 | 99 | 71 | 36 | 46 | 70 | 73 => true
  | _ => false

/-- Exact 63 internal decision-DAG nodes `N0..N62` of `canon121`. -/
def isInternalNode (q : Fin 121) : Bool :=
  match q.val with
  | 27 | 29 | 30 | 32 | 33 | 34 | 38 | 39 | 40 | 41 | 45 | 48 | 49 | 50
  | 54 | 55 | 58 | 59 | 60 | 61 | 62 | 65 | 66 | 67 | 68 | 72 | 74 | 75
  | 76 | 77 | 80 | 81 | 82 | 83 | 84 | 86 | 88 | 89 | 90 | 93 | 94 | 95
  | 96 | 98 | 101 | 102 | 103 | 104 | 105 | 107 | 108 | 109 | 110 | 111
  | 112 | 113 | 114 | 115 | 116 | 117 | 118 | 119 | 120 => true
  | _ => false

theorem isLeafState_false_of_isInternalNode (q : Fin 121) :
    isInternalNode q = true → isLeafState q = false := by
  revert q; decide

/-- Register index `r ∈ {0..4}` (`0=m, 1=j, 2=x, 3=f, 4=v`) for each leaf state. -/
def leafReg (q : Fin 121) : ℕ :=
  match q.val with
  | 4 | 31 => 0
  | 44 | 47 => 1
  | 99 | 71 => 2
  | 36 | 46 => 3
  | 70 | 73 => 4
  | _ => 0

theorem leafReg_lt_5 (q : Fin 121) : leafReg q < 5 := by
  revert q; decide

/-- Whether leaf state `q` is a register increment (`true`) or `decnz` (`false`). -/
def isLeafInc (q : Fin 121) : Bool :=
  match q.val with
  | 4 | 44 | 99 | 36 | 70 => true
  | _ => false

/-! ## Section 2: Call-Stack Bit Manipulation & Decision-Tree Dispatcher -/

/-- Removes leading `0`s from a bit list (used on reversed stacks to remove trailing `0`s). -/
def dropLeadingZeros : List (Fin 2) → List (Fin 2)
  | [] => []
  | b :: xs => if b == 0 then dropLeadingZeros xs else b :: xs

/-- Removes trailing `0`s from a call-stack bit list `bits`. -/
def trimZeros (bits : List (Fin 2)) : List (Fin 2) :=
  (dropLeadingZeros bits.reverse).reverse

/-- Pads or truncates `bits` with trailing `0`s to exact length `pos`. -/
def padTo (bits : List (Fin 2)) (pos : ℕ) : List (Fin 2) :=
  (bits ++ List.replicate (pos - bits.length) 0).take pos

/-- Reversed-stack scanner for `6.break.k`. -/
def popBreakRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | 0, b :: rest => if b == 0 then 1 :: rest else popBreakRev 0 rest
  | k + 1, b :: rest => if b == 0 then popBreakRev k rest else popBreakRev (k + 1) rest

/-- Reversed-stack scanner for `6.continue.k`. -/
def popContinueRev : ℕ → List (Fin 2) → List (Fin 2)
  | _, [] => []
  | 0, b :: rest => if b == 1 then 1 :: rest else popContinueRev 0 rest
  | k + 1, b :: rest => if b == 1 then popContinueRev k rest else popContinueRev (k + 1) rest

/-- Updates call stack `bits` on `6.break.k` at head position `pos`. -/
def applyBreak (bits : List (Fin 2)) (pos : ℕ) (k : ℕ) : List (Fin 2) :=
  (popBreakRev k (padTo bits pos).reverse).reverse

/-- Updates call stack `bits` on `6.continue.k` at head position `pos`. -/
def applyContinue (bits : List (Fin 2)) (pos : ℕ) (k : ℕ) : List (Fin 2) :=
  (popContinueRev k (padTo bits pos).reverse).reverse

/-- Return stack when breaking out of a subroutine at call-stack prefix `P`. -/
def retStack (P : List (Fin 2)) : List (Fin 2) :=
  (popBreakRev 0 P.reverse).reverse

/-- Walks internal DAG nodes from `q` along bit sequence `bits`. -/
def walkInternal (q : Fin 121) : List (Fin 2) → Option (Fin 121)
  | [] => if isInternalNode q then some q else none
  | b :: bs =>
    if isInternalNode q then
      match rh121Trans q b with
      | some (w, .right, q') =>
        if w == b && isInternalNode q' then walkInternal q' bs else none
      | _ => none
    else none

/-- Abstract instruction decoded at `State 27` (`main.0`). -/
inductive RhInstr where
  | halt
  | jump (stack' : List (Fin 2))
  | inc (r : ℕ) (stack_succ : List (Fin 2))
  | decnz (r : ℕ) (stack_succ stack_fail : List (Fin 2))
  deriving DecidableEq, Repr

/-- Outcome of walking the call-stack DAG from state `q`. -/
inductive TreeOutcome where
  | halt (q : Fin 121) (walked rem : List (Fin 2))
  | jumpLeft (q' : Fin 121) (walked rem' : List (Fin 2))
  | regLeaf (q' : Fin 121) (walked rem' : List (Fin 2))
  | outOfFuel
  deriving DecidableEq, Repr

/-- Walks the decision DAG starting at state `q` with traversed prefix `walked` and suffix `rem`. -/
def walkTape (q : Fin 121) (walked : List (Fin 2)) : List (Fin 2) → TreeOutcome
  | [] => .outOfFuel
  | b :: rem' =>
    match rh121Trans q b with
    | none => .halt q walked (b :: rem')
    | some (w, d, q') =>
      match d with
      | .left =>
        if w == 0 then .jumpLeft q' walked rem' else .outOfFuel
      | .right =>
        if w == b then
          if isLeafState q' then
            .regLeaf q' (walked ++ [b]) rem'
          else
            walkTape q' (walked ++ [b]) rem'
        else
          .outOfFuel

/-- Decodes a `TreeOutcome` into an abstract register-machine instruction `RhInstr`. -/
def outcomeToInstr (bits : List (Fin 2)) : TreeOutcome → RhInstr
  | .halt _ _ _ => .halt
  | .jumpLeft q' walked _ =>
    match q'.val with
    | 19 => .jump (applyBreak bits walked.length 0)
    | 91 => .jump (applyBreak bits walked.length 1)
    | 10 => .jump (applyContinue bits walked.length 0)
    | 37 => .jump (applyContinue bits walked.length 1)
    | 97 => .jump (applyContinue bits walked.length 2)
    | _ => .halt
  | .regLeaf q' walked _ =>
    if isLeafInc q' then
      .inc (leafReg q') (applyBreak bits walked.length 0)
    else
      .decnz (leafReg q') (applyBreak bits walked.length 0)
        (applyBreak bits walked.length 1)
  | .outOfFuel => .halt

/-- Computable call-stack dispatcher rooted at `State 27` (`main.0`). -/
def evalStack (bits : List (Fin 2)) : RhInstr :=
  outcomeToInstr bits (walkTape 27 [] (bits ++ List.replicate 18 0))

/-! ## Section 3: 5-Register Machine & Reachable Control Word Certificate (`decide`) -/

/-- Configuration of the 5-register abstract machine (`regs = [m, j, x, f, v]`). -/
structure RhRegCfg where
  stack : List (Fin 2)
  regs : List ℕ
  deriving DecidableEq, Repr

/-- Initial configuration at first entry to `main.0` (`State 27`): `stack = []`, `regs = 0^5`. -/
def rhRegInit : RhRegCfg := ⟨[], [0, 0, 0, 0, 0]⟩

/-- One step of the 5-register machine for `riemann121`. -/
def rhRegStep (c : RhRegCfg) : Option RhRegCfg :=
  match evalStack c.stack with
  | .halt => none
  | .jump stack' => some ⟨stack', c.regs⟩
  | .inc r stack_succ =>
    some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r stack_succ stack_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨stack_fail, c.regs⟩
    else
      some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 - 1)⟩

/-- `n`-step execution of `rhRegStep`. -/
def rhRegNSteps : ℕ → RhRegCfg → Option RhRegCfg
  | 0, c => some c
  | n + 1, c => (rhRegStep c).bind (rhRegNSteps n)

/-- Halting predicate for the 5-register abstract machine of `riemann121`. -/
def RhRegHalts : Prop :=
  (StateTransition.eval rhRegStep rhRegInit).Dom

theorem mem_eval_rhRegStep_iff_rhRegNSteps {c₀ ch : RhRegCfg} :
    ch ∈ StateTransition.eval rhRegStep c₀ ↔
      ∃ n, rhRegNSteps n c₀ = some ch ∧ rhRegStep ch = none := by
  rw [mem_eval']
  constructor
  · rintro ⟨hreach, hnone⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl, hnone⟩
    | head hstep _ ih =>
      obtain ⟨n, hn, _⟩ := ih
      change rhRegStep _ = some _ at hstep
      exact ⟨n + 1, by simp [rhRegNSteps, hstep, hn], hnone⟩
  · rintro ⟨n, hn, hnone⟩
    refine ⟨?_, hnone⟩
    induction n generalizing c₀ with
    | zero => injection hn with h; subst h; exact Relation.ReflTransGen.refl
    | succ n ih =>
      unfold rhRegNSteps at hn
      rcases hs : rhRegStep c₀ with _ | c₁
      · simp [hs] at hn
      · rw [hs, Option.bind_some] at hn
        exact Relation.ReflTransGen.head hs (ih hn)

theorem rhRegHalts_iff_exists_rhRegNSteps :
    RhRegHalts ↔ ∃ n c, rhRegNSteps n rhRegInit = some c ∧ rhRegStep c = none := by
  unfold RhRegHalts
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨n, hn, hnone⟩ := mem_eval_rhRegStep_iff_rhRegNSteps.mp hc
    exact ⟨n, c, hn, hnone⟩
  · rintro ⟨n, c, hn, hnone⟩
    exact ⟨c, mem_eval_rhRegStep_iff_rhRegNSteps.mpr ⟨n, hn, hnone⟩⟩

/-- Boolean test for absence of four consecutive `0` bits (`0000`) in a bit list. -/
def hasNoFourZeros : List (Fin 2) → Bool
  | 0 :: 0 :: 0 :: 0 :: _ => false
  | _ :: rest => hasNoFourZeros rest
  | [] => true


/-- Successor call stacks produced by one step of `evalStack`. -/
def instrNextStacks (ins : RhInstr) : List (List (Fin 2)) :=
  match ins with
  | .halt => []
  | .jump s' => [s']
  | .inc _ s_succ => [s_succ]
  | .decnz _ s_succ s_fail => [s_succ, s_fail]

/-- Breadth-first closure generating all reachable call stacks from `[]`. -/
def reachableStacksAux : ℕ → List (List (Fin 2)) → List (List (Fin 2))
  | 0, acc => acc
  | fuel + 1, acc =>
    let nexts := acc.flatMap fun s => instrNextStacks (evalStack s)
    let added := nexts.filter fun s => !acc.contains s
    if added.isEmpty then acc else reachableStacksAux fuel (acc ++ added)

/-- Exact finite set (size 121) of all call stacks reachable from `[]` under `evalStack`. -/
def allValidStacks : List (List (Fin 2)) :=
  reachableStacksAux 30 [[]]

/-- Membership predicate for reachable call stacks of `riemann121`. -/
def isValidStack (bits : List (Fin 2)) : Bool :=
  allValidStacks.contains bits

theorem isValidStack_nil : isValidStack [] = true := by decide

theorem isValidStack_closed_and_noFourZeros :
    ∀ bits ∈ allValidStacks,
      bits.length ≤ 18 ∧
      hasNoFourZeros ([1, 1, 0] ++ bits ++ [1, 0]) = true ∧
      ∀ s' ∈ instrNextStacks (evalStack bits), isValidStack s' = true := by
  decide

theorem rhRegStep_preserves_isValidStack {c c' : RhRegCfg}
    (h : isValidStack c.stack = true) (hstep : rhRegStep c = some c') :
    isValidStack c'.stack = true := by
  have hmem : c.stack ∈ allValidStacks := List.contains_iff_mem.mp h
  have hcl := (isValidStack_closed_and_noFourZeros c.stack hmem).2.2
  unfold rhRegStep at hstep
  rcases hev : evalStack c.stack with _ | s' | ⟨r, s_succ⟩ | ⟨r, s_succ, s_fail⟩
  · simp [hev] at hstep
  · simp only [hev, Option.some.injEq] at hstep
    subst hstep
    exact hcl s' (by simp [instrNextStacks, hev])
  · simp only [hev, Option.some.injEq] at hstep
    subst hstep
    exact hcl s_succ (by simp [instrNextStacks, hev])
  · simp only [hev] at hstep
    by_cases hz : (c.regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      exact hcl s_fail (by simp [instrNextStacks, hev])
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hstep
      subst hstep
      exact hcl s_succ (by simp [instrNextStacks, hev])


end ConjectureMachines.Riemann120.Layer2

namespace ConjectureMachines.Riemann120

open Turing (Dir)
open StateTransition ConjectureMachines
open ConjectureMachines.Semantics.Riemann
open Backend
open Layer2
  (RhInstr TreeOutcome walkTape outcomeToInstr evalStack
   padTo popBreakRev popContinueRev applyBreak applyContinue
   isLeafState isLeafInc leafReg leafReg_lt_5
   allValidStacks isValidStack isValidStack_nil rhRegStep_preserves_isValidStack
   RhRegCfg rhRegInit rhRegStep rhRegNSteps RhRegHalts
   mem_eval_rhRegStep_iff_rhRegNSteps)
open ConjectureMachines.Semantics.Riemann.Layer1
  (nSteps nSteps_zero nSteps_succ nSteps_add nSteps_bind_eq step_nSteps step_one
   nSteps_eval_dom nSteps_of_halt mem_eval_iff_nSteps fin2_cases
   default_cons_zero append_replicate_zero_default
   Tape.mkL append_replicate_cons append_reverse_cons
   encodeReg encodeRegs encodeRegs_cons encodeRegs_nil encodeRegs_append encodeReg_length
   regsTape regsTape_cons regsTape_append
   list_take_cons_drop list_take_set_drop)
open ConjectureMachines.Semantics.Zf.Layer1
  (rootLeft stackLeft stackLeft_append_singleton)

set_option maxRecDepth 200000

def tm (isEd : Bool) : Machine 121 2 :=
  if isEd then edited121 else riemann121

def tmTrans (isEd : Bool) : Fin 121 → Fin 2 → Option (Fin 2 × Dir × Fin 121) :=
  if isEd then ed121Trans else rh121Trans

theorem tm_transition_eq (isEd : Bool) (q : Fin 121) (a : Fin 2) :
    (tm isEd).transition q a = tmTrans isEd q a := by
  cases isEd <;> rfl

set_option maxHeartbeats 400000 in
-- Finite state-table decision procedure.
theorem tm_common_sub (isEd : Bool) (q : Fin 121) (a : Fin 2)
    (t : Fin 2 × Dir × Fin 121) :
    commonTrans q a = some t → (tm isEd).transition q a = some t := by
  revert isEd q a t; decide

theorem step_tm_of_common (isEd : Bool) {c c' : Cfg 121 2}
    (hs : step common121 c = some c') : step (tm isEd) c = some c' := by
  obtain ⟨q, T⟩ := c
  dsimp only [step] at hs ⊢
  change (commonTrans q T.head).map _ = some c' at hs
  rcases htr : commonTrans q T.head with _ | t
  · rw [htr] at hs; cases hs
  · rw [tm_common_sub isEd q T.head t htr]
    rw [htr] at hs; exact hs

theorem nSteps_tm_of_common (isEd : Bool) {n : ℕ} {c c' : Cfg 121 2}
    (hn : nSteps common121 n c = some c') : nSteps (tm isEd) n c = some c' := by
  induction n generalizing c with
  | zero => exact hn
  | succ n ih =>
    rw [nSteps_succ, Option.bind_eq_some_iff] at hn ⊢
    obtain ⟨c₁, hs, hrest⟩ := hn
    exact ⟨c₁, step_tm_of_common isEd hs, ih hrest⟩

def stepPrefix (tr : Fin 121 → Fin 2 → Option (Fin 2 × Dir × Fin 121))
    (q : Fin 121) (L R : List (Fin 2)) : Option (Fin 121 × List (Fin 2) × List (Fin 2)) :=
  match R with
  | [] => none
  | h :: R' =>
    match tr q h with
    | none => none
    | some (w, .right, q') => some (q', w :: L, R')
    | some (w, .left, q') =>
      match L with
      | [] => none
      | l :: L' => some (q', L', l :: w :: R')

def runPrefix (tr : Fin 121 → Fin 2 → Option (Fin 2 × Dir × Fin 121)) :
    ℕ → Fin 121 → List (Fin 2) → List (Fin 2) → Option (Fin 121 × List (Fin 2) × List (Fin 2))
  | 0, q, L, R => some (q, L, R)
  | n + 1, q, L, R =>
    match stepPrefix tr q L R with
    | none => none
    | some (q', L', R') => runPrefix tr n q' L' R'

theorem stepPrefix_sound (isEd : Bool) {q q' : Fin 121} {L R L' R' : List (Fin 2)}
    (hs : stepPrefix (tmTrans isEd) q L R = some (q', L', R'))
    (L₀ R₀ : ListBlank (Fin 2)) :
    step (tm isEd) ⟨q, Tape.mk' (ListBlank.append L L₀) (ListBlank.append R R₀)⟩ =
      some ⟨q', Tape.mk' (ListBlank.append L' L₀) (ListBlank.append R' R₀)⟩ := by
  cases R with
  | nil => simp [stepPrefix] at hs
  | cons h R_rest =>
    dsimp only [stepPrefix] at hs
    rcases htr : tmTrans isEd q h with _ | ⟨w, d, q_next⟩
    · rw [htr] at hs; cases hs
    · rw [htr] at hs
      cases d with
      | left =>
        cases L with
        | nil => simp at hs
        | cons l L_rest =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          rcases hs with ⟨rfl, rfl, rfl⟩
          simp [step, tm_transition_eq, htr, Tape.mk', Tape.write, Tape.move, ListBlank.append]
      | right =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hs
        rcases hs with ⟨rfl, rfl, rfl⟩
        simp [step, tm_transition_eq, htr, Tape.mk', Tape.write, Tape.move, ListBlank.append]

theorem runPrefix_sound (isEd : Bool) {n : ℕ} {q q' : Fin 121} {L R L' R' : List (Fin 2)}
    (hr : runPrefix (tmTrans isEd) n q L R = some (q', L', R'))
    (L₀ R₀ : ListBlank (Fin 2)) :
    nSteps (tm isEd) n ⟨q, Tape.mk' (ListBlank.append L L₀) (ListBlank.append R R₀)⟩ =
      some ⟨q', Tape.mk' (ListBlank.append L' L₀) (ListBlank.append R' R₀)⟩ := by
  induction n generalizing q L R with
  | zero =>
    simp only [runPrefix, Option.some.injEq, Prod.mk.injEq] at hr
    rcases hr with ⟨rfl, rfl, rfl⟩
    rfl
  | succ n ih =>
    dsimp only [runPrefix] at hr
    rcases hs : stepPrefix (tmTrans isEd) q L R with _ | ⟨q₁, L₁, R₁⟩
    · rw [hs] at hr; cases hr
    · rw [hs] at hr
      exact step_nSteps (stepPrefix_sound isEd hs L₀ R₀) (ih hr)

def rootPrefixOf (isEd : Bool) : List (Fin 2) :=
  if isEd then [1, 0, 0, 0, 0] else [0, 1, 1, 0, 0, 0, 0]

def rootHeaderOf (isEd : Bool) (b : Fin 2) : List (Fin 2) :=
  if isEd then [1] else [1, 1, b]

def rootLeftOf (isEd : Bool) : ListBlank (Fin 2) :=
  if isEd then ListBlank.cons 1 default else rootLeft

def stackLeftOf (isEd : Bool) (w : List (Fin 2)) : ListBlank (Fin 2) :=
  ListBlank.append w.reverse (rootLeftOf isEd)

theorem append_rootPrefixOf_default (isEd : Bool) :
    ListBlank.append (rootPrefixOf isEd) default = rootLeftOf isEd := by
  cases isEd <;> simp [rootPrefixOf, rootLeftOf, rootLeft, ListBlank.append, default_cons_zero]

theorem append_reverse_rootPrefixOf_default (isEd : Bool) (w : List (Fin 2)) :
    ListBlank.append (w.reverse ++ rootPrefixOf isEd) default = stackLeftOf isEd w := by
  rw [ListBlank.append_assoc, append_rootPrefixOf_default]
  rfl

theorem stackLeftOf_append (isEd : Bool) (w₁ w₂ : List (Fin 2)) :
    stackLeftOf isEd (w₁ ++ w₂) = ListBlank.append w₂.reverse (stackLeftOf isEd w₁) := by
  unfold stackLeftOf
  rw [List.reverse_append, ListBlank.append_assoc]

theorem stackLeftOf_append_singleton (isEd : Bool) (w : List (Fin 2)) (a : Fin 2) :
    stackLeftOf isEd (w ++ [a]) = (stackLeftOf isEd w).cons a := by
  rw [stackLeftOf_append]
  rfl

theorem stackLeftOf_eq_append (isEd : Bool) (w : List (Fin 2)) :
    stackLeftOf isEd w = ListBlank.append (rootHeaderOf isEd 0 ++ w).reverse default := by
  cases isEd <;>
    simp [stackLeftOf, rootLeftOf, rootHeaderOf, rootLeft, ListBlank.append_assoc, ListBlank.append]

theorem noFourZeros_rootHeaderOf (isEd : Bool) (w : List (Fin 2))
    (hw : NoFourZeros ([1, 1, 0] ++ w) = true) :
    NoFourZeros (rootHeaderOf isEd 0 ++ w) = true := by
  cases isEd
  · exact hw
  · dsimp only [rootHeaderOf, List.cons_append, List.nil_append, NoFourZeros] at hw ⊢
    rcases w with _ | ⟨x₁, _ | ⟨x₂, _ | ⟨x₃, w'⟩⟩⟩
    · rfl
    · rcases fin2_cases x₁ with rfl | rfl <;> rfl
    · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;> rfl
    · rcases fin2_cases x₁ with rfl | rfl <;> rcases fin2_cases x₂ with rfl | rfl <;>
        rcases fin2_cases x₃ with rfl | rfl <;> first | exact hw | cases hw

theorem root_scan_to_main_tm (isEd : Bool) (b : Fin 2) (R : ListBlank (Fin 2)) :
    nSteps (tm isEd) (if isEd then 1 else 3)
      ⟨20, Tape.mk' default (ListBlank.append (rootHeaderOf isEd b) R)⟩ =
      some ⟨27, Tape.mk' (rootLeftOf isEd) R⟩ := by
  cases isEd
  · have h : runPrefix (tmTrans false) 3 20 [] [1, 1, b] = some (27, [0, 1, 1], []) := by
      revert b; decide
    simpa [rootHeaderOf, rootLeftOf, rootLeft, ListBlank.append] using
      runPrefix_sound false h default R
  · have h : runPrefix (tmTrans true) 1 20 [] [1] = some (27, [1], []) := by decide
    simpa [rootHeaderOf, rootLeftOf, ListBlank.append] using
      runPrefix_sound true h default R

theorem continue0_reaches_main0_tm (isEd : Bool) (b : Fin 2) (rest : List (Fin 2))
    (hok : NoFourZeros (rootHeaderOf isEd b ++ rest) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨10, Tape.mkL (ListBlank.append (rootHeaderOf isEd b ++ rest).reverse default) R⟩ =
      some ⟨27, Tape.mk' (rootLeftOf isEd) (ListBlank.append rest R)⟩ := by
  have hone : (1 : Fin 2) ∈ (rootHeaderOf isEd b ++ rest).reverse := by
    rw [List.mem_reverse]
    cases isEd <;> simp [rootHeaderOf]
  have hrev_ok : NoFourZeros (rootHeaderOf isEd b ++ rest).reverse = true := by
    rwa [NoFourZeros_reverse]
  obtain ⟨z', hz', s₁, _, hscan⟩ :=
    continue0_scan_rev (rootHeaderOf isEd b ++ rest).reverse hone hrev_ok R
  rw [List.reverse_reverse] at hscan
  have hbounce := rhRun_bounce_default z' hz' (ListBlank.append (rootHeaderOf isEd b ++ rest) R)
  have hroot := root_scan_to_main_tm isEd b (ListBlank.append rest R)
  rw [← ListBlank.append_assoc] at hroot
  have hpos : 1 ≤ s₁ + ((2 * (3 - z') + 1) + (if isEd then 1 else 3)) := by
    cases isEd <;> omega
  exact ⟨_, hpos, nSteps_bind_eq (nSteps_tm_of_common isEd hscan)
    (nSteps_bind_eq (nSteps_tm_of_common isEd hbounce) hroot)⟩

theorem continue0_return_tm (isEd : Bool) (w : List (Fin 2))
    (hw : NoFourZeros ([1, 1, 0] ++ w) = true) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s ⟨10, Tape.mkL (stackLeftOf isEd w) R⟩ =
      some ⟨27, Tape.mk' (rootLeftOf isEd) (ListBlank.append w R)⟩ := by
  rw [stackLeftOf_eq_append]
  exact continue0_reaches_main0_tm isEd 0 w (noFourZeros_rootHeaderOf isEd w hw) R

theorem prep_pass1_eval_tm (isEd : Bool) (stack : List (Fin 2))
    (hstack : NoFourZeros ([1, 1, 0] ++ stack) = true) (p : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨6, Tape.mk' ((stackLeftOf isEd stack).cons 1)
        (ListBlank.append (List.replicate (p + 1) 0) (ListBlank.append [1, 0] R))⟩ =
      some ⟨27, Tape.mk' (rootLeftOf isEd)
        (ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R)⟩ := by
  have h10 := nSteps_tm_of_common isEd (prep_pass1_to_10 (stackLeftOf isEd stack) p R)
  have hL_eq : ListBlank.append (List.replicate p 1) (((stackLeftOf isEd stack).cons 1).cons 0) =
      stackLeftOf isEd (stack ++ [1, 0] ++ List.replicate p 1) := by
    rw [stackLeftOf_append, stackLeftOf_append, List.reverse_replicate]
    rfl
  rw [hL_eq] at h10
  have hw_ok : NoFourZeros ([1, 1, 0] ++ (stack ++ [1, 0] ++ List.replicate p 1)) = true := by
    have ha : [1, 1, 0] ++ (stack ++ [1, 0] ++ List.replicate p 1) =
        (([1, 1, 0] ++ stack) ++ [1, 0]) ++ List.replicate p 1 := by
      simp [List.append_assoc]
    rw [ha, NoFourZeros_append_replicate_one, NoFourZeros_snoc_one_bit]
    exact hstack
  obtain ⟨s_ret, hs1, hret⟩ := continue0_return_tm isEd (stack ++ [1, 0] ++ List.replicate p 1)
    hw_ok (ListBlank.append [1, 0] R)
  have hR_eq : ListBlank.append (stack ++ [1, 0] ++ List.replicate p 1)
      (ListBlank.append [1, 0] R) =
      ListBlank.append (stack ++ [1, 0] ++ encodeReg p) R := by
    simp only [encodeReg, List.replicate_succ', List.append_assoc, ListBlank.append_assoc]
    rfl
  rw [hR_eq] at hret
  exact ⟨_, by omega, nSteps_bind_eq h10 hret⟩

theorem cleanup_to_main_tm (isEd : Bool) (stack' : List (Fin 2))
    (hstack' : NoFourZeros ([1, 1, 0] ++ stack') = true) (z m : ℕ) (R : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨21, Tape.mk' (stackLeftOf isEd stack')
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) R))⟩ =
      some ⟨27, Tape.mk' (rootLeftOf isEd)
        (ListBlank.append stack'
          (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R)))⟩ := by
  obtain ⟨s₁, hs1, h10⟩ := cleanup_to_10 (stackLeftOf isEd stack') z m R
  obtain ⟨s₂, hs2, hret⟩ := continue0_return_tm isEd stack' hstack'
    (ListBlank.append (List.replicate (z + m) 0) (ListBlank.append [1, 0] R))
  exact ⟨s₁ + s₂, by omega, nSteps_bind_eq (nSteps_tm_of_common isEd h10) hret⟩

def mapStack (bits : List (Fin 2)) : List (Fin 2) :=
  match bits with
  | 1 :: 1 :: 1 :: 1 :: 0 :: rest => 1 :: 1 :: 1 :: 1 :: 0 :: 0 :: rest
  | [1, 1, 1, 1, 1] => [1, 1, 1, 1, 0, 1]
  | 1 :: 1 :: 1 :: 1 :: 1 :: 0 :: rest => 1 :: 1 :: 1 :: 1 :: 0 :: 1 :: rest
  | 1 :: 1 :: 1 :: 1 :: 1 :: 1 :: rest => 1 :: 1 :: 1 :: 1 :: 1 :: rest
  | _ => bits

def stackOf (isEd : Bool) (bits : List (Fin 2)) : List (Fin 2) :=
  if isEd then mapStack bits else bits

@[simp]
theorem stackOf_nil (isEd : Bool) : stackOf isEd [] = [] := by
  cases isEd <;> rfl

def rhRootCfgRaw (isEd : Bool) (padTotal : ℕ) (stack : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  ⟨27, Tape.mk' (rootLeftOf isEd)
    (ListBlank.append
      (stack ++ List.replicate (padTotal - stack.length) 0 ++ [1, 0] ++ encodeRegs regs)
      extra)⟩

theorem rhRootCfgRaw_default_eq (isEd : Bool) (padTotal : ℕ) (stack : List (Fin 2))
    (regs : List ℕ) :
    rhRootCfgRaw isEd padTotal stack regs default =
      ⟨27, Tape.mk' (rootLeftOf isEd)
        (ListBlank.append stack
          (ListBlank.append (List.replicate (padTotal - stack.length) 0)
            (regsTape (0 :: regs))))⟩ := by
  unfold rhRootCfgRaw
  simp only [List.append_assoc, ListBlank.append_assoc]
  rfl

def rhRootCfgOf (isEd : Bool) (padTotal : ℕ) (bits : List (Fin 2)) (regs : List ℕ)
    (extra : ListBlank (Fin 2) := default) : Cfg 121 2 :=
  rhRootCfgRaw isEd padTotal (stackOf isEd bits) regs extra

theorem rhRootCfgOf_default_eq (isEd : Bool) (padTotal : ℕ) (bits : List (Fin 2)) (regs : List ℕ) :
    rhRootCfgOf isEd padTotal bits regs default =
      ⟨27, Tape.mk' (rootLeftOf isEd)
        (ListBlank.append (stackOf isEd bits)
          (ListBlank.append (List.replicate (padTotal - (stackOf isEd bits).length) 0)
            (regsTape (0 :: regs))))⟩ :=
  rhRootCfgRaw_default_eq isEd padTotal (stackOf isEd bits) regs

theorem step_mk'_none_tm (isEd : Bool) {q : Fin 121} {a : Fin 2}
    (h : tmTrans isEd q a = none) (L R : ListBlank (Fin 2)) :
    step (tm isEd) ⟨q, Tape.mk' L (R.cons a)⟩ = none := by
  simp [step, tm_transition_eq, h, Tape.mk']

theorem popBreakRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popBreakRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => cases k <;> simp [popBreakRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => simp [popBreakRev]
      | succ k' => have := ih k'; simp [popBreakRev]; omega
    · cases k with
      | zero => have := ih 0; simp [popBreakRev]; omega
      | succ k' => have := ih (k' + 1); simp [popBreakRev]; omega

theorem popContinueRev_length_le (k : ℕ) (rev : List (Fin 2)) :
    (popContinueRev k rev).length ≤ rev.length := by
  induction rev generalizing k with
  | nil => cases k <;> simp [popContinueRev]
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · cases k with
      | zero => have := ih 0; simp [popContinueRev]; omega
      | succ k' => have := ih (k' + 1); simp [popContinueRev]; omega
    · cases k with
      | zero => simp [popContinueRev]
      | succ k' => have := ih k'; simp [popContinueRev]; omega

theorem popBreakRev_of_count_eq (k : ℕ) (rev : List (Fin 2)) (h : rev.count 0 = k) :
    popBreakRev k rev = [] ∧ popBreakRev k (rev ++ [0]) = [1] := by
  induction rev generalizing k with
  | nil =>
    simp only [List.count_nil] at h
    subst h
    exact ⟨rfl, rfl⟩
  | cons b xs ih =>
    rcases fin2_cases b with rfl | rfl
    · rw [List.count_cons_self] at h
      subst h
      simpa [popBreakRev] using ih (xs.count 0) rfl
    · have h' : xs.count 0 = k := by simpa using h
      cases k with
      | zero => simpa [popBreakRev] using ih 0 h'
      | succ k' => simpa [popBreakRev] using ih (k' + 1) h'

theorem break0_scan_to_21 (rev : List (Fin 2))
    (h0 : 1 ≤ rev.count 0) (L R : ListBlank (Fin 2)) :
    let w' := (popBreakRev 0 rev).reverse
    ∃ s, 1 ≤ s ∧ nSteps common121 s
      ⟨19, Tape.mkL (ListBlank.append rev L) R⟩ =
      some ⟨21, Tape.mk' (ListBlank.append w'.reverse L)
        (ListBlank.append (List.replicate (rev.length - w'.length) 0) R)⟩ := by
  induction rev generalizing R with
  | nil => simp at h0
  | cons b xs ih =>
    intro w'
    rcases fin2_cases b with rfl | rfl
    · have hstep : step common121
          ⟨19, Tape.mkL ((ListBlank.append xs L).cons 0) R⟩ =
          some ⟨21, Tape.mk' ((ListBlank.append xs L).cons 1) R⟩ :=
        step_mkL_right (by rfl) _ _
      have hw'_rev : w'.reverse = 1 :: xs := by simp [w', popBreakRev]
      have hsub : (0 :: xs).length - w'.length = 0 := by
        have : w'.length = (0 :: xs).length := by
          rw [← List.length_reverse, hw'_rev]; rfl
        omega
      refine ⟨1, le_refl 1, ?_⟩
      rw [hw'_rev, hsub, List.replicate_zero, ListBlank.append, ListBlank.append]
      exact step_one hstep
    · have hstep : step common121
          ⟨19, Tape.mkL ((ListBlank.append xs L).cons 1) R⟩ =
          some ⟨19, Tape.mkL (ListBlank.append xs L) (R.cons 0)⟩ :=
        step_mkL_left (by rfl) _ _
      have h0' : 1 ≤ xs.count 0 := by simpa using h0
      obtain ⟨s, hs1, hs⟩ := ih h0' (R.cons 0)
      have hw'_eq : (popBreakRev 0 xs).reverse = w' := by simp [w', popBreakRev]
      have hlen_le : w'.length ≤ xs.length := by
        rw [← hw'_eq, List.length_reverse]
        exact popBreakRev_length_le 0 xs
      have hsub : (1 :: xs).length - w'.length = (xs.length - w'.length) + 1 := by
        simp; omega
      rw [hw'_eq, append_replicate_cons, ← hsub] at hs
      exact ⟨s + 1, by omega, step_nSteps hstep hs⟩

theorem append_replicate_zeros_eq (d z : ℕ) (R : ListBlank (Fin 2)) :
    ListBlank.append (List.replicate d (0 : Fin 2)) (ListBlank.append (List.replicate z 0) R) =
      ListBlank.append (List.replicate (d + z) 0) R := by
  rw [← ListBlank.append_assoc, ← List.replicate_add]

theorem break0_cleanup_to_root_tm (isEd : Bool) (padTotal : ℕ)
    (walked : List (Fin 2))
    (hw_le : walked.length ≤ padTotal)
    (z m : ℕ) (hz_eq : z + m = padTotal - walked.length)
    (hno4 : NoFourZeros ([1, 1, 0] ++ (popBreakRev 0 walked.reverse).reverse) = true)
    (regs_all : List ℕ) :
    let w' := (popBreakRev 0 walked.reverse).reverse
    ∃ padTotal', padTotal ≤ padTotal' ∧ ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨19, Tape.mkL (stackLeftOf isEd walked)
        (ListBlank.append (List.replicate z 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ =
      some (rhRootCfgRaw isEd padTotal' w' regs_all default) := by
  intro w'
  by_cases hlt : 1 ≤ walked.count 0
  · have hlt_rev : 1 ≤ walked.reverse.count 0 := by rw [List.count_reverse]; exact hlt
    obtain ⟨s₁, hs₁_pos, hs₁_c⟩ := break0_scan_to_21 walked.reverse hlt_rev (rootLeftOf isEd)
      (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) (regsTape regs_all)))
    have hs₁ := nSteps_tm_of_common isEd hs₁_c
    rw [List.length_reverse, append_replicate_zeros_eq] at hs₁
    change nSteps (tm isEd) s₁ _ =
      some ⟨21, Tape.mk' (stackLeftOf isEd w')
        (ListBlank.append (List.replicate (walked.length - w'.length + z) 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ at hs₁
    obtain ⟨s₂, hs₂_pos, hcl⟩ := cleanup_to_main_tm isEd w' hno4
      (walked.length - w'.length + z) m (regsTape regs_all)
    have hlen_le : w'.length ≤ walked.length := by
      have := popBreakRev_length_le 0 walked.reverse
      simpa [w'] using this
    have hpad_eq : walked.length - w'.length + z + m = padTotal - w'.length := by omega
    rw [hpad_eq] at hcl
    have hroot_eq : ⟨27, Tape.mk' (rootLeftOf isEd)
        (ListBlank.append w'
          (ListBlank.append (List.replicate (padTotal - w'.length) 0)
            (ListBlank.append [1, 0] (regsTape regs_all))))⟩ =
        rhRootCfgRaw isEd padTotal w' regs_all default := by
      rw [rhRootCfgRaw_default_eq, regsTape_cons]; rfl
    rw [hroot_eq] at hcl
    exact ⟨padTotal, le_refl padTotal, s₁ + s₂, by omega, nSteps_bind_eq hs₁ hcl⟩
  · have heq : walked.reverse.count 0 = 0 := by rw [List.count_reverse]; omega
    obtain ⟨hw'_nil, hpop_0⟩ := popBreakRev_of_count_eq 0 walked.reverse heq
    have hw' : w' = [] := by simp [w', hw'_nil]
    cases isEd
    · have hstack_eq : stackLeftOf false walked =
          ListBlank.append (walked.reverse ++ [0])
            ((default : ListBlank (Fin 2)).cons 1 |>.cons 1) := by
        unfold stackLeftOf rootLeftOf rootLeft
        rw [ListBlank.append_assoc]; rfl
      have hcnt_0 : 1 ≤ (walked.reverse ++ [0]).count 0 := by
        rw [List.count_append, heq]
        decide
      obtain ⟨s₁, hs₁_pos, hs₁_c⟩ := break0_scan_to_21 (walked.reverse ++ [0]) hcnt_0
        ((default : ListBlank (Fin 2)).cons 1 |>.cons 1)
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) (regsTape regs_all)))
      have hs₁ := nSteps_tm_of_common false hs₁_c
      rw [← hstack_eq] at hs₁
      have hrev_1 : (popBreakRev 0 (walked.reverse ++ [0])).reverse.reverse = [1] := by
        rw [List.reverse_reverse, hpop_0]
      have hsub_len : (walked.reverse ++ [0]).length -
          (popBreakRev 0 (walked.reverse ++ [0])).reverse.length = walked.length := by
        rw [List.length_reverse, hpop_0, List.length_append, List.length_reverse]; simp
      rw [hrev_1, hsub_len, append_replicate_zeros_eq] at hs₁
      change nSteps (tm false) s₁ _ =
        some ⟨21, Tape.mk' (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
          (ListBlank.append (List.replicate (walked.length + z) 0)
            (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ at hs₁
      obtain ⟨s₂, hs₂_pos, hcl_c⟩ := cleanup_to_10
        (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1)
        (walked.length + z) m (regsTape regs_all)
      have hcl := nSteps_tm_of_common false hcl_c
      obtain ⟨s₃, hs₃_pos, hret⟩ := continue0_reaches_main0_tm false 1 [] (by decide)
        (ListBlank.append (List.replicate (walked.length + z + m) 0)
          (ListBlank.append [1, 0] (regsTape regs_all)))
      have hL111 : ListBlank.append (rootHeaderOf false 1 ++ [] : List (Fin 2)).reverse default =
          (((default : ListBlank (Fin 2)).cons 1 |>.cons 1).cons 1) := rfl
      rw [hL111, ListBlank.append] at hret
      have hpad_eq : walked.length + z + m = padTotal - ([] : List (Fin 2)).length := by
        simp; omega
      rw [hpad_eq] at hcl hret
      have hroot_eq : ⟨27, Tape.mk' (rootLeftOf false)
          (ListBlank.append (List.replicate (padTotal - ([] : List (Fin 2)).length) 0)
            (ListBlank.append [1, 0] (regsTape regs_all)))⟩ =
          rhRootCfgRaw false padTotal [] regs_all default := by
        rw [rhRootCfgRaw_default_eq, regsTape_cons]; rfl
      rw [hroot_eq] at hret
      rw [hw']
      exact ⟨padTotal, le_refl padTotal, s₁ + (s₂ + s₃), by omega,
        nSteps_bind_eq hs₁ (nSteps_bind_eq hcl hret)⟩
    · have heq1 : (walked.reverse ++ [1]).count 0 = 0 := by
        rw [List.count_append, heq]; rfl
      obtain ⟨_, hpop1_0⟩ := popBreakRev_of_count_eq 0 (walked.reverse ++ [1]) heq1
      have hstack_eq : stackLeftOf true walked =
          ListBlank.append ((walked.reverse ++ [1]) ++ [0]) default := by
        unfold stackLeftOf rootLeftOf
        rw [ListBlank.append_assoc, ListBlank.append_assoc]
        simp [ListBlank.append, default_cons_zero]
      have hcnt_0 : 1 ≤ ((walked.reverse ++ [1]) ++ [0]).count 0 := by
        rw [List.count_append, heq1]
        decide
      obtain ⟨s₁, hs₁_pos, hs₁_c⟩ := break0_scan_to_21 ((walked.reverse ++ [1]) ++ [0]) hcnt_0
        default
        (ListBlank.append (List.replicate z 0) (ListBlank.append (encodeReg m) (regsTape regs_all)))
      have hs₁ := nSteps_tm_of_common true hs₁_c
      rw [← hstack_eq] at hs₁
      have hrev_1 : (popBreakRev 0 ((walked.reverse ++ [1]) ++ [0])).reverse.reverse = [1] := by
        rw [List.reverse_reverse, hpop1_0]
      have hsub_len : ((walked.reverse ++ [1]) ++ [0]).length -
          (popBreakRev 0 ((walked.reverse ++ [1]) ++ [0])).reverse.length = walked.length + 1 := by
        rw [List.length_reverse, hpop1_0, List.length_append, List.length_append,
          List.length_reverse]
        simp
      rw [hrev_1, hsub_len, append_replicate_zeros_eq] at hs₁
      change nSteps (tm true) s₁ _ =
        some ⟨21, Tape.mk' (stackLeftOf true [])
          (ListBlank.append (List.replicate (walked.length + 1 + z) 0)
            (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ at hs₁
      obtain ⟨s₂, hs₂_pos, hcl⟩ := cleanup_to_main_tm true [] (by decide)
        (walked.length + 1 + z) m (regsTape regs_all)
      have hpad_eq : walked.length + 1 + z + m = (padTotal + 1) - ([] : List (Fin 2)).length := by
        simp; omega
      rw [hpad_eq] at hcl
      have hroot_eq : ⟨27, Tape.mk' (rootLeftOf true)
          (ListBlank.append []
            (ListBlank.append (List.replicate ((padTotal + 1) - ([] : List (Fin 2)).length) 0)
              (ListBlank.append [1, 0] (regsTape regs_all))))⟩ =
          rhRootCfgRaw true (padTotal + 1) [] regs_all default := by
        rw [rhRootCfgRaw_default_eq, regsTape_cons]; rfl
      rw [hroot_eq] at hcl
      rw [hw']
      exact ⟨padTotal + 1, by omega, s₁ + s₂, by omega, nSteps_bind_eq hs₁ hcl⟩

def walkTapeOf (isEd : Bool) (q : Fin 121) (walked : List (Fin 2)) : List (Fin 2) → TreeOutcome
  | [] => .outOfFuel
  | b :: rem' =>
    match tmTrans isEd q b with
    | none => .halt q walked (b :: rem')
    | some (w, d, q') =>
      match d with
      | .left =>
        if w == 0 then .jumpLeft q' walked rem' else .outOfFuel
      | .right =>
        if w == b then
          if isLeafState q' then
            .regLeaf q' (walked ++ [b]) rem'
          else
            walkTapeOf isEd q' (walked ++ [b]) rem'
        else
          .outOfFuel

def evalStackOf (isEd : Bool) (bits : List (Fin 2)) : RhInstr :=
  if isEd && bits == [1, 1, 1, 1, 1, 0, 1, 1] then .jump [1, 1, 1, 1]
  else evalStack bits

def rhRegStepOf (isEd : Bool) (c : RhRegCfg) : Option RhRegCfg :=
  match evalStackOf isEd c.stack with
  | .halt => none
  | .jump stack' => some ⟨stack', c.regs⟩
  | .inc r stack_succ =>
    some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 + 1)⟩
  | .decnz r stack_succ stack_fail =>
    if c.regs.getD r 0 == 0 then
      some ⟨stack_fail, c.regs⟩
    else
      some ⟨stack_succ, c.regs.set r (c.regs.getD r 0 - 1)⟩

def rhRegNStepsOf (isEd : Bool) : ℕ → RhRegCfg → Option RhRegCfg
  | 0, c => some c
  | n + 1, c => (rhRegStepOf isEd c).bind (rhRegNStepsOf isEd n)

def RhRegHaltsOf (isEd : Bool) : Prop :=
  (StateTransition.eval (rhRegStepOf isEd) rhRegInit).Dom

theorem mem_eval_rhRegStepOf_iff_rhRegNStepsOf (isEd : Bool) {c₀ ch : RhRegCfg} :
    ch ∈ StateTransition.eval (rhRegStepOf isEd) c₀ ↔
      ∃ n, rhRegNStepsOf isEd n c₀ = some ch ∧ rhRegStepOf isEd ch = none := by
  rw [mem_eval']
  constructor
  · rintro ⟨hreach, hnone⟩
    induction hreach using Relation.ReflTransGen.head_induction_on with
    | refl => exact ⟨0, rfl, hnone⟩
    | head hstep _ ih =>
      obtain ⟨n, hn, _⟩ := ih
      change rhRegStepOf isEd _ = some _ at hstep
      exact ⟨n + 1, by simp [rhRegNStepsOf, hstep, hn], hnone⟩
  · rintro ⟨n, hn, hnone⟩
    refine ⟨?_, hnone⟩
    induction n generalizing c₀ with
    | zero => injection hn with h; subst h; exact Relation.ReflTransGen.refl
    | succ n ih =>
      unfold rhRegNStepsOf at hn
      rcases hs : rhRegStepOf isEd c₀ with _ | c₁
      · simp [hs] at hn
      · rw [hs, Option.bind_some] at hn
        exact Relation.ReflTransGen.head hs (ih hn)

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem isValidStack_closed_of (isEd : Bool) :
    ∀ bits ∈ allValidStacks,
      ∀ s' ∈ Riemann120.Layer2.instrNextStacks (evalStackOf isEd bits),
        isValidStack s' = true := by
  revert isEd; decide

theorem rhRegStepOf_valid (isEd : Bool) {bits bits' : List (Fin 2)} {regs regs' : List ℕ}
    (hv : isValidStack bits = true)
    (hstep : rhRegStepOf isEd ⟨bits, regs⟩ = some ⟨bits', regs'⟩) :
    isValidStack bits' = true := by
  have hmem : bits ∈ allValidStacks := List.contains_iff_mem.mp hv
  have hcl := isValidStack_closed_of isEd bits hmem
  unfold rhRegStepOf at hstep
  rcases hev : evalStackOf isEd bits with _ | s' | ⟨r, s_succ⟩ | ⟨r, s_succ, s_fail⟩
  · simp [hev] at hstep
  · simp only [hev, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact hcl _ (by simp [Riemann120.Layer2.instrNextStacks, hev])
  · simp only [hev, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
    rcases hstep with ⟨rfl, rfl⟩
    exact hcl _ (by simp [Riemann120.Layer2.instrNextStacks, hev])
  · simp only [hev] at hstep
    by_cases hz : (regs.getD r 0 == 0) = true
    · simp only [hz, ↓reduceIte, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      exact hcl _ (by simp [Riemann120.Layer2.instrNextStacks, hev])
    · simp only [hz, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, RhRegCfg.mk.injEq] at hstep
      rcases hstep with ⟨rfl, rfl⟩
      exact hcl _ (by simp [Riemann120.Layer2.instrNextStacks, hev])

def validStackSimCheck (isEd : Bool) (bits : List (Fin 2)) : Bool :=
  let tr := tmTrans isEd
  let rPfx := rootPrefixOf isEd
  let s := stackOf isEd bits
  let pfx := s ++ List.replicate (18 - s.length) 0
  let ev := evalStackOf isEd bits
  (s.length ≤ 18) &&
  match walkTapeOf isEd 27 [] pfx with
  | .halt q_h walked_h rem_h =>
    (1 ≤ walked_h.length) &&
    (ev == .halt) &&
    match rem_h with
    | [] => false
    | b_h :: rem_h' =>
      (runPrefix tr walked_h.length 27 rPfx pfx ==
        some (q_h, walked_h.reverse ++ rPfx, b_h :: rem_h')) &&
      (tr q_h b_h == none)
  | .jumpLeft q' walked rem' =>
    match ev with
    | .jump bits' =>
      let w' := stackOf isEd bits'
      (walked.length ≤ 16) &&
      (walked.length + (1 + rem'.length) == 18) &&
      (0 :: rem' == List.replicate (1 + rem'.length) 0) &&
      (w'.length ≤ walked.length) &&
      if (q' == 19 || q' == 91) && !isEd then
        (runPrefix tr (2 * walked.length - w'.length + 2) 27 rPfx pfx ==
          some (21, w'.reverse ++ rPfx,
            List.replicate (walked.length - w'.length) 0 ++ (0 :: rem'))) &&
        NoFourZeros ([1, 1, 0] ++ w')
      else
        let n_jmp :=
          if isEd then
            if q' == 87 && (walked.reverse.drop 1).head? == some 1 then 2 * walked.length + 12
            else 2 * walked.length + 10
          else 2 * walked.length + 14
        (runPrefix tr n_jmp 27 rPfx pfx ==
          some (27, rPfx, w' ++ List.replicate (walked.length - w'.length) 0 ++ (0 :: rem')))
    | _ => false
  | .regLeaf q' walked_l rem_l =>
    let r := leafReg q'
    let w'_b0 := (popBreakRev 0 walked_l.reverse).reverse
    let w'_b1 := (popBreakRev 1 walked_l.reverse).reverse
    (1 ≤ walked_l.length) &&
    (walked_l.length ≤ 16) &&
    (walked_l.length + rem_l.length == 18) &&
    (rem_l == List.replicate rem_l.length 0) &&
    (commonTrans q' 0 == some (1, .right, 6)) &&
    (runPrefix tr walked_l.length 27 rPfx pfx ==
      some (q', walked_l.reverse ++ rPfx, rem_l)) &&
    (runPrefix tr walked_l.length 27 rPfx walked_l ==
      some (q', walked_l.reverse ++ rPfx, [])) &&
    NoFourZeros ([1, 1, 0] ++ walked_l) &&
    NoFourZeros ([1, 1, 0] ++ w'_b0) &&
    (if isLeafInc q' then
      (q' == regIncStage3 r) &&
      match ev with
      | .inc r_ev bits_succ =>
        (r_ev == r) &&
        (w'_b0 == stackOf isEd bits_succ)
      | _ => false
     else
      (q' == regDecnzStage3 r) &&
      (walked_l.dropLast ++ [0] == walked_l) &&
      NoFourZeros ([1, 1, 0] ++ w'_b1) &&
      match ev with
      | .decnz r_ev bits_succ bits_fail =>
        (r_ev == r) &&
        (w'_b0 == stackOf isEd bits_succ) &&
        (w'_b1 == stackOf isEd bits_fail)
      | _ => false)
  | .outOfFuel => false

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem validStackSimCheck_all (isEd : Bool) :
    ∀ bits ∈ allValidStacks, validStackSimCheck isEd bits = true := by
  revert isEd; decide

def initPadOf (isEd : Bool) : ℕ :=
  if isEd then 21 else 3821

theorem initPadOf_ge_18 (isEd : Bool) : 18 ≤ initPadOf isEd := by
  cases isEd <;> decide

theorem rhRootCfgRaw_regsTape_eq (isEd : Bool) (padTotal : ℕ) (stack : List (Fin 2))
    (regs extra : List ℕ) :
    rhRootCfgRaw isEd padTotal stack regs (regsTape extra) =
      rhRootCfgRaw isEd padTotal stack (regs ++ extra) default := by
  unfold rhRootCfgRaw regsTape
  rw [encodeRegs_append]
  simp only [List.append_assoc, ListBlank.append_assoc]

theorem rhRootCfgOf_regsTape_eq (isEd : Bool) (padTotal : ℕ) (bits : List (Fin 2))
    (regs extra : List ℕ) :
    rhRootCfgOf isEd padTotal bits regs (regsTape extra) =
      rhRootCfgOf isEd padTotal bits (regs ++ extra) default :=
  rhRootCfgRaw_regsTape_eq isEd padTotal (stackOf isEd bits) regs extra

theorem rhRootCfgOf_eq_prefix (isEd : Bool) {padTotal : ℕ} (hpad : 18 ≤ padTotal)
    {bits : List (Fin 2)} (hbits : (stackOf isEd bits).length ≤ 18) (regs_all : List ℕ) :
    rhRootCfgOf isEd padTotal bits regs_all default =
      ⟨27, Tape.mk' (ListBlank.append (rootPrefixOf isEd) default)
        (ListBlank.append (stackOf isEd bits ++ List.replicate (18 - (stackOf isEd bits).length) 0)
          (ListBlank.append (List.replicate (padTotal - 18) 0)
            (regsTape (0 :: regs_all))))⟩ := by
  rw [rhRootCfgOf_default_eq, append_rootPrefixOf_default]
  have hsub : padTotal - (stackOf isEd bits).length =
      (18 - (stackOf isEd bits).length) + (padTotal - 18) := by omega
  rw [hsub, List.replicate_add]
  simp only [ListBlank.append_assoc]

theorem regs_append_getElem {regs extra : List ℕ} {r : ℕ}
    (hlen : regs.length = 5) (hr : r < 5) :
    (regs ++ extra)[r]'(by simp [hlen]; omega) = regs.getD r 0 := by
  have hr' : r < regs.length := by omega
  rw [List.getElem_append_left hr']
  simp [List.getD_eq_getElem?_getD, hr']

theorem regs_append_set {regs extra : List ℕ} {r v : ℕ}
    (hlen : regs.length = 5) (hr : r < 5) :
    (regs ++ extra).set r v = regs.set r v ++ extra :=
  List.set_append_left (i := r) (x := v) (by omega)

theorem rhRegStepOf_of_evalStackOf (isEd : Bool) {bits : List (Fin 2)} {regs : List ℕ} :
    rhRegStepOf isEd ⟨bits, regs⟩ =
      match evalStackOf isEd bits with
      | .halt => none
      | .jump stack' => some ⟨stack', regs⟩
      | .inc r stack_succ => some ⟨stack_succ, regs.set r (regs.getD r 0 + 1)⟩
      | .decnz r stack_succ stack_fail =>
        if regs.getD r 0 == 0 then some ⟨stack_fail, regs⟩
        else some ⟨stack_succ, regs.set r (regs.getD r 0 - 1)⟩ := rfl

theorem step_mkL_left_tm (isEd : Bool) {q q' : Fin 121} {a b : Fin 2}
    (h : (tm isEd).transition q a = some (b, .left, q')) (L R : ListBlank (Fin 2)) :
    step (tm isEd) ⟨q, Tape.mkL (L.cons a) R⟩ =
      some ⟨q', Tape.mkL L (R.cons b)⟩ := by
  simp [step, h, Tape.mkL, Tape.write, Tape.move]

theorem step_78_to_19_tm (isEd : Bool) (L R : ListBlank (Fin 2)) :
    nSteps (tm isEd) 2 ⟨78, Tape.mkL ((L.cons 0).cons 0) R⟩ =
      some ⟨19, Tape.mkL L ((R.cons 0).cons 0)⟩ := by
  cases isEd
  · exact step_nSteps (step_mkL_left_tm false rfl (L.cons 0) R)
      (step_one (step_mkL_left_tm false rfl L (R.cons 0)))
  · exact step_nSteps (step_mkL_left_tm true rfl (L.cons 0) R)
      (step_one (step_mkL_left_tm true rfl L (R.cons 0)))

theorem decnz_zero_cleanup_to_root (isEd : Bool) (padTotal : ℕ)
    (walked : List (Fin 2))
    (hw_last : walked.dropLast ++ [0] = walked)
    (hw_le : walked.length ≤ padTotal)
    (m : ℕ) (hm_eq : 2 + m = padTotal - walked.length)
    (hno4 : NoFourZeros ([1, 1, 0] ++ (popBreakRev 1 walked.reverse).reverse) = true)
    (regs_all : List ℕ) :
    ∃ padTotal', padTotal ≤ padTotal' ∧ ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨78, Tape.mkL ((stackLeftOf isEd walked).cons 0)
        ((ListBlank.append (encodeReg m) (regsTape regs_all)).cons 0)⟩ =
      some (rhRootCfgRaw isEd padTotal' (popBreakRev 1 walked.reverse).reverse regs_all
        default) := by
  have hstack : stackLeftOf isEd walked = (stackLeftOf isEd walked.dropLast).cons 0 := by
    conv_lhs => rw [← hw_last]
    exact stackLeftOf_append_singleton isEd walked.dropLast 0
  have hstep78 : nSteps (tm isEd) 2
      ⟨78, Tape.mkL ((stackLeftOf isEd walked).cons 0)
        ((ListBlank.append (encodeReg m) (regsTape regs_all)).cons 0)⟩ =
      some ⟨19, Tape.mkL (stackLeftOf isEd walked.dropLast)
        (ListBlank.append (List.replicate 3 0)
          (ListBlank.append (encodeReg m) (regsTape regs_all)))⟩ := by
    rw [hstack]
    exact step_78_to_19_tm isEd (stackLeftOf isEd walked.dropLast)
      ((ListBlank.append (encodeReg m) (regsTape regs_all)).cons 0)
  have hw_len : walked.dropLast.length + 1 = walked.length := by
    have h := congrArg List.length hw_last
    simp only [List.length_append, List.length_singleton] at h
    exact h
  have hw'_eq : (popBreakRev 0 walked.dropLast.reverse).reverse =
      (popBreakRev 1 walked.reverse).reverse := by
    have hrev : walked.reverse = 0 :: walked.dropLast.reverse := by
      conv_lhs => rw [← hw_last]
      simp
    simp [hrev, popBreakRev]
  rw [← hw'_eq] at hno4
  obtain ⟨padTotal', hpad_le, s, hs1, hcl⟩ :=
    break0_cleanup_to_root_tm isEd padTotal walked.dropLast
    (by omega) 3 m (by omega) hno4 regs_all
  change nSteps (tm isEd) s _ =
    some (rhRootCfgRaw isEd padTotal' (popBreakRev 0 walked.dropLast.reverse).reverse regs_all
      default) at hcl
  rw [hw'_eq] at hcl
  exact ⟨padTotal', hpad_le, 2 + s, by omega, nSteps_bind_eq hstep78 hcl⟩

theorem rhRegIncrChain_step_01 (isEd : Bool) (m : ℕ) (hm : m < 5) :
    runPrefix (tmTrans isEd) 2 (rhRegIncrChain (m + 1)) [] [0, 1] =
      some (rhRegIncrChain m, [1, 0], []) := by
  revert isEd m hm; decide

theorem rhRegIncrChain_scan_pref_tm (isEd : Bool) (pref : List ℕ) (hpref : pref.length ≤ 4)
    (L R : ListBlank (Fin 2)) :
    nSteps (tm isEd) ((encodeRegs pref).length + 1)
      ⟨rhRegIncrChain (pref.length + 1),
        Tape.mk' L ((ListBlank.append (encodeRegs pref) R).cons 0)⟩ =
      some ⟨11, Tape.mk' (ListBlank.append (encodeRegs pref).reverse (L.cons 0)) R⟩ := by
  induction pref generalizing L with
  | nil =>
    exact step_one (step_tm_of_common isEd (step_mk'_right (by rfl) L R))
  | cons r rs ih =>
    simp only [List.length_cons] at hpref ⊢
    have hrs_lt : rs.length + 1 < 5 := by omega
    have hrs_le : rs.length ≤ 4 := by omega
    have h01 : nSteps (tm isEd) 2
        ⟨rhRegIncrChain (rs.length + 1 + 1),
          Tape.mk' L ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0)⟩ =
        some ⟨rhRegIncrChain (rs.length + 1),
          Tape.mk' ((L.cons 0).cons 1)
            (ListBlank.append (List.replicate r 1)
              ((ListBlank.append (encodeRegs rs) R).cons 0))⟩ := by
      have h := runPrefix_sound isEd (rhRegIncrChain_step_01 isEd (rs.length + 1) hrs_lt) L
        (ListBlank.append (List.replicate r 1) ((ListBlank.append (encodeRegs rs) R).cons 0))
      have hR_in : ListBlank.append ([0, 1] : List (Fin 2))
          (ListBlank.append (List.replicate r 1) ((ListBlank.append (encodeRegs rs) R).cons 0)) =
          ((ListBlank.append (encodeRegs (r :: rs)) R).cons 0) := by
        rw [encodeRegs_cons, ListBlank.append_assoc,
          Layer1.append_encodeReg, List.replicate_succ, ListBlank.append]
        rfl
      rw [ListBlank.append, hR_in] at h
      exact h
    have hones := nSteps_tm_of_common isEd
      (nSteps_mk'_right_scan (rhRegIncrChain_trans_one (rs.length + 1) (by omega))
        r ((L.cons 0).cons 1) ((ListBlank.append (encodeRegs rs) R).cons 0))
    rw [append_replicate_cons] at hones
    have hrest := ih hrs_le (ListBlank.append (List.replicate (r + 1) 1) (L.cons 0))
    rw [← Layer1.append_encodeReg_reverse, ← ListBlank.append_assoc,
      ← List.reverse_append, ← encodeRegs_cons] at hrest
    have hcomb := nSteps_bind_eq h01 (nSteps_bind_eq hones hrest)
    have hlen : 2 + (r + ((encodeRegs rs).length + 1)) =
        (encodeRegs (r :: rs)).length + 1 := by
      simp [encodeRegs_cons]; omega
    rw [hlen] at hcomb
    exact hcomb

theorem regIncStage3_enter_chain_3 (isEd : Bool) (k : ℕ) (hk : k < 5)
    (hnot : (isEd && k == 4) = false) :
    runPrefix (tmTrans isEd) 3 (regIncStage3 k) [] [1, 0, 1] =
      some (rhRegIncrChain (k + 1), [1, 0, 0], []) := by
  rcases k with _ | _ | _ | _ | _ | k
  · cases isEd <;> rfl
  · cases isEd <;> rfl
  · cases isEd <;> rfl
  · cases isEd <;> rfl
  · cases isEd
    · rfl
    · cases hnot
  · omega

theorem regIncStage3_enter_chain_70 :
    runPrefix (tmTrans true) 4 (regIncStage3 4) [] [1, 0, 1, 1] =
      some (rhRegIncrChain 5, [1, 0, 0, 1], []) := by
  decide

theorem stage3_inc_from_chain (isEd : Bool) (k : ℕ) (hk5 : k < 5) (m : ℕ)
    (regs : List ℕ) (hk : k < regs.length) (L_base : ListBlank (Fin 2)) :
    ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
      ⟨rhRegIncrChain (k + 1),
        Tape.mk' (((L_base.cons 0).cons 0).cons 1)
          (ListBlank.append (List.replicate m 1)
            ((ListBlank.append (encodeRegs (regs.take k))
              (regsTape (regs[k] :: regs.drop (k + 1)))).cons 0))⟩ =
      some ⟨19, Tape.mkL L_base
        ((regsTape (m :: regs.set k (regs[k] + 1))).cons 0 |>.cons 0)⟩ := by
  set pref := m :: regs.take k
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hle : k ≤ regs.length := Nat.le_of_lt hk
  have htake_len : (regs.take k).length = k := List.length_take_of_le hle
  have hp_ones := nSteps_tm_of_common isEd
    (nSteps_mk'_right_scan (rhRegIncrChain_trans_one (k + 1) (by omega))
      m (((L_base.cons 0).cons 0).cons 1)
      ((ListBlank.append (encodeRegs (regs.take k)) (regsTape (r :: suff))).cons 0))
  rw [append_replicate_cons] at hp_ones
  have htake_scan := rhRegIncrChain_scan_pref_tm isEd (regs.take k) (by omega)
    (ListBlank.append (List.replicate (m + 1) 1) ((L_base.cons 0).cons 0))
    (regsTape (r :: suff))
  rw [htake_len, ← Layer1.append_encodeReg_reverse,
    ← ListBlank.append_assoc, ← List.reverse_append, ← encodeRegs_cons] at htake_scan
  set L_pref := ListBlank.append (encodeRegs pref).reverse ((L_base.cons 0).cons 0)
  have hr_scan_c : nSteps common121 ((r + 1) + 1)
      ⟨11, Tape.mk' L_pref (regsTape (r :: suff))⟩ =
      some ⟨13, Tape.mk' (ListBlank.append (List.replicate (r + 2) 1) L_pref) (regsTape suff)⟩ := by
    rw [regsTape_cons, Layer1.append_encodeReg]
    have hones := nSteps_mk'_right_scan (q := 11) (a := 1) (b := 1) (by rfl)
      (r + 1) L_pref ((regsTape suff).cons 0)
    have hzero : step common121
        ⟨11, Tape.mk' (ListBlank.append (List.replicate (r + 1) 1) L_pref)
          ((regsTape suff).cons 0)⟩ =
        some ⟨13, Tape.mk' ((ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1)
          (regsTape suff)⟩ :=
      step_mk'_right (by rfl) _ _
    have hcomb := nSteps_bind_eq hones (step_one hzero)
    have hcons : (ListBlank.append (List.replicate (r + 1) 1) L_pref).cons 1 =
        ListBlank.append (List.replicate (r + 2) 1) L_pref := by
      rw [← ListBlank.append, ← List.replicate_succ]
    rw [hcons] at hcomb
    exact hcomb
  have hr_scan := nSteps_tm_of_common isEd hr_scan_c
  obtain ⟨s_shift, hs1, hshift_c⟩ := inc_shift_eval suff (r + 1) L_pref
  have hshift := nSteps_tm_of_common isEd hshift_c
  have hret_c := return0_scan_fence pref L_base (regsTape ((r + 1) :: suff))
  have hset : ListBlank.append (encodeRegs pref) (regsTape ((r + 1) :: suff)) =
      regsTape (m :: regs.set k (r + 1)) := by
    rw [← regsTape_append]
    congr 1
    simp only [pref, List.cons_append]
    congr 1
    exact list_take_set_drop regs k (r + 1) hk
  rw [hset] at hret_c
  have hret := nSteps_tm_of_common isEd hret_c
  have htotal := nSteps_bind_eq hp_ones
    (nSteps_bind_eq htake_scan (nSteps_bind_eq hr_scan (nSteps_bind_eq hshift hret)))
  exact ⟨_, by omega, htotal⟩

theorem stage3_inc_pass2_tm (isEd : Bool) (k : ℕ) (hk5 : k < 5) (p : ℕ) (hp : 1 ≤ p)
    (regs : List ℕ) (hk : k < regs.length) (L_stack : ListBlank (Fin 2)) :
    ∃ z m, z + m = p + 2 ∧
      ∃ s, 1 ≤ s ∧ nSteps (tm isEd) s
        ⟨regIncStage3 k, Tape.mk' L_stack ((regsTape (p :: regs)).cons 0 |>.cons 1)⟩ =
        some ⟨19, Tape.mkL L_stack
          (ListBlank.append (List.replicate z 0)
            (ListBlank.append (encodeReg m)
              (regsTape (regs.set k (regs[k] + 1)))))⟩ := by
  set r := regs[k]
  set suff := regs.drop (k + 1)
  have hregs_split : regsTape (p :: regs) =
      ListBlank.append (encodeRegs (p :: regs.take k)) (regsTape (r :: suff)) := by
    have hlist : p :: regs = (p :: regs.take k) ++ r :: suff := by
      simp only [List.cons_append]
      congr 1
      exact (list_take_cons_drop regs k hk).symm
    rw [hlist, regsTape_append]
  by_cases h70 : (isEd && k == 4) = true
  · have hisEd : isEd = true := by cases isEd <;> simp at h70 ⊢
    have hk4 : k = 4 := by
      rw [hisEd, Bool.true_and, beq_iff_eq] at h70
      exact h70
    subst hisEd hk4
    set m := p - 1
    have hp_eq : p = m + 1 := by omega
    refine ⟨3, m, by omega, ?_⟩
    have henter := runPrefix_sound true regIncStage3_enter_chain_70 L_stack
      (ListBlank.append (List.replicate m 1)
        ((ListBlank.append (encodeRegs (regs.take 4)) (regsTape (r :: suff))).cons 0))
    have hR_in : ListBlank.append ([1, 0, 1, 1] : List (Fin 2))
        (ListBlank.append (List.replicate m 1)
          ((ListBlank.append (encodeRegs (regs.take 4)) (regsTape (r :: suff))).cons 0)) =
        ((regsTape (p :: regs)).cons 0 |>.cons 1) := by
      rw [hregs_split, hp_eq, encodeRegs_cons, ListBlank.append_assoc,
        Layer1.append_encodeReg,
        List.replicate_succ, List.replicate_succ, ListBlank.append]
      rfl
    have hL_out : ListBlank.append ([1, 0, 0, 1] : List (Fin 2)) L_stack =
        ((((L_stack.cons 1).cons 0).cons 0).cons 1) := rfl
    rw [ListBlank.append, ListBlank.append, hR_in, hL_out] at henter
    obtain ⟨s_ch, hs_ch_pos, hch⟩ := stage3_inc_from_chain true 4 hk5 m regs hk (L_stack.cons 1)
    have hstep19 : step (tm true)
        ⟨19, Tape.mkL (L_stack.cons 1)
          ((regsTape (m :: regs.set 4 (r + 1))).cons 0 |>.cons 0)⟩ =
        some ⟨19, Tape.mkL L_stack
          (ListBlank.append (List.replicate 3 0)
            (ListBlank.append (encodeReg m)
              (regsTape (regs.set 4 (r + 1)))))⟩ := by
      rw [regsTape_cons]
      exact step_tm_of_common true (step_mkL_left (by rfl) L_stack _)
    exact ⟨4 + (s_ch + 1), by omega,
      nSteps_bind_eq henter (nSteps_bind_eq hch (step_one hstep19))⟩
  · have hnot : (isEd && k == 4) = false := Bool.eq_false_iff.mpr h70
    refine ⟨2, p, by omega, ?_⟩
    have henter := runPrefix_sound isEd (regIncStage3_enter_chain_3 isEd k hk5 hnot) L_stack
      (ListBlank.append (List.replicate p 1)
        ((ListBlank.append (encodeRegs (regs.take k)) (regsTape (r :: suff))).cons 0))
    have hR_in : ListBlank.append ([1, 0, 1] : List (Fin 2))
        (ListBlank.append (List.replicate p 1)
          ((ListBlank.append (encodeRegs (regs.take k)) (regsTape (r :: suff))).cons 0)) =
        ((regsTape (p :: regs)).cons 0 |>.cons 1) := by
      rw [hregs_split, encodeRegs_cons, ListBlank.append_assoc,
        Layer1.append_encodeReg,
        List.replicate_succ, ListBlank.append]
      rfl
    have hL_out : ListBlank.append ([1, 0, 0] : List (Fin 2)) L_stack =
        (((L_stack.cons 0).cons 0).cons 1) := rfl
    rw [ListBlank.append, ListBlank.append, hR_in, hL_out] at henter
    obtain ⟨s_ch, hs_ch_pos, hch⟩ := stage3_inc_from_chain isEd k hk5 p regs hk L_stack
    have hR2 : ((regsTape (p :: regs.set k (r + 1))).cons 0 |>.cons 0) =
        ListBlank.append (List.replicate 2 0)
          (ListBlank.append (encodeReg p)
            (regsTape (regs.set k (r + 1)))) := by
      rw [regsTape_cons]; rfl
    rw [hR2] at hch
    exact ⟨3 + s_ch, by omega, nSteps_bind_eq henter hch⟩

theorem initPadOf_ge_19 (isEd : Bool) : 19 ≤ initPadOf isEd := by
  cases isEd <;> decide

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem rhRootCfgOf_step_sim (isEd : Bool) {padTotal : ℕ} (hpad19 : 19 ≤ padTotal)
    {bits : List (Fin 2)} (hvalid : isValidStack bits = true)
    {regs : List ℕ} (hregs : regs.length = 5) (extra : List ℕ) :
    (evalStackOf isEd bits = .halt →
      ∃ s ≥ 1, ∃ ch,
        nSteps (tm isEd) s (rhRootCfgOf isEd padTotal bits regs (regsTape extra)) = some ch ∧
        step (tm isEd) ch = none) ∧
    (∀ bits' regs', rhRegStepOf isEd ⟨bits, regs⟩ = some ⟨bits', regs'⟩ →
      isValidStack bits' = true ∧
      regs'.length = 5 ∧
      ∃ padTotal', 19 ≤ padTotal' ∧ ∃ s ≥ 1, ∃ extra' : List ℕ,
        nSteps (tm isEd) s (rhRootCfgOf isEd padTotal bits regs (regsTape extra)) =
          some (rhRootCfgOf isEd padTotal' bits' regs' (regsTape extra'))) := by
  have hpad18 : 18 ≤ padTotal := by omega
  have hmem : bits ∈ allValidStacks := List.contains_iff_mem.mp hvalid
  have hchk := validStackSimCheck_all isEd bits hmem
  dsimp only [validStackSimCheck] at hchk
  rw [Bool.and_eq_true] at hchk
  rcases hchk with ⟨hs_le, hchk⟩
  have hs_le := of_decide_eq_true hs_le
  set s_stk := stackOf isEd bits
  set regs_all := regs ++ extra
  set R_extra := ListBlank.append (List.replicate (padTotal - 18) 0)
    (regsTape (0 :: regs_all))
  have hroot_pfx := rhRootCfgOf_eq_prefix isEd hpad18 hs_le regs_all
  rcases hout : walkTapeOf isEd 27 [] (s_stk ++ List.replicate (18 - s_stk.length) 0) with
    ⟨q_h, walked_h, rem_h⟩ | ⟨q', walked, rem'⟩ | ⟨q', walked_l, rem_l⟩ | _
  · rw [hout] at hchk; dsimp only at hchk
    repeat rw [Bool.and_eq_true] at hchk
    repeat rw [and_assoc] at hchk
    rcases hchk with ⟨hw_pos, hev, hchk⟩
    have hw_pos := of_decide_eq_true hw_pos
    have hev := beq_iff_eq.mp hev
    cases rem_h with
    | nil => cases hchk
    | cons b_h rem_h' =>
      dsimp only at hchk
      rw [Bool.and_eq_true] at hchk
      rcases hchk with ⟨hrun, htr_none⟩
      have hrun := beq_iff_eq.mp hrun
      have htr_none := beq_iff_eq.mp htr_none
      have hs := runPrefix_sound isEd hrun default R_extra
      rw [← hroot_pfx, ← rhRootCfgOf_regsTape_eq, ListBlank.append] at hs
      constructor
      · intro _
        exact ⟨walked_h.length, hw_pos, _, hs, step_mk'_none_tm isEd htr_none _ _⟩
      · intro bits' regs' hstep
        rw [rhRegStepOf_of_evalStackOf, hev] at hstep
        cases hstep
  · rw [hout] at hchk; dsimp only at hchk
    rcases hev : evalStackOf isEd bits with _ | bits_jmp | _ | _
    · rw [hev] at hchk; cases hchk
    · rw [hev] at hchk; dsimp only at hchk
      set w' := stackOf isEd bits_jmp
      repeat rw [Bool.and_eq_true] at hchk
      repeat rw [and_assoc] at hchk
      rcases hchk with ⟨hw_le, hw_len_eq, hrem0, hw'_le, hq_cases⟩
      have hw_le := of_decide_eq_true hw_le
      have hw_len_eq := beq_iff_eq.mp hw_len_eq
      have hrem0 := beq_iff_eq.mp hrem0
      have hw'_le := of_decide_eq_true hw'_le
      constructor
      · intro hh; cases hh
      · intro bits' regs' hstep
        have hv' := rhRegStepOf_valid isEd hvalid hstep
        rw [rhRegStepOf_of_evalStackOf, hev] at hstep
        rcases Option.some.inj hstep with ⟨rfl, rfl⟩
        refine ⟨hv', hregs, padTotal, hpad19, ?_⟩
        rcases hbr : ((q' == 19 || q' == 91) && !isEd) with _ | _
        · rw [hbr, ite_eq_right Bool.false_ne_true] at hq_cases
          have hrun := beq_iff_eq.mp hq_cases
          have hs₁ := runPrefix_sound isEd hrun default R_extra
          have hR_eq : ListBlank.append
              (w' ++ List.replicate (walked.length - w'.length) 0 ++ (0 :: rem')) R_extra =
              ListBlank.append w'
                (ListBlank.append (List.replicate (padTotal - w'.length) 0)
                  (regsTape (0 :: regs_all))) := by
            rw [List.append_assoc, ListBlank.append_assoc, ListBlank.append_assoc, hrem0]
            dsimp only [R_extra]
            rw [append_replicate_zeros_eq, append_replicate_zeros_eq]
            congr 3; omega
          rw [hR_eq, ← hroot_pfx, append_rootPrefixOf_default, ← rhRootCfgOf_default_eq,
            ← rhRootCfgOf_regsTape_eq, ← rhRootCfgOf_regsTape_eq] at hs₁
          exact ⟨_, by split_ifs <;> omega, extra, hs₁⟩
        · rw [hbr, ite_eq_left rfl] at hq_cases
          rw [Bool.and_eq_true] at hq_cases
          rcases hq_cases with ⟨hrun, hno4⟩
          have hrun := beq_iff_eq.mp hrun
          have hs₁ := runPrefix_sound isEd hrun default R_extra
          rw [append_reverse_rootPrefixOf_default] at hs₁
          have hR_eq : ListBlank.append
              (List.replicate (walked.length - w'.length) 0 ++ (0 :: rem')) R_extra =
              ListBlank.append (List.replicate (padTotal - w'.length) 0)
                (ListBlank.append (encodeReg 0) (regsTape regs_all)) := by
            rw [ListBlank.append_assoc, hrem0]
            dsimp only [R_extra]
            rw [append_replicate_zeros_eq, append_replicate_zeros_eq, regsTape_cons]
            congr 2; omega
          rw [hR_eq] at hs₁
          obtain ⟨s₂, hs₂_pos, hcl⟩ := cleanup_to_main_tm isEd w' hno4
            (padTotal - w'.length) 0 (regsTape regs_all)
          have hadd0 : padTotal - w'.length + 0 = padTotal - w'.length := by omega
          rw [hadd0] at hcl
          have hroot_w' : ⟨27, Tape.mk' (rootLeftOf isEd)
              (ListBlank.append w'
                (ListBlank.append (List.replicate (padTotal - w'.length) 0)
                  (ListBlank.append [1, 0] (regsTape regs_all))))⟩ =
              rhRootCfgOf isEd padTotal bits_jmp regs_all default := by
            rw [rhRootCfgOf_default_eq, regsTape_cons]; rfl
          rw [hroot_w'] at hcl
          have htot := nSteps_bind_eq hs₁ hcl
          rw [← hroot_pfx, ← rhRootCfgOf_regsTape_eq, ← rhRootCfgOf_regsTape_eq] at htot
          exact ⟨(2 * walked.length - w'.length + 2) + s₂, by omega, extra, htot⟩
    · rw [hev] at hchk; cases hchk
    · rw [hev] at hchk; cases hchk
  · rw [hout] at hchk; dsimp only at hchk
    set r := leafReg q'
    set w'_b0 := (popBreakRev 0 walked_l.reverse).reverse
    set w'_b1 := (popBreakRev 1 walked_l.reverse).reverse
    repeat rw [Bool.and_eq_true] at hchk
    repeat rw [and_assoc] at hchk
    rcases hchk with
      ⟨hw_pos, hw_le, hw_len_eq, hrem0, hq0, hrun1, hrun2, hno4_w, hno4_b0, hleaf_kind⟩
    have hw_pos := of_decide_eq_true hw_pos
    have hw_le := of_decide_eq_true hw_le
    have hw_len_eq := beq_iff_eq.mp hw_len_eq
    have hrem0 := beq_iff_eq.mp hrem0
    have hq0 := beq_iff_eq.mp hq0
    have hrun1 := beq_iff_eq.mp hrun1
    have hrun2 := beq_iff_eq.mp hrun2
    have hr5 : r < 5 := leafReg_lt_5 q'
    have hr_all : r < regs_all.length := by simp [regs_all, hregs]; omega
    set p := padTotal - walked_l.length - 2
    have hs₁' := runPrefix_sound isEd hrun1 default R_extra
    rw [append_reverse_rootPrefixOf_default] at hs₁'
    have hR_leaf : ListBlank.append rem_l R_extra =
        ((ListBlank.append (List.replicate (p + 1) 0)
          (ListBlank.append [1, 0] (regsTape regs_all))).cons 0) := by
      rw [hrem0, append_replicate_zeros_eq]
      have hcnt : rem_l.length + (padTotal - 18) = (p + 1) + 1 := by omega
      rw [hcnt, List.replicate_succ, ListBlank.append, regsTape_cons]
      rfl
    rw [hR_leaf] at hs₁'
    have hstep_q' : step (tm isEd)
        ⟨q', Tape.mk' (stackLeftOf isEd walked_l)
          ((ListBlank.append (List.replicate (p + 1) 0)
            (ListBlank.append [1, 0] (regsTape regs_all))).cons 0)⟩ =
        some ⟨6, Tape.mk' ((stackLeftOf isEd walked_l).cons 1)
          (ListBlank.append (List.replicate (p + 1) 0)
            (ListBlank.append [1, 0] (regsTape regs_all)))⟩ :=
      step_tm_of_common isEd (step_mk'_right hq0 _ _)
    obtain ⟨s_prep, hs_prep_pos, hprep⟩ :=
      prep_pass1_eval_tm isEd walked_l hno4_w p (regsTape regs_all)
    have hprep_eq : ListBlank.append (walked_l ++ [1, 0] ++ encodeReg p) (regsTape regs_all) =
        ListBlank.append walked_l ((regsTape (p :: regs_all)).cons 0 |>.cons 1) := by
      rw [regsTape_cons]
      simp only [List.append_assoc, ListBlank.append_assoc, ListBlank.append]
    rw [hprep_eq, ← append_rootPrefixOf_default] at hprep
    have hs₂ := runPrefix_sound isEd hrun2 default ((regsTape (p :: regs_all)).cons 0 |>.cons 1)
    rw [append_reverse_rootPrefixOf_default, ListBlank.append] at hs₂
    have hpass12 := nSteps_bind_eq hs₁' (step_nSteps hstep_q' (nSteps_bind_eq hprep hs₂))
    have hw_pad : walked_l.length ≤ padTotal := by omega
    rcases hinc : isLeafInc q' with _ | _
    · rw [hinc, ite_eq_right Bool.false_ne_true] at hleaf_kind
      repeat rw [Bool.and_eq_true] at hleaf_kind
      repeat rw [and_assoc] at hleaf_kind
      rcases hleaf_kind with ⟨hq_eq, hw_last, hno4_b1, hev_chk⟩
      have hq_eq := beq_iff_eq.mp hq_eq
      have hw_last := beq_iff_eq.mp hw_last
      rcases hev : evalStackOf isEd bits with _ | _ | _ | ⟨r_ev, bits_succ, bits_fail⟩
      · rw [hev] at hev_chk; cases hev_chk
      · rw [hev] at hev_chk; cases hev_chk
      · rw [hev] at hev_chk; cases hev_chk
      · rw [hev] at hev_chk; dsimp only at hev_chk
        repeat rw [Bool.and_eq_true] at hev_chk
        repeat rw [and_assoc] at hev_chk
        rcases hev_chk with ⟨hr_ev, hw'_b0_eq, hw'_b1_eq⟩
        have hr_ev := beq_iff_eq.mp hr_ev
        subst hr_ev
        have hw'_b0_eq := beq_iff_eq.mp hw'_b0_eq
        have hw'_b1_eq := beq_iff_eq.mp hw'_b1_eq
        constructor
        · intro hh; cases hh
        · intro bits' regs' hstep
          have hv' := rhRegStepOf_valid isEd hvalid hstep
          rw [hq_eq] at hpass12
          have hget : regs_all[r] = regs.getD r 0 := regs_append_getElem hregs hr5
          by_cases hz : regs.getD r 0 = 0
          · have hbeq : (regs.getD r 0 == 0) = true := beq_iff_eq.mpr hz
            rw [rhRegStepOf_of_evalStackOf, hev] at hstep
            dsimp only at hstep
            rw [hbeq] at hstep
            rcases Option.some.inj hstep with ⟨rfl, rfl⟩
            have hz_all : regs_all[r] = 0 := by rw [hget, hz]
            obtain ⟨s₃, hs₃_pos, hp2_c⟩ := stage3_decnz_pass2_zero r hr5 p regs_all hr_all hz_all
              (stackLeftOf isEd walked_l)
            obtain ⟨padTotal', hpad_le, s₄, hs₄_pos, hcl_tm⟩ :=
              decnz_zero_cleanup_to_root isEd padTotal walked_l hw_last hw_pad p (by omega) hno4_b1
                regs_all
            rw [← regsTape_cons] at hcl_tm
            have htot := nSteps_bind_eq hpass12
              (nSteps_bind_eq (nSteps_tm_of_common isEd hp2_c) hcl_tm)
            change nSteps (tm isEd) _ _ =
              some (rhRootCfgRaw isEd padTotal' w'_b1 regs_all default) at htot
            rw [← hroot_pfx, ← rhRootCfgOf_regsTape_eq, hw'_b1_eq] at htot
            change nSteps (tm isEd) _ _ =
              some (rhRootCfgOf isEd padTotal' bits_fail regs_all default) at htot
            rw [← rhRootCfgOf_regsTape_eq] at htot
            exact ⟨hv', hregs, padTotal', by omega, _, by omega, extra, htot⟩
          · have hbeq : (regs.getD r 0 == 0) = false := beq_eq_false_iff_ne.mpr hz
            rw [rhRegStepOf_of_evalStackOf, hev] at hstep
            dsimp only at hstep
            rw [hbeq] at hstep
            rcases Option.some.inj hstep with ⟨rfl, rfl⟩
            have hpos_all : 0 < regs_all[r] := by omega
            obtain ⟨s₃, hs₃_pos, hp2_c⟩ := stage3_decnz_pass2_pos r hr5 p regs_all hr_all hpos_all
              (stackLeftOf isEd walked_l)
            have hR2 :
                ((regsTape (p :: (regs_all.set r (regs_all[r] - 1) ++ [0]))).cons 0 |>.cons 0)
                = ListBlank.append (List.replicate 2 0)
                  (ListBlank.append (encodeReg p)
                    (regsTape (regs_all.set r (regs_all[r] - 1) ++ [0]))) := by
              rw [regsTape_cons]; rfl
            rw [hR2] at hp2_c
            obtain ⟨padTotal', hpad_le, s₄, hs₄_pos, hcl_tm⟩ :=
              break0_cleanup_to_root_tm isEd padTotal walked_l hw_pad 2 p (by omega) hno4_b0
                (regs_all.set r (regs_all[r] - 1) ++ [0])
            have htot := nSteps_bind_eq hpass12
              (nSteps_bind_eq (nSteps_tm_of_common isEd hp2_c) hcl_tm)
            have hregs_eq : regs_all.set r (regs_all[r] - 1) ++ [0] =
                regs.set r (regs.getD r 0 - 1) ++ (extra ++ [0]) := by
              rw [← List.append_assoc, ← hget, regs_append_set hregs hr5]
            change nSteps (tm isEd) _ _ =
              some (rhRootCfgRaw isEd padTotal' w'_b0 _ default) at htot
            rw [← hroot_pfx, ← rhRootCfgOf_regsTape_eq, hregs_eq, hw'_b0_eq] at htot
            change nSteps (tm isEd) _ _ =
              some (rhRootCfgOf isEd padTotal' bits_succ _ default) at htot
            rw [← rhRootCfgOf_regsTape_eq] at htot
            exact ⟨hv', by simp [hregs], padTotal', by omega, _, by omega, extra ++ [0], htot⟩
    · rw [hinc, ite_eq_left rfl] at hleaf_kind
      rw [Bool.and_eq_true] at hleaf_kind
      rcases hleaf_kind with ⟨hq_eq, hev_chk⟩
      have hq_eq := beq_iff_eq.mp hq_eq
      rcases hev : evalStackOf isEd bits with _ | _ | ⟨r_ev, bits_succ⟩ | _
      · rw [hev] at hev_chk; cases hev_chk
      · rw [hev] at hev_chk; cases hev_chk
      · rw [hev] at hev_chk; dsimp only at hev_chk
        rw [Bool.and_eq_true] at hev_chk
        rcases hev_chk with ⟨hr_ev, hw'_b0_eq⟩
        have hr_ev := beq_iff_eq.mp hr_ev
        subst hr_ev
        have hw'_b0_eq := beq_iff_eq.mp hw'_b0_eq
        constructor
        · intro hh; cases hh
        · intro bits' regs' hstep
          have hv' := rhRegStepOf_valid isEd hvalid hstep
          rw [rhRegStepOf_of_evalStackOf, hev] at hstep
          rcases Option.some.inj hstep with ⟨rfl, rfl⟩
          rw [hq_eq] at hpass12
          obtain ⟨z_inc, m_inc, hzm_eq, s₃, hs₃_pos, hp2_tm⟩ :=
            stage3_inc_pass2_tm isEd r hr5 p (by omega) regs_all hr_all
              (stackLeftOf isEd walked_l)
          obtain ⟨padTotal', hpad_le, s₄, hs₄_pos, hcl_tm⟩ :=
            break0_cleanup_to_root_tm isEd padTotal walked_l hw_pad z_inc m_inc (by omega) hno4_b0
              (regs_all.set r (regs_all[r] + 1))
          have htot := nSteps_bind_eq hpass12 (nSteps_bind_eq hp2_tm hcl_tm)
          have hregs_eq : regs_all.set r (regs_all[r] + 1) =
              regs.set r (regs.getD r 0 + 1) ++ extra := by
            rw [regs_append_getElem hregs hr5, regs_append_set hregs hr5]
          change nSteps (tm isEd) _ _ =
            some (rhRootCfgRaw isEd padTotal' w'_b0 _ default) at htot
          rw [← hroot_pfx, ← rhRootCfgOf_regsTape_eq, hregs_eq, hw'_b0_eq] at htot
          change nSteps (tm isEd) _ _ =
            some (rhRootCfgOf isEd padTotal' bits_succ _ default) at htot
          rw [← rhRootCfgOf_regsTape_eq] at htot
          exact ⟨hv', by simp [hregs], padTotal', by omega, _, by omega, extra, htot⟩
      · rw [hev] at hev_chk; cases hev_chk
  · rw [hout] at hchk; cases hchk

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem rhReg_eval_dom_of_tm_halt (isEd : Bool) :
    ∀ N {padTotal : ℕ} {c : RhRegCfg} {extra : List ℕ} {ch : Cfg 121 2},
      19 ≤ padTotal →
      isValidStack c.stack = true →
      c.regs.length = 5 →
      nSteps (tm isEd) N (rhRootCfgOf isEd padTotal c.stack c.regs (regsTape extra)) = some ch →
      step (tm isEd) ch = none →
      (StateTransition.eval (rhRegStepOf isEd) c).Dom := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro padTotal c extra ch hpad hv hregs hN hnone
    have hsim := rhRootCfgOf_step_sim isEd hpad hv hregs extra
    rcases hs : rhRegStepOf isEd c with _ | c'
    · rw [Part.dom_iff_mem]
      exact ⟨c, mem_eval'.mpr ⟨Relation.ReflTransGen.refl, hs⟩⟩
    · obtain ⟨hv', hregs', padTotal', hpad', s, hs_pos, extra', hsteps⟩ :=
        hsim.2 c'.stack c'.regs hs
      have hle : s ≤ N := by
        by_cases h : s ≤ N
        · exact h
        · exfalso
          have hgt : 1 ≤ s - N := by omega
          have hsplit : s = N + (s - N) := by omega
          rw [hsplit, nSteps_add, hN, Option.bind_some, nSteps_of_halt hnone hgt] at hsteps
          cases hsteps
      have hsplit : N = s + (N - s) := by omega
      rw [hsplit, nSteps_add, hsteps, Option.bind_some] at hN
      have hDom' := ih (N - s) (by omega) hpad' hv' hregs' hN hnone
      have hreach : Reaches (rhRegStepOf isEd) c c' :=
        Relation.ReflTransGen.head hs Relation.ReflTransGen.refl
      rwa [reaches_eval' hreach]

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem tm_eval_dom_of_rhReg_halt (isEd : Bool) {padTotal : ℕ} (hpad : 19 ≤ padTotal)
    {c : RhRegCfg} {extra : List ℕ}
    (hv : isValidStack c.stack = true) (hregs : c.regs.length = 5)
    (hDom : (StateTransition.eval (rhRegStepOf isEd) c).Dom) :
    (StateTransition.eval (step (tm isEd))
      (rhRootCfgOf isEd padTotal c.stack c.regs (regsTape extra))).Dom := by
  rw [Part.dom_iff_mem] at hDom ⊢
  obtain ⟨ch_reg, hmem⟩ := hDom
  obtain ⟨n, hn, hnone⟩ := (mem_eval_rhRegStepOf_iff_rhRegNStepsOf isEd).mp hmem
  have hrun : ∀ m {pad₀ : ℕ} {c₀ : RhRegCfg} {ext₀ : List ℕ},
      19 ≤ pad₀ → isValidStack c₀.stack = true → c₀.regs.length = 5 →
      rhRegNStepsOf isEd m c₀ = some ch_reg →
      isValidStack ch_reg.stack = true ∧
      ch_reg.regs.length = 5 ∧
      ∃ pad_f, 19 ≤ pad_f ∧ ∃ T ext_f,
        nSteps (tm isEd) T (rhRootCfgOf isEd pad₀ c₀.stack c₀.regs (regsTape ext₀)) =
          some (rhRootCfgOf isEd pad_f ch_reg.stack ch_reg.regs (regsTape ext_f)) := by
    intro m
    induction m with
    | zero =>
      intro pad₀ c₀ ext₀ hp₀ hv₀ hr₀ hm
      injection hm with heq
      subst heq
      exact ⟨hv₀, hr₀, pad₀, hp₀, 0, ext₀, rfl⟩
    | succ m ih =>
      intro pad₀ c₀ ext₀ hp₀ hv₀ hr₀ hm
      unfold rhRegNStepsOf at hm
      rcases hs : rhRegStepOf isEd c₀ with _ | c₁
      · simp [hs] at hm
      · rw [hs, Option.bind_some] at hm
        obtain ⟨hv₁, hr₁, pad₁, hp₁, s₁, _, ext₁, hst₁⟩ :=
          (rhRootCfgOf_step_sim isEd hp₀ hv₀ hr₀ ext₀).2 c₁.stack c₁.regs hs
        obtain ⟨hvf, hrf, pad_f, hpf, T, ext_f, hT⟩ := ih hp₁ hv₁ hr₁ hm
        exact ⟨hvf, hrf, pad_f, hpf, s₁ + T, ext_f, nSteps_bind_eq hst₁ hT⟩
  obtain ⟨hvf, hrf, pad_f, hpf, T, ext_f, hT⟩ := hrun n hpad hv hregs hn
  have hhalt_ev : evalStackOf isEd ch_reg.stack = .halt := by
    rw [rhRegStepOf_of_evalStackOf] at hnone
    rcases hev : evalStackOf isEd ch_reg.stack with _ | _ | ⟨_, _⟩ | ⟨r_d, _, _⟩
    · rfl
    · rw [hev] at hnone; cases hnone
    · rw [hev] at hnone; cases hnone
    · rw [hev] at hnone
      by_cases hz : (ch_reg.regs.getD r_d 0 == 0) = true <;>
        simp only [hz, ↓reduceIte, Bool.false_eq_true] at hnone <;>
        cases hnone
  obtain ⟨s_h, _, ch_tm, hs_h, htm_none⟩ :=
    (rhRootCfgOf_step_sim isEd hpf hvf hrf ext_f).1 hhalt_ev
  exact ⟨ch_tm, mem_eval_iff_nSteps.mpr ⟨T + s_h, nSteps_bind_eq hT hs_h, htm_none⟩⟩

def initTm (isEd : Bool) : Cfg 121 2 :=
  if isEd then ⟨11, default⟩ else init

set_option maxHeartbeats 1600000 in
-- Finite state-table decision procedure.
theorem boot_ed_runPrefix :
    runPrefix (tmTrans true) 9037 11 (List.replicate 12 0) (List.replicate 50 0) =
      some (27, rootPrefixOf true,
        List.replicate 21 0 ++ encodeRegs (0 :: [0, 0, 0, 0, 0] ++ List.replicate 12 0)) := by
  decide

theorem boot_reaches_main0_tm (isEd : Bool) :
    ∃ s extra,
      nSteps (tm isEd) s (initTm isEd) =
        some (rhRootCfgOf isEd (initPadOf isEd) [] [0, 0, 0, 0, 0] (regsTape extra)) := by
  cases isEd
  · obtain ⟨s, hs⟩ := boot_reaches_main0
    exact ⟨s, List.replicate 1904 0, hs⟩
  · have hs := runPrefix_sound true boot_ed_runPrefix default default
    have hinit : (⟨11, Tape.mk' (ListBlank.append (List.replicate 12 0) default)
        (ListBlank.append (List.replicate 50 0) default)⟩ : Cfg 121 2) = initTm true := by
      rw [append_replicate_zero_default, append_replicate_zero_default]
      rfl
    have hout : (⟨27, Tape.mk' (ListBlank.append (rootPrefixOf true) default)
        (ListBlank.append
          (List.replicate 21 0 ++ encodeRegs (0 :: [0, 0, 0, 0, 0] ++ List.replicate 12 0))
          default)⟩ : Cfg 121 2) =
        rhRootCfgOf true 21 [] [0, 0, 0, 0, 0] (regsTape (List.replicate 12 0)) := by
      rw [append_rootPrefixOf_default, ListBlank.append_assoc, rhRootCfgOf_regsTape_eq,
        rhRootCfgOf_default_eq]
      rfl
    rw [hinit, hout] at hs
    exact ⟨9037, List.replicate 12 0, hs⟩

set_option maxHeartbeats 800000 in
-- Finite state-table decision procedure.
theorem halts_tm_iff_rhRegHaltsOf (isEd : Bool) :
    (StateTransition.eval (step (tm isEd)) (initTm isEd)).Dom ↔ RhRegHaltsOf isEd := by
  obtain ⟨s_boot, extra_boot, hboot⟩ := boot_reaches_main0_tm isEd
  unfold RhRegHaltsOf
  rw [nSteps_eval_dom hboot]
  constructor
  · intro hDom
    rw [Part.dom_iff_mem] at hDom
    obtain ⟨ch, hmem⟩ := hDom
    obtain ⟨N, hN, hnone⟩ := mem_eval_iff_nSteps.mp hmem
    exact rhReg_eval_dom_of_tm_halt isEd N (initPadOf_ge_19 isEd) isValidStack_nil rfl hN hnone
  · intro hDom
    exact tm_eval_dom_of_rhReg_halt isEd (initPadOf_ge_19 isEd) isValidStack_nil rfl hDom


set_option maxHeartbeats 800000 in
theorem evalStackOf_false_eq_evalStack :
    ∀ bits ∈ Layer2.allValidStacks, evalStackOf false bits = Layer2.evalStack bits := by
  decide

theorem rhRegHaltsOf_false_iff_rhRegHalts : RhRegHaltsOf false ↔ Layer2.RhRegHalts := by
  have hrel : Respects Layer2.rhRegStep (rhRegStepOf false)
      (fun c₁ c₂ => Layer2.isValidStack c₁.stack = true ∧ c₁ = c₂) := by
    intro c₁ c₂ ⟨hv, hc⟩
    cases hc
    have hmem : c₁.stack ∈ Layer2.allValidStacks := List.contains_iff_mem.mp hv
    have hev := evalStackOf_false_eq_evalStack c₁.stack hmem
    have hstep_eq : rhRegStepOf false c₁ = Layer2.rhRegStep c₁ := by
      unfold rhRegStepOf Layer2.rhRegStep
      rw [hev]
    rcases hs : Layer2.rhRegStep c₁ with _ | c₁'
    · dsimp only
      rw [hstep_eq, hs]
    · dsimp only
      have hs' : rhRegStepOf false c₁ = some c₁' := by rw [hstep_eq, hs]
      exact ⟨c₁', ⟨Layer2.rhRegStep_preserves_isValidStack hv hs, rfl⟩,
        Relation.TransGen.single hs'⟩
  exact (tr_eval_dom' hrel ⟨Layer2.isValidStack_nil, rfl⟩).symm

/-- **Lockstep Simulation Theorem**: `riemann121` halts on the blank tape if and only if
the 5-register abstract machine `RhRegHalts` halts from `rhRegInit`. -/
theorem halts_riemann121_iff_rhRegHalts :
    ConjectureMachines.Halts riemann121 ↔ Layer2.RhRegHalts :=
  (halts_tm_iff_rhRegHaltsOf false).trans rhRegHaltsOf_false_iff_rhRegHalts

end ConjectureMachines.Riemann120

end
