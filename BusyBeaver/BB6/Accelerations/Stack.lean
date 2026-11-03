/-
Copyright (c) 2026 Google LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import BusyBeaver.Basic
public import BusyBeaver.Bridge

/-!
# Shared Stack Encodings for `BB(6)` Accelerations (`BusyBeaver/BB6/Accelerations/Stack.lean`)

Shared half-tape encodings (`encStack`, `encStack2`, `encRun`) and head-digit update operations
(`incRun`, `bumpHead`, `bumpHeadBy`) used across the `BB(6)` multi-layer acceleration modules.
-/

@[expose] public section

namespace BusyBeaver.Stack

open Turing

/-- Encode a digit stack `s` as `1^{a + 1} 0 ...` from the tape head outward. -/
def encStack : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s => ListBlank.append (([1] : List (Fin 2)) ^ (a + 1)) (ListBlank.cons 0 (encStack s))

/-- Encode a digit stack `s` as `1^{a + 1} 00 ...` from the tape head outward. -/
def encStack2 : List ℕ → ListBlank (Fin 2)
  | [] => default
  | a :: s =>
    ListBlank.append (([1] : List (Fin 2)) ^ (a + 1))
      (ListBlank.cons 0 (ListBlank.cons 0 (encStack2 s)))

/-- Encode a zero-run stack `s` as `0^k 1 ...` from the tape head outward. -/
def encRun : List ℕ → ListBlank (Fin 2)
  | [] => default
  | k :: xs => ListBlank.append (([0] : List (Fin 2)) ^ k) (ListBlank.cons 1 (encRun xs))

/-- Prepend a leading `0` to `encRun xs` (incrementing the head run on non-empty stacks). -/
def incRun : List ℕ → List ℕ
  | [] => []
  | k :: xs => (k + 1) :: xs

/-- Increment the head digit of a stack, or push `0` onto an empty stack. -/
def bumpHead : List ℕ → List ℕ
  | [] => [0]
  | a :: s => (a + 1) :: s

/-- Iterate `bumpHead` `k` times on a stack. -/
def bumpHeadBy : ℕ → List ℕ → List ℕ
  | 0, s => s
  | k + 1, s => bumpHeadBy k (bumpHead s)

/-- Appending `0 ^ n` onto the blank half-tape yields the blank half-tape. -/
theorem zeros_append_default (n : ℕ) :
    ListBlank.append (([0] : List (Fin 2)) ^ n) (default : ListBlank (Fin 2)) = default := by
  induction n with
  | zero => rfl
  | succ k ih =>
    rw [ListBlank.append_pow_succ, ih]
    simp

/-- Increment the primary coordinate of the top pair-stack element, or push `(0, 0)` if empty. -/
def bumpPairHead : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [(0, 0)]
  | (a, b) :: s => (a + 1, b) :: s

private def liftPairList : List ℕ → List (ℕ × ℕ)
  | [] => []
  | x :: xs => (x, 0) :: liftPairList xs

private theorem map_fst_liftPairList : ∀ s : List ℕ, (liftPairList s).map Prod.fst = s
  | [] => rfl
  | _ :: xs => congrArg (_ :: ·) (map_fst_liftPairList xs)

private theorem length_liftPairList : ∀ s : List ℕ, (liftPairList s).length = s.length
  | [] => rfl
  | _ :: xs => congrArg Nat.succ (length_liftPairList xs)

private theorem mem_liftPairList : ∀ {a : ℕ} {s : List ℕ}, a ∈ s → (a, 0) ∈ liftPairList s
  | _, _ :: _, .head _ => .head _
  | _, _ :: _, .tail _ h => .tail _ (mem_liftPairList h)

/-- One-digit (`List ℕ`) sufficient conditions for `HasStackReduction` (`maxSepL = maxSepR = 1`). -/
def OneDigitStackReduction {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop) : Prop :=
  encLeft1 [] = default ∧
  encRight1 [] = default ∧
  (∀ a L, (encLeft1 (a :: L)).head = (1 : Fin 2)) ∧
  (∀ d R, (encRight1 (d :: R)).head = (1 : Fin 2)) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ L : List ℕ, encLeft1 L ≠ t) ∧
  (∃ t : ListBlank (Fin 2), t.head = (1 : Fin 2) ∧ ∀ R : List ℕ, encRight1 R ≠ t) ∧
  (∃ strideL offsetL sepL strideR offsetR sepR : ℕ,
    strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧
    strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧
    (∀ a L, encLeft1 (a :: L) =
      ListBlank.append (([1] : List (Fin 2)) ^ (strideL * a + offsetL))
        (ListBlank.append (([0] : List (Fin 2)) ^ sepL) (encLeft1 L))) ∧
    (∀ d R, encRight1 (d :: R) =
      ListBlank.append (([1] : List (Fin 2)) ^ (strideR * d + offsetR))
        (ListBlank.append (([0] : List (Fin 2)) ^ sepR) (encRight1 R)))) ∧
  (∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes) ∧
  IsValidStackModes encLeft1 encRight1 evalStackCfg1 ∧
  (∀ cfg, IsInStackSystem1 cfg ↔ ∃ m L R, cfg = evalStackCfg1 m L R) ∧
  (∀ m L R, IsInStackSystem1 (evalStackCfg1 m L R)) ∧
  (∃ (m_g : StackMode) (L_g R_g : List ℕ),
    ReachesPlus M (init []) (evalStackCfg1 m_g L_g R_g) ∧
    3 ≤ L_g.length + R_g.length ∧
    (∃ a ∈ L_g ++ R_g, 1 ≤ a)) ∧
  ((∃ (m m' : StackMode) (x : ℕ) (g : ℕ → ℕ) (f : List ℕ → List ℕ),
      (∀ s, s.length ≤ (f s).length) ∧
      ∀ z L R,
        ReachesPlus M (evalStackCfg1 m (x :: z :: L) R) (evalStackCfg1 m' (g z :: L) (f R))) ∨
    (∃ (m m' : StackMode) (x : ℕ) (g : ℕ → ℕ) (f : List ℕ → List ℕ),
      (∀ s, s.length ≤ (f s).length) ∧
      ∀ z L R,
        ReachesPlus M (evalStackCfg1 m L (x :: z :: R)) (evalStackCfg1 m' (f L) (g z :: R)))) ∧
  (∀ cfg, IsInStackSystem1 cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧ (IsInStackSystem1 cfg' ∨ (step M cfg').isNone))

/-- Lift a 1-digit (`List ℕ`) stack reduction to `HasStackReduction` (`List (ℕ × ℕ)`). -/
theorem HasStackReduction.of_oneDigit {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin 2) Λ)
    (StackMode : Type)
    (encLeft1 encRight1 : List ℕ → ListBlank (Fin 2))
    (evalStackCfg1 : StackMode → List ℕ → List ℕ → Cfg (Fin 2) Λ)
    (IsInStackSystem1 : Cfg (Fin 2) Λ → Prop)
    (h : OneDigitStackReduction M StackMode encLeft1 encRight1 evalStackCfg1 IsInStackSystem1) :
    HasStackReduction M := by
  refine ⟨StackMode, 1, 0,
    fun (L : List (ℕ × ℕ)) => encLeft1 (L.map Prod.fst),
    fun (R : List (ℕ × ℕ)) => encRight1 (R.map Prod.fst),
    fun (m : StackMode) (L R : List (ℕ × ℕ)) => evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    fun (cfg : Cfg (Fin 2) Λ) =>
      ∃ (m : StackMode) (L R : List (ℕ × ℕ)),
        cfg = evalStackCfg1 m (L.map Prod.fst) (R.map Prod.fst),
    ?_⟩
  rcases h with ⟨hnilL, hnilR, hheadL, hheadR, ⟨tL, htL, hnsL⟩, ⟨tR, htR, hnsR⟩,
    ⟨sL, oL, sepL, sR, oR, sepR, hsL, hoL, hsepL, hsR, hoR, hsepR, hblkL, hblkR⟩,
    hmodes, hvalid1, hiff1, _,
    ⟨m_g, L_g, R_g, hreach_g, hlen_g, ⟨a_g, hmem_g, ha_g⟩⟩,
    htransfer, hclosed1⟩
  refine ⟨Or.inl ⟨rfl, rfl⟩, hnilL, hnilR,
    fun a _ L => hheadL a (L.map Prod.fst),
    fun d _ R => hheadR d (R.map Prod.fst),
    ⟨tL, htL, fun L => hnsL (L.map Prod.fst)⟩,
    ⟨tR, htR, fun R => hnsR (R.map Prod.fst)⟩,
    ⟨sL, oL, sepL, 1, sR, oR, sepR, 1,
      hsL, hoL, hsepL, le_refl 1, by decide,
      hsR, hoR, hsepR, le_refl 1, by decide,
      fun a b L => by simpa [Nat.mod_one] using hblkL a (L.map Prod.fst),
      fun d b R => by simpa [Nat.mod_one] using hblkR d (R.map Prod.fst)⟩,
    hmodes,
    fun m => ?_,
    fun _ => Iff.rfl,
    fun m L R => ⟨m, L, R, rfl⟩,
    ?_,
    ?_,
    ?_⟩
  · rcases hvalid1 m with ⟨q, vL, vR, hvL, hvR, h1 | h2 | h3⟩
    · exact ⟨q, vL, vR, hvL, hvR, Or.inl (fun L R => h1 (L.map Prod.fst) (R.map Prod.fst))⟩
    · exact ⟨q, vL, vR, hvL, hvR,
        Or.inr (Or.inl (fun L R => h2 (L.map Prod.fst) (R.map Prod.fst)))⟩
    · exact ⟨q, vL, vR, hvL, hvR,
        Or.inr (Or.inr (fun L R => h3 (L.map Prod.fst) (R.map Prod.fst)))⟩
  · refine ⟨m_g, liftPairList L_g, liftPairList R_g, ?_, ?_, ?_⟩
    · simpa only [map_fst_liftPairList] using hreach_g
    · rw [length_liftPairList, length_liftPairList]
      exact hlen_g
    · refine ⟨(a_g, 0), ?_, ha_g⟩
      rcases List.mem_append.mp hmem_g with hL | hR
      · exact List.mem_append_left _ (mem_liftPairList hL)
      · exact List.mem_append_right _ (mem_liftPairList hR)
  · rcases htransfer with ⟨m, m', x, g, f, hflen, hstep⟩ | ⟨m, m', x, g, f, hflen, hstep⟩
    · refine Or.inl ⟨m, m', (x, 0), fun p => (g p.1, 0),
        fun s => liftPairList (f (s.map Prod.fst)), ?_, ?_⟩
      · intro s
        rw [length_liftPairList]
        simpa using hflen (s.map Prod.fst)
      · intro z L R
        dsimp only [List.map_cons]
        rw [map_fst_liftPairList]
        exact hstep z.1 (L.map Prod.fst) (R.map Prod.fst)
    · refine Or.inr ⟨m, m', (x, 0), fun p => (g p.1, 0),
        fun s => liftPairList (f (s.map Prod.fst)), ?_, ?_⟩
      · intro s
        rw [length_liftPairList]
        simpa using hflen (s.map Prod.fst)
      · intro z L R
        dsimp only [List.map_cons]
        rw [map_fst_liftPairList]
        exact hstep z.1 (L.map Prod.fst) (R.map Prod.fst)
  · intro cfg ⟨m, L, R, hcfg⟩
    have hsys1 : IsInStackSystem1 cfg := (hiff1 cfg).mpr ⟨m, L.map Prod.fst, R.map Prod.fst, hcfg⟩
    rcases hclosed1 cfg hsys1 with ⟨cfg', hstep, hnext | hhalt⟩
    · rcases (hiff1 cfg').mp hnext with ⟨m', L1', R1', hcfg'⟩
      refine ⟨cfg', hstep, Or.inl ⟨m', liftPairList L1', liftPairList R1', ?_⟩⟩
      rw [map_fst_liftPairList, map_fst_liftPairList]
      exact hcfg'
    · exact ⟨cfg', hstep, Or.inr hhalt⟩

/-! ## Direction and Tape Reflection -/

/-- Flip tape direction. -/
def reflectDir : Dir → Dir
  | .left => .right
  | .right => .left

@[simp] theorem reflectDir_reflectDir (d : Dir) : reflectDir (reflectDir d) = d := by
  cases d <;> rfl

/-- Reflect a doubly-infinite tape by swapping its left and right half-tapes. -/
def reflectTape {Γ : Type*} [Inhabited Γ] (T : Tape Γ) : Tape Γ :=
  ⟨T.head, T.right, T.left⟩

@[simp] theorem reflectTape_reflectTape {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    reflectTape (reflectTape T) = T := by
  cases T; rfl

@[simp] theorem reflectTape_head {Γ : Type*} [Inhabited Γ] (T : Tape Γ) :
    (reflectTape T).head = T.head := rfl

@[simp] theorem reflectTape_write {Γ : Type*} [Inhabited Γ] (b : Γ) (T : Tape Γ) :
    reflectTape (Tape.write b T) = Tape.write b (reflectTape T) := by
  cases T; rfl

@[simp] theorem reflectTape_move {Γ : Type*} [Inhabited Γ] (d : Dir) (T : Tape Γ) :
    reflectTape (Tape.move d T) = Tape.move (reflectDir d) (reflectTape T) := by
  cases d <;> cases T <;> rfl

@[simp] theorem reflectTape_step_tape {Γ : Type*} [Inhabited Γ] (b : Γ) (d : Dir) (T : Tape Γ) :
    reflectTape ((T.write b).move d) = ((reflectTape T).write b).move (reflectDir d) := by
  cases d <;> cases T <;> rfl

/-! ## Configuration Functors -/

/-- Map state and tape across Turing machine configuration types. -/
def mapCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ]
    (σ : Option Λ₁ → Option Λ₂) (Tmap : Tape Γ → Tape Γ) (c : Cfg Γ Λ₁) : Cfg Γ Λ₂ :=
  ⟨σ c.q, Tmap c.tape⟩

/-- Relabel control states of a configuration. -/
def mapState {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] (f : Λ₁ → Λ₂) (c : Cfg Γ Λ₁) : Cfg Γ Λ₂ :=
  ⟨c.q.map f, c.tape⟩

/-- Relabel control states and reflect tape of a configuration. -/
def mirrorCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] (f : Λ₁ → Λ₂) (c : Cfg Γ Λ₁) : Cfg Γ Λ₂ :=
  ⟨c.q.map f, reflectTape c.tape⟩

@[simp] theorem mapState_headRight {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mapState f (Cfg.headRight q l r) = Cfg.headRight (f q) l r := rfl

@[simp] theorem mapState_headLeft {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mapState f (Cfg.headLeft q l r) = Cfg.headLeft (f q) l r := rfl

@[simp] theorem mapState_zero {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [OfNat Γ 0]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mapState f ⟨some q, ⟨(0 : Γ), l, r⟩⟩ = ⟨some (f q), ⟨(0 : Γ), l, r⟩⟩ := rfl

@[simp] theorem mirrorCfg_headRight {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mirrorCfg f (Cfg.headRight q l r) = Cfg.headLeft (f q) r l := rfl

@[simp] theorem mirrorCfg_headLeft {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mirrorCfg f (Cfg.headLeft q l r) = Cfg.headRight (f q) r l := rfl

@[simp] theorem mirrorCfg_zero {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [OfNat Γ 0]
    (f : Λ₁ → Λ₂) (q : Λ₁) (l r : ListBlank Γ) :
    mirrorCfg f ⟨some q, ⟨(0 : Γ), l, r⟩⟩ = ⟨some (f q), ⟨(0 : Γ), r, l⟩⟩ := rfl

/-! ## Commutation with Machine Steps -/

theorem step_mapCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂)
    (f : Λ₁ → Λ₂) (dmap : Dir → Dir) (Tmap : Tape Γ → Tape Γ)
    (hT_head : ∀ (T : Tape Γ), (Tmap T).head = T.head)
    (hT : ∀ (b : Γ) (d : Dir) (T : Tape Γ),
      Tmap ((T.write b).move d) = ((Tmap T).write b).move (dmap d))
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (dmap d)⟩)
    (c : Cfg Γ Λ₁) :
    step M₂ (mapCfg (Option.map f) Tmap c) = (step M₁ c).map (mapCfg (Option.map f) Tmap) := by
  rcases c with ⟨_ | q, T⟩
  · rfl
  · dsimp only [mapCfg, step, Option.map]
    rw [hT_head, hM]
    cases h : M₁ q T.head with
    | none => rfl
    | some res =>
      rcases res with ⟨q', ⟨b, d⟩⟩
      dsimp only [Option.map, Function.comp_apply]
      rw [hT]

theorem multiStep_mapCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂)
    (f : Λ₁ → Λ₂) (dmap : Dir → Dir) (Tmap : Tape Γ → Tape Γ)
    (hT_head : ∀ (T : Tape Γ), (Tmap T).head = T.head)
    (hT : ∀ (b : Γ) (d : Dir) (T : Tape Γ),
      Tmap ((T.write b).move d) = ((Tmap T).write b).move (dmap d))
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (dmap d)⟩)
    (n : ℕ) (c : Cfg Γ Λ₁) :
    multiStep M₂ (mapCfg (Option.map f) Tmap c) n =
      (multiStep M₁ c n).map (mapCfg (Option.map f) Tmap) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [multiStep_succ]
    rw [step_mapCfg M₁ M₂ f dmap Tmap hT_head hT hM]
    cases hs : step M₁ c with
    | none => rfl
    | some c' =>
      dsimp only [Option.map, Option.bind]
      exact ih c'

theorem reachesPlus_mapCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂)
    (f : Λ₁ → Λ₂) (dmap : Dir → Dir) (Tmap : Tape Γ → Tape Γ)
    (hT_head : ∀ (T : Tape Γ), (Tmap T).head = T.head)
    (hT : ∀ (b : Γ) (d : Dir) (T : Tape Γ),
      Tmap ((T.write b).move d) = ((Tmap T).write b).move (dmap d))
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (dmap d)⟩)
    {c₁ c₂ : Cfg Γ Λ₁} (h : ReachesPlus M₁ c₁ c₂) :
    ReachesPlus M₂ (mapCfg (Option.map f) Tmap c₁) (mapCfg (Option.map f) Tmap c₂) := by
  rcases h with ⟨n, hn, hstep⟩
  refine ⟨n, hn, ?_⟩
  rw [multiStep_mapCfg M₁ M₂ f dmap Tmap hT_head hT hM, hstep]
  rfl

theorem step_isNone_mapCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂)
    (f : Λ₁ → Λ₂) (dmap : Dir → Dir) (Tmap : Tape Γ → Tape Γ)
    (hT_head : ∀ (T : Tape Γ), (Tmap T).head = T.head)
    (hT : ∀ (b : Γ) (d : Dir) (T : Tape Γ),
      Tmap ((T.write b).move d) = ((Tmap T).write b).move (dmap d))
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (dmap d)⟩)
    (c : Cfg Γ Λ₁) :
    (step M₂ (mapCfg (Option.map f) Tmap c)).isNone = (step M₁ c).isNone := by
  rw [step_mapCfg M₁ M₂ f dmap Tmap hT_head hT hM]
  cases step M₁ c <;> rfl

theorem reachesPlus_mapState {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂) (f : Λ₁ → Λ₂)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ => ⟨q'.map f, Stmt.write b d⟩)
    {c₁ c₂ : Cfg Γ Λ₁} (h : ReachesPlus M₁ c₁ c₂) :
    ReachesPlus M₂ (mapState f c₁) (mapState f c₂) :=
  reachesPlus_mapCfg M₁ M₂ f id id (fun _ => rfl) (fun _ _ _ => rfl) hM h

theorem reachesPlus_mirrorCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂) (f : Λ₁ → Λ₂)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (reflectDir d)⟩)
    {c₁ c₂ : Cfg Γ Λ₁} (h : ReachesPlus M₁ c₁ c₂) :
    ReachesPlus M₂ (mirrorCfg f c₁) (mirrorCfg f c₂) :=
  reachesPlus_mapCfg M₁ M₂ f reflectDir reflectTape (fun _ => rfl) reflectTape_step_tape hM h

theorem step_isNone_mapState {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂) (f : Λ₁ → Λ₂)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ => ⟨q'.map f, Stmt.write b d⟩)
    (c : Cfg Γ Λ₁) :
    (step M₂ (mapState f c)).isNone = (step M₁ c).isNone :=
  step_isNone_mapCfg M₁ M₂ f id id (fun _ => rfl) (fun _ _ _ => rfl) hM c

theorem step_isNone_mirrorCfg {Γ Λ₁ Λ₂ : Type*} [Inhabited Γ] [Inhabited Λ₁] [Inhabited Λ₂]
    (M₁ : Machine Γ Λ₁) (M₂ : Machine Γ Λ₂) (f : Λ₁ → Λ₂)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (reflectDir d)⟩)
    (c : Cfg Γ Λ₁) :
    (step M₂ (mirrorCfg f c)).isNone = (step M₁ c).isNone :=
  step_isNone_mapCfg M₁ M₂ f reflectDir reflectTape (fun _ => rfl) reflectTape_step_tape hM c

/-! ## Closed Stack Transition Systems -/

/-- A closed 2nd-order digit-stack transition system for a Turing machine `M`.
Bundles the stack modes, polarity, unary-block recurrences, transfer rule, and closure
under `ReachesPlus`, independent of blank-tape reachability. -/
structure ClosedStackSystem {k : ℕ} {Λ : Type*} [Inhabited Λ]
    (M : Machine (Fin (k + 2)) Λ) where
  StackMode : Type
  dSym : Fin (k + 2)
  sSym : Fin (k + 2)
  encLeft : List (StackTuple (k + 2)) → ListBlank (Fin (k + 2))
  encRight : List (StackTuple (k + 2)) → ListBlank (Fin (k + 2))
  evalStackCfg :
    StackMode → List (StackTuple (k + 2)) → List (StackTuple (k + 2)) → Cfg (Fin (k + 2)) Λ
  IsInStackSystem : Cfg (Fin (k + 2)) Λ → Prop
  hpolarity : IsValidStackPolarity dSym sSym
  hnilL : encLeft [] = default
  hnilR : encRight [] = default
  hheadL : ∀ a b L, (encLeft ((a, b) :: L)).head = dSym
  hheadR : ∀ d b R, (encRight ((d, b) :: R)).head = dSym
  hnsL : ∃ t : ListBlank (Fin (k + 2)), t.head = dSym ∧ ∀ L, encLeft L ≠ t
  hnsR : ∃ t : ListBlank (Fin (k + 2)), t.head = dSym ∧ ∀ R, encRight R ≠ t
  hparams : ∃ strideL offsetL sepL maxSepL strideR offsetR sepR maxSepR : ℕ,
    strideL > 0 ∧ offsetL > 0 ∧ sepL > 0 ∧ 1 ≤ maxSepL ∧ maxSepL ≤ 4 ∧
    strideR > 0 ∧ offsetR > 0 ∧ sepR > 0 ∧ 1 ≤ maxSepR ∧ maxSepR ≤ 4 ∧
    (∀ a b L, encLeft ((a, b) :: L) =
      ListBlank.append (([dSym] : List (Fin (k + 2))) ^ (strideL * a + offsetL))
        (ListBlank.append
          (([sSym] : List (Fin (k + 2))) ^ (stackSepLen (n := k + 1) sepL maxSepL b))
          (encLeft L))) ∧
    (∀ d b R, encRight ((d, b) :: R) =
      ListBlank.append (([dSym] : List (Fin (k + 2))) ^ (strideR * d + offsetR))
        (ListBlank.append
          (([sSym] : List (Fin (k + 2))) ^ (stackSepLen (n := k + 1) sepR maxSepR b))
          (encRight R)))
  hmodes : ∃ modes : List StackMode, modes.length ≤ 6 ∧ ∀ m : StackMode, m ∈ modes
  hvalid : IsValidStackModes encLeft encRight evalStackCfg
  hiff : ∀ cfg, IsInStackSystem cfg ↔ ∃ m L R, cfg = evalStackCfg m L R
  hin : ∀ m L R, IsInStackSystem (evalStackCfg m L R)
  htransfer :
    (∃ (m m' : StackMode) (x : StackTuple (k + 2))
        (g : StackTuple (k + 2) → StackTuple (k + 2))
        (f : List (StackTuple (k + 2)) → List (StackTuple (k + 2))),
        (∀ s, s.length ≤ (f s).length) ∧
        ∀ z L R,
          ReachesPlus M (evalStackCfg m (x :: z :: L) R) (evalStackCfg m' (g z :: L) (f R))) ∨
    (∃ (m m' : StackMode) (x : StackTuple (k + 2))
        (g : StackTuple (k + 2) → StackTuple (k + 2))
        (f : List (StackTuple (k + 2)) → List (StackTuple (k + 2))),
        (∀ s, s.length ≤ (f s).length) ∧
        ∀ z L R,
          ReachesPlus M (evalStackCfg m L (x :: z :: R)) (evalStackCfg m' (f L) (g z :: R)))
  hclosed : ∀ cfg, IsInStackSystem cfg →
    ∃ cfg', ReachesPlus M cfg cfg' ∧ (IsInStackSystem cfg' ∨ (step M cfg').isNone)

/-- Derive `HasStackReduction` from a `ClosedStackSystem` together with an initial reachability
path from the blank tape to a non-trivial stack configuration. -/
theorem HasStackReduction.of_closedSystem {k : ℕ} {Λ : Type*} [Inhabited Λ]
    {M : Machine (Fin (k + 2)) Λ} (W : ClosedStackSystem M)
    (m_g : W.StackMode) (L_g R_g : List (StackTuple (k + 2)))
    (hreach : ReachesPlus M (init []) (W.evalStackCfg m_g L_g R_g))
    (hlen : 3 ≤ L_g.length + R_g.length)
    (hpos : ∃ x ∈ L_g ++ R_g, 1 ≤ x.1) :
    HasStackReduction M := by
  refine ⟨W.StackMode, W.dSym, W.sSym, W.encLeft, W.encRight, W.evalStackCfg, W.IsInStackSystem,
    W.hpolarity, W.hnilL, W.hnilR, W.hheadL, W.hheadR, W.hnsL, W.hnsR, W.hparams, W.hmodes,
    W.hvalid, W.hiff, W.hin, ⟨m_g, L_g, R_g, hreach, hlen, hpos⟩, W.htransfer, W.hclosed⟩

/-- Transport a `ClosedStackSystem` along a state relabeling bijection `f`. -/
def ClosedStackSystem.relabel {k : ℕ} {Λ₁ Λ₂ : Type*} [Inhabited Λ₁] [Inhabited Λ₂]
    {M₁ : Machine (Fin (k + 2)) Λ₁} {M₂ : Machine (Fin (k + 2)) Λ₂}
    (W : ClosedStackSystem M₁) (f : Λ₁ → Λ₂)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ => ⟨q'.map f, Stmt.write b d⟩) :
    ClosedStackSystem M₂ where
  StackMode := W.StackMode
  dSym := W.dSym
  sSym := W.sSym
  encLeft := W.encLeft
  encRight := W.encRight
  evalStackCfg m L R := mapState f (W.evalStackCfg m L R)
  IsInStackSystem cfg := ∃ m L R, cfg = mapState f (W.evalStackCfg m L R)
  hpolarity := W.hpolarity
  hnilL := W.hnilL
  hnilR := W.hnilR
  hheadL := W.hheadL
  hheadR := W.hheadR
  hnsL := W.hnsL
  hnsR := W.hnsR
  hparams := W.hparams
  hmodes := W.hmodes
  hvalid := by
    intro m
    rcases W.hvalid m with ⟨q, vL, vR, hvL, hvR, h1 | h2 | h3⟩
    · refine ⟨f q, vL, vR, hvL, hvR, Or.inl (fun L R => ?_)⟩
      dsimp only
      rw [h1, mapState_zero]
    · refine ⟨f q, vL, vR, hvL, hvR, Or.inr (Or.inl (fun L R => ?_))⟩
      dsimp only
      rw [h2, mapState_headLeft]
    · refine ⟨f q, vL, vR, hvL, hvR, Or.inr (Or.inr (fun L R => ?_))⟩
      dsimp only
      rw [h3, mapState_headRight]
  hiff := by intro cfg; rfl
  hin := by intro m L R; exact ⟨m, L, R, rfl⟩
  htransfer := by
    rcases W.htransfer with ⟨m, m', x, g, fl, hflen, hstep⟩ | ⟨m, m', x, g, fl, hflen, hstep⟩
    · refine Or.inl ⟨m, m', x, g, fl, hflen, fun z L R => ?_⟩
      exact reachesPlus_mapState M₁ M₂ f hM (hstep z L R)
    · refine Or.inr ⟨m, m', x, g, fl, hflen, fun z L R => ?_⟩
      exact reachesPlus_mapState M₁ M₂ f hM (hstep z L R)
  hclosed := by
    intro cfg ⟨m, L, R, hcfg⟩
    rw [hcfg]
    have hsys₁ : W.IsInStackSystem (W.evalStackCfg m L R) := W.hin m L R
    rcases W.hclosed (W.evalStackCfg m L R) hsys₁ with ⟨cfg', hreach, hsys' | hhalt⟩
    · rcases (W.hiff cfg').mp hsys' with ⟨m', L', R', hcfg'⟩
      refine ⟨mapState f cfg', reachesPlus_mapState M₁ M₂ f hM hreach, Or.inl ⟨m', L', R', ?_⟩⟩
      rw [hcfg']
    · refine ⟨mapState f cfg', reachesPlus_mapState M₁ M₂ f hM hreach, Or.inr ?_⟩
      rw [step_isNone_mapState M₁ M₂ f hM]
      exact hhalt

/-- Transport a `ClosedStackSystem` along a state bijection `f` and tape reflection (mirror). -/
def ClosedStackSystem.mirror {k : ℕ} {Λ₁ Λ₂ : Type*} [Inhabited Λ₁] [Inhabited Λ₂]
    {M₁ : Machine (Fin (k + 2)) Λ₁} {M₂ : Machine (Fin (k + 2)) Λ₂}
    (W : ClosedStackSystem M₁) (f : Λ₁ → Λ₂)
    (h_symm : W.encLeft = W.encRight)
    (hM : ∀ q a, M₂ (f q) a = (M₁ q a).map fun ⟨q', Stmt.write b d⟩ =>
      ⟨q'.map f, Stmt.write b (reflectDir d)⟩) :
    ClosedStackSystem M₂ where
  StackMode := W.StackMode
  dSym := W.dSym
  sSym := W.sSym
  encLeft := W.encLeft
  encRight := W.encRight
  evalStackCfg m L R := mirrorCfg f (W.evalStackCfg m R L)
  IsInStackSystem cfg := ∃ m L R, cfg = mirrorCfg f (W.evalStackCfg m R L)
  hpolarity := W.hpolarity
  hnilL := W.hnilL
  hnilR := W.hnilR
  hheadL := W.hheadL
  hheadR := W.hheadR
  hnsL := W.hnsL
  hnsR := W.hnsR
  hparams := W.hparams
  hmodes := W.hmodes
  hvalid := by
    intro m
    rcases W.hvalid m with ⟨q, vL, vR, hvL, hvR, h1 | h2 | h3⟩
    · refine ⟨f q, vR, vL, hvR, hvL, Or.inl (fun L R => ?_)⟩
      dsimp only
      rw [h1, mirrorCfg_zero, h_symm]
    · refine ⟨f q, vR, vL, hvR, hvL, Or.inr (Or.inr (fun L R => ?_))⟩
      dsimp only
      rw [h2, mirrorCfg_headLeft, h_symm]
    · refine ⟨f q, vR, vL, hvR, hvL, Or.inr (Or.inl (fun L R => ?_))⟩
      dsimp only
      rw [h3, mirrorCfg_headRight, h_symm]
  hiff := by intro cfg; rfl
  hin := by intro m L R; exact ⟨m, L, R, rfl⟩
  htransfer := by
    rcases W.htransfer with ⟨m, m', x, g, fl, hflen, hstep⟩ | ⟨m, m', x, g, fl, hflen, hstep⟩
    · refine Or.inr ⟨m, m', x, g, fl, hflen, fun z L R => ?_⟩
      exact reachesPlus_mirrorCfg M₁ M₂ f hM (hstep z R L)
    · refine Or.inl ⟨m, m', x, g, fl, hflen, fun z L R => ?_⟩
      exact reachesPlus_mirrorCfg M₁ M₂ f hM (hstep z R L)
  hclosed := by
    intro cfg ⟨m, L, R, hcfg⟩
    rw [hcfg]
    have hsys₁ : W.IsInStackSystem (W.evalStackCfg m R L) := W.hin m R L
    rcases W.hclosed (W.evalStackCfg m R L) hsys₁ with ⟨cfg', hreach, hsys' | hhalt⟩
    · rcases (W.hiff cfg').mp hsys' with ⟨m', R', L', hcfg'⟩
      refine ⟨mirrorCfg f cfg', reachesPlus_mirrorCfg M₁ M₂ f hM hreach, Or.inl ⟨m', L', R', ?_⟩⟩
      rw [hcfg']
    · refine ⟨mirrorCfg f cfg', reachesPlus_mirrorCfg M₁ M₂ f hM hreach, Or.inr ?_⟩
      rw [step_isNone_mirrorCfg M₁ M₂ f hM]
      exact hhalt

end BusyBeaver.Stack
